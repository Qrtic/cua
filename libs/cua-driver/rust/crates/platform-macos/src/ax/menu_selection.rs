//! Semantic selection for native popup options without an AXPress action.
//!
//! VCL exposes these as AXMenuItem children of a writable AXSelectedChildren
//! menu. Their AX window is the host, while their rendered popup is separate.
//! Geometry proves visibility only; authority comes from reciprocal native AX
//! ancestry, one PID/window, and the live parent's writable selection model.
//! This route never sends pointer/keyboard input or activates the application.

use super::bindings::*;
use core_foundation::{
    array::CFArray,
    base::{CFEqual, CFGetTypeID, CFRelease, CFRetain, CFType, CFTypeRef, TCFType},
    string::CFString,
};
use std::time::{Duration, Instant};

const MAX_DEPTH: usize = 24;
const MAX_CHILDREN: isize = 256;

trait SelectionTree {
    type Node: Clone;
    fn role(&self, node: &Self::Node) -> Option<String>;
    fn owner(&self, node: &Self::Node) -> Option<i32>;
    fn window_id(&self, node: &Self::Node) -> Option<u32>;
    fn parent(&self, node: &Self::Node) -> Option<Self::Node>;
    fn contains(&self, parent: &Self::Node, child: &Self::Node) -> bool;
    fn same(&self, a: &Self::Node, b: &Self::Node) -> bool;
    fn bool_attr(&self, node: &Self::Node, name: &str) -> Option<bool>;
    fn actions(&self, node: &Self::Node) -> Vec<String>;
    fn selection_settable(&self, menu: &Self::Node) -> bool;
    fn visible_popup(&self, menu: &Self::Node, pid: i32, host: u32) -> Option<u32>;
    fn within_budget(&self) -> bool;
}

struct SelectionPath<N> {
    menu: N,
    control: N,
    popup: u32,
}

fn prove<T: SelectionTree>(
    tree: &T,
    element: &T::Node,
    pid: i32,
    host: u32,
) -> Option<SelectionPath<T::Node>> {
    if pid <= 0
        || host == 0
        || tree.role(element).as_deref() != Some("AXMenuItem")
        || tree
            .actions(element)
            .iter()
            .any(|action| !action.trim().is_empty())
        || tree.bool_attr(element, "AXSelected").is_none()
        || tree.bool_attr(element, "AXEnabled") != Some(true)
        || tree.bool_attr(element, "AXHidden") != Some(false)
    {
        return None;
    }
    let menu = tree.parent(element)?;
    if tree.role(&menu).as_deref() != Some("AXMenu")
        || !tree.contains(&menu, element)
        || tree.bool_attr(&menu, "AXEnabled") != Some(true)
        || tree.bool_attr(&menu, "AXHidden") != Some(false)
        || !tree.selection_settable(&menu)
    {
        return None;
    }
    let control = tree.parent(&menu)?;
    if tree.role(&control).as_deref() != Some("AXPopUpButton")
        || !tree.contains(&control, &menu)
        || tree.bool_attr(&control, "AXEnabled") != Some(true)
        || !tree
            .actions(&control)
            .iter()
            .any(|action| action == "AXShowMenu")
    {
        return None;
    }
    let mut current = element.clone();
    let mut seen = Vec::new();
    for _ in 0..MAX_DEPTH {
        if !tree.within_budget()
            || tree.owner(&current) != Some(pid)
            || tree.window_id(&current) != Some(host)
            || seen.iter().any(|old| tree.same(old, &current))
        {
            return None;
        }
        match tree.role(&current).as_deref()? {
            "AXWindow" | "AXSheet" => {
                let popup = tree.visible_popup(&menu, pid, host)?;
                return tree.within_budget().then_some(SelectionPath {
                    menu,
                    control,
                    popup,
                });
            }
            "AXMenuItem" | "AXMenu" | "AXPopUpButton" | "AXGroup" | "AXScrollArea"
            | "AXSplitGroup" | "AXToolbar" | "AXRadioGroup" => {}
            // In particular, never turn a web menu or application menu into
            // an authorized native popup selection.
            _ => return None,
        }
        let parent = tree.parent(&current)?;
        if !tree.contains(&parent, &current) {
            return None;
        }
        seen.push(current);
        current = parent;
    }
    None
}

fn same_path<T: SelectionTree>(
    tree: &T,
    a: &SelectionPath<T::Node>,
    b: &SelectionPath<T::Node>,
) -> bool {
    a.popup == b.popup && tree.same(&a.menu, &b.menu) && tree.same(&a.control, &b.control)
}

struct Node(AXUIElementRef);
impl Node {
    unsafe fn owned(ptr: AXUIElementRef) -> Option<Self> {
        if ptr.is_null() {
            return None;
        }
        if AXUIElementSetMessagingTimeout(ptr, 0.1) != kAXErrorSuccess {
            CFRelease(ptr as CFTypeRef);
            return None;
        }
        Some(Self(ptr))
    }
    unsafe fn retained(ptr: AXUIElementRef) -> Option<Self> {
        if ptr.is_null() {
            return None;
        }
        CFRetain(ptr as CFTypeRef);
        Self::owned(ptr)
    }
}
impl Clone for Node {
    fn clone(&self) -> Self {
        unsafe {
            CFRetain(self.0 as CFTypeRef);
        }
        Self(self.0)
    }
}
impl Drop for Node {
    fn drop(&mut self) {
        unsafe {
            CFRelease(self.0 as CFTypeRef);
        }
    }
}

struct NativeTree {
    deadline: Instant,
}
impl NativeTree {
    fn new() -> Self {
        Self {
            deadline: Instant::now() + Duration::from_secs(2),
        }
    }

    fn elements(&self, node: &Node, name: &str) -> Option<Vec<Node>> {
        if !self.within_budget() {
            return None;
        }
        unsafe {
            let attr = CFString::new(name);
            let mut value: CFTypeRef = std::ptr::null();
            let error =
                AXUIElementCopyAttributeValue(node.0, attr.as_concrete_TypeRef(), &mut value);
            if error != kAXErrorSuccess || value.is_null() {
                return None;
            }
            if CFGetTypeID(value) != CFArray::<CFTypeRef>::type_id() {
                CFRelease(value);
                return None;
            }
            let array = CFArray::<CFTypeRef>::wrap_under_create_rule(value as _);
            if array.len() > MAX_CHILDREN {
                return None;
            }
            (0..array.len())
                .map(|index| {
                    let value = *array.get(index)?;
                    if CFGetTypeID(value) != AXUIElementGetTypeID() {
                        return None;
                    }
                    Node::retained(value as AXUIElementRef)
                })
                .collect()
        }
    }

    fn selected(&self, path: &SelectionPath<Node>, target: &Node) -> bool {
        self.bool_attr(target, "AXSelected") == Some(true)
            && self
                .elements(&path.menu, "AXSelectedChildren")
                .is_some_and(|rows| rows.len() == 1 && self.same(&rows[0], target))
    }

    fn committed_value(&self, control: &Node, title: &str) -> bool {
        if title.is_empty() {
            return false;
        }
        unsafe {
            if copy_string_attr(control.0, "AXValue").as_deref() == Some(title) {
                return true;
            }
        }
        let Some(children) = self.elements(control, "AXChildren") else {
            return false;
        };
        let values: Vec<_> = children
            .iter()
            .filter(|child| {
                matches!(
                    self.role(child).as_deref(),
                    Some("AXTextArea" | "AXTextField")
                ) && self.owner(child) == self.owner(control)
                    && self.window_id(child) == self.window_id(control)
            })
            .filter_map(|child| unsafe { copy_string_attr(child.0, "AXValue") })
            .collect();
        values.len() == 1 && values[0] == title
    }
}

impl SelectionTree for NativeTree {
    type Node = Node;
    fn role(&self, node: &Node) -> Option<String> {
        unsafe { copy_string_attr(node.0, "AXRole") }
    }
    fn owner(&self, node: &Node) -> Option<i32> {
        let mut pid = 0;
        (unsafe { AXUIElementGetPid(node.0, &mut pid) } == kAXErrorSuccess).then_some(pid)
    }
    fn window_id(&self, node: &Node) -> Option<u32> {
        unsafe { ax_get_window_id(node.0) }
    }
    fn parent(&self, node: &Node) -> Option<Node> {
        unsafe { Node::owned(copy_element_attr(node.0, "AXParent")?) }
    }
    fn contains(&self, parent: &Node, child: &Node) -> bool {
        self.elements(parent, "AXChildren")
            .is_some_and(|children| children.iter().any(|node| self.same(node, child)))
    }
    fn same(&self, a: &Node, b: &Node) -> bool {
        unsafe { CFEqual(a.0 as CFTypeRef, b.0 as CFTypeRef) != 0 }
    }
    fn bool_attr(&self, node: &Node, name: &str) -> Option<bool> {
        unsafe { copy_bool_attr(node.0, name) }
    }
    fn actions(&self, node: &Node) -> Vec<String> {
        unsafe { copy_action_names(node.0) }
    }
    fn selection_settable(&self, menu: &Node) -> bool {
        unsafe { is_attribute_settable(menu.0, "AXSelectedChildren") }
    }
    fn visible_popup(&self, menu: &Node, pid: i32, host: u32) -> Option<u32> {
        if !self.within_budget() {
            return None;
        }
        let frame = unsafe { element_screen_rect(menu.0) }?;
        visible_menu_window(
            pid,
            host,
            &frame,
            &crate::windows::all_windows_including_accessory_layers(),
        )
    }
    fn within_budget(&self) -> bool {
        Instant::now() < self.deadline
    }
}

fn visible_menu_window(
    pid: i32,
    host: u32,
    frame: &[f64; 4],
    windows: &[crate::windows::WindowInfo],
) -> Option<u32> {
    if frame.iter().any(|n| !n.is_finite()) || frame[2] <= 0.0 || frame[3] <= 0.0 {
        return None;
    }
    let mut matching = windows.iter().filter(|window| {
        let b = &window.bounds;
        window.pid == pid
            && window.window_id != 0
            && window.window_id != host
            && matches!(window.layer, 0 | 101)
            && window.is_on_screen
            && window.on_current_space != Some(false)
            && frame
                .iter()
                .zip([b.x, b.y, b.width, b.height])
                .all(|(a, b)| b.is_finite() && (a - b).abs() <= 0.5)
    });
    let id = matching.next()?.window_id;
    matching.next().is_none().then_some(id)
}

/// Read-only capability discovery. No synthetic action is added to AXActions.
pub(crate) unsafe fn is_selectable(element: AXUIElementRef) -> bool {
    let Some(element) = Node::retained(element) else {
        return false;
    };
    let tree = NativeTree::new();
    let Some(pid) = tree.owner(&element) else {
        return false;
    };
    let Some(host) = tree.window_id(&element) else {
        return false;
    };
    prove(&tree, &element, pid, host).is_some()
}

/// Select exactly the observed menu child, then dismiss its still-open native
/// popup through its advertised AXShowMenu. Never retry an uncertain mutation.
/// The result is true only if the closed control reports the selected label.
pub(crate) unsafe fn select(element: AXUIElementRef, pid: i32, host: u32) -> anyhow::Result<bool> {
    let element = Node::retained(element)
        .ok_or_else(|| anyhow::anyhow!("menu selection target unavailable; no input was sent"))?;
    let tree = NativeTree::new();
    let path = prove(&tree, &element, pid, host).ok_or_else(|| {
        anyhow::anyhow!("menu selection capability or ownership changed; no input was sent")
    })?;
    let title = copy_string_attr(element.0, "AXTitle").unwrap_or_default();
    let retained = CFType::wrap_under_get_rule(element.0 as CFTypeRef);
    let selection = CFArray::from_CFTypes(&[retained]);
    let attr = CFString::new("AXSelectedChildren");
    crate::foreground_activity::check_request()?;
    let error = AXUIElementSetAttributeValue(
        path.menu.0,
        attr.as_concrete_TypeRef(),
        selection.as_CFTypeRef(),
    );
    if error != kAXErrorSuccess {
        anyhow::bail!(
            "AXSelectedChildren returned {error}; effect uncertain, no fallback was attempted"
        );
    }
    std::thread::sleep(Duration::from_millis(40));
    if !tree.contains(&path.control, &path.menu) {
        return Ok(tree.committed_value(&path.control, &title));
    }
    if !tree.selected(&path, &element) {
        anyhow::bail!("AXSelectedChildren did not confirm the requested option; no second actuator was attempted");
    }
    std::thread::sleep(Duration::from_millis(40));
    let current =
        prove(&tree, &element, pid, host).filter(|current| same_path(&tree, &path, current));
    if current.is_none() || !tree.selected(&path, &element) {
        anyhow::bail!(
            "menu selection or ownership changed during readback; no dismissal was attempted"
        );
    }
    crate::foreground_activity::check_request()?;
    let error = perform_action(path.control.0, "AXShowMenu");
    if error != kAXErrorSuccess {
        anyhow::bail!("selected menu option but AXShowMenu dismissal returned {error}; no retry was attempted");
    }
    let deadline = Instant::now() + Duration::from_millis(350);
    loop {
        crate::foreground_activity::check_request()?;
        if !tree.contains(&path.control, &path.menu) {
            return Ok(tree.committed_value(&path.control, &title));
        }
        if Instant::now() >= deadline || !tree.within_budget() {
            return Ok(false);
        }
        std::thread::sleep(Duration::from_millis(25));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[derive(Clone)]
    struct TestNode {
        role: &'static str,
        pid: i32,
        window: u32,
        parent: Option<u8>,
        children: Vec<u8>,
        enabled: bool,
        hidden: bool,
        selected: Option<bool>,
        actions: Vec<String>,
        settable: bool,
    }
    struct Tree {
        nodes: HashMap<u8, TestNode>,
        popup: Option<u32>,
        budget: bool,
    }
    impl SelectionTree for Tree {
        type Node = u8;
        fn role(&self, n: &u8) -> Option<String> {
            self.nodes.get(n).map(|n| n.role.into())
        }
        fn owner(&self, n: &u8) -> Option<i32> {
            self.nodes.get(n).map(|n| n.pid)
        }
        fn window_id(&self, n: &u8) -> Option<u32> {
            self.nodes.get(n).map(|n| n.window)
        }
        fn parent(&self, n: &u8) -> Option<u8> {
            self.nodes.get(n)?.parent
        }
        fn contains(&self, p: &u8, c: &u8) -> bool {
            self.nodes.get(p).is_some_and(|n| n.children.contains(c))
        }
        fn same(&self, a: &u8, b: &u8) -> bool {
            a == b
        }
        fn bool_attr(&self, n: &u8, name: &str) -> Option<bool> {
            let n = self.nodes.get(n)?;
            match name {
                "AXEnabled" => Some(n.enabled),
                "AXHidden" => Some(n.hidden),
                "AXSelected" => n.selected,
                _ => None,
            }
        }
        fn actions(&self, n: &u8) -> Vec<String> {
            self.nodes[n].actions.clone()
        }
        fn selection_settable(&self, n: &u8) -> bool {
            self.nodes[n].settable
        }
        fn visible_popup(&self, _: &u8, _: i32, _: u32) -> Option<u32> {
            self.popup
        }
        fn within_budget(&self) -> bool {
            self.budget
        }
    }
    fn tree() -> Tree {
        let roles = [
            "AXMenuItem",
            "AXMenu",
            "AXPopUpButton",
            "AXGroup",
            "AXWindow",
        ];
        Tree {
            nodes: roles
                .iter()
                .enumerate()
                .map(|(i, role)| {
                    (
                        i as u8,
                        TestNode {
                            role,
                            pid: 42,
                            window: 700,
                            parent: (i < 4).then_some(i as u8 + 1),
                            children: if i == 0 { vec![] } else { vec![i as u8 - 1] },
                            enabled: true,
                            hidden: false,
                            selected: Some(false),
                            actions: if i == 2 {
                                vec!["AXShowMenu".into()]
                            } else {
                                vec![]
                            },
                            settable: i == 1,
                        },
                    )
                })
                .collect(),
            popup: Some(701),
            budget: true,
        }
    }

    #[test]
    fn admits_only_reciprocal_native_popup_selection() {
        let t = tree();
        let p = prove(&t, &0, 42, 700).unwrap();
        assert_eq!((p.menu, p.control, p.popup), (1, 2, 701));
        assert!(prove(&t, &0, 99, 700).is_none());
        assert!(prove(&t, &0, 42, 701).is_none());
    }

    #[test]
    fn closed_disabled_readonly_web_and_foreign_options_are_not_addressable() {
        for mutation in 0..12 {
            let mut t = tree();
            match mutation {
                0 => t.nodes.get_mut(&2).unwrap().children.clear(),
                1 => t.nodes.get_mut(&1).unwrap().children.clear(),
                2 => t.nodes.get_mut(&0).unwrap().enabled = false,
                3 => t.nodes.get_mut(&0).unwrap().hidden = true,
                4 => t.nodes.get_mut(&1).unwrap().settable = false,
                5 => t.nodes.get_mut(&2).unwrap().actions.clear(),
                6 => t.nodes.get_mut(&3).unwrap().role = "AXWebArea",
                7 => t.nodes.get_mut(&2).unwrap().role = "AXMenuBarItem",
                8 => t.nodes.get_mut(&3).unwrap().pid = 99,
                9 => t.nodes.get_mut(&0).unwrap().actions.push("AXPress".into()),
                10 => t.popup = None,
                _ => t.budget = false,
            }
            assert!(prove(&t, &0, 42, 700).is_none(), "mutation {mutation}");
        }
    }

    #[test]
    fn changed_popup_identity_invalidates_the_selection_path() {
        let mut t = tree();
        let before = prove(&t, &0, 42, 700).unwrap();
        t.popup = Some(702);
        assert!(!same_path(&t, &before, &prove(&t, &0, 42, 700).unwrap()));
        t.nodes.get_mut(&3).unwrap().parent = Some(2);
        t.nodes.get_mut(&2).unwrap().children.push(3);
        assert!(prove(&t, &0, 42, 700).is_none());
    }

    #[test]
    fn vcl_layer_zero_popup_is_visible_without_replacing_the_host_identity() {
        use crate::windows::{WindowBounds, WindowInfo};
        let frame = [818.0, 378.0, 217.0, 104.0];
        let w = WindowInfo {
            window_id: 701,
            pid: 42,
            app_name: String::new(),
            title: String::new(),
            bounds: WindowBounds {
                x: 818.0,
                y: 378.0,
                width: 217.0,
                height: 104.0,
            },
            layer: 0,
            z_index: 0,
            is_on_screen: true,
            current_space_id: None,
            on_current_space: Some(true),
            space_ids: None,
        };
        assert_eq!(
            visible_menu_window(42, 700, &frame, &[w.clone()]),
            Some(701)
        );
        assert_eq!(visible_menu_window(42, 701, &frame, &[w.clone()]), None);
        assert_eq!(
            visible_menu_window(42, 700, &frame, &[w.clone(), w.clone()]),
            None
        );
        for mutation in 0..6 {
            let mut bad = w.clone();
            match mutation {
                0 => bad.pid = 99,
                1 => bad.is_on_screen = false,
                2 => bad.on_current_space = Some(false),
                3 => bad.bounds.y += 1.0,
                4 => bad.window_id = 0,
                _ => bad.layer = 3,
            }
            assert_eq!(
                visible_menu_window(42, 700, &frame, &[bad]),
                None,
                "mutation {mutation}"
            );
        }
    }
}
