//! Element-bound semantic proof for native controls in one attached AXPopover.
//!
//! A control can name either the AXPopover (Calendar/Pages) or the host (Keynote)
//! as AXWindow. Its physical window ID must match the actual AXPopover, which
//! must remain in its reciprocal AXParent chain and name the exact host.
//! Native popup-button menus may omit AXWindow and report the popover's ID,
//! while WindowServer displays a separate menu surface. Prove their reciprocal
//! control ancestry and visible menu geometry; this only authorizes AX actions.
//! Keep physical window identities intact for pointer and keyboard routing.

use super::bindings::{
    ax_get_window_id, copy_element_attr, copy_string_attr, kAXErrorSuccess,
    AXUIElementCopyAttributeValue, AXUIElementGetPid, AXUIElementRef,
    AXUIElementSetMessagingTimeout,
};
use core_foundation::{
    array::CFArray,
    base::{CFEqual, CFGetTypeID, CFRelease, CFRetain, CFTypeRef, TCFType},
    string::CFString,
};
use std::time::{Duration, Instant};

const MAX_DEPTH: usize = 32;
const MAX_CHILDREN: isize = 1024;

fn native_control_role(role: Option<&str>) -> bool {
    matches!(
        role,
        Some(
            "AXButton"
                | "AXTextField"
                | "AXTextArea"
                | "AXPopUpButton"
                | "AXCheckBox"
                | "AXRadioButton"
        )
    )
}

pub(crate) fn native_text_role(role: Option<&str>) -> bool {
    matches!(role, Some("AXTextField" | "AXTextArea"))
}

fn native_menu_role(role: Option<&str>) -> bool {
    matches!(role, Some("AXMenu" | "AXMenuItem"))
}

fn container_role(role: &str) -> bool {
    matches!(
        role,
        "AXRadioGroup" | "AXGroup" | "AXScrollArea" | "AXSplitGroup" | "AXToolbar"
    )
}

trait PopoverTree {
    type Node: Clone;
    fn role(&self, node: &Self::Node) -> Option<String>;
    fn owner(&self, node: &Self::Node) -> Option<i32>;
    fn window(&self, node: &Self::Node) -> Option<Self::Node>;
    fn window_id(&self, node: &Self::Node) -> Option<u32>;
    fn parent(&self, node: &Self::Node) -> Option<Self::Node>;
    fn contains_child(&self, parent: &Self::Node, child: &Self::Node) -> bool;
    fn same(&self, left: &Self::Node, right: &Self::Node) -> bool;
    fn within_budget(&self) -> bool;
    fn visible_menu_window(&self, node: &Self::Node, pid: i32) -> Option<u32>;
}

struct MenuPath<N> {
    control: N,
    nodes: Vec<N>,
    windows: Vec<(N, u32)>,
}

/// Only a live menu/submenu chain ending at one native popup button. Neither
/// menu-bar items nor an application root are a substitute for that control.
fn menu_control<T: PopoverTree>(
    tree: &T,
    pid: i32,
    element: &T::Node,
) -> Result<MenuPath<T::Node>, &'static str> {
    let mut current = element.clone();
    let mut nodes = Vec::new();
    let mut windows = Vec::new();
    for _ in 0..MAX_DEPTH {
        if !tree.within_budget() || tree.owner(&current) != Some(pid) {
            return Err("menu_owner_or_deadline");
        }
        if nodes.iter().any(|node| tree.same(node, &current)) {
            return Err("menu_cycle");
        }
        let role = tree.role(&current).ok_or("menu_role_missing")?;
        if !native_menu_role(Some(&role)) {
            return Err("menu_role_unexpected");
        }
        if role == "AXMenu" {
            let window = tree
                .visible_menu_window(&current, pid)
                .ok_or("menu_not_visible")?;
            windows.push((current.clone(), window));
        }
        let parent = tree.parent(&current).ok_or("menu_parent_missing")?;
        if !tree.contains_child(&parent, &current) {
            return Err("menu_child_relation_missing");
        }
        nodes.push(current);
        match (role.as_str(), tree.role(&parent).as_deref()) {
            ("AXMenu", Some("AXPopUpButton")) if tree.owner(&parent) == Some(pid) => {
                return Ok(MenuPath {
                    control: parent,
                    nodes,
                    windows,
                });
            }
            ("AXMenu", Some("AXMenuItem")) | ("AXMenuItem", Some("AXMenu")) => {
                current = parent;
            }
            _ => return Err("menu_control_boundary"),
        }
    }
    Err("menu_depth_limit")
}

fn same_menu_path<T: PopoverTree>(tree: &T, a: &MenuPath<T::Node>, b: &MenuPath<T::Node>) -> bool {
    tree.same(&a.control, &b.control)
        && a.nodes.len() == b.nodes.len()
        && a.nodes.iter().zip(&b.nodes).all(|(a, b)| tree.same(a, b))
        && a.windows.len() == b.windows.len()
        && a.windows
            .iter()
            .zip(&b.windows)
            .all(|((a, aw), (b, bw))| aw == bw && tree.same(a, b))
}

fn prove<T: PopoverTree>(tree: &T, pid: i32, host_id: u32, element: &T::Node) -> bool {
    match prove_checked(tree, pid, host_id, element) {
        Ok(()) => true,
        Err(reason) => {
            // Bounded diagnostic facts only; never log labels or text values.
            tracing::debug!(target: "cua_popover_proof", pid, host_id, reason,
                "attached popover proof refused");
            false
        }
    }
}

fn containing_popover<T: PopoverTree>(
    tree: &T,
    pid: i32,
    element: &T::Node,
) -> Result<T::Node, &'static str> {
    let mut current = element.clone();
    let mut visited = Vec::new();
    for _ in 0..MAX_DEPTH {
        if !tree.within_budget() {
            return Err("popover_lookup_deadline");
        }
        if tree.owner(&current) != Some(pid) {
            return Err("popover_lookup_owner_mismatch");
        }
        if visited.iter().any(|node| tree.same(node, &current)) {
            return Err("popover_lookup_cycle");
        }
        match tree.role(&current).as_deref() {
            Some("AXPopover") => return Ok(current),
            Some(role) if native_control_role(Some(role)) || container_role(role) => {}
            _ => return Err("popover_lookup_boundary"),
        }
        let parent = tree
            .parent(&current)
            .ok_or("popover_lookup_parent_missing")?;
        if !tree.contains_child(&parent, &current) {
            return Err("popover_lookup_child_relation_missing");
        }
        visited.push(current);
        current = parent;
    }
    Err("popover_lookup_depth_limit")
}

fn prove_checked<T: PopoverTree>(
    tree: &T,
    pid: i32,
    host_id: u32,
    element: &T::Node,
) -> Result<(), &'static str> {
    // The root can advertise AXCancel. Its AXWindow names the host, whereas a
    // button's AXWindow can name the popover or the document host. That logical
    // attribute does not replace the button's independently read physical ID.
    let is_popover_root = tree.role(element).as_deref() == Some("AXPopover");
    let menu_path = if native_menu_role(tree.role(element).as_deref()) {
        Some(menu_control(tree, pid, element)?)
    } else {
        None
    };
    let control = menu_path.as_ref().map_or(element, |menu| &menu.control);
    let mut control_window = None;
    let popover = if is_popover_root {
        element.clone()
    } else if native_control_role(tree.role(control).as_deref()) {
        let window = tree.window(control).ok_or("element_window_missing")?;
        let popover = match tree.role(&window).as_deref() {
            Some("AXPopover") => window.clone(),
            Some("AXWindow") => containing_popover(tree, pid, control)?,
            _ => return Err("element_window_not_popover"),
        };
        control_window = Some(window);
        popover
    } else {
        return Err("element_not_native_control_or_popover");
    };
    let popover_role = tree.role(&popover);
    if popover_role.as_deref() != Some("AXPopover") {
        tracing::debug!(target: "cua_popover_proof", role = ?popover_role,
            "element window is not a popover");
        return Err("element_window_not_popover");
    }
    if tree.owner(&popover) != Some(pid) {
        return Err("popover_owner_mismatch");
    }
    let Some(popover_id) = tree.window_id(&popover).filter(|id| *id != host_id) else {
        return Err("popover_window_id_missing_or_host");
    };
    let Some(host) = tree.window(&popover) else {
        return Err("popover_host_attribute_missing");
    };
    if let Some(window) = &control_window {
        if tree.owner(window) != Some(pid)
            || tree.window_id(element) != Some(popover_id)
            || tree.window_id(control) != Some(popover_id)
            || !(tree.same(window, &popover) || tree.same(window, &host))
        {
            return Err("control_window_does_not_match_popover_or_host");
        }
    }
    if !matches!(tree.role(&host).as_deref(), Some("AXWindow" | "AXSheet")) {
        return Err("host_role_unexpected");
    }
    if tree.owner(&host) != Some(pid) {
        return Err("host_owner_mismatch");
    }
    if tree.window_id(&host) != Some(host_id) {
        return Err("host_window_id_mismatch");
    }
    if menu_path.as_ref().is_some_and(|path| {
        path.nodes
            .iter()
            .any(|node| tree.window_id(node) != Some(popover_id))
    }) {
        return Err("menu_surface_mismatch");
    }

    let mut current = element.clone();
    let mut visited = Vec::new();
    let mut crossed_popover = false;
    for depth in 0..MAX_DEPTH {
        if !tree.within_budget() {
            return Err("ancestry_deadline");
        }
        if tree.owner(&current) != Some(pid) {
            return Err("ancestor_owner_mismatch");
        }
        if visited.iter().any(|node| tree.same(node, &current)) {
            return Err("ancestry_cycle");
        }
        if tree.same(&current, &host) {
            // Re-read the attachment after traversal; an old AXParent alone
            // must not authorize a closed or reattached panel.
            let unchanged = crossed_popover
                && tree.window_id(&current) == Some(host_id)
                && tree.window_id(&popover) == Some(popover_id)
                && if is_popover_root {
                    tree.same(element, &popover)
                        && tree.role(element).as_deref() == Some("AXPopover")
                } else {
                    control_window.as_ref().is_some_and(|window| {
                        tree.window(control)
                            .is_some_and(|node| tree.same(&node, window))
                            && tree.owner(window) == Some(pid)
                            && tree.window_id(element) == Some(popover_id)
                            && tree.window_id(control) == Some(popover_id)
                            && (tree.same(window, &popover) || tree.same(window, &host))
                            && matches!(
                                tree.role(window).as_deref(),
                                Some("AXPopover" | "AXWindow")
                            )
                    })
                }
                && menu_path.as_ref().is_none_or(|path| {
                    menu_control(tree, pid, element).is_ok_and(|current| {
                        same_menu_path(tree, path, &current)
                            && current
                                .nodes
                                .iter()
                                .all(|node| tree.window_id(node) == Some(popover_id))
                    })
                })
                && tree.role(&popover).as_deref() == Some("AXPopover")
                && tree
                    .window(&popover)
                    .is_some_and(|node| tree.same(&node, &host))
                && tree.within_budget();
            return unchanged.then_some(()).ok_or("attachment_changed");
        }
        let role = tree.role(&current);
        match role.as_deref() {
            Some("AXPopover") if tree.same(&current, &popover) && !crossed_popover => {
                crossed_popover = true;
            }
            Some(role)
                if menu_path.is_some() && native_menu_role(Some(role)) && !crossed_popover => {}
            Some(role) if native_control_role(Some(role)) || container_role(role) => {}
            // A different top-level window, nested popover, web subtree or
            // application root cannot be treated as an attachment to this host.
            _ => {
                tracing::debug!(target: "cua_popover_proof", depth, role = ?role,
                    "unexpected role in popover ancestry");
                return Err("ancestor_role_unexpected");
            }
        }
        let Some(parent) = tree.parent(&current) else {
            return Err("ancestor_parent_missing");
        };
        if !tree.contains_child(&parent, &current) {
            tracing::debug!(target: "cua_popover_proof", depth, role = ?role,
                "popover ancestry lacks reciprocal child relation");
            return Err("ancestor_child_relation_missing");
        }
        visited.push(current);
        current = parent;
    }
    Err("ancestry_depth_limit")
}

/// No unknown-action mapping, selection writes, ancestor or pixel fallback.
pub(crate) fn advertised_action(
    role: Option<&str>,
    action: &str,
    advertised: &[String],
) -> Option<&'static str> {
    let native = match (role, action) {
        (Some("AXPopover"), "cancel") => "AXCancel",
        (Some("AXMenu" | "AXMenuItem"), "cancel") => "AXCancel",
        (Some("AXMenuItem"), "press" | "click") => "AXPress",
        (Some("AXMenuItem"), "pick") => "AXPick",
        (
            Some("AXButton" | "AXPopUpButton" | "AXCheckBox" | "AXRadioButton"),
            "press" | "click",
        ) => "AXPress",
        (Some("AXButton" | "AXPopUpButton" | "AXCheckBox" | "AXRadioButton"), "pick") => "AXPick",
        (role, "show_menu") if native_control_role(role) => "AXShowMenu",
        (role, "confirm") if native_text_role(role) => "AXConfirm",
        _ => return None,
    };
    advertised
        .iter()
        .any(|value| value == native)
        .then_some(native)
}

struct AxNode(AXUIElementRef);
impl AxNode {
    unsafe fn owned(ptr: AXUIElementRef) -> Option<Self> {
        if ptr.is_null() {
            return None;
        }
        if AXUIElementSetMessagingTimeout(ptr, 0.2) != kAXErrorSuccess {
            CFRelease(ptr as CFTypeRef);
            return None;
        }
        Some(Self(ptr))
    }
}
impl Clone for AxNode {
    fn clone(&self) -> Self {
        unsafe {
            CFRetain(self.0 as CFTypeRef);
        }
        Self(self.0)
    }
}
impl Drop for AxNode {
    fn drop(&mut self) {
        unsafe {
            CFRelease(self.0 as CFTypeRef);
        }
    }
}

struct NativeTree {
    deadline: Instant,
}
impl PopoverTree for NativeTree {
    type Node = AxNode;
    fn role(&self, node: &AxNode) -> Option<String> {
        unsafe { copy_string_attr(node.0, "AXRole") }
    }
    fn owner(&self, node: &AxNode) -> Option<i32> {
        let mut pid = 0;
        (unsafe { AXUIElementGetPid(node.0, &mut pid) } == kAXErrorSuccess).then_some(pid)
    }
    fn window(&self, node: &AxNode) -> Option<AxNode> {
        unsafe { AxNode::owned(copy_element_attr(node.0, "AXWindow")?) }
    }
    fn window_id(&self, node: &AxNode) -> Option<u32> {
        unsafe { ax_get_window_id(node.0) }
    }
    fn parent(&self, node: &AxNode) -> Option<AxNode> {
        unsafe { AxNode::owned(copy_element_attr(node.0, "AXParent")?) }
    }
    fn contains_child(&self, parent: &AxNode, child: &AxNode) -> bool {
        unsafe {
            let attr = CFString::new("AXChildren");
            let mut value: CFTypeRef = std::ptr::null();
            if AXUIElementCopyAttributeValue(parent.0, attr.as_concrete_TypeRef(), &mut value)
                != kAXErrorSuccess
                || value.is_null()
            {
                return false;
            }
            if CFGetTypeID(value) != CFArray::<CFTypeRef>::type_id() {
                CFRelease(value);
                return false;
            }
            let children = CFArray::<CFTypeRef>::wrap_under_create_rule(value as _);
            children.len() <= MAX_CHILDREN
                && (0..children.len()).any(|index| {
                    CFEqual(
                        *children.get(index).expect("bounded index"),
                        child.0 as CFTypeRef,
                    ) != 0
                })
        }
    }
    fn same(&self, left: &AxNode, right: &AxNode) -> bool {
        unsafe { CFEqual(left.0 as CFTypeRef, right.0 as CFTypeRef) != 0 }
    }
    fn within_budget(&self) -> bool {
        Instant::now() < self.deadline
    }
    fn visible_menu_window(&self, node: &AxNode, pid: i32) -> Option<u32> {
        if !self.within_budget() {
            return None;
        }
        let frame = unsafe { super::bindings::element_screen_rect(node.0) }?;
        let window = match_menu_window(
            pid,
            &frame,
            &crate::windows::all_windows_including_accessory_layers(),
        )?;
        self.within_budget().then_some(window)
    }
}

/// A menu's inherited AX window ID is not its rendered surface. Require a
/// unique current popup-level WindowServer frame owned by this process.
fn match_menu_window(
    pid: i32,
    frame: &[f64; 4],
    windows: &[crate::windows::WindowInfo],
) -> Option<u32> {
    if frame.iter().any(|v| !v.is_finite()) || frame[2] <= 0.0 || frame[3] <= 0.0 {
        return None;
    }
    let mut matching = windows.iter().filter(|window| {
        let b = &window.bounds;
        window.pid == pid
            && window.window_id != 0
            && window.layer == 101
            && window.is_on_screen
            && window.on_current_space != Some(false)
            && frame
                .iter()
                .zip([b.x, b.y, b.width, b.height])
                .all(|(a, b)| b.is_finite() && (a - b).abs() <= 0.5)
    });
    let window = matching.next()?.window_id;
    matching.next().is_none().then_some(window)
}

fn requires_host_attachment(
    role: Option<&str>,
    physical_window: Option<u32>,
    host_id: u32,
    parent_window: impl FnOnce() -> Option<u32>,
) -> bool {
    (role == Some("AXPopover") || native_control_role(role) || native_menu_role(role))
        && physical_window.is_some_and(|id| id != host_id)
        && parent_window() != Some(host_id)
}

/// Classification only. Exact surfaces and controls whose nearest parent
/// surface is the target keep the ordinary route. A different or unknown
/// logical surface still requires the full attachment proof.
pub(crate) unsafe fn has_displaced_popover_window(element: AXUIElementRef, host_id: u32) -> bool {
    // Keynote's AXWindow attribute points to the host even though the button
    // physically lives in a separate popover. Classify the actual element ID.
    requires_host_attachment(
        copy_string_attr(element, "AXRole").as_deref(),
        ax_get_window_id(element),
        host_id,
        // TextEdit's save sheet hosts buttons on a separate accessory
        // CGWindow. Physical displacement alone does not make them popovers.
        // Do not use AXWindow here: Keynote can alias that attribute to a host
        // even for a real popover. Require the nearest AXParent surface.
        || super::element_ancestry::parent_window_id(element),
    )
}

/// # Safety
/// `element` must stay retained for this bounded, read-only proof.
pub(crate) unsafe fn proves_attached_popover(
    pid: i32,
    host_id: u32,
    element: AXUIElementRef,
) -> bool {
    if element.is_null() {
        return false;
    }
    CFRetain(element as CFTypeRef);
    let Some(element) = AxNode::owned(element) else {
        return false;
    };
    prove(
        &NativeTree {
            deadline: Instant::now() + Duration::from_secs(2),
        },
        pid,
        host_id,
        &element,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cell::Cell, collections::HashMap};

    #[derive(Clone)]
    struct Node {
        identity: u32,
        role: &'static str,
        owner: i32,
        window: Option<u32>,
        id: Option<u32>,
        parent: Option<u32>,
        children: Vec<u32>,
    }
    struct Tree {
        nodes: HashMap<u32, Node>,
        budget: Cell<usize>,
        reattach: bool,
        popup_window_reads: Cell<usize>,
        menu_windows: HashMap<u32, u32>,
        menu_window_reads: Cell<usize>,
        replace_menu_window: bool,
    }
    impl PopoverTree for Tree {
        type Node = u32;
        fn role(&self, node: &u32) -> Option<String> {
            self.nodes.get(node).map(|n| n.role.into())
        }
        fn owner(&self, node: &u32) -> Option<i32> {
            self.nodes.get(node).map(|n| n.owner)
        }
        fn window(&self, node: &u32) -> Option<u32> {
            if *node == 2 {
                let reads = self.popup_window_reads.get();
                self.popup_window_reads.set(reads + 1);
                if self.reattach && reads > 0 {
                    return Some(8);
                }
            }
            self.nodes.get(node)?.window
        }
        fn window_id(&self, node: &u32) -> Option<u32> {
            self.nodes.get(node)?.id
        }
        fn parent(&self, node: &u32) -> Option<u32> {
            self.nodes.get(node)?.parent
        }
        fn contains_child(&self, parent: &u32, child: &u32) -> bool {
            self.nodes
                .get(parent)
                .is_some_and(|n| n.children.iter().any(|c| self.same(c, child)))
        }
        fn same(&self, a: &u32, b: &u32) -> bool {
            self.nodes
                .get(a)
                .zip(self.nodes.get(b))
                .is_some_and(|(a, b)| a.identity == b.identity)
        }
        fn within_budget(&self) -> bool {
            let remaining = self.budget.get();
            self.budget.set(remaining.saturating_sub(1));
            remaining > 0
        }
        fn visible_menu_window(&self, node: &u32, _pid: i32) -> Option<u32> {
            let reads = self.menu_window_reads.get();
            self.menu_window_reads.set(reads + 1);
            self.menu_windows
                .get(node)
                .map(|window| window + u32::from(self.replace_menu_window && reads > 0))
        }
    }
    fn pages() -> Tree {
        let roles = [
            "AXButton",
            "AXRadioGroup",
            "AXPopover",
            "AXScrollArea",
            "AXGroup",
            "AXSplitGroup",
            "AXWindow",
        ];
        let nodes = roles
            .into_iter()
            .enumerate()
            .map(|(index, role)| {
                let i = index as u32;
                (
                    i,
                    Node {
                        identity: i,
                        role,
                        owner: 42,
                        window: if i == 0 {
                            Some(2)
                        } else if i < 6 {
                            Some(6)
                        } else {
                            None
                        },
                        id: Some(if i <= 2 { 900 } else { 700 }),
                        parent: (i < 6).then_some(i + 1),
                        children: if i == 0 { vec![] } else { vec![i - 1] },
                    },
                )
            })
            .collect();
        Tree {
            nodes,
            budget: Cell::new(100),
            reattach: false,
            popup_window_reads: Cell::new(0),
            menu_windows: HashMap::new(),
            menu_window_reads: Cell::new(0),
            replace_menu_window: false,
        }
    }
    #[test]
    fn pages_swatch_crosses_its_attached_popover_to_exact_host() {
        assert!(prove(&pages(), 42, 700, &0));
    }

    fn calendar_menu() -> Tree {
        // Native T022 evidence: the menu and its item omit AXWindow and report
        // the popover's physical ID; AXParent reciprocally reaches the popup
        // button, then AXPopover, then the exact document host.
        let mut tree = pages();
        let button = tree.nodes.get_mut(&0).unwrap();
        button.role = "AXPopUpButton";
        button.window = Some(6);
        button.parent = Some(2);
        button.children = vec![7];
        tree.nodes.get_mut(&2).unwrap().children = vec![0];
        tree.menu_windows.insert(7, 1700);
        for (identity, role, parent, children) in
            [(7, "AXMenu", 0, vec![8]), (8, "AXMenuItem", 7, vec![])]
        {
            tree.nodes.insert(
                identity,
                Node {
                    identity,
                    role,
                    owner: 42,
                    window: None,
                    id: Some(900),
                    parent: Some(parent),
                    children,
                },
            );
        }
        tree
    }

    #[test]
    fn calendar_live_menu_item_and_cancel_root_prove_their_exact_attached_popover() {
        for element in [7, 8] {
            assert!(
                prove(&calendar_menu(), 42, 700, &element),
                "element {element}"
            );
        }
    }

    #[test]
    fn calendar_menu_classification_never_treats_it_as_a_host_pointer() {
        for role in ["AXMenu", "AXMenuItem"] {
            assert!(requires_host_attachment(Some(role), Some(900), 700, || {
                Some(900)
            }));
            assert!(!requires_host_attachment(
                Some(role),
                Some(700),
                700,
                || Some(700)
            ));
        }
    }

    #[test]
    fn calendar_menu_actions_are_only_the_requested_advertised_semantics() {
        assert_eq!(
            advertised_action(Some("AXMenuItem"), "pick", &["AXPick".into()]),
            Some("AXPick")
        );
        assert_eq!(
            advertised_action(Some("AXMenuItem"), "press", &["AXPress".into()]),
            Some("AXPress")
        );
        assert_eq!(
            advertised_action(Some("AXMenu"), "cancel", &["AXCancel".into()]),
            Some("AXCancel")
        );
        assert_eq!(
            advertised_action(Some("AXMenu"), "press", &["AXPress".into()]),
            None
        );
        assert_eq!(
            advertised_action(Some("AXMenuItem"), "press", &["AXPick".into()]),
            None
        );
        assert_eq!(
            advertised_action(Some("AXMenuItem"), "unknown", &["AXPress".into()]),
            None
        );
    }

    #[test]
    fn calendar_menu_refuses_a_closed_foreign_or_reparented_item() {
        for broken_parent in [0, 2, 7] {
            let mut tree = calendar_menu();
            tree.nodes.get_mut(&broken_parent).unwrap().children.clear();
            assert!(
                !prove(&tree, 42, 700, &8),
                "missing reciprocal edge {broken_parent}"
            );
        }
        for foreign in [0, 2, 7, 8] {
            let mut tree = calendar_menu();
            tree.nodes.get_mut(&foreign).unwrap().owner = 99;
            assert!(!prove(&tree, 42, 700, &8), "foreign node {foreign}");
        }
        for mismatched in [0, 7, 8] {
            let mut tree = calendar_menu();
            tree.nodes.get_mut(&mismatched).unwrap().id = Some(901);
            assert!(!prove(&tree, 42, 700, &8), "different surface {mismatched}");
        }
        let mut tree = calendar_menu();
        tree.nodes.get_mut(&0).unwrap().role = "AXWebArea";
        assert!(!prove(&tree, 42, 700, &8));
        let mut tree = calendar_menu();
        tree.reattach = true;
        assert!(!prove(&tree, 42, 700, &8));
        let tree = calendar_menu();
        tree.budget.set(0);
        assert!(!prove(&tree, 42, 700, &8));
    }

    #[test]
    fn calendar_menu_requires_a_current_stable_visible_surface() {
        let mut tree = calendar_menu();
        tree.menu_windows.clear();
        assert!(
            !prove(&tree, 42, 700, &8),
            "a retained AX menu alone is not an open menu"
        );
        let mut tree = calendar_menu();
        tree.replace_menu_window = true;
        assert!(
            !prove(&tree, 42, 700, &8),
            "replacement menu surface must be re-observed"
        );
    }

    #[test]
    fn calendar_submenu_keeps_the_same_control_and_checks_each_visible_menu() {
        let mut tree = calendar_menu();
        tree.nodes.get_mut(&8).unwrap().children = vec![9];
        for (identity, role, parent, children) in
            [(9, "AXMenu", 8, vec![10]), (10, "AXMenuItem", 9, vec![])]
        {
            tree.nodes.insert(
                identity,
                Node {
                    identity,
                    role,
                    owner: 42,
                    window: None,
                    id: Some(900),
                    parent: Some(parent),
                    children,
                },
            );
        }
        tree.menu_windows.insert(9, 1701);
        assert!(prove(&tree, 42, 700, &10));
        tree.menu_windows.remove(&7);
        assert!(
            !prove(&tree, 42, 700, &10),
            "closed parent menu invalidates the submenu"
        );
    }

    #[test]
    fn visible_menu_frame_excludes_stale_foreign_hidden_and_ambiguous_windows() {
        use crate::windows::{WindowBounds, WindowInfo};
        let frame = [1035.0, 699.0, 116.0, 153.0];
        let candidate = WindowInfo {
            window_id: 104749,
            pid: 42,
            app_name: String::new(),
            title: String::new(),
            bounds: WindowBounds {
                x: frame[0],
                y: frame[1],
                width: frame[2],
                height: frame[3],
            },
            layer: 101,
            z_index: 0,
            is_on_screen: true,
            current_space_id: None,
            on_current_space: Some(true),
            space_ids: None,
        };
        assert_eq!(
            match_menu_window(42, &frame, &[candidate.clone()]),
            Some(104749)
        );
        assert_eq!(match_menu_window(42, &frame, &[]), None);
        assert_eq!(
            match_menu_window(42, &frame, &[candidate.clone(), candidate.clone()]),
            None
        );
        for mutation in 0..6 {
            let mut invalid = candidate.clone();
            match mutation {
                0 => invalid.pid = 99,
                1 => invalid.layer = 0,
                2 => invalid.is_on_screen = false,
                3 => invalid.on_current_space = Some(false),
                4 => invalid.bounds.x += 1.0,
                _ => invalid.window_id = 0,
            }
            assert_eq!(
                match_menu_window(42, &frame, &[invalid]),
                None,
                "mutation {mutation}"
            );
        }
        for invalid in [[f64::NAN, 699.0, 116.0, 153.0], [1035.0, 699.0, 0.0, 153.0]] {
            assert_eq!(match_menu_window(42, &invalid, &[candidate.clone()]), None);
        }
    }
    #[test]
    fn calendar_fields_and_choices_keep_their_attached_popover_identity() {
        // T022: Calendar exposes a title field and calendar choice in its
        // host tree while their physical window remains the AXPopover.
        for role in [
            "AXTextField",
            "AXTextArea",
            "AXPopUpButton",
            "AXCheckBox",
            "AXRadioButton",
        ] {
            for logical_window in [2, 6] {
                let mut tree = pages();
                tree.nodes.get_mut(&0).unwrap().role = role;
                tree.nodes.get_mut(&0).unwrap().window = Some(logical_window);
                assert!(
                    prove(&tree, 42, 700, &0),
                    "{role}, logical window {logical_window}"
                );
                assert!(requires_host_attachment(Some(role), Some(900), 700, || {
                    Some(900)
                }));
                assert!(
                    !requires_host_attachment(Some(role), Some(900), 700, || Some(700)),
                    "an accessory field belonging to the exact sheet keeps its ordinary route"
                );
                tree.nodes.get_mut(&2).unwrap().window = Some(8);
                assert!(
                    !prove(&tree, 42, 700, &0),
                    "changed attachment must refuse {role}"
                );
            }
        }
    }
    #[test]
    fn calendar_text_field_proof_rejects_missing_child_edges_and_foreign_nodes() {
        for changed in 0..=6 {
            let mut tree = pages();
            tree.nodes.get_mut(&0).unwrap().role = "AXTextField";
            tree.nodes.get_mut(&changed).unwrap().owner = 99;
            assert!(!prove(&tree, 42, 700, &0), "foreign node {changed}");
        }
        for changed in 1..=6 {
            let mut tree = pages();
            tree.nodes.get_mut(&0).unwrap().role = "AXTextField";
            tree.nodes.get_mut(&changed).unwrap().children.clear();
            assert!(!prove(&tree, 42, 700, &0), "detached node {changed}");
        }
    }
    #[test]
    fn calendar_field_confirm_and_choice_press_require_the_advertised_action() {
        assert_eq!(
            advertised_action(Some("AXTextField"), "confirm", &["AXConfirm".into()]),
            Some("AXConfirm")
        );
        assert_eq!(
            advertised_action(Some("AXTextField"), "confirm", &["AXShowMenu".into()]),
            None
        );
        assert_eq!(
            advertised_action(Some("AXPopUpButton"), "press", &["AXPress".into()]),
            Some("AXPress")
        );
        assert_eq!(
            advertised_action(Some("AXTextField"), "press", &["AXConfirm".into()]),
            None
        );
    }
    #[test]
    fn popover_root_proves_its_own_attachment_for_direct_cancel() {
        assert!(prove(&pages(), 42, 700, &2));
        // The physical popover is not interchangeable with its host.
        assert!(!prove(&pages(), 42, 900, &2));
        assert!(!prove(&pages(), 42, 701, &2));
        for i in 2..=6 {
            let mut tree = pages();
            tree.nodes.get_mut(&i).unwrap().owner = 99;
            assert!(!prove(&tree, 42, 700, &2), "foreign ancestor {i}");
        }
        for i in 3..=6 {
            let mut tree = pages();
            tree.nodes.get_mut(&i).unwrap().children.clear();
            assert!(!prove(&tree, 42, 700, &2), "detached ancestor {i}");
        }
        let mut tree = pages();
        tree.reattach = true;
        assert!(!prove(&tree, 42, 700, &2));
        let mut tree = pages();
        tree.nodes.get_mut(&2).unwrap().id = None;
        assert!(!prove(&tree, 42, 700, &2));
        let mut tree = pages();
        tree.nodes.get_mut(&2).unwrap().window = None;
        assert!(!prove(&tree, 42, 700, &2));
    }
    #[test]
    fn refusal_diagnostics_distinguish_attachment_and_ancestry_failures() {
        let mut tree = pages();
        tree.nodes.get_mut(&2).unwrap().window = None;
        assert_eq!(
            prove_checked(&tree, 42, 700, &0),
            Err("popover_host_attribute_missing")
        );
        let mut tree = pages();
        tree.nodes.get_mut(&3).unwrap().children.clear();
        assert_eq!(
            prove_checked(&tree, 42, 700, &0),
            Err("ancestor_child_relation_missing")
        );
        assert_eq!(
            prove_checked(&pages(), 42, 701, &0),
            Err("host_window_id_mismatch")
        );
    }
    #[test]
    fn exact_popover_window_keeps_ordinary_route() {
        assert!(!requires_host_attachment(
            Some("AXPopover"),
            Some(900),
            900,
            || panic!("exact physical surface needs no ancestry read")
        ));
        assert!(requires_host_attachment(
            Some("AXPopover"),
            Some(900),
            700,
            || Some(900)
        ));
        assert!(!requires_host_attachment(
            Some("AXPopover"),
            None,
            700,
            || panic!("unmapped surface needs no classification read")
        ));
        // Classification only. A displaced physical window still needs a
        // separate, reciprocal AXPopover attachment before any action.
        assert!(requires_host_attachment(
            Some("AXButton"),
            Some(900),
            700,
            || Some(900)
        ));
        assert!(!requires_host_attachment(
            Some("AXWindow"),
            Some(900),
            700,
            || panic!("non-candidate needs no ancestry read")
        ));
        assert!(!requires_host_attachment(
            Some("AXWindow"),
            Some(700),
            700,
            || panic!("non-candidate needs no ancestry read")
        ));
    }
    #[test]
    fn accessory_button_in_exact_sheet_uses_the_descendant_semantic_route() {
        use cua_driver_core::background_input::{
            decide_background_input, BackgroundAction, BackgroundTargetFacts, ElementAncestry,
            ExactWindowTarget, WindowServerOwnership,
        };
        // H056: native button 103307 -> AXSplitGroup -> AXSheet 103306 ->
        // document 103289. Fresh exact-target facts already prove the sheet.
        let target = ExactWindowTarget {
            pid: 42,
            window_id: 103306,
        };
        let facts = BackgroundTargetFacts {
            window_server: WindowServerOwnership::SamePid,
            ax_window_present: true,
            target_minimized: Some(false),
            app_hidden: Some(false),
            competing_keyboard_destinations: 2,
            element: ElementAncestry::ProvenDescendant,
        };
        let action =
            if requires_host_attachment(Some("AXButton"), Some(103307), target.window_id, || {
                Some(103306)
            }) {
                BackgroundAction::AttachedPopoverSemantic
            } else {
                BackgroundAction::AxSemantic
            };
        assert!(decide_background_input(target, &facts, action).is_execute());
        // The old physical-ID classification chose this incompatible route.
        assert!(!decide_background_input(
            target,
            &facts,
            BackgroundAction::AttachedPopoverSemantic
        )
        .is_execute());
        for other_or_unknown in [None, Some(103289), Some(103308)] {
            assert!(requires_host_attachment(
                Some("AXButton"),
                Some(103307),
                target.window_id,
                || other_or_unknown,
            ));
        }
    }
    fn wrapped_toolbar_popover() -> Tree {
        let mut tree = pages();
        tree.nodes.get_mut(&0).unwrap().window = Some(6);
        tree.nodes.get_mut(&3).unwrap().role = "AXButton";
        tree.nodes.get_mut(&4).unwrap().role = "AXToolbar";
        tree.nodes.insert(
            9,
            Node {
                identity: 9,
                role: "AXWindow",
                owner: 42,
                window: None,
                id: Some(900),
                parent: None,
                children: vec![],
            },
        );
        tree
    }
    #[test]
    fn logical_host_window_does_not_hide_a_physical_toolbar_popover() {
        assert!(prove(&wrapped_toolbar_popover(), 42, 700, &0));
        assert!(prove(&wrapped_toolbar_popover(), 42, 700, &2));
        assert!(!prove(&wrapped_toolbar_popover(), 42, 701, &0));
    }
    #[test]
    fn logical_host_requires_matching_physical_popover_and_exact_identity() {
        for id in [None, Some(700), Some(901)] {
            let mut tree = wrapped_toolbar_popover();
            tree.nodes.get_mut(&0).unwrap().id = id;
            assert!(!prove(&tree, 42, 700, &0));
        }
        let mut tree = wrapped_toolbar_popover();
        tree.nodes.get_mut(&6).unwrap().owner = 99;
        assert!(!prove(&tree, 42, 700, &0));
        for role in ["AXSheet", "AXApplication", "AXWebArea", "AXGroup"] {
            let mut tree = wrapped_toolbar_popover();
            tree.nodes.get_mut(&0).unwrap().window = Some(9);
            tree.nodes.get_mut(&9).unwrap().role = role;
            assert!(!prove(&tree, 42, 700, &0), "wrapper {role}");
        }
        let mut tree = wrapped_toolbar_popover();
        tree.nodes.get_mut(&0).unwrap().window = Some(9);
        assert!(!prove(&tree, 42, 700, &0), "unrelated AXWindow wrapper");
    }
    #[test]
    fn wrapper_never_substitutes_for_a_live_attached_popover() {
        for role in [
            "AXWindow",
            "AXSheet",
            "AXApplication",
            "AXWebArea",
            "AXUnknown",
        ] {
            let mut tree = wrapped_toolbar_popover();
            tree.nodes.get_mut(&2).unwrap().role = role;
            assert!(!prove(&tree, 42, 700, &0), "ancestor {role}");
        }
        for i in 1..=6 {
            let mut tree = wrapped_toolbar_popover();
            tree.nodes.get_mut(&i).unwrap().children.clear();
            assert!(!prove(&tree, 42, 700, &0), "detached ancestor {i}");
        }
        let mut tree = wrapped_toolbar_popover();
        tree.reattach = true;
        assert!(!prove(&tree, 42, 700, &0));
        let tree = wrapped_toolbar_popover();
        tree.budget.set(2);
        assert!(!prove(&tree, 42, 700, &0));
    }
    #[test]
    fn equivalent_proxy_identity_is_accepted() {
        let mut tree = pages();
        tree.nodes.insert(9, tree.nodes[&0].clone());
        assert!(prove(&tree, 42, 700, &9));
    }
    #[test]
    fn wrong_host_and_foreign_nodes_are_refused() {
        assert!(!prove(&pages(), 42, 701, &0));
        for i in 0..=6 {
            let mut tree = pages();
            tree.nodes.get_mut(&i).unwrap().owner = 99;
            assert!(!prove(&tree, 42, 700, &0), "foreign node {i}");
        }
    }
    #[test]
    fn detached_and_missing_relations_are_refused() {
        for i in 1..=6 {
            let mut tree = pages();
            tree.nodes.get_mut(&i).unwrap().children.clear();
            assert!(!prove(&tree, 42, 700, &0), "detached node {i}");
        }
        for i in 0..6 {
            let mut tree = pages();
            tree.nodes.get_mut(&i).unwrap().parent = None;
            assert!(!prove(&tree, 42, 700, &0));
        }
        let mut tree = pages();
        tree.nodes.get_mut(&2).unwrap().window = None;
        assert!(!prove(&tree, 42, 700, &0));
    }
    #[test]
    fn cycles_and_deadlines_are_refused() {
        let mut tree = pages();
        tree.nodes.get_mut(&3).unwrap().parent = Some(1);
        tree.nodes.get_mut(&1).unwrap().children.push(3);
        assert!(!prove(&tree, 42, 700, &0));
        for budget in [0, 3, 7] {
            let tree = pages();
            tree.budget.set(budget);
            assert!(!prove(&tree, 42, 700, &0));
        }
    }
    #[test]
    fn excessive_depth_is_refused() {
        let mut tree = pages();
        tree.nodes.get_mut(&3).unwrap().parent = Some(10);
        let last = 10 + MAX_DEPTH as u32;
        tree.nodes.get_mut(&4).unwrap().children = vec![last];
        for i in 10..=last {
            tree.nodes.insert(
                i,
                Node {
                    identity: i,
                    role: "AXGroup",
                    owner: 42,
                    window: Some(6),
                    id: Some(700),
                    parent: Some(if i == last { 4 } else { i + 1 }),
                    children: vec![if i == 10 { 3 } else { i - 1 }],
                },
            );
        }
        assert!(!prove(&tree, 42, 700, &0));
    }
    #[test]
    fn attachment_change_and_non_popover_paths_are_refused() {
        let mut tree = pages();
        tree.reattach = true;
        assert!(!prove(&tree, 42, 700, &0));
        for role in [
            "AXWindow",
            "AXSheet",
            "AXApplication",
            "AXWebArea",
            "AXUnknown",
        ] {
            let mut tree = pages();
            tree.nodes.get_mut(&3).unwrap().role = role;
            assert!(!prove(&tree, 42, 700, &0), "{role}");
        }
        let mut tree = pages();
        tree.nodes.get_mut(&2).unwrap().role = "AXGroup";
        assert!(!prove(&tree, 42, 700, &0));
    }
    #[test]
    fn only_advertised_direct_semantic_actions_are_allowed() {
        assert_eq!(
            advertised_action(Some("AXButton"), "press", &["AXPress".into()]),
            Some("AXPress")
        );
        assert_eq!(
            advertised_action(Some("AXButton"), "pick", &["AXPick".into()]),
            Some("AXPick")
        );
        for action in ["focus", "confirm", "set_value", "type_text", "unknown"] {
            assert_eq!(
                advertised_action(Some("AXButton"), action, &["AXPress".into()]),
                None
            );
        }
        assert_eq!(
            advertised_action(Some("AXButton"), "press", &["AXShowMenu".into()]),
            None
        );
    }
    #[test]
    fn popover_root_only_accepts_explicitly_advertised_cancel() {
        assert_eq!(
            advertised_action(Some("AXPopover"), "cancel", &["AXCancel".into()]),
            Some("AXCancel")
        );
        assert_eq!(advertised_action(Some("AXPopover"), "cancel", &[]), None);
        for role in [Some("AXButton"), Some("AXWindow"), Some("AXSheet"), None] {
            assert_eq!(
                advertised_action(role, "cancel", &["AXCancel".into()]),
                None
            );
        }
        for action in ["press", "click", "pick", "show_menu", "focus", "confirm"] {
            assert_eq!(
                advertised_action(
                    Some("AXPopover"),
                    action,
                    &["AXPress".into(), "AXCancel".into()]
                ),
                None
            );
        }
    }
}
