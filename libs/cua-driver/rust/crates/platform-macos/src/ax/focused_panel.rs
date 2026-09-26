//! Discover a native focused panel omitted from AXWindows while inactive.
//!
//! AppKit's floating chart editor keeps AXFocusedWindow and its focused text
//! control readable after deactivation, but drops the panel from AXWindows and
//! AXChildren. The application's explicit focus relation, reciprocal AXParent,
//! focused control's exact AXWindow, and live WindowServer owner establish this
//! panel's identity without activating its document host. This is discovery,
//! not a visibility exception or permission to redirect input to another window.

use super::bindings::{
    ax_get_window_id, copy_element_attr, copy_string_attr, kAXErrorSuccess,
    AXUIElementCreateApplication, AXUIElementGetPid, AXUIElementRef,
    AXUIElementSetMessagingTimeout,
};
use core_foundation::base::{CFEqual, CFRelease, CFRetain, CFTypeRef};
use std::time::{Duration, Instant};

trait PanelTree {
    type Node: Clone;
    fn app(&self) -> &Self::Node;
    fn relation(&self, node: &Self::Node, name: &str) -> Option<Self::Node>;
    fn role(&self, node: &Self::Node) -> Option<String>;
    fn subrole(&self, node: &Self::Node) -> Option<String>;
    fn owner(&self, node: &Self::Node) -> Option<i32>;
    fn window_id(&self, node: &Self::Node) -> Option<u32>;
    fn same(&self, left: &Self::Node, right: &Self::Node) -> bool;
    fn owns_window(&self, pid: i32, window_id: u32) -> bool;
    fn within_budget(&self) -> bool;
}

fn native_focus_role(role: Option<&str>) -> bool {
    matches!(
        role,
        Some(
            "AXTextArea"
                | "AXTextField"
                | "AXButton"
                | "AXCheckBox"
                | "AXRadioButton"
                | "AXPopUpButton"
                | "AXCell"
                | "AXTable"
                | "AXOutline"
        )
    )
}

fn prove<T: PanelTree>(tree: &T, pid: i32, requested: Option<u32>) -> Option<T::Node> {
    let app = tree.app();
    let panel = tree.relation(app, "AXFocusedWindow")?;
    // Ordinary windows, web surfaces, sheets and unidentified popup surfaces
    // retain their existing discovery/attachment paths.
    if tree.role(&panel).as_deref() != Some("AXWindow")
        || tree.subrole(&panel).as_deref() != Some("AXDialog")
    {
        return None;
    }
    let id = tree.window_id(&panel)?;
    if pid <= 0 || id == 0 || requested.is_some_and(|expected| expected != id) {
        return None;
    }
    let focused = tree.relation(app, "AXFocusedUIElement")?;
    if !native_focus_role(tree.role(&focused).as_deref()) {
        return None;
    }
    // Read both relations twice. A stale focus value, a retargeted editor, an
    // app replacement or a sibling's AXWindow cannot inherit this discovery.
    for _ in 0..2 {
        if !tree.within_budget()
            || tree.owner(app) != Some(pid)
            || tree.owner(&panel) != Some(pid)
            || tree.owner(&focused) != Some(pid)
            || tree.window_id(&panel) != Some(id)
            || tree.window_id(&focused) != Some(id)
            || !tree.owns_window(pid, id)
            || !tree
                .relation(&panel, "AXParent")
                .is_some_and(|p| tree.same(&p, app))
            || !tree
                .relation(&focused, "AXWindow")
                .is_some_and(|p| tree.same(&p, &panel))
            || !tree
                .relation(app, "AXFocusedWindow")
                .is_some_and(|p| tree.same(&p, &panel))
            || !tree
                .relation(app, "AXFocusedUIElement")
                .is_some_and(|p| tree.same(&p, &focused))
        {
            return None;
        }
    }
    tree.within_budget().then_some(panel)
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
    fn into_raw(self) -> AXUIElementRef {
        std::mem::ManuallyDrop::new(self).0
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
    app: Node,
    deadline: Instant,
}
impl PanelTree for NativeTree {
    type Node = Node;
    fn app(&self) -> &Node {
        &self.app
    }
    fn relation(&self, node: &Node, name: &str) -> Option<Node> {
        if !self.within_budget() {
            return None;
        }
        unsafe { Node::owned(copy_element_attr(node.0, name)?) }
    }
    fn role(&self, node: &Node) -> Option<String> {
        unsafe { copy_string_attr(node.0, "AXRole") }
    }
    fn subrole(&self, node: &Node) -> Option<String> {
        unsafe { copy_string_attr(node.0, "AXSubrole") }
    }
    fn owner(&self, node: &Node) -> Option<i32> {
        let mut pid = 0;
        (unsafe { AXUIElementGetPid(node.0, &mut pid) } == kAXErrorSuccess).then_some(pid)
    }
    fn window_id(&self, node: &Node) -> Option<u32> {
        unsafe { ax_get_window_id(node.0) }
    }
    fn same(&self, left: &Node, right: &Node) -> bool {
        unsafe { CFEqual(left.0 as CFTypeRef, right.0 as CFTypeRef) != 0 }
    }
    fn owns_window(&self, pid: i32, window_id: u32) -> bool {
        matches!(
            crate::windows::resolve_window_owner(pid, window_id),
            crate::windows::WindowOwner::SamePid
        )
    }
    fn within_budget(&self) -> bool {
        Instant::now() < self.deadline
    }
}

/// Retained, exact native panel; caller must CFRelease. No activation or input.
/// `requested = None` discovers at most the single app-focused panel so that
/// background keyboard ambiguity also accounts for a floating sibling.
pub(crate) fn copy_focused_panel(pid: i32, requested: Option<u32>) -> Option<AXUIElementRef> {
    unsafe {
        let app = Node::owned(AXUIElementCreateApplication(pid))?;
        prove(
            &NativeTree {
                app,
                deadline: Instant::now() + Duration::from_millis(750),
            },
            pid,
            requested,
        )
        .map(Node::into_raw)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::collections::HashMap;

    struct Fake {
        app: usize,
        nodes: HashMap<usize, (&'static str, &'static str, i32, Option<u32>)>,
        links: HashMap<(usize, &'static str), usize>,
        owner_live: bool,
        within_budget: bool,
        focus_reads: Cell<usize>,
        change_focus_after: usize,
    }
    impl Fake {
        fn panel() -> Self {
            Self {
                app: 0,
                nodes: HashMap::from([
                    (0, ("AXApplication", "", 42, None)),
                    (1, ("AXWindow", "AXDialog", 42, Some(99))),
                    (2, ("AXTextArea", "", 42, Some(99))),
                    (3, ("AXWindow", "AXStandardWindow", 42, Some(7))),
                ]),
                links: HashMap::from([
                    ((0, "AXFocusedWindow"), 1),
                    ((0, "AXFocusedUIElement"), 2),
                    ((1, "AXParent"), 0),
                    ((2, "AXWindow"), 1),
                ]),
                owner_live: true,
                within_budget: true,
                focus_reads: Cell::new(0),
                change_focus_after: usize::MAX,
            }
        }
    }
    impl PanelTree for Fake {
        type Node = usize;
        fn app(&self) -> &usize {
            &self.app
        }
        fn relation(&self, node: &usize, name: &str) -> Option<usize> {
            if name == "AXFocusedWindow" {
                let count = self.focus_reads.get() + 1;
                self.focus_reads.set(count);
                if count > self.change_focus_after {
                    return Some(3);
                }
            }
            self.links.get(&(*node, name)).copied()
        }
        fn role(&self, node: &usize) -> Option<String> {
            self.nodes.get(node).map(|n| n.0.into())
        }
        fn subrole(&self, node: &usize) -> Option<String> {
            self.nodes.get(node).map(|n| n.1.into())
        }
        fn owner(&self, node: &usize) -> Option<i32> {
            self.nodes.get(node).map(|n| n.2)
        }
        fn window_id(&self, node: &usize) -> Option<u32> {
            self.nodes.get(node).and_then(|n| n.3)
        }
        fn same(&self, a: &usize, b: &usize) -> bool {
            a == b
        }
        fn owns_window(&self, pid: i32, id: u32) -> bool {
            self.owner_live && pid == 42 && id == 99
        }
        fn within_budget(&self) -> bool {
            self.within_budget
        }
    }

    #[test]
    fn discovers_app_focused_native_panel_without_axwindows_or_activation() {
        let tree = Fake::panel();
        assert_eq!(prove(&tree, 42, Some(99)), Some(1));
        assert_eq!(prove(&tree, 42, None), Some(1));
        assert_eq!(prove(&tree, 42, Some(7)), None);
    }
    #[test]
    fn foreign_owner_or_sibling_focus_never_supplies_exact_panel() {
        for node in [0, 1, 2] {
            let mut tree = Fake::panel();
            tree.nodes.get_mut(&node).unwrap().2 = 43;
            assert_eq!(prove(&tree, 42, Some(99)), None);
        }
        for key in [(1, "AXParent"), (2, "AXWindow"), (0, "AXFocusedUIElement")] {
            let mut tree = Fake::panel();
            tree.links.insert(key, 3);
            assert_eq!(prove(&tree, 42, Some(99)), None);
        }
    }
    #[test]
    fn missing_or_reused_physical_id_and_closed_window_are_rejected() {
        for id in [None, Some(0), Some(7)] {
            for node in [1, 2] {
                let mut tree = Fake::panel();
                tree.nodes.get_mut(&node).unwrap().3 = id;
                assert_eq!(prove(&tree, 42, Some(99)), None);
            }
        }
        let mut tree = Fake::panel();
        tree.owner_live = false;
        assert_eq!(prove(&tree, 42, Some(99)), None);
    }
    #[test]
    fn a_normal_window_web_surface_or_sheet_cannot_use_panel_discovery() {
        for (node, role, subrole) in [
            (1, "AXWindow", "AXStandardWindow"),
            (1, "AXSheet", "AXDialog"),
            (1, "AXWebArea", "AXDialog"),
            (2, "AXWebArea", ""),
        ] {
            let mut tree = Fake::panel();
            let entry = tree.nodes.get_mut(&node).unwrap();
            entry.0 = role;
            entry.1 = subrole;
            assert_eq!(prove(&tree, 42, Some(99)), None);
        }
    }
    #[test]
    fn focus_change_missing_relationship_or_deadline_fails_closed() {
        for after in [0, 1, 2] {
            let mut tree = Fake::panel();
            tree.change_focus_after = after;
            assert_eq!(prove(&tree, 42, Some(99)), None);
        }
        for key in [(1, "AXParent"), (2, "AXWindow"), (0, "AXFocusedUIElement")] {
            let mut tree = Fake::panel();
            tree.links.remove(&key);
            assert_eq!(prove(&tree, 42, Some(99)), None);
        }
        let mut tree = Fake::panel();
        tree.within_budget = false;
        assert_eq!(prove(&tree, 42, Some(99)), None);
    }
}
