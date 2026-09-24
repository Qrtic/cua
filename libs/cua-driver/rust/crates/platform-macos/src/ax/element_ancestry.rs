//! Resolve the nearest AX window/sheet, rather than a sheet's document host.
//!
//! AppKit controls in a sheet can expose AXWindow = the document while their
//! AXParent chain reaches a distinct AXSheet first. The nearest native surface
//! is the input owner. An unmappable sheet is not permission to use its host.

use super::bindings::{
    ax_get_window_id, copy_element_attr, copy_string_attr, kAXErrorSuccess, AXUIElementGetPid,
    AXUIElementRef, AXUIElementSetMessagingTimeout,
};
use core_foundation::base::{CFEqual, CFRelease, CFRetain, CFTypeRef};
use std::time::{Duration, Instant};

const MAX_DEPTH: usize = 40;

trait Ancestry {
    type Node: Clone;
    fn role(&self, node: &Self::Node) -> Option<String>;
    fn owner(&self, node: &Self::Node) -> Option<i32>;
    fn window_id(&self, node: &Self::Node) -> Option<u32>;
    fn relation(&self, node: &Self::Node, name: &str) -> Option<Self::Node>;
    fn same(&self, a: &Self::Node, b: &Self::Node) -> bool;
    fn within_budget(&self) -> bool;
}

fn resolve<T: Ancestry>(tree: &T, start: &T::Node) -> Option<u32> {
    let pid = tree.owner(start)?;
    let mut node = start.clone();
    let mut visited = Vec::new();
    for _ in 0..MAX_DEPTH {
        if !tree.within_budget()
            || visited.iter().any(|prior| tree.same(prior, &node))
            || tree.owner(&node) != Some(pid)
        {
            return None;
        }
        let role = tree.role(&node)?;
        match role.as_str() {
            "AXWindow" | "AXSheet" => return tree.window_id(&node),
            "AXApplication" => return None,
            _ => {}
        }
        let Some(parent) = tree.relation(&node, "AXParent") else {
            // Some accessibility implementations omit parent links. Retain
            // the existing direct AXWindow proof only when no nearer surface
            // was encountered, never after an unmappable sheet or a cycle.
            let window = tree.relation(start, "AXWindow")?;
            return (tree.within_budget() && tree.owner(&window) == Some(pid))
                .then(|| tree.window_id(&window))
                .flatten();
        };
        visited.push(node);
        node = parent;
    }
    None
}

struct Node(AXUIElementRef);
impl Clone for Node {
    fn clone(&self) -> Self {
        unsafe { CFRetain(self.0 as CFTypeRef) };
        Self(self.0)
    }
}
impl Drop for Node {
    fn drop(&mut self) {
        unsafe { CFRelease(self.0 as CFTypeRef) };
    }
}
struct Native(Instant);
impl Ancestry for Native {
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
    fn relation(&self, node: &Node, name: &str) -> Option<Node> {
        unsafe {
            let related = Node(copy_element_attr(node.0, name)?);
            (AXUIElementSetMessagingTimeout(related.0, 0.1) == kAXErrorSuccess).then_some(related)
        }
    }
    fn same(&self, a: &Node, b: &Node) -> bool {
        unsafe { CFEqual(a.0 as CFTypeRef, b.0 as CFTypeRef) != 0 }
    }
    fn within_budget(&self) -> bool {
        Instant::now() < self.0
    }
}

/// # Safety
/// `element` is a live retained AX reference with its caller's bounded messaging
/// timeout for the duration of the call.
pub(super) unsafe fn window_id(element: AXUIElementRef) -> Option<u32> {
    CFRetain(element as CFTypeRef);
    let node = Node(element);
    // The observation retains this exact object for the later action. Lowering
    // its per-object timeout here also lowers AXPress's timeout and can report
    // CannotComplete while an AppKit sheet is already opening/closing. Bound
    // newly copied ancestors, but preserve the caller's timeout on the start.
    resolve(&Native(Instant::now() + Duration::from_secs(1)), &node)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    struct Tree {
        // role, parent, AXWindow, native window ID, owning process
        nodes: HashMap<u8, (&'static str, Option<u8>, Option<u8>, Option<u32>, i32)>,
    }
    impl Ancestry for Tree {
        type Node = u8;
        fn role(&self, n: &u8) -> Option<String> {
            self.nodes.get(n).map(|r| r.0.into())
        }
        fn owner(&self, n: &u8) -> Option<i32> {
            self.nodes.get(n).map(|r| r.4)
        }
        fn window_id(&self, n: &u8) -> Option<u32> {
            self.nodes.get(n).and_then(|r| r.3)
        }
        fn relation(&self, n: &u8, name: &str) -> Option<u8> {
            self.nodes
                .get(n)
                .and_then(|r| if name == "AXParent" { r.1 } else { r.2 })
        }
        fn same(&self, a: &u8, b: &u8) -> bool {
            a == b
        }
        fn within_budget(&self) -> bool {
            true
        }
    }
    fn sheet() -> Tree {
        Tree {
            nodes: HashMap::from([
                (0, ("AXButton", Some(1), Some(2), None, 42)),
                (1, ("AXSheet", Some(2), Some(2), Some(8), 42)),
                (2, ("AXWindow", Some(3), None, Some(7), 42)),
                (3, ("AXApplication", None, None, None, 42)),
            ]),
        }
    }
    #[test]
    fn sheet_controls_and_sheet_itself_belong_to_sheet_not_document() {
        let t = sheet();
        assert_eq!(resolve(&t, &0), Some(8));
        assert_eq!(resolve(&t, &1), Some(8));
        assert_eq!(resolve(&t, &2), Some(7));
    }
    #[test]
    fn unmappable_sheet_never_inherits_its_document_id() {
        let mut t = sheet();
        t.nodes.get_mut(&1).unwrap().3 = None;
        assert_eq!(resolve(&t, &0), None);
    }
    #[test]
    fn sibling_sheet_is_not_the_requested_sheet() {
        let mut t = sheet();
        t.nodes.get_mut(&1).unwrap().3 = Some(9);
        assert_eq!(resolve(&t, &0), Some(9));
        assert_ne!(resolve(&t, &0), Some(8));
    }
    #[test]
    fn ordinary_controls_and_parentless_direct_proof_still_work() {
        let mut t = sheet();
        t.nodes.get_mut(&0).unwrap().1 = Some(2);
        assert_eq!(resolve(&t, &0), Some(7));
        t.nodes.get_mut(&0).unwrap().1 = None;
        assert_eq!(resolve(&t, &0), Some(7));
    }
    #[test]
    fn cycles_foreign_parents_and_application_menus_fail_closed() {
        let mut t = sheet();
        t.nodes.get_mut(&0).unwrap().1 = Some(0);
        assert_eq!(resolve(&t, &0), None);
        t.nodes.get_mut(&0).unwrap().1 = Some(1);
        t.nodes.get_mut(&1).unwrap().4 = 99;
        assert_eq!(resolve(&t, &0), None);
        t.nodes.get_mut(&0).unwrap().1 = Some(3);
        assert_eq!(resolve(&t, &0), None);
    }
}
