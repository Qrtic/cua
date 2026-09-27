//! Resolve the nearest AX window, sheet or popover, rather than its host.
//!
//! AppKit controls in a sheet can expose AXWindow = the document while their
//! AXParent chain reaches a distinct AXSheet first. The same rule applies to
//! attached AXPopovers: their semantic route must prove attachment to the host,
//! not silently inherit the host's identity. An unmappable surface is not
//! permission to use its host.
//!
//! ExtensionKit may vend a control from a different process than its containing
//! sheet. Such an embedding needs a live, reciprocal parent chain and a verified
//! WindowServer owner; a foreign AXWindow attribute alone is never sufficient.
//! AppKit file-panel accessories can instead start in the host, traverse one
//! remote service, then return to the host's window or sheet. That bounded round trip has
//! its own reciprocal proof; it does not authorize arbitrary provider chains.

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

const MAX_DEPTH: usize = 40;

trait Ancestry {
    type Node: Clone;
    fn role(&self, node: &Self::Node) -> Option<String>;
    fn owner(&self, node: &Self::Node) -> Option<i32>;
    fn window_id(&self, node: &Self::Node) -> Option<u32>;
    fn relation(&self, node: &Self::Node, name: &str) -> Option<Self::Node>;
    fn contains_child(&self, parent: &Self::Node, child: &Self::Node) -> bool;
    fn owns_window(&self, pid: i32, window_id: u32) -> bool;
    fn same(&self, a: &Self::Node, b: &Self::Node) -> bool;
    fn within_budget(&self) -> bool;
}

fn resolve<T: Ancestry>(tree: &T, start: &T::Node) -> Option<u32> {
    resolve_with_window_fallback(tree, start, true)
}

fn resolve_with_window_fallback<T: Ancestry>(
    tree: &T,
    start: &T::Node,
    allow_window_attribute: bool,
) -> Option<u32> {
    resolve_same_process(tree, start, allow_window_attribute)
        .or_else(|| resolve_embedded_control(tree, start))
}

fn resolve_same_process<T: Ancestry>(
    tree: &T,
    start: &T::Node,
    allow_window_attribute: bool,
) -> Option<u32> {
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
            "AXWindow" | "AXSheet" | "AXPopover" => return tree.window_id(&node),
            "AXApplication" => return None,
            _ => {}
        }
        let Some(parent) = tree.relation(&node, "AXParent") else {
            if !allow_window_attribute {
                return None;
            }
            // Some accessibility implementations omit parent links. Retain
            // the existing direct AXWindow proof only when no nearer surface
            // was encountered, never after an unmappable sheet/popover or a cycle.
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

/// Prove one provider-to-host embedding without weakening the ordinary path.
/// All parent links must be reciprocal, including links inside the provider.
/// The first surface remains authoritative; neither its host nor a sibling can
/// inherit the control. Re-read the complete chain before returning the ID.
fn resolve_embedded_control<T: Ancestry>(tree: &T, start: &T::Node) -> Option<u32> {
    let provider = tree.owner(start)?;
    if provider <= 0 {
        return None;
    }
    let mut current = start.clone();
    let mut nodes: Vec<(T::Node, i32, String)> = Vec::new();
    let mut crossed_provider_boundary = false;
    for _ in 0..MAX_DEPTH {
        if !tree.within_budget() || nodes.iter().any(|(n, _, _)| tree.same(n, &current)) {
            return None;
        }
        let owner = tree.owner(&current)?;
        let role = tree.role(&current)?;
        if owner <= 0 {
            return None;
        }
        if let Some((_, previous_owner, _)) = nodes.last() {
            if owner != *previous_owner {
                if crossed_provider_boundary {
                    // Only the observed return to the original process may
                    // enter the accessory proof. A failed reciprocal link or
                    // a detached one-way embedding must not trigger a retry.
                    return (owner == provider)
                        .then(|| resolve_accessory_surface(tree, start))
                        .flatten();
                }
                if *previous_owner != provider || owner == provider {
                    return None;
                }
                crossed_provider_boundary = true;
            }
        }
        nodes.push((current.clone(), owner, role.clone()));
        match role.as_str() {
            "AXWindow" | "AXSheet" | "AXPopover" => {
                let id = tree.window_id(&current)?;
                if !crossed_provider_boundary || id == 0 || !tree.owns_window(owner, id) {
                    return None;
                }
                for (index, (node, observed_owner, observed_role)) in nodes.iter().enumerate() {
                    if !tree.within_budget()
                        || tree.owner(node) != Some(*observed_owner)
                        || tree.role(node).as_deref() != Some(observed_role.as_str())
                    {
                        return None;
                    }
                    if let Some((parent, _, _)) = nodes.get(index + 1) {
                        if !tree
                            .relation(node, "AXParent")
                            .is_some_and(|n| tree.same(&n, parent))
                            || !tree.contains_child(parent, node)
                        {
                            return None;
                        }
                    }
                }
                return (tree.within_budget()
                    && tree.window_id(&current) == Some(id)
                    && tree.owns_window(owner, id))
                .then_some(id);
            }
            "AXApplication" => return None,
            _ => {}
        }
        let parent = tree.relation(&current, "AXParent")?;
        if !tree.contains_child(&parent, &current) {
            return None;
        }
        current = parent;
    }
    None
}

/// AppKit can expose host-owned accessory controls below a remote file-panel
/// split group. Prove exactly host -> one service -> the same host's AXWindow
/// or AXSheet. Standalone file panels expose AXWindow rather than AXSheet.
/// No intervening surface, web subtree, extra provider, AXWindow attribute shortcut or
/// cached downward traversal can supply this relationship. Revalidate every
/// live link before returning, just as for the one-way provider embedding.
fn resolve_accessory_surface<T: Ancestry>(tree: &T, start: &T::Node) -> Option<u32> {
    let host = tree.owner(start)?;
    if host <= 0 {
        return None;
    }
    let mut remote = None;
    let mut returned_to_host = false;
    let mut current = start.clone();
    let mut nodes: Vec<(T::Node, i32, String)> = Vec::new();
    for _ in 0..MAX_DEPTH {
        if !tree.within_budget() || nodes.iter().any(|(node, _, _)| tree.same(node, &current)) {
            return None;
        }
        let owner = tree.owner(&current)?;
        let role = tree.role(&current)?;
        if owner <= 0 || matches!(role.as_str(), "" | "AXWebArea" | "AXApplication" | "AXPopover") {
            return None;
        }
        if owner == host {
            returned_to_host |= remote.is_some();
        } else {
            if returned_to_host || remote.is_some_and(|pid| pid != owner) {
                return None;
            }
            remote = Some(owner);
        }
        nodes.push((current.clone(), owner, role.clone()));
        if matches!(role.as_str(), "AXWindow" | "AXSheet") {
            let id = tree.window_id(&current)?;
            if remote.is_none() || !returned_to_host || owner != host || id == 0
                || !tree.owns_window(host, id)
            {
                return None;
            }
            for (index, (node, observed_owner, observed_role)) in nodes.iter().enumerate() {
                if !tree.within_budget() || tree.owner(node) != Some(*observed_owner)
                    || tree.role(node).as_deref() != Some(observed_role.as_str())
                {
                    return None;
                }
                if let Some((parent, _, _)) = nodes.get(index + 1) {
                    if !tree.relation(node, "AXParent").is_some_and(|live| tree.same(&live, parent))
                        || !tree.contains_child(parent, node)
                    {
                        return None;
                    }
                }
            }
            return (tree.within_budget() && tree.window_id(&current) == Some(id)
                && tree.owns_window(host, id)).then_some(id);
        }
        let parent = tree.relation(&current, "AXParent")?;
        if !tree.contains_child(&parent, &current) {
            return None;
        }
        current = parent;
    }
    None
}

/// A native text editor must have a complete reciprocal chain to the exact
/// physical surface. An AXWindow attribute alone cannot distinguish a native
/// field from a detached or incompletely exposed web input. This stricter
/// proof authorizes editor focus preparation, not a new pointer/keyboard route.
fn prove_native_text<T: Ancestry>(tree: &T, start: &T::Node, pid: i32, window_id: u32) -> bool {
    if tree.owner(start) != Some(pid)
        || !matches!(tree.role(start).as_deref(), Some("AXTextField" | "AXTextArea"))
    {
        return false;
    }
    let mut node = start.clone();
    let mut visited: Vec<(T::Node, String)> = Vec::new();
    for _ in 0..MAX_DEPTH {
        if !tree.within_budget()
            || visited.iter().any(|(prior, _)| tree.same(prior, &node))
        {
            return false;
        }
        if tree.owner(&node) != Some(pid) {
            // This may be the file-panel service on a host-owned accessory's
            // ancestry. The complete separate proof still requires the same
            // host, exact window/sheet and live reciprocal links, and rejects web
            // content. Ordinary same-process editors keep their fast path.
            return resolve_accessory_surface(tree, start) == Some(window_id);
        }
        let Some(role) = tree.role(&node).filter(|role| !role.is_empty()) else {
            return false;
        };
        match role.as_str() {
            "AXWebArea" | "AXApplication" => return false,
            "AXWindow" | "AXSheet" | "AXPopover" => {
                if tree.window_id(&node) != Some(window_id) || !tree.owns_window(pid, window_id) {
                    return false;
                }
                // Focus may follow immediately: do not authorize it from a
                // chain that detached while the remaining ancestors were read.
                for (index, (child, observed_role)) in visited.iter().enumerate() {
                    let parent = visited.get(index + 1).map_or(&node, |(parent, _)| parent);
                    if !tree.within_budget()
                        || tree.owner(child) != Some(pid)
                        || tree.role(child).as_deref() != Some(observed_role.as_str())
                        || !tree.relation(child, "AXParent").is_some_and(|live| tree.same(&live, parent))
                        || !tree.contains_child(parent, child)
                    {
                        return false;
                    }
                }
                return tree.within_budget()
                    && tree.owner(&node) == Some(pid)
                    && tree.role(&node).as_deref() == Some(role.as_str())
                    && tree.window_id(&node) == Some(window_id)
                    && tree.owns_window(pid, window_id);
            }
            _ => {}
        }
        let Some(parent) = tree.relation(&node, "AXParent") else {
            return false;
        };
        if !tree.contains_child(&parent, &node) {
            return false;
        }
        visited.push((node, role));
        node = parent;
    }
    false
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
    fn contains_child(&self, parent: &Node, child: &Node) -> bool {
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
            children.len() <= 1024
                && (0..children.len()).any(|index| {
                    CFEqual(
                        *children.get(index).expect("bounded index"),
                        child.0 as CFTypeRef,
                    ) != 0
                })
        }
    }
    fn owns_window(&self, pid: i32, window_id: u32) -> bool {
        matches!(
            crate::windows::resolve_window_owner(pid, window_id),
            crate::windows::WindowOwner::SamePid
        )
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
    native_window_id(element, true)
}

/// Resolve a surface through AXParent only. A displaced physical surface may
/// expose AXWindow = host even when its parent chain is missing; that attribute
/// alone must not downgrade an attached-popover route to an ordinary action.
///
/// # Safety
/// Same retained-element and messaging-timeout requirements as `window_id`.
pub(super) unsafe fn parent_window_id(element: AXUIElementRef) -> Option<u32> {
    native_window_id(element, false)
}

/// # Safety
/// The addressed element stays retained with a bounded AX messaging timeout.
pub(super) unsafe fn proves_native_text(element: AXUIElementRef, pid: i32, window_id: u32) -> bool {
    CFRetain(element as CFTypeRef);
    let node = Node(element);
    let tree = Native(Instant::now() + Duration::from_secs(1));
    prove_native_text(&tree, &node, pid, window_id)
}

unsafe fn native_window_id(element: AXUIElementRef, allow_window_attribute: bool) -> Option<u32> {
    CFRetain(element as CFTypeRef);
    let node = Node(element);
    // The observation retains this exact object for the later action. Lowering
    // its per-object timeout here also lowers AXPress's timeout and can report
    // CannotComplete while an AppKit sheet is already opening/closing. Bound
    // newly copied ancestors, but preserve the caller's timeout on the start.
    let tree = Native(Instant::now() + Duration::from_secs(1));
    if allow_window_attribute {
        resolve(&tree, &node)
    } else {
        resolve_with_window_fallback(&tree, &node, false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::collections::HashMap;

    struct Tree {
        // role, parent, AXWindow, native window ID, owning process
        nodes: HashMap<u8, (&'static str, Option<u8>, Option<u8>, Option<u32>, i32)>,
        children: HashMap<u8, Vec<u8>>,
        window_owners: HashMap<u32, i32>,
        child_checks: Cell<usize>,
        fail_child_check_after: Option<usize>,
        expire_after_child_checks: Option<usize>,
        expired: bool,
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
        fn contains_child(&self, parent: &u8, child: &u8) -> bool {
            self.child_checks.set(self.child_checks.get() + 1);
            !self
                .fail_child_check_after
                .is_some_and(|limit| self.child_checks.get() > limit)
                && self
                    .children
                    .get(parent)
                    .is_some_and(|children| children.contains(child))
        }
        fn owns_window(&self, pid: i32, window_id: u32) -> bool {
            self.window_owners.get(&window_id) == Some(&pid)
        }
        fn same(&self, a: &u8, b: &u8) -> bool {
            a == b
        }
        fn within_budget(&self) -> bool {
            !self.expired
                && !self
                    .expire_after_child_checks
                    .is_some_and(|limit| self.child_checks.get() >= limit)
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
            children: HashMap::from([(1, vec![0]), (2, vec![1]), (3, vec![2])]),
            window_owners: HashMap::from([(8, 42), (7, 42)]),
            child_checks: Cell::new(0),
            fail_child_check_after: None,
            expire_after_child_checks: None,
            expired: false,
        }
    }
    #[test]
    fn native_text_preparation_requires_the_exact_reciprocal_surface() {
        let mut t = sheet();
        t.nodes.get_mut(&0).unwrap().0 = "AXTextField";
        assert!(prove_native_text(&t, &0, 42, 8));
        assert!(!prove_native_text(&t, &0, 42, 7));
        t.nodes.get_mut(&0).unwrap().1 = Some(2);
        t.children.insert(2, vec![0, 1]);
        assert!(prove_native_text(&t, &0, 42, 7));
        t.nodes.get_mut(&0).unwrap().0 = "AXTextArea";
        assert!(prove_native_text(&t, &0, 42, 7));
        t.nodes.get_mut(&0).unwrap().1 = None;
        // A plausible AXWindow=7 still does not authorize editor focus.
        assert_eq!(resolve(&t, &0), Some(7));
        assert!(!prove_native_text(&t, &0, 42, 7));
    }

    #[test]
    fn native_text_preparation_rejects_web_unknown_detached_or_foreign_nodes() {
        for kind in 0..10 {
            let mut t = sheet();
            t.nodes.get_mut(&0).unwrap().0 = "AXTextField";
            match kind {
                0 => t.nodes.get_mut(&0).unwrap().0 = "AXButton",
                1 => t.nodes.get_mut(&1).unwrap().0 = "AXWebArea",
                2 => t.nodes.get_mut(&1).unwrap().0 = "AXApplication",
                3 => t.nodes.get_mut(&1).unwrap().0 = "",
                4 => t.nodes.get_mut(&1).unwrap().4 = 99,
                5 => { t.children.insert(1, Vec::new()); }
                6 => t.nodes.get_mut(&0).unwrap().1 = Some(0),
                7 => t.expired = true,
                8 => { t.window_owners.insert(8, 99); }
                _ => t.fail_child_check_after = Some(1),
            }
            assert!(!prove_native_text(&t, &0, 42, 8), "case {kind}");
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
    fn attached_popover_controls_keep_their_surface_identity() {
        let mut t = sheet();
        t.nodes.get_mut(&1).unwrap().0 = "AXPopover";
        // A host-directed semantic click must use the attachment proof rather
        // than the ordinary host-descendant route, even when AXWindow=host.
        assert_eq!(resolve(&t, &0), Some(8));
        assert_eq!(resolve(&t, &1), Some(8));
        assert_ne!(resolve(&t, &0), Some(7));
        // Some controls instead report AXWindow=popover. Parent traversal and
        // that attribute must produce the same surface identity.
        t.nodes.get_mut(&0).unwrap().2 = Some(1);
        assert_eq!(resolve(&t, &0), Some(8));
    }
    #[test]
    fn unmappable_popover_never_inherits_its_host_id() {
        let mut t = sheet();
        t.nodes.get_mut(&1).unwrap().0 = "AXPopover";
        t.nodes.get_mut(&1).unwrap().3 = None;
        assert_eq!(resolve(&t, &0), None);
        assert_eq!(resolve(&t, &1), None);
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
    fn displaced_surface_classification_requires_a_parent_chain_not_host_attribute() {
        let mut t = sheet();
        // TextEdit's Save/Cancel controls live on an accessory CGWindow while
        // their nearest logical surface is the requested save sheet.
        t.nodes.get_mut(&0).unwrap().3 = Some(9);
        assert_eq!(resolve_with_window_fallback(&t, &0, false), Some(8));
        // Keynote may expose AXWindow=host for a separate chart popover. A
        // missing parent must not turn that host attribute into sheet proof.
        t.nodes.get_mut(&0).unwrap().1 = None;
        assert_eq!(resolve(&t, &0), Some(7));
        assert_eq!(resolve_with_window_fallback(&t, &0, false), None);
        t.nodes.get_mut(&0).unwrap().1 = Some(1);
        t.nodes.get_mut(&1).unwrap().0 = "AXPopover";
        assert_eq!(resolve_with_window_fallback(&t, &0, false), Some(8));
        t.nodes.get_mut(&1).unwrap().3 = None;
        assert_eq!(resolve_with_window_fallback(&t, &0, false), None);
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

    #[test]
    fn remote_settings_controls_resolve_to_their_nearest_sheet() {
        let mut t = sheet();
        t.nodes.get_mut(&0).unwrap().0 = "AXTextField";
        t.nodes.get_mut(&0).unwrap().4 = 99;
        t.nodes.get_mut(&0).unwrap().2 = None;
        assert_eq!(resolve(&t, &0), Some(8));
        assert_eq!(resolve_with_window_fallback(&t, &0, false), Some(8));
        assert_ne!(resolve(&t, &0), Some(7));
    }

    fn save_panel_accessory() -> Tree {
        let mut tree = sheet();
        // AppKit vends the app-owned accessory through the remote file-panel
        // service's split group, then returns to the app-owned AXSheet. The
        // field itself has no native window or AXWindow attribute.
        tree.nodes.insert(0, ("AXTextField", Some(4), None, None, 42));
        tree.nodes.insert(4, ("AXSplitGroup", Some(1), None, Some(9), 99));
        tree.children.insert(4, vec![0]);
        tree.children.insert(1, vec![4]);
        tree.window_owners.insert(9, 42);
        tree
    }

    #[test]
    fn save_panel_accessory_resolves_reciprocal_return_to_its_own_sheet() {
        let tree = save_panel_accessory();
        assert_eq!(resolve(&tree, &0), Some(8));
        assert_eq!(resolve_with_window_fallback(&tree, &0, false), Some(8));
        assert_ne!(resolve(&tree, &0), Some(7));
        assert!(prove_native_text(&tree, &0, 42, 8));
        assert!(!prove_native_text(&tree, &0, 42, 7));
        assert!(!prove_native_text(&tree, &0, 99, 8));
    }

    #[test]
    fn save_panel_accessory_rejects_unproven_or_different_surfaces() {
        for kind in 0..10 {
            let mut tree = save_panel_accessory();
            match kind {
                0 => { tree.children.insert(4, vec![]); }
                1 => { tree.children.insert(1, vec![]); }
                2 => tree.nodes.get_mut(&1).unwrap().3 = None,
                3 => tree.nodes.get_mut(&1).unwrap().0 = "AXPopover",
                4 => tree.nodes.get_mut(&1).unwrap().0 = "AXApplication",
                5 => tree.nodes.get_mut(&4).unwrap().0 = "AXWebArea",
                6 => tree.nodes.get_mut(&4).unwrap().1 = Some(0),
                7 => tree.expired = true,
                8 => { tree.window_owners.insert(8, 99); }
                _ => tree.nodes.get_mut(&0).unwrap().1 = None,
            }
            assert_eq!(resolve(&tree, &0), None, "case {kind}");
            assert!(!prove_native_text(&tree, &0, 42, 8), "case {kind}");
        }
        let mut sibling = save_panel_accessory();
        sibling.nodes.get_mut(&1).unwrap().3 = Some(10);
        sibling.window_owners.insert(10, 42);
        assert_eq!(resolve(&sibling, &0), Some(10));
        assert!(!prove_native_text(&sibling, &0, 42, 8));
    }

    #[test]
    fn save_panel_accessory_requires_a_stable_single_remote_service() {
        let mut tree = save_panel_accessory();
        tree.nodes.get_mut(&4).unwrap().1 = Some(5);
        tree.nodes.insert(5, ("AXGroup", Some(1), None, None, 100));
        tree.children.insert(5, vec![4]);
        tree.children.insert(1, vec![5]);
        assert_eq!(resolve(&tree, &0), None);
        assert!(!prove_native_text(&tree, &0, 42, 8));
        // A return to the host followed by another remote segment is not the
        // single AppKit accessory bridge that this route proves.
        tree.nodes.insert(5, ("AXGroup", Some(6), None, None, 42));
        tree.nodes.insert(6, ("AXGroup", Some(1), None, None, 99));
        tree.children.insert(6, vec![5]);
        tree.children.insert(1, vec![6]);
        assert_eq!(resolve(&tree, &0), None);
        assert!(!prove_native_text(&tree, &0, 42, 8));
        // Even when both directions initially agree, a later detach is not
        // authority to retain the original sheet ID.
        let mut detached = save_panel_accessory();
        detached.fail_child_check_after = Some(2);
        assert_eq!(resolve_accessory_surface(&detached, &0), None);
        assert_eq!(detached.child_checks.get(), 3);
    }

    fn standalone_panel_accessory() -> Tree {
        let mut tree = save_panel_accessory();
        tree.nodes.get_mut(&1).unwrap().0 = "AXWindow";
        tree
    }

    #[test]
    fn standalone_panel_accessory_resolves_popup_and_text_to_exact_window() {
        for role in ["AXPopUpButton", "AXTextField"] {
            let mut tree = standalone_panel_accessory();
            tree.nodes.get_mut(&0).unwrap().0 = role;
            // The control has no AXWindow/native ID; the remote split group's
            // SPI ID cannot replace the first logical surface on its parent chain.
            assert_eq!(resolve(&tree, &0), Some(8));
            assert_eq!(resolve_with_window_fallback(&tree, &0, false), Some(8));
            assert_ne!(resolve(&tree, &0), Some(7));
            assert_ne!(resolve(&tree, &0), Some(9));
            if role == "AXTextField" {
                assert!(prove_native_text(&tree, &0, 42, 8));
                assert!(!prove_native_text(&tree, &0, 42, 7));
                assert!(!prove_native_text(&tree, &0, 99, 8));
            }
        }
    }

    #[test]
    fn standalone_panel_accessory_rejects_missing_foreign_or_unproven_window() {
        for kind in 0..9 {
            let mut tree = standalone_panel_accessory();
            match kind {
                0 => { tree.children.insert(4, vec![]); }
                1 => { tree.children.insert(1, vec![]); }
                2 => tree.nodes.get_mut(&1).unwrap().3 = None,
                3 => tree.nodes.get_mut(&1).unwrap().3 = Some(0),
                4 => { tree.window_owners.insert(8, 99); }
                5 => { tree.window_owners.remove(&8); }
                6 => tree.nodes.get_mut(&0).unwrap().1 = None,
                7 => tree.nodes.get_mut(&4).unwrap().0 = "AXWebArea",
                _ => tree.expired = true,
            }
            assert_eq!(resolve(&tree, &0), None, "case {kind}");
            assert!(!prove_native_text(&tree, &0, 42, 8), "case {kind}");
        }
        let mut sibling = standalone_panel_accessory();
        sibling.nodes.get_mut(&1).unwrap().3 = Some(10);
        sibling.window_owners.insert(10, 42);
        assert_eq!(resolve(&sibling, &0), Some(10));
        assert!(!prove_native_text(&sibling, &0, 42, 8));
    }

    #[test]
    fn standalone_panel_accessory_does_not_skip_an_intervening_surface() {
        for role in ["AXWindow", "AXSheet", "AXPopover"] {
            let mut tree = standalone_panel_accessory();
            tree.nodes.get_mut(&4).unwrap().0 = role;
            tree.window_owners.insert(9, 99);
            // A different physical surface owns the nearer parent. The existing
            // one-way embedding may resolve it, but never the farther host window.
            assert_eq!(resolve(&tree, &0), Some(9));
            assert_ne!(resolve(&tree, &0), Some(8));
            assert!(!prove_native_text(&tree, &0, 42, 8));
            tree.nodes.get_mut(&4).unwrap().3 = None;
            assert_eq!(resolve(&tree, &0), None);
        }
    }

    #[test]
    fn standalone_panel_accessory_rejects_extra_provider_return_and_cycle() {
        for kind in 0..3 {
            let mut tree = standalone_panel_accessory();
            tree.nodes.get_mut(&4).unwrap().1 = Some(5);
            tree.nodes.insert(5, ("AXGroup", Some(1), None, None, 100));
            tree.children.insert(5, vec![4]);
            tree.children.insert(1, vec![5]);
            if kind == 1 {
                tree.nodes.insert(5, ("AXGroup", Some(6), None, None, 42));
                tree.nodes.insert(6, ("AXGroup", Some(1), None, None, 99));
                tree.children.insert(6, vec![5]);
                tree.children.insert(1, vec![6]);
            } else if kind == 2 {
                tree.nodes.get_mut(&4).unwrap().1 = Some(0);
                tree.children.insert(0, vec![4]);
            }
            assert_eq!(resolve(&tree, &0), None, "case {kind}");
            assert!(!prove_native_text(&tree, &0, 42, 8), "case {kind}");
        }
    }

    #[test]
    fn standalone_panel_accessory_rechecks_edges_and_budget_before_return() {
        let mut detached = standalone_panel_accessory();
        detached.fail_child_check_after = Some(2);
        assert_eq!(resolve_accessory_surface(&detached, &0), None);
        assert_eq!(detached.child_checks.get(), 3);

        let mut expired = standalone_panel_accessory();
        // Both forward edges and their reciprocal rechecks succeeded. Expiry
        // still prevents returning the window at the final surface validation.
        expired.expire_after_child_checks = Some(4);
        assert_eq!(resolve_accessory_surface(&expired, &0), None);
        assert_eq!(expired.child_checks.get(), 4);
    }

    #[test]
    fn provider_subtree_requires_reciprocity_before_and_after_the_boundary() {
        let mut t = sheet();
        t.nodes.get_mut(&0).unwrap().4 = 99;
        t.nodes.get_mut(&0).unwrap().1 = Some(4);
        t.nodes.insert(4, ("AXGroup", Some(1), None, None, 99));
        t.children.insert(4, vec![0]);
        t.children.insert(1, vec![4]);
        assert_eq!(resolve(&t, &0), Some(8));
        t.children.insert(4, vec![]);
        assert_eq!(resolve(&t, &0), None);
        t.children.insert(4, vec![0]);
        t.children.insert(1, vec![]);
        assert_eq!(resolve(&t, &0), None);
    }

    #[test]
    fn foreign_window_attribute_and_unmapped_sheet_do_not_prove_embedding() {
        let mut t = sheet();
        t.nodes.get_mut(&0).unwrap().4 = 99;
        t.nodes.get_mut(&0).unwrap().1 = None;
        assert_eq!(resolve(&t, &0), None);
        t.nodes.get_mut(&0).unwrap().1 = Some(1);
        t.nodes.get_mut(&1).unwrap().3 = None;
        assert_eq!(resolve(&t, &0), None);
    }

    #[test]
    fn embedded_surface_owner_must_match_live_window_server_ownership() {
        let mut t = sheet();
        t.nodes.get_mut(&0).unwrap().4 = 99;
        t.window_owners.insert(8, 100);
        assert_eq!(resolve(&t, &0), None);
        t.window_owners.remove(&8);
        assert_eq!(resolve(&t, &0), None);
    }

    #[test]
    fn detached_provider_control_cannot_reuse_earlier_reciprocity() {
        let mut t = sheet();
        t.nodes.get_mut(&0).unwrap().4 = 99;
        t.fail_child_check_after = Some(1);
        assert_eq!(resolve(&t, &0), None);
        assert_eq!(t.child_checks.get(), 2);
    }

    #[test]
    fn multiple_provider_boundaries_and_cycles_are_not_an_embedding() {
        let mut t = sheet();
        t.nodes.get_mut(&0).unwrap().4 = 99;
        t.nodes.get_mut(&0).unwrap().1 = Some(4);
        t.nodes.insert(4, ("AXGroup", Some(1), None, None, 100));
        t.children.insert(4, vec![0]);
        t.children.insert(1, vec![4]);
        assert_eq!(resolve(&t, &0), None);
        t.nodes.get_mut(&4).unwrap().1 = Some(0);
        t.children.insert(0, vec![4]);
        assert_eq!(resolve(&t, &0), None);
    }

    #[test]
    fn expired_embedding_proof_never_returns_a_window() {
        let mut t = sheet();
        t.nodes.get_mut(&0).unwrap().4 = 99;
        t.expired = true;
        assert_eq!(resolve(&t, &0), None);
    }
}
