//! Discover an exact focused AXSheet that AppKit omits from AXWindows.
//!
//! The sheet remains its own target. A live reciprocal attachment to a current
//! AXWindows host proves discovery; it does not alias sheet input to that host.

use super::bindings::{
    ax_get_window_id, copy_element_attr, copy_string_attr, kAXErrorAttributeUnsupported,
    kAXErrorSuccess, try_copy_ax_windows, try_copy_bool_attr, AXError,
    AXUIElementCopyAttributeValue, AXUIElementCreateApplication, AXUIElementGetPid, AXUIElementRef,
    AXUIElementSetMessagingTimeout,
};
use core_foundation::{
    array::CFArray,
    base::{CFEqual, CFGetTypeID, CFRelease, CFRetain, CFTypeRef, TCFType},
    string::CFString,
};
use std::time::{Duration, Instant};

trait SheetTree {
    type Node: Clone;
    fn focused(&self) -> Option<Self::Node>;
    fn windows(&self) -> Option<Vec<Self::Node>>;
    fn role(&self, node: &Self::Node) -> Option<String>;
    fn identifier(&self, node: &Self::Node) -> Option<String>;
    fn owner(&self, node: &Self::Node) -> Option<i32>;
    fn window_id(&self, node: &Self::Node) -> Option<u32>;
    fn relation(&self, node: &Self::Node, name: &str) -> Option<Self::Node>;
    fn contains_child(&self, parent: &Self::Node, child: &Self::Node) -> bool;
    fn same(&self, left: &Self::Node, right: &Self::Node) -> bool;
    fn owns_window(&self, pid: i32, window_id: u32) -> bool;
    fn minimized(&self, node: &Self::Node) -> Result<bool, AXError>;
    fn on_screen(&self, pid: i32, window_id: u32) -> bool;
    fn within_budget(&self) -> bool;
}

const MAX_SHEET_DEPTH: usize = 8;

// Leaf first, document host last. Every link is reciprocal, same-process and
// mapped to a distinct live WindowServer window. AXWindow can point past the
// immediate AXParent: AppKit's GoToWindow is parented to save-panel while both
// sheets name the document as their AXWindow.
struct Attachment<N> {
    nodes: Vec<N>,
    window_ids: Vec<u32>,
}

fn prove_chain<T: SheetTree>(tree: &T, pid: i32, requested: u32) -> Option<Attachment<T::Node>> {
    let focused = tree.focused()?;
    if tree.role(&focused).as_deref() != Some("AXSheet")
        || tree.window_id(&focused) != Some(requested)
    {
        return None;
    }
    let mut nodes = Vec::new();
    let mut window_ids = Vec::new();
    let mut current = focused.clone();
    loop {
        let id = tree.window_id(&current)?;
        if !tree.within_budget()
            || id == 0
            || tree.owner(&current) != Some(pid)
            || !tree.owns_window(pid, id)
            || window_ids.contains(&id)
            || nodes.iter().any(|node| tree.same(node, &current))
        {
            return None;
        }
        let role = tree.role(&current)?;
        nodes.push(current.clone());
        window_ids.push(id);
        if role == "AXWindow" {
            break;
        }
        if role != "AXSheet" || nodes.len() > MAX_SHEET_DEPTH {
            return None;
        }
        let parent = tree.relation(&current, "AXParent")?;
        if !tree.contains_child(&parent, &current) {
            return None;
        }
        current = parent;
    }
    let host = nodes.last()?;
    let windows = tree.windows()?;
    if windows.iter().filter(|node| tree.same(node, host)).count() != 1 {
        return None;
    }
    // Revalidate the entire chain after discovery. A detached/reparented sheet,
    // a changed focus, a sibling window or a reused ID never inherits the proof.
    for (index, pair) in nodes.windows(2).enumerate() {
        if !tree.within_budget()
            || tree.owner(&pair[0]) != Some(pid)
            || tree.window_id(&pair[0]) != Some(window_ids[index])
            || !tree
                .relation(&pair[0], "AXParent")
                .is_some_and(|n| tree.same(&n, &pair[1]))
            || !tree
                .relation(&pair[0], "AXWindow")
                .is_some_and(|n| tree.same(&n, host))
            || !tree.contains_child(&pair[1], &pair[0])
        {
            return None;
        }
    }
    if !tree
        .focused()
        .is_some_and(|node| tree.same(&node, &focused))
        || tree.owner(host) != Some(pid)
        || tree.window_id(host) != window_ids.last().copied()
        || !tree.within_budget()
    {
        return None;
    }
    Some(Attachment { nodes, window_ids })
}

fn prove<T: SheetTree>(tree: &T, pid: i32, requested: u32) -> Option<T::Node> {
    prove_chain(tree, pid, requested)?.nodes.first().cloned()
}

fn visible_chain<T: SheetTree>(tree: &T, pid: i32, chain: &Attachment<T::Node>) -> bool {
    let Some(host) = chain.nodes.last() else {
        return false;
    };
    tree.minimized(host) == Ok(false)
        && chain.nodes.iter().zip(&chain.window_ids).all(|(node, id)| {
            let minimized = tree.minimized(node);
            (minimized == Ok(false) || minimized == Err(kAXErrorAttributeUnsupported))
                && tree.on_screen(pid, *id)
                && tree.within_budget()
        })
}

fn dialog_chain<T: SheetTree>(tree: &T, pid: i32, requested: u32) -> Option<Attachment<T::Node>> {
    let chain = prove_chain(tree, pid, requested)?;
    // A nested dialog is eligible only through a proven standard Open/Save
    // panel ancestor. An arbitrary AXSheet or same-PID sibling is insufficient.
    if !chain.nodes.iter().take(chain.nodes.len() - 1).any(|node| {
        matches!(
            tree.identifier(node).as_deref(),
            Some("save-panel" | "open-panel")
        )
    }) || !visible_chain(tree, pid, &chain)
    {
        return None;
    }
    let current = prove_chain(tree, pid, requested)?;
    if chain.window_ids != current.window_ids
        || !chain
            .nodes
            .iter()
            .zip(&current.nodes)
            .all(|(a, b)| tree.same(a, b))
        || !tree.within_budget()
    {
        return None;
    }
    Some(chain)
}

fn dialog_host<T: SheetTree>(tree: &T, pid: i32, requested: u32) -> Option<T::Node> {
    dialog_chain(tree, pid, requested)?.nodes.last().cloned()
}

fn prove_with_visibility<T: SheetTree>(
    tree: &T,
    pid: i32,
    requested: u32,
    require_unminimized: bool,
) -> Option<T::Node> {
    let chain = prove_chain(tree, pid, requested)?;
    let sheet = chain.nodes.first()?;
    if require_unminimized {
        // Only the exact unsupported-attribute case may inherit visibility.
        // Failed reads and a supported AXMinimized value retain their semantics.
        if tree.minimized(sheet) != Err(kAXErrorAttributeUnsupported)
            || !visible_chain(tree, pid, &chain)
        {
            return None;
        }
        let current = prove_chain(tree, pid, requested)?;
        if chain.window_ids != current.window_ids
            || !chain
                .nodes
                .iter()
                .zip(&current.nodes)
                .all(|(a, b)| tree.same(a, b))
        {
            return None;
        }
    }
    tree.within_budget().then(|| sheet.clone())
}

struct Node(AXUIElementRef);
impl Node {
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
impl SheetTree for NativeTree {
    type Node = Node;
    fn focused(&self) -> Option<Node> {
        self.relation(&self.app, "AXFocusedWindow")
    }
    fn windows(&self) -> Option<Vec<Node>> {
        unsafe {
            let snapshot = try_copy_ax_windows(self.app.0).ok()?;
            let complete = snapshot.complete && snapshot.windows.len() <= 32;
            let nodes: Vec<_> = snapshot.windows.into_iter().map(|ptr| Node(ptr)).collect();
            complete.then_some(nodes)
        }
    }
    fn role(&self, node: &Node) -> Option<String> {
        unsafe { copy_string_attr(node.0, "AXRole") }
    }
    fn identifier(&self, node: &Node) -> Option<String> {
        unsafe { copy_string_attr(node.0, "AXIdentifier") }
    }
    fn owner(&self, node: &Node) -> Option<i32> {
        let mut pid = 0;
        (unsafe { AXUIElementGetPid(node.0, &mut pid) } == kAXErrorSuccess).then_some(pid)
    }
    fn window_id(&self, node: &Node) -> Option<u32> {
        unsafe { ax_get_window_id(node.0) }
    }
    fn relation(&self, node: &Node, name: &str) -> Option<Node> {
        unsafe { Node::owned(copy_element_attr(node.0, name)?) }
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
    fn same(&self, left: &Node, right: &Node) -> bool {
        unsafe { CFEqual(left.0 as CFTypeRef, right.0 as CFTypeRef) != 0 }
    }
    fn owns_window(&self, pid: i32, window_id: u32) -> bool {
        matches!(
            crate::windows::resolve_window_owner(pid, window_id),
            crate::windows::WindowOwner::SamePid
        )
    }
    fn minimized(&self, node: &Node) -> Result<bool, AXError> {
        unsafe { try_copy_bool_attr(node.0, "AXMinimized") }
    }
    fn on_screen(&self, pid: i32, window_id: u32) -> bool {
        crate::windows::window_info_by_id(window_id)
            .is_some_and(|window| window.pid == pid && window.is_on_screen)
    }
    fn within_budget(&self) -> bool {
        Instant::now() < self.deadline
    }
}

/// Return a retained focused sheet only for the requested live native window.
/// Caller must CFRelease it. No GUI state, focus, or window identity is changed.
pub(crate) fn copy_focused_attached_sheet(pid: i32, window_id: u32) -> Option<AXUIElementRef> {
    unsafe {
        let app = Node::owned(AXUIElementCreateApplication(pid))?;
        prove(
            &NativeTree {
                app,
                deadline: Instant::now() + Duration::from_secs(2),
            },
            pid,
            window_id,
        )
        .map(Node::into_raw)
    }
}

/// Native proof of a focused Open/Save panel or one of its attached sheets.
/// IDs describe the checked chain; they never grant input to its other members.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DialogAttachment {
    pub window_id: u32,
    pub panel_id: u32,
    pub host_id: u32,
    pub path: Vec<u32>,
}

pub(crate) fn focused_dialog_attachment(pid: i32, window_id: u32) -> Option<DialogAttachment> {
    unsafe {
        let tree = NativeTree {
            app: Node::owned(AXUIElementCreateApplication(pid))?,
            deadline: Instant::now() + Duration::from_secs(2),
        };
        let chain = dialog_chain(&tree, pid, window_id)?;
        let panel = chain
            .nodes
            .iter()
            .enumerate()
            .rev()
            .find(|(_, node)| {
                matches!(
                    tree.identifier(node).as_deref(),
                    Some("save-panel" | "open-panel")
                )
            })?
            .0;
        tree.within_budget().then(|| DialogAttachment {
            window_id,
            panel_id: chain.window_ids[panel],
            host_id: *chain.window_ids.last().unwrap(),
            path: chain.window_ids,
        })
    }
}

/// Retain the ultimate document host, not a nested sheet's immediate AXParent.
/// Caller must CFRelease the returned element. This never changes focus.
pub(crate) fn copy_focused_dialog_host(pid: i32, window_id: u32) -> Option<AXUIElementRef> {
    unsafe {
        let tree = NativeTree {
            app: Node::owned(AXUIElementCreateApplication(pid))?,
            deadline: Instant::now() + Duration::from_secs(2),
        };
        dialog_host(&tree, pid, window_id).map(Node::into_raw)
    }
}

pub(crate) fn focused_dialog_host(pid: i32, window_id: u32) -> Option<u32> {
    focused_dialog_attachment(pid, window_id).map(|chain| chain.host_id)
}

/// Closing a sheet may return focus to its previously proven host. Check one
/// WindowServer snapshot and the host's exact AX focus; unreadable AX or a
/// still-visible sheet cannot authorize this transition. No AX tree is built.
fn dialog_windows_allow_host_return(
    snapshot: &crate::windows::WindowEnumeration,
    pid: i32,
    sheet_id: u32,
    host_id: u32,
) -> bool {
    snapshot.succeeded
        && sheet_id != host_id
        && snapshot
            .windows
            .iter()
            .any(|window| window.pid == pid && window.window_id == host_id && window.is_on_screen)
        && !snapshot.windows.iter().any(|window| {
            window.window_id == sheet_id && (window.is_on_screen || window.pid != pid)
        })
}

/// Absence/hidden state is accepted only from a successful native snapshot;
/// a reused ID or enumeration failure cannot authorize returning to an ancestor.
pub(crate) fn sheet_is_closed(pid: i32, sheet_id: u32) -> bool {
    let snapshot = crate::windows::all_windows_including_accessory_layers_with_snapshot();
    snapshot.succeeded
        && !snapshot.windows.iter().any(|window| {
            window.window_id == sheet_id && (window.is_on_screen || window.pid != pid)
        })
}

pub(crate) fn dialog_returned_to_host(pid: i32, sheet_id: u32, host_id: u32) -> bool {
    let windows = crate::windows::all_windows_including_accessory_layers_with_snapshot();
    if !dialog_windows_allow_host_return(&windows, pid, sheet_id, host_id) {
        return false;
    }
    unsafe {
        let Some(app) = Node::owned(AXUIElementCreateApplication(pid)) else {
            return false;
        };
        let tree = NativeTree {
            app,
            deadline: Instant::now() + Duration::from_millis(500),
        };
        let Some(host) = tree.focused() else {
            return false;
        };
        tree.window_id(&host) == Some(host_id)
            && tree.owner(&host) == Some(pid)
            && tree.role(&host).as_deref() == Some("AXWindow")
            && tree.minimized(&host) == Ok(false)
            && tree
                .windows()
                .is_some_and(|windows| windows.iter().any(|w| tree.same(w, &host)))
            && tree.within_budget()
    }
}

/// Prove the unsupported AXMinimized case for one already retained sheet.
/// The host supplies visibility evidence only; input remains bound to the
/// sheet's own CGWindowID. Discovery alone never supplies this extra proof.
///
/// # Safety
///
/// `expected_sheet` must remain a valid retained AX element for this call.
pub(crate) unsafe fn proves_unminimized_focused_sheet(
    pid: i32,
    window_id: u32,
    expected_sheet: AXUIElementRef,
) -> bool {
    let Some(app) = Node::owned(AXUIElementCreateApplication(pid)) else {
        return false;
    };
    prove_with_visibility(
        &NativeTree {
            app,
            deadline: Instant::now() + Duration::from_secs(2),
        },
        pid,
        window_id,
        true,
    )
    .is_some_and(|sheet| CFEqual(sheet.0 as CFTypeRef, expected_sheet as CFTypeRef) != 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    #[derive(Clone)]
    struct FakeNode {
        identity: u32,
        role: &'static str,
        identifier: &'static str,
        owner: i32,
        window: u32,
    }
    struct Tree {
        sheet: FakeNode,
        host: FakeNode,
        host_listed: bool,
        attached: bool,
        matching_window_relation: bool,
        focused_reads: Cell<usize>,
        focus_changed: bool,
        owned: bool,
        sheet_minimized: Result<bool, AXError>,
        host_minimized: Result<bool, AXError>,
        sheet_on_screen: bool,
        host_on_screen: bool,
        budget: Cell<usize>,
    }
    impl SheetTree for Tree {
        type Node = FakeNode;
        fn focused(&self) -> Option<FakeNode> {
            let reads = self.focused_reads.get();
            self.focused_reads.set(reads + 1);
            if reads > 0 && self.focus_changed {
                None
            } else {
                Some(self.sheet.clone())
            }
        }
        fn windows(&self) -> Option<Vec<FakeNode>> {
            self.host_listed.then(|| vec![self.host.clone()])
        }
        fn role(&self, node: &FakeNode) -> Option<String> {
            Some(node.role.into())
        }
        fn identifier(&self, node: &FakeNode) -> Option<String> {
            Some(node.identifier.into())
        }
        fn owner(&self, node: &FakeNode) -> Option<i32> {
            Some(node.owner)
        }
        fn window_id(&self, node: &FakeNode) -> Option<u32> {
            Some(node.window)
        }
        fn relation(&self, _node: &FakeNode, name: &str) -> Option<FakeNode> {
            if name == "AXWindow" && !self.matching_window_relation {
                Some(self.sheet.clone())
            } else {
                Some(self.host.clone())
            }
        }
        fn contains_child(&self, _parent: &FakeNode, child: &FakeNode) -> bool {
            self.attached && child.identity == self.sheet.identity
        }
        fn same(&self, a: &FakeNode, b: &FakeNode) -> bool {
            a.identity == b.identity
        }
        fn owns_window(&self, _pid: i32, _window: u32) -> bool {
            self.owned
        }
        fn minimized(&self, node: &FakeNode) -> Result<bool, AXError> {
            if node.identity == self.sheet.identity {
                self.sheet_minimized
            } else {
                self.host_minimized
            }
        }
        fn on_screen(&self, pid: i32, window: u32) -> bool {
            pid == self.sheet.owner
                && ((window == self.sheet.window && self.sheet_on_screen)
                    || (window == self.host.window && self.host_on_screen))
        }
        fn within_budget(&self) -> bool {
            let n = self.budget.get();
            self.budget.set(n.saturating_sub(1));
            n > 0
        }
    }
    fn pages() -> Tree {
        Tree {
            sheet: FakeNode {
                identity: 1,
                role: "AXSheet",
                identifier: "save-panel",
                owner: 42,
                window: 900,
            },
            host: FakeNode {
                identity: 2,
                role: "AXWindow",
                identifier: "document",
                owner: 42,
                window: 700,
            },
            host_listed: true,
            attached: true,
            matching_window_relation: true,
            focused_reads: Cell::new(0),
            focus_changed: false,
            owned: true,
            sheet_minimized: Err(kAXErrorAttributeUnsupported),
            host_minimized: Ok(false),
            sheet_on_screen: true,
            host_on_screen: true,
            budget: Cell::new(100),
        }
    }
    #[test]
    fn discovers_focused_sheet_missing_from_top_level_windows() {
        let sheet = prove(&pages(), 42, 900).unwrap();
        assert_eq!(sheet.window, 900);
    }

    #[test]
    fn dialog_activation_requires_a_live_standard_panel_and_exact_host() {
        for identifier in ["save-panel", "open-panel"] {
            let mut tree = pages();
            tree.sheet.identifier = identifier;
            assert_eq!(dialog_host(&tree, 42, 900).unwrap().window, 700);
        }
        for alter in [
            |t: &mut Tree| t.sheet.identifier = "confirmation",
            |t: &mut Tree| t.attached = false,
            |t: &mut Tree| t.matching_window_relation = false,
            |t: &mut Tree| t.host_listed = false,
            |t: &mut Tree| t.host.owner = 99,
            |t: &mut Tree| t.host_minimized = Ok(true),
            |t: &mut Tree| t.sheet_minimized = Err(super::super::bindings::kAXErrorCannotComplete),
            |t: &mut Tree| t.sheet_on_screen = false,
            |t: &mut Tree| t.host_on_screen = false,
            |t: &mut Tree| t.focus_changed = true,
        ] {
            let mut tree = pages();
            alter(&mut tree);
            assert!(dialog_host(&tree, 42, 900).is_none());
        }
        assert!(dialog_host(&pages(), 42, 700).is_none());
        assert!(dialog_host(&pages(), 42, 901).is_none());
    }

    #[test]
    fn dialog_close_requires_a_successful_snapshot_and_never_accepts_a_reused_sheet_id() {
        use crate::windows::{WindowBounds, WindowEnumeration, WindowInfo};
        let window = |id, pid, visible| WindowInfo {
            window_id: id,
            pid,
            app_name: String::new(),
            title: String::new(),
            bounds: WindowBounds {
                x: 0.0,
                y: 0.0,
                width: 100.0,
                height: 100.0,
            },
            layer: 0,
            z_index: 0,
            is_on_screen: visible,
            current_space_id: None,
            on_current_space: None,
            space_ids: None,
        };
        let mut snapshot = WindowEnumeration {
            windows: vec![window(700, 42, true)],
            current_space_id: None,
            succeeded: true,
        };
        assert!(dialog_windows_allow_host_return(&snapshot, 42, 900, 700));
        snapshot.windows.push(window(900, 42, false));
        assert!(dialog_windows_allow_host_return(&snapshot, 42, 900, 700));
        snapshot.windows[1].is_on_screen = true;
        assert!(!dialog_windows_allow_host_return(&snapshot, 42, 900, 700));
        snapshot.windows[1].is_on_screen = false;
        snapshot.windows[1].pid = 99;
        assert!(!dialog_windows_allow_host_return(&snapshot, 42, 900, 700));
        snapshot.windows.pop();
        snapshot.succeeded = false;
        assert!(!dialog_windows_allow_host_return(&snapshot, 42, 900, 700));
        snapshot.succeeded = true;
        snapshot.windows[0].is_on_screen = false;
        assert!(!dialog_windows_allow_host_return(&snapshot, 42, 900, 700));
        assert!(!dialog_windows_allow_host_return(&snapshot, 42, 900, 900));
    }

    #[test]
    fn visible_save_sheet_with_unsupported_minimized_state_keeps_its_own_target() {
        let sheet = prove_with_visibility(&pages(), 42, 900, true).unwrap();
        assert_eq!(sheet.window, 900);
        assert!(prove_with_visibility(&pages(), 42, 700, true).is_none());
        assert!(prove_with_visibility(&pages(), 42, 901, true).is_none());
    }

    #[test]
    fn visibility_proof_requires_both_windows_on_screen_and_unminimized_host() {
        use super::super::bindings::{kAXErrorCannotComplete, kAXErrorNoValue};
        for state in [Ok(true), Err(kAXErrorCannotComplete), Err(kAXErrorNoValue)] {
            let mut tree = pages();
            tree.host_minimized = state;
            assert!(prove_with_visibility(&tree, 42, 900, true).is_none());
        }
        for (sheet, host) in [(false, true), (true, false), (false, false)] {
            let mut tree = pages();
            tree.sheet_on_screen = sheet;
            tree.host_on_screen = host;
            assert!(prove_with_visibility(&tree, 42, 900, true).is_none());
        }
    }

    #[test]
    fn visibility_proof_never_turns_failed_or_supported_sheet_reads_into_an_omission() {
        use super::super::bindings::{
            kAXErrorAPIDisabled, kAXErrorCannotComplete, kAXErrorFailure, kAXErrorInvalidUIElement,
            kAXErrorNoValue,
        };
        for state in [
            Ok(true),
            Ok(false),
            Err(kAXErrorAPIDisabled),
            Err(kAXErrorCannotComplete),
            Err(kAXErrorFailure),
            Err(kAXErrorInvalidUIElement),
            Err(kAXErrorNoValue),
        ] {
            let mut tree = pages();
            tree.sheet_minimized = state;
            assert!(prove_with_visibility(&tree, 42, 900, true).is_none());
        }
    }

    #[test]
    fn visibility_proof_preserves_attachment_owner_focus_and_deadline_checks() {
        for alter in [
            |tree: &mut Tree| tree.attached = false,
            |tree: &mut Tree| tree.host_listed = false,
            |tree: &mut Tree| tree.matching_window_relation = false,
            |tree: &mut Tree| tree.owned = false,
            |tree: &mut Tree| tree.sheet.owner = 99,
            |tree: &mut Tree| tree.host.owner = 99,
            |tree: &mut Tree| tree.sheet.role = "AXWindow",
            |tree: &mut Tree| tree.focus_changed = true,
            |tree: &mut Tree| tree.budget.set(4),
        ] {
            let mut tree = pages();
            alter(&mut tree);
            assert!(prove_with_visibility(&tree, 42, 900, true).is_none());
        }
    }

    #[test]
    fn discovery_does_not_require_visibility_or_establish_input_eligibility() {
        let mut tree = pages();
        tree.sheet_on_screen = false;
        tree.host_minimized = Ok(true);
        assert!(prove(&tree, 42, 900).is_some());
        assert!(prove_with_visibility(&tree, 42, 900, true).is_none());
    }
    #[test]
    fn requested_host_or_sibling_is_not_substituted_with_sheet() {
        assert!(prove(&pages(), 42, 700).is_none());
        assert!(prove(&pages(), 42, 901).is_none());
    }
    #[test]
    fn detached_or_unlisted_host_is_refused() {
        let mut tree = pages();
        tree.attached = false;
        assert!(prove(&tree, 42, 900).is_none());
        let mut tree = pages();
        tree.host_listed = false;
        assert!(prove(&tree, 42, 900).is_none());
    }
    #[test]
    fn foreign_or_missing_windowserver_owner_is_refused() {
        let mut tree = pages();
        tree.sheet.owner = 99;
        assert!(prove(&tree, 42, 900).is_none());
        let mut tree = pages();
        tree.host.owner = 99;
        assert!(prove(&tree, 42, 900).is_none());
        let mut tree = pages();
        tree.owned = false;
        assert!(prove(&tree, 42, 900).is_none());
    }
    #[test]
    fn non_sheet_or_conflicting_attachment_is_refused() {
        let mut tree = pages();
        tree.sheet.role = "AXWindow";
        assert!(prove(&tree, 42, 900).is_none());
        let mut tree = pages();
        tree.matching_window_relation = false;
        assert!(prove(&tree, 42, 900).is_none());
        let mut tree = pages();
        tree.host.window = 900;
        assert!(prove(&tree, 42, 900).is_none());
    }
    #[test]
    fn focused_sheet_change_or_deadline_refuses_discovery() {
        let mut tree = pages();
        tree.focus_changed = true;
        assert!(prove(&tree, 42, 900).is_none());
        for budget in [0, 2, 3] {
            let tree = pages();
            tree.budget.set(budget);
            assert!(prove(&tree, 42, 900).is_none());
        }
    }
}

#[cfg(test)]
#[path = "attached_sheet_tests.rs"]
mod nested_tests;
