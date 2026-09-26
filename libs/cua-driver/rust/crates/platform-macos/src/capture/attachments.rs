//! Positive AX attachments for an exact window capture; never compositor-root
//! inference. Discovery deliberately excludes web/content subtrees and is not
//! exhaustive. An empty result means no proven additional surfaces. A caller
//! must rediscover after capture and discard pixels if the selected set changes.

use crate::ax::bindings::{
    ax_get_window_id, copy_element_attr, copy_string_attr, element_screen_rect,
    kAXErrorAttributeUnsupported, kAXErrorNoValue, kAXErrorSuccess, AXError,
    AXUIElementCreateApplication, AXUIElementGetPid, AXUIElementGetTypeID, AXUIElementRef,
    AXUIElementSetMessagingTimeout,
};
use crate::windows::WindowInfo;
use core_foundation::{
    array::{CFArray, CFArrayRef},
    base::{CFEqual, CFGetTypeID, CFRelease, CFRetain, CFTypeRef, TCFType},
    string::{CFString, CFStringRef},
};
use std::collections::VecDeque;
use std::time::{Duration, Instant};

const DISCOVERY_BUDGET: Duration = Duration::from_millis(350);
const MAX_ROOTS: usize = 32;
const MAX_CHILDREN: usize = 128;
const MAX_NODES: usize = 128;
const MAX_DEPTH: usize = 12;
const MAX_ATTACHMENTS: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DiscoveryStop {
    InvalidHost,
    AxUnavailable,
    Deadline,
    RootLimit,
    ChildLimit,
    NodeLimit,
    DepthLimit,
    AttachmentLimit,
    Cycle,
    Changed,
}

impl std::fmt::Display for DiscoveryStop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

trait Tree {
    type Node: Clone;
    fn roots(&self) -> Result<Vec<Self::Node>, DiscoveryStop>;
    fn role(&self, node: &Self::Node) -> Option<String>;
    fn owner(&self, node: &Self::Node) -> Option<i32>;
    fn id(&self, node: &Self::Node) -> Option<u32>;
    fn frame(&self, node: &Self::Node) -> Option<[f64; 4]>;
    fn parent(&self, node: &Self::Node) -> Option<Self::Node>;
    fn window(&self, node: &Self::Node) -> Option<Self::Node>;
    fn children(&self, node: &Self::Node) -> Result<Vec<Self::Node>, DiscoveryStop>;
    fn same(&self, left: &Self::Node, right: &Self::Node) -> bool;
    fn popover(&self, node: &Self::Node, pid: i32, host: u32) -> bool;
    fn current_space(&self, id: u32) -> bool;
    fn fresh_windows(&self) -> Option<Vec<WindowInfo>>;
    fn within_budget(&self) -> bool;
}

fn budget<T: Tree>(tree: &T) -> Result<(), DiscoveryStop> {
    tree.within_budget()
        .then_some(())
        .ok_or(DiscoveryStop::Deadline)
}

fn exact_window(windows: &[WindowInfo], pid: i32, id: u32) -> Option<&WindowInfo> {
    let mut matches = windows.iter().filter(|window| window.window_id == id);
    let window = matches.next()?;
    let b = &window.bounds;
    (matches.next().is_none()
        && id != 0
        && window.pid == pid
        && window.is_on_screen
        && window.on_current_space != Some(false)
        && [b.x, b.y, b.width, b.height].iter().all(|n| n.is_finite())
        && b.width > 0.0
        && b.height > 0.0)
        .then_some(window)
}

fn same_identity(a: &WindowInfo, b: &WindowInfo) -> bool {
    a.window_id == b.window_id
        && a.pid == b.pid
        && a.layer == b.layer
        && [a.bounds.x, a.bounds.y, a.bounds.width, a.bounds.height]
            .iter()
            .zip([b.bounds.x, b.bounds.y, b.bounds.width, b.bounds.height])
            .all(|(a, b)| a.to_bits() == b.to_bits())
}

fn surface_matches<T: Tree>(tree: &T, node: &T::Node, window: &WindowInfo) -> bool {
    tree.within_budget()
        && tree.owner(node) == Some(window.pid)
        && tree.id(node) == Some(window.window_id)
        && tree.frame(node).is_some_and(|frame| {
            frame
                .iter()
                .zip([
                    window.bounds.x,
                    window.bounds.y,
                    window.bounds.width,
                    window.bounds.height,
                ])
                .all(|(ax, cg)| ax.is_finite() && (ax - cg).abs() <= 0.5)
        })
        && tree.current_space(window.window_id)
        && tree.within_budget()
}

fn container(role: &str) -> bool {
    // No AXWebArea, text, tables, lists, outlines, canvas, application or
    // sibling AXWindow traversal. Chart/popover anchors may be native buttons.
    matches!(
        role,
        "AXGroup"
            | "AXToolbar"
            | "AXButton"
            | "AXPopUpButton"
            | "AXSplitGroup"
            | "AXScrollArea"
            | "AXRadioGroup"
    )
}

fn exact_root<T: Tree>(tree: &T, window: &WindowInfo) -> Result<T::Node, DiscoveryStop> {
    budget(tree)?;
    let roots = tree.roots()?;
    if roots.len() > MAX_ROOTS {
        return Err(DiscoveryStop::RootLimit);
    }
    let mut selected = None;
    for root in roots {
        budget(tree)?;
        if tree.id(&root) != Some(window.window_id) {
            continue;
        }
        if selected.is_some()
            || tree.role(&root).as_deref() != Some("AXWindow")
            || !surface_matches(tree, &root, window)
        {
            return Err(DiscoveryStop::InvalidHost);
        }
        selected = Some(root);
    }
    selected.ok_or(DiscoveryStop::InvalidHost)
}

fn prove_path<T: Tree>(
    tree: &T,
    pid: i32,
    host: &WindowInfo,
    path: &[T::Node],
    windows: &[WindowInfo],
) -> Result<Option<u32>, DiscoveryStop> {
    budget(tree)?;
    let Some(leaf) = path.last() else {
        return Ok(None);
    };
    let role = tree.role(leaf);
    if !matches!(role.as_deref(), Some("AXPopover" | "AXSheet")) || path.len() < 2 {
        return Ok(None);
    }
    let Some(id) = tree.id(leaf).filter(|id| *id != host.window_id) else {
        return Ok(None);
    };
    let Some(physical) = exact_window(windows, pid, id) else {
        return Ok(None);
    };
    if !tree
        .window(leaf)
        .is_some_and(|root| tree.same(&root, &path[0]))
        || !surface_matches(tree, &path[0], host)
        || !surface_matches(tree, leaf, physical)
    {
        budget(tree)?;
        return Ok(None);
    }
    for (index, pair) in path.windows(2).enumerate() {
        budget(tree)?;
        if tree.owner(&pair[1]) != Some(pid)
            || !tree
                .parent(&pair[1])
                .is_some_and(|parent| tree.same(&parent, &pair[0]))
        {
            return Ok(None);
        }
        let children = tree.children(&pair[0])?;
        if children.len() > MAX_CHILDREN {
            return Err(DiscoveryStop::ChildLimit);
        }
        if children
            .iter()
            .filter(|child| tree.same(child, &pair[1]))
            .count()
            != 1
        {
            return Ok(None);
        }
        if role.as_deref() == Some("AXSheet") {
            // Focus-independent subset of attached_sheet's reciprocal proof:
            // only direct sheet-to-sheet-to-exact-host chains. No arbitrary
            // container, same-PID sibling, AXMain or geometry-based parentage.
            if tree.role(&pair[1]).as_deref() != Some("AXSheet")
                || !tree
                    .window(&pair[1])
                    .is_some_and(|root| tree.same(&root, &path[0]))
            {
                return Ok(None);
            }
            let Some(sheet_id) = tree.id(&pair[1]) else {
                return Ok(None);
            };
            if sheet_id == host.window_id
                || path[..=index]
                    .iter()
                    .any(|node| tree.id(node) == Some(sheet_id))
            {
                return Ok(None);
            }
            let Some(sheet) = exact_window(windows, pid, sheet_id) else {
                return Ok(None);
            };
            if !surface_matches(tree, &pair[1], sheet) {
                return Ok(None);
            }
        } else if index + 2 < path.len()
            && !tree.role(&pair[1]).is_some_and(|role| container(&role))
        {
            return Ok(None);
        }
    }
    if role.as_deref() == Some("AXPopover") && !tree.popover(leaf, pid, host.window_id) {
        budget(tree)?;
        return Ok(None);
    }
    budget(tree)?;
    Ok(Some(id))
}

fn collect<T: Tree>(
    tree: &T,
    pid: i32,
    host_id: u32,
    windows: &[WindowInfo],
) -> Result<Vec<u32>, DiscoveryStop> {
    let host = exact_window(windows, pid, host_id).ok_or(DiscoveryStop::InvalidHost)?;
    let root = exact_root(tree, host)?;
    let mut queue = VecDeque::from([vec![root.clone()]]);
    let mut visited: Vec<T::Node> = Vec::new();
    let mut admitted = Vec::new();
    while let Some(path) = queue.pop_front() {
        budget(tree)?;
        if path.len() > MAX_DEPTH {
            return Err(DiscoveryStop::DepthLimit);
        }
        let node = path.last().expect("nonempty path");
        if path[..path.len() - 1]
            .iter()
            .any(|prior| tree.same(prior, node))
        {
            return Err(DiscoveryStop::Cycle);
        }
        if visited.iter().any(|prior| tree.same(prior, node)) {
            continue;
        }
        if visited.len() >= MAX_NODES {
            return Err(DiscoveryStop::NodeLimit);
        }
        visited.push(node.clone());
        if tree.owner(node) != Some(pid) {
            continue;
        }
        let Some(role) = tree.role(node) else {
            continue;
        };
        if matches!(role.as_str(), "AXPopover" | "AXSheet") {
            if let Some(id) = prove_path(tree, pid, host, &path, windows)? {
                if admitted.len() >= MAX_ATTACHMENTS {
                    return Err(DiscoveryStop::AttachmentLimit);
                }
                admitted.push((id, path.clone()));
            }
            // Popover contents cannot prove another direct host attachment.
            if role == "AXPopover" {
                continue;
            }
        } else if path.len() != 1 && !container(&role) {
            continue;
        }
        let children = tree.children(node)?;
        if children.len() > MAX_CHILDREN {
            return Err(DiscoveryStop::ChildLimit);
        }
        if queue.len() + visited.len() + children.len() > MAX_NODES {
            return Err(DiscoveryStop::NodeLimit);
        }
        for child in children {
            let mut next = path.clone();
            next.push(child);
            queue.push_back(next);
        }
    }
    budget(tree)?;
    let fresh = tree.fresh_windows().ok_or(DiscoveryStop::Changed)?;
    let live_host = exact_window(&fresh, pid, host_id).ok_or(DiscoveryStop::Changed)?;
    if !same_identity(host, live_host) || !tree.same(&root, &exact_root(tree, live_host)?) {
        return Err(DiscoveryStop::Changed);
    }
    let mut ids = Vec::new();
    for (id, path) in admitted {
        budget(tree)?;
        let before = exact_window(windows, pid, id).ok_or(DiscoveryStop::Changed)?;
        let after = exact_window(&fresh, pid, id).ok_or(DiscoveryStop::Changed)?;
        if !same_identity(before, after)
            || prove_path(tree, pid, live_host, &path, &fresh)? != Some(id)
        {
            return Err(DiscoveryStop::Changed);
        }
        ids.push(id);
    }
    budget(tree)?;
    ids.sort_unstable();
    ids.dedup();
    Ok(ids)
}

// Public AX bounded-array API, kept local to this collector rather than
// widening existing callers' bulk AXChildren reads.
#[link(name = "ApplicationServices", kind = "framework")]
extern "C" {
    fn AXUIElementGetAttributeValueCount(
        element: AXUIElementRef,
        attribute: CFStringRef,
        count: *mut isize,
    ) -> AXError;
    fn AXUIElementCopyAttributeValues(
        element: AXUIElementRef,
        attribute: CFStringRef,
        index: isize,
        maximum: isize,
        values: *mut CFArrayRef,
    ) -> AXError;
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

struct Native {
    app: Node,
    deadline: Instant,
    spaces: crate::input::skylight::SpaceQuery,
}
impl Native {
    fn ready(&self, node: &Node) -> bool {
        let remaining = self.deadline.saturating_duration_since(Instant::now());
        !remaining.is_zero()
            && unsafe {
                AXUIElementSetMessagingTimeout(
                    node.0,
                    remaining.min(Duration::from_millis(25)).as_secs_f32(),
                )
            } == kAXErrorSuccess
    }
    fn array(&self, node: &Node, name: &str, maximum: usize) -> Result<Vec<Node>, DiscoveryStop> {
        if !self.ready(node) {
            return Err(DiscoveryStop::Deadline);
        }
        let attribute = CFString::new(name);
        let mut count = 0;
        let status = unsafe {
            AXUIElementGetAttributeValueCount(node.0, attribute.as_concrete_TypeRef(), &mut count)
        };
        if name == "AXChildren" && matches!(status, kAXErrorAttributeUnsupported | kAXErrorNoValue)
        {
            return Ok(Vec::new());
        }
        if status != kAXErrorSuccess || count < 0 {
            return Err(DiscoveryStop::AxUnavailable);
        }
        if count as usize > maximum {
            return Err(if name == "AXWindows" {
                DiscoveryStop::RootLimit
            } else {
                DiscoveryStop::ChildLimit
            });
        }
        if count == 0 {
            return Ok(Vec::new());
        }
        if !self.ready(node) {
            return Err(DiscoveryStop::Deadline);
        }
        let mut raw: CFArrayRef = std::ptr::null();
        let status = unsafe {
            AXUIElementCopyAttributeValues(
                node.0,
                attribute.as_concrete_TypeRef(),
                0,
                count,
                &mut raw,
            )
        };
        if raw.is_null() {
            return Err(DiscoveryStop::AxUnavailable);
        }
        if status != kAXErrorSuccess
            || unsafe { CFGetTypeID(raw as CFTypeRef) } != CFArray::<CFTypeRef>::type_id()
        {
            unsafe { CFRelease(raw as CFTypeRef) };
            return Err(DiscoveryStop::AxUnavailable);
        }
        let values = unsafe { CFArray::<CFTypeRef>::wrap_under_create_rule(raw) };
        if values.len() != count {
            return Err(DiscoveryStop::Changed);
        }
        if !self.ready(node) {
            return Err(DiscoveryStop::Deadline);
        }
        let mut after = 0;
        if unsafe {
            AXUIElementGetAttributeValueCount(node.0, attribute.as_concrete_TypeRef(), &mut after)
        } != kAXErrorSuccess
            || after != count
        {
            return Err(DiscoveryStop::Changed);
        }
        let mut result = Vec::with_capacity(count as usize);
        for index in 0..count {
            let value = *values.get(index).ok_or(DiscoveryStop::Changed)?;
            if value.is_null() || unsafe { CFGetTypeID(value) } != unsafe { AXUIElementGetTypeID() }
            {
                return Err(DiscoveryStop::AxUnavailable);
            }
            unsafe { CFRetain(value) };
            result.push(Node(value as AXUIElementRef));
        }
        Ok(result)
    }
    fn relation(&self, node: &Node, name: &str) -> Option<Node> {
        self.ready(node)
            .then(|| unsafe { copy_element_attr(node.0, name).map(Node) })
            .flatten()
    }
}
impl Tree for Native {
    type Node = Node;
    fn roots(&self) -> Result<Vec<Node>, DiscoveryStop> {
        self.array(&self.app, "AXWindows", MAX_ROOTS)
    }
    fn role(&self, node: &Node) -> Option<String> {
        self.ready(node)
            .then(|| unsafe { copy_string_attr(node.0, "AXRole") })
            .flatten()
    }
    fn owner(&self, node: &Node) -> Option<i32> {
        let mut pid = 0;
        (self.ready(node) && unsafe { AXUIElementGetPid(node.0, &mut pid) } == kAXErrorSuccess)
            .then_some(pid)
    }
    fn id(&self, node: &Node) -> Option<u32> {
        self.ready(node)
            .then(|| unsafe { ax_get_window_id(node.0) })
            .flatten()
    }
    fn frame(&self, node: &Node) -> Option<[f64; 4]> {
        self.ready(node)
            .then(|| unsafe { element_screen_rect(node.0) })
            .flatten()
    }
    fn parent(&self, node: &Node) -> Option<Node> {
        self.relation(node, "AXParent")
    }
    fn window(&self, node: &Node) -> Option<Node> {
        self.relation(node, "AXWindow")
    }
    fn children(&self, node: &Node) -> Result<Vec<Node>, DiscoveryStop> {
        self.array(node, "AXChildren", MAX_CHILDREN)
    }
    fn same(&self, a: &Node, b: &Node) -> bool {
        unsafe { CFEqual(a.0 as CFTypeRef, b.0 as CFTypeRef) != 0 }
    }
    fn popover(&self, node: &Node, pid: i32, host: u32) -> bool {
        self.within_budget()
            && unsafe {
                crate::ax::attached_popover::proves_attached_popover_before(
                    pid,
                    host,
                    node.0,
                    self.deadline,
                )
            }
    }
    fn current_space(&self, id: u32) -> bool {
        self.within_budget()
            && self.spaces.window_space_ids(id).is_some_and(|spaces| {
                self.spaces
                    .current_space_for_window(id)
                    .is_some_and(|current| spaces.contains(&current))
            })
            && self.within_budget()
    }
    fn fresh_windows(&self) -> Option<Vec<WindowInfo>> {
        if !self.within_budget() {
            return None;
        }
        let snapshot = crate::windows::visible_windows_including_accessory_layers_with_snapshot();
        (snapshot.succeeded && self.within_budget()).then_some(snapshot.windows)
    }
    fn within_budget(&self) -> bool {
        Instant::now() < self.deadline
    }
}

/// Sorted, unique, positive attachment IDs excluding `host_id`. Neither Ok([])
/// nor Ok(nonempty) asserts exhaustive discovery. Err invalidates the entire
/// partial result; callers may capture only the exact target independently.
/// The 350ms budget is cooperative; synchronous AX messages/proof helpers can
/// overrun it. Existing native capture worker ownership/timeout remains required.
pub(super) fn attached_window_ids(
    pid: i32,
    host_id: u32,
    windows: &[WindowInfo],
) -> Result<Vec<u32>, DiscoveryStop> {
    let deadline = Instant::now() + DISCOVERY_BUDGET;
    let result = (|| {
        if pid <= 0 || host_id == 0 {
            return Err(DiscoveryStop::InvalidHost);
        }
        let app = unsafe { AXUIElementCreateApplication(pid) };
        if app.is_null() {
            return Err(DiscoveryStop::AxUnavailable);
        }
        let app = Node(app);
        let spaces =
            crate::input::skylight::SpaceQuery::new().ok_or(DiscoveryStop::AxUnavailable)?;
        collect(
            &Native {
                app,
                deadline,
                spaces,
            },
            pid,
            host_id,
            windows,
        )
    })();
    match &result {
        Ok(ids) => tracing::debug!(target: "cua_capture_geometry", pid, host_id,
            proven_attachments = ids.len(), exhaustive = false, "Collected explicit AX capture attachments"),
        Err(reason) => {
            tracing::debug!(target: "cua_capture_geometry", pid, host_id, reason = %reason,
            "Capture attachment discovery stopped; no additional surfaces authorized")
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::collections::{HashMap, HashSet};

    #[derive(Clone)]
    struct Fact {
        role: &'static str,
        owner: i32,
        id: u32,
        parent: Option<u32>,
        window: Option<u32>,
        children: Vec<u32>,
    }
    struct Fake {
        nodes: HashMap<u32, Fact>,
        roots: Vec<u32>,
        windows: Vec<WindowInfo>,
        current: HashSet<u32>,
        proof: bool,
        proof_calls: Cell<usize>,
        expired: Cell<bool>,
        expire_on_proof: bool,
        detach_after_proof: bool,
    }
    fn window(id: u32) -> WindowInfo {
        WindowInfo {
            window_id: id,
            pid: 42,
            app_name: String::new(),
            title: String::new(),
            bounds: crate::windows::WindowBounds {
                x: 100.0,
                y: 120.0,
                width: 400.0,
                height: 300.0,
            },
            layer: 0,
            z_index: 0,
            is_on_screen: true,
            current_space_id: None,
            on_current_space: None,
            space_ids: None,
        }
    }
    fn popover() -> Fake {
        Fake {
            nodes: HashMap::from([
                (
                    1,
                    Fact {
                        role: "AXWindow",
                        owner: 42,
                        id: 10,
                        parent: None,
                        window: None,
                        children: vec![2],
                    },
                ),
                (
                    2,
                    Fact {
                        role: "AXToolbar",
                        owner: 42,
                        id: 10,
                        parent: Some(1),
                        window: Some(1),
                        children: vec![3],
                    },
                ),
                (
                    3,
                    Fact {
                        role: "AXButton",
                        owner: 42,
                        id: 10,
                        parent: Some(2),
                        window: Some(1),
                        children: vec![4],
                    },
                ),
                (
                    4,
                    Fact {
                        role: "AXPopover",
                        owner: 42,
                        id: 20,
                        parent: Some(3),
                        window: Some(1),
                        children: vec![],
                    },
                ),
            ]),
            roots: vec![1],
            windows: vec![window(10), window(20)],
            current: HashSet::from([10, 20]),
            proof: true,
            proof_calls: Cell::new(0),
            expired: Cell::new(false),
            expire_on_proof: false,
            detach_after_proof: false,
        }
    }
    impl Tree for Fake {
        type Node = u32;
        fn roots(&self) -> Result<Vec<u32>, DiscoveryStop> {
            Ok(self.roots.clone())
        }
        fn role(&self, n: &u32) -> Option<String> {
            self.nodes.get(n).map(|v| v.role.into())
        }
        fn owner(&self, n: &u32) -> Option<i32> {
            self.nodes.get(n).map(|v| v.owner)
        }
        fn id(&self, n: &u32) -> Option<u32> {
            self.nodes.get(n).map(|v| v.id)
        }
        fn frame(&self, n: &u32) -> Option<[f64; 4]> {
            self.nodes.get(n).map(|_| [100.0, 120.0, 400.0, 300.0])
        }
        fn parent(&self, n: &u32) -> Option<u32> {
            if self.detach_after_proof && *n == 4 && self.proof_calls.get() > 0 {
                return None;
            }
            self.nodes.get(n)?.parent
        }
        fn window(&self, n: &u32) -> Option<u32> {
            self.nodes.get(n)?.window
        }
        fn children(&self, n: &u32) -> Result<Vec<u32>, DiscoveryStop> {
            Ok(self.nodes[n].children.clone())
        }
        fn same(&self, a: &u32, b: &u32) -> bool {
            a == b
        }
        fn popover(&self, _: &u32, _: i32, _: u32) -> bool {
            self.proof_calls.set(self.proof_calls.get() + 1);
            if self.expire_on_proof {
                self.expired.set(true);
            }
            self.proof
        }
        fn current_space(&self, id: u32) -> bool {
            self.current.contains(&id)
        }
        fn fresh_windows(&self) -> Option<Vec<WindowInfo>> {
            Some(self.windows.clone())
        }
        fn within_budget(&self) -> bool {
            !self.expired.get()
        }
    }
    #[test]
    fn toolbar_popover_requires_positive_proof_and_is_reproved() {
        let mut t = popover();
        let initial = t.windows.clone();
        assert_eq!(collect(&t, 42, 10, &initial), Ok(vec![20]));
        assert_eq!(t.proof_calls.get(), 2);
        t.proof = false;
        assert_eq!(collect(&t, 42, 10, &initial), Ok(vec![]));
    }
    #[test]
    fn foreign_hidden_off_space_and_duplicate_physical_ids_are_not_added() {
        for case in 0..5 {
            let mut t = popover();
            match case {
                0 => t.nodes.get_mut(&4).unwrap().owner = 99,
                1 => t.windows[1].is_on_screen = false,
                2 => {
                    t.current.remove(&20);
                }
                3 => t.windows.push(window(20)),
                _ => t.windows[1].on_current_space = Some(false),
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]));
        }
    }
    #[test]
    fn reparented_or_moved_surface_invalidates_the_partial_result() {
        let mut t = popover();
        let initial = t.windows.clone();
        t.detach_after_proof = true;
        assert_eq!(collect(&t, 42, 10, &initial), Err(DiscoveryStop::Changed));
        t.detach_after_proof = false;
        t.windows[1].bounds.x += 1.0;
        assert_eq!(collect(&t, 42, 10, &initial), Err(DiscoveryStop::Changed));
    }
    #[test]
    fn expiring_proof_and_structural_budgets_fail_without_partial_ids() {
        let mut t = popover();
        t.expire_on_proof = true;
        assert_eq!(
            collect(&t, 42, 10, &t.windows),
            Err(DiscoveryStop::Deadline)
        );
        let mut t = popover();
        t.nodes.get_mut(&1).unwrap().children = vec![2; MAX_CHILDREN + 1];
        assert_eq!(
            collect(&t, 42, 10, &t.windows),
            Err(DiscoveryStop::ChildLimit)
        );
        let mut t = popover();
        t.nodes.get_mut(&3).unwrap().children = vec![2];
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::Cycle));
    }
    #[test]
    fn web_and_sibling_window_subtrees_do_not_supply_attachments() {
        for role in ["AXWebArea", "AXWindow", "AXTable", "AXTextArea"] {
            let mut t = popover();
            t.nodes.get_mut(&2).unwrap().role = role;
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]));
            assert_eq!(t.proof_calls.get(), 0);
        }
    }
    #[test]
    fn host_alias_and_one_way_attachment_never_supply_a_child() {
        for case in 0..4 {
            let mut t = popover();
            match case {
                0 => t.nodes.get_mut(&4).unwrap().id = 10,
                1 => t.nodes.get_mut(&4).unwrap().window = Some(2),
                2 => t.nodes.get_mut(&4).unwrap().parent = Some(1),
                _ => t.nodes.get_mut(&3).unwrap().children = vec![],
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]));
        }
    }
    #[test]
    fn exact_root_is_required_without_focus_or_geometry_selection() {
        let mut t = popover();
        t.roots = vec![2];
        assert_eq!(
            collect(&t, 42, 10, &t.windows),
            Err(DiscoveryStop::InvalidHost)
        );
        t.roots = vec![1, 1];
        assert_eq!(
            collect(&t, 42, 10, &t.windows),
            Err(DiscoveryStop::InvalidHost)
        );
        t.roots = vec![1];
        t.current.remove(&10);
        assert_eq!(
            collect(&t, 42, 10, &t.windows),
            Err(DiscoveryStop::InvalidHost)
        );
    }
    #[test]
    fn only_reciprocal_direct_sheet_chains_are_eligible_and_ids_are_sorted() {
        let mut t = popover();
        t.nodes.get_mut(&1).unwrap().children = vec![4];
        let sheet = t.nodes.get_mut(&4).unwrap();
        sheet.role = "AXSheet";
        sheet.parent = Some(1);
        sheet.children = vec![5];
        t.nodes.insert(
            5,
            Fact {
                role: "AXSheet",
                owner: 42,
                id: 15,
                parent: Some(4),
                window: Some(1),
                children: vec![],
            },
        );
        t.windows.push(window(15));
        t.current.insert(15);
        assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![15, 20]));
        assert_eq!(t.proof_calls.get(), 0);
        t.nodes.get_mut(&5).unwrap().window = Some(4);
        assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![20]));
        t.nodes.get_mut(&4).unwrap().parent = Some(3);
        assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]));
    }
}
