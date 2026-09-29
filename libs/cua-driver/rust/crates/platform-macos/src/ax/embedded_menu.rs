//! Read-only discovery of a context menu rendered inside its exact host.
//!
//! Some AppKit collections expose a live menu through AX hit testing but omit
//! it from the anchor's AXChildren. A recently delivered, window-bound right
//! click is only a search hint. Live hit testing, native identities and the
//! remaining reciprocal ancestry must prove every published menu.

const MAX_DEPTH: usize = 16;
const MAX_ITEMS: usize = 64;

trait EmbeddedTree {
    type Node: Clone;
    fn hidden(&self) -> Option<bool>;
    fn focused_host(&self, window: u32) -> Option<Self::Node>;
    fn owner(&self, node: &Self::Node) -> Option<i32>;
    fn window(&self, node: &Self::Node) -> Option<u32>;
    fn role(&self, node: &Self::Node) -> Option<String>;
    fn frame(&self, node: &Self::Node) -> Option<[f64; 4]>;
    fn parent(&self, node: &Self::Node) -> Option<Self::Node>;
    fn children(&self, node: &Self::Node) -> Option<Vec<Self::Node>>;
    fn hit(&self, point: [f64; 2]) -> Option<Self::Node>;
    fn same(&self, left: &Self::Node, right: &Self::Node) -> bool;
    fn within_budget(&self) -> bool;
}

#[derive(Clone)]
struct Seed<N> {
    pid: i32,
    window: u32,
    host: N,
    host_frame: [f64; 4],
    point: [f64; 2],
}

#[derive(Clone)]
struct Selection<N> {
    root: N,
    anchor: N,
    items: Vec<N>,
    frame: [f64; 4],
    hit_point: [f64; 2],
}

fn valid_frame(frame: &[f64; 4]) -> bool {
    frame.iter().all(|value| value.is_finite()) && frame[2] > 0.0 && frame[3] > 0.0
}

fn frame_matches(left: &[f64; 4], right: &[f64; 4]) -> bool {
    valid_frame(left)
        && valid_frame(right)
        && left.iter().zip(right).all(|(a, b)| (a - b).abs() <= 0.5)
}

fn contains(frame: &[f64; 4], point: [f64; 2]) -> bool {
    valid_frame(frame)
        && point.iter().all(|value| value.is_finite())
        && point[0] >= frame[0]
        && point[1] >= frame[1]
        && point[0] < frame[0] + frame[2]
        && point[1] < frame[1] + frame[3]
}

fn select<T: EmbeddedTree>(
    tree: &T,
    seed: &Seed<T::Node>,
    live_host_frame: [f64; 4],
) -> Option<Selection<T::Node>> {
    if !host_is_current(tree, seed, &live_host_frame) {
        return None;
    }
    // These are read-only AX probes near our own last right-click, never
    // pointer motion or a sweep of the user's hardware cursor position.
    for offset in [
        [8.0, 8.0],
        [-8.0, 8.0],
        [8.0, -8.0],
        [-8.0, -8.0],
        [0.0, 0.0],
    ] {
        if !tree.within_budget() {
            return None;
        }
        let point = [seed.point[0] + offset[0], seed.point[1] + offset[1]];
        if !contains(&live_host_frame, point) {
            continue;
        }
        let Some(hit) = tree.hit(point) else { continue };
        let Some(selection) = select_hit(tree, seed, hit, point) else {
            continue;
        };
        return host_is_current(tree, seed, &live_host_frame).then_some(selection);
    }
    None
}

fn host_is_current<T: EmbeddedTree>(tree: &T, seed: &Seed<T::Node>, live: &[f64; 4]) -> bool {
    tree.within_budget()
        && tree.hidden() == Some(false)
        && frame_matches(live, &seed.host_frame)
        && contains(live, seed.point)
        && tree
            .focused_host(seed.window)
            .is_some_and(|host| tree.same(&host, &seed.host))
        && tree.owner(&seed.host) == Some(seed.pid)
        && tree.window(&seed.host) == Some(seed.window)
        && tree.role(&seed.host).as_deref() == Some("AXWindow")
        && tree
            .frame(&seed.host)
            .is_some_and(|frame| frame_matches(&frame, live))
        && tree.within_budget()
}

fn same_surface<T: EmbeddedTree>(tree: &T, seed: &Seed<T::Node>, node: &T::Node) -> bool {
    tree.within_budget()
        && tree.owner(node) == Some(seed.pid)
        && tree.window(node) == Some(seed.window)
}

fn frame_inside(inner: &[f64; 4], outer: &[f64; 4]) -> bool {
    valid_frame(inner)
        && valid_frame(outer)
        && inner[0] >= outer[0]
        && inner[1] >= outer[1]
        && inner[0] + inner[2] <= outer[0] + outer[2]
        && inner[1] + inner[3] <= outer[1] + outer[3]
}

fn select_hit<T: EmbeddedTree>(
    tree: &T,
    seed: &Seed<T::Node>,
    hit: T::Node,
    point: [f64; 2],
) -> Option<Selection<T::Node>> {
    if !same_surface(tree, seed, &hit) {
        return None;
    }
    let root = match tree.role(&hit).as_deref() {
        Some("AXMenuItem") => tree.parent(&hit)?,
        Some("AXMenu") => hit.clone(),
        _ => return None,
    };
    if !same_surface(tree, seed, &root) || tree.role(&root).as_deref() != Some("AXMenu") {
        return None;
    }
    let frame = tree.frame(&root)?;
    if !frame_inside(&frame, &seed.host_frame) || !contains(&frame, point) {
        return None;
    }
    if !tree
        .frame(&hit)
        .is_some_and(|frame| contains(&frame, point))
    {
        return None;
    }
    let items = tree.children(&root)?;
    if items.is_empty() || items.len() > MAX_ITEMS {
        return None;
    }
    if !tree.same(&hit, &root) && !items.iter().any(|item| tree.same(item, &hit)) {
        return None;
    }
    for (index, item) in items.iter().enumerate() {
        if !same_surface(tree, seed, item)
            || tree.role(item).as_deref() != Some("AXMenuItem")
            || !tree
                .parent(item)
                .is_some_and(|parent| tree.same(&parent, &root))
            || !tree
                .children(item)
                .is_some_and(|children| children.is_empty())
            || items[..index].iter().any(|seen| tree.same(seen, item))
        {
            return None;
        }
        // Separators can have zero-height frames. They are not actionable,
        // but must still be native members of this exact live menu.
        let item_frame = tree.frame(item)?;
        if item_frame[3] == 0.0 {
            if !item_frame.iter().all(|v| v.is_finite())
                || item_frame[2] < 0.0
                || item_frame[0] < frame[0]
                || item_frame[1] < frame[1]
                || item_frame[0] + item_frame[2] > frame[0] + frame[2]
                || item_frame[1] > frame[1] + frame[3]
            {
                return None;
            }
        } else if !frame_inside(&item_frame, &frame) {
            return None;
        }
    }
    let anchor = tree.parent(&root)?;
    if !tree
        .frame(&anchor)
        .is_some_and(|frame| contains(&frame, seed.point))
    {
        return None;
    }
    let mut current = anchor.clone();
    let mut path = vec![root.clone()];
    for _ in 0..MAX_DEPTH {
        if !same_surface(tree, seed, &current) || path.iter().any(|node| tree.same(node, &current))
        {
            return None;
        }
        if tree.same(&current, &seed.host) {
            return tree.within_budget().then_some(Selection {
                root,
                anchor,
                items,
                frame,
                hit_point: point,
            });
        }
        if matches!(
            tree.role(&current).as_deref(),
            None | Some(
                "AXWindow" | "AXSheet" | "AXMenu" | "AXMenuBar" | "AXMenuBarItem" | "AXApplication"
            )
        ) {
            return None;
        }
        let parent = tree.parent(&current)?;
        let siblings = tree.children(&parent)?;
        if siblings.len() > 1024 || !siblings.iter().any(|node| tree.same(node, &current)) {
            return None;
        }
        path.push(current);
        current = parent;
    }
    None
}

fn same_selection<T: EmbeddedTree>(
    tree: &T,
    left: &Selection<T::Node>,
    right: &Selection<T::Node>,
) -> bool {
    tree.same(&left.root, &right.root)
        && tree.same(&left.anchor, &right.anchor)
        && frame_matches(&left.frame, &right.frame)
        && left.items.len() == right.items.len()
        && left
            .items
            .iter()
            .zip(&right.items)
            .all(|(a, b)| tree.same(a, b))
}

use super::bindings::{self, AXUIElementRef};
use core_foundation::{
    array::CFArray,
    base::{CFEqual, CFGetTypeID, CFRelease, CFRetain, CFTypeRef, TCFType},
    string::CFString,
};
use std::{
    collections::HashMap,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc, Mutex, OnceLock,
    },
    time::{Duration, Instant},
};

const SEED_LIFETIME: Duration = Duration::from_secs(120);
const MAX_SEEDS: usize = 128;

// CF reference counting is thread-safe. Store the owned pointer as usize so
// only the explicitly bounded AX readers below can dereference it.
struct NativeNode(usize);
impl NativeNode {
    unsafe fn owned(ptr: AXUIElementRef) -> Option<Self> {
        if ptr.is_null() {
            return None;
        }
        bindings::AXUIElementSetMessagingTimeout(ptr, 0.15);
        Some(Self(ptr as usize))
    }
    fn ptr(&self) -> AXUIElementRef {
        self.0 as AXUIElementRef
    }
}
impl Clone for NativeNode {
    fn clone(&self) -> Self {
        unsafe {
            CFRetain(self.0 as CFTypeRef);
        }
        Self(self.0)
    }
}
impl Drop for NativeNode {
    fn drop(&mut self) {
        unsafe {
            CFRelease(self.0 as CFTypeRef);
        }
    }
}

struct NativeTree {
    app: NativeNode,
    deadline: Instant,
}
impl NativeTree {
    fn new(pid: i32) -> Option<Self> {
        Some(Self {
            app: unsafe { NativeNode::owned(bindings::AXUIElementCreateApplication(pid)) }?,
            deadline: Instant::now() + Duration::from_secs(2),
        })
    }
}
impl EmbeddedTree for NativeTree {
    type Node = NativeNode;
    fn hidden(&self) -> Option<bool> {
        self.within_budget()
            .then(|| unsafe { bindings::copy_bool_attr(self.app.ptr(), "AXHidden") })
            .flatten()
    }
    fn focused_host(&self, window: u32) -> Option<NativeNode> {
        if !self.within_budget() {
            return None;
        }
        let host = unsafe {
            NativeNode::owned(bindings::copy_element_attr(
                self.app.ptr(),
                "AXFocusedWindow",
            )?)
        }?;
        (self.window(&host) == Some(window)).then_some(host)
    }
    fn owner(&self, node: &NativeNode) -> Option<i32> {
        if !self.within_budget() {
            return None;
        }
        let mut pid = 0;
        (unsafe { bindings::AXUIElementGetPid(node.ptr(), &mut pid) } == bindings::kAXErrorSuccess)
            .then_some(pid)
    }
    fn window(&self, node: &NativeNode) -> Option<u32> {
        self.within_budget()
            .then(|| unsafe { bindings::ax_get_window_id(node.ptr()) })
            .flatten()
    }
    fn role(&self, node: &NativeNode) -> Option<String> {
        self.within_budget()
            .then(|| unsafe { bindings::copy_string_attr(node.ptr(), "AXRole") })
            .flatten()
    }
    fn frame(&self, node: &NativeNode) -> Option<[f64; 4]> {
        self.within_budget()
            .then(|| unsafe { bindings::element_screen_rect(node.ptr()) })
            .flatten()
    }
    fn parent(&self, node: &NativeNode) -> Option<NativeNode> {
        if !self.within_budget() {
            return None;
        }
        unsafe { NativeNode::owned(bindings::copy_element_attr(node.ptr(), "AXParent")?) }
    }
    fn children(&self, node: &NativeNode) -> Option<Vec<NativeNode>> {
        if !self.within_budget() {
            return None;
        }
        unsafe {
            let attr = CFString::new("AXChildren");
            let mut value: CFTypeRef = std::ptr::null();
            let status = bindings::AXUIElementCopyAttributeValue(
                node.ptr(),
                attr.as_concrete_TypeRef(),
                &mut value,
            );
            if status != bindings::kAXErrorSuccess || value.is_null() {
                if !value.is_null() {
                    CFRelease(value);
                }
                return (matches!(
                    status,
                    bindings::kAXErrorAttributeUnsupported | bindings::kAXErrorNoValue
                ) && self.role(node).as_deref() == Some("AXMenuItem"))
                .then(Vec::new);
            }
            if CFGetTypeID(value) != CFArray::<CFTypeRef>::type_id() {
                CFRelease(value);
                return None;
            }
            let values = CFArray::<CFTypeRef>::wrap_under_create_rule(value as _);
            if values.len() > 1024 {
                return None;
            }
            let mut children = Vec::new();
            for index in 0..values.len() {
                if !self.within_budget() {
                    return None;
                }
                let child = *values.get(index)?;
                if CFGetTypeID(child) != bindings::AXUIElementGetTypeID() {
                    return None;
                }
                CFRetain(child);
                children.push(NativeNode::owned(child as AXUIElementRef)?);
            }
            Some(children)
        }
    }
    fn hit(&self, point: [f64; 2]) -> Option<NativeNode> {
        if !self.within_budget() {
            return None;
        }
        unsafe {
            let mut element = std::ptr::null_mut();
            let status = bindings::AXUIElementCopyElementAtPosition(
                self.app.ptr(),
                point[0] as f32,
                point[1] as f32,
                &mut element,
            );
            if status != bindings::kAXErrorSuccess {
                if !element.is_null() {
                    CFRelease(element as CFTypeRef);
                }
                return None;
            }
            NativeNode::owned(element)
        }
    }
    fn same(&self, left: &NativeNode, right: &NativeNode) -> bool {
        unsafe { CFEqual(left.0 as CFTypeRef, right.0 as CFTypeRef) != 0 }
    }
    fn within_budget(&self) -> bool {
        Instant::now() < self.deadline
    }
}

#[derive(Clone)]
struct TimedSeed {
    seed: Seed<NativeNode>,
    generation: u64,
    created: Instant,
}
type SeedKey = (i32, u32);
fn seeds() -> &'static Mutex<HashMap<SeedKey, TimedSeed>> {
    static SEEDS: OnceLock<Mutex<HashMap<SeedKey, TimedSeed>>> = OnceLock::new();
    SEEDS.get_or_init(|| Mutex::new(HashMap::new()))
}
fn recent_seed(pid: i32, window: u32) -> Option<TimedSeed> {
    let mut seeds = seeds().lock().unwrap();
    seeds.retain(|_, seed| seed.created.elapsed() < SEED_LIFETIME);
    seeds.get(&(pid, window)).cloned()
}
fn live_frame(pid: i32, window: u32) -> Option<[f64; 4]> {
    let host = crate::windows::window_info_by_id(window)?;
    (host.pid == pid
        && host.layer == 0
        && host.is_on_screen
        && host.on_current_space != Some(false))
    .then_some([
        host.bounds.x,
        host.bounds.y,
        host.bounds.width,
        host.bounds.height,
    ])
}

/// Record only an already dispatched exact-window gesture. This does not
/// confirm that a menu opened and cannot authorize any future input.
pub(crate) fn remember_right_click(pid: i32, window: u32, point: [f64; 2]) {
    seeds().lock().unwrap().remove(&(pid, window));
    let Some(tree) = NativeTree::new(pid) else {
        return;
    };
    let Some(host_frame) = live_frame(pid, window) else {
        return;
    };
    let Some(host) = tree.focused_host(window) else {
        return;
    };
    let seed = Seed {
        pid,
        window,
        host,
        host_frame,
        point,
    };
    if !host_is_current(&tree, &seed, &host_frame) {
        return;
    }
    static GENERATION: AtomicU64 = AtomicU64::new(1);
    let generation = GENERATION.fetch_add(1, Ordering::Relaxed);
    let mut seeds = seeds().lock().unwrap();
    seeds.retain(|_, seed| seed.created.elapsed() < SEED_LIFETIME);
    if seeds.len() >= MAX_SEEDS || generation == 0 {
        return;
    }
    seeds.insert(
        (pid, window),
        TimedSeed {
            seed,
            generation,
            created: Instant::now(),
        },
    );
}

#[derive(PartialEq)]
struct ItemSignature {
    title: Option<String>,
    actions: Vec<String>,
    enabled: Option<bool>,
}
fn signatures(tree: &NativeTree, selection: &Selection<NativeNode>) -> Option<Vec<ItemSignature>> {
    let mut result = Vec::new();
    for item in &selection.items {
        if !tree.within_budget() {
            return None;
        }
        let title = unsafe { bindings::copy_string_attr(item.ptr(), "AXTitle") };
        let actions = unsafe { bindings::copy_action_names(item.ptr()) };
        let enabled = unsafe { bindings::copy_bool_attr(item.ptr(), "AXEnabled") };
        if actions.len() > 32 {
            return None;
        }
        result.push(ItemSignature {
            title,
            actions,
            enabled,
        });
    }
    tree.within_budget().then_some(result)
}

/// Retained alongside the AX snapshot, never keyed only by a recycled element
/// index. It cannot grant activation or pointer authority to a menu.
pub(crate) struct EmbeddedMenuProof {
    seed: TimedSeed,
    selection: Selection<NativeNode>,
    signatures: Vec<ItemSignature>,
}
impl EmbeddedMenuProof {
    pub(crate) fn root(&self) -> AXUIElementRef {
        self.selection.root.ptr()
    }
    pub(crate) fn is_live(&self) -> bool {
        let pid = self.seed.seed.pid;
        let window = self.seed.seed.window;
        let Some(current) = recent_seed(pid, window) else {
            return false;
        };
        if current.generation != self.seed.generation {
            return false;
        }
        let Some(tree) = NativeTree::new(pid) else {
            return false;
        };
        let Some(frame) = live_frame(pid, window) else {
            return false;
        };
        if !host_is_current(&tree, &self.seed.seed, &frame) {
            return false;
        }
        let Some(hit) = tree.hit(self.selection.hit_point) else {
            return false;
        };
        let Some(selection) = select_hit(&tree, &self.seed.seed, hit, self.selection.hit_point)
        else {
            return false;
        };
        same_selection(&tree, &self.selection, &selection)
            && signatures(&tree, &selection).as_ref() == Some(&self.signatures)
            && host_is_current(&tree, &self.seed.seed, &frame)
            && recent_seed(pid, window).is_some_and(|seed| seed.generation == self.seed.generation)
            && tree.within_budget()
    }
}

pub(crate) fn active_menu(pid: i32, window: u32) -> Option<Arc<EmbeddedMenuProof>> {
    let seed = recent_seed(pid, window)?;
    let tree = NativeTree::new(pid)?;
    let frame = live_frame(pid, window)?;
    let selection = select(&tree, &seed.seed, frame)?;
    let signatures = signatures(&tree, &selection)?;
    if !recent_seed(pid, window).is_some_and(|current| current.generation == seed.generation) {
        return None;
    }
    Some(Arc::new(EmbeddedMenuProof {
        seed,
        selection,
        signatures,
    }))
}

#[derive(Debug)]
pub(crate) struct StaleEmbeddedMenu;
impl std::fmt::Display for StaleEmbeddedMenu {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("The observed embedded context menu changed or closed. Re-observe the exact window; no menu action was sent.")
    }
}
impl std::error::Error for StaleEmbeddedMenu {}
impl StaleEmbeddedMenu {
    pub(crate) fn result(&self, pid: i32, window_id: u32) -> cua_driver_core::protocol::ToolResult {
        cua_driver_core::protocol::ToolResult::error(self.to_string()).with_structured(
            serde_json::json!({
                "code":"stale_observation", "reason":"embedded_menu_changed", "effect":"refused",
                "retryable":true, "pid":pid, "window_id":window_id,
            }),
        )
    }
}

#[cfg(test)]
pub(crate) fn expired_test_proof() -> Arc<EmbeddedMenuProof> {
    // A valid AX object for a nonexistent process. No live application is
    // read: this generation was never registered, so is_live returns early.
    let node =
        unsafe { NativeNode::owned(bindings::AXUIElementCreateApplication(i32::MAX)) }.unwrap();
    Arc::new(EmbeddedMenuProof {
        seed: TimedSeed {
            seed: Seed {
                pid: i32::MAX,
                window: u32::MAX,
                host: node.clone(),
                host_frame: [0.0, 0.0, 1.0, 1.0],
                point: [0.0, 0.0],
            },
            generation: 0,
            created: Instant::now() - SEED_LIFETIME,
        },
        selection: Selection {
            root: node.clone(),
            anchor: node,
            items: vec![],
            frame: [0.0, 0.0, 1.0, 1.0],
            hit_point: [0.0, 0.0],
        },
        signatures: vec![],
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[derive(Clone)]
    struct Node {
        owner: i32,
        window: u32,
        role: &'static str,
        frame: [f64; 4],
        parent: Option<u32>,
        children: Vec<u32>,
    }

    #[derive(Clone)]
    struct Tree {
        nodes: BTreeMap<u32, Node>,
        hidden: Option<bool>,
        focused: Option<u32>,
        hit: Option<u32>,
        budget: bool,
    }

    impl EmbeddedTree for Tree {
        type Node = u32;
        fn hidden(&self) -> Option<bool> {
            self.hidden
        }
        fn focused_host(&self, window: u32) -> Option<u32> {
            self.focused.filter(|id| self.nodes[id].window == window)
        }
        fn owner(&self, node: &u32) -> Option<i32> {
            self.nodes.get(node).map(|n| n.owner)
        }
        fn window(&self, node: &u32) -> Option<u32> {
            self.nodes.get(node).map(|n| n.window)
        }
        fn role(&self, node: &u32) -> Option<String> {
            self.nodes.get(node).map(|n| n.role.to_owned())
        }
        fn frame(&self, node: &u32) -> Option<[f64; 4]> {
            self.nodes.get(node).map(|n| n.frame)
        }
        fn parent(&self, node: &u32) -> Option<u32> {
            self.nodes.get(node)?.parent
        }
        fn children(&self, node: &u32) -> Option<Vec<u32>> {
            self.nodes.get(node).map(|n| n.children.clone())
        }
        fn hit(&self, _point: [f64; 2]) -> Option<u32> {
            self.hit
        }
        fn same(&self, left: &u32, right: &u32) -> bool {
            left == right
        }
        fn within_budget(&self) -> bool {
            self.budget
        }
    }

    fn fixture() -> (Tree, Seed<u32>) {
        let host_frame = [220.0, 301.0, 660.0, 510.0];
        let mut nodes = BTreeMap::new();
        for (id, role, frame, parent, children) in [
            (1, "AXWindow", host_frame, None, vec![2]),
            (2, "AXList", [425.0, 401.0, 440.0, 400.0], Some(1), vec![3]),
            // The single nonreciprocal edge observed in the live Freeform UI.
            (3, "AXButton", [425.0, 421.0, 440.0, 68.0], Some(2), vec![]),
            (
                4,
                "AXMenu",
                [640.0, 452.0, 200.0, 200.0],
                Some(3),
                vec![5, 6],
            ),
            (
                5,
                "AXMenuItem",
                [642.0, 454.0, 194.0, 25.0],
                Some(4),
                vec![],
            ),
            (
                6,
                "AXMenuItem",
                [642.0, 479.0, 194.0, 25.0],
                Some(4),
                vec![],
            ),
        ] {
            nodes.insert(
                id,
                Node {
                    owner: 17,
                    window: 700,
                    role,
                    frame,
                    parent,
                    children,
                },
            );
        }
        (
            Tree {
                nodes,
                hidden: Some(false),
                focused: Some(1),
                hit: Some(5),
                budget: true,
            },
            Seed {
                pid: 17,
                window: 700,
                host: 1,
                host_frame,
                point: [642.0, 454.0],
            },
        )
    }

    #[test]
    fn embedded_menu_discovers_live_menu_omitted_from_anchor_children() {
        let (tree, seed) = fixture();
        let selection = select(&tree, &seed, seed.host_frame)
            .expect("live embedded context menu is missing from the observation");
        assert_eq!(selection.root, 4);
        assert_eq!(selection.anchor, 3);
        assert_eq!(selection.items, vec![5, 6]);
        assert_eq!(selection.frame, tree.nodes[&4].frame);
        assert!(contains(&selection.frame, selection.hit_point));
    }

    fn rejects(change: impl FnOnce(&mut Tree, &mut Seed<u32>)) {
        let (mut tree, mut seed) = fixture();
        assert!(
            select(&tree, &seed, seed.host_frame).is_some(),
            "positive fixture must remain reachable"
        );
        change(&mut tree, &mut seed);
        assert!(select(&tree, &seed, seed.host_frame).is_none());
    }

    #[test]
    fn embedded_menu_rejects_closed_menu_with_retained_frame() {
        rejects(|tree, _| tree.hit = Some(3));
    }

    #[test]
    fn embedded_menu_rejects_foreign_process_and_window() {
        for id in 1..=6 {
            rejects(|tree, _| tree.nodes.get_mut(&id).unwrap().owner = 19);
            rejects(|tree, _| tree.nodes.get_mut(&id).unwrap().window = 701);
        }
    }

    #[test]
    fn embedded_menu_rejects_replaced_or_unfocused_host() {
        rejects(|tree, _| tree.focused = None);
        rejects(|tree, _| {
            tree.nodes.insert(10, tree.nodes[&1].clone());
            tree.focused = Some(10);
        });
    }

    #[test]
    fn embedded_menu_rejects_moved_host_and_hidden_app() {
        rejects(|tree, _| tree.nodes.get_mut(&1).unwrap().frame[0] += 10.0);
        rejects(|tree, _| tree.hidden = Some(true));
        rejects(|tree, _| tree.hidden = None);
        let (tree, seed) = fixture();
        let mut moved = seed.host_frame;
        moved[0] += 10.0;
        assert!(select(&tree, &seed, moved).is_none());
    }

    #[test]
    fn embedded_menu_rejects_other_missing_parent_edges_and_cycles() {
        rejects(|tree, _| tree.nodes.get_mut(&2).unwrap().children.clear());
        rejects(|tree, _| tree.nodes.get_mut(&1).unwrap().children.clear());
        rejects(|tree, _| {
            tree.nodes.get_mut(&4).unwrap().children.remove(0);
        });
        rejects(|tree, _| tree.nodes.get_mut(&2).unwrap().parent = Some(3));
    }

    #[test]
    fn embedded_menu_rejects_outside_anchor_and_menu_frame() {
        rejects(|_, seed| seed.point = [350.0, 350.0]);
        rejects(|tree, _| tree.nodes.get_mut(&4).unwrap().frame[0] = 100.0);
        rejects(|tree, _| tree.nodes.get_mut(&4).unwrap().frame[2] = 800.0);
        rejects(|tree, _| tree.nodes.get_mut(&4).unwrap().frame[0] = f64::NAN);
        rejects(|tree, _| tree.nodes.get_mut(&5).unwrap().frame[0] = 50.0);
    }

    #[test]
    fn embedded_menu_rejects_crossing_window_or_menu_bar() {
        for role in [
            "AXWindow",
            "AXSheet",
            "AXMenuBar",
            "AXApplication",
            "AXMenu",
        ] {
            rejects(|tree, _| tree.nodes.get_mut(&2).unwrap().role = role);
        }
    }

    #[test]
    fn embedded_menu_rejects_unknown_children_and_expired_budget() {
        rejects(|tree, _| tree.nodes.get_mut(&6).unwrap().role = "AXTextField");
        rejects(|tree, _| tree.nodes.get_mut(&6).unwrap().children.push(5));
        rejects(|tree, _| tree.budget = false);
        rejects(|tree, _| tree.nodes.get_mut(&4).unwrap().children = vec![5; MAX_ITEMS + 1]);
    }

    #[test]
    fn embedded_menu_revalidation_rejects_replaced_root_anchor_and_items() {
        let (tree, seed) = fixture();
        let original = select(&tree, &seed, seed.host_frame).unwrap();
        assert!(same_selection(&tree, &original, &original));
        for member in ["root", "anchor", "items", "frame"] {
            let mut changed = original.clone();
            match member {
                "root" => changed.root = 99,
                "anchor" => changed.anchor = 99,
                "items" => changed.items.reverse(),
                _ => changed.frame[0] += 5.0,
            }
            assert!(!same_selection(&tree, &original, &changed), "{member}");
        }
    }

    #[test]
    fn embedded_menu_accepts_reciprocal_anchor_without_weakening_leaf_proof() {
        let (mut tree, seed) = fixture();
        tree.nodes.get_mut(&3).unwrap().children.push(4);
        assert!(select(&tree, &seed, seed.host_frame).is_some());
        tree.nodes.get_mut(&6).unwrap().parent = Some(3);
        assert!(select(&tree, &seed, seed.host_frame).is_none());
    }

    #[test]
    fn embedded_menu_keeps_zero_height_separators_but_rejects_outside_geometry() {
        let (mut tree, seed) = fixture();
        tree.nodes.get_mut(&6).unwrap().frame[3] = 0.0;
        assert!(select(&tree, &seed, seed.host_frame).is_some());
        tree.nodes.get_mut(&6).unwrap().frame[1] = 1000.0;
        assert!(select(&tree, &seed, seed.host_frame).is_none());
    }
}
