//! Positive AX attachments for an exact window capture; never compositor-root
//! inference. Discovery deliberately excludes web/content subtrees and is not
//! exhaustive. An empty result means no proven additional surfaces. A caller
//! must rediscover after capture and discard pixels if the selected set changes.

use crate::ax::bindings::{
    ax_get_window_id, copy_element_attr, copy_string_attr, element_screen_rect,
    kAXErrorAttributeUnsupported, kAXErrorNoValue, kAXErrorSuccess, AXError,
    AXUIElementCopyAttributeValue, AXUIElementCreateApplication, AXUIElementGetPid,
    AXUIElementGetTypeID, AXUIElementRef, AXUIElementSetMessagingTimeout,
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
    fn focused(&self) -> Option<Self::Node>;
    fn role(&self, node: &Self::Node) -> Option<String>;
    fn owner(&self, node: &Self::Node) -> Option<i32>;
    fn id(&self, node: &Self::Node) -> Option<u32>;
    fn frame(&self, node: &Self::Node) -> Option<[f64; 4]>;
    fn parent(&self, node: &Self::Node) -> Option<Self::Node>;
    fn window(&self, node: &Self::Node) -> Option<Self::Node>;
    // Only the Outline-menu route permits an explicitly absent leaf AXWindow.
    // Unlike window(), an error or malformed value must never become absence.
    fn menu_window(&self, node: &Self::Node) -> Result<Option<Self::Node>, DiscoveryStop>;
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

#[derive(Debug, PartialEq, Eq)]
struct MenuProof {
    id: u32,
    members: Vec<(i32, String)>,
    frame: [u64; 4],
}

// Menu discovery alone may traverse one native provider and return to the
// original host. This never changes the same-PID popover/sheet proof above.
// Even a search prefix must have reciprocal edges; no remote application,
// web/table subtree or intervening AX surface can supply an attachment.
fn menu_path_members<T: Tree>(
    tree: &T,
    pid: i32,
    path: &[T::Node],
    terminal_menu: bool,
) -> Result<Option<Vec<(i32, String)>>, DiscoveryStop> {
    let mut members = Vec::new();
    let mut provider = None;
    let mut returned = false;
    for (index, node) in path.iter().enumerate() {
        budget(tree)?;
        let (Some(owner), Some(role)) = (tree.owner(node), tree.role(node)) else {
            budget(tree)?;
            return Ok(None);
        };
        let is_menu = terminal_menu && index + 1 == path.len();
        if owner <= 0
            || (index == 0 && (owner != pid || role != "AXWindow"))
            || (index > 0 && !(if is_menu { role == "AXMenu" } else { container(&role) }))
            || (is_menu && owner != pid)
        {
            return Ok(None);
        }
        if owner == pid {
            returned |= provider.is_some();
        } else {
            if returned || provider.is_some_and(|previous| previous != owner) {
                return Ok(None);
            }
            provider = Some(owner);
        }
        if index > 0 {
            let parent = &path[index - 1];
            if !tree.parent(node).is_some_and(|live| tree.same(&live, parent)) {
                budget(tree)?;
                return Ok(None);
            }
            let children = tree.children(parent)?;
            if children.len() > MAX_CHILDREN {
                return Err(DiscoveryStop::ChildLimit);
            }
            if children.iter().filter(|child| tree.same(child, node)).count() != 1 {
                return Ok(None);
            }
        }
        members.push((owner, role));
    }
    budget(tree)?;
    Ok(Some(members))
}

fn prove_menu_path<T: Tree>(
    tree: &T,
    pid: i32,
    host: &WindowInfo,
    path: &[T::Node],
    windows: &[WindowInfo],
) -> Result<Option<MenuProof>, DiscoveryStop> {
    budget(tree)?;
    if path.len() < 3 {
        return Ok(None);
    }
    let Some(members) = menu_path_members(tree, pid, path, true)? else {
        return Ok(None);
    };
    let anchor = &members[members.len() - 2];
    if anchor.0 != pid || anchor.1 != "AXPopUpButton" || !surface_matches(tree, &path[0], host) {
        budget(tree)?;
        return Ok(None);
    }
    let Some(frame) = tree.frame(path.last().expect("nonempty menu path")) else {
        budget(tree)?;
        return Ok(None);
    };
    if !frame.iter().all(|v| v.is_finite()) || frame[2] <= 0.0 || frame[3] <= 0.0 {
        return Ok(None);
    }
    // The existing popup-level route permits a native provider and missing SPI
    // IDs. Layer-zero windows need the narrower, same-process inherited-host
    // proof below; being a same-PID ordinary window is never sufficient.
    let candidate = |window: &WindowInfo| {
        let b = &window.bounds;
        window.pid == pid && window.window_id != host.window_id && window.window_id != 0
            && window.is_on_screen && window.on_current_space != Some(false)
            && frame.iter().zip([b.x, b.y, b.width, b.height])
                .all(|(ax, cg)| cg.is_finite() && (ax - cg).abs() <= 0.5)
    };
    let mut layer_zero_proven = false;
    if members.iter().all(|(owner, _)| *owner == pid)
        && windows.iter().any(|window| window.layer == 0 && candidate(window))
    {
        layer_zero_proven = true;
        for (index, node) in path.iter().enumerate() {
            budget(tree)?;
            if tree.id(node) != Some(host.window_id)
                || (index > 0 && !tree.window(node).is_some_and(|root| tree.same(&root, &path[0])))
            {
                budget(tree)?;
                layer_zero_proven = false;
                break;
            }
        }
        budget(tree)?;
    }
    // Count all eligible physical matches together: a coincident layer0/101
    // pair is ambiguous for the new same-process route, not a layer priority.
    let mut matches = windows.iter().filter(|window| {
        candidate(window) && (window.layer == 101 || (window.layer == 0 && layer_zero_proven))
    });
    let Some(menu) = matches.next() else { return Ok(None) };
    if matches.next().is_some() || exact_window(windows, pid, menu.window_id).is_none()
        || !tree.current_space(menu.window_id)
    {
        budget(tree)?;
        return Ok(None);
    }
    budget(tree)?;
    Ok(Some(MenuProof { id: menu.window_id, members, frame: frame.map(f64::to_bits) }))
}

// Collection roles are local to this focused-popover route, never the shared
// menu/provider/container walk. Focus supplies a candidate, not authority.
fn host_collection_role(role: &str) -> bool {
    matches!(role, "AXCell" | "AXRow" | "AXOutline" | "AXLayoutArea")
}

fn focused_popover_descendant_role(role: &str) -> bool {
    matches!(
        role,
        "AXButton"
            | "AXTextField"
            | "AXTextArea"
            | "AXPopUpButton"
            | "AXCheckBox"
            | "AXRadioButton"
            | "AXDateTimeArea"
            | "AXRadioGroup"
            | "AXGroup"
            | "AXScrollArea"
            | "AXSplitGroup"
            | "AXToolbar"
    )
}

fn reciprocal_edge<T: Tree>(
    tree: &T,
    parent: &T::Node,
    child: &T::Node,
) -> Result<bool, DiscoveryStop> {
    budget(tree)?;
    if !tree
        .parent(child)
        .is_some_and(|node| tree.same(&node, parent))
    {
        budget(tree)?;
        return Ok(false);
    }
    let children = tree.children(parent)?;
    if children.len() > MAX_CHILDREN {
        return Err(DiscoveryStop::ChildLimit);
    }
    budget(tree)?;
    Ok(children
        .iter()
        .filter(|node| tree.same(node, child))
        .count()
        == 1)
}

fn prove_collection_popover<T: Tree>(
    tree: &T,
    pid: i32,
    host: &WindowInfo,
    path: &[T::Node],
    windows: &[WindowInfo],
) -> Result<Option<u32>, DiscoveryStop> {
    budget(tree)?;
    let Some(leaf) = path.last().filter(|_| path.len() >= 3) else {
        return Ok(None);
    };
    if tree.role(leaf).as_deref() != Some("AXPopover") {
        return Ok(None);
    }
    let Some(id) = tree.id(leaf).filter(|id| *id != host.window_id) else {
        return Ok(None);
    };
    let Some(physical) = exact_window(windows, pid, id) else {
        return Ok(None);
    };
    if !surface_matches(tree, &path[0], host)
        || !surface_matches(tree, leaf, physical)
        || !tree
            .window(leaf)
            .is_some_and(|node| tree.same(&node, &path[0]))
    {
        budget(tree)?;
        return Ok(None);
    }
    let mut collection = false;
    for node in &path[1..path.len() - 1] {
        budget(tree)?;
        let Some(role) = tree.role(node) else {
            return Ok(None);
        };
        collection |= host_collection_role(&role);
        if !(container(&role) || host_collection_role(&role))
            || tree.owner(node) != Some(pid)
            || tree.id(node) != Some(host.window_id)
            || !tree
                .window(node)
                .is_some_and(|root| tree.same(&root, &path[0]))
        {
            budget(tree)?;
            return Ok(None);
        }
    }
    // This route cannot rescue an unrelated failure of the legacy proof.
    if !collection {
        return Ok(None);
    }
    for pair in path.windows(2) {
        if !reciprocal_edge(tree, &pair[0], &pair[1])? {
            return Ok(None);
        }
    }
    let proven = tree.popover(leaf, pid, host.window_id);
    budget(tree)?;
    Ok(proven.then_some(id))
}

fn collect_focused_collection_popover<T: Tree>(
    tree: &T,
    pid: i32,
    host: &WindowInfo,
    root: &T::Node,
    windows: &[WindowInfo],
    visited: &mut Vec<T::Node>,
) -> Result<Vec<u32>, DiscoveryStop> {
    let result = (|| {
        // Run only after the entire legacy discovery (including menu/provider
        // revalidation) returned empty. No new AX reads on legacy nonempty/Err.
        if !windows.iter().any(|window| {
            window.pid == pid
                && window.window_id != 0
                && window.window_id != host.window_id
                && window.is_on_screen
                && window.on_current_space != Some(false)
        }) {
            return Ok(Vec::new());
        }
        budget(tree)?;
        let focused = tree.focused();
        budget(tree)?;
        let Some(mut node) = focused else {
            return Ok(Vec::new());
        };
        let mut upward = Vec::new();
        let mut popover_index = None;
        loop {
            budget(tree)?;
            if upward.len() >= MAX_DEPTH {
                return Err(DiscoveryStop::DepthLimit);
            }
            if upward.iter().any(|prior| tree.same(prior, &node)) {
                return Err(DiscoveryStop::Cycle);
            }
            if !visited.iter().any(|prior| tree.same(prior, &node)) {
                if visited.len() >= MAX_NODES {
                    return Err(DiscoveryStop::NodeLimit);
                }
                visited.push(node.clone());
            }
            upward.push(node.clone());
            if tree.owner(&node) != Some(pid) {
                return Ok(Vec::new());
            }
            let role = tree.role(&node);
            match role.as_deref() {
                Some("AXPopover") if popover_index.is_none() => {
                    popover_index = Some(upward.len() - 1);
                }
                Some("AXWindow") if popover_index.is_some() && tree.same(&node, root) => break,
                Some(role) if popover_index.is_none() && focused_popover_descendant_role(role) => {}
                Some(role)
                    if popover_index.is_some()
                        && (container(role) || host_collection_role(role)) => {}
                _ => return Ok(Vec::new()),
            }
            let parent = tree.parent(&node);
            budget(tree)?;
            let Some(parent) = parent else {
                return Ok(Vec::new());
            };
            // Descendants only locate the first popover. Retain the legacy native
            // role/reciprocity boundary; host-side edges are fully proved below.
            if popover_index.is_none() && !reciprocal_edge(tree, &parent, &node)? {
                return Ok(Vec::new());
            }
            node = parent;
        }
        let mut path = upward.split_off(popover_index.expect("popover before host"));
        path.reverse();
        let id = prove_collection_popover(tree, pid, host, &path, windows)?;
        budget(tree)?;
        let Some(id) = id else { return Ok(Vec::new()) };
        let fresh = tree.fresh_windows().ok_or(DiscoveryStop::Changed)?;
        let live_host = exact_window(&fresh, pid, host.window_id).ok_or(DiscoveryStop::Changed)?;
        let before = exact_window(windows, pid, id).ok_or(DiscoveryStop::Changed)?;
        let after = exact_window(&fresh, pid, id).ok_or(DiscoveryStop::Changed)?;
        if !same_identity(host, live_host)
            || !same_identity(before, after)
            || !tree.same(root, &exact_root(tree, live_host)?)
            || prove_collection_popover(tree, pid, live_host, &path, &fresh)? != Some(id)
        {
            return Err(DiscoveryStop::Changed);
        }
        budget(tree)?;
        Ok(vec![id])
    })();
    budget(tree)?;
    result
}

fn outline_structure(role: &str) -> bool {
    matches!(role, "AXGroup" | "AXSplitGroup" | "AXLayoutArea" | "AXScrollArea")
}

fn charge_outline_node<T: Tree>(
    tree: &T,
    visited: &mut Vec<T::Node>,
    node: &T::Node,
) -> Result<(), DiscoveryStop> {
    budget(tree)?;
    if !visited.iter().any(|prior| tree.same(prior, node)) {
        if visited.len() >= MAX_NODES {
            return Err(DiscoveryStop::NodeLimit);
        }
        visited.push(node.clone());
    }
    Ok(())
}

// No row/cell/button/provider traversal. Every structural node, including the
// terminal Outline, must positively inherit this exact physical and AX host.
fn outline_path_members<T: Tree>(
    tree: &T,
    pid: i32,
    host: &WindowInfo,
    path: &[T::Node],
) -> Result<Option<Vec<(i32, String)>>, DiscoveryStop> {
    budget(tree)?;
    if path.len() < 2 || path.len() > MAX_DEPTH || !surface_matches(tree, &path[0], host) {
        budget(tree)?;
        return Ok(None);
    }
    let mut members = Vec::new();
    for (index, node) in path.iter().enumerate() {
        budget(tree)?;
        if path[..index].iter().any(|prior| tree.same(prior, node)) {
            return Err(DiscoveryStop::Cycle);
        }
        let Some(role) = tree.role(node) else { return Err(DiscoveryStop::AxUnavailable) };
        let allowed = if index == 0 { role == "AXWindow" } else {
            outline_structure(&role) || (index + 1 == path.len() && role == "AXOutline")
        };
        if !allowed || tree.owner(node) != Some(pid) || tree.id(node) != Some(host.window_id) {
            budget(tree)?;
            return Ok(None);
        }
        if index > 0 && (!tree.window(node).is_some_and(|root| tree.same(&root, &path[0]))
            || !reciprocal_edge(tree, &path[index - 1], node)?)
        {
            budget(tree)?;
            return Ok(None);
        }
        members.push((pid, role));
    }
    budget(tree)?;
    Ok(Some(members))
}

#[derive(Debug, PartialEq, Eq)]
struct OutlineMenuProof {
    menu: MenuProof,
    leaf_window_present: bool,
}

fn prove_outline_menu<T: Tree>(
    tree: &T,
    pid: i32,
    host: &WindowInfo,
    path: &[T::Node],
    windows: &[WindowInfo],
) -> Result<Option<OutlineMenuProof>, DiscoveryStop> {
    budget(tree)?;
    if path.len() < 3 || path.len() > MAX_DEPTH { return Ok(None) }
    let prefix = &path[..path.len() - 1];
    let Some(mut members) = outline_path_members(tree, pid, host, prefix)? else { return Ok(None) };
    if members.last().map(|(_, role)| role.as_str()) != Some("AXOutline") { return Ok(None) }
    let leaf = path.last().expect("nonempty Outline menu path");
    if tree.role(leaf).as_deref() != Some("AXMenu") || tree.owner(leaf) != Some(pid)
        || tree.id(leaf) != Some(host.window_id)
        || prefix.iter().any(|node| tree.same(node, leaf))
        || !reciprocal_edge(tree, prefix.last().expect("Outline anchor"), leaf)?
    {
        budget(tree)?;
        return Ok(None);
    }
    let logical = tree.menu_window(leaf)?;
    if logical.as_ref().is_some_and(|root| !tree.same(root, &path[0])) { return Ok(None) }
    let Some(frame) = tree.frame(leaf) else { budget(tree)?; return Ok(None) };
    if !frame.iter().all(|v| v.is_finite()) || frame[2] <= 0.0 || frame[3] <= 0.0 { return Ok(None) }
    let mut matches = windows.iter().filter(|window| {
        let b = &window.bounds;
        window.pid == pid && window.window_id != 0 && window.window_id != host.window_id
            && matches!(window.layer, 0 | 101) && window.is_on_screen
            && window.on_current_space != Some(false)
            && frame.iter().zip([b.x, b.y, b.width, b.height])
                .all(|(ax, cg)| cg.is_finite() && (ax - cg).abs() <= 0.5)
    });
    let Some(menu) = matches.next() else { budget(tree)?; return Ok(None) };
    if menu.layer != 101 || matches.next().is_some()
        || exact_window(windows, pid, menu.window_id).is_none()
        || !tree.current_space(menu.window_id)
    {
        budget(tree)?;
        return Ok(None);
    }
    members.push((pid, "AXMenu".into()));
    budget(tree)?;
    Ok(Some(OutlineMenuProof {
        menu: MenuProof { id: menu.window_id, members, frame: frame.map(f64::to_bits) },
        leaf_window_present: logical.is_some(),
    }))
}

fn collect_outline_menus<T: Tree>(
    tree: &T,
    pid: i32,
    host: &WindowInfo,
    root: &T::Node,
    windows: &[WindowInfo],
    visited: &mut Vec<T::Node>,
    seeds: &[Vec<T::Node>],
) -> Result<Vec<u32>, DiscoveryStop> {
    if seeds.is_empty() || !windows.iter().any(|window| window.pid == pid
        && window.window_id != 0 && window.window_id != host.window_id && window.layer == 101
        && window.is_on_screen && window.on_current_space != Some(false))
    {
        return Ok(Vec::new());
    }
    let mut queue = VecDeque::from(seeds.to_vec());
    let mut entered = Vec::new();
    let mut admitted: Vec<(Vec<T::Node>, OutlineMenuProof)> = Vec::new();
    while let Some(path) = queue.pop_front() {
        budget(tree)?;
        if path.len() > MAX_DEPTH { return Err(DiscoveryStop::DepthLimit) }
        let node = path.last().ok_or(DiscoveryStop::Changed)?;
        charge_outline_node(tree, visited, node)?;
        if entered.iter().any(|prior| tree.same(prior, node)) { return Err(DiscoveryStop::Cycle) }
        entered.push(node.clone());
        let Some(members) = outline_path_members(tree, pid, host, &path)? else {
            // An unproven retained prefix never becomes a search authority.
            return Ok(Vec::new());
        };
        let is_outline = members.last().map(|(_, role)| role.as_str()) == Some("AXOutline");
        let children = tree.children(node)?;
        if children.len() > MAX_CHILDREN { return Err(DiscoveryStop::ChildLimit) }
        for child in children {
            charge_outline_node(tree, visited, &child)?;
            let role = tree.role(&child).ok_or(DiscoveryStop::AxUnavailable)?;
            if role.is_empty() || role == "AXUnknown" { return Err(DiscoveryStop::AxUnavailable) }
            if is_outline {
                if role != "AXMenu" { continue } // Never read rows/cells or submenu contents.
                if path.len() == MAX_DEPTH { return Err(DiscoveryStop::DepthLimit) }
                let mut candidate = path.clone(); candidate.push(child);
                if let Some(proof) = prove_outline_menu(tree, pid, host, &candidate, windows)? {
                    if admitted.len() >= MAX_ATTACHMENTS { return Err(DiscoveryStop::AttachmentLimit) }
                    if admitted.iter().any(|(_, prior)| prior.menu.id == proof.menu.id) {
                        return Err(DiscoveryStop::Changed);
                    }
                    admitted.push((candidate, proof));
                }
            } else if outline_structure(&role) || role == "AXOutline" {
                if path.len() == MAX_DEPTH { return Err(DiscoveryStop::DepthLimit) }
                if !reciprocal_edge(tree, node, &child)? { return Err(DiscoveryStop::Changed) }
                let mut next = path.clone(); next.push(child); queue.push_back(next);
            }
        }
    }
    budget(tree)?;
    if admitted.is_empty() { return Ok(Vec::new()) }
    let fresh = tree.fresh_windows().ok_or(DiscoveryStop::Changed)?;
    let live_host = exact_window(&fresh, pid, host.window_id).ok_or(DiscoveryStop::Changed)?;
    if !same_identity(host, live_host) || !tree.same(root, &exact_root(tree, live_host)?) {
        return Err(DiscoveryStop::Changed);
    }
    let mut ids = Vec::new();
    for (path, proof) in admitted {
        let id = proof.menu.id;
        let before = exact_window(windows, pid, id).ok_or(DiscoveryStop::Changed)?;
        let after = exact_window(&fresh, pid, id).ok_or(DiscoveryStop::Changed)?;
        if !same_identity(before, after)
            || prove_outline_menu(tree, pid, live_host, &path, &fresh)? != Some(proof)
        {
            return Err(DiscoveryStop::Changed);
        }
        ids.push(id);
    }
    budget(tree)?;
    ids.sort_unstable(); ids.dedup();
    Ok(ids)
}

fn collect_after_legacy_empty<T: Tree>(
    tree: &T,
    pid: i32,
    host: &WindowInfo,
    root: &T::Node,
    windows: &[WindowInfo],
    visited: &mut Vec<T::Node>,
    seeds: &[Vec<T::Node>],
) -> Result<Vec<u32>, DiscoveryStop> {
    let ids = collect_focused_collection_popover(tree, pid, host, root, windows, visited)?;
    if !ids.is_empty() { return Ok(ids) }
    let result = collect_outline_menus(tree, pid, host, root, windows, visited, seeds);
    budget(tree)?;
    result
}

fn collect<T: Tree>(
    tree: &T,
    pid: i32,
    host_id: u32,
    windows: &[WindowInfo],
) -> Result<Vec<u32>, DiscoveryStop> {
    let host = exact_window(windows, pid, host_id).ok_or(DiscoveryStop::InvalidHost)?;
    let root = exact_root(tree, host)?;
    // Finish the original same-PID discovery and revalidation first. Merely
    // retaining skipped paths performs no extra AX reads. A nonempty original
    // result is returned unchanged; unrelated menu/provider work cannot lose it.
    let mut queue = VecDeque::from([(vec![root.clone()], false)]);
    let mut deferred = Vec::new();
    // Retain existing stop points without querying anything new. They are used
    // only after all established attachment routes have returned empty.
    let mut outline_seeds = Vec::new();
    let mut menu_phase = false;
    let mut provider_menu_phase = false;
    let mut visited: Vec<T::Node> = Vec::new();
    let mut admitted = Vec::new();
    loop {
        while let Some((path, resumed_seed)) = queue.pop_front() {
            budget(tree)?;
            if path.len() > MAX_DEPTH {
                return Err(DiscoveryStop::DepthLimit);
            }
            let node = path.last().expect("nonempty path");
            if path[..path.len() - 1].iter().any(|prior| tree.same(prior, node)) {
                return Err(DiscoveryStop::Cycle);
            }
            // A deferred seed was already charged to the original visited set.
            // All newly discovered nodes share its unchanged MAX_NODES ceiling.
            if !resumed_seed {
                if visited.iter().any(|prior| tree.same(prior, node)) {
                    continue;
                }
                if visited.len() >= MAX_NODES {
                    return Err(DiscoveryStop::NodeLimit);
                }
                visited.push(node.clone());
            }
            if tree.owner(node) != Some(pid) {
                if !menu_phase {
                    deferred.push((path, true));
                    continue;
                }
                if !provider_menu_phase {
                    continue;
                }
                if menu_path_members(tree, pid, &path, false)?.is_none() {
                    continue;
                }
            }
            let Some(role) = tree.role(node) else {
                continue;
            };
            if !menu_phase && matches!(role.as_str(), "AXOutline" | "AXLayoutArea") {
                outline_seeds.push(path.clone());
            }
            if role == "AXMenu" {
                if !menu_phase {
                    deferred.push((path, false));
                    continue;
                }
                if let Some(proof) = prove_menu_path(tree, pid, host, &path, windows)? {
                    if admitted.len() >= MAX_ATTACHMENTS {
                        return Err(DiscoveryStop::AttachmentLimit);
                    }
                    admitted.push((proof.id, path.clone(), Some(proof)));
                }
                // Only this directly anchored menu is proven; no submenu walk.
                continue;
            }
            if menu_phase {
                // Deferred work cannot widen the original popover/sheet route.
                if !container(&role) {
                    continue;
                }
            } else if matches!(role.as_str(), "AXPopover" | "AXSheet") {
                if let Some(id) = prove_path(tree, pid, host, &path, windows)? {
                    if admitted.len() >= MAX_ATTACHMENTS {
                        return Err(DiscoveryStop::AttachmentLimit);
                    }
                    admitted.push((id, path.clone(), None));
                }
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
            let pending = if menu_phase {
                queue.iter().filter(|entry| !entry.1).count()
            } else {
                queue.len()
            };
            if pending + visited.len() + children.len() > MAX_NODES {
                return Err(DiscoveryStop::NodeLimit);
            }
            for child in children {
                let mut next = path.clone();
                next.push(child);
                queue.push_back((next, false));
            }
        }
        budget(tree)?;
        let fresh = tree.fresh_windows().ok_or(DiscoveryStop::Changed)?;
        let live_host = exact_window(&fresh, pid, host_id).ok_or(DiscoveryStop::Changed)?;
        if !same_identity(host, live_host) || !tree.same(&root, &exact_root(tree, live_host)?) {
            return Err(DiscoveryStop::Changed);
        }
        let mut ids = Vec::new();
        for (id, path, menu) in admitted.drain(..) {
            budget(tree)?;
            let before = exact_window(windows, pid, id).ok_or(DiscoveryStop::Changed)?;
            let after = exact_window(&fresh, pid, id).ok_or(DiscoveryStop::Changed)?;
            if !same_identity(before, after) {
                return Err(DiscoveryStop::Changed);
            }
            let revalidated = if let Some(proof) = menu {
                prove_menu_path(tree, pid, live_host, &path, &fresh)? == Some(proof)
            } else {
                prove_path(tree, pid, live_host, &path, &fresh)? == Some(id)
            };
            if !revalidated {
                return Err(DiscoveryStop::Changed);
            }
            ids.push(id);
        }
        budget(tree)?;
        ids.sort_unstable();
        ids.dedup();
        if menu_phase || !ids.is_empty() || deferred.is_empty()
            || !windows.iter().any(|window| window.pid == pid && window.window_id != 0
                && window.window_id != host_id && matches!(window.layer, 0 | 101)
                && window.is_on_screen && window.on_current_space != Some(false))
        {
            return if ids.is_empty() {
                collect_after_legacy_empty(tree, pid, host, &root, windows, &mut visited, &outline_seeds)
            } else {
                Ok(ids)
            };
        }
        // Only an empty original result may use the remaining shared time and
        // node budget. Mixed popover/sheet+menu cases retain the original set.
        menu_phase = true;
        provider_menu_phase = windows.iter().any(|window| window.pid == pid
            && window.window_id != 0 && window.window_id != host_id && window.layer == 101
            && window.is_on_screen && window.on_current_space != Some(false));
        // Original discovery already identified foreign seeds. A layer-zero
        // menu cannot use them, so do not reread them or perform an empty extra
        // validation pass. Provider search remains available for layer101.
        queue = deferred.drain(..)
            .filter(|(_, foreign)| provider_menu_phase || !foreign)
            .map(|(path, _)| (path, true)).collect();
        if queue.is_empty() {
            return collect_after_legacy_empty(tree, pid, host, &root, windows, &mut visited, &outline_seeds);
        }
    }
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

fn menu_window_value_kind(status: AXError, has_value: bool, is_element: bool) -> Result<bool, DiscoveryStop> {
    match (status, has_value, is_element) {
        (kAXErrorSuccess, true, true) => Ok(true),
        (kAXErrorNoValue, false, _) => Ok(false),
        _ => Err(DiscoveryStop::AxUnavailable),
    }
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
    fn focused(&self) -> Option<Node> {
        self.relation(&self.app, "AXFocusedUIElement")
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
    fn menu_window(&self, node: &Node) -> Result<Option<Node>, DiscoveryStop> {
        if !self.ready(node) { return Err(DiscoveryStop::Deadline) }
        let attribute = CFString::new("AXWindow");
        let mut raw: CFTypeRef = std::ptr::null();
        let status = unsafe { AXUIElementCopyAttributeValue(node.0, attribute.as_concrete_TypeRef(), &mut raw) };
        let kind = menu_window_value_kind(status, !raw.is_null(), !raw.is_null()
            && unsafe { CFGetTypeID(raw) == AXUIElementGetTypeID() });
        if kind == Ok(true) {
            let retained = Node(raw as AXUIElementRef);
            budget(self)?;
            return Ok(Some(retained));
        }
        if !raw.is_null() { unsafe { CFRelease(raw) }; }
        budget(self)?;
        kind.map(|_| None)
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
    use std::cell::{Cell, RefCell};
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
        frames: HashMap<u32, [f64; 4]>,
        roots: Vec<u32>,
        windows: Vec<WindowInfo>,
        current: HashSet<u32>,
        proof: bool,
        proof_calls: Cell<usize>,
        expired: Cell<bool>,
        expire_on_proof: bool,
        detach_after_proof: bool,
        refreshed: Cell<bool>,
        refresh_count: Cell<usize>,
        change_on_refresh: usize,
        changed_node: Option<(u32, Fact)>,
        changed_frame: Option<(u32, [f64; 4])>,
        changed_windows: Option<Vec<WindowInfo>>,
        changed_roots: Option<Vec<u32>>,
        expire_after_refresh: bool,
        children_calls: RefCell<Vec<u32>>,
        children_errors: HashSet<u32>,
        expire_on_id: Option<u32>,
        focused: Option<u32>,
        focused_calls: Cell<usize>,
        expire_on_focus: bool,
        menu_window_calls: Cell<usize>,
        menu_window_errors: HashSet<u32>,
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
            frames: HashMap::new(),
            roots: vec![1],
            windows: vec![window(10), window(20)],
            current: HashSet::from([10, 20]),
            proof: true,
            proof_calls: Cell::new(0),
            expired: Cell::new(false),
            expire_on_proof: false,
            detach_after_proof: false,
            refreshed: Cell::new(false),
            refresh_count: Cell::new(0),
            change_on_refresh: 1,
            changed_node: None,
            changed_frame: None,
            changed_windows: None,
            changed_roots: None,
            expire_after_refresh: false,
            children_calls: RefCell::new(Vec::new()),
            children_errors: HashSet::new(),
            expire_on_id: None,
            focused: None,
            focused_calls: Cell::new(0),
            expire_on_focus: false,
            menu_window_calls: Cell::new(0),
            menu_window_errors: HashSet::new(),
        }
    }
    impl Fake {
        fn fact(&self, n: &u32) -> Option<&Fact> {
            if self.refresh_count.get() >= self.change_on_refresh {
                if let Some((id, fact)) = &self.changed_node {
                    if id == n {
                        return Some(fact);
                    }
                }
            }
            self.nodes.get(n)
        }
    }
    impl Tree for Fake {
        type Node = u32;
        fn roots(&self) -> Result<Vec<u32>, DiscoveryStop> {
            if self.refresh_count.get() >= self.change_on_refresh {
                if let Some(roots) = &self.changed_roots {
                    return Ok(roots.clone());
                }
            }
            Ok(self.roots.clone())
        }
        fn focused(&self) -> Option<u32> {
            self.focused_calls.set(self.focused_calls.get() + 1);
            if self.expire_on_focus {
                self.expired.set(true);
            }
            self.focused
        }
        fn role(&self, n: &u32) -> Option<String> {
            self.fact(n).map(|v| v.role.into())
        }
        fn owner(&self, n: &u32) -> Option<i32> {
            self.fact(n).map(|v| v.owner)
        }
        fn id(&self, n: &u32) -> Option<u32> {
            if self.expire_on_id == Some(*n) {
                self.expired.set(true);
            }
            self.fact(n).map(|v| v.id).filter(|id| *id != 0)
        }
        fn frame(&self, n: &u32) -> Option<[f64; 4]> {
            if self.refresh_count.get() >= self.change_on_refresh {
                if let Some((id, frame)) = self.changed_frame {
                    if id == *n {
                        return Some(frame);
                    }
                }
            }
            self.fact(n).map(|_| self.frames.get(n).copied().unwrap_or([100.0, 120.0, 400.0, 300.0]))
        }
        fn parent(&self, n: &u32) -> Option<u32> {
            if self.detach_after_proof && *n == 4 && self.proof_calls.get() > 0 {
                return None;
            }
            self.fact(n)?.parent
        }
        fn window(&self, n: &u32) -> Option<u32> {
            self.fact(n)?.window
        }
        fn menu_window(&self, n: &u32) -> Result<Option<u32>, DiscoveryStop> {
            self.menu_window_calls.set(self.menu_window_calls.get() + 1);
            if self.menu_window_errors.contains(n) { return Err(DiscoveryStop::AxUnavailable) }
            Ok(self.fact(n).ok_or(DiscoveryStop::AxUnavailable)?.window)
        }
        fn children(&self, n: &u32) -> Result<Vec<u32>, DiscoveryStop> {
            self.children_calls.borrow_mut().push(*n);
            if self.children_errors.contains(n) {
                return Err(DiscoveryStop::AxUnavailable);
            }
            Ok(self.fact(n).expect("known fake node").children.clone())
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
            self.refreshed.set(true);
            self.refresh_count.set(self.refresh_count.get() + 1);
            if self.expire_after_refresh && self.refresh_count.get() >= self.change_on_refresh {
                self.expired.set(true);
            }
            if self.refresh_count.get() >= self.change_on_refresh {
                if let Some(windows) = &self.changed_windows {
                    return Some(windows.clone());
                }
            }
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

    fn native_menu() -> Fake {
        let mut t = popover();
        let provider = t.nodes.get_mut(&2).unwrap();
        provider.role = "AXSplitGroup";
        provider.owner = 77;
        provider.id = 999; // Provider SPI ID has no current CG surface.
        provider.window = None;
        let popup = t.nodes.get_mut(&3).unwrap();
        popup.role = "AXPopUpButton";
        popup.id = 0;
        popup.window = None;
        let menu = t.nodes.get_mut(&4).unwrap();
        menu.role = "AXMenu";
        menu.id = 0; // The real menu and opener both return a SPI read error.
        menu.window = None;
        t.windows[1].layer = 101;
        t.windows[1].bounds.x = 415.0;
        t.windows[1].bounds.y = 294.0;
        t.windows[1].bounds.width = 150.0;
        t.windows[1].bounds.height = 232.0;
        t.frames.insert(4, [415.0, 294.0, 150.0, 232.0]);
        t.change_on_refresh = 2; // Empty original pass, then menu revalidation.
        t
    }

    #[test]
    fn native_menu_without_spi_or_window_attribute_has_a_reciprocal_host_proof() {
        let t = native_menu();
        assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![20]));
        assert_eq!(t.proof_calls.get(), 0, "menu proof cannot use the popover shortcut");
        assert!(t.refreshed.get());
        assert_eq!(t.refresh_count.get(), 2);
        let mut same_pid = native_menu();
        same_pid.nodes.get_mut(&2).unwrap().owner = 42;
        assert_eq!(collect(&same_pid, 42, 10, &same_pid.windows), Ok(vec![20]));
    }

    #[test]
    fn menu_frame_needs_one_current_exact_same_pid_popup_surface() {
        for case in 0..10 {
            let mut t = native_menu();
            match case {
                0 => t.windows[1].pid = 99,
                1 => t.windows[1].layer = 3,
                2 => t.windows[1].is_on_screen = false,
                3 => t.windows[1].on_current_space = Some(false),
                4 => { t.current.remove(&20); }
                5 => t.windows[1].bounds.width += 2.0,
                6 => {
                    let mut duplicate = t.windows[1].clone();
                    duplicate.window_id = 30;
                    t.windows.push(duplicate);
                }
                7 => t.windows.push(t.windows[1].clone()),
                8 => { t.frames.insert(4, [415.0, 294.0, f64::NAN, 232.0]); }
                _ => { t.frames.insert(4, [415.0, 294.0, 150.0, 0.0]); }
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]), "case {case}");
        }
    }

    #[test]
    fn menu_does_not_inherit_remote_sibling_or_one_way_ancestry() {
        for case in 0..10 {
            let mut t = native_menu();
            match case {
                0 => t.nodes.get_mut(&4).unwrap().owner = 99,
                1 => t.nodes.get_mut(&3).unwrap().owner = 88, // second provider
                2 => t.nodes.get_mut(&2).unwrap().role = "AXTable",
                3 => t.nodes.get_mut(&2).unwrap().role = "AXWebArea",
                4 => t.nodes.get_mut(&2).unwrap().role = "AXWindow",
                5 => t.nodes.get_mut(&2).unwrap().role = "AXSheet",
                6 => t.nodes.get_mut(&3).unwrap().role = "AXButton",
                7 => t.nodes.get_mut(&2).unwrap().parent = None,
                8 => t.nodes.get_mut(&3).unwrap().children.push(4),
                _ => {
                    t.nodes.get_mut(&4).unwrap().window = Some(1);
                    t.nodes.get_mut(&4).unwrap().parent = Some(1);
                }
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]), "case {case}");
        }
    }

    #[test]
    fn menu_rereads_provider_edges_roles_ax_frame_and_cg_identity() {
        for case in 0..6 {
            let mut t = native_menu();
            let initial = t.windows.clone();
            match case {
                0 => {
                    let mut changed = t.nodes[&2].clone();
                    changed.owner = 88; // Still a valid one-provider shape, but a changed identity.
                    t.changed_node = Some((2, changed));
                }
                1 => {
                    let mut changed = t.nodes[&3].clone();
                    changed.parent = None;
                    t.changed_node = Some((3, changed));
                }
                2 => {
                    let mut changed = t.nodes[&2].clone();
                    changed.role = "AXGroup";
                    t.changed_node = Some((2, changed));
                }
                3 => {
                    let mut changed = t.nodes[&3].clone();
                    changed.children.clear();
                    t.changed_node = Some((3, changed));
                }
                4 => t.changed_frame = Some((4, [415.25, 294.0, 150.0, 232.0])),
                _ => t.windows[1].bounds.x += 0.25,
            }
            assert_eq!(collect(&t, 42, 10, &initial), Err(DiscoveryStop::Changed), "case {case}");
        }
    }

    #[test]
    fn menu_search_keeps_structural_and_shared_deadline_bounds() {
        let mut t = native_menu();
        t.expire_after_refresh = true;
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::Deadline));
        let mut t = native_menu();
        t.nodes.get_mut(&2).unwrap().children = vec![3; MAX_CHILDREN + 1];
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::ChildLimit));
        let mut t = native_menu();
        t.nodes.get_mut(&3).unwrap().children.push(2);
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::Cycle));
    }

    #[test]
    fn visible_menu_never_relaxes_foreign_popover_or_sheet_admission() {
        for role in ["AXPopover", "AXSheet"] {
            let mut t = native_menu();
            let leaf = t.nodes.get_mut(&4).unwrap();
            leaf.role = role;
            leaf.id = 20;
            leaf.window = Some(1);
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]));
            assert_eq!(t.proof_calls.get(), 0);
        }
    }

    fn with_deferred_provider(mut t: Fake) -> Fake {
        t.nodes.get_mut(&1).unwrap().children.push(5);
        t.nodes.insert(5, Fact {
            role: "AXGroup", owner: 77, id: 999, parent: Some(1), window: None,
            children: vec![6; MAX_CHILDREN + 1],
        });
        let mut unrelated = window(30);
        unrelated.layer = 101;
        t.windows.push(unrelated);
        t
    }

    #[test]
    fn old_popover_and_sheet_survive_unrelated_menu_and_bad_remote_branch() {
        for sheet in [false, true] {
            for read_error in [false, true] {
                let mut t = popover();
                if sheet {
                    t.nodes.get_mut(&1).unwrap().children = vec![4];
                    let leaf = t.nodes.get_mut(&4).unwrap();
                    leaf.role = "AXSheet";
                    leaf.parent = Some(1);
                }
                let mut t = with_deferred_provider(t);
                if read_error {
                    t.children_errors.insert(5);
                }
                assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![20]));
                assert_eq!(t.refresh_count.get(), 1);
                assert!(!t.children_calls.borrow().contains(&5), "new remote work must never run");
            }
        }
    }

    #[test]
    fn old_revalidation_failure_does_not_start_deferred_menu_work() {
        let mut t = with_deferred_provider(popover());
        t.detach_after_proof = true;
        t.children_errors.insert(5);
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::Changed));
        assert_eq!(t.refresh_count.get(), 1);
        assert!(!t.children_calls.borrow().contains(&5));
    }

    #[test]
    fn menu_continuation_cannot_reset_nodes_used_by_original_discovery() {
        let mut t = native_menu();
        // root + deferred provider +126 ordinary leaves exhaust the same128
        // visited nodes. The provider's first new child must not get a new cap.
        for id in 100..226 {
            t.nodes.insert(id, Fact {
                role: "AXStaticText", owner: 42, id: 10, parent: Some(1),
                window: Some(1), children: vec![],
            });
            t.nodes.get_mut(&1).unwrap().children.push(id);
        }
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::NodeLimit));
        assert_eq!(t.refresh_count.get(), 1);
    }

    #[test]
    fn mixed_valid_popover_and_menu_keeps_the_original_attachment_set() {
        let mut t = with_deferred_provider(popover());
        t.nodes.get_mut(&5).unwrap().children = vec![6];
        t.nodes.insert(6, Fact {
            role: "AXPopUpButton", owner: 42, id: 0, parent: Some(5),
            window: None, children: vec![7],
        });
        t.nodes.insert(7, Fact {
            role: "AXMenu", owner: 42, id: 0, parent: Some(6),
            window: None, children: vec![],
        });
        t.current.insert(30);
        assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![20]));
        assert!(!t.children_calls.borrow().contains(&5));
        assert_eq!(t.refresh_count.get(), 1);
    }

    fn layer_zero_menu() -> Fake {
        let mut t = native_menu();
        for id in [2, 3, 4] {
            let node = t.nodes.get_mut(&id).unwrap();
            node.owner = 42;
            node.id = 10;
            node.window = Some(1);
        }
        t.nodes.get_mut(&2).unwrap().role = "AXGroup";
        // Match the retained Calc topology: root, five groups, opener, menu.
        let mut parent = 2;
        for id in 5..9 {
            t.nodes.get_mut(&parent).unwrap().children = vec![id];
            t.nodes.insert(id, Fact {
                role: "AXGroup", owner: 42, id: 10, parent: Some(parent),
                window: Some(1), children: vec![3],
            });
            parent = id;
        }
        t.nodes.get_mut(&3).unwrap().parent = Some(parent);
        t.windows[0].bounds = crate::windows::WindowBounds {
            x: 562.0, y: 276.0, width: 602.0, height: 511.0,
        };
        t.frames.insert(1, [562.0, 276.0, 602.0, 511.0]);
        t.windows[1].layer = 0;
        t.windows[1].bounds = crate::windows::WindowBounds {
            x: 818.0, y: 378.0, width: 217.0, height: 104.0,
        };
        t.frames.insert(4, [818.0, 378.0, 217.0, 104.0]);
        t
    }

    #[test]
    fn layer_zero_only_menu_uses_exact_inherited_host_path_and_revalidation() {
        let t = layer_zero_menu();
        assert!(t.windows.iter().all(|window| window.layer == 0));
        assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![20]));
        assert_eq!(t.refresh_count.get(), 2, "original and menu proofs both settle");
        assert_eq!(t.proof_calls.get(), 0, "no popover authority shortcut");
    }

    #[test]
    fn layer_zero_menu_needs_same_pid_host_ids_and_host_window_attributes() {
        for case in 0..8 {
            let mut t = layer_zero_menu();
            match case {
                0 => t.nodes.get_mut(&5).unwrap().owner = 77,
                1 => t.nodes.get_mut(&4).unwrap().id = 0,
                2 => t.nodes.get_mut(&3).unwrap().id = 20,
                3 => t.nodes.get_mut(&5).unwrap().id = 999,
                4 => t.nodes.get_mut(&4).unwrap().window = None,
                5 => t.nodes.get_mut(&3).unwrap().window = Some(2),
                6 => t.nodes.get_mut(&5).unwrap().window = Some(2),
                _ => t.nodes.get_mut(&5).unwrap().role = "AXWindow",
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]), "case {case}");
        }
        let mut provider = native_menu();
        provider.windows[1].layer = 0;
        assert_eq!(collect(&provider, 42, 10, &provider.windows), Ok(vec![]));
    }

    #[test]
    fn layer_zero_menu_rejects_one_way_edges_navigation_and_non_native_paths() {
        for case in 0..7 {
            let mut t = layer_zero_menu();
            match case {
                0 => t.nodes.get_mut(&4).unwrap().parent = Some(1),
                1 => t.nodes.get_mut(&3).unwrap().children.push(4),
                2 => t.nodes.get_mut(&3).unwrap().role = "AXGroup",
                3 => t.nodes.get_mut(&5).unwrap().role = "AXWebArea",
                4 => t.nodes.get_mut(&5).unwrap().role = "AXTable",
                5 => t.nodes.get_mut(&5).unwrap().role = "AXApplication",
                _ => {
                    t.nodes.get_mut(&1).unwrap().children = vec![4];
                    t.nodes.get_mut(&4).unwrap().parent = Some(1);
                }
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]), "case {case}");
        }
    }

    #[test]
    fn layer_zero_menu_requires_one_visible_current_exact_physical_match() {
        for case in 0..9 {
            let mut t = layer_zero_menu();
            match case {
                0 => t.windows[1].pid = 99,
                1 => t.windows[1].is_on_screen = false,
                2 => t.windows[1].on_current_space = Some(false),
                3 => { t.current.remove(&20); }
                4 => t.windows[1].bounds.x += 1.0,
                5 => t.windows[1].window_id = 10,
                6 => t.windows.push(t.windows[1].clone()),
                _ => {
                    let mut duplicate = t.windows[1].clone();
                    duplicate.window_id = 30;
                    duplicate.layer = if case == 7 { 0 } else { 101 };
                    t.windows.push(duplicate);
                }
            }
            let expected = if case == 5 { Err(DiscoveryStop::InvalidHost) } else { Ok(vec![]) };
            assert_eq!(collect(&t, 42, 10, &t.windows), expected, "case {case}");
        }
    }

    #[test]
    fn layer_zero_menu_rechecks_new_identity_proofs_and_never_returns_partial_ids() {
        for case in 0..6 {
            let mut t = layer_zero_menu();
            let initial = t.windows.clone();
            let mut changed = t.nodes[&5].clone();
            match case {
                0 => { changed.id = 999; t.changed_node = Some((5, changed)); }
                1 => { changed.window = Some(2); t.changed_node = Some((5, changed)); }
                2 => { changed.owner = 77; t.changed_node = Some((5, changed)); }
                3 => { changed.parent = None; t.changed_node = Some((5, changed)); }
                4 => t.changed_frame = Some((4, [818.25, 378.0, 217.0, 104.0])),
                _ => t.windows[1].layer = 101,
            }
            assert_eq!(collect(&t, 42, 10, &initial), Err(DiscoveryStop::Changed), "case {case}");
        }
    }

    #[test]
    fn layer_zero_additional_reads_keep_shared_deadline_and_node_limits() {
        let mut t = layer_zero_menu();
        t.expire_on_id = Some(4);
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::Deadline));
        let mut t = layer_zero_menu();
        t.expire_after_refresh = true;
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::Deadline));
        let mut t = layer_zero_menu();
        for id in 100..221 {
            t.nodes.insert(id, Fact {
                role: "AXStaticText", owner: 42, id: 10, parent: Some(1),
                window: Some(1), children: vec![],
            });
            t.nodes.get_mut(&1).unwrap().children.push(id);
        }
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::NodeLimit));
    }

    #[test]
    fn layer_zero_candidates_do_not_change_existing_nonempty_or_failed_discovery() {
        for sheet in [false, true] {
            for fails in [false, true] {
                let mut t = popover();
                if sheet {
                    t.nodes.get_mut(&1).unwrap().children = vec![4];
                    let node = t.nodes.get_mut(&4).unwrap();
                    node.role = "AXSheet";
                    node.parent = Some(1);
                }
                let mut t = with_deferred_provider(t);
                t.windows[2].layer = 0;
                t.children_errors.insert(5);
                t.detach_after_proof = fails && !sheet;
                if fails && sheet {
                    let mut changed = t.nodes[&4].clone();
                    changed.parent = Some(2);
                    t.changed_node = Some((4, changed));
                }
                let expected = if fails { Err(DiscoveryStop::Changed) } else { Ok(vec![20]) };
                assert_eq!(collect(&t, 42, 10, &t.windows), expected);
                assert_eq!(t.refresh_count.get(), 1);
                assert!(!t.children_calls.borrow().contains(&5));
            }
        }
    }

    #[test]
    fn layer_zero_addition_retains_existing_provider_layer101_proof() {
        let mut t = native_menu();
        let mut ordinary = t.windows[1].clone();
        ordinary.window_id = 30;
        ordinary.layer = 0;
        t.windows.push(ordinary);
        assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![20]));
    }

    #[test]
    fn layer_zero_only_never_reads_ineligible_deferred_provider() {
        for read_error in [false, true] {
            let mut t = native_menu();
            t.windows[1].layer = 0;
            if read_error {
                t.children_errors.insert(2);
            } else {
                t.nodes.get_mut(&2).unwrap().children = vec![3; MAX_CHILDREN + 1];
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]));
            assert_eq!(t.refresh_count.get(), 1, "no extra empty validation pass");
            assert!(!t.children_calls.borrow().contains(&2), "provider is ineligible for layer0");
        }
        // The old layer101 route still performs its provider search and keeps
        // its original read-error behavior rather than swallowing the error.
        let mut t = native_menu();
        t.children_errors.insert(2);
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::AxUnavailable));
        assert!(t.children_calls.borrow().contains(&2));
    }

    fn collection_popover() -> Fake {
        let mut t = popover();
        // Native path: host -> split -> layout -> scroll -> outline -> row ->
        // cell -> group -> popover. The old collector stops at layout.
        let chain = [
            (2, "AXSplitGroup"),
            (5, "AXLayoutArea"),
            (6, "AXScrollArea"),
            (7, "AXOutline"),
            (8, "AXRow"),
            (9, "AXCell"),
            (3, "AXGroup"),
        ];
        for (index, &(id, role)) in chain.iter().enumerate() {
            t.nodes.insert(
                id,
                Fact {
                    role,
                    owner: 42,
                    id: 10,
                    parent: Some(if index == 0 { 1 } else { chain[index - 1].0 }),
                    window: Some(1),
                    children: vec![chain.get(index + 1).map_or(4, |item| item.0)],
                },
            );
        }
        t.focused = Some(4);
        t
    }

    #[test]
    fn collection_popover_uses_focused_hint_but_reproves_retained_host_path() {
        for descendant in [false, true] {
            let mut t = collection_popover();
            if descendant {
                t.nodes.insert(
                    30,
                    Fact {
                        role: "AXCheckBox",
                        owner: 42,
                        id: 20,
                        parent: Some(4),
                        window: Some(1),
                        children: vec![],
                    },
                );
                t.nodes.get_mut(&4).unwrap().children = vec![30];
                t.focused = Some(30);
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![20]));
            assert_eq!(t.focused_calls.get(), 1);
            assert_eq!(t.proof_calls.get(), 2);
            assert_eq!(
                t.refresh_count.get(),
                2,
                "legacy empty then new positive revalidation"
            );
        }
    }

    #[test]
    fn collection_popover_hint_never_supplies_authority_or_widens_legacy_roles() {
        for case in 0..8 {
            let mut t = collection_popover();
            match case {
                0 => t.focused = None,
                1 => t.focused = Some(9), // A focused cell is not a popover.
                2 => t.proof = false,
                3 => t.nodes.get_mut(&5).unwrap().role = "AXWebArea",
                4 => t.nodes.get_mut(&5).unwrap().role = "AXTable",
                5 => t.nodes.get_mut(&5).unwrap().role = "AXApplication",
                6 => t.nodes.get_mut(&5).unwrap().role = "AXSheet",
                _ => t.nodes.get_mut(&5).unwrap().role = "AXWindow",
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]), "case {case}");
        }
        for role in ["AXCell", "AXRow", "AXOutline", "AXLayoutArea"] {
            assert!(
                !container(role),
                "menu/provider traversal must stay unchanged"
            );
        }
    }

    #[test]
    fn collection_popover_host_nodes_require_exact_owner_physical_and_logical_host() {
        for id in [2, 5, 6, 7, 8, 9, 3] {
            for case in 0..5 {
                let mut t = collection_popover();
                let node = t.nodes.get_mut(&id).unwrap();
                match case {
                    0 => node.owner = 77,
                    1 => node.id = 20,
                    2 => node.id = 0,
                    3 => node.window = Some(2), // Same physical ID is not CF identity.
                    _ => node.window = None,
                }
                assert_eq!(
                    collect(&t, 42, 10, &t.windows),
                    Ok(vec![]),
                    "node {id} case {case}"
                );
            }
        }
    }

    #[test]
    fn collection_popover_rejects_one_way_nested_and_replaced_host_paths() {
        for case in 0..6 {
            let mut t = collection_popover();
            match case {
                0 => t.nodes.get_mut(&9).unwrap().children.clear(),
                1 => t.nodes.get_mut(&9).unwrap().children.push(3),
                2 => t.nodes.get_mut(&5).unwrap().parent = Some(1),
                3 => t.nodes.get_mut(&8).unwrap().role = "AXPopover",
                4 => {
                    // Another retained AXWindow object with the same CG ID.
                    let mut alias = t.nodes[&1].clone();
                    alias.children = vec![2];
                    t.nodes.insert(31, alias);
                    t.nodes.get_mut(&2).unwrap().parent = Some(31);
                }
                _ => t.nodes.get_mut(&4).unwrap().window = Some(2),
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]), "case {case}");
        }
    }

    #[test]
    fn collection_popover_requires_live_unique_physical_surface_and_current_space() {
        for case in 0..7 {
            let mut t = collection_popover();
            match case {
                0 => t.windows[1].pid = 77,
                1 => t.windows[1].is_on_screen = false,
                2 => t.windows[1].on_current_space = Some(false),
                3 => {
                    t.current.remove(&20);
                }
                4 => t.windows.push(window(20)),
                5 => {
                    t.frames.insert(4, [101.0, 120.0, 400.0, 300.0]);
                }
                _ => t.nodes.get_mut(&4).unwrap().id = 10,
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]), "case {case}");
        }
    }

    #[test]
    fn collection_popover_changes_after_positive_proof_discard_entire_result() {
        for case in 0..7 {
            let mut t = collection_popover();
            // The first snapshot belongs to the unchanged legacy empty route.
            t.change_on_refresh = 2;
            let mut changed = t.nodes[&9].clone();
            match case {
                0 => changed.parent = None,
                1 => changed.children.clear(),
                2 => changed.id = 999,
                3 => changed.window = Some(2),
                4 => changed.owner = 77,
                5 => changed.role = "AXWebArea",
                _ => t.changed_frame = Some((4, [101.0, 120.0, 400.0, 300.0])),
            }
            t.changed_node = Some((9, changed));
            assert_eq!(
                collect(&t, 42, 10, &t.windows),
                Err(DiscoveryStop::Changed),
                "case {case}"
            );
        }
    }

    #[test]
    fn collection_popover_read_errors_and_shared_time_budget_remain_fail_closed() {
        for case in 0..5 {
            let mut t = collection_popover();
            let expected = match case {
                0 => {
                    t.children_errors.insert(9);
                    DiscoveryStop::AxUnavailable
                }
                1 => {
                    t.nodes.get_mut(&9).unwrap().children = vec![3; MAX_CHILDREN + 1];
                    DiscoveryStop::ChildLimit
                }
                2 => {
                    t.expire_on_focus = true;
                    DiscoveryStop::Deadline
                }
                3 => {
                    t.expire_on_proof = true;
                    DiscoveryStop::Deadline
                }
                _ => {
                    t.expire_after_refresh = true;
                    t.change_on_refresh = 2;
                    DiscoveryStop::Deadline
                }
            };
            assert_eq!(
                collect(&t, 42, 10, &t.windows),
                Err(expected),
                "case {case}"
            );
        }
    }

    #[test]
    fn collection_popover_uses_legacy_node_charge_and_bounds_focused_walk() {
        let mut t = collection_popover();
        // Original discovery uses 123 nodes, then the focused path must consume
        // the same budget, not start another 128-node allowance.
        for id in 100..220 {
            t.nodes.insert(
                id,
                Fact {
                    role: "AXStaticText",
                    owner: 42,
                    id: 10,
                    parent: Some(1),
                    window: Some(1),
                    children: vec![],
                },
            );
            t.nodes.get_mut(&1).unwrap().children.push(id);
        }
        assert_eq!(
            collect(&t, 42, 10, &t.windows),
            Err(DiscoveryStop::NodeLimit)
        );
        assert_eq!(t.focused_calls.get(), 1);
        let mut t = collection_popover();
        t.nodes.get_mut(&5).unwrap().parent = Some(9);
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::Cycle));
        let mut t = collection_popover();
        for id in 30..35 {
            t.nodes.insert(
                id,
                Fact {
                    role: "AXGroup",
                    owner: 42,
                    id: 20,
                    parent: Some(if id == 34 { 4 } else { id + 1 }),
                    window: Some(1),
                    children: if id == 30 { vec![] } else { vec![id - 1] },
                },
            );
        }
        t.nodes.get_mut(&4).unwrap().children = vec![34];
        t.focused = Some(30);
        assert_eq!(
            collect(&t, 42, 10, &t.windows),
            Err(DiscoveryStop::DepthLimit)
        );
    }

    #[test]
    fn collection_hint_is_not_read_for_legacy_success_or_error() {
        for kind in 0..4 {
            let mut t = match kind {
                0 => popover(),
                1 => native_menu(),
                2 => layer_zero_menu(),
                _ => {
                    let mut t = popover();
                    t.nodes.get_mut(&1).unwrap().children = vec![4];
                    t.nodes.get_mut(&4).unwrap().role = "AXSheet";
                    t.nodes.get_mut(&4).unwrap().parent = Some(1);
                    t
                }
            };
            t.focused = Some(999); // Invalid and expiring if queried.
            t.expire_on_focus = true;
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![20]));
            assert_eq!(t.focused_calls.get(), 0, "kind {kind}");
        }
        let mut t = collection_popover();
        t.children_errors.insert(1);
        assert_eq!(
            collect(&t, 42, 10, &t.windows),
            Err(DiscoveryStop::AxUnavailable)
        );
        assert_eq!(t.focused_calls.get(), 0);
    }
    #[test]
    fn collection_popover_revalidates_cg_identity_and_retained_root_after_new_proof() {
        for index in [0, 1] {
            for case in 0..8 {
                let mut t = collection_popover();
                t.change_on_refresh = 2;
                let mut windows = t.windows.clone();
                let window = &mut windows[index];
                match case {
                    0 => window.window_id += 1,
                    1 => window.pid = 77,
                    2 => window.layer += 1,
                    3 => window.bounds.x += 1.0,
                    4 => window.bounds.width += 1.0,
                    5 => window.is_on_screen = false,
                    6 => window.on_current_space = Some(false),
                    _ => windows.push(windows[index].clone()),
                }
                t.changed_windows = Some(windows);
                assert_eq!(
                    collect(&t, 42, 10, &t.windows),
                    Err(DiscoveryStop::Changed),
                    "surface {index} case {case}"
                );
            }
        }
        let mut t = collection_popover();
        t.nodes.insert(31, t.nodes[&1].clone());
        t.change_on_refresh = 2;
        t.changed_roots = Some(vec![31]);
        assert_eq!(
            collect(&t, 42, 10, &t.windows),
            Err(DiscoveryStop::Changed),
            "same CG identity cannot replace the retained AX root"
        );
    }

    #[test]
    fn collection_popover_descendant_hint_keeps_original_reciprocal_role_boundary() {
        for case in 0..4 {
            let mut t = collection_popover();
            t.nodes.insert(
                30,
                Fact {
                    role: "AXCheckBox",
                    owner: 42,
                    id: 20,
                    parent: Some(4),
                    window: Some(1),
                    children: vec![],
                },
            );
            t.nodes.get_mut(&4).unwrap().children = vec![30];
            t.focused = Some(30);
            match case {
                0 => t.nodes.get_mut(&30).unwrap().role = "AXCell",
                1 => t.nodes.get_mut(&30).unwrap().owner = 77,
                2 => t.nodes.get_mut(&4).unwrap().children.clear(),
                _ => t.nodes.get_mut(&4).unwrap().children.push(30),
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]), "case {case}");
            assert_eq!(t.proof_calls.get(), 0);
        }
    }

    fn outline_menu() -> Fake {
        let mut t = popover();
        t.nodes.remove(&3);
        for (id, role, parent, children) in [
            (2, "AXSplitGroup", 1, vec![5, 6]),
            (5, "AXScrollArea", 2, vec![7]),
            (7, "AXOutline", 5, vec![8, 4]),
            (8, "AXRow", 7, vec![]),
            (6, "AXLayoutArea", 2, vec![9]),
            (9, "AXScrollArea", 6, vec![11]),
            (11, "AXOutline", 9, vec![]),
        ] {
            t.nodes.insert(id, Fact { role, owner: 42, id: 10,
                parent: Some(parent), window: Some(1), children });
        }
        t.nodes.insert(4, Fact { role: "AXMenu", owner: 42, id: 10,
            parent: Some(7), window: None, children: vec![] });
        t.frames.insert(4, [130.0, 140.0, 90.0, 80.0]);
        let menu = &mut t.windows[1];
        menu.layer = 101;
        menu.bounds.x = 130.0; menu.bounds.y = 140.0;
        menu.bounds.width = 90.0; menu.bounds.height = 80.0;
        // Actual focus may remain in the other content Outline. It is no
        // authority for selecting the sidebar menu.
        t.focused = Some(11);
        t
    }

    #[test]
    fn outline_menu_is_reachable_with_content_outline_focused_and_absent_leaf_window() {
        for logical in [None, Some(1)] {
            let mut t = outline_menu();
            t.nodes.get_mut(&4).unwrap().window = logical;
            t.children_errors.extend([8, 4]); // No row or menu-item traversal.
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![20]));
            assert_eq!(t.menu_window_calls.get(), 2, "fresh leaf relationship each proof");
            assert_eq!(t.refresh_count.get(), 2);
            assert!(!t.children_calls.borrow().iter().any(|node| [8, 4].contains(node)));
        }
        assert!(!container("AXOutline"));
        assert!(!container("AXLayoutArea"));
    }

    #[test]
    fn outline_menu_leaf_absence_never_swallows_ax_errors_or_malformed_values() {
        assert_eq!(menu_window_value_kind(kAXErrorNoValue, false, false), Ok(false));
        assert_eq!(menu_window_value_kind(kAXErrorSuccess, true, true), Ok(true));
        for (status, has_value, is_element) in [
            (kAXErrorSuccess, false, false), (kAXErrorSuccess, true, false),
            (kAXErrorNoValue, true, true), (kAXErrorAttributeUnsupported, false, false),
            (-25204, false, false),
        ] {
            assert_eq!(menu_window_value_kind(status, has_value, is_element), Err(DiscoveryStop::AxUnavailable));
        }
        let mut t = outline_menu(); t.menu_window_errors.insert(4);
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::AxUnavailable));
    }

    #[test]
    fn outline_menu_requires_every_host_identity_and_reciprocal_edge() {
        for node in [2, 5, 7, 4] {
            for case in 0..5 {
                let mut t = outline_menu(); let fact = t.nodes.get_mut(&node).unwrap();
                match case {
                    0 => fact.owner = 77,
                    1 => fact.id = 20,
                    2 => fact.id = 0,
                    3 => fact.window = Some(5), // A same-PID node is not the retained root.
                    _ => fact.parent = Some(1),
                }
                // Node2 is already a direct host child; use a genuinely changed edge.
                if case == 4 && node == 2 { t.nodes.get_mut(&node).unwrap().parent = Some(7); }
                assert!(!matches!(collect(&t, 42, 10, &t.windows), Ok(ids) if !ids.is_empty()), "node {node} case {case}");
            }
        }
        for role in ["AXCell", "AXRow", "AXWebArea", "AXTable", "AXButton", "AXSheet", "AXWindow"] {
            let mut t = outline_menu(); t.nodes.get_mut(&5).unwrap().role = role;
            assert!(!matches!(collect(&t, 42, 10, &t.windows), Ok(ids) if !ids.is_empty()), "role {role}");
        }
        let mut t = outline_menu(); t.nodes.get_mut(&7).unwrap().children.push(4);
        assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]));
    }

    #[test]
    fn outline_menu_requires_unique_visible_current_space_layer101_geometry() {
        for case in 0..8 {
            let mut t = outline_menu();
            match case {
                0 => t.windows[1].layer = 0,
                1 => t.windows[1].pid = 77,
                2 => t.windows[1].is_on_screen = false,
                3 => t.windows[1].on_current_space = Some(false),
                4 => { t.current.remove(&20); }
                5 => t.windows[1].bounds.width += 1.0,
                6 => { let mut duplicate = t.windows[1].clone(); duplicate.window_id = 30; t.windows.push(duplicate); }
                _ => { let mut duplicate = t.windows[1].clone(); duplicate.window_id = 30; duplicate.layer = 0; t.windows.push(duplicate); }
            }
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![]), "case {case}");
        }
        let mut t = outline_menu(); let mut duplicate = t.nodes[&4].clone();
        duplicate.parent = Some(7); t.nodes.insert(30, duplicate);
        t.frames.insert(30, t.frames[&4]); t.nodes.get_mut(&7).unwrap().children.push(30);
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::Changed));
    }

    #[test]
    fn outline_menu_shares_node_child_depth_and_deadline_limits() {
        let t = outline_menu(); let mut visited = (100..100 + MAX_NODES as u32).collect();
        assert_eq!(collect_outline_menus(&t, 42, &t.windows[0], &1, &t.windows,
            &mut visited, &[vec![1, 2, 5, 7]]), Err(DiscoveryStop::NodeLimit));
        assert_eq!(collect_outline_menus(&t, 42, &t.windows[0], &1, &t.windows,
            &mut vec![1, 2], &[vec![1, 2, 2]]), Err(DiscoveryStop::Cycle));
        let mut t = outline_menu(); t.nodes.get_mut(&7).unwrap().children = vec![4; MAX_CHILDREN + 1];
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::ChildLimit));
        let mut t = outline_menu(); t.expire_on_id = Some(7);
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::Deadline));
        let mut t = outline_menu(); t.nodes.get_mut(&6).unwrap().children = vec![100];
        for n in 100..112 {
            t.nodes.insert(n, Fact { role: "AXGroup", owner: 42, id: 10,
                parent: Some(if n == 100 { 6 } else { n - 1 }), window: Some(1),
                children: if n == 111 { vec![] } else { vec![n + 1] } });
        }
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::DepthLimit));
    }

    #[test]
    fn outline_menu_discards_proven_ids_on_incomplete_other_structural_branch() {
        // The original BFS retains Layout6 before Outline7. Reorder the retained
        // seeds explicitly so this checks failure AFTER a menu was proven.
        for read_error in [false, true] {
            let mut t = outline_menu();
            let expected = if read_error {
                t.children_errors.insert(6);
                Err(DiscoveryStop::AxUnavailable)
            } else {
                t.nodes.get_mut(&6).unwrap().window = Some(2);
                Ok(vec![])
            };
            assert_eq!(collect_outline_menus(&t, 42, &t.windows[0], &1, &t.windows,
                &mut vec![1, 2, 5, 7, 6], &[vec![1, 2, 5, 7], vec![1, 2, 6]]), expected);
            assert_eq!(t.menu_window_calls.get(), 1);
        }
    }

    #[test]
    fn outline_menu_revalidates_leaf_edges_role_root_and_cg_after_discovery() {
        for case in 0..8 {
            let mut t = outline_menu(); t.change_on_refresh = 2;
            match case {
                0 => { let mut leaf = t.nodes[&4].clone(); leaf.parent = Some(1); t.changed_node = Some((4, leaf)); }
                1 => { let mut leaf = t.nodes[&4].clone(); leaf.window = Some(1); t.changed_node = Some((4, leaf)); }
                2 => { let mut anchor = t.nodes[&7].clone(); anchor.children.clear(); t.changed_node = Some((7, anchor)); }
                3 => { let mut prefix = t.nodes[&5].clone(); prefix.role = "AXGroup"; t.changed_node = Some((5, prefix)); }
                4 => t.changed_frame = Some((4, [130.0, 140.0, 91.0, 80.0])),
                5 => { let mut windows = t.windows.clone(); windows[1].bounds.x += 1.0; t.changed_windows = Some(windows); }
                6 => { t.nodes.insert(31, t.nodes[&1].clone()); t.changed_roots = Some(vec![31]); }
                _ => t.expire_after_refresh = true,
            }
            let result = collect(&t, 42, 10, &t.windows);
            assert_eq!(result, Err(if case == 7 { DiscoveryStop::Deadline } else { DiscoveryStop::Changed }), "case {case}");
        }
    }

    #[test]
    fn outline_fallback_adds_no_queries_after_existing_success_or_error() {
        for kind in 0..4 {
            let mut t = match kind { 0 => popover(), 1 => native_menu(), 2 => collection_popover(), _ => layer_zero_menu() };
            t.nodes.get_mut(&1).unwrap().children.push(50);
            t.nodes.insert(50, Fact { role: "AXLayoutArea", owner: 42, id: 10,
                parent: Some(1), window: Some(1), children: vec![51] });
            t.children_errors.insert(50); t.expire_on_id = Some(50);
            assert_eq!(collect(&t, 42, 10, &t.windows), Ok(vec![20]), "route {kind}");
            assert_eq!(t.menu_window_calls.get(), 0);
            assert!(!t.children_calls.borrow().contains(&50));
        }
        let mut t = outline_menu(); t.children_errors.insert(1);
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::AxUnavailable));
        assert_eq!(t.menu_window_calls.get(), 0);
        assert!(!t.children_calls.borrow().contains(&7));
        let mut t = collection_popover();
        t.windows[1].layer = 101;
        t.children_errors.insert(9);
        assert_eq!(collect(&t, 42, 10, &t.windows), Err(DiscoveryStop::AxUnavailable));
        assert_eq!(t.menu_window_calls.get(), 0, "H141 errors also retain priority");
    }
}
