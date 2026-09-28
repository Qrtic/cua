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
    ax_get_window_id, copy_element_attr, copy_string_attr, kAXErrorNoValue, kAXErrorSuccess,
    AXUIElementGetTypeID,
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
                | "AXDateTimeArea"
        )
    )
}

pub(crate) fn native_text_role(role: Option<&str>) -> bool {
    matches!(role, Some("AXTextField" | "AXTextArea"))
}

pub(crate) fn native_date_role(role: Option<&str>) -> bool {
    role == Some("AXDateTimeArea")
}

pub(crate) fn native_value_role(role: Option<&str>) -> bool {
    native_text_role(role) || native_date_role(role)
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

// These are host-side anchors, never controls or an expanded path inside a
// popover. They require the exact host's logical and physical identity below.
fn host_collection_role(role: &str) -> bool {
    matches!(role, "AXCell" | "AXRow" | "AXOutline" | "AXLayoutArea" | "AXTabGroup")
}

// Only literal inner structural roles are candidates. Neither missing AXRole
// nor a host-side/action node gains authority; each accepted node must retain
// the exact popup physical ID, logical popup/host and unique reciprocal path.
fn inner_structural_role(role: &str) -> bool {
    matches!(role, "AXList" | "AXUnknown")
}

enum ControlWindow<N> {
    Present(N),
    NoValue,
    Unavailable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ControlWindowKind { Present, NoValue, Unavailable }

fn control_window_kind(error: i32, value_present: bool, is_element: bool) -> ControlWindowKind {
    match (error, value_present, is_element) {
        (kAXErrorSuccess, true, true) => ControlWindowKind::Present,
        (kAXErrorNoValue, false, _) => ControlWindowKind::NoValue,
        _ => ControlWindowKind::Unavailable,
    }
}

trait PopoverTree {
    type Node: Clone;
    fn role(&self, node: &Self::Node) -> Option<String>;
    fn owner(&self, node: &Self::Node) -> Option<i32>;
    fn window(&self, node: &Self::Node) -> Option<Self::Node>;
    fn control_window(&self, node: &Self::Node) -> ControlWindow<Self::Node> {
        self.window(node).map_or(ControlWindow::Unavailable, ControlWindow::Present)
    }
    fn window_id(&self, node: &Self::Node) -> Option<u32>;
    fn parent(&self, node: &Self::Node) -> Option<Self::Node>;
    fn contains_child(&self, parent: &Self::Node, child: &Self::Node) -> bool;
    fn contains_unique_child(&self, parent: &Self::Node, child: &Self::Node) -> bool;
    fn virtual_button_child(&self, _parent: &Self::Node, _child: &Self::Node) -> bool { false }
    fn same(&self, left: &Self::Node, right: &Self::Node) -> bool;
    fn within_budget(&self) -> bool;
    fn visible_menu_window(&self, node: &Self::Node, pid: i32) -> Option<u32>;
}

/// Revalidate only the new host-collection route. Legacy-only paths do not
/// perform these reads. Nodes and observed roles are retained from the first
/// reciprocal traversal; no current or focused window can replace the host.
fn revalidate_host_collection<T: PopoverTree>(
    tree: &T,
    pid: i32,
    host_id: u32,
    popover_id: u32,
    host: &T::Node,
    nodes: &[T::Node],
    roles: &[String],
) -> bool {
    if nodes.is_empty() || nodes.len() != roles.len() || roles[0] != "AXPopover" {
        return false;
    }
    for (index, (node, role)) in nodes.iter().zip(roles).enumerate() {
        let parent = nodes.get(index + 1).unwrap_or(host);
        if !tree.within_budget()
            || tree.owner(node) != Some(pid)
            || tree.role(node).as_deref() != Some(role.as_str())
            || tree.window_id(node) != Some(if index == 0 { popover_id } else { host_id })
            || !tree.window(node).is_some_and(|window| tree.same(&window, host))
            || !tree.parent(node).is_some_and(|live| tree.same(&live, parent))
            || !tree.contains_unique_child(parent, node)
            || !tree.within_budget()
        {
            return false;
        }
    }
    tree.within_budget()
        && tree.owner(host) == Some(pid)
        && matches!(tree.role(host).as_deref(), Some("AXWindow" | "AXSheet"))
        && tree.window_id(host) == Some(host_id)
        && tree.within_budget()
}

/// Only paths containing a qualified inner structural node pay for this check.
/// These nodes are never host anchors or action targets. Their logical window
/// must remain the same retained popup/host, not a sibling with its ID.
fn revalidate_inner_structure<T: PopoverTree>(
    tree: &T,
    pid: i32,
    popover_id: u32,
    popover: &T::Node,
    nodes: &[T::Node],
    roles: &[String],
    structural_windows: &[(T::Node, T::Node)],
) -> bool {
    if nodes.is_empty() || nodes.len() != roles.len() || structural_windows.is_empty() {
        return false;
    }
    for (index, (node, role)) in nodes.iter().zip(roles).enumerate() {
        let parent = nodes.get(index + 1).unwrap_or(popover);
        if !tree.within_budget()
            || tree.owner(node) != Some(pid)
            || tree.role(node).as_deref() != Some(role.as_str())
            || !tree.parent(node).is_some_and(|live| tree.same(&live, parent))
            || !tree.contains_unique_child(parent, node)
        {
            return false;
        }
        if inner_structural_role(role) {
            let Some((_, window)) = structural_windows.iter().find(|(inner, _)| tree.same(inner, node)) else {
                return false;
            };
            if tree.owner(window) != Some(pid)
                || tree.window_id(node) != Some(popover_id)
                || !tree.window(node).is_some_and(|live| tree.same(&live, window))
            {
                return false;
            }
        }
        if !tree.within_budget() {
            return false;
        }
    }
    true
}

/// Only the explicitly absent action-control AXWindow uses this stronger
/// second pass. Every retained edge is unique and reciprocal; every other
/// node has a positive logical window and the phase's exact physical ID.
fn revalidate_no_value_path<T: PopoverTree>(
    tree: &T, pid: i32, host_id: u32, popover_id: u32,
    popover: &T::Node, host: &T::Node, host_role: &str,
    nodes: &[T::Node], roles: &[String], windows: &[Option<T::Node>],
) -> bool {
    if nodes.is_empty() || nodes.len() != roles.len() || nodes.len() != windows.len() {
        return false;
    }
    let Some(popup_index) = nodes.iter().position(|node| tree.same(node, popover)) else {
        return false;
    };
    for (index, node) in nodes.iter().enumerate() {
        let parent = nodes.get(index + 1).unwrap_or(host);
        if !tree.within_budget()
            || tree.owner(node) != Some(pid)
            || tree.role(node).as_deref() != Some(roles[index].as_str())
            || tree.window_id(node) != Some(if index <= popup_index { popover_id } else { host_id })
            || !tree.parent(node).is_some_and(|live| tree.same(&live, parent))
            || !tree.contains_unique_child(parent, node)
        {
            return false;
        }
        let window_unchanged = if index == 0 {
            windows[index].is_none()
                && matches!(tree.control_window(node), ControlWindow::NoValue)
        } else {
            windows[index].as_ref().is_some_and(|window| {
                tree.window(node).is_some_and(|live| tree.same(&live, window))
                    && tree.owner(window) == Some(pid)
            })
        };
        if !window_unchanged || !tree.within_budget() { return false; }
    }
    tree.within_budget()
        && tree.owner(host) == Some(pid)
        && tree.role(host).as_deref() == Some(host_role)
        && tree.window_id(host) == Some(host_id)
        && tree.within_budget()
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
        let role = tree.role(&current);
        match role.as_deref() {
            Some("AXPopover") => return Ok(current),
            // Candidate discovery only. The full walk below must bind each
            // inner structural node to this exact popup and revalidate its path.
            Some(role) if inner_structural_role(role) => {}
            Some(role) if native_control_role(Some(role)) || container_role(role) => {}
            _ => {
                tracing::debug!(target: "cua_popover_proof", stage = "containing_popover",
                    lookup_depth = visited.len() + 1,
                    role = role.as_deref().filter(|role| role.len() <= 64).unwrap_or("<missing-or-oversize>"),
                    "attached popover lookup stopped at role boundary");
                return Err("popover_lookup_boundary");
            }
        }
        let parent = tree
            .parent(&current)
            .ok_or("popover_lookup_parent_missing")?;
        if !tree.contains_child(&parent, &current)
            && !(tree.same(&current, element) && tree.virtual_button_child(&parent, &current))
        {
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
    let mut no_value_control = false;
    let mut no_value_role = None;
    let popover = if is_popover_root {
        element.clone()
    } else if let Some(role) = tree.role(control).filter(|role| native_control_role(Some(role.as_str()))) {
        match tree.control_window(control) {
            ControlWindow::Present(window) => {
                let popover = match tree.role(&window).as_deref() {
                    Some("AXPopover") => window.clone(),
                    Some("AXWindow") => containing_popover(tree, pid, control)?,
                    _ => return Err("element_window_not_popover"),
                };
                control_window = Some(window);
                popover
            }
            ControlWindow::NoValue if menu_path.is_none() => {
                no_value_control = true;
                no_value_role = Some(role);
                containing_popover(tree, pid, control)?
            }
            _ => return Err("element_window_missing"),
        }
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
    let host_role = tree.role(&host);
    if !matches!(host_role.as_deref(), Some("AXWindow" | "AXSheet")) {
        return Err("host_role_unexpected");
    }
    if tree.owner(&host) != Some(pid) {
        return Err("host_owner_mismatch");
    }
    if tree.window_id(&host) != Some(host_id) {
        return Err("host_window_id_mismatch");
    }
    if no_value_control && (pid <= 0 || host_id == 0 || popover_id == 0) {
        return Err("no_value_identity_missing");
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
    let mut host_segment_start = 0;
    let mut host_roles = Vec::new();
    let mut uses_host_collection = false;
    let mut inner_roles = Vec::new();
    let mut structural_windows = Vec::new();
    let mut no_value_windows = Vec::new();
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
            if no_value_control {
                let roles = [inner_roles, host_roles].concat();
                return (crossed_popover && revalidate_no_value_path(
                    tree, pid, host_id, popover_id, &popover, &host,
                    host_role.as_deref().expect("accepted host role"),
                    &visited, &roles, &no_value_windows,
                )).then_some(()).ok_or("no_value_attachment_changed");
            }
            // Re-read the attachment after traversal; an old AXParent alone
            // must not authorize a closed or reattached panel.
            let unchanged = (structural_windows.is_empty()
                || revalidate_inner_structure(
                    tree, pid, popover_id, &popover,
                    &visited[..host_segment_start], &inner_roles, &structural_windows,
                ))
                && crossed_popover
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
                && (!uses_host_collection
                    || revalidate_host_collection(
                        tree,
                        pid,
                        host_id,
                        popover_id,
                        &host,
                        &visited[host_segment_start..],
                        &host_roles,
                    ))
                && tree.within_budget();
            return unchanged.then_some(()).ok_or("attachment_changed");
        }
        let role = tree.role(&current);
        let strict_window = if no_value_control {
            if role.as_deref() == Some("AXUnknown")
                || (tree.same(&current, control) && role.as_deref() != no_value_role.as_deref())
                || tree.window_id(&current) != Some(if crossed_popover { host_id } else { popover_id })
            {
                return Err("no_value_node_identity_missing");
            }
            if tree.same(&current, control) {
                None
            } else {
                let window = tree.window(&current).ok_or("no_value_ancestor_window_missing")?;
                let logical_matches = if crossed_popover || tree.same(&current, &popover) {
                    tree.same(&window, &host)
                } else {
                    tree.same(&window, &popover) || tree.same(&window, &host)
                };
                if !logical_matches || tree.owner(&window) != Some(pid) || !tree.within_budget() {
                    return Err("no_value_ancestor_window_mismatch");
                }
                Some(window)
            }
        } else { None };
        match role.as_deref() {
            Some("AXPopover") if tree.same(&current, &popover) && !crossed_popover => {
                crossed_popover = true;
                host_segment_start = visited.len();
            }
            Some(role) if !crossed_popover && inner_structural_role(role) => {
                let window = strict_window.clone().or_else(|| tree.window(&current))
                    .ok_or("inner_list_window_missing")?;
                if tree.owner(&window) != Some(pid)
                    || tree.window_id(&current) != Some(popover_id)
                    || !(tree.same(&window, &popover) || tree.same(&window, &host))
                    || !tree.within_budget()
                {
                    return Err("inner_list_identity_mismatch");
                }
                structural_windows.push((current.clone(), window));
            }
            Some(role) if crossed_popover && host_collection_role(role) => {
                if tree.window_id(&current) != Some(host_id)
                    || !strict_window.clone().or_else(|| tree.window(&current))
                        .is_some_and(|window| tree.same(&window, &host))
                    || !tree.within_budget()
                {
                    return Err("host_collection_identity_mismatch");
                }
                uses_host_collection = true;
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
        let reciprocal = if no_value_control
            || (!crossed_popover && role.as_deref().is_some_and(inner_structural_role))
        {
            tree.contains_unique_child(&parent, &current)
        } else {
            tree.contains_child(&parent, &current)
                || (tree.same(&current, element) && tree.virtual_button_child(&parent, &current))
        };
        if !reciprocal {
            tracing::debug!(target: "cua_popover_proof", depth, role = ?role,
                "popover ancestry lacks reciprocal child relation");
            return Err("ancestor_child_relation_missing");
        }
        if crossed_popover {
            host_roles.push(role.expect("accepted role"));
        } else {
            inner_roles.push(role.expect("accepted role"));
        }
        if no_value_control { no_value_windows.push(strict_window); }
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
        let timeout_status = AXUIElementSetMessagingTimeout(ptr, 0.2);
        if timeout_status != kAXErrorSuccess {
            tracing::debug!(target: "cua_popover_proof", ax_error = timeout_status,
                timeout_seconds = 0.2,
                "attached popover node messaging timeout setup failed");
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
    allow_control_no_value: bool,
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
    fn control_window(&self, node: &AxNode) -> ControlWindow<AxNode> {
        if !self.allow_control_no_value {
            return self.window(node).map_or(ControlWindow::Unavailable, ControlWindow::Present);
        }
        // One AXWindow query, as on the existing successful path. Preserve the
        // raw status here: the legacy Option intentionally merges missing and
        // erroneous attributes and cannot grant the new proof.
        unsafe {
            let attr = CFString::new("AXWindow");
            let mut value: CFTypeRef = std::ptr::null();
            let error = AXUIElementCopyAttributeValue(node.0, attr.as_concrete_TypeRef(), &mut value);
            let types = (error == kAXErrorSuccess && !value.is_null())
                .then(|| (CFGetTypeID(value), AXUIElementGetTypeID()));
            match control_window_kind(error, !value.is_null(), types.is_some_and(|(a, b)| a == b)) {
                ControlWindowKind::Present => AxNode::owned(value as AXUIElementRef)
                    .map_or(ControlWindow::Unavailable, ControlWindow::Present),
                kind => {
                    tracing::debug!(target: "cua_popover_proof", ax_error = error,
                        value_present = !value.is_null(), ?kind,
                        actual_type_id = ?types.map(|(actual, _)| actual),
                        expected_type_id = ?types.map(|(_, expected)| expected),
                        "action control AXWindow unavailable");
                    if !value.is_null() { CFRelease(value); }
                    if kind == ControlWindowKind::NoValue { ControlWindow::NoValue }
                    else { ControlWindow::Unavailable }
                }
            }
        }
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
    fn contains_unique_child(&self, parent: &AxNode, child: &AxNode) -> bool {
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
                && (0..children.len()).filter(|index| {
                    CFEqual(
                        *children.get(*index).expect("bounded index"),
                        child.0 as CFTypeRef,
                    ) != 0
                }).count() == 1
        }
    }
    fn same(&self, left: &AxNode, right: &AxNode) -> bool {
        unsafe { CFEqual(left.0 as CFTypeRef, right.0 as CFTypeRef) != 0 }
    }
    fn virtual_button_child(&self, parent: &AxNode, child: &AxNode) -> bool {
        self.within_budget()
            && unsafe { super::virtual_button::proves(parent.0, child.0, self.deadline) }
    }
    fn within_budget(&self) -> bool {
        Instant::now() < self.deadline
    }
    fn visible_menu_window(&self, node: &AxNode, pid: i32) -> Option<u32> {
        let timing = super::menu_window_diagnostics::Timing::start();
        let mut observed_frame = None;
        let mut observed_windows = None;
        let mut matched_window = None;
        let mut phase = "budget_before_frame";
        let result = (|| {
            if !self.within_budget() {
                return None;
            }
            phase = "frame_read_missing";
            observed_frame = unsafe { super::bindings::element_screen_rect(node.0) };
            let frame = observed_frame?;
            observed_windows = Some(crate::windows::all_windows_including_accessory_layers());
            phase = "window_match";
            let window = match_menu_window(pid, &frame, observed_windows.as_deref().unwrap())?;
            // The original temporary snapshot was dropped before the final
            // budget check. Retain it only when matching has already failed.
            drop(observed_windows.take());
            matched_window = Some(window);
            phase = "budget_after_match";
            self.within_budget().then_some(window)
        })();
        // Resolve the original decision and its end timestamp before any
        // diagnostic enumeration/formatting. Reuse the existing snapshot only.
        let completed = crate::order_diagnostics::monotonic_us();
        if let Some(window) = matched_window.filter(|_| result.is_none()) {
            timing.refusal_after_match(completed, pid, observed_frame, window);
        } else if result.is_none() {
            timing.refusal(
                completed,
                pid,
                phase,
                observed_frame,
                observed_windows.iter().flatten().map(|window| {
                    super::menu_window_diagnostics::Candidate {
                        pid: window.pid,
                        id: window.window_id,
                        bounds: [
                            window.bounds.x,
                            window.bounds.y,
                            window.bounds.width,
                            window.bounds.height,
                        ],
                        layer: window.layer,
                        on_screen: window.is_on_screen,
                        on_current_space: window.on_current_space,
                    }
                }),
            );
        }
        result
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
            allow_control_no_value: true,
        },
        pid,
        host_id,
        &element,
    )
}

/// Capture-only variant sharing its caller's discovery deadline. Existing
/// action callers retain the separate two-second wrapper above. AX messaging
/// is synchronous: an already-started message may overrun this deadline by its
/// existing 0.2s timeout; an expired proof never authorizes an attachment.
///
/// # Safety
/// `element` must remain a retained, live AX reference for this read-only proof.
pub(crate) unsafe fn proves_attached_popover_before(
    pid: i32,
    host_id: u32,
    element: AXUIElementRef,
    deadline: Instant,
) -> bool {
    if element.is_null() || Instant::now() >= deadline {
        return false;
    }
    CFRetain(element as CFTypeRef);
    let Some(element) = AxNode::owned(element) else {
        return false;
    };
    Instant::now() < deadline
        && prove(&NativeTree { deadline, allow_control_no_value: false }, pid, host_id, &element)
        && Instant::now() < deadline
}

/// Project a real hit-tested preview control, not the actionless outer tile.
/// Only an exact displaced popover child is returned; caller must CFRelease.
pub(crate) unsafe fn copy_virtual_popover_button(wrapper: AXUIElementRef) -> Option<AXUIElementRef> {
    let mut pid = 0;
    if AXUIElementGetPid(wrapper, &mut pid) != kAXErrorSuccess || pid <= 0 { return None; }
    let host = AxNode::owned(copy_element_attr(wrapper, "AXWindow")?)?;
    if !matches!(copy_string_attr(host.0, "AXRole").as_deref(), Some("AXWindow" | "AXSheet")) {
        return None;
    }
    let host_id = ax_get_window_id(host.0)?;
    if ax_get_window_id(wrapper)? == host_id { return None; }
    let child = super::virtual_button::copy_child(wrapper, Instant::now() + Duration::from_millis(750))?;
    if proves_attached_popover(pid, host_id, child) {
        Some(child)
    } else {
        CFRelease(child as CFTypeRef);
        None
    }
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
        virtual_edges: Vec<(u32, u32)>,
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
        fn contains_unique_child(&self, parent: &u32, child: &u32) -> bool {
            self.nodes.get(parent).is_some_and(|node| {
                node.children.len() <= MAX_CHILDREN as usize
                    && node.children.iter().filter(|candidate| self.same(candidate, child)).count() == 1
            })
        }
        fn virtual_button_child(&self, parent: &u32, child: &u32) -> bool {
            self.virtual_edges.contains(&(*parent, *child))
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
            virtual_edges: Vec::new(),
        }
    }

    fn host_collection() -> Tree {
        // Retained live native structure: the collection and layout nodes are
        // outside the popover, with the host's logical and physical identity.
        let roles = [
            "AXCheckBox", "AXGroup", "AXPopover", "AXGroup", "AXCell", "AXRow",
            "AXOutline", "AXScrollArea", "AXLayoutArea", "AXSplitGroup", "AXWindow",
        ];
        let mut tree = pages();
        tree.nodes = roles.into_iter().enumerate().map(|(index, role)| {
            let node = index as u32;
            (node, Node {
                identity: node, role, owner: 42,
                window: if node == 0 { Some(2) } else if node < 10 { Some(10) } else { None },
                id: Some(if node <= 2 { 900 } else { 700 }),
                parent: (node < 10).then_some(node + 1),
                children: if node == 0 { vec![] } else { vec![node - 1] },
            })
        }).collect();
        tree.budget.set(500);
        tree
    }

    // Mutation is delivered on the second read of one retained host fact,
    // after the original traversal accepted it. It never touches real AX.
    struct ChangingHost {
        tree: Tree,
        node: u32,
        field: &'static str,
        reads: Cell<usize>,
        unique_reads: Cell<usize>,
    }
    impl ChangingHost {
        fn new(tree: Tree, node: u32, field: &'static str) -> Self {
            Self { tree, node, field, reads: Cell::new(0), unique_reads: Cell::new(0) }
        }
        fn changed(&self, node: &u32, field: &str) -> bool {
            if *node != self.node || field != self.field { return false; }
            let reads = self.reads.get();
            self.reads.set(reads + 1);
            reads > 0
        }
    }
    impl PopoverTree for ChangingHost {
        type Node = u32;
        fn role(&self, node: &u32) -> Option<String> {
            if self.changed(node, "role") { Some("AXGroup".into()) } else { self.tree.role(node) }
        }
        fn owner(&self, node: &u32) -> Option<i32> {
            if self.changed(node, "owner") { Some(99) } else { self.tree.owner(node) }
        }
        fn window(&self, node: &u32) -> Option<u32> {
            if self.changed(node, "window") { Some(9) } else { self.tree.window(node) }
        }
        fn window_id(&self, node: &u32) -> Option<u32> {
            if self.changed(node, "id") { Some(701) } else { self.tree.window_id(node) }
        }
        fn parent(&self, node: &u32) -> Option<u32> {
            if self.changed(node, "parent") { None } else { self.tree.parent(node) }
        }
        fn contains_child(&self, parent: &u32, child: &u32) -> bool {
            !self.changed(parent, "children") && self.tree.contains_child(parent, child)
        }
        fn contains_unique_child(&self, parent: &u32, child: &u32) -> bool {
            self.unique_reads.set(self.unique_reads.get() + 1);
            if self.field == "deadline" { self.tree.budget.set(0); }
            !self.changed(parent, "children") && self.tree.contains_unique_child(parent, child)
        }
        fn virtual_button_child(&self, parent: &u32, child: &u32) -> bool {
            self.tree.virtual_button_child(parent, child)
        }
        fn same(&self, left: &u32, right: &u32) -> bool { self.tree.same(left, right) }
        fn within_budget(&self) -> bool { self.tree.within_budget() }
        fn visible_menu_window(&self, node: &u32, pid: i32) -> Option<u32> {
            self.tree.visible_menu_window(node, pid)
        }
    }

    // This wrapper invokes the production raw-status classifier and proof.
    // Mutations start only after every first-pass unique edge was accepted.
    struct NoValueTree {
        tree: Tree,
        raw: (i32, bool, bool),
        late: Option<(u32, &'static str)>,
        edges: usize,
        unique_reads: Cell<usize>,
        control_reads: Cell<usize>,
        changed_reads: Cell<usize>,
    }
    impl NoValueTree {
        fn new(mut tree: Tree) -> Self {
            tree.nodes.get_mut(&0).unwrap().role = "AXTextField";
            tree.nodes.get_mut(&0).unwrap().window = None;
            tree.budget.set(1000);
            Self { tree, raw: (kAXErrorNoValue, false, false), late: None,
                edges: 6, unique_reads: Cell::new(0), control_reads: Cell::new(0),
                changed_reads: Cell::new(0) }
        }
        fn changed(&self, node: u32, field: &str) -> bool {
            let changed = self.unique_reads.get() >= self.edges
                && self.late == Some((node, field));
            if changed { self.changed_reads.set(self.changed_reads.get() + 1); }
            changed
        }
    }
    impl PopoverTree for NoValueTree {
        type Node = u32;
        fn role(&self, node: &u32) -> Option<String> {
            if self.changed(*node, "role") { Some("AXWebArea".into()) } else { self.tree.role(node) }
        }
        fn owner(&self, node: &u32) -> Option<i32> {
            if self.changed(*node, "owner") { Some(99) } else { self.tree.owner(node) }
        }
        fn window(&self, node: &u32) -> Option<u32> {
            if self.changed(*node, "window") { Some(9) } else { self.tree.window(node) }
        }
        fn control_window(&self, node: &u32) -> ControlWindow<u32> {
            if *node != 0 { return self.window(node).map_or(ControlWindow::Unavailable, ControlWindow::Present); }
            self.control_reads.set(self.control_reads.get() + 1);
            if self.changed(*node, "raw") { return ControlWindow::Unavailable; }
            if self.changed(*node, "window_present") { return ControlWindow::Present(6); }
            match control_window_kind(self.raw.0, self.raw.1, self.raw.2) {
                ControlWindowKind::NoValue => ControlWindow::NoValue,
                ControlWindowKind::Present => ControlWindow::Present(6),
                ControlWindowKind::Unavailable => ControlWindow::Unavailable,
            }
        }
        fn window_id(&self, node: &u32) -> Option<u32> {
            if self.changed(*node, "id") { None } else { self.tree.window_id(node) }
        }
        fn parent(&self, node: &u32) -> Option<u32> {
            if self.changed(*node, "parent") { None } else { self.tree.parent(node) }
        }
        fn contains_child(&self, parent: &u32, child: &u32) -> bool {
            self.tree.contains_child(parent, child)
        }
        fn contains_unique_child(&self, parent: &u32, child: &u32) -> bool {
            let changed = self.changed(*parent, "children");
            self.unique_reads.set(self.unique_reads.get() + 1);
            !changed && self.tree.contains_unique_child(parent, child)
        }
        fn virtual_button_child(&self, parent: &u32, child: &u32) -> bool {
            self.tree.virtual_button_child(parent, child)
        }
        fn same(&self, a: &u32, b: &u32) -> bool { self.tree.same(a, b) }
        fn within_budget(&self) -> bool {
            !self.changed(0, "deadline") && self.tree.within_budget()
        }
        fn visible_menu_window(&self, node: &u32, pid: i32) -> Option<u32> {
            self.tree.visible_menu_window(node, pid)
        }
    }

    #[test]
    fn no_value_control_requires_exact_raw_error_and_null() {
        assert_eq!(control_window_kind(kAXErrorNoValue, false, false), ControlWindowKind::NoValue);
        assert_eq!(control_window_kind(kAXErrorSuccess, true, true), ControlWindowKind::Present);
        for raw in [(kAXErrorNoValue, true, true), (kAXErrorSuccess, false, false),
            (kAXErrorSuccess, true, false), (-25204, false, false), (-25202, false, false),
            (-25201, true, true)] {
            assert_eq!(control_window_kind(raw.0, raw.1, raw.2), ControlWindowKind::Unavailable);
            let mut tree = NoValueTree::new(wrapped_toolbar_popover());
            tree.raw = raw;
            assert_eq!(prove_checked(&tree, 42, 700, &0), Err("element_window_missing"));
            assert_eq!(tree.unique_reads.get(), 0, "raw failure must not enter alternative proof");
        }
    }

    #[test]
    fn no_value_native_field_proves_complete_retained_toolbar_path_twice() {
        for sheet in [false, true] {
            let mut tree = NoValueTree::new(wrapped_toolbar_popover());
            if sheet { tree.tree.nodes.get_mut(&6).unwrap().role = "AXSheet"; }
            assert_eq!(prove_checked(&tree, 42, 700, &0), Ok(()));
            assert_eq!(tree.control_reads.get(), 2);
            assert_eq!(tree.unique_reads.get(), 12, "six actual edges on each pass");
        }
        let mut direct = NoValueTree::new(wrapped_toolbar_popover());
        for (node, parent, child) in [(0, 2, None), (2, 4, Some(0)), (4, 6, Some(2))] {
            let entry = direct.tree.nodes.get_mut(&node).unwrap();
            entry.parent = Some(parent);
            entry.children = child.into_iter().collect();
        }
        direct.tree.nodes.get_mut(&6).unwrap().children = vec![4];
        direct.edges = 3;
        assert_eq!(prove_checked(&direct, 42, 700, &0), Ok(()));
        assert_eq!(direct.unique_reads.get(), 6, "direct field/popover/toolbar/host path");
        let mut legacy = wrapped_toolbar_popover();
        legacy.nodes.get_mut(&0).unwrap().window = None;
        assert_eq!(prove_checked(&legacy, 42, 700, &0), Err("element_window_missing"),
            "a collapsed Option is not NoValue evidence");
    }

    #[test]
    fn no_value_route_requires_every_physical_owner_and_positive_ancestor_window() {
        for node in 0..=6 {
            for field in ["owner", "id_missing", "id_other"] {
                let mut tree = NoValueTree::new(wrapped_toolbar_popover());
                let entry = tree.tree.nodes.get_mut(&node).unwrap();
                match field { "owner" => entry.owner = 99, "id_missing" => entry.id = None,
                    _ => entry.id = Some(701) }
                assert!(!prove(&tree, 42, 700, &0), "node {node} field {field}");
            }
        }
        for node in 1..6 {
            for window in [None, Some(9)] {
                let mut tree = NoValueTree::new(wrapped_toolbar_popover());
                tree.tree.nodes.get_mut(&node).unwrap().window = window;
                assert!(!prove(&tree, 42, 700, &0), "node {node} window {window:?}");
            }
        }
        for id in [0, 701] { assert!(!prove(&NoValueTree::new(pages()), 42, id, &0)); }
        let mut tree = NoValueTree::new(pages());
        for node in 0..=2 { tree.tree.nodes.get_mut(&node).unwrap().id = Some(0); }
        assert!(!prove(&tree, 42, 700, &0));
    }

    #[test]
    fn no_value_route_never_accepts_opaque_boundaries_or_virtual_edges() {
        for node in [1, 3, 4] {
            for role in ["AXUnknown", "AXWebArea", "AXApplication", "AXTable", "AXPopover", "AXWindow"] {
                let mut tree = NoValueTree::new(wrapped_toolbar_popover());
                tree.tree.nodes.get_mut(&node).unwrap().role = role;
                assert!(!prove(&tree, 42, 700, &0), "node {node} role {role}");
            }
        }
        assert!(!prove(&NoValueTree::new(virtual_preview()), 42, 700, &0));
        let mut menu = NoValueTree::new(calendar_menu());
        menu.tree.nodes.get_mut(&0).unwrap().role = "AXPopUpButton";
        assert_eq!(prove_checked(&menu, 42, 700, &8), Err("element_window_missing"));
    }

    #[test]
    fn no_value_route_requires_unique_edges_and_rejects_cycles_and_bounds() {
        for parent in 1..=6 {
            for duplicate in [false, true] {
                let mut tree = NoValueTree::new(wrapped_toolbar_popover());
                let children = &mut tree.tree.nodes.get_mut(&parent).unwrap().children;
                if duplicate { children.push(parent - 1); } else { children.clear(); }
                assert!(!prove(&tree, 42, 700, &0), "parent {parent} duplicate {duplicate}");
            }
        }
        let mut tree = NoValueTree::new(pages());
        tree.tree.nodes.get_mut(&1).unwrap().parent = Some(0);
        tree.tree.nodes.get_mut(&0).unwrap().children.push(1);
        assert!(!prove(&tree, 42, 700, &0));
        let mut tree = NoValueTree::new(pages());
        tree.tree.nodes.get_mut(&2).unwrap().children = vec![1; MAX_CHILDREN as usize + 1];
        assert!(!prove(&tree, 42, 700, &0));
        let tree = NoValueTree::new(pages());tree.tree.budget.set(0);
        assert!(!prove(&tree, 42, 700, &0));
        let mut deep = NoValueTree::new(pages());
        deep.tree.nodes.get_mut(&0).unwrap().parent = Some(100);
        for id in 100..=132 {
            deep.tree.nodes.insert(id, Node { identity: id, role: "AXGroup", owner: 42,
                window: Some(6), id: Some(900),
                parent: Some(if id == 132 { 2 } else { id + 1 }),
                children: vec![if id == 100 { 0 } else { id - 1 }] });
        }
        deep.tree.nodes.get_mut(&2).unwrap().children = vec![132];
        assert_eq!(prove_checked(&deep, 42, 700, &0), Err("popover_lookup_depth_limit"));
    }

    #[test]
    fn no_value_route_rechecks_retained_facts_after_the_whole_first_walk() {
        for (node, field) in [(0, "owner"), (0, "role"), (0, "id"), (0, "parent"),
            (0, "raw"), (0, "window_present"), (1, "window"), (2, "window"),
            (3, "parent"), (4, "role"), (5, "id"), (6, "children"),
            (6, "owner"), (6, "role"), (6, "id"), (0, "deadline")] {
            let mut tree = NoValueTree::new(wrapped_toolbar_popover());
            tree.late = Some((node, field));
            assert!(prove_checked(&tree, 42, 700, &0).is_err(),
                "late node {node} field {field}");
            assert!(tree.unique_reads.get() >= 6, "must finish first walk");
            assert!(tree.changed_reads.get() > 0, "must exercise actual late {field} read");
        }
    }

    #[test]
    fn host_collection_proves_native_control_and_popover_root_to_exact_host() {
        for logical_host in [false, true] {
            let mut tree = host_collection();
            if logical_host { tree.nodes.get_mut(&0).unwrap().window = Some(10); }
            assert!(prove(&tree, 42, 700, &0));
            assert!(prove(&tree, 42, 700, &2));
            assert!(!prove(&tree, 42, 701, &0));
        }
    }

    #[test]
    fn popover_lookup_keeps_stepper_and_foreign_container_boundaries() {
        for role in ["AXIncrementor", "AXWebArea", "AXTable", "AXApplication"] {
            let mut tree = host_collection();
            tree.nodes.get_mut(&0).unwrap().role = "AXButton";
            tree.nodes.get_mut(&0).unwrap().window = Some(10);
            tree.nodes.get_mut(&1).unwrap().role = role;
            assert_eq!(prove_checked(&tree, 42, 700, &0), Err("popover_lookup_boundary"), "{role}");
        }
    }

    #[test]
    fn host_collection_does_not_admit_inner_collections_or_collection_actions() {
        for role in ["AXCell", "AXRow", "AXOutline", "AXLayoutArea"] {
            let mut tree = host_collection();
            tree.nodes.get_mut(&1).unwrap().role = role;
            assert!(!prove(&tree, 42, 700, &0), "inner {role}");
            tree.nodes.get_mut(&0).unwrap().window = Some(10);
            assert!(!prove(&tree, 42, 700, &0), "host-named inner {role}");
            assert!(!prove(&host_collection(), 42, 700, &4));
            assert_eq!(advertised_action(Some(role), "press", &["AXPress".into()]), None);
        }
    }

    #[test]
    fn host_collection_requires_every_outer_node_to_name_the_exact_host() {
        for node in 3..10 {
            for kind in 0..5 {
                let mut tree = host_collection();
                let entry = tree.nodes.get_mut(&node).unwrap();
                match kind {
                    0 => entry.owner = 99,
                    1 => entry.id = None,
                    2 => entry.id = Some(900),
                    3 => entry.window = None,
                    _ => entry.window = Some(9),
                }
                assert!(!prove(&tree, 42, 700, &0), "node {node} kind {kind}");
            }
        }
    }

    #[test]
    fn host_collection_requires_unique_reciprocal_edges_and_keeps_boundaries() {
        for parent in 3..=10 {
            for duplicate in [false, true] {
                let mut tree = host_collection();
                let entry = tree.nodes.get_mut(&parent).unwrap();
                if duplicate { entry.children.push(parent - 1); } else { entry.children.clear(); }
                assert!(!prove(&tree, 42, 700, &0), "parent {parent} duplicate {duplicate}");
            }
        }
        for role in ["AXTable", "AXList", "AXWebArea", "AXApplication", "AXWindow", "AXSheet", "AXPopover"] {
            let mut tree = host_collection();
            tree.nodes.get_mut(&5).unwrap().role = role;
            assert!(!prove(&tree, 42, 700, &0), "boundary {role}");
        }
        let mut tree = host_collection();
        tree.nodes.get_mut(&5).unwrap().parent = Some(4);
        tree.nodes.get_mut(&4).unwrap().children.push(5);
        assert!(!prove(&tree, 42, 700, &0), "cycle");
    }

    #[test]
    fn host_collection_rereads_live_roles_identity_and_edges_before_authorizing() {
        for field in ["role", "owner", "window", "id", "parent", "children"] {
            let node = if field == "children" { 5 } else { 4 };
            let tree = ChangingHost::new(host_collection(), node, field);
            assert!(!prove(&tree, 42, 700, &0), "changed {field}");
            assert!(tree.reads.get() >= 2, "must exercise fresh {field} read");
        }
    }

    #[test]
    fn host_collection_keeps_deadline_and_child_bounds_without_retry() {
        for budget in [0, 5, 15, 25] {
            let tree = host_collection();
            tree.budget.set(budget);
            assert!(!prove(&tree, 42, 700, &0), "budget {budget}");
        }
        let tree = ChangingHost::new(host_collection(), 4, "deadline");
        assert!(!prove(&tree, 42, 700, &0));
        assert_eq!(tree.unique_reads.get(), 1);
        let mut tree = host_collection();
        tree.nodes.get_mut(&5).unwrap().children = vec![4; MAX_CHILDREN as usize + 1];
        assert!(!prove(&tree, 42, 700, &0));
    }

    #[test]
    fn legacy_popover_paths_never_invoke_host_collection_revalidation() {
        let tree = ChangingHost::new(pages(), 4, "deadline");
        assert!(prove(&tree, 42, 700, &0));
        assert_eq!(tree.unique_reads.get(), 0);
        let tree = ChangingHost::new(wrapped_toolbar_popover(), 4, "deadline");
        assert!(prove(&tree, 42, 700, &0));
        assert_eq!(tree.unique_reads.get(), 0);
    }

    #[test]
    fn pages_swatch_crosses_its_attached_popover_to_exact_host() {
        assert!(prove(&pages(), 42, 700, &0));
    }

    fn virtual_preview() -> Tree {
        let mut tree = pages();
        tree.nodes.get_mut(&0).unwrap().window = Some(6);
        tree.nodes.get_mut(&1).unwrap().role = "AXButton";
        tree.nodes.get_mut(&1).unwrap().children.clear();
        tree.virtual_edges.push((1, 0));
        tree
    }

    #[test]
    fn h101_virtual_preview_still_requires_complete_outer_popover_attachment() {
        assert!(prove(&virtual_preview(), 42, 700, &0));
        for kind in 0..6 {
            let mut tree = virtual_preview();
            match kind {
                0 => tree.virtual_edges.clear(),
                1 => tree.nodes.get_mut(&1).unwrap().owner = 99,
                2 => tree.nodes.get_mut(&3).unwrap().children.clear(),
                3 => tree.nodes.get_mut(&0).unwrap().id = Some(700),
                4 => tree.reattach = true,
                _ => tree.budget.set(0),
            }
            assert!(!prove(&tree, 42, 700, &0), "case {kind}");
        }
    }

    #[test]
    fn h080_native_date_editor_reaches_its_reciprocal_popover_host() {
        let mut tree = pages();
        let editor = tree.nodes.get_mut(&0).unwrap();
        editor.role = "AXDateTimeArea";
        editor.window = Some(6);
        editor.parent = Some(2);
        tree.nodes.get_mut(&2).unwrap().children = vec![0];
        assert!(prove(&tree, 42, 700, &0));
    }

    #[test]
    fn native_date_editor_does_not_relax_closed_foreign_or_replaced_popovers() {
        for kind in 0..6 {
            let mut tree = pages();
            let editor = tree.nodes.get_mut(&0).unwrap();
            editor.role = "AXDateTimeArea";
            editor.window = Some(6);
            editor.parent = Some(2);
            tree.nodes.get_mut(&2).unwrap().children = vec![0];
            match kind {
                0 => tree.nodes.get_mut(&2).unwrap().children.clear(),
                1 => tree.nodes.get_mut(&0).unwrap().owner = 99,
                2 => tree.nodes.get_mut(&0).unwrap().id = Some(700),
                3 => tree.nodes.get_mut(&2).unwrap().role = "AXWebArea",
                4 => tree.reattach = true,
                _ => tree.budget.set(0),
            }
            assert!(!prove(&tree, 42, 700, &0), "case {kind}");
        }
        assert!(native_value_role(Some("AXDateTimeArea")));
        assert!(!native_text_role(Some("AXDateTimeArea")));
        assert_eq!(
            advertised_action(Some("AXDateTimeArea"), "confirm", &["AXConfirm".into()]),
            None
        );
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
            target_on_screen: Some(true),
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
    fn inner_list(logical_host: bool) -> Tree {
        let mut tree = wrapped_toolbar_popover();
        tree.nodes.get_mut(&0).unwrap().role = "AXCheckBox";
        tree.nodes.get_mut(&0).unwrap().window = Some(if logical_host { 6 } else { 2 });
        tree.nodes.get_mut(&1).unwrap().role = "AXCheckBox";
        tree.nodes.get_mut(&1).unwrap().parent = Some(8);
        tree.nodes.get_mut(&2).unwrap().children = vec![8];
        tree.nodes.insert(8, Node {
            identity: 8, role: "AXList", owner: 42,
            window: Some(6), id: Some(900), parent: Some(2), children: vec![1],
        });
        tree
    }

    #[test]
    fn inner_list_proves_both_logical_control_window_paths() {
        for logical_host in [false, true] {
            for list_window in [2, 6] {
                let mut tree = inner_list(logical_host);
                tree.nodes.get_mut(&8).unwrap().window = Some(list_window);
                assert_eq!(prove_checked(&tree, 42, 700, &0), Ok(()));
                assert!(!prove(&tree, 42, 701, &0));
            }
        }
        let mut tree = inner_list(true);
        tree.nodes.insert(10, tree.nodes[&6].clone());
        tree.nodes.get_mut(&8).unwrap().window = Some(10);
        assert!(prove(&tree, 42, 700, &0), "CF-equivalent logical host proxy");
    }

    #[test]
    fn inner_list_does_not_admit_outer_lists_or_new_actions() {
        for logical_host in [false, true] {
            let mut tree = inner_list(logical_host);
            assert!(!prove(&tree, 42, 700, &8), "list is not a control");
            tree.nodes.get_mut(&3).unwrap().role = "AXList";
            assert_eq!(prove_checked(&tree, 42, 700, &0), Err("ancestor_role_unexpected"));
        }
        for action in ["press", "click", "show_menu", "confirm", "cancel"] {
            assert_eq!(advertised_action(Some("AXList"), action,
                &["AXPress".into(), "AXShowMenu".into(), "AXConfirm".into(), "AXCancel".into()]), None);
        }
    }

    #[test]
    fn inner_list_requires_exact_native_identity_not_a_sibling_or_web_path() {
        for logical_host in [false, true] {
            for kind in 0..7 {
                let mut tree = inner_list(logical_host);
                let list = tree.nodes.get_mut(&8).unwrap();
                match kind {
                    0 => list.owner = 99,
                    1 => list.id = None,
                    2 => list.id = Some(700),
                    3 => list.id = Some(901),
                    4 => list.window = None,
                    5 => list.window = Some(9), // Same PID/physical ID, different retained window.
                    _ => list.parent = None,
                }
                assert!(!prove(&tree, 42, 700, &0), "logical_host={logical_host} kind={kind}");
            }
            for role in ["AXWebArea", "AXTable", "AXIncrementor", "AXApplication", "AXPopover"] {
                let mut tree = inner_list(logical_host);
                tree.nodes.get_mut(&1).unwrap().role = role;
                assert!(!prove(&tree, 42, 700, &0), "inner boundary {role}");
            }
            let mut tree = inner_list(logical_host);
            tree.nodes.insert(10, tree.nodes[&2].clone());
            tree.nodes.get_mut(&10).unwrap().identity = 10;
            tree.nodes.get_mut(&8).unwrap().window = Some(10);
            assert!(!prove(&tree, 42, 700, &0), "same-ID sibling popup is not the retained popup");
        }
    }

    #[test]
    fn inner_list_requires_unique_reciprocal_edges_and_existing_bounds() {
        for logical_host in [false, true] {
            for parent in [1, 8, 2] {
                for duplicate in [false, true] {
                    let mut tree = inner_list(logical_host);
                    let node = tree.nodes.get_mut(&parent).unwrap();
                    if duplicate { node.children.push(node.children[0]); } else { node.children.clear(); }
                    assert!(!prove(&tree, 42, 700, &0), "parent={parent} duplicate={duplicate}");
                }
            }
            let mut tree = inner_list(logical_host);
            tree.nodes.get_mut(&8).unwrap().children = vec![1; MAX_CHILDREN as usize + 1];
            assert!(!prove(&tree, 42, 700, &0));
            let mut tree = inner_list(logical_host);
            tree.nodes.get_mut(&8).unwrap().parent = Some(1);
            tree.nodes.get_mut(&1).unwrap().children.push(8);
            assert!(!prove(&tree, 42, 700, &0), "cycle before popup");
            let tree = inner_list(logical_host);
            tree.budget.set(0);
            assert!(!prove(&tree, 42, 700, &0));
            let mut tree = inner_list(logical_host);
            tree.reattach = true;
            assert!(!prove(&tree, 42, 700, &0), "final popup attachment changed");
            let mut tree = inner_list(logical_host);
            tree.budget.set(1000);
            tree.nodes.get_mut(&1).unwrap().parent = Some(10);
            let last = 10 + MAX_DEPTH as u32;
            tree.nodes.get_mut(&8).unwrap().children = vec![last];
            for node in 10..=last {
                tree.nodes.insert(node, Node {
                    identity: node, role: "AXGroup", owner: 42, window: Some(6), id: Some(900),
                    parent: Some(if node == last { 8 } else { node + 1 }),
                    children: vec![if node == 10 { 1 } else { node - 1 }],
                });
            }
            assert!(!prove(&tree, 42, 700, &0), "existing depth bound");
        }
    }

    // Arm only after the full walk has accepted the inner path and reached
    // the last outer parent. This exercises the final retained-path check,
    // not a failed first lookup or initial list qualification.
    struct LateInnerChange {
        tree: Tree,
        field: &'static str,
        armed: Cell<bool>,
        late_reads: Cell<usize>,
        unique_reads: Cell<usize>,
    }
    impl LateInnerChange {
        fn changed(&self, field: &str) -> bool {
            let changed = self.armed.get() && self.field == field;
            if changed { self.late_reads.set(self.late_reads.get() + 1); }
            changed
        }
    }
    impl PopoverTree for LateInnerChange {
        type Node = u32;
        fn role(&self, node: &u32) -> Option<String> {
            if (*node == 8 && self.changed("role")) || (*node == 1 && self.changed("prefix_role")) {
                Some("AXGroup".into())
            } else if *node == 8 && self.changed("role_to_list") {
                Some("AXList".into())
            } else if *node == 8 && self.changed("role_missing") {
                None
            } else { self.tree.role(node) }
        }
        fn owner(&self, node: &u32) -> Option<i32> {
            if *node == 8 && self.changed("owner") { None } else { self.tree.owner(node) }
        }
        fn window(&self, node: &u32) -> Option<u32> {
            // Popup and host are each ordinarily allowed, but switching the
            // retained logical window after qualification must still refuse.
            if *node == 8 && self.changed("window") { Some(2) } else { self.tree.window(node) }
        }
        fn window_id(&self, node: &u32) -> Option<u32> {
            if *node == 8 && self.changed("id") { Some(700) } else { self.tree.window_id(node) }
        }
        fn parent(&self, node: &u32) -> Option<u32> {
            if *node == 5 { self.armed.set(true); }
            if (*node == 8 && self.changed("parent")) || (*node == 1 && self.changed("prefix_parent")) {
                None
            } else { self.tree.parent(node) }
        }
        fn contains_child(&self, parent: &u32, child: &u32) -> bool {
            self.tree.contains_child(parent, child)
        }
        fn contains_unique_child(&self, parent: &u32, child: &u32) -> bool {
            self.unique_reads.set(self.unique_reads.get() + 1);
            if *parent == 8 && self.changed("deadline") { self.tree.budget.set(0); }
            !(*parent == 8 && self.changed("children")) && self.tree.contains_unique_child(parent, child)
        }
        fn same(&self, a: &u32, b: &u32) -> bool { self.tree.same(a, b) }
        fn within_budget(&self) -> bool { self.tree.within_budget() }
        fn visible_menu_window(&self, node: &u32, pid: i32) -> Option<u32> {
            self.tree.visible_menu_window(node, pid)
        }
    }

    #[test]
    fn inner_list_revalidates_retained_facts_after_the_successful_walk() {
        for logical_host in [false, true] {
            for field in ["role", "owner", "window", "id", "parent", "children", "deadline", "prefix_role", "prefix_parent"] {
                let tree = LateInnerChange { tree: inner_list(logical_host), field,
                    armed: Cell::new(false), late_reads: Cell::new(0), unique_reads: Cell::new(0) };
                assert_eq!(prove_checked(&tree, 42, 700, &0), Err("attachment_changed"), "{field}");
                assert!(tree.armed.get());
                assert!(tree.late_reads.get() > 0, "late {field} must actually be read");
                assert!(tree.unique_reads.get() >= 2, "must enter final inner-path proof");
            }
        }
    }

    #[test]
    fn inner_list_revalidation_does_not_run_on_legacy_routes() {
        for legacy in [pages(), wrapped_toolbar_popover()] {
            let tree = LateInnerChange { tree: legacy, field: "none",
                armed: Cell::new(false), late_reads: Cell::new(0), unique_reads: Cell::new(0) };
            assert!(prove(&tree, 42, 700, &0));
            assert_eq!(tree.unique_reads.get(), 0);
            assert_eq!(tree.late_reads.get(), 0);
        }
    }

    fn tab_group_host(logical_host: bool, with_inner_list: bool) -> Tree {
        let mut tree = if with_inner_list { inner_list(logical_host) } else { wrapped_toolbar_popover() };
        tree.nodes.get_mut(&0).unwrap().window = Some(if logical_host { 6 } else { 2 });
        // Exact native outer shape: popup -> button -> tab group -> split -> host.
        tree.nodes.get_mut(&4).unwrap().role = "AXTabGroup";
        tree.budget.set(500);
        tree
    }

    fn inner_structural_chain(logical_host: bool) -> Tree {
        // Complete observed ten-node chain, with normalized IDs:
        // CheckBox(0) -> CheckBox(1) -> List(10) -> List(11) -> Unknown(8)
        // -> Popover(2) -> Button(3) -> TabGroup(4) -> SplitGroup(5) -> Window(6).
        // The first six share the popup physical ID; all non-host AXWindow
        // attributes name the exact host in the observed logical_host variant.
        let mut tree = tab_group_host(logical_host, true);
        tree.nodes.get_mut(&1).unwrap().parent = Some(10);
        tree.nodes.get_mut(&8).unwrap().role = "AXUnknown";
        tree.nodes.get_mut(&8).unwrap().children = vec![11];
        for (node, parent, child) in [(10, 11, 1), (11, 8, 10)] {
            tree.nodes.insert(node, Node {
                identity: node, role: "AXList", owner: 42,
                window: Some(6), id: Some(900), parent: Some(parent), children: vec![child],
            });
        }
        tree
    }

    #[test]
    fn inner_structural_proves_complete_native_chain_and_qualified_unknown_prefix() {
        for logical_host in [false, true] {
            for logical_window in [2, 6] {
                let mut tree = inner_structural_chain(logical_host);
                for node in [8, 10, 11] {
                    tree.nodes.get_mut(&node).unwrap().window = Some(logical_window);
                }
                assert_eq!(prove_checked(&tree, 42, 700, &0), Ok(()));
            }
            // This former blanket-negative node was already fully qualified:
            // same popup physical ID, exact logical host, unique retained edges.
            let mut tree = inner_list(logical_host);
            tree.nodes.get_mut(&1).unwrap().role = "AXUnknown";
            assert_eq!(prove_checked(&tree, 42, 700, &0), Ok(()));
            let mut tree = inner_structural_chain(logical_host);
            for node in [10, 11] { tree.nodes.get_mut(&node).unwrap().role = "AXUnknown"; }
            assert_eq!(prove_checked(&tree, 42, 700, &0), Ok(()), "no List is needed to trigger revalidation");
        }
        let mut tree = inner_structural_chain(true);
        tree.nodes.insert(9000, tree.nodes[&6].clone());
        tree.nodes.get_mut(&8).unwrap().window = Some(9000);
        assert!(prove(&tree, 42, 700, &0), "CF-equivalent retained host proxy");
    }

    #[test]
    fn inner_structural_requires_exact_physical_logical_owner_and_real_role() {
        for logical_host in [false, true] {
            for node in [8, 10, 11] {
                for kind in 0..9 {
                    let mut tree = inner_structural_chain(logical_host);
                    let source = if kind == 8 { 2 } else { 6 };
                    tree.nodes.insert(9000, tree.nodes[&source].clone());
                    tree.nodes.get_mut(&9000).unwrap().identity = 9000;
                    let entry = tree.nodes.get_mut(&node).unwrap();
                    match kind {
                        0 => entry.owner = 99,
                        1 => entry.id = None,
                        2 => entry.id = Some(700),
                        3 => entry.id = Some(901),
                        4 => entry.window = None,
                        5 => entry.window = Some(9),
                        6 => entry.parent = None,
                        _ => entry.window = Some(9000),
                    }
                    assert!(!prove(&tree, 42, 700, &0), "node={node} kind={kind}");
                }
            }
            let tree = LateInnerChange { tree: inner_structural_chain(logical_host), field: "role_missing",
                armed: Cell::new(true), late_reads: Cell::new(0), unique_reads: Cell::new(0) };
            assert!(!prove(&tree, 42, 700, &0), "missing AXRole is not literal AXUnknown");
            assert!(tree.late_reads.get() > 0);
        }
    }

    #[test]
    fn inner_structural_keeps_target_outer_web_and_container_boundaries() {
        assert!(!native_control_role(Some("AXUnknown")));
        assert!(!container_role("AXUnknown"));
        assert!(!host_collection_role("AXUnknown"));
        for action in ["press", "click", "pick", "show_menu", "confirm", "cancel"] {
            assert_eq!(advertised_action(Some("AXUnknown"), action,
                &["AXPress".into(), "AXPick".into(), "AXShowMenu".into(), "AXConfirm".into(), "AXCancel".into()]), None);
        }
        for logical_host in [false, true] {
            assert!(!prove(&inner_structural_chain(logical_host), 42, 700, &8), "structure is not a target");
            for node in [2, 3, 4, 5, 6] {
                let mut tree = inner_structural_chain(logical_host);
                tree.nodes.get_mut(&node).unwrap().role = "AXUnknown";
                assert!(!prove(&tree, 42, 700, &0), "Unknown cannot replace popup/host or an outer node {node}");
            }
            for role in ["AXWebArea", "AXTable", "AXIncrementor", "AXApplication", "AXTabGroup", "AXOutline", "AXPopover"] {
                let mut tree = inner_structural_chain(logical_host);
                tree.nodes.get_mut(&8).unwrap().role = role;
                assert!(!prove(&tree, 42, 700, &0), "inner boundary {role}");
            }
        }
    }

    #[test]
    fn inner_structural_keeps_unique_edges_cycle_child_depth_and_deadline_limits() {
        for logical_host in [false, true] {
            for parent in [1, 10, 11, 8, 2] {
                for duplicate in [false, true] {
                    let mut tree = inner_structural_chain(logical_host);
                    let entry = tree.nodes.get_mut(&parent).unwrap();
                    if duplicate { entry.children.push(entry.children[0]); } else { entry.children.clear(); }
                    assert!(!prove(&tree, 42, 700, &0), "parent={parent} duplicate={duplicate}");
                }
            }
            let mut tree = inner_structural_chain(logical_host);
            tree.nodes.get_mut(&8).unwrap().parent = Some(1);
            tree.nodes.get_mut(&1).unwrap().children.push(8);
            assert!(!prove(&tree, 42, 700, &0), "reciprocal cycle");
            let tree = inner_structural_chain(logical_host);
            tree.budget.set(0);
            assert!(!prove(&tree, 42, 700, &0));
            for extra in [MAX_DEPTH - 10, MAX_DEPTH - 9] {
                let mut tree = inner_structural_chain(logical_host);
                tree.budget.set(2000);
                tree.nodes.get_mut(&8).unwrap().parent = Some(100);
                let last = 100 + extra as u32 - 1;
                tree.nodes.get_mut(&2).unwrap().children = vec![last];
                for node in 100..=last {
                    tree.nodes.insert(node, Node {
                        identity: node, role: "AXUnknown", owner: 42,
                        window: Some(6), id: Some(900),
                        parent: Some(if node == last { 2 } else { node + 1 }),
                        children: vec![if node == 100 { 8 } else { node - 1 }],
                    });
                }
                let expected = if extra == MAX_DEPTH - 10 { Ok(()) } else { Err("ancestry_depth_limit") };
                assert_eq!(prove_checked(&tree, 42, 700, &0), expected, "total depth {}", extra + 10);
            }
            for count in [MAX_CHILDREN as usize, MAX_CHILDREN as usize + 1] {
                let mut tree = inner_structural_chain(logical_host);
                for index in 1..count {
                    let node = 1000 + index as u32;
                    let mut sibling = tree.nodes[&11].clone();
                    sibling.identity = node;
                    tree.nodes.insert(node, sibling);
                    tree.nodes.get_mut(&8).unwrap().children.push(node);
                }
                assert_eq!(prove(&tree, 42, 700, &0), count == MAX_CHILDREN as usize, "children={count}");
            }
        }
    }

    #[test]
    fn inner_structural_revalidates_unknown_and_prefix_after_the_complete_walk() {
        for logical_host in [false, true] {
            for field in ["role", "role_to_list", "role_missing", "owner", "window", "id", "parent", "children", "deadline", "prefix_role", "prefix_parent"] {
                let tree = LateInnerChange { tree: inner_structural_chain(logical_host), field,
                    armed: Cell::new(false), late_reads: Cell::new(0), unique_reads: Cell::new(0) };
                assert_eq!(prove_checked(&tree, 42, 700, &0), Err("attachment_changed"), "late {field}");
                assert!(tree.armed.get());
                assert!(tree.late_reads.get() > 0, "late {field} must be read");
                assert!(tree.unique_reads.get() >= 2);
            }
        }
    }

    #[test]
    fn inner_structural_preserves_outer_revalidation_and_legacy_query_boundary() {
        for logical_host in [false, true] {
            for field in ["role", "owner", "window", "id", "parent", "children"] {
                let node = if field == "children" { 5 } else { 4 };
                let tree = ChangingHost::new(inner_structural_chain(logical_host), node, field);
                assert_eq!(prove_checked(&tree, 42, 700, &0), Err("attachment_changed"), "outer {field}");
                assert!(tree.reads.get() >= 2);
                assert!(tree.unique_reads.get() > 0);
            }
        }
        for legacy in [pages(), wrapped_toolbar_popover()] {
            let tree = LateInnerChange { tree: legacy, field: "role_missing",
                armed: Cell::new(true), late_reads: Cell::new(0), unique_reads: Cell::new(0) };
            assert!(prove(&tree, 42, 700, &0));
            assert_eq!(tree.unique_reads.get(), 0, "legacy-only route never enters structural revalidation");
            assert_eq!(tree.late_reads.get(), 0);
        }
    }

    #[test]
    fn host_tab_group_proves_outer_chain_with_and_without_inner_list() {
        for logical_host in [false, true] {
            for with_inner_list in [false, true] {
                let tree = tab_group_host(logical_host, with_inner_list);
                assert_eq!(prove_checked(&tree, 42, 700, &0), Ok(()));
                assert_eq!(prove_checked(&tree, 42, 700, &2), Ok(()), "popup root");
                assert!(!prove(&tree, 42, 701, &0));
            }
        }
    }

    #[test]
    fn host_tab_group_does_not_widen_inner_roles_actions_or_host_boundaries() {
        assert!(!container_role("AXTabGroup"));
        assert!(!native_control_role(Some("AXTabGroup")));
        for action in ["press", "click", "show_menu", "confirm", "cancel"] {
            assert_eq!(advertised_action(Some("AXTabGroup"), action,
                &["AXPress".into(), "AXShowMenu".into(), "AXConfirm".into(), "AXCancel".into()]), None);
        }
        for logical_host in [false, true] {
            let mut tree = tab_group_host(logical_host, false);
            assert!(!prove(&tree, 42, 700, &4), "tab group is not an action target");
            tree.nodes.get_mut(&1).unwrap().role = "AXTabGroup";
            assert!(!prove(&tree, 42, 700, &0), "tab group inside popup");
            for role in ["AXList", "AXWebArea", "AXTable", "AXWindow", "AXPopover", "AXUnknown"] {
                let mut tree = tab_group_host(logical_host, true);
                tree.nodes.get_mut(&4).unwrap().role = role;
                assert!(!prove(&tree, 42, 700, &0), "outer boundary {role}");
            }
        }
    }

    #[test]
    fn host_tab_group_requires_exact_host_facts_and_unique_reciprocal_edges() {
        for logical_host in [false, true] {
            for node in [3, 4, 5] {
                for kind in 0..5 {
                    let mut tree = tab_group_host(logical_host, true);
                    tree.nodes.insert(9, tree.nodes[&6].clone());
                    tree.nodes.get_mut(&9).unwrap().identity = 9;
                    let entry = tree.nodes.get_mut(&node).unwrap();
                    match kind {
                        0 => entry.owner = 99,
                        1 => entry.id = None,
                        2 => entry.id = Some(900),
                        3 => entry.window = None,
                        _ => entry.window = Some(9), // Same-ID sibling is not the retained host.
                    }
                    assert!(!prove(&tree, 42, 700, &0), "node={node} kind={kind}");
                }
            }
            for parent in 3..=6 {
                for duplicate in [false, true] {
                    let mut tree = tab_group_host(logical_host, true);
                    let entry = tree.nodes.get_mut(&parent).unwrap();
                    if duplicate { entry.children.push(parent - 1); } else { entry.children.clear(); }
                    assert!(!prove(&tree, 42, 700, &0), "parent={parent} duplicate={duplicate}");
                }
            }
            let mut tree = tab_group_host(logical_host, true);
            tree.nodes.get_mut(&4).unwrap().parent = Some(6);
            assert!(!prove(&tree, 42, 700, &0), "one-way reparent");
            let tree = ChangingHost::new(tab_group_host(logical_host, false), 4, "deadline");
            assert_eq!(prove_checked(&tree, 42, 700, &0), Err("attachment_changed"));
            assert_eq!(tree.unique_reads.get(), 1, "existing final proof deadline");
        }
    }

    #[test]
    fn host_tab_group_revalidates_live_identity_roles_and_edges_at_end() {
        for logical_host in [false, true] {
            for with_inner_list in [false, true] {
                for field in ["role", "owner", "window", "id", "parent", "children"] {
                    let node = if field == "children" { 5 } else { 4 };
                    let tree = ChangingHost::new(tab_group_host(logical_host, with_inner_list), node, field);
                    assert_eq!(prove_checked(&tree, 42, 700, &0), Err("attachment_changed"), "late {field}");
                    assert!(tree.reads.get() >= 2, "late {field} re-read must occur");
                    assert!(tree.unique_reads.get() > 0, "must reach final retained proof");
                }
            }
        }
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
