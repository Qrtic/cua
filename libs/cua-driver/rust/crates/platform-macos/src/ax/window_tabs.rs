//! Read-only navigation hints for inactive native macOS window tabs.
//!
//! An inactive tab can have a CGWindowID and screenshot but no AXWindow. Its
//! selector belongs to the selected sibling, never to the requested window.
//! Public hints are only title-match advice. The private retained module below
//! proves one completed tab switch for the existing order guard; neither path
//! mints elements, changes selection or performs input.

use super::bindings::*;
use core_foundation::base::{CFRelease, CFTypeRef};
use serde::Serialize;
use std::time::{Duration, Instant};

#[derive(Debug, Serialize, PartialEq, Eq)]
pub(crate) struct WindowTabHint {
    pub(crate) pid: i32,
    pub(crate) target_window_id: u32,
    pub(crate) host_window_id: u32,
    pub(crate) tab_label: String,
    pub(crate) match_kind: &'static str,
}

#[derive(Clone)]
struct TabHost {
    pid: i32,
    window_id: u32,
    title: String,
    tabs: Vec<(String, bool)>,
}

fn choose_hint(pid: i32, target_id: u32, title: &str, hosts: &[TabHost]) -> Option<WindowTabHint> {
    if pid <= 0 || target_id == 0 || title.trim().is_empty() || title.len() > 1024 {
        return None;
    }
    let mut matches = Vec::new();
    for host in hosts {
        if host.pid != pid || host.window_id == 0 || host.window_id == target_id {
            continue;
        }
        // A top-level tab group must identify its selected sibling, rather
        // than merely containing a similarly named application content tab.
        let selected: Vec<_> = host.tabs.iter().filter(|(_, selected)| *selected).collect();
        if selected.len() != 1 || selected[0].0 != host.title || host.title == title {
            continue;
        }
        for (label, selected) in &host.tabs {
            if label == title && !selected {
                matches.push(host.window_id);
            }
        }
    }
    if matches.len() != 1 {
        return None;
    }
    Some(WindowTabHint {
        pid,
        target_window_id: target_id,
        host_window_id: matches[0],
        tab_label: title.to_owned(),
        match_kind: "unique_exact_title",
    })
}

struct OwnedAx(AXUIElementRef);
impl Drop for OwnedAx {
    fn drop(&mut self) {
        unsafe { CFRelease(self.0 as CFTypeRef) }
    }
}

unsafe fn owned_children(element: AXUIElementRef) -> Option<Vec<OwnedAx>> {
    let children: Vec<_> = copy_children(element).into_iter().map(OwnedAx).collect();
    (children.len() <= 64).then_some(children)
}

unsafe fn prepare_node(node: AXUIElementRef, pid: i32) -> bool {
    let mut owner = 0;
    AXUIElementSetMessagingTimeout(node, 0.05) == kAXErrorSuccess
        && AXUIElementGetPid(node, &mut owner) == kAXErrorSuccess
        && owner == pid
}

/// Best-effort bounded inspection of immediate native tab groups only. Never
/// traverses web content, activates an app, or treats a title as input authority.
pub(crate) fn find_hint(pid: i32, target_id: u32) -> Option<WindowTabHint> {
    let deadline = Instant::now() + Duration::from_millis(350);
    let inventory = crate::windows::all_windows_with_space_snapshot();
    if !inventory.succeeded {
        return None;
    }
    let target = inventory
        .windows
        .iter()
        .find(|w| w.pid == pid && w.window_id == target_id)?;
    if target.is_on_screen || target.title.trim().is_empty() {
        return None;
    }
    unsafe {
        let ptr = AXUIElementCreateApplication(pid);
        if ptr.is_null() {
            return None;
        }
        let app = OwnedAx(ptr);
        if !prepare_node(app.0, pid) {
            return None;
        }
        let snapshot = try_copy_ax_windows(app.0).ok()?;
        let windows: Vec<_> = snapshot.windows.into_iter().map(OwnedAx).collect();
        if !snapshot.complete || windows.len() > 32 {
            return None;
        }
        let mut hosts = Vec::new();
        for window in &windows {
            if Instant::now() >= deadline {
                return None;
            }
            if !prepare_node(window.0, pid) {
                return None;
            }
            let Some(id) = ax_get_window_id(window.0) else {
                continue;
            };
            // Do not reinterpret a target which appeared while we were reading.
            if id == target_id {
                return None;
            }
            let Some(info) = inventory
                .windows
                .iter()
                .find(|w| w.pid == pid && w.window_id == id && w.is_on_screen && w.layer == 0)
            else {
                continue;
            };
            if copy_string_attr(window.0, "AXRole").as_deref() != Some("AXWindow") {
                continue;
            }
            for child in owned_children(window.0)? {
                if Instant::now() >= deadline {
                    return None;
                }
                if !prepare_node(child.0, pid) {
                    return None;
                }
                if copy_string_attr(child.0, "AXRole").as_deref() != Some("AXTabGroup") {
                    continue;
                }
                let mut tabs = Vec::new();
                for tab in owned_children(child.0)? {
                    if Instant::now() >= deadline {
                        return None;
                    }
                    if !prepare_node(tab.0, pid) {
                        return None;
                    }
                    if copy_string_attr(tab.0, "AXRole").as_deref() != Some("AXRadioButton") {
                        continue;
                    }
                    if !copy_action_names(tab.0)
                        .iter()
                        .any(|name| name == "AXPress")
                    {
                        continue;
                    }
                    if let Some(label) = copy_string_attr(tab.0, "AXTitle") {
                        // AppKit native radio tabs expose CFBoolean here;
                        // numeric-only reads discard the selected host tab.
                        let selected = copy_bool_attr(tab.0, "AXValue") == Some(true)
                            || copy_bool_attr(tab.0, "AXSelected") == Some(true);
                        tabs.push((label, selected));
                    }
                }
                hosts.push(TabHost {
                    pid,
                    window_id: id,
                    title: info.title.clone(),
                    tabs,
                });
            }
        }
        if Instant::now() >= deadline {
            return None;
        }
        choose_hint(pid, target_id, &target.title, &hosts)
    }
}

/// Private ordering evidence, separate from title-based navigation advice.
/// All retained AX objects stay on the caller's AX thread. Only Destination
/// (IDs plus the original lifetime/deadline) may enter the shared order guard.
pub(crate) mod retained {
    use super::*;
    use crate::ax::enablement::{process_start_stamp, ProcessStartStamp};
    use core_foundation::{
        array::CFArray,
        base::{CFEqual, CFGetTypeID, CFRetain, TCFType},
        boolean::CFBoolean,
        number::CFNumber,
        string::CFString,
    };
    use std::cell::Cell;

    #[derive(Clone, Copy)]
    pub(crate) struct Scope {
        pub(crate) pid: i32,
        pub(crate) source: u32,
        pub(crate) start: ProcessStartStamp,
        pub(crate) deadline: Instant,
    }
    pub(crate) struct Destination {
        scope: Scope,
        id: u32,
    }
    impl Destination {
        pub(crate) fn parts(&self) -> (i32, u32, u32, ProcessStartStamp, Instant) {
            (
                self.scope.pid,
                self.scope.source,
                self.id,
                self.scope.start,
                self.scope.deadline,
            )
        }
    }

    trait Tree {
        type Node: Clone;
        fn current(&self, scope: Scope) -> bool;
        fn same(&self, a: &Self::Node, b: &Self::Node) -> bool;
        fn owner(&self, n: &Self::Node) -> Option<i32>;
        fn role(&self, n: &Self::Node) -> Option<String>;
        fn id(&self, n: &Self::Node) -> Option<u32>;
        fn relation(&self, n: &Self::Node, attr: &str) -> Option<Self::Node>;
        fn children(&self, n: &Self::Node) -> Option<Vec<Self::Node>>;
        fn selected(&self, n: &Self::Node) -> Option<bool>;
        fn press_allowed(&self, n: &Self::Node) -> bool;
        fn ordinary_window(&self, n: &Self::Node) -> bool;
    }
    struct State<N> {
        group: N,
        window: N,
        id: u32,
        radios: Vec<(N, bool)>,
    }
    struct Proof<N> {
        radio: N,
        before: State<N>,
        scope: Scope,
    }

    fn unique<T: Tree>(t: &T, nodes: &[T::Node]) -> bool {
        nodes
            .iter()
            .enumerate()
            .all(|(i, n)| !nodes[..i].iter().any(|p| t.same(p, n)))
    }
    fn state<T: Tree>(t: &T, radio: &T::Node, scope: Scope) -> Option<State<T::Node>> {
        if !t.current(scope)
            || t.role(radio).as_deref() != Some("AXRadioButton")
            || !t.press_allowed(radio)
        {
            return None;
        }
        let group = t.relation(radio, "AXParent")?;
        let window = t.relation(&group, "AXParent")?;
        if t.same(radio, &group)
            || t.same(&group, &window)
            || t.same(radio, &window)
            || t.role(&group).as_deref() != Some("AXTabGroup")
            || !t.ordinary_window(&window)
        {
            return None;
        }
        let id = t.id(&window)?;
        let window_children = t.children(&window)?;
        if id == 0
            || !unique(t, &window_children)
            || window_children.iter().filter(|n| t.same(n, &group)).count() != 1
        {
            return None;
        }
        for n in [radio, &group, &window] {
            if t.owner(n) != Some(scope.pid) || t.id(n) != Some(id) {
                return None;
            }
            if !t.same(n, &window) {
                for attr in ["AXWindow", "AXTopLevelUIElement"] {
                    if !t.relation(n, attr).is_some_and(|w| t.same(&w, &window)) {
                        return None;
                    }
                }
            }
        }
        let children = t.children(&group)?;
        if children.is_empty()
            || children.len() > 64
            || !unique(t, &children)
            || children.iter().filter(|n| t.same(n, radio)).count() != 1
        {
            return None;
        }
        let mut radios = Vec::new();
        for n in children {
            // Classify EVERY direct child on EVERY pass. A replaced accessory
            // is not assumed non-radio from an earlier observation.
            if !t.current(scope)
                || t.owner(&n) != Some(scope.pid)
                || !t
                    .relation(&n, "AXParent")
                    .is_some_and(|p| t.same(&p, &group))
            {
                return None;
            }
            let role = t.role(&n)?;
            if role == "AXUnknown" {
                return None;
            }
            if role == "AXRadioButton" {
                if t.id(&n) != Some(id) {
                    return None;
                }
                for attr in ["AXWindow", "AXTopLevelUIElement"] {
                    if !t.relation(&n, attr).is_some_and(|w| t.same(&w, &window)) {
                        return None;
                    }
                }
                radios.push((n.clone(), t.selected(&n)?));
            }
        }
        if radios.len() < 2
            || radios.len() > 16
            || radios.iter().filter(|(_, v)| *v).count() != 1
            || !t.current(scope)
        {
            return None;
        }
        Some(State {
            group,
            window,
            id,
            radios,
        })
    }
    fn same_state<T: Tree>(t: &T, a: &State<T::Node>, b: &State<T::Node>, values: bool) -> bool {
        t.same(&a.group, &b.group)
            && (!values || (t.same(&a.window, &b.window) && a.id == b.id))
            && a.radios.len() == b.radios.len()
            && a.radios.iter().all(|(n, v)| {
                b.radios
                    .iter()
                    .any(|(m, w)| t.same(n, m) && (!values || v == w))
            })
    }
    fn capture<T: Tree>(t: &T, radio: T::Node, scope: Scope) -> Option<Proof<T::Node>> {
        let before = state(t, &radio, scope)?;
        if before.id != scope.source || before.radios.iter().find(|(n, _)| t.same(n, &radio))?.1 {
            return None;
        }
        let second = state(t, &radio, scope)?;
        (same_state(t, &before, &second, true) && t.current(scope)).then_some(Proof {
            radio,
            before,
            scope,
        })
    }
    fn confirm<T: Tree>(t: &T, proof: Proof<T::Node>, ax_status: AXError) -> Option<Destination> {
        if ax_status != kAXErrorSuccess {
            return None;
        }
        let after = state(t, &proof.radio, proof.scope)?;
        if after.id == proof.scope.source
            || t.same(&after.window, &proof.before.window)
            || !same_state(t, &proof.before, &after, false)
            || !after
                .radios
                .iter()
                .find(|(n, _)| t.same(n, &proof.radio))?
                .1
        {
            return None;
        }
        let second = state(t, &proof.radio, proof.scope)?;
        if !same_state(t, &after, &second, true)
            || t.owner(&proof.before.window) != Some(proof.scope.pid)
            || t.role(&proof.before.window).as_deref() != Some("AXWindow")
            || t.id(&proof.before.window) != Some(proof.scope.source)
            || !t.current(proof.scope)
        {
            return None;
        }
        Some(Destination {
            scope: proof.scope,
            id: after.id,
        })
    }

    impl Clone for OwnedAx {
        fn clone(&self) -> Self {
            unsafe { CFRetain(self.0.cast()) };
            Self(self.0)
        }
    }
    struct Native {
        scope: Scope,
        reads: Cell<usize>,
        action: AXUIElementRef,
    }
    impl Native {
        fn read<R>(&self, n: &OwnedAx, f: impl FnOnce(AXUIElementRef) -> Option<R>) -> Option<R> {
            if self.reads.get() >= 512 || !self.current(self.scope) {
                return None;
            }
            self.reads.set(self.reads.get() + 1);
            let remaining = self
                .scope
                .deadline
                .saturating_duration_since(Instant::now())
                .as_secs_f32();
            if remaining <= 0.0 {
                return None;
            }
            // Do not change the actual action object's AXPress response timeout.
            // Its existing bounded timeout may outlast the remaining proof
            // budget; the result is still rejected after that read returns.
            if unsafe { CFEqual(n.0.cast(), self.action.cast()) } == 0
                && unsafe { AXUIElementSetMessagingTimeout(n.0, remaining.min(0.05)) }
                    != kAXErrorSuccess
            {
                return None;
            }
            let result = f(n.0);
            self.current(self.scope).then_some(result).flatten()
        }
    }
    impl Tree for Native {
        type Node = OwnedAx;
        fn current(&self, s: Scope) -> bool {
            Instant::now() < s.deadline
                && crate::foreground_activity::check_request().is_ok()
                && process_start_stamp(s.pid) == Some(s.start)
        }
        fn same(&self, a: &OwnedAx, b: &OwnedAx) -> bool {
            unsafe { CFEqual(a.0.cast(), b.0.cast()) != 0 }
        }
        fn owner(&self, n: &OwnedAx) -> Option<i32> {
            self.read(n, |p| {
                let mut pid = 0;
                (unsafe { AXUIElementGetPid(p, &mut pid) } == kAXErrorSuccess).then_some(pid)
            })
        }
        fn role(&self, n: &OwnedAx) -> Option<String> {
            self.read(n, |p| unsafe { copy_string_attr(p, "AXRole") })
                .filter(|s| !s.is_empty() && s.len() <= 128)
        }
        fn id(&self, n: &OwnedAx) -> Option<u32> {
            self.read(n, |p| unsafe { ax_get_window_id(p) })
        }
        fn relation(&self, n: &OwnedAx, attr: &str) -> Option<OwnedAx> {
            self.read(n, |p| unsafe { copy_element_attr(p, attr) }.map(OwnedAx))
        }
        fn children(&self, n: &OwnedAx) -> Option<Vec<OwnedAx>> {
            self.read(n, |p| unsafe {
                let attr = CFString::new("AXChildren");
                let mut value: CFTypeRef = std::ptr::null();
                let error =
                    AXUIElementCopyAttributeValue(p, attr.as_concrete_TypeRef(), &mut value);
                if error != kAXErrorSuccess || value.is_null() {
                    if !value.is_null() {
                        CFRelease(value);
                    }
                    return None;
                }
                if CFGetTypeID(value) != CFArray::<CFTypeRef>::type_id() {
                    CFRelease(value);
                    return None;
                }
                let array = CFArray::<CFTypeRef>::wrap_under_create_rule(value.cast());
                if array.len() > 64 {
                    return None;
                }
                (0..array.len())
                    .map(|i| {
                        let value = *array.get(i)?;
                        if CFGetTypeID(value) != AXUIElementGetTypeID() {
                            return None;
                        }
                        CFRetain(value);
                        Some(OwnedAx(value as AXUIElementRef))
                    })
                    .collect()
            })
        }
        fn selected(&self, n: &OwnedAx) -> Option<bool> {
            self.read(n, |p| unsafe {
                let attr = CFString::new("AXValue");
                let mut value: CFTypeRef = std::ptr::null();
                let error =
                    AXUIElementCopyAttributeValue(p, attr.as_concrete_TypeRef(), &mut value);
                if error != kAXErrorSuccess || value.is_null() {
                    if !value.is_null() {
                        CFRelease(value);
                    }
                    return None;
                }
                if CFGetTypeID(value) == CFBoolean::type_id() {
                    return Some(CFBoolean::wrap_under_create_rule(value.cast()).into());
                }
                if CFGetTypeID(value) == CFNumber::type_id() {
                    return match CFNumber::wrap_under_create_rule(value.cast()).to_f64()? {
                        0.0 => Some(false),
                        1.0 => Some(true),
                        _ => None,
                    };
                }
                CFRelease(value);
                None
            })
        }
        fn press_allowed(&self, n: &OwnedAx) -> bool {
            // Unsupported AXEnabled is not an enabled=true claim. Preserve the
            // existing AX action eligibility; only its later success can confirm.
            self.read(n, |p| match unsafe { try_copy_bool_attr(p, "AXEnabled") } {
                Ok(true) | Err(kAXErrorAttributeUnsupported) => Some(true),
                _ => None,
            }) == Some(true)
                && self.read(n, |p| {
                    Some(
                        unsafe { copy_action_names(p) }
                            .iter()
                            .any(|a| a == "AXPress"),
                    )
                }) == Some(true)
        }
        fn ordinary_window(&self, n: &OwnedAx) -> bool {
            self.role(n).as_deref() == Some("AXWindow")
                && self
                    .read(n, |p| unsafe { copy_string_attr(p, "AXSubrole") })
                    .as_deref()
                    == Some("AXStandardWindow")
                && self.read(n, |p| unsafe { copy_bool_attr(p, "AXMinimized") }) == Some(false)
                && self.read(n, |p| unsafe { copy_bool_attr(p, "AXModal") }) == Some(false)
        }
    }
    pub(crate) struct Pending {
        proof: Proof<OwnedAx>,
        native: Native,
    }
    impl Pending {
        /// Called only at the real, already authorized plain AXPress seam.
        pub(crate) fn capture(element: AXUIElementRef, scope: Scope) -> Option<Self> {
            if element.is_null() {
                return None;
            }
            let native = Native {
                scope,
                reads: Cell::new(0),
                action: element,
            };
            unsafe { CFRetain(element.cast()) };
            let proof = capture(&native, OwnedAx(element), scope)?;
            Some(Self { proof, native })
        }
        pub(crate) fn confirm(self, ax_status: AXError) -> Option<Destination> {
            confirm(&self.native, self.proof, ax_status)
        }
    }
    #[cfg(test)]
    mod tests {
        use super::*;
        use std::collections::HashMap;
        #[derive(Clone)]
        struct Node {
            role: Option<&'static str>,
            pid: i32,
            id: u32,
            parent: Option<usize>,
            window: Option<usize>,
            top: Option<usize>,
            children: Vec<usize>,
            value: Option<bool>,
            ordinary: bool,
            press: bool,
        }
        struct Fake {
            nodes: HashMap<usize, Node>,
            passes: Cell<usize>,
            late: Option<&'static str>,
            start: ProcessStartStamp,
            alive: bool,
        }
        fn scope() -> Scope {
            Scope {
                pid: 42,
                source: 10,
                start: (1, 2),
                deadline: Instant::now() + Duration::from_secs(5),
            }
        }
        impl Fake {
            fn new() -> Self {
                let mut nodes = HashMap::new();
                for (n, role, parent, children, value, id) in [
                    (0, "AXRadioButton", Some(1), vec![], Some(false), 10),
                    (1, "AXTabGroup", Some(2), vec![0, 3, 4], None, 10),
                    (2, "AXWindow", None, vec![1], None, 10),
                    (3, "AXRadioButton", Some(1), vec![], Some(true), 10),
                    (4, "AXButton", Some(1), vec![], None, 10),
                    (5, "AXWindow", None, vec![], None, 20),
                ] {
                    nodes.insert(
                        n,
                        Node {
                            role: Some(role),
                            pid: 42,
                            id,
                            parent,
                            children,
                            value,
                            window: Some(2),
                            top: Some(2),
                            ordinary: role == "AXWindow",
                            press: true,
                        },
                    );
                }
                Self {
                    nodes,
                    passes: Cell::new(0),
                    late: None,
                    start: (1, 2),
                    alive: true,
                }
            }
            fn switch(&mut self) {
                self.nodes.get_mut(&1).unwrap().parent = Some(5);
                self.nodes.get_mut(&2).unwrap().children.clear();
                self.nodes.get_mut(&5).unwrap().children = vec![1];
                for n in [0, 1, 3, 4] {
                    let x = self.nodes.get_mut(&n).unwrap();
                    x.id = 20;
                    x.window = Some(5);
                    x.top = Some(5);
                }
                self.nodes.get_mut(&0).unwrap().value = Some(true);
                self.nodes.get_mut(&3).unwrap().value = Some(false);
            }
            fn late(&self, fault: &str) -> bool {
                self.passes.get() >= 4 && self.late == Some(fault)
            }
        }
        impl Tree for Fake {
            type Node = usize;
            fn current(&self, s: Scope) -> bool {
                self.alive
                    && self.start == s.start
                    && Instant::now() < s.deadline
                    && !self.late("expired")
            }
            fn same(&self, a: &usize, b: &usize) -> bool {
                a == b
            }
            fn owner(&self, n: &usize) -> Option<i32> {
                if *n == 0 && self.late("owner") {
                    Some(99)
                } else {
                    self.nodes.get(n).map(|n| n.pid)
                }
            }
            fn role(&self, n: &usize) -> Option<String> {
                if *n == 1 && self.late("role") {
                    return Some("AXWebArea".into());
                }
                self.nodes.get(n)?.role.map(str::to_string)
            }
            fn id(&self, n: &usize) -> Option<u32> {
                if *n == 2 && self.late("source") {
                    Some(99)
                } else {
                    self.nodes.get(n).map(|n| n.id)
                }
            }
            fn relation(&self, n: &usize, attr: &str) -> Option<usize> {
                if *n == 0 && attr == "AXParent" && self.late("parent") {
                    return Some(2);
                }
                let n = self.nodes.get(n)?;
                match attr {
                    "AXParent" => n.parent,
                    "AXWindow" => n.window,
                    "AXTopLevelUIElement" => n.top,
                    _ => None,
                }
            }
            fn children(&self, n: &usize) -> Option<Vec<usize>> {
                self.nodes.get(n).map(|n| n.children.clone())
            }
            fn selected(&self, n: &usize) -> Option<bool> {
                if *n == 0 && self.late("selection") {
                    Some(false)
                } else {
                    self.nodes.get(n)?.value
                }
            }
            fn press_allowed(&self, n: &usize) -> bool {
                self.passes.set(self.passes.get() + 1);
                self.nodes[n].press
            }
            fn ordinary_window(&self, n: &usize) -> bool {
                self.nodes[n].ordinary && self.nodes[n].role == Some("AXWindow")
            }
        }
        fn switched_destination() -> Destination {
            let mut tree = Fake::new();
            let proof = capture(&tree, 0, scope()).unwrap();
            tree.switch();
            confirm(&tree, proof, kAXErrorSuccess).unwrap()
        }
        #[test]
        fn retained_tab_success_requires_real_press_and_same_radio_group() {
            let proof = switched_destination();
            assert_eq!(
                (proof.parts().0, proof.parts().1, proof.parts().2),
                (42, 10, 20)
            );
            let mut tree = Fake::new();
            let proof = capture(&tree, 0, scope()).unwrap();
            tree.switch();
            // An outer Ok produced by nearest-container fallback cannot stand
            // in for the actual AXPress status passed to this production seam.
            assert!(confirm(&tree, proof, kAXErrorFailure).is_none());
        }
        #[test]
        fn retained_tab_reclassifies_every_current_child_without_freezing_accessory_identity() {
            let mut tree = Fake::new();
            let proof = capture(&tree, 0, scope()).unwrap();
            tree.switch();
            let accessory = tree.nodes.remove(&4).unwrap();
            tree.nodes.insert(6, accessory);
            tree.nodes.get_mut(&1).unwrap().children = vec![0, 3, 6];
            assert!(confirm(&tree, proof, kAXErrorSuccess).is_some());
            for role in [None, Some("AXUnknown"), Some("AXRadioButton")] {
                let mut tree = Fake::new();
                let proof = capture(&tree, 0, scope()).unwrap();
                tree.switch();
                tree.nodes.get_mut(&4).unwrap().role = role;
                assert!(confirm(&tree, proof, kAXErrorSuccess).is_none());
            }
        }
        #[test]
        fn retained_tab_refuses_missing_selection_and_incomplete_or_duplicate_edges() {
            for fault in 0..8 {
                let mut tree = Fake::new();
                match fault {
                    0 => tree.nodes.get_mut(&0).unwrap().value = None,
                    1 => tree.nodes.get_mut(&3).unwrap().value = Some(false),
                    2 => tree.nodes.get_mut(&0).unwrap().value = Some(true),
                    3 => tree.nodes.get_mut(&1).unwrap().children.push(0),
                    4 => tree.nodes.get_mut(&3).unwrap().parent = Some(2),
                    5 => tree.nodes.get_mut(&2).unwrap().children.clear(),
                    6 => tree.nodes.get_mut(&4).unwrap().role = None,
                    _ => tree.nodes.get_mut(&0).unwrap().press = false,
                }
                assert!(capture(&tree, 0, scope()).is_none(), "fault {fault}");
            }
        }
        #[test]
        fn retained_tab_refuses_foreign_replacement_web_and_wrong_window_proofs() {
            for fault in 0..10 {
                let mut tree = Fake::new();
                let proof = capture(&tree, 0, scope()).unwrap();
                tree.switch();
                match fault {
                    0 => tree.nodes.get_mut(&0).unwrap().pid = 99,
                    1 => tree.nodes.get_mut(&1).unwrap().role = Some("AXWebArea"),
                    2 => tree.nodes.get_mut(&5).unwrap().ordinary = false,
                    3 => tree.nodes.get_mut(&0).unwrap().window = Some(2),
                    4 => tree.nodes.get_mut(&0).unwrap().top = None,
                    5 => tree.nodes.get_mut(&3).unwrap().id = 10,
                    6 => tree.nodes.get_mut(&5).unwrap().id = 10,
                    7 => tree.nodes.get_mut(&2).unwrap().id = 20,
                    8 => {
                        let group = tree.nodes[&1].clone();
                        tree.nodes.insert(6, group);
                        tree.nodes.get_mut(&0).unwrap().parent = Some(6);
                    }
                    _ => {
                        let peer = tree.nodes.remove(&3).unwrap();
                        tree.nodes.insert(6, peer);
                        tree.nodes.get_mut(&1).unwrap().children = vec![0, 6, 4];
                    }
                }
                assert!(
                    confirm(&tree, proof, kAXErrorSuccess).is_none(),
                    "fault {fault}"
                );
            }
        }
        #[test]
        fn retained_tab_rejects_second_pass_changes_and_lifetime_or_deadline_loss() {
            for fault in ["owner", "parent", "source", "selection", "role", "expired"] {
                let mut tree = Fake::new();
                let proof = capture(&tree, 0, scope()).unwrap();
                tree.switch();
                tree.late = Some(fault);
                assert!(confirm(&tree, proof, kAXErrorSuccess).is_none(), "{fault}");
            }
            for fault in 0..3 {
                let mut tree = Fake::new();
                let mut s = scope();
                if fault == 0 {
                    s.deadline = Instant::now();
                }
                if fault == 1 {
                    tree.start = (1, 3);
                }
                if fault == 2 {
                    tree.alive = false;
                }
                assert!(capture(&tree, 0, s).is_none());
            }
        }
        #[test]
        fn retained_tab_bounds_full_children_and_radios() {
            for radio in [false, true] {
                let mut tree = Fake::new();
                for n in 6..70 {
                    let mut node = tree.nodes[&4].clone();
                    if radio {
                        node.role = Some("AXRadioButton");
                        node.value = Some(false);
                    }
                    tree.nodes.insert(n, node);
                    tree.nodes.get_mut(&1).unwrap().children.push(n);
                    if radio && n == 21 {
                        break;
                    }
                }
                assert!(capture(&tree, 0, scope()).is_none());
            }
        }
        pub(super) fn destination_for_guard_test() -> Destination {
            switched_destination()
        }
    }
    #[cfg(test)]
    pub(crate) fn destination_for_guard_test() -> Destination {
        tests::destination_for_guard_test()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn host() -> TabHost {
        TabHost {
            pid: 42,
            window_id: 7,
            title: "Existing document".into(),
            tabs: vec![
                ("Existing document".into(), true),
                ("Requested document".into(), false),
            ],
        }
    }

    #[test]
    fn inactive_window_gets_navigation_hint_without_elements_or_input_authority() {
        let hint = choose_hint(42, 8, "Requested document", &[host()]).unwrap();
        assert_eq!(hint.host_window_id, 7);
        assert_eq!(hint.target_window_id, 8);
        assert_eq!(hint.match_kind, "unique_exact_title");
        let value = serde_json::to_value(hint).unwrap();
        assert!(value.get("element_index").is_none());
        assert!(value.get("element_token").is_none());
    }

    #[test]
    fn duplicate_labels_in_one_or_two_hosts_are_ambiguous() {
        let mut duplicate = host();
        duplicate.tabs.push(("Requested document".into(), false));
        assert!(choose_hint(42, 8, "Requested document", &[duplicate]).is_none());
        let mut sibling = host();
        sibling.window_id = 9;
        assert!(choose_hint(42, 8, "Requested document", &[host(), sibling]).is_none());
    }

    #[test]
    fn foreign_identity_target_itself_or_unselected_host_are_not_hints() {
        let mut foreign = host();
        foreign.pid = 43;
        let mut same = host();
        same.window_id = 8;
        let mut unselected = host();
        unselected.tabs[0].1 = false;
        let mut wrong_title = host();
        wrong_title.title = "Different window".into();
        for candidate in [foreign, same, unselected, wrong_title] {
            assert!(choose_hint(42, 8, "Requested document", &[candidate]).is_none());
        }
    }

    #[test]
    fn partial_title_selected_target_and_missing_title_do_not_match() {
        assert!(choose_hint(42, 8, "Requested", &[host()]).is_none());
        assert!(choose_hint(42, 8, "", &[host()]).is_none());
        let mut selected = host();
        selected.tabs[1].1 = true;
        assert!(choose_hint(42, 8, "Requested document", &[selected]).is_none());
    }
}
