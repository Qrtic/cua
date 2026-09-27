//! Read-only proof for a bare launch that need not send a reopen request.
//! Failure supplies no reuse result; the caller retains its original path.

use crate::{ax::bindings::*, windows::WindowInfo};
use core_foundation::{
    array::CFArray,
    base::{CFEqual, CFGetTypeID, CFType, CFTypeRef, TCFType},
    boolean::CFBoolean,
    string::CFString,
};
use std::{
    collections::HashMap,
    time::{Duration, Instant},
};

const MAX_WINDOWS: usize = 32;
const BUDGET: Duration = Duration::from_millis(250);

pub(super) fn bare_request(
    urls: &[String],
    args: &[String],
    env: &HashMap<String, String>,
    new_instance: bool,
) -> bool {
    urls.is_empty() && args.is_empty() && env.is_empty() && !new_instance
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Identity {
    pub(super) pid: i32,
    pub(super) bundle: String,
    birth: (u64, u64),
    pub(super) name: String,
}

#[derive(Clone, Debug, PartialEq)]
struct Facts {
    pid: i32,
    id: u32,
    frame: [f64; 4],
    ordinary: bool,
    minimized: bool,
}

trait Probe {
    type Window: PartialEq;
    fn identity(&mut self) -> Option<Identity>;
    fn windows(&mut self) -> Option<Vec<Self::Window>>;
    fn facts(&mut self, window: &Self::Window) -> Option<Facts>;
    fn cg(&mut self) -> Option<Vec<WindowInfo>>;
    fn within_budget(&self) -> bool;
}

fn frame(window: &WindowInfo) -> [f64; 4] {
    [
        window.bounds.x,
        window.bounds.y,
        window.bounds.width,
        window.bounds.height,
    ]
}

fn usable(window: &WindowInfo, facts: &Facts, pid: i32) -> bool {
    let bounds = frame(window);
    facts.ordinary
        && !facts.minimized
        && facts.pid == pid
        && facts.id != 0
        && window.pid == pid
        && window.window_id == facts.id
        && window.layer == 0
        && window.is_on_screen
        && window.on_current_space == Some(true)
        && window.current_space_id.is_some_and(|space| {
            space != 0
                && window
                    .space_ids
                    .as_ref()
                    .is_some_and(|ids| ids.contains(&space))
        })
        && bounds.iter().all(|value| value.is_finite())
        && bounds[2] > 1.0
        && bounds[3] > 1.0
        && bounds == facts.frame
}

fn one_cg<'a>(windows: &'a [WindowInfo], id: u32) -> Option<&'a WindowInfo> {
    let mut matches = windows.iter().filter(|window| window.window_id == id);
    let only = matches.next()?;
    matches.next().is_none().then_some(only)
}

// The same retained AX objects, their membership, lifecycle, physical IDs,
// bounds and Space must survive a second read. This does not authorize input.
fn prove(probe: &mut impl Probe) -> Option<(Identity, Vec<WindowInfo>)> {
    let before = probe.identity()?;
    let cg_before = probe.cg()?;
    let windows = probe.windows()?;
    if windows.is_empty()
        || windows.len() > MAX_WINDOWS
        || windows
            .iter()
            .enumerate()
            .any(|(i, window)| windows[..i].contains(window))
    {
        return None;
    }
    let mut candidates = Vec::new();
    for (index, window) in windows.iter().enumerate() {
        let facts = probe.facts(window)?;
        if !facts.ordinary || facts.minimized {
            continue;
        }
        let cg = one_cg(&cg_before, facts.id)?;
        if !usable(cg, &facts, before.pid) {
            return None;
        }
        candidates.push((index, facts, cg.clone()));
    }
    if candidates.is_empty() || probe.windows()? != windows {
        return None;
    }
    for (index, facts, _) in &candidates {
        if probe.facts(&windows[*index])?.ne(facts) {
            return None;
        }
    }
    let cg_after = probe.cg()?;
    let mut result = Vec::new();
    for (_, facts, old) in candidates {
        let current = one_cg(&cg_after, facts.id)?;
        if !usable(current, &facts, before.pid)
            || old.current_space_id != current.current_space_id
            || old.space_ids != current.space_ids
        {
            return None;
        }
        result.push(current.clone());
    }
    (probe.identity()? == before && probe.within_budget()).then_some((before, result))
}

struct Element(CFType);
impl PartialEq for Element {
    fn eq(&self, other: &Self) -> bool {
        unsafe { CFEqual(self.0.as_CFTypeRef(), other.0.as_CFTypeRef()) != 0 }
    }
}
impl Element {
    fn ax(&self) -> AXUIElementRef {
        self.0.as_CFTypeRef() as AXUIElementRef
    }
}

struct Native {
    pid: i32,
    bundle: String,
    app: Element,
    deadline: Instant,
}
impl Native {
    // Timeout only affects these local AX proxies; it does not enable AX,
    // write an app attribute or change the process's focus.
    fn ready(&self, element: &Element) -> Option<()> {
        let left = self.deadline.checked_duration_since(Instant::now())?;
        if left.is_zero() {
            return None;
        }
        (unsafe { AXUIElementSetMessagingTimeout(element.ax(), left.as_secs_f32().min(0.05)) }
            == kAXErrorSuccess)
            .then_some(())
    }

    fn attribute(&self, element: &Element, name: &str) -> Option<CFType> {
        self.ready(element)?;
        let name = CFString::new(name);
        let mut value = std::ptr::null();
        let status = unsafe {
            AXUIElementCopyAttributeValue(element.ax(), name.as_concrete_TypeRef(), &mut value)
        };
        // Even an error may return a retained value. Always release it.
        let value = (!value.is_null()).then(|| unsafe { CFType::wrap_under_create_rule(value) })?;
        (status == kAXErrorSuccess && self.within_budget()).then_some(value)
    }

    fn string(&self, element: &Element, name: &str) -> Option<String> {
        let value = self.attribute(element, name)?;
        (value.type_of() == CFString::type_id()).then(|| unsafe {
            CFString::wrap_under_get_rule(value.as_CFTypeRef() as _).to_string()
        })
    }

    fn pair(&self, element: &Element, name: &str, kind: AXValueType) -> Option<[f64; 2]> {
        extern "C" {
            fn AXValueGetTypeID() -> core_foundation::base::CFTypeID;
        }
        let value = self.attribute(element, name)?;
        let mut pair = [0.0f64; 2];
        unsafe {
            if CFGetTypeID(value.as_CFTypeRef()) != AXValueGetTypeID()
                || AXValueGetType(value.as_CFTypeRef() as _) != kind
                || !AXValueGetValue(value.as_CFTypeRef() as _, kind, pair.as_mut_ptr().cast())
            {
                return None;
            }
        }
        pair.iter().all(|value| value.is_finite()).then_some(pair)
    }
}

impl Probe for Native {
    type Window = Element;
    fn identity(&mut self) -> Option<Identity> {
        use objc2_app_kit::NSRunningApplication;
        let birth = crate::ax::enablement::process_start_stamp(self.pid)?;
        let mut apps = crate::apps::list_running_apps()
            .into_iter()
            .filter(|app| app.bundle_id.as_deref() == Some(self.bundle.as_str()));
        let app = apps.next()?;
        if apps.next().is_some() || app.pid != self.pid || !app.running || birth.0 == 0 {
            return None;
        }
        unsafe {
            let running = NSRunningApplication::runningApplicationWithProcessIdentifier(self.pid)?;
            if running.isTerminated()
                || running.isHidden()
                || running
                    .bundleIdentifier()
                    .map(|id| id.to_string())
                    .as_deref()
                    != Some(self.bundle.as_str())
            {
                return None;
            }
        }
        (self.within_budget() && crate::ax::enablement::process_start_stamp(self.pid)? == birth)
            .then_some(Identity {
                pid: self.pid,
                bundle: self.bundle.clone(),
                birth,
                name: app.name,
            })
    }

    fn windows(&mut self) -> Option<Vec<Element>> {
        let value = self.attribute(&self.app, "AXWindows")?;
        if value.type_of() != CFArray::<CFTypeRef>::type_id() {
            return None;
        }
        let array = unsafe { CFArray::<CFTypeRef>::wrap_under_get_rule(value.as_CFTypeRef() as _) };
        if array.len() <= 0 || array.len() as usize > MAX_WINDOWS {
            return None;
        }
        (0..array.len())
            .map(|index| {
                let item = *array.get(index)?;
                if item.is_null() || unsafe { CFGetTypeID(item) != AXUIElementGetTypeID() } {
                    return None;
                }
                Some(Element(unsafe { CFType::wrap_under_get_rule(item) }))
            })
            .collect()
    }

    fn facts(&mut self, window: &Element) -> Option<Facts> {
        let ordinary = self.string(window, "AXRole")? == "AXWindow"
            && self.string(window, "AXSubrole")? == "AXStandardWindow";
        // Non-ordinary windows cannot supply reuse evidence.
        if !ordinary {
            return Some(Facts {
                pid: 0,
                id: 0,
                frame: [0.0; 4],
                ordinary,
                minimized: true,
            });
        }
        let minimized = self.attribute(window, "AXMinimized")?;
        if minimized.type_of() != CFBoolean::type_id() {
            return None;
        }
        let minimized =
            unsafe { CFBoolean::wrap_under_get_rule(minimized.as_CFTypeRef() as _) }.into();
        self.ready(window)?;
        let mut pid = 0;
        if unsafe { AXUIElementGetPid(window.ax(), &mut pid) } != kAXErrorSuccess {
            return None;
        }
        self.ready(window)?;
        let id = unsafe { ax_get_window_id(window.ax()) }?;
        let [x, y] = self.pair(window, "AXPosition", kAXValueCGPointType)?;
        let [w, h] = self.pair(window, "AXSize", kAXValueCGSizeType)?;
        self.within_budget().then_some(Facts {
            pid,
            id,
            frame: [x, y, w, h],
            ordinary,
            minimized,
        })
    }

    fn cg(&mut self) -> Option<Vec<WindowInfo>> {
        if !self.within_budget() {
            return None;
        }
        let snapshot = crate::windows::all_windows_with_space_snapshot();
        (snapshot.succeeded && self.within_budget()).then_some(snapshot.windows)
    }
    fn within_budget(&self) -> bool {
        Instant::now() < self.deadline
    }
}

pub(super) fn observe(pid: i32, bundle: &str) -> Option<(Identity, Vec<WindowInfo>)> {
    let deadline = Instant::now() + BUDGET;
    let app = unsafe { AXUIElementCreateApplication(pid) };
    if app.is_null() {
        return None;
    }
    let mut native = Native {
        pid,
        bundle: bundle.to_owned(),
        app: Element(unsafe { CFType::wrap_under_create_rule(app as _) }),
        deadline,
    };
    prove(&mut native)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;

    struct Fake {
        identities: VecDeque<Option<Identity>>,
        windows: VecDeque<Option<Vec<u8>>>,
        facts: VecDeque<Option<Facts>>,
        cg: VecDeque<Option<Vec<WindowInfo>>>,
        live: bool,
    }
    impl Probe for Fake {
        type Window = u8;
        fn identity(&mut self) -> Option<Identity> {
            self.identities.pop_front().flatten()
        }
        fn windows(&mut self) -> Option<Vec<u8>> {
            self.windows.pop_front().flatten()
        }
        fn facts(&mut self, _: &u8) -> Option<Facts> {
            self.facts.pop_front().flatten()
        }
        fn cg(&mut self) -> Option<Vec<WindowInfo>> {
            self.cg.pop_front().flatten()
        }
        fn within_budget(&self) -> bool {
            self.live
        }
    }
    fn valid() -> Fake {
        let identity = Identity {
            pid: 42,
            bundle: "org.example.app".into(),
            birth: (100, 12),
            name: "App".into(),
        };
        let facts = Facts {
            pid: 42,
            id: 7,
            frame: [10.0, 20.0, 640.0, 480.0],
            ordinary: true,
            minimized: false,
        };
        let window = WindowInfo {
            window_id: 7,
            pid: 42,
            app_name: "App".into(),
            title: "Window".into(),
            bounds: crate::windows::WindowBounds {
                x: 10.0,
                y: 20.0,
                width: 640.0,
                height: 480.0,
            },
            layer: 0,
            z_index: 9,
            is_on_screen: true,
            current_space_id: Some(4),
            on_current_space: Some(true),
            space_ids: Some(vec![4]),
        };
        Fake {
            identities: vec![Some(identity.clone()), Some(identity)].into(),
            windows: vec![Some(vec![1]), Some(vec![1])].into(),
            facts: vec![Some(facts.clone()), Some(facts)].into(),
            cg: vec![Some(vec![window.clone()]), Some(vec![window])].into(),
            live: true,
        }
    }

    #[test]
    fn bare_request_never_short_circuits_file_arguments_environment_or_new_instance() {
        assert!(bare_request(&[], &[], &HashMap::new(), false));
        assert!(!bare_request(
            &["/tmp/file".into()],
            &[],
            &HashMap::new(),
            false
        ));
        assert!(!bare_request(
            &[],
            &["--flag".into()],
            &HashMap::new(),
            false
        ));
        assert!(!bare_request(
            &[],
            &[],
            &HashMap::from([("KEY".into(), "value".into())]),
            false
        ));
        assert!(!bare_request(&[], &[], &HashMap::new(), true));
    }

    #[test]
    fn reuse_requires_two_reads_of_same_retained_window_and_lifetime() {
        let mut probe = valid();
        let (app, windows) = prove(&mut probe).expect("complete native evidence");
        assert_eq!(app.pid, 42);
        assert_eq!(windows.len(), 1);
        assert!(
            probe.identities.is_empty()
                && probe.windows.is_empty()
                && probe.facts.is_empty()
                && probe.cg.is_empty()
        );
    }

    #[test]
    fn hidden_missing_or_changed_same_pid_lifetime_does_not_reuse() {
        for phase in 0..2 {
            let mut probe = valid();
            // Native identity returns None for hidden, terminated, ambiguous
            // bundle inventory or an unavailable kernel birth stamp.
            probe.identities[phase] = None;
            assert!(prove(&mut probe).is_none());
        }
        let mut probe = valid();
        probe.identities[1].as_mut().unwrap().birth.1 += 1;
        assert!(prove(&mut probe).is_none());
        let mut probe = valid();
        probe.identities[1].as_mut().unwrap().bundle = "org.other".into();
        assert!(prove(&mut probe).is_none());
    }

    #[test]
    fn minimized_nonordinary_and_unreadable_ax_are_not_window_evidence() {
        for phase in 0..2 {
            for kind in 0..3 {
                let mut probe = valid();
                match kind {
                    0 => probe.facts[phase].as_mut().unwrap().minimized = true,
                    1 => probe.facts[phase].as_mut().unwrap().ordinary = false,
                    _ => probe.facts[phase] = None,
                }
                assert!(prove(&mut probe).is_none(), "phase={phase} kind={kind}");
            }
        }
    }

    #[test]
    fn ax_cg_owner_id_frame_visibility_space_or_duplicate_disagreement_refuses() {
        for phase in 0..2 {
            for kind in 0..8 {
                let mut probe = valid();
                let windows = probe.cg[phase].as_mut().unwrap();
                match kind {
                    0 => windows[0].pid += 1,
                    1 => windows[0].window_id += 1,
                    2 => windows[0].bounds.x += 1.0,
                    3 => windows[0].is_on_screen = false,
                    4 => windows[0].on_current_space = None,
                    5 => windows[0].space_ids = Some(vec![99]),
                    6 => windows[0].layer = 1,
                    _ => windows.push(windows[0].clone()),
                }
                assert!(prove(&mut probe).is_none(), "phase={phase} kind={kind}");
            }
        }
        let mut probe = valid();
        probe.facts[0].as_mut().unwrap().pid += 1;
        assert!(prove(&mut probe).is_none());
    }

    #[test]
    fn changed_or_ambiguous_membership_missing_cg_and_expiry_supply_no_partial_result() {
        for members in [vec![], vec![2], vec![1, 1], (0..33).collect()] {
            let mut probe = valid();
            probe.windows[1] = Some(members);
            assert!(prove(&mut probe).is_none());
        }
        let mut probe = valid();
        probe.cg[1] = None;
        assert!(prove(&mut probe).is_none());
        let mut probe = valid();
        probe.live = false;
        assert!(prove(&mut probe).is_none());
    }

    #[test]
    fn valid_prefix_cannot_leak_reuse_when_later_window_is_unproven() {
        let mut probe = valid();
        probe.windows[0] = Some(vec![1, 2]);
        // The first window is valid and already collected. The next native
        // read cannot prove its window; no partial reuse receipt may escape.
        probe.facts[1] = None;
        assert!(prove(&mut probe).is_none());
    }
}
