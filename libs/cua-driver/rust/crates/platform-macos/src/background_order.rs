//! Restore a document that a background action has visually covered, without
//! activating an application or changing its remembered key/first responder.
//!
//! AppKit may order a document forward when attaching a sheet without sending
//! NSWorkspace an application activation. The focus-steal observer cannot see
//! that event. This guard considers only pre-existing, overlapping target
//! windows which crossed the still-focused original window during one action.
//! Unmodified pointer motion does not prevent restoring that same window's
//! order; every other external event and any monitoring gap still vetoes it.

use std::collections::HashSet;
use std::time::{Duration, Instant};

use core_foundation::base::CFRelease;
use cua_driver_core::foreground_activity::OrderingSnapshot;

use crate::ax::bindings::{self as ax, AXUIElementRef};
use crate::windows::{WindowBounds, WindowInfo};

const MAX_AGE: Duration = Duration::from_secs(5);
const AX_TIMEOUT: f32 = 0.1;

struct OwnedAx(AXUIElementRef);

impl OwnedAx {
    fn bounded(raw: AXUIElementRef) -> Option<Self> {
        if raw.is_null() { return None; }
        let value = Self(raw);
        (unsafe { ax::AXUIElementSetMessagingTimeout(raw, AX_TIMEOUT) } == ax::kAXErrorSuccess)
            .then_some(value)
    }
}

impl Drop for OwnedAx {
    fn drop(&mut self) { unsafe { CFRelease(self.0.cast()) }; }
}

fn overlaps(a: &WindowBounds, b: &WindowBounds) -> bool {
    [a, b].iter().all(|r| r.x.is_finite() && r.y.is_finite()
        && r.width.is_finite() && r.height.is_finite() && r.width > 0.0 && r.height > 0.0)
        && a.x < b.x + b.width && b.x < a.x + a.width
        && a.y < b.y + b.height && b.y < a.y + a.height
}

fn exact_visible(windows: &[WindowInfo], pid: i32, id: u32) -> Option<&WindowInfo> {
    let mut matches = windows.iter().filter(|w| w.pid == pid && w.window_id == id
        && w.layer == 0 && w.is_on_screen && w.on_current_space != Some(false));
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn eligible_below(windows: &[WindowInfo], front_pid: i32, front_id: u32, target: i32) -> HashSet<u32> {
    let Some(front) = exact_visible(windows, front_pid, front_id) else { return HashSet::new() };
    if target == front_pid { return HashSet::new(); }
    windows.iter().filter(|w| w.pid == target && w.layer == 0 && w.is_on_screen
        && w.on_current_space != Some(false) && w.z_index < front.z_index
        && overlaps(&w.bounds, &front.bounds)).map(|w| w.window_id).collect()
}

fn crossed(windows: &[WindowInfo], front_pid: i32, front_id: u32,
           target: i32, candidates: &HashSet<u32>) -> bool {
    let Some(front) = exact_visible(windows, front_pid, front_id) else { return false };
    windows.iter().any(|w| candidates.contains(&w.window_id) && w.pid == target
        && w.layer == 0 && w.is_on_screen && w.on_current_space != Some(false)
        && w.z_index > front.z_index && overlaps(&w.bounds, &front.bounds))
}

fn unchanged_context(reliable: bool, non_motion_generation: u64, original_non_motion_generation: u64,
                     front_pid: Option<i32>, focused: Option<u32>,
                     original_pid: i32, original_window: u32, elapsed: Duration) -> bool {
    reliable && non_motion_generation == original_non_motion_generation && front_pid == Some(original_pid)
        && focused == Some(original_window) && elapsed <= MAX_AGE
}

pub(crate) struct BackgroundOrderGuard {
    pid: i32,
    window: u32,
    target_pid: i32,
    candidates: HashSet<u32>,
    generation: u64,
    non_motion_generation: u64,
    started: Instant,
    expires_at: Instant,
    attempted: bool,
    #[cfg(test)]
    observed_checks: Option<std::sync::Arc<std::sync::atomic::AtomicUsize>>,
}

impl BackgroundOrderGuard {
    pub(crate) fn capture(target_pid: i32, windows: &[WindowInfo]) -> Option<Self> {
        let activity = crate::foreground_activity::ordering_snapshot();
        if !activity.activity.reliable { return None; }
        let pid = crate::apps::frontmost_pid()?;
        if pid <= 0 || pid == target_pid { return None; }
        let window = focused_window(pid)?;
        let candidates = eligible_below(windows, pid, window, target_pid);
        if candidates.is_empty() { return None; }
        let started = Instant::now();
        let result = Self { pid, window, target_pid, candidates,
            generation: activity.activity.generation, non_motion_generation: activity.non_motion_generation,
            started, expires_at: started + MAX_AGE, attempted: false,
            #[cfg(test)]
            observed_checks: None,
        };
        if !result.current() { return None; }
        tracing::debug!(target: "cua_window_order", pid, window, target_pid,
            candidates=result.candidates.len(), "Captured background window-order protection");
        Some(result)
    }

    #[cfg(test)]
    pub(crate) fn observing_checks(checks: std::sync::Arc<std::sync::atomic::AtomicUsize>) -> Self {
        let started = Instant::now();
        // No candidate can cross: lifecycle tests observe the real polling
        // path without authorizing any accessibility mutation on the desktop.
        Self { pid: -1, window: 0, target_pid: -2, candidates: HashSet::new(),
            generation: 0, non_motion_generation: 0, started, expires_at: started + MAX_AGE, attempted: false,
            observed_checks: Some(checks) }
    }

    /// The action may have returned before AppKit attaches and raises its
    /// sheet. Keep checking only within the owning suppression lease; neither
    /// this guard nor its polling callback creates or extends that lease.
    pub(crate) fn poll(&mut self, deadline: Instant) -> bool {
        self.expires_at = self.expires_at.min(deadline);
        if self.attempted || Instant::now() >= self.expires_at { return false; }
        let latest = crate::windows::visible_windows_with_space_snapshot();
        if !latest.succeeded { return false; }
        self.restore_if_crossed(&latest.windows);
        !self.attempted
    }

    fn current(&self) -> bool {
        self.current_evidence().is_some()
    }

    fn current_evidence(&self) -> Option<OrderingSnapshot> {
        let activity = crate::foreground_activity::ordering_snapshot();
        if Instant::now() >= self.expires_at {
            tracing::debug!(target: "cua_window_order", pid=self.pid, window=self.window,
                target_pid=self.target_pid, "Window ordering guard deadline expired");
            return None;
        }
        let front_pid = crate::apps::frontmost_pid();
        let focused = focused_window(self.pid);
        let elapsed = self.started.elapsed();
        let valid = unchanged_context(activity.activity.reliable, activity.non_motion_generation,
            self.non_motion_generation,
            front_pid, focused, self.pid, self.window, elapsed);
        if !valid {
            // Log the same evidence that vetoed this check. An untagged event
            // is not proof of human input, and a second observation must not
            // replace the generation or window identity used for admission.
            tracing::debug!(target: "cua_window_order", pid=self.pid, window=self.window,
                target_pid=self.target_pid, monitor_reliable=activity.activity.reliable,
                original_generation=self.generation, current_generation=activity.activity.generation,
                original_non_motion_generation=self.non_motion_generation,
                current_non_motion_generation=activity.non_motion_generation,
                current_front_pid=?front_pid, current_focused_window=?focused,
                elapsed_ms=elapsed.as_millis(),
                activity_diagnostic=?crate::foreground_activity::diagnostic_state(),
                "Window ordering guard veto evidence");
        }
        valid.then_some(activity)
    }

    /// One cleanup attempt at most. Unlike focus restoration this must never
    /// activate an app or select a different window: a changed focus vetoes it.
    pub(crate) fn restore_if_crossed(&mut self, windows: &[WindowInfo]) {
        #[cfg(test)]
        if let Some(checks) = &self.observed_checks {
            checks.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        if self.attempted || !crossed(windows, self.pid, self.window, self.target_pid, &self.candidates) {
            return;
        }
        self.attempted = true;
        if !self.current() {
            tracing::debug!(target: "cua_window_order", pid=self.pid, window=self.window,
                "Window ordering restore skipped after context or activity changed");
            return;
        }
        let Some(app) = OwnedAx::bounded(unsafe { ax::AXUIElementCreateApplication(self.pid) }) else { return };
        let Some(window) = (unsafe { ax::copy_element_attr(app.0, "AXFocusedWindow") })
            .and_then(OwnedAx::bounded) else { return };
        let mut pid = 0;
        let identity_matches = unsafe {
            ax::AXUIElementGetPid(window.0, &mut pid) == ax::kAXErrorSuccess
                && pid == self.pid && ax::ax_get_window_id(window.0) == Some(self.window)
                && ax::copy_string_attr(window.0, "AXRole").as_deref() == Some("AXWindow")
                && ax::copy_action_names(window.0).iter().any(|a| a == "AXRaise")
        };
        if !identity_matches || !self.current() { return; }
        // Re-read ordering after the AX identity queries. A stale before/after
        // comparison never authorizes a raise after the target has moved away.
        let latest = crate::windows::visible_windows_with_space_snapshot();
        if !latest.succeeded || !crossed(&latest.windows, self.pid, self.window, self.target_pid, &self.candidates) {
            return;
        }
        let Some(admission) = self.current_evidence() else { return; };
        let status = unsafe { ax::perform_action(window.0, "AXRaise") };
        tracing::debug!(target: "cua_window_order", pid=self.pid, window=self.window,
            target_pid=self.target_pid, ax_status=status,
            original_generation=self.generation, current_generation=admission.activity.generation,
            original_non_motion_generation=self.non_motion_generation,
            current_non_motion_generation=admission.non_motion_generation,
            "Submitted ordering-only restore of the unchanged foreground window");
        // No second actuator or retry even if AX times out after an effect.
    }
}

fn focused_window(pid: i32) -> Option<u32> {
    let app = OwnedAx::bounded(unsafe { ax::AXUIElementCreateApplication(pid) })?;
    let window = unsafe { ax::copy_element_attr(app.0, "AXFocusedWindow") }.and_then(OwnedAx::bounded)?;
    unsafe { ax::ax_get_window_id(window.0) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn window(pid: i32, id: u32, z: usize) -> WindowInfo {
        WindowInfo { window_id: id, pid, z_index: z, app_name: String::new(), title: String::new(),
            bounds: WindowBounds { x: 0.0, y: 0.0, width: 600.0, height: 400.0 },
            layer: 0, is_on_screen: true, current_space_id: Some(1),
            on_current_space: Some(true), space_ids: Some(vec![1]) }
    }

    #[test]
    fn preexisting_background_document_crossing_original_front_is_detected() {
        let before = vec![window(1, 10, 30), window(2, 20, 10)];
        let ids = eligible_below(&before, 1, 10, 2);
        assert_eq!(ids, HashSet::from([20]));
        assert!(!crossed(&before, 1, 10, 2, &ids));
        assert!(crossed(&[window(2, 20, 40), window(1, 10, 30)], 1, 10, 2, &ids));
    }

    #[test]
    fn existing_foreground_target_other_apps_and_new_popups_are_not_candidates() {
        let before = vec![window(1, 10, 30), window(2, 20, 10), window(2, 21, 40), window(3, 30, 5)];
        let ids = eligible_below(&before, 1, 10, 2);
        assert_eq!(ids, HashSet::from([20]));
        assert!(eligible_below(&before, 1, 10, 1).is_empty());
        assert!(!crossed(&[window(1, 10, 30), window(2, 99, 50), window(3, 20, 40)], 1, 10, 2, &ids));
    }

    #[test]
    fn hidden_off_space_nonoverlapping_and_missing_original_windows_do_not_restore() {
        let front = window(1, 10, 30);
        for kind in 0..5 {
            let mut target = window(2, 20, 40);
            match kind {
                0 => target.is_on_screen = false,
                1 => target.on_current_space = Some(false),
                2 => target.bounds.x = 900.0,
                3 => target.bounds.width = f64::NAN,
                _ => target.layer = 3,
            }
            assert!(!crossed(&[front.clone(), target], 1, 10, 2, &HashSet::from([20])));
        }
        assert!(!crossed(&[window(2, 20, 40)], 1, 10, 2, &HashSet::from([20])));
    }

    #[test]
    fn non_motion_activity_focus_change_monitor_gap_or_expired_lease_vetoes_restore() {
        let ok = |reliable, generation, pid, focused, age| unchanged_context(
            reliable, generation, 7, pid, focused, 1, 10, age);
        assert!(ok(true, 7, Some(1), Some(10), Duration::ZERO));
        assert!(!ok(false, 7, Some(1), Some(10), Duration::ZERO));
        assert!(!ok(true, 8, Some(1), Some(10), Duration::ZERO));
        assert!(!ok(true, 7, Some(2), Some(10), Duration::ZERO));
        assert!(!ok(true, 7, Some(1), Some(11), Duration::ZERO));
        assert!(!ok(true, 7, Some(1), None, Duration::ZERO));
        assert!(!ok(true, 7, None, Some(10), Duration::ZERO));
        assert!(!ok(true, 7, Some(1), Some(10), MAX_AGE + Duration::from_millis(1)));
    }

    #[test]
    fn motion_allows_only_exact_window_order_restore_and_never_masks_a_click() {
        use cua_driver_core::foreground_activity::{Activity, EpisodeLease, Source};
        let mut activity = Activity::default();
        for time in (0..=5_000).step_by(100) { activity.health(time, true); }
        let before = activity.ordering_snapshot(5_000);
        let input_lease = EpisodeLease::begin(5_000, before.activity).unwrap();
        activity.pointer_motion_event(5_001, Source::Unknown);
        let current = activity.ordering_snapshot(5_001);
        let permits = |pid, focused, evidence: cua_driver_core::foreground_activity::OrderingSnapshot| {
            unchanged_context(evidence.activity.reliable, evidence.non_motion_generation,
                before.non_motion_generation, pid, focused, 1, 10, Duration::from_millis(1))
        };
        assert!(permits(Some(1), Some(10), current));
        assert!(!input_lease.permits(5_001, current.activity));
        assert!(!permits(Some(2), Some(10), current));
        assert!(!permits(Some(1), Some(11), current));
        activity.event(5_002, Source::Unknown);
        activity.pointer_motion_event(5_003, Source::Unknown);
        assert!(!permits(Some(1), Some(10), activity.ordering_snapshot(5_003)));
    }
}
