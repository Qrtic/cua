//! Restore a document that a background action has visually covered, without
//! activating an application or changing its remembered key/first responder.
//!
//! AppKit may order a document forward when attaching a sheet without sending
//! NSWorkspace an application activation. The focus-steal observer cannot see
//! that event. This guard considers only pre-existing, overlapping target
//! windows which crossed the still-focused original window during one action.

use std::collections::HashSet;
use std::time::{Duration, Instant};

use core_foundation::base::CFRelease;

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

fn unchanged_context(reliable: bool, generation: u64, original_generation: u64,
                     front_pid: Option<i32>, focused: Option<u32>,
                     original_pid: i32, original_window: u32, elapsed: Duration) -> bool {
    reliable && generation == original_generation && front_pid == Some(original_pid)
        && focused == Some(original_window) && elapsed <= MAX_AGE
}

pub(crate) struct BackgroundOrderGuard {
    pid: i32,
    window: u32,
    target_pid: i32,
    candidates: HashSet<u32>,
    generation: u64,
    started: Instant,
    expires_at: Instant,
    attempted: bool,
}

impl BackgroundOrderGuard {
    pub(crate) fn capture(target_pid: i32, windows: &[WindowInfo]) -> Option<Self> {
        let activity = crate::foreground_activity::snapshot();
        if !activity.reliable { return None; }
        let pid = crate::apps::frontmost_pid()?;
        if pid <= 0 || pid == target_pid { return None; }
        let window = focused_window(pid)?;
        let candidates = eligible_below(windows, pid, window, target_pid);
        if candidates.is_empty() { return None; }
        let started = Instant::now();
        let result = Self { pid, window, target_pid, candidates,
            generation: activity.generation, started, expires_at: started + MAX_AGE, attempted: false };
        if !result.current() { return None; }
        tracing::debug!(target: "cua_window_order", pid, window, target_pid,
            candidates=result.candidates.len(), "Captured background window-order protection");
        Some(result)
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
        let activity = crate::foreground_activity::snapshot();
        Instant::now() < self.expires_at && unchanged_context(activity.reliable, activity.generation, self.generation,
            crate::apps::frontmost_pid(), focused_window(self.pid),
            self.pid, self.window, self.started.elapsed())
    }

    /// One cleanup attempt at most. Unlike focus restoration this must never
    /// activate an app or select a different window: a changed focus vetoes it.
    pub(crate) fn restore_if_crossed(&mut self, windows: &[WindowInfo]) {
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
        if !latest.succeeded || !crossed(&latest.windows, self.pid, self.window, self.target_pid, &self.candidates)
            || !self.current() { return; }
        let status = unsafe { ax::perform_action(window.0, "AXRaise") };
        tracing::debug!(target: "cua_window_order", pid=self.pid, window=self.window,
            target_pid=self.target_pid, ax_status=status,
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
    fn any_human_activity_focus_change_monitor_gap_or_expired_lease_vetoes_restore() {
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
}
