//! Restore a document that a background action has visually covered, without
//! activating an application or changing its remembered key/first responder.
//!
//! AppKit may order a document forward when attaching a sheet without sending
//! NSWorkspace an application activation. The focus-steal observer cannot see
//! that event. This guard considers only pre-existing, overlapping target
//! windows which crossed the still-focused original window during one action.
//! An explicit reopen can also admit an exact, previously hidden window on the
//! current Space, using evidence captured before the launch request.
//! Targeted background input and explicit file-open requests may additionally
//! admit newly created standard document windows from that same process
//! lifetime. Menus, sheets and existing windows above the user's document are
//! never enrolled by this extension.
//! Unmodified pointer motion does not prevent restoring that same window's
//! order; every other external event and any monitoring gap still vetoes it.

use std::collections::HashSet;
use std::time::{Duration, Instant};

use core_foundation::base::CFRelease;
use cua_driver_core::foreground_activity::OrderingSnapshot;

use crate::ax::bindings::{self as ax, AXUIElementRef};
use crate::windows::{WindowBounds, WindowEnumeration, WindowInfo};
use crate::order_diagnostics::{CheckSource, Phase, PollDiagnostics, Trace};

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

fn eligible_before_reopen(windows: &[WindowInfo], front_pid: i32, front_id: u32,
                          target: i32, target_was_hidden: bool) -> HashSet<u32> {
    let mut candidates = eligible_below(windows, front_pid, front_id, target);
    if !target_was_hidden || target == front_pid { return candidates; }
    let Some(front) = exact_visible(windows, front_pid, front_id) else { return candidates };
    // Hidden is a separately verified application property. Off-screen alone
    // never establishes permission to include a minimized or other-Space window.
    // A candidate still has to become visible on this Space before any restore.
    candidates.extend(windows.iter().filter(|w| w.pid == target && w.layer == 0
        && !w.is_on_screen && w.on_current_space == Some(true)
        && overlaps(&w.bounds, &front.bounds)).map(|w| w.window_id));
    candidates
}

pub(crate) fn reopen_window_evidence(
    complete: &WindowEnumeration,
    visible: &WindowEnumeration,
) -> Option<Vec<WindowInfo>> {
    if !complete.succeeded || !visible.succeeded { return None; }
    // On macOS the complete CG inventory may be grouped in an order different
    // from the visible stack. Its relative indices cannot establish which
    // on-screen document was in front. Use it only for hidden membership.
    let mut evidence = visible.windows.clone();
    let visible_ids: HashSet<_> = evidence.iter().map(|w| w.window_id).collect();
    evidence.extend(complete.windows.iter()
        .filter(|w| !w.is_on_screen && !visible_ids.contains(&w.window_id)).cloned());
    Some(evidence)
}

struct NewWindowEvidence {
    known: HashSet<u32>,
    process_start: crate::ax::enablement::ProcessStartStamp,
}

impl NewWindowEvidence {
    fn capture(target: i32, process_start: Option<crate::ax::enablement::ProcessStartStamp>,
               complete: &WindowEnumeration, visible: &WindowEnumeration) -> Option<Self> {
        // A visible-only snapshot cannot distinguish a new document from an
        // existing hidden or minimized one. Failed membership enumeration must
        // not turn every subsequently visible window into a new document.
        if target <= 0 || !complete.succeeded || !visible.succeeded { return None; }
        Some(Self {
            process_start: process_start?,
            known: complete.windows.iter().chain(visible.windows.iter())
                .filter(|w| w.pid == target).map(|w| w.window_id).collect(),
        })
    }
}

fn newly_crossing_windows(windows: &[WindowInfo], front_pid: i32, front_id: u32,
                         target: i32, known: &HashSet<u32>) -> Vec<u32> {
    let Some(front) = exact_visible(windows, front_pid, front_id) else { return Vec::new() };
    if target == front_pid { return Vec::new(); }
    windows.iter().filter(|w| w.pid == target && !known.contains(&w.window_id)
        && w.layer == 0 && w.is_on_screen && w.on_current_space == Some(true)
        && w.z_index > front.z_index && overlaps(&w.bounds, &front.bounds))
        .map(|w| w.window_id).collect()
}

fn standard_document(role: Option<&str>, subrole: Option<&str>, modal: Option<bool>) -> bool {
    role == Some("AXWindow") && subrole == Some("AXStandardWindow") && modal != Some(true)
}

fn proven_new_documents(pid: i32, candidates: &[u32], deadline: Instant) -> HashSet<u32> {
    // This is a targeted, bounded membership query, not an AX scan of every app.
    if candidates.is_empty() || candidates.len() > 8 { return HashSet::new(); }
    let Some(app) = OwnedAx::bounded(unsafe { ax::AXUIElementCreateApplication(pid) }) else {
        return HashSet::new();
    };
    let mut proven = HashSet::new();
    for raw in unsafe { ax::copy_ax_windows(app.0) } {
        let Some(window) = OwnedAx::bounded(raw) else { continue };
        if Instant::now() >= deadline { continue; }
        let Some(id) = (unsafe { ax::ax_get_window_id(window.0) }) else { continue };
        if !candidates.contains(&id) { continue; }
        let mut owner = 0;
        if unsafe { ax::AXUIElementGetPid(window.0, &mut owner) } != ax::kAXErrorSuccess || owner != pid {
            continue;
        }
        let role = unsafe { ax::copy_string_attr(window.0, "AXRole") };
        let subrole = unsafe { ax::copy_string_attr(window.0, "AXSubrole") };
        let modal = unsafe { ax::copy_bool_attr(window.0, "AXModal") };
        if standard_document(role.as_deref(), subrole.as_deref(), modal) {
            proven.insert(id);
        }
    }
    proven
}

// A separate membership proof for retained native-tab switches. It never
// changes NewWindowEvidence.known or authorizes arbitrary newly visible IDs.
fn inactive_tab_windows(target: i32, complete: &WindowEnumeration, visible: &WindowEnumeration) -> HashSet<u32> {
    if !complete.succeeded || !visible.succeeded { return HashSet::new(); }
    complete.windows.iter().filter(|w| w.pid == target && w.layer == 0
        && complete.windows.iter().filter(|n| n.window_id == w.window_id).count() == 1
        && !visible.windows.iter().any(|n| n.window_id == w.window_id))
        .map(|w| w.window_id).collect()
}

fn known_tab_destination(proof: &crate::ax::window_tabs::retained::Destination, target: i32,
                         before: &NewWindowEvidence, visible: &HashSet<u32>, inactive: &HashSet<u32>,
                         deadline: Instant) -> Option<u32> {
    let (pid, source, id, start, original_deadline) = proof.parts();
    (pid == target && id != source && before.known.contains(&source) && visible.contains(&source)
        && before.known.contains(&id) && inactive.contains(&id) && !visible.contains(&id)
        && before.process_start == start && deadline == original_deadline && Instant::now() < deadline)
        .then_some(id)
}

fn tab_crosses(windows: &[WindowInfo], front_pid: i32, front_id: u32, target: i32, id: u32) -> bool {
    let Some(front) = exact_visible(windows, front_pid, front_id) else { return false; };
    let matches: Vec<_> = windows.iter().filter(|w| w.window_id == id).collect();
    matches.len() == 1 && matches[0].pid == target && matches[0].layer == 0
        && matches[0].is_on_screen && matches[0].on_current_space == Some(true)
        && matches[0].z_index > front.z_index && overlaps(&matches[0].bounds, &front.bounds)
}

fn tab_document_visible(pid: i32, id: u32, deadline: Instant) -> bool {
    let Some(app) = OwnedAx::bounded(unsafe { ax::AXUIElementCreateApplication(pid) }) else { return false; };
    if Instant::now() >= deadline || unsafe { ax::copy_bool_attr(app.0, "AXHidden") } != Some(false) { return false; }
    let Ok(snapshot) = (unsafe { ax::try_copy_ax_windows(app.0) }) else { return false; };
    let Some(windows) = snapshot.windows.into_iter().map(OwnedAx::bounded).collect::<Option<Vec<_>>>() else { return false; };
    if !snapshot.complete || windows.len() > 32 { return false; }
    let mut matches = 0;
    for window in windows {
        if Instant::now() >= deadline { return false; }
        let Some(current_id) = (unsafe { ax::ax_get_window_id(window.0) }) else { return false; };
        if current_id != id { continue; }
        matches += 1;
        let mut owner = 0;
        let modal = unsafe { ax::copy_bool_attr(window.0, "AXModal") };
        if unsafe { ax::AXUIElementGetPid(window.0, &mut owner) } != ax::kAXErrorSuccess || owner != pid
            || unsafe { ax::copy_bool_attr(window.0, "AXMinimized") } != Some(false)
            || modal != Some(false)
            || !standard_document(unsafe { ax::copy_string_attr(window.0, "AXRole") }.as_deref(),
                unsafe { ax::copy_string_attr(window.0, "AXSubrole") }.as_deref(), modal) { return false; }
    }
    matches == 1 && Instant::now() < deadline
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
    new_windows: Option<NewWindowEvidence>,
    tab_inactive: HashSet<u32>,
    tab_sources_below: HashSet<u32>,
    pending_tab: Option<crate::ax::window_tabs::retained::Destination>,
    generation: u64,
    non_motion_generation: u64,
    started: Instant,
    expires_at: Instant,
    attempted: bool,
    trace: Trace,
    #[cfg(test)]
    observed_checks: Option<std::sync::Arc<std::sync::atomic::AtomicUsize>>,
}

impl BackgroundOrderGuard {
    pub(crate) fn capture_before_input(target_pid: i32,
                                      process_start: Option<crate::ax::enablement::ProcessStartStamp>,
                                      complete: &WindowEnumeration,
                                      visible: &WindowEnumeration) -> Option<Self> {
        if !visible.succeeded { return None; }
        let new_windows = NewWindowEvidence::capture(target_pid, process_start, complete, visible);
        // Ordinary input does not authorize unhiding an existing document.
        // New-window membership is captured before dispatch; fresh AX ownership,
        // standard-window role and unchanged context are still required later.
        let inactive = inactive_tab_windows(target_pid, complete, visible);
        Self::capture_evidence(target_pid, &visible.windows, false, new_windows).map(|mut guard| {
            guard.tab_inactive = inactive;
            guard.tab_sources_below = visible.windows.iter().filter(|w| w.pid == target_pid && w.layer == 0
                && w.is_on_screen && w.on_current_space == Some(true) && guard.candidates.contains(&w.window_id)
                && visible.windows.iter().filter(|n| n.window_id == w.window_id).count() == 1)
                .map(|w| w.window_id).collect();
            guard
        })
    }

    pub(crate) fn capture_before_file_open(target_pid: i32, complete: &WindowEnumeration,
                                           visible: &WindowEnumeration, target_was_hidden: bool,
                                           opens_file: bool) -> Option<Self> {
        let evidence = reopen_window_evidence(complete, visible)?;
        let new_windows = if opens_file {
            NewWindowEvidence::capture(target_pid,
                crate::ax::enablement::process_start_stamp(target_pid), complete, visible)
        } else { None };
        Self::capture_evidence(target_pid, &evidence, target_was_hidden, new_windows)
    }

    fn capture_evidence(target_pid: i32, windows: &[WindowInfo], target_was_hidden: bool,
                        new_windows: Option<NewWindowEvidence>) -> Option<Self> {
        let activity = crate::foreground_activity::ordering_snapshot();
        if !activity.activity.reliable {
            tracing::debug!(target: "cua_window_order", target_pid, target_was_hidden,
                reason="monitor_unreliable", "Window ordering capture unavailable");
            return None;
        }
        let Some(pid) = crate::apps::frontmost_pid() else {
            tracing::debug!(target: "cua_window_order", target_pid, target_was_hidden,
                reason="foreground_pid_unavailable", "Window ordering capture unavailable");
            return None;
        };
        if pid <= 0 || pid == target_pid {
            tracing::debug!(target: "cua_window_order", pid, target_pid, target_was_hidden,
                reason="target_already_foreground_or_invalid", "Window ordering capture unavailable");
            return None;
        }
        let Some(window) = focused_window(pid) else {
            tracing::debug!(target: "cua_window_order", pid, target_pid, target_was_hidden,
                reason="foreground_ax_window_unavailable", "Window ordering capture unavailable");
            return None;
        };
        let candidates = eligible_before_reopen(windows, pid, window, target_pid, target_was_hidden);
        if exact_visible(windows, pid, window).is_none() || (candidates.is_empty() && new_windows.is_none()) {
            let target_windows: Vec<_> = windows.iter().filter(|w| w.pid == target_pid)
                .map(|w| (w.window_id, w.is_on_screen, w.on_current_space, w.z_index, w.bounds.clone())).collect();
            tracing::debug!(target: "cua_window_order", pid, window, target_pid, target_was_hidden,
                foreground_window_present=exact_visible(windows, pid, window).is_some(),
                ?target_windows, reason="no_eligible_preexisting_window", "Window ordering capture unavailable");
            return None;
        }
        let started = Instant::now();
        let result = Self { pid, window, target_pid, candidates, new_windows,
            tab_inactive: HashSet::new(), tab_sources_below: HashSet::new(), pending_tab: None,
            generation: activity.activity.generation, non_motion_generation: activity.non_motion_generation,
            started, expires_at: started + MAX_AGE, attempted: false,
            trace: Trace::new(),
            #[cfg(test)]
            observed_checks: None,
        };
        if !result.current() { return None; }
        tracing::debug!(target: "cua_window_order", pid, window, target_pid,
            order_trace_id=result.trace.id(),
            candidates=result.candidates.len(), protect_new_documents=result.new_windows.is_some(),
            "Captured background window-order protection");
        Some(result)
    }

    #[cfg(test)]
    pub(crate) fn observing_checks(checks: std::sync::Arc<std::sync::atomic::AtomicUsize>) -> Self {
        let started = Instant::now();
        // No candidate can cross: lifecycle tests observe the real polling
        // path without authorizing any accessibility mutation on the desktop.
        Self { pid: -1, window: 0, target_pid: -2, candidates: HashSet::new(), new_windows: None,
            tab_inactive: HashSet::new(), tab_sources_below: HashSet::new(), pending_tab: None,
            generation: 0, non_motion_generation: 0, started, expires_at: started + MAX_AGE, attempted: false,
            trace: Trace::new(),
            observed_checks: Some(checks) }
    }

    pub(crate) fn limit_deadline(&mut self, deadline: Instant) {
        self.expires_at = self.expires_at.min(deadline);
    }

    pub(crate) fn native_tab_scope(&self, pid: i32, source: u32) -> Option<crate::ax::window_tabs::retained::Scope> {
        let before = self.new_windows.as_ref()?;
        if self.attempted || self.pending_tab.is_some() || pid != self.target_pid
            || !before.known.contains(&source) || !self.tab_sources_below.contains(&source)
            || self.tab_inactive.is_empty() || !self.current() { return None; }
        Some(crate::ax::window_tabs::retained::Scope {
            pid, source, start: before.process_start, deadline: self.expires_at,
        })
    }

    pub(crate) fn confirm_native_tab(&mut self, proof: crate::ax::window_tabs::retained::Destination) {
        let (pid, source, id, start, deadline) = proof.parts();
        let Some(scope) = self.native_tab_scope(pid, source) else { return; };
        if start == scope.start && deadline == scope.deadline
            && self.new_windows.as_ref().and_then(|before| known_tab_destination(&proof, self.target_pid,
                before, &self.tab_sources_below, &self.tab_inactive, self.expires_at)) == Some(id)
            && self.current() {
            // Pending evidence only. The existing guarded poll/report must
            // freshly establish visibility, standard-window ownership and
            // unchanged foreground/activity before it can enroll this one ID.
            self.pending_tab = Some(proof);
        }
    }

    pub(crate) fn diagnostic_trace(&self) -> Trace { self.trace }

    /// AppKit may raise its document during a blocking AX call or after the
    /// action returns. Check only within the owning suppression lease; neither
    /// this guard nor its polling callback creates or extends that lease.
    pub(crate) fn poll(&mut self, deadline: Instant, diagnostics: PollDiagnostics) -> bool {
        self.trace.record_poll(diagnostics);
        let _timing = self.trace.span(Phase::OrderingPoll, Some(diagnostics.source));
        self.limit_deadline(deadline);
        if self.attempted || Instant::now() >= self.expires_at { return false; }
        let latest = crate::windows::visible_windows_with_space_snapshot();
        if !latest.succeeded { return false; }
        self.restore_if_crossed(&latest.windows, diagnostics.source);
        !self.attempted
    }

    fn current(&self) -> bool {
        self.current_evidence().is_some()
    }

    fn current_evidence(&self) -> Option<OrderingSnapshot> {
        let activity = crate::foreground_activity::ordering_snapshot();
        if self.new_windows.as_ref().is_some_and(|new| {
            crate::ax::enablement::process_start_stamp(self.target_pid) != Some(new.process_start)
        }) { return None; }
        if Instant::now() >= self.expires_at {
            tracing::debug!(target: "cua_window_order", pid=self.pid, window=self.window,
                order_trace_id=self.trace.id(),
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
                order_trace_id=self.trace.id(),
                target_pid=self.target_pid, monitor_reliable=activity.activity.reliable,
                original_generation=self.generation, current_generation=activity.activity.generation,
                original_non_motion_generation=self.non_motion_generation,
                current_non_motion_generation=activity.non_motion_generation,
                current_front_pid=?front_pid, current_focused_window=?focused,
                elapsed_ms=elapsed.as_millis(),
                activity_diagnostic=?crate::foreground_activity::ordering_diagnostic_state(),
                "Window ordering guard veto evidence");
        }
        valid.then_some(activity)
    }

    /// One cleanup attempt at most. Unlike focus restoration this must never
    /// activate an app or select a different window: a changed focus vetoes it.
    pub(crate) fn restore_if_crossed(&mut self, windows: &[WindowInfo], source: CheckSource) {
        let _timing = self.trace.span(Phase::OrderingCheck, Some(source));
        #[cfg(test)]
        if let Some(checks) = &self.observed_checks {
            checks.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        if self.attempted { return; }
        if let Some(new) = &self.new_windows {
            let proposed = newly_crossing_windows(windows, self.pid, self.window, self.target_pid, &new.known);
            // A reflex activation is handled by the focus lease. Only enroll
            // its document after the unchanged original window has focus again.
            if !proposed.is_empty() && self.current() {
                let proven = proven_new_documents(self.target_pid, &proposed, self.expires_at);
                if !proven.is_empty() && self.current() {
                    tracing::debug!(target: "cua_window_order", target_pid=self.target_pid,
                        ?proven, "Enrolled new standard documents from the guarded target action");
                    self.candidates.extend(proven);
                }
            }
        }
        let mut tab_candidate = None;
        if let Some(proof) = &self.pending_tab {
            let (pid, _, id, start, deadline) = proof.parts();
            if self.tab_inactive.contains(&id) && self.new_windows.as_ref().is_some_and(|n| n.process_start == start)
                && deadline == self.expires_at && tab_crosses(windows, self.pid, self.window, pid, id)
                && self.current() && tab_document_visible(pid, id, self.expires_at) && self.current() {
                tab_candidate = Some(id);
            }
        }
        if !crossed(windows, self.pid, self.window, self.target_pid, &self.candidates)
            && tab_candidate.is_none() { return; }
        self.attempted = true;
        if !self.current() {
            tracing::debug!(target: "cua_window_order", pid=self.pid, window=self.window,
                order_trace_id=self.trace.id(), check_source=source.label(),
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
        if !latest.succeeded || (!crossed(&latest.windows, self.pid, self.window, self.target_pid, &self.candidates)
            && !tab_candidate.is_some_and(|id| tab_crosses(&latest.windows, self.pid, self.window, self.target_pid, id))) {
            return;
        }
        let Some(admission) = self.current_evidence() else { return; };
        if tab_candidate.is_some() && Instant::now() >= self.expires_at { return; }
        let status = self.trace.measure(Phase::OrderingRaise, Some(source), || unsafe {
            ax::perform_action(window.0, "AXRaise")
        });
        tracing::debug!(target: "cua_window_order", pid=self.pid, window=self.window,
            order_trace_id=self.trace.id(), check_source=source.label(),
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
    fn capture_deadline_is_clamped_before_any_report_or_async_poll() {
        let checks = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let mut guard = BackgroundOrderGuard::observing_checks(checks);
        let original = guard.expires_at;
        guard.limit_deadline(original + Duration::from_secs(30));
        assert_eq!(guard.expires_at, original);
        let expired = Instant::now();
        guard.limit_deadline(expired);
        guard.limit_deadline(original);
        assert_eq!(guard.expires_at, expired);
        assert!(!guard.current());
        assert!(!guard.poll(original, PollDiagnostics {
            source: CheckSource::ActivePoll,
            timing: crate::order_diagnostics::PollTiming {
                wait_started: expired, scheduled_wake: expired, woke: expired,
            },
        }));
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
    fn reopen_uses_visible_stacking_when_complete_inventory_has_different_order() {
        // Recorded on macOS: CG's complete inventory ranks a covered Electron
        // document above the frontmost terminal; the visible snapshot does not.
        let complete = WindowEnumeration { succeeded: true, current_space_id: Some(1),
            windows: vec![window(2, 20, 291), window(1, 10, 62)] };
        let visible = WindowEnumeration { succeeded: true, current_space_id: Some(1),
            windows: vec![window(1, 10, 31), window(2, 20, 30)] };
        let evidence = reopen_window_evidence(&complete, &visible).unwrap();
        assert_eq!(eligible_before_reopen(&evidence, 1, 10, 2, false), HashSet::from([20]));
    }

    #[test]
    fn reopen_preserves_hidden_membership_without_importing_complete_stack_indices() {
        let mut hidden = window(2, 21, 700);
        hidden.is_on_screen = false;
        let complete = WindowEnumeration { succeeded: true, current_space_id: Some(1),
            windows: vec![window(2, 20, 900), hidden, window(2, 22, 800), window(1, 10, 2)] };
        let visible = WindowEnumeration { succeeded: true, current_space_id: Some(1),
            windows: vec![window(1, 10, 31), window(2, 20, 30)] };
        let evidence = reopen_window_evidence(&complete, &visible).unwrap();
        assert_eq!(evidence.len(), 3);
        assert_eq!(eligible_before_reopen(&evidence, 1, 10, 2, false), HashSet::from([20]));
        assert_eq!(eligible_before_reopen(&evidence, 1, 10, 2, true), HashSet::from([20, 21]));
        // An entry claimed visible only in the older full snapshot has no
        // current ordering proof and must not become a restore candidate.
        assert!(!evidence.iter().any(|w| w.window_id == 22));
    }

    #[test]
    fn reopen_fails_closed_when_either_membership_or_visible_snapshot_failed() {
        for (all_ok, visible_ok) in [(false, true), (true, false), (false, false)] {
            let complete = WindowEnumeration { succeeded: all_ok, current_space_id: Some(1),
                windows: vec![window(2, 20, 900), window(1, 10, 2)] };
            let visible = WindowEnumeration { succeeded: visible_ok, current_space_id: Some(1),
                windows: vec![window(1, 10, 31), window(2, 20, 30)] };
            assert!(reopen_window_evidence(&complete, &visible).is_none());
        }
    }

    #[test]
    fn file_open_proposes_only_new_same_process_windows_above_the_original_document() {
        let before = HashSet::from([20, 21]);
        let windows = vec![window(1, 10, 30), window(2, 20, 50), window(2, 22, 40),
            window(2, 23, 20), window(3, 24, 60)];
        assert_eq!(newly_crossing_windows(&windows, 1, 10, 2, &before), vec![22]);
        assert!(newly_crossing_windows(&windows, 1, 10, 1, &before).is_empty());
        assert!(newly_crossing_windows(&windows, 1, 99, 2, &before).is_empty());
        assert!(newly_crossing_windows(&windows, 9, 10, 2, &before).is_empty());
    }

    #[test]
    fn input_created_document_is_distinct_from_preexisting_occluded_windows() {
        let mut hidden = window(2, 21, 800);
        hidden.is_on_screen = false;
        let complete = WindowEnumeration { succeeded: true, current_space_id: Some(1),
            windows: vec![window(2, 20, 900), hidden, window(1, 10, 2)] };
        // A second existing window appears between the two before-snapshots.
        // It must also remain known rather than being claimed by the action.
        let visible = WindowEnumeration { succeeded: true, current_space_id: Some(1),
            windows: vec![window(1, 10, 31), window(2, 20, 30), window(2, 23, 29)] };
        let evidence = NewWindowEvidence::capture(2, Some((100, 200)), &complete, &visible).unwrap();
        assert_eq!(evidence.process_start, (100, 200));
        let after = vec![window(1, 10, 31), window(2, 20, 30), window(2, 21, 32),
            window(2, 23, 33), window(2, 22, 34), window(3, 24, 35)];
        // The vault manager/new document produced by this input is the only
        // proposal. Neither a revealed old document nor another app qualifies.
        assert_eq!(newly_crossing_windows(&after, 1, 10, 2, &evidence.known), vec![22]);
    }

    #[test]
    fn new_input_document_membership_requires_complete_success_and_process_identity() {
        for (all_ok, visible_ok, stamp) in [
            (false, true, Some((100, 200))),
            (true, false, Some((100, 200))),
            (true, true, None),
        ] {
            let complete = WindowEnumeration { succeeded: all_ok, current_space_id: Some(1),
                windows: vec![window(2, 20, 900)] };
            let visible = WindowEnumeration { succeeded: visible_ok, current_space_id: Some(1),
                windows: vec![window(1, 10, 31), window(2, 20, 30)] };
            assert!(NewWindowEvidence::capture(2, stamp, &complete, &visible).is_none());
        }
    }

    #[test]
    fn new_file_windows_need_current_space_overlap_and_ordinary_window_layer() {
        let front = window(1, 10, 30);
        for kind in 0..7 {
            let mut target = window(2, 22, 40);
            match kind {
                0 => target.is_on_screen = false,
                1 => target.on_current_space = Some(false),
                2 => target.on_current_space = None,
                3 => target.layer = 3,
                4 => target.bounds.x = 900.0,
                5 => target.bounds.width = f64::NAN,
                _ => target.bounds.height = 0.0,
            }
            assert!(newly_crossing_windows(&[front.clone(), target], 1, 10, 2, &HashSet::new()).is_empty());
        }
    }

    #[test]
    fn new_file_protection_excludes_dialogs_menus_and_unknown_window_roles() {
        assert!(standard_document(Some("AXWindow"), Some("AXStandardWindow"), Some(false)));
        assert!(standard_document(Some("AXWindow"), Some("AXStandardWindow"), None));
        for (role, subrole, modal) in [
            (Some("AXWindow"), Some("AXStandardWindow"), Some(true)),
            (Some("AXSheet"), Some("AXStandardWindow"), Some(false)),
            (Some("AXWindow"), Some("AXDialog"), Some(false)),
            (Some("AXMenu"), None, None),
            (Some("AXWindow"), None, None),
            (None, Some("AXStandardWindow"), None),
        ] { assert!(!standard_document(role, subrole, modal)); }
    }

    #[test]
    fn exact_hidden_reopen_window_can_cross_without_app_activation() {
        let front = window(1, 10, 30);
        let mut hidden = window(2, 20, 10);
        hidden.is_on_screen = false;
        let before = vec![front.clone(), hidden];
        let ids = eligible_before_reopen(&before, 1, 10, 2, true);
        assert_eq!(ids, HashSet::from([20]));
        assert!(eligible_before_reopen(&before, 1, 10, 2, false).is_empty());
        assert!(!crossed(&before, 1, 10, 2, &ids));
        assert!(crossed(&[window(2, 20, 40), front], 1, 10, 2, &ids));
    }

    #[test]
    fn reopen_never_authorizes_new_other_space_or_other_process_windows() {
        let front = window(1, 10, 30);
        let mut hidden = window(2, 20, 10);
        hidden.is_on_screen = false;
        for space in [Some(false), None] {
            hidden.on_current_space = space;
            assert!(eligible_before_reopen(&[front.clone(), hidden.clone()], 1, 10, 2, true).is_empty());
        }
        hidden.on_current_space = Some(true);
        let before = [front.clone(), hidden];
        let ids = eligible_before_reopen(&before, 1, 10, 2, true);
        assert!(!crossed(&[front.clone(), window(2, 21, 40)], 1, 10, 2, &ids));
        assert!(!crossed(&[front, window(3, 20, 40)], 1, 10, 2, &ids));
        assert!(eligible_before_reopen(&before, 1, 10, 1, true).is_empty());
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
    #[test]
    fn native_tab_membership_uses_the_retained_success_proof_not_new_document_heuristics() {
        let proof = crate::ax::window_tabs::retained::destination_for_guard_test();
        let (_, source, id, start, deadline) = proof.parts();
        let before = NewWindowEvidence { known: HashSet::from([source, id, 30]), process_start: start };
        let visible = HashSet::from([source]); let inactive = HashSet::from([id, 30]);
        assert_eq!(known_tab_destination(&proof, 42, &before, &visible, &inactive, deadline), Some(id));
        // Simultaneously revealed old30 remains excluded, as does the original
        // known-id set from the new-document route.
        let after = vec![window(1, 1, 10), window(42, id, 11), window(42, 30, 12)];
        assert!(newly_crossing_windows(&after, 1, 1, 42, &before.known).is_empty());
        assert!(tab_crosses(&after, 1, 1, 42, id));
        assert!(!tab_crosses(&[window(1, 1, 10), window(42, id, 9), window(42, 30, 12)], 1, 1, 42, id));
        for fault in 0..7 {
            let mut before = NewWindowEvidence { known: HashSet::from([source, id]), process_start: start };
            let mut visible = HashSet::from([source]); let mut inactive = HashSet::from([id]);
            let mut target = 42; let mut limit = deadline;
            match fault { 0 => { before.known.remove(&id); }, 1 => { visible.insert(id); },
                2 => { inactive.clear(); }, 3 => before.process_start = (9, 9),
                4 => target = 99, 5 => limit = deadline - Duration::from_millis(1), _ => visible.clear() }
            assert!(known_tab_destination(&proof, target, &before, &visible, &inactive, limit).is_none());
        }
    }

    #[test]
    fn native_tab_inactive_membership_needs_complete_success_and_unique_before_ids() {
        let mut hidden = window(42, 20, 1); hidden.is_on_screen = false;
        let mut complete = WindowEnumeration { succeeded: true, current_space_id: Some(1), windows: vec![window(42, 10, 3), hidden.clone()] };
        let mut visible = WindowEnumeration { succeeded: true, current_space_id: Some(1), windows: vec![window(42, 10, 3)] };
        assert_eq!(inactive_tab_windows(42, &complete, &visible), HashSet::from([20]));
        visible.succeeded = false; assert!(inactive_tab_windows(42, &complete, &visible).is_empty());
        visible.succeeded = true; complete.succeeded = false;
        assert!(inactive_tab_windows(42, &complete, &visible).is_empty());
        complete.succeeded = true; complete.windows.push(hidden);
        assert!(inactive_tab_windows(42, &complete, &visible).is_empty());
    }

    #[test]
    fn native_tab_current_crossing_refuses_foreign_unknown_space_duplicate_and_peer_only_order() {
        for fault in 0..9 {
            let mut target = window(42, 20, 11); let mut windows = vec![window(1, 1, 10)];
            match fault { 0 => target.pid = 99, 1 => target.layer = 1, 2 => target.is_on_screen = false,
                3 => target.on_current_space = None, 4 => target.on_current_space = Some(false),
                5 => target.bounds.x = 1000.0, 6 => target.bounds.width = f64::NAN,
                7 => windows.push(target.clone()), _ => target.z_index = 9 }
            windows.push(target); assert!(!tab_crosses(&windows, 1, 1, 42, 20), "fault {fault}");
        }
    }

}
