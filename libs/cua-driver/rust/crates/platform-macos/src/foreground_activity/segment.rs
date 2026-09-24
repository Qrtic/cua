//! Cross-RPC ownership. No background timer activates or restores a window.
use super::*;
use cua_driver_core::{
    background_input::ExactWindowTarget,
    foreground_segment::{
        Binding, CallKind, Cleanup, Limits, Owner, Reservation, Segment, State as SegmentState,
    },
    protocol::ToolResult,
};
use serde_json::{json, Value};
use std::collections::VecDeque;

struct Resources {
    background: Arc<tokio::sync::OwnedMutexGuard<()>>,
    _foreground: tokio::sync::OwnedMutexGuard<()>,
}

struct Inner {
    policy: Segment,
    resources: Option<Resources>,
    ending: bool,
    restoring: bool,
    activated: bool,
    dialog_closed: bool,
    dialog_closed_destination: Option<ExactWindowTarget>,
    dialog_target: Option<crate::ax::attached_sheet::DialogAttachment>,
    dialog_observation_required: bool,
    cleanup_unknown: bool,
    summary: Option<Value>,
}

struct NativeSegment {
    binding: Binding,
    owner: Arc<cua_driver_core::session::TransportOwner>,
    original: ExactWindowTarget,
    dialog_host: Option<ExactWindowTarget>,
    dialog_panel: Option<u32>,
    inner: Mutex<Inner>,
}

fn registry() -> &'static Mutex<VecDeque<Arc<NativeSegment>>> {
    static REGISTRY: OnceLock<Mutex<VecDeque<Arc<NativeSegment>>>> = OnceLock::new();
    REGISTRY.get_or_init(|| Mutex::new(VecDeque::new()))
}

fn cleanup_latch() -> &'static AtomicBool {
    static UNKNOWN: AtomicBool = AtomicBool::new(false);
    &UNKNOWN
}

fn all_segments() -> Vec<Arc<NativeSegment>> {
    registry()
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .iter()
        .cloned()
        .collect()
}

fn failure(code: &str, message: &str, refused: bool) -> ToolResult {
    ToolResult::error(message).with_structured(json!({
        "code": code, "effect": if refused { "refused" } else { "unverifiable" },
        "retryable": false,
    }))
}

fn admission_failure(reason: &str, message: &str) -> ToolResult {
    ToolResult::error(message).with_structured(json!({
        "code": "foreground_activity_unavailable", "effect": "refused", "retryable": false,
        "foreground_failure": {"reason": reason},
    }))
}

fn owner_from_args(
    args: &Value,
) -> Result<(Owner, Arc<cua_driver_core::session::TransportOwner>), ToolResult> {
    let refuse = || {
        failure(
            "foreground_segment_owner_unavailable",
            "A live canonical native transport, session and runtime are required",
            true,
        )
    };
    let session_id = args
        .get("_session_id")
        .and_then(Value::as_str)
        .filter(|s| !s.is_empty())
        .ok_or_else(refuse)?;
    let transport_session_id = args
        .get("_transport_session_id")
        .and_then(Value::as_str)
        .filter(|s| !s.is_empty())
        .ok_or_else(refuse)?;
    let runtime_scope =
        cua_driver_core::tool::current_dispatch_runtime_scope().ok_or_else(refuse)?;
    let owner = cua_driver_core::session::current_transport_owner_for(transport_session_id)
        .ok_or_else(refuse)?;
    if cua_driver_core::session::is_session_ending_or_ended(session_id)
        || cua_driver_core::session::is_runtime_scope_suspended(&runtime_scope)
    {
        return Err(refuse());
    }
    Ok((
        Owner {
            runtime_scope,
            session_id: session_id.into(),
            transport_session_id: transport_session_id.into(),
        },
        owner,
    ))
}

fn target_from_args(args: &Value) -> Result<ExactWindowTarget, ToolResult> {
    let pid = args
        .get("pid")
        .and_then(Value::as_i64)
        .and_then(|v| i32::try_from(v).ok())
        .filter(|v| *v > 0);
    let window_id = args
        .get("window_id")
        .and_then(Value::as_u64)
        .and_then(|v| u32::try_from(v).ok())
        .filter(|v| *v > 0);
    match (pid, window_id) {
        (Some(pid), Some(window_id)) => Ok(ExactWindowTarget { pid, window_id }),
        _ => Err(failure(
            "foreground_segment_target_invalid",
            "An exact positive native PID and window ID are required",
            true,
        )),
    }
}

fn lookup(args: &Value) -> Result<Arc<NativeSegment>, ToolResult> {
    let (owner, transport) = owner_from_args(args)?;
    let target = target_from_args(args)?;
    let id = args
        .get("foreground_segment_id")
        .and_then(Value::as_str)
        .filter(|id| !id.is_empty() && id.len() <= 128)
        .ok_or_else(|| {
            failure(
                "foreground_segment_invalid",
                "A bounded segment token is required",
                true,
            )
        })?;
    let segment = all_segments()
        .into_iter()
        .find(|segment| segment.binding.id == id)
        .ok_or_else(|| {
            failure(
                "foreground_segment_invalid",
                "Segment is unknown or retired",
                true,
            )
        })?;
    if !binding_matches(&segment, &owner, target, &transport) {
        return Err(failure(
            "foreground_segment_owner_mismatch",
            "Segment owner or exact target does not match this native request",
            true,
        ));
    }
    Ok(segment)
}

fn binding_matches(
    segment: &NativeSegment,
    owner: &Owner,
    target: ExactWindowTarget,
    transport: &Arc<cua_driver_core::session::TransportOwner>,
) -> bool {
    segment.binding.owner == *owner
        && (segment.binding.target == target
            || (segment.dialog_host.is_some() && segment.current_target() == target))
        && Arc::ptr_eq(&segment.owner, transport)
}

impl NativeSegment {
    fn current_target(&self) -> ExactWindowTarget {
        let inner = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        inner
            .dialog_target
            .as_ref()
            .map_or(self.binding.target, |dialog| ExactWindowTarget {
                pid: self.binding.target.pid,
                window_id: dialog.window_id,
            })
    }

    fn expected_front(&self) -> ExactWindowTarget {
        let activated = self
            .inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .activated;
        if activated {
            self.current_target()
        } else {
            self.original
        }
    }

    fn cleanup_is_settled(&self) -> bool {
        let inner = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        !inner.policy.in_flight()
            && !inner.ending
            && !inner.restoring
            && !inner.cleanup_unknown
            && inner.resources.is_none()
    }

    fn accept_dialog_return(&self) -> bool {
        let destination = self
            .inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .dialog_closed_destination;
        let Some(host) = destination.or(self.dialog_host) else {
            return false;
        };
        if !self
            .inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .activated
            || !exact_front(host)
            || !crate::ax::attached_sheet::dialog_returned_to_host(
                self.binding.target.pid,
                self.dialog_panel.unwrap_or(self.binding.target.window_id),
                host.window_id,
            )
        {
            return false;
        }
        let mut inner = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        inner.dialog_closed = true;
        inner.dialog_closed_destination = Some(host);
        true
    }

    fn dialog_closed(&self) -> bool {
        self.inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .dialog_closed
    }

    fn validate_dialog_call(
        &self,
        tool: &str,
        target: ExactWindowTarget,
    ) -> Result<(), ToolResult> {
        if tool == "prepare_dialog" && self.dialog_host.is_none() {
            return Err(failure(
                "foreground_dialog_required",
                "Preparing a dialog requires a proven Open/Save dialog segment",
                true,
            ));
        }
        if self.dialog_host.is_some() {
            let inner = self.inner.lock().unwrap_or_else(|e| e.into_inner());
            if inner
                .dialog_target
                .as_ref()
                .is_some_and(|dialog| dialog.window_id != target.window_id)
            {
                return Err(failure("foreground_dialog_target_changed",
                    "The attached dialog changed; observe its new exact window before further input", true));
            }
            if inner.dialog_observation_required && tool != "get_window_state" {
                return Err(failure("foreground_dialog_observation_required",
                    "Observe the new attached dialog before sending another action; no input was sent", true));
            }
        }
        if self.dialog_closed() {
            return Err(failure(
                "foreground_dialog_closed",
                "The dialog closed onto its exact host; finish this segment before observing or acting again",
                true,
            ));
        }
        Ok(())
    }

    fn owner_live(&self) -> bool {
        self.owner.is_live()
            && !cua_driver_core::session::is_session_ending_or_ended(&self.binding.owner.session_id)
            && !cua_driver_core::session::is_runtime_scope_suspended(
                &self.binding.owner.runtime_scope,
            )
    }

    fn check_liveness(&self) -> anyhow::Result<()> {
        let mut inner = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        if inner.cleanup_unknown {
            anyhow::bail!("native_cleanup_unconfirmed");
        }
        if !self.owner_live() {
            inner.policy.revoke();
        }
        inner
            .policy
            .check(&self.binding, clock_ms(), snapshot())
            .map_err(|reason| {
                tracing::warn!(?reason, "foreground segment activity/owner check failed");
                anyhow::anyhow!(
                    "foreground_activity_interrupted: foreground segment is no longer live"
                )
            })
    }

    fn check(&self) -> anyhow::Result<()> {
        self.check_liveness()?;
        let expected = self.expected_front();
        let focus_live =
            LEASE.with(Cell::get).is_some() || exact_front(expected) || self.accept_dialog_return();
        if !focus_live {
            tracing::warn!(pid=expected.pid, window_id=expected.window_id,
                focused_window_id=?bounded_focused_window(expected.pid),
                "foreground segment exact focus changed outside a proven dialog transition");
            self.inner
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .policy
                .revoke();
        }
        self.check_liveness()
    }

    fn summary(&self, restoration: &str) -> Value {
        json!({"foreground_segment_id": self.binding.id, "phase": "closed",
               "pid": self.binding.target.pid, "window_id": self.binding.target.window_id,
               "cleanup_confirmed": true, "restoration": restoration})
    }

    fn revoke(&self) {
        self.inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .policy
            .revoke();
        self.settle_revoked();
    }

    fn mark_unknown(&self) {
        cleanup_latch().store(true, Ordering::Release);
        let mut inner = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        inner.cleanup_unknown = true;
        inner.policy.revoke();
        if !inner.policy.in_flight() {
            let _ = inner.policy.finish_cleanup(Cleanup::Unknown);
        }
    }

    fn settle_revoked(&self) {
        let mut inner = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        if inner.restoring
            || inner.policy.in_flight()
            || inner.policy.state() != SegmentState::Revoked
        {
            return;
        }
        if inner.cleanup_unknown {
            let _ = inner.policy.finish_cleanup(Cleanup::Unknown);
        } else {
            if inner.policy.finish_cleanup(Cleanup::Confirmed).is_err() {
                inner.cleanup_unknown = true;
                cleanup_latch().store(true, Ordering::Release);
                return;
            }
            inner.ending = false;
            inner.summary = Some(self.summary("skipped_interrupted"));
            inner.resources.take();
        }
    }

    fn finish_restore(&self, restoration: &str) -> Option<Value> {
        let mut inner = self.inner.lock().unwrap_or_else(|e| e.into_inner());
        inner.ending = false;
        inner.restoring = false;
        if inner.cleanup_unknown {
            let _ = inner.policy.finish_cleanup(Cleanup::Unknown);
            return None;
        }
        if inner.policy.finish_cleanup(Cleanup::Confirmed).is_err() {
            return None;
        }
        let summary = self.summary(restoration);
        inner.summary = Some(summary.clone());
        inner.resources.take();
        Some(summary)
    }
}

/// An invocation ticket settles only after its async scope AND blocking workers.
pub(super) struct Call {
    segment: Arc<NativeSegment>,
    target: ExactWindowTarget,
    dialog_transition: Mutex<Option<Value>>,
    reservation: Mutex<Option<Reservation>>,
}

impl Call {
    pub(super) fn target(&self) -> ExactWindowTarget {
        self.target
    }
    pub(super) fn activity_lease(&self) -> EpisodeLease {
        self.segment
            .inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .policy
            .activity_lease()
    }
    pub(super) fn check(&self) -> anyhow::Result<()> {
        self.segment.check()
    }
    pub(super) fn revoke(&self) {
        self.segment.revoke();
    }
    pub(super) fn cleanup_unknown(&self) {
        self.segment.mark_unknown();
    }
    pub(super) fn cleanup_is_unknown(&self) -> bool {
        self.segment
            .inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .cleanup_unknown
    }
    pub(super) fn mark_activated(&self) {
        self.segment
            .inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .activated = true;
    }
    pub(super) fn background_lease(
        &self,
        pid: i32,
    ) -> Option<Arc<tokio::sync::OwnedMutexGuard<()>>> {
        if pid != self.target().pid {
            return None;
        }
        self.segment
            .inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .resources
            .as_ref()
            .map(|resources| Arc::clone(&resources.background))
    }
    pub(super) fn settle(&self) {
        if let Some(reservation) = self
            .reservation
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .take()
        {
            let failed = {
                self.segment
                    .inner
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .policy
                    .settle(reservation)
                    .is_err()
            };
            if failed {
                self.segment.mark_unknown();
            }
        }
        self.segment.settle_revoked();
    }
    pub(super) fn closed_summary(&self) -> Option<Value> {
        self.segment
            .inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .summary
            .clone()
    }
    pub(super) fn is_dialog(&self) -> bool {
        self.segment.dialog_host.is_some()
    }

    pub(super) fn mark_dialog_observed(&self) {
        let mut inner = self.segment.inner.lock().unwrap_or_else(|e| e.into_inner());
        if inner
            .dialog_target
            .as_ref()
            .is_some_and(|dialog| dialog.window_id == self.target.window_id)
        {
            inner.dialog_observation_required = false;
        }
    }

    pub(super) fn settle_dialog_return(
        &self,
        mut check_live: impl FnMut() -> anyhow::Result<()>,
    ) -> anyhow::Result<bool> {
        if !self.is_dialog() {
            return Ok(false);
        }
        // Post-dispatch read only. A nested sheet may change AX focus before
        // WindowServer finishes its animation. Preserve the ORIGINAL lease,
        // owner, panel and deadline. No input can use the new target until a
        // fresh observation; the current call's exact target never changes.
        let started = Instant::now();
        let settled = settle_dialog_condition(
            Duration::from_millis(350),
            || {
                check_live()?;
                self.segment.check_liveness()
            },
            || {
                if exact_front(self.segment.current_target()) || self.segment.accept_dialog_return()
                {
                    return true;
                }
                if let (Some(host), Some(panel)) =
                    (self.segment.dialog_host, self.segment.dialog_panel)
                {
                    if let Some(window_id) = crate::ax::attached_sheet::replaced_dialog_host(
                        self.target.pid,
                        panel,
                        host.window_id,
                    ) {
                        let destination = ExactWindowTarget {
                            pid: self.target.pid,
                            window_id,
                        };
                        if exact_front(destination) {
                            let mut inner =
                                self.segment.inner.lock().unwrap_or_else(|e| e.into_inner());
                            if inner
                                .policy
                                .check(&self.segment.binding, clock_ms(), snapshot())
                                .is_ok()
                            {
                                inner.dialog_closed = true;
                                inner.dialog_closed_destination = Some(destination);
                                return true;
                            }
                        }
                    }
                }
                let before = self
                    .segment
                    .inner
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .dialog_target
                    .clone();
                let after = bounded_focused_window(self.target.pid).and_then(|id| {
                    exact_front(ExactWindowTarget {
                        pid: self.target.pid,
                        window_id: id,
                    })
                    .then(|| {
                        crate::ax::attached_sheet::focused_dialog_attachment(self.target.pid, id)
                    })
                    .flatten()
                });
                let (Some(before), Some(after)) = (before, after) else {
                    return false;
                };
                let closed =
                    crate::ax::attached_sheet::sheet_is_closed(self.target.pid, before.window_id);
                if !dialog_transition_allowed(&before, &after, closed)
                    || !exact_front(ExactWindowTarget {
                        pid: self.target.pid,
                        window_id: after.window_id,
                    })
                {
                    return false;
                }
                let mut inner = self.segment.inner.lock().unwrap_or_else(|e| e.into_inner());
                if inner.dialog_target.as_ref() != Some(&before) {
                    return false;
                }
                // Revocation/timer and adoption share the policy lock. The
                // surrounding settlement also checks activity after this read.
                if inner
                    .policy
                    .check(&self.segment.binding, clock_ms(), snapshot())
                    .is_err()
                {
                    return false;
                }
                *self
                    .dialog_transition
                    .lock()
                    .unwrap_or_else(|e| e.into_inner()) = Some(json!({
                    "phase":"transitioned", "foreground_segment_id":self.segment.binding.id,
                    "pid":self.target.pid, "window_id":self.target.window_id,
                    "target_window_id":after.window_id, "observation_required":true,
                }));
                inner.dialog_target = Some(after);
                inner.dialog_observation_required = true;
                true
            },
        );
        if matches!(settled, Ok(false)) {
            let windows = crate::windows::all_windows_including_accessory_layers_with_snapshot();
            let relevant: Vec<_> = windows
                .windows
                .iter()
                .filter(|window| window.pid == self.target.pid)
                .take(64)
                .map(|window| (window.window_id, window.is_on_screen))
                .collect();
            tracing::warn!(pid=self.target.pid, window_id=self.target.window_id,
                host=?self.segment.dialog_host, panel=?self.segment.dialog_panel,
                focused_window_id=?bounded_focused_window(self.target.pid),
                elapsed_ms=started.elapsed().as_millis(), snapshot_succeeded=windows.succeeded,
                windows=?relevant, "dialog settlement could not prove the resulting window");
        }
        settled
    }

    pub(super) fn dialog_closed_summary(&self) -> Option<Value> {
        if self.segment.dialog_closed() {
            Some(json!({
                "phase": "closed", "foreground_segment_id": self.segment.binding.id,
                "pid": self.target.pid, "window_id": self.target.window_id,
            }))
        } else {
            self.dialog_transition
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .clone()
        }
    }
}

fn dialog_transition_allowed(
    before: &crate::ax::attached_sheet::DialogAttachment,
    after: &crate::ax::attached_sheet::DialogAttachment,
    previous_sheet_closed: bool,
) -> bool {
    before.panel_id == after.panel_id
        && before.host_id == after.host_id
        && before.window_id != after.window_id
        && (after.path.contains(&before.window_id)
            || (previous_sheet_closed && before.path.contains(&after.window_id)))
}

fn settle_dialog_condition(
    budget: Duration,
    mut check_live: impl FnMut() -> anyhow::Result<()>,
    mut probe: impl FnMut() -> bool,
) -> anyhow::Result<bool> {
    let deadline = Instant::now() + budget;
    loop {
        check_live()?;
        let returned = probe();
        // A successful AX/WindowServer read cannot override intervening input,
        // cancellation, ended ownership or an exhausted native segment.
        check_live()?;
        if returned {
            return Ok(true);
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Ok(false);
        }
        std::thread::sleep(remaining.min(Duration::from_millis(10)));
    }
}

impl Drop for Call {
    fn drop(&mut self) {
        // Unwinding/early refusal is not a licence to keep an unowned segment open.
        let reserved = self
            .reservation
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .is_some();
        if reserved {
            self.revoke();
            self.settle();
        }
    }
}

fn supported_tool(name: &str) -> bool {
    matches!(
        name,
        "click"
            | "double_click"
            | "right_click"
            | "drag"
            | "scroll"
            | "type_text"
            | "press_key"
            | "hotkey"
            | "set_value"
            | "perform_secondary_action"
            | "get_window_state"
            | "prepare_dialog"
    )
}

fn validate_element_target(
    args: &Value,
    target: ExactWindowTarget,
    tool: &str,
) -> Result<(), ToolResult> {
    if args
        .get("element_token")
        .is_some_and(|value| !value.is_string())
    {
        return Err(failure(
            "foreground_segment_target_invalid",
            "Segment element token must be a valid exact-window token",
            true,
        ));
    }
    let resolved = cua_driver_core::element_token::resolve_element_args(
        target.pid,
        args.get("element_index")
            .and_then(Value::as_u64)
            .and_then(|index| usize::try_from(index).ok()),
        args.get("element_token").and_then(Value::as_str),
        args.get("snapshot_id").and_then(Value::as_str),
        Some(u64::from(target.window_id)),
        tool,
    )
    .map_err(|_| {
        failure(
            "foreground_segment_target_invalid",
            "Segment element target is invalid or stale; no input was sent",
            true,
        )
    })?;
    if matches!(resolved, cua_driver_core::element_token::ResolvedElement::Element { window_id: Some(window), .. } if window != target.window_id)
    {
        return Err(failure(
            "foreground_segment_target_mismatch",
            "Element token belongs to a different exact window; no input was sent",
            true,
        ));
    }
    Ok(())
}

pub(super) fn admit_call(args: &Value, tool: &str) -> Result<Option<Arc<Call>>, ToolResult> {
    if cleanup_latch().load(Ordering::Acquire) {
        return Err(failure(
            "native_cleanup_unconfirmed",
            "Native segment cleanup is unknown; stop all GUI work",
            false,
        ));
    }
    if args.get("foreground_segment_id").is_none() {
        if let Some(pid) = args.get("pid").and_then(Value::as_i64) {
            if all_segments().iter().any(|segment| {
                segment.binding.target.pid as i64 == pid
                    && segment
                        .inner
                        .lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .resources
                        .is_some()
            }) {
                return Err(failure(
                    "foreground_segment_required",
                    "This process belongs to an active foreground segment",
                    true,
                ));
            }
        }
        return Ok(None);
    }
    let segment = lookup(args)?;
    if !supported_tool(tool) {
        return Err(failure(
            "foreground_segment_action_unsupported",
            "This action is not supported within an exact-window foreground segment",
            true,
        ));
    }
    if tool == "get_window_state"
        && args
            .get("window_selection")
            .and_then(Value::as_str)
            .is_some_and(|selection| selection != "exact")
    {
        return Err(failure(
            "foreground_segment_target_invalid",
            "Segment observations must retain their exact window target",
            true,
        ));
    }
    let target = target_from_args(args)?;
    validate_element_target(args, target, tool)?;
    segment.check().map_err(|_| {
        failure(
            "foreground_activity_interrupted",
            "Segment activity or ownership ended; no new call admitted",
            true,
        )
    })?;
    segment.validate_dialog_call(tool, target)?;
    let reservation = segment
        .inner
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .policy
        .reserve(
            &segment.binding,
            clock_ms(),
            snapshot(),
            if tool == "prepare_dialog" {
                CallKind::Activation
            } else if tool == "get_window_state" {
                CallKind::Observation
            } else {
                CallKind::Mutation
            },
        )
        .map_err(|_| {
            failure(
                "foreground_segment_not_available",
                "Segment is busy, ended or exhausted; no new call admitted",
                true,
            )
        })?;
    Ok(Some(Arc::new(Call {
        segment,
        target,
        dialog_transition: Mutex::new(None),
        reservation: Mutex::new(Some(reservation)),
    })))
}

fn exact_front(target: ExactWindowTarget) -> bool {
    crate::input::skylight::front_process_matches(target.pid, target.window_id) == Some(true)
        && bounded_focused_window(target.pid) == Some(target.window_id)
}

fn bounded_focused_window(pid: i32) -> Option<u32> {
    use crate::ax::bindings::*;
    struct Owned(AXUIElementRef);
    impl Drop for Owned {
        fn drop(&mut self) {
            unsafe { core_foundation::base::CFRelease(self.0 as _) };
        }
    }
    unsafe {
        let app = AXUIElementCreateApplication(pid);
        if app.is_null() {
            return None;
        }
        let app = Owned(app);
        if AXUIElementSetMessagingTimeout(app.0, 0.1) != kAXErrorSuccess {
            return None;
        }
        let window = Owned(copy_element_attr(app.0, "AXFocusedWindow")?);
        if AXUIElementSetMessagingTimeout(window.0, 0.1) != kAXErrorSuccess {
            return None;
        }
        ax_get_window_id(window.0)
    }
}

pub(crate) async fn begin_segment(args: Value) -> ToolResult {
    let (owner, transport) = match owner_from_args(&args) {
        Ok(owner) => owner,
        Err(result) => return result,
    };
    let target = match target_from_args(&args) {
        Ok(target) => target,
        Err(result) => return result,
    };
    let dialog = match args.get("scope").and_then(Value::as_str) {
        None | Some("batch") => false,
        Some("dialog") => true,
        _ => {
            return failure(
                "foreground_segment_scope_invalid",
                "Segment scope must be batch or dialog",
                true,
            )
        }
    };
    if cleanup_latch().load(Ordering::Acquire) {
        return failure(
            "native_cleanup_unconfirmed",
            "Native cleanup is unknown; no segment can begin",
            false,
        );
    }
    let background = match tokio::time::timeout(
        Duration::from_millis(100),
        crate::background_mutation::acquire(target.pid),
    )
    .await
    {
        Ok(guard) => Arc::new(guard),
        Err(_) => {
            return failure(
                "foreground_segment_busy",
                "Target mutation ownership is busy",
                true,
            )
        }
    };
    let foreground = match foreground_writer().try_lock_owned() {
        Ok(guard) => guard,
        Err(_) => {
            return failure(
                "foreground_segment_busy",
                "Native foreground ownership is busy",
                true,
            )
        }
    };
    let binding = Binding {
        owner,
        target,
        id: format!("fgs_{}", uuid::Uuid::new_v4().simple()),
    };
    let activity = snapshot();
    let mut policy = match Segment::begin(binding.clone(), clock_ms(), activity, Limits::default())
    {
        Ok(policy) => policy,
        Err(_) => {
            return admission_refusal(
                activity_admission_reason(activity),
                activity,
                "Five seconds of reliable idle are required",
            );
        }
    };
    // No activation or other write in begin. A cancelled capture cannot leave input.
    let (original, attachment) = match tokio::task::spawn_blocking(move || {
        if !matches!(
            crate::windows::resolve_window_owner(target.pid, target.window_id),
            crate::windows::WindowOwner::SamePid
        ) {
            return Err("target_window_unavailable");
        }
        let attachment = if dialog {
            Some(crate::ax::attached_sheet::focused_dialog_attachment(target.pid, target.window_id)
                .ok_or("dialog_attachment_unproven")?)
        } else { None };
        let pid = crate::apps::frontmost_pid().ok_or("original_frontmost_unavailable")?;
        let original = ExactWindowTarget {
            pid,
            window_id: bounded_focused_window(pid).ok_or("original_focused_window_unavailable")?,
        };
        (exact_front(original)
            && matches!(
                crate::windows::resolve_window_owner(original.pid, original.window_id),
                crate::windows::WindowOwner::SamePid
            ))
        .then_some((original, attachment))
        .ok_or("original_window_unproven")
    })
    .await
    {
        Ok(Ok(proof)) => proof,
        result => {
            return admission_failure(
                match result { Ok(Err(reason)) => reason, _ => "native_evidence_worker_failed" },
                "Exact original window, target ownership, or requested Open/Save attachment is unavailable",
            )
        }
    };
    if !transport.is_live()
        || cua_driver_core::session::is_session_ending_or_ended(&binding.owner.session_id)
        || cua_driver_core::session::is_runtime_scope_suspended(&binding.owner.runtime_scope)
        || policy.check(&binding, clock_ms(), snapshot()).is_err()
    {
        return admission_failure(
            "native_admission_changed",
            "Foreground admission changed during preparation",
        );
    }
    let segment = Arc::new(NativeSegment {
        binding,
        owner: transport,
        original,
        dialog_host: attachment.as_ref().map(|a| ExactWindowTarget {
            pid: target.pid,
            window_id: a.host_id,
        }),
        dialog_panel: attachment.as_ref().map(|a| a.panel_id),
        inner: Mutex::new(Inner {
            policy,
            resources: Some(Resources {
                background,
                _foreground: foreground,
            }),
            ending: false,
            restoring: false,
            activated: false,
            dialog_closed: false,
            dialog_closed_destination: None,
            dialog_target: attachment,
            dialog_observation_required: false,
            cleanup_unknown: false,
            summary: None,
        }),
    });
    {
        let mut entries = registry().lock().unwrap_or_else(|e| e.into_inner());
        while entries.len() >= 64 {
            if let Some(index) = entries.iter().position(|entry| {
                entry
                    .inner
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .resources
                    .is_none()
            }) {
                entries.remove(index);
            } else {
                return failure(
                    "foreground_segment_busy",
                    "Native segment registry is full",
                    true,
                );
            }
        }
        entries.push_back(Arc::clone(&segment));
    }
    let watched = Arc::clone(&segment);
    tokio::spawn(async move {
        loop {
            tokio::time::sleep(Duration::from_millis(50)).await;
            let (state, deadline, lease) = {
                let inner = watched.inner.lock().unwrap_or_else(|e| e.into_inner());
                (
                    inner.policy.state(),
                    inner.policy.deadline_ms(),
                    inner.policy.activity_lease(),
                )
            };
            if matches!(state, SegmentState::Closed | SegmentState::CleanupUnknown) {
                break;
            }
            // Closing after a call/step budget is exhausted is not a new lease:
            // a client that disappears without end must still expire. The timer
            // only revokes ownership and never moves focus or emits input.
            if !watched.owner_live()
                || clock_ms() >= deadline
                || !lease.permits(clock_ms(), snapshot())
            {
                watched.revoke();
            }
            watched.settle_revoked();
        }
    });
    ToolResult::text("Native foreground segment opened; no window activation or input dispatched.").with_structured(json!({
        "foreground_segment_id": segment.binding.id, "phase": "open", "pid": target.pid, "window_id": target.window_id,
        "scope": if dialog { "dialog" } else { "batch" },
    }))
}

/// Activation is a separately admitted native call. It emits no click/key and
/// does not mint AX tokens; the wrapper observes once after exact readiness.
pub(crate) async fn prepare_dialog(args: Value) -> ToolResult {
    let target = match target_from_args(&args) {
        Ok(target) => target,
        Err(result) => return result,
    };
    let Some(call) = current_invocation().and_then(|context| context.segment_call.clone()) else {
        return failure(
            "foreground_dialog_required",
            "A live native dialog segment is required",
            true,
        );
    };
    if call.segment.dialog_host.is_none() || call.target() != target {
        return failure(
            "foreground_dialog_required",
            "Dialog segment target does not match",
            true,
        );
    }
    let expected_host = call.segment.dialog_host.unwrap();
    let prepared = spawn_blocking(move || {
        check_request()?;
        if crate::ax::attached_sheet::focused_dialog_host(target.pid, target.window_id)
            != Some(expected_host.window_id)
        {
            anyhow::bail!("dialog attachment changed before activation");
        }
        crate::input::skylight::with_foreground_hid_activation(target.pid, target.window_id, || {
            Ok(())
        })
    })
    .await;
    match prepared {
        Ok(Ok(())) => ToolResult::text("Exact Open/Save dialog is ready for a fresh observation; no click or key was sent.")
            .with_structured(json!({"phase":"prepared", "pid":target.pid, "window_id":target.window_id,
                "foreground_segment_id":call.segment.binding.id})),
        _ => ToolResult::error("Dialog preparation did not establish exact foreground readiness; finish or abort the segment without replaying input.")
            .with_structured(json!({"code":"foreground_dialog_preparation_failed", "effect":"unverifiable", "retryable":false})),
    }
}

fn claim_end(inner: &mut Inner, binding: &Binding, finish: bool) -> Result<(), ToolResult> {
    if inner.ending || inner.restoring {
        return Err(failure(
            "foreground_segment_busy",
            "Segment end is already running",
            false,
        ));
    }
    inner.policy.request_close(binding).map_err(|_| {
        failure(
            "foreground_segment_not_available",
            "Segment cannot close",
            false,
        )
    })?;
    // Claim exclusive end ownership under the same lock BEFORE any wait for
    // native workers. No second end may queue another restore behind us.
    inner.ending = true;
    if !finish {
        inner.policy.revoke();
    }
    Ok(())
}

pub(crate) async fn end_segment(args: Value) -> ToolResult {
    let segment = match lookup(&args) {
        Ok(segment) => segment,
        Err(result) => return result,
    };
    let finish = match args.get("mode").and_then(Value::as_str) {
        Some("finish") => true,
        Some("abort") => false,
        _ => {
            return failure(
                "foreground_segment_end_invalid",
                "End mode must be finish or abort",
                true,
            )
        }
    };
    {
        let mut inner = segment.inner.lock().unwrap_or_else(|e| e.into_inner());
        if inner.cleanup_unknown {
            return failure(
                "native_cleanup_unconfirmed",
                "Segment cleanup is unknown",
                false,
            );
        }
        if let Some(summary) = &inner.summary {
            return ToolResult::text("Segment is already closed.").with_structured(summary.clone());
        }
        if let Err(refusal) = claim_end(&mut inner, &segment.binding, finish) {
            return refusal;
        }
    }
    struct EndGuard {
        segment: Arc<NativeSegment>,
        context: Option<Arc<InvocationContext>>,
        completed: bool,
    }
    impl Drop for EndGuard {
        fn drop(&mut self) {
            if !self.completed {
                if let Some(context) = &self.context {
                    context.cancelled.store(true, Ordering::Release);
                }
                {
                    let mut inner = self.segment.inner.lock().unwrap_or_else(|e| e.into_inner());
                    if !inner.restoring {
                        inner.ending = false;
                    }
                }
                self.segment.revoke();
            }
        }
    }
    let mut guard = EndGuard {
        segment: Arc::clone(&segment),
        context: None,
        completed: false,
    };
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        if !segment
            .inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .policy
            .in_flight()
        {
            break;
        }
        if Instant::now() >= deadline {
            segment.mark_unknown();
            return failure(
                "native_cleanup_unconfirmed",
                "Segment workers did not settle within the cleanup bound",
                false,
            );
        }
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
    let lease;
    {
        let mut inner = segment.inner.lock().unwrap_or_else(|e| e.into_inner());
        if inner.cleanup_unknown {
            return failure(
                "native_cleanup_unconfirmed",
                "Segment cleanup is unknown",
                false,
            );
        }
        if let Some(summary) = &inner.summary {
            guard.completed = true;
            return ToolResult::text("Segment closed without focus reclamation.")
                .with_structured(summary.clone());
        }
        lease = inner.policy.activity_lease();
        inner.restoring = true;
    }
    let context = Arc::new(InvocationContext {
        cancelled: AtomicBool::new(false),
        interrupted: AtomicBool::new(false),
        interruption_cause: Mutex::new(None),
        cleanup_unconfirmed: AtomicBool::new(false),
        session_id: Some(segment.binding.owner.session_id.clone()),
        runtime_scope: Some(segment.binding.owner.runtime_scope.clone()),
        foreground_admission: Some(lease),
        background_leases: Mutex::new(Vec::new()),
        transport_owner: Some(Arc::clone(&segment.owner)),
        segment_call: None,
        workers: AtomicUsize::new(0),
        invocation_done: AtomicBool::new(false),
    });
    guard.context = Some(Arc::clone(&context));
    let worker_segment = Arc::clone(&segment);
    let worker_context = Arc::clone(&context);
    let work = INVOCATION
        .scope(Arc::clone(&context), async move {
            spawn_blocking(move || {
                struct FailedRestore(Arc<NativeSegment>, bool);
                impl Drop for FailedRestore {
                    fn drop(&mut self) {
                        if !self.1 {
                            self.0.mark_unknown();
                        }
                    }
                }
                let mut emergency = FailedRestore(Arc::clone(&worker_segment), false);
                let live = finish
                    && worker_segment.owner_live()
                    && lease.permits(clock_ms(), snapshot())
                    && worker_segment
                        .inner
                        .lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .policy
                        .state()
                        == SegmentState::Closing;
                let restoration = if !live {
                    "skipped_interrupted"
                } else if exact_front(worker_segment.original) {
                    "unchanged"
                } else if worker_segment.original == worker_segment.binding.target
                    && worker_segment.accept_dialog_return()
                {
                    // The original WAS the sheet. It closed normally; leave
                    // its host in front instead of restoring a vanished window.
                    "unchanged"
                } else if !exact_front(worker_segment.current_target())
                    && !worker_segment.accept_dialog_return()
                {
                    worker_segment.revoke();
                    "skipped_interrupted"
                } else if crate::input::skylight::restore_exact_window_guarded(
                    worker_segment.original.pid,
                    worker_segment.original.window_id,
                    || {
                        worker_context.check()?;
                        if !worker_segment.owner_live() || !lease.permits(clock_ms(), snapshot()) {
                            anyhow::bail!("foreground segment interrupted during restoration");
                        }
                        Ok(())
                    },
                ) {
                    "restored"
                } else if !worker_segment.owner_live()
                    || !lease.permits(clock_ms(), snapshot())
                    || worker_context.cancelled.load(Ordering::Acquire)
                    || worker_context.interrupted.load(Ordering::Acquire)
                {
                    "skipped_interrupted"
                } else {
                    "failed"
                };
                if worker_context.cleanup_unconfirmed.load(Ordering::Acquire) {
                    worker_segment.mark_unknown();
                }
                let summary = worker_segment.finish_restore(restoration);
                emergency.1 = true;
                (summary, restoration == "failed")
            })
            .await
        })
        .await;
    guard.completed = true;
    match work {
        Ok((Some(summary), failed)) => {
            let result = if failed {
                ToolResult::error("Segment input settled but original-window restoration failed")
            } else {
                ToolResult::text("Native foreground segment closed and owned input settled")
            };
            result.with_structured(summary)
        }
        _ => {
            segment.mark_unknown();
            failure(
                "native_cleanup_unconfirmed",
                "Segment cleanup could not be confirmed",
                false,
            )
        }
    }
}

pub(crate) fn stop_session_segments(session_id: &str) -> Result<(), String> {
    let mut settled = true;
    for segment in all_segments() {
        if segment.binding.owner.session_id == session_id
            || segment.binding.owner.transport_session_id == session_id
        {
            segment.revoke();
            settled &= segment.cleanup_is_settled();
        }
    }
    if settled {
        Ok(())
    } else {
        Err("Foreground segment native cleanup is still pending or unconfirmed".into())
    }
}

pub(crate) fn stop_runtime_segments(runtime_scope: &str) {
    for segment in all_segments() {
        if segment.binding.owner.runtime_scope == runtime_scope {
            segment.revoke();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dialog_return_waits_for_appkit_and_windowserver_to_agree() {
        let reads = Cell::new(0);
        assert!(settle_dialog_condition(
            Duration::from_millis(100),
            || Ok(()),
            || {
                reads.set(reads.get() + 1);
                reads.get() >= 3
            },
        )
        .unwrap());
        assert_eq!(reads.get(), 3);
    }

    #[test]
    fn dialog_return_settlement_stops_before_reading_after_cancellation() {
        let error = settle_dialog_condition(
            Duration::from_millis(100),
            || anyhow::bail!("request cancelled"),
            || panic!("cancelled ownership must not perform another AX query"),
        )
        .unwrap_err();
        assert!(error.to_string().contains("request cancelled"));
    }

    #[test]
    fn dialog_return_proof_does_not_override_activity_during_the_read() {
        let changed = Cell::new(false);
        let error = settle_dialog_condition(
            Duration::from_millis(100),
            || {
                if changed.get() {
                    anyhow::bail!("activity changed");
                }
                Ok(())
            },
            || {
                changed.set(true);
                true
            },
        )
        .unwrap_err();
        assert!(error.to_string().contains("activity changed"));
    }

    #[test]
    fn dialog_return_without_exact_host_proof_expires_without_acceptance() {
        assert!(!settle_dialog_condition(Duration::from_millis(15), || Ok(()), || false).unwrap());
    }

    fn idle() -> Snapshot {
        Snapshot {
            reliable: true,
            state: State::Idle,
            idle_ms: 5_000,
            generation: 7,
        }
    }

    async fn fixture() -> (
        Arc<NativeSegment>,
        Arc<tokio::sync::Mutex<()>>,
        Arc<tokio::sync::Mutex<()>>,
    ) {
        let binding = Binding {
            owner: Owner {
                runtime_scope: "test-runtime".into(),
                session_id: "test-session".into(),
                transport_session_id: "test-owner".into(),
            },
            target: ExactWindowTarget {
                pid: 42,
                window_id: 71,
            },
            id: "fgs_offline_test".into(),
        };
        let background = Arc::new(tokio::sync::Mutex::new(()));
        let foreground = Arc::new(tokio::sync::Mutex::new(()));
        let segment = Arc::new(NativeSegment {
            owner: cua_driver_core::session::TransportOwner::new(
                binding.owner.transport_session_id.clone(),
            ),
            original: ExactWindowTarget {
                pid: 43,
                window_id: 72,
            },
            dialog_host: None,
            dialog_panel: None,
            inner: Mutex::new(Inner {
                policy: Segment::begin(binding.clone(), 5_000, idle(), Limits::default()).unwrap(),
                resources: Some(Resources {
                    background: Arc::new(Arc::clone(&background).lock_owned().await),
                    _foreground: Arc::clone(&foreground).lock_owned().await,
                }),
                ending: false,
                restoring: false,
                activated: false,
                dialog_closed: false,
                dialog_closed_destination: None,
                dialog_target: None,
                dialog_observation_required: false,
                cleanup_unknown: false,
                summary: None,
            }),
            binding,
        });
        (segment, background, foreground)
    }

    fn call(segment: &Arc<NativeSegment>) -> Arc<Call> {
        let reservation = segment
            .inner
            .lock()
            .unwrap()
            .policy
            .reserve(&segment.binding, 5_000, idle(), CallKind::Mutation)
            .unwrap();
        Arc::new(Call {
            segment: Arc::clone(segment),
            target: segment.current_target(),
            dialog_transition: Mutex::new(None),
            reservation: Mutex::new(Some(reservation)),
        })
    }

    fn context(call: Arc<Call>) -> Arc<InvocationContext> {
        Arc::new(InvocationContext {
            cancelled: AtomicBool::new(false),
            interrupted: AtomicBool::new(false),
            interruption_cause: Mutex::new(None),
            cleanup_unconfirmed: AtomicBool::new(false),
            session_id: None,
            runtime_scope: None,
            foreground_admission: None,
            background_leases: Mutex::new(Vec::new()),
            transport_owner: None,
            segment_call: Some(call),
            workers: AtomicUsize::new(0),
            invocation_done: AtomicBool::new(false),
        })
    }

    #[test]
    fn foreground_segment_whitelist_excludes_unbound_and_persistent_actions() {
        for tool in [
            "press_key",
            "type_text",
            "set_value",
            "get_window_state",
            "click",
            "hotkey",
            "prepare_dialog",
        ] {
            assert!(supported_tool(tool), "{tool}");
        }
        for tool in [
            "launch_app",
            "bring_to_front",
            "set_window_frame",
            "move_cursor",
            "invoke_menu",
            "unknown",
        ] {
            assert!(!supported_tool(tool), "{tool}");
        }
    }

    #[tokio::test]
    async fn foreground_dialog_close_is_not_cleanup_or_authority_to_act_on_host() {
        let (mut segment, _, _) = fixture().await;
        assert!(segment
            .validate_dialog_call("prepare_dialog", segment.current_target())
            .is_err());
        Arc::get_mut(&mut segment).unwrap().dialog_host = Some(ExactWindowTarget {
            pid: 42,
            window_id: 99,
        });
        assert!(segment
            .validate_dialog_call("prepare_dialog", segment.current_target())
            .is_ok());
        let ticket = call(&segment);
        segment.inner.lock().unwrap().dialog_closed = true;
        segment.inner.lock().unwrap().dialog_closed_destination = Some(ExactWindowTarget {
            pid: 42,
            window_id: 100,
        });
        assert_eq!(
            segment.current_target().window_id,
            71,
            "replacement never inherits input"
        );
        for tool in [
            "prepare_dialog",
            "get_window_state",
            "click",
            "type_text",
            "set_value",
        ] {
            let refusal = segment
                .validate_dialog_call(tool, segment.current_target())
                .unwrap_err();
            assert_eq!(
                refusal.structured_content.unwrap()["code"],
                "foreground_dialog_closed"
            );
        }
        let proof = ticket.dialog_closed_summary().unwrap();
        assert_eq!(proof["window_id"], 71);
        assert_eq!(ticket.target().window_id, 71);
        assert!(ticket.closed_summary().is_none());
        ticket.settle();
        assert!(segment.inner.lock().unwrap().resources.is_some());
        segment.revoke();
        assert!(segment.cleanup_is_settled());
    }

    #[test]
    fn nested_dialog_transition_requires_ancestry_and_closed_child_on_return() {
        use crate::ax::attached_sheet::DialogAttachment;
        let panel = DialogAttachment {
            window_id: 7,
            panel_id: 7,
            host_id: 1,
            path: vec![7, 1],
        };
        let child = DialogAttachment {
            window_id: 9,
            panel_id: 7,
            host_id: 1,
            path: vec![9, 7, 1],
        };
        assert!(dialog_transition_allowed(&panel, &child, false));
        assert!(!dialog_transition_allowed(&child, &panel, false));
        assert!(dialog_transition_allowed(&child, &panel, true));
        assert!(!dialog_transition_allowed(&child, &child, true));
        let sibling = DialogAttachment {
            window_id: 10,
            path: vec![10, 7, 1],
            ..child.clone()
        };
        assert!(!dialog_transition_allowed(&child, &sibling, true));
        let other_host = DialogAttachment {
            host_id: 2,
            ..child.clone()
        };
        assert!(!dialog_transition_allowed(&panel, &other_host, false));
        let other_panel = DialogAttachment {
            panel_id: 8,
            ..child
        };
        assert!(!dialog_transition_allowed(&panel, &other_panel, false));
    }

    #[tokio::test]
    async fn nested_target_requires_observation_without_rebinding_in_flight_input_or_lease() {
        use crate::ax::attached_sheet::DialogAttachment;
        let (mut segment, _, _) = fixture().await;
        Arc::get_mut(&mut segment).unwrap().dialog_host = Some(ExactWindowTarget {
            pid: 42,
            window_id: 99,
        });
        let ticket = call(&segment);
        let binding = segment.binding.clone();
        let deadline = segment.inner.lock().unwrap().policy.deadline_ms();
        {
            let mut inner = segment.inner.lock().unwrap();
            inner.dialog_target = Some(DialogAttachment {
                window_id: 72,
                panel_id: 71,
                host_id: 99,
                path: vec![72, 71, 99],
            });
            inner.dialog_observation_required = true;
        }
        let child = ExactWindowTarget {
            pid: 42,
            window_id: 72,
        };
        assert_eq!(ticket.target(), binding.target);
        assert_eq!(segment.current_target(), child);
        assert!(segment
            .validate_dialog_call("click", binding.target)
            .is_err());
        assert!(segment.validate_dialog_call("click", child).is_err());
        assert!(segment
            .validate_dialog_call("get_window_state", child)
            .is_ok());
        ticket.mark_dialog_observed(); // old call cannot admit new-target input
        assert!(segment.validate_dialog_call("click", child).is_err());
        assert_eq!(segment.binding, binding);
        assert_eq!(segment.inner.lock().unwrap().policy.deadline_ms(), deadline);
        ticket.settle();
        segment.revoke();
    }

    #[test]
    fn foreground_segment_element_token_cannot_override_exact_window() {
        use cua_driver_core::element_token::{format_token, global};
        let target = ExactWindowTarget {
            pid: 2_147_470_501,
            window_id: 601,
        };
        let own_snapshot = global().register_snapshot(target.pid, target.window_id, 3);
        let sibling_snapshot = global().register_snapshot(target.pid, 602, 3);
        let own = format_token(own_snapshot, 1);
        let sibling = format_token(sibling_snapshot, 1);
        assert!(
            validate_element_target(&json!({"element_token": own}), target, "set_value").is_ok()
        );
        assert!(validate_element_target(
            &json!({"element_token": sibling, "window_id": 601}),
            target,
            "set_value"
        )
        .is_err());
        assert!(
            validate_element_target(&json!({"element_token": "stale"}), target, "set_value")
                .is_err()
        );
        assert!(
            validate_element_target(&json!({"element_token": null}), target, "set_value").is_err()
        );
        assert!(
            validate_element_target(&json!({"element_index": 1}), target, "set_value").is_err()
        );
        // Replacing that window's observation must revoke the previously valid
        // token rather than allowing it to bind to the replacement cache.
        global().register_snapshot(target.pid, target.window_id, 3);
        assert!(
            validate_element_target(&json!({"element_token": own}), target, "set_value").is_err()
        );
    }

    #[tokio::test]
    async fn foreground_segment_exact_target_rewrite_is_refused_before_dispatch() {
        let (segment, _, _) = fixture().await;
        let ticket = call(&segment);
        let context = context(Arc::clone(&ticket));
        INVOCATION
            .scope(context, async {
                assert!(check_segment_target(42, Some(71)).is_ok());
                for (pid, window) in [(42, Some(72)), (43, Some(71)), (42, None)] {
                    let result = check_segment_target(pid, window).unwrap_err();
                    let result = result.structured_content.unwrap();
                    assert_eq!(result["code"], "foreground_segment_target_mismatch");
                    assert_eq!(result["effect"], "refused");
                }
            })
            .await;
        ticket.revoke();
        ticket.settle();
        assert!(
            check_segment_target(99, None).is_ok(),
            "tokenless dispatch is unchanged"
        );
    }

    #[tokio::test]
    async fn foreground_segment_activation_attempt_never_revives_original_expectation() {
        let (segment, _, _) = fixture().await;
        assert_eq!(segment.expected_front(), segment.original);
        let ticket = call(&segment);
        ticket.mark_activated();
        assert_eq!(segment.expected_front(), segment.binding.target);
        ticket.settle();
        assert_eq!(segment.expected_front(), segment.binding.target);
        ticket.revoke();
        assert_eq!(segment.expected_front(), segment.binding.target);
    }

    #[tokio::test]
    async fn foreground_segment_session_cleanup_proof_requires_released_resources() {
        let (segment, _, _) = fixture().await;
        assert!(!segment.cleanup_is_settled());
        let ticket = call(&segment);
        ticket.revoke();
        assert!(
            !segment.cleanup_is_settled(),
            "in-flight worker has not settled"
        );
        ticket.settle();
        assert!(segment.cleanup_is_settled());
        segment.inner.lock().unwrap().cleanup_unknown = true;
        assert!(
            !segment.cleanup_is_settled(),
            "unknown cleanup cannot be reported complete"
        );
    }

    #[tokio::test]
    async fn foreground_segment_binding_requires_actual_transport_capability() {
        let (segment, _, _) = fixture().await;
        assert!(binding_matches(
            &segment,
            &segment.binding.owner,
            segment.binding.target,
            &segment.owner
        ));
        let same_name_new_capability =
            cua_driver_core::session::TransportOwner::new("test-owner".into());
        assert!(!binding_matches(
            &segment,
            &segment.binding.owner,
            segment.binding.target,
            &same_name_new_capability
        ));
        let mut foreign = segment.binding.owner.clone();
        foreign.session_id = "other-session".into();
        assert!(!binding_matches(
            &segment,
            &foreign,
            segment.binding.target,
            &segment.owner
        ));
        foreign = segment.binding.owner.clone();
        foreign.runtime_scope = "other-runtime".into();
        assert!(!binding_matches(
            &segment,
            &foreign,
            segment.binding.target,
            &segment.owner
        ));
        assert!(!binding_matches(
            &segment,
            &segment.binding.owner,
            ExactWindowTarget {
                pid: 42,
                window_id: 999
            },
            &segment.owner
        ));
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn foreground_segment_concurrent_end_claims_only_one_restore_owner_before_waiting() {
        let (segment, background, foreground) = fixture().await;
        let ticket = call(&segment);
        let barrier = Arc::new(std::sync::Barrier::new(3));
        let mut waiters = Vec::new();
        for _ in 0..2 {
            let segment = Arc::clone(&segment);
            let barrier = Arc::clone(&barrier);
            waiters.push(std::thread::spawn(move || {
                barrier.wait();
                let mut inner = segment.inner.lock().unwrap();
                claim_end(&mut inner, &segment.binding, true).is_ok()
            }));
        }
        barrier.wait();
        let winners = waiters
            .into_iter()
            .map(|thread| usize::from(thread.join().unwrap()))
            .sum::<usize>();
        assert_eq!(winners, 1, "only one end may proceed to its worker wait");
        assert!(segment.inner.lock().unwrap().ending);
        assert!(segment.inner.lock().unwrap().policy.in_flight());
        assert!(background.try_lock().is_err());
        assert!(foreground.try_lock().is_err());
        ticket.settle();
        {
            let mut inner = segment.inner.lock().unwrap();
            assert!(
                claim_end(&mut inner, &segment.binding, true).is_err(),
                "settlement does not transfer end ownership"
            );
            inner.restoring = true;
        }
        segment.finish_restore("unchanged").unwrap();
        assert!(segment.cleanup_is_settled());
    }

    #[tokio::test]
    async fn foreground_segment_normal_call_settles_without_releasing_segment_ownership() {
        let (segment, background, foreground) = fixture().await;
        let ticket = call(&segment);
        let context = context(Arc::clone(&ticket));
        context.finish_invocation();
        assert!(!segment.inner.lock().unwrap().policy.in_flight());
        assert_eq!(
            segment.inner.lock().unwrap().policy.state(),
            SegmentState::Open
        );
        assert!(background.try_lock().is_err());
        assert!(foreground.try_lock().is_err());
        assert!(ticket.closed_summary().is_none());
        ticket.revoke();
        assert!(background.try_lock().is_ok());
        assert!(foreground.try_lock().is_ok());
        assert_eq!(
            ticket.closed_summary().unwrap()["restoration"],
            "skipped_interrupted"
        );
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn foreground_segment_abort_waits_for_detached_native_worker_before_closed_proof() {
        let (segment, background, foreground) = fixture().await;
        let ticket = call(&segment);
        let context = context(Arc::clone(&ticket));
        let child_context = Arc::clone(&context);
        let (started_tx, started_rx) = tokio::sync::oneshot::channel();
        let (continue_tx, continue_rx) = std::sync::mpsc::channel();
        let task = tokio::spawn(async move {
            let _cancel = CancelInvocation {
                context: Arc::clone(&child_context),
                completed: false,
            };
            INVOCATION
                .scope(child_context, async {
                    spawn_blocking(move || {
                        started_tx.send(()).unwrap();
                        continue_rx.recv().unwrap();
                        // This worker never touches an AX object or posts input.
                    })
                    .await
                    .unwrap();
                })
                .await;
        });
        started_rx.await.unwrap();
        task.abort();
        assert!(task.await.unwrap_err().is_cancelled());
        assert_eq!(context.workers.load(Ordering::Acquire), 1);
        assert!(segment.inner.lock().unwrap().policy.in_flight());
        assert_eq!(
            segment.inner.lock().unwrap().policy.state(),
            SegmentState::Revoked
        );
        assert!(ticket.closed_summary().is_none());
        assert!(background.try_lock().is_err());
        assert!(foreground.try_lock().is_err());
        continue_tx.send(()).unwrap();
        let released =
            tokio::time::timeout(Duration::from_secs(1), Arc::clone(&foreground).lock_owned())
                .await
                .unwrap();
        drop(released);
        assert!(!segment.inner.lock().unwrap().policy.in_flight());
        assert!(background.try_lock().is_ok());
        assert_eq!(
            ticket.closed_summary().unwrap(),
            json!({
                "foreground_segment_id": "fgs_offline_test", "phase": "closed", "pid": 42,
                "window_id": 71, "cleanup_confirmed": true, "restoration": "skipped_interrupted",
            })
        );
    }

    #[tokio::test]
    async fn foreground_segment_call_can_borrow_only_its_owned_pid_lock() {
        let (segment, background, _) = fixture().await;
        let ticket = call(&segment);
        assert!(ticket.background_lease(99).is_none());
        let borrowed = ticket.background_lease(42).unwrap();
        ticket.revoke();
        ticket.settle();
        assert!(
            background.try_lock().is_err(),
            "borrowed native work still owns coordinator"
        );
        drop(borrowed);
        assert!(background.try_lock().is_ok());
    }

    #[tokio::test]
    async fn foreground_segment_closed_proof_is_not_published_during_restore_worker() {
        let (segment, background, foreground) = fixture().await;
        segment.inner.lock().unwrap().restoring = true;
        segment.revoke();
        assert!(segment.inner.lock().unwrap().summary.is_none());
        assert!(background.try_lock().is_err());
        assert!(foreground.try_lock().is_err());
        let summary = segment.finish_restore("skipped_interrupted").unwrap();
        assert_eq!(summary["cleanup_confirmed"], true);
        assert!(foreground.try_lock().is_ok());
    }
}
