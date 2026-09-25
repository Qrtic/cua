//! set_value tool — matches the Swift reference in SetValueTool.swift.
//!
//! Value handling is determined by the element's native role and value type:
//!
//! * **AXPopUpButton**: Find the child option whose AXTitle or AXValue matches
//!   `value` (case-insensitive) and AXPress it directly.  The native macOS popup
//!   menu is never opened, so focus is never stolen.  Falls back to Safari
//!   `osascript do JavaScript` for WebKit `<select>` elements that expose no AX
//!   children when the popup is closed.
//!
//! * **AXDateTimeArea**: Write a typed CFDate parsed from an explicit RFC 3339
//!   timestamp. A locale-dependent date or a time without a zone is rejected.
//!
//! * **Native text fields**: Enter the exact field's editor before writing
//!   `AXValue`, so AppKit commits the value when the form is saved.
//!
//! * **Everything else**: Write `AXValue` directly (sliders, steppers).

use async_trait::async_trait;
use cua_driver_core::{
    protocol::ToolResult,
    tool::{Tool, ToolDef},
};
use serde_json::Value;
use std::sync::Arc;

use crate::apps;
use crate::ax::bindings::{
    copy_children, copy_number_attr, copy_string_attr, kAXErrorSuccess, perform_action,
    set_number_attr, set_string_attr, AXUIElementRef,
};
use crate::focus_guard;
use crate::window_change_detector::WindowChangeDetector;
use core_foundation::base::CFRelease;

use super::ToolState;

pub struct SetValueTool {
    state: Arc<ToolState>,
}

impl SetValueTool {
    pub fn new(state: Arc<ToolState>) -> Self {
        Self { state }
    }
}

static DEF: std::sync::OnceLock<ToolDef> = std::sync::OnceLock::new();

fn def() -> &'static ToolDef {
    DEF.get_or_init(|| ToolDef {
        name: "set_value".into(),
        description:
            "Set a value on a UI element, according to its native role:\n\
             \n\
             - **AXPopUpButton / select dropdown**: finds the child option whose \
             title or value matches `value` (case-insensitive) and AXPresses it \
             directly — the native macOS popup menu is never opened, so focus \
             is never stolen. Use this for HTML <select> elements in Safari or \
             any native NSPopUpButton.\n\
             \n\
             - **AXDateTimeArea**: writes a native CFDate from an RFC 3339 timestamp \
             with an explicit timezone offset. Preserve components the user did not \
             ask to change; do not send a plain time or locale-dependent date.\n\
             \n\
             - **Native text fields**: prepares and verifies the exact field's \
             editing focus before writing a string AXValue.\n\
             \n\
             - **All other elements**: writes AXValue directly (sliders, steppers).\n\
             \n\
             For free-form text entry into web inputs, prefer `type_text_chars` \
             which synthesises key events — AXValue writes are ignored by WebKit."
            .into(),
        input_schema: serde_json::json!({
            "type": "object",
            "required": ["pid", "value"],
            "properties": {
                "session": { "type": "string", "description": "For multi-call work, prefer a short public session label and repeat it on every call that accepts it. Omit it to use the authenticated transport's implicit lifecycle session." },
                "pid": { "type": "integer" },
                "window_id": {
                    "type": "integer",
                    "description": "CGWindowID for the window whose get_window_state produced the element_index. Required when element_index is used; optional when element_token is supplied (the token carries it)."
                },
                "element_index": cua_driver_core::tool_schema::element_index_schema(),
                "element_token": cua_driver_core::tool_schema::element_token_schema(),
                "snapshot_id": cua_driver_core::tool_schema::snapshot_id_schema(),
                "value": {
                    "type": "string",
                    "description": "New value. Native date/time editors require an RFC 3339 timestamp with an explicit timezone; other supported controls receive their native value type."
                }
            },
            "additionalProperties": false
        }),
        read_only:   false,
        destructive: true,
        idempotent:  true,
        open_world:  true,
    })
}

#[async_trait]
impl Tool for SetValueTool {
    fn def(&self) -> &ToolDef {
        def()
    }

    async fn invoke(&self, args: Value) -> ToolResult {
        use cua_driver_core::tool_args::ArgsExt;
        let pid = match args.require_i32("pid") {
            Ok(v) => v,
            Err(e) => return e,
        };
        let app_context_route = crate::ax::app_context::delegation_route_from_args(&args);
        let value = match args.require_str("value") {
            Ok(v) => v,
            Err(e) => return e,
        };

        // Surface 6: element_token / element_index precedence. Neither
        // is now schema-required so the resolver can centralize the
        // "missing addressing" error message.
        let element_token_arg = args.opt_str("element_token");
        let window_id_arg = args.opt_u64("window_id");
        let element_index_arg = args.opt_u64("element_index").map(|v| v as usize);
        let resolved = match cua_driver_core::element_token::resolve_element_args(
            pid,
            element_index_arg,
            element_token_arg.as_deref(),
            args.opt_str("snapshot_id").as_deref(),
            window_id_arg,
            "set_value",
        ) {
            Ok(r) => r,
            Err(e) => return e,
        };
        let (element_index, window_id, snapshot_id) = match resolved {
            cua_driver_core::element_token::ResolvedElement::None => {
                return ToolResult::error(
                    "set_value requires element_index (+ window_id) or element_token to \
                     address the target element.",
                )
            }
            cua_driver_core::element_token::ResolvedElement::Element {
                window_id: Some(wid),
                element_index: idx,
                snapshot_id,
                via_token: _,
            } => (idx, wid, snapshot_id),
            cua_driver_core::element_token::ResolvedElement::Element {
                window_id: None, ..
            } => {
                return ToolResult::error(
                    "set_value requires window_id when element_index is used \
                 (omit only when supplying element_token, which carries it).",
                )
            }
        };

        if let Err(refusal) = super::guard_same_pid_transient_target(pid, Some(window_id)).await {
            return refusal;
        }

        // Retain out of the cache so a concurrent get_window_state can't free
        // the element mid-action (use-after-free → daemon crash). Guard lives
        // to the end of this method, past the AX write below.
        let element_guard = match self.state.element_cache.get_element_retained_for_snapshot(
            pid,
            window_id,
            snapshot_id,
            element_index,
        ) {
            Some(e) => e,
            None => {
                return cua_driver_core::element_token::stale_element_cache_result(
                    "set_value",
                    pid,
                    window_id,
                    snapshot_id,
                )
            }
        };
        let element_ptr = element_guard.as_ptr();
        if unsafe {
            super::ensure_app_context_element_window(
                app_context_route.as_ref(),
                element_ptr as AXUIElementRef,
            )
        }
        .is_err()
        {
            return super::app_context_delegation_stale_refusal();
        }

        // set_value is an always-background semantic AX mutation. Re-prove
        // that the retained element still belongs to the requested exact
        // window immediately before any cursor or AX work; a cache hit alone
        // is not delivery proof after a window lifecycle or Space change.
        let route_element = element_guard.clone();
        let (native_date, native_text, attached_popover_value) =
            match crate::foreground_activity::spawn_blocking(move || unsafe {
                let element = route_element.as_ptr() as AXUIElementRef;
                let role = copy_string_attr(element, "AXRole");
                let native_date = crate::ax::attached_popover::native_date_role(role.as_deref());
                let attached = crate::ax::attached_popover::native_value_role(role.as_deref())
                    && crate::ax::attached_popover::has_displaced_popover_window(
                        element, window_id,
                    );
                let native_text = crate::ax::attached_popover::native_text_role(role.as_deref())
                    && (attached || crate::ax::exact_target::native_text_field_in_window(
                        element, pid, window_id,
                    ));
                (native_date, native_text, attached)
            })
            .await
            {
                Ok(attached) => attached,
                Err(error) => {
                    return ToolResult::error(format!(
                        "Native value surface lookup failed: {error}; no input was sent."
                    ))
                }
            };
        let gate_action = if attached_popover_value {
            cua_driver_core::background_input::BackgroundAction::AttachedPopoverSemantic
        } else {
            cua_driver_core::background_input::BackgroundAction::AxSemantic
        };
        let _mutation_lease = match super::gate_background_window_action(
            pid,
            window_id,
            Some(element_ptr),
            gate_action,
        )
        .await
        {
            Ok(lease) => lease,
            Err(refusal_result) => return refusal_result,
        };

        let cursor_key = super::cursor_tools::resolve_cursor_key(&args);
        let center_element = element_guard.clone();
        if let Ok(Some((screen_x, screen_y))) = crate::foreground_activity::spawn_blocking(move || unsafe {
            crate::ax::bindings::element_screen_center(center_element.as_ptr() as AXUIElementRef)
        })
        .await
        {
            crate::cursor::overlay::send_command(
                cursor_key.clone(),
                cursor_overlay::OverlayCommand::PinAbove(window_id as u64),
            );
            crate::cursor::overlay::animate_input_feedback(cursor_key.clone(), screen_x, screen_y)
                .await;
            self.state
                .cursor_registry
                .update_position(&cursor_key, screen_x, screen_y);
        }
        // An AXValue read-back is not ground truth for web content. Chromium,
        // WebKit, and Electron can echo the write through accessibility while
        // the renderer never observes it. Reuse type_text's bounded ancestor
        // check so native browser chrome stays trusted but rendered content is
        // always reported as unverified.
        let ax_echo_surface = super::type_text::target_in_web_area(
            pid,
            Some((element_ptr, Some(element_index))),
            Some(window_id),
        );

        // ── Focus-suppression wrap (Swift WindowChangeDetector + FocusGuard) ──
        // AXValue writes on popups / sliders can cause reflex activations
        // in Chromium-based apps; the AXPopUpButton path also AXPresses a
        // child option which can trigger app activation in some setups. Only
        // suppress the target itself so a concurrent user app switch survives.
        let prior_front = apps::frontmost_pid();
        let snapshot = WindowChangeDetector::snapshot_targeted(prior_front, pid);

        let result = focus_guard::with_focus_suppressed(
            // The WindowChangeDetector snapshot owns the one canonical
            // target-only lease for this action. A second lease could retain a
            // stale restore anchor after concurrent user focus changes.
            None,
            prior_front,
            "set_value.AXValue",
            || async move {
                crate::foreground_activity::spawn_blocking(move || {
                    let element_ptr = element_guard.as_ptr();
                    crate::foreground_activity::check_request()?;
                    super::ensure_app_context_delegation_live(app_context_route.as_ref())?;
                    unsafe {
                        super::ensure_app_context_element_window(
                            app_context_route.as_ref(),
                            element_ptr as AXUIElementRef,
                        )?;
                    }
                    if native_date {
                        set_native_date_value(
                            element_ptr,
                            element_index,
                            pid,
                            window_id,
                            attached_popover_value,
                            &value,
                        )
                    } else if native_text {
                        set_native_text_value(
                            element_ptr,
                            element_index,
                            pid,
                            window_id,
                            attached_popover_value,
                            &value,
                        )
                    } else {
                        set_value_blocking(element_ptr, element_index, pid, &value)
                    }
                })
                .await
            },
        )
        .await;

        let changes = snapshot.detect_async().await;

        match result {
            Ok(Ok(mut outcome)) => {
                apply_surface_trust(&mut outcome, ax_echo_surface);
                apply_verification_label(&mut outcome);
                let mut msg = outcome.detail;
                msg.push_str(&changes.result_suffix());
                let verified = outcome.verified.unwrap_or(false);
                let mut structured = serde_json::json!({
                    "path": "ax",
                    "verified": verified,
                    "effect": if verified { "confirmed" } else { "unverifiable" },
                });
                if let Some(response) = outcome.native_response {
                    structured["native_ax_response"] = response.json();
                }
                if ax_echo_surface {
                    structured["escalation"] = serde_json::json!({
                        "recommended": "px",
                        "reason": "AXValue read-back is not trusted for web content. Verify \
                                   through the renderer; use browser page tools for a tab or \
                                   manipulate the control through its pixel action."
                    });
                }
                ToolResult::text(msg).with_structured(structured)
            }
            Ok(Err(e)) => match e.downcast_ref::<NativeValueResponse>() {
                Some(response) => response.result(),
                None => ToolResult::error(format!("set_value failed: {e}")),
            },
            Err(e) => ToolResult::error(format!("Task error: {e}")),
        }
    }
}

// ── Blocking implementation (runs on spawn_blocking thread) ─────────────────

/// Outcome of a `set_value` write.
///
/// `verified` is `None` for paths that do not perform a value read-back (the
/// AXPopUpButton path drives menu items rather than writing AXValue), and
/// `Some(false)` when a read-back ran but could not confirm the write. A
/// successful `AXUIElementSetAttributeValue` return code is not by itself
/// evidence that the value landed: web content behind an AXWebArea accepts the
/// write and echoes it back through AXValue while the renderer never observes
/// it — the same trap `type_text` already documents.
struct SetValueOutcome {
    detail: String,
    verified: Option<bool>,
    /// `Some(false)` when the element already held the requested value, so the
    /// write was a no-op. Lets callers distinguish "idempotent" from "applied".
    changed: Option<bool>,
    native_response: Option<NativeValueResponse>,
}

/// A native response is separate from the value read back on the same control.
/// No text, identifiers or paths are included in this bounded diagnostic.
#[derive(Debug)]
struct NativeValueResponse {
    phase: &'static str,
    native_error: Option<i32>,
    value_write_attempted: bool,
    value_readback_matches: Option<bool>,
}

impl std::fmt::Display for NativeValueResponse {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "Native value {} response is unconfirmed ({:?}); do not replay",
            self.phase, self.native_error
        )
    }
}
impl std::error::Error for NativeValueResponse {}

impl NativeValueResponse {
    fn json(&self) -> Value {
        serde_json::json!({
            "phase": self.phase,
            "native_error": self.native_error,
            "value_write_attempted": self.value_write_attempted,
            "value_readback_matches": self.value_readback_matches,
        })
    }

    fn result(&self) -> ToolResult {
        ToolResult::error(self.to_string()).with_structured(serde_json::json!({
            "code": "ax_action_response_unconfirmed", "effect": "unverifiable",
            "verified": false, "retryable": false, "native_ax_response": self.json(),
        }))
    }
}

trait NativeValueField {
    fn validate(&self) -> anyhow::Result<()>;
    fn focused(&self) -> Option<bool>;
    fn focus_settable(&self) -> bool;
    fn focus(&self) -> i32;
    fn value(&self) -> Option<String>;
    fn set_value(&self, value: &str) -> i32;
}

struct LiveNativeTextField {
    element_ptr: usize,
    pid: i32,
    window_id: u32,
    attached: bool,
}

impl NativeValueField for LiveNativeTextField {
    fn validate(&self) -> anyhow::Result<()> {
        use cua_driver_core::background_input::{
            decide_background_input, BackgroundAction, BackgroundInputDecision, ExactWindowTarget,
        };
        let element = self.element_ptr as AXUIElementRef;
        let facts = crate::ax::exact_target::gather_background_facts(
            self.pid,
            self.window_id,
            Some(self.element_ptr),
        );
        let action = if self.attached {
            BackgroundAction::AttachedPopoverSemantic
        } else {
            BackgroundAction::AxSemantic
        };
        if let BackgroundInputDecision::Refuse(refusal) = decide_background_input(
            ExactWindowTarget {
                pid: self.pid,
                window_id: self.window_id,
            },
            &facts,
            action,
        ) {
            anyhow::bail!(
                "Native text write refused before dispatch: {}",
                refusal.reason
            );
        }
        let role = unsafe { copy_string_attr(element, "AXRole") };
        if !crate::ax::attached_popover::native_text_role(role.as_deref())
            || (!self.attached && !unsafe {
                crate::ax::exact_target::native_text_field_in_window(element, self.pid, self.window_id)
            })
            || unsafe { crate::ax::bindings::copy_bool_attr(element, "AXEnabled") } == Some(false)
            || !unsafe { crate::ax::bindings::is_attribute_settable(element, "AXValue") }
        {
            anyhow::bail!("Native target is not a proven, enabled, settable text field; no value write was sent");
        }
        crate::foreground_activity::check_request()
    }

    fn focused(&self) -> Option<bool> {
        unsafe {
            crate::ax::bindings::copy_bool_attr(self.element_ptr as AXUIElementRef, "AXFocused")
        }
    }

    fn focus_settable(&self) -> bool {
        unsafe {
            crate::ax::bindings::is_attribute_settable(
                self.element_ptr as AXUIElementRef,
                "AXFocused",
            )
        }
    }

    fn focus(&self) -> i32 {
        unsafe {
            crate::ax::bindings::set_bool_attr_true(self.element_ptr as AXUIElementRef, "AXFocused")
        }
    }

    fn value(&self) -> Option<String> {
        unsafe { copy_string_attr(self.element_ptr as AXUIElementRef, "AXValue") }
    }

    fn set_value(&self, value: &str) -> i32 {
        unsafe { set_string_attr(self.element_ptr as AXUIElementRef, "AXValue", value) }
    }
}

struct LiveNativeDateField {
    base: LiveNativeTextField,
    requested_absolute_time: f64,
}

impl NativeValueField for LiveNativeDateField {
    fn validate(&self) -> anyhow::Result<()> {
        use cua_driver_core::background_input::{
            decide_background_input, BackgroundAction, BackgroundInputDecision, ExactWindowTarget,
        };
        let element = self.base.element_ptr as AXUIElementRef;
        let facts = crate::ax::exact_target::gather_background_facts(
            self.base.pid,
            self.base.window_id,
            Some(self.base.element_ptr),
        );
        let action = if self.base.attached {
            BackgroundAction::AttachedPopoverSemantic
        } else {
            BackgroundAction::AxSemantic
        };
        if let BackgroundInputDecision::Refuse(refusal) = decide_background_input(
            ExactWindowTarget {
                pid: self.base.pid,
                window_id: self.base.window_id,
            },
            &facts,
            action,
        ) {
            anyhow::bail!(
                "Native date write refused before dispatch: {}",
                refusal.reason
            );
        }
        let role = unsafe { copy_string_attr(element, "AXRole") };
        if !crate::ax::attached_popover::native_date_role(role.as_deref())
            || unsafe { crate::ax::bindings::copy_bool_attr(element, "AXEnabled") } == Some(false)
            || !unsafe { crate::ax::bindings::is_attribute_settable(element, "AXValue") }
            || unsafe { crate::ax::date_value::copy(element) }.is_none()
        {
            anyhow::bail!("Native date target is not an enabled, settable CFDate control; no value write was sent");
        }
        crate::foreground_activity::check_request()
    }

    fn focused(&self) -> Option<bool> {
        self.base.focused()
    }
    fn focus_settable(&self) -> bool {
        self.base.focus_settable()
    }
    fn focus(&self) -> i32 {
        self.base.focus()
    }
    fn value(&self) -> Option<String> {
        unsafe { crate::ax::date_value::copy(self.base.element_ptr as AXUIElementRef) }
            .and_then(crate::ax::date_value::format)
    }
    fn set_value(&self, _value: &str) -> i32 {
        // Parsed before focus or mutation; never coerce an arbitrary string.
        unsafe {
            crate::ax::date_value::set(
                self.base.element_ptr as AXUIElementRef,
                self.requested_absolute_time,
            )
        }
    }
}

fn set_native_date_value(
    element_ptr: usize,
    element_index: usize,
    pid: i32,
    window_id: u32,
    attached: bool,
    value: &str,
) -> anyhow::Result<SetValueOutcome> {
    let requested_absolute_time =
        crate::ax::date_value::parse(value).map_err(anyhow::Error::msg)?;
    let normalized = crate::ax::date_value::format(requested_absolute_time).ok_or_else(|| {
        anyhow::anyhow!("Native date is outside the supported timestamp range; no input was sent")
    })?;
    write_native_value(
        &LiveNativeDateField {
            base: LiveNativeTextField {
                element_ptr,
                pid,
                window_id,
                attached,
            },
            requested_absolute_time,
        },
        element_index,
        &normalized,
    )
}

fn apply_surface_trust(outcome: &mut SetValueOutcome, ax_echo_surface: bool) {
    if ax_echo_surface && outcome.verified == Some(true) {
        outcome.verified = Some(false);
        outcome.changed = None;
        outcome.detail.push_str(
            " AXValue read-back is not trusted for web content; verify the \
             renderer via screenshot or use the browser page tools.",
        );
    }
}

fn apply_verification_label(outcome: &mut SetValueOutcome) {
    if outcome.verified != Some(true) {
        if let Some(rest) = outcome.detail.strip_prefix("✅ Set") {
            outcome.detail = format!("📨 Sent (unverified){rest}");
        }
    }
}

/// Prepare only a proven native field. A projected field stays bound to its
/// physical popover. Text never enters numeric, stepping or keyboard fallbacks.
fn set_native_text_value(
    element_ptr: usize,
    element_index: usize,
    pid: i32,
    window_id: u32,
    attached: bool,
    value: &str,
) -> anyhow::Result<SetValueOutcome> {
    write_native_value(
        &LiveNativeTextField {
            element_ptr,
            pid,
            window_id,
            attached,
        },
        element_index,
        value,
    )
}

fn write_native_value(
    field: &impl NativeValueField,
    element_index: usize,
    value: &str,
) -> anyhow::Result<SetValueOutcome> {
    field.validate()?;
    // A background Cocoa field can accept AXValue without opening its field
    // editor, changing only its display. Enter the exact control's editor and
    // verify that preparation before writing; never activate the application
    // or substitute pointer/keyboard input here.
    if field.focused() != Some(true) {
        if !field.focus_settable() {
            anyhow::bail!("Native value editor is not focusable; no value write was sent");
        }
        let error = field.focus();
        if error != kAXErrorSuccess || !wait_for_native_editor(field)? {
            return Err(NativeValueResponse {
                phase: "editor_focus",
                native_error: (error != kAXErrorSuccess).then_some(error),
                value_write_attempted: false,
                value_readback_matches: None,
            }
            .into());
        }
    }
    // Focus can rebuild or dismiss the popup. A retained pointer and a prior
    // proof cannot authorize a write after that transition.
    field.validate()?;
    let before = field.value();
    let error = field.set_value(value);
    // AppKit can apply the edit and still return CannotComplete. Read back
    // once on a freshly re-proven attachment instead of declaring failure or
    // replaying. A detached or unreadable field proves no postcondition.
    let after = field.validate().ok().and_then(|_| field.value());
    let (verified, changed) = classify_write(before.as_deref(), after.as_deref(), value, false);
    let native_response = if error != kAXErrorSuccess {
        let response = NativeValueResponse {
            phase: "value_write",
            native_error: Some(error),
            value_write_attempted: true,
            value_readback_matches: verified,
        };
        tracing::warn!(target: "cua_native_text", native_error = error,
            value_readback_matches = ?verified,
            "AXValue response did not complete; retained independent field readback without replay");
        if verified != Some(true) {
            return Err(response.into());
        }
        Some(response)
    } else {
        None
    };
    Ok(SetValueOutcome {
        detail: format!("Set AXValue on native control [{element_index}]."),
        verified,
        changed,
        native_response,
    })
}

/// AXFocused can return before AppKit installs the next field editor. Wait
/// briefly for that one requested transition; never send the focus write a
/// second time. Each read re-proves the target and observes cancellation.
fn wait_for_native_editor(field: &impl NativeValueField) -> anyhow::Result<bool> {
    use std::time::{Duration, Instant};
    let deadline = Instant::now() + Duration::from_millis(250);
    loop {
        field.validate()?;
        if field.focused() == Some(true) {
            return Ok(true);
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Ok(false);
        }
        std::thread::sleep(remaining.min(Duration::from_millis(20)));
    }
}

fn set_value_blocking(
    element_ptr: usize,
    element_index: usize,
    pid: i32,
    value: &str,
) -> anyhow::Result<SetValueOutcome> {
    let element = element_ptr as AXUIElementRef;

    let role = unsafe { copy_string_attr(element, "AXRole") }.unwrap_or_default();

    if role == "AXPopUpButton" {
        let element_title = unsafe { copy_string_attr(element, "AXTitle") }.unwrap_or_default();
        // Menu-item selection, not an AXValue write — no read-back to report.
        select_popup_option(element, element_index, pid, value, &element_title).map(|detail| {
            SetValueOutcome {
                detail,
                verified: None,
                changed: None,
                native_response: None,
            }
        })
    } else {
        // Default path: write AXValue directly. Numeric controls (AXSlider /
        // AXStepper) reject a CFString with -25201 and need a CFNumber; text
        // fields take a CFString. Try numeric first when the value parses as a
        // number, then fall back to a string write.
        // Numeric target carried through so we can step toward it if the
        // direct writes are rejected (SwiftUI AXSlider rejects every AXValue
        // write with -25200 yet exposes a readable AXValue + increment/decrement
        // actions).
        let numeric_target = value.trim().parse::<f64>().ok();
        // Read the value before writing so an unchanged field can be reported as
        // idempotent rather than silently indistinguishable from a fresh write.
        let before = unsafe { copy_string_attr(element, "AXValue") };
        crate::foreground_activity::check_request()?;
        let err = match numeric_target {
            Some(n) => {
                let e = unsafe { set_number_attr(element, "AXValue", n) };
                if e == kAXErrorSuccess {
                    e
                } else {
                    crate::foreground_activity::check_request()?;
                    unsafe { set_string_attr(element, "AXValue", value) }
                }
            }
            None => unsafe { set_string_attr(element, "AXValue", value) },
        };
        if err == kAXErrorSuccess {
            let after = unsafe { copy_string_attr(element, "AXValue") };
            let (verified, changed) = classify_write(
                before.as_deref(),
                after.as_deref(),
                value,
                numeric_target.is_some(),
            );
            let suffix = match (verified, changed) {
                (Some(true), Some(false)) => " Value already matched; write was idempotent.",
                (Some(true), _) => "",
                (Some(false), _) => " Read-back did not confirm the value; verify via screenshot.",
                (None, _) => " Value is not readable through AX; could not confirm.",
            };
            Ok(SetValueOutcome {
                detail: format!("✅ Set AXValue on [{element_index}] {role}.{suffix}"),
                verified,
                changed,
                native_response: None,
            })
        } else if let Some(target) = numeric_target {
            // Both direct writes failed for a numeric target — fall back to
            // stepping the control via AXIncrement / AXDecrement actions.
            if step_to_value(element, target) {
                let after = unsafe { copy_string_attr(element, "AXValue") };
                let (verified, changed) =
                    classify_write(before.as_deref(), after.as_deref(), value, true);
                Ok(SetValueOutcome {
                    detail: format!(
                        "✅ Set AXValue on [{element_index}] {role} via AXIncrement/AXDecrement stepping."
                    ),
                    verified,
                    changed,
                    native_response: None,
                })
            } else {
                anyhow::bail!("AXUIElementSetAttributeValue(AXValue) failed with error {err}")
            }
        } else {
            anyhow::bail!("AXUIElementSetAttributeValue(AXValue) failed with error {err}")
        }
    }
}

/// Decide what a post-write AXValue read proves.
///
/// Returns `(verified, changed)`:
/// - `verified = None` when AXValue is not readable at all, so the write can be
///   neither confirmed nor denied.
/// - `verified = Some(true)` when the read-back equals the requested value.
///   Numeric controls are compared numerically so `"25"` matches a slider that
///   reports `"25.0"`.
/// - `changed = Some(false)` when the read-back equals what was there before,
///   i.e. the element's value did not move. Combined with `verified` this
///   separates "already had the requested value" (verified + unchanged) from
///   "the write did not take" (unverified + unchanged).
fn classify_write(
    before: Option<&str>,
    after: Option<&str>,
    requested: &str,
    numeric: bool,
) -> (Option<bool>, Option<bool>) {
    let Some(after) = after else {
        return (None, None);
    };
    let matches = |observed: &str, expected: &str| -> bool {
        if observed == expected {
            return true;
        }
        if !numeric {
            return false;
        }
        match (
            observed.trim().parse::<f64>(),
            expected.trim().parse::<f64>(),
        ) {
            (Ok(a), Ok(b)) => {
                let scale = a.abs().max(b.abs()).max(1.0);
                (a - b).abs() <= 1e-9 * scale
            }
            _ => false,
        }
    };
    let verified = matches(after, requested);
    let changed = before.map(|before| !matches(after, before));
    (Some(verified), changed)
}

// ── AXIncrement / AXDecrement stepping fallback ──────────────────────────────

/// Step a numeric control toward `target` using its `AXIncrement` /
/// `AXDecrement` actions. Used only when direct `AXValue` writes are rejected
/// (notably SwiftUI's `AXSlider`, which exposes a readable-but-unsettable
/// `AXValue` plus increment/decrement actions).
///
/// Returns `true` once the control's value lands within half of the last
/// observed step of `target`, `false` if it can't be read or can't be moved.
fn step_to_value(element: AXUIElementRef, target: f64) -> bool {
    // Can't target precisely without feedback — bail if AXValue is unreadable.
    let mut current = match unsafe { copy_number_attr(element, "AXValue") } {
        Some(v) => v,
        None => return false,
    };

    // Half of the last observed step. Start near-zero so we never declare the
    // target "reached" before performing (and observing) a real
    // AXIncrement/AXDecrement — otherwise a slider at 0.0 targeting 0.5 would
    // report success without ever moving. The radius widens only after we learn
    // the control's actual step size from an observed value change.
    let mut step_radius = f64::EPSILON;

    // Hard cap to prevent runaway on a control that never quite converges.
    for _ in 0..500 {
        if crate::foreground_activity::check_request().is_err() {
            return false;
        }
        if (current - target).abs() <= step_radius {
            return true;
        }

        let action = if current < target {
            "AXIncrement"
        } else {
            "AXDecrement"
        };
        let _ = unsafe { perform_action(element, action) };

        let next = match unsafe { copy_number_attr(element, "AXValue") } {
            Some(v) => v,
            None => return false,
        };

        // The action didn't move the value — the control can't be stepped (or
        // has hit a min/max bound short of target). Stop to avoid looping.
        if next == current {
            return false;
        }

        // Refine the stop threshold to half of the actual step the control took.
        let step = (next - current).abs();
        if step > 0.0 {
            step_radius = step / 2.0;
        }
        current = next;
    }

    // Exhausted the iteration cap without converging.
    (current - target).abs() <= step_radius
}

// ── AXPopUpButton path ───────────────────────────────────────────────────────

fn select_popup_option(
    element: AXUIElementRef,
    element_index: usize,
    pid: i32,
    value: &str,
    element_title: &str,
) -> anyhow::Result<String> {
    let children = unsafe { copy_children(element) };

    if !children.is_empty() {
        // Strategy 1: AX children (native AppKit NSPopUpButton).
        let value_lower = value.to_lowercase();
        let mut matched_idx: Option<usize> = None;
        let mut available: Vec<String> = Vec::with_capacity(children.len());

        for (i, &child) in children.iter().enumerate() {
            let child_title = unsafe { copy_string_attr(child, "AXTitle") }.unwrap_or_default();
            let child_value = unsafe { copy_string_attr(child, "AXValue") }.unwrap_or_default();
            available.push(child_title.clone());
            if child_title.to_lowercase() == value_lower
                || child_value.to_lowercase() == value_lower
            {
                matched_idx = Some(i);
                break;
            }
        }

        let result = if let Some(i) = matched_idx {
            let child = children[i];
            let opt_title =
                unsafe { copy_string_attr(child, "AXTitle") }.unwrap_or_else(|| value.to_string());
            let dispatch = crate::foreground_activity::check_request()
                .map(|()| unsafe { perform_action(child, "AXPress") });
            if let Err(error) = dispatch {
                Err(error)
            } else if matches!(dispatch, Ok(code) if code == kAXErrorSuccess) {
                Ok(format!(
                    "✅ Selected '{opt_title}' in AXPopUpButton [{element_index}] \
                     \"{element_title}\" via AX child AXPress."
                ))
            } else {
                Err(anyhow::anyhow!("AXPress on child option failed"))
            }
        } else {
            let avail = available
                .iter()
                .map(|t| format!("\"{t}\""))
                .collect::<Vec<_>>()
                .join(", ");
            anyhow::bail!(
                "No AX child matching '{value}' in AXPopUpButton [{element_index}] \
                 \"{element_title}\". Available: [{avail}]"
            )
        };

        // Release children (copy_children retains each one).
        for &child in &children {
            unsafe {
                CFRelease(child as _);
            }
        }

        return result;
    }

    // Strategy 2: Safari/WebKit — no AX children when popup is closed.
    // Use osascript do JavaScript to set the <select> element's DOM value.
    let app_name = crate::apps::get_app_name_for_pid(pid).unwrap_or_default();

    if app_name != "Safari" {
        anyhow::bail!(
            "AXPopUpButton [{element_index}] '{element_title}' has no AX children and \
             target is '{app_name}' (not Safari) — no fallback available."
        )
    }

    set_select_via_js(element_index, element_title, value)
}

// ── Safari JavaScript fallback ───────────────────────────────────────────────

/// Set an HTML `<select>` value in Safari via `osascript do JavaScript`.
/// Searches all `<select>` elements for an `<option>` whose text or value matches
/// `value` (case-insensitive), then sets it and dispatches a `change` event.
fn set_select_via_js(
    element_index: usize,
    element_title: &str,
    value: &str,
) -> anyhow::Result<String> {
    // Percent-encode the lowercased value using only unreserved URL characters
    // as the allowed set, matching the Swift reference's percent-encoding approach.
    // This makes the string safe to embed in both a JS single-quoted string
    // (via decodeURIComponent) and an AppleScript double-quoted string.
    let v_low = value.to_lowercase();
    let v_encoded = percent_encode_unreserved(&v_low);

    // JavaScript that matches the Swift reference verbatim.
    let js = format!(
        "(function(){{\
         var v=decodeURIComponent('{v_encoded}');\
         var ss=document.querySelectorAll('select'),opts=[];\
         for(var i=0;i<ss.length;i++){{\
         for(var j=0;j<ss[i].options.length;j++){{\
         var t=ss[i].options[j].text.toLowerCase(),\
         u=ss[i].options[j].value.toLowerCase();\
         opts.push(t+'|'+u);\
         if(t===v||u===v){{\
         ss[i].value=ss[i].options[j].value;\
         ss[i].dispatchEvent(new Event('change',{{bubbles:true}}));\
         return 'SET:'+ss[i].value;}}}}\
         }}return 'NOTFOUND:'+opts.join(',');\
         }})()"
    );

    let apple_script =
        format!("tell application \"Safari\" to do JavaScript \"{js}\" in front document");

    // Spawn osascript with a 10-second deadline. A stuck Safari permission
    // prompt or unresponsive renderer can cause wait() to block indefinitely,
    // which would stall the MCP tool handler permanently.
    crate::foreground_activity::check_request()?;
    let child = std::process::Command::new("osascript")
        .arg("-e")
        .arg(&apple_script)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| anyhow::anyhow!("osascript launch failed: {e}"))?;

    let out = wait_for_owned_script(
        child,
        std::time::Duration::from_secs(10),
        crate::foreground_activity::check_request,
    )?;

    let raw = String::from_utf8_lossy(&out.stdout).trim().to_string();

    if let Some(dom_val) = raw.strip_prefix("SET:") {
        Ok(format!(
            "✅ Set select [{element_index}] '{element_title}' to '{value}' via \
             Safari JavaScript (DOM value: \"{dom_val}\")."
        ))
    } else if let Some(available) = raw.strip_prefix("NOTFOUND:") {
        anyhow::bail!(
            "No <option> matching '{value}' found in any <select>. \
             Available (text|value): {available}"
        )
    } else if raw.is_empty() && !out.status.success() {
        let err_text = String::from_utf8_lossy(&out.stderr);
        anyhow::bail!("osascript failed: {}", err_text.trim())
    } else {
        anyhow::bail!(
            "JavaScript returned unexpected output: {}",
            &raw[..raw.len().min(200)]
        )
    }
}

/// The helper is part of this native operation, not a detached GUI actor.
/// Stop and reap it before reporting cancellation/error; Drop covers unwinding
/// without introducing an input retry or changing any application permission.
struct OwnedScriptChild(Option<std::process::Child>);

impl OwnedScriptChild {
    fn stop_and_reap(&mut self) -> anyhow::Result<()> {
        let Some(child) = self.0.as_mut() else {
            return Ok(());
        };
        // The process can exit between the poll and kill. A successful wait is
        // the authoritative settlement proof even when kill reports that race.
        let _ = child.kill();
        child.wait().map_err(|error| {
            crate::foreground_activity::mark_native_cleanup_unconfirmed();
            anyhow::anyhow!("osascript cleanup could not confirm child exit: {error}")
        })?;
        self.0.take();
        Ok(())
    }
}

impl Drop for OwnedScriptChild {
    fn drop(&mut self) {
        if let Err(error) = self.stop_and_reap() {
            // Preserve the settlement failure even during unwinding; callers
            // must not mistake a later ordinary ToolResult for safe cleanup.
            crate::foreground_activity::mark_native_cleanup_unconfirmed();
            tracing::error!("owned script cleanup failed: {error}");
        }
    }
}

fn wait_for_owned_script(
    child: std::process::Child,
    timeout: std::time::Duration,
    mut check_request: impl FnMut() -> anyhow::Result<()>,
) -> anyhow::Result<std::process::Output> {
    let mut owned = OwnedScriptChild(Some(child));
    let deadline = std::time::Instant::now() + timeout;
    loop {
        let stop = check_request().err().or_else(|| {
            (std::time::Instant::now() >= deadline)
                .then(|| anyhow::anyhow!("osascript timed out before completing"))
        });
        if let Some(error) = stop {
            owned.stop_and_reap()?;
            return Err(error);
        }
        match owned
            .0
            .as_mut()
            .expect("owned child is present until exit")
            .try_wait()
        {
            Ok(Some(_)) => {
                // try_wait has already reaped the child. Output collection can
                // now fail without leaving a live helper behind.
                return owned
                    .0
                    .take()
                    .expect("exited child is present")
                    .wait_with_output()
                    .map_err(|error| anyhow::anyhow!("osascript output error: {error}"));
            }
            Ok(None) => std::thread::sleep(std::time::Duration::from_millis(50)),
            Err(error) => {
                owned.stop_and_reap()?;
                return Err(anyhow::anyhow!("osascript wait error: {error}"));
            }
        }
    }
}

// ── Percent-encoding helper ──────────────────────────────────────────────────

/// Percent-encode a string, leaving only unreserved URL characters (`-._~` +
/// alphanumerics) unencoded.  Matches the Swift reference's approach.
fn percent_encode_unreserved(s: &str) -> String {
    let mut out = String::with_capacity(s.len() * 3);
    for b in s.bytes() {
        if b.is_ascii_alphanumeric() || b == b'-' || b == b'.' || b == b'_' || b == b'~' {
            out.push(b as char);
        } else {
            out.push('%');
            out.push(hex_digit(b >> 4));
            out.push(hex_digit(b & 0xF));
        }
    }
    out
}

fn hex_digit(n: u8) -> char {
    match n {
        0..=9 => (b'0' + n) as char,
        10..=15 => (b'A' + n - 10) as char,
        _ => '0',
    }
}

#[cfg(test)]
mod tests {
    use super::{
        apply_surface_trust, apply_verification_label, classify_write, kAXErrorSuccess,
        write_native_value, NativeValueField, NativeValueResponse, SetValueOutcome,
    };
    use std::cell::{Cell, RefCell};

    struct EditorField {
        focused: Cell<bool>,
        delayed_focus_reads: Cell<usize>,
        focus_settable: bool,
        focus_sticks: bool,
        focus_error: i32,
        revoke_on_validation: Option<usize>,
        revoke_after_focus: bool,
        revoke_after_write: bool,
        write_error: i32,
        write_applies: bool,
        display: RefCell<String>,
        stored: RefCell<String>,
        calls: RefCell<Vec<&'static str>>,
    }

    impl EditorField {
        fn new() -> Self {
            Self {
                focused: Cell::new(false),
                delayed_focus_reads: Cell::new(0),
                focus_settable: true,
                focus_sticks: true,
                focus_error: kAXErrorSuccess,
                revoke_on_validation: None,
                revoke_after_focus: false,
                revoke_after_write: false,
                write_error: kAXErrorSuccess,
                write_applies: true,
                display: RefCell::new("old".into()),
                stored: RefCell::new("old".into()),
                calls: RefCell::new(Vec::new()),
            }
        }
    }

    impl NativeValueField for EditorField {
        fn validate(&self) -> anyhow::Result<()> {
            self.calls.borrow_mut().push("validate");
            if self.revoke_on_validation.is_some_and(|limit| {
                self.calls.borrow().iter().filter(|call| **call == "validate").count() >= limit
            }) {
                anyhow::bail!("target revoked while waiting for its editor");
            }
            if self.revoke_after_focus && self.focused.get() {
                anyhow::bail!("popover detached after focus");
            }
            if self.revoke_after_write && self.calls.borrow().contains(&"write") {
                anyhow::bail!("popover detached after write");
            }
            Ok(())
        }
        fn focused(&self) -> Option<bool> {
            if self.focused.get() && self.delayed_focus_reads.get() > 0 {
                self.delayed_focus_reads.set(self.delayed_focus_reads.get() - 1);
                return Some(false);
            }
            Some(self.focused.get())
        }
        fn focus_settable(&self) -> bool {
            self.focus_settable
        }
        fn focus(&self) -> i32 {
            self.calls.borrow_mut().push("focus");
            self.focused.set(self.focus_sticks);
            self.focus_error
        }
        fn value(&self) -> Option<String> {
            self.calls.borrow_mut().push("read");
            Some(self.display.borrow().clone())
        }
        fn set_value(&self, value: &str) -> i32 {
            self.calls.borrow_mut().push("write");
            if self.write_applies {
                *self.display.borrow_mut() = value.into();
                // Observed Cocoa behavior: a value assigned outside the field
                // editor can change the control without updating the model.
                if self.focused.get() {
                    *self.stored.borrow_mut() = value.into();
                }
            }
            self.write_error
        }
    }

    #[test]
    fn native_popover_value_enters_editor_before_writing() {
        let field = EditorField::new();
        let outcome = write_native_value(&field, 81, "new").unwrap();
        assert_eq!(field.stored.borrow().as_str(), "new");
        assert_eq!(outcome.verified, Some(true));
        let calls = field.calls.borrow();
        assert!(
            calls.iter().position(|c| *c == "focus").unwrap()
                < calls.iter().position(|c| *c == "write").unwrap()
        );
        assert_eq!(calls.iter().filter(|c| **c == "write").count(), 1);
    }

    #[test]
    fn native_popover_value_timeout_with_matching_readback_is_not_a_false_failure() {
        let mut field = EditorField::new();
        field.focused.set(true);
        field.write_error = crate::ax::bindings::kAXErrorCannotComplete;
        let outcome = write_native_value(&field, 81, "new").unwrap();
        assert_eq!(field.stored.borrow().as_str(), "new");
        assert_eq!(outcome.verified, Some(true));
        let response = outcome.native_response.unwrap();
        assert_eq!(
            response.native_error,
            Some(crate::ax::bindings::kAXErrorCannotComplete)
        );
        assert_eq!(response.value_readback_matches, Some(true));
        assert!(response.value_write_attempted);
        let calls = field.calls.borrow();
        assert!(!calls.contains(&"focus"));
        assert_eq!(calls.iter().filter(|c| **c == "write").count(), 1);
    }

    #[test]
    fn native_popover_value_timeout_without_matching_readback_stays_indeterminate() {
        let mut field = EditorField::new();
        field.focused.set(true);
        field.write_error = crate::ax::bindings::kAXErrorCannotComplete;
        field.write_applies = false;
        let error = write_native_value(&field, 81, "new")
            .err()
            .expect("unconfirmed write must not succeed");
        let response = error
            .downcast_ref::<NativeValueResponse>()
            .expect("retain native effect phase");
        assert_eq!(response.phase, "value_write");
        assert_eq!(response.value_readback_matches, Some(false));
        let public = response.result();
        assert_eq!(
            public.structured_content.as_ref().unwrap()["effect"],
            "unverifiable"
        );
        assert_eq!(
            field
                .calls
                .borrow()
                .iter()
                .filter(|c| **c == "write")
                .count(),
            1
        );
    }

    #[test]
    fn native_popover_value_does_not_write_when_editor_focus_does_not_stick() {
        let mut field = EditorField::new();
        field.focus_sticks = false;
        let error = write_native_value(&field, 81, "new")
            .err()
            .expect("focus must be read back before value input");
        let response = error.downcast_ref::<NativeValueResponse>().unwrap();
        assert_eq!(response.phase, "editor_focus");
        assert!(!response.value_write_attempted);
        assert!(!field.calls.borrow().contains(&"write"));
        assert_eq!(field.calls.borrow().iter().filter(|call| **call == "focus").count(), 1);
    }

    #[test]
    fn native_value_waits_for_delayed_editor_without_replaying_input() {
        let field = EditorField::new();
        field.delayed_focus_reads.set(3);
        let outcome = write_native_value(&field, 81, "new").unwrap();
        assert_eq!(field.delayed_focus_reads.get(), 0);
        assert_eq!(field.stored.borrow().as_str(), "new");
        assert_eq!(outcome.verified, Some(true));
        let calls = field.calls.borrow();
        assert_eq!(calls.iter().filter(|call| **call == "focus").count(), 1);
        assert_eq!(calls.iter().filter(|call| **call == "write").count(), 1);
    }

    #[test]
    fn native_value_revocation_during_editor_wait_prevents_value_write() {
        let mut field = EditorField::new();
        field.delayed_focus_reads.set(10);
        field.revoke_on_validation = Some(3);
        assert!(write_native_value(&field, 81, "new").is_err());
        let calls = field.calls.borrow();
        assert_eq!(calls.iter().filter(|call| **call == "focus").count(), 1);
        assert!(!calls.contains(&"write"));
    }

    #[test]
    fn native_value_failed_focus_response_never_continues_to_value_write() {
        let mut field = EditorField::new();
        field.focus_error = crate::ax::bindings::kAXErrorCannotComplete;
        let error = write_native_value(&field, 81, "new").err().unwrap();
        let response = error.downcast_ref::<NativeValueResponse>().unwrap();
        assert_eq!(response.phase, "editor_focus");
        assert_eq!(response.native_error, Some(crate::ax::bindings::kAXErrorCannotComplete));
        assert!(!response.value_write_attempted);
        let calls = field.calls.borrow();
        assert_eq!(calls.iter().filter(|call| **call == "focus").count(), 1);
        assert!(!calls.contains(&"write"));
    }

    #[test]
    fn native_popover_value_rechecks_attachment_after_editor_focus() {
        let mut field = EditorField::new();
        field.revoke_after_focus = true;
        assert!(write_native_value(&field, 81, "new").is_err());
        assert!(!field.calls.borrow().contains(&"write"));
    }

    #[test]
    fn native_popover_value_does_not_write_without_a_supported_editor() {
        let mut field = EditorField::new();
        field.focus_settable = false;
        assert!(write_native_value(&field, 81, "new").is_err());
        assert!(!field.calls.borrow().contains(&"focus"));
        assert!(!field.calls.borrow().contains(&"write"));
    }

    #[test]
    fn native_popover_value_does_not_confirm_a_detached_readback_after_timeout() {
        let mut field = EditorField::new();
        field.focused.set(true);
        field.revoke_after_write = true;
        field.write_error = crate::ax::bindings::kAXErrorCannotComplete;
        let error = write_native_value(&field, 81, "new").err().unwrap();
        let response = error.downcast_ref::<NativeValueResponse>().unwrap();
        assert_eq!(response.value_readback_matches, None);
        assert_eq!(
            field
                .calls
                .borrow()
                .iter()
                .filter(|c| **c == "write")
                .count(),
            1
        );
        assert_eq!(
            field
                .calls
                .borrow()
                .iter()
                .filter(|c| **c == "read")
                .count(),
            1
        );
    }

    fn script_fixture() -> std::process::Child {
        std::process::Command::new("/bin/sleep")
            .arg("30")
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .expect("spawn non-GUI owned-child fixture")
    }

    fn assert_reaped(pid: u32) {
        let mut status = 0;
        assert_eq!(
            unsafe { libc::waitpid(pid as i32, &mut status, libc::WNOHANG) },
            -1
        );
        assert_eq!(
            std::io::Error::last_os_error().raw_os_error(),
            Some(libc::ECHILD)
        );
    }

    #[test]
    fn owned_script_child_is_reaped_before_cancel_or_timeout_returns() {
        for cancelled in [true, false] {
            let child = script_fixture();
            let pid = child.id();
            let result = super::wait_for_owned_script(child, std::time::Duration::ZERO, || {
                if cancelled {
                    anyhow::bail!("test request cancelled");
                }
                Ok(())
            });
            assert!(result.is_err());
            assert_reaped(pid);
        }
    }

    #[test]
    fn owned_script_child_is_reaped_during_unwind() {
        let child = script_fixture();
        let pid = child.id();
        let panic = std::panic::catch_unwind(|| {
            let _owned = super::OwnedScriptChild(Some(child));
            panic!("test native task unwind");
        });
        assert!(panic.is_err());
        assert_reaped(pid);
    }

    #[test]
    fn unreadable_value_reports_neither_verified_nor_changed() {
        // AXValue is not exposed: the write can be neither confirmed nor denied,
        // so the tool must not claim success on the return code alone.
        assert_eq!(
            classify_write(Some("old"), None, "new", false),
            (None, None)
        );
    }

    #[test]
    fn matching_read_back_verifies_the_write() {
        assert_eq!(
            classify_write(Some("old"), Some("new"), "new", false),
            (Some(true), Some(true))
        );
    }

    #[test]
    fn echoed_but_wrong_value_fails_verification() {
        // Web content behind an AXWebArea accepts the write and echoes a value
        // the renderer never took. A success return code must not be reported
        // as a verified write.
        assert_eq!(
            classify_write(Some("old"), Some("old"), "new", false),
            (Some(false), Some(false))
        );
    }

    #[test]
    fn idempotent_write_is_verified_but_unchanged() {
        assert_eq!(
            classify_write(Some("same"), Some("same"), "same", false),
            (Some(true), Some(false))
        );
    }

    #[test]
    fn numeric_controls_compare_numerically() {
        // AXSlider reports "25.0" for a requested "25".
        assert_eq!(
            classify_write(Some("10"), Some("25.000000001"), "25", true),
            (Some(true), Some(true))
        );
    }

    #[test]
    fn numeric_text_is_not_normalised_on_a_text_target() {
        assert_eq!(
            classify_write(Some("old"), Some("7"), "007", false),
            (Some(false), Some(true))
        );
    }

    #[test]
    fn missing_before_still_verifies_numeric_after() {
        assert_eq!(
            classify_write(None, Some("25.0"), "25", true),
            (Some(true), None)
        );
    }

    #[test]
    fn web_content_ax_echo_is_never_reported_as_verified() {
        let mut outcome = SetValueOutcome {
            detail: "Set value.".to_owned(),
            verified: Some(true),
            changed: Some(true),
            native_response: None,
        };
        apply_surface_trust(&mut outcome, true);
        assert_eq!(outcome.verified, Some(false));
        assert_eq!(outcome.changed, None);
        assert!(outcome.detail.contains("not trusted for web content"));
    }

    #[test]
    fn native_read_back_remains_trusted() {
        let mut outcome = SetValueOutcome {
            detail: "Set value.".to_owned(),
            verified: Some(true),
            changed: Some(true),
            native_response: None,
        };
        apply_surface_trust(&mut outcome, false);
        assert_eq!(outcome.verified, Some(true));
        assert_eq!(outcome.changed, Some(true));
        assert_eq!(outcome.detail, "Set value.");
    }

    #[test]
    fn unverified_result_does_not_keep_a_success_checkmark() {
        let mut outcome = SetValueOutcome {
            detail: "✅ Set AXValue on [4] AXTextField.".to_owned(),
            verified: Some(false),
            changed: Some(false),
            native_response: None,
        };
        apply_verification_label(&mut outcome);
        assert_eq!(
            outcome.detail,
            "📨 Sent (unverified) AXValue on [4] AXTextField."
        );
    }
}
