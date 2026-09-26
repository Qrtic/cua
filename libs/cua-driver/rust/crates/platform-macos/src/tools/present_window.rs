//! Explicit presentation of one observed ordinary window. This is not a
//! fallback for background input and never activates all application windows.

use std::sync::Arc;
use std::time::{Duration, Instant};

use async_trait::async_trait;
use core_foundation::base::{CFEqual, CFRelease};
use cua_driver_core::{
    protocol::ToolResult,
    tool::{Tool, ToolDef},
};
use serde_json::{json, Value};

use crate::ax::bindings::{
    ax_get_window_id, copy_action_names, copy_ax_windows, copy_bool_attr, copy_string_attr,
    perform_action, AXUIElementCreateApplication, AXUIElementGetPid, AXUIElementRef,
};
use crate::windows::WindowInfo;

use super::ToolState;

pub struct PresentWindowTool {
    state: Arc<ToolState>,
}

impl PresentWindowTool {
    pub fn new(state: Arc<ToolState>) -> Self {
        Self { state }
    }
}

static DEF: std::sync::OnceLock<ToolDef> = std::sync::OnceLock::new();

fn def() -> &'static ToolDef {
    DEF.get_or_init(|| ToolDef {
        name: "present_window".into(),
        description: "Leave exactly one freshly observed ordinary AXWindow in front, only when the user explicitly requests presentation. Requires advertised AXRaise, an unchanged owned window, native idle/cancellation coverage, and independent focus/order verification. No application-wide activation, unhide, Space switch or foreground fallback.".into(),
        input_schema: json!({
            "type": "object",
            "required": ["pid", "window_id", "element_token", "delivery_mode", "presentation_scope"],
            "properties": {
                "pid": {"type": "integer", "minimum": 1},
                "window_id": {"type": "integer", "minimum": 1},
                "element_token": cua_driver_core::tool_schema::element_token_schema(),
                "delivery_mode": {"const": "foreground"},
                "presentation_scope": {"const": "exact_window_only_v1"}
            },
            "additionalProperties": false
        }),
        read_only: false, destructive: false, idempotent: true, open_world: false,
    })
}

fn visible_ordinary(window: &WindowInfo) -> bool {
    window.layer == 0 && window.is_on_screen && window.on_current_space == Some(true)
}

/// Raising the requested window may change its order, but must not raise a
/// sibling over any pre-existing foreign ordinary window. Also reject newly
/// exposed siblings. Failed inventories never enter this comparison.
fn siblings_preserved(before: &[WindowInfo], after: &[WindowInfo], pid: i32, target: u32) -> bool {
    let siblings: Vec<_> = before
        .iter()
        .filter(|w| w.pid == pid && w.window_id != target)
        .collect();
    if after
        .iter()
        .filter(|w| w.pid == pid && w.window_id != target && visible_ordinary(w))
        .any(|w| {
            !siblings
                .iter()
                .any(|old| old.window_id == w.window_id && visible_ordinary(old))
        })
    {
        return false;
    }
    for old in siblings.into_iter().filter(|w| visible_ordinary(w)) {
        let Some(current) = after
            .iter()
            .find(|w| w.pid == pid && w.window_id == old.window_id && visible_ordinary(w))
        else {
            return false;
        };
        for foreign in before
            .iter()
            .filter(|w| w.pid != pid && visible_ordinary(w))
        {
            let Some(now) = after.iter().find(|w| {
                w.pid == foreign.pid && w.window_id == foreign.window_id && visible_ordinary(w)
            }) else {
                return false;
            };
            if (old.z_index > foreign.z_index) != (current.z_index > now.z_index) {
                return false;
            }
        }
    }
    true
}

fn admitted_root(
    role: Option<&str>,
    owner: Option<i32>,
    window: Option<u32>,
    minimized: Option<bool>,
    advertised_raise: bool,
    exact_member: bool,
    pid: i32,
    target: u32,
) -> bool {
    role == Some("AXWindow")
        && owner == Some(pid)
        && window == Some(target)
        && minimized == Some(false)
        && advertised_raise
        && exact_member
}

unsafe fn validate_root(element: AXUIElementRef, pid: i32, target: u32) -> anyhow::Result<()> {
    let mut owner = 0;
    let owner = (AXUIElementGetPid(element, &mut owner) == 0).then_some(owner);
    let app = AXUIElementCreateApplication(pid);
    anyhow::ensure!(
        !app.is_null(),
        "exact presentation application is unavailable"
    );
    let mut matches = 0;
    for window in copy_ax_windows(app) {
        if CFEqual(window as _, element as _) != 0 && ax_get_window_id(window) == Some(target) {
            matches += 1;
        }
        CFRelease(window as _);
    }
    CFRelease(app as _);
    anyhow::ensure!(
        admitted_root(
            copy_string_attr(element, "AXRole").as_deref(),
            owner,
            ax_get_window_id(element),
            copy_bool_attr(element, "AXMinimized"),
            copy_action_names(element).iter().any(|a| a == "AXRaise"),
            matches == 1,
            pid,
            target,
        ),
        "presentation needs the same non-minimized AXWindow root with advertised AXRaise"
    );
    Ok(())
}

fn window_snapshot() -> anyhow::Result<Vec<WindowInfo>> {
    let snapshot = crate::windows::all_automation_windows_with_space_snapshot();
    anyhow::ensure!(
        snapshot.succeeded,
        "presentation window inventory is unavailable"
    );
    Ok(snapshot.windows)
}

fn exact_front(pid: i32, window: u32, windows: &[WindowInfo]) -> bool {
    crate::input::skylight::front_process_matches(pid, window) == Some(true)
        && crate::ax::bindings::focused_window_id_of_pid(pid) == Some(window)
        && windows
            .iter()
            .filter(|w| visible_ordinary(w))
            .max_by_key(|w| w.z_index)
            .is_some_and(|w| w.pid == pid && w.window_id == window)
}

fn refused(message: impl ToString, attempted: bool) -> ToolResult {
    ToolResult::error(message.to_string()).with_structured(json!({
        "code": if attempted { "window_presentation_unverified" } else { "window_presentation_refused" },
        "effect": if attempted { "unverifiable" } else { "refused" },
        "verified": false, "retryable": false, "attempted": attempted,
    }))
}

#[async_trait]
impl Tool for PresentWindowTool {
    fn def(&self) -> &ToolDef {
        def()
    }

    async fn invoke(&self, args: Value) -> ToolResult {
        use cua_driver_core::tool_args::ArgsExt;
        let pid = match args.require_i32("pid") {
            Ok(p) if p > 0 => p,
            _ => return refused("positive pid required", false),
        };
        let window = match args.opt_u32("window_id") {
            Ok(Some(w)) if w > 0 => w,
            _ => return refused("exact window_id required", false),
        };
        if args.get("delivery_mode").and_then(Value::as_str) != Some("foreground")
            || args.get("presentation_scope").and_then(Value::as_str)
                != Some("exact_window_only_v1")
            || args.get("foreground_segment_id").is_some()
        {
            return refused(
                "explicit standalone exact-window presentation is required",
                false,
            );
        }
        let token = match args.require_str("element_token") {
            Ok(token) => token,
            Err(error) => return error,
        };
        let resolved = match cua_driver_core::element_token::resolve_element_args(
            pid,
            None,
            Some(&token),
            None,
            Some(window as u64),
            "present_window",
        ) {
            Ok(value) => value,
            Err(error) => return error,
        };
        let cua_driver_core::element_token::ResolvedElement::Element {
            window_id: Some(resolved_window),
            element_index,
            snapshot_id,
            ..
        } = resolved
        else {
            return refused("observed window token is required", false);
        };
        if resolved_window != window {
            return refused("window token must match the exact requested window", false);
        }
        let Some(element) = self.state.element_cache.get_element_retained_for_snapshot(
            pid,
            window,
            snapshot_id,
            element_index,
        ) else {
            return cua_driver_core::element_token::stale_element_cache_result(
                "present_window",
                pid,
                window,
                snapshot_id,
            );
        };
        if let Err(refusal) = super::guard_same_pid_transient_target(pid, Some(window)).await {
            return refusal;
        }
        let state = Arc::clone(&self.state);
        let result = crate::foreground_activity::spawn_blocking(move || {
            let mut attempted = false;
            let outcome = (|| -> anyhow::Result<()> {
                let deadline = Instant::now() + Duration::from_secs(4);
                let check_target = || -> anyhow::Result<()> {
                    crate::foreground_activity::check_request()?;
                    anyhow::ensure!(Instant::now() < deadline, "exact presentation deadline expired");
                    let current = state.element_cache.get_element_retained_for_snapshot(pid, window, snapshot_id, element_index)
                        .ok_or_else(|| anyhow::anyhow!("presentation observation was replaced"))?;
                    anyhow::ensure!(unsafe { CFEqual(current.as_ptr() as _, element.as_ptr() as _) != 0 }, "presentation token changed");
                    unsafe { validate_root(element.as_ptr() as AXUIElementRef, pid, window)?; }
                    let windows = window_snapshot()?;
                    anyhow::ensure!(windows.iter().any(|w| w.pid == pid && w.window_id == window && visible_ordinary(w)),
                        "presentation target is hidden, off-Space or unavailable");
                    crate::foreground_activity::check_request()?;
                    anyhow::ensure!(Instant::now() < deadline, "exact presentation deadline expired");
                    Ok(())
                };
                check_target()?;
                let before = window_snapshot()?;
                let episode = crate::foreground_activity::Episode::begin(pid, window)?;
                let presented = (|| -> anyhow::Result<()> {
                    if !exact_front(pid, window, &before) {
                        check_target()?;
                        attempted = true;
                        crate::input::skylight::present_exact_window_guarded(pid, window, check_target)?;
                        check_target()?;
                        let ax_status = unsafe { perform_action(element.as_ptr() as AXUIElementRef, "AXRaise") };
                        tracing::debug!(pid, window, ax_status, "Explicit exact-window presentation requested");
                    }
                    let mut stable = None;
                    loop {
                        episode.check()?;
                        let now = Instant::now();
                        anyhow::ensure!(now < deadline, "exact presentation was not verified before its deadline");
                        let after = window_snapshot()?;
                        anyhow::ensure!(siblings_preserved(&before, &after, pid, window), "presentation changed another application window's order or visibility");
                        if exact_front(pid, window, &after) {
                            if now.duration_since(*stable.get_or_insert(now)) >= Duration::from_millis(100) { break; }
                        } else { stable = None; }
                        std::thread::sleep(Duration::from_millis(20));
                    }
                    check_target()?;
                    Ok(())
                })();
                episode.finish_presenting(presented)
            })();
            match outcome {
                Ok(()) => ToolResult::text("The requested window is now in front; sibling windows retained their order.")
                    .with_structured(json!({"code":"window_presentation_verified", "effect":"confirmed", "route":"system_api", "delivery":"foreground", "verified":true, "pid":pid, "window_id":window, "presentation_scope":"exact_window_only_v1", "siblings_preserved":true})),
                Err(error) => refused(format!("Exact-window presentation stopped: {error:#}"), attempted),
            }
        }).await;
        match result {
            Ok(result) => result,
            Err(error) => refused(
                format!("Presentation worker did not complete: {error}"),
                true,
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn w(pid: i32, id: u32, z: usize, visible: bool) -> WindowInfo {
        WindowInfo {
            pid,
            window_id: id,
            z_index: z,
            is_on_screen: visible,
            layer: 0,
            on_current_space: Some(true),
            app_name: String::new(),
            title: String::new(),
            current_space_id: Some(1),
            space_ids: Some(vec![1]),
            bounds: crate::windows::WindowBounds {
                x: 0.0,
                y: 0.0,
                width: 100.0,
                height: 100.0,
            },
        }
    }
    #[test]
    fn only_requested_window_may_cross_foreign_windows() {
        let before = vec![w(42, 1, 1, true), w(42, 2, 2, true), w(9, 3, 3, true)];
        assert!(siblings_preserved(
            &before,
            &[w(42, 1, 4, true), w(42, 2, 2, true), w(9, 3, 3, true)],
            42,
            1
        ));
        assert!(!siblings_preserved(
            &before,
            &[w(42, 1, 4, true), w(42, 2, 3, true), w(9, 3, 2, true)],
            42,
            1
        ));
    }
    #[test]
    fn hidden_new_replaced_or_closed_sibling_cannot_be_claimed_preserved() {
        let before = vec![
            w(42, 1, 1, true),
            w(42, 2, 2, true),
            w(9, 3, 3, true),
            w(42, 4, 0, false),
        ];
        for after in [
            vec![
                w(42, 1, 5, true),
                w(42, 2, 2, true),
                w(9, 3, 3, true),
                w(42, 4, 4, true),
            ],
            vec![
                w(42, 1, 5, true),
                w(42, 2, 2, true),
                w(9, 3, 3, true),
                w(42, 5, 4, true),
            ],
            vec![w(42, 1, 5, true), w(43, 2, 2, true), w(9, 3, 3, true)],
            vec![w(42, 1, 5, true), w(9, 3, 3, true)],
            vec![w(42, 1, 5, true), w(42, 2, 2, true)],
        ] {
            assert!(!siblings_preserved(&before, &after, 42, 1));
        }
    }
    #[test]
    fn presentation_requires_exact_advertised_ordinary_root() {
        assert!(admitted_root(
            Some("AXWindow"),
            Some(42),
            Some(1),
            Some(false),
            true,
            true,
            42,
            1
        ));
        for role in [None, Some("AXSheet"), Some("AXMenu"), Some("AXButton")] {
            assert!(!admitted_root(
                role,
                Some(42),
                Some(1),
                Some(false),
                true,
                true,
                42,
                1
            ));
        }
        for owner in [None, Some(9)] {
            assert!(!admitted_root(
                Some("AXWindow"),
                owner,
                Some(1),
                Some(false),
                true,
                true,
                42,
                1
            ));
        }
        for window in [None, Some(2)] {
            assert!(!admitted_root(
                Some("AXWindow"),
                Some(42),
                window,
                Some(false),
                true,
                true,
                42,
                1
            ));
        }
        for minimized in [None, Some(true)] {
            assert!(!admitted_root(
                Some("AXWindow"),
                Some(42),
                Some(1),
                minimized,
                true,
                true,
                42,
                1
            ));
        }
        assert!(!admitted_root(
            Some("AXWindow"),
            Some(42),
            Some(1),
            Some(false),
            false,
            true,
            42,
            1
        ));
        assert!(!admitted_root(
            Some("AXWindow"),
            Some(42),
            Some(1),
            Some(false),
            true,
            false,
            42,
            1
        ));
    }
}
