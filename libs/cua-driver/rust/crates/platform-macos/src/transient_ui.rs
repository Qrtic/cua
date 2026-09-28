//! Routing and detection for app-owned transient UI.
//!
//! AppKit and system frameworks sometimes put a modal prompt in an XPC view
//! service rather than in the requesting application's process.  The helper is
//! intentionally absent from `list_apps`, but its WindowServer surface still
//! needs to be observable and, after an explicit foreground escalation,
//! keyboard-addressable through the host application's stable public target.
//!
//! Some applications (notably Blender) instead create a second layer-0 window
//! in the same process for a modal workflow.  Capturing the original window can
//! still composite that front window into the returned image, while coordinates
//! and input remain scoped to the original CGWindowID.  The bounded detector
//! below recognizes only one uniquely focused, contained, frontmost successor;
//! callers must then re-address that exact window rather than silently replaying
//! coordinates against the cached host.

use std::{
    collections::HashMap,
    sync::{Mutex, MutexGuard},
    time::{Duration, Instant},
};

use core_foundation::base::{CFEqual, CFRelease, CFRetain, CFTypeRef};

use crate::ax::bindings::{
    ax_get_window_id, copy_bool_attr, copy_string_attr, try_copy_ax_windows, try_copy_element_attr,
    AXUIElementCreateApplication, AXUIElementGetPid, AXUIElementRef, AXUIElementSetMessagingTimeout,
};
use crate::windows::{WindowBounds, WindowInfo};

// AppKit's `NSModalPanelWindowLevel` / CoreGraphics layer for modal panels.
// Restricting routing to this level prevents unrelated accessory-process
// tooltips, overlays, and status items from being inferred as host UI.
const MODAL_PANEL_WINDOW_LAYER: i32 = 8;
const SHORTCUTS_HOST_BUNDLE_ID: &str = "com.apple.shortcuts";
const SHORTCUTS_HELPER_BUNDLE_ID: &str = "com.apple.WorkflowKit.ShortcutsViewService";
const SHORTCUTS_HELPER_SYSTEM_PATH: &str = "/System/Library/PrivateFrameworks/WorkflowKit.framework/XPCServices/ShortcutsViewService.xpc/Contents/MacOS/ShortcutsViewService";
const CRYPTEX_SYSTEM_PREFIX: &str = "/System/Volumes/Preboot/Cryptexes/";
const BLENDER_BUNDLE_ID: &str = "org.blenderfoundation.blender";
const BLENDER_FILE_VIEW_TITLE: &str = "Blender File View";

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct WindowTarget {
    pub(crate) pid: i32,
    pub(crate) window_id: u32,
}

/// Session namespace for transient input authorization.  The anonymous shape
/// is a distinct enum variant rather than a magic string, so no caller-chosen
/// `_session_id` can collide with process-scoped one-shot calls.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum TransientSessionKey {
    Anonymous,
    Session(String),
}

impl TransientSessionKey {
    pub(crate) fn from_args(args: &serde_json::Value) -> Self {
        args.get("_session_id")
            .and_then(serde_json::Value::as_str)
            .filter(|session| !session.is_empty())
            .map(|session| Self::Session(session.to_owned()))
            .unwrap_or(Self::Anonymous)
    }

    fn is_ended(&self) -> bool {
        match self {
            Self::Anonymous => false,
            Self::Session(session) => cua_driver_core::session::is_session_ended(session),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct RouteKey {
    session: TransientSessionKey,
    source: WindowTarget,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TransientRoute {
    pub(crate) source: WindowTarget,
    pub(crate) target: WindowTarget,
    /// Present only when an unbound application observation established the
    /// route. `source` is a current-context anchor, never a helper AX parent.
    pub(crate) app_context: Option<AppContextHelperProof>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct AppContextHelperProof {
    pub(crate) host_birth: crate::ax::enablement::ProcessStartStamp,
    pub(crate) helper_birth: crate::ax::enablement::ProcessStartStamp,
}

impl TransientRoute {
    pub(crate) fn is_live(self) -> bool {
        self.revalidate_with(resolve_visible_transient_helper, detect_app_context_helper)
    }

    fn revalidate_with(
        self,
        window_bound: impl FnOnce(WindowTarget) -> Option<WindowTarget>,
        app_context: impl FnOnce(WindowTarget)
            -> Result<(TransientHelperDetection, Option<AppContextHelperProof>), ()>,
    ) -> bool {
        match self.app_context {
            None => window_bound(self.source) == Some(self.target),
            Some(proof) => matches!(app_context(self.source),
                Ok((TransientHelperDetection::Unique(target), Some(current)))
                    if target == self.target && current == proof),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RouteResolution {
    None,
    Live(TransientRoute),
    Stale(TransientRoute),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TransientHelperDetection {
    None,
    Unique(WindowTarget),
    Ambiguous,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SamePidTransientClassification {
    DialogMetadata,
    TrustedBlenderFileView,
}

impl SamePidTransientClassification {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::DialogMetadata => "dialog_metadata",
            Self::TrustedBlenderFileView => "trusted_blender_file_view",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SamePidTransientProof {
    pub(crate) source: WindowTarget,
    pub(crate) target: WindowTarget,
    pub(crate) classification: SamePidTransientClassification,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SamePidTransientDetection {
    None,
    Unique(SamePidTransientProof),
    AttachedSheet(crate::ax::attached_sheet::AttachedSheetSuccessor),
    Ambiguous,
    Indeterminate,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SamePidAxWindowFacts {
    window_id: u32,
    /// Position in the application's `AXWindows` array (front/focused first).
    order: usize,
    subrole: Option<String>,
    identifier: Option<String>,
    modal: Option<bool>,
    focused: Option<bool>,
    main: Option<bool>,
    /// Application-level references remain meaningful when a background app's
    /// windows all report AXFocused=false. These can require a fresh context
    /// observation, but never authorize a modal redirect by themselves.
    app_focused: bool,
    app_main: bool,
}

impl SamePidAxWindowFacts {
    fn has_dialog_metadata(&self) -> bool {
        self.modal == Some(true)
            || self
                .subrole
                .as_deref()
                .is_some_and(|value| matches!(value, "AXDialog" | "AXSystemDialog" | "AXSheet"))
            || self
                .identifier
                .as_deref()
                .is_some_and(|value| matches!(value, "open-panel" | "save-panel"))
    }
}

impl TransientHelperDetection {
    pub(crate) fn unique_target(self) -> Option<WindowTarget> {
        match self {
            Self::Unique(target) => Some(target),
            Self::None | Self::Ambiguous => None,
        }
    }

    pub(crate) fn helper_is_visible(self) -> bool {
        !matches!(self, Self::None)
    }
}

/// Observation-created aliases from a stable host window to its current
/// out-of-process transient.  Entries never authorize input on their own:
/// every lookup revalidates the WindowServer/process evidence, and callers use
/// them only for the explicit foreground keyboard rung.
#[derive(Default)]
pub(crate) struct TransientUiRegistry {
    inner: Mutex<HashMap<RouteKey, TransientRoute>>,
}

impl TransientUiRegistry {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn record(
        &self,
        session: &TransientSessionKey,
        source: WindowTarget,
        target: Option<WindowTarget>,
    ) {
        self.record_route(session, source, target.map(|target| TransientRoute {
            source, target, app_context: None,
        }));
    }

    pub(crate) fn record_route(
        &self,
        session: &TransientSessionKey,
        source: WindowTarget,
        route: Option<TransientRoute>,
    ) {
        let mut routes = self.lock_routes();
        let key = RouteKey {
            session: session.clone(),
            source,
        };
        // Check after acquiring the registry lock. If session_end raced this
        // call, its global ended marker is already authoritative and this
        // write must not recreate an alias after the cleanup hook removed it.
        if session.is_ended() {
            routes.remove(&key);
            return;
        }
        match route.filter(|route| route.source == source) {
            Some(route) => {
                routes.insert(key, route);
            }
            None => {
                routes.remove(&key);
            }
        }
    }

    pub(crate) fn clear_route(
        &self,
        session: &TransientSessionKey,
        source: WindowTarget,
    ) -> Option<WindowTarget> {
        self.lock_routes().remove(&RouteKey {
            session: session.clone(),
            source,
        }).map(|route| route.target)
    }

    pub(crate) fn clear_session(&self, session: &str) {
        let session = TransientSessionKey::Session(session.to_owned());
        self.lock_routes().retain(|key, _| key.session != session);
    }

    #[cfg(test)]
    pub(crate) fn recorded_target(
        &self,
        session: &TransientSessionKey,
        source: WindowTarget,
    ) -> Option<WindowTarget> {
        self.lock_routes()
            .get(&RouteKey {
                session: session.clone(),
                source,
            })
            .map(|route| route.target)
    }

    /// Revalidate the recorded proof scope against fresh WindowServer/process
    /// state and, for app-context routes, complete AX identity evidence.  A changed/disappeared helper is reported as
    /// stale instead of falling back to the host window: typing into the host's
    /// previously focused field would be the dangerous failure mode.
    pub(crate) fn resolve_live(
        &self,
        session: &TransientSessionKey,
        source: WindowTarget,
    ) -> RouteResolution {
        self.resolve_route_with(session, source, TransientRoute::is_live)
    }

    #[cfg(test)]
    fn resolve_with(
        &self,
        session: &TransientSessionKey,
        source: WindowTarget,
        resolve: impl FnOnce(WindowTarget) -> Option<WindowTarget>,
    ) -> RouteResolution {
        self.resolve_route_with(session, source, |route| resolve(route.source) == Some(route.target))
    }

    fn resolve_route_with(
        &self,
        session: &TransientSessionKey,
        source: WindowTarget,
        resolve: impl FnOnce(TransientRoute) -> bool,
    ) -> RouteResolution {
        let key = RouteKey {
            session: session.clone(),
            source,
        };
        let recorded = {
            let mut routes = self.lock_routes();
            if session.is_ended() {
                routes.remove(&key);
                None
            } else {
                routes.get(&key).copied()
            }
        };
        let Some(route) = recorded else {
            return RouteResolution::None;
        };

        let live = resolve(route);
        let mut routes = self.lock_routes();
        if session.is_ended() {
            if routes.get(&key).copied() == Some(route) {
                routes.remove(&key);
            }
            return RouteResolution::Stale(route);
        }
        // Observation may have replaced this route while WindowServer was
        // being queried. Never delete or authorize against the newer value.
        if routes.get(&key).copied() != Some(route) {
            return RouteResolution::Stale(route);
        }
        if live {
            RouteResolution::Live(route)
        } else {
            routes.remove(&key);
            RouteResolution::Stale(route)
        }
    }

    /// A poisoned registry must not take down the driver or retain an input
    /// authorization that could have been only partially updated.  Clear all
    /// aliases before recovering the mutex, making the failure mode equivalent
    /// to "no transient route observed" until the next successful observation.
    fn lock_routes(&self) -> MutexGuard<'_, HashMap<RouteKey, TransientRoute>> {
        match self.inner.lock() {
            Ok(routes) => routes,
            Err(poisoned) => {
                let mut routes = poisoned.into_inner();
                routes.clear();
                self.inner.clear_poison();
                routes
            }
        }
    }
}

pub(crate) fn resolve_visible_transient_helper(source: WindowTarget) -> Option<WindowTarget> {
    detect_visible_transient_helper(source).unique_target()
}

/// Detect a same-process transient window that has taken the app's current
/// context from `source`, including while the application is in the background.
///
/// This is intentionally much narrower than "pick the topmost window for the
/// pid".  A candidate must be a live layer-0 AX window on the same current
/// Space, strictly contained by the requested source, precede it in the app's
/// AX window order, and be both the application's focused and main AX window
/// while the source is neither. Generic windows additionally require native
/// dialog/modal metadata. Blender 4.5's File View exposes neither, so its only
/// fallback is a deliberately narrow bundle-id plus exact native window-title
/// allowlist. A merely focused, contained sibling is never redirectable.
/// Application AXFocusedWindow/AXMainWindow references can also require an
/// explicit context handoff when AXFocused=false on background windows. They
/// only refuse the stale source; they do not supply missing modal authority.
pub(crate) fn detect_same_pid_transient_in_front(
    source: WindowTarget,
) -> SamePidTransientDetection {
    let enumeration = crate::windows::all_automation_windows_with_space_snapshot();
    if !enumeration.succeeded {
        return SamePidTransientDetection::Indeterminate;
    }
    let windows = enumeration.windows;
    let has_geometry_candidate = has_same_pid_transient_geometry_candidate(&windows, source);
    // AppKit can omit an attached AXSheet from AXWindows and leave the document
    // as AXMainWindow. Geometry only gates this read; reciprocal AX attachment,
    // exact focus, ownership and visible-chain revalidation authorize the hop.
    if windows.iter().any(|window| window.pid == source.pid
        && window.window_id != source.window_id && window.is_on_screen
        && window.on_current_space != Some(false))
    {
        use crate::ax::attached_sheet::FocusedSheetContext;
        let sheet_deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
        match crate::ax::attached_sheet::focused_attached_sheet_context(
            source.pid, source.window_id, has_geometry_candidate, sheet_deadline,
        ) {
            Some(FocusedSheetContext::Successor(proof)) => {
                return SamePidTransientDetection::AttachedSheet(proof);
            }
            Some(FocusedSheetContext::ExactLeafAncestors(ancestors))
                if geometry_candidates_are_proven_ancestors(&windows, source, &ancestors) =>
            {
                // The AX proof may take time. A new unrelated window or a
                // changed physical surface must not inherit the old snapshot.
                if !recheck_ancestor_geometry(&windows, source, &ancestors,
                    || std::time::Instant::now() < sheet_deadline,
                    crate::windows::all_automation_windows_with_space_snapshot)
                {
                    return SamePidTransientDetection::Indeterminate;
                }
                tracing::debug!(target: "cua_observation_timing", pid=source.pid,
                    window_id=source.window_id, ?ancestors,
                    "Exact focused sheet: fresh geometry candidates are proven ancestors");
                return SamePidTransientDetection::None;
            }
            _ => {}
        }
    }
    // Avoid an AX round-trip on the overwhelmingly common single-window path.
    // WindowServer geometry is only a prefilter; it never authorizes a
    // redirect without the exact AX focus/main proof collected below.
    if !has_geometry_candidate {
        return SamePidTransientDetection::None;
    }
    let ax_facts = match same_pid_ax_window_facts(source.pid) {
        Ok(facts) => facts,
        Err(()) => return SamePidTransientDetection::Indeterminate,
    };
    let trusted_blender_file_view =
        crate::apps::bundle_id_for_pid(source.pid).as_deref() == Some(BLENDER_BUNDLE_ID);
    detect_same_pid_transient_in_front_in(
        &windows,
        Some(&ax_facts),
        source,
        trusted_blender_file_view,
    )
}

fn has_same_pid_transient_geometry_candidate(windows: &[WindowInfo], source: WindowTarget) -> bool {
    let Some(source_window) = eligible_same_pid_source(windows, source) else {
        return false;
    };
    windows
        .iter()
        .any(|candidate| is_same_pid_transient_geometry_candidate(candidate, source_window))
}

// Do not waive the generic guard for a proved sheet when another geometric
// candidate remains. Only the exact retained chain's ancestors are excluded.
fn geometry_candidates_are_proven_ancestors(
    windows: &[WindowInfo], source: WindowTarget, ancestors: &[u32],
) -> bool {
    let Some(source_window) = eligible_same_pid_source(windows, source) else {
        return false;
    };
    if ancestors.is_empty() || ancestors.contains(&source.window_id) { return false; }
    let mut found = false;
    for candidate in windows.iter()
        .filter(|candidate| is_same_pid_transient_geometry_candidate(candidate, source_window))
    {
        found = true;
        if !ancestors.contains(&candidate.window_id) { return false; }
    }
    found
}

fn recheck_ancestor_geometry(
    before: &[WindowInfo], source: WindowTarget, ancestors: &[u32],
    mut within_budget: impl FnMut() -> bool,
    enumerate: impl FnOnce() -> crate::windows::WindowEnumeration,
) -> bool {
    if !within_budget() { return false; }
    let current = enumerate();
    if !within_budget() || !current.succeeded { return false; }
    for id in std::iter::once(&source.window_id).chain(ancestors.iter()) {
        let old: Vec<_> = before.iter().filter(|w| w.window_id == *id).collect();
        let fresh: Vec<_> = current.windows.iter().filter(|w| w.window_id == *id).collect();
        let ([old], [fresh]) = (old.as_slice(), fresh.as_slice()) else { return false; };
        if old.pid != source.pid || fresh.pid != source.pid
            || old.layer != fresh.layer || !fresh.is_on_screen || !old.is_on_screen
            || fresh.on_current_space != Some(true)
            || old.on_current_space != fresh.on_current_space
            || old.current_space_id != fresh.current_space_id || old.space_ids != fresh.space_ids
            || [old.bounds.x, old.bounds.y, old.bounds.width, old.bounds.height]
                != [fresh.bounds.x, fresh.bounds.y, fresh.bounds.width, fresh.bounds.height]
        { return false; }
    }
    geometry_candidates_are_proven_ancestors(&current.windows, source, ancestors)
        && within_budget()
}

fn same_pid_ax_window_facts(pid: i32) -> Result<Vec<SamePidAxWindowFacts>, ()> {
    const AX_MESSAGING_TIMEOUT_SECONDS: f32 = 0.2;

    unsafe {
        let app = AXUIElementCreateApplication(pid);
        if app.is_null() {
            return Err(());
        }
        let _ = AXUIElementSetMessagingTimeout(app, AX_MESSAGING_TIMEOUT_SECONDS);
        let snapshot = match try_copy_ax_windows(app) {
            Ok(snapshot) => snapshot,
            Err(_) => {
                CFRelease(app as CFTypeRef);
                return Err(());
            }
        };
        let app_window_id = |attribute| {
            let element = try_copy_element_attr(app, attribute).ok().flatten()?;
            let window_id = ax_get_window_id(element);
            CFRelease(element as CFTypeRef);
            window_id
        };
        let app_focused_id = app_window_id("AXFocusedWindow");
        let app_main_id = app_window_id("AXMainWindow");
        CFRelease(app as CFTypeRef);

        let mut complete = snapshot.complete;
        let facts = snapshot
            .windows
            .into_iter()
            .enumerate()
            .filter_map(|(order, window)| {
                let _ = AXUIElementSetMessagingTimeout(window, AX_MESSAGING_TIMEOUT_SECONDS);
                let facts = ax_get_window_id(window).map(|window_id| SamePidAxWindowFacts {
                    window_id,
                    order,
                    subrole: copy_string_attr(window, "AXSubrole"),
                    identifier: copy_string_attr(window, "AXIdentifier"),
                    modal: copy_bool_attr(window, "AXModal"),
                    focused: copy_bool_attr(window, "AXFocused"),
                    main: copy_bool_attr(window, "AXMain"),
                    app_focused: app_focused_id == Some(window_id),
                    app_main: app_main_id == Some(window_id),
                });
                if facts.is_none() {
                    complete = false;
                }
                CFRelease(window as CFTypeRef);
                facts
            })
            .collect::<Vec<_>>();
        complete.then_some(facts).ok_or(())
    }
}

fn detect_same_pid_transient_in_front_in(
    windows: &[WindowInfo],
    ax_facts: Option<&[SamePidAxWindowFacts]>,
    source: WindowTarget,
    trusted_blender_file_view: bool,
) -> SamePidTransientDetection {
    let Some(source_window) = eligible_same_pid_source(windows, source) else {
        return SamePidTransientDetection::None;
    };
    let Some(ax_facts) = ax_facts else {
        return SamePidTransientDetection::Indeterminate;
    };
    let Some(source_ax) = ax_facts
        .iter()
        .find(|facts| facts.window_id == source.window_id)
    else {
        return SamePidTransientDetection::Indeterminate;
    };
    let (Some(source_focused), Some(source_main)) = (source_ax.focused, source_ax.main) else {
        return SamePidTransientDetection::Indeterminate;
    };

    let mut matches = Vec::new();
    let mut unproven_focused_successor = false;
    for candidate in windows {
        if !is_same_pid_transient_geometry_candidate(candidate, source_window) {
            continue;
        }
        let Some(candidate_ax) = ax_facts
            .iter()
            .find(|facts| facts.window_id == candidate.window_id)
        else {
            return SamePidTransientDetection::Indeterminate;
        };
        let (Some(candidate_focused), Some(candidate_main)) =
            (candidate_ax.focused, candidate_ax.main)
        else {
            return SamePidTransientDetection::Indeterminate;
        };
        let exclusive_focus_handoff = candidate_ax.order < source_ax.order
            && candidate_focused
            && candidate_main
            && !source_focused
            && !source_main;
        if !exclusive_focus_handoff {
            // Calc's background Sort window reports AXFocused=false and
            // AXModal=false despite both application context references
            // pointing to it. Returning the source would pair its AX tree and
            // input target with a capture containing a different window.
            // Refuse without redirecting; an unpinned observation can select
            // the current application context through the normal resolver.
            if candidate_ax.order < source_ax.order
                && candidate_ax.app_focused
                && candidate_ax.app_main
                && !source_ax.app_focused
                && !source_ax.app_main
            {
                unproven_focused_successor = true;
            }
            continue;
        }
        let classification = if candidate_ax.has_dialog_metadata() {
            Some(SamePidTransientClassification::DialogMetadata)
        } else if trusted_blender_file_view && candidate.title == BLENDER_FILE_VIEW_TITLE {
            Some(SamePidTransientClassification::TrustedBlenderFileView)
        } else {
            None
        };
        let Some(classification) = classification else {
            unproven_focused_successor = true;
            continue;
        };
        matches.push(SamePidTransientProof {
            source,
            target: WindowTarget {
                pid: candidate.pid,
                window_id: candidate.window_id,
            },
            classification,
        });
    }

    if unproven_focused_successor || matches.len() > 1 {
        return SamePidTransientDetection::Ambiguous;
    }
    let Some(candidate) = matches.into_iter().next() else {
        return SamePidTransientDetection::None;
    };
    SamePidTransientDetection::Unique(candidate)
}

fn eligible_same_pid_source(windows: &[WindowInfo], source: WindowTarget) -> Option<&WindowInfo> {
    windows.iter().find(|window| {
        window.pid == source.pid
            && window.window_id == source.window_id
            && window.layer == 0
            && window.is_on_screen
            && window.on_current_space == Some(true)
    })
}

fn is_same_pid_transient_geometry_candidate(candidate: &WindowInfo, source: &WindowInfo) -> bool {
    candidate.pid == source.pid
        && candidate.window_id != source.window_id
        && candidate.layer == 0
        && candidate.is_on_screen
        && candidate.on_current_space == Some(true)
        && !candidate.title.trim().is_empty()
        && contained_by(&candidate.bounds, &source.bounds)
        && same_known_space(candidate, source)
}

fn same_known_space(left: &WindowInfo, right: &WindowInfo) -> bool {
    match (left.current_space_id, right.current_space_id) {
        (Some(left), Some(right)) => left == right,
        _ => false,
    }
}

pub(crate) fn detect_visible_transient_helper(source: WindowTarget) -> TransientHelperDetection {
    if crate::apps::bundle_id_for_pid(source.pid).as_deref() != Some(SHORTCUTS_HOST_BUNDLE_ID) {
        return TransientHelperDetection::None;
    }
    let windows = crate::windows::all_windows_including_accessory_layers();
    detect_visible_transient_helper_in(&windows, source, |helper_pid| {
        trusted_shortcuts_pair(source.pid, helper_pid)
    })
}

/// Preserve the old window-bound detector first. Only an unbound app-context
/// request may use app-owned helper evidence when that detector found nothing.
/// Neither layer nor current focus asserts which editor initiated the helper.
pub(crate) fn detect_transient_for_observation(
    source: WindowTarget,
    app_context: bool,
) -> Result<(TransientHelperDetection, Option<AppContextHelperProof>), ()> {
    observation_detection_with(app_context, detect_visible_transient_helper(source),
        || detect_app_context_helper(source))
}

fn observation_detection_with(
    app_context: bool,
    old: TransientHelperDetection,
    recover: impl FnOnce() -> Result<(TransientHelperDetection, Option<AppContextHelperProof>), ()>,
) -> Result<(TransientHelperDetection, Option<AppContextHelperProof>), ()> {
    if app_context && old == TransientHelperDetection::None { recover() }
    else { Ok((old, None)) }
}

fn app_context_candidate(
    windows: &[WindowInfo],
    source: WindowTarget,
    trusted: impl FnMut(i32) -> bool,
) -> TransientHelperDetection {
    let hosts: Vec<_> = windows.iter().filter(|w| w.pid == source.pid
        && w.window_id == source.window_id && w.window_id != 0
        && w.is_on_screen && w.layer == 0).collect();
    if hosts.len() != 1 { return TransientHelperDetection::None; }
    visible_app_owned_helper(windows, source.pid, trusted)
}

// Refusal evidence only until the complete AX proof succeeds. This predicate
// never creates a route and does not require a particular editor to be visible.
fn visible_app_owned_helper(
    windows: &[WindowInfo], host_pid: i32, mut trusted: impl FnMut(i32) -> bool,
) -> TransientHelperDetection {
    let candidates: Vec<_> = windows.iter().filter(|w| w.pid > 0 && w.pid != host_pid
        && w.window_id != 0 && w.is_on_screen && w.layer == MODAL_PANEL_WINDOW_LAYER
        && trusted(w.pid)).collect();
    match candidates.as_slice() {
        [] => TransientHelperDetection::None,
        [target] if windows.iter().filter(|w| w.pid == target.pid && w.is_on_screen).count() == 1 =>
            TransientHelperDetection::Unique(WindowTarget { pid: target.pid, window_id: target.window_id }),
        _ => TransientHelperDetection::Ambiguous,
    }
}

// Local retained objects never leave this synchronous AX read or acquire Send.
struct ContextAxNodes(Vec<AXUIElementRef>);
impl Drop for ContextAxNodes {
    fn drop(&mut self) {
        for node in &self.0 { unsafe { CFRelease(*node as CFTypeRef); } }
    }
}

unsafe fn context_ax_read<T>(
    node: AXUIElementRef,
    deadline: Instant,
    read: impl FnOnce() -> T,
) -> Result<T, ()> {
    let remaining = deadline.checked_duration_since(Instant::now()).ok_or(())?;
    if node.is_null() || remaining.is_zero()
        || AXUIElementSetMessagingTimeout(node, remaining.as_secs_f32().min(0.2)) != 0
    { return Err(()); }
    // The caller first takes ownership of any returned CF references, then
    // checks the shared deadline. Never discard a late raw retained result.
    Ok(read())
}

fn app_context_ax_identity(
    target: WindowTarget, owner: Option<i32>, physical: Option<u32>,
    role: Option<&str>, subrole: Option<&str>,
) -> bool {
    owner == Some(target.pid) && physical == Some(target.window_id) && target.window_id != 0
        && role == Some("AXWindow") && subrole == Some("AXStandardWindow")
}

/// Complete AXWindows membership plus the app's own focused/main references.
/// The helper may report AXModal=false; this is not a modal/parent proof.
unsafe fn context_ax_window(
    target: WindowTarget, helper: bool, deadline: Instant,
) -> Result<ContextAxNodes, ()> {
    let app = AXUIElementCreateApplication(target.pid);
    if app.is_null() { return Err(()); }
    let mut owned = ContextAxNodes(vec![app]);
    let snapshot = context_ax_read(app, deadline, || try_copy_ax_windows(app))?.map_err(|_| ())?;
    let count = snapshot.windows.len();
    owned.0.extend(snapshot.windows);
    if !snapshot.complete || count == 0 || count > 16 || (helper && count != 1) { return Err(()); }
    let mut selected = None;
    for &window in &owned.0[1..] {
        let owner = context_ax_read(window, deadline, || {
            let mut pid = 0;
            (AXUIElementGetPid(window, &mut pid) == 0).then_some(pid)
        })?;
        let physical = context_ax_read(window, deadline, || ax_get_window_id(window))?;
        // Unknown members must not conceal another candidate or a foreign window.
        if owner != Some(target.pid) || physical.is_none() { return Err(()); }
        if physical == Some(target.window_id) {
            if selected.replace(window).is_some() { return Err(()); }
            let role = context_ax_read(window, deadline, || copy_string_attr(window, "AXRole"))?;
            let subrole = context_ax_read(window, deadline, || copy_string_attr(window, "AXSubrole"))?;
            if !app_context_ax_identity(target, owner, physical, role.as_deref(), subrole.as_deref()) {
                return Err(());
            }
        }
    }
    let selected = selected.ok_or(())?;
    for attribute in ["AXFocusedWindow", "AXMainWindow"] {
        let reference = context_ax_read(app, deadline, || try_copy_element_attr(app, attribute))?
            .map_err(|_| ())?.ok_or(())?;
        owned.0.push(reference);
        if CFEqual(reference as CFTypeRef, selected as CFTypeRef) == 0 { return Err(()); }
    }
    if Instant::now() >= deadline { return Err(()); }
    CFRetain(selected as CFTypeRef);
    Ok(ContextAxNodes(vec![selected]))
}

fn context_births(source: WindowTarget, target: WindowTarget) -> Option<AppContextHelperProof> {
    Some(AppContextHelperProof {
        host_birth: crate::ax::enablement::process_start_stamp(source.pid)?,
        helper_birth: crate::ax::enablement::process_start_stamp(target.pid)?,
    })
}

fn accept_context_recheck(
    expected: TransientHelperDetection, births: AppContextHelperProof,
    current: TransientHelperDetection, current_births: Option<AppContextHelperProof>, in_budget: bool,
) -> bool {
    in_budget && current == expected && current_births == Some(births)
}

fn detect_app_context_helper(
    source: WindowTarget,
) -> Result<(TransientHelperDetection, Option<AppContextHelperProof>), ()> {
    if crate::apps::bundle_id_for_pid(source.pid).as_deref() != Some(SHORTCUTS_HOST_BUNDLE_ID) {
        return Ok((TransientHelperDetection::None, None));
    }
    let deadline = Instant::now() + Duration::from_secs(2);
    let before = crate::windows::all_windows_including_accessory_layers_with_snapshot();
    if !before.succeeded || Instant::now() >= deadline { return Err(()); }
    let detection = visible_app_owned_helper(&before.windows, source.pid,
        |pid| trusted_shortcuts_pair(source.pid, pid));
    if Instant::now() >= deadline { return Err(()); }
    let TransientHelperDetection::Unique(target) = detection else { return Ok((detection, None)); };
    if app_context_candidate(&before.windows, source, |pid| trusted_shortcuts_pair(source.pid, pid)) != detection {
        return Err(());
    }
    let births = context_births(source, target).ok_or(())?;
    let same_ax = unsafe {
        let host_before = context_ax_window(source, false, deadline)?;
        let helper_before = context_ax_window(target, true, deadline)?;
        let host_after = context_ax_window(source, false, deadline)?;
        let helper_after = context_ax_window(target, true, deadline)?;
        CFEqual(host_before.0[0] as CFTypeRef, host_after.0[0] as CFTypeRef) != 0
            && CFEqual(helper_before.0[0] as CFTypeRef, helper_after.0[0] as CFTypeRef) != 0
    };
    if !same_ax || Instant::now() >= deadline { return Err(()); }
    let after = crate::windows::all_windows_including_accessory_layers_with_snapshot();
    if !after.succeeded || !accept_context_recheck(detection, births,
        app_context_candidate(&after.windows, source, |pid| trusted_shortcuts_pair(source.pid, pid)),
        context_births(source, target), Instant::now() < deadline)
    { return Err(()); }
    Ok((detection, Some(births)))
}

/// Refuse host fallback even after a stale app-context route was removed.
/// This broader presence check is never used to select an observation target.
pub(crate) fn detect_transient_helper_for_input_guard(source: WindowTarget) -> TransientHelperDetection {
    let old = detect_visible_transient_helper(source);
    if old.helper_is_visible() { old }
    else { detect_any_visible_transient_helper_for_host(source.pid) }
}

/// Detect any visible trusted transient associated with a host process when a
/// keyboard call omitted `window_id`. Such a call cannot safely inherit a
/// previously observed route, but it must still refuse host fallback while a
/// modal helper is visible.
pub(crate) fn detect_any_visible_transient_helper_for_host(
    host_pid: i32,
) -> TransientHelperDetection {
    if crate::apps::bundle_id_for_pid(host_pid).as_deref() != Some(SHORTCUTS_HOST_BUNDLE_ID) {
        return TransientHelperDetection::None;
    }
    let snapshot = crate::windows::all_windows_including_accessory_layers_with_snapshot();
    if !snapshot.succeeded { return TransientHelperDetection::Ambiguous; }
    let old = detect_any_visible_transient_helper_for_host_in(&snapshot.windows, host_pid,
        |pid| trusted_shortcuts_pair(host_pid, pid));
    if old.helper_is_visible() { old }
    else { visible_app_owned_helper(&snapshot.windows, host_pid,
        |pid| trusted_shortcuts_pair(host_pid, pid)) }

}

/// A narrow WindowServer proof for a helper whose AX window cannot be mapped
/// back to its CGWindowID.  Requiring an active auxiliary process with exactly
/// one visible window avoids treating an arbitrary regular app as the target
/// of a global HID event.
pub(crate) fn active_helper_has_unique_visible_window_for_route(
    route: TransientRoute,
    target: WindowTarget,
) -> bool {
    if route.target != target || !route.is_live() {
        return false;
    }
    let windows = crate::windows::all_windows_including_accessory_layers();
    active_helper_has_unique_visible_window_in(
        &windows,
        target,
        crate::apps::is_active_auxiliary_application(target.pid),
    )
}

fn active_helper_has_unique_visible_window_in(
    windows: &[WindowInfo],
    target: WindowTarget,
    is_active_auxiliary: bool,
) -> bool {
    if !is_active_auxiliary {
        return false;
    }
    let visible: Vec<_> = windows
        .iter()
        .filter(|window| window.pid == target.pid && window.is_on_screen)
        .collect();
    visible.len() == 1
        && visible[0].window_id == target.window_id
        && visible[0].layer == MODAL_PANEL_WINDOW_LAYER
}

fn detect_visible_transient_helper_in(
    windows: &[WindowInfo],
    source: WindowTarget,
    mut is_trusted_pair: impl FnMut(i32) -> bool,
) -> TransientHelperDetection {
    let Some(host) = windows
        .iter()
        .find(|window| window.pid == source.pid && window.window_id == source.window_id)
    else {
        return TransientHelperDetection::None;
    };
    if !host.is_on_screen || host.layer != 0 || host.app_name.is_empty() || host.title.is_empty() {
        return TransientHelperDetection::None;
    }

    let mut matches = windows.iter().filter(|candidate| {
        candidate.pid != source.pid
            && candidate.pid > 0
            && candidate.window_id != 0
            && candidate.is_on_screen
            && candidate.layer == MODAL_PANEL_WINDOW_LAYER
            && candidate.app_name == host.app_name
            && candidate.title == host.title
            && contained_by(&candidate.bounds, &host.bounds)
            && is_trusted_pair(candidate.pid)
    });
    let Some(candidate) = matches.next() else {
        return TransientHelperDetection::None;
    };
    if matches.next().is_some() {
        return TransientHelperDetection::Ambiguous;
    }
    TransientHelperDetection::Unique(WindowTarget {
        pid: candidate.pid,
        window_id: candidate.window_id,
    })
}

fn detect_any_visible_transient_helper_for_host_in(
    windows: &[WindowInfo],
    host_pid: i32,
    mut is_trusted_pair: impl FnMut(i32) -> bool,
) -> TransientHelperDetection {
    let sources: Vec<_> = windows
        .iter()
        .filter(|window| {
            window.pid == host_pid
                && window.window_id != 0
                && window.is_on_screen
                && window.layer == 0
        })
        .map(|window| WindowTarget {
            pid: host_pid,
            window_id: window.window_id,
        })
        .collect();
    let mut found = None;
    for source in sources {
        match detect_visible_transient_helper_in(windows, source, &mut is_trusted_pair) {
            TransientHelperDetection::None => {}
            TransientHelperDetection::Ambiguous => return TransientHelperDetection::Ambiguous,
            TransientHelperDetection::Unique(target) => match found {
                None => found = Some(target),
                Some(existing) if existing == target => {}
                Some(_) => return TransientHelperDetection::Ambiguous,
            },
        }
    }
    found.map_or(
        TransientHelperDetection::None,
        TransientHelperDetection::Unique,
    )
}

fn trusted_shortcuts_pair(host_pid: i32, helper_pid: i32) -> bool {
    trusted_shortcuts_identity(
        crate::apps::bundle_id_for_pid(host_pid).as_deref(),
        crate::apps::bundle_id_for_pid(helper_pid).as_deref(),
        crate::apps::is_auxiliary_application(helper_pid),
        crate::apps::executable_path_for_pid(helper_pid).as_deref(),
    )
}

pub(crate) fn is_trusted_transient_helper_process(pid: i32) -> bool {
    trusted_shortcuts_helper_identity(
        crate::apps::bundle_id_for_pid(pid).as_deref(),
        crate::apps::is_auxiliary_application(pid),
        crate::apps::executable_path_for_pid(pid).as_deref(),
    )
}

fn trusted_shortcuts_identity(
    host_bundle_id: Option<&str>,
    helper_bundle_id: Option<&str>,
    helper_is_auxiliary: bool,
    helper_executable_path: Option<&str>,
) -> bool {
    host_bundle_id == Some(SHORTCUTS_HOST_BUNDLE_ID)
        && trusted_shortcuts_helper_identity(
            helper_bundle_id,
            helper_is_auxiliary,
            helper_executable_path,
        )
}

fn trusted_shortcuts_helper_identity(
    helper_bundle_id: Option<&str>,
    helper_is_auxiliary: bool,
    helper_executable_path: Option<&str>,
) -> bool {
    helper_bundle_id == Some(SHORTCUTS_HELPER_BUNDLE_ID)
        && helper_is_auxiliary
        && helper_executable_path.is_some_and(trusted_shortcuts_helper_path)
}

fn trusted_shortcuts_helper_path(path: &str) -> bool {
    path == SHORTCUTS_HELPER_SYSTEM_PATH
        || (path.starts_with(CRYPTEX_SYSTEM_PREFIX)
            && path.ends_with(SHORTCUTS_HELPER_SYSTEM_PATH)
            && !std::path::Path::new(path)
                .components()
                .any(|component| matches!(component, std::path::Component::ParentDir)))
}

fn contained_by(child: &WindowBounds, parent: &WindowBounds) -> bool {
    const TOLERANCE: f64 = 2.0;
    child.width >= 32.0
        && child.height >= 32.0
        && child.width < parent.width
        && child.height < parent.height
        && child.x >= parent.x - TOLERANCE
        && child.y >= parent.y - TOLERANCE
        && child.x + child.width <= parent.x + parent.width + TOLERANCE
        && child.y + child.height <= parent.y + parent.height + TOLERANCE
}

#[cfg(test)]
mod tests {
    use super::*;

    fn window(
        pid: i32,
        window_id: u32,
        app_name: &str,
        title: &str,
        layer: i32,
        bounds: WindowBounds,
    ) -> WindowInfo {
        WindowInfo {
            window_id,
            pid,
            app_name: app_name.into(),
            title: title.into(),
            bounds,
            layer,
            z_index: window_id as usize,
            is_on_screen: true,
            current_space_id: None,
            on_current_space: None,
            space_ids: None,
        }
    }

    fn rect(x: f64, y: f64, width: f64, height: f64) -> WindowBounds {
        WindowBounds {
            x,
            y,
            width,
            height,
        }
    }

    fn session(name: &str) -> TransientSessionKey {
        TransientSessionKey::Session(name.to_owned())
    }

    fn same_pid_ax(
        window_id: u32,
        order: usize,
        focused: bool,
        main: bool,
        modal: bool,
    ) -> SamePidAxWindowFacts {
        SamePidAxWindowFacts {
            window_id,
            order,
            subrole: Some("AXStandardWindow".into()),
            identifier: None,
            modal: Some(modal),
            focused: Some(focused),
            main: Some(main),
            app_focused: false,
            app_main: false,
        }
    }

    fn current_window(
        pid: i32,
        window_id: u32,
        title: &str,
        z_index: usize,
        bounds: WindowBounds,
    ) -> WindowInfo {
        let mut window = window(pid, window_id, "Blender", title, 0, bounds);
        window.z_index = z_index;
        window.current_space_id = Some(1);
        window.on_current_space = Some(true);
        window.space_ids = Some(vec![1]);
        window
    }

    #[test]
    fn nested_leaf_geometry_does_not_make_its_proven_save_parent_a_successor() {
        let source = WindowTarget { pid: 42, window_id: 950 };
        let windows = vec![
            current_window(42, 950, "", 0, rect(634.0, 451.0, 460.0, 183.0)),
            current_window(42, 900, "Save", 1, rect(679.0, 452.0, 370.0, 182.0)),
            current_window(42, 700, "Document", 2, rect(0.0, 33.0, 1728.0, 1020.0)),
        ];
        assert!(has_same_pid_transient_geometry_candidate(&windows, source));
        assert_eq!(detect_same_pid_transient_in_front_in(
            &windows, Some(&[same_pid_ax(700, 0, false, true, false)]), source, false),
            SamePidTransientDetection::Indeterminate,
            "AXWindows can omit both sheets despite positive native attachment proof");
        assert!(geometry_candidates_are_proven_ancestors(&windows, source, &[900, 700]));
        assert!(!geometry_candidates_are_proven_ancestors(&windows, source, &[]));
        assert!(!geometry_candidates_are_proven_ancestors(&windows, source, &[700]));
        assert!(!geometry_candidates_are_proven_ancestors(&windows, source, &[950, 900, 700]));
    }

    #[test]
    fn a_proven_sheet_ancestor_never_hides_an_unrelated_geometry_candidate() {
        let source = WindowTarget { pid: 42, window_id: 950 };
        let mut windows = vec![
            current_window(42, 950, "", 0, rect(0.0, 0.0, 460.0, 183.0)),
            current_window(42, 900, "Save", 1, rect(45.0, 1.0, 370.0, 182.0)),
        ];
        assert!(geometry_candidates_are_proven_ancestors(&windows, source, &[900, 700]));
        windows.push(current_window(42, 901, "Other dialog", 2, rect(50.0, 10.0, 100.0, 80.0)));
        assert!(!geometry_candidates_are_proven_ancestors(&windows, source, &[900, 700]));
        windows.remove(1);
        assert!(!geometry_candidates_are_proven_ancestors(&windows, source, &[900, 700]));
    }

    #[test]
    fn ancestor_geometry_exception_retains_source_visibility_space_and_pid_gates() {
        let source = WindowTarget { pid: 42, window_id: 950 };
        let windows = vec![
            current_window(42, 950, "", 0, rect(0.0, 0.0, 460.0, 183.0)),
            current_window(42, 900, "Save", 1, rect(45.0, 1.0, 370.0, 182.0)),
        ];
        for kind in 0..4 {
            let mut changed = windows.clone();
            match kind {
                0 => changed[0].is_on_screen = false,
                1 => changed[0].on_current_space = None,
                2 => changed[0].pid = 99,
                _ => changed[1].current_space_id = Some(2),
            }
            assert!(!geometry_candidates_are_proven_ancestors(&changed, source, &[900, 700]));
        }
    }

    #[test]
    fn ancestor_exception_rechecks_new_windows_and_changed_physical_identity() {
        let source = WindowTarget { pid: 42, window_id: 950 };
        let before = vec![
            current_window(42, 950, "", 0, rect(0.0, 0.0, 460.0, 183.0)),
            current_window(42, 900, "Save", 1, rect(45.0, 1.0, 370.0, 182.0)),
            current_window(42, 700, "Document", 2, rect(0.0, 0.0, 1728.0, 1020.0)),
        ];
        let snapshot = |windows| crate::windows::WindowEnumeration {
            windows, current_space_id: Some(1), succeeded: true,
        };
        assert!(recheck_ancestor_geometry(&before, source, &[900, 700], || true,
            || snapshot(before.clone())));
        for kind in 0..6 {
            let mut changed = before.clone();
            match kind {
                0 => changed.push(current_window(42, 901, "Other dialog", 0,
                    rect(50.0, 10.0, 100.0, 80.0))),
                1 => changed[0].bounds.x += 1.0,
                2 => changed[1].pid = 99,
                3 => changed[2].current_space_id = Some(2),
                4 => changed[2].is_on_screen = false,
                _ => { changed.remove(1); }
            }
            assert!(!recheck_ancestor_geometry(&before, source, &[900, 700], || true,
                || snapshot(changed)));
        }
    }

    #[test]
    fn ancestor_exception_uses_original_budget_and_refuses_failed_enumeration() {
        let source = WindowTarget { pid: 42, window_id: 950 };
        assert!(!recheck_ancestor_geometry(&[], source, &[900], || false,
            || panic!("expired proof must not start another WindowServer read")));
        let polls = std::cell::Cell::new(0);
        assert!(!recheck_ancestor_geometry(&[], source, &[900],
            || { let n = polls.get(); polls.set(n + 1); n == 0 },
            || crate::windows::WindowEnumeration {
                windows: vec![], current_space_id: Some(1), succeeded: true,
            }));
        assert_eq!(polls.get(), 2, "the same budget is checked after the read");
        assert!(!recheck_ancestor_geometry(&[], source, &[900], || true,
            || crate::windows::WindowEnumeration {
                windows: vec![], current_space_id: Some(1), succeeded: false,
            }));
    }

    #[test]
    fn detects_only_the_trusted_blender_file_view_fallback() {
        let source = WindowTarget {
            pid: 42,
            window_id: 100,
        };
        let windows = vec![
            current_window(
                42,
                200,
                BLENDER_FILE_VIEW_TITLE,
                // Blender's File View can be visually composited above its
                // host even when CGWindow ordering reports the host first.
                5,
                rect(200.0, 180.0, 600.0, 420.0),
            ),
            current_window(
                42,
                100,
                "arbitrary host title",
                10,
                rect(0.0, 0.0, 1000.0, 800.0),
            ),
        ];
        let ax_facts = vec![
            same_pid_ax(200, 0, true, true, false),
            same_pid_ax(100, 1, false, false, false),
        ];

        assert_eq!(
            detect_same_pid_transient_in_front_in(&windows, Some(&ax_facts), source, true),
            SamePidTransientDetection::Unique(SamePidTransientProof {
                source,
                target: WindowTarget {
                    pid: 42,
                    window_id: 200,
                },
                classification: SamePidTransientClassification::TrustedBlenderFileView,
            })
        );
    }

    #[test]
    fn contained_ordinary_same_pid_sibling_is_refused_without_redirect() {
        let source = WindowTarget {
            pid: 42,
            window_id: 100,
        };
        let windows = vec![
            current_window(
                42,
                200,
                "other document",
                20,
                rect(200.0, 180.0, 600.0, 420.0),
            ),
            current_window(42, 100, "host document", 10, rect(0.0, 0.0, 1000.0, 800.0)),
        ];
        let ax_facts = vec![
            same_pid_ax(200, 0, true, true, false),
            same_pid_ax(100, 1, false, false, false),
        ];

        assert_eq!(
            detect_same_pid_transient_in_front_in(&windows, Some(&ax_facts), source, true),
            SamePidTransientDetection::Ambiguous,
            "focus and containment alone must never authorize a sibling redirect"
        );
    }

    fn background_calc_sort_context() -> (WindowTarget, Vec<WindowInfo>, Vec<SamePidAxWindowFacts>) {
        let source = WindowTarget {
            pid: 32147,
            window_id: 103577,
        };
        let windows = vec![
            current_window(32147, 103609, "Sort", 0, rect(562.0, 276.0, 602.0, 511.0)),
            current_window(
                32147,
                103577,
                "H068-r33-sort-source.csv",
                2,
                rect(172.0, 104.0, 1382.0, 856.0),
            ),
        ];
        let mut successor = same_pid_ax(103609, 0, false, true, false);
        successor.app_focused = true;
        successor.app_main = true;
        (
            source,
            windows,
            vec![successor, same_pid_ax(103577, 2, false, false, false)],
        )
    }

    #[test]
    fn background_application_context_handoff_refuses_stale_host_without_redirect() {
        let (source, windows, facts) = background_calc_sort_context();
        assert_eq!(
            detect_same_pid_transient_in_front_in(&windows, Some(&facts), source, false),
            SamePidTransientDetection::Ambiguous,
            "the captured background Sort metadata must not yield a host AX/capture mismatch"
        );
        // Modal metadata alone does not turn application references into the
        // missing per-window focus proof for an automatic redirect.
        let mut modal = facts.clone();
        modal[0].modal = Some(true);
        assert_eq!(
            detect_same_pid_transient_in_front_in(&windows, Some(&modal), source, false),
            SamePidTransientDetection::Ambiguous
        );
    }

    #[test]
    fn background_handoff_requires_both_application_references_and_exclusive_source() {
        let (source, windows, facts) = background_calc_sort_context();
        for change in 0..4 {
            let mut changed = facts.clone();
            match change {
                0 => changed[0].app_focused = false,
                1 => changed[0].app_main = false,
                2 => changed[1].app_focused = true,
                _ => changed[1].app_main = true,
            }
            assert_eq!(
                detect_same_pid_transient_in_front_in(&windows, Some(&changed), source, false),
                SamePidTransientDetection::None
            );
        }
    }

    #[test]
    fn application_context_references_do_not_override_geometry_space_or_window_order() {
        let (source, windows, facts) = background_calc_sort_context();
        for change in 0..4 {
            let mut changed_windows = windows.clone();
            let mut changed_facts = facts.clone();
            match change {
                0 => changed_windows[0].bounds.x = 2000.0,
                1 => changed_windows[0].on_current_space = Some(false),
                2 => changed_windows[0].current_space_id = Some(2),
                _ => changed_facts[0].order = 3,
            }
            assert_eq!(
                detect_same_pid_transient_in_front_in(
                    &changed_windows,
                    Some(&changed_facts),
                    source,
                    false
                ),
                SamePidTransientDetection::None
            );
        }
    }

    #[test]
    fn native_dialog_metadata_allows_a_generic_same_pid_redirect() {
        let source = WindowTarget {
            pid: 42,
            window_id: 100,
        };
        let windows = vec![
            current_window(42, 200, "Confirm", 20, rect(200.0, 180.0, 600.0, 420.0)),
            current_window(42, 100, "host", 10, rect(0.0, 0.0, 1000.0, 800.0)),
        ];
        let ax_facts = vec![
            same_pid_ax(200, 0, true, true, true),
            same_pid_ax(100, 1, false, false, false),
        ];

        assert_eq!(
            detect_same_pid_transient_in_front_in(&windows, Some(&ax_facts), source, false),
            SamePidTransientDetection::Unique(SamePidTransientProof {
                source,
                target: WindowTarget {
                    pid: 42,
                    window_id: 200,
                },
                classification: SamePidTransientClassification::DialogMetadata,
            })
        );
    }

    #[test]
    fn geometry_candidate_with_unavailable_ax_evidence_is_indeterminate() {
        let source = WindowTarget {
            pid: 42,
            window_id: 100,
        };
        let windows = vec![
            current_window(42, 200, "child", 20, rect(200.0, 180.0, 600.0, 420.0)),
            current_window(42, 100, "host", 10, rect(0.0, 0.0, 1000.0, 800.0)),
        ];

        assert_eq!(
            detect_same_pid_transient_in_front_in(&windows, None, source, false),
            SamePidTransientDetection::Indeterminate
        );

        let source_only = vec![same_pid_ax(100, 1, false, false, false)];
        assert_eq!(
            detect_same_pid_transient_in_front_in(&windows, Some(&source_only), source, false),
            SamePidTransientDetection::Indeterminate,
            "an unmapped geometry candidate must not be treated as absent"
        );

        let mut unknown_focus = same_pid_ax(200, 0, true, true, true);
        unknown_focus.focused = None;
        let incomplete = vec![unknown_focus, same_pid_ax(100, 1, false, false, false)];
        assert_eq!(
            detect_same_pid_transient_in_front_in(&windows, Some(&incomplete), source, false),
            SamePidTransientDetection::Indeterminate,
            "unknown required focus metadata must fail closed"
        );
    }

    #[test]
    fn does_not_redirect_to_an_ordinary_same_pid_sibling() {
        let source = WindowTarget {
            pid: 42,
            window_id: 100,
        };
        let windows = vec![
            current_window(
                42,
                200,
                "other document",
                20,
                rect(1100.0, 0.0, 600.0, 700.0),
            ),
            current_window(42, 100, "host document", 10, rect(0.0, 0.0, 1000.0, 800.0)),
        ];
        let ax_facts = vec![
            same_pid_ax(200, 0, true, true, false),
            same_pid_ax(100, 1, false, false, false),
        ];

        assert_eq!(
            detect_same_pid_transient_in_front_in(&windows, Some(&ax_facts), source, false),
            SamePidTransientDetection::None,
            "a focused sibling is not enough without containment"
        );
    }

    #[test]
    fn requires_an_exclusive_focus_handoff_even_for_contained_windows() {
        let source = WindowTarget {
            pid: 42,
            window_id: 100,
        };
        let windows = vec![
            current_window(42, 200, "palette", 20, rect(200.0, 180.0, 600.0, 420.0)),
            current_window(42, 100, "host", 10, rect(0.0, 0.0, 1000.0, 800.0)),
        ];
        let ax_facts = vec![
            same_pid_ax(200, 0, false, false, false),
            same_pid_ax(100, 1, true, true, false),
        ];

        assert_eq!(
            detect_same_pid_transient_in_front_in(&windows, Some(&ax_facts), source, false),
            SamePidTransientDetection::None
        );
    }

    #[test]
    fn requires_the_transient_to_precede_the_source_in_ax_window_order() {
        let source = WindowTarget {
            pid: 42,
            window_id: 100,
        };
        let windows = vec![
            current_window(
                42,
                200,
                "contained sibling",
                20,
                rect(200.0, 180.0, 600.0, 420.0),
            ),
            current_window(42, 100, "host", 10, rect(0.0, 0.0, 1000.0, 800.0)),
        ];
        let ax_facts = vec![
            same_pid_ax(100, 0, false, false, false),
            same_pid_ax(200, 1, true, true, false),
        ];

        assert_eq!(
            detect_same_pid_transient_in_front_in(&windows, Some(&ax_facts), source, false),
            SamePidTransientDetection::None,
            "focus flags alone do not override the app's AX window order"
        );
    }

    #[test]
    fn multiple_proven_successors_fail_closed_as_ambiguous() {
        let source = WindowTarget {
            pid: 42,
            window_id: 100,
        };
        let windows = vec![
            current_window(42, 200, "first", 30, rect(100.0, 100.0, 700.0, 500.0)),
            current_window(42, 300, "second", 20, rect(200.0, 180.0, 600.0, 420.0)),
            current_window(42, 100, "host", 10, rect(0.0, 0.0, 1000.0, 800.0)),
        ];
        let ax_facts = vec![
            same_pid_ax(200, 0, true, true, true),
            same_pid_ax(300, 1, true, true, true),
            same_pid_ax(100, 2, false, false, false),
        ];

        assert_eq!(
            detect_same_pid_transient_in_front_in(&windows, Some(&ax_facts), source, false),
            SamePidTransientDetection::Ambiguous
        );
    }

    #[test]
    fn session_key_uses_only_runtime_session_id_and_has_explicit_anonymous_variant() {
        assert_eq!(
            TransientSessionKey::from_args(&serde_json::json!({})),
            TransientSessionKey::Anonymous
        );
        assert_eq!(
            TransientSessionKey::from_args(&serde_json::json!({
                "session": "public-label",
                "_session_id": "runtime-session"
            })),
            session("runtime-session")
        );
        assert_eq!(
            TransientSessionKey::from_args(&serde_json::json!({
                "session": "public-label"
            })),
            TransientSessionKey::Anonymous,
            "public labels must not select an authorization namespace"
        );
        assert_eq!(
            TransientSessionKey::from_args(&serde_json::json!({
                "_session_id": "foo "
            })),
            session("foo "),
            "the registry namespace must preserve the core lifecycle id byte-for-byte"
        );
    }

    #[test]
    fn routes_matching_auxiliary_panel_without_listing_helper_app() {
        let source = WindowTarget {
            pid: 85052,
            window_id: 100,
        };
        let windows = vec![
            window(
                85052,
                100,
                "Shortcuts",
                "Demo",
                0,
                rect(0.0, 33.0, 1296.0, 951.0),
            ),
            window(
                12649,
                200,
                "Shortcuts",
                "Demo",
                8,
                rect(694.0, 261.0, 340.0, 111.0),
            ),
        ];

        assert_eq!(
            detect_visible_transient_helper_in(&windows, source, |pid| pid == 12649),
            TransientHelperDetection::Unique(WindowTarget {
                pid: 12649,
                window_id: 200,
            })
        );
    }

    #[test]
    fn rejects_regular_or_unrelated_windows_even_when_they_overlap() {
        let source = WindowTarget {
            pid: 10,
            window_id: 100,
        };
        let host = window(
            10,
            100,
            "Editor",
            "Document",
            0,
            rect(0.0, 0.0, 1000.0, 800.0),
        );
        let regular = window(
            20,
            200,
            "Editor",
            "Document",
            8,
            rect(200.0, 200.0, 300.0, 120.0),
        );
        let wrong_title = window(
            30,
            300,
            "Editor",
            "Other",
            8,
            rect(200.0, 200.0, 300.0, 120.0),
        );
        let wrong_owner_name = window(
            40,
            400,
            "Other App",
            "Document",
            8,
            rect(200.0, 200.0, 300.0, 120.0),
        );

        let windows = vec![host, regular, wrong_title, wrong_owner_name];
        assert_eq!(
            detect_visible_transient_helper_in(&windows, source, |pid| pid != 20),
            TransientHelperDetection::None
        );
    }

    #[test]
    fn rejects_helper_outside_host_or_on_normal_window_layer() {
        let source = WindowTarget {
            pid: 10,
            window_id: 100,
        };
        let windows = vec![
            window(
                10,
                100,
                "Editor",
                "Document",
                0,
                rect(0.0, 0.0, 1000.0, 800.0),
            ),
            window(
                20,
                200,
                "Editor",
                "Document",
                8,
                rect(900.0, 700.0, 300.0, 120.0),
            ),
            window(
                30,
                300,
                "Editor",
                "Document",
                0,
                rect(200.0, 200.0, 300.0, 120.0),
            ),
        ];

        assert_eq!(
            detect_visible_transient_helper_in(&windows, source, |_| true),
            TransientHelperDetection::None
        );
    }

    #[test]
    fn rejects_ambiguous_matching_helper_panels() {
        let source = WindowTarget {
            pid: 10,
            window_id: 100,
        };
        let windows = vec![
            window(
                10,
                100,
                "Editor",
                "Document",
                0,
                rect(0.0, 0.0, 1000.0, 800.0),
            ),
            window(
                20,
                200,
                "Editor",
                "Document",
                MODAL_PANEL_WINDOW_LAYER,
                rect(200.0, 200.0, 300.0, 120.0),
            ),
            window(
                30,
                300,
                "Editor",
                "Document",
                MODAL_PANEL_WINDOW_LAYER,
                rect(250.0, 250.0, 300.0, 120.0),
            ),
        ];

        assert_eq!(
            detect_visible_transient_helper_in(&windows, source, |_| true),
            TransientHelperDetection::Ambiguous,
            "ambiguous helper candidates must fail closed"
        );
    }

    #[test]
    fn only_trusts_the_exact_shortcuts_system_helper_identity_without_requiring_activity() {
        assert!(trusted_shortcuts_identity(
            Some(SHORTCUTS_HOST_BUNDLE_ID),
            Some(SHORTCUTS_HELPER_BUNDLE_ID),
            true,
            Some(SHORTCUTS_HELPER_SYSTEM_PATH),
        ));
        assert!(trusted_shortcuts_identity(
            Some(SHORTCUTS_HOST_BUNDLE_ID),
            Some(SHORTCUTS_HELPER_BUNDLE_ID),
            true,
            Some("/System/Volumes/Preboot/Cryptexes/App/System/Library/PrivateFrameworks/WorkflowKit.framework/XPCServices/ShortcutsViewService.xpc/Contents/MacOS/ShortcutsViewService"),
        ));

        // Activity is intentionally not part of the identity proof. A visible
        // non-Regular helper can be temporarily inactive while another app is
        // frontmost; detection must still surface it so keyboard input fails
        // closed. The boolean below proves only the auxiliary activation
        // policy, while the routed HID bypass separately requires isActive.
        for (host, helper, auxiliary, path) in [
            (
                Some("com.example.shortcuts"),
                Some(SHORTCUTS_HELPER_BUNDLE_ID),
                true,
                Some(SHORTCUTS_HELPER_SYSTEM_PATH),
            ),
            (
                Some(SHORTCUTS_HOST_BUNDLE_ID),
                Some("com.example.ShortcutsViewService"),
                true,
                Some(SHORTCUTS_HELPER_SYSTEM_PATH),
            ),
            (
                Some(SHORTCUTS_HOST_BUNDLE_ID),
                Some(SHORTCUTS_HELPER_BUNDLE_ID),
                false,
                Some(SHORTCUTS_HELPER_SYSTEM_PATH),
            ),
            (
                Some(SHORTCUTS_HOST_BUNDLE_ID),
                Some(SHORTCUTS_HELPER_BUNDLE_ID),
                true,
                Some("/tmp/System/Library/PrivateFrameworks/WorkflowKit.framework/XPCServices/ShortcutsViewService.xpc/Contents/MacOS/ShortcutsViewService"),
            ),
        ] {
            assert!(!trusted_shortcuts_identity(host, helper, auxiliary, path));
        }
    }

    #[test]
    fn host_pid_detection_finds_one_helper_and_refuses_multiple_helpers() {
        let host_a = window(
            10,
            100,
            "Shortcuts",
            "Demo A",
            0,
            rect(0.0, 0.0, 1000.0, 800.0),
        );
        let host_b = window(
            10,
            101,
            "Shortcuts",
            "Demo B",
            0,
            rect(1000.0, 0.0, 1000.0, 800.0),
        );
        let helper_a = window(
            20,
            200,
            "Shortcuts",
            "Demo A",
            MODAL_PANEL_WINDOW_LAYER,
            rect(200.0, 200.0, 300.0, 120.0),
        );
        assert_eq!(
            detect_any_visible_transient_helper_for_host_in(
                &[host_a.clone(), host_b.clone(), helper_a.clone()],
                10,
                |pid| pid == 20,
            ),
            TransientHelperDetection::Unique(WindowTarget {
                pid: 20,
                window_id: 200,
            })
        );

        let helper_b = window(
            30,
            300,
            "Shortcuts",
            "Demo B",
            MODAL_PANEL_WINDOW_LAYER,
            rect(1200.0, 200.0, 300.0, 120.0),
        );
        assert_eq!(
            detect_any_visible_transient_helper_for_host_in(
                &[host_a, host_b, helper_a, helper_b],
                10,
                |pid| matches!(pid, 20 | 30),
            ),
            TransientHelperDetection::Ambiguous
        );
    }

    #[test]
    fn stale_route_is_refused_and_removed_instead_of_falling_back() {
        let registry = TransientUiRegistry::new();
        let source = WindowTarget {
            pid: 10,
            window_id: 100,
        };
        let target = WindowTarget {
            pid: 20,
            window_id: 200,
        };
        let session = session("stale-route");
        registry.record(&session, source, Some(target));

        assert_eq!(
            registry.resolve_with(&session, source, |_| None),
            RouteResolution::Stale(TransientRoute { source, target, app_context: None })
        );
        assert_eq!(
            registry.resolve_with(&session, source, |_| Some(target)),
            RouteResolution::None,
            "a stale route must be removed so no later call can revive it implicitly"
        );
    }

    #[test]
    fn live_route_requires_the_same_helper_window_observed_before() {
        let registry = TransientUiRegistry::new();
        let source = WindowTarget {
            pid: 10,
            window_id: 100,
        };
        let target = WindowTarget {
            pid: 20,
            window_id: 200,
        };
        let session = session("live-route");
        registry.record(&session, source, Some(target));

        assert_eq!(
            registry.resolve_with(&session, source, |_| Some(target)),
            RouteResolution::Live(TransientRoute { source, target, app_context: None })
        );
    }

    #[test]
    fn routes_are_isolated_by_session_and_anonymous_is_a_distinct_namespace() {
        let registry = TransientUiRegistry::new();
        let source = WindowTarget {
            pid: 10,
            window_id: 100,
        };
        let target = WindowTarget {
            pid: 20,
            window_id: 200,
        };
        let session_a = session("session-a");
        let session_b = session("session-b");
        registry.record(&session_a, source, Some(target));

        assert_eq!(
            registry.resolve_with(&session_a, source, |_| Some(target)),
            RouteResolution::Live(TransientRoute { source, target, app_context: None })
        );
        assert_eq!(
            registry.resolve_with(&session_b, source, |_| Some(target)),
            RouteResolution::None
        );
        assert_eq!(
            registry.resolve_with(&TransientSessionKey::Anonymous, source, |_| Some(target)),
            RouteResolution::None
        );
    }

    #[test]
    fn trailing_space_session_is_distinct_and_cleanup_removes_only_exact_id() {
        use std::sync::Arc;

        let registry = Arc::new(TransientUiRegistry::new());
        let source = WindowTarget {
            pid: 10,
            window_id: 100,
        };
        let target_a = WindowTarget {
            pid: 20,
            window_id: 200,
        };
        let target_b = WindowTarget {
            pid: 30,
            window_id: 300,
        };
        let plain = session("foo");
        let spaced = session("foo ");
        registry.record(&plain, source, Some(target_a));
        registry.record(&spaced, source, Some(target_b));

        let cleanup_registry = registry.clone();
        let _hook = cua_driver_core::session::register_scoped_session_end_hook(move |ended| {
            cleanup_registry.clear_session(ended);
        });
        cua_driver_core::session::fire_session_end("foo");

        assert_eq!(registry.recorded_target(&plain, source), None);
        assert_eq!(
            registry.recorded_target(&spaced, source),
            Some(target_b),
            "session_end cleanup must preserve a byte-distinct session id"
        );
    }

    #[test]
    fn session_end_clears_routes_and_prevents_resurrection() {
        use std::sync::Arc;

        let registry = Arc::new(TransientUiRegistry::new());
        let session_id = "transient-ui-ended-session-V7R4";
        let session = session(session_id);
        let source = WindowTarget {
            pid: 10,
            window_id: 100,
        };
        let target = WindowTarget {
            pid: 20,
            window_id: 200,
        };
        registry.record(&session, source, Some(target));

        let cleanup_registry = registry.clone();
        let _hook = cua_driver_core::session::register_scoped_session_end_hook(move |ended| {
            cleanup_registry.clear_session(ended);
        });
        cua_driver_core::session::fire_session_end(session_id);

        assert_eq!(
            registry.resolve_with(&session, source, |_| Some(target)),
            RouteResolution::None
        );
        registry.record(&session, source, Some(target));
        assert_eq!(
            registry.resolve_with(&session, source, |_| Some(target)),
            RouteResolution::None,
            "an in-flight observation must not revive an ended session"
        );
    }

    #[test]
    fn stale_revalidation_does_not_remove_a_concurrent_newer_route() {
        let registry = TransientUiRegistry::new();
        let session = session("concurrent-update");
        let source = WindowTarget {
            pid: 10,
            window_id: 100,
        };
        let old_target = WindowTarget {
            pid: 20,
            window_id: 200,
        };
        let new_target = WindowTarget {
            pid: 30,
            window_id: 300,
        };
        registry.record(&session, source, Some(old_target));

        assert_eq!(
            registry.resolve_with(&session, source, |_| {
                registry.record(&session, source, Some(new_target));
                None
            }),
            RouteResolution::Stale(TransientRoute {
                source,
                target: old_target,
                app_context: None,
            })
        );
        assert_eq!(
            registry.resolve_with(&session, source, |_| Some(new_target)),
            RouteResolution::Live(TransientRoute {
                source,
                target: new_target,
                app_context: None,
            }),
            "stale cleanup must compare-and-remove only the value it read"
        );
    }

    #[test]
    fn poisoned_registry_is_cleared_and_recovers_without_panicking() {
        use std::sync::Arc;

        let registry = Arc::new(TransientUiRegistry::new());
        let source = WindowTarget {
            pid: 10,
            window_id: 100,
        };
        let target = WindowTarget {
            pid: 20,
            window_id: 200,
        };
        let session = session("poison-recovery");
        registry.record(&session, source, Some(target));

        let poisoner = registry.clone();
        assert!(std::thread::spawn(move || {
            let _routes = poisoner.inner.lock().unwrap();
            panic!("poison registry for recovery test");
        })
        .join()
        .is_err());

        assert_eq!(
            registry.resolve_with(&session, source, |_| Some(target)),
            RouteResolution::None,
            "poison recovery must clear previously authorized aliases"
        );

        registry.record(&session, source, Some(target));
        assert_eq!(
            registry.resolve_with(&session, source, |_| Some(target)),
            RouteResolution::Live(TransientRoute { source, target, app_context: None }),
            "the registry should accept fresh observations after recovery"
        );
    }

    #[test]
    fn foreground_proof_requires_active_auxiliary_and_one_exact_modal_window() {
        let target = WindowTarget {
            pid: 20,
            window_id: 200,
        };
        let panel = window(
            20,
            200,
            "Editor",
            "Document",
            MODAL_PANEL_WINDOW_LAYER,
            rect(200.0, 200.0, 300.0, 120.0),
        );

        assert!(active_helper_has_unique_visible_window_in(
            std::slice::from_ref(&panel),
            target,
            true
        ));
        assert!(!active_helper_has_unique_visible_window_in(
            std::slice::from_ref(&panel),
            target,
            false
        ));

        let mut sibling = panel.clone();
        sibling.window_id = 201;
        assert!(!active_helper_has_unique_visible_window_in(
            &[panel, sibling],
            target,
            true
        ));
    }
    fn app_context_fixture() -> TransientRoute {
        TransientRoute {
            source: WindowTarget { pid: 10, window_id: 100 },
            target: WindowTarget { pid: 20, window_id: 200 },
            app_context: Some(AppContextHelperProof { host_birth: (1, 2), helper_birth: (3, 4) }),
        }
    }

    #[test]
    fn app_context_recovery_never_runs_for_exact_or_old_positive_or_ambiguous() {
        let route = app_context_fixture();
        for (app, old) in [(false, TransientHelperDetection::None),
            (false, TransientHelperDetection::Unique(route.target)),
            (true, TransientHelperDetection::Unique(route.target)),
            (true, TransientHelperDetection::Ambiguous)] {
            assert_eq!(observation_detection_with(app, old, || panic!("must not recover")), Ok((old, None)));
        }
        assert_eq!(observation_detection_with(true, TransientHelperDetection::None,
            || Ok((TransientHelperDetection::Unique(route.target), route.app_context))),
            Ok((TransientHelperDetection::Unique(route.target), route.app_context)));
        assert!(observation_detection_with(true, TransientHelperDetection::None, || Err(())).is_err());
    }

    #[test]
    fn app_owned_helper_does_not_require_editor_title_or_containment() {
        let r = app_context_fixture();
        let host = window(10, 100, "Shortcuts", "Editor A", 0, rect(0.0, 0.0, 100.0, 100.0));
        let helper = window(20, 200, "Service", "Unrelated title", 8, rect(500.0, 500.0, 200.0, 200.0));
        let windows = [host, helper];
        assert_eq!(detect_visible_transient_helper_in(&windows, r.source, |_| true), TransientHelperDetection::None);
        assert_eq!(app_context_candidate(&windows, r.source, |pid| pid == 20), TransientHelperDetection::Unique(r.target));
        assert_eq!(visible_app_owned_helper(&windows[1..], r.source.pid, |_| true), TransientHelperDetection::Unique(r.target),
            "windowless refusal must not depend on an editor being visible");
    }

    #[test]
    fn app_owned_candidate_rejects_multiple_hidden_foreign_or_untrusted_surfaces() {
        let r = app_context_fixture();
        let host = window(10, 100, "Host", "Editor", 0, rect(0.0, 0.0, 100.0, 100.0));
        let helper = window(20, 200, "Service", "Panel", 8, rect(0.0, 0.0, 100.0, 100.0));
        assert_eq!(app_context_candidate(&[host.clone(), helper.clone()], r.source, |_| false), TransientHelperDetection::None);
        for pid in [20, 30] {
            let mut other = helper.clone(); other.pid = pid; other.window_id = 201;
            assert_eq!(app_context_candidate(&[host.clone(), helper.clone(), other], r.source, |_| true), TransientHelperDetection::Ambiguous);
        }
        let mut hidden = helper.clone(); hidden.is_on_screen = false;
        assert_eq!(app_context_candidate(&[host.clone(), hidden], r.source, |_| true), TransientHelperDetection::None);
        let mut bad_host = host.clone(); bad_host.pid = 11;
        assert_eq!(app_context_candidate(&[bad_host, helper.clone()], r.source, |_| true), TransientHelperDetection::None);
        for (bundle, path) in [("foreign.service", SHORTCUTS_HELPER_SYSTEM_PATH),
            (SHORTCUTS_HELPER_BUNDLE_ID, "/tmp/ShortcutsViewService")] {
            assert_eq!(app_context_candidate(&[host.clone(), helper.clone()], r.source, |_| trusted_shortcuts_identity(
                Some(SHORTCUTS_HOST_BUNDLE_ID), Some(bundle), true, Some(path))), TransientHelperDetection::None);
        }
    }

    #[test]
    fn app_context_ax_identity_requires_exact_owner_physical_role_and_subrole() {
        let r = app_context_fixture();
        assert!(app_context_ax_identity(r.target, Some(20), Some(200), Some("AXWindow"), Some("AXStandardWindow")));
        for (owner, id, role, subrole) in [
            (None, Some(200), Some("AXWindow"), Some("AXStandardWindow")),
            (Some(99), Some(200), Some("AXWindow"), Some("AXStandardWindow")),
            (Some(20), None, Some("AXWindow"), Some("AXStandardWindow")),
            (Some(20), Some(0), Some("AXWindow"), Some("AXStandardWindow")),
            (Some(20), Some(201), Some("AXWindow"), Some("AXStandardWindow")),
            (Some(20), Some(200), None, Some("AXStandardWindow")),
            (Some(20), Some(200), Some("AXUnknown"), Some("AXStandardWindow")),
            (Some(20), Some(200), Some("AXWindow"), None),
        ] { assert!(!app_context_ax_identity(r.target, owner, id, role, subrole)); }
    }

    #[test]
    fn app_context_recheck_rejects_disappearance_new_identity_and_expiry() {
        let r = app_context_fixture(); let birth = r.app_context.unwrap();
        let before = TransientHelperDetection::Unique(r.target);
        assert!(accept_context_recheck(before, birth, before, Some(birth), true));
        for after in [TransientHelperDetection::None, TransientHelperDetection::Ambiguous,
            TransientHelperDetection::Unique(WindowTarget { pid: 20, window_id: 201 })] {
            assert!(!accept_context_recheck(before, birth, after, Some(birth), true));
        }
        for changed in [None,
            Some(AppContextHelperProof { host_birth: (1, 3), ..birth }),
            Some(AppContextHelperProof { helper_birth: (3, 5), ..birth })] {
            assert!(!accept_context_recheck(before, birth, before, changed, true));
        }
        assert!(!accept_context_recheck(before, birth, before, Some(birth), false));
    }

    #[test]
    fn app_context_route_revalidation_never_falls_back_to_title_proof() {
        let r = app_context_fixture();
        let live = (TransientHelperDetection::Unique(r.target), r.app_context);
        assert!(r.revalidate_with(|_| panic!("wrong scope"), |_| Ok(live)));
        for result in [Err(()), Ok((TransientHelperDetection::None, None)),
            Ok((TransientHelperDetection::Unique(r.target), None))] {
            assert!(!r.revalidate_with(|_| panic!("must not use title fallback"), |_| result));
        }
        let old = TransientRoute { app_context: None, ..r };
        assert!(old.revalidate_with(|_| Some(r.target), |_| panic!("old route must stay old")));
    }

    #[test]
    fn same_numbers_with_new_context_proof_invalidate_older_registry_lookup() {
        let registry = TransientUiRegistry::new(); let s = session("context-race");
        let old = app_context_fixture();
        let new = TransientRoute { app_context: Some(AppContextHelperProof {
            helper_birth: (4, 5), ..old.app_context.unwrap()
        }), ..old };
        registry.record_route(&s, old.source, Some(old));
        assert_eq!(registry.resolve_route_with(&s, old.source, |_| {
            registry.record_route(&s, old.source, Some(new)); true
        }), RouteResolution::Stale(old));
        assert_eq!(registry.resolve_route_with(&s, new.source, |r| r == new), RouteResolution::Live(new));
        assert_eq!(registry.resolve_route_with(&s, new.source, |_| false), RouteResolution::Stale(new));
        assert_eq!(registry.resolve_route_with(&s, new.source, |_| panic!("removed")), RouteResolution::None);
    }

}
