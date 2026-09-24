//! Discovery of visible macOS permission dialogs outside ordinary app windows.
//!
//! Permission helpers are accessory applications, so the regular-app
//! inventory and desktop-independent capture omit their dialogs. Expose their
//! verified, visible permission windows as separate app targets. This is
//! discovery only: it does not establish which app requested a dialog, grant
//! permission, activate a window, or transfer another app's action authority.

use std::{collections::HashSet, str::FromStr};

use core_foundation::base::{CFRelease, CFTypeRef};
use serde_json::{json, Value};

use crate::ax::bindings::{
    ax_get_window_id, copy_string_attr, try_copy_ax_windows, AXUIElementCreateApplication,
    AXUIElementSetMessagingTimeout,
};
use crate::windows::WindowInfo;

const BUNDLE_ID: &str = "com.apple.UserNotificationCenter";
const APP_NAME: &str = "UserNotificationCenter";
const CODE_PATH: &str = "/System/Library/CoreServices/UserNotificationCenter.app";
const EXECUTABLE: &str =
    "/System/Library/CoreServices/UserNotificationCenter.app/Contents/MacOS/UserNotificationCenter";
const ACCESSIBILITY_BUNDLE_ID: &str = "com.apple.accessibility.universalAccessAuthWarn";
const ACCESSIBILITY_APP_NAME: &str = "universalAccessAuthWarn";
const ACCESSIBILITY_CODE_PATH: &str = "/System/Library/PrivateFrameworks/UniversalAccess.framework/Versions/A/Resources/universalAccessAuthWarn.app";
const ACCESSIBILITY_EXECUTABLE: &str = "/System/Library/PrivateFrameworks/UniversalAccess.framework/Versions/A/Resources/universalAccessAuthWarn.app/Contents/MacOS/universalAccessAuthWarn";
const MAX_WINDOWS: usize = 4;

struct DialogIdentity {
    bundle_id: &'static str,
    app_name: &'static str,
    code_path: &'static str,
    executable: &'static str,
}

const IDENTITIES: [DialogIdentity; 2] = [
    DialogIdentity {
        bundle_id: BUNDLE_ID,
        app_name: APP_NAME,
        code_path: CODE_PATH,
        executable: EXECUTABLE,
    },
    DialogIdentity {
        bundle_id: ACCESSIBILITY_BUNDLE_ID,
        app_name: ACCESSIBILITY_APP_NAME,
        code_path: ACCESSIBILITY_CODE_PATH,
        executable: ACCESSIBILITY_EXECUTABLE,
    },
];

fn identity_for_bundle(bundle: Option<&str>) -> Option<&'static DialogIdentity> {
    IDENTITIES
        .iter()
        .find(|identity| Some(identity.bundle_id) == bundle)
}

pub(crate) fn is_system_dialog_bundle(bundle: &str) -> bool {
    identity_for_bundle(Some(bundle)).is_some()
}

fn trusted_identity(bundle: Option<&str>, path: Option<&str>, signed: bool) -> bool {
    identity_for_bundle(bundle).is_some_and(|identity| path == Some(identity.code_path) && signed)
}

fn trusted_process(pid: i32) -> bool {
    use core_foundation::url::kCFURLPOSIXPathStyle;
    use security_framework::os::macos::code_signing::{
        Flags, GuestAttributes, SecCode, SecRequirement,
    };

    let bundle = super::bundle_id_for_pid(pid);
    let Some(identity) = identity_for_bundle(bundle.as_deref()) else {
        return false;
    };
    if pid <= 0 {
        return false;
    }
    let verified_path = (|| {
        let mut attributes = GuestAttributes::new();
        attributes.set_pid(pid as libc::pid_t);
        let code = SecCode::copy_guest_with_attribues(None, &attributes, Flags::NONE).ok()?;
        let requirement = SecRequirement::from_str(&format!(
            "anchor apple and identifier \"{}\"",
            identity.bundle_id
        ))
        .ok()?;
        // Dynamic SecCodeCheckValidity takes default flags. Static-code flags
        // return errSecCSInvalidFlags (-67070), even for this Apple-signed app.
        // The explicit anchor/identifier requirement still validates identity.
        code.check_validity(Flags::NONE, &requirement).ok()?;
        Some(
            code.path(Flags::NONE)
                .ok()?
                .get_file_system_path(kCFURLPOSIXPathStyle)
                .to_string(),
        )
    })();
    super::executable_path_for_pid(pid).as_deref() == Some(identity.executable)
        && trusted_identity(
            super::bundle_id_for_pid(pid).as_deref(),
            verified_path.as_deref(),
            verified_path.is_some(),
        )
}

fn visible_candidate(window: &WindowInfo) -> bool {
    window.pid > 0
        && window.window_id > 0
        && IDENTITIES
            .iter()
            .any(|identity| identity.app_name == window.app_name)
        && window.is_on_screen
        && window.on_current_space != Some(false)
        && window.layer >= 0
        && [
            window.bounds.x,
            window.bounds.y,
            window.bounds.width,
            window.bounds.height,
        ]
        .iter()
        .all(|value| value.is_finite())
        && window.bounds.width > 0.0
        && window.bounds.height > 0.0
}

fn dialog_role_matches(bundle: Option<&str>, role: Option<&str>, subrole: Option<&str>) -> bool {
    role == Some("AXWindow")
        && match bundle {
            Some(BUNDLE_ID) => subrole == Some("AXSystemDialog"),
            // This dedicated Apple helper exposes the Accessibility Access alert as
            // AXStandardWindow with AXModal=0. This exception belongs only to its
            // verified code identity; it is not a generic standard-window rule.
            Some(ACCESSIBILITY_BUNDLE_ID) => subrole == Some("AXStandardWindow"),
            _ => false,
        }
}

fn dialog_window_ids(pid: i32) -> HashSet<u32> {
    let bundle = super::bundle_id_for_pid(pid);
    if identity_for_bundle(bundle.as_deref()).is_none() {
        return HashSet::new();
    }
    unsafe {
        let app = AXUIElementCreateApplication(pid);
        if app.is_null() {
            return HashSet::new();
        }
        if AXUIElementSetMessagingTimeout(app, 0.2) != 0 {
            CFRelease(app as CFTypeRef);
            return HashSet::new();
        }
        let snapshot = try_copy_ax_windows(app);
        CFRelease(app as CFTypeRef);
        let Ok(snapshot) = snapshot else {
            return HashSet::new();
        };
        let bounded = snapshot.complete && snapshot.windows.len() <= MAX_WINDOWS;
        let mut ids = HashSet::new();
        for window in snapshot.windows {
            if bounded && AXUIElementSetMessagingTimeout(window, 0.2) == 0 {
                let role = copy_string_attr(window, "AXRole");
                let subrole = copy_string_attr(window, "AXSubrole");
                if dialog_role_matches(bundle.as_deref(), role.as_deref(), subrole.as_deref()) {
                    if let Some(id) = ax_get_window_id(window) {
                        ids.insert(id);
                    }
                }
            }
            CFRelease(window as CFTypeRef);
        }
        ids
    }
}

/// A missing result is not a claim that the desktop contains no other dialogs.
/// AX and signature checks are bounded and only run for a visible candidate.
pub(crate) fn visible_windows() -> Vec<WindowInfo> {
    let snapshot = crate::windows::visible_windows_including_accessory_layers_with_snapshot();
    if !snapshot.succeeded {
        return Vec::new();
    }
    let candidates: Vec<_> = snapshot
        .windows
        .into_iter()
        .filter(visible_candidate)
        .collect();
    if candidates.len() > MAX_WINDOWS {
        return Vec::new();
    }
    let mut trusted = std::collections::HashMap::new();
    let mut ax_ids = std::collections::HashMap::new();
    candidates
        .into_iter()
        .filter(|window| {
            *trusted
                .entry(window.pid)
                .or_insert_with(|| trusted_process(window.pid))
                && identity_for_bundle(super::bundle_id_for_pid(window.pid).as_deref())
                    .is_some_and(|identity| identity.app_name == window.app_name)
                && ax_ids
                    .entry(window.pid)
                    .or_insert_with(|| dialog_window_ids(window.pid))
                    .contains(&window.window_id)
        })
        .collect()
}

pub(crate) fn running_apps() -> Vec<super::AppInfo> {
    use objc2_app_kit::NSRunningApplication;
    let mut seen = HashSet::new();
    visible_windows()
        .into_iter()
        .filter(|window| seen.insert(window.pid))
        .filter_map(|window| unsafe {
            let app = NSRunningApplication::runningApplicationWithProcessIdentifier(window.pid)?;
            if app.isTerminated() {
                return None;
            }
            let bundle = app.bundleIdentifier()?.to_string();
            let identity = identity_for_bundle(Some(&bundle))?;
            Some(super::AppInfo {
                name: identity.app_name.to_owned(),
                pid: window.pid,
                bundle_id: Some(identity.bundle_id.to_owned()),
                running: true,
                active: app.isActive(),
                launch_path: None,
                kind: Some("system_dialog".to_owned()),
                last_used: None,
            })
        })
        .collect()
}

pub(crate) fn observation_advisories(observed_pid: i32) -> Vec<Value> {
    advisories_from_windows(observed_pid, &visible_windows())
}

fn advisories_from_windows(observed_pid: i32, windows: &[WindowInfo]) -> Vec<Value> {
    IDENTITIES
        .iter()
        .filter_map(|identity| {
            let count = windows
                .iter()
                .filter(|window| window.pid != observed_pid && window.app_name == identity.app_name)
                .count();
            (count > 0).then(|| {
                json!({
                    "app_name": identity.app_name,
                    "bundle_id": identity.bundle_id,
                    "kind": "system_dialog",
                    "window_count": count,
                    "visibility": "on_screen",
                    "identity_verified": true,
                    "relationship": "not_established",
                    "advisory": true,
                })
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> WindowInfo {
        WindowInfo {
            window_id: 96843,
            pid: 968,
            app_name: APP_NAME.to_owned(),
            title: String::new(),
            bounds: crate::windows::WindowBounds {
                x: 734.0,
                y: 208.0,
                width: 260.0,
                height: 208.0,
            },
            layer: 8,
            z_index: 1,
            is_on_screen: true,
            current_space_id: None,
            on_current_space: None,
            space_ids: None,
        }
    }

    #[test]
    fn documents_consent_fixture_is_discoverable_without_layer_zero_or_ax_modal() {
        assert!(visible_candidate(&fixture()));
        // The actual Documents dialog reports AXModal=0; its system-dialog
        // subrole and exact window identity are the relevant facts.
        assert!(dialog_role_matches(
            Some(BUNDLE_ID),
            Some("AXWindow"),
            Some("AXSystemDialog")
        ));
    }

    #[test]
    fn names_and_bundle_ids_do_not_replace_code_identity() {
        assert!(trusted_identity(Some(BUNDLE_ID), Some(CODE_PATH), true));
        assert!(!trusted_identity(Some(BUNDLE_ID), Some(CODE_PATH), false));
        assert!(!trusted_identity(
            Some(BUNDLE_ID),
            Some("/tmp/UserNotificationCenter"),
            true
        ));
        assert!(!trusted_identity(
            Some("com.example.fake"),
            Some(CODE_PATH),
            true
        ));
        assert!(!trusted_identity(None, Some(CODE_PATH), true));
    }

    #[test]
    fn accessibility_alert_requires_its_dedicated_apple_identity_and_window_role() {
        assert!(trusted_identity(
            Some(ACCESSIBILITY_BUNDLE_ID),
            Some(ACCESSIBILITY_CODE_PATH),
            true
        ));
        assert!(!trusted_identity(
            Some(ACCESSIBILITY_BUNDLE_ID),
            Some(CODE_PATH),
            true
        ));
        assert!(!trusted_identity(
            Some(BUNDLE_ID),
            Some(ACCESSIBILITY_CODE_PATH),
            true
        ));
        assert!(!trusted_identity(
            Some(ACCESSIBILITY_BUNDLE_ID),
            Some(ACCESSIBILITY_CODE_PATH),
            false
        ));
        assert!(!trusted_identity(
            Some(ACCESSIBILITY_BUNDLE_ID),
            Some("/tmp/universalAccessAuthWarn.app"),
            true
        ));
        let mut window = fixture();
        window.app_name = ACCESSIBILITY_APP_NAME.to_owned();
        window.layer = 0;
        assert!(visible_candidate(&window));
        assert!(dialog_role_matches(
            Some(ACCESSIBILITY_BUNDLE_ID),
            Some("AXWindow"),
            Some("AXStandardWindow")
        ));
        assert!(!dialog_role_matches(
            Some(BUNDLE_ID),
            Some("AXWindow"),
            Some("AXStandardWindow")
        ));
        assert!(!dialog_role_matches(
            Some("com.example.fake"),
            Some("AXWindow"),
            Some("AXStandardWindow")
        ));
        assert!(!dialog_role_matches(
            Some(ACCESSIBILITY_BUNDLE_ID),
            Some("AXMenu"),
            Some("AXStandardWindow")
        ));
        assert!(is_system_dialog_bundle(ACCESSIBILITY_BUNDLE_ID));
        assert!(is_system_dialog_bundle(BUNDLE_ID));
        assert!(!is_system_dialog_bundle("com.apple.SystemUIServer"));
    }

    #[test]
    fn separate_permission_helpers_keep_their_own_advisory_identity() {
        let notification = fixture();
        let mut accessibility = fixture();
        accessibility.pid = 32276;
        accessibility.window_id = 86953;
        accessibility.app_name = ACCESSIBILITY_APP_NAME.to_owned();
        let windows = [notification, accessibility];
        let hints = advisories_from_windows(0, &windows);
        assert_eq!(hints.len(), 2);
        assert_eq!(hints[0]["bundle_id"], BUNDLE_ID);
        assert_eq!(hints[1]["bundle_id"], ACCESSIBILITY_BUNDLE_ID);
        assert!(hints
            .iter()
            .all(|hint| hint["window_count"] == 1 && hint["relationship"] == "not_established"));
        let other = advisories_from_windows(968, &windows);
        assert_eq!(other.len(), 1);
        assert_eq!(other[0]["bundle_id"], ACCESSIBILITY_BUNDLE_ID);
        assert!(advisories_from_windows(32276, &windows[1..]).is_empty());
    }

    #[test]
    fn other_accessory_surfaces_and_hidden_windows_are_not_exposed() {
        let mut window = fixture();
        window.app_name = "Control Centre".to_owned();
        assert!(!visible_candidate(&window));
        window = fixture();
        window.is_on_screen = false;
        assert!(!visible_candidate(&window));
        window = fixture();
        window.on_current_space = Some(false);
        assert!(!visible_candidate(&window));
        window = fixture();
        window.layer = -1;
        assert!(!visible_candidate(&window));
    }

    #[test]
    fn malformed_windows_and_ordinary_ax_windows_are_rejected() {
        let mut window = fixture();
        window.bounds.width = f64::NAN;
        assert!(!visible_candidate(&window));
        window = fixture();
        window.window_id = 0;
        assert!(!visible_candidate(&window));
        assert!(!dialog_role_matches(
            Some(BUNDLE_ID),
            Some("AXWindow"),
            Some("AXStandardWindow")
        ));
        assert!(!dialog_role_matches(
            Some(BUNDLE_ID),
            Some("AXMenu"),
            Some("AXSystemDialog")
        ));
        assert!(!dialog_role_matches(
            Some(BUNDLE_ID),
            Some("AXWindow"),
            None
        ));
    }

    #[test]
    #[ignore = "read-only live check: requires an already visible supported macOS permission dialog"]
    fn live_system_dialog_discovery_read_only() {
        for window in crate::windows::visible_windows_including_accessory_layers_with_snapshot()
            .windows
            .into_iter()
            .filter(visible_candidate)
        {
            println!("System dialog diagnostic: candidate={} trusted={} ax_ids={:?} bundle={:?} executable={:?}",
                     visible_candidate(&window), trusted_process(window.pid), dialog_window_ids(window.pid),
                     super::super::bundle_id_for_pid(window.pid), super::super::executable_path_for_pid(window.pid));
        }
        let windows = visible_windows();
        assert!(
            !windows.is_empty(),
            "No verified visible system dialog was discovered"
        );
        let apps = running_apps();
        assert!(apps
            .iter()
            .any(|app| identity_for_bundle(app.bundle_id.as_deref()).is_some()));
        assert!(!observation_advisories(0).is_empty());
        let own_bundle = super::super::bundle_id_for_pid(windows[0].pid).unwrap();
        assert!(observation_advisories(windows[0].pid)
            .iter()
            .all(|hint| hint["bundle_id"] != own_bundle));
        println!("Verified {} visible system dialog(s); separate app inventory and observation hints are present. No action dispatched.", windows.len());
    }
}
