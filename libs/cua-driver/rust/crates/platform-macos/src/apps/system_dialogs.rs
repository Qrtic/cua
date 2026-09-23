//! Discovery of visible macOS permission dialogs outside ordinary app windows.
//!
//! UserNotificationCenter is an accessory application, so the regular-app
//! inventory and desktop-independent capture omit its dialogs. Expose its
//! verified, visible AXSystemDialog windows as a separate app target. This is
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

pub(crate) const BUNDLE_ID: &str = "com.apple.UserNotificationCenter";
const APP_NAME: &str = "UserNotificationCenter";
const CODE_PATH: &str = "/System/Library/CoreServices/UserNotificationCenter.app";
const EXECUTABLE: &str =
    "/System/Library/CoreServices/UserNotificationCenter.app/Contents/MacOS/UserNotificationCenter";
const MAX_WINDOWS: usize = 4;

fn trusted_identity(bundle: Option<&str>, path: Option<&str>, signed: bool) -> bool {
    bundle == Some(BUNDLE_ID) && path == Some(CODE_PATH) && signed
}

fn trusted_process(pid: i32) -> bool {
    use core_foundation::url::kCFURLPOSIXPathStyle;
    use security_framework::os::macos::code_signing::{
        Flags, GuestAttributes, SecCode, SecRequirement,
    };

    if pid <= 0 || super::bundle_id_for_pid(pid).as_deref() != Some(BUNDLE_ID) {
        return false;
    }
    let verified_path = (|| {
        let mut attributes = GuestAttributes::new();
        attributes.set_pid(pid as libc::pid_t);
        let code = SecCode::copy_guest_with_attribues(None, &attributes, Flags::NONE).ok()?;
        let requirement =
            SecRequirement::from_str(&format!("anchor apple and identifier \"{BUNDLE_ID}\""))
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
    super::executable_path_for_pid(pid).as_deref() == Some(EXECUTABLE)
        && trusted_identity(
            super::bundle_id_for_pid(pid).as_deref(),
            verified_path.as_deref(),
            verified_path.is_some(),
        )
}

fn visible_candidate(window: &WindowInfo) -> bool {
    window.pid > 0
        && window.window_id > 0
        && window.app_name == APP_NAME
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

fn dialog_role_matches(role: Option<&str>, subrole: Option<&str>) -> bool {
    role == Some("AXWindow") && subrole == Some("AXSystemDialog")
}

fn dialog_window_ids(pid: i32) -> HashSet<u32> {
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
                if dialog_role_matches(role.as_deref(), subrole.as_deref()) {
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
            Some(super::AppInfo {
                name: app.localizedName()?.to_string(),
                pid: window.pid,
                bundle_id: Some(BUNDLE_ID.to_owned()),
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
    let count = visible_windows()
        .iter()
        .filter(|window| window.pid != observed_pid)
        .count();
    if count == 0 {
        return Vec::new();
    }
    vec![json!({
        "app_name": APP_NAME,
        "bundle_id": BUNDLE_ID,
        "kind": "system_dialog",
        "window_count": count,
        "visibility": "on_screen",
        "identity_verified": true,
        "relationship": "not_established",
        "advisory": true,
    })]
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
            Some("AXWindow"),
            Some("AXStandardWindow")
        ));
        assert!(!dialog_role_matches(Some("AXMenu"), Some("AXSystemDialog")));
        assert!(!dialog_role_matches(Some("AXWindow"), None));
    }

    #[test]
    #[ignore = "read-only live check: requires an already visible macOS UserNotificationCenter dialog"]
    fn live_system_dialog_discovery_read_only() {
        for window in crate::windows::visible_windows_including_accessory_layers_with_snapshot()
            .windows
            .into_iter()
            .filter(|window| window.app_name == APP_NAME)
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
            .any(|app| app.bundle_id.as_deref() == Some(BUNDLE_ID)));
        assert!(!observation_advisories(0).is_empty());
        assert!(observation_advisories(windows[0].pid).is_empty());
        println!("Verified {} visible system dialog(s); separate app inventory and observation hints are present. No action dispatched.", windows.len());
    }
}
