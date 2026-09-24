//! Read-only navigation hints for inactive native macOS window tabs.
//!
//! An inactive tab can have a CGWindowID and screenshot but no AXWindow. Its
//! selector belongs to the selected sibling, never to the requested window.
//! Return only a title-match advisory; do not mint elements or perform input.

use super::bindings::*;
use core_foundation::base::{CFRelease, CFTypeRef};
use serde::Serialize;
use std::time::{Duration, Instant};

#[derive(Debug, Serialize, PartialEq, Eq)]
pub(crate) struct WindowTabHint {
    pub(crate) pid: i32,
    pub(crate) target_window_id: u32,
    pub(crate) host_window_id: u32,
    pub(crate) tab_label: String,
    pub(crate) match_kind: &'static str,
}

#[derive(Clone)]
struct TabHost {
    pid: i32,
    window_id: u32,
    title: String,
    tabs: Vec<(String, bool)>,
}

fn choose_hint(pid: i32, target_id: u32, title: &str, hosts: &[TabHost]) -> Option<WindowTabHint> {
    if pid <= 0 || target_id == 0 || title.trim().is_empty() || title.len() > 1024 {
        return None;
    }
    let mut matches = Vec::new();
    for host in hosts {
        if host.pid != pid || host.window_id == 0 || host.window_id == target_id {
            continue;
        }
        // A top-level tab group must identify its selected sibling, rather
        // than merely containing a similarly named application content tab.
        let selected: Vec<_> = host.tabs.iter().filter(|(_, selected)| *selected).collect();
        if selected.len() != 1 || selected[0].0 != host.title || host.title == title {
            continue;
        }
        for (label, selected) in &host.tabs {
            if label == title && !selected {
                matches.push(host.window_id);
            }
        }
    }
    if matches.len() != 1 {
        return None;
    }
    Some(WindowTabHint {
        pid,
        target_window_id: target_id,
        host_window_id: matches[0],
        tab_label: title.to_owned(),
        match_kind: "unique_exact_title",
    })
}

struct OwnedAx(AXUIElementRef);
impl Drop for OwnedAx {
    fn drop(&mut self) {
        unsafe { CFRelease(self.0 as CFTypeRef) }
    }
}

unsafe fn owned_children(element: AXUIElementRef) -> Option<Vec<OwnedAx>> {
    let children: Vec<_> = copy_children(element).into_iter().map(OwnedAx).collect();
    (children.len() <= 64).then_some(children)
}

unsafe fn prepare_node(node: AXUIElementRef, pid: i32) -> bool {
    let mut owner = 0;
    AXUIElementSetMessagingTimeout(node, 0.05) == kAXErrorSuccess
        && AXUIElementGetPid(node, &mut owner) == kAXErrorSuccess
        && owner == pid
}

/// Best-effort bounded inspection of immediate native tab groups only. Never
/// traverses web content, activates an app, or treats a title as input authority.
pub(crate) fn find_hint(pid: i32, target_id: u32) -> Option<WindowTabHint> {
    let deadline = Instant::now() + Duration::from_millis(350);
    let inventory = crate::windows::all_windows_with_space_snapshot();
    if !inventory.succeeded {
        return None;
    }
    let target = inventory
        .windows
        .iter()
        .find(|w| w.pid == pid && w.window_id == target_id)?;
    if target.is_on_screen || target.title.trim().is_empty() {
        return None;
    }
    unsafe {
        let ptr = AXUIElementCreateApplication(pid);
        if ptr.is_null() {
            return None;
        }
        let app = OwnedAx(ptr);
        if !prepare_node(app.0, pid) {
            return None;
        }
        let snapshot = try_copy_ax_windows(app.0).ok()?;
        let windows: Vec<_> = snapshot.windows.into_iter().map(OwnedAx).collect();
        if !snapshot.complete || windows.len() > 32 {
            return None;
        }
        let mut hosts = Vec::new();
        for window in &windows {
            if Instant::now() >= deadline {
                return None;
            }
            if !prepare_node(window.0, pid) {
                return None;
            }
            let Some(id) = ax_get_window_id(window.0) else {
                continue;
            };
            // Do not reinterpret a target which appeared while we were reading.
            if id == target_id {
                return None;
            }
            let Some(info) = inventory
                .windows
                .iter()
                .find(|w| w.pid == pid && w.window_id == id && w.is_on_screen && w.layer == 0)
            else {
                continue;
            };
            if copy_string_attr(window.0, "AXRole").as_deref() != Some("AXWindow") {
                continue;
            }
            for child in owned_children(window.0)? {
                if Instant::now() >= deadline {
                    return None;
                }
                if !prepare_node(child.0, pid) {
                    return None;
                }
                if copy_string_attr(child.0, "AXRole").as_deref() != Some("AXTabGroup") {
                    continue;
                }
                let mut tabs = Vec::new();
                for tab in owned_children(child.0)? {
                    if Instant::now() >= deadline {
                        return None;
                    }
                    if !prepare_node(tab.0, pid) {
                        return None;
                    }
                    if copy_string_attr(tab.0, "AXRole").as_deref() != Some("AXRadioButton") {
                        continue;
                    }
                    if !copy_action_names(tab.0)
                        .iter()
                        .any(|name| name == "AXPress")
                    {
                        continue;
                    }
                    if let Some(label) = copy_string_attr(tab.0, "AXTitle") {
                        // AppKit native radio tabs expose CFBoolean here;
                        // numeric-only reads discard the selected host tab.
                        let selected = copy_bool_attr(tab.0, "AXValue") == Some(true)
                            || copy_bool_attr(tab.0, "AXSelected") == Some(true);
                        tabs.push((label, selected));
                    }
                }
                hosts.push(TabHost {
                    pid,
                    window_id: id,
                    title: info.title.clone(),
                    tabs,
                });
            }
        }
        if Instant::now() >= deadline {
            return None;
        }
        choose_hint(pid, target_id, &target.title, &hosts)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn host() -> TabHost {
        TabHost {
            pid: 42,
            window_id: 7,
            title: "Existing document".into(),
            tabs: vec![
                ("Existing document".into(), true),
                ("Requested document".into(), false),
            ],
        }
    }

    #[test]
    fn inactive_window_gets_navigation_hint_without_elements_or_input_authority() {
        let hint = choose_hint(42, 8, "Requested document", &[host()]).unwrap();
        assert_eq!(hint.host_window_id, 7);
        assert_eq!(hint.target_window_id, 8);
        assert_eq!(hint.match_kind, "unique_exact_title");
        let value = serde_json::to_value(hint).unwrap();
        assert!(value.get("element_index").is_none());
        assert!(value.get("element_token").is_none());
    }

    #[test]
    fn duplicate_labels_in_one_or_two_hosts_are_ambiguous() {
        let mut duplicate = host();
        duplicate.tabs.push(("Requested document".into(), false));
        assert!(choose_hint(42, 8, "Requested document", &[duplicate]).is_none());
        let mut sibling = host();
        sibling.window_id = 9;
        assert!(choose_hint(42, 8, "Requested document", &[host(), sibling]).is_none());
    }

    #[test]
    fn foreign_identity_target_itself_or_unselected_host_are_not_hints() {
        let mut foreign = host();
        foreign.pid = 43;
        let mut same = host();
        same.window_id = 8;
        let mut unselected = host();
        unselected.tabs[0].1 = false;
        let mut wrong_title = host();
        wrong_title.title = "Different window".into();
        for candidate in [foreign, same, unselected, wrong_title] {
            assert!(choose_hint(42, 8, "Requested document", &[candidate]).is_none());
        }
    }

    #[test]
    fn partial_title_selected_target_and_missing_title_do_not_match() {
        assert!(choose_hint(42, 8, "Requested", &[host()]).is_none());
        assert!(choose_hint(42, 8, "", &[host()]).is_none());
        let mut selected = host();
        selected.tabs[1].1 = true;
        assert!(choose_hint(42, 8, "Requested document", &[selected]).is_none());
    }
}
