//! A hit-tested native button hidden below an actionless AXButton wrapper.
//!
//! This proves only that one virtual child belongs to its wrapper. Callers must
//! additionally prove the complete attached-popover path to the addressed host.
//! No synthetic action, focus change or pointer input is emitted here.

use super::bindings::*;
use core_foundation::{
    array::CFArray,
    base::{CFEqual, CFGetTypeID, CFRelease, CFTypeRef, TCFType},
    string::CFString,
};
use std::time::Instant;

#[derive(Clone)]
struct ButtonEvidence {
    role: String,
    description: String,
    pid: i32,
    window_id: u32,
    frame: [f64; 4],
    actions: Vec<String>,
    enabled: Option<bool>,
}

fn contains(outer: [f64; 4], inner: [f64; 4], tolerance: f64) -> bool {
    outer.iter().chain(inner.iter()).all(|n| n.is_finite())
        && outer[2] > 0.0
        && outer[3] > 0.0
        && inner[2] > 0.0
        && inner[3] > 0.0
        && inner[0] >= outer[0] - tolerance
        && inner[1] >= outer[1] - tolerance
        && inner[0] + inner[2] <= outer[0] + outer[2] + tolerance
        && inner[1] + inner[3] <= outer[1] + outer[3] + tolerance
}

fn candidate_pair(parent: &ButtonEvidence, child: &ButtonEvidence) -> bool {
    let centre = [
        parent.frame[0] + parent.frame[2] / 2.0,
        parent.frame[1] + parent.frame[3] / 2.0,
    ];
    parent.role == "AXButton" && child.role == "AXButton"
        && parent.pid > 0 && parent.pid == child.pid
        && parent.window_id > 0 && parent.window_id == child.window_id
        && !parent.description.trim().is_empty()
        && parent.description == child.description
        && parent.actions.is_empty()
        && child.actions.iter().any(|action| action == "AXPress")
        && child.enabled == Some(true)
        // AppKit rounds the tile and preview edges independently (one point
        // in the measured case). Never substitute merely overlapping bounds.
        && contains(parent.frame, child.frame, 2.0)
        && centre[0] >= child.frame[0] && centre[0] <= child.frame[0] + child.frame[2]
        && centre[1] >= child.frame[1] && centre[1] <= child.frame[1] + child.frame[3]
}

struct Owned(AXUIElementRef);
impl Drop for Owned {
    fn drop(&mut self) {
        unsafe {
            CFRelease(self.0 as CFTypeRef);
        }
    }
}
unsafe fn bounded(ptr: AXUIElementRef) -> Option<Owned> {
    if ptr.is_null() {
        return None;
    }
    let owned = Owned(ptr);
    (AXUIElementSetMessagingTimeout(ptr, 0.1) == kAXErrorSuccess).then_some(owned)
}

unsafe fn actions(element: AXUIElementRef) -> Option<Vec<String>> {
    let mut value = std::ptr::null();
    let status = AXUIElementCopyActionNames(element, &mut value);
    if status != kAXErrorSuccess || value.is_null() {
        return None;
    }
    if CFGetTypeID(value as CFTypeRef) != CFArray::<CFTypeRef>::type_id() {
        CFRelease(value as CFTypeRef);
        return None;
    }
    let names = CFArray::<CFTypeRef>::wrap_under_create_rule(value);
    if names.len() > 64 {
        return None;
    }
    (0..names.len())
        .map(|i| {
            let ptr = *names.get(i)?;
            (CFGetTypeID(ptr) == CFString::type_id())
                .then(|| CFString::wrap_under_get_rule(ptr as _).to_string())
        })
        .collect()
}

unsafe fn no_children(element: AXUIElementRef, attribute: &str, allow_unsupported: bool) -> bool {
    let mut value = std::ptr::null();
    let name = CFString::new(attribute);
    let status = AXUIElementCopyAttributeValue(element, name.as_concrete_TypeRef(), &mut value);
    if value.is_null() {
        return status == kAXErrorNoValue
            || (allow_unsupported && status == kAXErrorAttributeUnsupported);
    }
    if status != kAXErrorSuccess || CFGetTypeID(value) != CFArray::<CFTypeRef>::type_id() {
        CFRelease(value);
        return false;
    }
    CFArray::<CFTypeRef>::wrap_under_create_rule(value as _).is_empty()
}

unsafe fn read_button(element: AXUIElementRef, deadline: Instant) -> Option<ButtonEvidence> {
    if Instant::now() >= deadline || AXUIElementSetMessagingTimeout(element, 0.1) != kAXErrorSuccess
    {
        return None;
    }
    let role = copy_string_attr(element, "AXRole")?;
    if role != "AXButton" {
        return None;
    }
    let mut pid = 0;
    if AXUIElementGetPid(element, &mut pid) != kAXErrorSuccess {
        return None;
    }
    let evidence = ButtonEvidence {
        role,
        pid,
        description: copy_string_attr(element, "AXDescription")?,
        window_id: ax_get_window_id(element)?,
        frame: element_screen_rect(element)?,
        actions: actions(element)?,
        enabled: copy_bool_attr(element, "AXEnabled"),
    };
    (Instant::now() < deadline).then_some(evidence)
}

unsafe fn hit(pid: i32, frame: [f64; 4], deadline: Instant) -> Option<Owned> {
    if Instant::now() >= deadline {
        return None;
    }
    let app = bounded(AXUIElementCreateApplication(pid))?;
    let mut element = std::ptr::null_mut();
    let status = AXUIElementCopyElementAtPosition(
        app.0,
        (frame[0] + frame[2] / 2.0) as f32,
        (frame[1] + frame[3] / 2.0) as f32,
        &mut element,
    );
    if status != kAXErrorSuccess {
        if !element.is_null() {
            CFRelease(element as CFTypeRef);
        }
        return None;
    }
    bounded(element)
}

/// Bounded alternate edge proof. It does not authorize an action by itself.
pub(crate) unsafe fn proves(
    parent: AXUIElementRef,
    child: AXUIElementRef,
    deadline: Instant,
) -> bool {
    let prove_once = || -> Option<()> {
        let p = read_button(parent, deadline)?;
        let c = read_button(child, deadline)?;
        if !candidate_pair(&p, &c)
            || !no_children(parent, "AXChildren", false)
            || !no_children(parent, "AXChildrenInNavigationOrder", true)
        {
            return None;
        }
        let actual_parent = bounded(copy_element_attr(child, "AXParent")?)?;
        let pw = bounded(copy_element_attr(parent, "AXWindow")?)?;
        let cw = bounded(copy_element_attr(child, "AXWindow")?)?;
        if CFEqual(actual_parent.0 as CFTypeRef, parent as CFTypeRef) == 0
            || CFEqual(pw.0 as CFTypeRef, cw.0 as CFTypeRef) == 0
        {
            return None;
        }
        let window = crate::windows::window_info_by_id(p.window_id)?;
        let b = &window.bounds;
        if window.pid != p.pid
            || !window.is_on_screen
            || window.on_current_space == Some(false)
            || !contains([b.x, b.y, b.width, b.height], p.frame, 2.0)
        {
            return None;
        }
        let live = hit(p.pid, p.frame, deadline)?;
        (Instant::now() < deadline && CFEqual(live.0 as CFTypeRef, child as CFTypeRef) != 0)
            .then_some(())
    };
    prove_once().is_some() && prove_once().is_some()
}

/// Discover the inner native button, still requiring the caller's host proof.
pub(crate) unsafe fn copy_child(
    parent: AXUIElementRef,
    deadline: Instant,
) -> Option<AXUIElementRef> {
    let p = read_button(parent, deadline)?;
    if !p.actions.is_empty() || !no_children(parent, "AXChildren", false) {
        return None;
    }
    let child = hit(p.pid, p.frame, deadline)?;
    if !proves(parent, child.0, deadline) {
        return None;
    }
    Some(std::mem::ManuallyDrop::new(child).0)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn preview() -> (ButtonEvidence, ButtonEvidence) {
        let parent = ButtonEvidence {
            role: "AXButton".into(),
            description: "Blank".into(),
            pid: 42,
            window_id: 900,
            frame: [232.0, 609.0, 114.0, 96.0],
            actions: vec![],
            enabled: None,
        };
        let child = ButtonEvidence {
            frame: [233.0, 608.0, 112.0, 68.0],
            actions: vec!["AXPress".into()],
            enabled: Some(true),
            ..parent.clone()
        };
        (parent, child)
    }
    #[test]
    fn admits_measured_single_preview_with_one_point_rounding_difference() {
        let (parent, child) = preview();
        assert!(candidate_pair(&parent, &child));
    }
    #[test]
    fn never_projects_foreign_mislabeled_disabled_or_unactionable_hit() {
        for mutation in 0..9 {
            let (mut p, mut c) = preview();
            match mutation {
                0 => c.pid = 43,
                1 => c.window_id = 901,
                2 => c.role = "AXImage".into(),
                3 => c.description = "Title".into(),
                4 => p.description.clear(),
                5 => c.enabled = None,
                6 => c.enabled = Some(false),
                7 => c.actions.clear(),
                _ => p.actions.push("AXPress".into()),
            }
            assert!(!candidate_pair(&p, &c), "case {mutation}");
        }
    }
    #[test]
    fn mere_overlap_offcentre_or_invalid_geometry_does_not_prove_a_virtual_child() {
        for frame in [
            [200.0, 608.0, 112.0, 68.0],
            [233.0, 608.0, 112.0, 20.0],
            [233.0, 608.0, 0.0, 68.0],
            [f64::NAN, 608.0, 112.0, 68.0],
            [233.0, 605.0, 112.0, 68.0],
        ] {
            let (p, mut c) = preview();
            c.frame = frame;
            assert!(!candidate_pair(&p, &c));
        }
    }
}
