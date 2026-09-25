//! Recover a native editor recreated by the one focus request we just sent.
//!
//! AppKit can invalidate every field object when committing the previous field.
//! A retained CF reference prevents a use-after-free, but does not keep that AX
//! object valid. Only an exact, already-focused replacement is eligible here;
//! neither focus nor value input is replayed.

use super::{bindings::*, cache::RetainedElement};
use core_foundation::{
    base::{CFEqual, CFGetTypeID, CFRelease, CFTypeRef, TCFType},
    string::CFString,
};
use std::{
    cell::{Cell, RefCell},
    time::{Duration, Instant},
};

#[derive(Clone, Debug, PartialEq)]
struct Identity {
    pid: i32,
    window_id: u32,
    role: String,
    identifier: String,
    placeholder: Option<String>,
    description: Option<String>,
    value: String,
    frame: [f64; 4],
    ancestors: Vec<(String, Option<String>)>,
}

fn eligible_identity(identity: &Identity) -> bool {
    identity.pid > 0
        && identity.window_id > 0
        && matches!(identity.role.as_str(), "AXTextField" | "AXTextArea")
        && !identity.identifier.trim().is_empty()
        && identity.frame.iter().all(|v| v.is_finite())
        && identity.frame[2] > 0.0
        && identity.frame[3] > 0.0
        && identity
            .ancestors
            .last()
            .is_some_and(|(role, _)| role == "AXWindow")
}

fn matches_recreated_editor(before: &Identity, after: &Identity) -> bool {
    eligible_identity(before) && eligible_identity(after) && before == after
}

fn may_resolve_replacement(error: AXError, focus_requested: bool, already_rebound: bool) -> bool {
    error == kAXErrorInvalidUIElement && focus_requested && !already_rebound
}

// Missing optional strings are allowed; failed reads are not matching evidence.
unsafe fn optional_string(element: AXUIElementRef, name: &str) -> Option<Option<String>> {
    let name = CFString::new(name);
    let mut value: CFTypeRef = std::ptr::null();
    let status = AXUIElementCopyAttributeValue(element, name.as_concrete_TypeRef(), &mut value);
    if status != kAXErrorSuccess {
        if !value.is_null() {
            CFRelease(value);
        }
        return (status == kAXErrorAttributeUnsupported || status == kAXErrorNoValue)
            .then_some(None);
    }
    if value.is_null() {
        return None;
    }
    if CFGetTypeID(value) != CFString::type_id() {
        CFRelease(value);
        return None;
    }
    let text = CFString::wrap_under_create_rule(value as _).to_string();
    (text.len() <= 16_384).then_some(Some(text))
}

unsafe fn identity(element: AXUIElementRef, pid: i32, window_id: u32) -> Option<Identity> {
    let deadline = Instant::now() + Duration::from_millis(150);
    let role = optional_string(element, "AXRole")??;
    let identifier = optional_string(element, "AXIdentifier")??;
    let placeholder = optional_string(element, "AXPlaceholderValue")?;
    let description = optional_string(element, "AXDescription")?;
    let value = optional_string(element, "AXValue")??;
    let frame = element_screen_rect(element)?;
    let mut ancestors = Vec::new();
    let mut retained = vec![RetainedElement::retain(element as usize)];
    for _ in 0..32 {
        if Instant::now() >= deadline {
            return None;
        }
        let parent = copy_element_attr(retained.last()?.as_ptr() as AXUIElementRef, "AXParent")?;
        let parent_guard = RetainedElement::retain(parent as usize);
        CFRelease(parent as CFTypeRef);
        if retained
            .iter()
            .any(|old| CFEqual(old.as_ptr() as CFTypeRef, parent as CFTypeRef) != 0)
        {
            return None;
        }
        let mut owner = 0;
        if AXUIElementGetPid(parent, &mut owner) != kAXErrorSuccess || owner != pid {
            return None;
        }
        let parent_role = optional_string(parent, "AXRole")??;
        let parent_id = optional_string(parent, "AXIdentifier")?;
        let done = parent_role == "AXWindow";
        if matches!(
            parent_role.as_str(),
            "AXApplication" | "AXWebArea" | "AXSheet" | "AXPopover"
        ) {
            return None;
        }
        ancestors.push((parent_role, parent_id));
        retained.push(parent_guard);
        if done {
            if ax_get_window_id(parent) != Some(window_id) || Instant::now() >= deadline {
                return None;
            }
            let result = Identity {
                pid,
                window_id,
                role,
                identifier,
                placeholder,
                description,
                value,
                frame,
                ancestors,
            };
            return eligible_identity(&result).then_some(result);
        }
    }
    None
}

pub(crate) struct NativeTextEditor {
    element: RefCell<RetainedElement>,
    original: Option<Identity>,
    focus_requested: Cell<bool>,
    rebound: Cell<bool>,
}

impl NativeTextEditor {
    pub(crate) unsafe fn new(ptr: usize, pid: i32, window_id: u32, allow_rebind: bool) -> Self {
        Self {
            element: RefCell::new(RetainedElement::retain(ptr)),
            original: allow_rebind
                .then(|| identity(ptr as AXUIElementRef, pid, window_id))
                .flatten(),
            focus_requested: Cell::new(false),
            rebound: Cell::new(false),
        }
    }

    pub(crate) fn ptr(&self) -> usize {
        self.element.borrow().as_ptr()
    }
    pub(crate) fn rebound(&self) -> bool {
        self.rebound.get()
    }

    pub(crate) fn focus(&self) -> AXError {
        self.focus_requested.set(true);
        unsafe { set_bool_attr_true(self.ptr() as AXUIElementRef, "AXFocused") }
    }

    pub(crate) fn focused(&self) -> Option<bool> {
        let result = unsafe { try_copy_bool_attr(self.ptr() as AXUIElementRef, "AXFocused") };
        let error = match result {
            Ok(value) => return Some(value),
            Err(error) => error,
        };
        if !may_resolve_replacement(error, self.focus_requested.get(), self.rebound.get()) {
            return None;
        }
        let before = self.original.as_ref()?;
        if crate::foreground_activity::check_request().is_err() {
            return None;
        }
        unsafe {
            let candidate = focused_element_of_pid(before.pid)?;
            let retained = RetainedElement::retain(candidate as usize);
            CFRelease(candidate as CFTypeRef);
            let after = identity(candidate, before.pid, before.window_id)?;
            if !matches_recreated_editor(before, &after)
                || !super::exact_target::native_text_field_in_window(
                    candidate,
                    before.pid,
                    before.window_id,
                )
                || try_copy_bool_attr(candidate, "AXFocused") != Ok(true)
                || crate::foreground_activity::check_request().is_err()
            {
                return None;
            }
            *self.element.borrow_mut() = retained;
            self.rebound.set(true);
            tracing::debug!(target: "cua_native_text", pid = before.pid, window_id = before.window_id,
                "Rebound invalid native editor to its proven focused replacement without replaying input");
            Some(true)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn field() -> Identity {
        Identity {
            pid: 10,
            window_id: 20,
            role: "AXTextField".into(),
            identifier: "field-last".into(),
            placeholder: Some("Last".into()),
            description: Some("Last".into()),
            value: "Baseline".into(),
            frame: [10.0, 20.0, 30.0, 40.0],
            ancestors: vec![
                ("AXSplitGroup".into(), None),
                ("AXWindow".into(), Some("host".into())),
            ],
        }
    }
    #[test]
    fn recreated_editor_requires_exact_semantics_geometry_context_and_prior_value() {
        let original = field();
        assert!(matches_recreated_editor(&original, &original.clone()));
        for change in 0..9 {
            let mut candidate = original.clone();
            match change {
                0 => candidate.pid += 1,
                1 => candidate.window_id += 1,
                2 => candidate.identifier = "field-first".into(),
                3 => candidate.placeholder = Some("Email".into()),
                4 => candidate.description = None,
                5 => candidate.value = "different record".into(),
                6 => candidate.frame[0] += 1.0,
                7 => candidate.ancestors[0].1 = Some("another form".into()),
                _ => candidate.role = "AXTextArea".into(),
            }
            assert!(
                !matches_recreated_editor(&original, &candidate),
                "change {change}"
            );
        }
    }
    #[test]
    fn anonymous_unbounded_or_non_native_identity_never_allows_rebinding() {
        for change in 0..6 {
            let mut candidate = field();
            match change {
                0 => candidate.identifier.clear(),
                1 => candidate.frame[0] = f64::NAN,
                2 => candidate.frame[2] = 0.0,
                3 => candidate.ancestors.clear(),
                4 => candidate.role = "AXWebArea".into(),
                _ => candidate.window_id = 0,
            }
            assert!(!matches_recreated_editor(&candidate, &candidate.clone()));
        }
    }
    #[test]
    fn only_definitive_invalidation_after_one_focus_request_allows_resolution() {
        assert!(may_resolve_replacement(
            kAXErrorInvalidUIElement,
            true,
            false
        ));
        assert!(!may_resolve_replacement(
            kAXErrorCannotComplete,
            true,
            false
        ));
        assert!(!may_resolve_replacement(kAXErrorSuccess, true, false));
        assert!(!may_resolve_replacement(
            kAXErrorInvalidUIElement,
            false,
            false
        ));
        assert!(!may_resolve_replacement(
            kAXErrorInvalidUIElement,
            true,
            true
        ));
    }
}
