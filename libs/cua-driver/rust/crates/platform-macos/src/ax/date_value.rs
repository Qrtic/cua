//! Typed native date values. Never guess a locale, time zone, or date component.

use core_foundation::{
    base::{CFGetTypeID, CFRelease, CFTypeRef, TCFType},
    date::CFDate,
    string::CFString,
};
use time::{format_description::well_known::Rfc3339, OffsetDateTime};

use super::bindings::{
    kAXErrorSuccess, AXError, AXUIElementCopyAttributeValue, AXUIElementRef,
    AXUIElementSetAttributeValue,
};

const CF_EPOCH_UNIX_NANOS: i128 = 978_307_200_000_000_000;

pub(crate) fn parse(value: &str) -> Result<f64, &'static str> {
    // RFC 3339's -00:00 denotes an unknown local offset, not known UTC.
    if value.ends_with("-00:00") {
        return Err("A native date/time value needs a known time zone offset");
    }
    let date = OffsetDateTime::parse(value, &Rfc3339).map_err(|_| {
        "Use an RFC 3339 date/time with an explicit time zone, such as 2030-01-15T17:00:00+08:00"
    })?;
    Ok((date.unix_timestamp_nanos() - CF_EPOCH_UNIX_NANOS) as f64 / 1_000_000_000.0)
}

pub(crate) fn format(absolute_time: f64) -> Option<String> {
    if !absolute_time.is_finite() || absolute_time.abs() > 1_000_000_000_000.0 {
        return None;
    }
    let unix_nanos = (absolute_time * 1_000_000_000.0).round() as i128 + CF_EPOCH_UNIX_NANOS;
    OffsetDateTime::from_unix_timestamp_nanos(unix_nanos)
        .ok()?
        .format(&Rfc3339)
        .ok()
}

/// Borrow a CFDate without changing ownership or coercing another CF type.
pub(crate) unsafe fn borrowed_absolute_time(value: CFTypeRef) -> Option<f64> {
    if value.is_null() || CFGetTypeID(value) != CFDate::type_id() {
        return None;
    }
    let date = CFDate::wrap_under_get_rule(value.cast());
    let value = date.abs_time();
    format(value).map(|_| value)
}

pub(crate) unsafe fn copy(element: AXUIElementRef) -> Option<f64> {
    let name = CFString::new("AXValue");
    let mut value: CFTypeRef = std::ptr::null();
    if AXUIElementCopyAttributeValue(element, name.as_concrete_TypeRef(), &mut value)
        != kAXErrorSuccess
        || value.is_null()
    {
        return None;
    }
    let result = borrowed_absolute_time(value);
    CFRelease(value);
    result
}

/// The caller must re-prove the exact enabled, writable native date control.
pub(crate) unsafe fn set(element: AXUIElementRef, absolute_time: f64) -> AXError {
    let name = CFString::new("AXValue");
    let date = CFDate::new(absolute_time);
    AXUIElementSetAttributeValue(element, name.as_concrete_TypeRef(), date.as_CFTypeRef())
}

#[cfg(test)]
mod tests {
    use super::*;
    use core_foundation::{number::CFNumber, string::CFString};

    #[test]
    fn explicit_offsets_preserve_the_requested_instant() {
        let local = parse("2026-10-02T17:00:00+08:00").unwrap();
        assert_eq!(local, parse("2026-10-02T09:00:00Z").unwrap());
        assert_eq!(format(local).as_deref(), Some("2026-10-02T09:00:00Z"));
        assert_eq!(format(0.0).as_deref(), Some("2001-01-01T00:00:00Z"));
        assert_eq!(
            format(parse("2000-02-29T00:00:00Z").unwrap()).as_deref(),
            Some("2000-02-29T00:00:00Z")
        );
    }

    #[test]
    fn ambiguous_invalid_and_nonfinite_dates_are_not_coerced() {
        for value in [
            "5:00 PM",
            "2026-10-02",
            "02/10/2026",
            "2026-10-02T17:00:00",
            "2030-02-29T17:00:00Z",
            "2026-10-02T17:00:00-00:00",
            "812595600",
        ] {
            assert!(parse(value).is_err(), "{value}");
        }
        for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, 1e18] {
            assert!(format(value).is_none());
        }
        let text = CFString::new("2026-10-02T09:00:00Z");
        let number = CFNumber::from(812_595_600.0);
        assert!(unsafe { borrowed_absolute_time(text.as_CFTypeRef()) }.is_none());
        assert!(unsafe { borrowed_absolute_time(number.as_CFTypeRef()) }.is_none());
    }

    #[test]
    fn typed_cfdate_roundtrip_does_not_lose_its_reference_epoch_or_fraction() {
        for input in [
            "2026-12-25T23:59:59+08:00",
            "2001-01-01T00:00:00.125Z",
            "1969-12-31T23:59:59Z",
        ] {
            let seconds = parse(input).unwrap();
            let date = CFDate::new(seconds);
            assert_eq!(
                unsafe { borrowed_absolute_time(date.as_CFTypeRef()) },
                Some(seconds)
            );
            let normalized = format(seconds).unwrap();
            assert_eq!(parse(&normalized).unwrap(), seconds);
        }
    }
}
