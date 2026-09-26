//! Window / display screenshot capture for macOS.
//!
//! ## Window capture (primary: ScreenCaptureKit)
//!
//! Window capture takes one complete ScreenCaptureKit stream frame with a
//! exact window filter, validates its composition metadata,
//! stops the stream, and encodes PNG in memory. SCScreenshotManager omits
//! the frame metadata: a correctly sized bitmap can contain a resized or
//! offset host after child-window composition. No subprocess, temp file,
//! or base64 is used on the native success path.
//!
//! Native child-window composition is always disabled. Positively associated
//! physical surfaces intersecting the target are explicitly included in a
//! display filter cropped to that same target. Off-crop attachments remain
//! identity-checked but do not enlarge or contribute pixels to the crop.
//!
//! A process-local bounded warm cache (TTL 2s, capacity 32) reuses
//! `SCContentFilter` + `SCStreamConfiguration` plans across rapid captures of
//! the same window id so warm hits skip `SCShareableContent::get` and plan
//! construction only when no attachments were discovered. Composed plans,
//! streams and captured frames are never cached. Discovery and all selected
//! physical identities are rechecked before releasing captured bytes.
//!
//! Sources:
//! - https://developer.apple.com/documentation/screencapturekit/scstreamframeinfo
//! - https://developer.apple.com/documentation/screencapturekit/sccontentfilter/init(desktopindependentwindow:)
//! - https://docs.rs/screencapturekit/6.0.1/screencapturekit/
//!
//! The window shell compatibility backend cannot prove exclusion of implicit
//! child surfaces. Errors from the explicit native window route therefore
//! carry a typed no-fallback marker, including worker timeouts. This can make
//! previously masked native failures visible; it cannot return an unverified
//! automatically composed image as recovery. Display capture is unchanged.
//!
//! ## Display capture
//!
//! `screencapture -x <file>` still captures the full main display (unchanged
//! in this slice).

use base64::{engine::general_purpose::STANDARD as BASE64, Engine};
use std::collections::HashMap;
use std::hash::Hash;
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Mutex, OnceLock};
use std::time::{Duration, Instant};

mod attachments;
pub(crate) mod desktop;

/// Bounded TTL map keyed by insertion time. Std-only; used for the warm SCK
/// window filter/config cache and unit-tested independently of ScreenCaptureKit.
struct TimedCache<K, V> {
    ttl: Duration,
    capacity: usize,
    next_seq: u64,
    map: HashMap<K, TimedCacheEntry<V>>,
}

struct TimedCacheEntry<V> {
    value: V,
    inserted_at: Instant,
    /// Monotonic insertion sequence for oldest-first eviction (stable ties).
    seq: u64,
}

impl<K, V> TimedCache<K, V>
where
    K: Eq + Hash + Clone,
{
    fn new(ttl: Duration, capacity: usize) -> Self {
        Self {
            ttl,
            capacity,
            next_seq: 0,
            map: HashMap::new(),
        }
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.map.len()
    }

    /// Insert or replace `key`. Capacity 0 stores nothing. At capacity, a new
    /// key evicts the oldest insertion. Replacing an existing key refreshes
    /// its timestamp and insertion order.
    fn insert_at(&mut self, key: K, value: V, now: Instant) {
        if self.capacity == 0 {
            return;
        }

        // Do not let expired entries occupy capacity merely because their
        // individual keys have not been queried again.
        self.map.retain(|_, entry| {
            now.checked_duration_since(entry.inserted_at)
                .unwrap_or(Duration::ZERO)
                < self.ttl
        });

        if self.map.contains_key(&key) {
            let seq = self.alloc_seq();
            // Key present: refresh value, timestamp, and insertion order.
            let entry = self.map.get_mut(&key).expect("contains_key just true");
            entry.value = value;
            entry.inserted_at = now;
            entry.seq = seq;
            return;
        }

        while self.map.len() >= self.capacity {
            let oldest_key = self
                .map
                .iter()
                .min_by_key(|(_, entry)| entry.seq)
                .map(|(k, _)| k.clone());
            match oldest_key {
                Some(k) => {
                    self.map.remove(&k);
                }
                None => break,
            }
        }

        let seq = self.alloc_seq();
        self.map.insert(
            key,
            TimedCacheEntry {
                value,
                inserted_at: now,
                seq,
            },
        );
    }

    /// Clone a fresh value for `key`. Removes the entry when its age is
    /// greater than or equal to TTL. If `now` is earlier than insertion, age is
    /// treated as zero (still fresh).
    fn get_cloned_at(&mut self, key: &K, now: Instant) -> Option<V>
    where
        V: Clone,
    {
        let expired = match self.map.get(key) {
            Some(entry) => {
                let age = now
                    .checked_duration_since(entry.inserted_at)
                    .unwrap_or(Duration::ZERO);
                age >= self.ttl
            }
            None => return None,
        };

        if expired {
            self.map.remove(key);
            None
        } else {
            self.map.get(key).map(|entry| entry.value.clone())
        }
    }

    /// Remove `key` only when `pred` accepts the stored value. Used to drop a
    /// stale plan without clobbering a concurrently refreshed entry.
    fn remove_if<F>(&mut self, key: &K, pred: F) -> bool
    where
        F: FnOnce(&V) -> bool,
    {
        let should_remove = match self.map.get(key) {
            Some(entry) => pred(&entry.value),
            None => return false,
        };
        if should_remove {
            self.map.remove(key);
            true
        } else {
            false
        }
    }

    fn alloc_seq(&mut self) -> u64 {
        let seq = self.next_seq;
        self.next_seq = self.next_seq.wrapping_add(1);
        seq
    }
}

struct SecureCapturePath {
    directory: std::path::PathBuf,
    file: std::path::PathBuf,
}

impl SecureCapturePath {
    fn new(file_name: &str) -> anyhow::Result<Self> {
        use std::os::unix::fs::DirBuilderExt;

        let directory = std::env::temp_dir().join(format!(
            "cua-driver-rs-capture-{}-{}",
            std::process::id(),
            uuid::Uuid::new_v4()
        ));
        std::fs::DirBuilder::new().mode(0o700).create(&directory)?;
        let file = directory.join(file_name);
        Ok(Self { directory, file })
    }
}

impl Drop for SecureCapturePath {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.file);
        let _ = std::fs::remove_dir(&self.directory);
    }
}

/// An explicit window capture refused or failed. Keep the original error
/// chain, while preventing an unverified backend from reintroducing implicit
/// window-group composition. The marker is internal, not a public error spec.
#[derive(Debug)]
struct UnverifiedWindowFallback;

impl std::fmt::Display for UnverifiedWindowFallback {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("explicit window capture failed; unverified shell composition is disabled")
    }
}

impl std::error::Error for UnverifiedWindowFallback {}

fn prohibit_unverified_window_fallback(error: anyhow::Error) -> anyhow::Error {
    error.context(UnverifiedWindowFallback)
}

/// Prefer `native`; only unmarked native errors/empty output allow `fallback`.
///
/// On non-empty native success, returns those bytes without invoking
/// fallback. When both paths fail, the error message preserves both
/// contexts. Closures are not required to be `Send`/`Sync`.
fn capture_window_with_backends<N, F>(
    window_id: u32,
    native: N,
    fallback: F,
) -> anyhow::Result<Vec<u8>>
where
    N: FnOnce(u32) -> anyhow::Result<Vec<u8>>,
    F: FnOnce(u32) -> anyhow::Result<Vec<u8>>,
{
    match native(window_id) {
        Ok(bytes) if !bytes.is_empty() => Ok(bytes),
        Ok(_) => match fallback(window_id) {
            Ok(bytes) => Ok(bytes),
            Err(fallback_err) => Err(anyhow::anyhow!(
                "window {window_id} capture failed: native produced empty bytes; \
                 shell fallback: {fallback_err:#}"
            )),
        },
        Err(native_err) => {
            if native_err.is::<UnverifiedWindowFallback>() {
                return Err(native_err);
            }
            tracing::debug!(target: "cua_capture_geometry", window_id, error = %native_err,
                "Native window capture unavailable; trying compatibility capture");
            match fallback(window_id) {
                Ok(bytes) => Ok(bytes),
                Err(fallback_err) => Err(anyhow::anyhow!(
                    "window {window_id} capture failed: native: {native_err:#}; \
                     shell fallback: {fallback_err:#}"
                )),
            }
        }
    }
}

/// Shell compatibility path: `screencapture -l <id> -x -o <tmp.png>`.
fn screenshot_window_bytes_shell(window_id: u32) -> anyhow::Result<Vec<u8>> {
    let capture = SecureCapturePath::new("window.png")?;
    let tmp_path = capture.file.to_string_lossy().into_owned();

    let output = Command::new("screencapture")
        .args([
            "-l",
            &window_id.to_string(),
            "-x", // no sound
            "-o", // no shadow
            &tmp_path,
        ])
        .output()?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        if stderr.is_empty() {
            anyhow::bail!(
                "screencapture failed for window {window_id} with status {}",
                output.status
            );
        }
        anyhow::bail!(
            "screencapture failed for window {window_id} with status {}: {stderr}",
            output.status
        );
    }

    let bytes = std::fs::read(&capture.file)?;

    if bytes.is_empty() {
        anyhow::bail!("screencapture produced empty output for window {window_id}");
    }
    Ok(bytes)
}

/// Hard ceiling on capture dimensions to avoid unbounded allocations.
const MAX_CAPTURE_DIM: u32 = 16384;

fn window_frame_usable(rect: screencapturekit::cg::CGRect) -> bool {
    let w = rect.size.width;
    let h = rect.size.height;
    rect.origin.x.is_finite()
        && rect.origin.y.is_finite()
        && w.is_finite()
        && h.is_finite()
        && w > 0.0
        && h > 0.0
}

/// Round a positive finite pixel extent into `1..=MAX_CAPTURE_DIM` as `u32`.
fn rounded_pixel_dim(value: f64, label: &str) -> anyhow::Result<u32> {
    if !value.is_finite() || value <= 0.0 {
        anyhow::bail!("invalid capture {label}: {value}");
    }
    let rounded = value.round();
    if !(rounded.is_finite()) || rounded < 1.0 || rounded > f64::from(MAX_CAPTURE_DIM) {
        anyhow::bail!("capture {label} {rounded} out of allowed range 1..={MAX_CAPTURE_DIM}");
    }
    // After the range check the value fits in u32.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let dim = rounded as u32;
    if dim == 0 || dim > MAX_CAPTURE_DIM {
        anyhow::bail!("capture {label} {dim} out of allowed range 1..={MAX_CAPTURE_DIM}");
    }
    Ok(dim)
}

fn checked_image_dim(value: usize, label: &str) -> anyhow::Result<u32> {
    if value == 0 || value > MAX_CAPTURE_DIM as usize {
        anyhow::bail!("{label} {value} out of allowed range 1..={MAX_CAPTURE_DIM}");
    }
    u32::try_from(value).map_err(|_| anyhow::anyhow!("{label} {value} does not fit u32"))
}

/// Owned ScreenCaptureKit filter + stream config for one window id.
struct WindowCapturePlan {
    filter: screencapturekit::prelude::SCContentFilter,
    config: screencapturekit::prelude::SCStreamConfiguration,
    binding: WindowCaptureBinding,
    pixel_scale: f64,
}

/// Cheap WindowServer fingerprint used to reject a cached filter after a
/// resize/move, owner change, layer change, or CGWindowID reuse. Float fields
/// are kept as their exact bit patterns because both CGWindowList and
/// ScreenCaptureKit report the same WindowServer frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct WindowCaptureIdentity {
    pid: i32,
    layer: i32,
    x: u64,
    y: u64,
    width: u64,
    height: u64,
}

impl WindowCaptureIdentity {
    fn new(pid: i32, layer: i32, x: f64, y: f64, width: f64, height: f64) -> Self {
        Self {
            pid,
            layer,
            x: x.to_bits(),
            y: y.to_bits(),
            width: width.to_bits(),
            height: height.to_bits(),
        }
    }

    fn frame(self) -> screencapturekit::cg::CGRect {
        screencapturekit::cg::CGRect::new(
            f64::from_bits(self.x),
            f64::from_bits(self.y),
            f64::from_bits(self.width),
            f64::from_bits(self.height),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SelectedCaptureWindow {
    window_id: u32,
    identity: WindowCaptureIdentity,
    is_on_screen: bool,
}

impl SelectedCaptureWindow {
    fn from_info(window: &crate::windows::WindowInfo) -> Self {
        Self {
            window_id: window.window_id,
            identity: WindowCaptureIdentity::new(
                window.pid,
                window.layer,
                window.bounds.x,
                window.bounds.y,
                window.bounds.width,
                window.bounds.height,
            ),
            is_on_screen: window.is_on_screen,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct WindowCaptureSelection {
    target: SelectedCaptureWindow,
    // Complete positively discovered set, including surfaces outside the crop.
    // These must still be revalidated if they move into the crop during capture.
    attachments: Vec<SelectedCaptureWindow>,
    discovery_usable: bool,
}

impl WindowCaptureSelection {
    fn render_windows(&self) -> Vec<&SelectedCaptureWindow> {
        let mut selected = vec![&self.target];
        selected.extend(self.attachments.iter().filter(|window| {
            capture_frames_intersect(self.target.identity.frame(), window.identity.frame())
        }));
        selected
    }

    fn can_cache(&self) -> bool {
        self.discovery_usable && self.attachments.is_empty()
    }
}

fn capture_frames_intersect(
    a: screencapturekit::cg::CGRect,
    b: screencapturekit::cg::CGRect,
) -> bool {
    window_frame_usable(a)
        && window_frame_usable(b)
        && a.origin.x.max(b.origin.x) < (a.origin.x + a.size.width).min(b.origin.x + b.size.width)
        && a.origin.y.max(b.origin.y) < (a.origin.y + a.size.height).min(b.origin.y + b.size.height)
}

fn capture_frame_contains(
    outer: screencapturekit::cg::CGRect,
    inner: screencapturekit::cg::CGRect,
) -> bool {
    window_frame_usable(outer)
        && window_frame_usable(inner)
        && outer.origin.x <= inner.origin.x
        && outer.origin.y <= inner.origin.y
        && outer.origin.x + outer.size.width >= inner.origin.x + inner.size.width
        && outer.origin.y + outer.size.height >= inner.origin.y + inner.size.height
}

fn capture_selection_from_snapshot(
    window_id: u32,
    windows: &[crate::windows::WindowInfo],
    attachment_ids: &[u32],
    discovery_usable: bool,
) -> anyhow::Result<WindowCaptureSelection> {
    let unique = |id| -> anyhow::Result<SelectedCaptureWindow> {
        let mut matches = windows.iter().filter(|window| window.window_id == id);
        let window = matches
            .next()
            .ok_or_else(|| anyhow::anyhow!("WindowServer no longer lists selected window {id}"))?;
        if matches.next().is_some() || id == 0 || window.pid <= 0 {
            anyhow::bail!("WindowServer identity is ambiguous for selected window {id}");
        }
        let selected = SelectedCaptureWindow::from_info(window);
        let frame = selected.identity.frame();
        if !window_frame_usable(frame)
            || !(frame.origin.x + frame.size.width).is_finite()
            || !(frame.origin.y + frame.size.height).is_finite()
        {
            anyhow::bail!("WindowServer frame is invalid for selected window {id}");
        }
        Ok(selected)
    };
    let target = unique(window_id)?;
    let mut ids = attachment_ids.to_vec();
    ids.sort_unstable();
    if ids.contains(&window_id)
        || ids.windows(2).any(|pair| pair[0] == pair[1])
        || (!discovery_usable && !ids.is_empty())
    {
        anyhow::bail!("Invalid explicit attachment set for window {window_id}");
    }
    let attachments = ids
        .into_iter()
        .map(|id| {
            let selected = unique(id)?;
            if selected.identity.pid != target.identity.pid {
                anyhow::bail!("Attached window {id} no longer belongs to the target process");
            }
            Ok(selected)
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    Ok(WindowCaptureSelection {
        target,
        attachments,
        discovery_usable,
    })
}

fn current_window_capture_selection(window_id: u32) -> anyhow::Result<WindowCaptureSelection> {
    let snapshot = crate::windows::all_windows_including_accessory_layers_with_snapshot();
    if !snapshot.succeeded {
        anyhow::bail!("WindowServer capture identity snapshot failed");
    }
    // Prove the target before making AX queries for its process. This same raw
    // snapshot is passed to bounded attachment discovery; no same-PID grouping.
    let target = capture_selection_from_snapshot(window_id, &snapshot.windows, &[], false)?;
    let (ids, discovery_usable) = match attachments::attached_window_ids(
        target.target.identity.pid,
        window_id,
        &snapshot.windows,
    ) {
        Ok(ids) => (ids, true),
        Err(reason) => {
            tracing::debug!(target: "cua_capture_geometry", window_id, ?reason,
                "Attachment discovery unavailable; using exact independent surface, discovery is not complete");
            (Vec::new(), false)
        }
    };
    capture_selection_from_snapshot(window_id, &snapshot.windows, &ids, discovery_usable)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CaptureDisplayIdentity {
    display_id: u32,
    x: u64,
    y: u64,
    width: u64,
    height: u64,
    scale: u64,
}

impl CaptureDisplayIdentity {
    fn new(
        display_id: u32,
        frame: screencapturekit::cg::CGRect,
        scale: f64,
    ) -> anyhow::Result<Self> {
        if display_id == 0
            || !window_frame_usable(frame)
            || !(frame.origin.x + frame.size.width).is_finite()
            || !(frame.origin.y + frame.size.height).is_finite()
            || !scale.is_finite()
            || scale <= 0.0
        {
            anyhow::bail!("Invalid active display identity for explicit window capture");
        }
        Ok(Self {
            display_id,
            x: frame.origin.x.to_bits(),
            y: frame.origin.y.to_bits(),
            width: frame.size.width.to_bits(),
            height: frame.size.height.to_bits(),
            scale: scale.to_bits(),
        })
    }

    fn frame(self) -> screencapturekit::cg::CGRect {
        screencapturekit::cg::CGRect::new(
            f64::from_bits(self.x),
            f64::from_bits(self.y),
            f64::from_bits(self.width),
            f64::from_bits(self.height),
        )
    }

    fn scale(self) -> f64 {
        f64::from_bits(self.scale)
    }
}

fn active_capture_displays() -> anyhow::Result<Vec<CaptureDisplayIdentity>> {
    use core_graphics::display::{CGDisplay, CGGetActiveDisplayList};
    let mut count = 0;
    // Bound the list before allocating. Never substitute the main/first display
    // when enumeration fails or a mirrored/overlapping layout is ambiguous.
    if unsafe { CGGetActiveDisplayList(0, std::ptr::null_mut(), &mut count) } != 0
        || count == 0
        || count > 32
    {
        anyhow::bail!("Active display enumeration is unavailable or exceeds capture bound");
    }
    let mut ids = [0_u32; 32];
    if unsafe { CGGetActiveDisplayList(32, ids.as_mut_ptr(), &mut count) } != 0
        || count == 0
        || count > 32
    {
        anyhow::bail!("Active display enumeration changed during capture preparation");
    }
    let mut result = Vec::with_capacity(count as usize);
    for id in &ids[..count as usize] {
        if result
            .iter()
            .any(|display: &CaptureDisplayIdentity| display.display_id == *id)
        {
            anyhow::bail!("Active display list contains duplicate identities");
        }
        let display = CGDisplay::new(*id);
        if !display.is_active() {
            anyhow::bail!("Selected display is no longer active");
        }
        let mode = display
            .display_mode()
            .ok_or_else(|| anyhow::anyhow!("Active display has no current mode"))?;
        let (width, height) = (mode.width(), mode.height());
        if width == 0 || height == 0 {
            anyhow::bail!("Active display mode has invalid dimensions");
        }
        let sx = mode.pixel_width() as f64 / width as f64;
        let sy = mode.pixel_height() as f64 / height as f64;
        if !sx.is_finite() || !sy.is_finite() || (sx - sy).abs() > 0.000_001 {
            anyhow::bail!("Active display backing scale is ambiguous");
        }
        let frame = display.bounds();
        result.push(CaptureDisplayIdentity::new(
            *id,
            screencapturekit::cg::CGRect::new(
                frame.origin.x,
                frame.origin.y,
                frame.size.width,
                frame.size.height,
            ),
            sx,
        )?);
    }
    Ok(result)
}

fn select_capture_display(
    selection: &WindowCaptureSelection,
    displays: &[CaptureDisplayIdentity],
) -> anyhow::Result<Option<CaptureDisplayIdentity>> {
    let render = selection.render_windows();
    if render.len() == 1 {
        return Ok(None);
    }
    if render.iter().any(|window| !window.is_on_screen) {
        anyhow::bail!("Explicit attached-window composition requires on-screen selected surfaces");
    }
    let target = selection.target.identity.frame();
    let mut containing = displays
        .iter()
        .filter(|display| capture_frame_contains(display.frame(), target));
    let chosen = containing.next().copied().ok_or_else(|| {
        anyhow::anyhow!(
            "No single active display fully contains the target crop for explicit attachments"
        )
    })?;
    if containing.next().is_some() {
        anyhow::bail!("Multiple active displays contain the target crop; composition is ambiguous");
    }
    // The attachment itself may extend beyond host/display. Only its
    // intersection with the unchanged host crop is rendered. Geometry here
    // constrains pixels; positive AX discovery, not intersection, admits IDs.
    Ok(Some(chosen))
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct WindowCaptureBinding {
    selection: WindowCaptureSelection,
    display: Option<CaptureDisplayIdentity>,
}

fn current_window_capture_binding(window_id: u32) -> anyhow::Result<WindowCaptureBinding> {
    let selection = current_window_capture_selection(window_id)?;
    let display = if selection.render_windows().len() > 1 {
        select_capture_display(&selection, &active_capture_displays()?)?
    } else {
        None
    };
    Ok(WindowCaptureBinding { selection, display })
}

fn capture_plan_is_reusable(plan: &WindowCaptureBinding, live: &WindowCaptureBinding) -> bool {
    plan == live && live.selection.can_cache() && live.display.is_none()
}

fn window_capture_configuration(
    width: u32,
    height: u32,
    target: screencapturekit::cg::CGRect,
    display: Option<CaptureDisplayIdentity>,
) -> screencapturekit::prelude::SCStreamConfiguration {
    let mut config = screencapturekit::prelude::SCStreamConfiguration::new()
        .with_width(width)
        .with_height(height)
        .with_includes_child_windows(false)
        .with_shows_cursor(false)
        .with_minimum_frame_interval(&screencapturekit::cm::CMTime::new(1, 5));
    if let Some(display) = display {
        let frame = display.frame();
        config = config.with_ignores_shadows_display(true);
        // Display sourceRect is relative to its selected display; preserve
        // the target's full extent rather than fitting a host/popup union.
        config.set_source_rect(screencapturekit::cg::CGRect::new(
            target.origin.x - frame.origin.x,
            target.origin.y - frame.origin.y,
            target.size.width,
            target.size.height,
        ));
    } else {
        config = config.with_ignores_shadows_single_window(true);
        // Exact physical popovers must keep the default independent extent:
        // an explicit sourceRect can produce -3811/-3812 or empty pixels.
    }
    config
}

fn capture_rect_matches(
    actual: screencapturekit::cg::CGRect,
    expected: screencapturekit::cg::CGRect,
) -> bool {
    // Metadata crosses a float32 system boundary. Allow subpixel rounding,
    // never the hundreds of pixels of padding observed in H058.
    let close = |a: f64, b: f64| a.is_finite() && b.is_finite() && (a - b).abs() <= 0.25;
    window_frame_usable(actual)
        && window_frame_usable(expected)
        && close(actual.origin.x, expected.origin.x)
        && close(actual.origin.y, expected.origin.y)
        && close(actual.size.width, expected.size.width)
        && close(actual.size.height, expected.size.height)
}

fn validate_window_capture_geometry(
    frame: screencapturekit::cg::CGRect,
    width: u32,
    height: u32,
    info: &screencapturekit::cm::FrameInfo,
) -> anyhow::Result<()> {
    use screencapturekit::cm::SCFrameStatus;
    let local = screencapturekit::cg::CGRect::new(0.0, 0.0, frame.size.width, frame.size.height);
    let scale = info
        .scale_factor
        .filter(|scale| scale.is_finite() && *scale > 0.0);
    let unscaled = info
        .content_scale
        .is_some_and(|scale| scale.is_finite() && (scale - 1.0).abs() <= 0.000_001);
    let dimensions_match = scale.is_some_and(|scale| {
        (f64::from(width) - frame.size.width * scale).abs() <= 1.0
            && (f64::from(height) - frame.size.height * scale).abs() <= 1.0
    });
    if info.frame_status != Some(SCFrameStatus::Complete)
        || !unscaled
        || !dimensions_match
        || !info
            .screen_rect
            .is_some_and(|rect| capture_rect_matches(rect, frame))
        || !info
            .content_rect
            .is_some_and(|rect| capture_rect_matches(rect, local))
        || !info
            .bounding_rect
            .is_some_and(|rect| capture_rect_matches(rect, local))
    {
        anyhow::bail!(
            "ScreenCaptureKit frame geometry does not match the exact window: \
             expected {frame:?} at {width}x{height}, actual {info:?}"
        );
    }
    Ok(())
}

fn frame_status_from_attachment(
    value: &core_foundation::base::CFType,
) -> Option<screencapturekit::cm::SCFrameStatus> {
    use core_foundation::number::CFNumber;
    let raw = value.downcast::<CFNumber>()?.to_i64()?;
    screencapturekit::cm::SCFrameStatus::from_raw(i32::try_from(raw).ok()?)
}

fn window_frame_status(
    sample: &screencapturekit::cm::CMSampleBuffer,
) -> Option<screencapturekit::cm::SCFrameStatus> {
    use core_foundation::array::{CFArray, CFArrayRef};
    use core_foundation::base::{CFType, TCFType};
    use core_foundation::dictionary::CFDictionary;
    use core_foundation::string::{CFString, CFStringRef};
    #[link(name = "CoreMedia", kind = "framework")]
    extern "C" {
        fn CMSampleBufferGetSampleAttachmentsArray(
            sample: *const std::ffi::c_void,
            create_if_necessary: bool,
        ) -> CFArrayRef;
    }
    #[link(name = "ScreenCaptureKit", kind = "framework")]
    extern "C" {
        static SCStreamFrameInfoStatus: CFStringRef;
    }
    // Apple's attachment is an NSNumber containing SCFrameStatus.rawValue.
    // screencapturekit 6.0.1 casts the value to the Swift enum itself, which
    // fails on actual macOS frames and silently drops the complete status.
    // Read the typed number through the exported SDK key; never default an
    // absent or malformed status to Complete.
    unsafe {
        let raw = CMSampleBufferGetSampleAttachmentsArray(sample.as_ptr(), false);
        if raw.is_null() {
            return None;
        }
        let attachments = CFArray::<CFType>::wrap_under_get_rule(raw);
        let first = attachments.get(0)?;
        let dictionary = first.downcast::<CFDictionary>()?;
        let key = CFString::wrap_under_get_rule(SCStreamFrameInfoStatus);
        let value = dictionary.find(key.as_CFTypeRef())?;
        if value.is_null() {
            return None;
        }
        let value = CFType::wrap_under_get_rule(*value);
        frame_status_from_attachment(&value)
    }
}

fn capture_complete_window_frame(
    filter: &screencapturekit::prelude::SCContentFilter,
    config: &screencapturekit::prelude::SCStreamConfiguration,
) -> anyhow::Result<screencapturekit::cm::CMSampleBuffer> {
    use screencapturekit::cm::SCFrameStatus;
    use screencapturekit::prelude::{SCStream, SCStreamOutputType};
    let (sender, receiver) = mpsc::sync_channel(1);
    let first_frame = AtomicBool::new(false);
    let mut stream = SCStream::new(filter, config);
    let handler = stream
        .add_output_handler(
            move |sample: screencapturekit::cm::CMSampleBuffer, output_type| {
                if output_type == SCStreamOutputType::Screen
                    && window_frame_status(&sample) == Some(SCFrameStatus::Complete)
                    && !first_frame.swap(true, Ordering::AcqRel)
                {
                    let _ = sender.try_send(sample);
                }
            },
            SCStreamOutputType::Screen,
        )
        .ok_or_else(|| anyhow::anyhow!("ScreenCaptureKit rejected window frame output"))?;
    stream
        .start_capture()
        .map_err(|error| anyhow::anyhow!("ScreenCaptureKit window stream start failed: {error}"))?;
    let sample = receiver.recv_timeout(Duration::from_secs(1));
    // Stop on both success and timeout. The outer worker gate also bounds
    // a hung Apple callback and prevents accumulation of capture workers.
    let stopped = stream.stop_capture();
    stream.remove_output_handler(handler, SCStreamOutputType::Screen);
    stopped
        .map_err(|error| anyhow::anyhow!("ScreenCaptureKit window stream stop failed: {error}"))?;
    sample.map_err(|error| {
        anyhow::anyhow!("ScreenCaptureKit complete window frame unavailable: {error}")
    })
}

const WINDOW_PLAN_CACHE_TTL: Duration = Duration::from_secs(2);
const WINDOW_PLAN_CACHE_CAPACITY: usize = 32;
/// Keep native capture below the public observation deadline after the AX
/// walk's own 20-second bound. Explicit capture errors remain visible.
const WINDOW_CAPTURE_NATIVE_TIMEOUT: Duration = Duration::from_secs(3);

/// Permit at most one ScreenCaptureKit worker. If an Apple completion callback
/// never fires, the timed-out worker keeps this permit, and every later request
/// is refused instead of leaking more blocked threads.
struct NativeCaptureGate {
    active: AtomicBool,
}

impl NativeCaptureGate {
    const fn new() -> Self {
        Self {
            active: AtomicBool::new(false),
        }
    }

    fn try_acquire(&'static self) -> Option<NativeCapturePermit> {
        self.active
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .ok()
            .map(|_| NativeCapturePermit { gate: self })
    }
}

struct NativeCapturePermit {
    gate: &'static NativeCaptureGate,
}

impl Drop for NativeCapturePermit {
    fn drop(&mut self) {
        self.gate.active.store(false, Ordering::Release);
    }
}

fn native_capture_gate() -> &'static NativeCaptureGate {
    static GATE: NativeCaptureGate = NativeCaptureGate::new();
    &GATE
}

fn run_native_capture_worker<T, F>(
    gate: &'static NativeCaptureGate,
    timeout: Duration,
    work: F,
) -> anyhow::Result<T>
where
    T: Send + 'static,
    F: FnOnce() -> anyhow::Result<T> + Send + 'static,
{
    let permit = gate
        .try_acquire()
        .ok_or_else(|| anyhow::anyhow!("ScreenCaptureKit capture already in flight"))?;
    let (sender, receiver) = mpsc::sync_channel(1);
    std::thread::Builder::new()
        .name("cua-sck-window-capture".into())
        .spawn(move || {
            let result = work();
            drop(permit);
            let _ = sender.send(result);
        })
        .map_err(|error| anyhow::anyhow!("failed to start ScreenCaptureKit worker: {error}"))?;

    match receiver.recv_timeout(timeout) {
        Ok(result) => result,
        Err(mpsc::RecvTimeoutError::Timeout) => {
            anyhow::bail!(
                "ScreenCaptureKit capture timed out after {} ms",
                timeout.as_millis()
            )
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            anyhow::bail!("ScreenCaptureKit worker ended without a result")
        }
    }
}

fn window_plan_cache() -> &'static Mutex<TimedCache<u32, std::sync::Arc<WindowCapturePlan>>> {
    static CACHE: OnceLock<Mutex<TimedCache<u32, std::sync::Arc<WindowCapturePlan>>>> =
        OnceLock::new();
    CACHE.get_or_init(|| {
        Mutex::new(TimedCache::new(
            WINDOW_PLAN_CACHE_TTL,
            WINDOW_PLAN_CACHE_CAPACITY,
        ))
    })
}

fn lock_window_plan_cache(
) -> std::sync::MutexGuard<'static, TimedCache<u32, std::sync::Arc<WindowCapturePlan>>> {
    window_plan_cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// Resolve only explicitly selected SCWindow objects. The display builder must
/// include this exact list; an empty/excluding filter would capture unrelated
/// desktop pixels. Runs outside the cache lock.
fn build_window_capture_plan(
    window_id: u32,
    expected: &WindowCaptureBinding,
) -> anyhow::Result<std::sync::Arc<WindowCapturePlan>> {
    use screencapturekit::prelude::{SCContentFilter, SCShareableContent};

    let content = SCShareableContent::get()
        .map_err(|error| anyhow::anyhow!("SCShareableContent::get failed: {error}"))?;
    let windows = content.windows();
    let render = expected.selection.render_windows();
    let mut selected = Vec::with_capacity(render.len());
    for wanted in &render {
        let mut matching = windows
            .iter()
            .filter(|window| window.window_id() == wanted.window_id);
        let window = matching.next().ok_or_else(|| {
            anyhow::anyhow!(
                "ScreenCaptureKit no longer lists selected window {}",
                wanted.window_id
            )
        })?;
        if matching.next().is_some() {
            anyhow::bail!("ScreenCaptureKit selected window identity is ambiguous");
        }
        let frame = window.frame();
        let owner = window
            .owning_application()
            .ok_or_else(|| anyhow::anyhow!("ScreenCaptureKit selected window has no owner"))?;
        let actual = WindowCaptureIdentity::new(
            owner.process_id(),
            window.window_layer(),
            frame.origin.x,
            frame.origin.y,
            frame.size.width,
            frame.size.height,
        );
        if actual != wanted.identity || window.is_on_screen() != wanted.is_on_screen {
            anyhow::bail!(
                "ScreenCaptureKit selected window {} changed identity during preparation",
                wanted.window_id
            );
        }
        selected.push(window);
    }
    let mut filter = if let Some(display_identity) = expected.display {
        if selected.len() < 2 {
            anyhow::bail!("Explicit display composition has no in-crop attachment");
        }
        let displays = content.displays();
        let mut matches = displays
            .iter()
            .filter(|display| display.display_id() == display_identity.display_id);
        let display = matches
            .next()
            .ok_or_else(|| anyhow::anyhow!("ScreenCaptureKit selected display is absent"))?;
        if matches.next().is_some()
            || !capture_rect_matches(display.frame(), display_identity.frame())
        {
            anyhow::bail!("ScreenCaptureKit selected display changed geometry or identity");
        }
        SCContentFilter::create()
            .with_display(display)
            .with_including_windows(&selected)
            .build()
    } else {
        if selected.len() != 1 {
            anyhow::bail!("Explicit attachments have no verified display crop");
        }
        SCContentFilter::create().with_window(selected[0]).build()
    };
    filter.set_include_menu_bar(false);
    let scale = f64::from(filter.point_pixel_scale());
    let frame = expected.selection.target.identity.frame();
    if let Some(display) = expected.display {
        if !capture_rect_matches(filter.content_rect(), display.frame())
            || !scale.is_finite()
            || (scale - display.scale()).abs() > 0.000_001
        {
            anyhow::bail!("ScreenCaptureKit explicit display bounds/backing scale disagree with current display");
        }
    }
    let out_w = rounded_pixel_dim(frame.size.width * scale, "width")?;
    let out_h = rounded_pixel_dim(frame.size.height * scale, "height")?;
    let config = window_capture_configuration(out_w, out_h, frame, expected.display);
    tracing::debug!(target: "cua_capture_geometry", window_id,
        selected_window_ids = ?render.iter().map(|window| window.window_id).collect::<Vec<_>>(),
        discovered_attachment_count = expected.selection.attachments.len(),
        display_id = ?expected.display.map(|display| display.display_id),
        "Built explicit window capture with native child composition disabled");
    Ok(std::sync::Arc::new(WindowCapturePlan {
        filter,
        config,
        binding: expected.clone(),
        pixel_scale: scale,
    }))
}

/// Capture one complete frame, verify its actual mapping, and encode RGBA/PNG.
fn capture_window_from_plan(window_id: u32, plan: &WindowCapturePlan) -> anyhow::Result<Vec<u8>> {
    use screencapturekit::cm::{CMSampleBufferExt, CMSampleBufferSCExt};
    use screencapturekit::screenshot_manager::CGImageExt;

    let source = plan.config.source_rect();
    let content = plan.filter.content_rect();
    tracing::debug!(target: "cua_capture_geometry", window_id,
        planned_children = false,
        configured_children = plan.config.includes_child_windows(),
        source_x = source.origin.x, source_y = source.origin.y,
        source_width = source.size.width, source_height = source.size.height,
        content_x = content.origin.x, content_y = content.origin.y,
        content_width = content.size.width, content_height = content.size.height,
        output_width = plan.config.width(), output_height = plan.config.height(),
        "Capturing exact window with ScreenCaptureKit configuration");
    let sample = capture_complete_window_frame(&plan.filter, &plan.config)?;
    let mut info = sample.frame_info().ok_or_else(|| {
        anyhow::anyhow!("ScreenCaptureKit omitted frame geometry for window {window_id}")
    })?;
    info.frame_status = window_frame_status(&sample);
    let image = sample.cg_image().map_err(|error| {
        anyhow::anyhow!("ScreenCaptureKit frame image failed for window {window_id}: {error}")
    })?;

    let w = checked_image_dim(image.width(), "CGImage width")?;
    let h = checked_image_dim(image.height(), "CGImage height")?;
    validate_window_capture_geometry(plan.binding.selection.target.identity.frame(), w, h, &info)?;
    if !info
        .scale_factor
        .is_some_and(|scale| (scale - plan.pixel_scale).abs() <= 0.000_001)
    {
        anyhow::bail!("ScreenCaptureKit complete-frame scale changed during capture");
    }
    tracing::debug!(target: "cua_capture_geometry", window_id, ?info,
        "Verified complete window frame geometry; explicit identities remain to be rechecked");

    let rgba = image
        .rgba_data()
        .map_err(|e| anyhow::anyhow!("CGImage::rgba_data failed for window {window_id}: {e}"))?;

    let expected_len = (w as u64)
        .checked_mul(h as u64)
        .and_then(|n| n.checked_mul(4))
        .ok_or_else(|| anyhow::anyhow!("RGBA byte length overflow for {w}x{h}"))?;
    if rgba.len() as u64 != expected_len {
        anyhow::bail!(
            "CGImage RGBA length {} != {w}*{h}*4 ({expected_len}) for window {window_id}",
            rgba.len()
        );
    }

    cua_driver_core::image_utils::encode_rgba_to_png(&rgba, w, h)
}

enum CaptureIdentityValidation<T> {
    Matched(Vec<u8>),
    Changed(T),
}

/// Do not release bytes until every physical identity, discovered attachment
/// and display/crop binding still matches. The injected form exercises races
/// without relying on native timing in unit tests.
fn capture_then_validate_identity<C, I, T>(
    expected_identity: T,
    capture: C,
    current_identity: I,
) -> anyhow::Result<CaptureIdentityValidation<T>>
where
    C: FnOnce() -> anyhow::Result<Vec<u8>>,
    I: FnOnce() -> anyhow::Result<T>,
    T: PartialEq,
{
    let bytes = capture()?;
    let actual_identity = current_identity()?;
    if actual_identity == expected_identity {
        Ok(CaptureIdentityValidation::Matched(bytes))
    } else {
        Ok(CaptureIdentityValidation::Changed(actual_identity))
    }
}

fn capture_window_from_plan_validated(
    window_id: u32,
    plan: &WindowCapturePlan,
) -> anyhow::Result<CaptureIdentityValidation<WindowCaptureBinding>> {
    capture_then_validate_identity(
        plan.binding.clone(),
        || capture_window_from_plan(window_id, plan),
        || current_window_capture_binding(window_id),
    )
}

fn evict_window_capture_plan(window_id: u32, plan: &std::sync::Arc<WindowCapturePlan>) {
    lock_window_plan_cache().remove_if(&window_id, |stored| std::sync::Arc::ptr_eq(stored, plan));
}

/// Single-frame capture, with at most one rebuild after a changed binding or
/// a failed warm plan. A fresh native failure is not replayed. All discovery,
/// build, frame and revalidation work stays inside the existing three-second
/// worker, whose permit remains owned until a blocked native call returns.
fn screenshot_window_bytes_sck_inner(window_id: u32) -> anyhow::Result<Vec<u8>> {
    let mut binding = current_window_capture_binding(window_id)?;
    let mut retry_available = true;
    loop {
        let cached = lock_window_plan_cache().get_cloned_at(&window_id, Instant::now());
        let reusable = cached.filter(|plan| {
            if capture_plan_is_reusable(&plan.binding, &binding) {
                true
            } else {
                evict_window_capture_plan(window_id, plan);
                false
            }
        });
        let was_cached = reusable.is_some();
        let plan = match reusable {
            Some(plan) => plan,
            None => {
                let plan = build_window_capture_plan(window_id, &binding)?;
                if binding.selection.can_cache() && binding.display.is_none() {
                    lock_window_plan_cache().insert_at(
                        window_id,
                        std::sync::Arc::clone(&plan),
                        Instant::now(),
                    );
                }
                plan
            }
        };
        match capture_window_from_plan_validated(window_id, &plan) {
            Ok(CaptureIdentityValidation::Matched(bytes)) => return Ok(bytes),
            Ok(CaptureIdentityValidation::Changed(current)) => {
                evict_window_capture_plan(window_id, &plan);
                if !retry_available {
                    anyhow::bail!(
                        "ScreenCaptureKit explicit window binding changed again during retry"
                    );
                }
                binding = current;
                retry_available = false;
            }
            Err(error) => {
                evict_window_capture_plan(window_id, &plan);
                if !was_cached || !retry_available {
                    return Err(error);
                }
                tracing::debug!(target: "cua_capture_geometry", window_id, error = %error,
                    "Discarding failed warm plan; rebuilding once with fresh attachment discovery");
                binding = current_window_capture_binding(window_id)?;
                retry_available = false;
            }
        }
    }
}

/// Preserve typed refusal and source context across the worker boundary. A
/// timeout also cannot fall back: the timed-out worker may still own a capture
/// of a formerly attached surface, and shell composition is not verified.
fn screenshot_window_bytes_sck(window_id: u32) -> anyhow::Result<Vec<u8>> {
    run_native_capture_worker(
        native_capture_gate(),
        WINDOW_CAPTURE_NATIVE_TIMEOUT,
        move || screenshot_window_bytes_sck_inner(window_id),
    )
    .and_then(|bytes| {
        if bytes.is_empty() {
            anyhow::bail!("ScreenCaptureKit produced empty explicit-window bytes");
        }
        Ok(bytes)
    })
    .map_err(|error| {
        prohibit_unverified_window_fallback(error.context(format!(
            "ScreenCaptureKit explicit capture failed for window {window_id}"
        )))
    })
}

/// Capture a window by its `window_id` (CGWindowID).
/// Returns raw PNG bytes or an error.
///
/// Uses explicit native capture. Its typed failures cannot fall back to an
/// unverified implicit window-group screenshot.
pub fn screenshot_window_bytes(window_id: u32) -> anyhow::Result<Vec<u8>> {
    capture_window_with_backends(
        window_id,
        screenshot_window_bytes_sck,
        screenshot_window_bytes_shell,
    )
}

/// Capture a window by its `window_id` (CGWindowID).
/// Returns (base64-encoded PNG, width, height) or an error.
pub fn screenshot_window(window_id: u32) -> anyhow::Result<(String, u32, u32)> {
    let bytes = screenshot_window_bytes(window_id)?;
    let (w, h) = png_dimensions(&bytes)?;
    let b64 = BASE64.encode(&bytes);
    Ok((b64, w, h))
}

/// Capture the full main display.
/// Returns raw PNG bytes or an error.
pub fn screenshot_display_bytes() -> anyhow::Result<Vec<u8>> {
    let capture = SecureCapturePath::new("display.png")?;
    let tmp_path = capture.file.to_string_lossy().into_owned();

    let output = Command::new("screencapture")
        .args(["-x", &tmp_path])
        .output()?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        if stderr.is_empty() {
            anyhow::bail!(
                "screencapture failed for main display with status {}",
                output.status
            );
        }
        anyhow::bail!(
            "screencapture failed for main display with status {}: {stderr}",
            output.status
        );
    }

    let bytes = std::fs::read(&capture.file)?;

    if bytes.is_empty() {
        anyhow::bail!("screencapture produced empty output for main display");
    }
    Ok(bytes)
}

/// Capture the main display and return (base64-encoded PNG, width, height).
pub fn screenshot_display() -> anyhow::Result<(String, u32, u32)> {
    let bytes = screenshot_display_bytes()?;
    let (w, h) = png_dimensions(&bytes)?;
    let b64 = BASE64.encode(&bytes);
    Ok((b64, w, h))
}

// PNG/JPEG/resize/crosshair helpers — re-exports of the shared
// `cua_driver_core::image_utils` module. The previous file-local copies were
// near-identical to the Windows and Linux versions; the dedup-audit
// (2026-05) moved them all to one place. See
// `CUA_DRIVER_RS_DEDUP_AUDIT.md` for the audit trail.

/// Convert raw PNG bytes to JPEG at the given quality (1-95).
pub fn png_bytes_to_jpeg(png_bytes: &[u8], quality: u8) -> anyhow::Result<Vec<u8>> {
    cua_driver_core::image_utils::png_bytes_to_jpeg(png_bytes, quality)
}

/// Downscale `png_bytes` so neither dimension exceeds `max_dim`.
/// If `max_dim == 0` or the image already fits, returns the original
/// bytes unchanged.
pub fn resize_png_if_needed(png_bytes: &[u8], max_dim: u32) -> anyhow::Result<Vec<u8>> {
    cua_driver_core::image_utils::resize_png_if_needed(png_bytes, max_dim)
}

/// Draw a red crosshair at pixel (cx, cy) on a PNG image and write to
/// `path`. Used by `click`'s `debug_image_out` param to verify
/// coordinate spaces. The crosshair uses top-left-origin coords
/// matching the click tool's convention.
pub fn write_crosshair_png(png_bytes: &[u8], cx: f64, cy: f64, path: &str) -> anyhow::Result<()> {
    cua_driver_core::image_utils::write_crosshair_png(png_bytes, cx, cy, path)
}

/// Draw a red crosshair at pixel (cx, cy) on a PNG image and return the
/// modified PNG bytes. Used by recording's click-marker callback to
/// produce click.png.
pub fn crosshair_png_bytes(png_bytes: &[u8], cx: f64, cy: f64) -> anyhow::Result<Vec<u8>> {
    cua_driver_core::image_utils::crosshair_png_bytes(png_bytes, cx, cy)
}

/// Parse width and height from a PNG file's IHDR chunk.
pub fn png_dimensions(data: &[u8]) -> anyhow::Result<(u32, u32)> {
    cua_driver_core::image_utils::png_dimensions(data)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::rc::Rc;
    use std::sync::Arc;

    #[test]
    fn frame_status_decodes_actual_numeric_attachment_values() {
        use core_foundation::base::TCFType;
        use core_foundation::number::CFNumber;
        use screencapturekit::cm::SCFrameStatus;

        for (raw, status) in [
            (0_i64, SCFrameStatus::Complete),
            (1, SCFrameStatus::Idle),
            (2, SCFrameStatus::Blank),
            (3, SCFrameStatus::Suspended),
            (4, SCFrameStatus::Started),
            (5, SCFrameStatus::Stopped),
        ] {
            let attachment = CFNumber::from(raw).as_CFType();
            assert_eq!(frame_status_from_attachment(&attachment), Some(status));
        }
    }

    #[test]
    fn malformed_frame_status_cannot_be_treated_as_complete() {
        use core_foundation::base::TCFType;
        use core_foundation::boolean::CFBoolean;
        use core_foundation::number::CFNumber;
        use core_foundation::string::CFString;

        for raw in [-1_i64, 6, i64::MIN, i64::MAX] {
            assert_eq!(
                frame_status_from_attachment(&CFNumber::from(raw).as_CFType()),
                None
            );
        }
        for attachment in [
            CFString::new("0").as_CFType(),
            CFBoolean::false_value().as_CFType(),
            CFNumber::from(0.5_f64).as_CFType(),
        ] {
            assert_eq!(frame_status_from_attachment(&attachment), None);
        }
    }

    fn capture_window_fixture(
        window_id: u32,
        identity: WindowCaptureIdentity,
    ) -> crate::windows::WindowInfo {
        let frame = identity.frame();
        crate::windows::WindowInfo {
            window_id,
            pid: identity.pid,
            app_name: "capture fixture".into(),
            title: String::new(),
            bounds: crate::windows::WindowBounds {
                x: frame.origin.x,
                y: frame.origin.y,
                width: frame.size.width,
                height: frame.size.height,
            },
            layer: identity.layer,
            z_index: 0,
            is_on_screen: true,
            current_space_id: None,
            on_current_space: None,
            space_ids: None,
        }
    }

    fn capture_display_fixture(
        id: u32,
        x: f64,
        y: f64,
        width: f64,
        height: f64,
    ) -> CaptureDisplayIdentity {
        CaptureDisplayIdentity::new(
            id,
            screencapturekit::cg::CGRect::new(x, y, width, height),
            2.0,
        )
        .unwrap()
    }

    fn binding_fixture(
        windows: &[crate::windows::WindowInfo],
        target: u32,
        ids: &[u32],
    ) -> WindowCaptureBinding {
        WindowCaptureBinding {
            selection: capture_selection_from_snapshot(target, windows, ids, true).unwrap(),
            display: None,
        }
    }

    #[test]
    fn gimp_partially_overlapping_standard_auxiliary_never_enables_hidden_children() {
        // H072/T051: both report AXStandardWindow; the auxiliary is partly
        // outside the host, so neither AXMain nor containing-peer rules prove
        // correct native grouping. Only the requested physical ID is selected.
        let host = WindowCaptureIdentity::new(15492, 0, 0.0, 33.0, 800.0, 632.0);
        let welcome = WindowCaptureIdentity::new(15492, 0, 95.0, 33.0, 610.0, 731.0);
        let windows = vec![
            capture_window_fixture(121580, host),
            capture_window_fixture(121581, welcome),
        ];
        let selected = capture_selection_from_snapshot(121581, &windows, &[], true).unwrap();
        assert_eq!(
            selected
                .render_windows()
                .iter()
                .map(|window| window.window_id)
                .collect::<Vec<_>>(),
            vec![121581]
        );
        let config = window_capture_configuration(1220, 1462, welcome.frame(), None);
        assert!(!config.includes_child_windows());
        assert_eq!(
            config.source_rect(),
            screencapturekit::cg::CGRect::new(0.0, 0.0, 0.0, 0.0)
        );
    }

    #[test]
    fn calc_sort_and_physical_popover_keep_independent_default_extent() {
        for frame in [
            screencapturekit::cg::CGRect::new(562.0, 276.0, 602.0, 511.0),
            screencapturekit::cg::CGRect::new(659.0, 283.0, 280.0, 608.0),
            screencapturekit::cg::CGRect::new(-1280.0, 36.0, 370.0, 182.0),
        ] {
            let config = window_capture_configuration(740, 364, frame, None);
            assert!(!config.includes_child_windows());
            assert!(config.ignores_shadows_single_window());
            assert_eq!(
                config.source_rect(),
                screencapturekit::cg::CGRect::new(0.0, 0.0, 0.0, 0.0)
            );
        }
    }

    #[test]
    fn explicit_keynote_composition_contains_only_proven_ids_and_fixed_host_crop() {
        let host = WindowCaptureIdentity::new(7489, 0, 142.0, 233.0, 1357.0, 610.0);
        let popup = WindowCaptureIdentity::new(7489, 0, 659.0, 283.0, 280.0, 608.0);
        let windows = vec![
            capture_window_fixture(121921, host),
            capture_window_fixture(121978, popup),
            capture_window_fixture(
                999,
                WindowCaptureIdentity::new(7489, 0, 150.0, 250.0, 400.0, 300.0),
            ),
        ];
        let selection = capture_selection_from_snapshot(121921, &windows, &[121978], true).unwrap();
        let ids = selection
            .render_windows()
            .iter()
            .map(|window| window.window_id)
            .collect::<Vec<_>>();
        assert_eq!(ids, vec![121921, 121978]);
        assert!(
            !ids.contains(&999),
            "same PID and overlap cannot add an unproven document"
        );
        let display = select_capture_display(
            &selection,
            &[capture_display_fixture(1, 0.0, 0.0, 1728.0, 1117.0)],
        )
        .unwrap();
        let config = window_capture_configuration(2714, 1220, host.frame(), display);
        assert_eq!((config.width(), config.height()), (2714, 1220));
        assert!(!config.includes_child_windows());
        assert!(config.ignores_shadows_display());
        assert_eq!(config.source_rect(), host.frame());
        assert!(!selection.can_cache());
    }

    #[test]
    fn attachment_admission_rejects_foreign_duplicate_missing_and_invalid_surfaces() {
        let host = capture_window_fixture(
            10,
            WindowCaptureIdentity::new(42, 0, 100.0, 100.0, 600.0, 500.0),
        );
        let popup = capture_window_fixture(
            11,
            WindowCaptureIdentity::new(42, 0, 200.0, 200.0, 200.0, 200.0),
        );
        for ids in [vec![10], vec![11, 11], vec![12]] {
            assert!(capture_selection_from_snapshot(
                10,
                &[host.clone(), popup.clone()],
                &ids,
                true
            )
            .is_err());
        }
        for variant in 0..4 {
            let mut invalid = popup.clone();
            match variant {
                0 => invalid.pid = 43,
                1 => invalid.bounds.width = f64::NAN,
                2 => invalid.bounds.x = f64::INFINITY,
                _ => invalid.bounds.height = -1.0,
            }
            assert!(
                capture_selection_from_snapshot(10, &[host.clone(), invalid], &[11], true).is_err()
            );
        }
        assert!(
            capture_selection_from_snapshot(10, &[host.clone(), host.clone()], &[], true).is_err()
        );
        assert!(capture_selection_from_snapshot(10, &[host, popup], &[11], false).is_err());
    }

    #[test]
    fn off_crop_attachments_contribute_no_pixels_but_still_invalidate_identity() {
        let host = capture_window_fixture(
            10,
            WindowCaptureIdentity::new(42, 0, 100.0, 100.0, 600.0, 500.0),
        );
        let popup = capture_window_fixture(
            11,
            WindowCaptureIdentity::new(42, 0, 300.0, 700.0, 200.0, 200.0),
        );
        let before = binding_fixture(&[host.clone(), popup.clone()], 10, &[11]);
        assert_eq!(before.selection.render_windows().len(), 1);
        assert_eq!(
            select_capture_display(&before.selection, &[]).unwrap(),
            None
        );
        assert!(!before.selection.can_cache());
        let mut moved = popup;
        moved.bounds.y = 500.0;
        let after = binding_fixture(&[host, moved], 10, &[11]);
        assert_eq!(after.selection.render_windows().len(), 2);
        assert!(matches!(
            capture_then_validate_identity(before, || Ok(vec![1]), || Ok(after)).unwrap(),
            CaptureIdentityValidation::Changed(_)
        ));
    }

    #[test]
    fn attachment_can_extend_outside_display_without_enlarging_target_crop() {
        let host = capture_window_fixture(
            10,
            WindowCaptureIdentity::new(42, 0, 100.0, 100.0, 600.0, 500.0),
        );
        let popup = capture_window_fixture(
            11,
            WindowCaptureIdentity::new(42, 0, 650.0, 450.0, 400.0, 400.0),
        );
        let selection =
            capture_selection_from_snapshot(10, &[host.clone(), popup], &[11], true).unwrap();
        let display = select_capture_display(
            &selection,
            &[capture_display_fixture(1, 0.0, 0.0, 800.0, 700.0)],
        )
        .unwrap();
        assert!(display.is_some());
        let config =
            window_capture_configuration(1200, 1000, selection.target.identity.frame(), display);
        assert_eq!(config.source_rect(), selection.target.identity.frame());
    }

    #[test]
    fn composition_requires_unique_active_display_covering_entire_target() {
        let host = capture_window_fixture(
            10,
            WindowCaptureIdentity::new(42, 0, -1600.0, 100.0, 600.0, 500.0),
        );
        let popup = capture_window_fixture(
            11,
            WindowCaptureIdentity::new(42, 0, -1500.0, 200.0, 200.0, 200.0),
        );
        let selection = capture_selection_from_snapshot(10, &[host, popup], &[11], true).unwrap();
        let left = capture_display_fixture(1, -1920.0, 0.0, 1920.0, 1080.0);
        let right = capture_display_fixture(2, 0.0, 0.0, 1728.0, 1117.0);
        assert_eq!(
            select_capture_display(&selection, &[right, left]).unwrap(),
            Some(left)
        );
        assert!(select_capture_display(&selection, &[right]).is_err());
        let mirror = capture_display_fixture(3, -1920.0, 0.0, 1920.0, 1080.0);
        assert!(select_capture_display(&selection, &[left, mirror]).is_err());
        let too_small = capture_display_fixture(4, -1920.0, 0.0, 600.0, 1080.0);
        assert!(select_capture_display(&selection, &[too_small, right]).is_err());
        let config =
            window_capture_configuration(1200, 1000, selection.target.identity.frame(), Some(left));
        assert_eq!(
            config.source_rect(),
            screencapturekit::cg::CGRect::new(320.0, 100.0, 600.0, 500.0)
        );
        assert!(!config.includes_child_windows());
    }

    #[test]
    fn cache_binding_tracks_discovery_all_physical_frames_and_display_scale() {
        let host = capture_window_fixture(
            10,
            WindowCaptureIdentity::new(42, 0, 100.0, 100.0, 600.0, 500.0),
        );
        let popup = capture_window_fixture(
            11,
            WindowCaptureIdentity::new(42, 0, 200.0, 200.0, 200.0, 200.0),
        );
        let windows = vec![host, popup];
        let empty = binding_fixture(&windows, 10, &[]);
        assert!(capture_plan_is_reusable(&empty, &empty));
        let mut unknown = empty.clone();
        unknown.selection.discovery_usable = false;
        assert!(!capture_plan_is_reusable(&empty, &unknown));
        let attached = binding_fixture(&windows, 10, &[11]);
        assert!(!capture_plan_is_reusable(&empty, &attached));
        assert!(
            !capture_plan_is_reusable(&attached, &attached),
            "composed plans are never warm cached"
        );
        let mut moved_windows = windows.clone();
        moved_windows[1].bounds.x += 1.0;
        let moved = binding_fixture(&moved_windows, 10, &[11]);
        assert!(matches!(
            capture_then_validate_identity(attached.clone(), || Ok(vec![1]), || Ok(moved)).unwrap(),
            CaptureIdentityValidation::Changed(_)
        ));
        assert!(
            matches!(
                capture_then_validate_identity(attached, || Ok(vec![1]), || Ok(empty.clone()))
                    .unwrap(),
                CaptureIdentityValidation::Changed(_)
            ),
            "closed attachment must discard captured bytes"
        );
        let mut changed_display = empty.clone();
        changed_display.display = Some(capture_display_fixture(1, 0.0, 0.0, 1728.0, 1117.0));
        let mut changed_scale = changed_display.clone();
        changed_scale.display.as_mut().unwrap().scale = 1.0_f64.to_bits();
        assert_ne!(changed_display, changed_scale);
        assert!(capture_then_validate_identity(
            empty,
            || Ok(vec![1]),
            || -> anyhow::Result<WindowCaptureBinding> {
                anyhow::bail!("post-capture identity read failed")
            }
        )
        .is_err());
    }

    fn exact_frame_info(frame: screencapturekit::cg::CGRect) -> screencapturekit::cm::FrameInfo {
        let local =
            screencapturekit::cg::CGRect::new(0.0, 0.0, frame.size.width, frame.size.height);
        screencapturekit::cm::FrameInfo {
            frame_status: Some(screencapturekit::cm::SCFrameStatus::Complete),
            scale_factor: Some(2.0),
            content_scale: Some(1.0),
            screen_rect: Some(frame),
            content_rect: Some(local),
            bounding_rect: Some(local),
            ..Default::default()
        }
    }

    #[test]
    fn frame_metadata_accepts_exact_host_and_independent_popup() {
        for frame in [
            screencapturekit::cg::CGRect::new(142.0, 233.0, 1357.0, 610.0),
            screencapturekit::cg::CGRect::new(659.0, 283.0, 280.0, 608.0),
            screencapturekit::cg::CGRect::new(-1280.0, 36.0, 370.0, 182.0),
        ] {
            let info = exact_frame_info(frame);
            assert!(validate_window_capture_geometry(
                frame,
                (frame.size.width * 2.0) as u32,
                (frame.size.height * 2.0) as u32,
                &info,
            )
            .is_ok());
        }
    }

    #[test]
    fn frame_metadata_rejects_observed_child_fitting_despite_matching_bitmap_size() {
        let frame = screencapturekit::cg::CGRect::new(142.0, 233.0, 1357.0, 610.0);
        let mut info = exact_frame_info(frame);
        // H058: the popup extended 48 points below its host. SCK still
        // returned 2714x1220, shrinking the composed content to 92.7%.
        info.content_scale = Some(0.9270516633987427);
        info.content_rect = Some(screencapturekit::cg::CGRect::new(
            0.0,
            0.0,
            1258.0091072320938,
            609.9999945163727,
        ));
        info.bounding_rect = info.content_rect;
        assert!(validate_window_capture_geometry(frame, 2714, 1220, &info).is_err());
    }

    #[test]
    fn frame_metadata_rejects_observed_display_origin_crop_with_unit_content_scale() {
        let frame = screencapturekit::cg::CGRect::new(142.0, 233.0, 1357.0, 610.0);
        let mut info = exact_frame_info(frame);
        // A display-coordinate sourceRect clipped the host while retaining
        // the requested bitmap size and contentScale=1. Dimensions or scale
        // alone cannot admit this frame.
        info.content_rect = Some(screencapturekit::cg::CGRect::new(0.0, 0.0, 1215.0, 425.0));
        info.bounding_rect = info.content_rect;
        assert!(validate_window_capture_geometry(frame, 2714, 1220, &info).is_err());
    }

    #[test]
    fn frame_metadata_rejects_stale_origin_missing_proof_and_nonfinite_values() {
        let frame = screencapturekit::cg::CGRect::new(142.0, 233.0, 1357.0, 610.0);
        let exact = exact_frame_info(frame);
        let mut stale = exact.clone();
        stale.screen_rect = Some(screencapturekit::cg::CGRect::new(
            100.0, 233.0, 1357.0, 610.0,
        ));
        let mut missing = exact.clone();
        missing.content_rect = None;
        let mut nonfinite = exact.clone();
        nonfinite.scale_factor = Some(f64::INFINITY);
        let mut incomplete = exact;
        incomplete.frame_status = Some(screencapturekit::cm::SCFrameStatus::Idle);
        for info in [stale, missing, nonfinite, incomplete] {
            assert!(validate_window_capture_geometry(frame, 2714, 1220, &info).is_err());
        }
    }

    #[test]
    fn native_window_capture_short_circuits_shell_fallback() {
        let png = cua_driver_core::image_utils::encode_rgba_to_png(&[0, 0, 0, 255], 1, 1)
            .expect("encode 1x1 PNG");
        assert!(!png.is_empty(), "PNG bytes must be non-empty");

        let native_calls = Rc::new(Cell::new(0u32));
        let fallback_calls = Rc::new(Cell::new(0u32));
        let native_window_id = Rc::new(Cell::new(None::<u32>));

        let native_calls_n = Rc::clone(&native_calls);
        let native_window_id_n = Rc::clone(&native_window_id);
        let png_n = png.clone();
        let fallback_calls_f = Rc::clone(&fallback_calls);

        let got = capture_window_with_backends(
            42,
            move |window_id| {
                native_calls_n.set(native_calls_n.get() + 1);
                native_window_id_n.set(Some(window_id));
                Ok(png_n)
            },
            move |_window_id| {
                fallback_calls_f.set(fallback_calls_f.get() + 1);
                anyhow::bail!("shell fallback must not run when native succeeds");
            },
        )
        .expect("native capture should succeed");

        assert_eq!(native_calls.get(), 1, "native backend called once");
        assert_eq!(
            native_window_id.get(),
            Some(42),
            "native backend receives window id 42"
        );
        assert_eq!(fallback_calls.get(), 0, "shell fallback must not run");
        assert_eq!(got, png, "helper returns native PNG bytes verbatim");
    }

    #[test]
    fn empty_native_capture_uses_shell_fallback() {
        let got = capture_window_with_backends(
            42,
            |_| Ok(Vec::new()),
            |window_id| Ok(format!("fallback-{window_id}").into_bytes()),
        )
        .expect("empty native capture should fall back");

        assert_eq!(got, b"fallback-42");
    }

    #[test]
    fn capture_error_preserves_native_and_fallback_contexts() {
        let error = capture_window_with_backends(
            42,
            |_| anyhow::bail!("native denied"),
            |_| anyhow::bail!("fallback denied"),
        )
        .expect_err("both capture backends should fail")
        .to_string();

        assert!(error.contains("native denied"), "{error}");
        assert!(error.contains("fallback denied"), "{error}");
    }

    #[test]
    fn explicit_capture_refusal_never_uses_unverified_shell_and_preserves_source() {
        let fallback_calls = Cell::new(0);
        let error = capture_window_with_backends(
            42,
            |_| {
                Err(prohibit_unverified_window_fallback(
                    anyhow::anyhow!("selected attachment changed during frame capture")
                        .context("ScreenCaptureKit capture failed"),
                ))
            },
            |_| {
                fallback_calls.set(fallback_calls.get() + 1);
                Ok(vec![99])
            },
        )
        .unwrap_err();
        assert!(error.is::<UnverifiedWindowFallback>());
        let detail = format!("{error:#}");
        assert!(detail.contains("selected attachment changed"), "{detail}");
        assert!(
            detail.contains("ScreenCaptureKit capture failed"),
            "{detail}"
        );
        assert_eq!(fallback_calls.get(), 0);
    }

    #[test]
    fn explicit_timeout_and_worker_refusal_markers_survive_outer_error_context() {
        for reason in [
            "capture timed out after 3000 ms",
            "capture already in flight",
            "frame geometry mismatch",
        ] {
            let fallback_calls = Cell::new(0);
            let error = capture_window_with_backends(
                42,
                |_| {
                    Err(
                        prohibit_unverified_window_fallback(anyhow::anyhow!(reason.to_owned()))
                            .context("outer observation"),
                    )
                },
                |_| {
                    fallback_calls.set(fallback_calls.get() + 1);
                    Ok(vec![99])
                },
            )
            .unwrap_err();
            assert!(error.is::<UnverifiedWindowFallback>());
            assert!(format!("{error:#}").contains(reason));
            assert_eq!(fallback_calls.get(), 0);
        }
    }

    #[test]
    fn native_window_capture_cache_reuses_fresh_and_expires_stale_entries() {
        use std::time::{Duration, Instant};

        let t0 = Instant::now();
        let mut cache: TimedCache<u32, Arc<&'static str>> =
            TimedCache::new(Duration::from_secs(2), 4);

        let descriptor = Arc::new("descriptor");
        cache.insert_at(42, Arc::clone(&descriptor), t0);
        assert_eq!(cache.len(), 1);

        let fresh = cache
            .get_cloned_at(&42, t0 + Duration::from_millis(1500))
            .expect("fresh cache hit within TTL");
        assert!(
            Arc::ptr_eq(&fresh, &descriptor),
            "fresh hit must return the same Arc"
        );
        assert_eq!(cache.len(), 1);

        let stale = cache.get_cloned_at(&42, t0 + Duration::from_secs(2));
        assert!(stale.is_none(), "entry must expire at TTL");
        assert_eq!(cache.len(), 0, "stale entry must be removed on get");
    }

    #[test]
    fn native_window_capture_cache_purges_expired_before_capacity_eviction() {
        let t0 = Instant::now();
        let mut cache = TimedCache::new(Duration::from_secs(2), 2);
        cache.insert_at(1, "expired", t0);
        cache.insert_at(2, "fresh", t0 + Duration::from_millis(1500));

        cache.insert_at(3, "new", t0 + Duration::from_secs(2));

        assert_eq!(cache.len(), 2);
        assert!(cache
            .get_cloned_at(&1, t0 + Duration::from_secs(2))
            .is_none());
        assert_eq!(
            cache.get_cloned_at(&2, t0 + Duration::from_secs(2)),
            Some("fresh")
        );
        assert_eq!(
            cache.get_cloned_at(&3, t0 + Duration::from_secs(2)),
            Some("new")
        );
    }

    #[test]
    fn native_window_capture_cache_remove_if_does_not_remove_replacement() {
        let t0 = Instant::now();
        let mut cache = TimedCache::new(Duration::from_secs(2), 2);
        let old = Arc::new("old");
        let replacement = Arc::new("replacement");
        cache.insert_at(42, Arc::clone(&old), t0);
        cache.insert_at(42, Arc::clone(&replacement), t0);

        assert!(!cache.remove_if(&42, |stored| Arc::ptr_eq(stored, &old)));
        let stored = cache
            .get_cloned_at(&42, t0)
            .expect("replacement remains cached");
        assert!(Arc::ptr_eq(&stored, &replacement));
    }

    #[test]
    fn window_capture_identity_changes_with_owner_layer_or_frame() {
        let original = WindowCaptureIdentity::new(10, 0, 1.0, 2.0, 800.0, 600.0);
        assert_ne!(
            original,
            WindowCaptureIdentity::new(11, 0, 1.0, 2.0, 800.0, 600.0)
        );
        assert_ne!(
            original,
            WindowCaptureIdentity::new(10, 1, 1.0, 2.0, 800.0, 600.0)
        );
        assert_ne!(
            original,
            WindowCaptureIdentity::new(10, 0, 1.0, 2.0, 801.0, 600.0)
        );
    }

    #[test]
    fn post_capture_identity_change_never_returns_stale_bytes() {
        let before = WindowCaptureIdentity::new(10, 0, 1.0, 2.0, 800.0, 600.0);
        let after = WindowCaptureIdentity::new(10, 0, 5.0, 2.0, 800.0, 600.0);

        let outcome = capture_then_validate_identity(before, || Ok(vec![1, 2, 3]), || Ok(after))
            .expect("capture and identity read succeed");

        assert!(matches!(
            outcome,
            CaptureIdentityValidation::Changed(identity) if identity == after
        ));
    }

    #[test]
    fn second_identity_change_during_retry_also_fails_closed() {
        let first = WindowCaptureIdentity::new(10, 0, 1.0, 2.0, 800.0, 600.0);
        let second = WindowCaptureIdentity::new(10, 0, 5.0, 2.0, 800.0, 600.0);
        let third = WindowCaptureIdentity::new(10, 0, 5.0, 2.0, 900.0, 600.0);

        let first_attempt = capture_then_validate_identity(first, || Ok(vec![1]), || Ok(second))
            .expect("first attempt completes");
        assert!(matches!(
            first_attempt,
            CaptureIdentityValidation::Changed(identity) if identity == second
        ));

        let retry = capture_then_validate_identity(second, || Ok(vec![2]), || Ok(third))
            .expect("retry completes");
        assert!(matches!(
            retry,
            CaptureIdentityValidation::Changed(identity) if identity == third
        ));
    }

    #[test]
    fn identity_mismatch_eviction_does_not_clobber_replacement_cache_entry() {
        let now = Instant::now();
        let mut cache = TimedCache::new(Duration::from_secs(2), 1);
        let stale = std::sync::Arc::new(1u8);
        let replacement = std::sync::Arc::new(2u8);
        cache.insert_at(42, std::sync::Arc::clone(&stale), now);

        // Model another capture refreshing the same key before this stale
        // attempt handles its post-capture identity mismatch.
        cache.insert_at(42, std::sync::Arc::clone(&replacement), now);
        assert!(!cache.remove_if(&42, |stored| { std::sync::Arc::ptr_eq(stored, &stale) }));

        let stored = cache
            .get_cloned_at(&42, now)
            .expect("replacement remains cached");
        assert!(std::sync::Arc::ptr_eq(&stored, &replacement));
    }

    #[test]
    fn native_capture_gate_allows_only_one_worker_until_permit_drops() {
        static GATE: NativeCaptureGate = NativeCaptureGate::new();

        let permit = GATE.try_acquire().expect("first worker acquires gate");
        assert!(
            GATE.try_acquire().is_none(),
            "a second worker must be refused while the first is active"
        );

        drop(permit);
        assert!(
            GATE.try_acquire().is_some(),
            "gate reopens only when the worker-owned permit drops"
        );
    }

    #[test]
    fn timed_out_native_worker_blocks_replacement_until_original_returns() {
        use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

        static GATE: NativeCaptureGate = NativeCaptureGate::new();
        static SPAWNED_WORK: AtomicUsize = AtomicUsize::new(0);
        let (started_sender, started_receiver) = mpsc::channel();
        let (release_sender, release_receiver) = mpsc::channel();

        let first_caller = std::thread::spawn(move || {
            run_native_capture_worker(&GATE, Duration::from_millis(10), move || {
                SPAWNED_WORK.fetch_add(1, AtomicOrdering::SeqCst);
                started_sender.send(()).expect("worker reports it started");
                release_receiver
                    .recv()
                    .expect("test releases stalled worker");
                Ok(1u8)
            })
        });
        started_receiver
            .recv()
            .expect("first worker starts before its timeout is observed");
        let first = first_caller.join().expect("first caller joins");
        assert!(first
            .expect_err("stalled worker times out")
            .to_string()
            .contains("timed out"));

        let second = run_native_capture_worker(&GATE, Duration::from_secs(1), || {
            SPAWNED_WORK.fetch_add(1, AtomicOrdering::SeqCst);
            Ok(2u8)
        });
        assert!(second
            .expect_err("replacement is refused while original remains blocked")
            .to_string()
            .contains("already in flight"));
        assert_eq!(
            SPAWNED_WORK.load(AtomicOrdering::SeqCst),
            1,
            "refused replacement must not spawn"
        );

        release_sender.send(()).expect("release original worker");
        let deadline = Instant::now() + Duration::from_secs(1);
        while GATE.active.load(AtomicOrdering::Acquire) && Instant::now() < deadline {
            std::thread::yield_now();
        }
        assert!(!GATE.active.load(AtomicOrdering::Acquire));

        assert_eq!(
            run_native_capture_worker(&GATE, Duration::from_secs(1), || {
                SPAWNED_WORK.fetch_add(1, AtomicOrdering::SeqCst);
                Ok(3u8)
            })
            .expect("gate reopens after original worker returns"),
            3
        );
        assert_eq!(SPAWNED_WORK.load(AtomicOrdering::SeqCst), 2);
    }
}
