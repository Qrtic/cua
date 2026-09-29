//! Main-thread-owned per-display windows. Render workers carry only display IDs
//! and layout generations, never NSWindow/CALayer pointers that hotplug retires.

use super::displays::{DisplayGeometry, DisplayLayout};
use super::visibility::{self, WindowClips};
use objc2::{class, msg_send, rc::Retained, runtime::AnyObject};
use objc2_foundation::{MainThreadMarker, NSPoint, NSRect, NSSize};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    ffi::c_void,
    sync::{
        atomic::{AtomicBool, Ordering},
        Mutex,
    },
};

struct Surface {
    window: Retained<AnyObject>,
    layer: Retained<AnyObject>,
    window_id: u32,
}

impl Drop for Surface {
    fn drop(&mut self) {
        debug_assert!(MainThreadMarker::new().is_some());
        SURFACE_WINDOW_IDS
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .0
            .remove(&self.window_id);
        tracing::debug!(target: "cua_window_order", window_id = self.window_id,
            "Retired owned transparent cursor surface");
        unsafe {
            let nil = std::ptr::null_mut::<AnyObject>();
            let _: () = msg_send![&*self.layer, setContents: nil];
            let _: () = msg_send![&*self.window, orderOut: nil];
            let _: () = msg_send![&*self.window, close];
        }
    }
}

#[derive(Default)]
struct SurfaceSet {
    layout: DisplayLayout,
    surfaces: BTreeMap<u32, Surface>,
}

thread_local! {
    static SURFACES: RefCell<SurfaceSet> = RefCell::new(SurfaceSet::default());
}

static REFRESH_QUEUED: AtomicBool = AtomicBool::new(false);

// Only windows created here are transparent, non-interactive cursor surfaces.
// Never infer this identity from the Driver PID, a title or screen-sized bounds:
// a different Driver window can be a real dialog that must remain observable.
struct SurfaceWindowIds(BTreeSet<u32>);

impl SurfaceWindowIds {
    fn contains(&self, driver_pid: i32, pid: i32, window_id: u32) -> bool {
        pid == driver_pid && window_id != 0 && self.0.contains(&window_id)
    }
}

static SURFACE_WINDOW_IDS: Mutex<SurfaceWindowIds> = Mutex::new(SurfaceWindowIds(BTreeSet::new()));

pub(crate) fn is_owned_cursor_window(pid: i32, window_id: u32) -> bool {
    SURFACE_WINDOW_IDS
        .lock()
        .unwrap_or_else(|error| error.into_inner())
        .contains(std::process::id() as i32, pid, window_id)
}

unsafe fn enumerate_displays() -> Vec<DisplayGeometry> {
    use core_foundation::array::{CFArrayGetCount, CFArrayGetValueAtIndex, CFArrayRef};
    let screens: *mut AnyObject = msg_send![class!(NSScreen), screens];
    if screens.is_null() {
        return Vec::new();
    }
    // Current macOS may return Swift-backed NSArray storage whose Objective-C
    // `count` annotation is signed Int, despite NSArray's NSUInteger API.
    // The toll-free CFArray interface has one stable CFIndex ABI for both.
    let screens = screens as CFArrayRef;
    let count = CFArrayGetCount(screens);
    let key: *mut AnyObject =
        msg_send![class!(NSString), stringWithUTF8String: c"NSScreenNumber".as_ptr().cast::<u8>()];
    let mut displays = BTreeMap::new();
    for index in 0..count {
        let screen = CFArrayGetValueAtIndex(screens, index) as *mut AnyObject;
        let description: *mut AnyObject = msg_send![screen, deviceDescription];
        let number: *mut AnyObject = msg_send![description, objectForKey: key];
        if number.is_null() {
            continue;
        }
        let id: u32 = msg_send![number, unsignedIntValue];
        let frame: NSRect = msg_send![screen, frame];
        let bounds = core_graphics::display::CGDisplayBounds(id);
        let mut scale: f64 = msg_send![screen, backingScaleFactor];
        if !scale.is_finite() || scale < 1.0 {
            scale = crate::tools::get_screen_size::get_backing_scale(id).max(1.0);
        }
        if let Some(display) = DisplayGeometry::new(
            id,
            [
                frame.origin.x,
                frame.origin.y,
                frame.size.width,
                frame.size.height,
            ],
            [
                bounds.origin.x,
                bounds.origin.y,
                bounds.size.width,
                bounds.size.height,
            ],
            scale,
        ) {
            displays.insert(id, display);
        } else {
            tracing::warn!(
                display_id = id,
                "cursor overlay skipped invalid/oversized display geometry"
            );
        }
    }
    displays.into_values().collect()
}

fn ns_frame(display: &DisplayGeometry) -> NSRect {
    let [x, y, w, h] = display.appkit_frame;
    NSRect::new(NSPoint::new(x, y), NSSize::new(w, h))
}

unsafe fn create_surface(display: &DisplayGeometry) -> Option<Surface> {
    let allocated: *mut AnyObject = msg_send![class!(NSWindow), alloc];
    let window: *mut AnyObject = msg_send![allocated,
        initWithContentRect: ns_frame(display) styleMask: 0u64 backing: 2u64 defer: false];
    let window = Retained::from_raw(window)?;
    let clear: *mut AnyObject = msg_send![class!(NSColor), clearColor];
    let _: () = msg_send![&*window, setOpaque: false];
    let _: () = msg_send![&*window, setBackgroundColor: clear];
    let _: () = msg_send![&*window, setHasShadow: false];
    let _: () = msg_send![&*window, setIgnoresMouseEvents: true];
    let _: () = msg_send![&*window, setSharingType: 1u64];
    let _: () = msg_send![&*window, setLevel: 0i64];
    let _: () = msg_send![&*window, setCollectionBehavior: (1u64 | (1 << 8) | (1 << 4))];
    let _: () = msg_send![&*window, setReleasedWhenClosed: false];
    let _: () = msg_send![&*window, setHidesOnDeactivate: false];
    let content: *mut AnyObject = msg_send![&*window, contentView];
    let _: () = msg_send![content, setWantsLayer: true];
    let layer: *mut AnyObject = msg_send![content, layer];
    let layer = Retained::retain(layer)?;
    let gravity: *mut AnyObject =
        msg_send![class!(NSString), stringWithUTF8String: c"topLeft".as_ptr().cast::<u8>()];
    let _: () = msg_send![&*layer, setContentsGravity: gravity];
    let _: () = msg_send![&*layer, setContentsScale: display.scale];
    // Empty, click-through, normal-level windows never activate the Driver.
    let _: () = msg_send![&*window, orderFrontRegardless];
    let number: isize = msg_send![&*window, windowNumber];
    let window_id = u32::try_from(number).unwrap_or(0);
    if window_id != 0 {
        SURFACE_WINDOW_IDS
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .0
            .insert(window_id);
        let display_id = display.id;
        tracing::debug!(target: "cua_window_order", window_id, display_id,
            "Registered owned transparent cursor surface");
    }
    Some(Surface {
        window,
        layer,
        window_id,
    })
}

unsafe fn refresh_surfaces() {
    MainThreadMarker::new().expect("cursor display refresh must run on the main thread");
    let desired = enumerate_displays();
    let published = SURFACES.with(|cell| {
        let mut state = cell.borrow_mut();
        if state.layout.displays == desired {
            return None;
        }
        let mut next = BTreeMap::new();
        let mut installed = Vec::new();
        for display in desired {
            let changed = state
                .layout
                .displays
                .iter()
                .find(|old| old.id == display.id)
                != Some(&display);
            let surface = state
                .surfaces
                .remove(&display.id)
                .or_else(|| create_surface(&display));
            if let Some(surface) = surface {
                if changed {
                    let _: () =
                        msg_send![&*surface.window, setFrame: ns_frame(&display) display: false];
                    let _: () = msg_send![&*surface.layer, setContentsScale: display.scale];
                    let _: () =
                        msg_send![&*surface.layer, setContents: std::ptr::null_mut::<AnyObject>()];
                }
                next.insert(display.id, surface);
                installed.push(display);
            } else {
                let display_id = display.id;
                tracing::warn!(
                    display_id,
                    "cursor overlay could not create display surface"
                );
            }
        }
        // Remaining old surfaces are disconnected; drop only these owned windows.
        state.surfaces = next;
        state
            .layout
            .replace(installed)
            .then(|| state.layout.clone())
    });
    if let Some(layout) = published {
        super::publish_display_layout(layout);
    }
}

/// Register once for the lifetime of this AppKit owner, including startup with
/// no attached display. Notification delivery only queues coalesced main work.
pub(super) unsafe fn initialize() {
    use block2::RcBlock;
    use objc2_foundation::{NSNotification, NSNotificationCenter, NSString};
    let center = NSNotificationCenter::defaultCenter();
    let name = NSString::from_str("NSApplicationDidChangeScreenParametersNotification");
    let block = RcBlock::new(|_: std::ptr::NonNull<NSNotification>| {
        if !REFRESH_QUEUED.swap(true, Ordering::AcqRel) {
            dispatch_main(std::ptr::null_mut(), refresh_callback);
        }
    });
    let token = center.addObserverForName_object_queue_usingBlock(Some(&name), None, None, &block);
    // AppKit and this observer have process lifetime, like the existing owner.
    std::mem::forget(token);
    refresh_surfaces();
}

unsafe extern "C" fn refresh_callback(_ctx: *mut c_void) {
    REFRESH_QUEUED.store(false, Ordering::Release);
    refresh_surfaces();
}

extern "C" {
    fn CGImageRelease(image: *mut c_void);
}

struct Frame {
    display_id: u32,
    image: usize,
}

impl Drop for Frame {
    fn drop(&mut self) {
        unsafe {
            CGImageRelease(self.image as *mut c_void);
        }
    }
}

struct FrameBatch {
    generation: u64,
    frames: Vec<Frame>,
    clips: WindowClips,
}

/// One queued batch, not an unbounded queue of full-resolution screen images.
#[derive(Default)]
struct LatestFrame<T> {
    pending: Option<T>,
    scheduled: bool,
}

impl<T> LatestFrame<T> {
    fn replace(&mut self, batch: T) -> bool {
        self.pending = Some(batch);
        !std::mem::replace(&mut self.scheduled, true)
    }

    fn take(&mut self) -> Option<T> {
        self.scheduled = false;
        self.pending.take()
    }
}

static FRAMES: Mutex<LatestFrame<FrameBatch>> = Mutex::new(LatestFrame {
    pending: None,
    scheduled: false,
});

pub(super) fn submit_frames(
    generation: u64,
    pixmaps: Vec<(u32, tiny_skia::Pixmap)>,
    clips: WindowClips,
) {
    let frames = pixmaps
        .into_iter()
        .filter_map(|(display_id, pixmap)| {
            super::pixmap_to_cgimage(&pixmap).map(|image| Frame { display_id, image })
        })
        .collect();
    let schedule = FRAMES.lock().unwrap().replace(FrameBatch {
        generation,
        frames,
        clips,
    });
    if schedule {
        dispatch_main(std::ptr::null_mut(), present_frames);
    }
}

unsafe extern "C" fn present_frames(_ctx: *mut c_void) {
    let Some(batch) = FRAMES.lock().unwrap().take() else {
        return;
    };
    SURFACES.with(|cell| {
        let state = cell.borrow();
        if batch.generation != state.layout.generation {
            return;
        }
        if !visibility::clips_are_current(&batch.clips) {
            // Window activation, movement or a closed save panel can race a
            // queued frame. Clear stale pixels instead of briefly presenting
            // them above the new foreground window, and request a fresh frame.
            for surface in state.surfaces.values() {
                let _: () = msg_send![&*surface.layer,
                    setContents: std::ptr::null_mut::<AnyObject>()];
            }
            super::request_visibility_refresh();
            return;
        }
        for frame in &batch.frames {
            if !state
                .layout
                .accepts_frame(batch.generation, frame.display_id)
            {
                continue;
            }
            if let Some(surface) = state.surfaces.get(&frame.display_id) {
                let image = frame.image as *mut AnyObject;
                let _: () = msg_send![&*surface.layer, setContents: image];
            }
        }
    });
    // Each CGImage is released even when its display/generation was retired.
}

#[derive(Clone, Copy)]
struct EnqueueDiagnostic {
    site: &'static str,
    sequence: u64,
    started_ns: Option<u64>,
}

type OrderRequest = (u64, Option<(u64, bool)>, Option<EnqueueDiagnostic>);

fn enqueue_diagnostic(
    site: &'static str,
    measurement: Option<&crate::order_diagnostics::CallMeasurement>,
) -> Option<EnqueueDiagnostic> {
    let measurement = measurement?;
    Some(EnqueueDiagnostic {
        site,
        sequence: measurement.sequence()?,
        started_ns: measurement.started_ns(),
    })
}

pub(super) fn order_front(generation: u64) {
    static DIAGNOSTICS: crate::order_diagnostics::LimitedCallsite =
        crate::order_diagnostics::LimitedCallsite::new("overlay_enqueue_front");
    let diagnostic = DIAGNOSTICS.begin();
    let metadata = enqueue_diagnostic("overlay_enqueue_front", diagnostic.as_ref());
    dispatch_main(
        Box::into_raw(Box::new((generation, None::<(u64, bool)>, metadata))).cast(),
        order_callback,
    );
    if let Some(timing) = diagnostic.and_then(|measurement| measurement.finish()) {
        let _ = crate::order_diagnostics::diagnostic_only(|| {
            tracing::debug!(
                target: "cua_window_order",
                diagnostic_site = "overlay_enqueue_front",
                sequence = timing.sequence,
                clock = "CLOCK_UPTIME_RAW",
                started_ns = timing.started_ns,
                finished_ns = timing.finished_ns,
                rust_thread_id = ?std::thread::current().id(),
                requested_generation = generation,
                "Queued existing unpinned overlay order callback"
            );
        });
    }
}

pub(super) fn order_above(generation: u64, target_wid: u64, raise_front: bool) {
    static DIAGNOSTICS: crate::order_diagnostics::LimitedCallsite =
        crate::order_diagnostics::LimitedCallsite::new("overlay_enqueue_above");
    let diagnostic = DIAGNOSTICS.begin();
    let metadata = enqueue_diagnostic("overlay_enqueue_above", diagnostic.as_ref());
    dispatch_main(
        Box::into_raw(Box::new((
            generation,
            Some((target_wid, raise_front)),
            metadata,
        )))
        .cast(),
        order_callback,
    );
    if let Some(timing) = diagnostic.and_then(|measurement| measurement.finish()) {
        let _ = crate::order_diagnostics::diagnostic_only(|| {
            tracing::debug!(
                target: "cua_window_order",
                diagnostic_site = "overlay_enqueue_above",
                sequence = timing.sequence,
                clock = "CLOCK_UPTIME_RAW",
                started_ns = timing.started_ns,
                finished_ns = timing.finished_ns,
                rust_thread_id = ?std::thread::current().id(),
                requested_generation = generation,
                target_window_id = target_wid,
                captured_raise_front = raise_front,
                "Queued existing target-relative overlay order callback"
            );
        });
    }
}

unsafe extern "C" fn order_callback(ctx: *mut c_void) {
    static DIAGNOSTICS: crate::order_diagnostics::LimitedCallsite =
        crate::order_diagnostics::LimitedCallsite::new("overlay_callback");
    static SURFACE_DIAGNOSTICS: crate::order_diagnostics::LimitedCallsite =
        crate::order_diagnostics::LimitedCallsite::new("overlay_surface_sequence");
    let diagnostic = DIAGNOSTICS.begin();
    let (generation, target, enqueued): OrderRequest = *Box::from_raw(ctx.cast());
    let mut observed_generation = None;
    let mut generation_matched = false;
    let mut receiver_count = 0;
    SURFACES.with(|cell| {
        let state = cell.borrow();
        observed_generation = Some(state.layout.generation);
        if state.layout.generation != generation {
            return;
        }
        generation_matched = true;
        receiver_count = state.surfaces.len();
        for (display_id, surface) in &state.surfaces {
            let surface_diagnostic = SURFACE_DIAGNOSTICS.begin();
            let mut relative_finished_ns = None;
            let mut front_started_ns = None;
            if let Some((target_wid, raise_front)) = target {
                let _: () =
                    msg_send![&*surface.window, orderWindow: 1i64 relativeTo: target_wid as i64];
                relative_finished_ns = surface_diagnostic
                    .as_ref()
                    .and_then(|measurement| measurement.timestamp());
                if raise_front {
                    front_started_ns = surface_diagnostic
                        .as_ref()
                        .and_then(|measurement| measurement.timestamp());
                    let _: () = msg_send![&*surface.window, orderFrontRegardless];
                }
            } else {
                front_started_ns = surface_diagnostic
                    .as_ref()
                    .and_then(|measurement| measurement.started_ns());
                let _: () = msg_send![&*surface.window, orderFrontRegardless];
            }
            if let Some(timing) = surface_diagnostic.and_then(|measurement| measurement.finish()) {
                let _ = crate::order_diagnostics::diagnostic_only(|| {
                    tracing::debug!(
                        target: "cua_window_order",
                        diagnostic_site = "overlay_surface_sequence",
                        sequence = timing.sequence,
                        clock = "CLOCK_UPTIME_RAW",
                        started_ns = timing.started_ns,
                        finished_ns = timing.finished_ns,
                        rust_thread_id = ?std::thread::current().id(),
                        enqueue_site = enqueued.map(|entry| entry.site),
                        enqueue_sequence = enqueued.map(|entry| entry.sequence),
                        receiver_window_id = surface.window_id,
                        display_id = *display_id,
                        target_window_id = target.map(|value| value.0),
                        relative_order_called = target.is_some(),
                        relative_finished_ns,
                        front_order_called = target.is_none_or(|value| value.1),
                        front_started_ns,
                        "Existing owned overlay ordering sequence returned"
                    );
                });
            }
        }
    });
    if let Some(timing) = diagnostic.and_then(|measurement| measurement.finish()) {
        let _ = crate::order_diagnostics::diagnostic_only(|| {
            tracing::debug!(
                target: "cua_window_order",
                diagnostic_site = "overlay_callback",
                sequence = timing.sequence,
                clock = "CLOCK_UPTIME_RAW",
                started_ns = timing.started_ns,
                finished_ns = timing.finished_ns,
                rust_thread_id = ?std::thread::current().id(),
                enqueue_site = enqueued.map(|entry| entry.site),
                enqueue_sequence = enqueued.map(|entry| entry.sequence),
                enqueue_started_ns = enqueued.and_then(|entry| entry.started_ns),
                requested_generation = generation,
                observed_generation,
                generation_matched,
                receiver_count,
                target_window_id = target.map(|value| value.0),
                captured_raise_front = target.map(|value| value.1),
                "Existing overlay order callback returned"
            );
        });
    }
}

fn dispatch_main(context: *mut c_void, callback: unsafe extern "C" fn(*mut c_void)) {
    #[link(name = "dispatch", kind = "dylib")]
    extern "C" {
        static _dispatch_main_q: u8;
        fn dispatch_async_f(
            queue: *const c_void,
            context: *mut c_void,
            work: unsafe extern "C" fn(*mut c_void),
        );
    }
    unsafe {
        dispatch_async_f(
            &raw const _dispatch_main_q as *const c_void,
            context,
            callback,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{LatestFrame, SurfaceWindowIds};
    use std::{cell::Cell, rc::Rc};

    #[test]
    fn cursor_identity_covers_multiple_displays_and_retires_closed_windows() {
        let mut ids = SurfaceWindowIds([11, 12].into_iter().collect());
        assert!(ids.contains(7, 7, 11));
        assert!(ids.contains(7, 7, 12));
        assert!(!ids.contains(7, 8, 11));
        assert!(!ids.contains(7, 7, 13));
        assert!(!ids.contains(7, 7, 0));
        ids.0.remove(&11);
        assert!(!ids.contains(7, 7, 11), "a retired ID grants no exclusion");
        assert!(ids.contains(7, 7, 12), "the other display remains owned");
    }

    #[test]
    fn slow_main_queue_keeps_only_the_latest_batch_and_drops_replaced_frames() {
        struct Tracked(Rc<Cell<usize>>);
        impl Drop for Tracked {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }
        let dropped = Rc::new(Cell::new(0));
        let mut mailbox = LatestFrame {
            pending: None,
            scheduled: false,
        };
        assert!(mailbox.replace(Tracked(dropped.clone())));
        for _ in 0..50 {
            assert!(!mailbox.replace(Tracked(dropped.clone())));
        }
        assert_eq!(dropped.get(), 50);
        let presented = mailbox.take().unwrap();
        assert!(
            mailbox.replace(Tracked(dropped.clone())),
            "next callback can be scheduled while presenting"
        );
        drop(presented);
        drop(mailbox);
        assert_eq!(dropped.get(), 52);
    }
}
