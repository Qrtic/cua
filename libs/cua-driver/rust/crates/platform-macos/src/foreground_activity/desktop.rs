//! One-use primary-display observations and input with no app activation.
use super::*;
use cua_driver_core::{foreground_segment::Owner, protocol::ToolResult, session::TransportOwner};
use serde_json::{json, Value};
use std::collections::VecDeque;
use std::sync::atomic::AtomicU64;

const OBSERVATION_TTL_MS: u64 = 30_000;
const ACTION_LIMIT_MS: u64 = 15_000;
const CAPTURE_LIMIT_MS: u64 = 10_000;
const MAX_OBSERVATIONS: usize = 32;

static DISPLAY_GENERATION: AtomicU64 = AtomicU64::new(0);

extern "C" fn display_changed(_display: u32, _flags: u32, _context: *mut std::ffi::c_void) {
    DISPLAY_GENERATION.fetch_add(1, Ordering::AcqRel);
}

#[link(name = "CoreGraphics", kind = "framework")]
extern "C" {
    fn CGDisplayRegisterReconfigurationCallback(
        callback: extern "C" fn(u32, u32, *mut std::ffi::c_void),
        context: *mut std::ffi::c_void,
    ) -> i32;
}

fn display_generation() -> Option<u64> {
    static COVERED: OnceLock<bool> = OnceLock::new();
    // Process-lifetime passive coverage also rejects change-and-return to an
    // identical display mode between observation and action.
    let covered = COVERED.get_or_init(|| unsafe {
        CGDisplayRegisterReconfigurationCallback(display_changed, std::ptr::null_mut()) == 0
    });
    covered.then(|| DISPLAY_GENERATION.load(Ordering::Acquire))
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct Geometry {
    generation: u64,
    display_id: u32,
    x: f64,
    y: f64,
    pub(crate) width: f64,
    pub(crate) height: f64,
    mode_width: u64,
    mode_height: u64,
    pixel_width: u64,
    pixel_height: u64,
}

impl Geometry {
    fn valid(self) -> bool {
        self.display_id != 0
            && [self.x, self.y, self.width, self.height]
                .iter()
                .all(|v| v.is_finite())
            && self.width > 0.0
            && self.height > 0.0
            && self.width <= 100_000.0
            && self.height <= 100_000.0
            && self.width.fract() == 0.0
            && self.height.fract() == 0.0
            && self.mode_width > 0
            && self.mode_height > 0
            && self.pixel_width > 0
            && self.pixel_height > 0
            && self.pixel_width <= 100_000
            && self.pixel_height <= 100_000
    }

    pub(crate) fn scale(self) -> f64 {
        self.pixel_width as f64 / self.width
    }

    fn matches_capture(self, width: u32, height: u32) -> bool {
        self.valid()
            && u64::from(width) == self.pixel_width
            && u64::from(height) == self.pixel_height
    }

    fn point(self, x: f64, y: f64) -> anyhow::Result<(f64, f64)> {
        anyhow::ensure!(
            self.valid()
                && x.is_finite()
                && y.is_finite()
                && x >= 0.0
                && y >= 0.0
                && x < self.pixel_width as f64
                && y < self.pixel_height as f64,
            "desktop coordinates must lie within the bound primary-display image"
        );
        Ok((
            self.x + x * self.width / self.pixel_width as f64,
            self.y + y * self.height / self.pixel_height as f64,
        ))
    }
}

fn geometry() -> Option<Geometry> {
    use core_graphics::display::{CGDisplay, CGDisplayBounds, CGMainDisplayID};
    let generation = display_generation()?;
    let display_id = unsafe { CGMainDisplayID() };
    if display_id == 0 {
        return None;
    }
    let bounds = unsafe { CGDisplayBounds(display_id) };
    let mode = CGDisplay::new(display_id).display_mode()?;
    let value = Geometry {
        generation,
        display_id,
        x: bounds.origin.x,
        y: bounds.origin.y,
        width: bounds.size.width,
        height: bounds.size.height,
        mode_width: mode.width(),
        mode_height: mode.height(),
        pixel_width: mode.pixel_width(),
        pixel_height: mode.pixel_height(),
    };
    (value.valid() && display_generation() == Some(generation)).then_some(value)
}

fn refusal(code: &str, message: &str) -> ToolResult {
    ToolResult::error(message).with_structured(json!({
        "code": code, "effect": "refused", "retryable": false,
        "desktop_binding_version": 1,
    }))
}

fn owner_from_args(args: &Value) -> Result<(Owner, Arc<TransportOwner>), ToolResult> {
    let denied = || {
        refusal(
            "desktop_owner_unavailable",
            "A live canonical desktop transport, session and runtime are required",
        )
    };
    let session_id = args
        .get("_session_id")
        .and_then(Value::as_str)
        .filter(|v| !v.is_empty())
        .ok_or_else(denied)?;
    let transport_session_id = args
        .get("_transport_session_id")
        .and_then(Value::as_str)
        .filter(|v| !v.is_empty())
        .ok_or_else(denied)?;
    let runtime_scope = cua_driver_core::tool::current_dispatch_runtime_scope()
        .filter(|v| !v.is_empty())
        .ok_or_else(denied)?;
    let transport = cua_driver_core::session::current_transport_owner_for(transport_session_id)
        .ok_or_else(denied)?;
    let owner = Owner {
        session_id: session_id.into(),
        transport_session_id: transport_session_id.into(),
        runtime_scope,
    };
    if !owner_live(&owner, &transport) {
        return Err(denied());
    }
    Ok((owner, transport))
}

fn owner_live(owner: &Owner, transport: &TransportOwner) -> bool {
    transport.is_live()
        && !cua_driver_core::session::is_session_ending_or_ended(&owner.session_id)
        && !cua_driver_core::session::is_runtime_scope_suspended(&owner.runtime_scope)
}

struct Binding {
    id: String,
    owner: Owner,
    transport: Arc<TransportOwner>,
    geometry: Geometry,
    issued_ms: u64,
    generation: u64,
    mutation_epoch: u64,
}

impl Binding {
    fn fresh(&self, now: u64) -> bool {
        now >= self.issued_ms && now - self.issued_ms < OBSERVATION_TTL_MS
    }

    fn validate(
        &self,
        owner: &Owner,
        transport: &Arc<TransportOwner>,
        now: u64,
        display: Option<Geometry>,
        activity: Snapshot,
    ) -> Result<(), &'static str> {
        if self.owner != *owner || !Arc::ptr_eq(&self.transport, transport) {
            return Err("desktop_observation_owner_mismatch");
        }
        if !self.fresh(now) {
            return Err("desktop_observation_stale");
        }
        if display != Some(self.geometry) || !self.geometry.valid() {
            return Err("desktop_display_changed");
        }
        if !activity.reliable || activity.generation != self.generation {
            return Err("desktop_activity_changed");
        }
        Ok(())
    }
}

fn registry() -> &'static Mutex<VecDeque<Binding>> {
    static REGISTRY: OnceLock<Mutex<VecDeque<Binding>>> = OnceLock::new();
    REGISTRY.get_or_init(|| Mutex::new(VecDeque::new()))
}

fn take_binding(records: &mut VecDeque<Binding>, id: &str) -> Option<Binding> {
    let index = records.iter().position(|record| record.id == id)?;
    records.remove(index)
}

pub(crate) struct Capture {
    owner: Owner,
    transport: Arc<TransportOwner>,
    pub(crate) geometry: Geometry,
    activity: Snapshot,
    started_ms: u64,
    mutation_epoch: u64,
    authority: Arc<cua_driver_core::desktop_authority::Lease>,
    cancelled: Arc<AtomicBool>,
    _writer: tokio::sync::OwnedMutexGuard<()>,
}

impl Capture {
    pub(crate) fn begin(args: &Value) -> Result<Self, ToolResult> {
        let (owner, transport) = owner_from_args(args)?;
        let authority = cua_driver_core::desktop_authority::current().ok_or_else(|| {
            refusal(
                "desktop_owner_unavailable",
                "Desktop capture requires canonical mutation serialization",
            )
        })?;
        let mutation_epoch = authority.observation_epoch().ok_or_else(|| {
            refusal(
                "desktop_busy",
                "Desktop capture cannot overlap native mutation or unsettled cleanup",
            )
        })?;
        let writer = foreground_writer().try_lock_owned().map_err(|_| {
            refusal(
                "desktop_busy",
                "Native foreground input is in progress; no desktop binding was created",
            )
        })?;
        let activity = snapshot();
        let geometry = geometry().ok_or_else(|| {
            refusal(
                "desktop_display_unavailable",
                "Stable primary-display geometry is unavailable",
            )
        })?;
        Ok(Self {
            owner,
            transport,
            geometry,
            activity,
            started_ms: clock_ms(),
            mutation_epoch,
            authority,
            cancelled: Arc::new(AtomicBool::new(false)),
            _writer: writer,
        })
    }

    pub(crate) fn cancellation_guard(&self) -> CaptureCancellation {
        CaptureCancellation(Arc::clone(&self.cancelled))
    }

    pub(crate) fn cleanup_unknown(&self) {
        self.authority.cleanup_unknown();
    }

    pub(crate) fn check(&self) -> Result<(), ToolResult> {
        if self.cancelled.load(Ordering::Acquire) || !owner_live(&self.owner, &self.transport) {
            return Err(refusal(
                "desktop_owner_unavailable",
                "Desktop capture owner ended or request was cancelled",
            ));
        }
        let now = clock_ms();
        if now < self.started_ms || now - self.started_ms >= CAPTURE_LIMIT_MS {
            return Err(refusal(
                "desktop_observation_stale",
                "Desktop capture exceeded its bounded lifetime",
            ));
        }
        let after = snapshot();
        if !self.activity.reliable
            || !after.reliable
            || self.activity.generation != after.generation
            || self.authority.observation_epoch() != Some(self.mutation_epoch)
        {
            return Err(refusal(
                "desktop_activity_changed",
                "Desktop capture activity or native mutation authority changed",
            ));
        }
        if geometry() != Some(self.geometry) {
            return Err(refusal(
                "desktop_display_changed",
                "Primary display changed during desktop capture",
            ));
        }
        Ok(())
    }

    pub(crate) fn finish(self, width: u32, height: u32) -> Result<String, ToolResult> {
        self.check()?;
        let now = clock_ms();
        let after = snapshot();
        if !owner_live(&self.owner, &self.transport) {
            return Err(refusal(
                "desktop_owner_unavailable",
                "The desktop observation owner ended during capture",
            ));
        }
        if now < self.started_ms
            || now - self.started_ms >= OBSERVATION_TTL_MS
            || !self.activity.reliable
            || !after.reliable
            || self.activity.generation != after.generation
        {
            return Err(refusal("desktop_activity_changed", "Reliable unchanged activity is required across desktop capture; no action binding was created"));
        }
        if geometry() != Some(self.geometry) || !self.geometry.matches_capture(width, height) {
            return Err(refusal(
                "desktop_display_changed",
                "The primary display changed or its image geometry could not be calibrated",
            ));
        }
        let id = format!("desktop_{}", uuid::Uuid::new_v4().simple());
        let mut records = registry().lock().unwrap_or_else(|e| e.into_inner());
        records.retain(|record| {
            record.fresh(now)
                && owner_live(&record.owner, &record.transport)
                && !(record.owner == self.owner && Arc::ptr_eq(&record.transport, &self.transport))
        });
        while records.len() >= MAX_OBSERVATIONS {
            records.pop_front();
        }
        records.push_back(Binding {
            id: id.clone(),
            owner: self.owner,
            transport: self.transport,
            geometry: self.geometry,
            issued_ms: now,
            generation: after.generation,
            mutation_epoch: self.mutation_epoch,
        });
        Ok(id)
    }
}

pub(crate) struct CaptureCancellation(Arc<AtomicBool>);
impl Drop for CaptureCancellation {
    fn drop(&mut self) {
        self.0.store(true, Ordering::Release);
    }
}

pub(super) struct Admission {
    binding: Binding,
    started_ms: u64,
    pub(super) lease: EpisodeLease,
    authority: Arc<cua_driver_core::desktop_authority::Lease>,
    // The context and its blocking workers retain this even after cancellation.
    _writer: tokio::sync::OwnedMutexGuard<()>,
}

pub(super) fn admit(args: &Value, tool: &str) -> Result<Admission, ToolResult> {
    if args.get("scope").and_then(Value::as_str) != Some("desktop")
        || !matches!(tool, "click" | "drag" | "press_key" | "hotkey")
        || [
            "pid",
            "window_id",
            "element_index",
            "element_token",
            "foreground_segment_id",
            "capture_scope",
        ]
        .iter()
        .any(|key| args.get(*key).is_some())
        || args
            .get("delivery_mode")
            .is_some_and(|mode| mode.as_str() != Some("foreground"))
    {
        return Err(refusal("desktop_target_invalid", "Desktop input requires an explicit windowless target and cannot inherit an app or foreground segment"));
    }
    let (owner, transport) = owner_from_args(args)?;
    let id = args
        .get("desktop_observation_id")
        .and_then(Value::as_str)
        .filter(|id| !id.is_empty() && id.len() <= 128)
        .ok_or_else(|| {
            refusal(
                "desktop_observation_required",
                "Observe the desktop before one desktop action",
            )
        })?;
    // Consume before all remaining checks: a refusal or uncertain result never
    // permits replay, including a later retry with recovered activity evidence.
    let binding = take_binding(
        &mut registry().lock().unwrap_or_else(|e| e.into_inner()),
        id,
    )
    .ok_or_else(|| {
        refusal(
            "desktop_observation_stale",
            "Desktop observation is unknown, consumed or retired",
        )
    })?;
    let authority = cua_driver_core::desktop_authority::current().ok_or_else(|| {
        refusal(
            "desktop_owner_unavailable",
            "Desktop input requires canonical mutation serialization",
        )
    })?;
    if !authority.admits_observation(binding.mutation_epoch) {
        return Err(refusal(
            "desktop_observation_stale",
            "Native mutation occurred after desktop observation; no input was sent",
        ));
    }
    let writer = foreground_writer().try_lock_owned().map_err(|_| {
        refusal(
            "desktop_busy",
            "Native foreground input is already in progress",
        )
    })?;
    let now = clock_ms();
    let activity = snapshot();
    binding.validate(&owner, &transport, now, geometry(), activity)
        .map_err(|code| refusal(code, "Desktop observation no longer matches this request, display or activity; no input was sent"))?;
    if !owner_live(&owner, &transport) {
        return Err(refusal(
            "desktop_owner_unavailable",
            "Desktop owner ended before input",
        ));
    }
    let lease = EpisodeLease::begin(now, activity).ok_or_else(|| admission_refusal(
        activity_admission_reason(activity), activity, "Desktop input requires five seconds of reliable native idle evidence; no input was dispatched"))?;
    Ok(Admission {
        binding,
        started_ms: now,
        lease,
        authority,
        _writer: writer,
    })
}

impl Admission {
    pub(super) fn check(&self) -> anyhow::Result<()> {
        let now = clock_ms();
        anyhow::ensure!(self.authority.is_current() && action_permitted(self.started_ms, now, self.lease,
            owner_live(&self.binding.owner, &self.binding.transport), snapshot(),
            self.binding.geometry, geometry()),
            "foreground_activity_interrupted: desktop activity, display, owner or bounded lifetime changed");
        Ok(())
    }
}

fn action_permitted(
    started_ms: u64,
    now: u64,
    lease: EpisodeLease,
    owner_live: bool,
    activity: Snapshot,
    expected: Geometry,
    current: Option<Geometry>,
) -> bool {
    now >= started_ms
        && now - started_ms < ACTION_LIMIT_MS
        && owner_live
        && lease.permits(now, activity)
        && current == Some(expected)
}

pub(crate) fn screenshot_point(x: f64, y: f64) -> anyhow::Result<(f64, f64)> {
    let context =
        current_invocation().ok_or_else(|| anyhow::anyhow!("owned desktop invocation required"))?;
    context.check()?;
    context
        .desktop
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("owned desktop observation required"))?
        .binding
        .geometry
        .point(x, y)
}

/// This route intentionally has no PID/window activation or restoration hook.
pub(crate) fn run<T>(work: impl FnOnce() -> anyhow::Result<T>) -> anyhow::Result<T> {
    check_invocation(true)?;
    anyhow::ensure!(
        current_invocation().is_some_and(|context| context.desktop.is_some()),
        "owned desktop invocation required"
    );
    anyhow::ensure!(
        !DESKTOP_EPISODE.with(Cell::get)
            && LEASE.with(Cell::get).is_none()
            && PRESSED.with(|held| held.borrow().is_empty()),
        "nested or unsettled desktop input"
    );
    DESKTOP_EPISODE.with(|slot| slot.set(true));
    run_without_activation(
        || check_invocation(true),
        work,
        || {
            let remaining = release_owned_inputs();
            DESKTOP_EPISODE.with(|slot| slot.set(false));
            remaining
        },
    )
}

fn run_without_activation<T>(
    check: impl Fn() -> anyhow::Result<()>,
    work: impl FnOnce() -> anyhow::Result<T>,
    cleanup: impl FnOnce() -> bool,
) -> anyhow::Result<T> {
    struct Cleanup<F: FnOnce() -> bool>(Option<F>);
    impl<F: FnOnce() -> bool> Cleanup<F> {
        fn settle(&mut self) -> bool {
            self.0.take().is_some_and(|cleanup| cleanup())
        }
    }
    impl<F: FnOnce() -> bool> Drop for Cleanup<F> {
        fn drop(&mut self) {
            self.settle();
        }
    }
    let mut cleanup = Cleanup(Some(cleanup));
    check()?;
    let result = work();
    let remaining = cleanup.settle();
    check()?;
    anyhow::ensure!(
        !remaining || result.is_err(),
        "desktop action left held controls; owned cleanup completed"
    );
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn display() -> Geometry {
        Geometry {
            generation: 1,
            display_id: 1,
            x: 0.0,
            y: 0.0,
            width: 1000.0,
            height: 500.0,
            mode_width: 1000,
            mode_height: 500,
            pixel_width: 2000,
            pixel_height: 1000,
        }
    }
    fn idle() -> Snapshot {
        Snapshot {
            reliable: true,
            state: State::Idle,
            idle_ms: 5000,
            generation: 9,
        }
    }
    fn binding() -> Binding {
        Binding {
            id: "opaque".into(),
            owner: Owner {
                session_id: "canonical-session".into(),
                runtime_scope: "runtime".into(),
                transport_session_id: "transport".into(),
            },
            transport: TransportOwner::new("transport".into()),
            geometry: display(),
            issued_ms: 100,
            generation: 9,
            mutation_epoch: 0,
        }
    }

    #[test]
    fn unowned_desktop_execution_and_forged_capture_context_do_not_reach_native_work() {
        let called = Cell::new(false);
        let result: anyhow::Result<()> = run(|| {
            called.set(true);
            Ok(())
        });
        assert!(result.is_err());
        assert!(!called.get());
        let result =
            Capture::begin(&json!({"_session_id":"forged", "_transport_session_id":"forged"}));
        assert!(
            matches!(result, Err(refusal) if refusal.structured_content.as_ref()
            .is_some_and(|value| value["code"] == "desktop_owner_unavailable"))
        );
    }

    #[test]
    fn stale_consumed_and_cross_owner_observations_never_replay() {
        let original = binding();
        let mut owner = original.owner.clone();
        let transport = Arc::clone(&original.transport);
        let mut records = VecDeque::from([original]);
        let consumed = take_binding(&mut records, "opaque").unwrap();
        assert!(take_binding(&mut records, "opaque").is_none());
        assert!(consumed
            .validate(&owner, &transport, 101, Some(display()), idle())
            .is_ok());
        for time in [99, 100 + OBSERVATION_TTL_MS] {
            assert_eq!(
                consumed.validate(&owner, &transport, time, Some(display()), idle()),
                Err("desktop_observation_stale")
            );
        }
        owner.session_id = "another-session".into();
        assert_eq!(
            consumed.validate(&owner, &transport, 101, Some(display()), idle()),
            Err("desktop_observation_owner_mismatch")
        );
        owner = consumed.owner.clone();
        owner.runtime_scope = "replacement-runtime".into();
        assert_eq!(
            consumed.validate(&owner, &transport, 101, Some(display()), idle()),
            Err("desktop_observation_owner_mismatch")
        );
        let replacement = TransportOwner::new("transport".into());
        assert_eq!(
            consumed.validate(&consumed.owner, &replacement, 101, Some(display()), idle()),
            Err("desktop_observation_owner_mismatch")
        );
    }

    #[test]
    fn desktop_action_revokes_on_activity_owner_display_or_deadline_change() {
        let lease = EpisodeLease::begin(100, idle()).unwrap();
        let check = |now, live, activity, geometry| {
            action_permitted(100, now, lease, live, activity, display(), geometry)
        };
        assert!(check(101, true, idle(), Some(display())));
        assert!(!check(99, true, idle(), Some(display())));
        assert!(!check(100 + ACTION_LIMIT_MS, true, idle(), Some(display())));
        assert!(!check(101, false, idle(), Some(display())));
        assert!(!check(101, true, idle(), None));
        assert!(!check(
            101,
            true,
            Snapshot {
                reliable: false,
                ..idle()
            },
            Some(display())
        ));
        assert!(!check(
            101,
            true,
            Snapshot {
                generation: 10,
                ..idle()
            },
            Some(display())
        ));
        // Becoming idle again cannot revive the old generation.
        assert!(!check(
            6000,
            true,
            Snapshot {
                generation: 10,
                ..idle()
            },
            Some(display())
        ));
    }

    #[test]
    fn capture_and_pointer_geometry_fail_closed() {
        assert!(display().matches_capture(2000, 1000));
        assert!(!display().matches_capture(1000, 500));
        assert_eq!(display().point(1000.0, 500.0).unwrap(), (500.0, 250.0));
        for (x, y) in [
            (f64::NAN, 0.0),
            (0.0, f64::INFINITY),
            (-1.0, 0.0),
            (2000.0, 0.0),
            (0.0, 1000.0),
        ] {
            assert!(display().point(x, y).is_err());
        }
        let invalid = Geometry {
            width: 0.0,
            ..display()
        };
        assert!(!invalid.matches_capture(2000, 1000));
        let b = binding();
        for changed in [
            None,
            Some(Geometry {
                generation: 2,
                ..display()
            }),
            Some(Geometry {
                display_id: 2,
                ..display()
            }),
            Some(Geometry {
                x: 1.0,
                ..display()
            }),
            Some(invalid),
        ] {
            assert_eq!(
                b.validate(&b.owner, &b.transport, 101, changed, idle()),
                Err("desktop_display_changed")
            );
        }
        for activity in [
            Snapshot {
                reliable: false,
                ..idle()
            },
            Snapshot {
                generation: 10,
                ..idle()
            },
        ] {
            assert_eq!(
                b.validate(&b.owner, &b.transport, 101, Some(display()), activity),
                Err("desktop_activity_changed")
            );
        }
    }

    #[test]
    fn desktop_work_has_only_action_and_owned_cleanup_even_on_interruption_or_unwind() {
        use std::cell::RefCell;
        let held = RefCell::new(PressedInputs::default());
        let released = RefCell::new(Vec::new());
        let result: anyhow::Result<()> = run_without_activation(
            || Ok(()),
            || {
                held.borrow_mut()
                    .press(InputControl::Key(55), "cmd-up")
                    .unwrap();
                held.borrow_mut()
                    .press(InputControl::Mouse(0), "mouse-up")
                    .unwrap();
                anyhow::bail!("activity interrupted");
            },
            || {
                released
                    .borrow_mut()
                    .extend(held.borrow_mut().drain_reversed());
                true
            },
        );
        assert!(result.is_err());
        assert_eq!(*released.borrow(), ["mouse-up", "cmd-up"]);
        assert!(held.borrow().is_empty());
        let cleanup = Cell::new(0);
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _: anyhow::Result<()> = run_without_activation(
                || Ok(()),
                || panic!("worker unwind"),
                || {
                    cleanup.set(cleanup.get() + 1);
                    false
                },
            );
        }));
        assert!(panic.is_err());
        assert_eq!(cleanup.get(), 1);
        let called = Cell::new(false);
        let denied: anyhow::Result<()> = run_without_activation(
            || anyhow::bail!("cancelled before input"),
            || {
                called.set(true);
                Ok(())
            },
            || false,
        );
        assert!(denied.is_err());
        assert!(!called.get());
    }
}
