//! Content-free timing only. These values never grant or extend input authority.
//! Span records are written after the measured operation finishes. Their
//! monotonic fields record event times; log-line order is not event order.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::OnceLock;
use std::time::Instant;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CheckSource {
    ActivePoll,
    DeferredPoll,
    ImmediateReport,
    ReportPoll,
}

impl CheckSource {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::ActivePoll => "active_poll",
            Self::DeferredPoll => "deferred_poll",
            Self::ImmediateReport => "immediate_report",
            Self::ReportPoll => "report_poll",
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) enum Phase {
    AxDispatch,
    CosmeticGeometry,
    OrderingPoll,
    OrderingCheck,
    OrderingRaise,
}

impl Phase {
    fn label(self) -> &'static str {
        match self {
            Self::AxDispatch => "ax_dispatch",
            Self::CosmeticGeometry => "cosmetic_geometry",
            Self::OrderingPoll => "ordering_poll",
            Self::OrderingCheck => "ordering_check",
            Self::OrderingRaise => "ordering_raise",
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct PollTiming {
    pub(crate) wait_started: Instant,
    pub(crate) scheduled_wake: Instant,
    pub(crate) woke: Instant,
}

impl PollTiming {
    fn durations_at(self, callback_started: Instant) -> [u64; 3] {
        [
            micros(
                self.scheduled_wake
                    .saturating_duration_since(self.wait_started),
            ),
            micros(self.woke.saturating_duration_since(self.wait_started)),
            micros(callback_started.saturating_duration_since(self.woke)),
        ]
    }
}

#[derive(Clone, Copy)]
pub(crate) struct PollDiagnostics {
    pub(crate) source: CheckSource,
    pub(crate) timing: PollTiming,
}

fn micros(duration: std::time::Duration) -> u64 {
    duration.as_micros().min(u64::MAX as u128) as u64
}

pub(crate) fn monotonic_us() -> u64 {
    static ORIGIN: OnceLock<Instant> = OnceLock::new();
    micros(ORIGIN.get_or_init(Instant::now).elapsed())
}

const CALLSITE_RECORD_LIMIT: u64 = 128;

/// Contain only diagnostic acquisition/emission, especially inside an extern
/// C callback. This catches unwinding panics, not panic=abort or native faults.
/// Never put an AppKit call, transport or other business operation inside it.
pub(crate) fn diagnostic_only<T>(diagnostic: impl FnOnce() -> T) -> Option<T> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(diagnostic)) {
        Ok(value) => Some(value),
        Err(payload) => {
            // A subscriber may panic with a payload whose destructor also
            // panics. Do not let that destructor unwind across the FFI edge.
            std::mem::forget(payload);
            None
        }
    }
}

/// Diagnostic output only: never a limit on the operation being measured.
/// Each site emits at most 128 records and one explicit saturation notice.
pub(crate) struct LimitedCallsite {
    name: &'static str,
    count: AtomicU64,
}

impl LimitedCallsite {
    pub(crate) const fn new(name: &'static str) -> Self {
        Self {
            name,
            count: AtomicU64::new(0),
        }
    }

    fn sequence_if_enabled(&self, enabled: bool) -> Option<u64> {
        if !enabled {
            return None;
        }
        self.count
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |count| {
                if count <= CALLSITE_RECORD_LIMIT {
                    Some(count + 1)
                } else {
                    None
                }
            })
            .ok()
            .map(|previous| previous + 1)
    }

    pub(crate) fn begin(&self) -> Option<CallMeasurement> {
        diagnostic_only(|| {
            let sequence = self.sequence_if_enabled(
                tracing::enabled!(target: "cua_window_order", tracing::Level::DEBUG),
            )?;
            Some(CallMeasurement {
                callsite: self.name,
                sequence,
                started_ns: uptime_ns(),
            })
        })
        .flatten()
    }
}

fn checked_uptime(status: i32, seconds: i64, nanos: i64) -> Option<u64> {
    if status != 0 || !(0..1_000_000_000).contains(&nanos) {
        return None;
    }
    u64::try_from(seconds)
        .ok()?
        .checked_mul(1_000_000_000)?
        .checked_add(nanos as u64)
}

/// Process-independent CLOCK_UPTIME_RAW nanoseconds, also used by the
/// independent sampler. Failure stays explicit; UTC is not a fallback.
pub(crate) fn uptime_ns() -> Option<u64> {
    let mut time = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    let status = unsafe { libc::clock_gettime(libc::CLOCK_UPTIME_RAW, &mut time) };
    checked_uptime(status, time.tv_sec, time.tv_nsec)
}

pub(crate) struct CallMeasurement {
    callsite: &'static str,
    sequence: u64,
    started_ns: Option<u64>,
}

impl CallMeasurement {
    pub(crate) fn sequence(&self) -> Option<u64> {
        (self.sequence <= CALLSITE_RECORD_LIMIT).then_some(self.sequence)
    }

    pub(crate) fn started_ns(&self) -> Option<u64> {
        self.started_ns
    }

    pub(crate) fn timestamp(&self) -> Option<u64> {
        self.sequence().and_then(|_| uptime_ns())
    }

    /// Call only after the existing operation. stderr is synchronous and can
    /// still delay subsequent work; these diagnostics are not timing-neutral.
    pub(crate) fn finish(self) -> Option<CallTiming> {
        diagnostic_only(|| {
            let finished_ns = uptime_ns();
            if self.sequence > CALLSITE_RECORD_LIMIT {
                tracing::debug!(
                    target: "cua_window_order",
                    diagnostic_site = self.callsite,
                    diagnostic_saturated = true,
                    record_limit = CALLSITE_RECORD_LIMIT,
                    clock = "CLOCK_UPTIME_RAW",
                    started_ns = self.started_ns,
                    finished_ns,
                    "Window/input diagnostic record limit reached"
                );
                return None;
            }
            Some(CallTiming {
                sequence: self.sequence,
                started_ns: self.started_ns,
                finished_ns,
            })
        })
        .flatten()
    }
}

pub(crate) struct CallTiming {
    pub(crate) sequence: u64,
    pub(crate) started_ns: Option<u64>,
    pub(crate) finished_ns: Option<u64>,
}

#[derive(Clone, Copy)]
pub(crate) struct Trace {
    id: u64,
    clock: fn() -> u64,
}

impl Trace {
    pub(crate) fn new() -> Self {
        static NEXT_ID: AtomicU64 = AtomicU64::new(1);
        Self {
            id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
            clock: monotonic_us,
        }
    }

    pub(crate) fn id(self) -> u64 {
        self.id
    }

    pub(crate) fn span(self, phase: Phase, source: Option<CheckSource>) -> Span {
        let started = (self.clock)();
        Span {
            trace: self,
            phase,
            source,
            started,
        }
    }

    pub(crate) fn measure<T>(
        self,
        phase: Phase,
        source: Option<CheckSource>,
        action: impl FnOnce() -> T,
    ) -> T {
        let _span = self.span(phase, source);
        action()
    }

    pub(crate) fn record_poll(self, poll: PollDiagnostics) {
        // This is the guard callback entry: queue time includes spawn_blocking
        // and the existing dispatcher/guard locks, not just executor scheduling.
        let [requested_wait_us, actual_wait_us, callback_queue_us] =
            poll.timing.durations_at(Instant::now());
        tracing::debug!(target: "cua_window_order", order_trace_id=self.id,
            monotonic_us=(self.clock)(), phase="poll_schedule", check_source=poll.source.label(),
            requested_wait_us, actual_wait_us, callback_queue_us,
            "Background ordering diagnostic");
    }

    fn emit(
        self,
        phase: Phase,
        stage: &'static str,
        source: Option<CheckSource>,
        at: u64,
        elapsed: Option<u64>,
    ) {
        tracing::debug!(target: "cua_window_order", order_trace_id=self.id,
            monotonic_us=at, phase=phase.label(), stage,
            check_source=source.map(CheckSource::label).unwrap_or("none"),
            elapsed_us=elapsed, "Background ordering diagnostic");
    }
}

pub(crate) struct Span {
    trace: Trace,
    phase: Phase,
    source: Option<CheckSource>,
    started: u64,
}

impl Drop for Span {
    fn drop(&mut self) {
        let now = (self.trace.clock)();
        // Do not synchronously log between the caller's final input check and
        // its AX action. Preserve the original start/end times when emitting.
        self.trace
            .emit(self.phase, "begin", self.source, self.started, None);
        self.trace.emit(
            self.phase,
            "end",
            self.source,
            now,
            Some(now.saturating_sub(self.started)),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::collections::BTreeMap;
    use std::sync::{Arc, Mutex};
    use std::time::Duration;
    use tracing::field::{Field, Visit};
    use tracing::span::{Attributes, Id, Record};
    use tracing::{Event, Metadata, Subscriber};

    thread_local! { static CLOCK: Cell<u64> = const { Cell::new(0) }; }
    fn fake_clock() -> u64 {
        CLOCK.with(Cell::get)
    }
    fn set_clock(value: u64) {
        CLOCK.with(|clock| clock.set(value));
    }

    #[test]
    fn limited_callsite_has_one_saturation_ticket_then_stops() {
        let site = LimitedCallsite::new("test.limit");
        for expected in 1..=CALLSITE_RECORD_LIMIT + 1 {
            assert_eq!(site.sequence_if_enabled(true), Some(expected));
        }
        for _ in 0..16 {
            assert_eq!(site.sequence_if_enabled(true), None);
        }
        assert_eq!(site.count.load(Ordering::Relaxed), CALLSITE_RECORD_LIMIT + 1);
    }

    #[test]
    fn disabled_callsite_does_not_consume_its_diagnostic_budget() {
        let site = LimitedCallsite::new("test.disabled");
        for _ in 0..16 {
            assert_eq!(site.sequence_if_enabled(false), None);
        }
        assert_eq!(site.count.load(Ordering::Relaxed), 0);
        assert_eq!(site.sequence_if_enabled(true), Some(1));
    }

    #[test]
    fn shared_uptime_rejects_failure_invalid_fields_and_overflow() {
        assert_eq!(checked_uptime(0, 12, 34), Some(12_000_000_034));
        for (status, seconds, nanos) in [
            (-1, 12, 34),
            (0, -1, 0),
            (0, 0, -1),
            (0, 0, 1_000_000_000),
            (0, i64::MAX, 0),
        ] {
            assert_eq!(checked_uptime(status, seconds, nanos), None);
        }
    }

    #[derive(Clone, Default)]
    struct Events(Arc<Mutex<Vec<BTreeMap<String, String>>>>);
    struct Fields(BTreeMap<String, String>);
    impl Visit for Fields {
        fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
            self.0.insert(field.name().to_owned(), format!("{value:?}"));
        }
        fn record_str(&mut self, field: &Field, value: &str) {
            self.0.insert(field.name().to_owned(), value.to_owned());
        }
    }
    impl Subscriber for Events {
        fn enabled(&self, _: &Metadata<'_>) -> bool {
            true
        }
        fn new_span(&self, _: &Attributes<'_>) -> Id {
            Id::from_u64(1)
        }
        fn record(&self, _: &Id, _: &Record<'_>) {}
        fn record_follows_from(&self, _: &Id, _: &Id) {}
        fn event(&self, event: &Event<'_>) {
            let mut fields = Fields(BTreeMap::new());
            event.record(&mut fields);
            self.0.lock().unwrap().push(fields.0);
        }
        fn enter(&self, _: &Id) {}
        fn exit(&self, _: &Id) {}
    }

    struct PanickingSubscriber {
        panic_when_enabled: bool,
    }

    impl Subscriber for PanickingSubscriber {
        fn register_callsite(
            &self,
            _: &'static Metadata<'static>,
        ) -> tracing::subscriber::Interest {
            // Keep subscriber installation non-panicking. Exercise the real
            // protected enabled/event calls rather than callsite registration.
            tracing::subscriber::Interest::sometimes()
        }

        fn enabled(&self, _: &Metadata<'_>) -> bool {
            assert!(!self.panic_when_enabled, "diagnostic enabled panic");
            true
        }

        fn new_span(&self, _: &Attributes<'_>) -> Id {
            Id::from_u64(1)
        }

        fn record(&self, _: &Id, _: &Record<'_>) {}
        fn record_follows_from(&self, _: &Id, _: &Id) {}

        fn event(&self, _: &Event<'_>) {
            panic!("diagnostic event panic");
        }

        fn enter(&self, _: &Id) {}
        fn exit(&self, _: &Id) {}
    }

    #[test]
    fn subscriber_panics_are_contained_by_real_diagnostic_entry_points() {
        let site = LimitedCallsite::new("test.panic");
        tracing::subscriber::with_default(
            PanickingSubscriber {
                panic_when_enabled: true,
            },
            || assert!(site.begin().is_none()),
        );
        assert_eq!(site.count.load(Ordering::Relaxed), 0);

        tracing::subscriber::with_default(
            PanickingSubscriber {
                panic_when_enabled: false,
            },
            || {
                let measurement = CallMeasurement {
                    callsite: "test.panic",
                    sequence: CALLSITE_RECORD_LIMIT + 1,
                    started_ns: Some(1),
                };
                assert!(measurement.finish().is_none());
                assert!(diagnostic_only(|| {
                    tracing::debug!(target: "cua_window_order", "diagnostic emission probe");
                })
                .is_none());
            },
        );
    }

    #[test]
    fn saturation_notice_is_emitted_only_when_the_operation_finishes() {
        let events = Events::default();
        tracing::subscriber::with_default(events.clone(), || {
            let measurement = CallMeasurement {
                callsite: "test.saturation",
                sequence: CALLSITE_RECORD_LIMIT + 1,
                started_ns: Some(1),
            };
            assert!(events.0.lock().unwrap().is_empty());
            assert!(measurement.finish().is_none());
        });
        let rows = events.0.lock().unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0]["diagnostic_site"], "test.saturation");
        assert_eq!(rows[0]["diagnostic_saturated"], "true");
        assert_eq!(rows[0]["record_limit"], CALLSITE_RECORD_LIMIT.to_string());
    }

    #[test]
    fn correlated_events_distinguish_ax_cosmetic_and_each_check_source() {
        let events = Events::default();
        let trace = Trace {
            clock: fake_clock,
            ..Trace::new()
        };
        tracing::subscriber::with_default(events.clone(), || {
            set_clock(100);
            let result = trace.measure(Phase::AxDispatch, None, || {
                set_clock(180);
                Err::<(), _>(37)
            });
            assert_eq!(result, Err(37), "diagnostics preserve the actuator result");
            trace.measure(Phase::CosmeticGeometry, None, || set_clock(200));
            for source in [
                CheckSource::ActivePoll,
                CheckSource::DeferredPoll,
                CheckSource::ImmediateReport,
                CheckSource::ReportPoll,
            ] {
                trace.measure(Phase::OrderingCheck, Some(source), || {
                    set_clock(fake_clock() + 5)
                });
            }
            trace.measure(Phase::OrderingRaise, Some(CheckSource::ActivePoll), || {
                set_clock(240)
            });
        });
        let rows = events.0.lock().unwrap();
        assert_eq!(rows.len(), 14);
        assert!(rows
            .iter()
            .all(|row| row["order_trace_id"] == trace.id().to_string()));
        let ends: Vec<_> = rows.iter().filter(|row| row["stage"] == "end").collect();
        assert_eq!(ends[0]["phase"], "ax_dispatch");
        assert_eq!(ends[0]["monotonic_us"], "180");
        assert_eq!(ends[0]["elapsed_us"], "80");
        assert_eq!(ends[1]["phase"], "cosmetic_geometry");
        assert_eq!(ends[1]["elapsed_us"], "20");
        assert_eq!(
            ends.iter()
                .skip(2)
                .take(4)
                .map(|r| r["check_source"].as_str())
                .collect::<Vec<_>>(),
            [
                "active_poll",
                "deferred_poll",
                "immediate_report",
                "report_poll"
            ]
        );
        assert_eq!(ends[6]["phase"], "ordering_raise");
        assert!(rows.iter().all(|row| row.keys().all(|key| [
            "message",
            "order_trace_id",
            "monotonic_us",
            "phase",
            "stage",
            "check_source",
            "elapsed_us"
        ]
        .contains(&key.as_str()))));
        assert_ne!(Trace::new().id(), trace.id());
    }

    #[test]
    fn poll_wait_and_callback_queue_are_measured_separately_without_sleeping() {
        let start = Instant::now();
        let timing = PollTiming {
            wait_started: start,
            scheduled_wake: start + Duration::from_millis(100),
            woke: start + Duration::from_millis(113),
        };
        assert_eq!(
            timing.durations_at(start + Duration::from_millis(120)),
            [100_000, 113_000, 7_000]
        );
    }

    #[test]
    fn action_runs_before_any_synchronous_span_logging() {
        let events = Events::default();
        let trace = Trace {
            clock: fake_clock,
            ..Trace::new()
        };
        tracing::subscriber::with_default(events.clone(), || {
            for phase in [Phase::AxDispatch, Phase::OrderingRaise] {
                events.0.lock().unwrap().clear();
                set_clock(100);
                let result = trace.measure(phase, Some(CheckSource::ActivePoll), || {
                    assert!(
                        events.0.lock().unwrap().is_empty(),
                        "the action must run before even a begin record is written"
                    );
                    set_clock(180);
                    Err::<(), _>(37)
                });
                assert_eq!(result, Err(37));
                let rows = events.0.lock().unwrap();
                assert_eq!(rows.len(), 2, "both records must be complete on return");
                assert_eq!(rows[0]["stage"], "begin");
                assert_eq!(rows[0]["monotonic_us"], "100");
                assert_eq!(rows[1]["stage"], "end");
                assert_eq!(rows[1]["monotonic_us"], "180");
                assert_eq!(rows[1]["elapsed_us"], "80");
            }
        });
    }

    #[test]
    fn diagnostic_scope_closes_on_early_return_without_replaying_work() {
        let events = Events::default();
        let trace = Trace {
            clock: fake_clock,
            ..Trace::new()
        };
        let calls = Cell::new(0);
        tracing::subscriber::with_default(events.clone(), || {
            set_clock(10);
            assert_eq!(
                trace.measure(
                    Phase::OrderingRaise,
                    Some(CheckSource::ImmediateReport),
                    || {
                        calls.set(calls.get() + 1);
                        set_clock(15);
                        None::<()>
                    }
                ),
                None
            );
        });
        assert_eq!(calls.get(), 1);
        let rows = events.0.lock().unwrap();
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[1]["stage"], "end");
        assert_eq!(rows[1]["elapsed_us"], "5");
    }
}
