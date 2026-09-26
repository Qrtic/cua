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
