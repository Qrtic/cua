//! Content-free diagnostics over an already captured menu/window snapshot.
//! These values never participate in admission. Emit only after the original
//! visibility decision and end timestamp; log-line order is not event order.

const MAX_CANDIDATE_RECORDS: usize = 32;

#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) struct Candidate {
    pub pid: i32,
    pub id: u32,
    pub bounds: [f64; 4],
    pub layer: i32,
    pub on_screen: bool,
    pub on_current_space: Option<bool>,
}

#[derive(Debug, PartialEq)]
struct CandidateRecord {
    candidate: Candidate,
    matches: bool,
}

#[derive(Debug, PartialEq)]
struct Summary {
    frame_status: &'static str,
    candidate_count: usize,
    matching_count: usize,
    records: Vec<CandidateRecord>,
}

fn analyze(
    pid: i32,
    frame: Option<[f64; 4]>,
    candidates: impl IntoIterator<Item = Candidate>,
) -> Summary {
    let frame_status = match frame {
        None => "missing_or_not_read",
        Some(frame) if frame.iter().all(|v| v.is_finite()) && frame[2] > 0.0 && frame[3] > 0.0 => {
            "valid"
        }
        Some(_) => "invalid",
    };
    let mut summary = Summary {
        frame_status,
        candidate_count: 0,
        matching_count: 0,
        records: Vec::new(),
    };
    for candidate in candidates {
        // Do not record unrelated processes or any titles, labels or values.
        if candidate.pid != pid {
            continue;
        }
        summary.candidate_count += 1;
        let matches = frame_status == "valid"
            && candidate.id != 0
            && candidate.layer == 101
            && candidate.on_screen
            && candidate.on_current_space != Some(false)
            && frame
                .unwrap()
                .iter()
                .zip(candidate.bounds)
                .all(|(a, b)| b.is_finite() && (a - b).abs() <= 0.5);
        summary.matching_count += usize::from(matches);
        if summary.records.len() < MAX_CANDIDATE_RECORDS {
            summary.records.push(CandidateRecord { candidate, matches });
        }
    }
    summary
}

pub(super) struct Timing {
    id: u64,
    started: u64,
}

impl Timing {
    pub(super) fn start() -> Self {
        Self {
            id: crate::order_diagnostics::Trace::new().id(),
            started: crate::order_diagnostics::monotonic_us(),
        }
    }

    pub(super) fn refusal_after_match(
        self,
        completed: u64,
        pid: i32,
        frame: Option<[f64; 4]>,
        matched_window: u32,
    ) {
        if !tracing::enabled!(target: "cua_popover_proof", tracing::Level::DEBUG) {
            return;
        }
        // The successful match's snapshot was released before the original
        // final budget check. Do not recapture it or imply an empty snapshot.
        tracing::debug!(target: "cua_popover_proof", menu_trace_id=self.id,
            monotonic_us=self.started, phase="menu_visibility", stage="begin", pid,
            "Deferred menu visibility diagnostic");
        tracing::debug!(target: "cua_popover_proof", menu_trace_id=self.id,
            monotonic_us=completed, phase="menu_visibility", stage="result", pid,
            budget_phase="budget_after_match", ax_menu_rect=?frame,
            matched_window_id=matched_window,
            candidate_snapshot_state="released_before_final_budget_check",
            "Menu visibility refusal after successful match");
        tracing::debug!(target: "cua_popover_proof", menu_trace_id=self.id,
            monotonic_us=completed, phase="menu_visibility", stage="end", pid,
            elapsed_us=completed.saturating_sub(self.started),
            "Deferred menu visibility diagnostic");
    }

    pub(super) fn refusal(
        self,
        completed: u64,
        pid: i32,
        budget_phase: &'static str,
        frame: Option<[f64; 4]>,
        candidates: impl IntoIterator<Item = Candidate>,
    ) {
        if !tracing::enabled!(target: "cua_popover_proof", tracing::Level::DEBUG) {
            return;
        }
        // Only in-memory analysis after the caller's final decision. Count all
        // matches in that finite snapshot, but cap emitted candidate records.
        let summary = analyze(pid, frame, candidates);
        tracing::debug!(target: "cua_popover_proof", menu_trace_id=self.id,
            monotonic_us=self.started, phase="menu_visibility", stage="begin", pid,
            "Deferred menu visibility diagnostic");
        tracing::debug!(target: "cua_popover_proof", menu_trace_id=self.id,
            monotonic_us=completed, phase="menu_visibility", stage="result", pid,
            budget_phase, ax_menu_rect=?frame, frame_status=summary.frame_status,
            candidate_count=summary.candidate_count, matching_count=summary.matching_count,
            candidate_records=summary.records.len(),
            candidates_truncated=(summary.candidate_count > summary.records.len()),
            "Menu visibility refusal snapshot");
        for record in summary.records {
            tracing::debug!(target: "cua_popover_proof", menu_trace_id=self.id,
                monotonic_us=completed, phase="menu_visibility", stage="candidate", pid,
                window_id=record.candidate.id, bounds=?record.candidate.bounds,
                layer=record.candidate.layer, on_screen=record.candidate.on_screen,
                on_current_space=?record.candidate.on_current_space,
                matches=record.matches, "Retained same-process window candidate");
        }
        tracing::debug!(target: "cua_popover_proof", menu_trace_id=self.id,
            monotonic_us=completed, phase="menu_visibility", stage="end", pid,
            elapsed_us=completed.saturating_sub(self.started),
            "Deferred menu visibility diagnostic");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn candidate() -> Candidate {
        Candidate {
            pid: 42,
            id: 9,
            bounds: [1402.0, 113.0, 320.0, 786.0],
            layer: 101,
            on_screen: true,
            on_current_space: Some(true),
        }
    }

    #[test]
    fn menu_diagnostic_distinguishes_missing_invalid_and_exact_frame() {
        let c = candidate();
        assert_eq!(analyze(42, None, [c]).frame_status, "missing_or_not_read");
        for frame in [[0.0, 0.0, 0.0, 786.0], [f64::NAN, 0.0, 320.0, 786.0]] {
            let s = analyze(42, Some(frame), [c]);
            assert_eq!(s.frame_status, "invalid");
            assert_eq!(s.matching_count, 0);
        }
        let s = analyze(42, Some(c.bounds), [c]);
        assert_eq!(s.matching_count, 1);
        assert!(s.records[0].matches);
    }

    #[test]
    fn menu_diagnostic_retains_mismatch_fields_and_exact_tolerance() {
        let c = candidate();
        for mutate in 0..6 {
            let mut changed = c;
            match mutate {
                0 => changed.id = 0,
                1 => changed.layer = 0,
                2 => changed.on_screen = false,
                3 => changed.on_current_space = Some(false),
                4 => changed.bounds[0] += 0.5001,
                _ => changed.bounds[3] = f64::INFINITY,
            }
            let s = analyze(42, Some(c.bounds), [changed]);
            assert_eq!(s.matching_count, 0);
            assert_eq!(s.records[0].candidate, changed);
        }
        let mut boundary = c;
        boundary.bounds[0] += 0.5;
        boundary.on_current_space = None;
        assert_eq!(analyze(42, Some(c.bounds), [boundary]).matching_count, 1);
    }

    #[test]
    fn menu_diagnostic_counts_ambiguity_without_leaking_other_processes() {
        let c = candidate();
        let mut foreign = c;
        foreign.pid = 99;
        let s = analyze(42, Some(c.bounds), [c, foreign, c]);
        assert_eq!(s.candidate_count, 2);
        assert_eq!(s.matching_count, 2);
        assert!(s.records.iter().all(|r| r.candidate.pid == 42));
    }

    #[test]
    fn menu_diagnostic_caps_records_but_preserves_complete_match_count() {
        let c = candidate();
        let s = analyze(
            42,
            Some(c.bounds),
            (0..100).map(|i| Candidate { id: i + 1, ..c }),
        );
        assert_eq!(s.candidate_count, 100);
        assert_eq!(s.matching_count, 100);
        assert_eq!(s.records.len(), MAX_CANDIDATE_RECORDS);
    }

    #[test]
    fn menu_diagnostic_defers_logs_and_keeps_original_event_times() {
        use std::collections::BTreeMap;
        use std::sync::{Arc, Mutex};
        use tracing::field::{Field, Visit};
        use tracing::span::{Attributes, Id, Record};
        use tracing::{Event, Metadata, Subscriber};
        #[derive(Clone, Default)]
        struct Events(Arc<Mutex<Vec<BTreeMap<String, String>>>>);
        struct Fields(BTreeMap<String, String>);
        impl Visit for Fields {
            fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
                self.0.insert(field.name().into(), format!("{value:?}"));
            }
            fn record_str(&mut self, field: &Field, value: &str) {
                self.0.insert(field.name().into(), value.into());
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
            fn enter(&self, _: &Id) {}
            fn exit(&self, _: &Id) {}
            fn event(&self, event: &Event<'_>) {
                let mut fields = Fields(BTreeMap::new());
                event.record(&mut fields);
                self.0.lock().unwrap().push(fields.0);
            }
        }
        let events = Events::default();
        tracing::subscriber::with_default(events.clone(), || {
            let _started_only = Timing::start();
            assert!(events.0.lock().unwrap().is_empty());
            let timing = Timing {
                id: 7,
                started: 100,
            };
            timing.refusal(
                180,
                42,
                "budget_after_match",
                Some(candidate().bounds),
                [candidate()],
            );
        });
        let rows = events.0.lock().unwrap();
        assert_eq!(rows.len(), 4);
        assert_eq!(rows[0]["stage"], "begin");
        assert_eq!(rows[0]["monotonic_us"], "100");
        assert_eq!(rows[1]["budget_phase"], "budget_after_match");
        assert_eq!(rows[1]["matching_count"], "1");
        assert_eq!(rows[2]["window_id"], "9");
        assert_eq!(rows[3]["stage"], "end");
        assert_eq!(rows[3]["monotonic_us"], "180");
        assert_eq!(rows[3]["elapsed_us"], "80");
        assert!(rows.iter().all(|row| row["menu_trace_id"] == "7"));
        assert!(rows
            .iter()
            .all(|row| !row.contains_key("title") && !row.contains_key("label")));

        let after_match_events = Events::default();
        tracing::subscriber::with_default(after_match_events.clone(), || {
            Timing {
                id: 8,
                started: 200,
            }
            .refusal_after_match(280, 42, Some(candidate().bounds), 9);
        });
        let after_match = after_match_events.0.lock().unwrap();
        assert_eq!(after_match.len(), 3);
        assert_eq!(after_match[0]["monotonic_us"], "200");
        assert_eq!(after_match[1]["budget_phase"], "budget_after_match");
        assert_eq!(after_match[1]["matched_window_id"], "9");
        assert_eq!(
            after_match[1]["candidate_snapshot_state"],
            "released_before_final_budget_check"
        );
        assert_eq!(after_match[2]["monotonic_us"], "280");
        assert!(after_match.iter().all(|row| {
            row["menu_trace_id"] == "8"
                && row["stage"] != "candidate"
                && !row.contains_key("candidate_count")
                && !row.contains_key("matching_count")
                && !row.contains_key("title")
                && !row.contains_key("label")
        }));
    }
}
