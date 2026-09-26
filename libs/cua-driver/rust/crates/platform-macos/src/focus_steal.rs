//! Layer-3 focus-steal preventer — Rust port of Swift's
//! `SystemFocusStealPreventer.swift` plus the PR #1521 4-layer hardening
//! (closure scope, RAII lease, 5s monotonic deadline, 1s janitor).
//!
//! ## What this protects against
//!
//! `NSWorkspace.OpenConfiguration.activates = false` tells LaunchServices
//! "don't activate the target on launch". LaunchServices honors that.
//! What it does NOT do is stop the launched app from calling
//! `NSApp.activate(ignoringOtherApps:)` in its own
//! `applicationDidFinishLaunching`. Chrome, Electron, Safari, Calculator
//! all do exactly that — so a "background" launch flashes the target on
//! top of the user's work for a few frames.
//!
//! The preventer subscribes to
//! `NSWorkspace.didActivateApplicationNotification` and, when an activation
//! matches a registered suppression entry, submits an exact prior-window
//! restore only while native activity coverage and generation remain valid.
//! Human/unknown input or a monitoring gap invalidates that restoration lease.
//!
//! ## Layered design (matches PR #1521)
//!
//! 1. **Closure API** — `with_suppression(target, restore_to, origin, f)`
//!    begins an entry, awaits `f`, ends the entry. Use this when the
//!    suppression scope is a single async block.
//! 2. **RAII API** — `begin_suppression(target, restore_to, origin)`
//!    returns a `SuppressionLease`. `Drop` ends the entry synchronously
//!    (no awaiting). Use this when the caller needs to hold the lease
//!    across multiple branches or when async cancellation may interrupt
//!    the closure path.
//! 3. **5s monotonic deadline** — every entry stamps an
//!    `Instant::now() + 5s`. The observer prunes expired entries before
//!    matching, so a leaked lease can't cause a stale entry to keep
//!    re-activating the prior frontmost app forever.
//! 4. **1s janitor** — a tokio interval task wakes up every second
//!    while the dispatcher is non-empty, prunes expired entries, and
//!    stops when the map drains. Re-starts when the next entry is
//!    added. Coordinated via `tokio::sync::watch`.
//!
//! ## Singleton
//!
//! `FocusStealPreventer::shared()` returns a process-wide
//! `Arc<FocusStealPreventer>`. The observer registration happens inside
//! `OnceLock::get_or_init`, so it's safe to call from any thread without
//! racing on observer install.
//!
//! ## Why a fresh background `NSOperationQueue` (not `mainQueue`)
//!
//! NSWorkspace's block-based observer fires on the queue you give it. If
//! the queue is `nil` (Swift default) or `mainQueue`, the block runs on
//! the main thread — which means it requires a live main run loop.
//! `cua-driver call` (one-shot subcommand) and `--no-overlay` mode don't
//! have one, so the activation observer would never fire. A fresh
//! background `NSOperationQueue` sidesteps that — the block runs on the
//! queue's own thread regardless of run-loop state.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Duration, Instant};

use objc2_app_kit::{
    NSWorkspace, NSWorkspaceApplicationKey, NSWorkspaceDidActivateApplicationNotification,
};
use objc2_foundation::NSOperationQueue;
use uuid::Uuid;

/// Per-entry deadline. After this much wall-clock time the dispatcher's
/// observer (and the janitor) treats the entry as leaked and prunes it
/// without firing. Mirrors Swift PR #1521.
pub(crate) const ENTRY_DEADLINE: Duration = Duration::from_secs(5);

/// Janitor tick interval. The task wakes up this often while the
/// dispatcher is non-empty and prunes expired entries.
const JANITOR_TICK: Duration = Duration::from_secs(1);

// The activation notification can overtake NSWorkspace.frontmostApplication.
// Recheck that specific notification briefly; never turn it into a renewable
// focus lock or a new suppression entry.
const ACTIVATION_RECHECK_INTERVAL: Duration = Duration::from_millis(25);
const ACTIVATION_RECHECK_LIMIT: usize = 10;

/// Identifier for a suppression. `with_suppression` and `begin_suppression`
/// hand one of these back; `end_suppression` consumes it.
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
pub struct SuppressionHandle(Uuid);

/// Dispatcher-internal entry shape.
#[derive(Debug)]
struct Entry {
    activity_restore: Option<crate::foreground_activity::RestoreEvidence>,
    /// `Some(pid)` matches only that pid's activations. `None` is a
    /// wildcard — matches any activation whose pid != `restore_to`.
    /// The wildcard variant is used while a launch is in flight and the
    /// real pid isn't known yet.
    target_pid: Option<i32>,
    /// One intentional activation that a wildcard entry must allow through.
    ///
    /// Raw background pixel clicks use the focus-without-raise recipe: the
    /// target must become AppKit-active long enough for its event queue to
    /// accept the click, while activations of every *other* app should still
    /// be suppressed as cross-app side effects.
    allowed_pid: Option<i32>,
    /// Pid to restore focus to when an activation matches this entry.
    restore_to: i32,
    /// Monotonic deadline. After this, the entry is pruned without
    /// firing.
    deadline: Instant,
    /// An ordinary background action has returned, but this target-only
    /// protection tail remains until its original bounded settle deadline.
    returned_tail: bool,
    /// Provenance for tracing — e.g. `"LaunchAppTool.pre"`.
    #[allow(dead_code)]
    origin: &'static str,
}

/// Keep the authorizing entry identity until the restore is actually submitted.
#[derive(Clone, Copy, Debug)]
struct RestoreCandidate {
    handle: SuppressionHandle,
    activated_pid: i32,
    restore_to: i32,
}

/// Created only after this candidate's native submission succeeds. It grants
/// no new lease, time or destination; completion still validates the original
/// entry and captured activity/window evidence before each AX operation.
#[derive(Clone, Copy, Debug)]
struct RestoreCompletion {
    candidate: RestoreCandidate,
    evidence: crate::foreground_activity::RestoreEvidence,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ActivationRecheck {
    Waiting,
    Ready,
    Revoked,
}

/// Singleton focus-steal preventer.
///
/// Constructed lazily on first `shared()` call. Owns the dispatcher state
/// (Sync via the inner Mutex); the NSWorkspace observer + queue are
/// intentionally retained-and-forgotten on install so their lifetime is
/// the whole process and we don't need to thread `!Send` Cocoa handles
/// through this struct.
pub struct FocusStealPreventer {
    dispatcher: Arc<Dispatcher>,
}

impl FocusStealPreventer {
    /// Return (or initialize on first call) the process-wide singleton.
    pub fn shared() -> Arc<Self> {
        static SINGLETON: OnceLock<Arc<FocusStealPreventer>> = OnceLock::new();
        SINGLETON
            .get_or_init(|| {
                let dispatcher = Arc::new(Dispatcher::new());
                install_observer(&dispatcher);
                Arc::new(FocusStealPreventer { dispatcher })
            })
            .clone()
    }

    /// Begin suppressing focus-steals targeting `target_pid` (or any pid
    /// when `None`, the wildcard). Returns a `SuppressionLease` whose
    /// `Drop` ends the entry synchronously.
    ///
    /// `restore_to` is the pid the preventer re-activates if it matches
    /// a notification. `origin` is a static label for tracing.
    pub fn begin_suppression(
        target_pid: Option<i32>,
        restore_to: i32,
        origin: &'static str,
    ) -> SuppressionLease {
        let shared = Self::shared();
        let handle = shared.dispatcher.add(target_pid, restore_to, origin);
        shared
            .dispatcher
            .attach_activity_restore(handle, restore_to);
        SuppressionLease {
            handle,
            dispatcher: Arc::clone(&shared.dispatcher),
            released: false,
            poll_task: None,
        }
    }

    /// Begin wildcard suppression while allowing one intentional activation.
    ///
    /// This is narrower than disabling suppression altogether: activation of
    /// `allowed_pid` is ignored, but any other pid still restores
    /// `restore_to`.
    pub fn begin_suppression_allowing(
        allowed_pid: i32,
        restore_to: i32,
        origin: &'static str,
    ) -> SuppressionLease {
        let shared = Self::shared();
        let handle = shared
            .dispatcher
            .add_allowing(allowed_pid, restore_to, origin);
        shared
            .dispatcher
            .attach_activity_restore(handle, restore_to);
        SuppressionLease {
            handle,
            dispatcher: Arc::clone(&shared.dispatcher),
            released: false,
            poll_task: None,
        }
    }

    /// Run `f` with a suppression entry active. Equivalent to
    /// `begin_suppression(...)` + run `f` + drop the lease — but expressed
    /// as a single async call site.
    pub async fn with_suppression<R, F, Fut>(
        target_pid: Option<i32>,
        restore_to: i32,
        origin: &'static str,
        f: F,
    ) -> R
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = R>,
    {
        let _lease = Self::begin_suppression(target_pid, restore_to, origin);
        f().await
    }
}

/// Begin-suppression convenience that bounces through the singleton.
pub fn begin_suppression(
    target_pid: Option<i32>,
    restore_to: i32,
    origin: &'static str,
) -> SuppressionLease {
    FocusStealPreventer::begin_suppression(target_pid, restore_to, origin)
}

/// Begin wildcard suppression while permitting `allowed_pid` to activate.
pub fn begin_suppression_allowing(
    allowed_pid: i32,
    restore_to: i32,
    origin: &'static str,
) -> SuppressionLease {
    FocusStealPreventer::begin_suppression_allowing(allowed_pid, restore_to, origin)
}

/// End only returned background tails for an intentionally foregrounded target.
/// Active actions, wildcard launch protection, and other targets are unchanged.
pub fn cancel_deferred_suppression(target_pid: i32) {
    FocusStealPreventer::shared()
        .dispatcher
        .cancel_deferred(target_pid);
}

/// RAII lease. `Drop` ends the entry synchronously, so the entry is
/// removed even if a future is cancelled mid-await.
pub struct SuppressionLease {
    handle: SuppressionHandle,
    dispatcher: Arc<Dispatcher>,
    released: bool,
    // This task borrows the entry's authority; it must never own or extend it.
    poll_task: Option<tokio::task::JoinHandle<()>>,
}

impl SuppressionLease {
    /// Narrow an in-flight launch lease without recapturing the old foreground.
    /// The app may already be active when LaunchServices returns. Recapturing
    /// then would lose the original exact-window proof. Keep its generation,
    /// deadline and cancellation identity; never renew or widen the lease.
    pub fn narrow_to(self, target_pid: i32, origin: &'static str) -> Option<Self> {
        self.dispatcher
            .narrow_to(self.handle, target_pid, origin)
            .then_some(self)
    }

    /// Explicit release. Useful if the caller wants to drop the lease
    /// before its scope ends without taking the `Drop` path.
    pub fn release(mut self) {
        self.dispatcher.remove(self.handle);
        self.released = true;
    }

    pub(crate) fn targeted_deadline(&self) -> Option<Instant> {
        self.dispatcher.with_current_targeted(self.handle, |deadline| deadline)
    }

    /// Keep a returned action's target-only protection off its response path.
    /// The original five-second cap still applies. No runtime, a non-targeted
    /// entry, or an already elapsed deadline falls back to normal immediate
    /// Drop. Runtime shutdown also drops the timer-owned lease.
    pub fn defer_release(self, deadline: Instant) {
        let Ok(runtime) = tokio::runtime::Handle::try_current() else {
            return;
        };
        let Some(deadline) = self.dispatcher.mark_deferred(self.handle, deadline) else {
            return;
        };
        runtime.spawn(async move {
            tokio::time::sleep_until(tokio::time::Instant::from_std(deadline)).await;
            drop(self);
        });
    }

    /// Cover the action itself, including an AX call that blocks while AppKit
    /// raises its document. The same single callback survives the response
    /// handoff; it never recaptures the foreground or renews the entry deadline.
    /// Entry removal serializes with each callback. Aborting a task alone would
    /// not stop a spawn_blocking callback which had already begun.
    pub(crate) fn start_polling(
        &mut self,
        mut poll: impl FnMut(Instant) -> bool + Send + 'static,
    ) -> bool {
        if self.poll_task.is_some() { return false; }
        let Ok(runtime) = tokio::runtime::Handle::try_current() else { return false };
        let Some(mut deadline) = self.targeted_deadline() else {
            return false;
        };
        let mut dispatcher = Arc::clone(&self.dispatcher);
        let handle = self.handle;
        tracing::debug!(target: "cua_window_order", lease=%handle.0,
            remaining_ms=deadline.saturating_duration_since(Instant::now()).as_millis() as u64,
            "Started ordering protection during the active action");
        self.poll_task = Some(runtime.spawn(async move {
            loop {
                let next = (Instant::now() + Duration::from_millis(100)).min(deadline);
                tokio::time::sleep_until(tokio::time::Instant::from_std(next)).await;
                if Instant::now() >= deadline { break; }
                let result = tokio::task::spawn_blocking(move || {
                    let keep_polling = dispatcher.with_current_targeted(handle, |current_deadline| {
                        (poll(current_deadline), current_deadline)
                    });
                    (dispatcher, poll, keep_polling)
                }).await;
                let Ok((returned_dispatcher, returned_poll, keep_polling)) = result else { return };
                dispatcher = returned_dispatcher;
                poll = returned_poll;
                match keep_polling {
                    Some((true, current_deadline)) => deadline = deadline.min(current_deadline),
                    Some((false, _)) | None => return,
                }
            }
        }));
        true
    }

    /// Retain the same polling task and focus lease off the response path.
    /// If capture ran without an async runtime, this starts its only poll here.
    /// Returning false from the callback leaves ordinary focus protection alive
    /// until the original deadline; a second callback is never substituted.
    pub(crate) fn defer_release_with_poll(
        mut self,
        deadline: Instant,
        poll: impl FnMut(Instant) -> bool + Send + 'static,
    ) {
        self.start_polling(poll);
        self.defer_release(deadline);
    }
}

impl Drop for SuppressionLease {
    fn drop(&mut self) {
        if !self.released {
            self.dispatcher.remove(self.handle);
        }
        if let Some(task) = self.poll_task.take() {
            task.abort();
        }
    }
}

// ── Dispatcher ──────────────────────────────────────────────────────────────

/// Holds the suppression entries plus the janitor lifecycle.
///
/// `entries` is a `HashMap<Uuid, Entry>` so add/remove are O(1) by handle.
/// Lookups by `(target_pid, restore_to)` during a notification are O(N) —
/// N is at most a handful of in-flight launches at a time so a linear
/// scan is fine.
pub(crate) struct Dispatcher {
    entries: Mutex<HashMap<Uuid, Entry>>,
    /// `true` while the janitor task should keep running. The janitor
    /// loop watches for transitions to detect when to start/stop.
    janitor_active: tokio::sync::watch::Sender<bool>,
    janitor_started: Mutex<bool>,
}

impl Dispatcher {
    fn with_current_targeted<T>(&self, handle: SuppressionHandle, poll: impl FnOnce(Instant) -> T) -> Option<T> {
        let entries = self.entries.lock().unwrap();
        let entry = entries.get(&handle.0)?;
        if entry.target_pid.is_none() || entry.deadline <= Instant::now() {
            return None;
        }
        Some(poll(entry.deadline))
    }

    fn attach_activity_restore(&self, handle: SuppressionHandle, pid: i32) {
        let evidence = crate::foreground_activity::capture_restore(pid);
        if let Some(entry) = self.entries.lock().unwrap().get_mut(&handle.0) {
            entry.activity_restore = evidence;
            tracing::debug!(target: "cua_focus_restore", origin = entry.origin,
                lease = %handle.0, target_pid = ?entry.target_pid,
                restore_pid = pid, has_restore_evidence = evidence.is_some(),
                "Captured launch/action restoration evidence");
        }
    }

    fn narrow_to(&self, handle: SuppressionHandle, target_pid: i32, origin: &'static str) -> bool {
        let mut entries = self.entries.lock().unwrap();
        let Some(entry) = entries.get_mut(&handle.0) else {
            return false;
        };
        if target_pid <= 0
            || entry.target_pid.is_some()
            || entry.allowed_pid.is_some()
            || entry.restore_to == target_pid
            || entry.returned_tail
            || entry.deadline <= Instant::now()
        {
            return false;
        }
        entry.target_pid = Some(target_pid);
        entry.origin = origin;
        tracing::debug!(target: "cua_focus_restore", origin,
            target_pid, restore_pid = entry.restore_to,
            has_restore_evidence = entry.activity_restore.is_some(),
            "Narrowed launch lease with original restoration evidence");
        true
    }

    fn new() -> Self {
        let (tx, _rx) = tokio::sync::watch::channel(false);
        Self {
            entries: Mutex::new(HashMap::new()),
            janitor_active: tx,
            janitor_started: Mutex::new(false),
        }
    }

    /// Add an entry, return its handle. Always attempts to start the
    /// janitor task — `kick_janitor()` is idempotent and is the only
    /// reliable path to recover if the very first add happened before
    /// a tokio runtime was ready. Gating the kick on "map was empty"
    /// (as we used to) lost the janitor permanently in that case:
    /// subsequent adds would skip the kick and the janitor never
    /// started, leaving deadline-reaping entirely up to the
    /// `snapshot_matches` reap fallback (only fires on an activation).
    fn add(
        self: &Arc<Self>,
        target_pid: Option<i32>,
        restore_to: i32,
        origin: &'static str,
    ) -> SuppressionHandle {
        self.add_entry(target_pid, None, restore_to, origin)
    }

    /// Add a wildcard entry that ignores one intentional target activation.
    fn add_allowing(
        self: &Arc<Self>,
        allowed_pid: i32,
        restore_to: i32,
        origin: &'static str,
    ) -> SuppressionHandle {
        self.add_entry(None, Some(allowed_pid), restore_to, origin)
    }

    fn add_entry(
        self: &Arc<Self>,
        target_pid: Option<i32>,
        allowed_pid: Option<i32>,
        restore_to: i32,
        origin: &'static str,
    ) -> SuppressionHandle {
        let id = Uuid::new_v4();
        let entry = Entry {
            activity_restore: None,
            target_pid,
            allowed_pid,
            restore_to,
            deadline: Instant::now() + ENTRY_DEADLINE,
            returned_tail: false,
            origin,
        };
        {
            let mut guard = self.entries.lock().unwrap();
            guard.insert(id, entry);
        }
        // Always kick — idempotent if the task is already running.
        self.kick_janitor();
        // Signal the janitor that there's work to do (it will start a
        // fresh tokio interval on the next tick).
        let _ = self.janitor_active.send(true);
        SuppressionHandle(id)
    }

    /// Remove an entry. When the map drains to empty, signals the janitor
    /// to stop until the next add.
    fn remove(&self, handle: SuppressionHandle) {
        let now_empty = {
            let mut guard = self.entries.lock().unwrap();
            if let Some(entry) = guard.remove(&handle.0) {
                tracing::debug!(target: "cua_focus_restore", lease = %handle.0,
                    origin = entry.origin, target_pid = ?entry.target_pid,
                    returned_tail = entry.returned_tail,
                    expired = entry.deadline <= Instant::now(),
                    "Ended restoration lease");
            }
            guard.is_empty()
        };
        if now_empty {
            let _ = self.janitor_active.send(false);
        }
    }

    fn mark_deferred(&self, handle: SuppressionHandle, deadline: Instant) -> Option<Instant> {
        let mut entries = self.entries.lock().unwrap();
        let entry = entries.get_mut(&handle.0)?;
        let deadline = deadline.min(entry.deadline);
        if entry.target_pid.is_none() || deadline <= Instant::now() {
            return None;
        }
        entry.returned_tail = true;
        entry.deadline = deadline;
        tracing::debug!(target: "cua_focus_restore", lease = %handle.0,
            origin = entry.origin, target_pid = ?entry.target_pid,
            remaining_ms = deadline.saturating_duration_since(Instant::now()).as_millis() as u64,
            "Deferred restoration lease");
        Some(deadline)
    }

    fn cancel_deferred(&self, target_pid: i32) {
        let now_empty = {
            let mut entries = self.entries.lock().unwrap();
            entries
                .retain(|_, entry| !(entry.returned_tail && entry.target_pid == Some(target_pid)));
            entries.is_empty()
        };
        if now_empty {
            let _ = self.janitor_active.send(false);
        }
    }

    /// Snapshot the entries (cloned to a small Vec) — used by tests
    /// and the activation handler to evaluate matches without holding
    /// the lock across the restore call.
    fn snapshot_restore_candidates(
        &self,
        activated_pid: i32,
        current_front: Option<i32>,
    ) -> Vec<RestoreCandidate> {
        let mut guard = self.entries.lock().unwrap();
        // Reap expired entries first — keeps the dispatcher honest even
        // if the janitor hasn't ticked yet.
        let now = Instant::now();
        guard.retain(|_, e| e.deadline > now);
        if current_front != Some(activated_pid) {
            // NSWorkspace notifications can arrive after a newer activation.
            // A stale notification is not evidence for either adoption or
            // restoration, so leave every lease unchanged.
            return Vec::new();
        }
        let mut candidates = Vec::new();
        for (id, entry) in guard.iter_mut() {
            if entry.allowed_pid == Some(activated_pid) {
                continue;
            }
            match entry.target_pid {
                Some(target_pid)
                    if target_pid == activated_pid && entry.restore_to != activated_pid =>
                {
                    candidates.push(RestoreCandidate {
                        handle: SuppressionHandle(*id),
                        activated_pid,
                        restore_to: entry.restore_to,
                    });
                }
                Some(target_pid) if target_pid == activated_pid => {}
                Some(_) if activated_pid != entry.restore_to => {
                    // The lease covers only its target. An unrelated
                    // activation is therefore user/external state that must be
                    // preserved. Track it as the new restore destination so a
                    // later reflex activation of the target cannot pull the
                    // user back to the app that happened to be frontmost when
                    // the action started.
                    entry.restore_to = activated_pid;
                }
                Some(_) => {}
                // Wildcard: match any activation except the restore_to pid
                // (don't fight ourselves when we re-activate the prior
                // frontmost).
                None if activated_pid != entry.restore_to => {
                    candidates.push(RestoreCandidate {
                        handle: SuppressionHandle(*id),
                        activated_pid,
                        restore_to: entry.restore_to,
                    });
                }
                None => {}
            }
        }
        candidates
    }

    #[cfg(test)]
    fn snapshot_matches(&self, activated_pid: i32, current_front: Option<i32>) -> Vec<i32> {
        self.snapshot_restore_candidates(activated_pid, current_front)
            .into_iter()
            .map(|candidate| candidate.restore_to)
            .collect()
    }

    fn early_activation_candidates(
        &self,
        activated_pid: i32,
        current_front: Option<i32>,
    ) -> Vec<RestoreCandidate> {
        let entries = self.entries.lock().unwrap();
        let now = Instant::now();
        entries.iter().filter_map(|(id, entry)| {
            // Only a known target and the exact prior foreground may wait.
            // Unknown/newer foreground, wildcard launch scopes and intentional
            // activations do not acquire delayed restoration authority.
            (entry.deadline > now
                && entry.target_pid == Some(activated_pid)
                && entry.allowed_pid != Some(activated_pid)
                && entry.restore_to != activated_pid
                && current_front == Some(entry.restore_to))
                .then_some(RestoreCandidate {
                    handle: SuppressionHandle(*id),
                    activated_pid,
                    restore_to: entry.restore_to,
                })
        }).collect()
    }

    fn recheck_activation_candidate(
        &self,
        candidate: RestoreCandidate,
        current_front: Option<i32>,
    ) -> ActivationRecheck {
        let entries = self.entries.lock().unwrap();
        let Some(entry) = entries.get(&candidate.handle.0) else {
            return ActivationRecheck::Revoked;
        };
        if entry.deadline <= Instant::now()
            || entry.target_pid != Some(candidate.activated_pid)
            || entry.allowed_pid == Some(candidate.activated_pid)
            || entry.restore_to != candidate.restore_to
            || entry.restore_to == candidate.activated_pid
        {
            return ActivationRecheck::Revoked;
        }
        match current_front {
            Some(pid) if pid == candidate.activated_pid => ActivationRecheck::Ready,
            Some(pid) if pid == candidate.restore_to => ActivationRecheck::Waiting,
            _ => ActivationRecheck::Revoked,
        }
    }

    fn submit_restore_if_current(
        &self,
        candidate: RestoreCandidate,
        current_front: impl FnOnce() -> Option<i32>,
        submit: impl FnOnce(i32),
    ) -> bool {
        // Serialize the final restore submission with cancellation. A candidate
        // may have been queued before a foreground action cancelled its tail,
        // before expiration, or before a newer user activation changed the
        // restore destination. None of those stale candidates may act.
        let entries = self.entries.lock().unwrap();
        let Some(entry) = entries.get(&candidate.handle.0) else {
            return false;
        };
        if entry.deadline <= Instant::now()
            || entry.restore_to != candidate.restore_to
            || entry.restore_to == candidate.activated_pid
            || entry.allowed_pid == Some(candidate.activated_pid)
            || entry
                .target_pid
                .is_some_and(|pid| pid != candidate.activated_pid)
            || !should_restore_after_activation(current_front(), candidate.activated_pid)
        {
            return false;
        }
        // The production closure only submits exact WindowServer/key records;
        // it must not wait for activation or re-enter this dispatcher. Our
        // observer is on its own serial NSOperationQueue, so a resulting
        // notification is queued rather than synchronously re-entering here.
        submit(candidate.restore_to);
        true
    }

    fn restoration_completion_is_current(
        &self,
        completion: RestoreCompletion,
        current_front: impl FnOnce() -> Option<i32>,
    ) -> bool {
        let candidate = completion.candidate;
        let entries = self.entries.lock().unwrap();
        let Some(entry) = entries.get(&candidate.handle.0) else { return false; };
        entry.deadline > Instant::now()
            && entry.restore_to == candidate.restore_to
            && entry.restore_to != candidate.activated_pid
            && entry.allowed_pid != Some(candidate.activated_pid)
            && entry.target_pid.is_none_or(|pid| pid == candidate.activated_pid)
            && entry.activity_restore == Some(completion.evidence)
            && current_front() == Some(candidate.restore_to)
    }

    /// Number of entries (for tests).
    fn len(&self) -> usize {
        self.entries.lock().unwrap().len()
    }

    /// Reap entries whose deadline is past. Returns the number reaped.
    fn reap_expired(&self) -> usize {
        let mut guard = self.entries.lock().unwrap();
        let now = Instant::now();
        let before = guard.len();
        guard.retain(|_, e| e.deadline > now);
        let after = guard.len();
        let reaped = before - after;
        if after == 0 && reaped > 0 {
            let _ = self.janitor_active.send(false);
        }
        reaped
    }

    /// Start the janitor task on the current tokio runtime (idempotent).
    ///
    /// Safe to call from `add()` on every entry — returns immediately
    /// when the task is already up. If the spawn cannot proceed (no
    /// tokio runtime available — e.g. the first `add()` raced the
    /// binary's runtime init), the `started` flag is intentionally left
    /// `false` so the next add from a tokio-aware caller retries.
    /// Without that retry path the janitor could go permanently
    /// un-spawned and deadline-reaping would degrade to the
    /// `snapshot_matches` reap fallback (only runs on an activation).
    fn kick_janitor(self: &Arc<Self>) {
        let mut started = self.janitor_started.lock().unwrap();
        if *started {
            return;
        }
        // If there's no tokio runtime available (e.g. the binary is in
        // the middle of an init path that runs before Tokio is up), skip
        // — the next add from a tokio-aware caller will retry. We do NOT
        // set `*started = true` in this branch so the retry actually
        // takes the spawn path.
        if tokio::runtime::Handle::try_current().is_err() {
            return;
        }
        // Mark started ONLY after a successful `tokio::spawn`. The
        // spawn itself is infallible under the current API but we still
        // sequence the flag update after the spawn so any future
        // panic-from-spawn path would leave `started = false` and the
        // next add would retry.
        let weak = Arc::downgrade(self);
        let mut rx = self.janitor_active.subscribe();
        tokio::spawn(async move {
            loop {
                // Block until the dispatcher is non-empty.
                if !*rx.borrow_and_update() {
                    if rx.changed().await.is_err() {
                        break;
                    }
                    continue;
                }
                let mut tick = tokio::time::interval(JANITOR_TICK);
                tick.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
                tick.tick().await; // immediate first tick
                loop {
                    tokio::select! {
                        _ = tick.tick() => {
                            let Some(d) = weak.upgrade() else { return };
                            let _ = d.reap_expired();
                            if d.len() == 0 {
                                // Map drained — break to outer select, wait
                                // for next add.
                                break;
                            }
                        }
                        ch = rx.changed() => {
                            if ch.is_err() { return; }
                            // Active flag may have flipped; loop top will
                            // re-check via `borrow_and_update`.
                            break;
                        }
                    }
                }
            }
        });
        *started = true;
    }
}

// ── Observer registration ────────────────────────────────────────────────────

/// Register the NSWorkspace.didActivateApplicationNotification observer.
///
/// The returned token and the queue are intentionally `mem::forget`-leaked
/// — the singleton is process-lifetime, so we never tear the observer
/// down. Forgetting avoids having to thread `!Send` `Retained<...>`
/// handles through `FocusStealPreventer` (which lives in `Arc<...>` /
/// `OnceLock<...>` and therefore needs to be `Send + Sync`).
fn install_observer(dispatcher: &Arc<Dispatcher>) {
    use block2::RcBlock;
    use objc2_foundation::NSNotification;
    use std::ptr::NonNull;

    let ws = unsafe { NSWorkspace::sharedWorkspace() };
    let center = unsafe { ws.notificationCenter() };

    // Fresh background NSOperationQueue. Critical: with `nil` queue,
    // AppKit delivers synchronously on the posting thread (typically main);
    // with `mainQueue`, the block requires a running main run loop. A
    // fresh queue runs the block on a private background thread no matter
    // what run loop the binary has up.
    let queue = unsafe { NSOperationQueue::new() };
    // setMaxConcurrentOperationCount: 1 means activations are processed
    // serially — they're cheap so contention isn't a worry, but serial
    // processing keeps the restore order deterministic if two come in
    // back to back.
    unsafe { queue.setMaxConcurrentOperationCount(1) };

    let dispatcher_clone = Arc::clone(dispatcher);
    let block = RcBlock::new(move |note_ptr: NonNull<NSNotification>| {
        // SAFETY: AppKit gives us a borrowed NSNotification for the
        // duration of the block. We don't escape the reference.
        let note = unsafe { note_ptr.as_ref() };
        handle_activation(&dispatcher_clone, note);
    });

    let token = unsafe {
        center.addObserverForName_object_queue_usingBlock(
            Some(NSWorkspaceDidActivateApplicationNotification),
            None,
            Some(&queue),
            &block,
        )
    };

    // Intentionally leak both — the observer needs to outlive any
    // particular `Arc<FocusStealPreventer>` and the singleton has
    // process lifetime.
    std::mem::forget(token);
    std::mem::forget(queue);
}

/// Match a single activation notification against the dispatcher and,
/// for each matching entry, re-activate the entry's `restore_to` pid.
///
/// Runs on the observer queue's background thread — safe to call
/// blocking system APIs.
fn handle_activation(dispatcher: &Arc<Dispatcher>, note: &objc2_foundation::NSNotification) {
    use objc2::msg_send;
    use objc2::runtime::AnyObject;

    let activated_pid: i32 = unsafe {
        let info = match note.userInfo() {
            Some(i) => i,
            None => return,
        };
        // userInfo[NSWorkspaceApplicationKey] -> NSRunningApplication*.
        // We go through a raw msg_send to avoid Retained generic
        // bookkeeping for the cross-cast.
        let app_ptr: *mut AnyObject = msg_send![&*info, objectForKey: NSWorkspaceApplicationKey];
        if app_ptr.is_null() {
            return;
        }
        let pid: libc::pid_t = msg_send![app_ptr, processIdentifier];
        pid as i32
    };

    reconcile_activation(
        dispatcher,
        activated_pid,
        || observed_activation_front(activated_pid),
        std::thread::sleep,
        |candidate| restore_activation_candidate(dispatcher, candidate),
    );
}

fn observed_activation_front(activated_pid: i32) -> Option<i32> {
    // The notification and NSWorkspace's cached foreground can disagree for
    // the whole bounded recheck. Waiting on that same cache cannot establish
    // whether restoration is appropriate. Read WindowServer directly, as the
    // existing exact-window input teardown already does. Keep the cached value
    // only as diagnostic evidence; it must not authorize or veto restoration.
    let current_front = crate::input::skylight::front_process_pid();
    let workspace_front = crate::apps::frontmost_pid();
    if current_front != workspace_front {
        tracing::debug!(target: "cua_focus_restore", activated_pid,
            current_front = ?current_front, workspace_front = ?workspace_front,
            "Foreground sources disagree during activation protection");
    }
    current_front
}

fn reconcile_activation(
    dispatcher: &Arc<Dispatcher>,
    activated_pid: i32,
    mut read_front: impl FnMut() -> Option<i32>,
    mut pause: impl FnMut(Duration),
    mut restore: impl FnMut(RestoreCandidate),
) {
    let current_front = read_front();
    let entry_count = dispatcher.len();
    let candidates = dispatcher.snapshot_restore_candidates(activated_pid, current_front);
    if entry_count > 0 {
        tracing::debug!(target: "cua_focus_restore", activated_pid,
            current_front = ?current_front, entry_count, candidate_count = candidates.len(),
            "Received activation during restoration protection");
    }
    for candidate in candidates {
        restore(candidate);
    }

    // A stale notification and an early notification can both disagree with
    // the first foreground query. Retain only the original matching targeted
    // entries while that query still reports their prior foreground. A newer
    // application or unavailable identity ends the recheck immediately.
    let mut pending = dispatcher.early_activation_candidates(activated_pid, current_front);
    if pending.is_empty() { return; }
    tracing::debug!(target: "cua_focus_restore", activated_pid,
        pending_count=pending.len(), "Rechecking activation notification ahead of foreground state");
    let until = Instant::now() + ACTIVATION_RECHECK_INTERVAL * ACTIVATION_RECHECK_LIMIT as u32;
    for iteration in 0..ACTIVATION_RECHECK_LIMIT {
        let remaining = until.saturating_duration_since(Instant::now());
        if pending.is_empty() || remaining.is_zero() { break; }
        pause(ACTIVATION_RECHECK_INTERVAL.min(remaining));
        if Instant::now() >= until { break; }
        let current_front = read_front();
        pending.retain(|candidate| {
            let decision = dispatcher.recheck_activation_candidate(*candidate, current_front);
            tracing::debug!(target: "cua_focus_restore", lease = %candidate.handle.0,
                activated_pid, iteration, current_front = ?current_front, decision = ?decision,
                "Rechecked activation restoration authority");
            match decision {
            ActivationRecheck::Waiting => true,
            ActivationRecheck::Ready => {
                // Submission still revalidates this exact entry, foreground,
                // original activity generation and prior window ownership.
                // A refused submission is never replayed by this recheck.
                restore(*candidate);
                false
            }
            ActivationRecheck::Revoked => false,
            }
        });
    }
    if !pending.is_empty() {
        tracing::debug!(target: "cua_focus_restore", activated_pid, pending_count = pending.len(),
            "Activation recheck ended without a current target foreground");
    }
}

fn restore_activation_candidate(dispatcher: &Arc<Dispatcher>, candidate: RestoreCandidate) {
    let activated_pid = candidate.activated_pid;
    // Notification delivery and restoration are asynchronous. If another
    // application is already frontmost, the user (or an unrelated system
    // event) won the race; restoring the stale pid would steal focus from
    // that newer foreground. Compare immediately before each restore and
    // fail safe by leaving the newer foreground alone.
    let evidence = dispatcher
        .entries
        .lock()
        .unwrap()
        .get(&candidate.handle.0)
        .and_then(|entry| entry.activity_restore);
    if let Some(evidence) = evidence {
        let mut submitted = false;
        let admitted = dispatcher.submit_restore_if_current(candidate, || observed_activation_front(activated_pid), |pid| {
            submitted = crate::foreground_activity::restore_background_focus(evidence, pid);
        });
        tracing::debug!(target: "cua_focus_restore", lease = %candidate.handle.0,
            activated_pid, restore_pid = candidate.restore_to, admitted, submitted,
            "Evaluated activation restoration candidate");
        if admitted && submitted {
            let completion = RestoreCompletion { candidate, evidence };
            // AX calls and readiness reads must not hold entries.lock():
            // cancellation needs to invalidate this same ticket between steps.
            let result = crate::foreground_activity::complete_background_focus(
                evidence, candidate.restore_to, || {
                    if !dispatcher.restoration_completion_is_current(completion, || {
                        crate::input::skylight::front_process_pid()
                    }) {
                        anyhow::bail!("original restoration lease or foreground was revoked");
                    }
                    Ok(())
                },
            );
            tracing::debug!(target: "cua_focus_restore", lease = %candidate.handle.0,
                activated_pid, restore_pid = candidate.restore_to,
                completed = result.is_ok(), error = ?result.err(),
                "Completed exact prior-window restoration");
        }
    } else {
        tracing::debug!(target: "cua_focus_restore", lease = %candidate.handle.0,
            activated_pid, restore_pid = candidate.restore_to,
            "Activation candidate has no current restoration evidence");
    }
}

fn should_restore_after_activation(current_front: Option<i32>, activated_pid: i32) -> bool {
    current_front == Some(activated_pid)
}

/// Re-activate `pid` if it's still running. Safe to call from any
/// thread — Apple documents `activateWithOptions:` as thread-safe.

// ── Tests ────────────────────────────────────────────────────────────────────
//
// These tests exercise the pure-Rust dispatcher half — no Cocoa
// observers, no real notifications. They run under `cargo test
// -p platform-macos focus_steal::`.

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    /// Dispatcher::add returns a handle, the entry is reachable by
    /// match, and remove() drops it.
    #[test]
    fn dispatcher_add_match_remove() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.add");
        assert_eq!(d.len(), 1);
        let matches = d.snapshot_matches(42, Some(42));
        assert_eq!(matches, vec![7]);
        // Non-matching pid: no restore candidates.
        assert!(d.snapshot_matches(99, Some(99)).is_empty());
        d.remove(h);
        assert_eq!(d.len(), 0);
    }

    /// A target-only lease must not treat unrelated activation as a focus
    /// steal. That activation can be the user switching apps while a
    /// background action is still in its snapshot→detect window.
    #[test]
    fn targeted_lease_does_not_match_third_party_activation() {
        let d = Arc::new(Dispatcher::new());
        let _lease = d.add(Some(42), 7, "test.target_only");

        assert_eq!(d.snapshot_matches(42, Some(42)), vec![7]);
        assert!(
            d.snapshot_matches(99, Some(99)).is_empty(),
            "third-party activation must remain frontmost"
        );
        assert!(
            d.snapshot_matches(7, Some(7)).is_empty(),
            "restore target must not recursively match"
        );
    }

    /// A third-party activation during a target-only lease becomes the latest
    /// foreground to preserve. If the automated target activates afterwards,
    /// it must restore that new app rather than the stale snapshot-time app.
    #[test]
    fn targeted_lease_tracks_latest_unrelated_foreground() {
        let d = Arc::new(Dispatcher::new());
        let _lease = d.add(Some(42), 7, "test.target_tracks_user");

        assert!(d.snapshot_matches(99, Some(99)).is_empty());
        assert_eq!(d.snapshot_matches(42, Some(42)), vec![99]);
    }

    #[test]
    fn targeted_lease_does_not_restore_target_to_itself() {
        let d = Arc::new(Dispatcher::new());
        let _lease = d.add(Some(42), 42, "test.target_already_front");

        assert!(d.snapshot_matches(42, Some(42)).is_empty());
        assert!(d.snapshot_matches(99, Some(99)).is_empty());
        assert_eq!(d.snapshot_matches(42, Some(42)), vec![99]);
    }

    #[test]
    fn stale_activation_notification_does_not_replace_restore_target() {
        let d = Arc::new(Dispatcher::new());
        let _lease = d.add(Some(42), 7, "test.target_ignores_stale");

        assert!(d.snapshot_matches(99, Some(123)).is_empty());
        assert_eq!(d.snapshot_matches(42, Some(42)), vec![7]);
    }

    #[test]
    fn restore_requires_target_to_still_be_frontmost() {
        assert!(should_restore_after_activation(Some(42), 42));
        assert!(!should_restore_after_activation(Some(99), 42));
        assert!(!should_restore_after_activation(None, 42));
    }

    #[test]
    fn early_notification_is_rechecked_before_target_focus_settles() {
        let d = Arc::new(Dispatcher::new());
        let handle = d.add(Some(42), 7, "test.early_activation");
        let original_deadline = d.entries.lock().unwrap()[&handle.0].deadline;
        let mut reads = [Some(7), Some(7), Some(42)].into_iter();
        let mut submitted = Vec::new();
        reconcile_activation(&d, 42, || reads.next().expect("bounded recheck"), |_| {}, |candidate| {
            assert_eq!(candidate.handle, handle);
            d.submit_restore_if_current(candidate, || Some(42), |pid| submitted.push(pid));
        });
        assert_eq!(submitted, vec![7], "an early notification must not strand the target in front");
        assert_eq!(d.entries.lock().unwrap()[&handle.0].deadline, original_deadline);
    }

    #[test]
    fn early_activation_recheck_preserves_newer_or_unknown_foreground() {
        for newer in [Some(99), None] {
            let d = Arc::new(Dispatcher::new());
            let _handle = d.add(Some(42), 7, "test.early_newer_front");
            let mut reads = [Some(7), newer].into_iter();
            let mut pauses = 0;
            reconcile_activation(&d, 42, || reads.next().expect("stop after newer foreground"),
                |_| pauses += 1, |_| panic!("newer foreground must be preserved"));
            assert_eq!(pauses, 1);
        }
    }

    #[test]
    fn early_activation_recheck_cannot_adopt_a_replacement_lease() {
        let d = Arc::new(Dispatcher::new());
        let old = d.add(Some(42), 7, "test.early_old");
        d.mark_deferred(old, Instant::now() + Duration::from_secs(1));
        let mut replacement = None;
        let mut reads = [Some(7), Some(42)].into_iter();
        reconcile_activation(&d, 42, || reads.next().expect("cancelled notification"), |_| {
            d.cancel_deferred(42);
            replacement = Some(d.add(Some(42), 7, "test.early_new"));
        }, |_| panic!("a new lease must not inherit an old notification"));
        assert!(!d.entries.lock().unwrap().contains_key(&old.0));
        assert!(d.entries.lock().unwrap().contains_key(&replacement.unwrap().0));
    }

    #[test]
    fn early_activation_recheck_cannot_extend_an_expired_entry() {
        let d = Arc::new(Dispatcher::new());
        let handle = d.add(Some(42), 7, "test.early_expires");
        let mut reads = [Some(7), Some(42)].into_iter();
        reconcile_activation(&d, 42, || reads.next().expect("expired notification"), |_| {
            d.entries.lock().unwrap().get_mut(&handle.0).unwrap().deadline = Instant::now();
        }, |_| panic!("expired authority must not be renewed"));
    }

    #[test]
    fn early_activation_recheck_uses_original_target_and_restore_destination() {
        let d = Arc::new(Dispatcher::new());
        let handle = d.add(Some(42), 7, "test.early_anchor");
        let pending = d.early_activation_candidates(42, Some(7))[0];
        assert_eq!(d.recheck_activation_candidate(pending, Some(7)), ActivationRecheck::Waiting);
        assert!(d.snapshot_restore_candidates(99, Some(99)).is_empty());
        assert_eq!(d.recheck_activation_candidate(pending, Some(42)), ActivationRecheck::Revoked);
        let fresh = d.early_activation_candidates(42, Some(99))[0];
        d.entries.lock().unwrap().get_mut(&handle.0).unwrap().target_pid = Some(123);
        assert_eq!(d.recheck_activation_candidate(fresh, Some(42)), ActivationRecheck::Revoked);
    }

    #[test]
    fn early_activation_recheck_does_not_expand_wildcard_or_foreground_scopes() {
        for target in [None, Some(7), Some(99)] {
            let d = Arc::new(Dispatcher::new());
            let _handle = d.add(target, 7, "test.early_scope");
            reconcile_activation(&d, 42, || Some(7), |_| panic!("no matching target scope"),
                |_| panic!("no matching target scope"));
        }
        let d = Arc::new(Dispatcher::new());
        let _allowed = d.add_allowing(42, 7, "test.early_allowed");
        reconcile_activation(&d, 42, || Some(7), |_| panic!("intentional activation"),
            |_| panic!("intentional activation"));
    }

    #[test]
    fn early_activation_recheck_is_bounded_and_does_not_restore_an_unchanged_front() {
        let d = Arc::new(Dispatcher::new());
        let handle = d.add(Some(42), 7, "test.early_no_activation");
        let deadline = d.entries.lock().unwrap()[&handle.0].deadline;
        let mut pauses = Vec::new();
        reconcile_activation(&d, 42, || Some(7), |duration| pauses.push(duration),
            |_| panic!("no target activation occurred"));
        assert!(!pauses.is_empty() && pauses.len() <= ACTIVATION_RECHECK_LIMIT);
        assert!(pauses.iter().all(|&d| d <= ACTIVATION_RECHECK_INTERVAL));
        assert_eq!(d.entries.lock().unwrap()[&handle.0].deadline, deadline);
    }

    #[test]
    fn settled_activation_keeps_the_immediate_path() {
        let d = Arc::new(Dispatcher::new());
        let _handle = d.add(Some(42), 7, "test.already_settled");
        let mut submitted = Vec::new();
        reconcile_activation(&d, 42, || Some(42), |_| panic!("settled event must not wait"),
            |candidate| { d.submit_restore_if_current(candidate, || Some(42), |pid| submitted.push(pid)); });
        assert_eq!(submitted, vec![7]);
    }

    /// Wildcard entries (`target_pid = None`) match every activation
    /// except the entry's own restore_to pid.
    #[test]
    fn wildcard_matches_all_but_restore_to() {
        let d = Arc::new(Dispatcher::new());
        let _h = d.add(None, 7, "test.wild");
        // pid 99 != restore_to 7 → should match.
        assert_eq!(d.snapshot_matches(99, Some(99)), vec![7]);
        // pid 7 == restore_to → must NOT match (don't fight ourselves).
        assert!(d.snapshot_matches(7, Some(7)).is_empty());
    }

    #[test]
    fn narrowing_launch_lease_retains_identity_and_original_deadline() {
        let d = Arc::new(Dispatcher::new());
        let handle = d.add(None, 7, "test.launch_pre");
        let deadline = d.entries.lock().unwrap()[&handle.0].deadline;
        let lease = SuppressionLease {
            handle,
            dispatcher: Arc::clone(&d),
            released: false,
            poll_task: None,
        };
        let lease = lease.narrow_to(42, "test.launch_post").unwrap();
        assert_eq!(lease.handle, handle);
        assert_eq!(d.len(), 1);
        assert_eq!(d.entries.lock().unwrap()[&handle.0].deadline, deadline);
        assert_eq!(d.snapshot_matches(42, Some(42)), vec![7]);
        assert!(d.snapshot_matches(99, Some(99)).is_empty());
        drop(lease);
        assert_eq!(d.len(), 0);
    }

    #[test]
    fn narrowing_cannot_revive_or_retarget_a_cancelled_expired_or_scoped_lease() {
        let d = Arc::new(Dispatcher::new());
        let removed = d.add(None, 7, "test.removed");
        d.remove(removed);
        assert!(!d.narrow_to(removed, 42, "test.post"));
        let expired = d.add(None, 7, "test.expired");
        d.entries
            .lock()
            .unwrap()
            .get_mut(&expired.0)
            .unwrap()
            .deadline = Instant::now();
        assert!(!d.narrow_to(expired, 42, "test.post"));
        let targeted = d.add(Some(42), 7, "test.targeted");
        assert!(!d.narrow_to(targeted, 99, "test.post"));
        let allowing = d.add_allowing(42, 7, "test.allowing");
        assert!(!d.narrow_to(allowing, 99, "test.post"));
        let wildcard = d.add(None, 7, "test.wildcard");
        assert!(!d.narrow_to(wildcard, 7, "test.post"));
        assert!(!d.narrow_to(wildcard, 0, "test.post"));
    }

    /// A background pixel click intentionally makes its target AppKit-active
    /// without raising it. The wildcard guard must allow that one pid while
    /// continuing to suppress unrelated cross-app activations.
    #[test]
    fn wildcard_can_allow_intentional_target_activation() {
        let d = Arc::new(Dispatcher::new());
        let _h = d.add_allowing(42, 7, "test.allow");

        assert!(
            d.snapshot_matches(42, Some(42)).is_empty(),
            "intentional target activation must not be restored before the click"
        );
        assert_eq!(
            d.snapshot_matches(99, Some(99)),
            vec![7],
            "unrelated activations must remain suppressed"
        );
        assert!(
            d.snapshot_matches(7, Some(7)).is_empty(),
            "restoring the original foreground must never recurse"
        );
    }

    /// Lease Drop is the standard remove path.
    #[test]
    fn lease_drop_removes_entry() {
        // Use a private dispatcher to avoid singleton coupling.
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(1), 2, "test.lease");
        let lease = SuppressionLease {
            handle: h,
            dispatcher: Arc::clone(&d),
            released: false,
            poll_task: None,
        };
        assert_eq!(d.len(), 1);
        drop(lease);
        assert_eq!(d.len(), 0);
    }

    /// Explicit release() short-circuits the Drop path.
    #[test]
    fn lease_release_removes_entry() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(1), 2, "test.lease");
        let lease = SuppressionLease {
            handle: h,
            dispatcher: Arc::clone(&d),
            released: false,
            poll_task: None,
        };
        lease.release();
        assert_eq!(d.len(), 0);
    }

    /// Force a leaked entry whose deadline is already past, then call
    /// reap_expired and snapshot_matches — both must purge it.
    #[test]
    fn deadline_reaps_leaked_entry() {
        let d = Arc::new(Dispatcher::new());
        // Insert a handle manually with a past deadline.
        let id = Uuid::new_v4();
        {
            let mut guard = d.entries.lock().unwrap();
            guard.insert(
                id,
                Entry {
                    activity_restore: None,
                    target_pid: Some(42),
                    allowed_pid: None,
                    restore_to: 7,
                    deadline: Instant::now() - Duration::from_secs(1),
                    returned_tail: false,
                    origin: "test.leak",
                },
            );
        }
        assert_eq!(d.len(), 1);
        // snapshot_matches reaps expired entries before matching.
        let matches = d.snapshot_matches(42, Some(42));
        assert!(matches.is_empty(), "expired entry should not fire");
        assert_eq!(d.len(), 0, "snapshot_matches should purge expired");
    }

    /// Janitor lifecycle: starts on first add, stops when empty,
    /// restarts on next add. Spin up a tokio runtime to host the task.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn janitor_starts_stops_restarts() {
        let d = Arc::new(Dispatcher::new());
        // First add → janitor starts.
        let h1 = d.add(Some(1), 2, "test.j1");
        d.kick_janitor();
        // Give the janitor task time to spin up.
        tokio::time::sleep(Duration::from_millis(50)).await;
        // The dispatcher should still hold the entry.
        assert_eq!(d.len(), 1);
        // Now remove → janitor goes idle.
        d.remove(h1);
        tokio::time::sleep(Duration::from_millis(50)).await;
        assert_eq!(d.len(), 0);
        // Add again — same kick, same lifecycle. (start_janitor is
        // idempotent — already-started task picks up new adds via watch.)
        let _h2 = d.add(Some(3), 4, "test.j2");
        d.kick_janitor();
        tokio::time::sleep(Duration::from_millis(50)).await;
        assert_eq!(d.len(), 1);
    }

    /// Verifies the CodeRabbit #2 fix: `add()` always calls
    /// `kick_janitor()`, regardless of whether the map was empty.
    ///
    /// Scenario: first `add()` happens outside a tokio runtime —
    /// `kick_janitor()` short-circuits via `Handle::try_current()` and
    /// leaves `started = false`. A second `add()` from a tokio-aware
    /// caller (the more common case in practice) must retry the spawn.
    /// The old code skipped the kick because the map was non-empty,
    /// stranding the janitor forever.
    #[test]
    fn add_always_kicks_janitor_after_initial_runtime_miss() {
        let d = Arc::new(Dispatcher::new());
        // Outside any tokio runtime — kick_janitor's `try_current` guard
        // returns Err, the function returns without setting started.
        let h1 = d.add(Some(1), 2, "test.no_runtime");
        assert_eq!(d.len(), 1);
        assert!(
            !*d.janitor_started.lock().unwrap(),
            "kick without a runtime must leave started=false so the next \
             add retries"
        );

        // Now spin up a tokio runtime and add a second entry. The fix
        // is that this *second* add still calls kick_janitor (the old
        // code skipped because the map was already non-empty). Verify
        // by asserting started flips to true.
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .expect("build current-thread runtime");
        let d_in = Arc::clone(&d);
        rt.block_on(async move {
            let _h2 = d_in.add(Some(3), 4, "test.with_runtime");
            assert_eq!(d_in.len(), 2);
            assert!(
                *d_in.janitor_started.lock().unwrap(),
                "second add from inside the runtime must retry the spawn \
                 (regression guard for CodeRabbit #2)"
            );
        });

        // Clean up so the dispatcher doesn't outlive the runtime with
        // a still-armed entry — not strictly needed (Dispatcher is
        // `Send + Sync` and the spawned task holds only a Weak ref),
        // but keeps the test self-contained.
        d.remove(h1);
    }

    /// Snapshot ordering doesn't matter, but the restore pid set
    /// must contain every match. Multiple concurrent suppressions
    /// targeting the same pid should both fire.
    #[test]
    fn multiple_entries_match_independently() {
        let d = Arc::new(Dispatcher::new());
        let _a = d.add(Some(42), 1, "test.m1");
        let _b = d.add(Some(42), 2, "test.m2");
        let matches = d.snapshot_matches(42, Some(42));
        assert_eq!(matches.len(), 2);
        // Set equality — order is HashMap-dependent.
        assert!(matches.contains(&1));
        assert!(matches.contains(&2));
    }

    fn private_lease(d: &Arc<Dispatcher>, handle: SuppressionHandle) -> SuppressionLease {
        SuppressionLease {
            handle,
            dispatcher: Arc::clone(d),
            released: false,
            poll_task: None,
        }
    }

    #[test]
    fn deferred_cancel_preserves_active_wildcard_and_other_targets() {
        let d = Arc::new(Dispatcher::new());
        let tail = d.add(Some(42), 7, "test.tail");
        let active = d.add(Some(42), 7, "test.active");
        let wildcard = d.add(None, 7, "test.wildcard");
        let allowing = d.add_allowing(42, 7, "test.allowing");
        let other = d.add(Some(99), 7, "test.other");
        let deadline = Instant::now() + Duration::from_secs(1);
        assert!(d.mark_deferred(tail, deadline).is_some());
        assert!(d.mark_deferred(other, deadline).is_some());
        assert!(d.mark_deferred(wildcard, deadline).is_none());
        assert!(d.mark_deferred(allowing, deadline).is_none());
        d.cancel_deferred(42);
        let entries = d.entries.lock().unwrap();
        assert!(!entries.contains_key(&tail.0));
        for handle in [active, wildcard, allowing, other] {
            assert!(entries.contains_key(&handle.0));
        }
        assert!(!entries[&active.0].returned_tail);
        assert!(!entries[&wildcard.0].returned_tail);
    }

    #[test]
    fn deferred_cancel_invalidates_already_queued_restore() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.queued");
        d.mark_deferred(h, Instant::now() + Duration::from_secs(1));
        let candidate = d.snapshot_restore_candidates(42, Some(42))[0];
        d.cancel_deferred(42);
        let mut submitted = Vec::new();
        assert!(!d.submit_restore_if_current(candidate, || Some(42), |pid| submitted.push(pid)));
        assert!(submitted.is_empty());
    }

    #[test]
    fn deferred_restore_rechecks_expiry_without_a_janitor_tick() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.queued_expiry");
        let candidate = d.snapshot_restore_candidates(42, Some(42))[0];
        d.entries.lock().unwrap().get_mut(&h.0).unwrap().deadline = Instant::now();
        let mut submitted = Vec::new();
        assert!(!d.submit_restore_if_current(candidate, || Some(42), |pid| submitted.push(pid)));
        assert!(submitted.is_empty());
    }

    #[test]
    fn deferred_restore_rechecks_target_and_latest_restore_anchor() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.queued_anchor");
        let candidate = d.snapshot_restore_candidates(42, Some(42))[0];
        assert!(d.snapshot_restore_candidates(99, Some(99)).is_empty());
        let mut submitted = Vec::new();
        assert!(!d.submit_restore_if_current(candidate, || Some(42), |pid| submitted.push(pid)));
        assert!(submitted.is_empty());

        let current = d.snapshot_restore_candidates(42, Some(42))[0];
        assert!(d.submit_restore_if_current(current, || Some(42), |pid| submitted.push(pid)));
        assert_eq!(submitted, vec![99]);
        d.entries.lock().unwrap().get_mut(&h.0).unwrap().target_pid = Some(123);
        assert!(!d.submit_restore_if_current(current, || Some(42), |_| {}));
    }

    #[test]
    fn deferred_restore_submission_and_cancellation_share_entries_lock() {
        let d = Arc::new(Dispatcher::new());
        let _h = d.add(Some(42), 7, "test.submit_lock");
        let candidate = d.snapshot_restore_candidates(42, Some(42))[0];
        assert!(d.submit_restore_if_current(
            candidate,
            || {
                assert!(
                    d.entries.try_lock().is_err(),
                    "foreground check must hold entries lock"
                );
                Some(42)
            },
            |_| assert!(
                d.entries.try_lock().is_err(),
                "restore submission must hold entries lock"
            ),
        ));
        assert!(!d.submit_restore_if_current(candidate, || Some(99), |_| panic!("stale front")));
    }

    fn submitted_completion_fixture() -> (Arc<Dispatcher>, SuppressionHandle, RestoreCompletion) {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.exact_completion");
        let evidence = crate::foreground_activity::RestoreEvidence::for_test(7, 70, 3);
        d.entries.lock().unwrap().get_mut(&h.0).unwrap().activity_restore = Some(evidence);
        let candidate = d.snapshot_restore_candidates(42, Some(42))[0];
        assert!(d.submit_restore_if_current(candidate, || Some(42), |_| {}));
        (d, h, RestoreCompletion { candidate, evidence })
    }

    #[test]
    fn restoration_completion_uses_original_entry_after_submission_lock_is_released() {
        let (d, _, completion) = submitted_completion_fixture();
        assert!(d.entries.try_lock().is_ok(), "AX completion must be able to reacquire the lease");
        assert!(d.restoration_completion_is_current(completion, || Some(7)));
        for newer_or_unresolved_front in [Some(42), Some(99), None] {
            assert!(!d.restoration_completion_is_current(completion, || newer_or_unresolved_front));
        }
    }

    #[test]
    fn restoration_completion_cannot_outlive_cancelled_or_replaced_tail() {
        let (d, h, completion) = submitted_completion_fixture();
        d.mark_deferred(h, Instant::now() + Duration::from_secs(1));
        assert!(d.restoration_completion_is_current(completion, || Some(7)));
        d.cancel_deferred(42);
        let replacement = d.add(Some(42), 7, "test.replacement");
        d.entries.lock().unwrap().get_mut(&replacement.0).unwrap().activity_restore = Some(completion.evidence);
        assert!(!d.restoration_completion_is_current(completion, || Some(7)));
    }

    #[test]
    fn restoration_completion_rechecks_deadline_destination_target_and_activity_identity() {
        for change in ["expired", "destination", "target", "allowed", "evidence", "missing_evidence"] {
            let (d, h, completion) = submitted_completion_fixture();
            {
                let mut entries = d.entries.lock().unwrap();
                let entry = entries.get_mut(&h.0).unwrap();
                match change {
                    "expired" => entry.deadline = Instant::now(),
                    "destination" => entry.restore_to = 99,
                    "target" => entry.target_pid = Some(99),
                    "allowed" => entry.allowed_pid = Some(42),
                    "evidence" => entry.activity_restore = Some(crate::foreground_activity::RestoreEvidence::for_test(7, 70, 4)),
                    "missing_evidence" => entry.activity_restore = None,
                    _ => unreachable!(),
                }
            }
            assert!(!d.restoration_completion_is_current(completion, || Some(7)), "{change}");
        }
    }

    #[test]
    fn restoration_completion_revalidates_between_individual_ax_steps() {
        let (d, h, completion) = submitted_completion_fixture();
        let mut completed_operations = Vec::new();
        for operation in ["AXRaise", "AXMain", "AXFocused"] {
            if !d.restoration_completion_is_current(completion, || Some(7)) { break; }
            completed_operations.push(operation);
            d.remove(h); // e.g. user starts an intentional foreground segment.
        }
        assert_eq!(completed_operations, ["AXRaise"]);
    }

    #[test]
    fn deferred_old_cleanup_cannot_remove_a_new_same_pid_lease() {
        let d = Arc::new(Dispatcher::new());
        let old = d.add(Some(42), 7, "test.old_tail");
        let old_lease = private_lease(&d, old);
        d.mark_deferred(old, Instant::now() + Duration::from_secs(1));
        d.cancel_deferred(42);
        let new = d.add(Some(42), 99, "test.new_action");
        drop(old_lease);
        assert!(d.entries.lock().unwrap().contains_key(&new.0));
        assert_eq!(d.snapshot_matches(42, Some(42)), vec![99]);
    }

    #[test]
    fn deferred_deadline_never_extends_original_five_second_cap() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.cap");
        let original = d.entries.lock().unwrap()[&h.0].deadline;
        assert_eq!(
            d.mark_deferred(h, original + Duration::from_secs(30)),
            Some(original)
        );
        let shorter = Instant::now() + Duration::from_millis(100);
        assert_eq!(d.mark_deferred(h, shorter), Some(shorter));
        assert_eq!(d.mark_deferred(h, original), Some(shorter));
        assert!(d.mark_deferred(h, Instant::now()).is_none());
    }

    #[tokio::test]
    async fn deferred_timer_holds_then_drops_only_its_lease() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.timer");
        private_lease(&d, h).defer_release(Instant::now() + Duration::from_millis(30));
        assert!(d.entries.lock().unwrap()[&h.0].returned_tail);
        tokio::time::timeout(Duration::from_secs(1), async {
            while d.entries.lock().unwrap().contains_key(&h.0) {
                tokio::time::sleep(Duration::from_millis(5)).await;
            }
        })
        .await
        .expect("deferred lease was not released at its deadline");
    }

    #[tokio::test]
    async fn deferred_cleanup_observes_effects_after_the_fast_response_window() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.delayed_ordering");
        let polls = Arc::new(AtomicUsize::new(0));
        let called = Arc::clone(&polls);
        let dispatcher = Arc::clone(&d);
        let (sender, receiver) = tokio::sync::oneshot::channel();
        let mut sender = Some(sender);
        private_lease(&d, h).defer_release_with_poll(
            Instant::now() + Duration::from_secs(3), move |_| {
                assert!(dispatcher.entries.try_lock().is_err(), "poll must serialize with cancellation");
                let count = called.fetch_add(1, Ordering::SeqCst) + 1;
                if count < 3 { return true; }
                sender.take().unwrap().send(()).unwrap();
                false
            });
        assert!(d.entries.lock().unwrap()[&h.0].returned_tail);
        assert_eq!(polls.load(Ordering::SeqCst), 0, "cleanup must not block the response");
        tokio::time::timeout(Duration::from_secs(2), receiver).await.unwrap().unwrap();
        assert_eq!(polls.load(Ordering::SeqCst), 3);
        assert!(d.entries.lock().unwrap().contains_key(&h.0), "completed cleanup must retain focus protection");
        d.cancel_deferred(42);
    }

    #[tokio::test]
    async fn cancelled_cleanup_tail_cannot_submit_its_first_poll() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.cancelled_ordering");
        let calls = Arc::new(AtomicUsize::new(0));
        let submitted = Arc::clone(&calls);
        private_lease(&d, h).defer_release_with_poll(
            Instant::now() + Duration::from_secs(1), move |_| {
                submitted.fetch_add(1, Ordering::SeqCst);
                true
            });
        d.cancel_deferred(42);
        tokio::time::sleep(Duration::from_millis(180)).await;
        assert_eq!(calls.load(Ordering::SeqCst), 0);
        assert_eq!(d.len(), 0);
    }

    #[test]
    fn active_action_ordering_poll_is_eligible_before_return() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.active_ordering");
        let original = d.entries.lock().unwrap()[&h.0].deadline;
        assert_eq!(d.with_current_targeted(h, |deadline| deadline), Some(original),
            "an in-flight background action needs ordering protection before its response");
    }

    #[tokio::test]
    async fn active_poll_runs_before_handoff_and_keeps_the_original_callback() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.active_handoff");
        let deadline = d.entries.lock().unwrap()[&h.0].deadline;
        let mut lease = private_lease(&d, h);
        let calls = Arc::new(AtomicUsize::new(0));
        let submitted = Arc::clone(&calls);
        let (first_tx, first_rx) = tokio::sync::oneshot::channel();
        let (third_tx, third_rx) = tokio::sync::oneshot::channel();
        let mut first_tx = Some(first_tx);
        let mut third_tx = Some(third_tx);
        assert!(lease.start_polling(move |observed_deadline| {
            assert_eq!(observed_deadline, deadline);
            match submitted.fetch_add(1, Ordering::SeqCst) + 1 {
                1 => { first_tx.take().unwrap().send(()).unwrap(); },
                3 => { third_tx.take().unwrap().send(()).unwrap(); return false; },
                _ => {},
            }
            true
        }));
        tokio::time::timeout(Duration::from_secs(2), first_rx).await.unwrap().unwrap();
        assert!(!d.entries.lock().unwrap()[&h.0].returned_tail,
            "the first ordering check must precede the response handoff");
        lease.defer_release_with_poll(deadline + Duration::from_secs(30), |_| {
            panic!("handoff must not replace or duplicate the existing guard")
        });
        tokio::time::timeout(Duration::from_secs(2), third_rx).await.unwrap().unwrap();
        assert_eq!(calls.load(Ordering::SeqCst), 3);
        assert_eq!(d.entries.lock().unwrap()[&h.0].deadline, deadline);
        assert!(d.entries.lock().unwrap()[&h.0].returned_tail);
        d.cancel_deferred(42);
    }

    #[tokio::test]
    async fn dropping_active_lease_prevents_its_first_poll() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.active_drop");
        let calls = Arc::new(AtomicUsize::new(0));
        let submitted = Arc::clone(&calls);
        let mut lease = private_lease(&d, h);
        assert!(lease.start_polling(move |_| {
            submitted.fetch_add(1, Ordering::SeqCst);
            true
        }));
        drop(lease);
        tokio::time::sleep(Duration::from_millis(180)).await;
        assert_eq!(calls.load(Ordering::SeqCst), 0);
        assert_eq!(d.len(), 0);
    }

    #[tokio::test]
    async fn active_lease_drop_serializes_with_an_inflight_blocking_poll() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.active_drop_serialization");
        let mut lease = private_lease(&d, h);
        let (entered_tx, entered_rx) = tokio::sync::oneshot::channel();
        let (release_tx, release_rx) = std::sync::mpsc::channel();
        let mut entered_tx = Some(entered_tx);
        let dispatcher = Arc::clone(&d);
        assert!(lease.start_polling(move |_| {
            assert!(dispatcher.entries.try_lock().is_err());
            entered_tx.take().unwrap().send(()).unwrap();
            release_rx.recv_timeout(Duration::from_secs(2)).unwrap();
            false
        }));
        tokio::time::timeout(Duration::from_secs(2), entered_rx).await.unwrap().unwrap();
        let (dropping_tx, dropping_rx) = tokio::sync::oneshot::channel();
        let mut dropping = tokio::task::spawn_blocking(move || {
            dropping_tx.send(()).unwrap();
            drop(lease);
        });
        dropping_rx.await.unwrap();
        assert!(tokio::time::timeout(Duration::from_millis(30), &mut dropping).await.is_err(),
            "Drop must not return while an authorized callback can still act");
        release_tx.send(()).unwrap();
        tokio::time::timeout(Duration::from_secs(2), dropping).await.unwrap().unwrap();
        assert_eq!(d.len(), 0);
        assert_eq!(d.with_current_targeted(h, |_| panic!("removed lease")), None::<()>);
    }

    #[tokio::test]
    async fn active_poll_does_not_outlive_its_original_deadline() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.active_expiry");
        d.entries.lock().unwrap().get_mut(&h.0).unwrap().deadline =
            Instant::now() + Duration::from_millis(20);
        let mut lease = private_lease(&d, h);
        assert!(lease.start_polling(|_| panic!("first poll would exceed original deadline")));
        tokio::time::sleep(Duration::from_millis(130)).await;
        assert!(lease.poll_task.as_ref().unwrap().is_finished());
        assert!(lease.targeted_deadline().is_none());
        drop(lease);
        assert_eq!(d.len(), 0);
    }

    #[test]
    fn active_poll_without_runtime_does_not_drop_its_lease() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.active_no_runtime");
        let mut lease = private_lease(&d, h);
        assert!(!lease.start_polling(|_| panic!("no runtime")));
        assert_eq!(d.len(), 1);
        assert!(!d.entries.lock().unwrap()[&h.0].returned_tail);
        drop(lease);
        assert_eq!(d.len(), 0);
    }

    #[test]
    fn cleanup_poll_requires_a_live_targeted_entry() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.poll_lifecycle");
        let wildcard = d.add(None, 7, "test.wildcard_poll");
        assert_eq!(d.with_current_targeted(wildcard, |_| panic!("wildcard has no ordering authority")), None::<()>);
        d.mark_deferred(h, Instant::now() + Duration::from_secs(1));
        assert_eq!(d.with_current_targeted(h, |deadline| {
            assert!(deadline > Instant::now());
            9
        }), Some(9));
        d.entries.lock().unwrap().get_mut(&h.0).unwrap().deadline = Instant::now();
        assert_eq!(d.with_current_targeted(h, |_| panic!("expired tail")), None::<()>);
        d.cancel_deferred(42);
        assert_eq!(d.with_current_targeted(h, |_| panic!("cancelled tail")), None::<()>);
    }

    #[test]
    fn deferred_runtime_shutdown_drops_timer_owned_lease() {
        let d = Arc::new(Dispatcher::new());
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        runtime.block_on(async {
            let h = d.add(Some(42), 7, "test.shutdown");
            private_lease(&d, h).defer_release(Instant::now() + Duration::from_secs(4));
            assert_eq!(d.len(), 1);
        });
        drop(runtime);
        assert_eq!(d.len(), 0);
    }

    #[test]
    fn deferred_without_runtime_drops_immediately() {
        let d = Arc::new(Dispatcher::new());
        let h = d.add(Some(42), 7, "test.no_runtime_tail");
        private_lease(&d, h).defer_release(Instant::now() + Duration::from_secs(1));
        assert_eq!(d.len(), 0);
    }
}
