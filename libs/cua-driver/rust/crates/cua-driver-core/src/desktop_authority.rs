//! Process-wide native mutation ordering for guarded desktop observations.
//! Caller labels never create a lease. Blocking workers retain the canonical
//! dispatch lease so cancellation cannot expose an unfinished mutation.
use std::future::Future;
use std::sync::{
    atomic::{AtomicBool, AtomicU64, Ordering},
    Arc, OnceLock,
};

pub struct Authority {
    coordinator: Arc<tokio::sync::Mutex<()>>,
    epoch: AtomicU64,
    cleanup_unknown: AtomicBool,
    cleanup_changed: tokio::sync::Notify,
}

impl Default for Authority {
    fn default() -> Self {
        Self::new()
    }
}

impl Authority {
    fn new() -> Self {
        Self {
            coordinator: Arc::new(tokio::sync::Mutex::new(())),
            epoch: AtomicU64::new(0),
            cleanup_unknown: AtomicBool::new(false),
            cleanup_changed: tokio::sync::Notify::new(),
        }
    }

    pub async fn acquire(self: &Arc<Self>, mutation: bool) -> Result<Arc<Lease>, &'static str> {
        let changed = self.cleanup_changed.notified();
        tokio::pin!(changed);
        changed.as_mut().enable();
        if self.cleanup_unknown.load(Ordering::Acquire) {
            return Err("native_cleanup_unconfirmed");
        }
        // Preserve the uncontended no-yield path used by native input.
        let guard = match self.coordinator.clone().try_lock_owned() {
            Ok(guard) => guard,
            Err(_) => tokio::select! {
                guard = self.coordinator.clone().lock_owned() => guard,
                _ = changed => return Err("native_cleanup_unconfirmed"),
            },
        };
        if self.cleanup_unknown.load(Ordering::Acquire) {
            return Err("native_cleanup_unconfirmed");
        }
        let before = self.epoch.load(Ordering::Acquire);
        let epoch = if mutation {
            let Some(next) = before.checked_add(1) else {
                self.cleanup_unknown.store(true, Ordering::Release);
                self.cleanup_changed.notify_waiters();
                return Err("native_cleanup_unconfirmed");
            };
            self.epoch.store(next, Ordering::Release);
            next
        } else {
            before
        };
        Ok(Arc::new(Lease {
            authority: Arc::clone(self),
            before,
            epoch,
            mutation,
            _guard: guard,
        }))
    }
}

pub struct Lease {
    authority: Arc<Authority>,
    before: u64,
    epoch: u64,
    mutation: bool,
    _guard: tokio::sync::OwnedMutexGuard<()>,
}

impl Lease {
    pub fn is_current(&self) -> bool {
        !self.authority.cleanup_unknown.load(Ordering::Acquire)
            && self.authority.epoch.load(Ordering::Acquire) == self.epoch
    }

    pub fn observation_epoch(&self) -> Option<u64> {
        (!self.mutation && self.is_current()).then_some(self.epoch)
    }

    /// The entering action invalidates all other observations, but can consume
    /// its own immediately preceding observation exactly once in platform code.
    pub fn admits_observation(&self, observed_epoch: u64) -> bool {
        self.mutation && self.is_current() && self.before == observed_epoch
    }

    /// Cleanup uncertainty is sticky. The unreaped child retains this lease;
    /// new dispatches cannot treat a normal RPC response as native settlement.
    pub fn cleanup_unknown(&self) {
        self.authority
            .cleanup_unknown
            .store(true, Ordering::Release);
        self.authority.cleanup_changed.notify_waiters();
    }
}

pub fn global() -> &'static Arc<Authority> {
    static AUTHORITY: OnceLock<Arc<Authority>> = OnceLock::new();
    AUTHORITY.get_or_init(|| Arc::new(Authority::new()))
}

#[cfg(test)]
pub(crate) fn coordinator() -> &'static Arc<tokio::sync::Mutex<()>> {
    &global().coordinator
}

tokio::task_local! { static DISPATCH_LEASE: Option<Arc<Lease>>; }

pub fn current() -> Option<Arc<Lease>> {
    DISPATCH_LEASE.try_with(Clone::clone).ok().flatten()
}

pub(crate) async fn scope<F: Future>(lease: Option<Arc<Lease>>, work: F) -> F::Output {
    DISPATCH_LEASE.scope(lease, work).await
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn mutation_retires_observation_but_does_not_invalidate_itself() {
        let authority = Arc::new(Authority::new());
        let capture = authority.acquire(false).await.unwrap();
        let epoch = capture.observation_epoch().unwrap();
        drop(capture);
        let action = authority.acquire(true).await.unwrap();
        assert!(action.admits_observation(epoch));
        assert!(action.is_current());
        assert!(action.observation_epoch().is_none());
        drop(action);
        let other = authority.acquire(true).await.unwrap();
        assert!(!other.admits_observation(epoch));
        drop(other);
        let fresh = authority.acquire(false).await.unwrap();
        assert!(fresh.observation_epoch().unwrap() > epoch);
    }

    #[tokio::test]
    async fn cancelled_dispatch_keeps_capture_excluded_until_worker_settles() {
        let authority = Arc::new(Authority::new());
        let dispatch = authority.acquire(true).await.unwrap();
        let worker = Arc::clone(&dispatch);
        drop(dispatch);
        let capture = authority.acquire(false);
        tokio::pin!(capture);
        assert!(
            tokio::time::timeout(std::time::Duration::from_millis(10), &mut capture)
                .await
                .is_err()
        );
        drop(worker);
        assert!(
            tokio::time::timeout(std::time::Duration::from_secs(1), capture)
                .await
                .unwrap()
                .is_ok()
        );
    }

    #[tokio::test]
    async fn unconfirmed_cleanup_refuses_without_waiting_for_quarantined_worker() {
        let authority = Arc::new(Authority::new());
        let worker = authority.acquire(false).await.unwrap();
        worker.cleanup_unknown();
        assert!(!worker.is_current());
        assert!(authority.acquire(true).await.is_err());
        assert!(authority.acquire(false).await.is_err());
    }

    #[tokio::test]
    async fn quarantine_wakes_an_already_queued_capture_without_releasing_worker() {
        let authority = Arc::new(Authority::new());
        let worker = authority.acquire(true).await.unwrap();
        let capture = authority.acquire(false);
        tokio::pin!(capture);
        assert!(
            tokio::time::timeout(std::time::Duration::from_millis(10), &mut capture)
                .await
                .is_err()
        );
        worker.cleanup_unknown();
        assert!(
            tokio::time::timeout(std::time::Duration::from_secs(1), capture)
                .await
                .unwrap()
                .is_err()
        );
    }
}
