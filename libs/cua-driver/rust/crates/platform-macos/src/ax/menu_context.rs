//! Bounded ownership of target-only activation while an application menu is open.
//!
//! This is cleanup state, never input authority. Every subsequent menu action
//! still proves the live focused document and menu ancestry before dispatch.

use std::{
    collections::HashMap,
    sync::{atomic::{AtomicBool, Ordering}, Arc, Mutex},
    time::{Duration, Instant},
};

use crate::input::skylight::SyntheticTargetFocusContext;

const MAX_MENU_CONTEXT_AGE: Duration = Duration::from_secs(120);

pub(crate) struct MenuContextLease<T = SyntheticTargetFocusContext> {
    pub(crate) context: T,
    pub(crate) started: Instant,
    owner: String,
    pid: i32,
    window_id: u32,
}

impl<T> MenuContextLease<T> {
    pub(crate) fn new(context: T, owner: String, pid: i32, window_id: u32) -> Self {
        Self { context, started: Instant::now(), owner, pid, window_id }
    }

    fn expired(&self, now: Instant) -> bool {
        now.saturating_duration_since(self.started) >= MAX_MENU_CONTEXT_AGE
    }
}

struct ContextEntries<T> {
    by_pid: HashMap<i32, MenuContextLease<T>>,
}

impl<T> Default for ContextEntries<T> {
    fn default() -> Self { Self { by_pid: HashMap::new() } }
}

impl<T> ContextEntries<T> {
    fn take(&mut self, owner: &str, pid: i32, window_id: u32) -> Result<Option<MenuContextLease<T>>, ()> {
        if self.by_pid.get(&pid).is_some_and(|entry| entry.owner != owner || entry.window_id != window_id) {
            return Err(());
        }
        Ok(self.by_pid.remove(&pid))
    }

    fn remove_where(&mut self, predicate: impl Fn(&MenuContextLease<T>) -> bool) -> Vec<MenuContextLease<T>> {
        let pids: Vec<_> = self.by_pid.iter().filter(|(_, e)| predicate(e)).map(|(pid, _)| *pid).collect();
        pids.into_iter().filter_map(|pid| self.by_pid.remove(&pid)).collect()
    }
}

pub(crate) struct MenuContextRegistry {
    entries: Mutex<ContextEntries<SyntheticTargetFocusContext>>,
    reaper_started: AtomicBool,
}

impl MenuContextRegistry {
    pub(crate) fn new() -> Arc<Self> {
        Arc::new(Self { entries: Mutex::new(ContextEntries::default()), reaper_started: AtomicBool::new(false) })
    }

    fn remove_where(&self, predicate: impl Fn(&MenuContextLease) -> bool) {
        let removed = self.entries.lock().unwrap_or_else(|e| e.into_inner()).remove_where(predicate);
        // Drop posts only the retained target's synthetic deactivation. Never
        // hold the registry lock during native cleanup or address the real front.
        drop(removed);
    }

    fn expire(&self) {
        let now = Instant::now();
        self.remove_where(|entry| entry.expired(now) || cua_driver_core::session::is_session_ended(&entry.owner));
    }

    pub(crate) fn take(&self, owner: Option<&str>, pid: i32, window_id: u32) -> anyhow::Result<Option<MenuContextLease>> {
        self.expire();
        let owner = owner.filter(|owner| !owner.is_empty());
        // Anonymous one-shot calls cannot acquire another transport's lease.
        let mut entries = self.entries.lock().unwrap_or_else(|e| e.into_inner());
        if owner.is_none() && entries.by_pid.contains_key(&pid) {
            anyhow::bail!("application-menu context belongs to another session; no input was sent");
        }
        let Some(owner) = owner else { return Ok(None) };
        if cua_driver_core::session::is_session_ended(owner) {
            anyhow::bail!("application-menu session ended; no input was sent");
        }
        entries.take(owner, pid, window_id).map_err(|()| anyhow::anyhow!(
            "application-menu context belongs to another session or exact window; no input was sent"
        ))
    }

    /// Retain only after a fresh, exact visible-menu proof in the caller. The
    /// original deadline survives transfers across actions and cannot be renewed.
    pub(crate) fn park(self: &Arc<Self>, lease: MenuContextLease) -> anyhow::Result<()> {
        if lease.expired(Instant::now()) || cua_driver_core::session::is_session_ended(&lease.owner) {
            return Ok(()); // RAII ends this context without sending further input.
        }
        if !self.reaper_started.swap(true, Ordering::AcqRel) {
            let weak = Arc::downgrade(self);
            if let Err(error) = std::thread::Builder::new().name("cua-menu-cleanup".into()).spawn(move || {
                loop {
                    std::thread::sleep(Duration::from_millis(250));
                    let Some(registry) = weak.upgrade() else { break };
                    registry.expire();
                }
            }) {
                self.reaper_started.store(false, Ordering::Release);
                return Err(error.into());
            }
        }
        let mut entries = self.entries.lock().unwrap_or_else(|e| e.into_inner());
        // The action retains the native per-PID mutation lease through this
        // insertion. A concurrent session end still wins at the final check.
        if cua_driver_core::session::is_session_ended(&lease.owner) || lease.expired(Instant::now()) {
            drop(entries);
            return Ok(());
        }
        if entries.by_pid.contains_key(&lease.pid) {
            drop(entries);
            anyhow::bail!("application-menu context changed during dispatch; retained cleanup was not replaced");
        }
        entries.by_pid.insert(lease.pid, lease);
        Ok(())
    }

    pub(crate) fn clear_session(&self, session: &str) { self.remove_where(|entry| entry.owner == session); }
    pub(crate) fn clear_all(&self) { self.remove_where(|_| true); }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicUsize;

    struct Cleanup(Arc<AtomicUsize>);
    impl Drop for Cleanup { fn drop(&mut self) { self.0.fetch_add(1, Ordering::SeqCst); } }

    fn entry(owner: &str, pid: i32, window: u32, count: &Arc<AtomicUsize>) -> MenuContextLease<Cleanup> {
        MenuContextLease::new(Cleanup(count.clone()), owner.into(), pid, window)
    }

    #[test]
    fn another_session_or_window_cannot_take_menu_context() {
        let count = Arc::new(AtomicUsize::new(0));
        let mut entries = ContextEntries::default();
        entries.by_pid.insert(7, entry("owner", 7, 42, &count));
        assert!(entries.take("other", 7, 42).is_err());
        assert!(entries.take("owner", 7, 43).is_err());
        assert_eq!(entries.by_pid.len(), 1);
        assert_eq!(count.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn transfer_preserves_original_deadline_and_cleans_up_once() {
        let count = Arc::new(AtomicUsize::new(0));
        let mut entries = ContextEntries::default();
        let lease = entry("owner", 7, 42, &count);
        let started = lease.started;
        entries.by_pid.insert(7, lease);
        let lease = entries.take("owner", 7, 42).unwrap().unwrap();
        assert_eq!(lease.started, started);
        assert!(!lease.expired(started + MAX_MENU_CONTEXT_AGE - Duration::from_millis(1)));
        assert!(lease.expired(started + MAX_MENU_CONTEXT_AGE));
        entries.by_pid.insert(7, lease);
        drop(entries.remove_where(|entry| entry.expired(started + MAX_MENU_CONTEXT_AGE)));
        assert_eq!(count.load(Ordering::SeqCst), 1);
        drop(entries);
        assert_eq!(count.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn disconnect_removes_only_exact_owner_and_preserves_other_contexts() {
        let count = Arc::new(AtomicUsize::new(0));
        let mut entries = ContextEntries::default();
        entries.by_pid.insert(7, entry("owner", 7, 42, &count));
        entries.by_pid.insert(8, entry("owner ", 8, 44, &count));
        drop(entries.remove_where(|entry| entry.owner == "owner"));
        assert_eq!(count.load(Ordering::SeqCst), 1);
        assert!(entries.by_pid.contains_key(&8));
        drop(entries);
        assert_eq!(count.load(Ordering::SeqCst), 2);
    }
}
