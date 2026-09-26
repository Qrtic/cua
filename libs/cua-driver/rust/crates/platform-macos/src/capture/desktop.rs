//! Bounded child lifecycle for an owned desktop observation. Other screenshot
//! callers keep their existing implementation and targeting semantics.
use super::SecureCapturePath;
use crate::foreground_activity::desktop::Capture;
use cua_driver_core::protocol::ToolResult;
use std::process::{Child, Command, Stdio};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Mutex, OnceLock,
};
use std::time::{Duration, Instant};

const CAPTURE_MS: u64 = 10_000;
const REAP_MS: u64 = 1_000;
const POLL_MS: u64 = 20;
const MAX_PNG_BYTES: u64 = 64 * 1024 * 1024;

fn refused(code: &str, message: &str) -> ToolResult {
    ToolResult::error(message).with_structured(serde_json::json!({
        "code": code, "effect": "refused", "retryable": false, "desktop_binding_version": 1,
    }))
}

trait ChildControl {
    fn poll(&mut self) -> std::io::Result<Option<bool>>;
    fn kill(&mut self);
}

struct ManagedChild {
    child: Child,
    reaped: bool,
}
impl ChildControl for ManagedChild {
    fn poll(&mut self) -> std::io::Result<Option<bool>> {
        let status = self.child.try_wait()?;
        if status.is_some() {
            self.reaped = true;
        }
        Ok(status.map(|status| status.success()))
    }
    fn kill(&mut self) {
        if !self.reaped {
            let _ = self.child.kill();
        }
    }
}

trait Clock {
    fn now(&self) -> u64;
    fn sleep(&mut self);
}
struct RealClock(Instant);
impl Clock for RealClock {
    fn now(&self) -> u64 {
        self.0.elapsed().as_millis().min(u64::MAX as u128) as u64
    }
    fn sleep(&mut self) {
        std::thread::sleep(Duration::from_millis(POLL_MS));
    }
}

fn wait_for_child(
    child: &mut impl ChildControl,
    clock: &mut impl Clock,
    mut check: impl FnMut() -> Result<(), ToolResult>,
) -> Result<(), ToolResult> {
    let start = clock.now();
    loop {
        check()?;
        if clock.now().saturating_sub(start) >= CAPTURE_MS {
            return Err(refused(
                "desktop_observation_stale",
                "Desktop screenshot child exceeded its deadline",
            ));
        }
        match child.poll() {
            Ok(Some(true)) => return Ok(()),
            Ok(Some(false)) | Err(_) => {
                return Err(refused(
                    "desktop_display_unavailable",
                    "Desktop screenshot child failed",
                ))
            }
            Ok(None) => clock.sleep(),
        }
    }
}

fn stop_and_reap(child: &mut impl ChildControl, clock: &mut impl Clock) -> bool {
    if matches!(child.poll(), Ok(Some(_))) {
        return true;
    }
    child.kill();
    let start = clock.now();
    loop {
        if matches!(child.poll(), Ok(Some(_))) {
            return true;
        }
        if clock.now().saturating_sub(start) >= REAP_MS {
            return false;
        }
        clock.sleep();
    }
}

struct OwnedChild {
    child: Option<ManagedChild>,
    capture: Option<Capture>,
    path: Option<SecureCapturePath>,
}

impl OwnedChild {
    fn settle(&mut self) -> bool {
        let Some(child) = &mut self.child else {
            return true;
        };
        if child.reaped || stop_and_reap(child, &mut RealClock(Instant::now())) {
            return true;
        }
        // Never release either serialization lease or the private capture path
        // while the child may still be writing. A sticky native refusal stops
        // all later desktop mutations, even if the background reaper succeeds.
        self.capture
            .as_ref()
            .expect("owned capture")
            .cleanup_unknown();
        quarantine(Quarantined {
            child: self.child.take().expect("owned child"),
            _capture: self.capture.take().expect("owned capture"),
            _path: self.path.take().expect("owned path"),
        });
        false
    }
}
impl Drop for OwnedChild {
    fn drop(&mut self) {
        self.settle();
    }
}

struct Quarantined {
    child: ManagedChild,
    _capture: Capture,
    _path: SecureCapturePath,
}
fn quarantined() -> &'static Mutex<Vec<Quarantined>> {
    static CHILDREN: OnceLock<Mutex<Vec<Quarantined>>> = OnceLock::new();
    CHILDREN.get_or_init(|| Mutex::new(Vec::new()))
}
fn quarantine(child: Quarantined) {
    quarantined()
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .push(child);
    static REAPER_STARTED: AtomicBool = AtomicBool::new(false);
    if !REAPER_STARTED.swap(true, Ordering::AcqRel) {
        if std::thread::Builder::new()
            .name("desktop-capture-reaper".into())
            .spawn(|| loop {
                std::thread::sleep(Duration::from_millis(100));
                quarantined()
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .retain_mut(|owned| {
                        if matches!(owned.child.poll(), Ok(Some(_))) {
                            false
                        } else {
                            owned.child.kill();
                            true
                        }
                    });
            })
            .is_err()
        {
            // The static quarantine still owns every guard and child. A later
            // quarantine can retry creating the reaper; no input is re-enabled.
            REAPER_STARTED.store(false, Ordering::Release);
        }
    }
}

pub(crate) fn capture_owned(capture: Capture) -> Result<(Vec<u8>, Capture), ToolResult> {
    capture.check()?;
    let path = SecureCapturePath::new("display.png").map_err(|_| {
        refused(
            "desktop_display_unavailable",
            "Could not create a private desktop capture path",
        )
    })?;
    // No pipes can fill or outlive the child. -m selects only the main display.
    let child = Command::new("/usr/sbin/screencapture")
        .args(["-x", "-m", "-t", "png"])
        .arg(&path.file)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|_| {
            refused(
                "desktop_display_unavailable",
                "Could not start the desktop screenshot child",
            )
        })?;
    let mut owned = OwnedChild {
        child: Some(ManagedChild {
            child,
            reaped: false,
        }),
        capture: Some(capture),
        path: Some(path),
    };
    let result = (|| {
        let capture = owned.capture.as_ref().expect("owned capture");
        wait_for_child(
            owned.child.as_mut().expect("owned child"),
            &mut RealClock(Instant::now()),
            || capture.check(),
        )?;
        capture.check()?;
        let path = &owned.path.as_ref().expect("owned path").file;
        let info = std::fs::symlink_metadata(path).map_err(|_| {
            refused(
                "desktop_display_unavailable",
                "Desktop screenshot is unavailable",
            )
        })?;
        if !info.is_file() || info.len() == 0 || info.len() > MAX_PNG_BYTES {
            return Err(refused(
                "desktop_display_unavailable",
                "Desktop screenshot is not a bounded nonempty regular file",
            ));
        }
        std::fs::read(path).map_err(|_| {
            refused(
                "desktop_display_unavailable",
                "Desktop screenshot could not be read",
            )
        })
    })();
    if !owned.settle() {
        return Err(refused("native_cleanup_unconfirmed", "Desktop screenshot child cleanup is unconfirmed; stop input without replay or reconnection"));
    }
    result.map(|png| (png, owned.capture.take().expect("owned capture")))
}

pub(crate) fn write_output(
    path: &std::path::Path,
    png: &[u8],
    check: impl FnOnce() -> Result<(), ToolResult>,
) -> Result<(), ToolResult> {
    use std::io::Write;
    use std::os::unix::fs::OpenOptionsExt;
    let invalid = || {
        refused(
            "desktop_display_unavailable",
            "Desktop screenshot output must be a writable regular file",
        )
    };
    if std::fs::symlink_metadata(path).is_ok_and(|info| !info.is_file()) {
        return Err(invalid());
    }
    // Do not use truncate at open: first prove the opened object is a regular
    // file. NONBLOCK prevents a replaced FIFO from hanging before that proof.
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(false)
        .custom_flags(libc::O_NONBLOCK | libc::O_NOFOLLOW)
        .open(path)
        .map_err(|_| invalid())?;
    if !file.metadata().map_err(|_| invalid())?.is_file() {
        return Err(invalid());
    }
    check()?;
    file.set_len(0).map_err(|_| invalid())?;
    file.write_all(png).map_err(|_| invalid())
}

#[cfg(test)]
mod tests {
    use super::*;
    struct FakeClock(u64);
    impl Clock for FakeClock {
        fn now(&self) -> u64 {
            self.0
        }
        fn sleep(&mut self) {
            self.0 += POLL_MS;
        }
    }
    struct FakeChild {
        polls: usize,
        finish_at: usize,
        killed: bool,
        finish_after_kill: bool,
    }
    impl ChildControl for FakeChild {
        fn poll(&mut self) -> std::io::Result<Option<bool>> {
            self.polls += 1;
            Ok(
                (self.polls >= self.finish_at || (self.killed && self.finish_after_kill))
                    .then_some(true),
            )
        }
        fn kill(&mut self) {
            self.killed = true;
        }
    }
    fn hung(reaps: bool) -> FakeChild {
        FakeChild {
            polls: 0,
            finish_at: usize::MAX,
            killed: false,
            finish_after_kill: reaps,
        }
    }

    #[test]
    fn hung_child_has_a_real_deadline_and_is_killed_and_reaped() {
        let mut child = hung(true);
        let mut clock = FakeClock(0);
        assert!(wait_for_child(&mut child, &mut clock, || Ok(())).is_err());
        assert_eq!(clock.0, CAPTURE_MS);
        assert!(stop_and_reap(&mut child, &mut clock));
        assert!(child.killed);
    }
    #[test]
    fn cancellation_stops_before_more_capture_work_and_requires_reaping() {
        let mut child = hung(true);
        let mut clock = FakeClock(0);
        assert!(wait_for_child(&mut child, &mut clock, || Err(refused(
            "desktop_owner_unavailable",
            "cancelled"
        )))
        .is_err());
        assert_eq!(child.polls, 0);
        assert!(stop_and_reap(&mut child, &mut clock));
        assert!(child.killed);
    }
    #[test]
    fn failed_reaping_is_bounded_and_never_claims_settlement() {
        let mut child = hung(false);
        let mut clock = FakeClock(0);
        assert!(!stop_and_reap(&mut child, &mut clock));
        assert_eq!(clock.0, REAP_MS);
        assert!(child.killed);
    }

    #[test]
    fn output_file_refuses_fifo_and_symlink_without_writing_their_targets() {
        use std::os::unix::fs::symlink;
        let path = SecureCapturePath::new("display.png").unwrap();
        let fifo = std::ffi::CString::new(path.file.as_os_str().as_encoded_bytes()).unwrap();
        assert_eq!(unsafe { libc::mkfifo(fifo.as_ptr(), 0o600) }, 0);
        assert!(write_output(&path.file, b"new", || Ok(())).is_err());
        std::fs::remove_file(&path.file).unwrap();
        let target = SecureCapturePath::new("target.png").unwrap();
        std::fs::write(&target.file, b"original").unwrap();
        symlink(&target.file, &path.file).unwrap();
        assert!(write_output(&path.file, b"new", || Ok(())).is_err());
        assert_eq!(std::fs::read(&target.file).unwrap(), b"original");
        std::fs::remove_file(&path.file).unwrap();
        write_output(&path.file, b"new", || Ok(())).unwrap();
        write_output(&path.file, b"x", || Ok(())).unwrap();
        assert_eq!(std::fs::read(&path.file).unwrap(), b"x");
    }
}
