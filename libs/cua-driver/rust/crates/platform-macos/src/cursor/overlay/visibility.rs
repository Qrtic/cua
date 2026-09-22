//! WindowServer clipping for each cursor, independent of the shared overlay's
//! z-order. AppKit can reorder only one of the display surfaces, or another
//! session can pin those surfaces elsewhere. Neither may expose a background
//! cursor over a window covering its actual target.

use std::collections::BTreeMap;

use crate::windows::{WindowBounds, WindowInfo};

#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) struct Rect {
    pub left: f64,
    pub top: f64,
    pub right: f64,
    pub bottom: f64,
}

impl Rect {
    pub fn from_xywh(x: f64, y: f64, width: f64, height: f64) -> Option<Self> {
        let right = x + width;
        let bottom = y + height;
        (width > 0.0 && height > 0.0 && [x, y, right, bottom].iter().all(|value| value.is_finite()))
            .then_some(Self {
                left: x,
                top: y,
                right,
                bottom,
            })
    }

    fn from_bounds(bounds: &WindowBounds) -> Option<Self> {
        Self::from_xywh(bounds.x, bounds.y, bounds.width, bounds.height)
    }

    pub fn intersect(self, other: Self) -> Option<Self> {
        let left = self.left.max(other.left);
        let top = self.top.max(other.top);
        let right = self.right.min(other.right);
        let bottom = self.bottom.min(other.bottom);
        Self::from_xywh(left, top, right - left, bottom - top)
    }

    fn subtract(self, cover: Self, output: &mut Vec<Self>) {
        let Some(cover) = self.intersect(cover) else {
            output.push(self);
            return;
        };
        // Four disjoint strips around the intersection; no overlapping paint.
        for (x, y, width, height) in [
            (
                self.left,
                self.top,
                self.right - self.left,
                cover.top - self.top,
            ),
            (
                self.left,
                cover.bottom,
                self.right - self.left,
                self.bottom - cover.bottom,
            ),
            (
                self.left,
                cover.top,
                cover.left - self.left,
                cover.bottom - cover.top,
            ),
            (
                cover.right,
                cover.top,
                self.right - cover.right,
                cover.bottom - cover.top,
            ),
        ] {
            if let Some(rect) = Self::from_xywh(x, y, width, height) {
                output.push(rect);
            }
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub(super) struct WindowClip {
    pub bounds: Option<Rect>,
    pub visible: Vec<Rect>,
}

pub(super) type WindowClips = BTreeMap<u64, WindowClip>;

pub(super) fn capture_clips(targets: impl IntoIterator<Item = u64>) -> WindowClips {
    let targets: Vec<_> = targets.into_iter().collect();
    if targets.is_empty() {
        return WindowClips::new();
    }
    // This is a raw, read-only WindowServer snapshot: no AX traversal, Space
    // queries, input guard, or application activation on the rendering path.
    let snapshot = crate::windows::visible_windows_including_accessory_layers_with_snapshot();
    targets
        .into_iter()
        .map(|target| {
            let clip = if snapshot.succeeded {
                clip_for_window(target, &snapshot.windows, std::process::id() as i32)
            } else {
                WindowClip::default()
            };
            (target, clip)
        })
        .collect()
}

pub(super) fn clips_are_current(clips: &WindowClips) -> bool {
    *clips == capture_clips(clips.keys().copied())
}

fn clip_for_window(target: u64, windows: &[WindowInfo], overlay_pid: i32) -> WindowClip {
    let Some(window) = windows.iter().find(|window| {
        u64::from(window.window_id) == target && window.is_on_screen && window.layer == 0
    }) else {
        // Closed, hidden, minimized and off-Space targets must not fall back
        // to a cursor at the front of the desktop.
        return WindowClip::default();
    };
    let Some(bounds) = Rect::from_bounds(&window.bounds) else {
        return WindowClip::default();
    };
    let mut visible = vec![bounds];
    for cover in windows.iter().filter(|cover| {
        cover.is_on_screen
            // Our surfaces stay at normal window level. Higher-level panels
            // already composite above them. Their bounding boxes are not an
            // opacity mask: Dock, for example, owns a transparent screen-sized
            // layer-20 window that would otherwise hide every cursor.
            && cover.layer == 0
            && cover.z_index > window.z_index
            && cover.pid != overlay_pid
    }) {
        let Some(cover) = Rect::from_bounds(&cover.bounds) else {
            continue;
        };
        let mut next = Vec::new();
        for rect in visible {
            rect.subtract(cover, &mut next);
            // Decorative feedback may disappear on a pathologically crowded
            // desktop; it must not create unbounded work or lose its clipping.
            if next.len() > 128 {
                return WindowClip {
                    bounds: Some(bounds),
                    visible: Vec::new(),
                };
            }
        }
        visible = next;
        if visible.is_empty() {
            break;
        }
    }
    WindowClip {
        bounds: Some(bounds),
        visible,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn window(id: u32, pid: i32, z: usize, rect: [f64; 4]) -> WindowInfo {
        WindowInfo {
            window_id: id,
            pid,
            app_name: String::new(),
            title: String::new(),
            bounds: WindowBounds {
                x: rect[0],
                y: rect[1],
                width: rect[2],
                height: rect[3],
            },
            layer: 0,
            z_index: z,
            is_on_screen: true,
            current_space_id: None,
            on_current_space: None,
            space_ids: None,
        }
    }

    #[test]
    fn covering_foreground_window_hides_only_the_background_cursor() {
        let windows = vec![
            window(1, 10, 10, [0.0, 0.0, 100.0, 100.0]),
            window(2, 20, 20, [0.0, 0.0, 100.0, 100.0]),
            window(3, 99, 30, [0.0, 0.0, 1000.0, 1000.0]),
        ];
        assert!(clip_for_window(1, &windows, 99).visible.is_empty());
        assert_eq!(clip_for_window(2, &windows, 99).visible.len(), 1);
        // Even an unpinned third session on a shared, frontmost surface cannot
        // change which pixels these two target-bound cursors may paint.
    }

    #[test]
    fn partial_cover_leaves_disjoint_visible_target_regions() {
        let windows = vec![
            window(1, 10, 10, [0.0, 0.0, 100.0, 100.0]),
            window(2, 20, 20, [30.0, 20.0, 40.0, 50.0]),
        ];
        let clip = clip_for_window(1, &windows, 99);
        assert_eq!(clip.visible.len(), 4);
        let cover = Rect::from_bounds(&windows[1].bounds).unwrap();
        let area: f64 = clip
            .visible
            .iter()
            .map(|rect| {
                assert!(rect.intersect(cover).is_none());
                (rect.right - rect.left) * (rect.bottom - rect.top)
            })
            .sum();
        assert_eq!(area, 8000.0);
        for (i, rect) in clip.visible.iter().enumerate() {
            for other in &clip.visible[i + 1..] {
                assert!(rect.intersect(*other).is_none());
            }
        }
    }

    #[test]
    fn missing_and_offscreen_targets_never_become_unpinned() {
        assert!(clip_for_window(42, &[], 99).visible.is_empty());
        let mut target = window(1, 10, 10, [0.0, 0.0, 100.0, 100.0]);
        target.is_on_screen = false;
        assert!(clip_for_window(1, &[target], 99).visible.is_empty());
    }

    #[test]
    fn other_display_and_lower_windows_do_not_occlude_the_target() {
        let windows = vec![
            window(1, 10, 10, [-192.0, -1080.0, 1920.0, 1080.0]),
            window(2, 20, 20, [0.0, 0.0, 1728.0, 1117.0]),
            window(3, 30, 5, [-192.0, -1080.0, 1920.0, 1080.0]),
        ];
        let clip = clip_for_window(1, &windows, 99);
        assert_eq!(clip.visible, vec![clip.bounds.unwrap()]);
    }

    #[test]
    fn higher_level_compositor_bounds_do_not_hide_normal_window_feedback() {
        let target = window(1, 10, 10, [0.0, 0.0, 100.0, 100.0]);
        let mut cover = window(2, 20, 20, [0.0, 0.0, 1728.0, 1117.0]);
        for layer in [3, 20, 25, 101] {
            cover.layer = layer;
            let clip = clip_for_window(1, &[target.clone(), cover.clone()], 99);
            assert_eq!(clip.visible, vec![clip.bounds.unwrap()]);
        }
    }

    #[test]
    fn same_app_normal_windows_still_occlude_the_target() {
        let target = window(1, 10, 10, [0.0, 0.0, 100.0, 100.0]);
        let mut cover = window(2, 10, 20, [0.0, 0.0, 100.0, 100.0]);
        cover.layer = 0;
        assert!(clip_for_window(1, &[target, cover], 99).visible.is_empty());
    }
}
