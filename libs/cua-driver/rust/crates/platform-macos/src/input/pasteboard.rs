//! Scoped literal-text paste. Original clipboard representations remain local
//! and are restored only while our pasteboard generation is still current.

use anyhow::{anyhow, ensure, Context};
use objc2::{rc::Retained, runtime::ProtocolObject};
use objc2_app_kit::{NSPasteboard, NSPasteboardItem, NSPasteboardTypeString, NSPasteboardWriting};
use objc2_foundation::{NSArray, NSString};

const MAX_ITEMS: usize = 32;
const MAX_TYPES_PER_ITEM: usize = 64;
const MAX_SNAPSHOT_BYTES: usize = 16 * 1024 * 1024;

unsafe fn copy_items(board: &NSPasteboard) -> anyhow::Result<Vec<Retained<NSPasteboardItem>>> {
    let Some(items) = board.pasteboardItems() else {
        ensure!(
            board.types().is_none_or(|types| types.is_empty()),
            "Clipboard representations could not be preserved"
        );
        return Ok(Vec::new());
    };
    ensure!(
        items.len() <= MAX_ITEMS,
        "Clipboard has too many items for a temporary paste"
    );
    let mut saved = Vec::with_capacity(items.len());
    let mut bytes = 0usize;
    for item_index in 0..items.len() {
        let item = items.objectAtIndex(item_index);
        let types = item.types();
        ensure!(
            types.len() <= MAX_TYPES_PER_ITEM,
            "Clipboard has too many representations"
        );
        let copy = NSPasteboardItem::new();
        for type_index in 0..types.len() {
            let kind = types.objectAtIndex(type_index);
            let data = item
                .dataForType(&kind)
                .context("Clipboard representation is unavailable")?;
            bytes = bytes
                .checked_add(data.length())
                .context("Clipboard size overflow")?;
            ensure!(
                bytes <= MAX_SNAPSHOT_BYTES,
                "Clipboard is too large for a temporary paste"
            );
            ensure!(
                copy.setData_forType(&data, &kind),
                "Could not preserve a clipboard representation"
            );
        }
        saved.push(copy);
    }
    Ok(saved)
}

unsafe fn write_items(board: &NSPasteboard, items: &[Retained<NSPasteboardItem>]) -> bool {
    if items.is_empty() {
        return true;
    }
    let objects: Vec<Retained<ProtocolObject<dyn NSPasteboardWriting>>> = items
        .iter()
        .map(|item| ProtocolObject::from_retained(item.clone()))
        .collect();
    board.writeObjects(&NSArray::from_vec(objects))
}

struct Restore {
    board: Retained<NSPasteboard>,
    saved: Vec<Retained<NSPasteboardItem>>,
    owned_generation: Option<isize>,
}

impl Restore {
    fn finish(&mut self) -> anyhow::Result<()> {
        let Some(generation) = self.owned_generation.take() else {
            return Ok(());
        };
        unsafe {
            // A user or another application may copy during the action. Their
            // newer clipboard must never be replaced by our older snapshot.
            if self.board.changeCount() != generation {
                return Ok(());
            }
            self.board.clearContents();
            ensure!(
                write_items(&self.board, &self.saved),
                "Original clipboard restoration failed"
            );
        }
        Ok(())
    }
}

impl Drop for Restore {
    fn drop(&mut self) {
        if let Err(error) = self.finish() {
            tracing::error!(%error, "temporary pasteboard cleanup failed");
        }
    }
}

fn with_text_on<T>(
    board: Retained<NSPasteboard>,
    text: &str,
    before_publish: impl FnOnce() -> anyhow::Result<()>,
    action: impl FnOnce() -> anyhow::Result<T>,
) -> anyhow::Result<T> {
    unsafe {
        let generation = board.changeCount();
        let saved = copy_items(&board)?;
        let payload = NSPasteboardItem::new();
        ensure!(
            payload.setString_forType(&NSString::from_str(text), NSPasteboardTypeString),
            "Could not prepare literal text"
        );
        before_publish()?;
        ensure!(
            board.changeCount() == generation,
            "Clipboard changed while preparing literal text; no paste was sent"
        );
        let mut restore = Restore {
            board,
            saved,
            owned_generation: None,
        };
        restore.owned_generation = Some(restore.board.clearContents());
        let published = write_items(&restore.board, &[payload]);
        restore.owned_generation = Some(restore.board.changeCount());
        if !published {
            restore.finish()?;
            return Err(anyhow!("Could not publish literal text; no paste was sent"));
        }
        let result = action();
        restore.finish()?;
        result
    }
}

/// Caller holds the exact foreground input guard throughout `action`, including
/// its delivery readback. No clipboard contents are logged or written to disk.
pub(crate) fn with_literal_text<T>(
    text: &str,
    action: impl FnOnce() -> anyhow::Result<T>,
) -> anyhow::Result<T> {
    with_text_on(
        unsafe { NSPasteboard::generalPasteboard() },
        text,
        crate::foreground_activity::check_request,
        action,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use objc2::msg_send;
    use objc2_foundation::NSData;
    use std::sync::Mutex;

    // Named boards isolate data, but AppKit's type-conversion cache is shared
    // within this process. Keep each native test's entire board lifetime under
    // one lock, as production paste is covered by the foreground input guard.
    static NATIVE_PASTEBOARD_TEST: Mutex<()> = Mutex::new(());

    unsafe fn seed(board: &NSPasteboard) {
        let first = NSPasteboardItem::new();
        assert!(
            first.setString_forType(&NSString::from_str("original 中文"), NSPasteboardTypeString)
        );
        assert!(first.setData_forType(
            &NSData::with_bytes(&[0, 1, 2, 255]),
            &NSString::from_str("com.example.binary")
        ));
        let second = NSPasteboardItem::new();
        assert!(second.setString_forType(&NSString::from_str("second"), NSPasteboardTypeString));
        board.clearContents();
        assert!(write_items(board, &[first, second]));
    }

    #[test]
    fn restores_every_representation_and_item_after_literal_paste() {
        let _guard = NATIVE_PASTEBOARD_TEST.lock().expect("pasteboard test lock");
        unsafe {
            let board = NSPasteboard::pasteboardWithUniqueName();
            seed(&board);
            with_text_on(
                board.clone(),
                "table 111",
                || Ok(()),
                || {
                    assert_eq!(
                        board
                            .stringForType(NSPasteboardTypeString)
                            .unwrap()
                            .to_string(),
                        "table 111"
                    );
                    Ok(())
                },
            )
            .unwrap();
            let items = board.pasteboardItems().unwrap();
            assert_eq!(items.len(), 2);
            assert_eq!(
                items
                    .objectAtIndex(0)
                    .stringForType(NSPasteboardTypeString)
                    .unwrap()
                    .to_string(),
                "original 中文"
            );
            assert_eq!(
                items
                    .objectAtIndex(0)
                    .dataForType(&NSString::from_str("com.example.binary"))
                    .unwrap()
                    .bytes(),
                &[0, 1, 2, 255]
            );
            assert_eq!(
                items
                    .objectAtIndex(1)
                    .stringForType(NSPasteboardTypeString)
                    .unwrap()
                    .to_string(),
                "second"
            );
            let _: () = msg_send![&*board, releaseGlobally];
        }
    }

    #[test]
    fn does_not_overwrite_a_newer_copy_during_the_action() {
        let _guard = NATIVE_PASTEBOARD_TEST.lock().expect("pasteboard test lock");
        unsafe {
            let board = NSPasteboard::pasteboardWithUniqueName();
            seed(&board);
            with_text_on(
                board.clone(),
                "temporary",
                || Ok(()),
                || {
                    board.clearContents();
                    assert!(board.setString_forType(
                        &NSString::from_str("new copy"),
                        NSPasteboardTypeString
                    ));
                    Ok(())
                },
            )
            .unwrap();
            assert_eq!(
                board
                    .stringForType(NSPasteboardTypeString)
                    .unwrap()
                    .to_string(),
                "new copy"
            );
            let _: () = msg_send![&*board, releaseGlobally];
        }
    }

    #[test]
    fn interruption_before_paste_preserves_original_items() {
        let _guard = NATIVE_PASTEBOARD_TEST.lock().expect("pasteboard test lock");
        unsafe {
            let board = NSPasteboard::pasteboardWithUniqueName();
            seed(&board);
            let result: anyhow::Result<()> = with_text_on(
                board.clone(),
                "temporary",
                || Ok(()),
                || Err(anyhow!("input interrupted before dispatch")),
            );
            assert!(result.is_err());
            assert_eq!(board.pasteboardItems().unwrap().len(), 2);
            assert_eq!(
                board
                    .pasteboardItems()
                    .unwrap()
                    .objectAtIndex(0)
                    .stringForType(NSPasteboardTypeString)
                    .unwrap()
                    .to_string(),
                "original 中文"
            );
            let _: () = msg_send![&*board, releaseGlobally];
        }
    }
}
