//! `get_desktop_state` — full-display vision screenshot (macOS).
//!
//! Vision-only desktop capture: grabs the ENTIRE main display at native
//! pixel size (no downscale) so screen-absolute pixel picks land exactly,
//! then reports the true screen size + backing scale. No AX walk, no
//! pid/window_id. This is the capture surface for actions with a primary-display
//! desktop target and screen-absolute coordinates.
//!
//! Mirrors `get_window_state.rs`'s vision ToolResult shape: an `image_png`
//! content part (or a written-out file path), a text summary line, and a
//! `structuredContent` object.

use async_trait::async_trait;
use cua_driver_contract::GetDesktopStateInput;
use cua_driver_core::{
    protocol::{Content, ToolResult},
    tool::{Tool, ToolDef},
    tool_args::parse_typed_input,
};
use serde_json::Value;

pub struct GetDesktopStateTool;

static DEF: std::sync::OnceLock<ToolDef> = std::sync::OnceLock::new();

fn def() -> &'static ToolDef {
    DEF.get_or_init(|| ToolDef {
        name: "get_desktop_state".into(),
        description: "Capture the full display in true screen pixels with no downscale. \
            Use its native-size PNG as the coordinate source for actions whose target is \
            {kind:\"desktop\",display_id:\"primary\"}. Returns the true screen size and \
            backing scale factor and a one-use desktop_observation_id, valid for 30 seconds \
            under this native transport/session. Desktop input requires that fresh binding. \
            Vision-only: no AX tree walk."
            .into(),
        input_schema: serde_json::json!({
            "type": "object",
            "properties": {
                "session": { "type": "string", "description": "For multi-call work, prefer a short public session label and repeat it on every call that accepts it. Omit it to use the authenticated transport's implicit lifecycle session." },
                "screenshot_out_file": { "type": "string", "description": "Write PNG here instead of base64." }
            },
            "additionalProperties": false
        }),
        read_only: true,
        destructive: false,
        idempotent: false,
        open_world: false,
    })
}

#[async_trait]
impl Tool for GetDesktopStateTool {
    fn def(&self) -> &ToolDef {
        def()
    }

    async fn invoke(&self, args: Value) -> ToolResult {
        let input = match parse_typed_input::<GetDesktopStateInput>("get_desktop_state", args.clone()) {
            Ok(input) => input,
            Err(result) => return result,
        };
        let screenshot_out_file = input.screenshot_out_file.map(|s| {
            // Expand ~ prefix (mirrors get_window_state).
            if let Some(relative) = s.strip_prefix("~/") {
                let home = std::env::var("HOME").unwrap_or_default();
                format!("{home}/{relative}")
            } else {
                s
            }
        });

        // Capture and bind the same stable display under native ownership. A
        // screenshot never grants a caller-supplied process or desktop lease.
        let capture = match crate::foreground_activity::desktop::Capture::begin(&args) {
            Ok(capture) => capture,
            Err(refusal) => return refusal,
        };
        let screen_width = capture.geometry.width as u64;
        let screen_height = capture.geometry.height as u64;
        let scale_factor = capture.geometry.scale();
        let _cancel_capture = capture.cancellation_guard();

        // Capture the FULL display at native size — no resize. Run the
        // blocking screencapture subprocess off the async runtime.
        let out_file = screenshot_out_file.clone();
        let res = tokio::task::spawn_blocking(
            move || -> Result<(Option<String>, Option<String>, u32, u32, String), ToolResult> {
                use base64::{engine::general_purpose::STANDARD as BASE64, Engine};
                // The worker owns both capture leases through child settlement,
                // even if this async request is cancelled and drops its handle.
                let (png, capture) = crate::capture::desktop::capture_owned(capture)?;
                let (w, h) = crate::capture::png_dimensions(&png)
                    .map_err(|_| ToolResult::error("Desktop screenshot has invalid PNG geometry"))?;
                capture.check()?;
                let (b64, file) = if let Some(ref path) = out_file {
                    crate::capture::desktop::write_output(std::path::Path::new(path), &png, || capture.check())?;
                    (None, Some(path.clone()))
                } else {
                    (Some(BASE64.encode(&png)), None)
                };
                let token = capture.finish(w, h)?;
                Ok((b64, file, w, h, token))
            },
        )
        .await;

        let (b64_opt, file_path, screenshot_width, screenshot_height, desktop_observation_id) = match res {
            Ok(Ok(v)) => v,
            Ok(Err(refusal)) => return refusal,
            Err(e) => return ToolResult::error(format!("Desktop screenshot task error: {e}")),
        };

        let mut content: Vec<Content> = Vec::new();
        if let Some(b64) = b64_opt {
            content.push(Content::image_png(b64));
        }
        let summary = format!(
            "desktop screenshot {screenshot_width}x{screenshot_height} px \
             (screen {screen_width}x{screen_height} pts @ {scale_factor}x)"
        );
        content.push(Content::text(summary));

        let mut structured = serde_json::json!({
            "platform": "macos",
            "display": "primary",
            "screenshot_width": screenshot_width,
            "screenshot_height": screenshot_height,
            "screen_width": screen_width,
            "screen_height": screen_height,
            "scale_factor": scale_factor,
            "screenshot_mime_type": "image/png",
            "desktop_binding_version": 1,
            "desktop_observation_id": desktop_observation_id,
        });
        if let Some(ref fp) = file_path {
            structured["screenshot_file_path"] = serde_json::json!(fp);
        }

        ToolResult {
            content,
            is_error: None,
            structured_content: Some(structured),
            meta: None,
            action_record: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schema_has_no_pid_or_window_id_and_is_read_only() {
        let d = def();
        assert!(d.read_only, "get_desktop_state must be read_only");
        assert!(!d.destructive);
        assert!(!d.idempotent);
        assert!(!d.open_world);

        let props = d.input_schema["properties"].as_object().unwrap();
        assert!(!props.contains_key("pid"), "must not accept pid");
        assert!(
            !props.contains_key("window_id"),
            "must not accept window_id"
        );
        assert!(
            !props.contains_key("capture_mode"),
            "must not accept capture_mode"
        );
        assert!(props.contains_key("session"));
        assert!(props.contains_key("screenshot_out_file"));
        assert_eq!(
            d.input_schema["additionalProperties"],
            serde_json::json!(false)
        );
    }

    #[test]
    fn description_mentions_full_and_screen_or_display() {
        let desc = def().description.to_lowercase();
        assert!(desc.contains("full"), "description must mention 'full'");
        assert!(
            desc.contains("screen") || desc.contains("display"),
            "description must mention 'screen' or 'display'"
        );
    }
}
