//! Native-only lifecycle endpoints. The public marketplace tool surface does
//! not expose native tokens; its checked executor owns batch/dialog lifetimes.

use async_trait::async_trait;
use cua_driver_core::{
    protocol::ToolResult,
    tool::{Tool, ToolDef},
};
use serde_json::{json, Value};
use std::sync::OnceLock;

pub struct BeginForegroundSegmentTool;
pub struct EndForegroundSegmentTool;
pub struct PrepareDialogTool;
pub struct PrepareObservationTool;

fn definition(end: bool) -> &'static ToolDef {
    static BEGIN: OnceLock<ToolDef> = OnceLock::new();
    static END: OnceLock<ToolDef> = OnceLock::new();
    let slot = if end { &END } else { &BEGIN };
    slot.get_or_init(|| {
        let mut schema = json!({
            "type": "object",
            "properties": {
                "pid": {"type": "integer", "minimum": 1, "maximum": i32::MAX},
                "window_id": {"type": "integer", "minimum": 1, "maximum": u32::MAX}
            },
            "required": ["pid", "window_id"],
            "additionalProperties": false
        });
        if end {
            schema["properties"]["foreground_segment_id"] = json!({
                "type": "string", "minLength": 1, "maxLength": 128
            });
            schema["properties"]["mode"] = json!({
                "type": "string", "enum": ["finish", "abort"]
            });
            schema["required"] = json!(["pid", "window_id", "foreground_segment_id", "mode"]);
        } else {
            schema["properties"]["scope"] = json!({"type":"string", "enum":["batch", "dialog"], "default":"batch"});
        }
        ToolDef {
            name: if end { "end_foreground_segment" } else { "begin_foreground_segment" }.into(),
            description: if end {
                "Settle this transport's exact native foreground segment. Finish may restore the original window only without intervention; abort never reclaims focus. Never replay an uncertain end."
            } else {
                "Reserve one exact native foreground segment for the current trusted transport. Dialog scope requires a live attached standard Open/Save sheet and retains its host only for restoration. Captures original focus without activation or input; end explicitly after settlement."
            }.into(),
            input_schema: schema,
            read_only: false,
            destructive: false,
            idempotent: false,
            open_world: false,
        }
    })
}

#[async_trait]
impl Tool for BeginForegroundSegmentTool {
    fn def(&self) -> &ToolDef {
        definition(false)
    }

    async fn invoke(&self, args: Value) -> ToolResult {
        crate::foreground_activity::begin_segment(args).await
    }
}

#[async_trait]
impl Tool for EndForegroundSegmentTool {
    fn def(&self) -> &ToolDef {
        definition(true)
    }

    async fn invoke(&self, args: Value) -> ToolResult {
        crate::foreground_activity::end_segment(args).await
    }
}

#[async_trait]
impl Tool for PrepareDialogTool {
    fn def(&self) -> &ToolDef {
        static DEF: OnceLock<ToolDef> = OnceLock::new();
        DEF.get_or_init(|| ToolDef {
            name: "prepare_dialog".into(),
            description: "Activate this segment's exact attached Open/Save dialog and necessary host once, without clicking or typing. Requires native dialog scope, current owner, idle/activity lease and exact readiness. Observe the dialog after preparation.".into(),
            input_schema: json!({
                "type":"object", "properties": {
                    "pid":{"type":"integer", "minimum":1, "maximum":i32::MAX},
                    "window_id":{"type":"integer", "minimum":1, "maximum":u32::MAX},
                    "foreground_segment_id":{"type":"string", "minLength":1, "maxLength":128},
                    "delivery_mode":{"type":"string", "enum":["foreground"]}
                }, "required":["pid", "window_id", "foreground_segment_id"], "additionalProperties":false
            }),
            read_only:false, destructive:false, idempotent:false, open_world:false,
        })
    }

    async fn invoke(&self, args: Value) -> ToolResult {
        crate::foreground_activity::prepare_dialog(args).await
    }
}

#[async_trait]
impl Tool for PrepareObservationTool {
    fn def(&self) -> &ToolDef {
        static DEF: OnceLock<ToolDef> = OnceLock::new();
        DEF.get_or_init(|| ToolDef {
            name: "prepare_observation".into(),
            description: "Briefly expose the exact ordinary document window to let an occluded renderer progress. Sends no click or key. Requires a live same-owner batch foreground segment, fresh standard-window proof, current Space and activity lease. Observe once, then finish the segment immediately.".into(),
            input_schema: json!({
                "type":"object", "properties": {
                    "pid":{"type":"integer", "minimum":1, "maximum":i32::MAX},
                    "window_id":{"type":"integer", "minimum":1, "maximum":u32::MAX},
                    "foreground_segment_id":{"type":"string", "minLength":1, "maxLength":128},
                    "delivery_mode":{"type":"string", "enum":["foreground"]}
                }, "required":["pid", "window_id", "foreground_segment_id", "delivery_mode"], "additionalProperties":false
            }),
            read_only:false, destructive:false, idempotent:false, open_world:false,
        })
    }

    async fn invoke(&self, args: Value) -> ToolResult {
        crate::foreground_activity::prepare_observation(args).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn foreground_segment_controls_require_exact_target_and_explicit_end_mode() {
        for end in [false, true] {
            let def = definition(end);
            assert!(!def.read_only && !def.destructive && !def.idempotent && !def.open_world);
            assert_eq!(def.input_schema["additionalProperties"], false);
            assert_eq!(def.input_schema["required"][0], "pid");
            assert_eq!(def.input_schema["required"][1], "window_id");
            assert!(def.input_schema["properties"].get("session_id").is_none());
            assert!(def.input_schema["properties"]
                .get("runtime_scope")
                .is_none());
        }
        assert_eq!(
            definition(true).input_schema["properties"]["mode"]["enum"],
            json!(["finish", "abort"])
        );
        assert_eq!(
            definition(true).input_schema["properties"]["foreground_segment_id"]["maxLength"],
            128
        );
    }

    #[test]
    fn dialog_preparation_is_native_exact_and_has_no_input_or_host_override() {
        let tool = PrepareDialogTool;
        let def = tool.def();
        assert!(!def.read_only && !def.idempotent && !def.open_world);
        assert_eq!(
            def.input_schema["required"],
            json!(["pid", "window_id", "foreground_segment_id"])
        );
        assert_eq!(
            definition(false).input_schema["properties"]["scope"]["enum"],
            json!(["batch", "dialog"])
        );
        for forbidden in [
            "host_pid",
            "host_window_id",
            "text",
            "key",
            "x",
            "y",
            "session_id",
        ] {
            assert!(def.input_schema["properties"].get(forbidden).is_none());
        }
    }

    #[test]
    fn rendering_preparation_has_no_input_duration_or_target_override() {
        let tool = PrepareObservationTool;
        let def = tool.def();
        assert!(!def.read_only && !def.idempotent && !def.open_world);
        assert_eq!(
            def.input_schema["required"],
            json!(["pid", "window_id", "foreground_segment_id", "delivery_mode"])
        );
        assert_eq!(def.input_schema["additionalProperties"], false);
        for forbidden in [
            "host_pid",
            "host_window_id",
            "text",
            "key",
            "x",
            "y",
            "duration",
            "session_id",
        ] {
            assert!(def.input_schema["properties"].get(forbidden).is_none());
        }
    }
}
