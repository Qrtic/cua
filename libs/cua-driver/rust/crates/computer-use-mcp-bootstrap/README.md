# Computer Use MCP bootstrap

`computer-use-mcp-bootstrap` is the small, persistent MCP host used by the
Computer Use plugin before its managed runtime is installed. It advertises the
fixed eleven-tool plugin contract immediately. The first valid tool call starts
setup once and returns `computer_use_setup_pending`; later calls are forwarded
to the verified Python wrapper in the same MCP process. Its initialize response
preserves the complete guarded-wrapper instructions, with first-use guidance
prepended.

```sh
computer-use-mcp-bootstrap \
  --plugin-version 0.6.0 \
  --setup-program /absolute/path/to/setup-runner \
  --setup-arg first-argument \
  --backend-program /absolute/path/to/backend-runner \
  --backend-arg first-argument
```

Both child programs are inherited-environment commands chosen by the trusted
plugin launcher. Option values are repeatable and passed verbatim. Programs
must be absolute paths to regular executable files; the backend is checked only
after setup because it may be installed by that setup.

Setup owns download verification and native onboarding. It may remain silent
while installing. Progress is one JSON object per stdout line; diagnostics go
to stderr. The status schema is:

```json
{
  "schema_version": 1,
  "code": "computer_use_setup_pending",
  "stage": "accessibility",
  "retryable": true,
  "requires_user_action": true,
  "accessibility": false,
  "screen_recording": false,
  "screen_recording_capturable": null
}
```

Pending stages are `installing`, `accessibility`,
`screen_recording_registration`, `screen_recording`, `driver_restarting`,
`tcc_propagation`, `capture_verification`, and `service_starting`. Only
`accessibility` and `screen_recording` require user action. The registration
stage performs the bounded app-owned ScreenCaptureKit request needed for macOS
to add the signed bundle to its Screen Recording privacy pane. Calls received
during an autonomous stage are held for a bounded
interval and forwarded when the backend becomes ready; a user-action stage
returns promptly so the user can complete the macOS step. Successful setup must emit
`computer_use_setup_ready` with stage `ready`, `retryable: false`, and all
three permission/verification booleans true, `requires_user_action: false`,
then exit zero. Any other terminal combination fails closed. A failed event's
`retryable` bit is preserved: one later call reports it, and only a retryable
failure re-arms setup for the call after that. The host initializes the backend
and requires its complete tool catalog to equal the embedded public catalog
before forwarding. It tracks every deferred and forwarded request ID and
resolves all outstanding calls with a structured failure if setup or the
backend exits. On Unix, child commands run in private process groups so
cancellation and host termination cannot leave ordinary descendants behind.
The bootstrap allows the group up to 25 seconds to exit cleanly before
escalating to `SIGKILL`; this contains the plugin relay's bounded 20-second
exact-daemon cleanup window.

`src/tool_catalog.json` and `src/initialize_instructions.txt` are generated
from the marketplace Python wrapper's public definitions and must be refreshed
together when that wrapper contract changes.
