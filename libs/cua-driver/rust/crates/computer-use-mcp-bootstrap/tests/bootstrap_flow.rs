#![cfg(unix)]

use std::fs::{self, File};
use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::thread;
use std::time::{Duration, Instant};

use serde_json::{json, Value};
use tempfile::TempDir;

struct Host {
    child: Child,
    stdin: ChildStdin,
    lines: Receiver<String>,
}

impl Host {
    fn send(&mut self, value: Value) {
        serde_json::to_writer(&mut self.stdin, &value).unwrap();
        self.stdin.write_all(b"\n").unwrap();
        self.stdin.flush().unwrap();
    }

    fn receive(&self) -> Value {
        let line = self
            .lines
            .recv_timeout(Duration::from_secs(3))
            .expect("bootstrap response timeout");
        serde_json::from_str(&line).expect("valid bootstrap JSON-RPC response")
    }
}

impl Drop for Host {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn write_script(path: &Path, contents: &str) {
    fs::write(path, contents).unwrap();
}

fn spawn_host_with_scripts(temp: &TempDir, setup_contents: &str, backend_contents: &str) -> Host {
    let setup = temp.path().join("setup.sh");
    let backend = temp.path().join("backend.sh");
    let starts = temp.path().join("setup-starts");
    let gate = temp.path().join("permission-gate");
    let catalog = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/tool_catalog.json");

    write_script(&setup, setup_contents);
    write_script(&backend, backend_contents);

    let binary = env!("CARGO_BIN_EXE_computer-use-mcp-bootstrap");
    let mut child = Command::new(binary)
        .arg("--plugin-version")
        .arg("0.6.0")
        .arg("--setup-program")
        .arg("/bin/sh")
        .arg("--setup-arg")
        .arg(&setup)
        .arg("--setup-arg")
        .arg(&starts)
        .arg("--setup-arg")
        .arg(&gate)
        .arg("--backend-program")
        .arg("/bin/sh")
        .arg("--backend-arg")
        .arg(&backend)
        .arg("--backend-arg")
        .arg(&catalog)
        .arg("--backend-arg")
        .arg(&gate)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let (sender, lines) = mpsc::channel();
    thread::spawn(move || {
        for line in BufReader::new(stdout).lines() {
            if sender.send(line.unwrap()).is_err() {
                break;
            }
        }
    });
    Host {
        child,
        stdin,
        lines,
    }
}

const NORMAL_SETUP: &str = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf 'downloading verified archives\n'
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_pending","stage":"accessibility","retryable":true,"requires_user_action":true,"accessibility":false,"screen_recording":false,"screen_recording_capturable":null}'
while [ ! -f "$2" ]; do /bin/sleep 0.01; done
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_pending","stage":"screen_recording","retryable":true,"requires_user_action":true,"accessibility":true,"screen_recording":false,"screen_recording_capturable":null}'
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_pending","stage":"capture_verification","retryable":true,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":null}'
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;

const NORMAL_BACKEND: &str = r#"#!/bin/sh
set -eu
catalog=$1
IFS= read -r initialize
printf '%s\n' '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/initialize","result":{"protocolVersion":"2025-06-18","capabilities":{"tools":{}},"serverInfo":{"name":"fake","version":"1"}}}'
IFS= read -r initialized
IFS= read -r tools_list
tools=$(/usr/bin/tr -d '\n' < "$catalog")
printf '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/tools-list","result":{"tools":%s}}\n' "$tools"
while IFS= read -r request; do
  case "$request" in
    *'"method":"tools/call"'*)
      printf '%s\n' '{"jsonrpc":"2.0","id":5,"result":{"content":[{"type":"text","text":"proxied"}],"structuredContent":{"proxied":true}}}'
      ;;
  esac
done
"#;

fn spawn_host(temp: &TempDir) -> Host {
    spawn_host_with_scripts(temp, NORMAL_SETUP, NORMAL_BACKEND)
}

#[test]
fn negotiates_and_forwards_the_canonical_protocol_version() {
    let temp = TempDir::new().unwrap();
    let gate = temp.path().join("permission-gate");
    let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;
    let backend = r#"#!/bin/sh
set -eu
IFS= read -r initialize
printf '%s\n' "$initialize" > "$2.initialize"
printf '%s\n' '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/initialize","result":{"protocolVersion":"2025-06-18","capabilities":{"tools":{}}}}'
/bin/sleep 30
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, backend);
    host.send(json!({
        "jsonrpc":"2.0",
        "id":1,
        "method":"initialize",
        "params":{
            "protocolVersion":"2024-11-05",
            "capabilities":{"roots":{"listChanged":true}},
            "clientInfo":{"name":"legacy-client","version":"1"}
        }
    }));
    let initialized = host.receive();
    assert_eq!(initialized["result"]["protocolVersion"], "2025-06-18");
    host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();

    let marker = gate.with_extension("initialize");
    let deadline = Instant::now() + Duration::from_secs(3);
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "backend did not receive initialize"
        );
        thread::sleep(Duration::from_millis(10));
    }
    let forwarded: Value = serde_json::from_str(&fs::read_to_string(marker).unwrap()).unwrap();
    assert_eq!(forwarded["params"]["protocolVersion"], "2025-06-18");
    assert_eq!(forwarded["params"]["clientInfo"]["name"], "legacy-client");
    assert_eq!(
        forwarded["params"]["capabilities"]["roots"]["listChanged"],
        true
    );
}

#[test]
fn initializes_lists_then_setups_once_and_proxies_without_reconnect() {
    let temp = TempDir::new().unwrap();
    let starts = temp.path().join("setup-starts");
    let gate = temp.path().join("permission-gate");
    let mut host = spawn_host(&temp);

    host.send(json!({
        "jsonrpc":"2.0",
        "id":1,
        "method":"initialize",
        "params":{
            "protocolVersion":"2025-06-18",
            "capabilities":{},
            "clientInfo":{"name":"test","version":"1"}
        }
    }));
    let initialized = host.receive();
    assert_eq!(initialized["result"]["serverInfo"]["version"], "0.6.0");
    assert!(initialized["result"]["instructions"]
        .as_str()
        .unwrap()
        .ends_with(include_str!("../src/initialize_instructions.txt").trim_end()));
    host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));

    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/list","params":{}}));
    let listed = host.receive();
    assert_eq!(listed["result"]["tools"].as_array().unwrap().len(), 11);
    assert!(!starts.exists(), "tools/list must not start setup");

    host.send(json!({
        "jsonrpc":"2.0",
        "id":3,
        "method":"tools/call",
        "params":{"name":"list_apps","arguments":{}}
    }));
    let pending = host.receive();
    assert_eq!(
        pending["result"]["structuredContent"],
        json!({
            "schema_version":1,
            "code":"computer_use_setup_pending",
            "stage":"installing",
            "retryable":true,
            "requires_user_action":false
        })
    );

    File::create(&gate).unwrap();
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        assert!(Instant::now() < deadline, "backend never became ready");
        host.send(json!({
            "jsonrpc":"2.0",
            "id":5,
            "method":"tools/call",
            "params":{"name":"list_apps","arguments":{}}
        }));
        let response = host.receive();
        if response["result"]["structuredContent"]["proxied"] == true {
            break;
        }
        assert_eq!(
            response["result"]["structuredContent"]["code"],
            "computer_use_setup_pending"
        );
        thread::sleep(Duration::from_millis(20));
    }

    assert_eq!(fs::read_to_string(starts).unwrap(), "start\n");
    host.send(json!({"jsonrpc":"2.0","id":6,"method":"shutdown"}));
    assert_eq!(host.receive()["result"], Value::Null);
}

#[test]
fn autonomous_service_starting_call_waits_and_is_forwarded_when_ready() {
    let temp = TempDir::new().unwrap();
    let gate = temp.path().join("permission-gate");
    let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_pending","stage":"service_starting","retryable":true,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
: > "$2.service-starting"
while [ ! -f "$2" ]; do /bin/sleep 0.01; done
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, NORMAL_BACKEND);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();

    let marker = gate.with_extension("service-starting");
    let deadline = Instant::now() + Duration::from_secs(3);
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "service-starting was not emitted"
        );
        thread::sleep(Duration::from_millis(10));
    }
    host.send(json!({"jsonrpc":"2.0","id":5,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    assert!(
        host.lines.recv_timeout(Duration::from_millis(150)).is_err(),
        "autonomous finalization returned a premature pending result"
    );
    File::create(&gate).unwrap();
    let response = host.receive();
    assert_eq!(response["id"], 5);
    assert_eq!(response["result"]["structuredContent"]["proxied"], true);
}

#[test]
fn cancelling_one_deferred_call_does_not_stop_setup_or_other_waiters() {
    let temp = TempDir::new().unwrap();
    let gate = temp.path().join("permission-gate");
    let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_pending","stage":"service_starting","retryable":true,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
trap 'printf "cancelled\n" > "$2.cancelled"; exit 130' INT TERM
: > "$2.service-starting"
while [ ! -f "$2" ]; do /bin/sleep 0.01; done
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;
    let backend = r#"#!/bin/sh
set -eu
catalog=$1
IFS= read -r initialize
printf '%s\n' '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/initialize","result":{"protocolVersion":"2025-06-18","capabilities":{"tools":{}}}}'
IFS= read -r initialized
IFS= read -r tools_list
tools=$(/usr/bin/tr -d '\n' < "$catalog")
printf '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/tools-list","result":{"tools":%s}}\n' "$tools"
IFS= read -r call
printf '%s\n' '{"jsonrpc":"2.0","id":8,"result":{"content":[{"type":"text","text":"proxied"}],"structuredContent":{"proxied":true}}}'
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, backend);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();

    let marker = gate.with_extension("service-starting");
    let deadline = Instant::now() + Duration::from_secs(3);
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "service-starting was not emitted"
        );
        thread::sleep(Duration::from_millis(10));
    }
    for id in [7, 8] {
        host.send(json!({"jsonrpc":"2.0","id":id,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    }
    host.send(json!({"jsonrpc":"2.0","method":"notifications/cancelled","params":{"requestId":7,"reason":"test"}}));
    assert!(
        host.lines.recv_timeout(Duration::from_millis(150)).is_err(),
        "cancelled deferred call must not receive a response"
    );
    assert!(
        !gate.with_extension("cancelled").exists(),
        "one cancelled waiter stopped shared setup"
    );

    File::create(&gate).unwrap();
    let response = host.receive();
    assert_eq!(response["id"], 8);
    assert_eq!(response["result"]["structuredContent"]["proxied"], true);
    assert!(
        !gate.with_extension("cancelled").exists(),
        "shared setup was terminated instead of completing"
    );
}

#[test]
fn cancellation_for_unknown_request_does_not_stop_setup() {
    let temp = TempDir::new().unwrap();
    let gate = temp.path().join("permission-gate");
    let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_pending","stage":"accessibility","retryable":true,"requires_user_action":true,"accessibility":false,"screen_recording":false,"screen_recording_capturable":null}'
: > "$2.accessibility"
while [ ! -f "$2" ]; do /bin/sleep 0.01; done
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, NORMAL_BACKEND);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();
    let marker = gate.with_extension("accessibility");
    let deadline = Instant::now() + Duration::from_secs(3);
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "accessibility stage was not emitted"
        );
        thread::sleep(Duration::from_millis(10));
    }

    host.send(json!({"jsonrpc":"2.0","method":"notifications/cancelled","params":{"requestId":999,"reason":"stale"}}));
    host.send(json!({"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    let pending = host.receive();
    assert_eq!(pending["id"], 3);
    assert_eq!(
        pending["result"]["structuredContent"]["stage"],
        "accessibility"
    );
    File::create(&gate).unwrap();
}

#[test]
fn cancellation_during_backend_initialization_preserves_other_deferred_calls() {
    let temp = TempDir::new().unwrap();
    let gate = temp.path().join("permission-gate");
    let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;
    let backend = r#"#!/bin/sh
set -eu
catalog=$1
IFS= read -r initialize
: > "$2.backend-initialize"
while [ ! -f "$2" ]; do /bin/sleep 0.01; done
printf '%s\n' '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/initialize","result":{"protocolVersion":"2025-06-18","capabilities":{"tools":{}}}}'
IFS= read -r initialized
IFS= read -r tools_list
tools=$(/usr/bin/tr -d '\n' < "$catalog")
printf '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/tools-list","result":{"tools":%s}}\n' "$tools"
IFS= read -r call
printf '%s\n' '{"jsonrpc":"2.0","id":8,"result":{"content":[{"type":"text","text":"proxied"}],"structuredContent":{"proxied":true}}}'
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, backend);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();

    let marker = gate.with_extension("backend-initialize");
    let deadline = Instant::now() + Duration::from_secs(3);
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "backend initialization did not start"
        );
        thread::sleep(Duration::from_millis(10));
    }
    for id in [7, 8] {
        host.send(json!({"jsonrpc":"2.0","id":id,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    }
    host.send(json!({"jsonrpc":"2.0","method":"notifications/cancelled","params":{"requestId":7,"reason":"test"}}));
    assert!(
        host.lines.recv_timeout(Duration::from_millis(150)).is_err(),
        "cancelled request must not receive a response"
    );
    File::create(&gate).unwrap();

    let completed = host.receive();
    assert_eq!(completed["id"], 8);
    assert_eq!(completed["result"]["structuredContent"]["proxied"], true);
}

#[test]
fn retryable_setup_failure_is_reported_once_then_restarts_on_the_next_call() {
    let temp = TempDir::new().unwrap();
    let starts = temp.path().join("setup-starts");
    let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
count=$(/usr/bin/wc -l < "$1" | /usr/bin/tr -d ' ')
if [ "$count" = 1 ]; then
  printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_failed","stage":"failed","retryable":true,"requires_user_action":false,"accessibility":true,"screen_recording":false,"screen_recording_capturable":null,"error":{"code":"onboarding_host_exited","message":"restart after the permission change"}}'
  exit 1
fi
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, NORMAL_BACKEND);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    assert_eq!(
        host.receive()["result"]["structuredContent"]["code"],
        "computer_use_setup_pending"
    );

    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        assert!(
            Instant::now() < deadline,
            "retryable failure was not reported"
        );
        host.send(json!({"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
        let response = host.receive();
        let structured = &response["result"]["structuredContent"];
        if structured["code"] == "computer_use_setup_failed" {
            assert_eq!(structured["retryable"], true);
            break;
        }
        assert_eq!(structured["code"], "computer_use_setup_pending");
        thread::sleep(Duration::from_millis(20));
    }

    host.send(json!({"jsonrpc":"2.0","id":4,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    let restarted = host.receive();
    assert_eq!(
        restarted["result"]["structuredContent"]["code"],
        "computer_use_setup_pending"
    );
    let deadline = Instant::now() + Duration::from_secs(3);
    while fs::read_to_string(&starts)
        .unwrap_or_default()
        .lines()
        .count()
        < 2
    {
        assert!(Instant::now() < deadline, "setup was not restarted");
        thread::sleep(Duration::from_millis(10));
    }
    assert_eq!(fs::read_to_string(starts).unwrap().lines().count(), 2);
}

#[test]
fn nonretryable_setup_failure_never_restarts() {
    let temp = TempDir::new().unwrap();
    let starts = temp.path().join("setup-starts");
    let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_failed","stage":"failed","retryable":false,"requires_user_action":false,"error":{"code":"integrity_failed","message":"stop"}}'
exit 1
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, NORMAL_BACKEND);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();

    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        assert!(
            Instant::now() < deadline,
            "terminal failure was not reported"
        );
        host.send(json!({"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
        let response = host.receive();
        let structured = &response["result"]["structuredContent"];
        if structured["code"] == "computer_use_setup_failed" {
            assert_eq!(structured["retryable"], false);
            break;
        }
        thread::sleep(Duration::from_millis(20));
    }
    host.send(json!({"jsonrpc":"2.0","id":4,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    assert_eq!(
        host.receive()["result"]["structuredContent"]["retryable"],
        false
    );
    assert_eq!(fs::read_to_string(starts).unwrap(), "start\n");
}

#[test]
fn backend_exit_settles_every_forwarded_request_id() {
    let temp = TempDir::new().unwrap();
    let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;
    let backend = r#"#!/bin/sh
set -eu
catalog=$1
IFS= read -r initialize
printf '%s\n' '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/initialize","result":{"protocolVersion":"2025-06-18","capabilities":{"tools":{}},"serverInfo":{"name":"fake","version":"1"}}}'
IFS= read -r initialized
IFS= read -r tools_list
tools=$(/usr/bin/tr -d '\n' < "$catalog")
printf '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/tools-list","result":{"tools":%s}}\n' "$tools"
printf '%s\n' '{"jsonrpc":"2.0","method":"notifications/message","params":{"level":"info","data":"ready"}}'
IFS= read -r first
IFS= read -r second
exit 17
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, backend);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();

    let notification = host.receive();
    assert_eq!(notification["method"], "notifications/message");
    for id in [7, 8] {
        host.send(json!({"jsonrpc":"2.0","id":id,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    }
    let first = host.receive();
    let second = host.receive();
    assert_eq!(
        [first["id"].as_i64(), second["id"].as_i64()],
        [Some(7), Some(8)]
    );
    for response in [&first, &second] {
        assert_eq!(
            response["result"]["structuredContent"]["code"],
            "computer_use_backend_unavailable"
        );
        assert_eq!(response["result"]["structuredContent"]["retryable"], true);
    }
}

#[test]
fn backend_write_failure_settles_the_entire_deferred_batch() {
    let temp = TempDir::new().unwrap();
    let gate = temp.path().join("permission-gate");
    let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;
    let backend = r#"#!/bin/sh
set -eu
catalog=$1
IFS= read -r initialize
printf '%s\n' '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/initialize","result":{"protocolVersion":"2025-06-18","capabilities":{"tools":{}}}}'
IFS= read -r initialized
IFS= read -r tools_list
: > "$2.catalog-waiting"
while [ ! -f "$2" ]; do /bin/sleep 0.01; done
exec 0<&-
tools=$(/usr/bin/tr -d '\n' < "$catalog")
printf '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/tools-list","result":{"tools":%s}}\n' "$tools"
/bin/sleep 30
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, backend);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();

    let marker = gate.with_extension("catalog-waiting");
    let deadline = Instant::now() + Duration::from_secs(3);
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "backend did not reach catalog initialization"
        );
        thread::sleep(Duration::from_millis(10));
    }
    for id in [7, 8, 9] {
        host.send(json!({"jsonrpc":"2.0","id":id,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    }
    File::create(&gate).unwrap();

    let mut settled_ids = Vec::new();
    for _ in 0..3 {
        let response = host.receive();
        settled_ids.push(response["id"].as_i64().unwrap());
        assert_eq!(
            response["result"]["structuredContent"]["code"],
            "computer_use_backend_unavailable"
        );
        assert_eq!(response["result"]["structuredContent"]["retryable"], true);
    }
    settled_ids.sort_unstable();
    assert_eq!(settled_ids, [7, 8, 9]);
}

#[test]
fn invalid_ready_backend_responses_fail_before_retiring_the_request() {
    let cases = [
        r#"{"id":7,"result":{"unexpected":true}}"#,
        r#"{"jsonrpc":"2.0","id":7,"result":{},"error":{"code":-32000,"message":"both"}}"#,
    ];
    for (index, invalid_response) in cases.into_iter().enumerate() {
        let temp = TempDir::new().unwrap();
        let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;
        let backend = format!(
            r#"#!/bin/sh
set -eu
catalog=$1
IFS= read -r initialize
printf '%s\n' '{{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/initialize","result":{{"protocolVersion":"2025-06-18","capabilities":{{"tools":{{}}}}}}}}'
IFS= read -r initialized
IFS= read -r tools_list
tools=$(/usr/bin/tr -d '\n' < "$catalog")
printf '{{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/tools-list","result":{{"tools":%s}}}}\n' "$tools"
printf '%s\n' '{{"jsonrpc":"2.0","method":"notifications/message","params":{{"level":"info","data":"ready"}}}}'
IFS= read -r call
printf '%s\n' '{}'
/bin/sleep 30
"#,
            invalid_response
        );
        let mut host = spawn_host_with_scripts(&temp, setup, &backend);
        host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
        host.receive();
        host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
        host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
        host.receive();
        assert_eq!(host.receive()["method"], "notifications/message");
        host.send(json!({"jsonrpc":"2.0","id":7,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
        let failure = host.receive();
        assert_eq!(failure["id"], 7, "case {index}");
        assert_eq!(
            failure["result"]["structuredContent"]["code"], "computer_use_backend_unavailable",
            "case {index}"
        );
    }
}

#[test]
fn cancellation_notification_reaches_the_ready_backend() {
    let temp = TempDir::new().unwrap();
    let cancellation_marker = temp.path().join("permission-gate.cancelled");
    let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;
    let backend = r#"#!/bin/sh
set -eu
catalog=$1
marker=$2.cancelled
IFS= read -r initialize
printf '%s\n' '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/initialize","result":{"protocolVersion":"2025-06-18","capabilities":{"tools":{}}}}'
IFS= read -r initialized
IFS= read -r tools_list
tools=$(/usr/bin/tr -d '\n' < "$catalog")
printf '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/tools-list","result":{"tools":%s}}\n' "$tools"
printf '%s\n' '{"jsonrpc":"2.0","method":"notifications/message","params":{"level":"info","data":"ready"}}'
IFS= read -r call
IFS= read -r cancelled
printf 'cancelled\n' > "$marker"
printf '%s\n' '{"jsonrpc":"2.0","method":"notifications/message","params":{"level":"info","data":"cancelled"}}'
exit 0
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, backend);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();
    assert_eq!(host.receive()["method"], "notifications/message");
    host.send(json!({"jsonrpc":"2.0","id":7,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.send(json!({"jsonrpc":"2.0","method":"notifications/cancelled","params":{"requestId":7,"reason":"test"}}));
    assert_eq!(host.receive()["params"]["data"], "cancelled");
    assert_eq!(
        fs::read_to_string(cancellation_marker).unwrap(),
        "cancelled\n"
    );
    assert!(
        host.lines.recv_timeout(Duration::from_millis(250)).is_err(),
        "cancelled request ID must not be failed after backend exit"
    );
}

#[test]
fn cancellation_write_failure_does_not_respond_to_the_cancelled_request() {
    let temp = TempDir::new().unwrap();
    let gate = temp.path().join("permission-gate");
    let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;
    let backend = r#"#!/bin/sh
set -eu
catalog=$1
IFS= read -r initialize
printf '%s\n' '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/initialize","result":{"protocolVersion":"2025-06-18","capabilities":{"tools":{}}}}'
IFS= read -r initialized
IFS= read -r tools_list
tools=$(/usr/bin/tr -d '\n' < "$catalog")
printf '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/tools-list","result":{"tools":%s}}\n' "$tools"
printf '%s\n' '{"jsonrpc":"2.0","method":"notifications/message","params":{"level":"info","data":"ready"}}'
IFS= read -r call
exec 0<&-
: > "$2.stdin-closed"
/bin/sleep 30
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, backend);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();
    assert_eq!(host.receive()["method"], "notifications/message");
    host.send(json!({"jsonrpc":"2.0","id":7,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));

    let marker = gate.with_extension("stdin-closed");
    let deadline = Instant::now() + Duration::from_secs(3);
    while !marker.exists() {
        assert!(Instant::now() < deadline, "backend stdin remained open");
        thread::sleep(Duration::from_millis(10));
    }
    host.send(json!({"jsonrpc":"2.0","method":"notifications/cancelled","params":{"requestId":7,"reason":"test"}}));
    assert!(
        host.lines.recv_timeout(Duration::from_millis(250)).is_err(),
        "cancelled request must not receive a response when cancellation forwarding fails"
    );
    host.send(json!({"jsonrpc":"2.0","id":8,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    let failure = host.receive();
    assert_eq!(failure["id"], 8);
    assert_eq!(
        failure["result"]["structuredContent"]["code"],
        "computer_use_setup_failed"
    );
}

#[test]
fn late_response_for_cancelled_request_is_discarded_without_poisoning_backend() {
    let temp = TempDir::new().unwrap();
    let marker = temp.path().join("permission-gate.late-response-written");
    let setup = r#"#!/bin/sh
set -eu
printf 'start\n' >> "$1"
printf '%s\n' '{"schema_version":1,"code":"computer_use_setup_ready","stage":"ready","retryable":false,"requires_user_action":false,"accessibility":true,"screen_recording":true,"screen_recording_capturable":true}'
"#;
    let backend = r#"#!/bin/sh
set -eu
catalog=$1
marker=$2.late-response-written
IFS= read -r initialize
printf '%s\n' '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/initialize","result":{"protocolVersion":"2025-06-18","capabilities":{"tools":{}}}}'
IFS= read -r initialized
IFS= read -r tools_list
tools=$(/usr/bin/tr -d '\n' < "$catalog")
printf '{"jsonrpc":"2.0","id":"computer-use-bootstrap/internal/tools-list","result":{"tools":%s}}\n' "$tools"
printf '%s\n' '{"jsonrpc":"2.0","method":"notifications/message","params":{"level":"info","data":"ready"}}'
IFS= read -r call
IFS= read -r cancelled
printf 'written\n' > "$marker"
printf '%s\n' '{"jsonrpc":"2.0","id":7,"result":{"content":[{"type":"text","text":"must not escape"}]}}'
IFS= read -r next_call
printf '%s\n' '{"jsonrpc":"2.0","id":8,"result":{"content":[{"type":"text","text":"proxied"}],"structuredContent":{"proxied":true}}}'
/bin/sleep 1
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, backend);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();
    assert_eq!(host.receive()["method"], "notifications/message");
    host.send(json!({"jsonrpc":"2.0","id":7,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.send(json!({"jsonrpc":"2.0","method":"notifications/cancelled","params":{"requestId":7,"reason":"test"}}));
    let deadline = Instant::now() + Duration::from_secs(3);
    while !marker.exists() {
        assert!(
            Instant::now() < deadline,
            "backend did not send its late response"
        );
        thread::sleep(Duration::from_millis(10));
    }
    assert!(
        host.lines.recv_timeout(Duration::from_millis(250)).is_err(),
        "late response for a cancelled request escaped the bootstrap"
    );
    host.send(json!({"jsonrpc":"2.0","id":8,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    let response = host.receive();
    assert_eq!(response["id"], 8);
    assert_eq!(response["result"]["structuredContent"]["proxied"], true);
}

#[test]
fn sigterm_reaches_the_active_setup_group_and_allows_cleanup_grace() {
    let temp = TempDir::new().unwrap();
    let gate = temp.path().join("permission-gate");
    let setup = r#"#!/bin/sh
exec python3 -c '
import os, pathlib, signal, sys, time
root = pathlib.Path(sys.argv[1])
pid = None
def stop_parent(_signal, _frame):
  time.sleep(2)
  root.with_suffix(".parent").write_text("parent\n")
  if pid is not None:
    os.waitpid(pid, 0)
  raise SystemExit(0)
signal.signal(signal.SIGINT, stop_parent)
signal.signal(signal.SIGTERM, stop_parent)
pid = os.fork()
if pid == 0:
  def stop_child(_signal, _frame):
    root.with_suffix(".child").write_text("child\n")
    raise SystemExit(0)
  signal.signal(signal.SIGINT, stop_child)
  signal.signal(signal.SIGTERM, stop_child)
  root.with_suffix(".ready").write_text("ready\n")
  while True:
    signal.pause()
while not root.with_suffix(".ready").exists():
  time.sleep(0.01)
print("{\"schema_version\":1,\"code\":\"computer_use_setup_pending\",\"stage\":\"accessibility\",\"retryable\":true,\"requires_user_action\":true,\"accessibility\":false,\"screen_recording\":false,\"screen_recording_capturable\":null}", flush=True)
while True:
  signal.pause()
' "$2"
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, NORMAL_BACKEND);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();

    let deadline = Instant::now() + Duration::from_secs(3);
    while !gate.with_extension("ready").exists() {
        assert!(Instant::now() < deadline, "setup descendant did not start");
        thread::sleep(Duration::from_millis(10));
    }
    unsafe {
        libc::kill(host.child.id() as i32, libc::SIGTERM);
    }
    let deadline = Instant::now() + Duration::from_secs(6);
    while host.child.try_wait().unwrap().is_none() {
        assert!(
            Instant::now() < deadline,
            "bootstrap did not exit on SIGTERM"
        );
        thread::sleep(Duration::from_millis(10));
    }
    let deadline = Instant::now() + Duration::from_secs(1);
    while (!gate.with_extension("parent").exists() || !gate.with_extension("child").exists())
        && Instant::now() < deadline
    {
        thread::sleep(Duration::from_millis(10));
    }
    assert_eq!(
        fs::read_to_string(gate.with_extension("parent")).unwrap(),
        "parent\n"
    );
    assert_eq!(
        fs::read_to_string(gate.with_extension("child")).unwrap(),
        "child\n"
    );
}

#[test]
fn cleanup_grace_survives_setup_leader_exiting_before_its_child() {
    let temp = TempDir::new().unwrap();
    let gate = temp.path().join("permission-gate");
    let setup = r#"#!/bin/sh
exec python3 -c '
import os, pathlib, signal, sys, time
root = pathlib.Path(sys.argv[1])
pid = os.fork()
if pid == 0:
  def stop_child(_signal, _frame):
    time.sleep(2)
    root.with_suffix(".child").write_text("child-clean\n")
    raise SystemExit(0)
  signal.signal(signal.SIGINT, stop_child)
  signal.signal(signal.SIGTERM, stop_child)
  root.with_suffix(".ready").write_text("ready\n")
  while True:
    signal.pause()
def stop_parent(_signal, _frame):
  raise SystemExit(0)
signal.signal(signal.SIGINT, stop_parent)
signal.signal(signal.SIGTERM, stop_parent)
while not root.with_suffix(".ready").exists():
  time.sleep(0.01)
print("{\"schema_version\":1,\"code\":\"computer_use_setup_pending\",\"stage\":\"accessibility\",\"retryable\":true,\"requires_user_action\":true,\"accessibility\":false,\"screen_recording\":false,\"screen_recording_capturable\":null}", flush=True)
while True:
  signal.pause()
' "$2"
"#;
    let mut host = spawn_host_with_scripts(&temp, setup, NORMAL_BACKEND);
    host.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    host.receive();
    host.send(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"list_apps","arguments":{}}}));
    host.receive();

    let deadline = Instant::now() + Duration::from_secs(3);
    while !gate.with_extension("ready").exists() {
        assert!(Instant::now() < deadline, "setup descendant did not start");
        thread::sleep(Duration::from_millis(10));
    }
    unsafe {
        libc::kill(host.child.id() as i32, libc::SIGTERM);
    }
    let deadline = Instant::now() + Duration::from_secs(6);
    while host.child.try_wait().unwrap().is_none() {
        assert!(
            Instant::now() < deadline,
            "bootstrap did not exit on SIGTERM"
        );
        thread::sleep(Duration::from_millis(10));
    }
    assert_eq!(
        fs::read_to_string(gate.with_extension("child")).unwrap(),
        "child-clean\n"
    );
}
