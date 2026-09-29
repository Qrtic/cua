from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path


INSTALLER = Path(__file__).resolve().parents[1] / "_install-rust.sh"


def extract_shell_function(name: str) -> str:
    source = INSTALLER.read_text()
    match = re.search(
        rf"(?ms)^{re.escape(name)}\(\) \{{\n.*?^\}}\n",
        source,
    )
    assert match, f"could not find shell function {name}"
    return match.group(0)


def run_policy(body: str) -> subprocess.CompletedProcess[str]:
    functions = "\n".join(
        extract_shell_function(name)
        for name in (
            "macos_requirement_compatibility",
            "macos_reset_tcc_after_requirement_change",
        )
    )
    return subprocess.run(
        ["/bin/bash", "-c", f"set -euo pipefail\n{functions}\n{body}"],
        check=False,
        capture_output=True,
        text=True,
    )


def run_release_identity_policy(
    body: str, env: dict[str, str] | None = None
) -> subprocess.CompletedProcess[str]:
    functions = "\n".join(
        extract_shell_function(name)
        for name in (
            "validate_apple_team_id",
            "macos_bundle_value",
            "macos_verify_release_app",
            "macos_verify_build_attestation",
            "directory_has_entries",
            "macos_refuse_legacy_history_identity_transition",
        )
    )
    return subprocess.run(
        ["/bin/bash", "-c", f"set -euo pipefail\n{functions}\n{body}"],
        check=False,
        capture_output=True,
        text=True,
        env={**os.environ, **(env or {})},
    )


def run_rollback_policy(body: str, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    function = extract_shell_function("restore_macos_app_backup_on_exit")
    stubs = r'''
    macos_verify_release_app() {
        [[ -z "${REJECT_APP_PATH:-}" || "$1" != "$REJECT_APP_PATH" ]]
    }
    macos_register_app() {
        if [[ -n "${REGISTER_LOG:-}" ]]; then
            printf '%s\n' "$1" >> "$REGISTER_LOG"
        fi
    }
    PRODUCTION_BUNDLE_ID="${PRODUCTION_BUNDLE_ID:-com.meta.musecode.cua.driver}"
    PRODUCTION_TEAM_ID="${PRODUCTION_TEAM_ID:-A1B2C3D4E5}"
    MACOS_APP_BACKUP_BUNDLE_ID="${MACOS_APP_BACKUP_BUNDLE_ID:-com.meta.musecode.cua.driver}"
    MACOS_APP_BACKUP_TEAM_ID="${MACOS_APP_BACKUP_TEAM_ID:-A1B2C3D4E5}"
    BINARY_NAME="${BINARY_NAME:-cua-driver}"
    '''
    return subprocess.run(
        ["/bin/bash", "-c", f"set -euo pipefail\n{function}\n{stubs}\n{body}"],
        check=False,
        capture_output=True,
        text=True,
        env={**os.environ, **env},
    )


def test_semantically_compatible_requirement_preserves_tcc_rows() -> None:
    result = run_policy(
        r'''
        err() { printf 'error: %s\n' "$*" >&2; }
        log() { printf 'log: %s\n' "$*"; }
        codesign() {
            [[ "$1" == "--verify" ]]
            [[ "$4" == '-R' ]]
            [[ "$5" == '=identifier "com.meta.musecode.cua.driver" and anchor apple generic' ]]
            [[ "$6" == '/replacement.app' ]]
        }
        tccutil() { echo unexpected >&2; return 99; }
        compatibility="$(macos_requirement_compatibility \
            'identifier "com.meta.musecode.cua.driver" and anchor apple generic' \
            /replacement.app)"
        [[ "$compatibility" == compatible ]]
        macos_reset_tcc_after_requirement_change "$compatibility"
        '''
    )

    assert result.returncode == 0, result.stderr
    assert "unexpected" not in result.stderr


def test_incompatible_requirement_resets_only_driver_permissions() -> None:
    result = run_policy(
        r'''
        err() { printf 'error: %s\n' "$*" >&2; }
        log() { printf 'log: %s\n' "$*"; }
        codesign() { return 3; }
        calls=""
        tccutil() { calls="${calls}${1}:${2}:${3}"$'\n'; }
        compatibility="$(macos_requirement_compatibility 'old requirement' /replacement.app)"
        [[ "$compatibility" == incompatible ]]
        macos_reset_tcc_after_requirement_change "$compatibility"
        printf '%s' "$calls"
        '''
    )

    assert result.returncode == 0, result.stderr
    assert result.stdout == (
        "log: the app signing requirement changed; cleared stale Accessibility and Screen Recording rows\n"
        "log: macOS authorization is required again: cua-driver permissions grant\n"
        "reset:Accessibility:com.meta.musecode.cua.driver\n"
        "reset:ScreenCapture:com.meta.musecode.cua.driver\n"
    )


def test_unknown_previous_requirement_does_not_destroy_grants() -> None:
    result = run_policy(
        r'''
        err() { printf 'error: %s\n' "$*" >&2; }
        log() { printf 'log: %s\n' "$*"; }
        codesign() { echo unexpected >&2; return 99; }
        tccutil() { echo unexpected >&2; return 99; }
        compatibility="$(macos_requirement_compatibility '' /replacement.app)"
        [[ "$compatibility" == unknown ]]
        macos_reset_tcc_after_requirement_change "$compatibility"
        '''
    )

    assert result.returncode == 0, result.stderr
    assert "unexpected" not in result.stderr


def test_requirement_evaluation_error_does_not_destroy_grants() -> None:
    result = run_policy(
        r'''
        err() { printf 'error: %s\n' "$*" >&2; }
        log() { printf 'log: %s\n' "$*"; }
        codesign() { echo 'malformed requirement' >&2; return 1; }
        tccutil() { echo unexpected >&2; return 99; }
        compatibility="$(macos_requirement_compatibility 'malformed' /replacement.app)"
        [[ "$compatibility" == unknown ]]
        macos_reset_tcc_after_requirement_change "$compatibility"
        '''
    )

    assert result.returncode == 0, result.stderr
    assert "could not evaluate the previous code-signing requirement" in result.stderr
    assert "unexpected" not in result.stderr


def test_reset_failure_is_actionable_and_returns_failure() -> None:
    result = run_policy(
        r'''
        err() { printf 'error: %s\n' "$*" >&2; }
        log() { printf 'log: %s\n' "$*"; }
        tccutil() { [[ "$2" != ScreenCapture ]]; }
        if macos_reset_tcc_after_requirement_change incompatible; then
            exit 90
        fi
        '''
    )

    assert result.returncode == 0, result.stderr
    assert "could not reset these TCC services" in result.stderr
    assert "tccutil reset Accessibility com.meta.musecode.cua.driver" in result.stderr
    assert "tccutil reset ScreenCapture com.meta.musecode.cua.driver" in result.stderr


def test_installer_verifies_then_registers_before_any_tcc_reset() -> None:
    source = INSTALLER.read_text()
    install = source.index('if [[ "$OS" == "Darwin" && -n "$SRC_APP"')
    staged_verify = source.index('macos_verify_release_app "$SRC_APP"', install)
    build_attestation = source.index(
        'macos_verify_build_attestation "$SRC_APP"', staged_verify
    )
    stop_daemon = source.index("stop_cua_driver_daemons", build_attestation)
    backup = source.index('mv "$APP_DEST" "$MACOS_APP_BACKUP"', staged_verify)
    copy = source.index('ditto "$SRC_APP" "$APP_DEST"', backup)
    installed_verify = source.index('macos_verify_release_app "$APP_DEST"', copy)
    register = source.index('macos_register_app "$APP_DEST"', installed_verify)
    reset = source.index("macos_reset_tcc_after_requirement_change", register)
    link = source.index('ln -sf "$APP_BINARY" "$BIN_LINK"', reset)
    commit = source.index("MACOS_APP_INSTALL_COMMITTED=1", link)

    assert (
        staged_verify
        < build_attestation
        < stop_daemon
        < backup
        < copy
        < installed_verify
        < register
        < reset
        < link
        < commit
    )


def test_only_the_release_bundle_identity_can_trigger_a_tcc_reset() -> None:
    source = INSTALLER.read_text()

    assert 'STAGED_BUNDLE_ID' in source
    assert 'PRODUCTION_BUNDLE_ID="com.meta.musecode.cua.driver"' in source
    assert '[[ "$PREV_BUNDLE_ID" == "$PRODUCTION_BUNDLE_ID" ]]' in source
    assert 'INSTALLED_BUNDLE_ID" == "$STAGED_BUNDLE_ID"' in source


def test_legacy_release_identity_is_an_explicit_fresh_permission_migration() -> None:
    source = INSTALLER.read_text()

    assert 'elif [[ "$PREV_BUNDLE_ID" == "$LEGACY_PRODUCTION_BUNDLE_ID" ]]' in source
    assert "MIGRATED_LEGACY_ID=1" in source
    assert (
        "Migrated CuaDriver.app from com.trycua.driver to "
        "com.meta.musecode.cua.driver."
    ) in source
    assert "Legacy TCC rows were cleared safely." in source
    migration = source.index('if [[ "$MIGRATED_LEGACY_ID" == "1" ]]')
    history_guard = source.index("macos_refuse_legacy_history_identity_transition", migration)
    tcc_reset = source.index("macos_reset_legacy_tcc_before_migration", history_guard)
    assert migration < history_guard < tcc_reset


def test_release_team_id_is_required_and_strictly_validated() -> None:
    result = run_release_identity_policy(
        """
        ! validate_apple_team_id ''
        ! validate_apple_team_id 'lowercase1'
        ! validate_apple_team_id 'TOO-SHORT'
        validate_apple_team_id 'A1B2C3D4E5'
        """
    )

    assert result.returncode == 0, result.stderr
    source = INSTALLER.read_text()
    assert 'PRODUCTION_TEAM_ID="${CUA_DRIVER_PRODUCTION_TEAM_ID:-}"' in source
    assert 'validate_apple_team_id "$PRODUCTION_TEAM_ID"' in source


def test_release_app_requires_exact_team_apple_anchor_and_notarization(
    tmp_path: Path,
) -> None:
    app = tmp_path / "CuaDriver.app"
    binary = app / "Contents/MacOS/cua-driver"
    binary.parent.mkdir(parents=True)
    (app / "Contents/Info.plist").write_text("fixture")
    binary.write_text("fixture")
    binary.chmod(0o755)

    result = run_release_identity_policy(
        f"""
        calls=''
        macos_bundle_value() {{
            case "$2" in
                CFBundleIdentifier) printf '%s' 'com.meta.musecode.cua.driver' ;;
                CFBundleExecutable) printf '%s' 'cua-driver' ;;
                *) return 1 ;;
            esac
        }}
        codesign() {{
            calls="${{calls}}codesign:$*"$'\\n'
            if [[ "$1" == '-d' ]]; then
                printf '%s\\n' 'TeamIdentifier=A1B2C3D4E5' >&2
            fi
            return 0
        }}
        spctl() {{ printf '%s\\n' 'source=Notarized Developer ID' >&2; return 0; }}
        macos_verify_release_app '{app}' \
            com.meta.musecode.cua.driver cua-driver A1B2C3D4E5
        printf '%s' "$calls"
        """
    )

    assert result.returncode == 0, result.stderr
    assert (
        '-R =anchor apple generic and identifier "com.meta.musecode.cua.driver" '
        'and certificate leaf[subject.OU] = "A1B2C3D4E5"'
    ) in result.stdout
    assert "source=Notarized Developer ID" in INSTALLER.read_text()


def test_release_app_rejects_wrong_team_or_failed_notarization(tmp_path: Path) -> None:
    app = tmp_path / "CuaDriver.app"
    binary = app / "Contents/MacOS/cua-driver"
    binary.parent.mkdir(parents=True)
    (app / "Contents/Info.plist").write_text("fixture")
    binary.write_text("fixture")
    binary.chmod(0o755)
    common = f"""
        macos_bundle_value() {{
            [[ "$2" == CFBundleIdentifier ]] \
                && printf '%s' com.meta.musecode.cua.driver \
                || printf '%s' cua-driver
        }}
    """
    wrong_team = run_release_identity_policy(
        common
        + f"""
        codesign() {{
            [[ "$1" == '-d' ]] && printf '%s\\n' 'TeamIdentifier=OTHERTEAM1' >&2
            return 0
        }}
        spctl() {{ echo unexpected; return 0; }}
        ! macos_verify_release_app '{app}' \
            com.meta.musecode.cua.driver cua-driver A1B2C3D4E5
        """
    )
    failed_notarization = run_release_identity_policy(
        common
        + f"""
        codesign() {{
            [[ "$1" == '-d' ]] && printf '%s\\n' 'TeamIdentifier=A1B2C3D4E5' >&2
            return 0
        }}
        spctl() {{ printf '%s\\n' 'source=Developer ID' >&2; return 0; }}
        ! macos_verify_release_app '{app}' \
            com.meta.musecode.cua.driver cua-driver A1B2C3D4E5
        """
    )

    assert wrong_team.returncode == 0, wrong_team.stderr
    assert "unexpected" not in wrong_team.stdout
    assert failed_notarization.returncode == 0, failed_notarization.stderr


def test_staged_binary_attestation_matches_bundle_and_team_pins(tmp_path: Path) -> None:
    app = tmp_path / "CuaDriver.app"
    binary = app / "Contents/MacOS/cua-driver"
    marker = tmp_path / "attestation-invoked"
    binary.parent.mkdir(parents=True)
    binary.write_text(
        "#!/bin/sh\n"
        "test \"$#\" = 1\n"
        "test \"$1\" = __build-attestation\n"
        f"printf invoked > '{marker}'\n"
        "printf '%s\\n' '{\"schema_version\":1}'\n"
    )
    binary.chmod(0o755)
    fake_plutil = tmp_path / "plutil"
    fake_plutil.write_text(
        "#!/bin/sh\n"
        "case \"$1\" in\n"
        "  -convert) /bin/cp \"$5\" \"$4\" ;;\n"
        "  -extract)\n"
        "    case \"$2\" in\n"
        "      schema_version) printf '%s' \"${TEST_ATTESTATION_SCHEMA:-1}\" ;;\n"
        "      bundle_id) printf '%s' \"${TEST_ATTESTATION_BUNDLE:-com.meta.musecode.cua.driver}\" ;;\n"
        "      production_team_id) printf '%s' \"${TEST_ATTESTATION_TEAM:-A1B2C3D4E5}\" ;;\n"
        "      *) exit 2 ;;\n"
        "    esac ;;\n"
        "  *) exit 2 ;;\n"
        "esac\n"
    )
    fake_plutil.chmod(0o755)
    temp = tmp_path / "temp"
    temp.mkdir()
    body = f"""
        BINARY_NAME=cua-driver
        TMP_DIR='{temp}'
        MACOS_PLUTIL='{fake_plutil}'
        macos_verify_build_attestation '{app}' \
            com.meta.musecode.cua.driver A1B2C3D4E5
    """
    result = run_release_identity_policy(body)

    assert result.returncode == 0, result.stderr
    assert marker.read_text() == "invoked"


def test_staged_binary_attestation_rejects_mismatched_embedded_pins(
    tmp_path: Path,
) -> None:
    app = tmp_path / "CuaDriver.app"
    binary = app / "Contents/MacOS/cua-driver"
    binary.parent.mkdir(parents=True)
    binary.write_text("#!/bin/sh\nprintf '%s\\n' '{\"schema_version\":1}'\n")
    binary.chmod(0o755)
    fake_plutil = tmp_path / "plutil"
    fake_plutil.write_text(
        "#!/bin/sh\n"
        "case \"$1:$2\" in\n"
        "  -convert:xml1) /bin/cp \"$5\" \"$4\" ;;\n"
        "  -extract:schema_version) printf 1 ;;\n"
        "  -extract:bundle_id) printf '%s' \"$TEST_ATTESTATION_BUNDLE\" ;;\n"
        "  -extract:production_team_id) printf '%s' \"$TEST_ATTESTATION_TEAM\" ;;\n"
        "  *) exit 2 ;;\n"
        "esac\n"
    )
    fake_plutil.chmod(0o755)
    temp = tmp_path / "temp"
    temp.mkdir()
    body = f"""
        BINARY_NAME=cua-driver
        TMP_DIR='{temp}'
        MACOS_PLUTIL='{fake_plutil}'
        ! macos_verify_build_attestation '{app}' \
            com.meta.musecode.cua.driver A1B2C3D4E5
    """
    wrong_team = run_release_identity_policy(
        body,
        {
            "TEST_ATTESTATION_BUNDLE": "com.meta.musecode.cua.driver",
            "TEST_ATTESTATION_TEAM": "OTHERTEAM1",
        },
    )
    wrong_bundle = run_release_identity_policy(
        body,
        {
            "TEST_ATTESTATION_BUNDLE": "com.example.lookalike",
            "TEST_ATTESTATION_TEAM": "A1B2C3D4E5",
        },
    )

    assert wrong_team.returncode == 0, wrong_team.stderr
    assert wrong_bundle.returncode == 0, wrong_bundle.stderr


def test_legacy_history_blocks_identity_migration_without_deleting_state(
    tmp_path: Path,
) -> None:
    history = tmp_path / "computer-history"
    history.mkdir()
    marker = history / "segment.enc"
    marker.write_text("encrypted")
    result = run_release_identity_policy(
        """
        err() { printf 'error: %s\\n' "$*" >&2; }
        MACOS_HISTORY_ROOT="$TEST_HISTORY_ROOT"
        APP_DEST=/Applications/CuaDriver.app
        BINARY_NAME=cua-driver
        ! macos_refuse_legacy_history_identity_transition
        """,
        {"TEST_HISTORY_ROOT": str(history)},
    )

    assert result.returncode == 0
    assert marker.read_text() == "encrypted"
    assert "cannot migrate com.trycua.driver" in result.stderr
    assert "history purge-offline --yes" in result.stderr


def test_legacy_tcc_cleanup_is_scoped_and_fails_closed() -> None:
    function = extract_shell_function("macos_reset_legacy_tcc_before_migration")
    result = subprocess.run(
        [
            "/bin/bash",
            "-c",
            f"""set -euo pipefail
            {function}
            err() {{ printf 'error: %s\\n' "$*" >&2; }}
            log() {{ printf 'log: %s\\n' "$*"; }}
            macos_register_app() {{ return 0; }}
            calls=''
            tccutil() {{
                calls="${{calls}}${{1}}:${{2}}:${{3}}"$'\\n'
                [[ "$2" != ScreenCapture ]]
            }}
            LEGACY_PRODUCTION_BUNDLE_ID=com.trycua.driver
            APP_DEST=/Applications/CuaDriver.app
            if macos_reset_legacy_tcc_before_migration; then
                exit 90
            fi
            printf '%s' "$calls"
            """,
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr
    assert result.stdout.splitlines() == [
        "reset:Accessibility:com.trycua.driver",
        "reset:ScreenCapture:com.trycua.driver",
        "reset:AppleEvents:com.trycua.driver",
    ]
    assert "legacy app was preserved" in result.stderr


def test_exit_cleanup_restores_the_previous_app(tmp_path: Path) -> None:
    app = tmp_path / "CuaDriver.app"
    backup = tmp_path / "CuaDriver.app.install-backup"
    register_log = tmp_path / "register.log"
    app.mkdir()
    (app / "candidate").write_text("partial")
    backup.mkdir()
    (backup / "previous").write_text("valid")

    result = run_rollback_policy(
        "restore_macos_app_backup_on_exit",
        {
            "APP_DEST": str(app),
            "MACOS_APP_BACKUP": str(backup),
            "MACOS_APP_SWAP_STARTED": "1",
            "MACOS_APP_HAD_PREVIOUS": "1",
            "MACOS_APP_INSTALL_COMMITTED": "0",
            "REGISTER_LOG": str(register_log),
        },
    )

    assert result.returncode == 0, result.stderr
    assert (app / "previous").read_text() == "valid"
    assert not backup.exists()
    assert register_log.read_text().strip() == str(app)


def test_exit_cleanup_removes_a_partial_first_install(tmp_path: Path) -> None:
    app = tmp_path / "CuaDriver.app"
    app.mkdir()
    (app / "candidate").write_text("partial")

    result = run_rollback_policy(
        "restore_macos_app_backup_on_exit",
        {
            "APP_DEST": str(app),
            "MACOS_APP_BACKUP": str(tmp_path / "missing-backup"),
            "MACOS_APP_SWAP_STARTED": "1",
            "MACOS_APP_HAD_PREVIOUS": "0",
            "MACOS_APP_INSTALL_COMMITTED": "0",
        },
    )

    assert result.returncode == 0, result.stderr
    assert not app.exists()


def test_exit_cleanup_leaves_a_committed_install_untouched(tmp_path: Path) -> None:
    app = tmp_path / "CuaDriver.app"
    backup = tmp_path / "CuaDriver.app.install-backup"
    app.mkdir()
    (app / "candidate").write_text("valid")
    backup.mkdir()
    (backup / "previous").write_text("old")

    result = run_rollback_policy(
        "restore_macos_app_backup_on_exit",
        {
            "APP_DEST": str(app),
            "MACOS_APP_BACKUP": str(backup),
            "MACOS_APP_SWAP_STARTED": "1",
            "MACOS_APP_HAD_PREVIOUS": "0",
            "MACOS_APP_INSTALL_COMMITTED": "1",
        },
    )

    assert result.returncode == 0, result.stderr
    assert (app / "candidate").read_text() == "valid"
    assert not backup.exists()


def test_rollback_preserves_an_unauthenticated_failed_candidate(tmp_path: Path) -> None:
    app = tmp_path / "CuaDriver.app"
    backup = tmp_path / "CuaDriver.app.install-backup"
    app.mkdir()
    (app / "untrusted").write_text("preserve")
    backup.mkdir()
    (backup / "previous").write_text("valid")

    result = run_rollback_policy(
        "restore_macos_app_backup_on_exit",
        {
            "APP_DEST": str(app),
            "MACOS_APP_BACKUP": str(backup),
            "MACOS_APP_SWAP_STARTED": "1",
            "MACOS_APP_HAD_PREVIOUS": "1",
            "MACOS_APP_INSTALL_COMMITTED": "0",
            "REJECT_APP_PATH": str(app),
        },
    )

    assert result.returncode == 0, result.stderr
    assert (app / "previous").read_text() == "valid"
    preserved = list(tmp_path.glob("CuaDriver.app.failed-install.*"))
    assert len(preserved) == 1
    assert (preserved[0] / "untrusted").read_text() == "preserve"
