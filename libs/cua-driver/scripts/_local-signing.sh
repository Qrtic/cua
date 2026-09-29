#!/usr/bin/env bash
#
# macOS local-development signing helpers for _install-local-rust.sh.
# This file has no top-level side effects so its policy can be exercised by
# focused shell tests without building or installing cua-driver.

CUA_LOCAL_SIGN_CN="CuaDriver Local Signing (cua-driver-rs)"

escape_extended_regex() {
    printf '%s' "$1" | sed 's/[][\\.^$*+?(){}|]/\\&/g'
}

local_signing_keychain() {
    if [ -n "${CUA_DRIVER_LOCAL_SIGNING_KEYCHAIN:-}" ]; then
        printf '%s' "$CUA_DRIVER_LOCAL_SIGNING_KEYCHAIN"
    elif [ -f "$HOME/Library/Keychains/cua-driver-signing.keychain-db" ]; then
        printf '%s' "$HOME/Library/Keychains/cua-driver-signing.keychain-db"
    elif [ -f "$HOME/Library/Keychains/login.keychain-db" ]; then
        printf '%s' "$HOME/Library/Keychains/login.keychain-db"
    else
        printf '%s' "$HOME/Library/Keychains/login.keychain"
    fi
}

print_local_signing_bootstrap() {
    echo "Create and unlock a dedicated development signing keychain, then rerun:" >&2
    echo "  SIGNING_KEYCHAIN=\"\$HOME/Library/Keychains/cua-driver-signing.keychain-db\"" >&2
    echo "  security create-keychain \"\$SIGNING_KEYCHAIN\"  # first time only; prompts for a password" >&2
    echo "  security set-keychain-settings \"\$SIGNING_KEYCHAIN\"" >&2
    echo "  security unlock-keychain \"\$SIGNING_KEYCHAIN\"" >&2
    echo "  export CUA_DRIVER_LOCAL_SIGNING_KEYCHAIN=\"\$SIGNING_KEYCHAIN\"" >&2
    echo "  bash libs/cua-driver/scripts/install-local.sh --require-stable-signing" >&2
    echo "If the certificate is newly created, authorize its private key for codesign as described in:" >&2
    echo "  libs/cua-driver/scripts/README.md#stable-macos-local-signing" >&2
}

# Echoes the `codesign --sign` argument: a matching identity's SHA-1 when
# available, or "-" when it cannot be created or found.
ensure_local_signing_identity() {
    { [ "$OS" = "Darwin" ] && command -v codesign >/dev/null 2>&1; } \
        || { printf -- '-'; return; }
    local kc
    kc="$(local_signing_keychain)"
    [ -f "$kc" ] || { printf -- '-'; return; }
    local identity
    if [ -n "${CUA_DRIVER_LOCAL_SIGNING_IDENTITY:-}" ]; then
        case "$CUA_DRIVER_LOCAL_SIGNING_IDENTITY" in
            *[!0-9A-Fa-f]*|'') printf -- '-'; return ;;
        esac
        [ "${#CUA_DRIVER_LOCAL_SIGNING_IDENTITY}" -eq 40 ] \
            || { printf -- '-'; return; }
        identity="$(security find-identity -p codesigning "$kc" 2>/dev/null \
            | awk -v wanted="$CUA_DRIVER_LOCAL_SIGNING_IDENTITY" \
                '{ for (field = 1; field <= NF; field++) if (toupper($field) == toupper(wanted)) { print $field; exit } }')"
        [ -n "$identity" ] && printf '%s' "$identity" || printf -- '-'
        return
    fi
    identity="$(security find-identity -p codesigning "$kc" 2>/dev/null \
        | awk -v cn="$CUA_LOCAL_SIGN_CN" 'index($0, "\"" cn "\"") { print $2; exit }')"
    if [ -n "$identity" ]; then
        printf '%s' "$identity"
        return
    fi
    command -v openssl >/dev/null 2>&1 || { printf -- '-'; return; }
    local tmp
    tmp="$(mktemp -d)" || { printf -- '-'; return; }
    printf '[req]\ndistinguished_name=dn\nx509_extensions=ext\nprompt=no\n[dn]\nCN=%s\n[ext]\nbasicConstraints=critical,CA:FALSE\nkeyUsage=critical,digitalSignature\nextendedKeyUsage=critical,codeSigning\n' \
        "$CUA_LOCAL_SIGN_CN" > "$tmp/req.cnf"
    local pw="cua-local-$$"
    if openssl req -x509 -newkey rsa:2048 -keyout "$tmp/key.pem" -out "$tmp/cert.pem" \
            -days 3650 -nodes -config "$tmp/req.cnf" >/dev/null 2>&1 \
       && { openssl pkcs12 -export -legacy -inkey "$tmp/key.pem" -in "$tmp/cert.pem" \
                -out "$tmp/id.p12" -passout pass:"$pw" -name "$CUA_LOCAL_SIGN_CN" >/dev/null 2>&1 \
            || openssl pkcs12 -export -inkey "$tmp/key.pem" -in "$tmp/cert.pem" \
                -out "$tmp/id.p12" -passout pass:"$pw" -name "$CUA_LOCAL_SIGN_CN" >/dev/null 2>&1; } \
       && security import "$tmp/id.p12" -k "$kc" -P "$pw" \
            -T /usr/bin/codesign >/dev/null 2>&1; then
        identity="$(security find-identity -p codesigning "$kc" 2>/dev/null \
            | awk -v cn="$CUA_LOCAL_SIGN_CN" 'index($0, "\"" cn "\"") { print $2; exit }')"
        rm -rf "$tmp"
        if [ -n "$identity" ]; then
            printf '%s' "$identity"
            return
        fi
        printf -- '-'
        return
    fi
    rm -rf "$tmp"
    printf -- '-'
}

# Keychain-backed codesign can wait forever for a GUI authorization prompt.
codesign_bounded() {
    local timeout_seconds="$1"
    shift
    local kc=""
    if [ -n "${CUA_DRIVER_LOCAL_SIGNING_KEYCHAIN:-}" ]; then
        kc="$CUA_DRIVER_LOCAL_SIGNING_KEYCHAIN"
    elif [ -f "$HOME/Library/Keychains/cua-driver-signing.keychain-db" ]; then
        kc="$HOME/Library/Keychains/cua-driver-signing.keychain-db"
    fi
    if [ -n "$kc" ]; then
        set -- --keychain "$kc" "$@"
    fi
    if command -v gtimeout >/dev/null 2>&1; then
        gtimeout "$timeout_seconds" codesign "$@"
    elif command -v perl >/dev/null 2>&1; then
        perl -e 'alarm shift; exec @ARGV' "$timeout_seconds" codesign "$@"
    else
        codesign "$@"
    fi
}

clean_partial_bundle_signature() {
    local app="$1"
    rm -rf "$app/Contents/_CodeSignature"
    find "$app" -type f -name '*.cstemp' -delete
}

designated_requirement() {
    codesign -d -r- "$1" 2>&1 \
        | sed -n -e 's/^designated => //p' -e 's/^# designated => //p'
}

local_app_bundle_value() {
    local app="$1"
    local key="$2"
    /usr/libexec/PlistBuddy -c "Print :$key" \
        "$app/Contents/Info.plist" 2>/dev/null
}

# Local builds can use either the dedicated development certificate or an
# ad-hoc signature, so there is no global signer pin. Still require a valid
# sealed bundle, the exact bundle/executable tuple, and a code-signing
# requirement that independently binds the expected identifier. This prevents
# a mutable Info.plist alone from authorizing deletion or process cleanup.
verify_local_app_identity() {
    local app="$1"
    local expected_bundle_id="$2"
    local expected_executable="$3"
    local actual_bundle_id actual_executable requirement

    [ -d "$app" ] && [ ! -L "$app" ] || return 1
    [ -f "$app/Contents/Info.plist" ] \
        && [ ! -L "$app/Contents/Info.plist" ] || return 1
    actual_bundle_id="$(local_app_bundle_value "$app" CFBundleIdentifier || true)"
    actual_executable="$(local_app_bundle_value "$app" CFBundleExecutable || true)"
    [ "$actual_bundle_id" = "$expected_bundle_id" ] || return 1
    [ "$actual_executable" = "$expected_executable" ] || return 1
    [ -f "$app/Contents/MacOS/$expected_executable" ] \
        && [ ! -L "$app/Contents/MacOS/$expected_executable" ] \
        && [ -x "$app/Contents/MacOS/$expected_executable" ] || return 1
    codesign --verify --deep --strict "$app" >/dev/null 2>&1 || return 1
    codesign --verify --deep --strict \
        -R "=identifier \"$expected_bundle_id\"" "$app" >/dev/null 2>&1 \
        || return 1
    requirement="$(designated_requirement "$app" || true)"
    [ "$(classify_designated_requirement "$requirement")" != "unknown" ]
}

classify_designated_requirement() {
    case "$1" in
        *"certificate leaf"*) printf '%s' "certificate-backed" ;;
        *cdhash*) printf '%s' "ad-hoc" ;;
        *) printf '%s' "unknown" ;;
    esac
}

# An ad-hoc signature's designated requirement is its cdhash. Replacing the
# bundle with a different ad-hoc build leaves TCC rows carrying the old csreq;
# toggling the visible System Settings entry does not reliably rewrite it.
ad_hoc_requirement_changed() {
    local previous_requirement="$1"
    local installed_requirement="$2"

    [ -n "$previous_requirement" ] \
        && [ -n "$installed_requirement" ] \
        && [ "$previous_requirement" != "$installed_requirement" ] \
        && [ "$(classify_designated_requirement "$previous_requirement")" = "ad-hoc" ] \
        && [ "$(classify_designated_requirement "$installed_requirement")" = "ad-hoc" ]
}

# Reset only the two TCC services used by Cua Driver Local, and only when an
# actual ad-hoc cdhash transition was observed. The caller must register the
# newly installed bundle with LaunchServices before invoking this function.
reset_local_tcc_after_ad_hoc_change() {
    local previous_requirement="$1"
    local installed_requirement="$2"
    local bundle_id="com.meta.musecode.cua.driver.local"
    local service failed_services=""

    ad_hoc_requirement_changed "$previous_requirement" "$installed_requirement" || return 0

    if ! command -v tccutil >/dev/null 2>&1; then
        echo "${RED}Error: tccutil is required to clear stale local-app permission rows after an ad-hoc cdhash change.${NORMAL}" >&2
        return 1
    fi

    for service in Accessibility ScreenCapture; do
        if ! tccutil reset "$service" "$bundle_id" >/dev/null 2>&1; then
            failed_services="$failed_services $service"
        fi
    done
    if [ -n "$failed_services" ]; then
        echo "${RED}Error: could not reset these TCC services for $bundle_id:$failed_services.${NORMAL}" >&2
        echo "The replacement will be rolled back. After resolving tccutil, retry:" >&2
        echo "  tccutil reset Accessibility $bundle_id" >&2
        echo "  tccutil reset ScreenCapture $bundle_id" >&2
        return 1
    fi

    echo "${YELLOW}The ad-hoc cdhash changed; cleared stale Accessibility and Screen Recording rows for $bundle_id.${NORMAL}" >&2
    echo "Re-grant them to the new app with: cua-driver-local permissions grant" >&2
}

legacy_local_app_bundle_id() {
    local_app_bundle_value "$1" CFBundleIdentifier
}

register_local_app() {
    local app="$1"
    local lsregister="/System/Library/Frameworks/CoreServices.framework/Versions/A/Frameworks/LaunchServices.framework/Versions/A/Support/lsregister"
    [ -x "$lsregister" ] && "$lsregister" -f "$app" >/dev/null 2>&1
}

register_legacy_local_app() {
    register_local_app "$1"
}

# Restore only a replacement that this installer has authenticated. The prior
# app is re-registered before failure is reported to the caller.
restore_local_app_backup() {
    local app="$1"
    local backup="$2"
    local expected_bundle_id="$3"
    local expected_executable="$4"

    if [ -e "$app" ] || [ -L "$app" ]; then
        if ! verify_local_app_identity "$app" "$expected_bundle_id" "$expected_executable"; then
            echo "${RED:-}Error: refusing to remove unauthenticated rollback candidate at $app.${NORMAL:-}" >&2
            return 1
        fi
        rm -rf -- "$app" || return 1
    fi
    if [ -d "$backup" ] && [ ! -L "$backup" ]; then
        if ! verify_local_app_identity "$backup" "$expected_bundle_id" "$expected_executable"; then
            echo "${RED:-}Error: refusing to restore unauthenticated app backup at $backup.${NORMAL:-}" >&2
            return 1
        fi
        mv "$backup" "$app" || return 1
        if ! register_local_app "$app"; then
            echo "${RED:-}Error: restored $app but could not re-register it with LaunchServices.${NORMAL:-}" >&2
            return 1
        fi
    fi
}

remove_authenticated_local_app_backup() {
    local backup="$1"
    local expected_bundle_id="$2"
    local expected_executable="$3"

    [ -e "$backup" ] || [ -L "$backup" ] || return 0
    if ! verify_local_app_identity "$backup" "$expected_bundle_id" "$expected_executable"; then
        echo "${YELLOW:-}warning: preserving unauthenticated local install backup at $backup.${NORMAL:-}" >&2
        return 1
    fi
    rm -rf -- "$backup"
}

remove_legacy_local_app_path() {
    local app="$1"
    if [ -w "$(dirname "$app")" ]; then
        rm -rf -- "$app"
    else
        sudo rm -rf -- "$app"
    fi
}

# Remove only the retired local-development bundle. When TCC cleanup is
# requested, keep the bundle available and registered until every scoped reset
# succeeds so a failed reset remains retryable.
cleanup_legacy_local_app() {
    local app="$1"
    local reset_tcc="${2:-1}"
    local expected_bundle_id="com.trycua.driver.local"
    local actual_bundle_id service failed_services=""

    [ "${OS:-}" = "Darwin" ] || return 0
    [ -e "$app" ] || [ -L "$app" ] || return 0
    if [ -L "$app" ] || [ ! -d "$app" ]; then
        echo "${RED:-}Error: refusing to remove unsafe legacy local app path $app.${NORMAL:-}" >&2
        return 1
    fi
    actual_bundle_id="$(legacy_local_app_bundle_id "$app" || true)"
    if [ "$actual_bundle_id" != "$expected_bundle_id" ]; then
        echo "${RED:-}Error: preserving $app because its bundle ID is ${actual_bundle_id:-unreadable}, not $expected_bundle_id.${NORMAL:-}" >&2
        return 1
    fi
    if ! verify_local_app_identity "$app" "$expected_bundle_id" "cua-driver-local"; then
        echo "${RED:-}Error: preserving $app because its executable or code-signing identity could not be authenticated.${NORMAL:-}" >&2
        return 1
    fi

    if [ "$reset_tcc" = "1" ]; then
        if ! command -v tccutil >/dev/null 2>&1; then
            echo "${RED:-}Error: tccutil is required to clear the retired local-app permission rows.${NORMAL:-}" >&2
            return 1
        fi
        if ! register_legacy_local_app "$app"; then
            echo "${RED:-}Error: could not register $app before resetting its TCC rows; the app was preserved.${NORMAL:-}" >&2
            return 1
        fi
        for service in Accessibility ScreenCapture AppleEvents; do
            if ! tccutil reset "$service" "$expected_bundle_id" >/dev/null 2>&1; then
                failed_services="$failed_services $service"
            fi
        done
        if [ -n "$failed_services" ]; then
            echo "${RED:-}Error: could not reset these TCC services for $expected_bundle_id:$failed_services; the legacy app was preserved.${NORMAL:-}" >&2
            return 1
        fi
    fi

    if ! remove_legacy_local_app_path "$app"; then
        echo "${RED:-}Error: could not remove retired local app $app.${NORMAL:-}" >&2
        return 1
    fi
    echo "${YELLOW:-}Removed retired local app $app (${expected_bundle_id}).${NORMAL:-}" >&2
}

# Signs a staged local app without touching the live installation. Strict mode
# refuses the ad-hoc path; non-strict mode keeps it available for casual local
# development but makes the resulting TCC reset impossible to miss.
sign_staged_local_app() {
    local app_stage="$1"
    local app_dest="$2"
    local sign_id requirement signing_class
    sign_id="$(ensure_local_signing_identity)"

    if [ "$sign_id" != "-" ] \
       && codesign_bounded 20 --force --deep --sign "$sign_id" "$app_stage" 2>/dev/null; then
        requirement="$(designated_requirement "$app_stage")"
        signing_class="$(classify_designated_requirement "$requirement")"
        if [ "$signing_class" = "certificate-backed" ]; then
            echo "${GREEN}signed staged app with a stable local identity — TCC grants survive future install-local rebuilds${NORMAL}"
            return 0
        fi
        echo "${YELLOW}warning: the requested stable identity produced a non-certificate designated requirement${NORMAL}" >&2
    fi

    if [ "${CUA_DRIVER_REQUIRE_STABLE_SIGNING:-0}" = "1" ]; then
        clean_partial_bundle_signature "$app_stage"
        echo "${RED}Error: stable macOS signing is required, but no usable certificate-backed identity was available.${NORMAL}" >&2
        echo "The live installation was not changed." >&2
        print_local_signing_bootstrap
        return 1
    fi

    if [ -d "$app_dest" ]; then
        requirement="$(designated_requirement "$app_dest")"
        if [ "$(classify_designated_requirement "$requirement")" = "certificate-backed" ]; then
            clean_partial_bundle_signature "$app_stage"
            echo "${RED}Error: stable signing failed; preserving the existing certificate-signed $app_dest and its TCC grants.${NORMAL}" >&2
            print_local_signing_bootstrap
            return 1
        fi
    fi

    clean_partial_bundle_signature "$app_stage"
    if ! codesign_bounded 20 --force --deep --sign - "$app_stage" 2>/dev/null; then
        clean_partial_bundle_signature "$app_stage"
        echo "${RED}Error: codesign of staged MuseCodeCuaDriverLocal.app failed; live installation was not changed.${NORMAL}" >&2
        return 1
    fi
    requirement="$(designated_requirement "$app_stage")"
    if [ "$(classify_designated_requirement "$requirement")" != "ad-hoc" ]; then
        echo "${RED}Error: could not verify the staged app's ad-hoc designated requirement; live installation was not changed.${NORMAL}" >&2
        return 1
    fi
    echo "${YELLOW}WARNING: MuseCodeCuaDriverLocal.app was signed ad-hoc (designated requirement uses cdhash).${NORMAL}" >&2
    echo "${YELLOW}Accessibility and Screen Recording grants WILL become invalid on the next rebuild.${NORMAL}" >&2
    print_local_signing_bootstrap
}
