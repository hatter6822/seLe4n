#!/usr/bin/env bash
# AK4-G: End-to-end ABI round-trip integration test.
#
# Runs `lake exe abi_roundtrip_suite`, which simulates the Rust-side
# `sele4n-abi` encoder (including IPC-buffer overflow merge) and verifies
# that every 5-arg syscall decodes successfully via the Lean kernel's
# `decodeSyscallArgsFromState`.
#
# Hooked into `test_full.sh`. Added in v0.29.8 (WS-AK / Phase AK4).

set -euo pipefail

# AN11-E.3 (TST-M03): source the shared one-shot helpers (log_info, etc.).
# The previous `|| true` swallow silently hid a missing _common.sh; the
# loud-failure source below ensures the helper file is always present.
# shellcheck disable=SC1091
source "$(dirname "$0")/_common.sh"

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

# Ensure the Lean toolchain is available.
if [ -f "$HOME/.elan/env" ]; then
    # shellcheck disable=SC1091
    source "$HOME/.elan/env"
fi

log_info "test_abi_roundtrip" "Building abi_roundtrip_suite..."
lake build abi_roundtrip_suite >/dev/null

# AN11-B (H-21): wrap the suite in a timeout so a runaway proof / scenario
# cannot hang CI past its job budget.
LEAN_TEST_TIMEOUT_MINS="${LEAN_TEST_TIMEOUT_MINS:-30}"
if command -v timeout >/dev/null 2>&1; then
    TIMEOUT_BIN="timeout"
elif command -v gtimeout >/dev/null 2>&1; then
    TIMEOUT_BIN="gtimeout"
else
    TIMEOUT_BIN=""
fi

log_info "test_abi_roundtrip" "Running AbiRoundtripSuite (timeout: ${LEAN_TEST_TIMEOUT_MINS}m)..."
# `time_command` (from _common.sh) wraps the run with wall-clock timing
# and prints a uniform success / failure line on completion.
if [[ -n "${TIMEOUT_BIN}" ]]; then
    if ! time_command "test_abi_roundtrip" \
            "${TIMEOUT_BIN}" "${LEAN_TEST_TIMEOUT_MINS}m" lake exe abi_roundtrip_suite; then
        rc=$?
        if [[ "${rc}" -eq 124 ]]; then
            log_error "test_abi_roundtrip" \
                "timed out after ${LEAN_TEST_TIMEOUT_MINS}m — set LEAN_TEST_TIMEOUT_MINS=<minutes> to extend"
        fi
        exit "${rc}"
    fi
else
    log_warn "test_abi_roundtrip" "timeout(1) not found; running unguarded"
    time_command "test_abi_roundtrip" lake exe abi_roundtrip_suite
fi

log_info "test_abi_roundtrip" "PASS"
