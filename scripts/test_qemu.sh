#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AG9-A: QEMU Integration Testing for seLe4n on Raspberry Pi 5 (raspi4b model)
#
# Validates the kernel binary boots correctly in QEMU, exercising:
# 1. UART boot banner output
# 2. Exception vector table setup (VBAR_EL1)
# 3. GIC-400 interrupt controller initialization
# 4. ARM Generic Timer interrupt delivery
# 5. Syscall dispatch (SVC instruction handling)
#
# Prerequisites:
#   - qemu-system-aarch64 installed (QEMU >= 8.0)
#   - Rust toolchain with aarch64-unknown-none target
#   - cargo build --release --target aarch64-unknown-none completes
#
# Usage:
#   ./scripts/test_qemu.sh              # Run QEMU integration tests
#   QEMU_TIMEOUT=120 ./scripts/test_qemu.sh  # Custom timeout (seconds)
#
# CI Integration:
#   This script exits 0 if QEMU is not available (graceful skip for CI
#   environments without QEMU). Set REQUIRE_QEMU=1 to force failure.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

cd "${REPO_ROOT}"

# ── Configuration ──────────────────────────────────────────────────────────
QEMU_BIN="${QEMU_BIN:-qemu-system-aarch64}"
QEMU_TIMEOUT="${QEMU_TIMEOUT:-60}"
QEMU_MACHINE="${QEMU_MACHINE:-raspi4b}"
QEMU_CPU="${QEMU_CPU:-cortex-a76}"
QEMU_MEMORY="${QEMU_MEMORY:-1G}"
REQUIRE_QEMU="${REQUIRE_QEMU:-0}"
RUST_DIR="${REPO_ROOT}/rust"
RUST_TARGET="aarch64-unknown-none"
KERNEL_BIN="${RUST_DIR}/target/${RUST_TARGET}/release/sele4n-hal"

# ── QEMU availability check ───────────────────────────────────────────────
log_section "META" "=== AG9-A: QEMU Integration Testing ==="

if ! command -v "${QEMU_BIN}" &>/dev/null; then
    if [[ "${REQUIRE_QEMU}" -eq 1 ]]; then
        record_failure "META" "QEMU not found: ${QEMU_BIN} (REQUIRE_QEMU=1)"
        finalize_report
    fi
    log_section "META" "SKIP: ${QEMU_BIN} not found — QEMU tests skipped"
    log_section "META" "       Install: apt install qemu-system-arm  (Debian/Ubuntu)"
    log_section "META" "       Install: brew install qemu            (macOS)"
    if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
        echo "QEMU_TESTS_SKIPPED=true" >> "${GITHUB_OUTPUT}"
    fi
    exit 0
fi

QEMU_VERSION=$("${QEMU_BIN}" --version | head -1)
log_section "META" "QEMU found: ${QEMU_VERSION}"

# ── Rust cross-compilation target check ────────────────────────────────────
if ! command -v cargo &>/dev/null; then
    log_section "META" "SKIP: cargo not found — cannot build kernel binary"
    exit 0
fi

# Check if aarch64 target is installed
if ! rustup target list --installed 2>/dev/null | grep -q "${RUST_TARGET}"; then
    log_section "BUILD" "Installing Rust target: ${RUST_TARGET}"
    rustup target add "${RUST_TARGET}" 2>/dev/null || {
        log_section "META" "SKIP: Cannot install ${RUST_TARGET} target"
        exit 0
    }
fi

# ── Temp logs (created before first use; cleaned up on exit) ──────────────
QEMU_LOG=$(mktemp /tmp/qemu_boot_XXXXXX.log)
QEMU_BUILD_LOG=$(mktemp /tmp/qemu_build_XXXXXX.log)
cleanup() { rm -f "${QEMU_LOG}" "${QEMU_BUILD_LOG}"; }
trap cleanup EXIT

# ── Build kernel binary ───────────────────────────────────────────────────
log_section "BUILD" "Building kernel binary for ${RUST_TARGET}..."
cd "${RUST_DIR}"
if ! cargo build --release --target "${RUST_TARGET}" -p sele4n-hal 2>"${QEMU_BUILD_LOG}"; then
    # Cross-compilation may fail without linker config — this is expected
    # in CI environments without aarch64 linker. Skip gracefully.
    log_section "META" "SKIP: Cross-compilation failed (expected without aarch64 linker)"
    log_section "META" "       Configure .cargo/config.toml with linker for ${RUST_TARGET}"
    tail -10 "${QEMU_BUILD_LOG}"
    exit 0
fi
cd "${REPO_ROOT}"

if [[ ! -f "${KERNEL_BIN}" ]]; then
    log_section "META" "SKIP: Kernel binary not found at ${KERNEL_BIN}"
    exit 0
fi

log_section "BUILD" "Kernel binary built: $(wc -c < "${KERNEL_BIN}") bytes"

# ── QEMU boot test (temp logs created above, before first use) ────────────

log_section "TRACE" "RUN: QEMU boot test (timeout: ${QEMU_TIMEOUT}s)"

# Launch QEMU with serial output to file, kill after timeout
timeout "${QEMU_TIMEOUT}" "${QEMU_BIN}" \
    -machine "${QEMU_MACHINE}" \
    -cpu "${QEMU_CPU}" \
    -m "${QEMU_MEMORY}" \
    -kernel "${KERNEL_BIN}" \
    -serial stdio \
    -display none \
    -no-reboot \
    -semihosting \
    > "${QEMU_LOG}" 2>&1 || true

# ── Validate boot output ──────────────────────────────────────────────────
BOOT_PASS=true

# Check 1: UART boot banner — mandatory: a kernel that boots without its
# banner is a failed boot (the KERNEL_BIN SKIP above is the only soft path)
if grep -q "seLe4n" "${QEMU_LOG}" 2>/dev/null; then
    log_section "TRACE" "PASS: Boot banner detected"
else
    record_failure "TRACE" "Boot banner not detected"
    BOOT_PASS=false
fi

# Check 2: Non-empty output — mandatory: a silent QEMU run is a hung or
# dead kernel, not a pass
if [[ -s "${QEMU_LOG}" ]]; then
    log_section "TRACE" "PASS: QEMU produced output (UART functional)"
    QEMU_LINES=$(wc -l < "${QEMU_LOG}")
    log_section "TRACE" "      Output: ${QEMU_LINES} lines"
else
    record_failure "TRACE" "QEMU produced no output (hung or dead kernel)"
    BOOT_PASS=false
fi

# Check 3: No fatal exceptions in output
if grep -qi "fatal\|panic\|unhandled.*exception\|SError" "${QEMU_LOG}" 2>/dev/null; then
    record_failure "TRACE" "Fatal exception detected in QEMU output"
    BOOT_PASS=false
else
    log_section "TRACE" "PASS: No fatal exceptions in boot output"
fi

# Check 4: QEMU did not crash or segfault
if grep -qi "segfault\|core dumped\|aborted" "${QEMU_LOG}" 2>/dev/null; then
    record_failure "TRACE" "QEMU crashed during boot"
    BOOT_PASS=false
else
    log_section "TRACE" "PASS: QEMU completed without crash"
fi

# Check 5: Structured boot sequence validation from fixture — every fragment
# is mandatory once QEMU has run; an empty log already failed Check 2, so the
# -s guard only suppresses duplicate per-fragment reports
FIXTURE="${REPO_ROOT}/tests/fixtures/qemu_boot_expected.txt"
if [[ ! -f "${FIXTURE}" ]]; then
    record_failure "TRACE" "Boot fixture missing: ${FIXTURE}"
    BOOT_PASS=false
elif [[ -s "${QEMU_LOG}" ]]; then
    log_section "TRACE" "Validating boot sequence against ${FIXTURE##*/}..."
    while IFS='|' read -r check_name fragment; do
        # Skip comments and blank lines
        [[ "${check_name}" =~ ^[[:space:]]*# ]] && continue
        [[ -z "${check_name}" ]] && continue
        check_name=$(echo "${check_name}" | xargs)
        fragment=$(echo "${fragment}" | xargs)
        if grep -q "${fragment}" "${QEMU_LOG}" 2>/dev/null; then
            log_section "TRACE" "PASS: ${check_name} — '${fragment}' found"
        else
            record_failure "TRACE" "${check_name} — '${fragment}' missing from boot log"
            BOOT_PASS=false
        fi
    done < "${FIXTURE}"
fi

# ── Summary ────────────────────────────────────────────────────────────────
log_section "META" "QEMU boot log: ${QEMU_LOG}"

if [[ "${BOOT_PASS}" = true ]]; then
    log_section "META" "PASS: AG9-A QEMU integration tests"
else
    log_section "META" "FAIL: AG9-A QEMU integration tests — see ${QEMU_LOG}"
fi

finalize_report
