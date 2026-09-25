#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AG9-A: QEMU Integration Testing for seLe4n on Raspberry Pi 5
#
# Validates the kernel image boots correctly in QEMU, exercising:
# 1. UART boot banner output
# 2. Exception vector table setup (VBAR_EL1)
# 3. GIC-400 interrupt controller initialization
# 4. ARM Generic Timer interrupt delivery
# 5. Syscall dispatch (SVC instruction handling)
#
# Prerequisites:
#   - qemu-system-aarch64 installed (QEMU >= 8.0)
#   - Rust toolchain with aarch64-unknown-none-softfloat target
#   - cargo build --release --target aarch64-unknown-none-softfloat
#     --features kernel_image --bin sele4n-kernel completes (WS-BP BP5.1's
#     bare-metal image; the Rust half boots on its own, and KERNEL_BIN may
#     name the archive lane's Lean-linked image instead)
#   - a QEMU machine that models the BCM2712 -- which QEMU does not ship
#     (the v0.36.2 audit).  The image programs the BCM2712's UART10, GIC-400
#     and SoC-bus window (`SeLe4n/Platform/RPi5/Board.lean`), so on `raspi4b`
#     (a BCM2711) or `virt` its first console write faults and its device-tree
#     check refuses the board.  QEMU_MACHINE is therefore unset by default and
#     the lane SKIPs after building the image; WS-BP BP8.1 owns the machine.
#
# Usage:
#   ./scripts/test_qemu.sh              # Build the image; SKIP (no BCM2712 machine)
#   QEMU_MACHINE=raspi4b ./scripts/test_qemu.sh   # Run it on a named machine anyway
#   QEMU_TIMEOUT=120 ./scripts/test_qemu.sh  # Custom timeout (seconds)
#
# CI Integration:
#   A gate that cannot run certifies nothing, so an unavailable prerequisite
#   (no QEMU, no cargo, no cross target, no kernel image, no machine) exits
#   SELE4N_SKIP_EXIT (77) — NOT 0.  Callers must invoke this through
#   `run_gate_check`, which records the gate as NOT RUN; a plain `run_check`,
#   or a direct call under `set -e`, will treat 77 as a failure.  Set
#   REQUIRE_QEMU=1 to fail outright instead of skipping.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

cd "${REPO_ROOT}"

# ── Configuration ──────────────────────────────────────────────────────────
QEMU_BIN="${QEMU_BIN:-qemu-system-aarch64}"
QEMU_TIMEOUT="${QEMU_TIMEOUT:-60}"
QEMU_MACHINE="${QEMU_MACHINE:-}"
QEMU_CPU="${QEMU_CPU:-cortex-a76}"
QEMU_MEMORY="${QEMU_MEMORY:-1G}"
REQUIRE_QEMU="${REQUIRE_QEMU:-0}"
RUST_DIR="${REPO_ROOT}/rust"
RUST_TARGET="aarch64-unknown-none-softfloat"
# WS-BP BP5.1: the bare-metal image is the `sele4n-kernel` binary behind the
# `kernel_image` feature; `sele4n-hal` itself is a library and builds no file
# QEMU could boot.  A caller may name another image (the archive lane's
# Lean-linked one) in KERNEL_BIN, in which case nothing is built here.
KERNEL_BIN_DEFAULT="${RUST_DIR}/target/${RUST_TARGET}/release/sele4n-kernel"
KERNEL_BIN="${KERNEL_BIN:-${KERNEL_BIN_DEFAULT}}"

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
    exit "${SELE4N_SKIP_EXIT:-77}"
fi

QEMU_VERSION=$("${QEMU_BIN}" --version | head -1)
log_section "META" "QEMU found: ${QEMU_VERSION}"

# ── Rust cross-compilation target check ────────────────────────────────────
if ! command -v cargo &>/dev/null; then
    log_section "META" "SKIP: cargo not found — cannot build kernel binary"
    exit "${SELE4N_SKIP_EXIT:-77}"
fi

# Check if aarch64 target is installed
if ! rustup target list --installed 2>/dev/null | grep -q "${RUST_TARGET}"; then
    log_section "BUILD" "Installing Rust target: ${RUST_TARGET}"
    rustup target add "${RUST_TARGET}" 2>/dev/null || {
        log_section "META" "SKIP: Cannot install ${RUST_TARGET} target"
        exit "${SELE4N_SKIP_EXIT:-77}"
    }
fi

# ── Temp logs (created before first use; cleaned up on exit) ──────────────
QEMU_LOG=$(mktemp /tmp/qemu_boot_XXXXXX.log)
QEMU_BUILD_LOG=$(mktemp /tmp/qemu_build_XXXXXX.log)
cleanup() { rm -f "${QEMU_LOG}" "${QEMU_BUILD_LOG}"; }
trap cleanup EXIT

# ── Build the kernel image ────────────────────────────────────────────────
if [[ "${KERNEL_BIN}" == "${KERNEL_BIN_DEFAULT}" ]]; then
    log_section "BUILD" "Building the kernel image (sele4n-kernel) for ${RUST_TARGET}..."
    cd "${RUST_DIR}"
    if ! cargo build --release --target "${RUST_TARGET}" -p sele4n-hal \
            --features kernel_image --bin sele4n-kernel 2>"${QEMU_BUILD_LOG}"; then
        # Cross-compilation may fail without linker config — this is expected
        # in CI environments without aarch64 linker. Skip gracefully.
        log_section "META" "SKIP: Cross-compilation failed (expected without aarch64 linker)"
        log_section "META" "       Configure .cargo/config.toml with linker for ${RUST_TARGET}"
        tail -10 "${QEMU_BUILD_LOG}"
        exit "${SELE4N_SKIP_EXIT:-77}"
    fi
    cd "${REPO_ROOT}"
else
    log_section "BUILD" "Using the kernel image named by KERNEL_BIN: ${KERNEL_BIN}"
fi

if [[ ! -f "${KERNEL_BIN}" ]]; then
    log_section "META" "SKIP: Kernel image not found at ${KERNEL_BIN}"
    exit "${SELE4N_SKIP_EXIT:-77}"
fi

log_section "BUILD" "Kernel image: $(wc -c < "${KERNEL_BIN}") bytes"

# ── A machine the image can boot on ───────────────────────────────────────
# The image is built for the BCM2712 and QEMU models no such machine; running
# it on `raspi4b` or `virt` faults at the first console write and refuses the
# board at the device-tree check, so without an explicit machine the lane has
# nothing it can certify (WS-BP BP8.1 owns the machine question).
if [[ -z "${QEMU_MACHINE}" ]]; then
    log_section "META" "SKIP: no QEMU machine models the BCM2712 the image is built for (set QEMU_MACHINE to run it on one anyway)"
    exit "${SELE4N_SKIP_EXIT:-77}"
fi

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
