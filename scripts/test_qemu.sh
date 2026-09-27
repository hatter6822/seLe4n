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
#     --features kernel_image,board_qemu_virt --bin sele4n-kernel completes
#     (WS-BP BP8.1: the image built for QEMU's `virt` machine -- QEMU models no
#     BCM2712, so the Raspberry Pi 5 image meets no device under it; the Rust
#     half boots on its own, and KERNEL_BIN may name another image instead)
#
# Usage:
#   ./scripts/test_qemu.sh              # Build the virt image; boot it at EL1 and at EL2
#   KERNEL_BIN=… QEMU_MACHINE=… ./scripts/test_qemu.sh   # Boot a named image on a named machine
#   QEMU_TIMEOUT=30 ./scripts/test_qemu.sh  # Custom per-boot timeout (seconds)
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
QEMU_TIMEOUT="${QEMU_TIMEOUT:-10}"
QEMU_MACHINE="${QEMU_MACHINE:-}"
QEMU_CPU="${QEMU_CPU:-cortex-a76}"
QEMU_MEMORY="${QEMU_MEMORY:-1G}"
REQUIRE_QEMU="${REQUIRE_QEMU:-0}"
RUST_DIR="${REPO_ROOT}/rust"
RUST_TARGET="aarch64-unknown-none-softfloat"
# WS-BP BP5.1: the bare-metal image is the `sele4n-kernel` binary behind the
# `kernel_image` feature; `sele4n-hal` itself is a library and builds no file
# QEMU could boot.  WS-BP BP8.1: built for `virt` (`board_qemu_virt`).  A caller may name another image (the archive lane's
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
            --features kernel_image,board_qemu_virt --bin sele4n-kernel 2>"${QEMU_BUILD_LOG}"; then
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

# ── WS-BP BP8.1: QEMU's `virt`, at both entry levels ───────────────────────
# QEMU models no BCM2712, so the lane boots the image built for `virt`
# (`board_qemu_virt`, rust/sele4n-hal/src/board.rs): `virt`'s device map and
# RAM base, the same kernel otherwise.  QEMU passes the device tree in x0 only
# to an image carrying the arm64 Image header, so it is handed the raw binary
# cut from the ELF, never the ELF.  It runs twice — at QEMU's default EL1
# entry, and with `virtualization=on`, where QEMU enters at EL2 as the
# Raspberry Pi firmware does, so the drop to EL1 and the SMC conduit execute
# before the board is the first thing to run them.  An image named by
# KERNEL_BIN runs on the machine named by QEMU_MACHINE instead, once.
OBJCOPY=$(python3 -c 'import sys; sys.path.insert(0, sys.argv[1]); from check_fp_simd_free_objects import rust_llvm_tool; print(rust_llvm_tool("llvm-objcopy"))' "${SCRIPT_DIR}")
QEMU_IMAGE=$(mktemp /tmp/qemu_image_XXXXXX.img)
trap 'cleanup; rm -f "${QEMU_IMAGE}"' EXIT
if ! "${OBJCOPY}" -O binary "${KERNEL_BIN}" "${QEMU_IMAGE}"; then
    record_failure "BUILD" "${OBJCOPY} could not cut a raw image from ${KERNEL_BIN}"
    finalize_report
fi

FIXTURE="${REPO_ROOT}/tests/fixtures/qemu_boot_expected.txt"
BOOT_PASS=true

# boot_once LABEL MACHINE [FRAGMENT...]: boot the image on MACHINE and require
# the fixture's fragments IN ORDER, then each extra FRAGMENT anywhere.
boot_once() {
    local label="$1" machine="$2"
    shift 2
    log_section "TRACE" "RUN: ${label} — -machine ${machine} (timeout: ${QEMU_TIMEOUT}s)"
    : > "${QEMU_LOG}"
    timeout "${QEMU_TIMEOUT}" "${QEMU_BIN}" \
        -machine "${machine}" \
        -cpu "${QEMU_CPU}" \
        -smp 1 \
        -m "${QEMU_MEMORY}" \
        -kernel "${QEMU_IMAGE}" \
        -serial "file:${QEMU_LOG}" \
        -monitor none \
        -display none \
        -no-reboot || true
    tr -d '\r' < "${QEMU_LOG}" > "${QEMU_LOG}.txt"
    mv "${QEMU_LOG}.txt" "${QEMU_LOG}"
    if [[ ! -s "${QEMU_LOG}" ]]; then
        record_failure "TRACE" "${label}: QEMU produced no output (hung or dead kernel)"
        BOOT_PASS=false
        return
    fi
    if grep -qi "fatal\|panic\|unhandled.*exception\|SError" "${QEMU_LOG}"; then
        record_failure "TRACE" "${label}: fatal exception in boot output: $(grep -i -m1 'fatal\|panic\|unhandled.*exception\|SError' "${QEMU_LOG}")"
        BOOT_PASS=false
    fi
    # The fixture's fragments in the order the fixture lists them: each must
    # occur on a line after the previous fragment's line.
    local after=0 check_name fragment line
    while IFS='|' read -r check_name fragment; do
        [[ "${check_name}" =~ ^[[:space:]]*# ]] && continue
        [[ -z "${check_name// /}" ]] && continue
        check_name=$(echo "${check_name}" | xargs)
        fragment=$(echo "${fragment}" | xargs)
        # No match is grep's status 1, which `set -e -o pipefail` would turn
        # into a silent exit; it is a missing fragment, and is reported.
        line=$(tail -n "+$((after + 1))" "${QEMU_LOG}" | grep -n -F -m1 -- "${fragment}" | cut -d: -f1) || line=""
        if [[ -n "${line}" ]]; then
            after=$((after + line))
            log_section "TRACE" "PASS: ${label}: ${check_name} — '${fragment}' at line ${after}"
        else
            record_failure "TRACE" "${label}: ${check_name} — '${fragment}' missing after line ${after}"
            BOOT_PASS=false
        fi
    done < "${FIXTURE}"
    for fragment in "$@"; do
        if grep -q -F -- "${fragment}" "${QEMU_LOG}"; then
            log_section "TRACE" "PASS: ${label}: '${fragment}'"
        else
            record_failure "TRACE" "${label}: '${fragment}' missing from boot log"
            BOOT_PASS=false
        fi
    done
    log_section "TRACE" "${label}: $(wc -l < "${QEMU_LOG}") lines of boot output"
}

if [[ ! -f "${FIXTURE}" ]]; then
    record_failure "TRACE" "Boot fixture missing: ${FIXTURE}"
    finalize_report
fi
# The fixture's `.sha256` companion (WS-BP BP8.1: it landed with the boot path
# this lane now runs): a fixture edit must be paired with a hash refresh in the
# same commit, as Tier 2 requires of every `.expected` fixture.  Tier 2's sweep
# reads `*.expected.sha256` only, so this lane checks its own.
if ! (cd "$(dirname "${FIXTURE}")" && sha256sum -c "$(basename "${FIXTURE}").sha256" > /dev/null 2>&1); then
    record_failure "TRACE" "${FIXTURE##*/} does not match its .sha256 companion (cd tests/fixtures && sha256sum ${FIXTURE##*/} > ${FIXTURE##*/}.sha256)"
    finalize_report
fi

if [[ -n "${QEMU_MACHINE}" ]]; then
    boot_once "the image on ${QEMU_MACHINE}" "${QEMU_MACHINE}"
else
    boot_once "virt, EL1 entry" "virt,gic-version=2" \
        "booting on QEMU virt" "Entered at EL1, running at EL1" "PSCI conduit: Hvc"
    boot_once "virt, EL2 entry" "virt,gic-version=2,virtualization=on" \
        "booting on QEMU virt" "Entered at EL2, running at EL1" "PSCI conduit: Smc"
fi

# ── Summary ────────────────────────────────────────────────────────────────
if [[ "${BOOT_PASS}" = true ]]; then
    log_section "META" "PASS: QEMU boot"
else
    log_section "META" "FAIL: QEMU boot"
fi

finalize_report
