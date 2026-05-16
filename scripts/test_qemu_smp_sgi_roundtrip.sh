#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM1.H.5 — Cross-core SGI round-trip test.
#
# Boots QEMU `-smp 4` with seLe4n.  After all 4 cores reach their per-
# core ready banner, the boot core sends an SGI to core 1; core 1's
# handler increments a shared atomic counter then sends an ACK SGI
# back.  The boot core waits for the counter increment and emits a
# success banner.
#
# **Prerequisites**:
#   * SM1.F.5 SGI handler dispatch wired and registered for INTID
#     `tlbShootdownReq` on every secondary's IRQ vector.
#   * SM1.H.1 base bringup test passes.
#
# **Test handler design** (kernel-side, NOT in the HAL):
#   * Boot core registers an `acknowledge` handler at INTID
#     `tlbShootdownAck` (= 2 per SM0.H).
#   * Each secondary registers a `forward` handler at INTID
#     `tlbShootdownReq` (= 1) that:
#         1. Increments the shared `SGI_REQ_RECEIVED` AtomicU32.
#         2. Sends INTID 2 (ack) back to the boot core via send_sgi(0x01, 2).
#   * Boot core, after Phase 6 banner, sends INTID 1 to core 1 via
#     send_sgi(0x02, 1) and waits for `SGI_ACK_RECEIVED == 1`.
#   * On ACK, boot core emits "[smp-test] SGI round-trip complete".
#
# At v1.0.0 (this script's landing) the kernel-side test handlers are
# NOT yet wired (they require SM5+ per-core scheduler state to register
# from Lean).  This script SKIPs with a documentation banner until the
# handler wiring lands at SM5.
#
# Skip / pass / fail conditions:
#   * No QEMU on PATH       → SKIP
#   * No kernel image       → SKIP
#   * Test handlers unwired → SKIP (current state at SM1.F)
#   * Timeout / no ACK      → FAIL

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM1.H.5: qemu-system-aarch64 not found on PATH"
  exit 0
fi

# Kernel image must be set explicitly via $SELE4N_KERNEL_IMAGE — at
# SM1.H landing there is no kernel binary target (see
# test_qemu_smp_bringup.sh header for details).
KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-}"

if [[ -z "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM1.H.5: SELE4N_KERNEL_IMAGE env var not set"
  echo "       Set SELE4N_KERNEL_IMAGE=/path/to/kernel.elf to enable."
  exit 0
fi

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM1.H.5: kernel image not found at ${KERNEL_IMAGE}"
  exit 0
fi

# --------------------------------------------------------------------------
# Pre-condition: kernel-side SGI test handlers must be wired.  At SM1.F
# the handler dispatch infrastructure is in place (gic::dispatch_sgi,
# gic::register_sgi_handler, FFI exports), but registering the test
# handlers requires Lean-side glue that lands at SM5+ when per-core
# scheduler state exists.
#
# We detect the wiring by greping the kernel image's `.rodata` strings
# for the test banner the handlers would emit.  If the banner string
# is absent, the handlers haven't been registered → SKIP.
# --------------------------------------------------------------------------
TEST_BANNER="\\[smp-test\\] SGI round-trip complete"
if ! strings "${KERNEL_IMAGE}" 2>/dev/null | grep -q "smp-test.*SGI round-trip"; then
  echo "[SKIP] WS-SM SM1.H.5: SGI test handlers not yet wired in kernel image"
  echo ""
  echo "  Reason: kernel-side SGI handler registration requires SM5+"
  echo "          per-core scheduler state to register from Lean.  At"
  echo "          SM1.F the HAL primitives (send_sgi, dispatch_sgi,"
  echo "          register_sgi_handler) are present and unit-tested; the"
  echo "          kernel-side wiring is the SM5 / SM7 follow-on."
  echo ""
  echo "  When wired (SM5+), this script will:"
  echo "    1. Boot QEMU virt -smp 4."
  echo "    2. Wait for primary's '[smp-test] sending INTID 1 to core 1'."
  echo "    3. Wait for core 1's '[smp-test] received SGI 1, sending ACK'."
  echo "    4. Wait for primary's '[smp-test] SGI round-trip complete'."
  echo ""
  echo "  HAL-level coverage at SM1.F (already passing):"
  echo "    cargo test -p sele4n-hal --lib gic::tests::sm1f"
  echo "    cargo test -p sele4n-hal --lib ffi::tests::sm1f6"
  exit 0
fi

# --------------------------------------------------------------------------
# Run the test (only reached if test handlers are wired)
# --------------------------------------------------------------------------
LOG="$(mktemp -t sele4n-smp-sgi.XXXXXX.log)"
# shellcheck disable=SC2064
trap "rm -f '${LOG}'" EXIT

TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-30}"

echo "[META] WS-SM SM1.H.5: booting QEMU virt -smp 4 for SGI round-trip"
echo "[META]   kernel image: ${KERNEL_IMAGE}"
echo "[META]   log: ${LOG}"

set +e
timeout "${TIMEOUT_SECS}s" qemu-system-aarch64 \
    -machine "virt,secure=on,virtualization=on" \
    -cpu cortex-a76 \
    -smp 4 \
    -m 1G \
    -kernel "${KERNEL_IMAGE}" \
    -nographic \
    -serial mon:stdio \
    -d guest_errors \
    < /dev/null \
    > "${LOG}" 2>&1
QEMU_EXIT=$?
set -e

case "${QEMU_EXIT}" in
  0|124) ;;
  *)
    echo "[FAIL] WS-SM SM1.H.5: QEMU exited with code ${QEMU_EXIT}" >&2
    echo "       Last 40 lines of UART log:" >&2
    tail -n 40 "${LOG}" >&2
    exit 1
    ;;
esac

# Verify the round-trip completion banner.
if ! grep -qE "${TEST_BANNER}" "${LOG}"; then
  echo "[FAIL] WS-SM SM1.H.5: round-trip banner missing from UART log" >&2
  echo "       Last 80 lines of UART log:" >&2
  tail -n 80 "${LOG}" >&2
  exit 1
fi

echo "[PASS] WS-SM SM1.H.5: cross-core SGI round-trip succeeded"
exit 0
