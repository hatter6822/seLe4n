#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM5.C.12 (plan §6 Tier-4) — Cross-core wake-via-SGI round-trip test.
#
# Boots QEMU `-smp 4` with seLe4n and exercises the cross-core wake protocol
# end-to-end: core A wakes a thread bound to core B (`wakeThread`), the verified
# state commits, core A emits a `.reschedule` SGI to core B (`emitWakeSgi`), and
# core B's SGI handler (`handleRescheduleSgiOnCore`) re-runs its scheduler and
# dispatches the woken thread.  The runtime witness for SM5.C's
# `wakeThread_roundtrip_reachable_current`: a cross-core wake is not merely "not
# lost" but actually scheduled once its SGI is serviced — on real hardware-
# modelled cores, with a real GIC delivering the SGI.
#
# **What the formal layer already guarantees (SM5.C, no QEMU needed)**:
#   * `wakeThread_target_runQueue_contains` — the woken thread lands in the
#     target run queue (it is not lost; SM5.C.10).
#   * `wakeThread_emits_sgi_if_remote` — a remote wake of a TCB emits exactly a
#     `.reschedule` SGI to the target (Theorem 3.3.1; SM5.C.4).
#   * `wakeThread_then_handle_dispatches_current` /
#     `wakeThread_roundtrip_reachable_current` — the wake → SGI-handler round-trip
#     dispatches the woken thread to *current* in two genuine scheduler steps
#     (the `SchedReachable` `.tail`/`.switch` closure; SM5.C.6 multi-step).
#   * `wakeThread_preserves_ipcSchedulerContract` — the wake never creates a
#     runnable-but-blocked thread (it sets `ipcState := .ready`; §10).
#   * `Concurrency.wakeOrdering_happensBefore` — the run-queue publication
#     happens-before the target observes it on the SGI (the BKL ordering, §11),
#     backed by the Rust `dsb ish` before `GICD_SGIR` (SM1.F.8).
#   These are machine-checked in `tests/SmpWakeSuite.lean` (Tier 2/3) and hold
#   for ALL executions — the QEMU test is a complementary *runtime* spot-check.
#
# **Prerequisites (SM5+)**:
#   * Per-core scheduler state so each core runs an independent thread that can
#     be the wake source / target (SM5.D+).
#   * The `@[export]` kernel-transition bodies wrapped in `withLockSet` over the
#     `wakeThreadLockSet` footprint (the per-core FFI seam; SM5.D+).
#   * A cross-core wake driver in the kernel image emitting the banner below.
#
# At v0.31.40 (this script's landing) the kernel is modelled single-core at the
# abstract layer; the per-core scheduler wiring that lets a real core wake a
# thread on another core lands at SM5.D+.  This script therefore SKIPs with a
# documentation banner until that wiring exists.
#
# Skip / pass / fail conditions:
#   * No QEMU on PATH                 → SKIP
#   * No kernel image                 → SKIP
#   * Cross-core wake driver unwired  → SKIP (current state, SM5.C)
#   * SGI lost / no dispatch / hang   → FAIL
#   * Woken thread runs on target     → PASS

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM5.C.12: qemu-system-aarch64 not found on PATH"
  exit 0
fi

KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-}"

if [[ -z "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM5.C.12: SELE4N_KERNEL_IMAGE env var not set"
  echo "       Set SELE4N_KERNEL_IMAGE=/path/to/kernel.elf to enable."
  exit 0
fi

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM5.C.12: kernel image not found at ${KERNEL_IMAGE}"
  exit 0
fi

# --------------------------------------------------------------------------
# Pre-condition: the cross-core wake driver must be wired in the kernel
# image.  We detect it by the banner the driver emits.  At SM5.C the driver
# is NOT present (it needs SM5.D+ per-core scheduler state to run an
# independent thread that issues a cross-core wake), so this SKIPs.
# --------------------------------------------------------------------------
TEST_BANNER="\\[smp-test\\] cross-core-wake: woken thread dispatched on target"
if ! strings "${KERNEL_IMAGE}" 2>/dev/null | grep -q "smp-test.*cross-core-wake"; then
  echo "[SKIP] WS-SM SM5.C.12: cross-core wake driver not wired in kernel image"
  echo ""
  echo "  Reason: exercising a real cross-core wake requires SM5.D+ per-core"
  echo "          scheduler state (an independent thread on one core that wakes"
  echo "          a thread bound to another core) and the @[export] wake body"
  echo "          wrapped in withLockSet over wakeThreadLockSet.  At SM5.C the"
  echo "          kernel is modelled single-core; the wake correctness guarantee"
  echo "          is established FORMALLY (and for ALL executions) by:"
  echo "            wakeThread_target_runQueue_contains   (not lost; SM5.C.10)"
  echo "            wakeThread_emits_sgi_if_remote        (Thm 3.3.1; SM5.C.4)"
  echo "            wakeThread_roundtrip_reachable_current (dispatched; SM5.C.6)"
  echo "            wakeThread_preserves_ipcSchedulerContract (coherent; §10)"
  echo "            Concurrency.wakeOrdering_happensBefore (BKL ordering; §11)"
  echo "          machine-checked in tests/SmpWakeSuite.lean."
  echo ""
  echo "  When wired (SM5.D+), this script will:"
  echo "    1. Boot QEMU virt -smp 4."
  echo "    2. Have core 0 wake a thread bound to core 1 (wakeThread) and emit"
  echo "       the .reschedule SGI (emitWakeSgi)."
  echo "    3. Assert core 1's SGI handler dispatches the woken thread (it runs)."
  echo "    4. Assert '[smp-test] cross-core-wake: woken thread dispatched on target'."
  echo ""
  echo "  Formal coverage at SM5.C (already passing):"
  echo "    lake exe smp_wake_suite"
  exit 0
fi

# --------------------------------------------------------------------------
# Run the test (only reached if the wake driver is wired)
# --------------------------------------------------------------------------
LOG="$(mktemp -t sele4n-smp-wake.XXXXXX.log)"
# shellcheck disable=SC2064
trap "rm -f '${LOG}'" EXIT

TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-60}"

echo "[META] WS-SM SM5.C.12: booting QEMU virt -smp 4 for cross-core wake round-trip"
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

# A lost SGI / failed dispatch manifests as the banner being absent (the woken
# thread never ran on the target).  A hang ⟹ the timeout fires (124).
if ! grep -qE "${TEST_BANNER}" "${LOG}"; then
  echo "[FAIL] WS-SM SM5.C.12: dispatch banner missing (SGI lost or no re-schedule)" >&2
  echo "       QEMU exit code: ${QEMU_EXIT}" >&2
  echo "       Last 80 lines of UART log:" >&2
  tail -n 80 "${LOG}" >&2
  exit 1
fi

case "${QEMU_EXIT}" in
  0|124) ;;
  *)
    echo "[FAIL] WS-SM SM5.C.12: QEMU exited with code ${QEMU_EXIT}" >&2
    tail -n 40 "${LOG}" >&2
    exit 1
    ;;
esac

echo "[PASS] WS-SM SM5.C.12: cross-core wake round-trip completed (woken thread dispatched)"
exit 0
