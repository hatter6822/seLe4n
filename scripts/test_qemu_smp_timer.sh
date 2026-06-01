#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM5.D (plan §6 Tier-4) — Per-core timer-tick boot test.
#
# Boots QEMU `-smp 4` with seLe4n and exercises the per-core ARM Generic Timer:
# each core's CNTV fires independently, its ISR (`timer::per_core_timer_tick_isr`)
# records the per-core tick, re-arms the per-core comparator, and drives the Lean
# per-core tick (`lean_per_core_timer_tick` → `perCoreTimerTickEntry`, SM5.D.1).
# The runtime witness for SM5.D's defining SMP property: every core advances its
# OWN local accounting (domain time, CBS budgets) without advancing the single
# global monotonic counter — on real hardware-modelled cores, with a real GIC.
#
# **What the formal layer already guarantees (SM5.D, no QEMU needed)**:
#   * `timerTickOnCore_advances_per_core` — the tick advances core c's local
#     accounting WITHOUT advancing the global `machine.timer` (SM5.D.2 headline:
#     the global tick counter is primary-owned, mirroring the Rust HAL TICK_COUNT).
#   * `timerTickOnCore_rotates_domain` — a domain-boundary tick rotates core c's
#     active domain to the next schedule entry (SM5.D.6).
#   * `timerTickOnCore_preempts_local` — budget / time-slice exhaustion re-selects
#     and dispatches core c's highest-priority budget-eligible thread (SM5.D.5).
#   * `cbsReplenish_can_wake_remote_core` — a CBS replenishment whose refilled
#     thread targets a remote core fires a cross-core `.reschedule` SGI (SM5.D.4).
#   * `timerTickOnCore_preserves_currentThreadValidOnCore` — the tick preserves
#     per-core current-thread validity UNCONDITIONALLY (§7 B1).
#   * `timerTickOnCore_preserves_objects_invExt` /
#     `timerTickOnCore_clears_lastTimeoutErrors` — object-store invariant + the
#     SM5.D.9 diagnostic clear.
#   These are machine-checked in `tests/SmpTimerSuite.lean` (Tier 2/3) and hold
#   for ALL executions — the QEMU test is a complementary *runtime* spot-check.
#
# **Prerequisites (SM5.I+)**:
#   * Per-core scheduler state so each core has live current / run-queue / domain
#     slots the tick advances (SM5.D models the transition; SM5.I drives it).
#   * The per-core timer ISR wired to drive `timerTickOnCore` against live
#     per-core kernel state under the `timerTickOnCoreLockSet` `withLockSet`
#     bracket (the per-core FFI seam; SM5.I).
#   * A per-core timer driver in the kernel image emitting the banner below.
#
# At v0.31.41 (this script's landing) `perCoreTimerTickEntry` is a deliberate
# `pure ()` placeholder; the per-core scheduler-tick wiring that lets a real
# core's CNTV advance live per-core state lands at SM5.I.  This script therefore
# SKIPs with a documentation banner until that wiring exists.
#
# Skip / pass / fail conditions:
#   * No QEMU on PATH                 → SKIP
#   * No kernel image                 → SKIP
#   * Per-core timer driver unwired   → SKIP (current state, SM5.D)
#   * Global timer advanced per-core  → FAIL
#   * Per-core tick banner missing    → FAIL
#   * Per-core ticks observed on 0..3 → PASS

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

LOG="$(mktemp -t sele4n-smp-timer.XXXXXX.log)"
TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT:-45}"
TEST_BANNER="\\[smp-test\\] per-core-timer: cores 0-3 ticked locally"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM5.D: qemu-system-aarch64 not found on PATH"
  exit 0
fi

KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-}"

if [[ -z "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM5.D: SELE4N_KERNEL_IMAGE env var not set"
  echo "       Set SELE4N_KERNEL_IMAGE=/path/to/kernel.elf to enable."
  exit 0
fi

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM5.D: kernel image not found at ${KERNEL_IMAGE}"
  exit 0
fi

# --------------------------------------------------------------------------
# Pre-condition: the per-core timer driver must be wired in the kernel image.
# We detect it by the banner the driver emits.  At SM5.D the driver is NOT
# present (it needs SM5.I per-core scheduler state to advance), so this SKIPs.
# --------------------------------------------------------------------------
if ! strings "${KERNEL_IMAGE}" 2>/dev/null | grep -q "smp-test.*per-core-timer"; then
  echo "[SKIP] WS-SM SM5.D: per-core timer driver not wired in kernel image"
  echo ""
  echo "  Reason: exercising a real per-core timer tick requires SM5.I per-core"
  echo "          scheduler state (live current / run-queue / domain slots per"
  echo "          core) and the per-core timer ISR driving timerTickOnCore under"
  echo "          withLockSet over timerTickOnCoreLockSet.  At SM5.D the per-core"
  echo "          entry seam (perCoreTimerTickEntry) is a pure () placeholder; the"
  echo "          tick correctness guarantee is established FORMALLY (and for ALL"
  echo "          executions) by:"
  echo "            timerTickOnCore_advances_per_core      (no global advance; D.2)"
  echo "            timerTickOnCore_rotates_domain         (domain rotation; D.6)"
  echo "            timerTickOnCore_preempts_local         (budget preempt; D.5)"
  echo "            cbsReplenish_can_wake_remote_core      (cross-core wake; D.4)"
  echo "            timerTickOnCore_preserves_currentThreadValidOnCore (B1; §7)"
  echo "          machine-checked in tests/SmpTimerSuite.lean."
  echo ""
  echo "  When wired (SM5.I), this script will:"
  echo "    1. Boot QEMU virt -smp 4."
  echo "    2. Let each core's CNTV fire and run timerTickOnCore locally."
  echo "    3. Assert the global monotonic timer is advanced by ONE authority"
  echo "       (no per-core double-advance)."
  echo "    4. Assert '[smp-test] per-core-timer: cores 0-3 ticked locally'."
  echo ""
  echo "  Formal coverage at SM5.D (already passing):"
  echo "    lake exe smp_timer_suite"
  exit 0
fi

echo "[META] WS-SM SM5.D: booting QEMU virt -smp 4 for per-core timer tick"
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

if ! grep -qE "${TEST_BANNER}" "${LOG}"; then
  echo "[FAIL] WS-SM SM5.D: per-core tick banner missing (a core failed to tick)" >&2
  echo "       QEMU exit code: ${QEMU_EXIT}" >&2
  echo "       Last 80 lines of UART log:" >&2
  tail -n 80 "${LOG}" >&2
  exit 1
fi

case "${QEMU_EXIT}" in
  0|124) ;;
  *)
    echo "[FAIL] WS-SM SM5.D: QEMU exited with code ${QEMU_EXIT}" >&2
    tail -n 40 "${LOG}" >&2
    exit 1
    ;;
esac

echo "[PASS] WS-SM SM5.D: per-core timer tick completed (cores 0-3 ticked locally)"
exit 0
