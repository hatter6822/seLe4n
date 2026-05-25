#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM3.D.7 (plan §6.3 Tier-4) — Cross-core deadlock-freedom stress test.
#
# Boots QEMU `-smp 4` with seLe4n and drives multiple cores through
# contended multi-object kernel transitions (scheduling + IPC paths)
# that each acquire their `lockSet_<τ>` footprint under the SM3.C
# `withLockSet` 2PL discipline in SM0.I `LockId` order.  The runtime
# witness for SM3.D's `deadlockFreedom_under_2pl_and_ordering`
# (Theorem 2.1.9): under sustained cross-core lock contention the
# system makes progress — no wait-cycle ever forms — and every core
# eventually completes its transition (the `boundedWait_under_2pl`
# bound holds in practice).
#
# **What the formal layer already guarantees (SM3.D, no QEMU needed)**:
#   * `deadlockFreedom_under_2pl_and_ordering` — no two cores mutually
#     block (Theorem 2.1.9).
#   * `waitGraph_acyclic_under_2pl` — the N-core wait graph is a DAG.
#   * `conflictWaitGraph_acyclic_under_2pl` — the mode-aware (read/write)
#     wait graph is a DAG.
#   * `boundedWait_under_2pl` — WCRT ≤ maxLockSetSize·(numCores−1)·T_cs.
#   * `execution_satisfies_hypotheses_of_all_prefix` — the hypotheses
#     are discharged by the `withLockSet` growing phase.
#   These are machine-checked in `tests/DeadlockFreedomSuite.lean`
#   (Tier 2/3) and hold for ALL executions — the QEMU stress test is a
#   complementary *runtime* spot-check on real hardware-modelled cores.
#
# **Prerequisites (SM5+)**:
#   * Per-core scheduler state so each core runs an independent thread
#     issuing syscalls (SM5).
#   * Cross-core IPC handshake so contended endpoint/notification
#     transitions exercise multi-core lock acquisition (SM6).
#   * The `@[export]` kernel-transition bodies wrapped in `withLockSet`
#     (SM3.C.9, deferred to the SM5+ per-core FFI seam).
#
# At v1.0.0 (this script's landing) the kernel is modelled single-core
# at the abstract layer, and the multi-core scheduling/IPC wiring that
# would let real cores contend for locks lands at SM5+.  This script
# therefore SKIPs with a documentation banner until that wiring exists.
#
# Skip / pass / fail conditions:
#   * No QEMU on PATH                 → SKIP
#   * No kernel image                 → SKIP
#   * Multi-core contention unwired   → SKIP (current state, SM3.D)
#   * Deadlock / no-progress / hang   → FAIL
#   * All cores complete, no cycle    → PASS

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM3.D.7: qemu-system-aarch64 not found on PATH"
  exit 0
fi

KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-}"

if [[ -z "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM3.D.7: SELE4N_KERNEL_IMAGE env var not set"
  echo "       Set SELE4N_KERNEL_IMAGE=/path/to/kernel.elf to enable."
  exit 0
fi

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM3.D.7: kernel image not found at ${KERNEL_IMAGE}"
  exit 0
fi

# --------------------------------------------------------------------------
# Pre-condition: the multi-core lock-contention driver must be wired in
# the kernel image.  We detect it by the banner the driver emits.  At
# SM3.D the driver is NOT present (it needs SM5+ per-core scheduler
# state to run independent contending threads), so this SKIPs.
# --------------------------------------------------------------------------
TEST_BANNER="\\[smp-test\\] deadlock-stress: all cores completed"
if ! strings "${KERNEL_IMAGE}" 2>/dev/null | grep -q "smp-test.*deadlock-stress"; then
  echo "[SKIP] WS-SM SM3.D.7: cross-core lock-contention driver not wired in kernel image"
  echo ""
  echo "  Reason: exercising real cross-core lock contention requires"
  echo "          SM5+ per-core scheduler state (independent contending"
  echo "          threads) and SM6 cross-core IPC.  At SM3.D the kernel"
  echo "          is modelled single-core; the deadlock-freedom guarantee"
  echo "          is established FORMALLY (and for ALL executions) by:"
  echo "            deadlockFreedom_under_2pl_and_ordering (Theorem 2.1.9)"
  echo "            waitGraph_acyclic_under_2pl  (N-core DAG)"
  echo "            conflictWaitGraph_acyclic_under_2pl  (mode-aware DAG)"
  echo "            boundedWait_under_2pl  (WCRT bound)"
  echo "          machine-checked in tests/DeadlockFreedomSuite.lean."
  echo ""
  echo "  When wired (SM5+), this script will:"
  echo "    1. Boot QEMU virt -smp 4."
  echo "    2. Drive each core through contended multi-object syscalls"
  echo "       (scheduling + IPC) acquiring lockSets via withLockSet."
  echo "    3. Assert every core emits its per-core completion banner"
  echo "       within the bounded-wait window (no hang ⟹ no deadlock)."
  echo "    4. Assert '[smp-test] deadlock-stress: all cores completed'."
  echo ""
  echo "  Formal coverage at SM3.D (already passing):"
  echo "    lake exe deadlock_freedom_suite"
  exit 0
fi

# --------------------------------------------------------------------------
# Run the test (only reached if the contention driver is wired)
# --------------------------------------------------------------------------
LOG="$(mktemp -t sele4n-smp-deadlock.XXXXXX.log)"
# shellcheck disable=SC2064
trap "rm -f '${LOG}'" EXIT

TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-60}"

echo "[META] WS-SM SM3.D.7: booting QEMU virt -smp 4 for deadlock-freedom stress"
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

# A genuine deadlock manifests as a hang ⟹ the timeout fires (124) AND
# the completion banner is absent.  Distinguish hang-without-progress
# (FAIL) from clean completion.
if ! grep -qE "${TEST_BANNER}" "${LOG}"; then
  echo "[FAIL] WS-SM SM3.D.7: completion banner missing (possible deadlock/hang)" >&2
  echo "       QEMU exit code: ${QEMU_EXIT}" >&2
  echo "       Last 80 lines of UART log:" >&2
  tail -n 80 "${LOG}" >&2
  exit 1
fi

case "${QEMU_EXIT}" in
  0|124) ;;
  *)
    echo "[FAIL] WS-SM SM3.D.7: QEMU exited with code ${QEMU_EXIT}" >&2
    tail -n 40 "${LOG}" >&2
    exit 1
    ;;
esac

echo "[PASS] WS-SM SM3.D.7: cross-core deadlock-freedom stress completed (no cycle)"
exit 0
