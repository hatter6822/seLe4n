#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM5.F.10 (plan §6 Tier-4) — Cross-core priority-inheritance round-trip test.
#
# Boots QEMU `-smp 4` with seLe4n and exercises the cross-core PIP protocol
# end-to-end: a high-priority thread on core A blocks (Reply IPC) on a resource
# held by a lower-priority server on core B; the kernel boosts the server to the
# waiter's priority on its home core B (`updatePipBoostOnCore` / `pipBoostWithWake`),
# commits the verified boost state, fires a `.reschedule` SGI to core B
# (`fireCrossCoreSgis`), and core B's SGI handler re-runs its scheduler so the
# boosted server runs and releases the resource.  The runtime witness for SM5.F's
# cross-core priority-inheritance: a remote boost is not merely computed but
# actually delivered + rescheduled — on real hardware-modelled cores, with a real
# GIC delivering the SGI.
#
# **What the formal layer already guarantees (SM5.F, no QEMU needed)**:
#   * `pipBoostWithWake_emits_sgi_if_remote` — a remote, runnable-on-home, material
#     boost emits exactly a `.reschedule` SGI to the holder's home core (Thm 3.6.1).
#   * `pipBoostWithWake_no_sgi_if_not_runnable` — a boost of a blocked holder fires
#     no spurious cross-core IPI (C9 precision).
#   * `propagatePipChainCrossCore_head_sgi_remote` /
#     `propagatePipChainCrossCore_second_link_sgi_remote` — every remote link of a
#     donation chain across cores contributes its `.reschedule` SGI (SM5.F.4).
#   * `computeMaxWaiterPriority_eq_sup_perCore` — the global boost is exactly the
#     supremum over every core's waiter slice (no waiter's contribution lost).
#   * `priorityInheritance_perCore_witness_full` — the cross-core PIP is an acyclic,
#     consistent, complete decomposition of the global discipline (SM5.F.9).
#   * `Concurrency.pipBoostOrdering_happensBefore` — the boost's run-queue
#     publication happens-before the home core observes it on the SGI (the BKL
#     ordering, §9b), backed by the Rust `dsb ish` before `GICD_SGIR` (SM1.F.8).
#   * `propagatePipChainCrossCore_singleCore_no_sgis` /
#     `crossCoreWakeDispatch_singleCore` — the dispatch is inert (`pure ()`) on
#     single-core, so it is trace-preserving until per-core affinities exist.
#   These are machine-checked in `tests/SmpPipSuite.lean` (Tier 2/3) and hold for
#   ALL executions — the QEMU test is a complementary *runtime* spot-check.
#
# **Prerequisites (SM5.I+)**:
#   * Per-core scheduler state so a high-priority thread on one core blocks on a
#     server bound to another core (SM5.D+).
#   * The IPC donation / timeout / resume `@[export]` bodies routing through the
#     per-core boost (`pipBoostWithWake`) + firing the SGIs over the FFI
#     (`fireCrossCoreSgis`) — the per-core FFI seam (SM5.I).
#   * A cross-core PIP driver in the kernel image emitting the banner below.
#
# At v0.31.50 (this script's landing) the kernel is modelled single-core at the
# abstract layer; the per-core scheduler + donation-path wiring that lets a real
# core boost a server on another core lands at SM5.I.  This script therefore SKIPs
# with a documentation banner until that wiring exists.
#
# Skip / pass / fail conditions:
#   * No QEMU on PATH                    → SKIP
#   * No kernel image                    → SKIP
#   * Cross-core PIP driver unwired      → SKIP (current state, SM5.F)
#   * Boost SGI lost / no reschedule     → FAIL
#   * Boosted server runs on home core   → PASS

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM5.F.10: qemu-system-aarch64 not found on PATH"
  exit 0
fi

KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-}"

if [[ -z "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM5.F.10: SELE4N_KERNEL_IMAGE env var not set"
  echo "       Set SELE4N_KERNEL_IMAGE=/path/to/kernel.elf to enable."
  exit 0
fi

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM5.F.10: kernel image not found at ${KERNEL_IMAGE}"
  exit 0
fi

# --------------------------------------------------------------------------
# Pre-condition: the cross-core PIP driver must be wired in the kernel image.
# We detect it by the banner the driver emits.  At SM5.F the driver is NOT
# present (it needs SM5.I per-core scheduler state + donation-path SGI firing),
# so this SKIPs.
# --------------------------------------------------------------------------
if ! strings "${KERNEL_IMAGE}" 2>/dev/null | grep -q "smp-test.*cross-core-pip"; then
  echo "[SKIP] WS-SM SM5.F.10: cross-core PIP driver not wired in kernel image"
  echo ""
  echo "  Reason: exercising a real cross-core priority-inheritance boost requires"
  echo "          SM5.I per-core scheduler state (a high-priority thread on one core"
  echo "          blocked on a server bound to another core) and the IPC donation"
  echo "          @[export] body routing through pipBoostWithWake + fireCrossCoreSgis."
  echo "          At SM5.F the kernel is modelled single-core; the cross-core PIP"
  echo "          correctness guarantee is established FORMALLY (and for ALL"
  echo "          executions) by:"
  echo "            pipBoostWithWake_emits_sgi_if_remote        (Thm 3.6.1)"
  echo "            propagatePipChainCrossCore_head_sgi_remote  (chain link; SM5.F.4)"
  echo "            computeMaxWaiterPriority_eq_sup_perCore      (no waiter lost)"
  echo "            priorityInheritance_perCore_witness_full     (sound+complete; SM5.F.9)"
  echo "            Concurrency.pipBoostOrdering_happensBefore   (BKL ordering; §9b)"
  echo "          machine-checked in tests/SmpPipSuite.lean."
  echo ""
  echo "  When wired (SM5.I), this script will:"
  echo "    1. Boot QEMU virt -smp 4."
  echo "    2. Have a high-priority thread on core 0 block on a server bound to"
  echo "       core 1; the kernel boosts the server on core 1 and fires the"
  echo "       .reschedule SGI (fireCrossCoreSgis)."
  echo "    3. Assert core 1's SGI handler reschedules and the boosted server runs."
  echo "    4. Assert '[smp-test] cross-core-pip: boosted server dispatched on home'."
  echo ""
  echo "  Formal coverage at SM5.F (already passing):"
  echo "    lake exe smp_pip_suite"
  exit 0
fi

# --------------------------------------------------------------------------
# Run the test (only reached if the cross-core PIP driver is wired)
# --------------------------------------------------------------------------
LOG="$(mktemp -t sele4n-smp-pip.XXXXXX.log)"
# shellcheck disable=SC2064
trap "rm -f '${LOG}'" EXIT

TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-60}"

echo "[META] WS-SM SM5.F.10: booting QEMU virt -smp 4 for cross-core PIP round-trip"
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

if grep -q "smp-test.*cross-core-pip: boosted server dispatched on home" "${LOG}"; then
  echo "[PASS] WS-SM SM5.F.10: cross-core PIP boost delivered + rescheduled on home core"
  exit 0
else
  echo "[FAIL] WS-SM SM5.F.10: cross-core PIP round-trip banner not observed (qemu exit ${QEMU_EXIT})"
  echo "------ QEMU log tail ------"
  tail -40 "${LOG}" || true
  exit 1
fi
