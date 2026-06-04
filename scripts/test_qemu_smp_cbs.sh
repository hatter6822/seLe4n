#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM5.H (plan §6 Tier-4) — Per-core CBS replenishment + affinity-migration test.
#
# Boots QEMU `-smp 4` with seLe4n and exercises per-core CBS: each core runs its OWN
# Constant-Bandwidth-Server replenishment queue (plan §3.8), and an affinity change on
# a SchedContext-bound thread migrates that thread's pending replenishments AND its
# run-queue entry to the new home core (full thread migration), emitting a cross-core
# `.reschedule` SGI when the new home is remote.
#
# **What the formal layer already guarantees (SM5.H, no QEMU needed)**:
#   * `replenishOnCore_preserves_perCoreCbsInvariant` — per-core CBS scheduling keeps
#     the replenish queue valid + future-ordered + affinity-consistent.
#   * `timerTickBudgetOnCore_bound_exhausted_replenish_eq` (A2) — the LIVE per-core
#     timer tick's replenish write IS the abstract `replenishOnCore` primitive's.
#   * `timerTickBudgetOnCore_preserves_replenishQueueValidOnCore` (A4) — the live
#     budget tick preserves replenish-queue validity on every core.
#   * `schedContextMigration_consistent_of_bindingConsistent` (B7) — the affinity
#     migration RESTORES per-core CBS affinity consistency on every core.
#   * `setThreadCpuAffinityWithMigration_preserves_perCoreCbsInvariant_smp` (A5) — the
#     full composite preserves the aggregate per-core CBS invariant on every core.
#   * `setThreadCpuAffinityWithMigration_preserves_runQueueOnCoreWellFormed` — the
#     run-queue migration keeps both cores' run queues well-formed.
#   * `affinityMigrationOrdering_happensBefore` (C10) — the migration's re-homing
#     happens-before the new home core observes it on the `.reschedule` SGI.
#   These are machine-checked in `tests/SmpCbsSuite.lean` (Tier 2/3) and hold for ALL
#   executions — the QEMU test is a complementary *runtime* spot-check.
#
# **Prerequisites (SM5.I+)**:
#   * The per-core run loop driving `timerTickOnCore` on each core's timer tick.
#   * A `tcbSetAffinity`-driven migration driver in the kernel image emitting the
#     banner below.
#
# At v0.31.54 (this script's landing) the kernel is modelled single-core at the
# abstract layer; the per-core scheduler tick that drives `timerTickOnCore` per core
# lands at SM5.I.  This script therefore SKIPs with a documentation banner until that
# wiring exists.
#
# Skip / pass / fail conditions:
#   * No QEMU on PATH                          → SKIP
#   * No kernel image                          → SKIP
#   * Per-core CBS / migration driver unwired  → SKIP (current state, SM5.H)
#   * A core fails to migrate / cross-core leak → FAIL
#   * Each core runs its own CBS + migration works → PASS

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM5.H: qemu-system-aarch64 not found on PATH"
  exit 0
fi

KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-}"

if [[ -z "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM5.H: SELE4N_KERNEL_IMAGE env var not set"
  echo "       Set SELE4N_KERNEL_IMAGE=/path/to/kernel.elf to enable."
  exit 0
fi

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM5.H: kernel image not found at ${KERNEL_IMAGE}"
  exit 0
fi

# --------------------------------------------------------------------------
# Pre-condition: the per-core CBS + affinity-migration driver must be wired in the
# kernel image.  Detect it by the banner the driver emits.  At SM5.H the driver is
# NOT present (it needs SM5.I's per-core scheduler tick driving timerTickOnCore plus
# a tcbSetAffinity-driven migration), so this SKIPs.  Capture `strings` first, then
# grep, to avoid a SIGPIPE under `set -o pipefail`.
# --------------------------------------------------------------------------
KERNEL_STRINGS="$(strings "${KERNEL_IMAGE}" 2>/dev/null || true)"
if ! grep -q "smp-test.*per-core-cbs" <<<"${KERNEL_STRINGS}"; then
  echo "[SKIP] WS-SM SM5.H: per-core CBS / affinity-migration driver not wired in kernel image"
  echo ""
  echo "  Reason: exercising real per-core CBS + thread migration requires SM5.I's"
  echo "          per-core scheduler tick driving timerTickOnCore on each core, plus a"
  echo "          tcbSetAffinity-driven migration.  At SM5.H the kernel is modelled"
  echo "          single-core; the per-core CBS correctness guarantee is established"
  echo "          FORMALLY (and for ALL executions) by:"
  echo "            replenishOnCore_preserves_perCoreCbsInvariant   (per-core CBS inv.)"
  echo "            timerTickBudgetOnCore_bound_exhausted_replenish_eq  (A2 live bridge)"
  echo "            timerTickBudgetOnCore_preserves_replenishQueueValidOnCore (A4)"
  echo "            schedContextMigration_consistent_of_bindingConsistent  (B7 migrate)"
  echo "            setThreadCpuAffinityWithMigration_preserves_perCoreCbsInvariant_smp"
  echo "            affinityMigrationOrdering_happensBefore         (C10 cross-core HB)"
  echo "          machine-checked in tests/SmpCbsSuite.lean."
  echo ""
  echo "  When wired (SM5.I), this script will:"
  echo "    1. Boot QEMU virt -smp 4 with per-core CBS SchedContexts."
  echo "    2. Tick each core's timer so each refills its own SchedContexts' budgets."
  echo "    3. tcbSetAffinity-migrate a bound thread to a remote core."
  echo "    4. Assert its replenishments + run-queue entry moved + the SGI fired."
  echo "    5. Assert '[smp-test] per-core-cbs: migration complete on all cores'."
  echo ""
  echo "  Formal coverage at SM5.H (already passing):"
  echo "    lake exe smp_cbs_suite"
  exit 0
fi

# --------------------------------------------------------------------------
# Run the test (only reached if the per-core CBS / migration driver is wired)
# --------------------------------------------------------------------------
LOG="$(mktemp -t sele4n-smp-cbs.XXXXXX.log)"
# shellcheck disable=SC2064
trap "rm -f '${LOG}'" EXIT

TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-60}"

echo "[META] WS-SM SM5.H: booting QEMU virt -smp 4 for per-core CBS + migration"
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

if grep -q "smp-test.*per-core-cbs: migration complete on all cores" "${LOG}"; then
  echo "[PASS] WS-SM SM5.H: per-core CBS + affinity migration verified on -smp 4"
  exit 0
else
  echo "[FAIL] WS-SM SM5.H: per-core CBS migration banner not observed (qemu exit ${QEMU_EXIT})"
  echo "------ QEMU log tail ------"
  tail -40 "${LOG}" || true
  exit 1
fi
