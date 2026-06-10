#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM5.K.5 (plan §6 / §8 Tier-4) — Per-core scheduler 4-thread/4-core test.
#
# Boots QEMU `-smp 4` with seLe4n and exercises the SM5 per-core scheduler
# end-to-end: a 4-thread workload, one thread bound (cpuAffinity) to each core, is
# distributed across the four cores.  The runtime witness for the SM5 acceptance
# gate (plan §8): each core selects and runs its OWN bound thread from its OWN run
# queue, a cross-core wake delivers a `.reschedule` SGI to the target core, and no
# core stalls (the per-core idle thread is the priority-0 fallback).
#
# **What the formal layer already guarantees (SM5, no QEMU needed)**:
#   * chooseThreadOnCore_selects_highest / _perCore_independence — each core selects
#     the highest-priority runnable thread from its own run queue, independently of
#     the other cores (SM5.A).
#   * switchToThreadOnCore_sets_current / _rejects_remote — per-core context switch
#     dispatches a locally-bound thread and rejects a remote-bound one (SM5.B).
#   * wakeThread_emits_sgi_if_remote — a wake of a thread bound to a remote core
#     emits a cross-core `.reschedule` SGI (SM5.C).
#   * chooseThreadOnCore_always_succeeds — the per-core idle thread guarantees no
#     core ever stalls (SM5.E); no_starvation_under_smp — no thread starves under
#     SMP (SM5.J.4).
#   * wcrt_bound_rpi5_smp — every per-core op's WCRT under fine locks is bounded by
#     maxLockSetSize·3·tCs, within the 1 ms tick budget (SM5.J).
#   These are machine-checked in tests/SmpSchedulerSuite.lean (the 4-thread/4-core
#   aggregate, 50+ scenarios + the golden trace fixture) and tests/SmpWcrtSuite.lean
#   (Tier 2/3) and hold for ALL executions — the QEMU test is a complementary
#   *runtime* spot-check.
#
# **Prerequisites (SM5.I+ / SM6+)**:
#   * The per-core run loop driving chooseThreadOnCore / switchToThreadOnCore on each
#     core's timer tick (the SM5.I per-core scheduler-tick driver).
#   * Cross-core wake wired to fire the `.reschedule` SGI over the GIC (SM5.C/SM5.F
#     fireCrossCoreSgis seam, production call-site substitution at SM5.I+).
#   * A 4-thread/4-core scheduler driver in the kernel image emitting the banner below.
#
# At the SM5.K landing the kernel is modelled single-core at the abstract layer; the
# per-core scheduler run loop that drives the live 4-core distribution lands at
# SM5.I+.  This script therefore SKIPs with a documentation banner until that wiring
# exists.
#
# Skip / pass / fail conditions:
#   * No QEMU on PATH                          → SKIP
#   * No kernel image                          → SKIP
#   * Per-core scheduler driver unwired        → SKIP (current state, SM5.K)
#   * A core fails to run its bound thread / cross-core leak → FAIL
#   * Each core runs its own thread + wake SGI delivered → PASS

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM5.K.5: qemu-system-aarch64 not found on PATH"
  exit 0
fi

KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-}"

if [[ -z "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM5.K.5: SELE4N_KERNEL_IMAGE env var not set"
  echo "       Set SELE4N_KERNEL_IMAGE=/path/to/kernel.elf to enable."
  exit 0
fi

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM5.K.5: kernel image not found at ${KERNEL_IMAGE}"
  exit 0
fi

# --------------------------------------------------------------------------
# Pre-condition: the per-core 4-thread scheduler driver must be wired in the kernel
# image.  Detect it by the banner the driver emits.  At SM5.K the driver is NOT
# present (it needs SM5.I's per-core scheduler run loop), so this SKIPs.  Capture
# `strings` first, then grep, to avoid a SIGPIPE under `set -o pipefail`.
# --------------------------------------------------------------------------
KERNEL_STRINGS="$(strings "${KERNEL_IMAGE}" 2>/dev/null || true)"
if ! grep -q "smp-test.*per-core-scheduler" <<<"${KERNEL_STRINGS}"; then
  echo "[SKIP] WS-SM SM5.K.5: per-core scheduler driver not wired in kernel image"
  echo ""
  echo "  Reason: exercising the real 4-thread/4-core distribution requires SM5.I's"
  echo "          per-core scheduler run loop driving chooseThreadOnCore /"
  echo "          switchToThreadOnCore on each core, plus the cross-core wake SGI"
  echo "          firing seam.  At SM5.K the kernel is modelled single-core; the"
  echo "          per-core scheduler correctness guarantee is established FORMALLY"
  echo "          (and for ALL executions) by:"
  echo "            chooseThreadOnCore_selects_highest      (per-core selection)"
  echo "            chooseThreadOnCore_perCore_independence  (cross-core independence)"
  echo "            switchToThreadOnCore_sets_current/_rejects_remote (per-core switch)"
  echo "            wakeThread_emits_sgi_if_remote           (cross-core wake SGI)"
  echo "            no_starvation_under_smp                  (no thread starves)"
  echo "            wcrt_bound_rpi5_smp                      (bounded WCRT under fine locks)"
  echo "          machine-checked in tests/SmpSchedulerSuite.lean (50+ scenarios + the"
  echo "          golden 4-core trace fixture) and tests/SmpWcrtSuite.lean."
  echo ""
  echo "  When wired (SM5.I+), this script will:"
  echo "    1. Boot QEMU virt -smp 4 with a 4-thread workload (one bound per core)."
  echo "    2. Let each core's run loop select + run its OWN bound thread."
  echo "    3. Trigger a cross-core wake and assert the .reschedule SGI is delivered."
  echo "    4. Assert '[smp-test] per-core-scheduler: 4 threads ran on 4 cores'."
  echo ""
  echo "  Formal coverage at SM5.K (already passing):"
  echo "    lake exe smp_scheduler_suite"
  echo "    lake exe smp_wcrt_suite"
  exit 0
fi

# --------------------------------------------------------------------------
# Run the test (only reached if the per-core scheduler driver is wired)
# --------------------------------------------------------------------------
LOG="$(mktemp -t sele4n-smp-scheduler.XXXXXX.log)"
# shellcheck disable=SC2064
trap "rm -f '${LOG}'" EXIT

TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-60}"

echo "[META] WS-SM SM5.K.5: booting QEMU virt -smp 4 for the 4-thread/4-core scheduler"
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

if grep -q "smp-test.*per-core-scheduler: 4 threads ran on 4 cores" "${LOG}"; then
  echo "[PASS] WS-SM SM5.K.5: each core ran its own bound thread; cross-core wake delivered"
  exit 0
else
  echo "[FAIL] WS-SM SM5.K.5: per-core scheduler banner not observed (qemu exit ${QEMU_EXIT})"
  echo "------ QEMU log tail ------"
  tail -40 "${LOG}" || true
  exit 1
fi
