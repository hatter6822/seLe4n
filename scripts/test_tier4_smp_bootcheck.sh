#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM0.T → SM1.H — Tier-4 SMP boot-check (populated at SM1.H).
#
# At SM0 this slot was reserved as a SKIP-only stub.  Now (post-SM1.H)
# the slot routes through three concrete QEMU tests:
#
#   1. SM1.H.1 — `test_qemu_smp_bringup.sh` (`-smp 4`, full bringup)
#   2. SM1.H.3 — `test_qemu_smp_minimal.sh` (`-smp 2`, minimal smoke)
#   3. SM1.H.5 — `test_qemu_smp_sgi_roundtrip.sh` (cross-core SGI)
#
# Each sub-test handles its own SKIP conditions (qemu missing, kernel
# image missing, kernel-side handlers unwired) and exits 0 in those
# cases — so the tier-4 wrapper passes when the environment is bare,
# and exercises the substantive checks only when the prerequisites
# are met.
#
# Future phases populate additional sub-tests:
#   * SM5.K — per-core scheduler liveness probe
#   * SM6.F — cross-core IPC handshake exerciser
#   * SM7.E — TLB shootdown ACK timing
#   * SM8.E — information flow non-interference under SMP

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

log_section "META" "WS-SM tier-4 SMP boot-check (populated at SM1.H)"
log_section "META" "  Sub-tests handle their own SKIP conditions (qemu/kernel-image)."
log_section "META" "  Future phases (SM5.K, SM6.F, SM7.E, SM8.E) extend this slot."

# SM1.H.1 — full 4-core bringup.
run_check "META" "${SCRIPT_DIR}/test_qemu_smp_bringup.sh"

# SM1.H.3 — minimal 2-core bringup (boot + 1 secondary).
run_check "META" "${SCRIPT_DIR}/test_qemu_smp_minimal.sh"

# SM1.H.5 — cross-core SGI round-trip.  SKIPs at SM1.H if kernel-side
# handlers are not yet wired (SM5+ follow-on).
run_check "META" "${SCRIPT_DIR}/test_qemu_smp_sgi_roundtrip.sh"

# SM1.G.3 — cross-core kprintln stress test.  SKIPs at SM1.G if the
# stress-test routine isn't wired in the kernel image (SM5+ follow-on).
run_check "META" "${SCRIPT_DIR}/test_qemu_smp_kprintln_stress.sh"

# SM3.D.7 — cross-core deadlock-freedom stress (plan §6.3).  SKIPs at
# SM3.D if the multi-core lock-contention driver isn't wired in the
# kernel image (needs SM5+ per-core scheduler state).  Deadlock-freedom
# is established FORMALLY for all executions in
# tests/DeadlockFreedomSuite.lean; this is a complementary runtime
# spot-check on real hardware-modelled cores.
run_check "META" "${SCRIPT_DIR}/test_qemu_smp_deadlock_stress.sh"

# SM5.C.12 — cross-core wake-via-SGI round-trip (plan §6).  SKIPs at
# SM5.C if the cross-core wake driver isn't wired in the kernel image
# (needs SM5.D+ per-core scheduler state + the @[export] wake body under
# withLockSet).  The wake correctness — the woken thread is not lost,
# the .reschedule SGI is emitted, and the target dispatches it — is
# established FORMALLY for all executions in tests/SmpWakeSuite.lean;
# this is a complementary runtime spot-check on real cores with a real
# GIC delivering the SGI.
run_check "META" "${SCRIPT_DIR}/test_qemu_smp_wake.sh"

# SM5.D — per-core timer-tick boot test (plan §6).  SKIPs at SM5.D if the
# per-core timer driver isn't wired in the kernel image (needs SM5.I
# per-core scheduler state + the per-core ISR driving timerTickOnCore under
# withLockSet).  The tick correctness — each core advances its OWN local
# accounting without advancing the single global timer, rotates its domain,
# preempts on budget exhaustion, and fires cross-core CBS-replenish wakes —
# is established FORMALLY for all executions in tests/SmpTimerSuite.lean;
# this is a complementary runtime spot-check on real cores with a real GIC.
run_check "META" "${SCRIPT_DIR}/test_qemu_smp_timer.sh"

# SM5.F — cross-core priority-inheritance round-trip test (plan §6).  SKIPs at
# SM5.F if the cross-core PIP driver isn't wired in the kernel image (needs
# SM5.I per-core scheduler state + the IPC donation @[export] body routing
# through pipBoostWithWake + firing the SGIs over fireCrossCoreSgis).  The
# cross-core PIP correctness — a remote, runnable, material boost fires exactly
# a .reschedule SGI to the holder's home core, every remote chain link is
# poked, the global boost is the exact supremum of the per-core slices, and the
# boost happens-before the home core observes it on the SGI — is established
# FORMALLY for all executions in tests/SmpPipSuite.lean; this is a complementary
# runtime spot-check on real cores with a real GIC.
run_check "META" "${SCRIPT_DIR}/test_qemu_smp_pip.sh"

# SM5.G — per-core domain-scheduling rotation test (plan §6).  SKIPs at SM5.G if
# the per-core domain-rotation driver isn't wired in the kernel image (needs
# SM5.I's per-core scheduler tick driving scheduleDomainOnCore on each core plus a
# multi-domain schedule configured at boot).  The per-core domain-scheduling
# correctness — each core rotates its OWN domain schedule with the round-robin
# period, the active domain always lands in the schedule (preserved by the live
# tick), selection respects the active-domain barrier, and a rotation on one core
# leaves the others' selection unchanged — is established FORMALLY for all
# executions in tests/SmpDomainSuite.lean; this is a complementary runtime
# spot-check on real cores.
run_check "META" "${SCRIPT_DIR}/test_qemu_smp_domain.sh"

# WS-SM SM5.H — per-core CBS replenishment + affinity-driven thread migration.
# SKIP-only until SM5.I wires the per-core scheduler tick (driving timerTickOnCore
# on each core) plus a tcbSetAffinity-driven migration.  The per-core CBS
# correctness — each core runs its OWN replenishment queue, the live budget tick's
# replenish write IS the verified `replenishOnCore` primitive (A2) and preserves
# replenish-queue validity (A4), an affinity change migrates a thread's
# replenishments AND its run-queue entry to the new home core (restoring per-core
# CBS affinity consistency, B7/A5) and emits the cross-core SGI under the verified
# happens-before ordering (C10) — is established FORMALLY for all executions in
# tests/SmpCbsSuite.lean; this is a complementary runtime spot-check on real cores.
run_check "META" "${SCRIPT_DIR}/test_qemu_smp_cbs.sh"

# WS-SM SM5.K.5 — the 4-thread/4-core per-core scheduler acceptance test (plan §6 /
# §8).  SKIPs at SM5.K if the per-core scheduler run loop isn't wired in the kernel
# image (needs SM5.I+ driving chooseThreadOnCore / switchToThreadOnCore on each core
# plus the cross-core wake SGI firing seam).  The per-core scheduler correctness —
# each core selects + runs its OWN bound thread from its OWN run queue independently,
# a cross-core wake delivers a .reschedule SGI to the target core, the per-core idle
# thread guarantees no core stalls, and every op's WCRT under fine locks is bounded —
# is established FORMALLY for all executions in tests/SmpSchedulerSuite.lean (the
# 4-thread/4-core aggregate, 50+ scenarios + the golden trace fixture) and
# tests/SmpWcrtSuite.lean; this is a complementary runtime spot-check on real cores.
run_check "META" "${SCRIPT_DIR}/test_qemu_smp_scheduler.sh"

finalize_report
