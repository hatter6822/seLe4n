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

finalize_report
