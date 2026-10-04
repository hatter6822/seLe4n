#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM0.T → SM1.H → WS-BP BP8.4 — the Tier-4 SMP acceptance gates.
#
# Reserved at SM0 as a SKIP-only stub and populated through SM1.G/H, SM3.D,
# SM5, SM6 and SM7, every gate here SKIPped on every run until WS-BP BP8.2 (the
# bring-up) and BP8.4 (the rest): each asked for a kernel ELF no target built
# and looked for its driver's banner in it with `strings`.  Since BP8.4:
#
# * The six gates that need no user program — the four-PE bring-up, the
#   PE-withheld boot, the cross-core SGI round trip, the console stress and
#   the two TLB shootdown exercisers — boot the `virt` image
#   `scripts/qemu_boot_lib.sh` builds and report a result: on the HAL-only
#   image always, and on the Lean-linked image too when the archive
#   `scripts/test_lean_aarch64_archive.sh` builds is present.  Without the
#   archive the Lean-linked half is recorded NOT RUN, never silently omitted.
# * The eight gates that need a user-level driver program report NOT RUN with
#   that reason (`exerciser_user_program_gate`): the image carries no user
#   program until SM10's root task.
#
# A gate that cannot run exits `SELE4N_SKIP_EXIT` and is invoked through
# `run_gate_check`, which records it as NOT RUN — never as PASS.  A bare
# environment therefore reports how many acceptance gates did not execute
# instead of printing "All checks passed" over work nothing performed.
#
# `SELE4N_REQUIRE_GATES=1` promotes any skipped gate to a hard failure; that is
# the mode the v1.0.0 release validation (SM10.5) must run in, since a release
# may not certify phases whose gates never ran.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

LEAN_ARCHIVE="${REPO_ROOT}/.lake/build/aarch64-unknown-none-softfloat/libsele4n.a"

log_section "META" "WS-SM tier-4 SMP acceptance gates (executable since WS-BP BP8.2/BP8.4)"
log_section "META" "  A gate that cannot run is reported NOT RUN, never PASS."

LEAN_MODE=0
if [[ -f "${LEAN_ARCHIVE}" ]]; then
    LEAN_MODE=1
    log_section "META" "  Lean archive present: every executable gate also runs on the Lean-linked image."
else
    record_skip "META" "the Lean-linked runs of the executable gates: no archive at ${LEAN_ARCHIVE} (run scripts/test_lean_aarch64_archive.sh first)"
fi

# gate SCRIPT: run an executable gate on the HAL-only image, and on the
# Lean-linked one when the archive is present.
gate() {
    run_gate_check "META" "${SCRIPT_DIR}/$1"
    if [[ "${LEAN_MODE}" -eq 1 ]]; then
        run_gate_check "META" "${SCRIPT_DIR}/$1" --lean-kernel
    fi
}

# gate_lean_only SCRIPT: a gate whose subject is the Lean kernel's, so it runs
# on the Lean-linked image alone and is NOT RUN without the archive.
gate_lean_only() {
    if [[ "${LEAN_MODE}" -eq 1 ]]; then
        run_gate_check "META" "${SCRIPT_DIR}/$1" --lean-kernel
    else
        record_skip "META" "$1 --lean-kernel: needs the Lean-linked image (no archive at ${LEAN_ARCHIVE})"
    fi
}

# SM1.H.1 / WS-BP BP8.2 — the four-PE bring-up, at EL1 and EL2.
gate test_qemu_smp_bringup.sh

# SM1.H.3 / WS-BP BP6.3 — the PE-withheld boot: the HAL-only image boots on
# two PEs, the Lean-linked one refuses them.
gate test_qemu_smp_minimal.sh

# SM1.H.5 — the cross-core SGI round trip.
gate test_qemu_smp_sgi_roundtrip.sh

# SM1.G.3 — the cross-core console stress.
gate test_qemu_smp_kprintln_stress.sh

# SM7.E.2 — the cross-core TLB shootdown round trip through the live protocol.
# The shootdown correctness is established FORMALLY for all executions in
# tests/SmpTlbShootdownSuite.lean; this is its runtime witness on emulated
# cores, and the run that decides WS-SM SM7 §8's acceptance box.
gate test_qemu_smp_shootdown.sh

# SM7.E.3 — four concurrent initiators, eight generations: the round lock's
# serialisation and the acknowledgment under contention.
gate test_qemu_smp_shootdown_stress.sh

# WS-BP BP8.5 — the per-core counters read through the Lean seam on the booted
# machine: `Concurrency.perCoreStats` executed on every core and
# `perCoreStatsPlausible` decided there, each word held inside the bracket of
# two Rust reads of the same slot.  The reader and the verdict are the kernel's,
# so the Lean-linked image alone.
gate_lean_only test_qemu_smp_per_core_stats.sh

# The gates that need a user program: each reports NOT RUN with its reason.
# SM3.D.7 — cross-core deadlock-freedom stress (formal:
# tests/DeadlockFreedomSuite.lean).
run_gate_check "META" "${SCRIPT_DIR}/test_qemu_smp_deadlock_stress.sh"
# SM5.C.12 — cross-core wake via SGI (formal: tests/SmpWakeSuite.lean).
run_gate_check "META" "${SCRIPT_DIR}/test_qemu_smp_wake.sh"
# SM5.D — per-core timer tick (formal: tests/SmpTimerSuite.lean).
run_gate_check "META" "${SCRIPT_DIR}/test_qemu_smp_timer.sh"
# SM5.F.10 — cross-core priority inheritance (formal: tests/SmpPipSuite.lean).
run_gate_check "META" "${SCRIPT_DIR}/test_qemu_smp_pip.sh"
# SM5.G.6 — per-core domain rotation (formal: tests/SmpDomainSuite.lean).
run_gate_check "META" "${SCRIPT_DIR}/test_qemu_smp_domain.sh"
# SM5.H — per-core CBS replenishment and migration (formal:
# tests/SmpCbsSuite.lean).
run_gate_check "META" "${SCRIPT_DIR}/test_qemu_smp_cbs.sh"
# SM5.K.5 — four threads on four cores (formal: tests/SmpSchedulerSuite.lean,
# tests/SmpWcrtSuite.lean).
run_gate_check "META" "${SCRIPT_DIR}/test_qemu_smp_scheduler.sh"
# SM6.F.5 — the cross-core IPC handshake (formal: tests/SmpIpcSuite.lean,
# tests/SmpNotificationSuite.lean).
run_gate_check "META" "${SCRIPT_DIR}/test_qemu_smp_ipc.sh"

finalize_report
