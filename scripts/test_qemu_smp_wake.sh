#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM5.C.12 (plan §6 Tier-4) — cross-core wake-via-SGI round trip.
#
# Boots QEMU `-smp 4` and requires the banner
#   [smp-test] cross-core-wake: woken thread dispatched on target
# — which the image cannot print yet.  The gate needs
# a thread on one core blocked in a receive and woken by a thread on another
# through the live syscall seam, so the wake's `.reschedule` SGI and the
# target core's dispatch are observed on a real GIC, and the kernel
# image carries no user program: the two initial threads WS-BP BP7.11 starts
# run no code, and a user program is SM10's root task.  Until it exists this
# gate reports NOT RUN with that reason, through
# `scripts/qemu_exerciser_lib.sh`'s `exerciser_user_program_gate`, rather
# than looking for the banner in the image with `strings` — which is what it
# did until WS-BP BP8.4, against a kernel ELF no target built.  Registered:
# `docs/REGISTERED_DEBT.md` (WS-BP).
#
# The property is established for every execution, machine-checked, by
# tests/SmpWakeSuite.lean (Tier 2/3); this gate is its runtime spot-check on emulated cores.
#
# Exit codes:
#   77  NOT RUN (SELE4N_SKIP_EXIT) until the root task exists; `run_gate_check`
#       records it, and SELE4N_REQUIRE_GATES=1 makes it a failure.
#   0   PASS / 1 FAIL, once the driver program exists.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"
cd "${REPO_ROOT}"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/qemu_exerciser_lib.sh"

exerciser_user_program_gate "WS-SM SM5.C.12 (plan §6 Tier-4)" "cross-core wake-via-SGI round trip" "tests/SmpWakeSuite.lean" \
    "[smp-test] cross-core-wake: woken thread dispatched on target"
