#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM7.E.2 / WS-BP BP8.4 — cross-core TLB shootdown round trip.
#
# Core 1 translates core 0's window page (priming its TLB); core 0 remaps the
# page break-before-make through one shootdown round — the round lock, the
# generation, the published operand, the `.tlbShootdownReq` SGIs, the broadcast
# invalidation and the bounded wait for every target's acknowledgment, in the
# order the Lean seam `completeShootdownRounds` runs them; core 1 reads the page
# again and must see the new backing page.  What the log must carry: the round
# complete, every secondary's acknowledged generation at or above the round's,
# and the stale translation removed.  A round mutated to invalidate locally
# leaves core 1 reading the old page, which is how the probe was shown decisive.
# A missing acknowledgment times the round out, which halts the system
# fail-closed as the seam does, and the FATAL line fails this gate: that, and a
# serialisation break, are failures of SM7, not of the harness
# (`docs/dev_history/planning/SMP_TLB_SHOOTDOWN_PLAN.md` §8).
#
# Driver: `smp_exercisers::shootdown_round_trip` (`rust/sele4n-hal/src/smp_exercisers.rs`,
# compiled into the test image alone).  The boot, the image and what the log
# must say are `scripts/qemu_exerciser_lib.sh`'s, shared by every exerciser
# gate; the four drivers run in one boot and this gate reads its own.
#
# Until WS-BP BP8.4 this gate SKIPped on every run: it asked for a kernel ELF no
# target built and looked for its banner in that image with `strings`.
#
# Usage:
#   ./scripts/test_qemu_smp_shootdown.sh                 # the HAL-only exerciser image
#   ./scripts/test_qemu_smp_shootdown.sh --lean-kernel   # the Lean-linked one
#
# Exit codes:
#   0   PASS
#   77  SKIP / NOT RUN (SELE4N_SKIP_EXIT) — QEMU, cargo or the cross target is
#       missing, so this gate certified nothing; `run_gate_check` records it
#       as NOT RUN.  REQUIRE_QEMU=1 makes an absent QEMU a failure.
#   1   FAIL

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"
cd "${REPO_ROOT}"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/qemu_boot_lib.sh"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/qemu_exerciser_lib.sh"

exerciser_gate "WS-SM SM7.E.2 / WS-BP BP8.4" "cross-core TLB shootdown round trip" tlb-shootdown "$@"
