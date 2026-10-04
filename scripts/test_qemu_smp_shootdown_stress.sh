#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM7.E.3 / WS-BP BP8.4 — concurrent TLB shootdown stress.
#
# Eight generations of four concurrent initiators: at each, every core remaps
# its own window page through a shootdown round of its own — the secondaries
# from their agent SGI handlers, the boot core from its bring-up tail — so four
# initiators contend for the round lock at once, and the waiters self-service
# the round in flight as the seam's cooperative acquire does; then every core
# reads every page and reports any stale translation.  What the log must
# carry: every core completing generations 2..9 (32 rounds), the 32 rounds
# carrying 32 distinct generations — one per round, which is what the round
# lock serialising them means — no stale translation, and the completion
# banner.  A second initiator inside the critical section is reported by the
# in-flight witness (`RoundOutcome::SerialisationBroken`) and fails this gate:
# the shootdown-round-serialisation break WS-SM SM7 §8 names as a failure of
# SM7.
#
# Driver: `smp_exercisers::shootdown_stress` (`rust/sele4n-hal/src/smp_exercisers.rs`,
# compiled into the test image alone).  The boot, the image and what the log
# must say are `scripts/qemu_exerciser_lib.sh`'s, shared by every exerciser
# gate; the four drivers run in one boot and this gate reads its own.
#
# Until WS-BP BP8.4 this gate SKIPped on every run: it asked for a kernel ELF no
# target built and looked for its banner in that image with `strings`.
#
# Usage:
#   ./scripts/test_qemu_smp_shootdown_stress.sh                 # the HAL-only exerciser image
#   ./scripts/test_qemu_smp_shootdown_stress.sh --lean-kernel   # the Lean-linked one
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

exerciser_gate "WS-SM SM7.E.3 / WS-BP BP8.4" "concurrent TLB shootdown stress" tlb-shootdown-stress "$@"
