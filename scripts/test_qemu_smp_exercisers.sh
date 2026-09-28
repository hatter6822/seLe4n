#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-BP BP8.4 — every Tier-4 exerciser, from one boot.
#
# The four in-image drivers (`rust/sele4n-hal/src/smp_exercisers.rs`) run in
# one boot of the exerciser image, so this gate boots it once and holds the log
# to all four — the cross-core SGI round trip (SM1.H.5), the console stress
# (SM1.G.3), the TLB shootdown round trip (SM7.E.2) and the concurrent
# shootdown stress (SM7.E.3) — and to the image's own tally, `4 passed, 0
# failed`.  The per-driver gates `test_qemu_smp_{sgi_roundtrip,kprintln_stress,
# shootdown,shootdown_stress}.sh` read the same drivers one at a time; this is
# the one the Lean archive lane runs on every PR, with `--lean-kernel` and
# `REQUIRE_QEMU=1`, so the two shootdown exercisers execute on the kernel the
# image ships (`docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` §8).
#
# Usage:
#   ./scripts/test_qemu_smp_exercisers.sh                 # the HAL-only exerciser image
#   ./scripts/test_qemu_smp_exercisers.sh --lean-kernel   # the Lean-linked one
#
# Exit codes:
#   0   PASS
#   77  SKIP / NOT RUN (SELE4N_SKIP_EXIT) — QEMU, cargo or the cross target is
#       missing, so this gate certified nothing.  REQUIRE_QEMU=1 makes an absent
#       QEMU a failure.
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

exerciser_gate "WS-BP BP8.4" "the Tier-4 exercisers" all "$@"
