#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM1.G.3 / WS-BP BP8.4 — cross-core console stress.
#
# Every core prints 32 lines at once through `kprintln_core!` — the three
# secondaries from their agent SGI handlers, the boot core from its own bring-up
# tail — so four writers contend for the console's ticket lock.  What the log
# must carry: for every core, exactly the iterations 0..31 once each as whole
# `[core N] stress iter I` lines, and no line torn by another core's.
#
# Driver: `smp_exercisers::kprintln_stress` (`rust/sele4n-hal/src/smp_exercisers.rs`,
# compiled into the test image alone).  The boot, the image and what the log
# must say are `scripts/qemu_exerciser_lib.sh`'s, shared by every exerciser
# gate; the four drivers run in one boot and this gate reads its own.
#
# Until WS-BP BP8.4 this gate SKIPped on every run: it asked for a kernel ELF no
# target built and looked for its banner in that image with `strings`.
#
# Usage:
#   ./scripts/test_qemu_smp_kprintln_stress.sh                 # the HAL-only exerciser image
#   ./scripts/test_qemu_smp_kprintln_stress.sh --lean-kernel   # the Lean-linked one
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

exerciser_gate "WS-SM SM1.G.3 / WS-BP BP8.4" "cross-core console stress" kprintln-stress "$@"
