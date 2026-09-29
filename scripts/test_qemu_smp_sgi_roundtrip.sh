#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM1.H.5 / WS-BP BP8.4 — cross-core SGI round trip.
#
# The boot core sends the agent SGI (INTID 15) to each secondary in turn.  The
# secondary's handler prints the SGI's arrival with the GIC's attribution of
# the source core, answers with an SGI of its own into the boot core's command
# slot, and the boot core's handler prints the acknowledgment; the per-core SGI
# counters move on both ends.  What the log must carry, per secondary: the
# send, the arrival attributed to core 0, the acknowledgment attributed to the
# secondary, and both counters up by at least one.
#
# Driver: `smp_exercisers::sgi_round_trip` (`rust/sele4n-hal/src/smp_exercisers.rs`,
# compiled into the test image alone).  The boot, the image and what the log
# must say are `scripts/qemu_exerciser_lib.sh`'s, shared by every exerciser
# gate; the four drivers run in one boot and this gate reads its own.
#
# Until WS-BP BP8.4 this gate SKIPped on every run: it asked for a kernel ELF no
# target built and looked for its banner in that image with `strings`.
#
# Usage:
#   ./scripts/test_qemu_smp_sgi_roundtrip.sh                 # the HAL-only exerciser image
#   ./scripts/test_qemu_smp_sgi_roundtrip.sh --lean-kernel   # the Lean-linked one
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

exerciser_gate "WS-SM SM1.H.5 / WS-BP BP8.4" "cross-core SGI round trip" sgi-round-trip "$@"
