#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-CV CV0.1 — the heap allocations of one syscall round trip.
#
# The Tier-4 driver (`rust/sele4n-hal/src/smp_exercisers.rs`,
# `heap_allocations_per_syscall`) dispatches one `NotificationSignal` through
# the syscall seam on the boot core and reads that core's own slot of the
# kernel heap's monotone allocation counter (`lean_heap.rs`,
# `allocations_by_core`) before and after, with IRQs masked across both reads.
# The number is evidence — the context-by-value plan's baseline, re-read at its
# acceptance — and no gate pins it; this gate holds only that both reads
# happened, the delta is their difference, and the round trip returned a frame
# (`scripts/qemu_exerciser_lib.sh`).
#
# The syscall is the Lean kernel's, so this gate runs on the Lean-linked image
# alone; without `--lean-kernel` it reports NOT RUN.
#
# Usage:
#   ./scripts/test_qemu_heap_allocations_per_syscall.sh --lean-kernel
#
# Exit codes:
#   0   PASS
#   77  SKIP / NOT RUN (SELE4N_SKIP_EXIT) — no `--lean-kernel`, or QEMU, cargo
#       or the cross target is missing.  REQUIRE_QEMU=1 makes an absent QEMU a
#       failure.
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

exerciser_parse_args "$@"
if [[ "${LEAN_KERNEL}" -ne 1 ]]; then
    echo "[SKIP] WS-CV CV0.1: heap allocations per syscall — NOT RUN: needs --lean-kernel"
    echo ""
    echo "  The round trip is dispatched through the Lean kernel; the HAL-only image"
    echo "  links none, so there is nothing for this gate to measure on it."
    exit "${SELE4N_SKIP_EXIT:-77}"
fi
exerciser_gate "WS-CV CV0.1" "heap allocations per syscall" heap-allocations-per-syscall --lean-kernel
