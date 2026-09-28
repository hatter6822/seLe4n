#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-BP BP8.5 — the per-core counters read on the booted machine.
#
# `Concurrency.perCoreStats` reads a core's four counters through the HAL's
# accessors and `perCoreStatsPlausible` states their containment; both were
# proved and runtime-checked, and until this gate executed on no machine.  The
# Tier-4 driver (`rust/sele4n-hal/src/smp_exercisers.rs`, `per_core_stats`)
# reads every core's snapshot through the Lean seam `lean_per_core_stats_component`
# on the boot core, after every declared PE serves the kernel, between two
# Rust reads of the same slot, and the check (`scripts/qemu_exerciser_lib.sh`)
# re-derives the relations from the words the seam reported: the verdict is
# `1` and the words it was decided on satisfy it, every serving core reports a
# tick and an IRQ, every word lies inside its slot's bracket — a word outside
# it was read off another core's slot — and the four slots are told apart by
# their SGI counts.
#
# The reader and the verdict are the Lean kernel's, so this gate runs on the
# Lean-linked image alone; without `--lean-kernel` it reports NOT RUN.
#
# Usage:
#   ./scripts/test_qemu_smp_per_core_stats.sh --lean-kernel
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
    echo "[SKIP] WS-BP BP8.5: per-core counters on the booted machine — NOT RUN: needs --lean-kernel"
    echo ""
    echo "  The reader (Concurrency.perCoreStats) and the verdict (perCoreStatsPlausible)"
    echo "  are the Lean kernel's; the HAL-only image links neither, so there is nothing"
    echo "  for this gate to execute on it."
    exit "${SELE4N_SKIP_EXIT:-77}"
fi
exerciser_gate "WS-BP BP8.5" "per-core counters on the booted machine" per-core-stats --lean-kernel
