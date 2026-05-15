#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM0.T — Tier-4 SMP boot-check (extension-point STUB at SM0).
#
# This script reserves the tier-4 slot for the SMP boot-check evidence
# that later WS-SM phases populate:
#
#   * SM1.H — QEMU `-smp 4` bring-up trace + per-core ready flag check
#   * SM5.K — per-core scheduler liveness probe
#   * SM6.F — cross-core IPC handshake exerciser
#   * SM7.E — TLB shootdown ACK timing
#   * SM8.E — information flow non-interference under SMP
#
# At SM0 the script exits 0 with a SKIP marker — the slot is reserved,
# nothing to verify yet (no SMP code path is exercised at runtime;
# `SMP_ENABLED = false` keeps the kernel single-core and the SM0
# evidence is in `tests/SmpFoundationsSuite.lean` instead).
#
# Wired into `scripts/test_tier4_nightly_candidates.sh` so a future
# CI run that flips `NIGHTLY_ENABLE_EXPERIMENTAL=1` will exercise the
# (later phases') populated checks.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

log_section "META" "WS-SM tier-4 SMP boot-check stub (SM0)"
log_section "META" "  Populated by SM1.H..SM8.E as those phases land."
log_section "META" "  At SM0 the SMP runtime path is gated by SMP_ENABLED=false;"
log_section "META" "  evidence for SM0 itself lives in tests/SmpFoundationsSuite.lean"
log_section "META" "  (run via 'lake exe smp_foundations_suite')."

finalize_report
