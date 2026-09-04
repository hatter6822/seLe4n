#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"

sub_args=()
if [[ "${CONTINUE_MODE}" -eq 1 ]]; then
  sub_args+=("--continue")
fi

run_check "META" "${SCRIPT_DIR}/test_full.sh" "${sub_args[@]}"
run_gate_check "META" "${SCRIPT_DIR}/test_tier4_nightly_candidates.sh" "${sub_args[@]}"
if [[ "${NIGHTLY_ENABLE_EXPERIMENTAL:-0}" == "1" ]]; then
  log_section "INVARIANT" "Tier 4 staged candidates executed (NIGHTLY_ENABLE_EXPERIMENTAL=1)."
  # WS-SM SM2.C-defer D-6: Tier 5 cross-language correspondence harness.
  # Compares Lean oracle vs. Rust oracle output on ≥NUM_SEQUENCES op-sequences.
  # See docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md §5.6.
  run_check "META" "${SCRIPT_DIR}/test_tier5_cross_language.sh"
  log_section "INVARIANT" "Tier 5 cross-language correspondence harness executed."
  # WS-RR RR6.21: miri over the deployed reader-writer lock.  Nightly
  # rather than per-PR because miri interprets every atomic access and
  # is roughly three orders of magnitude slower than a native run; the
  # loom gate (per-PR, `.github/workflows/lean_action_ci.yml`) covers
  # the interleavings, and miri covers undefined behaviour, data races
  # and provenance.  See SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md §8 (D-5).
  run_check "META" "${SCRIPT_DIR}/test_miri_queued_rw_lock.sh"
  log_section "INVARIANT" "miri gate executed over the deployed queued RwLock."
else
  log_section "INVARIANT" "Tier 4 keeps an explicit extension-point default; set NIGHTLY_ENABLE_EXPERIMENTAL=1 to run staged candidates."
fi

finalize_report
