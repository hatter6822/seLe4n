#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AL0-A (WS-AL / v1.0.0 cascade closure): baseline-metrics capture script.
#
# Emits one `METRIC:VALUE` line per tracked metric. Used by AL0-B to
# produce `docs/audits/AL0_baseline.txt` and by AL0-C
# (check_monotonic.sh) to detect regressions in subsequent WS-AL
# commits.
#
# Exit codes:
#   0 — all metrics emitted successfully
#   1 — tool dependency missing (rg / lake / cargo)
#
# See docs/audits/AUDIT_v0.29.0_DEFERRED.md § "AK7 cascade resolution"
# and the WS-AL workstream plan.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

# Tool dependency check
for tool in rg grep awk wc; do
  if ! command -v "${tool}" >/dev/null 2>&1; then
    echo "ERROR: missing required tool: ${tool}" >&2
    exit 1
  fi
done

# --- Raw kind-destructuring patterns (target: decrease) ------------------
# Uses `rg -g '*.lean'` (correct glob flag; `--include` is a grep-only flag).
# `rg` enables regex by default — the `-E` short-flag is `--encoding` in
# rg (not "extended regex" like grep); don't pass it.
# Sums per-file counts into a single repo-wide total.
rg_count() {
  rg -c "$1" -g '*.lean' SeLe4n/ 2>/dev/null \
    | awk -F: '{s+=$2} END {print s+0}'
}

# rg_count_excl_helpers — like rg_count but excludes files that by
# definition contain the raw pattern (AL2-A helper definitions in
# SeLe4n/Model/State.lean). Counted metrics using this exclusion reflect
# only CALLER use of the raw pattern, which is what the cascade removes.
rg_count_excl_helpers() {
  rg -c "$1" -g '*.lean' \
    -g '!SeLe4n/Model/State.lean' \
    SeLe4n/ 2>/dev/null \
    | awk -F: '{s+=$2} END {print s+0}'
}

# Excl-helpers variant: RAW_MATCH_* and RAW_LOOKUP_* metrics track
# *caller* use of the raw pattern, not the helper-definition bodies
# (which, by design, contain the pattern exactly once). `SeLe4n/Model/
# State.lean` is excluded because it holds the AL2-A getX? definitions.
echo "RAW_MATCH_TCB:$(rg_count_excl_helpers 'some \(\.tcb')"
echo "RAW_MATCH_SCHEDCTX:$(rg_count_excl_helpers 'some \(\.schedContext')"
echo "RAW_MATCH_ENDPOINT:$(rg_count_excl_helpers 'some \(\.endpoint')"
echo "RAW_MATCH_NOTIFICATION:$(rg_count_excl_helpers 'some \(\.notification')"
echo "RAW_MATCH_CNODE:$(rg_count_excl_helpers 'some \(\.cnode')"
echo "RAW_MATCH_VSPACEROOT:$(rg_count_excl_helpers 'some \(\.vspaceRoot')"
echo "RAW_MATCH_UNTYPED:$(rg_count_excl_helpers 'some \(\.untyped')"

# --- Raw lookup patterns (target: decrease) ------------------------------
echo "RAW_LOOKUP_TID:$(rg_count_excl_helpers '\.get\? *tid\.toObjId|\[tid\.toObjId\]')"
echo "RAW_LOOKUP_SCID:$(rg_count_excl_helpers '\.get\? *scId\.toObjId|\[scId\.toObjId\]')"

# --- Helper adoption (target: increase) ----------------------------------
echo "GETTCB_ADOPTION:$(rg_count 'getTcb\?')"
echo "GETSCHEDCTX_ADOPTION:$(rg_count 'getSchedContext\?')"
echo "SENTINEL_CHECK_DISPATCH:$(rg -c 'validateThreadIdArg|validateSchedContextIdArg|validateObjIdArg' SeLe4n/Kernel/API.lean 2>/dev/null || echo 0)"
echo "REQUIRE_NOT_NULL_CSPACE:$(rg -c 'requireNotNull' SeLe4n/Kernel/Capability/Operations.lean 2>/dev/null || echo 0)"

# --- Safety invariants (target: zero) ------------------------------------
echo "SORRY_COUNT:$(rg_count '\bsorry\b')"
echo "AXIOM_COUNT:$(rg_count '^axiom\s|\baxiom\s')"

# --- Build health (target: increase or hold) -----------------------------
if [[ "${AL0_SKIP_BUILD:-0}" != "1" ]] && command -v lake >/dev/null 2>&1; then
  # shellcheck disable=SC1090
  source "${HOME}/.elan/env" 2>/dev/null || true
  # Lake emits two possible outputs:
  #   1. incremental: no-op summary line "Build completed successfully (N jobs)."
  #   2. full rebuild: per-task "✔ [k/N] Built ..." lines + summary line.
  # Parse the summary for the authoritative job count; fall back to 0 on
  # failure to build.
  BUILD_OUT=$(lake build 2>&1)
  LAKE_JOBS=$(printf '%s\n' "${BUILD_OUT}" \
    | grep -oE 'Build completed successfully \([0-9]+ jobs\)' \
    | grep -oE '[0-9]+' || echo 0)
  echo "LAKE_JOBS:${LAKE_JOBS:-0}"
else
  echo "LAKE_JOBS:SKIPPED"
fi

if [[ "${AL0_SKIP_AK7:-0}" != "1" ]] && command -v lake >/dev/null 2>&1; then
  AK7_CHECKS=$(lake exe ak7_regression_suite 2>/dev/null \
    | grep -c 'ak7 check passed' || true)
  echo "TEST_COUNT_AK7:${AK7_CHECKS}"
else
  echo "TEST_COUNT_AK7:SKIPPED"
fi

if [[ "${AL0_SKIP_CARGO:-0}" != "1" ]] && [[ -d rust ]] && command -v cargo >/dev/null 2>&1; then
  CARGO=$( (cd rust && cargo test --workspace 2>&1) \
    | grep -E '^test result' \
    | awk '{s+=$4} END {print s+0}')
  echo "CARGO_TESTS:${CARGO}"
else
  echo "CARGO_TESTS:SKIPPED"
fi
