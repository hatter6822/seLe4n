#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AL0-C (WS-AL / v1.0.0 cascade closure): monotonicity regression guard.
#
# Compares the current `ak7_cascade_baseline.sh` output against
# `docs/audits/AL0_baseline.txt` and enforces per-metric direction:
#
#   DECREASE-OR-EQUAL (should-drop) metrics:
#     RAW_MATCH_*   — raw kind-destructuring patterns (AK7-F cascade)
#     RAW_LOOKUP_*  — raw toObjId lookup sites (AK7-F cascade)
#     SORRY_COUNT   — always 0
#     AXIOM_COUNT   — always 0
#
#   INCREASE-OR-EQUAL (should-grow) metrics:
#     GETTCB_ADOPTION, GETSCHEDCTX_ADOPTION — kind-verified helper use
#     SENTINEL_CHECK_DISPATCH — toValid? calls at dispatch (AK7-E)
#     REQUIRE_NOT_NULL_CSPACE — null-cap guards (AK7-I)
#     TEST_COUNT_AK7  — runtime suite size
#     LAKE_JOBS       — build job count (catches accidental module deletion)
#     CARGO_TESTS     — Rust test count
#
# Exit codes:
#   0 — all metrics within bounds
#   1 — at least one metric regressed
#   2 — baseline file missing or baseline tool failed
#
# Wired into scripts/test_tier0_hygiene.sh by AL0-D.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

BASELINE="docs/audits/AL0_baseline.txt"
if [[ ! -f "${BASELINE}" ]]; then
  echo "ERROR: missing baseline file ${BASELINE}" >&2
  echo "       Run: ./scripts/ak7_cascade_baseline.sh > ${BASELINE}" >&2
  exit 2
fi

# Capture current metrics.
CURRENT=$("${SCRIPT_DIR}/ak7_cascade_baseline.sh") || {
  echo "ERROR: baseline capture failed" >&2
  exit 2
}

# --- Metric direction tables --------------------------------------------
# Should-drop: current value must be ≤ baseline value.
DROP_METRICS="RAW_MATCH_TCB RAW_MATCH_SCHEDCTX RAW_MATCH_ENDPOINT
RAW_MATCH_NOTIFICATION RAW_MATCH_CNODE RAW_MATCH_VSPACEROOT
RAW_MATCH_UNTYPED RAW_LOOKUP_TID RAW_LOOKUP_SCID
SORRY_COUNT AXIOM_COUNT"

# Should-grow: current value must be ≥ baseline value.
GROW_METRICS="GETTCB_ADOPTION GETSCHEDCTX_ADOPTION
SENTINEL_CHECK_DISPATCH REQUIRE_NOT_NULL_CSPACE
TEST_COUNT_AK7 LAKE_JOBS CARGO_TESTS"

# --- Lookup helpers -----------------------------------------------------
get_metric() {
  local file_or_text="$1" metric="$2"
  if [[ -f "${file_or_text}" ]]; then
    awk -F: -v m="${metric}" '$1==m {print $2; exit}' "${file_or_text}"
  else
    printf '%s\n' "${file_or_text}" | awk -F: -v m="${metric}" '$1==m {print $2; exit}'
  fi
}

FAIL=0

check_direction() {
  local metric="$1" direction="$2"
  local cur base
  cur=$(get_metric "${CURRENT}" "${metric}")
  base=$(get_metric "${BASELINE}" "${metric}")

  # SKIPPED is a legal value; don't regression-check it.
  [[ "${cur}" == "SKIPPED" || "${base}" == "SKIPPED" ]] && return 0
  # Missing metric on either side means a drift the script-owner must fix.
  if [[ -z "${cur}" || -z "${base}" ]]; then
    echo "WARN: metric ${metric} missing (cur='${cur}' base='${base}')" >&2
    return 0
  fi

  case "${direction}" in
    drop)
      if (( cur > base )); then
        echo "FAIL: ${metric} regressed: ${base} -> ${cur} (must decrease or hold)" >&2
        FAIL=1
      fi
      ;;
    grow)
      if (( cur < base )); then
        echo "FAIL: ${metric} regressed: ${base} -> ${cur} (must increase or hold)" >&2
        FAIL=1
      fi
      ;;
  esac
}

for m in ${DROP_METRICS}; do check_direction "${m}" drop; done
for m in ${GROW_METRICS}; do check_direction "${m}" grow; done

if [[ "${FAIL}" -eq 1 ]]; then
  echo "FAIL: ak7 cascade monotonicity check failed" >&2
  exit 1
fi

echo "PASS: ak7 cascade monotonicity check (baseline: ${BASELINE})"
exit 0
