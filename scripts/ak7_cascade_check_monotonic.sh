#!/usr/bin/env bash
# AK7 cascade monotonicity gate (AN10-D, restored from AL0).
#
# Re-introduced by WS-AN Phase AN10. Reads the post-AN10 floors from
# `docs/audits/AL0_baseline.txt` (KEY=value format produced by
# `scripts/ak7_cascade_baseline.sh`). For every metric, enforces the
# direction the AK7 cascade is supposed to drive:
#   * SHOULD-DROP: current value MUST be ≤ baseline floor.
#                  Regression means the migration regressed (a previously
#                  hygienized site re-introduced the raw pattern).
#   * SHOULD-GROW: current value MUST be ≥ baseline floor.
#                  Regression means a typed-helper consumer reverted to the
#                  raw pattern, or a `storeObjectKindChecked` site reverted
#                  to bare `storeObject`.
#
# When all metrics pass, exit 0. When any metric fails, exit 1 with a
# per-metric diagnostic.
#
# Wired into `scripts/test_tier0_hygiene.sh` so every commit is gated.
#
# To re-anchor the baseline (after AN10 close, or after each subsequent
# WS-AN-style hygiene push):
#   bash scripts/ak7_cascade_baseline.sh > docs/audits/AL0_baseline.txt

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

BASELINE_FILE="docs/audits/AL0_baseline.txt"

if [[ ! -f "$BASELINE_FILE" ]]; then
  echo "[ak7-monotonicity] Baseline not found: $BASELINE_FILE" >&2
  echo "[ak7-monotonicity] Run: bash scripts/ak7_cascade_baseline.sh > $BASELINE_FILE" >&2
  exit 1
fi

# Capture current state via the baseline script.
CURRENT_FILE=$(mktemp)
trap 'rm -f "$CURRENT_FILE"' EXIT
bash scripts/ak7_cascade_baseline.sh > "$CURRENT_FILE"

read_metric() {
  local key="$1"
  local file="$2"
  local v
  v=$(grep "^${key}=" "$file" 2>/dev/null | head -1 | cut -d= -f2 || true)
  if [[ -z "$v" ]]; then
    echo 0
  else
    echo "$v"
  fi
}

# (metric, direction) pairs: direction is "drop" or "grow".
METRICS=(
  "RAW_MATCH_TCB:drop"
  "RAW_MATCH_SCHEDCONTEXT:drop"
  "RAW_MATCH_ENDPOINT:drop"
  "RAW_MATCH_NOTIFICATION:drop"
  "RAW_MATCH_UNTYPED:drop"
  "RAW_MATCH_CNODE:drop"
  "RAW_MATCH_VSPACEROOT:drop"
  "RAW_MATCH_TOTAL:drop"
  "RAW_LOOKUP_TID:drop"
  "GETTCB_ADOPTION:grow"
  "GETSCHEDCTX_ADOPTION:grow"
  "GETENDPOINT_ADOPTION:grow"
  "GETNOTIFICATION_ADOPTION:grow"
  "GETUNTYPED_ADOPTION:grow"
  "GETCNODE_ADOPTION:grow"
  "GETVSPACEROOT_ADOPTION:grow"
  "STOREOBJECTCHECKED_ADOPTION:grow"
  "SENTINEL_CHECK_DISPATCH:grow"
  "TEST_COUNT_AK7:grow"
)

# SORRY/AXIOM are zero-floor (any positive value is a regression).
ZERO_METRICS=(
  "SORRY_COUNT"
  "AXIOM_COUNT"
)

failed=0
echo "[ak7-monotonicity] Checking AK7 cascade metrics against $BASELINE_FILE"

for entry in "${METRICS[@]}"; do
  metric="${entry%:*}"
  direction="${entry##*:}"
  baseline=$(read_metric "$metric" "$BASELINE_FILE")
  current=$(read_metric "$metric" "$CURRENT_FILE")
  case "$direction" in
    drop)
      if (( current > baseline )); then
        echo "  REGRESSION (should-drop): $metric  current=$current  baseline=$baseline" >&2
        failed=1
      else
        echo "  OK   $metric  ${current} <= ${baseline}"
      fi
      ;;
    grow)
      if (( current < baseline )); then
        echo "  REGRESSION (should-grow): $metric  current=$current  baseline=$baseline" >&2
        failed=1
      else
        echo "  OK   $metric  ${current} >= ${baseline}"
      fi
      ;;
  esac
done

for metric in "${ZERO_METRICS[@]}"; do
  current=$(read_metric "$metric" "$CURRENT_FILE")
  if (( current > 0 )); then
    echo "  REGRESSION (should-stay-zero): $metric  current=$current" >&2
    failed=1
  else
    echo "  OK   $metric  0"
  fi
done

if (( failed != 0 )); then
  echo "" >&2
  echo "[ak7-monotonicity] One or more AK7 cascade metrics regressed." >&2
  echo "[ak7-monotonicity] Either restore the value (preferred) or, after a" >&2
  echo "[ak7-monotonicity] documented refactor, re-anchor the baseline:" >&2
  echo "  bash scripts/ak7_cascade_baseline.sh > $BASELINE_FILE" >&2
  exit 1
fi

echo "[ak7-monotonicity] All AK7 cascade metrics pass."
