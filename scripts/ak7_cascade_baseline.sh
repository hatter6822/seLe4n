#!/usr/bin/env bash
# AK7 cascade monotonicity baseline capture (AN10-D, restored from AL0).
#
# Re-introduced by WS-AN Phase AN10 (DEF-AK7-E.cascade / DEF-AK7-F.reader.hygiene
# / DEF-AK7-F.writer.hygiene closure) to track residual hygiene migration:
#   * `RAW_MATCH_*`         — raw `match st.objects[id]?` patterns by variant.
#                             SHOULD-DROP metric (every commit ≤ baseline floor).
#   * `RAW_LOOKUP_TID`      — bare `tid.toObjId` lookup at object store.
#                             SHOULD-DROP metric.
#   * `GETTCB_ADOPTION`,
#     `GETSCHEDCTX_ADOPTION` — typed-helper call sites in production / tests.
#                             SHOULD-GROW metric (every commit ≥ baseline floor).
#   * `STOREOBJECTCHECKED_ADOPTION`
#                           — `storeObjectKindChecked` consumer sites.
#                             SHOULD-GROW metric.
#   * `SENTINEL_CHECK_DISPATCH`
#                           — production dispatch sites guarded by
#                             `validateThreadIdArg` / `validateSchedContextIdArg`
#                             / `validateObjIdArg`. SHOULD-GROW metric.
#   * `TEST_COUNT_AK7`      — `tests/An10CascadeSuite.lean` test count.
#                             SHOULD-GROW metric.
#
# All counts exclude `SeLe4n/Model/State.lean` (the helper definition file
# itself, which retains the discriminator pattern by design — once per
# variant) and `docs/dev_history/` archived material.
#
# Output: human-readable report on stdout; KEY=VALUE machine-diffable
# block at the bottom (mirrors AN0-A baseline format).
#
# Usage:
#   scripts/ak7_cascade_baseline.sh         # print baseline at HEAD
#   scripts/ak7_cascade_check_monotonic.sh  # gate: enforce floors

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

# Build the list of kernel proof-surface files exactly once (excluding the
# helper definition file `Model/State.lean`).
KERNEL_FILES=()
while IFS= read -r f; do
  KERNEL_FILES+=("$f")
done < <(find SeLe4n/Kernel -type f -name "*.lean")

ALL_FILES=("${KERNEL_FILES[@]}")
TEST_FILES=()
while IFS= read -r f; do
  TEST_FILES+=("$f")
done < <(find tests SeLe4n/Testing Main.lean -type f -name "*.lean" 2>/dev/null)

# Helper: count `match <expr>.objects[<idExpr>]?` patterns followed within
# ≤4 lines by `some (.<variant> ...)`. Multi-line tolerant. The `match`
# expression head can be bare (`st.objects[…]`) or parenthesized
# (`(st.objects[…] : Option KernelObject)`) and the state name can be
# any identifier (`st`, `st'`, `stMid`, `stStored`, etc.) — captured by
# matching on `.objects[` regardless of preceding context.
count_raw_match_variant() {
  local variant="$1"
  awk -v v="$variant" '
    BEGIN {hits=0; pending=0}
    /match.*\.objects\[/ {pending=4; next}
    pending > 0 {
      if (index($0, "some (." v) > 0) {hits++; pending=0; next}
      pending--
    }
    END {print hits + 0}
  ' "${KERNEL_FILES[@]}"
}

# RAW_MATCH_* by-variant counts (production proof surface).
RAW_MATCH_TCB=$(count_raw_match_variant "tcb")
RAW_MATCH_SCHEDCONTEXT=$(count_raw_match_variant "schedContext")
RAW_MATCH_ENDPOINT=$(count_raw_match_variant "endpoint")
RAW_MATCH_NOTIFICATION=$(count_raw_match_variant "notification")
RAW_MATCH_UNTYPED=$(count_raw_match_variant "untyped")
RAW_MATCH_CNODE=$(count_raw_match_variant "cnode")
RAW_MATCH_VSPACEROOT=$(count_raw_match_variant "vspaceRoot")

# Total raw-match site count: every `match <expr>.objects[…]?` regardless
# of variant. Used as a coarse upper-bound diagnostic; the per-variant
# counts are the binding monotonicity targets. Matches both the bare
# (`match st.objects[`) and parenthesized (`match (st.objects[…] : …)`)
# forms, which co-exist in the codebase pre-migration.
RAW_MATCH_TOTAL=$( (grep -cE "match.*\.objects\[" "${KERNEL_FILES[@]}" 2>/dev/null || true) \
  | awk -F: '{s += $2} END {print s + 0}')

# RAW_LOOKUP_TID — `tid.toObjId` projected at object-store boundaries.
RAW_LOOKUP_TID=$( (grep -c "\.toObjId\]?" "${KERNEL_FILES[@]}" 2>/dev/null || true) \
  | awk -F: '{s += $2} END {print s + 0}')

# Typed-helper adoption (kernel + tests + harness; excludes the helper
# definition file itself).
count_adoption() {
  local symbol="$1"
  # `grep -c` reports per-file counts; awk sums them. We swallow grep's
  # non-zero exit (no matches in any file) via `|| true` because pipefail
  # would otherwise terminate the script.
  (grep -c "$symbol" "${ALL_FILES[@]}" "${TEST_FILES[@]}" 2>/dev/null || true) \
    | awk -F: '{s += $2} END {print s + 0}'
}

GETTCB_ADOPTION=$(count_adoption "getTcb?")
GETSCHEDCTX_ADOPTION=$(count_adoption "getSchedContext?")
GETENDPOINT_ADOPTION=$(count_adoption "getEndpoint?")
GETNOTIFICATION_ADOPTION=$(count_adoption "getNotification?")
GETUNTYPED_ADOPTION=$(count_adoption "getUntyped?")
STOREOBJECTCHECKED_ADOPTION=$(count_adoption "storeObjectKindChecked")

# Dispatch-boundary sentinel guard adoption (production API only).
SENTINEL_CHECK_DISPATCH=$(grep -c "validateThreadIdArg\|validateSchedContextIdArg\|validateObjIdArg" \
  SeLe4n/Kernel/API.lean 2>/dev/null || echo 0)

# AN10 regression suite test count (cascades into the post-AN10 floor).
TEST_COUNT_AK7=0
if [[ -f tests/An10CascadeSuite.lean ]]; then
  # Per-test definitions are named `def an10_<letter>_<id>`.
  TEST_COUNT_AK7=$(grep -c "^def an10_" tests/An10CascadeSuite.lean 2>/dev/null || echo 0)
fi

# Proof-surface health (should-stay-zero).
SORRY_COUNT=$( (grep -rn "\bsorry\b" SeLe4n/ Main.lean --include="*.lean" 2>/dev/null \
  | grep -v "^[^:]*:[^:]*:\s*--" || true) | wc -l)
AXIOM_COUNT=$( (grep -rn "^axiom " SeLe4n/ Main.lean --include="*.lean" 2>/dev/null || true) | wc -l)

cat <<EOF
# AK7 cascade baseline (AN10-D)
#
# Refreshed by WS-AN Phase AN10. Format: human-readable sections plus a
# KEY=VALUE block for monotonicity-script consumption.
#
# Should-drop metrics: every subsequent commit must keep these <= baseline.
# Should-grow metrics: every subsequent commit must keep these >= baseline.

## Reader-side raw patterns (should-drop)

raw_match_tcb            = $RAW_MATCH_TCB
raw_match_schedcontext   = $RAW_MATCH_SCHEDCONTEXT
raw_match_endpoint       = $RAW_MATCH_ENDPOINT
raw_match_notification   = $RAW_MATCH_NOTIFICATION
raw_match_untyped        = $RAW_MATCH_UNTYPED
raw_match_cnode          = $RAW_MATCH_CNODE
raw_match_vspaceroot     = $RAW_MATCH_VSPACEROOT
raw_match_total          = $RAW_MATCH_TOTAL
raw_lookup_tid           = $RAW_LOOKUP_TID

## Typed-helper adoption (should-grow)

gettcb_adoption          = $GETTCB_ADOPTION
getschedctx_adoption     = $GETSCHEDCTX_ADOPTION
getendpoint_adoption     = $GETENDPOINT_ADOPTION
getnotification_adoption = $GETNOTIFICATION_ADOPTION
getuntyped_adoption      = $GETUNTYPED_ADOPTION

## Writer-side wrapper adoption (should-grow)

storeobjectchecked_adoption = $STOREOBJECTCHECKED_ADOPTION

## Dispatch-boundary sentinel guards (should-grow)

sentinel_check_dispatch  = $SENTINEL_CHECK_DISPATCH

## Regression test counts (should-grow)

test_count_ak7           = $TEST_COUNT_AK7

## Proof-surface health (should-stay-zero)

sorry_count              = $SORRY_COUNT
axiom_count              = $AXIOM_COUNT

## Machine-diffable block

RAW_MATCH_TCB=$RAW_MATCH_TCB
RAW_MATCH_SCHEDCONTEXT=$RAW_MATCH_SCHEDCONTEXT
RAW_MATCH_ENDPOINT=$RAW_MATCH_ENDPOINT
RAW_MATCH_NOTIFICATION=$RAW_MATCH_NOTIFICATION
RAW_MATCH_UNTYPED=$RAW_MATCH_UNTYPED
RAW_MATCH_CNODE=$RAW_MATCH_CNODE
RAW_MATCH_VSPACEROOT=$RAW_MATCH_VSPACEROOT
RAW_MATCH_TOTAL=$RAW_MATCH_TOTAL
RAW_LOOKUP_TID=$RAW_LOOKUP_TID
GETTCB_ADOPTION=$GETTCB_ADOPTION
GETSCHEDCTX_ADOPTION=$GETSCHEDCTX_ADOPTION
GETENDPOINT_ADOPTION=$GETENDPOINT_ADOPTION
GETNOTIFICATION_ADOPTION=$GETNOTIFICATION_ADOPTION
GETUNTYPED_ADOPTION=$GETUNTYPED_ADOPTION
STOREOBJECTCHECKED_ADOPTION=$STOREOBJECTCHECKED_ADOPTION
SENTINEL_CHECK_DISPATCH=$SENTINEL_CHECK_DISPATCH
TEST_COUNT_AK7=$TEST_COUNT_AK7
SORRY_COUNT=$SORRY_COUNT
AXIOM_COUNT=$AXIOM_COUNT
EOF
