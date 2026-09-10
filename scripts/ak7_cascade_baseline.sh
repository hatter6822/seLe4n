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
#   * `READER_HYGIENE_SUITE_TESTS`      — `tests/An10CascadeSuite.lean` test count.
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

# WS-SM SM8.B (PR #861 review round 43): count CODE, not the prose about it.
#
# Every metric below is a line-oriented `grep` over Lean sources, so a
# docstring *quoting* the pattern it discusses moved the number: a comment
# reading "opens by matching `post.objects[oid]?`" counted as a raw
# object-store match and pushed `RAW_MATCH_TOTAL` above its floor.  The tree
# carried the scar — that docstring had been split across two lines on purpose
# so the counter would not see it — and a metric that makes writing about the
# code regress a hygiene floor is measuring the wrong text.  Worse in the other
# direction: `SORRY_COUNT` greps `\bsorry\b` over the kernel behind a
# `grep -v '^…--'` heuristic that a block comment or a trailing comment walks
# straight past, so a docstring could break the project's most load-bearing
# gate.
#
# Counting instead against the comment-free overlay, whose `.lean` files are
# byte-aligned with the originals, so every count means what it says and prose
# may be written plainly.
CODE_VIEW="${REPO_ROOT}/.lake/build/leancodeview"
python3 "${REPO_ROOT}/scripts/lean_code_view.py" --overlay "${CODE_VIEW}" >/dev/null
cd "$CODE_VIEW"

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

# Helper: emit one `<file> <variant> <count>` row per (file, variant) pair with
# at least one `match <expr>.objects[<idExpr>]?` followed within ≤4 lines by
# `some (.<variant> ...)`. Multi-line tolerant. The `match` expression head can
# be bare (`st.objects[…]`) or parenthesized (`(st.objects[…] : Option
# KernelObject)`) and the state name can be any identifier (`st`, `st'`,
# `stMid`, `stStored`, etc.) — captured by matching on `.objects[` regardless of
# preceding context.
#
# **Per-file, because a cardinality is not a set.**  This metric used to be a
# whole-tree count with a single floor, and a count answers "how many" when the
# property is "which": a migration that hygienizes one raw read in file A and
# introduces a fresh one in file B leaves the total unchanged, so the gate --
# whose entire purpose is to stop a hygienized site from re-introducing the raw
# pattern -- passed on exactly the movement it exists to catch.  The floor is
# now the (file, variant) -> count map, the same shape
# `scripts/identifier_naming_baseline.json` uses and for the same reason: a set
# of pairs alone cannot see a second occurrence inside a file that already
# contains one, and a count alone cannot see the first occurrence in a file that
# did not.  A pair absent from the baseline fails outright; a pair present may
# only fall.
#
# `FNR == 1` resets the pending window at every file boundary: awk carries state
# across the file list, so a trailing `match … .objects[` at the end of one file
# could otherwise pair with a `some (.tcb …)` in the first lines of the next and
# report a site that exists in neither.
emit_raw_match_rows() {
  awk '
    FNR == 1 {pending = 0}
    /match.*\.objects\[/ {pending = 4; next}
    pending > 0 {
      for (i = 1; i <= nvars; i++) {
        if (index($0, "some (." vars[i]) > 0) {
          key = FILENAME " " vars[i]
          hits[key]++
          pending = 0
          next
        }
      }
      pending--
    }
    BEGIN {
      nvars = split("tcb schedContext endpoint notification untyped cnode vspaceRoot",
                    vars, " ")
    }
    END {for (k in hits) print k, hits[k]}
  ' "${KERNEL_FILES[@]}" | sort
}

# Helper: `<file> <count>` rows for the bare `tid.toObjId` object-store lookup,
# per file for the same reason.
emit_raw_lookup_rows() {
  (grep -c "\.toObjId\]?" "${KERNEL_FILES[@]}" 2>/dev/null || true) \
    | awk -F: '$2 > 0 {print $1, $2}' | sort
}

RAW_MATCH_ROWS="$(emit_raw_match_rows)"
RAW_LOOKUP_ROWS="$(emit_raw_lookup_rows)"

# The scalar per-variant totals are now *derived* from the inventory rather than
# recomputed, so the two can never disagree about the same tree.
count_raw_match_variant() {
  local variant="$1"
  printf '%s\n' "${RAW_MATCH_ROWS}" \
    | awk -v v="$variant" '$2 == v {s += $3} END {print s + 0}'
}

# RAW_MATCH_* by-variant counts (production proof surface).
RAW_MATCH_TCB=$(count_raw_match_variant "tcb")
RAW_MATCH_SCHEDCONTEXT=$(count_raw_match_variant "schedContext")
RAW_MATCH_ENDPOINT=$(count_raw_match_variant "endpoint")
RAW_MATCH_NOTIFICATION=$(count_raw_match_variant "notification")
RAW_MATCH_UNTYPED=$(count_raw_match_variant "untyped")
RAW_MATCH_CNODE=$(count_raw_match_variant "cnode")
RAW_MATCH_VSPACEROOT=$(count_raw_match_variant "vspaceRoot")

# Total raw-match site count. Derived from the inventory, so it is the sum of
# exactly the sites the gate pins -- it used to be an independently-shaped
# `grep -cE "match.*\.objects\["`, which counts every raw object-store match
# whether or not it discriminates a variant, so the "total" and the per-variant
# figures below were answers to two different questions printed under one
# heading.  The matches discriminating no variant are the remainder, reported
# separately as RAW_MATCH_UNCLASSIFIED below.
RAW_MATCH_TOTAL=$(printf '%s\n' "${RAW_MATCH_ROWS}" \
  | awk 'NF {s += $3} END {print s + 0}')

# The raw matches that discriminate NO variant: every `match <expr>.objects[…]?`
# minus the classified sites above.  Printed as a diagnostic only -- a match that
# binds the whole `KernelObject` without naming a constructor is not a
# reader-hygiene site, so this figure is deliberately absent from the enforced
# METRICS list in `ak7_cascade_check_monotonic.sh`; see the note there.
#
# **It is the remainder, not the whole** (PR #893 review).  It was
# `grep -cE "match.*\.objects\["` verbatim -- every raw match, classified ones
# included -- so a variable named UNCLASSIFIED reported 130 while exactly 111 of
# those sites were classified, and RAW_MATCH_TOTAL beside it reported that 111.
# Two names for two different questions, one of which the name denied: the
# project's own "a name is not the thing" defect, in a metric that reads as
# measurement.  Deriving it by subtraction is what keeps the two consistent on
# any tree.
RAW_MATCH_ALL=$( (grep -cE "match.*\.objects\[" "${KERNEL_FILES[@]}" 2>/dev/null || true) \
  | awk -F: '{s += $2} END {print s + 0}')
RAW_MATCH_UNCLASSIFIED=$(( RAW_MATCH_ALL - RAW_MATCH_TOTAL ))

# RAW_LOOKUP_TID — `tid.toObjId` projected at object-store boundaries. Derived
# from the per-file rows, so the total and the inventory cannot diverge.
RAW_LOOKUP_TID=$(printf '%s\n' "${RAW_LOOKUP_ROWS}" \
  | awk 'NF {s += $2} END {print s + 0}')

# Typed-helper adoption (kernel + tests + harness; excludes the helper
# definition file itself).
#
# The metric means "consumers read the store through the typed helper", and a
# substring search does not measure that: `getEndpoint?` occurs inside
# `getEndpoint?_eq_some_iff`, `getEndpoint?_congr_objects` and every theorem
# named `*_ok_getEndpoint?`, none of which is a read of the object store.  29 of
# 210 hits were such names, so writing a lemma *about* the helper raised the
# adoption floor and adding a bridging lemma could satisfy a migration this
# gate exists to drive -- a presence check standing in for a relation, in the
# gate's own should-grow direction.
#
# Counting whole symbols instead: the occurrence must not be preceded or
# followed by an identifier character, so a qualified call (`st.getEndpoint?`,
# `SystemState.getEndpoint?`) counts and a longer identifier that merely
# contains the name does not.  `?` and `!` are identifier characters in Lean,
# so both guards list them.
count_adoption() {
  local symbol="$1"
  # `grep -cP` reports per-file counts; awk sums them. We swallow grep's
  # non-zero exit (no matches in any file) via `|| true` because pipefail
  # would otherwise terminate the script.
  # `\x27` is the apostrophe (Lean's prime suffix); spelling it as an escape
  # keeps the pattern inside one double-quoted shell string.
  local pattern="(?<![A-Za-z0-9_\\x27!?])${symbol}(?![A-Za-z0-9_\\x27!?])"
  (grep -cP "$pattern" "${ALL_FILES[@]}" "${TEST_FILES[@]}" 2>/dev/null || true) \
    | awk -F: '{s += $2} END {print s + 0}'
}

GETTCB_ADOPTION=$(count_adoption "getTcb\?")
GETSCHEDCTX_ADOPTION=$(count_adoption "getSchedContext\?")
GETENDPOINT_ADOPTION=$(count_adoption "getEndpoint\?")
GETNOTIFICATION_ADOPTION=$(count_adoption "getNotification\?")
GETUNTYPED_ADOPTION=$(count_adoption "getUntyped\?")
GETCNODE_ADOPTION=$(count_adoption "getCNode\?")
GETVSPACEROOT_ADOPTION=$(count_adoption "getVSpaceRoot\?")
STOREOBJECTCHECKED_ADOPTION=$(count_adoption "storeObjectKindChecked")

# Dispatch-boundary sentinel guard adoption (production API only).
SENTINEL_CHECK_DISPATCH=$(grep -c "validateThreadIdArg\|validateSchedContextIdArg\|validateObjIdArg" \
  SeLe4n/Kernel/API.lean 2>/dev/null || echo 0)

# AN10 regression suite test count (cascades into the post-AN10 floor).
READER_HYGIENE_SUITE_TESTS=0
if [[ -f tests/An10CascadeSuite.lean ]]; then
  # Per-test definitions are named `def an10_<letter>_<id>`.
  READER_HYGIENE_SUITE_TESTS=$(grep -c "^def an10_" tests/An10CascadeSuite.lean 2>/dev/null || echo 0)
fi

# AN11-A KernelError matrix row count (cascades into the post-AN11 floor).
# Counts rows in the `errorMatrix : List KernelErrorRejection` definition
# by counting `private def row_*` per-row definitions.  Should-grow metric.
KERRORMATRIX_ROWS=0
if [[ -f tests/KernelErrorMatrixSuite.lean ]]; then
  KERRORMATRIX_ROWS=$(grep -c "^private def row_" tests/KernelErrorMatrixSuite.lean 2>/dev/null || echo 0)
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
raw_match_unclassified   = $RAW_MATCH_UNCLASSIFIED
raw_lookup_tid           = $RAW_LOOKUP_TID

## Typed-helper adoption (should-grow)

gettcb_adoption          = $GETTCB_ADOPTION
getschedctx_adoption     = $GETSCHEDCTX_ADOPTION
getendpoint_adoption     = $GETENDPOINT_ADOPTION
getnotification_adoption = $GETNOTIFICATION_ADOPTION
getuntyped_adoption      = $GETUNTYPED_ADOPTION
getcnode_adoption        = $GETCNODE_ADOPTION
getvspaceroot_adoption   = $GETVSPACEROOT_ADOPTION

## Writer-side wrapper adoption (should-grow)

storeobjectchecked_adoption = $STOREOBJECTCHECKED_ADOPTION

## Dispatch-boundary sentinel guards (should-grow)

sentinel_check_dispatch  = $SENTINEL_CHECK_DISPATCH

## Regression test counts (should-grow)

reader_hygiene_suite_tests           = $READER_HYGIENE_SUITE_TESTS
kerrormatrix_rows        = $KERRORMATRIX_ROWS

## Proof-surface health (should-stay-zero)

sorry_count              = $SORRY_COUNT
axiom_count              = $AXIOM_COUNT

## Machine-diffable block
##
## RAW_SITE / RAW_LOOKUP_SITE rows are the binding floors: the gate refuses any
## (file, variant) pair absent from the baseline, and holds every pair present
## to its recorded count. The scalars below are derived from those rows and are
## kept as human-readable diagnostics.

$(printf '%s\n' "${RAW_MATCH_ROWS}" | awk 'NF {print "RAW_SITE=" $1 "|" $2 "|" $3}')
$(printf '%s\n' "${RAW_LOOKUP_ROWS}" | awk 'NF {print "RAW_LOOKUP_SITE=" $1 "|" $2}')

RAW_MATCH_TCB=$RAW_MATCH_TCB
RAW_MATCH_SCHEDCONTEXT=$RAW_MATCH_SCHEDCONTEXT
RAW_MATCH_ENDPOINT=$RAW_MATCH_ENDPOINT
RAW_MATCH_NOTIFICATION=$RAW_MATCH_NOTIFICATION
RAW_MATCH_UNTYPED=$RAW_MATCH_UNTYPED
RAW_MATCH_CNODE=$RAW_MATCH_CNODE
RAW_MATCH_VSPACEROOT=$RAW_MATCH_VSPACEROOT
RAW_MATCH_TOTAL=$RAW_MATCH_TOTAL
RAW_MATCH_UNCLASSIFIED=$RAW_MATCH_UNCLASSIFIED
RAW_LOOKUP_TID=$RAW_LOOKUP_TID
GETTCB_ADOPTION=$GETTCB_ADOPTION
GETSCHEDCTX_ADOPTION=$GETSCHEDCTX_ADOPTION
GETENDPOINT_ADOPTION=$GETENDPOINT_ADOPTION
GETNOTIFICATION_ADOPTION=$GETNOTIFICATION_ADOPTION
GETUNTYPED_ADOPTION=$GETUNTYPED_ADOPTION
GETCNODE_ADOPTION=$GETCNODE_ADOPTION
GETVSPACEROOT_ADOPTION=$GETVSPACEROOT_ADOPTION
STOREOBJECTCHECKED_ADOPTION=$STOREOBJECTCHECKED_ADOPTION
SENTINEL_CHECK_DISPATCH=$SENTINEL_CHECK_DISPATCH
READER_HYGIENE_SUITE_TESTS=$READER_HYGIENE_SUITE_TESTS
KERRORMATRIX_ROWS=$KERRORMATRIX_ROWS
SORRY_COUNT=$SORRY_COUNT
AXIOM_COUNT=$AXIOM_COUNT
EOF
