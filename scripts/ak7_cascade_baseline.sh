#!/usr/bin/env bash
# AK7 cascade monotonicity baseline capture (AN10-D, restored from AL0).
#
# Re-introduced by WS-AN Phase AN10 (DEF-AK7-E.cascade / DEF-AK7-F.reader.hygiene
# / DEF-AK7-F.writer.hygiene closure) to track residual hygiene migration:
#   * `RAW_MATCH_*`         — raw `match st.objects[id]?` patterns by variant.
#                             SHOULD-DROP metric (every commit ≤ baseline floor).
#   * `STORE_READ_CODE`     — raw object-store reads in executable positions.
#   * `STORE_READ_SPEC`     — the same reads in propositions (diagnostic).
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

# The raw object-store match scanner, as ONE program shared by the real run and
# the self-test below -- two copies of a scanner is the shape this file's own
# metrics exist to catch.
#
# **The match line is scanned, not stepped over** (PR #893 review round 4).  The
# window used to open on the line *after* the discriminator, because the rule
# ended in `next`; a `match` whose first arm sits on the same line --
# `match st.objects[id]? with | some (.tcb t) => ...`, which Lean accepts --
# therefore recorded no `RAW_SITE` at all.  That is not a lost row but a lost
# *site*: `RAW_MATCH_TOTAL` is derived from these rows, so such a read is absent
# from every enforced metric and moves only `RAW_MATCH_UNCLASSIFIED`, which is
# diagnostic-only -- it would pass Tier 0 in silence.  Round 2 had widened this
# scan to the *end* of the window and never asked whether the window began in
# the right place, which is the sweep rule failing one line over.  `scan_arms`
# runs on the discriminator line without consuming a window slot, so the four
# following lines are scanned exactly as before and no existing figure moves.
# `$0` and the rest are awk's fields, not shell parameters, so the program is
# single-quoted deliberately.
# shellcheck disable=SC2016
RAW_MATCH_AWK='
    # The enclosing declaration name, or "" when this line declares nothing.
    # A Lean declaration header sits at column 0, so the caller gates on that;
    # an attribute may share the line (`@[simp] theorem foo`) or occupy its own,
    # and an anonymous `instance :` yields the sentinel rather than a stray `:`.
    function decl_name(   i, n, parts, nm) {
      n = split($0, parts, /[ \t]+/)
      for (i = 1; i <= n; i++) {
        if (parts[i] ~ /^(def|theorem|lemma|abbrev|instance|example|structure|inductive|class)$/) {
          if (i < n) {
            nm = parts[i + 1]
            sub(/[({:\[].*$/, "", nm)
            if (nm != "") return nm
          }
          return "<anonymous>"
        }
      }
      return ""
    }
    function scan_arms(   i, seen_key, key) {
      for (i = 1; i <= nvars; i++) {
        if (index($0, "some (." vars[i]) > 0) {
          seen_key = match_id SUBSEP vars[i]
          if (!(seen_key in seen)) {
            seen[seen_key] = 1
            key = FILENAME " " curdecl " " vars[i]
            hits[key]++
            # The first variant this match discriminates makes it a classified
            # SITE; later arms of the same match add rows but not sites.
            if (!(match_id in site_seen)) {
              site_seen[match_id] = 1
              nsites++
            }
          }
        }
      }
    }
    FNR == 1 {pending = 0; match_id++; delete seen; curdecl = "<file-scope>"}
    # Before the match rules, and WITHOUT `next`: a one-line
    # `def f ... := match st.objects[id]? with ...` both opens a declaration and
    # is a site, so the header must be read first and then fall through.
    /^[^ \t]/ {d = decl_name(); if (d != "") curdecl = d}
    /match.*\.objects\[/ {pending = 4; match_id++; delete seen; scan_arms(); next}
    pending > 0 {
      scan_arms()
      pending--
    }
    BEGIN {
      nvars = split("tcb schedContext endpoint notification untyped cnode vspaceRoot",
                    vars, " ")
      match_id = 0
    }
    END {
      if (mode == "sites") {print nsites + 0}
      else {for (k in hits) print k, hits[k]}
    }
'

# Self-test: the scanner against synthesized Lean fixtures, in a temporary tree,
# so it can be checked without touching the repository.  Each case names the
# shape it pins; the one-line case is the round-4 finding, kept so the window
# cannot silently close over the discriminator again.
if [[ "${1:-}" == "--self-test" ]]; then
  fx="$(mktemp -d)"
  trap 'rm -rf "$fx"' EXIT
  printf '%s\n' \
    'def a (st : SystemState) (id : ObjId) : Nat :=' \
    '  match st.objects[id]? with | some (.tcb t) => 1 | _ => 0' \
    > "$fx/OneLine.lean"
  printf '%s\n' \
    'def b (st : SystemState) (id : ObjId) : Nat :=' \
    '  match st.objects[id]? with' \
    '  | some (.tcb t) => 1' \
    '  | _ => 0' \
    > "$fx/MultiLine.lean"
  printf '%s\n' \
    'def c (st : SystemState) (id : ObjId) : Nat :=' \
    '  match st.objects[id]? with' \
    '  | some (.tcb t) => 1' \
    '  | some (.endpoint e) => 2' \
    '  | _ => 0' \
    > "$fx/TwoArms.lean"
  printf '%s\n' \
    'def d (st : SystemState) (id : ObjId) : Nat :=' \
    '  match st.objects[id]? with' \
    '  | some (.tcb t) => 1' \
    '  | _ => 0' \
    'def e (st : SystemState) (id : ObjId) : Nat :=' \
    '  match st.objects[id]? with | some (.tcb t) => 2 | _ => 0' \
    > "$fx/TwoSites.lean"
  printf '%s\n' \
    'def f (st : SystemState) (id : ObjId) : Nat :=' \
    '  match st.objects[id]? with' \
    '  | none => 0' \
    '  | none => 0' \
    '  | none => 0' \
    '  | none => 0' \
    '  | some (.tcb t) => 1' \
    > "$fx/OutsideWindow.lean"
  # The round-6 swap: `TwoSites.lean` with `d` hygienized and a fresh `g`.
  printf '%s\n' \
    'def d (st : SystemState) (id : ObjId) : Nat :=' \
    '  st.getTcb? id |>.map (fun _ => 1) |>.getD 0' \
    'def e (st : SystemState) (id : ObjId) : Nat :=' \
    '  match st.objects[id]? with | some (.tcb t) => 2 | _ => 0' \
    'def g (st : SystemState) (id : ObjId) : Nat :=' \
    '  match st.objects[id]? with | some (.tcb t) => 3 | _ => 0' \
    > "$fx/Swapped.lean"
  st_fail=0
  st_ok=0
  st_expect() {
    local name="$1" file="$2" want="$3" got
    got="$( (cd "$fx" && awk "$RAW_MATCH_AWK" "$file") | sort | tr '\n' ';' )"
    if [[ "$got" == "$want" ]]; then
      echo "  OK   self-test: $name"
      st_ok=$(( st_ok + 1 ))
    else
      echo "  SELF-TEST FAIL: $name: expected [$want], got [$got]" >&2
      st_fail=1
    fi
  }
  # The round-4 finding: a discriminator whose first arm shares its line.
  st_expect "a one-line match records its arm" OneLine.lean "OneLine.lean a tcb 1;"
  # ...and the shapes that must not change while it is fixed.
  st_expect "a multi-line match still records its arm" MultiLine.lean "MultiLine.lean b tcb 1;"
  st_expect "every arm of a multi-arm match is recorded" TwoArms.lean \
    "TwoArms.lean c endpoint 1;TwoArms.lean c tcb 1;"
  # The round-6 finding.  This assertion used to read `TwoSites.lean tcb 2` --
  # one row, two occurrences -- and that collapse WAS the defect: hygienizing
  # `d` while a fresh raw read appears in some other declaration of the same
  # file leaves the count at 2 and the floor accepts it.  Keyed by the enclosing
  # declaration, `d` and `e` are separate floors, so the reappearance is a key
  # the baseline does not name and fails outright.
  st_expect "two sites in one file are two keyed floors" TwoSites.lean \
    "TwoSites.lean d tcb 1;TwoSites.lean e tcb 1;"
  # ...and the swap the old keying could not see, as the scanner sees it: `d`
  # hygienized, a new declaration `g` carrying the raw read.  Same file, same
  # variant, same total; a DIFFERENT inventory, which is the whole point.
  st_expect "a raw read moved between declarations changes the inventory" Swapped.lean \
    "Swapped.lean e tcb 1;Swapped.lean g tcb 1;"
  # The window is still four lines after the discriminator, not five.
  st_expect "an arm beyond the window is not recorded" OutsideWindow.lean ""
  # ...and `mode=sites` counts MATCHES, not variant incidences -- the operand
  # `RAW_MATCH_UNCLASSIFIED` subtracts from a count of match lines.  A two-arm
  # match is two rows and ONE site; getting this wrong made the remainder
  # negative (PR #893 review round 5).
  st_sites() {
    local name="$1" file="$2" want="$3" got
    got="$( (cd "$fx" && awk -v mode=sites "$RAW_MATCH_AWK" "$file") )"
    if [[ "$got" == "$want" ]]; then
      echo "  OK   self-test: $name"
      st_ok=$(( st_ok + 1 ))
    else
      echo "  SELF-TEST FAIL: $name: expected [$want], got [$got]" >&2
      st_fail=1
    fi
  }
  st_sites "a two-arm match is two rows but ONE site" TwoArms.lean 1
  st_sites "two separate matches are two sites" TwoSites.lean 2
  st_sites "a one-line match counts as a site" OneLine.lean 1
  st_sites "a file with no classified match has no site" OutsideWindow.lean 0
  if [[ "$st_fail" -ne 0 ]]; then
    echo "raw-match scanner self-test: FAILED" >&2
    exit 1
  fi
  echo "raw-match scanner self-test: $st_ok cases, $st_ok correct."
  exit 0
fi

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
#
# **Every arm of the match is recorded, not just the first** (PR #893 review
# round 2).  A `match` may discriminate several constructors inside the window --
# `some (.tcb ...)` on one arm, `some (.endpoint ...)` on the next -- and the
# first cut of this single-pass scan set `pending = 0` and `next` on the first
# hit, so every later arm of the same match went unrecorded.  The per-variant
# scans it replaced could not miss them, because each variant got its own pass;
# consolidating the passes silently narrowed what the inventory sees, and the
# hole is precisely a *newly added second variant at an existing match site* --
# which the monotonic gate would then pass.  The window is now scanned to the
# end, with `seen` keyed by (match, variant) so a variant occurring twice in one
# match still counts once, exactly as a per-variant pass counted it.
emit_raw_match_rows() {
  awk "$RAW_MATCH_AWK" "${KERNEL_FILES[@]}" | sort
}

# The number of distinct `match … .objects[…]` expressions that discriminated at
# least one constructor -- **sites, not variant incidences** (PR #893 review
# round 5).  `RAW_MATCH_TOTAL` counts one row per (file, variant), so subtracting
# it from a count of match *lines* compares two different things: since the
# multi-arm support landed, one match discriminating `.tcb` and `.endpoint`
# contributes two rows against one line and the remainder goes negative.  The
# operand the subtraction wants is this one, computed by the same program so the
# two readings cannot drift.
count_classified_match_sites() {
  awk -v mode=sites "$RAW_MATCH_AWK" "${KERNEL_FILES[@]}"
}

# The object-store READ census (`scripts/lean_store_read_census.py`).
#
# This replaces the old `RAW_LOOKUP_TID` / `RAW_LOOKUP_SITE` pair, which was a
# `grep -c "\.toObjId\]?"` over the kernel tree and was wrong in four ways at
# once.  It counted *lines*, so two reads on one line counted once and a reflow
# lowered the number.  It was named `_TID` while four types carry `.toObjId`
# (`ThreadId`, `SchedContextId`, `ReplyId`, `KindedObjId`), so reply-stack and
# scheduling-context vocabulary moved a figure that claimed to be about
# threads.  It keyed rows by `(file)` alone, while its sibling `RAW_SITE` had
# been refined to `(file, declaration, variant)` in PR #893 review round 6 for
# the stated reason that a per-file key is a cardinality one level up -- the
# refinement was never swept onto this metric.  And, decisively, it counted a
# read in a *theorem statement* and a read in a *transition body* as the same
# thing: 96.9% of the figure was specification vocabulary, so the number
# tracked how much invariant text the project had written rather than how much
# unhygienic code it had, and every invariant cut re-anchored it upward
# (1609 -> 1600 -> 1678 -> 1711 over three days).
#
# The census answers the two questions separately.  `STORE_READ_CODE` is the
# migratable population -- a raw read in the body of a declaration whose result
# is not a `Prop` -- and is enforced.  `STORE_READ_SPEC` is everything else and
# is a diagnostic, for the same reason `RAW_MATCH_UNCLASSIFIED` is: a
# proposition about the store has no helper form (`getTcb? k = none` holds both
# for an absent key and for a wrong-kinded object, so a frame statement
# quantified over every key cannot be phrased through a variant accessor
# without weakening it), and holding it to a drop would make writing an
# invariant a Tier 0 failure.
emit_store_read_rows() {
  python3 "${REPO_ROOT}/scripts/lean_store_read_census.py" --rows
}

RAW_MATCH_ROWS="$(emit_raw_match_rows)"
STORE_READ_ROWS="$(emit_store_read_rows)"

# The scalar per-variant totals are now *derived* from the inventory rather than
# recomputed, so the two can never disagree about the same tree.
count_raw_match_variant() {
  local variant="$1"
  printf '%s\n' "${RAW_MATCH_ROWS}" \
    | awk -v v="$variant" '$3 == v {s += $4} END {print s + 0}'
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
  | awk 'NF {s += $4} END {print s + 0}')

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
RAW_MATCH_CLASSIFIED_SITES=$(count_classified_match_sites)
RAW_MATCH_UNCLASSIFIED=$(( RAW_MATCH_ALL - RAW_MATCH_CLASSIFIED_SITES ))

# The two scalars, derived from the census rows so the totals and the
# inventory cannot diverge.
STORE_READ_CODE=$(printf '%s\n' "${STORE_READ_ROWS}" \
  | awk -F'|' '/^STORE_READ_CODE_SITE=/ {s += $NF} END {print s + 0}')
STORE_READ_SPEC=$(printf '%s\n' "${STORE_READ_ROWS}" \
  | awk -F'|' '/^STORE_READ_SPEC_SITE=/ {s += $NF} END {print s + 0}')

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
store_read_code          = $STORE_READ_CODE   (enforced)
store_read_spec          = $STORE_READ_SPEC (diagnostic)

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
## RAW_SITE and STORE_READ_CODE_SITE rows are the binding floors: the gate
## refuses any key absent from the baseline, and holds every key present to its
## recorded count.  Both are keyed by the enclosing DECLARATION, because a
## per-file key is a cardinality one level up -- hygienizing one declaration
## while another starts reading raw leaves a per-file row unmoved, which is the
## movement the inventory exists to catch.  STORE_READ_SPEC_SITE rows are
## recorded but not enforced.  The scalars below are derived from these rows.

$(printf '%s\n' "${RAW_MATCH_ROWS}" | awk 'NF {print "RAW_SITE=" $1 "|" $2 "|" $3 "|" $4}')
$(printf '%s\n' "${STORE_READ_ROWS}")

RAW_MATCH_TCB=$RAW_MATCH_TCB
RAW_MATCH_SCHEDCONTEXT=$RAW_MATCH_SCHEDCONTEXT
RAW_MATCH_ENDPOINT=$RAW_MATCH_ENDPOINT
RAW_MATCH_NOTIFICATION=$RAW_MATCH_NOTIFICATION
RAW_MATCH_UNTYPED=$RAW_MATCH_UNTYPED
RAW_MATCH_CNODE=$RAW_MATCH_CNODE
RAW_MATCH_VSPACEROOT=$RAW_MATCH_VSPACEROOT
RAW_MATCH_TOTAL=$RAW_MATCH_TOTAL
RAW_MATCH_UNCLASSIFIED=$RAW_MATCH_UNCLASSIFIED
STORE_READ_CODE=$STORE_READ_CODE
STORE_READ_SPEC=$STORE_READ_SPEC
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
