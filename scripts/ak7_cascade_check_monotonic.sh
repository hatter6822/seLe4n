#!/usr/bin/env bash
# AK7 cascade monotonicity gate (AN10-D, restored from AL0).
#
# Re-introduced by WS-AN Phase AN10. Reads the floors from
# `scripts/store_reader_hygiene_baseline.txt` (KEY=value format produced by
# `scripts/ak7_cascade_baseline.sh`).
#
# **The binding floor is an inventory, not a count.**  Until WS-OD OD3.5 this
# gate held a single whole-tree cardinality per variant, which answers "how
# many" when the property it enforces is "which": a change that hygienizes one
# raw read in file A and introduces a fresh one in file B leaves every total
# unchanged, so the gate passed on precisely the movement it exists to catch --
# a previously hygienized site re-introducing the raw pattern.  The floor is now
# the `RAW_SITE` rows: a key the baseline does not name fails outright, and a
# key it names may only fall.  (`STORE_READ_CODE` had the same inventory until
# `v0.35.8`, when its population reached zero and the inventory gave way to a
# `ZERO_METRICS` entry -- at zero a cardinality and a set say the same thing,
# and this file must not answer one question twice.  Its site rows survive as
# the failure message's locator and as the total's consistency check, not as a
# floor.)
# That is the shape `scripts/identifier_naming_baseline.json` already uses, for
# the same reason -- a set of pairs alone cannot see a second occurrence inside
# a file that already contains one, and a count alone cannot see the first
# occurrence in a file that did not, so the floor has to be both.
#
# **The key is (file, DECLARATION, variant), and that granularity is where this
# refinement stops** (PR #893 review round 6).  A (file, variant) key is still a
# cardinality one level up: 22 of the 30 rows it produced had a count above one,
# so hygienizing a raw read in one declaration while a fresh one appeared in
# another declaration of the same file left the row and every scalar identical
# -- the cross-file case this header already describes, with "file B" replaced
# by "declaration e", and it survived the fix for it.  Keying by the enclosing
# declaration turns that into a key the baseline does not name, which fails
# outright.  It stops there because the DECLARATION IS THE UNIT OF
# HYGIENIZATION: a count-preserving swap inside one declaration means that
# declaration still has the same raw reads, which is not the movement this gate
# exists to catch, whereas a whole declaration going clean while another starts
# reading raw is.  Finer keys (line numbers, ordinals) would also churn the
# baseline on every unrelated edit above them, so they buy noise, not reach.
#
# The scalar metrics below are derived from those rows (or are independent
# should-grow ratchets) and are kept because they are what a reader quotes.
# For every metric, enforces the direction the AK7 cascade is supposed to
# drive:
#   * SHOULD-DROP: current value MUST be ≤ baseline floor.
#                  Regression means the migration regressed (a previously
#                  hygienized site re-introduced the raw pattern).
#   * SHOULD-GROW: current value MUST be ≥ baseline floor.
#                  Regression means a typed-helper consumer reverted to the
#                  raw pattern, or a `storeObjectKindChecked` site reverted
#                  to bare `storeObject`.
#
# **The should-grow floors are a proxy; the inventory is the fact.**  "A
# consumer reverted to the raw pattern" is exactly what the RAW_SITE inventory
# decides, site by site.  A whole-tree adoption count only approximates it, and
# it approximates in a direction that produces false alarms: *deleting* a
# duplicated read lowers the count while improving hygiene.  WS-OD OD3.6 hit
# this immediately — consolidating three `st.getEndpoint?` reads onto the
# `receiveRendezvousSender?` resolver that already asked the same question took
# GETENDPOINT_ADOPTION from 178 to 175 with every RAW_SITE row and every raw
# total byte-identical.  So when a should-grow metric falls, first check the
# inventory: if no raw-read site was added or grew, the fall is a consolidation
# or a deletion and re-anchoring the baseline is the correct response, not a
# revert.  If a raw site *did* move, the inventory says so on its own and the
# adoption number is not what you should be reading.
#
# When all metrics pass, exit 0. When any metric fails, exit 1 with a
# per-metric diagnostic.
#
# Wired into `scripts/test_tier0_hygiene.sh` so every commit is gated.
#
# To re-anchor the baseline (after AN10 close, or after each subsequent
# WS-AN-style hygiene push):
#   bash scripts/ak7_cascade_baseline.sh > scripts/store_reader_hygiene_baseline.txt
#
# The baseline lives beside the gate that reads it.  It used to live under
# `docs/dev_history/`, which this project reserves for material retained "only
# for historical traceability" and instructs contributors not to read -- a live
# Tier 0 floor is neither.
#
# Self-test:
#   scripts/ak7_cascade_check_monotonic.sh --self-test

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

BASELINE_FILE="${STORE_READER_BASELINE_FILE:-scripts/store_reader_hygiene_baseline.txt}"

# ---------------------------------------------------------------------------
# Self-test.
#
# Every mutation here is TOKEN-PRESERVING: it keeps the raw-read sites the tree
# already has and breaks the *relation* the floor asserts.  A fixture that
# mutated by DELETION would be satisfied by any cardinality check -- which is
# exactly how the whole-tree count passed for as long as it did -- so a deleting
# case proves nothing about this gate and none is written.
#
#   moved   — one site relocated from a pinned file to another pinned file.
#             Every scalar total is byte-identical; only the inventory moves.
#             This is the case the pre-OD3.5 gate could not see, and it is the
#             failure mode the gate exists for: a previously hygienized file
#             re-introducing the raw pattern while some other file gives one up.
#   second  — a second occurrence added to a file the baseline already names.
#             The key set is unchanged, so a set-of-pairs floor with no counts
#             passes; only the per-key count sees it.
#
# There are two case shapes, because the file carries two kinds of claim and a
# mutation is token-preserving with respect to whichever one it holds fixed:
#
#   st_case         — the INVENTORY mutations.  Every scalar is inherited from
#                     the baseline verbatim and the harness asserts it, so the
#                     case is provably about the per-key floor.
#   st_census_case  — the CENSUS mutations, for `STORE_READ_CODE`, which is a
#                     zero-floor rather than an inventory.  Here the scalars
#                     move and the harness asserts the fixture is internally
#                     consistent (the total equals the sum of its site rows) --
#                     otherwise the case would be testing a capture the gate is
#                     right to reject for a different reason.
#
# Run against synthesized baseline/current pairs rather than by editing the
# tree, so the self-test is hermetic and cannot leave the repository dirty.
# ---------------------------------------------------------------------------
if [[ "${1:-}" == "--self-test" ]]; then
  st_tmp="$(mktemp -d)"
  trap 'rm -rf "$st_tmp"' EXIT
  st_failed=0

  st_base="$st_tmp/baseline.txt"
  cat > "$st_base" <<'SELFTEST_BASELINE'
RAW_SITE=SeLe4n/Kernel/A.lean|foo|tcb|2
RAW_SITE=SeLe4n/Kernel/B.lean|bar|tcb|1
STORE_READ_SPEC_SITE=SeLe4n/Kernel/A.lean|frame|9
RAW_MATCH_TCB=3
RAW_MATCH_SCHEDCONTEXT=0
RAW_MATCH_ENDPOINT=0
RAW_MATCH_NOTIFICATION=0
RAW_MATCH_UNTYPED=0
RAW_MATCH_CNODE=0
RAW_MATCH_VSPACEROOT=0
RAW_MATCH_TOTAL=3
RAW_MATCH_UNCLASSIFIED=3
STORE_READ_CODE=0
STORE_READ_SPEC=9
GETTCB_ADOPTION=0
GETSCHEDCTX_ADOPTION=0
GETENDPOINT_ADOPTION=0
GETNOTIFICATION_ADOPTION=0
GETUNTYPED_ADOPTION=0
GETCNODE_ADOPTION=0
GETVSPACEROOT_ADOPTION=0
STOREOBJECTCHECKED_ADOPTION=0
SENTINEL_CHECK_DISPATCH=0
READER_HYGIENE_SUITE_TESTS=0
KERRORMATRIX_ROWS=0
SORRY_COUNT=0
AXIOM_COUNT=0
SELFTEST_BASELINE

  # `<name> <expect: pass|fail> <current-inventory rows>`; the scalars are
  # inherited from the baseline verbatim, so every case below leaves every
  # total unchanged by construction.
  st_case() {
    local name="$1" expect="$2" rows="$3"
    local cur="$st_tmp/current.txt"
    printf '%s\n' "$rows" > "$cur"
    grep -v '^RAW_SITE=\|^STORE_READ_CODE_SITE=\|^STORE_READ_SPEC_SITE=' "$st_base" >> "$cur"
    if diff -q <(grep -v '^RAW_SITE=\|^STORE_READ_CODE_SITE=\|^STORE_READ_SPEC_SITE=' "$st_base") \
                <(grep -v '^RAW_SITE=\|^STORE_READ_CODE_SITE=\|^STORE_READ_SPEC_SITE=' "$cur") >/dev/null; then
      : # scalars identical, as required
    else
      echo "  SELF-TEST BROKEN: case '$name' perturbed a scalar metric" >&2
      st_failed=1
      return
    fi
    if diff -q <(grep '^RAW_SITE=\|^STORE_READ_CODE_SITE=\|^STORE_READ_SPEC_SITE=' "$st_base" | sort) \
                <(grep '^RAW_SITE=\|^STORE_READ_CODE_SITE=\|^STORE_READ_SPEC_SITE=' "$cur" | sort) >/dev/null \
       && [[ "$expect" == "fail" ]]; then
      echo "  SELF-TEST BROKEN: case '$name' is inert (mutation changed nothing)" >&2
      st_failed=1
      return
    fi
    local out status=0
    out="$(STORE_READER_BASELINE_FILE="$st_base" STORE_READER_SELFTEST_CURRENT="$cur" \
             bash "$0" --internal-compare 2>&1)" || status=$?
    if [[ "$expect" == "fail" && "$status" -eq 0 ]]; then
      echo "  SELF-TEST FAIL: '$name' should have been rejected but passed" >&2
      st_failed=1
    elif [[ "$expect" == "pass" && "$status" -ne 0 ]]; then
      echo "  SELF-TEST FAIL: '$name' should have passed but was rejected" >&2
      printf '%s\n' "$out" >&2
      st_failed=1
    else
      echo "  OK   self-test '$name' ($expect)"
    fi
  }

  # `<name> <expect> <baseline STORE_READ_CODE> <current STORE_READ_CODE>
  #  <current STORE_READ_SPEC> <current-inventory rows> [unchanged]`.  The
  # census metrics MOVE here, which is the point, so the harness's assertion is
  # the other one: the fixture must be internally consistent (each total equal
  # to the sum of its own site rows), or the case would be exercising a capture
  # the gate rejects as a defect rather than the property under test.
  #
  # A seventh argument `unchanged` declares that the case's current file is the
  # baseline, deliberately -- the zero-floor case, where "the baseline says the
  # same thing" is precisely the excuse being refused and the ordinary inert
  # guard would reject the one case that matters.  The guard compares SORTED
  # content, so it does not pass a case on row order.
  st_census_case() {
    local name="$1" expect="$2" base_code="$3" cur_code="$4" cur_spec="$5" rows="$6"
    local unchanged="${7:-}"
    local base="$st_tmp/census_baseline.txt" cur="$st_tmp/census_current.txt"
    local scalars
    scalars="$(grep -v '^RAW_SITE=\|^STORE_READ_CODE_SITE=\|^STORE_READ_SPEC_SITE=\|^STORE_READ_CODE=\|^STORE_READ_SPEC=' \
      "$st_base" || true)"
    { printf '%s\n' "$scalars"
      printf 'RAW_SITE=SeLe4n/Kernel/A.lean|foo|tcb|2\n'
      printf 'RAW_SITE=SeLe4n/Kernel/B.lean|bar|tcb|1\n'
      printf 'STORE_READ_SPEC_SITE=SeLe4n/Kernel/A.lean|frame|9\n'
      if (( base_code > 0 )); then
        printf 'STORE_READ_CODE_SITE=SeLe4n/Kernel/A.lean|step|%s\n' "$base_code"
      fi
      printf 'STORE_READ_CODE=%s\nSTORE_READ_SPEC=9\n' "$base_code"
    } > "$base"
    { printf '%s\n' "$scalars"
      printf '%s\n' "$rows"
      printf 'STORE_READ_CODE=%s\nSTORE_READ_SPEC=%s\n' "$cur_code" "$cur_spec"
    } > "$cur"
    # The fixture must be internally consistent, or the case would exercise the
    # gate-defect branch rather than the property under test.
    local f declared summed
    for f in "$base" "$cur"; do
      declared="$(grep '^STORE_READ_CODE=' "$f" | cut -d= -f2)"
      summed="$(grep '^STORE_READ_CODE_SITE=' "$f" 2>/dev/null || true)"
      summed="$(printf '%s\n' "$summed" | awk -F'|' 'NF > 1 {s += $NF} END {print s + 0}')"
      if [[ "$declared" != "$summed" ]]; then
        echo "  SELF-TEST BROKEN: case '$name' fixture is inconsistent (CODE=$declared, sites sum to $summed)" >&2
        st_failed=1
        return
      fi
    done
    if diff -q <(sort "$base") <(sort "$cur") >/dev/null 2>&1; then
      if [[ "$unchanged" != "unchanged" ]]; then
        echo "  SELF-TEST BROKEN: case '$name' is inert (mutation changed nothing)" >&2
        st_failed=1
        return
      fi
    elif [[ "$unchanged" == "unchanged" ]]; then
      echo "  SELF-TEST BROKEN: case '$name' declares itself unchanged but differs from the baseline" >&2
      st_failed=1
      return
    fi
    local out status=0
    out="$(STORE_READER_BASELINE_FILE="$base" STORE_READER_SELFTEST_CURRENT="$cur" \
             bash "$0" --internal-compare 2>&1)" || status=$?
    if [[ "$expect" == "fail" && "$status" -eq 0 ]]; then
      echo "  SELF-TEST FAIL: '$name' should have been rejected but passed" >&2
      st_failed=1
    elif [[ "$expect" == "pass" && "$status" -ne 0 ]]; then
      echo "  SELF-TEST FAIL: '$name' should have passed but was rejected" >&2
      printf '%s\n' "$out" >&2
      st_failed=1
    else
      echo "  OK   self-test '$name' ($expect)"
    fi
  }

  st_case "clean tree" pass \
'RAW_SITE=SeLe4n/Kernel/A.lean|foo|tcb|2
RAW_SITE=SeLe4n/Kernel/B.lean|bar|tcb|1
STORE_READ_SPEC_SITE=SeLe4n/Kernel/A.lean|frame|9'

  # TOKEN-PRESERVING: B gives one up, C gains one. RAW_MATCH_TCB stays 3.
  st_case "a raw read moved to an unpinned file (totals unchanged)" fail \
'RAW_SITE=SeLe4n/Kernel/A.lean|foo|tcb|2
RAW_SITE=SeLe4n/Kernel/C.lean|baz|tcb|1
STORE_READ_SPEC_SITE=SeLe4n/Kernel/A.lean|frame|9'

  # TOKEN-PRESERVING: same key set, one file gains a second occurrence and the
  # other gives one up. A set-of-pairs floor with no counts passes this.
  st_case "a second raw read inside an already-pinned file" fail \
'RAW_SITE=SeLe4n/Kernel/A.lean|foo|tcb|3
RAW_SITE=SeLe4n/Kernel/B.lean|bar|tcb|0
STORE_READ_SPEC_SITE=SeLe4n/Kernel/A.lean|frame|9'

  # TOKEN-PRESERVING: the variant changes, the file and the total do not.
  st_case "a pinned site changed variant" fail \
'RAW_SITE=SeLe4n/Kernel/A.lean|foo|tcb|2
RAW_SITE=SeLe4n/Kernel/B.lean|bar|schedContext|1
STORE_READ_SPEC_SITE=SeLe4n/Kernel/A.lean|frame|9'

  # TOKEN-PRESERVING, and the round-6 shape: the swap stays INSIDE one file and
  # moves between declarations.  `foo` gives one up and `qux` gains one, so the
  # file's total, the variant's total and every scalar are identical -- which is
  # exactly what a (file, variant) key could not see, and what the declaration
  # component turns into a key the baseline does not name.
  st_case "a raw read moved between declarations of one pinned file" fail \
'RAW_SITE=SeLe4n/Kernel/A.lean|foo|tcb|1
RAW_SITE=SeLe4n/Kernel/A.lean|qux|tcb|1
RAW_SITE=SeLe4n/Kernel/B.lean|bar|tcb|1
STORE_READ_SPEC_SITE=SeLe4n/Kernel/A.lean|frame|9'

  # The migration working must not be a failure.
  st_case "a pinned site hygienized away" pass \
'RAW_SITE=SeLe4n/Kernel/A.lean|foo|tcb|1
RAW_SITE=SeLe4n/Kernel/B.lean|bar|tcb|1
STORE_READ_SPEC_SITE=SeLe4n/Kernel/A.lean|frame|9'

  # ---- census cases: the zero floor ------------------------------------
  #
  # A read that MOVED FROM SPEC INTO CODE: the two populations' SUM is
  # unchanged, which is exactly what the superseded `RAW_LOOKUP_TID` measured,
  # so the superseded gate admitted this and the split one must not.
  st_census_case "a store read moved from a proposition into a transition" fail 0 1 8 \
'RAW_SITE=SeLe4n/Kernel/A.lean|foo|tcb|2
RAW_SITE=SeLe4n/Kernel/B.lean|bar|tcb|1
STORE_READ_CODE_SITE=SeLe4n/Kernel/A.lean|step|1
STORE_READ_SPEC_SITE=SeLe4n/Kernel/A.lean|frame|8'

  # ...and writing a new invariant is the other direction, which must PASS, or
  # the spec population would be enforced by the back door.
  st_census_case "a new proposition reads the store" pass 0 0 10 \
'RAW_SITE=SeLe4n/Kernel/A.lean|foo|tcb|2
RAW_SITE=SeLe4n/Kernel/B.lean|bar|tcb|1
STORE_READ_SPEC_SITE=SeLe4n/Kernel/A.lean|frame|10'

  # NOT A CEILING: baseline and current agree at one, which is the whole of
  # what a `:drop` metric asks, so the superseded treatment passed this.  A
  # zero floor cannot be satisfied by a matching baseline -- that is the
  # difference between "no worse than last time" and "none", and it is the
  # difference the four upward re-anchorings of `RAW_LOOKUP_TID` exploited.
  st_census_case "an executable read the baseline also carries" fail 1 1 9 \
'RAW_SITE=SeLe4n/Kernel/A.lean|foo|tcb|2
RAW_SITE=SeLe4n/Kernel/B.lean|bar|tcb|1
STORE_READ_CODE_SITE=SeLe4n/Kernel/A.lean|step|1
STORE_READ_SPEC_SITE=SeLe4n/Kernel/A.lean|frame|9' unchanged

  # The total and the inventory are two readings of one census.  A capture
  # claiming the population is empty while naming a live site is a gate defect
  # -- the shape a hand-edited or truncated baseline takes -- and must be
  # refused rather than passed on the strength of the total alone.
  st_inconsistent_case() {
    local base="$st_tmp/incons_baseline.txt" cur="$st_tmp/incons_current.txt"
    grep -v '^RAW_SITE=\|^STORE_READ_CODE_SITE=\|^STORE_READ_SPEC_SITE=' "$st_base" > "$base"
    printf 'RAW_SITE=SeLe4n/Kernel/A.lean|foo|tcb|2\nRAW_SITE=SeLe4n/Kernel/B.lean|bar|tcb|1\n' >> "$base"
    printf 'STORE_READ_SPEC_SITE=SeLe4n/Kernel/A.lean|frame|9\n' >> "$base"
    cp "$base" "$cur"
    printf 'STORE_READ_CODE_SITE=SeLe4n/Kernel/A.lean|step|1\n' >> "$cur"
    local status=0
    STORE_READER_BASELINE_FILE="$base" STORE_READER_SELFTEST_CURRENT="$cur" \
      bash "$0" --internal-compare >/dev/null 2>&1 || status=$?
    if (( status == 0 )); then
      echo "  SELF-TEST FAIL: 'a site row the total does not count' should have been rejected" >&2
      st_failed=1
    else
      echo "  OK   self-test 'a site row the total does not count' (fail)"
    fi
  }
  st_inconsistent_case

  if (( st_failed != 0 )); then
    echo "[ak7-monotonicity] Self-test FAILED." >&2
    exit 1
  fi
  echo "[ak7-monotonicity] Self-test passed (10 cases: 6 inventory mutations with"
  echo "                   every scalar held fixed, 3 census mutations, 1 inconsistent capture)."
  exit 0
fi

if [[ ! -f "$BASELINE_FILE" ]]; then
  echo "[ak7-monotonicity] Baseline not found: $BASELINE_FILE" >&2
  echo "[ak7-monotonicity] Run: bash scripts/ak7_cascade_baseline.sh > $BASELINE_FILE" >&2
  exit 1
fi

# Capture current state via the baseline script -- or, under `--internal-compare`
# (the self-test's own re-entry), read a synthesized one, so the comparison logic
# below is exercised on fixtures without touching the tree.
if [[ "${1:-}" == "--internal-compare" ]]; then
  CURRENT_FILE="${STORE_READER_SELFTEST_CURRENT:?--internal-compare needs STORE_READER_SELFTEST_CURRENT}"
else
  CURRENT_FILE=$(mktemp)
  trap 'rm -f "$CURRENT_FILE"' EXIT
  bash scripts/ak7_cascade_baseline.sh > "$CURRENT_FILE"
fi

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
  # RAW_MATCH_UNCLASSIFIED is deliberately NOT enforced (PR #893 review).  A raw
  # match that binds the whole `KernelObject` without naming a constructor is
  # not a reader-hygiene site -- the baseline script says so at the point it
  # computes the figure -- so holding it to a drop would make a legitimate
  # non-discriminating match a hard Tier 0 failure, refusing code this migration
  # has no quarrel with.  The variant-discriminating reads are enforced, per
  # site, by the RAW_SITE inventory below, which is the binding floor; this
  # figure is a diagnostic and its comment now matches its treatment.
  # The object-store read census.  `STORE_READ_CODE` -- the migratable
  # population, a raw read in the body of a declaration whose result is not a
  # `Prop` -- is NOT here: it is **zero**, and is enforced as zero in
  # `ZERO_METRICS` below rather than held to a ceiling.  `STORE_READ_SPEC` is
  # deliberately NOT enforced in either direction: a proposition about the
  # store has no helper form (`getTcb? k = none` holds for an absent key and a
  # wrong-kinded object alike, so a frame statement quantified over every key
  # cannot be phrased through a variant accessor without weakening it), so
  # holding it to a drop would make writing an invariant a hard Tier 0 failure.
  # It is reported by the baseline for readers, exactly as
  # `RAW_MATCH_UNCLASSIFIED` is.
  #
  # This pair replaced `RAW_LOOKUP_TID`, which summed both populations into one
  # number that was 96.9% specification -- so it rose on every invariant cut
  # and was re-anchored upward four times in three days, which is a ratchet
  # running backwards rather than a floor.
  "GETTCB_ADOPTION:grow"
  "GETSCHEDCTX_ADOPTION:grow"
  "GETENDPOINT_ADOPTION:grow"
  "GETNOTIFICATION_ADOPTION:grow"
  "GETUNTYPED_ADOPTION:grow"
  "GETCNODE_ADOPTION:grow"
  "GETVSPACEROOT_ADOPTION:grow"
  "STOREOBJECTCHECKED_ADOPTION:grow"
  "SENTINEL_CHECK_DISPATCH:grow"
  "READER_HYGIENE_SUITE_TESTS:grow"
  "KERRORMATRIX_ROWS:grow"
)

# Zero-floor metrics: any positive value is a regression, and the floor is not
# a number anyone may re-anchor.  That distinction is the whole point, and it is
# what `RAW_LOOKUP_TID` lacked: a ceiling invites the next cut that exceeds it
# to raise the ceiling, which happened four times in three days and made the
# figure meaningless.  A zero here cannot be relaxed by regenerating the
# baseline -- only by editing this list, which is a visible, reviewable act.
#
# `STORE_READ_CODE` joined them once the migration reached zero: every store
# read in the tree outside `SeLe4n/Model/State.lean` -- where the typed
# accessors are defined and the raw read IS their body -- now sits in a
# proposition.  So a raw read appearing in an executable position is not "one
# more than before", it is the first, and the gate says so.
ZERO_METRICS=(
  "SORRY_COUNT"
  "AXIOM_COUNT"
  "STORE_READ_CODE"
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

# ---------------------------------------------------------------------------
# The binding floor: the raw-read site inventory.
#
# `check_inventory <key> <label>` compares the baseline's `<key>=<id>|<count>`
# rows against the current tree's. Two distinct failures, because the property
# has two halves and either alone is satisfiable while the other is violated:
#
#   NEW SITE   — a key the baseline does not name at all. Always a regression,
#                whatever the totals do: this is the raw pattern appearing
#                somewhere it had been driven out of.
#   GREW       — a key the baseline names, whose count rose. This is the second
#                occurrence inside a file that already had one, which a set of
#                keys alone cannot see.
#
# A key that fell, or vanished, is the migration working and is reported as
# progress (the baseline may be re-anchored to lock the gain in, but a stale
# high floor is never a failure).
# ---------------------------------------------------------------------------
inventory_rows() {
  local key="$1" file="$2"
  grep "^${key}=" "$file" 2>/dev/null | sed "s/^${key}=//" || true
}

check_inventory() {
  local key="$1" label="$2"
  local base_rows cur_rows
  base_rows="$(inventory_rows "$key" "$BASELINE_FILE")"
  cur_rows="$(inventory_rows "$key" "$CURRENT_FILE")"

  local new_sites=0 grew=0 improved=0
  local row id count base_count
  while IFS= read -r row; do
    [[ -z "$row" ]] && continue
    id="${row%|*}"
    count="${row##*|}"
    base_count="$(printf '%s\n' "$base_rows" \
      | awk -F'|' -v k="$id" 'substr($0, 1, length(k) + 1) == k "|" {print $NF; found=1}
                              END {if (!found) print ""}' | head -1)"
    if [[ -z "$base_count" ]]; then
      echo "  REGRESSION (new raw-read site): ${label}  ${id}  count=${count}" >&2
      echo "    This site is not in the baseline. A raw discriminator read has" >&2
      echo "    appeared where the migration had driven it out; the whole-tree" >&2
      echo "    totals cannot see this, which is why the inventory is the floor." >&2
      new_sites=$((new_sites + 1))
    elif (( count > base_count )); then
      echo "  REGRESSION (raw-read site grew): ${label}  ${id}  current=${count}  baseline=${base_count}" >&2
      grew=$((grew + 1))
    fi
  done <<< "$cur_rows"

  while IFS= read -r row; do
    [[ -z "$row" ]] && continue
    id="${row%|*}"
    base_count="${row##*|}"
    count="$(printf '%s\n' "$cur_rows" \
      | awk -F'|' -v k="$id" 'substr($0, 1, length(k) + 1) == k "|" {print $NF; found=1}
                              END {if (!found) print 0}' | head -1)"
    if (( count < base_count )); then
      improved=$((improved + 1))
    fi
  done <<< "$base_rows"

  if (( new_sites != 0 || grew != 0 )); then
    failed=1
  else
    local total
    total="$(printf '%s\n' "$base_rows" | awk 'NF' | wc -l)"
    if (( improved > 0 )); then
      echo "  OK   ${label}  ${total} pinned site(s); ${improved} improved below floor"
    else
      echo "  OK   ${label}  ${total} pinned site(s), none new, none grown"
    fi
  fi
}

check_inventory "RAW_SITE" "raw variant-discriminating reads"

# `STORE_READ_CODE` gets no inventory floor, because at zero a cardinality and
# a set say the same thing and this file must not answer one question twice.
# What it gets instead is the relation between them, asserted rather than
# assumed: the total is the sum over the site rows.  Both are read out of the
# same file here, so a hand-edited or truncated capture claiming `=0` beside a
# live site row is a gate defect, not a pass.
site_sum() {
  local key="$1" file="$2" rows
  # `grep` exits 1 on no match and `pipefail` is on, so the empty case -- which
  # is the one this gate exists to keep -- must not look like a failure.
  rows="$(grep "^${key}=" "$file" 2>/dev/null || true)"
  printf '%s\n' "$rows" | awk -F'|' 'NF > 1 {s += $NF} END {print s + 0}'
}

for file_label in "baseline:$BASELINE_FILE" "current:$CURRENT_FILE"; do
  label="${file_label%%:*}"
  file="${file_label#*:}"
  declared=$(read_metric "STORE_READ_CODE" "$file")
  summed=$(site_sum "STORE_READ_CODE_SITE" "$file")
  if (( declared != summed )); then
    echo "  GATE DEFECT: ${label} STORE_READ_CODE=${declared} but its site rows sum to ${summed}" >&2
    echo "    The total and the inventory are two readings of one census and" >&2
    echo "    must agree; a capture where they do not is not evidence of" >&2
    echo "    anything." >&2
    failed=1
  fi
done

for metric in "${ZERO_METRICS[@]}"; do
  current=$(read_metric "$metric" "$CURRENT_FILE")
  if (( current > 0 )); then
    echo "  REGRESSION (should-stay-zero): $metric  current=$current" >&2
    if [[ "$metric" == "STORE_READ_CODE" ]]; then
      echo "    A raw object-store read has appeared in an executable position." >&2
      echo "    Read it through the typed accessor for the kind the site" >&2
      echo "    discriminates (\`getTcb?\`, \`getEndpoint?\`, ...), or through" >&2
      echo "    \`getObject?\` / \`getObjectType?\` where the read is genuinely" >&2
      echo "    kind-agnostic.  Sites:" >&2
      grep "^STORE_READ_CODE_SITE=" "$CURRENT_FILE" 2>/dev/null \
        | sed 's/^STORE_READ_CODE_SITE=/      /' >&2
    fi
    failed=1
  else
    echo "  OK   $metric  0"
  fi
done

if (( failed != 0 )); then
  echo "" >&2
  echo "[ak7-monotonicity] One or more AK7 cascade metrics regressed." >&2
  echo "[ak7-monotonicity] For a should-drop or should-grow metric, and for the" >&2
  echo "[ak7-monotonicity] raw-read site inventory: either restore the value" >&2
  echo "[ak7-monotonicity] (preferred) or, after a documented refactor," >&2
  echo "[ak7-monotonicity] re-anchor the baseline:" >&2
  echo "  bash scripts/ak7_cascade_baseline.sh > $BASELINE_FILE" >&2
  echo "[ak7-monotonicity] For a should-stay-zero metric -- SORRY_COUNT," >&2
  echo "[ak7-monotonicity] AXIOM_COUNT, STORE_READ_CODE -- re-anchoring does" >&2
  echo "[ak7-monotonicity] NOTHING: the floor is zero, not the recorded value," >&2
  echo "[ak7-monotonicity] and only fixing the tree clears it." >&2
  exit 1
fi

echo "[ak7-monotonicity] All AK7 cascade metrics pass."
