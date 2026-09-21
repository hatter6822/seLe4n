#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AN11-E.10 (TST-M12) — testing-framework self-test (umbrella script).
#
# This script is the canonical "test the testing infrastructure" runner:
# it walks every tier (`test_fast.sh`, `test_smoke.sh`, `test_full.sh`,
# `test_nightly.sh`), then runs the Tier 4 nightly candidates with
# `NIGHTLY_ENABLE_EXPERIMENTAL=1`, then mutates the real trace fixture five
# ways and asserts that `test_tier2_trace.sh` rejects each one FOR THE REASON
# THAT MUTATION IS ABOUT (catching a class of "fixture compare silently
# passing" bugs -- including, since `v0.35.113`, in this script: the control
# these replace was refused by the fixture-path guard and never reached the
# comparison at all).  Run them alone with `--controls-only`.
#
# **When to run**: before bumping Lean/Lake/elan toolchain versions, or
# after editing `scripts/test_lib.sh` / `scripts/_common.sh` / a tier-N
# script.  This is the meta-gate that every other gate hides behind.
#
# **Why not wire into Tier 4**: integrating this into
# `test_tier4_nightly_candidates.sh` would create a circular run (this
# script invokes `test_tier4_nightly_candidates.sh` already), so it is
# documented here and in `CLAUDE.md` as a manual umbrella check rather
# than auto-wired into a tier.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${ROOT_DIR}"

# `--controls-only` runs the Tier 2 trace-gate controls alone, skipping the tier
# stack above them.  They are seconds where the stack is tens of minutes, and a
# control nobody can run on its own is a control nobody re-runs after touching
# the gate it is about -- which is how the superseded one stayed inert.
CONTROLS_ONLY=0
for arg in "$@"; do
  case "${arg}" in
    --controls-only) CONTROLS_ONLY=1 ;;
    *) echo "usage: $0 [--controls-only]" >&2; exit 2 ;;
  esac
done

# A tier that reports incomplete coverage exits `SELE4N_SKIP_EXIT` (77) rather
# than 0, so that a gate which did not run is never scored as one that passed.
# Under `set -e` a bare invocation would abort this script at the first such
# tier — and on every checkout without a kernel image that is `test_nightly.sh`,
# four lines before the control-fixture check this audit exists to perform.
# Tolerate the status, say so, and carry on; anything else still aborts.
SELE4N_SKIP_EXIT="${SELE4N_SKIP_EXIT:-77}"
run_tier() {
  local rc=0
  "$@" || rc=$?
  if [[ "${rc}" -eq 0 ]]; then
    return 0
  fi
  if [[ "${rc}" -eq "${SELE4N_SKIP_EXIT}" ]]; then
    echo "[AUDIT] NOT RUN (incomplete coverage): $* — see that tier's output for the gates it skipped"
    return 0
  fi
  echo "[AUDIT] FAILED (exit ${rc}): $*" >&2
  return "${rc}"
}

# ---------------------------------------------------------------------------
# v0.35.113: five controls, each identified by the REASON the gate gives.
#
# The superseded control copied the fixture to a `mktemp` path and asserted that
# `test_tier2_trace.sh` failed.  It did fail -- at the `TRACE_FIXTURE_PATH must
# be a git-tracked file` guard, which refuses any path outside the index, so the
# control never reached the comparison it claimed to exercise and would have
# reported success with that comparison deleted outright.  This script's own
# header says it exists to catch "fixture compare silently passing" bugs, and it
# was passing silently; the bug it names is the one PR #897's review then found.
# "The gate could not read it" and "the gate checked it and it differs" must
# never produce the same verdict -- the rule this tree already states for
# `check_anchor_consistency.py`, here in the FAIL direction.
#
# So the fixture is mutated IN PLACE, which is the only way to reach the
# comparison: the guard is a security property and must not be widened, and the
# checksum sweep runs first, so the `.sha256` companion is refreshed too -- the
# mutation is exactly the consistent fixture edit a maintainer makes, which is
# what the comparison has to adjudicate.  Both files are restored from the index
# after every control and the restoration is verified, so a crashed run is loud
# rather than a silently edited fixture.
#
# Each control asserts WHICH failure fired and, where the claim is that one
# direction alone decides, that the others stayed silent:
#
#   1. a line appended   -> the forward direction (an expectation with no line)
#   2. a line deleted    -> the reverse direction (a line with no expectation)
#   3. two lines swapped -> the SEQUENCE comparison ALONE
#   4. a line duplicated -> the SEQUENCE comparison ALONE
#   5. an untracked path -> the injection guard, and none of the above
#
# 3 and 4 are the ones that decide, because the multiset is unchanged: measured
# against the pre-v0.35.113 gate, the transposition passed and the duplication
# passed while reporting `240/240` against a 239-line trace.
# ---------------------------------------------------------------------------
CONTROL_FIXTURE="tests/fixtures/main_trace_smoke.expected"
CONTROL_HASH="${CONTROL_FIXTURE}.sha256"
CONTROL_LOG="$(mktemp)"
CONTROL_SCRATCH="$(mktemp)"
CONTROL_UNTRACKED="$(mktemp)"

# The controls mutate the real fixture in place and restore it from the index
# between each one, which is the only way to reach the comparison (the fixture-path
# guard refuses any path outside the index -- see the block above).  That restore
# DESTROYS an unstaged edit, and a maintainer editing a fixture is exactly who runs
# `--controls-only`: it is seconds where the tier stack is tens of minutes.
#
# So the script takes OWNERSHIP of the two control files before it touches them,
# and refuses when they are dirty.  Two things make the refusal sound rather than
# cosmetic.  It is fail-closed: "I could not run" and "I ran and the gate passed"
# must not produce the same verdict, so the refusal is a non-zero exit with the
# reason, never a skip.  And the ownership flag is what the trap reads, because the
# trap is installed before the check can run -- without it, a refusal would fire
# the very restore it exists to prevent.
#
# A STAGED edit is not dirty and is preserved: `git checkout --` restores from the
# index, so the content the script puts back is the content the maintainer staged.
# `git diff --quiet` asks precisely the unstaged question, which is the one that
# loses work.  That is the supported workflow -- regenerate the fixture, stage it,
# re-run the controls -- and it is also why a STAGED edit is not refused: the
# controls are measured against the INDEXED fixture, so if that content does not
# describe the trace a control fails loudly on the first run rather than the
# harness silently scoring a bad baseline.  A control failure there is the harness
# reporting the staged fixture, not a defect in the harness.
CONTROL_FIXTURE_OWNED=0

restore_control_fixture() {
  if [[ "${CONTROL_FIXTURE_OWNED}" -ne 1 ]]; then
    return 0
  fi
  git checkout -- "${CONTROL_FIXTURE}" "${CONTROL_HASH}" 2>/dev/null || true
}
trap 'restore_control_fixture; rm -f "${CONTROL_LOG}" "${CONTROL_SCRATCH}" "${CONTROL_UNTRACKED}"' EXIT INT TERM

# Taken BEFORE the tier stack, not before the controls: with the check inside
# `run_trace_gate_controls` a full run would spend tens of minutes and then
# discard the edits, which is worse than discarding them at once.  A legitimately
# regenerated fixture also makes the tier stack PASS, so nothing earlier would
# have refused.
take_control_fixture_ownership() {
  if ! git diff --quiet -- "${CONTROL_FIXTURE}" "${CONTROL_HASH}"; then
    echo "[AUDIT] ERROR: refusing to run -- the trace-gate controls mutate these files in place and restore them from the git index, which would permanently discard your unstaged edits:" >&2
    git diff --stat -- "${CONTROL_FIXTURE}" "${CONTROL_HASH}" >&2
    echo "[AUDIT] Commit or stash them (or \`git add\` them, which this script preserves) and re-run." >&2
    exit 1
  fi
  CONTROL_FIXTURE_OWNED=1
}

refresh_control_hash() {
  (cd "$(dirname "${CONTROL_FIXTURE}")" \
     && sha256sum "$(basename "${CONTROL_FIXTURE}")" > "$(basename "${CONTROL_HASH}")")
}

# The four failure messages the trace gate can give, as the substrings that
# identify each one.  Named once: a control that asserted its own spelling of a
# message would be a second answer to "what does this gate say".
CONTROL_REASON_FORWARD="Missing expected trace line"
CONTROL_REASON_REVERSE="not accounted for by any fixture expectation"
CONTROL_REASON_SEQUENCE="is not the sequence"
CONTROL_REASON_GUARD="must be a git-tracked file"

# $1 = control name, $2 = the reason that MUST appear, $3.. = reasons that must
# NOT appear.  A control whose gate run SUCCEEDS is a control that asserts
# nothing, and so is one that fails for a reason other than its own subject.
assert_trace_gate_rejects() {
  local name="$1" want="$2"
  shift 2
  local rc=0
  if [[ -n "${CONTROL_FIXTURE_OVERRIDE:-}" ]]; then
    TRACE_FIXTURE_PATH="${CONTROL_FIXTURE_OVERRIDE}" \
      "${SCRIPT_DIR}/test_tier2_trace.sh" > "${CONTROL_LOG}" 2>&1 || rc=$?
  else
    "${SCRIPT_DIR}/test_tier2_trace.sh" > "${CONTROL_LOG}" 2>&1 || rc=$?
  fi
  if [[ "${rc}" -eq 0 ]]; then
    echo "[AUDIT] ERROR: control '${name}' did not fail Tier 2 -- the trace gate accepts a fixture that does not describe the trace" >&2
    exit 1
  fi
  if ! grep -Fq "${want}" "${CONTROL_LOG}"; then
    echo "[AUDIT] ERROR: control '${name}' failed Tier 2 for the wrong reason; expected a message containing: ${want}" >&2
    sed -n '1,40p' "${CONTROL_LOG}" >&2
    exit 1
  fi
  local unwanted
  for unwanted in "$@"; do
    if grep -Fq "${unwanted}" "${CONTROL_LOG}"; then
      echo "[AUDIT] ERROR: control '${name}' also reported '${unwanted}' -- this control is meant to be decided by its own subject alone, and a verdict two checks share cannot show that either one of them decides" >&2
      exit 1
    fi
  done
  echo "[AUDIT] Control '${name}': rejected, reason '${want}'"
}

assert_control_fixture_restored() {
  if ! git diff --quiet -- "${CONTROL_FIXTURE}" "${CONTROL_HASH}"; then
    echo "[AUDIT] ERROR: the control fixture was not restored to its indexed content" >&2
    exit 1
  fi
}

run_trace_gate_controls() {
  restore_control_fixture
  assert_control_fixture_restored

  # 1. An expectation with no trace line: the forward direction.
  printf '%s\n' '[CONTROL] impossible expected line' >> "${CONTROL_FIXTURE}"
  refresh_control_hash
  assert_trace_gate_rejects "appended expectation" "${CONTROL_REASON_FORWARD}"
  restore_control_fixture
  assert_control_fixture_restored

  # 2. A trace line with no expectation: the reverse direction.  The sequence
  #    comparison fires here too, which is why it is not forbidden -- what this
  #    control asserts is that the reverse direction is still live.
  sed -i '$d' "${CONTROL_FIXTURE}"
  refresh_control_hash
  assert_trace_gate_rejects "deleted expectation" "${CONTROL_REASON_REVERSE}" \
    "${CONTROL_REASON_FORWARD}"
  restore_control_fixture
  assert_control_fixture_restored

  # 3. Two expectations transposed: the multiset is unchanged, so BOTH
  #    containment directions hold and only the sequence comparison decides.
  awk 'NR==1{first=$0;next} NR==2{print;print first;next} {print}' \
    "${CONTROL_FIXTURE}" > "${CONTROL_SCRATCH}"
  cp "${CONTROL_SCRATCH}" "${CONTROL_FIXTURE}"
  refresh_control_hash
  assert_trace_gate_rejects "transposed expectations" "${CONTROL_REASON_SEQUENCE}" \
    "${CONTROL_REASON_FORWARD}" "${CONTROL_REASON_REVERSE}"
  restore_control_fixture
  assert_control_fixture_restored

  # 4. One expectation duplicated: every expectation still occurs and every
  #    trace line is still accounted for, so again only the sequence decides.
  #    The pre-v0.35.113 gate reported `240/240` on this against 239 lines.
  awk 'NR==1{print;print;next} {print}' \
    "${CONTROL_FIXTURE}" > "${CONTROL_SCRATCH}"
  cp "${CONTROL_SCRATCH}" "${CONTROL_FIXTURE}"
  refresh_control_hash
  assert_trace_gate_rejects "duplicated expectation" "${CONTROL_REASON_SEQUENCE}" \
    "${CONTROL_REASON_FORWARD}" "${CONTROL_REASON_REVERSE}"
  restore_control_fixture
  assert_control_fixture_restored

  # 5. An untracked fixture path: the injection guard refuses it, and the
  #    refusal must be distinguishable from every comparison verdict above --
  #    which is the defect this whole block replaces.
  cp "${CONTROL_FIXTURE}" "${CONTROL_UNTRACKED}"
  # An assignment prefixed to a FUNCTION call persists in bash outside POSIX
  # mode, so the override is set and cleared explicitly rather than inline.
  CONTROL_FIXTURE_OVERRIDE="${CONTROL_UNTRACKED}"
  assert_trace_gate_rejects "untracked fixture path" "${CONTROL_REASON_GUARD}" \
    "${CONTROL_REASON_FORWARD}" "${CONTROL_REASON_REVERSE}" \
    "${CONTROL_REASON_SEQUENCE}"
  CONTROL_FIXTURE_OVERRIDE=""
  assert_control_fixture_restored

  echo "[AUDIT] Trace-gate controls: 5 of 5 rejected, each by its own subject"
}

take_control_fixture_ownership

if [[ "${CONTROLS_ONLY}" -eq 1 ]]; then
  echo "[AUDIT] Verifying Tier 2 control-data failure behavior (controls only)"
  run_trace_gate_controls
  echo "[AUDIT] Trace-gate control audit completed successfully"
  exit 0
fi

echo "[AUDIT] Running baseline tiered entrypoint checks"
run_tier "${SCRIPT_DIR}/test_fast.sh"
run_tier "${SCRIPT_DIR}/test_smoke.sh"
run_tier "${SCRIPT_DIR}/test_full.sh"
run_tier "${SCRIPT_DIR}/test_nightly.sh"

echo "[AUDIT] Running Tier 4 staged candidates in experimental mode"
NIGHTLY_ENABLE_EXPERIMENTAL=1 run_tier "${SCRIPT_DIR}/test_tier4_nightly_candidates.sh"

echo "[AUDIT] Verifying Tier 2 control-data failure behavior"
run_trace_gate_controls
echo "[AUDIT] Testing framework audit completed successfully"
