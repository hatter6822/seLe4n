#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# Re-run the tier anchors whose subject this cut changes.
#
# `CLAUDE.md` states this sweep as a PROCEDURE, with the `rg` command to run and
# the arithmetic: *seconds against tens of minutes per iteration.*  Four
# consecutive cuts then shipped an anchor the procedure would have caught, each
# found fifty minutes into the Full lane:
#
#   * `v0.35.116` moved a table parse and THREE anchors over the old home went
#     silent, of which the Tier 3 run reported one.
#   * `v0.35.118` widened a regex, deleting the line a `v0.35.115` positive pinned.
#   * `v0.35.119` hoisted a classifier, leaving a loop binding unused; it became
#     `_ns`, and a `v0.35.117` anchor had pinned `for ns, files in ...` verbatim.
#     Tier 3 stopped there, so the 21 anchors that cut ADDED never ran at all.
#   * `v0.35.121` bound a state once, retiring the inline spelling a `v0.35.86`
#     positive pinned -- found by the ad-hoc form of this sweep, in seconds.
#
# A rule restated four times and broken four times is owed a check.  This is the
# execution half; `scripts/select_changed_anchors.py` is the selection half, and
# they are two files for one reason: an anchor's verdict must come from the tier
# suites' own `run_check` / `run_negative_check`, so this gate and Tier 3 cannot
# disagree about any anchor, and those helpers live in bash.
#
# WHY THIS AND NOT A BIGGER SATISFIABILITY GATE.  `check_anchor_consistency.py`
# decides whether two anchors CONTRADICT; it cannot decide whether a positive is
# currently SATISFIED, which is what all four cuts above broke.  And for the
# bounded-gap family -- now the tree's dominant anchor form -- it is structurally
# limited to exact-key matching, because `_literal_runs` refuses a quantifier or a
# class.  Running the anchor is the only thing that answers the question.
#
# Usage:
#   check_changed_file_anchors.sh [--continue]
#   check_changed_file_anchors.sh --selection FILE [--continue]   # a prepared set
#   check_changed_file_anchors.sh --controls                      # decisiveness
#
# `--selection` is the seam the controls use, in the shape
# `check_anchor_consistency.py --self-test` and `audit_testing_framework.sh`
# already use: a synthetic input driven through the real dispatch, because a gate
# whose decisiveness is asserted rather than exercised is indistinguishable from
# one that is wrong.
#
# Exit status: 0 when every swept anchor decides as declared, 1 otherwise.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Extract this script's own flags before `parse_common_args`, which rejects
# anything but `--continue`.
SELECTION_OVERRIDE=""
CONTROLS_MODE=0
FORWARD=()
while [[ "$#" -gt 0 ]]; do
  case "$1" in
    --selection) SELECTION_OVERRIDE="${2:?--selection needs a path}"; shift 2 ;;
    --controls)  CONTROLS_MODE=1; shift ;;
    *)           FORWARD+=("$1"); shift ;;
  esac
done

# shellcheck source=scripts/test_lib.sh
source "${SCRIPT_DIR}/test_lib.sh"
parse_common_args "${FORWARD[@]+"${FORWARD[@]}"}"
cd "${REPO_ROOT}"

# --------------------------------------------------------------------------- #
# The controls.  Each drives the real dispatch over a one-row synthetic
# selection and asserts the VERDICT and the MESSAGE, not just the exit status --
# `v0.35.113`'s lesson, where a control asserted a non-zero exit that an
# unrelated injection guard was producing.
# --------------------------------------------------------------------------- #
if [[ "${CONTROLS_MODE}" -eq 1 ]]; then
  tmp="$(mktemp -d)"
  trap 'rm -rf "${tmp}"' EXIT
  rc=0
  # `(name, row, expect_exit, expect_grep)`; `-` means "assert nothing further".
  run_control() {
    local name="$1" row="$2" want_exit="$3" want_grep="$4"
    printf '%s\n' "${row}" > "${tmp}/sel"
    set +e
    "${BASH_SOURCE[0]}" --selection "${tmp}/sel" > "${tmp}/out" 2>&1
    local got_exit=$?
    set -e
    if [[ "${got_exit}" -ne "${want_exit}" ]]; then
      echo "FAIL: --controls ${name}: exit ${got_exit}, expected ${want_exit}" >&2
      sed 's/^/    /' "${tmp}/out" >&2
      rc=1
      return
    fi
    if [[ "${want_grep}" != "-" ]] && ! grep -qF "${want_grep}" "${tmp}/out"; then
      echo "FAIL: --controls ${name}: output does not carry '${want_grep}'" >&2
      sed 's/^/    /' "${tmp}/out" >&2
      rc=1
      return
    fi
    echo "  ok   ${name}"
  }

  P='run_check "HYGIENE" rg -n '"'"'finalize_report'"'"' scripts/test_lib.sh'
  A='run_check "HYGIENE" rg -n '"'"'zzNoSuchTokenInThisTree'"'"' scripts/test_lib.sh'
  NP='run_negative_check "HYGIENE" rg -n '"'"'zzNoSuchTokenInThisTree'"'"' scripts/test_lib.sh'
  NF='run_negative_check "HYGIENE" rg -n '"'"'finalize_report'"'"' scripts/test_lib.sh'

  run_control "a satisfied positive passes" \
    "$(printf 't.sh\t1\tpath\tanchor\tsweep\t%s' "${P}")" 0 "Swept 1 anchor(s)"
  run_control "an UNSATISFIED positive fails -- the whole point" \
    "$(printf 't.sh\t2\tpath\tanchor\tsweep\t%s' "${A}")" 1 "Command failed"
  run_control "a satisfied negative passes" \
    "$(printf 't.sh\t3\tpath\tanchor\tsweep\t%s' "${NP}")" 0 "Swept 1 anchor(s)"
  # A violated negative's message is `run_negative_check`'s own -- "Forbidden
  # pattern present", not the positive's "Command failed".  Asserting the MESSAGE
  # rather than the exit status is what makes this control say the *polarity* was
  # honoured, and it corrected this expectation on its first run.
  run_control "a VIOLATED negative fails, so polarity is not lost" \
    "$(printf 't.sh\t4\tpath\tanchor\tsweep\t%s' "${NF}")" 1 \
    "Forbidden pattern present"
  run_control "a tool invocation is deferred and named, not run" \
    "$(printf 't.sh\t5\tpath\tplain\tdefer:tool\trun_check "H" python3 scripts/nope.py')" \
    0 "deferred (runs a tool, not a text scan): t.sh:5"
  run_control "a tier-local variable is deferred BY NAME" \
    "$(printf 't.sh\t6\tpath\tfiltered\tdefer:var:TRACE_OUTPUT\trun_check "H" rg -n x y')" \
    0 "deferred (reads TRACE_OUTPUT): t.sh:6"
  run_control "a command substitution is deferred BY REASON" \
    "$(printf 't.sh\t7\tpath\tanchor\tdefer:subst\trun_check "H" rg -n x y')" \
    0 "deferred (substitutes a command): t.sh:7"
  run_control "an unreadable search FAILS rather than being skipped" \
    "$(printf 't.sh\t8\tpath\tunparsed\tfail:unparsed\trun_check "H" rg -n')" \
    1 "is a search this gate cannot read"
  # `fail:unlexable` shares the message with `fail:unparsed` on purpose: both say
  # the gate could not read the invocation, and the SELECTOR's report names which.
  # A separate arm answering the same thing would be two answers to one question.
  run_control "an unlexable search FAILS on the same arm" \
    "$(printf 't.sh\t9\tpath\tanchor\tfail:unlexable\trun_check "H" rg -n "x')" \
    1 "is a search this gate cannot read"
  # The two ways a swept anchor can fail to be CHECKED while still being counted.
  # Both are the fail-open this gate exists to remove, and both are the empirical
  # backstop for the selector's model of shell quoting: if that model ever
  # misplaces a real expansion as literal, the miss lands on one of these.
  run_control "a swept anchor that reaches no verdict FAILS, not passes" \
    "$(printf 't.sh\t11\tpath\tanchor\tsweep\trun_check "H" rg -n "unterminated')" \
    1 "produced no verdict"
  # shellcheck disable=SC2016  # The literal `${...}` is the POINT: this row must
  # reach the dispatch unexpanded so the `eval` is the thing that expands it, which
  # is the fatal condition under `set -u` that the epilogue exists to report.
  run_control "a FATAL expansion is reported in this gate's own voice" \
    "$(printf 't.sh\t12\tpath\tanchor\tsweep\trun_check "H" rg -n x "${ZZ_UNDEFINED_TIER_LOCAL}"')" \
    1 "the shell exited while sweeping t.sh:12"
  # An anchor that exits the shell with status ZERO.  Row 12 above exits 1 (an
  # unbound variable under `set -u`), so the epilogue's recorded failure and the
  # shell's own status agreed by accident and this gate's VERDICT was never the
  # thing being asserted.  This row separates them: measured pre-fix, the sweep
  # printed the failure and returned 0.
  run_control "an anchor that exits ZERO still FAILS the sweep" \
    "$(printf 't.sh\t14\tpath\tanchor\tsweep\texit 0')" \
    1 "the shell exited while sweeping t.sh:14"
  run_control "a disposition this gate does not know FAILS" \
    "$(printf 't.sh\t10\tpath\tanchor\tsomething_new\trun_check "H" rg -n x y')" \
    1 "which this gate does not know"
  # EVERY ROW IS ACCOUNTED FOR.  A non-blank row the loop skips -- a malformed one
  # with no command -- used to be dropped by the `continue` guard in silence; the
  # reconciliation turns that into a named failure.  The same check is what catches
  # an `eval`ed anchor draining the selection, which fd 9 now prevents: measured on
  # the pre-fix reader, a stdin-reading anchor skipped the following row and this
  # line reported "accounted for 1 of 2".
  run_control "a row the loop SKIPS is not silently dropped" \
    "$(printf 't.sh\t13\tpath\tanchor\tsweep\t')" \
    1 "accounted for 0 of 1 selected row(s)"
  run_control "an empty selection is an honest zero" \
    "" 0 "Swept 0 anchor(s)"

  if [[ "${rc}" -eq 0 ]]; then
    echo "CONTROLS PASS: changed-file anchor sweep -- a satisfied and an unsatisfied"
    echo "  positive, a satisfied and a violated negative, a deferred tool"
    echo "  invocation, tier-local variable and command substitution all named by"
    echo "  reason, an unreadable and an unlexable search failing, a swept anchor"
    echo "  that reaches no verdict and one whose expansion is fatal both failing,"
    echo "  an anchor that exits ZERO still failing the sweep,"
    echo "  an unknown disposition failing, a skipped row failing the row"
    echo "  reconciliation, and the honest zero."
  fi
  exit "${rc}"
fi

SELECTION=""
DERIVATION="$(mktemp)"
CLEANUP=("${DERIVATION}")

# ONE failure channel.  `set -u` makes an unbound variable fatal to the *shell*,
# not to the `eval` -- a subshell would contain it but would also strip
# `record_failure`'s bookkeeping, so a genuinely failing anchor would lose its own
# message, which the controls assert.  So the sweep stays in this shell and an
# early exit is REPORTED here, naming the row, in the gate's own voice.  Without
# it the only trace of a mis-deferred anchor is bash's `VAR: unbound variable` and
# an exit status, which reads like a broken script rather than a finding.
SWEEPING_ROW=""
SWEEP_COMPLETE=0
# A RECORDED FAILURE MUST FAIL (PR #897's review, `v0.35.150`).  `record_failure`
# only counts; the verdict is `finalize_report`'s, and this path never reaches it
# -- the shell is already on its way out, carrying whatever status the anchor
# chose.  So an anchor ending in `exit 0` printed "FAIL: ... the shell exited
# while sweeping ..." and the script returned **0**: the row reconciliation and
# `finalize_report` never ran and CI accepted every anchor the sweep had not yet
# reached.  The existing fatal-expansion control could not see it, because `set
# -u` exits 1 and the epilogue's failure agreed with the shell's status by
# accident.  The status is therefore OVERRIDDEN here rather than inherited.
_sweep_exit() {
  local status=$?
  if [[ "${SWEEP_COMPLETE}" -eq 0 && -n "${SWEEPING_ROW}" ]]; then
    record_failure "HYGIENE" \
      "changed-file anchor sweep: the shell exited while sweeping ${SWEEPING_ROW}, so the rows after it were never swept; either the anchor expanded an unbound tier-local (fatal under \`set -u\`, and the selector should have deferred it) or it exited the shell itself"
    status=1
  fi
  rm -f "${CLEANUP[@]}"
  trap - EXIT
  exit "${status}"
}
trap _sweep_exit EXIT

if [[ -n "${SELECTION_OVERRIDE}" ]]; then
  SELECTION="${SELECTION_OVERRIDE}"
  printf '# derivation: --selection %s\n' "${SELECTION}" > "${DERIVATION}"
else
  SELECTION="$(mktemp)"
  CLEANUP+=("${SELECTION}")
  # The selection FAILS rather than returning nothing when it cannot derive a
  # change set: "the gate could not read it" and "the gate checked it" must never
  # produce the same PASS line.  Its stderr carries the derivation, which the
  # report names so a reader can tell a clean sweep from a vacuous one.
  if ! python3 "${SCRIPT_DIR}/select_changed_anchors.py" \
        > "${SELECTION}" 2> "${DERIVATION}"; then
    record_failure "HYGIENE" "changed-file anchor sweep: $(cat "${DERIVATION}")"
    finalize_report
  fi
fi

log_section "HYGIENE" "$(head -1 "${DERIVATION}")"

swept=0
deferred_tool=0
deferred_var=0
deferred_subst=0
unreadable=0
unknown=0

# `_kind` is the classifier's verdict, carried in the selection for a reader and
# not consulted here: the DISPOSITION decides, and it is computed from the kind in
# the selector, so one place decides what a sweepable anchor is.
#
# THE SELECTION IS READ ON FD 9, not on stdin.  An `eval`ed anchor that read stdin
# would drain the rest of the rows, and the loop would end early with a "Swept N"
# line that reads like a complete pass -- silently unrun anchors, which is the
# fail-open this gate exists to remove.  The dedicated descriptor makes that
# impossible, and the row reconciliation below catches every OTHER cause of an
# early exit from the loop.
while IFS=$'\t' read -r script lineno prov _kind disposition command <&9; do
  [[ -n "${command:-}" ]] || continue
  case "${disposition}" in
    sweep)
      swept=$((swept + 1))
      before="${FAILURE_COUNT}"
      SWEEPING_ROW="${script}:${lineno} [${prov}]"
      # `eval` of the tier suite's own line, through the tier suite's own helper.
      # That is what makes this gate's verdict identical to Tier 3's by
      # construction rather than by resemblance.  The `set -e` dance is
      # `run_gate_check`'s own, so fail-fast still means fail-fast.
      set +e
      eval "${command}"
      rc=$?
      if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
        set -e
      fi
      # A swept anchor must have reached a VERDICT: either it passed (`rc` 0) or
      # `run_check` recorded a failure.  Neither means it never ran -- `set -u`
      # aborts the `eval` on an unbound variable, and a bad expansion or a syntax
      # error in the eval'd text does the same -- and an anchor counted as swept
      # without being checked is exactly the fail-open this gate exists to remove.
      #
      # This is also the EMPIRICAL backstop for the selector's model of shell
      # quoting (`expanding_text`).  That model over-approximates deliberately, so
      # its only unsafe direction is misplacing a real expansion as literal; if it
      # ever does, the miss FAILS here instead of passing silently.  Measuring the
      # outcome beats trusting the model, which is this project's own rule.
      if [[ "${rc}" -ne 0 && "${FAILURE_COUNT}" -eq "${before}" ]]; then
        record_failure "HYGIENE" \
          "changed-file anchor sweep: ${script}:${lineno} produced no verdict (exit ${rc}), so it was counted as swept without being checked"
      fi
      ;;
    defer:tool)
      deferred_tool=$((deferred_tool + 1))
      log_section "HYGIENE" \
        "  deferred (runs a tool, not a text scan): ${script}:${lineno} [${prov}]"
      ;;
    defer:var:*)
      deferred_var=$((deferred_var + 1))
      log_section "HYGIENE" \
        "  deferred (reads ${disposition#defer:var:}): ${script}:${lineno} [${prov}]"
      ;;
    defer:subst)
      # A command substitution in an expanding position: its value comes from
      # running something, so this gate cannot reproduce what the suite ran.
      deferred_subst=$((deferred_subst + 1))
      log_section "HYGIENE" \
        "  deferred (substitutes a command): ${script}:${lineno} [${prov}]"
      ;;
    fail:unparsed | fail:unlexable)
      unreadable=$((unreadable + 1))
      record_failure "HYGIENE" \
        "changed-file anchor sweep: ${script}:${lineno} is a search this gate cannot read, so what it pins is unswept"
      ;;
    *)
      # An explicit default branch: a disposition nobody anticipated must fail
      # rather than be counted as swept.
      unknown=$((unknown + 1))
      record_failure "HYGIENE" \
        "changed-file anchor sweep: ${script}:${lineno} has disposition '${disposition}', which this gate does not know"
      ;;
  esac
done 9< "${SELECTION}"
SWEEP_COMPLETE=1

# EVERY ROW IS ACCOUNTED FOR.  The dispositions partition the selection, so their
# counts must sum to its rows; a shortfall means the loop ended early and the
# "Swept N" line below describes a subset while reading like a complete pass.  A
# count is the right question here because the claim is exactly *did this process
# every row* -- and it catches any cause, not only the stdin drain fd 9 prevents.
rows="$(grep -cve '^[[:space:]]*$' "${SELECTION}" || true)"
accounted=$((swept + deferred_tool + deferred_var + deferred_subst + unreadable + unknown))
if [[ "${accounted}" -ne "${rows}" ]]; then
  record_failure "HYGIENE" \
    "changed-file anchor sweep: accounted for ${accounted} of ${rows} selected row(s), so the sweep ended early and what the rest pin is unswept"
fi

log_section "HYGIENE" \
  "Swept ${swept} anchor(s) over this cut's changed files; deferred ${deferred_tool} tool invocation(s), ${deferred_var} reading a tier-local variable and ${deferred_subst} substituting a command; ${unreadable} unreadable, ${unknown} unknown; ${accounted} of ${rows} row(s) accounted for."

finalize_report
