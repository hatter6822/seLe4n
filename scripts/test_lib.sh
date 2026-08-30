#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
set -euo pipefail

TEST_LIB_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${TEST_LIB_DIR}/.." && pwd)"
export REPO_ROOT

CONTINUE_MODE=0
FAILURE_COUNT=0
FAILURE_MESSAGES=()

# An acceptance gate that did not run is not an acceptance gate that passed.
#
# Sub-tests that cannot execute (a missing emulator, a kernel image the
# tree does not build yet) used to `exit 0`, which `run_check` scored as
# PASS — so a tier whose every gate declined to run still printed "All
# checks passed".  A gate reporting success for work it never did is
# worse than no gate, because the phase it certifies reads as validated.
#
# The contract: such a sub-test exits `SELE4N_SKIP_EXIT` and is invoked
# through `run_gate_check`, which records it as NOT RUN.  Skips are
# counted and named separately from failures, and `finalize_report`
# never claims a clean run while any gate was skipped.
#
# `SELE4N_REQUIRE_GATES=1` promotes a skipped gate to a hard failure —
# the mode a release cut (SM10.1) runs in, where "the emulator was
# absent" must stop the release rather than decorate it.
SELE4N_SKIP_EXIT=77
SKIP_COUNT=0
SKIP_MESSAGES=()

# AN11-B (H-21): per-suite timeout for `lake exe …` invocations. Default 30
# minutes is generous on CI hardware (the slowest production suite —
# `operation_chain_suite` — completes in well under 5 minutes); nightly
# workflows may override via the env var (e.g. `LEAN_TEST_TIMEOUT_MINS=120`).
# Override at invocation:  LEAN_TEST_TIMEOUT_MINS=10 ./scripts/test_smoke.sh
LEAN_TEST_TIMEOUT_MINS="${LEAN_TEST_TIMEOUT_MINS:-30}"
export LEAN_TEST_TIMEOUT_MINS

if [[ -t 1 ]] && [[ "${NO_COLOR:-}" = "" ]]; then
  COLOR_RESET='\033[0m'
  COLOR_META='\033[1;36m'
  COLOR_BUILD='\033[1;35m'
  COLOR_TRACE='\033[1;34m'
  COLOR_HYGIENE='\033[1;33m'
  COLOR_INVARIANT='\033[1;35m'
  COLOR_PASS='\033[1;32m'
  COLOR_FAIL='\033[1;31m'
  COLOR_RUN='\033[1;34m'
else
  COLOR_RESET=''
  COLOR_META=''
  COLOR_BUILD=''
  COLOR_TRACE=''
  COLOR_HYGIENE=''
  COLOR_INVARIANT=''
  COLOR_PASS=''
  COLOR_FAIL=''
  COLOR_RUN=''
fi

category_color() {
  local category="$1"
  case "${category}" in
    META)
      printf '%s' "${COLOR_META}"
      ;;
    BUILD)
      printf '%s' "${COLOR_BUILD}"
      ;;
    TRACE)
      printf '%s' "${COLOR_TRACE}"
      ;;
    HYGIENE)
      printf '%s' "${COLOR_HYGIENE}"
      ;;
    INVARIANT)
      printf '%s' "${COLOR_INVARIANT}"
      ;;
    *)
      printf '%s' "${COLOR_META}"
      ;;
  esac
}

status_color() {
  local message="$1"
  case "${message}" in
    PASS*)
      printf '%s' "${COLOR_PASS}"
      ;;
    FAIL*)
      printf '%s' "${COLOR_FAIL}"
      ;;
    RUN*)
      printf '%s' "${COLOR_RUN}"
      ;;
    *)
      printf '%s' ""
      ;;
  esac
}

log_section() {
  local category="$1"
  local message="$2"
  local cat_color
  local msg_color
  cat_color="$(category_color "${category}")"
  msg_color="$(status_color "${message}")"
  printf '%b[%s]%b %b%s%b\n' \
    "${cat_color}" "${category}" "${COLOR_RESET}" \
    "${msg_color}" "${message}" "${COLOR_RESET}"
}

parse_common_args() {
  CONTINUE_MODE=0
  for arg in "$@"; do
    case "${arg}" in
      --continue)
        CONTINUE_MODE=1
        ;;
      *)
        echo "error: unknown argument '${arg}'" >&2
        exit 2
        ;;
    esac
  done
  # H-12 fix: in continue mode, disable errexit so that run_check can
  # return non-zero without aborting the script.  Failure tracking is
  # managed by record_failure/finalize_report, not by set -e.
  if [[ "${CONTINUE_MODE}" -eq 1 ]]; then
    set +e
  fi
}

record_failure() {
  local category="$1"
  local message="$2"
  FAILURE_COUNT=$((FAILURE_COUNT + 1))
  FAILURE_MESSAGES+=("${category}: ${message}")
  log_section "${category}" "FAIL: ${message}"
}

# Record a gate that declined to run.  Under `SELE4N_REQUIRE_GATES=1` this
# is a failure outright; otherwise it is tracked so `finalize_report` can
# say what was not covered instead of silently counting it as covered.
record_skip() {
  local category="$1"
  local message="$2"
  if [[ "${SELE4N_REQUIRE_GATES:-0}" -eq 1 ]]; then
    record_failure "${category}" "acceptance gate did not run: ${message}"
    return 0
  fi
  SKIP_COUNT=$((SKIP_COUNT + 1))
  SKIP_MESSAGES+=("${category}: ${message}")
  log_section "${category}" "SKIP (NOT RUN): ${message}"
}

# ---------------------------------------------------------------------------
# The code view: a gate reads code, never the prose that describes it.
#
# WS-SM SM8.B (PR #861 review round 43).  Surface anchors matched raw file
# text, so a docstring could decide a gate in both directions — satisfying a
# positive anchor for a theorem that had been deleted, and firing a negative
# anchor by explaining the thing it forbids.  The AK7 counters had the same
# exposure, and one docstring in the tree had already been broken across two
# lines to stop a line-oriented counter seeing the pattern it was discussing.
#
# `scripts/lean_code_view.py --overlay` builds a whole-repo overlay whose
# `.lean` files are comment-free and byte-aligned with the originals (every
# other path is a symlink).  A text scan run with that directory as its working
# directory therefore resolves every path exactly as written and sees code
# only, with `rg -n` line numbers still pointing at real lines.
#
# The default is the code view, deliberately.  Requiring an opt-in would mean a
# future anchor written the obvious way silently regains the defect, which is
# the failure mode this closes; prose checks opt *out*, via `run_prose_check`.
# Build the overlay at most once per run, and cache it in the SHELL's scope.
#
# This used to be a function whose result was read with `$(...)`.  Command
# substitution runs in a subshell, so the `LEAN_CODE_VIEW_DIR` assignment was
# discarded the moment it returned and the overlay was rebuilt for **every
# anchor** — about 0.2s each across ~2500 checks, roughly eight minutes of pure
# overhead on a Tier 3 run, which is most of what it cost.
#
# Setting the variable directly rather than printing it keeps the assignment in
# the caller's scope, so the second anchor onward reuses the first one's build.
# Freshness is unaffected: each invocation of a tier script starts with the
# variable unset and rebuilds once, and nothing mutates the tree mid-run.
#
# Deliberately NOT exported.  The cache is sound only for a process that does
# not change the tree, and `test_code_view_wiring.sh` does exactly that — it
# plants a fixture and then asserts an anchor finds it.  Inheriting a parent's
# overlay would hand that child a view built before its fixture existed, so the
# variable stays shell-local and every child rebuilds (a no-op re-sync once the
# overlay directory exists, so the cost is a fraction of a second per process).
_ensure_lean_code_view() {
  if [[ -n "${LEAN_CODE_VIEW_DIR:-}" ]]; then
    return 0
  fi
  local repo view
  repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
  view="${repo}/.lake/build/leancodeview"
  python3 "${repo}/scripts/lean_code_view.py" --overlay "${view}" >/dev/null || return 1
  LEAN_CODE_VIEW_DIR="${view}"
}

# The path form, kept for callers that want the directory as a value.  Building
# through `_ensure_lean_code_view` first means this is a cache read, not a
# rebuild, whenever the shell has already produced one.
lean_code_view_dir() {
  _ensure_lean_code_view || return 1
  printf '%s' "${LEAN_CODE_VIEW_DIR}"
}

# Does this command read Lean source as text?
#
# Total over the shapes this repository uses, which was checked rather than
# assumed: every `bash -lc` anchor either invokes a tool (`lake`, a script, an
# environment source) or is a pure `rg`/`grep` scan, and none mixes the two.
# `_run_with_view` fails closed if that ever stops holding.
_scans_lean_source() {
  case "$1" in
    rg|grep) return 0 ;;
    bash)
      local script="$*"
      case "${script}" in
        *lake*|*scripts/*|*"source "*) return 1 ;;
        *.lean*) return 0 ;;
      esac
      return 1
      ;;
  esac
  return 1
}

# How long each check took, so a slow one is visible in the report instead of
# requiring an investigation to locate.  Two Tier 1 gates once accounted for
# roughly thirty-three of the tier's thirty-four minutes and nothing in the
# output said so; the tier printed the same PASS lines either way.
SLOW_CHECK_LINES=()
# Below this a duration is noise -- Tier 0 runs hundreds of sub-second checks.
SLOW_CHECK_THRESHOLD_MS="${SLOW_CHECK_THRESHOLD_MS:-1000}"

_now_ms() {
  # `%N` is a GNU extension; fall back to whole seconds where it is absent so a
  # non-GNU `date` degrades to coarse timing rather than breaking the harness.
  local raw
  raw="$(date +%s%3N 2>/dev/null || true)"
  case "${raw}" in
    ''|*[!0-9]*) printf '%s000\n' "$(date +%s)" ;;
    *) printf '%s\n' "${raw}" ;;
  esac
}

# Set `DURATION_NOTE` to " (12.3s)" when a check was slow enough to be worth
# naming, and record it for the end-of-run summary; empty otherwise.
#
# A global rather than a printed value on purpose: called as `$(_note_duration
# ...)` it would run in a command-substitution subshell, so the summary array
# would be appended to in a child and lost, leaving the per-check note printing
# correctly while the summary stayed permanently empty.
DURATION_NOTE=""
_note_duration() {
  local start="$1" label="$2" now elapsed
  now="$(_now_ms)"
  elapsed=$(( now - start ))
  DURATION_NOTE=""
  if [[ "${elapsed}" -lt "${SLOW_CHECK_THRESHOLD_MS}" ]]; then
    return 0
  fi
  local pretty
  pretty="$(printf '%d.%01ds' "$(( elapsed / 1000 ))" "$(( (elapsed % 1000) / 100 ))")"
  SLOW_CHECK_LINES+=("${elapsed}|${pretty}|${label}")
  DURATION_NOTE=" (${pretty})"
}

# The slowest checks, worst first.  Reported on success as well as failure: the
# point is to make cost visible on an ordinary green run.
_report_slow_checks() {
  if [[ "${#SLOW_CHECK_LINES[@]}" -eq 0 ]]; then
    return 0
  fi
  # No early-closing pipeline.  `… | sort | head -10` looks harmless and is not:
  # `sort` buffers its whole output, so once the sorted text exceeds the 64 KiB
  # pipe buffer `head` closes the pipe mid-write and `sort` dies of SIGPIPE with
  # status 141.  Every tier sources this file under `set -euo pipefail`, where
  # `pipefail` reports that 141 as the command substitution's status and `errexit`
  # then aborts `finalize_report` *before* it prints the pass/fail summary — so a
  # run with enough slow checks (an overloaded runner, or a lowered
  # `SLOW_CHECK_THRESHOLD_MS`) would exit 141 with no verdict at all.
  #
  # `mapfile` from a process substitution drains `sort` completely, and the
  # truncation happens in bash where nothing can be closed early.
  local -a _sorted=()
  mapfile -t _sorted < <(printf '%s\n' "${SLOW_CHECK_LINES[@]}" | sort -t'|' -k1,1nr)
  local _shown="${#_sorted[@]}"
  if [[ "${_shown}" -gt 10 ]]; then _shown=10; fi
  log_section "META" "Slowest checks (>= ${SLOW_CHECK_THRESHOLD_MS}ms):"
  local _i pretty label
  for (( _i = 0; _i < _shown; _i++ )); do
    IFS='|' read -r _ pretty label <<< "${_sorted[_i]}"
    [[ -n "${pretty}" ]] || continue
    log_section "META" "  ${pretty}  ${label}"
  done
  if [[ "${#_sorted[@]}" -gt "${_shown}" ]]; then
    log_section "META" "  … and $(( ${#_sorted[@]} - _shown )) more over the threshold."
  fi
}

# Run a command, in the code view when it scans Lean source.
_run_with_view() {
  if _scans_lean_source "$@"; then
    # `_ensure_lean_code_view`, not `$(lean_code_view_dir)`: the latter would put
    # the cache assignment in a subshell and rebuild the overlay every call.
    if ! _ensure_lean_code_view; then
      echo "error: could not build the Lean code view" >&2
      return 125
    fi
    ( cd "${LEAN_CODE_VIEW_DIR}" && "$@" )
    return $?
  fi
  # Fail closed on the shape the classifier cannot place: a tool invocation
  # that also greps Lean source would run against raw text and quietly reopen
  # the hole.  Split it into a tool check and a scan check instead.
  if [[ "$1" == "bash" ]]; then
    local script="$*"
    if [[ "${script}" == *.lean* && ( "${script}" == *"rg "* || "${script}" == *"grep "* ) ]]; then
      echo "error: this check both invokes a tool and scans Lean source, so it" >&2
      echo "       cannot run in the code view; split it into two checks." >&2
      return 125
    fi
  fi
  "$@"
}

run_check() {
  local category="$1"
  shift

  log_section "${category}" "RUN: $*"
  local _t0
  _t0="$(_now_ms)"
  if _run_with_view "$@"; then
    _note_duration "${_t0}" "$*"
    log_section "${category}" "PASS${DURATION_NOTE}"
    return 0
  fi

  record_failure "${category}" "Command failed: $*"
  if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
    finalize_report
  fi
  return 1
}

# `run_check` for an acceptance gate whose sub-test may legitimately be
# unable to run.  Identical to `run_check` except that the reserved exit
# code `SELE4N_SKIP_EXIT` is reported as NOT RUN rather than PASS.
#
# Use this — not `run_check` — for any check that certifies a phase's
# acceptance criteria against real hardware or an emulator.
run_gate_check() {
  local category="$1"
  shift

  log_section "${category}" "RUN: $*"
  local _t0 _rc
  _t0="$(_now_ms)"
  set +e
  _run_with_view "$@"
  _rc=$?
  if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
    set -e
  fi

  if [[ "${_rc}" -eq 0 ]]; then
    _note_duration "${_t0}" "$*"
    log_section "${category}" "PASS${DURATION_NOTE}"
    return 0
  fi

  if [[ "${_rc}" -eq "${SELE4N_SKIP_EXIT}" ]]; then
    record_skip "${category}" "$*"
    # Under SELE4N_REQUIRE_GATES a skip became a failure; honour fail-fast.
    if [[ "${SELE4N_REQUIRE_GATES:-0}" -eq 1 && "${CONTINUE_MODE}" -eq 0 ]]; then
      finalize_report
    fi
    return 0
  fi

  record_failure "${category}" "Command failed: $*"
  if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
    finalize_report
  fi
  return 1
}

# The opt-out: a check whose subject really is the prose — a documentation
# citation, a comment that must name the theorem it argues from, a status line.
# Runs against the real tree.  Rare by construction; if a new one is not
# obviously about documentation, it is probably a code check written wrongly.
run_prose_check() {
  local category="$1"
  shift

  log_section "${category}" "RUN (prose): $*"
  if "$@"; then
    log_section "${category}" "PASS"
    return 0
  fi

  record_failure "${category}" "Prose check failed: $*"
  if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
    finalize_report
  fi
  return 1
}

# WS-SM SM8.B (v0.33.5): the dual of `run_check` — the command MUST fail.
#
# This used to carry a CONVENTION — "match a definition, not a mention" —
# because a negative anchor over a prose-bearing tree fires on the comment that
# *explains* the forbidden thing.  It misfired three times in PR #861 anyway,
# which is what a convention gets you: it holds until someone writes an
# ordinary sentence.  Round 43 replaced it with a mechanism.  Lean scans now
# run against the comment-free code view (see `_run_with_view` above), so a
# docstring saying "there is no `setDomainSchedule`" is invisible to an anchor
# banning `setDomainSchedule`, and the pattern may be written plainly.
#
# The convention survives only where it is still load-bearing: a check over
# `docs/`, or one routed through `run_prose_check`, reads real text and must
# still distinguish a use from an explanation by construction.
#
# Surface anchors so far could only pin that something *is* present.  Several
# SM8.B findings were the opposite shape: a tautology that must not come back, a
# wildcard match arm that must not be reintroduced.  Grepping for absence needs
# an inverted check, and writing `! rg …` inline does not route through
# `record_failure`, so a regression would print nothing and pass.
#
# Usage:
#   run_negative_check "INVARIANT" rg -n 'forbidden_symbol' SeLe4n/
# PR #861 review (P2): only ripgrep's documented *no-match* status counts as
# absence.  `rg` exits 0 on a match, 1 on a clean no-match, and 2 on an error —
# an unrecognized flag, an unreadable path, a malformed pattern.  Treating every
# nonzero status as "absent" made those errors silent PASSes, i.e. a gate that
# fails open exactly when it is misconfigured, which is when it is least likely
# to be noticed.  Status 2 (and anything else) is now an infrastructure failure.
# The prose dual of `run_negative_check`: a forbidden *wording*, not a forbidden
# construct.  Reads the real text.
#
# Needed because routing negative checks through the code view would otherwise
# make three of them vacuous overnight: an anchor forbidding "bits per domain
# switch" inside a Lean docstring can never fire against a view with no
# docstrings in it, so it would pass forever and report a retracted figure as
# absent.  A mechanism that silently disarms an existing check is not an
# improvement on the convention it replaced, so the split is explicit on both
# sides — `run_negative_check` for constructs, this for wording.
run_prose_negative_check() {
  local category="$1"
  shift

  log_section "${category}" "RUN (prose, must not match): $*"
  local status=0
  "$@" >/dev/null 2>&1 || status=$?

  case "${status}" in
    0)
      record_failure "${category}" "Forbidden wording present: $*"
      ;;
    1)
      log_section "${category}" "PASS"
      return 0
      ;;
    *)
      record_failure "${category}" \
        "Prose negative check errored (status ${status}), which is not absence: $*"
      ;;
  esac

  if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
    finalize_report
  fi
  return 1
}

run_negative_check() {
  local category="$1"
  shift

  log_section "${category}" "RUN (must not match): $*"
  local status=0
  local _t0
  _t0="$(_now_ms)"
  _run_with_view "$@" >/dev/null 2>&1 || status=$?

  case "${status}" in
    0)
      record_failure "${category}" "Forbidden pattern present: $*"
      ;;
    1)
      _note_duration "${_t0}" "$*"
      log_section "${category}" "PASS${DURATION_NOTE}"
      return 0
      ;;
    *)
      record_failure "${category}" \
        "Negative check could not run (exit ${status}, not a clean no-match): $*"
      ;;
  esac

  if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
    finalize_report
  fi
  return 1
}

# AN11-B (H-21): Run a command under `timeout`, mapping the canonical
# `coreutils` exit code 124 (timeout fired) to an explicit, actionable
# failure message that names the timeout budget. Other non-zero exits keep
# their original semantics.  Use this for any `lake exe <suite>` invocation
# where a runaway proof / scenario could hang CI past its job budget.
#
# Audit-pass v2 (post-AN11) corrections:
#   * Use the `if "$@"; then …; else …; fi` idiom instead of `set +e ; rc=$? ;
#     set -e` — the latter unconditionally re-enables errexit, which broke
#     `--continue` mode (parse_common_args disables errexit and the wrapper
#     was flipping it back on after every check).
#   * Fold the failure message into a single string — `record_failure` only
#     consumes `$1`/`$2`, so the multi-arg call form silently dropped the
#     `Override…` advice.
#
# Usage:
#   run_check_with_timeout "TRACE" lake exe operation_chain_suite
run_check_with_timeout() {
  local category="$1"
  shift

  local mins="${LEAN_TEST_TIMEOUT_MINS}"
  log_section "${category}" "RUN: $* (timeout: ${mins}m)"

  # `timeout` is a coreutils binary that ships with every Linux distro the
  # CI uses and with macOS via brew (gtimeout); pre-flight check keeps the
  # script portable when neither is present.
  local timeout_bin=""
  if command -v timeout >/dev/null 2>&1; then
    timeout_bin="timeout"
  elif command -v gtimeout >/dev/null 2>&1; then
    timeout_bin="gtimeout"
  fi

  if [[ -z "${timeout_bin}" ]]; then
    log_section "${category}" "WARN: timeout(1) not found; running unguarded"
    if "$@"; then
      log_section "${category}" "PASS"
      return 0
    fi
    record_failure "${category}" "Command failed: $*"
    if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
      finalize_report
    fi
    return 1
  fi

  # The `if … then … else … fi` form catches the failure without tripping
  # `set -e`, regardless of the caller's errexit state.  `$?` inside the
  # else-branch holds the exit code; we capture it before any further
  # commands clobber the value.
  local rc=0
  if "${timeout_bin}" "${mins}m" "$@"; then
    log_section "${category}" "PASS"
    return 0
  else
    rc=$?
  fi

  case "${rc}" in
    124)
      record_failure "${category}" \
        "Timed out after ${mins}m: $* — possible runaway proof or scenario. Override the budget with LEAN_TEST_TIMEOUT_MINS=<minutes> for a single run, or investigate the suite for an infinite loop / divergent term."
      if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
        finalize_report
      fi
      return 1
      ;;
    *)
      record_failure "${category}" "Command failed (exit ${rc}): $*"
      if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
        finalize_report
      fi
      return 1
      ;;
  esac
}

finalize_report() {
  _report_slow_checks
  _report_skipped_gates
  if [[ "${FAILURE_COUNT}" -gt 0 ]]; then
    log_section "META" "Completed with ${FAILURE_COUNT} failure(s)."
    local entry
    for entry in "${FAILURE_MESSAGES[@]}"; do
      log_section "META" "${entry}"
    done
    exit 1
  fi

  # Never claim a clean run over gates that did not execute: the summary
  # line is what a reader (and a release checklist) takes as the verdict.
  #
  # Exiting SELE4N_SKIP_EXIT rather than 0 is what carries that verdict across
  # the process boundary.  Tier scripts nest — `test_nightly.sh` runs
  # `test_tier4_nightly_candidates.sh`, which runs `test_tier4_smp_bootcheck.sh`
  # — and a 0 here would have each parent's `run_check` record PASS, so the
  # nightly still printed "All checks passed" over fourteen gates that never
  # ran.  Reporting NOT RUN inside one script while the enclosing verdict stays
  # clean is the same defect one level up.  Parents invoke child runners with
  # `run_gate_check`, which understands this status.
  if [[ "${SKIP_COUNT}" -gt 0 ]]; then
    log_section "META" \
      "Checks passed, but ${SKIP_COUNT} acceptance gate(s) DID NOT RUN — coverage is incomplete."
    log_section "META" \
      "  Re-run with SELE4N_REQUIRE_GATES=1 to treat a skipped gate as a failure."
    exit "${SELE4N_SKIP_EXIT}"
  fi

  log_section "META" "All checks passed."
}

# Name every gate that declined to run, so an unexecuted gate is visible
# in the log rather than inferred from its absence.
_report_skipped_gates() {
  if [[ "${SKIP_COUNT}" -eq 0 ]]; then
    return 0
  fi
  log_section "META" "Skipped (NOT RUN) — ${SKIP_COUNT} acceptance gate(s):"
  local entry
  for entry in "${SKIP_MESSAGES[@]}"; do
    log_section "META" "  ${entry}"
  done
}

resolve_elan_env_file() {
  local elan_home_default="${HOME}/.elan"
  local elan_home="${ELAN_HOME:-${elan_home_default}}"
  printf '%s/env\n' "${elan_home}"
}

ensure_lake_available() {
  if command -v lake >/dev/null 2>&1; then
    return 0
  fi

  local elan_env_file
  elan_env_file="$(resolve_elan_env_file)"
  if [[ -f "${elan_env_file}" ]]; then
    # shellcheck disable=SC1090,SC1091
    source "${elan_env_file}"
  fi

  if command -v lake >/dev/null 2>&1; then
    return 0
  fi

  local setup_script="${REPO_ROOT}/scripts/setup_lean_env.sh"
  if [[ -x "${setup_script}" ]]; then
    log_section "BUILD" "lake missing; attempting automatic Lean toolchain setup"
    if "${setup_script}"; then
      elan_env_file="$(resolve_elan_env_file)"
      if [[ -f "${elan_env_file}" ]]; then
        # shellcheck disable=SC1090,SC1091
        source "${elan_env_file}"
      fi
    else
      record_failure "BUILD" "automatic setup via ${setup_script} failed"
      finalize_report
    fi
  fi

  if command -v lake >/dev/null 2>&1; then
    return 0
  fi

  record_failure "BUILD" "lake not found on PATH after auto-setup attempt. Run ./scripts/setup_lean_env.sh manually."
  finalize_report
}
