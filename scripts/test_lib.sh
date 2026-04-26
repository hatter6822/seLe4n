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

run_check() {
  local category="$1"
  shift

  log_section "${category}" "RUN: $*"
  if "$@"; then
    log_section "${category}" "PASS"
    return 0
  fi

  record_failure "${category}" "Command failed: $*"
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
  if [[ "${FAILURE_COUNT}" -gt 0 ]]; then
    log_section "META" "Completed with ${FAILURE_COUNT} failure(s)."
    local entry
    for entry in "${FAILURE_MESSAGES[@]}"; do
      log_section "META" "${entry}"
    done
    exit 1
  fi

  log_section "META" "All checks passed."
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
