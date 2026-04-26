#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AN11-E.3 (TST-M03) — shared shell helpers for one-shot tier scripts.
#
# `test_lib.sh` provides the rich `run_check` / `run_check_with_timeout`
# infrastructure for tier scripts that aggregate multiple checks under a
# single tier umbrella.  Lean / Rust one-shot wrappers (e.g.
# `test_abi_roundtrip.sh`) do not need that machinery — they just need
# log helpers that match the same `[TAG] message` format so multi-script
# CI runs are uniformly readable.
#
# **Do not source `test_lib.sh` from this file.**  `test_lib.sh` enables
# `set -euo pipefail` and parses common args; one-shot scripts that want
# those should source `test_lib.sh` directly.
#
# Sourcing convention:
#
#   source "$(dirname "$0")/_common.sh"
#
# (No `|| true` swallow — if `_common.sh` is missing, the script must
# fail loudly so the operator notices.)

# Guard against double-sourcing.  Use `return` (which exits a sourced
# script cleanly), and fall through to a no-op `:` if invoked rather
# than sourced (return is invalid outside a function/sourced context).
# shellcheck disable=SC2317  # The `:` fallback is reachable when this
# file is *executed* directly rather than sourced.
if [[ -n "${SELE4N_COMMON_SH_LOADED:-}" ]]; then
  return 0 2>/dev/null
  : # no-op fallback if not sourced
fi
SELE4N_COMMON_SH_LOADED=1
export SELE4N_COMMON_SH_LOADED

# Detect whether stdout is a terminal and color is desired.  Mirrors
# `test_lib.sh` so the two helper sets render identically when stacked.
if [[ -t 1 ]] && [[ "${NO_COLOR:-}" = "" ]]; then
  COMMON_COLOR_RESET='\033[0m'
  COMMON_COLOR_INFO='\033[1;36m'
  COMMON_COLOR_ERROR='\033[1;31m'
  COMMON_COLOR_WARN='\033[1;33m'
else
  COMMON_COLOR_RESET=''
  COMMON_COLOR_INFO=''
  COMMON_COLOR_ERROR=''
  COMMON_COLOR_WARN=''
fi

# log_info <tag> <message...> — tagged informational message to stdout.
log_info() {
  local tag="$1"
  shift
  printf '%b[%s]%b %s\n' "${COMMON_COLOR_INFO}" "${tag}" "${COMMON_COLOR_RESET}" "$*"
}

# log_warn <tag> <message...> — tagged warning to stderr.
log_warn() {
  local tag="$1"
  shift
  printf '%b[%s]%b %s\n' "${COMMON_COLOR_WARN}" "${tag}" "${COMMON_COLOR_RESET}" "$*" >&2
}

# log_error <tag> <message...> — tagged error to stderr.
log_error() {
  local tag="$1"
  shift
  printf '%b[%s]%b %s\n' "${COMMON_COLOR_ERROR}" "${tag}" "${COMMON_COLOR_RESET}" "$*" >&2
}

# time_command <tag> <command...> — run a command, print elapsed wall-clock
# time on success.  On failure, prints the elapsed time then propagates
# the original exit code.
time_command() {
  local tag="$1"
  shift
  local start_ns end_ns elapsed_s
  start_ns="$(date +%s%N 2>/dev/null || echo 0)"
  local rc
  set +e
  "$@"
  rc=$?
  set -e
  end_ns="$(date +%s%N 2>/dev/null || echo 0)"
  if [[ "${start_ns}" -gt 0 && "${end_ns}" -gt 0 ]]; then
    elapsed_s=$(awk "BEGIN { printf \"%.2f\", (${end_ns} - ${start_ns}) / 1000000000 }")
    if [[ "${rc}" -eq 0 ]]; then
      log_info "${tag}" "completed in ${elapsed_s}s: $*"
    else
      log_error "${tag}" "failed after ${elapsed_s}s (rc=${rc}): $*"
    fi
  fi
  return "${rc}"
}

# tmpfile_cleanup <varname> — register a temp-file path stored in the
# named bash variable so it is removed on script exit.  Idempotent across
# multiple calls; preserves any existing EXIT trap chain by combining.
tmpfile_cleanup() {
  local varname="$1"
  local path="${!varname:-}"
  if [[ -z "${path}" ]]; then
    return 0
  fi
  # Append our cleanup to any existing EXIT trap.  The traps are written
  # with `'${path}'` quoted so the path is captured by-value at registration
  # time (single-quote suppression of expansion is exactly the SC2064 cure
  # — but since the path is passed in via `$1` and consumed before the
  # trap fires, the value is fixed by the time we get here).  The
  # disables below acknowledge the auditor's concern explicitly.
  local existing
  existing="$(trap -p EXIT | sed -E "s/^trap -- '(.*)' EXIT$/\1/")"
  if [[ -n "${existing}" ]]; then
    # shellcheck disable=SC2064  # path expansion at registration is intentional
    trap "${existing}; rm -f '${path}'" EXIT
  else
    # shellcheck disable=SC2064  # path expansion at registration is intentional
    trap "rm -f '${path}'" EXIT
  fi
}
