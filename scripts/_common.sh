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
#
# Audit-pass v3 portability fix: GNU `date +%s%N` returns nanoseconds,
# but BSD `date` (macOS) does not understand `%N` and returns the literal
# string `…N` — a downstream `[[ … -gt 0 ]]` would then error in
# arithmetic context with `set -euo pipefail`.  We probe support once at
# source time and fall back to integer-second precision on BSD.
if date +%s%N 2>/dev/null | grep -Eq '^[0-9]+$'; then
  _SELE4N_DATE_HAS_NANO=1
else
  _SELE4N_DATE_HAS_NANO=0
fi

time_command() {
  local tag="$1"
  shift
  local start end elapsed_s rc
  if [[ "${_SELE4N_DATE_HAS_NANO}" -eq 1 ]]; then
    start="$(date +%s%N)"
  else
    start="$(date +%s)"
  fi
  if "$@"; then
    rc=0
  else
    rc=$?
  fi
  if [[ "${_SELE4N_DATE_HAS_NANO}" -eq 1 ]]; then
    end="$(date +%s%N)"
    elapsed_s=$(awk "BEGIN { printf \"%.2f\", (${end} - ${start}) / 1000000000 }")
  else
    end="$(date +%s)"
    elapsed_s="$((end - start))"
  fi
  if [[ "${rc}" -eq 0 ]]; then
    log_info "${tag}" "completed in ${elapsed_s}s: $*"
  else
    log_error "${tag}" "failed after ${elapsed_s}s (rc=${rc}): $*"
  fi
  return "${rc}"
}

# tmpfile_cleanup <varname> — register a temp-file path stored in the
# named bash variable so it is removed on script exit.  Composable across
# multiple calls without corrupting trap quoting.
#
# Audit-pass v3 fix: the prior implementation re-extracted the existing
# EXIT trap via `sed` and re-registered it inside an outer single-quoted
# trap, which corrupted the quoting whenever the existing trap itself
# contained single-quoted text (it always did, after the first call).
# The new implementation tracks paths in a global array and registers
# the EXIT trap **once on first use**, preserving any pre-existing trap
# the caller installed via `eval`-able composition.
_SELE4N_TMPFILES=()
_SELE4N_TRAP_INSTALLED=0
_sele4n_tmpfile_cleanup_handler() {
  local f
  for f in "${_SELE4N_TMPFILES[@]}"; do
    rm -f "${f}"
  done
  # If the caller had a pre-existing EXIT trap, _SELE4N_PRIOR_EXIT_TRAP
  # holds its body; eval it so chained cleanup still runs.
  if [[ -n "${_SELE4N_PRIOR_EXIT_TRAP:-}" ]]; then
    eval "${_SELE4N_PRIOR_EXIT_TRAP}"
  fi
}

tmpfile_cleanup() {
  local varname="$1"
  local path="${!varname:-}"
  if [[ -z "${path}" ]]; then
    return 0
  fi
  _SELE4N_TMPFILES+=("${path}")
  if [[ "${_SELE4N_TRAP_INSTALLED}" -eq 0 ]]; then
    # Capture any existing EXIT trap body (as a single eval-able string)
    # so we chain cleanly instead of silently replacing it.
    local prior
    prior="$(trap -p EXIT)"
    if [[ -n "${prior}" ]]; then
      # Strip the `trap -- '` prefix and `' EXIT` suffix; `trap -p` always
      # uses single-quote escaping so this is the canonical inverse.
      _SELE4N_PRIOR_EXIT_TRAP="$(printf '%s' "${prior}" | sed -E "s/^trap -- '(.*)' EXIT$/\1/" | sed "s/'\\\\''/'/g")"
    fi
    trap _sele4n_tmpfile_cleanup_handler EXIT
    _SELE4N_TRAP_INSTALLED=1
  fi
}
