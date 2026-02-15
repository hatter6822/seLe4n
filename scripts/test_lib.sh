#!/usr/bin/env bash
set -euo pipefail

TEST_LIB_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${TEST_LIB_DIR}/.." && pwd)"
export REPO_ROOT

CONTINUE_MODE=0
FAILURE_COUNT=0
FAILURE_MESSAGES=()

log_section() {
  local category="$1"
  local message="$2"
  printf '[%s] %s\n' "${category}" "${message}"
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
