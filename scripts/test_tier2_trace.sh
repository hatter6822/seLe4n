#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

TRACE_FIXTURE="tests/fixtures/main_trace_smoke.expected"
TRACE_OUTPUT="$(mktemp)"
trap 'rm -f "${TRACE_OUTPUT}"' EXIT

run_check "TRACE" bash -lc "lake exe sele4n > '${TRACE_OUTPUT}'"

if [[ -f "${TRACE_FIXTURE}" ]]; then
  missing=0
  while IFS= read -r expected_line || [[ -n "${expected_line}" ]]; do
    [[ -z "${expected_line}" ]] && continue
    if ! grep -Fq "${expected_line}" "${TRACE_OUTPUT}"; then
      record_failure "TRACE" "Missing expected trace line: ${expected_line}"
      missing=1
      if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
        finalize_report
      fi
    fi
  done < "${TRACE_FIXTURE}"

  if [[ "${missing}" -eq 0 ]]; then
    log_section "TRACE" "Fixture comparison passed (${TRACE_FIXTURE})."
  fi
else
  log_section "TRACE" "Fixture ${TRACE_FIXTURE} not found; trace output was generated but no comparison was performed."
fi

finalize_report
