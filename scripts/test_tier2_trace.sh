#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

TRACE_FIXTURE="${TRACE_FIXTURE_PATH:-tests/fixtures/main_trace_smoke.expected}"
TRACE_OUTPUT="$(mktemp)"
MISSING_REPORT="$(mktemp)"
trap 'rm -f "${TRACE_OUTPUT}" "${MISSING_REPORT}"' EXIT

if [[ ! -f "${TRACE_FIXTURE}" ]]; then
  record_failure "TRACE" "Fixture not found: ${TRACE_FIXTURE}"
  finalize_report
fi

run_check "TRACE" bash -lc "lake exe sele4n > '${TRACE_OUTPUT}'"

missing=0
while IFS= read -r expected_line || [[ -n "${expected_line}" ]]; do
  [[ -z "${expected_line}" ]] && continue
  if ! grep -Fq "${expected_line}" "${TRACE_OUTPUT}"; then
    printf '%s\n' "${expected_line}" >> "${MISSING_REPORT}"
    record_failure "TRACE" "Missing expected trace line: ${expected_line}"
    missing=1
    if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
      finalize_report
    fi
  fi
done < "${TRACE_FIXTURE}"

if [[ "${missing}" -eq 0 ]]; then
  log_section "TRACE" "Fixture comparison passed (${TRACE_FIXTURE})."
else
  log_section "TRACE" "Missing expectation lines:"
  while IFS= read -r missing_line || [[ -n "${missing_line}" ]]; do
    log_section "TRACE" "  - ${missing_line}"
  done < "${MISSING_REPORT}"
  log_section "TRACE" "If behavior changed intentionally, update ${TRACE_FIXTURE} in this PR."
fi

finalize_report
