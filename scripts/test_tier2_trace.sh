#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

ensure_lake_available

TRACE_FIXTURE="${TRACE_FIXTURE_PATH:-tests/fixtures/main_trace_smoke.expected}"
TRACE_OUTPUT="$(mktemp)"
MISSING_REPORT="$(mktemp)"
trap 'rm -f "${TRACE_OUTPUT}" "${MISSING_REPORT}"' EXIT
TRACE_ARTIFACT_DIR="${TRACE_ARTIFACT_DIR:-}"

write_trace_artifacts() {
  if [[ -z "${TRACE_ARTIFACT_DIR}" ]]; then
    return 0
  fi

  mkdir -p "${TRACE_ARTIFACT_DIR}"
  cp "${TRACE_OUTPUT}" "${TRACE_ARTIFACT_DIR}/main_trace_smoke.actual.log"
  cp "${MISSING_REPORT}" "${TRACE_ARTIFACT_DIR}/main_trace_smoke.missing.txt"
  log_section "TRACE" "Wrote trace diagnostics to ${TRACE_ARTIFACT_DIR}."
}

if [[ ! -f "${TRACE_FIXTURE}" ]]; then
  record_failure "TRACE" "Fixture not found: ${TRACE_FIXTURE}"
  write_trace_artifacts
  finalize_report
fi

run_check "TRACE" bash -lc "lake exe sele4n > '${TRACE_OUTPUT}'"

expected_count=0
matched_count=0

while IFS= read -r expected_line || [[ -n "${expected_line}" ]]; do
  [[ -z "${expected_line}" ]] && continue
  expected_count=$((expected_count + 1))

  if grep -Fq "${expected_line}" "${TRACE_OUTPUT}"; then
    matched_count=$((matched_count + 1))
    continue
  fi

  printf '%s\n' "${expected_line}" >> "${MISSING_REPORT}"
  record_failure "TRACE" "Missing expected trace line: ${expected_line}"
  if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
    break
  fi
done < "${TRACE_FIXTURE}"

if [[ "${expected_count}" -eq 0 ]]; then
  record_failure "TRACE" "Fixture is empty: ${TRACE_FIXTURE}. Add at least one stable semantic expectation."
  write_trace_artifacts
  finalize_report
fi

if [[ "${matched_count}" -eq "${expected_count}" ]]; then
  log_section "TRACE" "Fixture comparison passed (${matched_count}/${expected_count} matched)."
else
  log_section "TRACE" "Matched ${matched_count}/${expected_count} expected lines from ${TRACE_FIXTURE}."
  log_section "TRACE" "Missing expectation lines:"
  while IFS= read -r missing_line || [[ -n "${missing_line}" ]]; do
    log_section "TRACE" "  - ${missing_line}"
  done < "${MISSING_REPORT}"
  log_section "TRACE" "If behavior changed intentionally, update ${TRACE_FIXTURE} in this PR and explain why."
fi

write_trace_artifacts

finalize_report
