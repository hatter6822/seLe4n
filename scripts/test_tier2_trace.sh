#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

ensure_lake_available

# AA2-E (M-8): Validate TRACE_FIXTURE_PATH is a git-tracked file to prevent
# CI fixture override attacks via environment variable injection.
if [ -n "${TRACE_FIXTURE_PATH:-}" ]; then
  if ! git ls-files --error-unmatch "${TRACE_FIXTURE_PATH}" >/dev/null 2>&1; then
    echo "ERROR: TRACE_FIXTURE_PATH must be a git-tracked file (got: ${TRACE_FIXTURE_PATH})" >&2
    exit 1
  fi
fi
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

# V8-F + AN11-C (H-22): Fixture drift detection — verify ALL `tests/fixtures/`
# `.expected` files have hashes matching their `.sha256` companion.  The
# main trace fixture is checked unconditionally (as a runtime gate); the
# secondary fixtures (`robin_hood_smoke.expected`, `two_phase_arch_smoke.expected`)
# are checked alongside in the same `sha256sum -c` invocation so the
# remediation message is uniform across all three.  See
# `tests/fixtures/README.md` for regeneration workflow.
SHA256_COMPANIONS=()
SHA256_DIR="tests/fixtures"
if [[ -d "${SHA256_DIR}" ]]; then
  while IFS= read -r companion; do
    SHA256_COMPANIONS+=("$(basename "${companion}")")
  done < <(find "${SHA256_DIR}" -maxdepth 1 -type f -name "*.expected.sha256" | sort)
fi

if [[ "${#SHA256_COMPANIONS[@]}" -gt 0 ]]; then
  if ! (cd "${SHA256_DIR}" && sha256sum -c "${SHA256_COMPANIONS[@]}" > /dev/null 2>&1); then
    drift_msg="Fixture drift detected in tests/fixtures/. One or more"
    drift_msg+=" .expected files do not match their .sha256 companion."
    drift_msg+=" To update, regenerate the affected hash file via:"
    drift_msg+=" cd tests/fixtures && sha256sum <fixture>.expected"
    drift_msg+=" > <fixture>.expected.sha256"
    drift_msg+=" — see tests/fixtures/README.md for the full workflow."
    record_failure "TRACE" "${drift_msg}"
    if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
      write_trace_artifacts
      finalize_report
    fi
  else
    log_section "TRACE" "Fixture hashes verified (${#SHA256_COMPANIONS[@]} files)."
  fi
fi

run_check_with_timeout "TRACE" bash -lc "lake exe sele4n > '${TRACE_OUTPUT}'"

expected_count=0
matched_count=0

trim_field() {
  local value="$1"
  value="${value#"${value%%[![:space:]]*}"}"
  value="${value%"${value##*[![:space:]]}"}"
  printf '%s' "${value}"
}

while IFS= read -r expected_line || [[ -n "${expected_line}" ]]; do
  [[ -z "${expected_line}" ]] && continue
  [[ "${expected_line}" =~ ^[[:space:]]*# ]] && continue

  scenario_id=""
  risk_class=""
  expected_fragment="${expected_line}"

  if [[ "${expected_line}" == *"|"* ]]; then
    IFS='|' read -r raw_scenario raw_risk raw_fragment <<< "${expected_line}"
    if [[ -n "${raw_fragment:-}" ]]; then
      scenario_id="$(trim_field "${raw_scenario}")"
      risk_class="$(trim_field "${raw_risk}")"
      expected_fragment="$(trim_field "${raw_fragment}")"
    fi
  fi

  if [[ -z "${expected_fragment}" ]]; then
    record_failure "TRACE" "Fixture expectation line is empty after parsing: ${expected_line}"
    if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
      break
    fi
    continue
  fi

  expected_count=$((expected_count + 1))

  if grep -Fq "${expected_fragment}" "${TRACE_OUTPUT}"; then
    matched_count=$((matched_count + 1))
    continue
  fi

  if [[ -n "${scenario_id}" || -n "${risk_class}" ]]; then
    printf '%s\n' "${scenario_id} | ${risk_class} | ${expected_fragment}" >> "${MISSING_REPORT}"
    record_failure "TRACE" "Missing expected trace line [${scenario_id}] (${risk_class}): ${expected_fragment}"
  else
    printf '%s\n' "${expected_fragment}" >> "${MISSING_REPORT}"
    record_failure "TRACE" "Missing expected trace line: ${expected_fragment}"
  fi
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
  # S2-E: Show a fixture diff to make review easier
  log_section "TRACE" "--- Fixture diff (expected fragments vs actual trace) ---"
  # Extract expected fragments for line-by-line comparison
  EXPECTED_FRAGMENTS="$(mktemp)"
  while IFS= read -r fline || [[ -n "${fline}" ]]; do
    [[ -z "${fline}" ]] && continue
    [[ "${fline}" =~ ^[[:space:]]*# ]] && continue
    if [[ "${fline}" == *"|"* ]]; then
      raw_frag="$(printf '%s' "${fline}" | cut -d'|' -f3-)"
      raw_frag="${raw_frag#"${raw_frag%%[![:space:]]*}"}"
      raw_frag="${raw_frag%"${raw_frag##*[![:space:]]}"}"
      printf '%s\n' "${raw_frag}"
    else
      printf '%s\n' "${fline}"
    fi
  done < "${TRACE_FIXTURE}" > "${EXPECTED_FRAGMENTS}"
  # Show lines in expected but not in actual (removed/changed)
  while IFS= read -r eline || [[ -n "${eline}" ]]; do
    if ! grep -Fq "${eline}" "${TRACE_OUTPUT}" 2>/dev/null; then
      log_section "TRACE" "  MISSING: ${eline}"
    fi
  done < "${EXPECTED_FRAGMENTS}"
  # Show lines in actual that don't match any expected fragment (new/changed)
  NEW_LINES=0
  while IFS= read -r aline || [[ -n "${aline}" ]]; do
    found=0
    while IFS= read -r eline || [[ -n "${eline}" ]]; do
      if [[ "${aline}" == *"${eline}"* ]]; then
        found=1
        break
      fi
    done < "${EXPECTED_FRAGMENTS}"
    if [[ "${found}" -eq 0 && -n "${aline}" ]]; then
      if [[ "${NEW_LINES}" -lt 20 ]]; then
        log_section "TRACE" "  NEW:     ${aline}"
      fi
      NEW_LINES=$((NEW_LINES + 1))
    fi
  done < "${TRACE_OUTPUT}"
  if [[ "${NEW_LINES}" -gt 20 ]]; then
    log_section "TRACE" "  ... and $((NEW_LINES - 20)) more new lines (run diff manually for full output)"
  fi
  rm -f "${EXPECTED_FRAGMENTS}"
  log_section "TRACE" "If behavior changed intentionally, update ${TRACE_FIXTURE} in this PR and explain why."
fi

write_trace_artifacts

finalize_report
