#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

if [[ "${NIGHTLY_ENABLE_EXPERIMENTAL:-0}" != "1" ]]; then
  log_section "META" "Tier 4 candidates staged but not enabled (set NIGHTLY_ENABLE_EXPERIMENTAL=1 to run)."
  log_section "META" "Staged candidates: repeat-run trace determinism + full suite replay."
  finalize_report
fi

ensure_lake_available

ARTIFACT_DIR="tests/artifacts/nightly"
mkdir -p "${ARTIFACT_DIR}"

run_check "TRACE" bash -lc 'lake exe sele4n > tests/artifacts/nightly/sele4n_run1.trace'
run_check "TRACE" bash -lc 'lake exe sele4n > tests/artifacts/nightly/sele4n_run2.trace'
run_check "TRACE" bash -lc 'diff -u tests/artifacts/nightly/sele4n_run1.trace tests/artifacts/nightly/sele4n_run2.trace > tests/artifacts/nightly/sele4n_determinism.diff'
run_check "META" "${SCRIPT_DIR}/test_full.sh"

finalize_report
