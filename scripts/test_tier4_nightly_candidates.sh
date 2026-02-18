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

run_check "META" python3 "${SCRIPT_DIR}/scenario_catalog.py" validate
run_check "META" bash -lc "python3 '${SCRIPT_DIR}/scenario_catalog.py' nightly-seeds > '${ARTIFACT_DIR}/scenario_seeds.txt'"

run_check "TRACE" bash -lc 'lake exe sele4n > tests/artifacts/nightly/sele4n_run1.trace'
run_check "TRACE" bash -lc 'lake exe sele4n > tests/artifacts/nightly/sele4n_run2.trace'
run_check "TRACE" bash -lc 'diff -u tests/artifacts/nightly/sele4n_run1.trace tests/artifacts/nightly/sele4n_run2.trace > tests/artifacts/nightly/sele4n_determinism.diff'
run_check "TRACE" rg -n 'service restart status: some' tests/artifacts/nightly/sele4n_run1.trace
run_check "TRACE" rg -n 'service start denied branch: SeLe4n.Model.KernelError.policyDenied' tests/artifacts/nightly/sele4n_run1.trace
run_check "TRACE" rg -n 'service isolation api↔denied: true' tests/artifacts/nightly/sele4n_run1.trace
# shellcheck disable=SC2016
run_check "TRACE" bash -lc 'while read -r seed; do [[ -z "${seed}" ]] && continue; lake exe trace_sequence_probe "${seed}" 320 | tee "tests/artifacts/nightly/trace_sequence_probe_seed_${seed}.log"; done < tests/artifacts/nightly/scenario_seeds.txt'
# shellcheck disable=SC2016
run_check "TRACE" bash -lc 'printf "seed,steps\n" > tests/artifacts/nightly/trace_sequence_probe_manifest.csv; while read -r seed; do [[ -z "${seed}" ]] && continue; printf "%s,320\n" "${seed}" >> tests/artifacts/nightly/trace_sequence_probe_manifest.csv; done < tests/artifacts/nightly/scenario_seeds.txt'
run_check "META" "${SCRIPT_DIR}/test_full.sh"

finalize_report
