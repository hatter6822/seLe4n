#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

ensure_lake_available

# Run suites through the Lean interpreter to avoid pathological C compilation
# times for very large test modules (notably NegativeStateSuite).
run_check "TRACE" lake env lean --run tests/NegativeStateSuite.lean
run_check "TRACE" lake env lean --run tests/InformationFlowSuite.lean

finalize_report
