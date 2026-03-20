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

# Run suites through the Lean interpreter to avoid pathological C compilation
# times for very large test modules (notably NegativeStateSuite).
run_check "TRACE" lake env lean --run tests/NegativeStateSuite.lean
run_check "TRACE" lake env lean --run tests/OperationChainSuite.lean
run_check "TRACE" lake env lean --run tests/InformationFlowSuite.lean
run_check "TRACE" lake env lean --run tests/RobinHoodSuite.lean

finalize_report
