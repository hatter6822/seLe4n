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
run_check "TRACE" lake exe operation_chain_suite
run_check "TRACE" lake env lean --run tests/InformationFlowSuite.lean
run_check "TRACE" lake env lean --run tests/RobinHoodSuite.lean
# R8-D (I-M04): Execute frozen/radix test suites that were compiled but never run.
# Q4: Radix tree O(1) operations (lookup, insert, erase, fold, toList).
run_check "TRACE" lake exe radix_tree_suite
# Q5: FrozenMap, FrozenSet, FrozenSystemState.
run_check "TRACE" lake exe frozen_state_suite
# Q6: Freeze correctness proofs (lookup equivalence, radix equivalence).
run_check "TRACE" lake exe freeze_proof_suite
# Q7: Frozen kernel operations.
run_check "TRACE" lake exe frozen_ops_suite
# Q9-A: Two-Phase Architecture integration tests (builder→freeze→execution).
run_check "TRACE" lake exe two_phase_arch_suite
# D1: Thread suspension/resumption tests.
run_check "TRACE" lake exe suspend_resume_suite
# D2: Priority management tests.
run_check "TRACE" lake exe priority_management_suite
# D3: IPC buffer configuration tests.
run_check "TRACE" lake exe ipc_buffer_suite
# D5: Bounded latency / liveness surface anchor tests.
run_check "TRACE" lake exe liveness_suite

finalize_report
