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
# D4: Priority Inheritance Protocol test suite.
run_check "TRACE" lake exe priority_inheritance_suite
# D5: Bounded latency / liveness surface anchor tests.
run_check "TRACE" lake exe liveness_suite
# T-03/AC6-A: Dedicated RegisterDecode + SyscallArgDecode test suite.
run_check "TRACE" lake exe decoding_suite
# AG9-E: Badge overflow hardware validation test suite.
run_check "TRACE" lake exe badge_overflow_suite
# AK3-A.8 (A-C01 CRITICAL): AsidPool rollover regression suite.
run_check "TRACE" lake exe asid_pool_suite
# AK3-C.5 + AK3-L: InterruptDispatch regression suite.
run_check "TRACE" lake exe interrupt_dispatch_suite
# AK3-B: W^X four-layer defense regression suite.
run_check "TRACE" lake exe wx_defense_suite
# AK3-E + AK3-J: decode validation regression suite.
run_check "TRACE" lake exe decode_validation_suite
# AK4-G (R-ABI-C01): End-to-end ABI round-trip suite —
# simulates Rust encoder, verifies Lean decode succeeds for all 5-arg syscalls.
run_check "TRACE" lake exe abi_roundtrip_suite
# AK7 (foundational model): 33 regression tests covering AK7-A..AK7-K.
run_check "TRACE" lake exe model_integrity_suite
# AK9 (platform / boot / DTB / MMIO): 21 regression tests covering AK9-A..AK9-H.
run_check "TRACE" lake exe ak9_platform_suite
# AN9 (hardware-binding closure): 23 regression tests covering AN9-A..AN9-J
# (includes audit-fix substantive proofs for D1, A1, B1).
run_check "TRACE" lake exe an9_hardware_binding_suite
# AN10 (AK7 cascade closure): 17 regression tests covering AN10-A/B/C/D —
# typed-helper kind discrimination, ValidObjId/ValidThreadId/ValidSchedContextId
# sentinel rejection, storeObjectKindChecked cross-kind rejection, and
# typed-helper / raw-match equivalence.
run_check "TRACE" lake exe an10_cascade_suite

finalize_report
