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
run_check_with_timeout "TRACE" lake env lean --run tests/NegativeStateSuite.lean
run_check_with_timeout "TRACE" lake exe operation_chain_suite
run_check_with_timeout "TRACE" lake env lean --run tests/InformationFlowSuite.lean
run_check_with_timeout "TRACE" lake env lean --run tests/RobinHoodSuite.lean
# R8-D (I-M04): Execute frozen/radix test suites that were compiled but never run.
# Q4: Radix tree O(1) operations (lookup, insert, erase, fold, toList).
run_check_with_timeout "TRACE" lake exe radix_tree_suite
# Q5: FrozenMap, FrozenSet, FrozenSystemState.
run_check_with_timeout "TRACE" lake exe frozen_state_suite
# Q6: Freeze correctness proofs (lookup equivalence, radix equivalence).
run_check_with_timeout "TRACE" lake exe freeze_proof_suite
# Q7: Frozen kernel operations.
run_check_with_timeout "TRACE" lake exe frozen_ops_suite
# Q9-A: Two-Phase Architecture integration tests (builder→freeze→execution).
run_check_with_timeout "TRACE" lake exe two_phase_arch_suite
# D1: Thread suspension/resumption tests.
run_check_with_timeout "TRACE" lake exe suspend_resume_suite
# D2: Priority management tests.
run_check_with_timeout "TRACE" lake exe priority_management_suite
# D3: IPC buffer configuration tests.
run_check_with_timeout "TRACE" lake exe ipc_buffer_suite
# D4: Priority Inheritance Protocol test suite.
run_check_with_timeout "TRACE" lake exe priority_inheritance_suite
# D5: Bounded latency / liveness surface anchor tests.
run_check_with_timeout "TRACE" lake exe liveness_suite
# T-03/AC6-A: Dedicated RegisterDecode + SyscallArgDecode test suite.
run_check_with_timeout "TRACE" lake exe decoding_suite
# AG9-E: Badge overflow hardware validation test suite.
run_check_with_timeout "TRACE" lake exe badge_overflow_suite
# AK3-A.8 (A-C01 CRITICAL): AsidPool rollover regression suite.
run_check_with_timeout "TRACE" lake exe asid_pool_suite
# AK3-C.5 + AK3-L: InterruptDispatch regression suite.
run_check_with_timeout "TRACE" lake exe interrupt_dispatch_suite
# AK3-B: W^X four-layer defense regression suite.
run_check_with_timeout "TRACE" lake exe wx_defense_suite
# AK3-E + AK3-J: decode validation regression suite.
run_check_with_timeout "TRACE" lake exe decode_validation_suite
# AK4-G (R-ABI-C01): End-to-end ABI round-trip suite —
# simulates Rust encoder, verifies Lean decode succeeds for all 5-arg syscalls.
run_check_with_timeout "TRACE" lake exe abi_roundtrip_suite
# AK7 (foundational model): 33 regression tests covering AK7-A..AK7-K.
run_check_with_timeout "TRACE" lake exe model_integrity_suite
# AK9 (platform / boot / DTB / MMIO): 21 regression tests covering AK9-A..AK9-H.
run_check_with_timeout "TRACE" lake exe ak9_platform_suite
# AN9 (hardware-binding closure): 23 regression tests covering AN9-A..AN9-J
# (includes audit-fix substantive proofs for D1, A1, B1).
run_check_with_timeout "TRACE" lake exe an9_hardware_binding_suite
# AN10 (AK7 cascade closure): 17 regression tests covering AN10-A/B/C/D —
# typed-helper kind discrimination, ValidObjId/ValidThreadId/ValidSchedContextId
# sentinel rejection, storeObjectKindChecked cross-kind rejection, and
# typed-helper / raw-match equivalence.
run_check_with_timeout "TRACE" lake exe an10_cascade_suite
# AN11-A (H-20): KernelError variant cross-syscall coverage matrix.
# 41 rows pinning the production error path → expected variant mapping.
# A regression that drops or remaps an error variant fails the matching row.
run_check_with_timeout "TRACE" lake exe kernel_error_matrix_suite
# AN11-E.1 (TST-M01): AK8 sub-item runtime coverage — 13 tests covering
# AK8-E/F/G/H/I (every AK8 sub-item with a runtime-observable surface).
run_check_with_timeout "TRACE" lake exe ak8_coverage_suite
# WS-RC R2.C (DEEP-TEST-03): hardware syscall dispatch FFI bridge regression
# suite — exercises `suspendThreadInner`, `syscallDispatchInner`,
# `KernelError → UInt32`, encoded-UInt64 contract, and the kernel-state
# IO.Ref bootstrap.  See `tests/SyscallDispatchSuite.lean`.
run_check_with_timeout "TRACE" lake exe syscall_dispatch_suite
# WS-SM SM0.S — Foundations test suite for the SM0 typed identifiers
# (CoreId, SharingDomain, SgiKind, LockKind, LockId, BklState) plus the
# AN12-B inventory hardening + ArchAssumption 6-way machinery.  Runtime
# assertions (~41) plus surface-anchor `#check`s of every public symbol.
run_check_with_timeout "TRACE" lake exe smp_foundations_suite
# WS-SM SM2.A.12 — Memory model test suite for the SM2.A abstract memory
# model (MemoryOrder, AtomicLocation, MemoryEvent, MemoryTrace,
# wellFormed, eventPos, synchronizesWith, sequencedBefore, happensBefore,
# and the four partial-order theorems).  Runtime assertions (~36) plus
# surface-anchor `#check`s of every public symbol.
run_check_with_timeout "TRACE" lake exe memory_model_suite
# WS-SM SM2.B — TicketLock test suite for the SM2.B abstract TicketLock
# spec (TicketLockState, applyOp, promotePending, releaseAndPromote, all
# 8 wf invariants, plus the substantive theorems mutex / FIFO /
# bounded-wait / RA-pairing / reachability / determinism / closure-form
# aliases).  Runtime assertions (~35) plus surface-anchor `#check`s of
# every public symbol.
run_check_with_timeout "TRACE" lake exe ticket_lock_suite
# WS-SM SM2.C — RwLock test suite for the SM2.C abstract RwLock spec
# (RwLockState, AccessMode, RwLockOp, applyOp,
# promoteWaitersOnWriterRelease, promoteWaitersIfReadersEmpty, all 5 wf
# invariants, plus the substantive theorems writer-readers-exclusion /
# reader-multiplicity / FIFO admission / bounded-wait / RA-pairing /
# reader-batching / no-writer-starvation / wf-preservation / determinism
# / closure-form aliases / bit-packed encoding / refinement bridge).
# Runtime assertions (~40) plus surface-anchor `#check`s of every public
# symbol.
run_check_with_timeout "TRACE" lake exe rw_lock_suite

# WS-SM SM2.C-defer D-1..D-4: deferred-completion test suite.
# Runtime assertions for the Execution / Reachable infrastructure,
# writerWaitDepth, append/drop theorems, head-promotion claims, and
# the concrete event model.  See
# docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md.
run_check_with_timeout "TRACE" lake exe rw_lock_deferred_suite

# WS-SM SM2.D.6 — Verified-lock-primitive surface anchor suite.
# Surface anchors + decidable examples + runtime structural
# assertions for the SM2.D LockBridge typed handles, FFI wrappers,
# RAII combinators, and the SM2.D.7 22-theorem aggregator.
run_check_with_timeout "TRACE" lake exe smp_surface_anchors

# WS-SM SM2.D.3 — LockBridge RAII combinator suite.  Decidable
# examples + runtime structural assertions for the RAII pattern
# (acquire-action-release sequencing) plus the smart-constructor
# round-trips and the peek decoder algebra.
run_check_with_timeout "TRACE" lake exe lock_bridge_suite

# WS-SM SM3.A — Per-object lock field regression suite.  Surface
# anchors + decidable examples + runtime structural assertions for the
# per-object `lock : RwLockState` fields on every kernel-object struct
# (TCB, Endpoint, CNode, Notification, UntypedObject, SchedContext,
# VSpaceRoot) plus the ObjStore-level table lock on SystemState.
# Covers the SM3.A.11 default-state theorems
# (`default_objects_locks_unheld`, `default_objStoreLock_unheld`)
# and the per-variant `objectLockOf` reduction lemmas.
run_check_with_timeout "TRACE" lake exe per_object_lock_suite

# WS-SM SM3.B — LockSet regression suite.  Exercises the SM3.B
# `LockSet` type, `KernelObject.lockKind` projection,
# `LockId.fromObject` / `LockId.lookup`, per-syscall `lockSet_<τ>`
# declarations, the `lockAcquireSequence` canonical sort and
# ordered/complete/canonical theorems, `permittedKinds` plus the
# per-transition `lockSet_consistent_<τ>` theorems, the audit-pass-5
# `pipChainStart_<τ>` PIP chain-walk start markers, the audit-pass-6
# `tcbSetPriority`/`tcbSetMCPriority`/`tcbSetIPCBuffer`/`serviceRegister`
# footprint extensions (SC + VSpaceRoot + endpoint locks), and the
# 90-theorem inventory aggregator (with the new `chainStart` category).
run_check_with_timeout "TRACE" lake exe lock_set_suite

# WS-SM SM3.C — withLockSet 2PL discipline regression suite.
# Exercises the SM3.C.1 `withLockSet` 2PL combinator + per-object
# `acquireLockOnObject` / `releaseLockOnObject` primitives,
# `KernelObject.updateLock` per-variant helper + 7 simp lemmas,
# `lockHeld` / `lockSetHeld` predicates (SMP-migration precondition
# for Corollary 2.1.11), the SM3.C.5/C.6 ordering theorems
# (`lockSet_acquired_in_order`, `lockSet_released_in_reverse`),
# the SM3.C.7/C.8 atomicity/invariant-preservation theorems
# (`lockSet_atomic_under_2pl`, `lockSet_invariant_preserved`),
# the SM3.C.11 dynamic PIP-chain-walk machinery
# (`withDynamicChainExtension`, `walkAndAcquire`, `dynamicChainHeld`,
# `walkAndAcquire_path_ascending_in_ObjId_if_terminated`), and the
# 51-theorem SM3.C inventory aggregator.
run_check_with_timeout "TRACE" lake exe with_lock_set_suite

# WS-SM SM3.D — deadlock-freedom regression suite.  Exercises the SM3.D
# abstract `KernelExecution` model, the 2PL + ordering hypotheses + the
# `ladder_of_2pl_and_order` invariant, the SM3.D.3 `lockOrder_strict`
# (LockId strict-order helpers), the SM3.D.1/D.4 `noDeadlock` +
# `deadlockFreedom_under_2pl_and_ordering` (Theorem 2.1.9), the SM3.D.5
# wait-graph acyclicity (`waitGraph_acyclic_under_2pl` + the
# `noDeadlock_of_waitGraph_acyclic` coherence corollary), the SM3.D.6
# `boundedWait_under_2pl` bound, the §7 grounding bridge
# (`execution_satisfies_hypotheses_of_all_prefix`), and the 37-theorem
# SM3.D inventory.  Includes a non-vacuity witness: a genuine 2-core
# deadlock fixture that necessarily violates the ordering hypothesis.
run_check_with_timeout "TRACE" lake exe deadlock_freedom_suite

# WS-SM SM3.E — serializability regression suite.  Exercises the SM3.E
# `KernelTransitionInstance` schedule model, the SM3.E.1 conflict relation +
# `conflictOrder`, the SM3.E.4 `strictly_2pl_preserved` discipline, the SM3.E.5
# commutativity lemmas (read-only + disjoint-subsystem structural, write/write
# observational `objStoreEquiv`), the SM3.E.3 conflict-graph acyclicity
# (`conflictGraph_acyclic`) + the commit-sort serialization order +
# `serializability_under_2pl` (Theorem 2.1.10) + the read-only non-vacuity
# witness, the SM3.E.6 `singleCore_proof_preservation` (Corollary 2.1.11), and
# the 111-theorem SM3.E inventory.
run_check_with_timeout "TRACE" lake exe serializability_suite

finalize_report
