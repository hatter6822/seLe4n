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

# WS-SM SM4.A — per-core Vector bootstrap regression suite.  Exercises the
# SM4.A.1/A.2 `SeLe4n.PerCoreVector` helper surface (the get_eq_getElem bridge plus
# the six lemmas get_set_eq / get_set_ne / length / replicate_get / ext /
# nodup_of_finRange) on concrete vectors, the SM4.A.3 Array-backed runtime
# check, the SM4.A.4 RPi5 coreCount=4 pinning, the SM4.A.5 single-core +
# 4-core simulation bindings, and the SM4.A.6/A.7/A.8 CoreId / bootCoreId /
# allCores recap.
run_check_with_timeout "TRACE" lake exe per_core_vector_suite

# WS-SM SM4.B foundation suite — runtime mirror of the seven per-core
# SchedulerState accessors (SM4.B.8), the default-state per-core
# initialisation theorem (SM4.B.9), and per-core extensionality (SM4.B.10).
run_check_with_timeout "TRACE" lake exe per_core_scheduler_state_suite

# WS-SM SM4.C — per-core scheduler invariant migration regression suite.
# Exercises the SM4.C per-core predicate forms, the 16 boot-core bridges
# (each `Iff.rfl`), the `schedulerInvariant_perCore` aggregate (SM4.C.29) +
# `schedulerInvariant_smp` + `aggregateForall`, the per-conjunct
# projections, the live-surface bundle bridges
# (`schedulerInvariantBundleFull/Extended_to_perCore_bootCore`), the
# default-state theorem on every core, the frame / idle-frame / three
# cross-core independence corollaries, the SM4.C.30 pairwise theorem, and
# the single-core-preservation-lifts-to-SMP skeleton.  Runtime asserts the
# decidable foundations + theorem applicability.
run_check_with_timeout "TRACE" lake exe scheduler_invariant_per_core_suite

# WS-SM SM4.C audit-pass-4 — per-operation per-core preservation suite.
# Surface anchors + elaboration-time witness for the 5 per-op per-core
# preservation theorems composing existing single-core preservation with
# the SM4.C SMP-preservation skeleton.
run_check_with_timeout "TRACE" lake exe scheduler_invariant_per_core_preservation_suite

# WS-SM SM4.D — cross-subsystem per-core invariant migration suite.
# Surface anchors + elaboration-time witnesses + runtime assertions for the
# per-core IPC↔scheduler coherence predicates, the capability no-stale-ref
# retype precondition, the architecture register-decode consistency, the
# IF-M1 per-core projections (incl. value-level decidable checks on the
# default state), and the cross-subsystem capstone aggregates.
run_check_with_timeout "TRACE" lake exe cross_subsystem_per_core_suite

# WS-SM SM5.A — per-core chooseThread suite.  Surface anchors +
# elaboration-time theorem-application witnesses + the six SM5.A.8 runtime
# selection scenarios (empty/idle-fallback, single in-domain, highest-
# priority, out-of-domain skip, per-core independence, selection soundness)
# evaluating the real `chooseThreadOnCore` computation, plus the SM5.A.2
# lock-set witnesses.
run_check_with_timeout "TRACE" lake exe smp_scheduler_selection_suite

# WS-SM SM5.B — per-core switchToThread suite.  25 runtime assertions over the
# real `switchToThreadOnCore` computation: the SM5.B.9 switch scenarios
# (sets-current, dequeue-on-dispatch, preempt-previous, reject-remote,
# admit-unbound / admit-matching-affinity, cross-core independence, non-TCB
# error path), the SM5.B.2 cross-domain lock-set witnesses, and the SM5.B.4
# affinity-admits algebra.
run_check_with_timeout "TRACE" lake exe smp_switch_to_thread_suite

# WS-SM SM5.C — Cross-core wake via SGI.  Exercises the real `wakeThread` /
# `enqueueRunnableOnCore` / `handleRescheduleSgiOnCore` / `setThreadCpuAffinity`
# computations: determine-target affinity routing, enqueue + make-ready, local
# vs remote wake (SGI emission), the full wake→SGI→handle round-trip, the
# affinity-control op, the SM5.C.3 lock-set witnesses, and the SM5.C.11
# SGI-delivery latency bound.
run_check_with_timeout "TRACE" lake exe smp_wake_suite

# WS-SM SM5.D — per-core timer tick.  Runtime assertions for the SM5.D.10 tick
# scenarios: the SM5.D.3 lock-set + SM5.D.7 WCRT bound, SM5.D.6 domain decrement +
# rotation, SM5.D.5 budget-tick preemption, SM5.D.2/.9 idle tick +
# lastTimeoutErrors clearing, SM5.D.4 CBS replenishment, and the SM5.D.1 per-core
# timer-entry seam.
run_check_with_timeout "TRACE" lake exe smp_timer_suite

# WS-SM SM5.E — per-core idle threads.  Runtime assertions for the SM5.E
# scenarios: SM5.E.1/.2/.5 idle field facts (priority 0, cpuAffinity = some c,
# distinct ids), SM5.E.6 chooseThreadOnCore_always_succeeds (empty core ⇒ idle
# fallback; after enqueueIdleThreadOnCore the selection picks idle), SM5.E.5
# priority-0 ⇒ a higher-priority user thread still outranks idle (no starvation),
# SM5.E.4 per-core idle locality (frame + affinity + cross-core), and the SM5.E
# theorem-inventory partition counts.
run_check_with_timeout "TRACE" lake exe smp_idle_suite

# WS-SM SM5.F — per-core priority inheritance.  Runtime assertions on a concrete
# cross-core blocking scenario (a server bound to a remote core with a
# high-priority waiter on the boot core): SM5.F.1 per-core ≤ global decomposition
# (computeMaxWaiterPriorityOnCore), SM5.F.2 cross-core PIP wake SGI emission
# (pipBoostWithWake — remote material vs local), SM5.F.7 per-core blocking-graph
# slice + consistency (blockingServerOnCore), SM5.F.6 cross-core resume wake
# (restoreToReadyWithWake), and the SM5.F theorem-inventory partition counts.
run_check_with_timeout "TRACE" lake exe smp_pip_suite

# WS-SM SM5.G — per-core domain scheduling.  Runtime assertions for the SM5.G.6
# domain-rotation scenarios on concrete domain-schedule fixtures: single-domain
# no-op, multi-domain rotation (domain + index + time), cyclic return-to-start
# (advanceDomainOnCore_cyclic), post-rotation in-domain membership (Thm 3.7.1),
# selection respecting the active-domain barrier (chooseThreadOnCore_respects_activeDomain),
# cross-core domain independence, plus the SM5.G.5 lock-set witnesses and the SM5.G
# theorem-inventory partition counts.
run_check_with_timeout "TRACE" lake exe smp_domain_suite

# WS-SM SM5.H — per-core CBS.  Runtime assertions for the SM5.H.8 cross-core CBS
# scenarios on concrete CBS fixtures: per-core replenishment scheduling
# (replenishOnCore), the cross-core SchedContext replenishment migration
# (migrateSchedContextReplenishment — entries genuinely move between cores), the
# affinity-change-with-migration composite (setThreadCpuAffinityWithMigration), the
# CBS budget bounds (consumeBudget / applyRefill keep budgetRemaining ≤ budget), the
# affinity-consistency witnesses, and the SM5.H theorem-inventory partition counts.
run_check_with_timeout "TRACE" lake exe smp_cbs_suite

# WS-SM SM5.I — Per-core invariant suite runtime checks.  Exercises the actual
# transition computation on concrete fixtures: the structural-invariant safety
# facts on the freshly-booted system, the advanceDomainOnCore frame + the
# enqueueRunnableOnCore wake maintaining runnable-are-TCBs with sibling-core
# framing, and the SM5.I theorem-inventory partition counts.
run_check_with_timeout "TRACE" lake exe smp_invariant_suite

# WS-SM SM5.J — WCRT-under-fine-locks runtime checks.  Exercises the actual
# WCRT_lockSet / WCRT_smp computations on concrete per-core op footprints: the
# per-op exact lock-WCRT values (chooseThread = 2·3·tCs, timerTick = 3·3·tCs,
# replenish = 1·3·tCs), the RPi5 maxLockSetSize·3·tCs bound + the typical-syscall
# < 1 ms tick-budget fit, the combined WCRT_smp decomposition + monotonicity, the
# per-core idle no-stall on an idle-enqueued fixture, and the SM5.J inventory counts.
run_check_with_timeout "TRACE" lake exe smp_wcrt_suite

# WS-SM SM5.K.1 — Aggregate SMP per-core scheduler runtime checks (the acceptance-
# gate 4-thread/4-core workload).  Exercises the full SM5 per-core scheduler surface
# on a single deterministic fixture: per-core selection (each core runs its own bound
# thread), cross-core independence, affinity admission, cross-core wake SGI routing,
# per-core switch (set current / reject remote), per-core WCRT bounds, the idle
# no-stall, and the deterministic 4-core scheduling trace verified byte-for-byte
# against tests/fixtures/smp_4core_scheduler.expected.
run_check_with_timeout "TRACE" lake exe smp_scheduler_suite

# WS-SM SM6.A — Cross-core endpoint call runtime checks.  Exercises the actual
# endpointCallOnCore / removeRunnableOnCore / lockSet_endpointCall computations:
# the SM6.A.2/.5/.8 lock-set footprint (kinds permitted, keys nodup, donation
# extension, WithCaps dest-CNode), the SM6.A.1/.4 per-core caller blocking
# (removeRunnableOnCore bridge + descheduling + sibling-core locality), the
# SM6.A.1 no-receiver path (blockedOnCall, no SGI), and the SM6.A.3 local vs
# remote rendezvous SGI emission (remote receiver wakes onto its home core).
run_check_with_timeout "TRACE" lake exe smp_cross_core_call_suite

finalize_report
