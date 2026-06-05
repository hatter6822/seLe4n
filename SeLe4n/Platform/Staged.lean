-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Sim.Contract
import SeLe4n.Platform.FFI
import SeLe4n.Platform.RPi5.Contract
import SeLe4n.Platform.RPi5.VSpaceBoot
import SeLe4n.Kernel.Architecture.CacheModel
import SeLe4n.Kernel.Architecture.ExceptionModel
import SeLe4n.Kernel.Architecture.TimerModel
-- AN9-C / AN9-A / AN9-B: hardware-binding closure modules
import SeLe4n.Kernel.Architecture.BarrierComposition
import SeLe4n.Kernel.Architecture.TlbCacheComposition
-- AN12-B (Theme 4.4): SMP-latent single-core assumption inventory
import SeLe4n.Kernel.Concurrency.Assumptions
-- WS-SM SM0.C (closes SMP-H3): build-time `@`-references for every
-- `smpLatentInventory` entry's `identifier` and `sourceTheorem` so a
-- renamed underlying symbol fails the build instead of silently
-- leaving a dangling inventory entry.  This is the post-AN12-B
-- "audit-by-source-read" pattern's structural replacement.
import SeLe4n.Kernel.Concurrency.Anchors
-- WS-SM SM0.E/SM0.F/SM0.H/SM0.I: foundational typed-identifier modules
-- pulled into Staged so the SM0 build closure is one unit.  No runtime
-- behavior change at SM0; SM1..SM9 wire these into kernel transitions.
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Concurrency.Locks
import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Sgi
-- WS-SM SM1.B.5: typed FFI wrapper for `ffi_current_core_id`.  Pulled
-- into Staged so CI builds the bridge (CoreId-typed wrapper around the
-- Rust per-CPU base) on every push.  Reachability: production import
-- closure runs through here even before per-core scheduler state lands
-- at SM5.
import SeLe4n.Kernel.Concurrency.Runtime
-- WS-SM SM1.C.6: secondary-core kernel-entry placeholder.  Pulled into
-- Staged so CI verifies the `@[export lean_secondary_kernel_main]`
-- attribute keeps emitting a C-callable wrapper that the Rust HAL's
-- `rust_secondary_main` (smp.rs Step 6) resolves at link time.  At
-- SM1.C the body is `pure ()`; SM5 replaces it with the per-core
-- scheduler entry.
import SeLe4n.Kernel.SecondaryEntry
-- WS-SM SM1.E.4: typed `tlbiForSharing` FFI wrapper.  Pulled into
-- Staged so CI builds the typed wrapper around the Rust
-- `ffi_tlbi_for_sharing` dispatcher on every push.  Reachability:
-- staged at SM1.E; SM7 (TLB shootdown) is the first runtime exerciser.
import SeLe4n.Kernel.Architecture.TlbiForSharing
-- WS-SM SM2.A: abstract memory model for verified lock primitives.
-- Pulled into Staged so CI builds the operational ARMv8.1-A LSE memory
-- model (MemoryOrder, MemoryEvent, MemoryTrace, synchronizesWith,
-- happensBefore + partial-order theorems) on every push.  Reachability:
-- staged at SM2.A; SM2.B (TicketLock) and SM2.C (RwLock) are the first
-- runtime exercisers.
import SeLe4n.Kernel.Concurrency.MemoryModel
-- WS-SM SM2.B: abstract TicketLock specification.  Pulled into Staged so
-- CI builds the operational TicketLock spec (TicketLockState, applyOp,
-- promotePending, releaseAndPromote, the 8-conjunct wf invariant, plus
-- the substantive theorems mutex / FIFO / bounded-wait / RA-pairing /
-- reachability / determinism / wf-preservation closure-form) on every
-- push.  Reachability: staged at SM2.B; SM3 per-object lock proofs are
-- the first runtime exercisers.
import SeLe4n.Kernel.Concurrency.Locks.TicketLock
-- WS-SM SM2.C: abstract RwLock specification.  Pulled into Staged so CI
-- builds the operational RwLock spec (RwLockState, AccessMode, RwLockOp,
-- applyOp, promoteWaitersOnWriterRelease, promoteWaitersIfReadersEmpty,
-- the 5-conjunct wf invariant, plus the substantive theorems writer-
-- readers-exclusion / reader-multiplicity / FIFO admission / bounded-
-- wait / RA-pairing / reader-batching / no-writer-starvation / wf-
-- preservation / determinism / closure-form / bit-packed encoding).
-- Reachability: staged at SM2.C; SM3 per-object lock proofs are the
-- first runtime exercisers.
import SeLe4n.Kernel.Concurrency.Locks.RwLock
-- WS-SM SM2.C.20: RwLock refinement bridge between the Lean abstract
-- state and the Rust bit-packed AtomicU64 representation.  Documents
-- the FIFO divergence and exports the simulation φ (`rwLockSim`).
import SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement
-- WS-SM SM2.D: TicketLock refinement bridge between the Lean abstract
-- state and the Rust two-u64 concrete representation.  Defines
-- `ticketLockSim` and exports the F-01 anchor theorem
-- `rust_ticketLock_refines_lean` for the SM2.D.7 lockPrimitives
-- aggregator.
import SeLe4n.Kernel.Concurrency.Locks.TicketLockRefinement
-- WS-SM SM2.D: typed lock FFI wrappers + RAII combinators.  Wraps the
-- raw `Platform.FFI.ffi*` lock declarations into typed Lean APIs
-- (`TicketLockHandle`, `RwLockHandle`, `withTicketLock`, `withReadLock`,
-- `withWriteLock`).  Reachability: staged at SM2.D; SM3+ per-object
-- locks are the first runtime exercisers.
import SeLe4n.Kernel.Concurrency.LockBridge
-- WS-SM SM2.D.7: lock-primitive theorem inventory.  Aggregates the
-- 22 substantive SM2 theorems (4 memory-model + 6 TicketLock + 10
-- RwLock + 2 refinement) with a `lockPrimitives.length = 22` size
-- witness.  Used by the cross-language symmetry script
-- `scripts/check_lock_ffi_symmetry.sh`.
import SeLe4n.Kernel.Concurrency.LockPrimitives
-- WS-SM SM3.B + SM3.C + SM3.D + SM3.E: LockSet + per-transition lockSet
-- declarations + the canonical sort and ordered/complete/canonical theorems +
-- LockId.fromObject / LockId.lookup projection layer +
-- per-transition lockSet_consistent theorems + 72-theorem SM3.B inventory
-- + SM3.C `withLockSet` 2PL combinator + per-object acquire/release
-- primitives + `lockSetHeld` predicate + 2PL discipline theorems
-- (`lockSet_acquired_in_order`, `lockSet_released_in_reverse`,
-- `lockSet_atomic_under_2pl`, `lockSet_invariant_preserved`) + SM3.C.11
-- dynamic PIP-chain-walk machinery + 51-theorem SM3.C inventory + SM3.D
-- deadlock-freedom (`deadlockFreedom_under_2pl_and_ordering`,
-- `waitGraph_acyclic_under_2pl`, `boundedWait_under_2pl`) + 66-theorem
-- SM3.D inventory + SM3.E serializability (`serializability_under_2pl`
-- Theorem 2.1.10, `conflictGraph_acyclic`, `strictly_2pl_preserved`,
-- the SM3.E.5 commutativity lemmas, `singleCore_proof_preservation`
-- Corollary 2.1.11) + 111-theorem SM3.E inventory.
-- Staged at SM3.C/D/E; SM5+ per-core scheduler integration is the first
-- runtime exerciser.  Reachability: every `@[export]` body in the
-- future SM3.C.9 migration wraps its kernel-transition action in
-- `withLockSet (lockSet_τ args)`, threading the SM3.B canonical sort
-- through `acquireAll` and the reverse through `releaseAll`.
import SeLe4n.Kernel.Concurrency.LockSet
-- WS-SM SM4.C: per-core scheduler invariant migration.  Lifts every
-- per-core scheduler invariant predicate to an explicit `(c : CoreId)`
-- parameter (plan §5.3/§5.6), exports the aggregate
-- `schedulerInvariant_perCore` (SM4.C.29) + `schedulerInvariant_smp`, the
-- boot-core bridges to the live `schedulerInvariantBundle*` surface, the
-- per-core / idle-core frame lemmas, the cross-core pairwise-independence
-- theorem (SM4.C.30), and the single-core-preservation-lifts-to-SMP
-- skeleton.  Reachability: staged at SM4.C; SM5's per-core scheduler
-- operations are the first runtime exerciser (which will move it
-- production-reached).
import SeLe4n.Kernel.Scheduler.Invariant.PerCore
-- WS-SM SM4.C audit-pass-4: per-operation per-core preservation theorems
-- for the 5 boot-core scheduler operations that have a single-core
-- `schedulerInvariantBundleFull` preservation theorem (`schedule`,
-- `handleYield`, `timerTick`, `switchDomain`, `scheduleDomain`), plus a
-- base-aggregate bridge for `chooseThread`.  Composes existing single-
-- core preservation theorems with the SM4.C SMP-preservation skeleton.
import SeLe4n.Kernel.Scheduler.Invariant.PerCorePreservation
-- WS-SM SM4.D: cross-subsystem per-core invariant migration (plan §5.4).
-- The capstone `CrossSubsystemPerCore` transitively imports the four
-- per-subsystem per-core slices: `IPC.Invariant.PerCore` (the twelve
-- IPC↔scheduler coherence predicates lifted to `(c : CoreId)` forms +
-- the genuine `∀ c` SMP aggregates), `Capability.Invariant.PerCore`
-- (`cleanupNoStaleSchedRef` SMP "no stale ref on any core"),
-- `Architecture.InvariantPerCore` (`registerDecodeConsistent` per-core),
-- and `InformationFlow.ProjectionPerCore` (the six scheduler-reading IF-M1
-- projections + `projectStateOnCore` + per-core observability frame
-- lemmas).  It exports `crossSubsystemInvariant_perCore` (the per-core
-- master invariant) and `crossSubsystemSchedulerContract_perCore` (the
-- SM4.D capstone bundle), with boot-core bridges to the live single-core
-- surface.  Reachability: staged at SM4.D; SM5's per-core scheduler is
-- the first runtime exerciser (which will move them production-reached).
import SeLe4n.Kernel.CrossSubsystemPerCore
-- WS-SM SM4.D audit-pass-2: per-operation cross-subsystem SMP-preservation.
-- Connects the per-core / ∀c SMP invariant predicates to the kernel's
-- transitions: `…_holds_if_idle` idle-discharge lemmas, the generic
-- single-core→SMP lifters, the `passiveServerIdle_scheduledNowhere`
-- natural-SMP form, and 11 concrete per-operation preservation theorems
-- (8 IPC ops → `ipcSchedulerContractPredicates_smp`, 2 architecture ops →
-- `registerDecodeConsistent_smp`, `timerTick` → schedContext↔run-queue),
-- each reusing the existing single-core preservation verbatim.  SM5's
-- per-core scheduler is the first runtime exerciser.
import SeLe4n.Kernel.CrossSubsystemPerCorePreservation
-- WS-SM SM4.D audit-pass-3: the one Platform-layer scheduler-reader found by
-- the exhaustive audit — `registerContextStableCheck` (RPi5 runtime contract)
-- — lifted to the per-core `registerContextStableCheckOnCore` + boot-core
-- bridge + idle/default witnesses.  Platform/RPi5 is adjacent to SM4.D's six
-- subsystems; this completes the "every SchedulerState-reading def has a
-- per-core form" coverage.  SM5's per-core platform bring-up consumes it.
import SeLe4n.Platform.RPi5.RuntimeContractPerCore
-- WS-SM SM5.A: per-core `chooseThread` (plan
-- `SMP_PER_CORE_SCHEDULER_PLAN.md` §3.1, §5).  The selection function
-- `chooseThreadOnCore` itself is production-reached (the legacy
-- `chooseThread` delegates to it, SM5.A.5); this module collects the
-- forward-looking SM5.A theorems: the `RunQueueLockId` + the cross-domain
-- `SchedLockId` (object-lock ⊕ run-queue, plan §4.4 order) + the complete
-- two-domain `chooseThreadOnCoreLockSet` (SM5.A.2), the per-core-independence frame +
-- corollaries (SM5.A.3), idle-fallback completeness
-- (`chooseThreadOnCore_ok_of_runnableTCBs` / `_none_no_eligible` /
-- `_some_of_eligible`, SM5.A.4), selection soundness
-- (`chooseThreadOnCore_some_mem_runQueueOnCore`, SM5.A.6), and the
-- decidability witnesses (SM5.A.7).  Reachability: staged at SM5.A; SM5.B's
-- per-core `switchToThread` (which dispatches the chosen thread) is the
-- first runtime exerciser (which will move it production-reached).
import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
-- WS-SM SM5.B: per-core `switchToThread` (plan
-- `SMP_PER_CORE_SCHEDULER_PLAN.md` §3.2, §5).  The context-switch transition
-- `switchToThreadOnCore` itself (with `preemptCurrentOnCore` / the
-- `affinityAdmitsCore` gate) is in production `Scheduler.Operations.Selection`;
-- this module collects the forward-looking SM5.B theorems: the cross-domain
-- `switchToThreadOnCoreLockSet` (object-store + run-queue write locks, plan
-- §4.4 order; SM5.B.2), the switch-semantics theorems
-- (`switchToThreadOnCore_sets_current` SM5.B.1, `_preempts_previous` SM5.B.3,
-- `_rejects_remote` SM5.B.4, `_runQueueOnCore_excludes_current` SM5.B.5), the
-- cross-core-independence frame (`_independent_of_other_core`, SM5.B.6), and
-- the totality + decidability witnesses (SM5.B.8).  Reachability: staged at
-- SM5.B; SM5.C's cross-core wake / SGI dispatch loop is the first runtime
-- exerciser (wiring `switchToThreadOnCore` + the runtime `withLockSet`
-- acquisition over `switchToThreadOnCoreLockSet`).
import SeLe4n.Kernel.Scheduler.Operations.PerCoreSwitchToThread
-- WS-SM SM5.C: cross-core wake via SGI (plan `SMP_PER_CORE_SCHEDULER_PLAN.md`
-- §3.3, §4.4, §5).  The wake transitions (`enqueueRunnableOnCore`,
-- `determineTargetCore`, `wakeThread`, `handleRescheduleSgiOnCore`,
-- `setThreadCpuAffinity`) are production defs in `Scheduler.Operations.Selection`;
-- this module collects the forward-looking SM5.C theorems: the wake / SGI-handler
-- cross-domain lock-sets (SM5.C.3), the boot-default `determineTargetCore` routing
-- (SM5.C.9), the `enqueueRunnableOnCore` preservation/membership/make-ready/frame
-- lemmas (SM5.C.1), the wake-semantics theorems (`wakeThread_emits_sgi_if_remote`
-- SM5.C.4, `wakeThread_target_runQueue_contains` SM5.C.10, `wakeThread_lossless`
-- SM5.C.6), the SGI-handler theorems (SM5.C.5), the SGI delivery latency bound
-- (SM5.C.11), and the `setThreadCpuAffinity` characterisations (SM5.C.8).
-- Reachability: staged at SM5.C; SM5.D's per-core timer tick (whose cross-core
-- CBS-replenish wake calls `wakeThread`) is the first runtime exerciser.
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
-- WS-SM SM5.C: the cross-core-wake theorem inventory (83-entry typed
-- aggregator with `ccwt!` compile-time identifier validation + per-category
-- counts + partition-sum + Nodup witnesses), mirroring the per-object-lock /
-- lock-set / deadlock / serializability inventories.  A renamed / removed SM5.C
-- theorem fails the inventory's elaboration here.
import SeLe4n.Kernel.Scheduler.Operations.CrossCoreWakeInventory
-- WS-SM SM5.D: the per-core timer-tick theorem surface — the SM5.D.3 cross-domain
-- lock-set (`timerTickOnCoreLockSet` over the `SchedLockId` extended with the
-- replenish-queue domain) + WCRT bound, SM5.D.6 domain rotation, SM5.D.4 CBS
-- replenishment + cross-core wake (`cbsReplenish_can_wake_remote_core`), SM5.D.5
-- budget tick + the IPC-timeout objects-`invExt` preservation chain, and the
-- SM5.D.2 `timerTickOnCore` headlines (advances-per-core / preempts-local /
-- clears-lastTimeoutErrors / preserves-currentThreadInActiveDomainOnCore) +
-- objects-`invExt` preservation + SM5.D.8 decidability (domain rotation is the
-- separate atomic `scheduleDomainOnCore`, not the budget-only tick).  The
-- production transitions are in `Scheduler.Operations.Core`; SM5.I's per-core
-- scheduler-tick driver is the first runtime exerciser.
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick
-- WS-SM SM5.I: the verified per-core run-loop step (`perCoreTimerTickStep`) the
-- per-core timer-tick kernel entry drives — a pure decision core over the verified
-- `timerTickOnCore` transition (fail-closed reductions + objects-`invExt` /
-- current-thread-validity preservation), the SM5.F pattern's verified core.
import SeLe4n.Kernel.Scheduler.Operations.PerCoreRunLoop
-- WS-SM SM5.D.1 / SM5.I: the per-core timer-tick kernel entry seam
-- (`@[export lean_per_core_timer_tick]`) the Rust per-core CNTP ISR
-- (`timer::per_core_timer_tick_isr`) resolves against.  SM5.I rewires it from the
-- SM5.D `pure ()` placeholder into the live driver: atomically run
-- `perCoreTimerTickStep` against the kernel state, then fire the cross-core SGIs.
import SeLe4n.Kernel.PerCoreTimerEntry
-- WS-SM SM5.D: the 101-entry per-core-timer theorem inventory (7 categories:
-- lockSet/domain/replenish/budget/tick/preservation/decidability) with the `pctt!`
-- compile-time identifier-validation macro + per-category count + partition-sum +
-- Nodup witnesses; mirrors `CrossCoreWakeInventory`.  A renamed/removed SM5.D theorem fails
-- this module's elaboration.
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerInventory
-- WS-SM SM5.E: the per-core idle-thread theorem surface — SM5.E.5
-- `idleThread_priority_zero` + field lemmas, the SM5.E.3 `enqueueIdleThreadOnCore`
-- run-queue primitive (frame / membership / `invExt` + run-queue-wellFormed +
-- runnable-are-TCBs preservation), the SM5.E.6 keystone
-- `chooseThreadOnCore_always_succeeds` (+ the `idleThreadEnqueuedOnCore` discharge
-- predicate, its constructive establishment, and the end-to-end non-vacuity
-- witness), and the SM5.E.4 `idleThread_core_locality` (affinity-based + frame
-- companion).  The idle *definitions* live in `Platform.Boot` (SM4.G); SM5.I's
-- per-core dispatch loop is the first runtime exerciser.
import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdle
-- WS-SM SM5.E: the per-core idle-aware dispatcher (`scheduleOrIdleOnCore`, the
-- SM5.I dispatch-loop seed) establishment theorems — the headline
-- `scheduleOrIdleOnCore_runs_idle` (idle is dispatched in a production transition
-- when nothing else is runnable) + the soundness surface (currentThreadValid /
-- queueCurrentConsistent / objects-invExt / runQueueWellFormed), composing the
-- SM5.D `scheduleEffectiveOnCore` establishment surface with the idle-dispatch
-- case.  The production defs (`idleDispatchableOnCore` / `dispatchIdleOnCore` /
-- `scheduleOrIdleOnCore`) live in `Scheduler.Operations.Core`.
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDispatch
-- WS-SM SM5.E: the per-core-idle theorem inventory (categories field / enqueue /
-- preservation / lockSet / alwaysSucceeds / locality / dispatch) with the `pcit!`
-- compile-time identifier-validation macro + per-category count + partition-sum +
-- Nodup witnesses; mirrors `PerCoreTimerInventory`.  A renamed/removed SM5.E
-- theorem fails this module's elaboration.
import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdleInventory
-- WS-SM SM5.F: the per-core priority-inheritance theorem surface — SM5.F.1
-- `computeMaxWaiterPriorityOnCore` (per-core waiter slice) + the per-core ≤ global
-- decomposition, SM5.F.2 `updatePipBoostOnCore` (per-core bucket migration) +
-- `pipBoostWithWake` cross-core PIP wake (emits `.reschedule` iff remote + material),
-- SM5.F.3 `pipBoost_perCore_consistent`, SM5.F.4 `propagatePipChainCrossCore`
-- (donation chain across cores), SM5.F.5/.6 `restoreToReadyOnCore` /
-- `restoreToReadyWithWake` (per-core resume PIP recompute + cross-core resume wake),
-- SM5.F.7 `blockingGraphOnCore_consistent` + SM5.F.8 `blockingAcyclic_perCore`, and
-- SM5.F.9 `priorityInheritance_perCore_witness`.  The per-core PIP *transition* defs
-- (`computeMaxWaiterPriorityOnCore` / `updatePipBoostOnCore` / `pipBoostWithWake` /
-- `propagatePipChainCrossCore` in `Scheduler.PriorityInheritance.*`, `restoreToReadyOnCore`
-- / `restoreToReadyWithWake` in `Lifecycle.Suspend`) are production-reached; SM5.I's
-- runtime dispatch (wiring `pipBoostWithWake` / `restoreToReadyWithWake` into the live
-- donation / timeout / resume paths) is the first runtime exerciser.
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
-- WS-SM SM5.F: the per-core-PIP theorem inventory (categories compute / updateBoost /
-- consistent / wake / chain / resume / blockingGraph / witness) with the `ppit!`
-- compile-time identifier-validation macro + per-category count + partition-sum +
-- Nodup witnesses; mirrors `PerCoreIdleInventory`.  A renamed/removed SM5.F theorem
-- fails this module's elaboration.
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCoreInventory
-- WS-SM SM5.G: the per-core domain-scheduling theorem surface — SM5.G.2
-- `advanceDomainOnCore` (pure per-core domain rotation) + frame lemmas + single-step
-- index/domain/time formulas + the `advanceDomainOnCoreN` iteration and cyclic
-- theorem `advanceDomainOnCore_cyclic`, SM5.G.2 bridge
-- `switchDomainOnCore_activeDomain_eq_advanceDomainOnCore` (the production switch's
-- domain effect IS this rotation), SM5.G.3 `activeDomainOnCore_isInDomainSchedule`
-- establishment / SMP preservation / the plan §3.7 Theorem 3.7.1 membership form,
-- SM5.G.4 `chooseThreadOnCore_respects_activeDomain`, and SM5.G.5 cross-core domain
-- independence + the `advanceDomainOnCoreLockSet` footprint.  `advanceDomainOnCore`
-- is forward-looking (the live tick path rotates via `scheduleDomainOnCore` →
-- `switchDomainOnCore`); SM5.I's per-core run loop is the first runtime exerciser.
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDomain
-- WS-SM SM5.G: the per-core-domain theorem inventory (categories rotation / cyclic /
-- bridge / domainSchedule / respects / independence) with the `pcdt!` compile-time
-- identifier-validation macro + per-category count + partition-sum + Nodup witnesses;
-- mirrors `PerCoreIdleInventory`.  A renamed/removed SM5.G theorem fails this
-- module's elaboration.
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDomainInventory
-- WS-SM SM5.H: per-core CBS (Constant Bandwidth Server) theorem surface — SM5.H.2
-- `replenishOnCore` (the per-core CBS replenishment-scheduling primitive) + frames,
-- SM5.H.3 / SM5.H.6 / SM5.H.5 `replenishOnCore` validity / pipeline-order / affinity
-- preservation, SM5.H.4 `migrateSchedContextReplenishment` (SchedContext replenishment
-- migration on affinity change) + `setThreadCpuAffinityWithMigration` + the headline
-- restoration `schedContextMigration_consistent`, SM5.H.5 the plan §3.8 Theorem 3.8.1
-- affinity invariant `replenishQueueAffinityConsistentOnCore`, and SM5.H.7 the aggregate
-- `perCoreCbsInvariant` + CBS budget-bound accounting.  `replenishOnCore` / the migration
-- are forward-looking (the live per-core CBS path is the SM5.D `timerTickOnCore`; the
-- affinity-migration `tcbSetAffinity` syscall is SM5.I+); SM5.I's per-core run loop is the
-- first runtime exerciser.
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbs
-- WS-SM SM5.H: the per-core-CBS theorem inventory (categories predicate / replenish /
-- preservation / migration / affinityWrite / consistency / budget) with the `pccbst!`
-- compile-time identifier-validation macro + per-category count + partition-sum + Nodup
-- witnesses; mirrors `PerCoreDomainInventory`.  A renamed/removed SM5.H theorem fails this
-- module's elaboration.
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbsInventory

/-!
# AN7-D.6 (PLT-M07) — Staged-modules build graph

This meta-module pulls seven platform-binding-adjacent modules into the
dependency graph so that `lake build SeLe4n.Platform.Staged` (and, via
`scripts/test_tier1_build.sh`, every CI run) forces each one to compile.
Without this wiring, the seven modules are orphans — they are not reached
from `Main.lean` or from any production kernel chain, so a regression that
breaks them would go undetected until the H3 hardware-binding workstream
reaches them.

The staged modules are:

1. `SeLe4n.Platform.Sim.Contract`              — Sim platform contract
2. `SeLe4n.Platform.FFI`                       — Lean @[extern] FFI declarations
3. `SeLe4n.Platform.RPi5.Contract`             — RPi5 platform contract
4. `SeLe4n.Platform.RPi5.VSpaceBoot`           — AN7-D.2 RPi5 boot VSpaceRoot
5. `SeLe4n.Kernel.Architecture.CacheModel`     — Cache coherency model
6. `SeLe4n.Kernel.Architecture.ExceptionModel` — ARM64 exception model
7. `SeLe4n.Kernel.Architecture.TimerModel`     — ARM generic timer model
8. `SeLe4n.Kernel.Architecture.BarrierComposition` — AN9-C BarrierKind algebra
9. `SeLe4n.Kernel.Architecture.TlbCacheComposition` — AN9-A page-table coherency
10. `SeLe4n.Kernel.Concurrency.Assumptions`    — AN12-B SMP-latent inventory
11. `SeLe4n.Kernel.Concurrency.Anchors`        — WS-SM SM0.C inventory build anchor (SMP-H3)
12. `SeLe4n.Kernel.Concurrency.Types`          — WS-SM SM0.E/SM0.F CoreId + SharingDomain
13. `SeLe4n.Kernel.Concurrency.Locks`          — WS-SM SM0.I BklState
14. `SeLe4n.Kernel.Concurrency.Locks.Kind`     — WS-SM SM0.I LockKind + LockId
15. `SeLe4n.Kernel.Concurrency.Sgi`            — WS-SM SM0.H SgiKind
16. `SeLe4n.Kernel.Concurrency.Runtime`        — WS-SM SM1.B.5 currentCoreId FFI wrapper
17. `SeLe4n.Kernel.SecondaryEntry`             — WS-SM SM1.C.6 secondary-core kernel-entry placeholder
18. `SeLe4n.Kernel.Architecture.TlbiForSharing` — WS-SM SM1.E.4 typed TLBI FFI dispatcher
19. `SeLe4n.Kernel.Concurrency.MemoryModel`     — WS-SM SM2.A abstract memory model
20. `SeLe4n.Kernel.Concurrency.Locks.TicketLock` — WS-SM SM2.B abstract TicketLock spec
21. `SeLe4n.Kernel.Concurrency.Locks.RwLock`    — WS-SM SM2.C abstract RwLock spec
22. `SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement` — WS-SM SM2.C.20 refinement bridge

Per the plan (AN9-J will transition most of these from "SMP-latent" to
"SMP-implemented, runtime-gated by smp_enabled=false at v1.0.0"), the
module remains present as a confirmation inventory rather than a
pending-work surface.  See `docs/spec/SELE4N_SPEC.md` §8.15 for the
activation roadmap.

Every imported module carries its own
`-- STATUS: staged for H3 hardware binding` header comment at the top of
its file (PLT-M07 requirement); this module plus the CI hygiene check
guarantees they all continue to compile.
-/

namespace SeLe4n.Platform.Staged

/-- AN7-D.6 anchor: a dummy definition whose mere presence forces Lean to
    link the seven imported modules into this compilation unit.  `lake
    build SeLe4n.Platform.Staged` will fail loudly if any of those modules
    acquires a broken proof. -/
def stagedBuildAnchor : Unit := ()

end SeLe4n.Platform.Staged
