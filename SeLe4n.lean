-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Machine
import SeLe4n.Model.Object
import SeLe4n.Model.State
-- WS-SM SM3.A audit-pass-6: pull the SM3.A theorem inventory into the
-- production import closure so `lake build` (default target) catches
-- regressions in the 34-entry aggregator at the production-build step,
-- not just at the Tier-3 invariant-surface or test-suite levels.  The
-- inventory has no run-time semantics (it is a documentation/audit
-- artifact); production reachability ensures CI cannot drop it
-- silently.
import SeLe4n.Model.Object.PerObjectLockInventory
import SeLe4n.Kernel.API
-- WS-RR RR8.10: the cancellation's arm-complete IPC bundle and its cross-core
-- lift.  Its three arm theorems live in three different modules, so the
-- composite has no natural home among them; putting it in the production import
-- closure is what keeps it inside every Tier 1 census's derived domain (the
-- `v0.35.60` lesson: a module outside the root is exempt from most of this
-- tree's defences by omission rather than by decision).
import SeLe4n.Kernel.IPC.Invariant.CancellationBundle
import SeLe4n.Kernel.Architecture.VSpaceBackend
import SeLe4n.Kernel.Architecture.TlbModel
import SeLe4n.Kernel.Architecture.RegisterDecode
-- WS-RA: the syscall return convention (ReturnShape / SyscallReturnFrame /
-- SyscallOutcome / the offset error label) — the return-direction dual of
-- RegisterDecode / SyscallArgDecode.
import SeLe4n.Kernel.Architecture.SyscallReturn
import SeLe4n.Platform.Contract
import SeLe4n.Platform.Boot
import SeLe4n.Platform.FFI
import SeLe4n.Platform.Sim.Contract
import SeLe4n.Platform.RPi5.Contract
-- WS-SM SM6.A (live cross-core `.call` completion): the cross-core syscall
-- dispatch entry `syscallDispatchCrossCoreEntry`
-- (`@[export lean_syscall_dispatch_cross_core]`) — the live seam the Rust SVC
-- handler resolves against, which fires the diff-recovered cross-core
-- `.reschedule` SGIs.  Pulls its closure (`Concurrency.Runtime`,
-- `Scheduler.PriorityInheritance.PerCore`) into the production library so the
-- `@[export]` symbol is emitted into the kernel image.
import SeLe4n.Kernel.SyscallDispatchEntry
-- WS-RR RR5.15: the other three state-committing kernel entries, promoted into
-- the production library for exactly the reason `SyscallDispatchEntry` was.
-- `kernel_entry.rs` tabulates five Lean entries that commit kernel state and
-- declares each as a hard `extern "C"` symbol; only one was production-reachable,
-- so `lake build SeLe4n:static` emitted a single `T lean_*` entry symbol and a
-- linked image would have failed to resolve the other three — the three whose
-- Rust seams the SM10.1 image needs on every secondary core.  Their modules were
-- staged-only, reachable from `Platform.Staged` and nothing else.
--
-- The `@[export]` symbol is emitted iff the defining module is in this library's
-- import closure, so promotion is the whole fix; `scripts/check_kernel_entry_exports.sh`
-- (RR5.16) verifies each symbol against the built archive rather than against
-- this import list, so a future regression is caught by object code.
--
-- WS-SM SM5.I: the per-core timer-tick entry `perCoreTimerTickEntry`
-- (`@[export lean_per_core_timer_tick]`) — the driver `timer::per_core_timer_tick_isr`
-- resolves against, committing `perCoreTimerTickStep` through
-- `modifyGetKernelState` and firing the recovered cross-core `.reschedule` SGIs.
import SeLe4n.Kernel.PerCoreTimerEntry
-- WS-SM SM5.C.5: the per-core reschedule entry `perCoreRescheduleEntry`
-- (`@[export lean_per_core_reschedule]`) — the receiver seam of the cross-core
-- wake protocol, resolved by `trap.rs::reschedule_sgi_handler` (SGI INTID 0).
import SeLe4n.Kernel.PerCoreRescheduleEntry
-- WS-SM SM1.C.6 / SM5.C.5: the secondary-core bring-up entry
-- `secondaryKernelMain` (`@[export lean_secondary_kernel_main]`), called by
-- `smp::rust_secondary_main` inside the kernel-entry bracket before `enable_irq`.
-- Definitionally the core's first reschedule
-- (`secondaryKernelMain_eq_perCoreRescheduleEntry`).
import SeLe4n.Kernel.SecondaryEntry
-- WS-SM SM6.D: the per-core IPC invariant bundle (`ipcInvariantFull_perCore`,
-- the four named per-core conjuncts, exact-decomposition bridges) and its
-- per-operation preservation layer (send/receive/call/reply/replyRecv/
-- signal/wait preserve every core's bundle view; per-core
-- `passiveServerIdle` frame family with no idle-core assumption).  Pulled
-- into the production library so the SM6.D theorem surface is
-- production-reachable (the cross-core `endpointCallOnCore` mirror lives in
-- the staged `IPC.CrossCore.EndpointCallInvariant`).
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundle
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundlePreservation
-- WS-SM SM6.D (completion): pointwise-lookup congruences for every
-- `ipcInvariantFull` conjunct + the `OffSchedulerAgrees` relation and its
-- step congruences — the transfer layer that carries the single-core
-- whole-bundle theorems across the cross-core scheduler substitutions.
-- (Consumed by the production `NotificationInvariant` /
-- `EndpointReplyInvariant` whole-bundle closures; imported here explicitly
-- so the congruence surface is directly production-anchored.)
import SeLe4n.Kernel.IPC.Invariant.LookupCongruence
-- WS-SM SM6.E: cancellation across cores — the `descheduleThread` per-core
-- deschedule primitive (the SM5.C `wakeThread` dual), the cross-core
-- cancellation composite `cancelIpcBlockingOnCore`, the per-core donation
-- cancellation (`cancelBoundDonationOnCore` / `cancelDonationOnCore`), the
-- `lockSet_cancelIpcBlocking` / `lockSet_cancelDonation` footprints with
-- suspend-footprint coverage, the 2PL atomicity theorems, and the flagship
-- `cancellation_cross_core_correct`.  Pulled into the production library so
-- the SM6.E theorem surface is production-reachable ahead of the live
-- `.tcbSuspend` cross-core dispatch wiring (the phase's tracked follow-on).
import SeLe4n.Kernel.IPC.CrossCore.Cancellation
-- WS-RR RR7.22 (residual): the cancellation sweep's queue shape — the
-- `dualQueueSystemInvariant` carriage across `removeFromAllEndpointQueues`
-- followed by the field clear, together with the one queue-shape fact
-- `ipcInvariantFull` does not entail (`sweptThreadBoundaryCoherent`, stated
-- rather than assumed, the way RR7.22 stated `splicePredecessorBlocked`).
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationQueueShape
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationNotificationShape
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationReplyShape
-- `v0.35.166` (WS-RR RR8.12, register row 63): the destroy path's reservation
-- theorems.  `lifecyclePreRetypeCleanup` preserves the SM5.H replenish-affinity
-- invariant — the composite `v0.35.164` and `v0.35.165` each left owed, since
-- each gave an *arm* its theorem and the frames the program over them needs were
-- `private` in a module downstream of both the cleanup and the retype wrapper.
-- It sits below the two `Cancellation*Shape` modules above (which is the only
-- layer that sees every frame it composes) and above nothing.
import SeLe4n.Kernel.Lifecycle.Invariant.RetypeReservation
-- WS-SM SM7.B: the TLB shootdown protocol — `tlbShootdownLocal` /
-- `tlbShootdownBroadcast` / `handleTlbShootdownReqOnCore`, the round
-- composition with its quiescence capstone, Theorem 3.3.1
-- (`tlbShootdownBroadcast_invalidatesAllCores`), the caller-facing
-- shootdown-aware kernel operations (unmap / remap / ASID flush /
-- ASID allocate), the initiator-side synchronization + termination +
-- timeout theorems (`shootdownAck_release_acquire`,
-- `shootdown_wait_loop_terminates`, `shootdown_timeout_handling`), and
-- the round's cross-domain lock-set (`TlbShootdownLockId`,
-- `lockSet_tlbShootdown_correct`).  Protocol + Wait reach production
-- through `Kernel.API` (the SM7.B.9 dispatch arms) already; the
-- explicit imports anchor the Wait + LockSet theorem surfaces the way
-- the SM6.D/SM6.E entries above do.
import SeLe4n.Kernel.Architecture.TlbShootdownProtocol
import SeLe4n.Kernel.Architecture.TlbShootdownWait
import SeLe4n.Kernel.Architecture.TlbShootdownLockSet
-- WS-SM SM7.C: the per-core TLB model (perCoreTlb accessors + ops +
-- tlbInvalidationConsistent_perCore, the 13th proofLayerInvariantBundle
-- conjunct) — mounted on `SystemState.perCoreTlb`.
import SeLe4n.Kernel.Architecture.PerCoreTlbModel
-- WS-SM SM7.D: the per-core **instruction-cache** model — the cache-side
-- companion of `PerCoreTlbModel`.  `IC IALLU` reaches only the executing PE,
-- so the kernel must issue the inner-shareable broadcast variant
-- (`icInvalidateBroadcast`) whenever it retires an executable mapping or
-- re-purposes memory; `icacheCoherent_perCore` (every cached line still has a
-- live executable mapping) is the 14th `proofLayerInvariantBundle` conjunct.
-- Also carries the SM7.D.2 data-cache-at-PoC reach theorems and the SM7.D.3
-- DMA scope tripwire.
import SeLe4n.Kernel.Architecture.PerCoreCacheModel
-- WS-SM SM7.B (SM1.E.4 promotion): the typed `tlbiForSharing` FFI
-- dispatcher — the shootdown round's runtime TLBI emitter
-- (`SyscallDispatchEntry.completeShootdownRounds` is the first runtime
-- exerciser, closing the SM1.E "staged until SM7" note).
import SeLe4n.Kernel.Architecture.TlbiForSharing
-- WS-RR RR2.5 / RR2.14: the invariant surfaces the live IPC paths needed and
-- did not have — the SchedContext donation primitives' own preservation
-- theorems (`IPC.Invariant.DonationPreservation`: the store walk, the
-- `donationReadAgreement` it establishes, the whole-bundle theorems for
-- `applyCallDonation{,OnCore}` / `applyReplyDonation`, and §8's
-- priority-inheritance chain-walk bundle), the capability transfer's
-- (`IPC.Invariant.CapTransferBundle`), and the live `.reply` dispatch chain's
-- (`IPC.CrossCore.EndpointReplyDispatchInvariant`).  All three are
-- production-clean.  Of the two dispatch chains only the `.call` chain's bundle
-- (`IPC.CrossCore.DispatchInvariant`) reads the staged cross-core call surface
-- and is staged with it, anchored from `Platform.Staged`.
import SeLe4n.Kernel.IPC.Invariant.DonationPreservation
import SeLe4n.Kernel.IPC.Invariant.CapTransferBundle
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatchInvariant
-- WS-RR (bind/unbind affinity closure): the replenish-queue invariant surface
-- for the two live arms that create and destroy a SchedContext's binding —
-- the orphan-freedom invariant (`replenishQueueEntriesBound_smp`), the
-- `schedContextBind` / `schedContextUnbind{,OnCore}` preservation theorems for
-- it and for `replenishQueueAffinityConsistent_smp`, and their object-store
-- invariant carriers.  Production-clean.
import SeLe4n.Kernel.SchedContext.BindingAffinity
-- WS-RR RR4: the fault-IPC path — the `Fault` type and wire format
-- (`Kernel.Architecture.Fault`), handler resolution and the fail-closed
-- dispositions (`Kernel.IPC.Operations.Fault`), the cross-core delivery and
-- reply (`Kernel.IPC.CrossCore.Fault`), the RR4.19 progress theorem
-- (`Kernel.IPC.Invariant.FaultProgress`) and the C-callable seam the Rust trap
-- handler resolves against (`lean_handle_fault` /
-- `lean_classify_synchronous_exception`).  One import: the entry's transitive
-- closure is the whole production fault surface.
import SeLe4n.Kernel.FaultEntry
-- **The frozen execution surface is production** (`v0.35.60`).  It was outside
-- both library roots and in no staged allowlist, built only by its own
-- `lean_exe` — which put it outside the *derived* domain of five of the six
-- Tier 1 censuses and outside the production/staging partition gate entirely.
-- That is this tree's own *a recognised set is not a derived set* rule at the
-- scale of a subsystem, and it cost five after-the-fact corrections
-- (`v0.35.12`, `v0.35.38`, `v0.35.47`, `v0.35.52`, `v0.35.58`), each found by a
-- later cut rather than by a gate, on a surface that carries the **live**
-- `TCB`, `Reply`, `SchedContext` and `IntrusiveQueue` records and mirrors the
-- reply and cancellation spines.
--
-- Two imports reach all five modules: `Agreement` pulls `Operations` → `Core`
-- and the live `Kernel.API` it is refined against, `Invariant` pulls
-- `Commutativity` → `Operations`.  The dependency runs frozen → production and
-- never the reverse, so this closes no cycle.
import SeLe4n.Kernel.FrozenOps.Agreement
import SeLe4n.Kernel.FrozenOps.Invariant
-- **The one remaining re-export hub that no build target reached** (`v0.35.60`).
-- Measured while promoting `FrozenOps`: of the 331 files the published
-- `readme_sync.production_*` metric counts as production, 251 are in this root's
-- closure and the rest are reached by `Platform.Staged`, a Tier 1 census or a
-- `lean_exe` — all but `SeLe4n.Kernel.RadixTree`, a hub with zero in-tree
-- consumers that nothing compiled.  Its three re-exports were therefore never
-- checked as a unit, so a re-export naming a renamed or deleted submodule would
-- have been invisible.  The submodules are already in this closure; this import
-- adds only the hub, which is the point -- a file outside every build target is
-- checked by nothing, which is the `FrozenOps` finding one file smaller.
import SeLe4n.Kernel.RadixTree
-- **Five more files outside both library roots** (`v0.35.76`).  The
-- store-access census's Tier 1 reconciliation
-- (`SeLe4n/Testing/StoreReadClassificationCensus.lean`) started refusing a row
-- in a module its environment does not contain, and its first run named
-- `Scheduler/PriorityInheritance/ChainFootprint.lean`.  Measured with the two
-- roots as the criterion -- the criterion every Tier 1 census's environment
-- actually uses, where the `v0.35.60` count above accepted a `lean_exe` as
-- reach -- five non-test modules were outside both.  Three come here: the
-- `Scheduler/PriorityInheritance` hub and the `FrozenOps` hub (RadixTree's
-- shape again, each reached by test suites alone, so a re-export naming a
-- deleted submodule was checked as a unit by nothing in CI -- their
-- submodules are already in this closure); and `ChainFootprint`, whose RR7.40
-- header says PRODUCTION and which no root imported, so its only staged
-- dependency (`Concurrency/Locks/DynamicChainExtension`, every import of which
-- was already here) is promoted with it.  The other two --
-- `Architecture/VSpaceARMv8` and `Capability/CSpaceWalkFootprint` -- are staged
-- instead; `Platform/Staged.lean` says why each cannot be here.
import SeLe4n.Kernel.Scheduler.PriorityInheritance
import SeLe4n.Kernel.FrozenOps
import SeLe4n.Kernel.Scheduler.PriorityInheritance.ChainFootprint
