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
import SeLe4n.Kernel.Architecture.VSpaceBackend
import SeLe4n.Kernel.Architecture.TlbModel
import SeLe4n.Kernel.Architecture.RegisterDecode
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
-- WS-SM SM7.B (SM1.E.4 promotion): the typed `tlbiForSharing` FFI
-- dispatcher — the shootdown round's runtime TLBI emitter
-- (`SyscallDispatchEntry.completeShootdownRounds` is the first runtime
-- exerciser, closing the SM1.E "staged until SM7" note).
import SeLe4n.Kernel.Architecture.TlbiForSharing
