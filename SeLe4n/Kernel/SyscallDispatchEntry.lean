-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.A: PRODUCTION (LANDED).  The cross-core-aware syscall dispatch entry
-- `syscallDispatchCrossCoreEntry` (`@[export lean_syscall_dispatch_cross_core]`)
-- is the live seam the Rust SVC handler resolves against; it runs the verified
-- `syscallDispatchFromAbi` (per-core caller via the threaded `executingCore`) and
-- fires the diff-recovered cross-core `.reschedule` SGIs.  (Former "STATUS:
-- staged" marker replaced with this landing note per the implement-the-improvement
-- rule; see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md.)

import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Concurrency.Runtime
-- WS-SM SM6.E: the per-core suspend behind `suspendThreadCrossCoreEntry`.
import SeLe4n.Kernel.IPC.CrossCore.Cancellation
-- WS-SM SM7.B: the shootdown round's pure transitions + diff recovery
-- (`shootdownChangedTargets` / `shootdownPostedOps` /
-- `handleTlbShootdownReqOnCore`), the wait budget, and the typed
-- broadcast-TLBI dispatcher behind `completeShootdownRounds`.
import SeLe4n.Kernel.Architecture.TlbShootdownProtocol
import SeLe4n.Kernel.Architecture.TlbShootdownWait
import SeLe4n.Kernel.Architecture.TlbiForSharing
import SeLe4n.Platform.FFI

/-!
# WS-SM SM6.A — Cross-core syscall dispatch entry (the live SGI-dispatch seam)

The C-callable seam the Rust SVC trap handler (`svc_dispatch::dispatch_svc`)
invokes for every syscall, in its cross-core-aware form.  It is the syscall
analogue of `perCoreTimerTickEntry` (the per-core timer ISR seam): it runs the
verified pure dispatch (`Platform.FFI.syscallDispatchFromAbi`) atomically against
the live kernel state, then **fires the cross-core `.reschedule` SGIs that the
state transition warrants** — recovered purely from the `(pre, post)` diff by
the SM5.F.4 dispatch `computeCrossCoreSgis`.

This closes the live half of the SM5.F.4 diff-based cross-core SGI dispatch for
the syscall path: the existing `Platform.FFI.syscallDispatchInner` commits the
post-state but never pokes a remote core, so a syscall whose effect makes a remote
thread newly runnable (an endpoint-call receiver or notification waiter / bound TCB
woken on another core — WS-SM SM6.A/SM6.B) or migrates its run-queue bucket (a
`.call`'s donation boosting a passive server pinned to another core) would leave
that core unscheduled until its next local timer tick.  This entry fires the IPI
immediately after the commit.  (The `computeCrossCoreSgis` diff recovers *both*
cases — see `crossCoreSgiBody_remote_wake` for the wake direction.)

**Single-core inertness (trace safety).** On the boot core,
`PriorityInheritance.computeCrossCoreSgis pre post bootCoreId = []` whenever every
thread's home core is the boot core (`computeCrossCoreSgis_nil_single_core`), and
`Concurrency.fireCrossCoreSgis [] = pure ()`.  So on the single-core
configuration the entry is observably identical to the boot-pinned
`syscallDispatchInner` — it commits the same state and performs no IPI.  The
model-layer trace harness exercises the pure `syscallEntry`, not this BaseIO
seam, so the golden trace is unaffected.

The `@[export lean_syscall_dispatch_cross_core]` keeps the symbol live for the
Rust extern.  The live switchover (the trap handler calling this instead of the
boot-pinned `syscall_dispatch_inner`) lands with the per-core dispatch seam,
when the executing core is threaded into `syscallDispatchFromAbi` so the calling
thread is identified and descheduled on its own core rather than the boot core.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-- **WS-SM SM7.B.12**: the sharing domain the live shootdown round's
TLBIs are issued in.  `.inner` on the single-cluster BCM2712
(`PlatformBinding.sharingDomain RPi5Platform = .inner`; the test suite
pins the agreement) — a multi-cluster port flips this to `.outer`, and
only this: the state protocol is domain-invariant
(`Architecture.tlbShootdown_outer_correct`), so every SM7.B round
theorem carries over unchanged. -/
def shootdownSharingDomain : Concurrency.SharingDomain := .inner

/-- **WS-SM SM7.B.7**: the cooperative round-lock acquire — spin on the
try-lock, and on every failed attempt **service this core's own
pending shootdown obligation** (its Rust ack flag down ⇒ an in-flight
round is waiting on this core: invalidate the local TLB and
release-acknowledge, exactly the `.tlbShootdownReq` handler's effect).

Without the servicing arm this loop would deadlock into the holder's
wait-timeout panic: the holder's round waits on THIS core's ack, and
with IRQs masked in the SVC path the `.tlbShootdownReq` SGI can never
preempt the spin.  With it, a lock-waiter discharges the in-flight
round's obligation itself (over-invalidation-safe full local flush —
the same conservative effect as the Rust handler; the holder's
catch-up commit drains the Lean-side queue), so the holder always
completes and releases.

Fuel-bounded fail-closed (the SM7.B.6 discipline): the fuel covers
> 10⁵ round-lengths of retries — exhaustion means a genuinely wedged
round holder, and halting is the safe verdict (proceeding without the
round would be the SMP-C4 hazard). -/
def acquireShootdownRoundLockServicingSelf
    (execCore : Concurrency.CoreId) : BaseIO Unit := do
  let rec go : Nat → BaseIO Unit
    | 0 => panic! "WS-SM SM7.B.7: shootdown round-lock acquire exhausted \
        its fuel — the in-flight round's holder is wedged; halting \
        fail-closed"
    | fuel + 1 => do
        if (← Concurrency.shootdownRoundLockTryAcquire) then
          pure ()
        else
          if !(← Concurrency.shootdownAckIsSet execCore) then
            Architecture.tlbiForSharing shootdownSharingDomain .vmalle1
            Concurrency.shootdownAckSet execCore
          go fuel
  go 1000000

/-- **WS-SM SM7.B (the live round runtime)**: complete the shootdown
round(s) a syscall commit posted — the runtime realisation of plan
§3.2 steps 1–6 around the already-committed pure posting.

`changed` is the diff-recovered posted-target set
(`Architecture.shootdownChangedTargets pre post`) and `ops` the
deduplicated posted operands (`Architecture.shootdownPostedOps`); when
no round was posted this is `pure ()` (single-syscall inertness — no
existing syscall's runtime behaviour changes).

Sequence, under THE global round lock (the SM7.A round-serialisation
contract — the ack vector carries no round identity; acquired
cooperatively, `acquireShootdownRoundLockServicingSelf`):

1. `shootdownResetForRound` — the Rust masked reset: online targets
   drop, offline cores and the initiator are born-acknowledged.
2. One `.tlbShootdownReq` SGI per **online** non-initiator core (the
   SM7.A PR #838 P1 target-set obligation).  The full non-initiator
   set is poked — not just `changed` — because the reset dropped every
   online target's flag, and the handler is idempotent
   (`handleTlbShootdownReqOnCore_idempotent`); poking a subset could
   strand a reset flag and hang the wait.
3. The initiator's local broadcast TLBIs — one `tlbiForSharing` per
   posted operand (each ends with the `dsb`+`isb` bracket).
4. Bounded `allAcked` wait; timeout is a fail-closed panic
   (`shootdown_timeout_handling`: the verdict is exact, so the panic
   only fires on a genuinely hung round).
5. Model catch-up: fold `handleTlbShootdownReqOnCore` over the
   targets — every queue drained, every model flag re-set, restoring
   quiescence (`shootdownRound_quiescent`) so the next round's posting
   succeeds.  Committed after the hardware acks certified that every
   target's TLBIs retired (`shootdownAck_release_acquire`).

On the v1.0.0 single-online-core boot this degenerates to: reset
(everything born-acknowledged), zero SGIs, the local TLBIs, an
immediately-satisfied wait, and the catch-up commit. -/
def completeShootdownRounds (changed : List Concurrency.CoreId)
    (ops : List Architecture.TlbInvalidation)
    (execCore : Concurrency.CoreId) : BaseIO Unit := do
  if changed.isEmpty then
    pure ()
  else do
    acquireShootdownRoundLockServicingSelf execCore
    Concurrency.shootdownResetForRound execCore
    for c in Architecture.shootdownTargets execCore do
      if (← Concurrency.shootdownCoreOnline c) then
        Concurrency.sendSgiToCore c .tlbShootdownReq
    for op in ops do
      Architecture.tlbiForSharing shootdownSharingDomain op
    let acked ← Concurrency.shootdownWaitAllAcked
      Architecture.shootdownWaitTimeoutTicks
    Concurrency.shootdownRoundLockRelease
    if !acked then
      panic! "WS-SM SM7.B.6: TLB shootdown round timed out — a target \
        core is hung or deaf; halting fail-closed (a silently skipped \
        invalidation would be the SMP-C4 stale-TLB hazard)"
    Platform.FFI.modifyGetKernelState (fun st =>
      ((), (Architecture.shootdownTargets execCore).foldl
        Architecture.handleTlbShootdownReqOnCore st))

/-- **WS-SM SM6.A**: the cross-core-aware syscall dispatch entry — the live
SGI-dispatch seam.  Reads the deployment labeling context and the executing core
from the hardware (`currentCoreId`), runs the verified
`Platform.FFI.syscallDispatchFromAbi` atomically against the kernel state ref
(`modifyGetKernelState`, committing the post-state), then — *after* the commit —
fires the cross-core `.reschedule` SGIs recovered from the `(pre, post)` diff by
`PriorityInheritance.computeCrossCoreSgis`, then — WS-SM SM7.B — runs the TLB
shootdown round(s) the commit posted (`completeShootdownRounds`, recovered from
the `tlbShootdown` diff; inert for every non-shootdown syscall).  Returns the
ABI-encoded result word
(every kernel rejection is encoded into the success word with bit 63 set, so the
pure dispatch never takes the `.error` arm; the arm is discharged inertly). -/
@[export lean_syscall_dispatch_cross_core]
def syscallDispatchCrossCoreEntry
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 : UInt64)
    (ipcBufferAddr : UInt64) : BaseIO UInt64 := do
  let ctx ← Platform.FFI.getKernelLabelingContext
  let execCore ← Concurrency.currentCoreId
  let result ← Platform.FFI.modifyGetKernelState (fun st =>
    match Platform.FFI.syscallDispatchFromAbi ctx execCore syscallId msgInfo x0 x1 x2 x3 x4 x5
        ipcBufferAddr st with
    | Except.ok (encoded, st') =>
        ((encoded, PriorityInheritance.computeCrossCoreSgis st st' execCore,
          Architecture.shootdownChangedTargets st st',
          Architecture.shootdownPostedOps st st'), st')
    | Except.error e =>
        ((Platform.FFI.encodeError e, ([] : List (CoreId × SgiKind)),
          ([] : List CoreId),
          ([] : List Architecture.TlbInvalidation)), st))
  Concurrency.fireCrossCoreSgis result.2.1
  -- WS-SM SM7.B: run the shootdown round(s) this commit posted (inert
  -- when the syscall touched no pending-shootdown queue).
  completeShootdownRounds result.2.2.1 result.2.2.2 execCore
  pure result.1

/-- **WS-SM SM6.A** structural marker: `syscallDispatchCrossCoreEntry` unfolds to
the read-context / read-core / commit-dispatch / fire-SGIs / return-encoded
driver.  Pins the body shape (atomic `modifyGetKernelState` over
`syscallDispatchFromAbi`, then `fireCrossCoreSgis` of the diff-recovered SGIs) so
a refactor that drops the SGI firing or the state commit breaks this marker at
elaboration; combined with `@[export]` (which the Rust extern resolves against)
the seam cannot regress silently. -/
theorem syscallDispatchCrossCoreEntry_def
    (syscallId : UInt32) (msgInfo : UInt64) (x0 x1 x2 x3 x4 x5 : UInt64)
    (ipcBufferAddr : UInt64) :
    syscallDispatchCrossCoreEntry syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr =
      (do
        let ctx ← Platform.FFI.getKernelLabelingContext
        let execCore ← Concurrency.currentCoreId
        let result ← Platform.FFI.modifyGetKernelState (fun st =>
          match Platform.FFI.syscallDispatchFromAbi ctx execCore syscallId msgInfo x0 x1 x2 x3 x4 x5
              ipcBufferAddr st with
          | Except.ok (encoded, st') =>
              ((encoded, PriorityInheritance.computeCrossCoreSgis st st' execCore,
                Architecture.shootdownChangedTargets st st',
                Architecture.shootdownPostedOps st st'), st')
          | Except.error e =>
              ((Platform.FFI.encodeError e, ([] : List (CoreId × SgiKind)),
                ([] : List CoreId),
                ([] : List Architecture.TlbInvalidation)), st))
        Concurrency.fireCrossCoreSgis result.2.1
        completeShootdownRounds result.2.2.1 result.2.2.2 execCore
        pure result.1) := rfl

/-- **WS-SM SM6.A** trace-safety witness: on the boot core, when every thread's
home core is the boot core (the single-core configuration), the diff-recovered
SGI list the entry fires is empty.  Combined with `fireCrossCoreSgis [] = pure ()`
this is the machine-checked statement that the cross-core entry is observably
identical to a plain commit-and-return on single-core — it commits the same
post-state and performs no IPI.  Re-exports `computeCrossCoreSgis_nil_single_core`
at the entry's dispatch granularity. -/
theorem syscallDispatchCrossCoreEntry_sgis_nil_single_core
    (pre post : SystemState)
    (hAllBoot : ∀ t : SeLe4n.ThreadId,
      determineTargetCore post t = Concurrency.bootCoreId)
    (hNoRemoteCur : ∀ c : Concurrency.CoreId, c ≠ Concurrency.bootCoreId →
      pre.scheduler.currentOnCore c = none) :
    PriorityInheritance.computeCrossCoreSgis pre post Concurrency.bootCoreId = [] :=
  PriorityInheritance.computeCrossCoreSgis_nil_single_core pre post hAllBoot hNoRemoteCur

/-- **WS-SM SM6.E**: the cross-core-aware suspend entry — the per-core seam the
Rust `sele4n_suspend_thread` atomicity bracket resolves against (the suspend
analogue of `syscallDispatchCrossCoreEntry`, superseding the boot-pinned
`Platform.FFI.suspendThreadInner`).  Reads the executing core from the hardware
(`currentCoreId`), runs the verified per-core
`Lifecycle.Suspend.suspendThreadOnCore` atomically against the kernel state ref
(committing the post-state; the pre-state is kept on every error), then —
*after* the commit — fires the **diff-recovered** cross-core `.reschedule`
SGIs (`computeCrossCoreSgis` over the committed pre/post pair), exactly as
`syscallDispatchCrossCoreEntry`.  The diff subsumes the single SGI
`suspendThreadOnCore` surfaces (the victim-deschedule poke is re-derived by
the diff seam's SM6.E descheduled-current rule,
`crossCoreSgiBody_remote_deschedule`) and additionally recovers the G2b
PIP-revert pokes — a suspend that severs a donation chain lowers remote
chain members' effective run-queue buckets, and each such member's home
core must re-run its scheduler (PR #831 review: the pre-fix entry fired
only the surfaced victim SGI, leaving the re-bucketed cores unpoked until
their next timer tick).  Sentinel `tid`s are rejected at the boundary
Sentinel `tid`s are rejected at the boundary
exactly as `suspendThreadInner`.

**Authority obligation (audit note).**  This export performs NO capability
check — it is the *mechanism* seam below the dispatch layer.  Its only
sanctioned caller is the Rust AN9-D atomicity bracket
(`sele4n_suspend_thread`), reached from the capability-gated syscall path;
the symbol is unreachable from user mode (user code enters via SVC →
`dispatch_svc` only).  Any future in-kernel caller MUST carry its own
authority for the target thread (a `.write`-bearing TCB capability or an
equivalent kernel-internal justification) — calling this raw seam without
one is a privilege-escalation bug, not a supported use.

**Single-core inertness (trace safety).**  On an all-boot deployment every
diff-derived SGI list is empty (`computeCrossCoreSgis_nil_single_core`), so
the entry commits the same post-state with no IPI. -/
@[export suspend_thread_cross_core]
def suspendThreadCrossCoreEntry (tid : UInt64) : BaseIO UInt32 := do
  let execCore ← Concurrency.currentCoreId
  let result ← Platform.FFI.modifyGetKernelState (fun st =>
    let threadId := SeLe4n.ThreadId.ofNat tid.toNat
    match threadId.toValid? with
    | none =>
        ((Platform.FFI.KernelError.toUInt32 .invalidArgument,
          ([] : List (CoreId × SgiKind))), st)
    | some vtid =>
        match Lifecycle.Suspend.suspendThreadOnCore st vtid execCore with
        | Except.ok (st', _) =>
            (((0 : UInt32),
              PriorityInheritance.computeCrossCoreSgis st st' execCore), st')
        | Except.error e =>
            ((Platform.FFI.KernelError.toUInt32 e, ([] : List (CoreId × SgiKind))), st))
  Concurrency.fireCrossCoreSgis result.2
  pure result.1

end SeLe4n.Kernel
