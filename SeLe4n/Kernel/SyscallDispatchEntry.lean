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
-- WS-SM SM7.C: the catch-up commit drains each target's queue onto its own
-- per-core `perCoreTlb` view (`handleTlbShootdownReqOnCorePerCore`), making
-- the mounted per-core TLB model operative on the live shootdown path.
import SeLe4n.Kernel.Architecture.PerCoreTlbModel
import SeLe4n.Kernel.Architecture.TlbShootdownWait
import SeLe4n.Kernel.Architecture.TlbiForSharing
-- WS-SM SM7.B.12: the RPi5 platform binding — `shootdownSharingDomain`
-- reads `PlatformBinding.sharingDomain` directly, so a multi-cluster
-- port that changes the binding flips the live round's TLBI domain
-- without touching this module.
import SeLe4n.Platform.RPi5.Contract
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
TLBIs are issued in — read **directly from the platform binding**
(`PlatformBinding.sharingDomain`), so the entry follows the platform:
`.inner` on the single-cluster BCM2712 (the test suite `rfl`-pins the
computed value), `.outer` on a multi-cluster port that changes the
binding — and only this changes: the state protocol is
domain-invariant (`Architecture.tlbShootdown_outer_correct`), so every
SM7.B round theorem carries over unchanged. -/
def shootdownSharingDomain : Concurrency.SharingDomain :=
  Platform.PlatformBinding.sharingDomain
    (platform := Platform.RPi5.RPi5Platform)

/-- **WS-SM SM7.B.12**: the RPi5 binding computes `.inner` — the
single-cluster BCM2712 pin, now derived rather than hardcoded. -/
theorem shootdownSharingDomain_rpi5 :
    shootdownSharingDomain = .inner := rfl

/-- **WS-SM SM7.B.7**: the cooperative round-lock acquire's retry
budget.  Covers > 10⁵ round-lengths of retries (a round completes in
< 1 µs on the 4-core BCM2712, plan §3.4) — exhaustion means a
genuinely wedged round holder. -/
def shootdownRoundLockAcquireFuel : Nat := 1000000

/-- **WS-SM SM7.B.7**: the budget literal, pinned. -/
theorem shootdownRoundLockAcquireFuel_value :
    shootdownRoundLockAcquireFuel = 1000000 := rfl

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
            -- Self-service is a LOCAL obligation: clean exactly this
            -- core's view (the Rust handler's `tlbi vmalle1`), then
            -- release-acknowledge.  The in-flight round's initiator
            -- owns the broadcast step — no IS-broadcast here.
            Concurrency.tlbiLocalFullFlush
            Concurrency.shootdownAckSet execCore
          go fuel
  go shootdownRoundLockAcquireFuel

/-- **WS-SM SM7.B (debt (1))**: publish a round's collapsed operand list
into the Rust per-descriptor mailbox under the seqlock discipline —
`begin`, one `slot` per operand (index-addressed), then `commit len`.
Each `TlbInvalidation` is transmitted as its raw
`(toOpTag, toAsid, toVaddr)` encoding, matching the Rust
`decode_tlb_invalidation` decode (SM7.B op-tag conformance).  Called by
the initiator under the round lock, before the SGIs fire. -/
def publishShootdownOps (ops : List Architecture.TlbInvalidation) :
    BaseIO Unit := do
  Concurrency.shootdownPublishBegin
  let mut i : Nat := 0
  for op in ops do
    Concurrency.shootdownPublishSlot i op.toOpTag op.toAsid op.toVaddr
    i := i + 1
  Concurrency.shootdownPublishCommit ops.length

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
1b. **Publish the collapsed operands** into the Rust per-descriptor
   mailbox (`publishShootdownOps`), BEFORE the SGIs — so each target's
   handler retires just this round's operands locally (matching the
   Lean `handleTlbShootdownReqOnCore` per-descriptor effect) instead of
   a blanket `vmalle1`.  The `dsb ish` in `sendSgiToCore` orders the
   publish before any target can take the SGI (SM7.B debt (1)).
2. One `.tlbShootdownReq` SGI per **online** non-initiator core (the
   SM7.A PR #838 P1 target-set obligation).  The full non-initiator
   set is poked — not just `changed` — because the reset dropped every
   online target's flag, and the handler is idempotent
   (`handleTlbShootdownReqOnCore_idempotent`); poking a subset could
   strand a reset flag and hang the wait.
3. The initiator's local broadcast TLBIs — one `tlbiForSharing` per
   posted operand after the `vmalle1`-dominance collapse
   (`collapseShootdownOps`; effect-exact by
   `collapseShootdownOps_effect_eq`); each ends with the `dsb`+`isb`
   bracket.
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
immediately-satisfied wait, and the catch-up commit.

**Model-vs-hardware catch-up fidelity** (PR #839 review P1, tracked
debt — see `docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` §SM7.B review-P1
cut).  The model *posting* (the pending-queue enqueue) rides the
syscall's own atomic `modifyGetKernelState` (`syscallDispatchCrossCoreEntry`),
and this model catch-up rides a *second* atomic step — neither is under
the `SHOOTDOWN_ROUND_LOCK`, which serialises only the **hardware**
round (reset/SGI/wait).  So under concurrent rounds one core's catch-up
fold can drain another core's freshly-posted descriptors, making the
model transiently quiescent before that other round's hardware SGIs
fire.  This is a *model-fidelity* divergence, **not** a hardware
hazard: the hardware TLB maintenance for each round is driven entirely
by that round's own `(pre, post)` diff (`shootdownPostedOps` /
`shootdownChangedTargets`), fires its own SGIs to the online targets,
and blocks on its own `SHOOTDOWN_ACK` channel before the initiating
syscall returns — so no round ever under-invalidates, and cross-round
model over-draining is safe over-application (the model's per-core TLB
effect is idempotent; `handleTlbShootdownReqOnCore_idempotent`).  Model
quiescence gates only capacity/`pendingBounded` bookkeeping, never a
hardware-cleanliness decision.  The faithful fix — round-generation-
tagged descriptors so catch-up drains only its own round — is a
verified-model-type change (`TlbShootdownState` + the SM7.A/B proof
surface + the Rust mirror), scoped as a follow-on. -/
def completeShootdownRounds (changed : List Concurrency.CoreId)
    (ops : List Architecture.TlbInvalidation)
    (execCore : Concurrency.CoreId) : BaseIO Unit := do
  if changed.isEmpty then
    pure ()
  else do
    -- A posted `vmalle1` supersedes every other operand — collapse to
    -- it once (`collapseShootdownOps_effect_eq`: the collapsed list's
    -- TLB effect is exactly the full list's) and reuse for both the
    -- per-descriptor mailbox publish and the initiator's broadcast.
    let collapsed := Architecture.collapseShootdownOps ops
    acquireShootdownRoundLockServicingSelf execCore
    Concurrency.shootdownResetForRound execCore
    -- WS-SM SM7.B (debt (1)): publish the round's exact operands into the
    -- per-descriptor mailbox BEFORE firing the SGIs, so each target's
    -- handler retires just these operands locally (matching the Lean
    -- `handleTlbShootdownReqOnCore` per-descriptor effect) rather than a
    -- blanket `vmalle1`.  The `dsb ish` in `sendSgiToCore` (SM1.F.8)
    -- orders this publish before any target can take the SGI.
    publishShootdownOps collapsed
    -- One CORE_IRQ_READY snapshot per round (the IRQ-serviceable set,
    -- not the CORE_READY release handshake — PR #839 review P1;
    -- bring-up never overlaps a round per the SM7.A P1 contract, so the
    -- snapshot is stable).
    let onlineMask ← Concurrency.shootdownOnlineMask
    for c in Architecture.shootdownTargets execCore do
      if Concurrency.coreOnlineInMask onlineMask c then
        Concurrency.sendSgiToCore c .tlbShootdownReq
    for op in collapsed do
      Architecture.tlbiForSharing shootdownSharingDomain op
    let acked ← Concurrency.shootdownWaitAllAcked
      Architecture.shootdownWaitTimeoutTicks
    Concurrency.shootdownRoundLockRelease
    if !acked then
      panic! "WS-SM SM7.B.6: TLB shootdown round timed out — a target \
        core is hung or deaf; halting fail-closed (a silently skipped \
        invalidation would be the SMP-C4 stale-TLB hazard)"
    -- WS-SM SM7.C: the model catch-up drains each *non-initiator* target's
    -- queue onto its own per-core `perCoreTlb` view
    -- (`handleTlbShootdownReqOnCorePerCore`) AND retires the round's collapsed
    -- operands on the *initiator's* own view (`drainInitiatorPerCoreView`, via
    -- `shootdownCatchUpPerCore`).  The initiator drain is the PR #844 P1 fix:
    -- the `tlbiForSharing` loop above is an inner-shareable broadcast that
    -- reaches the issuing PE too, so the initiator's own per-core view must
    -- retire the operands (`shootdownTargets execCore` explicitly excludes the
    -- initiator).  This makes the mounted per-core TLB model reflect the live
    -- round's real per-descriptor drain on **every** reached core, initiator
    -- included — the operative form of Theorem 3.3.1
    -- (`Architecture.shootdownRoundPerCore_invalidates_perCore`).  It stays
    -- **trace-safe**: the initiator drain is `perCoreTlb`-only (the scalar
    -- `st.tlb` boot-core view was already retired in the dispatch), so the
    -- catch-up's `tlb` / `tlbShootdown` effect is definitionally the SM7.B
    -- single-view target fold's (`shootdownCatchUpPerCore_agrees_singleView`);
    -- only the projection-invisible `perCoreTlb` additionally evolves, so the
    -- golden trace stays byte-identical.  The scalar `st.tlb` remains the
    -- pre-SMP single-view (all-cores-conflated) model; `perCoreTlb` is the
    -- per-core refinement.
    Platform.FFI.modifyGetKernelState (fun st =>
      ((), Architecture.shootdownCatchUpPerCore st execCore collapsed))

/-- **WS-SM SM7.B** (structural marker): a commit that changed no
pending-shootdown queue runs no round — no lock traffic, no reset, no
SGIs, no TLBIs, no wait.  This is the non-shootdown-syscall inertness
of the runtime bracket at the definition level (the state-diff half is
`shootdownChangedTargets_nil_of_eq`); the trace fixture's
byte-identity across the SM7.B landing rests on it. -/
theorem completeShootdownRounds_nil
    (ops : List Architecture.TlbInvalidation)
    (execCore : Concurrency.CoreId) :
    completeShootdownRounds [] ops execCore = pure () := rfl

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
