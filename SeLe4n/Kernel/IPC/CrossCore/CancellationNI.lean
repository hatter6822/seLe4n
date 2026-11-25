-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM6.E cross-core IPC (per-core / ∀-core
-- non-interference for the cancellation path; see
-- WS-SM SM6).

import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallNiPerCore
import SeLe4n.Kernel.InformationFlow.Invariant.Composition
-- WS-RR RR8.8/RR8.9: the reply-arm shape facts the two discharges consume
-- (`cancelledCallerDonation?_holder_holds_victim_donation`).
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationReplyShape
-- WS-SX SX24: the endpoint-queue link labels the queue arms' teardown reads
-- (`endpointQueueLabelsAgree.spliceOutMidQueueNode`).
import SeLe4n.Kernel.QueueLabels.Cancellation

/-!
# WS-SM SM6.E — Cross-core cancellation non-interference

The information-flow slice of SM6.E: cancelling a **non-observable** victim is
invisible to a low observer.

The SM6.E-*new* state effects over the single-core suspend pipeline are all
discharged **substantively** here:

* the **placement deschedule** (`descheduleThread`, the `removeRunnableOnCore`
  of a high victim on the core the state places it on — WS-RR RR8.6) — §2;
* the **∀-core replenish-queue frames** (`setReplenishQueueOnCore` at *any*
  core is projection-invisible — the exact purge of the per-core bound arm, on
  the core its own link names, reduces to exactly this) — §1;
* the **replenishment migration** (`migrateSchedContextReplenishment`, the
  §2b donated-arm addition) — §1;
* the **composite** `cancelIpcBlockingOnCore` for a `.ready` victim (the
  suspend-of-a-running-thread scenario — the cross-core-relevant case, since
  a blocked victim is neither queued nor current on any core) — §3.

The single-core object-level teardown (`cancelIpcBlocking`) is discharged on
every arm (§5 the reply arm, §5b the queue arms, WS-SX SX24) from the labels
every kernel entry carries (`endpointQueueLabelsAgree`,
`notificationLabelsAgree`), so the composites (§5b's close) take no teardown
hypothesis.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)
open SeLe4n.Kernel.Lifecycle.Suspend

-- ============================================================================
-- §1  ∀-core scheduler-internal frames (replenish queues are unobservable)
-- ============================================================================
-- The boot-core `projectState` frame for the replenishment migration is
-- production (`migrateSchedContextReplenishment_preserves_projection`,
-- SM5.H.4 NI in `InformationFlow.Invariant.Operations`); the per-core
-- (`projectStateOnCore`) forms and the single-write ∀-core purge frame are
-- new here — no per-core observable reads any replenish queue.

/-- WS-SM SM6.E: writing *any* core's replenish queue preserves the low
observer's projection — the ∀-core generalisation of the bootCore-pinned
AK6-F.2a frame, covering the per-core bound arm's exact purge on whichever core
its own link names. -/
theorem setReplenishQueueOnCore_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (c : CoreId) (rq : ReplenishQueue) :
    projectState ctx observer
      { st with scheduler := st.scheduler.setReplenishQueueOnCore c rq } =
    projectState ctx observer st := by
  simp only [projectState, projectRunnable, projectCurrent, projectActiveDomain,
    projectDomainTimeRemaining, projectDomainScheduleIndex, projectMachineRegs,
    SchedulerState.runnable,
    SchedulerState.setReplenishQueueOnCore_runQueueOnCore,
    SchedulerState.setReplenishQueueOnCore_currentOnCore,
    SchedulerState.setReplenishQueueOnCore_activeDomainOnCore,
    SchedulerState.setReplenishQueueOnCore_domainTimeRemainingOnCore,
    SchedulerState.setReplenishQueueOnCore_domainScheduleIndexOnCore]
  congr 1

/-- WS-SM SM6.E: the per-core projection is likewise insensitive to *any*
core's replenish queue — no per-core observable reads it. -/
theorem setReplenishQueueOnCore_preserves_projectionOnCore
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (c : CoreId) (rq : ReplenishQueue) (cObs : CoreId) :
    projectStateOnCore ctx observer
      { st with scheduler := st.scheduler.setReplenishQueueOnCore c rq } cObs =
    projectStateOnCore ctx observer st cObs :=
  projectStateOnCore_congr ctx observer
    (setReplenishQueueOnCore_preserves_projection ctx observer st c rq)
    (SchedulerState.setReplenishQueueOnCore_runQueueOnCore st.scheduler c cObs rq)
    (SchedulerState.setReplenishQueueOnCore_currentOnCore st.scheduler c cObs rq)
    (SchedulerState.setReplenishQueueOnCore_activeDomainOnCore st.scheduler c cObs rq)
    (SchedulerState.setReplenishQueueOnCore_domainTimeRemainingOnCore
      st.scheduler c cObs rq)
    (SchedulerState.setReplenishQueueOnCore_domainScheduleIndexOnCore
      st.scheduler c cObs rq)
    rfl

/-- WS-ZA ZA6.33: the settle of a non-observable returned context preserves
the per-core projection. -/
theorem settleReturnedContext_preserves_projectionOnCore
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (d : CoreId) (scId : SeLe4n.SchedContextId) (c : CoreId)
    (hS : objectObservable ctx observer scId.toObjId = false) :
    projectStateOnCore ctx observer (SchedContextOps.settleReturnedContext st d scId) c =
    projectStateOnCore ctx observer st c := by
  refine projectStateOnCore_congr ctx observer
    (settleReturnedContext_preserves_projection ctx observer st d scId hS)
    ?_ ?_ ?_ ?_ ?_ ?_ <;>
    first
      | rw [SchedContextOps.settleReturnedContext_machine]
      | (rw [(SchedContextOps.settleReturnedContext_releaseOnlyWrite st d scId).2]; rfl)

-- ============================================================================
-- §2  The placement deschedule of a high victim is invisible
-- ============================================================================

/-- WS-RR RR8.6: removing a **non-observable** thread from wherever the state
places it is invisible to a low observer — at a resolved core it is the
`removeRunnableOnCore` invisibility, and at no core the step is the identity. -/
theorem descheduleAtPlacement_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (victim : SeLe4n.ThreadId)
    (hVictimHigh : threadObservable ctx observer victim = false) :
    projectState ctx observer (descheduleAtPlacement st victim)
      = projectState ctx observer st := by
  unfold descheduleAtPlacement descheduleAt
  split
  · exact removeRunnableOnCore_preserves_projection ctx observer st victim _ hVictimHigh
  · rfl

/-- WS-RR RR8.6: ...and on every core. -/
theorem descheduleAtPlacement_preserves_projectionOnCore
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (victim : SeLe4n.ThreadId) (c : CoreId)
    (hVictimHigh : threadObservable ctx observer victim = false) :
    projectStateOnCore ctx observer (descheduleAtPlacement st victim) c
      = projectStateOnCore ctx observer st c := by
  unfold descheduleAtPlacement descheduleAt
  split
  · exact removeRunnableOnCore_preserves_projectionOnCore ctx observer st victim _ c
      hVictimHigh
  · rfl

/-- WS-SM SM6.E (boot-core form): descheduling a **non-observable** victim
from the core the state places it on is invisible to a low observer — the
wakeThread-dual of the SM6.A wake-invisibility. -/
theorem descheduleThread_cancellation_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (victim : SeLe4n.ThreadId) (executingCore : CoreId)
    (hVictimHigh : threadObservable ctx observer victim = false) :
    projectState ctx observer (descheduleThread st victim executingCore).1
      = projectState ctx observer st := by
  rw [descheduleThread_state_eq]
  exact descheduleAtPlacement_preserves_projection ctx observer st victim hVictimHigh

/-- WS-SM SM6.E (∀-core form): descheduling a high victim is invisible on
*every* core — including the victim's placed core, whose run-queue/current
edits touch only a thread the observer filters out. -/
theorem descheduleThread_cancellation_NI_smp
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (victim : SeLe4n.ThreadId) (executingCore : CoreId)
    (hVictimHigh : threadObservable ctx observer victim = false) :
    lowEquivalent_smp ctx observer
      (descheduleThread st victim executingCore).1 st := by
  intro c
  show projectStateOnCore ctx observer
      (descheduleThread st victim executingCore).1 c
    = projectStateOnCore ctx observer st c
  rw [descheduleThread_state_eq]
  exact descheduleAtPlacement_preserves_projectionOnCore ctx observer st victim c
    hVictimHigh

-- ============================================================================
-- §3  The cancellation composite
-- ============================================================================

/-- WS-ZA ZA6.30: the labelling obligation of the reply arm's replenishment
migration — the context the cancellation returns is non-observable.  The
projection keeps each context's release core and release time
(`releaseQueuedOn_eq_of_projectObjects`), so moving an observable context's
release entry between cores is a visible write; the migration is invisible
exactly when the migrated context is hidden.  Quantified over the resolution,
as `descheduledHolderHigh` is, and discharged outright where none is resolved
(`cancelledDonationContextHigh_of_no_donation`). -/
def cancelledDonationContextHigh (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB) : Prop :=
  ∀ scId holder,
    Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = some (scId, holder) →
      objectObservable ctx observer scId.toObjId = false

/-- With no donation resolved nothing migrates, so the obligation is vacuous. -/
theorem cancelledDonationContextHigh_of_no_donation (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = none) :
    cancelledDonationContextHigh ctx observer st victim tcb := by
  intro scId holder hW
  rw [h] at hW
  exact absurd hW (by simp)

/-- **WS-RR RR7.22 (residual, remediation)**: the SM5.H replenishment migration
the corrected reply arm obliges is invisible when the returned context is
non-observable (`cancelledDonationContextHigh`). -/
theorem cancelIpcBlockingMigrated_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState)
    (hCtxHigh : cancelledDonationContextHigh ctx observer st victim tcb) :
    projectState ctx observer (cancelIpcBlockingMigrated victim tcb st)
      = projectState ctx observer (cancelIpcBlocking st victim tcb) := by
  rcases cancelIpcBlockingMigrated_cases victim tcb st with h | ⟨scId, holder, hRes, _, h⟩ <;> rw [h]
  exact settleReturnedContext_preserves_projection ctx observer _ _ scId
    (hCtxHigh scId holder hRes)

/-- The per-core form of the same. -/
theorem cancelIpcBlockingMigrated_preserves_projectionOnCore
    (ctx : LabelingContext) (observer : IfObserver)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState) (c : CoreId)
    (hCtxHigh : cancelledDonationContextHigh ctx observer st victim tcb) :
    projectStateOnCore ctx observer (cancelIpcBlockingMigrated victim tcb st) c
      = projectStateOnCore ctx observer (cancelIpcBlocking st victim tcb) c := by
  rcases cancelIpcBlockingMigrated_cases victim tcb st with h | ⟨scId, holder, hRes, _, h⟩ <;> rw [h]
  exact settleReturnedContext_preserves_projectionOnCore ctx observer _ _ scId c
    (hCtxHigh scId holder hRes)

-- ============================================================================
-- §4b  `v0.35.158` — the reclaim's holder deschedule (WS-OD OD1.7's wake until then)
-- ============================================================================

-- `v0.35.158`: `enqueueAbortedHolderOnCore_projectRunnableOnCore_high`,
-- `enqueueAbortedHolderOnCore_preserves_projection` and
-- `enqueueAbortedHolderOnCore_preserves_projectionOnCore` — the invisibility of
-- WS-OD OD1.7's guarded run-queue insert — are retired with the insert.  The
-- reclaim's scheduler step is `descheduleAtPlacement` now, whose invisibility
-- the module already states (§3, `descheduleAtPlacement_preserves_projection`).

/-- **`v0.35.158`**: the information-flow obligation the reclaim's holder
*deschedule* carries (`abortHolderWakeHigh` until this cut, for the wake it
replaced).

The deschedule acts on the **holder**, whose label the victim's does not
determine.  A run-queue removal is filtered by the removed thread's own observability
(`projectRunnable`; `removeRunnableOnCore_preserves_projection`), so the
deschedule is invisible exactly when the holder is non-observable — which is the
condition the wake carried, unchanged, because an insert and a removal are
filtered by the same thread.

Stated as the policy fact rather than as a projection equality, because that is
what a deployment can actually establish: a server holding a high caller's
donated SchedContext is reachable from that caller, so a labeling that admits
the `Call` in the first place labels the server at least as high.

**WS-RR RR8.9 — DISCHARGED** (`v0.35.84` for the wake, carried over):
`descheduledHolderHigh_of_donationOwnerFlowsToHolder` proves this outright from
`donationOwnerFlowsToHolder`, the state form of exactly that fact
(`label victim ⊑ label endpoint` from the donating `Call`'s gate,
`label endpoint ⊑ label holder` from the server's own receive gate, composed by
`securityFlowsTo_trans`).  It needs **nothing** about queues: the obligation is
a single `threadObservable` of the holder.  Kept as a definition because the
*consumers* take it as a hypothesis — the discharge is what a caller applies to
get it.

Discharged outright wherever no donation is resolved
(`descheduledHolderHigh_of_no_donation`), which is every arm but a reply arm
whose caller had donated. -/
def descheduledHolderHigh (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB) : Prop :=
  ∀ holder : SeLe4n.ThreadId,
    cancelUnboundHolder? st (cancelIpcBlockingMigrated victim tcb st) victim tcb = some holder →
      threadObservable ctx observer holder = false

/-- `v0.35.158`: with no donation resolved the deschedule never fires, so the
obligation is vacuous — the step adds an obligation exactly where it adds a
write, and nowhere else. -/
theorem descheduledHolderHigh_of_no_donation (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = none) :
    descheduledHolderHigh ctx observer st victim tcb := by
  intro holder hW
  rw [show cancelUnboundHolder? st (cancelIpcBlockingMigrated victim tcb st) victim tcb = none by
    unfold cancelUnboundHolder?; rw [h]] at hW
  exact absurd hW (by simp)

/-- `v0.35.158`: under that obligation the deschedule preserves the projection. -/
theorem descheduleUnboundHolder_preserves_projection (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (hHigh : descheduledHolderHigh ctx observer st victim tcb) :
    projectState ctx observer
        (descheduleUnboundHolder st (cancelIpcBlockingMigrated victim tcb st) victim tcb)
      = projectState ctx observer (cancelIpcBlockingMigrated victim tcb st) := by
  unfold descheduleUnboundHolder
  split
  · rfl
  · rename_i holder hW
    exact descheduleAtPlacement_preserves_projection ctx observer _ holder (hHigh holder hW)

/-- `v0.35.158`: ...and the per-core projection on every core. -/
theorem descheduleUnboundHolder_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (c : CoreId) (hHigh : descheduledHolderHigh ctx observer st victim tcb) :
    projectStateOnCore ctx observer
        (descheduleUnboundHolder st (cancelIpcBlockingMigrated victim tcb st) victim tcb) c
      = projectStateOnCore ctx observer (cancelIpcBlockingMigrated victim tcb st) c := by
  unfold descheduleUnboundHolder
  split
  · rfl
  · rename_i holder hW
    exact descheduleAtPlacement_preserves_projectionOnCore ctx observer _ holder c
      (hHigh holder hW)

/-- WS-SM SM6.E (boot-core form, fully substantive): cancelling a `.ready`
high victim — the suspend-of-a-running-thread scenario, the cross-core-
relevant case — is invisible: the teardown is the identity, so the whole
composite is the (invisible) placement deschedule. -/
theorem cancelIpcBlockingOnCore_ready_cancellation_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hReady : tcb.ipcState = .ready)
    (hVictimHigh : threadObservable ctx observer victim = false) :
    projectState ctx observer
        (cancelIpcBlockingOnCore victim tcb executingCore st).1
      = projectState ctx observer st := by
  rw [cancelIpcBlockingOnCore_ready_eq_descheduleThread victim tcb executingCore st
        hReady]
  exact descheduleThread_cancellation_NI ctx observer st victim executingCore
    hVictimHigh

/-- WS-SM SM6.E (∀-core form, fully substantive): cancelling a `.ready` high
victim is invisible on *every* core. -/
theorem cancelIpcBlockingOnCore_ready_cancellation_NI_smp
    (ctx : LabelingContext) (observer : IfObserver)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hReady : tcb.ipcState = .ready)
    (hVictimHigh : threadObservable ctx observer victim = false) :
    lowEquivalent_smp ctx observer
      (cancelIpcBlockingOnCore victim tcb executingCore st).1 st := by
  intro c
  show projectStateOnCore ctx observer
      (cancelIpcBlockingOnCore victim tcb executingCore st).1 c
    = projectStateOnCore ctx observer st c
  rw [cancelIpcBlockingOnCore_ready_eq_descheduleThread victim tcb executingCore st
        hReady,
      descheduleThread_state_eq]
  exact descheduleAtPlacement_preserves_projectionOnCore ctx observer st victim c
    hVictimHigh

-- ============================================================================
-- §5  WS-RR RR2.18 — discharging the teardown projection on the reply arm
-- ============================================================================
-- The cancellation's own teardown projection is proved arm by arm: here the
-- `.blockedOnReply` teardown — the arm the live `.tcbSuspend` of a caller
-- awaiting a reply takes — from the writes that arm actually makes, each
-- invisible for its own reason (the queue arms are §5b):
--
--   * the victim's `ipcState` / queue-link reset (`restoreToReady`) and its
--     `replyObject` clear land on the victim's own TCB, which
--     `LabelingContextValid` makes unobservable when the victim is;
--   * the Reply's `caller` back-link clear is invisible **unconditionally** —
--     `projectKernelObject` strips `caller`, so it does not even need the Reply
--     object to be high.
--
-- Since WS-RR RR8.5 the last two are one step — `consumeReplyLink` is the reply
-- path's own `consumeCallerReply`, read through `consumeCallerReplyLink` — so
-- their invisibility is that path's theorem (`consumeCallerReply_preserves_projection`)
-- reached through the bridge, not a second argument over raw inserts.

-- WS-RR RR8.10: `restoreToReadyStaging_preserves_objects_invExt` is **deleted**.
-- It was a byte-for-byte duplicate of the production
-- `Lifecycle.Suspend.restoreToReadyStaging_invExt`
-- (`Lifecycle/Invariant/SuspendPreservation.lean`) -- same statement, same
-- proof -- declared here in a *staged* module, so production code that needed
-- the fact could not reach this copy and the tree carried two answers to one
-- question with only one of them importable.  Found while RR8.10's production
-- composite reached for it; the two spellings below now read the production one.
theorem restoreToReady_preserves_objects_invExt (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (Lifecycle.Suspend.restoreToReady st tid).objects.invExt :=
  Lifecycle.Suspend.restoreToReadyStaging_invExt st tid false hInv

/-- **WS-RR RR7.14**: the cancellation spelling. -/
theorem restoreToReadyCancelled_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (Lifecycle.Suspend.restoreToReadyCancelled st tid).objects.invExt :=
  Lifecycle.Suspend.restoreToReadyStaging_invExt st tid _ hInv

/-- WS-RR RR2.18: `restoreToReady` at a high thread is invisible.

**WS-RR RR7.14 (load-bearing)**: stated over `restoreToReadyStaging`, so the
restart (WS-SX SX4) is covered by the same argument — its program counter and
state are written *into the victim's own TCB*, the one object the premise
already has as high, so an observer that cannot see the thread cannot see its
restart either.  Had the write gone anywhere else (the machine register banks,
say) this would not hold. -/
theorem restoreToReadyStaging_preserves_projection_high
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId) (restart : Bool)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (Lifecycle.Suspend.restoreToReadyStaging st tid restart)
      = projectState ctx observer st := by
  unfold Lifecycle.Suspend.restoreToReadyStaging SystemState.updateTcb
  split
  · exact objects_insert_preserves_projection_high ctx observer st tid.toObjId _
      hTidObjHigh hObjInv
  · rfl

theorem restoreToReady_preserves_projection_high
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (Lifecycle.Suspend.restoreToReady st tid)
      = projectState ctx observer st :=
  restoreToReadyStaging_preserves_projection_high ctx observer st tid false
    hTidObjHigh hObjInv

/-- **WS-RR RR7.14**: the cancellation spelling — the restart (WS-SX SX4) is
invisible to an observer who cannot see the cancelled thread. -/
theorem restoreToReadyCancelled_preserves_projection_high
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (Lifecycle.Suspend.restoreToReadyCancelled st tid)
      = projectState ctx observer st :=
  restoreToReadyStaging_preserves_projection_high ctx observer st tid _
    hTidObjHigh hObjInv

/-- WS-RR RR2.18: the whole reply-link consume is invisible for a high victim.

**WS-RR RR8.5**: derived from the reply path's own
`consumeCallerReply_preserves_projection` through the bridge, so the argument is
made once — the `.reply` `caller := none` write is projection-stripped and the
caller-TCB `replyObject := none` write lands on a high TCB.  It reads the index
completeness that theorem asks for the (already-present) Reply's membership,
which the composite below carries through the writes ahead of the teardown. -/
theorem consumeReplyLink_preserves_projection_high
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (Lifecycle.Suspend.consumeReplyLink st tid tcb)
      = projectState ctx observer st := by
  unfold Lifecycle.Suspend.consumeReplyLink
  cases tcb.replyObject with
  | none => rfl
  | some rid =>
    exact consumeCallerReply_preserves_projection ctx observer st _ tid rid hTidObjHigh
      hObjInv (SystemState.consumeCallerReply_eq_link st tid rid)

/-- The cancelled caller's donation return is invisible when the returned context
is hidden.

WS-SX SX9.1 (D34) supersedes WS-RR RR7.22's unconditional form: the projection
shows a binding word to an observer cleared for the context it names, so the
return is invisible exactly where that context is hidden
(`cancelledDonationContextHigh`, the obligation the cancel's migration already
carries), and the holder's word it clears names that context
(`replyFrameHeadHolderDonation`, the reply head's coherence the reclaim's
trigger reads).  The other hypotheses are structural: the identity registry is
complete and well-formed, so `storeObject` extends neither. -/
theorem returnDonationToCancelledCaller_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB)
    (hObjInv : st.objects.invExt)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hCtxHigh : cancelledDonationContextHigh ctx observer st victim tcb)
    (hOwed : ∀ rid, tcb.replyObject = some rid → replyFrameHeadHolderDonation st rid victim) :
    projectState ctx observer (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb)
      = projectState ctx observer st := by
  refine Lifecycle.Suspend.returnDonationToCancelledCaller_elim
    (P := fun s => projectState ctx observer s = projectState ctx observer st) rfl ?_
  intro scId holder s hRes hPop
  have hS := hCtxHigh scId holder hRes
  apply popHeldReplyHead_liftPops hPop
  · -- WS-SX SX9.1 (D34): the returned context is hidden (the migration's own
    -- obligation), and the holder's binding word names it (the reply head's
    -- coherence, `replyFrameHeadHolderDonation`).
    intro n s' hRet
    refine returnDonatedSchedContext_preserves_projection ctx observer st s' holder scId victim
      hObjInv n hRet hIdxComplete hObjSetInv (.inr fun t hT => ?_) (.inl hS)
    have hR := cancelledCallerDonation?_holder_holds_victim_donation st victim tcb scId holder
      hOwed hRes
    unfold replyDonationReturn? at hR
    split at hR
    · rename_i ht hL
      split at hR
      · rename_i s0 o0 hB
        cases hR
        rw [lookupTcb_some_objects st holder ht hL] at hT
        cases hT
        rw [TCB.scBindingScCode_of_donated hB]
        simpa using hS
      all_goals cases hR
    · cases hR
  · intro n _ hK
    exact keepDonatedSchedContext_preserves_projection ctx observer _ _ holder scId n hObjInv
      hK hIdxComplete hObjSetInv (.inr hS)

/-- `v0.35.4`, restated for the splice at **WS-HP HP6.4**: the cancelled caller's
frame removal preserves the projection — the identity where there is nothing to
remove, one `cutReplyFrameOut` otherwise.

The splice writes the frame *below* the cut at the intermediate state, so the index
set's well-formedness has to reach that state; `hSetInv` is what carries it, and it
is the one hypothesis this gained when the sever became a splice. -/
theorem cutThreadReplyFrameOut_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) (tcb : TCB)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st)
    (hSetInv : st.objectIndexSet.table.invExt)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (cutThreadReplyFrameOut st tcb)
      = projectState ctx observer st := by
  rcases cutThreadReplyFrameOut_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]
  · exact cutReplyFrameOut_preserves_projection ctx observer hIdxComplete hSetInv hObjInv h

/-- **WS-RR RR2.18: the teardown projection, discharged on the reply arm.**

For a victim blocked awaiting a reply, `cancelIpcBlocking`'s writes are the
victim's own TCB (twice), the Reply's `caller` back-link, and the donation
return — the first two invisible because the victim is high, the third invisible
outright, the fourth invisible because the projection erases the binding fields
it writes.  The reply arm of `cancelIpcBlocking_preserves_projection_high` (§5b).

**WS-RR RR8.5**: the second and third of those writes are the reply path's own
`consumeCallerReply` now, so their invisibility is
`consumeCallerReply_preserves_projection` through the bridge; what the composite
adds is the index completeness that theorem reads, carried from the return
through the splice and the restore. -/
theorem cancelIpcBlocking_blockedOnReply_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (ep : SeLe4n.ObjId)
    (rt : Option SeLe4n.ThreadId)
    (hBlocked : tcb.ipcState = .blockedOnReply ep rt)
    (hValid : LabelingContextValid ctx)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hObjInv : st.objects.invExt)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hCtxHigh : cancelledDonationContextHigh ctx observer st victim tcb)
    (hOwed : ∀ rid, tcb.replyObject = some rid → replyFrameHeadHolderDonation st rid victim) :
    projectState ctx observer (Lifecycle.Suspend.cancelIpcBlocking st victim tcb)
      = projectState ctx observer st := by
  have hObjHigh : objectObservable ctx observer victim.toObjId = false :=
    hValid.coherenceImpliesObjectHigh observer victim hVictimHigh
  unfold Lifecycle.Suspend.cancelIpcBlocking
  rw [hBlocked]
  simp only []
  -- The arm's fourth write is the donation return, invisible when the
  -- returned context is hidden (D34 shows the binding words where their
  -- context is): `hCtxHigh` and `hOwed`.
  have hInvR : (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb).objects.invExt :=
    returnDonationToCancelledCaller_preserves_objects_invExt st victim tcb hObjInv
  -- `v0.35.4`: the arm's fifth write is the frame cut, invisible to every
  -- observer — it writes Reply stack links only, which the projection strips.  It reads the index completeness the return
  -- carries forward.
  have hCompR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objectIndexSetComplete
    st victim tcb hObjInv hObjSetInv hIdxComplete
  have hSetInvR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objectIndexSet_invExt
    st victim tcb hObjSetInv
  have hInvD : (cutThreadReplyFrameOut
      (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb) tcb).objects.invExt :=
    cutThreadReplyFrameOut_preserves_objects_invExt _ tcb hInvR
  -- WS-RR RR8.5: the teardown is the reply path's consume, whose projection
  -- theorem reads the index completeness of the state it runs on — carried
  -- here through the splice and the restore, neither of which touches the index.
  have h1 : projectState ctx observer
      (Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled
          (cutThreadReplyFrameOut
            (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb) tcb) victim)
        victim tcb)
      = projectState ctx observer
        (Lifecycle.Suspend.restoreToReadyCancelled
          (cutThreadReplyFrameOut
            (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb) tcb) victim) :=
    consumeReplyLink_preserves_projection_high ctx observer _ victim tcb hObjHigh
      (restoreToReadyCancelled_preserves_objects_invExt _ victim hInvD)
  -- WS-ZA ZA4.6: the arm's last write unlinks the victim from its server's
  -- reply-waiter queue, which the projection erases.
  refine (unlinkReplyWaiterOpt_preserves_projection ctx observer _ victim _).trans ?_
  exact h1.trans
    ((restoreToReadyCancelled_preserves_projection_high ctx observer _ victim hObjHigh
      hInvD).trans
      ((cutThreadReplyFrameOut_preserves_projection ctx observer _ tcb hCompR hSetInvR
        hInvR).trans
        (returnDonationToCancelledCaller_preserves_projection ctx observer st victim tcb hObjInv
          hIdxComplete hObjSetInv hCtxHigh hOwed)))


-- ============================================================================
-- §5b  WS-SX SX24 — the queue arms' teardown projection, discharged
-- ============================================================================
-- The three endpoint arms and the notification arm take the victim off the
-- queue it waits in: they rewrite that queue's endpoint or notification and
-- splice the victim's two neighbours.  Each write is at an object the observer
-- cannot see, read off labels the kernel entries carry (D46, D47):
--
--   * the endpoint's: the rewrite runs only when an end of one of its queues
--     names the victim, and an end carries the endpoint's label
--     (`endpointQueueLabelsAgree`), so the victim's label is the endpoint's and
--     `endpointObjectHigh_of_admittedThreadHigh` hides the object;
--   * the endpoint-queue neighbours': each link of the victim's names a thread
--     of its label (`endpointQueueLabelsAgree`);
--   * the notification's: the victim, blocked on it, is one its gate admits
--     (`notificationLabelsAgree`), so `notificationObjectHigh_of_admittedThreadHigh`
--     hides it;
--   * the notification-queue neighbours': each of the victim's notification
--     links names a thread of its label (`notificationLabelsAgree`);
--   * the victim's own TCB: hidden with the victim (`LabelingContextValid`).

/-- A thread of a hidden thread's label has a hidden TCB. -/
theorem objectHigh_of_threadLabel_eq {ctx : LabelingContext} {observer : IfObserver}
    (hValid : LabelingContextValid ctx) {victim u : SeLe4n.ThreadId}
    (hVictimHigh : threadObservable ctx observer victim = false)
    (h : ctx.threadLabelOf u = ctx.threadLabelOf victim) :
    objectObservable ctx observer u.toObjId = false :=
  hValid.coherenceImpliesObjectHigh observer u (by
    unfold threadObservable at hVictimHigh ⊢; rw [h]; exact hVictimHigh)

/-- **A thread rewritten at a hidden TCB** is invisible. -/
theorem updateTcb_preserves_projection_high (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hHigh : objectObservable ctx observer t.toObjId = false) (hObjInv : st.objects.invExt) :
    projectState ctx observer (st.updateTcb t f) = projectState ctx observer st := by
  unfold SystemState.updateTcb
  split
  · exact objects_insert_preserves_projection_high ctx observer st t.toObjId _ hHigh hObjInv
  · rfl

/-- **The mid-queue splice of a hidden thread** is invisible: both neighbours
it patches carry the thread's label. -/
theorem spliceOutMidQueueNode_preserves_projection_high (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (victim : SeLe4n.ThreadId)
    (hValid : LabelingContextValid ctx)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hQ : endpointQueueLabelsAgree ctx st) (hObjInv : st.objects.invExt) :
    projectState ctx observer (spliceOutMidQueueNode st victim)
      = projectState ctx observer st := by
  rw [spliceOutMidQueueNode_eq_patches]
  split
  · rfl
  · rename_i tcb hL
    obtain ⟨hP, hN⟩ := endpointQueueLabelsAgree.links hQ (lookupTcb_some_objects st victim tcb hL)
    rw [queueNeighbourPatch_preserves_projection_high ctx observer st _ tcb.queueNext
      (queueUnlinkSuccessor tcb) (fun n hn => objectHigh_of_threadLabel_eq hValid hVictimHigh
        (hN n hn)) (queueNeighbourPatch_invExt _ _ _ hObjInv)]
    exact queueNeighbourPatch_preserves_projection_high ctx observer st st.objects tcb.queuePrev
      (queueUnlinkPredecessor tcb)
      (fun p hp => objectHigh_of_threadLabel_eq hValid hVictimHigh (hP p hp)) hObjInv

/-- **The targeted dequeue of a hidden thread** (`removeFromBlockingEndpoint`) is
invisible: the splice, and an endpoint rewritten only when an end names the
thread, so it carries the thread's label. -/
theorem removeFromBlockingEndpoint_preserves_projection_high (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (victim : SeLe4n.ThreadId) (e : SeLe4n.ObjId)
    (hValid : LabelingContextValid ctx)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hQ : endpointQueueLabelsAgree ctx st) (hObjInv : st.objects.invExt) :
    projectState ctx observer (removeFromBlockingEndpoint st victim e)
      = projectState ctx observer st := by
  have hS := spliceOutMidQueueNode_preserves_projection_high ctx observer st victim hValid
    hVictimHigh hQ hObjInv
  have hI := spliceOutMidQueueNode_preserves_objects_invExt st victim hObjInv
  have hQS := endpointQueueLabelsAgree.spliceOutMidQueueNode victim hObjInv hQ
  unfold removeFromBlockingEndpoint
  dsimp only
  split
  · rename_i ep hEp hW
    split
    · rename_i hG
      obtain ⟨hSnd, hRcv⟩ := endpointQueueLabelsAgree.ends hQS
        ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp)
      have hLab : ctx.threadLabelOf victim = ctx.endpointLabelOf e := by
        simp only [Bool.or_eq_true, beq_iff_eq] at hG
        rcases hG with ((h | h) | h) | h
        · exact hSnd.1 _ h
        · exact hSnd.2 _ h
        · exact hRcv.1 _ h
        · exact hRcv.2 _ h
      have hEHigh := endpointObjectHigh_of_admittedThreadHigh ctx observer e victim hValid
        (by rw [hLab]; exact securityFlowsTo_refl _) hVictimHigh
      exact (objects_insert_preserves_projection_high ctx observer _ e _ hEHigh hI).trans hS
    · exact hS
  · exact hS

/-- **The notification-queue neighbours unlinked**, each a hidden thread, is
invisible. -/
theorem unlinkNtfnNeighbours_preserves_projection_high (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (prev next : Option SeLe4n.ThreadId)
    (hP : ∀ p, prev = some p → objectObservable ctx observer p.toObjId = false)
    (hN : ∀ n, next = some n → objectObservable ctx observer n.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (unlinkNtfnNeighbours st prev next)
      = projectState ctx observer st := by
  unfold unlinkNtfnNeighbours
  cases prev with
  | none =>
    cases next with
    | none => rfl
    | some n => exact updateTcb_preserves_projection_high ctx observer _ n _ (hN n rfl) hObjInv
  | some p =>
    cases next with
    | none => exact updateTcb_preserves_projection_high ctx observer _ p _ (hP p rfl) hObjInv
    | some n =>
      exact (updateTcb_preserves_projection_high ctx observer _ n _ (hN n rfl)
        (SystemState.updateTcb_preserves_objects_invExt _ _ _ hObjInv)).trans
        (updateTcb_preserves_projection_high ctx observer _ p _ (hP p rfl) hObjInv)

/-- **A hidden thread taken out of its notification queue** is invisible: the
notification it waited on admitted it, and its two neighbours carry its label. -/
theorem removeFromNotificationWaitQueue_preserves_projection_high (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (victim : SeLe4n.ThreadId)
    (hValid : LabelingContextValid ctx)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hN : notificationLabelsAgree ctx st) (hObjInv : st.objects.invExt) :
    projectState ctx observer (removeFromNotificationWaitQueue st victim)
      = projectState ctx observer st := by
  have hObjHigh := hValid.coherenceImpliesObjectHigh observer victim hVictimHigh
  unfold removeFromNotificationWaitQueue
  split
  · rename_i tcb hT
    split
    · rename_i oid hI
      split
      · rename_i notif hNt hW
        dsimp only
        obtain ⟨hSelf, hP, hNx⟩ := hN _ _ ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)
        have hOHigh := notificationObjectHigh_of_admittedThreadHigh ctx observer oid victim
          (hSelf oid hI) hVictimHigh
        refine (unlinkNtfnNeighbours_preserves_projection_high ctx observer _ _ _
          (fun p hp => ?_) (fun n hn => objectHigh_of_threadLabel_eq hValid hVictimHigh (hNx n hn))
          (SystemState.updateTcb_preserves_objects_invExt _ _ _
            (RHTable_insert_preserves_invExt _ _ _ hObjInv))).trans
          ((updateTcb_preserves_projection_high ctx observer _ victim _ hObjHigh
            (RHTable_insert_preserves_invExt _ _ _ hObjInv)).trans
            (objects_insert_preserves_projection_high ctx observer st oid _ hOHigh hObjInv))
        split at hp
        · cases hp
        · exact objectHigh_of_threadLabel_eq hValid hVictimHigh (hP p hp)
      · rfl
    · rfl
  · rfl

/-- **WS-SX SX24 (D47): the IPC teardown of a hidden victim is invisible**, on
every arm, from the labels every kernel entry carries — no teardown-projection
hypothesis.  The `.ready` arm writes nothing; the three endpoint arms and the
notification arm are the queue removals above, then the victim's own restore;
the `.blockedOnReply` arm is `cancelIpcBlocking_blockedOnReply_preserves_projection`,
whose obligations (`hCtxHigh`, the index facts, `hOwed`) it alone reads. -/
theorem cancelIpcBlocking_preserves_projection_high (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (hValid : LabelingContextValid ctx)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hObjInv : st.objects.invExt)
    (hQ : endpointQueueLabelsAgree ctx st) (hN : notificationLabelsAgree ctx st)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hCtxHigh : cancelledDonationContextHigh ctx observer st victim tcb)
    (hOwed : ∀ ep rt, tcb.ipcState = .blockedOnReply ep rt →
      ∀ rid, tcb.replyObject = some rid → replyFrameHeadHolderDonation st rid victim) :
    projectState ctx observer (Lifecycle.Suspend.cancelIpcBlocking st victim tcb)
      = projectState ctx observer st := by
  have hObjHigh := hValid.coherenceImpliesObjectHigh observer victim hVictimHigh
  cases hB : tcb.ipcState with
  | ready => unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
  | blockedOnSend e | blockedOnReceive e | blockedOnCall e =>
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    exact (restoreToReadyCancelled_preserves_projection_high ctx observer _ victim hObjHigh
      (removeFromBlockingEndpoint_preserves_objects_invExt st victim e hObjInv)).trans
      (removeFromBlockingEndpoint_preserves_projection_high ctx observer st victim e hValid
        hVictimHigh hQ hObjInv)
  | blockedOnReply ep rt =>
    exact cancelIpcBlocking_blockedOnReply_preserves_projection ctx observer st victim tcb ep rt
      hB hValid hVictimHigh hObjInv hIdxComplete hObjSetInv hCtxHigh (hOwed ep rt hB)
  | blockedOnNotification n =>
    have hEq : Lifecycle.Suspend.cancelIpcBlocking st victim tcb =
        Lifecycle.Suspend.restoreToReadyCancelled
          (removeFromNotificationWaitQueue st victim) victim := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    rw [hEq]
    exact (restoreToReadyCancelled_preserves_projection_high ctx observer _ victim hObjHigh
      (removeFromNotificationWaitQueue_preserves_objects_invExt st victim hObjInv)).trans
      (removeFromNotificationWaitQueue_preserves_projection_high ctx observer st victim hValid
        hVictimHigh hN hObjInv)

/-- **The teardown of a hidden victim is invisible on every core**: it writes
objects alone (`cancelIpcBlocking_scheduler_eq`, `cancelIpcBlocking_machine_eq`),
so the per-core projection follows from the boot-core one. -/
theorem cancelIpcBlocking_preserves_projectionOnCore_high (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (hValid : LabelingContextValid ctx)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hObjInv : st.objects.invExt)
    (hQ : endpointQueueLabelsAgree ctx st) (hN : notificationLabelsAgree ctx st)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hCtxHigh : cancelledDonationContextHigh ctx observer st victim tcb)
    (hOwed : ∀ ep rt, tcb.ipcState = .blockedOnReply ep rt →
      ∀ rid, tcb.replyObject = some rid → replyFrameHeadHolderDonation st rid victim)
    (c : CoreId) :
    projectStateOnCore ctx observer (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) c
      = projectStateOnCore ctx observer st c := by
  have hS := cancelIpcBlocking_scheduler_eq st victim tcb
  have hM := cancelIpcBlocking_machine_eq st victim tcb
  exact projectStateOnCore_congr ctx observer
    (cancelIpcBlocking_preserves_projection_high ctx observer st victim tcb hValid hVictimHigh
      hObjInv hQ hN hIdxComplete hObjSetInv hCtxHigh hOwed)
    (by rw [hS]; rfl) (by rw [hS]; rfl) (by rw [hS]; rfl) (by rw [hS]; rfl) (by rw [hS]; rfl)
    (by rw [hM])

/-- **WS-SM SM6.E (boot-core form): the cross-core cancellation of a hidden
victim is invisible**, on every arm.

WS-SX SX24 (D47) retires the teardown-projection hypothesis this theorem took
(and the reply-arm corollary that discharged it for `.blockedOnReply` alone):
the teardown is `cancelIpcBlocking_preserves_projection_high`, read off the
labels every kernel entry carries (`endpointQueueLabelsAgree`,
`notificationLabelsAgree`).  Two labelling obligations remain the reclaim's, on
the scheduler side: `descheduledHolderHigh` (discharged where no donation is
resolved, `descheduledHolderHigh_of_no_donation`, and in general from the
`Call`-time flow check, `descheduledHolderHigh_of_donationOwnerFlowsToHolder`)
and `cancelledDonationContextHigh` (WS-ZA ZA6.30: the returned context's
release entry moves to its owner's home core, and the projection keeps release
cores; discharged where no donation is resolved,
`cancelledDonationContextHigh_of_no_donation`).  `hOwed` is the reply head's
coherence the reply arm's donation return reads. -/
theorem cancelIpcBlockingOnCore_cancellation_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hValid : LabelingContextValid ctx)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hObjInv : st.objects.invExt)
    (hQ : endpointQueueLabelsAgree ctx st) (hN : notificationLabelsAgree ctx st)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hHolderHigh : descheduledHolderHigh ctx observer st victim tcb)
    (hCtxHigh : cancelledDonationContextHigh ctx observer st victim tcb)
    (hOwed : ∀ ep rt, tcb.ipcState = .blockedOnReply ep rt →
      ∀ rid, tcb.replyObject = some rid → replyFrameHeadHolderDonation st rid victim) :
    projectState ctx observer
        (cancelIpcBlockingOnCore victim tcb executingCore st).1
      = projectState ctx observer st := by
  rw [cancelIpcBlockingOnCore_state_eq,
      descheduleAtPlacement_preserves_projection ctx observer _ victim hVictimHigh]
  unfold cancelIpcBlockingReclaimed
  rw [descheduleUnboundHolder_preserves_projection ctx observer st victim tcb hHolderHigh,
      cancelIpcBlockingMigrated_preserves_projection ctx observer victim tcb st hCtxHigh]
  exact cancelIpcBlocking_preserves_projection_high ctx observer st victim tcb hValid hVictimHigh
    hObjInv hQ hN hIdxComplete hObjSetInv hCtxHigh hOwed

/-- **WS-SM SM6.E (∀-core form): the cross-core cancellation of a hidden victim
is invisible on every core**, on every arm — the per-core teardown is
`cancelIpcBlocking_preserves_projectionOnCore_high` (WS-SX SX24). -/
theorem cancelIpcBlockingOnCore_cancellation_NI_smp
    (ctx : LabelingContext) (observer : IfObserver)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hValid : LabelingContextValid ctx)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hObjInv : st.objects.invExt)
    (hQ : endpointQueueLabelsAgree ctx st) (hN : notificationLabelsAgree ctx st)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hHolderHigh : descheduledHolderHigh ctx observer st victim tcb)
    (hCtxHigh : cancelledDonationContextHigh ctx observer st victim tcb)
    (hOwed : ∀ ep rt, tcb.ipcState = .blockedOnReply ep rt →
      ∀ rid, tcb.replyObject = some rid → replyFrameHeadHolderDonation st rid victim) :
    lowEquivalent_smp ctx observer
      (cancelIpcBlockingOnCore victim tcb executingCore st).1 st := by
  intro c
  show projectStateOnCore ctx observer
      (cancelIpcBlockingOnCore victim tcb executingCore st).1 c
    = projectStateOnCore ctx observer st c
  rw [cancelIpcBlockingOnCore_state_eq,
      descheduleAtPlacement_preserves_projectionOnCore ctx observer _ victim c
        hVictimHigh]
  unfold cancelIpcBlockingReclaimed
  rw [descheduleUnboundHolder_preserves_projectionOnCore ctx observer st victim tcb c
        hHolderHigh,
      cancelIpcBlockingMigrated_preserves_projectionOnCore ctx observer victim tcb st c hCtxHigh]
  exact cancelIpcBlocking_preserves_projectionOnCore_high ctx observer st victim tcb hValid
    hVictimHigh hObjInv hQ hN hIdxComplete hObjSetInv hCtxHigh hOwed c

-- ============================================================================
-- §6  WS-RR RR8.9 — the deschedule obligation, discharged from the labelling
-- ============================================================================

-- `v0.35.158`: `cancelAbortedHolderWake?_donation` is retired with the wake;
-- the deschedule's trigger states the same fact beside its definition
-- (`cancelUnboundHolder?_donation`, `Lifecycle/Suspend.lean`).

/-- **WS-RR RR8.9**, carried over at `v0.35.158`: `descheduledHolderHigh` is
**discharged** — the reclaim's holder deschedule is invisible to any observer
that cannot see the victim.

This is the whole of the obligation, and it needs none of the queue reasoning
the wake's own docstring once said it waited on: a run-queue removal is
filtered by the removed thread's *own* observability, so all that is required
is that a non-observable victim's donation holder is non-observable too — which
is `donationOwnerFlowsToHolder`, the labelling fact a deployment establishes at
the `Call` that minted the donation.

`hOwed` is the local coherence fact the reclaim's trigger already needs
(`replyFrameHeadHolderDonation`, WS-HP HP4.2), consumed here through
`cancelledCallerDonation?_holder_holds_victim_donation` so the donation the
labelling fact is read at is the one the resolver found. -/
theorem descheduledHolderHigh_of_donationOwnerFlowsToHolder
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB)
    (hFlow : donationOwnerFlowsToHolder ctx st)
    (hOwed : ∀ rid, tcb.replyObject = some rid →
      replyFrameHeadHolderDonation st rid victim)
    (hVictimHigh : threadObservable ctx observer victim = false) :
    descheduledHolderHigh ctx observer st victim tcb := by
  intro holder hW
  obtain ⟨scId, hRes⟩ := cancelUnboundHolder?_donation st _ victim tcb holder hW
  exact donationHolderHigh_of_donorHigh ctx observer st holder victim scId hFlow
    (cancelledCallerDonation?_holder_holds_victim_donation st victim tcb scId holder hOwed hRes)
    hVictimHigh

end SeLe4n.Kernel
