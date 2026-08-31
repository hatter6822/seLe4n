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
-- docs/planning/SMP_CROSS_CORE_IPC_PLAN.md).

import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallNiPerCore
import SeLe4n.Kernel.InformationFlow.Invariant.Composition

/-!
# WS-SM SM6.E — Cross-core cancellation non-interference

The information-flow slice of SM6.E: cancelling a **non-observable** victim is
invisible to a low observer.

The SM6.E-*new* state effects over the single-core suspend pipeline are all
discharged **substantively** here:

* the **home-core deschedule** (`descheduleThread`, the `removeRunnableOnCore`
  of a high victim on an arbitrary core) — §2;
* the **∀-core replenish-queue frames** (`setReplenishQueueOnCore` at *any*
  core is projection-invisible — the rqCore-parametrised purge of the per-core
  bound arm reduces to exactly this) — §1;
* the **replenishment migration** (`migrateSchedContextReplenishment`, the
  §2b donated-arm addition) — §1;
* the **composite** `cancelIpcBlockingOnCore` for a `.ready` victim (the
  suspend-of-a-running-thread scenario — the cross-core-relevant case, since
  a blocked victim is neither queued nor current on any core) — §3.

The single-core object-level teardown (`cancelIpcBlocking`'s sweeps and
reply-link consume) and the donated-arm return (`cleanupDonatedSchedContext`)
are surface **shared with the single-core suspend pipeline**, whose projection
preservation is the InformationFlow subsystem's established closure form
(`suspendThread_preserves_projection` / `cancelDonatedDonation_preserves_projection`,
AK6-F.17/18).  The composites here (§3/§4) take exactly that single obligation
as a hypothesis and discharge every cross-core leg substantively — so closing
the single-core closure forms immediately closes the cross-core NI too.
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
AK6-F.2a frame, covering the per-core bound arm's rqCore-parametrised purge. -/
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

/-- WS-SM SM6.E: the donated-arm replenishment migration (§2b) is invisible
on *every* core — the per-core strengthening of the production SM5.H.4
boot-core frame. -/
theorem migrateSchedContextReplenishment_preserves_projectionOnCore
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) (c : CoreId) :
    projectStateOnCore ctx observer
      (migrateSchedContextReplenishment st scId fromCore toCore) c =
    projectStateOnCore ctx observer st c := by
  refine projectStateOnCore_congr ctx observer
    (migrateSchedContextReplenishment_preserves_projection ctx observer st scId
      fromCore toCore)
    ?_ ?_ ?_ ?_ ?_ ?_
  · unfold migrateSchedContextReplenishment
    split
    · rfl
    · simp only [SchedulerState.setReplenishQueueOnCore_runQueueOnCore]
  · unfold migrateSchedContextReplenishment
    split
    · rfl
    · simp only [SchedulerState.setReplenishQueueOnCore_currentOnCore]
  · unfold migrateSchedContextReplenishment
    split
    · rfl
    · simp only [SchedulerState.setReplenishQueueOnCore_activeDomainOnCore]
  · unfold migrateSchedContextReplenishment
    split
    · rfl
    · simp only [SchedulerState.setReplenishQueueOnCore_domainTimeRemainingOnCore]
  · unfold migrateSchedContextReplenishment
    split
    · rfl
    · simp only [SchedulerState.setReplenishQueueOnCore_domainScheduleIndexOnCore]
  · unfold migrateSchedContextReplenishment
    split
    · rfl
    · rfl

-- ============================================================================
-- §2  The home-core deschedule of a high victim is invisible
-- ============================================================================

/-- WS-SM SM6.E (boot-core form): descheduling a **non-observable** victim
from its home core is invisible to a low observer — the wakeThread-dual of
the SM6.A wake-invisibility. -/
theorem descheduleThread_cancellation_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (victim : SeLe4n.ThreadId) (executingCore : CoreId)
    (hVictimHigh : threadObservable ctx observer victim = false) :
    projectState ctx observer (descheduleThread st victim executingCore).1
      = projectState ctx observer st := by
  rw [descheduleThread_state_eq]
  exact removeRunnableOnCore_preserves_projection ctx observer st victim _ hVictimHigh

/-- WS-SM SM6.E (∀-core form): descheduling a high victim is invisible on
*every* core — including the victim's home core, whose run-queue/current
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
  exact removeRunnableOnCore_preserves_projectionOnCore ctx observer st victim _ c
    hVictimHigh

-- ============================================================================
-- §3  The cancellation composite
-- ============================================================================

/-- WS-SM SM6.E (boot-core form): the cross-core cancellation of a high
victim is invisible, given the single-core teardown's projection preservation
(the obligation the production closure form
`suspendThread_preserves_projection` G3 documents; the cross-core deschedule
leg is discharged substantively).

WS-RR RR2.18: `hTeardownProj` is **discharged** for the two arms whose teardown
touches only the victim and its Reply object —
`cancelIpcBlockingOnCore_ready_cancellation_NI` (`.ready`) and
`cancelIpcBlockingOnCore_reply_cancellation_NI` (`.blockedOnReply`, §5).  It
remains a hypothesis on the queue arms for a stated reason, given at the second
of those. -/
theorem cancelIpcBlockingOnCore_cancellation_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hTeardownProj : projectState ctx observer (cancelIpcBlocking st victim tcb)
        = projectState ctx observer st) :
    projectState ctx observer
        (cancelIpcBlockingOnCore victim tcb executingCore st).1
      = projectState ctx observer st := by
  rw [cancelIpcBlockingOnCore_state_eq,
      removeRunnableOnCore_preserves_projection ctx observer _ victim _ hVictimHigh]
  exact hTeardownProj

/-- WS-SM SM6.E (∀-core form): the cross-core cancellation of a high victim
is invisible on *every* core, given the per-core teardown projection.

WS-RR RR2.18: see the boot-core form above for which arms now discharge that
hypothesis outright. -/
theorem cancelIpcBlockingOnCore_cancellation_NI_smp
    (ctx : LabelingContext) (observer : IfObserver)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hTeardownProj : ∀ c : CoreId,
        projectStateOnCore ctx observer (cancelIpcBlocking st victim tcb) c
          = projectStateOnCore ctx observer st c) :
    lowEquivalent_smp ctx observer
      (cancelIpcBlockingOnCore victim tcb executingCore st).1 st := by
  intro c
  show projectStateOnCore ctx observer
      (cancelIpcBlockingOnCore victim tcb executingCore st).1 c
    = projectStateOnCore ctx observer st c
  rw [cancelIpcBlockingOnCore_state_eq,
      removeRunnableOnCore_preserves_projectionOnCore ctx observer _ victim _ c
        hVictimHigh]
  exact hTeardownProj c

/-- WS-SM SM6.E (boot-core form, fully substantive): cancelling a `.ready`
high victim — the suspend-of-a-running-thread scenario, the cross-core-
relevant case — is invisible: the teardown is the identity, so the whole
composite is the (invisible) home-core deschedule. -/
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
  exact removeRunnableOnCore_preserves_projectionOnCore ctx observer st victim _ c
    hVictimHigh

-- ============================================================================
-- §4  The per-core donated arm
-- ============================================================================

/-- WS-SM SM6.E (boot-core form): the per-core donated-arm cancellation is
invisible given the single-core return's projection preservation (the
AK6-F.17 `cancelDonatedDonation_preserves_projection` obligation) — the
SM6.E-new replenishment migration is discharged substantively. -/
theorem cancelDonatedDonationOnCore_cancellation_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hReturnProj : ∀ stR, cleanupDonatedSchedContext st tid = .ok stR →
        projectState ctx observer stR = projectState ctx observer st)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · cases h
    · injection h with h
      subst h
      rw [migrateSchedContextReplenishment_preserves_projection]
      exact hReturnProj _ (by assumption)
  · cases h

/-- WS-SM SM6.E (∀-core form): the per-core donated-arm cancellation is
invisible on *every* core given the per-core return projection. -/
theorem cancelDonatedDonationOnCore_cancellation_NI_smp
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hReturnProj : ∀ stR, cleanupDonatedSchedContext st tid = .ok stR →
        ∀ c : CoreId, projectStateOnCore ctx observer stR c
          = projectStateOnCore ctx observer st c)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    lowEquivalent_smp ctx observer st' st := by
  intro c
  show projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · cases h
    · injection h with h
      subst h
      rw [migrateSchedContextReplenishment_preserves_projectionOnCore]
      exact hReturnProj _ (by assumption) c
  · cases h


-- ============================================================================
-- §5  WS-RR RR2.18 — discharging the teardown projection on the reply arm
-- ============================================================================
-- `hTeardownProj` above is the cancellation's *own* projection equality, taken
-- as a hypothesis: a closure form that gives back what it is handed.  Below it
-- is **discharged** for the `.blockedOnReply` teardown — the arm the live
-- `.tcbSuspend` of a caller awaiting a reply takes — from the three writes that
-- arm actually makes, each invisible for its own reason:
--
--   * the victim's `ipcState` / queue-link reset (`restoreToReady`) and its
--     `replyObject` clear (`clearTcbReplyObject`) land on the victim's own TCB,
--     which `LabelingContextValid` makes unobservable when the victim is;
--   * the Reply's `caller` back-link clear (`clearReplyObjectCaller`) is
--     invisible **unconditionally** — `projectKernelObject` strips `caller`,
--     so it does not even need the Reply object to be high.

/-- WS-RR RR2.18: `restoreToReady` writes one TCB, so it preserves the
object-store invariant. -/
theorem restoreToReady_preserves_objects_invExt (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (Lifecycle.Suspend.restoreToReady st tid).objects.invExt := by
  unfold Lifecycle.Suspend.restoreToReady
  split
  · exact RHTable_insert_preserves_invExt st.objects tid.toObjId _ hInv
  · exact hInv

/-- WS-RR RR2.18: `restoreToReady` at a high thread is invisible. -/
theorem restoreToReady_preserves_projection_high
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (Lifecycle.Suspend.restoreToReady st tid)
      = projectState ctx observer st := by
  unfold Lifecycle.Suspend.restoreToReady
  split
  · exact objects_insert_preserves_projection_high ctx observer st tid.toObjId _
      hTidObjHigh hObjInv
  · rfl

/-- WS-RR RR2.18: clearing a high thread's `replyObject` is invisible. -/
theorem clearTcbReplyObject_preserves_projection_high
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (Lifecycle.Suspend.clearTcbReplyObject st tid)
      = projectState ctx observer st := by
  unfold Lifecycle.Suspend.clearTcbReplyObject
  split
  · exact objects_insert_preserves_projection_high ctx observer st tid.toObjId _
      hTidObjHigh hObjInv
  · rfl

/-- WS-RR RR2.18: clearing a Reply object's `caller` back-link is invisible
**unconditionally** — the projection strips `caller`, so no high-object
hypothesis on the Reply is needed. -/
theorem clearReplyObjectCaller_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt) :
    projectState ctx observer (Lifecycle.Suspend.clearReplyObjectCaller st rid)
      = projectState ctx observer st := by
  unfold Lifecycle.Suspend.clearReplyObjectCaller
  split
  · next r hR =>
    refine objects_insert_preserves_projection_of_proj_eq ctx observer st rid.toObjId _ hObjInv ?_
    rw [(SystemState.getReply?_eq_some_iff st rid r).mp hR]
    exact congrArg some (projectKernelObject_reply_caller_invariant ctx observer r none).symm
  · rfl

/-- WS-RR RR2.18: the whole reply-link consume is invisible for a high victim. -/
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
      simp only []
      rw [clearReplyObjectCaller_preserves_projection ctx observer _ rid
        (clearTcbReplyObject_preserves_objects_invExt st tid hObjInv)]
      exact clearTcbReplyObject_preserves_projection_high ctx observer st tid hTidObjHigh hObjInv

/-- **WS-RR RR2.18: the teardown projection, discharged on the reply arm.**

For a victim blocked awaiting a reply, `cancelIpcBlocking`'s three writes are
the victim's own TCB (twice) and the Reply's `caller` back-link — the first two
invisible because the victim is high, the third invisible outright.  This is the
`hTeardownProj` obligation the cross-core theorems above take as a hypothesis,
proved rather than assumed. -/
theorem cancelIpcBlocking_blockedOnReply_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (ep : SeLe4n.ObjId)
    (rt : Option SeLe4n.ThreadId)
    (hBlocked : tcb.ipcState = .blockedOnReply ep rt)
    (hValid : LabelingContextValid ctx)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (Lifecycle.Suspend.cancelIpcBlocking st victim tcb)
      = projectState ctx observer st := by
  have hObjHigh : objectObservable ctx observer victim.toObjId = false :=
    hValid.coherenceImpliesObjectHigh observer victim hVictimHigh
  unfold Lifecycle.Suspend.cancelIpcBlocking
  rw [hBlocked]
  simp only []
  have h1 : projectState ctx observer
      (Lifecycle.Suspend.consumeReplyLink (Lifecycle.Suspend.restoreToReady st victim) victim tcb)
      = projectState ctx observer (Lifecycle.Suspend.restoreToReady st victim) :=
    consumeReplyLink_preserves_projection_high ctx observer _ victim tcb hObjHigh
      (restoreToReady_preserves_objects_invExt st victim hObjInv)
  exact h1.trans (restoreToReady_preserves_projection_high ctx observer st victim hObjHigh hObjInv)


/-- **WS-RR RR2.18 (boot-core form, fully substantive)**: cancelling a
`.blockedOnReply` high victim across cores is invisible — no teardown-projection
hypothesis.

Together with `cancelIpcBlockingOnCore_ready_cancellation_NI` (the `.ready`
victim) this covers the two arms whose write set is confined to the victim's own
TCB and its Reply object.  The three *queue* arms
(`.blockedOnSend` / `.blockedOnReceive` / `.blockedOnCall`, and
`.blockedOnNotification`) still take `hTeardownProj`, and cannot be discharged
without a labelling invariant this tree does not yet carry: their teardown
rewrites the endpoint or notification object the victim was queued on and splices
its queue neighbours' TCBs, and *nothing states that those are high when the
victim is*.  That is a real gap, not a proof-engineering one — a low endpoint
holding a high waiter would make the cancellation visible — and closing it means
introducing an endpoint/notification queue label-uniformity invariant and
**establishing** it on every enqueue path.  Registered as WS-RR RR3 debt rather
than papered over here. -/
theorem cancelIpcBlockingOnCore_reply_cancellation_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState) (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId)
    (hBlocked : tcb.ipcState = .blockedOnReply ep rt)
    (hValid : LabelingContextValid ctx)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer
        (cancelIpcBlockingOnCore victim tcb executingCore st).1
      = projectState ctx observer st :=
  cancelIpcBlockingOnCore_cancellation_NI ctx observer victim tcb executingCore st hVictimHigh
    (cancelIpcBlocking_blockedOnReply_preserves_projection ctx observer st victim tcb ep rt
      hBlocked hValid hVictimHigh hObjInv)

end SeLe4n.Kernel
