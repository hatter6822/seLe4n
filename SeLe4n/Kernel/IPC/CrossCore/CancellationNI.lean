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

/-- **WS-RR RR7.22 (residual, remediation)**: the SM5.H replenishment migration
the corrected reply arm obliges is invisible — the projection shows run queues,
current slots and the domain schedule, not replenishments. -/
theorem cancelIpcBlockingMigrated_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState) :
    projectState ctx observer (cancelIpcBlockingMigrated victim tcb st)
      = projectState ctx observer (cancelIpcBlocking st victim tcb) := by
  unfold cancelIpcBlockingMigrated
  split
  · rename_i scId holder _
    exact migrateSchedContextReplenishment_preserves_projection ctx observer _ scId _ _
  · rfl

/-- The per-core form of the same. -/
theorem cancelIpcBlockingMigrated_preserves_projectionOnCore
    (ctx : LabelingContext) (observer : IfObserver)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState) (c : CoreId) :
    projectStateOnCore ctx observer (cancelIpcBlockingMigrated victim tcb st) c
      = projectStateOnCore ctx observer (cancelIpcBlocking st victim tcb) c := by
  unfold cancelIpcBlockingMigrated
  split
  · rename_i scId holder _
    exact migrateSchedContextReplenishment_preserves_projectionOnCore ctx observer _ scId _ _ c
  · rfl

-- ============================================================================
-- §4b  WS-OD OD1.7 — the reclaim's holder wake
-- ============================================================================

/-- WS-OD OD1.7: placing a **high** thread is invisible in every core's runnable
projection — the insert is filtered out exactly as the enqueue primitive's is. -/
theorem enqueueAbortedHolderOnCore_projectRunnableOnCore_high (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (c' : CoreId) (hHigh : threadObservable ctx observer tid = false) :
    projectRunnableOnCore ctx observer (enqueueAbortedHolderOnCore st c tid) c'
      = projectRunnableOnCore ctx observer st c' := by
  unfold projectRunnableOnCore
  by_cases hcc : c' = c
  · subst hcc
    cases hTcb : st.getTcb? tid with
    | none => simp only [enqueueAbortedHolderOnCore, hTcb]
    | some tcb =>
      simp only [enqueueAbortedHolderOnCore, hTcb]
      split
      · rfl
      · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        exact RunQueue.toList_filter_insert_neg' _ tid _ _ hHigh
  · rw [enqueueAbortedHolderOnCore_runQueueOnCore_ne st c tid c' (fun e => hcc e.symm)]

/-- WS-OD OD1.7: placing a **high** thread preserves the whole-state projection.

Strictly weaker premises than `enqueueRunnableOnCore_preserves_projection`'s:
this step performs no object write at all, so it needs neither the target's
object-observability nor the store invariant. -/
theorem enqueueAbortedHolderOnCore_preserves_projection (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hHighThread : threadObservable ctx observer tid = false) :
    projectState ctx observer (enqueueAbortedHolderOnCore st c tid)
      = projectState ctx observer st := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueAbortedHolderOnCore, hTcb]
  | some tcb =>
    simp only [enqueueAbortedHolderOnCore, hTcb]
    split
    · rfl
    · simp only [projectState]
      congr 1
      all_goals
        first
          | rfl
          | (simp only [projectRunnable, SchedulerState.runnable]
             by_cases hc : c = bootCoreId
             · subst hc
               rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
               exact RunQueue.toList_filter_insert_neg' _ tid _ _ hHighThread
             · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hc])
          | simp only [projectCurrent, projectMachineRegs, projectActiveDomain,
              projectDomainTimeRemaining, projectDomainSchedule, projectDomainScheduleIndex,
              SchedulerState.setRunQueueOnCore_currentOnCore,
              SchedulerState.setRunQueueOnCore_activeDomainOnCore,
              SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore,
              SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore,
              SchedulerState.setRunQueueOnCore_domainSchedule]

/-- WS-OD OD1.7: ...and the per-core projection on every core. -/
theorem enqueueAbortedHolderOnCore_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (cc : CoreId) (tid : SeLe4n.ThreadId)
    (c : CoreId) (hHighThread : threadObservable ctx observer tid = false) :
    projectStateOnCore ctx observer (enqueueAbortedHolderOnCore st cc tid) c
      = projectStateOnCore ctx observer st c :=
  projectStateOnCore_congr_runnable ctx observer
    (enqueueAbortedHolderOnCore_preserves_projection ctx observer st cc tid hHighThread)
    (enqueueAbortedHolderOnCore_projectRunnableOnCore_high ctx observer st cc tid c hHighThread)
    (enqueueAbortedHolderOnCore_currentOnCore st cc tid c)
    (enqueueAbortedHolderOnCore_activeDomainOnCore st cc tid c)
    (enqueueAbortedHolderOnCore_domainTimeRemainingOnCore st cc tid c)
    (enqueueAbortedHolderOnCore_domainScheduleIndexOnCore st cc tid c)
    (by rw [enqueueAbortedHolderOnCore_machineEq])

/-- **WS-OD OD1.7**: the information-flow obligation the holder *wake* adds.

The wake is the scheduler twin of OD1.4's `abortHolderProjectionStable`, and it
carries the same gap for the same reason: the reclaim's abort and its wake both
act on the **holder**, whose label the victim's does not determine.  A run-queue
insert is filtered by the inserted thread's own observability
(`projectRunnable`), so the wake is invisible exactly when the holder is
non-observable.

Stated as the policy fact rather than as a projection equality, because that is
what a deployment can actually establish: a server holding a high caller's
donated SchedContext is reachable from that caller, so a labeling that admits
the `Call` in the first place labels the server at least as high.  Closing it as
a *theorem* needs the endpoint-queue label-uniformity invariant OD1.4's
obligation also waits on — registered WS-OD debt, not assumed away here.

Discharged outright wherever no donation is resolved
(`abortHolderWakeHigh_of_no_donation`), which is every arm but a reply arm whose
caller had donated. -/
def abortHolderWakeHigh (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB) : Prop :=
  ∀ holder : SeLe4n.ThreadId,
    cancelAbortedHolderWake? st (cancelIpcBlockingMigrated victim tcb st) victim tcb = some holder →
      threadObservable ctx observer holder = false

/-- WS-OD OD1.7: with no donation resolved the wake never fires, so the
obligation is vacuous — the remediation adds an obligation exactly where it adds
a write, and nowhere else. -/
theorem abortHolderWakeHigh_of_no_donation (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = none) :
    abortHolderWakeHigh ctx observer st victim tcb := by
  intro holder hW
  rw [show cancelAbortedHolderWake? st (cancelIpcBlockingMigrated victim tcb st) victim tcb = none by
    unfold cancelAbortedHolderWake?; rw [h]] at hW
  exact absurd hW (by simp)

/-- WS-OD OD1.7: under that obligation the wake preserves the projection. -/
theorem wakeAbortedDonationHolder_preserves_projection (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (hHigh : abortHolderWakeHigh ctx observer st victim tcb) :
    projectState ctx observer
        (wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st) victim tcb)
      = projectState ctx observer (cancelIpcBlockingMigrated victim tcb st) := by
  unfold wakeAbortedDonationHolder
  split
  · rfl
  · rename_i holder hW
    exact enqueueAbortedHolderOnCore_preserves_projection ctx observer _ _ holder (hHigh holder hW)

/-- WS-OD OD1.7: ...and the per-core projection on every core. -/
theorem wakeAbortedDonationHolder_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (c : CoreId) (hHigh : abortHolderWakeHigh ctx observer st victim tcb) :
    projectStateOnCore ctx observer
        (wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st) victim tcb) c
      = projectStateOnCore ctx observer (cancelIpcBlockingMigrated victim tcb st) c := by
  unfold wakeAbortedDonationHolder
  split
  · rfl
  · rename_i holder hW
    exact enqueueAbortedHolderOnCore_preserves_projectionOnCore ctx observer _ _ holder c
      (hHigh holder hW)

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
        = projectState ctx observer st)
    (hWakeHigh : abortHolderWakeHigh ctx observer st victim tcb) :
    projectState ctx observer
        (cancelIpcBlockingOnCore victim tcb executingCore st).1
      = projectState ctx observer st := by
  rw [cancelIpcBlockingOnCore_state_eq,
      removeRunnableOnCore_preserves_projection ctx observer _ victim _ hVictimHigh,
      wakeAbortedDonationHolder_preserves_projection ctx observer st victim tcb hWakeHigh,
      cancelIpcBlockingMigrated_preserves_projection]
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
          = projectStateOnCore ctx observer st c)
    (hWakeHigh : abortHolderWakeHigh ctx observer st victim tcb) :
    lowEquivalent_smp ctx observer
      (cancelIpcBlockingOnCore victim tcb executingCore st).1 st := by
  intro c
  show projectStateOnCore ctx observer
      (cancelIpcBlockingOnCore victim tcb executingCore st).1 c
    = projectStateOnCore ctx observer st c
  rw [cancelIpcBlockingOnCore_state_eq,
      removeRunnableOnCore_preserves_projectionOnCore ctx observer _ victim _ c
        hVictimHigh,
      wakeAbortedDonationHolder_preserves_projectionOnCore ctx observer st victim tcb c
        hWakeHigh,
      cancelIpcBlockingMigrated_preserves_projectionOnCore]
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
object-store invariant.

**WS-RR RR7.14**: stated over `restoreToReadyStaging`, so the plain and the
frame-staging spellings share one proof — a staged frame is one more field of
the same single insert. -/
theorem restoreToReadyStaging_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) :
    (Lifecycle.Suspend.restoreToReadyStaging st tid frame).objects.invExt := by
  unfold Lifecycle.Suspend.restoreToReadyStaging
  split
  · exact RHTable_insert_preserves_invExt st.objects tid.toObjId _ hInv
  · exact hInv

theorem restoreToReady_preserves_objects_invExt (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (Lifecycle.Suspend.restoreToReady st tid).objects.invExt :=
  restoreToReadyStaging_preserves_objects_invExt st tid none hInv

/-- **WS-RR RR7.14**: the cancellation spelling. -/
theorem restoreToReadyCancelled_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (Lifecycle.Suspend.restoreToReadyCancelled st tid).objects.invExt :=
  restoreToReadyStaging_preserves_objects_invExt st tid _ hInv

/-- WS-RR RR2.18: `restoreToReady` at a high thread is invisible.

**WS-RR RR7.14 (load-bearing)**: stated over `restoreToReadyStaging`, so the
staged return frame is covered by the same argument — it is written *into the
victim's own TCB*, the one object the premise already has as high, so an
observer that cannot see the thread cannot see the frame it was handed either.
Had the staging gone anywhere else (the machine register banks, say) this
would not hold, and that is precisely why `writeReturnFrameToTcb` does not
touch `machine`. -/
theorem restoreToReadyStaging_preserves_projection_high
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (Lifecycle.Suspend.restoreToReadyStaging st tid frame)
      = projectState ctx observer st := by
  unfold Lifecycle.Suspend.restoreToReadyStaging
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
  restoreToReadyStaging_preserves_projection_high ctx observer st tid none
    hTidObjHigh hObjInv

/-- **WS-RR RR7.14**: the cancellation spelling — the `.ipcCancelled` frame is
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

/-- **WS-OD OD1.4**: the projection obligation the holder abort adds to the
donation return.

The return's own three stores are invisible to every observer (see
`returnDonationToCancelledCaller_preserves_projection` below).  Its *prefix* is
not: `abortHolderPendingIpc` ends the holder's outstanding send or call, and that
writes the holder's endpoint object, the holder's queue neighbours' links and the
holder's own `ipcState` / `threadState` / queue links — every one of which
survives `projectKernelObject`.  So a low observer that can see the holder's
endpoint would see a high victim's cancellation through it.

This is **the same gap the three queue arms already carry**, arriving at the
reply arm through the holder rather than through the victim: closing it needs an
endpoint/notification queue label-uniformity invariant, established on every
enqueue path.  Stated as an obligation rather than assumed away, and discharged
outright wherever the abort is inert (`abortHolderProjectionStable_of_allowed`) —
which is every state on which the reclaim's `passiveServerIdle` hole did not
exist in the first place. -/
def abortHolderProjectionStable (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB) : Prop :=
  ∀ (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId),
    Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = some (scId, holder) →
    projectState ctx observer (Lifecycle.Suspend.abortHolderPendingIpc st holder)
      = projectState ctx observer st

/-- **WS-OD OD1.4**: the obligation is discharged outright when the abort is the
identity.

A holder that is not blocked sending or calling is left untouched by the reclaim
— bit for bit — so there is nothing for an observer of any label to see.  That
covers every state on which the `passiveServerIdle` hole did not arise, which is
why the remediation costs no *existing* information-flow result: it adds an
obligation exactly where it adds a write. -/
theorem abortHolderProjectionStable_of_allowed
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB)
    (hAllowed : ∀ (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId),
      Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = some (scId, holder) →
      ∀ t, lookupTcb st holder = some t → passiveServerIdleAllowed t.ipcState) :
    abortHolderProjectionStable ctx observer st victim tcb := by
  intro scId holder hRes
  rw [Lifecycle.Suspend.abortHolderPendingIpc_eq_self_of_allowed st holder
    (hAllowed scId holder hRes)]

/-- **WS-RR RR7.22 (residual, remediation)**: the donation return's own writes are
invisible to **every** observer, high or low.

Not an accident and not a hypothesis: `projectKernelObject` erases exactly the two
fields the return writes — `TCB.schedContextBinding` (AI4-A) and
`SchedContext.boundThread` (AI4-A) — so all three of its stores are
projection-stable, and `storeObject_projectionStable_preserves_projection` carries
each one at a key of any label.

Worth stating plainly, because the obvious worry about this remediation is the
opposite: returning a high caller's SchedContext writes the *server's* TCB, and a
low server would then see a high thread's cancellation.  It does not, because the
donation binding is not part of what the projection shows.

**WS-OD OD1.4** adds the one hypothesis that is not structural:
`abortHolderProjectionStable`, the holder abort's own projection equality.  The
abort writes queue state, which the projection keeps, so it cannot be discharged
from the erasure argument — see that predicate's docstring for what closing it
needs, and `abortHolderProjectionStable_of_allowed` for the states where it is
free.  The remaining hypotheses are structural: the identity registry is complete
and well-formed, so `storeObject` extends neither. -/
theorem returnDonationToCancelledCaller_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB)
    (hObjInv : st.objects.invExt)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hAbortProj : abortHolderProjectionStable ctx observer st victim tcb) :
    projectState ctx observer (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb)
      = projectState ctx observer st := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  split
  · rename_i scId holder _ hRes _
    split
    · rename_i st' h
      -- WS-OD OD1.4: the store chain runs on the *aborted* state, so its three
      -- structural facts are carried across the abort first.
      have hObjInvA := Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder
        hObjInv
      have hObjSetInvA := Lifecycle.Suspend.abortHolderPendingIpc_preserves_objectIndexSet_invExt
        st holder hObjSetInv
      have hIdxCompleteA := Lifecycle.Suspend.abortHolderPendingIpc_preserves_objectIndexSetComplete
        st holder hObjInv hObjSetInv hIdxComplete
      -- WS-OD OD3.2: the chain is four object writes now — the head clear sits
      -- between the SchedContext store and the client's binding, and is
      -- projection-stable for the same reason the other three are (every field
      -- the return touches is stripped by `projectKernelObject`).
      obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose h
      obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
        hSc, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
        returnDonatedSchedContext_ok_storeChain _ st' holder scId victim n hPop
      have hInv1 := SeLe4n.Model.storeObject_preserves_objects_invExt _ s1 _ _ hObjInvA hS1
      have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
      have hInv3 := SeLe4n.Model.storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
      have hSet1 := SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt _ s1 _ _
        hObjSetInvA hS1
      have hSet2 := storeDonationHeadPop_preserves_objectIndexSet_invExt hSet1 hClear
      have hSet3 := SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt s2 s3 _ _ hSet2 hS3
      have hC1 := SeLe4n.Model.storeObject_preserves_objectIndexSetComplete _ s1 _ _ hObjInvA
        hObjSetInvA hIdxCompleteA hS1
      have hC2 := storeDonationHeadPop_preserves_objectIndexSetComplete hInv1 hSet1 hC1 hClear
      have hC3 := SeLe4n.Model.storeObject_preserves_objectIndexSetComplete s2 s3 _ _ hInv2
        hSet2 hC2 hS3
      have hP1 := storeObject_projectionStable_preserves_projection ctx observer _ s1
        scId.toObjId _ (.schedContext sc) hSc
        (projectKernelObject_schedContext_donationWrite_invariant ctx observer sc _ _)
        (hIdxCompleteA scId.toObjId (by rw [hSc]; intro hx; cases hx))
        hObjInvA hS1
      have hP2 := storeDonationHeadPop_preserves_projection ctx observer hC1 hSet1 hInv1 hClear
      have hP3 := storeObject_projectionStable_preserves_projection ctx observer s2 s3
        victim.toObjId _ (.tcb clientTcb) (lookupTcb_some_objects s2 victim clientTcb hL1)
        (projectKernelObject_tcb_schedContextBinding_invariant ctx observer clientTcb _)
        (hC2 victim.toObjId (by
          rw [lookupTcb_some_objects s2 victim clientTcb hL1]
          intro hx
          cases hx))
        hInv2 hS3
      have hP4 := storeObject_projectionStable_preserves_projection ctx observer s3 s4
        holder.toObjId _ (.tcb serverTcb) (lookupTcb_some_objects s3 holder serverTcb hL2)
        (projectKernelObject_tcb_schedContextBinding_invariant ctx observer serverTcb _)
        (hC3 holder.toObjId (by
          rw [lookupTcb_some_objects s3 holder serverTcb hL2]
          intro hx
          cases hx))
        hInv3 hS4
      have hFinal : projectState ctx observer st' = projectState ctx observer s4 := by
        rw [hEq]
        rfl
      rw [hFinal, hP4, hP3, hP2, hP1]
      exact hAbortProj scId holder hRes
    · rfl
  · rfl

/-- `v0.35.4`: the cancelled caller's frame detach preserves the projection — the
identity where there is nothing to detach, one `detachReplyFrameAbove` otherwise. -/
theorem detachFrameAboveThreadReply_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) (tcb : TCB)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (detachFrameAboveThreadReply st tcb)
      = projectState ctx observer st := by
  rcases detachFrameAboveThreadReply_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]
  · exact detachReplyFrameAbove_preserves_projection ctx observer hIdxComplete hObjInv h

/-- **WS-RR RR2.18: the teardown projection, discharged on the reply arm.**

For a victim blocked awaiting a reply, `cancelIpcBlocking`'s writes are the
victim's own TCB (twice), the Reply's `caller` back-link, and the donation
return — the first two invisible because the victim is high, the third invisible
outright, the fourth invisible because the projection erases the binding fields
it writes.  This is the `hTeardownProj` obligation the cross-core theorems above
take as a hypothesis, proved rather than assumed.

**WS-OD OD1.4**: the return acquired a *prefix* — the holder abort — whose write
set the projection does **not** erase, so the arm now carries
`abortHolderProjectionStable` and nothing else changes.  The obligation is free
(`abortHolderProjectionStable_of_allowed`) on every state where the abort is
inert, which is every state on which the `passiveServerIdle` hole this
remediation closes did not arise. -/
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
    (hAbortProj : abortHolderProjectionStable ctx observer st victim tcb) :
    projectState ctx observer (Lifecycle.Suspend.cancelIpcBlocking st victim tcb)
      = projectState ctx observer st := by
  have hObjHigh : objectObservable ctx observer victim.toObjId = false :=
    hValid.coherenceImpliesObjectHigh observer victim hVictimHigh
  unfold Lifecycle.Suspend.cancelIpcBlocking
  rw [hBlocked]
  simp only []
  -- WS-RR RR7.22 (residual, remediation): the arm's fourth write is the donation
  -- return, and it is invisible to *every* observer rather than only to a high
  -- one — the projection erases the binding fields it touches.
  have hInvR : (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb).objects.invExt :=
    returnDonationToCancelledCaller_preserves_objects_invExt st victim tcb hObjInv
  -- `v0.35.4`: the arm's fifth write is the frame detach, invisible to every
  -- observer for the same reason as the return — it writes a Reply's `prev`,
  -- which the projection strips.  It reads the index completeness the return
  -- carries forward.
  have hCompR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objectIndexSetComplete
    st victim tcb hObjInv hObjSetInv hIdxComplete
  have hInvD : (detachFrameAboveThreadReply
      (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb) tcb).objects.invExt :=
    detachFrameAboveThreadReply_preserves_objects_invExt _ tcb hInvR
  have h1 : projectState ctx observer
      (Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled
          (detachFrameAboveThreadReply
            (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb) tcb) victim)
        victim tcb)
      = projectState ctx observer
        (Lifecycle.Suspend.restoreToReadyCancelled
          (detachFrameAboveThreadReply
            (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb) tcb) victim) :=
    consumeReplyLink_preserves_projection_high ctx observer _ victim tcb hObjHigh
      (restoreToReadyCancelled_preserves_objects_invExt _ victim hInvD)
  exact h1.trans
    ((restoreToReadyCancelled_preserves_projection_high ctx observer _ victim hObjHigh
      hInvD).trans
      ((detachFrameAboveThreadReply_preserves_projection ctx observer _ tcb hCompR hInvR).trans
        (returnDonationToCancelledCaller_preserves_projection ctx observer st victim tcb hObjInv
          hIdxComplete hObjSetInv hAbortProj)))


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
than papered over here.

**WS-OD OD1.4 — what this arm now carries, and why it is not the same
hypothesis.**  The reclaim's holder abort splices a *third* thread out of a
*third* endpoint's queue, so the reply arm reaches the same labelling gap through
the holder that the queue arms reach through the victim, and takes
`abortHolderProjectionStable` for it.  Three things distinguish it from
`hTeardownProj` and are the reason it is stated rather than absorbed.  (1) It is
about a state the theorem's own hypotheses do not name — the holder is resolved
by `cancelledCallerDonation?`, not supplied — so the predicate quantifies over
the resolution rather than over a bound thread.  (2) It is **discharged
outright** whenever the abort is inert (`abortHolderProjectionStable_of_allowed`),
which is every state on which the `passiveServerIdle` hole did not arise; no
information-flow result that held before this remediation is weakened on the
states it held for.  (3) Closing it in general needs exactly the invariant the
queue arms need, plus the fact that the holder is high when the victim is —
which follows from the flow check the donating `Call` passed
(`label victim ⊑ label holder`, `securityFlowsTo_trans`) rather than from a new
assumption.  Registered as WS-OD debt beside the queue arms' gap.

**WS-OD OD1.7** adds `abortHolderWakeHigh`, the scheduler twin of the same gap:
the reclaim not only aborts the holder's IPC, it now *places* the holder on its
home core's run queue, and a run-queue insert is filtered by the inserted
thread's own observability.  All three distinguishing points above apply to it
unchanged — it quantifies over the same resolution, it is discharged outright
where no donation is resolved (`abortHolderWakeHigh_of_no_donation`), and it
closes in general from the same `Call`-time flow check.  Two obligations rather
than one because they are two writes in two domains: OD1.4's is about the object
store, this one about the scheduler. -/
theorem cancelIpcBlockingOnCore_reply_cancellation_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState) (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId)
    (hBlocked : tcb.ipcState = .blockedOnReply ep rt)
    (hValid : LabelingContextValid ctx)
    (hVictimHigh : threadObservable ctx observer victim = false)
    (hObjInv : st.objects.invExt)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hAbortProj : abortHolderProjectionStable ctx observer st victim tcb)
    (hWakeHigh : abortHolderWakeHigh ctx observer st victim tcb) :
    projectState ctx observer
        (cancelIpcBlockingOnCore victim tcb executingCore st).1
      = projectState ctx observer st :=
  cancelIpcBlockingOnCore_cancellation_NI ctx observer victim tcb executingCore st hVictimHigh
    (cancelIpcBlocking_blockedOnReply_preserves_projection ctx observer st victim tcb ep rt
      hBlocked hValid hVictimHigh hObjInv hIdxComplete hObjSetInv hAbortProj)
    hWakeHigh

end SeLe4n.Kernel
