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
leg is discharged substantively). -/
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
is invisible on *every* core, given the per-core teardown projection. -/
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

end SeLe4n.Kernel
