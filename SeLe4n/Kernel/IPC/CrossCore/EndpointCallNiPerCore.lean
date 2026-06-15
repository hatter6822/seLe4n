-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM6.A.7 cross-core IPC (per-core / ∀-core
-- non-interference; see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md).

import SeLe4n.Kernel.IPC.CrossCore.EndpointCallNI
import SeLe4n.Kernel.InformationFlow.ProjectionPerCore

/-!
# WS-SM SM6.A.7 — Per-core (∀-core) non-interference for the cross-core call

`endpointCallOnCore_call_path_NI` certifies non-interference for the **boot-core**
observer projection (`projectState`).  For a genuinely cross-core call the
receiver is woken onto its *home* core, so the security-relevant statement is the
**per-core** one: for *every* core `c`, the per-core observer projection
(`projectStateOnCore … c`) is preserved — i.e. the post-state is
`lowEquivalent_smp` to the pre-state.

The argument: the call touches the scheduler only by (a) the cross-core wake
enqueuing the *high* receiver onto its home core and (b) the per-core deschedule
removing the *high* caller from its own core.  Both run-queue edits insert/remove
a thread the observer filters out (`projectRunnableOnCore` filters by
`threadObservable`), so every core's runnable projection is unchanged; the call
never touches any core's current-thread / domain slots or the machine registers;
and the object writes are all high.  §1 supplies the machine-register frame for
the object steps (mirroring the existing `*_scheduler_eq` family), §2 the
filtered per-core congruence, §3 the per-core run-queue projection lemmas, §4 the
per-step per-core preservation, and §5 the ∀-core assembly.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  Machine-register frame for the object steps (mirrors `*_scheduler_eq`)
-- ============================================================================

/-- `storeTcbQueueLinks` leaves the machine registers untouched. -/
theorem storeTcbQueueLinks_machine_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    st'.machine = st.machine := by
  unfold storeTcbQueueLinks at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_machine_eq st pair.2 tid.toObjId _ hStore

/-- `storeTcbIpcStateAndMessage` leaves the machine registers untouched. -/
theorem storeTcbIpcStateAndMessage_machine_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.machine = st.machine := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_machine_eq st pair.2 tid.toObjId _ hStore

/-- `endpointQueuePopHead` leaves the machine registers untouched. -/
theorem endpointQueuePopHead_machine_eq
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, _headTcb, st')) :
    st'.machine = st.machine := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []
        cases hLookup : lookupTcb st headTid with
        | none => simp
        | some headTcb =>
          simp only []
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair => simp only []; cases hNext : headTcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, hEq⟩; subst hEq
                exact (storeTcbQueueLinks_machine_eq _ _ headTid none none none hFinal).trans
                  (storeObject_machine_eq _ _ endpointId _ hStore)
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, hEq⟩; subst hEq
                    exact (storeTcbQueueLinks_machine_eq _ _ headTid none none none hFinal).trans
                      ((storeTcbQueueLinks_machine_eq _ _ nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext hLink).trans
                        (storeObject_machine_eq _ _ endpointId _ hStore))

/-- `endpointQueueEnqueue` leaves the machine registers untouched. -/
theorem endpointQueueEnqueue_machine_eq
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    st'.machine = st.machine := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        split at hStep
        · simp at hStep
        · split at hStep
          · simp at hStep
          · revert hStep
            cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                intro hStep
                exact (storeTcbQueueLinks_machine_eq _ _ tid _ _ _ hStep).trans
                  (storeObject_machine_eq _ _ endpointId _ hStore)
            | some tailTid =>
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail]
              | some tailTcb =>
                simp only [hLookupTail]
                cases hStore : storeObject endpointId _ st with
                | error e => simp
                | ok pair =>
                  simp only []
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some tid) with
                  | error e => simp
                  | ok st2 =>
                    simp only []
                    intro hStep
                    exact (storeTcbQueueLinks_machine_eq _ _ tid _ _ _ hStep).trans
                      ((storeTcbQueueLinks_machine_eq _ _ tailTid _ _ _ hLink1).trans
                        (storeObject_machine_eq _ _ endpointId _ hStore))

-- ============================================================================
-- §2  Per-core observable-state congruence taking the *filtered* runnable
-- ============================================================================

/-- SM6.A.7: the per-core form of `projectStateOnCore_congr` that takes the
already-*filtered* `projectRunnableOnCore` equality (rather than raw run-queue
slot equality), so it applies to a run-queue write of a high thread — where the
slot changes but the low-observer projection does not. -/
theorem projectStateOnCore_congr_runnable (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c : CoreId}
    (hBase : projectState ctx observer st' = projectState ctx observer st)
    (hRun : projectRunnableOnCore ctx observer st' c = projectRunnableOnCore ctx observer st c)
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hAD : st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c)
    (hDTR : st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c)
    (hDSI : st'.scheduler.domainScheduleIndexOnCore c = st.scheduler.domainScheduleIndexOnCore c)
    (hRegs : st'.machine.regsOnCore c = st.machine.regsOnCore c) :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  unfold projectStateOnCore
  rw [hBase, hRun,
      projectCurrentOnCore_frame ctx observer hCur,
      projectActiveDomainOnCore_frame ctx observer hAD,
      projectDomainTimeRemainingOnCore_frame ctx observer hDTR,
      projectDomainScheduleIndexOnCore_frame ctx observer hDSI,
      projectMachineRegsOnCore_frame ctx observer hCur hRegs]

-- ============================================================================
-- §3  Per-core run-queue projection: a high enqueue/remove is filter-invisible
-- ============================================================================

/-- SM6.A.7: enqueuing a **high** thread onto *any* core's run queue leaves every
core's runnable projection unchanged (the inserted thread is filtered out at its
target core; other cores' slots are untouched). -/
theorem enqueueRunnableOnCore_projectRunnableOnCore_high (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (c' : CoreId) (hHigh : threadObservable ctx observer tid = false) :
    projectRunnableOnCore ctx observer (enqueueRunnableOnCore st c tid) c'
      = projectRunnableOnCore ctx observer st c' := by
  unfold projectRunnableOnCore
  by_cases hcc : c' = c
  · subst hcc
    cases hTcb : st.getTcb? tid with
    | none => simp only [enqueueRunnableOnCore, hTcb]
    | some tcb =>
      simp only [enqueueRunnableOnCore, hTcb]
      split
      · rfl
      · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        exact RunQueue.toList_filter_insert_neg' _ tid _ _ hHigh
  · rw [enqueueRunnableOnCore_runQueueOnCore_ne st c c' tid (fun e => hcc e.symm)]

/-- SM6.A.7: removing a **high** thread from *any* core's run queue leaves every
core's runnable projection unchanged. -/
theorem removeRunnableOnCore_projectRunnableOnCore_high (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (c' : CoreId) (hHigh : threadObservable ctx observer tid = false) :
    projectRunnableOnCore ctx observer (removeRunnableOnCore st tid c) c'
      = projectRunnableOnCore ctx observer st c' := by
  unfold projectRunnableOnCore
  by_cases hcc : c' = c
  · subst hcc
    rw [removeRunnableOnCore_runQueueOnCore_self]
    exact RunQueue.toList_filter_remove_neg _ tid _ hHigh
  · rw [removeRunnableOnCore_runQueueOnCore_ne st tid c c' (fun h => hcc h.symm)]

-- ============================================================================
-- §4  Per-step per-core projection preservation
-- ============================================================================

/-- The fully filtered per-core congruence: takes the *projection-level*
equalities for the three observer-gated slots (runnable, current, machine
registers) plus raw equalities for the three transparent domain slots.  The
caller deschedule needs this stronger form because `removeRunnableOnCore` clears
the *current* thread on the executing core (a high thread), so the raw current
slot changes while its projection does not. -/
theorem projectStateOnCore_congr_proj (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c : CoreId}
    (hBase : projectState ctx observer st' = projectState ctx observer st)
    (hRun : projectRunnableOnCore ctx observer st' c = projectRunnableOnCore ctx observer st c)
    (hCurP : projectCurrentOnCore ctx observer st' c = projectCurrentOnCore ctx observer st c)
    (hAD : st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c)
    (hDTR : st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c)
    (hDSI : st'.scheduler.domainScheduleIndexOnCore c = st.scheduler.domainScheduleIndexOnCore c)
    (hRegsP : projectMachineRegsOnCore ctx observer st' c = projectMachineRegsOnCore ctx observer st c) :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  unfold projectStateOnCore
  rw [hBase, hRun, hCurP,
      projectActiveDomainOnCore_frame ctx observer hAD,
      projectDomainTimeRemainingOnCore_frame ctx observer hDTR,
      projectDomainScheduleIndexOnCore_frame ctx observer hDSI, hRegsP]

/-- `enqueueRunnableOnCore` leaves every core's active-domain slot untouched. -/
theorem enqueueRunnableOnCore_activeDomainOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (c' : CoreId) :
    (enqueueRunnableOnCore st c tid).scheduler.activeDomainOnCore c'
      = st.scheduler.activeDomainOnCore c' := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, hTcb]
  | some tcb =>
    simp only [enqueueRunnableOnCore, hTcb]
    split
    · rfl
    · simp only [SchedulerState.setRunQueueOnCore_activeDomainOnCore]

/-- `enqueueRunnableOnCore` leaves every core's domain-time-remaining slot. -/
theorem enqueueRunnableOnCore_domainTimeRemainingOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (c' : CoreId) :
    (enqueueRunnableOnCore st c tid).scheduler.domainTimeRemainingOnCore c'
      = st.scheduler.domainTimeRemainingOnCore c' := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, hTcb]
  | some tcb =>
    simp only [enqueueRunnableOnCore, hTcb]
    split
    · rfl
    · simp only [SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore]

/-- `enqueueRunnableOnCore` leaves every core's domain-schedule-index slot. -/
theorem enqueueRunnableOnCore_domainScheduleIndexOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (c' : CoreId) :
    (enqueueRunnableOnCore st c tid).scheduler.domainScheduleIndexOnCore c'
      = st.scheduler.domainScheduleIndexOnCore c' := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, hTcb]
  | some tcb =>
    simp only [enqueueRunnableOnCore, hTcb]
    split
    · rfl
    · simp only [SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]

/-- `enqueueRunnableOnCore` leaves the machine registers untouched. -/
theorem enqueueRunnableOnCore_machineEq (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : (enqueueRunnableOnCore st c tid).machine = st.machine := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, hTcb]
  | some tcb => simp only [enqueueRunnableOnCore, hTcb]; split <;> rfl

/-- `removeRunnableOnCore` leaves every core's machine registers untouched. -/
theorem removeRunnableOnCore_machine_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) : (removeRunnableOnCore st tid c).machine = st.machine := rfl

/-- `removeRunnableOnCore` leaves every core's active-domain slot untouched. -/
theorem removeRunnableOnCore_activeDomainOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (c c' : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.activeDomainOnCore c'
      = st.scheduler.activeDomainOnCore c' := by
  simp [removeRunnableOnCore, SchedulerState.setCurrentOnCore_activeDomainOnCore,
    SchedulerState.setRunQueueOnCore_activeDomainOnCore]

/-- `removeRunnableOnCore` leaves every core's domain-time-remaining slot. -/
theorem removeRunnableOnCore_domainTimeRemainingOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c c' : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.domainTimeRemainingOnCore c'
      = st.scheduler.domainTimeRemainingOnCore c' := by
  simp [removeRunnableOnCore, SchedulerState.setCurrentOnCore_domainTimeRemainingOnCore,
    SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore]

/-- `removeRunnableOnCore` leaves every core's domain-schedule-index slot. -/
theorem removeRunnableOnCore_domainScheduleIndexOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c c' : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.domainScheduleIndexOnCore c'
      = st.scheduler.domainScheduleIndexOnCore c' := by
  simp [removeRunnableOnCore, SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore,
    SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]

/-- SM6.A.7: descheduling a **high** caller preserves every core's *projected*
current thread.  At a remote core the slot is untouched; at the executing core
the cleared thread is the high caller, which the observer already projected to
`none`. -/
theorem removeRunnableOnCore_projectCurrentOnCore_high (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (tid : SeLe4n.ThreadId) (c c' : CoreId)
    (hHigh : threadObservable ctx observer tid = false) :
    projectCurrentOnCore ctx observer (removeRunnableOnCore st tid c) c'
      = projectCurrentOnCore ctx observer st c' := by
  unfold projectCurrentOnCore
  by_cases hcc : c = c'
  · subst hcc
    rw [removeRunnableOnCore_currentOnCore_self]
    cases hCur : st.scheduler.currentOnCore c with
    | none => simp
    | some t =>
      by_cases ht : t = tid
      · subst ht; simp [hHigh]
      · simp [ht]
  · rw [removeRunnableOnCore_currentOnCore_ne st tid c c' hcc]

/-- SM6.A.7: descheduling a **high** caller preserves every core's *projected*
machine registers (the machine is untouched; the only gate change clears a high
current thread the observer already projected away). -/
theorem removeRunnableOnCore_projectMachineRegsOnCore_high (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (tid : SeLe4n.ThreadId) (c c' : CoreId)
    (hHigh : threadObservable ctx observer tid = false) :
    projectMachineRegsOnCore ctx observer (removeRunnableOnCore st tid c) c'
      = projectMachineRegsOnCore ctx observer st c' := by
  unfold projectMachineRegsOnCore
  rw [removeRunnableOnCore_machine_eq]
  by_cases hcc : c = c'
  · subst hcc
    rw [removeRunnableOnCore_currentOnCore_self]
    cases hCur : st.scheduler.currentOnCore c with
    | none => simp
    | some t =>
      by_cases ht : t = tid
      · subst ht; simp [hHigh]
      · simp [ht]
  · rw [removeRunnableOnCore_currentOnCore_ne st tid c c' hcc]

/-- Pop preserves the per-core projection (object-store frame: scheduler and
machine registers are untouched, so every per-core slot agrees). -/
theorem endpointQueuePopHead_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB) (c : CoreId)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hNextHigh : ∀ nextTid, headTcb.queueNext = some nextTid →
        objectObservable ctx observer nextTid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  have hSched := endpointQueuePopHead_scheduler_eq endpointId isReceiveQ st st' tid hStep
  have hMach := endpointQueuePopHead_machine_eq endpointId isReceiveQ st st' tid hStep
  exact projectStateOnCore_congr ctx observer
    (endpointQueuePopHead_preserves_projection ctx observer endpointId isReceiveQ st st' tid
      headTcb hEndpointHigh hTidObjHigh hNextHigh hObjInv hStep)
    (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hMach])

/-- Store preserves the per-core projection (object-store frame). -/
theorem storeTcbIpcStateAndMessage_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage) (c : CoreId)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  have hSched := storeTcbIpcStateAndMessage_scheduler_eq st st' tid ipc msg hStep
  have hMach := storeTcbIpcStateAndMessage_machine_eq st st' tid ipc msg hStep
  exact projectStateOnCore_congr ctx observer
    (storeTcbIpcStateAndMessage_preserves_projection ctx observer st st' tid ipc msg
      hTidObjHigh hObjInv hStep)
    (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hSched]) (by rw [hMach])

/-- Enqueuing a high thread preserves the per-core projection (the run-queue
insert is filter-invisible; current / domain / registers untouched). -/
theorem enqueueRunnableOnCore_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (cc : CoreId) (tid : SeLe4n.ThreadId)
    (c : CoreId) (hHighThread : threadObservable ctx observer tid = false)
    (hHighObj : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectStateOnCore ctx observer (enqueueRunnableOnCore st cc tid) c
      = projectStateOnCore ctx observer st c :=
  projectStateOnCore_congr_runnable ctx observer
    (enqueueRunnableOnCore_preserves_projection ctx observer st cc tid hHighThread hHighObj hObjInv)
    (enqueueRunnableOnCore_projectRunnableOnCore_high ctx observer st cc tid c hHighThread)
    (enqueueRunnableOnCore_currentOnCore st cc tid c)
    (enqueueRunnableOnCore_activeDomainOnCore st cc tid c)
    (enqueueRunnableOnCore_domainTimeRemainingOnCore st cc tid c)
    (enqueueRunnableOnCore_domainScheduleIndexOnCore st cc tid c)
    (by rw [enqueueRunnableOnCore_machineEq])

/-- The cross-core wake of a high receiver preserves the per-core projection. -/
theorem wakeThread_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (c : CoreId)
    (hHighThread : threadObservable ctx observer tid = false)
    (hHighObj : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectStateOnCore ctx observer (wakeThread st tid executingCore).1 c
      = projectStateOnCore ctx observer st c := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_preserves_projectionOnCore ctx observer st
    (determineTargetCore st tid) tid c hHighThread hHighObj hObjInv

/-- Descheduling a high caller preserves the per-core projection (filtered
runnable / current / registers; domain slots untouched). -/
theorem removeRunnableOnCore_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (tid : SeLe4n.ThreadId) (cc : CoreId)
    (c : CoreId) (hHigh : threadObservable ctx observer tid = false) :
    projectStateOnCore ctx observer (removeRunnableOnCore st tid cc) c
      = projectStateOnCore ctx observer st c :=
  projectStateOnCore_congr_proj ctx observer
    (removeRunnableOnCore_preserves_projection ctx observer st tid cc hHigh)
    (removeRunnableOnCore_projectRunnableOnCore_high ctx observer st tid cc c hHigh)
    (removeRunnableOnCore_projectCurrentOnCore_high ctx observer st tid cc c hHigh)
    (removeRunnableOnCore_activeDomainOnCore st tid cc c)
    (removeRunnableOnCore_domainTimeRemainingOnCore st tid cc c)
    (removeRunnableOnCore_domainScheduleIndexOnCore st tid cc c)
    (removeRunnableOnCore_projectMachineRegsOnCore_high ctx observer st tid cc c hHigh)

-- ============================================================================
-- §5  SM6.A.7 — the ∀-core (`lowEquivalent_smp`) non-interference theorem
-- ============================================================================

/-- WS-SM SM6.A.7 (per-core / ∀-core non-interference): a cross-core endpoint
call at a **non-observable** endpoint, between a non-observable caller and a
non-observable receiver, is invisible to a low observer on *every* core — the
post-state is `lowEquivalent_smp` to the pre-state.  This is the SMP-faithful
strengthening of `endpointCallOnCore_call_path_NI` (which covers only the boot
core): no covert channel is opened on the *remote* core the receiver is woken
onto, nor on the executing core where the caller is descheduled, nor on any
bystander core.  Proof: the same single-step chain as the boot-core theorem, but
each step is discharged at an arbitrary observer core `c` — the object writes are
high (object-store frame), the receiver wake's run-queue insert and the caller
deschedule's run-queue remove (and current-thread clear) edit only *high* threads
the observer filters out, and no step touches any core's domain slots or machine
registers. -/
theorem endpointCallOnCore_call_path_NI_smp
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (recvTcb0 : TCB) (st' st'' st4 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hObjInv : st.objects.invExt)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hReceiverHigh : threadObservable ctx observer receiver = false)
    (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
    (hCallerHigh : threadObservable ctx observer caller = false)
    (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
    (hNextHigh : ∀ nextTid, recvTcb0.queueNext = some nextTid →
        objectObservable ctx observer nextTid.toObjId = false) :
    lowEquivalent_smp ctx observer
      (endpointCallOnCore endpointId caller msg executingCore st).1 st := by
  intro c
  have hInv' : st'.objects.invExt :=
    endpointQueuePopHead_preserves_objects_invExt endpointId true st st' receiver recvTcb0 hObjInv hPop
  have hInv'' : st''.objects.invExt :=
    storeTcbIpcStateAndMessage_preserves_objects_invExt st' st'' receiver .ready (some msg) hInv' hStore
  show projectStateOnCore ctx observer
      (endpointCallOnCore endpointId caller msg executingCore st).1 c
    = projectStateOnCore ctx observer st c
  rw [endpointCallOnCore_rendezvous_eq endpointId caller msg executingCore st ep receiver
        recvTcb0 st' st'' st4 hSz1 hSz2 hObj hHead hPop hStore hCallerStore]
  show projectStateOnCore ctx observer (removeRunnableOnCore st4 caller executingCore) c
    = projectStateOnCore ctx observer st c
  rw [removeRunnableOnCore_preserves_projectionOnCore ctx observer st4 caller executingCore c
        hCallerHigh,
      storeTcbIpcStateAndMessage_preserves_projectionOnCore ctx observer
        (wakeThread st'' receiver executingCore).1 st4 caller
        (.blockedOnReply endpointId (some receiver)) none c hCallerObjHigh
        (wakeThread_preserves_objects_invExt st'' receiver executingCore hInv'') hCallerStore,
      wakeThread_preserves_projectionOnCore ctx observer st'' receiver executingCore c
        hReceiverHigh hReceiverObjHigh hInv'',
      storeTcbIpcStateAndMessage_preserves_projectionOnCore ctx observer st' st'' receiver .ready
        (some msg) c hReceiverObjHigh hInv' hStore]
  exact endpointQueuePopHead_preserves_projectionOnCore ctx observer endpointId true st st' receiver
    recvTcb0 c hEndpointHigh hReceiverObjHigh hNextHigh hObjInv hPop

end SeLe4n.Kernel
