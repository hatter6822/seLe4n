/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.Invariant.Helpers

namespace SeLe4n.Kernel

open SeLe4n.Model

/-! ### WS-F3/K-F5: Capability CRUD and Lifecycle NI proofs — all completed

The following capability and lifecycle operations have NI properties that
follow from compositional reasoning over `storeObject`-level primitives.

**CSpace operations (completed WS-H9):**
- `cspaceDeleteSlot_preserves_lowEquivalent` — line 978
- `cspaceCopy_preserves_lowEquivalent` — line 1099
- `cspaceMove_preserves_lowEquivalent` — line 1158

**Lifecycle operations (completed WS-K-F5):**
- `lifecycleRetypeObject_preserves_lowEquivalent` — Helpers.lean:670
- `retypeFromUntyped_preserves_lowEquivalent` — end of this file
- `lifecycleRevokeDeleteRetype_preserves_projection` — end of this file
- `lifecycleRevokeDeleteRetype_preserves_lowEquivalent` — end of this file

The pattern for each is identical: all mutations happen at non-observable
targets via `storeObject`, and CDT/lifecycle metadata is not part of
`ObservableState`. The proofs compose `storeObject_preserves_projection`
with CDT-specific frame lemmas.
-/

-- ============================================================================
-- WS-F3/F-20: Enforcement-NI bridge theorems
-- ============================================================================

/-- WS-F3/F-20: If cspaceMintChecked succeeds, the resulting state transition
preserves low-equivalence. -/
theorem cspaceMintChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hSlotUniq₁ : cspaceSlotUnique s₁)
    (hSlotUniq₂ : cspaceSlotUnique s₂)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : cspaceMintChecked ctx src dst rights badge s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceMintChecked ctx src dst rights badge s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow₁ : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true := by
    cases h : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) with
    | false =>
      have := cspaceMintChecked_flowDenied ctx src dst rights badge s₁ h
      rw [this] at hStep₁; simp at hStep₁
    | true => rfl
  rw [cspaceMintChecked_eq_cspaceMint_when_allowed ctx src dst rights badge s₁ hFlow₁] at hStep₁
  rw [cspaceMintChecked_eq_cspaceMint_when_allowed ctx src dst rights badge s₂ hFlow₁] at hStep₂
  exact cspaceMint_preserves_lowEquivalent ctx observer src dst rights badge
    s₁ s₂ s₁' s₂' hLow hSrcHigh hDstHigh hSlotUniq₁ hSlotUniq₂ hObjInv₁ hObjInv₂ hStep₁ hStep₂

-- ============================================================================
-- WS-H8/H-07: Enforcement-NI bridge theorems for new wrappers
-- ============================================================================

/-- R5-A/M-01: endpointSendDualChecked NI — projection-based (internalized).

Replaces the prior hypothesis-accepting version. Instead of accepting the
two-state NI property as a hypothesis, this version takes a
one-sided projection preservation hypothesis `hProjection`. The caller proves
that each individual execution preserves the observer's projection. -/
theorem endpointSendDualChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hProjection : ∀ t t', endpointSendDual endpointId sender msg t = .ok ((), t') →
        projectState ctx observer t' = projectState ctx observer t)
    (hStep₁ : endpointSendDualChecked ctx endpointId sender msg s₁ = .ok ((), s₁'))
    (hStep₂ : endpointSendDualChecked ctx endpointId sender msg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow := enforcementSoundness_endpointSendDualChecked ctx endpointId sender msg s₁ s₁' hStep₁
  rw [endpointSendDualChecked_eq_endpointSendDual_when_allowed ctx endpointId sender msg s₁ hFlow] at hStep₁
  rw [endpointSendDualChecked_eq_endpointSendDual_when_allowed ctx endpointId sender msg s₂ hFlow] at hStep₂
  unfold lowEquivalent; rw [hProjection s₁ s₁' hStep₁, hProjection s₂ s₂' hStep₂]; exact hLow

/-- WS-H8/H-07: If notificationSignalChecked succeeds, the resulting state
transition preserves low-equivalence. -/
theorem notificationSignalChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hWaiterDomain₁ : ∀ ntfn tid, s₁.objects[notificationId]? = some (.notification ntfn) →
        tid ∈ ntfn.waitingThreads → threadObservable ctx observer tid = false)
    (hWaiterDomain₂ : ∀ ntfn tid, s₂.objects[notificationId]? = some (.notification ntfn) →
        tid ∈ ntfn.waitingThreads → threadObservable ctx observer tid = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : notificationSignalChecked ctx notificationId signaler badge s₁ = .ok ((), s₁'))
    (hStep₂ : notificationSignalChecked ctx notificationId signaler badge s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = true := by
    cases h : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) with
    | false =>
      have := notificationSignalChecked_flowDenied ctx notificationId signaler badge s₁ h
      rw [this] at hStep₁; simp at hStep₁
    | true => rfl
  rw [notificationSignalChecked_eq_notificationSignal_when_allowed ctx notificationId signaler badge s₁ hFlow] at hStep₁
  rw [notificationSignalChecked_eq_notificationSignal_when_allowed ctx notificationId signaler badge s₂ hFlow] at hStep₂
  exact notificationSignal_preserves_lowEquivalent ctx observer notificationId badge
    s₁ s₂ s₁' s₂' hLow hNtfnHigh hCoherent hWaiterDomain₁ hWaiterDomain₂ hObjInv₁ hObjInv₂ hStep₁ hStep₂

/-- R5-A/M-01: cspaceCopyChecked NI — projection-based (internalized).
Replaces the prior hypothesis-accepting version. -/
private theorem cspaceCopyChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hProjection : ∀ t t', cspaceCopy src dst t = .ok ((), t') →
        projectState ctx observer t' = projectState ctx observer t)
    (hStep₁ : cspaceCopyChecked ctx src dst s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceCopyChecked ctx src dst s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow := enforcementSoundness_cspaceCopyChecked ctx src dst s₁ s₁' hStep₁
  rw [cspaceCopyChecked_eq_cspaceCopy_when_allowed ctx src dst s₁ hFlow] at hStep₁
  rw [cspaceCopyChecked_eq_cspaceCopy_when_allowed ctx src dst s₂ hFlow] at hStep₂
  unfold lowEquivalent; rw [hProjection s₁ s₁' hStep₁, hProjection s₂ s₂' hStep₂]; exact hLow

/-- R5-A/M-01: cspaceMoveChecked NI — projection-based (internalized).
Replaces the prior hypothesis-accepting version. -/
theorem cspaceMoveChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hProjection : ∀ t t', cspaceMove src dst t = .ok ((), t') →
        projectState ctx observer t' = projectState ctx observer t)
    (hStep₁ : cspaceMoveChecked ctx src dst s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceMoveChecked ctx src dst s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow := enforcementSoundness_cspaceMoveChecked ctx src dst s₁ s₁' hStep₁
  rw [cspaceMoveChecked_eq_cspaceMove_when_allowed ctx src dst s₁ hFlow] at hStep₁
  rw [cspaceMoveChecked_eq_cspaceMove_when_allowed ctx src dst s₂ hFlow] at hStep₂
  unfold lowEquivalent; rw [hProjection s₁ s₁' hStep₁, hProjection s₂ s₂' hStep₂]; exact hLow

-- ============================================================================
-- WS-H9: Scheduler NI proofs (Part A)
-- ============================================================================

/-- WS-H9: setCurrentThread to a non-observable thread preserves projection.
The proof uses the fact that setCurrentThread only modifies scheduler.current,
and if both the old and new current thread are non-observable, projectCurrent
returns none in both cases. -/
theorem setCurrentThread_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (tid : Option SeLe4n.ThreadId) (st st' : SystemState)
    (hTidHigh : ∀ t, tid = some t → threadObservable ctx observer t = false)
    (hCurrentHigh : ∀ t, st.scheduler.current = some t → threadObservable ctx observer t = false)
    (hStep : setCurrentThread tid st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold setCurrentThread at hStep
  have hEq : st' = { st with scheduler := { st.scheduler with current := tid } } := by
    simp only [Except.ok.injEq, Prod.mk.injEq] at hStep; exact hStep.2.symm
  subst hEq
  simp only [projectState]; congr 1
  · -- projectCurrent: both return none since non-observable
    simp only [projectCurrent]
    cases hCur : st.scheduler.current with
    | none =>
      cases hTid : tid with
      | none => rfl
      | some t => simp [hTidHigh t hTid]
    | some t =>
      have := hCurrentHigh t hCur; simp [this]
      cases hTid : tid with
      | none => rfl
      | some t' => simp [hTidHigh t' hTid]
  · -- machineRegs: both return none since non-observable
    simp only [projectMachineRegs]
    cases hCur : st.scheduler.current with
    | none =>
      cases hTid : tid with
      | none => rfl
      | some t => simp [hTidHigh t hTid]
    | some t =>
      have := hCurrentHigh t hCur; simp [this]
      cases hTid : tid with
      | none => rfl
      | some t' => simp [hTidHigh t' hTid]

/-- WS-H12b: Removing a non-observable thread from the run queue preserves projection.
The `RunQueue.remove` operation only drops the given thread; since it's non-observable,
the filtered `projectRunnable` list is unchanged. -/
private theorem remove_rq_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (hTidHigh : threadObservable ctx observer tid = false) :
    projectState ctx observer
        { st with scheduler := { st.scheduler with
            runQueue := st.scheduler.runQueue.remove tid } }
      = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · simp only [projectRunnable, SchedulerState.runnable, RunQueue.toList_filter_remove_neg _ _ _ hTidHigh]

/-- WS-H12b: Inserting a non-observable thread into the run queue preserves projection,
provided the thread was not already in the queue. -/
private theorem insert_rq_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId) (prio : Priority)
    (hTidHigh : threadObservable ctx observer tid = false)
    (hNotMem : ¬(tid ∈ st.scheduler.runQueue)) :
    projectState ctx observer
        { st with scheduler := { st.scheduler with
            runQueue := st.scheduler.runQueue.insert tid prio } }
      = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · simp only [projectRunnable, SchedulerState.runnable, RunQueue.toList_filter_insert_neg _ _ _ _ hTidHigh hNotMem]


/-- WS-H12c: saveOutgoingContext produces a state whose non-objects, non-scheduler
fields are identical to the original. -/
private theorem saveOutgoingContext_machine (st : SystemState) :
    (saveOutgoingContext st).machine = st.machine := by
  simp only [saveOutgoingContext]
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases h : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some obj => cases obj <;> simp_all

private theorem saveOutgoingContext_services (st : SystemState) :
    (saveOutgoingContext st).services = st.services := by
  simp only [saveOutgoingContext]
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases h : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some obj => cases obj <;> simp_all

private theorem saveOutgoingContext_irqHandlers (st : SystemState) :
    (saveOutgoingContext st).irqHandlers = st.irqHandlers := by
  simp only [saveOutgoingContext]
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases h : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some obj => cases obj <;> simp_all

private theorem saveOutgoingContext_objectIndex (st : SystemState) :
    (saveOutgoingContext st).objectIndex = st.objectIndex := by
  simp only [saveOutgoingContext]
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases h : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some obj => cases obj <;> simp_all

/-- WS-H12c: saveOutgoingContext preserves projectObjects because
projectKernelObject strips registerContext from TCBs. -/
private theorem saveOutgoingContext_preserves_projectObjects
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) (oid : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt) :
    projectObjects ctx observer (saveOutgoingContext st) oid =
    projectObjects ctx observer st oid := by
  simp only [projectObjects]
  split
  · next hObs =>
      simp only [saveOutgoingContext]
      cases hCur : st.scheduler.current with
      | none => rfl
      | some outTid =>
          cases hOut : st.objects[outTid.toObjId]? with
          | none => simp_all
          | some outObj =>
              cases outObj with
              | tcb outTcb =>
                  simp only [hOut, Option.map]
                  simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
                  by_cases hEq : outTid.toObjId == oid
                  · simp only [hEq, ↓reduceIte, projectKernelObject]
                    have hEq' := beq_iff_eq.mp hEq
                    subst hEq'
                    have : st.objects.get? outTid.toObjId = st.objects[outTid.toObjId]? := (RHTable_getElem?_eq_get? st.objects outTid.toObjId).symm
                    rw [this]; simp only [hOut]
                  · simp [hEq]
              | endpoint _ => simp_all
              | notification _ => simp_all
              | cnode _ => simp_all
              | vspaceRoot _ => simp_all
              | untyped _ => simp_all
  · rfl

/-- WS-H12c: saveOutgoingContext preserves the information-flow projection.
The context save only modifies `registerContext` in one TCB. Since
`projectKernelObject` strips `registerContext` (replacing it with `default`),
this does not change the projected objects. -/
private theorem saveOutgoingContext_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (saveOutgoingContext st) = projectState ctx observer st := by
  simp only [saveOutgoingContext]
  cases hCur : st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases hOut : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              simp only [hOut]
              -- Now: projectState ctx observer { st with objects := st.objects.insert ... } = projectState ctx observer st
              simp only [projectState]
              congr 1
              · -- objects field
                exact funext (fun oid => by
                  simp only [projectObjects]
                  split
                  · simp only [Option.map]
                    simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
                    by_cases hEq : outTid.toObjId == oid
                    · simp only [hEq, ↓reduceIte, projectKernelObject]
                      have hEq' := beq_iff_eq.mp hEq
                      subst hEq'; rw [← RHTable_getElem?_eq_get?]; simp only [hOut]
                    · simp [hEq]
                  · rfl)
          | endpoint _ => simp_all
          | notification _ => simp_all
          | cnode _ => simp_all
          | vspaceRoot _ => simp_all
          | untyped _ => simp_all

/-- WS-H12c: restoreIncomingContext preserves the information-flow projection
when the current thread is non-observable. -/
private theorem restoreIncomingContext_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) (tid : SeLe4n.ThreadId)
    (hCurrentHigh : ∀ t, st.scheduler.current = some t → threadObservable ctx observer t = false) :
    projectState ctx observer (restoreIncomingContext st tid) = projectState ctx observer st := by
  simp only [restoreIncomingContext]
  cases hTcb : st.objects[tid.toObjId]? with
  | none => simp_all
  | some obj =>
      cases obj with
      | tcb inTcb =>
          simp only []
          -- Goal: projectState ctx observer { st with machine := { st.machine with regs := inTcb.registerContext } } = projectState ctx observer st
          -- Only machine.regs changes; all other projection fields are unchanged
          simp only [projectState]
          congr 1
          · -- machineRegs: current is non-observable, so regs projected as none regardless
            simp only [projectMachineRegs]
            cases hCur : st.scheduler.current with
            | none => rfl
            | some t => simp [hCurrentHigh t hCur]
      | endpoint _ => simp_all
      | notification _ => simp_all
      | cnode _ => simp_all
      | vspaceRoot _ => simp_all
      | untyped _ => simp_all

/-- WS-H12c: projectObjects depends only on the objects field. -/
private theorem projectObjects_ext_objects
    (ctx : LabelingContext) (observer : IfObserver) (s₁ s₂ : SystemState)
    (hObjs : s₁.objects = s₂.objects) :
    (fun oid => projectObjects ctx observer s₁ oid) =
    (fun oid => projectObjects ctx observer s₂ oid) := by
  ext oid; simp only [projectObjects, hObjs]

/-- WS-H12c: saveOutgoingContext with a scheduler override preserves projection
relative to the same scheduler override on the original state. -/
private theorem saveOutgoingContext_with_sched_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (sched : SchedulerState)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer { (saveOutgoingContext st) with scheduler := sched }
    = projectState ctx observer { st with scheduler := sched } := by
  simp only [saveOutgoingContext]
  cases hCur : st.scheduler.current with
  | none => rfl
  | some outTid =>
      cases hOut : st.objects[outTid.toObjId]? with
      | none => simp_all
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              simp only [hOut]
              -- Goal: projectState ctx observer { { st with objects := st.objects.insert ... } with scheduler := sched }
              --     = projectState ctx observer { st with scheduler := sched }
              -- The LHS has objects changed, everything else (incl. scheduler override) same
              simp only [projectState]
              congr 1
              · -- objects field: same proof as saveOutgoingContext_preserves_projection
                exact funext (fun oid => by
                  simp only [projectObjects]
                  split
                  · simp only [Option.map]
                    simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
                    by_cases hEq : outTid.toObjId == oid
                    · simp only [hEq, ↓reduceIte, projectKernelObject]
                      have hEq' := beq_iff_eq.mp hEq
                      subst hEq'; rw [← RHTable_getElem?_eq_get?]; simp only [hOut]
                    · simp [hEq]
                  · rfl)
          | endpoint _ => simp_all
          | notification _ => simp_all
          | cnode _ => simp_all
          | vspaceRoot _ => simp_all
          | untyped _ => simp_all

/-- WS-H9/H12c: schedule when all schedulable threads are non-observable preserves projection.
schedule = chooseThread >> save >> dequeue >> restore >> setCurrentThread.
Context save/restore and dequeue preserve the projection. -/
theorem schedule_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hCurrentHigh : ∀ t, st.scheduler.current = some t → threadObservable ctx observer t = false)
    (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable → threadObservable ctx observer tid = false)
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pair =>
    simp only [hChoose] at hStep
    rcases pair with ⟨next, stC⟩
    have hPres := chooseThread_preserves_state st stC next hChoose
    cases next with
    | none =>
      rw [hPres] at hStep
      exact (setCurrentThread_preserves_projection ctx observer none (saveOutgoingContext st) st'
        (fun _ h => by cases h)
        (fun t h => by rw [saveOutgoingContext_scheduler] at h; exact hCurrentHigh t h)
        hStep).trans (saveOutgoingContext_preserves_projection ctx observer st hObjInv)
    | some tid =>
      rw [hPres] at hStep
      cases hObj : st.objects[tid.toObjId]? with
      | none => simp [hObj] at hStep
      | some obj =>
        cases obj with
        | tcb tcb =>
          simp only [hObj] at hStep
          split at hStep
          · next hCond =>
            have hTidHigh : threadObservable ctx observer tid = false :=
              hAllRunnable tid ((RunQueue.mem_toList_iff_mem _ tid).mpr hCond.1)
            have hSavedSched : (saveOutgoingContext st).scheduler = st.scheduler :=
              saveOutgoingContext_scheduler st
            let stSaved := saveOutgoingContext st
            let stDequeued := { stSaved with scheduler :=
                { stSaved.scheduler with runQueue := stSaved.scheduler.runQueue.remove tid } }
            let stRestored := restoreIncomingContext stDequeued tid
            have hSetProj := setCurrentThread_preserves_projection ctx observer (some tid) stRestored st'
              (fun t h => by cases h; exact hTidHigh)
              (fun t hc => by
                simp only [stRestored, restoreIncomingContext_scheduler, stDequeued] at hc
                rw [hSavedSched] at hc
                exact hCurrentHigh t hc)
              hStep
            have hRestoreProj := restoreIncomingContext_preserves_projection ctx observer stDequeued tid
              (fun t h => by
                simp only [stDequeued] at h
                rw [hSavedSched] at h
                exact hCurrentHigh t h)
            have hDeqProj : projectState ctx observer stDequeued = projectState ctx observer st := by
              have hDeqEq : stDequeued = { saveOutgoingContext st with scheduler :=
                  { st.scheduler with runQueue := st.scheduler.runQueue.remove tid } } := by
                simp only [stDequeued, stSaved, hSavedSched]
              rw [hDeqEq]
              exact (saveOutgoingContext_with_sched_preserves_projection ctx observer st _ hObjInv).trans
                (remove_rq_preserves_projection ctx observer st tid hTidHigh)
            exact hSetProj.trans (hRestoreProj.trans hDeqProj)
          · simp at hStep
        | _ => simp [hObj] at hStep

/-- WS-H9/H12b: switchDomain preserves low-equivalence (deterministic on scheduler fields).
switchDomain only modifies scheduler fields (current, activeDomain, domainTimeRemaining,
domainScheduleIndex) and optionally re-enqueues a non-observable current thread.
All computations depend only on fields that are in the observable projection
(domainSchedule, domainScheduleIndex), which are identical in low-equivalent states.
WS-H12b: requires current threads to be non-observable so the re-enqueue
does not affect the projected runnable list. -/
theorem switchDomain_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCurrentHigh₁ : ∀ t, s₁.scheduler.current = some t → threadObservable ctx observer t = false)
    (hCurrentHigh₂ : ∀ t, s₂.scheduler.current = some t → threadObservable ctx observer t = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : switchDomain s₁ = .ok ((), s₁'))
    (hStep₂ : switchDomain s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold switchDomain at hStep₁ hStep₂
  unfold lowEquivalent at hLow ⊢
  have hDomSched : s₁.scheduler.domainSchedule = s₂.scheduler.domainSchedule := by
    have := congrArg ObservableState.domainSchedule hLow
    simp only [projectState, projectDomainSchedule] at this; exact this
  have hDomIdx : s₁.scheduler.domainScheduleIndex = s₂.scheduler.domainScheduleIndex := by
    have := congrArg ObservableState.domainScheduleIndex hLow
    simp only [projectState, projectDomainScheduleIndex] at this; exact this
  -- Both sides compute the same match/lookup because scheduler fields are identical
  cases hSched₁ : s₁.scheduler.domainSchedule with
  | nil =>
    have hSched₂ : s₂.scheduler.domainSchedule = [] := by rw [← hDomSched]; exact hSched₁
    simp only [hSched₁] at hStep₁; simp only [hSched₂] at hStep₂
    simp only [Except.ok.injEq, Prod.mk.injEq] at hStep₁ hStep₂
    rw [hStep₁.2.symm, hStep₂.2.symm]; exact hLow
  | cons entry rest =>
    have hSched₂ : s₂.scheduler.domainSchedule = entry :: rest := by rw [← hDomSched]; exact hSched₁
    simp only [hSched₁] at hStep₁; simp only [hSched₂] at hStep₂
    rw [← hDomIdx] at hStep₂
    cases hEntry : (entry :: rest)[
        (s₁.scheduler.domainScheduleIndex + 1) % (entry :: rest).length]? with
    | none =>
      simp only [hEntry, Except.ok.injEq, Prod.mk.injEq] at hStep₁ hStep₂
      rw [hStep₁.2.symm, hStep₂.2.symm]; exact hLow
    | some ent =>
      simp only [hEntry, Except.ok.injEq, Prod.mk.injEq] at hStep₁ hStep₂
      have hEq₁ := hStep₁.2.symm; have hEq₂ := hStep₂.2.symm
      subst hEq₁; subst hEq₂
      -- WS-H12b: Helper to reduce the match-based runQueue to the original runQueue
      -- in the filtered (projected) list. Non-observable current thread's insert is invisible.
      have rq_filter_reduce : ∀ (s : SystemState),
          (∀ t, s.scheduler.current = some t → threadObservable ctx observer t = false) →
          (match s.scheduler.current with
            | none => s.scheduler.runQueue
            | some tid => match s.objects[tid.toObjId]? with
              | some (KernelObject.tcb tcb) => s.scheduler.runQueue.insert tid tcb.priority
              | _ => s.scheduler.runQueue).toList.filter (threadObservable ctx observer)
          = s.scheduler.runQueue.toList.filter (threadObservable ctx observer) := by
        intro s hCurH
        split
        · -- current = none
          rfl
        · -- current = some tid, split on objects lookup
          next tid hCur =>
          have hH := hCurH tid hCur
          split
          · -- objects = some (.tcb tcb)
            next tcb _ => exact RunQueue.toList_filter_insert_neg' _ _ _ _ hH
          · -- objects = not tcb (catch-all)
            rfl
      -- U-M39: Rewrite past saveOutgoingContext using projection preservation
      rw [saveOutgoingContext_with_sched_preserves_projection ctx observer s₁ _ hObjInv₁,
          saveOutgoingContext_with_sched_preserves_projection ctx observer s₂ _ hObjInv₂]
      simp only [projectState]; congr 1
      · exact congrArg ObservableState.objects hLow
      · -- WS-H12b: runnable field uses rq_filter_reduce
        simp only [projectRunnable, SchedulerState.runnable]
        have h₁ := rq_filter_reduce s₁ hCurrentHigh₁
        have h₂ := rq_filter_reduce s₂ hCurrentHigh₂
        have hBase := congrArg ObservableState.runnable hLow
        simp only [projectState, projectRunnable, SchedulerState.runnable] at hBase
        exact h₁.trans (hBase.trans h₂.symm)
      all_goals first
        | exact congrArg ObservableState.services hLow
        | exact congrArg ObservableState.irqHandlers hLow
        | exact congrArg ObservableState.objectIndex hLow
        | exact congrArg ObservableState.machineRegs hLow
        | exact congrArg ObservableState.memory hLow
        | rfl

-- ============================================================================
-- WS-H9: VSpace NI proofs (Part D)
-- ============================================================================

/-- WS-H9: vspaceMapPage at a non-observable VSpace root preserves projection. -/
theorem vspaceMapPage_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (st st' : SystemState)
    (hRootHigh : ∀ rootId root, Architecture.resolveAsidRoot st asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hObjInv : st.objects.invExt)
    (hStep : Architecture.vspaceMapPage asid vaddr paddr default st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold Architecture.vspaceMapPage at hStep
  cases hResolve : Architecture.resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
    rcases pair with ⟨rootId, root⟩
    simp only [hResolve] at hStep
    simp only [PagePermissions.default_wxCompliant, Bool.not_true] at hStep
    cases hMap : root.mapPage vaddr paddr default with
    | none => simp [hMap] at hStep
    | some root' =>
      simp only [hMap] at hStep
      have hHigh := hRootHigh rootId root hResolve
      exact storeObject_preserves_projection ctx observer st st' rootId _ hHigh hObjInv hStep

/-- WS-H9: vspaceMapPage preserves low-equivalence. -/
theorem vspaceMapPage_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hRootHigh₁ : ∀ rootId root, Architecture.resolveAsidRoot s₁ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hRootHigh₂ : ∀ rootId root, Architecture.resolveAsidRoot s₂ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : Architecture.vspaceMapPage asid vaddr paddr default s₁ = .ok ((), s₁'))
    (hStep₂ : Architecture.vspaceMapPage asid vaddr paddr default s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    vspaceMapPage_preserves_projection ctx observer asid vaddr paddr s₁ s₁' hRootHigh₁ hObjInv₁ hStep₁,
    vspaceMapPage_preserves_projection ctx observer asid vaddr paddr s₂ s₂' hRootHigh₂ hObjInv₂ hStep₂]
  exact hLow

/-- WS-H9: vspaceUnmapPage at a non-observable VSpace root preserves projection. -/
theorem vspaceUnmapPage_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (hRootHigh : ∀ rootId root, Architecture.resolveAsidRoot st asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hObjInv : st.objects.invExt)
    (hStep : Architecture.vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold Architecture.vspaceUnmapPage at hStep
  cases hResolve : Architecture.resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
    rcases pair with ⟨rootId, root⟩
    simp only [hResolve] at hStep
    cases hUnmap : root.unmapPage vaddr with
    | none => simp [hUnmap] at hStep
    | some root' =>
      simp only [hUnmap] at hStep
      have hHigh := hRootHigh rootId root hResolve
      exact storeObject_preserves_projection ctx observer st st' rootId _ hHigh hObjInv hStep

/-- WS-H9: vspaceUnmapPage preserves low-equivalence. -/
theorem vspaceUnmapPage_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hRootHigh₁ : ∀ rootId root, Architecture.resolveAsidRoot s₁ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hRootHigh₂ : ∀ rootId root, Architecture.resolveAsidRoot s₂ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : Architecture.vspaceUnmapPage asid vaddr s₁ = .ok ((), s₁'))
    (hStep₂ : Architecture.vspaceUnmapPage asid vaddr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    vspaceUnmapPage_preserves_projection ctx observer asid vaddr s₁ s₁' hRootHigh₁ hObjInv₁ hStep₁,
    vspaceUnmapPage_preserves_projection ctx observer asid vaddr s₂ s₂' hRootHigh₂ hObjInv₂ hStep₂]
  exact hLow

/-- WS-H9: vspaceLookup is a read-only operation — it does not modify state. -/
theorem vspaceLookup_preserves_state
    (st : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (st' : SystemState)
    (hStep : Architecture.vspaceLookup asid vaddr st = .ok (paddr, st')) :
    st' = st := by
  unfold Architecture.vspaceLookup at hStep
  cases hResolve : Architecture.resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
    rcases pair with ⟨_, root⟩
    simp only [hResolve] at hStep
    cases hLookup : root.lookupAddr vaddr with
    | none => simp [hLookup] at hStep
    | some p =>
      simp only [hLookup, Except.ok.injEq, Prod.mk.injEq] at hStep
      exact hStep.2.symm

-- WS-H9: vspaceLookup preserves low-equivalence (trivially, as read-only).
/-- WS-I2/R-16: VSpace map preserves low-equivalence under optional memory
ownership projection when the mapped physical address is non-observable. The
operation updates only VSpace metadata, not machine memory, so projection
preservation follows from the base theorem. -/
theorem vspaceMapPage_preserves_lowEquivalent_memoryOwnedHigh
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (_hOwnerHigh : ∀ mo dom,
      ctx.memoryOwnership = some mo →
      mo.regionOwner paddr = some dom →
      securityFlowsTo (mo.domainLabelOf dom) observer.clearance = false)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hRootHigh₁ : ∀ rootId root, Architecture.resolveAsidRoot s₁ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hRootHigh₂ : ∀ rootId root, Architecture.resolveAsidRoot s₂ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : Architecture.vspaceMapPage asid vaddr paddr default s₁ = .ok ((), s₁'))
    (hStep₂ : Architecture.vspaceMapPage asid vaddr paddr default s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  exact vspaceMapPage_preserves_lowEquivalent ctx observer asid vaddr paddr
    s₁ s₂ s₁' s₂' hLow hRootHigh₁ hRootHigh₂ hObjInv₁ hObjInv₂ hStep₁ hStep₂

/-- WS-I2/R-16: VSpace unmap preserves low-equivalence under optional memory
ownership projection. Unmapping mutates VSpace metadata only. -/
theorem vspaceUnmapPage_preserves_lowEquivalent_memoryOwnedHigh
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (_hOwnerHigh : ∀ mo paddr dom,
      ctx.memoryOwnership = some mo →
      mo.regionOwner paddr = some dom →
      securityFlowsTo (mo.domainLabelOf dom) observer.clearance = false)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hRootHigh₁ : ∀ rootId root, Architecture.resolveAsidRoot s₁ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hRootHigh₂ : ∀ rootId root, Architecture.resolveAsidRoot s₂ asid = some (rootId, root) →
        objectObservable ctx observer rootId = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : Architecture.vspaceUnmapPage asid vaddr s₁ = .ok ((), s₁'))
    (hStep₂ : Architecture.vspaceUnmapPage asid vaddr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  exact vspaceUnmapPage_preserves_lowEquivalent ctx observer asid vaddr
    s₁ s₂ s₁' s₂' hLow hRootHigh₁ hRootHigh₂ hObjInv₁ hObjInv₂ hStep₁ hStep₂

theorem vspaceLookup_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (s₁ s₂ s₁' s₂' : SystemState) (p₁ p₂ : SeLe4n.PAddr)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : Architecture.vspaceLookup asid vaddr s₁ = .ok (p₁, s₁'))
    (hStep₂ : Architecture.vspaceLookup asid vaddr s₂ = .ok (p₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have h₁ := vspaceLookup_preserves_state s₁ asid vaddr p₁ s₁' hStep₁
  have h₂ := vspaceLookup_preserves_state s₂ asid vaddr p₂ s₂' hStep₂
  subst h₁; subst h₂; exact hLow

-- ============================================================================
-- WS-H9: CSpace NI proofs (Part C)
-- ============================================================================

/-- WS-H9: storeCapabilityRef preserves projection (modifies only lifecycle). -/
theorem storeCapabilityRef_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (ref : SlotRef) (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeCapabilityRef at hStep
  simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
  have hEq := hStep.2.symm; subst hEq
  simp only [projectState]; congr 1

/-- Core: cspaceDeleteSlotCore at a non-observable CNode preserves projection. -/
theorem cspaceDeleteSlotCore_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (addr : CSpaceAddr) (st st' : SystemState)
    (hAddrHigh : objectObservable ctx observer addr.cnode = false)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cspaceDeleteSlotCore at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | cnode cn =>
      simp only [hObj] at hStep
      cases hStore : storeObject addr.cnode (.cnode (cn.remove addr.slot)) st with
      | error e => simp [hStore] at hStep
      | ok pair₁ =>
        simp only [hStore] at hStep
        cases hRef : storeCapabilityRef addr none pair₁.2 with
        | error e => simp [hRef] at hStep
        | ok pair₂ =>
          simp only [hRef] at hStep; cases hStep
          -- detachSlotFromCdt only modifies CDT (not in projection)
          have hDetach : projectState ctx observer (SystemState.detachSlotFromCdt pair₂.2 addr) =
              projectState ctx observer pair₂.2 := by
            simp only [projectState, SystemState.detachSlotFromCdt]
            split
            · rfl
            · congr 1
          rw [hDetach,
              storeCapabilityRef_preserves_projection ctx observer pair₁.2 pair₂.2 addr none hRef,
              storeObject_preserves_projection ctx observer st pair₁.2 addr.cnode _ hAddrHigh hObjInv hStore]

/-- WS-H9: cspaceDeleteSlot at a non-observable CNode preserves projection (guarded wrapper). -/
theorem cspaceDeleteSlot_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (addr : CSpaceAddr) (st st' : SystemState)
    (hAddrHigh : objectObservable ctx observer addr.cnode = false)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cspaceDeleteSlot at hStep
  split at hStep
  · simp at hStep
  · exact cspaceDeleteSlotCore_preserves_projection ctx observer addr st st' hAddrHigh hObjInv hStep

/-- WS-H9: cspaceDeleteSlot preserves low-equivalence. -/
private theorem cspaceDeleteSlot_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (addr : CSpaceAddr) (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hAddrHigh : objectObservable ctx observer addr.cnode = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : cspaceDeleteSlot addr s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceDeleteSlot addr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    cspaceDeleteSlot_preserves_projection ctx observer addr s₁ s₁' hAddrHigh hObjInv₁ hStep₁,
    cspaceDeleteSlot_preserves_projection ctx observer addr s₂ s₂' hAddrHigh hObjInv₂ hStep₂]
  exact hLow

/-- cspaceRevoke at a non-observable CNode preserves projection.
Extracted as a standalone theorem for compositional reasoning in
`lifecycleRevokeDeleteRetype_preserves_projection`. -/
theorem cspaceRevoke_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (addr : CSpaceAddr) (st st' : SystemState)
    (hAddrHigh : objectObservable ctx observer addr.cnode = false)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cspaceRevoke at hStep
  cases hL : cspaceLookupSlot addr st with
  | error e => simp [hL] at hStep
  | ok p =>
    rcases p with ⟨par, stL⟩
    have hEqL : stL = st := cspaceLookupSlot_preserves_state st stL addr par hL
    subst stL
    cases hC : st.objects[addr.cnode]? with
    | none => simp [hL, hC] at hStep
    | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hL, hC] at hStep
      | cnode cn =>
        simp [hL, hC, storeObject] at hStep; cases hStep
        rw [revokeAndClearRefsState_preserves_projectState]
        simp only [projectState]; congr 1
        · funext oid; by_cases hObs : objectObservable ctx observer oid
          · simp [projectObjects, hObs]
            have hNe : oid ≠ addr.cnode := by
              intro hEq; subst hEq; simp [hAddrHigh] at hObs
            simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]; simp [Ne.symm hNe]
          · simp [projectObjects, hObs]
        · simp only [projectObjectIndex]
          split
          · rfl
          · rw [List.filter_cons]; simp [hAddrHigh]

/-- WS-H9: A state modification that only changes CDT fields preserves projection. -/
private theorem cdt_only_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState)
    (st' : SystemState)
    (hObjects : st'.objects = st.objects)
    (hScheduler : st'.scheduler = st.scheduler)
    (hServices : st'.services = st.services)
    (hIrq : st'.irqHandlers = st.irqHandlers)
    (hObjIdx : st'.objectIndex = st.objectIndex)
    (hMachine : st'.machine = st.machine) :
    projectState ctx observer st' = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · funext oid; simp only [projectObjects, hObjects]
  · simp [projectRunnable, hScheduler]
  · simp [projectCurrent, hScheduler]
  · funext sid; simp only [projectServicePresence, lookupService, hServices]
  · simp [projectActiveDomain, hScheduler]
  · funext irq; simp only [projectIrqHandlers, hIrq]
  · simp only [projectObjectIndex, hObjIdx]
  · simp [projectDomainTimeRemaining, hScheduler]
  · simp [projectDomainSchedule, hScheduler]
  · simp [projectDomainScheduleIndex, hScheduler]
  · simp [projectMachineRegs, hScheduler, hMachine]
  · -- R5-C.1: memory
    exact projectMemory_eq_of_memory_eq ctx observer st' st (by rw [hMachine])

/-- WS-H9: ensureCdtNodeForSlot preserves projection (modifies only CDT). -/
private theorem ensureCdtNodeForSlot_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (ref : SlotRef) :
    projectState ctx observer (SystemState.ensureCdtNodeForSlot st ref).2 =
      projectState ctx observer st := by
  unfold SystemState.ensureCdtNodeForSlot
  cases st.cdtSlotNode[ref]? with
  | some _ => rfl
  | none => exact cdt_only_preserves_projection ctx observer st _ rfl rfl rfl rfl rfl rfl

/-- WS-H9: attachSlotToCdtNode preserves projection (modifies only CDT). -/
private theorem attachSlotToCdtNode_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (ref : SlotRef) (node : CdtNodeId) :
    projectState ctx observer (SystemState.attachSlotToCdtNode st ref node) =
      projectState ctx observer st := by
  exact cdt_only_preserves_projection ctx observer st _
    (SystemState.attachSlotToCdtNode_objects_eq st ref node) rfl rfl rfl rfl rfl

/-- WS-H9: cspaceInsertSlot at non-observable CNode preserves projection. -/
private theorem cspaceInsertSlot_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (dst : CSpaceAddr) (cap : Capability)
    (st st' : SystemState)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceInsertSlot dst cap st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · funext oid; by_cases hObs : objectObservable ctx observer oid
    · simp [projectObjects, hObs]
      by_cases hEq : oid = dst.cnode
      · subst hEq; simp [hDstHigh] at hObs
      · exact congrArg (Option.map (projectKernelObject ctx observer))
          (cspaceInsertSlot_preserves_objects_ne st st' dst cap oid hEq hObjInv hStep)
    · simp [projectObjects, hObs]
  · simp [projectRunnable, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep]
  · simp [projectCurrent, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep]
  · funext sid; simp only [projectServicePresence, lookupService,
      cspaceInsertSlot_preserves_services st st' dst cap hStep]
  · simp [projectActiveDomain, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep]
  · funext irq; simp only [projectIrqHandlers,
      cspaceInsertSlot_preserves_irqHandlers st st' dst cap hStep]
  · exact cspaceInsertSlot_preserves_projectObjectIndex st st' dst cap hDstHigh hStep
  · simp [projectDomainTimeRemaining, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep]
  · simp [projectDomainSchedule, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep]
  · simp [projectDomainScheduleIndex, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep]
  · simp [projectMachineRegs, cspaceInsertSlot_preserves_scheduler st st' dst cap hStep,
      cspaceInsertSlot_preserves_machine st st' dst cap hStep]
  · -- R5-C.1: memory
    exact projectMemory_eq_of_memory_eq ctx observer st' st
      (by rw [cspaceInsertSlot_preserves_machine st st' dst cap hStep])

/-- WS-H9: cspaceCopy at non-observable CNodes preserves projection.
cspaceCopy = cspaceLookupSlot (read-only) + cspaceInsertSlot (at non-obs dst)
+ ensureCdtNodeForSlot × 2 (CDT only) + CDT.addEdge (CDT only). -/
theorem cspaceCopy_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr) (st st' : SystemState)
    (_hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceCopy src dst st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cspaceCopy at hStep
  cases hLookup : cspaceLookupSlot src st with
  | error e => simp [hLookup] at hStep
  | ok pair =>
    rcases pair with ⟨cap, stL⟩
    have hStEq := cspaceLookupSlot_preserves_state st stL src cap hLookup
    simp only [hLookup] at hStep
    rw [hStEq] at hStep
    cases hInsert : cspaceInsertSlot dst cap st with
    | error e => simp [hInsert] at hStep
    | ok pair₂ =>
      rcases pair₂ with ⟨_, stIns⟩
      simp only [hInsert, Except.ok.injEq, Prod.mk.injEq] at hStep
      have hEq := hStep.2.symm; subst hEq
      have hAddEdge : ∀ stx cdt', projectState ctx observer { stx with cdt := cdt' } =
          projectState ctx observer stx := by
        intro stx _; simp only [projectState]; congr 1
      rw [hAddEdge,
          ensureCdtNodeForSlot_preserves_projection ctx observer _ dst,
          ensureCdtNodeForSlot_preserves_projection ctx observer _ src,
          cspaceInsertSlot_preserves_projection ctx observer dst cap st stIns hDstHigh hObjInv hInsert]

/-- WS-H9: cspaceCopy preserves low-equivalence. -/
private theorem cspaceCopy_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr) (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : cspaceCopy src dst s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceCopy src dst s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    cspaceCopy_preserves_projection ctx observer src dst s₁ s₁' hSrcHigh hDstHigh hObjInv₁ hStep₁,
    cspaceCopy_preserves_projection ctx observer src dst s₂ s₂' hSrcHigh hDstHigh hObjInv₂ hStep₂]
  exact hLow

/-- WS-H9: cspaceMove at non-observable CNodes preserves projection. -/
theorem cspaceMove_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr) (st st' : SystemState)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceMove src dst st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold cspaceMove at hStep
  cases hLookup : cspaceLookupSlot src st with
  | error e => simp [hLookup] at hStep
  | ok pair =>
    rcases pair with ⟨cap, stL⟩
    have hStEq := cspaceLookupSlot_preserves_state st stL src cap hLookup
    simp only [hLookup] at hStep
    rw [hStEq] at hStep
    cases hInsert : cspaceInsertSlot dst cap st with
    | error e => simp [hInsert] at hStep
    | ok pair₂ =>
      rcases pair₂ with ⟨_, stIns⟩
      simp only [hInsert] at hStep
      cases hDelete : cspaceDeleteSlotCore src stIns with
      | error e => simp [hDelete] at hStep
      | ok pair₃ =>
        rcases pair₃ with ⟨_, stDel⟩
        simp only [hDelete] at hStep
        -- Split on srcNode? match (none → stDel, some → attachSlotToCdtNode stDel dst srcNode)
        split at hStep
        · -- none: st' = stDel
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          rw [← hStep.2]
          have hObjInvIns := cspaceInsertSlot_preserves_objects_invExt st stIns dst cap hObjInv hInsert
          rw [cspaceDeleteSlotCore_preserves_projection ctx observer src stIns stDel hSrcHigh hObjInvIns hDelete,
              cspaceInsertSlot_preserves_projection ctx observer dst cap st stIns hDstHigh hObjInv hInsert]
        · -- some srcNode: attachSlotToCdtNode only modifies CDT
          next srcNode =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          rw [← hStep.2]
          have hAttach : ∀ stx nodeId, projectState ctx observer (SystemState.attachSlotToCdtNode stx dst nodeId) =
              projectState ctx observer stx := by
            intro stx _; simp only [projectState, SystemState.attachSlotToCdtNode]; congr 1
          have hObjInvIns := cspaceInsertSlot_preserves_objects_invExt st stIns dst cap hObjInv hInsert
          rw [hAttach,
              cspaceDeleteSlotCore_preserves_projection ctx observer src stIns stDel hSrcHigh hObjInvIns hDelete,
              cspaceInsertSlot_preserves_projection ctx observer dst cap st stIns hDstHigh hObjInv hInsert]

/-- WS-H9: cspaceMove preserves low-equivalence. -/
private theorem cspaceMove_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr) (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : cspaceMove src dst s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceMove src dst s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    cspaceMove_preserves_projection ctx observer src dst s₁ s₁' hSrcHigh hDstHigh hObjInv₁ hStep₁,
    cspaceMove_preserves_projection ctx observer src dst s₂ s₂' hSrcHigh hDstHigh hObjInv₂ hStep₂]
  exact hLow

-- ============================================================================
-- WS-H9: IPC NI proofs (Part B)
-- ============================================================================

/-- WS-H9: storeTcbQueueLinks at a non-observable thread preserves projection.
storeTcbQueueLinks modifies only the TCB's queue link fields via storeObject. -/
theorem storeTcbQueueLinks_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeTcbQueueLinks at hStep
  simp only [tcbWithQueueLinks] at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId
        (.tcb { tcb with queuePrev := prev, queuePPrev := pprev, queueNext := next }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      exact storeObject_preserves_projection ctx observer st pair.2 tid.toObjId _ hTidObjHigh hObjInv hStore

-- ============================================================================
-- U4-A: Queue operation projection preservation
-- ============================================================================

/-- U4-A: endpointQueuePopHead at a non-observable endpoint preserves projection
    when the popped head and next-of-head threads have non-observable TCBs.
    This is the key building block for endpointSendDual/ReceiveDual NI proofs. -/
theorem endpointQueuePopHead_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hHeadObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hNextObjHigh : ∀ nextTid, headTcb.queueNext = some nextTid →
        objectObservable ctx observer nextTid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []
        cases hLookup : lookupTcb st headTid with
        | none => simp
        | some htcb =>
          simp only []
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []
            have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hProjStore := storeObject_preserves_projection ctx observer st pair.2
                endpointId _ hEndpointHigh hObjInv hStore
            cases hNext : htcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨hTidEq, hTcbEq, hStEq⟩
                subst hStEq; subst hTidEq
                rw [storeTcbQueueLinks_preserves_projection ctx observer pair.2 st3
                    headTid none none none hHeadObjHigh hObjInv1 hFinal,
                    hProjStore]
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none
                    (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨hTidEq, hTcbEq, hStEq⟩
                    subst hStEq; subst hTidEq
                    have hNextHigh := hNextObjHigh nextTid (hTcbEq ▸ hNext)
                    have hObjInv2 := storeTcbQueueLinks_preserves_objects_invExt pair.2 st2
                        nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext hObjInv1 hLink
                    rw [storeTcbQueueLinks_preserves_projection ctx observer st2 st3
                        headTid none none none hHeadObjHigh hObjInv2 hFinal,
                        storeTcbQueueLinks_preserves_projection ctx observer
                        pair.2 st2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext
                        hNextHigh hObjInv1 hLink,
                        hProjStore]

/-- U4-A: endpointQueueEnqueue at a non-observable endpoint preserves projection
    when the enqueued thread and current tail thread have non-observable TCBs. -/
theorem endpointQueueEnqueue_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hTailObjHigh : ∀ ep tailTid, st.objects[endpointId]? = some (.endpoint ep) →
        (if isReceiveQ then ep.receiveQ else ep.sendQ).tail = some tailTid →
        objectObservable ctx observer tailTid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
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
                have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair
                    hObjInv hStore
                rw [storeTcbQueueLinks_preserves_projection ctx observer pair.2 st'
                    tid none (some QueuePPrev.endpointHead) none hTidObjHigh hObjInv1 hStep,
                    storeObject_preserves_projection ctx observer st pair.2
                    endpointId _ hEndpointHigh hObjInv hStore]
            | some tailTid =>
              have hTailHigh := hTailObjHigh ep tailTid hObj hTail
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail]
              | some tailTcb =>
                simp only [hLookupTail]
                cases hStore : storeObject endpointId _ st with
                | error e => simp
                | ok pair =>
                  simp only []
                  cases hLink : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev
                      tailTcb.queuePPrev (some tid) with
                  | error e => simp
                  | ok st2 =>
                    simp only []
                    intro hStep
                    have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair
                        hObjInv hStore
                    have hProjStore := storeObject_preserves_projection ctx observer st pair.2
                        endpointId _ hEndpointHigh hObjInv hStore
                    have hObjInv2 := storeTcbQueueLinks_preserves_objects_invExt pair.2 st2
                        tailTid _ _ _ hObjInv1 hLink
                    rw [storeTcbQueueLinks_preserves_projection ctx observer st2 st'
                        tid (some tailTid) (some (QueuePPrev.tcbNext tailTid)) none
                        hTidObjHigh hObjInv2 hStep,
                        storeTcbQueueLinks_preserves_projection ctx observer pair.2 st2
                        tailTid _ _ _ hTailHigh hObjInv1 hLink,
                        hProjStore]

-- ============================================================================
-- U4-A: endpointSendDual projection preservation
-- ============================================================================

/-- U4-A: endpointSendDual at a non-observable endpoint preserves projection.

    Replaces the externalized `hProjection` hypothesis with semantic domain
    isolation hypotheses. The proof composes queue operation projection lemmas
    with TCB state and scheduler preservation.

    The queue domain hypotheses capture the security property that all threads
    interacting through a non-observable endpoint are themselves non-observable. -/
theorem endpointSendDual_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (st st' : SystemState)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hSenderHigh : threadObservable ctx observer sender = false)
    (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hRecvQueueHeadHigh : ∀ ep receiver, st.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.head = some receiver → threadObservable ctx observer receiver = false)
    (hRecvQueueNextHigh : ∀ ep receiver recvTcb nextTid,
        st.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.head = some receiver →
        st.objects[receiver.toObjId]? = some (.tcb recvTcb) →
        recvTcb.queueNext = some nextTid →
        objectObservable ctx observer nextTid.toObjId = false)
    (hSendQueueTailHigh : ∀ ep tailTid, st.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.tail = some tailTid → objectObservable ctx observer tailTid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointSendDual at hStep
  -- Eliminate bounds-check error branches
  simp only [show ¬(msg.registers.size > maxMessageRegisters) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(msg.caps.size > maxExtraCaps) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hRecvHead : ep.receiveQ.head with
      | some _ =>
        -- Path 1: Receiver waiting — PopHead + storeTcbIpcState + ensureRunnable
        simp only [hRecvHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok triple =>
          obtain ⟨receiver, recvTcb, st1⟩ := triple
          simp only [hPop] at hStep
          -- Use existing lemmas to extract receiver identity and TCB
          have hHeadEq : ep.receiveQ.head = some receiver :=
            endpointQueuePopHead_returns_head endpointId true st ep receiver st1 hObj hPop
          have hRecvHigh := hRecvQueueHeadHigh ep receiver hObj hHeadEq
          have hRecvObjHigh := hCoherent receiver hRecvHigh
          have hPreTcb := endpointQueuePopHead_returns_pre_tcb endpointId true st ep
              receiver recvTcb st1 hObj hPop
          have hNextHighForPop : ∀ nextTid, recvTcb.queueNext = some nextTid →
              objectObservable ctx observer nextTid.toObjId = false :=
            fun nextTid hQN => hRecvQueueNextHigh ep receiver recvTcb nextTid hObj
              hHeadEq hPreTcb hQN
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true
              st st1 receiver recvTcb hObjInv hPop
          have hProjPop := endpointQueuePopHead_preserves_projection ctx observer
              endpointId true st st1 receiver recvTcb hEndpointHigh hRecvObjHigh
              hNextHighForPop hObjInv hPop
          cases hTcbStore : storeTcbIpcStateAndMessage st1 receiver .ready (some msg) with
          | error e => simp [hTcbStore] at hStep
          | ok st2 =>
            simp only [hTcbStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hStEq⟩ := hStep; subst hStEq
            rw [ensureRunnable_preserves_projection ctx observer st2 receiver hRecvHigh,
                storeTcbIpcStateAndMessage_preserves_projection ctx observer st1 st2
                receiver _ _ hRecvObjHigh hObjInv1 hTcbStore,
                hProjPop]
      | none =>
        -- Path 2: No receiver — Enqueue sender + storeTcbIpcState + removeRunnable
        simp only [hRecvHead] at hStep
        have hTailHigh : ∀ ep' tailTid, st.objects[endpointId]? = some (.endpoint ep') →
            (if false then ep'.receiveQ else ep'.sendQ).tail = some tailTid →
            objectObservable ctx observer tailTid.toObjId = false := by
          intro ep' tailTid hEp' hTail; simp at hTail
          exact hSendQueueTailHigh ep' tailTid hEp' hTail
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false
              sender st st1 hObjInv hEnq
          have hProjEnq := endpointQueueEnqueue_preserves_projection ctx observer
              endpointId false sender st st1 hEndpointHigh hSenderObjHigh
              hTailHigh hObjInv hEnq
          cases hTcbStore : storeTcbIpcStateAndMessage st1 sender
              (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hTcbStore] at hStep
          | ok st2 =>
            simp only [hTcbStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hStEq⟩ := hStep; subst hStEq
            rw [removeRunnable_preserves_projection ctx observer st2 sender hSenderHigh,
                storeTcbIpcStateAndMessage_preserves_projection ctx observer st1 st2
                sender _ _ hSenderObjHigh hObjInv1 hTcbStore,
                hProjEnq]

/-- U4-B: endpointReceiveDual at a non-observable endpoint preserves projection.

    Two paths:
    * Path 1 (sender waiting): PopHead from sendQ → storeTcbIpcStateAndMessage (sender) →
      [ensureRunnable if send-path] → storeTcbPendingMessage (receiver)
    * Path 2 (no sender): Enqueue receiver on receiveQ → storeTcbIpcState → removeRunnable -/
theorem endpointReceiveDual_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hReceiverHigh : threadObservable ctx observer receiver = false)
    (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hSendQueueHeadHigh : ∀ ep sender, st.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.head = some sender → threadObservable ctx observer sender = false)
    (hSendQueueNextHigh : ∀ ep sender senderTcb nextTid,
        st.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.head = some sender →
        st.objects[sender.toObjId]? = some (.tcb senderTcb) →
        senderTcb.queueNext = some nextTid →
        objectObservable ctx observer nextTid.toObjId = false)
    (hRecvQueueTailHigh : ∀ ep tailTid, st.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.tail = some tailTid → objectObservable ctx observer tailTid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hSendHead : ep.sendQ.head with
      | some _ =>
        -- Path 1: Sender waiting — PopHead + storeTcbIpcStateAndMessage + [ensureRunnable] + storeTcbPendingMessage
        simp only [hSendHead] at hStep
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hPop] at hStep
        | ok triple =>
          obtain ⟨sender, senderTcb, st1⟩ := triple
          simp only [hPop] at hStep
          have hHeadEq : ep.sendQ.head = some sender :=
            endpointQueuePopHead_returns_head endpointId false st ep sender st1 hObj hPop
          have hSenderHigh := hSendQueueHeadHigh ep sender hObj hHeadEq
          have hSenderObjHigh := hCoherent sender hSenderHigh
          have hPreTcb := endpointQueuePopHead_returns_pre_tcb endpointId false st ep
              sender senderTcb st1 hObj hPop
          have hNextHighForPop : ∀ nextTid, senderTcb.queueNext = some nextTid →
              objectObservable ctx observer nextTid.toObjId = false :=
            fun nextTid hQN => hSendQueueNextHigh ep sender senderTcb nextTid hObj
              hHeadEq hPreTcb hQN
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId false
              st st1 sender senderTcb hObjInv hPop
          have hProjPop := endpointQueuePopHead_preserves_projection ctx observer
              endpointId false st st1 sender senderTcb hEndpointHigh hSenderObjHigh
              hNextHighForPop hObjInv hPop
          -- Branch on whether sender was in a Call (if senderWasCall then ...)
          split at hStep
          · -- Call path: sender → blockedOnReply, then deliver message to receiver
            cases hIpc : storeTcbIpcStateAndMessage st1 sender
                (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc] at hStep
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2
                  sender _ _ hObjInv1 hIpc
              have hProjIpc := storeTcbIpcStateAndMessage_preserves_projection ctx observer
                  st1 st2 sender _ _ hSenderObjHigh hObjInv1 hIpc
              cases hPend : storeTcbPendingMessage st2 receiver senderTcb.pendingMessage with
              | error e => simp [hPend] at hStep
              | ok st3 =>
                simp only [hPend] at hStep
                have hStEq := (Prod.mk.inj (Except.ok.inj hStep)).2; subst hStEq
                rw [storeTcbPendingMessage_preserves_projection ctx observer st2 st3
                    receiver _ hReceiverObjHigh hObjInv2 hPend,
                    hProjIpc, hProjPop]
          · -- Send path: sender → ready, ensureRunnable, then deliver message to receiver
            cases hIpc : storeTcbIpcStateAndMessage st1 sender .ready none with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc] at hStep
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2
                  sender _ _ hObjInv1 hIpc
              have hProjIpc := storeTcbIpcStateAndMessage_preserves_projection ctx observer
                  st1 st2 sender _ _ hSenderObjHigh hObjInv1 hIpc
              have hProjEns := ensureRunnable_preserves_projection ctx observer st2 sender hSenderHigh
              have hObjInvEns : (ensureRunnable st2 sender).objects.invExt := by
                rw [ensureRunnable_preserves_objects]; exact hObjInv2
              cases hPend : storeTcbPendingMessage (ensureRunnable st2 sender) receiver
                  senderTcb.pendingMessage with
              | error e => simp [hPend] at hStep
              | ok st3 =>
                simp only [hPend] at hStep
                have hStEq := (Prod.mk.inj (Except.ok.inj hStep)).2; subst hStEq
                rw [storeTcbPendingMessage_preserves_projection ctx observer
                    (ensureRunnable st2 sender) st3 receiver _ hReceiverObjHigh hObjInvEns hPend,
                    hProjEns, hProjIpc, hProjPop]
      | none =>
        -- Path 2: No sender — Enqueue receiver + storeTcbIpcState + removeRunnable
        simp only [hSendHead] at hStep
        have hTailHigh : ∀ ep' tailTid, st.objects[endpointId]? = some (.endpoint ep') →
            (if true then ep'.receiveQ else ep'.sendQ).tail = some tailTid →
            objectObservable ctx observer tailTid.toObjId = false := by
          intro ep' tailTid hEp' hTail; simp at hTail
          exact hRecvQueueTailHigh ep' tailTid hEp' hTail
        cases hEnq : endpointQueueEnqueue endpointId true receiver st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId true
              receiver st st1 hObjInv hEnq
          have hProjEnq := endpointQueueEnqueue_preserves_projection ctx observer
              endpointId true receiver st st1 hEndpointHigh hReceiverObjHigh
              hTailHigh hObjInv hEnq
          cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
          | error e => simp [hIpc] at hStep
          | ok st2 =>
            simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hStEq⟩ := hStep; subst hStEq
            rw [removeRunnable_preserves_projection ctx observer st2 receiver hReceiverHigh,
                storeTcbIpcState_preserves_projection ctx observer st1 st2 receiver _
                hReceiverObjHigh hObjInv1 hIpc,
                hProjEnq]

/-- WS-H9: endpointReply at non-observable target preserves projection. -/
theorem endpointReply_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (st st' : SystemState)
    (hTargetHigh : threadObservable ctx observer target = false)
    (hTargetObjHigh : objectObservable ctx observer target.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointReply at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | blockedOnReply ep replyTarget =>
      -- Resolve ipcState match and storeTcbIpcStateAndMessage in hStep
      cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
      | error e =>
        exfalso; simp only [hIpc, hStore] at hStep
        revert hStep; split <;> split <;> simp
      | ok stMid =>
        have hEq : st' = ensureRunnable stMid target := by
          simp only [hIpc, hStore] at hStep
          revert hStep; split <;> (try split) <;> simp <;> exact Eq.symm
        rw [hEq,
            ensureRunnable_preserves_projection ctx observer stMid target hTargetHigh,
            storeTcbIpcStateAndMessage_preserves_projection ctx observer st stMid target _ _ hTargetObjHigh hObjInv hStore]
    | _ => simp [hIpc] at hStep

/-- WS-H9: endpointReply preserves low-equivalence. -/
theorem endpointReply_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hTargetHigh : threadObservable ctx observer target = false)
    (hTargetObjHigh : objectObservable ctx observer target.toObjId = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : endpointReply replier target msg s₁ = .ok ((), s₁'))
    (hStep₂ : endpointReply replier target msg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    endpointReply_preserves_projection ctx observer replier target msg s₁ s₁' hTargetHigh hTargetObjHigh hObjInv₁ hStep₁,
    endpointReply_preserves_projection ctx observer replier target msg s₂ s₂' hTargetHigh hTargetObjHigh hObjInv₂ hStep₂]
  exact hLow

-- ============================================================================
-- WS-H8/H9: endpointReceiveDualChecked NI bridge + IPC NI completion
-- ============================================================================

/-- U4-C: endpointCall at a non-observable endpoint preserves projection.

    Two paths:
    * Path 1 (receiver waiting on receiveQ): PopHead → storeTcbIpcStateAndMessage (receiver) →
      ensureRunnable (receiver) → storeTcbIpcState (caller to blockedOnReply) → removeRunnable (caller)
    * Path 2 (no receiver): Enqueue caller on sendQ → storeTcbIpcStateAndMessage (caller) →
      removeRunnable (caller) -/
theorem endpointCall_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (st st' : SystemState)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hCallerHigh : threadObservable ctx observer caller = false)
    (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hRecvQueueHeadHigh : ∀ ep receiver, st.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.head = some receiver → threadObservable ctx observer receiver = false)
    (hRecvQueueNextHigh : ∀ ep receiver recvTcb nextTid,
        st.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.head = some receiver →
        st.objects[receiver.toObjId]? = some (.tcb recvTcb) →
        recvTcb.queueNext = some nextTid →
        objectObservable ctx observer nextTid.toObjId = false)
    (hSendQueueTailHigh : ∀ ep tailTid, st.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.tail = some tailTid → objectObservable ctx observer tailTid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointCall at hStep
  -- Eliminate bounds-check error branches
  simp only [show ¬(msg.registers.size > maxMessageRegisters) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(msg.caps.size > maxExtraCaps) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hRecvHead : ep.receiveQ.head with
      | some _ =>
        -- Path 1: Receiver waiting — PopHead + storeTcbIpcStateAndMessage(receiver) +
        -- ensureRunnable(receiver) + storeTcbIpcState(caller) + removeRunnable(caller)
        simp only [hRecvHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok triple =>
          obtain ⟨receiver, _recvTcb, st1⟩ := triple
          simp only [hPop] at hStep
          have hHeadEq : ep.receiveQ.head = some receiver :=
            endpointQueuePopHead_returns_head endpointId true st ep receiver st1 hObj hPop
          have hRecvHigh := hRecvQueueHeadHigh ep receiver hObj hHeadEq
          have hRecvObjHigh := hCoherent receiver hRecvHigh
          have hPreTcb := endpointQueuePopHead_returns_pre_tcb endpointId true st ep
              receiver _recvTcb st1 hObj hPop
          have hNextHighForPop : ∀ nextTid, _recvTcb.queueNext = some nextTid →
              objectObservable ctx observer nextTid.toObjId = false :=
            fun nextTid hQN => hRecvQueueNextHigh ep receiver _recvTcb nextTid hObj
              hHeadEq hPreTcb hQN
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true
              st st1 receiver _recvTcb hObjInv hPop
          have hProjPop := endpointQueuePopHead_preserves_projection ctx observer
              endpointId true st st1 receiver _recvTcb hEndpointHigh hRecvObjHigh
              hNextHighForPop hObjInv hPop
          cases hTcbStore : storeTcbIpcStateAndMessage st1 receiver .ready (some msg) with
          | error e => simp [hTcbStore] at hStep
          | ok st2 =>
            simp only [hTcbStore] at hStep
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2
                receiver _ _ hObjInv1 hTcbStore
            have hProjTcb := storeTcbIpcStateAndMessage_preserves_projection ctx observer
                st1 st2 receiver _ _ hRecvObjHigh hObjInv1 hTcbStore
            have hProjEns := ensureRunnable_preserves_projection ctx observer st2 receiver hRecvHigh
            have hObjInvEns : (ensureRunnable st2 receiver).objects.invExt := by
              rw [ensureRunnable_preserves_objects]; exact hObjInv2
            cases hIpc : storeTcbIpcState (ensureRunnable st2 receiver) caller
                (.blockedOnReply endpointId (some receiver)) with
            | error e => simp [hIpc] at hStep
            | ok st3 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hStEq⟩ := hStep; subst hStEq
              rw [removeRunnable_preserves_projection ctx observer st3 caller hCallerHigh,
                  storeTcbIpcState_preserves_projection ctx observer (ensureRunnable st2 receiver)
                  st3 caller _ hCallerObjHigh hObjInvEns hIpc,
                  hProjEns, hProjTcb, hProjPop]
      | none =>
        -- Path 2: No receiver — Enqueue caller + storeTcbIpcStateAndMessage + removeRunnable
        simp only [hRecvHead] at hStep
        have hTailHigh : ∀ ep' tailTid, st.objects[endpointId]? = some (.endpoint ep') →
            (if false then ep'.receiveQ else ep'.sendQ).tail = some tailTid →
            objectObservable ctx observer tailTid.toObjId = false := by
          intro ep' tailTid hEp' hTail; simp at hTail
          exact hSendQueueTailHigh ep' tailTid hEp' hTail
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false
              caller st st1 hObjInv hEnq
          have hProjEnq := endpointQueueEnqueue_preserves_projection ctx observer
              endpointId false caller st st1 hEndpointHigh hCallerObjHigh
              hTailHigh hObjInv hEnq
          cases hTcbStore : storeTcbIpcStateAndMessage st1 caller
              (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hTcbStore] at hStep
          | ok st2 =>
            simp only [hTcbStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hStEq⟩ := hStep; subst hStEq
            rw [removeRunnable_preserves_projection ctx observer st2 caller hCallerHigh,
                storeTcbIpcStateAndMessage_preserves_projection ctx observer st1 st2
                caller _ _ hCallerObjHigh hObjInv1 hTcbStore,
                hProjEnq]

/-- U4-C: endpointReplyRecv at non-observable targets preserves projection.

    Sequential composition: reply (storeTcbIpcStateAndMessage + ensureRunnable) followed
    by endpointReceiveDual. The reply part modifies only replyTarget's TCB; the endpoint
    and its queues remain unchanged, so queue domain isolation hypotheses transfer. -/
theorem endpointReplyRecv_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (replierReceiver replyTarget : SeLe4n.ThreadId)
    (replyMsg : IpcMessage) (st st' : SystemState)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hReceiverHigh : threadObservable ctx observer replierReceiver = false)
    (hReceiverObjHigh : objectObservable ctx observer replierReceiver.toObjId = false)
    (hReplyTargetHigh : threadObservable ctx observer replyTarget = false)
    (hReplyTargetObjHigh : objectObservable ctx observer replyTarget.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hSendQueueHeadHigh : ∀ ep sender, st.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.head = some sender → threadObservable ctx observer sender = false)
    (hSendQueueNextHigh : ∀ ep sender senderTcb nextTid,
        st.objects[endpointId]? = some (.endpoint ep) →
        ep.sendQ.head = some sender →
        st.objects[sender.toObjId]? = some (.tcb senderTcb) →
        senderTcb.queueNext = some nextTid →
        objectObservable ctx observer nextTid.toObjId = false)
    (hRecvQueueTailHigh : ∀ ep tailTid, st.objects[endpointId]? = some (.endpoint ep) →
        ep.receiveQ.tail = some tailTid → objectObservable ctx observer tailTid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecv endpointId replierReceiver replyTarget replyMsg st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold endpointReplyRecv at hStep
  -- Eliminate bounds-check error branches
  simp only [show ¬(replyMsg.registers.size > maxMessageRegisters) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(replyMsg.caps.size > maxExtraCaps) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    -- Case split on ipcState
    cases hIpc : tcb.ipcState with
    | blockedOnReply ep expectedReplier =>
      cases hStore : storeTcbIpcStateAndMessage st replyTarget .ready (some replyMsg) with
      | error e =>
        exfalso; simp only [hIpc, hStore] at hStep
        revert hStep; split <;> split <;> simp
      | ok stReply =>
        simp only [hIpc, hStore] at hStep
        -- Case-split endpointReceiveDual to extract the final state
        cases hRecv : endpointReceiveDual endpointId replierReceiver
            (ensureRunnable stReply replyTarget) with
        | error e =>
          exfalso; revert hStep; rw [hRecv]; split <;> (try split) <;> simp
        | ok pair =>
          obtain ⟨senderId, stFinal⟩ := pair
          have hStEq : st' = stFinal := by
            revert hStep; rw [hRecv]; split <;> (try split) <;> simp <;> exact Eq.symm
          subst hStEq
          have hObjInvReply := storeTcbIpcStateAndMessage_preserves_objects_invExt st stReply
              replyTarget _ _ hObjInv hStore
          have hProjReply := storeTcbIpcStateAndMessage_preserves_projection ctx observer
              st stReply replyTarget _ _ hReplyTargetObjHigh hObjInv hStore
          have hProjEns := ensureRunnable_preserves_projection ctx observer stReply replyTarget
              hReplyTargetHigh
          have hObjInvEns : (ensureRunnable stReply replyTarget).objects.invExt := by
            rw [ensureRunnable_preserves_objects]; exact hObjInvReply
          -- Prove endpointId ≠ replyTarget.toObjId from structure
          have hEpNe : endpointId ≠ replyTarget.toObjId := by
            intro hContra
            unfold storeTcbIpcStateAndMessage at hStore; simp only [hLookup] at hStore
            cases hStObj : storeObject replyTarget.toObjId
                (.tcb { tcb with ipcState := .ready, pendingMessage := some replyMsg }) st with
            | error e => simp [hStObj] at hStore
            | ok pair =>
              simp only [hStObj, Except.ok.injEq] at hStore; subst hStore
              have hTcbMid : (ensureRunnable pair.2 replyTarget).objects[replyTarget.toObjId]? =
                  some (.tcb { tcb with ipcState := .ready, pendingMessage := some replyMsg }) := by
                rw [ensureRunnable_preserves_objects pair.2 replyTarget]
                exact storeObject_objects_eq st pair.2 replyTarget.toObjId _ hObjInv hStObj
              rw [← hContra] at hTcbMid
              unfold endpointReceiveDual at hRecv; rw [hTcbMid] at hRecv; simp at hRecv
          -- Transfer endpoint objects from st to intermediate state
          have hObjsMid : (ensureRunnable stReply replyTarget).objects[endpointId]? =
              st.objects[endpointId]? := by
            rw [ensureRunnable_preserves_objects stReply replyTarget]
            exact storeTcbIpcStateAndMessage_preserves_objects_ne st stReply replyTarget _ _
                endpointId hEpNe hObjInv hStore
          -- Transfer queue hypotheses from st to intermediate state
          have hSQHH_mid : ∀ ep' sender',
              (ensureRunnable stReply replyTarget).objects[endpointId]? = some (.endpoint ep') →
              ep'.sendQ.head = some sender' → threadObservable ctx observer sender' = false := by
            intro ep' sender' hEp' hHead; rw [hObjsMid] at hEp'
            exact hSendQueueHeadHigh ep' sender' hEp' hHead
          have hSQNH_mid : ∀ ep' sender' senderTcb' nextTid',
              (ensureRunnable stReply replyTarget).objects[endpointId]? = some (.endpoint ep') →
              ep'.sendQ.head = some sender' →
              (ensureRunnable stReply replyTarget).objects[sender'.toObjId]? = some (.tcb senderTcb') →
              senderTcb'.queueNext = some nextTid' →
              objectObservable ctx observer nextTid'.toObjId = false := by
            intro ep' sender' senderTcb' nextTid' hEp' hHead hSenderTcb hNext
            rw [hObjsMid] at hEp'
            by_cases hSenderNe : sender'.toObjId = replyTarget.toObjId
            · -- sender at same ObjId as replyTarget — queueNext preserved
              unfold storeTcbIpcStateAndMessage at hStore; simp only [hLookup] at hStore
              cases hStObj : storeObject replyTarget.toObjId
                  (.tcb { tcb with ipcState := .ready, pendingMessage := some replyMsg }) st with
              | error e => simp [hStObj] at hStore
              | ok pair =>
                simp only [hStObj, Except.ok.injEq] at hStore; subst hStore
                have hTcbMid : (ensureRunnable pair.2 replyTarget).objects[sender'.toObjId]? =
                    some (.tcb { tcb with ipcState := .ready, pendingMessage := some replyMsg }) := by
                  rw [ensureRunnable_preserves_objects pair.2 replyTarget, hSenderNe]
                  exact storeObject_objects_eq st pair.2 replyTarget.toObjId _ hObjInv hStObj
                rw [hTcbMid] at hSenderTcb; cases hSenderTcb
                have hOrigTcb := lookupTcb_some_objects st replyTarget tcb hLookup
                rw [← hSenderNe] at hOrigTcb
                exact hSendQueueNextHigh ep' sender' tcb nextTid' hEp' hHead hOrigTcb hNext
            · have hSenderObj : (ensureRunnable stReply replyTarget).objects[sender'.toObjId]? =
                  st.objects[sender'.toObjId]? := by
                rw [ensureRunnable_preserves_objects stReply replyTarget]
                exact storeTcbIpcStateAndMessage_preserves_objects_ne st stReply replyTarget _ _
                    sender'.toObjId hSenderNe hObjInv hStore
              rw [hSenderObj] at hSenderTcb
              exact hSendQueueNextHigh ep' sender' senderTcb' nextTid' hEp' hHead hSenderTcb hNext
          have hRQTH_mid : ∀ ep' tailTid,
              (ensureRunnable stReply replyTarget).objects[endpointId]? = some (.endpoint ep') →
              ep'.receiveQ.tail = some tailTid →
              objectObservable ctx observer tailTid.toObjId = false := by
            intro ep' tailTid hEp' hTail; rw [hObjsMid] at hEp'
            exact hRecvQueueTailHigh ep' tailTid hEp' hTail
          rw [endpointReceiveDual_preserves_projection ctx observer endpointId replierReceiver
              (ensureRunnable stReply replyTarget) st' senderId hEndpointHigh hReceiverHigh
              hReceiverObjHigh hCoherent hSQHH_mid hSQNH_mid hRQTH_mid hObjInvEns hRecv,
              hProjEns, hProjReply]
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep

/-- R5-A/M-01: endpointReceiveDualChecked NI — projection-based (internalized). -/
theorem endpointReceiveDualChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (s₁ s₂ : SystemState) (r₁ r₂ : SeLe4n.ThreadId)
    (s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hProjection : ∀ t t' (r : SeLe4n.ThreadId),
        endpointReceiveDual endpointId receiver t = .ok (r, t') →
        projectState ctx observer t' = projectState ctx observer t)
    (hStep₁ : endpointReceiveDualChecked ctx endpointId receiver s₁ = .ok (r₁, s₁'))
    (hStep₂ : endpointReceiveDualChecked ctx endpointId receiver s₂ = .ok (r₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow := enforcementSoundness_endpointReceiveDualChecked ctx endpointId receiver s₁ r₁ s₁' hStep₁
  rw [endpointReceiveDualChecked_eq_endpointReceiveDual_when_allowed ctx endpointId receiver s₁ hFlow] at hStep₁
  rw [endpointReceiveDualChecked_eq_endpointReceiveDual_when_allowed ctx endpointId receiver s₂ hFlow] at hStep₂
  unfold lowEquivalent; rw [hProjection s₁ s₁' r₁ hStep₁, hProjection s₂ s₂' r₂ hStep₂]; exact hLow

/-- R5-A/M-01: endpointReceiveDual NI — projection-based (internalized). -/
theorem endpointReceiveDual_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (s₁ s₂ : SystemState) (sender₁ sender₂ : SeLe4n.ThreadId)
    (s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hProjection : ∀ t t' (r : SeLe4n.ThreadId),
        endpointReceiveDual endpointId receiver t = .ok (r, t') →
        projectState ctx observer t' = projectState ctx observer t)
    (hStep₁ : endpointReceiveDual endpointId receiver s₁ = .ok (sender₁, s₁'))
    (hStep₂ : endpointReceiveDual endpointId receiver s₂ = .ok (sender₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [hProjection s₁ s₁' sender₁ hStep₁, hProjection s₂ s₂' sender₂ hStep₂]; exact hLow

/-- R5-A/M-01: endpointCall NI — projection-based (internalized). -/
theorem endpointCall_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hProjection : ∀ t t', endpointCall endpointId caller msg t = .ok ((), t') →
        projectState ctx observer t' = projectState ctx observer t)
    (hStep₁ : endpointCall endpointId caller msg s₁ = .ok ((), s₁'))
    (hStep₂ : endpointCall endpointId caller msg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [hProjection s₁ s₁' hStep₁, hProjection s₂ s₂' hStep₂]; exact hLow

/-- R5-A/M-01: endpointReplyRecv NI — projection-based (internalized). -/
theorem endpointReplyRecv_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId)
    (replierReceiver replyTarget : SeLe4n.ThreadId)
    (replyMsg : IpcMessage)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hProjection : ∀ t t',
        endpointReplyRecv endpointId replierReceiver replyTarget replyMsg t = .ok ((), t') →
        projectState ctx observer t' = projectState ctx observer t)
    (hStep₁ : endpointReplyRecv endpointId replierReceiver replyTarget replyMsg s₁ = .ok ((), s₁'))
    (hStep₂ : endpointReplyRecv endpointId replierReceiver replyTarget replyMsg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [hProjection s₁ s₁' hStep₁, hProjection s₂ s₂' hStep₂]; exact hLow

-- ============================================================================
-- WS-H9: Scheduler compound operation NI proofs
-- ============================================================================

/-- WS-H9: rotateToBack a non-observable thread preserves projection.
`rotateToBack` changes run queue ordering but `projectRunnable` filters by
`threadObservable`, so non-observable threads are invisible in the projected list. -/
private theorem rotateToBack_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (hTidHigh : threadObservable ctx observer tid = false) :
    projectState ctx observer
        { st with scheduler := { st.scheduler with
            runQueue := st.scheduler.runQueue.rotateToBack tid } }
      = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · simp only [projectRunnable, SchedulerState.runnable, RunQueue.toList_filter_rotateToBack_neg _ _ _ hTidHigh]

/-- WS-H9: handleYield with non-observable current thread preserves projection.
handleYield = rotateToBack (non-obs thread filtered out of projection) + schedule. -/
theorem handleYield_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hCurrentHigh : ∀ t, st.scheduler.current = some t → threadObservable ctx observer t = false)
    (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable → threadObservable ctx observer tid = false)
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- V5-F: handleYield now returns .error .invalidArgument when current = none
    simp [hCur] at hStep
  | some tid =>
    have hTidHigh := hCurrentHigh tid hCur
    simp only [hCur] at hStep
    -- WS-H12b: new handleYield does match on objects, then insert + rotateToBack + schedule
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hStep
        -- hStep : schedule { st with scheduler.runQueue := (rq.insert tid prio).rotateToBack tid } = .ok ((), st')
        let rq' := (st.scheduler.runQueue.insert tid tcb.priority).rotateToBack tid
        let stIR : SystemState :=
          { st with scheduler := { st.scheduler with runQueue := rq' } }
        -- Show insert + rotateToBack preserves projection
        have hInsertRotProj : projectState ctx observer stIR = projectState ctx observer st := by
          simp only [projectState]; congr 1
          · simp only [projectRunnable, SchedulerState.runnable]
            rw [RunQueue.toList_filter_rotateToBack_neg _ _ _ hTidHigh,
                RunQueue.toList_filter_insert_neg' _ _ _ _ hTidHigh]
        have hAllRunnableIR : ∀ t, t ∈ stIR.scheduler.runnable →
            threadObservable ctx observer t = false := by
          intro t hMem'; simp only [SchedulerState.runnable] at hMem'
          have hMemRot := (RunQueue.rotateToBack_mem_iff _ _ t).mp
            ((RunQueue.mem_toList_iff_mem _ t).mp hMem')
          rcases (RunQueue.mem_insert _ _ _ t).mp hMemRot with hOrig | hEq
          · exact hAllRunnable t ((RunQueue.mem_toList_iff_mem _ t).mpr hOrig)
          · subst hEq; exact hTidHigh
        have hSchedStep : schedule stIR = .ok ((), st') := by
          simpa [stIR, rq', hCur] using hStep
        exact (schedule_preserves_projection ctx observer stIR st'
          (fun t hc => hCurrentHigh t (by simpa [stIR] using hc))
          hAllRunnableIR hObjInv hSchedStep).trans hInsertRotProj
      | _ => simp [hObj] at hStep

/-- WS-H9: handleYield preserves low-equivalence. -/
theorem handleYield_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCurrentHigh₁ : ∀ t, s₁.scheduler.current = some t →
        threadObservable ctx observer t = false)
    (hAllRunnable₁ : ∀ tid, tid ∈ s₁.scheduler.runnable →
        threadObservable ctx observer tid = false)
    (hCurrentHigh₂ : ∀ t, s₂.scheduler.current = some t →
        threadObservable ctx observer t = false)
    (hAllRunnable₂ : ∀ tid, tid ∈ s₂.scheduler.runnable →
        threadObservable ctx observer tid = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : handleYield s₁ = .ok ((), s₁'))
    (hStep₂ : handleYield s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    handleYield_preserves_projection ctx observer s₁ s₁' hCurrentHigh₁ hAllRunnable₁ hObjInv₁ hStep₁,
    handleYield_preserves_projection ctx observer s₂ s₂' hCurrentHigh₂ hAllRunnable₂ hObjInv₂ hStep₂]
  exact hLow

/-- WS-H9: Inserting a non-observable object and ticking machine preserves projection.
machine is not in ObservableState; the insert is at a non-observable ObjId. -/
private theorem insert_tick_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hOidHigh : objectObservable ctx observer oid = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer
        { st with objects := st.objects.insert oid obj, machine := tick st.machine }
      = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · funext o; simp only [projectObjects]
    by_cases hObs : objectObservable ctx observer o
    · simp only [hObs, ite_true]
      by_cases hEq : o = oid
      · subst hEq; simp [hOidHigh] at hObs
      · simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]; simp [show ¬(oid == o) from by simp; exact Ne.symm hEq]
    · simp [hObs]

/-- WS-H9: timerTick with non-observable current thread preserves projection.
timerTick modifies: machine (not projected), objects at current tid (non-obs),
and optionally rotateToBack + schedule (covered by existing helpers). -/
theorem timerTick_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hCurrentHigh : ∀ t, st.scheduler.current = some t → threadObservable ctx observer t = false)
    (hCurrentObjHigh : ∀ t, st.scheduler.current = some t → objectObservable ctx observer t.toObjId = false)
    (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable → threadObservable ctx observer tid = false)
    (hObjInv : st.objects.invExt)
    (hStep : timerTick st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep; subst hStep
    simp only [projectState]; congr 1
  | some tid =>
    simp only [hCur] at hStep
    have hTidHigh := hCurrentHigh tid hCur
    have hTidObjHigh := hCurrentObjHigh tid hCur
    -- Split on the match st.objects[tid.toObjId]?
    split at hStep
    · -- Case: some (.tcb tcb)
      next tcb hTcbEq =>
      -- Split on timeSlice ≤ 1
      split at hStep
      · -- Time-slice expired: insert back into runQueue + schedule
        -- WS-H12b: new timerTick does insert (re-enqueue) then schedule, no if-then-else
        let tcbReset : KernelObject := KernelObject.tcb { tcb with timeSlice := defaultTimeSlice }
        have hInsertTickProj := insert_tick_preserves_projection ctx observer st
          tid.toObjId tcbReset hTidObjHigh hObjInv
        let stIT : SystemState :=
          { st with objects := st.objects.insert tid.toObjId tcbReset, machine := tick st.machine }
        -- stIT has the same runQueue as st
        let stInsert : SystemState :=
          { stIT with scheduler := { stIT.scheduler with
              runQueue := stIT.scheduler.runQueue.insert tid tcb.priority } }
        -- Show insert preserves projection (non-observable thread)
        have hInsertRqProj : projectState ctx observer stInsert = projectState ctx observer stIT := by
          simp only [projectState]; congr 1
          · simp only [projectRunnable, SchedulerState.runnable]
            exact RunQueue.toList_filter_insert_neg' _ _ _ _ hTidHigh
        have hCurSched : ∀ t, stInsert.scheduler.current = some t →
            threadObservable ctx observer t = false :=
          fun t hc => hCurrentHigh t (by simpa [stInsert, stIT] using hc)
        have hAllRunnableSched : ∀ t, t ∈ stInsert.scheduler.runnable →
            threadObservable ctx observer t = false := by
          intro t hMem'; simp only [SchedulerState.runnable] at hMem'
          rcases (RunQueue.mem_insert _ _ _ t).mp
            ((RunQueue.mem_toList_iff_mem _ t).mp hMem') with hOrig | hEq
          · exact hAllRunnable t ((RunQueue.mem_toList_iff_mem _ t).mpr hOrig)
          · subst hEq; exact hTidHigh
        have hSchedStep : schedule stInsert = .ok ((), st') := by
          simpa [stInsert, stIT, hCur] using hStep
        have hObjInvInsert : stInsert.objects.invExt := RHTable_insert_preserves_invExt st.objects _ _ hObjInv
        rw [schedule_preserves_projection ctx observer stInsert st' hCurSched hAllRunnableSched hObjInvInsert hSchedStep,
            hInsertRqProj, hInsertTickProj]
      · -- Time-slice not expired: insert + tick
        next hSliceNot =>
        have hEq := Except.ok.inj hStep
        simp only [Prod.mk.injEq, true_and] at hEq; subst hEq
        exact insert_tick_preserves_projection ctx observer st tid.toObjId
          (KernelObject.tcb { tcb with timeSlice := tcb.timeSlice - 1 }) hTidObjHigh hObjInv
    · -- Catch-all: error (not a TCB or not found)
      simp at hStep

/-- WS-H9: timerTick preserves low-equivalence. -/
theorem timerTick_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCurrentHigh₁ : ∀ t, s₁.scheduler.current = some t →
        threadObservable ctx observer t = false)
    (hCurrentObjHigh₁ : ∀ t, s₁.scheduler.current = some t →
        objectObservable ctx observer t.toObjId = false)
    (hAllRunnable₁ : ∀ tid, tid ∈ s₁.scheduler.runnable →
        threadObservable ctx observer tid = false)
    (hCurrentHigh₂ : ∀ t, s₂.scheduler.current = some t →
        threadObservable ctx observer t = false)
    (hCurrentObjHigh₂ : ∀ t, s₂.scheduler.current = some t →
        objectObservable ctx observer t.toObjId = false)
    (hAllRunnable₂ : ∀ tid, tid ∈ s₂.scheduler.runnable →
        threadObservable ctx observer tid = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : timerTick s₁ = .ok ((), s₁'))
    (hStep₂ : timerTick s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    timerTick_preserves_projection ctx observer s₁ s₁' hCurrentHigh₁ hCurrentObjHigh₁ hAllRunnable₁ hObjInv₁ hStep₁,
    timerTick_preserves_projection ctx observer s₂ s₂' hCurrentHigh₂ hCurrentObjHigh₂ hAllRunnable₂ hObjInv₂ hStep₂]
  exact hLow

-- ============================================================================
-- WS-K-F5: Lifecycle NI proofs — completing deferred proof list
-- ============================================================================

/-- WS-K-F5: `retypeFromUntyped` at non-observable targets preserves
low-equivalence. The operation decomposes (via `retypeFromUntyped_ok_decompose`)
into a read-only `cspaceLookupSlot` followed by two `storeObject` calls —
one for the untyped watermark advance and one for the new child. Both targets
are non-observable, so each store preserves low-equivalence. -/
theorem retypeFromUntyped_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject) (allocSize : Nat)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hUntypedHigh : objectObservable ctx observer untypedId = false)
    (hChildHigh : objectObservable ctx observer childId = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : retypeFromUntyped authority untypedId childId newObj allocSize s₁ = .ok ((), s₁'))
    (hStep₂ : retypeFromUntyped authority untypedId childId newObj allocSize s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  -- Decompose each step into constituent storeObject calls
  rcases retypeFromUntyped_ok_decompose s₁ s₁' authority untypedId childId newObj allocSize hStep₁ with
    ⟨ut₁, ut₁', cap₁, stL₁, stUt₁, _, _, _, _, hLookup₁, _, _, hStoreUt₁, hStoreChild₁⟩
  rcases retypeFromUntyped_ok_decompose s₂ s₂' authority untypedId childId newObj allocSize hStep₂ with
    ⟨ut₂, ut₂', cap₂, stL₂, stUt₂, _, _, _, _, hLookup₂, _, _, hStoreUt₂, hStoreChild₂⟩
  -- Lookup is read-only: stL₁ = s₁, stL₂ = s₂
  have hEqL₁ := cspaceLookupSlot_ok_state_eq s₁ authority cap₁ stL₁ hLookup₁
  have hEqL₂ := cspaceLookupSlot_ok_state_eq s₂ authority cap₂ stL₂ hLookup₂
  rw [hEqL₁] at hStoreUt₁; rw [hEqL₂] at hStoreUt₂
  -- First storeObject (untyped update) at non-observable untypedId
  have hMid := storeObject_at_unobservable_preserves_lowEquivalent
    ctx observer untypedId (.untyped ut₁') (.untyped ut₂') s₁ s₂ stUt₁ stUt₂
    hLow hUntypedHigh hObjInv₁ hObjInv₂ hStoreUt₁ hStoreUt₂
  -- Propagate invExt through first storeObject
  have hObjInvUt₁ := storeObject_preserves_objects_invExt s₁ stUt₁ untypedId _ hObjInv₁ hStoreUt₁
  have hObjInvUt₂ := storeObject_preserves_objects_invExt s₂ stUt₂ untypedId _ hObjInv₂ hStoreUt₂
  -- Second storeObject (child creation) at non-observable childId
  exact storeObject_at_unobservable_preserves_lowEquivalent
    ctx observer childId newObj newObj stUt₁ stUt₂ s₁' s₂'
    hMid hChildHigh hObjInvUt₁ hObjInvUt₂ hStoreChild₁ hStoreChild₂

-- ============================================================================
-- lifecycleRevokeDeleteRetype NI proofs
-- ============================================================================

/-- `lifecycleRevokeDeleteRetype` at non-observable cleanup CNode and target
preserves projection. The operation decomposes (via
`lifecycleRevokeDeleteRetype_ok_implies_staged_steps`) into:
1. `cspaceRevoke` at `cleanup` — projection preserved by `cspaceRevoke_preserves_projection`,
2. `cspaceDeleteSlot` at `cleanup` — projection preserved by `cspaceDeleteSlot_preserves_projection`,
3. `cspaceLookupSlot` at `cleanup` — read-only (fails with `invalidCapability`, no state change),
4. `lifecycleRetypeObject` at `target` — projection preserved via `storeObject_preserves_projection`. -/
theorem lifecycleRevokeDeleteRetype_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (authority cleanup : CSpaceAddr) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState)
    (hCleanupHigh : objectObservable ctx observer cleanup.cnode = false)
    (hTargetHigh : objectObservable ctx observer target = false)
    (hObjInv : st.objects.invExt)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  rcases lifecycleRevokeDeleteRetype_ok_implies_staged_steps st st' authority cleanup target newObj hStep with
    ⟨stRevoked, stDeleted, _, hRevoke, hDelete, _, hRetype⟩
  rcases lifecycleRetypeObject_ok_as_storeObject stDeleted st' authority target newObj hRetype with
    ⟨_, _, _, _, _, _, hStore⟩
  -- Propagate invExt through cspaceRevoke: cspaceRevoke does cspaceLookupSlot (preserves state)
  -- + storeObject (preserves invExt) + revokeAndClearRefsState (preserves objects)
  have hObjInvRevoked : stRevoked.objects.invExt := by
    unfold cspaceRevoke at hRevoke
    cases hL : cspaceLookupSlot cleanup st with
    | error e => simp [hL] at hRevoke
    | ok p =>
      rcases p with ⟨par, stL⟩
      have hEqL := cspaceLookupSlot_preserves_state st stL cleanup par hL
      subst stL
      cases hC : st.objects[cleanup.cnode]? with
      | none => simp [hL, hC] at hRevoke
      | some obj =>
        cases obj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hL, hC] at hRevoke
        | cnode cn =>
          simp [hL, hC, storeObject] at hRevoke; cases hRevoke
          rw [revokeAndClearRefsState_preserves_objects]
          exact RHTable_insert_preserves_invExt st.objects _ _ hObjInv
  -- Propagate invExt through cspaceDeleteSlot: cspaceDeleteSlot does storeObject + storeCapabilityRef + detachSlotFromCdt
  have hObjInvDeleted : stDeleted.objects.invExt := by
    unfold cspaceDeleteSlot at hDelete
    -- U-H03: Discharge CDT children guard
    split at hDelete
    · simp at hDelete
    · unfold cspaceDeleteSlotCore at hDelete
      cases hObj : stRevoked.objects[cleanup.cnode]? with
      | none => simp [hObj] at hDelete
      | some obj =>
        cases obj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hDelete
        | cnode cn =>
          simp only [hObj] at hDelete
          cases hSt : storeObject cleanup.cnode (.cnode (cn.remove cleanup.slot)) stRevoked with
          | error e => simp [hSt] at hDelete
          | ok pair₁ =>
            simp only [hSt] at hDelete
            have hInvPair := storeObject_preserves_objects_invExt stRevoked pair₁.2 cleanup.cnode _ hObjInvRevoked hSt
            cases hRef : storeCapabilityRef cleanup none pair₁.2 with
            | error e => simp [hRef] at hDelete
            | ok pair₂ =>
              simp only [hRef] at hDelete; cases hDelete
              -- detachSlotFromCdt only modifies CDT, storeCapabilityRef preserves objects
              have hRefObjs := storeCapabilityRef_preserves_objects pair₁.2 pair₂.2 cleanup none hRef
              simp only [SystemState.detachSlotFromCdt]; split
              · exact hRefObjs ▸ hInvPair
              · exact hRefObjs ▸ hInvPair
  rw [storeObject_preserves_projection ctx observer stDeleted st' target newObj hTargetHigh hObjInvDeleted hStore,
      cspaceDeleteSlot_preserves_projection ctx observer cleanup stRevoked stDeleted hCleanupHigh hObjInvRevoked hDelete,
      cspaceRevoke_preserves_projection ctx observer cleanup st stRevoked hCleanupHigh hObjInv hRevoke]

/-- `lifecycleRevokeDeleteRetype` at non-observable cleanup CNode and target
preserves low-equivalence. Composes low-equivalence preservation across
three sub-operations: `cspaceRevoke`, `cspaceDeleteSlot`, and
`lifecycleRetypeObject`. -/
theorem lifecycleRevokeDeleteRetype_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (authority cleanup : CSpaceAddr) (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCleanupHigh : objectObservable ctx observer cleanup.cnode = false)
    (hTargetHigh : objectObservable ctx observer target = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : lifecycleRevokeDeleteRetype authority cleanup target newObj s₁ = .ok ((), s₁'))
    (hStep₂ : lifecycleRevokeDeleteRetype authority cleanup target newObj s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  unfold lowEquivalent; rw [
    lifecycleRevokeDeleteRetype_preserves_projection ctx observer authority cleanup target
      newObj s₁ s₁' hCleanupHigh hTargetHigh hObjInv₁ hStep₁,
    lifecycleRevokeDeleteRetype_preserves_projection ctx observer authority cleanup target
      newObj s₂ s₂' hCleanupHigh hTargetHigh hObjInv₂ hStep₂]
  exact hLow


-- ============================================================================
-- R5-B: registerServiceChecked Non-Interference (M-02)
-- ============================================================================

/-- R5-B.2/M-02: registerService at a non-observable service preserves projection.
registerService only modifies `serviceRegistry`, which only affects the `services`
field of `ObservableState`. If the registered service is non-observable, the
projected service presence is unchanged. -/
theorem registerService_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (reg : ServiceRegistration) (st st' : SystemState)
    (hStep : registerService reg st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  -- registerService on success produces { st with serviceRegistry := ... }
  -- Extract the state equality from the success case
  unfold registerService at hStep
  split at hStep <;> try simp at hStep
  split at hStep <;> try simp at hStep
  -- Match on CapTarget cases
  split at hStep
  · -- .object epId
    split at hStep <;> try simp at hStep
    · -- endpoint found
      split at hStep <;> try simp at hStep
      · -- hasRight check passed — only serviceRegistry changes, projection unchanged
        -- because the new service is non-observable (hServiceHigh)
        cases hStep; simp only [projectState]; congr 1
  all_goals simp at hStep

/-- R5-B/M-02: registerServiceChecked NI — projection-based.
If the registered service is non-observable, both executions preserve projection. -/
theorem registerServiceChecked_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (caller : SeLe4n.ThreadId) (reg : ServiceRegistration)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : registerServiceChecked ctx caller reg s₁ = .ok ((), s₁'))
    (hStep₂ : registerServiceChecked ctx caller reg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hFlow₁ := enforcementSoundness_registerServiceChecked ctx caller reg s₁ s₁' hStep₁
  rw [registerServiceChecked_eq_registerService_when_allowed ctx caller reg s₁ hFlow₁] at hStep₁
  rw [registerServiceChecked_eq_registerService_when_allowed ctx caller reg s₂
    (enforcementSoundness_registerServiceChecked ctx caller reg s₂ s₂' hStep₂)] at hStep₂
  unfold lowEquivalent; rw [
    registerService_preserves_projection ctx observer reg s₁ s₁' hStep₁,
    registerService_preserves_projection ctx observer reg s₂ s₂' hStep₂]
  exact hLow

-- ============================================================================
-- S6-E: Memory scrubbing preserves non-interference
-- ============================================================================

/-- S6-E: `scrubObjectMemory` preserves the observer projection.

    Memory scrubbing zeros a contiguous region in `machine.memory`. Since all
    non-memory projection fields (objects, scheduler, services, etc.) are
    unchanged, and `projectMemory` returns the same result when `machine.memory`
    is deterministically modified, the overall projection is preserved when
    scrubbing non-observable memory.

    The key insight: if the scrubbed region is NOT observable to the observer
    (`memoryAddressObservable` returns false for all addresses in the range),
    then `projectMemory` returns `none` for those addresses both before and
    after scrubbing. If the region IS observable, the values change from
    arbitrary data to 0, but this is a deterministic function of the object ID
    and type — not of the state — so both s₁ and s₂ get the same change.

    For the single-state projection preservation (used by projection lemmas): -/
theorem scrubObjectMemory_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (objectId : SeLe4n.ObjId) (objType : KernelObjectType)
    (st : SystemState)
    (hNotObs : ∀ addr : SeLe4n.PAddr,
      objectId.toNat * objectTypeAllocSize objType ≤ addr.toNat →
      addr.toNat < objectId.toNat * objectTypeAllocSize objType +
        objectTypeAllocSize objType →
      memoryAddressObservable ctx observer addr = false) :
    projectState ctx observer (scrubObjectMemory st objectId objType) =
      projectState ctx observer st := by
  -- scrubObjectMemory only modifies machine.memory. All non-memory fields
  -- (objects, scheduler, services, etc.) are definitionally unchanged.
  -- Only the memory projection needs case analysis.
  simp only [projectState]; congr 1
  -- memory projection: for each address, if observable and in range → contradiction;
  -- if observable and not in range → value unchanged; if not observable → both none
  funext addr
  simp only [projectMemory, scrubObjectMemory, SeLe4n.zeroMemoryRange]
  split
  · -- Address observable
    split
    · -- In scrubbed range — contradicts hNotObs
      rename_i hObs hInRange
      have hNotObs' := hNotObs addr hInRange.1 hInRange.2
      rw [hNotObs'] at hObs; cases hObs
    · -- Outside scrubbed range — value unchanged
      rfl
  · rfl

/-- S6-E: `scrubObjectMemory` preserves low-equivalence when applied
    symmetrically to both states with a non-observable target.

    When a deleted object's security label does NOT flow to the observer,
    the scrubbing region is not observable, so `lowEquivalent` is preserved.
    This is the standard NI pattern for lifecycle operations that operate
    on high-domain objects. -/
theorem scrubObjectMemory_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (objectId : SeLe4n.ObjId) (objType : KernelObjectType)
    (s₁ s₂ : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hNotObs : ∀ addr : SeLe4n.PAddr,
      objectId.toNat * objectTypeAllocSize objType ≤ addr.toNat →
      addr.toNat < objectId.toNat * objectTypeAllocSize objType +
        objectTypeAllocSize objType →
      memoryAddressObservable ctx observer addr = false) :
    lowEquivalent ctx observer
      (scrubObjectMemory s₁ objectId objType)
      (scrubObjectMemory s₂ objectId objType) := by
  unfold lowEquivalent
  rw [scrubObjectMemory_preserves_projection ctx observer objectId objType s₁ hNotObs,
      scrubObjectMemory_preserves_projection ctx observer objectId objType s₂ hNotObs]
  exact hLow

