-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.Projection
import SeLe4n.Kernel.InformationFlow.Enforcement
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Capability.Invariant
import SeLe4n.Kernel.Scheduler.Operations
import SeLe4n.Kernel.Lifecycle.Operations
import SeLe4n.Kernel.Service.Invariant
import SeLe4n.Kernel.Architecture.VSpace

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

-- ============================================================================
-- R5-C.1: Memory projection preservation helper
-- ============================================================================

/-- R5-C.1: storeObject preserves memory projection (storeObject does not modify machine state). -/
theorem storeObject_preserves_projectMemory
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    projectMemory ctx observer st' = projectMemory ctx observer st :=
  projectMemory_eq_of_memory_eq ctx observer st' st (by rw [storeObject_machine_eq st st' oid obj hStore])

-- ============================================================================
-- WS-F3: storeObject objectIndex filter preservation
-- ============================================================================

/-- WS-F3: storeObject at a non-observable ID preserves the projected object index.
If the target is non-observable, its addition to the raw index is filtered out. -/
private theorem storeObject_preserves_projectObjectIndex
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hOidHigh : objectObservable ctx observer oid = false)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    projectObjectIndex ctx observer st' = projectObjectIndex ctx observer st := by
  unfold storeObject at hStore; cases hStore
  simp only [projectObjectIndex]
  split
  · rfl
  · rw [List.filter_cons]; simp [hOidHigh]

/-- WS-F3: cspaceInsertSlot at a non-observable CNode preserves the projected object index.
Follows from the store's frame lemma. -/
theorem cspaceInsertSlot_preserves_projectObjectIndex
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hOidHigh : objectObservable ctx observer addr.cnode = false)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    projectObjectIndex ctx observer st' = projectObjectIndex ctx observer st := by
  obtain ⟨cn, _, _, _, hStore⟩ :=
    cspaceInsertSlot_ok_decompose st st' addr cap hStep
  exact storeObject_preserves_projectObjectIndex ctx observer st st'
    addr.cnode _ hOidHigh hStore

-- ============================================================================
-- Shared non-interference proof infrastructure
-- ============================================================================

/-- A generic storeObject at a non-observable id preserves low-equivalence.
This is the shared proof skeleton used by multiple non-interference theorems. -/
theorem storeObject_at_unobservable_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (targetId : SeLe4n.ObjId)
    (obj₁ obj₂ : KernelObject)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hTargetHigh : objectObservable ctx observer targetId = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStore₁ : storeObject targetId obj₁ s₁ = .ok ((), s₁'))
    (hStore₂ : storeObject targetId obj₂ s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hObjLow : projectObjects ctx observer s₁ = projectObjects ctx observer s₂ :=
    congrArg ObservableState.objects hLow
  have hRunLow : projectRunnable ctx observer s₁ = projectRunnable ctx observer s₂ :=
    congrArg ObservableState.runnable hLow
  have hCurLow : projectCurrent ctx observer s₁ = projectCurrent ctx observer s₂ :=
    congrArg ObservableState.current hLow
  have hDomLow : projectActiveDomain ctx observer s₁ = projectActiveDomain ctx observer s₂ :=
    congrArg ObservableState.activeDomain hLow
  have hIrqLow : projectIrqHandlers ctx observer s₁ = projectIrqHandlers ctx observer s₂ :=
    congrArg ObservableState.irqHandlers hLow
  have hIdxLow : projectObjectIndex ctx observer s₁ = projectObjectIndex ctx observer s₂ :=
    congrArg ObservableState.objectIndex hLow
  have hObj' : projectObjects ctx observer s₁' = projectObjects ctx observer s₂' := by
    funext oid
    by_cases hObs : objectObservable ctx observer oid
    · by_cases hEq : oid = targetId
      · subst hEq; simp [hTargetHigh] at hObs
      · have hObj₁ : s₁'.objects[oid]? = s₁.objects[oid]? :=
          storeObject_objects_ne s₁ s₁' targetId oid obj₁ hEq hObjInv₁ hStore₁
        have hObj₂ : s₂'.objects[oid]? = s₂.objects[oid]? :=
          storeObject_objects_ne s₂ s₂' targetId oid obj₂ hEq hObjInv₂ hStore₂
        have hObjBase : (s₁.objects[oid]?).map (projectKernelObject ctx observer) =
            (s₂.objects[oid]?).map (projectKernelObject ctx observer) := by
          have hBase := congrFun hObjLow oid
          simp only [projectObjects, hObs, ite_true, SystemState.getObject?] at hBase
          exact hBase
        simpa [projectObjects, hObs, hObj₁, hObj₂] using hObjBase
    · simp [projectObjects, hObs]
  have hRun' : projectRunnable ctx observer s₁' = projectRunnable ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simpa [projectRunnable, hSched₁, hSched₂] using hRunLow
  have hCur' : projectCurrent ctx observer s₁' = projectCurrent ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simpa [projectCurrent, hSched₁, hSched₂] using hCurLow
  have hDom' : projectActiveDomain ctx observer s₁' = projectActiveDomain ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simpa [projectActiveDomain, hSched₁, hSched₂] using hDomLow
  have hIrq' : projectIrqHandlers ctx observer s₁' = projectIrqHandlers ctx observer s₂' := by
    have hIH₁ := storeObject_irqHandlers_eq s₁ s₁' targetId obj₁ hStore₁
    have hIH₂ := storeObject_irqHandlers_eq s₂ s₂' targetId obj₂ hStore₂
    funext irq; simp only [projectIrqHandlers, hIH₁, hIH₂]
    exact congrFun hIrqLow irq
  have hIdx' : projectObjectIndex ctx observer s₁' = projectObjectIndex ctx observer s₂' := by
    rw [storeObject_preserves_projectObjectIndex ctx observer s₁ s₁' targetId obj₁ hTargetHigh hStore₁,
        storeObject_preserves_projectObjectIndex ctx observer s₂ s₂' targetId obj₂ hTargetHigh hStore₂]
    exact hIdxLow
  have hDTR : projectDomainTimeRemaining ctx observer s₁' = projectDomainTimeRemaining ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simp [projectDomainTimeRemaining, hSched₁, hSched₂]
    exact congrArg ObservableState.domainTimeRemaining hLow
  have hDS : projectDomainSchedule ctx observer s₁' = projectDomainSchedule ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simp [projectDomainSchedule, hSched₁, hSched₂]
    exact congrArg ObservableState.domainSchedule hLow
  have hDSI : projectDomainScheduleIndex ctx observer s₁' = projectDomainScheduleIndex ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    simp [projectDomainScheduleIndex, hSched₁, hSched₂]
    exact congrArg ObservableState.domainScheduleIndex hLow
  have hMR : projectMachineRegs ctx observer s₁' = projectMachineRegs ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' targetId obj₁ hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' targetId obj₂ hStore₂
    have hM₁ := storeObject_machine_eq s₁ s₁' targetId obj₁ hStore₁
    have hM₂ := storeObject_machine_eq s₂ s₂' targetId obj₂ hStore₂
    simp [projectMachineRegs, hSched₁, hSched₂, hM₁, hM₂]
    exact congrArg ObservableState.machineRegs hLow
  have hMem : projectMemory ctx observer s₁' = projectMemory ctx observer s₂' := by
    have hM₁ := storeObject_machine_eq s₁ s₁' targetId obj₁ hStore₁
    have hM₂ := storeObject_machine_eq s₂ s₂' targetId obj₂ hStore₂
    have hMemLow : projectMemory ctx observer s₁ = projectMemory ctx observer s₂ :=
      congrArg ObservableState.memory hLow
    rw [projectMemory_eq_of_memory_eq ctx observer s₁' s₁ (by rw [hM₁]),
        projectMemory_eq_of_memory_eq ctx observer s₂' s₂ (by rw [hM₂])]
    exact hMemLow
  unfold lowEquivalent
  simp [projectState, hObj', hRun', hCur', hDom', hIrq', hIdx', hDTR, hDS, hDSI, hMR, hMem]

-- ============================================================================
-- WS-E3/H-09: Multi-step operation helpers for non-interference
-- ============================================================================

/-- List filter commutation: filtering by (· ≠ a) then by p equals just filtering by p
when p a = false. Used for removeRunnable projection preservation. -/
private theorem list_filter_ne_then_filter_eq
    {α : Type} [DecidableEq α] (xs : List α) (a : α) (p : α → Bool)
    (hPa : p a = false) :
    (xs.filter (· ≠ a)).filter p = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter]
    by_cases hxeq : x = a
    · -- x = a: the (· ≠ a) filter drops x; p a = false drops it from RHS too
      subst hxeq
      simp only [ne_eq, not_true, decide_false, hPa]
      exact ih
    · -- x ≠ a: the (· ≠ a) filter keeps x
      have hNeTrue : decide (x ≠ a) = true := decide_eq_true_eq.mpr hxeq
      rw [hNeTrue]; simp only [List.filter]
      cases hpx : p x
      · exact ih
      · simp only [List.cons.injEq, true_and]; exact ih

/-- List filter absorption: filtering by p on (xs ++ [a]) equals filtering by p on xs
when p a = false. Used for ensureRunnable projection preservation. -/
private theorem list_filter_append_singleton_unobs
    {α : Type} [DecidableEq α] (xs : List α) (a : α) (p : α → Bool)
    (hPa : p a = false) :
    (xs ++ [a]).filter p = xs.filter p := by
  rw [List.filter_append]
  simp [List.filter, hPa]

/-- WS-ZA ZA4.5: the projection strips every run-queue field from a TCB, so two
stores agreeing off those fields project equally. -/
theorem projectObjects_of_objectsAgreeOffRunLinks
    (ctx : LabelingContext) (observer : IfObserver) {st st' : SystemState}
    (h : st'.objectsAgreeOffRunLinks st) :
    projectObjects ctx observer st' = projectObjects ctx observer st := by
  funext oid
  unfold projectObjects SystemState.getObject?
  split
  · cases e : st.objects[oid]? with
    | none => rw [h.get_none_iff.mpr e]
    | some o => cases o with
      | tcb t =>
        obtain ⟨t', _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht', rfl⟩ := h.get_tcb_fwd e
        rw [ht']; rfl
      | _ => rw [h.get_of_not_tcb (fun _ e => KernelObject.noConfusion e) e]
  · rfl

/-- A step that changes nothing outside the object table, and nothing the
observer projects inside it, preserves the projection. -/
theorem projectState_of_objects_only (ctx : LabelingContext) (observer : IfObserver)
    {s st : SystemState} (hS : s = { st with objects := s.objects })
    (hO : projectObjects ctx observer s = projectObjects ctx observer st) :
    projectState ctx observer s = projectState ctx observer st := by
  unfold projectState
  rw [hO, hS]
  rfl

/-- WS-ZA ZA4.7: recording a blocking sender's badge and grant bit writes only
fields the projection erases. -/
theorem recordSendCap_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (tid : SeLe4n.ThreadId) (badge : Option SeLe4n.Badge) (grant : Bool) :
    projectState ctx observer (recordSendCap st tid badge grant) = projectState ctx observer st :=
  projectState_of_objects_only ctx observer rfl
    (projectObjects_of_objectsAgreeOffRunLinks ctx observer
      (recordSendCap_objectsAgreeOffRunLinks st tid badge grant))

/-- WS-ZA ZA4.6: joining a server's reply-waiter queue writes only reply-waiter
links, which the projection erases, so the projection is unchanged whoever the
caller, server and old head are. -/
theorem linkReplyWaiter_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (w s : SeLe4n.ThreadId) :
    projectState ctx observer (st.linkReplyWaiter w s) = projectState ctx observer st :=
  projectState_of_objects_only ctx observer (SystemState.linkReplyWaiter_eq_objects st w s)
    (projectObjects_of_objectsAgreeOffRunLinks ctx observer
      (SystemState.linkReplyWaiter_objectsAgreeOffRunLinks st w s))

/-- WS-ZA ZA4.6: leaving a server's reply-waiter queue, likewise. -/
theorem unlinkReplyWaiter_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (w s : SeLe4n.ThreadId) :
    projectState ctx observer (st.unlinkReplyWaiter w s) = projectState ctx observer st :=
  projectState_of_objects_only ctx observer (SystemState.unlinkReplyWaiter_eq_objects st w s)
    (projectObjects_of_objectsAgreeOffRunLinks ctx observer
      (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks st w s))

theorem unlinkReplyWaiterOpt_preserves_projection (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (w : SeLe4n.ThreadId) (s? : Option SeLe4n.ThreadId) :
    projectState ctx observer (st.unlinkReplyWaiterOpt w s?) = projectState ctx observer st := by
  cases s? with
  | none => rfl
  | some s => exact unlinkReplyWaiter_preserves_projection ctx observer st w s

/-- WS-ZA ZA4.4: a signal's pop writes the old head and its successor, each only
in its notification links; with both threads high the projection is unchanged. -/
theorem detachNtfnHead_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (hHead : objectObservable ctx observer head.toObjId = false)
    (hNext : ∀ n, next = some n → objectObservable ctx observer n.toObjId = false)
    (hInv : st.objects.invExt) :
    projectState ctx observer (detachNtfnHead st head next) = projectState ctx observer st := by
  refine projectState_of_objects_only ctx observer (detachNtfnHead_eq_objects st head next hInv) ?_
  funext o
  unfold projectObjects SystemState.getObject?
  split
  · rename_i hObs
    rw [detachNtfnHead_objects_ne st head next hInv o
      (fun e => by rw [e, hObs] at hHead; cases hHead)
      (fun n hn e => by have h := hNext n hn; rw [e, hObs] at h; cases h)]
  · rfl

/-- Removing a non-observable thread preserves low-equivalence projection. -/
theorem removeRunnable_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hTidHigh : threadObservable ctx observer tid = false) :
    projectState ctx observer (removeRunnable st tid) = projectState ctx observer st := by
  have hS := removeRunnable_scheduler st tid
  have hD := removeRunnable_onlyObjectsSchedulerDiffer st tid
  unfold SystemState.onlyObjectsSchedulerDiffer at hD
  have hRun : projectRunnable ctx observer (removeRunnable st tid) = projectRunnable ctx observer st := by
    simp only [projectRunnable, hS, SchedulerState.runnable,
      SchedulerState.markReschedulePendingOnCoreIf_runQueueOnCore,
      SchedulerState.setCurrentOnCore_runQueueOnCore, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
    exact RunQueue.toList_filter_remove_neg _ tid (threadObservable ctx observer) hTidHigh
  have hCur : projectCurrent ctx observer (removeRunnable st tid) = projectCurrent ctx observer st := by
    simp only [projectCurrent, hS,
      SchedulerState.markReschedulePendingOnCoreIf_currentOnCore,
      SchedulerState.setCurrentOnCore_currentOnCore_self]
    cases hC : st.scheduler.currentOnCore bootCoreId with
    | none => simp
    | some x =>
      by_cases hEq : some x = some tid
      · rw [if_pos hEq]; cases (Option.some.inj hEq); simp [hTidHigh]
      · rw [if_neg hEq]
  have hObj : projectObjects ctx observer (removeRunnable st tid) = projectObjects ctx observer st :=
    projectObjects_of_objectsAgreeOffRunLinks ctx observer (removeRunnable_objectsAgreeOffRunLinks st tid)
  have hDom : projectActiveDomain ctx observer (removeRunnable st tid) =
      projectActiveDomain ctx observer st := by
    rw [hD]; first | rfl | simp [projectActiveDomain, hS]
  have hIrq : projectIrqHandlers ctx observer (removeRunnable st tid) =
      projectIrqHandlers ctx observer st := by
    rw [hD]; rfl
  have hIdx : projectObjectIndex ctx observer (removeRunnable st tid) =
      projectObjectIndex ctx observer st := by
    rw [hD]; rfl
  have hDTR : projectDomainTimeRemaining ctx observer (removeRunnable st tid) =
      projectDomainTimeRemaining ctx observer st := by
    rw [hD]; first | rfl | simp [projectDomainTimeRemaining, hS]
  have hDS : projectDomainSchedule ctx observer (removeRunnable st tid) =
      projectDomainSchedule ctx observer st := by
    rw [hD]; first | rfl | simp [projectDomainSchedule, hS]
  have hDSI : projectDomainScheduleIndex ctx observer (removeRunnable st tid) =
      projectDomainScheduleIndex ctx observer st := by
    rw [hD]; first | rfl | simp [projectDomainScheduleIndex, hS]
  have hMR : projectMachineRegs ctx observer (removeRunnable st tid) =
      projectMachineRegs ctx observer st := by
    rw [hD]
    simp only [projectMachineRegs, hS,
      SchedulerState.markReschedulePendingOnCoreIf_currentOnCore,
      SchedulerState.setCurrentOnCore_currentOnCore_self]
    cases hC : st.scheduler.currentOnCore bootCoreId with
    | none => simp
    | some x =>
      by_cases hEq : some x = some tid
      · rw [if_pos hEq]; cases (Option.some.inj hEq); simp [hTidHigh]
      · rw [if_neg hEq]
  have hMem : projectMemory ctx observer (removeRunnable st tid) =
      projectMemory ctx observer st :=
    projectMemory_eq_of_memory_eq ctx observer (removeRunnable st tid) st (by rw [hD])
  simp only [projectState, hObj, hRun, hCur, hDom, hIrq, hIdx, hDTR, hDS, hDSI, hMR, hMem]

/-- Adding a non-observable thread to runnable preserves low-equivalence projection. -/
theorem ensureRunnable_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hTidHigh : threadObservable ctx observer tid = false) :
    projectState ctx observer (ensureRunnable st tid) = projectState ctx observer st := by
  have hObj := projectObjects_of_objectsAgreeOffRunLinks ctx observer
    (ensureRunnable_objectsAgreeOffRunLinks st tid)
  -- AN10-B: post-migration `ensureRunnable` reads via `getTcb?`.
  unfold ensureRunnable at hObj ⊢
  split
  · rfl
  · rename_i hNotMem
    cases hTcb : st.getTcb? tid with
    | none => rfl
    | some tcb =>
          simp only [hNotMem, hTcb] at hObj
          by_cases hAdm : st.runEnqueueAdmits bootCoreId tid = true
          case neg => simp only [hAdm, Bool.false_eq_true, if_false]
          simp only [hAdm, if_true] at hObj ⊢
          have hD := SystemState.runEnqueueAdmitted_onlyObjectsSchedulerDiffer st bootCoreId tid
            tcb.boostedPriority
          unfold SystemState.onlyObjectsSchedulerDiffer at hD
          rw [hD] at hObj ⊢
          -- the enqueue frames every projection except the objects (equal off
          -- run-queue fields) and projectRunnable.
          simp only [projectState, projectCurrent, projectActiveDomain, projectDomainTimeRemaining,
            projectDomainScheduleIndex, projectMachineRegs,
            SystemState.runEnqueueAdmitted_scheduler,
            SchedulerState.markReschedulePendingOnCore_currentOnCore, SchedulerState.setRunQueueOnCore_currentOnCore,
            SchedulerState.setRunQueueEndsOnCore_currentOnCore,
            SchedulerState.markReschedulePendingOnCore_activeDomainOnCore, SchedulerState.setRunQueueOnCore_activeDomainOnCore,
            SchedulerState.setRunQueueEndsOnCore_activeDomainOnCore,
            SchedulerState.markReschedulePendingOnCore_domainTimeRemainingOnCore, SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore,
            SchedulerState.setRunQueueEndsOnCore_domainTimeRemainingOnCore,
            SchedulerState.markReschedulePendingOnCore_domainScheduleIndexOnCore, SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore,
            SchedulerState.setRunQueueEndsOnCore_domainScheduleIndexOnCore]
          congr 1
          simp only [projectRunnable, SchedulerState.runnable,
            SchedulerState.markReschedulePendingOnCore_runQueueOnCore, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          exact RunQueue.toList_filter_insert_neg' _ _ _ _ hTidHigh

/-- storeTcbIpcState at a non-observable object preserves projection (single-state). -/
theorem storeTcbIpcState_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeTcbIpcState modifyTcb at hStep
  cases hLookup : lookupTcb st tid with
  | none =>
    simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb (tcb.setIpcState ipc)) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have := Except.ok.inj hStep; subst this
      simp only [projectState]; congr 1
      · -- projectObjects: storeObject at non-observable tid.toObjId
        funext oid
        by_cases hObs : objectObservable ctx observer oid
        · simp [projectObjects, hObs, SystemState.getObject?]
          by_cases hEq : oid = tid.toObjId
          · subst hEq; simp [hTidObjHigh] at hObs
          · exact congrArg (Option.map (projectKernelObject ctx observer))
              (storeObject_objects_ne st pair.2 tid.toObjId oid _ hEq hObjInv hStore)
        · simp [projectObjects, hObs]
      · -- projectRunnable: scheduler preserved by storeObject
        simp [projectRunnable, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- projectCurrent: scheduler preserved by storeObject
        simp [projectCurrent, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- activeDomain: scheduler preserved by storeObject
        simp [projectActiveDomain, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- irqHandlers: preserved by storeObject
        funext irq; simp only [projectIrqHandlers, storeObject_irqHandlers_eq st pair.2 tid.toObjId _ hStore]
      · -- objectIndex: non-observable target
        exact storeObject_preserves_projectObjectIndex ctx observer st pair.2 tid.toObjId _ hTidObjHigh hStore
      · -- WS-H8: domainTimeRemaining
        simp [projectDomainTimeRemaining, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- WS-H8: domainSchedule
        simp [projectDomainSchedule, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- WS-H8: domainScheduleIndex
        simp [projectDomainScheduleIndex, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · -- WS-H10: machineRegs
        simp [projectMachineRegs, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore,
              storeObject_machine_eq st pair.2 tid.toObjId _ hStore]
      · -- R5-C.1: memory
        exact storeObject_preserves_projectMemory ctx observer st pair.2 tid.toObjId _ hStore

/-- WS-H9: storeTcbPendingMessage at a non-observable object preserves projection. -/
theorem storeTcbPendingMessage_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeTcbPendingMessage modifyTcb at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      simp only [projectState]; congr 1
      · funext oid; by_cases hObs : objectObservable ctx observer oid
        · simp [projectObjects, hObs, SystemState.getObject?]
          by_cases hEq : oid = tid.toObjId
          · subst hEq; simp [hTidObjHigh] at hObs
          · exact congrArg (Option.map (projectKernelObject ctx observer))
              (storeObject_objects_ne st pair.2 tid.toObjId oid _ hEq hObjInv hStore)
        · simp [projectObjects, hObs]
      · simp [projectRunnable, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectCurrent, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectActiveDomain, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · funext irq; simp only [projectIrqHandlers, storeObject_irqHandlers_eq st pair.2 tid.toObjId _ hStore]
      · exact storeObject_preserves_projectObjectIndex ctx observer st pair.2 tid.toObjId _ hTidObjHigh hStore
      · simp [projectDomainTimeRemaining, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectDomainSchedule, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectDomainScheduleIndex, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectMachineRegs, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore,
              storeObject_machine_eq st pair.2 tid.toObjId _ hStore]
      · -- R5-C.1: memory
        exact storeObject_preserves_projectMemory ctx observer st pair.2 tid.toObjId _ hStore

/-- WS-H9: storeTcbIpcStateAndMessage at a non-observable object preserves projection. -/
theorem storeTcbIpcStateAndMessage_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeTcbIpcStateAndMessage modifyTcb at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId
        (.tcb (TCB.setIpcState { tcb with pendingMessage := msg } ipc)) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      simp only [projectState]; congr 1
      · funext oid; by_cases hObs : objectObservable ctx observer oid
        · simp [projectObjects, hObs, SystemState.getObject?]
          by_cases hEq : oid = tid.toObjId
          · subst hEq; simp [hTidObjHigh] at hObs
          · exact congrArg (Option.map (projectKernelObject ctx observer))
              (storeObject_objects_ne st pair.2 tid.toObjId oid _ hEq hObjInv hStore)
        · simp [projectObjects, hObs]
      · simp [projectRunnable, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectCurrent, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectActiveDomain, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · funext irq; simp only [projectIrqHandlers, storeObject_irqHandlers_eq st pair.2 tid.toObjId _ hStore]
      · exact storeObject_preserves_projectObjectIndex ctx observer st pair.2 tid.toObjId _ hTidObjHigh hStore
      · simp [projectDomainTimeRemaining, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectDomainSchedule, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectDomainScheduleIndex, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore]
      · simp [projectMachineRegs, storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore,
              storeObject_machine_eq st pair.2 tid.toObjId _ hStore]
      · -- R5-C.1: memory
        exact storeObject_preserves_projectMemory ctx observer st pair.2 tid.toObjId _ hStore

/-- storeObject at a non-observable object preserves projection (single-state). -/
theorem storeObject_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hOidHigh : objectObservable ctx observer oid = false)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · funext o
    by_cases hObs : objectObservable ctx observer o
    · simp [projectObjects, hObs, SystemState.getObject?]
      by_cases hEq : o = oid
      · subst hEq; simp [hOidHigh] at hObs
      · exact congrArg (Option.map (projectKernelObject ctx observer))
          (storeObject_objects_ne st st' oid o obj hEq hObjInv hStore)
    · simp [projectObjects, hObs]
  · simp [projectRunnable, storeObject_scheduler_eq st st' oid obj hStore]
  · simp [projectCurrent, storeObject_scheduler_eq st st' oid obj hStore]
  · simp [projectActiveDomain, storeObject_scheduler_eq st st' oid obj hStore]
  · funext irq; simp only [projectIrqHandlers, storeObject_irqHandlers_eq st st' oid obj hStore]
  · exact storeObject_preserves_projectObjectIndex ctx observer st st' oid obj hOidHigh hStore
  · simp [projectDomainTimeRemaining, storeObject_scheduler_eq st st' oid obj hStore]
  · simp [projectDomainSchedule, storeObject_scheduler_eq st st' oid obj hStore]
  · simp [projectDomainScheduleIndex, storeObject_scheduler_eq st st' oid obj hStore]
  · simp [projectMachineRegs, storeObject_scheduler_eq st st' oid obj hStore,
          storeObject_machine_eq st st' oid obj hStore]
  · -- R5-C.1: memory
    exact storeObject_preserves_projectMemory ctx observer st st' oid obj hStore

/-- Finding F-1: `storeTcbReceiveComplete` at a non-observable object preserves
projection.  The store touches only the (non-observable) target TCB; the extra
`pendingReceiveReply := none` is erased by `projectKernelObject` regardless.  Mirror of
`storeTcbIpcStateAndMessage_preserves_projection`, delegating to the field-agnostic
`storeObject_preserves_projection`. -/
theorem storeTcbReceiveComplete_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold storeTcbReceiveComplete modifyTcb at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId
        (.tcb (TCB.setIpcState { tcb with pendingMessage := msg, pendingReceiveReplyCode := 0 } .ready)) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      obtain ⟨⟨⟩, st''⟩ := pair
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      exact storeObject_preserves_projection ctx observer st st'' tid.toObjId _ hTidObjHigh hObjInv hStore

/-- **WS-RR RR7.22 (residual, remediation)**: storing an object whose
**projection** equals the projection of the one already at that key preserves
`projectState` — *unconditionally*, even at a low-visible key.

This is the general form of the reply-`caller` lemma below, which had been the
only instance: the argument never depended on the field being `Reply.caller`, only
on `projectKernelObject` erasing whatever changed.  Stating it once means a new
projection-stripped field (`schedContextBinding` and `SchedContext.boundThread`,
for the donation hand-off) is a two-line corollary rather than a second copy of
this case analysis.

`hIdxContains` is what keeps `objectIndex` still: the key already exists, so
`storeObject` does not extend the identity registry. -/
theorem storeObject_projectionStable_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj old : KernelObject)
    (hPrev : st.objects[oid]? = some old)
    (hProj : projectKernelObject ctx observer obj = projectKernelObject ctx observer old)
    (hIdxContains : st.objectIndexSet.contains oid = true)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  simp only [projectState]; congr 1
  · funext o
    by_cases hObs : objectObservable ctx observer o
    · simp [projectObjects, hObs, SystemState.getObject?]
      by_cases hEq : o = oid
      · subst hEq
        rw [storeObject_objects_eq st st' o _ hObjInv hStore, hPrev]
        simp only [Option.map_some]
        exact congrArg some hProj
      · exact congrArg (Option.map (projectKernelObject ctx observer))
          (storeObject_objects_ne st st' oid o _ hEq hObjInv hStore)
    · simp [projectObjects, hObs]
  · simp [projectRunnable, storeObject_scheduler_eq st st' oid _ hStore]
  · simp [projectCurrent, storeObject_scheduler_eq st st' oid _ hStore]
  · simp [projectActiveDomain, storeObject_scheduler_eq st st' oid _ hStore]
  · funext irq; simp only [projectIrqHandlers, storeObject_irqHandlers_eq st st' oid _ hStore]
  · unfold storeObject at hStore; cases hStore
    simp only [projectObjectIndex, hIdxContains, if_true]
  · simp [projectDomainTimeRemaining, storeObject_scheduler_eq st st' oid _ hStore]
  · simp [projectDomainSchedule, storeObject_scheduler_eq st st' oid _ hStore]
  · simp [projectDomainScheduleIndex, storeObject_scheduler_eq st st' oid _ hStore]
  · simp [projectMachineRegs, storeObject_scheduler_eq st st' oid _ hStore,
          storeObject_machine_eq st st' oid _ hStore]
  · exact storeObject_preserves_projectMemory ctx observer st st' oid _ hStore

/-- WS-OD OD3.2: **the donation return's reply-stack head clear is invisible to
every observer.**

The pop resets the popped Reply's `next` and `prev`, and
`projectKernelObject` strips both (OD2.2), so the write is projection-stable
whether or not the Reply is low-visible — the same reason the binding hand-off
itself is invisible.  An instance of
`storeObject_projectionStable_preserves_projection`, so a projection hop over the
donation return is one more rewrite rather than a second case analysis. -/
theorem storeDonationHeadClear_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hIdxComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadClear head? st = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, hRead, hS⟩
  · rfl
  · exact storeObject_projectionStable_preserves_projection ctx observer st st' rid.toObjId
      _ (.reply r) hRead
      (projectKernelObject_reply_stackLinks_invariant ctx observer r none none)
      (hIdxComplete rid.toObjId (by rw [hRead]; intro hx; cases hx))
      hObjInv hS

/-- **Recording a Reply's stasher is invisible to every observer.**  It is
nothing or one store of the Reply with its `stasherCode` set, which
`projectKernelObject` erases, so it is projection-stable whether or not the
Reply is low-visible. -/
theorem recordReplyStasher_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (code : Nat) (recv : SeLe4n.ThreadId)
    (hIdxComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (st.recordReplyStasher code recv) = projectState ctx observer st := by
  rcases SystemState.recordReplyStasher_eq_or st code recv with h | ⟨rid, r, _, hRead, hS⟩
  · rw [h]
  · exact storeObject_projectionStable_preserves_projection ctx observer st _ rid.toObjId
      _ (.reply r) hRead
      (projectKernelObject_reply_stasher_invariant ctx observer r _)
      (hIdxComplete rid.toObjId (by rw [hRead]; intro hx; cases hx))
      hObjInv hS

/-- `v0.35.4`: the pop's re-head of the frame below preserves the projection for
the same reason — it writes a Reply's `next`, which `projectKernelObject` strips. -/
theorem storeReplyReHead_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hIdxComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (hObjInv : st.objects.invExt)
    (h : storeReplyReHead scId head? st = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, hRead, hS⟩
  · rfl
  · exact storeObject_projectionStable_preserves_projection ctx observer st st' rid.toObjId
      _ (.reply r) hRead
      (projectKernelObject_reply_next_invariant ctx observer r (some (.head scId)))
      (hIdxComplete rid.toObjId (by rw [hRead]; intro hx; cases hx))
      hObjInv hS

/-- `v0.35.4`: the whole pop — the unlink and the re-head — preserves the
projection, composed from its two stores.  The re-head reads the index
completeness at the intermediate state, which the unlink store carries forward. -/
theorem storeDonationHeadPop_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hIdxComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (hSetInv : st.objectIndexSet.table.invExt)
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · rfl
  · have hInv1 := storeDonationHeadClear_preserves_objects_invExt hObjInv hClear
    have hC1 := storeDonationHeadClear_preserves_objectIndexSetComplete hObjInv hSetInv
      hIdxComplete hClear
    rw [storeReplyReHead_preserves_projection ctx observer hC1 hInv1 hReHead,
      storeDonationHeadClear_preserves_projection ctx observer hIdxComplete hObjInv hClear]

/-- `v0.35.4`: **the donation push's two Reply writes preserve the projection** —
the pushed frame gains its stack links and the old head its upward link, and
`projectKernelObject` strips both, so the push is unobservable through a
low-visible Reply.  The old head's index membership is read at the intermediate
state, which the first store carries forward. -/
theorem storeDonationFramePush_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hIdxComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (hSetInv : st.objectIndexSet.table.invExt)
    (hObjInv : st.objects.invExt)
    (hPre : st.getReply? pushRid = some pushReply)
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  obtain ⟨_, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have hPreObj := (SystemState.getReply?_eq_some_iff _ _ _).mp hPre
  have hP1 : projectState ctx observer s1 = projectState ctx observer st :=
    storeObject_projectionStable_preserves_projection ctx observer st s1 pushRid.toObjId
      _ (.reply pushReply) hPreObj
      (projectKernelObject_reply_stackLinks_invariant ctx observer pushReply oldHead?
        (some (.head scId)))
      (hIdxComplete pushRid.toObjId (by rw [hPreObj]; intro hx; cases hx))
      hObjInv hS1
  rcases hRest with ⟨_, rfl⟩ | ⟨old, oldR, _, hOldR, hS2⟩
  · exact hP1
  · have hInv1 := SeLe4n.Model.storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
    have hC1 := SeLe4n.Model.storeObject_preserves_objectIndexSetComplete st s1 _ _ hObjInv
      hSetInv hIdxComplete hS1
    have hOldObj := (SystemState.getReply?_eq_some_iff _ _ _).mp hOldR
    rw [storeObject_projectionStable_preserves_projection ctx observer s1 st' old.toObjId
      _ (.reply oldR) hOldObj
      (projectKernelObject_reply_next_invariant ctx observer oldR (some (.frame pushRid)))
      (hC1 old.toObjId (by rw [hOldObj]; intro hx; cases hx))
      hInv1 hS2, hP1]

/-- `v0.35.4`: the `O(1)` removal preserves the projection — **WS-HP HP6.5**: its
two or three writes move a Reply's stack links, and `projectKernelObject` strips
both, so the removal is unobservable through a low-visible Reply.

The frame below the cut is written at the *intermediate* state, so its index
membership is read there and carried forward by the first store — the shape
`storeDonationFramePush_preserves_projection` already uses for its own second
write, and the reason this gained `hSetInv` when the sever became a splice. -/
theorem spliceReplyFrameOut_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hIdxComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (hSetInv : st.objectIndexSet.table.invExt)
    (hObjInv : st.objects.invExt)
    (h : spliceReplyFrameOut st rid = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  rcases spliceReplyFrameOut_cases h with rfl | ⟨r, above, a, hR, hN, hA, hP, hS⟩ |
      ⟨r, below, b, hR, hN, _, hB, hBn, hS⟩
  · rfl
  rotate_left
  · -- The cut from the frame below: its `next`, then the cut frame's `prev`.
    obtain ⟨s1, hS1, hS2⟩ := severReplyFrameBelowStores_cases hS
    have hBObj := (SystemState.getReply?_eq_some_iff _ _ _).mp hB
    have hP1 : projectState ctx observer s1 = projectState ctx observer st :=
      storeObject_projectionStable_preserves_projection ctx observer st s1 below.toObjId
        _ (.reply b) hBObj
        (projectKernelObject_reply_next_invariant ctx observer b none)
        (hIdxComplete below.toObjId (by rw [hBObj]; intro hx; cases hx))
        hObjInv hS1
    have hInv1 := SeLe4n.Model.storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
    have hC1 := SeLe4n.Model.storeObject_preserves_objectIndexSetComplete st s1 _ _ hObjInv
      hSetInv hIdxComplete hS1
    have hRObj1 : s1.objects[rid.toObjId]? = some (.reply r) := by
      rw [SeLe4n.Model.storeObject_objects_ne st s1 below.toObjId rid.toObjId _
        (fun e => severReplyFrameBelow_ne hR hN hB hBn e.symm) hObjInv hS1]
      exact (SystemState.getReply?_eq_some_iff _ _ _).mp hR
    rw [storeObject_projectionStable_preserves_projection ctx observer s1 st' rid.toObjId
      _ (.reply r) hRObj1
      (projectKernelObject_reply_prev_invariant ctx observer r none)
      (hC1 rid.toObjId (by rw [hRObj1]; intro hx; cases hx))
      hInv1 hS2, hP1]
  · have hAObj := (SystemState.getReply?_eq_some_iff _ _ _).mp hA
    rcases spliceReplyFrameStores_cases hS with ⟨s1, _, hS1, hS2⟩ |
      ⟨below, b, s1, s2, hBelow, hS1, hS2, hS3⟩
    · have hP1 : projectState ctx observer s1 = projectState ctx observer st :=
        storeObject_projectionStable_preserves_projection ctx observer st s1 above.toObjId
          _ (.reply a) hAObj
          (by rw [Reply.unlinkedFrom_eq]
              exact projectKernelObject_reply_stackLinks_invariant ctx observer a _ _)
          (hIdxComplete above.toObjId (by rw [hAObj]; intro hx; cases hx))
          hObjInv hS1
      have hInv1 := SeLe4n.Model.storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
      have hC1 := SeLe4n.Model.storeObject_preserves_objectIndexSetComplete st s1 _ _ hObjInv
        hSetInv hIdxComplete hS1
      rcases spliceReplyFrameStores_sever_cut_read hObjInv hR hA hS1 with hR1 | hR1
      · have hRObj1 := (SystemState.getReply?_eq_some_iff _ _ _).mp hR1
        rw [storeObject_projectionStable_preserves_projection ctx observer s1 st' rid.toObjId
          _ (.reply r) hRObj1
          (projectKernelObject_reply_stackLinks_invariant ctx observer r none none)
          (hC1 rid.toObjId (by rw [hRObj1]; intro hx; cases hx))
          hInv1 hS2, hP1]
      · have hRObj1 := (SystemState.getReply?_eq_some_iff _ _ _).mp hR1
        rw [storeObject_projectionStable_preserves_projection ctx observer s1 st' rid.toObjId
          _ (.reply (r.unlinkedFrom rid)) hRObj1
          ((projectKernelObject_reply_stackLinks_invariant ctx observer r none none).trans
            (by rw [Reply.unlinkedFrom_eq]
                exact (projectKernelObject_reply_stackLinks_invariant ctx observer r _ _).symm))
          (hC1 rid.toObjId (by rw [hRObj1]; intro hx; cases hx))
          hInv1 hS2, hP1]
    · obtain ⟨_, hNe, hB, _⟩ := spliceFrameBelow?_eq_some hBelow
      have hNeBR : below ≠ rid := spliceFrameBelow?_ne_cut hR hN hBelow
      have hNeAR : above ≠ rid := spliceFrameBelow?_above_ne_cut hR hA hP hBelow
      have hRObj := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
      have hP1 : projectState ctx observer s1 = projectState ctx observer st :=
        storeObject_projectionStable_preserves_projection ctx observer st s1 above.toObjId
          _ (.reply a) hAObj
          (projectKernelObject_reply_prev_invariant ctx observer a (some below))
          (hIdxComplete above.toObjId (by rw [hAObj]; intro hx; cases hx))
          hObjInv hS1
      have hInv1 := SeLe4n.Model.storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
      have hSetInv1 := SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt st s1 _ _
        hSetInv hS1
      have hC1 := SeLe4n.Model.storeObject_preserves_objectIndexSetComplete st s1 _ _ hObjInv
        hSetInv hIdxComplete hS1
      have hBObj1 : s1.objects[below.toObjId]? = some (.reply b) := by
        rw [SeLe4n.Model.storeObject_objects_ne st s1 above.toObjId below.toObjId _
          (fun hEq => hNe (SeLe4n.ReplyId.toObjId_injective _ _ hEq)) hObjInv hS1]
        exact (SystemState.getReply?_eq_some_iff _ _ _).mp hB
      have hP2 : projectState ctx observer s2 = projectState ctx observer s1 :=
        storeObject_projectionStable_preserves_projection ctx observer s1 s2 below.toObjId
          _ (.reply b) hBObj1
          (projectKernelObject_reply_next_invariant ctx observer b (some (.frame above)))
          (hC1 below.toObjId (by rw [hBObj1]; intro hx; cases hx))
          hInv1 hS2
      have hInv2 := SeLe4n.Model.storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2
      have hC2 := SeLe4n.Model.storeObject_preserves_objectIndexSetComplete s1 s2 _ _ hInv1
        hSetInv1 hC1 hS2
      have hRObj2 : s2.objects[rid.toObjId]? = some (.reply r) := by
        rw [SeLe4n.Model.storeObject_objects_ne s1 s2 below.toObjId rid.toObjId _
          (fun hEq => hNeBR (SeLe4n.ReplyId.toObjId_injective _ _ hEq).symm) hInv1 hS2,
          SeLe4n.Model.storeObject_objects_ne st s1 above.toObjId rid.toObjId _
            (fun hEq => hNeAR (SeLe4n.ReplyId.toObjId_injective _ _ hEq).symm) hObjInv hS1]
        exact hRObj
      rw [storeObject_projectionStable_preserves_projection ctx observer s2 st' rid.toObjId
        _ (.reply r) hRObj2
        (projectKernelObject_reply_stackLinks_invariant ctx observer r none none)
        (hC2 rid.toObjId (by rw [hRObj2]; intro hx; cases hx))
        hInv2 hS3, hP2, hP1]

/-- WS-SM SM6.D (#7.1 fold): writing only a Reply object's `caller` back-link (the
fold's atomic `linkCallerReply` reply-write) preserves `projectState`
**unconditionally** — even when the Reply object is low-visible — because
`projectKernelObject` strips `caller` to `none`.  No `objectObservable`-HIGH
hypothesis on `rid` is required (unlike the general `storeObject_preserves_projection`).
WS-RR RR7.22 (residual, remediation) made it the instance of
`storeObject_projectionStable_preserves_projection` it always was. -/
theorem storeObject_reply_caller_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (rid : SeLe4n.ObjId) (r : SeLe4n.Kernel.Reply)
    (c : Option SeLe4n.ThreadId)
    (hPrev : st.objects[rid]? = some (.reply r))
    (hIdxContains : st.objectIndexSet.contains rid = true)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject rid (.reply { r with callerCode := SeLe4n.ThreadId.optCode c }) st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st :=
  storeObject_projectionStable_preserves_projection ctx observer st st' rid _ _ hPrev
    (projectKernelObject_reply_caller_invariant ctx observer r c) hIdxContains hObjInv hStore

/-- WS-SM SM6.D (#7.1 fold): the fold's atomic `linkCallerReply` (the reply-link
the receive transition now performs in-line) preserves `projectState` whenever the
linked **caller** is high (`hCallerObjHigh`) — its two writes are both invisible to
any observer: the `.reply` `caller := some caller` write is projection-stripped
(`storeObject_reply_caller_preserves_projection`), and the caller-TCB
`replyObject := some rid` write is on a high TCB (`storeObject_preserves_projection`).
`hIdxComplete` supplies the `objectIndex` membership of the (already-present) Reply.
Used by the receive-transition non-interference proof at the Call rendezvous, where
the dequeued caller is high. -/
theorem linkCallerReply_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
    (hIdxComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold SystemState.linkCallerReply at hStep
  cases hLink : SystemState.linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hObjInv1 := SystemState.linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
    have hProj1 : projectState ctx observer st1 = projectState ctx observer st := by
      unfold SystemState.linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => rw [hGetR] at hLink; simp at hLink
      | some r =>
        simp only [hGetR] at hLink
        split at hLink
        · have hRidPrev : st.objects[rid.toObjId]? = some (.reply r) :=
            (SystemState.getReply?_eq_some_iff st rid r).mp hGetR
          exact storeObject_reply_caller_preserves_projection ctx observer st st1
            rid.toObjId r (some caller) hRidPrev
            (hIdxComplete rid.toObjId (by rw [hRidPrev]; exact Option.some_ne_none _)) hObjInv hLink
        · simp at hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · rw [storeObject_preserves_projection ctx observer st1 st' caller.toObjId _
              hCallerObjHigh hObjInv1 hStep, hProj1]
      · simp at hStep

/-- PR #827 #3 fold: `consumeCallerReply` (the fold's atomic reply-link teardown)
preserves `projectState` whenever the answered **caller** is high
(`hCallerObjHigh`) — its two writes are both invisible to any observer: the
`.reply` `caller := none` write is projection-stripped
(`storeObject_reply_caller_preserves_projection` — `projectKernelObject` erases
`Reply.caller` structurally), and the caller-TCB `replyObject := none` write is
on a high TCB (`storeObject_preserves_projection`).  `hIdxComplete` supplies the
`objectIndex` membership of the (already-present) Reply.  The non-interference
building block for the reply primitives' in-transition consume. -/
theorem consumeCallerReply_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
    (hIdxComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (hObjInv : st.objects.invExt)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold SystemState.consumeCallerReply at hStep
  cases hCons : SystemState.consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have hObjInv1 := SystemState.consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
    have hProj1 : projectState ctx observer st1 = projectState ctx observer st := by
      unfold SystemState.consumeReply at hCons
      cases hGet : st.getReply? rid with
      | none => rw [hGet] at hCons; cases hCons; rfl
      | some r =>
        rw [hGet] at hCons
        have hRidPrev : st.objects[rid.toObjId]? = some (.reply r) :=
          (SystemState.getReply?_eq_some_iff st rid r).mp hGet
        exact storeObject_projectionStable_preserves_projection ctx observer st st1
          rid.toObjId _ (.reply r) hRidPrev
          (projectKernelObject_reply_consumed_invariant ctx observer r)
          (hIdxComplete rid.toObjId (by rw [hRidPrev]; exact Option.some_ne_none _)) hObjInv hCons
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]; exact hProj1
    | some tcb =>
      simp only [hT] at hStep
      rw [storeObject_preserves_projection ctx observer st1 st' caller.toObjId _
            hCallerObjHigh hObjInv1 hStep, hProj1]

/-- WS-RM (`v0.35.6`): the fold preserves the projection unconditionally — its
writes move a Reply's stack links, which `projectKernelObject` strips. -/
theorem spliceReplyFrameOutOrSelf_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (rid : SeLe4n.ReplyId)
    (hIdxComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (hSetInv : st.objectIndexSet.table.invExt)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (spliceReplyFrameOutOrSelf st rid)
      = projectState ctx observer st := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]
  · exact spliceReplyFrameOut_preserves_projection ctx observer hIdxComplete hSetInv hObjInv h

/-- WS-RM (`v0.35.6`): the fold preserves index-set completeness — it stores at a
key that already resolves, so the set it would have to name already names it. -/
theorem spliceReplyFrameOutOrSelf_preserves_objectIndexSetComplete
    (st : SystemState) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st) :
    SeLe4n.Model.objectIndexSetComplete (spliceReplyFrameOutOrSelf st rid) := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]; exact hIdxComplete
  · rcases spliceReplyFrameOut_cases h with hEq | ⟨r, above, a, _, _, hA, _, hS⟩ |
        ⟨r, below, b, _, _, _, _, _, hS⟩
    · rw [hEq]; exact hIdxComplete
    rotate_left
    · obtain ⟨s1, hS1, hS2⟩ := severReplyFrameBelowStores_cases hS
      have hInv1 := SeLe4n.Model.storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
      have hSetInv1 := SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt st s1 _ _
        hObjSetInv hS1
      exact storeObject_preserves_objectIndexSetComplete s1 _ rid.toObjId _ hInv1 hSetInv1
        (storeObject_preserves_objectIndexSetComplete st s1 below.toObjId _ hObjInv
          hObjSetInv hIdxComplete hS1) hS2
    · rcases spliceReplyFrameStores_cases hS with ⟨s1, _, hS1, hS2⟩ |
        ⟨below, b, s1, s2, hBelow, hS1, hS2, hS3⟩
      · exact storeObject_preserves_objectIndexSetComplete s1 _ rid.toObjId _
          (SeLe4n.Model.storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1)
          (SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt st s1 _ _ hObjSetInv hS1)
          (storeObject_preserves_objectIndexSetComplete st s1 above.toObjId _ hObjInv
            hObjSetInv hIdxComplete hS1) hS2
      · have hInv1 := SeLe4n.Model.storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
        have hSetInv1 := SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt st s1 _ _
          hObjSetInv hS1
        have hC1 := storeObject_preserves_objectIndexSetComplete st s1 above.toObjId _ hObjInv
          hObjSetInv hIdxComplete hS1
        exact storeObject_preserves_objectIndexSetComplete s2 _ rid.toObjId _
          (SeLe4n.Model.storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2)
          (SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt s1 s2 _ _ hSetInv1 hS2)
          (storeObject_preserves_objectIndexSetComplete s1 s2 below.toObjId _ hInv1
            hSetInv1 hC1 hS2) hS3

/-- WS-RR RR8.5: the thread-keyed fold preserves index-set completeness — the
`OrSelf` lemma under the victim's own `replyObject`.  The reply arm's projection
composite needs completeness at the state the consume runs on, now that the
consume writes through `storeObject`. -/
theorem spliceThreadReplyFrameOut_preserves_objectIndexSetComplete
    (st : SystemState) (tcb : TCB)
    (hObjInv : st.objects.invExt)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st) :
    SeLe4n.Model.objectIndexSetComplete (spliceThreadReplyFrameOut st tcb) := by
  unfold spliceThreadReplyFrameOut
  cases tcb.replyObject with
  | none => exact hIdxComplete
  | some rid =>
    exact spliceReplyFrameOutOrSelf_preserves_objectIndexSetComplete st rid hObjInv
      hObjSetInv hIdxComplete

/-- **WS-RM (`v0.35.6`): `removeCallerReplyFrame` preserves the projection** under
exactly the hypothesis the consume alone needed.  The splice half is
unconditional (`projectKernelObject` erases both stack links), so taking the frame
off its stack costs the information-flow surface one rewrite per write and no new
obligation — the index-set invariant it now threads was already a hypothesis. -/
theorem removeCallerReplyFrame_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
    (hIdxComplete : SeLe4n.Model.objectIndexSetComplete st)
    (hObjInv : st.objects.invExt)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  rw [removeCallerReplyFrame_eq] at hStep
  rw [consumeCallerReply_preserves_projection ctx observer _ st' caller rid hCallerObjHigh
      (spliceReplyFrameOutOrSelf_preserves_objectIndexSetComplete st rid hObjInv hObjSetInv
        hIdxComplete)
      (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv) hStep]
  exact spliceReplyFrameOutOrSelf_preserves_projection ctx observer st rid hIdxComplete
    hObjSetInv hObjInv

/-- WS-SM SM6.D (#7.3 fold): `linkServerStashedReply` preserves the low-observer
projection when both the caller and server objects are non-observable (high).  It
composes `linkCallerReply` (caller-side, projection-preserving at a high caller) with
one server `.tcb` re-store clearing `pendingReceiveReply` (projection-preserving at a
high server). -/
theorem linkServerStashedReply_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (caller server : SeLe4n.ThreadId)
    (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
    (hServerObjHigh : objectObservable ctx observer server.toObjId = false)
    (hIdxComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold SystemState.linkServerStashedReply at hStep
  cases hStash : (st.getTcb? server).bind (·.pendingReceiveReply) with
  | none => simp [hStash] at hStep
  | some rid =>
    simp only [hStash] at hStep
    cases hLink : SystemState.linkCallerReply caller rid st with
    | error e => simp [hLink] at hStep
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hLink] at hStep
      have hObjInv1 := linkCallerReply_preserves_objects_invExt st st1 caller rid hObjInv hLink
      have hProj1 : projectState ctx observer st1 = projectState ctx observer st :=
        linkCallerReply_preserves_projection ctx observer st st1 caller rid hCallerObjHigh hIdxComplete hObjInv hLink
      cases hT : st1.getTcb? server with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep; subst hEq; exact hProj1
      | some sTcb =>
        simp only [hT] at hStep
        rw [storeObject_preserves_projection ctx observer st1 st' server.toObjId _
              hServerObjHigh hObjInv1 hStep, hProj1]

-- ============================================================================
-- Non-interference theorem #1: chooseThread (WS-D2, F-05, TPI-D01)
-- ============================================================================

/-- Choosing the next thread does not leak high-domain scheduling decisions. -/
theorem chooseThread_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (next₁ next₂ : Option SeLe4n.ThreadId)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : chooseThread s₁ = .ok (next₁, s₁'))
    (hStep₂ : chooseThread s₂ = .ok (next₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hEq₁ : s₁' = s₁ := chooseThread_preserves_state s₁ s₁' next₁ hStep₁
  have hEq₂ : s₂' = s₂ := chooseThread_preserves_state s₂ s₂' next₂ hStep₂
  subst hEq₁; subst hEq₂
  exact hLow

-- ============================================================================
-- Non-interference theorem #3: cspaceMint (WS-D2, F-05, TPI-D02)
-- ============================================================================

/-- Minting a capability in a non-observable CNode preserves low-equivalence. -/
theorem cspaceMint_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (_hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : cspaceMint src dst rights badge s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceMint src dst rights badge s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  rcases cspaceMint_child_attenuates s₁ s₁' src dst rights badge hObjInv₁ hStep₁ with
    ⟨parent₁, child₁, hLookup₁, _, _⟩
  rcases cspaceMint_child_attenuates s₂ s₂' src dst rights badge hObjInv₂ hStep₂ with
    ⟨parent₂, child₂, hLookup₂, _, _⟩
  unfold cspaceMint at hStep₁ hStep₂
  rw [hLookup₁] at hStep₁; rw [hLookup₂] at hStep₂
  -- AL1b (AK7-I.cascade): promote parent₁/parent₂ via toNonNull? on both branches.
  have hNotNull₁ : parent₁.isNull = false := by
    by_cases h : parent₁.isNull
    · exfalso; simp [Capability.toNonNull?, h] at hStep₁
    · exact Bool.not_eq_true _ |>.mp h
  have hNotNull₂ : parent₂.isNull = false := by
    by_cases h : parent₂.isNull
    · exfalso; simp [Capability.toNonNull?, h] at hStep₂
    · exact Bool.not_eq_true _ |>.mp h
  have hToNN₁ : parent₁.toNonNull? = some ⟨parent₁, hNotNull₁⟩ :=
    Capability.toNonNull?_of_not_null hNotNull₁
  have hToNN₂ : parent₂.toNonNull? = some ⟨parent₂, hNotNull₂⟩ :=
    Capability.toNonNull?_of_not_null hNotNull₂
  cases hMint₁ : mintDerivedCap ⟨parent₁, hNotNull₁⟩ rights badge with
  | error e => simp [hToNN₁, hMint₁] at hStep₁
  | ok c₁ =>
    cases hMint₂ : mintDerivedCap ⟨parent₂, hNotNull₂⟩ rights badge with
    | error e => simp [hToNN₂, hMint₂] at hStep₂
    | ok c₂ =>
      have hInsert₁ : cspaceInsertSlot dst c₁ s₁ = .ok ((), s₁') := by
        simpa [hToNN₁, hMint₁] using hStep₁
      have hInsert₂ : cspaceInsertSlot dst c₂ s₂ = .ok ((), s₂') := by
        simpa [hToNN₂, hMint₂] using hStep₂
      have hObjLow := congrArg ObservableState.objects hLow
      have hRunLow := congrArg ObservableState.runnable hLow
      have hCurLow := congrArg ObservableState.current hLow
      have hSched₁ := cspaceInsertSlot_preserves_scheduler s₁ s₁' dst c₁ hInsert₁
      have hSched₂ := cspaceInsertSlot_preserves_scheduler s₂ s₂' dst c₂ hInsert₂
      unfold lowEquivalent projectState
      congr 1
      · funext oid
        by_cases hObs : objectObservable ctx observer oid
        · have hNeDst : oid ≠ dst.cnode := by intro hEq; subst hEq; simp [hDstHigh] at hObs
          have hObj₁ := cspaceInsertSlot_preserves_objects_ne s₁ s₁' dst c₁ oid hNeDst hObjInv₁ hInsert₁
          have hObj₂ := cspaceInsertSlot_preserves_objects_ne s₂ s₂' dst c₂ oid hNeDst hObjInv₂ hInsert₂
          simp only [projectObjects, hObs, ite_true, SystemState.getObject?]
          rw [hObj₁, hObj₂]
          have hBase := congrFun hObjLow oid
          simp only [projectState, projectObjects, hObs, ite_true, SystemState.getObject?] at hBase
          exact hBase
        · simp [projectObjects, hObs]
      · simpa [projectRunnable, hSched₁, hSched₂] using hRunLow
      · simpa [projectCurrent, hSched₁, hSched₂] using hCurLow
      · -- activeDomain
        simpa [projectActiveDomain, hSched₁, hSched₂] using congrArg ObservableState.activeDomain hLow
      · -- irqHandlers
        funext irq
        simp only [projectIrqHandlers]
        rw [cspaceInsertSlot_preserves_irqHandlers s₁ s₁' dst c₁ hInsert₁,
            cspaceInsertSlot_preserves_irqHandlers s₂ s₂' dst c₂ hInsert₂]
        exact congrFun (congrArg ObservableState.irqHandlers hLow) irq
      · -- objectIndex
        rw [cspaceInsertSlot_preserves_projectObjectIndex s₁ s₁' dst c₁ hDstHigh hInsert₁,
            cspaceInsertSlot_preserves_projectObjectIndex s₂ s₂' dst c₂ hDstHigh hInsert₂]
        exact congrArg ObservableState.objectIndex hLow
      · -- domainTimeRemaining
        simpa [projectDomainTimeRemaining, hSched₁, hSched₂] using congrArg ObservableState.domainTimeRemaining hLow
      · -- domainSchedule
        simpa [projectDomainSchedule, hSched₁, hSched₂] using congrArg ObservableState.domainSchedule hLow
      · -- domainScheduleIndex
        simpa [projectDomainScheduleIndex, hSched₁, hSched₂] using congrArg ObservableState.domainScheduleIndex hLow
      · -- machineRegs
        simp [projectMachineRegs, hSched₁, hSched₂,
          cspaceInsertSlot_preserves_machine s₁ s₁' dst c₁ hInsert₁,
          cspaceInsertSlot_preserves_machine s₂ s₂' dst c₂ hInsert₂]
        exact congrArg ObservableState.machineRegs hLow
      · -- R5-C.1: memory
        rw [projectMemory_eq_of_memory_eq ctx observer s₁' s₁
              (by rw [cspaceInsertSlot_preserves_machine s₁ s₁' dst c₁ hInsert₁]),
            projectMemory_eq_of_memory_eq ctx observer s₂' s₂
              (by rw [cspaceInsertSlot_preserves_machine s₂ s₂' dst c₂ hInsert₂])]
        exact congrArg ObservableState.memory hLow

-- ============================================================================
-- Non-interference theorem #4: cspaceRevoke (WS-D2, F-05, TPI-D02)
-- ============================================================================

/-- A step that rewrites only derivation state (the tree and the slots' link
words) is invisible to every observer: the projection reads no tree and clears
every projected CNode's and thread's links. -/
theorem projectState_of_agreeOffDerivationLinks (ctx : LabelingContext)
    (observer : IfObserver) {st st' : SystemState}
    (h : SystemState.objectsAgreeOffDerivationLinks st' st)
    (hF : st' = { st with objects := st'.objects, cdt := st'.cdt }) :
    projectState ctx observer st' = projectState ctx observer st := by
  have hO : projectObjects ctx observer st' = projectObjects ctx observer st := by
    funext oid
    unfold projectObjects SystemState.getObject?
    rcases h oid with e | ⟨cn, cn', ha, hb, hw⟩ | ⟨t, t', ha, hb, hw⟩
    · rw [e]
    · have hp : projectKernelObject ctx observer (.cnode cn') =
          projectKernelObject ctx observer (.cnode cn) :=
        CNode.proj_eq_of_withoutLinks_eq
          (fun c => projectKernelObject ctx observer (.cnode c)) hw
      rw [ha, hb]
      simp only [Option.map_some, hp]
    · -- The projection clears a thread's space-slot links as `withoutLinks` does.
      have hp : projectKernelObject ctx observer (.tcb t') =
          projectKernelObject ctx observer (.tcb t) :=
        (show projectKernelObject ctx observer (.tcb t') =
            projectKernelObject ctx observer (.tcb t'.withoutLinks) from rfl).trans
          (hw ▸ rfl)
      rw [ha, hb]
      simp only [Option.map_some, hp]
  rw [hF]
  simp only [projectState]
  congr 1

/-- Detaching the local revoke's emptied siblings is invisible to every observer:
it writes only derivation state, which the projection does not read. -/
theorem projectState_detachRevokedSlots (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) (sourceSlot : SeLe4n.Slot)
    (target : CapTarget) (hInv : st.objects.invExt) :
    projectState ctx observer (detachRevokedSlots st cnodeId cn sourceSlot target) =
      projectState ctx observer st := by
  obtain ⟨_, h⟩ := detachRevokedSlots_shape st cnodeId cn sourceSlot target
  exact projectState_of_agreeOffDerivationLinks ctx observer (h.agree hInv)
    (by rw [h.cdt]; exact h.fields)

/-- A run of slot-link writes is invisible to every observer: the projection
clears every CNode's link words. -/
theorem projectState_of_linkReach (ctx : LabelingContext) (observer : IfObserver)
    {st₀ st : SystemState} (h : SystemState.linkReach st₀ st) (hInv : st₀.objects.invExt) :
    projectState ctx observer st = projectState ctx observer st₀ :=
  projectState_of_agreeOffDerivationLinks ctx observer (h.agree hInv)
    (by rw [h.cdt]; exact h.fields)

/-- Adding a derivation edge, tree and slot links together, is invisible to
every observer: the projection reads neither. -/
theorem projectState_cdtAddChild (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (p c : SlotRef) (op : DerivationOp) (hInv : st.objects.invExt) :
    projectState ctx observer (st.cdtAddChild p c op) = projectState ctx observer st := by
  rw [projectState_of_linkReach ctx observer (SystemState.cdtAddChild_reach st p c op) hInv]
  exact projectState_of_agreeOffDerivationLinks ctx observer
    (SystemState.objectsAgreeOffDerivationLinks.of_objects_eq rfl) rfl

/-- Moving a derivation node, tree and slot links together, is invisible to
every observer. -/
theorem projectState_cdtMove (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (src dst : SlotRef) (hInv : st.objects.invExt) :
    projectState ctx observer (st.cdtMove src dst) = projectState ctx observer st := by
  rw [projectState_of_linkReach ctx observer (SystemState.cdtMove_reach st src dst) hInv]
  exact projectState_of_agreeOffDerivationLinks ctx observer
    (SystemState.objectsAgreeOffDerivationLinks.of_objects_eq rfl) rfl

/-- Revoking capabilities in a non-observable CNode preserves low-equivalence. -/
theorem cspaceRevoke_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (addr : CSpaceAddr)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCNodeHigh : objectObservable ctx observer addr.cnode = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : cspaceRevoke addr s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceRevoke addr s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hObjLow := congrArg ObservableState.objects hLow
  have hRunLow := congrArg ObservableState.runnable hLow
  have hCurLow := congrArg ObservableState.current hLow
  obtain ⟨par₁, cn₁, t₁, _, hCn₁, hS₁, rfl⟩ := cspaceRevoke_ok_decompose addr s₁ s₁' hStep₁
  obtain ⟨par₂, cn₂, t₂, _, hCn₂, hS₂, rfl⟩ := cspaceRevoke_ok_decompose addr s₂ s₂' hStep₂
  -- The revoked siblings leave the tree and the slot maps, which the observer
  -- does not see; what is left is the one CNode store.
  unfold lowEquivalent
  rw [projectState_detachRevokedSlots ctx observer t₁ _ _ _ _
      (storeObject_preserves_objects_invExt s₁ t₁ _ _ hObjInv₁ hS₁),
    projectState_detachRevokedSlots ctx observer t₂ _ _ _ _
      (storeObject_preserves_objects_invExt s₂ t₂ _ _ hObjInv₂ hS₂)]
  have hC₁ : s₁.objects[addr.cnode]? = some (.cnode cn₁) := by
    unfold SystemState.getCNode? at hCn₁; split at hCn₁ <;> simp_all
  have hC₂ : s₂.objects[addr.cnode]? = some (.cnode cn₂) := by
    unfold SystemState.getCNode? at hCn₂; split at hCn₂ <;> simp_all
  simp [hC₁, storeObject] at hS₁
  simp [hC₂, storeObject] at hS₂
  cases hS₁; cases hS₂
  unfold projectState
  -- `v0.35.78`: past the detach the state is `storeObject`'s record (the
  -- revoke stores once), so its `scheduler` field is `s₁`'s / `s₂`'s
  -- definitionally and `congr 1` closes the runnable and current components
  -- from `hRunLow` and `hCurLow` by assumption; the bullets below are the rest.
  congr 1
  · funext oid
    by_cases hObs : objectObservable ctx observer oid
    · have hNe : oid ≠ addr.cnode := by
        intro hEq; subst hEq; simp [hCNodeHigh] at hObs
      have hBase : projectObjects ctx observer s₁ oid = projectObjects ctx observer s₂ oid :=
        congrFun hObjLow oid
      simp [projectObjects, hObs, SystemState.getObject?] at hBase ⊢
      simp only [RHTable_getElem?_eq_get?]
      rw [RHTable_getElem?_insert _ _ _ hObjInv₁, RHTable_getElem?_insert _ _ _ hObjInv₂]
      simp [Ne.symm hNe]
      exact hBase
    · simp [projectObjects, hObs]
  · -- activeDomain
    simp only [projectActiveDomain]
    exact congrArg ObservableState.activeDomain hLow
  · -- irqHandlers
    funext irq
    simp only [projectIrqHandlers]
    exact congrFun (congrArg ObservableState.irqHandlers hLow) irq
  · -- objectIndex
    simp only [projectObjectIndex]
    have hIdx := congrArg ObservableState.objectIndex hLow
    -- Both sides: if objectIndexSet.contains addr.cnode then idx else addr.cnode :: idx
    -- Since hCNodeHigh filters addr.cnode out, prepending it is invisible
    split <;> split
    · exact hIdx
    · rw [List.filter_cons]; simp [hCNodeHigh]; exact hIdx
    · rw [List.filter_cons]; simp [hCNodeHigh]; exact hIdx
    · rw [List.filter_cons, List.filter_cons]; simp [hCNodeHigh]; exact hIdx
  · -- domainTimeRemaining
    simp only [projectDomainTimeRemaining]
    exact congrArg ObservableState.domainTimeRemaining hLow
  · -- domainSchedule
    simp only [projectDomainSchedule]
    exact congrArg ObservableState.domainSchedule hLow
  · -- domainScheduleIndex
    simp only [projectDomainScheduleIndex]
    exact congrArg ObservableState.domainScheduleIndex hLow
  · -- machineRegs
    simp only [projectMachineRegs]
    exact congrArg ObservableState.machineRegs hLow
  · -- R5-C.1: memory
    funext paddr; simp only [projectMemory]
    exact congrFun (congrArg ObservableState.memory hLow) paddr

-- ============================================================================
-- WS-F3/F-21: notificationSignal non-interference
-- ============================================================================

/-- WS-F3/F-21: notificationSignal at non-observable entities preserves projection.
WS-ZA ZA4.4: a wake also clears the woken head's successor's predecessor link
(seL4's `tcbEPDequeue`), so the successor it relinks must be non-observable too,
as a blocking wait's old tail is. -/
theorem notificationSignal_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (st st' : SystemState)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hWaiterDomain : ∀ ntfn tid, st.objects[notificationId]? = some (.notification ntfn) →
        ntfn.waitHead = some tid → threadObservable ctx observer tid = false)
    (hSuccHigh : ∀ t, notificationSignalSuccessor? st notificationId = some t →
        objectObservable ctx observer t.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold notificationSignal SystemState.getObject? at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp [hObj] at hStep
    | notification ntfn =>
      simp [hObj] at hStep
      cases hWaiters : ntfn.waitHead with
      | none =>
        -- No waiters: just storeObject on notification
        simp [hWaiters] at hStep
        exact storeObject_preserves_projection ctx observer st st' notificationId _ hNtfnHigh hObjInv hStep
      | some waiter =>
        simp [hWaiters] at hStep
        -- Waiter path: storeObject + storeTcbIpcStateAndMessage + ensureRunnable (R3-A/M-16)
        have hWaiterHigh := hWaiterDomain ntfn waiter hObj hWaiters
        have hWaiterObjHigh := hCoherent waiter hWaiterHigh
        revert hStep
        cases hStore : storeObject notificationId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter .ready
              (some { IpcMessage.empty with badge := some badge }) with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            have hObjInvMid := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
            rw [ensureRunnable_preserves_projection ctx observer _ waiter hWaiterHigh,
                detachNtfnHead_preserves_projection ctx observer st2 waiter _ hWaiterObjHigh
                  (fun n hn => hSuccHigh n
                    ((notificationSignalSuccessor?_eq_wake st notificationId ntfn waiter hObj
                      hWaiters).trans hn))
                  (storeTcbIpcStateAndMessage_preserves_objects_invExt _ _ _ _ _ hObjInvMid hTcb),
                storeTcbIpcStateAndMessage_preserves_projection ctx observer pair.2 st2 waiter _ _ hWaiterObjHigh hObjInvMid hTcb,
                storeObject_preserves_projection ctx observer st pair.2 notificationId _ hNtfnHigh hObjInv hStore]

/-- WS-F3/F-21: notificationSignal preserves low-equivalence. -/
theorem notificationSignal_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId,
        threadObservable ctx observer tid = false →
        objectObservable ctx observer tid.toObjId = false)
    (hWaiterDomain₁ : ∀ ntfn tid, s₁.objects[notificationId]? = some (.notification ntfn) →
        ntfn.waitHead = some tid → threadObservable ctx observer tid = false)
    (hSuccHigh₁ : ∀ t, notificationSignalSuccessor? s₁ notificationId = some t →
        objectObservable ctx observer t.toObjId = false)
    (hWaiterDomain₂ : ∀ ntfn tid, s₂.objects[notificationId]? = some (.notification ntfn) →
        ntfn.waitHead = some tid → threadObservable ctx observer tid = false)
    (hSuccHigh₂ : ∀ t, notificationSignalSuccessor? s₂ notificationId = some t →
        objectObservable ctx observer t.toObjId = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : notificationSignal notificationId badge s₁ = .ok ((), s₁'))
    (hStep₂ : notificationSignal notificationId badge s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact notificationSignal_projection_preserved ctx observer notificationId badge s₂ s₂'
      hNtfnHigh hCoherent hWaiterDomain₂ hSuccHigh₂ hObjInv₂ hStep₂
  exact notificationSignal_projection_preserved ctx observer notificationId badge s₁ s₁'
    hNtfnHigh hCoherent hWaiterDomain₁ hSuccHigh₁ hObjInv₁ hStep₁

-- ============================================================================
-- WS-F3/F-21: notificationWait non-interference
-- ============================================================================

/-- WS-F3/F-21: the wait's park at non-observable entities preserves projection. -/
theorem notificationWaitPark_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (st st' : SystemState)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hWaiterHigh : threadObservable ctx observer waiter = false)
    (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWaitPark notificationId waiter st = .ok (result, st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold notificationWaitPark SystemState.getObject? at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp [hObj] at hStep
    | notification ntfn =>
      simp [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        -- Consume pending badge: storeObject + storeTcbIpcState
        simp [hBadge] at hStep; revert hStep
        cases hStore : storeObject notificationId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 waiter _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            have hObjInvMid := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
            rw [storeTcbIpcState_preserves_projection ctx observer pair.2 st2 waiter _ hWaiterObjHigh hObjInvMid hTcb,
                storeObject_preserves_projection ctx observer st pair.2 notificationId _ hNtfnHigh hObjInv hStore]
      | none =>
        -- WS-G7: Block path: lookupTcb → ipcState check → storeObject + storeTcbIpcState + removeRunnable
        simp [hBadge] at hStep
        -- WS-G7: match on lookupTcb
        cases hLk : lookupTcb st waiter with
        | none => simp [hLk] at hStep
        | some tcb =>
          simp only [hLk] at hStep
          by_cases hBlocked : tcb.ipcState = .blockedOnNotification notificationId
          · simp [hBlocked] at hStep
          · simp [hBlocked] at hStep; revert hStep
            cases hStore : storeObject notificationId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObj hObjInv hStore
              simp only [storeTcbIpcStateAndMessage_fromTcb_eq hLk']
              cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter _ none with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
                have hObjInvMid := storeObject_preserves_objects_invExt' st notificationId _ pair hObjInv hStore
                rw [removeRunnable_preserves_projection ctx observer st2 waiter hWaiterHigh,
                    storeTcbIpcStateAndMessage_preserves_projection ctx observer pair.2 st2 waiter _ _ hWaiterObjHigh hObjInvMid hTcb,
                    storeObject_preserves_projection ctx observer st pair.2 notificationId _ hNtfnHigh hObjInv hStore]

/-- WS-ZA ZA4.4: a TCB field write at a **high** thread preserves the observer
projection — the write is one `storeObject` at the thread's key. -/
theorem modifyTcb_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hHigh : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) (h : modifyTcb st tid f = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  obtain ⟨_, _, hS⟩ := modifyTcb_ok_decompose h
  exact storeObject_preserves_projection ctx observer st st' tid.toObjId _ hHigh hObjInv hS

/-- WS-ZA ZA4.4: the optional form, high whenever a thread is named. -/
theorem modifyTcbOpt_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {t? : Option SeLe4n.ThreadId} {f : TCB → TCB}
    (hHigh : ∀ t, t? = some t → objectObservable ctx observer t.toObjId = false)
    (hObjInv : st.objects.invExt) (h : modifyTcbOpt st t? f = .ok st') :
    projectState ctx observer st' = projectState ctx observer st := by
  cases t? with
  | none => unfold modifyTcbOpt at h; cases h; rfl
  | some t => exact modifyTcb_preserves_projection ctx observer (hHigh t rfl) hObjInv h

/-- WS-F3/F-21: notificationWait at non-observable entities preserves projection.
WS-ZA ZA4.4: a wait that blocks also writes the queue's old tail (its successor
link), so the tail it relinks must be non-observable too. -/
theorem notificationWait_projection_preserved
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (st st' : SystemState)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hWaiterHigh : threadObservable ctx observer waiter = false)
    (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false)
    (hTailHigh : ∀ t, notificationWaitTail? st notificationId = some t →
      objectObservable ctx observer t.toObjId = false)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  rcases notificationWait_ok_cases hStep with ⟨b, _, hP⟩ | ⟨_, stP, hP, hL⟩
  · exact notificationWaitPark_projection_preserved ctx observer notificationId waiter _ st st'
      hNtfnHigh hWaiterHigh hWaiterObjHigh hObjInv hP
  · obtain ⟨st3, h3, h4⟩ := linkNtfnWaiter_ok_cases hL
    have hInvP := notificationWaitPark_preserves_objects_invExt hObjInv hP
    rw [modifyTcbOpt_preserves_projection ctx observer hTailHigh
          (modifyTcb_preserves_objects_invExt hInvP h3) h4,
        modifyTcb_preserves_projection ctx observer hWaiterObjHigh hInvP h3,
        notificationWaitPark_projection_preserved ctx observer notificationId waiter _ st stP
          hNtfnHigh hWaiterHigh hWaiterObjHigh hObjInv hP]

/-- WS-F3/F-21: notificationWait preserves low-equivalence. -/
theorem notificationWait_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result₁ result₂ : Option SeLe4n.Badge)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hWaiterHigh : threadObservable ctx observer waiter = false)
    (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false)
    (hTailHigh₁ : ∀ t, notificationWaitTail? s₁ notificationId = some t →
      objectObservable ctx observer t.toObjId = false)
    (hTailHigh₂ : ∀ t, notificationWaitTail? s₂ notificationId = some t →
      objectObservable ctx observer t.toObjId = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : notificationWait notificationId waiter s₁ = .ok (result₁, s₁'))
    (hStep₂ : notificationWait notificationId waiter s₂ = .ok (result₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  suffices h₁ : projectState ctx observer s₁' = projectState ctx observer s₁ by
    suffices h₂ : projectState ctx observer s₂' = projectState ctx observer s₂ by
      unfold lowEquivalent; rw [h₁, h₂]; exact hLow
    exact notificationWait_projection_preserved ctx observer notificationId waiter result₂ s₂ s₂'
      hNtfnHigh hWaiterHigh hWaiterObjHigh hTailHigh₂ hObjInv₂ hStep₂
  exact notificationWait_projection_preserved ctx observer notificationId waiter result₁ s₁ s₁'
    hNtfnHigh hWaiterHigh hWaiterObjHigh hTailHigh₁ hObjInv₁ hStep₁

-- ============================================================================
-- WS-F3/CRIT-03: Additional NI theorems for API coverage
-- ============================================================================

/-- WS-F3: cspaceInsertSlot at a non-observable CNode preserves low-equivalence. -/
theorem cspaceInsertSlot_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (dst : CSpaceAddr) (cap : Capability)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : cspaceInsertSlot dst cap s₁ = .ok ((), s₁'))
    (hStep₂ : cspaceInsertSlot dst cap s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have hSched₁ := cspaceInsertSlot_preserves_scheduler s₁ s₁' dst cap hStep₁
  have hSched₂ := cspaceInsertSlot_preserves_scheduler s₂ s₂' dst cap hStep₂
  unfold lowEquivalent projectState; congr 1
  · funext oid
    by_cases hObs : objectObservable ctx observer oid
    · have hNe : oid ≠ dst.cnode := by intro hEq; subst hEq; simp [hDstHigh] at hObs
      simp only [projectObjects, hObs, ite_true, SystemState.getObject?]
      rw [cspaceInsertSlot_preserves_objects_ne s₁ s₁' dst cap oid hNe hObjInv₁ hStep₁,
          cspaceInsertSlot_preserves_objects_ne s₂ s₂' dst cap oid hNe hObjInv₂ hStep₂]
      have h := congrFun (congrArg ObservableState.objects hLow) oid
      simp only [projectState, projectObjects, hObs, ite_true, SystemState.getObject?] at h
      exact h
    · simp [projectObjects, hObs]
  · simpa [projectRunnable, hSched₁, hSched₂] using congrArg ObservableState.runnable hLow
  · simpa [projectCurrent, hSched₁, hSched₂] using congrArg ObservableState.current hLow
  · simpa [projectActiveDomain, hSched₁, hSched₂] using congrArg ObservableState.activeDomain hLow
  · funext irq; simp only [projectIrqHandlers]
    rw [cspaceInsertSlot_preserves_irqHandlers s₁ s₁' dst cap hStep₁,
        cspaceInsertSlot_preserves_irqHandlers s₂ s₂' dst cap hStep₂]
    exact congrFun (congrArg ObservableState.irqHandlers hLow) irq
  · rw [cspaceInsertSlot_preserves_projectObjectIndex s₁ s₁' dst cap hDstHigh hStep₁,
        cspaceInsertSlot_preserves_projectObjectIndex s₂ s₂' dst cap hDstHigh hStep₂]
    exact congrArg ObservableState.objectIndex hLow
  · -- domainTimeRemaining
    simpa [projectDomainTimeRemaining, hSched₁, hSched₂] using congrArg ObservableState.domainTimeRemaining hLow
  · -- domainSchedule
    simpa [projectDomainSchedule, hSched₁, hSched₂] using congrArg ObservableState.domainSchedule hLow
  · -- domainScheduleIndex
    simpa [projectDomainScheduleIndex, hSched₁, hSched₂] using congrArg ObservableState.domainScheduleIndex hLow
  · -- machineRegs
    have hM₁ := cspaceInsertSlot_preserves_machine s₁ s₁' dst cap hStep₁
    have hM₂ := cspaceInsertSlot_preserves_machine s₂ s₂' dst cap hStep₂
    simp [projectMachineRegs, hSched₁, hSched₂, hM₁, hM₂]
    exact congrArg ObservableState.machineRegs hLow
  · -- R5-C.1: memory
    rw [projectMemory_eq_of_memory_eq ctx observer s₁' s₁
          (by rw [cspaceInsertSlot_preserves_machine s₁ s₁' dst cap hStep₁]),
        projectMemory_eq_of_memory_eq ctx observer s₂' s₂
          (by rw [cspaceInsertSlot_preserves_machine s₂ s₂' dst cap hStep₂])]
    exact congrArg ObservableState.memory hLow


