-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation

/-!
# WS-ZA ZA4.3 — the yield syscall preserves `ipcInvariantFull`

`yieldOnCore` charges the caller (`yieldChargeOnCore`: the timer tick's
slice expiry, or the budget spend the tick's exhausted arm shares) and then
runs core `c`'s scheduling point (`scheduleEffectiveOnCore`).  Neither writes a
field a conjunct of the IPC bundle reads: the charge rewrites a TCB's
`timeSlice` or a SchedContext's budget accounting (its `boundThread`
untouched), queues the caller on core `c`, schedules a refill and flags the
cores the caller's moved key stales; the scheduling point saves the outgoing
thread's registers and moves one thread from the queue to `current`.
`passiveServerIdle` — the one conjunct that reads the scheduler — holds because
the yielding thread is queued before the scheduling point runs, so no thread
leaves both the boot queue and the boot `current` slot.  A yield times out no
IPC, so no premise beyond the pre-state bundle is needed.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

/-- A scheduler-only write that keeps every boot-queue member queued and the
boot `current` slot fixed preserves the bundle. -/
theorem ipcInvariantFull_of_schedulerGrow {st st' : SystemState}
    (hObj : st'.objects = st.objects)
    (hQ : ∀ y : SeLe4n.ThreadId, y ∈ st.scheduler.runQueueOnCore bootCoreId →
      y ∈ st'.scheduler.runQueueOnCore bootCoreId)
    (hC : st'.scheduler.currentOnCore bootCoreId = st.scheduler.currentOnCore bootCoreId)
    (hInv : ipcInvariantFull st) : ipcInvariantFull st' :=
  ipcInvariantFull_of_getElem_eq (s1 := st) (fun _ => by rw [hObj])
    (passiveServerIdle_of_frame
      (passiveServerIdleFrame_of_backward_monotone
        (fun _ tcb h => ⟨tcb, by rw [hObj] at h; exact h, rfl, rfl⟩) hQ hC)
      hInv.passiveServerIdle) hInv

/-- Inserting into core `c`'s run queue keeps every boot-queue member queued. -/
theorem runQueueOnCore_boot_mem_of_insert (s : SchedulerState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (p : SeLe4n.Priority) (y : SeLe4n.ThreadId)
    (hy : y ∈ s.runQueueOnCore bootCoreId) :
    y ∈ (s.setRunQueueOnCore c ((s.runQueueOnCore c).insert tid p)).runQueueOnCore
      bootCoreId := by
  by_cases hcc : c = bootCoreId
  · subst hcc
    rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self, RunQueue.mem_insert]
    exact Or.inl hy
  · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hcc]
    exact hy

/-- The slice expiry (the tick's unbound arm, and yield's) preserves the
bundle: it rewrites the thread's `timeSlice` — a field no conjunct reads — and
queues the thread on core `c`. -/
theorem sliceExpireOnCore_preserves_ipcInvariantFull (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (sliceExpireOnCore st c tid tcb hTcb) := by
  have hPre := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  have hAdm := SystemState.rewriteAdmissible_tcb hTcb
    { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }
  have hAt := rewriteObject_objects_self st tid.toObjId _ hAdm hObjInv
  have hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ tid.toObjId →
      (st.rewriteObject tid.toObjId _ hAdm).objects[oid]? = st.objects[oid]? :=
    fun oid hNe => rewriteObject_objects_ne st tid.toObjId oid _ hAdm (Ne.symm hNe) hObjInv
  have h1 := ipcInvariantFull_of_tcbFieldUpdate st _ tid.toObjId tcb _ hInv hPre hAt hFrame
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (passiveServerIdleFrame_of_tcbFieldUpdate tid.toObjId tcb _ hPre hAt hFrame rfl rfl
      (rewriteObject_scheduler st tid.toObjId _ hAdm))
  unfold sliceExpireOnCore; dsimp only
  exact ipcInvariantFull_runEnqueueOnCore _ c tid _ h1

/-- The slice expiry queues the thread on core `c`. -/
theorem sliceExpireOnCore_mem_runQueue (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hObjInv : st.objects.invExt) (hAdm : st.runEnqueueAdmits c tid = true) :
    tid ∈ (sliceExpireOnCore st c tid tcb hTcb).scheduler.runQueueOnCore c := by
  unfold sliceExpireOnCore; dsimp only
  rw [SystemState.runEnqueueOnCore_runQueueOnCore_self _ (by
    rw [SystemState.runEnqueueAdmits_rewriteObject_tcb
      (t' := { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }) _ hObjInv hTcb rfl]
    exact hAdm)]
  exact (RunQueue.mem_insert _ _ _ _).mpr (Or.inr rfl)

/-- The budget spend (shared by the tick's bound arm and yield's) preserves the
bundle: the SchedContext write keeps its `boundThread`, and the refill and the
re-enqueue are scheduler writes that only grow the queues. -/
theorem spendBudgetOnCore_preserves_ipcInvariantFull (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (scId : SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (ticks : Nat)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (spendBudgetOnCore st c tid scId sc hSc ticks) := by
  have hPre := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hSc
  have hAdm := SystemState.rewriteAdmissible_schedContext hSc
    (cbsUpdateDeadline (scheduleReplenishment (consumeBudget sc ticks) st.machine.timer
      ⟨sc.budgetRemaining.val⟩) st.machine.timer true)
  have h1 : ipcInvariantFull (st.rewriteObject scId.toObjId _ hAdm) :=
    insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull st scId sc _
      hObjInv hInv hPre (by
        unfold cbsUpdateDeadline scheduleReplenishment consumeBudget
        repeat' split
        all_goals rfl)
  unfold spendBudgetOnCore
  dsimp only
  have h2 : ipcInvariantFull (replenishOnCore (st.rewriteObject scId.toObjId _ hAdm) c scId
      (st.machine.timer + sc.period.val)) :=
    ipcInvariantFull_of_schedulerGrow (st := st.rewriteObject scId.toObjId _ hAdm) rfl
      (by intro y hy; simpa [replenishOnCore] using hy) (by simp [replenishOnCore]) h1
  exact ipcInvariantFull_runEnqueueOnCore _ c tid _ h2

/-- Saving the outgoing thread's registers preserves the bundle: it rewrites
`registerContext`, a field no conjunct reads, and leaves the scheduler alone. -/
theorem saveOutgoingContextOnCore_preserves_ipcInvariantFull (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (saveOutgoingContextOnCore st c) := by
  unfold saveOutgoingContextOnCore
  split
  · exact hInv
  · rename_i outTid _
    cases hT : st.getTcb? outTid with
    | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact hInv
    | some tcb =>
      have hPre := (SystemState.getTcb?_eq_some_iff st outTid tcb).mp hT
      have hAt : (st.updateTcb outTid fun t =>
          { t with registerContext := st.machine.regsOnCore c }).objects[outTid.toObjId]? =
          some (.tcb { tcb with registerContext := st.machine.regsOnCore c }) := by
        rw [SystemState.updateTcb_eq_of_some hT]
        exact RobinHood.RHTable.getElem?_insert_self st.objects outTid.toObjId _ hObjInv
      have hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ outTid.toObjId →
          (st.updateTcb outTid fun t =>
            { t with registerContext := st.machine.regsOnCore c }).objects[oid]? =
            st.objects[oid]? :=
        fun oid hNe => SystemState.updateTcb_objects_ne st outTid _ oid (Ne.symm hNe) hObjInv
      exact ipcInvariantFull_of_tcbFieldUpdate st _ outTid.toObjId tcb _ hInv hPre hAt hFrame
        rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (passiveServerIdleFrame_of_tcbFieldUpdate outTid.toObjId tcb _ hPre hAt hFrame rfl rfl
          (SystemState.updateTcb_scheduler _ _ _))

/-- `passiveServerIdle` across a dispatch: the object table is unchanged past
run-queue links, and every thread queued or current on the boot core before is
queued or current on it after. -/
theorem passiveServerIdle_of_dispatch {s1 s2 : SystemState}
    (hA : s2.objectsAgreeOffRunLinks s1)
    (hMove : ∀ y : SeLe4n.ThreadId, y ∈ s1.scheduler.runQueueOnCore bootCoreId →
      y ∈ s2.scheduler.runQueueOnCore bootCoreId ∨
        s2.scheduler.currentOnCore bootCoreId = some y)
    (hCurMove : ∀ y : SeLe4n.ThreadId, s1.scheduler.currentOnCore bootCoreId = some y →
      y ∈ s2.scheduler.runQueueOnCore bootCoreId ∨
        s2.scheduler.currentOnCore bootCoreId = some y)
    (hInv : passiveServerIdle s1) : passiveServerIdle s2 := by
  intro x tcb hT hU hQ hC
  obtain ⟨t0, h0, hE⟩ := hA.get_tcb' hT
  rw [TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hE]
  refine hInv x t0 h0
    (by rw [← TCB.proj_eq_of_withoutRunLinks_eq TCB.schedContextBinding hE]; exact hU)
    (fun hx => ?_) (fun hx => ?_)
  · rcases hMove x hx with h | h
    · exact hQ h
    · exact hC h
  · rcases hCurMove x hx with h | h
    · exact hQ h
    · exact hC h

/-- `passiveServerIdle` across a dispatch on core `c`: on another core the boot
slots are untouched; on the boot core every queued thread stays queued or
becomes current, and the outgoing current thread was queued before. -/
theorem passiveServerIdle_of_dispatchOnCore {s1 s2 : SystemState} (c : CoreId)
    (hA : s2.objectsAgreeOffRunLinks s1)
    (hOther : c ≠ bootCoreId →
      s2.scheduler.runQueueOnCore bootCoreId = s1.scheduler.runQueueOnCore bootCoreId ∧
      s2.scheduler.currentOnCore bootCoreId = s1.scheduler.currentOnCore bootCoreId)
    (hSelf : ∀ y : SeLe4n.ThreadId, y ∈ s1.scheduler.runQueueOnCore c →
      y ∈ s2.scheduler.runQueueOnCore c ∨ s2.scheduler.currentOnCore c = some y)
    (hCurQ : ∀ t : SeLe4n.ThreadId, s1.scheduler.currentOnCore c = some t →
      t ∈ s1.scheduler.runQueueOnCore c)
    (hInv : passiveServerIdle s1) : passiveServerIdle s2 := by
  by_cases hcc : c = bootCoreId
  · subst hcc
    exact passiveServerIdle_of_dispatch hA hSelf (fun y hy => hSelf y (hCurQ y hy)) hInv
  · obtain ⟨hQ, hC⟩ := hOther hcc
    exact passiveServerIdle_of_dispatch hA (fun y hy => Or.inl (hQ ▸ hy))
      (fun y hy => Or.inr (hC ▸ hy)) hInv

/-- The scheduling point preserves the bundle when the outgoing current thread
is queued on its core (as a yield and an expired budget or slice leave it):
the save rewrites `registerContext` only, and the dispatch moves one queued
thread into `current`. -/
theorem scheduleEffectiveOnCore_preserves_ipcInvariantFull (st : SystemState) (c : CoreId)
    (st' : SystemState) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hCurQ : ∀ t : SeLe4n.ThreadId, st.scheduler.currentOnCore c = some t →
      t ∈ st.scheduler.runQueueOnCore c)
    (hStep : scheduleEffectiveOnCore st c = .ok st') : ipcInvariantFull st' := by
  have hS := saveOutgoingContextOnCore_preserves_ipcInvariantFull st c hObjInv hInv
  have hSched := saveOutgoingContextOnCore_scheduler st c
  have hCurQ' : ∀ t : SeLe4n.ThreadId,
      (saveOutgoingContextOnCore st c).scheduler.currentOnCore c = some t →
      t ∈ (saveOutgoingContextOnCore st c).scheduler.runQueueOnCore c := by
    rw [hSched]; exact hCurQ
  unfold scheduleEffectiveOnCore at hStep
  split at hStep
  · cases hStep
  · cases hStep
    have hA := (SystemState.objectsAgreeOffRunLinks.of_objects_eq
      (SystemState.clearReschedulePendingOnCore_objects _ c)).trans
      (idleFallbackOnCore_objectsAgreeOffRunLinks (saveOutgoingContextOnCore st c) c)
    refine ipcInvariantFull_of_objectsAgreeOffRunLinks hA ?_ hS
    refine passiveServerIdle_of_dispatchOnCore c hA ?_ ?_ hCurQ' hS.passiveServerIdle
    · intro hcc
      simp only [SystemState.clearReschedulePendingOnCore,
        SchedulerState.clearReschedulePendingOnCore_runQueueOnCore,
        SchedulerState.clearReschedulePendingOnCore_currentOnCore]
      unfold idleFallbackOnCore
      split
      · simp [dispatchIdleOnCore, restoreIncomingContextOnCore_scheduler,
          SystemState.runRemoveOnCore_scheduler,
          SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hcc,
          SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hcc]
      · simp [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hcc]
    · intro y hy
      simp only [SystemState.clearReschedulePendingOnCore,
        SchedulerState.clearReschedulePendingOnCore_runQueueOnCore,
        SchedulerState.clearReschedulePendingOnCore_currentOnCore]
      unfold idleFallbackOnCore
      split
      · rw [dispatchIdleOnCore_runQueueOnCore, dispatchIdleOnCore_currentOnCore,
          RunQueue.mem_remove]
        by_cases hY : y = idleThreadId c
        · exact Or.inr (by rw [hY])
        · exact Or.inl ⟨hy, hY⟩
      · simp only [SchedulerState.setCurrentOnCore_runQueueOnCore]
        exact Or.inl hy
  · split at hStep
    · split at hStep
      · cases hStep
        rename_i tid _ _ _ _ _
        have hA := (SystemState.objectsAgreeOffRunLinks.of_objects_eq
          (restoreIncomingContextOnCore_objects
            ((saveOutgoingContextOnCore st c).runRemoveOnCore c tid) c tid)).trans
          (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks (saveOutgoingContextOnCore st c) c tid)
        refine ipcInvariantFull_of_objectsAgreeOffRunLinks hA ?_ hS
        refine passiveServerIdle_of_dispatchOnCore c hA ?_ ?_ hCurQ' hS.passiveServerIdle
        · intro hcc
          simp [restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
            SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hcc,
            SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hcc]
        · intro y hy
          simp only [SchedulerState.clearReschedulePendingOnCore_runQueueOnCore,
            SchedulerState.clearReschedulePendingOnCore_currentOnCore,
            SchedulerState.setCurrentOnCore_runQueueOnCore,
            SchedulerState.setCurrentOnCore_currentOnCore_self,
            restoreIncomingContextOnCore_scheduler, SystemState.runRemoveOnCore_scheduler,
            SchedulerState.setRunQueueOnCore_runQueueOnCore_self, RunQueue.mem_remove]
          exact (Classical.em _).elim Or.inr
            (fun h => Or.inl ⟨hy, fun hE => h (by rw [hE])⟩)
      · cases hStep
    · cases hStep

/-- The budget spend keeps the object table's invariant and every core's
`current` slot, and queues the thread on core `c`. -/
theorem spendBudgetOnCore_frame (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (scId : SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (ticks : Nat)
    (hObjInv : st.objects.invExt) (hAdm : st.runEnqueueAdmits c tid = true) :
    (spendBudgetOnCore st c tid scId sc hSc ticks).objects.invExt ∧
    (∀ c' : CoreId, (spendBudgetOnCore st c tid scId sc hSc ticks).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c') ∧
    tid ∈ (spendBudgetOnCore st c tid scId sc hSc ticks).scheduler.runQueueOnCore c := by
  refine ⟨spendBudgetOnCore_objects_invExt st c tid scId sc hSc ticks hObjInv, fun c' => ?_, ?_⟩
  · unfold spendBudgetOnCore
    simp [replenishOnCore, rewriteObject_scheduler]
  · unfold spendBudgetOnCore; dsimp only
    rw [SystemState.runEnqueueOnCore_runQueueOnCore_self _ (by
      refine (SystemState.runEnqueueAdmits_congr ?_ c).trans hAdm
      exact congrArg (Option.map TCB.runCoreCode)
        (rewriteObject_schedContext_getTcb? _ _ _ (SystemState.rewriteAdmissible_schedContext hSc _)
          hObjInv tid))]
    exact (RunQueue.mem_insert _ _ _ _).mpr (Or.inr rfl)

/-- The yield's charge preserves the bundle, keeps the object table's invariant
and every core's `current` slot, and leaves the caller queued on core `c`. -/
theorem yieldChargeOnCore_preserves_ipcInvariantFull (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hAdm : st.runEnqueueAdmits c tid = true)
    (hStep : yieldChargeOnCore st c tid = .ok st') :
    ipcInvariantFull st' ∧ st'.objects.invExt ∧
    (∀ c' : CoreId, st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c') ∧
    tid ∈ st'.scheduler.runQueueOnCore c := by
  unfold yieldChargeOnCore at hStep
  split at hStep
  · cases hStep
  · rename_i tcb hTcb _
    split at hStep
    · cases hStep
      exact ⟨sliceExpireOnCore_preserves_ipcInvariantFull st c tid tcb hTcb hObjInv hInv,
        sliceExpireOnCore_objects_invExt st c tid tcb hTcb hObjInv,
        fun c' => by simp [sliceExpireOnCore, rewriteObject_scheduler],
        sliceExpireOnCore_mem_runQueue st c tid tcb hTcb hObjInv hAdm⟩
    all_goals
      split at hStep
      · rename_i sc hSc _
        cases hStep
        obtain ⟨hI, hC, hM⟩ := spendBudgetOnCore_frame st c tid _ sc hSc _ hObjInv hAdm
        refine ⟨markKeyChangeFor_preserves_ipcInvariantFull _ _ _
            (spendBudgetOnCore_preserves_ipcInvariantFull st c tid _ sc hSc _ hObjInv hInv),
          by rw [markKeyChangeFor_objects]; exact hI,
          fun c' => by rw [markKeyChangeFor_currentOnCore]; exact hC c',
          by rw [markKeyChangeFor_runQueueOnCore]; exact hM⟩
      · cases hStep

/-- **The yield syscall preserves `ipcInvariantFull`.** -/
theorem yieldOnCore_preserves_ipcInvariantFull (st : SystemState) (c : CoreId)
    (st' : SystemState) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hAdm : ∀ t, st.scheduler.currentOnCore c = some t → st.runEnqueueAdmits c t = true)
    (hStep : yieldOnCore st c = .ok st') : ipcInvariantFull st' := by
  unfold yieldOnCore at hStep
  split at hStep
  · cases hStep
  · rename_i tid hCur
    split at hStep
    · cases hStep
    · rename_i st1 hCharge
      obtain ⟨hI1, hObj1, hCur1, hMem1⟩ := yieldChargeOnCore_preserves_ipcInvariantFull
        st c tid st1 hObjInv hInv (hAdm tid hCur) hCharge
      refine scheduleEffectiveOnCore_preserves_ipcInvariantFull st1 c _ hObj1 hI1
        (fun t ht => ?_) hStep
      rw [hCur1, hCur] at ht
      cases ht
      exact hMem1

end SeLe4n.Kernel
