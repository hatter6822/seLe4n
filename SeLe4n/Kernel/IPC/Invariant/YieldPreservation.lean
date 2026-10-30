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
thread's registers and moves one thread from the queue to `current`.  No
conjunct reads the scheduler, and a yield times out no IPC, so no premise
beyond the pre-state bundle is needed.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

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
  unfold sliceExpireOnCore; dsimp only
  exact ipcInvariantFull_runEnqueueOnCore _ c tid _ h1

/-- The budget spend (shared by the tick's bound arm and yield's) preserves the
bundle: the SchedContext write keeps its `boundThread`, and the refill and the
re-enqueue write no object a conjunct reads. -/
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
        all_goals simp [SchedContext.boundThread])
  unfold spendBudgetOnCore
  dsimp only
  have h2 : ipcInvariantFull (replenishOnCore (st.rewriteObject scId.toObjId _ hAdm) c scId) :=
    ipcInvariantFull_of_objectsAgreeOffSchedulerLinks
      (.of_releaseLinks (SystemState.releasePlace_agree _ c scId)) h1
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

/-- The scheduling point preserves the bundle: the save rewrites
`registerContext` only, and the dispatch moves one queued thread into `current`
through the run-queue links and scheduler state, which no conjunct reads. -/
theorem scheduleEffectiveOnCore_preserves_ipcInvariantFull (st : SystemState) (c : CoreId)
    (st' : SystemState) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : scheduleEffectiveOnCore st c = .ok st') : ipcInvariantFull st' := by
  have hS := saveOutgoingContextOnCore_preserves_ipcInvariantFull st c hObjInv hInv
  unfold scheduleEffectiveOnCore at hStep
  split at hStep
  · cases hStep
  · cases hStep
    exact ipcInvariantFull_of_objectsAgreeOffRunLinks
      ((SystemState.objectsAgreeOffRunLinks.of_objects_eq
        (SystemState.clearReschedulePendingOnCore_objects _ c)).trans
        (idleFallbackOnCore_objectsAgreeOffRunLinks (saveOutgoingContextOnCore st c) c)) hS
  · split at hStep
    · split at hStep
      · cases hStep
        rename_i tid _ _ _ _ _
        exact ipcInvariantFull_of_objectsAgreeOffRunLinks
          ((SystemState.objectsAgreeOffRunLinks.of_objects_eq
            (restoreIncomingContextOnCore_objects
              ((saveOutgoingContextOnCore st c).runRemoveOnCore c tid) c tid)).trans
            (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks
              (saveOutgoingContextOnCore st c) c tid)) hS
      · cases hStep
    · cases hStep

/-- The yield's charge preserves the bundle and keeps the object table's
invariant. -/
theorem yieldChargeOnCore_preserves_ipcInvariantFull (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : yieldChargeOnCore st c tid = .ok st') :
    ipcInvariantFull st' ∧ st'.objects.invExt := by
  unfold yieldChargeOnCore at hStep
  split at hStep
  · cases hStep
  · rename_i tcb hTcb _
    split at hStep
    · cases hStep
      exact ⟨sliceExpireOnCore_preserves_ipcInvariantFull st c tid tcb hTcb hObjInv hInv,
        sliceExpireOnCore_objects_invExt st c tid tcb hTcb hObjInv⟩
    all_goals
      split at hStep
      · rename_i sc hSc _
        cases hStep
        refine ⟨markKeyChangeFor_preserves_ipcInvariantFull _ _ _
            (spendBudgetOnCore_preserves_ipcInvariantFull st c tid _ sc hSc _ hObjInv hInv), ?_⟩
        rw [markKeyChangeFor_objects]
        exact spendBudgetOnCore_objects_invExt st c tid _ sc hSc _ hObjInv
      · cases hStep

/-- **The yield syscall preserves `ipcInvariantFull`.** -/
theorem yieldOnCore_preserves_ipcInvariantFull (st : SystemState) (c : CoreId)
    (st' : SystemState) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : yieldOnCore st c = .ok st') : ipcInvariantFull st' := by
  unfold yieldOnCore at hStep
  split at hStep
  · cases hStep
  · rename_i tid _
    split at hStep
    · cases hStep
    · rename_i st1 hCharge
      obtain ⟨hI1, hObj1⟩ := yieldChargeOnCore_preserves_ipcInvariantFull
        st c tid st1 hObjInv hInv hCharge
      exact scheduleEffectiveOnCore_preserves_ipcInvariantFull st1 c _ hObj1 hI1 hStep

end SeLe4n.Kernel
