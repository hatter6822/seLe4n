-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ReschedulePendingArms.Capability
import SeLe4n.Kernel.Scheduler.Invariant.ReschedulePendingSchedulingPoints
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick

/-!
# The priority, affinity and scheduling-context arms cover

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md`, PR B2.  These arms write a
thread's key — its priority, its binding — or move it between cores, and each
ends the write in the key hook (`markKeyChangeFor`) or a flagging slot writer.
The proofs pair each key write with its hook (`stepCovers_markKeyChangeFor`)
and chain the remaining slot steps with `stepCovers_trans`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)
open SeLe4n.Kernel.PriorityInheritance (scheduleLocalSuccessor)

/-- A scheduling-context update that keeps the deadline and the budget's sign
moves no key input. -/
theorem keyInputsEq_updateSchedContext {st : SystemState} {scId : SeLe4n.SchedContextId}
    {f : SchedContext → SchedContext} (hInv : st.objects.invExt)
    (hF : ∀ sc, (f sc).deadline = sc.deadline)
    (hB : ∀ sc, (f sc).budgetRemaining.isPositive = sc.budgetRemaining.isPositive := by
      intro _; rfl) :
    keyInputsEq st (st.updateSchedContext scId f) := by
  cases hS : st.getSchedContext? scId with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hS]; exact keyInputsEq_refl st
  | some sc =>
    unfold SystemState.updateSchedContext
    rw [SystemState.getSchedContextWitnessed?_eq_some hS]
    apply keyInputsEq_rewriteObject _ hInv
    have hO : st.objects[scId.toObjId]? = some (.schedContext sc) :=
      (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hS
    rw [hO]
    simp only [keyInputsOf, hF, hB]

/-- The reschedule seam is the identity or the executing core's own reschedule
handler, so it covers. -/
theorem priorityRescheduleOnCore_stepCovers (e : CoreId) (st st' : SystemState)
    (running? : Option CoreId) (sp : Bool) (sgi? : Option (CoreId × SgiKind))
    (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCore st running? e sp
      = .ok (st', sgi?)) :
    stepCovers e st st' := by
  rcases SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases
      st st' running? e sp sgi? h with hEq | hH
  · rw [hEq]; exact stepCovers_refl e st
  · exact handleRescheduleSgiOnCore_stepCovers e st st' hInv hH

/-- **One boost update covers**: the boost write on the holder ends in the key
hook, and the re-bucket keeps the queue's membership. -/
theorem updatePipBoostOnCore_stepCovers (e c : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    stepCovers e st (PriorityInheritance.updatePipBoostOnCore st c tid) := by
  unfold PriorityInheritance.updatePipBoostOnCore
  split
  · rename_i tcb hT _
    dsimp only []
    split
    · exact stepCovers_refl e st
    have hAdm := SystemState.rewriteAdmissible_tcb hT
      { tcb with pipBoostCode := SeLe4n.Priority.optCode (PriorityInheritance.computeMaxWaiterPriority st tid) }
    have hK : keyInputsEqExcept tid st (st.rewriteObject tid.toObjId _ hAdm) := by
      have := keyInputsEqExcept_updateTcb (f := fun t => { t with
        pipBoostCode := SeLe4n.Priority.optCode (PriorityInheritance.computeMaxWaiterPriority st tid) }) hInv (by rw [hT]; rfl)
      unfold SystemState.updateTcb at this
      rw [SystemState.getTcbWitnessed?_eq_some hT] at this
      exact this
    have hAgree := SystemState.RunCoresAgree.rewriteObject_tcb
      (tcb' := { tcb with pipBoostCode := SeLe4n.Priority.optCode (PriorityInheritance.computeMaxWaiterPriority st tid) })
      hT hAdm hInv rfl
    have hE0 : ∀ t, budgetEligibleView (st.rewriteObject tid.toObjId _ hAdm) t =
        budgetEligibleView st t := budgetEligibleView_rewriteObject_tcb hT hAdm hInv rfl
    split
    · split
      · rename_i hMem _
        -- The re-key relinks queue neighbours' TCB run-queue fields, which no
        -- key input reads (WS-ZA ZA4.5).
        refine stepCovers_markKeyChangeFor hT (hK.trans_offRunLinks
            (SystemState.runRequeueOnCore_objectsAgreeOffRunLinks _ c tid _)
            (fun y hy => SystemState.runRequeueOnCore_runCoreCode_ne _ c tid y _ hy))
          (candidacyNotGained_of_eq ((budgetEligibleView_of_objectsAgreeOffRunLinks
            (SystemState.runRequeueOnCore_objectsAgreeOffRunLinks _ c tid _) tid).trans (hE0 tid)).symm)
          (fun c' _ => Or.inr ⟨fun t ht => ?_, ?_⟩) (fun c' _ hF => ?_)
        · rw [SystemState.runRequeueOnCore_queuedOn] at ht
          split at ht
          · rename_i hy; subst hy
            by_cases hc : c' = c
            · subst hc; exact hMem
            · simp [hc] at ht
          · rwa [hAgree.queuedOn] at ht
        · simp only [SystemState.runRequeueOnCore_scheduler, SystemState.rewriteObject_scheduler,
            SchedulerState.setRunQueueOnCore_currentOnCore,
            SchedulerState.setRunQueueEndsOnCore_currentOnCore]
        · simp only [SystemState.runRequeueOnCore_scheduler, SystemState.rewriteObject_scheduler,
            SchedulerState.setRunQueueOnCore_reschedulePendingOnCore,
            SchedulerState.setRunQueueEndsOnCore_reschedulePendingOnCore]
          exact hF
      · exact stepCovers_markKeyChangeFor hT hK (candidacyNotGained_of_eq (hE0 tid).symm)
          (fun c' _ => Or.inr ⟨fun t ht => by rwa [hAgree.queuedOn] at ht, rfl⟩) (fun c' _ hF => hF)
    · exact stepCovers_markKeyChangeFor hT hK (candidacyNotGained_of_eq (hE0 tid).symm)
        (fun c' _ => Or.inr ⟨fun t ht => by rwa [hAgree.queuedOn] at ht, rfl⟩) (fun c' _ hF => hF)
  · exact stepCovers_refl e st

/-- **The cross-core chain walk covers**: each link is one boost update. -/
theorem propagatePipChainCrossCore_stepCovers (e ec : CoreId) (fuel : Nat) :
    ∀ (st : SystemState) (tid : SeLe4n.ThreadId), st.objects.invExt →
      stepCovers e st (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1 ∧
        (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1.objects.invExt := by
  induction fuel with
  | zero => intro st _ hInv; exact ⟨stepCovers_refl e st, hInv⟩
  | succ n ih =>
    intro st tid hInv
    rw [PriorityInheritance.propagatePipChainCrossCore_step]
    have h1 := updatePipBoostOnCore_stepCovers e (determineTargetCore st tid) st tid hInv
    have h1Inv := PriorityInheritance.updatePipBoostOnCore_preserves_objects_invExt st
      (determineTargetCore st tid) tid hInv
    dsimp only []
    split
    · rename_i next _
      obtain ⟨h2, h2Inv⟩ := ih _ next h1Inv
      exact ⟨stepCovers_trans h1 h2, h2Inv⟩
    · exact ⟨h1, h1Inv⟩

theorem updatePrioritySource_keyInputsEqExcept (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (p : SeLe4n.Priority) (hInv : st.objects.invExt)
    (hT : st.getTcb? tid = some tcb) :
    keyInputsEqExcept tid st (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) := by
  unfold SchedContext.PriorityManagement.updatePrioritySource
  split
  · rename_i _ scId _
    have hK := keyInputsEq_updateSchedContext (scId := scId)
      (f := fun sc => { sc with priority := p }) hInv (fun _ => rfl)
    have hT' : ((st.updateSchedContext scId fun sc => { sc with priority := p }).getTcb? tid).isSome := by
      have := getTcb?_keyFields_of_keyInputsEq hK tid
      rw [hT] at this
      cases h : (st.updateSchedContext scId fun sc => { sc with priority := p }).getTcb? tid with
      | none => rw [h] at this; cases this
      | some _ => rfl
    exact hK.trans_keyInputsEqExcept (keyInputsEqExcept_updateTcb
      (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv) hT')
  · exact keyInputsEqExcept_updateTcb hInv (by rw [hT]; rfl)

/-- The priority write moves no binding. -/
theorem updatePrioritySource_bindingsAgree (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    bindingsAgree (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) st := by
  unfold SchedContext.PriorityManagement.updatePrioritySource
  split
  · exact (bindingsAgree.updateTcb (f := fun t => { t with priority := p })
      (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv) (fun _ => rfl)).trans
      (bindingsAgree.updateSchedContext hInv)
  · exact bindingsAgree.updateTcb (f := fun t => { t with priority := p }) hInv (fun _ => rfl)

/-! ### Affinity -/

/-- A step that moves no key input covers when every remote core is flagged or
kept its slots (a queue may only shrink), and no remote flag dropped. -/
theorem stepCovers_of_keys_slots {e : CoreId} {pre post : SystemState}
    (hKeys : ∀ t, schedKeyView post t = schedKeyView pre t)
    (hElig : ∀ t, budgetEligibleView post t = budgetEligibleView pre t)
    (hSlots : ∀ c, c ≠ e → post.scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, post.queuedOn c t = true → pre.queuedOn c t = true) ∧
        post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c))
    (hMono : reschedulePendingMonotone e pre post) : stepCovers e pre post :=
  ⟨reschedulePendingCovers_of_frame hKeys hElig hSlots, hMono⟩

/-- **A release-queue edit covers**: it writes the contexts' release links and
the release-queue slots alone, which no key input, run queue, current slot or
flag reads. -/
theorem stepCovers_of_releaseOnlyWrite (e : CoreId) {st st' : SystemState}
    (hW : st'.releaseOnlyWrite st) (hA : st'.objectsAgreeOffReleaseLinks st) :
    stepCovers e st st' := by
  apply stepCovers_of_keys_slots
    (schedKeyView_eq_of_keyInputsEq (keyInputsEq_of_objectsAgreeOffReleaseLinks hA))
    (budgetEligibleView_eq_of_keyInputsEq (keyInputsEq_of_objectsAgreeOffReleaseLinks hA))
  · intro c _
    exact Or.inr ⟨fun t ht => by
      rwa [SystemState.queuedOn_of_getTcb? (hA.getTcb? t)] at ht, by rw [hW.2]; rfl⟩
  · intro c _ hp
    rw [hW.2]
    exact hp

theorem migrateSchedContextReplenishment_stepCovers (e : CoreId) (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) :
    stepCovers e st (migrateSchedContextReplenishment st scId fromCore toCore) :=
  stepCovers_of_releaseOnlyWrite e (migrateSchedContextReplenishment_releaseOnlyWrite _ _ _ _)
    (migrateSchedContextReplenishment_agree _ _ _ _)

/-- The re-placement covers. -/
theorem releasePlace_stepCovers (e : CoreId) (st : SystemState) (c : CoreId)
    (scId : SeLe4n.SchedContextId) : stepCovers e st (st.releasePlace c scId) :=
  stepCovers_of_releaseOnlyWrite e (SystemState.releasePlace_releaseOnlyWrite _ _ _)
    (SystemState.releasePlace_agree _ _ _)

theorem migrateRunQueueOnAffinityChange_stepCovers (e : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) :
    stepCovers e st (migrateRunQueueOnAffinityChange st tid fromCore toCore) := by
  apply stepCovers_of_keys_slots
    (schedKeyView_of_objectsAgreeOffRunLinks
      (migrateRunQueueOnAffinityChange_objectsAgreeOffRunLinks _ _ _ _))
    (budgetEligibleView_of_objectsAgreeOffRunLinks
      (migrateRunQueueOnAffinityChange_objectsAgreeOffRunLinks _ _ _ _))
  · intro c _
    rw [migrateRunQueueOnAffinityChange_currentOnCore]
    unfold migrateRunQueueOnAffinityChange
    split
    · exact Or.inr ⟨fun _ h => h, rfl⟩
    · split
      · exact Or.inr ⟨fun _ h => h, rfl⟩
      · split
        · by_cases hTo : c = toCore
          · subst hTo; left; simp
          · right
            rename_i tcb _ _
            refine ⟨fun t ht => ?_, rfl⟩
            have hO := SystemState.RunCoresAgree.of_objects
              (st := (st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid
                tcb.boostedPriority) (st' := { ((st.runRemoveOnCore fromCore tid).runEnqueueAdmitted
                  toCore tid tcb.boostedPriority) with
                    scheduler := ((st.runRemoveOnCore fromCore tid).runEnqueueAdmitted toCore tid
                      tcb.boostedPriority).scheduler.markReschedulePendingOnCore toCore }) rfl
            rw [hO.queuedOn, SystemState.runEnqueueAdmitted_queuedOn] at ht
            split at ht
            · simp [hTo] at ht
            · rw [SystemState.runRemoveOnCore_queuedOn] at ht
              split at ht
              · cases ht
              · exact ht
        · exact Or.inr ⟨fun _ h => h, rfl⟩
  · intro c _ hp
    unfold migrateRunQueueOnAffinityChange
    split
    · exact hp
    · split
      · exact hp
      · split
        · by_cases hTo : toCore = c
          · subst hTo; simp
          · simp [hTo, hp]
        · exact hp

/-- WS-ZA ZA6.3: the vacate covers — the one slot it empties is on a core it
flags. -/
theorem vacateForAffinityChange_stepCovers (e : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (oldCore newCore : CoreId) :
    stepCovers e st (vacateForAffinityChange st tid oldCore newCore) := by
  apply stepCovers_of_keys_slots
    (schedKeyView_of_objectsAgreeOffRunLinks
      (vacateForAffinityChange_objectsAgreeOffRunLinks _ _ _ _))
    (budgetEligibleView_of_objectsAgreeOffRunLinks
      (vacateForAffinityChange_objectsAgreeOffRunLinks _ _ _ _))
  · intro c _
    unfold vacateForAffinityChange
    split
    · by_cases hc : c = oldCore
      · subst hc; left; simp
      · right
        refine ⟨fun t ht => ht, ?_⟩
        simp [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ (Ne.symm hc)]
    · exact Or.inr ⟨fun _ h => h, rfl⟩
  · intro c _ hp
    unfold vacateForAffinityChange
    split
    · by_cases hc : oldCore = c
      · subst hc; simp
      · simp [hc, hp]
    · exact hp

/-- WS-ZA ZA6.3: the requeue covers — the one queue it grows is on a core it
flags. -/
theorem requeueVacatedOnNewHome_stepCovers (e : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (newCore : CoreId) (vacated : Bool) :
    stepCovers e st (requeueVacatedOnNewHome st tid newCore vacated) := by
  apply stepCovers_of_keys_slots
    (schedKeyView_of_objectsAgreeOffRunLinks
      (requeueVacatedOnNewHome_objectsAgreeOffRunLinks _ _ _ _))
    (budgetEligibleView_of_objectsAgreeOffRunLinks
      (requeueVacatedOnNewHome_objectsAgreeOffRunLinks _ _ _ _))
  · intro c _
    unfold requeueVacatedOnNewHome
    split
    · split
      · by_cases hc : c = newCore
        · subst hc; left; simp
        · right
          refine ⟨fun t ht => ?_, by simp⟩
          change (st.runEnqueueOnCore newCore tid _).queuedOn c t = true at ht
          exact SystemState.runEnqueueOnCore_queuedOn_imp_ne hc ht
      · exact Or.inr ⟨fun _ h => h, rfl⟩
    · exact Or.inr ⟨fun _ h => h, rfl⟩
  · intro c _ hp
    unfold requeueVacatedOnNewHome
    split
    · split
      · by_cases hc : newCore = c
        · subst hc; simp
        · simp [hc, hp]
      · exact hp
    · exact hp

theorem setThreadCpuAffinityOnCore_stepCovers (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (affinity : Option CoreId) (e : CoreId)
    (sgi : Option (CoreId × SgiKind)) (hInv : st.objects.invExt)
    (hStep : setThreadCpuAffinityOnCore st vtid affinity e = .ok (st', sgi)) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold setThreadCpuAffinityOnCore at hStep
  obtain ⟨tcb, stSet, hT, -, -, -, hSet, rfl, -⟩ :=
    setThreadCpuAffinityWithMigration_ok_shape hStep
  have hInvV : (vacateForAffinityChange st vtid.val (determineTargetCore st vtid.val)
      (affinity.getD Concurrency.bootCoreId)).objects.invExt := by
    rw [vacateForAffinityChange_objects]; exact hInv
  have hTV : (vacateForAffinityChange st vtid.val (determineTargetCore st vtid.val)
      (affinity.getD Concurrency.bootCoreId)).getTcb? vtid.val = some tcb := by
    rw [vacateForAffinityChange_getTcb?]; exact hT
  have s0 := vacateForAffinityChange_stepCovers e st vtid.val (determineTargetCore st vtid.val)
    (affinity.getD Concurrency.bootCoreId)
  generalize vacateForAffinityChange st vtid.val (determineTargetCore st vtid.val)
    (affinity.getD Concurrency.bootCoreId) = sv at hSet hInvV hTV s0
  have hSetEq : stSet =
      { sv with objects := sv.objects.insert vtid.val.toObjId (.tcb { tcb with cpuAffinity := affinity }) } := by
    unfold setThreadCpuAffinity at hSet
    rw [SystemState.getTcbWitnessed?_eq_some hTV] at hSet
    exact (Except.ok.inj hSet).symm
  subst hSetEq
  have kSet := insertObjects_tcbKeyKeeping_keyFrame (tcb' := { tcb with
    cpuAffinity := affinity }) hInvV ((SystemState.getTcb?_eq_some_iff sv vtid.val tcb).mp hTV) rfl
  have s1 := stepCovers_trans s0 (kSet.stepCovers (e := e))
  cases tcb.schedContextBinding.scId? with
  | some scId =>
    refine ⟨stepCovers_trans s1 (stepCovers_trans
      (migrateSchedContextReplenishment_stepCovers e _ scId _ _)
      (stepCovers_trans (migrateRunQueueOnAffinityChange_stepCovers e _ _ _ _)
        (requeueVacatedOnNewHome_stepCovers e _ _ _ _))), ?_⟩
    exact requeueVacatedOnNewHome_preserves_objects_invExt _ _ _ _
      (migrateRunQueueOnAffinityChange_preserves_objects_invExt _ _ _ _
        (migrateSchedContextReplenishment_preserves_objects_invExt _ _ _ _ kSet.2.2))
  | none =>
    exact ⟨stepCovers_trans s1 (stepCovers_trans
        (migrateRunQueueOnAffinityChange_stepCovers e _ _ _ _)
        (requeueVacatedOnNewHome_stepCovers e _ _ _ _)),
      requeueVacatedOnNewHome_preserves_objects_invExt _ _ _ _
        (migrateRunQueueOnAffinityChange_preserves_objects_invExt _ _ _ _ kSet.2.2)⟩

/-! ### Scheduling-context configure -/

/-- The effective key reads the TCB's key fields and the deadline of the one
context its binding names. -/
theorem resolveEffectivePrioDeadline_congr_binding {st st' : SystemState} {a b : TCB}
    (hK : tcbKeyFields b = tcbKeyFields a)
    (hSc : ∀ sc, a.schedContextBinding.scId? = some sc →
      (st'.getSchedContext? sc).map (·.deadline) = (st.getSchedContext? sc).map (·.deadline)) :
    resolveEffectivePrioDeadline st' b = resolveEffectivePrioDeadline st a := by
  simp only [tcbKeyFields, Prod.mk.injEq] at hK
  obtain ⟨hP, hD, hB, hPip, -⟩ := hK
  unfold resolveEffectivePrioDeadline
  rw [hP, hD, hB, hPip]
  cases hA : a.schedContextBinding with
  | unbound => rfl
  | bound sc =>
    have := hSc sc (by rw [hA]; rfl)
    cases hq : st'.getSchedContext? sc <;> cases hp : st.getSchedContext? sc <;> simp_all
  | donated sc o =>
    have := hSc sc (by rw [hA]; rfl)
    cases hq : st'.getSchedContext? sc <;> cases hp : st.getSchedContext? sc <;> simp_all

/-- The full key, likewise: the domain is a key field. -/
theorem effectiveSchedParams_congr_binding {st st' : SystemState} {a b : TCB}
    (hK : tcbKeyFields b = tcbKeyFields a)
    (hSc : ∀ sc, a.schedContextBinding.scId? = some sc →
      (st'.getSchedContext? sc).map (·.deadline) = (st.getSchedContext? sc).map (·.deadline)) :
    effectiveSchedParams st' b = effectiveSchedParams st a := by
  have hDom : b.domain = a.domain := by
    simp only [tcbKeyFields, Prod.mk.injEq] at hK; exact hK.2.2.2.2
  exact effectiveSchedParams_eq_of (resolveEffectivePrioDeadline_congr_binding hK hSc) hDom

/-- A write that moves only context `S`'s slot, a context on both sides, keeps
the key of every thread whose binding does not name `S`. -/
theorem schedKeyView_eq_of_scSlotWrite {pre post : SystemState} {S : SeLe4n.SchedContextId}
    {sc0 sc1 : SchedContext}
    (hFrame : ∀ oid, oid ≠ S.toObjId → keyInputsOf post.objects[oid]? = keyInputsOf pre.objects[oid]?)
    (hPre : pre.objects[S.toObjId]? = some (.schedContext sc0))
    (hPost : post.objects[S.toObjId]? = some (.schedContext sc1))
    {t : SeLe4n.ThreadId}
    (hNo : ∀ tcb, pre.getTcb? t = some tcb → tcb.schedContextBinding.scId? ≠ some S) :
    schedKeyView post t = schedKeyView pre t := by
  by_cases hEq : t.toObjId = S.toObjId
  · unfold schedKeyView SystemState.getTcb?
    rw [hEq, hPre, hPost]; rfl
  · have hT := getTcb?_keyFields_of_keyInputsOf (hFrame _ hEq)
    unfold schedKeyView
    cases hq : post.getTcb? t <;> cases hp : pre.getTcb? t <;> simp only [hq, hp] at hT ⊢
    · rfl
    · simp at hT
    · simp at hT
    · rename_i b a
      simp only [Option.map_some, Option.some.injEq] at hT ⊢
      rw [effectiveSchedParams_congr_binding hT (fun sc hsc => ?_)]
      have hNe : sc ≠ S := fun h => hNo a hp (h ▸ hsc)
      have hNeO : sc.toObjId ≠ S.toObjId := fun h => hNe (SeLe4n.SchedContextId.toObjId_injective _ _ h)
      exact getSchedContext?_deadline_of_keyInputsOf (hFrame _ hNeO)

/-- Budget eligibility reads the binding and the budget sign of the one context
it names. -/
theorem hasSufficientBudget_congr_binding {st st' : SystemState} {a b : TCB}
    (hB : b.schedContextBinding = a.schedContextBinding)
    (hSc : ∀ sc, a.schedContextBinding.scId? = some sc →
      (st'.getSchedContext? sc).map (·.budgetRemaining.isPositive) =
        (st.getSchedContext? sc).map (·.budgetRemaining.isPositive)) :
    hasSufficientBudget st' b = hasSufficientBudget st a := by
  unfold hasSufficientBudget
  rw [hB]
  cases hA : a.schedContextBinding with
  | unbound => rfl
  | bound sc =>
    have := hSc sc (by rw [hA]; rfl)
    cases hq : st'.getSchedContext? sc <;> cases hp : st.getSchedContext? sc <;> simp_all
  | donated sc o =>
    have := hSc sc (by rw [hA]; rfl)
    cases hq : st'.getSchedContext? sc <;> cases hp : st.getSchedContext? sc <;> simp_all

/-- A write that moves only context `S`'s slot, a context on both sides, keeps
the budget eligibility of every thread whose binding does not name `S`. -/
theorem budgetEligibleView_eq_of_scSlotWrite {pre post : SystemState} {S : SeLe4n.SchedContextId}
    {sc0 sc1 : SchedContext}
    (hFrame : ∀ oid, oid ≠ S.toObjId → keyInputsOf post.objects[oid]? = keyInputsOf pre.objects[oid]?)
    (hPre : pre.objects[S.toObjId]? = some (.schedContext sc0))
    (hPost : post.objects[S.toObjId]? = some (.schedContext sc1))
    {t : SeLe4n.ThreadId}
    (hNo : ∀ tcb, pre.getTcb? t = some tcb → tcb.schedContextBinding.scId? ≠ some S) :
    budgetEligibleView post t = budgetEligibleView pre t := by
  by_cases hEq : t.toObjId = S.toObjId
  · unfold budgetEligibleView SystemState.getTcb?
    rw [hEq, hPre, hPost]; rfl
  · have hT := getTcb?_keyFields_of_keyInputsOf (hFrame _ hEq)
    unfold budgetEligibleView
    cases hq : post.getTcb? t <;> cases hp : pre.getTcb? t <;> simp only [hq, hp] at hT ⊢
    · rfl
    · simp at hT
    · simp at hT
    · rename_i b a
      simp only [Option.map_some, Option.some.injEq, tcbKeyFields, Prod.mk.injEq] at hT ⊢
      refine hasSufficientBudget_congr_binding hT.2.2.1 (fun sc hsc => ?_)
      have hNe : sc ≠ S := fun h => hNo a hp (h ▸ hsc)
      have hNeO : sc.toObjId ≠ S.toObjId := fun h => hNe (SeLe4n.SchedContextId.toObjId_injective _ _ h)
      exact getSchedContext?_budget_of_keyInputsOf (hFrame _ hNeO)

/-- What a key write on `tid` keeps: no key input but `tid`'s TCB moves, no run
queue gains a member, and no current slot or flag moves. -/
def keyWriteSlotFrame (tid : SeLe4n.ThreadId) (pre post : SystemState) : Prop :=
  keyInputsEqExcept tid pre post ∧
  (∀ c t, post.queuedOn c t = true → pre.queuedOn c t = true) ∧
  (∀ c, post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c) ∧
  (∀ c, post.scheduler.reschedulePendingOnCore c = pre.scheduler.reschedulePendingOnCore c) ∧
  post.objects.invExt

theorem keyWriteSlotFrame_refl {tid : SeLe4n.ThreadId} {st : SystemState} {t : TCB}
    (hT : st.objects[tid.toObjId]? = some (.tcb t)) (hInv : st.objects.invExt) :
    keyWriteSlotFrame tid st st :=
  ⟨⟨fun _ _ => rfl, ⟨fun sc h => (by rw [hT] at h; cases h), fun sc h => (by rw [hT] at h; cases h)⟩⟩,
   fun _ _ h => h, fun _ => rfl, fun _ => rfl, hInv⟩

/-- A TCB stored over `tid`'s TCB, keeping its run-queue core, keeps the frame. -/
theorem keyWriteSlotFrame_insertTcb {tid : SeLe4n.ThreadId} {pre s : SystemState} {t' t0 : TCB}
    (h : keyWriteSlotFrame tid pre s) (hT0 : s.objects[tid.toObjId]? = some (.tcb t0))
    (hc : t'.runCoreCode = t0.runCoreCode) :
    keyWriteSlotFrame tid pre { s with objects := s.objects.insert tid.toObjId (.tcb t') } := by
  obtain ⟨hK, hRq, hCur, hFl, hInv⟩ := h
  have hAgree : SystemState.RunCoresAgree
      { s with objects := s.objects.insert tid.toObjId (.tcb t') } s := fun y => by
    unfold SystemState.getTcb?
    by_cases hy : y.toObjId = tid.toObjId
    · rw [hy, insertObjects_getElem_self s _ _ hInv, hT0]; simp [hc]
    · rw [insertObjects_getElem_ne s _ _ _ hy hInv]
  refine ⟨⟨fun oid hne => ?_, ⟨hK.2.1, fun sc hs => ?_⟩⟩,
    fun c t ht => hRq c t (by rwa [hAgree.queuedOn] at ht), hCur, hFl,
    RobinHood.RHTable.insert_preserves_invExt _ _ _ hInv⟩
  · rw [insertObjects_getElem_ne s _ _ oid hne hInv]; exact hK.1 oid hne
  · rw [insertObjects_getElem_self s _ _ hInv] at hs; cases hs

/-- Re-keying a queued `tid` through its TCB run-queue links keeps the frame:
the links are no key input (WS-ZA ZA4.5). -/
theorem keyWriteSlotFrame_runRequeue {tid : SeLe4n.ThreadId} {pre s : SystemState}
    (h : keyWriteSlotFrame tid pre s) (c : CoreId) (p : SeLe4n.Priority)
    (hMem : s.queuedOn c tid = true) :
    keyWriteSlotFrame tid pre (s.runRequeueOnCore c tid p) := by
  obtain ⟨hK, hRq, hCur, hFl, hInv⟩ := h
  refine ⟨hK.trans_offRunLinks (SystemState.runRequeueOnCore_objectsAgreeOffRunLinks _ c tid _)
      (fun y hy => SystemState.runRequeueOnCore_runCoreCode_ne _ c tid y _ hy),
    fun c' t ht => hRq c' t ?_, fun c' => ?_, fun c' => ?_,
    SystemState.runRequeueOnCore_objects_invExt _ _ _ _ hInv⟩
  · rw [SystemState.runRequeueOnCore_queuedOn] at ht
    split at ht
    · rename_i hy; subst hy
      by_cases hcc : c' = c
      · subst hcc; exact hMem
      · simp [hcc] at ht
    · exact ht
  · rw [SystemState.runRequeueOnCore_scheduler, SchedulerState.setRunQueueOnCore_currentOnCore,
      SchedulerState.setRunQueueEndsOnCore_currentOnCore]; exact hCur c'
  · rw [SystemState.runRequeueOnCore_scheduler, SchedulerState.setRunQueueOnCore_reschedulePendingOnCore,
      SchedulerState.setRunQueueEndsOnCore_reschedulePendingOnCore]; exact hFl c'

/-- Configure's bound-thread propagation is a key write on the bound thread. -/
theorem schedContextConfigureBoundPropagate_keyWriteSlotFrame (stStored : SystemState)
    (scId : SeLe4n.SchedContextId) (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (hBound : stStored.getTcb? boundTid = some boundTcb) (priority domain : Nat)
    (hInv : stStored.objects.invExt) :
    keyWriteSlotFrame boundTid stStored
      (SchedContextOps.schedContextConfigureBoundPropagate stStored scId boundTid boundTcb hBound
        priority domain) := by
  have hBTRaw := (SystemState.getTcb?_eq_some_iff stStored boundTid boundTcb).mp hBound
  have h0 := keyWriteSlotFrame_refl hBTRaw hInv
  unfold SchedContextOps.schedContextConfigureBoundPropagate
  dsimp only [SystemState.rewriteObject]
  split
  · split
    · split
      · exact h0
      · split
        · rename_i hMem
          refine keyWriteSlotFrame_runRequeue ?_ _ _ hMem
          exact keyWriteSlotFrame_insertTcb h0 hBTRaw rfl
        · exact keyWriteSlotFrame_insertTcb h0 hBTRaw rfl
    · rename_i currentTcb hCurrent _ _
      refine keyWriteSlotFrame_insertTcb ?_
        ((SystemState.getTcb?_eq_some_iff _ boundTid currentTcb).mp hCurrent) rfl
      split
      · exact h0
      · split
        · rename_i hMem
          refine keyWriteSlotFrame_runRequeue ?_ _ _ hMem
          exact keyWriteSlotFrame_insertTcb h0 hBTRaw rfl
        · exact keyWriteSlotFrame_insertTcb h0 hBTRaw rfl
  · split
    · exact h0
    · split
      · rename_i hMem
        refine keyWriteSlotFrame_runRequeue ?_ _ _ hMem
        exact keyWriteSlotFrame_insertTcb h0 hBTRaw rfl
      · exact keyWriteSlotFrame_insertTcb h0 hBTRaw rfl

/-- **Configure covers.**  The context's deadline write is read only by the
thread the context names as bound (`schedContextBindingBidirectional`), and
that thread's key write ends in the key hook; with no live bound thread the
write moves no thread's key. -/
theorem schedContextConfigure_stepCovers (st st' : SystemState) (vScId : SeLe4n.ValidObjId)
    (budget period priority deadline domain : Nat) (e : CoreId)
    (hObjInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st)
    (hStep : SchedContextOps.schedContextConfigure vScId budget period priority deadline domain st
      = .ok ((), st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold SchedContextOps.schedContextConfigure at hStep
  split at hStep
  · contradiction
  · split at hStep
    · rename_i sc hSc
      dsimp only [] at hStep
      split at hStep
      · split at hStep
        · contradiction
        · rename_i stStored hStore
          have hScRaw := (SystemState.getSchedContext?_eq_some_iff st _ sc).mp hSc
          have hInvCl := SchedContextOps.purgeReplenishment_objects_invExt st ⟨vScId.val.toNat⟩ hObjInv
          have hInvSt := storeObject_preserves_objects_invExt _ stStored _ _ hInvCl hStore
          have hSchedSt := storeObject_scheduler_eq _ stStored _ _ hStore
          have hAtS := storeObject_objects_eq _ stStored _ _ hInvCl hStore
          -- The purge rewrites release links alone, which are no key input.
          have hNeS : ∀ oid, oid ≠ vScId.val →
              keyInputsOf stStored.objects[oid]? = keyInputsOf st.objects[oid]? := by
            intro oid h
            rw [storeObject_objects_ne _ stStored vScId.val oid _ h hInvCl hStore]
            exact keyInputsEq_of_objectsAgreeOffReleaseLinks
              (SchedContextOps.purgeReplenishment_agree st ⟨vScId.val.toNat⟩) oid
          have hCurSt : ∀ c, stStored.scheduler.currentOnCore c = st.scheduler.currentOnCore c := by
            intro c; rw [hSchedSt]; exact SchedContextOps.purgeReplenishment_currentOnCore _ _ c
          have hFlSt : ∀ c, stStored.scheduler.reschedulePendingOnCore c =
              st.scheduler.reschedulePendingOnCore c := by
            intro c; rw [hSchedSt]
            exact SchedContextOps.purgeReplenishment_reschedulePendingOnCore _ _ c
          have hGetSt : ∀ t, stStored.getTcb? t = st.getTcb? t := by
            intro t
            unfold SystemState.getTcb?
            by_cases h : t.toObjId = vScId.val
            · rw [h, hAtS]; rw [show vScId.val = (SchedContextId.ofObjId vScId.val).toObjId from rfl,
                hScRaw]
            · rw [storeObject_objects_ne _ stStored vScId.val _ _ h hInvCl hStore]
              have := SchedContextOps.purgeReplenishment_getTcb? st ⟨vScId.val.toNat⟩ t
              unfold SystemState.getTcb? at this
              exact this
          have hRqSt : ∀ c t, stStored.queuedOn c t = st.queuedOn c t := fun c t => by
            unfold SystemState.queuedOn; rw [hGetSt]
          have hKeySt : ∀ t, (∀ tcb, st.getTcb? t = some tcb →
              tcb.schedContextBinding.scId? ≠ some (SchedContextId.ofObjId vScId.val)) →
              schedKeyView stStored t = schedKeyView st t :=
            fun t hNo => schedKeyView_eq_of_scSlotWrite (S := SchedContextId.ofObjId vScId.val) (fun oid h => hNeS oid h)
              hScRaw hAtS hNo
          have hEligSt : ∀ t, (∀ tcb, st.getTcb? t = some tcb →
              tcb.schedContextBinding.scId? ≠ some (SchedContextId.ofObjId vScId.val)) →
              budgetEligibleView stStored t = budgetEligibleView st t :=
            fun t hNo => budgetEligibleView_eq_of_scSlotWrite (S := SchedContextId.ofObjId vScId.val) (fun oid h => hNeS oid h)
              hScRaw hAtS hNo
          have hReader : ∀ t tcb, st.getTcb? t = some tcb →
              tcb.schedContextBinding.scId? = some (SchedContextId.ofObjId vScId.val) →
              sc.boundThread = some t := by
            intro t tcb hT hB
            obtain ⟨sc', hSc', hBT⟩ := hBi t tcb _ ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hB
            rw [hScRaw] at hSc'; cases hSc'; exact hBT
          have hNoReader : (∀ t tcb, st.getTcb? t = some tcb →
              tcb.schedContextBinding.scId? ≠ some (SchedContextId.ofObjId vScId.val)) →
              stepCovers e st stStored := fun hNo =>
            ⟨reschedulePendingCovers_of_frame (fun t => hKeySt t (hNo t)) (fun t => hEligSt t (hNo t))
              (fun c _ => Or.inr ⟨fun t ht => by rwa [hRqSt] at ht, hCurSt c⟩),
             fun c _ h => by rw [hFlSt]; exact h⟩
          split at hStep
          · rename_i hBT
            cases hStep
            refine ⟨hNoReader fun t tcb hT hB => ?_, hInvSt⟩
            have := hReader t tcb hT hB; rw [hBT] at this; cases this
          · rename_i boundTid hBT
            split at hStep
            · rename_i boundTcb hBound _
              cases hStep
              have hFr := schedContextConfigureBoundPropagate_keyWriteSlotFrame stStored ⟨vScId.val.toNat⟩ boundTid
                boundTcb hBound priority domain hInvSt
              have hPre : st.getTcb? boundTid = some boundTcb := by rw [← hGetSt]; exact hBound
              -- The key hook over the candidacy hook, read against the pre-state's
              -- TCB, is the pre-state hook: it flags the bound thread's key change
              -- and the budget the reset hands it.
              rw [markKeyChangeFor_markCandidacyGainFor_eq (mid :=
                SchedContextOps.schedContextConfigureBoundPropagate stStored ⟨vScId.val.toNat⟩
                  boundTid boundTcb hBound priority domain) hPre]
              have hNoOther : ∀ t, t ≠ boundTid → ∀ tcb, st.getTcb? t = some tcb →
                  tcb.schedContextBinding.scId? ≠ some (SchedContextId.ofObjId vScId.val) := by
                intro t ht tcb hT hB
                have := hReader t tcb hT hB; rw [hBT] at this; exact ht (Option.some.inj this).symm
              have hX : stepCovers e st (markKeyChangeFrom st
                    (SchedContextOps.schedContextConfigureBoundPropagate stStored ⟨vScId.val.toNat⟩
                      boundTid boundTcb hBound priority domain) boundTid) ∧
                  (markKeyChangeFrom st
                    (SchedContextOps.schedContextConfigureBoundPropagate stStored ⟨vScId.val.toNat⟩
                      boundTid boundTcb hBound priority domain) boundTid).objects.invExt := by
                refine ⟨⟨markKeyChangeFrom_covers (fun t ht => ⟨?_, ?_⟩)
                    (fun c _ => Or.inr ⟨fun t ht => ?_, ?_⟩),
                  fun c _ h => markKeyChangeFrom_reschedulePendingOnCore_mono _ _ _ _ ?_⟩, ?_⟩
                · rw [schedKeyView_eq_of_keyInputsEqExcept hFr.1 ht]
                  exact hKeySt t (hNoOther t ht)
                · rw [budgetEligibleView_eq_of_keyInputsEqExcept hFr.1 ht]
                  exact hEligSt t (hNoOther t ht)
                · have := hFr.2.1 c t ht; rwa [hRqSt] at this
                · rw [hFr.2.2.1, hCurSt]
                · rw [hFr.2.2.2.1, hFlSt]; exact h
                · rw [markKeyChangeFrom_objects]; exact hFr.2.2.2.2
              -- The bound thread's chain re-walk: the identity, or one walk.
              generalize markKeyChangeFrom st
                  (SchedContextOps.schedContextConfigureBoundPropagate stStored ⟨vScId.val.toNat⟩
                    boundTid boundTcb hBound priority domain) boundTid = X at hX ⊢
              have hRe := PriorityInheritance.repropagateFromWaiter_preserves
                (fun s => stepCovers e X s ∧ s.objects.invExt) X boundTid
                (determineTargetCore st boundTid) st.objectIndex.length
                (fun server _ => propagatePipChainCrossCore_stepCovers e _ _ _ server hX.2)
                ⟨stepCovers_refl e _, hX.2⟩
              exact ⟨stepCovers_trans hX.1 hRe.1, hRe.2⟩
            · rename_i hNone
              cases hStep
              refine ⟨hNoReader fun t tcb hT hB => ?_, hInvSt⟩
              have := hReader t tcb hT hB; rw [hBT] at this; cases this
              rw [← hGetSt] at hT
              exact absurd (SystemState.getTcbWitnessed?_eq_some hT) (by rw [hNone]; simp)
      · contradiction
    · contradiction

/-! ### The yield -/

/-- The slice expiry writes the caller's `timeSlice`, which is no key input,
and core `e`'s queue. -/
theorem sliceExpireOnCore_stepCovers (e : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hInv : st.objects.invExt) :
    stepCovers e st (sliceExpireOnCore st e tid tcb hTcb) := by
  have hO := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  refine stepCovers_of_local_slots ?_ ?_ ?_ ?_
  · exact schedKeyView_of_keyInputsEq_offRunLinks
      (keyInputsEq_rewriteObject (SystemState.rewriteAdmissible_tcb hTcb _) hInv
        (by rw [hO]; rfl))
      (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ e tid _)
  · exact budgetEligibleView_of_keyInputsEq_offRunLinks
      (keyInputsEq_rewriteObject (SystemState.rewriteAdmissible_tcb hTcb _) hInv
        (by rw [hO]; rfl))
      (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ e tid _)
  · intro c hc t ht
    have := SystemState.runEnqueueOnCore_queuedOn_imp_ne hc ht
    rwa [(SystemState.RunCoresAgree.rewriteObject_tcb
      (tcb' := { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }) hTcb _ hInv rfl).queuedOn]
      at this
  · intro c hc
    have hne : e ≠ c := Ne.symm hc
    simp [sliceExpireOnCore, hne, SystemState.rewriteObject_scheduler,
      SystemState.runEnqueueOnCore_runQueueOnCore_ne _ _ _ _ _ hne]

/-- **The budget spend and its key hook cover.**  The spend rewrites the
SchedContext's budget and deadline — a key input only the caller reads
(`schedContextBindingBidirectional`) — refills on core `e` and queues the
caller there.  The caller's key hook flags any core its moved key stales. -/
theorem spendBudgetKeyHook_stepCovers (st : SystemState) (e : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (scId : SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (ticks : Nat) (hObjInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st)
    (hBindId : tcb.schedContextBinding.scId? = some scId) :
    stepCovers e st (markKeyChangeFor (spendBudgetOnCore st e tid scId sc hSc ticks) tid
      (effectiveSchedParams st tcb)) ∧
    (markKeyChangeFor (spendBudgetOnCore st e tid scId sc hSc ticks) tid
      (effectiveSchedParams st tcb)).objects.invExt := by
  have hTRaw := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  have hScRaw := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hSc
  have hAdm := SystemState.rewriteAdmissible_schedContext hSc
    (cbsUpdateDeadline (scheduleReplenishment (consumeBudget sc ticks)
      st.machine.timer ⟨sc.budgetRemaining.val⟩) st.machine.timer true)
  have hAt := SystemState.rewriteObject_objects_self st scId.toObjId _ hAdm hObjInv
  have hNe : ∀ oid, scId.toObjId ≠ oid →
      (st.rewriteObject scId.toObjId _ hAdm).objects[oid]? = st.objects[oid]? :=
    fun oid h => SystemState.rewriteObject_objects_ne st scId.toObjId oid _ hAdm h hObjInv
  unfold spendBudgetOnCore
  dsimp only
  refine ⟨⟨markKeyChangeFor_covers hTcb (fun t ht => ?_)
    (candidacyNotGained_of_budget_mono (fun y => ?_) (fun s hs => ?_))
    (fun c hc => Or.inr ⟨?_, ?_⟩),
    fun c hc hp => markKeyChangeFor_reschedulePendingOnCore_mono _ _ _ _ ?_⟩, ?_⟩
  · rw [schedKeyView_of_objectsAgreeOffRunLinks
      (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ e tid _) t,
      schedKeyView_eq_of_keyInputsEq
        (keyInputsEq_of_objectsAgreeOffReleaseLinks (replenishOnCore_agree _ e scId)) t]
    refine schedKeyView_eq_of_scSlotWrite (fun oid h => ?_) hScRaw hAt
      (fun tcb' hT' hB' => ht ?_)
    · show keyInputsOf (st.rewriteObject scId.toObjId _ hAdm).objects[oid]? = _
      rw [hNe oid (Ne.symm h)]
    · obtain ⟨sc1, h1, hb1⟩ := hBi t tcb' scId
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT') hB'
      obtain ⟨sc2, h2, hb2⟩ := hBi tid tcb scId hTRaw hBindId
      rw [hScRaw] at h1 h2
      cases h1; cases h2
      rw [hb1] at hb2
      exact Option.some.inj hb2
  · -- The spend rewrites a context, no binding.
    rw [TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.schedContextBinding
      ((SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ e tid _).getTcb? y),
      replenishOnCore_getTcb?]
    exact congrArg (Option.map TCB.schedContextBinding)
      (SystemState.rewriteObject_schedContext_getTcb? st _ _ hAdm hObjInv y)
  · -- The spend only consumes budget: no context's budget goes from empty to
    -- positive.
    rw [(SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ e tid _).getSchedContext?,
      (replenishOnCore_agree _ e scId).getSchedContext?_map _ (fun _ => rfl) s] at hs
    change ((st.rewriteObject scId.toObjId _ hAdm).getSchedContext? s).map _ = _ at hs
    by_cases hS : s = scId
    · subst hS
      rw [SystemState.rewriteObject_schedContext_getSchedContext?_self st s _ hAdm hObjInv] at hs
      rw [hSc]
      simp only [Option.map_some, Option.some.injEq, cbsUpdateDeadline, scheduleReplenishment,
        consumeBudget, Budget.decrement, Budget.isPositive, decide_eq_true_eq] at hs ⊢
      split at hs <;> simp_all <;> omega
    · rw [SystemState.rewriteObject_getSchedContext?_ne st _ _ hAdm hObjInv s
        (fun h => hS (SchedContextId.toObjId_injective _ _ h).symm)] at hs
      exact hs
  · intro t ht
    have := SystemState.runEnqueueOnCore_queuedOn_imp_ne hc ht
    have hRep : ∀ c t, (replenishOnCore (st.rewriteObject scId.toObjId _ hAdm) e scId).queuedOn c t =
        (st.rewriteObject scId.toObjId _ hAdm).queuedOn c t := fun c t =>
      SystemState.queuedOn_of_getTcb? (replenishOnCore_getTcb? _ e scId t) c
    rwa [hRep, (SystemState.RunCoresAgree.rewriteObject_not_tcb hAdm hObjInv
      (fun t h => by rw [hScRaw] at h; cases h) (fun t h => by cases h)).queuedOn] at this
  · simp [replenishOnCore_currentOnCore, SystemState.rewriteObject_scheduler]
  · simpa [SystemState.rewriteObject_scheduler] using hp
  · rw [markKeyChangeFor_objects]
    exact SystemState.runEnqueueOnCore_objects_invExt _ e tid _
      (SystemState.releasePlace_objects_invExt _ e scId
        (SystemState.rewriteObject_preserves_objects_invExt st _ _ hAdm hObjInv))

/-- **The yield's charge covers**: the unbound arm is a slice expiry on core
`e`, the bound arm a budget spend ending in the caller's key hook. -/
theorem yieldChargeOnCore_stepCovers (st st' : SystemState) (e : CoreId)
    (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st)
    (h : yieldChargeOnCore st e tid = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold yieldChargeOnCore at h
  split at h
  · cases h
  · rename_i tcb hTcb _
    split at h
    · cases h
      exact ⟨sliceExpireOnCore_stepCovers e st tid tcb hTcb hObjInv,
        sliceExpireOnCore_objects_invExt st e tid tcb hTcb hObjInv⟩
    · rename_i scId hBind
      split at h
      · rename_i sc hSc _
        cases h
        exact spendBudgetKeyHook_stepCovers st e tid tcb hTcb scId sc hSc _ hObjInv hBi
          (by rw [hBind]; rfl)
      · cases h
    · rename_i scId owner hBind
      split at h
      · rename_i sc hSc _
        cases h
        exact spendBudgetKeyHook_stepCovers st e tid tcb hTcb scId sc hSc _ hObjInv hBi
          (by rw [hBind]; rfl)
      · cases h

/-- **The yield covers**: its charge covers and the scheduling point on core
`e` covers (`scheduleEffectiveOnCore_stepCovers`). -/
theorem yieldOnCore_stepCovers (st st' : SystemState) (e : CoreId)
    (hObjInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st)
    (h : yieldOnCore st e = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold yieldOnCore at h
  split at h
  · cases h
  · rename_i tid _
    split at h
    · cases h
    · rename_i st1 hCharge
      obtain ⟨h1, hInv1⟩ := yieldChargeOnCore_stepCovers st st1 e tid hObjInv hBi hCharge
      exact ⟨stepCovers_trans h1 (scheduleEffectiveOnCore_stepCovers e st1 _ hInv1 h),
        scheduleEffectiveOnCore_preserves_objects_invExt st1 e _ hInv1 h⟩

/-! ### Scheduling-context bind and unbind -/

/-- A re-key through the TCB run-queue links keeps every core's membership and
slot, and drops no flag (WS-ZA ZA4.5). -/
theorem runRequeue_slots (S : SystemState) (h c : CoreId) (x : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hMem : S.queuedOn h x = true) :
    (∀ t, (S.runRequeueOnCore h x p).queuedOn c t = true → S.queuedOn c t = true) ∧
    (S.runRequeueOnCore h x p).scheduler.currentOnCore c = S.scheduler.currentOnCore c ∧
    (S.runRequeueOnCore h x p).scheduler.reschedulePendingOnCore c =
      S.scheduler.reschedulePendingOnCore c := by
  refine ⟨fun t ht => ?_, by simp, by simp⟩
  rw [SystemState.runRequeueOnCore_queuedOn] at ht
  split at ht
  · rename_i hy; subst hy
    by_cases hc : c = h
    · subst hc; exact hMem
    · simp [hc] at ht
  · exact ht

/-- A placement through the TCB run-queue links, flagging its core, keeps every
other core's membership and slot, and drops no flag (WS-ZA ZA4.5). -/
theorem runEnqueueMark_slots (S : SystemState) (h c : CoreId)
    (x : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    ((S.runEnqueueOnCore h x p).markReschedulePendingOnCore h).scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, ((S.runEnqueueOnCore h x p).markReschedulePendingOnCore h).queuedOn c t = true →
          S.queuedOn c t = true) ∧
        ((S.runEnqueueOnCore h x p).markReschedulePendingOnCore h).scheduler.currentOnCore c =
          S.scheduler.currentOnCore c) := by
  simp only [SystemState.markReschedulePendingOnCore]
  by_cases hh : h = c
  · subst hh; exact Or.inl (SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_self _ _)
  · exact Or.inr ⟨fun t ht => SystemState.runEnqueueOnCore_queuedOn_imp_ne (Ne.symm hh) ht, by simp⟩

/-- A step's slots, covered against a state whose scheduler and run-queue cores
equal those of `st`, are covered against `st`. -/
theorem slots_bridge {S st post : SystemState} {c : CoreId}
    (hA : SystemState.RunCoresAgree S st) (hSch : S.scheduler = st.scheduler)
    (h : post.scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, post.queuedOn c t = true → S.queuedOn c t = true) ∧
        post.scheduler.currentOnCore c = S.scheduler.currentOnCore c)) :
    post.scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, post.queuedOn c t = true → st.queuedOn c t = true) ∧
        post.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :=
  h.imp id fun ⟨hq, hc⟩ => ⟨fun t ht => by rw [← hA.queuedOn]; exact hq t ht, by rw [hc, hSch]⟩

theorem runEnqueueMark_flag_mono (S : SystemState) (h c : CoreId) (x : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hF : S.scheduler.reschedulePendingOnCore c = true) :
    ((S.runEnqueueOnCore h x p).markReschedulePendingOnCore h).scheduler.reschedulePendingOnCore c = true := by
  simp only [SystemState.markReschedulePendingOnCore]
  by_cases hh : h = c
  · subst hh; exact SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_self _ _
  · rw [SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_ne _ _ _ hh]
    simpa using hF

/-- Bind's run-queue stage moves no run-queue core but `tid`'s. -/
theorem bindQueueStage_runCoreCode_ne (S : SystemState) (home : CoreId) (tid : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (b : Bool) (y : SeLe4n.ThreadId) (hy : y ≠ tid) :
    ((if S.queuedOn home tid then S.runRequeueOnCore home tid p
      else if b then (S.runEnqueueOnCore home tid p).markReschedulePendingOnCore home
      else S).getTcb? y).map TCB.runCoreCode = (S.getTcb? y).map TCB.runCoreCode := by
  split
  · exact SystemState.runRequeueOnCore_runCoreCode_ne _ _ _ y _ hy
  · split
    · exact SystemState.runEnqueueOnCore_runCoreCode_ne _ _ _ y _ hy
    · rfl

/-- Bind's run-queue stage flags its core or keeps every core's slots. -/
theorem bindQueueStage_slots (S : SystemState) (home : CoreId) (tid : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (b : Bool) (c : CoreId) :
    (if S.queuedOn home tid then S.runRequeueOnCore home tid p
      else if b then (S.runEnqueueOnCore home tid p).markReschedulePendingOnCore home
      else S).scheduler.reschedulePendingOnCore c = true ∨
    ((∀ t, (if S.queuedOn home tid then S.runRequeueOnCore home tid p
      else if b then (S.runEnqueueOnCore home tid p).markReschedulePendingOnCore home
      else S).queuedOn c t = true → S.queuedOn c t = true) ∧
      (if S.queuedOn home tid then S.runRequeueOnCore home tid p
      else if b then (S.runEnqueueOnCore home tid p).markReschedulePendingOnCore home
      else S).scheduler.currentOnCore c = S.scheduler.currentOnCore c) := by
  split
  · rename_i hMem
    obtain ⟨hR, hC, _⟩ := runRequeue_slots _ _ c _ _ hMem
    exact Or.inr ⟨hR, hC⟩
  · split
    · exact runEnqueueMark_slots _ _ c _ _
    · exact Or.inr ⟨fun t ht => ht, rfl⟩

/-- **Bind covers.**  The context write keeps its deadline, the thread's binding
and priority write ends in the key hook, and the one placement that grows a
queue — placing a parked thread — flags that core. -/
theorem schedContextBind_stepCovers (st st' : SystemState) (vScId : SeLe4n.ValidObjId)
    (vTid : SeLe4n.ValidThreadId) (e : CoreId) (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextBind vScId vTid st = .ok ((), st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold SchedContextOps.schedContextBind at hStep
  split at hStep
  · rename_i sc hSc _
    split at hStep
    · contradiction
    split at hStep
    · contradiction
    split at hStep
    · rename_i tcb hT
      split at hStep
      · contradiction
      split at hStep
      · contradiction
      split at hStep
      · rename_i hUnb
        cases hStep
        have hScRaw : st.objects[vScId.val]? = some (.schedContext sc) :=
          (SystemState.getSchedContext?_eq_some_iff st _ sc).mp hSc
        have hAdm : st.rewriteAdmissible vScId.val (.schedContext
            { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some vTid.val), donationOrigin := none }) :=
          SystemState.rewriteAdmissible_schedContext hSc _
        have hInv1 := SystemState.rewriteObject_preserves_objects_invExt st _ _ hAdm hObjInv
        have hK1 : keyInputsEq st (st.rewriteObject vScId.val _ hAdm) :=
          keyInputsEq_rewriteObject hAdm hObjInv (by rw [hScRaw]; rfl)
        have hT1 : (st.rewriteObject vScId.val _ hAdm).getTcb? vTid.val = some tcb :=
          (SystemState.rewriteObject_schedContext_getTcb? st _ _ hAdm hObjInv _).trans hT
        have hK2 := keyInputsEq.trans_keyInputsEqExcept hK1
          (keyInputsEqExcept_updateTcb (f := fun t => { t with
            scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode ((SchedContextBinding.bound ⟨vScId.val.toNat⟩)), scBindingOwnerCode := SeLe4n.Kernel.SchedContextBinding.ownerCode ((SchedContextBinding.bound ⟨vScId.val.toNat⟩)),
            priority := sc.priority }) hInv1 (by rw [hT1]; rfl))
        have hInv2 := SystemState.updateTcb_preserves_objects_invExt _ vTid.val
          (fun t => { t with
            scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode ((SchedContextBinding.bound ⟨vScId.val.toNat⟩)), scBindingOwnerCode := SeLe4n.Kernel.SchedContextBinding.ownerCode ((SchedContextBinding.bound ⟨vScId.val.toNat⟩)),
            priority := sc.priority }) hInv1
        -- The queue stage moves the thread through its TCB run-queue links
        -- (WS-ZA ZA4.5); only the thread's own run-queue core moves.
        have hA2 : SystemState.RunCoresAgree ((st.rewriteObject vScId.val _ hAdm).updateTcb vTid.val
            fun t => { t with
              scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode ((SchedContextBinding.bound ⟨vScId.val.toNat⟩)), scBindingOwnerCode := SeLe4n.Kernel.SchedContextBinding.ownerCode ((SchedContextBinding.bound ⟨vScId.val.toNat⟩)),
              priority := sc.priority }) st :=
          SystemState.RunCoresAgree.trans (SystemState.RunCoresAgree.updateTcb hInv1 fun _ => rfl)
            (SystemState.RunCoresAgree.rewriteObject_not_tcb hAdm hObjInv
              (fun t h => by rw [hScRaw] at h; cases h) (fun t h => by cases h))
        refine ⟨stepCovers_markKeyChangeFor hT (hK2.trans_offRunLinks ?_ ?_) ?_ ?_ ?_, ?_⟩
        · intro x
          split
          · exact SystemState.runRequeueOnCore_objectsAgreeOffRunLinks _ _ _ _ x
          · split
            · exact SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _ x
            · rfl
        · intro y hy
          exact bindQueueStage_runCoreCode_ne _ _ _ _ _ y hy
        · -- An unbound thread is budget-eligible already: a bind gains no candidacy.
          intro _
          simp only [budgetEligibleView, hT, Option.map_some, hasSufficientBudget, hUnb]
        · intro c hc
          exact slots_bridge hA2
            (by simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler])
            (bindQueueStage_slots _ _ _ _ _ c)
        · intro c _ hF
          split
          · rename_i hMem
            obtain ⟨_, _, hFl⟩ := runRequeue_slots _ _ c _ _ hMem
            rw [hFl]
            simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]; exact hF
          · split
            · exact runEnqueueMark_flag_mono _ _ _ _ _
                (by simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]; exact hF)
            · simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]; exact hF
        · rw [markKeyChangeFor_objects]
          split
          · exact SystemState.runRequeueOnCore_objects_invExt _ _ _ _ hInv2
          · split
            · exact SystemState.runEnqueueOnCore_objects_invExt _ _ _ _ hInv2
            · exact hInv2
      · contradiction
    · contradiction
  · contradiction

/-- Scheduler-record coverage: every core is flagged afterwards, or its current
slot is unchanged (queue membership lives in the TCB links, which a
scheduler-record write leaves alone; WS-ZA ZA4.5). -/
def schedSlotsCovered (s0 s1 : SchedulerState) : Prop :=
  ∀ c, s1.reschedulePendingOnCore c = true ∨ s1.currentOnCore c = s0.currentOnCore c

/-- No flag drops. -/
def schedFlagsMono (s0 s1 : SchedulerState) : Prop :=
  ∀ c, s0.reschedulePendingOnCore c = true → s1.reschedulePendingOnCore c = true

theorem schedSlotsCovered_refl (s : SchedulerState) : schedSlotsCovered s s :=
  fun _ => Or.inr rfl

theorem schedFlagsMono_refl (s : SchedulerState) : schedFlagsMono s s := fun _ h => h

theorem schedSlotsCovered_clearMark (s : SchedulerState) (r : CoreId) (v : Option SeLe4n.ThreadId) :
    schedSlotsCovered s ((s.setCurrentOnCore r v).markReschedulePendingOnCore r) ∧
      schedFlagsMono s ((s.setCurrentOnCore r v).markReschedulePendingOnCore r) := by
  refine ⟨fun c => ?_, fun c hF => ?_⟩
  · by_cases hh : r = c
    · subst hh; exact Or.inl (SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_self _ _)
    · refine Or.inr ?_
      rw [SchedulerState.markReschedulePendingOnCore_currentOnCore,
        SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hh]
  · by_cases hh : r = c
    · subst hh; exact SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_self _ _
    · rw [SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_ne _ _ _ hh,
        SchedulerState.setCurrentOnCore_reschedulePendingOnCore]; exact hF

/-- A scheduler-record step covered on every core covers. -/
theorem stepCovers_of_schedSlots {e : CoreId} (st : SystemState) (s : SchedulerState)
    (hC : schedSlotsCovered st.scheduler s) (hM : schedFlagsMono st.scheduler s) :
    stepCovers e st { st with scheduler := s } :=
  ⟨reschedulePendingCovers_of_frame (fun _ => rfl) (fun _ => rfl)
    (fun c _ => (hC c).imp id fun h => ⟨fun _ ht => ht, h⟩), fun c _ h => hM c h⟩

theorem priorityRescheduleOnCore_invExt (e : CoreId) (st st' : SystemState)
    (running? : Option CoreId) (sp : Bool) (sgi? : Option (CoreId × SgiKind))
    (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCore st running? e sp
      = .ok (st', sgi?)) :
    st'.objects.invExt := by
  rcases SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases
      st st' running? e sp sgi? h with hEq | hH
  · rw [hEq]; exact hInv
  · exact handleRescheduleSgiOnCore_preserves_objects_invExt _ e st' hInv hH

theorem unbindClear_covered (s : SchedulerState) (r? : Option CoreId) :
    schedSlotsCovered s (match r? with
      | some r => (s.setCurrentOnCore r none).markReschedulePendingOnCore r
      | none => s) ∧
    schedFlagsMono s (match r? with
      | some r => (s.setCurrentOnCore r none).markReschedulePendingOnCore r
      | none => s) := by
  cases r? with
  | none => exact ⟨schedSlotsCovered_refl s, schedFlagsMono_refl s⟩
  | some r => exact schedSlotsCovered_clearMark s r none

/-- Unbind's run-queue stage through the TCB links keeps every core flagged or
slot-unchanged against any scheduler record equal to its input's (WS-ZA ZA4.5). -/
theorem unbindQueueStage_slots (S : SystemState)
    (home : CoreId) (tid : SeLe4n.ThreadId) (p : SeLe4n.Priority) (wasCurrent : Bool)
    (c : CoreId) :
    (SchedContextOps.schedContextUnbindQueueStage S home tid p wasCurrent).scheduler.reschedulePendingOnCore c
        = true ∨
      ((∀ t, (SchedContextOps.schedContextUnbindQueueStage S home tid p wasCurrent).queuedOn c t = true →
          S.queuedOn c t = true) ∧
        (SchedContextOps.schedContextUnbindQueueStage S home tid p wasCurrent).scheduler.currentOnCore c =
          S.scheduler.currentOnCore c) := by
  unfold SchedContextOps.schedContextUnbindQueueStage
  split
  · rename_i hMem
    obtain ⟨hR, hC, _⟩ := runRequeue_slots S home c tid p hMem
    exact Or.inr ⟨hR, hC⟩
  · split
    · exact runEnqueueMark_slots S home c tid p
    · exact Or.inr ⟨fun _ h => h, rfl⟩

/-- The unbind's run-queue stage moves no run-queue core but `tid`'s. -/
theorem unbindQueueStage_runCoreCode_ne (S : SystemState)
    (home : CoreId) (tid : SeLe4n.ThreadId) (p : SeLe4n.Priority) (wasCurrent : Bool)
    (y : SeLe4n.ThreadId) (hy : y ≠ tid) :
    ((SchedContextOps.schedContextUnbindQueueStage S home tid p wasCurrent).getTcb? y).map
      TCB.runCoreCode = (S.getTcb? y).map TCB.runCoreCode := by
  unfold SchedContextOps.schedContextUnbindQueueStage
  split
  · exact SystemState.runRequeueOnCore_runCoreCode_ne _ _ _ y _ hy
  · split
    · exact SystemState.runEnqueueOnCore_runCoreCode_ne _ _ _ y _ hy
    · rfl

theorem unbindQueueStage_flag_mono (S : SystemState) (home : CoreId) (tid : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (wasCurrent : Bool) (c : CoreId)
    (hF : S.scheduler.reschedulePendingOnCore c = true) :
    (SchedContextOps.schedContextUnbindQueueStage S home tid p wasCurrent).scheduler.reschedulePendingOnCore c
      = true := by
  unfold SchedContextOps.schedContextUnbindQueueStage
  split
  · rename_i hMem
    rw [(runRequeue_slots S home c tid p hMem).2.2]; exact hF
  · split
    · exact runEnqueueMark_flag_mono S home c tid p hF
    · exact hF

/-- The unbind's stage and purge flag their core or keep every core's slots
against the stage's input. -/
theorem unbindTailStage_slots (S : SystemState) (home : CoreId) (tid : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (wasCurrent : Bool) (scId : SchedContextId) (c : CoreId) :
    (SchedContextOps.purgeReplenishment
        (SchedContextOps.schedContextUnbindQueueStage S home tid p wasCurrent) scId
        ).scheduler.reschedulePendingOnCore c = true ∨
    ((∀ t, (SchedContextOps.purgeReplenishment
        (SchedContextOps.schedContextUnbindQueueStage S home tid p wasCurrent) scId
        ).queuedOn c t = true → S.queuedOn c t = true) ∧
      (SchedContextOps.purgeReplenishment
        (SchedContextOps.schedContextUnbindQueueStage S home tid p wasCurrent) scId
        ).scheduler.currentOnCore c = S.scheduler.currentOnCore c) := by
  have h := unbindQueueStage_slots S home tid p wasCurrent c
  have hq : ∀ t, (SchedContextOps.purgeReplenishment
      (SchedContextOps.schedContextUnbindQueueStage S home tid p wasCurrent) scId).queuedOn c t =
      (SchedContextOps.schedContextUnbindQueueStage S home tid p wasCurrent).queuedOn c t :=
    fun t => SystemState.queuedOn_of_getTcb? (SchedContextOps.purgeReplenishment_getTcb? _ _ t) c
  simp only [SchedContextOps.purgeReplenishment_currentOnCore,
    SchedContextOps.purgeReplenishment_reschedulePendingOnCore, hq]
  exact h

/-- Unbind's object tail — the context write keeps its deadline, the binding
write is the bound thread's key write, the run-queue stage moves only TCB
run-queue links (flagging the core it places on), the purge is a
release-queue write — ends in the key hook. -/
theorem unbindTail_stepCovers (e : CoreId) (st1 : SystemState) (vScId : SeLe4n.ValidObjId)
    (sc : SchedContext) (tid : SeLe4n.ThreadId) (tcb : TCB) (home : CoreId)
    (prio : SeLe4n.Priority) (wasCurrent : Bool)
    (hInv : st1.objects.invExt)
    (hSc : st1.objects[vScId.val]? = some (.schedContext sc))
    (hT : st1.getTcb? tid = some tcb)
    (hAdm : st1.rewriteAdmissible vScId.val (.schedContext
      { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })) :
    stepCovers e st1 (markKeyChangeFor (markCandidacyGainFor
      (SchedContextOps.purgeReplenishment
          (SchedContextOps.schedContextUnbindQueueStage
            ((st1.rewriteObject vScId.val _ hAdm).updateTcb tid fun t =>
              { t with scBindingScCode := 0, scBindingOwnerCode := 0 })
            home tid prio wasCurrent)
          ⟨vScId.val.toNat⟩) tid (hasSufficientBudget st1 tcb))
      tid (effectiveSchedParams st1 tcb)) := by
  have hK1 : keyInputsEq st1 (st1.rewriteObject vScId.val _ hAdm) :=
    keyInputsEq_rewriteObject hAdm hInv (by rw [hSc]; rfl)
  have hInv1 := SystemState.rewriteObject_preserves_objects_invExt st1 _ _ hAdm hInv
  have hT1 : (st1.rewriteObject vScId.val _ hAdm).getTcb? tid = some tcb :=
    (SystemState.rewriteObject_schedContext_getTcb? st1 _ _ hAdm hInv _).trans hT
  have hK2 := keyInputsEq.trans_keyInputsEqExcept hK1
    (keyInputsEqExcept_updateTcb (f := fun t => { t with
      scBindingScCode := 0, scBindingOwnerCode := 0 }) hInv1 (by rw [hT1]; rfl))
  have hA2 : SystemState.RunCoresAgree ((st1.rewriteObject vScId.val _ hAdm).updateTcb tid
      fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 }) st1 :=
    SystemState.RunCoresAgree.trans (SystemState.RunCoresAgree.updateTcb hInv1 fun _ => rfl)
      (SystemState.RunCoresAgree.rewriteObject_not_tcb hAdm hInv
        (fun t h => by rw [hSc] at h; cases h) (fun t h => by cases h))
  -- The binding write is the bound thread's key and candidacy change: the
  -- pre-state hook flags both (an unbound thread is always budget-eligible).
  rw [markKeyChangeFor_markCandidacyGainFor_eq hT]
  have hKX : keyInputsEqExcept tid st1 (SchedContextOps.purgeReplenishment
      (SchedContextOps.schedContextUnbindQueueStage
        ((st1.rewriteObject vScId.val _ hAdm).updateTcb tid fun t =>
          { t with scBindingScCode := 0, scBindingOwnerCode := 0 })
        home tid prio wasCurrent)
      ⟨vScId.val.toNat⟩) := (hK2.trans_offRunLinks
      (SchedContextOps.schedContextUnbindQueueStage_objectsAgreeOffRunLinks _ _ _ _ _)
      (fun y hy => unbindQueueStage_runCoreCode_ne _ _ _ _ _ y hy)).trans_keyInputsEq
      (keyInputsEq_of_objectsAgreeOffReleaseLinks (SchedContextOps.purgeReplenishment_agree _ _))
  refine ⟨markKeyChangeFrom_covers (fun t ht => ⟨schedKeyView_eq_of_keyInputsEqExcept hKX ht,
      budgetEligibleView_eq_of_keyInputsEqExcept hKX ht⟩) (fun c _ => ?_),
    fun c _ hF => markKeyChangeFrom_reschedulePendingOnCore_mono _ _ _ _ ?_⟩
  · exact slots_bridge hA2
      (by simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler])
      (unbindTailStage_slots _ _ _ _ _ _ c)
  · simp only [SchedContextOps.purgeReplenishment_reschedulePendingOnCore]
    exact unbindQueueStage_flag_mono _ _ _ _ _ c
      (by simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]; exact hF)

/-- **Unbind covers.**  The running core's slot clear and the home-core
re-bucket flag the cores whose slots grow or move; the rest is the object tail. -/
theorem schedContextUnbind_stepCovers (st st' : SystemState) (vScId : SeLe4n.ValidObjId)
    (e : CoreId) (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold SchedContextOps.schedContextUnbind at hStep
  split at hStep
  · rename_i sc hSc _
    have hScRaw : st.objects[vScId.val]? = some (.schedContext sc) :=
      (SystemState.getSchedContext?_eq_some_iff st _ sc).mp hSc
    split at hStep
    · contradiction
    · rename_i tid _
      split at hStep
      · rename_i tcb hT
        split at hStep
        · contradiction
        · cases hStep
          constructor
          · refine stepCovers_trans ?_ (unbindTail_stepCovers e _ vScId sc tid tcb _ _ _ ?_ ?_ ?_ _)
            · exact stepCovers_of_schedSlots _ _ (unbindClear_covered _ _).1
                (unbindClear_covered _ _).2
            · exact hObjInv
            · exact hScRaw
            · exact hT
          · rw [markKeyChangeFor_objects, markCandidacyGainFor_objects]
            refine SchedContextOps.purgeReplenishment_objects_invExt _ _ ?_
            refine SchedContextOps.schedContextUnbindQueueStage_objects_invExt _ _ _ _ _
              (SystemState.updateTcb_preserves_objects_invExt _ _ _
                (SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ ?_))
            exact hObjInv
      · cases hStep
        have hAdm : st.rewriteAdmissible vScId.val (.schedContext
            { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) :=
          SystemState.rewriteAdmissible_schedContext hSc _
        have hK1 : keyInputsEq st (st.rewriteObject vScId.val _ hAdm) :=
          keyInputsEq_rewriteObject hAdm hObjInv (by rw [hScRaw]; rfl)
        have hInv1 := SystemState.rewriteObject_preserves_objects_invExt st _ _ hAdm hObjInv
        have hK2 := keyInputsEq_trans hK1
          (keyInputsEq_of_objectsAgreeOffReleaseLinks (SchedContextOps.purgeReplenishment_agree
            (st.rewriteObject vScId.val _ hAdm) ⟨vScId.val.toNat⟩))
        refine ⟨stepCovers_of_frame (schedKeyView_eq_of_keyInputsEq hK2)
          (budgetEligibleView_eq_of_keyInputsEq hK2)
          (fun c _ t ht => ?_) (fun c _ => ?_) (fun c _ hF => ?_), ?_⟩
        · rw [SystemState.queuedOn_of_getTcb? (SchedContextOps.purgeReplenishment_getTcb? _ _ t),
            (SystemState.RunCoresAgree.rewriteObject_not_tcb hAdm hObjInv
              (fun t h => by rw [hScRaw] at h; cases h) (fun t h => by cases h)).queuedOn] at ht
          exact ht
        · dsimp only []; rw [SchedContextOps.purgeReplenishment_currentOnCore]; rfl
        · dsimp only []
          rw [SchedContextOps.purgeReplenishment_reschedulePendingOnCore]; exact hF
        · dsimp only []
          exact SchedContextOps.purgeReplenishment_objects_invExt _ _ hInv1
  · contradiction

/-- The dispatched unbind: the single-core unbind, then the running core's
scheduling point. -/
theorem schedContextUnbindOnCore_stepCovers (st st' : SystemState) (vScId : SeLe4n.ValidObjId)
    (e : CoreId) (sgi? : Option (CoreId × SgiKind)) (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextUnbindOnCore vScId e st = .ok (st', sgi?)) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold SchedContextOps.schedContextUnbindOnCore at hStep
  split at hStep
  · contradiction
  · rename_i stMid hUnbind
    obtain ⟨h1, hInvMid⟩ := schedContextUnbind_stepCovers st stMid vScId e hObjInv hUnbind
    exact ⟨stepCovers_trans h1 (priorityRescheduleOnCore_stepCovers e _ _ _ _ _ hInvMid hStep),
      priorityRescheduleOnCore_invExt e _ _ _ _ _ hInvMid hStep⟩

/-! ### Priority inheritance and priority control -/

theorem applyPriorityChangeOnCore_stepCovers (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (p : SeLe4n.Priority) (e : CoreId) (b : Bool)
    (sgi : Option (CoreId × SgiKind)) (hInv : st.objects.invExt)
    (hT : st.getTcb? tid = some tcb)
    (hStep : SchedContext.PriorityManagement.applyPriorityChangeOnCore st tid tcb p e b
      = .ok (st', sgi)) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold SchedContext.PriorityManagement.applyPriorityChangeOnCore at hStep
  obtain ⟨objs, hU⟩ :=
    SchedContext.PriorityManagement.updatePrioritySource_only_modifies_objects st tid tcb p
  have hInvU := SchedContext.PriorityManagement.updatePrioritySource_preserves_objects_invExt
    st tid tcb p hInv
  have hKeys := updatePrioritySource_keyInputsEqExcept st tid tcb p hInv hT
  generalize hMid : SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
    (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) tid p
    (determineTargetCore st tid) = mid at hStep
  have hMidA : mid.objectsAgreeOffRunLinks (SchedContext.PriorityManagement.updatePrioritySource
      st tid tcb p) := by
    rw [← hMid]
    exact SchedContext.PriorityManagement.migrateRunQueueBucketOnCore_objectsAgreeOffRunLinks _ _ _ _
  have hAU : SystemState.RunCoresAgree (SchedContext.PriorityManagement.updatePrioritySource
      st tid tcb p) st := fun y =>
    SchedContext.PriorityManagement.updatePrioritySource_runCoreCode st tid tcb p hInv y
  have hMidSched : ∀ c, (∀ x, mid.queuedOn c x = true → st.queuedOn c x = true) ∧
      mid.scheduler.currentOnCore c = st.scheduler.currentOnCore c ∧
      mid.scheduler.reschedulePendingOnCore c = st.scheduler.reschedulePendingOnCore c := by
    intro c
    subst hMid
    refine ⟨fun x hx => ?_, ?_, ?_⟩
    · rw [← hAU.queuedOn]
      unfold SchedContext.PriorityManagement.migrateRunQueueBucketOnCore at hx
      split at hx
      · rename_i hMem
        exact (runRequeue_slots _ _ c _ _ hMem).1 x hx
      · exact hx
    · rw [migrateRunQueueBucketOnCore_currentOnCore, hU]
    · unfold SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
      split
      · simp [SchedulerState.reschedulePendingOnCore, SchedulerState.setRunQueueOnCore,
          SchedulerState.setRunQueueEndsOnCore, hU]
      · rw [hU]
  have hKeysMid : keyInputsEqExcept tid st mid := by
    refine hKeys.trans_offRunLinks hMidA fun y hy => ?_
    rw [← hMid]
    unfold SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
    split
    · exact SystemState.runRequeueOnCore_runCoreCode_ne _ _ _ y _ hy
    · rfl
  have h1 := stepCovers_markKeyChangeFor (e := e) hT hKeysMid
    (candidacyNotGained_of_eq (budgetEligibleView_self_of_bindingsAgree hKeysMid
      ((bindingsAgree.of_objectsAgreeOffRunLinks hMidA).trans
        (updatePrioritySource_bindingsAgree st tid tcb p hInv))).symm)
    (fun c _ => Or.inr ⟨(hMidSched c).1, (hMidSched c).2.1⟩)
    (fun c _ hp => by rw [(hMidSched c).2.2]; exact hp)
  have hInvMk : (markKeyChangeFor mid tid (effectiveSchedParams st tcb)).objects.invExt := by
    rw [markKeyChangeFor_objects, ← hMid]
    exact SchedContext.PriorityManagement.migrateRunQueueBucketOnCore_objects_invExt _ _ _ _ hInvU
  -- The waiter-side chain re-walk: the identity, or one chain walk.
  have hRe : stepCovers e (markKeyChangeFor mid tid (effectiveSchedParams st tcb))
        (PriorityInheritance.repropagateFromWaiter
          (markKeyChangeFor mid tid (effectiveSchedParams st tcb)) tid e st.objectIndex.length) ∧
      (PriorityInheritance.repropagateFromWaiter
          (markKeyChangeFor mid tid (effectiveSchedParams st tcb)) tid e
          st.objectIndex.length).objects.invExt :=
    PriorityInheritance.repropagateFromWaiter_preserves
      (fun s => stepCovers e (markKeyChangeFor mid tid (effectiveSchedParams st tcb)) s ∧
        s.objects.invExt) _ tid _ _
      (fun server _ => propagatePipChainCrossCore_stepCovers e _ _ _ server hInvMk)
      ⟨stepCovers_refl e _, hInvMk⟩
  have h2 := priorityRescheduleOnCore_stepCovers e _ st' _ _ _ hRe.2 hStep
  refine ⟨stepCovers_trans (stepCovers_trans h1 hRe.1) h2, ?_⟩
  rcases SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases
      _ st' _ e _ _ hStep with hEq | hH
  · rw [hEq]; exact hRe.2
  · exact handleRescheduleSgiOnCore_preserves_objects_invExt _ e st' hRe.2 hH

theorem setPriorityOnCore_stepCovers (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (p : SeLe4n.Priority) (e : CoreId)
    (sgi : Option (CoreId × SgiKind)) (hInv : st.objects.invExt)
    (hStep : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid p e
      = .ok (st', sgi)) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold SchedContext.PriorityManagement.setPriorityOnCore at hStep
  split at hStep
  · split at hStep
    · contradiction
    · split at hStep
      · rename_i targetTcb hTarget
        exact applyPriorityChangeOnCore_stepCovers st st' _ targetTcb p e _ _ hInv hTarget hStep
      · contradiction
  · contradiction

theorem setMCPriorityOnCore_stepCovers (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (p : SeLe4n.Priority) (e : CoreId)
    (sgi : Option (CoreId × SgiKind)) (hInv : st.objects.invExt)
    (hStep : SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid p e
      = .ok (st', sgi)) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold SchedContext.PriorityManagement.setMCPriorityOnCore at hStep
  split at hStep
  · split at hStep
    · contradiction
    · split at hStep
      · rename_i targetTcb hTarget _
        have hPreRaw := (SystemState.getTcb?_eq_some_iff st vTargetTid.val targetTcb).mp hTarget
        have kM := insertObjects_tcbKeyKeeping_keyFrame (tcb' := { targetTcb with
          maxControlledPriority := p }) hInv hPreRaw rfl
        have hEq : st.rewriteObject vTargetTid.val.toObjId
            (.tcb { targetTcb with maxControlledPriority := p })
            (SystemState.rewriteAdmissible_tcb hTarget _) =
            { st with objects := (st.objects.insert vTargetTid.val.toObjId
              (.tcb { targetTcb with maxControlledPriority := p })) } := rfl
        have hAt : (st.rewriteObject vTargetTid.val.toObjId
            (.tcb { targetTcb with maxControlledPriority := p })
            (SystemState.rewriteAdmissible_tcb hTarget _)).getTcb? vTargetTid.val =
            some { targetTcb with maxControlledPriority := p } := by
          rw [hEq]
          exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr
            (insertObjects_getElem_self st _ _ hInv)
        have sM : stepCovers e st (st.rewriteObject vTargetTid.val.toObjId
            (.tcb { targetTcb with maxControlledPriority := p })
            (SystemState.rewriteAdmissible_tcb hTarget _)) := by
          rw [hEq]; exact kM.stepCovers
        dsimp only at hStep
        split at hStep
        · obtain ⟨h2, hI⟩ := applyPriorityChangeOnCore_stepCovers _ st' vTargetTid.val _ p e _ _
            (by rw [hEq]; exact kM.2.2) hAt hStep
          exact ⟨stepCovers_trans sM h2, hI⟩
        · cases hStep
          exact ⟨sM, by rw [hEq]; exact kM.2.2⟩
      · contradiction
  · contradiction

end SeLe4n.Kernel
