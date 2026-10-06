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

/-- A scheduling-context update that keeps the deadline moves no key input. -/
theorem keyInputsEq_updateSchedContext {st : SystemState} {scId : SeLe4n.SchedContextId}
    {f : SchedContext → SchedContext} (hInv : st.objects.invExt)
    (hF : ∀ sc, (f sc).deadline = sc.deadline) :
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
    simp only [keyInputsOf, hF]

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
  have hMidObj : mid.objects = (SchedContext.PriorityManagement.updatePrioritySource
      st tid tcb p).objects := by rw [← hMid]; exact migrateRunQueueBucketOnCore_objects_eq _ _ _ _
  have hMidSched : ∀ c, (∀ x, x ∈ mid.scheduler.runQueueOnCore c ↔
        x ∈ st.scheduler.runQueueOnCore c) ∧
      mid.scheduler.currentOnCore c = st.scheduler.currentOnCore c ∧
      mid.scheduler.reschedulePendingOnCore c = st.scheduler.reschedulePendingOnCore c := by
    intro c
    subst hMid
    refine ⟨fun x => (migrateRunQueueBucketOnCore_mem_runQueueOnCore _ _ _ _ _ x).trans
      (by rw [hU]), ?_, ?_⟩
    · rw [migrateRunQueueBucketOnCore_currentOnCore, hU]
    · unfold SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
      split
      · simp [SchedulerState.reschedulePendingOnCore, SchedulerState.setRunQueueOnCore, hU]
      · rw [hU]
  have hKeysMid : keyInputsEqExcept tid st mid :=
    hKeys.trans_keyInputsEq (keyInputsEq_of_objects_eq hMidObj)
  have h1 := stepCovers_markKeyChangeFor (e := e) hT hKeysMid
    (fun c _ => Or.inr ⟨fun x hx => ((hMidSched c).1 x).mp hx, (hMidSched c).2.1⟩)
    (fun c _ hp => by rw [(hMidSched c).2.2]; exact hp)
  have hInvMk : (markKeyChangeFor mid tid (resolveEffectivePrioDeadline st tcb)).objects.invExt := by
    rw [markKeyChangeFor_objects, hMidObj]; exact hInvU
  have h2 := priorityRescheduleOnCore_stepCovers e _ st' _ _ _ hInvMk hStep
  refine ⟨stepCovers_trans h1 h2, ?_⟩
  rcases SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases
      _ st' _ e _ _ hStep with hEq | hH
  · rw [hEq]; exact hInvMk
  · exact handleRescheduleSgiOnCore_preserves_objects_invExt _ e st' hInvMk hH

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

/-! ### Affinity -/

/-- A step that moves no key input covers when every remote core is flagged or
kept its slots (a queue may only shrink), and no remote flag dropped. -/
theorem stepCovers_of_keys_slots {e : CoreId} {pre post : SystemState}
    (hKeys : keyInputsEq pre post)
    (hSlots : ∀ c, c ≠ e → post.scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, t ∈ post.scheduler.runQueueOnCore c → t ∈ pre.scheduler.runQueueOnCore c) ∧
        post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c))
    (hMono : reschedulePendingMonotone e pre post) : stepCovers e pre post :=
  ⟨reschedulePendingCovers_of_frame (schedKeyView_eq_of_keyInputsEq hKeys) hSlots, hMono⟩

theorem migrateSchedContextReplenishment_stepCovers (e : CoreId) (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) :
    stepCovers e st (migrateSchedContextReplenishment st scId fromCore toCore) := by
  apply stepCovers_of_keys_slots
    (keyInputsEq_of_objects_eq (migrateSchedContextReplenishment_objects _ _ _ _))
  · intro c _
    obtain ⟨hR, hC⟩ := migrateSchedContextReplenishment_runQueue_current_eq st scId fromCore toCore c
    exact Or.inr ⟨fun t ht => by rw [hR] at ht; exact ht, hC⟩
  · intro c _ hp
    unfold migrateSchedContextReplenishment
    split
    · exact hp
    · simpa using hp

theorem migrateRunQueueOnAffinityChange_stepCovers (e : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) :
    stepCovers e st (migrateRunQueueOnAffinityChange st tid fromCore toCore) := by
  apply stepCovers_of_keys_slots
    (keyInputsEq_of_objects_eq (migrateRunQueueOnAffinityChange_objects_eq _ _ _ _))
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
            refine ⟨fun t ht => ?_, rfl⟩
            simp only [SchedulerState.markReschedulePendingOnCore_runQueueOnCore] at ht
            rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hTo)] at ht
            by_cases hFr : c = fromCore
            · subst hFr
              rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self, RunQueue.mem_remove] at ht
              exact ht.1
            · rwa [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hFr)] at ht
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

theorem setThreadCpuAffinityOnCore_stepCovers (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (affinity : Option CoreId) (e : CoreId)
    (sgi : Option (CoreId × SgiKind)) (hInv : st.objects.invExt)
    (hStep : setThreadCpuAffinityOnCore st vtid affinity e = .ok (st', sgi)) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold setThreadCpuAffinityOnCore setThreadCpuAffinityWithMigration at hStep
  split at hStep
  · rename_i tcb hT
    split at hStep
    · contradiction
    · split at hStep
      · contradiction
      · split at hStep
        · rename_i stSet hSet
          have hSetEq : stSet = { st with objects := (st.objects.insert vtid.val.toObjId
              (.tcb { tcb with cpuAffinity := affinity })) } := by
            unfold setThreadCpuAffinity at hSet
            rw [SystemState.getTcbWitnessed?_eq_some hT] at hSet
            exact (Except.ok.inj hSet).symm
          subst hSetEq
          dsimp only [] at hStep
          cases hStep
          have kSet := insertObjects_tcbKeyKeeping_keyFrame (tcb' := { tcb with
            cpuAffinity := affinity }) hInv ((SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hT) rfl
          have s1 := kSet.stepCovers (e := e)
          cases tcb.schedContextBinding.scId? with
          | some scId =>
            refine ⟨stepCovers_trans s1 (stepCovers_trans
              (migrateSchedContextReplenishment_stepCovers e _ scId _ _)
              (migrateRunQueueOnAffinityChange_stepCovers e _ _ _ _)), ?_⟩
            rw [migrateRunQueueOnAffinityChange_objects_eq, migrateSchedContextReplenishment_objects]
            exact kSet.2.2
          | none =>
            exact ⟨stepCovers_trans s1 (migrateRunQueueOnAffinityChange_stepCovers e _ _ _ _),
              by rw [migrateRunQueueOnAffinityChange_objects_eq]; exact kSet.2.2⟩
        · contradiction
  · contradiction

/-! ### Scheduling-context configure -/

/-- The effective key reads the TCB's key fields and the deadline of the one
context its binding names. -/
theorem resolveEffectivePrioDeadline_congr_binding {st st' : SystemState} {a b : TCB}
    (hK : tcbKeyFields b = tcbKeyFields a)
    (hSc : ∀ sc, a.schedContextBinding.scId? = some sc →
      (st'.getSchedContext? sc).map (·.deadline) = (st.getSchedContext? sc).map (·.deadline)) :
    resolveEffectivePrioDeadline st' b = resolveEffectivePrioDeadline st a := by
  simp only [tcbKeyFields, Prod.mk.injEq] at hK
  obtain ⟨hP, hD, hB, hPip⟩ := hK
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
      rw [resolveEffectivePrioDeadline_congr_binding hT (fun sc hsc => ?_)]
      have hNe : sc ≠ S := fun h => hNo a hp (h ▸ hsc)
      have hNeO : sc.toObjId ≠ S.toObjId := fun h => hNe (SeLe4n.SchedContextId.toObjId_injective _ _ h)
      exact getSchedContext?_deadline_of_keyInputsOf (hFrame _ hNeO)

/-- What a key write on `tid` keeps: no key input but `tid`'s TCB moves, no run
queue gains a member, and no current slot or flag moves. -/
def keyWriteSlotFrame (tid : SeLe4n.ThreadId) (pre post : SystemState) : Prop :=
  keyInputsEqExcept tid pre post ∧
  (∀ c t, t ∈ post.scheduler.runQueueOnCore c → t ∈ pre.scheduler.runQueueOnCore c) ∧
  (∀ c, post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c) ∧
  (∀ c, post.scheduler.reschedulePendingOnCore c = pre.scheduler.reschedulePendingOnCore c) ∧
  post.objects.invExt

theorem keyWriteSlotFrame_refl {tid : SeLe4n.ThreadId} {st : SystemState} {t : TCB}
    (hT : st.objects[tid.toObjId]? = some (.tcb t)) (hInv : st.objects.invExt) :
    keyWriteSlotFrame tid st st :=
  ⟨⟨fun _ _ => rfl, ⟨fun sc h => (by rw [hT] at h; cases h), fun sc h => (by rw [hT] at h; cases h)⟩⟩,
   fun _ _ h => h, fun _ => rfl, fun _ => rfl, hInv⟩

/-- A TCB stored over `tid`'s TCB keeps the frame. -/
theorem keyWriteSlotFrame_insertTcb {tid : SeLe4n.ThreadId} {pre s : SystemState} {t' : TCB}
    (h : keyWriteSlotFrame tid pre s) :
    keyWriteSlotFrame tid pre { s with objects := s.objects.insert tid.toObjId (.tcb t') } := by
  obtain ⟨hK, hRq, hCur, hFl, hInv⟩ := h
  refine ⟨⟨fun oid hne => ?_, ⟨hK.2.1, fun sc hs => ?_⟩⟩, hRq, hCur, hFl,
    RobinHood.RHTable.insert_preserves_invExt _ _ _ hInv⟩
  · rw [insertObjects_getElem_ne s _ _ oid hne hInv]; exact hK.1 oid hne
  · rw [insertObjects_getElem_self s _ _ hInv] at hs; cases hs

/-- Re-keying a queued `tid` in place keeps the frame. -/
theorem keyWriteSlotFrame_reKey {tid : SeLe4n.ThreadId} {pre s : SystemState}
    (h : keyWriteSlotFrame tid pre s) (c : CoreId) (p : SeLe4n.Priority)
    (hMem : tid ∈ s.scheduler.runQueueOnCore c) :
    keyWriteSlotFrame tid pre { s with scheduler := (s.scheduler.setRunQueueOnCore c
      (((s.scheduler.runQueueOnCore c).remove tid).insert tid p)) } := by
  obtain ⟨hK, hRq, hCur, hFl, hInv⟩ := h
  refine ⟨hK, fun c' t ht => hRq c' t ?_, fun c' => ?_, fun c' => ?_, hInv⟩
  · by_cases hcc : c = c'
    · subst hcc
      rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self, RunQueue.mem_insert,
        RunQueue.mem_remove] at ht
      rcases ht with ⟨ht, _⟩ | rfl
      · exact ht
      · exact hMem
    · rwa [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ c c' _ hcc] at ht
  · rw [SchedulerState.setRunQueueOnCore_currentOnCore]; exact hCur c'
  · rw [SchedulerState.setRunQueueOnCore_reschedulePendingOnCore]; exact hFl c'

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
        · rename_i hMem; exact keyWriteSlotFrame_reKey (keyWriteSlotFrame_insertTcb h0) _ _ hMem
        · exact keyWriteSlotFrame_insertTcb h0
    · apply keyWriteSlotFrame_insertTcb
      split
      · exact h0
      · split
        · rename_i hMem; exact keyWriteSlotFrame_reKey (keyWriteSlotFrame_insertTcb h0) _ _ hMem
        · exact keyWriteSlotFrame_insertTcb h0
  · split
    · exact h0
    · split
      · rename_i hMem; exact keyWriteSlotFrame_reKey (keyWriteSlotFrame_insertTcb h0) _ _ hMem
      · exact keyWriteSlotFrame_insertTcb h0

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
          have hInvCl : (SchedContextOps.purgeReplenishmentOnCore st
              (SchedContextOps.schedContextReplenishHome st sc) ⟨vScId.val.toNat⟩).objects.invExt := by
            rw [SchedContextOps.purgeReplenishmentOnCore_objects]; exact hObjInv
          have hInvSt := storeObject_preserves_objects_invExt _ stStored _ _ hInvCl hStore
          have hSchedSt := storeObject_scheduler_eq _ stStored _ _ hStore
          have hAtS := storeObject_objects_eq _ stStored _ _ hInvCl hStore
          have hNeS : ∀ oid, oid ≠ vScId.val → stStored.objects[oid]? = st.objects[oid]? := by
            intro oid h
            rw [storeObject_objects_ne _ stStored vScId.val oid _ h hInvCl hStore,
              SchedContextOps.purgeReplenishmentOnCore_objects]
          have hRqSt : ∀ c, stStored.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c := by
            intro c; rw [hSchedSt]; exact SchedContextOps.purgeReplenishmentOnCore_runQueueOnCore _ _ _ c
          have hCurSt : ∀ c, stStored.scheduler.currentOnCore c = st.scheduler.currentOnCore c := by
            intro c; rw [hSchedSt]; exact SchedContextOps.purgeReplenishmentOnCore_currentOnCore _ _ _ c
          have hFlSt : ∀ c, stStored.scheduler.reschedulePendingOnCore c =
              st.scheduler.reschedulePendingOnCore c := by
            intro c; rw [hSchedSt]
            simp [SchedContextOps.purgeReplenishmentOnCore]
          have hGetSt : ∀ t, stStored.getTcb? t = st.getTcb? t := by
            intro t
            unfold SystemState.getTcb?
            by_cases h : t.toObjId = vScId.val
            · rw [h, hAtS]; rw [show vScId.val = (SchedContextId.ofObjId vScId.val).toObjId from rfl,
                hScRaw]
            · rw [hNeS _ h]
          have hKeySt : ∀ t, (∀ tcb, st.getTcb? t = some tcb →
              tcb.schedContextBinding.scId? ≠ some (SchedContextId.ofObjId vScId.val)) →
              schedKeyView stStored t = schedKeyView st t :=
            fun t hNo => schedKeyView_eq_of_scSlotWrite (fun oid h => by rw [hNeS oid h])
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
            ⟨reschedulePendingCovers_of_frame (fun t => hKeySt t (hNo t))
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
              refine ⟨⟨markKeyChangeFor_covers hPre (fun t ht => ?_) (fun c _ => Or.inr ⟨fun t ht => ?_, ?_⟩),
                fun c _ h => markKeyChangeFor_reschedulePendingOnCore_mono _ _ _ _ ?_⟩, ?_⟩
              · rw [schedKeyView_eq_of_keyInputsEqExcept hFr.1 ht]
                refine hKeySt t fun tcb hT hB => ht ?_
                have := hReader t tcb hT hB; rw [hBT] at this; exact (Option.some.inj this).symm
              · have := hFr.2.1 c t ht; rwa [hRqSt] at this
              · rw [hFr.2.2.1, hCurSt]
              · rw [hFr.2.2.2.1, hFlSt]; exact h
              · rw [markKeyChangeFor_objects]; exact hFr.2.2.2.2
            · rename_i hNone
              cases hStep
              refine ⟨hNoReader fun t tcb hT hB => ?_, hInvSt⟩
              have := hReader t tcb hT hB; rw [hBT] at this; cases this
              rw [← hGetSt] at hT
              exact absurd (SystemState.getTcbWitnessed?_eq_some hT) (by rw [hNone]; simp)
      · contradiction
    · contradiction

/-! ### Scheduling-context bind and unbind -/

/-- A run-queue re-key of a queued thread adds no member. -/
theorem mem_runQueue_reKey {s : SchedulerState} {h c : CoreId} {x t : SeLe4n.ThreadId}
    {p : SeLe4n.Priority} (hMem : x ∈ s.runQueueOnCore h)
    (ht : t ∈ (s.setRunQueueOnCore h (((s.runQueueOnCore h).remove x).insert x p)).runQueueOnCore c) :
    t ∈ s.runQueueOnCore c := by
  by_cases hc : h = c
  · subst hc
    rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self, RunQueue.mem_insert,
      RunQueue.mem_remove] at ht
    rcases ht with ⟨ht, _⟩ | rfl
    · exact ht
    · exact hMem
  · rwa [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ h c _ hc] at ht

/-- Writing one core's run queue leaves every other core's. -/
theorem mem_runQueue_set_ne {s : SchedulerState} {h c : CoreId} {t : SeLe4n.ThreadId}
    {q : RunQueue} (hc : h ≠ c) (ht : t ∈ (s.setRunQueueOnCore h q).runQueueOnCore c) :
    t ∈ s.runQueueOnCore c := by
  rwa [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ h c _ hc] at ht

theorem keyInputsEqExcept_of_objects_eq {tid : SeLe4n.ThreadId} {a b c : SystemState}
    (h : keyInputsEqExcept tid a b) (hc : c.objects = b.objects) : keyInputsEqExcept tid a c := by
  unfold keyInputsEqExcept; rw [hc]; exact h

/-- Inserting into one core's queue and flagging that core keeps every core
flagged or slot-unchanged. -/
theorem insertMark_slots (s : SchedulerState) (h c : CoreId) (q : RunQueue) :
    ((s.setRunQueueOnCore h q).markReschedulePendingOnCore h).reschedulePendingOnCore c = true ∨
      ((∀ t, t ∈ ((s.setRunQueueOnCore h q).markReschedulePendingOnCore h).runQueueOnCore c →
          t ∈ s.runQueueOnCore c) ∧
        ((s.setRunQueueOnCore h q).markReschedulePendingOnCore h).currentOnCore c = s.currentOnCore c) := by
  by_cases hh : h = c
  · subst hh; exact Or.inl (SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_self _ _)
  · refine Or.inr ⟨fun t ht => ?_, ?_⟩
    · rw [SchedulerState.markReschedulePendingOnCore_runQueueOnCore] at ht
      exact mem_runQueue_set_ne hh ht
    · rw [SchedulerState.markReschedulePendingOnCore_currentOnCore,
        SchedulerState.setRunQueueOnCore_currentOnCore]

theorem insertMark_flag_mono (s : SchedulerState) (h c : CoreId) (q : RunQueue)
    (hF : s.reschedulePendingOnCore c = true) :
    ((s.setRunQueueOnCore h q).markReschedulePendingOnCore h).reschedulePendingOnCore c = true := by
  by_cases hh : h = c
  · subst hh; exact SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_self _ _
  · rw [SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_ne _ _ _ hh,
      SchedulerState.setRunQueueOnCore_reschedulePendingOnCore]; exact hF

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
            { sc with boundThread := some vTid.val, donationOrigin := none }) :=
          SystemState.rewriteAdmissible_schedContext hSc _
        have hInv1 := SystemState.rewriteObject_preserves_objects_invExt st _ _ hAdm hObjInv
        have hK1 : keyInputsEq st (st.rewriteObject vScId.val _ hAdm) :=
          keyInputsEq_rewriteObject hAdm hObjInv (by rw [hScRaw]; rfl)
        have hT1 : (st.rewriteObject vScId.val _ hAdm).getTcb? vTid.val = some tcb :=
          (SystemState.rewriteObject_schedContext_getTcb? st _ _ hAdm hObjInv _).trans hT
        have hK2 := keyInputsEq.trans_keyInputsEqExcept hK1
          (keyInputsEqExcept_updateTcb (f := fun t => { t with
            schedContextBinding := (SchedContextBinding.bound ⟨vScId.val.toNat⟩),
            priority := sc.priority }) hInv1 (by rw [hT1]; rfl))
        have hInv2 := SystemState.updateTcb_preserves_objects_invExt _ vTid.val
          (fun t => { t with
            schedContextBinding := (SchedContextBinding.bound ⟨vScId.val.toNat⟩),
            priority := sc.priority }) hInv1
        refine ⟨stepCovers_markKeyChangeFor hT (keyInputsEqExcept_of_objects_eq hK2 ?_) ?_ ?_, ?_⟩
        · dsimp only []; split
          · rfl
          · split <;> rfl
        · intro c hc
          dsimp only []
          split
          · rename_i hMem
            simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler] at hMem ⊢
            exact Or.inr ⟨fun t ht => mem_runQueue_reKey hMem ht,
              SchedulerState.setRunQueueOnCore_currentOnCore _ _ _ _⟩
          · split
            · simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
              exact insertMark_slots _ _ _ _
            · simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
              exact Or.inr ⟨fun t ht => ht, trivial⟩
        · intro c _ hF
          dsimp only []
          split
          · simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler,
              SchedulerState.setRunQueueOnCore_reschedulePendingOnCore]; exact hF
          · split
            · simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
              exact insertMark_flag_mono _ _ _ _ hF
            · simp only [SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]; exact hF
        · rw [markKeyChangeFor_objects]
          dsimp only []
          split
          · exact hInv2
          · split <;> exact hInv2
      · contradiction
    · contradiction
  · contradiction

/-- Scheduler-record coverage: every core is flagged afterwards, or no queue
gained a member and its current slot is unchanged. -/
def schedSlotsCovered (s0 s1 : SchedulerState) : Prop :=
  ∀ c, s1.reschedulePendingOnCore c = true ∨
    ((∀ t, t ∈ s1.runQueueOnCore c → t ∈ s0.runQueueOnCore c) ∧ s1.currentOnCore c = s0.currentOnCore c)

/-- No flag drops. -/
def schedFlagsMono (s0 s1 : SchedulerState) : Prop :=
  ∀ c, s0.reschedulePendingOnCore c = true → s1.reschedulePendingOnCore c = true

theorem schedSlotsCovered_trans {a b d : SchedulerState} (h₁ : schedSlotsCovered a b)
    (h₂ : schedSlotsCovered b d) (hM : schedFlagsMono b d) : schedSlotsCovered a d := by
  intro c
  rcases h₂ c with h | ⟨hRq₂, hCur₂⟩
  · exact Or.inl h
  rcases h₁ c with h | ⟨hRq₁, hCur₁⟩
  · exact Or.inl (hM c h)
  · exact Or.inr ⟨fun t ht => hRq₁ t (hRq₂ t ht), hCur₂.trans hCur₁⟩

theorem schedFlagsMono_trans {a b d : SchedulerState} (h₁ : schedFlagsMono a b)
    (h₂ : schedFlagsMono b d) : schedFlagsMono a d := fun c h => h₂ c (h₁ c h)

theorem schedSlotsCovered_refl (s : SchedulerState) : schedSlotsCovered s s :=
  fun _ => Or.inr ⟨fun _ h => h, rfl⟩

theorem schedFlagsMono_refl (s : SchedulerState) : schedFlagsMono s s := fun _ h => h

theorem schedSlotsCovered_reKey (s : SchedulerState) (h : CoreId) (x : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hMem : x ∈ s.runQueueOnCore h) :
    schedSlotsCovered s (s.setRunQueueOnCore h (((s.runQueueOnCore h).remove x).insert x p)) ∧
      schedFlagsMono s (s.setRunQueueOnCore h (((s.runQueueOnCore h).remove x).insert x p)) :=
  ⟨fun _ => Or.inr ⟨fun _ ht => mem_runQueue_reKey hMem ht,
    SchedulerState.setRunQueueOnCore_currentOnCore _ _ _ _⟩,
   fun c hF => by rw [SchedulerState.setRunQueueOnCore_reschedulePendingOnCore]; exact hF⟩

theorem schedSlotsCovered_insertMark (s : SchedulerState) (h : CoreId) (q : RunQueue) :
    schedSlotsCovered s ((s.setRunQueueOnCore h q).markReschedulePendingOnCore h) ∧
      schedFlagsMono s ((s.setRunQueueOnCore h q).markReschedulePendingOnCore h) :=
  ⟨fun c => insertMark_slots s h c q, fun c hF => insertMark_flag_mono s h c q hF⟩

theorem schedSlotsCovered_clearMark (s : SchedulerState) (r : CoreId) (v : Option SeLe4n.ThreadId) :
    schedSlotsCovered s ((s.setCurrentOnCore r v).markReschedulePendingOnCore r) ∧
      schedFlagsMono s ((s.setCurrentOnCore r v).markReschedulePendingOnCore r) := by
  refine ⟨fun c => ?_, fun c hF => ?_⟩
  · by_cases hh : r = c
    · subst hh; exact Or.inl (SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_self _ _)
    · refine Or.inr ⟨fun t ht => ?_, ?_⟩
      · rwa [SchedulerState.markReschedulePendingOnCore_runQueueOnCore,
          SchedulerState.setCurrentOnCore_runQueueOnCore] at ht
      · rw [SchedulerState.markReschedulePendingOnCore_currentOnCore,
          SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hh]
  · by_cases hh : r = c
    · subst hh; exact SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_self _ _
    · rw [SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_ne _ _ _ hh,
        SchedulerState.setCurrentOnCore_reschedulePendingOnCore]; exact hF

/-- A scheduler-record step covered on every core covers. -/
theorem stepCovers_of_schedSlots {e : CoreId} (st : SystemState) (s : SchedulerState)
    (hC : schedSlotsCovered st.scheduler s) (hM : schedFlagsMono st.scheduler s) :
    stepCovers e st { st with scheduler := s } :=
  ⟨reschedulePendingCovers_of_frame (fun _ => rfl) (fun c _ => hC c), fun c _ h => hM c h⟩

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

theorem unbindRebucket_covered (s0 : SchedulerState) (home : CoreId) (tid : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (wasCurrent : Bool) :
    schedSlotsCovered s0 (if tid ∈ s0.runQueueOnCore home then
        s0.setRunQueueOnCore home (((s0.runQueueOnCore home).remove tid).insert tid p)
      else if wasCurrent then
        (s0.setRunQueueOnCore home (((s0.runQueueOnCore home).remove tid).insert tid p))
          |>.markReschedulePendingOnCore home
      else s0) ∧
    schedFlagsMono s0 (if tid ∈ s0.runQueueOnCore home then
        s0.setRunQueueOnCore home (((s0.runQueueOnCore home).remove tid).insert tid p)
      else if wasCurrent then
        (s0.setRunQueueOnCore home (((s0.runQueueOnCore home).remove tid).insert tid p))
          |>.markReschedulePendingOnCore home
      else s0) := by
  split
  · rename_i hMem; exact schedSlotsCovered_reKey s0 home tid p hMem
  · split
    · exact schedSlotsCovered_insertMark s0 home _
    · exact ⟨schedSlotsCovered_refl s0, schedFlagsMono_refl s0⟩

/-- Unbind's object tail — the context write keeps its deadline, the binding
write is the bound thread's key write, the purge is a replenish-queue write —
ends in the key hook. -/
theorem unbindTail_stepCovers (e : CoreId) (st1 : SystemState) (vScId : SeLe4n.ValidObjId)
    (sc : SchedContext) (tid : SeLe4n.ThreadId) (tcb : TCB) (home : CoreId)
    (hInv : st1.objects.invExt)
    (hSc : st1.objects[vScId.val]? = some (.schedContext sc))
    (hT : st1.getTcb? tid = some tcb)
    (hAdm : st1.rewriteAdmissible vScId.val (.schedContext
      { sc with boundThread := none, isActive := false, donationOrigin := none })) :
    stepCovers e st1 (markKeyChangeFor
      { SchedContextOps.purgeReplenishmentOnCore
          ((st1.rewriteObject vScId.val _ hAdm).updateTcb tid fun t =>
            { t with schedContextBinding := SchedContextBinding.unbound })
          home ⟨vScId.val.toNat⟩ with
        scThreadIndex := scThreadIndexRemove
          (SchedContextOps.purgeReplenishmentOnCore
            ((st1.rewriteObject vScId.val _ hAdm).updateTcb tid fun t =>
              { t with schedContextBinding := SchedContextBinding.unbound })
            home ⟨vScId.val.toNat⟩).scThreadIndex ⟨vScId.val.toNat⟩ tid }
      tid (resolveEffectivePrioDeadline st1 tcb)) := by
  have hK1 : keyInputsEq st1 (st1.rewriteObject vScId.val _ hAdm) :=
    keyInputsEq_rewriteObject hAdm hInv (by rw [hSc]; rfl)
  have hInv1 := SystemState.rewriteObject_preserves_objects_invExt st1 _ _ hAdm hInv
  have hT1 : (st1.rewriteObject vScId.val _ hAdm).getTcb? tid = some tcb :=
    (SystemState.rewriteObject_schedContext_getTcb? st1 _ _ hAdm hInv _).trans hT
  have hK2 := keyInputsEq.trans_keyInputsEqExcept hK1
    (keyInputsEqExcept_updateTcb (f := fun t => { t with
      schedContextBinding := SchedContextBinding.unbound }) hInv1 (by rw [hT1]; rfl))
  refine stepCovers_markKeyChangeFor hT (keyInputsEqExcept_of_objects_eq hK2 ?_)
    (fun c _ => Or.inr ⟨fun t ht => ?_, ?_⟩) (fun c _ hF => ?_)
  · exact SchedContextOps.purgeReplenishmentOnCore_objects _ home ⟨vScId.val.toNat⟩
  · simp only [SchedContextOps.purgeReplenishmentOnCore_runQueueOnCore,
      SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler] at ht
    exact ht
  · simp only [SchedContextOps.purgeReplenishmentOnCore_currentOnCore,
      SystemState.updateTcb_scheduler, SystemState.rewriteObject_scheduler]
  · simp [SchedContextOps.purgeReplenishmentOnCore, SystemState.updateTcb_scheduler,
      SystemState.rewriteObject_scheduler, hF]

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
          · refine stepCovers_trans ?_ (unbindTail_stepCovers e _ vScId sc tid tcb _ ?_ ?_ ?_ _)
            · apply stepCovers_of_schedSlots
              · exact schedSlotsCovered_trans (unbindClear_covered _ _).1
                  (unbindRebucket_covered _ _ _ _ _).1 (unbindRebucket_covered _ _ _ _ _).2
              · exact schedFlagsMono_trans (unbindClear_covered _ _).2
                  (unbindRebucket_covered _ _ _ _ _).2
            · exact hObjInv
            · exact hScRaw
            · exact hT
          · rw [markKeyChangeFor_objects]
            dsimp only []
            rw [SchedContextOps.purgeReplenishmentOnCore_objects]
            refine SystemState.updateTcb_preserves_objects_invExt _ _ _
              (SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ ?_)
            exact hObjInv
      · cases hStep
        have hAdm : st.rewriteAdmissible vScId.val (.schedContext
            { sc with boundThread := none, isActive := false, donationOrigin := none }) :=
          SystemState.rewriteAdmissible_schedContext hSc _
        have hK1 : keyInputsEq st (st.rewriteObject vScId.val _ hAdm) :=
          keyInputsEq_rewriteObject hAdm hObjInv (by rw [hScRaw]; rfl)
        have hInv1 := SystemState.rewriteObject_preserves_objects_invExt st _ _ hAdm hObjInv
        refine ⟨stepCovers_of_frame (keyInputsEq_trans hK1 (keyInputsEq_of_objects_eq ?_))
          (fun c _ => ?_) (fun c _ => ?_) (fun c _ hF => ?_), ?_⟩
        · dsimp only []; rw [SchedContextOps.purgeReplenishmentFromAllCores_objects]
        · dsimp only []; rw [SchedContextOps.purgeReplenishmentFromAllCores_runQueueOnCore]; rfl
        · dsimp only []; rw [SchedContextOps.purgeReplenishmentFromAllCores_currentOnCore]; rfl
        · dsimp only []
          rw [SchedContextOps.purgeReplenishmentFromAllCores_reschedulePendingOnCore]; exact hF
        · dsimp only []
          rw [SchedContextOps.purgeReplenishmentFromAllCores_objects]; exact hInv1
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

end SeLe4n.Kernel
