-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ReschedulePendingArms.Cancellation

/-!
# The resume, suspend and retype arms cover

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md`, PR B2.  Resume rewrites the
resumed thread's boost and ends that write in the key hook before it enqueues;
suspend cancels the thread's IPC and donation (each key write hooked) before it
deschedules; retype's destroy path runs the same cancellations.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-! ### Resume -/

/-- The pre-state form of the hook is the key hook on the thread's pre-state key. -/
theorem markKeyChangeFrom_eq_of_getTcb {pre st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} (h : pre.getTcb? tid = some tcb) :
    markKeyChangeFrom pre st tid = markKeyChangeFor st tid (resolveEffectivePrioDeadline pre tcb) := by
  unfold markKeyChangeFrom; rw [h]

/-- Resume's mid state writes only the resumed thread's TCB. -/
theorem resumeReadyMidState_keyInputsEqExcept (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hT : (st.getTcb? tid).isSome) :
    keyInputsEqExcept tid st (Lifecycle.Suspend.resumeReadyMidState st tid) := by
  unfold Lifecycle.Suspend.resumeReadyMidState Lifecycle.Suspend.restoreToReady
    Lifecycle.Suspend.restoreToReadyStaging
  have h1 := keyInputsEqExcept_updateTcb (f := fun tcb' => tcb'.restoredToReady) hInv hT
  refine h1.trans (keyInputsEqExcept_updateTcb
    (SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv) ?_)
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hT
  rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv, ht]; rfl

/-- **Resume covers.**  The boost write ends in the key hook, the enqueue flags
the core it inserts on, and the inline reschedule is a scheduling point. -/
theorem resumeThreadOnCore_stepCovers (st st' : SystemState) (vtid : SeLe4n.ValidThreadId)
    (e : CoreId) (sgi : Option (CoreId × SgiKind)) (hInv : st.objects.invExt)
    (hStep : Lifecycle.Suspend.resumeThreadOnCore st vtid e = .ok (st', sgi)) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold Lifecycle.Suspend.resumeThreadOnCore at hStep
  dsimp only [] at hStep
  split at hStep
  · rename_i tcb hT
    split at hStep
    · contradiction
    have hMidInv := PriorityInheritance.resumeReadyMidState_objects_invExt st vtid.val hInv
    have h1 : stepCovers e st (markKeyChangeFrom st
        (Lifecycle.Suspend.resumeReadyMidState st vtid.val) vtid.val) := by
      rw [markKeyChangeFrom_eq_of_getTcb hT]
      have hS := PriorityInheritance.resumeReadyMidState_scheduler_eq st vtid.val
      exact stepCovers_markKeyChangeFor hT
        (resumeReadyMidState_keyInputsEqExcept st vtid.val hInv (by rw [hT]; rfl))
        (fun c _ => Or.inr ⟨fun t ht => by rwa [hS] at ht, by rw [hS]⟩)
        (fun c _ hF => by rw [hS]; exact hF)
    have h1Inv : (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val)
        vtid.val).objects.invExt := by rw [markKeyChangeFrom_objects]; exact hMidInv
    have h2 := stepCovers_trans h1
      ⟨enqueueRunnableOnCore_covers e (determineTargetCore st vtid.val) _ vtid.val h1Inv,
       enqueueRunnableOnCore_monotone e (determineTargetCore st vtid.val) _ vtid.val⟩
    have h2Inv := enqueueRunnableOnCore_preserves_objects_invExt _
      (determineTargetCore st vtid.val) vtid.val h1Inv
    split at hStep
    · split at hStep
      · rename_i st4 hH
        cases hStep
        exact ⟨stepCovers_trans h2 (handleRescheduleSgiOnCore_stepCovers e _ _ h2Inv hH),
          handleRescheduleSgiOnCore_preserves_objects_invExt _ e _ h2Inv hH⟩
      · contradiction
    · cases hStep
      exact ⟨h2, h2Inv⟩
  · contradiction

/-- Retiring a pending fault on resume rewrites registers and the fault slot
of one TCB, no key field. -/
theorem retirePendingFaultForResume_keyFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    capabilityKeyFrame st (retirePendingFaultForResume st tid) := by
  unfold retirePendingFaultForResume
  split
  · split
    · unfold applyFaultRestart
      exact ⟨keyInputsEq_updateTcb hInv (fun _ => rfl), SystemState.updateTcb_scheduler _ _ _,
        SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv⟩
    · exact ⟨keyInputsEq_refl st, rfl, hInv⟩
  · exact ⟨keyInputsEq_refl st, rfl, hInv⟩

/-! ### Priority-inheritance propagation -/

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
      { tcb with pipBoost := PriorityInheritance.computeMaxWaiterPriority st tid }
    have hK : keyInputsEqExcept tid st (st.rewriteObject tid.toObjId _ hAdm) := by
      have := keyInputsEqExcept_updateTcb (f := fun t => { t with
        pipBoost := PriorityInheritance.computeMaxWaiterPriority st tid }) hInv (by rw [hT]; rfl)
      unfold SystemState.updateTcb at this
      rw [SystemState.getTcbWitnessed?_eq_some hT] at this
      exact this
    split
    · split
      · rename_i hMem _
        refine stepCovers_markKeyChangeFor hT hK (fun c' _ => Or.inr ⟨fun t ht => ?_, ?_⟩)
          (fun c' _ hF => ?_)
        · exact mem_runQueue_reKey (s := st.scheduler) hMem ht
        · exact SchedulerState.setRunQueueOnCore_currentOnCore _ _ _ _
        · rw [SchedulerState.setRunQueueOnCore_reschedulePendingOnCore]; exact hF
      · exact stepCovers_markKeyChangeFor hT hK (fun c' _ => Or.inr ⟨fun t ht => ht, rfl⟩)
          (fun c' _ hF => hF)
    · exact stepCovers_markKeyChangeFor hT hK (fun c' _ => Or.inr ⟨fun t ht => ht, rfl⟩)
        (fun c' _ hF => hF)
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

/-! ### Suspend -/

/-- Taking a thread off the core the state places it on covers: a queue removal
stales nothing, and clearing a current slot raises that core's flag. -/
theorem descheduleAt_stepCovers (e : CoreId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (placed : Option CoreId) : stepCovers e st (descheduleAt st tid placed) := by
  unfold descheduleAt
  cases placed with
  | none => exact stepCovers_refl e st
  | some c => exact ⟨removeRunnableOnCore_covers e st tid c, removeRunnableOnCore_monotone e st tid c⟩

theorem descheduleAt_objects (st : SystemState) (tid : SeLe4n.ThreadId) (placed : Option CoreId) :
    (descheduleAt st tid placed).objects = st.objects := by
  unfold descheduleAt; cases placed <;> rfl

/-- The reclaim-complete teardown covers: the teardown, the replenishment
migration, and the unbound holder's deschedule. -/
theorem cancelIpcBlockingReclaimed_stepCovers (e : CoreId) (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt) :
    stepCovers e st (cancelIpcBlockingReclaimed victim tcb st) := by
  have hTorn := cancelIpcBlocking_stepCovers e st victim tcb hInv
  have hMig : stepCovers e st (cancelIpcBlockingMigrated victim tcb st) := by
    unfold cancelIpcBlockingMigrated
    split
    · exact stepCovers_trans hTorn (migrateSchedContextReplenishment_stepCovers e _ _ _ _)
    · exact hTorn
  unfold cancelIpcBlockingReclaimed descheduleUnboundHolder
  split
  · exact hMig
  · exact stepCovers_trans hMig (descheduleAt_stepCovers e _ _ _)

/-- Clearing the pending state touches no key field. -/
theorem clearPendingState_keyInputsEq (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    keyInputsEq st (Lifecycle.Suspend.clearPendingState st tid) := by
  unfold Lifecycle.Suspend.clearPendingState
  exact keyInputsEq_updateTcb hInv (fun _ => rfl)

/-- The suspend's reschedule is the executing core's scheduling point or
nothing. -/
theorem suspendRescheduleOnCore_stepCovers (e : CoreId) {st st' : SystemState}
    {runningCore : CoreId} {wc ld : Bool} {sgi : Option (CoreId × SgiKind)}
    (hInv : st.objects.invExt)
    (h : Lifecycle.Suspend.suspendRescheduleOnCore st runningCore e wc ld = .ok (st', sgi)) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold Lifecycle.Suspend.suspendRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨stepCovers_refl e _, hInv⟩)
    | (rename_i st4 hH
       cases h
       exact ⟨handleRescheduleSgiOnCore_stepCovers e _ _ hInv hH,
         handleRescheduleSgiOnCore_preserves_objects_invExt _ e _ hInv hH⟩)

/-- **Suspend covers.**  The IPC teardown, the PIP revert, the donation
cancellation (each key write hooked), the deschedule (a cleared current slot
flags its core), two key-free TCB writes and the executing core's own
scheduling point. -/
theorem suspendThreadOnCore_stepCovers (st st' : SystemState) (vtid : SeLe4n.ValidThreadId)
    (e : CoreId) (sgi : Option (CoreId × SgiKind)) (hInv : st.objects.invExt)
    (hStep : Lifecycle.Suspend.suspendThreadOnCore st vtid e = .ok (st', sgi)) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold Lifecycle.Suspend.suspendThreadOnCore at hStep
  dsimp only [] at hStep
  split at hStep
  · rename_i tcb hT
    split at hStep
    · contradiction
    have h1 := cancelIpcBlockingReclaimed_stepCovers e st vtid.val tcb hInv
    have h1Inv : (cancelIpcBlockingReclaimed vtid.val tcb st).objects.invExt := by
      rw [cancelIpcBlockingReclaimed_objects]
      exact Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st vtid.val tcb hInv
    cases hB : PriorityInheritance.blockingServer st vtid.val
    case' none =>
      rw [hB] at hStep
      dsimp only at hStep
      generalize cancelIpcBlockingReclaimed vtid.val tcb st = s2 at hStep h1 h1Inv
    case' some srv =>
      rw [hB] at hStep
      dsimp only at hStep
      have hc := propagatePipChainCrossCore_stepCovers e e
        (cancelIpcBlockingReclaimed vtid.val tcb st).objectIndex.length _ srv h1Inv
      replace h1 := stepCovers_trans h1 hc.1
      replace h1Inv := hc.2
      clear hc
      generalize (PriorityInheritance.propagatePipChainCrossCore
        (cancelIpcBlockingReclaimed vtid.val tcb st) srv e).1 = s2 at hStep h1 h1Inv
    all_goals
      split at hStep
      · contradiction
      rename_i s3 hDon
      obtain ⟨h3, h3Inv⟩ : stepCovers e st s3 ∧ s3.objects.invExt := by
        split at hDon
        · cases hDon; exact ⟨h1, h1Inv⟩
        · obtain ⟨a, b⟩ := cancelBoundDonationOnCore_stepCovers e h1Inv hDon
          exact ⟨stepCovers_trans h1 a, b⟩
        · obtain ⟨a, b⟩ := cancelDonatedDonationOnCore_stepCovers e h1Inv hDon
          exact ⟨stepCovers_trans h1 a, b⟩
      have h4 := stepCovers_trans h3 (descheduleAt_stepCovers e s3 vtid.val (placedCoreOf? st vtid.val))
      have h4Inv : (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)).objects.invExt := by
        rw [descheduleAt_objects]; exact h3Inv
      have h5 := stepCovers_trans h4 (stepCovers_of_keys_sched
        (clearPendingState_keyInputsEq _ vtid.val h4Inv) (SystemState.updateTcb_scheduler _ _ _))
      have h5Inv : (Lifecycle.Suspend.clearPendingStateValid
          (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)) vtid).objects.invExt := by
        unfold Lifecycle.Suspend.clearPendingStateValid Lifecycle.Suspend.clearPendingState
        exact SystemState.updateTcb_preserves_objects_invExt _ _ _ h4Inv
      have h6 := stepCovers_trans h5 (stepCovers_of_keys_sched
        (keyInputsEq_updateTcb h5Inv (tid := vtid.val)
          (f := fun t => { t with threadState := .Inactive }) (fun _ => rfl))
        (SystemState.updateTcb_scheduler _ _ _))
      have h6Inv := SystemState.updateTcb_preserves_objects_invExt _ vtid.val
        (fun t => { t with threadState := .Inactive }) h5Inv
      obtain ⟨h7, h7Inv⟩ := suspendRescheduleOnCore_stepCovers e h6Inv hStep
      exact ⟨stepCovers_trans h6 h7, h7Inv⟩
  · contradiction

end SeLe4n.Kernel
