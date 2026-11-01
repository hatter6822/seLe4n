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

/-- The resume's mid-state moves no thread's run-queue core. -/
theorem resumeReadyMidState_runCoresAgree (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    SystemState.RunCoresAgree (Lifecycle.Suspend.resumeReadyMidState st tid) st := by
  have hInv1 : (Lifecycle.Suspend.restoreToReady st tid).objects.invExt :=
    SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv
  have h1 : SystemState.RunCoresAgree (Lifecycle.Suspend.restoreToReady st tid) st :=
    SystemState.RunCoresAgree.updateTcb hInv (fun _ => rfl)
  have h2 : SystemState.RunCoresAgree (Lifecycle.Suspend.resumeReadyMidState st tid)
      (Lifecycle.Suspend.restoreToReady st tid) :=
    SystemState.RunCoresAgree.updateTcb hInv1 (fun _ => rfl)
  exact h2.trans h1

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
      have hS := PriorityInheritance.resumeReadyMidState_scheduler_eq st vtid.val
      have hK := resumeReadyMidState_keyInputsEqExcept st vtid.val hInv (by rw [hT]; rfl)
      exact ⟨markKeyChangeFrom_covers (fun t ht => ⟨schedKeyView_eq_of_keyInputsEqExcept hK ht,
          budgetEligibleView_eq_of_keyInputsEqExcept hK ht⟩)
        (fun c _ => Or.inr ⟨fun t ht => by
          rwa [(resumeReadyMidState_runCoresAgree st vtid.val hInv).queuedOn] at ht, by rw [hS]⟩),
        fun c _ hF => markKeyChangeFrom_reschedulePendingOnCore_mono _ _ _ _ (by rw [hS]; exact hF),
        currentKeptOffCore_of_eq fun c _ => by rw [markKeyChangeFrom_currentOnCore, hS],
        residentKeptOffCore_of_eq (by
          rw [markKeyChangeFrom_machine, PriorityInheritance.resumeReadyMidState_machine_eq]), banksKeptOffCore_of_eq (by
          rw [markKeyChangeFrom_machine, PriorityInheritance.resumeReadyMidState_machine_eq]),
        ((show tcbsKept st (Lifecycle.Suspend.resumeReadyMidState st vtid.val) from
          (tcbsKept.updateTcb _ _ _ hInv).trans (tcbsKept.updateTcb _ _ _
            (SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv))).trans
          (tcbsKept.of_objects_eq (markKeyChangeFrom_objects _ _ _))).residentTcbKept⟩
    have h1Inv : (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val)
        vtid.val).objects.invExt := by rw [markKeyChangeFrom_objects]; exact hMidInv
    have h2 := stepCovers_trans h1
      ⟨enqueueRunnableOnCore_covers e (determineTargetCore st vtid.val) _ vtid.val h1Inv,
       enqueueRunnableOnCore_monotone e (determineTargetCore st vtid.val) _ vtid.val, enqueueRunnableOnCore_currentKept e _ _ _,
       residentKeptOffCore_of_eq (by rw [enqueueRunnableOnCore_machineEq]), banksKeptOffCore_of_eq (by rw [enqueueRunnableOnCore_machineEq]),
       (tcbsKept_enqueueRunnableOnCore _ _ _ h1Inv).residentTcbKept⟩
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

/-- The suspend's writes set no core's resident thread (`resident_frame`). -/
macro_rules | `(tactic| resident_frame) => `(tactic|
  (simp only [SystemState.cancelYieldTo_machine, Lifecycle.Suspend.clearPendingStateValid,
    Lifecycle.Suspend.clearPendingState, SystemState.updateTcb_machine,
    removeRunnableOnCore_machine_eq, enqueueRunnableOnCore_machineEq]; done))

/-- ...and they write no core's bank (`bank_frame`). -/
macro_rules | `(tactic| bank_frame) => `(tactic|
  (simp only [SystemState.cancelYieldTo_machine, Lifecycle.Suspend.clearPendingStateValid,
    Lifecycle.Suspend.clearPendingState, SystemState.updateTcb_machine,
    removeRunnableOnCore_machine_eq, enqueueRunnableOnCore_machineEq]; done))

/-! ### Suspend -/

/-- Taking a thread off the core the state places it on covers: a queue removal
stales nothing, and clearing a current slot raises that core's flag. -/
theorem descheduleAt_stepCovers (e : CoreId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (placed : Option CoreId) : stepCovers e st (descheduleAt st tid placed) := by
  unfold descheduleAt
  cases placed with
  | none => exact stepCovers_refl e st
  | some c => exact ⟨removeRunnableOnCore_covers e st tid c, removeRunnableOnCore_monotone e st tid c,
    removeRunnableOnCore_currentKept e st tid c,
    residentKeptOffCore_of_eq (by rw [removeRunnableOnCore_machine_eq]), banksKeptOffCore_of_eq (by rw [removeRunnableOnCore_machine_eq]),
    (tcbsKept_removeRunnableOnCore st tid c).residentTcbKept⟩

theorem descheduleAt_objects_invExt (st : SystemState) (tid : SeLe4n.ThreadId)
    (placed : Option CoreId) (hInv : st.objects.invExt) :
    (descheduleAt st tid placed).objects.invExt := by
  unfold descheduleAt
  cases placed with
  | none => exact hInv
  | some c => exact removeRunnableOnCore_objects_invExt st tid c hInv

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

/-- WS-ZA ZA6.6: what the yield operations write (`KernelObject.withoutYield`) is
no key input. -/
theorem keyInputsEq_of_objectsAgreeOffYield {pre post : SystemState}
    (h : post.objectsAgreeOffYield pre) : keyInputsEq pre post := fun oid => by
  have hv : ∀ x : Option KernelObject,
      keyInputsOf (x.map KernelObject.withoutYield) = keyInputsOf x := by
    intro x; rcases x with _ | o
    · rfl
    · cases o <;> rfl
  rw [← hv post.objects[oid]?, h oid, hv]

/-- WS-ZA ZA6.6: the yield-link cancel moves no key and writes no scheduler state. -/
theorem cancelYieldTo_stepCovers (e : CoreId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : stepCovers e st (cancelYieldTo st tid) :=
  stepCovers_of_keys_sched
    (keyInputsEq_of_objectsAgreeOffYield (SystemState.cancelYieldTo_objectsAgreeOffYield st tid hInv))
    (SystemState.cancelYieldTo_scheduler st tid)

/-- **Suspend covers.**  The IPC teardown, the PIP revert, the donation
cancellation (each key write hooked), the deschedule (a cleared current slot
flags its core), two key-free TCB writes, the key-free yield-link cancel and the
executing core's own scheduling point. -/
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
      exact cancelIpcBlockingReclaimed_objects_invExt vtid.val tcb st
        (Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st vtid.val tcb hInv)
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
        exact descheduleAt_objects_invExt _ _ _ h3Inv
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
      have h6b := stepCovers_trans h6 (cancelYieldTo_stepCovers e _ vtid.val h6Inv)
      have h6bInv := SystemState.cancelYieldTo_preserves_objects_invExt _ vtid.val h6Inv
      obtain ⟨h7, h7Inv⟩ := suspendRescheduleOnCore_stepCovers e h6bInv hStep
      exact ⟨stepCovers_trans h6b h7, h7Inv⟩
  · contradiction

end SeLe4n.Kernel
