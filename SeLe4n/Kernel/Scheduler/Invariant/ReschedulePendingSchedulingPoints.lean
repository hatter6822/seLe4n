-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant.ReschedulePendingCoverage
import SeLe4n.Kernel.Scheduler.Operations.PerCoreSwitchToThread
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake

/-!
# The executing core's own scheduling points cover

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md`, PR B2.  A scheduling point
on the executing core `e` — the preempt, the switch, the reschedule handler,
and the commit's local successor and residency settling built from them —
writes only core `e`'s run queue and `current` slot, clears only core `e`'s
flag, and rewrites only register contexts.  So it covers every remote core by
frame (`stepCovers_of_frame`): no remote slot moves, no key moves, no remote
flag drops.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)
open SeLe4n.Kernel.PriorityInheritance (scheduleLocalSuccessor dispatchVacatedCore
  deferResidentElsewhere settleResidencyOnCore)

/-- The preempt re-enqueues on its own core and saves a register context. -/
theorem preemptCurrentOnCore_stepCovers (e : CoreId) (st : SystemState)
    (incoming : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    stepCovers e st (preemptCurrentOnCore st e incoming) := by
  apply stepCovers_of_frame
  · unfold preemptCurrentOnCore
    cases hC : st.scheduler.currentOnCore e with
    | none => exact keyInputsEq_refl st
    | some prevTid =>
      simp only []
      by_cases hEq : (prevTid == incoming) = true
      · simp only [hEq, if_true]; exact keyInputsEq_refl st
      · simp only [hEq, Bool.false_eq_true, if_false]
        cases hW : st.getTcbWitnessed? prevTid with
        | none => exact keyInputsEq_refl st
        | some w =>
          obtain ⟨prevTcb, h⟩ := w
          have hO : st.objects[prevTid.toObjId]? = some (.tcb prevTcb) :=
            (SystemState.getTcb?_eq_some_iff st prevTid prevTcb).mp h
          exact keyInputsEq_trans
            (keyInputsEq_rewriteObject (SystemState.rewriteAdmissible_tcb h _) hInv
              (by rw [hO]; rfl))
            (keyInputsEq_with_scheduler _ _)
  · intro c hc; exact preemptCurrentOnCore_runQueueOnCore_ne st e incoming c (Ne.symm hc)
  · intro c _; exact preemptCurrentOnCore_currentOnCore st e incoming c
  · intro c _ hp
    unfold preemptCurrentOnCore
    split
    · exact hp
    · split
      · exact hp
      · split
        · simpa [SystemState.rewriteObject_scheduler] using hp
        · exact hp

/-- A step that writes only core `e`'s run queue and `current` slot of the
scheduler, keeps the object store's key inputs and every flag, covers. -/
theorem stepCovers_of_local_slots {e : CoreId} {pre post : SystemState}
    (hKeys : keyInputsEq pre post)
    (hSched : ∀ c, c ≠ e →
      post.scheduler.runQueueOnCore c = pre.scheduler.runQueueOnCore c ∧
      post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c ∧
      post.scheduler.reschedulePendingOnCore c = pre.scheduler.reschedulePendingOnCore c) :
    stepCovers e pre post :=
  stepCovers_of_frame hKeys (fun c hc => (hSched c hc).1) (fun c hc => (hSched c hc).2.1)
    (fun c hc hp => by rw [(hSched c hc).2.2]; exact hp)

/-- The switch preempts, dequeues, restores and sets `current`, all on its own
core. -/
theorem switchToThreadOnCore_stepCovers (e : CoreId) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (h : switchToThreadOnCore st e tid = .ok st') :
    stepCovers e st st' := by
  unfold switchToThreadOnCore at h
  cases hT : st.getTcb? tid with
  | none => rw [hT] at h; cases h
  | some tcb =>
    rw [hT] at h
    simp only [] at h
    split at h
    · injection h with h
      subst h
      refine stepCovers_trans (preemptCurrentOnCore_stepCovers e st tid hInv)
        (stepCovers_of_local_slots ?_ ?_)
      · apply keyInputsEq_of_objects_eq
        simp
      · intro c hc
        have hne : e ≠ c := Ne.symm hc
        simp [hne]
    · cases h

/-- Clearing the executing core's own flag covers. -/
theorem clearReschedulePendingOnCore_stepCovers (e : CoreId) (st : SystemState) :
    stepCovers e st (st.clearReschedulePendingOnCore e) :=
  stepCovers_of_local_slots (keyInputsEq_of_objects_eq (by simp)) fun c hc => by
    have hne : e ≠ c := Ne.symm hc
    simp [SystemState.clearReschedulePendingOnCore, SchedulerState.clearReschedulePendingOnCore_reschedulePendingOnCore_ne _ _ _ hne]

/-- The drop of an out-of-domain incumbent re-queues it and clears the slot, all
on its own core. -/
theorem dropCurrentOnCore_stepCovers (e : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) :
    stepCovers e st (dropCurrentOnCore st e) := by
  refine stepCovers_trans (preemptCurrentOnCore_stepCovers e st (idleThreadId e) hInv)
    (stepCovers_of_local_slots ?_ ?_)
  · apply keyInputsEq_of_objects_eq
    rfl
  · intro c hc
    have hne : e ≠ c := Ne.symm hc
    simp [dropCurrentOnCore, hne]

/-- The reschedule handler on the executing core covers. -/
theorem handleRescheduleSgiOnCore_stepCovers (e : CoreId) (st st' : SystemState)
    (hInv : st.objects.invExt) (h : handleRescheduleSgiOnCore st e = .ok st') :
    stepCovers e st st' := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · cases h
  · split at h
    · injection h with h; subst h
      exact stepCovers_trans (dropCurrentOnCore_stepCovers e st hInv)
        (clearReschedulePendingOnCore_stepCovers e _)
    · injection h with h; subst h; exact clearReschedulePendingOnCore_stepCovers e st
  · split at h
    · split at h
      · injection h with h; subst h
        rename_i st₁ hSw
        exact stepCovers_trans (switchToThreadOnCore_stepCovers e st st₁ _ hInv hSw)
          (clearReschedulePendingOnCore_stepCovers e st₁)
      · cases h
    · injection h with h; subst h; exact clearReschedulePendingOnCore_stepCovers e st

/-- The commit's local successor covers, whichever caller the seam captured. -/
theorem scheduleLocalSuccessorFrom_stepCovers (e : CoreId) (caller? : Option SeLe4n.ThreadId)
    (pending0 : Bool) (post : SystemState) (hInv : post.objects.invExt) :
    stepCovers e post (PriorityInheritance.scheduleLocalSuccessorFrom caller? pending0 post e) := by
  unfold PriorityInheritance.scheduleLocalSuccessorFrom
  split
  · split
    · rename_i st' h
      exact handleRescheduleSgiOnCore_stepCovers e post st' hInv h
    · exact stepCovers_refl e post
  · exact stepCovers_refl e post

/-- Dispatching a vacated executing core covers. -/
theorem dispatchVacatedCore_stepCovers (e : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) :
    stepCovers e st (dispatchVacatedCore st e) := by
  unfold dispatchVacatedCore
  split
  · exact stepCovers_refl e st
  · split
    · rename_i st' h
      exact handleRescheduleSgiOnCore_stepCovers e st st' hInv h
    · exact stepCovers_refl e st

theorem dispatchVacatedCore_preserves_objects_invExt (e : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) : (dispatchVacatedCore st e).objects.invExt := by
  unfold dispatchVacatedCore
  split
  · exact hInv
  · split
    · rename_i st' h
      exact handleRescheduleSgiOnCore_preserves_objects_invExt st e st' hInv h
    · exact hInv

/-- Deferring a thread still resident elsewhere switches the executing core to
its idle thread, or preempts and vacates it. -/
theorem deferResidentElsewhere_stepCovers (e : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) :
    stepCovers e st (deferResidentElsewhere st e) := by
  unfold deferResidentElsewhere
  split
  · split
    · split
      · rename_i st' h
        exact switchToThreadOnCore_stepCovers e st st' _ hInv h
      · refine stepCovers_trans (preemptCurrentOnCore_stepCovers e st _ hInv)
          (stepCovers_of_local_slots (keyInputsEq_with_scheduler _ _) ?_)
        intro c hc
        have hne : e ≠ c := Ne.symm hc
        simp [hne]
    · exact stepCovers_refl e st
  · exact stepCovers_refl e st

/-- **The commit's residency settling covers**: the dispatch and the deferral
are scheduling points on the executing core, and the residency record is a
machine write. -/
theorem settleResidencyOnCore_stepCovers (e : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) :
    stepCovers e st (settleResidencyOnCore st e) := by
  unfold settleResidencyOnCore
  refine stepCovers_trans (stepCovers_trans (dispatchVacatedCore_stepCovers e st hInv)
    (deferResidentElsewhere_stepCovers e _ (dispatchVacatedCore_preserves_objects_invExt e st hInv)))
    (stepCovers_of_scheduler_eq (keyInputsEq_of_objects_eq rfl) rfl)

/-- Staging the caller's result rewrites a register context and the bank. -/
theorem stageCallerReturnFor_stepCovers (e : CoreId) (caller? : Option SeLe4n.ThreadId)
    (post : SystemState) (o : Architecture.SyscallOutcome) (hInv : post.objects.invExt) :
    stepCovers e post (Architecture.stageCallerReturnFor caller? post e o) ∧
      (Architecture.stageCallerReturnFor caller? post e o).objects.invExt := by
  have hW : ∀ tid f, keyInputsEq post (Architecture.writeReturnFrameToTcb post tid f) :=
    fun _ _ => keyInputsEq_updateTcb hInv fun _ => rfl
  have hWInv : ∀ tid f, (Architecture.writeReturnFrameToTcb post tid f).objects.invExt :=
    fun _ _ => SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv
  have hWriteSched : ∀ tid f, (Architecture.writeReturnFrameToTcb post tid f).scheduler = post.scheduler :=
    fun _ _ => by simp [Architecture.writeReturnFrameToTcb, SystemState.updateTcb_scheduler]
  cases o with
  | blocks => exact ⟨stepCovers_refl e post, hInv⟩
  | faulted => exact ⟨stepCovers_refl e post, hInv⟩
  | returns f =>
    cases caller? with
    | none => simp only [Architecture.stageCallerReturnFor]; exact ⟨stepCovers_refl e post, hInv⟩
    | some tid =>
      simp only [Architecture.stageCallerReturnFor]
      split
      · exact ⟨stepCovers_of_scheduler_eq (hW tid f) (hWriteSched tid f), hWInv tid f⟩
      · exact ⟨stepCovers_of_scheduler_eq (hW tid f) (hWriteSched tid f), hWInv tid f⟩

theorem scheduleLocalSuccessorFrom_preserves_objects_invExt (e : CoreId)
    (caller? : Option SeLe4n.ThreadId) (pending0 : Bool) (post : SystemState)
    (hInv : post.objects.invExt) :
    (PriorityInheritance.scheduleLocalSuccessorFrom caller? pending0 post e).objects.invExt := by
  unfold PriorityInheritance.scheduleLocalSuccessorFrom
  split
  · split
    · rename_i st' h
      exact handleRescheduleSgiOnCore_preserves_objects_invExt post e st' hInv h
    · exact hInv
  · exact hInv

/-- **The syscall commit's tail covers**: from the dispatched state, staging
the caller's result, the local successor and the residency settling raise no
remote staleness and drop no remote flag. -/
theorem syscallCommitTail_stepCovers (e : CoreId) (caller? : Option SeLe4n.ThreadId)
    (pending0 : Bool) (post : SystemState) (o : Architecture.SyscallOutcome) (hInv : post.objects.invExt) :
    stepCovers e post (settleResidencyOnCore
      (PriorityInheritance.scheduleLocalSuccessorFrom caller? pending0
        (Architecture.stageCallerReturnFor caller? post e o) e) e) := by
  obtain ⟨hStage, hStageInv⟩ := stageCallerReturnFor_stepCovers e caller? post o hInv
  exact stepCovers_trans (stepCovers_trans hStage
    (scheduleLocalSuccessorFrom_stepCovers e caller? pending0 _ hStageInv))
    (settleResidencyOnCore_stepCovers e _
      (scheduleLocalSuccessorFrom_preserves_objects_invExt e caller? pending0 _ hStageInv))

end SeLe4n.Kernel
