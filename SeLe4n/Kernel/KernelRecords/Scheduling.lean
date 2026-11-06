-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Frame
import SeLe4n.Kernel.Scheduler.Invariant.ReschedulePendingSchedulingPoints
import SeLe4n.Kernel.IPC.Invariant.ReplyWaitersFrame

/-!
# The scheduling points keep the records' reads

WS-ZA ZA6.37.  A scheduling point moves threads between a core's run queue and
its `current` slot, saves and restores register contexts, and records the
core's resident: it writes run-queue links, register files, the scheduler record
and the machine, none of which a record view reads (`RecordsFrame`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)
open SeLe4n.Kernel.PriorityInheritance (scheduleLocalSuccessorFrom dispatchVacatedCore
  deferResidentElsewhere settleResidencyOnCore pokeReleasedResident_objects)

namespace RecordsFrame

/-- The record update of one state's objects and scheduler over another. -/
theorem asid_of_onlyObjectsScheduler {st st' : SystemState}
    (h : SystemState.onlyObjectsSchedulerDiffer st' st) : st'.asidTable = st.asidTable := by
  rw [h]

/-- A step that writes run-queue links (and the scheduler) and keeps the reply
views. -/
theorem of_runLinkStep {st st' : SystemState} (h : st'.objectsAgreeOffRunLinks st)
    (hR : st'.replyViews = st.replyViews) (hD : SystemState.onlyObjectsSchedulerDiffer st' st)
    (hInv : st'.objects.invExt) : RecordsFrame st st' :=
  of_agreeOffRunLinks h hR (asid_of_onlyObjectsScheduler hD) hInv

theorem runEnqueueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    RecordsFrame st (st.runEnqueueOnCore c t p) :=
  of_runLinkStep (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks st c t p)
    (SystemState.runEnqueueOnCore_replyViews_eq st c t p)
    (SystemState.runEnqueueOnCore_onlyObjectsSchedulerDiffer st c t p)
    (SystemState.runEnqueueOnCore_objects_invExt st c t p hInv)

theorem runRemoveOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsFrame st (st.runRemoveOnCore c t) :=
  of_runLinkStep (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks st c t)
    (SystemState.runRemoveOnCore_replyViews_eq st c t)
    (SystemState.runRemoveOnCore_onlyObjectsSchedulerDiffer st c t)
    (SystemState.runRemoveOnCore_objects_invExt st c t hInv)

/-- A write of the scheduler record alone. -/
theorem withScheduler (st : SystemState) (s : SchedulerState) (hInv : st.objects.invExt) :
    RecordsFrame st { st with scheduler := s } := of_objects_eq hInv rfl rfl

/-- A write of the machine alone. -/
theorem withMachine (st : SystemState) (m : MachineState) (hInv : st.objects.invExt) :
    RecordsFrame st { st with machine := m } := of_objects_eq hInv rfl rfl

theorem preemptCurrentOnCore (st : SystemState) (c : CoreId) (incoming : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsFrame st (preemptCurrentOnCore st c incoming) := by
  unfold _root_.SeLe4n.Kernel.preemptCurrentOnCore
  split
  · exact refl hInv
  · split
    · exact refl hInv
    · split
      · rename_i prevTcb h _
        have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp h
        have h1 := rewriteObject (o := .tcb { prevTcb with registerContext := st.machine.regsOnCore c })
          (SystemState.rewriteAdmissible_tcb h _) hInv (by rw [hO]; rfl)
        exact h1.trans (runEnqueueOnCore _ c _ _ h1.invExt)
      · exact refl hInv

theorem dropCurrentOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (dropCurrentOnCore st c) := by
  have h := preemptCurrentOnCore st c (idleThreadId c) hInv
  exact h.trans (withScheduler _ _ h.invExt)

theorem restoreIncomingContextOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsFrame st (restoreIncomingContextOnCore st c tid) := by
  unfold _root_.SeLe4n.Kernel.restoreIncomingContextOnCore
  split
  · exact withMachine _ _ hInv
  · exact refl hInv

theorem switchToThreadOnCore {st st' : SystemState} {c : CoreId} {tid : SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : switchToThreadOnCore st c tid = .ok st') :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.switchToThreadOnCore at h
  split at h
  · split at h
    · cases h
      have h1 := preemptCurrentOnCore st c tid hInv
      have h2 := h1.trans (runRemoveOnCore _ c tid h1.invExt)
      have h3 : RecordsFrame st (restoreIncomingContextOnCoreUnlessCurrent
          ((_root_.SeLe4n.Kernel.preemptCurrentOnCore st c tid).runRemoveOnCore c tid) c tid) := by
        unfold restoreIncomingContextOnCoreUnlessCurrent
        split
        · exact h2
        · exact h2.trans (restoreIncomingContextOnCore _ c tid h2.invExt)
      exact h3.congr rfl rfl
    · cases h
  · cases h

theorem clearReschedulePendingOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (st.clearReschedulePendingOnCore c) := withScheduler _ _ hInv

theorem markReschedulePendingOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (st.markReschedulePendingOnCore c) := withScheduler _ _ hInv

theorem handleRescheduleSgiOnCore {st st' : SystemState} {c : CoreId}
    (hInv : st.objects.invExt) (h : handleRescheduleSgiOnCore st c = .ok st') :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.handleRescheduleSgiOnCore at h
  split at h
  · cases h
  · split at h
    · cases h
      have h1 := dropCurrentOnCore st c hInv
      exact h1.trans (clearReschedulePendingOnCore _ c h1.invExt)
    · cases h; exact clearReschedulePendingOnCore st c hInv
  · split at h
    · split at h
      · cases h
        rename_i st₁ hSw
        have h1 := switchToThreadOnCore hInv hSw
        exact h1.trans (clearReschedulePendingOnCore _ c h1.invExt)
      · split at h
        · cases h
          have h1 := dropCurrentOnCore st c hInv
          exact h1.trans (clearReschedulePendingOnCore _ c h1.invExt)
        · cases h; exact clearReschedulePendingOnCore st c hInv
    · cases h; exact clearReschedulePendingOnCore st c hInv

theorem dispatchVacatedCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (dispatchVacatedCore st c) := by
  unfold PriorityInheritance.dispatchVacatedCore
  split
  · exact refl hInv
  · split
    · rename_i st' h; exact handleRescheduleSgiOnCore hInv h
    · exact refl hInv

theorem scheduleLocalSuccessorFrom (caller? : Option SeLe4n.ThreadId) (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (scheduleLocalSuccessorFrom caller? st c) := by
  unfold PriorityInheritance.scheduleLocalSuccessorFrom
  split
  · split
    · rename_i st' h; exact handleRescheduleSgiOnCore hInv h
    · exact refl hInv
  · exact refl hInv

theorem deferResidentElsewhere (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (deferResidentElsewhere st c) := by
  unfold PriorityInheritance.deferResidentElsewhere
  dsimp only
  split
  · split
    · rename_i tid _ _
      have h0 := restoreIncomingContextOnCore st c tid hInv
      split
      · rename_i st' h; exact h0.trans (switchToThreadOnCore h0.invExt h)
      · exact h0.trans (dropCurrentOnCore _ c h0.invExt)
    · exact refl hInv
  · exact refl hInv

theorem pokeReleasedResident (st : SystemState) (c : CoreId) (o n : Nat)
    (hInv : st.objects.invExt) :
    RecordsFrame st (PriorityInheritance.pokeReleasedResident st c o n) := by
  rcases PriorityInheritance.pokeReleasedResident_cases st c o n with h | ⟨q, -, h⟩
  · rw [h]; exact refl hInv
  · rw [h]; exact markReschedulePendingOnCore st q hInv

theorem settleResidencyOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (settleResidencyOnCore st c) := by
  unfold PriorityInheritance.settleResidencyOnCore
  have h1 := dispatchVacatedCore st c hInv
  have h2 := h1.trans (deferResidentElsewhere _ c h1.invExt)
  refine RecordsFrame.trans ?_ (pokeReleasedResident _ c _ _ ?_)
  · exact h2.trans (withMachine _ _ h2.invExt)
  · exact h2.invExt

theorem saveOutgoingContextOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (saveOutgoingContextOnCore st c) := by
  unfold _root_.SeLe4n.Kernel.saveOutgoingContextOnCore
  split
  · exact refl hInv
  · exact updateTcb st _ hInv fun _ => rfl

end RecordsFrame

end SeLe4n.Kernel
