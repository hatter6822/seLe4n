-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.ContextLenderLinks
import SeLe4n.Kernel.KernelRecords.Tails

/-! # The lenders' stage: the unit a kernel entry chains

WS-SX SX8 (ruling (aa) of the notification-donation row).  `lendingLabelsEqual`
(every lender on a context's stack flows to the context's label) is carried
across a kernel entry the way the kernel records are (`RecordsStage`,
`KernelRecords/Frame.lean`): each step of the entry is a `LendersStage`, and the
stages compose.

* A step that writes no stack view, or only shrinks one, is a stage with no
  premise: `contextStackLinksShrink` composes and carries the flow
  (`LendersStage.of_linksShrink`), and `chainObjectsKept` (no reply object and no
  context written) is one.
* A step that pushes a frame or links a caller reads the chain facts at the
  state it runs from: `LendersPremises`, the store's invariant, the donation
  chain's well-formedness and the reply/caller reciprocity.  The entry theorems
  take them **as premises read off the state the step runs from**, exactly where
  the per-entry IPC theorems take the chain facts: no theorem yet concludes them
  at an entry's committed state (`docs/REGISTERED_DEBT.md` table C,
  "`ipcReachable` is not carried across a trace of kernel entries", owner WS-PK).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **What a lending step reads beyond the lenders' flow**, at the state it runs
from: the store's invariant, the donation chain's shape (a pushed frame is on no
stack), and the reply/caller reciprocity (a pushed frame's caller is the
donor). -/
structure LendersPremises (st : SystemState) : Prop where
  invExt : st.objects.invExt
  chain : donationChainWellFormed st
  linkage : replyCallerLinkageReciprocal st

/-- **A step that carries the lenders' flow**: the unit a kernel entry chains. -/
def LendersStage (ctx : LabelingContext) (st st' : SystemState) : Prop :=
  lendingLabelsEqual ctx st → lendingLabelsEqual ctx st'

namespace LendersStage

variable {ctx : LabelingContext}

theorem refl (st : SystemState) : LendersStage ctx st st := id

theorem trans {a b c : SystemState} (h₁ : LendersStage ctx a b) (h₂ : LendersStage ctx b c) :
    LendersStage ctx a c := h₂ ∘ h₁

theorem of_eq {st st' : SystemState} (h : st' = st) : LendersStage ctx st st' := by subst h; exact refl _

theorem of_linksShrink {st st' : SystemState} (h : contextStackLinksShrink st st') :
    LendersStage ctx st st' := fun hF => lendingLabelsEqual_of_linksShrink hF h

theorem of_kept {st st' : SystemState} (h : chainObjectsKept st st') :
    LendersStage ctx st st' := of_linksShrink h.linksShrink

theorem of_viewsAgree {st st' : SystemState} (h : contextStackViewsAgree st st') :
    LendersStage ctx st st' := fun hF => lendingLabelsEqual_of_viewsAgree hF h

/-- A stage onto a transition's state is a stage onto the state it returns. -/
theorem of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : LendersStage ctx st p.1) (h : p = (st', r)) : LendersStage ctx st st' := by
  subst h; exact s

end LendersStage

/-! ### The scheduler's and the entry's frames

Each mirrors its `RecordsFrame` twin (`KernelRecords/Scheduling.lean`,
`KernelRecords/Tails.lean`): the same steps write thread records, the
scheduler and the machine, and no reply object or context.  The store's
invariant at each intermediate state is read off the twin. -/

namespace chainObjectsKept

open SeLe4n.Kernel.Concurrency (CoreId)

theorem withMachine (st : SystemState) (m : MachineState) :
    chainObjectsKept st { st with machine := m } := of_objects_eq rfl

theorem withScheduler (st : SystemState) (s : SchedulerState) :
    chainObjectsKept st { st with scheduler := s } := of_objects_eq rfl

theorem rewriteObject_tcb {st : SystemState} {k : SeLe4n.ObjId} {x : TCB}
    (hA : st.rewriteAdmissible k (.tcb x)) (hInv : st.objects.invExt)
    (hB : objBindingShrink st.objects[k]? (some (.tcb x)) := by
      first
        | exact objBindingShrink.of_free rfl
        | exact objBindingShrink.of_eq rfl
        | (apply objBindingShrink.ofTcb (by assumption); exact .inr ⟨rfl, rfl⟩)
        | (apply objBindingShrink.ofTcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp
            (by assumption)); exact .inr ⟨rfl, rfl⟩)
        | (apply objBindingShrink.ofTcb (lookupTcb_some_objects _ _ _ (by assumption));
            exact .inr ⟨rfl, rfl⟩)) :
    chainObjectsKept st (st.rewriteObject k (.tcb x) hA) :=
  insert_other hInv (fun _ e => by cases e) (fun _ e => by cases e) hB

theorem runEnqueueOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : chainObjectsKept st (st.runEnqueueOnCore c t p) :=
  of_objectsAgreeOffRunLinks (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks st c t p)

theorem runRemoveOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    chainObjectsKept st (st.runRemoveOnCore c t) :=
  of_objectsAgreeOffRunLinks (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks st c t)

theorem preemptCurrentOnCore (st : SystemState) (c : CoreId) (incoming : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : chainObjectsKept st (preemptCurrentOnCore st c incoming) := by
  unfold _root_.SeLe4n.Kernel.preemptCurrentOnCore
  split
  · exact refl _
  · split
    · exact refl _
    · split
      · exact (rewriteObject_tcb _ hInv).trans (runEnqueueOnCore _ c _ _)
      · exact refl _

theorem dropCurrentOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    chainObjectsKept st (dropCurrentOnCore st c) :=
  (preemptCurrentOnCore st c (idleThreadId c) hInv).trans (withScheduler _ _)

theorem restoreIncomingContextOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    chainObjectsKept st (restoreIncomingContextOnCore st c tid) := by
  unfold _root_.SeLe4n.Kernel.restoreIncomingContextOnCore
  split
  · exact withMachine _ _
  · exact refl _

theorem switchToThreadOnCore {st st' : SystemState} {c : CoreId} {tid : SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : switchToThreadOnCore st c tid = .ok st') :
    chainObjectsKept st st' := by
  unfold _root_.SeLe4n.Kernel.switchToThreadOnCore at h
  split at h
  · split at h
    · cases h
      have h2 := (preemptCurrentOnCore st c tid hInv).trans (runRemoveOnCore _ c tid)
      have h3 : chainObjectsKept st (restoreIncomingContextOnCoreUnlessCurrent
          ((_root_.SeLe4n.Kernel.preemptCurrentOnCore st c tid).runRemoveOnCore c tid) c tid) := by
        unfold restoreIncomingContextOnCoreUnlessCurrent
        split
        · exact h2
        · exact h2.trans (restoreIncomingContextOnCore _ c tid)
      exact h3.trans (of_objects_eq rfl)
    · cases h
  · cases h

theorem handleRescheduleSgiOnCore {st st' : SystemState} {c : CoreId}
    (hInv : st.objects.invExt) (h : handleRescheduleSgiOnCore st c = .ok st') :
    chainObjectsKept st st' := by
  unfold _root_.SeLe4n.Kernel.handleRescheduleSgiOnCore at h
  split at h
  · cases h
  · split at h
    · cases h; exact (dropCurrentOnCore st c hInv).trans (withScheduler _ _)
    · cases h; exact withScheduler _ _
  · split at h
    · split at h
      · cases h
        rename_i st₁ hSw
        exact (switchToThreadOnCore hInv hSw).trans (withScheduler _ _)
      · split at h
        · cases h; exact (dropCurrentOnCore st c hInv).trans (withScheduler _ _)
        · cases h; exact withScheduler _ _
    · cases h; exact withScheduler _ _

theorem dispatchVacatedCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    chainObjectsKept st (PriorityInheritance.dispatchVacatedCore st c) := by
  unfold PriorityInheritance.dispatchVacatedCore
  split
  · exact refl _
  · split
    · rename_i st' h; exact handleRescheduleSgiOnCore hInv h
    · exact refl _

/-- The scheduling point's drop of a caller whose lent context went back
(WS-SX SX36.2): a run-queue removal, or nothing. -/
theorem dropReturnedContextCaller (returnable : Bool) (caller? : Option SeLe4n.ThreadId)
    (st : SystemState) (c : CoreId) :
    chainObjectsKept st (_root_.SeLe4n.Kernel.dropReturnedContextCaller returnable caller? st c) :=
  dropReturnedContextCaller_induct (fun a b => chainObjectsKept a b) returnable caller? st c
    (refl _) (fun t => removeRunnableOnCore st t c)

theorem scheduleLocalSuccessorFrom (caller? : Option SeLe4n.ThreadId) (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) :
    chainObjectsKept st (PriorityInheritance.scheduleLocalSuccessorFrom caller? st c) := by
  unfold PriorityInheritance.scheduleLocalSuccessorFrom
  split
  · split
    · rename_i st' h; exact handleRescheduleSgiOnCore hInv h
    · exact refl _
  · exact refl _

theorem deferResidentElsewhere (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    chainObjectsKept st (PriorityInheritance.deferResidentElsewhere st c) := by
  unfold PriorityInheritance.deferResidentElsewhere
  dsimp only
  split
  · split
    · rename_i tid _ _
      have h0 := restoreIncomingContextOnCore st c tid
      have hI0 := (RecordsFrame.restoreIncomingContextOnCore st c tid hInv).invExt
      split
      · rename_i st' h; exact h0.trans (switchToThreadOnCore hI0 h)
      · exact h0.trans (dropCurrentOnCore _ c hI0)
    · exact refl _
  · exact refl _

theorem pokeReleasedResident (st : SystemState) (c : CoreId) (o n : Nat) :
    chainObjectsKept st (PriorityInheritance.pokeReleasedResident st c o n) := by
  rcases PriorityInheritance.pokeReleasedResident_cases st c o n with h | ⟨q, -, h⟩
  · rw [h]; exact refl _
  · rw [h]; exact withScheduler _ _

theorem settleResidencyOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    chainObjectsKept st (PriorityInheritance.settleResidencyOnCore st c) := by
  unfold PriorityInheritance.settleResidencyOnCore
  have F1 := RecordsFrame.dispatchVacatedCore st c hInv
  have h2 := (dispatchVacatedCore st c hInv).trans (deferResidentElsewhere _ c F1.invExt)
  exact (h2.trans (withMachine _ _)).trans (pokeReleasedResident _ c _ _)

theorem settleResidencyAt (st : SystemState) (coreId : UInt64) (hInv : st.objects.invExt) :
    chainObjectsKept st (PriorityInheritance.settleResidencyAt st coreId) := by
  unfold PriorityInheritance.settleResidencyAt
  split
  · exact settleResidencyOnCore st _ hInv
  · exact refl _

end chainObjectsKept

/-! ### The yield's writes and the entry's tails -/

theorem objStackViews_map_withoutYield (o? : Option KernelObject) :
    objStackHead (o?.map KernelObject.withoutYield) = objStackHead o? ∧
    objStackPrev (o?.map KernelObject.withoutYield) = objStackPrev o? ∧
    objStackCaller (o?.map KernelObject.withoutYield) = objStackCaller o? := by
  cases o? with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some o => cases o <;> exact ⟨rfl, rfl, rfl⟩

/-- **A write of the yield codes and the consumed count alone** (the yield
link, `setConsumed`) is a frame of the three views. -/
theorem contextStackViewsAgree_of_objectsAgreeOffYield {st st' : SystemState}
    (h : st'.objectsAgreeOffYield st) : contextStackViewsAgree st st' := by
  have key : ∀ x : SeLe4n.ObjId, objStackHead st'.objects[x]? = objStackHead st.objects[x]? ∧
      objStackPrev st'.objects[x]? = objStackPrev st.objects[x]? ∧
      objStackCaller st'.objects[x]? = objStackCaller st.objects[x]? := fun x => by
    have a := objStackViews_map_withoutYield st'.objects[x]?
    have b := objStackViews_map_withoutYield st.objects[x]?
    rw [h x] at a
    exact ⟨a.1.symm.trans b.1, a.2.1.symm.trans b.2.1, a.2.2.symm.trans b.2.2⟩
  have keyB : ∀ o : Option KernelObject,
      objBindingWords (o.map KernelObject.withoutYield) = objBindingWords o := by
    intro o; cases o with
    | none => rfl
    | some o => cases o <;> rfl
  refine ⟨fun s => ?_, fun r => ?_, fun r => ?_, fun x => ?_⟩
  · rw [contextStackHead_eq_obj, contextStackHead_eq_obj]; exact (key _).1
  · rw [replyStackPrev_eq_obj, replyStackPrev_eq_obj]; exact (key _).2.1
  · rw [replyStackCaller_eq_obj, replyStackCaller_eq_obj]; exact (key _).2.2
  · rw [← keyB st'.objects[x]?, ← keyB st.objects[x]?, h x]

namespace chainObjectsKept

open SeLe4n.Kernel.Concurrency (CoreId)

theorem saveTrapFrameOnCore (st : SystemState) (c : CoreId) (rf : SeLe4n.RegisterFile)
    (hInv : st.objects.invExt) : chainObjectsKept st (Architecture.saveTrapFrameOnCore st c rf) := by
  unfold Architecture.saveTrapFrameOnCore
  split
  · split
    · split
      · rename_i tid _ _ _ _
        exact (updateTcb st tid _ hInv).trans (withMachine _ _)
      · exact refl _
    · exact refl _
  · exact refl _

theorem saveVacatedFrameOnCore (st : SystemState) (c : CoreId) (rf saved : SeLe4n.RegisterFile)
    (hInv : st.objects.invExt) :
    chainObjectsKept st (Architecture.saveVacatedFrameOnCore st c rf saved) := by
  unfold Architecture.saveVacatedFrameOnCore
  split
  · split
    · split
      · exact updateTcb st _ _ hInv
      · exact refl _
    · exact refl _
  · exact refl _

theorem saveCapturedTrapFrame (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt) :
    chainObjectsKept st (Architecture.saveCapturedTrapFrame st c frame) := by
  cases frame with
  | none => exact refl _
  | some ic =>
    exact (saveTrapFrameOnCore st c ic.snapshot hInv).trans (saveVacatedFrameOnCore _ c _ _
      (RecordsFrame.saveTrapFrameOnCore st c ic.snapshot hInv).invExt)

theorem saveCapturedSyscallFrame (st : SystemState) (c : CoreId)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt) :
    chainObjectsKept st (Architecture.saveCapturedSyscallFrame st c frame) := by
  cases frame with
  | none => exact refl _
  | some ic =>
    exact (saveTrapFrameOnCore st c ic.snapshot hInv).trans (saveVacatedFrameOnCore _ c _ _
      (RecordsFrame.saveTrapFrameOnCore st c ic.snapshot hInv).invExt)

theorem saveCapturedTrapFrameAt (st : SystemState) (coreId : UInt64)
    (frame : Option Architecture.InFlightContext) (hInv : st.objects.invExt) :
    chainObjectsKept st (Concurrency.saveCapturedTrapFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedTrapFrameAt
  split
  · exact saveCapturedTrapFrame st _ frame hInv
  · exact refl _

theorem syncUserWords (st : SystemState) (bytes : ByteArray) (n : Nat) :
    chainObjectsKept st (Architecture.IpcBufferRead.syncUserWords st bytes n) := by
  unfold Architecture.IpcBufferRead.syncUserWords
  split <;> exact withMachine _ _

theorem clearUserWords (st : SystemState) :
    chainObjectsKept st (Architecture.IpcBufferRead.clearUserWords st) := syncUserWords st _ _

theorem clearLedgers (st : SystemState) :
    chainObjectsKept st (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites st)) :=
  of_objects_eq rfl

theorem writeReturnFrameToTcb (st : SystemState) (t : SeLe4n.ThreadId)
    (f : Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    chainObjectsKept st (Architecture.writeReturnFrameToTcb st t f) := updateTcb st t _ hInv

theorem stageCallerReturnFor (caller? : Option SeLe4n.ThreadId) (st : SystemState) (c : CoreId)
    (o : Architecture.SyscallOutcome) (hInv : st.objects.invExt) :
    chainObjectsKept st (Architecture.stageCallerReturnFor caller? st c o) := by
  cases o with
  | blocks => exact refl _
  | faulted => exact refl _
  | resumes => exact refl _
  | returns f =>
    cases caller? with
    | none => exact refl _
    | some tid =>
      simp only [Architecture.stageCallerReturnFor]
      have h := writeReturnFrameToTcb st tid f hInv
      split
      · exact h.trans (withMachine _ _)
      · exact h

end chainObjectsKept

namespace LendersStage

variable {ctx : LabelingContext}

theorem activateThreadOnCore (st : SystemState) (c : Concurrency.CoreId)
    (hInv : st.objects.invExt) : LendersStage ctx st (_root_.SeLe4n.Kernel.activateThreadOnCore st c) :=
  of_viewsAgree (contextStackViewsAgree_of_objectsAgreeOffYield
    (activateThreadOnCore_objectsAgreeOffYield st c hInv))

theorem activateThreadAt (st : SystemState) (coreId : UInt64) (hInv : st.objects.invExt) :
    LendersStage ctx st (_root_.SeLe4n.Kernel.activateThreadAt st coreId) := by
  unfold _root_.SeLe4n.Kernel.activateThreadAt
  split
  · exact activateThreadOnCore st _ hInv
  · exact refl _

/-- **The settlement, the activation and the ledger drains** every committing
entry ends with. -/
theorem entryTail (st : SystemState) (coreId : UInt64) (hInv : st.objects.invExt) :
    LendersStage ctx st (Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites
      (_root_.SeLe4n.Kernel.activateThreadAt
        (PriorityInheritance.settleResidencyAt st coreId) coreId))) :=
  ((of_kept (chainObjectsKept.settleResidencyAt st coreId hInv)).trans
    (activateThreadAt _ coreId (RecordsFrame.settleResidencyAt st coreId hInv).invExt)).trans
    (of_kept (chainObjectsKept.clearLedgers _))

end LendersStage

end SeLe4n.Kernel
