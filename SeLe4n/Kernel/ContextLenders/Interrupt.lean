-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Timer

/-! # The interrupt entry keeps the lenders' flow

WS-SX SX8.  The interrupt's step is seL4's `sendSignal` on the line's bound
notification (the wake of a waiter or of the bound receiver, through thread
and notification records and the scheduler), then the checked donation, which
is seL4's `schedContext_donate` (`schedContextBindPerform`): the context names
its new thread, the thread its context, a parked thread is placed, and the
context is placed.  The donation moves the context between holders and keeps
its stack head, so the stacks and their lenders are unchanged; the flow every
lender has to the context's label is a fact about the label, not the holder.
The entry needs no premise but the store's invariant at the state it runs from.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace chainObjectsKept

theorem detachNtfnHead (st : SystemState) (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : chainObjectsKept st (_root_.SeLe4n.Kernel.detachNtfnHead st head next) := by
  unfold _root_.SeLe4n.Kernel.detachNtfnHead unlinkNtfnNeighbours clearNtfnLinks
  have h1 := updateTcb st head (fun t => { t with
    ntfnPrevCode := SeLe4n.ThreadId.optCode none,
    ntfnNextCode := SeLe4n.ThreadId.optCode none }) hInv
  have i1 := SystemState.updateTcb_preserves_objects_invExt st head (fun t => { t with
    ntfnPrevCode := SeLe4n.ThreadId.optCode none,
    ntfnNextCode := SeLe4n.ThreadId.optCode none }) hInv
  dsimp only
  split
  · exact h1.trans (updateTcb _ _ _ i1)
  · exact h1

theorem endpointQueueRemoveDual {st st' : SystemState} {e : SeLe4n.ObjId} {isRecv : Bool}
    {t : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.endpointQueueRemoveDual e isRecv t st = .ok ((), st')) :
    chainObjectsKept st st' :=
  endpointQueueRemoveDual_carry (P := fun s => chainObjectsKept st s) e isRecv t st st'
    (fun _ _ _ _ _ hInvS hStore _ hP =>
      hP.trans (storeObject_other hInvS hStore (fun _ e => by cases e) (fun _ e => by cases e)))
    (fun _ _ _ _ _ _ hInvS hStore hP => hP.trans (storeTcbQueueLinks hInvS hStore))
    hInv h (refl st)

/-- **The signal**: the bound receiver's or the head waiter's wake, or the
notification's badge. -/
theorem notificationSignalBoundOnCore (n : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) :
    chainObjectsKept st (_root_.SeLe4n.Kernel.notificationSignalBoundOnCore n badge c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationSignalBoundOnCore
  split
  · rename_i t epId _
    split
    · exact refl _
    · rename_i st1 hR
      have K1 := endpointQueueRemoveDual hInv hR
      have I1 := endpointQueueRemoveDual_preserves_objects_invExt _ _ _ _ _ hInv hR
      split
      · exact refl _
      · rename_i st2 hW
        exact (K1.trans (modifyTcb I1 hW)).trans (wakeThread _ t c
          (storeTcbSignalBoundWoken_preserves_objects_invExt _ _ _ _ I1 hW))
  · unfold notificationSignalOnCore
    split
    · rename_i ntfn hN
      split
      · rename_i waiter _
        dsimp only
        split
        · exact refl _
        · rename_i st' hS
          have K1 := storeObject_other hInv hS (fun _ e => by cases e) (fun _ e => by cases e)
            (objBindingShrink.ofNotification
              ((SystemState.getNotification?_eq_some_iff _ _ _).mp hN) (.inr rfl))
          have I1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS
          split
          · exact refl _
          · rename_i st'' hW
            have I2 := storeTcbSignalWoken_preserves_objects_invExt _ _ _ _ I1 hW
            exact ((K1.trans (modifyTcb I1 hW)).trans (detachNtfnHead _ waiter _ I2)).trans
              (wakeThread _ waiter c (detachNtfnHead_preserves_objects_invExt _ _ _ I2))
      · dsimp only
        split
        · exact refl _
        · rename_i st' hS
          exact storeObject_other hInv hS (fun _ e => by cases e) (fun _ e => by cases e)
            (objBindingShrink.ofNotification
              ((SystemState.getNotification?_eq_some_iff _ _ _).mp hN) (.inr rfl))
    · split <;> exact refl _

end chainObjectsKept

namespace LendersStep

/-- **seL4's `schedContext_donate`** as a labelled step: the context names its
new thread and the thread its context, a creating write whose label equation
(`hL`, the thread labelled as the context) each caller proves. -/
theorem schedContextBindPerform {ctx : LabelingContext} (st : SystemState)
    (vScId : SeLe4n.ValidObjId) (vTid : SeLe4n.ValidThreadId) (hInv : st.objects.invExt)
    (hL : ctx.threadLabelOf vTid.val = ctx.objectLabelOf vScId.val) :
    LendersStep ctx st (SchedContextOps.schedContextBindPerform st vScId vTid) := by
  unfold SchedContextOps.schedContextBindPerform
  split
  · exact refl hInv
  rename_i sc hSc _
  split
  · exact refl hInv
  have hTcbW : ∀ s : SystemState, s.objects.invExt → LendersStep ctx s
      (s.updateTcb vTid.val fun t => { t with
        scBindingScCode := SchedContextBinding.scCode
          (SchedContextBinding.bound (⟨vScId.val.toNat⟩ : SeLe4n.SchedContextId)),
        scBindingOwnerCode := 0 }) := fun s h =>
    updateTcb_grow s _ _ h
      (fun _ s0 _ hs => by
        simp only [SchedContextBinding.scCode] at hs
        rw [schedContextId_eq_of_succ (a := (⟨vScId.val.toNat⟩ : SeLe4n.SchedContextId)) hs]
        exact hL)
      (fun _ _ _ _ _ ho => by simp at ho)
  have hThr : ∀ t : SeLe4n.ThreadId, SeLe4n.ThreadId.optCode (some vTid.val) = t.val + 1 →
      ctx.threadLabelOf t = ctx.objectLabelOf (SeLe4n.SchedContextId.ofObjId vScId.val).toObjId := by
    intro t ht
    simp only [SeLe4n.ThreadId.optCode] at ht
    rw [threadId_eq_of_succ ht]; exact hL
  refine LendersStep.andThen ?_ fun h => of_frame (LendersFrame.releasePlace _ _ _ h)
  split
  · refine ((LendersStep.andThen ?_ fun h => hTcbW _ h).andThen
      fun h => of_frame (LendersFrame.runEnqueueOnCore _ _ _ _ h)).andThen
        fun h => of_frame (LendersFrame.withScheduler _ _ h)
    exact rewriteObject_schedContext_grow hSc _ (by exact LendersFrame.releaseReadyHead_scReply sc _)
      _ hInv hThr
  · refine LendersStep.andThen ?_ fun h => hTcbW _ h
    exact rewriteObject_schedContext_grow hSc _ (by exact LendersFrame.releaseReadyHead_scReply sc _)
      _ hInv hThr

/-- **seL4-MCS `maybeDonateSchedContext`**: the notification's context bound to
the woken thread, given the thread is labelled as that context. -/
theorem maybeDonateSchedContext {ctx : LabelingContext} (st : SystemState) (n : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hL : ∀ s, notificationContext? st n = some s →
      ctx.threadLabelOf t = ctx.objectLabelOf s.toObjId) :
    LendersStep ctx st (_root_.SeLe4n.Kernel.maybeDonateSchedContext st n t) := by
  rcases maybeDonateSchedContext_cases st n t with h | ⟨vS, vT, hT, ⟨ntfn, s, hN, hS, hV⟩, -, h⟩
  · rw [h]; exact refl hInv
  · rw [h]
    refine schedContextBindPerform st vS vT hInv ?_
    rw [hT, ← hV]
    exact hL s (by simp only [notificationContext?, hN, Option.bind_some, hS])

/-- **The checked donation**: the check is the label equation. -/
theorem maybeDonateSchedContextFlowing {ctx : LabelingContext} (st : SystemState)
    (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    LendersStep ctx st (_root_.SeLe4n.Kernel.maybeDonateSchedContextFlowing ctx st n t) := by
  unfold _root_.SeLe4n.Kernel.maybeDonateSchedContextFlowing
  split
  · rename_i hF
    refine maybeDonateSchedContext st n t hInv fun s hs => ?_
    unfold donationContextFlows at hF
    rw [hs] at hF
    exact ((twoWayLabelGate_iff_eq _ _).mp hF).symm
  · exact refl hInv

end LendersStep

namespace LendersStep

/-- **The checked signal** (seL4 `sendSignal` with the checked lend): the wake,
then the checked donation to the woken thread, whose check is its label
equation. -/
theorem sendSignalOnCoreFlowing (ctx : LabelingContext) (n : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (c : CoreId) (st : SystemState) (hInv : st.objects.invExt) :
    LendersStep ctx st (_root_.SeLe4n.Kernel.sendSignalOnCoreFlowing ctx n badge c st).1 := by
  have W : LendersFrame st (_root_.SeLe4n.Kernel.notificationSignalBoundOnCore n badge c st).1 :=
    ⟨(chainObjectsKept.notificationSignalBoundOnCore n badge c st hInv).linksShrink,
     notificationSignalBoundOnCore_preserves_objects_invExt n badge c st hInv⟩
  unfold _root_.SeLe4n.Kernel.sendSignalOnCoreFlowing
  generalize _root_.SeLe4n.Kernel.notificationSignalBoundOnCore n badge c st = r at W
  obtain ⟨st1, res⟩ := r
  cases res with
  | error _ => exact of_frame W
  | ok _ =>
    dsimp only
    unfold donateToSignalledFlowing
    split
    · exact (of_frame W).andThen fun h => maybeDonateSchedContextFlowing _ n _ h
    · exact of_frame W

end LendersStep

/-- The interrupt's step: the bound signal and the checked donation, then the
mask; the donation's check is its label equation, under the entry's context. -/
theorem LendersStep.interruptEntryStep (ctx : LabelingContext) (st : SystemState)
    (coreId intId : UInt64) (hInv : st.objects.invExt) :
    LendersStep ctx st (_root_.SeLe4n.Kernel.interruptEntryStep ctx st coreId intId) :=
  interruptEntryStep_of (P := LendersStep ctx st) ctx st coreId intId (.refl hInv) fun c _ _ =>
    handleInterruptOnCore_of (P := LendersStep ctx st) ctx st c _
      (fun _ h => h.andThen fun hI => LendersStep.of_frame
        (LendersFrame.of_kept (chainObjectsKept.of_objects_eq rfl) (RecordsFrame.of_objects_eq hI rfl rfl)))
      (.refl hInv)
      (fun ntfn badge _ => LendersStep.sendSignalOnCoreFlowing ctx ntfn badge c st hInv)

/-- **The interrupt entry's committed state keeps the lending labels**, from the
store's invariant at the state the entry runs from, under the context the
entry's checked donation reads. -/
theorem interruptEntryState_lendersStage (ctx : LabelingContext) (coreId intId : UInt64)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (hInv : st.objects.invExt) :
    LendersStage ctx st (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        (interruptEntryStep ctx (Concurrency.saveCapturedTrapFrameAt st coreId frame) coreId intId)
        coreId) coreId))) := by
  have F1 := RecordsFrame.saveCapturedTrapFrameAt st coreId frame hInv
  have L := LendersStep.interruptEntryStep ctx _ coreId intId F1.invExt
  exact ((LendersStage.of_kept (chainObjectsKept.saveCapturedTrapFrameAt st coreId frame hInv)).trans
    L.stage).trans (LendersStage.entryTail _ coreId L.invExt)

end SeLe4n.Kernel
