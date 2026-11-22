-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Cancel
import SeLe4n.Kernel.ContextLenders.Fault
import SeLe4n.Kernel.KernelRecords.IpcReply

/-! # The reply keeps the lenders' flow

WS-SX SX8.  seL4-MCS `doReplyTransfer` and its fault form: the caller woken,
its reply frame cut out (`removeCallerReplyFrame`), the donated context
returned (`applyReplyDonationOnCore`) and the fault answered.  Every step only
removes stack links (the census sites' existing `_linksShrink` results) or
writes neither a reply object nor a context; the store's invariant is read off
the records twin (`KernelRecords/IpcReply.lean`).  No premise beyond the
store's invariant. -/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace LendersFrame

/-- A step that only shrinks the links, read with its records twin. -/
theorem of_records {st st' : SystemState} (L : contextStackLinksShrink st st')
    (R : RecordsFrame st st') : LendersFrame st st' := ⟨L, R.invExt⟩

theorem settleReturnedContext (st : SystemState) (c : CoreId) (scId : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) :
    LendersFrame st (SchedContextOps.settleReturnedContext st c scId) :=
  of_views (contextStackViewsAgree_of_objectsAgreeOffReleaseLinks
      (SchedContextOps.settleReturnedContext_agree st c scId))
    (SchedContextOps.settleReturnedContext_objects_invExt st c scId hInv)

theorem descheduleAtPlacement (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.descheduleAtPlacement st t) := by
  refine of_kept ?_ (RecordsFrame.descheduleAtPlacement st t hInv)
  unfold _root_.SeLe4n.Kernel.descheduleAtPlacement _root_.SeLe4n.Kernel.descheduleAt
  split
  · exact chainObjectsKept.removeRunnableOnCore _ _ _
  · exact chainObjectsKept.refl _

theorem popUnheldReplyHead {st st' : SystemState} {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId}
    {home : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.popUnheldReplyHead st rid target home = .ok st') :
    LendersFrame st st' := by
  rcases popUnheldReplyHead_objects_frame h with ⟨-, rfl⟩ | ⟨_, _, st1, -, -, hP, rfl⟩ |
      ⟨_, _, -, -, hS⟩
  · exact refl hInv
  · exact (of_records (returnUnheldSchedContext_linksShrink hInv hP)
      (RecordsFrame.returnUnheldSchedContext hInv hP)).andThen fun h => settleReturnedContext _ _ _ h
  · exact of_records (severUnheldSchedContext_linksShrink hInv hS)
      (RecordsFrame.severUnheldSchedContext hInv hS)

theorem returnDonatedSchedContextResolved {st st' : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.returnDonatedSchedContextResolved st serverTid scId originalOwner
      = .ok st') : LendersFrame st st' := by
  obtain ⟨_, -, hR⟩ := returnDonatedSchedContextResolved_ok_decompose h
  exact of_records (returnDonatedSchedContext_linksShrink hInv hR)
    (RecordsFrame.returnDonatedSchedContextResolved hInv h)

/-- **The reply's donation return** (seL4-MCS `reply_remove`'s context half). -/
theorem applyReplyDonationOnCore {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {targetVtid : SeLe4n.ValidThreadId} {ownerHome : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.applyReplyDonationOnCore st rid targetVtid ownerHome = .ok st') :
    LendersFrame st st' := by
  unfold _root_.SeLe4n.Kernel.applyReplyDonationOnCore at h
  dsimp only at h
  split at h
  · exact popUnheldReplyHead hInv h
  · split at h
    · split at h
      · cases h
      · rename_i st1 hRet
        cases h
        exact ((returnDonatedSchedContextResolved hInv hRet).andThen fun h =>
          settleReturnedContext _ _ _ h).andThen fun h => descheduleAtPlacement _ _ h
    · cases h

theorem removeCallerReplyFrame {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.removeCallerReplyFrame caller rid st = .ok ((), st')) :
    LendersFrame st st' :=
  of_records (removeCallerReplyFrame_linksShrink hInv h) (RecordsFrame.removeCallerReplyFrame hInv h)

/-- **The per-core reply leg** (seL4 `doReplyTransfer`): the caller written
ready, woken, unlinked from its server's waiters, and its reply frame cut out. -/
theorem endpointReplyOnCore {replier target : SeLe4n.ThreadId} {msg : IpcMessage} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.endpointReplyOnCore replier target msg c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointReplyOnCore
  split
  · exact refl hInv
  split
  · exact refl hInv
  · rename_i tcb hL
    split
    · split
      · exact refl hInv
      · rename_i st1 hS
        unfold storeTcbIpcStateAndMessage_fromTcb at hS
        revert hS
        cases hSt : SeLe4n.Model.storeObject target.toObjId
            (.tcb (TCB.setIpcState { tcb with pendingMessage := some msg } .ready)) st with
        | error _ => intro h; cases h
        | ok p =>
          obtain ⟨⟨⟩, s⟩ := p
          intro h
          have he := Except.ok.inj h
          subst he
          have I1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hSt
          have A1 : LendersFrame st s := of_shrink
            (chainObjectsKept.storeObject_other hInv hSt (fun _ e => by cases e)
              (fun _ e => by cases e)).linksShrink I1
          have A2 := A1.andThen fun h => wakeThread s target c h (fun y hy => by
            rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr
              (storeObject_objects_eq st s _ _ hInv hSt)] at hy
            cases hy; simp)
          split
          · exact A2.andThen fun h => unlinkReplyWaiterOpt _ _ _ h
          · split
            · rename_i st2 hR
              exact (A2.andThen fun h => removeCallerReplyFrame h hR).andThen fun h =>
                unlinkReplyWaiterOpt _ _ _ h
            · exact refl hInv
    · exact refl hInv

theorem endpointReplyCrossCoreDispatch {replier target : SeLe4n.ThreadId} {msg : IpcMessage}
    {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    LendersFrame st
      (_root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatch replier target msg c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatch
  have A := endpointReplyOnCore (replier := replier) (target := target) (msg := msg) (c := c) hInv
  generalize _root_.SeLe4n.Kernel.endpointReplyOnCore replier target msg c st = r at A
  obtain ⟨st1, res⟩ := r
  dsimp only at A ⊢
  cases res with
  | error _ => exact refl hInv
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact refl hInv
      | exact A
      | exact A.andThen fun h => propagatePipChainCrossCore _ _ _ _ h
      | (rename_i hD
         exact (A.andThen fun h => applyReplyDonationOnCore h hD).andThen fun h =>
           propagatePipChainCrossCore _ _ _ _ h)
      | (rename_i hD
         exact A.andThen fun h => applyReplyDonationOnCore h hD)

theorem endpointReplyCrossCoreDispatchChecked {ctx : LabelingContext}
    {replier target : SeLe4n.ThreadId} {msg : IpcMessage} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    LendersFrame st
      (_root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked ctx replier target msg c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked
  split
  · exact endpointReplyCrossCoreDispatch hInv
  · exact refl hInv

/-- The decoded fault outcome applied: a restart or an abandon. -/
theorem faultReplyApplyOnCore (st : SystemState) (t : SeLe4n.ThreadId)
    (outcome : Architecture.FaultReplyOutcome) (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.faultReplyApplyOnCore st t outcome) := by
  refine of_shrink ?_ (RecordsStep.faultReplyApplyOnCore st t outcome hInv).1.invExt
  unfold _root_.SeLe4n.Kernel.faultReplyApplyOnCore
  split
  · unfold applyFaultRestart
    exact (chainObjectsKept.updateTcb st t _ hInv).linksShrink
  · unfold faultAbandonOnCore
    exact ((chainObjectsKept.removeRunnableOnCore st t _).trans (chainObjectsKept.updateTcb _ t _
      (removeRunnableOnCore_objects_invExt st t _ hInv))).linksShrink

theorem faultReplyOnCore {replier faulted : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    LendersFrame st (_root_.SeLe4n.Kernel.faultReplyOnCore replier faulted mi regs c st).1 := by
  unfold _root_.SeLe4n.Kernel.faultReplyOnCore
  split
  · exact refl hInv
  · split
    · exact refl hInv
    · dsimp only
      have A := endpointReplyCrossCoreDispatch (replier := replier) (target := faulted)
        (msg := IpcMessage.empty) (c := c) hInv
      generalize _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatch replier faulted
        IpcMessage.empty c st = r at A
      obtain ⟨st1, res⟩ := r
      dsimp only at A ⊢
      cases res with
      | error _ => exact refl hInv
      | ok sgi =>
        dsimp only
        exact A.andThen fun h => faultReplyApplyOnCore st1 faulted _ h

/-- **The checked reply transfer** (seL4 `doReplyTransfer`): a faulted caller
through the fault reply, any other through the checked reply leg, the reply's
capability transfer and the staged frame. -/
theorem replyTransferOnCoreChecked {ctx : LabelingContext} {replier callerTid : SeLe4n.ThreadId}
    {mi : MessageInfo} {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant c
      st = .ok ((), st')) : LendersFrame st st' := by
  unfold _root_.SeLe4n.Kernel.replyTransferOnCoreChecked at h
  split at h
  · have S := faultReplyOnCore (replier := replier) (faulted := callerTid) (mi := mi)
      (regs := regs) (c := c) hInv
    generalize _root_.SeLe4n.Kernel.faultReplyOnCore replier callerTid mi regs c st = r at S h
    obtain ⟨st1, res⟩ := r
    cases res with
    | error _ => cases h
    | ok _ => cases h; exact S
  · have A := endpointReplyCrossCoreDispatchChecked (ctx := ctx) (replier := replier)
      (target := callerTid) (msg := msg) (c := c) hInv
    generalize _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked ctx replier callerTid
      msg c st = r at A h
    obtain ⟨st1, res⟩ := r
    cases res with
    | error _ => cases h
    | ok _ =>
      simp only [] at h
      cases hX : _root_.SeLe4n.Kernel.replyTransferCaps st replier callerTid grant st1 with
      | error _ => rw [hX] at h; cases h
      | ok p =>
        obtain ⟨summary, stX⟩ := p
        rw [hX] at h
        cases h
        have AX := A.andThen fun h => of_kept (chainObjectsKept.receiveTransferCaps h hX)
          (RecordsFrame.receiveTransferCaps h hX)
        exact AX.andThen fun h => of_kept (chainObjectsKept.stageDeliveredMessage _ _ _ h)
          (RecordsFrame.stageDeliveredMessage _ _ _ h)

end LendersFrame

end SeLe4n.Kernel
