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

end LendersFrame

namespace LendersStep

variable {ctx : LabelingContext}

/-- **The unheld pop at a reply's head** (seL4-MCS `reply_pop` on a context no
thread holds): the context back to the answered caller, given that caller is
labelled as the context the reply heads. -/
theorem popUnheldReplyHead {st st' : SystemState} {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId}
    {home : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.popUnheldReplyHead st rid target home = .ok st')
    (hOwner : ∀ s, replyFrameHeadContext? st rid = some s →
      ctx.threadLabelOf target = ctx.objectLabelOf s.toObjId) :
    LendersStep ctx st st' := by
  rcases popUnheldReplyHead_objects_frame h with ⟨-, rfl⟩ | ⟨s, _, st1, hH, hO, hP, rfl⟩ |
      ⟨s, _, hH, hO, hS⟩
  · exact refl hInv
  · exact (⟨fun hL => returnUnheldSchedContext_preserves_lendingLabelsEqual hInv hL
      (hOwner s hH) (replyStackOuterCaller?_labelEq hL.1 hO) hP,
      (RecordsFrame.returnUnheldSchedContext hInv hP).invExt⟩ : LendersStep ctx st st1).andThen
        fun h => of_frame (LendersFrame.settleReturnedContext _ _ _ h)
  · exact ⟨fun hL => severUnheldSchedContext_preserves_lendingLabelsEqual hInv hL hS,
      (RecordsFrame.severUnheldSchedContext hInv hS).invExt⟩

/-- The held pop (seL4-MCS `reply_pop` keeping the context with its holder): its
next owner resolved off the stack, a shrink of the owner word. -/
theorem keepDonatedSchedContextResolved {st st' : SystemState} {holder : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.keepDonatedSchedContextResolved st holder scId = .ok st') :
    LendersStep ctx st st' :=
  ⟨fun hL => keepDonatedSchedContextResolved_preserves_lendingLabelsEqual hInv hL h,
   (RecordsFrame.keepDonatedSchedContextResolved hInv h).invExt⟩

/-- The resolved return to the original owner, given its label. -/
theorem returnDonatedSchedContextResolved {st st' : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.returnDonatedSchedContextResolved st serverTid scId originalOwner
      = .ok st')
    (hOwner : ctx.threadLabelOf originalOwner = ctx.objectLabelOf scId.toObjId) :
    LendersStep ctx st st' :=
  ⟨fun hL => returnDonatedSchedContextResolved_preserves_lendingLabelsEqual hInv hL hOwner h,
   (RecordsFrame.returnDonatedSchedContextResolved hInv h).invExt⟩

/-- **The reply's donation return** (seL4-MCS `reply_remove`'s context half), a
labelled step: the context the reply heads goes back to the answered caller,
given that caller is labelled as it (the reply dispatch proves it from the
answered frame at the pre-reply state). -/
theorem applyReplyDonationOnCore {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {targetVtid : SeLe4n.ValidThreadId} {ownerHome : CoreId} {keep : Bool} {executingCore : CoreId}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.applyReplyDonationOnCore st rid targetVtid ownerHome keep executingCore
      = .ok st')
    (hOwner : ∀ s, replyFrameHeadContext? st rid = some s →
      ctx.threadLabelOf targetVtid.val = ctx.objectLabelOf s.toObjId) :
    LendersStep ctx st st' := by
  unfold _root_.SeLe4n.Kernel.applyReplyDonationOnCore at h
  dsimp only at h
  split at h
  · exact popUnheldReplyHead hInv h hOwner
  · rename_i scId holder hHH
    split at h
    · split at h
      · split at h
        · cases h
        · rename_i st1 hRet
          cases h
          have hHead := (replyFrameHeadHolder?_eq_some hHH).1
          exact ((returnDonatedSchedContextResolved hInv hRet (hOwner scId hHead)).andThen fun h =>
            of_frame (LendersFrame.settleReturnedContext _ _ _ h)).andThen fun h =>
              descheduleReturnedHolder_induct (fun a b => a.objects.invExt → LendersStep ctx a b)
                keep executingCore _ _ (fun h => refl h)
                (fun h => of_frame (LendersFrame.descheduleAtPlacement _ _ h)) h
      · exact keepDonatedSchedContextResolved hInv h
    · cases h

end LendersStep

/-- **A frame's caller carries the label of the context the frame heads**, read
across a links shrink: a context `rid` heads after the shrink is one `rid` was on
the stack of before it, and the frame's recorded caller there is a lender on
that stack. -/
theorem calledFrame_labelEq {ctx : LabelingContext} {st st1 : SystemState}
    {target : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (hL : contextLendersLabelsEqual ctx st) (hC : replyStackCaller st rid = some target)
    (hS : contextStackLinksShrink st st1) :
    ∀ s, replyFrameHeadContext? st1 rid = some s →
      ctx.threadLabelOf target = ctx.objectLabelOf s.toObjId := by
  intro s hH
  obtain ⟨_, sc, -, -, hSc, hScR⟩ := replyFrameHeadContext?_eq_some hH
  have hOn : OnContextStackView st s rid := hS.head s rid (by
    unfold contextStackHead; rw [hSc]; simp only [Option.bind_some, hScR])
  rw [contextLendersLabelsEqual_iff_views] at hL
  exact hL s rid target hOn hC

/-- **The answered caller carries the label of the context its frame heads**,
read across the reply leg: the frame `rid` the target's thread record names at
the pre-reply state records the target as its caller (the reply linkage), so
`calledFrame_labelEq` applies. -/
theorem answeredFrame_labelEq {ctx : LabelingContext} {st st1 : SystemState}
    {target : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (hL : contextLendersLabelsEqual ctx st) (hLink : replyCallerLinkageReciprocal st)
    (hA : answeredReplyObject? st target = some rid) (hS : contextStackLinksShrink st st1) :
    ∀ s, replyFrameHeadContext? st1 rid = some s →
      ctx.threadLabelOf target = ctx.objectLabelOf s.toObjId := by
  refine calledFrame_labelEq hL ?_ hS
  unfold answeredReplyObject? at hA
  cases hT : st.getTcb? target with
  | none => rw [hT] at hA; cases hA
  | some tcb =>
    rw [hT] at hA
    obtain ⟨r, hR, hC⟩ := hLink.1 target tcb rid ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hA
    rw [replyStackCaller_eq_obj, hR]; exact hC

namespace LendersStep

variable {ctx : LabelingContext}

/-- **The cross-core reply** (seL4 `doReplyTransfer` with seL4-MCS's
`reply_remove`): the reply leg, then the donation return to the answered
caller, whose owner obligation is read at the pre-reply state through the reply
linkage (`answeredFrame_labelEq`) and carried across the reply leg's links
shrink; then the priority walk. -/
theorem endpointReplyCrossCoreDispatch {replier target : SeLe4n.ThreadId} {msg : IpcMessage}
    {c : CoreId} {st : SystemState} (hInv : st.objects.invExt)
    (hLink : replyCallerLinkageReciprocal st) (keep : Bool := false) :
    LendersStep ctx st
      (_root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatch replier target msg c st keep).1 := by
  unfold _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatch
  have A := LendersFrame.endpointReplyOnCore (replier := replier) (target := target) (msg := msg)
    (c := c) hInv
  generalize _root_.SeLe4n.Kernel.endpointReplyOnCore replier target msg c st = r at A
  obtain ⟨st1, res⟩ := r
  dsimp only at A ⊢
  have hPop : ∀ rid targetV st2, answeredReplyObject? st target = some rid →
      SeLe4n.ThreadId.toValid? target = some targetV →
      _root_.SeLe4n.Kernel.applyReplyDonationOnCore st1 rid targetV (determineTargetCore st1 target)
        keep c = .ok st2 → LendersStep ctx st st2 := fun rid targetV st2 hA hV hD =>
    ⟨fun hL => (applyReplyDonationOnCore A.invExt hD (by
        rw [SeLe4n.ThreadId.toValid?_some_val_eq _ _ hV]; exact answeredFrame_labelEq hL.1 hLink hA A.links)).stage (A.stage hL),
     (RecordsFrame.applyReplyDonationOnCore A.invExt hD).invExt⟩
  cases res with
  | error _ => exact refl hInv
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact refl hInv
      | exact of_frame A
      | exact of_frame (A.andThen fun h => LendersFrame.propagatePipChainCrossCore _ _ _ _ h)
      | (refine LendersStep.andThen ?_ fun h =>
           of_frame (LendersFrame.propagatePipChainCrossCore _ _ _ _ h)
         apply hPop <;> assumption)
      | (apply hPop <;> assumption)

theorem endpointReplyCrossCoreDispatchChecked {replier target : SeLe4n.ThreadId} {msg : IpcMessage}
    {c : CoreId} {st : SystemState} (hInv : st.objects.invExt)
    (hLink : replyCallerLinkageReciprocal st) (keep : Bool := false) :
    LendersStep ctx st
      (_root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked ctx replier target msg c st
        keep).1 := by
  unfold _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked
  split
  · exact endpointReplyCrossCoreDispatch hInv hLink keep
  · exact refl hInv

theorem faultReplyOnCore {replier faulted : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt)
    (hLink : replyCallerLinkageReciprocal st) (keep : Bool := false) :
    LendersStep ctx st
      (_root_.SeLe4n.Kernel.faultReplyOnCore replier faulted mi regs c st keep).1 := by
  unfold _root_.SeLe4n.Kernel.faultReplyOnCore
  split
  · exact refl hInv
  · split
    · exact refl hInv
    · dsimp only
      have A := endpointReplyCrossCoreDispatch (ctx := ctx) (replier := replier) (target := faulted)
        (msg := IpcMessage.empty) (c := c) hInv hLink keep
      generalize _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatch replier faulted
        IpcMessage.empty c st keep = r at A
      obtain ⟨st1, res⟩ := r
      dsimp only at A ⊢
      cases res with
      | error _ => exact refl hInv
      | ok sgi =>
        dsimp only
        exact A.andThen fun h => of_frame (LendersFrame.faultReplyApplyOnCore st1 faulted _ h)

/-- **The checked reply transfer** (seL4 `doReplyTransfer`): a faulted caller
through the fault reply, any other through the checked reply leg, the reply's
capability transfer and the staged frame. -/
theorem replyTransferOnCoreChecked {replier callerTid : SeLe4n.ThreadId}
    {mi : MessageInfo} {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState} (hInv : st.objects.invExt)
    (hLink : replyCallerLinkageReciprocal st) {keep : Bool}
    (h : _root_.SeLe4n.Kernel.replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant c
      st keep = .ok ((), st')) : LendersStep ctx st st' := by
  unfold _root_.SeLe4n.Kernel.replyTransferOnCoreChecked at h
  split at h
  · have S := faultReplyOnCore (ctx := ctx) (replier := replier) (faulted := callerTid) (mi := mi)
      (regs := regs) (c := c) hInv hLink keep
    generalize _root_.SeLe4n.Kernel.faultReplyOnCore replier callerTid mi regs c st keep = r at S h
    obtain ⟨st1, res⟩ := r
    cases res with
    | error _ => cases h
    | ok _ => cases h; exact S
  · have A := endpointReplyCrossCoreDispatchChecked (ctx := ctx) (replier := replier)
      (target := callerTid) (msg := msg) (c := c) hInv hLink keep
    generalize _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked ctx replier callerTid
      msg c st keep = r at A h
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
        exact (A.andThen fun h => of_frame (LendersFrame.of_kept (chainObjectsKept.receiveTransferCaps h hX)
          (RecordsFrame.receiveTransferCaps h hX))).andThen fun h => of_frame
            (LendersFrame.of_kept (chainObjectsKept.stageDeliveredMessage _ _ _ h)
              (RecordsFrame.stageDeliveredMessage _ _ _ h))

end LendersStep

end SeLe4n.Kernel
