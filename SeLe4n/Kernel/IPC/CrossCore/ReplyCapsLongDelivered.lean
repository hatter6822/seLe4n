-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.ReplyCapsReturnDelivered

/-!
# A long reply that transfers capabilities, delivered in place

seL4's `doReplyTransfer` runs `doIPCTransfer` whatever the message's length:
`transferCaps`, then the inline words and the words the replier's IPC buffer
holds past them.  A reply of more than four words to a caller the reply wakes
in place (`performReplyDeliveredLong`), on a donated reply object or to a
caller recording no server writes its own state in place; here the transfer
runs in place after those writes (`capTransferK`, on no endpoint) and the long
frame is written last with the transfer's report (`deliverLongCapsFrame`).  The
count is the replier's frame's, under the grant right, and none without it, so
the same writer answers a reply whose transfer moves nothing.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood
open Architecture.RegisterDecode

/-- The long reply's message: the replier's inline words, then its overflow
words, with the badge of the capability it replies on. -/
abbrev longReplyMessage (st : SystemState) (replier : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool) :
    IpcMessage :=
  longSendMessage SeLe4n.arm64DefaultLayout rf st replier len (SeLe4n.Badge.opt badgeWord badged)

/-- The capability transfer and long frame on the state `X` a reply's own
writes left, the replier and the caller entering as the words the transfer
reads of them. -/
@[inline] def replyCapsLongTail (X : SystemState) (c replier : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverLongCapsFrame
      (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
      c SeLe4n.arm64DefaultLayout rf len replier badgeWord badged

/-- **The long reply that transfers capabilities, delivered**: the caller woken
without the message, the server's priority walk, the transfer in place on no
endpoint, then the long frame with the transfer's report. -/
@[noinline] def performReplyCapsDeliveredLong (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (rf : SeLe4n.RegisterFile) (len : Nat) (replier : SeLe4n.ThreadId)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  replyCapsLongTail (PriorityInheritance.propagatePipChainCrossCore
      (storeReplyRendezvousReady st c server rid) server core).1
    c replier rf len badgeWord badged sv sb sroot count rv rb rroot

/-- **The long donated reply that transfers capabilities, delivered**: the
caller woken without the message, the loaned context handed back down the stack
in place, the server's priority walk, the transfer, then the long frame. -/
@[noinline] def performReplyDonatedCapsDeliveredLong (st : SystemState)
    (c server : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId)
    (home : Concurrency.CoreId) (rf : SeLe4n.RegisterFile) (len : Nat)
    (replier : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (core : Concurrency.CoreId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  replyCapsLongTail (PriorityInheritance.propagatePipChainCrossCore
      (replyDonationPopInPlace (storeReplyRendezvousReady st c server rid) c server scId home)
      server core).1
    c replier rf len badgeWord badged sv sb sroot count rv rb rroot

/-- **The long reply to a caller recording no server that transfers
capabilities, delivered**: the caller woken without the message, the context no
thread holds handed back to it and settled on its home, the transfer, then the
long frame. -/
@[noinline] def performReplyUnheldCapsDeliveredLong (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : Concurrency.CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (replier : SeLe4n.ThreadId)
    (badgeWord : SeLe4n.Badge) (badged : Bool)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  replyCapsLongTail (SchedContextOps.settleReturnedContext
      (returnUnheldSchedContextInPlace (storeReplyLegReady st c rid) c scId) home scId)
    c replier rf len badgeWord badged sv sb sroot count rv rb rroot

/-- What a routed long reply or reply-receive pins about its length. -/
theorem routedReplyLong_length (st : SystemState) (replier : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (bw : SeLe4n.Badge) (bd : Bool)
    (hR : (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr mi ∧
        sid = .reply) ∨
      (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyRecvLong capAddr mi ∧
        sid = .replyRecv)) :
    4 ≤ mi.length ∧
      ¬ (longReplyMessage st replier rf mi.length bw bd).registers.size > maxMessageRegisters := by
  obtain ⟨hGt, hMax, -⟩ := decodeSyscallArgsFromState_of_routedReplyLongAny st replier rf capAddr
    mi sid (by rcases hR with h | h; exact .inl h; exact .inr (.inl h))
  have hSz4 : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz4] at hGt
  refine ⟨by omega, ?_⟩
  rw [longSendMessage_size _ _ _ _ _ _ hSz4 (by omega)]
  omega

/-- **The checked long reply that transfers capabilities, in place**: under
the flow gate and `replyWakesInPlace`, a reply of more than four words to an
unfaulted caller blocked on it, from a replier whose frame routes as a long
reply or reply-receive with every overflow slot reading, commits
`performReplyCapsDeliveredLong`'s state. -/
theorem replyTransferChecked_capsLong_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c server : SeLe4n.ThreadId) (ct stcb : TCB) (ep : SeLe4n.ObjId)
    (rid : SeLe4n.ReplyId) (mi' : MessageInfo) (regs : Array SeLe4n.RegValue)
    (rf : SeLe4n.RegisterFile) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (core : Concurrency.CoreId) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (g : Bool)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hSRes : server.isReserved = false)
    (hG : replyWakesInPlace st c ct rid = true)
    (hNoF : ct.faultWords.isFault = false)
    (hFlow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf c) = true)
    (hS : st.getTcb? replier = some stcb) (hRf : stcb.registerContext = rf)
    (hR : (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr mi ∧
        sid = .reply) ∨
      (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyRecvLong capAddr mi ∧
        sid = .replyRecv))
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st replier j = .ok w) :
    replyTransferOnCoreChecked ctx replier c mi' regs
        (longReplyMessage st replier rf mi.length badgeWord badged) g core st =
      .ok ((), performReplyCapsDeliveredLong st c server rid rf mi.length replier badgeWord
        badged core stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
        (if g then routedExtraCaps rf else 0) ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot) := by
  obtain ⟨hLen, hSz'⟩ := routedReplyLong_length st replier rf capAddr mi sid badgeWord badged hR
  have hPF : ct.pendingFault = none := TCB.pendingFault_eq_none_of_not_isFault hNoF
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNF : threadHasPendingFault st c = false := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_none]
  obtain ⟨sgi, hD⟩ := replyDispatch_inPlace st replier c server ct ep rid
    (longReplyMessage st replier rf mi.length badgeWord badged) core hSz' hT hIpc hRO hSRes hG
  have hNo := replyWakesInPlace_noResizeDue hG
  have hNoS := storeReplyRendezvousReady_noResizeDue st c server rid hNo
  have hA := (ipcBufferReadsAgree_propagatePipChainCrossCore _ server core hNoS).trans
    (ipcBufferReadsAgree_storeReplyRendezvousReady st c server rid hNo)
  unfold replyTransferOnCoreChecked
  rw [hNF, endpointReplyCrossCoreDispatchChecked_flow_allowed _ _ _ _ _ _ hFlow]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hD]
  simp only []
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  unfold replyTransferCaps
  rw [replyCapRequest_of_routedReplyLong st replier stcb rf capAddr mi sid g hS hRf hR hRead, hTgt]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoS]
  unfold performReplyCapsDeliveredLong replyCapsLongTail
  exact replyHeldCapsLong_eq_delivered st _ c replier rf mi.length badgeWord badged stcb ct _
    (propagatePipChainCrossCore_noResizeDue _ server core hNoS) hA hLen

/-- **The checked long donated reply that transfers capabilities, in place**:
as `replyTransferChecked_donatedCaps_inPlace`, for a reply of more than four
words from a replier whose frame routes as a long reply or reply-receive with
every overflow slot reading, under either grant right. -/
theorem replyTransferChecked_donatedCapsLong_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c server : SeLe4n.ThreadId) (ct stcb : TCB) (ep : SeLe4n.ObjId)
    (rid : SeLe4n.ReplyId) (mi' : MessageInfo) (regs : Array SeLe4n.RegValue)
    (rf : SeLe4n.RegisterFile) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (core : Concurrency.CoreId) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (g : Bool)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hSRes : server.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode server rid = true)
    (hNoF : ct.faultWords.isFault = false)
    (hFlow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf c) = true)
    (hS : st.getTcb? replier = some stcb) (hRf : stcb.registerContext = rf)
    (hR : (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr mi ∧
        sid = .reply) ∨
      (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyRecvLong capAddr mi ∧
        sid = .replyRecv))
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st replier j = .ok w) :
    replyTransferOnCoreChecked ctx replier c mi' regs
        (longReplyMessage st replier rf mi.length badgeWord badged) g core st =
      .ok ((), performReplyDonatedCapsDeliveredLong st c server rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) rf mi.length replier
        badgeWord badged core stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
        (if g then routedExtraCaps rf else 0) ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot) := by
  obtain ⟨rp, scId, _, hRp, hN, _, _, _, hCode, hCRes, hNe, hNo, hLC, hFC, hLR, hFR, hDon, _⟩ :=
    replyPopsInPlace_donation st c server rid (longReplyMessage st replier rf mi.length badgeWord badged) ct hT hSRes hG
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  obtain ⟨hLen, hSz'⟩ := routedReplyLong_length st replier rf capAddr mi sid badgeWord badged hR
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st replier c server ct ep rid rp _ core hSz' hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hPF : ct.pendingFault = none := TCB.pendingFault_eq_none_of_not_isFault hNoF
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNF : threadHasPendingFault st c = false := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_none]
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hCRes)
  obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff server).mpr hSRes)
  have hRec : recordedReplyServer? st c = some server := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hAns : answeredReplyObject? st c = some rid := by
    simp only [answeredReplyObject?, hTc, Option.bind_some, hRO]
  have hNoS := storeReplyRendezvousReady_noResizeDue st c server rid hNo
  have hNoP := replyDonationPopInPlace_noResizeDue _ c server scId (determineTargetCore st c) hNoS
  have hAX := (ipcBufferReadsAgree_propagatePipChainCrossCore _ server core hNoP).trans
    ((ipcBufferReadsAgree_replyDonationPopInPlace _ c server scId (determineTargetCore st c)
      hNoS).trans (ipcBufferReadsAgree_storeReplyRendezvousReady st c server rid hNo))
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  unfold replyTransferOnCoreChecked
  rw [hNF, endpointReplyCrossCoreDispatchChecked_flow_allowed _ _ _ _ _ _ hFlow]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hsv, hAns, hcv]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    hDon cv (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
  simp only []
  rw [replyDonationPopInPlace_msg c id _ id _ c server scId _ hNoS hNe,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoP]
  unfold replyTransferCaps
  rw [replyCapRequest_of_routedReplyLong st replier stcb rf capAddr mi sid g hS hRf hR hRead, hTgt]
  unfold performReplyDonatedCapsDeliveredLong replyCapsLongTail
  exact replyHeldCapsLong_eq_delivered st _ c replier rf mi.length badgeWord badged stcb ct _
    (propagatePipChainCrossCore_noResizeDue _ _ _ hNoP) hAX hLen

/-- **The checked long reply to a caller recording no server that transfers
capabilities, in place**: as `replyTransferChecked_unheldCaps_inPlace`, for a
reply of more than four words routed as `replyTransferChecked_capsLong_inPlace`'s,
under either grant right. -/
theorem replyTransferChecked_unheldCapsLong_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c : SeLe4n.ThreadId) (ct stcb : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (mi' : MessageInfo) (regs : Array SeLe4n.RegValue)
    (rf : SeLe4n.RegisterFile) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (core : Concurrency.CoreId) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (g : Bool)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hNoF : ct.faultWords.isFault = false)
    (hFlow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf c) = true)
    (hS : st.getTcb? replier = some stcb) (hRf : stcb.registerContext = rf)
    (hR : (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr mi ∧
        sid = .reply) ∨
      (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyRecvLong capAddr mi ∧
        sid = .replyRecv))
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st replier j = .ok w) :
    replyTransferOnCoreChecked ctx replier c mi' regs
        (longReplyMessage st replier rf mi.length badgeWord badged) g core st =
      .ok ((), performReplyUnheldCapsDeliveredLong st c rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) rf mi.length replier badgeWord badged stcb.vspaceRoot
        stcb.ipcBuffer stcb.cspaceRoot (if g then routedExtraCaps rf else 0) ct.vspaceRoot
        ct.ipcBuffer ct.cspaceRoot) := by
  obtain ⟨rp, scId, hRp, hN, hCode, hCRes, hNo, hLC, hFC, hLR, hFR, -, hPop⟩ :=
    replyUnheldPopsInPlace_pop st c rid (longReplyMessage st replier rf mi.length badgeWord badged) ct hT hG
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  obtain ⟨hLen, hSz'⟩ := routedReplyLong_length st replier rf capAddr mi sid badgeWord badged hR
  obtain ⟨hEq, _⟩ := replyOnCore_eq_storeLeg st replier c none ct ep rid rp _ core hSz' hT hIpc
    hRO hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hPF : ct.pendingFault = none := TCB.pendingFault_eq_none_of_not_isFault hNoF
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNF : threadHasPendingFault st c = false := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_none]
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hCRes)
  have hRec : recordedReplyServer? st c = none := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hAns : answeredReplyObject? st c = some rid := by
    simp only [answeredReplyObject?, hTc, Option.bind_some, hRO]
  have hNoS := storeReplyLegReady_noResizeDue st c rid hNo
  have hNoP := returnUnheldSchedContextInPlace_noResizeDue _ c scId hNoS
  have hNoQ := settleReturnedContext_noResizeDue _ (determineTargetCore st c) scId hNoP
  have hAX := (ipcBufferReadsAgree_settleReturnedContext _ (determineTargetCore st c) scId).trans
    ((ipcBufferReadsAgree_returnUnheldSchedContextInPlace _ c scId hNoS).trans
      (ipcBufferReadsAgree_storeReplyLegReady st c rid hNo))
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  unfold replyTransferOnCoreChecked
  rw [hNF, endpointReplyCrossCoreDispatchChecked_flow_allowed _ _ _ _ _ _ hFlow]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hAns, hcv, SystemState.unlinkReplyWaiterOpt]
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo, hPop cv (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
  simp only []
  rw [returnUnheldSchedContextInPlace_msg c id _ id _ c scId hNoS, settleReturnedContext_msg]
  unfold replyTransferCaps
  rw [replyCapRequest_of_routedReplyLong st replier stcb rf capAddr mi sid g hS hRf hR hRead, hTgt]
  unfold performReplyUnheldCapsDeliveredLong replyCapsLongTail
  exact replyHeldCapsLong_eq_delivered st _ c replier rf mi.length badgeWord badged stcb ct _ hNoQ
    hAX hLen

end SeLe4n.Kernel
