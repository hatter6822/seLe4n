-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.FaultInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyUnheldPopFrame

/-!
# A fault answered in place, on every reply shape

A faulted caller is answered with its fault reply: `decodeFaultReply` of the
handler's label and words against the fault it carries, then
`faultReplyApplyOnCore` (restart or abandon, the record cleared).  The `.reply`
arm does it after the reply's writes (`faultReplyOnCore`); a fault handler's
server loop answers with `ReplyRecv`, whose transition
(`replyRecvTransferOnCore`) runs the reply leg with the empty message and the
receive leg unchanged, and answers the caller in place of staging a message.

Both arms apply one answer, read from words (`performFaultAnswer`,
`FaultInPlace.lean`): the caller's fault kind and saved context off its TCB on
the pre-state, the reply's label and words off the register file.  This file
composes it with each arm's in-place legs on the shapes the arms already write
in place, and proves each composite the specification's:

* `.replyRecv` blocking on the endpoint after any reply arm
  (`performReplyRecvArmFaultAnswer`, `ReplyRecvBlockComposed.lean`), built on
  the fault reply leg here (`storeFaultReplyLeg`);
* `.reply` on a donated reply (`performFaultReplyDonatedAnswer`,
  `faultReplyTransferChecked_donated_inPlace`) and to a caller recording no
  server (`performFaultReplyUnheldAnswer`,
  `faultReplyTransferChecked_unheld_inPlace`); its rendezvous form is
  `performFaultReplyAnswer` (`FaultInPlace.lean`).

None builds the fault record, the reply's message, the outcome or a frame.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- A reply-receive's words (WS-SX SX7.3: the whole message, MR0 onward, since
the reply capability is named by the reply register) are the layout's. -/
theorem wordAt_regMessageBody (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len i : Nat)
    (h : i < Architecture.regMessageLength layout len) :
    Architecture.wordAt (Architecture.regMessageBody layout rf len) i =
      Architecture.regLayoutWord layout rf i := by
  rw [← Architecture.regMessageWord_eq_regLayoutWord layout rf len i h,
    ← Architecture.regMessageBody_word]
  unfold Architecture.wordAt Architecture.wordOf
  cases (Architecture.regMessageBody layout rf len)[i]? <;> rfl

/-- The answer a reply-receive owes a caller carrying fault `tf`. -/
theorem replyRecvCallerFaultAnswer?_of_fault (st : SystemState) (c : SeLe4n.ThreadId)
    (ct : TCB) (tf : ThreadFault) (label : Nat) (msg : IpcMessage)
    (hT : st.getTcb? c = some ct) (hPF : ct.pendingFault = some tf) :
    replyRecvCallerFaultAnswer? st c label msg =
      some (Architecture.decodeFaultReply tf.fault tf.context
        { length := msg.registers.size, extraCaps := 0, label := label } msg.registers) := by
  unfold replyRecvCallerFaultAnswer?
  rw [hT]
  simp only [hPF]

/-- The reply leg's writes with no message to a caller recording no server
(`storeReplyLeg` at `IpcMessage.empty`), written out as
`storeFaultReplyRendezvous` is, so the empty message the woken thread holds is
the one constant cell (`storeFaultReplyLeg_eq`). -/
@[noinline] def storeFaultReplyLeg (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : SystemState :=
  let s1 := st.updateTcb c faultReplyReceiverTcb
  let s2 := enqueueRunnableOnCore s1 (determineTargetCore s1 c) c
  (s2.modifyObject rid.toObjId replyConsumedObject).updateTcb c
    (fun t => { t with replyObjectCode := 0 })

theorem storeFaultReplyLeg_eq (st : SystemState) (c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) :
    storeFaultReplyLeg st c rid = storeReplyLeg st c rid IpcMessage.empty := rfl

/-- The fault reply's leg keeps the donation chain: it is `storeReplyLeg` at
the empty message (`storeFaultReplyLeg_eq`), whose chain theorem it inherits. -/
theorem storeFaultReplyLeg_preserves_donationChainWellFormed (st : SystemState)
    (c : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (core : Concurrency.CoreId)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep none)
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true)
    (hObjInv : st.objects.invExt) (hChain : donationChainWellFormed st) :
    donationChainWellFormed (storeFaultReplyLeg st c rid) := by
  rw [storeFaultReplyLeg_eq]
  exact storeReplyLeg_preserves_donationChainWellFormed st c ct ep rid IpcMessage.empty core
    (by simp [IpcMessage.empty]) hT hIpc hRO hG hObjInv hChain

/-- **The donated reply's fault answer, in place**: the reply's writes with no
message, the loaned context handed back down the stack in place
(`replyDonationPopInPlace`, settled on the caller's home `home`), the server's
priority walk, then the fault answer (`performFaultAnswer`). -/
@[noinline] def performFaultReplyDonatedAnswer (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (core : CoreId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (n : Nat)
    (keepCurrent : Bool := false) : SystemState :=
  performFaultAnswer (PriorityInheritance.propagatePipChainCrossCore
      (replyDonationPopInPlace (storeFaultReplyRendezvous st c server rid) c server scId home
        keepCurrent core)
      server core).1 c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n 0

/-- **The checked donated fault reply, in place**: under `replyPopsInPlace`, a
reply to a faulted caller blocked on it, whose reply object heads the stack of
the context the server holds on loan, commits `performFaultReplyDonatedAnswer`'s
state. -/
theorem faultReplyTransferChecked_donated_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c server : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (mi : MessageInfo) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (msg : IpcMessage) (grant : Bool) (core : CoreId)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hSRes : server.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode server rid = true)
    (hF : ct.faultWords.isFault = true)
    (keep : Bool := false) :
    replyTransferOnCoreChecked ctx replier c mi (Architecture.regMessageRegs layout rf) msg grant core
        st keep =
      .ok ((), performFaultReplyDonatedAnswer st c server rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) core ct.faultKind mi.label ct.faultIp ct.faultSp ct.faultLr
        ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7
        layout rf (min mi.length layout.msgRegs.size) keep) := by
  obtain ⟨rp, scId, _, hRp, hN, _, _, _, hCode, hCRes, hNe, hNo, hLC, hFC, hLR, hFR, hDon, _⟩ :=
    replyPopsInPlace_donation st c server rid IpcMessage.empty ct hT hSRes hG
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st replier c server ct ep rid rp IpcMessage.empty core
    (by simp [IpcMessage.empty]) hT hIpc hRO hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨tf, hPF⟩ : ∃ tf, ct.pendingFault = some tf :=
    Option.isSome_iff_exists.mp (by rw [TCB.pendingFault_isSome]; exact hF)
  have hHas : threadHasPendingFault st c = true := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_some]
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hCRes)
  obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff server).mpr hSRes)
  have hRec : recordedReplyServer? st c = some server := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hAns : answeredReplyObject? st c = some rid := by
    simp only [answeredReplyObject?, hTc, Option.bind_some, hRO]
  unfold replyTransferOnCoreChecked
  rw [hHas]
  simp only [↓reduceIte]
  unfold faultReplyOnCore
  rw [hTc]
  simp only [hPF]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hsv, hAns, hcv]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    hDon keep core cv (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
  simp only []
  unfold performFaultReplyDonatedAnswer
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswer _ c ct tf hPF mi _ layout rf
    (min mi.length layout.msgRegs.size) 0
    (by simp only [Architecture.regMessageRegs, Array.size_map])
    (fun i _ => wordAt_regMessageRegs layout rf i),
    storeFaultReplyRendezvous_eq, storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]

/-- **The fault answer to a caller recording no server, in place**: the reply
leg's writes with no message, the context its reply object heads handed to it in
place (`returnUnheldSchedContextInPlace`, settled on its home `home`), then the
fault answer (`performFaultAnswer`).  No server's boost to revert: none is
recorded. -/
@[noinline] def performFaultReplyUnheldAnswer (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (n : Nat) : SystemState :=
  performFaultAnswer (SchedContextOps.settleReturnedContext
      (returnUnheldSchedContextInPlace (storeFaultReplyLeg st c rid) c scId) home scId) c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n 0

/-- **The checked fault reply to a caller recording no server, in place**: under
`replyUnheldPopsInPlace`, a reply to a faulted caller blocked on it with no
server recorded commits `performFaultReplyUnheldAnswer`'s state. -/
theorem faultReplyTransferChecked_unheld_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (mi : MessageInfo) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (msg : IpcMessage) (grant : Bool) (core : CoreId)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hF : ct.faultWords.isFault = true)
    (keep : Bool := false) :
    replyTransferOnCoreChecked ctx replier c mi (Architecture.regMessageRegs layout rf) msg grant core
        st keep =
      .ok ((), performFaultReplyUnheldAnswer st c rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) ct.faultKind mi.label ct.faultIp ct.faultSp ct.faultLr
        ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7
        layout rf (min mi.length layout.msgRegs.size)) := by
  obtain ⟨rp, scId, hRp, hN, hCode, hCRes, hNo, hLC, hFC, hLR, hFR, -, hPop⟩ :=
    replyUnheldPopsInPlace_pop st c rid IpcMessage.empty ct hT hG
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  obtain ⟨hEq, _⟩ := replyOnCore_eq_storeLeg st replier c none ct ep rid rp IpcMessage.empty core
    (by simp [IpcMessage.empty]) hT hIpc hRO hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨tf, hPF⟩ : ∃ tf, ct.pendingFault = some tf :=
    Option.isSome_iff_exists.mp (by rw [TCB.pendingFault_isSome]; exact hF)
  have hHas : threadHasPendingFault st c = true := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_some]
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hCRes)
  have hRec : recordedReplyServer? st c = none := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hAns : answeredReplyObject? st c = some rid := by
    simp only [answeredReplyObject?, hTc, Option.bind_some, hRO]
  unfold replyTransferOnCoreChecked
  rw [hHas]
  simp only [↓reduceIte]
  unfold faultReplyOnCore
  rw [hTc]
  simp only [hPF]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hAns, hcv, SystemState.unlinkReplyWaiterOpt]
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo, hPop keep core cv (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
  simp only []
  unfold performFaultReplyUnheldAnswer
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswer _ c ct tf hPF mi _ layout rf
    (min mi.length layout.msgRegs.size) 0
    (by simp only [Architecture.regMessageRegs, Array.size_map])
    (fun i _ => wordAt_regMessageRegs layout rf i),
    storeFaultReplyLeg_eq, storeReplyLeg_eq_hold _ _ _ _ hNo]

/-- **The fault answer to a caller recording no server, its reply object linked
to nothing, in place** (WS-SX SX8.3): the reply leg's writes with no message,
then the fault answer (`performFaultAnswer`).  No context to hand back (the
reply object heads none, as seL4's `reply_remove` finds it once a lent context
was let go of by `schedContext_unbindReply`) and no server's boost to revert. -/
@[noinline] def performFaultReplyUnlinkedAnswer (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (n : Nat) : SystemState :=
  performFaultAnswer (storeFaultReplyLeg st c rid) c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7
    layout rf n 0

/-- **The checked fault reply to a caller recording no server, its reply object
linked to nothing, in place**: under `replyUnlinkedInPlace`, a reply to a
faulted caller blocked on it with no server recorded commits
`performFaultReplyUnlinkedAnswer`'s state. -/
theorem faultReplyTransferChecked_unlinked_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (mi : MessageInfo) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (msg : IpcMessage) (grant : Bool) (core : CoreId)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnlinkedInPlace st c rid = true)
    (hF : ct.faultWords.isFault = true)
    (keep : Bool := false) :
    replyTransferOnCoreChecked ctx replier c mi (Architecture.regMessageRegs layout rf) msg grant core
        st keep =
      .ok ((), performFaultReplyUnlinkedAnswer st c rid ct.faultKind mi.label ct.faultIp ct.faultSp
        ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6
        ct.faultX7 layout rf (min mi.length layout.msgRegs.size)) := by
  have hNo := replyWakesInPlace_noResizeDue ((replyUnlinkedInPlace_eq_wakes st c ct rid) ▸ hG)
  obtain ⟨sgi, hD⟩ := replyDispatch_unlinked_inPlace st replier c ct ep rid IpcMessage.empty core
    (by simp [IpcMessage.empty]) hT hIpc hRO hG keep
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨tf, hPF⟩ : ∃ tf, ct.pendingFault = some tf :=
    Option.isSome_iff_exists.mp (by rw [TCB.pendingFault_isSome]; exact hF)
  have hHas : threadHasPendingFault st c = true := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_some]
  unfold replyTransferOnCoreChecked
  rw [hHas]
  simp only [↓reduceIte]
  unfold faultReplyOnCore
  rw [hTc]
  simp only [hPF]
  rw [hD]
  simp only []
  unfold performFaultReplyUnlinkedAnswer
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswer _ c ct tf hPF mi _ layout rf
    (min mi.length layout.msgRegs.size) 0
    (by simp only [Architecture.regMessageRegs, Array.size_map])
    (fun i _ => wordAt_regMessageRegs layout rf i),
    storeFaultReplyLeg_eq, storeReplyLeg_eq_hold _ _ _ _ hNo]

end SeLe4n.Kernel
