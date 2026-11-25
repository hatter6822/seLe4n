-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvCapsFrame
import SeLe4n.Kernel.IPC.CrossCore.ReplyCapsLongDelivered
import SeLe4n.Kernel.IPC.CrossCore.ReplyUnheldPopFrame
import SeLe4n.Kernel.IPC.CrossCore.LongReplyRecvFrame

/-!
# The reply-receive whose reply leg transfers capabilities, in place

seL4's `handleReplyRecv` runs `doReplyTransfer` (the reply's writes, the
`reply_pop` of a donated or unheld reply object, then `doIPCTransfer` with no
endpoint, which installs the replier's extra capability in the caller's receive
slot) and then `receiveIPC`.  The specification orders the reply-receive the
same way (`endpointReplyRecvAnsweringOnCore`).  The in-place forms here run the
reply's writes (and the pop), the transfer in place (`capTransferK` with no
endpoint to unwrap at, as `performReplyCapsDelivered` runs it), the receive
leg's block and the caller's frame carrying the transfer's report.  The receive
leg's guard is read on the pre-state and carried across the transfer
(`receiveTransferCaps_reply_transferFrame`, `receiveGuard_of_transferFrame`):
every CNode the transfer writes keeps its kind, so it is written in place.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-! ### The frame with the transfer's report -/

/-- `regMessageFrame` with the transfer's report in its message-info word, the
badge given as an option (`regMessageFrameCapsW` takes it as a word and a flag). -/
@[inline] def regMessageFrameCapsOpt (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (capInfo : Nat) :
    Architecture.SyscallReturnFrame :=
  { x0 := Architecture.badgeWordOrZero badge
    x1 := regMessageInfoWordCaps layout len capInfo
    x2 := Architecture.regMessageWord layout rf len 0
    x3 := Architecture.regMessageWord layout rf len 1
    x4 := Architecture.regMessageWord layout rf len 2
    x5 := Architecture.regMessageWord layout rf len 3 }

theorem returnFrameOfMessage_regMessageBody_capsOpt (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (capInfo : Nat) :
    Architecture.returnFrameOfMessage
        { registers := Architecture.regMessageBody layout rf len, badge := badge } capInfo 0 =
      regMessageFrameCapsOpt layout rf len badge capInfo := by
  simp only [Architecture.returnFrameOfMessage, Architecture.returnMessageInfo,
    regMessageFrameCapsOpt, Architecture.badgeWordOrZero, regMessageInfoWordCaps,
    Architecture.regMessageBody_size, Architecture.regMessageBody_word, Nat.add_zero]

/-- **The reply-receive's last write, with the transfer's report**: the frame
written into the ready caller's saved registers, the message held where the
caller is, unexpectedly, not ready.  The report comes first, so it is read
before the state is handed over. -/
@[noinline] def deliverReplyRecvCapsFrame (capInfo : Nat) (Y : SystemState) (c : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) : SystemState :=
  writeDeliveredFrameIfReady Y c (regMessageFrameCapsOpt layout rf len badge capInfo)
    (fun _ => holdReplyRecvBody Y c layout rf len badge)

/-! ### The request a routed reply-receive makes -/

/-- The extra-capability count a routed reply-receive's frame names is the
count its message-info word holds (`routedExtraCaps`). -/
theorem routedExtraCaps_eq_of_replyRecv {rf : SeLe4n.RegisterFile} {capAddr : SeLe4n.CPtr}
    {mi : MessageInfo}
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf opCode SeLe4n.arm64DefaultLayout rf =
      .replyRecv capAddr mi) :
    routedExtraCaps rf = mi.extraCaps := by
  unfold Architecture.RegisterDecode.registerRoutedSyscallOf at hR
  dsimp only at hR
  cases hD : Architecture.RegisterDecode.decodeMsgInfoWord
      (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.msgInfoReg) with
  | error e => rw [hD] at hR; cases hR
  | ok m =>
    rw [hD] at hR
    have hm : m = mi := by
      simp only [Architecture.RegisterDecode.routedShortTail_eq,
        Architecture.RegisterDecode.routedLongTail_eq] at hR
      by_cases hLen : m.length ≤ SeLe4n.arm64DefaultLayout.msgRegs.size ∨
            Architecture.RegisterDecode.syscallNumberReadsOverflow
              opCode = false <;>
        first | rw [if_pos hLen] at hR | rw [if_neg hLen] at hR
      repeat' split at hR
      all_goals first
        | (cases hR; rfl)
        | (cases hR; done)
        | (rcases Architecture.RegisterDecode.unroutedSyscall_eq hR with h | ⟨h, -⟩ <;> cases h)
        | skip
      all_goals done
    subst hm
    unfold Architecture.RegisterDecode.decodeMsgInfoWord at hD
    cases hD; rfl

/-- **The request a routed reply-receive makes**: under the grant right, the
replier's frame asks for the count its message-info word names. -/
theorem replyCapRequest_of_routedReplyRecv (st : SystemState) (replier : SeLe4n.ThreadId)
    (stcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hS : st.getTcb? replier = some stcb)
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf opCode SeLe4n.arm64DefaultLayout
      stcb.registerContext = .replyRecv capAddr mi) :
    replyCapRequest st replier true =
      frameCapRequestOf st stcb (routedExtraCaps stcb.registerContext) := by
  obtain ⟨decoded, hDec0, hSid, -, -, hMi, -⟩ :=
    Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecv st replier
      SeLe4n.arm64DefaultLayout stcb.registerContext 32 capAddr mi
      (by rw [Architecture.RegisterDecode.registerRoutedSyscall_default]; exact hR)
  obtain ⟨_, hDec⟩ := Architecture.RegisterDecode.decodeSyscallArgsFromState_blockedSender hDec0
    (by rw [hSid]; rfl)
  unfold replyCapRequest
  rw [hS]
  simp only [senderFrameCapRequest, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    blockedSenderDecode, hDec, hMi, routedExtraCaps_eq_of_replyRecv hR]
  rfl

/-! ### The reply-receive that blocks -/

/-- **The reply-receive that blocks, its reply leg transferring**: under the
reply's guard, with no sender waiting, a reply leg whose transfer answers
`(summary, S2)` on the state the reply leaves, and the receive's block
admissible on `S2`, the composite is the reply's writes, the transfer, the
receive's block, the server's priority walk and the caller staged with the
transfer's report. -/
theorem replyRecvOnCore_blocks_transfer (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true)
    (hS : ep.sendQ.head = none)
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyTransferCaps st tid c grant (storeReplyRendezvous st c tid rid msg) =
      .ok (summary, S2))
    (hE2 : S2.objects[epId]? = some (.endpoint ep)) {rt2 : TCB}
    (hR2 : S2.objects[tid.toObjId]? = some (.tcb rt2)) (hA2 : receiveBlockAdmits rt2 = true)
    (hNo2 : S2.objects.noResizeDue)
    (hG2 : receiveBlocksInPlace S2 epId tid ep.receiveQ.tail (some rid) = true) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock (receiveReturnSchedContext true S2 tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c
            summary.capInfo) := by
  obtain ⟨hE3, ⟨rt3, hR3, hA3⟩, hG3⟩ := receiveReturnSchedContext_receiveGuard true S2 tid hNo2
    hE2 hR2 hA2 hG2
  generalize hQ : receiveReturnSchedContext true S2 tid = Q at hE3 hR3 hG3 ⊢
  obtain ⟨hEq, hHead⟩ := replyOnCore_inPlace st tid c tid ct ep0 rid msg core hSz hT hIpc hRO hG
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRec : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  generalize hS1 : storeReplyRendezvous st c tid rid msg = S1 at hEq hHead hXf
  have hPop : replyRecvPopDonation rid c S1 = .ok (none, S1) := by
    unfold replyRecvPopDonation
    rw [replyFrameHeadHolder?_of_no_head _ _ hHead]
    simp only [popUnheldReplyHead_of_no_head _ _ _ _ hHead]
  have hXf' : replyRecvReplyTransfer none st tid c grant S1 = .ok (summary, S2) := hXf
  have hEp2 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE3
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core Q =
      (removeRunnableOnCore (storeReceiveBlock Q epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq Q epId ep tid rt3 (some rid) core hE3 hS hR3 hA3 hG3]
    have hSnd : (receiveRendezvousSender? Q epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp2, hS]
    simp only [hSnd, ↓reduceIte]
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRec, Option.getD_some, hEq, hPop, hXf', hQ, hRecv, Option.bind_some, hS]
  have hRes : tid.isReserved = false := by
    have h := hG3
    simp only [receiveBlocksInPlace, enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1.1.1.1.1
  simp [replyRecvPostReceiveDonation_none_self _ _ _ _ hRes, applyReceiveLegPipHandoff, replyRecvAnswerCaller]

/-! ### The donated reply-receive -/

/-- **The donated reply-receive that blocks, its reply leg transferring**: as
`replyRecvAnsweringOnCore_donated_inPlace`, with the reply leg's transfer
answering `(summary, S2)` on the state the pop leaves and the receive's block
admissible on `S2`. -/
theorem replyRecvOnCore_donated_transfer (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hS : ep.sendQ.head = none)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyTransferCaps st tid c grant
      (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c)) = .ok (summary, S2))
    (hE2 : S2.objects[epId]? = some (.endpoint ep)) {rt2 : TCB}
    (hR2 : S2.objects[tid.toObjId]? = some (.tcb rt2)) (hA2 : receiveBlockAdmits rt2 = true)
    (hNo2 : S2.objects.noResizeDue)
    (hG2 : receiveBlocksInPlace S2 epId tid ep.receiveQ.tail (some rid) = true) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (descheduleAtPlacement (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true S2 tid) epId tid ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid) tid core).1 c
          summary.capInfo) := by
  obtain ⟨rp', scId, sc, hRp', hN, hScO, hHead, hBelow, hCode, hCRes, hNe, hNo, hLC, hFC, hLR, hFR,
    _, hPop⟩ := replyPopsInPlace_donation st c tid rid msg ct hT hSRes hG
  rw [hRp] at hRp'
  cases hRp'
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc] at hXf
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st tid c tid ct ep0 rid rp msg core hSz hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRecS : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  rw [← storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hPop
  generalize hS1 : storeReplyRendezvous st c tid rid msg = S1 at hEq hPop hXf
  generalize hP : popDonationSettledInPlace S1 c tid scId (determineTargetCore st c) = P
    at hPop hXf
  have hXf' : replyRecvReplyTransfer none st tid c grant P = .ok (summary, S2) := hXf
  obtain ⟨hE3, ⟨rt3, hR3, hA3⟩, hG3⟩ := receiveReturnSchedContext_receiveGuard true S2 tid hNo2
    hE2 hR2 hA2 hG2
  generalize hQ : receiveReturnSchedContext true S2 tid = Q at hE3 hR3 hG3 ⊢
  have hEp2 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE3
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core Q =
      (removeRunnableOnCore (storeReceiveBlock Q epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq Q epId ep tid rt3 (some rid) core hE3 hS hR3 hA3 hG3]
    have hSnd : (receiveRendezvousSender? Q epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp2, hS]
    simp only [hSnd, ↓reduceIte]
  obtain ⟨tb, hTb, hBk⟩ := receiveBlock_receiver_blocked Q epId ep tid rt3 (some rid) core hE3 hR3
    hA3 hG3
  have hDq : rendezvousDequeuedCall (removeRunnableOnCore (storeReceiveBlock Q epId tid
      ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid = false := by
    unfold rendezvousDequeuedCall lookupTcb
    simp only [hSRes, Bool.false_eq_true, ↓reduceIte, hTb, hBk]
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_some, hEq, hPop, hXf', hQ, hRecv, Option.bind_some, hS]
  simp [replyRecvPostReceiveDonation, hDq, applyReceiveLegPipHandoff, replyRecvAnswerCaller]

/-! ### The reply-receive answering a caller recording no server -/

/-- **The unheld reply-receive that blocks, its reply leg transferring**: as
`replyRecvAnsweringOnCore_unheld_inPlace`, with the reply leg's transfer
answering `(summary, S2)` on the state the pop leaves and the receive's block
admissible on `S2`. -/
theorem replyRecvOnCore_unheld_transfer (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hS : ep.sendQ.head = none)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyTransferCaps st tid c grant
      (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLeg st c rid msg) c ⟨replyHeadContextCode st rid - 1⟩)
        (determineTargetCore st c) ⟨replyHeadContextCode st rid - 1⟩) = .ok (summary, S2))
    (hE2 : S2.objects[epId]? = some (.endpoint ep)) {rt2 : TCB}
    (hR2 : S2.objects[tid.toObjId]? = some (.tcb rt2)) (hA2 : receiveBlockAdmits rt2 = true)
    (hNo2 : S2.objects.noResizeDue)
    (hG2 : receiveBlocksInPlace S2 epId tid ep.receiveQ.tail (some rid) = true) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock (receiveReturnSchedContext true S2 tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c
            summary.capInfo) := by
  obtain ⟨rp', scId, hRp', hN, hCode, hCRes, hNo, hLC, hFC, hLR, hFR, hPopR, -⟩ :=
    replyUnheldPopsInPlace_pop st c rid msg ct hT hG
  rw [hRp] at hRp'
  cases hRp'
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc] at hXf
  obtain ⟨hEq, _⟩ := replyOnCore_eq_storeLeg st tid c none ct ep0 rid rp msg core hSz hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRecS : recordedReplyServer? st c = none := by
    simp only [recordedReplyServer?, hTc, hIpc]
  rw [← storeReplyLeg_eq_hold _ _ _ _ hNo] at hPopR
  simp only [SystemState.unlinkReplyWaiterOpt] at hEq
  generalize hS1 : storeReplyLeg st c rid msg = S1 at hEq hPopR hXf
  generalize hP : SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace S1 c scId)
    (determineTargetCore st c) scId = P at hPopR hXf
  have hXf' : replyRecvReplyTransfer none st tid c grant P = .ok (summary, S2) := hXf
  obtain ⟨hE3, ⟨rt3, hR3, hA3⟩, hG3⟩ := receiveReturnSchedContext_receiveGuard true S2 tid hNo2
    hE2 hR2 hA2 hG2
  generalize hQ : receiveReturnSchedContext true S2 tid = Q at hE3 hR3 hG3 ⊢
  have hEp2 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE3
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core Q =
      (removeRunnableOnCore (storeReceiveBlock Q epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq Q epId ep tid rt3 (some rid) core hE3 hS hR3 hA3 hG3]
    have hSnd : (receiveRendezvousSender? Q epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp2, hS]
    simp only [hSnd, ↓reduceIte]
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_none, hEq, hPopR, hXf', hQ, hRecv, Option.bind_some, hS]
  have hRes : tid.isReserved = false := by
    have h := hG3
    simp only [receiveBlocksInPlace, enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1.1.1.1.1
  simp [replyRecvPostReceiveDonation_none_self _ _ _ _ hRes, applyReceiveLegPipHandoff, replyRecvAnswerCaller]

/-! ### The reply-receive on a reply object linked to nothing -/

/-- **The unlinked reply-receive that blocks, its reply leg transferring**
(WS-SX SX8.3): as `replyRecvAnsweringOnCore_unlinked_inPlace`, with the reply
leg's transfer answering `(summary, S2)` on the state the reply leg leaves and
the receive's block admissible on `S2`. -/
theorem replyRecvOnCore_unlinked_transfer (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnlinkedInPlace st c rid = true)
    (hS : ep.sendQ.head = none)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyTransferCaps st tid c grant (storeReplyLeg st c rid msg) = .ok (summary, S2))
    (hE2 : S2.objects[epId]? = some (.endpoint ep)) {rt2 : TCB}
    (hR2 : S2.objects[tid.toObjId]? = some (.tcb rt2)) (hA2 : receiveBlockAdmits rt2 = true)
    (hNo2 : S2.objects.noResizeDue)
    (hG2 : receiveBlocksInPlace S2 epId tid ep.receiveQ.tail (some rid) = true) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock (receiveReturnSchedContext true S2 tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c
            summary.capInfo) := by
  have hG' := hG
  simp only [replyUnlinkedInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG'
  obtain ⟨⟨⟨⟨⟨hCRes, hLC⟩, hFC⟩, hLR⟩, hFR⟩, hRpG⟩ := hG'
  rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRp] at hRpG
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hRpG
  obtain ⟨hNext, hPrev⟩ := hRpG
  obtain ⟨hEq, hR5⟩ := replyOnCore_eq_storeLeg st tid c none ct ep0 rid rp msg core hSz hT hIpc
    hRO hCRes hLC hFC hLR hFR hRp (Or.inl ⟨hNext, hPrev⟩)
  simp only [SystemState.unlinkReplyWaiterOpt] at hEq hR5
  have hHead : replyFrameHeadContext? (storeReplyLeg st c rid msg) rid = none := by
    unfold replyFrameHeadContext?
    rw [hR5]
    simp only [Reply.consumed, hNext]
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRecS : recordedReplyServer? st c = none := by
    simp only [recordedReplyServer?, hTc, hIpc]
  generalize hS1 : storeReplyLeg st c rid msg = S1 at hEq hHead hXf
  have hPop : replyRecvPopDonation rid c S1 = .ok (none, S1) := by
    unfold replyRecvPopDonation
    rw [replyFrameHeadHolder?_of_no_head _ _ hHead]
    simp only [popUnheldReplyHead_of_no_head _ _ _ _ hHead]
  have hXf' : replyRecvReplyTransfer none st tid c grant S1 = .ok (summary, S2) := hXf
  obtain ⟨hE3, ⟨rt3, hR3, hA3⟩, hG3⟩ := receiveReturnSchedContext_receiveGuard true S2 tid hNo2
    hE2 hR2 hA2 hG2
  generalize hQ : receiveReturnSchedContext true S2 tid = Q at hE3 hR3 hG3 ⊢
  have hEp2 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE3
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core Q =
      (removeRunnableOnCore (storeReceiveBlock Q epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq Q epId ep tid rt3 (some rid) core hE3 hS hR3 hA3 hG3]
    have hSnd : (receiveRendezvousSender? Q epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp2, hS]
    simp only [hSnd, ↓reduceIte]
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_none, hEq, hPop, hXf', hQ, hRecv, Option.bind_some, hS]
  have hRes : tid.isReserved = false := by
    have h := hG3
    simp only [receiveBlocksInPlace, enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1.1.1.1.1
  simp [replyRecvPostReceiveDonation_none_self _ _ _ _ hRes, applyReceiveLegPipHandoff, replyRecvAnswerCaller]

/-- Under `replyUnlinkedInPlace`, the reply object is consumed free (it heads no
stack, so consumption takes its links off). -/
theorem replyUnlinkedInPlace_consumedFree {st : SystemState} {c : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {rp : Reply} (hG : replyUnlinkedInPlace st c rid = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) : rp.consumed.isFree = true := by
  simp only [replyUnlinkedInPlace, Bool.and_eq_true] at hG
  have hRpG := hG.2
  rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRp] at hRpG
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hRpG
  rw [← Reply.consumedIsFree_eq]; simp only [Reply.consumedIsFree, hRpG.1]

theorem replyUnlinkedInPlace_findsCaller {st : SystemState} {c : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} (hG : replyUnlinkedInPlace st c rid = true) :
    st.objects.findsInPlace c.toObjId = true := by
  simp only [replyUnlinkedInPlace, Bool.and_eq_true] at hG
  exact hG.1.1.1.2

/-! ### The long reply-receive that blocks -/

/-- The long reply-receive's frame with the transfer's report, the report
first so it is read before the state is handed over. -/
@[noinline] def deliverLongReplyRecvCapsFrame (capInfo : Nat) (Y : SystemState)
    (c : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (len : Nat) (tid : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge) : SystemState :=
  deliverLongReplyRecvFrame Y c rf len tid badge capInfo

end SeLe4n.Kernel
