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
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvUnheldInPlace

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
(`receiveTransferCaps_reply_transferFrame`, `receiveGuard_of_transferFrame`)
under `replyTransferStoresInPlace`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-! ### The frame with the transfer's report -/

/-- `regReplyRecvInfoWord` with the transfer's report. -/
@[noinline] def regReplyRecvInfoWordCaps (layout : SeLe4n.SyscallRegisterLayout) (len capInfo : Nat) :
    UInt64 :=
  (({ length := min (min (Architecture.regMessageLength layout len - 1) 4) maxMessageRegisters
      extraCaps := capInfo % 4
      label := min 0 (Architecture.errorLabelBase - 1)
      capsUnwrapped := capInfo / 4 % 8 } : MessageInfo).encode).toUInt64

/-- `regReplyRecvFrame` with the transfer's report in its message-info word. -/
@[inline] def regReplyRecvFrameCaps (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (capInfo : Nat) :
    Architecture.SyscallReturnFrame :=
  { x0 := Architecture.badgeWordOrZero badge
    x1 := regReplyRecvInfoWordCaps layout len capInfo
    x2 := Architecture.regMessageWord layout rf len 1
    x3 := Architecture.regMessageWord layout rf len 2
    x4 := Architecture.regMessageWord layout rf len 3
    x5 := Architecture.regMessageWord layout rf len 4 }

theorem returnFrameOfMessage_regReplyRecvBody_caps (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (capInfo : Nat) :
    Architecture.returnFrameOfMessage
        { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } capInfo 0 =
      regReplyRecvFrameCaps layout rf len badge capInfo := by
  simp only [Architecture.returnFrameOfMessage, Architecture.returnMessageInfo,
    regReplyRecvFrameCaps, Architecture.badgeWordOrZero, regReplyRecvInfoWordCaps,
    Architecture.regReplyRecvBody_size, Architecture.regReplyRecvBody_word, Nat.add_zero]

/-- **The reply-receive's last write, with the transfer's report**: the frame
written into the ready caller's saved registers, the message held where the
caller is, unexpectedly, not ready.  The report comes first, so it is read
before the state is handed over. -/
@[noinline] def deliverReplyRecvCapsFrame (capInfo : Nat) (Y : SystemState) (c : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) : SystemState :=
  writeDeliveredFrameIfReady Y c (regReplyRecvFrameCaps layout rf len badge capInfo)
    (fun _ => holdReplyRecvBody Y c layout rf len badge)

/-! ### The request a routed reply-receive makes -/

/-- The extra-capability count a routed reply-receive's frame names is the
count its message-info word holds (`routedExtraCaps`). -/
theorem routedExtraCaps_eq_of_replyRecv {rf : SeLe4n.RegisterFile} {capAddr : SeLe4n.CPtr}
    {mi : MessageInfo}
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout rf =
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
      repeat' split at hR
      all_goals first
        | (cases hR; rfl)
        | (cases hR; done)
        | (rcases Architecture.RegisterDecode.unroutedSyscall_eq hR with h | ⟨h, -⟩ <;> cases h)
        | skip
      all_goals done
    subst hm
    unfold Architecture.RegisterDecode.decodeMsgInfoWord at hD
    split at hD
    · cases hD; rfl
    · cases hD

/-- **The request a routed reply-receive makes**: under the grant right, the
replier's frame asks for the count its message-info word names. -/
theorem replyCapRequest_of_routedReplyRecv (st : SystemState) (replier : SeLe4n.ThreadId)
    (stcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hS : st.getTcb? replier = some stcb)
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
      stcb.registerContext = .replyRecv capAddr mi) :
    replyCapRequest st replier true =
      frameCapRequestOf st stcb (routedExtraCaps stcb.registerContext) := by
  obtain ⟨decoded, hDec, -, -, -, hMi, -⟩ :=
    Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecv st replier
      SeLe4n.arm64DefaultLayout stcb.registerContext 32 capAddr mi
      (by rw [Architecture.RegisterDecode.registerRoutedSyscall_default]; exact hR)
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
    (hG2 : receiveBlocksInPlace S2 epId tid ep.receiveQ.tail (some rid) = true) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock S2 epId tid ep.recvTailCode
            (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c summary.capInfo) := by
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
  have hEp2 : S2.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE2
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core S2 =
      (removeRunnableOnCore (storeReceiveBlock S2 epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq S2 epId ep tid rt2 (some rid) core hE2 hS hR2 hA2 hG2]
    have hSnd : (receiveRendezvousSender? S2 epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp2, hS]
    simp only [hSnd, ↓reduceIte]
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRec, Option.getD_some, hEq, hPop, hXf', hRecv, hEp2, Option.bind_some, hS]
  simp [replyRecvPostReceiveDonation, applyReceiveLegPipHandoff,
    Architecture.stageWokenSendCompletion_none, replyRecvAnswerCaller]

/-- The receive leg that blocks, after the reply's transfer: the server's block
on the endpoint, the server taken off its core, then its priority walk. -/
@[inline] def storeReplyRecvBlockTail (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) :
    SystemState :=
  (PriorityInheritance.propagatePipChainCrossCore
    (removeRunnableOnCore (storeReceiveBlock Y epId tid tailCode (rid.val + 1)) tid core) tid
    core).1

/-- **The blocking reply-receive whose reply leg transfers, delivered**: the
reply's writes, the transfer in place on no endpoint, the server's block and
priority walk, then the caller's frame with the transfer's report.  The replier
and the caller enter as the words the transfer reads of them, read before the
reply's writes. -/
@[noinline] def performReplyRecvBlockCapsDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  let X := storeReplyRendezvousReady st c tid rid
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverReplyRecvCapsFrame
      (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (storeReplyRecvBlockTail
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
        tid rid epId tailCode core)
      c layout rf len badge

theorem storeReplyRecvBlockTail_noResizeDue (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (hNo : Y.objects.noResizeDue) :
    (storeReplyRecvBlockTail Y tid rid epId tailCode core).objects.noResizeDue :=
  propagatePipChainCrossCore_noResizeDue _ _ _ (removeRunnableOnCore_noResizeDue _ _ _
    (storeReceiveBlock_noResizeDue _ _ _ _ _ hNo))

/-- **The receive leg's tail stages the caller's held message as the frame
with the report**, the server it blocks staging nothing: on a state `Y` where
the receive blocks in place (its guard on `Y` with the caller's message held),
staging the caller with the report and then the server is
`deliverReplyRecvCapsFrame` on `storeReplyRecvBlockTail`. -/
theorem replyRecvBlockTail_staged (Y : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (ep : Endpoint) (core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (capInfo : Nat)
    (hNo : Y.objects.noResizeDue) (hNe : tid ≠ c)
    (hSz4 : Architecture.regMessageLength layout len - 1 ≤ 4)
    (hE2 : (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge })).objects[epId]? =
        some (.endpoint ep)) {rt2 : TCB}
    (hR2 : (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge })).objects[tid.toObjId]? =
        some (.tcb rt2))
    (hA2 : receiveBlockAdmits rt2 = true)
    (hG2 : receiveBlocksInPlace (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge })) epId tid
        ep.receiveQ.tail (some rid) = true) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock (Y.mapTcbInPlace c (holdMessage
            { registers := Architecture.regReplyRecvBody layout rf len, badge := badge }))
            epId tid ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1
        c capInfo) tid 0 =
      deliverReplyRecvCapsFrame capInfo (storeReplyRecvBlockTail Y tid rid epId ep.recvTailCode core)
        c layout rf len badge := by
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨t, hT1, hB⟩ := receiveBlock_receiver_blocked _ epId ep tid rt2 (some rid) core hE2 hR2
    hA2 hG2
  have h3 := removeRunnableOnCore_noResizeDue _ tid core
    (storeReceiveBlock_noResizeDue _ epId tid ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid)) hNo)
  rw [storeReceiveBlock_msg _ _ _ _ _ _ _ hNo hNe, removeRunnableOnCore_msg,
    SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hT1
  obtain ⟨x, hX, hEq⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h3 tid t hT1
  rw [storeReceiveBlock_msg _ _ _ _ _ _ _ hNo hNe, removeRunnableOnCore_msg,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ h3,
    stageDeliveredMessage_holdMessage_caps _ _ _ _ (propagatePipChainCrossCore_noResizeDue _ _ _ h3)
      (by rw [Architecture.regReplyRecvBody_size]; exact hSz4),
    returnFrameOfMessage_regReplyRecvBody_caps]
  exact stageDeliveredMessage_writeDeliveredFrameIfReady_blocked
    (storeReplyRecvBlockTail Y tid rid epId ep.recvTailCode core) c tid _ _ 0 hCT x hX
    (by rw [hEq, hB]; exact fun h => by cases h)

/-- **The blocking reply-receive whose reply leg transfers, delivered**: under
the guard of `replyRecvOnCore_blocks_inPlace` (its inert transfer replaced by a
granting replier whose frame asks for `count` capabilities, `hReq`), a reply of
at most four words and the transfer's stores in place
(`replyTransferStoresInPlace`, read on the pre-state), the checked arm's result
is `performReplyRecvBlockCapsDelivered`. -/
theorem replyRecvOnCore_blocks_capsDelivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (stcb : TCB) (count : Nat)
    (hSz4 : Architecture.regMessageLength layout len - 1 ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hFree : rp.consumed.isFree = true) (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count)
    (hW : replyTransferStoresInPlace st c.toObjId stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
      count ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot = true) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvBlockCapsDelivered st c tid rid epId ep.recvTailCode layout rf len
        badge core stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot count ct.vspaceRoot ct.ipcBuffer
        ct.cspaceRoot) := by
  have hNo := replyWakesInPlace_noResizeDue hG
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG
    exact hG.1.1.1.2
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  have hSz : ¬ (Architecture.regReplyRecvBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regReplyRecvBody_size]; unfold maxMessageRegisters; omega
  generalize hMsg : ({ registers := Architecture.regReplyRecvBody layout rf len, badge := badge } :
    IpcMessage) = msg
  have hNoX := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have hAX := ipcBufferReadsAgree_storeReplyRendezvousReady st c tid rid hNo
  obtain ⟨hIX, hLX⟩ := storeReplyRendezvousReady_fields st c tid rid hNo
  generalize hX : storeReplyRendezvousReady st c tid rid = X at hNoX hAX hIX hLX
  have hS1 : storeReplyRendezvous st c tid rid msg = X.mapTcbInPlace c (holdMessage msg) := by
    rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, hX]
  obtain ⟨s, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 s hNoX hT1
  have hXf : replyTransferCaps st tid c true (storeReplyRendezvous st c tid rid msg) =
      .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    unfold replyTransferCaps
    rw [hReq, hTgt, hS1, receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoX, hT1]
    rfl
  -- the receive's guard, on the state the reply leaves, then across the transfer
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := storeReplyRendezvous_receiveGuard st c tid rid msg ct rp
    epId ep rt hNo hT hIpc hFC hRp hNe hE hR hA hEnq hFree hStash hRec
  rw [hS1] at hE1 hR1 hG1 hXf
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAX) hIX hLX
    ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoX) c.toObjId stcb ct count hW
    (by rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoX, hT1]; rfl)).1
  obtain ⟨hE2, ⟨rt2, hR2, hA2⟩, hG2⟩ := receiveGuard_of_transferFrame hFr hE1 hR1 hA1 hG1
  rw [← hS1] at hXf
  rw [replyRecvOnCore_blocks_transfer st epId tid c rid msg true core ct ep0 ep (hMsg ▸ hSz) hT hIpc
    hRO hG hS hXf hE2 hR2 hA2 hG2]
  dsimp only
  subst hMsg
  simp only [CapTransferSummary.capInfo_empty]
  rw [replyRecvBlockTail_staged Y1 c tid rid epId ep core layout rf len badge s.capInfo hNoY hNe hSz4
    hE2 hR2 hA2 hG2]
  -- the in-place transfer is the specification's
  have hK := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => deliverReplyRecvCapsFrame i (storeReplyRecvBlockTail Y tid rid epId ep.recvTailCode
      core) c layout rf len badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hK
  rw [hAX.frameCapRequestOf, hAX.capTargetOf, hT1] at hK
  unfold performReplyRecvBlockCapsDelivered
  rw [hX]
  exact congrArg (fun Z => (.ok ((), Z) : Except KernelError (Unit × SystemState))) hK.symm

end SeLe4n.Kernel
