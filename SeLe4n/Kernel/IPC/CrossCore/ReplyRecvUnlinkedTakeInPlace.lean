/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvUnheldInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyCapsReturnDelivered

/-!
# A reply-receive to a caller recording no server, its receive leg taking a waiting sender, in place

WS-SX SX8.3: seL4-MCS's `handleReplyRecv` through a reply capability whose
caller records no server (the server was finalised, so `doReplyTransfer` lets
any holder of the capability answer it), then `receiveIPC` meeting a sender
already queued on the endpoint.  On a reply object linked to nothing the reply
leg is `storeReplyLeg` (no reply waiters to leave, nothing to pop); the take's
guard, read on the pre-state, is carried across it (`storeReplyLeg_takeGuard`),
across the reply leg's transfer and across the receive's context return, as for
the reply-receive answering a caller blocked on this server
(`replyRecvOnCore_take_delivered`).  The in-place performers are proven equal to
the specification (`replyRecvOnCore_unlinked_take_delivered`,
`replyRecvOnCore_unlinked_take_capsDelivered`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section UnlinkedTakeGuard

/-- **The reply leg alone keeps every thread's send-capability words**:
`storeReplyRendezvousReady_keepsSendCaps` without the unlink. -/
theorem storeReplyLegReady_keepsSendCaps (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    SystemState.objectsKeepSendCaps (storeReplyLegReady st c rid) st := by
  unfold storeReplyLegReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _
    (determineTargetCore (st.updateTcb c receiverReady) c) c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  refine (SystemState.updateTcb_keepsSendCaps _ c ?_ hNo3).trans
      ((SystemState.modifyObject_keepsSendCaps _ _ ?_ hNo2).trans
        ((enqueueRunnableOnCore_keepsSendCaps _ _ c hNo1).trans
          (SystemState.updateTcb_keepsSendCaps _ c ?_ hNo)))
  · intro _; rfl
  · intro o; cases o <;> rfl
  · intro _; rfl

/-- **The take's guard across the reply leg alone** (no server's reply waiters
to leave): `storeReplyRendezvous_takeGuard` for `storeReplyLeg`. -/
theorem storeReplyLeg_takeGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hG : receiveTakesInPlace st epId tid s sTcb = true) :
    (storeReplyLeg st c rid msg).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb1, (storeReplyLeg st c rid msg).objects[s.toObjId]? = some (.tcb sTcb1) ∧
        SenderWordsKept sTcb1 sTcb ∧
        receiveTakesInPlace (storeReplyLeg st c rid msg) epId tid s sTcb1 = true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hSc' : s.toObjId ≠ c.toObjId := fun e => hSC (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hSr : s.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hS; cases hS
  have hKS := storeReplyLegReady_keepsSendCaps st c rid hNo
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo]
  generalize hS1 : storeReplyLegReady st c rid = S1 at hKS
  have hAg := fun x hx hy => hS1 ▸ storeReplyLegReady_agree st c rid ct hNo hTc hFC x hx hy
  have hHold : ∀ x, x ≠ c.toObjId →
      (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = S1.objects[x]? := fun x hx => by
    rw [SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyLegReady_keepsFinds st c rid hNo hFC
  obtain ⟨tc1, htc1, -⟩ := hS1 ▸ storeReplyLegReady_callerView st c rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyLegReady_reply st c rid ct rp hNo hTc hFC hRp hRc
  have hAt : ∀ x, (x = c.toObjId ∧
        ∃ t, (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = some (.tcb t)) ∨
      (x = rid.toObjId ∧
        (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = some (.reply rp.consumed)) ∨
      ((S1.mapTcbInPlace c (holdMessage msg)).objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks := by
    intro x
    by_cases hxc : x = c.toObjId
    · subst hxc
      left
      refine ⟨rfl, holdMessage msg tc1, ?_⟩
      rw [SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl
    · by_cases hxr : x = rid.toObjId
      · subst hxr; right; left; rw [hHold _ hxc]; exact ⟨rfl, hR1⟩
      · right; right; rw [hHold _ hxc]; exact hAg x hxc hxr
  have hV : ∀ x, (S1.mapTcbInPlace c (holdMessage msg)).getObjectType? x = st.getObjectType? x := by
    intro x
    rcases hAt x with ⟨e, t, h⟩ | ⟨e, h⟩ | h
    · subst e; unfold SystemState.getObjectType?
      rw [h, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc]; rfl
    · subst e; unfold SystemState.getObjectType?; rw [h, hRp]; rfl
    · exact getObjectType?_of_view h
  have hKF : (S1.mapTcbInPlace c (holdMessage msg)).objectsKeepFinds st :=
    (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK
  have hTcb : ∀ p : SeLe4n.ThreadId, (st.getTcb? p).isSome = true →
      ((S1.mapTcbInPlace c (holdMessage msg)).getTcb? p).isSome = true := by
    intro p hp
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hp
    have h1 := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht
    rcases hAt p.toObjId with ⟨_, t', h⟩ | ⟨e, _⟩ | h
    · exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h⟩
    · rw [e, hRp] at h1; cases h1
    · obtain ⟨t', h', _⟩ := agreeAt_tcb h h1
      exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h'⟩
  obtain ⟨sTcb1, hS1o, e1⟩ := agreeAt_tcb (hAg _ hSc' hSr) hS
  have hw : sTcb1.sendCapWords = sTcb.sendCapWords := by
    have k := hKS s.toObjId
    rw [hS1o, hS] at k
    simpa [KernelObject.sendCapWords] using k
  have hKept := SenderWordsKept.of_withoutRunLinks e1 hw
  refine ⟨by rw [hHold _ hEc]; exact agreeAt_of_not_tcb (hAg _ hEc hEr) (fun _ e => by cases e) hE,
    sTcb1, by rw [hHold _ hSc']; exact hS1o, hKept, ?_⟩
  exact receiveTakesInPlace_of_frame epId tid s sTcb sTcb1 hKF hV hTcb hKept.queueNext
    hKept.ipcState hG

/-! ### The answered caller's held message, past the take -/


end UnlinkedTakeGuard

section UnlinkedTake

/-- **The reply-receive on an unlinked reply object meeting a waiting sender,
its reply leg transferring**: `replyRecvOnCore_take_transfer` for a caller
recording no server whose reply object is linked to nothing
(`replyUnlinkedInPlace`): the reply leg is `storeReplyLeg`, nothing is popped,
and the composite is the reply's writes, the transfer, the return, the take,
the replier's priority walk and the caller staged with the transfer's report. -/
theorem replyRecvOnCore_unlinked_take_transfer (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (rp : Reply) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnlinkedInPlace st c rid = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hH : ep.sendQ.head = some s)
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyTransferCaps st tid c grant (storeReplyLeg st c rid msg) = .ok (summary, S2))
    (hE2 : (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep))
    {sTcb2 : TCB}
    (hT2 : (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2))
    (hG2 : receiveTakesInPlace (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 = .send capAddr mi)
    (hF : sTcb2.ipcFaultSend = false) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
          (PriorityInheritance.propagatePipChainCrossCore
            ((wakeThread ((storePopHead (receiveReturnSchedContext true S2 tid) epId false s
                sTcb2.queueNext).updateTcb s receiverReady) s core).1.updateTcb tid
              (callReceiverTcb (blockedSenderMessage (storePopHead
                (receiveReturnSchedContext true S2 tid) epId false s sTcb2.queueNext)
                s sTcb2))) tid core).1 c summary.capInfo) := by
  generalize hQ : receiveReturnSchedContext true S2 tid = Q at hE2 hT2 hG2 ⊢
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
  have hEp2 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE2
  obtain ⟨hRecv, -, -⟩ := receiveTake_delivered Q epId ep tid (some rid) core s sTcb2 capAddr mi
    hE2 hH hT2 hG2 hR hF
  have hNoCall := receiveTake_dequeuedNoCall Q epId ep tid core s sTcb2
    (blockedSenderMessage (storePopHead Q epId false s sTcb2.queueNext) s sTcb2) hE2 hH hT2 hG2
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_none, hEq, hPop, hXf', hQ, hRecv, hEp2, Option.bind_some, hH]
  simp only [replyRecvPostReceiveDonation, hNoCall, Bool.false_eq_true, ↓reduceIte]
  simp [replyRecvAnswerCaller]

/-- **The reply-receive on an unlinked reply object meeting a waiting sender,
its reply transferring nothing, delivered**: the reply leg's writes
(`storeReplyLegReady`), the take, the replier's priority walk, then the caller's
frame and the replier's frame, its six words read from the sender's saved
registers before any write. -/
@[noinline] def performReplyRecvUnlinkedTakeLegs (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) : SystemState :=
  replyRecvTakeLegs 0 (receiveReturnSchedContextFast true (storeReplyLegReady st c rid)
    tid.val) c tid s epId nextCode core layout rf len badge

/-- The inert take on an unlinked reply object, the legs
(`performReplyRecvUnlinkedTakeLegs`) and then the replier's frame
(`writeTakerFrame`), each out of line so the arm releases the replier's register
file between them. -/
@[inline] def performReplyRecvUnlinkedTakeDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  writeTakerFrame (performReplyRecvUnlinkedTakeLegs st c tid rid epId s nextCode core layout rf len badge)
    tid w0 w1 w2 w3 w4 w5

/-- **The reply-receive on an unlinked reply object meeting a waiting sender,
its reply transferring nothing, is the specification's**: under
`replyUnlinkedInPlace` for a caller recording no server, a reply of at most four
words transferring no capability (`replyTransferInert`), and a sender `s` at the
head of the send queue blocked by a routed capability-free send, not delivering
a fault, whose take writes only its slots (every check read on the pre-state),
the checked arm's result is `performReplyRecvUnlinkedTakeDelivered`. -/
theorem replyRecvOnCore_unlinked_take_delivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (rp : Reply) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnlinkedInPlace st c rid = true) (hNe : tid ≠ c)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hInert : replyTransferInert st tid ct grant = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvUnlinkedTakeDelivered st c tid rid epId s sTcb.queueNextCode core layout rf
        len badge
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5) := by
  have hNo := replyWakesInPlace_noResizeDue (show replyWakesInPlace st c ct rid = true from hG)
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    have hG' : replyWakesInPlace st c ct rid = true := hG
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG'
    exact hG'.1.1.1.2
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hSz : ¬ (Architecture.regMessageBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regMessageBody_size]; unfold maxMessageRegisters; omega
  obtain ⟨hE1, sTcb1, hS1, hK, hG1⟩ := storeReplyLeg_takeGuard st c tid rid
    { registers := Architecture.regMessageBody layout rf len, badge := badge } ct rp epId ep s
    sTcb hNo hT hFC hRp hE hS hSC hGt
  have hXf := replyTransferCaps_of_inert st tid c grant ct hTc hInert
    (storeReplyLeg st c rid
      { registers := Architecture.regMessageBody layout rf len, badge := badge })
  have hR1 : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb1.registerContext) SeLe4n.arm64DefaultLayout
      sTcb1.registerContext 32 = .send capAddr mi := by rw [hK.regs]; exact hR
  obtain ⟨hE2, sTcb2, hS2, hK2, hG2⟩ := receiveReturnSchedContext_takeGuard true _ tid
    (storeReplyLeg_noResizeDue st c rid _ hNo) hE1 hS1 hG1
  have hKt := hK2.trans hK
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb2.registerContext) SeLe4n.arm64DefaultLayout
      sTcb2.registerContext 32 = .send capAddr mi := by rw [hKt.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hKt.faultSend]; exact hF
  rw [replyRecvOnCore_unlinked_take_transfer st epId tid c rid _ grant core ct ep0 rp ep s capAddr mi
    hSz hT hIpc hRO hG hRp hH hXf hE2 hS2 hG2 hR2 hF2]
  dsimp only
  rw [CapTransferSummary.capInfo_empty]
  have hNoX := storeReplyLegReady_noResizeDue st c rid hNo
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo,
    receiveReturnSchedContext_msg c id _ id true _ tid hNoX hNe.symm] at hE2 hS2 hG2 ⊢
  rw [replyRecvTakeFrame_staged _ c tid s epId ep sTcb2 core layout rf len badge 0 capAddr mi
    (receiveReturnSchedContext_noResizeDue true _ tid hNoX) hNe hSC hSz4 hE2 hH hS2 hG2 hR2 hF2,
    hKt.queueNext, hKt.regs, hKt.ipcBadgeView]
  unfold performReplyRecvUnlinkedTakeDelivered performReplyRecvUnlinkedTakeLegs
  rw [receiveReturnSchedContextFast_eq]

/-- **The reply-receive on an unlinked reply object meeting a waiting sender,
its reply leg transferring, delivered**: the reply leg's writes
(`storeReplyLegReady`), the transfer in place on no endpoint, the take, the
replier's priority walk, then the caller's frame with the transfer's report and
the replier's frame.  The replier and the caller enter as the words the transfer
reads of them, the sender as its successor and the six words of its frame, all
read before the reply's writes. -/
@[noinline] def performReplyRecvUnlinkedTakeCapsLegs (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := storeReplyLegReady st c rid
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    replyRecvTakeLegs (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (receiveReturnSchedContextFast true
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X) tid.val)
      c tid s epId nextCode core layout rf len badge

/-- The installing take on an unlinked reply object, its legs
(`performReplyRecvUnlinkedTakeCapsLegs`) and then the server's frame
(`writeTakerFrame`), each out of line so the arm releases the server's register
file between them. -/
@[inline] def performReplyRecvUnlinkedTakeCapsDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) (w0 w1 w2 w3 w4 w5 : UInt64)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  writeTakerFrame (performReplyRecvUnlinkedTakeCapsLegs st c tid rid epId s nextCode core layout rf len
    badge sv sb sroot count rv rb rroot) tid w0 w1 w2 w3 w4 w5

/-- **The reply-receive on an unlinked reply object meeting a waiting sender,
its reply leg transferring, is the specification's**: under the guard of
`replyRecvOnCore_unlinked_take_delivered` (its inert transfer replaced by a
granting replier whose frame asks for `count` capabilities, `hReq`), the checked
arm's result is `performReplyRecvUnlinkedTakeCapsDelivered`. -/
theorem replyRecvOnCore_unlinked_take_capsDelivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (rp : Reply) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (stcb : TCB) (count : Nat)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnlinkedInPlace st c rid = true) (hNe : tid ≠ c)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvUnlinkedTakeCapsDelivered st c tid rid epId s sTcb.queueNextCode core layout
        rf len badge
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5
        stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] count ct.spaceCells[2] ct.ipcBuffer
        ct.spaceCells[0]) := by
  have hNo := replyWakesInPlace_noResizeDue (show replyWakesInPlace st c ct rid = true from hG)
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    have hG' : replyWakesInPlace st c ct rid = true := hG
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG'
    exact hG'.1.1.1.2
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  have hSz : ¬ (Architecture.regMessageBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regMessageBody_size]; unfold maxMessageRegisters; omega
  obtain ⟨hE1, sTcb1, hS1o, hK1, hG1⟩ := storeReplyLeg_takeGuard st c tid rid
    { registers := Architecture.regMessageBody layout rf len, badge := badge } ct rp epId ep s
    sTcb hNo hT hFC hRp hE hS hSC hGt
  generalize hMsg : ({ registers := Architecture.regMessageBody layout rf len, badge := badge } :
    IpcMessage) = msg at hE1 hS1o hG1
  have hNoX := storeReplyLegReady_noResizeDue st c rid hNo
  have hAX := ipcBufferReadsAgree_storeReplyLegReady st c rid hNo
  generalize hX : storeReplyLegReady st c rid = X at hNoX hAX
  have hS1 : storeReplyLeg st c rid msg = X.mapTcbInPlace c (holdMessage msg) := by
    rw [storeReplyLeg_eq_hold _ _ _ _ hNo, hX]
  obtain ⟨sm, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 sm hNoX hT1
  have hXf : replyTransferCaps st tid c true (storeReplyLeg st c rid msg) =
      .ok (sm, Y1.mapTcbInPlace c (holdMessage msg)) := by
    unfold replyTransferCaps
    rw [hReq, hTgt, hS1, receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _)
      c _ _ _ X hNoX, hT1]
    rfl
  rw [hS1] at hE1 hS1o hG1
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAX)
    ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoX) c.toObjId stcb ct count
    (by rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X
      hNoX, hT1]; rfl)).1
  obtain ⟨hE2', sTcb2', hS2o', hK2', hG2'⟩ := takeGuard_of_transferFrame hFr hE1 hS1o hG1
  obtain ⟨hE2, sTcb2, hS2o, hK2, hG2⟩ := receiveReturnSchedContext_takeGuard true _ tid
    ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNoY) hE2' hS2o' hG2'
  have hK := hK2.trans (hK2'.trans hK1)
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb2.registerContext) SeLe4n.arm64DefaultLayout
      sTcb2.registerContext 32 = .send capAddr mi := by rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  rw [replyRecvOnCore_unlinked_take_transfer st epId tid c rid msg true core ct ep0 rp ep s capAddr mi
    (hMsg ▸ hSz) hT hIpc hRO hG hRp hH hXf hE2 hS2o hG2 hR2 hF2]
  dsimp only
  subst hMsg
  rw [CapTransferSummary.capInfo_empty]
  rw [receiveReturnSchedContext_msg c id _ id true Y1 tid hNoY hNe.symm] at hE2 hS2o hG2 ⊢
  rw [replyRecvTakeFrame_staged _ c tid s epId ep sTcb2 core layout rf len badge sm.capInfo capAddr
    mi (receiveReturnSchedContext_noResizeDue true Y1 tid hNoY) hNe hSC hSz4 hE2 hH hS2o hG2 hR2
    hF2, hK.queueNext, hK.regs, hK.ipcBadgeView, ← receiveReturnSchedContextFast_eq]
  have hKl := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => replyRecvTakeLegs i (receiveReturnSchedContextFast true Y tid.val) c tid s epId
      sTcb.queueNextCode core layout rf len badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hKl
  rw [hAX.frameCapRequestOf, hAX.capTargetOf, hT1] at hKl
  unfold performReplyRecvUnlinkedTakeCapsDelivered performReplyRecvUnlinkedTakeCapsLegs
  rw [hX]
  dsimp only
  rw [hKl]

end UnlinkedTake

section UnheldTake

/-- **The take's guard across a pop that leaves the sender's slot alone**: a
step writing only what a pop writes (`popFrame`), the sender's object found
unchanged, keeps the endpoint and the take's in-place guard. -/
theorem takeGuard_of_popFrame {P T : SystemState} (hF : popFrame P T)
    {epId : SeLe4n.ObjId} {ep : Endpoint} {tid sid : SeLe4n.ThreadId} {sTcb : TCB}
    (hE : T.objects[epId]? = some (.endpoint ep))
    (hG : receiveTakesInPlace T epId tid sid sTcb = true) :
    P.objects[epId]? = some (.endpoint ep) ∧ receiveTakesInPlace P epId tid sid sTcb = true :=
  ⟨popAgreeAt_endpoint (hF.2.2.2 epId) hE,
    receiveTakesInPlace_of_frame epId tid sid sTcb sTcb hF.2.2.1
      (fun x => getObjectType?_of_popAgree (hF.2.2.2 x))
      (fun _ hp => getTcb?_isSome_of_popAgree (hF.2.2.2 _) hp) rfl rfl hG⟩

/-- **The take's guard across the reply leg, the unheld pop and its settle**:
on the state they leave, the endpoint is as it was, the sender a thread keeping
every word the take reads, and the take's in-place guard, read on the
pre-state, still holds.  The pop and the settle write the caller's binding, the
reply stack's links and the context, never the sender's slot. -/
theorem popUnheldSettled_takeGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (scId : SeLe4n.SchedContextId) (home : CoreId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hG : receiveTakesInPlace st epId tid s sTcb = true) :
    (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLeg st c rid msg) c scId) home scId).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb1, (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
          (storeReplyLeg st c rid msg) c scId) home scId).objects[s.toObjId]? = some (.tcb sTcb1) ∧
        SenderWordsKept sTcb1 sTcb ∧
        receiveTakesInPlace (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
          (storeReplyLeg st c rid msg) c scId) home scId) epId tid s sTcb1 = true := by
  have hSc' : s.toObjId ≠ c.toObjId := fun e => hSC (SeLe4n.ThreadId.toObjId_injective _ _ e)
  obtain ⟨hE1, sTcb1, hS1, hK, hG1⟩ := storeReplyLeg_takeGuard st c tid rid msg ct rp epId ep s
    sTcb hNo hT hFC hRp hE hS hSC hG
  have hNoT := storeReplyLeg_noResizeDue st c rid msg hNo
  generalize storeReplyLeg st c rid msg = T at hE1 hS1 hG1 hNoT
  have hPt := returnUnheldSchedContextInPlace_tcbAt T c scId hNoT hSc' hS1
  have hFr := returnUnheldSchedContextInPlace_popFrame T c scId hNoT
  generalize returnUnheldSchedContextInPlace T c scId = Rr at hPt hFr
  have hPt' := releaseAgreeAt_of_not_sc (SchedContextOps.settleReturnedContext_agree Rr home scId)
    hPt (fun _ e => by cases e)
  have hF := (settleReturnedContext_popFrame Rr home scId).trans hFr
  obtain ⟨hEP, hGP⟩ := takeGuard_of_popFrame hF hE1 hG1
  exact ⟨hEP, sTcb1, hPt', hK, hGP⟩

/-- **The reply-receive to a caller recording no server meeting a waiting
sender, its reply leg transferring**: under `replyUnheldPopsInPlace`, a reply
leg whose transfer answers `(summary, S2)` on the state the reply leg, the
unheld pop and its settle leave, and on the state the replier's context return
leaves on `S2` a sender `s` at the head of the send queue blocked by a routed
capability-free send, not delivering a fault, whose take writes only its slots,
the composite is the reply's writes, the pop, the transfer, the return, the
take, the replier's priority walk and the caller staged with the transfer's
report. -/
theorem replyRecvOnCore_unheld_take_transfer (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hH : ep.sendQ.head = some s)
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyTransferCaps st tid c grant (SchedContextOps.settleReturnedContext
      (returnUnheldSchedContextInPlace (storeReplyLeg st c rid msg) c
        ⟨replyHeadContextCode st rid - 1⟩) (determineTargetCore st c)
        ⟨replyHeadContextCode st rid - 1⟩) = .ok (summary, S2))
    (hE2 : (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep))
    {sTcb2 : TCB}
    (hT2 : (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2))
    (hG2 : receiveTakesInPlace (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 = .send capAddr mi)
    (hF : sTcb2.ipcFaultSend = false) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
          (PriorityInheritance.propagatePipChainCrossCore
            ((wakeThread ((storePopHead (receiveReturnSchedContext true S2 tid) epId false s
                sTcb2.queueNext).updateTcb s receiverReady) s core).1.updateTcb tid
              (callReceiverTcb (blockedSenderMessage (storePopHead
                (receiveReturnSchedContext true S2 tid) epId false s sTcb2.queueNext)
                s sTcb2))) tid core).1 c summary.capInfo) := by
  generalize hQ : receiveReturnSchedContext true S2 tid = Q at hE2 hT2 hG2 ⊢
  obtain ⟨rp, scId, hRp, hN, hCode, hCRes, hNo, hLC, hFC, hLR, hFR, hPopR, -⟩ :=
    replyUnheldPopsInPlace_pop st c rid msg ct hT hG
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
  have hXf' : replyRecvReplyTransfer none st tid c grant (SchedContextOps.settleReturnedContext
      (returnUnheldSchedContextInPlace (storeReplyLeg st c rid msg) c scId)
      (determineTargetCore st c) scId) = .ok (summary, S2) := hXf
  have hEp2 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE2
  obtain ⟨hRecv, -, -⟩ := receiveTake_delivered Q epId ep tid (some rid) core s sTcb2 capAddr mi
    hE2 hH hT2 hG2 hR hF
  have hNoCall := receiveTake_dequeuedNoCall Q epId ep tid core s sTcb2
    (blockedSenderMessage (storePopHead Q epId false s sTcb2.queueNext) s sTcb2) hE2 hH hT2 hG2
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_none, hEq, hPopR, hXf', hQ, hRecv, hEp2, Option.bind_some, hH]
  simp only [replyRecvPostReceiveDonation, hNoCall, Bool.false_eq_true, ↓reduceIte]
  simp [replyRecvAnswerCaller]

/-- **The reply-receive to a caller recording no server meeting a waiting
sender, its reply transferring nothing, delivered**: the reply leg's writes
(`storeReplyLegReady`), the unheld pop and its settle on the caller's home
core, the take, the replier's priority walk, then the caller's frame and the
replier's frame. -/
@[noinline] def performReplyRecvUnheldTakeLegs (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) : SystemState :=
  replyRecvTakeLegs 0 (receiveReturnSchedContextFast true (SchedContextOps.settleReturnedContext
    (returnUnheldSchedContextInPlace (storeReplyLegReady st c rid) c scId) home scId) tid.val)
    c tid s epId nextCode core layout rf len badge

/-- The inert take to a caller recording no server, the legs
(`performReplyRecvUnheldTakeLegs`) and then the replier's frame
(`writeTakerFrame`), each out of line so the arm releases the replier's register
file between them. -/
@[inline] def performReplyRecvUnheldTakeDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  writeTakerFrame (performReplyRecvUnheldTakeLegs st c tid rid scId home epId s nextCode core layout
    rf len badge) tid w0 w1 w2 w3 w4 w5

/-- **The reply-receive to a caller recording no server meeting a waiting
sender, its reply transferring nothing, is the specification's**: under
`replyUnheldPopsInPlace`, a reply of at most four words transferring no
capability, and a sender `s` at the head of the send queue blocked by a routed
capability-free send, not delivering a fault, whose take writes only its slots
(every check read on the pre-state), the checked arm's result is
`performReplyRecvUnheldTakeDelivered`, the context the reply object heads and
the caller's home read on the pre-state. -/
theorem replyRecvOnCore_unheld_take_delivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true) (hNe : tid ≠ c)
    (hInert : replyTransferInert st tid ct grant = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvUnheldTakeDelivered st c tid rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) epId s sTcb.queueNextCode core layout rf len badge
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5) := by
  obtain ⟨rp, -, hRp, -, -, -, hNo, -, hFC, -, -, -, -⟩ :=
    replyUnheldPopsInPlace_pop st c rid
      { registers := Architecture.regMessageBody layout rf len, badge := badge } ct hT hG
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hSz : ¬ (Architecture.regMessageBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regMessageBody_size]; unfold maxMessageRegisters; omega
  generalize hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId
  generalize hHome : determineTargetCore st c = home
  obtain ⟨hE1, sTcb1, hS1, hK, hG1⟩ := popUnheldSettled_takeGuard st c tid rid
    { registers := Architecture.regMessageBody layout rf len, badge := badge } ct rp scId home
    epId ep s sTcb hNo hT hFC hRp hE hS hSC hGt
  have hNoP := settleReturnedContext_noResizeDue
    (returnUnheldSchedContextInPlace (storeReplyLeg st c rid
      { registers := Architecture.regMessageBody layout rf len, badge := badge }) c scId) home scId
    (returnUnheldSchedContextInPlace_noResizeDue _ c scId (storeReplyLeg_noResizeDue st c rid _ hNo))
  have hXf := replyTransferCaps_of_inert st tid c grant ct hTc hInert
    (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace (storeReplyLeg st c rid
      { registers := Architecture.regMessageBody layout rf len, badge := badge }) c scId) home scId)
  obtain ⟨hE2, sTcb2, hS2, hK2, hG2⟩ := receiveReturnSchedContext_takeGuard true _ tid hNoP hE1
    hS1 hG1
  have hKt := hK2.trans hK
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout
      sTcb2.registerContext 32 = .send capAddr mi := by rw [hKt.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hKt.faultSend]; exact hF
  rw [← hSc, ← hHome] at hXf
  rw [replyRecvOnCore_unheld_take_transfer st epId tid c rid _ grant core ct ep0 ep s capAddr mi
    hSz hT hIpc hRO hG hH hXf (by rw [hSc, hHome]; exact hE2) (by rw [hSc, hHome]; exact hS2)
    (by rw [hSc, hHome]; exact hG2) hR2 hF2]
  rw [hSc, hHome]
  dsimp only
  rw [CapTransferSummary.capInfo_empty]
  have h1 := storeReplyLegReady_noResizeDue st c rid hNo
  have h2' := settleReturnedContext_noResizeDue _ home scId
    (returnUnheldSchedContextInPlace_noResizeDue _ c scId h1)
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo, returnUnheldSchedContextInPlace_msg c id _ id _ c scId h1,
    settleReturnedContext_msg, receiveReturnSchedContext_msg c id _ id true _ tid h2' hNe.symm]
    at hE2 hS2 hG2 ⊢
  rw [replyRecvTakeFrame_staged _ c tid s epId ep sTcb2 core layout rf len badge 0 capAddr mi
    (receiveReturnSchedContext_noResizeDue true _ tid h2') hNe hSC hSz4 hE2 hH hS2 hG2 hR2 hF2,
    hKt.queueNext, hKt.regs, hKt.ipcBadgeView]
  unfold performReplyRecvUnheldTakeDelivered performReplyRecvUnheldTakeLegs
  rw [receiveReturnSchedContextFast_eq]

/-- **The reply-receive to a caller recording no server meeting a waiting
sender, its reply leg transferring, delivered**: the reply leg's writes, the
unheld pop and its settle, the transfer in place on no endpoint, the take, the
replier's priority walk, then the caller's frame with the transfer's report and
the replier's frame. -/
@[noinline] def performReplyRecvUnheldTakeCapsLegs (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := SchedContextOps.settleReturnedContext
    (returnUnheldSchedContextInPlace (storeReplyLegReady st c rid) c scId) home scId
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    replyRecvTakeLegs (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (receiveReturnSchedContextFast true
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X) tid.val)
      c tid s epId nextCode core layout rf len badge

/-- The installing take to a caller recording no server, its legs
(`performReplyRecvUnheldTakeCapsLegs`) and then the replier's frame
(`writeTakerFrame`). -/
@[inline] def performReplyRecvUnheldTakeCapsDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (w0 w1 w2 w3 w4 w5 : UInt64)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  writeTakerFrame (performReplyRecvUnheldTakeCapsLegs st c tid rid scId home epId s nextCode core
    layout rf len badge sv sb sroot count rv rb rroot) tid w0 w1 w2 w3 w4 w5

/-- **The reply-receive to a caller recording no server meeting a waiting
sender, its reply leg transferring, is the specification's**: under the guard of
`replyRecvOnCore_unheld_take_delivered` (its inert transfer replaced by a
granting replier whose frame asks for `count` capabilities, `hReq`), the checked
arm's result is `performReplyRecvUnheldTakeCapsDelivered`. -/
theorem replyRecvOnCore_unheld_take_capsDelivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (stcb : TCB) (count : Nat)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true) (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvUnheldTakeCapsDelivered st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId s sTcb.queueNextCode core
        layout rf len badge
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5
        stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] count ct.spaceCells[2] ct.ipcBuffer
        ct.spaceCells[0]) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  have hSz : ¬ (Architecture.regMessageBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regMessageBody_size]; unfold maxMessageRegisters; omega
  generalize hMsg : ({ registers := Architecture.regMessageBody layout rf len, badge := badge } :
    IpcMessage) = msg
  obtain ⟨rp, scId, hRp, -, hCode, -, hNo, -, hFC, -⟩ :=
    replyUnheldPopsInPlace_pop st c rid msg ct hT hG
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  obtain ⟨hE1, sTcb1, hS1o, hK1, hG1⟩ := popUnheldSettled_takeGuard st c tid rid msg ct rp scId
    (determineTargetCore st c) epId ep s sTcb hNo hT hFC hRp hE hS hSC hGt
  have hNoX := storeReplyLegReady_noResizeDue st c rid hNo
  have hAX := ipcBufferReadsAgree_storeReplyLegReady st c rid hNo
  have hP1 : SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLeg st c rid msg) c scId) (determineTargetCore st c) scId =
      (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLegReady st c rid) c scId) (determineTargetCore st c) scId).mapTcbInPlace c
        (holdMessage msg) := by
    rw [storeReplyLeg_eq_hold _ _ _ _ hNo, returnUnheldSchedContextInPlace_msg c id _ id _ c scId hNoX,
      settleReturnedContext_msg]
  have hAP := (ipcBufferReadsAgree_settleReturnedContext _ (determineTargetCore st c) scId).trans
    ((ipcBufferReadsAgree_returnUnheldSchedContextInPlace _ c scId hNoX).trans hAX)
  have hNoP := settleReturnedContext_noResizeDue _ (determineTargetCore st c) scId
    (returnUnheldSchedContextInPlace_noResizeDue _ c scId hNoX)
  generalize hX : SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
    (storeReplyLegReady st c rid) c scId) (determineTargetCore st c) scId = X at hP1 hNoP
  have hAX' : ipcBufferReadsAgree X st := hX ▸ hAP
  rw [hP1] at hE1 hS1o hG1
  obtain ⟨sm, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 sm hNoP hT1
  have hHT : receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
      (X.mapTcbInPlace c (holdMessage msg)) = .ok (sm, Y1.mapTcbInPlace c (holdMessage msg)) := by
    rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoP, hT1]
    rfl
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAX')
    ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoP) c.toObjId stcb ct count hHT).1
  obtain ⟨hE2', sTcb2', hS2o', hK2', hG2'⟩ := takeGuard_of_transferFrame hFr hE1 hS1o hG1
  obtain ⟨hE2, sTcb2, hS2o, hK2, hG2⟩ := receiveReturnSchedContext_takeGuard true _ tid
    ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNoY) hE2' hS2o' hG2'
  have hK := hK2.trans (hK2'.trans hK1)
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout
      sTcb2.registerContext 32 = .send capAddr mi := by rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  have hXf : replyTransferCaps st tid c true
      (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLeg st c rid msg) c ⟨replyHeadContextCode st rid - 1⟩)
        (determineTargetCore st c) ⟨replyHeadContextCode st rid - 1⟩) =
      .ok (sm, Y1.mapTcbInPlace c (holdMessage msg)) := by
    unfold replyTransferCaps
    rw [hReq, hTgt, hSc, hP1, hHT]
  rw [replyRecvOnCore_unheld_take_transfer st epId tid c rid msg true core ct ep0 ep s capAddr mi
    (hMsg ▸ hSz) hT hIpc hRO hG hH hXf hE2 hS2o hG2 hR2 hF2]
  dsimp only
  subst hMsg
  rw [CapTransferSummary.capInfo_empty]
  rw [receiveReturnSchedContext_msg c id _ id true Y1 tid hNoY hNe.symm] at hE2 hS2o hG2 ⊢
  rw [replyRecvTakeFrame_staged _ c tid s epId ep sTcb2 core layout rf len badge sm.capInfo capAddr
    mi (receiveReturnSchedContext_noResizeDue true Y1 tid hNoY) hNe hSC hSz4 hE2 hH hS2o hG2 hR2
    hF2, hK.queueNext, hK.regs, hK.ipcBadgeView, ← receiveReturnSchedContextFast_eq]
  have hKl := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => replyRecvTakeLegs i (receiveReturnSchedContextFast true Y tid.val) c tid s epId
      sTcb.queueNextCode core layout rf len badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hKl
  rw [hAX'.frameCapRequestOf, hAX'.capTargetOf, hT1] at hKl
  unfold performReplyRecvUnheldTakeCapsDelivered performReplyRecvUnheldTakeCapsLegs
  rw [hSc, hX]
  dsimp only
  rw [hKl]

end UnheldTake

end SeLe4n.Kernel
