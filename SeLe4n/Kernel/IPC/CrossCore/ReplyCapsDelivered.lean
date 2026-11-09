-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.CallCapsDelivered
import SeLe4n.Kernel.IPC.CrossCore.LongReplyInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyInPlace

/-!
# A capability-carrying reply, delivered in place

seL4's `doReplyTransfer` runs `doIPCTransfer` on no endpoint under the reply
capability's grant right: the replier's extra capabilities go to the caller's
receive slot, none unwraps, and the caller's frame reports the transfer.  The
specification wakes the caller holding the message, walks the server's
priority chain, transfers on the state that left (reading the replier's
request and the caller's receive slot from the state before the reply), then
stages the caller's frame with the report.  The in-place reply
(`performReplyCapsDelivered`) wakes the caller holding nothing, walks the same
chain, runs the transfer in place (`capTransferK` with no endpoint to unwrap
at) and writes the frame carrying the report straight into the caller's
registers (`replyRendezvousCaps_eq_delivered`), which is the checked reply's
answer when its dispatch runs in place (`replyTransferChecked_caps_inPlace`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood

/-- **The reply that transfers capabilities, delivered**: the caller woken
without the message, the server's priority walk, the transfer in place on no
endpoint, then the caller's frame with the transfer's report.  The replier and
the caller enter as the words the transfer reads of them, read before the
reply's writes. -/
@[noinline] def performReplyCapsDelivered (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  let X := (PriorityInheritance.propagatePipChainCrossCore
    (storeReplyRendezvousReady st c server rid) server core).1
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverCapsFrame
      (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
      c layout rf len badgeWord badged

/-- **The specification's reply transfer after the in-place dispatch is the
delivered reply**, for a message of at most four words read in the replier's
registers: the transfer on no endpoint after the reply's writes and the
priority walk, then the caller's stage with the transfer's report. -/
theorem replyRendezvousCaps_eq_delivered (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId) (stcb ct : TCB)
    (count : Nat)
    (hNo : st.objects.noResizeDue) (hSz : Architecture.regMessageLength layout len ≤ 4) :
    (match receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
        (PriorityInheritance.propagatePipChainCrossCore
          (storeReplyRendezvous st c server rid
            { registers := Architecture.regMessageBody layout rf len,
              badge := SeLe4n.Badge.opt badgeWord badged }) server core).1 with
      | .ok (s, st'') =>
        (.ok ((), Architecture.stageDeliveredMessage st'' c s.capInfo) :
          Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyCapsDelivered st c server rid layout rf len badgeWord badged core
        stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot count ct.vspaceRoot ct.ipcBuffer
        ct.cspaceRoot) := by
  have hNoS := storeReplyRendezvousReady_noResizeDue st c server rid hNo
  have hNoX := propagatePipChainCrossCore_noResizeDue _ server core hNoS
  have hA := (ipcBufferReadsAgree_propagatePipChainCrossCore _ server core hNoS).trans
    (ipcBufferReadsAgree_storeReplyRendezvousReady st c server rid hNo)
  unfold performReplyCapsDelivered
  have hK := capTransferK_eq_at
    (PriorityInheritance.propagatePipChainCrossCore
      (storeReplyRendezvousReady st c server rid) server core).1
    c.toObjId false stcb count ct
    (fun i Y => deliverCapsFrame i Y c layout rf len badgeWord badged)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hK
  rw [hK, hA.frameCapRequestOf, hA.capTargetOf]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoS]
  generalize (PriorityInheritance.propagatePipChainCrossCore
    (storeReplyRendezvousReady st c server rid) server core).1 = Y0 at hNoX
  rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ Y0 hNoX]
  obtain ⟨s, Y1, hT⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) Y0
  have hNo1 := receiveTransferCaps_noResizeDue _ _ _ Y0 Y1 s hNoX hT
  rw [hT]
  simp only [mapStepState]
  rw [stageDeliveredMessage_holdMessage_caps _ _ _ _ hNo1
      (by rw [Architecture.regMessageBody_size]; exact hSz),
    returnFrameOfMessage_regMessageBody_caps]
  rfl

/-! ### The request a routed reply makes -/

/-- The extra-capability count a routed reply's frame names is the count its
message-info word holds (`routedExtraCaps`). -/
theorem routedExtraCaps_eq_of_reply {rf : SeLe4n.RegisterFile} {capAddr : SeLe4n.CPtr}
    {mi : MessageInfo}
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout rf =
      .reply capAddr mi) :
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

/-- **The request a routed reply makes**: under the grant right, the replier's
frame asks for the count its message-info word names (`replyCapRequest` is
`frameCapRequestOf`). -/
theorem replyCapRequest_of_routedReply (st : SystemState) (replier : SeLe4n.ThreadId)
    (stcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hS : st.getTcb? replier = some stcb)
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
      stcb.registerContext = .reply capAddr mi) :
    replyCapRequest st replier true =
      frameCapRequestOf st stcb (routedExtraCaps stcb.registerContext) := by
  obtain ⟨decoded, hDec, -, -, -, hMi, -⟩ :=
    Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReply st replier
      SeLe4n.arm64DefaultLayout stcb.registerContext 32 capAddr mi
      (by rw [Architecture.RegisterDecode.registerRoutedSyscall_default]; exact hR)
  unfold replyCapRequest
  rw [hS]
  simp only [senderFrameCapRequest, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    blockedSenderDecode, hDec, hMi, routedExtraCaps_eq_of_reply hR]
  rfl

/-- **The checked reply transfer that moves capabilities, in place**: under
the flow gate and `replyWakesInPlace`, a granting reply of at most four words
to an unfaulted caller blocked on it, from a replier whose frame routes as a
reply, commits `performReplyCapsDelivered`'s state. -/
theorem replyTransferChecked_caps_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c server : SeLe4n.ThreadId) (ct stcb : TCB) (ep : SeLe4n.ObjId)
    (rid : SeLe4n.ReplyId) (mi' : MessageInfo) (regs : Array SeLe4n.RegValue)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hSz : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hSRes : server.isReserved = false)
    (hG : replyWakesInPlace st c ct rid = true)
    (hNoF : ct.faultWords.isFault = false)
    (hFlow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf c) = true)
    (hS : st.getTcb? replier = some stcb)
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
      stcb.registerContext = .reply capAddr mi) :
    replyTransferOnCoreChecked ctx replier c mi' regs
        { registers := Architecture.regMessageBody layout rf len,
          badge := SeLe4n.Badge.opt badgeWord badged } true core st =
      .ok ((), performReplyCapsDelivered st c server rid layout rf len badgeWord badged core
        stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot (routedExtraCaps stcb.registerContext)
        ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot) := by
  have hPF : ct.pendingFault = none := TCB.pendingFault_eq_none_of_not_isFault hNoF
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNF : threadHasPendingFault st c = false := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_none]
  have hSz' : ¬ (Architecture.regMessageBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regMessageBody_size]
    have : (4 : Nat) ≤ maxMessageRegisters := by decide
    omega
  obtain ⟨sgi, hD⟩ := replyDispatch_inPlace st replier c server ct ep rid
    { registers := Architecture.regMessageBody layout rf len,
      badge := SeLe4n.Badge.opt badgeWord badged } core hSz' hT hIpc hRO hSRes hG
  unfold replyTransferOnCoreChecked
  rw [hNF, endpointReplyCrossCoreDispatchChecked_flow_allowed _ _ _ _ _ _ hFlow]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hD]
  simp only []
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  unfold replyTransferCaps
  rw [replyCapRequest_of_routedReply st replier stcb capAddr mi hS hR, hTgt]
  exact replyRendezvousCaps_eq_delivered st c server rid layout rf len badgeWord badged core
    stcb ct _ (replyWakesInPlace_noResizeDue hG) hSz

end SeLe4n.Kernel
