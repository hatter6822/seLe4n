-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvCapsDelivered

/-!
# The long reply-receive whose reply pops a donation, in place

A reply-receive of more than four words whose reply object heads the stack of a
context (the server's loan, seL4-MCS's `reply_pop` between the legs, or a
context no thread holds, its server finalised) writes in place as the short one
does (`replyRecvOnCore_donated_delivered`, `replyRecvOnCore_unheld_delivered`),
with the long frame of `replyRecvOnCore_blocks_deliveredLong`: the replier's
MR1..MR3 and first overflow word in the caller's saved registers and its other
overflow words copied into the caller's buffer.  Every write between the
replier's buffer read and the copy keeps every buffer read
(`ipcBufferReadsAgree`), so the copy reads what the specification's message
holds.  Each shape has an inert and an installing performer.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

theorem ipcBufferReadsAgree_descheduleAtPlacement (s : SystemState) (t : SeLe4n.ThreadId) :
    ipcBufferReadsAgree (descheduleAtPlacement s t) s := by
  unfold descheduleAtPlacement descheduleAt
  split
  · exact ipcBufferReadsAgree_removeRunnableOnCore _ _ _
  · exact .refl _

theorem ipcBufferReadsAgree_storeReplyRecvDonatedTail (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (hNo : Y.objects.noResizeDue) :
    ipcBufferReadsAgree (storeReplyRecvDonatedTail Y tid rid epId tailCode core) Y := by
  have h2 := storeReceiveBlock_noResizeDue _ epId tid tailCode (rid.val + 1) hNo
  have h3 := removeRunnableOnCore_noResizeDue _ tid core h2
  have h4 := descheduleAtPlacement_noResizeDue _ tid h3
  exact (ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core h4).trans
    ((ipcBufferReadsAgree_descheduleAtPlacement _ tid).trans
      ((ipcBufferReadsAgree_removeRunnableOnCore _ tid core).trans
        (ipcBufferReadsAgree_storeReceiveBlock _ epId tid tailCode _ hNo)))

theorem storeReplyRecvDonatedTail_noResizeDue (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (hNo : Y.objects.noResizeDue) :
    (storeReplyRecvDonatedTail Y tid rid epId tailCode core).objects.noResizeDue :=
  propagatePipChainCrossCore_noResizeDue _ _ _ (descheduleAtPlacement_noResizeDue _ _
    (removeRunnableOnCore_noResizeDue _ _ _ (storeReceiveBlock_noResizeDue _ _ _ _ _ hNo)))

/-- **The blocking receive leg's tail stages the caller's held long message as
the long frame**, the server it blocks staging nothing: on a state `Y` where the
server, its receive blocked, is no longer ready, staging the caller holding the
long message read in `Z` and then the server is the long frame on
`storeReplyRecvBlockTail`, its overflow words read in that state, which reads
every buffer as `Z` does (`hW`). -/
theorem replyRecvBlockTail_stagedLong (Y Z : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (capInfo : Nat)
    (hNo : Y.objects.noResizeDue) (hNe : tid ≠ c) (hLen : 5 ≤ len)
    (hW : ipcWordReadsAgree (storeReplyRecvBlockTail Y tid rid epId tailCode core) Z)
    (hB : ∃ x, (removeRunnableOnCore (storeReceiveBlock (Y.mapTcbInPlace c (holdMessage
        { registers := longReplyRecvRegs rf Z tid len, badge := badge })) epId tid tailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core).getTcb? tid = some x ∧
      x.ipcState = .blockedOnReceive epId) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock (Y.mapTcbInPlace c (holdMessage
            { registers := longReplyRecvRegs rf Z tid len, badge := badge })) epId tid tailCode
            (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c capInfo) tid 0 =
      deliverLongReplyRecvCapsFrame capInfo (storeReplyRecvBlockTail Y tid rid epId tailCode core)
        c rf len tid badge := by
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨t, hT1, hBk⟩ := hB
  have h3 := removeRunnableOnCore_noResizeDue _ tid core
    (storeReceiveBlock_noResizeDue _ epId tid tailCode (SeLe4n.ReplyId.optCode (some rid)) hNo)
  rw [storeReceiveBlock_msg _ _ _ _ _ _ _ hNo hNe, removeRunnableOnCore_msg,
    SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hT1
  obtain ⟨x, hX, hEq⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h3 tid t hT1
  rw [storeReceiveBlock_msg _ _ _ _ _ _ _ hNo hNe, removeRunnableOnCore_msg,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ h3]
  have hTailEq : (PriorityInheritance.propagatePipChainCrossCore (removeRunnableOnCore
      (storeReceiveBlock Y epId tid tailCode (SeLe4n.ReplyId.optCode (some rid))) tid core)
      tid core).1 = storeReplyRecvBlockTail Y tid rid epId tailCode core := rfl
  rw [hTailEq, ← deliverLongReplyRecvFrame_eq _ Z c tid rf len badge capInfo
    (storeReplyRecvBlockTail_noResizeDue Y tid rid epId tailCode core hNo) hW hLen]
  unfold deliverLongReplyRecvCapsFrame
  exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x
    (by rw [deliverLongReplyRecvFrame_getTcb?_ne _ _ _ _ _ _ _ _ hCT]; exact hX)
    (by rw [hEq, hBk]; exact fun h => by cases h)

/-- The donated receive leg's tail, as `replyRecvBlockTail_stagedLong`, the
server also descheduled from the context it gave back. -/
theorem replyRecvDonatedTail_stagedLong (Y Z : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (capInfo : Nat)
    (hNo : Y.objects.noResizeDue) (hNe : tid ≠ c) (hLen : 5 ≤ len)
    (hW : ipcWordReadsAgree (storeReplyRecvDonatedTail Y tid rid epId tailCode core) Z)
    (hB : ∃ x, (removeRunnableOnCore (storeReceiveBlock (Y.mapTcbInPlace c (holdMessage
        { registers := longReplyRecvRegs rf Z tid len, badge := badge })) epId tid tailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core).getTcb? tid = some x ∧
      x.ipcState = .blockedOnReceive epId) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (descheduleAtPlacement (removeRunnableOnCore (storeReceiveBlock (Y.mapTcbInPlace c
            (holdMessage { registers := longReplyRecvRegs rf Z tid len, badge := badge })) epId tid
            tailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid) tid core).1 c capInfo)
        tid 0 =
      deliverLongReplyRecvCapsFrame capInfo (storeReplyRecvDonatedTail Y tid rid epId tailCode core)
        c rf len tid badge := by
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨t, hT1, hBk⟩ := hB
  have h3 := removeRunnableOnCore_noResizeDue _ tid core
    (storeReceiveBlock_noResizeDue _ epId tid tailCode (SeLe4n.ReplyId.optCode (some rid)) hNo)
  have h5 := descheduleAtPlacement_noResizeDue _ tid h3
  rw [storeReceiveBlock_msg _ _ _ _ _ _ _ hNo hNe, removeRunnableOnCore_msg,
    SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hT1
  obtain ⟨x1, hX1, e1⟩ := descheduleAtPlacement_ipcStateCarried _ tid tid t hT1
  obtain ⟨x, hX, hEq⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h5 tid x1 hX1
  rw [storeReceiveBlock_msg _ _ _ _ _ _ _ hNo hNe, removeRunnableOnCore_msg,
    descheduleAtPlacement_msg, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ h5]
  have hTailEq : (PriorityInheritance.propagatePipChainCrossCore (descheduleAtPlacement
      (removeRunnableOnCore (storeReceiveBlock Y epId tid tailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core) tid) tid core).1 =
      storeReplyRecvDonatedTail Y tid rid epId tailCode core := rfl
  rw [hTailEq, ← deliverLongReplyRecvFrame_eq _ Z c tid rf len badge capInfo
    (storeReplyRecvDonatedTail_noResizeDue Y tid rid epId tailCode core hNo) hW hLen]
  unfold deliverLongReplyRecvCapsFrame
  exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x
    (by rw [deliverLongReplyRecvFrame_getTcb?_ne _ _ _ _ _ _ _ _ hCT]; exact hX)
    (by rw [hEq, e1, hBk]; exact fun h => by cases h)

/-! ### The donated long reply-receive -/

/-- **The donated long reply-receive, its reply transferring nothing,
delivered**: the reply's writes, the pop and its settle, the server's block,
deschedule and priority walk, then the long frame. -/
@[noinline] def performReplyRecvDonatedDeliveredLong (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) : SystemState :=
  deliverLongReplyRecvCapsFrame 0 (storeReplyRecvDonatedTail
    (popDonationSettledInPlace (storeReplyRendezvousReady st c tid rid) c tid scId home) tid rid
    epId tailCode core) c rf len tid badge

/-- **The donated long reply-receive, delivered**: under the guard of
`replyRecvOnCore_donated_inPlace` and a message of `len` words, more than four,
the checked arm's result is `performReplyRecvDonatedDeliveredLong`. -/
theorem replyRecvOnCore_donated_deliveredLong (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (grant : Bool) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hLen : 5 ≤ len) (hSz : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : enqueueAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : replyTransferInert st tid ct grant = true) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvDonatedDeliveredLong st c tid rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) epId ep.recvTailCode rf len badge core) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hNe', hNo, _⟩ := replyPopsInPlace_donation st c tid rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } ct hT hSRes hG
  have hNe : tid ≠ c := fun e => hNe' e.symm
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvOnCore_donated_inPlace st epId tid c rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core
    ct ep0 rt ep rp hSz hT hIpc hRO hSRes hG hE hS hR hA hEnq hRp hStash hRec hInert
  rw [hEq]
  simp only [CapTransferSummary.capInfo_empty]
  revert hX
  generalize (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId
  intro hX
  have h1 := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have hNoP := popDonationSettledInPlace_noResizeDue _ c tid scId (determineTargetCore st c) h1
  have hAP := (ipcBufferReadsAgree_settleReturnedContext _ (determineTargetCore st c) scId).trans
    ((ipcBufferReadsAgree_returnDonatedSchedContextInPlace _ tid c scId h1).trans
      (ipcBufferReadsAgree_storeReplyRendezvousReady st c tid rid hNo))
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    popDonationSettledInPlace_msg c id _ id _ c tid scId _ h1 (fun e => hNe e.symm)] at hX ⊢
  exact congrArg (fun Z => (.ok ((), Z) : Except KernelError (Unit × SystemState)))
    (replyRecvDonatedTail_stagedLong _ st c tid rid epId ep.recvTailCode core rf len badge 0 hNoP
      hNe hLen ((ipcBufferReadsAgree_storeReplyRecvDonatedTail _ tid rid epId ep.recvTailCode core
        hNoP).words.trans hAP.words) ⟨x, hX, hB⟩)

/-! ### The long reply-receive answering a caller recording no server -/

/-- **The unheld long reply-receive, its reply transferring nothing,
delivered**: the reply leg's writes, the unheld pop and its settle, the
replier's block and priority walk, then the long frame. -/
@[noinline] def performReplyRecvUnheldDeliveredLong (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) : SystemState :=
  deliverLongReplyRecvCapsFrame 0 (storeReplyRecvBlockTail
    (SchedContextOps.settleReturnedContext
      (returnUnheldSchedContextInPlace (storeReplyLegReady st c rid) c scId) home scId) tid rid
    epId tailCode core) c rf len tid badge

/-- **The unheld long reply-receive, delivered**: under the guard of
`replyRecvOnCore_unheld_inPlace` and a message of `len` words, more than four,
the checked arm's result is `performReplyRecvUnheldDeliveredLong`. -/
theorem replyRecvOnCore_unheld_deliveredLong (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (grant : Bool) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hLen : 5 ≤ len) (hSz : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : replyTransferInert st tid ct grant = true) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvUnheldDeliveredLong st c tid rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) epId ep.recvTailCode rf len badge core) := by
  obtain ⟨_, _, _, _, _, _, hNo, _⟩ := replyUnheldPopsInPlace_pop st c rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } ct hT hG
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvOnCore_unheld_inPlace st epId tid c rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core
    ct ep0 rt ep rp hSz hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hStash hRec hInert
  rw [hEq]
  simp only [CapTransferSummary.capInfo_empty]
  revert hX
  generalize (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId
  intro hX
  have h1 := storeReplyLegReady_noResizeDue st c rid hNo
  have hNoP := settleReturnedContext_noResizeDue _ (determineTargetCore st c) scId
    (returnUnheldSchedContextInPlace_noResizeDue _ c scId h1)
  have hAP := (ipcBufferReadsAgree_settleReturnedContext _ (determineTargetCore st c) scId).trans
    ((ipcBufferReadsAgree_returnUnheldSchedContextInPlace _ c scId h1).trans
      (ipcBufferReadsAgree_storeReplyLegReady st c rid hNo))
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo, returnUnheldSchedContextInPlace_msg c id _ id _ c scId h1,
    settleReturnedContext_msg] at hX ⊢
  exact congrArg (fun Z => (.ok ((), Z) : Except KernelError (Unit × SystemState)))
    (replyRecvBlockTail_stagedLong _ st c tid rid epId ep.recvTailCode core rf len badge 0 hNoP
      hNe hLen ((ipcBufferReadsAgree_storeReplyRecvBlockTail _ tid rid epId ep.recvTailCode core
        hNoP).words.trans hAP.words) ⟨x, hX, hB⟩)

/-- **The donated long reply-receive whose reply leg transfers, delivered**: as
`performReplyRecvDonatedCapsDelivered`, with the long frame. -/
@[noinline] def performReplyRecvDonatedCapsDeliveredLong (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  let X := popDonationSettledInPlace (storeReplyRendezvousReady st c tid rid) c tid scId home
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverLongReplyRecvCapsFrame
      (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (storeReplyRecvDonatedTail
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
        tid rid epId tailCode core)
      c rf len tid badge

/-- **The donated long reply-receive whose reply leg transfers, delivered**:
as `replyRecvOnCore_donated_capsDelivered`, for a message of `len` words, more
than four, read in the replier's registers and buffer. -/
theorem replyRecvOnCore_donated_capsDeliveredLong (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (stcb : TCB) (count : Nat)
    (hLen : 5 ≤ len) (hSz : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : enqueueAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count)
    (hW : replyTransferStoresInPlace st c.toObjId stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
      count ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot = true) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvDonatedCapsDeliveredLong st c tid rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) epId ep.recvTailCode rf len badge core stcb.vspaceRoot
        stcb.ipcBuffer stcb.cspaceRoot count ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  generalize hMsg : ({ registers := longReplyRecvRegs rf st tid len, badge := badge } :
    IpcMessage) = msg
  obtain ⟨rp', scId, sc, hRp', hN, hScO, hHead, hBelow, hCode, -, hNe', hNo, -, hFC, -⟩ :=
    replyPopsInPlace_donation st c tid rid msg ct hT hSRes hG
  rw [hRp] at hRp'
  cases hRp'
  have hNe : tid ≠ c := fun e => hNe' e.symm
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := popDonationSettled_receiveGuard st c tid rid msg ct rp
    epId ep rt scId sc (determineTargetCore st c) hNo hT hFC hRp hN hScO hHead hBelow
    hNe hE hR hA hEnq hStash hRec
  have hNoX := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have hAX := ipcBufferReadsAgree_storeReplyRendezvousReady st c tid rid hNo
  obtain ⟨hIX, hLX⟩ := storeReplyRendezvousReady_fields st c tid rid hNo
  have hP1 : popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid scId
      (determineTargetCore st c) =
      (popDonationSettledInPlace (storeReplyRendezvousReady st c tid rid) c tid scId
        (determineTargetCore st c)).mapTcbInPlace c (holdMessage msg) := by
    rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]
    exact popDonationSettledInPlace_msg c id _ id _ c tid scId _ hNoX hNe'
  have hFrP := (settleReturnedContext_popFrame _ (determineTargetCore st c) scId).trans
    (returnDonatedSchedContextInPlace_popFrame (storeReplyRendezvousReady st c tid rid) tid c scId
      hNoX)
  have hAP := (ipcBufferReadsAgree_settleReturnedContext _ (determineTargetCore st c) scId).trans
    ((ipcBufferReadsAgree_returnDonatedSchedContextInPlace _ tid c scId hNoX).trans hAX)
  have hNoP := popDonationSettledInPlace_noResizeDue _ c tid scId (determineTargetCore st c) hNoX
  generalize hX : popDonationSettledInPlace (storeReplyRendezvousReady st c tid rid) c tid scId
    (determineTargetCore st c) = X at hP1 hNoP
  have hAX' : ipcBufferReadsAgree X st := hX ▸ hAP
  have hIX' : X.objectIndexSet = st.objectIndexSet := hX ▸ hFrP.1.trans hIX
  have hLX' : X.lifecycle = st.lifecycle := hX ▸ hFrP.2.1.trans hLX
  rw [hP1] at hE1 hR1 hG1
  obtain ⟨s, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 s hNoP hT1
  have hHT : receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
      (X.mapTcbInPlace c (holdMessage msg)) = .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoP, hT1]
    rfl
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAX')
    hIX' hLX' ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoP) c.toObjId stcb ct count hW hHT).1
  obtain ⟨hE2, ⟨rt2, hR2, hA2⟩, hG2⟩ := receiveGuard_of_transferFrame hFr hE1 hR1 hA1 hG1
  have hXf : replyTransferCaps st tid c true
      (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c)) =
      .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    unfold replyTransferCaps
    rw [hReq, hTgt, hSc, hP1, hHT]
  rw [replyRecvOnCore_donated_transfer st epId tid c rid msg true core ct ep0 ep rp (hMsg ▸ hSz) hT
    hIpc hRO hSRes hG hS hRp hXf hE2 hR2 hA2 hG2]
  dsimp only
  subst hMsg
  simp only [CapTransferSummary.capInfo_empty]
  obtain ⟨t2, hT2, hB2⟩ := receiveBlock_receiver_blocked _ epId ep tid rt2 (some rid) core hE2 hR2
    hA2 hG2
  have hWY := ipcWordReadsAgree_receiveTransferCaps _ _ _ hNoP hT1
  rw [replyRecvDonatedTail_stagedLong Y1 st c tid rid epId ep.recvTailCode core rf len badge s.capInfo hNoY hNe
    hLen ((ipcBufferReadsAgree_storeReplyRecvDonatedTail Y1 tid rid epId ep.recvTailCode core hNoY).words.trans
      (hWY.trans hAX'.words)) ⟨t2, hT2, hB2⟩]
  have hK := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => deliverLongReplyRecvCapsFrame i (storeReplyRecvDonatedTail Y tid rid epId ep.recvTailCode
      core) c rf len tid badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hK
  rw [hAX'.frameCapRequestOf, hAX'.capTargetOf, hT1] at hK
  unfold performReplyRecvDonatedCapsDeliveredLong
  rw [hSc, hX]
  exact congrArg (fun Z => (.ok ((), Z) : Except KernelError (Unit × SystemState))) hK.symm


/-- **The unheld long reply-receive whose reply leg transfers, delivered**: as
`performReplyRecvUnheldCapsDelivered`, with the long frame. -/
@[noinline] def performReplyRecvUnheldCapsDeliveredLong (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  let X := SchedContextOps.settleReturnedContext
    (returnUnheldSchedContextInPlace (storeReplyLegReady st c rid) c scId) home scId
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverLongReplyRecvCapsFrame
      (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (storeReplyRecvBlockTail
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
        tid rid epId tailCode core)
      c rf len tid badge

/-- **The unheld long reply-receive whose reply leg transfers, delivered**: as
`replyRecvOnCore_unheld_capsDelivered`, for a message of `len` words, more than
four, read in the replier's registers and buffer. -/
theorem replyRecvOnCore_unheld_capsDeliveredLong (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (stcb : TCB) (count : Nat)
    (hLen : 5 ≤ len) (hSz : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count)
    (hW : replyTransferStoresInPlace st c.toObjId stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
      count ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot = true) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvUnheldCapsDeliveredLong st c tid rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) epId ep.recvTailCode rf len badge core stcb.vspaceRoot
        stcb.ipcBuffer stcb.cspaceRoot count ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  generalize hMsg : ({ registers := longReplyRecvRegs rf st tid len, badge := badge } :
    IpcMessage) = msg
  obtain ⟨rp', scId, hRp', hN, hCode, -, hNo, -, hFC, -⟩ :=
    replyUnheldPopsInPlace_pop st c rid msg ct hT hG
  rw [hRp] at hRp'
  cases hRp'
  obtain ⟨rp2, scId2, sc, hRp2, hN2, hScO, hHead, hBelow⟩ := replyUnheldPopsInPlace_stack st c rid hG
  rw [hRp] at hRp2
  cases hRp2
  rw [hN] at hN2
  injection hN2 with hN2
  injection hN2 with hN2
  subst hN2
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := popUnheldSettled_receiveGuard st c tid rid msg ct rp
    epId ep rt scId sc (determineTargetCore st c) hNo hT hFC hRp hN hScO hHead hBelow hNe hE hR
    hA hEnq hStash hRec
  have hNoX := storeReplyLegReady_noResizeDue st c rid hNo
  have hAX := ipcBufferReadsAgree_storeReplyLegReady st c rid hNo
  obtain ⟨hIX, hLX⟩ := storeReplyLegReady_fields st c rid hNo
  have hP1 : SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLeg st c rid msg) c scId) (determineTargetCore st c) scId =
      (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLegReady st c rid) c scId) (determineTargetCore st c) scId).mapTcbInPlace c
        (holdMessage msg) := by
    rw [storeReplyLeg_eq_hold _ _ _ _ hNo, returnUnheldSchedContextInPlace_msg c id _ id _ c scId hNoX,
      settleReturnedContext_msg]
  have hFrP := (settleReturnedContext_popFrame _ (determineTargetCore st c) scId).trans
    (returnUnheldSchedContextInPlace_popFrame (storeReplyLegReady st c rid) c scId hNoX)
  have hAP := (ipcBufferReadsAgree_settleReturnedContext _ (determineTargetCore st c) scId).trans
    ((ipcBufferReadsAgree_returnUnheldSchedContextInPlace _ c scId hNoX).trans hAX)
  have hNoP := settleReturnedContext_noResizeDue _ (determineTargetCore st c) scId
    (returnUnheldSchedContextInPlace_noResizeDue _ c scId hNoX)
  generalize hX : SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
    (storeReplyLegReady st c rid) c scId) (determineTargetCore st c) scId = X at hP1 hNoP
  have hAX' : ipcBufferReadsAgree X st := hX ▸ hAP
  have hIX' : X.objectIndexSet = st.objectIndexSet := hX ▸ hFrP.1.trans hIX
  have hLX' : X.lifecycle = st.lifecycle := hX ▸ hFrP.2.1.trans hLX
  rw [hP1] at hE1 hR1 hG1
  obtain ⟨s, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 s hNoP hT1
  have hHT : receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
      (X.mapTcbInPlace c (holdMessage msg)) = .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoP, hT1]
    rfl
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAX')
    hIX' hLX' ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoP) c.toObjId stcb ct count hW hHT).1
  obtain ⟨hE2, ⟨rt2, hR2, hA2⟩, hG2⟩ := receiveGuard_of_transferFrame hFr hE1 hR1 hA1 hG1
  have hXf : replyTransferCaps st tid c true
      (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLeg st c rid msg) c ⟨replyHeadContextCode st rid - 1⟩)
        (determineTargetCore st c) ⟨replyHeadContextCode st rid - 1⟩) =
      .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    unfold replyTransferCaps
    rw [hReq, hTgt, hSc, hP1, hHT]
  rw [replyRecvOnCore_unheld_transfer st epId tid c rid msg true core ct ep0 ep rp (hMsg ▸ hSz) hT
    hIpc hRO hG hS hRp hXf hE2 hR2 hA2 hG2]
  dsimp only
  subst hMsg
  simp only [CapTransferSummary.capInfo_empty]
  obtain ⟨t2, hT2, hB2⟩ := receiveBlock_receiver_blocked _ epId ep tid rt2 (some rid) core hE2 hR2
    hA2 hG2
  have hWY := ipcWordReadsAgree_receiveTransferCaps _ _ _ hNoP hT1
  rw [replyRecvBlockTail_stagedLong Y1 st c tid rid epId ep.recvTailCode core rf len badge s.capInfo hNoY hNe
    hLen ((ipcBufferReadsAgree_storeReplyRecvBlockTail Y1 tid rid epId ep.recvTailCode core hNoY).words.trans
      (hWY.trans hAX'.words)) ⟨t2, hT2, hB2⟩]
  have hK := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => deliverLongReplyRecvCapsFrame i (storeReplyRecvBlockTail Y tid rid epId ep.recvTailCode
      core) c rf len tid badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hK
  rw [hAX'.frameCapRequestOf, hAX'.capTargetOf, hT1] at hK
  unfold performReplyRecvUnheldCapsDeliveredLong
  rw [hSc, hX]
  exact congrArg (fun Z => (.ok ((), Z) : Except KernelError (Unit × SystemState))) hK.symm

end SeLe4n.Kernel
