-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.LongReplyInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvInPlace

/-!
# A reply-receive of more than four words, written in place

A reply-receive's message is its decoded words, MR0 on (`longReplyRecvRegs`):
seL4-MCS names the reply capability in the reply register, not the message.  When
the reply-receive answers a caller blocked on the server and then blocks on an
endpoint no sender waits on, every write in its slot (`replyRecvBlocksFast`),
the delivery here writes the frame into the caller's saved registers and
copies the overflow words slot for slot (`deliverLongReplyRecvFrame`), as seL4's
`doReplyTransfer` copies them (`copyMRs`).  No message is built
(`performReplyRecvBlockDeliveredLong`, `replyRecvBlock_stagedLong`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-! ## The message -/

/-- A long reply-receive's message words: its decoded words, MR0 on
(`longSendMessage`'s).  seL4-MCS names the reply capability in the reply
register, never in the message, so the reply carries every word the replier
wrote. -/
@[inline] def longReplyRecvRegs (rf : SeLe4n.RegisterFile) (S : SystemState)
    (s : SeLe4n.ThreadId) (len : Nat) : Array SeLe4n.RegValue :=
  (longSendMessage SeLe4n.arm64DefaultLayout rf S s len none).registers

theorem longReplyRecvRegs_size (rf : SeLe4n.RegisterFile) (S : SystemState)
    (s : SeLe4n.ThreadId) (len : Nat) (hLen : 4 ≤ len) :
    (longReplyRecvRegs rf S s len).size = len :=
  longSendMessage_size SeLe4n.arm64DefaultLayout rf S s len none rfl hLen

theorem longReplyRecvMessage_eq (rf : SeLe4n.RegisterFile) (S : SystemState)
    (s : SeLe4n.ThreadId) (len : Nat) (badge : Option SeLe4n.Badge) :
    ({ registers := longReplyRecvRegs rf S s len, badge := badge } : IpcMessage) =
      longSendMessage SeLe4n.arm64DefaultLayout rf S s len badge := rfl

theorem Badge.opt_getD_isSome (badge : Option SeLe4n.Badge) :
    SeLe4n.Badge.opt (badge.getD SeLe4n.Badge.zero) badge.isSome = badge := by
  cases badge <;> rfl

/-! ## The delivery -/

/-- **A long reply-receive's delivery to the caller, in place**: a long send's
(`deliverLongSendFrame`), its badge given as an option.  The frame carries the
replier's MR0..MR3 and its overflow words are copied slot for slot, as seL4's
`doReplyTransfer` copies them (`copyMRs`). -/
@[inline] def deliverLongReplyRecvFrame (X : SystemState) (r : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (s : SeLe4n.ThreadId) (badge : Option SeLe4n.Badge)
    (capInfo : Nat) : SystemState :=
  deliverLongSendFrame X r SeLe4n.arm64DefaultLayout rf len s (badge.getD SeLe4n.Badge.zero)
    badge.isSome capInfo

/-- **The in-place delivery is the specification's stage** of the long
reply-receive's message, its overflow words read in a state `Y` that reads
every buffer as the delivery's own does. -/
theorem deliverLongReplyRecvFrame_eq (X Y : SystemState) (r s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (capInfo : Nat)
    (hNoX : X.objects.noResizeDue) (hA : ipcWordReadsAgree X Y) (hLen : 4 ≤ len) :
    deliverLongReplyRecvFrame X r rf len s badge capInfo =
      Architecture.stageDeliveredMessage (X.mapTcbInPlace r (holdMessage
        { registers := longReplyRecvRegs rf Y s len, badge := badge })) r capInfo := by
  unfold deliverLongReplyRecvFrame
  rw [deliverLongSendFrame_eq X Y r s _ rf len _ _ capInfo hNoX hA rfl hLen,
    Badge.opt_getD_isSome, longReplyRecvMessage_eq]

theorem deliverLongReplyRecvFrame_getTcb?_ne (X : SystemState) (r s t : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (capInfo : Nat)
    (hNe : r.toObjId ≠ t.toObjId) :
    (deliverLongReplyRecvFrame X r rf len s badge capInfo).getTcb? t = X.getTcb? t := by
  unfold deliverLongReplyRecvFrame deliverLongSendFrame
  cases X.getTcb? r with
  | none => rfl
  | some x =>
    simp only []
    split
    · rw [overflowCopyStore_getTcb?, SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hNe]
    · unfold holdLongSendMessage
      rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hNe]

/-! ## The blocking reply-receive -/

theorem ipcBufferReadsAgree_storeEndpointEnqueue (st : SystemState) (epId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (tail? : Option SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (storeEndpointEnqueue st epId isReceiveQ tid tail?) st ∧
      (storeEndpointEnqueue st epId isReceiveQ tid tail?).objects.noResizeDue := by
  unfold storeEndpointEnqueue
  have h1 := modifyObject_noResizeDue st epId
    (enqueueEndpoint isReceiveQ tid (ThreadId.optCode tail?)) hNo
  have a1 := ipcBufferReadsAgree_modifyObject st epId
    (enqueueEndpoint isReceiveQ tid (ThreadId.optCode tail?))
    (fun o => by
      cases o with
      | endpoint e => simp only [enqueueEndpoint]; split <;> rfl
      | _ => rfl) hNo
  generalize st.modifyObject epId (enqueueEndpoint isReceiveQ tid (ThreadId.optCode tail?)) = s1
    at h1 a1
  have hL : ∀ t, (enqueueLinks tail? t).spaceCells[2] = t.spaceCells[2] ∧
      (enqueueLinks tail? t).ipcBuffer = t.ipcBuffer := fun t => by
    unfold enqueueLinks; split <;> exact ⟨rfl, rfl⟩
  cases tail? with
  | none =>
    exact ⟨(ipcBufferReadsAgree_updateTcb s1 tid _ hL h1).trans a1, updateTcb_noResizeDue _ _ _ h1⟩
  | some p =>
    have h2 := updateTcb_noResizeDue s1 p (tcbWithQueueNext tid) h1
    have a2 := ipcBufferReadsAgree_updateTcb s1 p (tcbWithQueueNext tid) (fun _ => ⟨rfl, rfl⟩) h1
    exact ⟨(ipcBufferReadsAgree_updateTcb _ tid _ hL h2).trans (a2.trans a1),
      updateTcb_noResizeDue _ _ _ h2⟩

/-- **The receive's block keeps every read**: it writes the endpoint's queue,
the server's queue links, IPC state and pending reply code, and the reply
object's stasher record, never a VSpace root, a buffer address or the
machine. -/
theorem ipcBufferReadsAgree_storeReceiveBlock (st : SystemState) (epId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (tc rc : Nat) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (storeReceiveBlock st epId tid tc rc) st := by
  unfold storeReceiveBlock
  rw [storeEndpointEnqueueCode_eq]
  obtain ⟨a1, h1⟩ := ipcBufferReadsAgree_storeEndpointEnqueue st epId true tid
    (ThreadId.ofOptCode tc) hNo
  generalize storeEndpointEnqueue st epId true tid (ThreadId.ofOptCode tc) = s1 at a1 h1
  have a2 := ipcBufferReadsAgree_updateTcb s1 tid
    (fun t => (TCB.setIpcState { t with pendingMessage := none } (.blockedOnReceive epId)))
    (fun _ => ⟨rfl, rfl⟩) h1
  have h2 := updateTcb_noResizeDue s1 tid
    (fun t => (TCB.setIpcState { t with pendingMessage := none } (.blockedOnReceive epId))) h1
  generalize s1.updateTcb tid
    (fun t => (TCB.setIpcState { t with pendingMessage := none } (.blockedOnReceive epId))) = s2
    at a2 h2
  obtain ⟨s3, h3, a3, hEq3⟩ : ∃ s3 : SystemState, s3.objects.noResizeDue ∧
      ipcBufferReadsAgree s3 s2 ∧ storeReplyStasher s2 rc tid = s3 := by
    rcases rc with _ | k
    · exact ⟨s2, h2, .refl _, rfl⟩
    · exact ⟨_, modifyObject_noResizeDue _ _ _ h2,
        ipcBufferReadsAgree_modifyObject _ _ _ (fun o => by cases o <;> rfl) h2, rfl⟩
  rw [hEq3]
  exact (ipcBufferReadsAgree_updateTcb s3 tid (fun t => { t with pendingReceiveReplyCode := rc })
    (fun _ => ⟨rfl, rfl⟩) h3).trans
    (a3.trans (a2.trans a1))

theorem ipcBufferReadsAgree_storeReplyRecvBlockReady (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (storeReplyRecvBlockReady st c tid rid epId tailCode core) st := by
  unfold storeReplyRecvBlockReady
  have h1 := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have h2 := storeReceiveBlock_noResizeDue _ epId tid tailCode (rid.val + 1) h1
  have h3 := removeRunnableOnCore_noResizeDue _ tid core h2
  exact (ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core h3).trans
    ((ipcBufferReadsAgree_removeRunnableOnCore _ tid core).trans
      ((ipcBufferReadsAgree_storeReceiveBlock _ epId tid tailCode _ h1).trans
        (ipcBufferReadsAgree_storeReplyRendezvousReady st c tid rid hNo)))

/-- **The blocking long reply-receive, delivered from the registers and the
replier's buffer**: the reply's writes, the server's block and priority walk,
then the reply's frame written into the caller's saved registers and its
overflow words copied into the caller's buffer.  The message is built only
where the caller is, unexpectedly, not ready. -/
@[noinline] def performReplyRecvBlockDeliveredLong (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) (core : CoreId) : SystemState :=
  deliverLongReplyRecvFrame (storeReplyRecvBlockReady st c tid rid epId tailCode core) c rf len
    tid badge 0

/-- **The blocking long reply-receive's stages are its delivery**: under the
in-place guard of `replyRecvOnCore_blocks_inPlace`, staging the caller of the
composite's state and then the server (blocked on the endpoint, so staging it
is the identity) is `performReplyRecvBlockDeliveredLong`. -/
theorem replyRecvOnCore_blocks_deliveredLong (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hLen : 5 ≤ len)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hG : replyWakesInPlace st c ct rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hFree : rp.consumed.isFree = true) (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock (storeReplyRendezvous st c tid rid
            { registers := longReplyRecvRegs rf st tid len, badge := badge }) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c 0) tid 0 =
      performReplyRecvBlockDeliveredLong st c tid rid epId ep.recvTailCode rf len badge core := by
  have hNo := replyWakesInPlace_noResizeDue hG
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG
    exact hG.1.1.1.2
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have h1 := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have h3 := removeRunnableOnCore_noResizeDue _ tid core
    (storeReceiveBlock_noResizeDue _ epId tid ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid)) h1)
  obtain ⟨hE1, ⟨rt1, hR1, hA1, hB1⟩, hG1⟩ := storeReplyRendezvous_receiveGuard st c tid rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } ct rp
    epId ep rt hNo hT hFC hRp hNe hE hR hA hEnq hFree hStash hRec
  obtain ⟨t, hT1, hB⟩ := receiveBlock_receiver_blocked _ epId ep tid rt1 (some rid) core hE1 hR1
    hA1 hG1
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, storeReceiveBlock_msg _ _ _ _ _ _ _ h1 hNe,
    removeRunnableOnCore_msg, SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hT1
  obtain ⟨x, hX, hEq⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h3 tid t hT1
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, storeReceiveBlock_msg _ _ _ _ _ _ _ h1 hNe,
    removeRunnableOnCore_msg, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ h3]
  change Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
      ((storeReplyRecvBlockReady st c tid rid epId ep.recvTailCode core).mapTcbInPlace c
        (holdMessage { registers := longReplyRecvRegs rf st tid len, badge := badge })) c 0) tid 0 = _
  rw [← deliverLongReplyRecvFrame_eq _ st c tid rf len badge 0
    (storeReplyRecvBlockReady_noResizeDue st c tid rid epId ep.recvTailCode core hNo)
    (ipcBufferReadsAgree_storeReplyRecvBlockReady st c tid rid epId ep.recvTailCode core hNo).words
    (by omega)]
  exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x
    (by rw [deliverLongReplyRecvFrame_getTcb?_ne _ _ _ _ _ _ _ _ hCT]; exact hX)
    (by rw [hEq, hB]; exact fun h => by cases h)

end SeLe4n.Kernel
