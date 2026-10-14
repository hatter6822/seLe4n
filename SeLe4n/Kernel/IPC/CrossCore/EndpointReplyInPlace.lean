/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallInPlace
import SeLe4n.Kernel.IPC.CrossCore.Fault

/-!
# The reply, written in place

WS-ZA ZA4.7: a reply to a caller blocked on it writes the caller (ready, holding
the message, its reply object released), the reply object (consumed), the
caller's run queue and the server's reply-waiter queue, then reverts the
server's priority boost.  The specification (`endpointReplyOnCore` inside
`endpointReplyCrossCoreDispatch` inside `replyTransferOnCoreChecked`) reaches
each write through a step that may refuse, so its compiled form keeps the
pre-state alive for the refusal and copies every table it writes.  Here every
refusal is ruled out before the first write (`replyWakesInPlace`), the writes
run on a state nothing else holds (`performReplyRendezvous`), and the result is
proven equal to the specification (`replyTransferChecked_inPlace`).  The
argument is the call rendezvous's (`EndpointCallInPlace`): each write rewrites
a key where it stands or maps one slot's value, so no key moves.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood

/-- Leaving a reply-waiter queue maps four slots' values, so it moves no key. -/
theorem unlinkReplyWaiter_keepsFinds (st : SystemState) (w s : SeLe4n.ThreadId) :
    (st.unlinkReplyWaiter w s).objectsKeepFinds st := by
  unfold SystemState.unlinkReplyWaiter
  exact (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans
    ((SystemState.mapTcbInPlace_keepsFinds _ _ _).trans
    ((SystemState.updateTcbAtCode_keepsFinds _ _ _).trans
    (SystemState.updateTcbAtCode_keepsFinds _ _ _)))

/-- The reply object a delivered reply consumes. -/
@[inline] def replyConsumedObject : KernelObject → KernelObject
  | .reply r => .reply r.consumed
  | o => o

/-- **The reply writes only its slots**: the answered caller and its reply
object each rewritten where they stand, each store changing only `objects`, the
caller an unreserved thread carrying no fault, its reply object heading no
stack and below no frame. -/
@[inline] def replyWakesInPlace (st : SystemState) (c : SeLe4n.ThreadId) (ct : TCB)
    (rid : SeLe4n.ReplyId) : Bool :=
  !c.isReserved &&
  storeLeavesIndexAndTypes st c.toObjId .tcb &&
  st.objects.findsInPlace c.toObjId &&
  storeLeavesIndexAndTypes st rid.toObjId .reply &&
  st.objects.findsInPlace rid.toObjId &&
  ct.pendingFault.isNone &&
  (match st.objects[rid.toObjId]? with
   | some (.reply rp) => rp.next.isNone
   | _ => false)

/-- The reply's writes up to the priority walk, each in its slot: the caller
handed the message and woken on its home core, its reply object consumed and
released, and the caller off the server's reply waiters. -/
@[noinline] def storeReplyRendezvous (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) : SystemState :=
  let s1 := st.updateTcb c (callReceiverTcb msg)
  let s2 := enqueueRunnableOnCore s1 (determineTargetCore s1 c) c
  let s3 := (s2.modifyObject rid.toObjId replyConsumedObject).updateTcb c
    (fun t => { t with replyObject := none })
  s3.unlinkReplyWaiter c server

/-- The reply's state: the writes, the server's priority walk, and the
caller's delivered message staged in its return frame. -/
@[noinline] def performReplyRendezvous (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (core : Concurrency.CoreId) : SystemState :=
  Architecture.stageDeliveredMessage
    (PriorityInheritance.propagatePipChainCrossCore
      (storeReplyRendezvous st c server rid msg) server core).1 c 0

/-- **The reply, in place**: under `replyWakesInPlace` the specification's
reply returns `storeReplyRendezvous`'s state with the caller wake's SGI, and the
consumed reply object heads no context there. -/
theorem replyOnCore_inPlace (st : SystemState) (replier c server : SeLe4n.ThreadId)
    (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (core : Concurrency.CoreId)
    (hSz : ¬ msg.registers.size > maxMessageRegisters) (hCp : ¬ msg.caps.size > maxExtraCaps)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true) :
    endpointReplyOnCore replier c msg core st =
        (storeReplyRendezvous st c server rid msg,
         .ok (wakeThread (st.updateTcb c (callReceiverTcb msg)) c core).2) ∧
      replyFrameHeadHolder? (storeReplyRendezvous st c server rid msg) rid = none := by
  simp only [replyWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨⟨hCRes, hLC⟩, hFC⟩, hLR⟩, hFR⟩, _⟩, hRp⟩ := hG
  obtain ⟨rp, hRo, hNext⟩ : ∃ rp, st.objects[rid.toObjId]? = some (.reply rp) ∧
      rp.next = none := by
    split at hRp
    · next rp hRo => exact ⟨rp, hRo, Option.isNone_iff_eq_none.mp hRp⟩
    · cases hRp
  have hNeCQ : c.toObjId ≠ rid.toObjId := fun h => by rw [h, hRo] at hT; cases hT
  have hNeQC : rid.toObjId ≠ c.toObjId := fun h => hNeCQ h.symm
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hLook : lookupTcb st c = some ct := by
    simp only [lookupTcb, hCRes, Bool.false_eq_true, ↓reduceIte]; exact hTc
  -- The caller handed the message.
  have hSt1 : storeTcbIpcStateAndMessage_fromTcb st c ct .ready (some msg) =
      .ok (st.updateTcb c (callReceiverTcb msg)) := by
    unfold storeTcbIpcStateAndMessage_fromTcb
    rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLC),
      SystemState.updateTcb_eq_of_some hTc]
    rfl
  have hT1 := updateTcb_getTcb?_self_of_findsInPlace (callReceiverTcb msg) hTc hFC
  have hO1q := (updateTcb_get?_ne_of_findsInPlace (callReceiverTcb msg) hTc hFC hNeCQ).trans hRo
  have hK1 : ∀ k, (st.updateTcb c (callReceiverTcb msg)).objects.findsInPlace k =
      st.objects.findsInPlace k := updateTcb_findsInPlace _ hTc hFC
  have hL1 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes (st.updateTcb c (callReceiverTcb msg)) id ty = true :=
    fun h => updateTcb_storeLeaves _ hTc hFC h
  unfold storeReplyRendezvous
  dsimp only
  generalize hS1 : st.updateTcb c (callReceiverTcb msg) = S1 at *
  -- The wake.
  have hA2 := enqueueRunnableOnCore_agree_of_findsInPlace S1 (determineTargetCore S1 c) c _ hT1
    rfl ((hK1 _).trans hFC)
  have hD2 := enqueueRunnableOnCore_onlyObjectsSchedulerDiffer S1 (determineTargetCore S1 c) c
  have hK2 : ∀ k, (enqueueRunnableOnCore S1 (determineTargetCore S1 c) c).objects.findsInPlace k
      = st.objects.findsInPlace k := fun k =>
    (enqueueRunnableOnCore_keepsFinds S1 _ c ((hK1 _).trans hFC) k).trans (hK1 k)
  have hL2 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes (enqueueRunnableOnCore S1 (determineTargetCore S1 c) c) id ty
        = true := fun h => storeLeaves_of_onlyObjectsSchedulerDiffer hD2 hA2 (hL1 h)
  obtain ⟨ct2, hO2c, hct2⟩ := hA2.get_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT1)
  have hO2q := hA2.get_reply_iff.mpr hO1q
  have hW : (wakeThread S1 c core).1 = enqueueRunnableOnCore S1 (determineTargetCore S1 c) c := rfl
  generalize hS2 : enqueueRunnableOnCore S1 (determineTargetCore S1 c) c = S2 at *
  have hFR2 := (hK2 _).trans hFR
  have hFC2 := (hK2 _).trans hFC
  have hRp2 : S2.getReply? rid = some rp := (SystemState.getReply?_eq_some_iff _ _ _).mpr hO2q
  have hSp : spliceReplyFrameOutOrSelf S2 rid = S2 := by
    unfold spliceReplyFrameOutOrSelf
    rw [spliceReplyFrameOut_of_no_frame_above S2 rid rp hRp2 hNext]
  have hS3 : S2.modifyObject rid.toObjId replyConsumedObject =
      { S2 with objects := (S2.objects.insert rid.toObjId (.reply rp.consumed)) } := by
    unfold SystemState.modifyObject
    rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? (by exact hO2q)]
    rfl
  have hStR : storeObject rid.toObjId (.reply rp.consumed) S2 =
      .ok ((), { S2 with objects := (S2.objects.insert rid.toObjId (.reply rp.consumed)) }) :=
    storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL2 hLR)
  rw [hS3]
  generalize hS3' : ({ S2 with objects := (S2.objects.insert rid.toObjId
      (.reply rp.consumed)) } : SystemState) = S3 at *
  have hT3c : S3.getTcb? c = some ct2 := by
    rw [← hS3']
    exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      ((RHTable.get?_insert_ne_of_findsInPlace _ _ hFR2 hNeQC).trans hO2c)
  have hO3q : S3.objects[rid.toObjId]? = some (.reply rp.consumed) := by
    rw [← hS3']; exact RHTable.get?_insert_self_of_findsInPlace _ hFR2
  have hFC3 : S3.objects.findsInPlace c.toObjId = true := by
    rw [← hS3']; exact (RHTable.findsInPlace_insert_of_findsInPlace _ _ hFR2).trans hFC2
  have hL3 : storeLeavesIndexAndTypes S3 c.toObjId .tcb = true := by
    rw [← hS3']
    exact storeLeavesIndexAndTypes_insert_inPlace hFR2 (fun _ e => by cases e) (hL2 hLC)
  have hSt4 : storeObject c.toObjId (.tcb { ct2 with replyObject := none }) S3 =
      .ok ((), S3.updateTcb c (fun t => { t with replyObject := none })) := by
    rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL3),
      SystemState.updateTcb_eq_of_some hT3c]
  have hO4q : (S3.updateTcb c (fun t => { t with replyObject := none })).objects[rid.toObjId]?
      = some (.reply rp.consumed) :=
    (updateTcb_get?_ne_of_findsInPlace _ hT3c hFC3 hNeCQ).trans hO3q
  refine ⟨?_, ?_⟩
  · unfold endpointReplyOnCore
    rw [if_neg hSz, if_neg hCp, hLook]
    dsimp only
    rw [hIpc]
    dsimp only
    rw [hSt1]
    dsimp only
    rw [hRO]
    dsimp only
    unfold removeCallerReplyFrame
    rw [hW, hSp]
    unfold SystemState.consumeCallerReply SystemState.consumeReply
    simp only [hRp2, hStR, hT3c, hSt4]
  · apply replyFrameHeadHolder?_of_no_head
    have hR5 := (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks
      (S3.updateTcb c (fun t => { t with replyObject := none })) c server).get_reply_iff.mpr hO4q
    unfold replyFrameHeadContext?
    rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hR5]
    simp only [Reply.consumed, hNext]

/-- **The checked reply transfer, in place**: under the flow gate and
`replyWakesInPlace`, a reply to an unfaulted caller blocked on it commits
`performReplyRendezvous`'s state. -/
theorem replyTransferChecked_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c server : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (msg : IpcMessage)
    (core : Concurrency.CoreId)
    (hSz : ¬ msg.registers.size > maxMessageRegisters) (hCaps : msg.caps = #[])
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hSRes : server.isReserved = false)
    (hG : replyWakesInPlace st c ct rid = true)
    (hFlow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf c) = true) :
    replyTransferOnCoreChecked ctx replier c mi regs msg core st =
      .ok ((), performReplyRendezvous st c server rid msg core) := by
  have hG' := hG
  simp only [replyWakesInPlace, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hG'
  have hCRes : c.isReserved = false := hG'.1.1.1.1.1.1
  have hPF : ct.pendingFault = none := hG'.1.2
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨hEq, hHead⟩ := replyOnCore_inPlace st replier c server ct ep rid msg core hSz
    (by rw [hCaps]; decide) hT hIpc hRO hG
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hCRes)
  obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff server).mpr hSRes)
  have hNF : threadHasPendingFault st c = false := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_none]
  have hRec : recordedReplyServer? st c = some server := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hAns : answeredReplyObject? st c = some rid := by
    simp only [answeredReplyObject?, hTc, Option.bind_some, hRO]
  unfold replyTransferOnCoreChecked
  rw [hNF, endpointReplyCrossCoreDispatchChecked_flow_allowed _ _ _ _ _ _ hFlow]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hsv, hAns, hcv]
  unfold applyReplyDonationOnCore
  rw [SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv, hHead]
  rfl

end SeLe4n.Kernel
