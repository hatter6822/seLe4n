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

A reply-receive's message is its decoded words less MR0, which names the reply
capability (`longReplyRecvRegs`): the replier's inline words one register past
MR0, then its first overflow word, then the rest of its overflow words.  When
the reply-receive answers a caller blocked on the server and then blocks on an
endpoint no sender waits on, every write in its slot (`replyRecvBlocksFast`),
the delivery here writes the frame into the caller's saved registers and
copies the overflow words, from the replier's slot `i + 1` to the caller's
slot `i`, word by word (`deliverLongReplyRecvFrame`), as seL4's
`doReplyTransfer` copies them (`copyMRs`).  No message is built
(`performReplyRecvBlockDeliveredLong`, `replyRecvBlock_stagedLong`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-! ## The overflow words, copied from a later slot -/

/-- Word `j` of thread `s`'s buffer recorded as a user-word store at thread
`r`'s slot `i`, both advancing, up to the first slot of `r`'s that does not
resolve (`overflowCopyStoreFrom_eq`).  Each word is read before the write that
records it. -/
def overflowCopyStoreFrom (S : SystemState) (r s : SeLe4n.ThreadId) :
    Nat → Nat → Nat → SystemState
  | _, _, 0 => S
  | j, i, n + 1 =>
    match overflowSlotOf S r i with
    | some pa => overflowCopyStoreFrom
        (S.recordPhysicalWrite (.storeUserWord pa (overflowWordAt S s j))) r s (j + 1) (i + 1) n
    | none => S

theorem overflowCopyStoreFrom_eq (r s : SeLe4n.ThreadId) (X : SystemState) (t : TCB)
    (Y : SystemState) :
    ∀ (n j i : Nat) (S : SystemState),
      (∀ k, overflowSlotOf S r k = Architecture.IpcBufferRead.ipcBufferSlotPAddr? X t k true) →
      ipcWordReadsAgree S Y →
      overflowCopyStoreFrom S r s j i n =
        Architecture.recordPhysicalWrites S
          (Architecture.overflowDeliveryWrites X t (overflowRegsFrom Y s j n) i)
  | 0, _, _, S, _, _ => (Architecture.recordPhysicalWrites_nil S).symm
  | n + 1, j, i, S, hS, hA => by
    simp only [overflowCopyStoreFrom, overflowRegsFrom, hS]
    unfold Architecture.overflowDeliveryWrites
    split
    · next pa hPa =>
      rw [hPa, recordPhysicalWrites_cons]
      have hReg : (⟨(overflowWordAt Y s j).toNat⟩ : SeLe4n.RegValue).val.toUInt64 =
          overflowWordAt Y s j := by
        simp only [Nat.toUInt64_eq, UInt64.ofNat_toNat]
      rw [hReg, hA.overflowWordAt]
      have hA' := (ipcBufferReadsAgree_recordPhysicalWrite S
        (.storeUserWord pa (overflowWordAt Y s j))).words.trans hA
      exact overflowCopyStoreFrom_eq r s X t Y n (j + 1) (i + 1) _
        (fun k => by rw [(ipcBufferReadsAgree_recordPhysicalWrite S _).overflowSlotOf, hS k]) hA'
    · next hPa => rw [hPa]; exact (Architecture.recordPhysicalWrites_nil S).symm

theorem overflowCopyStoreFrom_getTcb? (r s t : SeLe4n.ThreadId) :
    ∀ (n j i : Nat) (S : SystemState), (overflowCopyStoreFrom S r s j i n).getTcb? t = S.getTcb? t
  | 0, _, _, _ => rfl
  | n + 1, j, i, S => by
    simp only [overflowCopyStoreFrom]
    split
    · exact overflowCopyStoreFrom_getTcb? r s t n (j + 1) (i + 1) _
    · rfl

/-! ## The message -/

/-- A long reply-receive's message words: its decoded words (`longSendMessage`'s)
less MR0, the reply capability's address. -/
@[inline] def longReplyRecvRegs (rf : SeLe4n.RegisterFile) (S : SystemState)
    (s : SeLe4n.ThreadId) (len : Nat) : Array SeLe4n.RegValue :=
  let full := (longSendMessage SeLe4n.arm64DefaultLayout rf S s len none).registers
  full.extract 1 full.size

theorem longReplyRecvRegs_size (rf : SeLe4n.RegisterFile) (S : SystemState)
    (s : SeLe4n.ThreadId) (len : Nat) (hLen : 4 ≤ len) :
    (longReplyRecvRegs rf S s len).size = len - 1 := by
  simp only [longReplyRecvRegs, Array.size_extract,
    longSendMessage_size SeLe4n.arm64DefaultLayout rf S s len none rfl hLen]
  omega

theorem longReplyRecvRegs_tail (rf : SeLe4n.RegisterFile) (S : SystemState)
    (s : SeLe4n.ThreadId) (len : Nat) (hLen : 5 ≤ len) :
    (longReplyRecvRegs rf S s len).toList.drop 4 = overflowRegsFrom S s 1 (len - 5) := by
  have hT := longSendMessage_tail SeLe4n.arm64DefaultLayout rf S s len none rfl
  have hE : (longReplyRecvRegs rf S s len).toList =
      (longSendMessage SeLe4n.arm64DefaultLayout rf S s len none).registers.toList.drop 1 := by
    simp only [longReplyRecvRegs, Array.toList_extract, List.extract_eq_drop_take]
    exact List.take_of_length_le (by simp)
  have hN : len - 4 = (len - 5) + 1 := by omega
  rw [hE, List.drop_drop, Nat.add_comm, ← List.drop_drop, hT, hN]
  rfl

theorem longReplyRecvRegs_word (rf : SeLe4n.RegisterFile) (S : SystemState)
    (s : SeLe4n.ThreadId) (len : Nat) (hLen : 5 ≤ len) (i : Nat) (hi : i < 3) :
    ((((longReplyRecvRegs rf S s len)[i]?).map SeLe4n.RegValue.val).getD 0).toUInt64 =
      Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf (i + 1) := by
  rw [← Architecture.regMessageRegs_word]
  have hSz := longSendMessage_size SeLe4n.arm64DefaultLayout rf S s len none rfl (by omega)
  simp only [longReplyRecvRegs, Array.getElem?_extract, hSz]
  rw [if_pos (by omega)]
  simp only [longSendMessage]
  have hL4 : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [Array.getElem?_append_left (by simp [Architecture.regMessageRegs, hL4]; omega), Nat.add_comm]

theorem longReplyRecvRegs_word3 (rf : SeLe4n.RegisterFile) (S : SystemState)
    (s : SeLe4n.ThreadId) (len : Nat) (hLen : 5 ≤ len) :
    ((((longReplyRecvRegs rf S s len)[3]?).map SeLe4n.RegValue.val).getD 0).toUInt64 =
      overflowWordAt S s 0 := by
  have hSz := longSendMessage_size SeLe4n.arm64DefaultLayout rf S s len none rfl (by omega)
  have hN : len - 4 = (len - 5) + 1 := by omega
  simp only [longReplyRecvRegs, Array.getElem?_extract, hSz]
  rw [if_pos (by omega)]
  simp only [longSendMessage]
  have hL4 : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [Array.getElem?_append_right (by simp [Architecture.regMessageRegs, hL4]), hN]
  simp [Architecture.regMessageRegs, overflowRegsFrom, Nat.toUInt64_eq, hL4]

theorem longReplyRecvFrame_eq (rf : SeLe4n.RegisterFile) (S : SystemState)
    (s : SeLe4n.ThreadId) (len k capInfo : Nat) (badge : Option SeLe4n.Badge) (hLen : 5 ≤ len) :
    withFrameWords (Architecture.badgeWordOrZero badge) (longMessageInfoWord (len - 1) k capInfo)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3) (overflowWordAt S s 0) =
      withFrameWords
        (Architecture.returnFrameOfMessage
          { registers := longReplyRecvRegs rf S s len, badge := badge } capInfo k).x0
        (Architecture.returnFrameOfMessage
          { registers := longReplyRecvRegs rf S s len, badge := badge } capInfo k).x1
        (Architecture.returnFrameOfMessage
          { registers := longReplyRecvRegs rf S s len, badge := badge } capInfo k).x2
        (Architecture.returnFrameOfMessage
          { registers := longReplyRecvRegs rf S s len, badge := badge } capInfo k).x3
        (Architecture.returnFrameOfMessage
          { registers := longReplyRecvRegs rf S s len, badge := badge } capInfo k).x4
        (Architecture.returnFrameOfMessage
          { registers := longReplyRecvRegs rf S s len, badge := badge } capInfo k).x5 := by
  simp only [Architecture.returnFrameOfMessage,
    longReplyRecvRegs_word rf S s len hLen 0 (by omega),
    longReplyRecvRegs_word rf S s len hLen 1 (by omega),
    longReplyRecvRegs_word rf S s len hLen 2 (by omega),
    longReplyRecvRegs_word3 rf S s len hLen]
  congr 1
  simp only [longMessageInfoWord, Architecture.returnMessageInfo,
    longReplyRecvRegs_size rf S s len (by omega)]

/-! ## The delivery -/

/-- The long reply-receive's message held where the caller is, unexpectedly,
not ready.  Out of line, so the message is built only on that path. -/
@[noinline] def holdLongReplyRecvMessage (X : SystemState) (r : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (s : SeLe4n.ThreadId) (badge : Option SeLe4n.Badge) :
    SystemState :=
  X.mapTcbInPlace r (holdMessage { registers := longReplyRecvRegs rf X s len, badge := badge })

/-- **A long reply-receive's delivery to the caller, in place**: the frame
written into the caller's saved registers (the replier's MR1..MR3, then its
first overflow word), its length counting the overflow words the caller's
buffer takes, then the replier's overflow words from slot 1 on copied into the
caller's from slot 0 (`overflowCopyStoreFrom`).  A caller that is,
unexpectedly, not ready holds the message (`holdLongReplyRecvMessage`).  Each
step reads what it needs before it writes (`deliverLongReplyRecvFrame_eq`). -/
@[inline] def deliverLongReplyRecvFrame (X : SystemState) (r : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (s : SeLe4n.ThreadId) (badge : Option SeLe4n.Badge)
    (capInfo : Nat) : SystemState :=
  match X.getTcb? r with
  | some t =>
    if t.ipcState = .ready then
      let k := overflowSlotsFrom X r 0 (len - 5)
      overflowCopyStoreFrom
        (X.mapTcbInPlace r (withFrameWords (Architecture.badgeWordOrZero badge)
          (longMessageInfoWord (len - 1) k capInfo)
          (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
          (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
          (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3) (overflowWordAt X s 0)))
        r s 1 0 (len - 5)
    else holdLongReplyRecvMessage X r rf len s badge
  | none => X

/-- **The in-place delivery is the specification's stage** of the long
reply-receive's message, its overflow words read in a state `Y` that reads
every buffer as the delivery's own does. -/
theorem deliverLongReplyRecvFrame_eq (X Y : SystemState) (r s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (capInfo : Nat)
    (hNoX : X.objects.noResizeDue) (hA : ipcWordReadsAgree X Y) (hLen : 5 ≤ len) :
    deliverLongReplyRecvFrame X r rf len s badge capInfo =
      Architecture.stageDeliveredMessage (X.mapTcbInPlace r (holdMessage
        { registers := longReplyRecvRegs rf Y s len, badge := badge })) r capInfo := by
  rw [stageDeliveredMessage_holdMessage_overflow _ r _ _ capInfo hNoX
    (longReplyRecvRegs_tail rf Y s len hLen)]
  unfold deliverLongReplyRecvFrame
  cases hT : X.getTcb? r with
  | none => rfl
  | some t =>
    simp only []
    split
    · have hX : ∀ j, overflowSlotOf X r j =
          Architecture.IpcBufferRead.ipcBufferSlotPAddr? X t j true := fun j => by
        simp only [overflowSlotOf, hT]
      have hS : ∀ (a b c d e g : UInt64) j,
          overflowSlotOf (X.mapTcbInPlace r (withFrameWords a b c d e g)) r j =
            Architecture.IpcBufferRead.ipcBufferSlotPAddr? X t j true := fun a b c d e g j => by
        simp only [overflowSlotOf, SystemState.getTcb?_mapTcbInPlace, hT, Option.map_some]
        exact ipcBufferSlotPAddr?_mapTcbInPlace X r _ t _ j true rfl rfl
      have hAg : ∀ (a b c d e g : UInt64),
          ipcWordReadsAgree (X.mapTcbInPlace r (withFrameWords a b c d e g)) Y :=
        fun a b c d e g =>
          (ipcBufferReadsAgree_mapTcbInPlace X r (withFrameWords a b c d e g)
            (fun _ => ⟨rfl, rfl⟩)).words.trans hA
      have hC := overflowSlotsFrom_eq X r X t hX (overflowRegsFrom Y s 1 (len - 5)) 0
      rw [overflowRegsFrom_length] at hC
      rw [overflowCopyStoreFrom_eq r s X t Y _ 1 0 _ (hS _ _ _ _ _ _) (hAg _ _ _ _ _ _), hC,
        hA.overflowWordAt, longReplyRecvFrame_eq rf Y s len _ capInfo badge hLen]
    · unfold holdLongReplyRecvMessage longReplyRecvRegs longSendMessage
      rw [hA.overflowRegsFrom]

theorem deliverLongReplyRecvFrame_getTcb?_ne (X : SystemState) (r s t : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (capInfo : Nat)
    (hNe : r.toObjId ≠ t.toObjId) :
    (deliverLongReplyRecvFrame X r rf len s badge capInfo).getTcb? t = X.getTcb? t := by
  unfold deliverLongReplyRecvFrame
  cases X.getTcb? r with
  | none => rfl
  | some x =>
    simp only []
    split
    · rw [overflowCopyStoreFrom_getTcb?, SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hNe]
    · unfold holdLongReplyRecvMessage
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
  have hL : ∀ t, (enqueueLinks tail? t).vspaceRoot = t.vspaceRoot ∧
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
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := storeReplyRendezvous_receiveGuard st c tid rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } ct rp
    epId ep rt hNo hT hIpc hFC hRp hNe hE hR hA hEnq hFree hStash hRec
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
    hLen]
  exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x
    (by rw [deliverLongReplyRecvFrame_getTcb?_ne _ _ _ _ _ _ _ _ hCT]; exact hX)
    (by rw [hEq, hB]; exact fun h => by cases h)

end SeLe4n.Kernel
