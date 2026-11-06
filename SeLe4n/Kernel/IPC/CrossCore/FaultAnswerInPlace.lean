-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.FaultInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvUnheldInPlace

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

* `.replyRecv` blocking on the endpoint, after a reply that wakes its caller
  in its slots (`performReplyRecvFaultAnswer`,
  `replyRecvTransferOnCore_fault_blocks_inPlace`), after a donated reply
  (`performReplyRecvDonatedFaultAnswer`,
  `replyRecvTransferOnCore_fault_donated_inPlace`) and after a reply to a
  caller recording no server (`performReplyRecvUnheldFaultAnswer`,
  `replyRecvTransferOnCore_fault_unheld_inPlace`);
* `.reply` on a donated reply (`performFaultReplyDonatedAnswer`,
  `faultReplyTransferChecked_donated_inPlace`) and to a caller recording no
  server (`performFaultReplyUnheldAnswer`,
  `faultReplyTransferChecked_unheld_inPlace`); its rendezvous form is
  `performFaultReplyAnswer` (`FaultInPlace.lean`).

None builds the fault record, the reply's message, the outcome or a frame.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- A reply-receive's words, MR1 onward, are the layout's from word `1` on. -/
theorem wordAt_regReplyRecvBody (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len i : Nat)
    (h : i < Architecture.regMessageLength layout len - 1) :
    Architecture.wordAt (Architecture.regReplyRecvBody layout rf len) i =
      Architecture.regLayoutWord layout rf (i + 1) := by
  rw [← Architecture.regMessageWord_eq_regLayoutWord layout rf len (i + 1) (by omega),
    ← Architecture.regReplyRecvBody_word]
  unfold Architecture.wordAt Architecture.wordOf
  cases (Architecture.regReplyRecvBody layout rf len)[i]? <;> rfl

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

/-- **The blocking reply-receive answering a fault, in place**: the reply's
writes with no message (`storeFaultReplyRendezvous`), the server's block on the
endpoint and its priority walk, then the fault answer (`performFaultAnswer`)
from the caller's fault words (`kind`, `ip` … `x7`) and the reply's label and
words past MR0. -/
@[noinline] def performReplyRecvFaultAnswer (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat) :
    SystemState :=
  performFaultAnswer (PriorityInheritance.propagatePipChainCrossCore
      (removeRunnableOnCore (storeReceiveBlock (storeFaultReplyRendezvous st c tid rid) epId tid
        tailCode (rid.val + 1)) tid core) tid core).1 c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf (Architecture.regMessageLength layout len - 1) 1

/-- The fault answer leaves every other thread in the IPC state it was in. -/
theorem performFaultAnswer_ipcStateAt (X : SystemState) (c t : SeLe4n.ThreadId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (n off : Nat)
    (hNe : c.toObjId ≠ t.toObjId) (hNo : X.objects.noResizeDue) (x : TCB)
    (hX : X.getTcb? t = some x) :
    ∃ x', (performFaultAnswer X c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n
      off).getTcb? t = some x' ∧ x'.ipcState = x.ipcState := by
  have hUp : ∀ (Y : SystemState) (f : TCB → TCB), Y.objects.noResizeDue →
      (Y.updateTcb c f).getTcb? t = Y.getTcb? t := fun Y f hY => by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hY,
      SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hNe]
  unfold performFaultAnswer applyFaultRestart faultAbandonOnCore
  split
  · exact ⟨x, by rw [hUp _ _ hNo]; exact hX, rfl⟩
  · split
    · obtain ⟨x1, h1, e1⟩ := ipcStateCarried_of_agree
        (removeRunnableOnCore_objectsAgreeOffRunLinks X c (faultAbandonCore X c)) t x hX
      exact ⟨x1, by rw [hUp _ _ (removeRunnableOnCore_noResizeDue _ _ _ hNo)]; exact h1, e1⟩
    · split
      · exact ⟨x, by rw [hUp _ _ hNo]; exact hX, rfl⟩
      · exact ⟨x, by rw [hUp _ _ hNo]; exact hX, rfl⟩

/-- **The blocking reply-receive answering a fault is the specification's**:
under the guard of `replyRecvOnCore_blocks_inPlace`, for a caller carrying a
fault, the arm's transition is `performReplyRecvFaultAnswer` with no capability
installed, the reply's words those past MR0. -/
theorem replyRecvTransferOnCore_fault_blocks_inPlace (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (root : SeLe4n.ObjId) (slot : SeLe4n.Slot) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply) (tf : ThreadFault)
    (hPF : ct.pendingFault = some tf)
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
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    replyRecvTransferOnCore epId tid rid c label
        { registers := Architecture.regReplyRecvBody layout rf len, badge := badge }
        root slot core st =
      .ok ({ results := #[] }, performReplyRecvFaultAnswer st c tid rid epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf len) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  unfold replyRecvTransferOnCore
  rw [replyRecvCallerFaultAnswer?_of_fault st c ct tf label _ hTc hPF]
  simp only [replyRecvLegMessage]
  rw [replyRecvAnsweringOnCore_blocks_inPlace _ st epId tid c rid IpcMessage.empty root slot core
    ct ep0 rt ep rp (by simp [IpcMessage.empty]) hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hFree
    hStash hRec]
  unfold performReplyRecvFaultAnswer replyRecvAnswerCaller
  dsimp only
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswer _ c ct tf hPF _ _ layout rf
    (Architecture.regMessageLength layout len - 1) 1
    (by simp only [Architecture.regReplyRecvBody_size, Nat.min_self])
    (fun i hi => wordAt_regReplyRecvBody layout rf len i hi)]
  rfl

/-- **The blocking reply-receive's fault answer stages nothing for the server**:
the server is blocked on the endpoint once the legs have run, and the answer
leaves it so. -/
theorem performReplyRecvFaultAnswer_staged (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (core : CoreId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
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
    Architecture.stageDeliveredMessage (performReplyRecvFaultAnswer st c tid rid epId
        ep.recvTailCode core kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf len) tid 0 =
      performReplyRecvFaultAnswer st c tid rid epId ep.recvTailCode core kind label
        ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf len := by
  have hNo := replyWakesInPlace_noResizeDue hG
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG
    exact hG.1.1.1.2
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := storeReplyRendezvous_receiveGuard st c tid rid
    IpcMessage.empty ct rp epId ep rt hNo hT hIpc hFC hRp hNe hE hR hA hEnq hFree hStash hRec
  obtain ⟨t, hT1, hB⟩ := receiveBlock_receiver_blocked _ epId ep tid rt1 (some rid) core hE1 hR1
    hA1 hG1
  have h0 : (storeReplyRendezvous st c tid rid IpcMessage.empty).objects.noResizeDue := by
    rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, SystemState.mapTcbInPlace_noResizeDue]
    exact storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have h3 := removeRunnableOnCore_noResizeDue _ tid core
    (storeReceiveBlock_noResizeDue _ epId tid ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid)) h0)
  obtain ⟨x, hX, hEq⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h3 tid t hT1
  obtain ⟨x', hX', hEq'⟩ := performFaultAnswer_ipcStateAt _ c tid kind label ip sp lr
    x0 x1 x2 x3 x4 x5 x6 x7 layout rf (Architecture.regMessageLength layout len - 1) 1 hCT
    (propagatePipChainCrossCore_noResizeDue _ _ _ h3) x hX
  unfold performReplyRecvFaultAnswer
  exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x' hX'
    (by rw [hEq', hEq, hB]; exact fun h => by cases h)

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

/-- **The donated reply-receive answering a fault, in place**: the reply's
writes with no message, the pop and its settle, the server's block on the
endpoint, the server taken off its core and its priority walk, then the fault
answer (`performFaultAnswer`). -/
@[noinline] def performReplyRecvDonatedFaultAnswer (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (core : CoreId) (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat) :
    SystemState :=
  performFaultAnswer (PriorityInheritance.propagatePipChainCrossCore
      (descheduleAtPlacement (removeRunnableOnCore (storeReceiveBlock
        (popDonationSettledInPlace (storeFaultReplyRendezvous st c tid rid) c tid scId home) epId tid
        tailCode (rid.val + 1)) tid core) tid) tid core).1 c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf (Architecture.regMessageLength layout len - 1) 1

/-- **The donated reply-receive answering a fault is the specification's**, and
it stages nothing for the server, which the receive leaves blocked. -/
theorem replyRecvTransferOnCore_fault_donated_inPlace (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (root : SeLe4n.ObjId) (slot : SeLe4n.Slot) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply) (tf : ThreadFault)
    (hPF : ct.pendingFault = some tf)
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
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    replyRecvTransferOnCore epId tid rid c label
        { registers := Architecture.regReplyRecvBody layout rf len, badge := badge }
        root slot core st =
      .ok ({ results := #[] }, performReplyRecvDonatedFaultAnswer st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf len) ∧
    Architecture.stageDeliveredMessage (performReplyRecvDonatedFaultAnswer st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf len) tid 0 =
      performReplyRecvDonatedFaultAnswer st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf len := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hNe', hNo, _⟩ :=
    replyPopsInPlace_donation st c tid rid IpcMessage.empty ct hT hSRes hG
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe' (SeLe4n.ThreadId.toObjId_injective _ _ e)
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvAnsweringOnCore_donated_inPlace
    (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge })
    st epId tid c rid IpcMessage.empty root slot core ct ep0 rt ep rp (by simp [IpcMessage.empty])
    hT hIpc hRO hSRes hG hE hS hR hA hEnq hRp hStash hRec
  have hAns := replyRecvCallerFaultAnswer?_of_fault st c ct tf label
    { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } hTc hPF
  have hAp : ∀ X : SystemState, replyRecvAnswerCaller
        (replyRecvCallerFaultAnswer? st c label
          { registers := Architecture.regReplyRecvBody layout rf len, badge := badge }) X c =
      performFaultAnswer X c ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf
        (Architecture.regMessageLength layout len - 1) 1 := fun X => by
    rw [hAns]
    exact faultReplyApplyOnCore_decode_eq_performFaultAnswer _ c ct tf hPF _ _ layout rf
      (Architecture.regMessageLength layout len - 1) 1
      (by simp only [Architecture.regReplyRecvBody_size, Nat.min_self])
      (fun i hi => wordAt_regReplyRecvBody layout rf len i hi)
  have hL : replyRecvLegMessage (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge })
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } =
      IpcMessage.empty := by rw [hAns]; rfl
  refine ⟨?_, ?_⟩
  · unfold replyRecvTransferOnCore
    rw [hL, hEq, hAp]
    rfl
  · have h0 : (storeReplyRendezvous st c tid rid IpcMessage.empty).objects.noResizeDue := by
      rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, SystemState.mapTcbInPlace_noResizeDue]
      exact storeReplyRendezvousReady_noResizeDue st c tid rid hNo
    have h2 := popDonationSettledInPlace_noResizeDue _ c tid ⟨replyHeadContextCode st rid - 1⟩
      (determineTargetCore st c) h0
    have h3 := storeReceiveBlock_noResizeDue _ epId tid ep.recvTailCode
      (SeLe4n.ReplyId.optCode (some rid)) h2
    have h4 := removeRunnableOnCore_noResizeDue _ tid core h3
    have h5 := descheduleAtPlacement_noResizeDue _ tid h4
    obtain ⟨x1, hX1, e1⟩ := descheduleAtPlacement_ipcStateCarried _ tid tid x hX
    obtain ⟨x2, hX2, e2⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h5 tid x1 hX1
    obtain ⟨x3, hX3, e3⟩ := performFaultAnswer_ipcStateAt _ c tid ct.faultKind label ct.faultIp
      ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
      ct.faultX6 ct.faultX7 layout rf (Architecture.regMessageLength layout len - 1) 1 hCT
      (propagatePipChainCrossCore_noResizeDue _ _ _ h5) x2 hX2
    unfold performReplyRecvDonatedFaultAnswer
    exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x3 hX3
      (by rw [e3, e2, e1, hB]; exact fun h => by cases h)

/-- **The reply-receive answering a fault for a caller recording no server, in
place**: the reply leg's writes with no message, the unheld pop and its settle,
the replier's block on the endpoint and its priority walk, then the fault answer
(`performFaultAnswer`). -/
@[noinline] def performReplyRecvUnheldFaultAnswer (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (core : CoreId) (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat) :
    SystemState :=
  performFaultAnswer (PriorityInheritance.propagatePipChainCrossCore
      (removeRunnableOnCore (storeReceiveBlock
        (SchedContextOps.settleReturnedContext
          (returnUnheldSchedContextInPlace (storeFaultReplyLeg st c rid) c scId) home scId) epId tid
        tailCode (rid.val + 1)) tid core) tid core).1 c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf (Architecture.regMessageLength layout len - 1) 1

/-- **The reply-receive answering a fault for a caller recording no server is
the specification's**, and it stages nothing for the replier, which the receive
leaves blocked. -/
theorem replyRecvTransferOnCore_fault_unheld_inPlace (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (root : SeLe4n.ObjId) (slot : SeLe4n.Slot) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply) (tf : ThreadFault)
    (hPF : ct.pendingFault = some tf)
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
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    replyRecvTransferOnCore epId tid rid c label
        { registers := Architecture.regReplyRecvBody layout rf len, badge := badge }
        root slot core st =
      .ok ({ results := #[] }, performReplyRecvUnheldFaultAnswer st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf len) ∧
    Architecture.stageDeliveredMessage (performReplyRecvUnheldFaultAnswer st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf len) tid 0 =
      performReplyRecvUnheldFaultAnswer st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf len := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨_, _, _, _, _, _, hNo, _⟩ := replyUnheldPopsInPlace_pop st c rid IpcMessage.empty ct hT hG
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvAnsweringOnCore_unheld_inPlace
    (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge })
    st epId tid c rid IpcMessage.empty root slot core ct ep0 rt ep rp (by simp [IpcMessage.empty])
    hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hStash hRec
  have hAns := replyRecvCallerFaultAnswer?_of_fault st c ct tf label
    { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } hTc hPF
  have hAp : ∀ X : SystemState, replyRecvAnswerCaller
        (replyRecvCallerFaultAnswer? st c label
          { registers := Architecture.regReplyRecvBody layout rf len, badge := badge }) X c =
      performFaultAnswer X c ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf
        (Architecture.regMessageLength layout len - 1) 1 := fun X => by
    rw [hAns]
    exact faultReplyApplyOnCore_decode_eq_performFaultAnswer _ c ct tf hPF _ _ layout rf
      (Architecture.regMessageLength layout len - 1) 1
      (by simp only [Architecture.regReplyRecvBody_size, Nat.min_self])
      (fun i hi => wordAt_regReplyRecvBody layout rf len i hi)
  have hL : replyRecvLegMessage (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge })
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } =
      IpcMessage.empty := by rw [hAns]; rfl
  refine ⟨?_, ?_⟩
  · unfold replyRecvTransferOnCore
    rw [hL, hEq, hAp]
    rfl
  · have h0 : (storeReplyLeg st c rid IpcMessage.empty).objects.noResizeDue := by
      rw [storeReplyLeg_eq_hold _ _ _ _ hNo, SystemState.mapTcbInPlace_noResizeDue]
      exact storeReplyLegReady_noResizeDue st c rid hNo
    have h1 := returnUnheldSchedContextInPlace_noResizeDue _ c ⟨replyHeadContextCode st rid - 1⟩ h0
    have h2 := settleReturnedContext_noResizeDue _ (determineTargetCore st c)
      ⟨replyHeadContextCode st rid - 1⟩ h1
    have h3 := storeReceiveBlock_noResizeDue _ epId tid ep.recvTailCode
      (SeLe4n.ReplyId.optCode (some rid)) h2
    have h4 := removeRunnableOnCore_noResizeDue _ tid core h3
    obtain ⟨x2, hX2, e2⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h4 tid x hX
    obtain ⟨x3, hX3, e3⟩ := performFaultAnswer_ipcStateAt _ c tid ct.faultKind label ct.faultIp
      ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
      ct.faultX6 ct.faultX7 layout rf (Architecture.regMessageLength layout len - 1) 1 hCT
      (propagatePipChainCrossCore_noResizeDue _ _ _ h4) x2 hX2
    unfold performReplyRecvUnheldFaultAnswer
    exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x3 hX3
      (by rw [e3, e2, hB]; exact fun h => by cases h)

/-- **The donated reply's fault answer, in place**: the reply's writes with no
message, the loaned context handed back down the stack in place
(`replyDonationPopInPlace`, settled on the caller's home `home`), the server's
priority walk, then the fault answer (`performFaultAnswer`). -/
@[noinline] def performFaultReplyDonatedAnswer (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (core : CoreId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (n : Nat) : SystemState :=
  performFaultAnswer (PriorityInheritance.propagatePipChainCrossCore
      (replyDonationPopInPlace (storeFaultReplyRendezvous st c server rid) c server scId home)
      server core).1 c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n 0

/-- **The checked donated fault reply, in place**: under `replyPopsInPlace`, a
reply to a faulted caller blocked on it, whose reply object heads the stack of
the context the server holds on loan, commits `performFaultReplyDonatedAnswer`'s
state. -/
theorem faultReplyTransferChecked_donated_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c server : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (mi : MessageInfo) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (msg : IpcMessage) (core : CoreId)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hSRes : server.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode server rid = true)
    (hF : ct.faultWords.isFault = true) :
    replyTransferOnCoreChecked ctx replier c mi (Architecture.regMessageRegs layout rf) msg core
        st =
      .ok ((), performFaultReplyDonatedAnswer st c server rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) core ct.faultKind mi.label ct.faultIp ct.faultSp ct.faultLr
        ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7
        layout rf (min mi.length layout.msgRegs.size)) := by
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
    hDon cv (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
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
    (msg : IpcMessage) (core : CoreId)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hF : ct.faultWords.isFault = true) :
    replyTransferOnCoreChecked ctx replier c mi (Architecture.regMessageRegs layout rf) msg core
        st =
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
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo, hPop cv (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
  simp only []
  unfold performFaultReplyUnheldAnswer
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswer _ c ct tf hPF mi _ layout rf
    (min mi.length layout.msgRegs.size) 0
    (by simp only [Architecture.regMessageRegs, Array.size_map])
    (fun i _ => wordAt_regMessageRegs layout rf i),
    storeFaultReplyLeg_eq, storeReplyLeg_eq_hold _ _ _ _ hNo]

end SeLe4n.Kernel
