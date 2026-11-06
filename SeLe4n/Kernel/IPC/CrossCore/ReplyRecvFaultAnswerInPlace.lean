-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.FaultInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvInPlace

/-!
# A reply-receive answering a faulted caller, written in place

A fault handler's server loop answers each fault with `ReplyRecv`.  The arm's
transition (`replyRecvTransferOnCore`) runs the reply leg with the empty message,
the receive leg unchanged, and answers the caller with its fault reply
(`faultReplyApplyOnCore` of `decodeFaultReply`) in place of staging a delivered
message.  When the reply's writes and the receive's block each stay in their
slots (`replyRecvBlocksFast`, the guard of the blocking reply-receive), those
writes are the reply's with no message (`storeFaultReplyRendezvous`), the
receive's block and the server's priority walk, and the answer is the one the
`.reply` arm applies (`performFaultAnswer`), read from the caller's fault words
and the reply's registers past MR0, so neither the fault, the reply's message,
the outcome nor a frame is built (`replyRecvTransferOnCore_fault_blocks_inPlace`).
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

end SeLe4n.Kernel
