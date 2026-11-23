-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeInPlace
import SeLe4n.Kernel.IPC.CrossCore.FaultAnswerInPlace

/-!
# The reply-receive answering a fault whose receive leg meets a waiting sender

A fault handler's server loop answers a faulted caller with `ReplyRecv`:
seL4-MCS's `doReplyTransfer` takes `handleFaultReply` (no message, no
capability), and then `receiveIPC` takes a sender already queued on the
endpoint.  The specification runs the same order (`replyRecvTransferOnCore` at
the caller's fault answer): the reply leg with the empty message, the take, and
the answer (`faultReplyApplyOnCore`), which writes only the caller.

The answer commutes past the server's held message (`performFaultAnswer_msg`),
so the server's message is written as its frame in place (`writeTakerFrame`).
`replyRecvTransferOnCore_fault_take_inPlace` proves the in-place performer
equal to the specification.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

theorem performFaultAnswer_noResizeDue (X : SystemState) (c : SeLe4n.ThreadId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (n off : Nat)
    (hNo : X.objects.noResizeDue) :
    (performFaultAnswer X c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n
      off).objects.noResizeDue := by
  unfold performFaultAnswer applyFaultRestart faultAbandonOnCore
  split
  · exact updateTcb_noResizeDue _ _ _ hNo
  · split
    · exact updateTcb_noResizeDue _ _ _ (removeRunnableOnCore_noResizeDue _ _ _ hNo)
    · split
      · exact updateTcb_noResizeDue _ _ _ hNo
      · exact updateTcb_noResizeDue _ _ _ hNo

/-- **The fault answer commutes past another thread's message-slot write**:
it reads the caller's placement and home and writes the caller (and, on an
abandon, the run queue), none of which a message-slot write of `r` moves. -/
theorem performFaultAnswer_msg (X : SystemState) (c r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (n off : Nat)
    (hNe : c ≠ r) (hNo : X.objects.noResizeDue) :
    performFaultAnswer (X.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c kind label ip sp lr
        x0 x1 x2 x3 x4 x5 x6 x7 layout rf n off =
      (performFaultAnswer X c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n
        off).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold performFaultAnswer applyFaultRestart faultAbandonOnCore faultAbandonCore
  rw [placedCoreOf?_msg, determineTargetCore_msg]
  split
  · exact updateTcb_msg r ρ μ π X c _ hNo (fun h => absurd h hNe)
  · split
    · rw [removeRunnableOnCore_msg]
      exact updateTcb_msg r ρ μ π _ c _ (removeRunnableOnCore_noResizeDue _ _ _ hNo)
        (fun h => absurd h hNe)
    · split
      · exact updateTcb_msg r ρ μ π X c _ hNo (fun h => absurd h hNe)
      · exact updateTcb_msg r ρ μ π X c _ hNo (fun h => absurd h hNe)

/-- **The reply-receive answering a fault and meeting a waiting sender, as the
specification runs it**: under the reply's guard, for a caller carrying fault
`tf`, the reply leg writes the empty message, transfers nothing, the server's
context return runs, the take (`receiveTake_inPlace`) and the server's priority
walk, and the caller takes the decoded answer (`faultReplyApplyOnCore`). -/
theorem replyRecvTransferOnCore_fault_take_transfer (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat) (msg : IpcMessage)
    (grant : Bool) (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (tf : ThreadFault)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true)
    (hH : ep.sendQ.head = some s)
    (hE2 : (receiveReturnSchedContext true (storeReplyRendezvous st c tid rid IpcMessage.empty)
      tid).objects[epId]? = some (.endpoint ep))
    {sTcb2 : TCB}
    (hT2 : (receiveReturnSchedContext true (storeReplyRendezvous st c tid rid IpcMessage.empty)
      tid).objects[s.toObjId]? = some (.tcb sTcb2))
    (hG2 : receiveTakesInPlace (receiveReturnSchedContext true
      (storeReplyRendezvous st c tid rid IpcMessage.empty) tid) epId tid s sTcb2 = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 =
        .send capAddr mi)
    (hF : sTcb2.ipcFaultSend = false) :
    replyRecvTransferOnCore epId tid rid c label msg grant core st =
      .ok ({ results := #[] }, faultReplyApplyOnCore
          (PriorityInheritance.propagatePipChainCrossCore
            ((wakeThread ((storePopHead (receiveReturnSchedContext true
                (storeReplyRendezvous st c tid rid IpcMessage.empty) tid) epId false s
                sTcb2.queueNext).updateTcb s receiverReady) s core).1.updateTcb tid
              (callReceiverTcb (blockedSenderMessage (storePopHead
                (receiveReturnSchedContext true (storeReplyRendezvous st c tid rid
                  IpcMessage.empty) tid) epId false s sTcb2.queueNext)
                s sTcb2))) tid core).1 c
          (Architecture.decodeFaultReply tf.fault tf.context
            { length := msg.registers.size, extraCaps := 0, label := label } msg.registers)) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  unfold replyRecvTransferOnCore
  rw [replyRecvCallerFaultAnswer?_of_fault st c ct tf label msg hTc hPF]
  simp only [replyRecvLegMessage]
  generalize hQ : receiveReturnSchedContext true
    (storeReplyRendezvous st c tid rid IpcMessage.empty) tid = Q at hE2 hT2 hG2 ⊢
  obtain ⟨hEq, hHead⟩ := replyOnCore_inPlace st tid c tid ct ep0 rid IpcMessage.empty core
    (by simp [IpcMessage.empty]) hT hIpc hRO hG
  have hRec : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  generalize hS1 : storeReplyRendezvous st c tid rid IpcMessage.empty = S1 at hEq hHead hQ
  have hPop : replyRecvPopDonation rid c S1 = .ok (none, S1) := by
    unfold replyRecvPopDonation
    rw [replyFrameHeadHolder?_of_no_head _ _ hHead]
    simp only [popUnheldReplyHead_of_no_head _ _ _ _ hHead]
  have hEp2 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE2
  obtain ⟨hRecv, -, -⟩ := receiveTake_delivered (lend := true) Q epId ep tid (some rid) core s sTcb2 capAddr mi
    hE2 hH hT2 hG2 hR hF
  have hNoCall := receiveTake_dequeuedNoCall Q epId ep tid core s sTcb2
    (blockedSenderMessage (storePopHead Q epId false s sTcb2.queueNext) s sTcb2) hE2 hH hT2 hG2
  unfold endpointReplyRecvAnsweringOnCore
  simp only [hRec, Option.getD_some, hEq, hPop, replyRecvReplyTransfer, hQ, hRecv]
  simp only [replyRecvPostReceiveDonation, hNoCall, Bool.false_eq_true, ↓reduceIte]
  simp [replyRecvAnswerCaller]

/-- The fault take's writes before the server's own frame: the sender popped,
made ready and woken, the server made ready, its priority walk, then the fault
answer to the caller (`performFaultAnswer`). -/
@[noinline] def replyRecvFaultTakeLegs (Y : SystemState) (c tid s : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (nextCode : Nat) (core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (n off : Nat) : SystemState :=
  let W := (wakeThread ((storePopHead Y epId false s (ThreadId.ofOptCode nextCode)).updateTcb s
    receiverReady) s core).1
  let Z := (PriorityInheritance.propagatePipChainCrossCore (W.updateTcb tid receiverReady) tid
    core).1
  performFaultAnswer Z c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n off

/-- **The fault take's tail stages the server's message as its frame**: on any
`Q` where the take runs in place for a sender blocked by a routed
capability-free send, the fault answer and then the server's staged message are
the legs (`replyRecvFaultTakeLegs`) and the server's frame (`writeTakerFrame`). -/
theorem replyRecvFaultTakeFrame_staged (Q : SystemState) (c tid s : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (sTcb : TCB) (core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (n off : Nat) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hNo : Q.objects.noResizeDue) (hNe : tid ≠ c)
    (hE : Q.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : Q.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace Q epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
        .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    Architecture.stageDeliveredMessage (performFaultAnswer
        (PriorityInheritance.propagatePipChainCrossCore
          ((wakeThread ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady) s
            core).1.updateTcb tid (callReceiverTcb (blockedSenderMessage
              (storePopHead Q epId false s sTcb.queueNext) s sTcb))) tid core).1
        c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n off) tid 0 =
      writeTakerFrame
        (replyRecvFaultTakeLegs Q c tid s epId sTcb.queueNextCode core kind label
          ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n off) tid
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
          sTcb.ipcBadgeView).x5 := by
  have hG' := hG
  simp only [receiveTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, _⟩, hRS⟩, hRN⟩, _⟩, _⟩, hRT⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hFH⟩, _⟩ := hSG'
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  have hNeER : epId ≠ tid.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ tid.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ tid.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  obtain ⟨_, hFr⟩ := popHead_inPlace Q epId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hA3 := enqueueRunnableOnCore_agree_of_findsInPlace
    ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady)
    (determineTargetCore ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady) s)
    s _ hT2s rfl (by rw [updateTcb_findsInPlace _ hFr.head_tcb hFH1]; exact hFH1)
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1 hNeSR).trans hO1r
  obtain ⟨rt3, hO3r, _⟩ := hA3.get_tcb hO2r
  have hW3r : (wakeThread ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady)
      s core).1.getTcb? tid = some rt3 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r
  have hMsg := (blockedSender_of_routedSend (storePopHead Q epId false s sTcb.queueNext) s sTcb
    capAddr mi hR hF).2
  generalize blockedSenderMessage (storePopHead Q epId false s sTcb.queueNext) s sTcb = msgS
    at hMsg
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have hNoPY := storePopHead_noResizeDue Q epId false s sTcb.queueNext hNo
  have hNoU := updateTcb_noResizeDue _ s receiverReady hNoPY
  have hNoWY := wakeThread_noResizeDue _ s core hNoU
  have hNoWr := updateTcb_noResizeDue _ tid receiverReady hNoWY
  unfold writeTakerFrame replyRecvFaultTakeLegs
  dsimp only
  rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode]
  generalize (wakeThread ((storePopHead Q epId false s sTcb.queueNext).updateTcb s receiverReady) s
    core).1 = W at hW3r hNoWY hNoWr ⊢
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, ← holdMessage_receiverReady,
    ← SystemState.mapTcbInPlace_mapTcbInPlace, ← SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoWr]
  have hWr : (W.updateTcb tid receiverReady).getTcb? tid = some (receiverReady rt3) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, SystemState.mapTcbInPlace_getTcb?_self,
      hW3r]; rfl
  obtain ⟨x, hX, hXs⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core hNoWr tid _ hWr
  have hNoZ := propagatePipChainCrossCore_noResizeDue _ tid core hNoWr
  generalize (PriorityInheritance.propagatePipChainCrossCore (W.updateTcb tid receiverReady) tid
    core).1 = Z at hX hNoZ ⊢
  rw [performFaultAnswer_msg Z c tid _ _ _ kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf
    n off (fun e => hNe e.symm) hNoZ]
  obtain ⟨x', hX', hXs'⟩ := performFaultAnswer_ipcStateAt Z c tid kind label ip sp lr
    x0 x1 x2 x3 x4 x5 x6 x7 layout rf n off hCT hNoZ x hX
  have hNoD := performFaultAnswer_noResizeDue Z c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7
    layout rf n off hNoZ
  generalize performFaultAnswer Z c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n
    off = D at hX' hNoD ⊢
  have hSzS : msgS.registers.size ≤ 4 := by
    rw [hMsg]
    simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  rw [stageDeliveredMessage_holdMessage _ _ _ hNoD hSzS, hMsg,
    Architecture.returnFrameOfMessage_regMessageBody]
  unfold writeDeliveredFrameIfReady
  rw [hX']
  dsimp only
  rw [if_pos (by rw [hXs', hXs]; rfl)]

/-- **The reply-receive answering a fault and taking a waiting sender, in
place**: the reply's writes with no message (`storeFaultReplyRendezvous`), the
server's context return, the take, the server's priority walk and the fault
answer (`replyRecvFaultTakeLegs`), then the server's frame. -/
@[noinline] def performReplyRecvFaultTakeLegs (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat) :
    SystemState :=
  replyRecvFaultTakeLegs (receiveReturnSchedContextFast true (storeFaultReplyRendezvous st c tid rid)
    tid.val) c tid s epId nextCode core kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf
    (Architecture.regMessageLength layout len) 0

/-- The fault take, its legs and then the server's frame, each out of line so
the arm releases the server's register file between them. -/
@[inline] def performReplyRecvFaultTakeDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  writeTakerFrame (performReplyRecvFaultTakeLegs st c tid rid epId s nextCode core kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf len) tid w0 w1 w2 w3 w4 w5

/-- **The reply-receive answering a fault and taking a waiting sender is the
specification's**: under the reply's guard, for a caller carrying fault `tf`
and a sender `s` at the head of the send queue blocked by a routed
capability-free send, not delivering a fault, whose take writes only its slots
(every check read on the pre-state), the arm's transition, then the server's
staged message, is `performReplyRecvFaultTakeDelivered`. -/
theorem replyRecvTransferOnCore_fault_take_inPlace (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (grant : Bool) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rp : Reply) (ep : Endpoint) (tf : ThreadFault)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true) (hNe : tid ≠ c)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
        .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    (match replyRecvTransferOnCore epId tid rid c label
        { registers := Architecture.regMessageBody layout rf len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvFaultTakeDelivered st c tid rid epId s sTcb.queueNextCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf len
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
  have hNo := replyWakesInPlace_noResizeDue hG
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG
    exact hG.1.1.1.2
  obtain ⟨hE1, sTcb1, hS1, hK, hG1⟩ := storeReplyRendezvous_takeGuard st c tid rid
    IpcMessage.empty ct rp epId ep s sTcb hNo hT hFC hRp hE hS hSC hGt
  have hR1 : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb1.registerContext) SeLe4n.arm64DefaultLayout sTcb1.registerContext 32 =
        .send capAddr mi := by rw [hK.regs]; exact hR
  obtain ⟨hE2, sTcb2, hS2, hK2, hG2⟩ := receiveReturnSchedContext_takeGuard true _ tid
    (storeReplyRendezvous_noResizeDue st c tid rid _ hNo) hE1 hS1 hG1
  have hKt := hK2.trans hK
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb2.registerContext) SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 =
        .send capAddr mi := by rw [hKt.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hKt.faultSend]; exact hF
  rw [replyRecvTransferOnCore_fault_take_transfer st epId tid c rid label _ grant core ct ep0 ep s
    capAddr mi tf hPF hT hIpc hRO hG hH hE2 hS2 hG2 hR2 hF2]
  dsimp only
  rw [CapTransferSummary.capInfo_empty]
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswer _ c ct tf hPF _ _ layout rf
    (Architecture.regMessageLength layout len) 0
    (by simp only [Architecture.regMessageBody_size, Nat.min_self])
    (fun i hi => wordAt_regMessageBody layout rf len i hi)]
  rw [replyRecvFaultTakeFrame_staged _ c tid s epId ep sTcb2 core _ label _ _ _ _ _ _ _ _ _ _ _
    layout rf _ 0 capAddr mi (receiveReturnSchedContext_noResizeDue true _ tid
      (storeReplyRendezvous_noResizeDue st c tid rid _ hNo)) hNe hE2 hH hS2 hG2 hR2 hF2,
    hKt.queueNext, hKt.regs, hKt.ipcBadgeView]
  unfold performReplyRecvFaultTakeDelivered performReplyRecvFaultTakeLegs
  rw [receiveReturnSchedContextFast_eq]
  rfl

end SeLe4n.Kernel
