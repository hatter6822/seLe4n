-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.LongCallInPlace
import SeLe4n.Kernel.IPC.CrossCore.FaultReceiveInPlace

/-!
# A receive that takes a blocked sender or caller of more than four words

A send or call of more than four words that finds no receiver blocks with its
words where its frame holds them: the first four in its saved registers, the
rest in its IPC buffer.  seL4's receive that takes it copies them then
(`copyMRs`), and so does the specification's (`blockedSenderMessage`, the
frame decoded at the rendezvous).  When every write of the take stays in its
slot, the receive here writes the inline words into the receiver's saved
registers and copies the overflow words from the sender's IPC buffer into the
receiver's, word by word (`deliverLongSendFrame`), so no message is built.

The decodes of a long frame (`longSendDecode`, `longCallDecode`) live here, so
the send and call that meet a waiting receiver and the receive that takes a
blocked one read the same words through one definition.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- WS-ZA ZA6.35: the decode a long send's frame reads to: the inline words
and then its overflow slots' words, as `.send`. -/
def longSendDecode (st : SystemState) (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo) : SyscallDecodeResult :=
  { capAddr, msgInfo := mi, syscallId := .send,
    msgRegs := Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
      (overflowRegsFrom st tid 0 (mi.length - 4)).toArray,
    inlineCount := 4, overflowCount := mi.length - 4 }

@[simp] theorem longSendDecode_overflowCount (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) :
    (longSendDecode st tid rf capAddr mi).overflowCount = mi.length - 4 := rfl

/-- WS-ZA ZA6.35: **a routed long send whose overflow slots all read decodes**
to the inline words and then those slots' words, as `.send`, with no
capabilities (`longSendDecode`). -/
theorem decodeSyscallArgsFromState_of_routedSendLong_ok (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .sendLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout rf 32 =
      .ok (longSendDecode st tid rf capAddr mi) := by
  obtain ⟨_, _, _, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedSendLong st tid _ rf 32 capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  have hM := mapM_readOverflowWord st tid (mi.length - 4) 0
    (fun j _ h2 => hRead j (by omega))
  rw [hDec]
  unfold mergeOverflowWords
  simp only [Array.size_map, hSz, List.range_eq_range', hM, overflowRegsFrom_eq_map, List.map_map,
    bind, Except.bind, pure, Except.pure, longSendDecode]
  rfl

/-- …and one with an overflow slot that does not read is refused as the decode
refuses it. -/
theorem decodeSyscallArgsFromState_of_routedSendLong_error (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .sendLong capAddr mi)
    (j : Nat) (hj : j < mi.length - 4) (e : Architecture.IpcBufferRead.IpcBufferReadError)
    (h0 : Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .error e) :
    decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout rf 32 =
      .error .invalidMessageInfo := by
  obtain ⟨hGt, _, _, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedSendLong st tid _ rf 32 capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  rw [hDec]
  unfold mergeOverflowWords
  simp only [Array.size_map, hSz, List.range_eq_range',
    mapM_readOverflowWord_error st tid (mi.length - 4) 0 ⟨j, e, Nat.zero_le _, by omega, h0⟩,
    bind, Except.bind]

/-- **A frame that routes as a long send**, read for the sender `tid` whose
saved registers `rf` are and whose overflow slots all read: it asks to
transfer no capability, and a present sender's message is its inline words
and then the words its IPC buffer holds (`longSendMessage`). -/
theorem routedLongSenderFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .sendLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    (∀ endpointId badge grant, sendCapRequest st endpointId tid (.frame badge grant) = none) ∧
      ∀ badge grant, (st.getTcb? tid).isSome = true →
        sendPayloadMessage st tid (.frame badge grant) =
          longSendMessage SeLe4n.arm64DefaultLayout rf st tid mi.length badge := by
  obtain ⟨hGt, hMax, hX, -⟩ :=
    decodeSyscallArgsFromState_of_routedSendLong st tid _ rf 32 capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  have hD := decodeSyscallArgsFromState_of_routedSendLong_ok st tid rf capAddr mi hR hRead
  cases hT : st.getTcb? tid with
  | none =>
    refine ⟨fun endpointId _ _ => ?_, fun _ _ h => by cases h⟩
    unfold sendCapRequest
    split
    · rfl
    · rw [hT]
  | some tcb =>
    have hRf := hFrame tcb hT
    subst hRf
    refine ⟨fun endpointId badge grant => ?_, fun badge grant _ => ?_⟩
    · unfold sendCapRequest
      split
      · rfl
      · rw [hT]
        simp only [sendPayloadCapRequest, senderFrameCapRequest, blockedSenderDecode, hD]
        have hE : (Architecture.SyscallArgDecode.decodeExtraCapAddrs
            (longSendDecode st tid tcb.registerContext capAddr mi)).isEmpty = true := by
          unfold Architecture.SyscallArgDecode.decodeExtraCapAddrs longSendDecode
          simp only [hX]
          rfl
        simp only [hE, ↓reduceIte]
        split <;> rfl
    · simp only [sendPayloadMessage, senderFrameDecode, hT, blockedSenderDecode, hD,
        senderFrameMessage, extractMessageRegisters, longSendMessage, longSendDecode]
      congr 1
      apply Array.extract_eq_self_of_le
      simp only [Array.size_append, Architecture.regMessageRegs, Array.size_map, hSz,
        List.size_toArray, overflowRegsFrom_length]
      omega

/-- The decode a long call's frame reads to: the inline words and
then its overflow slots' words, as `.call`. -/
def longCallDecode (st : SystemState) (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo) : SyscallDecodeResult :=
  { capAddr, msgInfo := mi, syscallId := .call,
    msgRegs := Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
      (overflowRegsFrom st tid 0 (mi.length - 4)).toArray,
    inlineCount := 4, overflowCount := mi.length - 4 }

@[simp] theorem longCallDecode_overflowCount (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) :
    (longCallDecode st tid rf capAddr mi).overflowCount = mi.length - 4 := rfl

/-- **a routed long call whose overflow slots all read decodes**
to the inline words and then those slots' words, as `.call`, with no
capabilities (`longCallDecode`). -/
theorem decodeSyscallArgsFromState_of_routedCallLong_ok (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .callLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout rf 32 =
      .ok (longCallDecode st tid rf capAddr mi) := by
  obtain ⟨_, _, _, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedCallLong st tid _ rf 32 capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  have hM := mapM_readOverflowWord st tid (mi.length - 4) 0
    (fun j _ h2 => hRead j (by omega))
  rw [hDec]
  unfold mergeOverflowWords
  simp only [Array.size_map, hSz, List.range_eq_range', hM, overflowRegsFrom_eq_map, List.map_map,
    bind, Except.bind, pure, Except.pure, longCallDecode]
  rfl

/-- …and one with an overflow slot that does not read is refused as the decode
refuses it. -/
theorem decodeSyscallArgsFromState_of_routedCallLong_error (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .callLong capAddr mi)
    (j : Nat) (hj : j < mi.length - 4) (e : Architecture.IpcBufferRead.IpcBufferReadError)
    (h0 : Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .error e) :
    decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout rf 32 =
      .error .invalidMessageInfo := by
  obtain ⟨hGt, _, _, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedCallLong st tid _ rf 32 capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  rw [hDec]
  unfold mergeOverflowWords
  simp only [Array.size_map, hSz, List.range_eq_range',
    mapM_readOverflowWord_error st tid (mi.length - 4) 0 ⟨j, e, Nat.zero_le _, by omega, h0⟩,
    bind, Except.bind]

/-- **A frame that routes as a long call**, read for the caller `tid` whose
saved registers `rf` are and whose overflow slots all read: it asks to
transfer no capability, and a present sender's message is its inline words
and then the words its IPC buffer holds (`longSendMessage`). -/
theorem routedLongCallerFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .callLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    (∀ endpointId badge grant, sendCapRequest st endpointId tid (.frame badge grant) = none) ∧
      ∀ badge grant, (st.getTcb? tid).isSome = true →
        sendPayloadMessage st tid (.frame badge grant) =
          longSendMessage SeLe4n.arm64DefaultLayout rf st tid mi.length badge := by
  obtain ⟨hGt, hMax, hX, -⟩ :=
    decodeSyscallArgsFromState_of_routedCallLong st tid _ rf 32 capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  have hD := decodeSyscallArgsFromState_of_routedCallLong_ok st tid rf capAddr mi hR hRead
  cases hT : st.getTcb? tid with
  | none =>
    refine ⟨fun endpointId _ _ => ?_, fun _ _ h => by cases h⟩
    unfold sendCapRequest
    split
    · rfl
    · rw [hT]
  | some tcb =>
    have hRf := hFrame tcb hT
    subst hRf
    refine ⟨fun endpointId badge grant => ?_, fun badge grant _ => ?_⟩
    · unfold sendCapRequest
      split
      · rfl
      · rw [hT]
        simp only [sendPayloadCapRequest, senderFrameCapRequest, blockedSenderDecode, hD]
        have hE : (Architecture.SyscallArgDecode.decodeExtraCapAddrs
            (longCallDecode st tid tcb.registerContext capAddr mi)).isEmpty = true := by
          unfold Architecture.SyscallArgDecode.decodeExtraCapAddrs longCallDecode
          simp only [hX]
          rfl
        simp only [hE, ↓reduceIte]
        split <;> rfl
    · simp only [sendPayloadMessage, senderFrameDecode, hT, blockedSenderDecode, hD,
        senderFrameMessage, extractMessageRegisters, longSendMessage, longCallDecode]
      congr 1
      apply Array.extract_eq_self_of_le
      simp only [Array.size_append, Architecture.regMessageRegs, Array.size_map, hSz,
        List.size_toArray, overflowRegsFrom_length]
      omega

/-! ## The blocked long frame, read at the rendezvous -/

theorem ipcBufferReadsAgree.symm {a b : SystemState} (h : ipcBufferReadsAgree a b) :
    ipcBufferReadsAgree b a :=
  ⟨fun x => (h.1 x).symm, h.2.symm⟩

/-- **What a thread blocked by a long send or call holds**: a frame that
routes as a capability-free send or call of more than four words, its
overflow slots all reading, asks to transfer no capability, and its message is
its inline words and then the words its IPC buffer holds, under the badge its
capability carried (`longSendMessage`). -/
theorem blockedSender_of_routedLong (st : SystemState) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
        .sendLong capAddr mi ∨
      registerRoutedSyscall SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
        .callLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st s j = .ok w)
    (hF : sTcb.ipcFaultSend = false) :
    blockedSenderCapRequest st s sTcb = none ∧
      blockedSenderMessage st s sTcb =
        longSendMessage SeLe4n.arm64DefaultLayout sTcb.registerContext st s mi.length
          sTcb.ipcBadgeView := by
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  obtain ⟨d, hD, hGt, hMax, hX, hMsgRegs, hMi⟩ : ∃ d,
      blockedSenderDecode st s sTcb = .ok d ∧ 4 < mi.length ∧
      mi.length ≤ maxMessageRegisters ∧ mi.extraCaps = 0 ∧
      d.msgRegs = Architecture.regMessageRegs SeLe4n.arm64DefaultLayout sTcb.registerContext ++
        (overflowRegsFrom st s 0 (mi.length - 4)).toArray ∧ d.msgInfo = mi := by
    rcases hR with hR | hR
    · obtain ⟨hGt, hMax, hX, -⟩ :=
        decodeSyscallArgsFromState_of_routedSendLong st s _ _ 32 capAddr mi hR
      rw [hSz] at hGt
      exact ⟨_, decodeSyscallArgsFromState_of_routedSendLong_ok st s _ capAddr mi hR hRead,
        hGt, hMax, hX, rfl, rfl⟩
    · obtain ⟨hGt, hMax, hX, -⟩ :=
        decodeSyscallArgsFromState_of_routedCallLong st s _ _ 32 capAddr mi hR
      rw [hSz] at hGt
      exact ⟨_, decodeSyscallArgsFromState_of_routedCallLong_ok st s _ capAddr mi hR hRead,
        hGt, hMax, hX, rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · have hE : (Architecture.SyscallArgDecode.decodeExtraCapAddrs d).isEmpty = true := by
      unfold Architecture.SyscallArgDecode.decodeExtraCapAddrs
      rw [hMi, hX]
      rfl
    unfold blockedSenderCapRequest senderFrameCapRequest
    rw [hD]
    simp only [hF, Bool.false_eq_true, ↓reduceIte, hE, ite_self]
  · unfold blockedSenderMessage blockedSenderMessageOf
    rw [hD]
    simp only [hF, Bool.false_eq_true, ↓reduceIte, senderFrameMessage, extractMessageRegisters,
      longSendMessage, hMsgRegs, hMi]
    congr 1
    apply Array.extract_eq_self_of_le
    simp only [Array.size_append, Architecture.regMessageRegs, Array.size_map, hSz,
      List.size_toArray, overflowRegsFrom_length]
    omega

/-- **Every overflow slot of `n` reads**, asked of slot 0 and the slot
`overflowSecondRead` names, each read as the entry reads it
(`ipcBufferReadMrK`), so the answer builds no `Except` cell
(`overflowWordsRead_spec`). -/
@[inline] def overflowWordsRead (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (n : Nat) : Bool :=
  Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0 (fun _ => false) (fun _ =>
    Architecture.IpcBufferRead.ipcBufferReadMrK st tid
      (Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer n)
      (fun _ => false) (fun _ => true))

theorem overflowWordsRead_spec {st : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB} {n : Nat}
    (hT : st.getTcb? tid = some tcb) (hn : n ≤ Architecture.IpcBufferRead.maxOverflowSlots)
    (h : overflowWordsRead st tid tcb n = true) :
    ∀ j, j < n → ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w := by
  unfold overflowWordsRead at h
  rw [Architecture.IpcBufferRead.ipcBufferReadMrK_eq] at h
  cases h0 : Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
  | error e => rw [h0] at h; cases h
  | ok w0 =>
    rw [h0] at h
    dsimp only at h
    rw [Architecture.IpcBufferRead.ipcBufferReadMrK_eq] at h
    cases h1 : Architecture.IpcBufferRead.ipcBufferReadMr st tid
        (Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer n) with
    | error e => rw [h1] at h; cases h
    | ok w1 =>
      exact Architecture.IpcBufferRead.ipcBufferOverflowReadable hT hn ⟨w0, h0⟩ ⟨w1, h1⟩

/-! ## A receive taking a blocked long caller -/

theorem ipcBufferReadsAgree_storeReceiveCallReady (st : SystemState)
    (endpointId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (storeReceiveCallReady st endpointId s nextCode receiver rid) st := by
  unfold storeReceiveCallReady
  dsimp only
  generalize hP : storePopHead st endpointId false s (ThreadId.ofOptCode nextCode) = P
  have a0 : ipcBufferReadsAgree P st := hP ▸ ipcBufferReadsAgree_storePopHead st endpointId false s _ hNo
  have hNo0 : P.objects.noResizeDue := hP ▸ storePopHead_noResizeDue st endpointId false s _ hNo
  generalize hQ1 : P.updateTcb s (callCallerTcb endpointId receiver) = Q1
  have a1 : ipcBufferReadsAgree Q1 P := hQ1 ▸
    ipcBufferReadsAgree_updateTcb P s (callCallerTcb endpointId receiver) (fun _ => ⟨rfl, rfl⟩) hNo0
  have hNo1 : Q1.objects.noResizeDue := hQ1 ▸ updateTcb_noResizeDue _ _ _ hNo0
  generalize hQ2 : Q1.modifyObject rid.toObjId (replyWithCaller s) = Q2
  have a2 : ipcBufferReadsAgree Q2 Q1 := hQ2 ▸
    ipcBufferReadsAgree_modifyObject Q1 rid.toObjId (replyWithCaller s)
      (fun o => by cases o <;> rfl) hNo1
  have hNo2 : Q2.objects.noResizeDue := hQ2 ▸ modifyObject_noResizeDue _ _ _ hNo1
  generalize hQ3 : Q2.updateTcb s
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) = Q3
  have a3 : ipcBufferReadsAgree Q3 Q2 := hQ3 ▸
    ipcBufferReadsAgree_updateTcb Q2 s _ (fun _ => ⟨rfl, rfl⟩) hNo2
  have hNo3 : Q3.objects.noResizeDue := hQ3 ▸ updateTcb_noResizeDue _ _ _ hNo2
  have a4 : ipcBufferReadsAgree (Q3.updateTcb receiver receiverReady) Q3 :=
    ipcBufferReadsAgree_updateTcb Q3 receiver receiverReady (fun _ => ⟨rfl, rfl⟩) hNo3
  exact (ipcBufferReadsAgree_linkReplyWaiter _ s receiver).trans
    (a4.trans (a3.trans (a2.trans (a1.trans a0))))

/-- **The receive's take of a blocked long caller, delivered**: the caller
popped, blocked on the reply and linked, the receiver made ready holding no
message, the receiver's priority walk, then the caller's inline words (read
from its saved registers `rf` before any write) written into the receiver's
saved registers and its overflow words copied from its IPC buffer into the
receiver's (`deliverLongSendFrame`). -/
@[noinline] def performReceiveCallDeliveredLong (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (core : CoreId) (rf : SeLe4n.RegisterFile) (len : Nat) (badgeWord : SeLe4n.Badge)
    (badged : Bool) : SystemState :=
  deliverLongSendFrame (PriorityInheritance.propagatePipChainCrossCore
      (storeReceiveCallReady st endpointId s nextCode receiver rid) receiver core).1 receiver
    SeLe4n.arm64DefaultLayout rf len s badgeWord badged

/-- **The receive's take of a blocked long caller, delivered, is the
specification's**: under `receiveCallTakesInPlace`, for a caller blocked by a
routed capability-free call of more than four words whose overflow slots all
read, the WithCaps receive installs nothing and commits the take, the
rendezvous hands off no SchedContext and runs the receiver's priority walk, the
caller left blocked on the reply is owed no completion frame, and staging the
receiver's message writes `performReceiveCallDeliveredLong`'s state. -/
theorem receiveCallLongTake_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (root : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallTakesInPlace st endpointId receiver s sTcb rid = true)
    (hF : sTcb.ipcFaultSend = false)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .callLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st s j = .ok w) :
    endpointReceiveDualWithCapsOnCore endpointId receiver (some rid) root slot core st =
        (receiveCallTakeState st endpointId s sTcb receiver rid,
          .ok (s, { results := #[] }, none)) ∧
      applyReceiveRendezvousHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
          receiver s core =
        .ok (applyReceiverPipHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
          receiver core) ∧
      Architecture.stageDeliveredMessage (Architecture.stageWokenSendCompletion
          (applyReceiverPipHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
            receiver core) (some s)) receiver 0 =
        performReceiveCallDeliveredLong st endpointId s sTcb.queueNextCode receiver rid core
          sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged := by
  obtain ⟨hTake, hIpc, hBs, hBr⟩ :=
    receiveCallTake_inPlace st endpointId ep receiver rid core s sTcb hE hH hT hG
  have hG' := hG
  simp only [receiveCallTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hRT⟩, _⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, hFE⟩, _⟩, _⟩, _⟩ := hSG'
  have hNo : st.objects.noResizeDue := RHTable.noResizeDue_of_findsInPlace hFE
  obtain ⟨rt, hRTo, hDN⟩ : ∃ rt, st.getTcb? receiver = some rt ∧
      callDonatesNothing sTcb rt = true := by
    split at hRT
    · next rt h => exact ⟨rt, h, hRT⟩
    · cases hRT
  have hTs : st.getTcb? s = some sTcb := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨x, hx, hxI⟩ := Option.map_eq_some_iff.mp hIpc
  refine ⟨?_, ?_, ?_⟩
  · have hSnd : receiveRendezvousSender? st endpointId = some s := by
      simp only [receiveRendezvousSender?, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE,
        Option.bind_some, hH]
    have hReq : receiveCapRequest st endpointId = none := by
      unfold receiveCapRequest
      rw [hSnd]
      simp only [hTs]
      exact (blockedSender_of_routedLong st s sTcb capAddr mi (.inr hR) hRead hF).1
    unfold endpointReceiveDualWithCapsOnCore
    rw [hTake]
    simp only [hSnd, hReq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    rfl
  · have hCall : rendezvousDequeuedCall (receiveCallTakeState st endpointId s sTcb receiver rid)
        s = true := by
      unfold rendezvousDequeuedCall
      simp only [lookupTcb, hSRes, Bool.false_eq_true, ↓reduceIte, hx, hxI]
    obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
      ((SeLe4n.ThreadId.toValid?_isSome_iff s).mpr hSRes)
    obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.mp
      ((SeLe4n.ThreadId.toValid?_isSome_iff receiver).mpr hRRes)
    have hNone : callDonationSchedContext? (receiveCallTakeState st endpointId s sTcb receiver rid)
        s receiver = none := by
      rw [callDonationSchedContext?_congr (s := st) hBs hBr, callDonationSchedContext?_eq_bindings]
      simp only [lookupTcb, hRRes, hSRes, Bool.false_eq_true, ↓reduceIte, hRTo, hTs,
        Option.map_some]
      revert hDN
      unfold callDonatesNothing
      cases rt.schedContextBinding <;> cases sTcb.schedContextBinding <;>
        simp [donationOfBindings, SchedContextBinding.scId?]
    unfold applyReceiveRendezvousHandoff
    rw [applyReceiveRendezvousDonation_of_no_donation _ receiver s sv rv hsv hrv hNone]
    simp only [hCall, ↓reduceIte]
  · have hNoS := storeReceiveCallReady_noResizeDue st endpointId s sTcb.queueNextCode receiver
      rid hNo
    have hNo4 : (receiveCallTakeState st endpointId s sTcb receiver rid).objects.noResizeDue := by
      unfold receiveCallTakeState
      exact linkReplyWaiter_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _
        (updateTcb_noResizeDue _ _ _ (modifyObject_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _
          (storePopHead_noResizeDue _ _ _ _ _ hNo)))))
    obtain ⟨x', hx', hxI'⟩ := propagatePipChainCrossCore_ipcStateCarried _ receiver core hNo4 s x hx
    unfold applyReceiverPipHandoff
    rw [Architecture.stageWokenSendCompletion_id_when_not_ready _ s x' hx'
      (by rw [hxI', hxI]; simp)]
    rw [receiveCallTakeState_eq_hold _ _ _ _ _ _ hNo, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoS]
    have hAP := ipcBufferReadsAgree_storePopHead st endpointId false s sTcb.queueNext hNo
    have hReadP : ∀ j, j < mi.length - 4 → ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr
        (storePopHead st endpointId false s sTcb.queueNext) s j = .ok w := fun j hj => by
      rw [hAP.ipcBufferReadMr]; exact hRead j hj
    rw [(blockedSender_of_routedLong _ s sTcb capAddr mi (.inr hR) hReadP hF).2,
      TCB.ipcBadgeView_eq_opt]
    have hGt := (decodeSyscallArgsFromState_of_routedCallLong st s _ _ 32 capAddr mi hR).1
    have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    rw [hSz] at hGt
    have hAX := (ipcBufferReadsAgree_propagatePipChainCrossCore _ receiver core hNoS).trans
      ((ipcBufferReadsAgree_storeReceiveCallReady st endpointId s sTcb.queueNextCode receiver rid
        hNo).trans hAP.symm)
    unfold performReceiveCallDeliveredLong
    exact (deliverLongSendFrame_eq _ _ receiver s SeLe4n.arm64DefaultLayout sTcb.registerContext
      mi.length _ _ (propagatePipChainCrossCore_noResizeDue _ receiver core hNoS) hAX hSz
      (by omega)).symm

/-- A woken sender's completion frame keeps every read. -/
theorem ipcBufferReadsAgree_stageWokenSendCompletion (Y : SystemState) (t : SeLe4n.ThreadId)
    (hNo : Y.objects.noResizeDue) :
    ipcBufferReadsAgree (Architecture.stageWokenSendCompletion Y (some t)) Y := by
  unfold Architecture.stageWokenSendCompletion
  dsimp only
  cases Y.getTcb? t with
  | none => exact .refl Y
  | some tcb =>
    dsimp only
    split
    · unfold Architecture.writeReturnFrameToTcb
      exact ipcBufferReadsAgree_updateTcb _ t _ (fun _ => ⟨rfl, rfl⟩) hNo
    · exact .refl Y

/-! ## A receive taking a blocked long sender -/

/-- **A long delivery to a ready receiver, from words**: `deliverLongSendFrame`
with the four inline words read before the call (`deliverLongSendFrameWords_eq`),
so no register file is held across the writes before it.  A receiver that is
not ready is left as it is: the delivery is only called on one made ready. -/
@[inline] def deliverLongSendFrameWords (X : SystemState) (r : SeLe4n.ThreadId) (len : Nat)
    (s : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge) (badged : Bool) (w0 w1 w2 w3 : UInt64) :
    SystemState :=
  match X.getTcb? r with
  | some t =>
    if t.ipcState = .ready then
      let k := overflowSlotsFrom X r 0 (len - 4)
      overflowCopyStore
        (X.mapTcbInPlace r (withFrameWords (Architecture.badgeWordIf badgeWord badged)
          (longMessageInfoWord len k) w0 w1 w2 w3))
        r s 0 (len - 4)
    else X
  | none => X

theorem deliverLongSendFrameWords_eq (X : SystemState) (r : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (s : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge) (badged : Bool) (t : TCB)
    (hT : X.getTcb? r = some t) (hR : t.ipcState = .ready) :
    deliverLongSendFrameWords X r len s badgeWord badged
        (Architecture.regMessageWord layout rf len 0) (Architecture.regMessageWord layout rf len 1)
        (Architecture.regMessageWord layout rf len 2) (Architecture.regMessageWord layout rf len 3) =
      deliverLongSendFrame X r layout rf len s badgeWord badged := by
  unfold deliverLongSendFrameWords deliverLongSendFrame
  rw [hT]
  simp only [hR, ↓reduceIte]

/-- **The receive's take of a blocked long sender, delivered**: the sender
popped, made ready and woken with its completion frame, the receiver made
ready, then the sender's four inline words (read from its saved registers
before any write, so the completion frame's write to them copies nothing)
written into the receiver's saved registers and its overflow words copied from
its IPC buffer into the receiver's (`deliverLongSendFrameWords`).  No message
is built. -/
@[noinline] def performReceiveDeliveredLong (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (receiver : SeLe4n.ThreadId) (core : CoreId)
    (len : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool) (w0 w1 w2 w3 : UInt64) :
    SystemState :=
  let X := (wakeThread ((storePopHead st endpointId false s (ThreadId.ofOptCode nextCode)).updateTcb
    s receiverReady) s core).1
  deliverLongSendFrameWords (Architecture.stageWokenSendCompletion
    (X.updateTcb receiver receiverReady) (some s)) receiver len s badgeWord badged w0 w1 w2 w3

/-- **The receive's take of a blocked long sender, delivered, is the
specification's**: under `receiveTakesInPlace`, a sender blocked by a routed
capability-free send of more than four words whose overflow slots all read and
not delivering a fault, the WithCaps receive installs nothing and takes the
in-place writes, the rendezvous hands off no donation, and staging the woken
sender's completion and the receiver's message writes
`performReceiveDeliveredLong`'s state. -/
theorem receiveTakeLong_delivered (st : SystemState) (endpointId : SeLe4n.ObjId) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (root : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace st endpointId receiver s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .sendLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st s j = .ok w)
    (hF : sTcb.ipcFaultSend = false) :
    let P := storePopHead st endpointId false s sTcb.queueNext
    let W := wakeThread (P.updateTcb s receiverReady) s core
    let S4 := W.1.updateTcb receiver (callReceiverTcb (blockedSenderMessage P s sTcb))
    endpointReceiveDualWithCapsOnCore endpointId receiver replyId root slot core st =
        (S4, .ok (s, { results := #[] }, W.2)) ∧
      applyReceiveRendezvousHandoff S4 receiver s core = .ok S4 ∧
      Architecture.stageDeliveredMessage (Architecture.stageWokenSendCompletion S4 (some s))
          receiver 0 =
        performReceiveDeliveredLong st endpointId s sTcb.queueNextCode receiver core
          mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 0)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 1)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 2)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 3) := by
  intro P W S4
  have hTake := receiveTake_inPlace st endpointId ep receiver replyId core s sTcb hE hH hT hG
  have hG' := hG
  simp only [receiveTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, hRS⟩, hRN⟩, hLR⟩, hFR⟩, hRT⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, hFE⟩, _⟩, hFH⟩, _⟩ := hSG'
  have hNo : st.objects.noResizeDue := RHTable.noResizeDue_of_findsInPlace hFE
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  have hNeER : endpointId ≠ receiver.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ receiver.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ receiver.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  obtain ⟨_, hFr⟩ := popHead_inPlace st endpointId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  have hNoP : P.objects.noResizeDue := storePopHead_noResizeDue _ _ _ _ _ hNo
  have hAP := ipcBufferReadsAgree_storePopHead st endpointId false s sTcb.queueNext hNo
  have hReadP : ∀ j, j < mi.length - 4 → ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr P s j =
      .ok w := fun j hj => by
    show ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr
      (storePopHead st endpointId false s sTcb.queueNext) s j = .ok w
    rw [hAP.ipcBufferReadMr]; exact hRead j hj
  obtain ⟨_, hMsg⟩ := blockedSender_of_routedLong P s sTcb capAddr mi (.inl hR) hReadP hF
  have hRS' : s ≠ receiver := fun h => hRS h.symm
  have hT2s : (P.updateTcb s receiverReady).getTcb? s = some (receiverReady (tcbOffQueue sTcb)) :=
    updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hA3 := enqueueRunnableOnCore_agree_of_findsInPlace (P.updateTcb s receiverReady)
    (determineTargetCore (P.updateTcb s receiverReady) s) s _ hT2s rfl
    (by rw [updateTcb_findsInPlace _ hFr.head_tcb hFH1]; exact hFH1)
  have hNo2 : (P.updateTcb s receiverReady).objects.noResizeDue := updateTcb_noResizeDue _ _ _ hNoP
  have hNoW : W.1.objects.noResizeDue := wakeThread_noResizeDue _ _ _ hNo2
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1 hNeSR).trans hO1r
  obtain ⟨rt3, hO3r, _⟩ := hA3.get_tcb hO2r
  have hW3r : W.1.getTcb? receiver = some rt3 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r
  refine ⟨?_, ?_, ?_⟩
  · -- the WithCaps receive installs nothing
    have hSnd : receiveRendezvousSender? st endpointId = some s := by
      simp only [receiveRendezvousSender?, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE,
        Option.bind_some, hH]
    have hReq : receiveCapRequest st endpointId = none := by
      unfold receiveCapRequest
      rw [hSnd]
      simp only [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hT]
      exact (blockedSender_of_routedLong st s sTcb capAddr mi (.inl hR) hRead hF).1
    unfold endpointReceiveDualWithCapsOnCore
    rw [hTake]
    simp only [hSnd, hReq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    rfl
  · -- the dequeued sender was no caller: no donation
    apply applyReceiveRendezvousHandoff_of_no_call
    have hL : lookupTcb S4 s = lookupTcb W.1 s := by
      show lookupTcb (W.1.updateTcb receiver _) s = _
      unfold lookupTcb
      split
      · rfl
      · rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoW, SystemState.getTcb?_mapTcbInPlace,
          if_neg hRS]
    have h1 : rendezvousDequeuedCall S4 s = rendezvousDequeuedCall W.1 s := by
      unfold rendezvousDequeuedCall; rw [hL]
    rw [h1, show W.1 = enqueueRunnableOnCore (P.updateTcb s receiverReady)
      (determineTargetCore (P.updateTcb s receiverReady) s) s from rfl,
      rendezvousDequeuedCall_of_objectsAgreeOffRunLinks hA3 s]
    unfold rendezvousDequeuedCall
    simp only [lookupTcb, hSRes, Bool.false_eq_true, ↓reduceIte, hT2s, receiverReady,
      TCB.ipcState_setIpcState]
  · -- staging: the held message is the frame read from the sender's registers
    have hS4 : S4 = (W.1.updateTcb receiver receiverReady).mapTcbInPlace receiver
        (holdMessage (blockedSenderMessage P s sTcb)) := by
      show W.1.updateTcb receiver _ = _
      rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoW,
        SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoW, SystemState.mapTcbInPlace_mapTcbInPlace,
        holdMessage_receiverReady]
    have hNoY : (W.1.updateTcb receiver receiverReady).objects.noResizeDue :=
      updateTcb_noResizeDue _ _ _ hNoW
    have hYr : (W.1.updateTcb receiver receiverReady).getTcb? receiver =
        some (receiverReady rt3) := by
      rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoW,
        SystemState.mapTcbInPlace_getTcb?_self, hW3r]
      rfl
    have hNoZ : (Architecture.stageWokenSendCompletion (W.1.updateTcb receiver receiverReady)
        (some s)).objects.noResizeDue := by
      unfold Architecture.stageWokenSendCompletion
      dsimp only
      split
      · split
        · exact updateTcb_noResizeDue _ _ _ hNoY
        · exact hNoY
      · exact hNoY
    have hZr : (Architecture.stageWokenSendCompletion (W.1.updateTcb receiver receiverReady)
        (some s)).getTcb? receiver = some (receiverReady rt3) := by
      unfold Architecture.stageWokenSendCompletion
      dsimp only
      split
      · split
        · unfold Architecture.writeReturnFrameToTcb
          rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoY, SystemState.getTcb?_mapTcbInPlace,
            if_neg hRS', hYr]
        · exact hYr
      · exact hYr
    have hGt := (decodeSyscallArgsFromState_of_routedSendLong st s _ _ 32 capAddr mi hR).1
    have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    rw [hSz] at hGt
    have hAY : ipcBufferReadsAgree (W.1.updateTcb receiver receiverReady) P :=
      (ipcBufferReadsAgree_updateTcb _ receiver receiverReady (fun _ => ⟨rfl, rfl⟩) hNoW).trans
        ((ipcBufferReadsAgree_wakeThread _ s core hNo2).trans
          (ipcBufferReadsAgree_updateTcb _ s receiverReady (fun _ => ⟨rfl, rfl⟩) hNoP))
    have hAZ := (ipcBufferReadsAgree_stageWokenSendCompletion _ s hNoY).trans hAY
    rw [hS4, stageWokenSendCompletion_msg _ receiver s _ _ _ hRS' hNoY, hMsg,
      TCB.ipcBadgeView_eq_opt]
    unfold performReceiveDeliveredLong
    rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode,
      deliverLongSendFrameWords_eq _ _ SeLe4n.arm64DefaultLayout sTcb.registerContext _ _ _ _ _ hZr
        (by simp only [receiverReady, TCB.ipcState_setIpcState])]
    exact (deliverLongSendFrame_eq _ _ receiver s SeLe4n.arm64DefaultLayout sTcb.registerContext
      mi.length _ _ hNoZ hAZ hSz (by omega)).symm

end SeLe4n.Kernel
