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
    inlineCount := 4, overflowCount := mi.length - 4 ,
    canReply := Syscall.wordCanReply (readRegWord rf SeLe4n.arm64DefaultLayout.syscallNumReg),
    replyCPtr := SeLe4n.CPtr.ofWord (readRegWord rf SeLe4n.arm64DefaultLayout.replyReg)}

@[simp] theorem longSendDecode_overflowCount (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) :
    (longSendDecode st tid rf capAddr mi).overflowCount = mi.length - 4 := rfl

/-- WS-ZA ZA6.35: **a routed long send whose overflow slots all read decodes**
to the inline words and then those slots' words, as `.send`, with no
capabilities (`longSendDecode`). -/
theorem decodeSyscallArgsFromState_of_routedSendLong_ok (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hR : registerRoutedSyscall opCode SeLe4n.arm64DefaultLayout rf 32 = .sendLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    decodeSyscallArgsFromState opCode st tid SeLe4n.arm64DefaultLayout rf 32 =
      .ok (longSendDecode st tid rf capAddr mi) := by
  obtain ⟨_, _, _, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedSendLong st tid _ rf 32 capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  have hM := mapM_readOverflowWord st tid (mi.length - 4) 0
    (fun j _ h2 => hRead j (by omega))
  rw [hDec]
  unfold mergeOverflowWords
  simp only [syscallReadsOverflow, ↓reduceIte, Array.size_map, hSz, List.range_eq_range', hM, overflowRegsFrom_eq_map, List.map_map,
    bind, Except.bind, pure, Except.pure, longSendDecode]
  rfl

/-- …and one with an overflow slot that does not read is clamped to its inline
words (`clampedFrameDecode`), as seL4 clamps a message with no IPC buffer. -/
theorem decodeSyscallArgsFromState_of_routedSendLong_clamped (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hR : registerRoutedSyscall opCode SeLe4n.arm64DefaultLayout rf 32 = .sendLong capAddr mi)
    (j : Nat) (hj : j < mi.length - 4) (e : Architecture.IpcBufferRead.IpcBufferReadError)
    (h0 : Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .error e) :
    decodeSyscallArgsFromState opCode st tid SeLe4n.arm64DefaultLayout rf 32 =
      .ok (clampedFrameDecode .send rf capAddr mi) := by
  obtain ⟨hGt, _, _, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedSendLong st tid _ rf 32 capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  rw [hDec]
  rw [mergeOverflowWords_clamped st tid rf _ capAddr mi rfl
    ⟨_, by rw [List.range_eq_range']
           exact mapM_readOverflowWord_error st tid (mi.length - 4) 0
             ⟨j, e, Nat.zero_le _, by omega, h0⟩⟩]

/-- **A frame that routes as a long send**, read for the sender `tid` whose
saved registers `rf` are and whose overflow slots all read: it asks to
transfer no capability, and a present sender's message is its inline words
and then the words its IPC buffer holds (`longSendMessage`). -/
theorem routedLongSenderFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout rf)
        SeLe4n.arm64DefaultLayout rf 32 = .sendLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    (∀ endpointId badge grant grantReply, sendCapRequest st endpointId tid (.frame badge grant grantReply) = none) ∧
      ∀ badge grant grantReply, (st.getTcb? tid).isSome = true →
        sendPayloadMessage st tid (.frame badge grant grantReply) =
          longSendMessage SeLe4n.arm64DefaultLayout rf st tid mi.length badge := by
  obtain ⟨hGt, hMax, hX, -⟩ :=
    decodeSyscallArgsFromState_of_routedSendLong st tid _ rf 32 capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  have hD := decodeSyscallArgsFromState_of_routedSendLong_ok st tid rf capAddr mi hR hRead
  cases hT : st.getTcb? tid with
  | none =>
    refine ⟨fun endpointId _ _ _ => ?_, fun _ _ _ h => by cases h⟩
    unfold sendCapRequest
    split
    · rfl
    · rw [hT]
  | some tcb =>
    have hRf := hFrame tcb hT
    subst hRf
    refine ⟨fun endpointId badge grant grantReply => ?_, fun badge grant grantReply _ => ?_⟩
    · unfold sendCapRequest
      split
      · rfl
      · rw [hT]
        simp only [sendPayloadCapRequest, senderFrameCapRequest, blockedSenderDecode, hD]
        have hE : ∀ s t, (senderExtraCapAddrs s t
            (longSendDecode st tid tcb.registerContext capAddr mi).msgInfo.extraCaps).isEmpty = true := by
          intro s t; unfold longSendDecode; simp only [hX, senderExtraCapAddrs_zero]; rfl
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
    inlineCount := 4, overflowCount := mi.length - 4 ,
    canReply := Syscall.wordCanReply (readRegWord rf SeLe4n.arm64DefaultLayout.syscallNumReg),
    replyCPtr := SeLe4n.CPtr.ofWord (readRegWord rf SeLe4n.arm64DefaultLayout.replyReg)}

@[simp] theorem longCallDecode_overflowCount (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) :
    (longCallDecode st tid rf capAddr mi).overflowCount = mi.length - 4 := rfl

/-- **a routed long call whose overflow slots all read decodes**
to the inline words and then those slots' words, as `.call`, with no
capabilities (`longCallDecode`). -/
theorem decodeSyscallArgsFromState_of_routedCallLong_ok (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hR : registerRoutedSyscall opCode SeLe4n.arm64DefaultLayout rf 32 = .callLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    decodeSyscallArgsFromState opCode st tid SeLe4n.arm64DefaultLayout rf 32 =
      .ok (longCallDecode st tid rf capAddr mi) := by
  obtain ⟨_, _, _, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedCallLong st tid _ rf 32 capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  have hM := mapM_readOverflowWord st tid (mi.length - 4) 0
    (fun j _ h2 => hRead j (by omega))
  rw [hDec]
  unfold mergeOverflowWords
  simp only [syscallReadsOverflow, ↓reduceIte, Array.size_map, hSz, List.range_eq_range', hM, overflowRegsFrom_eq_map, List.map_map,
    bind, Except.bind, pure, Except.pure, longCallDecode]
  rfl

/-- …and one with an overflow slot that does not read is clamped to its inline
words (`clampedFrameDecode`), as seL4 clamps a message with no IPC buffer. -/
theorem decodeSyscallArgsFromState_of_routedCallLong_clamped (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hR : registerRoutedSyscall opCode SeLe4n.arm64DefaultLayout rf 32 = .callLong capAddr mi)
    (j : Nat) (hj : j < mi.length - 4) (e : Architecture.IpcBufferRead.IpcBufferReadError)
    (h0 : Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .error e) :
    decodeSyscallArgsFromState opCode st tid SeLe4n.arm64DefaultLayout rf 32 =
      .ok (clampedFrameDecode .call rf capAddr mi) := by
  obtain ⟨hGt, _, _, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedCallLong st tid _ rf 32 capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  rw [hDec]
  rw [mergeOverflowWords_clamped st tid rf _ capAddr mi rfl
    ⟨_, by rw [List.range_eq_range']
           exact mapM_readOverflowWord_error st tid (mi.length - 4) 0
             ⟨j, e, Nat.zero_le _, by omega, h0⟩⟩]

/-- **A long send or call whose buffer does not read is its inline words**:
the decode clamps it to the four registers (`clampedFrameDecode`, seL4's
`handleInvocation` and `copyMRs` with no IPC buffer), so it asks to transfer no
capability and a present sender's message is its register words, as a short
send's of length four. -/
theorem routedClampedSenderFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi0 : MessageInfo)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout rf)
        SeLe4n.arm64DefaultLayout rf 32 = .sendLong capAddr mi0 ∨
      registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout rf)
        SeLe4n.arm64DefaultLayout rf 32 = .callLong capAddr mi0)
    (hUn : ∃ j e, j < mi0.length - 4 ∧
      Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .error e) :
    (∀ endpointId badge grant grantReply, sendCapRequest st endpointId tid (.frame badge grant grantReply) = none) ∧
      ∀ badge grant grantReply, (st.getTcb? tid).isSome = true →
        sendPayloadMessage st tid (.frame badge grant grantReply) =
          { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout rf 4,
            badge := badge } := by
  obtain ⟨j, e, hj, h0⟩ := hUn
  obtain ⟨sid, hD, hX⟩ : ∃ sid, decodeSyscallArgsFromState (blockedSenderCode SeLe4n.arm64DefaultLayout rf) st tid SeLe4n.arm64DefaultLayout rf 32 =
      .ok (clampedFrameDecode sid rf capAddr mi0) ∧ mi0.extraCaps = 0 := by
    rcases hR with hR | hR
    · exact ⟨.send, decodeSyscallArgsFromState_of_routedSendLong_clamped st tid rf capAddr mi0 hR
        j hj e h0, (decodeSyscallArgsFromState_of_routedSendLong st tid _ rf 32 capAddr mi0 hR).2.2.1⟩
    · exact ⟨.call, decodeSyscallArgsFromState_of_routedCallLong_clamped st tid rf capAddr mi0 hR
        j hj e h0, (decodeSyscallArgsFromState_of_routedCallLong st tid _ rf 32 capAddr mi0 hR).2.2.1⟩
  cases hT : st.getTcb? tid with
  | none =>
    refine ⟨fun endpointId _ _ _ => ?_, fun _ _ _ h => by cases h⟩
    unfold sendCapRequest
    split
    · rfl
    · rw [hT]
  | some tcb =>
    have hRf := hFrame tcb hT
    subst hRf
    refine ⟨fun endpointId badge grant grantReply => ?_, fun badge grant grantReply _ => ?_⟩
    · unfold sendCapRequest
      split
      · rfl
      · rw [hT]
        simp only [sendPayloadCapRequest, senderFrameCapRequest, blockedSenderDecode, hD]
        have hE : ∀ s t, (senderExtraCapAddrs s t
            (clampedFrameDecode sid tcb.registerContext capAddr mi0).msgInfo.extraCaps).isEmpty =
              true := by
          intro s t; unfold clampedFrameDecode; simp only [hX, senderExtraCapAddrs_zero]; rfl
        simp only [hE, ↓reduceIte]
        split <;> rfl
    · simp only [sendPayloadMessage, senderFrameDecode, hT, blockedSenderDecode, hD,
        senderFrameMessage, clampedFrameDecode]
      rfl

/-- **A frame that routes as a long call**, read for the caller `tid` whose
saved registers `rf` are and whose overflow slots all read: it asks to
transfer no capability, and a present sender's message is its inline words
and then the words its IPC buffer holds (`longSendMessage`). -/
theorem routedLongCallerFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout rf)
        SeLe4n.arm64DefaultLayout rf 32 = .callLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    (∀ endpointId badge grant grantReply, sendCapRequest st endpointId tid (.frame badge grant grantReply) = none) ∧
      ∀ badge grant grantReply, (st.getTcb? tid).isSome = true →
        sendPayloadMessage st tid (.frame badge grant grantReply) =
          longSendMessage SeLe4n.arm64DefaultLayout rf st tid mi.length badge := by
  obtain ⟨hGt, hMax, hX, -⟩ :=
    decodeSyscallArgsFromState_of_routedCallLong st tid _ rf 32 capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  have hD := decodeSyscallArgsFromState_of_routedCallLong_ok st tid rf capAddr mi hR hRead
  cases hT : st.getTcb? tid with
  | none =>
    refine ⟨fun endpointId _ _ _ => ?_, fun _ _ _ h => by cases h⟩
    unfold sendCapRequest
    split
    · rfl
    · rw [hT]
  | some tcb =>
    have hRf := hFrame tcb hT
    subst hRf
    refine ⟨fun endpointId badge grant grantReply => ?_, fun badge grant grantReply _ => ?_⟩
    · unfold sendCapRequest
      split
      · rfl
      · rw [hT]
        simp only [sendPayloadCapRequest, senderFrameCapRequest, blockedSenderDecode, hD]
        have hE : ∀ s t, (senderExtraCapAddrs s t
            (longCallDecode st tid tcb.registerContext capAddr mi).msgInfo.extraCaps).isEmpty = true := by
          intro s t; unfold longCallDecode; simp only [hX, senderExtraCapAddrs_zero]; rfl
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
    (hR : registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
        .sendLong capAddr mi ∨
      registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
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
  · have hE : ∀ s t, (senderExtraCapAddrs s t d.msgInfo.extraCaps).isEmpty = true := by
      intro s t; rw [hMi, hX, senderExtraCapAddrs_zero]; rfl
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

/-- **Every overflow slot reads**, asked of slot 0: the buffer is in one frame,
so every slot reads where slot 0 does (`ipcBufferOverflowReadable`).  Read as
the entry reads it (`ipcBufferReadMrK`), so the answer builds no `Except` cell
(`overflowWordsRead_spec`). -/
@[inline] def overflowWordsRead (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0 (fun _ => false) (fun _ => true)

theorem overflowWordsRead_spec {st : SystemState} {tid : SeLe4n.ThreadId} {n : Nat}
    (hn : n ≤ Architecture.IpcBufferRead.maxOverflowSlots)
    (h : overflowWordsRead st tid = true) :
    ∀ j, j < n → ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w := by
  unfold overflowWordsRead at h
  rw [Architecture.IpcBufferRead.ipcBufferReadMrK_eq] at h
  cases h0 : Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
  | error e => rw [h0] at h; cases h
  | ok w0 => exact Architecture.IpcBufferRead.ipcBufferOverflowReadable hn ⟨w0, h0⟩

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
    SeLe4n.arm64DefaultLayout rf len s badgeWord badged 0

/-- **The receive's take of a blocked long caller, delivered, is the
specification's**: under `receiveCallTakesInPlace`, for a caller blocked by a
routed capability-free call of more than four words whose overflow slots all
read, the WithCaps receive installs nothing and commits the take, the
rendezvous hands off no SchedContext and runs the receiver's priority walk, the
caller is left blocked on the reply, and staging the receiver's message writes
`performReceiveCallDeliveredLong`'s state. -/
theorem receiveCallLongTake_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallTakesInPlace st endpointId receiver s sTcb rid = true)
    (hF : sTcb.ipcFaultSend = false)
    (hR : registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .callLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st s j = .ok w) :
    endpointReceiveDualWithCapsOnCore endpointId receiver (some rid) core st =
        (receiveCallTakeState st endpointId s sTcb receiver rid,
          .ok (s, { results := #[] }, none)) ∧
      applyReceiveRendezvousHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
          receiver s core =
        .ok (applyReceiverPipHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
          receiver core) ∧
      Architecture.stageDeliveredMessage (applyReceiverPipHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
            receiver core) receiver 0 =
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
      mi.length _ _ 0 (propagatePipChainCrossCore_noResizeDue _ receiver core hNoS) hAX.words hSz
      (by omega)).symm


/-! ## A receive taking a blocked caller within the inline words -/

/-- What a thread whose saved frame routes as a capability-free call within
the inline words sends: its inline words under its capability's badge, and no
capability (`blockedSender_of_routedSend`'s call). -/
theorem blockedSender_of_routedCall (st : SystemState) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (h : registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .call capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    blockedSenderCapRequest st s sTcb = none ∧
      blockedSenderMessage st s sTcb =
        { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout
            sTcb.registerContext mi.length,
          badge := sTcb.ipcBadgeView } := by
  obtain ⟨d, hDec, _, _, _, hMi, hX, hRegs⟩ :=
    decodeSyscallArgsFromState_of_routedCall st s _ _ 32 capAddr mi h
  refine ⟨?_, ?_⟩
  · have hE : ∀ s t, (senderExtraCapAddrs s t d.msgInfo.extraCaps).isEmpty = true := by
      intro s t; rw [hMi, hX, senderExtraCapAddrs_zero]; rfl
    unfold blockedSenderCapRequest senderFrameCapRequest blockedSenderDecode
    rw [hDec]
    simp only [hF, Bool.false_eq_true, ↓reduceIte, hE, ite_self]
  · unfold blockedSenderMessage blockedSenderMessageOf blockedSenderDecode
    rw [hDec]
    simp only [hF, Bool.false_eq_true, ↓reduceIte, senderFrameMessage, hRegs, hMi]
    rfl

/-- **The receive's take of a blocked caller within the inline words,
delivered**: the caller popped, blocked on the reply and linked, the receiver
made ready holding no message, the receiver's priority walk, then the
caller's inline words, read from its saved registers `rf`, written into the
receiver's saved registers (`writeDeliveredFrameIfReady`).  No message is
built on the path a ready receiver takes. -/
@[noinline] def performReceiveCallDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (core : CoreId) (rf : SeLe4n.RegisterFile) (len : Nat) (badgeWord : SeLe4n.Badge)
    (badged : Bool) : SystemState :=
  let Y := (PriorityInheritance.propagatePipChainCrossCore
      (storeReceiveCallReady st endpointId s nextCode receiver rid) receiver core).1
  writeDeliveredFrameIfReady Y receiver
    (Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout rf len badgeWord badged)
    (fun _ => Y.mapTcbInPlace receiver (holdMessage
      { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout rf len,
        badge := SeLe4n.Badge.opt badgeWord badged }))

/-- **The receive's take of a blocked caller within the inline words,
delivered, is the specification's**: under `receiveCallTakesInPlace`, for a
caller blocked by a routed capability-free call of at most four words, the
WithCaps receive installs nothing and commits the take, the rendezvous hands
off no SchedContext and runs the receiver's priority walk, and staging the
receiver's message writes `performReceiveCallDelivered`'s state. -/
theorem receiveCallTake_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallTakesInPlace st endpointId receiver s sTcb rid = true)
    (hF : sTcb.ipcFaultSend = false)
    (hR : registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .call capAddr mi) :
    endpointReceiveDualWithCapsOnCore endpointId receiver (some rid) core st =
        (receiveCallTakeState st endpointId s sTcb receiver rid,
          .ok (s, { results := #[] }, none)) ∧
      applyReceiveRendezvousHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
          receiver s core =
        .ok (applyReceiverPipHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
          receiver core) ∧
      Architecture.stageDeliveredMessage (applyReceiverPipHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
            receiver core) receiver 0 =
        performReceiveCallDelivered st endpointId s sTcb.queueNextCode receiver rid core
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
      exact (blockedSender_of_routedCall st s sTcb capAddr mi hR hF).1
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
    rw [receiveCallTakeState_eq_hold _ _ _ _ _ _ hNo, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoS]
    have hNoY := propagatePipChainCrossCore_noResizeDue _ receiver core hNoS
    have hSz : (blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext) s
        sTcb).registers.size ≤ 4 := by
      rw [(blockedSender_of_routedCall _ s sTcb capAddr mi hR hF).2]
      simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
      have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      omega
    rw [stageDeliveredMessage_holdMessage _ _ _ hNoY hSz,
      (blockedSender_of_routedCall _ s sTcb capAddr mi hR hF).2,
      Architecture.returnFrameOfMessage_regMessageBody, TCB.ipcBadgeView_eq_opt]
    unfold performReceiveCallDelivered
    rw [Architecture.regMessageFrameW_eq]

/-! ## A receive taking a caller it links to no reply -/

/-- The caller a receive delivers without linking it to a reply: seL4
`receiveIPC`'s `setThreadState(sender, Inactive)` -- the Call is answered by
nothing, so the thread runs again only when something restarts it. -/
@[inline] def callerInactive (t : TCB) : TCB := { t with threadState := .Inactive }

/-- **A receive taking a caller it links to no reply writes only its slots**:
`receiveTakesInPlace`'s slots (the pop's, and the receiver an unreserved thread
other than the caller and its successor, rewritten where it stands), the sender
blocked on a call, and the link refused -- the cap grants neither `Grant` nor
`GrantReply`, or the receive supplies no reply object (`suppliesReply`).  seL4
then delivers the message and leaves the caller `Inactive`; no reply object, no
SchedContext and no reply-waiter queue is written, and nobody is woken. -/
@[inline] def receiveCallNoLinkTakesInPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) (suppliesReply : Bool) : Bool :=
  sendWakesInPlace st endpointId s sTcb.queueNext &&
  !receiver.isReserved && receiver != s &&
  (match sTcb.queueNext with
   | none => true
   | some n => receiver != n) &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  (st.getTcb? receiver).isSome &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => !((sTcb.ipcCanGrant || sTcb.ipcCanGrantReply) && suppliesReply)
   | _ => false)

/-- `receiveCallNoLinkTakesInPlace` as it is compiled: the caller's successor
asked of its link code, so no `some` cell is built for a caller with a successor
(`receiveCallNoLinkTakesInPlace_eq_impl`). -/
@[inline] def receiveCallNoLinkTakesInPlaceImpl (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) (suppliesReply : Bool) : Bool :=
  sendWakesInPlaceCode st endpointId s sTcb.queueNextCode &&
  !receiver.isReserved && receiver != s &&
  queueSuccessorDiffers receiver sTcb.queueNextCode &&
  storeLeavesIndexAndTypes st receiver.toObjId .tcb &&
  st.objects.findsInPlace receiver.toObjId &&
  (st.getTcb? receiver).isSome &&
  (match sTcb.ipcState with
   | .blockedOnCall _ => !((sTcb.ipcCanGrant || sTcb.ipcCanGrantReply) && suppliesReply)
   | _ => false)

@[csimp] theorem receiveCallNoLinkTakesInPlace_eq_impl :
    @receiveCallNoLinkTakesInPlace = @receiveCallNoLinkTakesInPlaceImpl := by
  funext st endpointId receiver s sTcb suppliesReply
  unfold receiveCallNoLinkTakesInPlace receiveCallNoLinkTakesInPlaceImpl
  rw [sendWakesInPlaceCode_eq, queueSuccessorDiffers_eq, TCB.ofOptCode_queueNextCode]
  rfl

/-- The state a no-link take commits: the caller popped, stored `.ready` and
made `Inactive`, the receiver made ready holding the caller's message. -/
def receiveCallNoLinkTakeState (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (receiver : SeLe4n.ThreadId) : SystemState :=
  (((storePopHead st endpointId false s sTcb.queueNext).updateTcb s receiverReady).updateTcb s
      callerInactive).updateTcb receiver
    (callReceiverTcb (blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext)
      s sTcb))

/-- **The receive's no-link take, in place**: under
`receiveCallNoLinkTakesInPlace`, the specification's receive pops the caller in
place, stores it `.ready`, makes it `Inactive` and hands the receiver its
message -- the no-link arm of `endpointReceiveDualOnCore`, written in its
slots. -/
theorem receiveCallNoLinkTake_inPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallNoLinkTakesInPlace st endpointId receiver s sTcb replyId.isSome = true) :
    endpointReceiveDualOnCore endpointId receiver replyId core st =
      (receiveCallNoLinkTakeState st endpointId s sTcb receiver, .ok (s, none)) := by
  simp only [receiveCallNoLinkTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, hRS⟩, hRN⟩, hLR⟩, hFR⟩, hRT⟩, hNC⟩ := hG
  obtain ⟨callEp, hCallSt, hNoLink⟩ : ∃ c, sTcb.ipcState = .blockedOnCall c ∧
      ((sTcb.ipcCanGrant || sTcb.ipcCanGrantReply) && replyId.isSome) = false := by
    split at hNC
    · next c hc =>
      refine ⟨c, hc, ?_⟩
      revert hNC
      cases sTcb.ipcCanGrant <;> cases sTcb.ipcCanGrantReply <;> cases replyId <;> simp
    · cases hNC
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, _⟩, hLH⟩, hFH⟩, _⟩ := hSG'
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  have hNeER : endpointId ≠ receiver.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ receiver.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ receiver.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  obtain ⟨hPop, hFr⟩ := popHead_inPlace st endpointId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  unfold endpointReceiveDualOnCore receiveCallNoLinkTakeState
  simp only [(SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE, hH, hPop]
  rw [if_pos (by rw [hCallSt]), if_neg (by rw [hNoLink]; simp)]
  have hM2 : storeTcbIpcStateAndMessage (storePopHead st endpointId false s sTcb.queueNext) s
      .ready none = .ok ((storePopHead st endpointId false s sTcb.queueNext).updateTcb s
        receiverReady) :=
    modifyTcb_eq_updateTcb receiverReady hSRes hFr.head_tcb (hFr.leaves hLH)
  rw [hM2]
  simp only []
  generalize blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext) s sTcb
    = msg
  generalize hS1 : storePopHead st endpointId false s sTcb.queueNext = S1 at *
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1
    hNeSR).trans hO1r
  have hFH2 : (S1.updateTcb s receiverReady).objects.findsInPlace s.toObjId = true :=
    (updateTcb_findsInPlace _ hFr.head_tcb hFH1 _).trans hFH1
  have hO3r := (updateTcb_get?_ne_of_findsInPlace callerInactive hT2s hFH2 hNeSR).trans hO2r
  have hL3 : storeLeavesIndexAndTypes ((S1.updateTcb s receiverReady).updateTcb s callerInactive)
      receiver.toObjId .tcb = true :=
    updateTcb_storeLeaves _ hT2s hFH2
      (updateTcb_storeLeaves _ hFr.head_tcb hFH1 (hFr.leaves hLR))
  have hM4 : storeTcbIpcStateAndMessage
      ((S1.updateTcb s receiverReady).updateTcb s callerInactive) receiver .ready (some msg) =
      .ok (((S1.updateTcb s receiverReady).updateTcb s callerInactive).updateTcb receiver
        (callReceiverTcb msg)) :=
    modifyTcb_eq_updateTcb _ hRRes ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r) hL3
  rw [show (fun t : TCB => { t with threadState := .Inactive }) = callerInactive from rfl, hM4]

/-- **The no-link take dequeues no caller for the hand-off**: the caller it
leaves is `.ready` and `Inactive`, not blocked on a reply, so the rendezvous
hands off nothing. -/
theorem receiveCallNoLinkTake_dequeuedNoCall (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (suppliesReply : Bool)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallNoLinkTakesInPlace st endpointId receiver s sTcb suppliesReply = true) :
    rendezvousDequeuedCall (receiveCallNoLinkTakeState st endpointId s sTcb receiver) s = false := by
  have hG' := hG
  simp only [receiveCallNoLinkTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, _⟩, hRS⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, hFE⟩, _⟩, hFH⟩, _⟩ := hSG'
  have hNo : st.objects.noResizeDue := RHTable.noResizeDue_of_findsInPlace hFE
  obtain ⟨_, hFr⟩ := popHead_inPlace st endpointId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  unfold receiveCallNoLinkTakeState
  generalize hP : storePopHead st endpointId false s sTcb.queueNext = P at hFr hFH1 ⊢
  have hNoP : P.objects.noResizeDue := hP ▸ storePopHead_noResizeDue _ _ _ _ _ hNo
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hFH2 : (P.updateTcb s receiverReady).objects.findsInPlace s.toObjId = true :=
    (updateTcb_findsInPlace _ hFr.head_tcb hFH1 _).trans hFH1
  have hT3s := updateTcb_getTcb?_self_of_findsInPlace callerInactive hT2s hFH2
  have hNoX : ((P.updateTcb s receiverReady).updateTcb s callerInactive).objects.noResizeDue :=
    updateTcb_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _ hNoP)
  unfold rendezvousDequeuedCall
  have hL : ∀ f, lookupTcb (((P.updateTcb s receiverReady).updateTcb s callerInactive).updateTcb
      receiver f) s = lookupTcb ((P.updateTcb s receiverReady).updateTcb s callerInactive) s := by
    intro f
    unfold lookupTcb
    split
    · rfl
    · rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoX, SystemState.getTcb?_mapTcbInPlace,
        if_neg hRS]
  rw [hL]
  simp only [lookupTcb, hSRes, Bool.false_eq_true, ↓reduceIte, hT3s]
  rfl

/-- **The receive's no-link take, delivered**: the caller popped, stored `.ready`
and made `Inactive` (none of its registers written, as seL4's `receiveIPC`), the
receiver made ready, and the six words of the delivered frame -- read from the
caller's saved registers before any write -- written into the receiver's saved
registers.  No message is built, no thread is woken. -/
@[noinline] def performReceiveCallNoLinkDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (receiver : SeLe4n.ThreadId)
    (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  let X := ((storePopHead st endpointId false s (ThreadId.ofOptCode nextCode)).updateTcb
    s receiverReady).updateTcb s callerInactive
  (X.updateTcb receiver receiverReady).mapTcbInPlace
    receiver (withFrameWords w0 w1 w2 w3 w4 w5)

/-- **The receive's no-link take, delivered, is the specification's**: under
`receiveCallNoLinkTakesInPlace`, for a caller blocked by a routed
capability-free call of at most four words, the WithCaps receive installs
nothing and commits the take, the rendezvous hands off nothing (the caller is
`.ready`, not blocked on a reply), and staging the receiver's message writes
`performReceiveCallNoLinkDelivered`'s state. -/
theorem receiveCallNoLinkTake_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallNoLinkTakesInPlace st endpointId receiver s sTcb replyId.isSome = true)
    (hF : sTcb.ipcFaultSend = false)
    (hR : registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .call capAddr mi) :
    let S4 := receiveCallNoLinkTakeState st endpointId s sTcb receiver
    let f := Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext
      mi.length sTcb.ipcBadgeView
    endpointReceiveDualWithCapsOnCore endpointId receiver replyId core st =
        (S4, .ok (s, { results := #[] }, none)) ∧
      applyReceiveRendezvousHandoff S4 receiver s core = .ok S4 ∧
      Architecture.stageDeliveredMessage S4 receiver 0 =
        performReceiveCallNoLinkDelivered st endpointId s sTcb.queueNextCode receiver
          f.x0 f.x1 f.x2 f.x3 f.x4 f.x5 := by
  intro S4 f
  have hTake := receiveCallNoLinkTake_inPlace st endpointId ep receiver replyId core s sTcb
    hE hH hT hG
  have hG' := hG
  simp only [receiveCallNoLinkTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG'
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
  have hMsg := (blockedSender_of_routedCall (storePopHead st endpointId false s sTcb.queueNext)
    s sTcb capAddr mi hR hF).2
  generalize hP : storePopHead st endpointId false s sTcb.queueNext = P at hFr hFH1 hO1r hMsg
  have hNoP : P.objects.noResizeDue := hP ▸ storePopHead_noResizeDue _ _ _ _ _ hNo
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1
    hNeSR).trans hO1r
  have hFH2 : (P.updateTcb s receiverReady).objects.findsInPlace s.toObjId = true :=
    (updateTcb_findsInPlace _ hFr.head_tcb hFH1 _).trans hFH1
  have hT3s := updateTcb_getTcb?_self_of_findsInPlace callerInactive hT2s hFH2
  have hO3r := (updateTcb_get?_ne_of_findsInPlace callerInactive hT2s hFH2 hNeSR).trans hO2r
  generalize hX : (P.updateTcb s receiverReady).updateTcb s callerInactive = X at hT3s hO3r
  have hNoX : X.objects.noResizeDue := hX ▸ updateTcb_noResizeDue _ _ _
    (updateTcb_noResizeDue _ _ _ hNoP)
  have hXr : X.getTcb? receiver = some rt := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r
  have hS4 : S4 = X.updateTcb receiver (callReceiverTcb (blockedSenderMessage P s sTcb)) := by
    show receiveCallNoLinkTakeState st endpointId s sTcb receiver = _
    unfold receiveCallNoLinkTakeState
    rw [hP, hX]
  refine ⟨?_, ?_, ?_⟩
  · have hSnd : receiveRendezvousSender? st endpointId = some s := by
      simp only [receiveRendezvousSender?, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE,
        Option.bind_some, hH]
    have hReq : receiveCapRequest st endpointId = none := by
      unfold receiveCapRequest
      rw [hSnd]
      simp only [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hT]
      exact (blockedSender_of_routedCall st s sTcb capAddr mi hR hF).1
    unfold endpointReceiveDualWithCapsOnCore
    rw [hTake]
    simp only [hSnd, hReq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    rfl
  · -- the dequeued caller is `.ready`, not blocked on a reply: no hand-off
    apply applyReceiveRendezvousHandoff_of_no_call
    have hL : lookupTcb S4 s = lookupTcb X s := by
      rw [hS4]
      unfold lookupTcb
      split
      · rfl
      · rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoX, SystemState.getTcb?_mapTcbInPlace,
          if_neg hRS]
    unfold rendezvousDequeuedCall
    rw [hL]
    simp only [lookupTcb, hSRes, Bool.false_eq_true, ↓reduceIte, hT3s]
    rfl
  · -- staging: the held message is the frame read from the caller's registers
    have hS4' : S4 = (X.updateTcb receiver receiverReady).mapTcbInPlace receiver
        (holdMessage (blockedSenderMessage P s sTcb)) := by
      rw [hS4, SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoX,
        SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoX, SystemState.mapTcbInPlace_mapTcbInPlace,
        holdMessage_receiverReady]
    have hNoY : (X.updateTcb receiver receiverReady).objects.noResizeDue :=
      updateTcb_noResizeDue _ _ _ hNoX
    have hYr : (X.updateTcb receiver receiverReady).getTcb? receiver =
        some (receiverReady rt) := by
      rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoX,
        SystemState.mapTcbInPlace_getTcb?_self, hXr]
      rfl
    have hSz : (blockedSenderMessage P s sTcb).registers.size ≤ 4 := by
      rw [hMsg]
      simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
      have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      omega
    rw [hS4', stageDeliveredMessage_holdMessage _ _ _ hNoY hSz, hMsg,
      Architecture.returnFrameOfMessage_regMessageBody]
    unfold writeDeliveredFrameIfReady performReceiveCallNoLinkDelivered
    rw [hYr]
    simp only [receiverReady, TCB.ipcState_setIpcState, ↓reduceIte]
    rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode, hP, hX]

/-! ## A receive taking a blocked long sender -/

/-- **A long delivery to a ready receiver, from words**: `deliverLongSendFrame`
with the four inline words read before the call (`deliverLongSendFrameWords_eq`),
so no register file is held across the writes before it.  A receiver that is
not ready is left as it is: the delivery is only called on one made ready. -/
@[inline] def deliverLongSendFrameWords (X : SystemState) (r : SeLe4n.ThreadId) (len : Nat)
    (s : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge) (badged : Bool) (capInfo : Nat)
    (w0 w1 w2 w3 : UInt64) : SystemState :=
  match X.getTcb? r with
  | some t =>
    if t.ipcState = .ready then
      let k := overflowSlotsFrom X r 0 (len - 4)
      overflowCopyStore
        (X.mapTcbInPlace r (withFrameWords (Architecture.badgeWordIf badgeWord badged)
          (longMessageInfoWord len k capInfo) w0 w1 w2 w3))
        r s 0 (len - 4)
    else X
  | none => X

theorem deliverLongSendFrameWords_eq (X : SystemState) (r : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (s : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge) (badged : Bool) (capInfo : Nat) (t : TCB)
    (hT : X.getTcb? r = some t) (hR : t.ipcState = .ready) :
    deliverLongSendFrameWords X r len s badgeWord badged capInfo
        (Architecture.regMessageWord layout rf len 0) (Architecture.regMessageWord layout rf len 1)
        (Architecture.regMessageWord layout rf len 2) (Architecture.regMessageWord layout rf len 3) =
      deliverLongSendFrame X r layout rf len s badgeWord badged capInfo := by
  unfold deliverLongSendFrameWords deliverLongSendFrame
  rw [hT]
  simp only [hR, ↓reduceIte]

/-- **The receive's take of a blocked long sender, delivered**: the sender
popped, made ready and woken (none of its registers written, as seL4's
`receiveIPC`), the receiver made ready, then the sender's four inline words
(read from its saved registers before any write) written into the receiver's saved registers and its overflow words copied from
its IPC buffer into the receiver's (`deliverLongSendFrameWords`).  No message
is built. -/
@[noinline] def performReceiveDeliveredLong (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (receiver : SeLe4n.ThreadId) (core : CoreId)
    (len : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool) (w0 w1 w2 w3 : UInt64) :
    SystemState :=
  let X := (wakeThread ((storePopHead st endpointId false s (ThreadId.ofOptCode nextCode)).updateTcb
    s receiverReady) s core).1
  deliverLongSendFrameWords (X.updateTcb receiver receiverReady) receiver len s badgeWord badged 0 w0 w1 w2 w3

/-- **The receive's take of a blocked long sender, delivered, is the
specification's**: under `receiveTakesInPlace`, a sender blocked by a routed
capability-free send of more than four words whose overflow slots all read and
not delivering a fault, the WithCaps receive installs nothing and takes the
in-place writes, the rendezvous hands off no donation, and staging the
receiver's message writes
`performReceiveDeliveredLong`'s state. -/
theorem receiveTakeLong_delivered (st : SystemState) (endpointId : SeLe4n.ObjId) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace st endpointId receiver s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .sendLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st s j = .ok w)
    (hF : sTcb.ipcFaultSend = false) :
    let P := storePopHead st endpointId false s sTcb.queueNext
    let W := wakeThread (P.updateTcb s receiverReady) s core
    let S4 := W.1.updateTcb receiver (callReceiverTcb (blockedSenderMessage P s sTcb))
    endpointReceiveDualWithCapsOnCore endpointId receiver replyId core st =
        (S4, .ok (s, { results := #[] }, W.2)) ∧
      applyReceiveRendezvousHandoff S4 receiver s core = .ok S4 ∧
      Architecture.stageDeliveredMessage S4
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
    have hNoZ : (W.1.updateTcb receiver receiverReady).objects.noResizeDue := hNoY
    have hZr : (W.1.updateTcb receiver receiverReady).getTcb? receiver = some (receiverReady rt3) := hYr
    have hGt := (decodeSyscallArgsFromState_of_routedSendLong st s _ _ 32 capAddr mi hR).1
    have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    rw [hSz] at hGt
    have hAY : ipcBufferReadsAgree (W.1.updateTcb receiver receiverReady) P :=
      (ipcBufferReadsAgree_updateTcb _ receiver receiverReady (fun _ => ⟨rfl, rfl⟩) hNoW).trans
        ((ipcBufferReadsAgree_wakeThread _ s core hNo2).trans
          (ipcBufferReadsAgree_updateTcb _ s receiverReady (fun _ => ⟨rfl, rfl⟩) hNoP))
    rw [hS4, hMsg,
      TCB.ipcBadgeView_eq_opt]
    unfold performReceiveDeliveredLong
    rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode,
      deliverLongSendFrameWords_eq _ _ SeLe4n.arm64DefaultLayout sTcb.registerContext _ _ _ _ 0 _ hZr
        (by simp only [receiverReady, TCB.ipcState_setIpcState])]
    exact (deliverLongSendFrame_eq _ _ receiver s SeLe4n.arm64DefaultLayout sTcb.registerContext
      mi.length _ _ 0 hNoZ hAY.words hSz (by omega)).symm

/-! ## A receive taking a long caller it links to no reply -/

/-- **The receive's no-link take of a long caller, delivered**: the caller
popped, stored `.ready` and made `Inactive` (none of its registers written, as
seL4's `receiveIPC`), the receiver made ready, then the caller's four inline
words (read from its saved registers before any write) written into the
receiver's saved registers and its overflow words copied from its IPC buffer
into the receiver's (`deliverLongSendFrameWords`).  No message is built, no
thread is woken. -/
@[noinline] def performReceiveCallNoLinkDeliveredLong (st : SystemState)
    (endpointId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (receiver : SeLe4n.ThreadId) (len : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (w0 w1 w2 w3 : UInt64) : SystemState :=
  let X := ((storePopHead st endpointId false s (ThreadId.ofOptCode nextCode)).updateTcb
    s receiverReady).updateTcb s callerInactive
  deliverLongSendFrameWords (X.updateTcb receiver receiverReady) receiver len s badgeWord badged 0
    w0 w1 w2 w3

/-- **The receive's no-link take of a long caller, delivered, is the
specification's**: under `receiveCallNoLinkTakesInPlace`, for a caller blocked
by a routed capability-free call of more than four words whose overflow slots
all read, the WithCaps receive installs nothing and commits the take, the
rendezvous hands off nothing (the caller is `.ready`, not blocked on a reply),
and staging the receiver's message writes
`performReceiveCallNoLinkDeliveredLong`'s state. -/
theorem receiveCallNoLinkTakeLong_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallNoLinkTakesInPlace st endpointId receiver s sTcb replyId.isSome = true)
    (hF : sTcb.ipcFaultSend = false)
    (hR : registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout
        sTcb.registerContext) SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .callLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st s j = .ok w) :
    let S4 := receiveCallNoLinkTakeState st endpointId s sTcb receiver
    endpointReceiveDualWithCapsOnCore endpointId receiver replyId core st =
        (S4, .ok (s, { results := #[] }, none)) ∧
      applyReceiveRendezvousHandoff S4 receiver s core = .ok S4 ∧
      Architecture.stageDeliveredMessage S4 receiver 0 =
        performReceiveCallNoLinkDeliveredLong st endpointId s sTcb.queueNextCode receiver
          mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 0)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 1)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 2)
          (Architecture.regMessageWord SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length 3) := by
  intro S4
  have hTake := receiveCallNoLinkTake_inPlace st endpointId ep receiver replyId core s sTcb
    hE hH hT hG
  have hG' := hG
  simp only [receiveCallNoLinkTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG'
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
  have hAP := ipcBufferReadsAgree_storePopHead st endpointId false s sTcb.queueNext hNo
  have hReadP : ∀ j, j < mi.length - 4 → ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr
      (storePopHead st endpointId false s sTcb.queueNext) s j = .ok w := fun j hj => by
    rw [hAP.ipcBufferReadMr]; exact hRead j hj
  have hMsg := (blockedSender_of_routedLong _ s sTcb capAddr mi (.inr hR) hReadP hF).2
  generalize hP : storePopHead st endpointId false s sTcb.queueNext = P at hFr hFH1 hO1r hMsg hAP
  have hNoP : P.objects.noResizeDue := hP ▸ storePopHead_noResizeDue _ _ _ _ _ hNo
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1
    hNeSR).trans hO1r
  have hFH2 : (P.updateTcb s receiverReady).objects.findsInPlace s.toObjId = true :=
    (updateTcb_findsInPlace _ hFr.head_tcb hFH1 _).trans hFH1
  have hT3s := updateTcb_getTcb?_self_of_findsInPlace callerInactive hT2s hFH2
  have hO3r := (updateTcb_get?_ne_of_findsInPlace callerInactive hT2s hFH2 hNeSR).trans hO2r
  have hNo2 : (P.updateTcb s receiverReady).objects.noResizeDue := updateTcb_noResizeDue _ _ _ hNoP
  have hAX : ipcBufferReadsAgree ((P.updateTcb s receiverReady).updateTcb s callerInactive) P :=
    (ipcBufferReadsAgree_updateTcb _ s callerInactive (fun _ => ⟨rfl, rfl⟩) hNo2).trans
      (ipcBufferReadsAgree_updateTcb _ s receiverReady (fun _ => ⟨rfl, rfl⟩) hNoP)
  generalize hX : (P.updateTcb s receiverReady).updateTcb s callerInactive = X at hT3s hO3r hAX
  have hNoX : X.objects.noResizeDue := hX ▸ updateTcb_noResizeDue _ _ _
    (updateTcb_noResizeDue _ _ _ hNoP)
  have hXr : X.getTcb? receiver = some rt := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r
  have hS4 : S4 = X.updateTcb receiver (callReceiverTcb (blockedSenderMessage P s sTcb)) := by
    show receiveCallNoLinkTakeState st endpointId s sTcb receiver = _
    unfold receiveCallNoLinkTakeState
    rw [hP, hX]
  refine ⟨?_, ?_, ?_⟩
  · have hSnd : receiveRendezvousSender? st endpointId = some s := by
      simp only [receiveRendezvousSender?, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE,
        Option.bind_some, hH]
    have hReq : receiveCapRequest st endpointId = none := by
      unfold receiveCapRequest
      rw [hSnd]
      simp only [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hT]
      exact (blockedSender_of_routedLong st s sTcb capAddr mi (.inr hR) hRead hF).1
    unfold endpointReceiveDualWithCapsOnCore
    rw [hTake]
    simp only [hSnd, hReq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    rfl
  · apply applyReceiveRendezvousHandoff_of_no_call
    have hL : lookupTcb S4 s = lookupTcb X s := by
      rw [hS4]
      unfold lookupTcb
      split
      · rfl
      · rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoX, SystemState.getTcb?_mapTcbInPlace,
          if_neg hRS]
    unfold rendezvousDequeuedCall
    rw [hL]
    simp only [lookupTcb, hSRes, Bool.false_eq_true, ↓reduceIte, hT3s]
    rfl
  · have hS4' : S4 = (X.updateTcb receiver receiverReady).mapTcbInPlace receiver
        (holdMessage (blockedSenderMessage P s sTcb)) := by
      rw [hS4, SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoX,
        SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoX, SystemState.mapTcbInPlace_mapTcbInPlace,
        holdMessage_receiverReady]
    have hNoY : (X.updateTcb receiver receiverReady).objects.noResizeDue :=
      updateTcb_noResizeDue _ _ _ hNoX
    have hYr : (X.updateTcb receiver receiverReady).getTcb? receiver =
        some (receiverReady rt) := by
      rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoX,
        SystemState.mapTcbInPlace_getTcb?_self, hXr]
      rfl
    have hGt := (decodeSyscallArgsFromState_of_routedCallLong st s _ _ 32 capAddr mi hR).1
    have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    rw [hSz] at hGt
    have hAY : ipcBufferReadsAgree (X.updateTcb receiver receiverReady) P :=
      (ipcBufferReadsAgree_updateTcb _ receiver receiverReady (fun _ => ⟨rfl, rfl⟩) hNoX).trans hAX
    rw [hS4', hMsg, TCB.ipcBadgeView_eq_opt]
    unfold performReceiveCallNoLinkDeliveredLong
    rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode, hP, hX,
      deliverLongSendFrameWords_eq _ _ SeLe4n.arm64DefaultLayout sTcb.registerContext _ _ _ _ 0 _ hYr
        (by simp only [receiverReady, TCB.ipcState_setIpcState])]
    exact (deliverLongSendFrame_eq _ _ receiver s SeLe4n.arm64DefaultLayout sTcb.registerContext
      mi.length _ _ 0 hNoY hAY.words hSz (by omega)).symm

/-! ## A receive taking a queued fault it links to no reply -/

/-- **The receive's no-link take of a queued fault, delivered**: the faulting
caller popped, stored `.ready` and made `Inactive`, keeping its fault (seL4's
`receiveIPC` leaves a fault it links to no reply `Inactive`), the receiver made
ready, then the fault delivered in place from the caller's fault words
(`deliverFaultFrame`), read before any write.  No thread is woken. -/
@[noinline] def performFaultReceiveNoLinkDelivered (st : SystemState)
    (endpointId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (receiver : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge) (badged : Bool) (k : Nat)
    (flag : Bool) (w0 w1 : UInt64) (lk : UInt64)
    (ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) : SystemState :=
  let X := ((storePopHead st endpointId false s (ThreadId.ofOptCode nextCode)).updateTcb
    s receiverReady).updateTcb s callerInactive
  deliverFaultFrame (X.updateTcb receiver receiverReady) receiver badgeWord badged k flag w0 w1 lk
    ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7

/-- **The receive's no-link take of a queued fault, delivered, is the
specification's**: under `receiveCallNoLinkTakesInPlace`, for a queued caller
holding a fault, the WithCaps receive installs nothing and commits the take,
the rendezvous hands off nothing, and staging the receiver's message writes
`performFaultReceiveNoLinkDelivered`'s state, the fault's words read from the
caller's TCB. -/
theorem receiveFaultNoLinkTake_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (core : CoreId) (s : SeLe4n.ThreadId) (sTcb : TCB) (f : Fault)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallNoLinkTakesInPlace st endpointId receiver s sTcb replyId.isSome = true)
    (hF : sTcb.ipcFaultSend = true) (hf : sTcb.faultWords.fault? = some f) :
    let S4 := receiveCallNoLinkTakeState st endpointId s sTcb receiver
    endpointReceiveDualWithCapsOnCore endpointId receiver replyId core st =
        (S4, .ok (s, { results := #[] }, none)) ∧
      applyReceiveRendezvousHandoff S4 receiver s core = .ok S4 ∧
      Architecture.stageDeliveredMessage S4 receiver 0 =
        performFaultReceiveNoLinkDelivered st endpointId s sTcb.queueNextCode receiver
          (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged sTcb.faultKind sTcb.faultFlag
          sTcb.faultWord0 sTcb.faultWord1 sTcb.faultLookup sTcb.faultIp sTcb.faultSp sTcb.faultLr
          sTcb.faultSpsr sTcb.faultX0 sTcb.faultX1 sTcb.faultX2 sTcb.faultX3 sTcb.faultX4
          sTcb.faultX5 sTcb.faultX6 sTcb.faultX7 := by
  intro S4
  have hTake := receiveCallNoLinkTake_inPlace st endpointId ep receiver replyId core s sTcb
    hE hH hT hG
  have hDq := receiveCallNoLinkTake_dequeuedNoCall st endpointId ep receiver s sTcb _ hE hH hT hG
  have hG' := hG
  simp only [receiveCallNoLinkTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG'
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
  have hMsg : blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext) s sTcb =
      faultMessage f sTcb.faultWords.context
        (SeLe4n.Badge.opt (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged) := by
    unfold blockedSenderMessage blockedSenderMessageOf
    rw [if_pos hF, TCB.pendingFault]
    unfold ThreadFaultWords.decode
    rw [hf]
    rfl
  generalize hP : storePopHead st endpointId false s sTcb.queueNext = P at hFr hFH1 hO1r hMsg
  have hNoP : P.objects.noResizeDue := hP ▸ storePopHead_noResizeDue _ _ _ _ _ hNo
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1
    hNeSR).trans hO1r
  have hFH2 : (P.updateTcb s receiverReady).objects.findsInPlace s.toObjId = true :=
    (updateTcb_findsInPlace _ hFr.head_tcb hFH1 _).trans hFH1
  have hO3r := (updateTcb_get?_ne_of_findsInPlace callerInactive hT2s hFH2 hNeSR).trans hO2r
  generalize hX : (P.updateTcb s receiverReady).updateTcb s callerInactive = X at hO3r
  have hNoX : X.objects.noResizeDue := hX ▸ updateTcb_noResizeDue _ _ _
    (updateTcb_noResizeDue _ _ _ hNoP)
  have hXr : X.getTcb? receiver = some rt := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r
  have hS4 : S4 = X.updateTcb receiver (callReceiverTcb (blockedSenderMessage P s sTcb)) := by
    show receiveCallNoLinkTakeState st endpointId s sTcb receiver = _
    unfold receiveCallNoLinkTakeState
    rw [hP, hX]
  refine ⟨?_, ?_, ?_⟩
  · have hSnd : receiveRendezvousSender? st endpointId = some s := by
      simp only [receiveRendezvousSender?, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE,
        Option.bind_some, hH]
    have hReq : receiveCapRequest st endpointId = none := by
      unfold receiveCapRequest
      rw [hSnd]
      simp only [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hT, blockedSenderCapRequest, hF,
        ↓reduceIte]
    unfold endpointReceiveDualWithCapsOnCore
    rw [hTake]
    simp only [hSnd, hReq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    rfl
  · apply applyReceiveRendezvousHandoff_of_no_call
    exact hDq
  · have hS4' : S4 = (X.updateTcb receiver receiverReady).mapTcbInPlace receiver
        (holdMessage (blockedSenderMessage P s sTcb)) := by
      rw [hS4, SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoX,
        SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoX, SystemState.mapTcbInPlace_mapTcbInPlace,
        holdMessage_receiverReady]
    have hNoY : (X.updateTcb receiver receiverReady).objects.noResizeDue :=
      updateTcb_noResizeDue _ _ _ hNoX
    have hYr : (X.updateTcb receiver receiverReady).getTcb? receiver =
        some (receiverReady rt) := by
      rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoX,
        SystemState.mapTcbInPlace_getTcb?_self, hXr]
      rfl
    rw [hS4', hMsg]
    unfold performFaultReceiveNoLinkDelivered
    rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode, hP, hX]
    exact (deliverFaultFrame_eq _ receiver sTcb.faultWords f hf _ _ hNoY
      ⟨_, hYr, by simp only [receiverReady, TCB.ipcState_setIpcState]⟩).symm

end SeLe4n.Kernel
