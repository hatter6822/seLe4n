-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.RegisterDecode

/-! # What a routed register read pins about the decode

The register file routes a syscall (`registerRoutedSyscall`) before any decode
record exists.  These theorems state, per route, that the full decode
(`decodeSyscallArgsFromState`) succeeds on the same registers and agrees with
the route: the syscall, the capability address, no overflow word, and the
route's operands.

They live apart from `RegisterDecode` because their case analysis over the
route's comparison chain is the slowest elaboration in that module, and only
the refusal-carrying entry (`RefusalCarryingEntry`) and the in-place receive
(`EndpointReceiveInPlace`) consume them: every other importer of the decode
layer starts without waiting for them.
-/

namespace SeLe4n.Kernel.Architecture.RegisterDecode

open SeLe4n
open SeLe4n.Model

/-- What a routed read pins about the decode: it succeeds, as `sid`, at
    `capAddr`, with no overflow words; the decoded registers are the mapped
    layout registers. -/
private theorem decodeSyscallArgsFromState_of_routed
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo) (sid : SyscallId)
    (hB : layout.capPtrReg.val < regCount ∧ layout.msgInfoReg.val < regCount ∧
      layout.syscallNumReg.val < regCount ∧ layout.msgRegs.all (·.val < regCount) = true)
    (hC : decodeCapPtr (readReg regs layout.capPtrReg) = .ok capAddr)
    (hM : decodeMsgInfo (readReg regs layout.msgInfoReg) = .ok msgInfo)
    (hLen : msgInfo.length ≤ layout.msgRegs.size)
    (hS : (readReg regs layout.syscallNumReg).val = sid.toNat) :
    decodeSyscallArgsFromState st tid layout regs regCount =
      .ok { capAddr, msgInfo, syscallId := sid,
            msgRegs := layout.msgRegs.map (readReg regs),
            inlineCount := layout.msgRegs.size, overflowCount := 0 } := by
  rw [decodeSyscallArgsFromState_eq_impl]
  unfold decodeSyscallArgsFromStateImpl
  rw [if_pos hB]
  have hId : decodeSyscallId (readReg regs layout.syscallNumReg) = .ok sid := by
    simp only [decodeSyscallId, hS, SyscallId.ofNat_toNat]
  simp only [hC, hM, hId, hLen, ↓reduceIte]

theorem decodeSyscallArgsFromState_of_routedSignal
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (badge : Badge)
    (h : registerRoutedSyscall layout regs regCount = .signal capAddr badge) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .notificationSignal ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧
      ∃ h0 : 0 < decoded.msgRegs.size,
        badge = Badge.ofNatMasked (decoded.msgRegs[0]'h0).val := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      cases h
      refine ⟨_, hD .notificationSignal ‹_›, rfl, rfl, rfl,
        by simpa only [Array.size_map] using ‹0 < layout.msgRegs.size›,
        by simp only [Array.getElem_map, readReg_val_eq_word, Badge.ofWord_eq_ofNatMasked]⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

theorem decodeSyscallArgsFromState_of_routedWait
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr)
    (h : registerRoutedSyscall layout regs regCount = .wait capAddr) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .notificationWait ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      cases h
      exact ⟨_, hD .notificationWait ‹_›, rfl, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA4.3: what a routed yield pins about the decode — it succeeds, as
`.yield`, with no overflow words. -/
theorem decodeSyscallArgsFromState_of_routedYield
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (h : registerRoutedSyscall layout regs regCount = .yield) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .yield ∧ decoded.overflowCount = 0 := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      exact ⟨_, hD .yield ‹_›, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA4.7: what a routed send pins about the decode — it succeeds, as
`.send`, at `capAddr`, with `msgInfo`, no overflow words and no extra
capabilities; the decoded registers are the mapped layout registers. -/
theorem decodeSyscallArgsFromState_of_routedSend
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall layout regs regCount = .send capAddr msgInfo) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .send ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo = msgInfo ∧ msgInfo.extraCaps = 0 ∧
      decoded.capRecvSlot = SeLe4n.Slot.ofNat 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      cases h
      exact ⟨_, hD .send ‹_ = SyscallId.send.toNat ∧ _›.1, rfl, rfl, rfl, rfl,
        ‹_ = SyscallId.send.toNat ∧ _›.2, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA4.7: what a routed call pins about the decode — it succeeds, as
`.call`, at `capAddr`, with the routed message info, no capabilities and no
overflow words; the decoded registers are the mapped layout registers. -/
theorem decodeSyscallArgsFromState_of_routedCall
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall layout regs regCount = .call capAddr msgInfo) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .call ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo = msgInfo ∧ msgInfo.extraCaps = 0 ∧
      decoded.capRecvSlot = SeLe4n.Slot.ofNat 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      cases h
      exact ⟨_, hD .call ‹_ = SyscallId.call.toNat ∧ _›.1, rfl, rfl, rfl, rfl,
        ‹_ = SyscallId.call.toNat ∧ _›.2, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA4.7: what a routed reply pins about the decode — it succeeds, as
`.reply`, at `capAddr`, with no overflow words, its message info `msgInfo` and
its words the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedReply
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall layout regs regCount = .reply capAddr msgInfo) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .reply ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo = msgInfo ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      cases h
      exact ⟨_, hD .reply ‹_ = SyscallId.reply.toNat›, rfl, rfl, rfl, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA4.7: what a routed receive pins about the decode — it succeeds, as
`.receive`, at `capAddr`, with message length 0 and no overflow words. -/
theorem decodeSyscallArgsFromState_of_routedReceive
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (len : Nat) (replyAddr : CPtr)
    (h : registerRoutedSyscall layout regs regCount = .receive capAddr len replyAddr) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .receive ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo.length = len ∧
      decoded.capRecvSlot = SeLe4n.Slot.ofNat 0 ∧
      (len ≠ 0 → decoded.msgRegs[0]? = some ⟨replyAddr.toNat⟩) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      all_goals
        cases h
        refine ⟨_, hD .receive ‹_›, rfl, rfl, rfl, rfl, rfl, fun hN => ?_⟩
      · simp only [Array.getElem?_map, Array.getElem?_eq_getElem ‹0 < layout.msgRegs.size›,
          Option.map_some, CPtr.ofWord_toNat, ← readReg_val_eq_word]
      · exact absurd (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hN) hLen) ‹¬0 < layout.msgRegs.size›
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA4.7: what a routed reply-receive pins about the decode — it
succeeds, as `.replyRecv`, at `capAddr`, with no overflow words, its message
info `msgInfo` and its words the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedReplyRecv
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall layout regs regCount = .replyRecv capAddr msgInfo) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .replyRecv ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo = msgInfo ∧
      decoded.capRecvSlot = SeLe4n.Slot.ofNat 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      cases h
      exact ⟨_, hD .replyRecv ‹_ = SyscallId.replyRecv.toNat›, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA5.1: what a routed invocation pins about the decode: it succeeds,
as `sid`, a routed invocation, at `capAddr`, with no overflow words, its words
the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedInvoke
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (sid : SyscallId) (capAddr : CPtr)
    (h : registerRoutedSyscall layout regs regCount = .invoke sid capAddr) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = sid ∧ routedInvocation sid = true ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      next sid' hSid =>
        cases h
        obtain ⟨hR, hN⟩ := routedInvocationSid?_some hSid
        exact ⟨_, hD sid hN, rfl, hR, rfl, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA5.13: what a routed declassification or audit call pins about the
decode: it succeeds, as `sid`, one of `routedAudited`, at `capAddr`, with no
overflow words, its words the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedAudited
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (sid : SyscallId) (capAddr : CPtr)
    (h : registerRoutedSyscall layout regs regCount = .audited sid capAddr) :
    ∃ decoded, decodeSyscallArgsFromState st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = sid ∧ routedAudited sid = true ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · next hLen =>
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h)
      next sid' hSid =>
        cases h
        obtain ⟨hR, hN⟩ := routedAuditedSid?_some hSid
        exact ⟨_, hD sid hN, rfl, hR, rfl, rfl, rfl⟩
    · repeat' (first | (cases h; done) | split at h)
  · cases h

/-- WS-ZA ZA5.2, ZA5.5: what a routed one-overflow-word invocation pins about
the decode: as `sid`, one of `routedOverflowOne`, at `capAddr`, with one
overflow word, its words the layout's message registers and then overflow slot
0; it refuses exactly when that slot's read does. -/
theorem decodeSyscallArgsFromState_of_routedOverflowOne
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (sid : SyscallId) (capAddr : CPtr)
    (h : registerRoutedSyscall layout regs regCount = .overflowOne sid capAddr) :
    routedOverflowOne sid = true ∧
    ∃ msgInfo, decodeSyscallArgsFromState st tid layout regs regCount =
      match readOverflowWord st tid 0 with
      | .error e => .error e
      | .ok w => .ok { capAddr, msgInfo, syscallId := sid,
                       msgRegs := layout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)],
                       inlineCount := layout.msgRegs.size, overflowCount := 1 } := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    split at h
    · repeat' (first | (cases h; done) | split at h)
    · next hLen =>
      split at h
      · next hLen1 =>
        split at h
        · next sid' hSid =>
          cases h
          obtain ⟨hR, hN⟩ := routedOverflowOneSid?_some hSid
          refine ⟨hR, mi, ?_⟩
          rw [decodeSyscallArgsFromState_eq_impl]
          unfold decodeSyscallArgsFromStateImpl
          rw [if_pos hB]
          have hId : decodeSyscallId (readReg regs layout.syscallNumReg) = .ok sid := by
            simp only [decodeSyscallId, hN, SyscallId.ofNat_toNat]
          simp only [hC, hM, hId, hLen1, Nat.not_succ_le_self, ↓reduceIte, mergeOverflowWords,
            Array.size_map, Nat.add_sub_cancel_left, List.range_one, List.mapM_cons,
            List.mapM_nil, bind, Except.bind, pure, Except.pure]
          cases readOverflowWord st tid 0 <;> rfl
        · cases h
      · cases h
  · cases h

end SeLe4n.Kernel.Architecture.RegisterDecode
