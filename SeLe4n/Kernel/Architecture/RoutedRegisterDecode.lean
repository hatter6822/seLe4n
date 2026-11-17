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
open SeLe4n.Kernel.Architecture.SyscallArgDecode (truncationMinimum)


/-- What a routed read pins about the decode: it succeeds, as `sid`, at
    `capAddr`, with no overflow words; the decoded registers are the mapped
    layout registers. -/
private theorem decodeSyscallArgsFromState_of_routedInline
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo) (sid : SyscallId)
    (hB : layout.capPtrReg.val < regCount ∧ layout.msgInfoReg.val < regCount ∧
      layout.syscallNumReg.val < regCount ∧ layout.msgRegs.all (·.val < regCount) = true)
    (hC : decodeCapPtr (readReg regs layout.capPtrReg) = .ok capAddr)
    (hM : decodeMsgInfo (readReg regs layout.msgInfoReg) = .ok msgInfo)
    (hLen : msgInfo.length ≤ layout.msgRegs.size)
    (hS : opCode = sid.toNat) :
    decodeSyscallArgsFromState opCode st tid layout regs regCount =
      .ok { capAddr, msgInfo, syscallId := sid,
            msgRegs := layout.msgRegs.map (readReg regs),
            inlineCount := layout.msgRegs.size, overflowCount := 0 } := by
  rw [decodeSyscallArgsFromState_eq_impl]
  unfold decodeSyscallArgsFromStateImpl
  simp only [decodeMsgInfoWord_readReg]
  rw [if_pos hB]
  have hId : decodeSyscallCode opCode = .ok sid := by
    simp only [decodeSyscallCode, hS, SyscallId.ofNat_toNat]
  have hW : CPtr.ofWord (readRegWord regs layout.capPtrReg) = capAddr :=
    Except.ok.inj ((decodeCapPtr_readReg regs layout.capPtrReg).symm.trans hC)
  simp only [hW, hM, hId, hLen, ↓reduceIte]

/-- What a routed read of a syscall that reads no overflow word pins about the
decode, whatever the message length: as `decodeSyscallArgsFromState_of_routed`,
no IPC-buffer word read (`syscallReadsOverflow`). -/
private theorem decodeSyscallArgsFromState_of_routedNoOverflow
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo) (sid : SyscallId)
    (hB : layout.capPtrReg.val < regCount ∧ layout.msgInfoReg.val < regCount ∧
      layout.syscallNumReg.val < regCount ∧ layout.msgRegs.all (·.val < regCount) = true)
    (hC : decodeCapPtr (readReg regs layout.capPtrReg) = .ok capAddr)
    (hM : decodeMsgInfo (readReg regs layout.msgInfoReg) = .ok msgInfo)
    (hNo : syscallReadsOverflow sid = false)
    (hS : opCode = sid.toNat) :
    decodeSyscallArgsFromState opCode st tid layout regs regCount =
      .ok { capAddr, msgInfo, syscallId := sid,
            msgRegs := layout.msgRegs.map (readReg regs),
            inlineCount := layout.msgRegs.size, overflowCount := 0 } := by
  by_cases hLen : msgInfo.length ≤ layout.msgRegs.size
  · exact decodeSyscallArgsFromState_of_routedInline st tid layout regs regCount capAddr msgInfo
      sid hB hC hM hLen hS
  rw [decodeSyscallArgsFromState_eq_impl]
  unfold decodeSyscallArgsFromStateImpl
  simp only [decodeMsgInfoWord_readReg]
  rw [if_pos hB]
  have hId : decodeSyscallCode opCode = .ok sid := by
    simp only [decodeSyscallCode, hS, SyscallId.ofNat_toNat]
  have hW : CPtr.ofWord (readRegWord regs layout.capPtrReg) = capAddr :=
    Except.ok.inj ((decodeCapPtr_readReg regs layout.capPtrReg).symm.trans hC)
  simp only [hW, hM, hId, hLen, ↓reduceIte, mergeOverflowWords, hNo, Bool.false_eq_true,
    Array.size_map, pure, Except.pure]

/-- What a routed read on the short route pins about the decode: the message
fits the inline registers, or the syscall reads no overflow word
(`syscallNumberReadsOverflow`); either way the decode is the inline one. -/
private theorem decodeSyscallArgsFromState_of_routed
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo) (sid : SyscallId)
    (hB : layout.capPtrReg.val < regCount ∧ layout.msgInfoReg.val < regCount ∧
      layout.syscallNumReg.val < regCount ∧ layout.msgRegs.all (·.val < regCount) = true)
    (hC : decodeCapPtr (readReg regs layout.capPtrReg) = .ok capAddr)
    (hM : decodeMsgInfo (readReg regs layout.msgInfoReg) = .ok msgInfo)
    (hLen : msgInfo.length ≤ layout.msgRegs.size ∨
      syscallNumberReadsOverflow opCode = false)
    (hS : opCode = sid.toNat) :
    decodeSyscallArgsFromState opCode st tid layout regs regCount =
      .ok { capAddr, msgInfo, syscallId := sid,
            msgRegs := layout.msgRegs.map (readReg regs),
            inlineCount := layout.msgRegs.size, overflowCount := 0 } := by
  rcases hLen with hLen | hNo
  · exact decodeSyscallArgsFromState_of_routedInline st tid layout regs regCount capAddr msgInfo
      sid hB hC hM hLen hS
  · rw [hS] at hNo
    simp only [syscallNumberReadsOverflow, SyscallId.ofNat_toNat] at hNo
    exact decodeSyscallArgsFromState_of_routedNoOverflow st tid layout regs regCount capAddr
      msgInfo sid hB hC hM hNo hS

theorem decodeSyscallArgsFromState_of_routedSignal
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr)
    (h : registerRoutedSyscall opCode layout regs regCount = .signal capAddr) :
    ∃ decoded, decodeSyscallArgsFromState opCode st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .notificationSignal ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      cases h
      exact ⟨_, hD .notificationSignal ‹_›, rfl, rfl, rfl⟩
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

theorem decodeSyscallArgsFromState_of_routedWait
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr)
    (h : registerRoutedSyscall opCode layout regs regCount = .wait capAddr) :
    ∃ decoded, decodeSyscallArgsFromState opCode st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .notificationWait ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      cases h
      exact ⟨_, hD .notificationWait ‹_›, rfl, rfl, rfl⟩
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- WS-ZA ZA4.3: what a routed yield pins about the decode — it succeeds, as
`.yield`, with no overflow words. -/
theorem decodeSyscallArgsFromState_of_routedYield
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (h : registerRoutedSyscall opCode layout regs regCount = .yield) :
    ∃ decoded, decodeSyscallArgsFromState opCode st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .yield ∧ decoded.overflowCount = 0 := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      exact ⟨_, hD .yield ‹_›, rfl, rfl⟩
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- WS-ZA ZA4.7: what a routed send pins about the decode — it succeeds, as
`.send`, at `capAddr`, with `msgInfo`, no overflow words and no extra
capabilities; the decoded registers are the mapped layout registers. -/
theorem decodeSyscallArgsFromState_of_routedSend
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall opCode layout regs regCount = .send capAddr msgInfo) :
    ∃ decoded, decodeSyscallArgsFromState opCode st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .send ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo = msgInfo ∧ msgInfo.extraCaps = 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      cases h
      exact ⟨_, hD .send ‹_ = SyscallId.send.toNat›, rfl, rfl, rfl, rfl,
        ‹msgInfo.extraCaps = 0›, rfl⟩
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- WS-ZA ZA4.7: what a routed call pins about the decode — it succeeds, as
`.call`, at `capAddr`, with the routed message info, no capabilities and no
overflow words; the decoded registers are the mapped layout registers. -/
theorem decodeSyscallArgsFromState_of_routedCall
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall opCode layout regs regCount = .call capAddr msgInfo) :
    ∃ decoded, decodeSyscallArgsFromState opCode st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .call ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo = msgInfo ∧ msgInfo.extraCaps = 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      cases h
      exact ⟨_, hD .call ‹_ = SyscallId.call.toNat›, rfl, rfl, rfl, rfl,
        ‹msgInfo.extraCaps = 0›, rfl⟩
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- WS-ZA ZA4.7: what a routed reply pins about the decode — it succeeds, as
`.reply`, at `capAddr`, with no overflow words, its message info `msgInfo` and
its words the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedReply
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall opCode layout regs regCount = .reply capAddr msgInfo) :
    ∃ decoded, decodeSyscallArgsFromState opCode st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .reply ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo = msgInfo ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      cases h
      exact ⟨_, hD .reply ‹_ = SyscallId.reply.toNat›, rfl, rfl, rfl, rfl, rfl⟩
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- WS-ZA ZA4.7: what a routed receive pins about the decode — it succeeds, as
`.receive`, at `capAddr`, with message length 0 and no overflow words. -/
theorem decodeSyscallArgsFromState_of_routedReceive
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (len : Nat) (replyAddr : CPtr)
    (h : registerRoutedSyscall opCode layout regs regCount = .receive capAddr len replyAddr) :
    ∃ decoded, decodeSyscallArgsFromState opCode st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .receive ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo.length = len ∧
      (len ≠ 0 → decoded.msgRegs[0]? = some ⟨replyAddr.word⟩) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      cases h
      refine ⟨_, hD .receive ‹_›, rfl, rfl, rfl, rfl, fun _ => ?_⟩
      simp only [Array.getElem?_map, Array.getElem?_eq_getElem ‹0 < layout.msgRegs.size›,
        Option.map_some, readReg_eq_word]
      rfl
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- WS-ZA ZA4.7: what a routed reply-receive pins about the decode — it
succeeds, as `.replyRecv`, at `capAddr`, with no overflow words, its message
info `msgInfo` and its words the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedReplyRecv
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall opCode layout regs regCount = .replyRecv capAddr msgInfo) :
    ∃ decoded, decodeSyscallArgsFromState opCode st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = .replyRecv ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧ decoded.msgInfo = msgInfo ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      cases h
      exact ⟨_, hD .replyRecv ‹_ = SyscallId.replyRecv.toNat›, rfl, rfl, rfl, rfl, rfl⟩
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- WS-ZA ZA5.1: what a routed invocation pins about the decode: it succeeds,
as `sid`, a routed invocation, at `capAddr`, with no overflow words, its words
the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedInvoke
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (sid : SyscallId) (capAddr : CPtr)
    (h : registerRoutedSyscall opCode layout regs regCount = .invoke sid capAddr) :
    ∃ decoded, decodeSyscallArgsFromState opCode st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = sid ∧ routedInvocation sid = true ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) ∧
      truncationMinimum sid ≤ decoded.msgInfo.length := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      next sid' hSid hT =>
        cases h
        obtain ⟨hR, hN⟩ := routedInvocationSid?_some hSid
        exact ⟨_, hD sid hN, rfl, hR, rfl, rfl, rfl, Nat.not_lt.mp hT⟩
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- WS-ZA ZA5.13: what a routed declassification or audit call pins about the
decode: it succeeds, as `sid`, one of `routedAudited`, at `capAddr`, with no
overflow words, its words the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedAudited
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (sid : SyscallId) (capAddr : CPtr)
    (h : registerRoutedSyscall opCode layout regs regCount = .audited sid capAddr) :
    ∃ decoded, decodeSyscallArgsFromState opCode st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = sid ∧ routedAudited sid = true ∧ decoded.capAddr = capAddr ∧
      decoded.overflowCount = 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) ∧
      decodeMsgInfo (readReg regs layout.msgInfoReg) = .ok decoded.msgInfo := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      next sid' hSid =>
        cases h
        obtain ⟨hR, hN⟩ := routedAuditedSid?_some hSid
        exact ⟨_, hD sid hN, rfl, hR, rfl, rfl, rfl, by first | exact hM | rfl⟩
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- WS-ZA ZA5.2, ZA5.5: what a routed one-overflow-word invocation pins about
the decode: as `sid`, one of `routedOverflowOne`, at `capAddr`, with one
overflow word, its words the layout's message registers and then overflow slot
0; when that slot does not read, the message is clamped to the registers
(`clampToInline`). -/
theorem decodeSyscallArgsFromState_of_routedOverflowOne
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (sid : SyscallId) (capAddr : CPtr)
    (h : registerRoutedSyscall opCode layout regs regCount = .overflowOne sid capAddr) :
    routedOverflowOne sid = true ∧
    ∃ msgInfo, msgInfo.length = layout.msgRegs.size + 1 ∧
      decodeSyscallArgsFromState opCode st tid layout regs regCount =
      match readOverflowWord st tid 0 with
      | .error _ => .ok (clampToInline
          { capAddr, msgInfo, syscallId := sid,
            msgRegs := layout.msgRegs.map (readReg regs),
            inlineCount := layout.msgRegs.size, overflowCount := 0 })
      | .ok w => .ok { capAddr, msgInfo, syscallId := sid,
                       msgRegs := layout.msgRegs.map (readReg regs) ++ #[(⟨w⟩ : RegValue)],
                       inlineCount := layout.msgRegs.size, overflowCount := 1 } := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      split at h
      · split at h <;> cases h
      split at h
      · split at h <;> cases h
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · next sid' hSid =>
        split at h
        · next hLen1 =>
          cases h
          obtain ⟨hR, hN⟩ := routedOverflowOneSid?_some hSid
          refine ⟨hR, mi, hLen1, ?_⟩
          rw [decodeSyscallArgsFromState_eq_impl]
          unfold decodeSyscallArgsFromStateImpl
          simp only [decodeMsgInfoWord_readReg]
          rw [if_pos hB]
          have hId : decodeSyscallCode opCode = .ok sid := by
            simp only [decodeSyscallCode, hN, SyscallId.ofNat_toNat]
          simp only [hM, hId, hLen1, Nat.not_succ_le_self, ↓reduceIte, mergeOverflowWords,
            syscallReadsOverflow_of_routedOverflowOne hR,
            Array.size_map, Nat.add_sub_cancel_left, List.range_one, List.mapM_cons,
            List.mapM_nil, bind, Except.bind, pure, Except.pure]
          cases readOverflowWord st tid 0 <;> rfl
        · repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      · repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- **The decode a long frame clamps to** when an overflow slot it names does
not read (`clampToInline`, seL4's `handleInvocation` with no IPC buffer): the
default layout's inline words, as `sid`, at `capAddr`, its message info's
length the four registers'. -/
def clampedFrameDecode (sid : SyscallId) (rf : RegisterFile) (capAddr : CPtr)
    (mi : MessageInfo) : SyscallDecodeResult :=
  { capAddr, msgInfo := { mi with length := 4 }, syscallId := sid,
    msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg rf),
    inlineCount := 4, overflowCount := 0 }

/-- A long frame's merge, an overflow slot of which does not read, is the
clamped decode. -/
theorem mergeOverflowWords_clamped (st : SystemState) (tid : ThreadId) (rf : RegisterFile)
    (sid : SyscallId) (capAddr : CPtr) (mi : MessageInfo)
    (hRd : syscallReadsOverflow sid = true)
    (hE : ∃ e, (List.range (mi.length - 4)).mapM (readOverflowWord st tid) = .error e) :
    mergeOverflowWords st tid
        { capAddr, msgInfo := mi, syscallId := sid,
          msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg rf),
          inlineCount := SeLe4n.arm64DefaultLayout.msgRegs.size, overflowCount := 0 } =
      .ok (clampedFrameDecode sid rf capAddr mi) := by
  obtain ⟨e, hE⟩ := hE
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  unfold mergeOverflowWords
  simp only [hRd, ↓reduceIte, Array.size_map, hSz, hE, pure, Except.pure, clampToInline,
    clampedFrameDecode]

/-- What a routed long send pins about the decode: as `.send`, at `capAddr`,
with the routed message info, which carries no capabilities and runs past the
layout's message registers to at most `maxMessageRegisters` words; the decode
merges the overflow words (`mergeOverflowWords`) onto the mapped layout
registers. -/
theorem decodeSyscallArgsFromState_of_routedSendLong
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall opCode layout regs regCount = .sendLong capAddr msgInfo) :
    layout.msgRegs.size < msgInfo.length ∧ msgInfo.length ≤ maxMessageRegisters ∧
    msgInfo.extraCaps = 0 ∧
    decodeSyscallArgsFromState opCode st tid layout regs regCount =
      mergeOverflowWords st tid
        { capAddr, msgInfo, syscallId := .send,
          msgRegs := layout.msgRegs.map (readReg regs),
          inlineCount := layout.msgRegs.size, overflowCount := 0 } := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      split at h
      · next hS =>
        split at h
        rotate_left
        · cases h
        rename_i hZ
        replace hS := And.intro hS hZ
        cases h
        have hWf : msgInfo.length ≤ maxMessageRegisters := by
          unfold decodeMsgInfo at hM
          split at hM
          · next mi' hD =>
            cases hM
            exact (MessageInfo.decode_wellFormed hD).1
          · cases hM
        refine ⟨by omega, hWf, hS.2, ?_⟩
        rw [decodeSyscallArgsFromState_eq_impl]
        unfold decodeSyscallArgsFromStateImpl
        simp only [decodeMsgInfoWord_readReg]
        rw [if_pos hB]
        have hId : decodeSyscallCode opCode = .ok .send := by
          simp only [decodeSyscallCode, hS.1, SyscallId.ofNat_toNat]
        simp only [hM, hId, hLen, ↓reduceIte]
      · repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- What a routed long call pins about the decode: as `.call`, at `capAddr`,
with the routed message info, which carries no capabilities and runs past the
layout's message registers to at most `maxMessageRegisters` words; the decode
merges the overflow words (`mergeOverflowWords`) onto the mapped layout
registers. -/
theorem decodeSyscallArgsFromState_of_routedCallLong
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall opCode layout regs regCount = .callLong capAddr msgInfo) :
    layout.msgRegs.size < msgInfo.length ∧ msgInfo.length ≤ maxMessageRegisters ∧
    msgInfo.extraCaps = 0 ∧
    decodeSyscallArgsFromState opCode st tid layout regs regCount =
      mergeOverflowWords st tid
        { capAddr, msgInfo, syscallId := .call,
          msgRegs := layout.msgRegs.map (readReg regs),
          inlineCount := layout.msgRegs.size, overflowCount := 0 } := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      split at h
      · split at h <;> cases h
      split at h
      · next hS =>
        split at h
        rotate_left
        · cases h
        rename_i hZ
        replace hS := And.intro hS hZ
        cases h
        have hWf : msgInfo.length ≤ maxMessageRegisters := by
          unfold decodeMsgInfo at hM
          split at hM
          · next mi' hD =>
            cases hM
            exact (MessageInfo.decode_wellFormed hD).1
          · cases hM
        refine ⟨by omega, hWf, hS.2, ?_⟩
        rw [decodeSyscallArgsFromState_eq_impl]
        unfold decodeSyscallArgsFromStateImpl
        simp only [decodeMsgInfoWord_readReg]
        rw [if_pos hB]
        have hId : decodeSyscallCode opCode = .ok .call := by
          simp only [decodeSyscallCode, hS.1, SyscallId.ofNat_toNat]
        simp only [hM, hId, hLen, ↓reduceIte]
      · repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- What a routed long reply pins about the decode: as `.reply`, at `capAddr`,
with the routed message info, which runs past the layout's message registers
to at most `maxMessageRegisters` words; the decode merges the overflow words
(`mergeOverflowWords`) onto the mapped layout registers. -/
theorem decodeSyscallArgsFromState_of_routedReplyLong
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall opCode layout regs regCount = .replyLong capAddr msgInfo) :
    layout.msgRegs.size < msgInfo.length ∧ msgInfo.length ≤ maxMessageRegisters ∧
    decodeSyscallArgsFromState opCode st tid layout regs regCount =
      mergeOverflowWords st tid
        { capAddr, msgInfo, syscallId := .reply,
          msgRegs := layout.msgRegs.map (readReg regs),
          inlineCount := layout.msgRegs.size, overflowCount := 0 } := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      split at h
      · split at h <;> cases h
      split at h
      · split at h <;> cases h
      split at h
      · next hS =>
        cases h
        have hWf : msgInfo.length ≤ maxMessageRegisters := by
          unfold decodeMsgInfo at hM
          split at hM
          · next mi' hD =>
            cases hM
            exact (MessageInfo.decode_wellFormed hD).1
          · cases hM
        refine ⟨by omega, hWf, ?_⟩
        rw [decodeSyscallArgsFromState_eq_impl]
        unfold decodeSyscallArgsFromStateImpl
        simp only [decodeMsgInfoWord_readReg]
        rw [if_pos hB]
        have hId : decodeSyscallCode opCode = .ok .reply := by
          simp only [decodeSyscallCode, hS, SyscallId.ofNat_toNat]
        simp only [hM, hId, hLen, ↓reduceIte]
      · repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- What a routed long reply-receive pins about the decode, as
`decodeSyscallArgsFromState_of_routedReplyLong` for `.replyRecv`. -/
theorem decodeSyscallArgsFromState_of_routedReplyRecvLong
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall opCode layout regs regCount = .replyRecvLong capAddr msgInfo) :
    layout.msgRegs.size < msgInfo.length ∧ msgInfo.length ≤ maxMessageRegisters ∧
    decodeSyscallArgsFromState opCode st tid layout regs regCount =
      mergeOverflowWords st tid
        { capAddr, msgInfo, syscallId := .replyRecv,
          msgRegs := layout.msgRegs.map (readReg regs),
          inlineCount := layout.msgRegs.size, overflowCount := 0 } := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      split at h
      · split at h <;> cases h
      split at h
      · split at h <;> cases h
      split at h
      · cases h
      split at h
      · next hS =>
        cases h
        have hWf : msgInfo.length ≤ maxMessageRegisters := by
          unfold decodeMsgInfo at hM
          split at hM
          · next mi' hD =>
            cases hM
            exact (MessageInfo.decode_wellFormed hD).1
          · cases hM
        refine ⟨by omega, hWf, ?_⟩
        rw [decodeSyscallArgsFromState_eq_impl]
        unfold decodeSyscallArgsFromStateImpl
        simp only [decodeMsgInfoWord_readReg]
        rw [if_pos hB]
        have hId : decodeSyscallCode opCode = .ok .replyRecv := by
          simp only [decodeSyscallCode, hS, SyscallId.ofNat_toNat]
        simp only [hM, hId, hLen, ↓reduceIte]
      · repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- A routed send's message fits the layout's message registers. -/
theorem registerRoutedSyscall_send_length
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall opCode layout regs regCount = .send capAddr msgInfo) :
    msgInfo.length ≤ layout.msgRegs.size := by
  unfold registerRoutedSyscall at h
  split at h
  · unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      cases h
      rcases hLen with hLen | hNo
      · exact hLen
      · simp only [‹opCode = SyscallId.send.toNat›,
          syscallNumberReadsOverflow, SyscallId.ofNat_toNat, syscallReadsOverflow,
          Bool.true_eq_false] at hNo
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- A routed call's message fits the layout's message registers. -/
theorem registerRoutedSyscall_call_length
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall opCode layout regs regCount = .call capAddr msgInfo) :
    msgInfo.length ≤ layout.msgRegs.size := by
  unfold registerRoutedSyscall at h
  split at h
  · unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      cases h
      rcases hLen with hLen | hNo
      · exact hLen
      · simp only [‹opCode = SyscallId.call.toNat›,
          syscallNumberReadsOverflow, SyscallId.ofNat_toNat, syscallReadsOverflow,
          Bool.true_eq_false] at hNo
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- The message info a route carries, if any. -/
private def routeMsgInfo? : RegisterRoutedSyscall → Option MessageInfo
  | .send _ mi | .call _ mi | .reply _ mi | .replyRecv _ mi | .sendLong _ mi
  | .callLong _ mi | .replyLong _ mi | .replyRecvLong _ mi | .transferring _ _ mi => some mi
  | _ => none

private theorem routedShortTail_msgInfo (capAddr : CPtr) (len n : Nat) :
    routeMsgInfo? (routedShortTail capAddr len n) = none := by
  unfold routedShortTail
  split <;> (repeat' split) <;> rfl

private theorem routedLongTail_msgInfo (capAddr : CPtr) (len size n : Nat) :
    routeMsgInfo? (routedLongTail capAddr len size n) = none := by
  unfold routedLongTail
  split <;> (repeat' split) <;> rfl

/-- **A route's message info is the message-info register's decode**: every
route that carries a message info carries the one `decodeMsgInfoWord` reads off
the message-info register, so an arm reads its fields (the extra-capability
count among them) off the route rather than off the register again. -/
theorem registerRoutedSyscall_msgInfo_decode
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    {r : RegisterRoutedSyscall} {capAddr : CPtr} {msgInfo : MessageInfo}
    (h : registerRoutedSyscall opCode layout regs regCount = r)
    (hr : r = .send capAddr msgInfo ∨ r = .call capAddr msgInfo ∨ r = .reply capAddr msgInfo ∨
      r = .replyRecv capAddr msgInfo ∨ r = .sendLong capAddr msgInfo ∨
      r = .callLong capAddr msgInfo ∨ r = .replyLong capAddr msgInfo ∨
      r = .replyRecvLong capAddr msgInfo ∨ ∃ sid, r = .transferring sid capAddr msgInfo) :
    decodeMsgInfoWord (readRegWord regs layout.msgInfoReg) = .ok msgInfo := by
  have hK : routeMsgInfo? r = some msgInfo := by
    rcases hr with h | h | h | h | h | h | h | h | ⟨_, h⟩ <;> rw [h] <;> rfl
  subst h
  unfold registerRoutedSyscall registerRoutedSyscallOf at hK
  split at hK
  · rcases hM : decodeMsgInfoWord (readRegWord regs layout.msgInfoReg) with e | mi <;>
      simp only [hM] at hK
    · cases hK
    · repeat' split at hK
      all_goals first
        | (rw [routedShortTail_msgInfo] at hK; cases hK)
        | (rw [routedLongTail_msgInfo] at hK; cases hK)
        | (cases hK; rfl)
        | cases hK
  · cases hK

/-- What an overflowed route pins about the decode: the syscall is one
`routedOverflowOne` admits, at `capAddr`, and the message info the register
decodes to runs `len` words, past the layout's message registers, to at most
`maxMessageRegisters`; the decode merges the overflow words
(`mergeOverflowWords`) onto the mapped layout registers. -/
theorem decodeSyscallArgsFromState_of_routedOverflowed
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (sid : SyscallId) (capAddr : CPtr) (len : Nat)
    (h : registerRoutedSyscall opCode layout regs regCount = .overflowed sid capAddr len) :
    ∃ msgInfo, decodeMsgInfo (readReg regs layout.msgInfoReg) = .ok msgInfo ∧
    msgInfo.length = len ∧
    layout.msgRegs.size + 1 < msgInfo.length ∧ msgInfo.length ≤ maxMessageRegisters ∧
    routedOverflowOne sid = true ∧
    decodeSyscallArgsFromState opCode st tid layout regs regCount =
      mergeOverflowWords st tid
        { capAddr, msgInfo, syscallId := sid,
          msgRegs := layout.msgRegs.map (readReg regs),
          inlineCount := layout.msgRegs.size, overflowCount := 0 } := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      have hWf : mi.length ≤ maxMessageRegisters := by
        unfold decodeMsgInfo at hM
        split at hM
        · next mi' hD =>
          cases hM
          exact (MessageInfo.decode_wellFormed hD).1
        · cases hM
      have key : ∀ sid', routedOverflowOneSid? opCode = some sid' →
          ¬ mi.length = layout.msgRegs.size + 1 →
          RegisterRoutedSyscall.overflowed sid' (CPtr.ofWord (readRegWord regs layout.capPtrReg))
              mi.length = .overflowed sid capAddr len →
          ∃ msgInfo, (Except.ok mi : Except KernelError MessageInfo) = .ok msgInfo ∧
          msgInfo.length = len ∧
          layout.msgRegs.size + 1 < msgInfo.length ∧ msgInfo.length ≤ maxMessageRegisters ∧
          routedOverflowOne sid = true ∧
          decodeSyscallArgsFromState opCode st tid layout regs regCount =
            mergeOverflowWords st tid
              { capAddr, msgInfo, syscallId := sid,
                msgRegs := layout.msgRegs.map (readReg regs),
                inlineCount := layout.msgRegs.size, overflowCount := 0 } := by
        intro sid' hSid hNe hEq
        cases hEq
        obtain ⟨hR, hN⟩ := routedOverflowOneSid?_some hSid
        refine ⟨mi, rfl, rfl, by omega, hWf, hR, ?_⟩
        rw [decodeSyscallArgsFromState_eq_impl]
        unfold decodeSyscallArgsFromStateImpl
        simp only [decodeMsgInfoWord_readReg]
        rw [if_pos hB]
        have hId : decodeSyscallCode opCode = .ok sid := by
          simp only [decodeSyscallCode, hN, SyscallId.ofNat_toNat]
        simp only [hM, hId, hLen, ↓reduceIte]
      split at h
      · split at h <;> cases h
      split at h
      · split at h <;> cases h
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · next sid' hSid =>
        split at h
        · cases h
        · next hNe => exact key sid' hSid hNe h
      · rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'
  · cases h

/-- What a five-word invocation routed short of its fifth word pins about the
decode: it succeeds, as `sid`, one of `routedOverflowOne`, at `capAddr`, with no
overflow words, its words the layout's message registers. -/
theorem decodeSyscallArgsFromState_of_routedShortArgs
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (sid : SyscallId) (capAddr : CPtr)
    (h : registerRoutedSyscall opCode layout regs regCount = .shortArgs sid capAddr) :
    ∃ decoded, decodeSyscallArgsFromState opCode st tid layout regs regCount = .ok decoded ∧
      decoded.syscallId = sid ∧ (routedInvocation sid || routedOverflowOne sid) = true ∧
      decoded.capAddr = capAddr ∧ decoded.overflowCount = 0 ∧
      decoded.msgRegs = layout.msgRegs.map (readReg regs) ∧
      decoded.msgInfo.length < truncationMinimum sid := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      have hD := fun sid hS =>
        decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ mi sid hB hC hM hLen hS
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      all_goals (rename_i sid' hSid hT; cases h)
      · obtain ⟨hR, hN⟩ := routedInvocationSid?_some hSid
        exact ⟨_, hD sid hN, rfl, by simp [hR], rfl, rfl, rfl, hT⟩
      · obtain ⟨hR, hN⟩ := routedOverflowOneSid?_some hSid
        exact ⟨_, hD sid hN, rfl, by simp [hR], rfl, rfl, rfl, hT⟩
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
  · cases h

/-- A refused route is the decode's refusal. -/
theorem decodeSyscallArgsFromState_of_routedRefused
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (e : KernelError)
    (h : registerRoutedSyscall opCode layout regs regCount = .refused e) :
    decodeSyscallArgsFromState opCode st tid layout regs regCount = .error e := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e' | mi
    · simp only [hM] at h
      cases h
      rw [decodeSyscallArgsFromState_eq_impl]
      unfold decodeSyscallArgsFromStateImpl
      simp only [decodeMsgInfoWord_readReg]
      rw [if_pos hB]
      simp only [hM]
    · simp only [hM] at h
      by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
          syscallNumberReadsOverflow opCode = false <;>
        first | rw [if_pos hLen] at h | rw [if_neg hLen] at h
      all_goals repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      -- the syscall number the decode refuses
      all_goals
        obtain ⟨hE, hN⟩ : e = .invalidSyscallNumber ∧
            SyscallId.ofNat? opCode = none := by
          first
          | (rcases unroutedSyscall_eq h with h' | ⟨h', hN⟩
             · cases h'
             · cases h'; exact ⟨rfl, hN⟩)
          | (cases h; exact ⟨rfl, ‹SyscallId.ofNat? _ = none›⟩)
        subst hE
        rw [decodeSyscallArgsFromState_eq_impl]
        unfold decodeSyscallArgsFromStateImpl
        simp only [decodeMsgInfoWord_readReg]
        rw [if_pos hB]
        simp only [hM, decodeSyscallCode, hN]
  · cases h

/-- The decode of a frame past the layout's message registers naming `sid`,
in bounds: the overflow words merged onto the mapped layout registers. -/
private theorem decodeSyscallArgsFromState_of_routedPast
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (msgInfo : MessageInfo) (sid : SyscallId)
    (hB : layout.capPtrReg.val < regCount ∧ layout.msgInfoReg.val < regCount ∧
      layout.syscallNumReg.val < regCount ∧ layout.msgRegs.all (·.val < regCount) = true)
    (hM : decodeMsgInfo (readReg regs layout.msgInfoReg) = .ok msgInfo)
    (hLen : ¬ msgInfo.length ≤ layout.msgRegs.size)
    (hS : opCode = sid.toNat) :
    decodeSyscallArgsFromState opCode st tid layout regs regCount =
      mergeOverflowWords st tid
        { capAddr := CPtr.ofWord (readRegWord regs layout.capPtrReg), msgInfo, syscallId := sid,
          msgRegs := layout.msgRegs.map (readReg regs),
          inlineCount := layout.msgRegs.size, overflowCount := 0 } := by
  rw [decodeSyscallArgsFromState_eq_impl]
  unfold decodeSyscallArgsFromStateImpl
  simp only [decodeMsgInfoWord_readReg]
  rw [if_pos hB]
  have hId : decodeSyscallCode opCode = .ok sid := by
    simp only [decodeSyscallCode, hS, SyscallId.ofNat_toNat]
  simp only [hM, hId, hLen, ↓reduceIte]

/-- What a routed capability-carrying send or call pins about the decode: it
names a send or a call, its message info asks for capabilities and its length
is bounded; a message within the layout's registers decodes to the mapped
registers, as `sid`, at `capAddr`, and a longer one merges its overflow words
(`mergeOverflowWords`). -/
theorem decodeSyscallArgsFromState_of_routedTransferring
    (st : SystemState) (tid : ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (sid : SyscallId) (capAddr : CPtr) (msgInfo : MessageInfo)
    (h : registerRoutedSyscall opCode layout regs regCount = .transferring sid capAddr msgInfo) :
    (sid = .send ∨ sid = .call) ∧ msgInfo.extraCaps ≠ 0 ∧
    msgInfo.length ≤ maxMessageRegisters ∧
    (msgInfo.length ≤ layout.msgRegs.size →
      decodeSyscallArgsFromState opCode st tid layout regs regCount =
        .ok { capAddr, msgInfo, syscallId := sid,
              msgRegs := layout.msgRegs.map (readReg regs),
              inlineCount := layout.msgRegs.size, overflowCount := 0 }) ∧
    (layout.msgRegs.size < msgInfo.length →
      decodeSyscallArgsFromState opCode st tid layout regs regCount =
        mergeOverflowWords st tid
          { capAddr, msgInfo, syscallId := sid,
            msgRegs := layout.msgRegs.map (readReg regs),
            inlineCount := layout.msgRegs.size, overflowCount := 0 }) := by
  unfold registerRoutedSyscall at h
  split at h
  · next hB =>
    unfold registerRoutedSyscallOf at h
    simp only [routedShortTail_eq, routedLongTail_eq, decodeMsgInfoWord_readReg] at h
    have hC := decodeCapPtr_readReg regs layout.capPtrReg
    rcases hM : decodeMsgInfo (readReg regs layout.msgInfoReg) with e | mi
    · simp only [hM] at h; cases h
    simp only [hM] at h
    have hWf : mi.length ≤ maxMessageRegisters := by
      unfold decodeMsgInfo at hM
      split at hM
      · next mi' hD =>
        cases hM
        exact (MessageInfo.decode_wellFormed hD).1
      · cases hM
    by_cases hLen : mi.length ≤ layout.msgRegs.size ∨
        syscallNumberReadsOverflow opCode = false
    · rw [if_pos hLen] at h
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      all_goals (cases h; exact ⟨by decide, ‹_›, hWf,
        fun _ => decodeSyscallArgsFromState_of_routed st tid layout regs regCount _ _ _ hB hC hM
          hLen ‹_›, fun h' => by
            rcases hLen with hL | hNo
            · omega
            · rw [‹opCode = _›] at hNo
              simp [syscallNumberReadsOverflow, SyscallId.ofNat_toNat, syscallReadsOverflow] at hNo⟩)
    · rw [if_neg hLen] at h
      replace hLen := (not_or.mp hLen).1
      repeat' (first | (cases h; done) | split at h |
        (rcases unroutedSyscall_eq h with h' | ⟨h', -⟩ <;> cases h'; done))
      all_goals (cases h; exact ⟨by decide, ‹_›, hWf, fun h' => absurd h' hLen,
        fun _ => decodeSyscallArgsFromState_of_routedPast st tid layout regs regCount _ _ hB hM
          hLen ‹_›⟩)
  · cases h

/-- **The decode reads the code only for its operation and its overflow read**:
two codes naming operations that read the overflow words alike decode the same
registers to the same record but its operation.  A frame's message (its
capability address, message info and words) is therefore one read whichever
of a send, a call or a reply its code names (`blockedSenderCode`). -/
theorem decodeSyscallArgsFromState_code_swap
    {st : SystemState} {tid : ThreadId} {layout : SyscallRegisterLayout}
    {regs : RegisterFile} {regCount : Nat} {c₁ c₂ : Nat} {d : SyscallDecodeResult}
    {s₂ : SyscallId}
    (h : decodeSyscallArgsFromState c₁ st tid layout regs regCount = .ok d)
    (h₂ : SyscallId.ofNat? c₂ = some s₂)
    (hO : syscallReadsOverflow s₂ = syscallReadsOverflow d.syscallId) :
    decodeSyscallArgsFromState c₂ st tid layout regs regCount = .ok { d with syscallId := s₂ } := by
  rw [decodeSyscallArgsFromState_eq_impl] at h ⊢
  unfold decodeSyscallArgsFromStateImpl at h ⊢
  by_cases hB : layout.capPtrReg.val < regCount ∧ layout.msgInfoReg.val < regCount ∧
      layout.syscallNumReg.val < regCount ∧ layout.msgRegs.all (·.val < regCount) = true
  · rw [if_pos hB] at h ⊢
    cases hM : decodeMsgInfoWord (readRegWord regs layout.msgInfoReg) with
    | error e => simp only [hM] at h; cases h
    | ok mi =>
    simp only [hM] at h ⊢
    unfold decodeSyscallCode at h ⊢
    rw [h₂]
    cases hC : SyscallId.ofNat? c₁ with
    | none => simp only [hC] at h; cases h
    | some s₁ =>
    simp only [hC] at h ⊢
    by_cases hLen : mi.length ≤ layout.msgRegs.size
    · rw [if_pos hLen] at h ⊢
      cases h; rfl
    · rw [if_neg hLen] at h ⊢
      unfold mergeOverflowWords at h ⊢
      dsimp only at h ⊢
      by_cases h1 : syscallReadsOverflow s₁ = true
      · rw [if_pos h1] at h
        have hd : d.syscallId = s₁ := by
          split at h <;> (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
        rw [hd, h1] at hO
        rw [if_pos hO]
        split at h <;>
          (simp only [pure, Except.pure, Except.ok.injEq] at h ⊢; subst h; rfl)
      · rw [if_neg h1] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have h2 : ¬ syscallReadsOverflow s₂ = true := by rw [hO]; exact h1
        rw [if_neg h2]; rfl
  · rw [if_neg hB] at h; cases h

/-- A blocked sender's code names a send or a call, both of which read the
overflow words. -/
theorem blockedSenderCode_names (layout : SyscallRegisterLayout) (regs : RegisterFile) :
    ∃ s, SyscallId.ofNat? (blockedSenderCode layout regs) = some s ∧
      syscallReadsOverflow s = true := by
  unfold blockedSenderCode
  split
  · exact ⟨.call, rfl, rfl⟩
  · exact ⟨.send, rfl, rfl⟩

/-- **A frame decoded as any operation that reads the overflow words decodes
as a blocked sender's** (`blockedSenderCode`), to the same message: a reply's
frame, routed by the operation its capability selected, carries what the
sender-frame reads (`blockedSenderDecode`) take from it. -/
theorem decodeSyscallArgsFromState_blockedSender
    {st : SystemState} {tid : ThreadId} {layout : SyscallRegisterLayout}
    {regs : RegisterFile} {regCount : Nat} {c : Nat} {d : SyscallDecodeResult}
    (h : decodeSyscallArgsFromState c st tid layout regs regCount = .ok d)
    (hO : syscallReadsOverflow d.syscallId = true) :
    ∃ s, decodeSyscallArgsFromState (blockedSenderCode layout regs) st tid layout regs regCount =
      .ok { d with syscallId := s } := by
  obtain ⟨s, hs, hsO⟩ := blockedSenderCode_names layout regs
  exact ⟨s, decodeSyscallArgsFromState_code_swap h hs (by rw [hsO, hO])⟩

end SeLe4n.Kernel.Architecture.RegisterDecode
