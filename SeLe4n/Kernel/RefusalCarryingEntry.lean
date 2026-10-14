-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingEndpoint

/-!
# The checked syscall entry, refusing in the state it was refused in

WS-ZA ZA1.3.  `syscallEntryCheckedR` is `syscallEntryChecked` in the
`RefusalCarrying` form (`syscallEntryCheckedR_eq`): the syscalls whose
arguments all sit in registers and whose checks all precede their first write
are routed on the register file to the dispatches of `RefusalCarryingDispatch`
and `RefusalCarryingEndpoint`; every other call takes
`RefusalCarrying.ofKernel` of the specification.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- `syscallEntryChecked`, refusing in the state it was handed
(`syscallEntryCheckedR_eq`).  A signal, wait, yield, capability-free send or
receive whose arguments all sit in registers is routed on the register file
itself (`registerRoutedSyscall`),
before any decode record exists: the decode writes nothing and such a call
fills no TLB entry (`tlbFillIpcBufferOnCore_zero`), so its dispatch is handed
the entry's own state and refuses in it.  Every other call keeps the
specification's form. -/
@[inline] def syscallEntryCheckedR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout)
    (executingCore : Concurrency.CoreId)
    (regCount : Nat := 32) : RefusalCarrying Unit :=
  fun st =>
    if isInsecureDefaultContext ctx then .error (.policyDenied, st)
    else
    match st.scheduler.currentOnCore executingCore with
    | none => .error (.illegalState, st)
    | some tid =>
      -- `lookupThreadRegisterContext`, read in place: its `.ok (regs, st)` is
      -- two cells this match never needs.
      match st.getObject? tid.toObjId with
      | some (.tcb tcb) =>
        match SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
                layout tcb.registerContext regCount with
        | .signal capAddr badge =>
          dispatchSignalCheckedR ctx capAddr (.ok { badge }) tid executingCore st
        | .wait capAddr =>
          dispatchWaitCheckedR ctx capAddr tid executingCore st
        -- WS-ZA ZA4.3: a yield reads no operand and checks nothing a write
        -- precedes, so a refusal is in the entry's own state.
        | .yield =>
          match yieldOnCoreR st executingCore with
          | .error r => .error r
          | .ok st' => .ok ((), st')
        -- WS-ZA ZA4.7: a send with no capabilities to transfer checks
        -- everything before its first write.
        | .send capAddr msgInfo =>
          dispatchSendCheckedR ctx capAddr
            (SeLe4n.Kernel.Architecture.RegisterDecode.extractMessageRegisters
              (layout.msgRegs.map (readReg tcb.registerContext)) msgInfo)
            tid executingCore st
        -- WS-ZA ZA4.7: a receive, with or without a reply object; one that
        -- blocks checks everything, the reply object included, before its
        -- first write.
        | .receive capAddr len mr0 =>
          dispatchReceiveCheckedR ctx capAddr len mr0 tid executingCore st
        | .viaDecode =>
          RefusalCarrying.ofKernel (syscallEntryChecked ctx layout executingCore regCount) st
      | some _ => .error (.illegalState, st)
      | none => .error (.objectNotFound, st)

theorem syscallEntryCheckedR_eq (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : Concurrency.CoreId)
    (regCount : Nat) :
    syscallEntryCheckedR ctx layout executingCore regCount =
      RefusalCarrying.ofKernel (syscallEntryChecked ctx layout executingCore regCount) := by
  funext st
  simp only [syscallEntryCheckedR]
  split
  · next hCtx => simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, ↓reduceIte]
  · next hCtx =>
    split
    · next hCur => simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur,
        Bool.false_eq_true, ↓reduceIte]
    · next tid hCur =>
      split
      · next tcb hObj =>
        have hRegs : lookupThreadRegisterContext tid st = .ok (tcb.registerContext, st) := by
          simp only [lookupThreadRegisterContext, hObj]
        split
        · next capAddr badge hSigRegs =>
          obtain ⟨decoded, hDec, hSig, hCap, hZero, h0, hBadge⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSignal
              st tid layout tcb.registerContext regCount capAddr badge hSigRegs
          subst hCap
          have hArgs : (.ok { badge } : Except KernelError
                Architecture.SyscallArgDecode.NotificationSignalArgs) =
              Architecture.SyscallArgDecode.decodeNotificationSignalArgs decoded := by
            simp only [Architecture.SyscallArgDecode.decodeNotificationSignalArgs,
              Architecture.SyscallArgDecode.requireMsgReg, h0, ↓reduceDIte, hBadge, bind,
              Except.bind, pure, Except.pure]
          rw [dispatchSignalCheckedR_eq ctx decoded _ tid executingCore hSig hArgs]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next capAddr hWaitRegs =>
          obtain ⟨decoded, hDec, hWait, hCap, hZero⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedWait
              st tid layout tcb.registerContext regCount capAddr hWaitRegs
          subst hCap
          rw [dispatchWaitCheckedR_eq ctx decoded tid executingCore hWait]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next hYieldRegs =>
          obtain ⟨decoded, hDec, hYield, hZero⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedYield
              st tid layout tcb.registerContext regCount hYieldRegs
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero,
            dispatchSyscallChecked, hYield, ne_eq, not_true_eq_false, dispatchYield,
            yieldOnCoreR_eq]
          cases yieldOnCore st executingCore <;> rfl
        · next capAddr msgInfo hSendRegs =>
          obtain ⟨decoded, hDec, hSend, hCap, hZero, hInfo, hX, hSlot, hRegs'⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSend
              st tid layout tcb.registerContext regCount capAddr msgInfo hSendRegs
          subst hCap
          have hCaps : Architecture.SyscallArgDecode.decodeExtraCapAddrs decoded = #[] := by
            simp [Architecture.SyscallArgDecode.decodeExtraCapAddrs, hInfo, hX]; rfl
          rw [dispatchSendCheckedR_eq ctx decoded _ tid executingCore hSend hCaps hSlot
            (by rw [hRegs', hInfo])]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next capAddr len mr0 hRecvRegs =>
          obtain ⟨decoded, hDec, hRecv, hCap, hZero, hLen, hSlot, hMr0⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReceive
              st tid layout tcb.registerContext regCount capAddr len mr0 hRecvRegs
          subst hCap
          rw [dispatchReceiveCheckedR_eq ctx decoded tid executingCore len mr0 hRecv hLen hSlot
            hMr0]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · rfl
      · next o hNot hObj =>
        have hRegs : lookupThreadRegisterContext tid st = .error .illegalState := by
          unfold lookupThreadRegisterContext; rw [hObj]
          cases o <;> first | rfl | exact absurd rfl (hNot _)
        simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs,
          Bool.false_eq_true, ↓reduceIte]
      · next hObj =>
        have hRegs : lookupThreadRegisterContext tid st = .error .objectNotFound := by
          simp only [lookupThreadRegisterContext, hObj]
        simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs,
          Bool.false_eq_true, ↓reduceIte]

end SeLe4n.Kernel
