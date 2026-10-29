-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingEndpoint
import SeLe4n.Kernel.RefusalCarryingReplyRecv
import SeLe4n.Kernel.RefusalCarryingInvocation
import SeLe4n.Kernel.RefusalCarryingDeclassification

/-!
# The checked syscall entry, refusing in the state it was refused in

WS-ZA ZA1.3.  `syscallEntryCheckedR` is `syscallEntryChecked` in the
`RefusalCarrying` form (`syscallEntryCheckedR_eq`): the syscalls whose
arguments all sit in registers and whose checks all precede their first write
are routed on the register file to the dispatches of `RefusalCarryingDispatch`,
`RefusalCarryingEndpoint`, `RefusalCarryingReplyRecv`, `RefusalCarryingInvocation`
and `RefusalCarryingDeclassification`; every other call takes
`RefusalCarrying.ofKernel` of the specification.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- `syscallEntryChecked`, refusing in the state it was handed
(`syscallEntryCheckedR_eq`), on the hardware's register layout
(`arm64DefaultLayout`, 32 registers).  A signal, wait, yield, capability-free send or call,
reply, receive, capability invocation (`routedInvocation`), or declassification or
audit call (`routedAudited`) whose arguments all sit in registers is routed on the
register file
itself (`registerRoutedSyscall`),
before any decode record exists: the decode writes nothing and such a call
fills no TLB entry (`tlbFillIpcBufferOnCore_zero`), so its dispatch is handed
the entry's own state and refuses in it.  Every other call keeps the
specification's form. -/
@[inline] def syscallEntryCheckedR (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
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
                SeLe4n.arm64DefaultLayout tcb.registerContext 32 with
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
          dispatchSendCheckedR ctx capAddr SeLe4n.arm64DefaultLayout tcb.registerContext msgInfo.length
            tid executingCore st
        -- WS-ZA ZA4.7: a call with no capabilities to transfer.
        | .call capAddr msgInfo =>
          dispatchCallCheckedR ctx capAddr SeLe4n.arm64DefaultLayout tcb.registerContext msgInfo.length
            tid executingCore st
        -- WS-ZA ZA4.7: a reply; one whose checks all pass before its first
        -- write writes in place.
        | .reply capAddr msgInfo =>
          dispatchReplyCheckedR ctx capAddr SeLe4n.arm64DefaultLayout tcb.registerContext msgInfo.length
            msgInfo.extraCaps msgInfo.label tid executingCore st
        -- WS-ZA ZA4.7: a receive, with or without a reply object; one that
        -- blocks checks everything, the reply object included, before its
        -- first write.
        | .receive capAddr len replyAddr =>
          dispatchReceiveCheckedR ctx capAddr len replyAddr tid executingCore st
        -- WS-ZA ZA4.7: a reply-receive; one that answers a caller blocked on
        -- this server and then blocks writes in place, after every check.
        | .replyRecv capAddr msgInfo =>
          dispatchReplyRecvCheckedR ctx capAddr SeLe4n.arm64DefaultLayout tcb.registerContext msgInfo.length
            msgInfo.extraCaps msgInfo.label tid executingCore st
        -- WS-ZA ZA5.1: a capability invocation outside IPC, its arguments
        -- read from the caller's registers.
        | .invoke sid capAddr =>
          dispatchInvocationCheckedR ctx sid capAddr tcb.registerContext tid executingCore st
        -- WS-ZA ZA5.2, ZA5.5: a scheduling-context configure or a service
        -- register, its fifth word read from overflow slot 0 of the caller's
        -- IPC buffer.  The decode's walk fills
        -- this core's TLB; when the core already caches the translation the
        -- fill writes nothing (`tlbFillIpcBufferOnCore_of_held`, the check read
        -- in place by `ipcBufferFillHeldOne`) and the
        -- dispatch is handed the entry's own state.  Otherwise the fill is the
        -- one write before the checks, and a refusal hands back the TLB the
        -- entry held, its entries back on the spares
        -- (`tlbUndoFillOnCore_tlbFillIpcBufferOnCore`).
        | .overflowOne sid capAddr =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
            (fun _ => .error (.invalidMessageInfo, st))
            (fun w =>
              if SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid then
                dispatchOverflowOneCheckedR ctx sid capAddr tcb.registerContext w tid executingCore st
              else
                let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
                match dispatchOverflowOneCheckedR ctx sid capAddr tcb.registerContext w tid
                    executingCore
                    (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid 1) with
                | .error (e, stF) =>
                  .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
                | .ok r => .ok r)
        -- WS-ZA ZA5.13: a declassification or an audit call, its arguments
        -- read from the caller's registers; an admitted one writes the audit
        -- ring, the taint words and the return registers in place.
        | .audited sid capAddr =>
          dispatchAuditedCheckedR ctx sid capAddr tcb.registerContext tid executingCore st
        | .viaDecode =>
          RefusalCarrying.ofKernel (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) st
      | some _ => .error (.illegalState, st)
      | none => .error (.objectNotFound, st)

/-- The saved registers the entry routes on are the executing thread's own,
which is what the send and call arms read their message from. -/
theorem frameOf {st : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB}
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb)) :
    ∀ t, st.getTcb? tid = some t → t.registerContext = tcb.registerContext := by
  intro t ht
  have hT : st.getTcb? tid = some tcb := by
    rw [SystemState.getObject?_eq_getElem] at hObj
    simp only [SystemState.getTcb?, hObj]
  rw [hT] at ht
  cases ht
  rfl

theorem syscallEntryCheckedR_eq (ctx : LabelingContext) (executingCore : Concurrency.CoreId) :
    syscallEntryCheckedR ctx executingCore =
      RefusalCarrying.ofKernel
        (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) := by
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
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr badge hSigRegs
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
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr hWaitRegs
          subst hCap
          rw [dispatchWaitCheckedR_eq ctx decoded tid executingCore hWait]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next hYieldRegs =>
          obtain ⟨decoded, hDec, hYield, hZero⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedYield
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 hYieldRegs
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero,
            dispatchSyscallChecked, hYield, ne_eq, not_true_eq_false, dispatchYield,
            yieldOnCoreR_eq]
          cases yieldOnCore st executingCore <;> rfl
        · next capAddr msgInfo hSendRegs =>
          obtain ⟨decoded, hDec, hSend, hCap, hZero, -, -, hSlot, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSend
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hSendRegs
          subst hCap
          rw [dispatchSendCheckedR_eq ctx decoded _ _ _ tid executingCore st hSend hSlot
            (frameOf hObj) hSendRegs]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next capAddr msgInfo hCallRegs =>
          obtain ⟨decoded, hDec, hCall, hCap, hZero, -, -, hSlot, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedCall
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hCallRegs
          subst hCap
          rw [dispatchCallCheckedR_eq ctx decoded _ _ _ tid executingCore st hCall hSlot
            (frameOf hObj) hCallRegs]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next capAddr msgInfo hReplyRegs =>
          obtain ⟨decoded, hDec, hReply, hCap, hZero, hInfo, hRegs'⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReply
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hReplyRegs
          subst hCap hInfo
          rw [dispatchReplyCheckedR_eq ctx decoded tid executingCore SeLe4n.arm64DefaultLayout tcb.registerContext
            hReply hRegs'.symm]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next capAddr len replyAddr hRecvRegs =>
          obtain ⟨decoded, hDec, hRecv, hCap, hZero, hLen, hSlot, hReplyAddr⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReceive
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr len replyAddr hRecvRegs
          subst hCap
          rw [dispatchReceiveCheckedR_eq ctx decoded tid executingCore len replyAddr hRecv hLen hSlot
            hReplyAddr]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next capAddr msgInfo hRRRegs =>
          obtain ⟨decoded, hDec, hRR, hCap, hZero, hInfo, hSlot, hRegs'⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecv
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRRRegs
          subst hCap hInfo
          rw [dispatchReplyRecvCheckedR_eq ctx decoded tid executingCore SeLe4n.arm64DefaultLayout tcb.registerContext
            hRR hRegs'.symm hSlot]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next sid capAddr hInvRegs =>
          obtain ⟨decoded, hDec, hSid, hRouted, hCap, hZero, hRegs'⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedInvoke
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr hInvRegs
          subst hCap hSid
          rw [dispatchInvocationCheckedR_eq ctx decoded tcb.registerContext tid executingCore
            hRouted hRegs']
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next sid capAddr hCfgRegs =>
          obtain ⟨hRouted, msgInfo, hDec⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedOverflowOne
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr hCfgRegs
          rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
          cases hR : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
          | error e =>
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
              SeLe4n.Kernel.Architecture.RegisterDecode.readOverflowWord, hR,
              Bool.false_eq_true, ↓reduceIte]
          | ok w =>
            have hD := dispatchOverflowOneCheckedR_eq ctx
              { capAddr, msgInfo, syscallId := sid,
                msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg tcb.registerContext) ++
                  #[(⟨w.toNat⟩ : RegValue)],
                inlineCount := SeLe4n.arm64DefaultLayout.msgRegs.size, overflowCount := 1 }
              tcb.registerContext w tid executingCore hRouted rfl
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
              SeLe4n.Kernel.Architecture.RegisterDecode.readOverflowWord, hR,
              Bool.false_eq_true, ↓reduceIte]
            split
            · next hHeld =>
              rw [← SeLe4n.Kernel.Architecture.ipcBufferFillHeld_one] at hHeld
              rw [SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_of_held hHeld]
              exact congrFun hD st
            · rw [congrFun hD]
              simp only [RefusalCarrying.ofKernel]
              generalize dispatchSyscallChecked _ _ _ _
                (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid 1) = K
              rcases K with e | r
              · simp only [SeLe4n.Kernel.Architecture.tlbUndoFillOnCore_tlbFillIpcBufferOnCore]
              · rfl
        · next sid capAddr hAudRegs =>
          obtain ⟨decoded, hDec, hSid, hRouted, hCap, hZero, hRegs'⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedAudited
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr hAudRegs
          subst hCap hSid
          rw [dispatchAuditedCheckedR_eq ctx decoded tcb.registerContext tid executingCore
            hRouted hRegs']
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
