-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingEndpoint
import SeLe4n.Kernel.RefusalCarryingOverflowed
import SeLe4n.Kernel.RefusalCarryingReplyRecv
import SeLe4n.Kernel.RefusalCarryingInvocation
import SeLe4n.Kernel.RefusalCarryingDeclassification
import SeLe4n.Kernel.Architecture.RoutedRegisterDecode

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
specification's form.

A specification: the compiled entry runs the continued form
(`syscallEntryCheckedK`, compiled as `syscallEntryRoutedK`), so no code is
generated for it. -/
noncomputable def syscallEntryCheckedR (ctx : LabelingContext)
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
        -- WS-ZA ZA6.35: a send of more than four words.  Its overflow slots,
        -- 928 bytes at most, lie on slot 0's page and at most the next
        -- (`firstPageSlots`), so the decode reads them all exactly when it
        -- reads slot 0 and the first slot of the next page, or slot 0 again
        -- when there is none (`ipcBufferOverflowReadable`); the walk is those
        -- pages' (`tlbFillIpcBufferInOnCore_eq`, the fill read in place), and
        -- the send's arm copies the words in place.
        | .sendLong capAddr msgInfo =>
            SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => .error (.invalidMessageInfo, st))
              (fun _ =>
                SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4))
                  (fun _ => .error (.invalidMessageInfo, st))
                  (fun _ =>
                    if SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid (msgInfo.length - 4) then
                      dispatchSendCheckedR ctx capAddr SeLe4n.arm64DefaultLayout tcb.registerContext
                        msgInfo.length tid executingCore st
                    else
                      let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
                      match dispatchSendCheckedR ctx capAddr SeLe4n.arm64DefaultLayout
                          tcb.registerContext msgInfo.length tid executingCore
                          (SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid
                        (msgInfo.length - 4)) with
                      | .error (e, stF) =>
                        .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
                      | .ok r => .ok r))
        -- A call of more than four words: read and filled as the long send's,
        -- the call's arm copying the words in place.
        | .callLong capAddr msgInfo =>
            SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => .error (.invalidMessageInfo, st))
              (fun _ =>
                SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4))
                  (fun _ => .error (.invalidMessageInfo, st))
                  (fun _ =>
                    if SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid (msgInfo.length - 4) then
                      dispatchCallLongCheckedR ctx capAddr SeLe4n.arm64DefaultLayout tcb.registerContext
                        msgInfo.length tid executingCore st
                    else
                      let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
                      match dispatchCallLongCheckedR ctx capAddr SeLe4n.arm64DefaultLayout
                          tcb.registerContext msgInfo.length tid executingCore
                          (SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid
                        (msgInfo.length - 4)) with
                      | .error (e, stF) =>
                        .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
                      | .ok r => .ok r))
        -- A reply of more than four words: read and filled as the long send's,
        -- the reply's arm copying the words in place.
        | .replyLong capAddr msgInfo =>
            SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => .error (.invalidMessageInfo, st))
              (fun _ =>
                SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4))
                  (fun _ => .error (.invalidMessageInfo, st))
                  (fun _ =>
                    if SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid (msgInfo.length - 4) then
                      dispatchReplyLongCheckedR ctx capAddr tcb.registerContext msgInfo.length
                        msgInfo.extraCaps msgInfo.label tid executingCore st
                    else
                      let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
                      match dispatchReplyLongCheckedR ctx capAddr tcb.registerContext msgInfo.length
                          msgInfo.extraCaps msgInfo.label tid executingCore
                          (SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid
                        (msgInfo.length - 4)) with
                      | .error (e, stF) =>
                        .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
                      | .ok r => .ok r))
        -- A reply-receive of more than four words: read and filled as the
        -- long reply's, the arm copying the words in place.
        | .replyRecvLong capAddr msgInfo =>
            SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => .error (.invalidMessageInfo, st))
              (fun _ =>
                SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4))
                  (fun _ => .error (.invalidMessageInfo, st))
                  (fun _ =>
                    if SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid (msgInfo.length - 4) then
                      dispatchReplyRecvLongCheckedR ctx capAddr tcb.registerContext msgInfo.length
                        msgInfo.extraCaps msgInfo.label tid executingCore st
                    else
                      let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
                      match dispatchReplyRecvLongCheckedR ctx capAddr tcb.registerContext msgInfo.length
                          msgInfo.extraCaps msgInfo.label tid executingCore
                          (SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid
                        (msgInfo.length - 4)) with
                      | .error (e, stF) =>
                        .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
                      | .ok r => .ok r))
        -- A send or call carrying capabilities: the capability operand checked
        -- before the first write; one that blocks writes in place, one that
        -- meets a receiver takes the specification's transfer
        -- (`dispatchTransferringCheckedR_eq`).  Past the inline words, its
        -- overflow slots read and filled as the long send's.
        | .transferring sid capAddr msgInfo =>
          if msgInfo.length ≤ 4 then
            dispatchTransferringCheckedR ctx sid capAddr tcb.registerContext msgInfo.length tid
              executingCore st
          else
            SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => .error (.invalidMessageInfo, st))
              (fun _ =>
                SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4))
                  (fun _ => .error (.invalidMessageInfo, st))
                  (fun _ =>
                    if SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid (msgInfo.length - 4) then
                      dispatchTransferringCheckedR ctx sid capAddr tcb.registerContext
                        msgInfo.length tid executingCore st
                    else
                      let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
                      match dispatchTransferringCheckedR ctx sid capAddr tcb.registerContext
                          msgInfo.length tid executingCore
                          (SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid
                        (msgInfo.length - 4)) with
                      | .error (e, stF) =>
                        .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
                      | .ok r => .ok r))
        -- WS-ZA ZA5.13: a declassification or an audit call, its arguments
        -- read from the caller's registers; an admitted one writes the audit
        -- ring, the taint words and the return registers in place.
        | .audited sid capAddr =>
          dispatchAuditedCheckedR ctx sid capAddr tcb.registerContext tid executingCore st
        -- A call past the inline words whose dispatch reads no word past slot
        -- 0: its overflow slots read and filled as the long send's are, then
        -- the short route's dispatch (`dispatchOverflowedCheckedR_eq`).
        | .overflowed sid capAddr len =>
            SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => .error (.invalidMessageInfo, st))
              (fun w =>
                SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (len - 4))
                  (fun _ => .error (.invalidMessageInfo, st))
                  (fun _ =>
                    if SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid (len - 4) then
                      dispatchOverflowedCheckedR ctx sid capAddr tcb.registerContext len w
                        tid executingCore st
                    else
                      let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
                      match dispatchOverflowedCheckedR ctx sid capAddr tcb.registerContext
                          len w tid executingCore
                          (SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid
                        (len - 4)) with
                      | .error (e, stF) =>
                        .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
                      | .ok r => .ok r))
        -- A five-word invocation of the inline words alone, short of its
        -- fifth argument: refused once its capability is found and checked.
        | .shortArgs sid capAddr => dispatchShortArgsCheckedR sid capAddr tid executingCore st
        -- A message-info word or a syscall number the decode refuses: refused
        -- before any write.
        | .refused e => .error (e, st)
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
          obtain ⟨decoded, hDec, hSend, hCap, hZero, -, -, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSend
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hSendRegs
          subst hCap
          rw [dispatchSendCheckedR_eq ctx decoded _ _ _ tid executingCore st hSend
            (frameOf hObj) (.inl hSendRegs)]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next capAddr msgInfo hCallRegs =>
          obtain ⟨decoded, hDec, hCall, hCap, hZero, -, -, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedCall
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hCallRegs
          subst hCap
          rw [dispatchCallCheckedR_eq ctx decoded _ _ _ tid executingCore st hCall
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
          obtain ⟨decoded, hDec, hRecv, hCap, hZero, hLen, hReplyAddr⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReceive
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr len replyAddr hRecvRegs
          subst hCap
          rw [dispatchReceiveCheckedR_eq ctx decoded tid executingCore len replyAddr hRecv hLen
            hReplyAddr]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next capAddr msgInfo hRRRegs =>
          obtain ⟨decoded, hDec, hRR, hCap, hZero, hInfo, hRegs'⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecv
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRRRegs
          subst hCap hInfo
          rw [dispatchReplyRecvCheckedR_eq ctx decoded tid executingCore SeLe4n.arm64DefaultLayout tcb.registerContext
            hRR hRegs'.symm]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next sid capAddr hInvRegs =>
          obtain ⟨decoded, hDec, hSid, hRouted, hCap, hZero, hRegs'⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedInvoke
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr hInvRegs
          subst hCap hSid
          rw [dispatchInvocationCheckedR_eq ctx decoded tcb.registerContext tid executingCore
            hRouted (.of_eq hRegs' 4)]
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
              tcb.registerContext w tid executingCore hRouted (.of_eq rfl 5)
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
        · next capAddr msgInfo hLongRegs =>
          obtain ⟨hGt, hMax, -, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSendLong
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hLongRegs
          have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
          rw [hSz] at hGt
          have hT : st.getTcb? tid = some tcb := by
            rw [SystemState.getObject?_eq_getElem] at hObj
            simp only [SystemState.getTcb?, hObj]
          have hn0 : 0 < msgInfo.length - 4 := by omega
          have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
            have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
            have h120 : maxMessageRegisters = 120 := rfl
            rw [h116]; rw [h120] at hMax; omega
          rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
          cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
          | error e =>
            have hD := decodeSyscallArgsFromState_of_routedSendLong_error st tid _ capAddr msgInfo
              hLongRegs 0 hn0 e hR0
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte]
          | ok w0 =>
            dsimp only
            rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
            cases hR1 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid
                (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer
                  (msgInfo.length - 4)) with
            | error e =>
              have hD := decodeSyscallArgsFromState_of_routedSendLong_error st tid _ capAddr
                msgInfo hLongRegs _
                (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead_lt hn0) e hR1
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte]
            | ok w1 =>
              have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable
                hT hn ⟨w0, hR0⟩ ⟨w1, hR1⟩
              have hD := decodeSyscallArgsFromState_of_routedSendLong_ok st tid _ capAddr msgInfo
                hLongRegs hRead
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte, longSendDecode_overflowCount,
                SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn_eq st executingCore tid hn0 hn,
                SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore_eq st executingCore tid hn0 hn]
              split
              · next hHeld =>
                rw [SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_of_held hHeld]
                exact dispatchSendCheckedR_eq ctx
                  (longSendDecode st tid tcb.registerContext capAddr msgInfo)
                  tcb.registerContext capAddr msgInfo tid executingCore st rfl (frameOf hObj)
                  (.inr ⟨hLongRegs, hRead⟩)
              · obtain ⟨tl, hTl⟩ := SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb
                  st executingCore tid (msgInfo.length - 4)
                have hAg : ipcBufferReadsAgree (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st
                    executingCore tid (msgInfo.length - 4)) st := by
                  rw [hTl]; exact .of_eq rfl rfl
                have hFrameF : ∀ t, (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st
                    executingCore tid (msgInfo.length - 4)).getTcb? tid = some t →
                    t.registerContext = tcb.registerContext := by
                  rw [hTl]; exact frameOf hObj
                have hDisp := dispatchSendCheckedR_eq ctx
                  (longSendDecode st tid tcb.registerContext capAddr msgInfo) tcb.registerContext
                  capAddr msgInfo tid executingCore
                  (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                    (msgInfo.length - 4)) rfl
                  hFrameF (.inr ⟨hLongRegs, fun j hj => by rw [hAg.ipcBufferReadMr]; exact hRead j hj⟩)
                have hC : (longSendDecode st tid tcb.registerContext capAddr msgInfo).capAddr =
                    capAddr := rfl
                rw [hC] at hDisp
                rw [hDisp]
                simp only [RefusalCarrying.ofKernel]
                generalize dispatchSyscallChecked _ _ _ _
                  (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                    (msgInfo.length - 4)) = K
                rcases K with e | r
                · simp only [SeLe4n.Kernel.Architecture.tlbUndoFillOnCore_tlbFillIpcBufferOnCore]
                · rfl
        · next capAddr msgInfo hCallLongRegs =>
          obtain ⟨hGt, hMax, -, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedCallLong
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hCallLongRegs
          have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
          rw [hSz] at hGt
          have hT : st.getTcb? tid = some tcb := by
            rw [SystemState.getObject?_eq_getElem] at hObj
            simp only [SystemState.getTcb?, hObj]
          have hn0 : 0 < msgInfo.length - 4 := by omega
          have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
            have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
            have h120 : maxMessageRegisters = 120 := rfl
            rw [h116]; rw [h120] at hMax; omega
          rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
          cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
          | error e =>
            have hD := decodeSyscallArgsFromState_of_routedCallLong_error st tid _ capAddr msgInfo
              hCallLongRegs 0 hn0 e hR0
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte]
          | ok w0 =>
            dsimp only
            rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
            cases hR1 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid
                (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer
                  (msgInfo.length - 4)) with
            | error e =>
              have hD := decodeSyscallArgsFromState_of_routedCallLong_error st tid _ capAddr
                msgInfo hCallLongRegs _
                (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead_lt hn0) e hR1
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte]
            | ok w1 =>
              have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable
                hT hn ⟨w0, hR0⟩ ⟨w1, hR1⟩
              have hD := decodeSyscallArgsFromState_of_routedCallLong_ok st tid _ capAddr msgInfo
                hCallLongRegs hRead
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte, longCallDecode_overflowCount,
                SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn_eq st executingCore tid hn0 hn,
                SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore_eq st executingCore tid hn0 hn]
              split
              · next hHeld =>
                rw [SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_of_held hHeld]
                exact dispatchCallLongCheckedR_eq ctx
                  (longCallDecode st tid tcb.registerContext capAddr msgInfo)
                  tcb.registerContext capAddr msgInfo tid executingCore st rfl (frameOf hObj)
                  hCallLongRegs hRead
              · obtain ⟨tl, hTl⟩ := SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb
                  st executingCore tid (msgInfo.length - 4)
                have hAg : ipcBufferReadsAgree (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st
                    executingCore tid (msgInfo.length - 4)) st := by
                  rw [hTl]; exact .of_eq rfl rfl
                have hFrameF : ∀ t, (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st
                    executingCore tid (msgInfo.length - 4)).getTcb? tid = some t →
                    t.registerContext = tcb.registerContext := by
                  rw [hTl]; exact frameOf hObj
                have hDisp := dispatchCallLongCheckedR_eq ctx
                  (longCallDecode st tid tcb.registerContext capAddr msgInfo) tcb.registerContext
                  capAddr msgInfo tid executingCore
                  (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                    (msgInfo.length - 4)) rfl
                  hFrameF hCallLongRegs (fun j hj => by rw [hAg.ipcBufferReadMr]; exact hRead j hj)
                have hC : (longCallDecode st tid tcb.registerContext capAddr msgInfo).capAddr =
                    capAddr := rfl
                rw [hC] at hDisp
                rw [hDisp]
                simp only [RefusalCarrying.ofKernel]
                generalize dispatchSyscallChecked _ _ _ _
                  (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                    (msgInfo.length - 4)) = K
                rcases K with e | r
                · simp only [SeLe4n.Kernel.Architecture.tlbUndoFillOnCore_tlbFillIpcBufferOnCore]
                · rfl
        · next capAddr msgInfo hReplyLongRegs =>
          obtain ⟨hGt, hMax, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyLong
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hReplyLongRegs
          have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
          rw [hSz] at hGt
          have hT : st.getTcb? tid = some tcb := by
            rw [SystemState.getObject?_eq_getElem] at hObj
            simp only [SystemState.getTcb?, hObj]
          have hn0 : 0 < msgInfo.length - 4 := by omega
          have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
            have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
            have h120 : maxMessageRegisters = 120 := rfl
            rw [h116]; rw [h120] at hMax; omega
          rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
          cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
          | error e =>
            have hD := decodeSyscallArgsFromState_of_routedReplyLong_error st tid _ capAddr msgInfo
              .reply (.inl ⟨hReplyLongRegs, rfl⟩) 0 hn0 e hR0
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte]
          | ok w0 =>
            dsimp only
            rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
            cases hR1 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid
                (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer
                  (msgInfo.length - 4)) with
            | error e =>
              have hD := decodeSyscallArgsFromState_of_routedReplyLong_error st tid _ capAddr
                msgInfo .reply (.inl ⟨hReplyLongRegs, rfl⟩) _
                (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead_lt hn0) e hR1
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte]
            | ok w1 =>
              have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable
                hT hn ⟨w0, hR0⟩ ⟨w1, hR1⟩
              have hD := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
                .reply (.inl ⟨hReplyLongRegs, rfl⟩) hRead
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte, longMessageDecode_overflowCount,
                SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn_eq st executingCore tid hn0 hn,
                SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore_eq st executingCore tid hn0 hn]
              split
              · next hHeld =>
                rw [SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_of_held hHeld]
                exact dispatchReplyLongCheckedR_eq ctx
                  (longMessageDecode .reply st tid tcb.registerContext capAddr msgInfo)
                  tcb.registerContext capAddr tid executingCore st rfl hReplyLongRegs rfl hRead
                  (frameOf hObj)
              · obtain ⟨tl, hTl⟩ := SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb
                  st executingCore tid (msgInfo.length - 4)
                have hAg : ipcBufferReadsAgree (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st
                    executingCore tid (msgInfo.length - 4)) st := by
                  rw [hTl]; exact .of_eq rfl rfl
                have hFrameF : ∀ t, (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st
                    executingCore tid (msgInfo.length - 4)).getTcb? tid = some t →
                    t.registerContext = tcb.registerContext := by
                  rw [hTl]; exact frameOf hObj
                have hDisp := dispatchReplyLongCheckedR_eq ctx
                  (longMessageDecode .reply st tid tcb.registerContext capAddr msgInfo)
                  tcb.registerContext capAddr tid executingCore
                  (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                    (msgInfo.length - 4)) rfl hReplyLongRegs
                  (by simp only [longReplyRegs, longMessageDecode, hAg.overflowRegsFrom])
                  (fun j hj => by rw [hAg.ipcBufferReadMr]; exact hRead j hj) hFrameF
                have hC : (longMessageDecode .reply st tid tcb.registerContext capAddr msgInfo).capAddr =
                    capAddr := rfl
                have hMi : (longMessageDecode .reply st tid tcb.registerContext capAddr msgInfo).msgInfo =
                    msgInfo := rfl
                rw [hC, hMi] at hDisp
                rw [hDisp]
                simp only [RefusalCarrying.ofKernel]
                generalize dispatchSyscallChecked _ _ _ _
                  (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                    (msgInfo.length - 4)) = K
                rcases K with e | r
                · simp only [SeLe4n.Kernel.Architecture.tlbUndoFillOnCore_tlbFillIpcBufferOnCore]
                · rfl
        · next capAddr msgInfo hReplyRecvLongRegs =>
          obtain ⟨hGt, hMax, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecvLong
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hReplyRecvLongRegs
          have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
          rw [hSz] at hGt
          have hT : st.getTcb? tid = some tcb := by
            rw [SystemState.getObject?_eq_getElem] at hObj
            simp only [SystemState.getTcb?, hObj]
          have hn0 : 0 < msgInfo.length - 4 := by omega
          have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
            have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
            have h120 : maxMessageRegisters = 120 := rfl
            rw [h116]; rw [h120] at hMax; omega
          rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
          cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
          | error e =>
            have hD := decodeSyscallArgsFromState_of_routedReplyLong_error st tid _ capAddr msgInfo
              .replyRecv (.inr (.inl ⟨hReplyRecvLongRegs, rfl⟩)) 0 hn0 e hR0
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte]
          | ok w0 =>
            dsimp only
            rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
            cases hR1 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid
                (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer
                  (msgInfo.length - 4)) with
            | error e =>
              have hD := decodeSyscallArgsFromState_of_routedReplyLong_error st tid _ capAddr
                msgInfo .replyRecv (.inr (.inl ⟨hReplyRecvLongRegs, rfl⟩)) _
                (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead_lt hn0) e hR1
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte]
            | ok w1 =>
              have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable
                hT hn ⟨w0, hR0⟩ ⟨w1, hR1⟩
              have hD := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
                .replyRecv (.inr (.inl ⟨hReplyRecvLongRegs, rfl⟩)) hRead
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte, longMessageDecode_overflowCount,
                SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn_eq st executingCore tid hn0 hn,
                SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore_eq st executingCore tid hn0 hn]
              split
              · next hHeld =>
                rw [SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_of_held hHeld]
                exact dispatchReplyRecvLongCheckedR_eq ctx
                  (longMessageDecode .replyRecv st tid tcb.registerContext capAddr msgInfo)
                  tcb.registerContext capAddr tid executingCore st rfl hReplyRecvLongRegs rfl hRead
                  (frameOf hObj)
              · obtain ⟨tl, hTl⟩ := SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb
                  st executingCore tid (msgInfo.length - 4)
                have hAg : ipcBufferReadsAgree (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st
                    executingCore tid (msgInfo.length - 4)) st := by
                  rw [hTl]; exact .of_eq rfl rfl
                have hFrameF : ∀ t, (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st
                    executingCore tid (msgInfo.length - 4)).getTcb? tid = some t →
                    t.registerContext = tcb.registerContext := by
                  rw [hTl]; exact frameOf hObj
                have hDisp := dispatchReplyRecvLongCheckedR_eq ctx
                  (longMessageDecode .replyRecv st tid tcb.registerContext capAddr msgInfo)
                  tcb.registerContext capAddr tid executingCore
                  (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                    (msgInfo.length - 4)) rfl hReplyRecvLongRegs
                  (by simp only [longReplyRegs, longMessageDecode, hAg.overflowRegsFrom])
                  (fun j hj => by rw [hAg.ipcBufferReadMr]; exact hRead j hj) hFrameF
                have hC : (longMessageDecode .replyRecv st tid tcb.registerContext capAddr msgInfo).capAddr =
                    capAddr := rfl
                have hMi : (longMessageDecode .replyRecv st tid tcb.registerContext capAddr msgInfo).msgInfo =
                    msgInfo := rfl
                rw [hC, hMi] at hDisp
                rw [hDisp]
                simp only [RefusalCarrying.ofKernel]
                generalize dispatchSyscallChecked _ _ _ _
                  (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                    (msgInfo.length - 4)) = K
                rcases K with e | r
                · simp only [SeLe4n.Kernel.Architecture.tlbUndoFillOnCore_tlbFillIpcBufferOnCore]
                · rfl
        · next sid capAddr msgInfo hTrRegs =>
          obtain ⟨hSC, -, hMax, hShortDec, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedTransferring
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr msgInfo hTrRegs
          have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
          split
          · next hShort =>
            rw [show dispatchTransferringCheckedR ctx sid capAddr tcb.registerContext msgInfo.length
                tid executingCore st = _ from
              dispatchTransferringCheckedR_eq ctx
                { capAddr, msgInfo, syscallId := sid,
                  msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg tcb.registerContext),
                  inlineCount := SeLe4n.arm64DefaultLayout.msgRegs.size, overflowCount := 0 }
                sid tid executingCore st rfl hSC tcb.registerContext capAddr msgInfo
                (frameOf hObj) hTrRegs (fun h => absurd hShort (by omega))]
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs,
              hShortDec (by rw [hSz]; exact hShort), Bool.false_eq_true, ↓reduceIte,
              SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
          · next hLong =>
            have hGt : 4 < msgInfo.length := by omega
            have hRR : (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 =
                  .replyLong capAddr msgInfo ∧ sid = .reply) ∨
                (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 =
                  .replyRecvLong capAddr msgInfo ∧ sid = .replyRecv) ∨
                (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 =
                  .transferring sid capAddr msgInfo ∧ 4 < msgInfo.length) :=
              .inr (.inr ⟨hTrRegs, hGt⟩)
            have hT : st.getTcb? tid = some tcb := by
              rw [SystemState.getObject?_eq_getElem] at hObj
              simp only [SystemState.getTcb?, hObj]
            have hn0 : 0 < msgInfo.length - 4 := by omega
            have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
              have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
              have h120 : maxMessageRegisters = 120 := rfl
              rw [h116]; rw [h120] at hMax; omega
            rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
            cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
            | error e =>
              have hD := decodeSyscallArgsFromState_of_routedReplyLong_error st tid _ capAddr msgInfo
                sid hRR 0 hn0 e hR0
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte]
            | ok w0 =>
              dsimp only
              rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
              cases hR1 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer
                    (msgInfo.length - 4)) with
              | error e =>
                have hD := decodeSyscallArgsFromState_of_routedReplyLong_error st tid _ capAddr
                  msgInfo sid hRR _
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead_lt hn0) e hR1
                simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                  Bool.false_eq_true, ↓reduceIte]
              | ok w1 =>
                have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable
                  hT hn ⟨w0, hR0⟩ ⟨w1, hR1⟩
                have hD := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
                  sid hRR hRead
                simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                  Bool.false_eq_true, ↓reduceIte, longMessageDecode_overflowCount,
                  SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn_eq st executingCore tid hn0 hn,
                  SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore_eq st executingCore tid hn0 hn]
                split
                · next hHeld =>
                  rw [SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_of_held hHeld]
                  exact dispatchTransferringCheckedR_eq ctx
                    (longMessageDecode sid st tid tcb.registerContext capAddr msgInfo)
                    sid tid executingCore st rfl hSC tcb.registerContext capAddr msgInfo
                    (frameOf hObj) hTrRegs (fun _ => hRead)
                · obtain ⟨tl, hTl⟩ :=
                    SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb
                      st executingCore tid (msgInfo.length - 4)
                  have hAg : ipcBufferReadsAgree (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st
                      executingCore tid (msgInfo.length - 4)) st := by
                    rw [hTl]; exact .of_eq rfl rfl
                  have hFrameF : ∀ t, (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st
                      executingCore tid (msgInfo.length - 4)).getTcb? tid = some t →
                      t.registerContext = tcb.registerContext := by
                    rw [hTl]; exact frameOf hObj
                  have hDisp := dispatchTransferringCheckedR_eq ctx
                    (longMessageDecode sid st tid tcb.registerContext capAddr msgInfo)
                    sid tid executingCore
                    (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                      (msgInfo.length - 4)) rfl hSC tcb.registerContext capAddr msgInfo
                    hFrameF hTrRegs
                    (fun _ j hj => by rw [hAg.ipcBufferReadMr]; exact hRead j hj)
                  have hC : (longMessageDecode sid st tid tcb.registerContext capAddr msgInfo).capAddr =
                      capAddr := rfl
                  rw [hC] at hDisp
                  rw [hDisp]
                  simp only [RefusalCarrying.ofKernel]
                  generalize dispatchSyscallChecked _ _ _ _
                    (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                      (msgInfo.length - 4)) = K
                  rcases K with e | r
                  · simp only [SeLe4n.Kernel.Architecture.tlbUndoFillOnCore_tlbFillIpcBufferOnCore]
                  · rfl
        · next sid capAddr hAudRegs =>
          obtain ⟨decoded, hDec, hSid, hRouted, hCap, hZero, hRegs'⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedAudited
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr hAudRegs
          subst hCap hSid
          rw [dispatchAuditedCheckedR_eq ctx decoded tcb.registerContext tid executingCore
            hRouted (.of_eq hRegs' 4)]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next sid capAddr len hOvRegs =>
          obtain ⟨msgInfo, hMI, hLenEq, hGt, hMax, hRt, -⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedOverflowed
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr len hOvRegs
          subst hLenEq
          have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
          rw [hSz] at hGt
          have hT : st.getTcb? tid = some tcb := by
            rw [SystemState.getObject?_eq_getElem] at hObj
            simp only [SystemState.getTcb?, hObj]
          have hn0 : 0 < msgInfo.length - 4 := by omega
          have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
            have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
            have h120 : maxMessageRegisters = 120 := rfl
            rw [h116]; rw [h120] at hMax; omega
          rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
          cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
          | error e =>
            have hD := decodeSyscallArgsFromState_of_routedOverflowed_error st tid _ sid capAddr
              msgInfo hMI hOvRegs 0 hn0 e hR0
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
              Bool.false_eq_true, ↓reduceIte]
          | ok w0 =>
            dsimp only
            rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
            cases hR1 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid
                (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer
                  (msgInfo.length - 4)) with
            | error e =>
              have hD := decodeSyscallArgsFromState_of_routedOverflowed_error st tid _ sid capAddr
                msgInfo hMI hOvRegs _
                (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead_lt hn0) e hR1
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte]
            | ok w1 =>
              have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable
                hT hn ⟨w0, hR0⟩ ⟨w1, hR1⟩
              have hD := decodeSyscallArgsFromState_of_routedOverflowed_ok st tid _ sid capAddr
                msgInfo hMI hOvRegs hRead
              have hW : overflowWordAt st tid 0 = w0 := by rw [overflowWordAt_eq, hR0]
              have hDisp := dispatchOverflowedCheckedR_eq ctx st tid tcb.registerContext sid
                capAddr msgInfo executingCore hRt (by omega)
              simp only [hW] at hDisp
              simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
                Bool.false_eq_true, ↓reduceIte, overflowedDecode_overflowCount,
                SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn_eq st executingCore tid hn0 hn,
                SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore_eq st executingCore tid hn0 hn]
              split
              · next hHeld =>
                rw [SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_of_held hHeld]
                exact hDisp st hCur
              · rw [hDisp _ (by
                  rw [SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_scheduler]; exact hCur)]
                simp only [RefusalCarrying.ofKernel]
                generalize dispatchSyscallChecked _ _ _ _
                  (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                    (msgInfo.length - 4)) = K
                rcases K with e | r
                · simp only [SeLe4n.Kernel.Architecture.tlbUndoFillOnCore_tlbFillIpcBufferOnCore]
                · rfl
        · next sid capAddr hShortRegs =>
          obtain ⟨decoded, hDec, hSid, hRouted, hCap, hZero, hRegs'⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedShortArgs
              st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr hShortRegs
          subst hCap hSid
          rw [dispatchShortArgsCheckedR_eq ctx decoded tcb.registerContext tid executingCore
            hRouted hRegs']
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next e hRefRegs =>
          have hD := SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedRefused
            st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 e hRefRegs
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hD,
            Bool.false_eq_true, ↓reduceIte]
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


-- ============================================================================
-- The entry with its operand's failed resolution told apart
-- ============================================================================

/-- Whether a resolved slot holds no capability user space may hold: an empty
slot, or a capability naming a reserved idle object. -/
@[inline] def capHeldNone (c : Option Capability) : Bool :=
  match c with
  | none => true
  | some cap => SeLe4n.Kernel.capTargetsReservedKernelObject cap

/-- Whether a resolved slot is empty.  Out of line, with the slot borrowed, so
the entry tests the slot's tag without projecting its capability: the arm
alone takes the capability out of the slot, once.  An inlined test would give
the compiled entry two projections of one field ahead of the arm's reuse of
the cell, a shape Lean 4.28's reset-reuse expansion releases twice. -/
@[noinline] def slotEmpty (c : @& Option Capability) : Bool := c.isNone

/-- The arm's result on a resolved slot.  Where the slot holds no capability
user space may hold (`noCap`: an empty slot, or a capability naming a reserved
idle object, `capHeldNone`), the resolution `syscallResolveCap` fails with
`.invalidCapability`, so a refusal with that error is the resolution's, handed
to `onLookup`; any other result is the arm's, handed to `kArm`.  The arm runs
once, on the slot's contents, as `dispatchOperandCheckedR` runs it. -/
@[inline] def noCapRefusal {β : Type} (noCap : Bool)
    (kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) : β :=
  match r with
  | .error (e, s) =>
    if noCap = true ∧ e = .invalidCapability then onLookup e s else kArm (.error (e, s))
  | .ok v => kArm (.ok v)

/-- **`dispatchOperandCheckedR`, continued**: a refusal before the operand's
resolution is handed to `kPre`, the arm's result on a capability the operand
resolved to is handed to `kArm`, and a resolution that fails as
`syscallResolveCap` fails -- the address not resolving, or the slot holding no
capability user space may hold -- is handed to `onLookup` with its error and
the state the refusal carries (`dispatchOperandCheckedK_spec`).  The entry
delivers that failure as a capability fault from the words it already has, the
operand's address and the error, so the lookup runs once. -/
@[inline] def dispatchOperandCheckedK {β : Type} (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (st : SystemState)
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β) : β :=
  if !(st.scheduler.currentOnCore executingCore).isEqSome tid then
    kPre (.error (.illegalState, st))
  else
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    match st.getObject? tcb.cspaceRoot with
    | some (.cnode rootCn) =>
      resolveCapAddressKUnrolled tcb.cspaceRoot capAddr rootCn.depth st
        (fun e => onLookup e st)
        (fun cnode slot =>
          let c := SystemState.lookupSlotCap st { cnode := cnode, slot := slot }
          -- an empty slot is the resolution's refusal, handed on without
          -- running the arm, so no refusal is built as a value
          if slotEmpty c then onLookup .invalidCapability st
          else noCapRefusal (capHeldNone c) kArm onLookup (arm c st))
    | some _ => kPre (.error (.invalidCapability, st))
    | none => kPre (.error (.objectNotFound, st))
  | some _ => kPre (.error (.illegalState, st))
  | none => kPre (.error (.objectNotFound, st))

/-- **What `dispatchOperandCheckedK` hands on.**  Either the refusal before the
resolution, as `dispatchOperandCheckedR` returns it; or, the caller's TCB and
CSpace root found, the arm's result, every refusal of which differs from any
error the resolution raises; or the resolution's failure, its error the one
`dispatchOperandCheckedR` refuses with. -/
theorem dispatchOperandCheckedK_spec {β : Type} (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (st : SystemState)
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β) (rr : AccessRight)
    (hNone : ∀ s, arm none s = .error (.invalidCapability, s)) :
    dispatchOperandCheckedK capAddr tid executingCore arm st kPre kArm onLookup =
        kPre (dispatchOperandCheckedR capAddr tid executingCore arm st) ∨
      ∃ tcb rootCn, st.getObject? tid.toObjId = some (.tcb tcb) ∧
        st.getObject? tcb.cspaceRoot = some (.cnode rootCn) ∧
        ((dispatchOperandCheckedK capAddr tid executingCore arm st kPre kArm onLookup =
            kArm (dispatchOperandCheckedR capAddr tid executingCore arm st) ∧
          ∀ ke s, dispatchOperandCheckedR capAddr tid executingCore arm st = .error (ke, s) →
            ∀ e, syscallResolveCap ⟨tid, tcb.cspaceRoot, capAddr, rootCn.depth, rr⟩ st =
              .error e → e ≠ ke) ∨
         ∃ e s, dispatchOperandCheckedK capAddr tid executingCore arm st kPre kArm onLookup =
            onLookup e s ∧
          dispatchOperandCheckedR capAddr tid executingCore arm st = .error (e, s) ∧
          syscallResolveCap ⟨tid, tcb.cspaceRoot, capAddr, rootCn.depth, rr⟩ st = .error e) := by
  unfold dispatchOperandCheckedK dispatchOperandCheckedR
  by_cases hc : (!(st.scheduler.currentOnCore executingCore).isEqSome tid) = true
  · rw [if_pos hc, if_pos hc]; exact .inl rfl
  rw [if_neg hc, if_neg hc]
  cases hObj : st.getObject? tid.toObjId with
  | none => exact .inl rfl
  | some o =>
  cases o <;> (try dsimp only) <;> try exact .inl rfl
  rename_i tcb
  cases hRoot : st.getObject? tcb.cspaceRoot with
    | none => dsimp only; exact .inl rfl
    | some r =>
    cases r <;> (try dsimp only) <;> try exact .inl rfl
    rename_i rootCn
    · refine .inr ⟨tcb, rootCn, rfl, hRoot, ?_⟩
      simp only [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
      cases hRes : resolveCapAddress tcb.cspaceRoot capAddr rootCn.depth st with
      | error e =>
        exact .inr ⟨e, st, rfl, rfl, by simp only [syscallResolveCap, hRes]⟩
      | ok ref =>
        obtain ⟨cn, sl⟩ := ref
        dsimp only
        cases hC : SystemState.lookupSlotCap st { cnode := cn, slot := sl } with
        | some cap =>
          rw [if_neg (by simp only [slotEmpty, Option.isNone, Bool.false_eq_true,
            not_false_eq_true])]
          unfold noCapRefusal capHeldNone
          rcases hA : arm (some cap) st with ⟨e, s⟩ | v <;> (try dsimp only)
          · by_cases hX : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true ∧
                e = .invalidCapability
            · rw [if_pos hX]
              refine .inr ⟨e, s, rfl, rfl, ?_⟩
              simp only [syscallResolveCap, hRes, hC, hX.1, ↓reduceIte, hX.2]
            · rw [if_neg hX]
              refine .inl ⟨rfl, fun ke s' h e' h' => ?_⟩
              cases h
              by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
              · simp only [syscallResolveCap, hRes, hC, hIdle, ↓reduceIte,
                  Except.error.injEq] at h'
                subst h'
                exact fun h => hX ⟨hIdle, h.symm⟩
              · simp only [syscallResolveCap, hRes, hC, hIdle, Bool.false_eq_true, ↓reduceIte,
                  reduceCtorEq] at h'
          · exact .inl ⟨rfl, fun ke s' h => by cases h⟩
        | none =>
          rw [if_pos (by simp only [slotEmpty, Option.isNone])]
          exact .inr ⟨.invalidCapability, st, rfl, hNone st,
            by simp only [syscallResolveCap, hRes, hC]⟩

/-- A refusal of an operand dispatch run on the state whose TLB the entry
filled for the IPC buffer, its state handed back with the TLB the entry held;
the identity when the translations were already held (`held`) and nothing was
filled. -/
@[inline] def undoFillRefusal (held : Bool) (c : Concurrency.CoreId) (n0 : Nat)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) :
    Except (KernelError × SystemState) (Unit × SystemState) :=
  match r with
  | .error (e, s) =>
    .error (e, if held then s else SeLe4n.Kernel.Architecture.tlbUndoFillOnCore s c n0)
  | .ok v => .ok v

/-- A continuation handed `undoFillRefusal`'s result, with the result's case
asked first: the case a dispatch that commits builds is taken apart where it is
built, so no result is built to be handed on. -/
@[inline] def undoFillRefusalK {β : Type} (held : Bool) (c : Concurrency.CoreId) (n0 : Nat)
    (k : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (r : Except (KernelError × SystemState) (Unit × SystemState)) : β :=
  match r with
  | .error (e, s) =>
    k (.error (e, if held then s else SeLe4n.Kernel.Architecture.tlbUndoFillOnCore s c n0))
  | .ok v => k (.ok v)

theorem undoFillRefusalK_eq {β : Type} (held : Bool) (c : Concurrency.CoreId) (n0 : Nat)
    (k : Except (KernelError × SystemState) (Unit × SystemState) → β) :
    undoFillRefusalK held c n0 k = fun r => k (undoFillRefusal held c n0 r) := by
  funext r
  rcases r with ⟨e, s⟩ | v <;> rfl

/-- **`dispatchOperandCheckedK` on the filled state**: the long routes' operand
dispatch, run on `stF` (the state with this core's TLB holding the IPC
buffer's translations, or the state itself when it held them already), each
refusal's state handed back with the TLB the entry held.  A failed resolution
reaches `onLookup` as the entry found it, so the lookup runs once and no
refusal is decoded again (`dispatchOperandFilledK_spec`). -/
@[inline] def dispatchOperandFilledK {β : Type} (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (held : Bool) (n0 : Nat)
    (stF : SystemState)
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β) : β :=
  dispatchOperandCheckedK capAddr tid executingCore arm stF
    (undoFillRefusalK held executingCore n0 kPre)
    (undoFillRefusalK held executingCore n0 kArm)
    (fun e s => onLookup e
      (if held then s else SeLe4n.Kernel.Architecture.tlbUndoFillOnCore s executingCore n0))

/-- A resolution's failure reads only the object store, so a TLB fill leaves
it alone. -/
theorem syscallResolveCap_error_perCoreTlb (gate : SyscallGate) (st : SystemState)
    (t : Vector TlbState Concurrency.numCores) (e : KernelError) :
    syscallResolveCap gate { st with perCoreTlb := t } = .error e ↔
      syscallResolveCap gate st = .error e := by
  unfold syscallResolveCap
  rw [resolveCapAddress_congr_objects { st with perCoreTlb := t } st rfl gate.capAddr
    gate.capDepth gate.cspaceRoot]
  cases resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st with
  | error e' => exact Iff.rfl
  | ok ref =>
    dsimp only
    have hL : SystemState.lookupSlotCap { st with perCoreTlb := t } ref =
        SystemState.lookupSlotCap st ref := rfl
    rw [hL]
    cases SystemState.lookupSlotCap st ref with
    | none => exact Iff.rfl
    | some cap =>
      dsimp only
      split <;> simp

/-- **What `dispatchOperandFilledK` hands on**, read on the state the entry
holds: either the refusal before the resolution; or, the caller's TCB and
CSpace root found, the arm's result, every refusal of which differs from any
error the resolution raises; or the resolution's failure, its error the one
the dispatch refuses with.  `R` is the long route's dispatch as the
specification runs it: on the filled state, a refusal handing back the TLB. -/
theorem dispatchOperandFilledK_spec {β : Type} (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (arm : Option Capability → RefusalCarrying Unit) (held : Bool) (n0 : Nat)
    (st : SystemState) (t : Vector TlbState Concurrency.numCores) (stF : SystemState)
    (hF : stF = { st with perCoreTlb := t })
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β) (rr : AccessRight)
    (hNone : ∀ s, arm none s = .error (.invalidCapability, s)) :
    let R := undoFillRefusal held executingCore n0
      (dispatchOperandCheckedR capAddr tid executingCore arm stF)
    dispatchOperandFilledK capAddr tid executingCore arm held n0 stF kPre kArm onLookup =
        kPre R ∨
      ∃ tcb rootCn, st.getObject? tid.toObjId = some (.tcb tcb) ∧
        st.getObject? tcb.cspaceRoot = some (.cnode rootCn) ∧
        ((dispatchOperandFilledK capAddr tid executingCore arm held n0 stF kPre kArm onLookup =
            kArm R ∧
          ∀ ke s, R = .error (ke, s) →
            ∀ e, syscallResolveCap ⟨tid, tcb.cspaceRoot, capAddr, rootCn.depth, rr⟩ st =
              .error e → e ≠ ke) ∨
         ∃ e s, dispatchOperandFilledK capAddr tid executingCore arm held n0 stF kPre kArm
            onLookup = onLookup e s ∧ R = .error (e, s) ∧
          syscallResolveCap ⟨tid, tcb.cspaceRoot, capAddr, rootCn.depth, rr⟩ st = .error e) := by
  intro R
  subst hF
  have hGet : ∀ x, ({ st with perCoreTlb := t } : SystemState).getObject? x = st.getObject? x :=
    fun _ => rfl
  unfold dispatchOperandFilledK
  rw [undoFillRefusalK_eq, undoFillRefusalK_eq]
  rcases dispatchOperandCheckedK_spec capAddr tid executingCore arm { st with perCoreTlb := t }
      (fun r => kPre (undoFillRefusal held executingCore n0 r))
      (fun r => kArm (undoFillRefusal held executingCore n0 r))
      (fun e s => onLookup e
        (if held then s else SeLe4n.Kernel.Architecture.tlbUndoFillOnCore s executingCore n0))
      rr hNone with h | ⟨tcb, rootCn, hT, hRoot, h⟩
  · exact .inl h
  refine .inr ⟨tcb, rootCn, (hGet _).symm.trans hT, (hGet _).symm.trans hRoot, ?_⟩
  rcases h with ⟨hK, hNe⟩ | ⟨e, s, hK, hE, hRes⟩
  · refine .inl ⟨hK, fun ke s hR e hRes => ?_⟩
    have hRes' := (syscallResolveCap_error_perCoreTlb _ st t e).mpr hRes
    revert hR
    unfold R undoFillRefusal
    cases hD : dispatchOperandCheckedR capAddr tid executingCore arm { st with perCoreTlb := t } with
    | ok v => cases held <;> simp
    | error p =>
      obtain ⟨ke', s'⟩ := p
      have := hNe ke' s' hD e hRes'
      cases held <;> simp only [Bool.false_eq_true, ↓reduceIte, Except.error.injEq,
        Prod.mk.injEq] <;> rintro ⟨rfl, -⟩ <;> exact this
  · refine .inr ⟨e, _, hK, ?_, (syscallResolveCap_error_perCoreTlb _ st t e).mp hRes⟩
    unfold R undoFillRefusal
    rw [hE]

/-- **A long route's operand dispatch, continued**: this core's TLB filled
with the IPC buffer's translations for `n` overflow slots unless it holds them
(`ipcBufferFillHeldIn`), then `dispatchOperandFilledK`.  The specification's
form is `longOperandSpecR` (`longOperandK_spec`). -/
@[inline] def longOperandK {β : Type} (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (arm : Option Capability → RefusalCarrying Unit)
    (n : Nat) (st : SystemState)
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β) : β :=
  let held := SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid n
  let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
  dispatchOperandFilledK capAddr tid executingCore arm held n0
    (if held then st else SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid n)
    kPre kArm onLookup

/-- The long route's operand dispatch as the specification runs it: on the
filled state, a refusal handing back the TLB the entry held. -/
@[inline] def longOperandSpecR (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (arm : Option Capability → RefusalCarrying Unit)
    (n : Nat) (st : SystemState) : Except (KernelError × SystemState) (Unit × SystemState) :=
  if SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid n then
    dispatchOperandCheckedR capAddr tid executingCore arm st
  else
    let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
    match dispatchOperandCheckedR capAddr tid executingCore arm
        (SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid n) with
    | .error (e, stF) =>
      .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
    | .ok r => .ok r

/-- A filled state is the state with its TLBs replaced. -/
theorem tlbFillIpcBufferInOnCore_eq_setPerCoreTlb (st : SystemState)
    (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId) {n : Nat} (hn0 : 0 < n)
    (hn : n ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots) :
    ∃ t, SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st c tid n =
      { st with perCoreTlb := t } := by
  rw [SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore_eq st c tid hn0 hn]
  exact SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb st c tid n

/-- **What `longOperandK` hands on**: `dispatchOperandFilledK_spec` with `R`
the specification's `longOperandSpecR`. -/
theorem longOperandK_spec {β : Type} (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (arm : Option Capability → RefusalCarrying Unit)
    (n : Nat) (st : SystemState)
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β) (rr : AccessRight)
    (hNone : ∀ s, arm none s = .error (.invalidCapability, s)) (hn0 : 0 < n)
    (hn : n ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots) :
    longOperandK capAddr tid executingCore arm n st kPre kArm onLookup =
        kPre (longOperandSpecR capAddr tid executingCore arm n st) ∨
      ∃ tcb rootCn, st.getObject? tid.toObjId = some (.tcb tcb) ∧
        st.getObject? tcb.cspaceRoot = some (.cnode rootCn) ∧
        ((longOperandK capAddr tid executingCore arm n st kPre kArm onLookup =
            kArm (longOperandSpecR capAddr tid executingCore arm n st) ∧
          ∀ ke s, longOperandSpecR capAddr tid executingCore arm n st = .error (ke, s) →
            ∀ e, syscallResolveCap ⟨tid, tcb.cspaceRoot, capAddr, rootCn.depth, rr⟩ st =
              .error e → e ≠ ke) ∨
         ∃ e s, longOperandK capAddr tid executingCore arm n st kPre kArm onLookup =
            onLookup e s ∧ longOperandSpecR capAddr tid executingCore arm n st = .error (e, s) ∧
          syscallResolveCap ⟨tid, tcb.cspaceRoot, capAddr, rootCn.depth, rr⟩ st = .error e) := by
  have hR : undoFillRefusal (SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid n)
      executingCore (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
      (dispatchOperandCheckedR capAddr tid executingCore arm
        (if SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid n then st
         else SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid n)) =
      longOperandSpecR capAddr tid executingCore arm n st := by
    unfold undoFillRefusal longOperandSpecR
    cases SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid n
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]
      split <;> (rename_i h; exact h.symm)
  obtain ⟨t, hF⟩ : ∃ t, (if SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid n
      then st else SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid n) =
      { st with perCoreTlb := t } := by
    split
    · exact ⟨st.perCoreTlb, rfl⟩
    · exact tlbFillIpcBufferInOnCore_eq_setPerCoreTlb st executingCore tid hn0 hn
  have h := dispatchOperandFilledK_spec capAddr tid executingCore arm
    (SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid n)
    (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length st t _ hF kPre kArm
    onLookup rr hNone
  simp only [hR] at h
  exact h

/-- **The one-overflow-word route's operand arm**: the configure's or the
service register's, with its fifth word `w`; no other syscall is routed here
(`routedOverflowOne`, `dispatchOverflowOneCheckedR_eq_operand`). -/
@[inline] def overflowOneOperandArmR (ctx : LabelingContext) (sid : SyscallId)
    (regs : RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId) :
    Option Capability → RefusalCarrying Unit :=
  match sid with
  | .serviceRegister => serviceRegisterOperandArmR ctx tid regs w
  | _ => configureOperandArmR regs w tid

theorem overflowOneOperandArmR_none (ctx : LabelingContext) (sid : SyscallId)
    (regs : RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId) (s : SystemState) :
    overflowOneOperandArmR ctx sid regs w tid none s = .error (.invalidCapability, s) := by
  unfold overflowOneOperandArmR
  cases sid <;> rfl

theorem dispatchOverflowOneCheckedR_eq_operand (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (regs : RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (h : Architecture.RegisterDecode.routedOverflowOne sid = true) :
    dispatchOverflowOneCheckedR ctx sid capAddr regs w tid executingCore =
      dispatchOperandCheckedR capAddr tid executingCore
        (overflowOneOperandArmR ctx sid regs w tid) := by
  cases sid <;> first | (cases h; done) | rfl

/-- **The one-overflow-word route's operand dispatch, continued**: this core's
TLB filled with the translation of the IPC buffer's first overflow slot unless
it holds it, then `dispatchOperandFilledK` (`overflowOneOperandK_spec`). -/
@[inline] def overflowOneOperandK {β : Type} (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (arm : Option Capability → RefusalCarrying Unit)
    (st : SystemState)
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β) : β :=
  let held := SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid
  let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
  dispatchOperandFilledK capAddr tid executingCore arm held n0
    (if held then st else SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid 1)
    kPre kArm onLookup

/-- The one-overflow-word dispatch as the specification runs it. -/
@[inline] def overflowOneOperandSpecR (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (arm : Option Capability → RefusalCarrying Unit)
    (st : SystemState) : Except (KernelError × SystemState) (Unit × SystemState) :=
  if SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid then
    dispatchOperandCheckedR capAddr tid executingCore arm st
  else
    let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
    match dispatchOperandCheckedR capAddr tid executingCore arm
        (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid 1) with
    | .error (e, stF) =>
      .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
    | .ok r => .ok r

theorem overflowOneOperandK_spec {β : Type} (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (arm : Option Capability → RefusalCarrying Unit)
    (st : SystemState)
    (kPre kArm : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (onLookup : KernelError → SystemState → β) (rr : AccessRight)
    (hNone : ∀ s, arm none s = .error (.invalidCapability, s)) :
    overflowOneOperandK capAddr tid executingCore arm st kPre kArm onLookup =
        kPre (overflowOneOperandSpecR capAddr tid executingCore arm st) ∨
      ∃ tcb rootCn, st.getObject? tid.toObjId = some (.tcb tcb) ∧
        st.getObject? tcb.cspaceRoot = some (.cnode rootCn) ∧
        ((overflowOneOperandK capAddr tid executingCore arm st kPre kArm onLookup =
            kArm (overflowOneOperandSpecR capAddr tid executingCore arm st) ∧
          ∀ ke s, overflowOneOperandSpecR capAddr tid executingCore arm st = .error (ke, s) →
            ∀ e, syscallResolveCap ⟨tid, tcb.cspaceRoot, capAddr, rootCn.depth, rr⟩ st =
              .error e → e ≠ ke) ∨
         ∃ e s, overflowOneOperandK capAddr tid executingCore arm st kPre kArm onLookup =
            onLookup e s ∧ overflowOneOperandSpecR capAddr tid executingCore arm st = .error (e, s) ∧
          syscallResolveCap ⟨tid, tcb.cspaceRoot, capAddr, rootCn.depth, rr⟩ st = .error e) := by
  have hR : undoFillRefusal (SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid)
      executingCore (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
      (dispatchOperandCheckedR capAddr tid executingCore arm
        (if SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid then st
         else SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid 1)) =
      overflowOneOperandSpecR capAddr tid executingCore arm st := by
    unfold undoFillRefusal overflowOneOperandSpecR
    cases SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]
      split <;> (rename_i h; exact h.symm)
  obtain ⟨t, hF⟩ : ∃ t, (if SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid
      then st else SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid 1) =
      { st with perCoreTlb := t } := by
    split
    · exact ⟨st.perCoreTlb, rfl⟩
    · exact SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb st executingCore tid 1
  have h := dispatchOperandFilledK_spec capAddr tid executingCore arm
    (SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid)
    (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length st t _ hF kPre kArm
    onLookup rr hNone
  simp only [hR] at h
  exact h

/-- A function of `ipcBufferReadMrK`'s result is the read with the function
taken into each continuation. -/
theorem ipcBufferReadMrK_comp {α β : Type} (f : α → β) (st : SystemState) (tid : SeLe4n.ThreadId)
    (idx : Nat) (err : SeLe4n.Kernel.Architecture.IpcBufferRead.IpcBufferReadError → α)
    (ok : UInt64 → α) :
    f (SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid idx err ok) =
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid idx (fun e => f (err e))
        (fun w => f (ok w)) := by
  rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq,
    SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
  cases SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid idx <;> rfl

/-- **`syscallEntryCheckedR`, continued, its operand's failed resolution told
apart** (`syscallEntryCheckedK_spec`): each call routed to an operand dispatch
runs `dispatchOperandCheckedK`, which hands a failed resolution to `kLook`
with the syscall, the operand's address and the error, and the arm's result
on a resolved operand to `kRes`; every other result -- a refusal before the
resolution, and every call not routed to an operand dispatch -- is handed to
`kGen` as `syscallEntryCheckedR` returns it.  The routing, the arms and the
resolution are `syscallEntryCheckedR`'s own.

A specification too: compiled, it is the dispatch over the out-of-line arms
(`syscallEntryRoutedK`, through `syscallEntryCheckedK_eq_routed`), so an entry
that inlines it holds one dispatch rather than every arm, and no code is
generated for this form. -/
noncomputable def syscallEntryCheckedK {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β) : β :=
  if isInsecureDefaultContext ctx then kGen (.error (.policyDenied, st))
  else
  match st.scheduler.currentOnCore executingCore with
  | none => kGen (.error (.illegalState, st))
  | some tid =>
    match st.getObject? tid.toObjId with
    | some (.tcb tcb) =>
      match SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
              SeLe4n.arm64DefaultLayout tcb.registerContext 32 with
      | .signal capAddr badge =>
        dispatchOperandCheckedK capAddr tid executingCore
          (signalOperandArmThenTaintR ctx (.ok { badge }) tid executingCore
            (syscallRequiredRight .notificationSignal)) st kGen kRes
          (kLook .notificationSignal capAddr)
      | .wait capAddr =>
        dispatchOperandCheckedK capAddr tid executingCore
          (waitOperandArmThenTaintR ctx tid executingCore (syscallRequiredRight .notificationWait))
          st kGen kRes (kLook .notificationWait capAddr)
      | .yield =>
        kGen (match yieldOnCoreR st executingCore with
          | .error r => .error r
          | .ok st' => .ok ((), st'))
      | .send capAddr msgInfo =>
        dispatchOperandCheckedK capAddr tid executingCore
          (sendOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
            msgInfo.length tid executingCore (syscallRequiredRight .send)) st kGen kRes
          (kLook .send capAddr)
      | .call capAddr msgInfo =>
        dispatchOperandCheckedK capAddr tid executingCore
          (callOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
            msgInfo.length tid executingCore (syscallRequiredRight .call)) st kGen kRes
          (kLook .call capAddr)
      | .reply capAddr msgInfo =>
        dispatchOperandCheckedK capAddr tid executingCore
          (replyOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
            msgInfo.length msgInfo.extraCaps msgInfo.label tid executingCore
            (syscallRequiredRight .reply)) st kGen kRes (kLook .reply capAddr)
      | .receive capAddr len replyAddr =>
        dispatchOperandCheckedK capAddr tid executingCore
          (receiveOperandArmThenTaintR ctx tid len replyAddr executingCore
            (syscallRequiredRight .receive)) st kGen kRes (kLook .receive capAddr)
      | .replyRecv capAddr msgInfo =>
        dispatchOperandCheckedK capAddr tid executingCore
          (replyRecvOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
            msgInfo.length msgInfo.extraCaps msgInfo.label tid executingCore
            (syscallRequiredRight .replyRecv)) st kGen kRes (kLook .replyRecv capAddr)
      | .invoke sid capAddr =>
        dispatchOperandCheckedK capAddr tid executingCore
          (invocationOperandArmR ctx sid capAddr tcb.registerContext tid executingCore) st kGen
          kRes (kLook sid capAddr)
      | .overflowOne sid capAddr =>
        -- the continuations taken into both of the read's, so each is a tail
        -- call the compiled read jumps to (`ipcBufferReadMrK_comp`); the
        -- dispatch's refusals reach `kRes` and `kLook` as the entry found them
        -- (`overflowOneOperandK_spec`).
        SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
            (fun _ => kGen (.error (.invalidMessageInfo, st)))
            (fun w => overflowOneOperandK capAddr tid executingCore
              (overflowOneOperandArmR ctx sid tcb.registerContext w tid) st kGen kRes
              (kLook sid capAddr))
      | .sendLong capAddr msgInfo =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => kGen (.error (.invalidMessageInfo, st)))
              (fun _ =>
                SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4))
                  (fun _ => kGen (.error (.invalidMessageInfo, st)))
                  (fun _ => longOperandK capAddr tid executingCore
                    (sendOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
                      msgInfo.length tid executingCore (syscallRequiredRight .send))
                    (msgInfo.length - 4) st kGen kRes (kLook .send capAddr)))
      | .callLong capAddr msgInfo =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => kGen (.error (.invalidMessageInfo, st)))
              (fun _ =>
                SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4))
                  (fun _ => kGen (.error (.invalidMessageInfo, st)))
                  (fun _ => longOperandK capAddr tid executingCore
                    (callLongOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
                      msgInfo.length tid executingCore (syscallRequiredRight .call))
                    (msgInfo.length - 4) st kGen kRes (kLook .call capAddr)))
      | .replyLong capAddr msgInfo =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => kGen (.error (.invalidMessageInfo, st)))
              (fun _ =>
                SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4))
                  (fun _ => kGen (.error (.invalidMessageInfo, st)))
                  (fun _ => longOperandK capAddr tid executingCore
                    (replyLongOperandArmThenTaintR ctx tcb.registerContext msgInfo.length
                      msgInfo.extraCaps msgInfo.label tid executingCore (syscallRequiredRight .reply))
                    (msgInfo.length - 4) st kGen kRes (kLook .reply capAddr)))
      | .replyRecvLong capAddr msgInfo =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => kGen (.error (.invalidMessageInfo, st)))
              (fun _ =>
                SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4))
                  (fun _ => kGen (.error (.invalidMessageInfo, st)))
                  (fun _ => longOperandK capAddr tid executingCore
                    (replyRecvLongOperandArmThenTaintR ctx tcb.registerContext msgInfo.length
                      msgInfo.extraCaps msgInfo.label tid executingCore
                      (syscallRequiredRight .replyRecv))
                    (msgInfo.length - 4) st kGen kRes (kLook .replyRecv capAddr)))
      | .transferring sid capAddr msgInfo =>
        if msgInfo.length ≤ 4 then
          dispatchOperandCheckedK capAddr tid executingCore
            (transferringOperandArmThenTaintR ctx sid tcb.registerContext msgInfo.length tid
              executingCore (syscallRequiredRight sid))
            st kGen kRes (kLook sid capAddr)
        else
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => kGen (.error (.invalidMessageInfo, st)))
              (fun _ =>
                SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4))
                  (fun _ => kGen (.error (.invalidMessageInfo, st)))
                  (fun _ => longOperandK capAddr tid executingCore
                    (transferringOperandArmThenTaintR ctx sid tcb.registerContext
                      msgInfo.length tid executingCore (syscallRequiredRight sid))
                    (msgInfo.length - 4) st kGen kRes (kLook sid capAddr)))
      | .audited sid capAddr =>
        dispatchOperandCheckedK capAddr tid executingCore
          (auditedOperandArmR ctx sid tcb.registerContext capAddr tid executingCore) st kGen kRes
          (kLook sid capAddr)
      | .overflowed sid capAddr len =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
              (fun _ => kGen (.error (.invalidMessageInfo, st)))
              (fun w =>
                SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
                  (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (len - 4))
                  (fun _ => kGen (.error (.invalidMessageInfo, st)))
                  (fun _ => kGen (
                    if SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid (len - 4) then
                      dispatchOverflowedCheckedR ctx sid capAddr tcb.registerContext len w
                        tid executingCore st
                    else
                      let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
                      match dispatchOverflowedCheckedR ctx sid capAddr tcb.registerContext
                          len w tid executingCore
                          (SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid
                        (len - 4)) with
                      | .error (e, stF) =>
                        .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
                      | .ok r => .ok r)))
      | .shortArgs sid capAddr =>
        dispatchOperandCheckedK capAddr tid executingCore (shortArgsOperandArmR sid) st kGen kRes
          (kLook sid capAddr)
      | .refused e => kGen (.error (e, st))
      | .viaDecode =>
        kGen (RefusalCarrying.ofKernel
          (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) st)
    | some _ => kGen (.error (.illegalState, st))
    | none => kGen (.error (.objectNotFound, st))

/-- The decode facts a capability fault reads: the caller current, its TCB, its
saved frame's decode and its CSpace root, and what the continued entry handed
on -- the arm's result, every refusal of which differs from any error the
operand's resolution raises, or the resolution's failure, refused alike. -/
def EntryOperandOutcome {β : Type} (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (st : SystemState) (kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β) (result : β) : Prop :=
  ∃ tid tcb decoded rootCn,
    st.scheduler.currentOnCore executingCore = some tid ∧
    st.getObject? tid.toObjId = some (.tcb tcb) ∧
    SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded ∧
    st.getObject? tcb.cspaceRoot = some (.cnode rootCn) ∧
    ((result = kRes (syscallEntryCheckedR ctx executingCore st) ∧
      ∀ ke s, syscallEntryCheckedR ctx executingCore st = .error (ke, s) → ∀ e,
        syscallResolveCap ⟨tid, tcb.cspaceRoot, decoded.capAddr, rootCn.depth,
          syscallRequiredRight decoded.syscallId⟩ st = .error e → e ≠ ke) ∨
     ∃ e s, result = kLook decoded.syscallId decoded.capAddr e s ∧
      syscallEntryCheckedR ctx executingCore st = .error (e, s) ∧
      syscallResolveCap ⟨tid, tcb.cspaceRoot, decoded.capAddr, rootCn.depth, syscallRequiredRight decoded.syscallId⟩ st = .error e)

/-- One routed operand dispatch's share of `syscallEntryCheckedK_spec`. -/
theorem entryOperandOutcome_of_dispatch {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (decoded : SyscallDecodeResult) (sid : SyscallId)
    (arm : Option Capability → RefusalCarrying Unit)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded)
    (hSid : decoded.syscallId = sid)
    (hR : syscallEntryCheckedR ctx executingCore st =
      dispatchOperandCheckedR decoded.capAddr tid executingCore arm st)
    (hNone : ∀ s, arm none s = .error (.invalidCapability, s)) :
    dispatchOperandCheckedK decoded.capAddr tid executingCore arm st kGen kRes
        (kLook sid decoded.capAddr) = kGen (syscallEntryCheckedR ctx executingCore st) ∨
      EntryOperandOutcome ctx executingCore st kRes kLook
        (dispatchOperandCheckedK decoded.capAddr tid executingCore arm st kGen kRes
          (kLook sid decoded.capAddr)) := by
  rw [hR]
  subst hSid
  rcases dispatchOperandCheckedK_spec decoded.capAddr tid executingCore arm st kGen kRes
      (kLook decoded.syscallId decoded.capAddr) (syscallRequiredRight decoded.syscallId) hNone with
    h | ⟨tcb', rootCn, hObj', hRoot, h⟩
  · exact .inl h
  · rw [hObj] at hObj'
    cases hObj'
    exact .inr ⟨tid, tcb, decoded, rootCn, hCur, hObj, hDec, hRoot, by rw [hR]; exact h⟩

/-- One long route's operand dispatch's share of `syscallEntryCheckedK_spec`. -/
theorem entryOperandOutcome_of_long {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (decoded : SyscallDecodeResult) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (arm : Option Capability → RefusalCarrying Unit) (n : Nat)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded)
    (hSid : decoded.syscallId = sid) (hCap : decoded.capAddr = capAddr)
    (hR : syscallEntryCheckedR ctx executingCore st =
      longOperandSpecR capAddr tid executingCore arm n st)
    (hNone : ∀ s, arm none s = .error (.invalidCapability, s)) (hn0 : 0 < n)
    (hn : n ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots) :
    longOperandK capAddr tid executingCore arm n st kGen kRes (kLook sid capAddr) =
        kGen (syscallEntryCheckedR ctx executingCore st) ∨
      EntryOperandOutcome ctx executingCore st kRes kLook
        (longOperandK capAddr tid executingCore arm n st kGen kRes (kLook sid capAddr)) := by
  rw [hR]
  subst hSid hCap
  rcases longOperandK_spec decoded.capAddr tid executingCore arm n st kGen kRes
      (kLook decoded.syscallId decoded.capAddr) (syscallRequiredRight decoded.syscallId) hNone
      hn0 hn with h | ⟨tcb', rootCn, hObj', hRoot, h⟩
  · exact .inl h
  · rw [hObj] at hObj'
    cases hObj'
    exact .inr ⟨tid, tcb, decoded, rootCn, hCur, hObj, hDec, hRoot, by rw [hR]; exact h⟩

/-- The one-overflow-word route's operand dispatch's share of
`syscallEntryCheckedK_spec`. -/
theorem entryOperandOutcome_of_overflowOne {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (decoded : SyscallDecodeResult) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (arm : Option Capability → RefusalCarrying Unit)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hObj : st.getObject? tid.toObjId = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded)
    (hSid : decoded.syscallId = sid) (hCap : decoded.capAddr = capAddr)
    (hR : syscallEntryCheckedR ctx executingCore st =
      overflowOneOperandSpecR capAddr tid executingCore arm st)
    (hNone : ∀ s, arm none s = .error (.invalidCapability, s)) :
    overflowOneOperandK capAddr tid executingCore arm st kGen kRes (kLook sid capAddr) =
        kGen (syscallEntryCheckedR ctx executingCore st) ∨
      EntryOperandOutcome ctx executingCore st kRes kLook
        (overflowOneOperandK capAddr tid executingCore arm st kGen kRes (kLook sid capAddr)) := by
  rw [hR]
  subst hSid hCap
  rcases overflowOneOperandK_spec decoded.capAddr tid executingCore arm st kGen kRes
      (kLook decoded.syscallId decoded.capAddr) (syscallRequiredRight decoded.syscallId)
      hNone with h | ⟨tcb', rootCn, hObj', hRoot, h⟩
  · exact .inl h
  · rw [hObj] at hObj'
    cases hObj'
    exact .inr ⟨tid, tcb, decoded, rootCn, hCur, hObj, hDec, hRoot, by rw [hR]; exact h⟩

/-- **What `syscallEntryCheckedK` hands on**: `syscallEntryCheckedR`'s result to
`kGen`, or, on a call routed to an operand dispatch whose caller's TCB, decode
and CSpace root were found, the outcome `EntryOperandOutcome` names. -/
theorem syscallEntryCheckedK_spec {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β) :
    syscallEntryCheckedK ctx executingCore st kGen kRes kLook =
        kGen (syscallEntryCheckedR ctx executingCore st) ∨
      EntryOperandOutcome ctx executingCore st kRes kLook
        (syscallEntryCheckedK ctx executingCore st kGen kRes kLook) := by
  by_cases hCtx : isInsecureDefaultContext ctx = true
  · exact .inl (by simp only [syscallEntryCheckedK, syscallEntryCheckedR, hCtx, ↓reduceIte])
  cases hCur : st.scheduler.currentOnCore executingCore with
  | none =>
    exact .inl (by simp only [syscallEntryCheckedK, syscallEntryCheckedR, hCtx, hCur,
      Bool.false_eq_true, ↓reduceIte])
  | some tid =>
  cases hObj : st.getObject? tid.toObjId with
  | none =>
    exact .inl (by simp only [syscallEntryCheckedK, syscallEntryCheckedR, hCtx, hCur, hObj,
      Bool.false_eq_true, ↓reduceIte])
  | some o =>
  cases o <;> try (refine .inl ?_; simp only [syscallEntryCheckedK, syscallEntryCheckedR, hCtx,
    hCur, hObj, Bool.false_eq_true, ↓reduceIte]; done)
  rename_i tcb
  · have hD := entryOperandOutcome_of_dispatch ctx executingCore st kGen kRes kLook tid tcb
    cases hRt : SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
        SeLe4n.arm64DefaultLayout tcb.registerContext 32 with
    | signal capAddr badge =>
      obtain ⟨decoded, hDec, hSid, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSignal
          st tid _ _ 32 capAddr badge hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl) (by intro _; rfl)
    | wait capAddr =>
      obtain ⟨decoded, hDec, hSid, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedWait
          st tid _ _ 32 capAddr hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl) (by intro _; rfl)
    | send capAddr msgInfo =>
      obtain ⟨decoded, hDec, hSid, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSend
          st tid _ _ 32 capAddr msgInfo hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl) (by intro _; rfl)
    | call capAddr msgInfo =>
      obtain ⟨decoded, hDec, hSid, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedCall
          st tid _ _ 32 capAddr msgInfo hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl) (by intro _; rfl)
    | reply capAddr msgInfo =>
      obtain ⟨decoded, hDec, hSid, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReply
          st tid _ _ 32 capAddr msgInfo hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl) (by intro _; rfl)
    | receive capAddr len replyAddr =>
      obtain ⟨decoded, hDec, hSid, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReceive
          st tid _ _ 32 capAddr len replyAddr hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl) (by intro _; rfl)
    | replyRecv capAddr msgInfo =>
      obtain ⟨decoded, hDec, hSid, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecv
          st tid _ _ 32 capAddr msgInfo hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl) (by intro _; rfl)
    | invoke sid capAddr =>
      obtain ⟨decoded, hDec, hSid, -, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedInvoke
          st tid _ _ 32 sid capAddr hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl) (by intro _; rfl)
    | audited sid capAddr =>
      obtain ⟨decoded, hDec, hSid, hRA, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedAudited
          st tid _ _ 32 sid capAddr hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl) (by
          intro _
          revert hRA
          cases sid <;> intro hRA <;> first | rfl | exact absurd hRA (by decide))
    | overflowOne sid capAddr =>
      obtain ⟨hRouted, msgInfo, hDecM⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedOverflowOne
          st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 sid capAddr hRt
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
      cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
      | error e =>
        exact .inl (by simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
          Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0])
      | ok w =>
        dsimp only
        have hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout
            tcb.registerContext 32 = .ok
              { capAddr, msgInfo, syscallId := sid,
                msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg tcb.registerContext) ++
                  #[(⟨w.toNat⟩ : RegValue)],
                inlineCount := SeLe4n.arm64DefaultLayout.msgRegs.size, overflowCount := 1 } := by
          rw [hDecM]
          simp only [SeLe4n.Kernel.Architecture.RegisterDecode.readOverflowWord, hR0]
        exact entryOperandOutcome_of_overflowOne ctx executingCore st kGen kRes kLook tid tcb _ sid
          capAddr (overflowOneOperandArmR ctx sid tcb.registerContext w tid) hCur hObj hDec rfl rfl
          (by
            simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true,
              ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0,
              dispatchOverflowOneCheckedR_eq_operand ctx sid capAddr _ w tid _ hRouted]
            rfl)
          (overflowOneOperandArmR_none ctx sid tcb.registerContext w tid)
    | sendLong capAddr msgInfo =>
      obtain ⟨hGt, hMax, -, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSendLong
          st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRt
      have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      rw [hSz] at hGt
      have hT : st.getTcb? tid = some tcb := by
        rw [SystemState.getObject?_eq_getElem] at hObj
        simp only [SystemState.getTcb?, hObj]
      have hn0 : 0 < msgInfo.length - 4 := by omega
      have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
        have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
        have h120 : maxMessageRegisters = 120 := rfl
        rw [h116]; rw [h120] at hMax; omega
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
      cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
      | error e =>
        exact .inl (by simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
          Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0])
      | ok w0 =>
        dsimp only
        rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
        cases hR1 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid
            (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4)) with
        | error e =>
          exact .inl (by simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
            Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0, hR1])
        | ok w1 =>
          dsimp only
          have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable hT hn ⟨w0, hR0⟩ ⟨w1, hR1⟩
          have hDec := decodeSyscallArgsFromState_of_routedSendLong_ok st tid _ capAddr msgInfo hRt hRead
          exact entryOperandOutcome_of_long ctx executingCore st kGen kRes kLook tid tcb
            (longSendDecode st tid tcb.registerContext capAddr msgInfo) .send capAddr
            (sendOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
              msgInfo.length tid executingCore (syscallRequiredRight .send))
            (msgInfo.length - 4) hCur hObj hDec rfl rfl (by
              simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true,
                ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0, hR1]
              rfl) (by intro _; rfl) hn0 hn
    | callLong capAddr msgInfo =>
      obtain ⟨hGt, hMax, -, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedCallLong
          st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRt
      have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      rw [hSz] at hGt
      have hT : st.getTcb? tid = some tcb := by
        rw [SystemState.getObject?_eq_getElem] at hObj
        simp only [SystemState.getTcb?, hObj]
      have hn0 : 0 < msgInfo.length - 4 := by omega
      have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
        have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
        have h120 : maxMessageRegisters = 120 := rfl
        rw [h116]; rw [h120] at hMax; omega
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
      cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
      | error e =>
        exact .inl (by simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
          Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0])
      | ok w0 =>
        dsimp only
        rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
        cases hR1 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid
            (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4)) with
        | error e =>
          exact .inl (by simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
            Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0, hR1])
        | ok w1 =>
          dsimp only
          have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable hT hn ⟨w0, hR0⟩ ⟨w1, hR1⟩
          have hDec := decodeSyscallArgsFromState_of_routedCallLong_ok st tid _ capAddr msgInfo hRt hRead
          exact entryOperandOutcome_of_long ctx executingCore st kGen kRes kLook tid tcb
            (longCallDecode st tid tcb.registerContext capAddr msgInfo) .call capAddr
            (callLongOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
              msgInfo.length tid executingCore (syscallRequiredRight .call))
            (msgInfo.length - 4) hCur hObj hDec rfl rfl (by
              simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true,
                ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0, hR1]
              rfl) (by intro _; rfl) hn0 hn
    | replyLong capAddr msgInfo =>
      obtain ⟨hGt, hMax, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyLong
          st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRt
      have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      rw [hSz] at hGt
      have hT : st.getTcb? tid = some tcb := by
        rw [SystemState.getObject?_eq_getElem] at hObj
        simp only [SystemState.getTcb?, hObj]
      have hn0 : 0 < msgInfo.length - 4 := by omega
      have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
        have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
        have h120 : maxMessageRegisters = 120 := rfl
        rw [h116]; rw [h120] at hMax; omega
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
      cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
      | error e =>
        exact .inl (by simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
          Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0])
      | ok w0 =>
        dsimp only
        rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
        cases hR1 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid
            (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4)) with
        | error e =>
          exact .inl (by simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
            Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0, hR1])
        | ok w1 =>
          dsimp only
          have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable hT hn ⟨w0, hR0⟩ ⟨w1, hR1⟩
          have hDec := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
            .reply (.inl ⟨hRt, rfl⟩) hRead
          exact entryOperandOutcome_of_long ctx executingCore st kGen kRes kLook tid tcb
            (longMessageDecode .reply st tid tcb.registerContext capAddr msgInfo) .reply capAddr
            (replyLongOperandArmThenTaintR ctx tcb.registerContext msgInfo.length
              msgInfo.extraCaps msgInfo.label tid executingCore (syscallRequiredRight .reply))
            (msgInfo.length - 4) hCur hObj hDec rfl rfl (by
              simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true,
                ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0, hR1]
              rfl) (by intro _; rfl) hn0 hn
    | replyRecvLong capAddr msgInfo =>
      obtain ⟨hGt, hMax, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecvLong
          st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 capAddr msgInfo hRt
      have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      rw [hSz] at hGt
      have hT : st.getTcb? tid = some tcb := by
        rw [SystemState.getObject?_eq_getElem] at hObj
        simp only [SystemState.getTcb?, hObj]
      have hn0 : 0 < msgInfo.length - 4 := by omega
      have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
        have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
        have h120 : maxMessageRegisters = 120 := rfl
        rw [h116]; rw [h120] at hMax; omega
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
      cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
      | error e =>
        exact .inl (by simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
          Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0])
      | ok w0 =>
        dsimp only
        rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
        cases hR1 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid
            (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4)) with
        | error e =>
          exact .inl (by simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
            Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0, hR1])
        | ok w1 =>
          dsimp only
          have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable hT hn ⟨w0, hR0⟩ ⟨w1, hR1⟩
          have hDec := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
            .replyRecv (.inr (.inl ⟨hRt, rfl⟩)) hRead
          exact entryOperandOutcome_of_long ctx executingCore st kGen kRes kLook tid tcb
            (longMessageDecode .replyRecv st tid tcb.registerContext capAddr msgInfo) .replyRecv capAddr
            (replyRecvLongOperandArmThenTaintR ctx tcb.registerContext msgInfo.length
              msgInfo.extraCaps msgInfo.label tid executingCore
              (syscallRequiredRight .replyRecv))
            (msgInfo.length - 4) hCur hObj hDec rfl rfl (by
              simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true,
                ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0, hR1]
              rfl) (by intro _; rfl) hn0 hn
    | transferring sid capAddr msgInfo =>
      by_cases hShort : msgInfo.length ≤ 4
      · obtain ⟨-, -, -, hShortDec, -⟩ :=
          SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedTransferring
            st tid _ _ 32 sid capAddr msgInfo hRt
        have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
        have hDec := hShortDec (by rw [hSz]; exact hShort)
        simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, hShort, Bool.false_eq_true,
          ↓reduceIte]
        exact hD
          ({ capAddr := capAddr, msgInfo := msgInfo, syscallId := sid,
             msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg tcb.registerContext),
             inlineCount := SeLe4n.arm64DefaultLayout.msgRegs.size,
             overflowCount := 0 } : SyscallDecodeResult)
          sid _ hCur hObj hDec rfl (by
          simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, hShort, Bool.false_eq_true,
            ↓reduceIte]
          rfl) (by intro _; rfl)
      · obtain ⟨-, -, hMax, -, -⟩ :=
          SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedTransferring
            st tid _ _ 32 sid capAddr msgInfo hRt
        have hGt : 4 < msgInfo.length := by omega
        have hRR : (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 =
              .replyLong capAddr msgInfo ∧ sid = .reply) ∨
            (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 =
              .replyRecvLong capAddr msgInfo ∧ sid = .replyRecv) ∨
            (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 =
              .transferring sid capAddr msgInfo ∧ 4 < msgInfo.length) :=
          .inr (.inr ⟨hRt, hGt⟩)
        have hT : st.getTcb? tid = some tcb := by
          rw [SystemState.getObject?_eq_getElem] at hObj
          simp only [SystemState.getTcb?, hObj]
        have hn0 : 0 < msgInfo.length - 4 := by omega
        have hn : msgInfo.length - 4 ≤ SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots := by
          have h116 : SeLe4n.Kernel.Architecture.IpcBufferRead.maxOverflowSlots = 116 := rfl
          have h120 : maxMessageRegisters = 120 := rfl
          rw [h116]; rw [h120] at hMax; omega
        simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, hShort, Bool.false_eq_true,
          ↓reduceIte]
        rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
        cases hR0 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 with
        | error e =>
          exact .inl (by simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, hShort,
            Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0])
        | ok w0 =>
          dsimp only
          rw [SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
          cases hR1 : SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMr st tid
              (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (msgInfo.length - 4)) with
          | error e =>
            exact .inl (by simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, hShort,
              Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0, hR1])
          | ok w1 =>
            dsimp only
            have hRead := SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowReadable hT hn ⟨w0, hR0⟩ ⟨w1, hR1⟩
            have hDec := decodeSyscallArgsFromState_of_routedReplyLong_ok st tid _ capAddr msgInfo
              sid hRR hRead
            exact entryOperandOutcome_of_long ctx executingCore st kGen kRes kLook tid tcb
              (longMessageDecode sid st tid tcb.registerContext capAddr msgInfo) sid capAddr
              (transferringOperandArmThenTaintR ctx sid tcb.registerContext
                msgInfo.length tid executingCore (syscallRequiredRight sid))
              (msgInfo.length - 4) hCur hObj hDec rfl rfl (by
                simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, hShort,
                  Bool.false_eq_true, ↓reduceIte, SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK_eq, hR0, hR1]
                rfl) (by intro _; rfl) hn0 hn
    | overflowed sid capAddr len =>
      refine .inl ?_
      simp only [syscallEntryCheckedK, syscallEntryCheckedR, hCtx, hCur, hObj, hRt,
        Bool.false_eq_true, ↓reduceIte]
      simp only [ipcBufferReadMrK_comp kGen]
    | shortArgs sid capAddr =>
      obtain ⟨decoded, hDec, hSid, hRS, hCap, -⟩ :=
        SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedShortArgs
          st tid _ _ 32 sid capAddr hRt
      subst hCap
      simp only [syscallEntryCheckedK, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
      exact hD decoded _ _ hCur hObj hDec hSid (by
        simp only [syscallEntryCheckedR, hCtx, hCur, hObj, hRt, Bool.false_eq_true, ↓reduceIte]
        rfl) (by
          intro _
          revert hRS
          cases sid <;> intro hRS <;> first | rfl | exact absurd hRS (by decide))
    | yield | viaDecode | refused _ =>
      exact .inl (by simp only [syscallEntryCheckedK, syscallEntryCheckedR, hCtx, hCur, hObj,
        hRt, Bool.false_eq_true, ↓reduceIte])

end SeLe4n.Kernel
