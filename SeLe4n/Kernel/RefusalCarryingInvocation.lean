-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingDispatch
import SeLe4n.Kernel.VSpaceRemapPerform
import SeLe4n.Kernel.IPC.CrossCore.SuspendAdmission

/-!
# Capability invocations on the register file

WS-ZA ZA5.1.  The capability invocations the IPC rows do not route — the
CSpace, untyped, VSpace, page-table, TCB, notification-binding,
scheduling-context binding and service-revoke and -query calls — read their
arguments from the caller's register file (`msgRegOfFile`) instead of a decode
record's message-register array.  `dispatchInvocationBy` is
`dispatchWithCapChecked` reading the register file
(`dispatchWithCapChecked_eq_invocationBy`), and `dispatchInvocationCheckedR`
runs it behind the shared operand check (`dispatchOperandCheckedR`), equal to
`dispatchSyscallChecked` (`dispatchInvocationCheckedR_eq`).

Every routed invocation is inert and records no declassification, so its taint
step leaves the state as the arm left it (`applySyscallTaintAfter_inert`), and
checks its rights in the classic order.  The scheduling-context configure and
the service register carry a fifth argument word and are routed as the entry's
`overflowOne` arm (`dispatchOverflowOneCheckedR`, at the end of this file); the
declassification and audit calls are the entry's `audited` arm
(`RefusalCarryingDeclassification`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.SyscallArgDecode
open Architecture.RegisterDecode (routedInvocation)

/-- `dispatchWithCapChecked`'s arm for a routed invocation, its arguments read
from the register file `regs` through `layout` and its operand address given
(`dispatchWithCapChecked_eq_invocationBy`).  Each decode reads the file at its
own call (`msgRegOfFile`), so no reader closure is built.
Any other syscall is `.illegalState`; the entry routes none here. -/
def dispatchInvocationBy (ctx : LabelingContext) (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) (st : SystemState) : Except KernelError (Unit × SystemState) :=
  match sid with
  | .cspaceCopy =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceCopyArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            match resolveCNodeOpSlots tid cap args.destIndex args.destDepth args.srcRoot
                args.srcIndex args.srcDepth st with
            | .error e => .error e
            | .ok (src, dst) => cspaceCopyChecked ctx src dst args.rights st
    | _ => .error (.invalidCapability 0)
  | .cspaceMove =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceMoveArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            match resolveCNodeOpSlots tid cap args.destIndex args.destDepth args.srcRoot
                args.srcIndex args.srcDepth st with
            | .error e => .error e
            | .ok (src, dst) => cspaceMoveChecked ctx src dst st
    | _ => .error (.invalidCapability 0)
  | .cspaceDelete =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceDeleteArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
            cspaceDeleteSlotZombie executingCore addr st
    | _ => .error (.invalidCapability 0)
  | .cspaceRevoke =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceDeleteArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
            cspaceRevokeCdtFinalising executingCore addr st
    | _ => .error (.invalidCapability 0)
  | .mintReplyCap =>
    match cap.target with
    | .object cnodeId =>
        match decodeMintReplyCapArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            mintReplyCapWithCdt src dst st
    | _ => .error (.invalidCapability 0)
  | .untypedRetype =>
    match cap.target with
    | .object _ => untypedRetypeFromCap tid executingCore capAddr (decodeUntypedRetypeArgsBy (msgRegOfFile layout regs)) st
    | _ => .error (.invalidCapability 0)
  | .untypedReset =>
    match cap.target with
    | .object _ => untypedResetFromCap tid capAddr st
    | _ => .error (.invalidCapability 0)
  | .vspaceMap =>
    match cap.target with
    | .object _ =>
          match decodeVSpaceMapArgsBy (msgRegOfFile layout regs) st.machine.maxASID with
          | .error e => .error e
          | .ok args =>
            if !vspaceCapAuthorizesAsid cap args.asid st then
              .error .illegalAuthority
            else
              vspaceMapOrRemapFromFrameCap tid executingCore args st
    | _ => .error (.invalidCapability 0)
  | .vspaceUnmap =>
    match cap.target with
    | .object _ =>
        match decodeVSpaceUnmapArgsBy (msgRegOfFile layout regs) st.machine.maxASID with
        | .error e => .error e
        | .ok args =>
          if !vspaceCapAuthorizesAsid cap args.asid st then
            .error .illegalAuthority
          else
            Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast
              executingCore args.asid args.vaddr st
    | _ => .error (.invalidCapability 0)
  | .vspaceUnifyInstruction =>
    match cap.target with
    | .object _ =>
        match decodeVSpaceUnmapArgsBy (msgRegOfFile layout regs) st.machine.maxASID with
        | .error e => .error e
        | .ok args =>
          if !vspaceCapAuthorizesAsid cap args.asid st then
            .error .illegalAuthority
          else
            Architecture.vspaceUnifyInstructionPage args.asid args.vaddr st
    | _ => .error (.invalidCapability 0)
  | .serviceRevoke =>
    match cap.target with
    | .object epId => revokeServiceChecked ctx tid epId st
    | _ => .error (.invalidCapability 0)
  | .serviceQuery =>
    match cap.target with
    | .object epId => serviceQueryStaged ctx tid epId st
    | _ => .error (.invalidCapability 0)
  | .schedContextBind =>
    match cap.target with
    | .object scId =>
      match resolveSchedContextBindThread tid (decodeSchedContextBindArgsBy (msgRegOfFile layout regs)) st with
      | .error e => .error e
      | .ok vThreadId =>
          match validateObjIdArg scId with
          | .error e => .error e
          | .ok vScId =>
              SchedContextOps.schedContextBind vScId vThreadId st
    | _ => .error (.invalidCapability 0)
  | .schedContextUnbind =>
    match cap.target with
    | .object scId =>
          match validateObjIdArg scId with
          | .error e => .error e
          | .ok vScId =>
              match SchedContextOps.schedContextUnbindOnCore vScId
                  executingCore st with
              | .ok (st', _) => .ok ((), st')
              | .error e => .error e
    | _ => .error (.invalidCapability 0)
  | .schedContextConsumed =>
    match cap.target with
    | .object scId =>
          match validateObjIdArg scId with
          | .error e => .error e
          | .ok vScId =>
              match schedContextConsumedOnCore (SeLe4n.SchedContextId.ofObjId vScId.val)
                  executingCore st with
              | .ok st' => .ok ((), st')
              | .error e => .error e
    | _ => .error (.invalidCapability 0)
  | .schedContextYieldTo =>
    match cap.target with
    | .object scId =>
          match validateObjIdArg scId with
          | .error e => .error e
          | .ok vScId =>
              match SchedContextOps.schedContextYieldToOnCore
                  (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore st with
              | .ok st' => .ok ((), st')
              | .error e => .error e
    | _ => .error (.invalidCapability 0)
  | .irqHandlerAck =>
    match cap.target with
    | .irqHandler line => Architecture.irqHandlerAck line st
    | _ => .error (.invalidCapability 0)
  | .irqControlGet =>
    match cap.target with
    | .irqControl _ =>
        irqControlGetFromCap tid capAddr (decodeIrqControlGetArgsBy (msgRegOfFile layout regs)) st
    | _ => .error (.invalidCapability 0)
  | .irqHandlerSetNotification =>
    match cap.target with
    | .irqHandler line =>
        irqHandlerSetNotificationFromCap tid executingCore line
          (decodeIrqHandlerSetNotificationArgsBy (msgRegOfFile layout regs)) st
    | _ => .error (.invalidCapability 0)
  | .irqHandlerClear =>
    match cap.target with
    | .irqHandler line => irqHandlerClear executingCore line st
    | _ => .error (.invalidCapability 0)
  | .tcbBindNotification =>
    match cap.target with
    | .object tcbObjId =>
      match decodeTcbBindNotificationArgsBy (msgRegOfFile layout regs) with
      | .error e => .error e
      | .ok args =>
          match st.getTcb? tid with
          | some callerTcb =>
            let ntfnGate : SyscallGate := {
              callerId      := tid
              cspaceRootCap := callerTcb.spaceCells[0]
              capAddr       := args.notificationCPtr
              requiredRight := .write
            }
            match syscallLookupArgumentCap bindNotificationCapNumber ntfnGate st with
            | .error e => .error e
            | .ok (ntfnCap, _) =>
              match ntfnCap.target with
              | .object notifId =>
                  bindNotification notifId (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st
              | _ => .error .illegalState
          | none => .error .objectNotFound
    | _ => .error (.invalidCapability 0)
  | .tcbUnbindNotification =>
    match cap.target with
    | .object tcbObjId =>
        match unbindNotification (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st with
        | .error e => .error e
        | .ok ((), st') => .ok ((), st')
    | _ => .error (.invalidCapability 0)
  | .tcbSuspend =>
    match cap.target with
    | .object objId =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match Lifecycle.Suspend.suspendThreadOnCore st vtid
                executingCore with
            | .ok (st', _) => .ok ((), st')
            | .error e => .error e
    | _ => .error (.invalidCapability 0)
  | .tcbResume =>
    match cap.target with
    | .object objId =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match Lifecycle.Suspend.resumeThreadOnCore
                (retirePendingFaultForResume st vtid.val) vtid
                executingCore with
            | .ok (st', _) => .ok ((), st')
            | .error e => .error e
    | _ => .error (.invalidCapability 0)
  | .tcbSetPriority =>
    match cap.target with
    | .object objId =>
      match decodeSetPriorityArgsBy (msgRegOfFile layout regs) with
      | .error e => .error e
      | .ok args =>
        match validateThreadIdArg tid with
        | .error e => .error e
        | .ok vCallerTid =>
            match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
            | .error e => .error e
            | .ok vTargetTid =>
                match SchedContext.PriorityManagement.setPriorityOnCore st
                    vCallerTid vTargetTid
                    (Priority.ofNat args.newPriority) executingCore with
                | .ok (st', _) => .ok ((), st')
                | .error e => .error e
    | _ => .error (.invalidCapability 0)
  | .tcbSetMCPriority =>
    match cap.target with
    | .object objId =>
      match decodeSetMCPriorityArgsBy (msgRegOfFile layout regs) with
      | .error e => .error e
      | .ok args =>
        match validateThreadIdArg tid with
        | .error e => .error e
        | .ok vCallerTid =>
            match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
            | .error e => .error e
            | .ok vTargetTid =>
                match SchedContext.PriorityManagement.setMCPriorityOnCore st
                    vCallerTid vTargetTid
                    (Priority.ofNat args.newMCP) executingCore with
                | .ok (st', _) => .ok ((), st')
                | .error e => .error e
    | _ => .error (.invalidCapability 0)
  | .tcbSetIPCBuffer =>
    match cap.target with
    | .object objId =>
      match decodeSetIPCBufferArgsBy (msgRegOfFile layout regs) with
      | .error e => .error e
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match Architecture.IpcBufferValidation.setIPCBufferOp st
                vtid args.bufferAddr with
            | .ok st' => .ok ((), st')
            | .error e => .error e
    | _ => .error (.invalidCapability 0)
  | .tcbSetAffinity =>
    match cap.target with
    | .object objId =>
      match decodeSetAffinityArgsBy (msgRegOfFile layout regs) with
      | .error e => .error e
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match decodeAffinity args.affinityRaw with
            | .error e => .error e
            | .ok affinity =>
                match setThreadCpuAffinityOnCore st vtid affinity
                        executingCore with
                | .ok (st', _) => .ok ((), st')
                | .error e => .error e
    | _ => .error (.invalidCapability 0)
  | .tcbSetFaultHandler =>
    match cap.target with
    | .object objId =>
      match decodeSetFaultHandlerArgsBy (msgRegOfFile layout regs) with
      | .error e => .error e
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match setThreadFaultHandlerOp st vtid args.handlerCPtr with
            | .ok st' => .ok ((), st')
            | .error e => .error e
    | _ => .error (.invalidCapability 0)
  | .tcbSetSpace =>
    match cap.target with
    | .object objId =>
      match decodeSetSpaceArgsBy (msgRegOfFile layout regs) with
      | .error e => .error e
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match resolveSetSpace tid args st with
            | .error e => .error e
            | .ok (cnSrc, vrSrc) =>
                match copyThreadSpacesZombie executingCore st vtid cnSrc vrSrc args.cspaceRootData with
                | .ok st' => .ok ((), st')
                | .error e => .error e
    | _ => .error (.invalidCapability 0)
  | .pageTableMap =>
    match cap.target with
    | .object objId =>
      match decodePageTableMapArgsBy (msgRegOfFile layout regs) with
      | .error e => .error e
      | .ok args =>
          match resolveCallerCapObject tid args.vspaceRoot .write st with
          | .error e => .error (e.forArgumentCap Architecture.pageTableMapRootCapNumber)
          | .ok (_, rootId) => Architecture.pageTableMap objId rootId args.vaddr st
    | _ => .error (.invalidCapability 0)
  | .pageTableUnmap =>
    match cap.target with
    | .object objId => Architecture.pageTableUnmap objId st
    | _ => .error (.invalidCapability 0)
  | _ => .error .illegalState

/-- What routing an invocation rests on: it is inert, records no
declassification, and is not the yield. -/
theorem routedInvocation_classic (sid : SyscallId) (h : routedInvocation sid = true) :
    contentFlowClass sid = .inert ∧ syscallRecordsDeclassification sid = false ∧
      sid ≠ .yield := by
  cases sid <;> simp only [routedInvocation, Bool.false_eq_true] at h <;>
    exact ⟨rfl, rfl, fun h => SyscallId.noConfusion h⟩

/-- A routed invocation's taint step leaves the state as its arm left it. -/
theorem applySyscallTaintAfter_routed (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (h : routedInvocation decoded.syscallId = true)
    (preEpoch : Nat) (preLength : Nat) (preTaint : TaintMap)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength preTaint post =
      post := by
  obtain ⟨hC, hR, -⟩ := routedInvocation_classic _ h
  simp only [applySyscallTaintAfter, syscallTaintPlan, hC, hR, Bool.false_eq_true,
    ↓reduceIte, applyOrigination, applyTaintFlow, applyTaintClears, applyTaintStep, List.foldl,
    List.filter]

/-- `dispatchWithCapChecked` at a routed invocation whose message registers are
the layout's, read from the file, is `dispatchInvocationBy` reading the file. -/
theorem dispatchWithCapChecked_eq_invocationBy (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (st : SystemState) (h : routedInvocation decoded.syscallId = true)
    (hRegs : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum decoded.syscallId ≤ decoded.msgInfo.length) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      dispatchInvocationBy ctx decoded.syscallId decoded.capAddr
        layout regs tid executingCore cap st := by
  have hCopy := decodeCSpaceCopyArgs_eq_by layout regs decoded hRegs
  have hMove := decodeCSpaceMoveArgs_eq_by layout regs decoded hRegs
  have hReply := decodeMintReplyCapArgs_eq_by layout regs decoded hRegs
  have hDelete := decodeCSpaceDeleteArgs_eq_by layout regs decoded hRegs
  have hRetype := decodeUntypedRetypeArgs_eq_by layout regs decoded hRegs
  have hMap := decodeVSpaceMapArgs_eq_by layout regs decoded st.machine.maxASID hRegs
  have hUnmap := decodeVSpaceUnmapArgs_eq_by layout regs decoded st.machine.maxASID hRegs
  have hScBind := decodeSchedContextBindArgs_eq_by layout regs decoded hRegs
  have hNtfn := decodeTcbBindNotificationArgs_eq_by layout regs decoded hRegs
  have hPrio := decodeSetPriorityArgs_eq_by layout regs decoded hRegs
  have hMcp := decodeSetMCPriorityArgs_eq_by layout regs decoded hRegs
  have hIpcBuf := decodeSetIPCBufferArgs_eq_by layout regs decoded hRegs
  have hAff := decodeSetAffinityArgs_eq_by layout regs decoded hRegs
  have hFault := decodeSetFaultHandlerArgs_eq_by layout regs decoded hRegs
  have hSpace := decodeSetSpaceArgs_eq_by layout regs decoded hRegs
  have hPt := decodePageTableMapArgs_eq_by layout regs decoded hRegs
  have hIrqGet := decodeIrqControlGetArgs_eq_by layout regs decoded hRegs
  have hIrqNtfn := decodeIrqHandlerSetNotificationArgs_eq_by layout regs decoded hRegs
  rcases decoded with ⟨capAddr, msgInfo, sid, msgRegs, inlineCount, overflowCount⟩
  rcases cap with ⟨target, rights, badge, mapping⟩
  simp only [truncationMinimum] at *
  cases sid <;> simp only [routedInvocation, Bool.false_eq_true] at h <;>
    simp only [truncationMinimum] at hLen <;>
    cases target <;>
    simp only [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchInvocationBy, hLen,
      hCopy, hMove, hReply, hDelete, hRetype, hMap, hUnmap,
      hScBind, hNtfn, hPrio, hMcp, hIpcBuf, hAff, hFault,
      hSpace, hPt, hIrqGet, hIrqNtfn, decodeVSpaceUnifyInstructionArgs,
      dispatchCapabilityOnlyChecked]
  all_goals first | rfl | (split <;> rfl)

/-- WS-ZA ZA5.2: answering an admitted resume's pending fault keeps it admitted:
the write reads back (its slot is found in place), and it clears the fault and
leaves the thread state. -/
theorem resumeAdmitted_retirePendingFault {st : SystemState}
    {tid : SeLe4n.ThreadId} (h : Lifecycle.Suspend.resumeAdmitted st tid = true) :
    Lifecycle.Suspend.resumeAdmitted (retirePendingFaultForResume st tid) tid = true := by
  unfold Lifecycle.Suspend.resumeAdmitted at h
  cases hT : st.getTcb? tid with
  | none => rw [hT] at h; cases h
  | some tcb =>
    rw [hT] at h
    cases hF : tcb.pendingFault with
    | none =>
      have hE : retirePendingFaultForResume st tid = st := by
        simp only [retirePendingFaultForResume, hT, hF]
      rw [hE]; unfold Lifecycle.Suspend.resumeAdmitted; rw [hT]; exact h
    | some tf =>
      have hIF : tcb.faultWords.isFault = true := by
        rw [← TCB.pendingFault_isSome, hF]; rfl
      simp only [hIF, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
      have hClear : ∀ t : TCB, (t.setPendingFault none).faultWords.isFault = false :=
        fun _ => rfl
      unfold Lifecycle.Suspend.resumeAdmitted
      cases hR : st.machine.residentOnSomeCore tid
      · simp only [retirePendingFaultForResume, hT, hF, hR, Bool.false_eq_true, if_false,
          applyFaultRestart]
        rw [updateTcb_getTcb?_self_of_findsInPlace _ hT h.2]
        simp only [TCB.withRestartFrame_threadState, hClear, Bool.not_false, Bool.true_or,
          Bool.and_true]
        exact h.1
      · simp only [retirePendingFaultForResume, hT, hF, hR, if_true, discardPendingFault]
        rw [updateTcb_getTcb?_self_of_findsInPlace _ hT h.2]
        simp only [hClear, Bool.not_false, Bool.true_or, Bool.and_true]
        exact h.1

/-- WS-ZA ZA5.2: `dispatchInvocationBy`, refusal-carrying, with each arm whose
write has been split into its checks and its in-slot write
(`RefusalCarrying.ofChecked`) reading the checks first and handing the state to
the write alone.  An arm whose checks refuse, and every arm not yet split, is
`ofKernel` of `dispatchInvocationBy`, whose refusal precedes any write
(`dispatchInvocationByR_eq`).  Where that arm of `dispatchInvocationBy` hands
an operation's refusal on as a refusal of another type, the refused path runs
the operation itself (`RefusalCarrying.ofCheckedThen`), so the operation's
refusal is read where it is, never rebuilt. -/
@[inline] def dispatchInvocationByR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
  match sid with
  | .tcbSetPriority =>
    match cap.target with
    | .object objId =>
      match decodeSetPriorityArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match validateThreadIdArg tid with
        | .error e => .error (e, st)
        | .ok vCallerTid =>
          match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | .error e => .error (e, st)
          | .ok vTargetTid =>
            RefusalCarrying.ofCheckedThen
              (SchedContext.PriorityManagement.setPriorityAdmitted st vCallerTid vTargetTid
                (Priority.ofNat args.newPriority) executingCore)
              (fun st => SchedContext.PriorityManagement.setPriorityPerform st vTargetTid.val
                (Priority.ofNat args.newPriority) executingCore)
              (fun st => SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid
                vTargetTid (Priority.ofNat args.newPriority) executingCore)
              (fun r => .ok ((), r.1)) st
    | _ => .error (.invalidCapability 0, st)
  | .tcbSetMCPriority =>
    match cap.target with
    | .object objId =>
      match decodeSetMCPriorityArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match validateThreadIdArg tid with
        | .error e => .error (e, st)
        | .ok vCallerTid =>
          match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | .error e => .error (e, st)
          | .ok vTargetTid =>
            RefusalCarrying.ofCheckedThen
              (SchedContext.PriorityManagement.setMCPriorityAdmitted st vCallerTid vTargetTid
                (Priority.ofNat args.newMCP))
              (fun st => st.updateTcb vTargetTid.val
                (fun t => { t with maxControlledPriority := Priority.ofNat args.newMCP }))
              (fun st => SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid
                vTargetTid (Priority.ofNat args.newMCP) executingCore)
              (fun r => .ok ((), r.1)) st
    | _ => .error (.invalidCapability 0, st)
  | .tcbSetIPCBuffer =>
    match cap.target with
    | .object objId =>
      match decodeSetIPCBufferArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error (e, st)
        | .ok vtid =>
          RefusalCarrying.ofCheckedThen
            (Architecture.IpcBufferValidation.setIPCBufferAdmitted st vtid args.bufferAddr)
            (fun st => st.updateTcb vtid.val (fun t => { t with ipcBuffer := args.bufferAddr }))
            (fun st => Architecture.IpcBufferValidation.setIPCBufferOp st vtid args.bufferAddr)
            (fun st' => .ok ((), st')) st
    | _ => .error (.invalidCapability 0, st)
  | .tcbSetAffinity =>
    match cap.target with
    | .object objId =>
      match decodeSetAffinityArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error (e, st)
        | .ok vtid =>
          decodeAffinityK args.affinityRaw
            (fun affinity =>
              RefusalCarrying.ofCheckedThen (setAffinityAdmitted st vtid.val affinity)
                (fun st => setAffinityPerform st vtid.val affinity)
                (fun st => setThreadCpuAffinityOnCore st vtid affinity executingCore)
                (fun r => .ok ((), r.1)) st)
            (fun e => .error (e, st))
    | _ => .error (.invalidCapability 0, st)
  | .tcbSuspend =>
    match cap.target with
    | .object objId =>
      match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
      | .error e => .error (e, st)
      | .ok vtid =>
        RefusalCarrying.ofCheckedThen (Lifecycle.Suspend.suspendAdmitted st vtid.val)
          (fun st => Lifecycle.Suspend.suspendPerform st vtid executingCore)
          (fun st => Lifecycle.Suspend.suspendThreadOnCore st vtid executingCore)
          (fun r => .ok ((), r.1)) st
    | _ => .error (.invalidCapability 0, st)
  | .tcbResume =>
    match cap.target with
    | .object objId =>
      match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
      | .error e => .error (e, st)
      | .ok vtid =>
        RefusalCarrying.ofCheckedThen (Lifecycle.Suspend.resumeAdmitted st vtid.val)
          (fun st => Lifecycle.Suspend.resumePerform
            (retirePendingFaultForResume st vtid.val) vtid.val executingCore)
          (fun st => Lifecycle.Suspend.resumeThreadOnCore
            (retirePendingFaultForResume st vtid.val) vtid executingCore)
          (fun r => .ok ((), r.1)) st
    | _ => .error (.invalidCapability 0, st)
  | .tcbSetFaultHandler =>
    match cap.target with
    | .object objId =>
      match decodeSetFaultHandlerArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error (e, st)
        | .ok vtid =>
          RefusalCarrying.ofCheckedThen (setThreadFaultHandlerAdmitted st vtid args.handlerCPtr)
            (fun st => st.updateTcb vtid.val
              (fun t => { t with faultHandlerSet := true, faultHandlerWord := args.handlerCPtr }))
            (fun st => setThreadFaultHandlerOp st vtid args.handlerCPtr)
            (fun st' => .ok ((), st')) st
    | _ => .error (.invalidCapability 0, st)
  | .tcbSetSpace =>
    match cap.target with
    | .object objId =>
      match decodeSetSpaceArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error (e, st)
        | .ok vtid =>
          resolveSetSpaceK tid args st (fun e => .error (e, st)) (fun cnC cnS vrC vrS =>
            RefusalCarrying.ofChecked
              (copyThreadSpacesAdmitted st vtid { cnode := cnC, slot := cnS } { cnode := vrC, slot := vrS }
                args.cspaceRootData)
              (fun st => copyThreadSpacesZombiePerform executingCore st vtid cnC cnS vrC vrS
                args.cspaceRootData)
              (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability 0, st)
  | .schedContextBind =>
    match cap.target with
    | .object scObjId =>
      match decodeSchedContextBindArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match st.getTcb? tid with
        | some callerTcb =>
          lookupSlotK callerTcb args.tcbCPtr st
            (fun t a b c => KernelError.argumentCapRefusal bindThreadCapNumber (fun e => .error (e, st))
              (.failedLookup false (LookupFault.ofWords t a b c)))
            (fun cnode slot =>
              match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
              | none => .error (.invalidCapability bindThreadCapNumber, st)
              | some tcbCap =>
                if SeLe4n.Kernel.capTargetsReservedKernelObject tcbCap then
                  .error (.invalidCapability bindThreadCapNumber, st)
                else if tcbCap.hasRight .write then
                  match tcbCap.target with
                  | .object tcbObjId =>
                    match st.getTcb? (SeLe4n.ThreadId.ofNat tcbObjId.toNat) with
                    | none => .error (.invalidCapability bindThreadCapNumber, st)
                    | some _ =>
                      match validateThreadIdArg (SeLe4n.ThreadId.ofNat tcbObjId.toNat) with
                      | .error e => .error (e, st)
                      | .ok vThreadId =>
                        match validateObjIdArg scObjId with
                        | .error e => .error (e, st)
                        | .ok vScId =>
                          RefusalCarrying.ofChecked
                            (SchedContextOps.schedContextBindAdmitted st vScId vThreadId)
                            (fun st => SchedContextOps.schedContextBindPerform st vScId vThreadId)
                            (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
                  | _ => .error (.invalidCapability bindThreadCapNumber, st)
                else .error (.illegalAuthority, st))
        | none => .error (.objectNotFound, st)
    | _ => .error (.invalidCapability 0, st)
  | .schedContextUnbind =>
    match cap.target with
    | .object scObjId =>
      match validateObjIdArg scObjId with
      | .error e => .error (e, st)
      | .ok vScId =>
        RefusalCarrying.ofCheckedThen (SchedContextOps.schedContextUnbindAdmitted st vScId)
          (fun st => SchedContextOps.schedContextUnbindOnCorePerform st vScId executingCore)
          (SchedContextOps.schedContextUnbind vScId)
          (fun r =>
            match SchedContext.PriorityManagement.priorityRescheduleOnCore r.2
                (SchedContextOps.schedContextRunningCore? st vScId.val) executingCore true with
            | .ok (st', _) => .ok ((), st')
            | .error e => .error e) st
    | _ => .error (.invalidCapability 0, st)
  | .schedContextConsumed =>
    match cap.target with
    | .object scObjId =>
      match validateObjIdArg scObjId with
      | .error e => .error (e, st)
      | .ok vScId =>
        RefusalCarrying.ofCheckedThen
          (schedContextConsumedAdmitted st (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore)
          (fun st => schedContextConsumedPerform st (SeLe4n.SchedContextId.ofObjId vScId.val)
            executingCore)
          (schedContextConsumedOnCore (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore)
          (fun st' => .ok ((), st')) st
    | _ => .error (.invalidCapability 0, st)
  | .schedContextYieldTo =>
    match cap.target with
    | .object scObjId =>
      match validateObjIdArg scObjId with
      | .error e => .error (e, st)
      | .ok vScId =>
        RefusalCarrying.ofCheckedThen
          (SchedContextOps.schedContextYieldToAdmitted st
            (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore)
          (fun st => SchedContextOps.schedContextYieldToPerform st
            (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore)
          (SchedContextOps.schedContextYieldToOnCore
            (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore)
          (fun st' => .ok ((), st')) st
    | _ => .error (.invalidCapability 0, st)
  -- WS-ZA ZA6.32: the acknowledge refuses only a line that is no device line
  -- of this board (`deviceInterruptLine`, the board's line count), read
  -- before the write, so the mask is written in place.
  | .irqHandlerAck =>
    match cap.target with
    | .irqHandler line =>
        RefusalCarrying.ofChecked (Architecture.deviceInterruptLine st line)
          (fun st => Architecture.setInterruptLineMask st line false)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability 0, st)
  -- WS-ZA ZA6.32: the issue reads the decode, the line checks and the two
  -- slots, then the destination's emptiness, before it writes the line and
  -- the handler capability in place (`irqControlGetPerformAt`, on the slots'
  -- words).
  | .irqControlGet =>
    match cap.target with
    | .irqControl _ =>
      match decodeIrqControlGetArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match irqControlLineRefusal st args.line with
        | some e => .error (e, st)
        | none =>
          resolveIssuingSlotsK tid capAddr args.dstCNode args.dstSlot st (fun e => .error (e, st))
            (fun srcCnode srcSlot dstCnode dstSlot =>
              RefusalCarrying.ofChecked (irqControlGetAdmittedAt dstCnode dstSlot args.line st)
                (fun st => irqControlGetPerformAt srcCnode srcSlot dstCnode dstSlot args.line st)
                (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability 0, st)
  -- WS-ZA ZA6.32: the bind reads the decode, the named capability's slot, its
  -- notification and send right, the line's node and the node slot's delete
  -- (a plain one, or the final delete of a notification capability) before any
  -- write, then empties the node slot and copies the capability into it in
  -- place (`irqHandlerSetNotificationBindAt`).
  | .irqHandlerSetNotification =>
    match cap.target with
    | .irqHandler line =>
      match decodeIrqHandlerSetNotificationArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        resolveCallerCapSlotK tid args.notificationCPtr .write st
          (KernelError.argumentCapRefusal irqHandlerNotificationCapNumber (fun e => .error (e, st)))
          (fun srcCnode srcSlot ncap _ =>
            RefusalCarrying.ofChecked (irqHandlerSetNotificationAdmitted st line srcCnode ncap)
              (fun st => irqHandlerSetNotificationBindAt executingCore line srcCnode srcSlot ncap st)
              (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability 0, st)
  -- WS-ZA ZA6.32: the clear reads the line's node, then empties its slot by
  -- the zombie delete every slot delete is (`zombieDeleteAt`).
  | .irqHandlerClear =>
    match cap.target with
    | .irqHandler line =>
        RefusalCarrying.ofChecked (cnodeInvoked (irqNodeAddr line).cnode st)
          (fun st => zombieDeleteAt executingCore (irqNodeAddr line).cnode (irqNodeAddr line).slot st)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability 0, st)
  | .tcbBindNotification =>
    match cap.target with
    | .object tcbObjId =>
      match decodeTcbBindNotificationArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match st.getTcb? tid with
        | some callerTcb =>
          lookupSlotK callerTcb args.notificationCPtr st
            (fun t a b c => KernelError.argumentCapRefusal bindNotificationCapNumber (fun e => .error (e, st))
              (.failedLookup false (LookupFault.ofWords t a b c)))
            (fun cnode slot =>
              match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
              | none => .error (.invalidCapability bindNotificationCapNumber, st)
              | some ntfnCap =>
                if SeLe4n.Kernel.capTargetsReservedKernelObject ntfnCap then
                  .error (.invalidCapability bindNotificationCapNumber, st)
                else if ntfnCap.hasRight .write then
                  match ntfnCap.target with
                  | .object notifId =>
                    RefusalCarrying.ofChecked
                      (bindNotificationInPlace st notifId (SeLe4n.ThreadId.ofNat tcbObjId.toNat))
                      (fun st => storeBindNotification st notifId
                        (SeLe4n.ThreadId.ofNat tcbObjId.toNat))
                      (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
                  | _ => .error (.illegalState, st)
                else .error (.illegalAuthority, st))
        | none => .error (.objectNotFound, st)
    | _ => .error (.invalidCapability 0, st)
  | .tcbUnbindNotification =>
    match cap.target with
    | .object tcbObjId =>
      let notificationId : SeLe4n.ObjId :=
        ⟨boundNotificationCodeOf st (SeLe4n.ThreadId.ofNat tcbObjId.toNat) - 1⟩
      RefusalCarrying.ofChecked
        (unbindNotificationInPlace st (SeLe4n.ThreadId.ofNat tcbObjId.toNat))
        (fun st => storeUnbindNotification st (SeLe4n.ThreadId.ofNat tcbObjId.toNat)
          notificationId)
        (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability 0, st)
  | .cspaceMove =>
    match cap.target with
    | .object cnodeId =>
      match decodeCSpaceMoveArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        if !cnodeInvoked cnodeId st then .error (.objectNotFound, st) else
        resolveCNodeOpSlotsK tid cap args.destIndex args.destDepth args.srcRoot
          args.srcIndex args.srcDepth st
          (fun e => .error (e, st))
          (fun srcCNode srcSlot dstCNode dstSlot =>
            RefusalCarrying.ofChecked
              (securityFlowsTo (ctx.objectLabelOf srcCNode) (ctx.objectLabelOf dstCNode) &&
                cspaceMoveAdmittedAt srcCNode srcSlot dstCNode dstSlot st)
              (fun st => cspaceMovePerformAt srcCNode srcSlot dstCNode dstSlot st)
              (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability 0, st)
  | .cspaceDelete =>
    match cap.target with
    | .object cnodeId =>
      match decodeCSpaceDeleteArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
        RefusalCarrying.ofChecked (cnodeInvoked addr.cnode st)
          (fun st => zombieDeleteAt executingCore cnodeId args.targetSlot st)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability 0, st)
  | .cspaceRevoke =>
    match cap.target with
    | .object cnodeId =>
      match decodeCSpaceDeleteArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
        RefusalCarrying.ofChecked (cspaceRevokeAdmitted addr st)
          (fun st => cspaceRevokePerformAt executingCore cnodeId args.targetSlot st)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability 0, st)
  | .mintReplyCap =>
    match cap.target with
    | .object cnodeId =>
      match decodeMintReplyCapArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
        let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
        RefusalCarrying.ofChecked (mintReplyCapAdmittedAt cnodeId args.srcSlot args.dstSlot st)
          (fun st => mintReplyCapPerformAt cnodeId args.srcSlot args.dstSlot st)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability 0, st)
  | .cspaceCopy =>
    match cap.target with
    | .object cnodeId =>
      match decodeCSpaceCopyArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        if !cnodeInvoked cnodeId st then .error (.objectNotFound, st) else
        resolveCNodeOpSlotsK tid cap args.destIndex args.destDepth args.srcRoot
          args.srcIndex args.srcDepth st
          (fun e => .error (e, st))
          (fun srcCNode srcSlot dstCNode dstSlot =>
            RefusalCarrying.ofChecked
              (securityFlowsTo (ctx.objectLabelOf srcCNode) (ctx.objectLabelOf dstCNode) &&
                cspaceCopyAdmittedAt srcCNode srcSlot dstCNode dstSlot args.rights st)
              (fun st => cspaceCopyPerformAt srcCNode srcSlot dstCNode dstSlot args.rights st)
              (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability 0, st)
  | .vspaceMap =>
    match cap.target with
    | .object rootId =>
      match decodeVSpaceMapArgsBy (msgRegOfFile layout regs) st.machine.maxASID with
      | .error e => .error (e, st)
      | .ok args =>
        if !vspaceCapAuthorizesAsid cap args.asid st then .error (.illegalAuthority, st)
        else
          resolveVSpaceMapFrameK tid args st (fun e => .error (e, st))
            (fun frameCnode frameSlot frameCap frame =>
              -- seL4's `Page_Map` on a capability whose mapping is in place:
              -- every refusal read before any write, in seL4's order
              -- (`vspaceMapOrRemapFromFrameCap_of_remapRefused`); admitted, the
              -- unmap in place, then the map in place on the state it leaves
              -- (`vspaceMapOrRemapFromFrameCap_of_remapAdmitted`).
              if capabilityMappingLive st frameCap then
                match vspaceRemapRefusal st args frameCap frame with
                | .error e => .error (e, st)
                | .ok () =>
                  if vspaceRemapInPlaceAt st args frameCap rootId then
                    .ok ((), vspaceMapPerformAt executingCore args.asid args.vaddr frame.base
                      args.perms rootId (frameCapObjId frameCap) frameCnode frameSlot
                      (vspaceUnmapPerformAt executingCore args.asid args.vaddr rootId st))
                  else
                    RefusalCarrying.ofChecked false (fun st => st)
                      (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
              else
                RefusalCarrying.ofChecked (vspaceMapAdmittedAt st args frameCap frame rootId)
                  (fun st => vspaceMapPerformAt executingCore args.asid args.vaddr frame.base
                    args.perms rootId (frameCapObjId frameCap) frameCnode frameSlot st)
                  (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability 0, st)
  | .vspaceUnmap =>
    match cap.target with
    | .object rootId =>
      match decodeVSpaceUnmapArgsBy (msgRegOfFile layout regs) st.machine.maxASID with
      | .error e => .error (e, st)
      | .ok args =>
        if !vspaceCapAuthorizesAsid cap args.asid st then .error (.illegalAuthority, st)
        -- An address nothing is mapped at is refused on the root's words
        -- (`vspaceUnmapUnmappedAt`), before the unmap's wrappers run.
        else if vspaceUnmapUnmappedAt st args.asid args.vaddr rootId then
          .error (.translationFault, st)
        else
          RefusalCarrying.ofChecked (vspaceUnmapAdmittedAt st args.asid args.vaddr rootId)
            (fun st => vspaceUnmapPerformAt executingCore args.asid args.vaddr rootId st)
            (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability 0, st)
  | .vspaceUnifyInstruction =>
    match cap.target with
    | .object _ =>
      match decodeVSpaceUnmapArgsBy (msgRegOfFile layout regs) st.machine.maxASID with
      | .error e => .error (e, st)
      | .ok args =>
        if !vspaceCapAuthorizesAsid cap args.asid st then .error (.illegalAuthority, st)
        else
          RefusalCarrying.ofChecked (vspaceUnifyAdmittedAt st args.asid args.vaddr)
            (fun st => vspaceUnifyPerformAt args.asid args.vaddr st)
            (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability 0, st)
  | .pageTableMap =>
    match cap.target with
    | .object objId =>
      match decodePageTableMapArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        resolveCallerCapObjectK tid args.vspaceRoot .write st
          (KernelError.argumentCapRefusal Architecture.pageTableMapRootCapNumber (fun e => .error (e, st)))
          (fun _ rootId =>
            RefusalCarrying.ofChecked (pageTableMapAdmittedAt st objId rootId args.vaddr)
              (fun st => pageTableMapPerformAt objId rootId args.vaddr st)
              (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability 0, st)
  -- The in-use refusal is read on the table's words (`pageTableUnmapInUseAt`),
  -- so it builds no install record or slot.
  | .pageTableUnmap =>
    match cap.target with
    | .object objId =>
      if pageTableUnmapInUseAt st objId then .error (.revocationRequired, st)
      else
        RefusalCarrying.ofChecked (pageTableUnmapAdmittedAt st objId)
          (fun st => pageTableUnmapPerformAt objId st)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability 0, st)
  | .untypedRetype =>
    match cap.target with
    | .object _ =>
      match decodeUntypedRetypeArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        -- The request as words (`carveRequestWordsK`), read by the carve's
        -- checks and writes (`untypedRetypeAdmittedCode`,
        -- `untypedRetypePerformCode`), so no request is built.
        carveRequestWordsK st executingCore args.newType args.sizeBits (fun e => .error (e, st))
          (fun k n dom core asid =>
          match validateObjIdArg args.childId with
          | .error e => .error (e.forArgumentWord UntypedRetypeArgs.childIdWord, st)
          | .ok vChild =>
            resolveIssuingSlotsK tid capAddr args.dstCNode args.dstSlot st (fun e => .error (e, st))
              (fun srcCnode srcSlot dstCnode dstSlot =>
                -- The kernel heap's refusal, answered here in the state the
                -- arm was handed: the carve's first check, so the general
                -- path it would otherwise fall back to (which decodes the
                -- invocation again) never runs for it.
                if !CarveRequest.heapAdmittedW st k n then .error (.untypedRegionExhausted st.machine.kernelHeapFreeBytes.toUInt64, st) else
                -- Every other refusal is read from the checks' words as well
                -- (`untypedRetypeRefusalCode`), so the general path, which
                -- decodes the invocation again, never runs here.
                if untypedRetypeAdmittedCode st ⟨srcCnode, srcSlot⟩ ⟨dstCnode, dstSlot⟩ vChild.val
                    k n asid then
                  .ok ((), untypedRetypePerformCode srcCnode srcSlot dstCnode dstSlot
                    vChild.val k n dom core asid st)
                else
                  .error (untypedRetypeRefusalCode st ⟨srcCnode, srcSlot⟩ ⟨dstCnode, dstSlot⟩
                    vChild.val k n asid, st)))
    | _ => .error (.invalidCapability 0, st)
  | .untypedReset =>
    match cap.target with
    | .object _ =>
      resolveCallerCapSlotK tid capAddr .retype st (fun e => .error (e, st))
        (fun srcCnode srcSlot _ _ =>
          RefusalCarrying.ofChecked (untypedResetAdmittedAt st srcCnode srcSlot)
            (fun st => untypedResetPerformAt srcCnode srcSlot st)
            (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability 0, st)
  -- WS-ZA ZA5.5: the revoke and the query through the endpoint read its
  -- recorded registration first and then write in place.
  | .serviceRevoke =>
    match cap.target with
    | .object epId =>
      RefusalCarrying.ofChecked
        (serviceEndpointWriteAdmitted ctx tid epId && recordedRegistrationPresent st epId)
        (fun st => revokeServiceByRecordedRegistrationPerform st epId)
        (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability 0, st)
  | .serviceQuery =>
    match cap.target with
    | .object epId =>
      RefusalCarrying.ofCheckedThen
        (serviceEndpointReadAdmitted ctx tid epId && recordedRegistrationPresent st epId)
        (fun st => serviceQueryPerform st tid epId)
        (lookupServiceChecked ctx tid epId)
        (fun r => .ok ((), Architecture.writeReturnFrameToTcb r.2 tid
          (Architecture.returnFrameOfWord r.1.sid.val.toUInt64))) st
    | _ => .error (.invalidCapability 0, st)
  | _ =>
    match dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap st with
    | .error e => .error (e, st)
    | .ok r => .ok r

theorem dispatchInvocationByR_eq (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState) :
    dispatchInvocationByR ctx sid capAddr layout regs tid executingCore cap st =
      RefusalCarrying.ofKernel
        (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st := by
  rcases cap with ⟨target, rights, badge, mapping, mAsid, mVaddr, mEpoch, mapped, freeIndex,
    cnGuard, cnGuardSize⟩
  unfold dispatchInvocationByR
  cases sid
  case tcbSetPriority =>
    cases target
    case object objId =>
      dsimp only
      cases hD : decodeSetPriorityArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        cases hC : validateThreadIdArg tid with
        | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC]
        | ok vC =>
          cases hT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, hT]
          | ok vT =>
            dsimp only
            refine RefusalCarrying.ofCheckedThen_eq _ _ _ _ _ _ ?_ ?_
            · simp only [dispatchInvocationBy, hD, hC, hT]
              split <;> simp_all
            intro hA
            obtain ⟨sgi, hS⟩ :=
              SchedContext.PriorityManagement.setPriorityOnCore_of_admitted _ _ _ _ _ hA
            simp only [dispatchInvocationBy, hD, hC, hT, hS]
    all_goals rfl
  case tcbSetMCPriority =>
    cases target
    case object objId =>
      dsimp only
      cases hD : decodeSetMCPriorityArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        cases hC : validateThreadIdArg tid with
        | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC]
        | ok vC =>
          cases hT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, hT]
          | ok vT =>
            dsimp only
            refine RefusalCarrying.ofCheckedThen_eq _ _ _ _ _ _ ?_ ?_
            · simp only [dispatchInvocationBy, hD, hC, hT]
              split <;> simp_all
            intro hA
            simp only [dispatchInvocationBy, hD, hC, hT,
              SchedContext.PriorityManagement.setMCPriorityOnCore_of_admitted _ _ _ _ _ hA]
    all_goals rfl
  case tcbSetIPCBuffer =>
    cases target
    case object objId =>
      dsimp only
      cases hD : decodeSetIPCBufferArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        cases hT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hT]
        | ok vT =>
          dsimp only
          refine RefusalCarrying.ofCheckedThen_eq _ _ _ _ _ _ ?_ ?_
          · simp only [dispatchInvocationBy, hD, hT]
            split <;> simp_all
          intro hA
          simp only [dispatchInvocationBy, hD, hT,
            Architecture.IpcBufferValidation.setIPCBufferOp_of_admitted _ _ _ hA]
    all_goals rfl
  case tcbSetAffinity =>
    cases target
    case object objId =>
      dsimp only
      cases hD : decodeSetAffinityArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        cases hT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hT]
        | ok vT =>
          dsimp only
          rw [decodeAffinityK_eq]
          cases hF : decodeAffinity args.affinityRaw with
          | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hT, hF]
          | ok affinity =>
            dsimp only
            refine RefusalCarrying.ofCheckedThen_eq _ _ _ _ _ _ ?_ ?_
            · simp only [dispatchInvocationBy, hD, hT, hF]
              split <;> simp_all
            intro hA
            obtain ⟨sgi, hS⟩ := setThreadCpuAffinityOnCore_of_admitted _ _ _ executingCore hA
            simp only [dispatchInvocationBy, hD, hT, hF, hS]
    all_goals rfl
  case tcbSuspend =>
    cases target
    case object objId =>
      dsimp only
      cases hT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hT]
      | ok vT =>
        dsimp only
        refine RefusalCarrying.ofCheckedThen_eq _ _ _ _ _ _ ?_ ?_
        · simp only [dispatchInvocationBy, hT]
          split <;> simp_all
        intro hA
        obtain ⟨sgi, hS⟩ := Lifecycle.Suspend.suspendThreadOnCore_of_admitted _ _ executingCore hA
        simp only [dispatchInvocationBy, hT, hS]
    all_goals rfl
  case tcbResume =>
    cases target
    case object objId =>
      dsimp only
      cases hT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hT]
      | ok vT =>
        dsimp only
        refine RefusalCarrying.ofCheckedThen_eq _ _ _ _ _ _ ?_ ?_
        · simp only [dispatchInvocationBy, hT]
          split <;> simp_all
        intro hA
        obtain ⟨sgi, hS⟩ := Lifecycle.Suspend.resumeThreadOnCore_of_admitted _ _ executingCore
          (resumeAdmitted_retirePendingFault hA)
        simp only [dispatchInvocationBy, hT, hS]
    all_goals rfl
  case tcbSetFaultHandler =>
    cases target
    case object objId =>
      dsimp only
      cases hD : decodeSetFaultHandlerArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        cases hT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hT]
        | ok vT =>
          dsimp only
          refine RefusalCarrying.ofCheckedThen_eq _ _ _ _ _ _ ?_ ?_
          · simp only [dispatchInvocationBy, hD, hT]
            split <;> simp_all
          intro hA
          simp only [dispatchInvocationBy, hD, hT, setThreadFaultHandlerOp_of_admitted _ _ _ hA]
    all_goals rfl
  case tcbSetSpace =>
    cases target
    case object objId =>
      dsimp only
      cases hD : decodeSetSpaceArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        cases hT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hT]
        | ok vT =>
          dsimp only
          rw [resolveSetSpaceK_eq]
          cases hR : resolveSetSpace tid args st with
          | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hT, hR]
          | ok ids =>
            obtain ⟨cnSrc, vrSrc⟩ := ids
            try dsimp only
            apply RefusalCarrying.ofChecked_eq
            intro hA
            simp only [dispatchInvocationBy, hD, hT, hR, copyThreadSpacesZombie_of_admitted hA]
    all_goals rfl
  case schedContextBind =>
    cases target
    case object objId =>
      dsimp only
      cases hD : decodeSchedContextBindArgsBy (msgRegOfFile layout regs) with
      | error e =>
        simp [RefusalCarrying.ofKernel, dispatchInvocationBy, resolveSchedContextBindThread, hD]
      | ok args =>
        cases hC : st.getTcb? tid with
        | none =>
          simp [RefusalCarrying.ofKernel, dispatchInvocationBy, resolveSchedContextBindThread,
            hD, hC]
        | some callerTcb =>
          dsimp only
          rw [lookupSlotK_eq]
          cases hRes : lookupSlot callerTcb args.tcbCPtr st with
          | error e =>
            simp [RefusalCarrying.ofKernel, dispatchInvocationBy, resolveSchedContextBindThread,
              hD, hC, syscallLookupCap, syscallResolveCap, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap, hRes]
          | ok ref =>
            obtain ⟨cnode, slot⟩ := ref
            dsimp only
            cases hL : SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
            | none =>
              simp [RefusalCarrying.ofKernel, dispatchInvocationBy, resolveSchedContextBindThread,
                hD, hC, syscallLookupCap, syscallResolveCap, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap, hRes, hL]
            | some tcbCap =>
              dsimp only
              by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject tcbCap = true
              · simp [RefusalCarrying.ofKernel, dispatchInvocationBy,
                  resolveSchedContextBindThread, hD, hC, syscallLookupCap, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap,
                  syscallResolveCap, hRes, hL, hIdle]
              · by_cases hRight : tcbCap.hasRight .write = true
                · cases hTg : tcbCap.target with
                  | object tcbObjId =>
                    cases hT : st.getTcb? (SeLe4n.ThreadId.ofNat tcbObjId.toNat) with
                    | none =>
                      simp [RefusalCarrying.ofKernel, dispatchInvocationBy,
                        resolveSchedContextBindThread, hD, hC, syscallLookupCap, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap,
                        syscallResolveCap, hRes, hL, hIdle, hRight, hTg, hT]
                    | some _ =>
                      cases hV : validateThreadIdArg (SeLe4n.ThreadId.ofNat tcbObjId.toNat) with
                      | error e =>
                        simp [RefusalCarrying.ofKernel, dispatchInvocationBy,
                          resolveSchedContextBindThread, hD, hC, syscallLookupCap, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap,
                          syscallResolveCap, hRes, hL, hIdle, hRight, hTg, hT, hV]
                      | ok vThreadId =>
                        cases hS : validateObjIdArg objId with
                        | error e =>
                          simp [RefusalCarrying.ofKernel, dispatchInvocationBy,
                            resolveSchedContextBindThread, hD, hC, syscallLookupCap, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap,
                            syscallResolveCap, hRes, hL, hIdle, hRight, hTg, hT, hV, hS]
                        | ok vScId =>
                          simp only [hIdle, hRight, hTg, hT, hV, hS, Bool.false_eq_true,
                            ↓reduceIte]
                          apply RefusalCarrying.ofChecked_eq
                          intro hA
                          simp only [dispatchInvocationBy, resolveSchedContextBindThread, hD, hC,
                            syscallLookupCap, syscallResolveCap, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap, hRes, hL, hIdle, hRight,
                            hTg, hT, hV, hS, Bool.false_eq_true, ↓reduceIte,
                            SchedContextOps.schedContextBind_of_admitted _ _ _ hA]
                  | _ => simp [RefusalCarrying.ofKernel, dispatchInvocationBy,
                    resolveSchedContextBindThread, hD, hC, syscallLookupCap, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap,
                    syscallResolveCap, hRes, hL, hIdle, hRight, hTg]
                · simp [RefusalCarrying.ofKernel, dispatchInvocationBy,
                    resolveSchedContextBindThread, hD, hC, syscallLookupCap, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap,
                    syscallResolveCap, hRes, hL, hIdle, hRight]
    all_goals rfl
  case schedContextUnbind =>
    cases target
    case object objId =>
      dsimp only
      cases hS : validateObjIdArg objId with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hS]
      | ok vScId =>
        dsimp only
        refine RefusalCarrying.ofCheckedThen_eq _ _ _ _ _ _ ?_ ?_
        · simp only [dispatchInvocationBy, hS, SchedContextOps.schedContextUnbindOnCore]
          rcases SchedContextOps.schedContextUnbind vScId st with _ | ⟨⟨⟩, st'⟩ <;> rfl
        intro hA
        obtain ⟨sgi, hU⟩ := SchedContextOps.schedContextUnbindOnCore_of_admitted st vScId
          executingCore hA
        simp only [dispatchInvocationBy, hS, hU]
    all_goals rfl
  case schedContextConsumed =>
    cases target
    case object objId =>
      dsimp only
      cases hS : validateObjIdArg objId with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hS]
      | ok vScId =>
        dsimp only
        refine RefusalCarrying.ofCheckedThen_eq _ _ _ _ _ _ ?_ ?_
        · simp only [dispatchInvocationBy, hS]
          split <;> simp_all
        intro hA
        simp only [dispatchInvocationBy, hS, schedContextConsumedOnCore_of_admitted _ _ _ hA]
    all_goals rfl
  case schedContextYieldTo =>
    cases target
    case object objId =>
      dsimp only
      cases hS : validateObjIdArg objId with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hS]
      | ok vScId =>
        dsimp only
        refine RefusalCarrying.ofCheckedThen_eq _ _ _ _ _ _ ?_ ?_
        · simp only [dispatchInvocationBy, hS]
          split <;> simp_all
        intro hA
        simp only [dispatchInvocationBy, hS,
          SchedContextOps.schedContextYieldToOnCore_of_admitted _ _ _ hA]
    all_goals rfl
  case irqHandlerAck =>
    cases target
    case irqHandler line =>
      dsimp only
      apply RefusalCarrying.ofChecked_eq
      intro hA
      simp only [dispatchInvocationBy, Architecture.irqHandlerAck, hA, ↓reduceIte]
    all_goals rfl
  case irqControlGet =>
    cases target
    case irqControl =>
      dsimp only
      cases hD : decodeIrqControlGetArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, irqControlGetFromCap, hD]
      | ok args =>
        dsimp only
        cases hL : irqControlLineRefusal st args.line with
        | some e =>
          simp [RefusalCarrying.ofKernel, dispatchInvocationBy, irqControlGetFromCap, hD, hL]
        | none =>
          dsimp only
          rw [resolveIssuingSlotsK_eq]
          cases hR : resolveIssuingSlots tid capAddr args.dstCNode args.dstSlot st with
          | error e =>
            simp [RefusalCarrying.ofKernel, dispatchInvocationBy, irqControlGetFromCap, hD, hL, hR]
          | ok pr =>
            obtain ⟨src, dst⟩ := pr
            dsimp only
            apply RefusalCarrying.ofChecked_eq
            intro hA
            simp only [dispatchInvocationBy, irqControlGetFromCap, hD, hL, hR,
              irqControlGet_of_admitted hA]
            all_goals rfl
    all_goals rfl
  case irqHandlerSetNotification =>
    cases target
    case irqHandler line =>
      dsimp only
      cases hD : decodeIrqHandlerSetNotificationArgsBy (msgRegOfFile layout regs) with
      | error e =>
        simp [RefusalCarrying.ofKernel, dispatchInvocationBy, irqHandlerSetNotificationFromCap, hD]
      | ok args =>
        dsimp only
        rw [resolveCallerCapSlotK_eq]
        cases hR : resolveCallerCapSlot tid args.notificationCPtr .write st with
        | error e =>
          simp [RefusalCarrying.ofKernel, dispatchInvocationBy, irqHandlerSetNotificationFromCap,
            hD, hR, KernelError.argumentCapRefusal]
        | ok r =>
          obtain ⟨src, ncap, oid⟩ := r
          obtain ⟨_, _, _, hLk, _, _⟩ :=
            resolveCallerCapSlot_ok tid args.notificationCPtr .write st src ncap oid hR
          dsimp only
          apply RefusalCarrying.ofChecked_eq
          intro hA
          simp only [dispatchInvocationBy, irqHandlerSetNotificationFromCap, hD, hR,
            irqHandlerSetNotification_of_admitted hLk hA]
          all_goals rfl
    all_goals rfl
  case irqHandlerClear =>
    cases target
    case irqHandler line =>
      dsimp only
      apply RefusalCarrying.ofChecked_eq
      intro hA
      have hF : cspaceDeleteFinalisingAdmitted (irqNodeAddr line) st = true :=
        cspaceDeleteFinalisingAdmitted_of_cnodeInvoked hA
      have hA' : cnodeInvoked (irqNodeId line) st = true := hA
      simp only [dispatchInvocationBy, irqHandlerClear, hA', Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, cspaceDeleteSlotZombie_of_admitted hF]
    all_goals rfl
  case tcbBindNotification =>
    cases target
    case object objId =>
      dsimp only
      cases hD : decodeTcbBindNotificationArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        cases hC : st.getTcb? tid with
        | none => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC]
        | some callerTcb =>
          dsimp only
          rw [lookupSlotK_eq]
          cases hRes : lookupSlot callerTcb args.notificationCPtr st with
          | error e =>
            simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, syscallLookupCap, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word,
              syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap, syscallResolveCap, hRes]
          | ok ref =>
            obtain ⟨cnode, slot⟩ := ref
            dsimp only
            cases hL : SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
            | none =>
              simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, syscallLookupCap, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap,
                syscallResolveCap, hRes, hL]
            | some ntfnCap =>
              dsimp only
              by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject ntfnCap = true
              · simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap,
                  syscallLookupCap, syscallResolveCap, hRes, hL, hIdle]
              · by_cases hRight : ntfnCap.hasRight .write = true
                · cases hTg : ntfnCap.target with
                  | object notifId =>
                    simp only [hIdle, hRight, hTg, Bool.false_eq_true, ↓reduceIte]
                    apply RefusalCarrying.ofChecked_eq
                    intro hA
                    simp only [dispatchInvocationBy, hD, hC, syscallLookupCap, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap,
                      syscallResolveCap, hRes, hL, hIdle, hRight, hTg, Bool.false_eq_true,
                      ↓reduceIte, bindNotification_of_inPlace _ _ _ hA]
                  | _ => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap,
                    syscallLookupCap, syscallResolveCap, hRes, hL, hIdle, hRight, hTg]
                · simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, SyscallGate.lookupSlot_mk, LookupFault.ofWords_word, syscallLookupArgumentCap, KernelError.argumentCapRefusal, KernelError.forArgumentCap,
                    syscallLookupCap, syscallResolveCap, hRes, hL, hIdle, hRight]
    all_goals rfl
  case tcbUnbindNotification =>
    cases target
    case object objId =>
      dsimp only
      apply RefusalCarrying.ofChecked_eq
      intro hA
      simp only [dispatchInvocationBy, unbindNotification_of_inPlace _ _ hA]
    all_goals rfl
  case cspaceMove =>
    cases target
    case object cnodeId =>
      dsimp only
      cases hD : decodeCSpaceMoveArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        dsimp only
        rw [resolveCNodeOpSlotsK_eq]
        cases hR : resolveCNodeOpSlots tid
            ⟨.object cnodeId, rights, badge, mapping, mAsid, mVaddr, mEpoch, mapped, freeIndex,
              cnGuard, cnGuardSize⟩ args.destIndex args.destDepth args.srcRoot
            args.srcIndex args.srcDepth st with
        | error e =>
          simp only [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hR]
          cases cnodeInvoked cnodeId st <;> rfl
        | ok p =>
          obtain ⟨⟨sc, ss⟩, ⟨dc, ds⟩⟩ := p
          dsimp only [cspaceMoveAdmittedAt, cspaceMovePerformAt]
          rw [show cnodeInvoked cnodeId st = true from
            cnodeInvoked_of_resolveCNodeOpSlots_ok hR]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          apply RefusalCarrying.ofChecked_eq
          intro hA
          simp only [Bool.and_eq_true] at hA
          simp only [dispatchInvocationBy, hD, cspaceMoveChecked, hA.1, ↓reduceIte, cnodeInvoked,
            cnodeInvoked_of_resolveCNodeOpSlots_ok hR, hR, Bool.not_true, Bool.false_eq_true,
            cspaceMove_of_admitted hA.2]
    all_goals rfl
  case cspaceDelete =>
    cases target
    case object cnodeId =>
      dsimp only
      cases hD : decodeCSpaceDeleteArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        apply RefusalCarrying.ofChecked_eq
        intro hA
        have hF : cspaceDeleteFinalisingAdmitted { cnode := cnodeId, slot := args.targetSlot } st =
            true := cspaceDeleteFinalisingAdmitted_of_cnodeInvoked hA
        simp only [dispatchInvocationBy, hD, hA, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          cspaceDeleteSlotZombie_of_admitted hF]
    all_goals rfl
  case cspaceRevoke =>
    cases target
    case object cnodeId =>
      dsimp only
      cases hD : decodeCSpaceDeleteArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        apply RefusalCarrying.ofChecked_eq
        intro hA
        simp only [dispatchInvocationBy, hD, cnodeInvoked_of_lookupSlotCap hA, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, cspaceRevokeCdtFinalising_of_admitted hA]
    all_goals rfl
  case mintReplyCap =>
    cases target
    case object cnodeId =>
      dsimp only
      cases hD : decodeMintReplyCapArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        dsimp only [mintReplyCapAdmittedAt, mintReplyCapPerformAt]
        apply RefusalCarrying.ofChecked_eq
        intro hA
        simp only [dispatchInvocationBy, hD, cnodeInvoked_of_mintReplyCapAdmitted hA,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte, mintReplyCapWithCdt_of_admitted hA]
    all_goals rfl
  case cspaceCopy =>
    cases target
    case object cnodeId =>
      dsimp only
      cases hD : decodeCSpaceCopyArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        dsimp only
        rw [resolveCNodeOpSlotsK_eq]
        cases hR : resolveCNodeOpSlots tid
            ⟨.object cnodeId, rights, badge, mapping, mAsid, mVaddr, mEpoch, mapped, freeIndex,
              cnGuard, cnGuardSize⟩ args.destIndex args.destDepth args.srcRoot
            args.srcIndex args.srcDepth st with
        | error e =>
          simp only [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hR]
          cases cnodeInvoked cnodeId st <;> rfl
        | ok p =>
          obtain ⟨⟨sc, ss⟩, ⟨dc, ds⟩⟩ := p
          dsimp only [cspaceCopyAdmittedAt, cspaceCopyPerformAt]
          rw [show cnodeInvoked cnodeId st = true from
            cnodeInvoked_of_resolveCNodeOpSlots_ok hR]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          apply RefusalCarrying.ofChecked_eq
          intro hA
          simp only [Bool.and_eq_true] at hA
          simp only [dispatchInvocationBy, hD, cspaceCopyChecked, hA.1, ↓reduceIte, cnodeInvoked,
            cnodeInvoked_of_resolveCNodeOpSlots_ok hR, hR, Bool.not_true, Bool.false_eq_true,
            cspaceCopy_of_admitted hA.2]
    all_goals rfl
  case vspaceMap =>
    cases target
    case object rootId =>
      dsimp only
      cases hD : decodeVSpaceMapArgsBy (msgRegOfFile layout regs) st.machine.maxASID with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        dsimp only
        split
        · next hAu => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hAu]
        · next hAu =>
          rw [resolveVSpaceMapFrameK_eq]
          cases hRs : resolveVSpaceMapFrame tid args st with
          | error e =>
            simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hAu,
              vspaceMapOrRemapFromFrameCap, hRs]
          | ok triple =>
            obtain ⟨frameSlot, frameCap, frame⟩ := triple
            dsimp only
            split
            · next hLive =>
              cases hRf : vspaceRemapRefusal st args frameCap frame with
              | error e =>
                simp only [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hAu, Bool.false_eq_true,
                  ↓reduceIte, vspaceMapOrRemapFromFrameCap_of_remapRefused tid executingCore args st
                    frameSlot frameCap frame e hRs hLive hRf]
              | ok u =>
                cases u
                dsimp only
                split
                · next hIn =>
                  simp only [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hAu,
                    Bool.false_eq_true, ↓reduceIte,
                    vspaceMapOrRemapFromFrameCap_of_remapAdmitted tid executingCore args st
                      frameSlot frameCap frame rootId hRs hLive hRf hIn]
                · apply RefusalCarrying.ofChecked_eq
                  intro h
                  cases h
            · apply RefusalCarrying.ofChecked_eq
              intro hA
              simp only [dispatchInvocationBy, hD, hAu, Bool.false_eq_true, ↓reduceIte,
                vspaceMapOrRemapFromFrameCap_of_admitted tid executingCore args st frameSlot frameCap
                  frame rootId hRs hA]
    all_goals rfl
  case vspaceUnmap =>
    cases target
    case object rootId =>
      dsimp only
      cases hD : decodeVSpaceUnmapArgsBy (msgRegOfFile layout regs) st.machine.maxASID with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        dsimp only
        split
        · next hAu => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hAu]
        · next hAu =>
          split
          · next hU =>
            simp only [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hAu, Bool.false_eq_true,
              ↓reduceIte, vspaceUnmapPageWithShootdownAndIcacheBroadcast_of_unmappedAt executingCore
                args.asid args.vaddr rootId st hU]
          · apply RefusalCarrying.ofChecked_eq
            intro hA
            simp only [dispatchInvocationBy, hD, hAu, Bool.false_eq_true, ↓reduceIte,
              vspaceUnmapPageWithShootdownAndIcacheBroadcast_of_admitted executingCore args.asid
                args.vaddr rootId st hA]
    all_goals rfl
  case vspaceUnifyInstruction =>
    cases target
    case object rootId =>
      dsimp only
      cases hD : decodeVSpaceUnmapArgsBy (msgRegOfFile layout regs) st.machine.maxASID with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        dsimp only
        split
        · next hAu => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hAu]
        · next hAu =>
          apply RefusalCarrying.ofChecked_eq
          intro hA
          simp only [dispatchInvocationBy, hD, hAu, Bool.false_eq_true, ↓reduceIte,
            vspaceUnifyInstructionPage_of_admitted args.asid args.vaddr st hA]
    all_goals rfl
  case pageTableMap =>
    cases target
    case object objId =>
      dsimp only
      cases hD : decodePageTableMapArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        dsimp only
        rw [resolveCallerCapObjectK_eq]
        cases hRs : resolveCallerCapObject tid args.vspaceRoot .write st with
        | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hRs,
            KernelError.argumentCapRefusal]
        | ok pr =>
          obtain ⟨_, rootId⟩ := pr
          dsimp only
          apply RefusalCarrying.ofChecked_eq
          intro hA
          simp only [dispatchInvocationBy, hD, hRs,
            pageTableMap_of_admitted objId rootId args.vaddr st hA]
    all_goals rfl
  case pageTableUnmap =>
    cases target
    case object objId =>
      dsimp only
      split
      · next hU =>
        simp only [RefusalCarrying.ofKernel, dispatchInvocationBy, pageTableUnmap_of_inUseAt hU]
      · apply RefusalCarrying.ofChecked_eq
        intro hA
        simp only [dispatchInvocationBy, pageTableUnmap_of_admitted objId st hA]
    all_goals rfl
  case untypedRetype =>
    cases target
    case object _ =>
      dsimp only
      cases hD : decodeUntypedRetypeArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, untypedRetypeFromCap, hD]
      | ok args =>
        dsimp only
        rw [carveRequestWordsK_eq]
        cases hQ : carveRequestOf? st executingCore args.newType args.sizeBits with
        | error e =>
          simp [RefusalCarrying.ofKernel, dispatchInvocationBy, untypedRetypeFromCap, hD, hQ]
        | ok req =>
          dsimp only
          cases hV : validateObjIdArg args.childId with
          | error e =>
            simp [RefusalCarrying.ofKernel, dispatchInvocationBy, untypedRetypeFromCap, hD, hQ, hV]
          | ok vChild =>
            dsimp only
            rw [resolveIssuingSlotsK_eq]
            cases hR : resolveIssuingSlots tid capAddr args.dstCNode args.dstSlot st with
            | error e =>
              simp [RefusalCarrying.ofKernel, dispatchInvocationBy, untypedRetypeFromCap, hD, hQ,
                hV, hR]
            | ok pr =>
              obtain ⟨src, dst⟩ := pr
              dsimp only
              rw [CarveRequest.heapAdmittedW_words st (.ofNat 0) executingCore (.ofNat 0) req,
                untypedRetypeAdmittedCode_eq st _ _ _ (.ofNat 0) executingCore (.ofNat 0) req,
                untypedRetypeRefusalCode_eq st _ _ _ (.ofNat 0) executingCore (.ofNat 0) req]
              have hP : ∀ s, untypedRetypePerformCode src.cnode src.slot dst.cnode dst.slot
                  vChild.val req.kindWord req.sizeWord (req.domainWord (.ofNat 0))
                  (req.coreWord executingCore) (req.asidWord (.ofNat 0)) s =
                  untypedRetypePerformAt src dst vChild.val req s := fun s =>
                untypedRetypePerformCode_eq src dst vChild.val (.ofNat 0) executingCore (.ofNat 0)
                  req s
              simp only [hP]
              cases hH : req.heapAdmitted st
              · simp [RefusalCarrying.ofKernel, dispatchInvocationBy, untypedRetypeFromCap, hD, hQ,
                  hV, hR, hH, untypedRetypeObject_heapRefused _ _ _ _ _ hH]
              · simp only [hH, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                cases hA : untypedRetypeAdmittedAt st src dst vChild.val req
                · simp only [Bool.false_eq_true, ↓reduceIte, RefusalCarrying.ofKernel,
                    dispatchInvocationBy, untypedRetypeFromCap, hD, hQ, hV, hR, hH,
                    untypedRetypeObject_refused hA]
                · simp only [↓reduceIte, RefusalCarrying.ofKernel, dispatchInvocationBy,
                    untypedRetypeFromCap, hD, hQ, hV, hR, untypedRetypeObject_of_admitted hA]
    all_goals rfl
  case untypedReset =>
    cases target
    case object _ =>
      dsimp only
      rw [resolveCallerCapSlotK_eq]
      cases hR : resolveCallerCapSlot tid capAddr .retype st with
      | error e =>
        simp [RefusalCarrying.ofKernel, dispatchInvocationBy, untypedResetFromCap,
          resolveCallerCapSlotK_eq, hR]
      | ok r =>
        obtain ⟨src, c, oid⟩ := r
        dsimp only
        apply RefusalCarrying.ofChecked_eq
        intro hA
        simp only [dispatchInvocationBy, untypedResetFromCap, resolveCallerCapSlotK_eq, hR,
          untypedResetSlot_of_admitted hA]
    all_goals rfl
  case serviceRevoke =>
    cases target
    case object epId =>
      dsimp only
      apply RefusalCarrying.ofChecked_eq
      intro hA
      simp only [dispatchInvocationBy, revokeServiceChecked_of_admitted ctx tid epId st hA]
    all_goals rfl
  case serviceQuery =>
    cases target
    case object epId =>
      dsimp only
      refine RefusalCarrying.ofCheckedThen_eq _ _ _ _ _ _ ?_ ?_
      · simp only [dispatchInvocationBy, serviceQueryStaged]
        split <;> simp_all
      intro hA
      simp only [dispatchInvocationBy, serviceQueryStaged_of_admitted ctx tid epId st hA]
    all_goals rfl
  all_goals
    dsimp only [RefusalCarrying.ofKernel]
    split <;> next h => rw [h]

/-- A routed invocation's arm behind the operand check: the gate's type and
right (`syscallInvokeTyped`), then `dispatchInvocationBy` reading the caller's own
registers.  Its taint step is the identity (`applySyscallTaintAfter_routed`), so
there is none. -/
@[inline] def invocationOperandArmR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (regs : RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability 0, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
        else if !syscallTargetAccepted sid st cap then .error (.invalidCapability 0, st)
        else if cap.hasRight (syscallRequiredRight sid) then
          dispatchInvocationByR ctx sid capAddr SeLe4n.arm64DefaultLayout regs tid
            executingCore cap st
        else .error (syscallMissingRightError sid, st)

/-- `dispatchSyscallChecked` for a routed invocation, its operand address, syscall
and arguments read from the caller's register file (`dispatchInvocationCheckedR_eq`).

A specification: the compiled entry runs the arm out of line
(`syscallEntryRoutedK`), so no code is generated for it. -/
noncomputable def dispatchInvocationCheckedR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (regs : RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (invocationOperandArmR ctx sid capAddr regs tid executingCore)

theorem dispatchInvocationCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (regs : RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (hRouted : routedInvocation decoded.syscallId = true)
    (hRegs : MsgRegsAgreeBelow decoded.msgRegs
      (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum decoded.syscallId ≤ decoded.msgInfo.length) :
    dispatchInvocationCheckedR ctx decoded.syscallId decoded.capAddr regs tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  obtain ⟨-, -, hNotYield⟩ := routedInvocation_classic _ hRouted
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ hNotYield
  intro st tcb ref _ hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel, 
    syscallInvokeTyped, syscallResolveCap, SyscallGate.lookupSlot_mk, hRef,
    applySyscallTaintAfter_routed st tid decoded hRouted]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [invocationOperandArmR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hType : syscallTargetAccepted decoded.syscallId st cap = false
      · simp only [hIdle, hType, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      replace hType : syscallTargetAccepted decoded.syscallId st cap = true := by simpa using hType
      by_cases hRight : cap.hasRight (syscallRequiredRight decoded.syscallId) = true
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [dispatchInvocationByR_eq]
        simp only [RefusalCarrying.ofKernel]
        rw [← dispatchWithCapChecked_eq_invocationBy ctx decoded SeLe4n.arm64DefaultLayout regs
          tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId }
          cap st hRouted hRegs hLen]
        rcases dispatchWithCapChecked ctx decoded tid executingCore _ cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]

/-! ## The scheduling-context configure

WS-ZA ZA5.2.  A configure carries five argument words, one more than the
layout's message registers: the fifth (WS-ZA ZA6.4: the deadline) is overflow
slot 0 of the caller's IPC buffer, read at the entry (`ipcBufferReadMrK`) and
handed here as the word `w`.  Its taint step is the identity and its rights are
checked in the classic order, as a routed invocation's are.  WS-ZA ZA6.4: the
invoked capability is a core's scheduling control and the context is the
capability at MR0 (`resolveSchedControlConfigureTarget`, resolved by the
refusal-carrying form through its continuation form
`resolveSchedControlConfigureTargetK`, which allocates nothing), resolved before
any write. -/

/-- `dispatchWithCapChecked`'s configure arm, its arguments read from the
register file `regs` through `layout` and then the overflow word `w`
(`dispatchWithCapChecked_eq_configureBy`). -/
@[inline] def dispatchConfigureBy (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (w : UInt64) (tid : SeLe4n.ThreadId) (cap : Capability) (st : SystemState) :
    Except KernelError (Unit × SystemState) :=
  match cap.target with
  | .schedControl core =>
    match decodeSchedContextConfigureArgsCheckedBy (msgRegOfFileThen layout regs w) with
    | .error e => .error e
    | .ok args =>
      match resolveSchedControlConfigureTarget tid core args.scCPtr st with
      | .error e => .error e
      | .ok vScId =>
        if hCore : core < SeLe4n.Kernel.Concurrency.numCores then
          SchedContextOps.schedControlConfigure ⟨core, hCore⟩ vScId args.budget args.period
            args.priority args.deadline args.domain st
        else .error (.invalidCapability 0)
  | _ => .error (.invalidCapability 0)

theorem dispatchWithCapChecked_eq_configureBy (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (w : UInt64) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState)
    (h : decoded.syscallId = .schedContextConfigure)
    (hRegs : MsgRegsAgreeBelow decoded.msgRegs
      (layout.msgRegs.map (readReg regs) ++ #[(⟨w⟩ : RegValue)]) 5)
    (hLen : 5 ≤ decoded.msgInfo.length) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      dispatchConfigureBy layout regs w tid cap st := by
  have hDec := decodeSchedContextConfigureArgsChecked_eq_by layout regs w decoded hRegs hLen
  rcases decoded with ⟨capAddr, msgInfo, sid, msgRegs, inlineCount, overflowCount⟩
  rcases cap with ⟨target, rights, badge, mapping⟩
  simp only at h
  subst h
  cases target <;>
    simp only [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchConfigureBy, hDec]
  all_goals rfl

/-- `dispatchConfigureBy`, refusal-carrying: the checks read first
(`schedControlConfigureAdmitted`) and the state handed to the in-slot write
alone (`schedControlConfigurePerform`), the move of a context homed on another
core among them; a refusal is in the state handed in (`dispatchConfigureByR_eq`). -/
@[inline] def dispatchConfigureByR (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (w : UInt64) (tid : SeLe4n.ThreadId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
  match cap.target with
  | .schedControl core =>
    match decodeSchedContextConfigureArgsCheckedBy (msgRegOfFileThen layout regs w) with
    | .error e => .error (e, st)
    | .ok args =>
      resolveSchedControlConfigureTargetK tid core args.scCPtr st (fun e => .error (e, st))
        (fun vScId =>
        if hCore : core < SeLe4n.Kernel.Concurrency.numCores then
          RefusalCarrying.ofChecked
            (SchedContextOps.schedControlConfigureAdmitted st ⟨core, hCore⟩ vScId args.budget
              args.period args.priority args.deadline args.domain)
            (fun st => SchedContextOps.schedControlConfigurePerform st ⟨core, hCore⟩ vScId
              args.budget args.period args.priority args.deadline args.domain)
            (SchedContextOps.schedControlConfigure ⟨core, hCore⟩ vScId args.budget args.period
              args.priority args.deadline args.domain) st
        else .error (.invalidCapability 0, st))
  | _ => .error (.invalidCapability 0, st)

theorem dispatchConfigureByR_eq (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (w : UInt64) (tid : SeLe4n.ThreadId) (cap : Capability) (st : SystemState) :
    dispatchConfigureByR layout regs w tid cap st =
      RefusalCarrying.ofKernel (dispatchConfigureBy layout regs w tid cap) st := by
  unfold dispatchConfigureByR
  simp only [RefusalCarrying.ofKernel, dispatchConfigureBy]
  cases cap.target with
  | schedControl core =>
    dsimp only
    cases decodeSchedContextConfigureArgsCheckedBy (msgRegOfFileThen layout regs w) with
    | error e => rfl
    | ok args =>
      dsimp only
      rw [resolveSchedControlConfigureTargetK_eq]
      cases resolveSchedControlConfigureTarget tid core args.scCPtr st with
      | error e => rfl
      | ok vScId =>
        dsimp only
        by_cases hCore : core < SeLe4n.Kernel.Concurrency.numCores
        · simp only [dif_pos hCore]
          rw [RefusalCarrying.ofChecked_eq _ _ _ _ (fun hA =>
            SchedContextOps.schedControlConfigure_of_admitted _ _ _ _ _ _ _ _ hA)]
          rfl
        · simp only [dif_neg hCore]
  | _ => rfl

/-- A configure's taint step leaves the state as its arm left it. -/
theorem applySyscallTaintAfter_configure (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (h : decoded.syscallId = .schedContextConfigure)
    (preEpoch : Nat) (preLength : Nat) (preTaint : TaintMap)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength preTaint post =
      post := by
  simp only [applySyscallTaintAfter, syscallTaintPlan, h, contentFlowClass,
    syscallRecordsDeclassification, Bool.false_eq_true, ↓reduceIte, applyOrigination,
    applyTaintFlow, applyTaintClears, applyTaintStep, List.foldl, List.filter]

/-- The configure's arm behind the operand check: the gate's type and right,
then `dispatchConfigureByR`. -/
@[inline] def configureOperandArmR (regs : RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability 0, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
        else if !syscallTargetAccepted .schedContextConfigure st cap then .error (.invalidCapability 0, st)
        else if cap.hasRight (syscallRequiredRight .schedContextConfigure) then
          dispatchConfigureByR SeLe4n.arm64DefaultLayout regs w tid cap st
        else .error (syscallMissingRightError .schedContextConfigure, st)

/-- `dispatchSyscallChecked` for a configure whose fifth word is `w`
(`dispatchConfigureCheckedR_eq`). -/
@[inline] def dispatchConfigureCheckedR (capAddr : SeLe4n.CPtr) (regs : RegisterFile)
    (w : UInt64) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore (configureOperandArmR regs w tid)

theorem dispatchConfigureCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (regs : RegisterFile) (w : UInt64)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .schedContextConfigure)
    (hRegs : MsgRegsAgreeBelow decoded.msgRegs
      (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs) ++ #[(⟨w⟩ : RegValue)]) 5)
    (hLen : 5 ≤ decoded.msgInfo.length) :
    dispatchConfigureCheckedR decoded.capAddr regs w tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  have hNotYield : decoded.syscallId ≠ .yield := by
    rw [hSid]; exact fun h => SyscallId.noConfusion h
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ hNotYield
  intro st tcb ref _ hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel, 
    syscallInvokeTyped, syscallResolveCap, SyscallGate.lookupSlot_mk, hRef,
    applySyscallTaintAfter_configure st tid decoded hSid]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [configureOperandArmR, hSid]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hType : syscallTargetAccepted .schedContextConfigure st cap = false
      · simp only [hIdle, hType, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      replace hType : syscallTargetAccepted .schedContextConfigure st cap = true := by simpa using hType
      by_cases hRight : cap.hasRight (syscallRequiredRight .schedContextConfigure) = true
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [dispatchConfigureByR_eq]
        simp only [RefusalCarrying.ofKernel]
        rw [← dispatchWithCapChecked_eq_configureBy ctx decoded SeLe4n.arm64DefaultLayout regs w
          tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight .schedContextConfigure }
          cap st hSid hRegs hLen]
        rcases dispatchWithCapChecked ctx decoded tid executingCore _ cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]

/-! ## The service register

WS-ZA ZA5.5.  A service register carries five argument words, as a configure
does: the fifth (whether invoking the interface needs the grant right) is
overflow slot 0 of the caller's IPC buffer, read at the entry and handed here
as the word `w`.  Its taint step is the identity and its rights are checked in
the classic order. -/

/-- `dispatchWithCapChecked`'s service-register arm, its arguments read from the
register file `regs` through `layout` and then the overflow word `w`
(`dispatchWithCapChecked_eq_serviceRegisterBy`). -/
@[inline] def dispatchServiceRegisterBy (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (w : UInt64) (cap : Capability)
    (st : SystemState) : Except KernelError (Unit × SystemState) :=
  match cap.target with
  | .object epId =>
    match decodeServiceRegisterArgsBy (msgRegOfFileThen layout regs w) with
    | .error e => .error e
    | .ok args =>
      registerServiceChecked ctx tid
        { iface := { ifaceId := args.interfaceId, methodCount := args.methodCount
                     maxMessageSize := args.maxMessageSize
                     maxResponseSize := args.maxResponseSize
                     requiresGrant := args.requiresGrant }
          endpointCap := cap } st
  | _ => .error (.invalidCapability 0)

theorem dispatchWithCapChecked_eq_serviceRegisterBy (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (w : UInt64) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState)
    (h : decoded.syscallId = .serviceRegister)
    (hRegs : MsgRegsAgreeBelow decoded.msgRegs
      (layout.msgRegs.map (readReg regs) ++ #[(⟨w⟩ : RegValue)]) 5)
    (hLen : 5 ≤ decoded.msgInfo.length) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      dispatchServiceRegisterBy ctx tid layout regs w cap st := by
  have hDec := decodeServiceRegisterArgs_eq_by layout regs w decoded hRegs hLen
  rcases decoded with ⟨capAddr, msgInfo, sid, msgRegs, inlineCount, overflowCount⟩
  rcases cap with ⟨target, rights, badge, mapping⟩
  simp only at h
  subst h
  cases target <;>
    simp only [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchServiceRegisterBy, hDec]
  all_goals rfl

/-- `dispatchServiceRegisterBy`, refusal-carrying: the checks read first (the
flow check and `registerServiceAdmitted`) and the state handed to the write
alone (`registerServicePerform`); a refusal is in the state handed in
(`dispatchServiceRegisterByR_eq`). -/
@[inline] def dispatchServiceRegisterByR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (w : UInt64) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
  match cap.target with
  | .object epId =>
    match decodeServiceRegisterArgsBy (msgRegOfFileThen layout regs w) with
    | .error e => .error (e, st)
    | .ok args =>
      let reg : ServiceRegistration :=
        { iface := { ifaceId := args.interfaceId, methodCount := args.methodCount
                     maxMessageSize := args.maxMessageSize
                     maxResponseSize := args.maxResponseSize
                     requiresGrant := args.requiresGrant }
          endpointCap := cap }
      RefusalCarrying.ofChecked
        (registrationWriteAdmitted ctx tid reg && registerServiceAdmitted st reg)
        (fun st => registerServicePerform st reg)
        (registerServiceChecked ctx tid reg) st
  | _ => .error (.invalidCapability 0, st)

theorem dispatchServiceRegisterByR_eq (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (w : UInt64) (cap : Capability)
    (st : SystemState) :
    dispatchServiceRegisterByR ctx tid layout regs w cap st =
      RefusalCarrying.ofKernel (dispatchServiceRegisterBy ctx tid layout regs w cap) st := by
  unfold dispatchServiceRegisterByR dispatchServiceRegisterBy
  cases cap.target with
  | object epId =>
    dsimp only
    cases decodeServiceRegisterArgsBy (msgRegOfFileThen layout regs w) with
    | error e => rfl
    | ok args =>
      dsimp only
      apply RefusalCarrying.ofChecked_eq
      intro hA
      exact registerServiceChecked_of_admitted _ _ _ _ hA
  | _ => rfl

/-- **WS-ZA ZA5.9**: the service record a register writes, built from the
decoded words and the invoked capability — `EndpointService.ofRegistration` of
the registration the arm names (`serviceRecordOfWords_eq`), read field by field
so no registration record is built. -/
@[inline] def serviceRecordOfWords (ifaceId : SeLe4n.InterfaceId)
    (methodCount maxMessageSize maxResponseSize : Nat) (requiresGrant : Bool)
    (cap : Capability) : EndpointService :=
  { registered := true, interfaceId := ifaceId, methodCount := methodCount,
    maxMessageSize := maxMessageSize, maxResponseSize := maxResponseSize,
    requiresGrant := requiresGrant, capRights := cap.rights,
    capBadgeWord := cap.badgeWord, capBadged := cap.badged, capMapAsid := cap.mapAsid,
    capMapVaddr := cap.mapVaddr, capMapEpoch := cap.mapEpoch, capMapped := cap.mapped,
    capFreeIndex := cap.freeIndex }

/-- **WS-ZA ZA5.9**: the compiled register write — the endpoint's record set in
its slot from the decoded words (`registerServicePerformImpl` of the arm's
registration, `registerServiceWordsPerform_eq`). -/
def registerServiceWordsPerform (st : SystemState) (epId : SeLe4n.ObjId)
    (ifaceId : SeLe4n.InterfaceId) (methodCount maxMessageSize maxResponseSize : Nat)
    (requiresGrant : Bool) (cap : Capability) : SystemState :=
  match st.getEndpoint? epId with
  | some _ => st.modifyObject epId (setServiceObject
      (serviceRecordOfWords ifaceId methodCount maxMessageSize maxResponseSize requiresGrant cap))
  | none => st

/-- **The register's refusal, on its words**: `0` when every check of
`registerServiceChecked` passes on the endpoint `epId` the capability names,
otherwise the first that fails, in its order — the flow (`1`), a registration
already recorded (`2`), an unknown interface (`3`), the endpoint's write right
(`4`), the endpoint already registered (`2`), no endpoint there (`5`).  Read off
the decoded words and the capability, so no registration is built
(`registerServiceRefusalError`, `dispatchServiceRegisterByR_eq_impl`). -/
@[inline] def registerServiceRefusalCode (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (ifaceId : SeLe4n.InterfaceId) (cap : Capability)
    (st : SystemState) : Nat :=
  if !serviceEndpointWriteAdmitted ctx tid epId then 1
  else if recordedRegistrationPresent st
      (SeLe4n.ObjId.ofNat (ServiceId.ofNat epId.toNat).toNat) then 2
  else if (st.interfaceRegistry[ifaceId]?).isNone then 3
  else
    match st.getObject? epId with
    | some (.endpoint ep) =>
      if !Capability.hasRight cap .write then 4
      else if ep.serviceRegistered then 2
      else 0
    | _ => 5

/-- The error a register's refusal code names. -/
@[inline] def registerServiceRefusalError (code : Nat) : KernelError :=
  if code = 1 then .flowDenied
  else if code = 2 then .illegalState
  else if code = 3 then .objectNotFound
  else if code = 4 then .illegalAuthority
  else (.invalidCapability 0)

/-- A register the checks refuse is refused with the error its code names. -/
theorem registerServiceChecked_refused (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (reg : ServiceRegistration) (epId : SeLe4n.ObjId) (st : SystemState)
    (hT : reg.endpointCap.target = .object epId)
    (hA : (registrationWriteAdmitted ctx tid reg && registerServiceAdmitted st reg) = false) :
    registerServiceChecked ctx tid reg st =
      .error (registerServiceRefusalError
        (registerServiceRefusalCode ctx tid epId reg.iface.ifaceId reg.endpointCap st)) := by
  have hSid : reg.sid = ServiceId.ofNat epId.toNat := by
    simp only [ServiceRegistration.sid, hT]
  unfold registerServiceChecked registerService registerServiceRefusalCode registrationWriteAdmitted
  unfold registrationWriteAdmitted registerServiceAdmitted at hA
  simp only [hT, hSid] at hA ⊢
  cases hF : serviceEndpointWriteAdmitted ctx tid epId
  · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true, registerServiceRefusalError]
  simp only [hF, Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hA ⊢
  cases hR : recordedRegistrationPresent st (SeLe4n.ObjId.ofNat (ServiceId.ofNat epId.toNat).toNat)
  · simp only [hR, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte] at hA ⊢
    cases hI : st.interfaceRegistry[reg.iface.ifaceId]?
    · simp only [Option.isNone_none, ↓reduceIte, registerServiceRefusalError]; rfl
    simp only [hI, Option.isSome_some, Option.isNone_some, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte, reduceCtorEq] at hA ⊢
    split
    · next hO => simp only [hO, registerServiceRefusalError]; rfl
    · next ep hO =>
      simp only [hO] at hA ⊢
      cases hW : reg.endpointCap.hasRight .write <;> cases hS : ep.serviceRegistered <;>
        simp only [hW, hS, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and,
          Bool.and_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
          registerServiceRefusalError] at hA ⊢ <;> first | rfl | exact absurd hA (by decide)
    · next val hNe hO =>
      split
      · next ep hE =>
        rw [hO] at hE
        exact absurd (Option.some.inj hE) (hNe ep)
      · rfl
  · simp only [↓reduceIte, registerServiceRefusalError]; rfl

/-- **WS-ZA ZA5.9: the register arm as compiled** — its checks read off the
decoded words and the invoked capability, and its write
`registerServiceWordsPerform`, and its refusal read off the same words
(`registerServiceRefusalCode`), so the arm builds no registration.  Equal
to `dispatchServiceRegisterByR` (`dispatchServiceRegisterByR_eq_impl`). -/
@[inline] def dispatchServiceRegisterByRImpl (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (w : UInt64) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
  match cap.target with
  | .object epId =>
    match decodeServiceRegisterArgsBy (msgRegOfFileThen layout regs w) with
    | .error e => .error (e, st)
    | .ok args =>
      if serviceEndpointWriteAdmitted ctx tid epId &&
          (!recordedRegistrationPresent st
              (SeLe4n.ObjId.ofNat (ServiceId.ofNat epId.toNat).toNat) &&
            (st.interfaceRegistry[args.interfaceId]?).isSome &&
            match st.getObject? epId with
            | some (.endpoint ep) => Capability.hasRight cap .write && !ep.serviceRegistered
            | _ => false) then
        .ok ((), registerServiceWordsPerform st epId args.interfaceId args.methodCount
          args.maxMessageSize args.maxResponseSize args.requiresGrant cap)
      else
        .error (registerServiceRefusalError
          (registerServiceRefusalCode ctx tid epId args.interfaceId cap st), st)
  | _ => .error (.invalidCapability 0, st)

@[csimp] theorem dispatchServiceRegisterByR_eq_impl :
    @dispatchServiceRegisterByR = @dispatchServiceRegisterByRImpl := by
  funext ctx tid layout regs w cap st
  unfold dispatchServiceRegisterByR dispatchServiceRegisterByRImpl RefusalCarrying.ofChecked
  rcases cap with ⟨target, rights, badge, badged, mAsid, mVaddr, mEpoch, mapped, freeIndex,
    cnGuard, cnGuardSize⟩
  cases target with
  | object epId =>
    dsimp only
    cases decodeServiceRegisterArgsBy (msgRegOfFileThen layout regs w) with
    | error e => rfl
    | ok args =>
      dsimp only
      simp only [registerServicePerform_eq_impl]
      let cap : Capability := ⟨.object epId, rights, badge, badged, mAsid, mVaddr, mEpoch, mapped,
        freeIndex, cnGuard, cnGuardSize⟩
      let reg : ServiceRegistration :=
        { iface := { ifaceId := args.interfaceId, methodCount := args.methodCount
                     maxMessageSize := args.maxMessageSize
                     maxResponseSize := args.maxResponseSize
                     requiresGrant := args.requiresGrant }
          endpointCap := cap }
      have hC : (registrationWriteAdmitted ctx tid reg && registerServiceAdmitted st reg) =
          (serviceEndpointWriteAdmitted ctx tid epId &&
            (!recordedRegistrationPresent st
                (SeLe4n.ObjId.ofNat (ServiceId.ofNat epId.toNat).toNat) &&
              (st.interfaceRegistry[args.interfaceId]?).isSome &&
              match st.getObject? epId with
              | some (.endpoint ep) => Capability.hasRight cap .write && !ep.serviceRegistered
              | _ => false)) := rfl
      change (if (registrationWriteAdmitted ctx tid reg && registerServiceAdmitted st reg) = true
        then _ else _) = _
      rw [hC]
      by_cases hA : (serviceEndpointWriteAdmitted ctx tid epId &&
            (!recordedRegistrationPresent st
                (SeLe4n.ObjId.ofNat (ServiceId.ofNat epId.toNat).toNat) &&
              (st.interfaceRegistry[args.interfaceId]?).isSome &&
              match st.getObject? epId with
              | some (.endpoint ep) => Capability.hasRight cap .write && !ep.serviceRegistered
              | _ => false)) = true
      · rw [if_pos hA, if_pos hA]; rfl
      · rw [if_neg hA, if_neg hA,
          registerServiceChecked_refused ctx tid reg epId st rfl (by rw [hC]; simpa using hA)]
  | _ => rfl

/-- A service register's taint step leaves the state as its arm left it. -/
theorem applySyscallTaintAfter_serviceRegister (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (h : decoded.syscallId = .serviceRegister)
    (preEpoch : Nat) (preLength : Nat) (preTaint : TaintMap)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength preTaint post =
      post := by
  simp only [applySyscallTaintAfter, syscallTaintPlan, h, contentFlowClass,
    syscallRecordsDeclassification, Bool.false_eq_true, ↓reduceIte, applyOrigination,
    applyTaintFlow, applyTaintClears, applyTaintStep, List.foldl, List.filter]

/-- The service register's arm behind the operand check: the gate's type and
right, then `dispatchServiceRegisterByR`. -/
@[inline] def serviceRegisterOperandArmR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (regs : RegisterFile) (w : UInt64) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability 0, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
        else if !syscallTargetAccepted .serviceRegister st cap then .error (.invalidCapability 0, st)
        else if cap.hasRight (syscallRequiredRight .serviceRegister) then
          dispatchServiceRegisterByR ctx tid SeLe4n.arm64DefaultLayout regs w cap st
        else .error (syscallMissingRightError .serviceRegister, st)

/-- `dispatchSyscallChecked` for a service register whose fifth word is `w`
(`dispatchServiceRegisterCheckedR_eq`). -/
@[inline] def dispatchServiceRegisterCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (regs : RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore (serviceRegisterOperandArmR ctx tid regs w)

theorem dispatchServiceRegisterCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (regs : RegisterFile) (w : UInt64)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .serviceRegister)
    (hRegs : MsgRegsAgreeBelow decoded.msgRegs
      (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs) ++ #[(⟨w⟩ : RegValue)]) 5)
    (hLen : 5 ≤ decoded.msgInfo.length) :
    dispatchServiceRegisterCheckedR ctx decoded.capAddr regs w tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  have hNotYield : decoded.syscallId ≠ .yield := by
    rw [hSid]; exact fun h => SyscallId.noConfusion h
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ hNotYield
  intro st tcb ref _ hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel, 
    syscallInvokeTyped, syscallResolveCap, SyscallGate.lookupSlot_mk, hRef,
    applySyscallTaintAfter_serviceRegister st tid decoded hSid]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [serviceRegisterOperandArmR, hSid]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hType : syscallTargetAccepted .serviceRegister st cap = false
      · simp only [hIdle, hType, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      replace hType : syscallTargetAccepted .serviceRegister st cap = true := by simpa using hType
      by_cases hRight : cap.hasRight (syscallRequiredRight .serviceRegister) = true
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [dispatchServiceRegisterByR_eq]
        simp only [RefusalCarrying.ofKernel]
        rw [← dispatchWithCapChecked_eq_serviceRegisterBy ctx decoded SeLe4n.arm64DefaultLayout
          regs w tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight .serviceRegister }
          cap st hSid hRegs hLen]
        rcases dispatchWithCapChecked ctx decoded tid executingCore _ cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]

/-! ## The CNode mint

A CNode mint carries five argument words: a copy's four (the two slots' index
and depth, and the rights mask) and the badge, overflow slot 0 of the caller's
IPC buffer, read at the entry and handed here as the word `w`.  Its taint step
is the identity and its rights are checked in the classic order.  The rights
are the request masked by the source capability's (`mintMaskedRights`, seL4's
`maskCapRights`), so a mint never refuses a mask. -/

/-- `dispatchWithCapChecked`'s CNode-mint arm, its arguments read from the
register file `regs` through `layout` and then the overflow word `w`
(`dispatchWithCapChecked_eq_mintBy`). -/
@[inline] def dispatchMintBy (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (w : UInt64) (cap : Capability)
    (st : SystemState) : Except KernelError (Unit × SystemState) :=
  match cap.target with
  | .object cnodeId =>
    match decodeCSpaceMintArgsBy (msgRegOfFileThen layout regs w) with
    | .error e => .error e
    | .ok args =>
      if !cnodeInvoked cnodeId st then .error .objectNotFound else
      match resolveCNodeOpSlots tid cap args.destIndex args.destDepth args.srcRoot
          args.srcIndex args.srcDepth st with
      | .error e => .error e
      | .ok (src, dst) =>
        let badge : Option SeLe4n.Badge :=
          if args.badge.word = 0 then none else some args.badge
        cspaceMintChecked ctx src dst (mintMaskedRights st src args.rights) badge st
  | _ => .error (.invalidCapability 0)

theorem dispatchWithCapChecked_eq_mintBy (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (w : UInt64) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState)
    (h : decoded.syscallId = .cspaceMint)
    (hRegs : MsgRegsAgreeBelow decoded.msgRegs
      (layout.msgRegs.map (readReg regs) ++ #[(⟨w⟩ : RegValue)]) 5)
    (hLen : 5 ≤ decoded.msgInfo.length) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      dispatchMintBy ctx tid layout regs w cap st := by
  have hDec := decodeCSpaceMintArgs_eq_by layout regs w decoded hRegs hLen
  rcases decoded with ⟨capAddr, msgInfo, sid, msgRegs, inlineCount, overflowCount⟩
  rcases cap with ⟨target, rights, badge, mapping⟩
  simp only at h
  subst h
  cases target <;>
    simp only [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchMintBy, hDec]
  all_goals rfl

/-- `dispatchMintBy`, refusal-carrying: the slots resolved, then the checks read
first (the flow check and `cspaceMintAdmittedAt`) and the state handed to the
write alone (`cspaceMintPerformAt`); a refusal is in the state handed in
(`dispatchMintByR_eq`). -/
@[inline] def dispatchMintByR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (w : UInt64) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
  match cap.target with
  | .object cnodeId =>
    match decodeCSpaceMintArgsBy (msgRegOfFileThen layout regs w) with
    | .error e => .error (e, st)
    | .ok args =>
      if !cnodeInvoked cnodeId st then .error (.objectNotFound, st) else
      resolveCNodeOpSlotsK tid cap args.destIndex args.destDepth args.srcRoot
        args.srcIndex args.srcDepth st
        (fun e => .error (e, st))
        (fun srcCNode srcSlot dstCNode dstSlot =>
          if securityFlowsTo (ctx.objectLabelOf srcCNode) (ctx.objectLabelOf dstCNode) &&
              cspaceMintDataRefused ⟨srcCNode, srcSlot⟩
                (mintMaskedRights st ⟨srcCNode, srcSlot⟩ args.rights) args.badge.word st
          then .error (.illegalState, st) else
          RefusalCarrying.ofChecked
            (securityFlowsTo (ctx.objectLabelOf srcCNode) (ctx.objectLabelOf dstCNode) &&
              cspaceMintAdmittedAt srcCNode srcSlot dstCNode dstSlot
                (mintMaskedRights st ⟨srcCNode, srcSlot⟩ args.rights) args.badge st)
            (fun st' => cspaceMintPerformAt srcCNode srcSlot dstCNode dstSlot
                (mintMaskedRights st ⟨srcCNode, srcSlot⟩ args.rights) args.badge st')
            (dispatchMintBy ctx tid layout regs w cap) st)
  | _ => .error (.invalidCapability 0, st)

theorem dispatchMintByR_eq (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (w : UInt64) (cap : Capability)
    (st : SystemState) :
    dispatchMintByR ctx tid layout regs w cap st =
      RefusalCarrying.ofKernel (dispatchMintBy ctx tid layout regs w cap) st := by
  unfold dispatchMintByR
  cases hT : cap.target with
  | object cnodeId =>
    dsimp only
    cases hD : decodeCSpaceMintArgsBy (msgRegOfFileThen layout regs w) with
    | error e => simp [RefusalCarrying.ofKernel, dispatchMintBy, hT, hD]
    | ok args =>
      dsimp only
      rw [resolveCNodeOpSlotsK_eq]
      cases hR : resolveCNodeOpSlots tid cap args.destIndex args.destDepth args.srcRoot
          args.srcIndex args.srcDepth st with
      | error e =>
        simp only [RefusalCarrying.ofKernel, dispatchMintBy, hT, hD, hR]
        cases cnodeInvoked cnodeId st <;> rfl
      | ok p =>
        obtain ⟨⟨sc, ss⟩, ⟨dc, ds⟩⟩ := p
        dsimp only [cspaceMintAdmittedAt, cspaceMintPerformAt]
        rw [show cnodeInvoked cnodeId st = true from
          cnodeInvoked_of_resolveCNodeOpSlots_ok hR hT]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases hRef : (securityFlowsTo (ctx.objectLabelOf sc) (ctx.objectLabelOf dc) &&
            cspaceMintDataRefused ⟨sc, ss⟩ (mintMaskedRights st ⟨sc, ss⟩ args.rights)
              args.badge.word st) = true
        · rw [if_pos hRef]
          simp only [Bool.and_eq_true] at hRef
          have hR2 := hRef.2
          rw [← mintDataWord_ofRegister] at hR2
          simp only [RefusalCarrying.ofKernel, dispatchMintBy, hT, hD, cspaceMintChecked,
            hRef.1, ↓reduceIte, cnodeInvoked, cnodeInvoked_of_resolveCNodeOpSlots_ok hR hT, hR,
            Bool.not_true, Bool.false_eq_true, cspaceMintWithCdt_of_dataRefused hR2]
        rw [if_neg hRef]
        apply RefusalCarrying.ofChecked_eq
        intro hA
        simp only [Bool.and_eq_true] at hA
        have hA2 := hA.2
        rw [← mintDataWord_ofRegister] at hA2
        simp only [dispatchMintBy, hT, hD, cspaceMintChecked, hA.1, ↓reduceIte, cnodeInvoked,
          cnodeInvoked_of_resolveCNodeOpSlots_ok hR hT, hR, Bool.not_true, Bool.false_eq_true,
          cspaceMintWithCdt_of_admitted hA2]
  | _ => simp [RefusalCarrying.ofKernel, dispatchMintBy, hT]

/-- A CNode mint's taint step leaves the state as its arm left it. -/
theorem applySyscallTaintAfter_cspaceMint (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (h : decoded.syscallId = .cspaceMint)
    (preEpoch : Nat) (preLength : Nat) (preTaint : TaintMap)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength preTaint post =
      post := by
  simp only [applySyscallTaintAfter, syscallTaintPlan, h, contentFlowClass,
    syscallRecordsDeclassification, Bool.false_eq_true, ↓reduceIte, applyOrigination,
    applyTaintFlow, applyTaintClears, applyTaintStep, List.foldl, List.filter]

/-- The CNode mint's arm behind the operand check: the gate's type and right,
then `dispatchMintByR`. -/
@[inline] def mintOperandArmR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (regs : RegisterFile) (w : UInt64) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability 0, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
        else if !syscallTargetAccepted .cspaceMint st cap then .error (.invalidCapability 0, st)
        else if cap.hasRight (syscallRequiredRight .cspaceMint) then
          dispatchMintByR ctx tid SeLe4n.arm64DefaultLayout regs w cap st
        else .error (syscallMissingRightError .cspaceMint, st)

/-- `dispatchSyscallChecked` for a CNode mint whose fifth word is `w`
(`dispatchMintCheckedR_eq`). -/
@[inline] def dispatchMintCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (regs : RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore (mintOperandArmR ctx tid regs w)

theorem dispatchMintCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (regs : RegisterFile) (w : UInt64)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .cspaceMint)
    (hRegs : MsgRegsAgreeBelow decoded.msgRegs
      (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs) ++ #[(⟨w⟩ : RegValue)]) 5)
    (hLen : 5 ≤ decoded.msgInfo.length) :
    dispatchMintCheckedR ctx decoded.capAddr regs w tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  have hNotYield : decoded.syscallId ≠ .yield := by
    rw [hSid]; exact fun h => SyscallId.noConfusion h
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ hNotYield
  intro st tcb ref _ hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    syscallInvokeTyped, syscallResolveCap, SyscallGate.lookupSlot_mk, hRef,
    applySyscallTaintAfter_cspaceMint st tid decoded hSid]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [mintOperandArmR, hSid]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hType : syscallTargetAccepted .cspaceMint st cap = false
      · simp only [hIdle, hType, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      replace hType : syscallTargetAccepted .cspaceMint st cap = true := by simpa using hType
      by_cases hRight : cap.hasRight (syscallRequiredRight .cspaceMint) = true
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [dispatchMintByR_eq]
        simp only [RefusalCarrying.ofKernel]
        rw [← dispatchWithCapChecked_eq_mintBy ctx decoded SeLe4n.arm64DefaultLayout
          regs w tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight .cspaceMint }
          cap st hSid hRegs hLen]
        rcases dispatchWithCapChecked ctx decoded tid executingCore _ cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]

/-! ## The one-overflow-word invocations

The register route's `overflowOne` arm names one of `routedOverflowOne`: the
configure, the service register or the CNode mint, each with its fifth word
`w`. -/

/-- `dispatchSyscallChecked` for a one-overflow-word invocation `sid` whose
fifth word is `w` (`dispatchOverflowOneCheckedR_eq`).  The last arm is never
taken: the route names only `routedOverflowOne` calls. -/
@[inline] def dispatchOverflowOneCheckedR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (regs : RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  match sid with
  | .schedContextConfigure => dispatchConfigureCheckedR capAddr regs w tid executingCore
  | .serviceRegister => dispatchServiceRegisterCheckedR ctx capAddr regs w tid executingCore
  | .cspaceMint => dispatchMintCheckedR ctx capAddr regs w tid executingCore
  | _ => fun st => .error (.illegalState, st)

theorem dispatchOverflowOneCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (regs : RegisterFile) (w : UInt64)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hR : Architecture.RegisterDecode.routedOverflowOne decoded.syscallId = true)
    (hRegs : MsgRegsAgreeBelow decoded.msgRegs
      (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs) ++ #[(⟨w⟩ : RegValue)]) 5)
    (hLen : 5 ≤ decoded.msgInfo.length) :
    dispatchOverflowOneCheckedR ctx decoded.syscallId decoded.capAddr regs w tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  cases hSid : decoded.syscallId <;> rw [hSid] at hR <;>
    first
    | (cases hR; done)
    | exact dispatchConfigureCheckedR_eq ctx decoded regs w tid executingCore hSid hRegs hLen
    | exact dispatchServiceRegisterCheckedR_eq ctx decoded regs w tid executingCore hSid hRegs hLen
    | exact dispatchMintCheckedR_eq ctx decoded regs w tid executingCore hSid hRegs hLen

end SeLe4n.Kernel
