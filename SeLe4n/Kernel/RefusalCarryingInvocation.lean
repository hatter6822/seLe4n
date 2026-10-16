-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingDispatch

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
checks its rights in the classic order.  The invocations outside the set keep
the general path: the in-place retype (its taint step clears provenance), the
scheduling-context configure and service register (a fifth argument word), and
the declassification and audit calls.
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
  | .cspaceMint =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceMintArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            let badge : Option SeLe4n.Badge :=
              if args.badge.val = 0 then none else some args.badge
            cspaceMintChecked ctx src dst args.rights badge st
    | _ => .error .invalidCapability
  | .cspaceCopy =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceCopyArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            cspaceCopyChecked ctx src dst st
    | _ => .error .invalidCapability
  | .cspaceMove =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceMoveArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            cspaceMoveChecked ctx src dst st
    | _ => .error .invalidCapability
  | .cspaceDelete =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceDeleteArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
            cspaceDeleteSlotFinalising executingCore addr st
    | _ => .error .invalidCapability
  | .cspaceRevoke =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceDeleteArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
            cspaceRevokeCdtFinalising executingCore addr st
    | _ => .error .invalidCapability
  | .mintReplyCap =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceCopyArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            mintReplyCapWithCdt src dst st
    | _ => .error .invalidCapability
  | .untypedRetype =>
    match cap.target with
    | .object _ => untypedRetypeFromCap tid capAddr (decodeUntypedRetypeArgsBy (msgRegOfFile layout regs)) st
    | _ => .error .invalidCapability
  | .untypedReset =>
    match cap.target with
    | .object untypedId =>
        untypedResetWithShootdown executingCore untypedId st
    | _ => .error .invalidCapability
  | .vspaceMap =>
    match cap.target with
    | .object _ =>
          match decodeVSpaceMapArgsBy (msgRegOfFile layout regs) st.machine.maxASID with
          | .error e => .error e
          | .ok args =>
            if !vspaceCapAuthorizesAsid cap args.asid st then
              .error .illegalAuthority
            else
              vspaceMapFromFrameCap tid executingCore args st
    | _ => .error .invalidCapability
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
    | _ => .error .invalidCapability
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
    | _ => .error .invalidCapability
  | .serviceRevoke =>
    match cap.target with
    | .object _ =>
      match decodeServiceRevokeArgsBy (msgRegOfFile layout regs) with
      | .error e => .error e
      | .ok args => revokeService args.targetService st
    | _ => .error .invalidCapability
  | .serviceQuery =>
    match cap.target with
    | .object epId =>
        match lookupServiceByCap epId st with
        | .ok (reg, st') =>
            .ok ((), Architecture.writeReturnFrameToTcb st' tid
              (Architecture.returnFrameOfWord reg.sid.val.toUInt64))
        | .error e => .error e
    | _ => .error .invalidCapability
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
    | _ => .error .invalidCapability
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
    | _ => .error .invalidCapability
  | .tcbBindNotification =>
    match cap.target with
    | .object tcbObjId =>
      match decodeTcbBindNotificationArgsBy (msgRegOfFile layout regs) with
      | .error e => .error e
      | .ok args =>
          match st.getTcb? tid with
          | some callerTcb =>
            match st.getCNode? callerTcb.cspaceRoot with
            | some rootCn =>
              let ntfnGate : SyscallGate := {
                callerId      := tid
                cspaceRoot    := callerTcb.cspaceRoot
                capAddr       := args.notificationCPtr
                capDepth      := rootCn.depth
                requiredRight := .write
              }
              match syscallLookupCap ntfnGate st with
              | .error e => .error e
              | .ok (ntfnCap, _) =>
                match ntfnCap.target with
                | .object notifId =>
                    bindNotification notifId (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st
                | _ => .error .invalidCapability
            | none => .error .invalidCapability
          | none => .error .objectNotFound
    | _ => .error .invalidCapability
  | .tcbUnbindNotification =>
    match cap.target with
    | .object tcbObjId =>
        match unbindNotification (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st with
        | .error e => .error e
        | .ok ((), st') => .ok ((), st')
    | _ => .error .invalidCapability
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
    | _ => .error .invalidCapability
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
    | _ => .error .invalidCapability
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
    | _ => .error .invalidCapability
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
    | _ => .error .invalidCapability
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
    | _ => .error .invalidCapability
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
    | _ => .error .invalidCapability
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
    | _ => .error .invalidCapability
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
            | .ok (cnId, vrId) =>
                match setThreadSpace st vtid cnId vrId with
                | .ok st' => .ok ((), st')
                | .error e => .error e
    | _ => .error .invalidCapability
  | .pageTableMap =>
    match cap.target with
    | .object objId =>
      match decodePageTableMapArgsBy (msgRegOfFile layout regs) with
      | .error e => .error e
      | .ok args =>
          match resolveCallerCapObject tid args.vspaceRoot .write st with
          | .error e => .error e
          | .ok (_, rootId) => Architecture.pageTableMap objId rootId args.vaddr st
    | _ => .error .invalidCapability
  | .pageTableUnmap =>
    match cap.target with
    | .object objId => Architecture.pageTableUnmap objId st
    | _ => .error .invalidCapability
  | _ => .error .illegalState

/-- What routing an invocation rests on: it is inert, records no
declassification, checks its rights in the classic order, and is not the yield. -/
theorem routedInvocation_classic (sid : SyscallId) (h : routedInvocation sid = true) :
    contentFlowClass sid = .inert ∧ syscallRecordsDeclassification sid = false ∧
      syscallChecksTargetFirst sid = false ∧ sid ≠ .yield := by
  cases sid <;> simp only [routedInvocation, Bool.false_eq_true] at h <;>
    exact ⟨rfl, rfl, rfl, fun h => SyscallId.noConfusion h⟩

/-- A routed invocation's taint step leaves the state as its arm left it. -/
theorem applySyscallTaintAfter_routed (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (h : routedInvocation decoded.syscallId = true)
    (preEpoch : Nat) (preLog : DeclassificationAuditLog) (preTaint : TaintTable)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLog preTaint post =
      post := by
  obtain ⟨hC, hR, -, -⟩ := routedInvocation_classic _ h
  simp only [applySyscallTaintAfter, syscallTaintPlan, hC, hR, Bool.false_eq_true,
    ↓reduceIte, applyOrigination, applyTaintFlow, applyTaintClears, List.foldl,
    List.filter]

/-- `dispatchWithCapChecked` at a routed invocation whose message registers are
the layout's, read from the file, is `dispatchInvocationBy` reading the file. -/
theorem dispatchWithCapChecked_eq_invocationBy (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (st : SystemState) (h : routedInvocation decoded.syscallId = true)
    (hRegs : decoded.msgRegs = layout.msgRegs.map (readReg regs)) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      dispatchInvocationBy ctx decoded.syscallId decoded.capAddr
        layout regs tid executingCore cap st := by
  have hMint := decodeCSpaceMintArgs_eq_by layout regs decoded hRegs
  have hCopy := decodeCSpaceCopyArgs_eq_by layout regs decoded hRegs
  have hMove := decodeCSpaceMoveArgs_eq_by layout regs decoded hRegs
  have hDelete := decodeCSpaceDeleteArgs_eq_by layout regs decoded hRegs
  have hRetype := decodeUntypedRetypeArgs_eq_by layout regs decoded hRegs
  have hMap := decodeVSpaceMapArgs_eq_by layout regs decoded st.machine.maxASID hRegs
  have hUnmap := decodeVSpaceUnmapArgs_eq_by layout regs decoded st.machine.maxASID hRegs
  have hRevoke := decodeServiceRevokeArgs_eq_by layout regs decoded hRegs
  have hScBind := decodeSchedContextBindArgs_eq_by layout regs decoded hRegs
  have hNtfn := decodeTcbBindNotificationArgs_eq_by layout regs decoded hRegs
  have hPrio := decodeSetPriorityArgs_eq_by layout regs decoded hRegs
  have hMcp := decodeSetMCPriorityArgs_eq_by layout regs decoded hRegs
  have hIpcBuf := decodeSetIPCBufferArgs_eq_by layout regs decoded hRegs
  have hAff := decodeSetAffinityArgs_eq_by layout regs decoded hRegs
  have hFault := decodeSetFaultHandlerArgs_eq_by layout regs decoded hRegs
  have hSpace := decodeSetSpaceArgs_eq_by layout regs decoded hRegs
  have hPt := decodePageTableMapArgs_eq_by layout regs decoded hRegs
  rcases decoded with ⟨capAddr, msgInfo, sid, msgRegs, capRecvSlot, inlineCount, overflowCount⟩
  rcases cap with ⟨target, rights, badge, mapping⟩
  cases sid <;> simp only [routedInvocation, Bool.false_eq_true] at h <;>
    cases target <;>
    simp only [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchInvocationBy, hMint,
      hCopy, hMove, hDelete, hRetype, hMap, hUnmap, hRevoke, hScBind, hNtfn, hPrio, hMcp,
      hIpcBuf, hAff, hFault, hSpace, hPt, decodeVSpaceUnifyInstructionArgs]
  all_goals rfl

/-- WS-ZA ZA5.2: an admitted resume carries no fault, so answering one first is
the identity. -/
theorem retirePendingFaultForResume_of_resumeAdmitted {st : SystemState}
    {tid : SeLe4n.ThreadId} (h : Lifecycle.Suspend.resumeAdmitted st tid = true) :
    retirePendingFaultForResume st tid = st := by
  unfold Lifecycle.Suspend.resumeAdmitted at h
  unfold retirePendingFaultForResume
  cases hT : st.getTcb? tid with
  | none => rfl
  | some tcb =>
    rw [hT] at h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    simp only [h.1]

/-- WS-ZA ZA5.2: `dispatchInvocationBy`, refusal-carrying, with each arm whose
write has been split into its checks and its in-slot write
(`RefusalCarrying.ofChecked`) reading the checks first and handing the state to
the write alone.  An arm whose checks refuse, and every arm not yet split, is
`ofKernel` of `dispatchInvocationBy`, whose refusal precedes any write
(`dispatchInvocationByR_eq`). -/
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
            RefusalCarrying.ofChecked
              (SchedContext.PriorityManagement.setPriorityAdmitted st vCallerTid vTargetTid
                (Priority.ofNat args.newPriority) executingCore)
              (fun st => SchedContext.PriorityManagement.setPriorityPerform st vTargetTid.val
                (Priority.ofNat args.newPriority) executingCore)
              (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
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
            RefusalCarrying.ofChecked
              (SchedContext.PriorityManagement.setMCPriorityAdmitted st vCallerTid vTargetTid
                (Priority.ofNat args.newMCP))
              (fun st => st.updateTcb vTargetTid.val
                (fun t => { t with maxControlledPriority := Priority.ofNat args.newMCP }))
              (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
  | .tcbSetIPCBuffer =>
    match cap.target with
    | .object objId =>
      match decodeSetIPCBufferArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error (e, st)
        | .ok vtid =>
          RefusalCarrying.ofChecked
            (Architecture.IpcBufferValidation.setIPCBufferAdmitted st vtid args.bufferAddr)
            (fun st => st.updateTcb vtid.val (fun t => { t with ipcBuffer := args.bufferAddr }))
            (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
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
              RefusalCarrying.ofChecked (setAffinityAdmitted st vtid.val affinity)
                (fun st => setAffinityPerform st vtid.val affinity)
                (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
            (fun e => .error (e, st))
    | _ => .error (.invalidCapability, st)
  | .tcbSuspend =>
    match cap.target with
    | .object objId =>
      match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
      | .error e => .error (e, st)
      | .ok vtid =>
        RefusalCarrying.ofChecked (Lifecycle.Suspend.suspendAdmitted st vtid.val)
          (fun st => Lifecycle.Suspend.suspendPerform st vtid executingCore)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
  | .tcbResume =>
    match cap.target with
    | .object objId =>
      match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
      | .error e => .error (e, st)
      | .ok vtid =>
        RefusalCarrying.ofChecked (Lifecycle.Suspend.resumeAdmitted st vtid.val)
          (fun st => Lifecycle.Suspend.resumePerform st vtid.val executingCore)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
  | .tcbSetFaultHandler =>
    match cap.target with
    | .object objId =>
      match decodeSetFaultHandlerArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error (e, st)
        | .ok vtid =>
          RefusalCarrying.ofChecked (setThreadFaultHandlerAdmitted st vtid args.handlerCPtr)
            (fun st => st.updateTcb vtid.val
              (fun t => { t with faultHandlerSet := true, faultHandlerWord := args.handlerCPtr }))
            (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
  | .tcbSetSpace =>
    match cap.target with
    | .object objId =>
      match decodeSetSpaceArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error (e, st)
        | .ok vtid =>
          resolveSetSpaceK tid args st (fun e => .error (e, st)) (fun cnId vrId =>
            RefusalCarrying.ofChecked (setThreadSpaceAdmitted st vtid cnId vrId)
              (fun st => st.updateTcb vtid.val
                (fun t => { t with cspaceRoot := cnId, vspaceRoot := vrId }))
              (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability, st)
  | .tcbBindNotification =>
    match cap.target with
    | .object tcbObjId =>
      match decodeTcbBindNotificationArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match st.getTcb? tid with
        | some callerTcb =>
          match st.getCNode? callerTcb.cspaceRoot with
          | some rootCn =>
            resolveCapAddressKUnrolled callerTcb.cspaceRoot args.notificationCPtr rootCn.depth st
              (fun e => .error (e, st))
              (fun cnode slot =>
                match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
                | none => .error (.invalidCapability, st)
                | some ntfnCap =>
                  if SeLe4n.Kernel.capTargetsReservedIdleObject ntfnCap then
                    .error (.invalidCapability, st)
                  else if ntfnCap.hasRight .write then
                    match ntfnCap.target with
                    | .object notifId =>
                      RefusalCarrying.ofChecked
                        (bindNotificationInPlace st notifId (SeLe4n.ThreadId.ofNat tcbObjId.toNat))
                        (fun st => storeBindNotification st notifId
                          (SeLe4n.ThreadId.ofNat tcbObjId.toNat))
                        (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
                    | _ => .error (.invalidCapability, st)
                  else .error (.illegalAuthority, st))
          | none => .error (.invalidCapability, st)
        | none => .error (.objectNotFound, st)
    | _ => .error (.invalidCapability, st)
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
    | _ => .error (.invalidCapability, st)
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
  rcases cap with ⟨target, rights, badge, mapping⟩
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
            apply RefusalCarrying.ofChecked_eq
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
            apply RefusalCarrying.ofChecked_eq
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
          apply RefusalCarrying.ofChecked_eq
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
            apply RefusalCarrying.ofChecked_eq
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
        apply RefusalCarrying.ofChecked_eq
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
        apply RefusalCarrying.ofChecked_eq
        intro hA
        obtain ⟨sgi, hS⟩ := Lifecycle.Suspend.resumeThreadOnCore_of_admitted _ _ executingCore hA
        simp only [dispatchInvocationBy, hT, retirePendingFaultForResume_of_resumeAdmitted hA, hS]
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
          apply RefusalCarrying.ofChecked_eq
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
            obtain ⟨cnId, vrId⟩ := ids
            try dsimp only
            apply RefusalCarrying.ofChecked_eq
            intro hA
            simp only [dispatchInvocationBy, hD, hT, hR, setThreadSpace_of_admitted _ _ _ _ hA]
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
          cases hN : st.getCNode? callerTcb.cspaceRoot with
          | none => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, hN]
          | some rootCn =>
            dsimp only
            rw [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
            cases hRes : resolveCapAddress callerTcb.cspaceRoot args.notificationCPtr
                rootCn.depth st with
            | error e =>
              simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, hN, syscallLookupCap,
                syscallResolveCap, hRes]
            | ok ref =>
              obtain ⟨cnode, slot⟩ := ref
              dsimp only
              cases hL : SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
              | none =>
                simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, hN, syscallLookupCap,
                  syscallResolveCap, hRes, hL]
              | some ntfnCap =>
                dsimp only
                by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject ntfnCap = true
                · simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, hN,
                    syscallLookupCap, syscallResolveCap, hRes, hL, hIdle]
                · by_cases hRight : ntfnCap.hasRight .write = true
                  · cases hTg : ntfnCap.target with
                    | object notifId =>
                      simp only [hIdle, hRight, hTg, Bool.false_eq_true, ↓reduceIte]
                      apply RefusalCarrying.ofChecked_eq
                      intro hA
                      simp only [dispatchInvocationBy, hD, hC, hN, syscallLookupCap,
                        syscallResolveCap, hRes, hL, hIdle, hRight, hTg, Bool.false_eq_true,
                        ↓reduceIte, bindNotification_of_inPlace _ _ _ hA]
                    | _ => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, hN,
                      syscallLookupCap, syscallResolveCap, hRes, hL, hIdle, hRight, hTg]
                  · simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hC, hN,
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
  all_goals
    dsimp only [RefusalCarrying.ofKernel]
    split <;> next h => rw [h]

/-- A routed invocation's arm behind the operand check: the rights gate
`syscallLookupCap` applies, then `dispatchInvocationBy` reading the caller's own
registers.  Its taint step is the identity (`applySyscallTaintAfter_routed`), so
there is none. -/
@[inline] def invocationOperandArmR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (regs : RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) :
    TaintTable → Option Capability → RefusalCarrying Unit :=
  fun _ operand st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight (syscallRequiredRight sid) then
          dispatchInvocationByR ctx sid capAddr SeLe4n.arm64DefaultLayout regs tid
            executingCore cap st
        else .error (.illegalAuthority, st)

/-- `dispatchSyscallChecked` for a routed invocation, its operand address, syscall
and arguments read from the caller's register file (`dispatchInvocationCheckedR_eq`). -/
@[inline] def dispatchInvocationCheckedR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (regs : RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (invocationOperandArmR ctx sid capAddr regs tid executingCore)

theorem dispatchInvocationCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (regs : RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (hRouted : routedInvocation decoded.syscallId = true)
    (hRegs : decoded.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs)) :
    dispatchInvocationCheckedR ctx decoded.syscallId decoded.capAddr regs tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  obtain ⟨-, -, hFirst, hNotYield⟩ := routedInvocation_classic _ hRouted
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ hFirst hNotYield
  intro st tcb rootCn ref _ _ hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel, hFirst,
    Bool.false_eq_true, ↓reduceIte, syscallInvoke, syscallLookupCap, syscallResolveCap, hRef,
    applySyscallTaintAfter_routed st tid decoded hRouted]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [invocationOperandArmR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight (syscallRequiredRight decoded.syscallId) = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [dispatchInvocationByR_eq]
        simp only [RefusalCarrying.ofKernel]
        rw [← dispatchWithCapChecked_eq_invocationBy ctx decoded SeLe4n.arm64DefaultLayout regs
          tid executingCore
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
          cap st hRouted hRegs]
        rcases dispatchWithCapChecked ctx decoded tid executingCore _ cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

end SeLe4n.Kernel
