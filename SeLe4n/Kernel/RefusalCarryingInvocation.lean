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
          match dispatchInvocationBy ctx sid capAddr SeLe4n.arm64DefaultLayout regs tid
              executingCore cap st with
          | .error e => .error (e, st)
          | .ok r => .ok r
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
        rw [← dispatchWithCapChecked_eq_invocationBy ctx decoded SeLe4n.arm64DefaultLayout regs
          tid executingCore
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
          cap st hRouted hRegs]
        rcases dispatchWithCapChecked ctx decoded tid executingCore _ cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

end SeLe4n.Kernel
