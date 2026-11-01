-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingDispatch
import SeLe4n.Kernel.VSpacePerform

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
  | .cspaceMint =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceMintArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
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
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
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
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
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
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
            cspaceDeleteSlotZombie executingCore addr st
    | _ => .error .invalidCapability
  | .cspaceRevoke =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceDeleteArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
            cspaceRevokeCdtFinalising executingCore addr st
    | _ => .error .invalidCapability
  | .mintReplyCap =>
    match cap.target with
    | .object cnodeId =>
        match decodeCSpaceCopyArgsBy (msgRegOfFile layout regs) with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            mintReplyCapWithCdt src dst st
    | _ => .error .invalidCapability
  | .untypedRetype =>
    match cap.target with
    | .object _ => untypedRetypeFromCap tid executingCore capAddr (decodeUntypedRetypeArgsBy (msgRegOfFile layout regs)) st
    | _ => .error .invalidCapability
  | .untypedReset =>
    match cap.target with
    | .object _ => untypedResetFromCap tid capAddr st
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
    | .object epId => revokeServiceChecked ctx tid epId st
    | _ => .error .invalidCapability
  | .serviceQuery =>
    match cap.target with
    | .object epId => serviceQueryStaged ctx tid epId st
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
            | .ok (cnSrc, vrSrc) =>
                match copyThreadSpacesZombie executingCore st vtid cnSrc vrSrc with
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
    (preEpoch : Nat) (preLength : Nat) (preTaint : TaintMap)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength preTaint post =
      post := by
  obtain ⟨hC, hR, -, -⟩ := routedInvocation_classic _ h
  simp only [applySyscallTaintAfter, syscallTaintPlan, hC, hR, Bool.false_eq_true,
    ↓reduceIte, applyOrigination, applyTaintFlow, applyTaintClears, applyTaintStep, List.foldl,
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
      hCopy, hMove, hDelete, hRetype, hMap, hUnmap, hScBind, hNtfn, hPrio, hMcp,
      hIpcBuf, hAff, hFault, hSpace, hPt, decodeVSpaceUnifyInstructionArgs,
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
      simp only [hF, Option.isNone_some, Bool.false_or, Bool.and_eq_true] at h
      unfold Lifecycle.Suspend.resumeAdmitted
      simp only [retirePendingFaultForResume, hT, hF, applyFaultRestart]
      rw [updateTcb_getTcb?_self_of_findsInPlace _ hT h.2]
      simp only [TCB.withRestartFrame_threadState, Option.isNone_none, Bool.true_or,
        Bool.and_true]
      exact h.1

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
          (fun st => Lifecycle.Suspend.resumePerform
            (retirePendingFaultForResume st vtid.val) vtid.val executingCore)
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
          resolveSetSpaceK tid args st (fun e => .error (e, st)) (fun cnC cnS vrC vrS =>
            RefusalCarrying.ofChecked
              (copyThreadSpacesAdmitted st vtid { cnode := cnC, slot := cnS } { cnode := vrC, slot := vrS })
              (fun st => copyThreadSpacesZombiePerform executingCore st vtid cnC cnS vrC vrS)
              (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability, st)
  | .schedContextBind =>
    match cap.target with
    | .object scObjId =>
      match decodeSchedContextBindArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match st.getTcb? tid with
        | some callerTcb =>
          match st.getCNode? callerTcb.cspaceRoot with
          | some rootCn =>
            resolveCapAddressKUnrolled callerTcb.cspaceRoot args.tcbCPtr rootCn.depth st
              (fun e => .error (e, st))
              (fun cnode slot =>
                match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
                | none => .error (.invalidCapability, st)
                | some tcbCap =>
                  if SeLe4n.Kernel.capTargetsReservedIdleObject tcbCap then
                    .error (.invalidCapability, st)
                  else if tcbCap.hasRight .write then
                    match tcbCap.target with
                    | .object tcbObjId =>
                      match st.getTcb? (SeLe4n.ThreadId.ofNat tcbObjId.toNat) with
                      | none => .error (.invalidCapability, st)
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
                    | _ => .error (.invalidCapability, st)
                  else .error (.illegalAuthority, st))
          | none => .error (.invalidCapability, st)
        | none => .error (.objectNotFound, st)
    | _ => .error (.invalidCapability, st)
  | .schedContextUnbind =>
    match cap.target with
    | .object scObjId =>
      match validateObjIdArg scObjId with
      | .error e => .error (e, st)
      | .ok vScId =>
        RefusalCarrying.ofChecked (SchedContextOps.schedContextUnbindAdmitted st vScId)
          (fun st => SchedContextOps.schedContextUnbindOnCorePerform st vScId executingCore)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
  | .schedContextConsumed =>
    match cap.target with
    | .object scObjId =>
      match validateObjIdArg scObjId with
      | .error e => .error (e, st)
      | .ok vScId =>
        RefusalCarrying.ofChecked
          (schedContextConsumedAdmitted st (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore)
          (fun st => schedContextConsumedPerform st (SeLe4n.SchedContextId.ofObjId vScId.val)
            executingCore)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
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
  | .cspaceMint =>
    match cap.target with
    | .object cnodeId =>
      match decodeCSpaceMintArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
        let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
        RefusalCarrying.ofChecked
          (securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) &&
            cspaceMintAdmittedAt cnodeId args.srcSlot args.dstSlot args.rights args.badge st)
          (fun st => cspaceMintPerformAt cnodeId args.srcSlot args.dstSlot args.rights args.badge st)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
  | .cspaceMove =>
    match cap.target with
    | .object cnodeId =>
      match decodeCSpaceMoveArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
        let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
        RefusalCarrying.ofChecked
          (securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) &&
            cspaceMoveAdmittedAt cnodeId args.srcSlot args.dstSlot st)
          (fun st => cspaceMovePerformAt cnodeId args.srcSlot args.dstSlot st)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
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
    | _ => .error (.invalidCapability, st)
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
    | _ => .error (.invalidCapability, st)
  | .mintReplyCap =>
    match cap.target with
    | .object cnodeId =>
      match decodeCSpaceCopyArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
        let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
        RefusalCarrying.ofChecked (mintReplyCapAdmittedAt cnodeId args.srcSlot args.dstSlot st)
          (fun st => mintReplyCapPerformAt cnodeId args.srcSlot args.dstSlot st)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
  | .cspaceCopy =>
    match cap.target with
    | .object cnodeId =>
      match decodeCSpaceCopyArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
        let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
        RefusalCarrying.ofChecked
          (securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) &&
            cspaceCopyAdmittedAt cnodeId args.srcSlot args.dstSlot st)
          (fun st => cspaceCopyPerformAt cnodeId args.srcSlot args.dstSlot st)
          (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
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
              RefusalCarrying.ofChecked (vspaceMapAdmittedAt st args frameCap frame rootId)
                (fun st => vspaceMapPerformAt executingCore args.asid args.vaddr frame.base
                  args.perms rootId (frameCapObjId frameCap) frameCnode frameSlot st)
                (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability, st)
  | .vspaceUnmap =>
    match cap.target with
    | .object rootId =>
      match decodeVSpaceUnmapArgsBy (msgRegOfFile layout regs) st.machine.maxASID with
      | .error e => .error (e, st)
      | .ok args =>
        if !vspaceCapAuthorizesAsid cap args.asid st then .error (.illegalAuthority, st)
        else
          RefusalCarrying.ofChecked (vspaceUnmapAdmittedAt st args.asid args.vaddr rootId)
            (fun st => vspaceUnmapPerformAt executingCore args.asid args.vaddr rootId st)
            (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
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
    | _ => .error (.invalidCapability, st)
  | .pageTableMap =>
    match cap.target with
    | .object objId =>
      match decodePageTableMapArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        resolveCallerCapObjectK tid args.vspaceRoot .write st (fun e => .error (e, st))
          (fun _ rootId =>
            RefusalCarrying.ofChecked (pageTableMapAdmittedAt st objId rootId args.vaddr)
              (fun st => pageTableMapPerformAt objId rootId args.vaddr st)
              (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability, st)
  | .pageTableUnmap =>
    match cap.target with
    | .object objId =>
      RefusalCarrying.ofChecked (pageTableUnmapAdmittedAt st objId)
        (fun st => pageTableUnmapPerformAt objId st)
        (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
  | .untypedRetype =>
    match cap.target with
    | .object _ =>
      match decodeUntypedRetypeArgsBy (msgRegOfFile layout regs) with
      | .error e => .error (e, st)
      | .ok args =>
        match carveRequestOf? st executingCore args.newType args.sizeBits with
        | .error e => .error (e, st)
        | .ok req =>
          match validateObjIdArg args.childId with
          | .error e => .error (e, st)
          | .ok vChild =>
            resolveUntypedRetypeK tid capAddr args st (fun e => .error (e, st))
              (fun srcCnode srcSlot dstCnode dstSlot =>
                RefusalCarrying.ofChecked
                  (untypedRetypeAdmittedAt st ⟨srcCnode, srcSlot⟩ ⟨dstCnode, dstSlot⟩ vChild.val req)
                  (fun st => untypedRetypePerformAt ⟨srcCnode, srcSlot⟩ ⟨dstCnode, dstSlot⟩
                    vChild.val req st)
                  (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability, st)
  | .untypedReset =>
    match cap.target with
    | .object _ =>
      resolveCallerCapSlotK tid capAddr .retype st (fun e => .error (e, st))
        (fun srcCnode srcSlot _ _ =>
          RefusalCarrying.ofChecked (untypedResetAdmittedAt st srcCnode srcSlot)
            (fun st => untypedResetPerformAt srcCnode srcSlot st)
            (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st)
    | _ => .error (.invalidCapability, st)
  -- WS-ZA ZA5.5: the revoke and the query through the endpoint read its
  -- recorded registration first and then write in place.
  | .serviceRevoke =>
    match cap.target with
    | .object epId =>
      RefusalCarrying.ofChecked
        (serviceEndpointWriteAdmitted ctx tid epId && recordedRegistrationPresent st epId)
        (fun st => revokeServiceByRecordedRegistrationPerform st epId)
        (dispatchInvocationBy ctx sid capAddr layout regs tid executingCore cap) st
    | _ => .error (.invalidCapability, st)
  | .serviceQuery =>
    match cap.target with
    | .object epId =>
      RefusalCarrying.ofChecked
        (serviceEndpointReadAdmitted ctx tid epId && recordedRegistrationPresent st epId)
        (fun st => serviceQueryPerform st tid epId)
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
          cases hN : st.getCNode? callerTcb.cspaceRoot with
          | none =>
            simp [RefusalCarrying.ofKernel, dispatchInvocationBy, resolveSchedContextBindThread,
              hD, hC, hN]
          | some rootCn =>
            dsimp only
            rw [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
            cases hRes : resolveCapAddress callerTcb.cspaceRoot args.tcbCPtr rootCn.depth st with
            | error e =>
              simp [RefusalCarrying.ofKernel, dispatchInvocationBy, resolveSchedContextBindThread,
                hD, hC, hN, syscallLookupCap, syscallResolveCap, hRes]
            | ok ref =>
              obtain ⟨cnode, slot⟩ := ref
              dsimp only
              cases hL : SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
              | none =>
                simp [RefusalCarrying.ofKernel, dispatchInvocationBy, resolveSchedContextBindThread,
                  hD, hC, hN, syscallLookupCap, syscallResolveCap, hRes, hL]
              | some tcbCap =>
                dsimp only
                by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject tcbCap = true
                · simp [RefusalCarrying.ofKernel, dispatchInvocationBy,
                    resolveSchedContextBindThread, hD, hC, hN, syscallLookupCap,
                    syscallResolveCap, hRes, hL, hIdle]
                · by_cases hRight : tcbCap.hasRight .write = true
                  · cases hTg : tcbCap.target with
                    | object tcbObjId =>
                      cases hT : st.getTcb? (SeLe4n.ThreadId.ofNat tcbObjId.toNat) with
                      | none =>
                        simp [RefusalCarrying.ofKernel, dispatchInvocationBy,
                          resolveSchedContextBindThread, hD, hC, hN, syscallLookupCap,
                          syscallResolveCap, hRes, hL, hIdle, hRight, hTg, hT]
                      | some _ =>
                        cases hV : validateThreadIdArg (SeLe4n.ThreadId.ofNat tcbObjId.toNat) with
                        | error e =>
                          simp [RefusalCarrying.ofKernel, dispatchInvocationBy,
                            resolveSchedContextBindThread, hD, hC, hN, syscallLookupCap,
                            syscallResolveCap, hRes, hL, hIdle, hRight, hTg, hT, hV]
                        | ok vThreadId =>
                          cases hS : validateObjIdArg objId with
                          | error e =>
                            simp [RefusalCarrying.ofKernel, dispatchInvocationBy,
                              resolveSchedContextBindThread, hD, hC, hN, syscallLookupCap,
                              syscallResolveCap, hRes, hL, hIdle, hRight, hTg, hT, hV, hS]
                          | ok vScId =>
                            simp only [hIdle, hRight, hTg, hT, hV, hS, Bool.false_eq_true,
                              ↓reduceIte]
                            apply RefusalCarrying.ofChecked_eq
                            intro hA
                            simp only [dispatchInvocationBy, resolveSchedContextBindThread, hD, hC,
                              hN, syscallLookupCap, syscallResolveCap, hRes, hL, hIdle, hRight,
                              hTg, hT, hV, hS, Bool.false_eq_true, ↓reduceIte,
                              SchedContextOps.schedContextBind_of_admitted _ _ _ hA]
                    | _ => simp [RefusalCarrying.ofKernel, dispatchInvocationBy,
                      resolveSchedContextBindThread, hD, hC, hN, syscallLookupCap,
                      syscallResolveCap, hRes, hL, hIdle, hRight, hTg]
                  · simp [RefusalCarrying.ofKernel, dispatchInvocationBy,
                      resolveSchedContextBindThread, hD, hC, hN, syscallLookupCap,
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
        apply RefusalCarrying.ofChecked_eq
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
        apply RefusalCarrying.ofChecked_eq
        intro hA
        simp only [dispatchInvocationBy, hS, schedContextConsumedOnCore_of_admitted _ _ _ hA]
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
  case cspaceMint =>
    cases target
    case object cnodeId =>
      dsimp only
      cases hD : decodeCSpaceMintArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        dsimp only [cspaceMintAdmittedAt, cspaceMintPerformAt]
        apply RefusalCarrying.ofChecked_eq
        intro hA
        simp only [Bool.and_eq_true] at hA
        simp only [dispatchInvocationBy, hD, cspaceMintChecked, hA.1, ↓reduceIte,
          cnodeInvoked_of_mintAdmitted hA.2, Bool.not_true, Bool.false_eq_true,
          cspaceMintWithCdt_of_admitted hA.2]
    all_goals rfl
  case cspaceMove =>
    cases target
    case object cnodeId =>
      dsimp only
      cases hD : decodeCSpaceMoveArgsBy (msgRegOfFile layout regs) with
      | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD]
      | ok args =>
        dsimp only [cspaceMoveAdmittedAt, cspaceMovePerformAt]
        apply RefusalCarrying.ofChecked_eq
        intro hA
        simp only [Bool.and_eq_true] at hA
        simp only [dispatchInvocationBy, hD, cspaceMoveChecked, hA.1, ↓reduceIte,
          cnodeInvoked_of_moveAdmitted hA.2, Bool.not_true, Bool.false_eq_true,
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
      cases hD : decodeCSpaceCopyArgsBy (msgRegOfFile layout regs) with
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
        dsimp only [cspaceCopyAdmittedAt, cspaceCopyPerformAt]
        apply RefusalCarrying.ofChecked_eq
        intro hA
        simp only [Bool.and_eq_true] at hA
        simp only [dispatchInvocationBy, hD, cspaceCopyChecked, hA.1, ↓reduceIte,
          cnodeInvoked_of_copyAdmitted hA.2, Bool.not_true, Bool.false_eq_true,
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
            simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hAu, vspaceMapFromFrameCap,
              hRs]
          | ok triple =>
            obtain ⟨frameSlot, frameCap, frame⟩ := triple
            dsimp only
            apply RefusalCarrying.ofChecked_eq
            intro hA
            simp only [dispatchInvocationBy, hD, hAu, Bool.false_eq_true, ↓reduceIte,
              vspaceMapFromFrameCap_of_admitted tid executingCore args st frameSlot frameCap frame
                rootId hRs hA]
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
          apply RefusalCarrying.ofChecked_eq
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
        | error e => simp [RefusalCarrying.ofKernel, dispatchInvocationBy, hD, hRs]
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
      apply RefusalCarrying.ofChecked_eq
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
            rw [resolveUntypedRetypeK_eq]
            cases hR : resolveUntypedRetype tid capAddr args st with
            | error e =>
              simp [RefusalCarrying.ofKernel, dispatchInvocationBy, untypedRetypeFromCap, hD, hQ,
                hV, hR]
            | ok pr =>
              obtain ⟨src, dst⟩ := pr
              dsimp only
              apply RefusalCarrying.ofChecked_eq
              intro hA
              simp only [dispatchInvocationBy, untypedRetypeFromCap, hD, hQ, hV, hR,
                untypedRetypeObject_of_admitted hA]
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
      apply RefusalCarrying.ofChecked_eq
      intro hA
      simp only [dispatchInvocationBy, serviceQueryStaged_of_admitted ctx tid epId st hA]
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
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
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
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ hNotYield
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
        else .error .invalidCapability
  | _ => .error .invalidCapability

theorem dispatchWithCapChecked_eq_configureBy (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (w : UInt64) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState)
    (h : decoded.syscallId = .schedContextConfigure)
    (hRegs : decoded.msgRegs = layout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)]) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      dispatchConfigureBy layout regs w tid cap st := by
  have hDec := decodeSchedContextConfigureArgsChecked_eq_by layout regs w decoded hRegs
  rcases decoded with ⟨capAddr, msgInfo, sid, msgRegs, capRecvSlot, inlineCount, overflowCount⟩
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
        else .error (.invalidCapability, st))
  | _ => .error (.invalidCapability, st)

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

/-- The configure's arm behind the operand check: the rights gate
`syscallLookupCap` applies, then `dispatchConfigureByR`. -/
@[inline] def configureOperandArmR (regs : RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight (syscallRequiredRight .schedContextConfigure) then
          dispatchConfigureByR SeLe4n.arm64DefaultLayout regs w tid cap st
        else .error (.illegalAuthority, st)

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
    (hRegs : decoded.msgRegs =
      SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)]) :
    dispatchConfigureCheckedR decoded.capAddr regs w tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  have hFirst : syscallChecksTargetFirst decoded.syscallId = false := by
    rw [hSid]; rfl
  have hNotYield : decoded.syscallId ≠ .yield := by
    rw [hSid]; exact fun h => SyscallId.noConfusion h
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ hNotYield
  intro st tcb rootCn ref _ _ hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel, hFirst,
    Bool.false_eq_true, ↓reduceIte, syscallInvoke, syscallLookupCap, syscallResolveCap, hRef,
    applySyscallTaintAfter_configure st tid decoded hSid]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [configureOperandArmR, hSid]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight (syscallRequiredRight .schedContextConfigure) = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [dispatchConfigureByR_eq]
        simp only [RefusalCarrying.ofKernel]
        rw [← dispatchWithCapChecked_eq_configureBy ctx decoded SeLe4n.arm64DefaultLayout regs w
          tid executingCore
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight .schedContextConfigure }
          cap st hSid hRegs]
        rcases dispatchWithCapChecked ctx decoded tid executingCore _ cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

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
  | _ => .error .invalidCapability

theorem dispatchWithCapChecked_eq_serviceRegisterBy (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (w : UInt64) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState)
    (h : decoded.syscallId = .serviceRegister)
    (hRegs : decoded.msgRegs = layout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)]) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      dispatchServiceRegisterBy ctx tid layout regs w cap st := by
  have hDec := decodeServiceRegisterArgs_eq_by layout regs w decoded hRegs
  rcases decoded with ⟨capAddr, msgInfo, sid, msgRegs, capRecvSlot, inlineCount, overflowCount⟩
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
  | _ => .error (.invalidCapability, st)

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

/-- **WS-ZA ZA5.9: the register arm as compiled** — its checks read off the
decoded words and the invoked capability, and its write
`registerServiceWordsPerform`, so the arm builds no registration on an admitted
call; only a refusal builds one, to run the specification for its error.  Equal
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
        match registerServiceChecked ctx tid
            { iface := { ifaceId := args.interfaceId, methodCount := args.methodCount
                         maxMessageSize := args.maxMessageSize
                         maxResponseSize := args.maxResponseSize
                         requiresGrant := args.requiresGrant }
              endpointCap := cap } st with
        | .error e => .error (e, st)
        | .ok r => .ok r
  | _ => .error (.invalidCapability, st)

@[csimp] theorem dispatchServiceRegisterByR_eq_impl :
    @dispatchServiceRegisterByR = @dispatchServiceRegisterByRImpl := by
  funext ctx tid layout regs w cap st
  unfold dispatchServiceRegisterByR dispatchServiceRegisterByRImpl RefusalCarrying.ofChecked
  rcases cap with ⟨target, rights, badge, mapping⟩
  cases target with
  | object epId =>
    dsimp only
    cases decodeServiceRegisterArgsBy (msgRegOfFileThen layout regs w) with
    | error e => rfl
    | ok args =>
      dsimp only
      simp only [registerServicePerform_eq_impl]
      rfl
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

/-- The service register's arm behind the operand check: the rights gate
`syscallLookupCap` applies, then `dispatchServiceRegisterByR`. -/
@[inline] def serviceRegisterOperandArmR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (regs : RegisterFile) (w : UInt64) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight (syscallRequiredRight .serviceRegister) then
          dispatchServiceRegisterByR ctx tid SeLe4n.arm64DefaultLayout regs w cap st
        else .error (.illegalAuthority, st)

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
    (hRegs : decoded.msgRegs =
      SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)]) :
    dispatchServiceRegisterCheckedR ctx decoded.capAddr regs w tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  have hFirst : syscallChecksTargetFirst decoded.syscallId = false := by
    rw [hSid]; rfl
  have hNotYield : decoded.syscallId ≠ .yield := by
    rw [hSid]; exact fun h => SyscallId.noConfusion h
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ hNotYield
  intro st tcb rootCn ref _ _ hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel, hFirst,
    Bool.false_eq_true, ↓reduceIte, syscallInvoke, syscallLookupCap, syscallResolveCap, hRef,
    applySyscallTaintAfter_serviceRegister st tid decoded hSid]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [serviceRegisterOperandArmR, hSid]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight (syscallRequiredRight .serviceRegister) = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [dispatchServiceRegisterByR_eq]
        simp only [RefusalCarrying.ofKernel]
        rw [← dispatchWithCapChecked_eq_serviceRegisterBy ctx decoded SeLe4n.arm64DefaultLayout
          regs w tid executingCore
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight .serviceRegister }
          cap st hSid hRegs]
        rcases dispatchWithCapChecked ctx decoded tid executingCore _ cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-! ## The one-overflow-word invocations

The register route's `overflowOne` arm names one of `routedOverflowOne`: the
configure or the service register, each with its fifth word `w`. -/

/-- `dispatchSyscallChecked` for a one-overflow-word invocation `sid` whose
fifth word is `w` (`dispatchOverflowOneCheckedR_eq`).  The last arm is never
taken: the route names only `routedOverflowOne` calls. -/
@[inline] def dispatchOverflowOneCheckedR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (regs : RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  match sid with
  | .schedContextConfigure => dispatchConfigureCheckedR capAddr regs w tid executingCore
  | .serviceRegister => dispatchServiceRegisterCheckedR ctx capAddr regs w tid executingCore
  | _ => fun st => .error (.illegalState, st)

theorem dispatchOverflowOneCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (regs : RegisterFile) (w : UInt64)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hR : Architecture.RegisterDecode.routedOverflowOne decoded.syscallId = true)
    (hRegs : decoded.msgRegs =
      SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)]) :
    dispatchOverflowOneCheckedR ctx decoded.syscallId decoded.capAddr regs w tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  cases hSid : decoded.syscallId <;> rw [hSid] at hR <;>
    first
    | (cases hR; done)
    | exact dispatchConfigureCheckedR_eq ctx decoded regs w tid executingCore hSid hRegs
    | exact dispatchServiceRegisterCheckedR_eq ctx decoded regs w tid executingCore hSid hRegs

end SeLe4n.Kernel
