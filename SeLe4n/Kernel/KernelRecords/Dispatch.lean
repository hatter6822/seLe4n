-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.KernelRecords.Capability
import SeLe4n.Kernel.KernelRecords.Audit
import SeLe4n.Kernel.KernelRecords.Tails
import SeLe4n.Kernel.KernelRecords.SchedulingArms
import SeLe4n.Kernel.KernelRecords.Delete
import SeLe4n.Kernel.KernelRecords.VSpace
import SeLe4n.Kernel.KernelRecords.SetSpace
import SeLe4n.Kernel.KernelRecords.Retype
import SeLe4n.Kernel.KernelRecords.LifecycleWaiters
import SeLe4n.Kernel.KernelRecords.IpcStages
import SeLe4n.Kernel.KernelRecords.IpcReplyRecv
import SeLe4n.Kernel.KernelRecords.Timer

/-! # The dispatchers keep the records

WS-ZA ZA6.37.  The capability-only dispatch keeps the records on every arm: each
arm is a records stage (`Kernel/KernelRecords/*.lean`), and the capability
resolution and the argument decodes read.  Three facts are read off the state
the dispatcher is handed, as the mapping traversal reads its own
(`MappingArmPremises`) and the IPC traversal its reachable bundle: the deletes,
the thread-space set and the handler bind and clear carry the reply-waiter
queues by the reachable bundle (`reachableDeleteBundle`), and the resume restores
an `.Inactive` thread, which is quiescent in IPC (`threadIpcFieldsQuiescent`, the
`targetThreadQuiescent` field of the dispatch's premises, stated here of every
`.Inactive` thread so it is a fact about the state, not about the call).  The arm runs on the state the dispatcher is handed, since its
lookups and decodes write nothing.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- A stage onto a transition's state is a stage onto the state it returns. -/
theorem RecordsStage.of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : RecordsStage st p.1) (h : p = (st', r)) : RecordsStage st st' := by
  subst h; exact s

/-- What the capability arms read off the dispatcher's state beyond the records:
the reachable bundle the deletes carry, and every `.Inactive` thread's IPC
quiescence, which the resume reads of its target. -/
structure RecordsArmPremises (st : SystemState) : Prop where
  deletes : reachableDeleteBundle st
  inactiveQuiescent : ∀ t tcb, st.getTcb? t = some tcb → tcb.threadState = .Inactive →
    threadIpcFieldsQuiescent st t

/-- The retire before a resume keeps the thread's state. -/
theorem retirePendingFaultForResume_threadState {st : SystemState} {t : SeLe4n.ThreadId} {y : TCB}
    (hInv : st.objects.invExt) (hy : (retirePendingFaultForResume st t).getTcb? t = some y) :
    ∃ x, st.getTcb? t = some x ∧ x.threadState = y.threadState := by
  cases hT : st.getTcb? t with
  | none => simp only [retirePendingFaultForResume, hT] at hy; cases hy
  | some x =>
    refine ⟨x, rfl, ?_⟩
    cases hF : x.pendingFault with
    | none => simp only [retirePendingFaultForResume, hT, hF] at hy; cases hy; rfl
    | some tf =>
      simp only [retirePendingFaultForResume, hT, hF] at hy
      split at hy
      · rw [discardPendingFault_getTcb?_self st t x hT hInv] at hy; cases hy; rfl
      · rw [applyFaultRestart_pc st t _ x hT hInv] at hy; cases hy; rfl

/-- A resume that commits found its target `.Inactive`, so quiescent in IPC. -/
theorem inactiveQuiescent_of_resume {st : SystemState} {vtid : SeLe4n.ValidThreadId} {c : Concurrency.CoreId}
    {r : SystemState × Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (P : RecordsArmPremises st) (hInv : st.objects.invExt)
    (h : Lifecycle.Suspend.resumeThreadOnCore (retirePendingFaultForResume st vtid.val) vtid c
      = .ok r) : threadIpcFieldsQuiescent st vtid.val := by
  unfold Lifecycle.Suspend.resumeThreadOnCore at h
  dsimp only at h
  split at h
  · rename_i y hy
    split at h
    · cases h
    · rename_i hIn
      obtain ⟨x, hx, hS⟩ := retirePendingFaultForResume_threadState hInv hy
      exact P.inactiveQuiescent _ x hx (by rw [hS]; simpa using hIn)
  · cases h

/-- **The capability-only dispatch keeps the records on every arm**: the deletes,
the space set and the handler arms from the reachable bundle they read, the
resume from the target's quiescence, every other arm from the records alone. -/
theorem dispatchCapabilityOnly_recordsStage
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (k : Kernel Unit) (st st' : SystemState)
    (hArm : dispatchCapabilityOnly decoded cap tid executingCore = some k)
    (P : RecordsArmPremises st) (hStep : k st = .ok ((), st')) :
    RecordsStage st st' := by
  unfold dispatchCapabilityOnly at hArm
  cases hSy : decoded.syscallId <;> simp only [hSy] at hArm <;> try cases hArm
  case cspaceDelete =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceDeleteArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact fun h => (cspaceDeleteSlotZombie_deleteRecordsCarried ⟨h, P.deletes⟩ hStep).1
    all_goals try cases hStep
  case cspaceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceDeleteArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact fun h => (cspaceRevokeCdtFinalising_deleteRecordsCarried ⟨h, P.deletes⟩ hStep).1
    all_goals try cases hStep
  case mintReplyCap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceCopyArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact .of_frameK fun hI => RecordsFrame.mintReplyCapWithCdt hI hStep
    all_goals try cases hStep
  case untypedRetype =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      exact RecordsStage.untypedRetypeFromCap hStep
    all_goals try cases hStep
  case untypedReset =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      exact .of_frameK fun hI => RecordsFrame.untypedResetFromCap hI hStep
    all_goals try cases hStep
  case vspaceMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceMapArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · exact RecordsStage.vspaceMapOrRemapFromFrameCap hStep
    all_goals try cases hStep
  case vspaceUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceUnmapArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · exact RecordsStage.vspaceUnmapPageWithShootdownAndIcacheBroadcast hStep
    all_goals try cases hStep
  case vspaceUnifyInstruction =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceUnifyInstructionArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · exact .of_frameK fun hI => RecordsFrame.vspaceUnifyInstructionPage hI hStep
    all_goals try cases hStep
  case serviceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      obtain ⟨_, hRev⟩ := revokeServiceByRecordedRegistration_revokeService hStep
      exact .of_frameK fun hI => RecordsFrame.revokeService hI hRev
    all_goals try cases hStep
  case serviceQuery =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object epId =>
      try dsimp only [] at hStep
      cases hLkS : lookupServiceByRecordedRegistration epId st with
      | error e => simp only [hLkS] at hStep; cases hStep
      | ok pair =>
          obtain ⟨reg, st1⟩ := pair
          simp only [hLkS] at hStep
          have hStEq : st1 = st := lookupServiceByRecordedRegistration_preserves_state epId st reg st1 hLkS
          subst hStEq
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
          subst hStep
          exact .of_frameK fun hI => RecordsFrame.writeReturnFrameToTcb _ _ _ hI
    all_goals try cases hStep
  case schedContextConfigure =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case schedControl core =>
      try dsimp only [] at hStep
      cases hDec : decodeSchedContextConfigureArgsChecked decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : resolveSchedControlConfigureTarget tid core args.scCPtr st with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              split at hStep
              · exact .of_frameK fun hI => RecordsFrame.schedControlConfigure hI hStep
              · cases hStep
    all_goals try cases hStep
  case schedContextBind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hRes : resolveSchedContextBindThread tid (decodeSchedContextBindArgs decoded) st with
      | error e => simp only [hRes] at hStep; cases hStep
      | ok vThreadId =>
          simp only [hRes] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              exact .of_frameK fun hI => RecordsFrame.schedContextBind hI hStep
    all_goals try cases hStep
  case schedContextUnbind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hDec : decodeSchedContextUnbindArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              cases hUn : SchedContextOps.schedContextUnbindOnCore vScId
                  executingCore st with
              | error e => simp only [hUn] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hUn] at hStep
                  cases hStep
                  exact .of_frameK fun hI => RecordsFrame.schedContextUnbindOnCore hI hUn
    all_goals try cases hStep
  case schedContextConsumed =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hVal : validateObjIdArg scId with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hC : schedContextConsumedOnCore (SeLe4n.SchedContextId.ofObjId vScId.val)
              executingCore st with
          | error e => simp only [hC] at hStep; cases hStep
          | ok stC =>
              simp only [hC] at hStep
              cases hStep
              exact .of_frameK fun hI => RecordsFrame.schedContextConsumedOnCore hI hC
    all_goals try cases hStep
  case schedContextYieldTo =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hVal : validateObjIdArg scId with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hC : SchedContextOps.schedContextYieldToOnCore
              (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore st with
          | error e => simp only [hC] at hStep; cases hStep
          | ok stC =>
              simp only [hC] at hStep
              cases hStep
              exact .of_frameK fun hI => RecordsFrame.schedContextYieldToOnCore hI hC
    all_goals try cases hStep
  case irqHandlerAck =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      rw [Architecture.irqHandlerAck_ok hStep]
      exact .of_frameK fun hI => RecordsFrame.of_objects_eq hI rfl rfl
    all_goals try cases hStep
  case irqControlGet =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqControl => exact .of_frameK fun hI => RecordsFrame.irqControlGetFromCap hI hStep
    all_goals try cases hStep
  case irqHandlerSetNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      obtain ⟨_, _, _, hS⟩ := irqHandlerSetNotificationFromCap_ok tid executingCore line _ st st' hStep
      exact fun h => irqHandlerSetNotification_kernelRecordsSound ⟨h, P.deletes⟩ hS
    all_goals try cases hStep
  case irqHandlerClear =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line => exact fun h => irqHandlerClear_kernelRecordsSound ⟨h, P.deletes⟩ hStep
    all_goals try cases hStep
  case tcbBindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      try dsimp only [] at hStep
      cases hDec : decodeTcbBindNotificationArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hCaller : st.getTcb? tid with
          | none => simp only [hCaller] at hStep; cases hStep
          | some callerTcb =>
              simp only [hCaller] at hStep
              cases hRoot : st.getCNode? callerTcb.cspaceRoot with
              | none => simp only [hRoot] at hStep; cases hStep
              | some rootCn =>
                  simp only [hRoot] at hStep
                  try dsimp only [] at hStep
                  cases hCap2 : syscallLookupCap { callerId := tid, cspaceRoot := callerTcb.cspaceRoot, capAddr := args.notificationCPtr, capDepth := rootCn.depth, requiredRight := .write } st with
                  | error e => simp only [hCap2] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨ntfnCap, stL⟩ := pair
                      simp only [hCap2] at hStep
                      cases hNT : ntfnCap.target with
                      | object notifId =>
                          simp only [hNT] at hStep
                          exact .of_frameK fun hI => RecordsFrame.bindNotification hI hStep
                      | _ => simp only [hNT] at hStep; cases hStep
    all_goals try cases hStep
  case tcbUnbindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      try dsimp only [] at hStep
      cases hUn : unbindNotification (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st with
      | error e => simp only [hUn] at hStep; cases hStep
      | ok pair =>
          obtain ⟨u, stU⟩ := pair; cases u
          simp only [hUn] at hStep
          cases hStep
          exact .of_frameK fun hI => RecordsFrame.unbindNotification hI hUn
    all_goals try cases hStep
  case tcbSuspend =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSuspendArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSus : Lifecycle.Suspend.suspendThreadOnCore st vtid
                  executingCore with
              | error e => simp only [hSus] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hSus] at hStep
                  cases hStep
                  exact RecordsStage.suspendThreadOnCore hSus
    all_goals try cases hStep
  case tcbResume =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeResumeArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vtid =>
          simp only [hVal] at hStep
          cases hRes : Lifecycle.Suspend.resumeThreadOnCore
              (retirePendingFaultForResume st vtid.val) vtid
              executingCore with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok pair =>
              obtain ⟨stU, sgiU⟩ := pair
              simp only [hRes] at hStep
              cases hStep
              exact fun h => RecordsStage.resumeThreadOnCore
                (threadIpcFieldsQuiescent_retirePendingFaultForResume st _
                  (KernelRecords.objects_invExt h)
                  (inactiveQuiescent_of_resume P (KernelRecords.objects_invExt h) hRes)).ready hRes
                (RecordsStage.retirePendingFaultForResume st vtid.val h)
    all_goals try cases hStep
  case tcbSetPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : validateThreadIdArg tid with
          | error e => simp only [hValC] at hStep; cases hStep
          | ok vCallerTid =>
              simp only [hValC] at hStep
              cases hValT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
              | error e => simp only [hValT] at hStep; cases hStep
              | ok vTargetTid =>
                  simp only [hValT] at hStep
                  cases hSet : SchedContext.PriorityManagement.setPriorityOnCore st
                      vCallerTid vTargetTid (Priority.ofNat args.newPriority)
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact .of_frameK fun hI => RecordsFrame.setPriorityOnCore hI hSet
    all_goals try cases hStep
  case tcbSetMCPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetMCPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : validateThreadIdArg tid with
          | error e => simp only [hValC] at hStep; cases hStep
          | ok vCallerTid =>
              simp only [hValC] at hStep
              cases hValT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
              | error e => simp only [hValT] at hStep; cases hStep
              | ok vTargetTid =>
                  simp only [hValT] at hStep
                  cases hSet : SchedContext.PriorityManagement.setMCPriorityOnCore st
                      vCallerTid vTargetTid (Priority.ofNat args.newMCP)
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact .of_frameK fun hI => RecordsFrame.setMCPriorityOnCore hI hSet
    all_goals try cases hStep
  case tcbSetIPCBuffer =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetIPCBufferArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSet : Architecture.IpcBufferValidation.setIPCBufferOp st vtid
                  args.bufferAddr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  exact .of_frameK fun hI => RecordsFrame.setIPCBufferOp hI hSet
    all_goals try cases hStep
  case tcbSetAffinity =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetAffinityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hAff : decodeAffinity args.affinityRaw with
              | error e => simp only [hAff] at hStep; cases hStep
              | ok affinity =>
                  simp only [hAff] at hStep
                  cases hSet : setThreadCpuAffinityOnCore st vtid affinity
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact .of_frameK fun hI => RecordsFrame.setThreadCpuAffinityOnCore hI hSet
    all_goals try cases hStep
  case tcbSetFaultHandler =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetFaultHandlerArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSet : setThreadFaultHandlerOp st vtid args.handlerCPtr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  exact .of_frameK fun hI => RecordsFrame.setThreadFaultHandlerOp hI hSet
    all_goals try cases hStep
  case tcbSetSpace =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetSpaceArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hR : resolveSetSpace tid args st with
              | error e => simp only [hR] at hStep; cases hStep
              | ok p =>
                  obtain ⟨cn, vr⟩ := p
                  simp only [hR] at hStep
                  cases hSet : copyThreadSpacesZombie executingCore st vtid cn vr with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok stU =>
                      simp only [hSet] at hStep
                      cases hStep
                      exact fun h => copyThreadSpacesZombie_kernelRecordsSound executingCore ⟨h, P.deletes⟩ hSet
    all_goals try cases hStep
  case pageTableMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodePageTableMapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hR : resolveCallerCapObject tid args.vspaceRoot .write st with
          | error e => simp only [hR] at hStep; cases hStep
          | ok p =>
              obtain ⟨_, rootId⟩ := p
              simp only [hR] at hStep
              exact RecordsStage.pageTableMap hStep
    all_goals try cases hStep
  case pageTableUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      exact RecordsStage.pageTableUnmap hStep
    all_goals try cases hStep

/-! ### The wrapping steps of the capability dispatch -/

/-- The tail every waking arm ends with: clear the woken receiver's stash, then
stage the delivered frames. -/
theorem clearStashStage_recordsStage {st s st' : SystemState}
    {woken? : Option SeLe4n.ThreadId} {stage : SystemState → SystemState}
    (hS : RecordsStage st s) (hStage : ∀ x, RecordsStage x (stage x))
    (h : (match clearWokenReceiverStash woken? s with
      | .error e => .error e
      | .ok ((), s') => .ok ((), stage s')) =
        (.ok ((), st') : Except KernelError (Unit × SystemState))) :
    RecordsStage st st' := by
  split at h
  · cases h
  · rename_i s3 hClr
    cases h
    exact hS.trans ((RecordsStage.of_frameK fun hI =>
      RecordsFrame.clearWokenReceiverStash woken? hI hClr).trans (hStage _))

/-- A delivered-frame staging. -/
theorem stageWokenDelivery_recordsStage (x : SystemState) (w : Option SeLe4n.ThreadId) (n : Nat) :
    RecordsStage x (Architecture.stageWokenDelivery x w n) :=
  .of_frameK fun hI => RecordsFrame.stageWokenDelivery x w n hI

/-- The two badge stagings a signal arm ends with. -/
theorem stageWokenDeliveryTwice_recordsStage (x : SystemState) (w p : Option SeLe4n.ThreadId) :
    RecordsStage x (Architecture.stageWokenDelivery
      (Architecture.stageWokenDelivery x w 0) p 0) :=
  (stageWokenDelivery_recordsStage x w 0).trans (stageWokenDelivery_recordsStage _ p 0)

/-- A return-frame write. -/
theorem writeReturnFrameToTcb_recordsStage (x : SystemState) (t : SeLe4n.ThreadId)
    (f : Architecture.SyscallReturnFrame) : RecordsStage x (Architecture.writeReturnFrameToTcb x t f) :=
  .of_frameK fun hI => RecordsFrame.writeReturnFrameToTcb x t f hI

/-- **Every arm `dispatchWithCapChecked` routes keeps the records**, the
capability-only arms it delegates, the IPC arms, the audit read and drain and
the declassification included.  The IPC arms read the reachable state the
deletes carry and the running thread, `.ready` in IPC; the reply-receive
answers its caller as the caller's fault record selects
(`RecordsStage.replyRecvTransferOnCore`). -/
theorem dispatchWithCapChecked_recordsStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st st' : SystemState) (P : RecordsArmPremises st) (hCaller : CallerReady st tid)
    (h : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    RecordsStage st st' := by
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid executingCore with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_recordsStage decoded cap tid executingCore k st st' hC P
      (dispatchCapabilityOnlyChecked_ok hC h)
  | none =>
  rw [hC] at h
  dsimp only at h
  cases hId : decoded.syscallId <;> rw [hId] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.auditRead =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    exact (RecordsStage.of_frameK fun hI => RecordsFrame.auditReadFromCore hI hA).trans
      (writeReturnFrameToTcb_recordsStage _ _ _)
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    exact (RecordsStage.of_frameK fun hI => RecordsFrame.auditDrainVisiblePrefix hI hA).trans
      (writeReturnFrameToTcb_recordsStage _ _ _)
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h
    rename_i hSend
    exact clearStashStage_recordsStage
      (RecordsStage.of_fst_eq (RecordsStage.endpointSendCrossCoreDispatchChecked P.deletes.1 hCaller)
        hSend)
      (fun x => stageWokenDelivery_recordsStage x _ _) h
  case none.receive.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ _ hRecv _ stDon hHand
    cases h
    exact (RecordsStage.of_fst_eq (RecordsStage.endpointReceiveDualWithCapsOnCore P.deletes.1 hCaller)
      hRecv).trans
      (((RecordsStage.of_frameK fun hI => RecordsFrame.applyReceiveRendezvousHandoff hI hHand).trans
        (RecordsStage.of_frameK fun hI => RecordsFrame.stageWokenSendCompletion _ _ hI)).trans
        (RecordsStage.of_frameK fun hI => RecordsFrame.stageDeliveredMessage _ _ _ hI))
  case none.call.object epId =>
    split at h
    · rename_i hCall
      cases h
      exact (RecordsStage.of_fst_eq
        (RecordsStage.endpointCallCrossCoreDispatchChecked P.deletes.1 hCaller) hCall).trans
        (stageWokenDelivery_recordsStage _ _ _)
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact RecordsStage.replyTransferOnCoreChecked h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hX
    cases h
    exact (RecordsStage.replyRecvTransferOnCore P.deletes.1 hCaller hX).trans
      (RecordsStage.of_frameK fun hI => RecordsFrame.stageDeliveredMessage _ _ _ hI)
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · exact .of_frameK fun hI => RecordsFrame.cspaceMintWithCdt hI h
      · cases h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · exact .of_frameK fun hI => RecordsFrame.cspaceCopy hI h
    · cases h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · exact .of_frameK fun hI => RecordsFrame.cspaceMove hI h
    · cases h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold registerServiceChecked at h
    split at h
    · exact .of_frameK fun hI => RecordsFrame.registerService hI h
    · cases h
  case none.notificationSignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_recordsStage
        (RecordsStage.of_fst_eq
          (RecordsStage.notificationSignalBoundCrossCoreDispatchChecked P.deletes.1) hSig)
        (fun x => stageWokenDeliveryTwice_recordsStage x _ _) h
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hW
      cases h
      exact (RecordsStage.of_fst_eq
        (RecordsStage.notificationWaitCrossCoreDispatchChecked P.deletes.1 hCaller) hW).trans
        (writeReturnFrameToTcb_recordsStage _ _ _)
    · rename_i hW
      cases h
      exact RecordsStage.of_fst_eq
        (RecordsStage.notificationWaitCrossCoreDispatchChecked P.deletes.1 hCaller) hW
    · cases h
  case none.declassify.object targetId =>
    exact .of_frameK fun hI => RecordsFrame.declassifyObjectFromCore hI h
  case none.declassifySignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_recordsStage
        (RecordsStage.of_fst_eq (RecordsStage.notificationSignalDeclassifiedOnCore P.deletes.1) hSig)
        (fun x => stageWokenDeliveryTwice_recordsStage x _ _) h
    · cases h

/-- **The taint pass keeps the records**: it writes the taint words alone. -/
theorem applySyscallTaint_recordsStage (plan : TaintPlan) (pre post : SystemState) :
    RecordsStage post (applySyscallTaint plan pre post) :=
  .of_frameK fun hI => RecordsFrame.of_agreeOffTaint
    (applySyscallTaint_objectsAgreeOffTaint _ _ _) (by rw [applySyscallTaint_frame])
    (applySyscallTaint_invExt hI) (by rw [applySyscallTaint_machine])

/-- **The checked syscall dispatch keeps the records**: the yield, the
capability resolution (a read, so the arm runs on the dispatcher's state and
reads its premises there), the routed arm, and the taint pass, which writes the
taint words alone. -/
theorem dispatchSyscallChecked_recordsStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st st' : SystemState)
    (P : RecordsArmPremises st) (hCaller : CallerReady st tid)
    (h : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    RecordsStage st st' := by
  unfold dispatchSyscallChecked at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact .of_frameK fun hI => RecordsFrame.yieldOnCore hI hYieldOk
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  split at h <;> try (cases h; done)
  cases hTF : syscallChecksTargetFirst decoded.syscallId <;>
    simp only [hTF, Bool.false_eq_true, ↓reduceIte] at h
  all_goals
    split at h
    · cases h
    rename_i stPost hD
    cases h
    refine RecordsStage.trans (b := stPost) ?_ (applySyscallTaint_recordsStage _ _ _)
  · unfold syscallInvoke at hD
    split at hD
    · cases hD
    · rename_i cap s1 hLk
      have hRz := syscallResolveCap_of_lookup _ st cap s1 hLk
      obtain ⟨-, -, -, hStEq⟩ := syscallResolveCap_implies_capability_at_slot _ st cap s1 hRz
      subst hStEq
      exact dispatchWithCapChecked_recordsStage ctx decoded tid executingCore _ cap _ stPost P
        hCaller hD
  · unfold syscallInvokeResolved at hD
    split at hD
    · cases hD
    · rename_i cap s1 hRz
      obtain ⟨-, -, -, hStEq⟩ := syscallResolveCap_implies_capability_at_slot _ st cap s1 hRz
      subst hStEq
      exact dispatchWithCapChecked_recordsStage ctx decoded tid executingCore _ cap _ stPost P
        hCaller hD

end SeLe4n.Kernel
