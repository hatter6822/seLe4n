-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.Capability
import SeLe4n.Kernel.MappingRecordStage.Scheduling
import SeLe4n.Kernel.MappingRecordStage.Retype
import SeLe4n.Kernel.MappingRecordStage.Audit
import SeLe4n.Kernel.MappingRecordStage.Fault

/-! # The dispatchers keep the mappings recorded

The capability-only dispatch, the capability dispatch with its IPC, audit and
declassification arms, the checked syscall dispatch, and the unchecked
capability and syscall dispatch the specification keeps are `MappingStage`s:
each arm is one (`Kernel/MappingRecordStage/*.lean`), the capability resolution
reads, and the taint pass writes the taint ledger alone.  The map, the unmap,
the deletes and the space set read the capability invariants and the teardown's
well-formedness off the dispatcher's state (`MappingArmPremises`): the arm runs
on the state the dispatcher is handed, since its lookups and decodes write
nothing.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState (MappingStage)
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- **The capability-only dispatch keeps the mappings recorded on every arm**:
the map, unmap, deletes and space set from the premises they read, every
other arm from the store's table invariant alone. -/
theorem dispatchCapabilityOnly_mappingStage
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (k : Kernel Unit) (st st' : SystemState)
    (hArm : dispatchCapabilityOnly decoded cap tid executingCore = some k)
    (P : MappingArmPremises st) (hStep : k st = .ok ((), st')) :
    MappingStage st st' := by
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
          exact cspaceDeleteSlotZombie_mappingStage P hStep
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
          exact cspaceRevokeCdtFinalising_mappingStage P hStep
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
          exact mintReplyCapWithCdt_mappingStage P.caps hStep
    all_goals try cases hStep
  case untypedRetype =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      exact untypedRetypeFromCap_mappingStage hStep
    all_goals try cases hStep
  case untypedReset =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      exact untypedResetFromCap_mappingStage hStep
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
          · exact vspaceMapFromFrameCap_mappingStage P.teardown hStep
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
          · exact vspaceUnmapPageWithShootdownAndIcacheBroadcast_mappingStage P.teardown hStep
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
          · exact vspaceUnifyInstructionPage_mappingStage hStep
    all_goals try cases hStep
  case serviceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      obtain ⟨_, hRev⟩ := revokeServiceByRecordedRegistration_revokeService hStep
      exact revokeService_mappingStage hRev
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
          exact writeReturnFrameToTcb_mappingStage _ _ _
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
              · exact schedControlConfigure_mappingStage hStep
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
              exact schedContextBind_mappingStage hStep
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
                  exact schedContextUnbindOnCore_mappingStage hUn
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
              exact schedContextConsumedOnCore_mappingStage hC
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
                          exact bindNotification_mappingStage hStep
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
          exact unbindNotification_mappingStage hUn
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
                  exact suspendThreadOnCore_mappingStage hSus
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
              exact (retirePendingFaultForResume_mappingStage st vtid.val).trans
                  (resumeThreadOnCore_mappingStage hRes)
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
                      exact setPriorityOnCore_mappingStage hSet
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
                      exact setMCPriorityOnCore_mappingStage hSet
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
                  exact setIPCBufferOp_mappingStage hSet
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
                      exact setThreadCpuAffinityOnCore_mappingStage hSet
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
                  exact setThreadFaultHandlerOp_mappingStage hSet
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
                      exact copyThreadSpacesZombie_mappingStage P hSet
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
              exact pageTableMap_mappingStage hStep
    all_goals try cases hStep
  case pageTableUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      exact pageTableUnmap_mappingStage hStep
    all_goals try cases hStep


/-! ### The wrapping steps of the capability dispatch -/

/-- The tail every waking arm ends with: clear the woken receiver's stash, then
stage the delivered frames. -/
theorem clearStashStage_mappingStage {st s st' : SystemState}
    {woken? : Option SeLe4n.ThreadId} {stage : SystemState → SystemState}
    (hS : MappingStage st s) (hStage : ∀ x, MappingStage x (stage x))
    (h : (match clearWokenReceiverStash woken? s with
      | .error e => .error e
      | .ok ((), s') => .ok ((), stage s')) =
        (.ok ((), st') : Except KernelError (Unit × SystemState))) :
    MappingStage st st' := by
  split at h
  · cases h
  · rename_i s3 hClr
    cases h
    exact hS.trans ((clearWokenReceiverStash_mappingStage woken? hClr).trans (hStage _))

/-- The two badge stagings a signal arm ends with. -/
theorem stageWokenDeliveryTwice_mappingStage (x : SystemState) (w p : Option SeLe4n.ThreadId) :
    MappingStage x (Architecture.stageWokenDelivery
      (Architecture.stageWokenDelivery x w 0) p 0) :=
  (stageWokenDelivery_mappingStage x w 0).trans (stageWokenDelivery_mappingStage _ p 0)

/-- **Every arm `dispatchWithCapChecked` routes keeps the mappings recorded**,
the capability-only arms it delegates, the IPC arms, the audit read and drain
and the declassification included. -/
theorem dispatchWithCapChecked_mappingStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st st' : SystemState) (P : MappingArmPremises st)
    (h : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    MappingStage st st' := by
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid executingCore with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_mappingStage decoded cap tid executingCore k st st' hC P
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
    exact (auditReadFromCore_mappingStage hA).trans (writeReturnFrameToTcb_mappingStage _ _ _)
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    exact (auditDrainVisiblePrefix_mappingStage hA).trans (writeReturnFrameToTcb_mappingStage _ _ _)
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h
    rename_i hSend
    exact clearStashStage_mappingStage
      (MappingStage.of_fst_eq endpointSendCrossCoreDispatchChecked_mappingStage hSend)
      (fun x => stageWokenDelivery_mappingStage x _ _) h
  case none.receive.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ _ hRecv _ stDon hHand
    cases h
    exact (MappingStage.of_fst_eq endpointReceiveDualWithCapsOnCore_mappingStage hRecv).trans
      (((applyReceiveRendezvousHandoff_mappingStage hHand).trans
        (stageWokenSendCompletion_mappingStage _ _)).trans
        (stageDeliveredMessage_mappingStage _ _ _))
  case none.call.object epId =>
    split at h
    · rename_i hCall
      cases h
      exact (MappingStage.of_fst_eq endpointCallCrossCoreDispatchChecked_mappingStage hCall).trans
        (stageWokenDelivery_mappingStage _ _ _)
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact replyTransferOnCoreChecked_mappingStage h
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · exact cspaceMintWithCdt_mappingStage P.caps h
      · cases h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · exact cspaceCopy_mappingStage P.caps h
    · cases h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · exact cspaceMove_mappingStage P.caps h
    · cases h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold registerServiceChecked at h
    split at h
    · exact registerService_mappingStage h
    · cases h
  case none.notificationSignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_mappingStage
        (MappingStage.of_fst_eq notificationSignalBoundCrossCoreDispatchChecked_mappingStage hSig)
        (fun x => stageWokenDeliveryTwice_mappingStage x _ _) h
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hW
      cases h
      exact (MappingStage.of_fst_eq notificationWaitCrossCoreDispatchChecked_mappingStage hW).trans
        (writeReturnFrameToTcb_mappingStage _ _ _)
    · rename_i hW
      cases h
      exact MappingStage.of_fst_eq notificationWaitCrossCoreDispatchChecked_mappingStage hW
    · cases h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ stR hRR
    cases h
    exact (endpointReplyRecvOnCore_mappingStage hRR).trans (stageDeliveredMessage_mappingStage _ _ _)
  case none.declassify.object targetId =>
    exact declassifyObjectFromCore_mappingStage h
  case none.declassifySignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_mappingStage
        (MappingStage.of_fst_eq (notificationSignalDeclassifiedOnCore_mappingStage _ _ _ _ _ _) hSig)
        (fun x => stageWokenDeliveryTwice_mappingStage x _ _) h
    · cases h

/-- **The checked syscall dispatch keeps the mappings recorded**: the yield, the
capability resolution (a read, so the arm runs on the dispatcher's state and
reads its premises there), the routed arm, and the taint pass, which writes the
taint ledger alone. -/
theorem dispatchSyscallChecked_mappingStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st st' : SystemState) (P : MappingArmPremises st)
    (h : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    MappingStage st st' := by
  unfold dispatchSyscallChecked at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact yieldOnCore_mappingStage hYieldOk
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
    refine MappingStage.trans (st' := stPost) ?_
      (MappingStage.of_objectsAgreeOffTaint applySyscallTaint_invExt
        (applySyscallTaint_objectsAgreeOffTaint _ _ _))
  · unfold syscallInvoke at hD
    split at hD
    · cases hD
    · rename_i cap s1 hLk
      have hRz := syscallResolveCap_of_lookup _ st cap s1 hLk
      obtain ⟨-, -, -, hStEq⟩ := syscallResolveCap_implies_capability_at_slot _ st cap s1 hRz
      subst hStEq
      exact dispatchWithCapChecked_mappingStage ctx decoded tid executingCore _ cap _ stPost P hD
  · unfold syscallInvokeResolved at hD
    split at hD
    · cases hD
    · rename_i cap s1 hRz
      obtain ⟨-, -, -, hStEq⟩ := syscallResolveCap_implies_capability_at_slot _ st cap s1 hRz
      subst hStEq
      exact dispatchWithCapChecked_mappingStage ctx decoded tid executingCore _ cap _ stPost P hD

/-! ### The unchecked dispatchers

The specification's dispatch without the flow checks, which the trace harness
runs; its arms are the checked dispatch's, ungated. -/

/-- The unchecked reply: the fault reply, or the reply and the delivered frame. -/
theorem replyTransferOnCore_mappingStage {replier callerTid : SeLe4n.ThreadId}
    {mi : MessageInfo} {regs : Array SeLe4n.RegValue} {msg : IpcMessage}
    {executingCore : Concurrency.CoreId} {st st' : SystemState}
    (h : replyTransferOnCore replier callerTid mi regs msg executingCore st = .ok ((), st')) :
    MappingStage st st' := by
  unfold replyTransferOnCore at h
  split at h
  · have hF := faultReplyOnCore_mappingStage (replier := replier) (faulted := callerTid)
      (mi := mi) (regs := regs) (executingCore := executingCore) (st := st)
    revert h hF
    generalize faultReplyOnCore replier callerTid mi regs executingCore st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h; cases h
    | ok _ => intro h hF; cases h; exact hF
  · have hR := endpointReplyCrossCoreDispatch_mappingStage (replier := replier)
      (target := callerTid) (msg := msg) (executingCore := executingCore) (st := st)
    revert h hR
    generalize endpointReplyCrossCoreDispatch replier callerTid msg executingCore st = r
    obtain ⟨s, res⟩ := r
    cases res with
    | error _ => intro h; cases h
    | ok _ =>
      intro h hR
      cases h
      exact hR.trans (stageDeliveredMessage_mappingStage s callerTid 0)

/-- **Every arm the unchecked `dispatchWithCap` routes keeps the mappings
recorded**, the capability-only arms included. -/
theorem dispatchWithCap_mappingStage (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (st st' : SystemState) (P : MappingArmPremises st)
    (h : dispatchWithCap decoded tid executingCore gate cap st = .ok ((), st')) :
    MappingStage st st' := by
  unfold dispatchWithCap at h
  cases hC : dispatchCapabilityOnly decoded cap tid executingCore with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_mappingStage decoded cap tid executingCore k st st' hC P h
  | none =>
  rw [hC] at h
  dsimp only at h
  cases hId : decoded.syscallId <;> rw [hId] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h
    rename_i hSend
    exact clearStashStage_mappingStage
      (MappingStage.of_fst_eq endpointSendDualWithCapsOnCore_mappingStage hSend)
      (fun x => stageWokenDelivery_mappingStage x _ _) h
  case none.receive.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ _ hRecv _ stDon hHand
    cases h
    exact (MappingStage.of_fst_eq endpointReceiveDualWithCapsOnCore_mappingStage hRecv).trans
      (((applyReceiveRendezvousHandoff_mappingStage hHand).trans
        (stageWokenSendCompletion_mappingStage _ _)).trans
        (stageDeliveredMessage_mappingStage _ _ _))
  case none.call.object epId =>
    split at h
    · rename_i hCall
      cases h
      exact (MappingStage.of_fst_eq endpointCallCrossCoreDispatch_mappingStage hCall).trans
        (stageWokenDelivery_mappingStage _ _ _)
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact replyTransferOnCore_mappingStage h
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals exact cspaceMintWithCdt_mappingStage P.caps h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact cspaceCopy_mappingStage P.caps h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact cspaceMove_mappingStage P.caps h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact registerService_mappingStage h
  case none.notificationSignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_mappingStage
        (MappingStage.of_fst_eq notificationSignalBoundOnCore_mappingStage hSig)
        (fun x => stageWokenDeliveryTwice_mappingStage x _ _) h
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hW
      cases h
      exact (MappingStage.of_fst_eq notificationWaitOnCore_mappingStage hW).trans
        (writeReturnFrameToTcb_mappingStage _ _ _)
    · rename_i hW
      cases h
      exact MappingStage.of_fst_eq notificationWaitOnCore_mappingStage hW
    · cases h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ stR hRR
    cases h
    exact (endpointReplyRecvOnCore_mappingStage hRR).trans (stageDeliveredMessage_mappingStage _ _ _)

/-- **The unchecked syscall dispatch keeps the mappings recorded.** -/
theorem dispatchSyscall_mappingStage (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (st st' : SystemState)
    (P : MappingArmPremises st)
    (h : dispatchSyscall decoded tid executingCore st = .ok ((), st')) :
    MappingStage st st' := by
  unfold dispatchSyscall at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact yieldOnCore_mappingStage hYieldOk
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  split at h <;> try (cases h; done)
  split at h
  · cases h
  rename_i stPost hD
  cases h
  refine MappingStage.trans (st' := stPost) ?_
    (MappingStage.of_objectsAgreeOffTaint applySyscallTaint_invExt
        (applySyscallTaint_objectsAgreeOffTaint _ _ _))
  unfold syscallInvoke at hD
  split at hD
  · cases hD
  · rename_i cap s1 hLk
    have hRz := syscallResolveCap_of_lookup _ st cap s1 hLk
    obtain ⟨-, -, -, hStEq⟩ := syscallResolveCap_implies_capability_at_slot _ st cap s1 hRz
    subst hStEq
    exact dispatchWithCap_mappingStage decoded tid executingCore _ cap _ stPost P hD

end SeLe4n.Kernel
