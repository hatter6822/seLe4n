/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Scheduling

/-!
# Every kernel entry keeps the run-queue link agreement

WS-ZA ZA4.5 part 2.  The capability-only dispatch, the capability dispatch, the
checked syscall dispatch, the timer tick and the reschedule interrupt are
`RunQueueStage`s: composed from the per-arm stages, so the run queues agree with
the threads' run-queue links after every entry that started from agreement.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- The capability-only dispatch keeps the run queues in agreement with the
threads' links on every arm.  The retype arm reads the detached-target pack the
invariant payoff reads; nothing else is assumed. -/
theorem dispatchCapabilityOnly_runQueueStage
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (k : Kernel Unit) (st st' : SystemState)
    (hArm : dispatchCapabilityOnly decoded cap tid executingCore = some k)
    (hPack : capabilityDispatchQuiescence decoded cap st)
    (hStep : k st = .ok ((), st')) :
    RunQueueStage st st' := by
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
          exact cspaceDeleteSlotFinalising_runQueueStage hStep
    all_goals try cases hStep
  case cspaceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceDeleteArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          exact cspaceRevokeCdtFinalising_runQueueStage hStep
    all_goals try cases hStep
  case mintReplyCap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceCopyArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          exact mintReplyCapWithCdt_runQueueStage hStep
    all_goals try cases hStep
  case untypedRetype =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      exact untypedRetypeFromCap_runQueueStage hStep
    all_goals try cases hStep
  case untypedReset =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      exact untypedResetWithShootdown_runQueueStage hStep
    all_goals try cases hStep
  case lifecycleRetype =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeLifecycleRetypeArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          exact lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_runQueueStage
              (objectOfKernelType_withIdentity_replacementFresh args.newType args.size args.targetObj)
              (hPack.retypeDetached args hSy hDec) hStep
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
          · exact vspaceMapFromFrameCap_runQueueStage hStep
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
          · exact vspaceUnmapPageWithShootdownAndIcacheBroadcast_runQueueStage hStep
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
          · exact vspaceUnifyInstructionPage_runQueueStage hStep
    all_goals try cases hStep
  case serviceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeServiceRevokeArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          exact revokeService_runQueueStage hStep
    all_goals try cases hStep
  case serviceQuery =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object epId =>
      try dsimp only [] at hStep
      cases hLkS : lookupServiceByCap epId st with
      | error e => simp only [hLkS] at hStep; cases hStep
      | ok pair =>
          obtain ⟨reg, st1⟩ := pair
          simp only [hLkS] at hStep
          have hStEq : st1 = st := lookupServiceByCap_preserves_state epId st reg st1 hLkS
          subst hStEq
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
          subst hStep
          exact writeReturnFrameToTcb_runQueueStage _ _ _
    all_goals try cases hStep
  case schedContextConfigure =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hDec : decodeSchedContextConfigureArgsChecked decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              exact schedContextConfigure_runQueueStage hStep
    all_goals try cases hStep
  case schedContextBind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hRes : resolveSchedContextBindThread tid decoded st with
      | error e => simp only [hRes] at hStep; cases hStep
      | ok vThreadId =>
          simp only [hRes] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              exact schedContextBind_runQueueStage hStep
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
                  exact schedContextUnbindOnCore_runQueueStage hUn
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
                  cases hCap2 : syscallLookupCap { callerId := tid, cspaceRoot := callerTcb.cspaceRoot, capAddr := SeLe4n.CPtr.ofNat args.notificationCPtr, capDepth := rootCn.depth, requiredRight := .write } st with
                  | error e => simp only [hCap2] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨ntfnCap, stL⟩ := pair
                      simp only [hCap2] at hStep
                      cases hNT : ntfnCap.target with
                      | object notifId =>
                          simp only [hNT] at hStep
                          exact bindNotification_runQueueStage hStep
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
          exact unbindNotification_runQueueStage hUn
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
                  exact suspendThreadOnCore_runQueueStage hSus
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
              exact (retirePendingFaultForResume_runQueueStage st vtid.val).trans
                  (resumeThreadOnCore_runQueueStage hRes)
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
                      exact setPriorityOnCore_runQueueStage hSet
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
                      exact setMCPriorityOnCore_runQueueStage hSet
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
                  exact setIPCBufferOp_runQueueStage hSet
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
                      exact setThreadCpuAffinityOnCore_runQueueStage hSet
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
                  exact setThreadFaultHandlerOp_runQueueStage hSet
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
                  cases hSet : setThreadSpace st vtid cn vr with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok stU =>
                      simp only [hSet] at hStep
                      cases hStep
                      exact setThreadSpace_runQueueStage hSet
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
              exact pageTableMap_runQueueStage hStep
    all_goals try cases hStep
  case pageTableUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      exact pageTableUnmap_runQueueStage hStep
    all_goals try cases hStep

/-! ### The wrapping steps of the capability dispatch -/

/-- Resolving the extra capabilities mints CDT nodes only. -/
theorem resolveExtraCaps_runQueueStage (cspaceRoot : SeLe4n.ObjId)
    (capAddrs : Array SeLe4n.CPtr) (depth : Nat) (granted : Bool) (st : SystemState) :
    RunQueueStage st (resolveExtraCaps cspaceRoot capAddrs depth granted st).2 :=
  let h := resolveExtraCaps_objects_scheduler_eq cspaceRoot capAddrs depth granted st
  RunQueueStage.of_frame h.1 (by rw [h.2]) (by rw [h.2])

/-- Clearing a woken receiver's stash rewrites one TCB's stash field. -/
theorem clearWokenReceiverStash_runQueueStage (receiver? : Option SeLe4n.ThreadId)
    {st st' : SystemState} (h : clearWokenReceiverStash receiver? st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold clearWokenReceiverStash at h
  split at h
  · cases h; exact RunQueueStage.refl _
  · split at h
    · rename_i rTcb hT
      split at h
      · exact storeObject_tcbOver_runQueueStage hT h (fun _ => rfl)
      · cases h; exact RunQueueStage.refl _
    · cases h; exact RunQueueStage.refl _

/-- Read a pair-returning transition's stage off the equation naming its result. -/
theorem runQueueStage_of_pair_eq {α : Type} {st s : SystemState} {p : SystemState × α}
    {r : α} (hS : RunQueueStage st p.1) (hEq : p = (s, r)) : RunQueueStage st s := by
  subst hEq; exact hS

/-- The tail every waking arm ends with: clear the woken receiver's stash, then
stage the delivered frames. -/
theorem clearStashStage_runQueueStage {st s st' : SystemState}
    {woken? : Option SeLe4n.ThreadId} {stage : SystemState → SystemState}
    (hS : RunQueueStage st s) (hStage : ∀ x, RunQueueStage x (stage x))
    (h : (match clearWokenReceiverStash woken? s with
      | .error e => .error e
      | .ok ((), s') => .ok ((), stage s')) =
        (.ok ((), st') : Except KernelError (Unit × SystemState))) :
    RunQueueStage st st' := by
  split at h
  · cases h
  · rename_i s3 hClr
    cases h
    exact (hS.trans (clearWokenReceiverStash_runQueueStage woken? hClr)).trans (hStage _)

/-- The two badge stagings a signal arm ends with. -/
theorem stageWokenDeliveryTwice_runQueueStage (x : SystemState) (w p : Option SeLe4n.ThreadId) :
    RunQueueStage x (Architecture.stageWokenDelivery
      (Architecture.stageWokenDelivery x w 0) p 0) :=
  (stageWokenDelivery_runQueueStage x w 0).trans (stageWokenDelivery_runQueueStage _ p 0)

theorem endpointSendCrossCoreDispatchChecked_runQueueStage (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (rights : AccessRightSet) (base : SeLe4n.Slot) (c : Concurrency.CoreId)
    (st : SystemState) :
    RunQueueStage st
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg rights base c st).1 := by
  unfold endpointSendCrossCoreDispatchChecked
  repeat' split
  all_goals first
    | exact RunQueueStage.refl _
    | exact endpointSendDualWithCapsOnCore_runQueueStage _ _ _ _ _ _ _

theorem endpointCallCrossCoreDispatchChecked_runQueueStage (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (rights : AccessRightSet) (base : SeLe4n.Slot) (c : Concurrency.CoreId)
    (st : SystemState) :
    RunQueueStage st
      (endpointCallCrossCoreDispatchChecked ctx endpointId caller msg rights base c st).1 := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · exact endpointCallCrossCoreDispatch_runQueueStage _ _ _ _ _ _ _
  · exact RunQueueStage.refl _

theorem notificationSignalBoundCrossCoreDispatchChecked_runQueueStage (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (c : Concurrency.CoreId) (st : SystemState) :
    RunQueueStage st (notificationSignalBoundCrossCoreDispatchChecked ctx notificationId
      signaler badge c st).1 := by
  unfold notificationSignalBoundCrossCoreDispatchChecked
  repeat' split
  all_goals first
    | exact RunQueueStage.refl _
    | exact notificationSignalBoundOnCore_runQueueStage _ _ _ _

theorem notificationWaitCrossCoreDispatchChecked_runQueueStage (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (c : Concurrency.CoreId)
    (st : SystemState) :
    RunQueueStage st
      (notificationWaitCrossCoreDispatchChecked ctx notificationId waiter c st).1 := by
  unfold notificationWaitCrossCoreDispatchChecked
  split
  · exact notificationWaitOnCore_runQueueStage _ _ _ _
  · exact RunQueueStage.refl _

/-- The declassified signal: the bound signal, then the audit records, which
touch the trail alone. -/
theorem notificationSignalDeclassifiedOnCore_runQueueStage (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : Concurrency.CoreId) (st : SystemState) :
    RunQueueStage st
      (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st).1 := by
  unfold notificationSignalDeclassifiedOnCore
  split
  · exact RunQueueStage.refl _
  split
  · split <;> exact RunQueueStage.refl _
  dsimp only
  split
  · exact RunQueueStage.refl _
  have hB := notificationSignalBoundOnCore_runQueueStage notificationId badge c st
  generalize notificationSignalBoundOnCore notificationId badge c st = r at hB
  obtain ⟨st1, res⟩ := r
  cases res with
  | error _ => exact RunQueueStage.refl _
  | ok sgi =>
    dsimp only at hB ⊢
    split
    · exact RunQueueStage.refl _
    · rename_i st2 hRec
      rw [recordDeclassifiedHops_frame _ _ _ _ _ hRec]
      exact hB.trans (RunQueueStage.of_frame rfl rfl rfl)

/-- **Every arm `dispatchWithCapChecked` routes keeps the run queues in
agreement with the threads' links**, the capability-only arms it delegates
included. -/
theorem dispatchWithCapChecked_runQueueStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st st' : SystemState) (hPack : capabilityDispatchQuiescence decoded cap st)
    (h : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid executingCore with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_runQueueStage decoded cap tid executingCore k st st' hC hPack h
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
    rw [auditReadFromCore_frame _ _ _ _ _ _ _ hA]
    exact writeReturnFrameToTcb_runQueueStage _ _ _
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    unfold auditDrainVisiblePrefix at hA
    split at hA
    · cases hA
      refine RunQueueStage.trans ?_ (writeReturnFrameToTcb_runQueueStage _ _ _)
      exact RunQueueStage.of_frame rfl rfl rfl
    · cases hA
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    generalize hR : resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
      gate.capDepth (cap.rights.mem .grant) st = r at h
    obtain ⟨caps, s1⟩ := r
    have hF1 : RunQueueStage st s1 := by
      have := resolveExtraCaps_runQueueStage gate.cspaceRoot (decodeExtraCapAddrs decoded)
        gate.capDepth (cap.rights.mem .grant) st
      rw [hR] at this; exact this
    dsimp only at h
    split at h
    · cases h
    rename_i hSend
    exact clearStashStage_runQueueStage
      (hF1.trans (runQueueStage_of_pair_eq
        (endpointSendCrossCoreDispatchChecked_runQueueStage _ _ _ _ _ _ _ _) hSend))
      (fun x => stageWokenDelivery_runQueueStage x _ _) h
  case none.receive.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ _ hRecv _ stDon hHand
    cases h
    exact (((runQueueStage_of_pair_eq
      (endpointReceiveDualWithCapsOnCore_runQueueStage _ _ _ _ _ _ _) hRecv).trans
      (applyReceiveRendezvousHandoff_runQueueStage hHand)).trans
      (stageWokenSendCompletion_runQueueStage _ _)).trans
      (stageDeliveredMessage_runQueueStage _ _ _)
  case none.call.object epId =>
    generalize hR : resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
      gate.capDepth (cap.rights.mem .grant) st = r at h
    obtain ⟨caps, s1⟩ := r
    have hF1 : RunQueueStage st s1 := by
      have := resolveExtraCaps_runQueueStage gate.cspaceRoot (decodeExtraCapAddrs decoded)
        gate.capDepth (cap.rights.mem .grant) st
      rw [hR] at this; exact this
    dsimp only at h
    split at h
    · rename_i hCall
      cases h
      exact (hF1.trans (runQueueStage_of_pair_eq
        (endpointCallCrossCoreDispatchChecked_runQueueStage _ _ _ _ _ _ _ _) hCall)).trans
        (stageWokenDelivery_runQueueStage _ _ _)
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact replyTransferOnCoreChecked_runQueueStage h
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · exact cspaceMintWithCdt_runQueueStage h
      · cases h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · exact cspaceCopy_runQueueStage h
    · cases h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · exact cspaceMove_runQueueStage h
    · cases h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold registerServiceChecked at h
    dsimp only at h
    split at h
    · exact registerService_runQueueStage h
    · cases h
  case none.notificationSignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_runQueueStage (runQueueStage_of_pair_eq
        (notificationSignalBoundCrossCoreDispatchChecked_runQueueStage _ _ _ _ _ _) hSig)
        (fun x => stageWokenDeliveryTwice_runQueueStage x _ _) h
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hW
      cases h
      exact (runQueueStage_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_runQueueStage _ _ _ _ _) hW).trans
        (writeReturnFrameToTcb_runQueueStage _ _ _)
    · rename_i hW
      cases h
      exact runQueueStage_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_runQueueStage _ _ _ _ _) hW
    · cases h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ stR hRR
    cases h
    exact (endpointReplyRecvOnCore_runQueueStage hRR).trans
      (stageDeliveredMessage_runQueueStage _ _ _)
  case none.declassify.object targetId =>
    unfold declassifyObjectFromCore at h
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rw [(authorizeDeclassificationOnCore_frame _ _ _ _ _ _ _ _ _ h).1]
    exact RunQueueStage.of_frame rfl rfl rfl
  case none.declassifySignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_runQueueStage (runQueueStage_of_pair_eq
        (notificationSignalDeclassifiedOnCore_runQueueStage _ _ _ _ _ _) hSig)
        (fun x => stageWokenDeliveryTwice_runQueueStage x _ _) h
    · cases h

/-- **The checked syscall dispatch keeps the run queues in agreement with the
threads' links**: the yield, the capability resolution (a read), the routed arm,
and the taint pass, which writes the taint ledger alone.  The pack is the
capability-only half of the one the invariant payoff reads. -/
theorem dispatchSyscallChecked_runQueueStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st st' : SystemState)
    (hPack : ∀ (gate : SyscallGate) (cap : Capability),
      syscallResolveCap gate st = .ok (cap, st) → capabilityDispatchQuiescence decoded cap st)
    (h : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold dispatchSyscallChecked at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact yieldOnCore_runQueueStage hYieldOk
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
    refine RunQueueStage.trans (st' := stPost) ?_ (RunQueueStage.of_frame
      (applySyscallTaint_objects _ _ _) (by rw [applySyscallTaint_scheduler])
      (by rw [applySyscallTaint_scheduler]))
  · unfold syscallInvoke at hD
    split at hD
    · cases hD
    · rename_i cap s1 hLk
      have hRz := syscallResolveCap_of_lookup _ st cap s1 hLk
      obtain ⟨-, -, -, hStEq⟩ := syscallResolveCap_implies_capability_at_slot _ st cap s1 hRz
      subst hStEq
      exact dispatchWithCapChecked_runQueueStage ctx decoded tid executingCore _ cap _ stPost
        (hPack _ cap hRz) hD
  · unfold syscallInvokeResolved at hD
    split at hD
    · cases hD
    · rename_i cap s1 hRz
      obtain ⟨-, -, -, hStEq⟩ := syscallResolveCap_implies_capability_at_slot _ st cap s1 hRz
      subst hStEq
      exact dispatchWithCapChecked_runQueueStage ctx decoded tid executingCore _ cap _ stPost
        (hPack _ cap hRz) hD

/-- **Every arm the unchecked `dispatchWithCap` routes keeps the run queues in
agreement with the threads' links**, the capability-only arms included. -/
theorem dispatchWithCap_runQueueStage (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (st st' : SystemState)
    (hPack : capabilityDispatchQuiescence decoded cap st)
    (h : dispatchWithCap decoded tid executingCore gate cap st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold dispatchWithCap at h
  cases hC : dispatchCapabilityOnly decoded cap tid executingCore with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_runQueueStage decoded cap tid executingCore k st st' hC hPack h
  | none =>
  rw [hC] at h
  dsimp only at h
  cases hId : decoded.syscallId <;> rw [hId] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    generalize hR : resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
      gate.capDepth (cap.rights.mem .grant) st = r at h
    obtain ⟨caps, s1⟩ := r
    have hF1 : RunQueueStage st s1 := by
      have := resolveExtraCaps_runQueueStage gate.cspaceRoot (decodeExtraCapAddrs decoded)
        gate.capDepth (cap.rights.mem .grant) st
      rw [hR] at this; exact this
    dsimp only at h
    split at h
    · cases h
    rename_i hSend
    exact clearStashStage_runQueueStage
      (hF1.trans (runQueueStage_of_pair_eq
        (endpointSendDualWithCapsOnCore_runQueueStage _ _ _ _ _ _ _) hSend))
      (fun x => stageWokenDelivery_runQueueStage x _ _) h
  case none.receive.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ _ hRecv _ stDon hHand
    cases h
    exact (((runQueueStage_of_pair_eq
      (endpointReceiveDualWithCapsOnCore_runQueueStage _ _ _ _ _ _ _) hRecv).trans
      (applyReceiveRendezvousHandoff_runQueueStage hHand)).trans
      (stageWokenSendCompletion_runQueueStage _ _)).trans
      (stageDeliveredMessage_runQueueStage _ _ _)
  case none.call.object epId =>
    generalize hR : resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
      gate.capDepth (cap.rights.mem .grant) st = r at h
    obtain ⟨caps, s1⟩ := r
    have hF1 : RunQueueStage st s1 := by
      have := resolveExtraCaps_runQueueStage gate.cspaceRoot (decodeExtraCapAddrs decoded)
        gate.capDepth (cap.rights.mem .grant) st
      rw [hR] at this; exact this
    dsimp only at h
    split at h
    · rename_i hCall
      cases h
      exact (hF1.trans (runQueueStage_of_pair_eq
        (endpointCallCrossCoreDispatch_runQueueStage _ _ _ _ _ _ _) hCall)).trans
        (stageWokenDelivery_runQueueStage _ _ _)
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact replyTransferOnCore_runQueueStage h
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals exact cspaceMintWithCdt_runQueueStage h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact cspaceCopy_runQueueStage h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact cspaceMove_runQueueStage h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact registerService_runQueueStage h
  case none.notificationSignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_runQueueStage (runQueueStage_of_pair_eq
        (notificationSignalBoundOnCore_runQueueStage _ _ _ _) hSig)
        (fun x => stageWokenDeliveryTwice_runQueueStage x _ _) h
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hW
      cases h
      exact (runQueueStage_of_pair_eq (notificationWaitOnCore_runQueueStage _ _ _ _) hW).trans
        (writeReturnFrameToTcb_runQueueStage _ _ _)
    · rename_i hW
      cases h
      exact runQueueStage_of_pair_eq (notificationWaitOnCore_runQueueStage _ _ _ _) hW
    · cases h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ stR hRR
    cases h
    exact (endpointReplyRecvOnCore_runQueueStage hRR).trans
      (stageDeliveredMessage_runQueueStage _ _ _)

/-- **The unchecked syscall dispatch keeps the run queues in agreement with the
threads' links.** -/
theorem dispatchSyscall_runQueueStage (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (st st' : SystemState)
    (hPack : ∀ (gate : SyscallGate) (cap : Capability),
      syscallLookupCap gate st = .ok (cap, st) → capabilityDispatchQuiescence decoded cap st)
    (h : dispatchSyscall decoded tid executingCore st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold dispatchSyscall at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact yieldOnCore_runQueueStage hYieldOk
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  split at h <;> try (cases h; done)
  split at h
  · cases h
  rename_i stPost hD
  cases h
  refine RunQueueStage.trans (st' := stPost) ?_ (RunQueueStage.of_frame
    (applySyscallTaint_objects _ _ _) (by rw [applySyscallTaint_scheduler])
    (by rw [applySyscallTaint_scheduler]))
  unfold syscallInvoke at hD
  split at hD
  · cases hD
  · rename_i cap s1 hLk
    have hRz := syscallResolveCap_of_lookup _ st cap s1 hLk
    obtain ⟨-, -, -, hStEq⟩ := syscallResolveCap_implies_capability_at_slot _ st cap s1 hRz
    subst hStEq
    exact dispatchWithCap_runQueueStage decoded tid executingCore _ cap _ stPost
      (hPack _ cap hLk) hD

end SeLe4n.Kernel
