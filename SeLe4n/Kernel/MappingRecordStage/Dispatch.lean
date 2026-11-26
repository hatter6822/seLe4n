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
declassification arms, and the checked syscall dispatch are `MappingStage`s:
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

/-- **The notification unbind keeps the mappings recorded**: a context and a
notification, each rewritten as the kind it was. -/
theorem unbindSchedContextNotification_mappingStage (st : SystemState)
    (s : SeLe4n.SchedContextId) : SystemState.MappingStage st (unbindSchedContextNotification st s) := by
  refine SystemState.MappingStage.of_invExt fun hInv => ?_
  rcases unbindSchedContextNotification_shape st s hInv with h | ⟨sc, hS, h | ⟨n, ntfn, h1, h⟩⟩
  · rw [h]; exact SystemState.MappingStage.refl st
  · rw [h]; exact updateSchedContext_mappingStage st _ _
  · rw [h]
    exact (updateSchedContext_mappingStage st _ _).trans
      (SystemState.MappingStage.insert (pre := .notification ntfn) rfl h1 rfl
        (by simp [KernelObject.objectType]))

/-- **A context's reply-stack unlink keeps the mappings recorded**: a Reply
stored over a Reply, then a context rewritten as the kind it was. -/
theorem schedContextUnbindReply_mappingStage (st : SystemState) (x : SeLe4n.ObjId) :
    SystemState.MappingStage st (schedContextUnbindReply st x) := by
  refine SystemState.MappingStage.of_invExt fun _ => ?_
  refine schedContextUnbindReply_induct (fun a b => SystemState.MappingStage a b) st x
    (SystemState.MappingStage.refl st) ?_
  intro _ rid r s1 _ _ hR _ hS
  exact (SystemState.MappingStage.storeObject hS ((SystemState.getReply?_eq_some_iff st rid r).mp hR)
    rfl (by simp [KernelObject.objectType])).trans (updateSchedContext_mappingStage s1 _ _)

/-- **`SchedContext_Unbind` keeps the mappings recorded.** -/
theorem schedContextUnbindAllOnCore_mappingStage {vScId : SeLe4n.ValidObjId}
    {ec : Concurrency.CoreId} {st st' : SystemState}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContextOps.schedContextUnbindAllOnCore vScId ec st = .ok (st', sgi?)) :
    SystemState.MappingStage st st' := by
  obtain ⟨stU, hU | ⟨-, hU, -⟩, rfl⟩ := SchedContextOps.schedContextUnbindAllOnCore_ok h
  · obtain ⟨rfl, -⟩ := hU
    exact (unbindSchedContextNotification_mappingStage _ _).trans
      (schedContextUnbindReply_mappingStage _ _)
  · exact (schedContextUnbindOnCore_mappingStage hU).trans
      ((unbindSchedContextNotification_mappingStage _ _).trans
        (schedContextUnbindReply_mappingStage _ _))

/-- **`SchedContext_UnbindObject` on a thread keeps the mappings recorded**: it
is the per-core thread unbind. -/
theorem schedContextUnbindThreadObjectOnCore_mappingStage {vScId : SeLe4n.ValidObjId}
    {tid : SeLe4n.ThreadId} {ec : Concurrency.CoreId} {st st' : SystemState}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContextOps.schedContextUnbindThreadObjectOnCore vScId tid ec st = .ok (st', sgi?)) :
    SystemState.MappingStage st st' :=
  schedContextUnbindOnCore_mappingStage (SchedContextOps.schedContextUnbindThreadObjectOnCore_ok h)

/-- **`SchedContext_UnbindObject` on a notification keeps the mappings
recorded**: it is the notification unbind. -/
theorem schedContextUnbindNotificationObject_mappingStage {vScId : SeLe4n.ValidObjId}
    {n : SeLe4n.ObjId} {st st' : SystemState}
    (h : SchedContextOps.schedContextUnbindNotificationObject vScId n st = .ok ((), st')) :
    SystemState.MappingStage st st' := by
  obtain ⟨-, rfl⟩ := SchedContextOps.schedContextUnbindNotificationObject_ok h
  exact unbindSchedContextNotification_mappingStage _ _

/-- **The bind keeps the mappings recorded**: a context and a notification,
each rewritten as the kind it was, neither holding a mapping fact. -/
theorem schedContextBindNotification_mappingStage {vScId : SeLe4n.ValidObjId}
    {n : SeLe4n.ObjId} {st st' : SystemState}
    (h : schedContextBindNotification vScId n st = .ok ((), st')) :
    SystemState.MappingStage st st' := by
  obtain ⟨hA, rfl⟩ := schedContextBindNotification_ok_admitted h
  obtain ⟨_, ntfn, hS, -, hN, -⟩ := schedContextBindNotificationAdmitted_facts hA
  refine SystemState.MappingStage.of_invExt fun hInv => ?_
  obtain ⟨h1, hEq⟩ := bindNotificationSchedLink_eq hS hN hInv
  rw [hEq]
  exact (updateSchedContext_mappingStage st _ _).trans
    (SystemState.MappingStage.insert (pre := .notification ntfn) rfl h1 rfl
      (by simp [KernelObject.objectType]))


/-- WS-ZA ZA6.32: **the handler issue keeps the mappings recorded**: it writes
the line's state, which no object holds, then installs a handler capability,
which records no mapping, and its derivation edge. -/
theorem irqControlGet_mappingStage {control dst : CSpaceAddr} {line : Nat}
    {st st' : SystemState} (h : irqControlGet control dst line st = .ok ((), st')) :
    MappingStage st st' := by
  unfold irqControlGet at h
  cases hR : irqControlLineRefusal st line with
  | some e => rw [hR] at h; cases h
  | none =>
    rw [hR] at h
    simp only at h
    cases hI : cspaceInsertSlot dst (Capability.irqHandlerOf line)
        (Architecture.setIrqLineSignal st line true) with
    | error e => rw [hI] at h; cases h
    | ok pr =>
      obtain ⟨⟨⟩, st1⟩ := pr
      rw [hI] at h
      injection h with h
      injection h with hu h
      subst h
      refine (MappingStage.of_objects_eq (Architecture.setIrqLineSignal_objects st line true)).trans
        (MappingStage.of_preserves (fun hI0 => ?_) (fun hI0 hL => ?_) fun hI0 hB => ?_)
      · have h1 : st1.objects.invExt := cspaceInsertSlot_objects_invExt hI0 hI
        exact (SystemState.cdtAddChild_reach st1 control dst .mint).invExt h1
      · exact cdtAddChild_preserves_liveMappingsRecorded (cspaceInsertSlot_objects_invExt hI0 hI)
          (cspaceInsertSlot_preserves_liveMappingsRecorded hI0 hI hL)
      · exact cdtAddChild_preserves_bookkeepingAgrees (cspaceInsertSlot_objects_invExt hI0 hI)
          (cspaceInsertSlot_preserves_bookkeepingAgrees hI0 hB hI)

theorem irqControlGetFromCap_mappingStage {tid : SeLe4n.ThreadId} {srcAddr : SeLe4n.CPtr}
    {root? : Option SeLe4n.CPtr}
    {args? : Except KernelError IrqControlGetArgs} {st st' : SystemState}
    (h : irqControlGetFromCap tid srcAddr root? args? st = .ok ((), st')) : MappingStage st st' := by
  obtain ⟨_, _, _, _, _, _, hG⟩ := irqControlGetFromCap_ok tid srcAddr root? args? st st' h
  exact irqControlGet_mappingStage hG

/-- WS-ZA ZA6.32: **the handler bind keeps the mappings recorded**: the node
slot's zombie delete, then the copy of a notification capability. -/
theorem irqHandlerSetNotification_mappingStage {ec : Concurrency.CoreId} {line : Nat}
    {src : CSpaceAddr} {st st' : SystemState} (P : MappingArmPremises st)
    (h : irqHandlerSetNotification ec line src st = .ok ((), st')) : MappingStage st st' := by
  obtain ⟨-, st1, -, -, -, hZ, hC⟩ :=
    irqHandlerSetNotification_ok (objects_invExt_of_capabilityInvariantBundle _ P.caps) h
  exact (cspaceDeleteSlotZombie_mappingStage P hZ).trans
    (cspaceCopy_mappingStage
      (cspaceDeleteSlotZombie_preserves_capabilityInvariantBundle ec _ st st1 P.caps hZ) hC)

/-- WS-ZA ZA6.32: **the handler clear keeps the mappings recorded**: the node
slot's zombie delete. -/
theorem irqHandlerClear_mappingStage {ec : Concurrency.CoreId} {line : Nat}
    {st st' : SystemState} (P : MappingArmPremises st)
    (h : irqHandlerClear ec line st = .ok ((), st')) : MappingStage st st' := by
  unfold irqHandlerClear at h
  split at h
  · cases h
  exact cspaceDeleteSlotZombie_mappingStage P h

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
      cases hDec : decodeMintReplyCapArgs decoded with
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
  case vspaceMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodePageMapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok words =>
          simp only [hDec] at hStep
          cases hX : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with
          | none => simp only [hX] at hStep; cases hStep
          | some rootCPtr =>
            simp only [hX] at hStep
            cases hOps : resolvePageMapOperands tid decoded.capAddr rootCPtr words st with
            | error e => simp only [hOps] at hStep; cases hStep
            | ok p =>
              obtain ⟨_, args⟩ := p
              simp only [hOps] at hStep
              exact vspaceMapOrRemapFromFrameCap_mappingStage P.teardown hStep
    all_goals try cases hStep
  case vspaceUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hR : resolveCallerCapSlot tid decoded.capAddr (syscallRequiredRight .vspaceUnmap) st with
      | error e => simp only [hR] at hStep; cases hStep
      | ok r =>
          obtain ⟨slot, _, _⟩ := r
          simp only [hR] at hStep
          exact vspaceUnmapFrameCap_mappingStage P.teardown hStep
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
    case serviceRegistry _ =>
      replace hStep := serviceEndpointArm_ok hStep
      obtain ⟨_, oid, -, hStep⟩ := hStep
      try dsimp only [] at hStep
      obtain ⟨_, hRev⟩ := revokeServiceByRecordedRegistration_revokeService hStep
      exact revokeService_mappingStage hRev
    all_goals try cases hStep
  case serviceQuery =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case serviceRegistry _ =>
      replace hStep := serviceEndpointArm_ok hStep
      obtain ⟨_, epId, -, hStep⟩ := hStep
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
          exact Architecture.writeCallReturnWord_of_frame (MappingStage _) (MappingStage.refl _)
            (fun _ => writeReturnFrameToTcb_mappingStage _ _ _)
    all_goals try cases hStep
  case schedContextConfigure =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case schedControl core =>
      try dsimp only [] at hStep
      rcases hXc : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with _ | scCPtr
      · simp only [hXc] at hStep; cases hStep
      simp only [hXc] at hStep
      cases hVal : resolveSchedControlConfigureTarget tid core scCPtr decoded.msgInfo.length st with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hDec : decodeSchedContextConfigureArgsChecked decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              split at hStep
              · exact schedControlConfigure_mappingStage hStep
              · cases hStep
    all_goals try cases hStep
  case schedContextBind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hN : resolveSchedContextBindNotificationCode tid
          (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
      | succ k =>
          simp only [hN] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              exact schedContextBindNotification_mappingStage hStep
      | zero =>
          simp only [hN] at hStep
          cases hRes : resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
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
              cases hUn : SchedContextOps.schedContextUnbindAllOnCore vScId
                  executingCore st with
              | error e => simp only [hUn] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hUn] at hStep
                  cases hStep
                  exact schedContextUnbindAllOnCore_mappingStage hUn
    all_goals try cases hStep
  case schedContextUnbindObject =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hN : resolveSchedContextBindNotificationCode tid
          (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
      | succ k =>
          simp only [hN] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              exact schedContextUnbindNotificationObject_mappingStage hStep
      | zero =>
          simp only [hN] at hStep
          cases hRes : resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok vThreadId =>
              simp only [hRes] at hStep
              cases hVal : validateObjIdArg scId with
              | error e => simp only [hVal] at hStep; cases hStep
              | ok vScId =>
                  simp only [hVal] at hStep
                  cases hUn : SchedContextOps.schedContextUnbindThreadObjectOnCore vScId
                      vThreadId.val executingCore st with
                  | error e => simp only [hUn] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hUn] at hStep
                      cases hStep
                      exact schedContextUnbindThreadObjectOnCore_mappingStage hUn
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
              exact schedContextYieldToOnCore_mappingStage hC
    all_goals try cases hStep
  case irqHandlerAck =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      rw [Architecture.irqHandlerAck_ok hStep]
      exact MappingStage.of_objects_eq rfl
    all_goals try cases hStep
  case irqControlGet =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqControl => exact irqControlGetFromCap_mappingStage hStep
    all_goals try cases hStep
  case irqHandlerSetNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      obtain ⟨_, _, _, hS⟩ := irqHandlerSetNotificationFromCap_ok tid executingCore line _ st st' hStep
      exact irqHandlerSetNotification_mappingStage P hS
    all_goals try cases hStep
  case irqHandlerClear =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line => exact irqHandlerClear_mappingStage P hStep
    all_goals try cases hStep
  case tcbBindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      simp only [tcbBindNotificationArm] at hStep
      try dsimp only [] at hStep
      cases hDec : tcbBindNotificationArgsOf st tid decoded.msgInfo.extraCaps with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hCaller : st.getTcb? tid with
          | none => simp only [hCaller] at hStep; cases hStep
          | some callerTcb =>
              simp only [hCaller] at hStep
              try dsimp only [] at hStep
              cases hCap2 : resolveBindNotificationCap { callerId := tid, cspaceRootCap := callerTcb.spaceCells[0], capAddr := args.notificationCPtr, requiredRight := .read } st with
              | error e => simp only [hCap2] at hStep; cases hStep
              | ok notifId =>
                  simp only [hCap2] at hStep
                  exact bindNotification_mappingStage hStep
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
          cases hRes : Lifecycle.Suspend.restartThreadOnCore st vtid executingCore with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok pair =>
              obtain ⟨stU, sgiU⟩ := pair
              simp only [hRes] at hStep
              cases hStep
              rcases Lifecycle.Suspend.restartThreadOnCore_cases hRes with
                hRes | ⟨st1, _, hSus, hRes⟩ | ⟨rfl, _⟩
              · exact (retirePendingFaultForResume_mappingStage st vtid.val).trans
                  (resumeThreadOnCore_mappingStage hRes)
              · exact (suspendThreadOnCore_mappingStage hSus).trans
                  ((retirePendingFaultForResume_mappingStage st1 vtid.val).trans
                    (resumeThreadOnCore_mappingStage hRes))
              · exact MappingStage.refl _
    all_goals try cases hStep
  case tcbSetPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : resolvePriorityAuthority st tid
              (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) with
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
          cases hValC : resolvePriorityAuthority st tid
              (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) with
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
              cases hSet : Architecture.IpcBufferValidation.setIPCBufferOp executingCore st
                  vtid tid (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0)
                  args.bufferAddr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  exact setIPCBufferOp_mappingStage P hSet
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
              cases hR : resolveSetSpace tid decoded.msgInfo.extraCaps args st with
              | error e => simp only [hR] at hStep; cases hStep
              | ok p =>
                  obtain ⟨cn, vr, fh⟩ := p
                  simp only [hR] at hStep
                  cases hSet : copyThreadSpacesZombie executingCore st vtid cn vr args.cspaceRootData fh with
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
          cases hX : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with
          | none => simp only [hX] at hStep; cases hStep
          | some rootCPtr =>
            simp only [hX] at hStep
            cases hR : resolveCallerCapObject tid rootCPtr .write st with
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

/-- **A reply holder's cancel keeps the mappings recorded**: the suspend's IPC
cancel, the chain revert and the `Inactive` write. -/
theorem cancelReplyHolder_mappingStage (st : SystemState) (holder : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) :
    MappingStage st (cancelReplyHolder st holder executingCore) := by
  rcases cancelReplyHolder_cases st holder executingCore with h | ⟨tcb, -, -, h⟩
  · rw [h]; exact MappingStage.refl st
  · rw [h]
    refine (?_ : MappingStage st _).trans (updateTcb_mappingStage _ _ _)
    unfold Lifecycle.Suspend.suspendCancelRevert
    dsimp only
    split
    · exact (cancelIpcKeepingContexts_mappingStage _ _ _).trans
        propagatePipChainCrossCore_mappingStage
    · exact cancelIpcKeepingContexts_mappingStage _ _ _

/-- A receive's busy-reply cancel keeps the mappings recorded. -/
theorem cancelRecvBusyReply_mappingStage (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult) (executingCore : Concurrency.CoreId)
    (st : SystemState) :
    MappingStage st (cancelRecvBusyReply ctx tid gate decoded executingCore st) := by
  unfold cancelRecvBusyReply
  split
  · exact MappingStage.refl st
  · exact cancelReplyHolder_mappingStage _ _ _

/-- **A donation through a notification keeps the mapping records**: it is the
identity or the bind's writes (`schedContextBindPerform_mappingStage`). -/
theorem maybeDonateSchedContext_mappingStage (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) : MappingStage st (maybeDonateSchedContext st n tid) :=
  maybeDonateSchedContext_induct MappingStage st n tid (MappingStage.refl _)
    (fun _ _ _ _ => schedContextBindPerform_mappingStage _ _ _)

/-- **seL4's return on a running receiver keeps the mapping records**: the
context's thread link and the thread's binding written in place, then
reschedule flags. -/
theorem schedContextReturnLinks_mappingStage (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) : MappingStage st (schedContextReturnLinks st vS tid) := by
  unfold schedContextReturnLinks
  split
  · exact MappingStage.refl _
  rename_i sc hSc _
  split
  · exact MappingStage.refl _
  dsimp only
  refine MappingStage.trans ?_ (markKeyChangeFor_mappingStage _ _ _)
  refine MappingStage.trans ?_ (markCandidacyGainFor_mappingStage _ _ _)
  split
  · refine MappingStage.trans ?_ (MappingStage.of_objects_eq
      (SystemState.markReschedulePendingOnCore_objects _ _))
    exact (MappingStage.rewriteObject_schedContext hSc _ _).trans
      (updateTcb_mappingStage _ _ _)
  · exact (MappingStage.rewriteObject_schedContext hSc _ _).trans
      (updateTcb_mappingStage _ _ _)

/-- **The return keeps the mapping records**: seL4's three writes, then the
purge. -/
theorem schedContextReturnPerform_mappingStage (st : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) : MappingStage st (schedContextReturnPerform st vS tid) :=
  (schedContextReturnLinks_mappingStage st vS tid).trans (purgeReplenishment_mappingStage _ _)

/-- **seL4-MCS `maybeReturnSchedContext` is a mapping stage**: the identity, or
seL4's writes and the purge (`schedContextReturnPerform_mappingStage`). -/
theorem maybeReturnSchedContext_mappingStage (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) : MappingStage st (maybeReturnSchedContext st n tid) :=
  maybeReturnSchedContext_induct MappingStage st n tid (MappingStage.refl _)
    (fun vS _ _ _ => schedContextReturnPerform_mappingStage st vS tid)

/-- **seL4 `receiveIPC`'s return keeps the mapping records.** -/
theorem receiveReturnSchedContext_mappingStage (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) : MappingStage st (receiveReturnSchedContext blocks st tid) :=
  receiveReturnSchedContext_induct MappingStage blocks st tid (MappingStage.refl _)
    (fun vS _ _ _ => schedContextReturnPerform_mappingStage st vS tid)

/-- **The `.replyRecv` composite keeps the mapping records**: the reply leg, the
pop, the reply's capability transfer, seL4-MCS `receiveIPC`'s return, the
receive leg, the post-receive donation, the priority hand-off and the answered
caller, each a mapping stage. -/
theorem endpointReplyRecvOnCore_mappingStage {answer : Option Architecture.FaultReplyOutcome}
    {epId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId}
    {msg : IpcMessage} {grant : Bool}
    {executingCore : Concurrency.CoreId} {st st' : SystemState} {summary : CapTransferSummary}
    (h : endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg grant executingCore st
      = .ok (summary, st')) : MappingStage st st' := by
  unfold endpointReplyRecvAnsweringOnCore at h
  dsimp only at h
  have hR := endpointReplyOnCore_mappingStage (replier := tid) (target := prevCaller)
    (msg := msg) (executingCore := executingCore) (st := st)
  revert h hR
  generalize endpointReplyOnCore tid prevCaller msg executingCore st = r1
  obtain ⟨st1, res1⟩ := r1
  cases res1 with
  | error _ => intro h; cases h
  | ok _ =>
  intro h hR
  dsimp only at h hR
  split at h
  · cases h
  rename_i ret st1q hPop
  have hP := replyRecvPopDonation_mappingStage hPop
  split at h
  · cases h
  rename_i xs st1p hX
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX
  have hXs := receiveTransferCaps_mappingStage hX
  -- the caller's answer, in the reply step (WS-SX SX32)
  have hA := replyRecvAnswerCaller_mappingStage answer st1p prevCaller xs.capInfo
  generalize replyRecvAnswerCaller answer st1p prevCaller xs.capInfo = st1a at h hA
  have hRet := receiveReturnSchedContext_mappingStage true st1a tid
  have hV := endpointReceiveDualWithCapsOnCore_mappingStage (endpointId := epId)
    (receiver := tid) (replyId := some rid)
    (executingCore := executingCore) (st := receiveReturnSchedContext true st1a tid)
  revert h hV
  generalize endpointReceiveDualWithCapsOnCore epId tid (some rid) executingCore
    (receiveReturnSchedContext true st1a tid) = r2
  obtain ⟨st2, res2⟩ := r2
  cases res2 with
  | error _ => intro h; cases h
  | ok q =>
  obtain ⟨nextThread, summ, _⟩ := q
  intro h hV
  dsimp only at h hV
  split at h
  · cases h
  rename_i st3 hPost
  cases h
  exact ((((((hR.trans hP).trans hXs).trans hA).trans hRet).trans hV).trans
    (replyRecvPostReceiveDonation_mappingStage hPost)).trans
    (applyReceiveLegPipHandoff_mappingStage _ _ _ _ _)

/-- **seL4's `sendSignal` keeps the mapping records**: the wake's writes, then
the donation's. -/
theorem sendSignalOnCore_mappingStage {n : SeLe4n.ObjId}
    {badge : SeLe4n.Badge} {c : Concurrency.CoreId} {st : SystemState} :
    MappingStage st (sendSignalOnCore n badge c st).1 :=
  sendSignalOnCore_induct (MappingStage st) n badge c st
    notificationSignalBoundOnCore_mappingStage
    (fun t _ _ _ => notificationSignalBoundOnCore_mappingStage.trans
      (maybeDonateSchedContext_mappingStage _ n t))

/-- **The declassifying signal's dispatch keeps the mapping records**: the
declassifying signal, then seL4's `sendSignal` donation. -/
theorem notificationSignalDeclassifiedCrossCoreDispatch_mappingStage (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : Concurrency.CoreId) (st : SystemState) :
    MappingStage st
      (notificationSignalDeclassifiedCrossCoreDispatch ctx declPolicy notificationId badge c st).1 :=
  have hS := notificationSignalDeclassifiedOnCore_mappingStage ctx declPolicy notificationId badge c st
  notificationSignalDeclassifiedCrossCoreDispatch_induct (MappingStage st) ctx declPolicy
    notificationId badge c st hS
    (fun t _ _ _ => hS.trans (maybeDonateSchedContext_mappingStage _ notificationId t))

theorem notificationSignalBoundCrossCoreDispatchChecked_mappingStage {ctx : LabelingContext}
    {notificationId : SeLe4n.ObjId} {signaler : SeLe4n.ThreadId} {badge : SeLe4n.Badge}
    {executingCore : Concurrency.CoreId} {st : SystemState} :
    MappingStage st (notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler
      badge executingCore st).1 :=
  notificationSignalBoundCrossCoreDispatchChecked_induct (MappingStage st) ctx notificationId
    signaler badge executingCore st (MappingStage.refl _) sendSignalOnCore_mappingStage

/-- **A receive that completes its bound notification keeps the mapping
records**: the checked wait's consumption and the badge register. -/
theorem completeSignalArm_mappingStage {ctx : LabelingContext} {tid : SeLe4n.ThreadId}
    {nid : SeLe4n.ObjId} {c : Concurrency.CoreId} {st st' : SystemState}
    (h : completeSignalArm ctx tid nid c st = .ok ((), st')) : MappingStage st st' := by
  unfold completeSignalArm at h
  split at h
  · rename_i hW
    cases h
    exact ((MappingStage.of_fst_eq notificationWaitCrossCoreDispatchChecked_mappingStage hW).trans
      (writeReturnFrameToTcb_mappingStage _ _ _)).trans
      (maybeDonateSchedContext_mappingStage _ _ _)
  · rename_i hW
    cases h
    exact (MappingStage.of_fst_eq notificationWaitCrossCoreDispatchChecked_mappingStage hW).trans
      (maybeReturnSchedContext_mappingStage _ _ _)
  · cases h

/-- **A reply-receive whose receive completes its bound notification keeps the
mapping records**: the reply, then the completion. -/
theorem replyRecvCompletesSignalArm_mappingStage {ctx : LabelingContext}
    {tid prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool}
    {c : Concurrency.CoreId} {st st' : SystemState}
    (h : replyRecvCompletesSignalArm ctx tid prevCaller label msg grant c st = .ok ((), st')) :
    MappingStage st st' := by
  obtain ⟨st1, hR, hOr⟩ := replyRecvCompletesSignalArm_split h
  rcases hOr with rfl | ⟨_, _, hC⟩
  · exact replyTransferOnCoreChecked_mappingStage hR
  · exact (replyTransferOnCoreChecked_mappingStage hR).trans (completeSignalArm_mappingStage hC)

/-- **The receive past its gate and busy-reply cancel keeps the mapping
records**: the bound notification completed, `NBRecv`'s failure, or the
per-core receive with its hand-off and delivery. -/
theorem receiveResolvedArm_mappingStage {ctx : LabelingContext} {decoded : SyscallDecodeResult}
    {gate : SyscallGate} {tid : SeLe4n.ThreadId} {epId : SeLe4n.ObjId}
    {c : Concurrency.CoreId} {st st' : SystemState}
    (h : receiveResolvedArm ctx decoded gate tid epId c st = .ok ((), st')) :
    MappingStage st st' := by
  unfold receiveResolvedArm at h
  split at h
  · cases h
  split at h
  · exact completeSignalArm_mappingStage h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  · cases h; exact writeReturnFrameToTcb_mappingStage _ _ _
  rename_i summ _ hRecv _ stDon hHand
  cases h
  exact (receiveReturnSchedContext_mappingStage _ _ _).trans
    ((MappingStage.of_fst_eq endpointReceiveDualWithCapsOnCore_mappingStage hRecv).trans
    ((applyReceiveRendezvousHandoff_mappingStage hHand).trans
      (stageDeliveredMessage_mappingStage _ _ _)))

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
    exact (auditReadFromCore_mappingStage hA).trans
      (Architecture.writeCallReturnWord_of_frame (MappingStage _) (MappingStage.refl _)
        (fun _ => writeReturnFrameToTcb_mappingStage _ _ _))
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    exact (auditDrainVisiblePrefix_mappingStage hA).trans
      (Architecture.writeCallReturnWord_of_frame (MappingStage _) (MappingStage.refl _)
        (fun _ => writeReturnFrameToTcb_mappingStage _ _ _))
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h; exact MappingStage.refl _
    split at h
    · cases h
    rename_i hSend
    exact clearStashStage_mappingStage
      (MappingStage.of_fst_eq endpointSendCrossCoreDispatchChecked_mappingStage hSend)
      (fun x => stageWokenDelivery_mappingStage x _ _) h
  case none.receive.object epId =>
    split at h
    · cases h
    exact (cancelRecvBusyReply_mappingStage ctx tid gate decoded executingCore st).trans
      (receiveResolvedArm_mappingStage h)
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
  case none.serviceRegister.serviceRegistry _ =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    replace h := serviceEndpointArm_ok h
    obtain ⟨_, epId, -, h⟩ := h
    try dsimp only at h
    unfold registerServiceChecked at h
    split at h
    · exact registerService_mappingStage h
    · cases h
  case none.notificationSignal.object notifId =>
    try dsimp only at h
    split at h
    · rename_i hSig
      cases h
      exact (MappingStage.of_fst_eq notificationSignalBoundCrossCoreDispatchChecked_mappingStage hSig)
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · cases h; exact writeReturnFrameToTcb_mappingStage _ _ _
    exact completeSignalArm_mappingStage h
  case none.replyRecv.object epId =>
    -- the reply skipped (an extra capability fails, or the reply answers no
    -- caller): the receive runs on the busy reply's cancel
    have hRecvLeg : ∀ {st'}, receiveResolvedArm ctx decoded gate tid epId executingCore
        (cancelRecvBusyReply ctx tid gate decoded executingCore st) = .ok ((), st') →
        MappingStage st st' := by
      intro st' h
      exact (cancelRecvBusyReply_mappingStage ctx tid gate decoded executingCore st).trans
        (receiveResolvedArm_mappingStage h)
    split at h
    · cases h
    split at h
    · exact hRecvLeg h
    split at h
    · cases h
    · exact hRecvLeg h
    repeat' split at h
    -- WS-SX SX33: a refused reply runs the receive alone, as the skip does
    all_goals first | (cases h; done) | (exact hRecvLeg h) | skip
    · exact replyRecvCompletesSignalArm_mappingStage h
    rename_i summ stR hRR
    cases h
    exact (endpointReplyRecvOnCore_mappingStage hRR).trans (stageDeliveredMessage_mappingStage _ _ _)
  case none.declassify.auditTrail code =>
    split at h
    · cases h
    · exact declassifyObjectFromCore_mappingStage h
  case none.declassifySignal.auditTrail code =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      cases h
      exact (MappingStage.of_fst_eq (notificationSignalDeclassifiedCrossCoreDispatch_mappingStage _ _ _ _ _ _) hSig)
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
  split at h
  · cases h
  rename_i stPost hD
  cases h
  refine MappingStage.trans (st' := stPost) ?_
    (MappingStage.of_objectsAgreeOffTaint applySyscallTaint_invExt
      (applySyscallTaint_objectsAgreeOffTaint _ _ _)
      (applySyscallTaint_ghostsKept _ _ _))
  obtain ⟨cap, -, -, hD⟩ := syscallInvokeTyped_ok _ _ _ st () stPost hD
  exact dispatchWithCapChecked_mappingStage ctx decoded tid executingCore _ cap _ stPost P hD

end SeLe4n.Kernel
