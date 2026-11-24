-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.CapabilityOnly

/-! # The capability-only table keeps the lenders' flow on every arm

WS-SX SX8, SX16.  Each arm of `dispatchCapabilityOnly` is a labelled step
(`LendersStep`): a `LendersFrame`, whose writes keep or shrink every context
stack's head, `prev` link, caller and binding word
(`ContextLenders.CapabilityOnly`); a removal whose pops discharge their owners
at their own pre-states; or a creating bind given its label equation.  The case split mirrors the records'
(`dispatchCapabilityOnly_recordsStage`).  The checked dispatch then needs no
capability-only hypothesis.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **Every capability-only arm is a labelled step**: a lenders' frame, a
removal whose pops discharge their owners at their own pre-states (the delete
chain's finalisation, the suspend's cancel), or a creating bind whose label
equation its label gate admitted (`hBT`, `hBN`: the checked arm's admissions,
`dispatchCapabilityOnlyChecked_lendersStep`). -/
theorem dispatchCapabilityOnly_lendersStep (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (k : Kernel Unit) (st st' : SystemState)
    (hArm : dispatchCapabilityOnly decoded cap tid executingCore = some k)
    (hInv : st.objects.invExt) (hStep : k st = .ok ((), st'))
    (hBT : decoded.syscallId = .schedContextBind → ∀ scId vScId vTid,
      cap.target = .object scId → validateObjIdArg scId = .ok vScId →
      resolveSchedContextBindNotificationCode tid
        (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st = 0 →
      resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st
        = .ok vTid →
      ctx.threadLabelOf vTid.val = ctx.objectLabelOf vScId.val)
    (hBN : decoded.syscallId = .schedContextBind → ∀ scId vScId k,
      cap.target = .object scId → validateObjIdArg scId = .ok vScId →
      resolveSchedContextBindNotificationCode tid
        (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st = k + 1 →
      ctx.objectLabelOf ⟨k⟩ = ctx.objectLabelOf vScId.val) :
    LendersStep ctx st st' := by
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
          exact LendersStep.cspaceDeleteSlotZombie hInv hStep
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
          exact LendersStep.cspaceRevokeCdtFinalising hInv hStep
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
          exact LendersStep.of_frame <| LendersFrame.of_kept (chainObjectsKept.mintReplyCapWithCdt hInv hStep) (RecordsFrame.mintReplyCapWithCdt hInv hStep)
    all_goals try cases hStep
  case untypedRetype =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      exact LendersStep.of_frame <| LendersFrame.untypedRetypeFromCap hInv hStep
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
              exact LendersStep.of_frame <| LendersFrame.vspaceMapOrRemapFromFrameCap hInv hStep
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
          exact LendersStep.of_frame <| LendersFrame.vspaceUnmapFrameCap hInv hStep
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
          · exact LendersStep.of_frame <| LendersFrame.vspaceUnifyInstructionPage hInv hStep
    all_goals try cases hStep
  case serviceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case serviceRegistry _ =>
      replace hStep := serviceEndpointArm_ok hStep
      obtain ⟨_, oid, -, hStep⟩ := hStep
      try dsimp only [] at hStep
      obtain ⟨_, hRev⟩ := revokeServiceByRecordedRegistration_revokeService hStep
      exact LendersStep.of_frame <| LendersFrame.of_kept (chainObjectsKept.revokeService hInv hRev) (RecordsFrame.revokeService hInv hRev)
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
          exact LendersStep.of_frame <| LendersFrame.writeCallReturnWord _ _ _ hInv
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
              · exact LendersStep.of_frame <| LendersFrame.schedControlConfigure hInv hStep
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
              exact LendersStep.schedContextBindNotification hInv hStep (hBN hSy _ vScId k hTgt hVal hN)
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
                  exact LendersStep.schedContextBind hInv hStep (hBT hSy _ vScId vThreadId hTgt hVal hN hRes)
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
                  exact LendersStep.of_frame <| LendersFrame.schedContextUnbindAllOnCore hInv hUn
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
              exact LendersStep.of_frame <| LendersFrame.schedContextUnbindNotificationObject hInv hStep
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
                      exact LendersStep.of_frame <| LendersFrame.schedContextUnbindThreadObjectOnCore hInv hUn
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
              exact LendersStep.of_frame <| LendersFrame.schedContextConsumedOnCore hInv hC
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
              exact LendersStep.of_frame <| LendersFrame.schedContextYieldToOnCore hInv hC
    all_goals try cases hStep
  case irqHandlerAck =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      rw [Architecture.irqHandlerAck_ok hStep]
      have hO := Architecture.setInterruptLineMask_objects st line false
      exact .of_frame ⟨(chainObjectsKept.of_objects_eq hO).linksShrink, hO ▸ hInv⟩
    all_goals try cases hStep
  case irqControlGet =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqControl => exact LendersStep.of_frame <| LendersFrame.irqControlGetFromCap hInv hStep
    all_goals try cases hStep
  case irqHandlerSetNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      obtain ⟨_, _, _, hS⟩ := irqHandlerSetNotificationFromCap_ok tid executingCore line _ st st' hStep
      exact LendersStep.irqHandlerSetNotification hInv hS
    all_goals try cases hStep
  case irqHandlerClear =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line => exact LendersStep.irqHandlerClear hInv hStep
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
                  exact LendersStep.of_frame <| LendersFrame.of_kept (chainObjectsKept.bindNotification hInv hStep) (RecordsFrame.bindNotification hInv hStep)
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
          exact LendersStep.of_frame <| LendersFrame.of_kept (chainObjectsKept.unbindNotification hInv hUn) (RecordsFrame.unbindNotification hInv hUn)
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
                  exact LendersStep.suspendThreadOnCore hInv hSus
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
              exact LendersStep.restartThreadOnCore hInv hRes
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
                      exact LendersStep.of_frame <| LendersFrame.setPriorityOnCore hInv hSet
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
                      exact LendersStep.of_frame <| LendersFrame.setMCPriorityOnCore hInv hSet
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
                  exact LendersStep.of_frame <| LendersFrame.setIPCBufferOp executingCore hInv hSet
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
                      exact LendersStep.of_frame <| LendersFrame.setThreadCpuAffinityOnCore hInv hSet
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
                      exact LendersStep.copyThreadSpacesZombie executingCore hInv hSet
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
                exact LendersStep.of_frame <| LendersFrame.pageTableMap hInv hStep
    all_goals try cases hStep
  case pageTableUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      exact LendersStep.of_frame <| LendersFrame.pageTableUnmap hInv hStep
    all_goals try cases hStep
/-- **`SchedContext_Bind`'s label equations are its gate's** (WS-SX SX17, D35):
a checked capability-only arm that succeeds on the bind passed
`schedContextBindLabelGate`, which admits the thread, or the notification, the
resolution answers only when it is labelled as the context. -/
theorem dispatchCapabilityOnlyChecked_bindLabels {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {cap : Capability} {k : Kernel Unit}
    {st : SystemState} {r : Unit × SystemState}
    (h : dispatchCapabilityOnlyChecked ctx decoded.syscallId decoded.msgInfo.extraCaps tid cap k st
      = .ok r) :
    (decoded.syscallId = .schedContextBind → ∀ scId vScId vTid,
      cap.target = .object scId → validateObjIdArg scId = .ok vScId →
      resolveSchedContextBindNotificationCode tid
        (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st = 0 →
      resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st
        = .ok vTid →
      ctx.threadLabelOf vTid.val = ctx.objectLabelOf vScId.val) ∧
    (decoded.syscallId = .schedContextBind → ∀ scId vScId n,
      cap.target = .object scId → validateObjIdArg scId = .ok vScId →
      resolveSchedContextBindNotificationCode tid
        (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st = n + 1 →
      ctx.objectLabelOf ⟨n⟩ = ctx.objectLabelOf vScId.val) := by
  refine ⟨fun hSy scId vScId vTid hT hV hN hR => ?_, fun hSy scId vScId n hT hV hN => ?_⟩
  · unfold dispatchCapabilityOnlyChecked at h
    rw [hSy, hT] at h
    rw [validateObjIdArg_ok_val scId vScId hV]
    exact (schedContextBindLabelAdmits_eq (schedContextBindLabelGate_admits h hN hR)).symm
  · unfold dispatchCapabilityOnlyChecked at h
    rw [hSy, hT] at h
    rw [validateObjIdArg_ok_val scId vScId hV]
    exact ((twoWayLabelGate_iff_eq _ _).1 (schedContextBindLabelGate_admits_notification h hN)).symm

/-- **A checked capability-only arm is a labelled step**: the arm it runs, the
bind's label equations read off the gate it passed. -/
theorem dispatchCapabilityOnlyChecked_lendersStep (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (k : Kernel Unit) (st st' : SystemState)
    (hArm : dispatchCapabilityOnly decoded cap tid executingCore = some k)
    (hInv : st.objects.invExt)
    (h : dispatchCapabilityOnlyChecked ctx decoded.syscallId decoded.msgInfo.extraCaps tid cap k st
      = .ok ((), st')) :
    LendersStep ctx st st' :=
  dispatchCapabilityOnly_lendersStep ctx decoded cap tid executingCore k st st' hArm hInv
    (dispatchCapabilityOnlyChecked_ok hArm h) (dispatchCapabilityOnlyChecked_bindLabels h).1
    (dispatchCapabilityOnlyChecked_bindLabels h).2

/-- **The capability dispatch keeps the lenders' flow**, given the waiters at
the dispatcher's state. -/
theorem dispatchWithCapChecked_lendersStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (ec : CoreId) (gate : SyscallGate)
    (cap : Capability) (st st' : SystemState)
    (P : LendersDispatchPremises ctx decoded tid ec gate cap st) (hCaller : CallerReady st tid)
    (hW : endpointWaitersLabelsEqual ctx st)
    (h : dispatchWithCapChecked ctx decoded tid ec gate cap st = .ok ((), st')) :
    LendersStage ctx st st' :=
  dispatchWithCapChecked_lendersStage_of_capabilityOnly ctx decoded tid ec gate cap st st' P hCaller
    hW (fun k hC hK => (dispatchCapabilityOnlyChecked_lendersStep ctx decoded cap tid ec k st st' hC
      P.reach.objects_invExt hK).stage) h

/-- **The checked syscall dispatch keeps the lenders' flow**, given the waiters
at the dispatcher's state. -/
theorem dispatchSyscallChecked_lendersStage (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (st st' : SystemState) (hInv : st.objects.invExt)
    (P : ∀ tcb, st.getObject? tid.toObjId = some (.tcb tcb) → ∀ cap,
      LendersDispatchPremises ctx decoded tid ec
        { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr,
          requiredRight := syscallRequiredRight decoded.syscallId } cap st)
    (hCaller : CallerReady st tid) (hW : endpointWaitersLabelsEqual ctx st)
    (h : dispatchSyscallChecked ctx decoded tid ec st = .ok ((), st')) : LendersStage ctx st st' :=
  dispatchSyscallChecked_lendersStage_of_capabilityOnly ctx decoded tid ec st st' hInv P hCaller hW
    (fun _ cap k st'' _ hC hK => (dispatchCapabilityOnlyChecked_lendersStep ctx decoded cap tid ec k
      st st'' hC hInv hK).stage) h

end SeLe4n.Kernel
