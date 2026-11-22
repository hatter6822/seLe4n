-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Capability

/-! # The checked capability dispatch carries the lenders' flow

WS-SX SX8.  The twin of `dispatchWithCapChecked_recordsStage`
(`KernelRecords/Dispatch.lean`) for `contextLendersFlow`, over every arm the
capability dispatch routes past the capability-only table: the IPC arms, the
signal and wait, the audit read and drain, the declassifications, and the
capability writes the dispatch runs itself.

**The premise pack** (`LendersDispatchPremises`): the reachable bundle at the
dispatcher's state, and the chain facts each lending step reads at the state it
runs from -- the `Call` after its rendezvous, the receive after seL4-MCS's
return, the reply-receive's legs -- read off those states as premises, exactly
where the records' and the chain's own per-entry theorems take them
(`docs/REGISTERED_DEBT.md` table C, "`ipcReachable` is not carried across a
trace of kernel entries", owner WS-PK).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **What the checked capability dispatch's lending arms read**: the reachable
bundle at the dispatcher's state, and, at the states the lending steps run
from, the chain facts they read. -/
structure LendersDispatchPremises (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState) : Prop where
  reach : ipcReachable st
  call : ∀ epId, cap.target = .object epId →
    LendersPremises (endpointCallWithCapsOnCore epId tid
      (.frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply)) ec st).1
  receive : ∀ epId, cap.target = .object epId →
    ReceiveLendersPremises (cancelRecvBusyReply ctx tid gate decoded ec st) tid gate decoded epId ec
  replyRecv : ∀ epId rid prevCaller replyBadge replyGrant, cap.target = .object epId →
    resolveReplyRecvReply gate decoded st = .ok (some (rid, prevCaller, replyBadge, replyGrant)) →
    let msg : IpcMessage :=
      { registers := Architecture.RegisterDecode.extractMessageRegisters decoded.msgRegs decoded.msgInfo, badge := replyBadge }
    ReplyRecvLendersPremises ctx st
      (replyRecvCallerFaultAnswer? st prevCaller decoded.msgInfo.label msg) epId tid rid prevCaller
      (replyRecvLegMessage (replyRecvCallerFaultAnswer? st prevCaller decoded.msgInfo.label msg) msg)
      replyGrant ec

/-- The tail every waking arm ends with: clear the woken receiver's stash, then
stage the delivered frames. -/
theorem clearStashStage_lendersStage {ctx : LabelingContext} {st s st' : SystemState}
    {woken? : Option SeLe4n.ThreadId} {stage : SystemState → SystemState}
    (hS : LendersStage ctx st s) (hI : s.objects.invExt)
    (hStage : ∀ x, x.objects.invExt → LendersStage ctx x (stage x))
    (h : (match clearWokenReceiverStash woken? s with
      | .error e => .error e
      | .ok ((), s') => .ok ((), stage s')) =
        (.ok ((), st') : Except KernelError (Unit × SystemState))) :
    LendersStage ctx st st' := by
  split at h
  · cases h
  · rename_i s3 hClr
    cases h
    have F := LendersFrame.clearWokenReceiverStash woken? hI hClr
    exact (hS.trans F.stage).trans (hStage _ F.invExt)

/-- **Every arm `dispatchWithCapChecked` routes past the capability-only table
carries the lenders' flow**: the IPC arms, the signal and the wait, the audit
read and drain, the declassifications, and the capability writes.  The
capability-only table's arms are `hCapOnly`'s (`dispatchCapabilityOnly`). -/
theorem dispatchWithCapChecked_lendersStage_of_capabilityOnly (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (ec : CoreId) (gate : SyscallGate)
    (cap : Capability) (st st' : SystemState)
    (P : LendersDispatchPremises ctx decoded tid ec gate cap st) (hCaller : CallerReady st tid)
    (hCapOnly : ∀ k, dispatchCapabilityOnly decoded cap tid ec = some k →
      dispatchCapabilityOnlyChecked ctx decoded.syscallId decoded.msgInfo.extraCaps tid cap k st
        = .ok ((), st') → LendersStage ctx st st')
    (h : dispatchWithCapChecked ctx decoded tid ec gate cap st = .ok ((), st')) :
    LendersStage ctx st st' := by
  have hInv := P.reach.objects_invExt
  have hIpc := P.reach.ipcInvariantFull
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid ec with
  | some k =>
    rw [hC] at h
    exact hCapOnly k hC h
  | none =>
  rw [hC] at h
  dsimp only at h
  cases hId : decoded.syscallId <;> rw [hId] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case auditRead =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    have F := LendersFrame.auditReadFromCore hInv hA
    exact (F.andThen fun hI => LendersFrame.writeCallReturnWord _ _ _ hI).stage
  case auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    have F := LendersFrame.auditDrainVisiblePrefix hInv hA
    exact (F.andThen fun hI => LendersFrame.writeCallReturnWord _ _ _ hI).stage
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case send.object epId =>
    split at h
    · cases h; exact LendersStage.refl _
    split at h
    · cases h
    rename_i hSend
    have hS := endpointSendCrossCoreDispatchChecked_lendersStage (ctx := ctx) epId tid
      (.frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply)) ec st hInv
    have hI := (RecordsStep.endpointSendCrossCoreDispatchChecked (ctx := ctx) (endpointId := epId)
      (payload := .frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply)) (c := ec)
      hInv hIpc.queueHeadBlockedConsistent hCaller.notParked).invExt
    rw [hSend] at hS hI
    exact clearStashStage_lendersStage hS hI
      (fun x hx => (LendersFrame.stageWokenDelivery x _ _ hx).stage) h
  case receive.object epId =>
    split at h
    · cases h
    exact receiveResolvedArm_lendersStage ctx decoded tid ec gate epId st st' hInv hIpc hCaller
      (P.receive epId hT) h
  case call.object epId =>
    split at h
    · rename_i hCall
      cases h
      intro hF
      have h1 := endpointCallCrossCoreDispatchChecked_preserves_contextLendersFlow epId tid _ ec st
        hInv P.reach.donationChainWellFormed (P.call epId hT) hF
      have hI := (RecordsStep.endpointCallCrossCoreDispatchChecked (ctx := ctx) (endpointId := epId)
        (caller := tid) (payload := .frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply))
        (c := ec) hInv hIpc.queueHeadBlockedConsistent).invExt
      rw [hCall] at h1 hI
      exact (LendersFrame.stageWokenDelivery _ _ _ hI).stage h1
    · cases h
  case reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact (LendersFrame.replyTransferOnCoreChecked hInv h).stage
  case replyRecv.object epId =>
    split at h
    · cases h
    split at h
    · exact receiveResolvedArm_lendersStage ctx decoded tid ec gate epId st st' hInv hIpc hCaller
        (P.receive epId hT) h
    split at h
    · cases h
    · exact receiveResolvedArm_lendersStage ctx decoded tid ec gate epId st st' hInv hIpc hCaller
        (P.receive epId hT) h
    rename_i rid prevCaller replyBadge replyGrant hRes
    repeat' split at h
    all_goals first | (cases h; done) | skip
    · exact (LendersFrame.replyRecvCompletesSignalArm hInv h).stage
    rename_i hX
    cases h
    have hS := replyRecvTransferOnCore_lendersStage hInv hIpc.queueHeadBlockedConsistent
      hCaller.ready (P.replyRecv epId rid prevCaller replyBadge replyGrant hT hRes) id hX
    have hI : _ := hX
    unfold replyRecvTransferOnCore at hI
    exact hS.trans (LendersFrame.stageDeliveredMessage _ _ _
      (endpointReplyRecvOnCore_preserves_objects_invExt _ _ _ _ _ _ _ _ _ _ hInv hI)).stage
  case cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · exact (LendersFrame.cspaceMintWithCdt hInv h).stage
      · cases h
  case cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · exact (LendersFrame.cspaceCopy hInv h).stage
    · cases h
  case cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · exact (LendersFrame.cspaceMove hInv h).stage
    · cases h
  case serviceRegister.serviceRegistry _ =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    replace h := serviceEndpointArm_ok h
    obtain ⟨_, epId, -, h⟩ := h
    try dsimp only at h
    unfold registerServiceChecked at h
    split at h
    · exact (LendersFrame.registerService hInv h).stage
    · cases h
  case notificationSignal.object notifId =>
    try dsimp only at h
    split at h
    · rename_i hSig
      cases h
      exact LendersStage.of_fst_eq
        (LendersFrame.notificationSignalBoundCrossCoreDispatchChecked ctx _ _ _ _ st hInv).stage hSig
    · cases h
  case notificationWait.object notifId =>
    split at h
    · cases h; exact (LendersFrame.writeReturnFrameToTcb _ _ _ hInv).stage
    exact (LendersFrame.completeSignalArm hInv hCaller.notParked h).stage
  case declassify.auditTrail code =>
    split at h
    · cases h
    exact (LendersFrame.declassifyObjectFromCore hInv h).stage
  case declassifySignal.auditTrail code =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      cases h
      exact LendersStage.of_fst_eq
        (LendersFrame.notificationSignalDeclassifiedCrossCoreDispatch _ _ _ _ _ st hInv).stage hSig
    · cases h

namespace LendersFrame

/-- The yield's charge: the slice end, or the budget forfeit with the key hook. -/
theorem yieldChargeOnCore {st st' : SystemState} {c : CoreId} {tid : SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.yieldChargeOnCore st c tid = .ok st') :
    LendersFrame st st' := by
  unfold _root_.SeLe4n.Kernel.yieldChargeOnCore at h
  split at h
  · cases h
  · rename_i tcb hTcb _
    split at h
    · rw [Except.ok.injEq] at h; subst h
      exact sliceExpireOnCore st c tid tcb hTcb hInv
    all_goals
      split at h
      · rename_i sc hSc _
        rw [Except.ok.injEq] at h; subst h
        exact (spendBudgetOnCore st c tid _ sc hSc _ _ hInv).andThen fun h => markKeyChangeFor _ _ _ h
      · cases h

/-- **The yield keeps the lenders' flow**: the charge and the reschedule. -/
theorem yieldOnCore {st st' : SystemState} {c : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.yieldOnCore st c = .ok st') : LendersFrame st st' := by
  unfold _root_.SeLe4n.Kernel.yieldOnCore at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hC
      exact (yieldChargeOnCore hInv hC).andThen fun h' => scheduleEffectiveOnCore h' h

end LendersFrame

theorem objStackViews_map_eraseTaint (o? : Option KernelObject) :
    objStackHead (o?.map KernelObject.eraseTaint) = objStackHead o? ∧
    objStackPrev (o?.map KernelObject.eraseTaint) = objStackPrev o? ∧
    objStackCaller (o?.map KernelObject.eraseTaint) = objStackCaller o? := by
  cases o? with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some o => cases o <;> exact ⟨rfl, rfl, rfl⟩

/-- **A write of taint words alone** is a frame of the three views. -/
theorem contextStackViewsAgree_of_objectsAgreeOffTaint {st st' : SystemState}
    (h : st.objectsAgreeOffTaint st') : contextStackViewsAgree st st' := by
  have key : ∀ x : SeLe4n.ObjId, objStackHead st'.objects[x]? = objStackHead st.objects[x]? ∧
      objStackPrev st'.objects[x]? = objStackPrev st.objects[x]? ∧
      objStackCaller st'.objects[x]? = objStackCaller st.objects[x]? := fun x => by
    have a := objStackViews_map_eraseTaint st'.objects[x]?
    have b := objStackViews_map_eraseTaint st.objects[x]?
    rw [h x] at a
    exact ⟨a.1.symm.trans b.1, a.2.1.symm.trans b.2.1, a.2.2.symm.trans b.2.2⟩
  refine ⟨fun s => ?_, fun r => ?_, fun r => ?_⟩
  · rw [contextStackHead_eq_obj, contextStackHead_eq_obj]; exact (key _).1
  · rw [replyStackPrev_eq_obj, replyStackPrev_eq_obj]; exact (key _).2.1
  · rw [replyStackCaller_eq_obj, replyStackCaller_eq_obj]; exact (key _).2.2

/-- **The taint pass keeps the lenders' flow**: it writes the taint words alone. -/
theorem applySyscallTaint_lendersStage {ctx : LabelingContext} (plan : TaintPlan)
    (pre post : SystemState) : LendersStage ctx post (applySyscallTaint plan pre post) :=
  LendersStage.of_viewsAgree
    (contextStackViewsAgree_of_objectsAgreeOffTaint (applySyscallTaint_objectsAgreeOffTaint _ _ _))

/-- **The checked syscall dispatch carries the lenders' flow**: the yield, the
capability resolution (a read, so the arm runs on the dispatcher's state and
reads its premises there), the routed arm, and the taint pass, which writes the
taint words alone.  The premise pack is read at the gate the dispatcher builds
from the caller's thread record. -/
theorem dispatchSyscallChecked_lendersStage_of_capabilityOnly (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (ec : CoreId) (st st' : SystemState)
    (hInv : st.objects.invExt)
    (P : ∀ tcb, st.getObject? tid.toObjId = some (.tcb tcb) → ∀ cap,
      LendersDispatchPremises ctx decoded tid ec
        { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr,
          requiredRight := syscallRequiredRight decoded.syscallId } cap st)
    (hCaller : CallerReady st tid)
    (hCapOnly : ∀ cap k st'', dispatchCapabilityOnly decoded cap tid ec = some k →
      dispatchCapabilityOnlyChecked ctx decoded.syscallId decoded.msgInfo.extraCaps tid cap k st
        = .ok ((), st'') → LendersStage ctx st st'')
    (h : dispatchSyscallChecked ctx decoded tid ec st = .ok ((), st')) :
    LendersStage ctx st st' := by
  unfold dispatchSyscallChecked at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact (LendersFrame.yieldOnCore hInv hYieldOk).stage
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  rename_i tcb hTcb
  split at h
  · cases h
  rename_i stPost hD
  cases h
  refine LendersStage.trans (b := stPost) ?_ (applySyscallTaint_lendersStage _ _ _)
  obtain ⟨cap, -, -, hD⟩ := syscallInvokeTyped_ok _ _ _ st () stPost hD
  exact dispatchWithCapChecked_lendersStage_of_capabilityOnly ctx decoded tid ec _ cap st stPost
    (P tcb hTcb cap) hCaller (fun k hk => hCapOnly cap k stPost hk) hD

end SeLe4n.Kernel
