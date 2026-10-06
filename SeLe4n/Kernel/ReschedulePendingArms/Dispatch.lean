-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ReschedulePendingArms.Ipc
import SeLe4n.Kernel.API
import SeLe4n.Kernel.Lifecycle.Invariant.RetypeReservation

/-!
# The checked dispatcher's own arms cover

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md`, PR B2.  Each arm
`dispatchWithCapChecked` routes itself (the IPC, notification, CSpace, service,
declassification and audit arms) is one of the transitions the sibling modules
prove covering, wrapped in steps that move no key input: extra-capability
resolution (CDT nodes only), the woken receiver's stash clear, the return-frame
staging, the service registry and the audit trail.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-! ### The wrapping steps -/

/-- Resolving the extra capabilities mints CDT nodes only. -/
theorem resolveExtraCaps_keyFrame (cspaceRoot : SeLe4n.ObjId) (capAddrs : Array SeLe4n.CPtr)
    (depth : Nat) (granted : Bool) (st : SystemState) (hInv : st.objects.invExt) :
    capabilityKeyFrame st (resolveExtraCaps cspaceRoot capAddrs depth granted st).2 := by
  suffices h : (resolveExtraCaps cspaceRoot capAddrs depth granted st).2.objects = st.objects ∧
      (resolveExtraCaps cspaceRoot capAddrs depth granted st).2.scheduler = st.scheduler from
    capabilityKeyFrame_of_objects_scheduler_eq hInv h.1 h.2
  unfold resolveExtraCaps
  split
  · exact ⟨rfl, rfl⟩
  · refine Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Array TransferCap × SystemState) =>
        acc.2.objects = st.objects ∧ acc.2.scheduler = st.scheduler) ⟨rfl, rfl⟩ ?_
    intro i acc hAcc
    split
    · exact hAcc
    · split
      · exact hAcc
      · split
        · exact hAcc
        · rename_i node stNode hNode
          unfold SystemState.ensureCdtNodeForSlotChecked at hNode
          split at hNode
          · cases hNode; exact hAcc
          · split at hNode
            · cases hNode; exact hAcc
            · cases hNode

theorem clearWokenReceiverStash_keyFrame (receiver? : Option SeLe4n.ThreadId) {st : SystemState}
    {pair : Unit × SystemState} (hInv : st.objects.invExt)
    (h : clearWokenReceiverStash receiver? st = .ok pair) : capabilityKeyFrame st pair.2 := by
  unfold clearWokenReceiverStash at h
  split at h
  · cases h; exact capabilityKeyFrame_refl hInv
  · split at h
    · rename_i rTcb hT
      split at h
      · exact keyFrame_storeObject_tcbKeeping_after
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) (by rfl) (capabilityKeyFrame_refl hInv) h
      · cases h; exact capabilityKeyFrame_refl hInv
    · cases h; exact capabilityKeyFrame_refl hInv

theorem registerService_keyFrame {reg : ServiceRegistration} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : registerService reg st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  unfold registerService at h
  repeat' split at h
  all_goals first
    | (cases h; exact capabilityKeyFrame_of_objects_scheduler_eq hInv rfl rfl)
    | (cases h; done)

/-- The declassified signal covers: the bound signal, then the audit records,
which touch the trail alone. -/
theorem notificationSignalDeclassifiedOnCore_stepCovers (e : CoreId)
    {ctx : GenericLabelingContext} {declPolicy : DeclassificationPolicy}
    {notificationId : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    stepCovers e st (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge
      c st).1 ∧
    (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge
      c st).1.objects.invExt := by
  have hRefl : stepCovers e st st ∧ st.objects.invExt := ⟨stepCovers_refl e st, hInv⟩
  unfold notificationSignalDeclassifiedOnCore
  split
  · exact hRefl
  split
  · split <;> exact hRefl
  dsimp only
  split
  · exact hRefl
  have hB := notificationSignalBoundOnCore_stepCovers e (notificationId := notificationId)
    (badge := badge) (executingCore := c) hInv
  generalize notificationSignalBoundOnCore notificationId badge c st = r at hB
  obtain ⟨st1, res⟩ := r
  obtain ⟨hB, hBInv⟩ := hB
  cases res with
  | error _ => exact hRefl
  | ok sgi =>
    dsimp only at hB ⊢
    split
    · exact hRefl
    · rename_i st2 hRec
      rw [recordDeclassifiedHops_frame _ _ _ _ _ hRec]
      exact ⟨stepCovers_trans hB (stepCovers_of_scheduler_eq (keyInputsEq_of_objects_eq rfl) rfl),
        hBInv⟩

/-! ### Retype -/

/-- A write that moves only slot `X` keeps the key of every thread that neither
lives at `X` nor names `X` as its scheduling context. -/
theorem schedKeyView_eq_of_slotUnread {pre post : SystemState} {X : SeLe4n.ObjId}
    (hFrame : ∀ oid, oid ≠ X → keyInputsOf post.objects[oid]? = keyInputsOf pre.objects[oid]?)
    {t : SeLe4n.ThreadId} (ht : t.toObjId ≠ X)
    (hNo : ∀ tcb, pre.getTcb? t = some tcb → ∀ sc, tcb.schedContextBinding.scId? = some sc →
      sc.toObjId ≠ X) :
    schedKeyView post t = schedKeyView pre t := by
  have hT := getTcb?_keyFields_of_keyInputsOf (hFrame _ ht)
  unfold schedKeyView
  cases hq : post.getTcb? t <;> cases hp : pre.getTcb? t <;> simp only [hq, hp] at hT ⊢
  · rfl
  · simp at hT
  · simp at hT
  · rename_i b a
    simp only [Option.map_some, Option.some.injEq] at hT ⊢
    rw [resolveEffectivePrioDeadline_congr_binding hT (fun sc hsc =>
      getSchedContext?_deadline_of_keyInputsOf (hFrame _ (hNo a hp sc hsc)))]

/-- **The retype covers**, under the detachment pack the dispatch's invariant
payoff already consumes: the cleanup is the identity on the object store and the
scheduler, so the retype is one store at a slot no placed thread lives at or
reads its deadline from. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_stepCovers (e : CoreId)
    {ec : CoreId} {authCap : Capability} {target : SeLe4n.ObjId} {newObj : KernelObject}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (hBi : schedContextBindingBidirectional st) (hDet : retypeTargetDetached st target)
    (hPlaced : ∀ c t, (t ∈ st.scheduler.runQueueOnCore c ∨
      st.scheduler.currentOnCore c = some t) → (st.getTcb? t).isSome)
    (h : lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache ec authCap target newObj st
      = .ok ((), st')) :
    stepCovers e st st' := by
  obtain ⟨stB, hB, hObjB, hSchB⟩ :=
    lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_ok_frame h
  obtain ⟨_, cur, stClean, hCur, hClean, hStore⟩ := lifecycleRetypeDirectWithCleanup_ok_decompose hB
  obtain ⟨hCO, hCS, _⟩ :=
    lifecyclePreRetypeCleanup_detached_frame st stClean target cur newObj hInv hCur hDet hClean
  have hScrubInv : (scrubObjectMemory stClean target cur.objectType).objects.invExt := by
    rw [scrubObjectMemory_objects_eq, hCO]; exact hInv
  have hSched : st'.scheduler = st.scheduler := by
    rw [hSchB, storeObject_scheduler_eq _ _ _ _ hStore]; exact hCS
  have hFrame : ∀ oid, oid ≠ target → st'.objects[oid]? = st.objects[oid]? := by
    intro oid hne
    rw [hObjB, storeObject_objects_ne _ _ _ _ _ hne hScrubInv hStore,
      scrubObjectMemory_objects_eq, hCO]
  have hUnread : ∀ c t, (t ∈ st.scheduler.runQueueOnCore c ∨
      st.scheduler.currentOnCore c = some t) → schedKeyView st' t = schedKeyView st t := by
    intro c t hP
    obtain ⟨tcb, hT⟩ := Option.isSome_iff_exists.mp (hPlaced c t hP)
    have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    have ht : t.toObjId ≠ target := by
      intro hEq
      rw [hEq] at hTo
      have hDs := hDet.tcbDescheduled tcb hTo c
      have hId : tcb.tid = t :=
        SeLe4n.ThreadId.toObjId_injective _ _ ((hDet.tcbSelfId tcb hTo).trans hEq.symm)
      rw [hId] at hDs
      rcases hP with hQ | hQ
      · have hQ' : (st.scheduler.runQueueOnCore c).contains t = true := hQ
        rw [hDs.1] at hQ'; cases hQ'
      · exact hDs.2 hQ
    refine schedKeyView_eq_of_slotUnread (fun oid hne => by rw [hFrame oid hne]) ht ?_
    intro tcb' hT' sc hsc hEq
    rw [hT] at hT'; cases hT'
    obtain ⟨sco, hSo, _⟩ := hBi t tcb sc hTo hsc
    rw [hEq] at hSo
    exact hDet.notSc sco hSo
  refine ⟨fun c _ => Or.inr ⟨fun t ht => ?_, by rw [hSched], fun t ht => ?_⟩,
    fun c _ hc => by rw [hSched]; exact hc⟩
  · rw [hSched] at ht; exact ⟨ht, (hUnread c t (Or.inl ht)).symm⟩
  · rw [hSched] at ht; exact schedKeyNotWeakened_of_eq (hUnread c t (Or.inr ht)).symm

/-! ### The capability-only arms -/

/-- **Every arm `dispatchCapabilityOnly` routes covers**, on the executing core,
under the binding reciprocity, the placement facts and the retype detachment
pack — the pre-state facts the dispatch's invariant payoff consumes. -/
theorem dispatchCapabilityOnly_stepCovers {decoded : SyscallDecodeResult} {cap : Capability}
    {tid : SeLe4n.ThreadId} {ec : CoreId} {k : Kernel Unit} {st st' : SystemState}
    (hInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st)
    (hPlaced : ∀ c t, (t ∈ st.scheduler.runQueueOnCore c ∨
      st.scheduler.currentOnCore c = some t) → (st.getTcb? t).isSome)
    (hDet : ∀ args, decoded.syscallId = .lifecycleRetype →
      decodeLifecycleRetypeArgs decoded = .ok args → retypeTargetDetached st args.targetObj)
    (hK : dispatchCapabilityOnly decoded cap tid ec = some k)
    (h : k st = .ok ((), st')) : stepCovers ec st st' := by
  unfold dispatchCapabilityOnly at hK
  cases hId : decoded.syscallId <;> rw [hId] at hK <;> simp only [Option.some.injEq,
    reduceCtorEq] at hK
  all_goals subst hK
  all_goals cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case lifecycleRetype.object =>
    split at h
    · cases h
    · rename_i args hArgs
      exact lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_stepCovers ec hInv hBi
        (hDet args hId hArgs) hPlaced h
  all_goals (repeat' split at h)
  all_goals first | (cases h; done) | skip
  all_goals try first
    | exact (cspaceDeleteSlotFinalising_keyFrame _ _ _ _ hInv h).stepCovers
    | exact (cspaceRevokeCdtFinalising_keyFrame _ _ _ _ hInv h).stepCovers
    | exact (mintReplyCapWithCdt_keyFrame _ _ _ _ hInv h).stepCovers
    | exact (untypedResetWithShootdown_keyFrame _ _ _ _ hInv h).stepCovers
    | exact (vspaceMapFromFrameCap_keyFrame _ _ _ _ _ hInv h).stepCovers
    | exact (vspaceRootOnlyWrite_keyFrame
        (vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame _ _ _ _ _ hInv h)).stepCovers
    | exact (capabilityKeyFrame_of_objects_scheduler_eq hInv
        (Architecture.vspaceUnifyInstructionPage_frame h).1
        (Architecture.vspaceUnifyInstructionPage_frame h).2.2.1).stepCovers
    | exact (capabilityKeyFrame_of_objects_scheduler_eq hInv
        (revokeService_preserves_objects _ _ _ h) (revokeService_preserves_scheduler _ _ _ h)).stepCovers
    | exact (schedContextConfigure_stepCovers _ _ _ _ _ _ _ _ _ hInv hBi h).1
    | exact (schedContextBind_stepCovers _ _ _ _ _ hInv h).1
    | exact (bindNotification_keyFrame _ _ _ _ hInv h).stepCovers
    | exact (pageTableMap_keyFrame _ _ _ _ _ hInv h).stepCovers
    | exact (pageTableUnmap_keyFrame _ _ _ hInv h).stepCovers
    | (cases h; rename_i hU
       first
        | (rw [lookupServiceByCap_preserves_state _ _ _ _ hU]
           exact (writeReturnFrameToTcb_keyFrame _ _ _ hInv).stepCovers)
        | exact (schedContextUnbindOnCore_stepCovers _ _ _ _ _ hInv hU).1
        | exact (unbindNotification_keyFrame _ _ _ hInv hU).stepCovers
        | exact (suspendThreadOnCore_stepCovers _ _ _ _ _ hInv hU).1
        | exact stepCovers_trans (retirePendingFaultForResume_keyFrame _ _ hInv).stepCovers
            (resumeThreadOnCore_stepCovers _ _ _ _ _
              (retirePendingFaultForResume_keyFrame _ _ hInv).2.2 hU).1
        | exact (setPriorityOnCore_stepCovers _ _ _ _ _ _ _ hInv hU).1
        | exact (setMCPriorityOnCore_stepCovers _ _ _ _ _ _ _ hInv hU).1
        | exact (setThreadCpuAffinityOnCore_stepCovers _ _ _ _ _ _ hInv hU).1
        | exact (setIPCBufferOp_keyFrame _ _ _ _ hInv hU).stepCovers
        | exact (setThreadFaultHandlerOp_keyFrame _ _ _ _ hInv hU).stepCovers
        | exact (setThreadSpace_keyFrame _ _ _ _ _ hInv hU).stepCovers)
  all_goals
    obtain ⟨_, _, _, _, _, _, _, _, _, hU⟩ := untypedRetypeFromCap_ok _ _ _ _ h
    exact (untypedRetypeObject_keyFrame _ _ _ _ _ _ hInv hU).stepCovers

/-! ### The checked dispatcher -/

/-- Read a pair-returning transition's coverage off the equation that named its
result. -/
theorem stepCovers_of_pair_eq {α : Type} {e : CoreId} {st s : SystemState}
    {p : SystemState × α} {r : α}
    (hCov : stepCovers e st p.1 ∧ p.1.objects.invExt) (hEq : p = (s, r)) :
    stepCovers e st s ∧ s.objects.invExt := by
  subst hEq; exact hCov

/-- The tail every waking arm ends with: clear the woken receiver's stash, then
stage the delivered frames. -/
theorem stepCovers_clearStash_stage {e : CoreId} {st s st' : SystemState}
    {woken? : Option SeLe4n.ThreadId} {stage : SystemState → SystemState}
    (hS : stepCovers e st s) (hInv : s.objects.invExt)
    (hStage : ∀ x, x.objects.invExt → capabilityKeyFrame x (stage x))
    (h : (match clearWokenReceiverStash woken? s with
      | .error e => .error e
      | .ok ((), s') => .ok ((), stage s')) = (.ok ((), st') : Except KernelError (Unit × SystemState))) :
    stepCovers e st st' := by
  split at h
  · cases h
  · rename_i s3 hClr
    cases h
    have hF := clearWokenReceiverStash_keyFrame woken? hInv hClr
    exact stepCovers_trans (stepCovers_trans hS hF.stepCovers) (hStage _ hF.2.2).stepCovers

/-- The two badge stagings a signal arm ends with. -/
theorem keyFrame_trans_stage {x : SystemState} {w p : Option SeLe4n.ThreadId}
    (hx : x.objects.invExt) :
    capabilityKeyFrame x (Architecture.stageWokenDelivery
      (Architecture.stageWokenDelivery x w 0) p 0) := by
  have h1 := stageWokenDelivery_keyFrame x w 0 hx
  exact h1.trans (stageWokenDelivery_keyFrame _ p 0 h1.2.2)

/-- **Every arm `dispatchWithCapChecked` routes covers** on the executing core,
the capability-only arms it delegates included. -/
theorem dispatchWithCapChecked_stepCovers (e : CoreId) {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId}
    {gate : SyscallGate} {cap : Capability} {st st' : SystemState} (hInv : st.objects.invExt)
    (hBi : schedContextBindingBidirectional st)
    (hPlaced : ∀ c t, (t ∈ st.scheduler.runQueueOnCore c ∨
      st.scheduler.currentOnCore c = some t) → (st.getTcb? t).isSome)
    (hDet : ∀ args, decoded.syscallId = .lifecycleRetype →
      decodeLifecycleRetypeArgs decoded = .ok args → retypeTargetDetached st args.targetObj)
    (h : dispatchWithCapChecked ctx decoded tid e gate cap st = .ok ((), st')) :
    stepCovers e st st' := by
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid e with
  | some k => rw [hC] at h; exact dispatchCapabilityOnly_stepCovers hInv hBi hPlaced hDet hC h
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
    exact (writeReturnFrameToTcb_keyFrame _ _ _ hInv).stepCovers
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    unfold auditDrainVisiblePrefix at hA
    split at hA
    · cases hA
      refine stepCovers_trans (stepCovers_of_scheduler_eq (keyInputsEq_of_objects_eq rfl) rfl) ?_
      apply capabilityKeyFrame.stepCovers
      exact writeReturnFrameToTcb_keyFrame _ _ _ (by exact hInv)
    · cases hA
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    generalize hR : resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded) gate.capDepth
      (cap.rights.mem .grant) st = r at h
    obtain ⟨caps, s1⟩ := r
    have hF1 : capabilityKeyFrame st s1 := by
      have := resolveExtraCaps_keyFrame gate.cspaceRoot (decodeExtraCapAddrs decoded)
        gate.capDepth (cap.rights.mem .grant) st hInv
      rw [hR] at this; exact this
    dsimp only at h
    split at h
    · cases h
    rename_i hSend
    obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
      (endpointSendCrossCoreDispatchChecked_stepCovers e hF1.2.2) hSend
    exact stepCovers_clearStash_stage (stepCovers_trans hF1.stepCovers hS) hSInv
      (fun x hx => stageWokenDelivery_keyFrame x _ _ hx) h
  case none.receive.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ _ hRecv _ stDon hHand
    cases h
    obtain ⟨hV, hVInv⟩ := stepCovers_of_pair_eq
      (endpointReceiveDualWithCapsOnCore_stepCovers e hInv) hRecv
    obtain ⟨hD, hDInv⟩ := applyReceiveRendezvousHandoff_stepCovers e hVInv hHand
    have hS1 := stageWokenSendCompletion_keyFrame stDon
      ((st.getEndpoint? epId).bind (·.sendQ.head)) hDInv
    have hS2 := stageDeliveredMessage_keyFrame _ tid summ.installedCount hS1.2.2
    exact stepCovers_trans (stepCovers_trans (stepCovers_trans hV hD) hS1.stepCovers)
      hS2.stepCovers
  case none.call.object epId =>
    generalize hR : resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded) gate.capDepth
      (cap.rights.mem .grant) st = r at h
    obtain ⟨caps, s1⟩ := r
    have hF1 : capabilityKeyFrame st s1 := by
      have := resolveExtraCaps_keyFrame gate.cspaceRoot (decodeExtraCapAddrs decoded)
        gate.capDepth (cap.rights.mem .grant) st hInv
      rw [hR] at this; exact this
    dsimp only at h
    split at h
    · rename_i hCall
      cases h
      obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
        (endpointCallCrossCoreDispatchChecked_stepCovers e hF1.2.2) hCall
      exact stepCovers_trans (stepCovers_trans hF1.stepCovers hS)
        (stageWokenDelivery_keyFrame _ _ _ hSInv).stepCovers
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact replyTransferOnCoreChecked_stepCovers e hInv h
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · exact (cspaceMintWithCdt_keyFrame _ _ _ _ _ _ hInv h).stepCovers
      · cases h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · exact (cspaceCopy_keyFrame _ _ _ _ hInv h).stepCovers
    · cases h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · exact (cspaceMove_keyFrame _ _ _ _ hInv h).stepCovers
    · cases h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold registerServiceChecked at h
    dsimp only at h
    split at h
    · exact (registerService_keyFrame hInv h).stepCovers
    · cases h
  case none.notificationSignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
        (notificationSignalBoundCrossCoreDispatchChecked_stepCovers e hInv) hSig
      exact stepCovers_clearStash_stage hS hSInv
        (fun x hx => keyFrame_trans_stage hx) h
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hW
      cases h
      obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_stepCovers e hInv) hW
      exact stepCovers_trans hS (writeReturnFrameToTcb_keyFrame _ _ _ hSInv).stepCovers
    · rename_i hW
      cases h
      exact (stepCovers_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_stepCovers e hInv) hW).1
    · cases h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ stR hRR
    cases h
    obtain ⟨hS, hSInv⟩ := endpointReplyRecvOnCore_stepCovers e hInv hRR
    exact stepCovers_trans hS (stageDeliveredMessage_keyFrame _ tid _ hSInv).stepCovers
  case none.declassify.object targetId =>
    unfold declassifyObjectFromCore at h
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rw [(authorizeDeclassificationOnCore_frame _ _ _ _ _ _ _ _ _ h).1]
    exact stepCovers_of_scheduler_eq (keyInputsEq_of_objects_eq rfl) rfl
  case none.declassifySignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
        (notificationSignalDeclassifiedOnCore_stepCovers e hInv) hSig
      exact stepCovers_clearStash_stage hS hSInv
        (fun x hx => keyFrame_trans_stage hx) h
    · cases h

end SeLe4n.Kernel
