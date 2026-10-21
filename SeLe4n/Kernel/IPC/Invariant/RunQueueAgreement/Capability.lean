/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Endpoint
import SeLe4n.Kernel.API
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation

/-!
# Capability, VSpace, untyped and service arms keep the run-queue link agreement

WS-ZA ZA4.5 part 2.  These arms write CNodes, the derivation tree, VSpace roots,
frames, untyped objects and the service registry, and at most a pending
message of a blocked thread: no run queue, no queue end and no thread's
run-queue entry.  Each is a `RunQueueStage` (`SystemState.RunQueueStage`).
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)

/-- A stage may assume the pre-state's store invariant. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.of_inv {st st' : SystemState}
    (h : st.objects.invExt → RunQueueStage st st') : RunQueueStage st st' :=
  RunQueueStage.of_invExt h

/-- A step whose every object slot gives the run-queue entries it gave and is
rewritten monotonely, and which writes no run queue and no end. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.of_slots {st st' : SystemState}
    (h : st.objects.invExt → st'.objects.invExt ∧
      (∀ (oid : SeLe4n.ObjId) (c : Concurrency.CoreId), SystemState.objRunLinkOn st'.objects[oid]? c =
        SystemState.objRunLinkOn st.objects[oid]? c) ∧
      (∀ oid : SeLe4n.ObjId, SystemState.slotStateMono st.objects[oid]? st'.objects[oid]?) ∧
      st'.scheduler = st.scheduler) : RunQueueStage st st' :=
  have hL : st.objects.invExt → ∀ c t, st'.runLinkOn c t = st.runLinkOn c t := fun hInv c t => by
    rw [SystemState.runLinkOn_eq_objRunLinkOn, SystemState.runLinkOn_eq_objRunLinkOn]
    exact (h hInv).2.1 _ c
  ⟨fun hInv r => ⟨(h hInv).1,
      SystemState.runQueueRefined_of_frame (hL hInv) (by rw [(h hInv).2.2.2])
        (by rw [(h hInv).2.2.2]) r⟩,
    fun _ hInv _ _ d => SystemState.currentDequeuedUniqueExcept_of_eq (by rw [(h hInv).2.2.2])
      (hL hInv) (SystemState.StateMono.of_slots (h hInv).2.2.1) d,
    fun hInv _ => SystemState.StateMono.of_slots (h hInv).2.2.1⟩

/-- A write confined to VSpace roots moves no thread's run-queue entry. -/
theorem vspaceRootOnlyWrite_runQueueStage {st st' : SystemState}
    (h : st.objects.invExt →
      st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler) :
    RunQueueStage st st' :=
  RunQueueStage.of_slots fun hInv =>
    have ⟨hI, hW, hS⟩ := h hInv
    ⟨hI, fun oid c => by
      rcases hW oid with e | ⟨⟨r, h1⟩, ⟨r', h2⟩⟩
      · rw [e]
      · rw [h1, h2]; rfl, fun oid => by
      rcases hW oid with e | ⟨⟨r, h1⟩, ⟨r', h2⟩⟩
      · exact SystemState.slotStateMono.of_eq e
      · exact SystemState.slotStateMono.of_obj h2
          (SystemState.objStateMono_nonTcb (by rw [h1]; rfl) rfl), hS⟩

/-- A write of the derivation tree alone. -/
theorem withCdt_runQueueStage (st : SystemState) (cdt : CapDerivationTree) :
    RunQueueStage st { st with cdt := cdt } :=
  RunQueueStage.of_frame rfl rfl rfl

/-- One slot-link write rewrites a CNode, which holds no run-queue state, or a
thread's slot-link words, which are not run-queue state. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.setSlotLinkWords (st : SystemState)
    (o : SeLe4n.ObjId) (s : SeLe4n.Slot) (f : SeLe4n.Model.LinkField) (c w : Nat) :
    RunQueueStage st (st.setSlotLinkWords o s f c w) := by
  cases hcn : st.objects[o]? with
  | none =>
    exact RunQueueStage.of_eq
      (SystemState.setSlotLinkWords_of_not_slots (fun _ h => by rw [hcn] at h; cases h) s f c w)
  | some ob =>
    cases ob with
    | cnode cn =>
      rw [SystemState.setSlotLinkWords_of_cnode hcn]
      exact RunQueueStage.insert rfl rfl rfl (fun _ => by rw [hcn]; rfl)
        (by rw [hcn]; exact ⟨fun _ hx => by simp [SystemState.objTcb?] at hx,
          fun _ hx _ => by simp [SystemState.objTcb?] at hx⟩)
    | tcb t =>
      rw [SystemState.setSlotLinkWords_of_tcb hcn]
      exact RunQueueStage.insert rfl rfl rfl (fun _ => by rw [hcn]; rfl)
        (by rw [hcn]; exact SystemState.objStateMono_tcb ⟨id, id⟩)
    | _ =>
      exact RunQueueStage.of_eq
        (SystemState.setSlotLinkWords_of_not_slots (fun _ h => by
          rw [hcn] at h; cases h; rfl) s f c w)

/-- A run of slot-link writes is a run-queue stage. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.of_linkReach {st₀ st : SystemState}
    (h : SystemState.linkReach st₀ st) : RunQueueStage st₀ st := by
  induction h with
  | refl => exact RunQueueStage.refl _
  | step _ o s f c w ih => exact ih.trans (RunQueueStage.setSlotLinkWords _ o s f c w)

theorem cdtRecord_runQueueStage (stM : SystemState) (src dst : CSpaceAddr)
    (kind : DerivationOp) :
    RunQueueStage stM (stM.cdtAddChild src dst kind) :=
  (withCdt_runQueueStage _ _).trans
    (RunQueueStage.of_linkReach (SystemState.cdtAddChild_reach stM src dst kind))

theorem cspaceLookupSlot_runQueueStage {st st' : SystemState} {addr : CSpaceAddr}
    {cap : Capability} (h : cspaceLookupSlot addr st = .ok (cap, st')) : RunQueueStage st st' :=
  RunQueueStage.of_eq (cspaceLookupSlot_state_eq st st' addr cap h)

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (cspaceLookupSlot_runQueueStage (by with_reducible assumption)))

/-- Peel a stage off an `.ok` equation `h`: split its matches, close the
refusing branches, and run `run_queue_stage` on the rest. -/
macro "run_queue_stage_at " h:ident : tactic => `(tactic|
  (repeat' (first | split at $h:ident | dsimp only at $h:ident)
   all_goals first
     | contradiction
     | (run_queue_stage; done)
     | (cases $h:ident; done)
     | (cases $h:ident; run_queue_stage; done)))

theorem cspaceInsertSlot_runQueueStage {st st' : SystemState} {addr : CSpaceAddr}
    {cap : Capability} (h : cspaceInsertSlot addr cap st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold cspaceInsertSlot at h; run_queue_stage_at h

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (cspaceInsertSlot_runQueueStage (by with_reducible assumption)))

theorem cspaceMint_runQueueStage {st st' : SystemState} {src dst : CSpaceAddr}
    {rights : AccessRightSet} {badge : Option SeLe4n.Badge}
    (h : cspaceMint src dst rights badge st = .ok ((), st')) : RunQueueStage st st' := by
  unfold cspaceMint at h; run_queue_stage_at h

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (cspaceMint_runQueueStage (by with_reducible assumption)))

theorem cspaceMintWithCdt_runQueueStage {st st' : SystemState} {src dst : CSpaceAddr}
    {rights : AccessRightSet} {badge : Option SeLe4n.Badge}
    (h : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) : RunQueueStage st st' := by
  unfold cspaceMintWithCdt at h
  split at h
  · contradiction
  · rename_i stM hMint
    cases h
    exact (cspaceMint_runQueueStage hMint).trans (cdtRecord_runQueueStage stM src dst .mint)

theorem cspaceCopy_runQueueStage {st st' : SystemState} {src dst : CSpaceAddr}
    (h : cspaceCopy src dst st = .ok ((), st')) : RunQueueStage st st' := by
  unfold cspaceCopy at h
  split at h
  · contradiction
  · rename_i cap stMid hLk
    split at h
    · contradiction
    · split at h
      · contradiction
      · rename_i st2 hIns
        cases h
        exact ((cspaceLookupSlot_runQueueStage hLk).trans
          (cspaceInsertSlot_runQueueStage hIns)).trans (cdtRecord_runQueueStage st2 src dst .copy)

theorem cspaceDeleteSlotCore_runQueueStage {st st' : SystemState} {addr : CSpaceAddr}
    (h : cspaceDeleteSlotCore addr st = .ok ((), st')) : RunQueueStage st st' := by
  rcases cspaceDeleteSlotCore_ok_cases h with ⟨cn, hPre, hS⟩ | ⟨t, hPre, hS⟩
  · exact RunQueueStage.storeObject_nonTcb hS hPre (fun _ e => by cases e) (fun _ e => by cases e)
  · exact storeObject_tcbOver_runQueueStage (tid := SeLe4n.ThreadId.ofObjId addr.cnode) (old := t)
      ((SystemState.getTcb?_eq_some_iff st _ t).mpr hPre) hS (fun _ => rfl)

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (cspaceDeleteSlotCore_runQueueStage (by with_reducible assumption)))

theorem cspaceMove_runQueueStage {st st' : SystemState} {src dst : CSpaceAddr}
    (h : cspaceMove src dst st = .ok ((), st')) : RunQueueStage st st' := by
  unfold cspaceMove at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i cap stL hLk
      split at h
      · contradiction
      · rename_i capNN hNN
        split at h
        · contradiction
        · rename_i st2 hIns
          split at h
          · contradiction
          · rename_i st3 hDel
            cases h
            exact ((cspaceLookupSlot_runQueueStage hLk).trans
              (cspaceInsertSlot_runQueueStage hIns)).trans
              ((cspaceDeleteSlotCore_runQueueStage hDel).trans ((withCdt_runQueueStage _ _).trans
                (RunQueueStage.of_linkReach (SystemState.cdtMove_reach st3 src dst))))

theorem mintReplyCapWithCdt_runQueueStage {st st' : SystemState} {src dst : CSpaceAddr}
    (h : mintReplyCapWithCdt src dst st = .ok ((), st')) : RunQueueStage st st' := by
  unfold mintReplyCapWithCdt at h
  split at h
  · contradiction
  · rename_i stM hMint
    cases h
    have hM : RunQueueStage st stM := by
      unfold mintReplyCap at hMint; run_queue_stage_at hMint
    exact hM.trans (cdtRecord_runQueueStage stM src dst .mint)

theorem cspaceDeleteSlot_runQueueStage {st st' : SystemState} {addr : CSpaceAddr}
    (h : cspaceDeleteSlot addr st = .ok ((), st')) : RunQueueStage st st' := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' h
  exact (cspaceDeleteSlotCore_runQueueStage hCore).trans ((withCdt_runQueueStage _ _).trans
    (RunQueueStage.of_linkReach (spliceDeletedCdtNode_reach stC addr)))

theorem finaliseDestroyedCapabilities_runQueueStage {ec : Concurrency.CoreId} {named : List SeLe4n.ObjId}
    {pages : List MappedPage} {st st' : SystemState}
    (h : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) : RunQueueStage st st' :=
  vspaceRootOnlyWrite_runQueueStage fun hInv =>
    finaliseDestroyedCapabilities_ok_frame ec named pages st st' hInv h

theorem cspaceDeleteSlotFinalising_runQueueStage {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    RunQueueStage st st' := by
  obtain ⟨st1, hD, hF⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  exact (cspaceDeleteSlot_runQueueStage hD).trans (finaliseDestroyedCapabilities_runQueueStage hF)

theorem cspaceRevokeCdtFinalising_runQueueStage {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    RunQueueStage st st' :=
  cspaceRevokeCdtFinalising_closed (RunQueueStage st)
    (fun _ _ _ hQ hD => hQ.trans (cspaceDeleteSlotFinalising_runQueueStage hD))
    (RunQueueStage.refl st) h

/-- A store whose slot holds no TCB on either side. -/
theorem storeObject_inert_runQueueStage {st st' : SystemState} {oid : SeLe4n.ObjId}
    {obj old : KernelObject} (hStore : storeObject oid obj st = .ok ((), st'))
    (hPre : st.objects[oid]? = some old) (hOld : ∀ t, old ≠ .tcb t)
    (hObj : ∀ t, obj ≠ .tcb t) : RunQueueStage st st' :=
  RunQueueStage.storeObject_nonTcb hStore hPre hObj hOld

theorem tagFrameMapping_runQueueStage {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {frameId : SeLe4n.ObjId} {st st' : SystemState} {e : Nat}
    (h : tagFrameMapping asid vaddr frameId st = .ok (e, st')) : RunQueueStage st st' := by
  obtain ⟨f, rootId, root, st1, hF, hR, -, h1, h2⟩ := tagFrameMapping_ok asid vaddr frameId st st' e h
  have hRootPre := (Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hR).2.1
  have hFramePre := (SystemState.getFrame?_eq_some_iff st frameId f).mp hF
  refine RunQueueStage.of_inv fun hInv => ?_
  have hNe : frameId ≠ rootId := by
    intro hEq; rw [hEq, hRootPre] at hFramePre; cases hFramePre
  have hFrame1 : st1.objects[frameId]? = some (.frame f) := by
    rw [storeObject_objects_ne st st1 _ _ _ hNe hInv h1]; exact hFramePre
  exact (storeObject_inert_runQueueStage h1 hRootPre (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h)).trans
    (storeObject_inert_runQueueStage h2 hFrame1 (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h))

theorem cspaceRecordFrameMapping_runQueueStage {addr : CSpaceAddr} {m : FrameMapping}
    {st st' : SystemState} (h : cspaceRecordFrameMapping addr m st = .ok ((), st')) :
    RunQueueStage st st' := by
  obtain ⟨cn, cap, hCn, -, hStore⟩ := cspaceRecordFrameMapping_ok_decompose addr m st st' h
  exact storeObject_inert_runQueueStage hStore
    ((SystemState.getCNode?_eq_some_iff st addr.cnode cn).mp hCn) (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h)

theorem vspaceMapFromFrameCap_runQueueStage {tid : SeLe4n.ThreadId} {ec : Concurrency.CoreId}
    {args : Architecture.SyscallArgDecode.VSpaceMapArgs} {st st' : SystemState}
    (h : vspaceMapFromFrameCap tid ec args st = .ok ((), st')) : RunQueueStage st st' := by
  obtain ⟨_, _, _, st1, _, _, _, _, _, hMap, epoch, st2, hT, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid ec args st st' h
  exact ((vspaceRootOnlyWrite_runQueueStage fun hInv =>
      vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame _ _ _ _ _ st st1 hInv hMap).trans
    (tagFrameMapping_runQueueStage hT)).trans (cspaceRecordFrameMapping_runQueueStage hRec)

theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_runQueueStage {ec : Concurrency.CoreId}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {st st' : SystemState}
    (h : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) : RunQueueStage st st' :=
  vspaceRootOnlyWrite_runQueueStage fun hInv =>
    vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame ec asid vaddr st st' hInv h

theorem vspaceUnifyInstructionPage_runQueueStage {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState} (h : Architecture.vspaceUnifyInstructionPage asid vaddr st = .ok ((), st')) :
    RunQueueStage st st' :=
  have hF := Architecture.vspaceUnifyInstructionPage_frame h
  RunQueueStage.of_frame hF.1 (by rw [hF.2.2.1]) (by rw [hF.2.2.1]) (by rw [hF.2.2.1])

theorem untypedResetWithShootdown_runQueueStage {ec : Concurrency.CoreId} {untypedId : SeLe4n.ObjId}
    {st st' : SystemState} (h : untypedResetWithShootdown ec untypedId st = .ok ((), st')) :
    RunQueueStage st st' := by
  obtain ⟨st1, hR, hObj, hSched, -, -⟩ := untypedResetWithShootdown_ok_frame ec untypedId st st' h
  refine RunQueueStage.trans (st' := st1) (RunQueueStage.of_slots fun hInv => ?_)
    (RunQueueStage.of_frame hObj (by rw [hSched]) (by rw [hSched]))
  obtain ⟨hExt, hS1, hW⟩ := untypedReset_ok_frame ec untypedId st st1 hInv hR
  have hT : ∀ o : Option KernelObject, resetTouched o → ∀ c, SystemState.objRunLinkOn o c = RunQueue.RunQueueLink.none := by
    intro o h c
    cases o with
    | none => rfl
    | some obj => cases obj <;> first | rfl | exact absurd h (by simp [resetTouched])
  have hN : ∀ o : Option KernelObject, resetTouched o → SystemState.objTcb? o = none := by
    intro o h
    cases o with
    | none => rfl
    | some obj => cases obj <;> first | rfl | exact absurd h (by simp [resetTouched])
  refine ⟨hExt, fun oid c => ?_, fun oid => ?_, hS1⟩
  · rcases hW oid with e | ⟨t1, t2⟩
    · rw [e]
    · rw [hT _ t1, hT _ t2]
  · rcases hW oid with e | ⟨t1, t2⟩
    · exact SystemState.slotStateMono.of_eq e
    · refine ⟨fun x hx => ?_, fun x' hx' => ?_⟩
      · first | (rw [hN _ t1] at hx; cases hx) | (rw [hN _ t2] at hx; cases hx)
      · first | (rw [hN _ t1] at hx'; cases hx') | (rw [hN _ t2] at hx'; cases hx')

theorem revokeService_runQueueStage {sid : ServiceId} {st st' : SystemState}
    (h : revokeService sid st = .ok ((), st')) : RunQueueStage st st' :=
  have hS := revokeService_preserves_scheduler st st' sid h
  RunQueueStage.of_frame (revokeService_preserves_objects st st' sid h) (by rw [hS]) (by rw [hS])

theorem registerService_runQueueStage {reg : ServiceRegistration} {st st' : SystemState}
    (h : registerService reg st = .ok ((), st')) : RunQueueStage st st' :=
  have hS := registerService_preserves_scheduler st st' reg h
  RunQueueStage.of_frame (registerService_preserves_objects st st' reg h) (by rw [hS])
    (by rw [hS])

theorem lookupServiceByCap_runQueueStage {epId : SeLe4n.ObjId} {st st' : SystemState}
    {reg : ServiceRegistration} (h : lookupServiceByCap epId st = .ok (reg, st')) :
    RunQueueStage st st' :=
  RunQueueStage.of_eq (lookupServiceByCap_preserves_state epId st reg st' h)

/-! ### One-field TCB rewrites -/

/-- The raw-insert form of a TCB rewrite that keeps the run-queue fields. -/
theorem insertTcb_runQueueStage {st : SystemState} {tid : SeLe4n.ThreadId} {tcb tcb' : TCB}
    (hPre : st.objects[tid.toObjId]? = some (.tcb tcb))
    (h : ∀ c, tcb'.runLinkOn c = tcb.runLinkOn c) (hm : TCB.StepMono tcb tcb' := by exact ⟨id, id⟩) :
    RunQueueStage st { st with objects := st.objects.insert tid.toObjId (.tcb tcb') } :=
  RunQueueStage.insert rfl rfl rfl (fun c => by rw [hPre]; exact h c)
    (by rw [hPre]; exact SystemState.objStateMono_tcb hm)

theorem setIPCBufferOp_runQueueStage {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {addr : SeLe4n.VAddr}
    (h : Architecture.IpcBufferValidation.setIPCBufferOp st vtid addr = .ok st') :
    RunQueueStage st st' := by
  unfold Architecture.IpcBufferValidation.setIPCBufferOp at h
  run_queue_stage_at h

theorem setThreadFaultHandlerOp_runQueueStage {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cptr : SeLe4n.CPtr}
    (h : setThreadFaultHandlerOp st vtid cptr = .ok st') : RunQueueStage st st' := by
  cases hT : st.getTcb? vtid.val with
  | none => simp [setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_none hT] at h
  | some tcb =>
      cases hR : resolveFaultHandlerCPtr st tcb cptr with
      | error e => simp [setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_some hT, hR] at h
      | ok tgt =>
          rw [setThreadFaultHandlerOp_ok_eq st vtid cptr tcb tgt hT hR] at h
          cases h
          unfold installFaultHandler SystemState.rewriteObject
          exact insertTcb_runQueueStage ((SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hT)
            (fun _ => rfl)

theorem setThreadSpace_runQueueStage {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {cn vr : SeLe4n.ObjId} (h : setThreadSpace st vtid cn vr = .ok st') :
    RunQueueStage st st' := by
  obtain ⟨tcb, hT, -, -, -, -, rfl⟩ := setThreadSpace_ok st st' vtid cn vr h
  exact insertTcb_runQueueStage ((SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hT)
    (fun _ => rfl)

theorem bindNotification_runQueueStage {st st' : SystemState} {nid : SeLe4n.ObjId}
    {tcbId : SeLe4n.ThreadId} (h : bindNotification nid tcbId st = .ok ((), st')) :
    RunQueueStage st st' := by
  refine RunQueueStage.of_inv fun hInv => ?_
  unfold bindNotification at h
  split at h
  · rename_i ntfn hN
    split at h
    · contradiction
    · rename_i tcb hT
      split at h
      · contradiction
      · split at h
        · contradiction
        · rename_i hStore1
          split at h
          · contradiction
          · rename_i hStore2
            cases h
            have hNraw := (SystemState.getNotification?_eq_some_iff st nid ntfn).mp hN
            have hTraw := lookupTcb_some_objects st tcbId tcb hT
            have hNeIds : tcbId.toObjId ≠ nid := by
              intro hEq
              rw [hEq, hNraw] at hTraw
              exact absurd (Option.some.inj hTraw) (fun hx => KernelObject.noConfusion hx)
            have hPre1 := storeObject_objects_ne st _ nid tcbId.toObjId _ hNeIds hInv hStore1
            exact (storeObject_inert_runQueueStage hStore1 hNraw (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h)).trans
              (RunQueueStage.storeObject_tcb hStore2 (hPre1.trans hTraw) (fun _ => rfl))
  · split at h <;> contradiction

theorem unbindNotification_runQueueStage {st st' : SystemState} {tcbId : SeLe4n.ThreadId}
    (h : unbindNotification tcbId st = .ok ((), st')) : RunQueueStage st st' := by
  refine RunQueueStage.of_inv fun hInv => ?_
  unfold unbindNotification at h
  split at h
  · contradiction
  · rename_i tcb hT
    split at h
    · contradiction
    · rename_i nid hBound
      split at h
      · contradiction
      · rename_i hStore1
        have k1 := RunQueueStage.storeObject_tcb hStore1 (lookupTcb_some_objects st tcbId tcb hT)
          (fun _ => rfl)
        split at h
        · rename_i ntfn hN1
          split at h
          · contradiction
          · rename_i hStore2
            cases h
            exact k1.trans (storeObject_inert_runQueueStage hStore2
              ((SystemState.getNotification?_eq_some_iff _ nid ntfn).mp hN1) (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h))
        · cases h; exact k1

/-! ### Page tables and the untyped carve -/

theorem recordPhysicalWrites_runQueueStage' (st : SystemState)
    (ws : List Architecture.PhysicalWrite) :
    RunQueueStage st (Architecture.recordPhysicalWrites st ws) :=
  RunQueueStage.of_frame (Architecture.recordPhysicalWrites_objects _ _)
    (by rw [Architecture.recordPhysicalWrites_scheduler])
    (by rw [Architecture.recordPhysicalWrites_scheduler])

theorem pageTableMap_runQueueStage {tableId rootId : SeLe4n.ObjId} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState} (h : Architecture.pageTableMap tableId rootId vaddr st = .ok ((), st')) :
    RunQueueStage st st' := by
  refine RunQueueStage.of_inv fun hInv => ?_
  obtain ⟨table, root, level, st1, hT, hR, -, -, -, -, hS1, hS2⟩ :=
    Architecture.pageTableMap_ok tableId rootId vaddr st st' h
  have hT' := (SystemState.getPageTable?_eq_some_iff st tableId table).mp hT
  have hR' := (SystemState.getVSpaceRoot?_eq_some_iff st rootId root).mp hR
  have hNe : rootId ≠ tableId := by
    intro hEq; subst hEq; rw [hT'] at hR'; cases hR'
  have hR1 : ∀ ws, (Architecture.recordPhysicalWrites st1 ws).objects[rootId]? =
      some (.vspaceRoot root) := fun _ => by
    rw [Architecture.recordPhysicalWrites_objects, storeObject_objects_ne _ _ _ _ _ hNe hInv hS1]
    exact hR'
  exact ((storeObject_inert_runQueueStage hS1 hT' (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h)).trans
    (recordPhysicalWrites_runQueueStage' _ _)).trans
    (storeObject_inert_runQueueStage hS2 (hR1 _) (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h))

theorem pageTableUnmap_runQueueStage {tableId : SeLe4n.ObjId} {st st' : SystemState}
    (h : Architecture.pageTableUnmap tableId st = .ok ((), st')) : RunQueueStage st st' := by
  refine RunQueueStage.of_inv fun hInv => ?_
  unfold Architecture.pageTableUnmap at h
  cases hT : st.getPageTable? tableId with
  | none => rw [hT] at h; cases h
  | some table =>
    rw [hT] at h
    have hT' := (SystemState.getPageTable?_eq_some_iff st tableId table).mp hT
    simp only at h
    cases hI : table.installedIn with
    | none => rw [hI] at h; cases h; exact RunQueueStage.refl _
    | some inst =>
      rw [hI] at h
      simp only at h
      cases hR : st.getVSpaceRoot? inst.root with
      | none => rw [hR] at h; exact storeObject_inert_runQueueStage h hT' (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h)
      | some root =>
        rw [hR] at h
        have hR' := (SystemState.getVSpaceRoot?_eq_some_iff st inst.root root).mp hR
        simp only at h
        split at h
        · split at h
          · cases h
          · cases hS1 : storeObject tableId _ st with
            | error e => rw [hS1] at h; cases h
            | ok p =>
              obtain ⟨⟨⟩, st1⟩ := p
              rw [hS1] at h
              have hNe : inst.root ≠ tableId := by
                intro hEq; rw [hEq, hT'] at hR'; cases hR'
              have hR1 : ∀ ws, (Architecture.recordPhysicalWrites st1 ws).objects[inst.root]? =
                  some (.vspaceRoot root) := fun _ => by
                rw [Architecture.recordPhysicalWrites_objects,
                  storeObject_objects_ne _ _ _ _ _ hNe hInv hS1]
                exact hR'
              exact ((storeObject_inert_runQueueStage hS1 hT' (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h)).trans
                (recordPhysicalWrites_runQueueStage' _ _)).trans
                (storeObject_inert_runQueueStage h (hR1 _) (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h))
        · exact storeObject_inert_runQueueStage h hT' (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h)

theorem untypedRetypeObject_runQueueStage {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {st st' : SystemState}
    (h : untypedRetypeObject src childId dst req st = .ok ((), st')) : RunQueueStage st st' := by
  refine RunQueueStage.of_inv fun hInv => ?_
  obtain ⟨_, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hInv h
  have hFresh := retypeFromUntyped_childId_fresh src untypedId childId _ _ st st1 hRt
  obtain ⟨ut₀, ut', cap, stL, stUt, _, hUt, _, _, hLk, _, _, hStUt, hStCh⟩ :=
    retypeFromUntyped_ok_decompose st st1 src untypedId childId _ _ hRt
  have hStL : stL = st := cspaceLookupSlot_ok_state_eq st src cap stL hLk
  subst hStL
  have hNe : childId ≠ untypedId := by
    intro h; rw [h, hUt] at hFresh; simp at hFresh
  have hChildNone : stUt.objects[childId]? = none := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hInv hStUt]
    cases h : stL.objects[childId]? with
    | none => rfl
    | some _ => rw [h] at hFresh; simp at hFresh
  have k1 := storeObject_inert_runQueueStage hStUt hUt (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h)
  have k2 : RunQueueStage stUt st1 :=
    RunQueueStage.storeObject hStCh (fun c => by rw [hChildNone]; cases req <;> rfl)
      (by
        rw [hChildNone]
        cases req <;> first
          | exact SystemState.objStateMono_nonTcb rfl rfl
          | exact ⟨fun _ h => by cases h, fun _ h _ => by cases h; exact .inl rfl⟩)
  have kZ : RunQueueStage st1 (req.scrub st1 ut) :=
    RunQueueStage.of_frame (CarveRequest.scrub_objects _ _ _)
      (by rw [CarveRequest.scrub_scheduler]) (by rw [CarveRequest.scrub_scheduler]) (by rw [CarveRequest.scrub_scheduler])
  exact (((k1.trans k2).trans kZ).trans (cspaceInsertSlot_runQueueStage hIns)).trans
    (cdtRecord_runQueueStage _ _ _ _)

end SeLe4n.Kernel
