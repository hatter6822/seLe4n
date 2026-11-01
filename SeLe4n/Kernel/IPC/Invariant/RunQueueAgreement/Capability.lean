/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Endpoint
import SeLe4n.Kernel.API
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation
import SeLe4n.Kernel.SlotConfinement.MemoryArms

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
      st'.scheduler = st.scheduler)
    (hF : st.objects.invExt → SystemState.TableReferenceFrame st st')
    (hR : st.objects.invExt → ∀ (oid : SeLe4n.ObjId) (c : Concurrency.CoreId),
      SystemState.objReleaseLinkOn st'.objects[oid]? c = SystemState.objReleaseLinkOn st.objects[oid]? c)
    (hV : st.objects.invExt → ∀ oid : SeLe4n.ObjId,
      objRefillView st'.objects[oid]? = objRefillView st.objects[oid]?)
    (hY : st.objects.invExt → ∀ oid : SeLe4n.ObjId,
      objYieldCodes st'.objects[oid]? = objYieldCodes st.objects[oid]?)
    (hRes : st'.machine.residentCode = st.machine.residentCode) :
    RunQueueStage st st' :=
  have hL : st.objects.invExt → ∀ c t, st'.runLinkOn c t = st.runLinkOn c t := fun hInv c t => by
    rw [SystemState.runLinkOn_eq_objRunLinkOn, SystemState.runLinkOn_eq_objRunLinkOn]
    exact (h hInv).2.1 _ c
  ⟨.of_tableFrame (fun hInv r => ⟨(h hInv).1,
      SystemState.runQueueRefined_of_frame (hL hInv) (by rw [(h hInv).2.2.2])
        (by rw [(h hInv).2.2.2]) r⟩) hF
      (fun hInv => ⟨.of_objReleaseLinkOn (hR hInv), by rw [(h hInv).2.2.2]⟩)
      (fun hInv => .of_eq (hV hInv)) hY hRes,
    fun _ hInv _ _ d => SystemState.currentDequeuedUniqueExcept_of_eq (by rw [(h hInv).2.2.2])
      (hL hInv) (SystemState.StateMono.of_slots (h hInv).2.2.1) d,
    fun hInv _ => SystemState.StateMono.of_slots (h hInv).2.2.1⟩

/-- A write confined to VSpace roots moves no thread's run-queue entry. -/
theorem vspaceRootOnlyWrite_runQueueStage {st st' : SystemState}
    (h : st.objects.invExt →
      st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler ∧
        st'.referenceTables = st.referenceTables)
    (hRes : st'.machine.residentCode = st.machine.residentCode) :
    RunQueueStage st st' :=
  RunQueueStage.of_slots (fun hInv =>
    have ⟨hI, hW, hS, _⟩ := h hInv
    ⟨hI, fun oid c => by
      rcases hW oid with e | ⟨⟨r, h1⟩, ⟨r', h2⟩⟩
      · rw [e]
      · rw [h1, h2]; rfl, fun oid => by
      rcases hW oid with e | ⟨⟨r, h1⟩, ⟨r', h2⟩⟩
      · exact SystemState.slotStateMono.of_eq e
      · exact SystemState.slotStateMono.of_obj h2
          (SystemState.objStateMono_nonTcb (by rw [h1]; rfl) rfl), hS⟩)
    (fun hInv => .of_getElem (h hInv).2.2.2 fun oid => by
      rcases (h hInv).2.1 oid with e | ⟨⟨r, h1⟩, ⟨r', h2⟩⟩
      · rw [e]
      · rw [h1, h2]; rfl)
    (fun hInv oid c => by
      rcases (h hInv).2.1 oid with e | ⟨⟨r, h1⟩, ⟨r', h2⟩⟩
      · rw [e]
      · rw [h1, h2]; rfl)
    (fun hInv oid => by
      rcases (h hInv).2.1 oid with e | ⟨⟨r, h1⟩, ⟨r', h2⟩⟩
      · rw [e]
      · rw [h1, h2]; rfl)
    (fun hInv oid => by
      rcases (h hInv).2.1 oid with e | ⟨⟨r, h1⟩, ⟨r', h2⟩⟩
      · rw [e]
      · rw [h1, h2]; rfl) hRes

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
        (by rw [hcn]; exact SystemState.objStateMono_tcb ⟨id, id, rfl⟩)
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

/-- WS-ZA ZA5.4: a free-index write stores a CNode over a CNode, or writes
nothing. -/
theorem setCapFreeIndex_runQueueStage (st : SystemState) (addr : CSpaceAddr) (idx : Nat) :
    RunQueueStage st (setCapFreeIndex st addr idx) := by
  cases hO : st.objects[addr.cnode]? with
  | some o =>
    cases o with
    | cnode cn =>
      exact RunQueueStage.storeObject_nonTcb (setCapFreeIndex_eq_storeObject hO) hO
        (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h)
    | _ => unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO]; exact RunQueueStage.refl _
  | none => unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO]; exact RunQueueStage.refl _

theorem untypedSourceSetFull_runQueueStage (st : SystemState) (src : CSpaceAddr)
    (cap : Capability) : RunQueueStage st (untypedSourceSetFull st src cap) :=
  untypedSourceSetFull_of (P := RunQueueStage st) (RunQueueStage.refl _)
    fun idx => setCapFreeIndex_runQueueStage st src idx

theorem cspaceMintWithCdt_runQueueStage {st st' : SystemState} {src dst : CSpaceAddr}
    {rights : AccessRightSet} {badge : Option SeLe4n.Badge}
    (h : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) : RunQueueStage st st' := by
  obtain ⟨_, stM, hMint, -, -, rfl⟩ := cspaceMintWithCdt_ok_decompose h
  exact ((cspaceMint_runQueueStage hMint).trans (cdtRecord_runQueueStage stM src dst .mint)).trans
    (untypedSourceSetFull_runQueueStage _ _ _)

theorem cspaceCopy_runQueueStage {st st' : SystemState} {src dst : CSpaceAddr}
    (h : cspaceCopy src dst st = .ok ((), st')) : RunQueueStage st st' := by
  obtain ⟨_, st2, -, -, hIns, -, rfl⟩ := cspaceCopy_ok_decompose h
  exact ((cspaceInsertSlot_runQueueStage hIns).trans (cdtRecord_runQueueStage st2 src dst .copy)).trans
    (untypedSourceSetFull_runQueueStage _ _ _)

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

/-- **A write of the kinds a retire touches is a run-queue stage**: no key it
changes holds a TCB on either side (`retireTouched`), and it frames the
scheduler.  The final-delete retire is such a write. -/
theorem RunQueueStage.of_retireTouched {st st' : SystemState}
    (h : st.objects.invExt → st'.objects.invExt ∧ st'.scheduler = st.scheduler ∧
      ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
        (retireTouched st.objects[oid]? ∧ retireTouched st'.objects[oid]?))
    (hF : st.objects.invExt → SystemState.TableReferenceFrame st st')
    (hRes : st'.machine.residentCode = st.machine.residentCode) :
    RunQueueStage st st' := by
  have hRT : ∀ o : Option KernelObject, retireTouched o → ∀ c,
      SystemState.objReleaseLinkOn o c = none := by
    intro o h c
    cases o with
    | none => rfl
    | some obj => cases obj <;> first | rfl | exact absurd h (by simp [retireTouched])
  have hVT : ∀ o : Option KernelObject, retireTouched o → objRefillView o = none := by
    intro o h
    cases o with
    | none => rfl
    | some obj => cases obj <;> first | rfl | exact absurd h (by simp [retireTouched])
  refine RunQueueStage.of_slots (fun hInv => ?_) hF (fun hInv oid c => by
    rcases (h hInv).2.2 oid with e | ⟨t1, t2⟩
    · rw [e]
    · rw [hRT _ t1, hRT _ t2]) (fun hInv oid => by
    rcases (h hInv).2.2 oid with e | ⟨t1, t2⟩
    · rw [e]
    · rw [hVT _ t1, hVT _ t2]) (fun hInv oid => by
    rcases (h hInv).2.2 oid with e | ⟨t1, t2⟩
    · rw [e]
    · rw [objYieldCodes_of_retireTouched t1, objYieldCodes_of_retireTouched t2]) hRes
  obtain ⟨hExt, hS1, hW⟩ := h hInv
  have hT : ∀ o : Option KernelObject, retireTouched o → ∀ c, SystemState.objRunLinkOn o c = RunQueue.RunQueueLink.none := by
    intro o h c
    cases o with
    | none => rfl
    | some obj => cases obj <;> first | rfl | exact absurd h (by simp [retireTouched])
  have hN : ∀ o : Option KernelObject, retireTouched o → SystemState.objTcb? o = none := by
    intro o h
    cases o with
    | none => rfl
    | some obj => cases obj <;> first | rfl | exact absurd h (by simp [retireTouched])
  refine ⟨hExt, fun oid c => ?_, fun oid => ?_, hS1⟩
  · rcases hW oid with e | ⟨t1, t2⟩
    · rw [e]
    · rw [hT _ t1, hT _ t2]
  · rcases hW oid with e | ⟨t1, t2⟩
    · exact SystemState.slotStateMono.of_eq e
    · refine ⟨fun x hx => ?_, fun x' hx' => ?_⟩
      · first | (rw [hN _ t1] at hx; cases hx) | (rw [hN _ t2] at hx; cases hx)
      · first | (rw [hN _ t1] at hx'; cases hx') | (rw [hN _ t2] at hx'; cases hx')

/-- **The final-delete retire is a run-queue stage.** -/
theorem retireFinalObject_runQueueStage (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) : RunQueueStage st (retireFinalObject ec target recorder st) :=
  have hS := (retireFinalObject_fields ec target recorder st).2.1
  have hL := fun hInv c t => retireFinalObject_runLinkOn ec target recorder (st := st) hInv c t
  ⟨⟨fun hInv r => ⟨(retireFinalObject_frame ec target recorder st hInv).1,
      SystemState.runQueueRefined_of_frame (hL hInv) (by rw [hS]) (by rw [hS]) r⟩,
      fun hInv _ hR => retireFinalObject_preserves_tableReferencesRecorded ec target recorder st
        hInv hR,
      fun hInv _ hR => (retireFinalObject_releaseStateAgree ec target recorder st hInv).refined hR,
      fun _ hInv _ hR x => SystemState.refillsSoundExcept_of_kept
        (.of_schedContexts_backward fun _ _ hp => retireFinalObject_back ec target recorder st hInv hp
          (fun _ h => KernelObject.noConfusion h))
        (fun c => by rw [(retireFinalObject_releaseStateAgree ec target recorder st hInv).replenishQueueOnCore c])
        ((retireFinalObject_releaseStateAgree ec target recorder st hInv).refined hR) x,
      fun hInv _ hY => SystemState.yieldLinksAgree_of_kept
        (retireFinalObject_yieldLinksKept ec target recorder st hInv) hY,
      fun hInv _ => .of_kept (retireFinalObject_yieldLinksKept ec target recorder st hInv)
        (by rw [(retireFinalObject_fields ec target recorder st).2.2])⟩,
    fun _ hInv _ _ d => SystemState.currentDequeuedUniqueExcept_of_eq (by rw [hS]) (hL hInv)
      (retireFinalObject_stateMono ec target recorder hInv) d,
    fun hInv _ => retireFinalObject_stateMono ec target recorder hInv⟩

theorem finaliseDestroyedCapabilities_runQueueStage {ec : Concurrency.CoreId} {named : List SeLe4n.ObjId}
    {pages : List MappedPage} {st st' : SystemState}
    (h : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) : RunQueueStage st st' :=
  vspaceRootOnlyWrite_runQueueStage (fun hInv =>
    finaliseDestroyedCapabilities_ok_frame ec named pages st st' hInv h)
    (congrArg MachineState.residentCode (finaliseDestroyedCapabilities_framed ec named pages st st' h).2)

/-- A store whose slot holds no TCB on either side. -/
theorem storeObject_inert_runQueueStage {st st' : SystemState} {oid : SeLe4n.ObjId}
    {obj old : KernelObject} (hStore : storeObject oid obj st = .ok ((), st'))
    (hPre : st.objects[oid]? = some old) (hOld : ∀ t, old ≠ .tcb t)
    (hObj : ∀ t, obj ≠ .tcb t)
    (hB : obj.tableBackLinks = old.tableBackLinks := by table_backlinks)
    (hR : ∀ c, SystemState.objReleaseLinkOn (some obj) c =
      SystemState.objReleaseLinkOn (some old) c := by release_links)
    (hV : objRefillView (some obj) = objRefillView (some old) := by refill_view)
    (hY : objYieldCodes (some obj) = objYieldCodes (some old) := by yield_codes) :
    RunQueueStage st st' :=
  RunQueueStage.storeObject_nonTcb hStore hPre hObj hOld hB hR hV hY

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
  exact ((vspaceRootOnlyWrite_runQueueStage (fun hInv =>
      vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame _ _ _ _ _ st st1 hInv hMap)
      (congrArg MachineState.residentCode
        (vspaceMapPageCheckedWithShootdownFromStatePerCore_framed _ _ _ _ _ st st1 hMap).2)).trans
    (tagFrameMapping_runQueueStage hT)).trans (cspaceRecordFrameMapping_runQueueStage hRec)

theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_runQueueStage {ec : Concurrency.CoreId}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {st st' : SystemState}
    (h : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) : RunQueueStage st st' :=
  vspaceRootOnlyWrite_runQueueStage (fun hInv =>
    vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame ec asid vaddr st st' hInv h)
    (congrArg MachineState.residentCode
      (vspaceUnmapPageWithShootdownAndIcacheBroadcast_framed ec asid vaddr st st' h).2)

theorem vspaceUnifyInstructionPage_runQueueStage {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState} (h : Architecture.vspaceUnifyInstructionPage asid vaddr st = .ok ((), st')) :
    RunQueueStage st st' :=
  have hF := Architecture.vspaceUnifyInstructionPage_frame h
  RunQueueStage.of_frame hF.1 (by rw [hF.2.2.1]) (by rw [hF.2.2.1]) (by rw [hF.2.2.1])
    (by simp only [SystemState.referenceTables, hF.2.2.2.2.2.2.2,
      Architecture.vspaceUnifyInstructionPage_declassificationTaint h])

/-- WS-ZA ZA5.4: the untyped reset is one free-index write
(`untypedResetSlot_ok_frame`). -/
theorem untypedResetSlot_runQueueStage {srcCnode : SeLe4n.ObjId} {srcSlot : SeLe4n.Slot}
    {st st' : SystemState} (h : untypedResetSlot srcCnode srcSlot st = .ok ((), st')) :
    RunQueueStage st st' := by
  rw [untypedResetSlot_ok_frame h]; exact setCapFreeIndex_runQueueStage _ _ _

/-- The registry's one object write — an endpoint's `serviceRegistered` — moves no
run-queue link: the endpoint holds none, before or after. -/
theorem serviceRecordRewrite_runQueueStage {st st' : SystemState}
    (hW : ServiceRecordRewrite st.objects st'.objects)
    (hS : st'.scheduler = st.scheduler)
    (hTab : st.objects.invExt → st.tableReferencesRecorded → st'.tableReferencesRecorded)
    (hM : st'.machine = st.machine) :
    RunQueueStage st st' := by
  rcases hW with h | ⟨e, ep, c, hE0, h⟩
  · exact RunQueueStage.of_frameWith h (by rw [hS]) (by rw [hS]) hTab (by rw [hS]) (hRes := by rw [hM])
  · exact RunQueueStage.insertWith h (by rw [hS]) (by rw [hS]) (fun _ => by rw [hE0]; rfl)
      (SystemState.objStateMono_nonTcb (by rw [hE0]; rfl) rfl) hTab (by rw [hS]) (hRes := by rw [hM])

/-- The revocation writes the registry and its endpoint's back-link
(`revokeService_preserves_tableReferencesRecorded`). -/
theorem revokeService_runQueueStage {sid : ServiceId} {st st' : SystemState}
    (h : revokeService sid st = .ok ((), st')) : RunQueueStage st st' :=
  serviceRecordRewrite_runQueueStage (revokeService_serviceRecordRewrite h)
    (revokeService_preserves_scheduler st st' sid h)
    (fun hInv hR => revokeService_preserves_tableReferencesRecorded h hInv hR)
    (revokeService_preserves_machine st st' sid h)

/-- The registration writes the registry and its endpoint's back-link
(`registerService_preserves_tableReferencesRecorded`). -/
theorem registerService_runQueueStage {reg : ServiceRegistration} {st st' : SystemState}
    (h : registerService reg st = .ok ((), st')) : RunQueueStage st st' :=
  serviceRecordRewrite_runQueueStage (registerService_serviceRecordRewrite h)
    (registerService_preserves_scheduler st st' reg h)
    (fun hInv hR => registerService_preserves_tableReferencesRecorded h hInv hR)
    (registerService_preserves_machine st st' reg h)

/-- WS-ZA ZA5.5: the release of a final endpoint's registration is a revocation
or nothing (`releaseFinalRegistration_cases`). -/
theorem releaseFinalRegistration_runQueueStage (target : Nat) (st : SystemState) :
    RunQueueStage st (releaseFinalRegistration target st) :=
  releaseFinalRegistration_closed (RunQueueStage st)
    (fun _ _ _ hQ hR => hQ.trans (revokeService_runQueueStage hR)) target st
    (RunQueueStage.refl st)

theorem lookupServiceByRecordedRegistration_runQueueStage {epId : SeLe4n.ObjId} {st st' : SystemState}
    {reg : ServiceRegistration} (h : lookupServiceByRecordedRegistration epId st = .ok (reg, st')) :
    RunQueueStage st st' :=
  RunQueueStage.of_eq (lookupServiceByRecordedRegistration_preserves_state epId st reg st' h)

/-! ### One-field TCB rewrites -/

/-- The raw-insert form of a TCB rewrite that keeps the run-queue fields. -/
theorem insertTcb_runQueueStage {st : SystemState} {tid : SeLe4n.ThreadId} {tcb tcb' : TCB}
    (hPre : st.objects[tid.toObjId]? = some (.tcb tcb))
    (h : ∀ c, tcb'.runLinkOn c = tcb.runLinkOn c) (hm : TCB.StepMono tcb tcb' := by exact ⟨id, id, by first | rfl | simp_all⟩)
    (hW : tcb'.taintWords = tcb.taintWords := by taint_words_kept)
    (hY : tcb'.yieldToCode = tcb.yieldToCode := by first | rfl | simp_all) :
    RunQueueStage st { st with objects := st.objects.insert tid.toObjId (.tcb tcb') } :=
  RunQueueStage.insert rfl rfl rfl (fun c => by rw [hPre]; exact h c)
    (by rw [hPre]; exact SystemState.objStateMono_tcb hm)
    (hY := by rw [hPre]; simp only [objYieldCodes, hY])

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

/-- A thread slot's copy: the delete, then a thread record rewritten in its
space slot alone, then link writes. -/
theorem threadSlotCopied_runQueueStage {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId)
    (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    RunQueueStage st (threadSlotCopied st tid slot srcCNode srcSlot rights) := by
  have hD := cspaceDeleteSlot_runQueueStage (copyIntoThreadSlot_delete hT slot)
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights with ⟨-, e⟩ | ⟨cap, -, e⟩
  · rw [e]; exact hD
  · rw [e]
    refine hD.trans (RunQueueStage.trans ?_ (cdtRecord_runQueueStage _ _ _ _))
    cases hU : (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
        { cnode := tid.toObjId, slot := slot }).getTcb? tid with
    | none => rw [SystemState.updateTcb_eq_self_of_none hU]; exact RunQueueStage.refl _
    | some u =>
      rw [SystemState.updateTcb_eq_of_some hU]
      exact insertTcb_runQueueStage ((SystemState.getTcb?_eq_some_iff _ _ _).mp hU) (fun _ => rfl)

/-- A thread space slot's set is a run-queue stage: the copy, then the retire. -/
theorem threadSlotSet_runQueueStage (ec : Concurrency.CoreId) {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    RunQueueStage st (threadSlotSet ec st tid slot srcCNode srcSlot rights) := by
  unfold threadSlotSet
  exact (threadSlotCopied_runQueueStage hT _ _ _ _).trans (retireFinalObject_runQueueStage ec _ _ _)

theorem copyThreadSpaces_runQueueStage {ec : Concurrency.CoreId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId}
    {cnSrc vrSrc : CSpaceAddr} (h : copyThreadSpaces ec st vtid cnSrc vrSrc = .ok st') :
    RunQueueStage st st' := by
  refine RunQueueStage.of_inv fun hInv => ?_
  obtain ⟨tcb, hT, -, -, hCn, -, rfl⟩ := copyThreadSpaces_ok h
  obtain ⟨cnCap, -, hCL, -⟩ := cspaceRootSourceAdmitted_spec hCn
  obtain ⟨t1, hT1'⟩ := Option.isSome_iff_exists.mp
    (threadSlotSet_getTcb? ec hInv hT (slot := TCB.cspaceRootSlot) (by decide)
      cnSrc.cnode cnSrc.slot
      TCB.cspaceRootRights hCL)
  exact (threadSlotSet_runQueueStage ec hT _ _ _ _).trans
    (threadSlotSet_runQueueStage ec hT1' _ _ _ _)

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

/-! ### The finalisation of a final delete's object -/

/-- **A cancelled waiter's wake is a stage**: the walk asked that no core runs
the thread (`cancelledWaiterWakeable`), and the thread is active. -/
theorem wakeCancelledWaiter_runQueueStage (st : SystemState) (t : SeLe4n.ThreadId)
    (hRun : runningOnSomeCore st t = false) (hA : st.activeAt t) :
    RunQueueStage st (wakeCancelledWaiter st t) :=
  enqueueRunnableOnCore_runQueueStage st _ t
    (fun c => currentNowhere_of_runningOnSomeCore_false hRun c) hA (homedOn_determineTargetCore _ _)

/-- **An endpoint waiter's cancel is a stage**: the head pop
(`endpointQueuePopHead_runQueueStage`, through `popHead_inPlace`), the waiter's
TCB rewritten with its run-queue links and its activity kept and its IPC state
made `.ready`, and the wake of a thread no core runs. -/
theorem storeEndpointWaiterCancelled_runQueueStage (st : SystemState)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (ep : Endpoint) (t : SeLe4n.ThreadId)
    (tcb : TCB) (hE : st.getEndpoint? endpointId = some ep)
    (hH : (endpointWaitQueue ep isReceiveQ).head = some t) (hT : st.getTcb? t = some tcb)
    (hC : endpointWaiterCancellable st endpointId t tcb = true) :
    RunQueueStage st (storeEndpointWaiterCancelled st endpointId isReceiveQ t tcb.queueNext) := by
  refine RunQueueStage.of_invExt fun hInv => ?_
  obtain ⟨hW, -, hG⟩ := endpointWaiterCancellable_parts hC
  simp only [cancelledWaiterWakeable, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hW
  have hEo := (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hE
  have hTo := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
  have hH' : (if isReceiveQ then ep.receiveQ else ep.sendQ).head = some t := hH
  obtain ⟨hPop, hFr⟩ := popHead_inPlace st endpointId isReceiveQ ep t tcb hEo hH' hTo hG
  have hS1 := endpointQueuePopHead_scheduler_eq endpointId isReceiveQ st _ t hPop
  have hI1 :=
    endpointQueuePopHead_preserves_objects_invExt endpointId isReceiveQ st _ t tcb hInv hPop
  unfold storeEndpointWaiterCancelled wakeCancelledWaiter
  generalize storePopHead st endpointId isReceiveQ t tcb.queueNext = s1 at hPop hFr hS1 hI1 ⊢
  have hM : TCB.StateMono cancelledEndpointWaiterTcb := fun x =>
    ⟨fun _ => TCB.ipcState_setIpcState
      { x with pendingMessage := none, pendingReceiveReplyCode := 0 } .ready, id, rfl⟩
  refine ((endpointQueuePopHead_runQueueStage hPop).trans
    (RunQueueStage.updateTcb s1 t (f := cancelledEndpointWaiterTcb) (fun _ _ => rfl) hM)).trans
    (enqueueRunnableOnCore_runQueueStage _ _ t (fun c => ?_) ?_ (homedOn_determineTargetCore _ _))
  · have hR : runningOnSomeCore (s1.updateTcb t cancelledEndpointWaiterTcb) t =
        runningOnSomeCore st t := by
      unfold runningOnSomeCore; rw [SystemState.updateTcb_scheduler, hS1]
    exact currentNowhere_of_runningOnSomeCore_false (hR.trans hW.2) c
  · exact ⟨cancelledEndpointWaiterTcb (tcbOffQueue tcb),
      by rw [SystemState.updateTcb_getTcb?_self _ _ _ hI1, hFr.head_tcb]; rfl, hW.1⟩

/-- The guarded removal of a thread from an endpoint queue: endpoint stores and
queue-link writes. -/
theorem endpointQueueRemoveDual_runQueueStage {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (h : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    RunQueueStage st st' := by
  refine RunQueueStage.of_inv fun hInv => ?_
  cases endpointQueueRemoveDual_shape st st' endpointId isReceiveQ tid h with
  | headLast ep tcb s1 s2 hEp _ _ _ _ _ _ hS1 hS2 hClear =>
    exact ((storeObject_endpoint_runQueueStage hEp hS1).trans
      (storeObject_endpoint_runQueueStage
        (storeObject_objects_eq _ _ _ _ hInv hS1) hS2)).trans
      (storeTcbQueueLinks_runQueueStage hClear)
  | headMore ep tcb nextTcb nextTid s1 s2 s3 hEp _ _ _ _ _ _ hS1 _ hRelink hS2 hClear =>
    have i1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
    have hEp2 := storeTcbQueueLinks_endpoint_eq i1 hRelink
      (storeObject_objects_eq _ _ _ _ hInv hS1)
    exact (((storeObject_endpoint_runQueueStage hEp hS1).trans
      (storeTcbQueueLinks_runQueueStage hRelink)).trans
      (storeObject_endpoint_runQueueStage hEp2 hS2)).trans
      (storeTcbQueueLinks_runQueueStage hClear)
  | midLast ep tcb prevTcb prevTid s1 s2 hEp _ _ _ _ _ _ _ _ _ hRelink hS hClear =>
    have hEp1 := storeTcbQueueLinks_endpoint_eq hInv hRelink hEp
    exact ((storeTcbQueueLinks_runQueueStage hRelink).trans
      (storeObject_endpoint_runQueueStage hEp1 hS)).trans
      (storeTcbQueueLinks_runQueueStage hClear)
  | midMore ep tcb prevTcb nextTcb prevTid nextTid s1 s2 s3 hEp _ _ _ _ _ _ _ _ _
      hRelinkPrev _ hRelinkNext hS hClear =>
    have i1 := storeTcbQueueLinks_preserves_objects_invExt _ _ _ _ _ _ hInv hRelinkPrev
    have hEp1 := storeTcbQueueLinks_endpoint_eq hInv hRelinkPrev hEp
    have hEp2 := storeTcbQueueLinks_endpoint_eq i1 hRelinkNext hEp1
    exact (((storeTcbQueueLinks_runQueueStage hRelinkPrev).trans
      (storeTcbQueueLinks_runQueueStage hRelinkNext)).trans
      (storeObject_endpoint_runQueueStage hEp2 hS)).trans
      (storeTcbQueueLinks_runQueueStage hClear)

/-- **A thread's endpoint cancel is a stage**: the removal
(`endpointQueueRemoveDual_runQueueStage`, through `queueRemove_inPlace`), then
the thread's TCB rewritten with its run-queue links and its activity kept and its
IPC state made `.ready`. -/
theorem storeEndpointBlockedCancelled_runQueueStage (st : SystemState) (e : SeLe4n.ObjId)
    (q : Bool) (t : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB)
    (hT : st.getTcb? t = some tcb) (hE : st.getEndpoint? e = some ep)
    (hC : endpointBlockedCancellable st e q t ep tcb = true) :
    RunQueueStage st (storeEndpointBlockedCancelled st e q t ep tcb) := by
  obtain ⟨-, -, hG, -⟩ := endpointBlockedCancellable_parts hC
  obtain ⟨hRem, -⟩ := queueRemove_inPlace st e q t ep tcb
    ((SystemState.getEndpoint?_eq_some_iff st e ep).mp hE)
    ((SystemState.getTcb?_eq_some_iff st t tcb).mp hT) hG
  have hM : TCB.StateMono cancelledEndpointWaiterTcb := fun x =>
    ⟨fun _ => TCB.ipcState_setIpcState
      { x with pendingMessage := none, pendingReceiveReplyCode := 0 } .ready, id, rfl⟩
  unfold storeEndpointBlockedCancelled
  exact (endpointQueueRemoveDual_runQueueStage hRem).trans
    (RunQueueStage.updateTcb _ t (f := cancelledEndpointWaiterTcb) (fun _ _ => rfl) hM)

/-- **A notification waiter's cancel is a stage**: the cancellation
(`cancelIpcBlocking_runQueueStage`) keeps the thread active
(`cancelIpcBlocking_stateMono`) and moves no core's current thread, then the
wake. -/
theorem notificationWaiterCancel_runQueueStage (st : SystemState)
    (notificationId : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hT : st.getTcb? t = some tcb)
    (hC : notificationWaiterCancellable st notificationId t tcb = true) :
    RunQueueStage st (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking st t tcb) t) := by
  refine RunQueueStage.of_invExt fun hInv => ?_
  obtain ⟨-, -, -, -, hW⟩ := notificationWaiterCancellable_parts hC
  simp only [cancelledWaiterWakeable, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hW
  refine (cancelIpcBlocking_runQueueStage st t tcb).trans
    (wakeCancelledWaiter_runQueueStage _ t ?_
      ((cancelIpcBlocking_stateMono st t tcb hInv).activeAt ⟨tcb, hT, hW.1⟩))
  unfold runningOnSomeCore
  rw [Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq]
  exact hW.2

/-- **A finalised thread's suspend is a kernel entry's worth of run-queue
steps**: a ready thread, no core's idle thread, taken off whichever core holds
it — queued there or current there — and marked `.Inactive`
(`descheduleAtPlacedThenOffWrite_runQueueEntryStage`).  It is no stage: the
thread was runnable and is not after it, which is what a suspend is. -/
theorem finaliseSuspend_runQueueEntryStage (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hT : st.getTcb? t = some tcb) (hS : tcb.ipcStateCode = 0) (hO : tcb.ipcObjectCode = 0)
    (hId : isIdleThreadId t = false) :
    SystemState.RunQueueEntryStage st
      ((descheduleAtPlacement st t).updateTcb t finalisedSuspendMark) :=
  descheduleAtPlacedThenOffWrite_runQueueEntryStage st t
    (fun _ x hx => by
      rw [hT] at hx; cases hx
      unfold TCB.ipcState; rw [hS, hO]; rfl)
    hId (fun _ _ => rfl) (fun _ h => h)

/-- A scheduling context rewritten in its slot is a run-queue stage: it writes
no thread and no scheduler field. -/
theorem updateSchedContext_runQueueStage (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext)
    (hf : ∀ sc, (f sc).releaseNextCode = sc.releaseNextCode ∧
      (f sc).releaseCoreCode = sc.releaseCoreCode ∧ (f sc).releaseAt = sc.releaseAt := by
        intro _; exact ⟨rfl, rfl, rfl⟩)
    (hv : ∀ sc, (f sc).refillView = sc.refillView := by intro _; rfl)
    (hy : ∀ sc, (f sc).yieldFromCode = sc.yieldFromCode := by intro _; first | rfl | simp) :
    SystemState.RunQueueStage st (st.updateSchedContext scId f) := by
  have hU := SystemState.updateSchedContext_scheduler st scId f
  apply SystemState.RunQueueStage.of_placement
  · exact fun hInv => SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv
  · show (st.updateSchedContext scId _).scheduler.runQueue = _
    rw [hU]
  · show (st.updateSchedContext scId _).scheduler.runQueueEnds = _
    rw [hU]
  · intro hInv x
    exact congrArg (Option.map TCB.placement)
      (SystemState.updateSchedContext_getTcb? st scId _ hInv x)
  · exact fun hInv => SystemState.StateMono.of_getTcb
      (SystemState.updateSchedContext_getTcb? st scId _ hInv)
  · exact SystemState.TableReferenceFrame.updateSchedContext st scId _
  · exact fun hInv => .updateSchedContext st scId f hInv hf
  · exact fun hInv => .updateSchedContext st scId f hInv hv
  · exact fun hInv => Kernel.YieldLinksKept.updateSchedContext st scId f hInv hy
  · show (st.updateSchedContext scId _).scheduler.currentCode = _
    rw [hU]
  · exact congrArg MachineState.residentCode (SystemState.updateSchedContext_machine st scId _)

/-- WS-ZA ZA6.4: **a context update that may write its refills is a frame stage
off that context** — the drain's refill, whose placement closes it. -/
theorem updateSchedContext_runQueueFrameStage (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext)
    (hf : ∀ sc, (f sc).releaseNextCode = sc.releaseNextCode ∧
      (f sc).releaseCoreCode = sc.releaseCoreCode ∧ (f sc).releaseAt = sc.releaseAt)
    (hy : ∀ sc, (f sc).yieldFromCode = sc.yieldFromCode := by intro _; first | rfl | simp) :
    SystemState.RunQueueFrameStage (· = scId) st (st.updateSchedContext scId f) := by
  have hU := SystemState.updateSchedContext_scheduler st scId f
  apply SystemState.RunQueueFrameStage.of_placement
  · exact fun hInv => SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv
  · show (st.updateSchedContext scId _).scheduler.runQueue = _
    rw [hU]
  · show (st.updateSchedContext scId _).scheduler.runQueueEnds = _
    rw [hU]
  · intro hInv x
    exact congrArg (Option.map TCB.placement)
      (SystemState.updateSchedContext_getTcb? st scId _ hInv x)
  · exact fun hInv => SystemState.StateMono.of_getTcb
      (SystemState.updateSchedContext_getTcb? st scId _ hInv)
  · exact SystemState.TableReferenceFrame.updateSchedContext st scId _
  · exact fun hInv => .updateSchedContext st scId f hInv hf
  · exact fun hInv => SystemState.RefillsKeptOff.updateSchedContext st scId f hInv
  · exact fun hInv => Kernel.YieldLinksKept.updateSchedContext st scId f hInv hy
  · show (st.updateSchedContext scId _).scheduler.currentCode = _
    rw [hU]
  · exact congrArg MachineState.residentCode (SystemState.updateSchedContext_machine st scId _)

/-- The revert of a finalised reply's caller's boost is a run-queue stage
(`propagatePipChainCrossCore_runQueueStage`). -/
theorem finaliseReplyRevert_runQueueStage (st : SystemState) (server? : Option SeLe4n.ThreadId) :
    SystemState.RunQueueStage st (finaliseReplyRevert st server?) := by
  cases server? with
  | none => exact .refl st
  | some s => exact PriorityInheritance.propagatePipChainCrossCore_runQueueStage st s _ _

/-- The finalisation's notification unbind is a run-queue stage. -/
theorem finaliseUnbindStep_runQueueEntryStage (st : SystemState) :
    FinaliseUnbindStep (SystemState.RunQueueEntryStage st) :=
  fun n s _ t h _ _ hCode hIn => by
    have hSpec := unbindNotification_of_inPlace s t hIn
    rw [hCode, Nat.add_sub_cancel] at hSpec
    exact h.trans (unbindNotification_runQueueStage hSpec).entry

/-- The finalisation's notification cancel is a run-queue stage. -/
theorem finaliseNotificationCancelStep_runQueueEntryStage (st : SystemState) :
    FinaliseNotificationCancelStep (SystemState.RunQueueEntryStage st) :=
  fun s _ t tcb _ h _ _ _ _ => h.trans (cancelIpcBlocking_runQueueStage s t tcb).entry

/-- The finalisation's endpoint cancel is a run-queue stage. -/
theorem finaliseEndpointCancelStep_runQueueEntryStage (st : SystemState) :
    FinaliseEndpointCancelStep (SystemState.RunQueueEntryStage st) :=
  fun s e q t ep tcb h hT hE hC =>
    h.trans (storeEndpointBlockedCancelled_runQueueStage s e q t ep tcb hT hE hC).entry

/-- The finalisation's suspend is a kernel entry's worth of run-queue steps. -/
theorem finaliseSuspendStep_runQueueEntryStage (st : SystemState) :
    FinaliseSuspendStep (SystemState.RunQueueEntryStage st) :=
  fun s t tcb h hT hS hO _ hId => h.trans (finaliseSuspend_runQueueEntryStage s t tcb hT hS hO hId)

/-- The release of the cores' holds writes no object and no queue. -/
theorem finaliseReleaseStep_runQueueEntryStage (st : SystemState) :
    FinaliseReleaseStep (SystemState.RunQueueEntryStage st) :=
  fun s t h => h.trans (SystemState.RunQueueStage.of_frameLive (st' := finaliseThreadReleaseCores s t)
    (finaliseThreadReleaseCores_objects s t)
    (by rw [finaliseThreadReleaseCores_scheduler]) (by rw [finaliseThreadReleaseCores_scheduler])
    (fun c u hU => by
      rw [finaliseThreadReleaseCores_machine] at hU
      unfold MachineState.releaseThread at hU
      rw [MachineState.releaseThreadOnCores_residentOnCore] at hU
      split at hU
      · cases hU
      · exact Or.inl hU)
    (by rw [finaliseThreadReleaseCores_scheduler])
    (by unfold finaliseThreadReleaseCores SystemState.referenceTables; dsimp only)
    (by rw [finaliseThreadReleaseCores_scheduler])).entry

/-- A context's release of its thread is a run-queue stage. -/
theorem finaliseScReleaseStep_runQueueEntryStage (st : SystemState) :
    FinaliseScReleaseStep (SystemState.RunQueueEntryStage st) :=
  fun _ _ _ _ _ _ h _ _ _ _ hOk => h.trans (cancelBoundDonationOnCore_runQueueStage hOk).entry

/-- A reply-blocked caller's cancel with its boost reverted is a run-queue stage. -/
theorem finaliseReplyStep_runQueueEntryStage (st : SystemState) :
    FinaliseReplyStep (SystemState.RunQueueEntryStage st) :=
  fun s _ _ c t h _ _ _ _ =>
    h.trans ((cancelIpcBlockingReclaimed_runQueueStage s c t).trans
      (finaliseReplyRevert_runQueueStage _ _)).entry

/-- **The finalisation is a kernel entry's worth of run-queue steps**, every
step of it (`finaliseFinalObject_closed`): each cancel's and each unbind's
stage, a context's dequeue of its holder (`descheduleAt_runQueueStage`), a
finalised thread's suspend (`finaliseSuspend_runQueueEntryStage`), the
release of the cores' holds on it, which writes no object and no queue, a
context's reply-stack unlink (a reply and a context rewritten), a reply's
caller cancel (a head reply's with its loan returned and its holder
descheduled: `cancelIpcBlockingReclaimed_runQueueStage`) with its boost
reverted, a stashed reply's unlink (a stash
field rewritten, off the run links), and the yield steps (the yield-link
codes, a context's consumed count and a yielder's return registers). -/
theorem finaliseFinalObject_runQueueEntryStage (target : Nat) (st : SystemState) :
    SystemState.RunQueueEntryStage st (finaliseFinalObject target st) :=
  finaliseFinalObject_closed (SystemState.RunQueueEntryStage st)
    (fun e q s ep t tcb h hE hH hT hC =>
      h.trans (storeEndpointWaiterCancelled_runQueueStage s e q ep t tcb hE hH hT hC).entry)
    (fun n s _ t tcb h _ _ hT hC =>
      h.trans (notificationWaiterCancel_runQueueStage s n t tcb hT hC).entry)
    (finaliseUnbindStep_runQueueEntryStage st)
    (fun s t _ h _ _ _ _ => h.trans (descheduleAt_runQueueStage s t _).entry)
    (finaliseScReleaseStep_runQueueEntryStage st)
    (finaliseNotificationCancelStep_runQueueEntryStage st)
    (finaliseEndpointCancelStep_runQueueEntryStage st)
    (finaliseSuspendStep_runQueueEntryStage st)
    (finaliseReleaseStep_runQueueEntryStage st)
    (fun _ s1 x _ _ _ h _ _ hR _ hS _ _ _ _ =>
      h.trans ((storeObject_replyOver_runQueueStage hR hS).trans
        (updateSchedContext_runQueueStage s1 ⟨x.val⟩ _)).entry)
    (finaliseReplyStep_runQueueEntryStage st)
    (fun s _ _ tid _ h _ _ e => e ▸ h.trans
      (RunQueueStage.updateTcb s tid (f := TCB.stashCleared) (fun _ _ => rfl)).entry)
    ⟨fun s t h => h.trans (SystemState.cancelYieldTo_runQueueStage s t).entry,
     fun s c h => h.trans (SystemState.completeYieldFrom_runQueueStage s c).entry⟩
    target st ⟨SystemState.RunQueueLinkStage.refl st, fun _ _ _ d => d⟩

theorem cspaceDeleteSlotFinalising_runQueueEntryStage {ec : Concurrency.CoreId}
    {addr : CSpaceAddr} {st st' : SystemState}
    (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  exact (((((cspaceDeleteSlot_runQueueStage hD).trans
    (finaliseDestroyedCapabilities_runQueueStage hF)).trans
    (releaseFinalRegistration_runQueueStage _ st2)).entry.trans
    (finaliseFinalObject_runQueueEntryStage _ _)).trans
    (retireFinalObject_runQueueStage ec _ _ _).entry)

theorem cspaceRevokeCdtFinalising_runQueueEntryStage {ec : Concurrency.CoreId}
    {addr : CSpaceAddr} {st st' : SystemState}
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' :=
  cspaceRevokeCdtFinalising_closed (SystemState.RunQueueEntryStage st)
    (fun _ _ _ hQ hD => hQ.trans (cspaceDeleteSlotFinalising_runQueueEntryStage hD))
    (fun d s hQ => hQ.trans (finaliseFinalObject_runQueueEntryStage d s))
    ⟨SystemState.RunQueueLinkStage.refl st, fun _ _ _ d => d⟩ h

/-- `.tcbSetSpace` through the zombie delete keeps the run queues in agreement:
the loop's passes are finalising deletes and finalisations, and the plain space
change after them is a run-queue stage (`copyThreadSpaces_runQueueStage`). -/
theorem copyThreadSpacesZombie_runQueueEntryStage {ec : Concurrency.CoreId}
    {st st' : SystemState} {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr}
    (h : copyThreadSpacesZombie ec st vtid cnSrc vrSrc = .ok st') :
    SystemState.RunQueueEntryStage st st' :=
  copyThreadSpacesZombie_closed (SystemState.RunQueueEntryStage st)
    (fun _ _ _ hQ hD => hQ.trans (cspaceDeleteSlotFinalising_runQueueEntryStage hD))
    (fun d s hQ => hQ.trans (finaliseFinalObject_runQueueEntryStage d s))
    (fun _ _ hQ hS => hQ.trans (RunQueueStage.entry (copyThreadSpaces_runQueueStage hS)))
    ⟨SystemState.RunQueueLinkStage.refl st, fun _ _ _ d => d⟩ h

theorem cspaceDeleteSlotZombie_runQueueEntryStage {ec : Concurrency.CoreId}
    {addr : CSpaceAddr} {st st' : SystemState}
    (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' :=
  cspaceDeleteSlotZombie_closed (SystemState.RunQueueEntryStage st)
    (fun _ _ _ hQ hD => hQ.trans (cspaceDeleteSlotFinalising_runQueueEntryStage hD))
    (fun d s hQ => hQ.trans (finaliseFinalObject_runQueueEntryStage d s))
    ⟨SystemState.RunQueueLinkStage.refl st, fun _ _ _ d => d⟩ h

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
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hInv h
  have hFresh := retypeFromUntyped_childId_fresh src untypedId childId _ _ st st1 hRt
  obtain ⟨ut₀, ut', cap, stUt, _, stCh, cn, hUt, _, _, _, _, _, _, _, _, _, hStUt, hStCh, hOCh,
    hStIdx⟩ := retypeFromUntyped_ok_stores st st1 src untypedId childId _ _ hInv hRt
  have hNe : childId ≠ untypedId := by
    intro h; rw [h, hUt] at hFresh; simp at hFresh
  have hChildNone : stUt.objects[childId]? = none := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hInv hStUt]
    cases h : st.objects[childId]? with
    | none => rfl
    | some _ => rw [h] at hFresh; simp at hFresh
  have k1 := storeObject_inert_runQueueStage hStUt hUt (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h)
  have k2 : RunQueueStage stUt stCh := by
   cases req with
   | schedContext _ =>
    unfold storeObject at hStCh; cases hStCh
    exact RunQueueStage.insert_freshContext rfl rfl rfl hChildNone rfl
      (schedContextWellFormed_empty _) rfl rfl (by rw [hChildNone]; rfl)
      (fun c => by rw [hChildNone]; simp [SystemState.objReleaseLinkOn, SchedContext.releaseLinkOn,
        CarveRequest.object, SeLe4n.Kernel.SchedContext.empty])
   | _ =>
    exact RunQueueStage.storeObject hStCh (fun c => by rw [hChildNone]; rfl)
      (by
        rw [hChildNone]
        first
        | exact SystemState.objStateMono_nonTcb rfl rfl
        | (refine ⟨fun _ h => ?_, fun _ h _ => ?_⟩
           · cases h
           · cases h; exact .inl rfl))
      (by rw [hChildNone]; rfl)
      (fun c => by rw [hChildNone]; rfl) (by rw [hChildNone]; rfl)
  have k3 := storeObject_inert_runQueueStage hStIdx hOCh (fun _ h => KernelObject.noConfusion h) (fun _ h => KernelObject.noConfusion h)
  have kZ : RunQueueStage st1 (req.scrub st1 ut (req.carveIndex ut (retypeFreeIndex st src utCap))) :=
    RunQueueStage.of_frame (CarveRequest.scrub_objects _ _ _ _)
      (by rw [CarveRequest.scrub_scheduler]) (by rw [CarveRequest.scrub_scheduler]) (by rw [CarveRequest.scrub_scheduler])
      (by cases req <;> simp only [CarveRequest.scrub, carveZeroFrame] <;> (try split) <;> rfl)
      (by rw [CarveRequest.scrub_scheduler]) (CarveRequest.scrub_residentCode _ _ _ _)
  exact ((((k1.trans k2).trans k3).trans kZ).trans (cspaceInsertSlot_runQueueStage hIns)).trans
    (cdtRecord_runQueueStage _ _ _ _)

end SeLe4n.Kernel
