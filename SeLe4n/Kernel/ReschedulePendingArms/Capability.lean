-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.Scheduler.Invariant.ReschedulePendingCoverage

/-!
# The capability arms cover

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md`, PR B2.  The CSpace, VSpace,
untyped and service arms write no scheduler state and no key input: their object
writes land on CNodes, VSpace roots, frames, page tables and untyped objects,
which feed no thread's key, and the one TCB rewrite among them (the revocation's
in-flight sweep) changes a pending message only.  So each covers by frame
(`stepCovers_of_scheduler_eq`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-! ### Writes no key reads -/

/-- A slot whose object feeds no key on either side. -/
theorem keyInputsEq_of_single_inert_write {st st' : SystemState} {k : SeLe4n.ObjId}
    (hNe : ∀ oid, oid ≠ k → st'.objects[oid]? = st.objects[oid]?)
    (hPre : keyInputsOf st.objects[k]? = none) (hPost : keyInputsOf st'.objects[k]? = none) :
    keyInputsEq st st' := by
  intro oid
  by_cases h : oid = k
  · subst h; rw [hPre, hPost]
  · rw [hNe oid h]

/-- A write of VSpace roots alone feeds no key. -/
theorem keyInputsEq_of_vspaceRootOnlyWrite {st st' : SystemState}
    (h : vspaceRootOnlyWrite st st') : keyInputsEq st st' := by
  intro oid
  rcases h oid with e | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
  · rw [e]
  · rw [hr, hr']; rfl

/-- A store of a CNode over a CNode feeds no key. -/
theorem keyInputsEq_storeObject_cnode {st st' : SystemState} {oid : SeLe4n.ObjId}
    {cn cn' : CNode} (hObjInv : st.objects.invExt)
    (hPre : st.objects[oid]? = some (.cnode cn))
    (hStore : storeObject oid (.cnode cn') st = .ok ((), st')) :
    keyInputsEq st st' :=
  keyInputsEq_storeObject hObjInv hStore (by rw [hPre]; rfl)

/-! ### CSpace primitives -/

theorem cspaceInsertSlot_keyInputsEq (st st' : SystemState) (addr : CSpaceAddr)
    (cap : Capability) (hObjInv : st.objects.invExt)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) : keyInputsEq st st' := by
  obtain ⟨cn, hPre, hAt⟩ := cspaceInsertSlot_objects_eq st st' addr cap hObjInv hStep
  exact keyInputsEq_of_single_inert_write
    (fun oid h => cspaceInsertSlot_preserves_objects_ne st st' addr cap oid h hObjInv hStep)
    (by rw [hPre]; rfl) (by rw [hAt]; rfl)

theorem cspaceDeleteSlotCore_keyInputsEq (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    keyInputsEq st st' ∧ st'.scheduler = st.scheduler ∧ st'.objects.invExt := by
  obtain ⟨o, hO, hH, hS⟩ := cspaceDeleteSlotCore_ok hStep
  refine ⟨keyInputsEq_storeObject hObjInv hS ?_, storeObject_scheduler_eq st st' _ _ hS,
    storeObject_preserves_objects_invExt st st' _ _ hObjInv hS⟩
  rw [hO]
  cases o <;> simp_all [keyInputsOf, KernelObject.removeSlotCap, TCB.removeSpaceCap,
    KernelObject.holdsSlots]

/-- What every capability arm establishes: no key input, no scheduler field and
no store invariant moved. -/
def capabilityKeyFrame (st st' : SystemState) : Prop :=
  keyInputsEq st st' ∧ st'.scheduler = st.scheduler ∧ st'.objects.invExt

theorem capabilityKeyFrame.trans {a b d : SystemState} (h₁ : capabilityKeyFrame a b)
    (h₂ : capabilityKeyFrame b d) : capabilityKeyFrame a d :=
  ⟨keyInputsEq_trans h₁.1 h₂.1, h₂.2.1.trans h₁.2.1, h₂.2.2⟩

theorem capabilityKeyFrame_of_objects_scheduler_eq {st st' : SystemState}
    (hObjInv : st.objects.invExt) (hObj : st'.objects = st.objects)
    (hSched : st'.scheduler = st.scheduler) : capabilityKeyFrame st st' :=
  ⟨keyInputsEq_of_objects_eq hObj, hSched, hObj ▸ hObjInv⟩

/-- Slot-link writes change only CNodes, which feed no key, and threads' slot
links, which no key reads. -/
theorem capabilityKeyFrame_of_linkReach {st₀ st : SystemState}
    (hR : SystemState.linkReach st₀ st) (hObjInv : st₀.objects.invExt) :
    capabilityKeyFrame st₀ st := by
  refine ⟨fun oid => ?_, ?_, hR.invExt hObjInv⟩
  · rcases hR.agree hObjInv oid with e | ⟨_, _, ha, hb, _⟩ | ⟨t, t', ha, hb, hw⟩
    · rw [e]
    · rw [ha, hb]; rfl
    · rw [ha, hb]
      exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => keyInputsOf (some (.tcb x))) hw
  · have h := congrArg SystemState.scheduler hR.fields; exact h

/-- A tree write followed by its slot-link writes feeds no key. -/
theorem capabilityKeyFrame_of_withCdt_linkReach {st st' : SystemState} {c : CapDerivationTree}
    (hR : SystemState.linkReach { st with cdt := c } st') (hObjInv : st.objects.invExt) :
    capabilityKeyFrame st st' :=
  (capabilityKeyFrame_of_objects_scheduler_eq (st' := { st with cdt := c }) hObjInv rfl rfl).trans
    (capabilityKeyFrame_of_linkReach hR hObjInv)

/-- The derivation edge every `WithCdt` form ends with, tree and slot links
together, writes no key input and no scheduler state. -/
theorem cdtRecord_keyFrame (stM : SystemState) (src dst : CSpaceAddr)
    (kind : DerivationOp) (hObjInv : stM.objects.invExt) :
    capabilityKeyFrame stM (stM.cdtAddChild src dst kind) :=
  capabilityKeyFrame_of_withCdt_linkReach (SystemState.cdtAddChild_reach stM src dst kind) hObjInv

theorem capabilityKeyFrame.stepCovers {e : CoreId} {st st' : SystemState}
    (h : capabilityKeyFrame st st')
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame)
    (hBank : banksKeptOffCore e st st' := by bank_kept) :
    stepCovers e st st' :=
  stepCovers_of_scheduler_eq h.1 h.2.1 hRes hBank

theorem cspaceDeleteSlot_keyInputsEq (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    keyInputsEq st st' ∧ st'.scheduler = st.scheduler ∧ st'.objects.invExt := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' hStep
  have hC : capabilityKeyFrame st stC := cspaceDeleteSlotCore_keyInputsEq st stC addr hObjInv hCore
  exact hC.trans (capabilityKeyFrame_of_withCdt_linkReach
    (spliceDeletedCdtNode_reach stC addr) hC.2.2)

theorem cspaceInsertSlot_keyFrame (st st' : SystemState) (addr : CSpaceAddr)
    (cap : Capability) (hObjInv : st.objects.invExt)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) : capabilityKeyFrame st st' :=
  ⟨cspaceInsertSlot_keyInputsEq st st' addr cap hObjInv hStep,
   cspaceInsertSlot_preserves_scheduler st st' addr cap hStep,
   cspaceInsertSlot_preserves_objects_invExt st st' addr cap hObjInv hStep⟩

theorem cspaceMint_keyFrame (st st' : SystemState) (src dst : CSpaceAddr)
    (rights : AccessRightSet) (badge : Option SeLe4n.Badge) (hObjInv : st.objects.invExt)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  unfold cspaceMint at hStep
  split at hStep
  · contradiction
  · rename_i parent stMid hLk
    have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src parent hLk
    subst hMid
    split at hStep
    · contradiction
    · split at hStep
      · contradiction
      · exact cspaceInsertSlot_keyFrame _ st' dst _ hObjInv hStep

/-- WS-ZA ZA5.4: a free-index write stores a CNode, which feeds no key, or
writes nothing. -/
theorem setCapFreeIndex_keyFrame (st : SystemState) (addr : CSpaceAddr) (idx : Nat)
    (hObjInv : st.objects.invExt) : capabilityKeyFrame st (setCapFreeIndex st addr idx) := by
  cases hO : st.objects[addr.cnode]? with
  | some o =>
    cases o with
    | cnode cn =>
      have hS := setCapFreeIndex_eq_storeObject (idx := idx) hO
      exact ⟨keyInputsEq_storeObject hObjInv hS (by rw [hO]; rfl),
        storeObject_scheduler_eq _ _ _ _ hS, storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS⟩
    | _ =>
      unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO]
      exact capabilityKeyFrame_of_objects_scheduler_eq hObjInv rfl rfl
  | none =>
    unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO]
    exact capabilityKeyFrame_of_objects_scheduler_eq hObjInv rfl rfl

theorem untypedSourceSetFull_keyFrame (st : SystemState) (src : CSpaceAddr) (cap : Capability)
    (hObjInv : st.objects.invExt) : capabilityKeyFrame st (untypedSourceSetFull st src cap) :=
  untypedSourceSetFull_of (P := capabilityKeyFrame st)
    (capabilityKeyFrame_of_objects_scheduler_eq hObjInv rfl rfl)
    fun idx => setCapFreeIndex_keyFrame st src idx hObjInv

theorem cspaceMintWithCdt_keyFrame (st st' : SystemState) (src dst : CSpaceAddr)
    (rights : AccessRightSet) (badge : Option SeLe4n.Badge) (hObjInv : st.objects.invExt)
    (hStep : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  obtain ⟨_, stM, hMint, -, -, rfl⟩ := cspaceMintWithCdt_ok_decompose hStep
  have hM := cspaceMint_keyFrame st stM src dst rights badge hObjInv hMint
  have hC := hM.trans (cdtRecord_keyFrame stM src dst .mint hM.2.2)
  exact hC.trans (untypedSourceSetFull_keyFrame _ src _ hC.2.2)

theorem cspaceCopy_keyFrame (st st' : SystemState) (src dst : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hStep : cspaceCopy src dst st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  obtain ⟨_, st2, -, -, hIns, -, rfl⟩ := cspaceCopy_ok_decompose hStep
  have hI := cspaceInsertSlot_keyFrame _ st2 dst _ hObjInv hIns
  have hC := hI.trans (cdtRecord_keyFrame st2 src dst .copy hI.2.2)
  exact hC.trans (untypedSourceSetFull_keyFrame _ src _ hC.2.2)

theorem cspaceMove_keyFrame (st st' : SystemState) (src dst : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hStep : cspaceMove src dst st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  unfold cspaceMove at hStep
  split at hStep
  · contradiction
  · split at hStep
    · contradiction
    · rename_i cap stMid hLk
      have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src cap hLk
      subst hMid
      split at hStep
      · contradiction
      · split at hStep
        · contradiction
        · rename_i st2 hIns
          have hI := cspaceInsertSlot_keyFrame _ st2 dst _ hObjInv hIns
          split at hStep
          · contradiction
          · rename_i st3 hDel
            have hD := cspaceDeleteSlotCore_keyInputsEq st2 st3 src hI.2.2 hDel
            have h3 := hI.trans hD
            cases hStep
            exact h3.trans (capabilityKeyFrame_of_withCdt_linkReach
              (SystemState.cdtMove_reach st3 src dst) hD.2.2)

theorem mintReplyCapWithCdt_keyFrame (st st' : SystemState) (src dst : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hStep : mintReplyCapWithCdt src dst st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  unfold mintReplyCapWithCdt at hStep
  split at hStep
  · contradiction
  · rename_i stM hMint
    cases hStep
    have hM : capabilityKeyFrame st stM := by
      unfold mintReplyCap at hMint
      split at hMint
      · contradiction
      · rename_i parent stMid hLk
        have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src parent hLk
        subst hMid
        split at hMint
        · dsimp only [] at hMint
          split at hMint
          · exact cspaceInsertSlot_keyFrame _ stM dst _ hObjInv hMint
          · contradiction
        · contradiction
    exact hM.trans (cdtRecord_keyFrame stM src dst .mint hM.2.2)

/-! ### Teardown of destroyed capabilities -/

theorem finaliseDestroyedCapabilities_keyFrame (ec : CoreId) (named : List SeLe4n.ObjId)
    (pages : List MappedPage) (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  obtain ⟨hExt, hW, hSched, -⟩ :=
    finaliseDestroyedCapabilities_ok_frame ec named pages st st' hObjInv hStep
  exact ⟨keyInputsEq_of_vspaceRootOnlyWrite hW, hSched, hExt⟩

/-- **A write of the kinds a retire touches moves no key input**: none of those
kinds feeds a key (`retireTouched`).  The final-delete retire is such a
write. -/
theorem capabilityKeyFrame_of_retireTouched {st st' : SystemState}
    (hExt : st'.objects.invExt) (hSched : st'.scheduler = st.scheduler)
    (hW : ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
      (retireTouched st.objects[oid]? ∧ retireTouched st'.objects[oid]?)) :
    capabilityKeyFrame st st' := by
  have hT : ∀ o : Option KernelObject, retireTouched o → keyInputsOf o = none := by
    intro o h
    cases o with
    | none => rfl
    | some obj => cases obj <;> first | rfl | exact absurd h (by simp [retireTouched])
  refine ⟨fun oid => ?_, hSched, hExt⟩
  rcases hW oid with e | ⟨t1, t2⟩
  · rw [e]
  · rw [hT _ t1, hT _ t2]

/-! ### VSpace and untyped -/

/-- A store whose slot feeds no key on either side. -/
theorem storeObject_inert_keyFrame {st st' : SystemState} {oid : SeLe4n.ObjId}
    {obj : KernelObject} (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hPre : keyInputsOf st.objects[oid]? = none) (hObj : keyInputsOf (some obj) = none) :
    capabilityKeyFrame st st' :=
  ⟨keyInputsEq_storeObject hObjInv hStore (hObj.trans hPre.symm),
   storeObject_scheduler_eq _ _ _ _ hStore,
   storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStore⟩

theorem vspaceRootOnlyWrite_keyFrame {st st' : SystemState}
    (h : st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler ∧
      st'.referenceTables = st.referenceTables) :
    capabilityKeyFrame st st' :=
  ⟨keyInputsEq_of_vspaceRootOnlyWrite h.2.1, h.2.2.1, h.1⟩

theorem tagFrameMapping_keyFrame (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (frameId : SeLe4n.ObjId) (st st' : SystemState) (e : Nat) (hObjInv : st.objects.invExt)
    (hStep : tagFrameMapping asid vaddr frameId st = .ok (e, st')) :
    capabilityKeyFrame st st' := by
  obtain ⟨f, rootId, root, st1, hF, hR, -, h1, h2⟩ :=
    tagFrameMapping_ok asid vaddr frameId st st' e hStep
  have hRootPre := (Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hR).2.1
  have hFramePre := (SystemState.getFrame?_eq_some_iff st frameId f).mp hF
  have k1 := storeObject_inert_keyFrame hObjInv h1 (by rw [hRootPre]; rfl) rfl
  have hNe : frameId ≠ rootId := by
    intro hEq; rw [hEq, hRootPre] at hFramePre; cases hFramePre
  have hFrame1 : st1.objects[frameId]? = some (.frame f) := by
    rw [storeObject_objects_ne st st1 _ _ _ hNe hObjInv h1]; exact hFramePre
  exact k1.trans (storeObject_inert_keyFrame k1.2.2 h2 (by rw [hFrame1]; rfl) rfl)

theorem cspaceRecordFrameMapping_keyFrame (addr : CSpaceAddr) (m : FrameMapping)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : cspaceRecordFrameMapping addr m st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  obtain ⟨cn, cap, hCn, -, hStore⟩ := cspaceRecordFrameMapping_ok_decompose addr m st st' hStep
  have hPre : st.objects[addr.cnode]? = some (.cnode cn) :=
    (SystemState.getCNode?_eq_some_iff st addr.cnode cn).mp hCn
  exact storeObject_inert_keyFrame hObjInv hStore (by rw [hPre]; rfl) rfl

theorem vspaceMapFromFrameCap_keyFrame (tid : SeLe4n.ThreadId) (ec : CoreId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs) (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : vspaceMapFromFrameCap tid ec args st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  obtain ⟨_, _, _, st1, _, _, _, _, _, hMap, epoch, st2, hT, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid ec args st st' hStep
  have k1 := vspaceRootOnlyWrite_keyFrame
    (vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame _ _ _ _ _ st st1 hObjInv hMap)
  have k2 := tagFrameMapping_keyFrame _ _ _ st1 st2 epoch k1.2.2 hT
  exact (k1.trans k2).trans (cspaceRecordFrameMapping_keyFrame _ _ st2 st' k2.2.2 hRec)

/-- **The carve's key frame** (WS-ZA ZA5.4 part 14): the carve moves no key input
off the child's slot, which was empty before it; whatever it stores there — a
fresh TCB or scheduling context carries key inputs of its own — is queued on no
core; and it leaves the scheduler and the store invariant alone.  The dispatch
turns this into the coverage (`untypedRetypeObject_stepCovers`). -/
theorem untypedRetypeObject_keyFrameOffChild (src dst : CSpaceAddr) (childId : SeLe4n.ObjId)
    (req : CarveRequest) (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    (∀ oid, oid ≠ childId → keyInputsOf st'.objects[oid]? = keyInputsOf st.objects[oid]?) ∧
    st.objects[childId]? = none ∧
    (∀ c (t : SeLe4n.ThreadId), t.toObjId = childId → st'.queuedOn c t = false) ∧
    st'.scheduler = st.scheduler ∧ st'.objects.invExt := by
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hObjInv hStep
  have hFresh := retypeFromUntyped_childId_fresh src untypedId childId _ _ st st1 hRt
  obtain ⟨ut₀, ut', cap, stUt, _, stCh, cn, hUt, _, _, _, _, _, _, _, _, _, hStUt, hStCh, hOCh,
    hStIdx⟩ := retypeFromUntyped_ok_stores st st1 src untypedId childId _ _ hObjInv hRt
  have k1 := storeObject_inert_keyFrame hObjInv hStUt (by rw [hUt]; rfl) rfl
  have hNe : childId ≠ untypedId := by
    intro h; rw [h, hUt] at hFresh; simp at hFresh
  have hAbs : st.objects[childId]? = none := by
    cases h : st.objects[childId]? with
    | none => rfl
    | some _ => rw [h] at hFresh; simp at hFresh
  have hInvCh : stCh.objects.invExt := storeObject_preserves_objects_invExt _ _ _ _ k1.2.2 hStCh
  have k3 := storeObject_inert_keyFrame hInvCh hStIdx (by rw [hOCh]; rfl) rfl
  have kZ : capabilityKeyFrame st1 (req.scrub st1 ut (req.carveIndex ut (retypeFreeIndex st src utCap))) :=
    capabilityKeyFrame_of_objects_scheduler_eq k3.2.2 (CarveRequest.scrub_objects _ _ _ _)
      (CarveRequest.scrub_scheduler _ _ _ _)
  have kI := cspaceInsertSlot_keyFrame _ st2 dst _ kZ.2.2 hIns
  have kR := ((k3.trans kZ).trans kI).trans (cdtRecord_keyFrame st2 src dst .retype kI.2.2)
  refine ⟨fun oid hne => ?_, hAbs, fun c t ht => ?_, ?_, kR.2.2⟩
  · rw [kR.1 oid, storeObject_objects_ne _ _ _ _ _ hne k1.2.2 hStCh]; exact k1.1 oid
  · rw [kR.1.runCoresAgree.queuedOn c t]
    unfold SystemState.queuedOn SystemState.getTcb?
    rw [ht, storeObject_objects_eq _ _ _ _ k1.2.2 hStCh]
    cases req <;> simp [CarveRequest.object, carvedTcb]
  · rw [kR.2.1, storeObject_scheduler_eq _ _ _ _ hStCh, k1.2.1]

/-- WS-ZA ZA5.4: the `.untypedReset` arm — the invoked slot's free-index rewind,
a CNode store, which feeds no key, and nothing else. -/
theorem untypedResetFromCap_keyFrame (tid : SeLe4n.ThreadId) (srcAddr : SeLe4n.CPtr)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : untypedResetFromCap tid srcAddr st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  obtain ⟨_, _, _, -, -, hS⟩ := untypedResetFromCap_ok _ _ st st' hStep
  rw [untypedResetSlot_ok_frame hS]
  exact setCapFreeIndex_keyFrame _ _ _ hObjInv

/-! ### One-field TCB rewrites and registry writes -/

/-- A store of a TCB over a TCB with the same four key fields. -/
theorem storeObject_tcbKeyKeeping_keyFrame {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {tcb tcb' : TCB} (hObjInv : st.objects.invExt)
    (hPre : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hStore : storeObject tid.toObjId (.tcb tcb') st = .ok ((), st'))
    (hKey : tcbKeyFields tcb' = tcbKeyFields tcb)
    (hRun : tcb'.runCoreCode = tcb.runCoreCode := by rfl) : capabilityKeyFrame st st' := by
  refine ⟨keyInputsEq_storeObject hObjInv hStore ?_, storeObject_scheduler_eq _ _ _ _ hStore,
    storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStore⟩
  rw [hPre]
  simp only [tcbKeyFields, Prod.mk.injEq] at hKey
  simp only [keyInputsOf, hKey, hRun]

/-- The raw-insert form of the same rewrite. -/
theorem insertObjects_tcbKeyKeeping_keyFrame {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb tcb' : TCB} (hObjInv : st.objects.invExt)
    (hPre : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hKey : tcbKeyFields tcb' = tcbKeyFields tcb)
    (hRun : tcb'.runCoreCode = tcb.runCoreCode := by rfl) :
    capabilityKeyFrame st { st with objects := st.objects.insert tid.toObjId (.tcb tcb') } := by
  refine ⟨fun oid => ?_, rfl, objects_insert_invExt hObjInv _ _⟩
  by_cases h : oid = tid.toObjId
  · subst h
    rw [insertObjects_getElem_self st _ _ hObjInv, hPre]
    simp only [tcbKeyFields, Prod.mk.injEq] at hKey
    simp only [keyInputsOf, hKey, hRun]
  · rw [insertObjects_getElem_ne st _ _ _ h hObjInv]

theorem writeReturnFrameToTcb_keyFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Architecture.SyscallReturnFrame) (hObjInv : st.objects.invExt) :
    capabilityKeyFrame st (Architecture.writeReturnFrameToTcb st tid frame) :=
  ⟨keyInputsEq_updateTcb hObjInv (fun _ => rfl),
   Architecture.writeReturnFrameToTcb_scheduler_eq st tid frame,
   writeReturnFrameToTcb_preserves_objects_invExt st tid frame hObjInv⟩

theorem writeDeliveredFrameToTcb_keyFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Architecture.SyscallReturnFrame) (hObjInv : st.objects.invExt) :
    capabilityKeyFrame st (Architecture.writeDeliveredFrameToTcb st tid frame) :=
  ⟨keyInputsEq_updateTcb hObjInv (fun _ => rfl),
   Architecture.writeDeliveredFrameToTcb_scheduler_eq st tid frame,
   writeDeliveredFrameToTcb_preserves_objects_invExt st tid frame hObjInv⟩

theorem setIPCBufferOp_keyFrame (st st' : SystemState) (vtid : SeLe4n.ValidThreadId)
    (addr : SeLe4n.VAddr) (hObjInv : st.objects.invExt)
    (hStep : Architecture.IpcBufferValidation.setIPCBufferOp st vtid addr = .ok st') :
    capabilityKeyFrame st st' := by
  unfold Architecture.IpcBufferValidation.setIPCBufferOp at hStep
  split at hStep
  · contradiction
  · split at hStep
    · rename_i tcb hTcb
      dsimp only [] at hStep
      split at hStep
      · rename_i hStore
        cases hStep
        exact storeObject_tcbKeyKeeping_keyFrame hObjInv
          ((SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hTcb) hStore rfl
      · contradiction
    · contradiction

theorem setThreadFaultHandlerOp_keyFrame (st st' : SystemState) (vtid : SeLe4n.ValidThreadId)
    (cptr : SeLe4n.CPtr) (hObjInv : st.objects.invExt)
    (hStep : setThreadFaultHandlerOp st vtid cptr = .ok st') : capabilityKeyFrame st st' := by
  cases hT : st.getTcb? vtid.val with
  | none => simp [setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_none hT] at hStep
  | some tcb =>
      cases hR : resolveFaultHandlerCPtr st tcb cptr with
      | error e =>
          simp [setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_some hT, hR] at hStep
      | ok tgt =>
          rw [setThreadFaultHandlerOp_ok_eq st vtid cptr tcb tgt hT hR] at hStep
          cases hStep
          unfold installFaultHandler SystemState.rewriteObject
          exact insertObjects_tcbKeyKeeping_keyFrame hObjInv
            ((SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hT) rfl

theorem threadSlotCopied_keyFrame {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    capabilityKeyFrame st (threadSlotCopied st tid slot srcCNode srcSlot rights) := by
  have hD : capabilityKeyFrame st _ :=
    cspaceDeleteSlot_keyInputsEq st _ _ hObjInv (copyIntoThreadSlot_delete hT slot)
  obtain ⟨⟨t', hT', -⟩, hI⟩ := threadSlotDeleted_tcb hObjInv hT slot
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights with ⟨-, e⟩ | ⟨cap, -, e⟩
  · rw [e]; exact hD
  · rw [e]
    have hU : capabilityKeyFrame
        (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
          { cnode := tid.toObjId, slot := slot })
        (SystemState.updateTcb (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
          { cnode := tid.toObjId, slot := slot }) tid
          (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights))) := by
      rw [SystemState.updateTcb_eq_of_some hT']
      exact insertObjects_tcbKeyKeeping_keyFrame hI
        ((SystemState.getTcb?_eq_some_iff _ tid t').mp hT') rfl
    exact (hD.trans hU).trans (cdtRecord_keyFrame _ _ _ _ hU.2.2)

theorem bindNotification_keyFrame (st st' : SystemState) (nid : SeLe4n.ObjId)
    (tcbId : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hStep : bindNotification nid tcbId st = .ok ((), st')) : capabilityKeyFrame st st' := by
  unfold bindNotification at hStep
  split at hStep
  · rename_i ntfn hN
    split at hStep
    · contradiction
    · rename_i tcb hT
      split at hStep
      · contradiction
      · split at hStep
        · contradiction
        · rename_i hStore1
          split at hStep
          · contradiction
          · rename_i hStore2
            cases hStep
            have hNraw := (SystemState.getNotification?_eq_some_iff st nid ntfn).mp hN
            have hTraw := lookupTcb_some_objects st tcbId tcb hT
            have hNeIds : tcbId.toObjId ≠ nid := by
              intro hEq
              rw [hEq, hNraw] at hTraw
              exact absurd (Option.some.inj hTraw) (fun hx => KernelObject.noConfusion hx)
            have k1 := storeObject_inert_keyFrame hObjInv hStore1 (by rw [hNraw]; rfl) rfl
            have hPre1 := storeObject_objects_ne st _ nid tcbId.toObjId _ hNeIds hObjInv hStore1
            exact k1.trans (storeObject_tcbKeyKeeping_keyFrame k1.2.2 (hPre1.trans hTraw)
              hStore2 rfl)
  · split at hStep <;> contradiction

theorem unbindNotification_keyFrame (st st' : SystemState) (tcbId : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : unbindNotification tcbId st = .ok ((), st')) : capabilityKeyFrame st st' := by
  unfold unbindNotification at hStep
  split at hStep
  · contradiction
  · rename_i tcb hT
    split at hStep
    · contradiction
    · rename_i nid hBound
      split at hStep
      · contradiction
      · rename_i hStore1
        have hTraw := lookupTcb_some_objects st tcbId tcb hT
        have k1 := storeObject_tcbKeyKeeping_keyFrame hObjInv hTraw hStore1 rfl
        split at hStep
        · rename_i ntfn hN1
          split at hStep
          · contradiction
          · rename_i hStore2
            cases hStep
            exact k1.trans (storeObject_inert_keyFrame k1.2.2 hStore2
              (by rw [(SystemState.getNotification?_eq_some_iff _ nid ntfn).mp hN1]; rfl) rfl)
        · cases hStep
          exact k1

theorem recordPhysicalWrites_keyFrame {st : SystemState} (hObjInv : st.objects.invExt)
    (ws : List Architecture.PhysicalWrite) :
    capabilityKeyFrame st (Architecture.recordPhysicalWrites st ws) :=
  capabilityKeyFrame_of_objects_scheduler_eq hObjInv
    (Architecture.recordPhysicalWrites_objects _ _)
    (Architecture.recordPhysicalWrites_scheduler _ _)

theorem pageTableMap_keyFrame (tableId rootId : SeLe4n.ObjId) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : Architecture.pageTableMap tableId rootId vaddr st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  obtain ⟨table, root, level, st1, hT, hR, -, -, -, -, hS1, hS2⟩ :=
    Architecture.pageTableMap_ok tableId rootId vaddr st st' hStep
  have hT' := (SystemState.getPageTable?_eq_some_iff st tableId table).mp hT
  have hR' := (SystemState.getVSpaceRoot?_eq_some_iff st rootId root).mp hR
  have k1 := storeObject_inert_keyFrame hObjInv hS1 (by rw [hT']; rfl) rfl
  have hNe : rootId ≠ tableId := by
    intro hEq; subst hEq; rw [hT'] at hR'; cases hR'
  have hR1 : st1.objects[rootId]? = some (.vspaceRoot root) := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hObjInv hS1]; exact hR'
  exact (k1.trans (recordPhysicalWrites_keyFrame k1.2.2 _)).trans
    (storeObject_inert_keyFrame (recordPhysicalWrites_keyFrame k1.2.2 _).2.2 hS2
    (by simp only [Architecture.recordPhysicalWrites_objects, hR1]; rfl) rfl)

theorem pageTableUnmap_keyFrame (tableId : SeLe4n.ObjId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : Architecture.pageTableUnmap tableId st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  unfold Architecture.pageTableUnmap at hStep
  cases hT : st.getPageTable? tableId with
  | none => rw [hT] at hStep; cases hStep
  | some table =>
    rw [hT] at hStep
    have hT' := (SystemState.getPageTable?_eq_some_iff st tableId table).mp hT
    simp only at hStep
    cases hI : table.installedIn with
    | none =>
      rw [hI] at hStep; cases hStep
      exact capabilityKeyFrame_of_objects_scheduler_eq hObjInv rfl rfl
    | some inst =>
      rw [hI] at hStep
      simp only at hStep
      cases hR : st.getVSpaceRoot? inst.root with
      | none =>
        rw [hR] at hStep
        exact storeObject_inert_keyFrame hObjInv hStep (by rw [hT']; rfl) rfl
      | some root =>
        rw [hR] at hStep
        have hR' := (SystemState.getVSpaceRoot?_eq_some_iff st inst.root root).mp hR
        simp only at hStep
        split at hStep
        · split at hStep
          · cases hStep
          · cases hS1 : storeObject tableId _ st with
            | error e => rw [hS1] at hStep; cases hStep
            | ok p =>
              obtain ⟨⟨⟩, st1⟩ := p
              rw [hS1] at hStep
              have k1 := storeObject_inert_keyFrame hObjInv hS1 (by rw [hT']; rfl) rfl
              have hNe : inst.root ≠ tableId := by
                intro hEq; rw [hEq, hT'] at hR'; cases hR'
              have hR1 : st1.objects[inst.root]? = some (.vspaceRoot root) := by
                rw [storeObject_objects_ne _ _ _ _ _ hNe hObjInv hS1]; exact hR'
              exact (k1.trans (recordPhysicalWrites_keyFrame k1.2.2 _)).trans
                (storeObject_inert_keyFrame (recordPhysicalWrites_keyFrame k1.2.2 _).2.2 hStep
                (by simp only [Architecture.recordPhysicalWrites_objects, hR1]; rfl) rfl)
        · exact storeObject_inert_keyFrame hObjInv hStep (by rw [hT']; rfl) rfl


end SeLe4n.Kernel
