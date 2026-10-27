-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.MappingRecords
import SeLe4n.Kernel.Capability.Invariant.Preservation.Revoke

/-! # The final delete keeps every live mapping recorded

The finalising delete destroys one capability, and with it the record that
capability held (`Capability.mapping`).  It also unmaps the page that record
names (`cspaceDeleteSlotFinalising_ok_unmapped`), so the mapping the record
witnessed is gone with it: a mapping still live afterwards was witnessed by a
capability in another slot, which the delete keeps.  The retire then erases the
object the destroyed capability was final to; a frame witnessing a live mapping
is named by that other slot too, so it is not that object.

So the delete keeps `SystemState.liveMappingsRecorded` on a state whose
capability invariants and teardown well-formedness hold
(`cspaceDeleteSlotFinalising_preserves_liveMappingsRecorded`), and so do the
revocation and the zombie delete, chains of such deletes.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- A frame is no object a finalisation writes. -/
theorem not_finaliseWritableAny_frame (f : FrameObject) :
    ¬ finaliseWritableAny (.frame f) := by
  simp [finaliseWritableAny, finaliseWritable, KernelObject.objectType]

/-- **The roots' mapping half of `vspaceRootsShrink`.** -/
theorem vspaceRootsShrink.mappingRoots {st st' : SystemState} (h : vspaceRootsShrink st st') :
    SystemState.mappingRootsShrink st st' := fun rid r' hR => by
  obtain ⟨r, hr, ha, hm, he, -⟩ := h rid r' hR
  exact ⟨r, hr, ha, hm, he⟩

/-- **The finalisation keeps the mappings recorded**: it keeps every root, every
frame and every slot's capability (`FinaliseFrameAny`). -/
theorem FinaliseFrameAny.liveMappingsRecorded {st st' : SystemState} (h : FinaliseFrameAny st st')
    (hL : st.liveMappingsRecorded) : st'.liveMappingsRecorded :=
  SystemState.liveMappingsRecorded.of_shrink
    (fun rid r' hR => ⟨r', (h.write.roots_iff rid r').1 hR, rfl, fun _ _ hm => hm, fun _ _ he => he⟩)
    (SystemState.mappingRecordsKept.of_fwd
      (fun r cap hc _ => ⟨r, cap, (h.slotCapAt r).trans hc, rfl, rfl⟩)
      (fun _ f hf => ⟨f, h.write.keeps hf (not_finaliseWritableAny_frame f), rfl⟩))
    hL

theorem finaliseFinalObject_preserves_liveMappingsRecorded (target : Nat) (st : SystemState)
    (hInv : st.objects.invExt) (hL : st.liveMappingsRecorded) :
    (finaliseFinalObject target st).liveMappingsRecorded :=
  (finaliseFinalObject_frame target st hInv).liveMappingsRecorded hL

/-- **The delete keeps every frame**: it writes a CNode or a thread where one
stands, then derivation links. -/
theorem cspaceDeleteSlot_keeps_frame {addr : CSpaceAddr} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (h : cspaceDeleteSlot addr st = .ok ((), st'))
    {fid : SeLe4n.ObjId} {f : FrameObject} (hf : st.objects[fid]? = some (.frame f)) :
    st'.objects[fid]? = some (.frame f) := by
  obtain ⟨stC, hC, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' h
  obtain ⟨o, hO, hH, hS⟩ := cspaceDeleteSlotCore_ok hC
  have hfC : stC.objects[fid]? = some (.frame f) := by
    by_cases hK : fid = addr.cnode
    · subst hK; rw [hO] at hf; cases hf; simp [KernelObject.holdsSlots] at hH
    · rwa [storeObject_objects_ne st _ _ fid _ hK hObjInv hS]
  have hInvC := storeObject_preserves_objects_invExt st _ _ _ hObjInv hS
  rcases (spliceDeletedCdtNode_reach stC addr).agree hInvC fid with
    hE | ⟨cn, cn', h1, h2, -⟩ | ⟨t, t', h1, h2, -⟩
  · rw [hE]; exact hfC
  all_goals first | (rw [h1] at hfC; cases hfC) | (rw [h2] at hfC; cases hfC)

/-- **The teardown keeps every frame**: it writes roots only. -/
theorem vspaceRootOnlyWrite.keeps_frame {st st' : SystemState} (h : vspaceRootOnlyWrite st st')
    {fid : SeLe4n.ObjId} {f : FrameObject} (hf : st.objects[fid]? = some (.frame f)) :
    st'.objects[fid]? = some (.frame f) := by
  rcases h fid with e | ⟨⟨r, hr⟩, -⟩
  · rw [e]; exact hf
  · rw [hf] at hr; cases hr

/-- **The retire keeps every frame but its target.** -/
theorem retireFinalObject_keeps_frame (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {fid : SeLe4n.ObjId} {f : FrameObject}
    (hf : st.objects[fid]? = some (.frame f)) :
    (retireFinalObject ec target recorder st).objects[fid]? = some (.frame f) ∨
      (target ≠ 0 ∧ fid = SeLe4n.ObjId.ofNat (target - 1)) := by
  by_cases h0 : target = 0
  · subst h0; rw [retireFinalObject_zero]; exact .inl hf
  rcases (retireFinalObject_frame ec target recorder st hInv).2.2.2.2 fid with
    e | ⟨hx, -, -⟩ | ⟨U, U', -, hU, -⟩
  · rw [e]; exact .inl hf
  · exact .inr ⟨h0, hx⟩
  · rw [hf] at hU; cases hU

/-- **The finalising delete keeps every live mapping recorded.**  A mapping
live after the delete was live before it (the delete only shrinks roots), so a
slot recorded it.  That slot is not the one deleted: the delete unmapped the
page the deleted capability recorded (`cspaceDeleteSlotFinalising_ok_unmapped`),
and on the well-formed post-state the mapping's own root is the one its ASID
resolves to, where the mapping is still live.  So the recording slot keeps its
capability, and the frame it names is kept: the retire erases only the object
the deleted capability was final to, which no other slot names
(`slotRetireTarget_spec`). -/
theorem cspaceDeleteSlotFinalising_preserves_liveMappingsRecorded (ec : Concurrency.CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (hInv : capabilityInvariantBundle st)
    (hW : teardownWellFormed st) (hL : st.liveMappingsRecorded)
    (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    st'.liveMappingsRecorded := by
  have hW' := cspaceDeleteSlotFinalising_preserves_teardownWellFormed ec hW h
  have hS := cspaceDeleteSlotFinalising_shrinks ec hW h
  have hUnmapped := cspaceDeleteSlotFinalising_ok_unmapped ec addr st st' hW h
  obtain ⟨st1, st2, hD, hF, hEq⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  obtain ⟨-, hC1, -⟩ := cspaceDeleteSlot_slots hW.1 hD
  have hInv1 := cspaceDeleteSlot_preserves_capabilityInvariantBundle st st1 addr hInv hD
  obtain ⟨hI2, -, hC2, -, hV2⟩ :=
    finaliseDestroyedCapabilities_slots ec _ _ st1 st2 hInv1.2.2.2.2.1 hF
  have hFr := finaliseFinalObject_frame (slotRetireTarget st addr.cnode addr.slot) st2 hI2
  intro rid r' v p perms e hR hM hE
  obtain ⟨r, hr, ha, hm, he, -⟩ := hS rid r' hR
  obtain ⟨s, cap, fid, f, hc, ht, hf, hb, hmap⟩ :=
    hL rid r v p perms e hr (hm v _ hM) (he v e hE)
  by_cases hs : s = addr
  · subst hs
    exfalso
    have hP : capabilityMappedPage st cap = some ⟨r.asid, v, p, some e⟩ := by
      have hG : st.getFrame? fid = some f := (SystemState.getFrame?_eq_some_iff st fid f).2 hf
      simp [capabilityMappedPage, hmap, ht, hG, hb]
    have hNot := hUnmapped cap hc _ hP
    have hRes := resolveAsidRoot_of_root hW' hR
    rw [ha] at hRes
    unfold mappedPageLive at hNot
    simp only [hRes, VSpaceRoot.lookup, hM, hE] at hNot
    simp at hNot
  · refine ⟨s, cap, fid, f, ?_, ht, ?_, hb, ha ▸ hmap⟩
    · rw [hEq]
      unfold retireFinalisedObject
      rw [retireFinalObject_slotCapAt _ _ _ _ hFr.invExt, hFr.slotCapAt, hC2, hC1 s hs]
      exact hc
    · have hf2 := hV2.keeps_frame (cspaceDeleteSlot_keeps_frame hW.1 hD hf)
      have hf3 := hFr.write.keeps hf2 (not_finaliseWritableAny_frame f)
      rw [hEq]
      unfold retireFinalisedObject
      rcases retireFinalObject_keeps_frame ec _ (slotRetireRecorder st addr.cnode addr.slot) _
          hFr.invExt hf3 with hk | ⟨hT, hx⟩
      · exact hk
      · exfalso
        obtain ⟨c, hc0, hn, hFin⟩ := slotRetireTarget_spec hInv hT
        have hAddr : SystemState.namesAt st.slotCapAt ⟨addr.cnode, addr.slot⟩
            (SeLe4n.ObjId.ofNat (slotRetireTarget st addr.cnode addr.slot - 1)) := ⟨c, hc0, hn⟩
        exact hFin _ hAddr s hs ⟨cap, hc, by rw [← hx]; simp [Capability.namedObject, ht]⟩

-- ============================================================================
-- Capability writes that keep every record
-- ============================================================================

/-- A store at a key holding no mapping facts, of an object holding none, is a
slot write's object half. -/
theorem storeObject_slotWriteObjects {st st' : SystemState} {k : SeLe4n.ObjId}
    {pre post : KernelObject} (hInv : st.objects.invExt)
    (hS : storeObject k post st = .ok ((), st')) (hPre : st.objects[k]? = some pre)
    (hp : pre.mappingView = (none, none)) (hq : post.mappingView = (none, none)) :
    ∀ j : SeLe4n.ObjId, st'.objects[j]? = st.objects[j]? ∨
      ∃ pre post : KernelObject, st.objects[j]? = some pre ∧ st'.objects[j]? = some post ∧
        pre.mappingView = (none, none) ∧ post.mappingView = (none, none) := fun j => by
  by_cases hj : j = k
  · subst hj; exact .inr ⟨pre, post, hPre, storeObject_objects_eq _ _ _ _ hInv hS, hp, hq⟩
  · exact .inl (storeObject_objects_ne _ _ _ _ _ hj hInv hS)

/-- **An insert into an empty slot keeps the mappings recorded**, whatever the
capability inserted: every capability already held keeps its slot. -/
theorem cspaceInsertSlot_preserves_liveMappingsRecorded {addr : CSpaceAddr} {cap : Capability}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : cspaceInsertSlot addr cap st = .ok ((), st')) (hL : st.liveMappingsRecorded) :
    st'.liveMappingsRecorded := by
  obtain ⟨cn, hGet, -, hNone, hStore⟩ := cspaceInsertSlot_ok_decompose st st' addr cap h
  have hPre := (SystemState.getCNode?_eq_some_iff st addr.cnode cn).mp hGet
  refine hL.of_slotWrite (storeObject_slotWriteObjects hInv hStore hPre rfl rfl)
    (fun r c hc _ => ⟨r, c, ?_, rfl, rfl⟩)
  by_cases hr : r = addr
  · subst hr
    rw [SystemState.slotCapAt_of_object hPre] at hc
    change cn.lookup r.slot = some c at hc
    rw [hNone] at hc; cases hc
  · rw [cspaceInsertSlot_slotCapAt_ne hInv h r hr]; exact hc

/-- **A free-index write keeps the mappings recorded**: it rewrites one slot's
free index, keeping the capability's target and record. -/
theorem setCapFreeIndex_preserves_liveMappingsRecorded {st : SystemState} {addr : CSpaceAddr}
    {idx : Nat} (hInv : st.objects.invExt) (hL : st.liveMappingsRecorded) :
    (setCapFreeIndex st addr idx).liveMappingsRecorded := by
  cases hO : st.objects[addr.cnode]? with
  | none => unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO]; exact hL
  | some o =>
    cases o with
    | cnode cn =>
      have hS := setCapFreeIndex_eq_storeObject (idx := idx) hO
      have hObj := storeObject_slotWriteObjects hInv hS hO rfl rfl
      cases hLk : cn.lookup addr.slot with
      | none =>
        have hEq : cn.setFreeIndex addr.slot idx = cn := by unfold CNode.setFreeIndex; rw [hLk]
        rw [hEq] at hS
        refine hL.of_slotWrite hObj (fun r c hc _ => ⟨r, c, ?_, rfl, rfl⟩)
        rw [SystemState.slotCapAt_eq_bind] at hc ⊢
        by_cases hr : r.cnode = addr.cnode
        · rw [hr, storeObject_objects_eq _ _ _ _ hInv hS]; rw [hr, hO] at hc; exact hc
        · rw [storeObject_objects_ne _ _ _ _ _ hr hInv hS]; exact hc
      | some c0 =>
        rw [CNode.setFreeIndex_of_lookup hLk] at hS
        refine hL.of_slotWrite hObj (fun r c hc _ => ?_)
        by_cases e : r = addr
        · subst e
          have h0 : st.slotCapAt r = some c0 := (SystemState.slotCapAt_of_object hO).trans hLk
          rw [h0] at hc; cases hc
          refine ⟨r, c0.withFreeIndex idx, ?_, Capability.withFreeIndex_target _ _, rfl⟩
          rw [SystemState.slotCapAt_of_object (storeObject_objects_eq _ _ _ _ hInv hS)]
          exact CNode.lookup_insert_eq cn r.slot _ (CNode.slotsUnique_holds _)
            (CNode.slotAddressable_of_lookup _ _ _ hLk)
        · exact ⟨r, c, (SystemState.slotCapAt_storeObject_ne hInv hO hS
            (fun s' hs => CNode.lookup_insert_ne cn addr.slot s' _ (Ne.symm hs)
              (CNode.slotsUnique_holds _)) r e).trans hc, rfl, rfl⟩
    | _ => unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO]; exact hL

/-- **Setting a derivation's source full keeps the mappings recorded.** -/
theorem untypedSourceSetFull_preserves_liveMappingsRecorded {st : SystemState} {src : CSpaceAddr}
    {cap : Capability} (hInv : st.objects.invExt) (hL : st.liveMappingsRecorded) :
    (untypedSourceSetFull st src cap).liveMappingsRecorded :=
  untypedSourceSetFull_of (P := SystemState.liveMappingsRecorded) hL
    fun _ => setCapFreeIndex_preserves_liveMappingsRecorded hInv hL

/-- **A derivation edge keeps the mappings recorded**: it writes link words. -/
theorem cdtAddChild_preserves_liveMappingsRecorded {st : SystemState} {p c : SlotRef}
    {op : DerivationOp} (hInv : st.objects.invExt) (hL : st.liveMappingsRecorded) :
    (st.cdtAddChild p c op).liveMappingsRecorded :=
  SystemState.liveMappingsRecorded.of_linkReach (SystemState.cdtAddChild_reach st p c op) hInv hL

/-- **A derivation-node move keeps the mappings recorded**: it writes link words. -/
theorem cdtMove_preserves_liveMappingsRecorded {st : SystemState} {old new : SlotRef}
    (hInv : st.objects.invExt) (hL : st.liveMappingsRecorded) :
    (st.cdtMove old new).liveMappingsRecorded :=
  SystemState.liveMappingsRecorded.of_linkReach (SystemState.cdtMove_reach st old new) hInv hL

/-- **The core delete of a slot whose record another slot also holds keeps the
mappings recorded**: every other slot keeps its capability, and a record the
deleted slot held is still held by a slot it names. -/
theorem cspaceDeleteSlotCore_preserves_liveMappingsRecorded {addr : CSpaceAddr}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : cspaceDeleteSlotCore addr st = .ok ((), st'))
    (hDup : ∀ cap, st.slotCapAt addr = some cap → cap.mapped = true →
      ∃ r, r ≠ addr ∧ st.slotCapAt r = some cap)
    (hL : st.liveMappingsRecorded) : st'.liveMappingsRecorded := by
  obtain ⟨o, hO, hH, hS⟩ := cspaceDeleteSlotCore_ok h
  have hp : o.mappingView = (none, none) := by
    cases o <;> simp_all [KernelObject.holdsSlots, KernelObject.mappingView]
  have hq : (o.removeSlotCap addr.slot).mappingView = (none, none) := by
    cases o <;> simp_all [KernelObject.holdsSlots, KernelObject.mappingView,
      KernelObject.removeSlotCap]
  obtain ⟨-, hOther⟩ := cspaceDeleteSlotCore_slotCapAt hInv h
  refine hL.of_slotWrite (storeObject_slotWriteObjects hInv hS hO hp hq) (fun r c hc hm => ?_)
  by_cases hr : r = addr
  · subst hr
    obtain ⟨r', hr', hc'⟩ := hDup c hc hm
    exact ⟨r', c, (hOther r' hr').trans hc', rfl, rfl⟩
  · exact ⟨r, c, (hOther r hr).trans hc, rfl, rfl⟩

theorem cspaceInsertSlot_objects_invExt {addr : CSpaceAddr} {cap : Capability}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : cspaceInsertSlot addr cap st = .ok ((), st')) : st'.objects.invExt := by
  obtain ⟨cn, -, -, -, hStore⟩ := cspaceInsertSlot_ok_decompose st st' addr cap h
  exact storeObject_preserves_objects_invExt _ _ _ _ hInv hStore

/-- **The copy keeps the mappings recorded**: it inserts a capability carrying
no record into an empty slot, adds a derivation edge and may set the source
full. -/
theorem cspaceCopy_preserves_liveMappingsRecorded {src dst : CSpaceAddr} {st st' : SystemState}
    (hInv : st.objects.invExt) (hL : st.liveMappingsRecorded)
    (h : cspaceCopy src dst st = .ok ((), st')) : st'.liveMappingsRecorded := by
  obtain ⟨cap, st2, -, -, hIns, -, rfl⟩ := cspaceCopy_ok_decompose h
  have hI2 := cspaceInsertSlot_objects_invExt hInv hIns
  exact untypedSourceSetFull_preserves_liveMappingsRecorded
    ((SystemState.cdtAddChild_reach st2 src dst .copy).invExt hI2)
    (cdtAddChild_preserves_liveMappingsRecorded hI2
      (cspaceInsertSlot_preserves_liveMappingsRecorded hInv hIns hL))

/-- **The mint keeps the mappings recorded**: an insert into an empty slot. -/
theorem cspaceMint_preserves_liveMappingsRecorded {src dst : CSpaceAddr}
    {rights : AccessRightSet} {badge : Option SeLe4n.Badge} {st st' : SystemState}
    (hInv : st.objects.invExt) (hL : st.liveMappingsRecorded)
    (h : cspaceMint src dst rights badge st = .ok ((), st')) : st'.liveMappingsRecorded := by
  obtain ⟨-, child, -, hIns, -⟩ := cspaceMint_ok_decompose src dst rights badge st st' h
  exact cspaceInsertSlot_preserves_liveMappingsRecorded hInv hIns hL

/-- **The `.cspaceMint` arm keeps the mappings recorded**: the mint, a
derivation edge, and the source set full. -/
theorem cspaceMintWithCdt_preserves_liveMappingsRecorded {src dst : CSpaceAddr}
    {rights : AccessRightSet} {badge : Option SeLe4n.Badge} {st st' : SystemState}
    (hInv : st.objects.invExt) (hL : st.liveMappingsRecorded)
    (h : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) :
    st'.liveMappingsRecorded := by
  unfold cspaceMintWithCdt at h
  cases hM : cspaceMint src dst rights badge st with
  | error e => rw [hM] at h; cases h
  | ok pr =>
    obtain ⟨⟨⟩, st1⟩ := pr
    rw [hM] at h
    obtain ⟨-, child, -, hIns, -⟩ := cspaceMint_ok_decompose src dst rights badge st st1 hM
    have hI1 := cspaceInsertSlot_objects_invExt hInv hIns
    have hL1 := cspaceMint_preserves_liveMappingsRecorded hInv hL hM
    simp only at h
    split at h
    · split at h
      · cases h
      · cases h
        exact untypedSourceSetFull_preserves_liveMappingsRecorded
          ((SystemState.cdtAddChild_reach st1 src dst .mint).invExt hI1)
          (cdtAddChild_preserves_liveMappingsRecorded hI1 hL1)
    · cases h
      exact cdtAddChild_preserves_liveMappingsRecorded hI1 hL1

/-- **The move keeps the mappings recorded**: the capability, with its record,
is inserted into the empty destination before the source is emptied, so the
record is held throughout, and the derivation node then moves with it. -/
theorem cspaceMove_preserves_liveMappingsRecorded {src dst : CSpaceAddr} {st st' : SystemState}
    (hInv : st.objects.invExt) (hL : st.liveMappingsRecorded)
    (h : cspaceMove src dst st = .ok ((), st')) : st'.liveMappingsRecorded := by
  unfold cspaceMove at h
  by_cases hSelf : src = dst
  · simp [hSelf] at h
  simp only [hSelf, ↓reduceIte] at h
  cases hSrc : cspaceLookupSlot src st with
  | error e => rw [hSrc] at h; cases h
  | ok pair =>
    obtain ⟨cap, st1⟩ := pair
    have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 src cap hSrc
    subst hSt1
    have hCapSrc : st1.slotCapAt src = some cap :=
      SystemState.slotCapAt_of_lookupSlotCap (cspaceLookupSlot_ok_lookupSlotCap hSrc)
    rw [hSrc] at h
    simp only at h
    cases hNN : cap.toNonNull? with
    | none => rw [hNN] at h; cases h
    | some capNN =>
      rw [hNN] at h
      simp only at h
      have hVal : capNN.val = cap := by
        unfold Capability.toNonNull? at hNN
        split at hNN
        · cases hNN; rfl
        · cases hNN
      cases hIns : cspaceInsertSlot dst capNN.val st1 with
      | error e => rw [hIns] at h; cases h
      | ok pr2 =>
        obtain ⟨⟨⟩, st2⟩ := pr2
        rw [hIns] at h
        simp only at h
        cases hDel : cspaceDeleteSlotCore src st2 with
        | error e => rw [hDel] at h; cases h
        | ok pr3 =>
          obtain ⟨⟨⟩, st3⟩ := pr3
          rw [hDel] at h
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
          subst h
          have hI2 := cspaceInsertSlot_objects_invExt hInv hIns
          have hL2 := cspaceInsertSlot_preserves_liveMappingsRecorded hInv hIns hL
          have hDst : st2.slotCapAt dst = some cap := hVal ▸ cspaceInsertSlot_slotCapAt_self hInv hIns
          have hSrc2 : st2.slotCapAt src = some cap := by
            rw [cspaceInsertSlot_slotCapAt_ne hInv hIns src hSelf]; exact hCapSrc
          have hL3 := cspaceDeleteSlotCore_preserves_liveMappingsRecorded hI2 hDel
            (fun c hc _ => ⟨dst, Ne.symm hSelf, by rw [hSrc2] at hc; cases hc; exact hDst⟩) hL2
          obtain ⟨o, -, -, hS3⟩ := cspaceDeleteSlotCore_ok hDel
          exact cdtMove_preserves_liveMappingsRecorded
            (storeObject_preserves_objects_invExt _ _ _ _ hI2 hS3) hL3

/-- **The reply-cap mint keeps the mappings recorded**: it inserts a reply
capability, which carries no record, into an empty slot and adds a derivation
edge. -/
theorem mintReplyCapWithCdt_preserves_liveMappingsRecorded {src dst : CSpaceAddr}
    {st st' : SystemState} (hInv : st.objects.invExt) (hL : st.liveMappingsRecorded)
    (h : mintReplyCapWithCdt src dst st = .ok ((), st')) : st'.liveMappingsRecorded := by
  unfold mintReplyCapWithCdt at h
  cases hM : mintReplyCap src dst st with
  | error e => rw [hM] at h; cases h
  | ok pr =>
    obtain ⟨⟨⟩, st1⟩ := pr
    rw [hM] at h
    cases h
    unfold mintReplyCap at hM
    cases hLk : cspaceLookupSlot src st with
    | error e => rw [hLk] at hM; cases hM
    | ok pair =>
      obtain ⟨parent, st0⟩ := pair
      have hSt0 : st0 = st := cspaceLookupSlot_preserves_state st st0 src parent hLk
      subst hSt0
      rw [hLk] at hM
      simp only at hM
      split at hM
      · split at hM
        · have hI1 := cspaceInsertSlot_objects_invExt hInv hM
          exact cdtAddChild_preserves_liveMappingsRecorded hI1
            (cspaceInsertSlot_preserves_liveMappingsRecorded hInv hM hL)
        · cases hM
      · cases hM

/-- **What a finalising delete chain carries**: the capability invariants, the
teardown's well-formedness and the mapping records together, each step's
preservation of the third reading the first two. -/
def mappingRecordsCarried (st : SystemState) : Prop :=
  capabilityInvariantBundle st ∧ teardownWellFormed st ∧ st.liveMappingsRecorded

theorem cspaceDeleteSlotFinalising_preserves_mappingRecordsCarried (ec : Concurrency.CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (h : mappingRecordsCarried st)
    (hD : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) : mappingRecordsCarried st' :=
  ⟨cspaceDeleteSlotFinalising_preserves_capabilityInvariantBundle ec addr st st' h.1 hD,
    cspaceDeleteSlotFinalising_preserves_teardownWellFormed ec h.2.1 hD,
    cspaceDeleteSlotFinalising_preserves_liveMappingsRecorded ec addr st st' h.1 h.2.1 h.2.2 hD⟩

theorem finaliseFinalObject_preserves_mappingRecordsCarried (target : Nat) (st : SystemState)
    (h : mappingRecordsCarried st) : mappingRecordsCarried (finaliseFinalObject target st) :=
  ⟨finaliseFinalObject_preserves_capabilityInvariantBundle target st h.1,
    (finaliseFinalObject_preserves_teardownWellFormed target st h.2.1).1,
    finaliseFinalObject_preserves_liveMappingsRecorded target st h.2.1.1 h.2.2⟩

/-- **The finalising revocation keeps every live mapping recorded**: a run of
finalising deletes (`cspaceRevokeCdtFinalising_closed`). -/
theorem cspaceRevokeCdtFinalising_preserves_liveMappingsRecorded (ec : Concurrency.CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (hInv : capabilityInvariantBundle st)
    (hW : teardownWellFormed st) (hL : st.liveMappingsRecorded)
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    st'.liveMappingsRecorded :=
  (cspaceRevokeCdtFinalising_closed mappingRecordsCarried
    (cspaceDeleteSlotFinalising_preserves_mappingRecordsCarried ec)
    finaliseFinalObject_preserves_mappingRecordsCarried ⟨hInv, hW, hL⟩ h).2.2

/-- **The zombie delete keeps every live mapping recorded**: a chain of
finalising deletes and finalisations (`cspaceDeleteSlotZombie_closed`). -/
theorem cspaceDeleteSlotZombie_preserves_liveMappingsRecorded (ec : Concurrency.CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (hInv : capabilityInvariantBundle st)
    (hW : teardownWellFormed st) (hL : st.liveMappingsRecorded)
    (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    st'.liveMappingsRecorded :=
  (cspaceDeleteSlotZombie_closed mappingRecordsCarried
    (cspaceDeleteSlotFinalising_preserves_mappingRecordsCarried ec)
    finaliseFinalObject_preserves_mappingRecordsCarried ⟨hInv, hW, hL⟩ h).2.2

end SeLe4n.Kernel
