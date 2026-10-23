-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.ThreadSpaceCopy
import SeLe4n.Kernel.Lifecycle.Operations.ScrubAndUntyped

/-!
The capability bundle across the untyped carve (WS-ZA ZA5.4 part 17).

`retypeFromUntyped` makes three writes: the untyped's child record (an untyped
for an untyped, so no slot and no CNode changes), the carved object at an id
that held nothing, and the invoked capability's free index (an in-place rewrite
of an occupied slot that keeps its target).  The carved object holds no
capability and no derivation link, and a carved CNode resolves at most
`maxCSpaceDepth` bits (its request carries the bound), so storing it moves no slot, no link and no tree node
(`storeObject_absent_preserves_capabilityInvariantBundle`).

`untypedRetypeObject` adds a scrub of machine memory, which the bundle does not
read, and the insert of the new capability into the empty destination with its
edge under the invoked slot (`cdtAddChild src dst .retype`), which is a copy's:
the source holds a capability, so the tree names it, and the destination was
empty, so it did not (`cdt_addEdge_after_insert`, `treeShape_addEdge_after_insert`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **Storing an object that holds no capability and no derivation link at an id
that held nothing keeps the capability bundle less its shape.**  Every slot
reads and every link reads as before (the new object's slots are empty, and an
absent object's read as empty), the tree is untouched, and the new object, if a
CNode, is within the depth bound. -/
theorem storeObject_absent_preserves_capabilityBundleOffLinks
    {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (h : capabilityBundleOffLinks st) (hLinksAgree : cdtLinksAgree st)
    (hAbsent : st.objects[k]? = none)
    (hStore : storeObject k o st = .ok ((), st'))
    (hLinks : ∀ s f, o.linkAt s f = none)
    (hDepth : ∀ cn, o = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hCaps : ∀ s, o.slotCap s = none) :
    capabilityBundleOffLinks st' ∧ cdtLinksAgree st' := by
  obtain ⟨_, hComp, hAcyc, hDep, hObjInv, hRCPV⟩ := h
  have hCdt := storeObject_cdt_eq st st' k o hStore
  have hSelf := storeObject_objects_eq st st' k o hObjInv hStore
  have hNe : ∀ oid, oid ≠ k → st'.objects[oid]? = st.objects[oid]? :=
    fun oid hn => storeObject_objects_ne st st' k oid o hn hObjInv hStore
  have hLinkAt : st'.slotLinkAt = st.slotLinkAt := funext fun r => funext fun f => by
    rw [SystemState.slotLinkAt_def, SystemState.slotLinkAt_def]
    by_cases e : r.cnode = k
    · rw [e, hSelf, hAbsent]; exact hLinks r.slot f
    · rw [hNe _ e]
  refine ⟨⟨cspaceLookupSound_holds st', ?_, cdtAcyclicity_of_cdt_eq st st' hAcyc hCdt, ?_,
    storeObject_preserves_objects_invExt st st' k o hObjInv hStore, ?_⟩,
    cdtLinksAgree_of_eq hLinksAgree hCdt hLinkAt⟩
  · intro ref hM
    rw [hCdt] at hM
    obtain ⟨o0, hO, hL⟩ := hComp ref hM
    have e : ref.cnode ≠ k := fun e => by rw [e, hAbsent] at hO; cases hO
    exact ⟨o0, by rw [hNe _ e]; exact hO, hL⟩
  · intro oid cn hO
    by_cases e : oid = k
    · rw [e, hSelf] at hO; exact hDepth cn (Option.some.inj hO)
    · rw [hNe _ e] at hO; exact hDep oid cn hO
  · intro oid o' slot cap rid hO hL hT
    have e : oid ≠ k := fun e => by
      rw [e, hSelf] at hO; cases hO; rw [hCaps] at hL; cases hL
    rw [hNe _ e] at hO
    have hR := hRCPV oid o' slot cap rid hO hL hT
    unfold SystemState.getReply? at hR ⊢
    by_cases e' : rid.toObjId = k
    · rw [e', hAbsent] at hR; exact absurd rfl hR
    · rw [hNe _ e']; exact hR

/-- Storing an object holding no capability at an id that held nothing keeps
every slot's capability. -/
theorem storeObject_absent_slotCapAt {st st' : SystemState} {k : SeLe4n.ObjId}
    {o : KernelObject} (hObjInv : st.objects.invExt) (hAbsent : st.objects[k]? = none)
    (hStore : storeObject k o st = .ok ((), st')) (hCaps : ∀ s, o.slotCap s = none)
    (r : SlotRef) : st'.slotCapAt r = st.slotCapAt r := by
  rw [SystemState.slotCapAt_storeObject hObjInv hStore]
  split
  · next h => rw [hCaps, SystemState.slotCapAt_eq_bind, h, hAbsent]; rfl
  · rfl

/-- **Rewriting an untyped's record keeps the capability bundle less its
shape**: an untyped holds no slot and no link and is no CNode, thread or Reply,
so every conjunct but the shape, which reads the untyped records, frames. -/
theorem storeObject_untyped_preserves_capabilityBundleOffLinks
    {st st' : SystemState} {k : SeLe4n.ObjId} {u u' : UntypedObject}
    (h : capabilityInvariantBundle st) (hPre : st.objects[k]? = some (.untyped u))
    (hStore : storeObject k (.untyped u') st = .ok ((), st')) :
    capabilityBundleOffLinks st' ∧ cdtLinksAgree st' := by
  have hObjInv := h.2.2.2.2.1
  have hSelf := storeObject_objects_eq st st' k _ hObjInv hStore
  have hNe : ∀ oid, oid ≠ k → st'.objects[oid]? = st.objects[oid]? :=
    fun oid hn => storeObject_objects_ne st st' k oid _ hn hObjInv hStore
  refine capabilityBundleOffLinks_of_frame h (storeObject_cdt_eq st st' k _ hStore) ?_ ?_ ?_ ?_
    (storeObject_preserves_objects_invExt st st' k _ hObjInv hStore)
  · intro oid cn hC
    by_cases e : oid = k
    · rw [e, hSelf] at hC; cases hC
    · rw [hNe oid e] at hC; exact hC
  · intro oid cn hC
    by_cases e : oid = k
    · rw [e, hPre] at hC; cases hC
    · rw [hNe oid e]; exact hC
  · intro oid
    by_cases e : oid = k
    · rw [e, hSelf, hPre]; rfl
    · rw [hNe oid e]
  · intro rid hR
    unfold SystemState.getReply? at hR ⊢
    by_cases e : rid.toObjId = k
    · rw [e, hPre] at hR; exact absurd rfl hR
    · rw [hNe _ e]; exact hR

/-- **What a carve's two object stores do to the readers the shape reads**: the
tree and every slot are kept, every object stays in the store and the carved one
joins it, and the untyped records are the pre-state's but for the parent, which
records the carved object, and the carved object's own (if it is an untyped). -/
theorem retypeFromUntyped_stores_shape
    {st stUt stCh : SystemState} {untypedId childId : SeLe4n.ObjId} {ut ut' : UntypedObject}
    {newObj : KernelObject} {idx size offset : Nat}
    (hShape : SystemState.CapTreeShape st) (hObjInv : st.objects.invExt)
    (hUt : st.objects[untypedId]? = some (.untyped ut))
    (hChild : st.objects[childId]? = none) (hNe : childId ≠ untypedId)
    (hAlloc : ut.allocate idx childId size = some (ut', offset))
    (hStUt : storeObject untypedId (.untyped ut') st = .ok ((), stUt))
    (hStCh : storeObject childId newObj stUt = .ok ((), stCh))
    (hCaps : ∀ s, newObj.slotCap s = none)
    (hKids : ∀ W, newObj.untyped? = some W → W.children = []) :
    SystemState.TreeShapeOver stCh.cdt stCh.slotCapAt stCh.objectPresent stCh.getUntyped?
      (fun _ => False) := by
  have hInvUt := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStUt
  have hChildUt : stUt.objects[childId]? = none := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hObjInv hStUt]; exact hChild
  have hCdt : stCh.cdt = st.cdt :=
    (storeObject_cdt_eq _ _ _ _ hStCh).trans (storeObject_cdt_eq _ _ _ _ hStUt)
  have hCap : stCh.slotCapAt = st.slotCapAt := funext fun r => by
    rw [storeObject_absent_slotCapAt hInvUt hChildUt hStCh hCaps r,
      SystemState.slotCapAt_storeObject hObjInv hStUt]
    split
    · next h => rw [SystemState.slotCapAt_eq_bind, h, hUt]; rfl
    · rfl
  have hChUt := storeObject_objects_eq _ _ _ _ hInvUt hStCh
  have hUtUt : stCh.objects[untypedId]? = some (.untyped ut') := by
    rw [storeObject_objects_ne _ _ _ _ _ (Ne.symm hNe) hInvUt hStCh,
      storeObject_objects_eq _ _ _ _ hObjInv hStUt]
  have hOth : ∀ v, v ≠ untypedId → v ≠ childId → stCh.objects[v]? = st.objects[v]? := fun v h1 h2 => by
    rw [storeObject_objects_ne _ _ _ _ _ h2 hInvUt hStCh,
      storeObject_objects_ne _ _ _ _ _ h1 hObjInv hStUt]
  have hPres : ∀ o, st.objectPresent o → stCh.objectPresent o := fun o hp =>
    SystemState.objectPresent_storeObject hInvUt hStCh o
      (SystemState.objectPresent_storeObject hObjInv hStUt o hp)
  rw [hCdt, hCap]
  refine hShape.carveRecord (u := untypedId) (w := childId) (U := ut) (U' := ut')
    (by rw [SystemState.getUntyped?_eq_bind, hUt]; rfl)
    (by rw [SystemState.getUntyped?_eq_bind, hUtUt]; rfl)
    (UntypedObject.allocate_preserves_region _ _ _ _ _ _ hAlloc).2
    (fun ch hch => by
      rw [UntypedObject.allocate_children_eq _ _ _ _ _ _ hAlloc] at hch
      rcases List.mem_cons.mp hch with e | e
      · exact .inr (by rw [e])
      · exact .inl e)
    (fun v h1 h2 => by rw [SystemState.getUntyped?_eq_bind, SystemState.getUntyped?_eq_bind, hOth v h1 h2])
    (fun W hW => hKids W (by rw [SystemState.getUntyped?_eq_bind, hChUt] at hW; exact hW))
    (fun r hr => hShape.live r childId hr hChild) (fun h => h hChild)
    (by show stCh.objects[childId]? ≠ none; rw [hChUt]; exact Option.some_ne_none _) hPres

/-- **`retypeFromUntyped` preserves the capability bundle** when the object it
carves holds no capability and no link, records no child if it is an untyped
and, if a CNode, is within the depth bound: the untyped's record gains the
child (`TreeShapeOver.carveRecord`), the object lands at an id that held nothing
(the collision guard), and the authority's free index is rewritten in its
occupied slot, its target kept.  The authority was not full (the carve fit), so
it had no strict descendant to its untyped, and a lower index owes (b) nothing
more (WS-ZA ZA5.4 part 19). -/
theorem retypeFromUntyped_preserves_capabilityInvariantBundle
    (st st' : SystemState) (authority : CSpaceAddr) (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject) (allocSize : Nat)
    (hInv : capabilityInvariantBundle st)
    (hCaps : ∀ s, newObj.slotCap s = none) (hLinks : ∀ s f, newObj.linkAt s f = none)
    (hDepth : ∀ cn, newObj = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hKids : ∀ W, newObj.untyped? = some W → W.children = [])
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  have hObjInv := hInv.2.2.2.2.1
  have hFresh := retypeFromUntyped_childId_fresh authority untypedId childId newObj allocSize
    st st' hStep
  obtain ⟨ut, ut', cap, stUt, _, stCh, cn, hUt, _, _, _, hAuth, hAlloc, hPreA, hLkA, _, _, hStUt,
    hStCh, hOCh, hStIdx⟩ := retypeFromUntyped_ok_stores st st' authority untypedId childId _ _
      hObjInv hStep
  have hNe : childId ≠ untypedId := by
    intro h; rw [h, hUt] at hFresh; simp at hFresh
  have hChild : st.objects[childId]? = none := by
    cases h : st.objects[childId]? with
    | none => rfl
    | some _ => rw [h] at hFresh; simp at hFresh
  have hInvUt := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStUt
  have hChildUt : stUt.objects[childId]? = none := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hObjInv hStUt]; exact hChild
  obtain ⟨hBUt, hLUt⟩ := storeObject_untyped_preserves_capabilityBundleOffLinks hInv hUt hStUt
  obtain ⟨hBCh, hLCh⟩ := storeObject_absent_preserves_capabilityBundleOffLinks hBUt hLUt hChildUt
    hStCh hLinks hDepth hCaps
  have hShapeCh := retypeFromUntyped_stores_shape hInv.treeShape hObjInv hUt hChild hNe hAlloc
    hStUt hStCh hCaps hKids
  have hCdtCh : stCh.cdt = st.cdt :=
    (storeObject_cdt_eq _ _ _ _ hStCh).trans (storeObject_cdt_eq _ _ _ _ hStUt)
  have hCapCh : stCh.slotCapAt = st.slotCapAt := funext fun r => by
    rw [storeObject_absent_slotCapAt hInvUt hChildUt hStCh hCaps r,
      SystemState.slotCapAt_storeObject hObjInv hStUt]
    split
    · next h => rw [SystemState.slotCapAt_eq_bind, h, hUt]; rfl
    · rfl
  -- the authority names the untyped and was not full: the carve fit after its index
  have hT : cap.target = .object untypedId := by
    unfold lifecycleRetypeAuthority at hAuth; simp at hAuth; exact hAuth.1
  have hCan := ((UntypedObject.allocate_some_iff _ _ _ _ _).mp hAlloc).1
  have hLe := le_alignedCarveIndex newObj.objectType allocSize ut cap.freeIndex
  have hNotFull : cap.freeIndex < ut.regionSize := by
    simp [UntypedObject.canAllocate] at hCan; omega
  have hSrc : st.slotCapAt authority = some cap := (SystemState.slotCapAt_of_object hPreA).trans hLkA
  have hUtSt : st.getUntyped? untypedId = some ut := by
    rw [SystemState.getUntyped?_eq_bind, hUt]; rfl
  refine storeObject_capRewrite_restores_capabilityInvariantBundle stCh st' authority cn cap _
    hBCh hLCh hShapeCh (fun _ _ h => h) hOCh hLkA (Capability.withFreeIndex_target _ _)
    (fun u _ ht _ _ r hr hru => ?_) hStIdx
  rw [Capability.withFreeIndex_target, hT] at ht
  cases ht
  rw [hCdtCh] at hr
  rw [hCapCh] at hru
  obtain ⟨c, hc, hct, -⟩ := hru
  exact hInv.treeShape.notFullLeaf authority cap _ ut id hSrc hT hUtSt hNotFull r hr
    ⟨c, hc, hct, by rw [hUtSt]; exact Option.some_ne_none _⟩

/-- **After a carve the authority has no strict descendant holding a
capability to its untyped**: the carve keeps the tree and every slot's target,
and before it the authority was not full. -/
theorem retypeFromUntyped_authority_leaf
    (st st' : SystemState) (authority : CSpaceAddr) (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject) (allocSize : Nat) (hInv : capabilityInvariantBundle st)
    (hCaps : ∀ s, newObj.slotCap s = none)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    ∀ u, SystemState.untypedCapAt st'.slotCapAt st'.getUntyped? authority u →
      ∀ r, CapDerivationTree.CdtChildReachable st'.cdt authority r →
        ¬ SystemState.untypedCapAt st'.slotCapAt st'.getUntyped? r u := by
  have hObjInv := hInv.2.2.2.2.1
  have hFresh := retypeFromUntyped_childId_fresh authority untypedId childId newObj allocSize
    st st' hStep
  obtain ⟨ut, ut', cap, stUt, _, stCh, cn, hUt, _, _, _, hAuth, hAlloc, hPreA, hLkA, _, _, hStUt,
    hStCh, hOCh, hStIdx⟩ := retypeFromUntyped_ok_stores st st' authority untypedId childId _ _
      hObjInv hStep
  have hNe : childId ≠ untypedId := by
    intro h; rw [h, hUt] at hFresh; simp at hFresh
  have hChild : st.objects[childId]? = none := by
    cases h : st.objects[childId]? with
    | none => rfl
    | some _ => rw [h] at hFresh; simp at hFresh
  have hInvUt := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStUt
  have hInvCh := storeObject_preserves_objects_invExt _ _ _ _ hInvUt hStCh
  have hChildUt : stUt.objects[childId]? = none := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hObjInv hStUt]; exact hChild
  have hCdt : st'.cdt = st.cdt := (storeObject_cdt_eq _ _ _ _ hStIdx).trans
    ((storeObject_cdt_eq _ _ _ _ hStCh).trans (storeObject_cdt_eq _ _ _ _ hStUt))
  have hCapCh : ∀ r, stCh.slotCapAt r = st.slotCapAt r := fun r => by
    rw [storeObject_absent_slotCapAt hInvUt hChildUt hStCh hCaps r,
      SystemState.slotCapAt_storeObject hObjInv hStUt]
    split
    · next h => rw [SystemState.slotCapAt_eq_bind, h, hUt]; rfl
    · rfl
  have hT : cap.target = .object untypedId := by
    unfold lifecycleRetypeAuthority at hAuth; simp at hAuth; exact hAuth.1
  have hCan := ((UntypedObject.allocate_some_iff _ _ _ _ _).mp hAlloc).1
  have hLe := le_alignedCarveIndex newObj.objectType allocSize ut cap.freeIndex
  have hNotFull : cap.freeIndex < ut.regionSize := by
    simp [UntypedObject.canAllocate] at hCan; omega
  have hSrc : st.slotCapAt authority = some cap := (SystemState.slotCapAt_of_object hPreA).trans hLkA
  have hUtSt : st.getUntyped? untypedId = some ut := by
    rw [SystemState.getUntyped?_eq_bind, hUt]; rfl
  -- every slot of the post-state holds a capability with a pre-state slot's target
  have hBack : ∀ r c', st'.slotCapAt r = some c' → ∃ c, st.slotCapAt r = some c ∧ c'.target = c.target := by
    intro r c' hc'
    by_cases e : r = authority
    · rw [e] at hc' ⊢
      rw [SystemState.slotCapAt_of_object (storeObject_objects_eq _ _ _ _ hInvCh hStIdx)] at hc'
      have hL := CNode.lookup_insert_eq cn authority.slot
        (cap.withFreeIndex (alignedCarveIndex newObj.objectType allocSize ut cap.freeIndex +
          allocSize)) (CNode.slotsUnique_holds _) (CNode.slotAddressable_of_lookup _ _ _ hLkA)
      cases Option.some.inj (hc'.symm.trans hL)
      exact ⟨cap, hSrc, Capability.withFreeIndex_target _ _⟩
    · rw [SystemState.slotCapAt_storeObject_ne hInvCh hOCh hStIdx
        (fun s' hs => CNode.lookup_insert_ne cn authority.slot s' _ (Ne.symm hs)
          (CNode.slotsUnique_holds _)) r e, hCapCh r] at hc'
      exact ⟨c', hc', rfl⟩
  intro u hu r hr hru
  obtain ⟨ca, hca, hcat, -⟩ := hu
  obtain ⟨c0, hc0, hc0t⟩ := hBack _ _ hca
  rw [hSrc] at hc0; cases hc0
  rw [hc0t, hT] at hcat; cases hcat
  obtain ⟨c, hc, hct, -⟩ := hru
  obtain ⟨d, hd, hdt⟩ := hBack _ _ hc
  rw [hCdt] at hr
  exact hInv.treeShape.notFullLeaf authority cap _ ut id hSrc hT hUtSt hNotFull r hr
    ⟨d, hd, hdt ▸ hct, by rw [hUtSt]; exact Option.some_ne_none _⟩

/-- **What a carve owes its new capability's place**: the carved object, if an
untyped, records nothing, and every capability to an untyped the carved object
is carved from is the authority or lies above it — the carved object's one
recorder is the authority's untyped (`TreeShapeOver.carvedFrom_last`), whose
capabilities form one chain the authority, not full before the carve, ends. -/
theorem retypeFromUntyped_fresh_child
    (st st' : SystemState) (authority : CSpaceAddr) (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject) (allocSize : Nat)
    (hInv : capabilityInvariantBundle st)
    (hCaps : ∀ s, newObj.slotCap s = none) (hLinks : ∀ s f, newObj.linkAt s f = none)
    (hDepth : ∀ cn, newObj = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hKids : ∀ W, newObj.untyped? = some W → W.children = [])
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    (∀ U, st'.getUntyped? childId = some U → U.children = []) ∧
    (∀ t, SystemState.CarvedFrom st'.getUntyped? t childId →
      ∀ p, SystemState.untypedCapAt st'.slotCapAt st'.getUntyped? p t →
        p = authority ∨ CapDerivationTree.CdtChildReachable st'.cdt p authority) := by
  have hObjInv := hInv.2.2.2.2.1
  have hFresh := retypeFromUntyped_childId_fresh authority untypedId childId newObj allocSize
    st st' hStep
  obtain ⟨ut, ut', cap, stUt, _, stCh, cn, hUt, _, _, _, hAuth, hAlloc, _, hLkA, hAU, hAC, hStUt,
    hStCh, hOCh, hStIdx⟩ := retypeFromUntyped_ok_stores st st' authority untypedId childId _ _
      hObjInv hStep
  have hNe : childId ≠ untypedId := by
    intro h; rw [h, hUt] at hFresh; simp at hFresh
  have hInvUt := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStUt
  have hInvCh := storeObject_preserves_objects_invExt _ _ _ _ hInvUt hStCh
  have hObjCh : st'.objects[childId]? = some newObj := by
    rw [storeObject_objects_ne _ _ _ _ _ (Ne.symm hAC) hInvCh hStIdx,
      storeObject_objects_eq _ _ _ _ hInvUt hStCh]
  have hObjU : st'.objects[untypedId]? = some (.untyped ut') := by
    rw [storeObject_objects_ne _ _ _ _ _ (Ne.symm hAU) hInvCh hStIdx,
      storeObject_objects_ne _ _ _ _ _ (Ne.symm hNe) hInvUt hStCh,
      storeObject_objects_eq _ _ _ _ hObjInv hStUt]
  have hUt' : st'.getUntyped? untypedId = some ut' := by
    rw [SystemState.getUntyped?_eq_bind, hObjU]; rfl
  have hRec : SystemState.recordsChild st'.getUntyped? untypedId childId :=
    ⟨ut', hUt', _, UntypedObject.allocate_children_new _ _ _ _ _ _ hAlloc, rfl⟩
  have hT : cap.target = .object untypedId := by
    unfold lifecycleRetypeAuthority at hAuth; simp at hAuth; exact hAuth.1
  have hSrcU : SystemState.untypedCapAt st'.slotCapAt st'.getUntyped? authority untypedId := by
    refine ⟨cap.withFreeIndex (alignedCarveIndex newObj.objectType allocSize ut cap.freeIndex +
      allocSize), ?_, by rw [Capability.withFreeIndex_target, hT], by rw [hUt']; simp⟩
    rw [SystemState.slotCapAt_of_object (storeObject_objects_eq _ _ _ _ hInvCh hStIdx)]
    exact CNode.lookup_insert_eq cn authority.slot _ (CNode.slotsUnique_holds _)
      (CNode.slotAddressable_of_lookup _ _ _ hLkA)
  have h' := (retypeFromUntyped_preserves_capabilityInvariantBundle st st' authority untypedId
    childId newObj allocSize hInv hCaps hLinks hDepth hKids hStep).treeShape
  have hLeaf := retypeFromUntyped_authority_leaf st st' authority untypedId childId newObj
    allocSize hInv hCaps hStep
  refine ⟨fun U hU => hKids U (by rw [SystemState.getUntyped?_eq_bind, hObjCh] at hU; exact hU),
    fun t hx p hp => ?_⟩
  rcases h'.carvedFrom_last hRec hx with e | ht
  · rw [e] at hp
    rcases h'.chainLinear _ p authority hp hSrcU with e' | e' | e'
    · exact .inl e'
    · exact .inr e'
    · exact absurd hp (hLeaf untypedId hSrcU p e')
  · exact .inr (h'.carvedBelow t untypedId ht p authority hp hSrcU.namesAt)

/-- **A carve names nothing new in the slots, and its object is in the store**:
the untyped's record and the carved object hold no capability, and the free-index
write keeps the invoked capability's target. -/
theorem retypeFromUntyped_namesAt
    (st st' : SystemState) (authority : CSpaceAddr) (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject) (allocSize : Nat) (hObjInv : st.objects.invExt)
    (hCaps : ∀ s, newObj.slotCap s = none)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    (∀ r o, SystemState.namesAt st'.slotCapAt r o → SystemState.namesAt st.slotCapAt r o) ∧
      st'.objectPresent childId := by
  have hFresh := retypeFromUntyped_childId_fresh authority untypedId childId newObj allocSize
    st st' hStep
  obtain ⟨ut, ut', cap, stUt, _, stCh, cn, hUt, _, _, _, _, _, _, hLkA, _, _, hStUt, hStCh, hOCh,
    hStIdx⟩ := retypeFromUntyped_ok_stores st st' authority untypedId childId _ _ hObjInv hStep
  have hNe : childId ≠ untypedId := by
    intro h; rw [h, hUt] at hFresh; simp at hFresh
  have hInvUt := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStUt
  have hInvCh := storeObject_preserves_objects_invExt _ _ _ _ hInvUt hStCh
  have hChildNone : stUt.objects[childId]? = none := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hObjInv hStUt]
    cases h : st.objects[childId]? with
    | none => rfl
    | some _ => rw [h] at hFresh; simp at hFresh
  have hA : ∀ r, stUt.slotCapAt r = st.slotCapAt r := fun r => by
    rw [SystemState.slotCapAt_storeObject hObjInv hStUt]
    split
    · next h => rw [SystemState.slotCapAt_eq_bind, h, hUt]; rfl
    · rfl
  have hB : ∀ r, stCh.slotCapAt r = stUt.slotCapAt r := fun r => by
    rw [SystemState.slotCapAt_storeObject hInvUt hStCh]
    split
    · next h => rw [hCaps, SystemState.slotCapAt_eq_bind, h, hChildNone]; rfl
    · rfl
  refine ⟨fun r o h => ?_, SystemState.objectPresent_storeObject hInvCh hStIdx childId ?_⟩
  · have h' := (SystemState.namesAt_storeObject_insert hInvCh hOCh hLkA
      (Capability.namedObject_of_target (Capability.withFreeIndex_target _ _)) hStIdx r o).mp h
    exact (SystemState.namesAt_of_eq ((hB r).trans (hA r))).mp h'
  · show stCh.objects[childId]? ≠ none
    rw [storeObject_objects_eq _ _ _ _ hInvUt hStCh]; exact Option.some_ne_none _

/-- After a carve the authority's slot still holds a capability: its free index
was advanced in place. -/
theorem retypeFromUntyped_lookupSlotCap_authority
    (st st' : SystemState) (authority : CSpaceAddr) (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject) (allocSize : Nat) (hObjInv : st.objects.invExt)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    (SystemState.lookupSlotCap st' authority).isSome := by
  obtain ⟨_, _, _, _, _, _, cn, _, _, _, _, _, _, _, hLkA, _, _, hStUt, hStCh, _,
    hStIdx⟩ := retypeFromUntyped_ok_stores st st' authority untypedId childId _ _ hObjInv hStep
  have hInvCh := storeObject_preserves_objects_invExt _ _ _ _
    (storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStUt) hStCh
  have hO := storeObject_objects_eq _ _ _ _ hInvCh hStIdx
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp
    (CNode.lookup_insert_ne_none cn authority.slot authority.slot _ (by rw [hLkA]; simp))
  rw [(cspaceLookupSound_holds st').1 _ _ _ _ hO hc]; rfl

/-- A request's scrub writes no derivation tree. -/
theorem CarveRequest.scrub_cdt (st : SystemState) (ut : UntypedObject) (idx : Nat)
    (req : CarveRequest) : (req.scrub st ut idx).cdt = st.cdt := by
  cases req <;> simp only [CarveRequest.scrub, carveZeroFrame] <;> (try split) <;> rfl

/-- A carved object holds no capability: a carved CNode's slots and a carved
thread's space slots are empty, and no other kind has slots. -/
theorem CarveRequest.object_slotCap (untypedId childId : SeLe4n.ObjId) (ut : UntypedObject)
    (idx : Nat) (req : CarveRequest) (s : SeLe4n.Slot) :
    (req.object untypedId childId ut idx).slotCap s = none := by
  cases req
  case tcb dom core =>
    simp only [CarveRequest.object, KernelObject.slotCap, TCB.spaceSlotCap, carvedTcb]
    split
    · next h =>
      rcases (by omega : s.toNat = 0 ∨ s.toNat = 1) with e | e <;> simp [e]
    · rfl
  all_goals
    simp [CarveRequest.object, KernelObject.slotCap, carvedCNode,
      CNode.lookup, CNode.slots_ofSlots, UniqueSlotMap.get?_filter, UniqueSlotMap.get?_empty]

/-- A carved object holds no derivation link: every link word of a carved CNode
and of a carved thread's space slots is 0. -/
theorem CarveRequest.object_linkAt (untypedId childId : SeLe4n.ObjId) (ut : UntypedObject)
    (idx : Nat) (req : CarveRequest) (s : SeLe4n.Slot) (f : LinkField) :
    (req.object untypedId childId ut idx).linkAt s f = none := by
  cases req
  case cnode r _ =>
    exact CNode.linkAt_of_linksClear (by simp [CNode.linksClear, carvedCNode, CNode.ofSlots]) s f
  case tcb dom core =>
    exact TCB.spaceLinkAt_of_spaceLinksClear (by simp [TCB.spaceLinksClear, carvedTcb]) s f
  all_goals rfl

/-- A carved CNode is within the depth bound: it has no guard and resolves
exactly its radix bits, which its request bounds (`CarveRequest.cnode`). -/
theorem CarveRequest.object_depthConsistent (untypedId childId : SeLe4n.ObjId)
    (ut : UntypedObject) (idx : Nat) (req : CarveRequest) :
    ∀ cn, req.object untypedId childId ut idx = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed) := by
  intro cn hO
  cases req <;> simp only [CarveRequest.object, KernelObject.cnode.injEq, reduceCtorEq] at hO
  case cnode r hr =>
    subst hO
    refine ⟨hr, fun hPos => ?_⟩
    simp only [CNode.bitsConsumed, carvedCNode, CNode.ofSlots_guardWidth] at hPos ⊢
    exact ⟨by simp [CNode.bitsConsumed], by simpa [CNode.bitsConsumed]
      using hPos, by simp [CNode.guardBounded]⟩

/-- A carved untyped records no child: it is the parent's next child, carved
whole. -/
theorem CarveRequest.object_untyped_children (untypedId childId : SeLe4n.ObjId)
    (ut : UntypedObject) (idx : Nat) (req : CarveRequest) :
    ∀ W, (req.object untypedId childId ut idx).untyped? = some W → W.children = [] := by
  intro W hW
  cases req <;> simp [CarveRequest.object, KernelObject.untyped?] at hW
  subst hW; rfl

/-- **The untyped carve preserves the capability bundle** (WS-ZA ZA5.4 part 17),
all eight conjuncts: the carve itself (`retypeFromUntyped_preserves_capabilityInvariantBundle`,
over a carved object that holds no capability and no link), a scrub of machine
memory, the install of the new capability into the empty destination, and its
edge under the invoked slot, `cdtAddChild src dst .retype`, as a copy's.  The
invoked slot still holds its capability after the carve, so the tree names it and
the new child lands right after it in the preorder; the destination was empty, so
the tree did not name it and the edge closes no cycle. -/
theorem untypedRetypeObject_preserves_capabilityInvariantBundle
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (req : CarveRequest)
    (st st' : SystemState) (hInv : capabilityInvariantBundle st)
    (hStep : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hInv.2.2.2.2.1 hStep
  have hKids := CarveRequest.object_untyped_children untypedId childId ut
    (req.carveIndex ut utCap.freeIndex) req
  have hInv1 := retypeFromUntyped_preserves_capabilityInvariantBundle st st1 src untypedId
    childId _ _ hInv (CarveRequest.object_slotCap _ _ _ _ req)
    (CarveRequest.object_linkAt _ _ _ _ req) (CarveRequest.object_depthConsistent _ _ _ _ req)
    hKids hRt
  have hLeaf1 := retypeFromUntyped_authority_leaf st st1 src untypedId childId _ _ hInv
    (CarveRequest.object_slotCap _ _ _ _ req) hRt
  obtain ⟨hKids1, hBelow1⟩ := retypeFromUntyped_fresh_child st st1 src untypedId childId _ _ hInv
    (CarveRequest.object_slotCap _ _ _ _ req) (CarveRequest.object_linkAt _ _ _ _ req)
    (CarveRequest.object_depthConsistent _ _ _ _ req) hKids hRt
  have hSrc1 := retypeFromUntyped_lookupSlotCap_authority st st1 src untypedId childId _ _
    hInv.2.2.2.2.1 hRt
  have hObjZ := CarveRequest.scrub_objects st1 ut (req.carveIndex ut utCap.freeIndex) req
  have hCdtZ := CarveRequest.scrub_cdt st1 ut (req.carveIndex ut utCap.freeIndex) req
  have hInvZ := capabilityInvariantBundle_of_objects_and_cdt_eq hInv1 hObjZ hCdtZ
  have hSrc : (SystemState.lookupSlotCap (req.scrub st1 ut (req.carveIndex ut utCap.freeIndex))
      src).isSome := by
    unfold SystemState.lookupSlotCap SystemState.lookupCNode at hSrc1 ⊢
    simpa only [SystemState.getObject?, hObjZ] using hSrc1
  have hObjInvZ := hInvZ.2.2.2.2.1
  have hBundle2 := cspaceInsertSlot_preserves_capabilityBundleOffCoverage _ st2 dst _
    hInvZ.offCoverage (fun rid hT => by
      rw [CarveRequest.capability_eq] at hT; cases hT) hIns
  have hCdt := cdt_addEdge_after_insert _ st2 src dst _ .retype hInvZ.2.1 hInvZ.2.2.1 hObjInvZ
    hSrc hIns hInvZ.linksAgree
  -- The carved object's id held nothing, so no slot named it (`live`), and the
  -- carve names nothing new: the new capability is the only slot naming it.
  have hFresh := retypeFromUntyped_childId_fresh src untypedId childId _ _ st st1 hRt
  obtain ⟨hNm1, hPres1⟩ := retypeFromUntyped_namesAt st st1 src untypedId childId _ _
    hInv.2.2.2.2.1 (CarveRequest.object_slotCap _ _ _ _ req) hRt
  have hCapZ : (req.scrub st1 ut (req.carveIndex ut utCap.freeIndex)).slotCapAt =
      st1.slotCapAt := funext fun r => by
    rw [SystemState.slotCapAt_eq_bind, SystemState.slotCapAt_eq_bind, hObjZ]
  have hUtZ : (req.scrub st1 ut (req.carveIndex ut utCap.freeIndex)).getUntyped? =
      st1.getUntyped? := funext fun o => by
    rw [SystemState.getUntyped?_eq_bind, SystemState.getUntyped?_eq_bind, hObjZ]
  have hShape := treeShape_addEdge_after_fresh _ st2 src dst _ .retype hInvZ.treeShape
    hInvZ.2.1 hObjInvZ hSrc hIns (by rw [hCapZ, hUtZ, hCdtZ]; exact hLeaf1) fun o ho => by
      rw [CarveRequest.capability_eq] at ho
      simp only [Capability.namedObject, Option.some.injEq] at ho
      subst ho
      refine ⟨fun r hr => ?_, cspaceInsertSlot_objectPresent hObjInvZ hIns _ ?_,
        by rw [hCapZ, hUtZ, hCdtZ]; exact hBelow1, by rw [hUtZ]; exact hKids1⟩
      · rw [hCapZ] at hr
        have h0 := hInv.treeShape.live r _ (hNm1 r _ hr)
        cases h : st.objects[childId]? with
        | none => exact h0 h
        | some _ => rw [h] at hFresh; simp at hFresh
      · show (req.scrub st1 ut (req.carveIndex ut utCap.freeIndex)).objects[childId]? ≠ none
        rw [hObjZ]; exact hPres1
  rcases hBundle2 with ⟨⟨_, _, _, hDepth2, hObjInv2, hRCPV2⟩, -, -⟩
  have hObjFinal : ({ st2 with cdt := st2.cdt.addEdge src dst .retype }).objects = st2.objects := rfl
  exact capabilityInvariantBundle_of_linkReach
    ⟨cspaceLookupSound_holds _, hCdt.1, hCdt.2.1,
      cspaceDepthConsistent_of_objects_eq st2 _ hDepth2 hObjFinal, hObjFinal ▸ hObjInv2,
      replyCapPointsToValidReply_of_objects_eq hObjFinal hRCPV2⟩
    (SystemState.cdtAddChild_reach st2 src dst .retype) hObjInv2 hCdt.2.2 hShape

end SeLe4n.Kernel
