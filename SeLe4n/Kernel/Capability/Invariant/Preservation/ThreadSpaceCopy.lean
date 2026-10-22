-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.Revoke
import SeLe4n.Kernel.Lifecycle.Operations.SetSpace

/-!
The capability bundle across setting a thread's space (`copyThreadSpaces`).
Each space slot's old content is deleted as a CNode slot's is
(`cspaceDeleteSlot`, which keeps the bundle), and the copy put in its place is
recorded as a child of its source slot.  The delete emptied the slot, so the tree
does not name it: the new edge reaches a fresh node and closes no cycle, as a
copy into an empty CNode slot does (`cdt_addEdge_after_insert`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- A capability a slot holds in a state satisfying the bundle is reply-backed. -/
theorem replyCapBacked_of_lookupSlotCap {st : SystemState} {src : SlotRef} {cap : Capability}
    (hInv : capabilityInvariantBundle st) (h : SystemState.lookupSlotCap st src = some cap) :
    ∀ rid, cap.target = .replyCap rid → st.getReply? rid ≠ none :=
  replyCapBacked_of_source_slot st src cap hInv
    ((cspaceLookupSlot_ok_iff_lookupSlotCap st src cap).2 h)

/-- **Filling an empty thread space slot and recording its derivation keeps the
capability bundle.**  The slot was empty, so the tree did not name it
(`cdtCompleteness`); the source is a CNode slot holding a capability, so it is a
different slot.  The fill keeps every link word and every CNode, and the copy is
reply-backed when its target is a reply. -/
theorem threadSlotFilled_preserves_capabilityInvariantBundle
    {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB} {slot : SeLe4n.Slot}
    {src : SlotRef} {cap c : Capability}
    (hInv : capabilityInvariantBundle st) (hT : st.getTcb? tid = some t)
    (hs : slot.toNat < 2) (hEmpty : t.spaceSlotCap slot = none)
    (hSrc : SystemState.lookupSlotCap st src = some cap)
    (hBacked : ∀ rid, c.target = .replyCap rid → st.getReply? rid ≠ none) :
    capabilityInvariantBundle
      ((st.updateTcb tid (·.insertSpaceCap slot c)).cdtAddChild src
        { cnode := tid.toObjId, slot := slot } .copy) := by
  rcases hInv with ⟨_, hComp, hAcyc, hDepth, hObjInv, hRCPV, hLinks, hShape⟩
  have hPre : st.objects[tid.toObjId]? = some (.tcb t) :=
    (SystemState.getTcb?_eq_some_iff st tid t).mp hT
  have hAt : (st.updateTcb tid (·.insertSpaceCap slot c)).objects[tid.toObjId]? =
      some (.tcb (t.insertSpaceCap slot c)) := by
    rw [SystemState.updateTcb_eq_of_some hT]
    exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv
  have hNe : ∀ k, tid.toObjId ≠ k →
      (st.updateTcb tid (·.insertSpaceCap slot c)).objects[k]? = st.objects[k]? :=
    fun k h => SystemState.updateTcb_objects_ne st tid _ k h hObjInv
  have hCdt1 := SystemState.updateTcb_cdt st tid (·.insertSpaceCap slot c)
  have hObjInv1 := SystemState.updateTcb_preserves_objects_invExt st tid
    (·.insertSpaceCap slot c) hObjInv
  generalize st.updateTcb tid (·.insertSpaceCap slot c) = st1 at hAt hNe hCdt1 hObjInv1 ⊢
  have hDstFresh : ¬ st.cdt.mentions { cnode := tid.toObjId, slot := slot } :=
    hComp.not_mentions_of_empty fun o hO => by rw [hPre] at hO; cases hO; exact hEmpty
  obtain ⟨cs, hCs, hLs⟩ := slotOccupied_of_lookupSlotCap st src (by rw [hSrc]; rfl)
  have hSrcCn : src.cnode ≠ tid.toObjId := by
    intro h; rw [h, hPre] at hCs; simp at hCs
  have hNeSD : src ≠ { cnode := tid.toObjId, slot := slot } := fun h => hSrcCn (by rw [h])
  have hSrcPost : ∃ o, st1.objects[src.cnode]? = some o ∧ o.slotCap src.slot ≠ none :=
    ⟨.cnode cs, by rw [hNe _ (Ne.symm hSrcCn)]; exact hCs, hLs⟩
  have hDstOcc : ∃ o, st1.objects[tid.toObjId]? = some o ∧ o.slotCap slot ≠ none :=
    ⟨_, hAt, by
      show (t.insertSpaceCap slot c).spaceSlotCap slot ≠ none
      rw [TCB.spaceSlotCap_insertSpaceCap t hs]; simp⟩
  have hComp1 : cdtCompleteness st1 := by
    intro ref hM
    rw [hCdt1] at hM
    by_cases h : ref.cnode = tid.toObjId
    · obtain ⟨o, hO, hL⟩ := hComp ref hM
      rw [h, hPre] at hO; cases hO
      exact ⟨.tcb (t.insertSpaceCap slot c), by rw [h]; exact hAt,
        TCB.spaceSlotCap_insertSpaceCap_mono t hs c _ hL⟩
    · rw [hNe _ (Ne.symm h)]; exact hComp ref hM
  have hDepth1 : cspaceDepthConsistent st1 := by
    intro k cn hO
    by_cases h : k = tid.toObjId
    · rw [h, hAt] at hO; cases hO
    · rw [hNe _ (Ne.symm h)] at hO; exact hDepth k cn hO
  have hReply : ∀ rid : SeLe4n.ReplyId, st1.getReply? rid = st.getReply? rid := by
    intro rid
    unfold SystemState.getReply?
    by_cases h : rid.toObjId = tid.toObjId
    · rw [h, hAt, hPre]
    · rw [hNe _ (Ne.symm h)]
  have hRCPV1 : replyCapPointsToValidReply st1 := by
    intro oid o s cap' rid hO hL hTg
    rw [hReply]
    by_cases h : oid = tid.toObjId
    · rw [h, hAt] at hO; cases hO
      rcases TCB.spaceSlotCap_insertSpaceCap_back hL with rfl | hL'
      · exact hBacked rid hTg
      · exact hRCPV tid.toObjId (.tcb t) s cap' rid hPre hL' hTg
    · rw [hNe _ (Ne.symm h)] at hO; exact hRCPV oid o s cap' rid hO hL hTg
  have hL1 : st1.slotLinkAt = st.slotLinkAt := by
    refine SystemState.slotLinkAt_eq_of_links fun k => ?_
    by_cases h : k = tid.toObjId
    · rw [h, hAt, hPre]; rfl
    · rw [hNe _ (Ne.symm h)]
  have hLinks1 : cdtLinksAgree st1 := cdtLinksAgree_of_eq hLinks hCdt1 hL1
  have hAcyc1 : st1.cdt.edgeWellFounded := by
    unfold cdtAcyclicity at hAcyc; rw [hCdt1]; exact hAcyc
  have hShape1 : SystemState.CapTreeShape
      { st1 with cdt := st1.cdt.addEdge src { cnode := tid.toObjId, slot := slot } .copy } := by
    refine hShape.addChild .copy (slotCapAt_ne_none_of_lookupSlotCap (by rw [hSrc]; rfl)) hDstFresh
      (by show st1.cdt.addEdge _ _ _ = _; rw [hCdt1]) fun r hr => ?_
    show st1.slotCapAt r = st.slotCapAt r
    rw [SystemState.slotCapAt_eq_bind, SystemState.slotCapAt_eq_bind]
    by_cases h : r.cnode = tid.toObjId
    · rw [h, hAt, hPre]
      have hrs : r.slot ≠ slot := fun e => hr (by cases r; simp_all)
      show (t.insertSpaceCap slot c).spaceSlotCap r.slot = t.spaceSlotCap r.slot
      rw [TCB.spaceSlotCap_insertSpaceCap t hs, if_neg hrs]
    · rw [hNe _ (Ne.symm h)]
  refine capabilityInvariantBundle_of_linkReach ?_
    (SystemState.cdtAddChild_reach st1 src _ .copy) hObjInv1 ?_ hShape1
  · refine ⟨cspaceLookupSound_holds _, fun ref hM => ?_, ?_,
      cspaceDepthConsistent_of_objects_eq st1 _ hDepth1 rfl, hObjInv1,
      replyCapPointsToValidReply_of_objects_eq rfl hRCPV1⟩
    · rcases hM with ⟨e, he, hr⟩ | hr
      · simp only [CapDerivationTree.addEdge_edges, List.mem_cons] at he
        rcases he with rfl | he
        · rcases hr with h | h <;> simp only at h <;> subst h
          · exact hSrcPost
          · exact hDstOcc
        · exact hComp1 ref (.inl ⟨e, he, hr⟩)
      · exact hComp1 ref (.inr hr)
    · exact CapDerivationTree.addEdge_preserves_edgeWellFounded_fresh st1.cdt src _ .copy hNeSD
        hAcyc1 fun e he => ⟨fun h => hDstFresh (.inl ⟨e, hCdt1 ▸ he, Or.inl h⟩),
          fun h => hDstFresh (.inl ⟨e, hCdt1 ▸ he, Or.inr h⟩)⟩
  · exact SystemState.cdtAddChild_agree hObjInv1 hLinks1
      (fun _ hM => slotInObject_of_occupied (hComp1 _ hM)) .copy
      (slotInObject_of_occupied hSrcPost) (slotInObject_of_occupied hDstOcc)
      (by rw [hCdt1]; exact hDstFresh) hNeSD

/-- **A thread space slot's copy keeps the capability bundle**: its delete is the
slot delete (`copyIntoThreadSlot_delete`), which keeps the bundle and leaves the
slot empty, and the fill and edge keep it
(`threadSlotFilled_preserves_capabilityInvariantBundle`). -/
theorem threadSlotCopied_preserves_capabilityInvariantBundle
    {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB} {slot : SeLe4n.Slot}
    (hInv : capabilityInvariantBundle st) (hT : st.getTcb? tid = some t)
    (hs : slot.toNat < 2) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) :
    capabilityInvariantBundle (threadSlotCopied st tid slot srcCNode srcSlot rights) := by
  have hObjInv := objects_invExt_of_capabilityInvariantBundle st hInv
  have hD := cspaceDeleteSlot_preserves_capabilityInvariantBundle st _ _ hInv
    (copyIntoThreadSlot_delete hT slot)
  obtain ⟨⟨t', hT', hW⟩, -⟩ := threadSlotDeleted_tcb hObjInv hT slot
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights with ⟨-, e⟩ | ⟨cap, hCap, e⟩
  · rw [e]; exact hD
  · rw [e]
    have hCells : t'.spaceCells = (t.removeSpaceCap slot).spaceCells := by
      simpa only [TCB.withoutLinks_spaceCells] using congrArg TCB.spaceCells hW
    have hEmpty : t'.spaceSlotCap slot = none := by
      have h := TCB.spaceSlotCap_removeSpaceCap t slot slot
      simp only [if_true] at h
      rw [← h]; unfold TCB.spaceSlotCap; rw [hCells]
    refine threadSlotFilled_preserves_capabilityInvariantBundle hD hT' hs hEmpty hCap ?_
    intro rid hTg
    exact replyCapBacked_of_lookupSlotCap hD hCap rid (by simpa using hTg)

/-- **Setting a thread's space keeps the capability bundle**: each of its two
slot copies does (`threadSlotCopied_preserves_capabilityInvariantBundle`). -/
theorem copyThreadSpaces_preserves_capabilityInvariantBundle
    {st st' : SystemState} {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr}
    (hInv : capabilityInvariantBundle st)
    (hStep : copyThreadSpaces st vtid cnSrc vrSrc = .ok st') :
    capabilityInvariantBundle st' := by
  obtain ⟨tcb, hT, -, -, -, -, rfl⟩ := copyThreadSpaces_ok hStep
  have hObjInv := objects_invExt_of_capabilityInvariantBundle st hInv
  have h1 := threadSlotCopied_preserves_capabilityInvariantBundle hInv hT (by decide)
    cnSrc.cnode cnSrc.slot TCB.cspaceRootRights (slot := TCB.cspaceRootSlot)
  obtain ⟨hT1, -⟩ := threadSlotCopied_tcb hObjInv hT TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
    TCB.cspaceRootRights
  obtain ⟨t1, hT1'⟩ := Option.isSome_iff_exists.mp hT1
  exact threadSlotCopied_preserves_capabilityInvariantBundle h1 hT1' (by decide)
    vrSrc.cnode vrSrc.slot TCB.vspaceRootRights

end SeLe4n.Kernel
