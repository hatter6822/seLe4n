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
copy into an empty CNode slot does (`cdt_addEdge_after_insert`).  Each source
names a CNode or a VSpace root (`copyThreadSpaces`'s checks), never an untyped, so
the copy owes the untyped chain nothing and the source is not left off (b)
(`TreeShapeOver.unoff_of_not_untyped`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- A capability a slot holds in a state satisfying the bundle is reply-backed. -/
theorem replyCapBacked_of_lookupSlotCap {st : SystemState} {src : SlotRef} {cap : Capability}
    (hInv : capabilityInvariantBundle st) (h : SystemState.lookupSlotCap st src = some cap) :
    ∀ rid, cap.target = .replyCap rid → st.getReply? rid ≠ none :=
  replyCapBacked_of_source_slot st src cap hInv
    ((cspaceLookupSlot_ok_iff_lookupSlotCap st src cap).2 h)

/-- One key's untyped record is kept by a write that keeps the key's object up
to links: an untyped holds no link. -/
theorem untyped?_of_agreeAt {st st' : SystemState} {k : SeLe4n.ObjId}
    (h : SystemState.objectAgreesOffDerivationLinksAt st' st k) :
    st'.getUntyped? k = st.getUntyped? k := by
  rw [SystemState.getUntyped?_eq_bind, SystemState.getUntyped?_eq_bind]
  have hB : ∀ x : Option KernelObject,
      x.bind KernelObject.untyped? = (x.map KernelObject.withoutLinks).bind KernelObject.untyped? := by
    intro x; cases x <;> simp
  rw [hB, h.map_withoutLinks, ← hB]

/-- **A thread slot's delete keeps every untyped record**: it stores a thread
over a thread and writes links. -/
theorem threadSlotDeleted_getUntyped? {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot) :
    (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
      { cnode := tid.toObjId, slot := slot }).getUntyped? = st.getUntyped? := by
  have hPre : st.objects[tid.toObjId]? = some (.tcb t) :=
    (SystemState.getTcb?_eq_some_iff st tid t).mp hT
  have hS := threadSlotCleared_store hT slot
  have hInvC := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS
  exact (spliceDeletedCdtNode_agree hInvC _).1.getUntyped?.trans
    (SystemState.getUntyped?_storeObject hObjInv hS (by rw [hPre]; rfl))

/-- **A thread slot's copy keeps every untyped record**: off the thread it keeps
each object up to links, and the thread is a thread before and after. -/
theorem threadSlotCopied_getUntyped? {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    (threadSlotCopied st tid slot srcCNode srcSlot rights).getUntyped? = st.getUntyped? := by
  obtain ⟨hFar, t', hT', -⟩ := threadSlotCopied_frame hObjInv hT slot srcCNode srcSlot rights
  funext k
  by_cases h : k = tid.toObjId
  · rw [SystemState.getUntyped?_eq_bind, SystemState.getUntyped?_eq_bind, h,
      (SystemState.getTcb?_eq_some_iff _ tid t').mp hT',
      (SystemState.getTcb?_eq_some_iff st tid t).mp hT]; rfl
  · exact untyped?_of_agreeAt (hFar k h)

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
    (hBacked : ∀ rid, c.target = .replyCap rid → st.getReply? rid ≠ none)
    (hTgt : c.target = cap.target)
    (hNotUt : ∀ u, cap.target = .object u → st.getUntyped? u = none) :
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
  have hUt1 : (st.updateTcb tid (·.insertSpaceCap slot c)).getUntyped? = st.getUntyped? := by
    funext k
    rw [SystemState.getUntyped?_eq_bind, SystemState.getUntyped?_eq_bind]
    by_cases h : k = tid.toObjId
    · rw [h, hAt, hPre]; rfl
    · rw [hNe _ (Ne.symm h)]
  have hObjInv1 := SystemState.updateTcb_preserves_objects_invExt st tid
    (·.insertSpaceCap slot c) hObjInv
  generalize st.updateTcb tid (·.insertSpaceCap slot c) = st1 at hAt hNe hCdt1 hObjInv1 hUt1 ⊢
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
    have hSrcSlot := SystemState.slotCapAt_of_lookupSlotCap hSrc
    have hSrcNotUt : ∀ u, ¬ SystemState.untypedCapAt st.slotCapAt st.getUntyped? src u :=
      fun u ⟨c', hc', ht', hu'⟩ => by
        rw [hSrcSlot] at hc'; cases hc'; exact hu' (hNotUt u ht')
    have hS1 : ∀ r, r ≠ { cnode := tid.toObjId, slot := slot } →
        st1.slotCapAt r = st.slotCapAt r := by
      intro r hr
      rw [SystemState.slotCapAt_eq_bind, SystemState.slotCapAt_eq_bind]
      by_cases h : r.cnode = tid.toObjId
      · rw [h, hAt, hPre]
        have hrs : r.slot ≠ slot := fun e => hr (by cases r; simp_all)
        show (t.insertSpaceCap slot c).spaceSlotCap r.slot = t.spaceSlotCap r.slot
        rw [TCB.spaceSlotCap_insertSpaceCap t hs, if_neg hrs]
      · rw [hNe _ (Ne.symm h)]
    show SystemState.TreeShapeOver _ _ _ st1.getUntyped? _
    rw [hUt1]
    refine SystemState.TreeShapeOver.unoff_of_not_untyped (a := src) ?_
      fun u ⟨c', hc', ht', hu'⟩ => hSrcNotUt u ⟨c', (hS1 src hNeSD).symm.trans hc', ht', hu'⟩
    refine hShape.addChild .copy (slotCapAt_ne_none_of_lookupSlotCap (by rw [hSrc]; rfl)) hDstFresh
      (by show st1.cdt.addEdge _ _ _ = _; rw [hCdt1]) (fun r hr => hS1 r hr) (fun o hp => ?_)
      (.inl ⟨fun o => ?_, fun u => ?_, fun u hu => (hSrcNotUt u hu).elim⟩)
    · show st1.objects[o]? ≠ none
      by_cases h : o = tid.toObjId
      · rw [h, hAt]; exact Option.some_ne_none _
      · rw [hNe _ (Ne.symm h)]; exact hp
    all_goals have hDst : st1.slotCapAt { cnode := tid.toObjId, slot := slot } = some c := by
                rw [SystemState.slotCapAt_of_object hAt]
                show (t.insertSpaceCap slot c).spaceSlotCap slot = some c
                rw [TCB.spaceSlotCap_insertSpaceCap t hs]; simp
    · show SystemState.namesAt st1.slotCapAt _ o ↔ _
      unfold SystemState.namesAt; rw [hDst, hSrcSlot]; simp [Capability.namedObject_of_target hTgt]
    · exact SystemState.untypedCapAt_of_target hSrcSlot hDst hTgt
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
    (rights : AccessRightSet)
    (hSrcNotUt : ∀ cap, SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } =
      some cap → ∀ u, cap.target = .object u → st.getUntyped? u = none) :
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
      (TCB.spaceCopyOf_target _ _) ?_
    rotate_left
    · intro u hu
      rw [threadSlotDeleted_getUntyped? hObjInv hT slot]
      exact hSrcNotUt cap (by rw [← threadSlotDeleted_lookupSlotCap hObjInv hT slot]; exact hCap) u hu
    intro rid hTg
    exact replyCapBacked_of_lookupSlotCap hD hCap rid (by simpa using hTg)

/-- A CNode slot lookup is the slot's capability. -/
theorem slotCapAt_of_lookupSlotCap {st : SystemState} {r : SlotRef} {cap : Capability}
    (h : SystemState.lookupSlotCap st r = some cap) :
    st.slotCapAt r = some cap ∧ ∃ cn, st.objects[r.cnode]? = some (.cnode cn) := by
  unfold SystemState.lookupSlotCap SystemState.lookupCNode at h
  cases hO : st.objects[r.cnode]? with
  | none => rw [hO] at h; cases h
  | some o =>
    cases o with
    | cnode cn =>
      rw [hO] at h
      exact ⟨by rw [SystemState.slotCapAt_of_object hO]; exact h, cn, rfl⟩
    | _ => rw [hO] at h; cases h

/-- **A thread space slot's set keeps the capability bundle**: the copy keeps it
(`threadSlotCopied_preserves_capabilityInvariantBundle`), and the retire of what
the old capability was the last capability to keeps it
(`retireFinalObject_preserves_capabilityInvariantBundle`): after the copy no
slot names that object — every other slot holds what it held, and the copy
names what its source names, a different slot that the old capability's
finality says does not name it — and the recorder word, read before, still
answers truly, as the copy keeps every untyped record. -/
theorem threadSlotSet_preserves_capabilityInvariantBundle (ec : Concurrency.CoreId)
    {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB} {slot : SeLe4n.Slot}
    (hInv : capabilityInvariantBundle st) (hT : st.getTcb? tid = some t)
    (hs : slot.toNat < 2) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet)
    (hSrcNotUt : ∀ cap, SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } =
      some cap → ∀ u, cap.target = .object u → st.getUntyped? u = none) :
    capabilityInvariantBundle (threadSlotSet ec st tid slot srcCNode srcSlot rights) := by
  have hObjInv := objects_invExt_of_capabilityInvariantBundle st hInv
  have h1 := threadSlotCopied_preserves_capabilityInvariantBundle hInv hT hs srcCNode srcSlot
    rights hSrcNotUt
  unfold threadSlotSet
  dsimp only
  refine retireFinalObject_preserves_capabilityInvariantBundle ec _ _ _ h1
    (fun hT0 r hr => ?_) (fun hT0 => ?_)
  · obtain ⟨c, hc, hn, hFin⟩ := slotRetireTarget_spec hInv hT0
    have hAddr : SystemState.namesAt st.slotCapAt ⟨tid.toObjId, slot⟩
        (SeLe4n.ObjId.ofNat (slotRetireTarget st tid.toObjId slot - 1)) := ⟨c, hc, hn⟩
    obtain ⟨c', hc', hn'⟩ := hr
    rw [threadSlotCopied_slotCapAt hObjInv hT hs] at hc'
    split at hc'
    · next hk =>
      cases hL : SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } with
      | none => rw [hL] at hc'; cases hc'
      | some cap =>
        rw [hL] at hc'
        simp only [Option.map_some, Option.some.injEq] at hc'
        subst hc'
        obtain ⟨hSrc, cn, hCn⟩ := slotCapAt_of_lookupSlotCap hL
        have hne : ({ cnode := srcCNode, slot := srcSlot } : SlotRef) ≠ ⟨tid.toObjId, slot⟩ := by
          intro e
          have : srcCNode = tid.toObjId := congrArg SlotRef.cnode e
          rw [this, (SystemState.getTcb?_eq_some_iff st tid t).mp hT] at hCn; cases hCn
        exact hFin _ hAddr _ hne ⟨cap, hSrc, by
          unfold Capability.namedObject at hn' ⊢; rw [TCB.spaceCopyOf_target] at hn'; exact hn'⟩
    · next hk =>
      have hne : r ≠ ⟨tid.toObjId, slot⟩ := by
        intro e; subst e; exact hk ⟨rfl, rfl⟩
      exact hFin _ hAddr r hne ⟨c', hc', hn'⟩
  · have hU := threadSlotCopied_getUntyped? hObjInv hT slot srcCNode srcSlot rights
    obtain ⟨hS1, hS0⟩ := recorderWord_spec st
      (SeLe4n.ObjId.ofNat (slotRetireTarget st tid.toObjId slot - 1)) tid.toObjId slot
      hInv.2.2.2.2.1
    unfold recorderFor
    rw [if_neg hT0]
    refine ⟨fun hne => ?_, fun h0 w => ?_⟩
    · rw [untypedRecordsChild_congr hU]; exact hS1 hne
    · rw [untypedRecordsChild_congr hU]; exact hS0 h0 w

/-- **Setting a thread's space keeps the capability bundle**: each of its two
slot sets does (`threadSlotSet_preserves_capabilityInvariantBundle`). -/
theorem copyThreadSpaces_preserves_capabilityInvariantBundle (ec : Concurrency.CoreId)
    {st st' : SystemState} {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr}
    (hInv : capabilityInvariantBundle st)
    (hStep : copyThreadSpaces ec st vtid cnSrc vrSrc = .ok st') :
    capabilityInvariantBundle st' := by
  obtain ⟨tcb, hT, -, -, hCn, hVr, rfl⟩ := copyThreadSpaces_ok hStep
  have hObjInv := objects_invExt_of_capabilityInvariantBundle st hInv
  -- A source naming a CNode or a VSpace root names no untyped.
  have hNotUt : ∀ {src : CSpaceAddr} {p : SeLe4n.ObjId → Prop},
      (∃ cap id, SystemState.lookupSlotCap st src = some cap ∧ cap.target = .object id ∧ p id) →
      (∀ id, p id → st.getUntyped? id = none) →
      ∀ cap, SystemState.lookupSlotCap st { cnode := src.cnode, slot := src.slot } = some cap →
        ∀ u, cap.target = .object u → st.getUntyped? u = none := by
    intro src p ⟨cap, id, hL, hTg, hp⟩ hK cap' hL' u hu
    have hcc : cap' = cap := Option.some.inj (hL'.symm.trans hL)
    subst hcc
    rw [hTg] at hu; cases hu; exact hK _ hp
  have hCnNot := hNotUt (cspaceRootSourceAdmitted_spec hCn) fun id h => by
    unfold SystemState.getCNode? at h; unfold SystemState.getUntyped?
    split at h <;> simp_all
  have hVrNot := hNotUt (vspaceRootSourceAdmitted_spec hVr) fun id h => by
    unfold SystemState.getVSpaceRoot? at h; unfold SystemState.getUntyped?
    split at h <;> simp_all
  have h1 := threadSlotSet_preserves_capabilityInvariantBundle ec hInv hT (by decide)
    cnSrc.cnode cnSrc.slot TCB.cspaceRootRights (slot := TCB.cspaceRootSlot) hCnNot
  obtain ⟨hT1, hI1⟩ := threadSlotCopied_tcb hObjInv hT TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
    TCB.cspaceRootRights
  obtain ⟨cnCap, -, hCL, -⟩ := cspaceRootSourceAdmitted_spec hCn
  obtain ⟨t1, hT1', hF1⟩ := threadSlotCopied_slotFilled hObjInv hT (slot := TCB.cspaceRootSlot)
    (by decide) TCB.cspaceRootRights (srcCNode := cnSrc.cnode) (srcSlot := cnSrc.slot) hCL
  unfold copyThreadSpacesPerform
  refine threadSlotSet_preserves_capabilityInvariantBundle ec h1
    (by unfold threadSlotSet; dsimp only
        exact retireFinalObject_getTcb?_of_slotCap _ _ _ _ hI1 hT1' hF1)
    (by decide) vrSrc.cnode vrSrc.slot TCB.vspaceRootRights fun cap hL u hu => ?_
  unfold threadSlotSet at hL ⊢
  dsimp only at hL ⊢
  rw [retireFinalObject_lookupSlotCap _ _ _ _ hI1, threadSlotCopied_lookupSlotCap hObjInv hT] at hL
  refine retireFinalObject_getUntyped?_none _ _ _ _ hI1 ?_
  rw [threadSlotCopied_getUntyped? hObjInv hT]
  exact hVrNot cap hL u hu

end SeLe4n.Kernel
