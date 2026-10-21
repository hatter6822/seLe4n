-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.Delete

/-!
AN4-F.3 (CAP-M03) child module extracted from
`SeLe4n.Kernel.Capability.Invariant.Preservation`. Contains compositional
preservation theorems for the transactional capability operations
`cspaceCopy`, `cspaceMove`, `cspaceMintWithCdt`, and `cspaceMutate`.
`cspaceMintWithCdt` lives here rather than in the sibling
`Preservation.Insert` child because it composes Copy-like CDT-expansion
semantics that group naturally with the Copy/Move/Mutate batch.
All declarations retain their original names, order, and proofs.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Internal

-- ============================================================================
-- WS-E4/C-02: Preservation theorems for new capability operations
-- ============================================================================

/-- A successful mint read its source and installed into its destination. -/
theorem cspaceMint_ok_decompose (src dst : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge) (st st1 : SystemState)
    (h : cspaceMint src dst rights badge st = .ok ((), st1)) :
    ∃ parent child, cspaceLookupSlot src st = .ok (parent, st) ∧
      cspaceInsertSlot dst child st = .ok ((), st1) := by
  unfold cspaceMint at h
  cases hL : cspaceLookupSlot src st with
  | error e => simp [hL] at h
  | ok pr =>
    obtain ⟨parent, stL⟩ := pr
    have hEq := cspaceLookupSlot_preserves_state st stL src parent hL; subst hEq
    simp only [hL] at h
    cases hNN : parent.toNonNull? with
    | none => simp [hNN] at h
    | some pNN =>
      simp only [hNN] at h
      cases hM : mintDerivedCap pNN rights badge with
      | error e => simp [hM] at h
      | ok child => simp only [hM] at h; exact ⟨parent, child, rfl, h⟩

/-- A successful reply-cap mint read its source and installed into its destination. -/
theorem mintReplyCap_ok_decompose (src dst : CSpaceAddr) (st st1 : SystemState)
    (h : mintReplyCap src dst st = .ok ((), st1)) :
    ∃ parent child, cspaceLookupSlot src st = .ok (parent, st) ∧
      cspaceInsertSlot dst child st = .ok ((), st1) := by
  unfold mintReplyCap at h
  cases hL : cspaceLookupSlot src st with
  | error e => simp [hL] at h
  | ok pr =>
    obtain ⟨parent, stL⟩ := pr
    have hEq := cspaceLookupSlot_preserves_state st stL src parent hL; subst hEq
    simp only [hL] at h
    split at h
    · split at h
      · exact ⟨parent, _, rfl, h⟩
      · cases h
    · cases h

/-- **A rewrite of one occupied slot that keeps its capability's target
preserves the capability bundle** — the shape of the mapping record `.vspaceMap`
writes and of a free-index write (WS-ZA ZA5.4), and of `cspaceMutate` with the
mutated field changed.  The slot is occupied, and that capability's target backs
the reply-cap conjunct. -/
theorem storeObject_capRewrite_preserves_capabilityInvariantBundle
    (st st' : SystemState) (addr : CSpaceAddr) (preCn : CNode) (cap cap' : Capability)
    (hInv : capabilityInvariantBundle st)
    (hPre : st.objects[addr.cnode]? = some (.cnode preCn))
    (hLk : preCn.lookup addr.slot = some cap) (hTgtEq : cap'.target = cap.target)
    (hStore : storeObject addr.cnode (.cnode (preCn.insert addr.slot cap')) st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hSound, hComp, hAcyclic, hDepthPre, hObjInv, hRCPV, hLinks⟩
  have hCompMid := cdtCompleteness_of_storeObject_cnode_mono st st' addr.cnode preCn _ hComp
                hObjInv hPre hStore fun s h => CNode.lookup_insert_ne_none preCn addr.slot s _ h
  have hAcyclicMid := cdtAcyclicity_of_cdt_eq st st' hAcyclic
    (storeObject_cdt_eq st st' addr.cnode _ hStore)
  have hDepthMid := cspaceDepthConsistent_of_storeObject_insertCNode
    st st' addr.cnode preCn addr.slot cap' hDepthPre hObjInv hPre hStore
  have hObjInvMid := storeObject_preserves_objects_invExt st st' addr.cnode _ hObjInv hStore
  refine ⟨cspaceLookupSound_holds st', hCompMid, hAcyclicMid, hDepthMid, hObjInvMid, ?_,
    cdtLinksAgree_of_eq hLinks (storeObject_cdt_eq st st' addr.cnode _ hStore)
      (SystemState.slotLinkAt_storeObject_cnode hObjInv hPre (CNode.insert_links ..) hStore)⟩
  -- The rewritten capability keeps its target, so the reply-cap-bearing slots are
  -- the pre-state's: the rewritten slot inherits its own pre-state backing, and
  -- every other slot frames through the single CNode store.
  have hSelf : st'.objects[addr.cnode]? =
      some (.cnode (preCn.insert addr.slot cap')) :=
    storeObject_objects_eq st st' addr.cnode _ hObjInv hStore
  have hNe : ∀ oid, oid ≠ addr.cnode → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st' addr.cnode oid _ h hObjInv hStore
  have hGetReply : ∀ rid : SeLe4n.ReplyId, st'.getReply? rid = st.getReply? rid := by
    intro rid
    simp only [SystemState.getReply?]
    by_cases hc : rid.toObjId = addr.cnode
    · rw [hc, hSelf, hPre]
    · rw [hNe rid.toObjId hc]
  intro oid cn slot cap'' rid hObj hLook hTgt
  rw [hGetReply]
  by_cases hc : oid = addr.cnode
  · subst hc
    rw [hSelf] at hObj
    simp only [Option.some.injEq] at hObj
    subst hObj
    simp only [KernelObject.slotCap] at hLook
    by_cases hs : slot = addr.slot
    · rw [hs] at hLook
      rw [CNode.lookup_insert_eq preCn addr.slot _ (CNode.slotsUnique_holds preCn)
        (CNode.slotAddressable_of_lookup_insert _ _ _ _ _ hLook)] at hLook
      simp only [Option.some.injEq] at hLook
      subst hLook
      exact hRCPV addr.cnode (.cnode preCn) addr.slot cap rid hPre hLk (hTgtEq ▸ hTgt)
    · rw [CNode.lookup_insert_ne preCn addr.slot slot _ (Ne.symm hs)
        (CNode.slotsUnique_holds preCn)] at hLook
      exact hRCPV addr.cnode (.cnode preCn) slot cap'' rid hPre hLook hTgt
  · rw [hNe oid hc] at hObj
    exact hRCPV oid cn slot cap'' rid hObj hLook hTgt

/-- WS-ZA ZA5.4: **a free-index write preserves the capability bundle** — an
in-place rewrite of one occupied slot that keeps its capability's target. -/
theorem setCapFreeIndex_preserves_capabilityInvariantBundle
    (st : SystemState) (addr : CSpaceAddr) (cn : CNode) (cap : Capability) (idx : Nat)
    (hInv : capabilityInvariantBundle st)
    (hPre : st.objects[addr.cnode]? = some (.cnode cn)) (hLk : cn.lookup addr.slot = some cap) :
    capabilityInvariantBundle (setCapFreeIndex st addr idx) := by
  have hS := setCapFreeIndex_eq_storeObject (idx := idx) hPre
  rw [CNode.setFreeIndex_of_lookup hLk] at hS
  exact storeObject_capRewrite_preserves_capabilityInvariantBundle st _ addr cn cap _ hInv hPre hLk
    (Capability.withFreeIndex_target _ _) hS

/-- WS-ZA ZA5.4: **setting a derivation's untyped source full preserves the
capability bundle**, given the source still holds the capability the derivation
read. -/
theorem untypedSourceSetFull_preserves_capabilityInvariantBundle
    (st : SystemState) (src : CSpaceAddr) (cn : CNode) (cap : Capability)
    (hInv : capabilityInvariantBundle st)
    (hPre : st.objects[src.cnode]? = some (.cnode cn)) (hLk : cn.lookup src.slot = some cap) :
    capabilityInvariantBundle (untypedSourceSetFull st src cap) :=
  untypedSourceSetFull_of (P := capabilityInvariantBundle) hInv
    fun idx => setCapFreeIndex_preserves_capabilityInvariantBundle st src cn cap idx hInv hPre hLk

/-- WS-E4/C-02: cspaceCopy preserves capabilityInvariantBundle.
Copy composes cspaceLookupSlot + cspaceInsertSlot, both of which preserve the bundle,
plus a CDT update that only touches the cdt field. -/
theorem cspaceCopy_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceCopy src dst st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  obtain ⟨cap, st2, hL, -, hInsert, -, rfl⟩ := cspaceCopy_ok_decompose hStep
  have hSrc : cspaceLookupSlot src st = .ok (cap, st) :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st src cap).2 hL
  have hBundleSt2 := cspaceInsertSlot_preserves_capabilityInvariantBundle st st2 dst cap.withoutMapping hInv
    (objects_invExt_of_capabilityInvariantBundle st hInv)
    (replyCapBacked_of_source_slot st src cap hInv hSrc) hInsert
  have hCdt := cdt_addEdge_after_insert st st2 src dst cap.withoutMapping .copy
    hInv.2.1 hInv.2.2.1 (objects_invExt_of_capabilityInvariantBundle st hInv)
    (by rw [hL]; rfl) hInsert hInv.linksAgree
  have hIX := objects_invExt_of_capabilityInvariantBundle _ hBundleSt2
  rcases hBundleSt2 with ⟨_, hComp2, _, hDepth2, hObjInv2, hRCPV2, -⟩
  have hObjFinal : ({ st2 with cdt := st2.cdt.addEdge src dst .copy }).objects = st2.objects := rfl
  -- The tree keeps its soundness because the new edge reaches an empty slot.
  have hMid : capabilityInvariantBundle (st2.cdtAddChild src dst .copy) := by
    refine capabilityInvariantBundle_of_linkReach ?_
      (SystemState.cdtAddChild_reach st2 src dst .copy) hIX hCdt.2.2
    exact ⟨cspaceLookupSound_holds _,
      hCdt.1, hCdt.2.1,
      cspaceDepthConsistent_of_objects_eq st2 _ hDepth2 hObjFinal,
      hObjFinal ▸ hObjInv2,
      replyCapPointsToValidReply_of_objects_eq hObjFinal hRCPV2⟩
  -- WS-ZA ZA5.4: the source still holds what the copy read; setting it full
  -- rewrites that slot in place.
  obtain ⟨cnS, hOS, hLS⟩ := cspaceInsertSlot_cdtAddChild_src .copy
    (objects_invExt_of_capabilityInvariantBundle st hInv) hL hInsert
  exact untypedSourceSetFull_preserves_capabilityInvariantBundle _ src cnS cap hMid hOS hLS

/-- WS-E4/C-02: cspaceMove preserves capabilityInvariantBundle.
Move composes lookup + insert + the core delete, then renames the source's tree
node to the destination (`moveNode`).  The destination was empty, so the tree did
not name it: the rename keeps the tree acyclic (`moveNode_edgeWellFounded`) and
takes the emptied source out of it (`moveNode_mentions`). -/
theorem cspaceMove_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceMove src dst st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceMove at hStep
  -- AK8-K (C-L1): self-move early-reject guard discharged first.
  by_cases hSelf : src = dst
  · simp [hSelf] at hStep
  simp [hSelf] at hStep
  cases hSrc : cspaceLookupSlot src st with
  | error e => simp [hSrc] at hStep
  | ok pair =>
      rcases pair with ⟨cap, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 src cap hSrc
      subst st1
      -- AL1b (AK7-I.cascade): promote cap via toNonNull?.
      have hNotNull : cap.isNull = false := by
        by_cases h : cap.isNull
        · exfalso; simp [Capability.toNonNull?, h, hSrc] at hStep
        · exact Bool.not_eq_true _ |>.mp h
      have hToNN : cap.toNonNull? = some ⟨cap, hNotNull⟩ :=
        Capability.toNonNull?_of_not_null hNotNull
      cases hInsert : cspaceInsertSlot dst cap st with
      | error e => simp [hSrc, hToNN, hInsert] at hStep
      | ok pair2 =>
          rcases pair2 with ⟨_, st2⟩
          cases hDelete : cspaceDeleteSlotCore src st2 with
          | error e => simp [hSrc, hToNN, hInsert, hDelete] at hStep
          | ok pair3 =>
              rcases pair3 with ⟨_, st3⟩
              have hBundleSt2 := cspaceInsertSlot_preserves_capabilityInvariantBundle st st2 dst cap hInv
                (objects_invExt_of_capabilityInvariantBundle st hInv)
                (replyCapBacked_of_source_slot st src cap hInv hSrc) hInsert
              have hBundleSt3 := cspaceDeleteSlotCore_preserves_capabilityInvariantBundleOff st2 st3 src
                hBundleSt2 hDelete
              obtain ⟨cnD, hGetD, hAddrD, hEmptyD, hStoreD⟩ :=
                cspaceInsertSlot_ok_decompose st st2 dst cap hInsert
              have hPreD : st.objects[dst.cnode]? = some (.cnode cnD) :=
                (SystemState.getCNode?_eq_some_iff _ _ _).mp hGetD
              have hCdt3 : st3.cdt = st.cdt :=
                (cspaceDeleteSlotCore_cdt_eq st2 st3 src hDelete).trans
                  (storeObject_cdt_eq st st2 _ _ hStoreD)
              have hFresh : ¬ st3.cdt.mentions dst := by
                rw [hCdt3]
                exact hInv.2.1.not_mentions_of_empty fun cn' h => by
                  rw [hPreD] at h; cases h; exact hEmptyD
              have hDst2 : ∃ cn, st2.objects[dst.cnode]? = some (.cnode cn) ∧
                  cn.lookup dst.slot ≠ none :=
                ⟨_, storeObject_objects_eq st st2 _ _
                    (objects_invExt_of_capabilityInvariantBundle st hInv) hStoreD,
                  by rw [CNode.lookup_insert_eq _ _ _ (CNode.slotsUnique_holds _) hAddrD]; simp⟩
              have hDst3 := cspaceDeleteSlotCore_keeps_other_slot st2 st3 src dst
                hBundleSt2.2.2.2.2.1 (Ne.symm hSelf) hDelete hDst2
              have hIX := hBundleSt3.2.2.2.2.1
              -- The insert and the delete write capabilities in place, so `src`
              -- (occupied before) and `dst` stay slots of their CNodes.
              have hSrcIn : st3.slotInObject src :=
                (cspaceDeleteSlotCore_links st2 st3 src hBundleSt2.2.2.2.2.1 hDelete).2 src |>.mpr
                  ((cspaceInsertSlot_links st st2 dst cap hInv.2.2.2.2.1 hInsert).2 src |>.mpr
                    (slotInObject_of_occupied (slotOccupied_of_cnode (slotOccupied_of_lookupSlotCap st src
                      (by rw [(cspaceLookupSlot_ok_iff_lookupSlotCap st src cap).1 hSrc]; rfl)))))
              have hLinks3 : cdtLinksAgree (st3.cdtMove src dst) :=
                SystemState.cdtMove_agree hIX hBundleSt3.2.2.2.2.2.2.1
                  hBundleSt3.2.2.2.2.2.2.2 hBundleSt3.2.2.1 hSrcIn
                  (slotInObject_of_occupied (slotOccupied_of_cnode hDst3)) hFresh hSelf
              rcases hBundleSt3 with ⟨_, hComp3, hAcyc3, hDepth3, hObjInv3, hRCPV3, -⟩
              simp [hSrc, hToNN, hInsert, hDelete] at hStep
              cases hStep
              have hObjEq : ({ st3 with cdt := st3.cdt.moveNode src dst }).objects = st3.objects := rfl
              refine capabilityInvariantBundle_of_linkReach ?_
                (SystemState.cdtMove_reach st3 src dst) hIX hLinks3
              exact ⟨cspaceLookupSound_holds _,
                fun ref hM => by
                  rcases CapDerivationTree.moveNode_mentions st3.cdt src dst hAcyc3 ref hM with
                    rfl | ⟨hNe, hM'⟩
                  · exact slotOccupied_of_cnode hDst3
                  · exact hComp3 ref hM' hNe,
                CapDerivationTree.moveNode_edgeWellFounded st3.cdt src dst hAcyc3 hFresh,
                cspaceDepthConsistent_of_objects_eq st3 _ hDepth3 hObjEq,
                hObjEq ▸ hObjInv3,
                replyCapPointsToValidReply_of_objects_eq hObjEq hRCPV3⟩

/-- WS-E4/C-03: cspaceMintWithCdt preserves capabilityInvariantBundle.
Composes cspaceMint (already proven) + CDT edge addition. -/
theorem cspaceMintWithCdt_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  obtain ⟨_, st1, hMint, hLP, -, rfl⟩ := cspaceMintWithCdt_ok_decompose hStep
  have hBundle := cspaceMint_preserves_capabilityInvariantBundle st st1 src dst rights badge hInv
    hMint
  obtain ⟨parent, child, hL, hI⟩ := cspaceMint_ok_decompose src dst rights badge st st1 hMint
  have hCdt := cdt_addEdge_after_insert st st1 src dst child .mint
    hInv.2.1 hInv.2.2.1 (objects_invExt_of_capabilityInvariantBundle st hInv)
    (by rw [(cspaceLookupSlot_ok_iff_lookupSlotCap st src parent).1 hL]; rfl) hI
    hInv.linksAgree
  have hIX := objects_invExt_of_capabilityInvariantBundle _ hBundle
  rcases hBundle with ⟨_, _, _, hDepth1, hObjInv1, hRCPV1, -⟩
  have hObjFinal : ({ st1 with cdt := st1.cdt.addEdge src dst .mint }).objects = st1.objects := rfl
  have hMid : capabilityInvariantBundle (st1.cdtAddChild src dst .mint) := by
    refine capabilityInvariantBundle_of_linkReach ?_
      (SystemState.cdtAddChild_reach st1 src dst .mint) hIX hCdt.2.2
    exact ⟨cspaceLookupSound_holds _,
      hCdt.1, hCdt.2.1,
      cspaceDepthConsistent_of_objects_eq st1 _ hDepth1 hObjFinal,
      hObjFinal ▸ hObjInv1, replyCapPointsToValidReply_of_objects_eq hObjFinal hRCPV1⟩
  obtain ⟨cnS, hOS, hLS⟩ := cspaceInsertSlot_cdtAddChild_src .mint
    (objects_invExt_of_capabilityInvariantBundle st hInv) hLP hI
  exact untypedSourceSetFull_preserves_capabilityInvariantBundle _ src cnS _ hMid hOS hLS

/-- WS-SM SM6.D / PR #822 Phase H: `mintReplyCapWithCdt` (the live `.mintReplyCap` dispatch
op) preserves `capabilityInvariantBundle`.  Mirrors `cspaceMintWithCdt_preserves_*`: the
reply-cap insert preserves the bundle (`mintReplyCap_preserves_*`), then the CDT mint-edge
addition only touches `cdt`, so the remaining conjuncts frame past `objects`, and the tree
stays complete and acyclic because the edge reaches the slot the insert found empty
(`cdt_addEdge_after_insert`), exactly as for `cspaceMintWithCdt`. -/
theorem mintReplyCapWithCdt_preserves_capabilityInvariantBundle
    (st st' : SystemState) (src dst : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : mintReplyCapWithCdt src dst st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold mintReplyCapWithCdt at hStep
  cases hMint : mintReplyCap src dst st with
  | error e => simp [hMint] at hStep
  | ok pair =>
      rcases pair with ⟨_, st1⟩
      have hBundle := mintReplyCap_preserves_capabilityInvariantBundle st st1 src dst hInv
        hMint
      obtain ⟨parent, child, hL, hI⟩ := mintReplyCap_ok_decompose src dst st st1 hMint
      have hCdt := cdt_addEdge_after_insert st st1 src dst child .mint
        hInv.2.1 hInv.2.2.1 (objects_invExt_of_capabilityInvariantBundle st hInv)
        (by rw [(cspaceLookupSlot_ok_iff_lookupSlotCap st src parent).1 hL]; rfl) hI
        hInv.linksAgree
      have hIX := objects_invExt_of_capabilityInvariantBundle _ hBundle
      rcases hBundle with ⟨_, _, _, hDepth1, hObjInv1, hRCPV1, -⟩
      simp [hMint] at hStep
      cases hStep
      have hObjFinal : ({ st1 with cdt := st1.cdt.addEdge src dst .mint }).objects = st1.objects := rfl
      refine capabilityInvariantBundle_of_linkReach ?_
        (SystemState.cdtAddChild_reach st1 src dst .mint) hIX hCdt.2.2
      exact ⟨cspaceLookupSound_holds _,
        hCdt.1, hCdt.2.1,
        cspaceDepthConsistent_of_objects_eq st1 _ hDepth1 hObjFinal,
        hObjFinal ▸ hObjInv1, replyCapPointsToValidReply_of_objects_eq hObjFinal hRCPV1⟩

-- ============================================================================
-- WS-F4/F-06: cspaceMutate preservation
-- ============================================================================

/-- WS-SM SM6.D / PR #822 Phase H (#1.a): `cspaceMutate` preserves `replyCapPointsToValidReply`.
Mutate overwrites the target slot with a cap carrying new rights/badge but the **same target**
(`{ cap with rights, badge }.target = cap.target` definitionally), so the set of reply-cap-bearing
slots is unchanged: the mutated slot inherits the pre-state slot's backing (via the read-only
`cspaceLookupSlot` that resolved `cap`) and every other slot frames through the single CNode store
(`getReply?` reads only `.reply` objects). -/
theorem cspaceMutate_preserves_replyCapPointsToValidReply
    (st st' : SystemState) (addr : CSpaceAddr) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (hRCPV : replyCapPointsToValidReply st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceMutate addr rights badge st = .ok ((), st')) :
    replyCapPointsToValidReply st' := by
  unfold cspaceMutate SystemState.getCNode? at hStep
  cases hLookup2 : cspaceLookupSlot addr st with
  | error e => simp [hLookup2] at hStep
  | ok pair =>
    rcases pair with ⟨cap, st1⟩
    have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr cap hLookup2; subst st1
    by_cases hNull : cap.isNull
    · simp [hLookup2, hNull] at hStep
    by_cases hRights : rightsSubset rights cap.rights
    · simp only [hLookup2, hNull, Bool.false_eq_true, ↓reduceIte, hRights] at hStep
      cases hPre : st.objects[addr.cnode]? with
      | none => simp_all
      | some preObj =>
        cases preObj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp_all
        | cnode preCn =>
          simp only [hPre] at hStep
          cases hStore : storeObject addr.cnode (.cnode (preCn.insert addr.slot
            ({ cap with rights := rights }.withBadge (badge.orElse (fun _ => cap.badge))))) st with
          | error e => simp_all
          | ok pair =>
            obtain ⟨_, stMid⟩ := pair
            simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hStep⟩ := hStep
            have hRefObj : st'.objects = stMid.objects := by rw [hStep]
            have hMidSelf : stMid.objects[addr.cnode]? = some (.cnode (preCn.insert addr.slot
                ({ cap with rights := rights }.withBadge (badge.orElse (fun _ => cap.badge))))) :=
              storeObject_objects_eq st stMid addr.cnode _ hObjInv hStore
            have hMidNe : ∀ oid, oid ≠ addr.cnode → stMid.objects[oid]? = st.objects[oid]? :=
              fun oid h => storeObject_objects_ne st stMid addr.cnode oid _ h hObjInv hStore
            have hGetReply : ∀ rid : SeLe4n.ReplyId, st'.getReply? rid = st.getReply? rid := by
              intro rid
              simp only [SystemState.getReply?, hRefObj]
              by_cases hc : rid.toObjId = addr.cnode
              · rw [hc, hMidSelf, hPre]
              · rw [hMidNe rid.toObjId hc]
            have hPreLook : preCn.lookup addr.slot = some cap := by
              have hLk := (cspaceLookupSlot_ok_iff_lookupSlotCap st addr cap).1 hLookup2
              rw [SystemState.lookupSlotCap,
                (SystemState.lookupCNode_eq_some_iff st addr.cnode preCn).2 hPre] at hLk
              exact hLk
            intro oid cn slot cap' rid hObj hLook hTgt
            rw [hGetReply]
            by_cases hc : oid = addr.cnode
            · subst hc
              rw [hRefObj, hMidSelf] at hObj
              simp only [Option.some.injEq] at hObj
              subst hObj
              simp only [KernelObject.slotCap] at hLook
              by_cases hs : slot = addr.slot
              · rw [hs] at hLook
                rw [CNode.lookup_insert_eq preCn addr.slot _ (CNode.slotsUnique_holds preCn)
                  (CNode.slotAddressable_of_lookup_insert _ _ _ _ _ hLook)] at hLook
                simp only [Option.some.injEq] at hLook
                subst hLook
                -- `{ cap with rights, badge }.target = cap.target` definitionally, so the
                -- mutated reply cap's backing is the pre-state slot's backing.
                exact hRCPV addr.cnode (.cnode preCn) addr.slot cap rid hPre hPreLook hTgt
              · rw [CNode.lookup_insert_ne preCn addr.slot slot _ (Ne.symm hs) (CNode.slotsUnique_holds preCn)] at hLook
                exact hRCPV addr.cnode (.cnode preCn) slot cap' rid hPre hLook hTgt
            · rw [hRefObj, hMidNe oid hc] at hObj
              exact hRCPV oid cn slot cap' rid hObj hLook hTgt
    · simp_all

/-- WS-F4/F-06: cspaceMutate preserves capabilityInvariantBundle.
Mutate composes cspaceLookupSlot (read-only) + cn.insert (which preserves
slotsUnique) + storeObject. -/
theorem cspaceMutate_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceMutate addr rights badge st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hSound, hComp, hAcyclic, hDepthPre, hObjInv, hRCPV, hLinks⟩
  -- WS-H4: cspaceMutate goes through storeObject(CNode.insert), same as insertSlot
  have ⟨hComp', hAcyclic', hDepth', hObjInv', hLinks'⟩ :
      cdtCompleteness st' ∧ cdtAcyclicity st' ∧
        cspaceDepthConsistent st' ∧ st'.objects.invExt ∧ cdtLinksAgree st' := by
    unfold cspaceMutate SystemState.getCNode? at hStep
    cases hLookup2 : cspaceLookupSlot addr st with
    | error e => simp [hLookup2] at hStep
    | ok pair =>
      rcases pair with ⟨cap, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr cap hLookup2; subst st1
      -- AK8-K (C-L2): null-cap guard discharged first.
      by_cases hNull : cap.isNull
      · simp [hLookup2, hNull] at hStep
      by_cases hRights : rightsSubset rights cap.rights
      · simp only [hLookup2, hNull, Bool.false_eq_true, ↓reduceIte, hRights] at hStep
        cases hPre : st.objects[addr.cnode]? with
        | none => simp_all
        | some preObj =>
          cases preObj with
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp_all
          | cnode preCn =>
            simp only [hPre] at hStep
            cases hStore : storeObject addr.cnode (.cnode (preCn.insert addr.slot
              ({ cap with rights := rights }.withBadge (badge.orElse (fun _ => cap.badge))))) st with
            | error e => simp_all
            | ok pair =>
              obtain ⟨_, stMid⟩ := pair
              simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hStep⟩ := hStep
              have hRefCdt : st'.cdt = stMid.cdt := by rw [hStep]
              have hRefObj : st'.objects = stMid.objects := by rw [hStep]
              have hCompMid := cdtCompleteness_of_storeObject_cnode_mono st stMid addr.cnode preCn _ hComp
                hObjInv hPre hStore fun s h => CNode.lookup_insert_ne_none preCn addr.slot s _ h
              have hAcyclicMid := cdtAcyclicity_of_cdt_eq st stMid hAcyclic
                (storeObject_cdt_eq st stMid addr.cnode _ hStore)
              have hDepthMid := cspaceDepthConsistent_of_storeObject_insertCNode
                st stMid addr.cnode preCn addr.slot
                ({ cap with rights := rights }.withBadge (badge.orElse (fun _ => cap.badge)))
                hDepthPre hObjInv hPre hStore
              have hObjInvMid := storeObject_preserves_objects_invExt st stMid addr.cnode _ hObjInv hStore
              exact ⟨cdtCompleteness_of_objects_cdt_eq stMid st' hCompMid hRefObj hRefCdt,
                cdtAcyclicity_of_cdt_eq stMid st' hAcyclicMid hRefCdt,
                cspaceDepthConsistent_of_objects_eq stMid st' hDepthMid hRefObj,
                hRefObj ▸ hObjInvMid,
                cdtLinksAgree_of_eq hLinks (hRefCdt.trans (storeObject_cdt_eq st stMid addr.cnode _ hStore))
                  ((SystemState.slotLinkAt_eq_of_objects fun o => by rw [hRefObj]).trans
                    (SystemState.slotLinkAt_storeObject_cnode hObjInv hPre (CNode.insert_links ..) hStore))⟩
      · simp_all
  exact ⟨cspaceLookupSound_holds st',
    hComp', hAcyclic', hDepth', hObjInv',
    cspaceMutate_preserves_replyCapPointsToValidReply st st' addr rights badge hRCPV hObjInv hStep,
    hLinks'⟩

-- ============================================================================
-- WS-BP BP7.1 (`v0.36.7`): the mapping record `.vspaceMap` writes
-- ============================================================================

/-- **WS-BP BP7.1 (`v0.36.7`): the mapping record preserves the capability
bundle.**  `cspaceRecordFrameMapping` is an in-place rewrite of one occupied slot
— the capability's `mapping` field set, its target, rights and badge kept. -/
theorem cspaceRecordFrameMapping_preserves_capabilityInvariantBundle
    (st st' : SystemState) (addr : CSpaceAddr) (m : FrameMapping)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRecordFrameMapping addr m st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  obtain ⟨preCn, cap, hCn, hLk, hStore⟩ := cspaceRecordFrameMapping_ok_decompose addr m st st' hStep
  exact storeObject_capRewrite_preserves_capabilityInvariantBundle st st' addr preCn cap
    (cap.withMapping (some m)) hInv
    ((SystemState.getCNode?_eq_some_iff st addr.cnode preCn).1 hCn) hLk rfl hStore

-- ============================================================================
-- WS-RC R4.D: `cspaceMutate` null-capability rejection — structural witnesses
-- ============================================================================

/-- WS-RC R4.D: every successful `cspaceMutate` outcome witnesses that the
    target slot held a non-null capability at the pre-state.

    The runtime guard at `Capability/Operations.lean:1093` rejects mutation of
    a slot that contains the `Capability.null` sentinel; this theorem codifies
    that guard at the proof system so a refactor that accidentally drops the
    `if cap.isNull then .error .nullCapability` branch is rejected by the
    Lean elaborator (the theorem fails to elaborate without that branch).

    Discharge recipe for callers reasoning about a successful mutation:
    obtain `hOk : cspaceMutate addr rights badge st = .ok ((), st')`, apply
    this theorem to recover the witness `cap` together with proofs that
    `cspaceLookupSlot addr st = .ok (cap, st)` and `cap.isNull = false`.

    Companion: `cspaceMutate_null_cap_rejected` proves the converse — every
    null-cap input produces the explicit `.nullCapability` error. -/
theorem cspaceMutate_rejects_null_cap
    (addr : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge) (st : SystemState) :
    ∀ st', cspaceMutate addr rights badge st = .ok ((), st') →
      ∃ cap, cspaceLookupSlot addr st = .ok (cap, st) ∧ cap.isNull = false := by
  intro st' hOk
  -- Extract a witness `cap` and the lookup equation via the `lookupSlotCap`
  -- bridge: `cspaceLookupSlot` succeeds iff `lookupSlotCap` returns `some _`,
  -- and the bridge avoids the `cases`-driven goal rewrite that would turn the
  -- target equation into a tautology.
  have hExists : ∃ cap, SystemState.lookupSlotCap st addr = some cap := by
    unfold cspaceMutate SystemState.getCNode? at hOk
    cases hL : cspaceLookupSlot addr st with
    | error e => rw [hL] at hOk; simp at hOk
    | ok pair =>
        rcases pair with ⟨cap, st1⟩
        have : SystemState.lookupSlotCap st addr = some cap := by
          unfold cspaceLookupSlot at hL
          cases hLook : SystemState.lookupSlotCap st addr with
          | none =>
              cases hCN : st.getCNode? addr.cnode with
              | none => simp [hLook, hCN] at hL
              | some _ => simp [hLook, hCN] at hL
          | some cap' =>
              simp [hLook] at hL; rcases hL with ⟨hCap, _⟩; subst hCap; rfl
        exact ⟨cap, this⟩
  obtain ⟨cap, hLook⟩ := hExists
  have hLkp : cspaceLookupSlot addr st = .ok (cap, st) :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st addr cap).2 hLook
  refine ⟨cap, hLkp, ?_⟩
  -- Now derive non-nullness from `hOk` using `hLkp`.
  unfold cspaceMutate SystemState.getCNode? at hOk
  rw [hLkp] at hOk
  simp only at hOk
  by_cases hNull : cap.isNull
  · simp [hNull] at hOk
  · exact Bool.not_eq_true _ |>.mp hNull

/-- WS-RC R4.D: complement to `cspaceMutate_rejects_null_cap`.

    Whenever the lookup at the pre-state returns a null capability, the
    mutation totalises to the `.nullCapability` error code — independent of
    the requested rights or badge. This proves the rejection is total: every
    null-cap input produces the explicit error code rather than a generic
    `.invalidCapability` (which would mask the guard's intent) or silent
    success (which would corrupt the slot).

    Together with `cspaceMutate_rejects_null_cap`, the runtime check at
    `Capability/Operations.lean:1093` is now witnessed by the proof surface;
    a future audit's `grep` for the validation can be re-derived from these
    theorem names without re-reading the function body. -/
theorem cspaceMutate_null_cap_rejected
    (addr : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge) (st : SystemState)
    (hCap : ∃ cap, cspaceLookupSlot addr st = .ok (cap, st) ∧ cap.isNull = true) :
    cspaceMutate addr rights badge st = .error .nullCapability := by
  obtain ⟨cap, hLkp, hNull⟩ := hCap
  unfold cspaceMutate SystemState.getCNode?
  rw [hLkp]
  simp [hNull]


end SeLe4n.Kernel
