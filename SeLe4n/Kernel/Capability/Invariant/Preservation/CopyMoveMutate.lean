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

/-- WS-E4/C-02: cspaceCopy preserves capabilityInvariantBundle.
Copy composes cspaceLookupSlot + cspaceInsertSlot, both of which preserve the bundle,
plus a CDT update that only touches the cdt field. -/
theorem cspaceCopy_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hDstCapacity : ∀ cn cap, st.objects[dst.cnode]? = some (.cnode cn) →
      (cn.insert dst.slot cap).slotCountBounded)
    (hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st')
    (hStep : cspaceCopy src dst st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceCopy at hStep
  cases hSrc : cspaceLookupSlot src st with
  | error e => simp [hSrc] at hStep
  | ok pair =>
      rcases pair with ⟨cap, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 src cap hSrc
      subst st1
      -- AL1b (AK7-I.cascade): promote cap via toNonNull?; .ok forces non-null.
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
          have hBundleSt2 := cspaceInsertSlot_preserves_capabilityInvariantBundle st st2 dst cap hInv
            (fun cn hObj => hDstCapacity cn cap hObj)
            (objects_invExt_of_capabilityInvariantBundle st hInv) hInsert
          rcases hBundleSt2 with ⟨hU2, _, hBnd2, hComp2, _, hDepth2, hObjInv2⟩
          cases hEnsSrc : SystemState.ensureCdtNodeForSlot st2 src with
          | mk srcNode stSrc =>
              cases hEnsDst : SystemState.ensureCdtNodeForSlot stSrc dst with
              | mk dstNode stDst =>
                  simp [hSrc, hToNN, hInsert, hEnsSrc, hEnsDst] at hStep
                  cases hStep
                  have hObjSrc : stSrc.objects = st2.objects := by
                    simpa [hEnsSrc] using SystemState.ensureCdtNodeForSlot_objects_eq st2 src
                  have hObjDst : stDst.objects = stSrc.objects := by
                    simpa [hEnsDst] using SystemState.ensureCdtNodeForSlot_objects_eq stSrc dst
                  have hObjFinal : ({ stDst with cdt := stDst.cdt.addEdge srcNode dstNode .copy }).objects = st2.objects := by
                    simp [hObjDst, hObjSrc]
                  have hU' := cspaceSlotUnique_of_objects_eq st2 { stDst with cdt := stDst.cdt.addEdge srcNode dstNode .copy } hU2 hObjFinal
                  -- WS-H4: cspaceSlotCountBounded transfers via objects equality
                  -- cdtCompleteness and cdtAcyclicity for CDT-modifying ops taken as hypotheses
                  exact ⟨hU', cspaceLookupSound_of_cspaceSlotUnique _ hU',
                    cspaceSlotCountBounded_of_objects_eq st2 _ hBnd2 hObjFinal,
                    hCdtPost.1, hCdtPost.2,
                    cspaceDepthConsistent_of_objects_eq st2 _ hDepth2 hObjFinal,
                    hObjFinal ▸ hObjInv2⟩

/-- WS-E4/C-02: cspaceMove preserves capabilityInvariantBundle.
Move composes lookup + insert + delete, all of which preserve the bundle. -/
theorem cspaceMove_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hDstCapacity : ∀ cn cap, st.objects[dst.cnode]? = some (.cnode cn) →
      (cn.insert dst.slot cap).slotCountBounded)
    (hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st')
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
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
                (fun cn hObj => hDstCapacity cn cap hObj)
                (objects_invExt_of_capabilityInvariantBundle st hInv) hInsert
              have hNSSt2 : st2.cdtNodeSlot = st.cdtNodeSlot := by
                unfold cspaceInsertSlot at hInsert
                cases hPre : st.objects[dst.cnode]? with
                | none => simp [hPre] at hInsert
                | some obj =>
                  cases obj with
                  | cnode cn =>
                    simp [hPre] at hInsert
                    cases hLookup : cn.lookup dst.slot with
                    | some _ => simp [hLookup] at hInsert
                    | none =>
                      simp [hLookup] at hInsert
                      cases hS : storeObject dst.cnode (.cnode (cn.insert dst.slot cap)) st with
                      | error e => simp [hS] at hInsert
                      | ok pair =>
                        obtain ⟨_, stM⟩ := pair
                        simp [hS] at hInsert
                        have hNS1 := (storeObject_cdtNodeSlot_eq st stM dst.cnode _ hS).1
                        have ⟨_, hNS2, _, _⟩ := storeCapabilityRef_cdt_eq stM st2 dst (some cap.target) hInsert
                        rw [hNS2, hNS1]
                  | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hPre] at hInsert
              have hBundleSt3 := cspaceDeleteSlotCore_preserves_capabilityInvariantBundle st2 st3 src hBundleSt2
                (by rw [hNSSt2]; exact hNodeSlotK) hDelete
              rcases hBundleSt3 with ⟨hU3, _, hBnd3, _, _, hDepth3, hObjInv3⟩
              cases hNode : SystemState.lookupCdtNodeOfSlot st2 src with
              | none =>
                  simp [hSrc, hToNN, hInsert, hDelete, hNode] at hStep
                  cases hStep
                  exact ⟨hU3, cspaceLookupSound_of_cspaceSlotUnique _ hU3,
                    hBnd3, hCdtPost.1, hCdtPost.2, hDepth3, hObjInv3⟩
              | some srcNode =>
                  simp [hSrc, hToNN, hInsert, hDelete, hNode] at hStep
                  cases hStep
                  have hObjEq : (SystemState.attachSlotToCdtNode st3 dst srcNode).objects = st3.objects :=
                    SystemState.attachSlotToCdtNode_objects_eq st3 dst srcNode
                  have hU' := cspaceSlotUnique_of_objects_eq st3
                    (SystemState.attachSlotToCdtNode st3 dst srcNode)
                    hU3 hObjEq
                  exact ⟨hU', cspaceLookupSound_of_cspaceSlotUnique _ hU',
                    cspaceSlotCountBounded_of_objects_eq st3 _ hBnd3 hObjEq,
                    hCdtPost.1, hCdtPost.2,
                    cspaceDepthConsistent_of_objects_eq st3 _ hDepth3 hObjEq,
                    hObjEq ▸ hObjInv3⟩

/-- WS-E4/C-03: cspaceMintWithCdt preserves capabilityInvariantBundle.
Composes cspaceMint (already proven) + CDT edge addition. -/
theorem cspaceMintWithCdt_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hInv : capabilityInvariantBundle st)
    (hDstCapacity : ∀ cn cap, st.objects[dst.cnode]? = some (.cnode cn) →
      (cn.insert dst.slot cap).slotCountBounded)
    (hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st')
    (hStep : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceMintWithCdt at hStep
  cases hMint : cspaceMint src dst rights badge st with
  | error e => simp [hMint] at hStep
  | ok pair =>
      rcases pair with ⟨_, st1⟩
      have hBundle := cspaceMint_preserves_capabilityInvariantBundle st st1 src dst rights badge hInv
        hDstCapacity hMint
      rcases hBundle with ⟨hU1, _, hBnd1, _, _, hDepth1, hObjInv1⟩
      cases hEnsSrc : SystemState.ensureCdtNodeForSlot st1 src with
      | mk srcNode stSrc =>
          cases hEnsDst : SystemState.ensureCdtNodeForSlot stSrc dst with
          | mk dstNode stDst =>
              simp [hMint, hEnsSrc, hEnsDst] at hStep
              cases hStep
              have hObjSrc : stSrc.objects = st1.objects := by
                simpa [hEnsSrc] using SystemState.ensureCdtNodeForSlot_objects_eq st1 src
              have hObjDst : stDst.objects = stSrc.objects := by
                simpa [hEnsDst] using SystemState.ensureCdtNodeForSlot_objects_eq stSrc dst
              have hObjFinal : ({ stDst with cdt := stDst.cdt.addEdge srcNode dstNode .mint }).objects = st1.objects := by
                simp [hObjDst, hObjSrc]
              have hU' := cspaceSlotUnique_of_objects_eq st1 { stDst with cdt := stDst.cdt.addEdge srcNode dstNode .mint } hU1 hObjFinal
              exact ⟨hU', cspaceLookupSound_of_cspaceSlotUnique _ hU',
                cspaceSlotCountBounded_of_objects_eq st1 _ hBnd1 hObjFinal,
                hCdtPost.1, hCdtPost.2,
                cspaceDepthConsistent_of_objects_eq st1 _ hDepth1 hObjFinal,
                hObjFinal ▸ hObjInv1⟩

/-- AE4-C (U-18/CAP-02): Discharge CDT acyclicity for `cspaceMintWithCdt`
when the destination CDT node is fresh (no edges reference it).

This bridges `addEdge_preserves_edgeWellFounded_fresh` into the
`cspaceMintWithCdt` context. When `ensureCdtNodeForSlot` creates a new
CDT node for an empty destination slot, that node has ID = `cdtNextNode`
and no edges reference it. This theorem proves that `addEdge` with such
a fresh child preserves both `cdtCompleteness` and `cdtAcyclicity`,
eliminating the `hCdtPost` hypothesis for the mint case.

Usage: callers that construct the state via `cspaceMintWithCdt` can
discharge the CDT invariants using this theorem + `hFreshDst` (provable
from `cdtNextNode` freshness). -/
theorem cspaceMintWithCdt_cdtAcyclicity_of_freshDst
    (cdt : CapDerivationTree) (srcNode dstNode : CdtNodeId) (hNeq : srcNode ≠ dstNode)
    (hAcyclic : cdt.edgeWellFounded)
    (hFreshDst : ∀ e ∈ cdt.edges, e.parent ≠ dstNode ∧ e.child ≠ dstNode) :
    (cdt.addEdge srcNode dstNode .mint).edgeWellFounded :=
  CapDerivationTree.addEdge_preserves_edgeWellFounded_fresh cdt srcNode dstNode .mint
    hNeq hAcyclic hFreshDst

-- ============================================================================
-- WS-F4/F-06: cspaceMutate preservation
-- ============================================================================

/-- WS-F4/F-06: cspaceMutate preserves capabilityInvariantBundle.
Mutate composes cspaceLookupSlot (read-only) + cn.insert (which preserves
slotsUnique) + storeObject + storeCapabilityRef. -/
theorem cspaceMutate_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hInv : capabilityInvariantBundle st)
    (hSlotCapacity : ∀ cn cap, st.objects[addr.cnode]? = some (.cnode cn) →
      (cn.insert addr.slot cap).slotCountBounded)
    (hStep : cspaceMutate addr rights badge st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hBounded, hComp, hAcyclic, hDepthPre, hObjInv⟩
  have hUnique' : cspaceSlotUnique st' := by
    intro cnodeId cn hObj
    -- Revert hStep to decompose the definition via goal-level case splits
    revert hStep; unfold cspaceMutate
    cases hLookup : cspaceLookupSlot addr st with
    | error e => simp
    | ok pair =>
      rcases pair with ⟨cap, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr cap hLookup
      subst st1
      -- AK8-K (C-L2): null-cap guard discharged first.
      by_cases hNull : cap.isNull
      · simp [hNull]
      by_cases hRights : rightsSubset rights cap.rights
      · simp only [hNull, Bool.false_eq_true, ↓reduceIte, hRights]
        cases hPre : st.objects[addr.cnode]? with
        | none => simp
        | some preObj =>
          cases preObj with
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp
          | cnode preCn =>
            simp only []
            cases hStore : storeObject addr.cnode
              (.cnode (preCn.insert addr.slot
                { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) st with
            | error e => simp
            | ok pair =>
              obtain ⟨_, stMid⟩ := pair
              simp only []
              intro hStep
              by_cases hEq : cnodeId = addr.cnode
              · rw [hEq] at hObj
                have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr
                  (some cap.target) hStep
                have hObjMid := storeObject_objects_eq st stMid addr.cnode
                  (.cnode (preCn.insert addr.slot
                    { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) hObjInv hStore
                have hFinal : st'.objects[addr.cnode]? =
                    some (.cnode (preCn.insert addr.slot
                      { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) := by
                  rw [← hObjMid]; exact congrArg (·[addr.cnode]?) hObjRef
                rw [hFinal] at hObj; cases hObj
                exact CNode.insert_slotsUnique preCn addr.slot _
                  (hUnique addr.cnode preCn hPre)
              · have hObjMid := storeObject_objects_ne st stMid addr.cnode cnodeId
                  (.cnode (preCn.insert addr.slot
                    { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) hEq hObjInv hStore
                have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr
                  (some cap.target) hStep
                have hFinal : st'.objects[cnodeId]? = st.objects[cnodeId]? := by
                  rw [← hObjMid]; exact congrArg (·[cnodeId]?) hObjRef
                rw [hFinal] at hObj
                exact hUnique cnodeId cn hObj
      · simp [hNull, hRights]
  -- WS-H4: cspaceMutate goes through storeObject(CNode.insert) → storeCapabilityRef, same as insertSlot
  have ⟨hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' ∧ st'.objects.invExt := by
    unfold cspaceMutate at hStep
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
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp_all
          | cnode preCn =>
            simp only [hPre] at hStep
            cases hStore : storeObject addr.cnode (.cnode (preCn.insert addr.slot
              { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) st with
            | error e => simp_all
            | ok pair =>
              obtain ⟨_, stMid⟩ := pair; simp only [hStore] at hStep
              have ⟨hRefCdt, hRefNS, _, hRefObj⟩ := storeCapabilityRef_cdt_eq stMid st' addr
                (some cap.target) hStep
              have hBndMid := cspaceSlotCountBounded_of_storeObject_cnode st stMid addr.cnode _ hBounded hObjInv hStore
                (hSlotCapacity preCn _ hPre)
              have hCompMid := cdtCompleteness_of_storeObject st stMid addr.cnode _ hComp hObjInv hStore
                (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
              have hAcyclicMid := cdtAcyclicity_of_cdt_eq st stMid hAcyclic
                (storeObject_cdt_eq st stMid addr.cnode _ hStore)
              have hDepthMid := cspaceDepthConsistent_of_storeObject_insertCNode
                st stMid addr.cnode preCn addr.slot
                { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) }
                hDepthPre hObjInv hPre hStore
              have hObjInvMid := storeObject_preserves_objects_invExt st stMid addr.cnode _ hObjInv hStore
              exact ⟨cspaceSlotCountBounded_of_objects_eq stMid st' hBndMid hRefObj,
                cdtCompleteness_of_objects_nodeSlot_eq stMid st' hCompMid hRefObj hRefNS,
                cdtAcyclicity_of_cdt_eq stMid st' hAcyclicMid hRefCdt,
                cspaceDepthConsistent_of_objects_eq stMid st' hDepthMid hRefObj,
                hRefObj ▸ hObjInvMid⟩
      · simp_all
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique',
    hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩


end SeLe4n.Kernel
