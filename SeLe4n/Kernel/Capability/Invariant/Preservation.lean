/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Authority

namespace SeLe4n.Kernel

open SeLe4n.Model

theorem cspaceLookupSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceLookupSlot addr st = .ok (cap, st')) :
    capabilityInvariantBundle st' := by
  have hEq : st' = st := cspaceLookupSlot_preserves_state st st' addr cap hStep
  subst hEq
  simpa using hInv

/-- WS-E2 / H-01: Compositional preservation of `cspaceInsertSlot`.
Uses pre-state `cspaceSlotUnique` + `CNode.insert_slotsUnique` to derive post-state
uniqueness, rather than re-proving from scratch. -/
theorem cspaceInsertSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hInv : capabilityInvariantBundle st)
    (hSlotCapacity : ∀ cn, st.objects[addr.cnode]? = some (.cnode cn) →
      (cn.insert addr.slot cap).slotCountBounded)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hBounded, hComp, hAcyclic, hDepthPre⟩
  -- Compositionally derive post-state uniqueness (WS-E2 / H-01)
  have hUnique' : cspaceSlotUnique st' := by
    intro cnodeId cn hObj
    by_cases hEq : cnodeId = addr.cnode
    · -- Modified CNode: derive uniqueness via CNode.insert_slotsUnique
      unfold cspaceInsertSlot at hStep
      rw [hEq] at hObj
      cases hPre : st.objects[addr.cnode]? with
      | none => simp [hPre] at hStep
      | some preObj =>
        cases preObj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hPre] at hStep
        | cnode preCn =>
          simp [hPre] at hStep
          -- WS-E4/H-02: case split on occupied-slot guard
          cases hLookup : preCn.lookup addr.slot with
          | some _ => simp [hLookup] at hStep
          | none =>
            simp [hLookup] at hStep
            cases hStore : storeObject addr.cnode (.cnode (preCn.insert addr.slot cap)) st with
            | error e => simp [hStore] at hStep
            | ok pair =>
              obtain ⟨_, stMid⟩ := pair
              simp [hStore] at hStep
              have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr (some cap.target) hStep
              have hObjMid := storeObject_objects_eq st stMid addr.cnode
                (.cnode (preCn.insert addr.slot cap)) hStore
              have hFinal : st'.objects[addr.cnode]? = some (.cnode (preCn.insert addr.slot cap)) := by
                rw [← hObjMid]; exact congrArg (·[addr.cnode]?) hObjRef
              rw [hFinal] at hObj; cases hObj
              exact CNode.insert_slotsUnique preCn addr.slot cap (hUnique addr.cnode preCn hPre)
    · -- Unmodified CNodes: transfer directly from pre-state
      have hPreObj := cspaceInsertSlot_preserves_objects_ne st st' addr cap cnodeId hEq hStep
      rw [hPreObj] at hObj
      exact hUnique cnodeId cn hObj
  -- WS-H4: Transfer new components through storeObject(CNode) → storeCapabilityRef chain
  have ⟨hBounded', hComp', hAcyclic', hDepth'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' := by
    unfold cspaceInsertSlot at hStep
    cases hPre : st.objects[addr.cnode]? with
    | none => simp [hPre] at hStep
    | some preObj =>
      cases preObj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hPre] at hStep
      | cnode preCn =>
        cases hLookup : preCn.lookup addr.slot with
        | some _ => simp [hPre, hLookup] at hStep
        | none =>
          simp [hPre, hLookup] at hStep
          cases hStore : storeObject addr.cnode (.cnode (preCn.insert addr.slot cap)) st with
          | error e => simp [hStore] at hStep
          | ok pair =>
            obtain ⟨_, stMid⟩ := pair
            simp [hStore] at hStep
            have ⟨hRefCdt, hRefNS, _, hRefObj⟩ := storeCapabilityRef_cdt_eq stMid st' addr (some cap.target) hStep
            have hBndMid := cspaceSlotCountBounded_of_storeObject_cnode st stMid addr.cnode
              (preCn.insert addr.slot cap) hBounded hStore (hSlotCapacity preCn hPre)
            have hCompMid := cdtCompleteness_of_storeObject st stMid addr.cnode
              (.cnode (preCn.insert addr.slot cap)) hComp hStore
              (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
            have hDepthMid := cspaceDepthConsistent_of_storeObject_insertCNode
              st stMid addr.cnode preCn addr.slot cap hDepthPre hPre hStore
            exact ⟨cspaceSlotCountBounded_of_objects_eq stMid st' hBndMid hRefObj,
              cdtCompleteness_of_objects_nodeSlot_eq stMid st' hCompMid hRefObj hRefNS,
              cdtAcyclicity_of_cdt_eq st st' hAcyclic
                (by rw [hRefCdt]; exact storeObject_cdt_eq st stMid addr.cnode _ hStore),
              cspaceDepthConsistent_of_objects_eq stMid st' hDepthMid hRefObj⟩
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique',
    hBounded', hComp', hAcyclic', hDepth'⟩

theorem cspaceMint_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hInv : capabilityInvariantBundle st)
    (hDstCapacity : ∀ cn cap, st.objects[dst.cnode]? = some (.cnode cn) →
      (cn.insert dst.slot cap).slotCountBounded)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceMint at hStep
  cases hSrc : cspaceLookupSlot src st with
  | error e => simp [hSrc] at hStep
  | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 src parent hSrc
      subst st1
      cases hMint : mintDerivedCap parent rights badge with
      | error e => simp [hSrc, hMint] at hStep
      | ok child =>
          have hInsert : cspaceInsertSlot dst child st = .ok ((), st') := by
            simpa [hSrc, hMint] using hStep
          exact cspaceInsertSlot_preserves_capabilityInvariantBundle st st' dst child hInv
            (fun cn hObj => hDstCapacity cn child hObj) hInsert

/-- WS-E2 / H-01: Compositional preservation of `cspaceDeleteSlot`.
Uses pre-state `cspaceSlotUnique` + `CNode.remove_slotsUnique` to derive post-state
uniqueness. -/
theorem cspaceDeleteSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hBounded, hComp, hAcyclic, hDepthPre⟩
  have hUnique' : cspaceSlotUnique st' := by
    intro cnodeId cn hObj
    unfold cspaceDeleteSlot at hStep
    cases hPre : st.objects[addr.cnode]? with
    | none => simp [hPre] at hStep
    | some preObj =>
      cases preObj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hPre] at hStep
      | cnode preCn =>
        simp [hPre] at hStep
        cases hStore : storeObject addr.cnode (.cnode (preCn.remove addr.slot)) st with
        | error e => simp [hStore] at hStep
        | ok pair =>
          obtain ⟨_, stMid⟩ := pair
          cases hRef : storeCapabilityRef addr none stMid with
          | error e => simp [hStore, hRef] at hStep
          | ok pairRef =>
            obtain ⟨_, stRef⟩ := pairRef
            simp [hStore, hRef] at hStep
            cases hStep
            have hObjRef : stRef.objects = stMid.objects :=
              storeCapabilityRef_preserves_objects stMid stRef addr none hRef
            have hObjDetach : (SystemState.detachSlotFromCdt stRef addr).objects = stRef.objects :=
              SystemState.detachSlotFromCdt_objects_eq stRef addr
            by_cases hEq : cnodeId = addr.cnode
            · rw [hEq] at hObj
              have hObjMid := storeObject_objects_eq st stMid addr.cnode
                (.cnode (preCn.remove addr.slot)) hStore
              have : (SystemState.detachSlotFromCdt stRef addr).objects[addr.cnode]? =
                  some (.cnode (preCn.remove addr.slot)) := by
                rw [hObjDetach, hObjRef, ← hObjMid]
              rw [this] at hObj; cases hObj
              exact CNode.remove_slotsUnique preCn addr.slot (hUnique addr.cnode preCn hPre)
            · have hObjMid := storeObject_objects_ne st stMid addr.cnode cnodeId
                (.cnode (preCn.remove addr.slot)) hEq hStore
              have : (SystemState.detachSlotFromCdt stRef addr).objects[cnodeId]? = st.objects[cnodeId]? := by
                rw [hObjDetach, hObjRef, ← hObjMid]
              rw [this] at hObj
              exact hUnique cnodeId cn hObj
  -- WS-H4: Prove new components through storeObject → storeCapabilityRef → detachSlotFromCdt
  have ⟨hBounded', hComp', hAcyclic', hDepth'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' := by
    unfold cspaceDeleteSlot at hStep
    cases hPre : st.objects[addr.cnode]? with
    | none => simp [hPre] at hStep
    | some preObj =>
      cases preObj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hPre] at hStep
      | cnode preCn =>
        simp [hPre] at hStep
        cases hStore : storeObject addr.cnode (.cnode (preCn.remove addr.slot)) st with
        | error e => simp [hStore] at hStep
        | ok pair =>
          obtain ⟨_, stMid⟩ := pair
          cases hRef : storeCapabilityRef addr none stMid with
          | error e => simp [hStore, hRef] at hStep
          | ok pairRef =>
            obtain ⟨_, stRef⟩ := pairRef
            simp [hStore, hRef] at hStep; cases hStep
            have ⟨hRefCdt, hRefNS, _, hRefObj⟩ := storeCapabilityRef_cdt_eq stMid stRef addr none hRef
            have hBndMid := cspaceSlotCountBounded_of_storeObject_cnode st stMid addr.cnode
              (preCn.remove addr.slot) hBounded hStore (CNode.remove_slotCountBounded preCn addr.slot (hBounded addr.cnode preCn hPre))
            have hCompMid := cdtCompleteness_of_storeObject st stMid addr.cnode _ hComp hStore
              (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
            have hAcyclicMid := cdtAcyclicity_of_cdt_eq st stMid hAcyclic
              (storeObject_cdt_eq st stMid addr.cnode _ hStore)
            have hDepthMid := cspaceDepthConsistent_of_storeObject_sameCNode
              st stMid addr.cnode preCn (preCn.remove addr.slot) hDepthPre hPre hStore rfl rfl rfl
            have hBndRef := cspaceSlotCountBounded_of_objects_eq stMid stRef hBndMid hRefObj
            have hCompRef := cdtCompleteness_of_objects_nodeSlot_eq stMid stRef hCompMid hRefObj hRefNS
            have hAcyclicRef := cdtAcyclicity_of_cdt_eq stMid stRef hAcyclicMid hRefCdt
            have hDepthRef := cspaceDepthConsistent_of_objects_eq stMid stRef hDepthMid hRefObj
            exact ⟨cspaceSlotCountBounded_of_detachSlotFromCdt stRef addr hBndRef,
              cdtCompleteness_of_detachSlotFromCdt stRef addr hCompRef,
              cdtAcyclicity_of_detachSlotFromCdt stRef addr hAcyclicRef,
              cspaceDepthConsistent_of_detachSlotFromCdt stRef addr hDepthRef⟩
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique',
    hBounded', hComp', hAcyclic', hDepth'⟩

/-- WS-E2 / H-01: Compositional preservation of `cspaceRevoke`.
Uses pre-state `cspaceSlotUnique` + `CNode.revokeTargetLocal_slotsUnique` to derive
post-state uniqueness. -/
theorem cspaceRevoke_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hBounded, hComp, hAcyclic, hDepthPre⟩
  have hUnique' : cspaceSlotUnique st' := by
    intro cnodeId cn hObj
    unfold cspaceRevoke at hStep
    cases hLookup : cspaceLookupSlot addr st with
    | error e => simp [hLookup] at hStep
    | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr parent hLookup
      subst st1
      cases hPre : st.objects[addr.cnode]? with
      | none => simp [hLookup, hPre] at hStep
      | some preObj =>
        cases preObj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hLookup, hPre] at hStep
        | cnode preCn =>
          simp [hLookup, hPre] at hStep
          cases hStore : storeObject addr.cnode
            (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) st with
          | error e => simp [hStore] at hStep
          | ok pair =>
            obtain ⟨_, stMid⟩ := pair
            simp [hStore] at hStep
            -- M-P01: hStep now gives st' = revokeAndClearRefsState ...
            have hObjRef : st'.objects = stMid.objects := by
              have hFused := revokeAndClearRefsState_preserves_objects preCn addr.slot parent.target addr.cnode stMid
              simp_all
            by_cases hEq : cnodeId = addr.cnode
            · rw [hEq] at hObj
              have hObjMid := storeObject_objects_eq st stMid addr.cnode
                (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) hStore
              have : st'.objects[addr.cnode]? =
                  some (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) := by
                rw [← hObjMid]; exact congrArg (·[addr.cnode]?) hObjRef
              rw [this] at hObj; cases hObj
              exact CNode.revokeTargetLocal_slotsUnique preCn addr.slot parent.target
                (hUnique addr.cnode preCn hPre)
            · have hObjMid := storeObject_objects_ne st stMid addr.cnode cnodeId
                (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) hEq hStore
              have : st'.objects[cnodeId]? = st.objects[cnodeId]? := by
                rw [← hObjMid]; exact congrArg (·[cnodeId]?) hObjRef
              rw [this] at hObj
              exact hUnique cnodeId cn hObj
  -- WS-H4: storeObject(CNode.revokeTargetLocal) → revokeAndClearRefsState (M-P01)
  have ⟨hBounded', hComp', hAcyclic', hDepth'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' := by
    unfold cspaceRevoke at hStep
    cases hLookup2 : cspaceLookupSlot addr st with
    | error e => simp [hLookup2] at hStep
    | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr parent hLookup2; subst st1
      cases hPre : st.objects[addr.cnode]? with
      | none => simp [hLookup2, hPre] at hStep
      | some preObj =>
        cases preObj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hLookup2, hPre] at hStep
        | cnode preCn =>
          simp [hLookup2, hPre] at hStep
          cases hStore : storeObject addr.cnode (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) st with
          | error e => simp [hStore] at hStep
          | ok pair =>
            obtain ⟨_, stMid⟩ := pair; simp [hStore] at hStep
            have hBndMid := cspaceSlotCountBounded_of_storeObject_cnode st stMid addr.cnode _ hBounded hStore
              (CNode.revokeTargetLocal_slotCountBounded preCn addr.slot parent.target (hBounded addr.cnode preCn hPre))
            have hCompMid := cdtCompleteness_of_storeObject st stMid addr.cnode _ hComp hStore
              (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
            have hAcyclicMid := cdtAcyclicity_of_cdt_eq st stMid hAcyclic
              (storeObject_cdt_eq st stMid addr.cnode _ hStore)
            have hDepthMid := cspaceDepthConsistent_of_storeObject_sameCNode
              st stMid addr.cnode preCn (preCn.revokeTargetLocal addr.slot parent.target)
              hDepthPre hPre hStore rfl rfl rfl
            -- M-P01: Use revokeAndClearRefsState field preservation
            have ⟨hClearCdt, hClearNS, _, hClearObj⟩ :=
              revokeAndClearRefsState_cdt_eq preCn addr.slot parent.target addr.cnode stMid
            rw [hStep] at *
            exact ⟨cspaceSlotCountBounded_of_objects_eq stMid _ hBndMid hClearObj,
              cdtCompleteness_of_objects_nodeSlot_eq stMid _ hCompMid hClearObj hClearNS,
              cdtAcyclicity_of_cdt_eq stMid _ hAcyclicMid hClearCdt,
              cspaceDepthConsistent_of_objects_eq stMid _ hDepthMid hClearObj⟩
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique',
    hBounded', hComp', hAcyclic', hDepth'⟩

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
      cases hInsert : cspaceInsertSlot dst cap st with
      | error e => simp [hSrc, hInsert] at hStep
      | ok pair2 =>
          rcases pair2 with ⟨_, st2⟩
          have hBundleSt2 := cspaceInsertSlot_preserves_capabilityInvariantBundle st st2 dst cap hInv
            (fun cn hObj => hDstCapacity cn cap hObj) hInsert
          rcases hBundleSt2 with ⟨hU2, _, hBnd2, hComp2, _, hDepth2⟩
          cases hEnsSrc : SystemState.ensureCdtNodeForSlot st2 src with
          | mk srcNode stSrc =>
              cases hEnsDst : SystemState.ensureCdtNodeForSlot stSrc dst with
              | mk dstNode stDst =>
                  simp [hSrc, hInsert, hEnsSrc, hEnsDst] at hStep
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
                    cspaceDepthConsistent_of_objects_eq st2 _ hDepth2 hObjFinal⟩

/-- WS-E4/C-02: cspaceMove preserves capabilityInvariantBundle.
Move composes lookup + insert + delete, all of which preserve the bundle. -/
theorem cspaceMove_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hDstCapacity : ∀ cn cap, st.objects[dst.cnode]? = some (.cnode cn) →
      (cn.insert dst.slot cap).slotCountBounded)
    (hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st')
    (hStep : cspaceMove src dst st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceMove at hStep
  cases hSrc : cspaceLookupSlot src st with
  | error e => simp [hSrc] at hStep
  | ok pair =>
      rcases pair with ⟨cap, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 src cap hSrc
      subst st1
      cases hInsert : cspaceInsertSlot dst cap st with
      | error e => simp [hSrc, hInsert] at hStep
      | ok pair2 =>
          rcases pair2 with ⟨_, st2⟩
          cases hDelete : cspaceDeleteSlot src st2 with
          | error e => simp [hSrc, hInsert, hDelete] at hStep
          | ok pair3 =>
              rcases pair3 with ⟨_, st3⟩
              have hBundleSt2 := cspaceInsertSlot_preserves_capabilityInvariantBundle st st2 dst cap hInv
                (fun cn hObj => hDstCapacity cn cap hObj) hInsert
              have hBundleSt3 := cspaceDeleteSlot_preserves_capabilityInvariantBundle st2 st3 src hBundleSt2 hDelete
              rcases hBundleSt3 with ⟨hU3, _, hBnd3, _, _, hDepth3⟩
              cases hNode : SystemState.lookupCdtNodeOfSlot st2 src with
              | none =>
                  simp [hSrc, hInsert, hDelete, hNode] at hStep
                  cases hStep
                  exact ⟨hU3, cspaceLookupSound_of_cspaceSlotUnique _ hU3,
                    hBnd3, hCdtPost.1, hCdtPost.2, hDepth3⟩
              | some srcNode =>
                  simp [hSrc, hInsert, hDelete, hNode] at hStep
                  cases hStep
                  have hObjEq : (SystemState.attachSlotToCdtNode st3 dst srcNode).objects = st3.objects :=
                    SystemState.attachSlotToCdtNode_objects_eq st3 dst srcNode
                  have hU' := cspaceSlotUnique_of_objects_eq st3
                    (SystemState.attachSlotToCdtNode st3 dst srcNode)
                    hU3 hObjEq
                  exact ⟨hU', cspaceLookupSound_of_cspaceSlotUnique _ hU',
                    cspaceSlotCountBounded_of_objects_eq st3 _ hBnd3 hObjEq,
                    hCdtPost.1, hCdtPost.2,
                    cspaceDepthConsistent_of_objects_eq st3 _ hDepth3 hObjEq⟩

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
      rcases hBundle with ⟨hU1, _, hBnd1, _, _, hDepth1⟩
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
                cspaceDepthConsistent_of_objects_eq st1 _ hDepth1 hObjFinal⟩

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
  rcases hInv with ⟨hUnique, _hSound, hBounded, hComp, hAcyclic, hDepthPre⟩
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
      by_cases hRights : rightsSubset rights cap.rights
      · simp only [hRights, ite_true]
        cases hPre : st.objects[addr.cnode]? with
        | none => simp
        | some preObj =>
          cases preObj with
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp
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
                    { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) hStore
                have hFinal : st'.objects[addr.cnode]? =
                    some (.cnode (preCn.insert addr.slot
                      { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) := by
                  rw [← hObjMid]; exact congrArg (·[addr.cnode]?) hObjRef
                rw [hFinal] at hObj; cases hObj
                exact CNode.insert_slotsUnique preCn addr.slot _
                  (hUnique addr.cnode preCn hPre)
              · have hObjMid := storeObject_objects_ne st stMid addr.cnode cnodeId
                  (.cnode (preCn.insert addr.slot
                    { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) hEq hStore
                have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr
                  (some cap.target) hStep
                have hFinal : st'.objects[cnodeId]? = st.objects[cnodeId]? := by
                  rw [← hObjMid]; exact congrArg (·[cnodeId]?) hObjRef
                rw [hFinal] at hObj
                exact hUnique cnodeId cn hObj
      · simp [hRights]
  -- WS-H4: cspaceMutate goes through storeObject(CNode.insert) → storeCapabilityRef, same as insertSlot
  have ⟨hBounded', hComp', hAcyclic', hDepth'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' := by
    unfold cspaceMutate at hStep
    cases hLookup2 : cspaceLookupSlot addr st with
    | error e => simp [hLookup2] at hStep
    | ok pair =>
      rcases pair with ⟨cap, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr cap hLookup2; subst st1
      by_cases hRights : rightsSubset rights cap.rights
      · simp only [hLookup2, hRights, ite_true] at hStep
        cases hPre : st.objects[addr.cnode]? with
        | none => simp_all
        | some preObj =>
          cases preObj with
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp_all
          | cnode preCn =>
            simp only [hPre] at hStep
            cases hStore : storeObject addr.cnode (.cnode (preCn.insert addr.slot
              { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) st with
            | error e => simp_all
            | ok pair =>
              obtain ⟨_, stMid⟩ := pair; simp only [hStore] at hStep
              have ⟨hRefCdt, hRefNS, _, hRefObj⟩ := storeCapabilityRef_cdt_eq stMid st' addr
                (some cap.target) hStep
              have hBndMid := cspaceSlotCountBounded_of_storeObject_cnode st stMid addr.cnode _ hBounded hStore
                (hSlotCapacity preCn _ hPre)
              have hCompMid := cdtCompleteness_of_storeObject st stMid addr.cnode _ hComp hStore
                (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
              have hAcyclicMid := cdtAcyclicity_of_cdt_eq st stMid hAcyclic
                (storeObject_cdt_eq st stMid addr.cnode _ hStore)
              have hDepthMid := cspaceDepthConsistent_of_storeObject_insertCNode
                st stMid addr.cnode preCn addr.slot
                { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) }
                hDepthPre hPre hStore
              exact ⟨cspaceSlotCountBounded_of_objects_eq stMid st' hBndMid hRefObj,
                cdtCompleteness_of_objects_nodeSlot_eq stMid st' hCompMid hRefObj hRefNS,
                cdtAcyclicity_of_cdt_eq stMid st' hAcyclicMid hRefCdt,
                cspaceDepthConsistent_of_objects_eq stMid st' hDepthMid hRefObj⟩
      · simp_all
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique',
    hBounded', hComp', hAcyclic', hDepth'⟩

-- ============================================================================
-- WS-F4/F-06: cspaceRevokeCdt and cspaceRevokeCdtStrict preservation
-- ============================================================================

/-- Helper: CDT-only state updates preserve capabilityInvariantBundle,
given that the new CDT is acyclic. -/
private theorem capabilityInvariantBundle_of_cdt_update
    (st : SystemState) (cdt' : CapDerivationTree)
    (hInv : capabilityInvariantBundle st)
    (hAcyclic' : cdt'.edgeWellFounded) :
    capabilityInvariantBundle { st with cdt := cdt' } := by
  rcases hInv with ⟨hU, _, hBnd, hComp, _, hDepthPre⟩
  have hObjEq : ({ st with cdt := cdt' } : SystemState).objects = st.objects := rfl
  exact ⟨cspaceSlotUnique_of_objects_eq st _ hU hObjEq,
    cspaceLookupSound_of_cspaceSlotUnique _ (cspaceSlotUnique_of_objects_eq st _ hU hObjEq),
    hBnd, hComp, hAcyclic',
    cspaceDepthConsistent_of_objects_eq st _ hDepthPre hObjEq⟩

/-- Fold body function for cspaceRevokeCdt: processes one CDT descendant node. -/
private def revokeCdtFoldBody
    (acc : Except KernelError (Unit × SystemState)) (node : CdtNodeId) :
    Except KernelError (Unit × SystemState) :=
  match acc with
  | .error e => .error e
  | .ok ((), stAcc) =>
      match SystemState.lookupCdtSlotOfNode stAcc node with
      | none => .ok ((), { stAcc with cdt := stAcc.cdt.removeNode node })
      | some descAddr =>
          match cspaceDeleteSlot descAddr stAcc with
          | .error _ => .ok ((), { stAcc with cdt := stAcc.cdt.removeNode node })
          | .ok ((), stDel) =>
              let stDetached := SystemState.detachSlotFromCdt stDel descAddr
              .ok ((), { stDetached with cdt := stDetached.cdt.removeNode node })

/-- Single fold step preserves capabilityInvariantBundle. -/
private theorem revokeCdtFoldBody_preserves
    (stAcc stNext : SystemState) (node : CdtNodeId)
    (hInv : capabilityInvariantBundle stAcc)
    (hStep : revokeCdtFoldBody (.ok ((), stAcc)) node = .ok ((), stNext)) :
    capabilityInvariantBundle stNext := by
  unfold revokeCdtFoldBody at hStep
  cases hSlot : SystemState.lookupCdtSlotOfNode stAcc node with
  | none =>
    simp [hSlot] at hStep; cases hStep
    exact capabilityInvariantBundle_of_cdt_update stAcc _ hInv
      (CapDerivationTree.edgeWellFounded_sub _ _ hInv.2.2.2.2.1 (CapDerivationTree.removeNode_edges_sub stAcc.cdt node))
  | some descAddr =>
    simp [hSlot] at hStep
    cases hDel : cspaceDeleteSlot descAddr stAcc with
    | error _ =>
      simp [hDel] at hStep; cases hStep
      exact capabilityInvariantBundle_of_cdt_update stAcc _ hInv
        (CapDerivationTree.edgeWellFounded_sub _ _ hInv.2.2.2.2.1 (CapDerivationTree.removeNode_edges_sub stAcc.cdt node))
    | ok pair =>
      obtain ⟨_, stDel⟩ := pair
      simp [hDel] at hStep; cases hStep
      have hDelInv := cspaceDeleteSlot_preserves_capabilityInvariantBundle stAcc stDel descAddr hInv hDel
      have hDetachObj := SystemState.detachSlotFromCdt_objects_eq stDel descAddr
      rcases hDelInv with ⟨hU2, _, hBnd2, hComp2, hAcyclic2, hDepth2del⟩
      have hDetachInv : capabilityInvariantBundle (SystemState.detachSlotFromCdt stDel descAddr) :=
        ⟨cspaceSlotUnique_of_objects_eq stDel _ hU2 hDetachObj,
         cspaceLookupSound_of_cspaceSlotUnique _ (cspaceSlotUnique_of_objects_eq stDel _ hU2 hDetachObj),
         cspaceSlotCountBounded_of_detachSlotFromCdt stDel descAddr hBnd2,
         cdtCompleteness_of_detachSlotFromCdt stDel descAddr hComp2,
         cdtAcyclicity_of_detachSlotFromCdt stDel descAddr hAcyclic2,
         cspaceDepthConsistent_of_objects_eq stDel _ hDepth2del hDetachObj⟩
      exact capabilityInvariantBundle_of_cdt_update _ _ hDetachInv
        (CapDerivationTree.edgeWellFounded_sub _ _ hDetachInv.2.2.2.2.1
          (CapDerivationTree.removeNode_edges_sub (SystemState.detachSlotFromCdt stDel descAddr).cdt node))

/-- Error propagation: revokeCdtFoldBody propagates errors unchanged. -/
private theorem revokeCdtFoldBody_error (e : KernelError) (node : CdtNodeId) :
    revokeCdtFoldBody (.error e) node = .error e := by
  unfold revokeCdtFoldBody; rfl

/-- Fold error propagation: foldl revokeCdtFoldBody starting from error stays error. -/
private theorem revokeCdtFoldBody_foldl_error
    (nodes : List CdtNodeId) (e : KernelError) :
    nodes.foldl revokeCdtFoldBody (.error e) = .error e := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => simp [List.foldl, revokeCdtFoldBody_error, ih]

/-- Fold induction: cspaceRevokeCdt fold preserves capabilityInvariantBundle. -/
private theorem revokeCdtFold_preserves
    (nodes : List CdtNodeId)
    (stInit stFinal : SystemState)
    (hInv : capabilityInvariantBundle stInit)
    (hFold : nodes.foldl revokeCdtFoldBody (.ok ((), stInit)) = .ok ((), stFinal)) :
    capabilityInvariantBundle stFinal := by
  induction nodes generalizing stInit stFinal with
  | nil =>
    simp [List.foldl] at hFold; cases hFold; exact hInv
  | cons node rest ih =>
    simp only [List.foldl] at hFold
    -- Case split on whether the step succeeds or errors
    cases hStep : revokeCdtFoldBody (.ok ((), stInit)) node with
    | error e =>
      rw [hStep, revokeCdtFoldBody_foldl_error] at hFold; simp at hFold
    | ok val =>
      obtain ⟨_, stMid⟩ := val
      rw [hStep] at hFold
      exact ih stMid stFinal (revokeCdtFoldBody_preserves stInit stMid node hInv hStep) hFold

/-- WS-F4/F-06: cspaceRevokeCdt preserves capabilityInvariantBundle.
Composes cspaceRevoke (proven) + fold over CDT descendants. -/
theorem cspaceRevokeCdt_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevokeCdt addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceRevokeCdt at hStep
  split at hStep
  · simp at hStep
  · rename_i stLocal hRevoke
    have hLocalInv := cspaceRevoke_preserves_capabilityInvariantBundle st stLocal addr hInv hRevoke
    split at hStep
    · simp at hStep; cases hStep; exact hLocalInv
    · rename_i rootNode hLookup
      -- hStep has the fold result; the inline lambda is definitionally equal to revokeCdtFoldBody
      change (stLocal.cdt.descendantsOf rootNode).foldl revokeCdtFoldBody
          (.ok ((), stLocal)) = .ok ((), st') at hStep
      exact revokeCdtFold_preserves _ stLocal st' hLocalInv hStep

/-- WS-M1/M-G04: Error-swallowing consistency theorem. When `revokeCdtFoldBody`
encounters a `cspaceDeleteSlot` error, it drops the error and performs only a
CDT `removeNode`. This theorem proves that invariant preservation holds through
the swallowed-error path specifically — the resulting state satisfies
`capabilityInvariantBundle` because `removeNode` only shrinks the edge set
(via `edgeWellFounded_sub`), leaving all other CSpace state untouched. -/
theorem cspaceRevokeCdt_swallowed_error_consistent
    (stAcc stNext : SystemState) (node : CdtNodeId)
    (descAddr : CSpaceAddr) (err : KernelError)
    (hInv : capabilityInvariantBundle stAcc)
    (hSlot : SystemState.lookupCdtSlotOfNode stAcc node = some descAddr)
    (hDelErr : cspaceDeleteSlot descAddr stAcc = .error err)
    (hStep : revokeCdtFoldBody (.ok ((), stAcc)) node = .ok ((), stNext)) :
    capabilityInvariantBundle stNext ∧
    stNext.objects = stAcc.objects ∧
    stNext.cdt.edges ⊆ stAcc.cdt.edges := by
  unfold revokeCdtFoldBody at hStep
  simp [hSlot, hDelErr] at hStep; cases hStep
  exact ⟨capabilityInvariantBundle_of_cdt_update stAcc _ hInv
    (CapDerivationTree.edgeWellFounded_sub _ _ hInv.2.2.2.2.1
      (CapDerivationTree.removeNode_edges_sub stAcc.cdt node)),
   rfl,
   CapDerivationTree.removeNode_edges_sub stAcc.cdt node⟩

/-- WS-F4/F-06: cspaceRevokeCdtStrict preserves capabilityInvariantBundle.
The strict variant composes cspaceRevoke + a fold that only does cspaceDeleteSlot
and CDT operations, same as the non-strict variant. -/
theorem cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (report : RevokeCdtStrictReport)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevokeCdtStrict addr st = .ok (report, st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceRevokeCdtStrict at hStep
  split at hStep
  · simp at hStep
  · rename_i stLocal hRevoke
    have hLocalInv := cspaceRevoke_preserves_capabilityInvariantBundle st stLocal addr hInv hRevoke
    split at hStep
    · -- No CDT root: stLocal is the final state
      simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact hLocalInv
    · -- CDT root found: fold processes descendants
      rename_i rootNode _hLookup
      -- The fold produces (report, stFinal) from a pure total step function,
      -- so we need to show the fold preserves the invariant through each step.
      -- Each step either: (a) does nothing (firstFailure already set),
      -- (b) removes a CDT node (objects unchanged), (c) deletes a slot + detaches CDT,
      -- or (d) records a failure + removes CDT node.
      -- In all cases, CNode objects are either unchanged or go through cspaceDeleteSlot.
      suffices h : ∀ (nodes : List CdtNodeId) (rep : RevokeCdtStrictReport) (stAcc : SystemState),
          capabilityInvariantBundle stAcc →
          capabilityInvariantBundle (nodes.foldl (fun acc node =>
            let (report, stCur) := acc
            match report.firstFailure with
            | some _ => (report, stCur)
            | none =>
                match SystemState.lookupCdtSlotOfNode stCur node with
                | none => (report, { stCur with cdt := stCur.cdt.removeNode node })
                | some descAddr =>
                    match cspaceDeleteSlot descAddr stCur with
                    | .error err =>
                        ({ report with firstFailure := some {
                            offendingNode := node, offendingSlot := some descAddr, error := err } },
                         { stCur with cdt := stCur.cdt.removeNode node })
                    | .ok ((), stDel) =>
                        let stDetached := SystemState.detachSlotFromCdt stDel descAddr
                        ({ report with deletedSlots := descAddr :: report.deletedSlots },
                         { stDetached with cdt := stDetached.cdt.removeNode node })
          ) (rep, stAcc)).2 by
        simp at hStep
        have hInvFold := h (stLocal.cdt.descendantsOf rootNode)
          { deletedSlots := [], firstFailure := none } stLocal hLocalInv
        obtain ⟨_, hStEq⟩ := hStep
        rw [← hStEq]; exact hInvFold
      intro nodes
      induction nodes with
      | nil => intro rep stAcc hI; simpa [List.foldl] using hI
      | cons node rest ih =>
        intro rep stAcc hI
        simp only [List.foldl]
        cases rep.firstFailure with
        | some _ => exact ih rep stAcc hI
        | none =>
          cases hSlot : SystemState.lookupCdtSlotOfNode stAcc node with
          | none =>
            simp
            exact ih rep { stAcc with cdt := stAcc.cdt.removeNode node }
              (capabilityInvariantBundle_of_cdt_update stAcc _ hI
                (CapDerivationTree.edgeWellFounded_sub _ _ hI.2.2.2.2.1 (CapDerivationTree.removeNode_edges_sub stAcc.cdt node)))
          | some descAddr =>
            simp
            cases hDel : cspaceDeleteSlot descAddr stAcc with
            | error err =>
              simp
              exact ih _ { stAcc with cdt := stAcc.cdt.removeNode node }
                (capabilityInvariantBundle_of_cdt_update stAcc _ hI
                  (CapDerivationTree.edgeWellFounded_sub _ _ hI.2.2.2.2.1 (CapDerivationTree.removeNode_edges_sub stAcc.cdt node)))
            | ok pair =>
              obtain ⟨_, stDel⟩ := pair
              simp
              have hDelInv := cspaceDeleteSlot_preserves_capabilityInvariantBundle stAcc stDel
                descAddr hI hDel
              have hDetachObj := SystemState.detachSlotFromCdt_objects_eq stDel descAddr
              rcases hDelInv with ⟨hU2, _, hBnd2, hComp2, hAcyclic2, hDepth2del⟩
              have hDetachInv : capabilityInvariantBundle (SystemState.detachSlotFromCdt stDel descAddr) :=
                ⟨cspaceSlotUnique_of_objects_eq stDel _ hU2 hDetachObj,
                 cspaceLookupSound_of_cspaceSlotUnique _ (cspaceSlotUnique_of_objects_eq stDel _ hU2 hDetachObj),
                 cspaceSlotCountBounded_of_detachSlotFromCdt stDel descAddr hBnd2,
                 cdtCompleteness_of_detachSlotFromCdt stDel descAddr hComp2,
                 cdtAcyclicity_of_detachSlotFromCdt stDel descAddr hAcyclic2,
                 cspaceDepthConsistent_of_objects_eq stDel _ hDepth2del hDetachObj⟩
              exact ih _ _ (capabilityInvariantBundle_of_cdt_update _ _ hDetachInv
                (CapDerivationTree.edgeWellFounded_sub _ _ hDetachInv.2.2.2.2.1
                  (CapDerivationTree.removeNode_edges_sub (SystemState.detachSlotFromCdt stDel descAddr).cdt node)))

-- ============================================================================
-- WS-E4: Preservation theorems for endpointReply
-- ============================================================================

/-- M-P05: Shared reply-path infrastructure — if `storeTcbIpcStateAndMessage`
succeeds and the target was a TCB (evidenced by `lookupTcb`), then
`ensureRunnable` on the result preserves the capability invariant bundle.

Extracted from `endpointReply_preserves_capabilityInvariantBundle` to eliminate
duplicated proof across the authorized/unrestricted reply branches. Also
provides reusable infrastructure for M3 (IPC capability transfer). -/
private theorem capabilityInvariantBundle_of_storeTcbAndEnsureRunnable
    (st st1 : SystemState) (target : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (tcb : TCB)
    (hUnique : cspaceSlotUnique st)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hDepthPre : cspaceDepthConsistent st)
    (hTcb : storeTcbIpcStateAndMessage st target ipc msg = .ok st1)
    (hLookup : lookupTcb st target = some tcb) :
    capabilityInvariantBundle (ensureRunnable st1 target) := by
  have hCnodeBackward : ∀ (cnodeId : SeLe4n.ObjId) (cn : CNode),
      st1.objects[cnodeId]? = some (.cnode cn) → st.objects[cnodeId]? = some (.cnode cn) := by
    intro cnodeId cn hCn1
    by_cases hEq : cnodeId = target.toObjId
    · subst hEq
      have hTargetTcb : ∃ tcb', st.objects[target.toObjId]? = some (.tcb tcb') := by
        unfold lookupTcb at hLookup; cases hObj : st.objects[target.toObjId]? with
        | none => simp [hObj] at hLookup
        | some obj => cases obj with
          | tcb t => exact ⟨t, rfl⟩
          | _ => simp [hObj] at hLookup
      have hTcbPost := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 target ipc msg hTcb hTargetTcb
      rcases hTcbPost with ⟨tcb', hTcb'⟩
      rw [hTcb'] at hCn1; cases hCn1
    · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target ipc msg cnodeId hEq hTcb] at hCn1; exact hCn1
  have hU1 : cspaceSlotUnique st1 := by
    intro cnodeId cn hCn1; exact hUnique cnodeId cn (hCnodeBackward cnodeId cn hCn1)
  have hU := cspaceSlotUnique_of_objects_eq st1 (ensureRunnable st1 target)
    hU1 (ensureRunnable_preserves_objects st1 target)
  have ⟨hBndE, hCompE, hAcyclicE⟩ :=
    cdtPredicates_through_reply_path st st1 target ipc msg hBounded hComp hAcyclic hTcb
  have hDepth1 : cspaceDepthConsistent st1 := by
    intro cnodeId cn hCn1; exact hDepthPre cnodeId cn (hCnodeBackward cnodeId cn hCn1)
  have hDepthE := cspaceDepthConsistent_of_objects_eq st1 _ hDepth1
    (ensureRunnable_preserves_objects st1 target)
  exact ⟨hU, cspaceLookupSound_of_cspaceSlotUnique _ hU,
    hBndE, hCompE, hAcyclicE, hDepthE⟩

/-- WS-F1/WS-E4/M-12/WS-H1: endpointReply preserves capabilityInvariantBundle.
Reply stores a TCB with message (not a CNode), so CSpace invariants are preserved.
Updated for WS-H1 reply-target scoping (replier parameter + replyTarget validation).
M-P05: Proof body delegated to `capabilityInvariantBundle_of_storeTcbAndEnsureRunnable`. -/
theorem endpointReply_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hBounded, hComp, hAcyclic, hDepthPre⟩
  unfold endpointReply at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready => simp [hIpc] at hStep
      | blockedOnSend _ => simp [hIpc] at hStep
      | blockedOnReceive _ => simp [hIpc] at hStep
      | blockedOnNotification _ => simp [hIpc] at hStep
      | blockedOnCall _ => simp [hIpc] at hStep
      | blockedOnReply epId _ =>
          simp only [hIpc] at hStep
          -- WS-H1/M-02: replyTarget validation — both branches dispatch to
          -- capabilityInvariantBundle_of_storeTcbAndEnsureRunnable.
          suffices ∀ st1, storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st1 →
              capabilityInvariantBundle (ensureRunnable st1 target) by
            split at hStep
            · -- some expected: if replier == expected
              split at hStep
              · -- authorized = true
                revert hStep
                cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
                | error e => simp
                | ok st1 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hStEq⟩; subst hStEq
                    exact this st1 hTcb
              · -- authorized = false
                simp_all
            · -- none: no replyTarget constraint
              dsimp only at hStep
              revert hStep
              cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
              | error e => simp
              | ok st1 =>
                  simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hStEq⟩; subst hStEq
                  exact this st1 hTcb
          -- Dispatch to extracted lemma
          intro st1 hTcb
          exact capabilityInvariantBundle_of_storeTcbAndEnsureRunnable
            st st1 target .ready (some msg) tcb
            hUnique hBounded hComp hAcyclic hDepthPre hTcb hLookup

/-- M3 composed bundle entrypoint: M1 scheduler + M2 capability + M3 IPC.

WS-H12e: Updated to use `ipcInvariantFull` (which composes `ipcInvariant`,
`dualQueueSystemInvariant`, and `allPendingMessagesBounded`) instead of
the bare `ipcInvariant`. This closes the gap where dual-queue structural
well-formedness and message payload bounds were defined but not composed
into the cross-subsystem proof surface. -/
def coreIpcInvariantBundle (st : SystemState) : Prop :=
  schedulerInvariantBundle st ∧ capabilityInvariantBundle st ∧ ipcInvariantFull st

/-- WS-H12e: Extract the bare `ipcInvariant` from the core bundle for
backward-compatible proof composition. -/
theorem coreIpcInvariantBundle_to_ipcInvariant {st : SystemState}
    (h : coreIpcInvariantBundle st) : ipcInvariant st :=
  h.2.2.1

/-- WS-H12e: Extract `dualQueueSystemInvariant` from the core bundle. -/
theorem coreIpcInvariantBundle_to_dualQueueSystemInvariant {st : SystemState}
    (h : coreIpcInvariantBundle st) : dualQueueSystemInvariant st :=
  h.2.2.2.1

/-- WS-H12e: Extract `allPendingMessagesBounded` from the core bundle. -/
theorem coreIpcInvariantBundle_to_allPendingMessagesBounded {st : SystemState}
    (h : coreIpcInvariantBundle st) : allPendingMessagesBounded st :=
  h.2.2.2.2.1

/-- WS-F5/D1d: Extract `badgeWellFormed` from the core bundle. -/
theorem coreIpcInvariantBundle_to_badgeWellFormed {st : SystemState}
    (h : coreIpcInvariantBundle st) : badgeWellFormed st :=
  h.2.2.2.2.2

/-- Named M3.5 coherence component: runnable threads stay IPC-ready. -/
def ipcSchedulerRunnableReadyComponent (st : SystemState) : Prop :=
  runnableThreadIpcReady st

/-- Named M3.5 coherence component: send-blocked threads are not runnable. -/
def ipcSchedulerBlockedSendComponent (st : SystemState) : Prop :=
  blockedOnSendNotRunnable st

/-- Named M3.5 coherence component: receive-blocked threads are not runnable. -/
def ipcSchedulerBlockedReceiveComponent (st : SystemState) : Prop :=
  blockedOnReceiveNotRunnable st

/-- WS-H1: Named coherence component: call-blocked threads are not runnable. -/
def ipcSchedulerBlockedCallComponent (st : SystemState) : Prop :=
  blockedOnCallNotRunnable st

/-- WS-H1: Named coherence component: reply-blocked threads are not runnable. -/
def ipcSchedulerBlockedReplyComponent (st : SystemState) : Prop :=
  blockedOnReplyNotRunnable st

/-- WS-F6/D2: Named coherence component: notification-blocked threads are not runnable. -/
def ipcSchedulerBlockedNotificationComponent (st : SystemState) : Prop :=
  blockedOnNotificationNotRunnable st

/-- Named M3.5 aggregate coherence component for IPC+scheduler interaction. -/
def ipcSchedulerCoherenceComponent (st : SystemState) : Prop :=
  ipcSchedulerRunnableReadyComponent st ∧
  ipcSchedulerBlockedSendComponent st ∧
  ipcSchedulerBlockedReceiveComponent st ∧
  ipcSchedulerBlockedCallComponent st ∧
  ipcSchedulerBlockedReplyComponent st ∧
  ipcSchedulerBlockedNotificationComponent st

theorem ipcSchedulerCoherenceComponent_iff_contractPredicates (st : SystemState) :
    ipcSchedulerCoherenceComponent st ↔ ipcSchedulerContractPredicates st := by
  rfl

/-- M3.5 composed bundle entrypoint layered over the M3 IPC seed bundle.

This is the step-4 composition target for active-slice endpoint/scheduler coupling.
WS-H12e: Adds `contextMatchesCurrent` and `currentThreadDequeueCoherent` to the
coupling bundle, ensuring register-context coherence and dequeue-on-dispatch
coherence predicates are part of the cross-subsystem proof surface. -/
def ipcSchedulerCouplingInvariantBundle (st : SystemState) : Prop :=
  coreIpcInvariantBundle st ∧ ipcSchedulerCoherenceComponent st ∧
  contextMatchesCurrent st ∧ currentThreadDequeueCoherent st

/-- M4-A composed bundle entrypoint:
M3.5 IPC+scheduler composition plus lifecycle metadata/invariant obligations. -/
def lifecycleCompositionInvariantBundle (st : SystemState) : Prop :=
  ipcSchedulerCouplingInvariantBundle st ∧ lifecycleInvariantBundle st

theorem lifecycleRetypeObject_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : schedulerInvariantBundle st)
    (hCurrentValid : currentThreadValid st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  have hSchedEq : st'.scheduler = st.scheduler :=
    lifecycle_storeObject_scheduler_eq st st' target newObj hStore
  rcases hInv with ⟨hQueue, hRunUnique, _hCurrent⟩
  exact ⟨by simpa [hSchedEq] using hQueue, by simpa [hSchedEq] using hRunUnique, hCurrentValid⟩

/-- WS-E2 / H-01: Compositional preservation of `lifecycleRetypeObject`.
Requires new CNode objects to have unique slots (analogous to existing
`hNewObjEndpointInv` / `hNewObjNotificationInv` side conditions on IPC proofs). -/
theorem lifecycleRetypeObject_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : capabilityInvariantBundle st)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hNewObjCNodeBounded : ∀ cn, newObj = .cnode cn → cn.slotCountBounded)
    (hNewObjCNodeDepth : ∀ cn, newObj = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hBounded, hComp, hAcyclic, hDepthPre⟩
  have hUnique' : cspaceSlotUnique st' := by
    rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
      ⟨_, _, _, _, _, _, hStore⟩
    intro cnodeId cn hObj
    by_cases hEq : cnodeId = target
    · rw [hEq] at hObj
      have hObjAtTarget := lifecycle_storeObject_objects_eq st st' target newObj hStore
      rw [hObjAtTarget] at hObj
      cases newObj with
      | cnode _ => cases hObj; exact hNewObjCNodeUniq cn rfl
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => cases hObj
    · have hPreserved := lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target
        cnodeId newObj hEq hStep
      rw [hPreserved] at hObj
      exact hUnique cnodeId cn hObj
  -- WS-H4: lifecycleRetypeObject delegates to storeObject, which preserves CDT fields
  have ⟨hBounded', hComp', hAcyclic', hDepth'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' := by
    rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
      ⟨_, _, _, _, _, _, hStore⟩
    have hNS := (storeObject_cdtNodeSlot_eq st st' target newObj hStore).1
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro cnodeId cn hObj
      by_cases hEq : cnodeId = target
      · rw [hEq] at hObj; rw [lifecycle_storeObject_objects_eq st st' target newObj hStore] at hObj
        cases newObj with
        | cnode _ => cases hObj; exact hNewObjCNodeBounded cn rfl
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => cases hObj
      · rw [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target cnodeId newObj hEq hStep] at hObj
        exact hBounded cnodeId cn hObj
    · exact cdtCompleteness_of_storeObject st st' target newObj hComp hStore hNS
    · exact cdtAcyclicity_of_cdt_eq st st' hAcyclic (storeObject_cdt_eq st st' target newObj hStore)
    · intro cnodeId cn hObj
      by_cases hEq : cnodeId = target
      · rw [hEq] at hObj; rw [lifecycle_storeObject_objects_eq st st' target newObj hStore] at hObj
        cases newObj with
        | cnode _ => cases hObj; exact hNewObjCNodeDepth cn rfl
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => cases hObj
      · rw [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target cnodeId newObj hEq hStep] at hObj
        exact hDepthPre cnodeId cn hObj
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique',
    hBounded', hComp', hAcyclic', hDepth'⟩

theorem lifecycleRetypeObject_preserves_ipcInvariant
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : ipcInvariant st)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    ipcInvariant st' := by
  intro oid ntfn hNtfn
  by_cases hEq : oid = target
  · subst hEq
    have hObjAtTarget : st'.objects[oid]? = some newObj := by
      rcases lifecycleRetypeObject_ok_as_storeObject st st' authority oid newObj hStep with
        ⟨_, _, _, _, _, _, hStore⟩
      exact lifecycle_storeObject_objects_eq st st' oid newObj hStore
    have hSomeEq : some newObj = some (.notification ntfn) := by
      simpa [hObjAtTarget] using hNtfn
    have hNewObjEq : newObj = .notification ntfn := by
      injection hSomeEq
    exact hNewObjNotificationInv ntfn hNewObjEq
  · have hPreserved : st'.objects[oid]? = st.objects[oid]? :=
      lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target oid newObj hEq hStep
    have hNtfnSt : st.objects[oid]? = some (.notification ntfn) := by simpa [hPreserved] using hNtfn
    exact hInv oid ntfn hNtfnSt

theorem lifecycleRetypeObject_preserves_coreIpcInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : coreIpcInvariantBundle st)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hNewObjCNodeBounded : ∀ cn, newObj = .cnode cn → cn.slotCountBounded)
    (hNewObjCNodeDepth : ∀ cn, newObj = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hCurrentValid : currentThreadValid st')
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    coreIpcInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpcFull⟩
  refine ⟨?_, ?_, ?_⟩
  · exact lifecycleRetypeObject_preserves_schedulerInvariantBundle st st' authority target newObj hSched
      hCurrentValid hStep
  · exact lifecycleRetypeObject_preserves_capabilityInvariantBundle st st' authority target newObj hCap
      hNewObjCNodeUniq hNewObjCNodeBounded hNewObjCNodeDepth hStep
  · exact ⟨lifecycleRetypeObject_preserves_ipcInvariant st st' authority target newObj hIpcFull.1 hNewObjNotificationInv hStep,
           hDualQueue', hBounded', hBadge'⟩

theorem lifecycleRetypeObject_preserves_lifecycleCompositionInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : lifecycleCompositionInvariantBundle st)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hNewObjCNodeBounded : ∀ cn, newObj = .cnode cn → cn.slotCountBounded)
    (hNewObjCNodeDepth : ∀ cn, newObj = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hCurrentValid : currentThreadValid st')
    (hCoherence' : ipcSchedulerCoherenceComponent st')
    (hCtxMatch' : contextMatchesCurrent st')
    (hDeqCoherent' : currentThreadDequeueCoherent st')
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    lifecycleCompositionInvariantBundle st' := by
  rcases hInv with ⟨hM35, hLifecycle⟩
  rcases hM35 with ⟨hM3, _hCoherence, _hCtx, _hDeq⟩
  have hM3' : coreIpcInvariantBundle st' :=
    lifecycleRetypeObject_preserves_coreIpcInvariantBundle st st' authority target newObj hM3
      hNewObjNotificationInv hNewObjCNodeUniq hNewObjCNodeBounded hNewObjCNodeDepth hCurrentValid hDualQueue' hBounded' hBadge' hStep
  have hLifecycle' : lifecycleInvariantBundle st' :=
    SeLe4n.Kernel.lifecycleRetypeObject_preserves_lifecycleInvariantBundle st st' authority target
      newObj hLifecycle hStep
  exact ⟨⟨hM3', hCoherence', hCtxMatch', hDeqCoherent'⟩, hLifecycle'⟩


theorem lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : capabilityInvariantBundle st)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hNewObjCNodeBounded : ∀ cn, newObj = .cnode cn → cn.slotCountBounded)
    (hNewObjCNodeDepth : ∀ cn, newObj = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases lifecycleRevokeDeleteRetype_ok_implies_staged_steps st st' authority cleanup target newObj hStep with
    ⟨stRevoked, stDeleted, _hNe, hRevoke, hDelete, _hLookupDeleted, hRetype⟩
  have hRevoked : capabilityInvariantBundle stRevoked :=
    cspaceRevoke_preserves_capabilityInvariantBundle st stRevoked cleanup hInv hRevoke
  have hDeleted : capabilityInvariantBundle stDeleted :=
    cspaceDeleteSlot_preserves_capabilityInvariantBundle stRevoked stDeleted cleanup hRevoked hDelete
  exact lifecycleRetypeObject_preserves_capabilityInvariantBundle stDeleted st' authority target newObj
    hDeleted hNewObjCNodeUniq hNewObjCNodeBounded hNewObjCNodeDepth hRetype

theorem lifecycleRevokeDeleteRetype_preserves_lifecycleCapabilityStaleAuthorityInvariant
    (st st' : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hCap : capabilityInvariantBundle st)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hNewObjCNodeBounded : ∀ cn, newObj = .cnode cn → cn.slotCountBounded)
    (hNewObjCNodeDepth : ∀ cn, newObj = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hLifecycleAfterCleanup :
      ∀ stRevoked stDeleted,
        cspaceRevoke cleanup st = .ok ((), stRevoked) →
        cspaceDeleteSlot cleanup stRevoked = .ok ((), stDeleted) →
        cspaceLookupSlot cleanup stDeleted = .error .invalidCapability →
        lifecycleInvariantBundle stDeleted)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    lifecycleCapabilityStaleAuthorityInvariant st' := by
  rcases lifecycleRevokeDeleteRetype_ok_implies_staged_steps st st' authority cleanup target newObj hStep with
    ⟨stRevoked, stDeleted, _hNe, hRevoke, hDelete, hLookupDeleted, hRetype⟩
  have hCap' : capabilityInvariantBundle st' :=
    lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle st st' authority cleanup target
      newObj hCap hNewObjCNodeUniq hNewObjCNodeBounded hNewObjCNodeDepth hStep
  have hLifecycleDeleted : lifecycleInvariantBundle stDeleted :=
    hLifecycleAfterCleanup stRevoked stDeleted hRevoke hDelete hLookupDeleted
  have hLifecycle' : lifecycleInvariantBundle st' :=
    SeLe4n.Kernel.lifecycleRetypeObject_preserves_lifecycleInvariantBundle stDeleted st' authority target
      newObj hLifecycleDeleted hRetype
  exact lifecycleCapabilityStaleAuthorityInvariant_of_bundles st' hLifecycle' hCap'
    (lifecycleAuthorityMonotonicity_holds st')

theorem lifecycleRevokeDeleteRetype_error_preserves_lifecycleCompositionInvariantBundle
    (st : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hAlias : authority = cleanup)
    (hInv : lifecycleCompositionInvariantBundle st) :
    lifecycleCompositionInvariantBundle st := by
  have _hExpected : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .error .illegalState :=
    lifecycleRevokeDeleteRetype_error_authority_cleanup_alias st authority cleanup target newObj hAlias
  exact hInv

/-- WS-E3/H-09: storeTcbIpcState stores a TCB (not a CNode), so cspaceSlotUnique is preserved. -/
private theorem cspaceSlotUnique_of_storeTcbIpcState
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hUniq : cspaceSlotUnique st)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    cspaceSlotUnique st' := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have := Except.ok.inj hStep; subst this
      exact cspaceSlotUnique_of_storeObject_nonCNode st pair.2 tid.toObjId _ hUniq hStore
        (fun cn h => by cases h)

/-- WS-E3/H-09: cspaceSlotUnique through storeObject + storeTcbIpcState + removeRunnable chain. -/
private theorem cspaceSlotUnique_through_blocking_path
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (ep : Endpoint)
    (hUniq : cspaceSlotUnique st)
    (hStore : storeObject endpointId (.endpoint ep) st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target ipc = .ok st2) :
    cspaceSlotUnique (removeRunnable st2 target) :=
  cspaceSlotUnique_of_objects_eq st2 (removeRunnable st2 target)
    (cspaceSlotUnique_of_storeTcbIpcState st1 st2 target ipc
      (cspaceSlotUnique_of_endpoint_store st st1 endpointId ep hUniq hStore)
      hTcb) rfl

/-- WS-E3/H-09: cspaceSlotUnique through storeObject + storeTcbIpcState + ensureRunnable chain. -/
private theorem cspaceSlotUnique_through_handshake_path
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ep : Endpoint)
    (hUniq : cspaceSlotUnique st)
    (hStore : storeObject endpointId (.endpoint ep) st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target .ready = .ok st2) :
    cspaceSlotUnique (ensureRunnable st2 target) :=
  cspaceSlotUnique_of_objects_eq st2 (ensureRunnable st2 target)
    (cspaceSlotUnique_of_storeTcbIpcState st1 st2 target .ready
      (cspaceSlotUnique_of_endpoint_store st st1 endpointId ep hUniq hStore)
      hTcb) (ensureRunnable_preserves_objects st2 target)

-- ============================================================================
-- WS-F5/D1d: cspaceMint / cspaceMutate badge preservation
-- ============================================================================

/-- WS-F5/D1d: Storing a CNode preserves `notificationBadgesWellFormed`.
CNode stores never modify notification objects. -/
theorem storeObject_cnode_preserves_notificationBadgesWellFormed
    (st st' : SystemState) (targetId : SeLe4n.ObjId) (cn : CNode)
    (hInv : notificationBadgesWellFormed st)
    (hStore : storeObject targetId (.cnode cn) st = .ok ((), st')) :
    notificationBadgesWellFormed st' :=
  storeObject_nonNotification_preserves_notificationBadgesWellFormed
    st st' targetId _ hInv hStore (fun ntfn h => by cases h)

/-- WS-F5/D1d: Storing a CNode with all-valid badges preserves
`capabilityBadgesWellFormed`. -/
theorem storeObject_cnode_preserves_capabilityBadgesWellFormed
    (st st' : SystemState) (targetId : SeLe4n.ObjId) (cn : CNode)
    (hInv : capabilityBadgesWellFormed st)
    (hStore : storeObject targetId (.cnode cn) st = .ok ((), st'))
    (hValid : ∀ slot cap badge, cn.lookup slot = some cap →
      cap.badge = some badge → badge.valid) :
    capabilityBadgesWellFormed st' := by
  intro oid cn' slot cap badge hObj hLookup hBadge
  by_cases hEq : oid = targetId
  · subst hEq; rw [storeObject_objects_eq st st' oid _ hStore] at hObj
    cases hObj; exact hValid slot cap badge hLookup hBadge
  · exact hInv oid cn' slot cap badge
      ((storeObject_objects_ne st st' targetId oid _ hEq hStore).symm.trans hObj)
      hLookup hBadge

private theorem badgeWellFormed_of_objects_eq
    (st st' : SystemState)
    (hObj : st'.objects = st.objects)
    (hInv : badgeWellFormed st) :
    badgeWellFormed st' :=
  ⟨fun oid ntfn badge hLk hP => hInv.1 oid ntfn badge (by rw [hObj] at hLk; exact hLk) hP,
   fun oid cn slot cap badge hLk hS hB => hInv.2 oid cn slot cap badge (by rw [hObj] at hLk; exact hLk) hS hB⟩

/-- WS-F5/D1d: `cspaceMint` preserves `badgeWellFormed` when the minted badge
(if any) is valid. The parent capability's badge validity is inherited from
the pre-state `capabilityBadgesWellFormed` invariant. -/
theorem cspaceMint_preserves_badgeWellFormed
    (st st' : SystemState) (src dst : CSpaceAddr)
    (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (hInv : badgeWellFormed st)
    (hBadgeValid : ∀ b, badge = some b → b.valid)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  unfold cspaceMint at hStep
  cases hLookup : cspaceLookupSlot src st with
  | error e => simp [hLookup] at hStep
  | ok pair =>
    have hPairEq := cspaceLookupSlot_ok_state_eq st src pair.1 pair.2 hLookup
    subst hPairEq
    simp only [hLookup] at hStep
    cases hMint : mintDerivedCap pair.1 rights badge with
    | error e => simp [hMint] at hStep
    | ok child =>
      simp only [hMint] at hStep
      -- cspaceInsertSlot stores a CNode
      unfold cspaceInsertSlot at hStep
      cases hObj : pair.2.objects[dst.cnode]? with
      | none => simp [hObj] at hStep
      | some obj =>
        cases obj with
        | cnode cn =>
          simp only [hObj] at hStep
          split at hStep
          · simp at hStep  -- slot occupied
          · cases hStore : storeObject dst.cnode (.cnode (cn.insert dst.slot child)) pair.2 with
            | error e => simp [hStore] at hStep
            | ok storeResult =>
              obtain ⟨_, stMid⟩ := storeResult
              simp [hStore] at hStep
              -- hStep : storeCapabilityRef dst (some child.target) stMid = .ok ((), st')
              have hObjEq := storeCapabilityRef_preserves_objects
                stMid st' dst (some child.target) hStep
              apply badgeWellFormed_of_objects_eq stMid st' hObjEq
              -- Extract child.badge from mintDerivedCap
              have hChildBadge : child.badge = badge := by
                unfold mintDerivedCap at hMint; split at hMint
                · cases hMint; rfl
                · simp at hMint
              constructor
              · exact storeObject_cnode_preserves_notificationBadgesWellFormed
                  pair.2 stMid dst.cnode _ hNtfn hStore
              · exact storeObject_cnode_preserves_capabilityBadgesWellFormed
                  pair.2 stMid dst.cnode _ hCap hStore
                  (fun slot' cap' badge' hLk hBdg => by
                    by_cases hSlotEq : dst.slot = slot'
                    · subst hSlotEq
                      rw [CNode.lookup_insert_eq] at hLk
                      cases hLk; rw [hChildBadge] at hBdg
                      exact hBadgeValid badge' hBdg
                    · rw [CNode.lookup_insert_ne cn dst.slot slot' child hSlotEq] at hLk
                      exact hCap dst.cnode cn slot' cap' badge' hObj hLk hBdg)
        | _ => simp [hObj] at hStep

/-- WS-F5/D1d: `cspaceMutate` preserves `badgeWellFormed` when the mutated
badge (if any) is valid. -/
theorem cspaceMutate_preserves_badgeWellFormed
    (st st' : SystemState) (addr : CSpaceAddr)
    (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (hInv : badgeWellFormed st)
    (hBadgeValid : ∀ b, badge = some b → b.valid)
    (hStep : cspaceMutate addr rights badge st = .ok ((), st')) :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  unfold cspaceMutate at hStep
  cases hLookup : cspaceLookupSlot addr st with
  | error e => simp [hLookup] at hStep
  | ok pair =>
    have hPairEq := cspaceLookupSlot_ok_state_eq st addr pair.1 pair.2 hLookup
    simp only [hLookup] at hStep
    rw [hPairEq] at hStep
    split at hStep
    · -- rights subset check passed
      cases hObj : st.objects[addr.cnode]? with
      | none => simp [hObj] at hStep
      | some obj =>
        cases obj with
        | cnode cn =>
          simp [hObj] at hStep
          cases hStore : storeObject addr.cnode
              (.cnode (cn.insert addr.slot
                ⟨pair.1.target, rights, badge.or pair.1.badge⟩)) st with
          | error e => simp [hStore] at hStep
          | ok storeResult =>
            obtain ⟨_, stMid⟩ := storeResult
            simp [hStore] at hStep
            -- hStep : storeCapabilityRef addr (some pair.1.target) stMid = .ok ((), st')
            have hObjEq := storeCapabilityRef_preserves_objects
              stMid st' addr (some pair.1.target) hStep
            apply badgeWellFormed_of_objects_eq stMid st' hObjEq
            constructor
            · exact storeObject_cnode_preserves_notificationBadgesWellFormed
                st stMid addr.cnode _ hNtfn hStore
            · exact storeObject_cnode_preserves_capabilityBadgesWellFormed
                st stMid addr.cnode _ hCap hStore
                (fun slot' cap' badge' hLk hBdg => by
                  by_cases hSlotEq : addr.slot = slot'
                  · -- The mutated slot
                    subst hSlotEq
                    rw [CNode.lookup_insert_eq] at hLk; cases hLk
                    -- mutatedCap.badge = badge.or pair.1.badge
                    cases hBadge : badge with
                    | some b =>
                      simp [hBadge, Option.or] at hBdg; subst hBdg
                      exact hBadgeValid b hBadge
                    | none =>
                      simp [hBadge, Option.or] at hBdg
                      -- Badge from original cap (pair.1.badge)
                      have hLookup' : cspaceLookupSlot addr st = .ok (pair.fst, st) := by
                        rw [(Prod.eta pair).symm, hPairEq] at hLookup; exact hLookup
                      have hSlotCap := (cspaceLookupSlot_ok_iff_lookupSlotCap st addr pair.1).1
                        hLookup'
                      unfold SystemState.lookupSlotCap SystemState.lookupCNode at hSlotCap
                      simp only [hObj] at hSlotCap
                      exact hCap addr.cnode cn addr.slot pair.1 badge' hObj hSlotCap hBdg
                  · -- Other slot: unchanged
                    rw [CNode.lookup_insert_ne cn addr.slot slot' _ hSlotEq] at hLk
                    exact hCap addr.cnode cn slot' cap' badge' hObj hLk hBdg)
        | _ => simp [hObj] at hStep
    · simp at hStep

/-- M-D01: IPC single-cap transfer preserves the capability invariant bundle.

The proof decomposes into the `.noSlot` case (state unchanged, trivial) and
the `.installed` case, which chains:
1. `cspaceInsertSlot_preserves_capabilityInvariantBundle` — slot insertion
2. `ensureCdtNodeForSlot` — CDT field preservation (objects unchanged)
3. `addEdge` with `.ipcTransfer` — CDT edge addition

The `hCdtPost` hypothesis (CDT completeness + acyclicity of the post-state)
follows the same pattern as `cspaceCopy_preserves_capabilityInvariantBundle`
since IPC transfer is semantically a cross-CSpace copy. -/
theorem ipcTransferSingleCap_preserves_capabilityInvariantBundle
    (st st' : SystemState) (cap : Capability) (senderSlot : CSpaceAddr)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot) (scanLimit : Nat)
    (result : CapTransferResult)
    (hInv : capabilityInvariantBundle st)
    (hSlotCapacity : ∀ cn, st.objects[receiverRoot]? = some (.cnode cn) →
      ∀ s, (cn.insert s cap).slotCountBounded)
    (hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st')
    (hStep : ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    capabilityInvariantBundle st' := by
  simp only [ipcTransferSingleCap] at hStep
  cases hObj : st.objects[receiverRoot]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | cnode cn =>
      simp [hObj] at hStep
      cases hSlot : cn.findFirstEmptySlot slotBase scanLimit with
      | none =>
        simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInv
      | some emptySlot =>
        simp [hSlot] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap st with
        | error e => simp [hIns] at hStep
        | ok pair2 =>
          rcases pair2 with ⟨_, st2⟩
          have hBundleSt2 := cspaceInsertSlot_preserves_capabilityInvariantBundle st st2
            { cnode := receiverRoot, slot := emptySlot } cap hInv
            (fun cn' hObj' => hSlotCapacity cn' (by rw [hObj] at hObj'; cases hObj'; exact hObj) emptySlot)
            hIns
          rcases hBundleSt2 with ⟨hU2, _, hBnd2, _, _, hDepth2⟩
          cases hEnsSrc : SystemState.ensureCdtNodeForSlot st2 senderSlot with
          | mk srcNode stSrc =>
            cases hEnsDst : SystemState.ensureCdtNodeForSlot stSrc { cnode := receiverRoot, slot := emptySlot } with
            | mk dstNode stDst =>
              simp [hIns, hEnsSrc, hEnsDst] at hStep
              obtain ⟨_, rfl⟩ := hStep
              have hObjSrc : stSrc.objects = st2.objects := by
                simpa [hEnsSrc] using SystemState.ensureCdtNodeForSlot_objects_eq st2 senderSlot
              have hObjDst : stDst.objects = stSrc.objects := by
                simpa [hEnsDst] using SystemState.ensureCdtNodeForSlot_objects_eq stSrc { cnode := receiverRoot, slot := emptySlot }
              have hObjFinal : ({ stDst with cdt := stDst.cdt.addEdge srcNode dstNode .ipcTransfer } : SystemState).objects = st2.objects := by
                simp [hObjDst, hObjSrc]
              have hU' := cspaceSlotUnique_of_objects_eq st2 _ hU2 hObjFinal
              exact ⟨hU', cspaceLookupSound_of_cspaceSlotUnique _ hU',
                cspaceSlotCountBounded_of_objects_eq st2 _ hBnd2 hObjFinal,
                hCdtPost.1, hCdtPost.2,
                cspaceDepthConsistent_of_objects_eq st2 _ hDepth2 hObjFinal⟩

end SeLe4n.Kernel
