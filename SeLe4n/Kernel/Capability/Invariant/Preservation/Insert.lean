/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Authority

/-!
AN4-F.3 (CAP-M03) child module extracted from
`SeLe4n.Kernel.Capability.Invariant.Preservation`. Contains compositional
preservation theorems for the capability `cspaceLookupSlot`/`cspaceInsertSlot`
entry points plus the `cspaceMint` base operation (which composes
`cspaceLookupSlot` + `cspaceInsertSlot`). All declarations retain their
original names, order, and proofs; `private` helpers are promoted to
public at file-boundary scope so sibling preservation children can consume
them unchanged.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Internal


/-! ## U4-L / U-M26: CDT Hypothesis Pattern Rationale

CDT-modifying operations (`cspaceCopy`, `cspaceMove`, `cspaceDeleteSlot`,
`cspaceRevoke`) take `cdtCompleteness st' ∧ cdtAcyclicity st'` as an
**externalized post-state hypothesis** rather than proving it from the
pre-state invariant. This is deliberate:

1. **Structural separation.** The capability invariant bundle
   (`capabilityInvariantBundle`) covers slot-level properties (uniqueness,
   soundness, bounded slot count, depth consistency, `objects.invExt`).
   CDT structural properties (completeness, acyclicity) are logically
   orthogonal — they depend on the CDT graph shape, not on per-CNode
   slot state. Bundling them as hypotheses keeps each proof focused.

2. **CDT operation complexity.** CDT mutations (`addEdge`, `removeNode`,
   `revokeDerivationEdge`) modify an edge list and two maps (`childMap`,
   `parentMap`). Proving acyclicity preservation for `addEdge` requires
   a reachability argument over the graph (no path from child to parent
   in the pre-state). This argument is inherently CDT-specific and does
   not compose naturally with the slot-level induction used in capability
   preservation proofs.

3. **Caller context.** The CDT hypotheses are discharged at the
   cross-subsystem composition layer (`proofLayerInvariantBundle` in
   `Architecture/Invariant.lean`), where the full kernel invariant —
   including CDT acyclicity from `capabilityInvariantBundle` — is
   available. The decomposition `pre-state bundle → per-subsystem
   preservation → post-state bundle` works because each subsystem
   preservation theorem contributes its piece and receives the CDT
   piece from the composed invariant.

This pattern is consistent with the IPC `dualQueueSystemInvariant`
externalization (U-M31) and the information flow `hProjection` pattern
(U-H09). -/

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
    (_hObjInv : st.objects.invExt)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hBounded, hComp, hAcyclic, hDepthPre, hObjInv⟩
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
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hPre] at hStep
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
                (.cnode (preCn.insert addr.slot cap)) hObjInv hStore
              have hFinal : st'.objects[addr.cnode]? = some (.cnode (preCn.insert addr.slot cap)) := by
                rw [← hObjMid]; exact congrArg (·[addr.cnode]?) hObjRef
              rw [hFinal] at hObj; cases hObj
              exact CNode.insert_slotsUnique preCn addr.slot cap (hUnique addr.cnode preCn hPre)
    · -- Unmodified CNodes: transfer directly from pre-state
      have hPreObj := cspaceInsertSlot_preserves_objects_ne st st' addr cap cnodeId hEq hObjInv hStep
      rw [hPreObj] at hObj
      exact hUnique cnodeId cn hObj
  -- WS-H4: Transfer new components through storeObject(CNode) → storeCapabilityRef chain
  have ⟨hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' ∧ st'.objects.invExt := by
    unfold cspaceInsertSlot at hStep
    cases hPre : st.objects[addr.cnode]? with
    | none => simp [hPre] at hStep
    | some preObj =>
      cases preObj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hPre] at hStep
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
              (preCn.insert addr.slot cap) hBounded hObjInv hStore (hSlotCapacity preCn hPre)
            have hCompMid := cdtCompleteness_of_storeObject st stMid addr.cnode
              (.cnode (preCn.insert addr.slot cap)) hComp hObjInv hStore
              (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
            have hDepthMid := cspaceDepthConsistent_of_storeObject_insertCNode
              st stMid addr.cnode preCn addr.slot cap hDepthPre hObjInv hPre hStore
            have hObjInvMid := storeObject_preserves_objects_invExt st stMid addr.cnode _ hObjInv hStore
            exact ⟨cspaceSlotCountBounded_of_objects_eq stMid st' hBndMid hRefObj,
              cdtCompleteness_of_objects_nodeSlot_eq stMid st' hCompMid hRefObj hRefNS,
              cdtAcyclicity_of_cdt_eq st st' hAcyclic
                (by rw [hRefCdt]; exact storeObject_cdt_eq st stMid addr.cnode _ hStore),
              cspaceDepthConsistent_of_objects_eq stMid st' hDepthMid hRefObj,
              hRefObj ▸ hObjInvMid⟩
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique',
    hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩

/-- S3-D: `cspaceInsertSlot` preserves `cdtMapsConsistent`. Insert only calls
    `storeObject` + `storeCapabilityRef`, neither of which modifies the CDT. -/
theorem cspaceInsertSlot_cdt_eq
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.cdt = st.cdt := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | cnode cn =>
      simp only [hObj] at hStep
      cases hLookup : cn.lookup addr.slot with
      | some _ => simp [hLookup] at hStep
      | none =>
        simp only [hLookup] at hStep
        cases hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st with
        | error e => simp [hStore] at hStep
        | ok pair =>
          rcases pair with ⟨_, stMid⟩
          have h1 := storeObject_cdt_eq st stMid addr.cnode _ hStore
          simp only [hStore] at hStep
          unfold storeCapabilityRef at hStep
          simp at hStep; rcases hStep with ⟨_, rfl⟩
          exact h1
    | _ => simp [hObj] at hStep

theorem cspaceInsertSlot_preserves_cdtMapsConsistent
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hCon : cdtMapsConsistent st)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    cdtMapsConsistent st' :=
  cdtMapsConsistent_of_cdt_eq st st' hCon (cspaceInsertSlot_cdt_eq st st' addr cap hStep)

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
      -- AL1b (AK7-I.cascade): promote parent via toNonNull?; non-null derives from success.
      have hNotNull : parent.isNull = false := by
        by_cases h : parent.isNull
        · exfalso; simp [Capability.toNonNull?, h, hSrc] at hStep
        · exact Bool.not_eq_true _ |>.mp h
      have hToNN : parent.toNonNull? = some ⟨parent, hNotNull⟩ :=
        Capability.toNonNull?_of_not_null hNotNull
      cases hMint : mintDerivedCap ⟨parent, hNotNull⟩ rights badge with
      | error e => simp [hSrc, hToNN, hMint] at hStep
      | ok child =>
          have hInsert : cspaceInsertSlot dst child st = .ok ((), st') := by
            simpa [hSrc, hToNN, hMint] using hStep
          exact cspaceInsertSlot_preserves_capabilityInvariantBundle st st' dst child hInv
            (fun cn hObj => hDstCapacity cn child hObj)
            (objects_invExt_of_capabilityInvariantBundle st hInv) hInsert


end SeLe4n.Kernel
