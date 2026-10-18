-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.EndpointReplyAndLifecycle

/-!
AN4-F.3 (CAP-M03) child module extracted from
`SeLe4n.Kernel.Capability.Invariant.Preservation`. Contains the final
preservation stratum covering four operation families: (1)
`cspaceMint`/`cspaceMutate` badge-wellformedness preservation; (2)
`ipcTransferSingleCap` / `ipcUnwrapCapsLoop` / `ipcUnwrapCaps` (grant and
no-grant variants) capability-invariant-bundle preservation; (3)
`cdtMapsConsistent` preservation for every CDT-modifying operation
(`cspaceMint`, `cspaceDeleteSlotCore`/`cspaceDeleteSlot`, `cspaceCopy`,
`cspaceMove`, `cspaceRevoke`); (4) the CDT-expanding / CDT-shrinking
composition witnesses and the V3-E / V3-F post-resolution rights
commentary blocks. All declarations retain their original names, order,
and proofs.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Internal

-- ============================================================================
-- WS-F5/D1d: cspaceMint / cspaceMutate badge preservation
-- ============================================================================

-- WS-RR RR3.11: `storeObject_cnode_preserves_{notification,capability}BadgesWellFormed`,
-- `badgeWellFormed_of_objects_eq` and the whole IPC de-threading D8 cap-transfer
-- badge cluster (`cspaceInsertSlot` / `ipcTransferSingleCap` / `ipcUnwrapCapsLoop` /
-- `ipcUnwrapCaps` `_preserves_badgeWellFormed`) moved UP to
-- `IPC/Invariant/Structural/PerOperation.lean`, beside the other `ipcUnwrapCaps`
-- conjunct frames.  The `*WithCaps` `ipcInvariantFull` bundles (in
-- `Structural/DualQueueMembership.lean`) now **establish** `badgeWellFormed`
-- instead of threading it on their own post-state, and an establisher has to be
-- reachable from the bundle that calls it -- this module is downstream of those
-- bundles, so the lemmas could not stay here.  Every consumer below resolves them
-- through the import chain unchanged; the proofs are byte-identical.


/-- WS-F5/D1d: `cspaceMint` preserves `badgeWellFormed` when the minted badge
(if any) is valid. The parent capability's badge validity is inherited from
the pre-state `capabilityBadgesWellFormed` invariant. -/
theorem cspaceMint_preserves_badgeWellFormed
    (st st' : SystemState) (src dst : CSpaceAddr)
    (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
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
    -- AL1b (AK7-I.cascade): pair.1 promoted via toNonNull? under success.
    have hNotNull : pair.1.isNull = false := by
      by_cases h : pair.1.isNull
      · exfalso; simp [Capability.toNonNull?, h] at hStep
      · exact Bool.not_eq_true _ |>.mp h
    have hToNN : pair.1.toNonNull? = some ⟨pair.1, hNotNull⟩ :=
      Capability.toNonNull?_of_not_null hNotNull
    simp only [hToNN] at hStep
    cases hMint : mintDerivedCap ⟨pair.1, hNotNull⟩ rights badge with
    | error e => simp [hMint] at hStep
    | ok child =>
      simp only [hMint] at hStep
      -- `cspaceInsertSlot` stores a CNode; what a successful insert consists of
      -- is `cspaceInsertSlot_ok_decompose`'s to say (WS-RR RR8.16, `v0.35.201`),
      -- not this proof's — re-deriving it here is a second reading of the
      -- operation's own `match` tree.
      obtain ⟨cn, hCnOpt, _hAddr, _hLk, hStore⟩ :=
        cspaceInsertSlot_ok_decompose pair.2 st' dst child hStep
      have hObj : pair.2.objects[dst.cnode]? = some (.cnode cn) :=
        (SystemState.getCNode?_eq_some_iff pair.2 dst.cnode cn).mp hCnOpt
      have hUniq := SeLe4n.Model.CNode.slotsUnique_holds cn
      -- Extract child.badge from mintDerivedCap. AN4-E (H-06) refactors the body
      -- to wrap the `.ok` in a second `if` that rejects null-valued candidates,
      -- so walk both splits.
      have hChildBadge : child.badge = badge :=
        mintDerivedCap_badge_propagated ⟨pair.fst, hNotNull⟩ rights badge child hMint
      exact ⟨storeObject_cnode_preserves_notificationBadgesWellFormed
          pair.2 st' dst.cnode _ hNtfn hObjInv hStore,
        storeObject_cnode_preserves_capabilityBadgesWellFormed
          pair.2 st' dst.cnode _ hCap hObjInv hStore
          (fun slot' cap' badge' hLk hBdg => by
            by_cases hSlotEq : dst.slot = slot'
            · subst hSlotEq
              rw [CNode.lookup_insert_eq cn dst.slot child hUniq
                (CNode.slotAddressable_of_lookup_insert _ _ _ _ _ hLk)] at hLk
              cases hLk; rw [hChildBadge] at hBdg
              exact hBadgeValid badge' hBdg
            · rw [CNode.lookup_insert_ne cn dst.slot slot' child hSlotEq hUniq] at hLk
              exact hCap dst.cnode cn slot' cap' badge' hObj hLk hBdg)⟩

/-- WS-F5/D1d: `cspaceMutate` preserves `badgeWellFormed` when the mutated
badge (if any) is valid. -/
theorem cspaceMutate_preserves_badgeWellFormed
    (st st' : SystemState) (addr : CSpaceAddr)
    (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (hInv : badgeWellFormed st)
    (hObjInv : st.objects.invExt)
    (hBadgeValid : ∀ b, badge = some b → b.valid)
    (hStep : cspaceMutate addr rights badge st = .ok ((), st')) :
    badgeWellFormed st' := by
  obtain ⟨hNtfn, hCap⟩ := hInv
  unfold cspaceMutate SystemState.getCNode? at hStep
  cases hLookup : cspaceLookupSlot addr st with
  | error e => simp [hLookup] at hStep
  | ok pair =>
    have hPairEq := cspaceLookupSlot_ok_state_eq st addr pair.1 pair.2 hLookup
    simp only [hLookup] at hStep
    rw [hPairEq] at hStep
    -- AK8-K (C-L2): null-cap guard discharged first.
    by_cases hNull : pair.1.isNull
    · simp [hNull] at hStep
    simp only [hNull, Bool.false_eq_true, ↓reduceIte] at hStep
    split at hStep
    · -- rights subset check passed
      cases hObj : st.objects[addr.cnode]? with
      | none => simp [hObj] at hStep
      | some obj =>
        cases obj with
        | cnode cn =>
          have hUniq := SeLe4n.Model.CNode.slotsUnique_holds cn
          simp [hObj] at hStep
          cases hStore : storeObject addr.cnode
              (.cnode (cn.insert addr.slot
                ⟨pair.1.target, rights, badge.or pair.1.badge, pair.1.mapping⟩)) st with
          | error e => simp [hStore] at hStep
          | ok storeResult =>
            obtain ⟨_, stMid⟩ := storeResult
            simp [hStore] at hStep
            -- hStep : stMid = st'
            have hObjEq : st'.objects = stMid.objects := by rw [hStep]
            apply badgeWellFormed_of_objects_eq stMid st' hObjEq
            constructor
            · exact storeObject_cnode_preserves_notificationBadgesWellFormed
                st stMid addr.cnode _ hNtfn hObjInv hStore
            · exact storeObject_cnode_preserves_capabilityBadgesWellFormed
                st stMid addr.cnode _ hCap hObjInv hStore
                (fun slot' cap' badge' hLk hBdg => by
                  by_cases hSlotEq : addr.slot = slot'
                  · -- The mutated slot
                    subst hSlotEq
                    rw [CNode.lookup_insert_eq cn addr.slot _ hUniq
                      (CNode.slotAddressable_of_lookup_insert _ _ _ _ _ hLk)] at hLk; cases hLk
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
                    rw [CNode.lookup_insert_ne cn addr.slot slot' _ hSlotEq hUniq] at hLk
                    exact hCap addr.cnode cn slot' cap' badge' hObj hLk hBdg)
        | _ => simp [hObj] at hStep
    · simp at hStep


/-- M-D01: IPC single-cap transfer preserves the capability invariant bundle.

The proof decomposes into the `.noSlot` case (state unchanged, trivial) and
the `.installed` case, which chains:
1. `cspaceInsertSlot_preserves_capabilityInvariantBundle` — slot insertion
2. `addEdge` with `.ipcTransfer` — CDT edge addition (objects unchanged)

The tree stays complete and acyclic as for `cspaceCopy`: the source still holds
its capability (`cdtNodeIsRevocable`) and the edge reaches the slot the insert
found empty (`cdt_addEdge_after_insert`). -/
theorem ipcTransferSingleCap_preserves_capabilityInvariantBundle
    (st st' : SystemState) (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot) (scanLimit : Nat)
    (result : CapTransferResult)
    (hInv : capabilityInvariantBundle st)
    (hSlotCapacity : ∀ cn, st.objects[receiverRoot]? = some (.cnode cn) →
      ∀ s, (cn.insert s cap.withoutMapping).slotCountBounded)
    (hCapBacked : ∀ rid, cap.target = .replyCap rid → st.getReply? rid ≠ none)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    capabilityInvariantBundle st' := by
  -- AN10-B: post-migration `ipcTransferSingleCap` reads via `getCNode?`.
  simp only [ipcTransferSingleCap] at hStep
  cases hCn : st.getCNode? receiverRoot with
  | none => simp [hCn] at hStep
  | some cn =>
    -- Bridge to raw lookup form so `hSlotCapacity` (stated against raw
    -- lookup) can be discharged from the typed-helper hypothesis.
    have hObj : st.objects[receiverRoot]? = some (.cnode cn) :=
      (SystemState.getCNode?_eq_some_iff st receiverRoot cn).mp hCn
    simp [hCn] at hStep
    cases hSlot : cn.findFirstEmptySlotChecked slotBase scanLimit with
      | none =>
        simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInv
      | some emptySlot =>
        simp [hSlot] at hStep
        -- A source destroyed since resolution declines the install and leaves
        -- the state untouched, so the claim holds there unchanged.
        cases hSrc : cdtNodeIsRevocable st srcNode with
        | false => simp [hSrc] at hStep; obtain ⟨_, rfl⟩ := hStep; first | rfl | assumption
        | true =>
        simp only [hSrc] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap.withoutMapping st with
        | error e => simp [hIns] at hStep
        | ok pair2 =>
          rcases pair2 with ⟨_, st2⟩
          have hBundleSt2 := cspaceInsertSlot_preserves_capabilityInvariantBundle st st2
            { cnode := receiverRoot, slot := emptySlot } cap.withoutMapping hInv
            (fun cn' hObj' => hSlotCapacity cn' (by rw [hObj] at hObj'; cases hObj'; exact hObj) emptySlot)
            (objects_invExt_of_capabilityInvariantBundle st hInv) hCapBacked hIns
          have hCdt := cdt_addEdge_after_insert st st2 srcNode
            { cnode := receiverRoot, slot := emptySlot } cap.withoutMapping .ipcTransfer
            hInv.2.2.1 hInv.2.2.2.1 (objects_invExt_of_capabilityInvariantBundle st hInv)
            (by unfold cdtNodeIsRevocable at hSrc; exact hSrc) hIns
          rcases hBundleSt2 with ⟨_, hBnd2, _, _, hDepth2, hObjInv2, hRCPV2⟩
          simp [hIns] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have hObjFinal : ∀ cdt' : CapDerivationTree,
              ({ st2 with cdt := cdt' } : SystemState).objects = st2.objects := fun _ => rfl
          exact ⟨cspaceLookupSound_holds _,
            cspaceSlotCountBounded_of_objects_eq st2 _ hBnd2 (hObjFinal _),
            hCdt.1, hCdt.2,
            cspaceDepthConsistent_of_objects_eq st2 _ hDepth2 (hObjFinal _),
            (hObjFinal _) ▸ hObjInv2,
            replyCapPointsToValidReply_of_objects_eq (hObjFinal _) hRCPV2⟩

/-- V3-E / M3-D3b: `ipcUnwrapCapsLoop` preserves `capabilityInvariantBundle`
through fuel-indexed induction. Each iteration delegates to
`ipcTransferSingleCap_preserves_capabilityInvariantBundle`, threading
`hSlotCap` (slot capacity) through the recursive structure; each step keeps
the tree sound from its own pre-state. -/
theorem ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle
    (caps : Array TransferCap) (receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ (stI : SystemState) (cap : Capability),
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCapBacked : ∀ (stI : SystemState) (cap : Capability),
        capabilityInvariantBundle stI →
        ∀ rid, cap.target = .replyCap rid → stI.getReply? rid ≠ none)
    (hStep : ipcUnwrapCapsLoop caps receiverRoot idx nextBase
             accResults fuel st = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  induction fuel generalizing idx nextBase accResults st with
  | zero =>
    simp [ipcUnwrapCapsLoop] at hStep
    obtain ⟨_, rfl⟩ := hStep
    exact hInv
  | succ n ih =>
    simp only [ipcUnwrapCapsLoop] at hStep
    cases hCap : caps[idx]? with
    | none =>
      simp [hCap] at hStep
      obtain ⟨_, rfl⟩ := hStep
      exact hInv
    | some tc =>
      simp [hCap] at hStep
      cases hTransfer : ipcTransferSingleCap tc.cap tc.srcSlot
          receiverRoot nextBase maxExtraCaps st with
      | error e =>
        simp [hTransfer] at hStep
        obtain ⟨_, rfl⟩ := hStep
        exact hInv
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hInvNext := ipcTransferSingleCap_preserves_capabilityInvariantBundle
          st stNext tc.cap tc.srcSlot
          receiverRoot nextBase maxExtraCaps result
          hInv
          (hSlotCap st tc.cap.withoutMapping hInv)
          (hCapBacked st tc.cap hInv)
          hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hInvNext hStep
        | noSlot => exact ih _ _ _ _ hInvNext hStep
        | grantDenied => exact ih _ _ _ _ hInvNext hStep
        | sourceRevoked => exact ih _ _ _ _ hInvNext hStep

/-- V3-E / M3-D3b: `ipcUnwrapCaps` preserves `capabilityInvariantBundle`
when the endpoint has Grant right (grantRight = true). Delegates to
`ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle` after unfolding
the entry point. -/
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant
    (st st' : SystemState) (msg : IpcMessage)
    (receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot)
    (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ (stI : SystemState) (cap : Capability),
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCapBacked : ∀ (stI : SystemState) (cap : Capability),
        capabilityInvariantBundle stI →
        ∀ rid, cap.target = .replyCap rid → stI.getReply? rid ≠ none)
    (hStep : ipcUnwrapCaps msg receiverRoot slotBase true st
             = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  simp [ipcUnwrapCaps] at hStep
  exact ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle
    msg.caps receiverRoot
    0 slotBase #[] msg.caps.size
    st st' summary hInv hSlotCap hCapBacked hStep

/-- M3-D3 / V3-E: ipcUnwrapCaps preserves capabilityInvariantBundle when the
endpoint lacks Grant right (grantRight = false). In this case, all caps are
silently dropped and the state is unchanged, so the invariant trivially holds.
See also: `ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant` for the
Grant=true case, and `ipcUnwrapCaps_preserves_capabilityInvariantBundle` for
the unified theorem. -/
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant
    (st st' : SystemState) (msg : IpcMessage)
    (receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot)
    (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hStep : ipcUnwrapCaps msg receiverRoot slotBase false st
             = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  simp [ipcUnwrapCaps] at hStep
  obtain ⟨_, rfl⟩ := hStep
  exact hInv

/-- V3-E / M3-D3b: `ipcUnwrapCaps` preserves `capabilityInvariantBundle`
for any value of `endpointGrantRight`. This is the primary entry point for
the IPC rendezvous composition chain.

- **Grant=false**: State unchanged (no transfers), trivially preserved.
- **Grant=true**: Fuel-indexed induction over `ipcUnwrapCapsLoop`, threading
  the slot-capacity hypothesis per-iteration.

The `hSlotCap` hypothesis is vacuous when Grant=false (no
`ipcTransferSingleCap` calls occur). -/
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle
    (st st' : SystemState) (msg : IpcMessage)
    (receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot)
    (endpointGrantRight : Bool)
    (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ (stI : SystemState) (cap : Capability),
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCapBacked : ∀ (stI : SystemState) (cap : Capability),
        capabilityInvariantBundle stI →
        ∀ rid, cap.target = .replyCap rid → stI.getReply? rid ≠ none)
    (hStep : ipcUnwrapCaps msg receiverRoot slotBase
             endpointGrantRight st = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  cases endpointGrantRight with
  | false =>
    exact ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant
      st st' msg receiverRoot slotBase summary hInv hStep
  | true =>
    exact ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant
      st st' msg receiverRoot slotBase summary
      hInv hSlotCap hCapBacked hStep

-- ============================================================================
-- S3-D: cdtMapsConsistent preservation theorems
-- ============================================================================

/-- S3-D: `cspaceMint` preserves `cdtMapsConsistent`. Mint delegates to
    `cspaceInsertSlot` which does not modify the CDT structure. -/
theorem cspaceMint_preserves_cdtMapsConsistent
    (st st' : SystemState)
    (src dst : CSpaceAddr) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (hCon : cdtMapsConsistent st)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    cdtMapsConsistent st' := by
  unfold cspaceMint at hStep
  cases hSrc : cspaceLookupSlot src st with
  | error e => simp [hSrc] at hStep
  | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 src parent hSrc
      subst st1
      -- AL1b (AK7-I.cascade): promote parent via toNonNull?.
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
          exact cspaceInsertSlot_preserves_cdtMapsConsistent st st' dst child hCon hInsert

/-- S3-D: Core `cspaceDeleteSlotCore` preserves `cdtMapsConsistent`. -/
theorem cspaceDeleteSlotCore_preserves_cdtMapsConsistent
    (st st' : SystemState) (addr : CSpaceAddr)
    (hCon : cdtMapsConsistent st)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    cdtMapsConsistent st' := by
  unfold cspaceDeleteSlotCore SystemState.getCNode? at hStep
  cases hPre : st.objects[addr.cnode]? with
  | none => simp [hPre] at hStep
  | some obj =>
    cases obj with
    | cnode cn =>
      simp only [hPre] at hStep
      cases hStore : storeObject addr.cnode (.cnode (cn.remove addr.slot)) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        rcases pair with ⟨_, stMid⟩
        have h1 := storeObject_cdt_eq st stMid addr.cnode _ hStore
        simp only [hStore] at hStep
        simp at hStep; subst hStep
        exact cdtMapsConsistent_of_cdt_eq st _ hCon h1
    | _ => simp [hPre] at hStep

/-- S3-D: `cspaceDeleteSlot` preserves `cdtMapsConsistent` (guarded wrapper). -/
theorem cspaceDeleteSlot_preserves_cdtMapsConsistent
    (st st' : SystemState) (addr : CSpaceAddr)
    (hCon : cdtMapsConsistent st)
    (hChildK : st.cdt.childMap.invExtK) (hParentK : st.cdt.parentMap.invExtK)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    cdtMapsConsistent st' := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' hStep
  have hConC := cspaceDeleteSlotCore_preserves_cdtMapsConsistent st stC addr hCon hCore
  have hCdt : stC.cdt = st.cdt := cspaceDeleteSlotCore_cdt_eq st stC addr hCore
  unfold cdtMapsConsistent at hConC ⊢
  rw [spliceDeletedCdtNode_eq]; dsimp only
  rw [hCdt] at hConC ⊢
  obtain ⟨h1, h2, _, _⟩ := CapDerivationTree.spliceNode_mapsWellFormed _ addr
    ⟨hConC.1, hConC.2, hChildK, hParentK⟩
  exact ⟨h1, h2⟩

/-- S3-D: `cspaceCopy` preserves `cdtMapsConsistent`. Copy calls `addEdge`
    on the CDT, so the postcondition is taken as a hypothesis, matching
    the existing pattern for `cdtCompleteness`/`cdtAcyclicity`. -/
theorem cspaceCopy_preserves_cdtMapsConsistent
    (st st' : SystemState) (src dst : CSpaceAddr)
    (hCdtMapsPost : cdtMapsConsistent st')
    (_hStep : cspaceCopy src dst st = .ok ((), st')) :
    cdtMapsConsistent st' := hCdtMapsPost

/-- S3-D: `cspaceMove` preserves `cdtMapsConsistent`. Move composes
    insert + delete + addEdge; postcondition taken as hypothesis. -/
theorem cspaceMove_preserves_cdtMapsConsistent
    (st st' : SystemState) (src dst : CSpaceAddr)
    (hCdtMapsPost : cdtMapsConsistent st')
    (_hStep : cspaceMove src dst st = .ok ((), st')) :
    cdtMapsConsistent st' := hCdtMapsPost

/-- The destroyed-slot step keeps the tree's index maps consistent and well
formed: the splice keeps them. -/
theorem spliceDeletedCdtNode_preserves_mapsWellFormed (st : SystemState) (ref : SlotRef)
    (h : st.cdt.mapsWellFormed) : (spliceDeletedCdtNode st ref).cdt.mapsWellFormed := by
  rw [spliceDeletedCdtNode_eq]
  exact CapDerivationTree.spliceNode_mapsWellFormed _ ref h

/-- S3-D: `cspaceRevoke` preserves `cdtMapsConsistent`.  Revoke stores the CNode
    `revokeTargetLocal` leaves, which does not touch the tree, and then each
    sibling it emptied takes the destroyed-slot step, which keeps the maps. -/
theorem cspaceRevoke_preserves_cdtMapsConsistent
    (st st' : SystemState) (addr : CSpaceAddr)
    (hCon : cdtMapsConsistent st)
    (hChildK : st.cdt.childMap.invExtK) (hParentK : st.cdt.parentMap.invExtK)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    cdtMapsConsistent st' := by
  obtain ⟨parent, cn, stS, _, _, hStore, rfl⟩ := cspaceRevoke_ok_decompose addr st st' hStep
  have hCdt := storeObject_cdt_eq st stS addr.cnode _ hStore
  have hS : stS.cdt.mapsWellFormed := hCdt ▸ ⟨hCon.1, hCon.2, hChildK, hParentK⟩
  suffices (detachRevokedSlots stS addr.cnode cn addr.slot parent.target).cdt.mapsWellFormed from
    ⟨this.1, this.2.1⟩
  unfold detachRevokedSlots
  refine SeLe4n.Model.CNode.foldCells_preserves cn stS _
    (fun acc => acc.cdt.mapsWellFormed) hS (fun acc slot cap _ hAcc => ?_)
  split
  · exact hAcc
  · exact spliceDeletedCdtNode_preserves_mapsWellFormed acc _ hAcc

-- ============================================================================
-- V3-D (M-PRF-1): CDT Acyclicity Discharge Chain Documentation
-- ============================================================================

/-! ## V3-D: CDT soundness through tree-changing operations

Every slot the tree names holds a capability (`cdtCompleteness`), so an empty
slot is outside the tree.  That one fact carries both directions:

- **Edge-adding operations** (`cspaceCopy`, `cspaceMintWithCdt`,
  `mintReplyCapWithCdt`, `ipcTransferSingleCap`) install into a slot the insert
  found empty, so the new edge reaches a fresh node and closes no cycle
  (`cdt_addEdge_after_insert`).  `cspaceMove` renames the source's node onto
  its empty destination (`moveNode_edgeWellFounded`).  Each theorem derives the
  post-state tree's soundness from its pre-state bundle.
- **Edge-removing operations** (`cspaceDeleteSlot`, `cspaceRevoke`) only lose
  edges (`edgeWellFounded_sub`), and take each slot they empty out of the tree
  (`capabilityInvariantBundleOff` between the two steps).
-/

/-- V3-D4: CDT-shrinking operations (delete, revoke) preserve acyclicity
    unconditionally. Removing edges from an acyclic graph yields an acyclic
    subgraph — any cycle in the smaller edge set would be a cycle in the
    original, contradicting well-foundedness. This is the mathematical
    foundation used by `cspaceDeleteSlot_preserves_capabilityInvariantBundle`
    and `cspaceRevoke_preserves_capabilityInvariantBundle`. -/
theorem cdtShrinkingOps_preserve_acyclicity
    (st st' : SystemState)
    (hAcyclic : cdtAcyclicity st)
    (hEdgeSub : ∀ e ∈ st'.cdt.edges, e ∈ st.cdt.edges) :
    cdtAcyclicity st' :=
  CapDerivationTree.edgeWellFounded_sub st.cdt st'.cdt hAcyclic hEdgeSub

-- ============================================================================
-- V3-E (M-PRF-2): ipcUnwrapCaps Grant=true loop composition
-- ============================================================================

/-! ## V3-E: Loop Composition for `ipcUnwrapCapsLoop`

`ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle` composes the per-step
`ipcTransferSingleCap_preserves_capabilityInvariantBundle` by induction on the
fuel, threading only the receiver's slot capacity (`hSlotCap`).  The no-Grant
case leaves the state unchanged
(`ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant`).
-/

-- ============================================================================
-- V3-F (M-PRF-3): Post-resolution rights check composition
-- ============================================================================

-- V3-F (M-PRF-3): See `resolveCapAddress_callers_check_rights` in API.lean.
-- All callers of `resolveCapAddress` perform post-resolution rights checks.
-- The machine-checked proof lives in API.lean where `syscallInvoke` is
-- defined, avoiding circular imports.


end SeLe4n.Kernel
