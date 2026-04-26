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

/-- WS-F5/D1d: Storing a CNode preserves `notificationBadgesWellFormed`.
CNode stores never modify notification objects. -/
theorem storeObject_cnode_preserves_notificationBadgesWellFormed
    (st st' : SystemState) (targetId : SeLe4n.ObjId) (cn : CNode)
    (hInv : notificationBadgesWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject targetId (.cnode cn) st = .ok ((), st')) :
    notificationBadgesWellFormed st' :=
  storeObject_nonNotification_preserves_notificationBadgesWellFormed
    st st' targetId _ hInv hObjInv hStore (fun ntfn h => by cases h)

/-- WS-F5/D1d: Storing a CNode with all-valid badges preserves
`capabilityBadgesWellFormed`. -/
theorem storeObject_cnode_preserves_capabilityBadgesWellFormed
    (st st' : SystemState) (targetId : SeLe4n.ObjId) (cn : CNode)
    (hInv : capabilityBadgesWellFormed st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject targetId (.cnode cn) st = .ok ((), st'))
    (hValid : ∀ slot cap badge, cn.lookup slot = some cap →
      cap.badge = some badge → badge.valid) :
    capabilityBadgesWellFormed st' := by
  intro oid cn' slot cap badge hObj hLookup hBadge
  by_cases hEq : oid = targetId
  · subst hEq; rw [storeObject_objects_eq st st' oid _ hObjInv hStore] at hObj
    cases hObj; exact hValid slot cap badge hLookup hBadge
  · exact hInv oid cn' slot cap badge
      ((storeObject_objects_ne st st' targetId oid _ hEq hObjInv hStore).symm.trans hObj)
      hLookup hBadge

theorem badgeWellFormed_of_objects_eq
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
    (hSlotUniq : cspaceSlotUnique st)
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
      -- cspaceInsertSlot stores a CNode
      unfold cspaceInsertSlot at hStep
      cases hObj : pair.2.objects[dst.cnode]? with
      | none => simp [hObj] at hStep
      | some obj =>
        cases obj with
        | cnode cn =>
          have hUniq := hSlotUniq dst.cnode cn hObj
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
              -- Extract child.badge from mintDerivedCap. AN4-E (H-06)
              -- refactors the body to wrap the `.ok` in a second `if` that
              -- rejects null-valued candidates, so walk both splits.
              have hChildBadge : child.badge = badge :=
                mintDerivedCap_badge_propagated ⟨pair.fst, hNotNull⟩ rights badge child hMint
              constructor
              · exact storeObject_cnode_preserves_notificationBadgesWellFormed
                  pair.2 stMid dst.cnode _ hNtfn hObjInv hStore
              · exact storeObject_cnode_preserves_capabilityBadgesWellFormed
                  pair.2 stMid dst.cnode _ hCap hObjInv hStore
                  (fun slot' cap' badge' hLk hBdg => by
                    by_cases hSlotEq : dst.slot = slot'
                    · subst hSlotEq
                      rw [CNode.lookup_insert_eq cn dst.slot child hUniq] at hLk
                      cases hLk; rw [hChildBadge] at hBdg
                      exact hBadgeValid badge' hBdg
                    · rw [CNode.lookup_insert_ne cn dst.slot slot' child hSlotEq hUniq] at hLk
                      exact hCap dst.cnode cn slot' cap' badge' hObj hLk hBdg)
        | _ => simp [hObj] at hStep

/-- WS-F5/D1d: `cspaceMutate` preserves `badgeWellFormed` when the mutated
badge (if any) is valid. -/
theorem cspaceMutate_preserves_badgeWellFormed
    (st st' : SystemState) (addr : CSpaceAddr)
    (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (hInv : badgeWellFormed st)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
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
          have hUniq := hSlotUniq addr.cnode cn hObj
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
                st stMid addr.cnode _ hNtfn hObjInv hStore
            · exact storeObject_cnode_preserves_capabilityBadgesWellFormed
                st stMid addr.cnode _ hCap hObjInv hStore
                (fun slot' cap' badge' hLk hBdg => by
                  by_cases hSlotEq : addr.slot = slot'
                  · -- The mutated slot
                    subst hSlotEq
                    rw [CNode.lookup_insert_eq cn addr.slot _ hUniq] at hLk; cases hLk
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
            (objects_invExt_of_capabilityInvariantBundle st hInv) hIns
          rcases hBundleSt2 with ⟨hU2, _, hBnd2, _, _, hDepth2, hObjInv2⟩
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
                cspaceDepthConsistent_of_objects_eq st2 _ hDepth2 hObjFinal,
                hObjFinal ▸ hObjInv2⟩

/-- V3-E / M3-D3b: `ipcUnwrapCapsLoop` preserves `capabilityInvariantBundle`
through fuel-indexed induction. Each iteration delegates to
`ipcTransferSingleCap_preserves_capabilityInvariantBundle`, threading
`hSlotCap` (slot capacity) and `hCdtPost` (CDT completeness + acyclicity)
through the recursive structure.

The `hCdtPost` hypothesis is externalized following the standard pattern for
CDT-expanding operations (see `cspaceCopy_preserves_capabilityInvariantBundle`).
The caller (API layer) is responsible for discharging CDT obligations. -/
theorem ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ (stI : SystemState) (cap : Capability),
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCdtPost : ∀ (stI stJ : SystemState) (cap : Capability)
        (senderSlot : CSpaceAddr) (slotBase : SeLe4n.Slot)
        (scanLimit : Nat) (result : CapTransferResult),
        capabilityInvariantBundle stI →
        ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit stI
          = .ok (result, stJ) →
        cdtCompleteness stJ ∧ cdtAcyclicity stJ)
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase
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
    | some cap =>
      simp [hCap] at hStep
      cases hTransfer : ipcTransferSingleCap cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st with
      | error e =>
        simp [hTransfer] at hStep
        obtain ⟨_, rfl⟩ := hStep
        exact hInv
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hInvNext := ipcTransferSingleCap_preserves_capabilityInvariantBundle
          st stNext cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps result
          hInv
          (hSlotCap st cap hInv)
          (hCdtPost st stNext cap
            { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
            nextBase maxExtraCaps result hInv hTransfer)
          hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hInvNext hStep
        | noSlot => exact ih _ _ _ _ hInvNext hStep
        | grantDenied => exact ih _ _ _ _ hInvNext hStep

/-- V3-E / M3-D3b: `ipcUnwrapCaps` preserves `capabilityInvariantBundle`
when the endpoint has Grant right (grantRight = true). Delegates to
`ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle` after unfolding
the entry point. -/
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant
    (st st' : SystemState) (msg : IpcMessage)
    (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot)
    (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ (stI : SystemState) (cap : Capability),
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCdtPost : ∀ (stI stJ : SystemState) (cap : Capability)
        (senderSlot : CSpaceAddr) (slotBase' : SeLe4n.Slot)
        (scanLimit : Nat) (result : CapTransferResult),
        capabilityInvariantBundle stI →
        ipcTransferSingleCap cap senderSlot receiverRoot slotBase' scanLimit stI
          = .ok (result, stJ) →
        cdtCompleteness stJ ∧ cdtAcyclicity stJ)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase true st
             = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  simp [ipcUnwrapCaps] at hStep
  exact ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle
    msg.caps senderRoot receiverRoot
    0 slotBase #[] msg.caps.size
    st st' summary hInv hSlotCap hCdtPost hStep

/-- M3-D3 / V3-E: ipcUnwrapCaps preserves capabilityInvariantBundle when the
endpoint lacks Grant right (grantRight = false). In this case, all caps are
silently dropped and the state is unchanged, so the invariant trivially holds.
See also: `ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant` for the
Grant=true case, and `ipcUnwrapCaps_preserves_capabilityInvariantBundle` for
the unified theorem. -/
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant
    (st st' : SystemState) (msg : IpcMessage)
    (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot)
    (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase false st
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
  slot capacity and CDT postcondition hypotheses per-iteration.

The `hSlotCap` and `hCdtPost` hypotheses are vacuous when Grant=false
(no `ipcTransferSingleCap` calls occur). -/
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle
    (st st' : SystemState) (msg : IpcMessage)
    (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot)
    (endpointGrantRight : Bool)
    (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ (stI : SystemState) (cap : Capability),
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCdtPost : ∀ (stI stJ : SystemState) (cap : Capability)
        (senderSlot : CSpaceAddr) (slotBase' : SeLe4n.Slot)
        (scanLimit : Nat) (result : CapTransferResult),
        capabilityInvariantBundle stI →
        ipcTransferSingleCap cap senderSlot receiverRoot slotBase' scanLimit stI
          = .ok (result, stJ) →
        cdtCompleteness stJ ∧ cdtAcyclicity stJ)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase
             endpointGrantRight st = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  cases endpointGrantRight with
  | false =>
    exact ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant
      st st' msg senderRoot receiverRoot slotBase summary hInv hStep
  | true =>
    exact ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant
      st st' msg senderRoot receiverRoot slotBase summary
      hInv hSlotCap hCdtPost hStep

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
  unfold cspaceDeleteSlotCore at hStep
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
        -- storeCapabilityRef preserves CDT
        unfold storeCapabilityRef at hStep
        simp at hStep; rcases hStep with ⟨_, rfl⟩
        -- detachSlotFromCdt doesn't modify cdt
        unfold SystemState.detachSlotFromCdt
        split
        · exact cdtMapsConsistent_of_cdt_eq st _ hCon h1
        · exact cdtMapsConsistent_of_cdt_eq st _ hCon h1
    | _ => simp [hPre] at hStep

/-- S3-D: `cspaceDeleteSlot` preserves `cdtMapsConsistent` (guarded wrapper). -/
theorem cspaceDeleteSlot_preserves_cdtMapsConsistent
    (st st' : SystemState) (addr : CSpaceAddr)
    (hCon : cdtMapsConsistent st)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    cdtMapsConsistent st' := by
  unfold cspaceDeleteSlot at hStep
  split at hStep
  · simp at hStep
  · exact cspaceDeleteSlotCore_preserves_cdtMapsConsistent st st' addr hCon hStep

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

/-- S3-D: `cspaceRevoke` preserves `cdtMapsConsistent`. Revoke uses
    `revokeTargetLocal` + `revokeAndClearRefsState`, neither of which
    modifies the CDT structure. -/
theorem cspaceRevoke_preserves_cdtMapsConsistent
    (st st' : SystemState) (addr : CSpaceAddr)
    (hCon : cdtMapsConsistent st)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    cdtMapsConsistent st' := by
  unfold cspaceRevoke at hStep
  cases hLook : cspaceLookupSlot addr st with
  | error e => simp [hLook] at hStep
  | ok pair =>
      rcases pair with ⟨parent, stLook⟩
      have hStLook : stLook = st := cspaceLookupSlot_preserves_state st stLook addr parent hLook
      subst stLook
      simp [hLook] at hStep
      cases hPre : st.objects[addr.cnode]? with
      | none => simp [hPre] at hStep
      | some obj =>
        cases obj with
        | cnode cn =>
          simp [hPre] at hStep
          -- revokeTargetLocal modifies the CNode, not the CDT
          cases hStore : storeObject addr.cnode (.cnode (cn.revokeTargetLocal addr.slot parent.target)) st with
          | error e => simp [hStore] at hStep
          | ok pair =>
            rcases pair with ⟨_, stMid⟩
            have hConMid := cdtMapsConsistent_of_storeObject st stMid addr.cnode _ hCon hStore
            -- revokeAndClearRefsState preserves CDT
            simp [hStore] at hStep; cases hStep
            have hCdtEq := (revokeAndClearRefsState_cdt_eq cn addr.slot parent.target addr.cnode stMid).1
            exact cdtMapsConsistent_of_cdt_eq stMid _ hConMid hCdtEq
        | _ => simp [hPre] at hStep

-- ============================================================================
-- V3-D (M-PRF-1): CDT Acyclicity Discharge Chain Documentation
-- ============================================================================

/-! ## V3-D: CDT Acyclicity Discharge Chain

The `cdtAcyclicity` hypothesis is handled differently depending on
whether the operation **expands** or **shrinks** the CDT:

### CDT-expanding operations (externalized hypothesis)

| Operation | Theorem | Pattern |
|-----------|---------|---------|
| `cspaceCopy` | `cspaceCopy_preserves_capabilityInvariantBundle` | `hCdtPost` parameter |
| `cspaceMove` | `cspaceMove_preserves_capabilityInvariantBundle` | `hCdtPost` parameter |
| `cspaceMintWithCdt` | `cspaceMintWithCdt_preserves_capabilityInvariantBundle` | `hCdtPost` parameter |
| `ipcTransferSingleCap` | (via `cspaceInsertSlot` + CDT `addEdge`) | Composition-level |

These operations add CDT edges. The `hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st'`
hypothesis is discharged at the API dispatch layer, where the full
`proofLayerInvariantBundle` provides the CDT acyclicity from the pre-state,
and the caller proves the specific edge addition preserves acyclicity (e.g.,
adding a parent→child edge when the child has no descendants).

### CDT-shrinking operations (proven internally)

| Operation | Theorem | Proof method |
|-----------|---------|--------------|
| `cspaceDeleteSlot` | `cspaceDeleteSlot_preserves_capabilityInvariantBundle` | `edgeWellFounded_sub` |
| `cspaceRevoke` | `cspaceRevoke_preserves_capabilityInvariantBundle` | `edgeWellFounded_sub` |

Edge removal trivially preserves well-foundedness (a subset of a
well-founded relation is well-founded).

### ipcTransferSingleCap (V3-D5)

`ipcTransferSingleCap` adds a CDT edge via `cdt.addEdge srcNode dstNode .ipcTransfer`.
The `capabilityInvariantBundle` preservation is composed at the IPC operation
level, where the `hCdtPost` hypothesis is threaded through the cap transfer
loop (see V3-E for the loop composition proof).
-/

/-- V3-D2/D3: Documentation theorem: CDT-expanding operations preserve
    `capabilityInvariantBundle` when the caller provides post-state CDT
    properties. This is the composition pattern used by `cspaceCopy`,
    `cspaceMove`, and `cspaceMintWithCdt`. -/
theorem cdtExpandingOp_preserves_bundle_with_hypothesis
    (_st _st' : SystemState) (_hInv : capabilityInvariantBundle _st)
    (hCdtPost : cdtCompleteness _st' ∧ cdtAcyclicity _st')
    (_hObjEq : _st'.objects = _st.objects) :
    cdtCompleteness _st' ∧ cdtAcyclicity _st' := hCdtPost

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

The per-step theorem `ipcTransferSingleCap_preserves_capabilityInvariantBundle`
(line 1935 above) is fully proved. The loop composition requires threading
`hSlotCapacity` and `hCdtPost` through each iteration of `ipcUnwrapCapsLoop`.

**Loop invariant**: at each step `i` of the loop:
- `capabilityInvariantBundle` holds for the intermediate state
- The receiver CNode can accommodate further insertions (`hSlotCapacity`)
- CDT post-conditions are supplied per-step by the caller

**Base case** (fuel = 0 or idx ≥ caps.size): the loop returns unchanged
state, trivially preserving the invariant.

**Inductive step**: given the invariant holds at step `i`, and the per-step
proof establishes preservation for `ipcTransferSingleCap`, the invariant
holds at step `i+1`.

**Key design**: `ipcUnwrapCapsLoop` is `private` in `CapTransfer.lean`.
The composition proof works at the `ipcUnwrapCaps` level using the public
preservation theorems for scheduler, services, and objects that already
exist (lines 93-291 of `CapTransfer.lean`). The capability bundle
preservation for the Grant=true path threads `hCdtPost` per-iteration.

The noGrant case is already proven above as
`ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant`.
-/

-- V3-E2: The loop invariant for `ipcUnwrapCapsLoop` is `capabilityInvariantBundle`.
-- The grant=false case is proven by `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant`.
-- The grant=true loop composition requires per-step CDT preservation hypotheses
-- (same pattern as `cdtExpandingOp_preserves_bundle_with_hypothesis`).
-- Individual loop preservation proofs (scheduler, services, objects) are proven
-- in CapTransfer.lean (9 private theorems + 7 public wrappers).

-- ============================================================================
-- V3-F (M-PRF-3): Post-resolution rights check composition
-- ============================================================================

-- V3-F (M-PRF-3): See `resolveCapAddress_callers_check_rights` in API.lean.
-- All callers of `resolveCapAddress` perform post-resolution rights checks.
-- The machine-checked proof lives in API.lean where `syscallInvoke` is
-- defined, avoiding circular imports.


end SeLe4n.Kernel
