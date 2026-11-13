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
preservation stratum covering three operation families: (1)
`cspaceMint`/`cspaceMutate` badge-wellformedness preservation; (2)
`ipcTransferSingleCap` / `ipcUnwrapCapsLoop` / `ipcUnwrapCaps` (grant and
no-grant variants) capability-invariant-bundle preservation; (3) the
CDT-shrinking composition witnesses and the V3-D / V3-E / V3-F commentary
blocks.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

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
              exact hCap dst.cnode (.cnode cn) slot' cap' badge' hObj hLk hBdg)⟩

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
                ({ pair.1 with rights := rights }.withBadge (badge.or pair.1.badge)))) st with
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
                      exact hCap addr.cnode (.cnode cn) addr.slot pair.1 badge' hObj hSlotCap hBdg
                  · -- Other slot: unchanged
                    rw [CNode.lookup_insert_ne cn addr.slot slot' _ hSlotEq hUniq] at hLk
                    exact hCap addr.cnode (.cnode cn) slot' cap' badge' hObj hLk hBdg)
        | _ => simp [hObj] at hStep
    · simp at hStep


/-- A free-index write keeps every occupied slot's target: it rewrites one
occupied slot's index and keeps its target. -/
theorem setCapFreeIndex_slotTarget {st : SystemState} {a : CSpaceAddr} {cn : CNode} {c : Capability}
    (idx : Nat) (hObjInv : st.objects.invExt) (hPre : st.objects[a.cnode]? = some (.cnode cn))
    (hLk : cn.lookup a.slot = some c) (r : SlotRef) {d : Capability}
    (h : st.slotCapAt r = some d) :
    ∃ d', (setCapFreeIndex st a idx).slotCapAt r = some d' ∧ (d'.target = d.target ∧ d'.cnodeGuard = d.cnodeGuard ∧ d'.cnodeGuardSize = d.cnodeGuardSize) := by
  have hS := setCapFreeIndex_eq_storeObject (idx := idx) hPre
  rw [CNode.setFreeIndex_of_lookup hLk] at hS
  by_cases e : r = a
  · subst e
    have h1 : (setCapFreeIndex st r idx).slotCapAt r = some (c.withFreeIndex idx) := by
      rw [SystemState.slotCapAt_of_object (storeObject_objects_eq _ _ _ _ hObjInv hS)]
      exact CNode.lookup_insert_eq cn r.slot _ (CNode.slotsUnique_holds _)
        (CNode.slotAddressable_of_lookup _ _ _ hLk)
    have h0 : st.slotCapAt r = some c := (SystemState.slotCapAt_of_object hPre).trans hLk
    rw [h0] at h; cases h
    exact ⟨_, h1, Capability.withFreeIndex_target _ _, rfl, rfl⟩
  · exact ⟨d, (SystemState.slotCapAt_storeObject_ne hObjInv hPre hS
      (fun s' hs => CNode.lookup_insert_ne cn a.slot s' _ (Ne.symm hs) (CNode.slotsUnique_holds _))
      r e).trans h, rfl, rfl, rfl⟩

/-- Setting a derivation's source full keeps every occupied slot's target. -/
theorem untypedSourceSetFull_slotTarget {st : SystemState} {a : CSpaceAddr} {cn : CNode}
    {c : Capability} (cap : Capability) (hObjInv : st.objects.invExt)
    (hPre : st.objects[a.cnode]? = some (.cnode cn)) (hLk : cn.lookup a.slot = some c)
    (r : SlotRef) {d : Capability} (h : st.slotCapAt r = some d) :
    ∃ d', (untypedSourceSetFull st a cap).slotCapAt r = some d' ∧ (d'.target = d.target ∧ d'.cnodeGuard = d.cnodeGuard ∧ d'.cnodeGuardSize = d.cnodeGuardSize) :=
  untypedSourceSetFull_of (P := fun s => ∃ d', s.slotCapAt r = some d' ∧ (d'.target = d.target ∧ d'.cnodeGuard = d.cnodeGuard ∧ d'.cnodeGuardSize = d.cnodeGuardSize))
    ⟨d, h, rfl, rfl, rfl⟩ fun idx => setCapFreeIndex_slotTarget idx hObjInv hPre hLk r h

/-- **A transfer keeps every occupied slot's target**: it installs into an
empty slot, records an edge, and may set its source full. -/
theorem ipcTransferSingleCap_slotTarget {st st' : SystemState} {cap : Capability}
    {srcNode : SlotRef} {dst : CSpaceAddr} (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap srcNode dst st = .ok ((), st')) (r : SlotRef)
    {d : Capability} (h : st.slotCapAt r = some d) :
    ∃ d', st'.slotCapAt r = some d' ∧ (d'.target = d.target ∧ d'.cnodeGuard = d.cnodeGuard ∧ d'.cnodeGuardSize = d.cnodeGuardSize) := by
  obtain ⟨_, st2, -, hSrc, -, hIns, rfl⟩ := ipcTransferSingleCap_ok_cases hStep
  obtain ⟨c, hLc⟩ := Option.isSome_iff_exists.mp
    (by unfold cdtNodeIsRevocable at hSrc; exact hSrc)
  obtain ⟨cnS, hOS, hLS⟩ := cspaceInsertSlot_cdtAddChild_src .ipcTransfer hObjInv hLc hIns
  have hInv2 := cspaceInsertSlot_preserves_objects_invExt _ _ _ _ hObjInv hIns
  have hA := SystemState.cdtAddChild_agreeObjects hInv2 srcNode dst .ipcTransfer
  refine untypedSourceSetFull_slotTarget cap hA.2 hOS hLS r ?_
  rw [hA.1.slotCapAt r]
  have hrd : r ≠ dst := by
    rintro rfl
    obtain ⟨cn0, hGet, -, hE, -⟩ := cspaceInsertSlot_ok_decompose _ _ _ _ hIns
    rw [SystemState.slotCapAt_eq_bind] at h
    have hG := (SystemState.getCNode?_eq_some_iff st r.cnode cn0).mp hGet
    simp [hG, KernelObject.slotCap, hE] at h
  exact (cspaceInsertSlot_slotCapAt_ne hObjInv hIns r hrd).trans h

/-- M-D01: IPC single-cap transfer preserves the capability invariant bundle.

An install that succeeds chains:
1. `cspaceInsertSlot_preserves_capabilityBundleOffCoverage` — slot insertion
2. `addEdge` with `.ipcTransfer` — CDT edge addition (objects unchanged)
3. `untypedSourceSetFull_preserves_capabilityInvariantBundle` — an untyped
   source capability's free index is set to its region size (seL4's rule:
   a derived untyped capability leaves its source full); for any other
   capability this step is the identity

The tree stays complete and acyclic as for `cspaceCopy`: the source still holds
its capability (`cdtNodeIsRevocable`) and the edge reaches the slot the insert
found empty (`cdt_addEdge_after_insert`). -/
theorem ipcTransferSingleCap_preserves_capabilityInvariantBundle
    (st st' : SystemState) (cap : Capability) (srcNode : SlotRef) (dst : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hSrcCap : ∃ c, st.slotCapAt srcNode = some c ∧ (cap.target = c.target ∧ cap.cnodeGuard = c.cnodeGuard ∧ cap.cnodeGuardSize = c.cnodeGuardSize))
    (hStep : ipcTransferSingleCap cap srcNode dst st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  obtain ⟨_, st2, -, hSrc, hRef, hIns, rfl⟩ := ipcTransferSingleCap_ok_cases hStep
  have hObjInv := objects_invExt_of_capabilityInvariantBundle st hInv
  obtain ⟨c, hLc⟩ := Option.isSome_iff_exists.mp
    (by unfold cdtNodeIsRevocable at hSrc; exact hSrc)
  obtain ⟨c0, hc0, hT0, hG0, hS0⟩ := hSrcCap
  -- The transferred capability names its source slot's object under its guard,
  -- so its kind and geometry are the source's, which the bundle backs.
  have hCapBacked : capTargetKindBackedAt st cap.withoutMapping.target := by
    rw [show cap.withoutMapping.target = cap.target from Capability.withMapping_target cap none, hT0]
    exact hInv.targetKindBacked.slotCapAt hc0
  have hCapGeo : cnodeCapGeometryAt st cap.withoutMapping :=
    cnodeCapGeometryAt_of_fields (hInv.capGeometry.slotCapAt hc0)
      ((Capability.withMapping_target cap none).trans hT0) hG0 hS0
  rw [Option.some.inj (hc0.symm.trans (SystemState.slotCapAt_of_lookupSlotCap hLc))] at hT0
  have hBundleSt2 := cspaceInsertSlot_preserves_capabilityBundleOffCoverage st st2
    dst cap.withoutMapping hInv.offCoverage hCapBacked hCapGeo hIns
  have hCdt := cdt_addEdge_after_insert st st2 srcNode dst cap.withoutMapping .ipcTransfer
    hInv.2.1 hInv.2.2.1 hObjInv
    (by unfold cdtNodeIsRevocable at hSrc; exact hSrc) hIns hInv.linksAgree
  have hShape := treeShape_addEdge_after_copy st st2 srcNode dst cap.withoutMapping .ipcTransfer
    hInv.treeShape hInv.2.1 hObjInv hInv.linksAgree hLc
    ((Capability.withMapping_target cap none).trans hT0) hT0 hRef hIns
  rcases hBundleSt2 with ⟨⟨_, _, _, hDepth2, hObjInv2, hRCPV2⟩, -, -⟩
  have hIX := hObjInv2
  have hObjFinal : ∀ cdt' : CapDerivationTree,
      ({ st2 with cdt := cdt' } : SystemState).objects = st2.objects := fun _ => rfl
  have hMid := capabilityBundleOffSource_of_linkReach ?_
    (SystemState.cdtAddChild_reach st2 srcNode _ .ipcTransfer) hIX hCdt.2.2 hShape
  · -- `cdtNodeIsRevocable`: the source holds a capability, and still does after
    -- the install and the edge, so setting it full restores the bundle.
    obtain ⟨cnS, hOS, hLS⟩ := cspaceInsertSlot_cdtAddChild_src .ipcTransfer hObjInv hLc hIns
    exact untypedSourceSetFull_preserves_capabilityInvariantBundle _ srcNode cnS cap hMid hOS hLS
      hT0
  · exact ⟨cspaceLookupSound_holds _,
      hCdt.1, hCdt.2.1,
      cnodeCapGeometry_of_objects_eq st2 _ hDepth2 (hObjFinal _),
      (hObjFinal _) ▸ hObjInv2,
      capTargetKindBacked_of_objects_eq (hObjFinal _) hRCPV2⟩

/-- A badge written to the receiver's buffer keeps the bundle: it goes to the
physical-write ledger, which the bundle does not read. -/
theorem recordUnwrappedBadge_preserves_capabilityInvariantBundle (st : SystemState)
    (tcb : TCB) (i : Nat) (b : SeLe4n.Badge) (hInv : capabilityInvariantBundle st) :
    capabilityInvariantBundle (recordUnwrappedBadge st tcb i b) := by
  unfold recordUnwrappedBadge
  split
  · exact hInv
  · exact hInv

/-- A badge written to the receiver's buffer keeps every slot. -/
theorem recordUnwrappedBadge_slotCapAt (st : SystemState) (tcb : TCB) (i : Nat)
    (b : SeLe4n.Badge) (r : SlotRef) :
    (recordUnwrappedBadge st tcb i b).slotCapAt r = st.slotCapAt r := by
  unfold recordUnwrappedBadge
  split <;> rfl

/-- V3-E / M3-D3b: `ipcUnwrapCaps` preserves `capabilityInvariantBundle`.

A badge write keeps it (`recordUnwrappedBadge_preserves_capabilityInvariantBundle`)
and an install keeps it (`ipcTransferSingleCap_preserves_capabilityInvariantBundle`),
threading the sources' occupancy (`hNames`) through the loop
(`ipcUnwrapCaps_rel`).  Each transferred capability names its source slot's
object, so the bundle's `capTargetKindBacked` backs it: the transfer owes no
backing premise of its own. -/
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle
    (st st' : SystemState) (caps : Array TransferCap) (endpointId : Option SeLe4n.ObjId)
    (rtcb : TCB) (slot? : Option CSpaceAddr) (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hNames : ∀ (i : Nat) (tc : TransferCap), caps[i]? = some tc →
        ∃ c, st.slotCapAt tc.srcSlot = some c ∧ (tc.cap.target = c.target ∧ tc.cap.cnodeGuard = c.cnodeGuard ∧ tc.cap.cnodeGuardSize = c.cnodeGuardSize))
    (hStep : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  let N : SystemState → Prop := fun s => ∀ (i : Nat) (tc : TransferCap), caps[i]? = some tc →
    ∃ c, s.slotCapAt tc.srcSlot = some c ∧ (tc.cap.target = c.target ∧ tc.cap.cnodeGuard = c.cnodeGuard ∧ tc.cap.cnodeGuardSize = c.cnodeGuardSize)
  have hR := ipcUnwrapCaps_rel
    (fun a b => capabilityInvariantBundle b → N b → capabilityInvariantBundle a ∧ N a)
    (fun _ h1 h2 => ⟨h1, h2⟩)
    (fun _ _ _ h1 h2 hA hN => let r := h2 hA hN; h1 r.1 r.2)
    (fun s i b hA hN => ⟨recordUnwrappedBadge_preserves_capabilityInvariantBundle s rtcb i b hA,
      fun j tc hj => by rw [recordUnwrappedBadge_slotCapAt]; exact hN j tc hj⟩)
    (fun dst s s' tc _ ⟨i, hi⟩ hT hA hN =>
      ⟨ipcTransferSingleCap_preserves_capabilityInvariantBundle s s' tc.cap tc.srcSlot dst hA
          (hN i tc hi) hT,
        fun j tc' hj => by
          obtain ⟨c, hc, hTg, hGg, hSg⟩ := hN j tc' hj
          obtain ⟨c', hc', hT', hG', hS'⟩ := ipcTransferSingleCap_slotTarget
            (objects_invExt_of_capabilityInvariantBundle s hA) hT _ hc
          exact ⟨c', hc', hTg.trans hT'.symm, hGg.trans hG'.symm, hSg.trans hS'.symm⟩⟩)
    hStep
  exact (hR hInv hNames).1

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
fuel, threading each capability's target being its source slot's (`hNames`, kept by every transfer,
`ipcTransferSingleCap_slotTarget`).  The no-Grant
case leaves the state unchanged
(`ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant`).
-/

-- ============================================================================
-- V3-F (M-PRF-3): Post-resolution rights check composition
-- ============================================================================

-- V3-F (M-PRF-3): See `resolveAddressBits_callers_check_rights` in API.lean.
-- All callers of `resolveAddressBits` perform post-resolution rights checks.
-- The machine-checked proof lives in API.lean where `syscallInvokeTyped` is
-- defined, avoiding circular imports.


end SeLe4n.Kernel
