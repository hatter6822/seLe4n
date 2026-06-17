-- SPDX-License-Identifier: GPL-3.0-or-later
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

/-- WS-SM SM6.D / PR #822 Phase H (#1.b keystone): `cspaceInsertSlot` preserves
`replyCapPointsToValidReply`, given that the inserted cap — if it is a reply cap — is itself
backed (`hCapBacked`).  This is the **unifying** lemma: `cspaceCopy`/`Move`/`Mint`/`mintReplyCap`
all insert through `cspaceInsertSlot` and discharge `hCapBacked` (the inserted cap copies a
backed source, or — for `mintReplyCap` — is backed by construction).  A CNode store never
affects `getReply?` (it reads only `.reply` objects; the stored object is a `.cnode`), so the
backing of every reply cap frames through; the newly-written slot is backed by `hCapBacked`,
every other slot by the pre-state invariant (`CNode.lookup_insert_eq`/`_ne`). -/
theorem cspaceInsertSlot_preserves_replyCapPointsToValidReply
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hRCPV : replyCapPointsToValidReply st)
    (hObjInv : st.objects.invExt)
    (hCapBacked : ∀ rid, cap.target = .replyCap rid → st.getReply? rid ≠ none)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    replyCapPointsToValidReply st' := by
  unfold cspaceInsertSlot at hStep
  cases hPre : st.objects[addr.cnode]? with
  | none => simp [hPre] at hStep
  | some preObj =>
    cases preObj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hPre] at hStep
    | cnode preCn =>
      simp only [hPre] at hStep
      cases hLookup : preCn.lookup addr.slot with
      | some _ => simp [hLookup] at hStep
      | none =>
        simp only [hLookup] at hStep
        cases hStore : storeObject addr.cnode (.cnode (preCn.insert addr.slot cap)) st with
        | error e => simp [hStore] at hStep
        | ok pair =>
          obtain ⟨_, stMid⟩ := pair
          simp only [hStore] at hStep
          have hRefObj : st'.objects = stMid.objects :=
            storeCapabilityRef_preserves_objects stMid st' addr (some cap.target) hStep
          have hMidSelf : stMid.objects[addr.cnode]? = some (.cnode (preCn.insert addr.slot cap)) :=
            storeObject_objects_eq st stMid addr.cnode _ hObjInv hStore
          have hMidNe : ∀ oid, oid ≠ addr.cnode → stMid.objects[oid]? = st.objects[oid]? :=
            fun oid h => storeObject_objects_ne st stMid addr.cnode oid _ h hObjInv hStore
          have hGetReply : ∀ rid : SeLe4n.ReplyId, st'.getReply? rid = st.getReply? rid := by
            intro rid
            simp only [SystemState.getReply?, hRefObj]
            by_cases hc : rid.toObjId = addr.cnode
            · rw [hc, hMidSelf, hPre]
            · rw [hMidNe rid.toObjId hc]
          intro oid cn slot cap' rid hObj hLook hTgt
          rw [hGetReply]
          by_cases hc : oid = addr.cnode
          · subst hc
            rw [hRefObj, hMidSelf] at hObj
            simp only [Option.some.injEq, KernelObject.cnode.injEq] at hObj
            subst hObj
            by_cases hs : slot = addr.slot
            · rw [hs, CNode.lookup_insert_eq preCn addr.slot cap (CNode.slotsUnique_holds preCn)] at hLook
              simp only [Option.some.injEq] at hLook
              subst hLook
              exact hCapBacked rid hTgt
            · rw [CNode.lookup_insert_ne preCn addr.slot slot cap (Ne.symm hs)
                (CNode.slotsUnique_holds preCn)] at hLook
              exact hRCPV addr.cnode preCn slot cap' rid hPre hLook hTgt
          · rw [hRefObj, hMidNe oid hc] at hObj
            exact hRCPV oid cn slot cap' rid hObj hLook hTgt

/-- WS-E2 / H-01: Compositional preservation of `cspaceInsertSlot`.
WS-RC R4.A close-out: slot-uniqueness is now carried structurally on
`CNode.slots : UniqueSlotMap` (`UniqueSlotMap.hWF`), so per-CNode
discharge via `slotsUnique_holds` is direct; the historical state-level
`cspaceSlotUnique` predicate is no longer threaded as a precondition. -/
theorem cspaceInsertSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hInv : capabilityInvariantBundle st)
    (hSlotCapacity : ∀ cn, st.objects[addr.cnode]? = some (.cnode cn) →
      (cn.insert addr.slot cap).slotCountBounded)
    (_hObjInv : st.objects.invExt)
    (hCapBacked : ∀ rid, cap.target = .replyCap rid → st.getReply? rid ≠ none)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hSound, hBounded, hComp, hAcyclic, hDepthPre, hObjInv, hRCPV⟩
  -- WS-H4: Transfer new components through storeObject(CNode) → storeCapabilityRef chain
  have ⟨hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' ∧ st'.objects.invExt := by
    unfold cspaceInsertSlot at hStep
    cases hPre : st.objects[addr.cnode]? with
    | none => simp [hPre] at hStep
    | some preObj =>
      cases preObj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hPre] at hStep
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
  exact ⟨cspaceLookupSound_holds st',
    hBounded', hComp', hAcyclic', hDepth', hObjInv',
    cspaceInsertSlot_preserves_replyCapPointsToValidReply st st' addr cap hRCPV hObjInv hCapBacked hStep⟩

/-- WS-SM SM6.D / PR #822 Phase H (#1.b): `cspaceDeleteSlotCore` preserves
`replyCapPointsToValidReply` — deletion only *removes* a cap (and clears its ref / detaches
its CDT node, neither of which touches the object store beyond the one CNode), so every reply
cap in the post-state already existed in the pre-state (backed by the pre-invariant) and
`getReply?` frames through.  Used by `cspaceDeleteSlot` and the CDT-revoke fold. -/
theorem cspaceDeleteSlotCore_preserves_replyCapPointsToValidReply
    (st st' : SystemState) (addr : CSpaceAddr)
    (hRCPV : replyCapPointsToValidReply st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    replyCapPointsToValidReply st' := by
  unfold cspaceDeleteSlotCore at hStep
  cases hPre : st.objects[addr.cnode]? with
  | none => simp [hPre] at hStep
  | some preObj =>
    cases preObj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hPre] at hStep
    | cnode cn =>
      simp only [hPre] at hStep
      cases hStore : storeObject addr.cnode (.cnode (cn.remove addr.slot)) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        obtain ⟨_, st1⟩ := pair
        simp only [hStore] at hStep
        cases hRef : storeCapabilityRef addr none st1 with
        | error e => simp [hRef] at hStep
        | ok pair2 =>
          obtain ⟨_, st2⟩ := pair2
          simp only [hRef] at hStep
          obtain ⟨rfl⟩ : st' = SystemState.detachSlotFromCdt st2 addr ∧ True := by
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep; exact ⟨hStep.2.symm, trivial⟩
          have hObjChain : (SystemState.detachSlotFromCdt st2 addr).objects = st1.objects := by
            rw [SystemState.detachSlotFromCdt_objects_eq,
              storeCapabilityRef_preserves_objects st1 st2 addr none hRef]
          have hMidSelf : st1.objects[addr.cnode]? = some (.cnode (cn.remove addr.slot)) :=
            storeObject_objects_eq st st1 addr.cnode _ hObjInv hStore
          have hMidNe : ∀ oid, oid ≠ addr.cnode → st1.objects[oid]? = st.objects[oid]? :=
            fun oid h => storeObject_objects_ne st st1 addr.cnode oid _ h hObjInv hStore
          have hGetReply : ∀ rid : SeLe4n.ReplyId,
              (SystemState.detachSlotFromCdt st2 addr).getReply? rid = st.getReply? rid := by
            intro rid
            simp only [SystemState.getReply?, hObjChain]
            by_cases hc : rid.toObjId = addr.cnode
            · rw [hc, hMidSelf, hPre]
            · rw [hMidNe rid.toObjId hc]
          intro oid cn' slot cap' rid hObj hLook hTgt
          rw [hGetReply]
          by_cases hc : oid = addr.cnode
          · subst hc
            rw [hObjChain, hMidSelf] at hObj
            simp only [Option.some.injEq, KernelObject.cnode.injEq] at hObj
            subst hObj
            by_cases hs : slot = addr.slot
            · rw [hs, CNode.lookup_remove_eq_none cn addr.slot (CNode.slotsUnique_holds cn)] at hLook
              exact absurd hLook (by simp)
            · rw [CNode.lookup_remove_ne cn addr.slot slot (Ne.symm hs)
                (CNode.slotsUnique_holds cn)] at hLook
              exact hRCPV addr.cnode cn slot cap' rid hPre hLook hTgt
          · rw [hObjChain, hMidNe oid hc] at hObj
            exact hRCPV oid cn' slot cap' rid hObj hLook hTgt

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

/-- WS-SM SM6.D / PR #822 Phase H (#1.a): a capability resolved from a CSpace slot in a state
satisfying `capabilityInvariantBundle` is reply-backed — if its target is a reply cap, the
backing reply object exists.  This is the shared discharge for the `hCapBacked` hypothesis of
`cspaceInsertSlot_preserves_capabilityInvariantBundle`: `cspaceCopy`/`cspaceMove` insert the
resolved source cap directly, and `cspaceMint` inserts a derivation with the same target
(`mintDerivedCap_target_preserved_with_badge_override`).  It unfolds the read-only
`cspaceLookupSlot` result to the source slot's containing CNode and appeals to the pre-state
`replyCapPointsToValidReply` conjunct. -/
theorem replyCapBacked_of_source_slot
    (st : SystemState) (src : CSpaceAddr) (parent : Capability)
    (hInv : capabilityInvariantBundle st)
    (hSrc : cspaceLookupSlot src st = .ok (parent, st)) :
    ∀ rid, parent.target = .replyCap rid → st.getReply? rid ≠ none := by
  intro rid hTgt
  have hCap : SystemState.lookupSlotCap st src = some parent :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st src parent).1 hSrc
  rw [SystemState.lookupSlotCap] at hCap
  cases hCN : SystemState.lookupCNode st src.cnode with
  | none => rw [hCN] at hCap; exact absurd hCap (by simp)
  | some cn =>
      rw [hCN] at hCap
      have hObjCN : st.objects[src.cnode]? = some (.cnode cn) :=
        (SystemState.lookupCNode_eq_some_iff st src.cnode cn).1 hCN
      exact replyCapPointsToValidReply_of_capabilityInvariantBundle st hInv
        src.cnode cn src.slot parent rid hObjCN hCap hTgt

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
          -- The minted child shares the parent's target; a reply-cap child therefore
          -- inherits the parent slot's backing via the pre-state invariant.
          have hChildTgt : child.target = parent.target :=
            mintDerivedCap_target_preserved_with_badge_override ⟨parent, hNotNull⟩ child rights badge hMint
          exact cspaceInsertSlot_preserves_capabilityInvariantBundle st st' dst child hInv
            (fun cn hObj => hDstCapacity cn child hObj)
            (objects_invExt_of_capabilityInvariantBundle st hInv)
            (fun rid h => replyCapBacked_of_source_slot st src parent hInv hSrc rid
              (by rw [← hChildTgt]; exact h))
            hInsert

/-- WS-SM SM6.D / PR #822 Phase H: `mintReplyCap` preserves `capabilityInvariantBundle`.
The source lookup is read-only (`cspaceLookupSlot_preserves_state`); the only success path
is a single `cspaceInsertSlot` of the derived `.replyCap` at `dst`, so preservation reduces
to the shared `cspaceInsertSlot_preserves_capabilityInvariantBundle` — exactly like
`cspaceMint` (the derivation of the child cap is irrelevant to the insert's bundle
preservation; only the slot write matters). -/
theorem mintReplyCap_preserves_capabilityInvariantBundle
    (st st' : SystemState) (src dst : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hDstCapacity : ∀ cn cap, st.objects[dst.cnode]? = some (.cnode cn) →
      (cn.insert dst.slot cap).slotCountBounded)
    (hStep : mintReplyCap src dst st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold mintReplyCap at hStep
  cases hSrc : cspaceLookupSlot src st with
  | error e => simp [hSrc] at hStep
  | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 src parent hSrc
      subst st1
      cases hTgt : parent.target with
      | object target =>
          cases hRep : st.getReply? (SeLe4n.ReplyId.ofObjId target) with
          | none => simp [hSrc, hTgt, hRep] at hStep
          | some r =>
              have hInsert : cspaceInsertSlot dst
                  { target := .replyCap (SeLe4n.ReplyId.ofObjId target),
                    rights := AccessRightSet.ofList [.read, .write], badge := none } st
                  = .ok ((), st') := by simpa [hSrc, hTgt, hRep] using hStep
              exact cspaceInsertSlot_preserves_capabilityInvariantBundle st st' dst _ hInv
                (fun cn hObj => hDstCapacity cn _ hObj)
                (objects_invExt_of_capabilityInvariantBundle st hInv)
                (fun rid h => by
                  simp only [CapTarget.replyCap.injEq] at h; subst h; rw [hRep]; simp) hInsert
      | cnodeSlot a b => simp [hSrc, hTgt] at hStep
      | replyCap rid => simp [hSrc, hTgt] at hStep


end SeLe4n.Kernel
