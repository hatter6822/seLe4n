-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.Insert

/-!
AN4-F.3 (CAP-M03) child module extracted from
`SeLe4n.Kernel.Capability.Invariant.Preservation`. Contains compositional
preservation theorems for capability deletion operations
(`cspaceDeleteSlotCore`, `cspaceDeleteSlot`) and the core
`cspaceRevoke` primitive that loops delete over all derived children.
Private `cdtNodeSlot` preservation helpers are promoted to public so
the Revoke sibling module can invoke them for transitive CDT-revocation
fold induction, and `capabilityInvariantBundle_of_cdt_update` (a CDT-only
update keeps the bundle when the new tree is acyclic) sits here for the
delete's splice and the revocation sweep alike.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Internal

/-- Core preservation theorem for `cspaceDeleteSlotCore` (no CDT guard).
Used directly by internal callers (processRevokeNode, cspaceMove, cspaceRevokeCdtStrict)
and indirectly by the `cspaceDeleteSlot` wrapper. -/
theorem cspaceDeleteSlotCore_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hSound, hBounded, hComp, hAcyclic, hDepthPre, hObjInv, hRCPV⟩
  -- WS-H4: Prove new components through storeObject → detachSlotFromCdt
  have ⟨hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' ∧ st'.objects.invExt := by
    unfold cspaceDeleteSlotCore SystemState.getCNode? at hStep
    cases hPre : st.objects[addr.cnode]? with
    | none => simp [hPre] at hStep
    | some preObj =>
      cases preObj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp [hPre] at hStep
      | cnode preCn =>
        simp [hPre] at hStep
        cases hStore : storeObject addr.cnode (.cnode (preCn.remove addr.slot)) st with
        | error e => simp [hStore] at hStep
        | ok pair =>
          obtain ⟨_, stMid⟩ := pair
          simp [hStore] at hStep; cases hStep
          have hBndMid := cspaceSlotCountBounded_of_storeObject_cnode st stMid addr.cnode
            (preCn.remove addr.slot) hBounded hObjInv hStore (CNode.remove_slotCountBounded preCn addr.slot (hBounded addr.cnode preCn hPre))
          have hCompMid := cdtCompleteness_of_storeObject st stMid addr.cnode _ hComp hObjInv hStore
            (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
          have hAcyclicMid := cdtAcyclicity_of_cdt_eq st stMid hAcyclic
            (storeObject_cdt_eq st stMid addr.cnode _ hStore)
          have hDepthMid := cspaceDepthConsistent_of_storeObject_sameCNode
            st stMid addr.cnode preCn (preCn.remove addr.slot) hDepthPre hObjInv hPre hStore rfl rfl rfl rfl
          have hObjInvMid := storeObject_preserves_objects_invExt st stMid addr.cnode _ hObjInv hStore
          have hNodeSlotKMid : stMid.cdtNodeSlot.invExtK := by
            rw [(storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1]; exact hNodeSlotK
          exact ⟨cspaceSlotCountBounded_of_detachSlotFromCdt stMid addr hBndMid,
            cdtCompleteness_of_detachSlotFromCdt stMid addr hCompMid hNodeSlotKMid,
            cdtAcyclicity_of_detachSlotFromCdt stMid addr hAcyclicMid,
            cspaceDepthConsistent_of_detachSlotFromCdt stMid addr hDepthMid,
            (SystemState.detachSlotFromCdt_objects_eq stMid addr) ▸ hObjInvMid⟩
  exact ⟨cspaceLookupSound_holds st',
    hBounded', hComp', hAcyclic', hDepth', hObjInv',
    cspaceDeleteSlotCore_preserves_replyCapPointsToValidReply st st' addr hRCPV hObjInv hStep⟩

/-- Helper: CDT-only state updates preserve capabilityInvariantBundle,
given that the new CDT is acyclic. -/
theorem capabilityInvariantBundle_of_cdt_update
    (st : SystemState) (cdt' : CapDerivationTree)
    (hInv : capabilityInvariantBundle st)
    (hAcyclic' : cdt'.edgeWellFounded) :
    capabilityInvariantBundle { st with cdt := cdt' } := by
  rcases hInv with ⟨_, hBnd, hComp, _, hDepthPre, hObjInvPre⟩
  have hObjEq : ({ st with cdt := cdt' } : SystemState).objects = st.objects := rfl
  -- WS-RC R4.A.6: cspaceSlotUnique conjunct removed from bundle; the new
  -- 6-tuple skips the legacy uniqueness slot.
  exact ⟨cspaceLookupSound_holds _,
    hBnd, hComp, hAcyclic',
    cspaceDepthConsistent_of_objects_eq st _ hDepthPre hObjEq,
    hObjEq ▸ hObjInvPre⟩

/-- WS-E2 / H-01: Compositional preservation of `cspaceDeleteSlot`.
Delegates to `cspaceDeleteSlotCore_preserves_capabilityInvariantBundle`, then keeps
acyclicity through the splice of the deleted slot's node. -/
theorem cspaceDeleteSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' hStep
  have hInvC := cspaceDeleteSlotCore_preserves_capabilityInvariantBundle
    st stC addr hInv hNodeSlotK hCore
  cases st.lookupCdtNodeOfSlot addr with
  | none => exact hInvC
  | some node =>
    exact capabilityInvariantBundle_of_cdt_update stC _ hInvC
      (CapDerivationTree.spliceNode_edgeWellFounded _ node hInvC.2.2.2.1)

/-- Core: `cspaceDeleteSlotCore` preserves `cdtNodeSlot.invExtK`. -/
theorem cspaceDeleteSlotCore_preserves_cdtNodeSlot
    (st st' : SystemState) (addr : CSpaceAddr)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    st'.cdtNodeSlot.invExtK := by
  unfold cspaceDeleteSlotCore SystemState.getCNode? at hStep
  cases hPre : st.objects[addr.cnode]? with
  | none => simp [hPre] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp [hPre] at hStep
    | cnode preCn =>
      simp [hPre] at hStep
      cases hStore : storeObject addr.cnode (.cnode (preCn.remove addr.slot)) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        obtain ⟨_, stMid⟩ := pair
        simp [hStore] at hStep; cases hStep
        have hRefEqSt : stMid.cdtNodeSlot = st.cdtNodeSlot :=
          (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
        -- detachSlotFromCdt either leaves cdtNodeSlot unchanged or erases one key
        unfold SystemState.detachSlotFromCdt
        cases hLookup : stMid.cdtSlotNode[addr]? with
        | none =>
          simp only []
          exact hRefEqSt ▸ hNodeSlotK
        | some origNode =>
          simp only []
          have hKRef : stMid.cdtNodeSlot.invExtK := by rw [hRefEqSt]; exact hNodeSlotK
          exact stMid.cdtNodeSlot.erase_preserves_invExtK origNode hKRef

/-- `cspaceDeleteSlot` preserves `cdtNodeSlot.invExtK` (guarded wrapper). -/
theorem cspaceDeleteSlot_preserves_cdtNodeSlot
    (st st' : SystemState) (addr : CSpaceAddr)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    st'.cdtNodeSlot.invExtK := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' hStep
  rw [spliceDeletedCdtNode_cdtNodeSlot]
  exact cspaceDeleteSlotCore_preserves_cdtNodeSlot st stC addr hNodeSlotK hCore

/-- **The destroyed-slot step keeps the structural capability invariants**: it
writes only the tree (a splice, which keeps it acyclic) and the two slot maps
(erasures, which keep every remaining node-to-slot entry backed by an object). -/
theorem detachDestroyedSlot_preserves (st : SystemState) (ref : SlotRef)
    (hBnd : cspaceSlotCountBounded st) (hComp : cdtCompleteness st)
    (hAcyc : cdtAcyclicity st) (hDepth : cspaceDepthConsistent st)
    (hObjInv : st.objects.invExt) (hK : st.cdtNodeSlot.invExtK) :
    cspaceSlotCountBounded (detachDestroyedSlot st ref) ∧
    cdtCompleteness (detachDestroyedSlot st ref) ∧
    cdtAcyclicity (detachDestroyedSlot st ref) ∧
    cspaceDepthConsistent (detachDestroyedSlot st ref) ∧
    (detachDestroyedSlot st ref).objects.invExt ∧
    (detachDestroyedSlot st ref).cdtNodeSlot.invExtK := by
  unfold detachDestroyedSlot
  generalize hS : spliceDeletedCdtNode st (st.lookupCdtNodeOfSlot ref) = stS
  have hObj : stS.objects = st.objects := hS ▸ spliceDeletedCdtNode_objects _ _
  have hNS : stS.cdtNodeSlot = st.cdtNodeSlot := hS ▸ spliceDeletedCdtNode_cdtNodeSlot _ _
  have hAcycS : cdtAcyclicity stS := by
    subst hS
    cases st.lookupCdtNodeOfSlot ref with
    | none => exact hAcyc
    | some n => exact CapDerivationTree.spliceNode_edgeWellFounded _ n hAcyc
  have hCompS : cdtCompleteness stS := fun n r h => by
    rw [hObj]; exact hComp n r (hNS ▸ h)
  have hKS : stS.cdtNodeSlot.invExtK := hNS ▸ hK
  refine ⟨cspaceSlotCountBounded_of_detachSlotFromCdt _ ref
      (cspaceSlotCountBounded_of_objects_eq st _ hBnd hObj),
    cdtCompleteness_of_detachSlotFromCdt _ ref hCompS hKS,
    cdtAcyclicity_of_detachSlotFromCdt _ ref hAcycS,
    cspaceDepthConsistent_of_detachSlotFromCdt _ ref
      (cspaceDepthConsistent_of_objects_eq st _ hDepth hObj),
    (SystemState.detachSlotFromCdt_objects_eq stS ref) ▸ hObj ▸ hObjInv, ?_⟩
  unfold SystemState.detachSlotFromCdt
  split
  · exact hKS
  · exact stS.cdtNodeSlot.erase_preserves_invExtK _ hKS

/-- ...and so does detaching every sibling the local revoke empties. -/
theorem detachRevokedSlots_preserves (st : SystemState) (cnodeId : SeLe4n.ObjId)
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (hBnd : cspaceSlotCountBounded st) (hComp : cdtCompleteness st)
    (hAcyc : cdtAcyclicity st) (hDepth : cspaceDepthConsistent st)
    (hObjInv : st.objects.invExt) (hK : st.cdtNodeSlot.invExtK) :
    let st' := detachRevokedSlots st cnodeId cn sourceSlot target
    cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧
      cspaceDepthConsistent st' ∧ st'.objects.invExt ∧ st'.cdtNodeSlot.invExtK := by
  unfold detachRevokedSlots
  refine SeLe4n.Model.CNode.foldCells_preserves cn st _
    (fun acc => cspaceSlotCountBounded acc ∧ cdtCompleteness acc ∧ cdtAcyclicity acc ∧
      cspaceDepthConsistent acc ∧ acc.objects.invExt ∧ acc.cdtNodeSlot.invExtK)
    ⟨hBnd, hComp, hAcyc, hDepth, hObjInv, hK⟩ (fun acc slot cap _ h => ?_)
  split
  · exact h
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact detachDestroyedSlot_preserves acc _ h1 h2 h3 h4 h5 h6

/-- The local revoke keeps `cdtNodeSlot.invExtK`. -/
theorem cspaceRevoke_preserves_cdtNodeSlot
    (st st' : SystemState) (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    st'.cdtNodeSlot.invExtK := by
  obtain ⟨parent, cn, stS, _, hCn, hStore, rfl⟩ := cspaceRevoke_ok_decompose addr st st' hStep
  rcases hInv with ⟨_, hBnd, hComp, hAcyc, hDepth, hObjInv, _⟩
  have hNS := (storeObject_cdtNodeSlot_eq st stS addr.cnode _ hStore).1
  have hObjInvS := storeObject_preserves_objects_invExt st stS addr.cnode _ hObjInv hStore
  have hPre : st.objects[addr.cnode]? = some (.cnode cn) := by
    unfold SystemState.getCNode? at hCn
    split at hCn <;> simp_all
  exact (detachRevokedSlots_preserves stS addr.cnode cn addr.slot parent.target
    (cspaceSlotCountBounded_of_storeObject_cnode st stS addr.cnode _ hBnd hObjInv hStore
      (CNode.revokeTargetLocal_slotCountBounded cn addr.slot parent.target
        (hBnd addr.cnode cn hPre) (SeLe4n.Model.CNode.slotsUnique_holds cn)))
    (cdtCompleteness_of_storeObject st stS addr.cnode _ hComp hObjInv hStore hNS)
    (cdtAcyclicity_of_cdt_eq st stS hAcyc (storeObject_cdt_eq st stS addr.cnode _ hStore))
    (cspaceDepthConsistent_of_storeObject_sameCNode st stS addr.cnode cn
      (cn.revokeTargetLocal addr.slot parent.target) hDepth hObjInv hPre hStore rfl rfl rfl rfl)
    hObjInvS (hNS ▸ hNodeSlotK)).2.2.2.2.2

/-- WS-SM SM6.D / PR #822 Phase H (#1.a): `cspaceRevoke` preserves `replyCapPointsToValidReply`.
Revoke only *removes* caps with the revoked target from the local CNode (`revokeTargetLocal`), so
every reply cap surviving in the post-state was already present pre-revoke (backed by the pre-invariant),
and `getReply?` frames through the single CNode store (`lookup_revokeTargetLocal_sub`). -/
theorem cspaceRevoke_preserves_replyCapPointsToValidReply
    (st st' : SystemState) (addr : CSpaceAddr)
    (hRCPV : replyCapPointsToValidReply st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    replyCapPointsToValidReply st' := by
  unfold cspaceRevoke SystemState.getCNode? at hStep
  cases hLookup2 : cspaceLookupSlot addr st with
  | error e => simp [hLookup2] at hStep
  | ok pair =>
    rcases pair with ⟨parent, st1⟩
    have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr parent hLookup2; subst st1
    cases hPre : st.objects[addr.cnode]? with
    | none => simp [hLookup2, hPre] at hStep
    | some preObj =>
      cases preObj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ =>
          simp [hLookup2, hPre] at hStep
      | cnode preCn =>
        simp [hLookup2, hPre] at hStep
        cases hStore : storeObject addr.cnode (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) st with
        | error e => simp [hStore] at hStep
        | ok pair =>
          obtain ⟨_, stMid⟩ := pair; simp [hStore] at hStep
          -- `hStep : detachRevokedSlots stMid … = st'`, which frames the objects
          have hObjFrame : st'.objects = stMid.objects := by rw [← hStep, detachRevokedSlots_objects]
          have hMidSelf : stMid.objects[addr.cnode]? = some (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) :=
            storeObject_objects_eq st stMid addr.cnode _ hObjInv hStore
          have hMidNe : ∀ oid, oid ≠ addr.cnode → stMid.objects[oid]? = st.objects[oid]? :=
            fun oid h => storeObject_objects_ne st stMid addr.cnode oid _ h hObjInv hStore
          have hGetReply : ∀ rid : SeLe4n.ReplyId, st'.getReply? rid = st.getReply? rid := by
            intro rid
            simp only [SystemState.getReply?, hObjFrame]
            by_cases hc : rid.toObjId = addr.cnode
            · rw [hc, hMidSelf, hPre]
            · rw [hMidNe rid.toObjId hc]
          intro oid cn slot cap' rid hObj hLook hTgt
          rw [hGetReply]
          by_cases hc : oid = addr.cnode
          · subst hc
            rw [hObjFrame, hMidSelf] at hObj
            simp only [Option.some.injEq, KernelObject.cnode.injEq] at hObj
            subst hObj
            have hLookPre : preCn.lookup slot = some cap' :=
              CNode.lookup_revokeTargetLocal_sub preCn addr.slot parent.target slot cap'
                (CNode.slotsUnique_holds preCn) hLook
            exact hRCPV addr.cnode preCn slot cap' rid hPre hLookPre hTgt
          · rw [hObjFrame, hMidNe oid hc] at hObj
            exact hRCPV oid cn slot cap' rid hObj hLook hTgt

/-- WS-E2 / H-01: Compositional preservation of `cspaceRevoke`.
WS-RC R4.A close-out: slot-uniqueness is now carried structurally on
`CNode.slots : UniqueSlotMap` (`UniqueSlotMap.hWF`); the historical
state-level `cspaceSlotUnique` predicate is no longer threaded as a
precondition. -/
theorem cspaceRevoke_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hSound, hBounded, hComp, hAcyclic, hDepthPre, hObjInv, hRCPV⟩
  -- WS-H4: storeObject(CNode.revokeTargetLocal)
  have ⟨hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' ∧ st'.objects.invExt := by
    unfold cspaceRevoke SystemState.getCNode? at hStep
    cases hLookup2 : cspaceLookupSlot addr st with
    | error e => simp [hLookup2] at hStep
    | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr parent hLookup2; subst st1
      cases hPre : st.objects[addr.cnode]? with
      | none => simp [hLookup2, hPre] at hStep
      | some preObj =>
        cases preObj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp [hLookup2, hPre] at hStep
        | cnode preCn =>
          simp [hLookup2, hPre] at hStep
          cases hStore : storeObject addr.cnode (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) st with
          | error e => simp [hStore] at hStep
          | ok pair =>
            obtain ⟨_, stMid⟩ := pair; simp [hStore] at hStep
            have hBndMid := cspaceSlotCountBounded_of_storeObject_cnode st stMid addr.cnode _ hBounded hObjInv hStore
              (CNode.revokeTargetLocal_slotCountBounded preCn addr.slot parent.target
                (hBounded addr.cnode preCn hPre) (SeLe4n.Model.CNode.slotsUnique_holds preCn))
            have hCompMid := cdtCompleteness_of_storeObject st stMid addr.cnode _ hComp hObjInv hStore
              (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
            have hAcyclicMid := cdtAcyclicity_of_cdt_eq st stMid hAcyclic
              (storeObject_cdt_eq st stMid addr.cnode _ hStore)
            have hDepthMid := cspaceDepthConsistent_of_storeObject_sameCNode
              st stMid addr.cnode preCn (preCn.revokeTargetLocal addr.slot parent.target)
              hDepthPre hObjInv hPre hStore rfl rfl rfl rfl
            have hObjInvMid := storeObject_preserves_objects_invExt st stMid addr.cnode _ hObjInv hStore
            have hKMid : stMid.cdtNodeSlot.invExtK := by
              rw [(storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1]; exact hNodeSlotK
            subst hStep
            obtain ⟨h1, h2, h3, h4, h5, _⟩ := detachRevokedSlots_preserves stMid addr.cnode preCn
              addr.slot parent.target hBndMid hCompMid hAcyclicMid hDepthMid hObjInvMid hKMid
            exact ⟨h1, h2, h3, h4, h5⟩
  exact ⟨cspaceLookupSound_holds st',
    hBounded', hComp', hAcyclic', hDepth', hObjInv',
    cspaceRevoke_preserves_replyCapPointsToValidReply st st' addr hRCPV hObjInv hStep⟩


end SeLe4n.Kernel
