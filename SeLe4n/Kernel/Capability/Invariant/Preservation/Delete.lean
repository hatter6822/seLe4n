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
`capabilityInvariantBundle_of_cdt_update` (a CDT-only update keeps the
bundle when the new tree is acyclic and names no new slot) sits here for the
delete's splice and the revocation sweep alike.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Internal

/-- The capability bundle with the tree's completeness relaxed at the slots
`gone` names (`cdtCompletenessOff`): what a destroyer leaves between emptying
slots and taking them out of the tree. -/
def capabilityInvariantBundleOff (st : SystemState) (gone : SlotRef → Prop) : Prop :=
  cspaceLookupSound st ∧
    cspaceSlotCountBounded st ∧ cdtCompletenessOff st gone ∧ cdtAcyclicity st ∧
    cspaceDepthConsistent st ∧ st.objects.invExt ∧ replyCapPointsToValidReply st

/-- Core preservation theorem for `cspaceDeleteSlotCore` (no CDT guard): the
emptied slot is still in the tree, so completeness holds everywhere else.  Used
by internal callers (processRevokeNode, cspaceMove, cspaceRevokeCdtStrict), which
each take the slot out of the tree next, and by the `cspaceDeleteSlot` wrapper. -/
theorem cspaceDeleteSlotCore_preserves_capabilityInvariantBundleOff
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    capabilityInvariantBundleOff st' (· = addr) := by
  rcases hInv with ⟨_hSound, hBounded, hComp, hAcyclic, hDepthPre, hObjInv, hRCPV⟩
  have ⟨hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompletenessOff st' (· = addr) ∧ cdtAcyclicity st' ∧
        cspaceDepthConsistent st' ∧ st'.objects.invExt := by
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
          simp [hStore] at hStep; subst hStep
          have hBndMid := cspaceSlotCountBounded_of_storeObject_cnode st stMid addr.cnode
            (preCn.remove addr.slot) hBounded hObjInv hStore (CNode.remove_slotCountBounded preCn addr.slot (hBounded addr.cnode preCn hPre))
          have hCompMid := cdtCompletenessOff_of_storeObject_cnode st stMid addr.cnode preCn _
            (· = addr) hComp hObjInv hPre hStore fun s hL hN => by
              by_cases hs : s = addr.slot
              · rw [hs]
              · rw [CNode.lookup_remove_ne preCn addr.slot s (Ne.symm hs)
                  (CNode.slotsUnique_holds _)] at hN
                exact absurd hN hL
          have hAcyclicMid := cdtAcyclicity_of_cdt_eq st stMid hAcyclic
            (storeObject_cdt_eq st stMid addr.cnode _ hStore)
          have hDepthMid := cspaceDepthConsistent_of_storeObject_sameCNode
            st stMid addr.cnode preCn (preCn.remove addr.slot) hDepthPre hObjInv hPre hStore rfl rfl rfl rfl
          have hObjInvMid := storeObject_preserves_objects_invExt st stMid addr.cnode _ hObjInv hStore
          exact ⟨hBndMid, hCompMid, hAcyclicMid, hDepthMid, hObjInvMid⟩
  exact ⟨cspaceLookupSound_holds st',
    hBounded', hComp', hAcyclic', hDepth', hObjInv',
    cspaceDeleteSlotCore_preserves_replyCapPointsToValidReply st st' addr hRCPV hObjInv hStep⟩

/-- The core delete keeps every other slot's capability. -/
theorem cspaceDeleteSlotCore_keeps_other_slot (st st' : SystemState) (addr ref : SlotRef)
    (hObjInv : st.objects.invExt) (hNe : ref ≠ addr)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st'))
    (hOcc : ∃ cn, st.objects[ref.cnode]? = some (.cnode cn) ∧ cn.lookup ref.slot ≠ none) :
    ∃ cn, st'.objects[ref.cnode]? = some (.cnode cn) ∧ cn.lookup ref.slot ≠ none := by
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
        simp [hStore] at hStep; subst hStep
        obtain ⟨cn, hCn, hL⟩ := hOcc
        by_cases hc : ref.cnode = addr.cnode
        · rw [hc, hPre] at hCn; cases hCn
          have hs : addr.slot ≠ ref.slot := fun h => hNe (by cases ref; cases addr; simp_all)
          refine ⟨_, by rw [hc]; exact storeObject_objects_eq st stMid _ _ hObjInv hStore, ?_⟩
          rw [CNode.lookup_remove_ne _ _ _ hs (CNode.slotsUnique_holds _)]; exact hL
        · exact ⟨cn, by rw [storeObject_objects_ne st stMid addr.cnode ref.cnode _ hc hObjInv hStore]; exact hCn, hL⟩

/-- A tree update that keeps the tree acyclic, names no new slot and none of
the slots `gone` names restores the full bundle. -/
theorem capabilityInvariantBundle_of_off_cdt_update
    (st : SystemState) (gone : SlotRef → Prop) (cdt' : CapDerivationTree)
    (hInv : capabilityInvariantBundleOff st gone)
    (hAcyclic' : cdt'.edgeWellFounded)
    (hSub : ∀ ref, cdt'.mentions ref → st.cdt.mentions ref)
    (hGone : ∀ ref, gone ref → ¬ cdt'.mentions ref) :
    capabilityInvariantBundle { st with cdt := cdt' } := by
  rcases hInv with ⟨_, hBnd, hComp, _, hDepthPre, hObjInvPre, hRCPV⟩
  have hObjEq : ({ st with cdt := cdt' } : SystemState).objects = st.objects := rfl
  exact ⟨cspaceLookupSound_holds _, hBnd, (hComp.of_cdt cdt' hSub).complete hGone, hAcyclic',
    cspaceDepthConsistent_of_objects_eq st _ hDepthPre hObjEq,
    hObjEq ▸ hObjInvPre, replyCapPointsToValidReply_of_objects_eq hObjEq hRCPV⟩

/-- Helper: CDT-only state updates preserve capabilityInvariantBundle,
given that the new CDT is acyclic and names no slot the old one did not. -/
theorem capabilityInvariantBundle_of_cdt_update
    (st : SystemState) (cdt' : CapDerivationTree)
    (hInv : capabilityInvariantBundle st)
    (hAcyclic' : cdt'.edgeWellFounded)
    (hSub : ∀ ref, cdt'.mentions ref → st.cdt.mentions ref) :
    capabilityInvariantBundle { st with cdt := cdt' } := by
  rcases hInv with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact capabilityInvariantBundle_of_off_cdt_update st (fun _ => False) cdt'
    ⟨h1, h2, h3.off _, h4, h5, h6, h7⟩ hAcyclic' hSub fun _ h => h.elim

/-- WS-E2 / H-01: Compositional preservation of `cspaceDeleteSlot`.
Delegates to `cspaceDeleteSlotCore_preserves_capabilityInvariantBundleOff`, then
the splice takes the emptied slot out of the tree and keeps it acyclic. -/
theorem cspaceDeleteSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' hStep
  have hInvC := cspaceDeleteSlotCore_preserves_capabilityInvariantBundleOff
    st stC addr hInv hCore
  have hTree := capabilityInvariantBundle_of_off_cdt_update stC _ _ hInvC
    (CapDerivationTree.spliceNode_edgeWellFounded _ addr hInvC.2.2.2.1)
    (CapDerivationTree.spliceNode_mentions stC.cdt addr)
    fun ref hEq => by
      subst hEq; exact CapDerivationTree.spliceNode_not_mentions_self _ _ hInvC.2.2.2.1
  obtain ⟨hA, hI⟩ := spliceDeletedCdtNode_agree hInvC.2.2.2.2.2.1 addr
  exact capabilityInvariantBundle_of_agree hTree hA (spliceDeletedCdtNode_reach stC addr).cdt hI

/-- The slots of `cn` (stored at `cnodeId`) the local revoke empties: every
occupied slot `revokeTargetLocalKeeps` drops. -/
def revokedLocalSlot (cnodeId : SeLe4n.ObjId) (cn : CNode) (sourceSlot : SeLe4n.Slot)
    (target : CapTarget) (ref : SlotRef) : Prop :=
  ref.cnode = cnodeId ∧ ∃ c, cn.lookup ref.slot = some c ∧
    CNode.revokeTargetLocalKeeps sourceSlot target ref.slot c = false

/-- **Detaching every sibling the local revoke empties restores the structural
capability invariants**: each step writes only the tree, by a splice, which
keeps it acyclic, names no new slot and takes its own slot out; so once every
emptied slot is detached the tree is complete again. -/
theorem detachRevokedSlots_preserves (st : SystemState) (cnodeId : SeLe4n.ObjId)
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (hBnd : cspaceSlotCountBounded st)
    (hComp : cdtCompletenessOff st (revokedLocalSlot cnodeId cn sourceSlot target))
    (hAcyc : cdtAcyclicity st) (hDepth : cspaceDepthConsistent st)
    (hObjInv : st.objects.invExt) :
    let st' := detachRevokedSlots st cnodeId cn sourceSlot target
    cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧
      cspaceDepthConsistent st' ∧ st'.objects.invExt := by
  unfold detachRevokedSlots
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, hR⟩ := SeLe4n.Model.CNode.foldCells_preserves_visited cn st
    (fun acc slot cap =>
      if CNode.revokeTargetLocalKeeps sourceSlot target slot cap then acc
      else spliceDeletedCdtNode acc { cnode := cnodeId, slot := slot })
    (fun acc => cspaceSlotCountBounded acc ∧
      cdtCompletenessOff acc (revokedLocalSlot cnodeId cn sourceSlot target) ∧
      cdtAcyclicity acc ∧ cspaceDepthConsistent acc ∧ acc.objects.invExt)
    (fun s acc => ∀ c, cn.lookup s = some c →
      CNode.revokeTargetLocalKeeps sourceSlot target s c = false →
      ¬ acc.cdt.mentions { cnode := cnodeId, slot := s })
    ⟨hBnd, hComp, hAcyc, hDepth, hObjInv⟩
    (fun acc slot cap _ h => by
      simp only [] at h ⊢
      split
      · exact h
      · obtain ⟨g1, g2, g3, g4, g5⟩ := h
        obtain ⟨hA, hI⟩ := spliceDeletedCdtNode_agree g5 { cnode := cnodeId, slot := slot }
        have hC := (spliceDeletedCdtNode_reach acc { cnode := cnodeId, slot := slot }).cdt
        exact ⟨cspaceSlotCountBounded_of_agree hA g1,
          cdtCompletenessOff_of_agree (st := { acc with cdt := acc.cdt.spliceNode _ }) hA hC
            (g2.of_cdt _ (CapDerivationTree.spliceNode_mentions acc.cdt _)),
          by unfold cdtAcyclicity; rw [spliceDeletedCdtNode_cdt]
             exact CapDerivationTree.spliceNode_edgeWellFounded _ _ g3,
          cspaceDepthConsistent_of_agree hA g4, hI⟩)
    (fun acc slot cap hL h c hL' hK => by
      rw [hL] at hL'; cases hL'
      simp only [] at h ⊢
      split
      · rename_i hT; rw [hK] at hT; cases hT
      · rw [spliceDeletedCdtNode_cdt]
        exact CapDerivationTree.spliceNode_not_mentions_self _ _ h.2.2.1)
    (fun acc slot cap s' _ _ hRs c hL' hK hM => by
      simp only [] at hRs hM
      split at hM
      · exact hRs c hL' hK hM
      · rw [spliceDeletedCdtNode_cdt] at hM
        exact hRs c hL' hK (CapDerivationTree.spliceNode_mentions _ _ _ hM))
  exact ⟨h1, h2.complete fun ref ⟨hc, c, hL, hK⟩ => by
      obtain ⟨rc, rs⟩ := ref; simp only at hc hL hK; subst hc; exact hR rs c hL c hL hK,
    h3, h4, h5⟩

/-- Detaching the revoked siblings names no slot the tree did not. -/
theorem detachRevokedSlots_mentions_sub (st : SystemState) (cnodeId : SeLe4n.ObjId)
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) (ref : SlotRef)
    (hM : (detachRevokedSlots st cnodeId cn sourceSlot target).cdt.mentions ref) :
    st.cdt.mentions ref := by
  unfold detachRevokedSlots at hM
  refine SeLe4n.Model.CNode.foldCells_preserves cn st _
    (fun acc => ∀ ref, acc.cdt.mentions ref → st.cdt.mentions ref) (fun _ h => h)
    (fun acc slot cap _ h => ?_) ref hM
  simp only []
  split
  · exact h
  · exact fun r hR => h r (CapDerivationTree.spliceNode_mentions _ _ _
      (by rw [spliceDeletedCdtNode_cdt] at hR; exact hR))

/-- The local revoke names no slot the tree did not. -/
theorem cspaceRevoke_mentions_sub (addr : CSpaceAddr) (st st' : SystemState)
    (hStep : cspaceRevoke addr st = .ok ((), st')) (ref : SlotRef)
    (hM : st'.cdt.mentions ref) : st.cdt.mentions ref := by
  obtain ⟨_, _, stS, _, _, hS, rfl⟩ := cspaceRevoke_ok_decompose addr st st' hStep
  have := detachRevokedSlots_mentions_sub _ _ _ _ _ ref hM
  rwa [storeObject_cdt_eq st stS _ _ hS] at this

/-- The delete names no slot the tree did not. -/
theorem cspaceDeleteSlot_mentions_sub (addr : CSpaceAddr) (st st' : SystemState)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) (ref : SlotRef)
    (hM : st'.cdt.mentions ref) : st.cdt.mentions ref := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' hStep
  rw [← cspaceDeleteSlotCore_cdt_eq st stC addr hCore]
  rw [spliceDeletedCdtNode_cdt] at hM
  exact CapDerivationTree.spliceNode_mentions _ _ _ hM

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
          have hInvMid := storeObject_preserves_objects_invExt st stMid addr.cnode _ hObjInv hStore
          subst hStep
          refine replyCapPointsToValidReply_of_agree (detachRevokedSlots_agree hInvMid _ _ _ _).1 ?_
          have hObjFrame : stMid.objects = stMid.objects := rfl
          have hMidSelf : stMid.objects[addr.cnode]? = some (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) :=
            storeObject_objects_eq st stMid addr.cnode _ hObjInv hStore
          have hMidNe : ∀ oid, oid ≠ addr.cnode → stMid.objects[oid]? = st.objects[oid]? :=
            fun oid h => storeObject_objects_ne st stMid addr.cnode oid _ h hObjInv hStore
          have hGetReply : ∀ rid : SeLe4n.ReplyId, stMid.getReply? rid = st.getReply? rid := by
            intro rid
            simp only [SystemState.getReply?]
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
            have hCompMid := cdtCompletenessOff_of_storeObject_cnode st stMid addr.cnode preCn _
              (revokedLocalSlot addr.cnode preCn addr.slot parent.target) hComp hObjInv hPre hStore
              fun s hL hN => by
                cases hc : preCn.lookup s with
                | none => exact absurd hc hL
                | some c =>
                  refine ⟨rfl, c, hc, ?_⟩
                  cases hK : CNode.revokeTargetLocalKeeps addr.slot parent.target s c
                  · rfl
                  · rw [CNode.lookup_revokeTargetLocal_of_keeps preCn addr.slot parent.target s c
                      (CNode.slotsUnique_holds _) hc hK] at hN
                    cases hN
            have hAcyclicMid := cdtAcyclicity_of_cdt_eq st stMid hAcyclic
              (storeObject_cdt_eq st stMid addr.cnode _ hStore)
            have hDepthMid := cspaceDepthConsistent_of_storeObject_sameCNode
              st stMid addr.cnode preCn (preCn.revokeTargetLocal addr.slot parent.target)
              hDepthPre hObjInv hPre hStore rfl rfl rfl rfl
            have hObjInvMid := storeObject_preserves_objects_invExt st stMid addr.cnode _ hObjInv hStore
            subst hStep
            exact detachRevokedSlots_preserves stMid addr.cnode preCn
              addr.slot parent.target hBndMid hCompMid hAcyclicMid hDepthMid hObjInvMid
  exact ⟨cspaceLookupSound_holds st',
    hBounded', hComp', hAcyclic', hDepth', hObjInv',
    cspaceRevoke_preserves_replyCapPointsToValidReply st st' addr hRCPV hObjInv hStep⟩


end SeLe4n.Kernel
