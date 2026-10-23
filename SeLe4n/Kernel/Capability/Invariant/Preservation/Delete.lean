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

/-- The capability bundle with the tree's completeness relaxed at the slots
`gone` names (`cdtCompletenessOff`): what a destroyer leaves between emptying
slots and taking them out of the tree.  An emptied slot stays in its CNode, so
every slot the tree names still has link words, and the links still agree. -/
def capabilityInvariantBundleOff (st : SystemState) (gone : SlotRef → Prop) : Prop :=
  cspaceLookupSound st ∧
    cdtCompletenessOff st gone ∧ cdtAcyclicity st ∧
    cspaceDepthConsistent st ∧ st.objects.invExt ∧ replyCapPointsToValidReply st ∧
    cdtLinksAgree st ∧ ∀ r, st.cdt.mentions r → st.slotInObject r

theorem capabilityBundleOffCoverage.off {st : SystemState} (h : capabilityBundleOffCoverage st)
    (gone : SlotRef → Prop) : capabilityInvariantBundleOff st gone :=
  ⟨h.1.1, h.1.2.1.off gone, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2,
    h.2.1, fun _ hM => h.1.2.1.slotInObject hM⟩

theorem capabilityInvariantBundle.off {st : SystemState} (h : capabilityInvariantBundle st)
    (gone : SlotRef → Prop) : capabilityInvariantBundleOff st gone :=
  h.offCoverage.off gone

/-- A slot the tree names holds a capability. -/
theorem cdtCompleteness.slotCapAt_ne_none {st : SystemState} (h : cdtCompleteness st)
    {r : SlotRef} (hM : st.cdt.mentions r) : st.slotCapAt r ≠ none := by
  obtain ⟨o, hO, hL⟩ := h r hM
  rw [SystemState.slotCapAt_of_object hO]; exact hL

/-- A slot with children holds a capability. -/
theorem cdtCompleteness.slotCapAt_of_children {st : SystemState} (h : cdtCompleteness st)
    {r : SlotRef} (hC : st.cdt.childrenOf r ≠ []) : st.slotCapAt r ≠ none :=
  h.slotCapAt_ne_none ((CapDerivationTree.mentions_iff st.cdt r).mpr (.inr (.inl hC)))

/-- The core delete keeps every object in the store. -/
theorem cspaceDeleteSlotCore_objectPresent {st st' : SystemState} {addr : SlotRef}
    (hObjInv : st.objects.invExt) (hStep : cspaceDeleteSlotCore addr st = .ok ((), st'))
    (o : SeLe4n.ObjId) (hp : st.objectPresent o) : st'.objectPresent o := by
  obtain ⟨_, -, -, hStore⟩ := cspaceDeleteSlotCore_ok hStep
  exact SystemState.objectPresent_storeObject hObjInv hStore o hp

/-- The core delete empties its slot and keeps every other slot's capability. -/
theorem cspaceDeleteSlotCore_slotCapAt {st st' : SystemState} {addr : SlotRef}
    (hObjInv : st.objects.invExt) (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    st'.slotCapAt addr = none ∧ ∀ r, r ≠ addr → st'.slotCapAt r = st.slotCapAt r := by
  obtain ⟨o, hPre, -, hStore⟩ := cspaceDeleteSlotCore_ok hStep
  refine ⟨?_, fun r hr => SystemState.slotCapAt_storeObject_ne hObjInv hPre hStore
    (fun s' hs => KernelObject.slotCap_removeSlotCap_ne o hs) r hr⟩
  rw [SystemState.slotCapAt_storeObject hObjInv hStore, if_pos rfl,
    KernelObject.slotCap_removeSlotCap_self]

/-- Core preservation theorem for `cspaceDeleteSlotCore` (no CDT guard): the
emptied slot is still in the tree, so completeness holds everywhere else.  Used
by internal callers (cspaceMove), which take the slot out of the tree next, and by the `cspaceDeleteSlot` wrapper. -/
theorem cspaceDeleteSlotCore_preserves_capabilityInvariantBundleOff
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityBundleOffCoverage st)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    capabilityInvariantBundleOff st' (· = addr) := by
  rcases hInv with ⟨⟨_hSound, hComp, hAcyclic, hDepthPre, hObjInv, hRCPV⟩, hLinks, -⟩
  obtain ⟨o, hPre, hH, hStore⟩ := cspaceDeleteSlotCore_ok hStep
  have hCdt := storeObject_cdt_eq st st' addr.cnode _ hStore
  have hAt := storeObject_objects_eq st st' addr.cnode _ hObjInv hStore
  have hNe : ∀ oid, oid ≠ addr.cnode → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st' addr.cnode oid _ h hObjInv hStore
  have hComp' : cdtCompletenessOff st' (· = addr) := by
    rintro ⟨c, s⟩ hM hNG
    rw [hCdt] at hM
    by_cases hEq : c = addr.cnode
    · subst hEq
      obtain ⟨o₀, hO, hL⟩ := hComp ⟨addr.cnode, s⟩ hM
      rw [hPre] at hO; cases hO
      have hs : s ≠ addr.slot := fun h => hNG (by cases addr; simp_all)
      exact ⟨_, hAt, by rw [KernelObject.slotCap_removeSlotCap_ne _ hs]; exact hL⟩
    · rw [hNe c hEq]; exact hComp ⟨c, s⟩ hM
  have hDepth' : cspaceDepthConsistent st' := by
    intro cnodeId cn hObj
    by_cases hEq : cnodeId = addr.cnode
    · subst hEq
      rw [hAt] at hObj
      cases o with
      | cnode pre =>
        cases hObj
        exact cspaceDepthConsistent_of_storeObject_sameCNode st st' _ pre (pre.remove addr.slot)
          hDepthPre hObjInv hPre hStore rfl rfl rfl rfl _ _ hAt
      | tcb _ => cases hObj
      | _ => simp [KernelObject.holdsSlots] at hH
    · rw [hNe cnodeId hEq] at hObj; exact hDepthPre cnodeId cn hObj
  have hLinksEq := SystemState.slotLinkAt_storeObject_of_links hObjInv hPre
    (KernelObject.linkWords_removeSlotCap o addr.slot) hStore
  exact ⟨cspaceLookupSound_holds st', hComp',
    cdtAcyclicity_of_cdt_eq st st' hAcyclic hCdt, hDepth',
    storeObject_preserves_objects_invExt st st' addr.cnode _ hObjInv hStore,
    cspaceDeleteSlotCore_preserves_replyCapPointsToValidReply st st' addr hRCPV hObjInv hStep,
    cdtLinksAgree_of_eq hLinks hCdt hLinksEq,
    fun r hM => (SystemState.slotInObject_storeObject_of_hasSlot hObjInv hPre
      (KernelObject.hasSlot_removeSlotCap o addr.slot) hStore r).mpr
        (hComp.slotInObject (hCdt ▸ hM))⟩

/-- The core delete keeps every other slot's capability. -/
theorem cspaceDeleteSlotCore_keeps_other_slot (st st' : SystemState) (addr ref : SlotRef)
    (hObjInv : st.objects.invExt) (hNe : ref ≠ addr)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st'))
    (hOcc : ∃ cn, st.objects[ref.cnode]? = some (.cnode cn) ∧ cn.lookup ref.slot ≠ none) :
    ∃ cn, st'.objects[ref.cnode]? = some (.cnode cn) ∧ cn.lookup ref.slot ≠ none := by
  obtain ⟨o, hPre, _, hStore⟩ := cspaceDeleteSlotCore_ok hStep
  obtain ⟨cn, hCn, hL⟩ := hOcc
  by_cases hc : ref.cnode = addr.cnode
  · rw [hc, hPre] at hCn; cases hCn
    have hs : ref.slot ≠ addr.slot := fun h => hNe (by cases ref; cases addr; simp_all)
    refine ⟨cn.remove addr.slot, ?_, ?_⟩
    · rw [hc]; exact storeObject_objects_eq st st' _ _ hObjInv hStore
    · rw [CNode.lookup_remove_ne _ _ _ (Ne.symm hs) (CNode.slotsUnique_holds _)]; exact hL
  · exact ⟨cn, by rw [storeObject_objects_ne st st' addr.cnode ref.cnode _ hc hObjInv hStore]; exact hCn, hL⟩

/-- The core delete clears a slot in place: every slot keeps its links and
stays inside or outside its CNode. -/
theorem cspaceDeleteSlotCore_links (st st' : SystemState) (addr : SlotRef)
    (hObjInv : st.objects.invExt) (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    st'.slotLinkAt = st.slotLinkAt ∧ ∀ r, st'.slotInObject r ↔ st.slotInObject r := by
  obtain ⟨o, hPre, _, hStore⟩ := cspaceDeleteSlotCore_ok hStep
  exact ⟨SystemState.slotLinkAt_storeObject_of_links hObjInv hPre
      (KernelObject.linkWords_removeSlotCap o addr.slot) hStore,
    SystemState.slotInObject_storeObject_of_hasSlot hObjInv hPre
      (KernelObject.hasSlot_removeSlotCap o addr.slot) hStore⟩

/-- A tree update that keeps the tree acyclic, names no new slot and none of
the slots `gone` names restores the full bundle. -/
theorem capabilityInvariantBundle_of_off_cdt_update
    (st : SystemState) (gone : SlotRef → Prop) (cdt' : CapDerivationTree)
    (hInv : capabilityInvariantBundleOff st gone)
    (hAcyclic' : cdt'.edgeWellFounded)
    (hSub : ∀ ref, cdt'.mentions ref → st.cdt.mentions ref)
    (hGone : ∀ ref, gone ref → ¬ cdt'.mentions ref) :
    capabilityBundleOffLinks { st with cdt := cdt' } := by
  rcases hInv with ⟨_, hComp, _, hDepthPre, hObjInvPre, hRCPV, -, -⟩
  have hObjEq : ({ st with cdt := cdt' } : SystemState).objects = st.objects := rfl
  exact ⟨cspaceLookupSound_holds _, (hComp.of_cdt cdt' hSub).complete hGone, hAcyclic',
    cspaceDepthConsistent_of_objects_eq st _ hDepthPre hObjEq,
    hObjEq ▸ hObjInvPre, replyCapPointsToValidReply_of_objects_eq hObjEq hRCPV⟩

/-- Helper: CDT-only state updates preserve capabilityInvariantBundle,
given that the new CDT is acyclic and names no slot the old one did not. -/
theorem capabilityInvariantBundle_of_cdt_update
    (st : SystemState) (cdt' : CapDerivationTree)
    (hInv : capabilityInvariantBundle st)
    (hAcyclic' : cdt'.edgeWellFounded)
    (hSub : ∀ ref, cdt'.mentions ref → st.cdt.mentions ref) :
    capabilityBundleOffLinks { st with cdt := cdt' } :=
  capabilityInvariantBundle_of_off_cdt_update st (fun _ => False) cdt'
    (hInv.off _) hAcyclic' hSub fun _ h => h.elim

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
    st stC addr hInv.offCoverage hCore
  have hTree := capabilityInvariantBundle_of_off_cdt_update stC _ _ hInvC
    (CapDerivationTree.spliceNode_edgeWellFounded _ addr hInvC.2.2.1)
    (CapDerivationTree.spliceNode_mentions stC.cdt addr)
    fun ref hEq => by
      subst hEq; exact CapDerivationTree.spliceNode_not_mentions_self _ _ hInvC.2.2.1
  obtain ⟨hA, hI⟩ := spliceDeletedCdtNode_agree hInvC.2.2.2.2.1 addr
  have hL := hInv.linksAgree
  have hE := cspaceDeleteSlotCore_slotCapAt hInv.2.2.2.2.1 hCore
  exact capabilityInvariantBundle_of_agree hTree hA (spliceDeletedCdtNode_reach stC addr).cdt hI
    (SystemState.cdtSplice_agree hInvC.2.2.2.2.1 hInvC.2.2.2.2.2.2.1
      hInvC.2.2.2.2.2.2.2 hInvC.2.2.1 addr)
    (hInv.treeShape.splice (st' := { stC with cdt := stC.cdt.spliceNode addr })
      hL.childrenUnique hL.rootsParentless
      (hL.parentOf_ne_self_of_wf hInv.2.2.1 addr)
      (by show stC.cdt.spliceNode addr = _; rw [cspaceDeleteSlotCore_cdt_eq st stC addr hCore])
      hE.1 hE.2 (fun o hp => cspaceDeleteSlotCore_objectPresent (st' := stC) hInv.2.2.2.2.1 hCore o hp)
      hInv.cdtCompleteness.slotCapAt_of_children)

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
    (hComp : cdtCompletenessOff st (revokedLocalSlot cnodeId cn sourceSlot target))
    (hAcyc : cdtAcyclicity st) (hDepth : cspaceDepthConsistent st)
    (hObjInv : st.objects.invExt) (hLinks : cdtLinksAgree st)
    (hIn : ∀ r, st.cdt.mentions r → st.slotInObject r)
    (cap₀ : SlotRef → Option Capability)
    (hShape : SystemState.TreeShapeOver st.cdt cap₀ st.objectPresent)
    (hSub : ∀ r, st.slotCapAt r ≠ none → st.slotCapAt r = cap₀ r)
    (hOrig : ∀ s c, cn.lookup s = some c →
      CNode.revokeTargetLocalKeeps sourceSlot target s c = false → cap₀ ⟨cnodeId, s⟩ = some c)
    (hGone : ∀ s c, cn.lookup s = some c → CNode.revokeTargetLocalKeeps sourceSlot target s c = false →
      st.slotCapAt ⟨cnodeId, s⟩ = none) :
    let st' := detachRevokedSlots st cnodeId cn sourceSlot target
    cdtCompleteness st' ∧ cdtAcyclicity st' ∧
      cspaceDepthConsistent st' ∧ st'.objects.invExt ∧ cdtLinksAgree st' ∧
      SystemState.CapTreeShape st' := by
  classical
  -- The shape is carried over the pre-revoke reading of every slot the tree
  -- still names (`cap₀`): an emptied slot keeps what it held until its splice
  -- takes it out of the tree, so each splice sees its slot's capability.
  unfold detachRevokedSlots
  obtain ⟨⟨h2, h3, h4, h5, h6, -, h8, h9⟩, hR⟩ := SeLe4n.Model.CNode.foldCells_preserves_visited cn st
    (fun acc slot cap =>
      if CNode.revokeTargetLocalKeeps sourceSlot target slot cap then acc
      else spliceDeletedCdtNode acc { cnode := cnodeId, slot := slot })
    (fun acc =>
      cdtCompletenessOff acc (revokedLocalSlot cnodeId cn sourceSlot target) ∧
      cdtAcyclicity acc ∧ cspaceDepthConsistent acc ∧ acc.objects.invExt ∧
      cdtLinksAgree acc ∧ (∀ r, acc.cdt.mentions r → acc.slotInObject r) ∧
      SystemState.TreeShapeOver acc.cdt
        (fun r => if acc.cdt.mentions r then cap₀ r else acc.slotCapAt r) acc.objectPresent ∧
      ∀ r, acc.slotCapAt r = st.slotCapAt r)
    (fun s acc => ∀ c, cn.lookup s = some c →
      CNode.revokeTargetLocalKeeps sourceSlot target s c = false →
      ¬ acc.cdt.mentions { cnode := cnodeId, slot := s })
    ⟨hComp, hAcyc, hDepth, hObjInv, hLinks, hIn,
      hShape.of_sub (fun r hr => by
        split
        · rfl
        · next hm => rw [if_neg hm] at hr; exact hSub r hr) fun _ h => h,
      fun _ => rfl⟩
    (fun acc slot cap hLk h => by
      simp only [] at h ⊢
      split
      · exact h
      · rename_i hK
        obtain ⟨g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
        obtain ⟨hA, hI⟩ := spliceDeletedCdtNode_agree g5 { cnode := cnodeId, slot := slot }
        have hC := (spliceDeletedCdtNode_reach acc { cnode := cnodeId, slot := slot }).cdt
        exact ⟨cdtCompletenessOff_of_agree (st := { acc with cdt := acc.cdt.spliceNode _ }) hA hC
            (g2.of_cdt _ (CapDerivationTree.spliceNode_mentions acc.cdt _)),
          by unfold cdtAcyclicity; rw [spliceDeletedCdtNode_cdt]
             exact CapDerivationTree.spliceNode_edgeWellFounded _ _ g3,
          cspaceDepthConsistent_of_agree hA g4, hI,
          SystemState.cdtSplice_agree g5 g6 g7 g3 _,
          fun r hM => (hA.slotInObject_iff r).mpr (g7 r (CapDerivationTree.spliceNode_mentions _ _ _
            (by rw [spliceDeletedCdtNode_cdt] at hM; exact hM))),
          g8.splice g6.childrenUnique g6.rootsParentless (g6.parentOf_ne_self_of_wf g3 _)
            (spliceDeletedCdtNode_cdt _ _)
            (by
              have hNm : ¬ (spliceDeletedCdtNode acc ⟨cnodeId, slot⟩).cdt.mentions ⟨cnodeId, slot⟩ := by
                rw [spliceDeletedCdtNode_cdt]
                exact CapDerivationTree.spliceNode_not_mentions_self _ _ g3
              simp only [if_neg hNm]
              rw [hA.slotCapAt, g9]; exact hGone slot cap hLk (Bool.eq_false_iff.mpr hK))
            (fun r _ hr => by
              by_cases hm' : (spliceDeletedCdtNode acc ⟨cnodeId, slot⟩).cdt.mentions r
              · have hm : acc.cdt.mentions r := by
                  rw [spliceDeletedCdtNode_cdt] at hm'
                  exact CapDerivationTree.spliceNode_mentions _ _ _ hm'
                rw [if_pos hm', if_pos hm]
              · rw [if_neg hm'] at hr ⊢
                rw [hA.slotCapAt] at hr ⊢
                split
                · rw [g9] at hr ⊢; exact hSub r hr
                · rfl)
            (fun o hp => hA.present o hp)
            (fun hc => by
              have hm : acc.cdt.mentions ⟨cnodeId, slot⟩ :=
                (CapDerivationTree.mentions_iff _ _).mpr (.inr (.inl hc))
              simp only [if_pos hm]
              rw [hOrig slot cap hLk (Bool.eq_false_iff.mpr hK)]; exact Option.some_ne_none _),
          fun r => (hA.slotCapAt r).trans (g9 r)⟩)
    (fun acc slot cap hL h c hL' hK => by
      rw [hL] at hL'; cases hL'
      simp only [] at h ⊢
      split
      · rename_i hT; rw [hK] at hT; cases hT
      · rw [spliceDeletedCdtNode_cdt]
        exact CapDerivationTree.spliceNode_not_mentions_self _ _ h.2.1)
    (fun acc slot cap s' _ _ hRs c hL' hK hM => by
      simp only [] at hRs hM
      split at hM
      · exact hRs c hL' hK hM
      · rw [spliceDeletedCdtNode_cdt] at hM
        exact hRs c hL' hK (CapDerivationTree.spliceNode_mentions _ _ _ hM))
  exact ⟨h2.complete fun ref ⟨hc, c, hL, hK⟩ => by
      obtain ⟨rc, rs⟩ := ref; simp only at hc hL hK; subst hc; exact hR rs c hL c hL hK,
    h3, h4, h5, h6, h8.of_sub (fun r hr => by
      show _ = ite _ _ _
      split
      · rw [h9] at hr ⊢; exact hSub r hr
      · rfl) fun _ h => h⟩

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
            simp only [Option.some.injEq] at hObj
            subst hObj
            have hLookPre : preCn.lookup slot = some cap' :=
              CNode.lookup_revokeTargetLocal_sub preCn addr.slot parent.target slot cap'
                (CNode.slotsUnique_holds preCn) hLook
            exact hRCPV addr.cnode (.cnode preCn) slot cap' rid hPre hLookPre hTgt
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
  rcases hInv with ⟨_hSound, hComp, hAcyclic, hDepthPre, hObjInv, hRCPV, hLinks, hShape⟩
  -- WS-H4: storeObject(CNode.revokeTargetLocal)
  have ⟨hComp', hAcyclic', hDepth', hObjInv', hLinks', hShape'⟩ :
      cdtCompleteness st' ∧ cdtAcyclicity st' ∧
        cspaceDepthConsistent st' ∧ st'.objects.invExt ∧ cdtLinksAgree st' ∧
        SystemState.CapTreeShape st' := by
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
            have hCdtMid := storeObject_cdt_eq st stMid addr.cnode _ hStore
            exact detachRevokedSlots_preserves stMid addr.cnode preCn
              addr.slot parent.target hCompMid hAcyclicMid hDepthMid hObjInvMid
              (cdtLinksAgree_of_eq hLinks hCdtMid
                (SystemState.slotLinkAt_storeObject_cnode hObjInv hPre (CNode.filterSlots_links ..) hStore))
              (fun r hM => (SystemState.slotInObject_storeObject_cnode
                (cn' := preCn.revokeTargetLocal addr.slot parent.target) hObjInv hPre rfl hStore r).mpr
                (hComp.slotInObject (hCdtMid ▸ hM)))
              st.slotCapAt
              (by rw [hCdtMid]; exact SystemState.TreeShapeOver.of_sub hShape (fun _ _ => rfl)
                    (SystemState.objectPresent_storeObject hObjInv hStore))
              (fun r hr => by
                rw [SystemState.slotCapAt_storeObject hObjInv hStore] at hr ⊢
                by_cases hc : r.cnode = addr.cnode
                · rw [if_pos hc] at hr ⊢
                  rw [SystemState.slotCapAt_eq_bind, hc, hPre]
                  cases hl : (preCn.revokeTargetLocal addr.slot parent.target).lookup r.slot with
                  | none => simp [KernelObject.slotCap, hl] at hr
                  | some c =>
                    have := CNode.lookup_revokeTargetLocal_sub preCn addr.slot parent.target r.slot c
                      (CNode.slotsUnique_holds _) hl
                    simp only [Option.bind_some, KernelObject.slotCap, hl, this]
                · rw [if_neg hc])
              (fun s c hL _ => (SystemState.slotCapAt_of_object (r := ⟨addr.cnode, s⟩) hPre).trans hL)
              (fun s c hL hK => by
                rw [SystemState.slotCapAt_storeObject hObjInv hStore, if_pos rfl]
                exact CNode.lookup_revokeTargetLocal_of_not_keeps preCn addr.slot parent.target s c
                  (CNode.slotsUnique_holds _) hL hK)
  exact ⟨cspaceLookupSound_holds st',
    hComp', hAcyclic', hDepth', hObjInv',
    cspaceRevoke_preserves_replyCapPointsToValidReply st st' addr hRCPV hObjInv hStep, hLinks', hShape'⟩


end SeLe4n.Kernel
