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


/-! ## U4-L / U-M26: the derivation tree's invariants from the pre-state

Every operation that changes the derivation tree proves `cdtCompleteness` and
`cdtAcyclicity` of its post-state from the pre-state's bundle; none takes them as
a hypothesis about the state it produces.

- **Growing the tree** (`cspaceCopy`, `cspaceMintWithCdt`, the reply-cap mint,
  IPC capability transfer): each installs into a slot it found empty, which
  `cdtCompleteness` keeps out of the tree, so the new edge reaches a fresh node
  and cannot close a cycle (`addEdge_preserves_edgeWellFounded_fresh`).
- **Moving a node** (`cspaceMove`): the destination is empty, so outside the
  tree, and renaming a node to a fresh one maps every cycle onto a cycle of the
  pre-state (`moveNode_edgeWellFounded`).
- **Shrinking the tree** (`cspaceDeleteSlot`, `cspaceRevoke`, the local revoke,
  CNode retype): the splice and the removal keep or contract edges of the
  pre-state (`CapDerivationTree.edgeWellFounded_sub`,
  `spliceNode_edgeWellFounded`) and take each emptied slot out of the tree, so
  completeness is restored once every emptied slot has left it. -/

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
  obtain ⟨preCn, hCnOpt, _hAddr, _hLookup, hStore⟩ :=
    cspaceInsertSlot_ok_decompose st st' addr cap hStep
  have hPre : st.objects[addr.cnode]? = some (.cnode preCn) :=
    (SystemState.getCNode?_eq_some_iff st addr.cnode preCn).mp hCnOpt
  have hSelf : st'.objects[addr.cnode]? = some (.cnode (preCn.insert addr.slot cap)) :=
    storeObject_objects_eq st st' addr.cnode _ hObjInv hStore
  have hNe : ∀ oid, oid ≠ addr.cnode → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st' addr.cnode oid _ h hObjInv hStore
  have hGetReply : ∀ rid : SeLe4n.ReplyId, st'.getReply? rid = st.getReply? rid := by
    intro rid
    simp only [SystemState.getReply?]
    by_cases hc : rid.toObjId = addr.cnode
    · rw [hc, hSelf, hPre]
    · rw [hNe rid.toObjId hc]
  intro oid cn slot cap' rid hObj hLook hTgt
  rw [hGetReply]
  by_cases hc : oid = addr.cnode
  · subst hc
    rw [hSelf] at hObj
    simp only [Option.some.injEq] at hObj
    subst hObj
    simp only [KernelObject.slotCap] at hLook
    by_cases hs : slot = addr.slot
    · rw [hs] at hLook
      rw [CNode.lookup_insert_eq preCn addr.slot cap (CNode.slotsUnique_holds preCn)
        (CNode.slotAddressable_of_lookup_insert _ _ _ _ _ hLook)] at hLook
      simp only [Option.some.injEq] at hLook
      subst hLook
      exact hCapBacked rid hTgt
    · rw [CNode.lookup_insert_ne preCn addr.slot slot cap (Ne.symm hs)
        (CNode.slotsUnique_holds preCn)] at hLook
      exact hRCPV addr.cnode (.cnode preCn) slot cap' rid hPre hLook hTgt
  · rw [hNe oid hc] at hObj
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
    (_hObjInv : st.objects.invExt)
    (hCapBacked : ∀ rid, cap.target = .replyCap rid → st.getReply? rid ≠ none)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hSound, hComp, hAcyclic, hDepthPre, hObjInv, hRCPV, hLinks⟩
  -- WS-H4: Transfer new components through the storeObject(CNode) step
  have ⟨hComp', hAcyclic', hDepth', hObjInv', hLinks'⟩ :
      cdtCompleteness st' ∧ cdtAcyclicity st' ∧
        cspaceDepthConsistent st' ∧ st'.objects.invExt ∧ cdtLinksAgree st' := by
    obtain ⟨preCn, hCnOpt, _hAddr, _hLookup, hStore⟩ :=
      cspaceInsertSlot_ok_decompose st st' addr cap hStep
    have hPre : st.objects[addr.cnode]? = some (.cnode preCn) :=
      (SystemState.getCNode?_eq_some_iff st addr.cnode preCn).mp hCnOpt
    exact ⟨cdtCompleteness_of_storeObject_cnode_mono st st' addr.cnode preCn
        (preCn.insert addr.slot cap) hComp hObjInv hPre hStore
        (fun s h => CNode.lookup_insert_ne_none preCn addr.slot s cap h),
      cdtAcyclicity_of_cdt_eq st st' hAcyclic
        (storeObject_cdt_eq st st' addr.cnode _ hStore),
      cspaceDepthConsistent_of_storeObject_insertCNode
        st st' addr.cnode preCn addr.slot cap hDepthPre hObjInv hPre hStore,
      storeObject_preserves_objects_invExt st st' addr.cnode _ hObjInv hStore,
      cdtLinksAgree_of_eq hLinks (storeObject_cdt_eq st st' addr.cnode _ hStore)
        (SystemState.slotLinkAt_storeObject_cnode hObjInv hPre (CNode.insert_links ..) hStore)⟩
  exact ⟨cspaceLookupSound_holds st',
    hComp', hAcyclic', hDepth', hObjInv',
    cspaceInsertSlot_preserves_replyCapPointsToValidReply st st' addr cap hRCPV hObjInv hCapBacked hStep,
    hLinks'⟩

/-- WS-SM SM6.D / PR #822 Phase H (#1.b): `cspaceDeleteSlotCore` preserves
`replyCapPointsToValidReply` — deletion only *removes* a cap (and detaches its CDT node,
which does not touch the object store beyond the one CNode), so every reply
cap in the post-state already existed in the pre-state (backed by the pre-invariant) and
`getReply?` frames through.  Used by `cspaceDeleteSlot` and the CDT-revoke fold. -/
theorem cspaceDeleteSlotCore_preserves_replyCapPointsToValidReply
    (st st' : SystemState) (addr : CSpaceAddr)
    (hRCPV : replyCapPointsToValidReply st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    replyCapPointsToValidReply st' := by
  obtain ⟨o, hPre, hH, hStore⟩ := cspaceDeleteSlotCore_ok hStep
  have hMidSelf := storeObject_objects_eq st st' addr.cnode _ hObjInv hStore
  have hMidNe : ∀ oid, oid ≠ addr.cnode → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st' addr.cnode oid _ h hObjInv hStore
  have hGetReply : ∀ rid : SeLe4n.ReplyId, st'.getReply? rid = st.getReply? rid := by
    intro rid
    simp only [SystemState.getReply?]
    by_cases hc : rid.toObjId = addr.cnode
    · rw [hc, hMidSelf, hPre]
      cases o <;> simp_all [KernelObject.holdsSlots, KernelObject.removeSlotCap]
    · rw [hMidNe rid.toObjId hc]
  intro oid o' slot cap' rid hObj hLook hTgt
  rw [hGetReply]
  by_cases hc : oid = addr.cnode
  · subst hc
    rw [hMidSelf] at hObj
    cases hObj
    exact hRCPV _ o slot cap' rid hPre (KernelObject.slotCap_removeSlotCap_back hLook) hTgt
  · rw [hMidNe oid hc] at hObj
    exact hRCPV oid o' slot cap' rid hObj hLook hTgt

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
        src.cnode (.cnode cn) src.slot parent rid hObjCN hCap hTgt

theorem cspaceMint_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hInv : capabilityInvariantBundle st)
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
                    rights := AccessRightSet.ofList [.write] } st
                  = .ok ((), st') := by simpa [hSrc, hTgt, hRep] using hStep
              exact cspaceInsertSlot_preserves_capabilityInvariantBundle st st' dst _ hInv
                (objects_invExt_of_capabilityInvariantBundle st hInv)
                (fun rid h => by
                  simp only [CapTarget.replyCap.injEq] at h; subst h; rw [hRep]; simp) hInsert
      | cnodeSlot a b => simp [hSrc, hTgt] at hStep
      | replyCap rid => simp [hSrc, hTgt] at hStep
      | auditTrail => simp [hSrc, hTgt] at hStep

/-- A slot `lookupSlotCap` reads a capability from is occupied in a live CNode. -/
theorem slotOccupied_of_lookupSlotCap (st : SystemState) (ref : SlotRef)
    (h : (SystemState.lookupSlotCap st ref).isSome) :
    ∃ cn, st.objects[ref.cnode]? = some (.cnode cn) ∧ cn.lookup ref.slot ≠ none := by
  unfold SystemState.lookupSlotCap at h
  cases hL : SystemState.lookupCNode st ref.cnode with
  | none => simp [hL] at h
  | some cn =>
    simp only [hL] at h
    refine ⟨cn, ?_, by simpa [Option.isSome_iff_ne_none] using h⟩
    unfold SystemState.lookupCNode at hL
    split at hL
    · rename_i c hc; cases hL; exact hc
    · cases hL

/-- An insert writes a capability in place: every slot keeps its links and stays
inside or outside its CNode. -/
theorem cspaceInsertSlot_links (st st' : SystemState) (addr : SlotRef) (cap : Capability)
    (hObjInv : st.objects.invExt) (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.slotLinkAt = st.slotLinkAt ∧ ∀ r, st'.slotInObject r ↔ st.slotInObject r := by
  obtain ⟨cn, hGet, -, -, hStore⟩ := cspaceInsertSlot_ok_decompose st st' addr cap hStep
  have hPre := (SystemState.getCNode?_eq_some_iff st addr.cnode cn).mp hGet
  exact ⟨SystemState.slotLinkAt_storeObject_cnode hObjInv hPre (CNode.insert_links ..) hStore,
    SystemState.slotInObject_storeObject_cnode hObjInv hPre (CNode.insert_radixWidth ..) hStore⟩

/-- **Installing a derived capability into an empty slot and recording its
derivation keeps the tree complete and acyclic, and the paired link writes keep the links
agreeing with it.**  The destination was empty, so
the tree did not name it (`cdtCompleteness`): the new edge reaches a fresh node
and closes no cycle (`addEdge_preserves_edgeWellFounded_fresh`).  The source
held a capability and still does; the destination now does.  This is the step
copy, mint, reply-cap mint and IPC capability transfer share. -/
theorem cdt_addEdge_after_insert (st st1 : SystemState) (src dst : SlotRef)
    (cap : Capability) (op : DerivationOp)
    (hComp : cdtCompleteness st) (hAcyc : cdtAcyclicity st) (hObjInv : st.objects.invExt)
    (hSrc : (SystemState.lookupSlotCap st src).isSome)
    (hIns : cspaceInsertSlot dst cap st = .ok ((), st1)) (hLinks : cdtLinksAgree st) :
    cdtCompleteness { st1 with cdt := st1.cdt.addEdge src dst op } ∧
      cdtAcyclicity { st1 with cdt := st1.cdt.addEdge src dst op } ∧
      cdtLinksAgree (st1.cdtAddChild src dst op) := by
  obtain ⟨cn, hGet, hAddr, hEmpty, hStore⟩ := cspaceInsertSlot_ok_decompose st st1 dst cap hIns
  have hPre : st.objects[dst.cnode]? = some (.cnode cn) :=
    (SystemState.getCNode?_eq_some_iff st dst.cnode cn).mp hGet
  have hCdt : st1.cdt = st.cdt := storeObject_cdt_eq st st1 dst.cnode _ hStore
  have hComp1 : cdtCompleteness st1 :=
    cdtCompleteness_of_storeObject_cnode_mono st st1 dst.cnode cn _ hComp hObjInv hPre hStore
      fun s h => CNode.lookup_insert_ne_none cn dst.slot s cap h
  have hDstPost : st1.objects[dst.cnode]? = some (.cnode (cn.insert dst.slot cap)) :=
    storeObject_objects_eq st st1 dst.cnode _ hObjInv hStore
  have hDstOcc : (cn.insert dst.slot cap).lookup dst.slot ≠ none := by
    rw [CNode.lookup_insert_eq cn dst.slot cap (CNode.slotsUnique_holds _) hAddr]; simp
  have hDstFresh : ¬ st.cdt.mentions dst :=
    hComp.not_mentions_of_empty fun cn' h => by rw [hPre] at h; cases h; exact hEmpty
  obtain ⟨cs, hCs, hLs⟩ := slotOccupied_of_lookupSlotCap st src hSrc
  have hNe : src ≠ dst := by
    rintro rfl; rw [hPre] at hCs; cases hCs; exact hLs hEmpty
  have hSrcPost : ∃ o, st1.objects[src.cnode]? = some o ∧ o.slotCap src.slot ≠ none := by
    by_cases hc : src.cnode = dst.cnode
    · rw [hc, hPre] at hCs; cases hCs
      exact ⟨.cnode _, by rw [hc]; exact hDstPost, CNode.lookup_insert_ne_none _ _ _ _ hLs⟩
    · exact ⟨.cnode cs, by rw [storeObject_objects_ne st st1 dst.cnode src.cnode _ hc hObjInv hStore]; exact hCs, hLs⟩
  refine ⟨fun ref hM => ?_, ?_, ?_⟩
  · obtain ⟨e, he, hr⟩ := hM
    simp only [CapDerivationTree.addEdge_edges, List.mem_cons] at he
    rcases he with rfl | he
    · rcases hr with h | h <;> simp only at h <;> subst h
      · exact hSrcPost
      · exact ⟨_, hDstPost, hDstOcc⟩
    · exact hComp1 ref ⟨e, he, hr⟩
  · exact CapDerivationTree.addEdge_preserves_edgeWellFounded_fresh st1.cdt src dst op hNe
      (by unfold cdtAcyclicity at hAcyc; rw [hCdt]; exact hAcyc)
      fun e he => ⟨fun h => hDstFresh ⟨e, hCdt ▸ he, Or.inl h⟩,
        fun h => hDstFresh ⟨e, hCdt ▸ he, Or.inr h⟩⟩
  · -- The insert keeps every link; the new edge's child was outside the tree.
    have hL1 : cdtLinksAgree st1 := cdtLinksAgree_of_eq hLinks hCdt
      (SystemState.slotLinkAt_storeObject_cnode hObjInv hPre (CNode.insert_links ..) hStore)
    exact SystemState.cdtAddChild_agree
      (storeObject_preserves_objects_invExt st st1 dst.cnode _ hObjInv hStore) hL1
      (fun _ hM => hComp1.slotInObject hM) op (slotInObject_of_occupied hSrcPost)
      (slotInObject_of_occupied ⟨_, hDstPost, hDstOcc⟩)
      (CapDerivationTree.parentOf_of_not_mentions (by rw [hCdt]; exact hDstFresh)) hNe

end SeLe4n.Kernel
