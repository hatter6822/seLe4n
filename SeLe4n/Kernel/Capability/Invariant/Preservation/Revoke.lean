-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Capability.Invariant.Preservation.BadgeIpcCapsAndCdtMaps
import SeLe4n.Kernel.Capability.FrameFinalise

/-!
# The finalising delete and revocation keep the capability invariants

WS-ZA ZA5.3 part 8.  `.cspaceDelete` and `.cspaceRevoke` run the finalising
delete (`cspaceDeleteSlotFinalising`): the delete, whose preservation is
`cspaceDeleteSlot_preserves_capabilityInvariantBundle`, then the teardown of
what the destroyed capability named, which writes address-space roots and
hardware ledgers only.  The revocation is seL4's `cteRevoke`, a run of those
deletes (`FinalisingDeleteChain`), so it keeps the bundle too
(`cspaceRevokeCdtFinalising_preserves_capabilityInvariantBundle`).

On a state the bundle holds in, the revocation is also **complete**: every
first child the loop reads lies in a live CNode, so no delete is refused, and
each delete takes one edge out of the tree, so the fuel the tree's edge bound
gives is enough; the source has no children afterwards
(`cspaceRevokeCdtFinalising_ok_childless`), as seL4's `cteRevoke` leaves it,
unless a child's zombie delete ran out of fuel and kept its slot, which ends the
revocation for a retry (`docs/planning/UNTYPED_RESET_PLAN.md` row 29 proves the
fuel suffices).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §0  The finalising delete reads finality from the links
-- ============================================================================

/-- **The table a finalising delete owes a teardown is the one no other slot
names**: under the capability bundle, `slotPageTables` (which reads finality
off the slot's four derivation links, `SystemState.capIsFinal`) lists a table
exactly when the slot's capability names it and no other slot names the object
that capability names (`SystemState.capFinalSpec`), as seL4's `finaliseCap`
tears down a page table only on its final capability. -/
theorem mem_slotPageTables_iff_of_bundle {st : SystemState} (h : capabilityInvariantBundle st)
    (addr : CSpaceAddr) (id : SeLe4n.ObjId) :
    id ∈ slotPageTables st addr ↔
      (st.slotCapAt addr).bind (capabilityPageTable st) = some id ∧ st.capFinalSpec addr := by
  rw [← capIsFinal_iff_capFinalSpec h addr]
  unfold slotPageTables
  cases (st.slotCapAt addr).bind (capabilityPageTable st) with
  | none => simp
  | some t => cases st.capIsFinal addr.cnode addr.slot <;> simp [eq_comm]

-- ============================================================================
-- §1  The teardown writes no derivation edge
-- ============================================================================

theorem storeObjectState_cdt (id : SeLe4n.ObjId) (obj : KernelObject) (st : SystemState) :
    (storeObjectState id obj st).cdt = st.cdt :=
  storeObject_cdt_eq st _ id obj (storeObject_eq_storeObjectState id obj st)

/-- One page's unmap writes a VSpace root and the hardware ledgers, never the
tree. -/
theorem unmapPageState_cdt (ec : Concurrency.CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (st : SystemState) :
    (unmapPageState ec asid vaddr st).cdt = st.cdt := by
  unfold unmapPageState
  split
  · rfl
  · next rootId root _ =>
    split
    · rfl
    · next root' _ =>
      dsimp only
      split <;>
        exact storeObjectState_cdt rootId (.vspaceRoot root') (Architecture.recordPhysicalWrites st
          (Architecture.mappingStore? st root' vaddr).toList)

theorem unmapLivePagesState_cdt (ec : Concurrency.CoreId) :
    ∀ (ps : List MappedPage) (st : SystemState), (unmapLivePagesState ec ps st).cdt = st.cdt
  | [], _ => rfl
  | p :: rest, st => by
    unfold unmapLivePagesState
    split
    · rw [unmapLivePagesState_cdt ec rest, unmapPageState_cdt]
    · exact unmapLivePagesState_cdt ec rest st

theorem detachPageTablesState_cdt :
    ∀ (os : List (SeLe4n.ObjId × PageTableInstall)) (st : SystemState),
      (detachPageTablesState os st).cdt = st.cdt
  | [], _ => rfl
  | o :: rest, st => by
    unfold detachPageTablesState
    split
    · exact detachPageTablesState_cdt rest st
    · rw [detachPageTablesState_cdt rest, storeObjectState_cdt]; rfl

/-- **The teardown writes no derivation edge.** -/
theorem finaliseDestroyedCapabilitiesState_cdt (ec : Concurrency.CoreId)
    (named : List SeLe4n.ObjId) (pages : List MappedPage) (st : SystemState) :
    (finaliseDestroyedCapabilitiesState ec named pages st).cdt = st.cdt := by
  unfold finaliseDestroyedCapabilitiesState
  rw [unmapLivePagesState_cdt, detachPageTablesState_cdt]

-- ============================================================================
-- §2  The finalising delete and revocation keep the bundle
-- ============================================================================

/-- **The teardown writes no slot and no untyped**: it writes address-space
roots, which hold neither. -/
theorem finaliseDestroyedCapabilities_slots (ec : Concurrency.CoreId)
    (named : List SeLe4n.ObjId) (pages : List MappedPage) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (h : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    st'.objects.invExt ∧ st'.cdt = st.cdt ∧ (∀ r, st'.slotCapAt r = st.slotCapAt r) ∧
      st'.getUntyped? = st.getUntyped? ∧ vspaceRootOnlyWrite st st' := by
  obtain ⟨hI', hW, -⟩ := finaliseDestroyedCapabilities_ok_frame ec _ _ st st' hObjInv h
  have hCdt : st'.cdt = st.cdt := by
    rw [finaliseDestroyedCapabilities_eq_ok_state] at h
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    subst h
    exact finaliseDestroyedCapabilitiesState_cdt ec _ _ st
  refine ⟨hI', hCdt, fun r => ?_, ?_, hW⟩
  · rw [SystemState.slotCapAt_eq_bind, SystemState.slotCapAt_eq_bind]
    rcases hW r.cnode with e | ⟨⟨q, hq⟩, ⟨q', hq'⟩⟩
    · rw [e]
    · rw [hq, hq']; rfl
  · funext o
    rw [SystemState.getUntyped?_eq_bind, SystemState.getUntyped?_eq_bind]
    rcases hW o with e | ⟨⟨q, hq⟩, ⟨q', hq'⟩⟩
    · rw [e]
    · rw [hq, hq']; rfl

/-- **The teardown keeps the capability invariants**: it writes neither the
tree nor any CNode or reply object (`finaliseDestroyedCapabilities_ok_frame`,
`finaliseDestroyedCapabilitiesState_cdt`). -/
theorem finaliseDestroyedCapabilities_preserves_capabilityInvariantBundle
    (ec : Concurrency.CoreId) (named : List SeLe4n.ObjId) (pages : List MappedPage)
    (st1 st' : SystemState) (h1 : capabilityInvariantBundle st1)
    (hF : finaliseDestroyedCapabilities ec named pages st1 = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  obtain ⟨hI', hCdt, -, hUt, hW⟩ := finaliseDestroyedCapabilities_slots ec _ _ st1 st' h1.2.2.2.2.1 hF
  refine capabilityInvariantBundle_of_frame h1 hCdt ?_ ?_ ?_ ?_ hI' ?_ hUt
  · intro oid cn hC
    rcases hW oid with e | ⟨-, ⟨r, hr⟩⟩
    · rwa [← e]
    · rw [hr] at hC; cases hC
  · intro oid cn hC
    rcases hW oid with e | ⟨⟨r, hr⟩, -⟩
    · rwa [e]
    · rw [hr] at hC; cases hC
  · intro oid
    rcases hW oid with e | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
    · rw [e]
    · rw [hr, hr']; rfl
  · intro rid hR
    unfold SystemState.getReply? at hR ⊢
    rcases hW rid.toObjId with e | ⟨⟨r, hr⟩, -⟩
    · rwa [e]
    · rw [hr] at hR; exact absurd rfl hR
  · intro o hp
    rcases hW o with e | ⟨-, ⟨r, hr⟩⟩
    · show st'.objects[o]? ≠ none; rw [e]; exact hp
    · show st'.objects[o]? ≠ none; rw [hr]; exact Option.some_ne_none _

/-- Whether an untyped records a child reads the untyped records alone. -/
theorem untypedRecordsChild_congr {st st' : SystemState} (h : st'.getUntyped? = st.getUntyped?)
    (w x : SeLe4n.ObjId) : untypedRecordsChild st' w x = untypedRecordsChild st w x := by
  unfold untypedRecordsChild
  rw [h]

/-- **The retire keeps the capability invariants** when no slot names its target
and its recorder word answers truly.  It writes no slot and no edge; it takes
the target, which no slot names, out of the store and out of the one untyped
that recorded it (`retireFinalObject_frame`, `retireFinalObject_unrecorded`),
and that keeps the tree's shape (`TreeShapeOver.retire`). -/
theorem retireFinalObject_preserves_capabilityInvariantBundle (ec : Concurrency.CoreId)
    (target recorder : Nat) (st : SystemState) (h : capabilityInvariantBundle st)
    (hNamed : target ≠ 0 →
      ∀ r, ¬ SystemState.namesAt st.slotCapAt r (SeLe4n.ObjId.ofNat (target - 1)))
    (hRec : target ≠ 0 →
      (recorder ≠ 0 → untypedRecordsChild st (SeLe4n.ObjId.ofNat (recorder - 1))
        (SeLe4n.ObjId.ofNat (target - 1)) = true) ∧
      (recorder = 0 → ∀ w, untypedRecordsChild st w (SeLe4n.ObjId.ofNat (target - 1)) = false)) :
    capabilityInvariantBundle (retireFinalObject ec target recorder st) := by
  by_cases hT : target = 0
  · subst hT; rw [retireFinalObject_zero]; exact h
  have hShape := h.2.2.2.2.2.2.2
  have hUniq : ∀ u v, untypedRecordsChild st u (SeLe4n.ObjId.ofNat (target - 1)) = true →
      untypedRecordsChild st v (SeLe4n.ObjId.ofNat (target - 1)) = true → u = v := by
    intro u v hu hv
    obtain ⟨U, hU, ch, hch, hc⟩ := (untypedRecordsChild_iff st u _).mp hu
    obtain ⟨V, hV, ch', hch', hc'⟩ := (untypedRecordsChild_iff st v _).mp hv
    exact hShape.childUnique u v U V hU hV ch hch ch' hch' (hc.trans hc'.symm)
  rcases retireFinalObject_unrecorded ec target recorder st h.2.2.2.2.1 hRec hUniq with hE | hUn
  · rw [hE]; exact h
  rcases retireFinalObject_admitted ec target recorder st with hE | hAdm
  · rw [hE]; exact h
  rcases retireFinalObject_target_gone ec target recorder st h.2.2.2.2.1 with hE | hGone
  · rw [hE]; exact h
  generalize hX : SeLe4n.ObjId.ofNat (target - 1) = x at hUn hNamed hAdm hGone
  have hx := hNamed hT
  obtain ⟨hI', -, -, hCdt, hW⟩ := retireFinalObject_frame ec target recorder st h.2.2.2.2.1
  rw [hX] at hW
  generalize retireFinalObject ec target recorder st = st' at hUn hI' hCdt hW hGone ⊢
  -- every key the retire changes holds no capability on either side, and
  -- after it is absent or an untyped
  have hKey : ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
      ((∀ o, st.objects[oid]? = some o → ∀ s, o.slotCap s = none) ∧
        (st'.objects[oid]? = none ∨ ∃ U, st'.objects[oid]? = some (.untyped U))) := by
    intro oid
    rcases hW oid with e | ⟨hxo, hcp, hn⟩ | ⟨U, U', -, hU, hU', -⟩
    · exact .inl e
    · refine .inr ⟨fun o hO s => ?_, .inl hn⟩
      rcases hcp with (⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩) | hp
      · rw [hf] at hO; cases hO; rfl
      · rw [hu] at hO; cases hO; rfl
      · rw [hr] at hO; cases hO; rfl
      · rw [hp] at hO; cases hO; rfl
      · subst hxo
        exact finalRetireAdmitted.slotCap hAdm hp o hO s
    · exact .inr ⟨fun o hO s => by rw [hU] at hO; cases hO; rfl, .inr ⟨_, hU'⟩⟩
  have hAfter : ∀ oid : SeLe4n.ObjId, (st'.objects[oid]? = none ∨
      ∃ U, st'.objects[oid]? = some (.untyped U)) → ∀ o, st'.objects[oid]? = some o →
      ∀ s, o.slotCap s = none := by
    rintro oid (hn | ⟨U, hU⟩) o hO s
    · rw [hn] at hO; cases hO
    · rw [hU] at hO; cases hO; rfl
  have hCap : ∀ r, st'.slotCapAt r = st.slotCapAt r := fun r => by
    rw [SystemState.slotCapAt_eq_bind, SystemState.slotCapAt_eq_bind]
    rcases hKey r.cnode with e | ⟨hb, ha⟩
    · rw [e]
    · have l : (st'.objects[r.cnode]?).bind (fun o => o.slotCap r.slot) = none := by
        cases hs : st'.objects[r.cnode]? with
        | none => rfl
        | some o => exact hAfter _ ha o hs r.slot
      have r' : (st.objects[r.cnode]?).bind (fun o => o.slotCap r.slot) = none := by
        cases hs : st.objects[r.cnode]? with
        | none => rfl
        | some o => exact hb o hs r.slot
      rw [l, r']
  have hCnB : ∀ (oid : SeLe4n.ObjId) (cn : CNode),
      st'.objects[oid]? = some (.cnode cn) → st.objects[oid]? = some (.cnode cn) := by
    intro oid cn hC
    rcases hKey oid with e | ⟨-, hn | ⟨U, hU⟩⟩
    · rwa [← e]
    · rw [hn] at hC; cases hC
    · rw [hU] at hC; cases hC
  -- a slot the tree names holds a capability, so its key is unchanged
  have hNamedKey : ∀ r : SlotRef, st.cdt.mentions r → st'.objects[r.cnode]? = st.objects[r.cnode]? := by
    intro r hm
    obtain ⟨o, hO, hL⟩ := h.2.1 r hm
    rcases hKey r.cnode with e | ⟨hb, -⟩
    · exact e
    · exact absurd (hb o hO r.slot) hL
  have hComp' : cdtCompleteness st' := by
    intro ref hRef
    rw [hCdt] at hRef
    obtain ⟨o, hO, hL⟩ := h.2.1 ref hRef
    exact ⟨o, by rw [hNamedKey ref hRef]; exact hO, hL⟩
  have hRCPV' : replyCapPointsToValidReply st' := by
    intro oid o' slot cap rid hO' hL hTg
    have hS : st.slotCapAt ⟨oid, slot⟩ = some cap := by
      rw [← hCap, SystemState.slotCapAt_of_object (r := ⟨oid, slot⟩) hO']; exact hL
    cases hO : st.objects[oid]? with
    | none =>
      rw [SystemState.slotCapAt_eq_bind] at hS
      simp only at hS; rw [hO] at hS; cases hS
    | some o =>
      have hR := h.2.2.2.2.2.1 oid o slot cap rid hO
        (by rw [← SystemState.slotCapAt_of_object (r := ⟨oid, slot⟩) hO]; exact hS) hTg
      unfold SystemState.getReply? at hR ⊢
      rcases hW rid.toObjId with e | ⟨hxo, -, -⟩ | ⟨U, -, -, hU, -⟩
      · rwa [e]
      · exact absurd ⟨cap, hS, by unfold Capability.namedObject; rw [hTg]; exact congrArg some hxo⟩ (hx ⟨oid, slot⟩)
      · rw [hU] at hR; exact absurd rfl hR
  have hL : cdtLinksAgree st' := by
    refine cdtLinksAgree_of_named h.2.2.2.2.2.2.1 hCdt (fun r f hm => ?_) (fun r f hm => ?_)
    · rw [SystemState.slotLinkAt_def, SystemState.slotLinkAt_def, hNamedKey r hm]
    · have hNone := LinksAgree.none_of_not_mentions h.2.2.2.2.2.2.1 hm f
      rcases hKey r.cnode with e | ⟨-, hn | ⟨U, hU⟩⟩
      · rw [SystemState.slotLinkAt_def, e, ← SystemState.slotLinkAt_def]; exact hNone
      · rw [SystemState.slotLinkAt_def, hn]
      · rw [SystemState.slotLinkAt_def, hU]; rfl
  refine ⟨cspaceLookupSound_holds st', hComp', ?_, fun oid cn hC => h.2.2.2.1 oid cn (hCnB oid cn hC),
    hI', hRCPV', hL, (hShape.retire hx (fun o hp ho => ?_) (fun u U' hu => ?_) ?_).of_readers
      hCdt hCap (fun _ hp => hp) rfl⟩
  · have hA := h.2.2.1; unfold cdtAcyclicity at hA ⊢; rw [hCdt]; exact hA
  · rcases hW o with e | ⟨he, -, -⟩ | ⟨U, U', -, -, hU', -⟩
    · show st'.objects[o]? ≠ none; rw [e]; exact hp
    · exact absurd he ho
    · show st'.objects[o]? ≠ none; rw [hU']; exact Option.some_ne_none _
  · have hu' := (SystemState.getUntyped?_eq_some_iff st' u U').mp hu
    rcases hW u with e | ⟨-, -, hn⟩ | ⟨U, U'', -, hU, hU', -, hSz, -, hch, -⟩
    · refine ⟨U', (SystemState.getUntyped?_eq_some_iff st u U').mpr (e ▸ hu'), rfl,
        fun ch hc => ⟨hUn u U' hu' ch hc, .inl ⟨ch, hc, rfl⟩⟩⟩
    · rw [hn] at hu'; cases hu'
    · have e2 : U'' = U' := by rw [hU'] at hu'; simpa using hu'
      subst e2
      have hu0 := (SystemState.getUntyped?_eq_some_iff st u U).mpr hU
      refine ⟨U, hu0, hSz, fun ch hc => ⟨hUn u U'' hU' ch hc, ?_⟩⟩
      rcases hch with e | e
      · rw [e] at hc; exact .inl ⟨ch, hc, rfl⟩
      · rw [e] at hc
        rcases (mem_childListAdopt hc).2 with hm | ⟨hr, c0, hc0, he⟩
        · exact .inl ⟨ch, hm, rfl⟩
        · refine .inr ⟨⟨U, hu0, (childListRecords_iff _ _).mp hr⟩, ?_⟩
          have := mem_retiredChildren hc0
          rw [he] at this
          exact (untypedRecordsChild_iff st _ _).mp this
  · cases hg : st'.getUntyped? x with
    | none => rfl
    | some X' => exact absurd ((SystemState.getUntyped?_eq_some_iff st' x X').mp hg) (hGone X')

theorem objId_ofNat_succ_sub_one (x : SeLe4n.ObjId) : SeLe4n.ObjId.ofNat (x.val + 1 - 1) = x := by
  simp [SeLe4n.ObjId.ofNat]

/-- **What a nonzero retire word names**: the slot's capability names the
target (`Capability.namedObject`: by `.object`, as a reply capability's reply
or as a CNode-slot capability's CNode), and the capability is final as the
store reads it (`SystemState.capIsFinal`). -/
theorem slotRetireTarget_names {st : SystemState} {cnode : SeLe4n.ObjId} {slot : SeLe4n.Slot}
    (hT : slotRetireTarget st cnode slot ≠ 0) :
    ∃ c, st.slotCapAt ⟨cnode, slot⟩ = some c ∧
      c.namedObject = some (SeLe4n.ObjId.ofNat (slotRetireTarget st cnode slot - 1)) ∧
      st.capIsFinal cnode slot = true := by
  unfold slotRetireTarget at hT ⊢
  cases hL : st.slotCapAt ⟨cnode, slot⟩ with
  | none => rw [hL] at hT; exact absurd rfl hT
  | some c =>
    rw [hL] at hT
    dsimp only at hT ⊢
    cases hTg : c.target with
    | object x =>
      rw [hTg] at hT
      dsimp only at hT ⊢
      split at hT
      · next hc =>
        rw [if_pos hc]
        simp only [Bool.and_eq_true] at hc
        exact ⟨c, rfl, by unfold Capability.namedObject; rw [hTg, objId_ofNat_succ_sub_one], hc.2⟩
      · exact absurd rfl hT
    | replyCap r =>
      rw [hTg] at hT
      dsimp only at hT ⊢
      split at hT
      · next hc =>
        rw [if_pos hc]
        simp only [Bool.and_eq_true] at hc
        exact ⟨c, rfl, by unfold Capability.namedObject; rw [hTg, objId_ofNat_succ_sub_one], hc.2⟩
      · exact absurd rfl hT
    | cnodeSlot cn _ =>
      rw [hTg] at hT
      dsimp only at hT ⊢
      split at hT
      · next hc =>
        rw [if_pos hc]
        simp only [Bool.and_eq_true] at hc
        exact ⟨c, rfl, by unfold Capability.namedObject; rw [hTg, objId_ofNat_succ_sub_one], hc.2⟩
      · exact absurd rfl hT
    | auditTrail => rw [hTg] at hT; exact absurd rfl hT

/-- **What a nonzero retire word names, under the capability bundle**: the
target's final capability (`slotRetireTarget_names`, `capIsFinal_iff_capFinalSpec`). -/
theorem slotRetireTarget_spec {st : SystemState} {cnode : SeLe4n.ObjId} {slot : SeLe4n.Slot}
    (h : capabilityInvariantBundle st) (hT : slotRetireTarget st cnode slot ≠ 0) :
    ∃ c, st.slotCapAt ⟨cnode, slot⟩ = some c ∧
      c.namedObject = some (SeLe4n.ObjId.ofNat (slotRetireTarget st cnode slot - 1)) ∧
      st.capFinalSpec ⟨cnode, slot⟩ := by
  obtain ⟨c, hc, hn, hf⟩ := slotRetireTarget_names hT
  exact ⟨c, hc, hn, (capIsFinal_iff_capFinalSpec h ⟨cnode, slot⟩).mp hf⟩

/-- **The delete empties its slot and keeps every other slot and every untyped
record.** -/
theorem cspaceDeleteSlot_slots {addr : CSpaceAddr} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (h : cspaceDeleteSlot addr st = .ok ((), st')) :
    st'.slotCapAt addr = none ∧ (∀ r, r ≠ addr → st'.slotCapAt r = st.slotCapAt r) ∧
      st'.getUntyped? = st.getUntyped? := by
  obtain ⟨stC, hC, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' h
  obtain ⟨o, -, -, hStore⟩ := cspaceDeleteSlotCore_ok hC
  have hInvC := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStore
  have hF : SystemState.SlotTreeFrame { stC with cdt := stC.cdt.spliceNode addr }
      (spliceDeletedCdtNode stC addr) :=
    .of_linkReach (spliceDeletedCdtNode_reach stC addr) hInvC
  obtain ⟨hSelf, hOther⟩ := cspaceDeleteSlotCore_slotCapAt hObjInv hC
  have hUC : stC.getUntyped? = st.getUntyped? := cspaceDeleteSlotCore_getUntyped? hObjInv hC
  exact ⟨(hF.slotCapAt addr).trans hSelf, fun r hr => (hF.slotCapAt r).trans (hOther r hr),
    hF.untyped.trans hUC⟩

/-- **The finalisation keeps the capability invariants**: it writes threads,
endpoints, notifications, replies and scheduling contexts only, each keeping its
kind and slots, and no edge (`finaliseFinalObject_frame`). -/
theorem finaliseFinalObject_preserves_capabilityInvariantBundle (target : Nat) (st : SystemState)
    (h : capabilityInvariantBundle st) : capabilityInvariantBundle (finaliseFinalObject target st) :=
  have hFr := finaliseFinalObject_frame target st h.2.2.2.2.1
  capabilityInvariantBundle_of_kindPreservingUpToBindings h hFr.cdt hFr.invExt hFr.kind

/-- **The finalising delete keeps the capability invariants**: the delete keeps
them (`cspaceDeleteSlot_preserves_capabilityInvariantBundle`), the teardown
after it writes neither the tree nor any slot
(`finaliseDestroyedCapabilities_preserves_capabilityInvariantBundle`), the
finalisation writes threads, endpoints and notifications only, each keeping its
kind and slots (`finaliseFinalObject_frame`), and the
retire takes out an object whose final capability the delete destroyed, so no
slot names it any more, from the one untyped the recorder word read before the
delete names (`recorderWord_spec`). -/
theorem cspaceDeleteSlotFinalising_preserves_capabilityInvariantBundle
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hInv : capabilityInvariantBundle st)
    (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  have h1 := cspaceDeleteSlot_preserves_capabilityInvariantBundle st st1 addr hInv hD
  have h2 := finaliseDestroyedCapabilities_preserves_capabilityInvariantBundle ec _ _ st1 st2 h1 hF
  obtain ⟨-, -, hC2, hU2, -⟩ := finaliseDestroyedCapabilities_slots ec _ _ st1 st2 h1.2.2.2.2.1 hF
  obtain ⟨hC1n, hC1, hU1⟩ := cspaceDeleteSlot_slots hInv.2.2.2.2.1 hD
  -- The finalisation writes threads, endpoints and notifications only, each
  -- keeping its kind and slots (`FinaliseFrame`).
  have hFr := finaliseFinalObject_frame (slotRetireTarget st addr.cnode addr.slot) st2
    h2.2.2.2.2.1
  have h3 := finaliseFinalObject_preserves_capabilityInvariantBundle
    (slotRetireTarget st addr.cnode addr.slot) st2 h2
  refine retireFinalObject_preserves_capabilityInvariantBundle ec _ _ _ h3
    (fun hT r hr => ?_) (fun hT => ?_)
  · obtain ⟨c, hc, ht, hFin⟩ := slotRetireTarget_spec hInv hT
    have hAddr : SystemState.namesAt st.slotCapAt ⟨addr.cnode, addr.slot⟩
        (SeLe4n.ObjId.ofNat (slotRetireTarget st addr.cnode addr.slot - 1)) := ⟨c, hc, ht⟩
    rw [SystemState.namesAt_of_eq (hFr.slotCapAt r), SystemState.namesAt_of_eq (hC2 r)] at hr
    by_cases hra : r = addr
    · subst hra
      obtain ⟨c', hc', -⟩ := hr
      rw [hC1n] at hc'; cases hc'
    · rw [SystemState.namesAt_of_eq (hC1 r hra)] at hr
      exact hFin _ hAddr r hra hr
  · have hU := hFr.getUntyped?.trans (hU2.trans hU1)
    obtain ⟨hS1, hS0⟩ := recorderWord_spec st
      (SeLe4n.ObjId.ofNat (slotRetireTarget st addr.cnode addr.slot - 1)) addr.cnode addr.slot
      hInv.2.2.2.2.1
    unfold slotRetireRecorder recorderFor
    rw [if_neg hT]
    refine ⟨fun hne => ?_, fun h0 w => ?_⟩
    · rw [untypedRecordsChild_congr hU]; exact hS1 hne
    · rw [untypedRecordsChild_congr hU]; exact hS0 h0 w

/-- **The finalising revocation keeps the capability invariants**: it is a run
of finalising deletes (`cspaceRevokeCdtFinalising_closed`). -/
theorem cspaceRevokeCdtFinalising_preserves_capabilityInvariantBundle
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hInv : capabilityInvariantBundle st)
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    capabilityInvariantBundle st' :=
  cspaceRevokeCdtFinalising_closed capabilityInvariantBundle
    (fun c s s' hs hD => cspaceDeleteSlotFinalising_preserves_capabilityInvariantBundle ec c s s' hs hD)
    (fun d s hs => finaliseFinalObject_preserves_capabilityInvariantBundle d s hs)
    hInv h

/-- **The zombie delete keeps the capability invariants**: it is a chain of
finalising deletes and finalisations (`cspaceDeleteSlotZombie_closed`). -/
theorem cspaceDeleteSlotZombie_preserves_capabilityInvariantBundle
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hInv : capabilityInvariantBundle st)
    (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    capabilityInvariantBundle st' :=
  cspaceDeleteSlotZombie_closed capabilityInvariantBundle
    (fun c s s' hs hD => cspaceDeleteSlotFinalising_preserves_capabilityInvariantBundle ec c s s' hs hD)
    (fun d s hs => finaliseFinalObject_preserves_capabilityInvariantBundle d s hs)
    hInv h

-- ============================================================================
-- §3  The revocation is complete
-- ============================================================================

private theorem filter_neither_length_add_le {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (l.filter (fun e => !p e && !q e)).length + (l.filter p).length ≤ l.length
  | [] => by simp
  | x :: xs => by
    have ih := filter_neither_length_add_le p q xs
    cases hp : p x <;> cases hq : q x <;> simp [List.filter_cons, hp, hq] <;> omega

/-- **A splice of a node with a parent edge takes an edge out**: the node's
edges go and only its child edges are re-made, so its parent edge is the one
lost.  (A parent edge from the node to itself would be re-made too; an acyclic
tree has none.) -/
theorem spliceEdges_length_lt_of_parent {es : List CapDerivationEdge} {node : SlotRef}
    {up : CapDerivationEdge} (hF : es.find? (fun e => e.isChildOf node) = some up)
    (hNe : up.parent ≠ node) : (CapDerivationTree.spliceEdges es node).length < es.length := by
  obtain ⟨hu, pre, post, he, hpre⟩ := List.find?_eq_some_iff_append.mp hF
  have huc : up.child = node := by simpa [CapDerivationEdge.isChildOf] using hu
  have hpre' : ∀ e ∈ pre, e.child ≠ node := fun e he' => by
    have := hpre e he'
    simpa [CapDerivationEdge.isChildOf] using this
  have hup : up.isParentOf node = false := by simp [CapDerivationEdge.isParentOf, hNe]
  unfold CapDerivationTree.spliceEdges
  rw [he, CapDerivationTree.spliceEdgesFrom_split node _ pre up post hpre' huc]
  simp only [List.length_append, CapDerivationTree.reparentEdges_length, List.filter_append,
    List.filter_cons, hup, Bool.false_eq_true, if_false, List.length_cons]
  have h1 := filter_neither_length_add_le (·.isParentOf node) (·.isChildOf node) pre
  have h2 := filter_neither_length_add_le (·.isParentOf node) (·.isChildOf node) post
  unfold CapDerivationTree.withoutNodeEdges
  omega

/-- **A child's splice in an acyclic tree takes an edge out of it.** -/
theorem spliceNode_edges_length_lt {cdt : CapDerivationTree} {p c : SlotRef}
    (hWF : cdt.edgeWellFounded) (hC : c ∈ cdt.childrenOf p) :
    (cdt.spliceNode c).edges.length < cdt.edges.length := by
  rw [CapDerivationTree.spliceNode_edges_eq]
  unfold CapDerivationTree.childrenOf at hC
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hC
  have heE := (List.mem_filter.1 he).1
  cases hF : cdt.edges.find? (fun x => x.isChildOf e.child) with
  | none =>
    have := List.find?_eq_none.1 hF e heE
    simp [CapDerivationEdge.isChildOf] at this
  | some up =>
    have hUp := List.mem_of_find?_eq_some hF
    have hUc : up.child = e.child := by
      have := List.find?_some (p := fun (x : CapDerivationEdge) => x.isChildOf e.child) hF; simpa [CapDerivationEdge.isChildOf] using this
    exact spliceEdges_length_lt_of_parent hF (hUc ▸ CapDerivationTree.edgeWellFounded_no_self_edge hWF hUp)

/-- **A finalising delete's tree is the splice of its slot**: the delete
splices the slot out and the teardown writes no edge. -/
theorem cspaceDeleteSlotFinalising_ok_cdt {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    st'.cdt = st.cdt.spliceNode addr := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  rw [finaliseDestroyedCapabilities_eq_ok_state] at hF
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hF
  subst hF
  obtain ⟨stC, hC, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st1 hD
  rw [retireFinalisedObject, retireFinalObject_cdt, finaliseFinalObject_cdt,
    finaliseDestroyedCapabilitiesState_cdt, spliceDeletedCdtNode_cdt,
    cspaceDeleteSlotCore_cdt_eq st stC addr hC]

/-- A slot's link, read as the loop reads it: its two words, decoded. -/
theorem slotLinkAt_eq_decodeLink (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) :
    st.slotLinkAt ⟨o, s⟩ f = decodeLink (st.slotLinkNodeWord o s f) (st.slotLinkSlotWord o s f) := by
  unfold SystemState.slotLinkAt SystemState.slotLinkNodeWord SystemState.slotLinkSlotWord
    SystemState.getObject?
  cases st.objects[o]? with
  | none => simp [decodeLink]
  | some ob => exact KernelObject.linkAt_eq_decode ob s f

/-- **A splice keeps every edge clear of the spliced slot.** -/
theorem spliceEdgesFrom_keeps (node : SlotRef) (kids : List CapDerivationEdge)
    {e : CapDerivationEdge} (hp : e.parent ≠ node) (hc : e.child ≠ node) :
    ∀ l : List CapDerivationEdge, e ∈ l → e ∈ CapDerivationTree.spliceEdgesFrom node kids l
  | [], h => absurd h List.not_mem_nil
  | a :: l, h => by
    unfold CapDerivationTree.spliceEdgesFrom
    by_cases ha : a.child = node
    · rw [if_pos ha]
      rcases List.mem_cons.1 h with rfl | h
      · exact absurd ha hc
      · apply List.mem_append_right
        unfold CapDerivationTree.withoutNodeEdges
        exact List.mem_filter.2 ⟨h, by
          simp [CapDerivationEdge.isParentOf, CapDerivationEdge.isChildOf, hp, hc]⟩
    · rw [if_neg ha]
      by_cases hb : a.parent = node
      · rw [if_pos hb]
        rcases List.mem_cons.1 h with rfl | h
        · exact absurd hb hp
        · exact spliceEdgesFrom_keeps node kids hp hc l h
      · rw [if_neg hb]
        rcases List.mem_cons.1 h with rfl | h
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (spliceEdgesFrom_keeps node kids hp hc l h)

/-- **A slot no edge names stays unnamed by a splice**: the edges it re-makes
take a parent and the children from edges already there. -/
theorem spliceEdgesFrom_avoid (node : SlotRef) (kids : List CapDerivationEdge) (a : SlotRef)
    (hk : ∀ e ∈ kids, e.child ≠ a) :
    ∀ l : List CapDerivationEdge, (∀ e ∈ l, e.parent ≠ a ∧ e.child ≠ a) →
      ∀ e ∈ CapDerivationTree.spliceEdgesFrom node kids l, e.parent ≠ a ∧ e.child ≠ a
  | [], _ => by simp [CapDerivationTree.spliceEdgesFrom]
  | b :: l, h => by
    have hb := h b (List.mem_cons_self ..)
    have hl := fun e he => h e (List.mem_cons_of_mem b he)
    unfold CapDerivationTree.spliceEdgesFrom
    split
    · intro e he
      rcases List.mem_append.1 he with he | he
      · unfold CapDerivationTree.reparentEdges at he
        obtain ⟨k, hk', rfl⟩ := List.mem_map.1 he
        exact ⟨hb.1, hk k hk'⟩
      · unfold CapDerivationTree.withoutNodeEdges at he
        exact hl e (List.mem_filter.1 he).1
    · split
      · exact spliceEdgesFrom_avoid node kids a hk l hl
      · intro e he
        rcases List.mem_cons.1 he with rfl | he
        · exact hb
        · exact spliceEdgesFrom_avoid node kids a hk l hl e he

/-- **A spliced slot is named by no edge after**, in a tree with no edge from a
slot to itself. -/
theorem spliceEdgesFrom_avoid_self (node : SlotRef) (kids : List CapDerivationEdge)
    (hk : ∀ e ∈ kids, e.child ≠ node) :
    ∀ l : List CapDerivationEdge, (∀ e ∈ l, e.parent ≠ e.child) →
      ∀ e ∈ CapDerivationTree.spliceEdgesFrom node kids l, e.parent ≠ node ∧ e.child ≠ node
  | [], _ => by simp [CapDerivationTree.spliceEdgesFrom]
  | b :: l, h => by
    have hb := h b (List.mem_cons_self ..)
    have hl := fun e he => h e (List.mem_cons_of_mem b he)
    unfold CapDerivationTree.spliceEdgesFrom
    split
    · next hc =>
      intro e he
      rcases List.mem_append.1 he with he | he
      · unfold CapDerivationTree.reparentEdges at he
        obtain ⟨k, hk', rfl⟩ := List.mem_map.1 he
        exact ⟨fun e => hb (e.trans hc.symm), hk k hk'⟩
      · unfold CapDerivationTree.withoutNodeEdges at he
        have := (List.mem_filter.1 he).2
        simp [CapDerivationEdge.isParentOf, CapDerivationEdge.isChildOf] at this
        exact this
    · next hc =>
      split
      · exact spliceEdgesFrom_avoid_self node kids hk l hl
      · next hp =>
        intro e he
        rcases List.mem_cons.1 he with rfl | he
        · exact ⟨hp, hc⟩
        · exact spliceEdgesFrom_avoid_self node kids hk l hl e he

/-- **Whether no edge of the tree names the slot `a`.** -/
def CdtAvoids (cdt : CapDerivationTree) (a : SlotRef) : Prop :=
  ∀ e ∈ cdt.edges, e.parent ≠ a ∧ e.child ≠ a

theorem CdtAvoids.splice {cdt : CapDerivationTree} {a : SlotRef} (h : CdtAvoids cdt a)
    (node : SlotRef) : CdtAvoids (cdt.spliceNode node) a := by
  unfold CdtAvoids
  rw [CapDerivationTree.spliceNode_edges_eq]
  exact spliceEdgesFrom_avoid node _ a
    (fun e he => (h e (List.mem_filter.1 he).1).2) _ h

theorem CdtAvoids.of_splice_self {cdt : CapDerivationTree} (hWF : cdt.edgeWellFounded)
    (node : SlotRef) : CdtAvoids (cdt.spliceNode node) node := by
  unfold CdtAvoids
  rw [CapDerivationTree.spliceNode_edges_eq]
  refine spliceEdgesFrom_avoid_self node _ (fun e he => ?_) _
    (fun e he => CapDerivationTree.edgeWellFounded_no_self_edge hWF he)
  have hm := List.mem_filter.1 he
  have hp : e.parent = node := by simpa [CapDerivationEdge.isParentOf] using hm.2
  exact fun hc => CapDerivationTree.edgeWellFounded_no_self_edge hWF hm.1 (hp.trans hc.symm)

theorem CdtAvoids.childless {cdt : CapDerivationTree} {a : SlotRef} (h : CdtAvoids cdt a) :
    cdt.childrenOf a = [] := by
  unfold CapDerivationTree.childrenOf
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro e he
  simpa [CapDerivationEdge.isParentOf] using (h e he).1

theorem mem_childrenOf_iff {cdt : CapDerivationTree} {p c : SlotRef} :
    c ∈ cdt.childrenOf p ↔ ∃ e ∈ cdt.edges, e.parent = p ∧ e.child = c := by
  unfold CapDerivationTree.childrenOf
  simp only [List.mem_map, List.mem_filter, CapDerivationEdge.isParentOf, decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨he, hp⟩, hc⟩; exact ⟨e, he, hp, hc⟩
  · rintro ⟨e, he, hp, hc⟩; exact ⟨e, ⟨he, hp⟩, hc⟩

/-- **A splice of any other slot keeps a child its parent's**. -/
theorem mem_childrenOf_splice {cdt : CapDerivationTree} {p c x : SlotRef}
    (h : c ∈ cdt.childrenOf p) (hp : x ≠ p) (hc : x ≠ c) : c ∈ (cdt.spliceNode x).childrenOf p := by
  obtain ⟨e, he, rfl, rfl⟩ := mem_childrenOf_iff.1 h
  refine mem_childrenOf_iff.2 ⟨e, ?_, rfl, rfl⟩
  rw [CapDerivationTree.spliceNode_edges_eq]
  exact spliceEdgesFrom_keeps x _ (Ne.symm hp) (Ne.symm hc) _ he

/-- **What the revocation's progress reads along a delete's chain**: the
capability invariants hold, the tree has at most `E` edges, and either the
child `c` is still a child of the source `src`, or the tree has lost an edge, or
no edge names the source any more. -/
def RevokeProgress (src c : SlotRef) (E : Nat) (s : SystemState) : Prop :=
  capabilityInvariantBundle s ∧ s.cdt.edges.length ≤ E ∧
    (c ∈ s.cdt.childrenOf src ∨ s.cdt.edges.length < E ∨ CdtAvoids s.cdt src)

/-- **A finalising delete keeps the progress**, and makes it strict when it
deletes the child. -/
theorem RevokeProgress.step {src c : SlotRef} {E : Nat} {ec : Concurrency.CoreId}
    {x : CSpaceAddr} {s s' : SystemState} (h : RevokeProgress src c E s)
    (hD : cspaceDeleteSlotFinalising ec x s = .ok ((), s')) :
    RevokeProgress src c E s' ∧ (x = c → s'.cdt.edges.length < E ∨ CdtAvoids s'.cdt src) := by
  obtain ⟨hInv, hLe, hOr⟩ := h
  have hInv' := cspaceDeleteSlotFinalising_preserves_capabilityInvariantBundle ec x s s' hInv hD
  have hCdt := cspaceDeleteSlotFinalising_ok_cdt hD
  have hLe' : s'.cdt.edges.length ≤ s.cdt.edges.length := by
    rw [hCdt, CapDerivationTree.spliceNode_edges_eq]; exact CapDerivationTree.spliceEdges_length_le _ _
  have hStrict : c ∈ s.cdt.childrenOf src → x = c → s'.cdt.edges.length < E := fun hm hx => by
    have := spliceNode_edges_length_lt hInv.2.2.1 hm
    rw [← hx, ← hCdt] at this; omega
  refine ⟨⟨hInv', by omega, ?_⟩, fun hx => ?_⟩
  · rcases hOr with hm | hl | ha
    · by_cases hxc : x = c
      · exact .inr (.inl (hStrict hm hxc))
      · by_cases hxs : x = src
        · subst hxs; rw [hCdt]; exact .inr (.inr (CdtAvoids.of_splice_self hInv.2.2.1 _))
        · rw [hCdt]; exact .inl (mem_childrenOf_splice hm hxs hxc)
    · exact .inr (.inl (by omega))
    · rw [hCdt]; exact .inr (.inr (ha.splice x))
  · rcases hOr with hm | hl | ha
    · exact .inl (hStrict hm hx)
    · exact .inl (by omega)
    · rw [hCdt]; exact .inr (ha.splice x)

/-- **A finalisation keeps the progress**: it writes no edge. -/
theorem RevokeProgress.finalise {src c : SlotRef} {E : Nat} {s : SystemState} (target : Nat)
    (h : RevokeProgress src c E s) : RevokeProgress src c E (finaliseFinalObject target s) := by
  obtain ⟨hInv, hLe, hOr⟩ := h
  refine ⟨finaliseFinalObject_preserves_capabilityInvariantBundle target s hInv, ?_, ?_⟩ <;>
    rw [finaliseFinalObject_cdt]
  · exact hLe
  · exact hOr

/-- **A source no edge names stays childless** through any chain of finalising
deletes and finalisations. -/
theorem FinalisingDeleteChain.avoids {ec : Concurrency.CoreId} {src : SlotRef}
    {st st' : SystemState} (hC : FinalisingDeleteChain ec st st') (h : CdtAvoids st.cdt src) :
    CdtAvoids st'.cdt src :=
  hC.closed (fun s => CdtAvoids s.cdt src)
    (fun x s s' hs hD => by
      show CdtAvoids s'.cdt src
      rw [cspaceDeleteSlotFinalising_ok_cdt hD]; exact hs.splice x)
    (fun d s hs => by
      show CdtAvoids (finaliseFinalObject d s).cdt src
      rw [finaliseFinalObject_cdt]; exact hs) h

/-- **A slot the tree names holds a capability, so its delete is admitted**. -/
theorem cspaceDeleteFinalisingAdmitted_of_child {st : SystemState} {p c : SlotRef}
    (hInv : capabilityInvariantBundle st) (hm : c ∈ st.cdt.childrenOf p) :
    cspaceDeleteFinalisingAdmitted c st = true := by
  have hMent : st.cdt.mentions c := by
    obtain ⟨e, he, -, hc⟩ := mem_childrenOf_iff.1 hm
    exact .inl ⟨e, he, .inr hc⟩
  obtain ⟨o, hO, hL⟩ := hInv.2.1 _ hMent
  unfold cspaceDeleteFinalisingAdmitted SystemState.getObject?
  rw [hO]
  exact KernelObject.hasSlot_holdsSlots (KernelObject.hasSlot_of_slotCap hL)

/-- **One zombie delete of a child of the source makes progress**: the tree
loses an edge, or no edge names the source any more, or the delete kept the
child's slot, its passes out of fuel (`zombieDeleteAtFuel`), which ends the
revocation (`revokeFirstChildLoop`).  Every step of the chain
keeps `RevokeProgress`; the last deletes the child, which on a state the
capability invariants hold in is admitted while it is still the source's
child. -/
theorem zombieDeleteAt_revokeProgress (ec : Concurrency.CoreId) {src : SlotRef}
    {cn : SeLe4n.ObjId} {sl : SeLe4n.Slot} {st : SystemState}
    (hInv : capabilityInvariantBundle st) (hm : ⟨cn, sl⟩ ∈ st.cdt.childrenOf src) :
    capabilityInvariantBundle (zombieDeleteAt ec cn sl st) ∧
      ((zombieDeleteAt ec cn sl st).cdt.edges.length < st.cdt.edges.length ∨
        CdtAvoids (zombieDeleteAt ec cn sl st).cdt src ∨
        zombieSlotClass (zombieDeleteAt ec cn sl st) cn sl cn sl ≠ 0) := by
  have hAdm := cspaceDeleteFinalisingAdmitted_of_child hInv hm
  have h0 : RevokeProgress src ⟨cn, sl⟩ st.cdt.edges.length st := ⟨hInv, Nat.le_refl _, .inl hm⟩
  -- the child's own delete, from a state with progress
  have hLast : ∀ s, RevokeProgress src ⟨cn, sl⟩ st.cdt.edges.length s →
      capabilityInvariantBundle (zombieDeleteSlot ec cn sl s) ∧
        ((zombieDeleteSlot ec cn sl s).cdt.edges.length < st.cdt.edges.length ∨
          CdtAvoids (zombieDeleteSlot ec cn sl s).cdt src) := by
    intro s hP
    unfold zombieDeleteSlot
    split
    · next hA =>
      have hD := cspaceDeleteSlotFinalising_of_slotHolder (ec := ec) hA
      obtain ⟨hP', hS⟩ := hP.step hD
      exact ⟨hP'.1, hS rfl⟩
    · next hA =>
      obtain ⟨hI, -, hOr⟩ := hP
      rcases hOr with hm' | hl | ha
      · exact absurd (cspaceDeleteFinalisingAdmitted_of_child hI hm') hA
      · exact ⟨hI, .inl hl⟩
      · exact ⟨hI, .inr ha⟩
  rcases zombieDeleteAt_cases ec cn sl st with ⟨hD, e⟩ | ⟨n, -, hR, e⟩
  · rw [e]
    have hStep := cspaceDeleteSlotFinalising_of_admitted (ec := ec) hD
    obtain ⟨hP', hS⟩ := h0.step hStep
    exact ⟨hP'.1, (hS rfl).imp_right .inl⟩
  · rw [e]
    have hP := hR.chain.closed (RevokeProgress src ⟨cn, sl⟩ st.cdt.edges.length)
      (fun _ _ _ hs hD => (hs.step hD).1) (fun d _ hs => hs.finalise d) h0
    rcases zombieDeleteAtFuel_kept_or_deleted ec cn sl (zombieFuel st) st with
      ⟨-, e'⟩ | ⟨hK, e'⟩
    · rw [e']
      obtain ⟨hB, hO⟩ := hLast _ hP
      exact ⟨hB, hO.imp_right .inl⟩
    · rw [e']
      exact ⟨hP.1, .inr (.inr hK)⟩

/-- **On a state the bundle holds in, the loop empties the source of children**
when its fuel exceeds the tree's edges.  The source's first-child link is the
head of its children (`cdtLinksAgree`); a child is in the tree, so its CNode is
a slot of a live object (`cdtCompleteness`) and its delete is admitted, never
the loop's stop; each child's zombie delete keeps the bundle and either takes an
edge out of the tree or leaves the source named by no edge, and so childless for
good (`zombieDeleteAt_revokeProgress`), so the fuel never runs out first — or
the loop stops at a child whose zombie delete kept its slot, its passes out of
fuel, which a reachable state never reaches (`docs/planning/UNTYPED_RESET_PLAN.md`
row 29); the caller then sees that slot occupied and retries. -/
theorem revokeFirstChildLoop_childless (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) :
    ∀ (n : Nat) (st : SystemState), capabilityInvariantBundle st →
      st.cdt.edges.length < n →
      (revokeFirstChildLoop ec cnode slot n st).cdt.childrenOf ⟨cnode, slot⟩ = [] ∨
        ∃ cc cs, zombieSlotClass (revokeFirstChildLoop ec cnode slot n st) cc cs cc cs ≠ 0
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, st, hInv, hn => by
    have hHead := hInv.linksAgree.firstChild ⟨cnode, slot⟩
    rw [slotLinkAt_eq_decodeLink] at hHead
    unfold revokeFirstChildLoop
    dsimp only
    split
    · next h0 =>
      rw [h0] at hHead
      exact .inl (List.head?_eq_none_iff.1 (by simpa [decodeLink] using hHead.symm))
    · next h0 =>
      simp only [decodeLink, h0, if_false] at hHead
      have hMem := List.mem_of_mem_head? hHead.symm
      have hMent : st.cdt.mentions ⟨SeLe4n.ObjId.ofNat (st.slotLinkNodeWord cnode slot .firstChild - 1),
          SeLe4n.Slot.ofNat (st.slotLinkSlotWord cnode slot .firstChild - 1)⟩ := by
        unfold CapDerivationTree.childrenOf at hMem
        obtain ⟨e, he, hc⟩ := List.mem_map.1 hMem
        exact .inl ⟨e, (List.mem_filter.1 he).1, .inr hc⟩
      obtain ⟨o, hO, hL⟩ := hInv.2.1 _ hMent
      have hAdm : cspaceDeleteFinalisingAdmitted
          ⟨SeLe4n.ObjId.ofNat (st.slotLinkNodeWord cnode slot .firstChild - 1),
            SeLe4n.Slot.ofNat (st.slotLinkSlotWord cnode slot .firstChild - 1)⟩ st = true := by
        unfold cspaceDeleteFinalisingAdmitted SystemState.getObject?
        rw [hO]
        exact KernelObject.hasSlot_holdsSlots (KernelObject.hasSlot_of_slotCap hL)
      rw [if_pos hAdm]
      obtain ⟨hInv2, hProg⟩ := zombieDeleteAt_revokeProgress ec hInv hMem
      split
      · next hK =>
        rcases hProg with hLt | hAv | hK'
        · exact revokeFirstChildLoop_childless ec cnode slot n _ hInv2 (by omega)
        · exact .inl ((revokeFirstChildLoop_chain ec cnode slot n _).avoids hAv).childless
        · exact absurd hK hK'
      · next hK => exact .inr ⟨_, _, hK⟩

/-- **The revocation is complete**: on a state the capability invariants hold
in, a successful revocation leaves its source with no children, as seL4's
`cteRevoke` does, or stops at a child whose zombie delete kept its slot, its
passes out of fuel (`revokeFirstChildLoop_childless`), and is retried.  The loop's fuel, one more than the tree's edge bound, exceeds
its edges (`CapDerivationTree.edges_length_le`). -/
theorem cspaceRevokeCdtFinalising_ok_childless (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (hInv : capabilityInvariantBundle st)
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    st'.cdt.childrenOf addr = [] ∨ ∃ cc cs, zombieSlotClass st' cc cs cc cs ≠ 0 := by
  unfold cspaceRevokeCdtFinalising at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    subst h
    exact revokeFirstChildLoop_childless ec addr.cnode addr.slot _ st hInv
      (Nat.lt_succ_of_le (CapDerivationTree.edges_length_le _))
  · split at h <;> cases h

end SeLe4n.Kernel
