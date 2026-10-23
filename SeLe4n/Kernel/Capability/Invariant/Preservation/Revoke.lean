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
(`cspaceRevokeCdtFinalising_ok_childless`), as seL4's `cteRevoke` leaves it.
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
  generalize hX : SeLe4n.ObjId.ofNat (target - 1) = x at hUn hNamed
  have hx := hNamed hT
  obtain ⟨hI', -, -, hCdt, hW⟩ := retireFinalObject_frame ec target recorder st h.2.2.2.2.1
  rw [hX] at hW
  generalize retireFinalObject ec target recorder st = st' at hUn hI' hCdt hW ⊢
  have hCnB : ∀ (oid : SeLe4n.ObjId) (cn : CNode),
      st'.objects[oid]? = some (.cnode cn) → st.objects[oid]? = some (.cnode cn) := by
    intro oid cn hC
    rcases hW oid with e | ⟨-, -, hn⟩ | ⟨U, -, hU'⟩
    · rwa [← e]
    · rw [hn] at hC; cases hC
    · rw [hU'] at hC; cases hC
  have hCnF : ∀ (oid : SeLe4n.ObjId) (cn : CNode),
      st.objects[oid]? = some (.cnode cn) → st'.objects[oid]? = some (.cnode cn) := by
    intro oid cn hC
    rcases hW oid with e | ⟨-, hc, -⟩ | ⟨U, hU, -⟩
    · rwa [e]
    · rcases hc with ⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩ <;> simp_all
    · rw [hU] at hC; cases hC
  have hTcb : ∀ oid : SeLe4n.ObjId,
      (st'.objects[oid]?).bind KernelObject.tcbSlots = (st.objects[oid]?).bind KernelObject.tcbSlots := by
    intro oid
    rcases hW oid with e | ⟨-, hc, hn⟩ | ⟨U, hU, hU'⟩
    · rw [e]
    · rw [hn]
      rcases hc with ⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩
      · rw [hf]; rfl
      · rw [hu]; rfl
      · rw [hr]; rfl
      · rw [hp]; rfl
    · rw [hU, hU']; rfl
  have hCn : ∀ (oid : SeLe4n.ObjId) (cn : CNode),
      st'.objects[oid]? = some (.cnode cn) ↔ st.objects[oid]? = some (.cnode cn) :=
    fun oid cn => ⟨hCnB oid cn, hCnF oid cn⟩
  have hCap : ∀ r, st'.slotCapAt r = st.slotCapAt r := fun r => by
    rw [SystemState.slotCapAt_eq_bind, SystemState.slotCapAt_eq_bind]
    exact (KernelObject.optSlots_eq_of_cnode_iff (hCn r.cnode) (hTcb r.cnode)).1 r.slot
  obtain ⟨hB, hL⟩ := capabilityBundleOffLinks_of_frame h hCdt hCnB hCnF hTcb (fun rid hR => by
    unfold SystemState.getReply? at hR ⊢
    rcases hW rid.toObjId with e | ⟨-, hc, -⟩ | ⟨U, hU, -⟩
    · rwa [e]
    · rcases hc with ⟨f, hf⟩ | ⟨u, hu⟩ | ⟨r, hr⟩ | ⟨p, hp⟩ <;> simp_all
    · rw [hU] at hR; exact absurd rfl hR) hI'
  refine hB.withLinks hL ((hShape.retire hx (fun o hp ho => ?_) (fun u U' hu => ?_)).of_readers
    hCdt hCap (fun _ hp => hp) rfl)
  · rcases hW o with e | ⟨he, -, -⟩ | ⟨U, -, hU'⟩
    · show st'.objects[o]? ≠ none; rw [e]; exact hp
    · exact absurd he ho
    · show st'.objects[o]? ≠ none; rw [hU']; exact Option.some_ne_none _
  · have hu' := (SystemState.getUntyped?_eq_some_iff st' u U').mp hu
    rcases hW u with e | ⟨-, -, hn⟩ | ⟨U, hU, hU'⟩
    · refine ⟨U', (SystemState.getUntyped?_eq_some_iff st u U').mpr (e ▸ hu'), rfl,
        fun ch hch => ⟨hch, hUn u U' hu' ch hch⟩⟩
    · rw [hn] at hu'; cases hu'
    · rw [hU'] at hu'; cases hu'
      exact ⟨U, (SystemState.getUntyped?_eq_some_iff st u U).mpr hU, rfl,
        fun ch hch => mem_childListErase.mp hch⟩

theorem objId_ofNat_succ_sub_one (x : SeLe4n.ObjId) : SeLe4n.ObjId.ofNat (x.val + 1 - 1) = x := by
  simp [SeLe4n.ObjId.ofNat]

/-- **What a nonzero retire word names**: the slot's capability names the
target by `.object`, and under the capability bundle it is the target's final
capability (`capIsFinal_iff_capFinalSpec`). -/
theorem slotRetireTarget_spec {st : SystemState} {cnode : SeLe4n.ObjId} {slot : SeLe4n.Slot}
    (h : capabilityInvariantBundle st) (hT : slotRetireTarget st cnode slot ≠ 0) :
    ∃ c, st.slotCapAt ⟨cnode, slot⟩ = some c ∧
      c.target = .object (SeLe4n.ObjId.ofNat (slotRetireTarget st cnode slot - 1)) ∧
      st.capFinalSpec ⟨cnode, slot⟩ := by
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
        exact ⟨c, rfl, by rw [hTg, objId_ofNat_succ_sub_one],
          (capIsFinal_iff_capFinalSpec h ⟨cnode, slot⟩).mp hc.2⟩
      · exact absurd rfl hT
    | cnodeSlot _ _ => rw [hTg] at hT; exact absurd rfl hT
    | replyCap _ => rw [hTg] at hT; exact absurd rfl hT
    | auditTrail => rw [hTg] at hT; exact absurd rfl hT

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

/-- **The finalising delete keeps the capability invariants**: the delete keeps
them (`cspaceDeleteSlot_preserves_capabilityInvariantBundle`), the teardown
after it writes neither the tree nor any slot
(`finaliseDestroyedCapabilities_preserves_capabilityInvariantBundle`), and the
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
  refine retireFinalObject_preserves_capabilityInvariantBundle ec _ _ st2 h2
    (fun hT r hr => ?_) (fun hT => ?_)
  · obtain ⟨c, hc, ht, hFin⟩ := slotRetireTarget_spec hInv hT
    have hAddr : SystemState.namesAt st.slotCapAt ⟨addr.cnode, addr.slot⟩
        (SeLe4n.ObjId.ofNat (slotRetireTarget st addr.cnode addr.slot - 1)) :=
      ⟨c, hc, by unfold Capability.namedObject; rw [ht]⟩
    rw [SystemState.namesAt_of_eq (hC2 r)] at hr
    by_cases hra : r = addr
    · subst hra
      obtain ⟨c', hc', -⟩ := hr
      rw [hC1n] at hc'; cases hc'
    · rw [SystemState.namesAt_of_eq (hC1 r hra)] at hr
      exact hFin _ hAddr r hra hr
  · have hU := hU2.trans hU1
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
  rw [retireFinalObject_cdt, finaliseDestroyedCapabilitiesState_cdt, spliceDeletedCdtNode_cdt,
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

/-- **On a state the bundle holds in, the loop empties the source of children**
when its fuel exceeds the tree's edges.  The source's first-child link is the
head of its children (`cdtLinksAgree`); a child is in the tree, so its CNode is
a slot of a live object (`cdtCompleteness`) and its delete is admitted, never
the loop's stop;
each delete keeps the bundle and splices one edge out
(`spliceNode_edges_length_lt`), so the fuel never runs out first. -/
theorem revokeFirstChildLoop_childless (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) :
    ∀ (n : Nat) (st : SystemState), capabilityInvariantBundle st →
      st.cdt.edges.length < n →
      (revokeFirstChildLoop ec cnode slot n st).cdt.childrenOf ⟨cnode, slot⟩ = []
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, st, hInv, hn => by
    have hHead := hInv.linksAgree.firstChild ⟨cnode, slot⟩
    rw [slotLinkAt_eq_decodeLink] at hHead
    unfold revokeFirstChildLoop
    dsimp only
    split
    · next h0 =>
      rw [h0] at hHead
      exact List.head?_eq_none_iff.1 (by simpa [decodeLink] using hHead.symm)
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
      have hD := cspaceDeleteSlotFinalising_of_slotHolder (ec := ec) hAdm
      have hInv2 := cspaceDeleteSlotFinalising_preserves_capabilityInvariantBundle ec _ st _ hInv hD
      have hLt := spliceNode_edges_length_lt hInv.2.2.1 hMem
      rw [← cspaceDeleteSlotFinalising_ok_cdt hD] at hLt
      exact revokeFirstChildLoop_childless ec cnode slot n _ hInv2 (by omega)

/-- **The revocation is complete**: on a state the capability invariants hold
in, a successful revocation leaves its source with no children, as seL4's
`cteRevoke` does.  The loop's fuel, one more than the tree's edge bound, exceeds
its edges (`CapDerivationTree.edges_length_le`). -/
theorem cspaceRevokeCdtFinalising_ok_childless (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (hInv : capabilityInvariantBundle st)
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    st'.cdt.childrenOf addr = [] := by
  unfold cspaceRevokeCdtFinalising at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    subst h
    exact revokeFirstChildLoop_childless ec addr.cnode addr.slot _ st hInv
      (Nat.lt_succ_of_le (CapDerivationTree.edges_length_le _))
  · split at h <;> cases h

end SeLe4n.Kernel
