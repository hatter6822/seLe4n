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

/-- **The finalising delete keeps the capability invariants**: the delete keeps
them (`cspaceDeleteSlot_preserves_capabilityInvariantBundle`), and the teardown
after it writes neither the tree nor any CNode or reply object
(`finaliseDestroyedCapabilities_ok_frame`, `finaliseDestroyedCapabilitiesState_cdt`). -/
theorem cspaceDeleteSlotFinalising_preserves_capabilityInvariantBundle
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hInv : capabilityInvariantBundle st)
    (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  obtain ⟨st1, hD, hF⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  have h1 := cspaceDeleteSlot_preserves_capabilityInvariantBundle st st1 addr hInv hD
  obtain ⟨hI', hW, -⟩ := finaliseDestroyedCapabilities_ok_frame ec _ _ st1 st' h1.2.2.2.2.1 hF
  have hCdt : st'.cdt = st1.cdt := by
    rw [finaliseDestroyedCapabilities_eq_ok_state] at hF
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hF
    subst hF
    exact finaliseDestroyedCapabilitiesState_cdt ec _ _ st1
  refine capabilityInvariantBundle_of_frame h1 hCdt ?_ ?_ ?_ hI'
  · intro oid cn hC
    rcases hW oid with e | ⟨-, ⟨r, hr⟩⟩
    · rwa [← e]
    · rw [hr] at hC; cases hC
  · intro oid cn hC
    rcases hW oid with e | ⟨⟨r, hr⟩, -⟩
    · rwa [e]
    · rw [hr] at hC; cases hC
  · intro rid hR
    unfold SystemState.getReply? at hR ⊢
    rcases hW rid.toObjId with e | ⟨⟨r, hr⟩, -⟩
    · rwa [e]
    · rw [hr] at hR; exact absurd rfl hR

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

/-- An element `q` keeps and `p` drops is in neither filter, so the two
together are shorter than the list. -/
private theorem filter_neither_length_add_lt {α : Type} (p q : α → Bool) :
    ∀ (l : List α) (x : α), x ∈ l → q x = true → p x = false →
      (l.filter (fun e => !p e && !q e)).length + (l.filter p).length < l.length
  | [], _, hx, _, _ => by cases hx
  | y :: ys, x, hx, hq, hp => by
    rcases List.mem_cons.1 hx with rfl | hx
    · have := filter_neither_length_add_le p q ys
      simp [List.filter_cons, hp, hq]; omega
    · have ih := filter_neither_length_add_lt p q ys x hx hq hp
      cases hpy : p y <;> cases hqy : q y <;> simp [List.filter_cons, hpy, hqy] <;> omega

/-- **A splice of a node with a parent edge takes an edge out**: the node's
edges go and only its child edges are re-made, so its parent edge is the one
lost.  (A parent edge from the node to itself would be re-made too; an acyclic
tree has none.) -/
theorem spliceEdges_length_lt_of_parent {es : List CapDerivationEdge} {node : SlotRef}
    {up : CapDerivationEdge} (hF : es.find? (fun e => e.isChildOf node) = some up)
    (hNe : up.parent ≠ node) : (CapDerivationTree.spliceEdges es node).length < es.length := by
  unfold CapDerivationTree.spliceEdges
  rw [hF, CapDerivationTree.reparentEdges_length]
  have hq : up.isChildOf node = true := List.find?_some (p := fun (e : CapDerivationEdge) => e.isChildOf node) hF
  have hp : up.isParentOf node = false := by
    simp [CapDerivationEdge.isParentOf, hNe]
  have := filter_neither_length_add_lt (·.isParentOf node) (·.isChildOf node) es up
    (List.mem_of_find?_eq_some hF) hq hp
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
  obtain ⟨st1, hD, hF⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  rw [finaliseDestroyedCapabilities_eq_ok_state] at hF
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hF
  subst hF
  obtain ⟨stC, hC, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st1 hD
  rw [finaliseDestroyedCapabilitiesState_cdt, spliceDeletedCdtNode_cdt,
    cspaceDeleteSlotCore_cdt_eq st stC addr hC]

/-- A slot's link, read as the loop reads it: its two words, decoded. -/
theorem slotLinkAt_eq_decodeLink (st : SystemState) (o : SeLe4n.ObjId) (s : SeLe4n.Slot)
    (f : LinkField) :
    st.slotLinkAt ⟨o, s⟩ f = decodeLink (st.slotLinkNodeWord o s f) (st.slotLinkSlotWord o s f) := by
  unfold SystemState.slotLinkAt SystemState.slotLinkNodeWord SystemState.slotLinkSlotWord
  cases st.getCNode? o with
  | none => simp [decodeLink]
  | some cn => rfl

/-- **On a state the bundle holds in, the loop empties the source of children**
when its fuel exceeds the tree's edges.  The source's first-child link is the
head of its children (`cdtLinksAgree`); a child is in the tree, so its CNode is
live (`cdtCompleteness`) and its delete is admitted, never the loop's stop;
each delete keeps the bundle and splices one edge out
(`spliceNode_edges_length_lt`), so the fuel never runs out first. -/
theorem revokeFirstChildLoop_childless (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) :
    ∀ (n : Nat) (st : SystemState), capabilityInvariantBundle st →
      st.cdt.edges.length < n →
      (revokeFirstChildLoop ec cnode slot n st).cdt.childrenOf ⟨cnode, slot⟩ = []
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, st, hInv, hn => by
    have hHead := hInv.2.2.2.2.2.2.firstChild ⟨cnode, slot⟩
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
        exact ⟨e, (List.mem_filter.1 he).1, .inr hc⟩
      obtain ⟨cn, hCn, -⟩ := hInv.2.1 _ hMent
      have hAdm : cspaceDeleteFinalisingAdmitted
          ⟨SeLe4n.ObjId.ofNat (st.slotLinkNodeWord cnode slot .firstChild - 1),
            SeLe4n.Slot.ofNat (st.slotLinkSlotWord cnode slot .firstChild - 1)⟩ st = true := by
        unfold cspaceDeleteFinalisingAdmitted
        rw [(SystemState.getCNode?_eq_some_iff st _ cn).2 hCn]
      rw [if_pos hAdm]
      have hD := cspaceDeleteSlotFinalising_of_cnode (ec := ec) hAdm
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
