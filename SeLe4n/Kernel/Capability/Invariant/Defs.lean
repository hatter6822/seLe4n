-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Lifecycle.Invariant
import SeLe4n.Model.CapabilityFinality

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

-- WS-RC R4.A close-out (Phase A2.c4): the historical state-level
-- `cspaceSlotUnique` predicate and its `cspaceSlotUnique_trivial`
-- discharge helper have been deleted.  Per-CNode slot uniqueness is now
-- carried structurally by `CNode.slots : UniqueSlotMap Capability` via
-- the `UniqueSlotMap.hWF` field; the canonical discharge is
-- `SeLe4n.Model.CNode.slotsUnique_holds` (or its plan-named alias
-- `SeLe4n.Model.CNode.cnode_slots_unique`).

/-- Lookup completeness: every capability stored in a CNode's slot HashMap is
retrievable via `lookupSlotCap`, and every capability stored in any object's
slot — a CNode's or a thread's space slot — is retrievable via the slot
reader `SystemState.slotCapAt`.

WS-G5: With HashMap-backed slots, lookup completeness is direct — `CNode.lookup`
delegates to `HashMap.getElem?`, which is the canonical accessor. The property
is trivially true by the identity `CNode.lookup slot = cn.slots[slot]?`. -/
def cspaceLookupSound (st : SystemState) : Prop :=
  (∀ (cnodeId : SeLe4n.ObjId) (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability),
    st.objects[cnodeId]? = some (KernelObject.cnode cn) →
    cn.lookup slot = some cap →
    SystemState.lookupSlotCap st { cnode := cnodeId, slot := slot } = some cap) ∧
  (∀ (oid : SeLe4n.ObjId) (o : KernelObject) (slot : SeLe4n.Slot) (cap : Capability),
    st.objects[oid]? = some o →
    o.slotCap slot = some cap →
    st.slotCapAt { cnode := oid, slot := slot } = some cap)

/-- Attenuation rule operation-correctness lemma (proved by `cspaceAttenuationRule_holds`).
Not a state invariant (no `st` parameter); removed from `capabilityInvariantBundle` in WS-F6/D1. -/
def cspaceAttenuationRule : Prop :=
  ∀ parent child rights badge,
    mintDerivedCap parent rights badge = .ok child →
    capAttenuates parent child

/-- Lifecycle-transition authority monotonicity obligations for the active slice.

This models transition-local non-escalation constraints:
1. delete cannot leave authority in the deleted slot,
2. local revoke cannot leave sibling authority to the revoked target.

Direct mint/derive attenuation remains the dedicated `cspaceAttenuationRule` bundle component. -/
def lifecycleAuthorityMonotonicity (st : SystemState) : Prop :=
  (∀ addr st',
      cspaceDeleteSlot addr st = .ok ((), st') →
      st'.slotCapAt addr = none ∧ SystemState.lookupSlotCap st' addr = none) ∧
  (∀ addr st' parent,
      cspaceRevoke addr st = .ok ((), st') →
      cspaceLookupSlot addr st = .ok (parent, st) →
      ∀ slot cap,
        SystemState.lookupSlotCap st' { cnode := addr.cnode, slot := slot } = some cap →
        cap.target = parent.target →
        slot = addr.slot)

-- ============================================================================
-- WS-H4: Meaningful capability invariant predicates (replacing trivially-true)
-- ============================================================================

/-- WS-H4/M-08: CDT slot coherence — every slot the derivation tree names holds
a capability in a live CNode, so CDT-based revocation finds the capability each
node stands for.  Since WS-ZA ZA5.3 part 2 the tree's nodes are the slots
themselves, so an empty slot is outside the tree: a copy, mint, move or transfer
into an empty slot adds a node the tree did not have, which is what keeps it
acyclic (`addEdge_preserves_edgeWellFounded_fresh`).  Every operation that
empties a slot takes it out of the tree in the same step (the splice, the
revoke's removal, the move's rename). -/
def cdtCompleteness (st : SystemState) : Prop :=
  ∀ ref : SlotRef, st.cdt.mentions ref →
    ∃ o, st.objects[ref.cnode]? = some o ∧ o.slotCap ref.slot ≠ none

/-- WS-ZA ZA5.3: a slot the tree names is a slot of a live object (a CNode's
slot, a thread's space slot), so its links have words to live in
(`SystemState.slotInObject`). -/
theorem slotInObject_of_occupied {st : SystemState} {ref : SlotRef}
    (h : ∃ o, st.objects[ref.cnode]? = some o ∧ o.slotCap ref.slot ≠ none) :
    st.slotInObject ref := by
  obtain ⟨o, hO, hL⟩ := h
  exact ⟨o, hO, KernelObject.hasSlot_of_slotCap hL⟩

/-- A CNode slot that holds a capability is an occupied slot of its object. -/
theorem slotOccupied_of_cnode {st : SystemState} {ref : SlotRef}
    (h : ∃ cn, st.objects[ref.cnode]? = some (.cnode cn) ∧ cn.lookup ref.slot ≠ none) :
    ∃ o, st.objects[ref.cnode]? = some o ∧ o.slotCap ref.slot ≠ none :=
  h.elim fun cn hc => ⟨.cnode cn, hc.1, hc.2⟩

theorem cdtCompleteness.slotInObject {st : SystemState} (h : cdtCompleteness st)
    {ref : SlotRef} (hM : st.cdt.mentions ref) : st.slotInObject ref :=
  slotInObject_of_occupied (h ref hM)

/-- **WS-ZA ZA5.3: the slot links encode the derivation tree** (`LinksAgree`):
each slot's parent, first-child, next and previous links are what the tree says
they are, so the tree's executable reads can walk the links instead. -/
def cdtLinksAgree (st : SystemState) : Prop :=
  LinksAgree st.slotLinkAt st.cdt

/-- A step that keeps the tree and every slot's links keeps the agreement. -/
theorem cdtLinksAgree_of_eq {st st' : SystemState} (h : cdtLinksAgree st)
    (hCdt : st'.cdt = st.cdt) (hL : st'.slotLinkAt = st.slotLinkAt) : cdtLinksAgree st' := by
  unfold cdtLinksAgree at h ⊢; rw [hCdt, hL]; exact h

/-- A slot the tree names lies in an object that exists. -/
theorem cdtCompleteness.present {st : SystemState} (h : cdtCompleteness st)
    {ref : SlotRef} (hM : st.cdt.mentions ref) : st.objects[ref.cnode]? ≠ none := by
  obtain ⟨o, hO, -⟩ := h ref hM
  rw [hO]; simp

/-- An empty slot is outside the tree. -/
theorem cdtCompleteness.not_mentions_of_empty {st : SystemState} (h : cdtCompleteness st)
    {ref : SlotRef} (hEmpty : ∀ o, st.objects[ref.cnode]? = some o →
      o.slotCap ref.slot = none) : ¬ st.cdt.mentions ref := by
  intro hM
  obtain ⟨o, hO, hSome⟩ := h ref hM
  exact hSome (hEmpty o hO)

/-- An empty CNode slot is outside the tree. -/
theorem cdtCompleteness.not_mentions_of_empty_cnode {st : SystemState} (h : cdtCompleteness st)
    {ref : SlotRef} {cn : CNode} (hCn : st.objects[ref.cnode]? = some (.cnode cn))
    (hEmpty : cn.lookup ref.slot = none) : ¬ st.cdt.mentions ref :=
  h.not_mentions_of_empty fun o hO => by rw [hCn] at hO; cases hO; exact hEmpty

/-- The tree's slots hold capabilities except, possibly, the slots `gone` names:
the state a destroyer leaves between emptying slots and taking them out of the
tree. -/
def cdtCompletenessOff (st : SystemState) (gone : SlotRef → Prop) : Prop :=
  ∀ ref : SlotRef, st.cdt.mentions ref → ¬ gone ref →
    ∃ o, st.objects[ref.cnode]? = some o ∧ o.slotCap ref.slot ≠ none

theorem cdtCompleteness.off {st : SystemState} (h : cdtCompleteness st)
    (gone : SlotRef → Prop) : cdtCompletenessOff st gone :=
  fun ref hM _ => h ref hM

/-- Once the slots `gone` names have left the tree, it is complete again. -/
theorem cdtCompletenessOff.complete {st : SystemState} {gone : SlotRef → Prop}
    (h : cdtCompletenessOff st gone) (hGone : ∀ ref, gone ref → ¬ st.cdt.mentions ref) :
    cdtCompleteness st :=
  fun ref hM => h ref hM fun hG => hGone ref hG hM

/-- A tree update that names no new slot keeps the relaxed completeness. -/
theorem cdtCompletenessOff.of_cdt {st : SystemState} {gone : SlotRef → Prop}
    (h : cdtCompletenessOff st gone) (cdt' : CapDerivationTree)
    (hSub : ∀ ref, cdt'.mentions ref → st.cdt.mentions ref) :
    cdtCompletenessOff { st with cdt := cdt' } gone :=
  fun ref hM hG => h ref (hSub ref hM) hG

/-- WS-H4/M-03: CDT acyclicity — the capability derivation tree has no cycles.
Required for `descendantsOf` termination and revocation completeness. Uses the
edge-well-founded formulation for clean subset-preservation proofs. -/
def cdtAcyclicity (st : SystemState) : Prop :=
  st.cdt.edgeWellFounded

/-- **One capability's CNode geometry is seL4's**: its guard fits its guard
size, and, where it names a CNode, its guard size and that CNode's radix use at
most a word's 64 bits — the bound `updateCapData` (`objecttype.c:395`) refuses a
Mint past, and the one `resolveAddressBits` (`cspace.c:126`) consumes a level
by. -/
def cnodeCapGeometryAt (st : SystemState) (cap : Capability) : Prop :=
  cap.cnodeGuard < 2 ^ cap.cnodeGuardSize ∧
  ∀ (id : SeLe4n.ObjId) (cn : CNode), cap.target = .object id →
    st.getCNode? id = some cn → cap.cnodeGuardSize + cn.radixWidth ≤ 64

/-- **Every slot's capability has seL4's CNode geometry** (`cnodeCapGeometryAt`),
read through `KernelObject.slotCap` over CNode slots and thread space slots.  The
4th conjunct of `capabilityInvariantBundle`.  seL4 keeps the guard in the
capability (`cap_cnode_cap`); a CNode holds slots only. -/
def cnodeCapGeometry (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (o : KernelObject) (slot : SeLe4n.Slot) (cap : Capability),
    st.objects[oid]? = some o →
    o.slotCap slot = some cap →
    cnodeCapGeometryAt st cap

/-- **A step that keeps every CNode's radix keeps every capability's geometry.** -/
theorem cnodeCapGeometryAt_mono {st st' : SystemState}
    (hRadix : ∀ (id : SeLe4n.ObjId) (cn' : CNode), st'.getCNode? id = some cn' →
      ∃ cn, st.getCNode? id = some cn ∧ cn'.radixWidth = cn.radixWidth) :
    ∀ cap, cnodeCapGeometryAt st cap → cnodeCapGeometryAt st' cap := by
  intro cap h
  refine ⟨h.1, fun id cn' hT hC => ?_⟩
  obtain ⟨cn, hC0, hR⟩ := hRadix id cn' hC
  rw [hR]; exact h.2 id cn hT hC0

/-- A step that leaves every CNode where it was keeps every capability's geometry. -/
theorem cnodeCapGeometryAt_congr {st st' : SystemState}
    (hCNode : ∀ cn : SeLe4n.ObjId, st'.getCNode? cn = st.getCNode? cn) :
    ∀ cap, cnodeCapGeometryAt st cap → cnodeCapGeometryAt st' cap :=
  cnodeCapGeometryAt_mono fun id cn' h => ⟨cn', by rw [← hCNode]; exact h, rfl⟩

/-- A capability that names no CNode-backed object and carries no guard has
seL4's geometry in every state where its target's radix is at most 64. -/
theorem cnodeCapGeometryAt_of_noGuard {st : SystemState} {cap : Capability}
    (hG : cap.cnodeGuard = 0) (hS : cap.cnodeGuardSize = 0)
    (hR : ∀ id cn, cap.target = .object id → st.getCNode? id = some cn → cn.radixWidth ≤ 64) :
    cnodeCapGeometryAt st cap :=
  ⟨by rw [hG, hS]; decide, fun id cn hT hC => by rw [hS, Nat.zero_add]; exact hR id cn hT hC⟩

/-- Geometry reads only the guard words and the target. -/
theorem cnodeCapGeometryAt_of_fields {st : SystemState} {cap cap' : Capability}
    (h : cnodeCapGeometryAt st cap) (hT : cap'.target = cap.target)
    (hG : cap'.cnodeGuard = cap.cnodeGuard) (hS : cap'.cnodeGuardSize = cap.cnodeGuardSize) :
    cnodeCapGeometryAt st cap' := by
  refine ⟨hG ▸ hS ▸ h.1, fun id cn hT' hC => ?_⟩
  rw [hS]; exact h.2 id cn (hT ▸ hT') hC

/-- **The kind a capability target claims of the object it names is the kind in
the store**: a reply capability's reply is a Reply (`getReply?`), and a CNode-slot
capability's CNode is a CNode (`getCNode?`).  Every other target claims no kind:
an `.object` capability is typed by the object it names, whatever it is, and its
presence is the tree shape's `live` (`capabilityInvariantBundle_objectCapsBacked`);
the audit trail, scheduling control and interrupt control name no object; an
interrupt handler names its line's node, whose presence and issued line are
`live`'s too. -/
def capTargetKindBackedAt (st : SystemState) : CapTarget → Prop
  | .replyCap rid => st.getReply? rid ≠ none
  | .cnodeSlotWord word => st.getCNode? (SeLe4n.Model.CapTarget.wordCnode word) ≠ none
  | _ => True

/-- **Every capability slot's capability names an object of the kind its target
claims** — a CNode's slot and a thread's space slot, read through
`KernelObject.slotCap`.  The 6th conjunct of `capabilityInvariantBundle`.

WS-SM SM6.D / PR #822 Phase H (#1) stated its reply half alone
(`replyCapPointsToValidReply`, now derived: `capTargetKindBacked.reply`): the
model admitted a `.replyCap rid` at an absent or non-Reply object, which the live
`.reply` path then rejects.  The CNode-slot half rules out a `.cnodeSlot` capability
whose CNode is gone or is another kind of object; the boot admits one only over a
CNode it installs (`bootCapTargetKindCheck`). -/
def capTargetKindBacked (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (o : KernelObject) (slot : SeLe4n.Slot) (cap : Capability),
    st.objects[oid]? = some o →
    o.slotCap slot = some cap →
    capTargetKindBackedAt st cap.target

/-- **A step that removes no Reply and no CNode keeps every target's kind
backed.** -/
theorem capTargetKindBackedAt_mono {st st' : SystemState}
    (hReply : ∀ rid : SeLe4n.ReplyId, st.getReply? rid ≠ none → st'.getReply? rid ≠ none)
    (hCNode : ∀ cn : SeLe4n.ObjId, st.getCNode? cn ≠ none → st'.getCNode? cn ≠ none) :
    ∀ t, capTargetKindBackedAt st t → capTargetKindBackedAt st' t := by
  intro t h
  cases t with
  | replyCap rid => exact hReply rid h
  | cnodeSlotWord w => exact hCNode (CapTarget.wordCnode w) h
  | _ => trivial

/-- A step that leaves every Reply and CNode where it was keeps every target's
kind backed. -/
theorem capTargetKindBackedAt_congr {st st' : SystemState}
    (hReply : ∀ rid : SeLe4n.ReplyId, st'.getReply? rid = st.getReply? rid)
    (hCNode : ∀ cn : SeLe4n.ObjId, st'.getCNode? cn = st.getCNode? cn) :
    ∀ t, capTargetKindBackedAt st t → capTargetKindBackedAt st' t :=
  capTargetKindBackedAt_mono (fun rid h => by rw [hReply]; exact h)
    (fun cn h => by rw [hCNode]; exact h)

/-- **A CNode stored over a CNode keeps every target's kind backed**: no Reply
is touched and the key stays a CNode. -/
theorem capTargetKindBackedAt_storeObject_cnode {st st' : SystemState} {k : SeLe4n.ObjId}
    {cn cn' : CNode} (hObjInv : st.objects.invExt) (hPre : st.objects[k]? = some (.cnode cn))
    (hStore : storeObject k (.cnode cn') st = .ok ((), st')) :
    ∀ t, capTargetKindBackedAt st t → capTargetKindBackedAt st' t := by
  have hSelf := storeObject_objects_eq st st' k _ hObjInv hStore
  have hNe : ∀ oid, oid ≠ k → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st' k oid _ h hObjInv hStore
  refine capTargetKindBackedAt_mono (fun rid hR => ?_) (fun c hC => ?_)
  · simp only [SystemState.getReply?] at hR ⊢
    by_cases hc : rid.toObjId = k
    · rw [hc, hPre] at hR; exact absurd rfl hR
    · rw [hNe rid.toObjId hc]; exact hR
  · simp only [SystemState.getCNode?] at hC ⊢
    by_cases hc : c = k
    · rw [hc, hSelf]; simp
    · rw [hNe c hc]; exact hC

/-- **No dangling reply caps**: every `.replyCap rid` held in a capability slot is
backed by an existing Reply object.  Mirrors the runtime reply arm of
`Testing/InvariantChecks.lean`.  The reply half of `capTargetKindBacked`
(`capTargetKindBacked.reply`), kept as its own statement for the consumers that
read a reply cap's Reply. -/
def replyCapPointsToValidReply (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (o : KernelObject) (slot : SeLe4n.Slot)
    (cap : Capability) (rid : SeLe4n.ReplyId),
    st.objects[oid]? = some o →
    o.slotCap slot = some cap →
    cap.target = .replyCap rid →
    st.getReply? rid ≠ none

/-- The reply half of the kind backing. -/
theorem capTargetKindBacked.reply {st : SystemState} (h : capTargetKindBacked st) :
    replyCapPointsToValidReply st := fun oid o slot cap rid hO hL hT => by
  have hK := h oid o slot cap hO hL
  rw [hT] at hK
  exact hK

/-- **A `.cnodeSlot` capability names a CNode**: the CNode-slot half. -/
theorem capTargetKindBacked.cnodeSlot {st : SystemState} (h : capTargetKindBacked st)
    {oid : SeLe4n.ObjId} {o : KernelObject} {slot : SeLe4n.Slot} {cap : Capability}
    {cn : SeLe4n.ObjId} {s : SeLe4n.Slot} (hO : st.objects[oid]? = some o)
    (hL : o.slotCap slot = some cap) (hT : cap.target = .cnodeSlot cn s) :
    st.getCNode? cn ≠ none := by
  have hK := h oid o slot cap hO hL
  rw [hT] at hK
  have hW : capTargetKindBackedAt st (.cnodeSlotWord (SeLe4n.pairWords cn.val s.val)) := hK
  simpa only [capTargetKindBackedAt, CapTarget.wordCnode_pair] using hW

/-- The slot-reader form: the capability a slot holds names an object of the
kind its target claims. -/
theorem capTargetKindBacked.slotCapAt {st : SystemState} (h : capTargetKindBacked st)
    {r : SlotRef} {cap : Capability} (hC : st.slotCapAt r = some cap) :
    capTargetKindBackedAt st cap.target := by
  unfold SystemState.slotCapAt SystemState.getObject? at hC
  cases hO : st.objects[r.cnode]? with
  | none => rw [hO] at hC; cases hC
  | some o => rw [hO] at hC; exact h r.cnode o r.slot cap hO hC

/-- The slot-reader form of `cnodeCapGeometry`. -/
theorem cnodeCapGeometry.slotCapAt {st : SystemState} (h : cnodeCapGeometry st)
    {r : SlotRef} {cap : Capability} (hC : st.slotCapAt r = some cap) :
    cnodeCapGeometryAt st cap := by
  unfold SystemState.slotCapAt SystemState.getObject? at hC
  cases hO : st.objects[r.cnode]? with
  | none => rw [hO] at hC; cases hC
  | some o => rw [hO] at hC; exact h r.cnode o r.slot cap hO hC

/-- The CNode reading of the reply-cap clause. -/
theorem replyCapPointsToValidReply.cnode {st : SystemState} (h : replyCapPointsToValidReply st)
    {oid : SeLe4n.ObjId} {cn : CNode} {slot : SeLe4n.Slot} {cap : Capability}
    {rid : SeLe4n.ReplyId} (hO : st.objects[oid]? = some (.cnode cn))
    (hL : cn.lookup slot = some cap) (hT : cap.target = .replyCap rid) : st.getReply? rid ≠ none :=
  h oid _ slot cap rid hO hL hT

/-- **A step whose every object was there before with the same slots, and that
removes no Reply and no CNode, keeps every target's kind backed.** -/
theorem capTargetKindBacked_of_slotCap_back {st st' : SystemState}
    (h : capTargetKindBacked st)
    (hBack : ∀ (oid : SeLe4n.ObjId) (o' : KernelObject), st'.objects[oid]? = some o' →
      ∃ o, st.objects[oid]? = some o ∧ o'.slotCap = o.slotCap)
    (hKind : ∀ t, capTargetKindBackedAt st t → capTargetKindBackedAt st' t) :
    capTargetKindBacked st' := fun oid o' slot cap hO hL => by
  obtain ⟨o, ho, he⟩ := hBack oid o' hO
  exact hKind _ (h oid o slot cap ho (he ▸ hL))

/-- `capTargetKindBacked` reads only the object store, so any transition leaving
`st.objects` unchanged frames it. -/
theorem capTargetKindBacked_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (h : capTargetKindBacked st) :
    capTargetKindBacked st' :=
  capTargetKindBacked_of_slotCap_back h (fun oid o' hO => ⟨o', hObjs ▸ hO, rfl⟩)
    (capTargetKindBackedAt_congr (SystemState.getReply?_frame hObjs)
      (fun cn => by unfold SystemState.getCNode?; rw [hObjs]))

/-- WS-ZA ZA4.5: a step writing only run-queue links keeps every target's kind
backed — CNodes and Reply objects are not TCBs. -/
theorem capTargetKindBacked_of_objectsAgreeOffRunLinks {st st' : SystemState}
    (hA : st'.objectsAgreeOffRunLinks st) (h : capTargetKindBacked st) :
    capTargetKindBacked st' :=
  capTargetKindBacked_of_slotCap_back h
    (fun _ _ hO => let ⟨o, ho, hc, _⟩ := hA.slots_back hO; ⟨o, ho, hc⟩)
    (capTargetKindBackedAt_congr hA.getReply? hA.getCNode?)

/-- **Geometry transported along the slot reading**: every post-state object reads
the slots of a pre-state object at its key, and every capability's geometry
survives the step. -/
theorem cnodeCapGeometry_of_slotCap_back {st st' : SystemState}
    (h : cnodeCapGeometry st)
    (hBack : ∀ (oid : SeLe4n.ObjId) (o' : KernelObject), st'.objects[oid]? = some o' →
      ∃ o, st.objects[oid]? = some o ∧ o'.slotCap = o.slotCap)
    (hGeo : ∀ cap, cnodeCapGeometryAt st cap → cnodeCapGeometryAt st' cap) :
    cnodeCapGeometry st' := fun oid o' slot cap hO hL => by
  obtain ⟨o, ho, he⟩ := hBack oid o' hO
  exact hGeo _ (h oid o slot cap ho (he ▸ hL))

/-- `cnodeCapGeometry` reads only the object store. -/
theorem cnodeCapGeometry_of_objects_eq
    (st st' : SystemState) (h : cnodeCapGeometry st) (hObjs : st'.objects = st.objects) :
    cnodeCapGeometry st' :=
  cnodeCapGeometry_of_slotCap_back h (fun oid o' hO => ⟨o', hObjs ▸ hO, rfl⟩)
    (cnodeCapGeometryAt_congr (fun cn => by unfold SystemState.getCNode?; rw [hObjs]))

/-- **A CNode stored over a CNode of the same radix keeps every capability's
geometry**: no other CNode is touched. -/
theorem cnodeCapGeometryAt_storeObject_cnode {st st' : SystemState} {k : SeLe4n.ObjId}
    {cn cn' : CNode} (hObjInv : st.objects.invExt) (hPre : st.objects[k]? = some (.cnode cn))
    (hStore : storeObject k (.cnode cn') st = .ok ((), st'))
    (hRw : cn'.radixWidth = cn.radixWidth) :
    ∀ cap, cnodeCapGeometryAt st cap → cnodeCapGeometryAt st' cap := by
  have hSelf := storeObject_objects_eq st st' k _ hObjInv hStore
  have hNe : ∀ oid, oid ≠ k → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st' k oid _ h hObjInv hStore
  refine cnodeCapGeometryAt_mono fun id c' hC => ?_
  simp only [SystemState.getCNode?] at hC ⊢
  by_cases hc : id = k
  · subst hc; rw [hSelf] at hC; simp at hC; subst hC; exact ⟨cn, by rw [hPre], hRw⟩
  · rw [hNe id hc] at hC; exact ⟨c', hC, rfl⟩

/-- **Geometry through a CNode store**: the stored CNode keeps its radix and every
capability it holds is one the pre-state CNode held, or one with seL4's geometry in
the post-state (`hNew`). -/
theorem cnodeCapGeometry_of_storeObject_cnode
    (st st' : SystemState) (k : SeLe4n.ObjId) (cn cn' : CNode)
    (h : cnodeCapGeometry st) (hObjInv : st.objects.invExt)
    (hPre : st.objects[k]? = some (.cnode cn))
    (hStore : storeObject k (.cnode cn') st = .ok ((), st'))
    (hRw : cn'.radixWidth = cn.radixWidth)
    (hNew : ∀ slot cap, cn'.lookup slot = some cap →
      cn.lookup slot = some cap ∨ cnodeCapGeometryAt st' cap) :
    cnodeCapGeometry st' := by
  have hGeo := cnodeCapGeometryAt_storeObject_cnode hObjInv hPre hStore hRw
  intro oid o slot cap hO hL
  by_cases hc : oid = k
  · subst hc
    rw [storeObject_objects_eq st st' oid _ hObjInv hStore] at hO; cases hO
    rcases hNew slot cap hL with hOld | hG
    · exact hGeo _ (h oid (.cnode cn) slot cap hPre hOld)
    · exact hG
  · rw [storeObject_objects_ne st st' k oid _ hc hObjInv hStore] at hO
    exact hGeo _ (h oid o slot cap hO hL)

/-- **Geometry through a store that adds no capability**: the stored object holds
only capabilities the object it replaces held, and is a CNode only over a CNode of
the same radix. -/
theorem cnodeCapGeometry_of_storeObject_slotsBack
    (st st' : SystemState) (k : SeLe4n.ObjId) (o o' : KernelObject)
    (h : cnodeCapGeometry st) (hObjInv : st.objects.invExt)
    (hPre : st.objects[k]? = some o)
    (hStore : storeObject k o' st = .ok ((), st'))
    (hBack : ∀ s c, o'.slotCap s = some c → o.slotCap s = some c)
    (hRadix : ∀ cn', o' = .cnode cn' → ∃ cn, o = .cnode cn ∧ cn'.radixWidth = cn.radixWidth) :
    cnodeCapGeometry st' := by
  have hSelf := storeObject_objects_eq st st' k _ hObjInv hStore
  have hNe : ∀ oid, oid ≠ k → st'.objects[oid]? = st.objects[oid]? :=
    fun oid hn => storeObject_objects_ne st st' k oid _ hn hObjInv hStore
  have hGeo : ∀ cap, cnodeCapGeometryAt st cap → cnodeCapGeometryAt st' cap := by
    refine cnodeCapGeometryAt_mono fun id cn' hC => ?_
    rw [SystemState.getCNode?_eq_some_iff] at hC
    by_cases e : id = k
    · subst e; rw [hSelf] at hC
      obtain ⟨cn, rfl, hR⟩ := hRadix cn' (Option.some.inj hC)
      exact ⟨cn, (SystemState.getCNode?_eq_some_iff _ _ _).mpr hPre, hR⟩
    · rw [hNe id e] at hC; exact ⟨cn', (SystemState.getCNode?_eq_some_iff _ _ _).mpr hC, rfl⟩
  intro oid o2 slot cap hO hL
  by_cases e : oid = k
  · subst e; rw [hSelf] at hO; cases hO
    exact hGeo _ (h oid o slot cap hPre (hBack slot cap hL))
  · rw [hNe oid e] at hO; exact hGeo _ (h oid o2 slot cap hO hL)

/-- **Geometry through a CNode insert**: the inserted capability has seL4's
geometry in the pre-state, and the CNode keeps its radix. -/
theorem cnodeCapGeometry_of_storeObject_insertCNode
    (st st' : SystemState) (k : SeLe4n.ObjId) (cn : CNode)
    (slot : SeLe4n.Slot) (cap : Capability)
    (h : cnodeCapGeometry st) (hObjInv : st.objects.invExt)
    (hPre : st.objects[k]? = some (.cnode cn))
    (hStore : storeObject k (.cnode (cn.insert slot cap)) st = .ok ((), st'))
    (hCap : cnodeCapGeometryAt st cap) :
    cnodeCapGeometry st' := by
  have hRw : (cn.insert slot cap).radixWidth = cn.radixWidth := CNode.insert_radixWidth ..
  refine cnodeCapGeometry_of_storeObject_cnode st st' k cn _ h hObjInv hPre hStore hRw
    (fun s c hL => ?_)
  by_cases hs : s = slot
  · subst hs
    rw [CNode.lookup_insert_eq cn s cap (CNode.slotsUnique_holds cn)
      (CNode.slotAddressable_of_lookup_insert _ _ _ _ _ hL)] at hL
    cases hL
    exact .inr (cnodeCapGeometryAt_storeObject_cnode hObjInv hPre hStore hRw _ hCap)
  · rw [CNode.lookup_insert_ne cn slot s cap (Ne.symm hs) (CNode.slotsUnique_holds cn)] at hL
    exact .inl hL

/-- Composed capability invariant bundle entrypoint.

The active lifecycle slice extends the M2 foundation bundle with security-meaningful
state predicates. Only genuine state invariants are included — predicates that assert
properties of the system state and must be preserved through every transition.

WS-H4: Extended with meaningful security predicates:
- `cdtCompleteness`: CDT slot reachability (every slot the tree names lies in an existing object)
- `cdtAcyclicity`: CDT cycle-freedom for sound revocation

WS-SX SX2.1: CNode geometry lives in the capability, as in seL4:
- `cnodeCapGeometry`: every slot's capability has guard < 2^guardSize and, where
  it names a CNode, guardSize + radix ≤ 64

WS-F6/D1: Reduced from 8-tuple to 6-tuple. Removed `cspaceAttenuationRule` (operation
property of `mintDerivedCap`, not a state invariant — no `st` parameter) and
`lifecycleAuthorityMonotonicity` (operation-correctness lemma about delete/revoke
effects, not a state property preserved through transitions). Both are retained as
standalone operation-correctness lemmas in `Authority.lean`.

**Design decisions (WS-H4):**
- CDT-expanding operations (`cspaceCopy`, `cspaceMove`, `cspaceMintWithCdt`,
  reply-cap mint, IPC capability transfer) prove acyclicity from the pre-state:
  each installs into a slot it found empty, which `cdtCompleteness` keeps out of
  the tree, so the new edge reaches a fresh node
  (`addEdge_preserves_edgeWellFounded_fresh`, `moveNode_edgeWellFounded`).
- CDT-shrinking operations (revoke/delete) prove acyclicity via
  `CapDerivationTree.edgeWellFounded_sub` (edge subset preserves well-foundedness).
- AF5-F (AF-26): This conjunction uses right-associative `∧` chains
  accessed via `.2.2.2...` projections. Refactoring to a named structure is
  recorded as a post-1.0 hardening candidate; registered in
  `docs/REGISTERED_DEBT.md` (Registered debt index, C.1); see the
  Builder.lean AF5-F annotation for the rationale.

WS-RC R4.A.6: The historical `cspaceSlotUnique` conjunct was removed when
`CNode.slots : SeLe4n.UniqueSlotMap Capability` carried the slot-uniqueness
witness structurally at construction time (via `UniqueSlotMap.hWF`).  The
bundle now has **7** conjuncts: the R4.A.6 close-out retired `cspaceSlotUnique`
(7 → 6), PR #822 Phase H #1.a added `replyCapPointsToValidReply` (the 7th,
6 → 7) so the step-preserved bundle rules out dangling `.replyCap` slots (since
generalised to `capTargetKindBacked`, which also rules out a `.cnodeSlot` capability
naming anything but a CNode), and
WS-ZA ZA5.3 part 4 added `cdtLinksAgree` (the 8th): the derivation links the
slots hold agree with the tree, so the executable children and descendant reads
that walk them read the tree.  WS-ZA ZA5.3 part 5 retired the slot-count
conjunct (8 → 7): a CNode's slots are a fixed array since part 1, so every CNode
is within its slot count by construction (`CNode.slotCountBounded_holds`).
Per-CNode slot uniqueness is discharged directly via
`SeLe4n.Model.CNode.slotsUnique_holds`.  WS-ZA ZA5.4 part 16 added the tree's
shape over the slots (the 8th, `CapTreeShape`): every slot holding a capability
is in the tree, as every capability is in seL4's mapping database, and the tree
has a preorder.  WS-ZA ZA5.4 part 19 added the untyped facts to that shape
(seL4's `untyped_mdb` and `untyped_inc`): the capabilities to one untyped form
one vertical first-child chain, one that is not full has no strict descendant
to its untyped, the capabilities to memory carved from an untyped lie below
every capability to it, and every child an untyped records is live and recorded
by it alone. -/
def capabilityInvariantBundle (st : SystemState) : Prop :=
  cspaceLookupSound st ∧
    cdtCompleteness st ∧ cdtAcyclicity st ∧
    cnodeCapGeometry st ∧ st.objects.invExt ∧ capTargetKindBacked st ∧
    cdtLinksAgree st ∧ SystemState.CapTreeShape st

/-! ## AN4-F.5 (CAP-M05) — Named-projection refactor of `capabilityInvariantBundle`

Mirror of the AN3-B playbook for IPC's `ipcInvariantFull`. The 8-conjunct
right-associative `∧` chain above (6 after the WS-RC R4.A.6 close-out retired
`cspaceSlotUnique`, 7 once PR #822 Phase H #1.a added
`replyCapPointsToValidReply`, 8 with `cdtLinksAgree`) is fragile to reason about —
consumers write `.2.2.1` to reach `cdtCompleteness`, `.2.2.2.1` for
`cdtAcyclicity`, and so on. The audit's CAP-M05 finding calls for a named
structure that exposes each field by name.

At v0.30.6 the tuple form remains the primary definition so the existing
consumer sites do not have to migrate in a single commit. The named
structure below is **derived** from the tuple via a bidirectional bridge
(`capabilityInvariantBundle_iff_CapabilityInvariantBundle`), and each field
has a `@[simp]` projection abbrev so consumers can migrate incrementally —
`bundle.cdtCompleteness` replaces `bundle.2.2.1`, and `simp` unfolds the
abbrev to the underlying tuple projection automatically.

A follow-up workstream (AN4-F.5.3..F.5.6, tracked for a subsequent commit
that touches the 30+ primary sites simultaneously) will swap the primary
def to the structure and delete the tuple form. Both forms are legal in
the interim. -/

/-- **The capability bundle less the slot-link agreement**: what a step leaves
between writing the tree and writing the slot links that encode it.  A run of
link writes (`SystemState.linkReach`) restores the full bundle once its links
agree with the tree (`capabilityInvariantBundle_of_linkReach`). -/
def capabilityBundleOffLinks (st : SystemState) : Prop :=
  cspaceLookupSound st ∧
    cdtCompleteness st ∧ cdtAcyclicity st ∧
    cnodeCapGeometry st ∧ st.objects.invExt ∧ capTargetKindBacked st

theorem capabilityInvariantBundle.offLinks {st : SystemState} (h : capabilityInvariantBundle st) :
    capabilityBundleOffLinks st :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem capabilityBundleOffLinks.withLinks {st : SystemState} (h : capabilityBundleOffLinks st)
    (hL : cdtLinksAgree st) (hShape : SystemState.CapTreeShape st) : capabilityInvariantBundle st :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, hL, hShape⟩

/-- **The capability bundle without the tree's coverage of the slots**: what an
insert leaves before it records the new slot's derivation (WS-ZA ZA5.4 part
16).  Every conjunct but the tree's shape holds, and the tree keeps its
preorder; the new slot holds a capability the tree does not yet name, until the
insert's derivation edge (`CapDerivationTree.addEdge`) names it. -/
def capabilityBundleOffCoverage (st : SystemState) : Prop :=
  capabilityBundleOffLinks st ∧ cdtLinksAgree st ∧ ∃ P, st.cdt.TreeOrder P

theorem capabilityInvariantBundle.offCoverage {st : SystemState}
    (h : capabilityInvariantBundle st) : capabilityBundleOffCoverage st :=
  ⟨h.offLinks, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.ordered⟩

/-- **The capability bundle off (b) at one source** (WS-ZA ZA5.4 part 19): what a
copy, mint or transfer of an untyped capability leaves between recording its
derivation and setting its source full (`untypedSourceSetFull`).  Every
conjunct holds, and the tree's shape holds but for (b) at `src`: the source,
not yet full, has the new copy below it (`SystemState.CapTreeShapeOff`). -/
def capabilityBundleOffSource (st : SystemState) (src : SlotRef) : Prop :=
  capabilityBundleOffLinks st ∧ cdtLinksAgree st ∧ SystemState.CapTreeShapeOff st src

/-- AN4-F.5 (CAP-M05): Named-projection view of `capabilityInvariantBundle`.
Each field records a distinct slot-level invariant (uniqueness,
soundness, size-bounded) or a CDT structural invariant (completeness,
acyclicity, depth) plus the underlying `RHTable` kernel-level invariant
on the object store. The structure is logically equivalent to the
right-associative tuple form via the bridge below. -/
structure CapabilityInvariantBundle (st : SystemState) : Prop where
  /-- `cspaceLookupSlot` agrees with the direct-object-store projection
      on every present CNode/slot pair. -/
  lookupSound : cspaceLookupSound st
  /-- Every slot the derivation tree names holds a capability. -/
  cdtCompleteness : cdtCompleteness st
  /-- The capability derivation graph is acyclic. -/
  cdtAcyclicity : cdtAcyclicity st
  /-- Every slot's capability has seL4's CNode geometry. -/
  capGeometry : cnodeCapGeometry st
  /-- The kernel-level `objects` `RHTable` invariant holds (external hash,
      capacity positive, no duplicate keys). -/
  objectsInvExt : st.objects.invExt
  /-- Every capability names an object of the kind its target claims: a reply
      capability a Reply, a CNode-slot capability a CNode. -/
  targetKindBacked : capTargetKindBacked st
  /-- WS-ZA ZA5.3: the slot links encode the derivation tree. -/
  linksAgree : cdtLinksAgree st
  /-- WS-ZA ZA5.4 part 16: every slot holding a capability is in the tree, and
      the tree has a preorder (seL4's mapping database); part 19: the untyped
      chains and descendants (seL4's `untyped_mdb` and `untyped_inc`). -/
  treeShape : SystemState.CapTreeShape st

/-- AN4-F.5.1 (CAP-M05): Bidirectional bridge between the tuple and named
forms. Consumers can move freely between the two representations; the
primary def continues to be the tuple form so existing destructures
compile unchanged. -/
theorem capabilityInvariantBundle_iff_CapabilityInvariantBundle
    (st : SystemState) :
    capabilityInvariantBundle st ↔ CapabilityInvariantBundle st := by
  constructor
  · rintro ⟨hS, hComp, hAcyc, hDep, hObj, hRCPV, hLinks, hShape⟩
    exact { lookupSound := hS
          , cdtCompleteness := hComp, cdtAcyclicity := hAcyc
          , capGeometry := hDep, objectsInvExt := hObj
          , targetKindBacked := hRCPV, linksAgree := hLinks, treeShape := hShape }
  · intro h
    exact ⟨h.lookupSound,
           h.cdtCompleteness, h.cdtAcyclicity, h.capGeometry,
           h.objectsInvExt, h.targetKindBacked, h.linksAgree, h.treeShape⟩

/-! ### AN4-F.5.2 (CAP-M05): `@[simp]` projection abbreviations

Shorthand accessors so consumers of the tuple form can use named fields
without going through the bidirectional bridge. Tagged `@[simp]` so the
definitional unfolding happens automatically during `simp`-closed goals. -/

namespace capabilityInvariantBundle

/-- Extract `cdtCompleteness` from the tuple form. -/
@[simp] abbrev cdtCompleteness {st : SystemState} (h : capabilityInvariantBundle st) :
    _root_.SeLe4n.Kernel.cdtCompleteness st := h.2.1

/-- Extract `cdtAcyclicity` from the tuple form. -/
@[simp] abbrev cdtAcyclicity {st : SystemState} (h : capabilityInvariantBundle st) :
    _root_.SeLe4n.Kernel.cdtAcyclicity st := h.2.2.1

/-- Extract `st.objects.invExt` from the tuple form. -/
@[simp] abbrev objectsInvExt {st : SystemState} (h : capabilityInvariantBundle st) :
    st.objects.invExt := h.2.2.2.2.1

/-- WS-ZA ZA5.3: extract `cdtLinksAgree` from the tuple form (the 7th conjunct). -/
@[simp] abbrev linksAgree {st : SystemState} (h : capabilityInvariantBundle st) :
    _root_.SeLe4n.Kernel.cdtLinksAgree st := h.2.2.2.2.2.2.1

/-- WS-ZA ZA5.4 part 16: extract the tree's shape (the 8th conjunct). -/
@[simp] abbrev treeShape {st : SystemState} (h : capabilityInvariantBundle st) :
    SystemState.CapTreeShape st := h.2.2.2.2.2.2.2

/-- Extract the capabilities' CNode geometry (the 4th conjunct). -/
@[simp] abbrev capGeometry {st : SystemState} (h : capabilityInvariantBundle st) :
    cnodeCapGeometry st := h.2.2.2.1

/-- Extract the target-kind backing (the 6th conjunct). -/
@[simp] abbrev targetKindBacked {st : SystemState} (h : capabilityInvariantBundle st) :
    capTargetKindBacked st := h.2.2.2.2.2.1

/-- **Every object a capability names is in the store** (seL4's `valid_cap`: no
capability outlives its object), its line issued when it is an interrupt node:
the tree shape's `live`, for every target that names an object
(`Capability.namedObject`). -/
theorem namedObjectPresent {st : SystemState} (h : capabilityInvariantBundle st)
    {r : SlotRef} {o : SeLe4n.ObjId} (hN : SystemState.namesAt st.slotCapAt r o) :
    st.objectPresent o :=
  h.treeShape.live r o hN

end capabilityInvariantBundle

/-- **No `.object` capability dangles**: every `.object x` capability held in a
capability slot — a CNode's slot or a thread's space slot, read through
`KernelObject.slotCap` — names an `x` present in the object store. -/
def objectCapsBacked (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (o : KernelObject) (slot : SeLe4n.Slot) (cap : Capability)
    (x : SeLe4n.ObjId),
    st.objects[oid]? = some o →
    o.slotCap slot = some cap →
    cap.target = .object x →
    st.objects[x]? ≠ none

/-- **The capability bundle backs every `.object` capability** — the answer to
"can a decoder reach an absent object through a capability it resolved": no.  It
is the tree shape's `live` (`capabilityInvariantBundle.namedObjectPresent`),
preserved by every transition that preserves the bundle; an object leaves the
store only through the final-delete retire, once no slot names it
(`capIsFinal_iff_capFinalSpec`, `TreeShapeOver.retire`). -/
theorem capabilityInvariantBundle_objectCapsBacked {st : SystemState}
    (h : capabilityInvariantBundle st) : objectCapsBacked st := by
  intro oid o slot cap x hO hL hT
  have hN : SystemState.namesAt st.slotCapAt ⟨oid, slot⟩ x :=
    ⟨cap, by rw [SystemState.slotCapAt_of_object (r := ⟨oid, slot⟩) hO]; exact hL,
      by unfold Capability.namedObject; rw [hT]⟩
  exact (h.namedObjectPresent hN).1

/-- The slot-reader form: a slot holding an `.object x` capability names a
present `x`. -/
theorem objectCapsBacked.slotCapAt {st : SystemState} (h : objectCapsBacked st)
    {r : SlotRef} {cap : Capability} {x : SeLe4n.ObjId}
    (hC : st.slotCapAt r = some cap) (hT : cap.target = .object x) : st.objects[x]? ≠ none := by
  unfold SystemState.slotCapAt SystemState.getObject? at hC
  cases hO : st.objects[r.cnode]? with
  | none => rw [hO] at hC; cases hC
  | some o => rw [hO] at hC; exact h r.cnode o r.slot cap x hO hC hT

/-- The CNode-lookup form (`SystemState.lookupSlotCap`, what a decoder resolves
through). -/
theorem objectCapsBacked.lookupSlotCap {st : SystemState} (h : objectCapsBacked st)
    {r : SlotRef} {cap : Capability} {x : SeLe4n.ObjId}
    (hC : SystemState.lookupSlotCap st r = some cap) (hT : cap.target = .object x) :
    st.objects[x]? ≠ none := by
  rw [SystemState.lookupSlotCap] at hC
  cases hCN : SystemState.lookupCNode st r.cnode with
  | none => rw [hCN] at hC; cases hC
  | some cn =>
    rw [hCN] at hC
    exact h r.cnode (.cnode cn) r.slot cap x
      ((SystemState.lookupCNode_eq_some_iff st r.cnode cn).1 hCN) hC hT

/-- **Every slot the tree names holds a capability**, read through the slot
reader: `cdtCompleteness`. -/
theorem cdtCompleteness.slotCapAt {st : SystemState} (h : cdtCompleteness st) (r : SlotRef)
    (hr : st.cdt.mentions r) : st.slotCapAt r ≠ none := by
  obtain ⟨o, hO, hC⟩ := h r hr
  rw [SystemState.slotCapAt_of_object hO]; exact hC

/-- **Finality is read from the links** (seL4's `isFinalCapability`): under the
capability bundle, the kernel's word-only reader `SystemState.capIsFinal` holds
of a slot exactly when no other slot names the object its capability names
(`SystemState.capFinalSpec`).  The slots naming one object are one preorder run
(`sameObjectContiguous`), so a second one sits next to the slot, and the slot's
parent, first-child, `prev` and `next` links reach it
(`SystemState.capIsFinal_iff_of_shape`). -/
theorem capIsFinal_iff_capFinalSpec {st : SystemState} (h : capabilityInvariantBundle st)
    (r : SlotRef) : st.capIsFinal r.cnode r.slot = true ↔ st.capFinalSpec r :=
  SystemState.capIsFinal_iff_of_shape h.linksAgree h.treeShape h.cdtCompleteness.slotCapAt
    h.cdtAcyclicity r

/-! ## AN4-F.4 (CAP-M04) — `RetypeTarget` precondition subtype

The destroy path (`lifecyclePreRetypeCleanup` → the scrub → the write that
replaces the object) carries a caller obligation: the cleanup
hook must have run on the target id before the object is replaced.  It was
first a documented invariant of the in-place retype's wrappers, retired in
WS-ZA ZA5.4 part 14 when every object came to be carved from an untyped; the
cleanup and this subtype stay for the capability finalisation that will
destroy objects (`docs/REGISTERED_DEBT.md`).

AN4-F.4 adds a subtype `RetypeTarget` that bundles the target `ObjId`
with a `cleanupHookDischarged` witness — a `Prop` that holds iff
`lifecyclePreRetypeCleanup` has observably run (or the target is
pre-cleanup-clean by boot construction). Threading `RetypeTarget` through
cleanup-aware entry points lets the type system enforce the obligation
rather than relying on a documented invariant alone.

**WS-RC R4.B (DEEP-CAP-04) — non-bypassable construction.** The predicate
now incorporates a `ScrubToken`-backed witness; manual discharge by
reasoning about post-scrub state alone is no longer sufficient. The token
is a refinement `Prop` whose only inhabitation route is a successful
`lifecyclePreRetypeCleanup` outcome (see `ScrubToken.fromCleanup`). A
caller cannot fabricate a token by re-proving the post-state's observable
facts, because the existential demands a concrete cleanup-hook discharge
witness from a prior state. -/

/-- WS-RC R4.B (B1 close-out, private-structure backing): structurally
opaque witness that `lifecyclePreRetypeCleanup` observably executed at
state `st` for `target`.

The structure's constructor `private mk ::` is file-private, so external
code cannot directly inhabit `ScrubTokenImpl`.  The only public
introduction route for a `ScrubToken` is `ScrubToken.fromCleanup`, which
demands a concrete `lifecyclePreRetypeCleanup ... = .ok ...` equation as
its argument.

This codifies the "no-bypass" property structurally: a refactor that
fabricates a `ScrubToken` without invoking the cleanup pipeline fails to
elaborate (it cannot wrap arbitrary observations in `ScrubTokenImpl`
without producing a real cleanup witness). -/
private structure ScrubTokenImpl (st : SystemState) (target : SeLe4n.ObjId) where
  -- Constructor is `mk` with file-private visibility inherited from the
  -- `private structure` declaration.  External code cannot reference
  -- this type by name (the `private` modifier blocks it) and therefore
  -- cannot invoke the constructor via anonymous-constructor `⟨...⟩`
  -- syntax, since the anonymous constructor's resolution requires
  -- naming the structure type.  Within this file (`Defs.lean`), only
  -- `ScrubToken.fromCleanup` constructs values of this type; the
  -- inhabitation route is therefore unique.
  mk ::
  /-- The pre-cleanup state from which the recorded cleanup invocation
      began. -/
  stPre : SystemState
  /-- The kernel object stored at `target` in `stPre`. -/
  currentObj : KernelObject
  /-- The replacement kernel object that the cleanup pipeline was
      preparing to install at `target`. -/
  newObj : KernelObject
  /-- The discharge equation: `lifecyclePreRetypeCleanup` succeeded at
      `stPre` for `target` and returned the post-cleanup state `st`. -/
  hCleanup : SeLe4n.Kernel.lifecyclePreRetypeCleanup stPre target
    currentObj newObj = .ok st

/-- WS-RC R4.B (B1 close-out): refinement witness that
`lifecyclePreRetypeCleanup` has observably executed for `target` and
produced post-cleanup state `st`.

The Prop is inhabited iff some `ScrubTokenImpl st target` value exists.
Manual fabrication is structurally infeasible because `ScrubTokenImpl`'s
constructor is `private mk ::` — external code cannot wrap an arbitrary
cleanup proof; the only public inhabitation route is
`ScrubToken.fromCleanup`, which demands the canonical
`lifecyclePreRetypeCleanup ... = .ok` witness from a prior state.

This is the third conjunct of `cleanupHookDischarged`; combined with the
two earlier observable conjuncts (object-type metadata consistency and
no-stale-scheduler-references), the whole predicate cannot be discharged
without invoking the cleanup pipeline. -/
def ScrubToken (st : SystemState) (target : SeLe4n.ObjId) : Prop :=
  Nonempty (ScrubTokenImpl st target)

/-- WS-RC R4.B (B1 close-out): the canonical `ScrubToken` introduction
site. Given a successful `lifecyclePreRetypeCleanup` outcome, witness the
token at the post-cleanup state. This is the **only** public route to a
`ScrubToken`; external callers must produce a concrete cleanup invocation
rather than proving the token directly via state observations. -/
theorem ScrubToken.fromCleanup
    {stPre stClean : SystemState} {target : SeLe4n.ObjId}
    {currentObj newObj : KernelObject}
    (hCleanup : SeLe4n.Kernel.lifecyclePreRetypeCleanup
      stPre target currentObj newObj = .ok stClean) :
    SeLe4n.Kernel.ScrubToken stClean target :=
  ⟨{ stPre := stPre, currentObj := currentObj, newObj := newObj,
     hCleanup := hCleanup }⟩

/-- WS-RC R4.B.2 (B2 close-out): tokenized form of
`lifecyclePreRetypeCleanup`.  Returns the post-cleanup state paired with a
`ScrubToken` proving that the cleanup pipeline produced it.

The returned `Subtype` carries the post-state alongside its matching
token (the token's type depends on the value of the post-state, hence
the `Subtype` rather than a plain product).  Callers that need to
construct a `RetypeTarget` consume the token via `mkRetypeTarget`
(WS-RC R4.B.3); callers that only need the post-state can use the bare
`lifecyclePreRetypeCleanup` directly.

The wrapper formulation avoids the recursive-fixpoint construction
problem inherent in a direct return-type change of
`lifecyclePreRetypeCleanup` — the bare function remains the canonical
proof-side entry point, and the tokenized form is layered on top via
`ScrubToken.fromCleanup`. -/
def lifecyclePreRetypeCleanupWithToken
    (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) :
    Except KernelError
      { stClean : SystemState // SeLe4n.Kernel.ScrubToken stClean target } :=
  match h : SeLe4n.Kernel.lifecyclePreRetypeCleanup st target currentObj newObj with
  | .error e => .error e
  | .ok stClean => .ok ⟨stClean, SeLe4n.Kernel.ScrubToken.fromCleanup h⟩

/-- WS-RC R4.B.2 (B2 close-out) bridge: the `WithToken` form is
equivalent to the bare form on the state component.  Use when porting
preservation proofs from the bare form to the tokenized form. -/
theorem lifecyclePreRetypeCleanupWithToken_state_eq
    {st : SystemState} {target : SeLe4n.ObjId}
    {currentObj newObj : KernelObject}
    {stClean : SystemState}
    {token : SeLe4n.Kernel.ScrubToken stClean target}
    (hWT : lifecyclePreRetypeCleanupWithToken st target currentObj newObj
        = .ok ⟨stClean, token⟩) :
    SeLe4n.Kernel.lifecyclePreRetypeCleanup st target currentObj newObj
        = .ok stClean := by
  unfold lifecyclePreRetypeCleanupWithToken at hWT
  split at hWT
  · cases hWT
  · case _ stClean' hBare =>
    -- `hWT : .ok ⟨stClean', ScrubToken.fromCleanup hBare⟩ = .ok ⟨stClean, token⟩`
    -- Extract `stClean' = stClean` via `Except.ok.injEq` + `Subtype` projection.
    have hEq := Except.ok.inj hWT
    have hStEq : stClean' = stClean := congrArg Subtype.val hEq
    subst hStEq
    exact hBare

/-- WS-RC R4.B.2 (B2 close-out): the `.error` case of the tokenized
wrapper agrees with the bare form on the error value.  Companion to
`lifecyclePreRetypeCleanupWithToken_state_eq`. -/
theorem lifecyclePreRetypeCleanupWithToken_error_eq
    {st : SystemState} {target : SeLe4n.ObjId}
    {currentObj newObj : KernelObject} {e : KernelError}
    (hWT : lifecyclePreRetypeCleanupWithToken st target currentObj newObj
        = .error e) :
    SeLe4n.Kernel.lifecyclePreRetypeCleanup st target currentObj newObj
        = .error e := by
  unfold lifecyclePreRetypeCleanupWithToken at hWT
  split at hWT
  · case _ e' hBare =>
    cases hWT; exact hBare
  · cases hWT

/-- AN4-F.4 (CAP-M04) + WS-RC R4.B: Predicate witnessing that the cleanup
hook has been discharged for `target`. The conjunction is now four-fold:
(a) the target's lifecycle object-type metadata matches its currently
stored kernel-object variant, (b) no stale scheduler-queue reference
points at `target`, (c) (WS-RC R4.B) a `ScrubToken` witness that
`lifecyclePreRetypeCleanup` has observably executed at this state.

The token conjunct strengthens the predicate so that manual discharge by
re-deriving the observable facts (a)+(b) is no longer sufficient; a
`lifecyclePreRetypeCleanup_ok` witness must be threaded in. This closes
DEEP-CAP-04 by making the "phantom-like" criticism unfounded — fabricating
the predicate without running cleanup is structurally impossible. -/
def cleanupHookDischarged (st : SystemState) (target : SeLe4n.ObjId) : Prop :=
  (∀ obj, st.objects[target]? = some obj →
    SystemState.lookupObjectTypeMeta st target = some obj.objectType)
  ∧ (∀ tcb, st.objects[target]? = some (.tcb tcb) →
      ¬ (tcb.tid ∈ (st.scheduler.runQueueOnCore bootCoreId).toList))
  ∧ SeLe4n.Kernel.ScrubToken st target

/-- AN4-F.4 (CAP-M04): Precondition subtype for cleanup-aware retype entry
points. Bundles a target `ObjId` with a `cleanupHookDischarged` witness at
the *pre-retype* state `st`. The subtype is the boundary a destroy-path
entry point takes, so callers cannot construct a target without carrying the
discharge obligation.

**WS-RC R4.B (DEEP-CAP-04)**: the predicate now incorporates a
`ScrubToken`-backed witness; manual discharge by reasoning about
post-scrub state alone is no longer sufficient. -/
structure RetypeTarget (st : SystemState) where
  id : SeLe4n.ObjId
  cleanupHookDischarged : SeLe4n.Kernel.cleanupHookDischarged st id

/-- WS-RC R4.B.3 (B3 close-out): smart constructor for `RetypeTarget`
that takes the three `cleanupHookDischarged` conjuncts and produces a
`RetypeTarget st` whose `id = target`.

The three explicit arguments mirror the structural conjuncts of
`cleanupHookDischarged`:
1. `hTypeMeta` — lifecycle object-type metadata matches the stored variant.
2. `hNoStaleRefs` — no stale scheduler-queue references point at the target.
3. `token` — the `ScrubToken` witness produced by `ScrubToken.fromCleanup`
   on a successful `lifecyclePreRetypeCleanup` outcome.

Callers obtaining the token via `lifecyclePreRetypeCleanupWithToken` can
feed the third component directly without re-deriving the cleanup
witness; the structural opacity of `ScrubToken` ensures the token's
provenance is auditable. -/
def mkRetypeTarget (st : SystemState) (target : SeLe4n.ObjId)
    (hTypeMeta : ∀ obj, st.objects[target]? = some obj →
      SystemState.lookupObjectTypeMeta st target = some obj.objectType)
    (hNoStaleRefs : ∀ tcb, st.objects[target]? = some (.tcb tcb) →
      ¬ (tcb.tid ∈ (st.scheduler.runQueueOnCore bootCoreId).toList))
    (token : SeLe4n.Kernel.ScrubToken st target) :
    RetypeTarget st :=
  { id := target,
    cleanupHookDischarged := ⟨hTypeMeta, hNoStaleRefs, token⟩ }

/-- WS-RC R4.B.3 (B3 close-out): a `RetypeTarget` built via
`mkRetypeTarget` records the supplied `target` as its `id`. -/
@[simp] theorem mkRetypeTarget_id (st : SystemState) (target : SeLe4n.ObjId)
    (hTypeMeta : ∀ obj, st.objects[target]? = some obj →
      SystemState.lookupObjectTypeMeta st target = some obj.objectType)
    (hNoStaleRefs : ∀ tcb, st.objects[target]? = some (.tcb tcb) →
      ¬ (tcb.tid ∈ (st.scheduler.runQueueOnCore bootCoreId).toList))
    (token : SeLe4n.Kernel.ScrubToken st target) :
    (mkRetypeTarget st target hTypeMeta hNoStaleRefs token).id = target := rfl

/-- WS-RC R4.B (no-bypass witness): every constructed `RetypeTarget`
carries an opaque `ScrubToken` whose existence proves the cleanup hook
ran. This is the structural codification of the construction discipline:
a future refactor that constructs a `RetypeTarget` without running
cleanup fails to elaborate, because the third conjunct of
`cleanupHookDischarged` cannot be inhabited otherwise. -/
theorem retypeTarget_implies_scrub_token_held
    {st : SystemState} (rt : RetypeTarget st) :
    SeLe4n.Kernel.ScrubToken st rt.id :=
  rt.cleanupHookDischarged.2.2

instance {st : SystemState} : CoeHead (RetypeTarget st) SeLe4n.ObjId where
  coe tgt := tgt.id

-- ============================================================================
-- WS-H4: Extraction theorems for new bundle components
-- ============================================================================

theorem cdtCompleteness_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cdtCompleteness st := hInv.2.1

theorem cdtAcyclicity_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cdtAcyclicity st := hInv.2.2.1

theorem cnodeCapGeometry_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cnodeCapGeometry st := hInv.2.2.2.1

theorem objects_invExt_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    st.objects.invExt := hInv.2.2.2.2.1

/-- Extract the target-kind backing (the 6th conjunct). -/
theorem capTargetKindBacked_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    capTargetKindBacked st := hInv.2.2.2.2.2.1

/-- WS-SM SM6.D / PR #822 Phase H (#1): extract the reply-cap backing invariant,
the reply half of the 6th conjunct. -/
theorem replyCapPointsToValidReply_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    replyCapPointsToValidReply st := hInv.2.2.2.2.2.1.reply

/-- WS-ZA ZA5.3: extract the slot-link agreement. -/
theorem cdtLinksAgree_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cdtLinksAgree st := hInv.2.2.2.2.2.2.1

-- ============================================================================
-- WS-H4: Transfer theorems for new components through state transitions
-- ============================================================================

/-- WS-H4: Transfer cdtCompleteness when the objects and the tree are unchanged. -/
theorem cdtCompleteness_of_objects_cdt_eq
    (st st' : SystemState)
    (hComp : cdtCompleteness st)
    (hObjEq : st'.objects = st.objects)
    (hCdtEq : st'.cdt = st.cdt) :
    cdtCompleteness st' := by
  intro ref hM
  rw [hCdtEq] at hM
  rw [hObjEq]
  exact hComp ref hM

/-- WS-ZA ZA4.5: the object-reading capability predicates carry across a step
that writes only run-queue links (CNodes are not TCBs, and a key is occupied in
one store exactly when it is in the other). -/
theorem cdtCompleteness_of_objectsAgreeOffRunLinks {st st' : SystemState}
    (hA : st'.objectsAgreeOffRunLinks st) (hComp : cdtCompleteness st)
    (hCdtEq : st'.cdt = st.cdt) : cdtCompleteness st' := by
  intro ref hM
  rw [hCdtEq] at hM
  obtain ⟨o, hO, hL⟩ := hComp ref hM
  obtain ⟨o', hO', hc, _⟩ := hA.slots_fwd hO
  exact ⟨o', hO', hc ▸ hL⟩

theorem cnodeCapGeometry_of_objectsAgreeOffRunLinks {st st' : SystemState}
    (hA : st'.objectsAgreeOffRunLinks st) (hDepth : cnodeCapGeometry st) :
    cnodeCapGeometry st' :=
  cnodeCapGeometry_of_slotCap_back hDepth
    (fun _ _ hO => let ⟨o, ho, hc, _⟩ := hA.slots_back hO; ⟨o, ho, hc⟩)
    (cnodeCapGeometryAt_congr hA.getCNode?)

/-- WS-H4: Transfer cdtCompleteness through storeObject.  Every key but `oid`
keeps its object; at `oid` the stored object must hold every slot the tree names
there (`hAt`). -/
theorem cdtCompleteness_of_storeObject
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hComp : cdtCompleteness st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hAt : ∀ ref : SlotRef, st.cdt.mentions ref → ref.cnode = oid →
      obj.slotCap ref.slot ≠ none) :
    cdtCompleteness st' := by
  intro ref hM
  rw [storeObject_cdt_eq st st' oid obj hStore] at hM
  by_cases hEq : ref.cnode = oid
  · exact ⟨obj, by rw [hEq, storeObject_objects_eq st st' oid _ hObjInv hStore], hAt ref hM hEq⟩
  · rw [storeObject_objects_ne st st' oid ref.cnode obj hEq hObjInv hStore]; exact hComp ref hM

/-- A store that keeps every occupied slot of the object it replaces occupied
keeps the tree's slots. -/
theorem cdtCompleteness_of_storeObject_slots_mono
    (st st' : SystemState) (oid : SeLe4n.ObjId) (pre obj : KernelObject)
    (hComp : cdtCompleteness st)
    (hObjInv : st.objects.invExt)
    (hPre : st.objects[oid]? = some pre)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hMono : ∀ s, pre.slotCap s ≠ none → obj.slotCap s ≠ none) :
    cdtCompleteness st' :=
  cdtCompleteness_of_storeObject st st' oid obj hComp hObjInv hStore fun ref hM hEq => by
    obtain ⟨o, hO, hL⟩ := hComp ref hM
    rw [hEq, hPre] at hO; cases hO
    exact hMono _ hL

/-- A CNode store that keeps every occupied slot occupied keeps the tree's slots. -/
theorem cdtCompleteness_of_storeObject_cnode_mono
    (st st' : SystemState) (oid : SeLe4n.ObjId) (cn cn' : CNode)
    (hComp : cdtCompleteness st)
    (hObjInv : st.objects.invExt)
    (hPre : st.objects[oid]? = some (.cnode cn))
    (hStore : storeObject oid (.cnode cn') st = .ok ((), st'))
    (hMono : ∀ s, cn.lookup s ≠ none → cn'.lookup s ≠ none) :
    cdtCompleteness st' :=
  cdtCompleteness_of_storeObject_slots_mono st st' oid (.cnode cn) (.cnode cn') hComp hObjInv hPre
    hStore hMono

/-- A CNode store keeps the tree's slots when the new CNode still holds every slot
the tree names in it. -/
theorem cdtCompleteness_of_storeObject_cnode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (cn' : CNode)
    (hComp : cdtCompleteness st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.cnode cn') st = .ok ((), st'))
    (hKeep : ∀ s, st.cdt.mentions ⟨oid, s⟩ → cn'.lookup s ≠ none) :
    cdtCompleteness st' :=
  cdtCompleteness_of_storeObject st st' oid _ hComp hObjInv hStore fun ref hM hEq =>
    hKeep ref.slot (by cases ref; cases hEq; exact hM)

/-- A CNode store that empties slots keeps the tree's slots except the emptied
ones, which `gone` must name. -/
theorem cdtCompletenessOff_of_storeObject_cnode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (cn cn' : CNode) (gone : SlotRef → Prop)
    (hComp : cdtCompleteness st)
    (hObjInv : st.objects.invExt)
    (hPre : st.objects[oid]? = some (.cnode cn))
    (hStore : storeObject oid (.cnode cn') st = .ok ((), st'))
    (hGone : ∀ s, cn.lookup s ≠ none → cn'.lookup s = none → gone ⟨oid, s⟩) :
    cdtCompletenessOff st' gone := by
  rintro ⟨c, s⟩ hM hNG
  rw [storeObject_cdt_eq st st' oid _ hStore] at hM
  by_cases hEq : c = oid
  · subst hEq
    obtain ⟨o₀, hO, hL⟩ := hComp ⟨c, s⟩ hM
    simp only [hPre] at hO; cases hO
    exact ⟨.cnode cn', storeObject_objects_eq st st' c _ hObjInv hStore,
      fun hN => hNG (hGone s hL hN)⟩
  · rw [storeObject_objects_ne st st' oid c _ hEq hObjInv hStore]; exact hComp ⟨c, s⟩ hM

/-- WS-H4: Transfer cdtAcyclicity when CDT is unchanged. -/
theorem cdtAcyclicity_of_cdt_eq
    (st st' : SystemState)
    (hAcyclic : cdtAcyclicity st)
    (hCdtEq : st'.cdt = st.cdt) :
    cdtAcyclicity st' := by
  unfold cdtAcyclicity
  rw [hCdtEq]
  exact hAcyclic

/-- WS-H4: storeTcbIpcState preserves CDT fields (delegates to storeObject). -/
private theorem storeTcbIpcState_cdt_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.cdt = st.cdt := by
  unfold storeTcbIpcState modifyTcb at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb (tcb.setIpcState ipc)) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_cdt_eq st pair.2 tid.toObjId _ hStore

-- **WS-RR RR8.16 (`v0.35.200`)**: the private `storeTcbIpcStateAndMessage_cdt_eq`
-- is **deleted**.  It answered "does the delivery store write a CDT table" here,
-- in a capability-invariant module, while the same question is now answered
-- beside the primitive (`IPC/Operations/Endpoint.lean`), where the `.call` and
-- `.reply` chains' bundle lifts read it.  Two answers to one question is what
-- this project retires; the survivor is the one at the transition.

/-- WS-H13: CNode.remove preserves radixWidth and has slot subset. -/
private theorem CNode.remove_radixWidth_eq (cn : CNode) (slot : SeLe4n.Slot) :
    (cn.remove slot).radixWidth = cn.radixWidth := rfl

private theorem CNode.remove_slots_sub (cn : CNode) (slot : SeLe4n.Slot)
    (hUniq : cn.slotsUnique) :
    ∀ (s : SeLe4n.Slot) (cap : Capability),
      (cn.remove slot).slots.get? s = some cap → cn.slots.get? s = some cap := by
  intro s cap hLookup
  simp only [CNode.slots_remove, SeLe4n.UniqueSlotMap.get?,
    SeLe4n.UniqueSlotMap.erase] at hLookup
  by_cases h : (slot == s) = true
  · -- s = slot: erase returns none, contradicting some cap
    have hEq : slot = s := eq_of_beq h
    rw [← hEq] at hLookup
    have := SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self cn.slots.table slot hUniq.1
    rw [this] at hLookup; exact absurd hLookup (by simp)
  · -- s ≠ slot: erase preserves lookup
    have hNe : slot ≠ s := fun heq => h (beq_iff_eq.mpr heq)
    have := SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne_K cn.slots.table slot s
      (fun hb => hNe (eq_of_beq hb)) hUniq
    rw [this] at hLookup
    show cn.slots.table.get? s = some cap
    exact hLookup

/-- WS-H13: CNode.revokeTargetLocal preserves radixWidth and has slot subset. -/
private theorem CNode.revokeTargetLocal_radixWidth_eq (cn : CNode) (slot : SeLe4n.Slot) (target : CapTarget) :
    (cn.revokeTargetLocal slot target).radixWidth = cn.radixWidth := rfl

private theorem CNode.revokeTargetLocal_slots_sub (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (hUniq : cn.slotsUnique) :
    ∀ (s : SeLe4n.Slot) (cap : Capability),
      (cn.revokeTargetLocal sourceSlot target).slots.get? s = some cap →
      cn.slots.get? s = some cap := by
  intro s cap hLookup
  simp only [CNode.revokeTargetLocal, CNode.slots_filterSlots, SeLe4n.UniqueSlotMap.get?,
    SeLe4n.UniqueSlotMap.filter] at hLookup
  exact SeLe4n.Kernel.RobinHood.RHTable.filter_get_subset cn.slots.table _ s cap hUniq.1 hLookup

/-- WS-H4: Transfer WS-H4 predicates through reply path.
storeTcbIpcStateAndMessage → ensureRunnable preserves both. -/
theorem cdtPredicates_through_reply_path
    (st st1 : SystemState) (target : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hObjInv : st.objects.invExt)
    (hTcb : storeTcbIpcStateAndMessage st target ipc msg = .ok st1) :
    cdtCompleteness (ensureRunnable st1 target) ∧
    cdtAcyclicity (ensureRunnable st1 target) := by
  have hCdt1 := storeTcbIpcStateAndMessage_cdt_eq hTcb
  have hComp1 : cdtCompleteness st1 := by
    unfold storeTcbIpcStateAndMessage modifyTcb at hTcb
    cases hL : lookupTcb st target with
    | none => simp [hL] at hTcb
    | some tcb =>
      simp only [hL] at hTcb
      cases hS : storeObject target.toObjId (.tcb (TCB.setIpcState { tcb with pendingMessage := msg } ipc)) st with
      | error e => simp [hS] at hTcb
      | ok pair =>
        simp only [hS] at hTcb; have hEq := Except.ok.inj hTcb; subst hEq
        exact cdtCompleteness_of_storeObject_slots_mono st pair.2 target.toObjId (.tcb tcb) _ hComp
          hObjInv (lookupTcb_some_objects st target tcb hL) hS (fun _ h => h)
  have hEns := ensureRunnable_onlyObjectsSchedulerDiffer st1 target
  unfold SystemState.onlyObjectsSchedulerDiffer at hEns
  have hEnsNS : (ensureRunnable st1 target).cdt = st1.cdt := by rw [hEns]
  have hEnsCdt : (ensureRunnable st1 target).cdt = st.cdt := by rw [hEns]; rw [hCdt1]
  exact ⟨cdtCompleteness_of_objectsAgreeOffRunLinks
      (ensureRunnable_objectsAgreeOffRunLinks st1 target) hComp1 hEnsNS,
    cdtAcyclicity_of_cdt_eq st _ hAcyclic hEnsCdt⟩
