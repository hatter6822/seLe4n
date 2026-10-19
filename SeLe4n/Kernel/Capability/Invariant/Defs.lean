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
retrievable via `lookupSlotCap`.

WS-G5: With HashMap-backed slots, lookup completeness is direct — `CNode.lookup`
delegates to `HashMap.getElem?`, which is the canonical accessor. The property
is trivially true by the identity `CNode.lookup slot = cn.slots[slot]?`. -/
def cspaceLookupSound (st : SystemState) : Prop :=
  ∀ (cnodeId : SeLe4n.ObjId) (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability),
    st.objects[cnodeId]? = some (KernelObject.cnode cn) →
    cn.lookup slot = some cap →
    SystemState.lookupSlotCap st { cnode := cnodeId, slot := slot } = some cap

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
      SystemState.lookupSlotCap st' addr = none) ∧
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

/-- WS-H4/C-03: Every CNode has at most `2^radixBits` occupied slots.
This is the meaningful slot-capacity invariant that replaces the trivially-true
`slotsUnique` predicate for actual security assurance. -/
def cspaceSlotCountBounded (st : SystemState) : Prop :=
  ∀ (cnodeId : SeLe4n.ObjId) (cn : CNode),
    st.objects[cnodeId]? = some (KernelObject.cnode cn) → cn.slotCountBounded

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
    ∃ cn, st.objects[ref.cnode]? = some (.cnode cn) ∧ cn.lookup ref.slot ≠ none

/-- WS-ZA ZA5.3: a slot the tree names lies in a live CNode's slot array, so its
links have words to live in (`SystemState.slotInCNode`). -/
theorem slotInCNode_of_occupied {st : SystemState} {ref : SlotRef}
    (h : ∃ cn, st.objects[ref.cnode]? = some (.cnode cn) ∧ cn.lookup ref.slot ≠ none) :
    st.slotInCNode ref := by
  obtain ⟨cn, hCn, hL⟩ := h
  obtain ⟨cap, hCap⟩ := Option.ne_none_iff_exists'.mp hL
  exact ⟨cn, hCn, cn.slots_get?_bounded ref.slot (by
    have := hCap; unfold CNode.lookup at this
    unfold SeLe4n.UniqueSlotMap.get? at this; rw [this]; simp)⟩

theorem cdtCompleteness.slotInCNode {st : SystemState} (h : cdtCompleteness st)
    {ref : SlotRef} (hM : st.cdt.mentions ref) : st.slotInCNode ref :=
  slotInCNode_of_occupied (h ref hM)

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
  obtain ⟨cn, hCn, -⟩ := h ref hM
  rw [hCn]; simp

/-- An empty slot is outside the tree. -/
theorem cdtCompleteness.not_mentions_of_empty {st : SystemState} (h : cdtCompleteness st)
    {ref : SlotRef} (hEmpty : ∀ cn, st.objects[ref.cnode]? = some (.cnode cn) →
      cn.lookup ref.slot = none) : ¬ st.cdt.mentions ref := by
  intro hM
  obtain ⟨cn, hCn, hSome⟩ := h ref hM
  exact hSome (hEmpty cn hCn)

/-- The tree's slots hold capabilities except, possibly, the slots `gone` names:
the state a destroyer leaves between emptying slots and taking them out of the
tree. -/
def cdtCompletenessOff (st : SystemState) (gone : SlotRef → Prop) : Prop :=
  ∀ ref : SlotRef, st.cdt.mentions ref → ¬ gone ref →
    ∃ cn, st.objects[ref.cnode]? = some (.cnode cn) ∧ cn.lookup ref.slot ≠ none

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

/-- WS-H13/H-01: CSpace depth consistency — every CNode has bounded depth and
well-formed bit allocation.

Each CNode in the object store has `depth ≤ maxCSpaceDepth`, and whenever its
`bitsConsumed` is positive it satisfies `cnodeWellFormed` (guard + radix ≤ depth,
individual widths bounded). Combined with `bitsConsumed > 0`, this guarantees
that multi-level `resolveCapAddress` terminates by structural recursion on
remaining bit count — no cross-CNode depth ordering is required. -/
def cspaceDepthConsistent (st : SystemState) : Prop :=
  ∀ (cnodeId : SeLe4n.ObjId) (cn : CNode),
    st.objects[cnodeId]? = some (.cnode cn) →
    cn.depth ≤ maxCSpaceDepth ∧
    (cn.bitsConsumed > 0 → cn.wellFormed)

/-- WS-SM SM6.D / PR #822 Phase H (#1): **no dangling reply caps** — every `.replyCap rid`
held in a CNode slot is backed by an existing Reply object.  Mirrors the runtime
`cspaceSlotCoherencyChecks` backing check (`.replyCap rid => getReply? rid .isSome` in
`Testing/InvariantChecks.lean`); the production capability/lifecycle invariants previously
only constrained `.object` cap targets, so the model admitted a `.replyCap rid` pointing at
an absent/non-Reply object that the live `.reply` path then rejects (`getReply?`).  The
7th conjunct of `capabilityInvariantBundle`; preserved by the cap ops via the keystone
`cspaceInsertSlot_preserves_replyCapPointsToValidReply` (+ delete dual). -/
def replyCapPointsToValidReply (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (cn : CNode) (slot : SeLe4n.Slot)
    (cap : Capability) (rid : SeLe4n.ReplyId),
    st.objects[oid]? = some (.cnode cn) →
    cn.lookup slot = some cap →
    cap.target = .replyCap rid →
    st.getReply? rid ≠ none

/-- #1: `replyCapPointsToValidReply` reads only the object store (CNode slots +
`getReply?`), so any transition leaving `st.objects` unchanged frames it. -/
theorem replyCapPointsToValidReply_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (h : replyCapPointsToValidReply st) :
    replyCapPointsToValidReply st' := by
  unfold replyCapPointsToValidReply SystemState.getReply? at h ⊢
  rw [hObjs]; exact h

/-- WS-ZA ZA4.5: a step writing only run-queue links keeps every reply cap
backed — CNodes and Reply objects are not TCBs. -/
theorem replyCapPointsToValidReply_of_objectsAgreeOffRunLinks {st st' : SystemState}
    (hA : st'.objectsAgreeOffRunLinks st) (h : replyCapPointsToValidReply st) :
    replyCapPointsToValidReply st' := by
  intro oid cn slot cap rid hCn hLk hT
  rw [hA.getReply? rid]
  exact h oid cn slot cap rid (hA.get_cnode_iff.mp hCn) hLk hT

/-- Composed capability invariant bundle entrypoint.

The active lifecycle slice extends the M2 foundation bundle with security-meaningful
state predicates. Only genuine state invariants are included — predicates that assert
properties of the system state and must be preserved through every transition.

WS-H4: Extended with meaningful security predicates:
- `cspaceSlotCountBounded`: slot capacity bound (replaces trivially-true `slotsUnique`)
- `cdtCompleteness`: CDT slot reachability (every slot the tree names lies in an existing object)
- `cdtAcyclicity`: CDT cycle-freedom for sound revocation

WS-H13: Extended with depth consistency:
- `cspaceDepthConsistent`: child CNodes have strictly smaller depth than parents

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
bundle now has **8** conjuncts: the R4.A.6 close-out retired `cspaceSlotUnique`
(7 → 6), PR #822 Phase H #1.a added `replyCapPointsToValidReply` (the 7th,
6 → 7) so the step-preserved bundle rules out dangling `.replyCap` slots, and
WS-ZA ZA5.3 part 4 added `cdtLinksAgree` (the 8th): the derivation links the
slots hold agree with the tree, so the executable children and descendant reads
that walk them read the tree.
Per-CNode slot uniqueness is discharged directly via
`SeLe4n.Model.CNode.slotsUnique_holds`. -/
def capabilityInvariantBundle (st : SystemState) : Prop :=
  cspaceLookupSound st ∧
    cspaceSlotCountBounded st ∧ cdtCompleteness st ∧ cdtAcyclicity st ∧
    cspaceDepthConsistent st ∧ st.objects.invExt ∧ replyCapPointsToValidReply st ∧
    cdtLinksAgree st

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
    cspaceSlotCountBounded st ∧ cdtCompleteness st ∧ cdtAcyclicity st ∧
    cspaceDepthConsistent st ∧ st.objects.invExt ∧ replyCapPointsToValidReply st

theorem capabilityInvariantBundle.offLinks {st : SystemState} (h : capabilityInvariantBundle st) :
    capabilityBundleOffLinks st :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem capabilityBundleOffLinks.withLinks {st : SystemState} (h : capabilityBundleOffLinks st)
    (hL : cdtLinksAgree st) : capabilityInvariantBundle st :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, hL⟩

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
  /-- Every CNode slot table satisfies its `slotCountBounded` invariant. -/
  slotCountBounded : cspaceSlotCountBounded st
  /-- Every slot the derivation tree names holds a capability. -/
  cdtCompleteness : cdtCompleteness st
  /-- The capability derivation graph is acyclic. -/
  cdtAcyclicity : cdtAcyclicity st
  /-- Child CNodes have strictly smaller guard/radix depth than their
      parents. -/
  depthConsistent : cspaceDepthConsistent st
  /-- The kernel-level `objects` `RHTable` invariant holds (external hash,
      capacity positive, no duplicate keys). -/
  objectsInvExt : st.objects.invExt
  /-- WS-SM SM6.D / PR #822 Phase H (#1): every `.replyCap rid` in a CNode slot is
      backed by an existing Reply object (no dangling reply caps). -/
  replyCapBacked : replyCapPointsToValidReply st
  /-- WS-ZA ZA5.3: the slot links encode the derivation tree. -/
  linksAgree : cdtLinksAgree st

/-- AN4-F.5.1 (CAP-M05): Bidirectional bridge between the tuple and named
forms. Consumers can move freely between the two representations; the
primary def continues to be the tuple form so existing destructures
compile unchanged. -/
theorem capabilityInvariantBundle_iff_CapabilityInvariantBundle
    (st : SystemState) :
    capabilityInvariantBundle st ↔ CapabilityInvariantBundle st := by
  constructor
  · rintro ⟨hS, hB, hComp, hAcyc, hDep, hObj, hRCPV, hLinks⟩
    exact { lookupSound := hS, slotCountBounded := hB
          , cdtCompleteness := hComp, cdtAcyclicity := hAcyc
          , depthConsistent := hDep, objectsInvExt := hObj
          , replyCapBacked := hRCPV, linksAgree := hLinks }
  · intro h
    exact ⟨h.lookupSound, h.slotCountBounded,
           h.cdtCompleteness, h.cdtAcyclicity, h.depthConsistent,
           h.objectsInvExt, h.replyCapBacked, h.linksAgree⟩

/-! ### AN4-F.5.2 (CAP-M05): `@[simp]` projection abbreviations

Shorthand accessors so consumers of the tuple form can use named fields
without going through the bidirectional bridge. Tagged `@[simp]` so the
definitional unfolding happens automatically during `simp`-closed goals. -/

namespace capabilityInvariantBundle

/-- Extract `cspaceLookupSound` from the tuple form. -/
@[simp] abbrev lookupSound {st : SystemState} (h : capabilityInvariantBundle st) :
    cspaceLookupSound st := h.1

/-- Extract `cspaceSlotCountBounded` from the tuple form. -/
@[simp] abbrev slotCountBounded {st : SystemState} (h : capabilityInvariantBundle st) :
    cspaceSlotCountBounded st := h.2.1

/-- Extract `cdtCompleteness` from the tuple form. -/
@[simp] abbrev cdtCompleteness {st : SystemState} (h : capabilityInvariantBundle st) :
    _root_.SeLe4n.Kernel.cdtCompleteness st := h.2.2.1

/-- Extract `cdtAcyclicity` from the tuple form. -/
@[simp] abbrev cdtAcyclicity {st : SystemState} (h : capabilityInvariantBundle st) :
    _root_.SeLe4n.Kernel.cdtAcyclicity st := h.2.2.2.1

/-- Extract `cspaceDepthConsistent` from the tuple form. -/
@[simp] abbrev depthConsistent {st : SystemState} (h : capabilityInvariantBundle st) :
    cspaceDepthConsistent st := h.2.2.2.2.1

/-- Extract `st.objects.invExt` from the tuple form. -/
@[simp] abbrev objectsInvExt {st : SystemState} (h : capabilityInvariantBundle st) :
    st.objects.invExt := h.2.2.2.2.2.1

/-- WS-SM SM6.D / PR #822 Phase H (#1): extract `replyCapPointsToValidReply` from the
tuple form (the 7th conjunct). -/
@[simp] abbrev replyCapBacked {st : SystemState} (h : capabilityInvariantBundle st) :
    _root_.SeLe4n.Kernel.replyCapPointsToValidReply st := h.2.2.2.2.2.2.1

/-- WS-ZA ZA5.3: extract `cdtLinksAgree` from the tuple form (the 8th conjunct). -/
@[simp] abbrev linksAgree {st : SystemState} (h : capabilityInvariantBundle st) :
    _root_.SeLe4n.Kernel.cdtLinksAgree st := h.2.2.2.2.2.2.2

end capabilityInvariantBundle

/-! ## AN4-F.4 (CAP-M04) — `RetypeTarget` precondition subtype

The retype pipeline (`lifecyclePreRetypeCleanup` → `scrubObjectMemory` →
`Internal.lifecycleRetypeObject`) carries a caller obligation: the cleanup
hook must have run on the target id before the retype primitive executes.
Historically this was a documented invariant maintained by
`lifecycleRetypeWithCleanup` (AN4-A) and its `Direct` variant, but the
obligation was not reflected in any type.

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
the *pre-retype* state `st`. The subtype is used at the boundary of
`lifecycleRetypeWithCleanup` and its proof-chain companions so callers
cannot construct a target without carrying the discharge obligation.

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

/-- AN4-F.4 (CAP-M04): Identity-coercion helper — recover the raw `ObjId`
from a `RetypeTarget`. Used by the cleanup-integrated wrappers when they
have to drop into the type-erased internal primitive. -/
@[inline] def RetypeTarget.toObjId {st : SystemState} (tgt : RetypeTarget st) :
    SeLe4n.ObjId := tgt.id

instance {st : SystemState} : CoeHead (RetypeTarget st) SeLe4n.ObjId where
  coe tgt := tgt.id

-- ============================================================================
-- WS-H4: Extraction theorems for new bundle components
-- ============================================================================

theorem cspaceSlotCountBounded_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cspaceSlotCountBounded st := hInv.2.1

theorem cdtCompleteness_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cdtCompleteness st := hInv.2.2.1

theorem cdtAcyclicity_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cdtAcyclicity st := hInv.2.2.2.1

theorem cspaceDepthConsistent_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cspaceDepthConsistent st := hInv.2.2.2.2.1

theorem objects_invExt_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    st.objects.invExt := hInv.2.2.2.2.2.1

/-- WS-SM SM6.D / PR #822 Phase H (#1): extract the reply-cap backing invariant. -/
theorem replyCapPointsToValidReply_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    replyCapPointsToValidReply st := hInv.2.2.2.2.2.2.1

/-- WS-ZA ZA5.3: extract the slot-link agreement. -/
theorem cdtLinksAgree_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cdtLinksAgree st := hInv.2.2.2.2.2.2.2

-- ============================================================================
-- WS-H4: Transfer theorems for new components through state transitions
-- ============================================================================

/-- WS-H4: Transfer cspaceSlotCountBounded through storeObject when
the stored object is NOT a CNode (endpoint, TCB, etc.). -/
private theorem cspaceSlotCountBounded_of_storeObject_nonCNode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hBounded : cspaceSlotCountBounded st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hNotCNode : ∀ cn, obj ≠ .cnode cn) :
    cspaceSlotCountBounded st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = oid
  · subst hEq
    have := storeObject_objects_eq st st' cnodeId obj hObjInv hStore
    rw [this] at hObj
    cases obj with
    | cnode cn' => exact absurd rfl (hNotCNode cn')
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => cases hObj
  · have hPre := storeObject_objects_ne st st' oid cnodeId obj hEq hObjInv hStore
    rw [hPre] at hObj
    exact hBounded cnodeId cn hObj

/-- WS-H4: Transfer cspaceSlotCountBounded through storeObject when
the stored object IS a CNode (requires new CNode to be bounded). -/
theorem cspaceSlotCountBounded_of_storeObject_cnode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (cn' : CNode)
    (hBounded : cspaceSlotCountBounded st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.cnode cn') st = .ok ((), st'))
    (hNewBounded : cn'.slotCountBounded) :
    cspaceSlotCountBounded st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = oid
  · subst hEq
    have := storeObject_objects_eq st st' cnodeId (.cnode cn') hObjInv hStore
    rw [this] at hObj; cases hObj
    exact hNewBounded
  · have hPre := storeObject_objects_ne st st' oid cnodeId (.cnode cn') hEq hObjInv hStore
    rw [hPre] at hObj
    exact hBounded cnodeId cn hObj

/-- WS-H4: Transfer cspaceSlotCountBounded when objects are unchanged. -/
theorem cspaceSlotCountBounded_of_objects_eq
    (st st' : SystemState)
    (hBounded : cspaceSlotCountBounded st)
    (hObjEq : st'.objects = st.objects) :
    cspaceSlotCountBounded st' := by
  intro cnodeId cn hObj
  rw [hObjEq] at hObj
  exact hBounded cnodeId cn hObj

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

/-- WS-ZA ZA4.5: the three object-reading capability predicates carry across a
step that writes only run-queue links (CNodes are not TCBs, and a key is
occupied in one store exactly when it is in the other). -/
theorem cspaceSlotCountBounded_of_objectsAgreeOffRunLinks {st st' : SystemState}
    (hA : st'.objectsAgreeOffRunLinks st) (hBounded : cspaceSlotCountBounded st) :
    cspaceSlotCountBounded st' :=
  fun cnodeId cn hObj => hBounded cnodeId cn (hA.get_cnode_iff.mp hObj)

theorem cdtCompleteness_of_objectsAgreeOffRunLinks {st st' : SystemState}
    (hA : st'.objectsAgreeOffRunLinks st) (hComp : cdtCompleteness st)
    (hCdtEq : st'.cdt = st.cdt) : cdtCompleteness st' := by
  intro ref hM
  rw [hCdtEq] at hM
  obtain ⟨cn, hCn, hL⟩ := hComp ref hM
  exact ⟨cn, hA.get_cnode_iff.mpr hCn, hL⟩

theorem cspaceDepthConsistent_of_objectsAgreeOffRunLinks {st st' : SystemState}
    (hA : st'.objectsAgreeOffRunLinks st) (hDepth : cspaceDepthConsistent st) :
    cspaceDepthConsistent st' :=
  fun cnodeId cn hObj => hDepth cnodeId cn (hA.get_cnode_iff.mp hObj)

/-- WS-H4: Transfer cdtCompleteness through storeObject.  Every key but `oid`
keeps its object; at `oid` the stored object must hold every slot the tree names
there (`hAt`). -/
theorem cdtCompleteness_of_storeObject
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hComp : cdtCompleteness st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hAt : ∀ ref : SlotRef, st.cdt.mentions ref → ref.cnode = oid →
      ∃ cn, obj = .cnode cn ∧ cn.lookup ref.slot ≠ none) :
    cdtCompleteness st' := by
  intro ref hM
  rw [storeObject_cdt_eq st st' oid obj hStore] at hM
  by_cases hEq : ref.cnode = oid
  · obtain ⟨cn, rfl, hL⟩ := hAt ref hM hEq
    exact ⟨cn, by rw [hEq, storeObject_objects_eq st st' oid _ hObjInv hStore], hL⟩
  · rw [storeObject_objects_ne st st' oid ref.cnode obj hEq hObjInv hStore]; exact hComp ref hM

/-- A store at a key that holds no CNode keeps the tree's slots: the tree names
no slot there. -/
theorem cdtCompleteness_of_storeObject_notCNode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hComp : cdtCompleteness st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hPre : ∀ cn, st.objects[oid]? ≠ some (.cnode cn)) :
    cdtCompleteness st' :=
  cdtCompleteness_of_storeObject st st' oid obj hComp hObjInv hStore fun ref hM hEq => by
    obtain ⟨cn, hCn, -⟩ := hComp ref hM
    exact absurd (hEq ▸ hCn) (hPre cn)

/-- A CNode store that keeps every occupied slot occupied keeps the tree's slots. -/
theorem cdtCompleteness_of_storeObject_cnode_mono
    (st st' : SystemState) (oid : SeLe4n.ObjId) (cn cn' : CNode)
    (hComp : cdtCompleteness st)
    (hObjInv : st.objects.invExt)
    (hPre : st.objects[oid]? = some (.cnode cn))
    (hStore : storeObject oid (.cnode cn') st = .ok ((), st'))
    (hMono : ∀ s, cn.lookup s ≠ none → cn'.lookup s ≠ none) :
    cdtCompleteness st' :=
  cdtCompleteness_of_storeObject st st' oid _ hComp hObjInv hStore fun ref hM hEq => by
    obtain ⟨cn₀, hCn, hL⟩ := hComp ref hM
    rw [hEq, hPre] at hCn; cases hCn
    exact ⟨cn', rfl, hMono _ hL⟩

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
    ⟨cn', rfl, hKeep ref.slot (by cases ref; cases hEq; exact hM)⟩

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
    obtain ⟨cn₀, hCn, hL⟩ := hComp ⟨c, s⟩ hM
    simp only [hPre] at hCn; cases hCn
    exact ⟨cn', storeObject_objects_eq st st' c _ hObjInv hStore,
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

/-- WS-H4: Transfer cspaceSlotCountBounded through storeTcbIpcState
(stores a TCB, not a CNode, so slot bounds are preserved). -/
private theorem cspaceSlotCountBounded_of_storeTcbIpcState
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hBounded : cspaceSlotCountBounded st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    cspaceSlotCountBounded st' := by
  intro cnodeId cn hObj
  have hPre : st.objects[cnodeId]? = some (.cnode cn) :=
    storeTcbIpcState_cnode_backward st st' tid ipc cnodeId cn hObjInv hStep hObj
  exact hBounded cnodeId cn hPre

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

/-- WS-H4: Transfer all three new predicates when objects and CDT fields are
both preserved. Used for scheduler-only updates (removeRunnable, ensureRunnable). -/
private theorem cdtPredicates_of_objects_cdt_eq
    (st st' : SystemState)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hObjEq : st'.objects = st.objects)
    (hCdtEq : st'.cdt = st.cdt) :
    cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' :=
  ⟨cspaceSlotCountBounded_of_objects_eq st st' hBounded hObjEq,
   cdtCompleteness_of_objects_cdt_eq st st' hComp hObjEq hCdtEq,
   cdtAcyclicity_of_cdt_eq st st' hAcyclic hCdtEq⟩

/-- WS-H13: Transfer cspaceDepthConsistent when objects are unchanged. -/
theorem cspaceDepthConsistent_of_objects_eq
    (st st' : SystemState)
    (hDepth : cspaceDepthConsistent st)
    (hObjEq : st'.objects = st.objects) :
    cspaceDepthConsistent st' := by
  intro cnodeId cn hObj; rw [hObjEq] at hObj; exact hDepth cnodeId cn hObj

/-- WS-H13: Transfer cspaceDepthConsistent through storeObject when the stored
object is NOT a CNode (endpoint, TCB, etc.). -/
private theorem cspaceDepthConsistent_of_storeObject_nonCNode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hDepth : cspaceDepthConsistent st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hNotCNode : ∀ cn, obj ≠ .cnode cn) :
    cspaceDepthConsistent st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = oid
  · subst hEq
    have := storeObject_objects_eq st st' cnodeId obj hObjInv hStore
    rw [this] at hObj; cases obj with
    | cnode cn' => exact absurd rfl (hNotCNode cn')
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => cases hObj
  · rw [storeObject_objects_ne st st' oid cnodeId obj hEq hObjInv hStore] at hObj
    exact hDepth cnodeId cn hObj

/-- WS-H13: Transfer cspaceDepthConsistent through storeObject when the stored
CNode has the same depth and bit-width fields as the pre-state CNode at that oid.
This covers CNode.insert, CNode.remove, and CNode.revokeTargetLocal. -/
theorem cspaceDepthConsistent_of_storeObject_sameCNode
    (st st' : SystemState) (targetOid : SeLe4n.ObjId) (preCn cn' : CNode)
    (hDepth : cspaceDepthConsistent st)
    (hObjInv : st.objects.invExt)
    (hPreObj : st.objects[targetOid]? = some (.cnode preCn))
    (hStore : storeObject targetOid (.cnode cn') st = .ok ((), st'))
    (hSameDepth : cn'.depth = preCn.depth)
    (hSameGW : cn'.guardWidth = preCn.guardWidth)
    (hSameRW : cn'.radixWidth = preCn.radixWidth)
    (hSameGV : cn'.guardValue = preCn.guardValue) :
    cspaceDepthConsistent st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = targetOid
  · rw [hEq] at hObj
    rw [storeObject_objects_eq st st' targetOid (.cnode cn') hObjInv hStore] at hObj; cases hObj
    have hPreBound := hDepth targetOid preCn hPreObj
    constructor
    · rw [hSameDepth]; exact hPreBound.1
    · intro hBits
      have hBitsPre : preCn.bitsConsumed > 0 := by
        unfold CNode.bitsConsumed at hBits ⊢; rw [hSameGW, hSameRW] at hBits; exact hBits
      have hWfPre := hPreBound.2 hBitsPre
      unfold CNode.wellFormed at hWfPre ⊢
      refine ⟨?_, ?_, ?_⟩
      · unfold CNode.bitsConsumed at hWfPre ⊢; rw [hSameGW, hSameRW, hSameDepth]; exact hWfPre.1
      · unfold CNode.bitsConsumed at hWfPre ⊢; rw [hSameGW, hSameRW]; exact hWfPre.2.1
      · unfold CNode.guardBounded at hWfPre ⊢; rw [hSameGW, hSameGV]; exact hWfPre.2.2
  · rw [storeObject_objects_ne st st' targetOid cnodeId (.cnode cn') hEq hObjInv hStore] at hObj
    exact hDepth cnodeId cn hObj

/-- WS-H13: Transfer cspaceDepthConsistent through storeObject when inserting a capability
into a CNode, given the inserted capability satisfies the parent-child depth constraint. -/
theorem cspaceDepthConsistent_of_storeObject_insertCNode
    (st st' : SystemState) (targetOid : SeLe4n.ObjId) (preCn : CNode)
    (insertSlot : SeLe4n.Slot) (insertCap : Capability)
    (hDepth : cspaceDepthConsistent st)
    (hObjInv : st.objects.invExt)
    (hPreObj : st.objects[targetOid]? = some (.cnode preCn))
    (hStore : storeObject targetOid (.cnode (preCn.insert insertSlot insertCap)) st = .ok ((), st')) :
    cspaceDepthConsistent st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = targetOid
  · rw [hEq] at hObj
    rw [storeObject_objects_eq st st' targetOid _ hObjInv hStore] at hObj; cases hObj
    simpa only [CNode.wellFormed, CNode.bitsConsumed, CNode.guardBounded, CNode.insert_depth,
      CNode.insert_guardWidth, CNode.insert_guardValue, CNode.insert_radixWidth]
      using hDepth targetOid preCn hPreObj
  · rw [storeObject_objects_ne st st' targetOid cnodeId _ hEq hObjInv hStore] at hObj
    exact hDepth cnodeId cn hObj

/-- WS-H13: CNode.remove preserves depth/guardWidth/radixWidth and has slot subset. -/
private theorem CNode.remove_depth_eq (cn : CNode) (slot : SeLe4n.Slot) :
    (cn.remove slot).depth = cn.depth := rfl

private theorem CNode.remove_guardWidth_eq (cn : CNode) (slot : SeLe4n.Slot) :
    (cn.remove slot).guardWidth = cn.guardWidth := rfl

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

/-- WS-H13: CNode.revokeTargetLocal preserves depth/guardWidth/radixWidth and has slot subset. -/
private theorem CNode.revokeTargetLocal_depth_eq (cn : CNode) (slot : SeLe4n.Slot) (target : CapTarget) :
    (cn.revokeTargetLocal slot target).depth = cn.depth := rfl

private theorem CNode.revokeTargetLocal_guardWidth_eq (cn : CNode) (slot : SeLe4n.Slot) (target : CapTarget) :
    (cn.revokeTargetLocal slot target).guardWidth = cn.guardWidth := rfl

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

/-- WS-H4: CDT-only state update preserves cspaceSlotCountBounded, and
cdtCompleteness whenever every slot the new tree names was named by the old one.
Used for `{ st with cdt := cdt' }` where the objects are unchanged. -/
private theorem boundedCompleteness_of_cdt_only_update
    (st : SystemState) (cdt' : CapDerivationTree)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st)
    (hSub : ∀ ref, cdt'.mentions ref → st.cdt.mentions ref) :
    cspaceSlotCountBounded { st with cdt := cdt' } ∧
    cdtCompleteness { st with cdt := cdt' } :=
  ⟨hBounded, fun ref hM => hComp ref (hSub ref hM)⟩

/-- WS-H4: Transfer WS-H4 predicates through reply path.
storeTcbIpcStateAndMessage → ensureRunnable preserves all three. -/
theorem cdtPredicates_through_reply_path
    (st st1 : SystemState) (target : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hObjInv : st.objects.invExt)
    (hTcb : storeTcbIpcStateAndMessage st target ipc msg = .ok st1) :
    cspaceSlotCountBounded (ensureRunnable st1 target) ∧
    cdtCompleteness (ensureRunnable st1 target) ∧
    cdtAcyclicity (ensureRunnable st1 target) := by
  have hCdt1 := storeTcbIpcStateAndMessage_cdt_eq hTcb
  have hBnd1 : cspaceSlotCountBounded st1 := by
    unfold storeTcbIpcStateAndMessage modifyTcb at hTcb
    cases hL : lookupTcb st target with
    | none => simp [hL] at hTcb
    | some tcb =>
      simp only [hL] at hTcb
      cases hS : storeObject target.toObjId (.tcb (TCB.setIpcState { tcb with pendingMessage := msg } ipc)) st with
      | error e => simp [hS] at hTcb
      | ok pair =>
        simp only [hS] at hTcb; have hEq := Except.ok.inj hTcb; subst hEq
        exact cspaceSlotCountBounded_of_storeObject_nonCNode st pair.2 target.toObjId _ hBounded hObjInv hS
          (fun cn h => by cases h)
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
        exact cdtCompleteness_of_storeObject_notCNode st pair.2 target.toObjId _ hComp hObjInv hS
          (fun cn h => by rw [lookupTcb_some_objects st target tcb hL] at h; cases h)
  have hEns := ensureRunnable_onlyObjectsSchedulerDiffer st1 target
  unfold SystemState.onlyObjectsSchedulerDiffer at hEns
  have hEnsNS : (ensureRunnable st1 target).cdt = st1.cdt := by rw [hEns]
  have hEnsCdt : (ensureRunnable st1 target).cdt = st.cdt := by rw [hEns]; rw [hCdt1]
  exact ⟨cspaceSlotCountBounded_of_objectsAgreeOffRunLinks
      (ensureRunnable_objectsAgreeOffRunLinks st1 target) hBnd1,
    cdtCompleteness_of_objectsAgreeOffRunLinks
      (ensureRunnable_objectsAgreeOffRunLinks st1 target) hComp1 hEnsNS,
    cdtAcyclicity_of_cdt_eq st _ hAcyclic hEnsCdt⟩
