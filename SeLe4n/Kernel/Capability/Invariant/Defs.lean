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

/-- WS-H4/M-08: CDT node-slot coherence — every registered CDT node
points to an object that exists in the state. This ensures CDT-based
revocation can locate capabilities referenced by node mappings. The
predicate is robust through `detachSlotFromCdt` operations because
detached nodes lose their mapping (vacuously satisfying the condition).

**Scope vs spec intent**: The WS-H4 spec envisions mint-based CDT
completeness ("every derived capability has a CDT edge"). This predicate
captures the weaker but foundational node-slot reachability property:
CDT nodes never point to deleted objects. Mint-tracking completeness
requires `cspaceMintWithCdt` as the sole mint path (see M-08/A-20
annotation in API.lean). -/
def cdtCompleteness (st : SystemState) : Prop :=
  ∀ (nodeId : CdtNodeId) (ref : SlotRef),
    st.cdtNodeSlot[nodeId]? = some ref →
    st.objects[ref.cnode]? ≠ none

/-- WS-H4/M-03: CDT acyclicity — the capability derivation tree has no cycles.
Required for `descendantsOf` termination and revocation completeness. Uses the
edge-well-founded formulation for clean subset-preservation proofs. -/
def cdtAcyclicity (st : SystemState) : Prop :=
  st.cdt.edgeWellFounded

/-- WS-H4/M-G02: Mint-tracking completeness — every CDT node that has a slot mapping
is either (a) the child of some derivation edge (it was derived via mint/copy), or
(b) isolated (a root node with no edges referencing it at all).

This is stronger than `cdtCompleteness` (which only ensures node→object reachability)
and captures the invariant that `addEdge` is always called alongside
`ensureCdtNodeForSlot` during mint/copy operations. Required for proving that
CDT-based revocation via `cspaceRevokeCdt` is exhaustive.

Kept as a standalone predicate (not in `capabilityInvariantBundle`) to avoid churn
on the 60+ theorems that destructure the 6-tuple bundle. Use
`capabilityInvariantBundleWithMintCompleteness` for the full 7-property assurance. -/
def cdtMintCompleteness (st : SystemState) : Prop :=
  ∀ (childNode : CdtNodeId) (childRef : SlotRef),
    st.cdtNodeSlot[childNode]? = some childRef →
    (∃ edge ∈ st.cdt.edges, edge.child = childNode) ∨
    (¬∃ edge ∈ st.cdt.edges, edge.parent = childNode ∨ edge.child = childNode)

/-- WS-H4/M-G02: The default system state has empty CDT node mappings,
so `cdtMintCompleteness` holds vacuously. -/
theorem cdtMintCompleteness_default : cdtMintCompleteness default := by
  intro childNode childRef hLookup
  have : (default : SystemState).cdtNodeSlot[childNode]? = none := by
    simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
  rw [this] at hLookup; exact absurd hLookup (by simp)

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

/-- Composed capability invariant bundle entrypoint.

The active lifecycle slice extends the M2 foundation bundle with security-meaningful
state predicates. Only genuine state invariants are included — predicates that assert
properties of the system state and must be preserved through every transition.

WS-H4: Extended with meaningful security predicates:
- `cspaceSlotCountBounded`: slot capacity bound (replaces trivially-true `slotsUnique`)
- `cdtCompleteness`: CDT node-slot reachability (every CDT node points to an existing object)
- `cdtAcyclicity`: CDT cycle-freedom for sound revocation

WS-H13: Extended with depth consistency:
- `cspaceDepthConsistent`: child CNodes have strictly smaller depth than parents

WS-F6/D1: Reduced from 8-tuple to 6-tuple. Removed `cspaceAttenuationRule` (operation
property of `mintDerivedCap`, not a state invariant — no `st` parameter) and
`lifecycleAuthorityMonotonicity` (operation-correctness lemma about delete/revoke
effects, not a state property preserved through transitions). Both are retained as
standalone operation-correctness lemmas in `Authority.lean`.

**Design decisions (WS-H4):**
- CDT-modifying operations (`cspaceCopy`, `cspaceMove`, `cspaceMintWithCdt`) take
  `hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st'` as hypotheses rather than
  proving acyclicity preservation through `addEdge`. This is because proving
  `addEdge_preserves_acyclicity` requires a cycle-check precondition that must be
  validated at the caller; the hypothesis pattern correctly defers this obligation.
- CDT-shrinking operations (revoke/delete) prove acyclicity via
  `CapDerivationTree.edgeWellFounded_sub` (edge subset preserves well-foundedness).
- AF5-F (AF-26): This conjunction uses right-associative `∧` chains
  accessed via `.2.2.2...` projections. Refactoring to a named structure is
  recorded as a post-1.0 hardening candidate; no currently-active plan file
  tracks it (see Builder.lean AF5-F annotation for rationale).

WS-RC R4.A.6: The historical `cspaceSlotUnique` conjunct was removed when
`CNode.slots : SeLe4n.UniqueSlotMap Capability` carried the slot-uniqueness
witness structurally at construction time (via `UniqueSlotMap.hWF`).  The
bundle now has 6 conjuncts; per-CNode slot uniqueness is discharged
directly via `SeLe4n.Model.CNode.slotsUnique_holds`. -/
def capabilityInvariantBundle (st : SystemState) : Prop :=
  cspaceLookupSound st ∧
    cspaceSlotCountBounded st ∧ cdtCompleteness st ∧ cdtAcyclicity st ∧
    cspaceDepthConsistent st ∧ st.objects.invExt ∧ replyCapPointsToValidReply st

/-! ## AN4-F.5 (CAP-M05) — Named-projection refactor of `capabilityInvariantBundle`

Mirror of the AN3-B playbook for IPC's `ipcInvariantFull`. The 6-conjunct
right-associative `∧` chain above (was 7 before the WS-RC R4.A.6
close-out retired `cspaceSlotUnique`) is fragile to reason about —
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
  /-- The CDT `childMap`/`parentMap`/`slotNode`/`nodeSlot` bookkeeping
      covers every capability edge emitted by the graph. -/
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

/-- AN4-F.5.1 (CAP-M05): Bidirectional bridge between the tuple and named
forms. Consumers can move freely between the two representations; the
primary def continues to be the tuple form so existing destructures
compile unchanged. -/
theorem capabilityInvariantBundle_iff_CapabilityInvariantBundle
    (st : SystemState) :
    capabilityInvariantBundle st ↔ CapabilityInvariantBundle st := by
  constructor
  · rintro ⟨hS, hB, hComp, hAcyc, hDep, hObj, hRCPV⟩
    exact { lookupSound := hS, slotCountBounded := hB
          , cdtCompleteness := hComp, cdtAcyclicity := hAcyc
          , depthConsistent := hDep, objectsInvExt := hObj
          , replyCapBacked := hRCPV }
  · intro h
    exact ⟨h.lookupSound, h.slotCountBounded,
           h.cdtCompleteness, h.cdtAcyclicity, h.depthConsistent,
           h.objectsInvExt, h.replyCapBacked⟩

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
    _root_.SeLe4n.Kernel.replyCapPointsToValidReply st := h.2.2.2.2.2.2

end capabilityInvariantBundle

/-- AE4-D (U-36/C-CAP06): Extended capability invariant bundle with mint
completeness. Conjoins the standard 7-property `capabilityInvariantBundle`
with `cdtMintCompleteness`, ensuring CDT-based revocation via `cspaceRevokeCdt`
is exhaustive — every CDT node with a slot mapping is either derived (child
of some edge) or isolated (no edges reference it).

Used at the cross-subsystem composition layer (`crossSubsystemInvariant`) to
provide full CDT coverage without modifying the 60+ theorems that destructure
the standard 7-tuple bundle. -/
def capabilityInvariantBundleWithMintCompleteness (st : SystemState) : Prop :=
  capabilityInvariantBundle st ∧ cdtMintCompleteness st

/-- AE4-D: Extract the standard bundle from the extended bundle. -/
theorem capabilityInvariantBundleWithMintCompleteness_to_bundle
    (st : SystemState)
    (h : capabilityInvariantBundleWithMintCompleteness st) :
    capabilityInvariantBundle st := h.1

/-- AE4-D: Extract mint completeness from the extended bundle. -/
theorem capabilityInvariantBundleWithMintCompleteness_to_mintCompleteness
    (st : SystemState)
    (h : capabilityInvariantBundleWithMintCompleteness st) :
    cdtMintCompleteness st := h.2

/-- AE4-D: Construct the extended bundle from the standard bundle + mint completeness. -/
theorem capabilityInvariantBundleWithMintCompleteness_of_parts
    (st : SystemState)
    (hBundle : capabilityInvariantBundle st)
    (hMint : cdtMintCompleteness st) :
    capabilityInvariantBundleWithMintCompleteness st := ⟨hBundle, hMint⟩

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
      ¬ (tcb.tid ∈ (st.scheduler.runQueueOnCore bootCoreId).flat))
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
      ¬ (tcb.tid ∈ (st.scheduler.runQueueOnCore bootCoreId).flat))
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
      ¬ (tcb.tid ∈ (st.scheduler.runQueueOnCore bootCoreId).flat))
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
-- S3-D/U-M03: CDT maps consistency as state-level invariant
-- ============================================================================

/-- S3-D: CDT maps consistency — the bidirectional maps (`childMap`,
    `parentMap`) are consistent with the canonical `edges` list.
    This lifts the CDT-level `childMapConsistent ∧ parentMapConsistent`
    to a state-level invariant predicate. -/
def cdtMapsConsistent (st : SystemState) : Prop :=
  st.cdt.childMapConsistent ∧ st.cdt.parentMapConsistent

/-- S3-D: Default state has empty CDT, so maps consistency holds vacuously.
    Both directions of the iff are trivially false (no edges, no map entries). -/
theorem cdtMapsConsistent_default : cdtMapsConsistent (default : SystemState) := by
  -- Empty CDT: edges = [], childMap = empty, parentMap = empty.
  -- Both iff directions have one side trivially false.
  refine ⟨?_, ?_⟩
  · -- childMapConsistent
    intro parent child; constructor
    · intro hMem
      -- childMap.get? parent = none for empty table
      exfalso
      have hGet : (default : SystemState).cdt.childMap.get? parent = none :=
        RobinHood.RHTable.getElem?_empty 16 (by omega) parent
      -- The goal's getD uses default.cdt.childMap.get?, which equals none
      change child ∈ ((default : SystemState).cdt.childMap.get? parent).getD [] at hMem
      rw [hGet] at hMem; exact (nomatch hMem)
    · intro ⟨_, hE, _, _⟩
      have : (default : SystemState).cdt.edges = [] := rfl
      rw [this] at hE; exact (nomatch hE)
  · -- parentMapConsistent
    intro child parent; constructor
    · intro hLookup
      have hGet : (default : SystemState).cdt.parentMap.get? child = none :=
        RobinHood.RHTable.getElem?_empty 16 (by omega) child
      change (default : SystemState).cdt.parentMap.get? child = some parent at hLookup
      rw [hGet] at hLookup; exact (nomatch hLookup)
    · intro ⟨_, hE, _, _⟩
      have : (default : SystemState).cdt.edges = [] := rfl
      rw [this] at hE; exact (nomatch hE)

-- ============================================================================
-- S3-D: cdtMapsConsistent transfer and frame theorems
-- ============================================================================

/-- S3-D: Transfer `cdtMapsConsistent` through state changes that preserve `cdt`. -/
theorem cdtMapsConsistent_of_cdt_eq
    (st st' : SystemState)
    (hCon : cdtMapsConsistent st)
    (hCdtEq : st'.cdt = st.cdt) :
    cdtMapsConsistent st' := by
  unfold cdtMapsConsistent at hCon ⊢; rw [hCdtEq]; exact hCon

/-- S3-D: `storeObject` preserves `cdtMapsConsistent` (CDT unchanged). -/
theorem cdtMapsConsistent_of_storeObject
    (st st' : SystemState) (oid : ObjId) (obj : KernelObject)
    (hCon : cdtMapsConsistent st)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    cdtMapsConsistent st' :=
  cdtMapsConsistent_of_cdt_eq st st' hCon (storeObject_cdt_eq st st' oid obj hStore)

/-- S3-D: `detachSlotFromCdt` preserves `cdtMapsConsistent` (CDT unchanged —
    it only modifies `cdtSlotNode` and `cdtNodeSlot`). -/
theorem cdtMapsConsistent_of_detachSlotFromCdt
    (st : SystemState) (ref : SlotRef)
    (hCon : cdtMapsConsistent st) :
    cdtMapsConsistent (SystemState.detachSlotFromCdt st ref) := by
  unfold SystemState.detachSlotFromCdt
  split
  · exact hCon  -- none case: state unchanged
  · exact hCon  -- some case: only cdtSlotNode/cdtNodeSlot modified, cdt unchanged

/-- M4-B bridge bundle: ties stale-reference exclusion to lifecycle transition authority
monotonicity so composition proofs can depend on a single named assumption.

WS-F6/D1: `lifecycleAuthorityMonotonicity` is an operation-correctness lemma (proved
by `lifecycleAuthorityMonotonicity_holds`), not extracted from a bundle. -/
def lifecycleCapabilityStaleAuthorityInvariant (st : SystemState) : Prop :=
  lifecycleStaleReferenceExclusionInvariant st ∧ lifecycleAuthorityMonotonicity st

theorem lifecycleCapabilityStaleAuthorityInvariant_of_bundles
    (st : SystemState)
    (hLifecycle : lifecycleInvariantBundle st)
    (_hCap : capabilityInvariantBundle st)
    (hMono : lifecycleAuthorityMonotonicity st) :
    lifecycleCapabilityStaleAuthorityInvariant st :=
  ⟨lifecycleStaleReferenceExclusionInvariant_of_lifecycleInvariantBundle st hLifecycle, hMono⟩

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
    replyCapPointsToValidReply st := hInv.2.2.2.2.2.2

-- ============================================================================
-- WS-H4/M-G02: Transfer theorems for cdtMintCompleteness
-- ============================================================================

/-- WS-H4/M-G02: Transfer cdtMintCompleteness when CDT edges and node-slot
mappings are unchanged (non-CDT operations). -/
theorem cdtMintCompleteness_of_cdt_edges_nodeSlot_eq
    (st st' : SystemState)
    (hMint : cdtMintCompleteness st)
    (hEdgesEq : st'.cdt.edges = st.cdt.edges)
    (hNodeSlotEq : st'.cdtNodeSlot = st.cdtNodeSlot) :
    cdtMintCompleteness st' := by
  intro childNode childRef hLookup
  rw [hNodeSlotEq] at hLookup
  rcases hMint childNode childRef hLookup with h | h
  · left; rcases h with ⟨edge, hMem, hChild⟩
    exact ⟨edge, hEdgesEq ▸ hMem, hChild⟩
  · right; intro ⟨edge, hMem, hPC⟩
    exact h ⟨edge, hEdgesEq ▸ hMem, hPC⟩

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
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => cases hObj
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

/-- WS-H4: Transfer cdtCompleteness when CDT and cdtNodeSlot are unchanged. -/
theorem cdtCompleteness_of_objects_nodeSlot_eq
    (st st' : SystemState)
    (hComp : cdtCompleteness st)
    (hObjEq : st'.objects = st.objects)
    (hNodeSlotEq : st'.cdtNodeSlot = st.cdtNodeSlot) :
    cdtCompleteness st' := by
  intro nodeId ref hNS
  rw [hNodeSlotEq] at hNS
  rw [hObjEq]
  exact hComp nodeId ref hNS

/-- WS-H4: Transfer cdtCompleteness through storeObject. After storeObject,
objects may change but every key that was non-none stays non-none. -/
theorem cdtCompleteness_of_storeObject
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hComp : cdtCompleteness st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hNodeSlotEq : st'.cdtNodeSlot = st.cdtNodeSlot) :
    cdtCompleteness st' := by
  intro nodeId ref hNS
  rw [hNodeSlotEq] at hNS
  have hPre := hComp nodeId ref hNS
  by_cases hEq : ref.cnode = oid
  · rw [hEq]; rw [storeObject_objects_eq st st' oid obj hObjInv hStore]; simp
  · rw [storeObject_objects_ne st st' oid ref.cnode obj hEq hObjInv hStore]; exact hPre

/-- WS-H4: Transfer cdtAcyclicity when CDT is unchanged. -/
theorem cdtAcyclicity_of_cdt_eq
    (st st' : SystemState)
    (hAcyclic : cdtAcyclicity st)
    (hCdtEq : st'.cdt = st.cdt) :
    cdtAcyclicity st' := by
  unfold cdtAcyclicity
  rw [hCdtEq]
  exact hAcyclic

/-- WS-H4: storeObject preserves CDT cdtNodeSlot field. -/
theorem storeObject_cdtNodeSlot_eq
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    st'.cdtNodeSlot = st.cdtNodeSlot ∧ st'.cdtSlotNode = st.cdtSlotNode := by
  unfold storeObject at hStore
  cases hStore; exact ⟨rfl, rfl⟩

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
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot ∧ st'.cdtSlotNode = st.cdtSlotNode := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact ⟨storeObject_cdt_eq st pair.2 tid.toObjId _ hStore,
             (storeObject_cdtNodeSlot_eq st pair.2 tid.toObjId _ hStore).1,
             (storeObject_cdtNodeSlot_eq st pair.2 tid.toObjId _ hStore).2⟩

/-- WS-H4: storeTcbIpcStateAndMessage preserves CDT fields. -/
private theorem storeTcbIpcStateAndMessage_cdt_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot ∧ st'.cdtSlotNode = st.cdtSlotNode := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact ⟨storeObject_cdt_eq st pair.2 tid.toObjId _ hStore,
             (storeObject_cdtNodeSlot_eq st pair.2 tid.toObjId _ hStore).1,
             (storeObject_cdtNodeSlot_eq st pair.2 tid.toObjId _ hStore).2⟩

/-- WS-H4: storeCapabilityRef preserves CDT fields. -/
theorem storeCapabilityRef_cdt_eq
    (st st' : SystemState) (ref : SlotRef) (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot ∧
    st'.cdtSlotNode = st.cdtSlotNode ∧ st'.objects = st.objects := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; exact ⟨rfl, rfl, rfl, rfl⟩

/-- S3-D: `storeCapabilityRef` preserves `cdtMapsConsistent` (CDT unchanged). -/
theorem cdtMapsConsistent_of_storeCapabilityRef
    (st st' : SystemState) (ref : SlotRef) (target : Option CapTarget)
    (hCon : cdtMapsConsistent st)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    cdtMapsConsistent st' :=
  cdtMapsConsistent_of_cdt_eq st st' hCon (storeCapabilityRef_cdt_eq st st' ref target hStep).1

/-- WS-H4: Transfer all three new predicates through a storeObject that is
not a CNode. Combines cspaceSlotCountBounded + cdtCompleteness + cdtAcyclicity. -/
private theorem cdtPredicates_of_storeObject_nonCNode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hNotCNode : ∀ cn, obj ≠ .cnode cn) :
    cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' := by
  have hCdt := storeObject_cdt_eq st st' oid obj hStore
  have ⟨hNS, _⟩ := storeObject_cdtNodeSlot_eq st st' oid obj hStore
  exact ⟨cspaceSlotCountBounded_of_storeObject_nonCNode st st' oid obj hBounded hObjInv hStore hNotCNode,
    cdtCompleteness_of_storeObject st st' oid obj hComp hObjInv hStore hNS,
    cdtAcyclicity_of_cdt_eq st st' hAcyclic hCdt⟩

/-- WS-H4: Transfer all three new predicates when objects and CDT fields are
both preserved. Used for scheduler-only updates (removeRunnable, ensureRunnable). -/
private theorem cdtPredicates_of_objects_cdtNodeSlot_eq
    (st st' : SystemState)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hObjEq : st'.objects = st.objects)
    (hCdtEq : st'.cdt = st.cdt)
    (hNodeSlotEq : st'.cdtNodeSlot = st.cdtNodeSlot) :
    cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' :=
  ⟨cspaceSlotCountBounded_of_objects_eq st st' hBounded hObjEq,
   cdtCompleteness_of_objects_nodeSlot_eq st st' hComp hObjEq hNodeSlotEq,
   cdtAcyclicity_of_cdt_eq st st' hAcyclic hCdtEq⟩

/-- WS-H4: detachSlotFromCdt preserves cdtCompleteness.
detachSlotFromCdt only clears entries from cdtNodeSlot (making the quantifier
vacuously true) and preserves objects. -/
theorem cdtCompleteness_of_detachSlotFromCdt
    (st : SystemState) (ref : SlotRef)
    (hComp : cdtCompleteness st)
    (hCdtNSK : st.cdtNodeSlot.invExtK) :
    cdtCompleteness (st.detachSlotFromCdt ref) := by
  intro nodeId slotRef hNS
  unfold SystemState.detachSlotFromCdt at hNS ⊢
  cases hLookup : st.cdtSlotNode[ref]? with
  | none => simp only [hLookup] at hNS ⊢; exact hComp nodeId slotRef hNS
  | some origNode =>
    simp only [hLookup] at hNS ⊢
    by_cases hEq : nodeId = origNode
    · subst hEq
      simp only [RHTable_getElem?_eq_get?] at hNS
      rw [RHTable_get?_erase_self st.cdtNodeSlot nodeId hCdtNSK.1] at hNS
      exact absurd hNS (by simp)
    · simp only [RHTable_getElem?_eq_get?] at hNS
      have hNeBeq : ¬((origNode == nodeId) = true) := by
        intro hBeq; exact hEq (eq_of_beq hBeq).symm
      rw [RHTable_get?_erase_ne_K st.cdtNodeSlot origNode nodeId hNeBeq hCdtNSK] at hNS
      exact hComp nodeId slotRef hNS

/-- WS-H4: detachSlotFromCdt preserves cdtAcyclicity (CDT edges unchanged). -/
theorem cdtAcyclicity_of_detachSlotFromCdt
    (st : SystemState) (ref : SlotRef)
    (hAcyclic : cdtAcyclicity st) :
    cdtAcyclicity (st.detachSlotFromCdt ref) := by
  unfold cdtAcyclicity
  show (st.detachSlotFromCdt ref).cdt.edgeWellFounded
  have : (st.detachSlotFromCdt ref).cdt = st.cdt := by
    unfold SystemState.detachSlotFromCdt; cases st.cdtSlotNode[ref]? <;> rfl
  rw [this]; exact hAcyclic

/-- WS-H4: detachSlotFromCdt preserves cspaceSlotCountBounded (objects unchanged). -/
theorem cspaceSlotCountBounded_of_detachSlotFromCdt
    (st : SystemState) (ref : SlotRef)
    (hBounded : cspaceSlotCountBounded st) :
    cspaceSlotCountBounded (st.detachSlotFromCdt ref) := by
  exact cspaceSlotCountBounded_of_objects_eq st _ hBounded
    (SystemState.detachSlotFromCdt_objects_eq st ref)

/-- WS-H4: Transfer all three new predicates through detachSlotFromCdt. -/
private theorem cdtPredicates_of_detachSlotFromCdt
    (st : SystemState) (ref : SlotRef)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hCdtNSK : st.cdtNodeSlot.invExtK) :
    cspaceSlotCountBounded (st.detachSlotFromCdt ref) ∧
    cdtCompleteness (st.detachSlotFromCdt ref) ∧
    cdtAcyclicity (st.detachSlotFromCdt ref) :=
  ⟨cspaceSlotCountBounded_of_detachSlotFromCdt st ref hBounded,
   cdtCompleteness_of_detachSlotFromCdt st ref hComp hCdtNSK,
   cdtAcyclicity_of_detachSlotFromCdt st ref hAcyclic⟩

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
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => cases hObj
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
    exact hDepth targetOid preCn hPreObj
  · rw [storeObject_objects_ne st st' targetOid cnodeId _ hEq hObjInv hStore] at hObj
    exact hDepth cnodeId cn hObj

/-- WS-H13: Transfer cspaceDepthConsistent through detachSlotFromCdt (objects unchanged). -/
theorem cspaceDepthConsistent_of_detachSlotFromCdt
    (st : SystemState) (ref : SlotRef)
    (hDepth : cspaceDepthConsistent st) :
    cspaceDepthConsistent (st.detachSlotFromCdt ref) :=
  cspaceDepthConsistent_of_objects_eq st _ hDepth
    (SystemState.detachSlotFromCdt_objects_eq st ref)

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
  simp only [CNode.remove, SeLe4n.UniqueSlotMap.get?,
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
  simp only [CNode.revokeTargetLocal, SeLe4n.UniqueSlotMap.get?,
    SeLe4n.UniqueSlotMap.filter] at hLookup
  exact SeLe4n.Kernel.RobinHood.RHTable.filter_get_subset cn.slots.table _ s cap hUniq.1 hLookup

/-- WS-H13: CNode.insert preserves depth/guardWidth/radixWidth. -/
private theorem CNode.insert_depth_eq (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).depth = cn.depth := rfl

private theorem CNode.insert_guardWidth_eq (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).guardWidth = cn.guardWidth := rfl

private theorem CNode.insert_radixWidth_eq (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).radixWidth = cn.radixWidth := rfl

/-- WS-H4: CDT-only state update preserves cspaceSlotCountBounded and cdtCompleteness.
Used for `{ st with cdt := cdt' }` where objects and cdtNodeSlot are unchanged. -/
private theorem boundedCompleteness_of_cdt_only_update
    (st : SystemState) (cdt' : CapDerivationTree)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) :
    cspaceSlotCountBounded { st with cdt := cdt' } ∧
    cdtCompleteness { st with cdt := cdt' } :=
  ⟨hBounded, hComp⟩

/-- WS-H4: Transfer WS-H4 predicates through endpoint/TCB blocking path.
storeObject(.endpoint) → storeTcbIpcState → removeRunnable preserves all three. -/
private theorem cdtPredicates_through_blocking_path
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ep : Endpoint) (ipc : ThreadIpcState)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject endpointId (.endpoint ep) st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target ipc = .ok st2) :
    cspaceSlotCountBounded (removeRunnable st2 target) ∧
    cdtCompleteness (removeRunnable st2 target) ∧
    cdtAcyclicity (removeRunnable st2 target) := by
  have hCdt1 := storeObject_cdt_eq st st1 endpointId (.endpoint ep) hStore
  have ⟨hNS1, _⟩ := storeObject_cdtNodeSlot_eq st st1 endpointId (.endpoint ep) hStore
  have ⟨hCdt2, hNS2, _⟩ := storeTcbIpcState_cdt_eq st1 st2 target ipc hTcb
  have hObjInv1 : st1.objects.invExt := storeObject_preserves_objects_invExt st st1 endpointId _ hObjInv hStore
  have hBnd1 := cspaceSlotCountBounded_of_storeObject_nonCNode st st1 endpointId (.endpoint ep)
    hBounded hObjInv hStore (fun cn h => by cases h)
  have hBnd2 := cspaceSlotCountBounded_of_storeTcbIpcState st1 st2 target ipc hBnd1 hObjInv1 hTcb
  refine ⟨?_, ?_, ?_⟩
  · exact cspaceSlotCountBounded_of_objects_eq st2 _ hBnd2 (removeRunnable_preserves_objects st2 target)
  · -- cdtCompleteness transfers through storeObject, storeTcbIpcState, removeRunnable
    -- All three only replace object entries (never delete), so objects[ref.cnode]? ≠ none is preserved
    have hComp1 := cdtCompleteness_of_storeObject st st1 endpointId (.endpoint ep) hComp hObjInv hStore hNS1
    have hComp2 : cdtCompleteness st2 := by
      unfold storeTcbIpcState at hTcb
      cases hLookup : lookupTcb st1 target with
      | none => simp [hLookup] at hTcb
      | some tcb =>
        simp only [hLookup] at hTcb
        cases hS : storeObject target.toObjId (.tcb { tcb with ipcState := ipc }) st1 with
        | error e => simp [hS] at hTcb
        | ok pair =>
          simp only [hS] at hTcb
          have hEq := Except.ok.inj hTcb; subst hEq
          exact cdtCompleteness_of_storeObject st1 pair.2 target.toObjId _ hComp1 hObjInv1 hS
            (storeObject_cdtNodeSlot_eq st1 pair.2 target.toObjId _ hS).1
    exact cdtCompleteness_of_objects_nodeSlot_eq st2 _ hComp2
      (removeRunnable_preserves_objects st2 target)
      (by simp [removeRunnable])
  · exact cdtAcyclicity_of_cdt_eq st (removeRunnable st2 target) hAcyclic
      (by show (removeRunnable st2 target).cdt = st.cdt; simp [removeRunnable]; rw [hCdt2, hCdt1])

/-- WS-H4: Transfer WS-H4 predicates through endpoint/TCB handshake path.
storeObject(.endpoint) → storeTcbIpcState → ensureRunnable preserves all three. -/
private theorem cdtPredicates_through_handshake_path
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ep : Endpoint)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject endpointId (.endpoint ep) st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target .ready = .ok st2) :
    cspaceSlotCountBounded (ensureRunnable st2 target) ∧
    cdtCompleteness (ensureRunnable st2 target) ∧
    cdtAcyclicity (ensureRunnable st2 target) := by
  have hCdt1 := storeObject_cdt_eq st st1 endpointId (.endpoint ep) hStore
  have ⟨hNS1, _⟩ := storeObject_cdtNodeSlot_eq st st1 endpointId (.endpoint ep) hStore
  have ⟨hCdt2, hNS2, _⟩ := storeTcbIpcState_cdt_eq st1 st2 target .ready hTcb
  have hObjInv1 : st1.objects.invExt := storeObject_preserves_objects_invExt st st1 endpointId _ hObjInv hStore
  have hBnd1 := cspaceSlotCountBounded_of_storeObject_nonCNode st st1 endpointId (.endpoint ep)
    hBounded hObjInv hStore (fun cn h => by cases h)
  have hBnd2 := cspaceSlotCountBounded_of_storeTcbIpcState st1 st2 target .ready hBnd1 hObjInv1 hTcb
  have hComp1 := cdtCompleteness_of_storeObject st st1 endpointId (.endpoint ep) hComp hObjInv hStore hNS1
  have hComp2 : cdtCompleteness st2 := by
    unfold storeTcbIpcState at hTcb
    cases hLookup : lookupTcb st1 target with
    | none => simp [hLookup] at hTcb
    | some tcb =>
      simp only [hLookup] at hTcb
      cases hS : storeObject target.toObjId (.tcb { tcb with ipcState := .ready }) st1 with
      | error e => simp [hS] at hTcb
      | ok pair =>
        simp only [hS] at hTcb
        have hEq := Except.ok.inj hTcb; subst hEq
        exact cdtCompleteness_of_storeObject st1 pair.2 target.toObjId _ hComp1 hObjInv1 hS
          (storeObject_cdtNodeSlot_eq st1 pair.2 target.toObjId _ hS).1
  have hEnsNS : (ensureRunnable st2 target).cdtNodeSlot = st2.cdtNodeSlot := by
    unfold ensureRunnable
    split
    · rfl
    · split
      · rfl
      · rfl
  have hEnsCdt : (ensureRunnable st2 target).cdt = st.cdt := by
    unfold ensureRunnable; split
    · rw [hCdt2, hCdt1]
    · split <;> rw [hCdt2, hCdt1]
  exact ⟨cspaceSlotCountBounded_of_objects_eq st2 _ hBnd2 (ensureRunnable_preserves_objects st2 target),
    cdtCompleteness_of_objects_nodeSlot_eq st2 _ hComp2
      (ensureRunnable_preserves_objects st2 target) hEnsNS,
    cdtAcyclicity_of_cdt_eq st _ hAcyclic hEnsCdt⟩

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
  have ⟨hCdt1, hNS1, _⟩ := storeTcbIpcStateAndMessage_cdt_eq st st1 target ipc msg hTcb
  have hBnd1 : cspaceSlotCountBounded st1 := by
    unfold storeTcbIpcStateAndMessage at hTcb
    cases hL : lookupTcb st target with
    | none => simp [hL] at hTcb
    | some tcb =>
      simp only [hL] at hTcb
      cases hS : storeObject target.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
      | error e => simp [hS] at hTcb
      | ok pair =>
        simp only [hS] at hTcb; have hEq := Except.ok.inj hTcb; subst hEq
        exact cspaceSlotCountBounded_of_storeObject_nonCNode st pair.2 target.toObjId _ hBounded hObjInv hS
          (fun cn h => by cases h)
  have hComp1 : cdtCompleteness st1 := by
    unfold storeTcbIpcStateAndMessage at hTcb
    cases hL : lookupTcb st target with
    | none => simp [hL] at hTcb
    | some tcb =>
      simp only [hL] at hTcb
      cases hS : storeObject target.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
      | error e => simp [hS] at hTcb
      | ok pair =>
        simp only [hS] at hTcb; have hEq := Except.ok.inj hTcb; subst hEq
        exact cdtCompleteness_of_storeObject st pair.2 target.toObjId _ hComp hObjInv hS
          (storeObject_cdtNodeSlot_eq st pair.2 target.toObjId _ hS).1
  have hEnsNS : (ensureRunnable st1 target).cdtNodeSlot = st1.cdtNodeSlot := by
    unfold ensureRunnable
    split
    · rfl
    · split
      · rfl
      · rfl
  have hEnsCdt : (ensureRunnable st1 target).cdt = st.cdt := by
    unfold ensureRunnable; split
    · rw [hCdt1]
    · split <;> rw [hCdt1]
  exact ⟨cspaceSlotCountBounded_of_objects_eq st1 _ hBnd1 (ensureRunnable_preserves_objects st1 target),
    cdtCompleteness_of_objects_nodeSlot_eq st1 _ hComp1
      (ensureRunnable_preserves_objects st1 target) hEnsNS,
    cdtAcyclicity_of_cdt_eq st _ hAcyclic hEnsCdt⟩
