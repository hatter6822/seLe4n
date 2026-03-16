# WS-M Workstream Plan — Capability Subsystem Audit & Remediation (v0.16.13)

**Created**: 2026-03-16
**Baseline version**: 0.16.13
**Baseline audit**: End-to-end Capability subsystem audit (5 files, 3,520 LoC)
**Prior portfolios**: WS-L (v0.16.13, complete), WS-K (v0.16.8, complete)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Audit Summary

A comprehensive end-to-end audit of the Capability subsystem was conducted covering:

- **Operations**: `Operations.lean` (740 lines) — 14 core operations + 5 multi-level
  resolution theorems
- **Invariant Definitions**: `Invariant/Defs.lean` (741 lines) — 6-tuple invariant bundle,
  transfer theorems, CDT predicate infrastructure
- **Authority**: `Invariant/Authority.lean` (634 lines) — authority reduction, badge routing,
  attenuation proofs, operation correctness lemmas
- **Preservation**: `Invariant/Preservation.lean` (1,383 lines) — per-operation invariant
  preservation, lifecycle integration, composed bundles
- **Re-export hub**: `Invariant.lean` (22 lines)

**Supporting files audited**:
- `Model/Object/Types.lean` — Capability, CNode, AccessRight, Badge, CapTarget definitions
- `Model/Object/Structures.lean` — CNode operations, CapDerivationTree, CDT operations
- `Model/State.lean` — SystemState CDT integration, storeObject, capability ref tracking
- `Kernel/API.lean` — Capability-gated syscall wrappers (lines 111–727)
- `Kernel/InformationFlow/Enforcement/Wrappers.lean` — Policy-gated capability operations

**Overall verdict**: Zero `sorry`/`axiom`. All proofs machine-checked. Zero critical
vulnerabilities. Five performance optimization opportunities. Four proof strengthening
opportunities. Three test coverage gaps. Two previously deferred items to resolve.

---

## 2. Finding Registry

### Performance Findings

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| M-P01 | MEDIUM | `Operations.lean:489–505` | `cspaceRevoke` constructs `revokedRefs` list via `HashMap.fold` then immediately passes it to `clearCapabilityRefs` which iterates again — two O(m) passes over revoked slots where one suffices. Fusing the fold with the ref-clearing would halve the work on the revoke hot path. |
| M-P02 | MEDIUM | `Structures.lean:770–780` | `CapDerivationTree.parentOf` scans the full edge list (`O(E)`) to find a node's parent. Adding a `parentMap : Std.HashMap CdtNodeId CdtNodeId` index (symmetric to `childMap`) would reduce this to `O(1)` amortized, matching the `childrenOf` optimization already present (WS-G8/F-P14). |
| M-P03 | LOW | `Structures.lean:800–815` | `CapDerivationTree.removeAsChild` and `removeAsParent` each filter the full edge list (`O(E)`) and rebuild `childMap` from scratch. With both `childMap` and a `parentMap`, these could be O(1) entry erasure + targeted list splice. |
| M-P04 | LOW | `Operations.lean:651–673` | `cspaceRevokeCdt` calls `cdt.descendantsOf` (BFS, `O(N+E)`) then iterates descendants with `foldl`. The BFS materializes the full descendant list before any deletions begin. A streaming BFS that interleaves discovery with deletion would reduce peak memory from `O(N)` to `O(queue depth)`. |
| M-P05 | LOW | `Preservation.lean:780–864` | `endpointReply_preserves_capabilityInvariantBundle` duplicates the CNode-backward-preservation proof pattern across both reply-target branches (authorized and unrestricted). Extracting a shared lemma would reduce proof term size and compilation time. |

### Proof Strengthening Findings

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| M-G01 | HIGH | `Operations.lean:198–218` | `resolveCapAddress_guard_reject` theorem proves the contrapositive (bad guard → error) but lacks the forward companion: if resolution succeeds at a leaf CNode, the guard matched. The current proof is complete and compiles with zero sorry. The strengthening opportunity is adding `resolveCapAddress_guard_match` for bidirectional guard-correctness characterization, which auditors need for full CSpace attack-surface assurance. |
| M-G02 | MEDIUM | `Invariant/Defs.lean:92–95` | `cdtCompleteness` captures node→object reachability but not the stronger mint-tracking property: "every derived capability has a CDT edge from parent to child." The current predicate is weaker than the WS-H4 spec intent (documented in the docstring). A `cdtMintCompleteness` predicate would close this gap. |
| M-G03 | MEDIUM | `Operations.lean:517–528, 535–552` | `cspaceCopy` and `cspaceMove` preservation theorems require callers to supply `hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st'` as hypotheses rather than proving these from the operation semantics. This defers the cycle-check obligation to every call site, weakening compositionality. A `addEdge_preserves_acyclicity` theorem (conditioned on the child not already being an ancestor of the parent) would allow self-contained proofs. |
| M-G04 | LOW | `Operations.lean:649–673` | `cspaceRevokeCdt` swallows `cspaceDeleteSlot` errors during descendant traversal (line 668: error branch falls through to `.ok` with CDT node removal). While `cspaceRevokeCdtStrict` provides the strict alternative, the non-strict variant should document the design rationale more explicitly, and there should be a theorem proving that any swallowed error still leaves the CDT in a consistent state (currently covered implicitly by the fold invariant, but not stated as a named theorem). |

### Test Coverage Findings

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| M-T01 | MEDIUM | `NegativeStateSuite.lean`, `OperationChainSuite.lean` | `resolveCapAddress` multi-level resolution is tested only implicitly via scenario fixtures (SCN-CSPACE-DEEP-RADIX, 12 levels). No standalone unit tests exercise edge cases: zero `radixWidth` with non-zero `guardWidth`, maximum depth (64 bits), guard mismatch at intermediate levels, or partial bit consumption leaving a non-zero remainder. |
| M-T02 | MEDIUM | `OperationChainSuite.lean` | `cspaceRevokeCdtStrict` is exercised in chain9 but only with a 3-level derivation chain. No test covers: (a) strict revocation with >10 descendants, (b) partial failure mid-traversal with `firstFailure` populated, (c) the `deletedSlots` list ordering guarantee (reverse of traversal order). |
| M-T03 | LOW | `MainTraceHarness.lean` | L-T03 (capability transfer during IPC) remains deferred from WS-L. With the Capability subsystem audit now complete, this is the appropriate workstream to model CSpace IPC integration and add the corresponding test coverage. |

### Previously Deferred Items

| ID | Origin | Description | Resolution Strategy |
|----|--------|-------------|---------------------|
| M-D01 | WS-L/L-T03 | Capability transfer during IPC — CSpace IPC integration not yet modeled | Model IPC capability transfer semantics (`endpointSendWithCaps`), prove rights attenuation through transfer, add test coverage |
| M-D02 | `Operations.lean:486–487` | `cspaceRevoke` docstring states "derivation-tree state is still out-of-scope for the active slice" but `cspaceRevokeCdt` already implements CDT traversal | Update docstring to reflect current implementation state; `cspaceRevokeCdt` resolves the deferred scope |

---

## 3. Planning Principles

1. **Proof completeness first**: Close all open proof gaps (M-G01 through M-G04) before
   adding new operations. Every theorem must be fully machine-checked.
2. **Performance on hot paths**: Address M-P01 (revoke double-pass) and M-P02 (parentOf
   linear scan) as they affect real kernel throughput.
3. **Deferred resolution**: Resolve L-T03 (capability transfer during IPC) and update
   stale docstrings, closing all known deferred items in the Capability subsystem.
4. **Self-contained proofs**: Eliminate hypothesis-deferral patterns (M-G03) where
   possible, making preservation theorems compositionally complete.
5. **Test coverage**: Fill edge-case gaps in multi-level resolution and strict revocation.
6. **Zero sorry/axiom**: Every new theorem must be fully machine-checked.
7. **Coherent slices**: Each phase independently deliverable and testable.
8. **Minimal disruption**: Preserve existing API signatures where possible; new operations
   and indices are additive.

---

## 4. Phase Overview

### Phase 1: Proof Strengthening & Correctness (WS-M1) — COMPLETED (v0.16.14)

**Focus**: Strengthen invariant coverage and proof surface completeness.
**Priority**: HIGH — proof correctness is the project's core value proposition.
**Findings addressed**: M-G01, M-G02, M-G03, M-G04, M-D02.
**Subtasks**: 10 atomic units (M1-E, M1-A1, M1-A2, M1-B1, M1-B2, M1-B3, M1-C1,
M1-C2, M1-D1, M1-D2) — each independently buildable and testable.
**Deliverables**: `resolveCapAddress_guard_match`, `cdtMintCompleteness` + transfer
theorem + extended bundle, `addEdge_preserves_edgeWellFounded_fresh` + `addEdgeWouldBeSafe`,
`cspaceRevokeCdt_swallowed_error_consistent`, docstring updates. 7 new proved declarations.

### Phase 2: Performance Optimization (WS-M2) — COMPLETED (v0.16.15)

**Focus**: Eliminate redundant traversals on CSpace hot paths.
**Priority**: HIGH — directly impacts capability operation throughput.
**Findings addressed**: M-P01, M-P02, M-P03, M-P05.
**Subtasks**: 12 atomic units across 3 tasks (M2-A1–A4, M2-B1–B8, M2-C1–C2).
**Results**: Fused `revokeAndClearRefsState` single-pass revoke, CDT `parentMap`
O(1) parent lookup, targeted `removeNode`/`removeAsChild`/`removeAsParent`, shared
reply lemma extraction, field preservation lemmas for NI proofs,
`parentMapConsistent` invariant + proofs, runtime consistency check. 12+ new
proved declarations. Zero sorry/axiom.

### Phase 3: IPC Capability Transfer (WS-M3)

**Focus**: Model and prove capability transfer during IPC, resolving L-T03.
**Priority**: MEDIUM — resolves the last deferred item from WS-L.
**Findings addressed**: M-D01, M-T03.

### Phase 4: Test Coverage Expansion (WS-M4)

**Focus**: Fill test coverage gaps for multi-level resolution and strict revocation.
**Priority**: MEDIUM — ensures edge cases are exercised.
**Findings addressed**: M-T01, M-T02.

### Phase 5: Streaming Revocation & Documentation (WS-M5)

**Focus**: Streaming BFS optimization (M-P04) and full documentation sync.
**Priority**: LOW — optimization and documentation polish.
**Findings addressed**: M-P04.

---

## 5. Detailed Phase Plans

### Phase 1: Proof Strengthening & Correctness (WS-M1)

**Target version**: 0.16.14
**Files modified**: `Operations.lean`, `Invariant/Defs.lean`, `Invariant/Authority.lean`,
`Invariant/Preservation.lean`, `Model/Object/Structures.lean`

Phase 1 is subdivided into 10 atomic subtasks across 5 findings. Each subtask is
independently buildable and testable. Tasks are ordered by dependency: M1-E (docstring)
has no proof dependencies and ships first; M1-A (guard theorem) is self-contained;
M1-B (mint completeness) is additive; M1-C (acyclicity) has the widest proof surface;
M1-D (error-swallowing) depends on existing infrastructure.

---

#### Task M1-E: Update stale `cspaceRevoke` docstring (M-D02)

**Problem**: `cspaceRevoke` (Operations.lean:484–487) docstring says "derivation-tree
state is still out-of-scope for the active slice" but `cspaceRevokeCdt` (lines 649–673)
already implements full CDT traversal. The stale comment is misleading for reviewers.

**Implementation**:
1. Replace the `cspaceRevoke` docstring (Operations.lean:484–488) with:
   ```lean
   /-- Revoke capabilities with the same target as the source in the containing CNode.

   This is the local (single-CNode) revocation variant. For cross-CNode revocation
   using CDT traversal, see `cspaceRevokeCdt` and `cspaceRevokeCdtStrict`.

   The source slot remains present and sibling slots naming the same target are removed. -/
   ```

**Verification**: `lake build` succeeds (docstring-only, no proof impact).

**Files**: `SeLe4n/Kernel/Capability/Operations.lean`

---

#### Task M1-A: Strengthen `resolveCapAddress_guard_reject` (M-G01)

**Reassessment**: The current proof (Operations.lean:198–218) compiles successfully with
zero sorry — the `simp only [hNLt, ite_false]` tactic closes all remaining goals via
let-unfolding and hypothesis matching. The finding described the proof as "incomplete"
but this was based on a surface-level reading of the tactic chain. The real strengthening
opportunity is twofold:

##### Subtask M1-A1: Add explicit guard-match extraction theorem

Add a forward-direction companion: if `resolveCapAddress` succeeds at a leaf CNode in
one hop, then the guard extracted from `addr` matched the CNode's `guardValue`. This is
the positive direction — the existing theorem proves the contrapositive (bad guard →
error). Both together give a bidirectional characterization of guard correctness.

**Implementation**:
1. In `Operations.lean`, after `resolveCapAddress_guard_reject` (line 218), add:
   ```lean
   /-- WS-H13/H-01 (M-G01): Guard match extraction — if `resolveCapAddress` succeeds
   at a leaf CNode (all bits consumed in one hop), the guard extracted from `addr`
   matched the CNode's `guardValue`. Combined with `resolveCapAddress_guard_reject`,
   this gives a full bidirectional characterization of the guard check. -/
   theorem resolveCapAddress_guard_match
       (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bits : Nat) (st : SystemState)
       (cn : CNode) (ref : SlotRef)
       (hObj : st.objects[rootId]? = some (.cnode cn))
       (hOk : resolveCapAddress rootId addr bits st = .ok ref)
       (hLeaf : bits = cn.guardWidth + cn.radixWidth) :
       (addr.toNat >>> (bits - (cn.guardWidth + cn.radixWidth))) /
         2 ^ cn.radixWidth % 2 ^ cn.guardWidth = cn.guardValue
   ```
2. Proof: unfold `resolveCapAddress`, eliminate impossible branches via `hObj` and
   `hLeaf`, then the guard mismatch branch returns `.error` which contradicts `hOk`.
   The success branch requires the guard to match, which is the conclusion.

**Verification**: `lake build` succeeds.

##### Subtask M1-A2: Add multi-level guard correctness summary docstring

Add a docstring block above the guard theorems summarizing the bidirectional
characterization (reject + match) as a coherent guard-correctness surface. This makes
the proof surface self-documenting for auditors.

**Verification**: `lake build` succeeds (docstring only).

**Files**: `SeLe4n/Kernel/Capability/Operations.lean`

---

#### Task M1-B: Add `cdtMintCompleteness` predicate (M-G02)

**Problem**: `cdtCompleteness` (Defs.lean:92–95) only captures node→object reachability.
The WS-H4 spec envisions the stronger mint-tracking property: every mint-derived
capability has a CDT edge from source to destination. This is needed to prove CDT-based
revocation exhaustiveness.

**Design decision**: Keep `cdtMintCompleteness` as a standalone predicate with its own
preservation theorems. Do NOT add it to `capabilityInvariantBundle` (which would break
60+ theorem signatures). Instead, provide a composition theorem
`capabilityInvariantBundleWithMintCompleteness` that conjoins the bundle with
`cdtMintCompleteness` for callers that need the stronger property.

##### Subtask M1-B1: Define `cdtMintCompleteness` predicate

**Implementation**:
1. In `Invariant/Defs.lean`, after `cdtAcyclicity` (line 101), add:
   ```lean
   /-- WS-H4/M-G02: Mint-tracking completeness — every CDT node pair that was created
   by a `cspaceMintWithCdt` operation has a corresponding derivation edge. This is
   stronger than `cdtCompleteness` (which only ensures node→object reachability) and
   is required for proving revocation exhaustiveness.

   Formulated as: for every CDT node that has a slot mapping, the node appears as a
   child in at least one CDT edge (i.e., it was derived from some parent), or it is a
   root node (original capability, not derived). This captures the invariant that
   `addEdge` is always called alongside `ensureCdtNodeForSlot` during mint/copy. -/
   def cdtMintCompleteness (st : SystemState) : Prop :=
     ∀ (childNode : CdtNodeId) (childRef : SlotRef),
       st.cdtNodeSlot[childNode]? = some childRef →
       (∃ edge ∈ st.cdt.edges, edge.child = childNode) ∨
       (¬∃ edge ∈ st.cdt.edges, edge.parent = childNode ∨ edge.child = childNode)
   ```
   The predicate says: every CDT node is either (a) the child of some derivation edge
   (it was derived via mint/copy), or (b) completely isolated (a root node with no
   edges referencing it). This is weaker than full bidirectional tracking but sufficient
   for revocation: `descendantsOf` traverses edges, so any node reachable via edges
   will be found.

**Verification**: `lake build` succeeds.

##### Subtask M1-B2: Prove `cdtMintCompleteness` establishment and preservation

**Implementation**:
1. In `Invariant/Defs.lean`, add an extraction theorem:
   ```lean
   theorem cdtMintCompleteness_default : cdtMintCompleteness default
   ```
   Proof: the default state has an empty CDT (`cdtNodeSlot = {}`), so the universal
   quantifier is vacuously true.

2. In `Invariant/Preservation.lean`, add preservation through non-CDT operations:
   ```lean
   theorem cdtMintCompleteness_of_cdt_edges_eq
       (st st' : SystemState)
       (hMint : cdtMintCompleteness st)
       (hEdgesEq : st'.cdt.edges = st.cdt.edges)
       (hNodeSlotEq : st'.cdtNodeSlot = st.cdtNodeSlot) :
       cdtMintCompleteness st'
   ```
   Proof: rewrite both fields and apply `hMint`.

**Verification**: `lake build` succeeds.

##### Subtask M1-B3: Compose `capabilityInvariantBundleWithMintCompleteness`

**Implementation**:
1. In `Invariant/Defs.lean`, add:
   ```lean
   /-- Extended capability invariant bundle including mint-tracking completeness.
   Provides the full 7-property assurance without changing the base 6-tuple bundle. -/
   def capabilityInvariantBundleWithMintCompleteness (st : SystemState) : Prop :=
     capabilityInvariantBundle st ∧ cdtMintCompleteness st
   ```
2. Add extraction theorems for both components.

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Kernel/Capability/Invariant/Defs.lean`,
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean`

---

#### Task M1-C: Prove `addEdge_preserves_edgeWellFounded` (M-G03)

**Problem**: `cspaceCopy`, `cspaceMove`, and `cspaceMintWithCdt` preservation theorems
require callers to supply `hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st'` as
hypotheses (Preservation.lean:322, 367, 418). This defers the CDT cycle-check obligation
to every call site. A theorem proving that `addEdge` preserves acyclicity (conditioned on
no cycle being created) would make proofs self-contained.

**Design decision**: Keep `hCdtPost` as a hypothesis in the preservation theorems. The
`addEdge_preserves_edgeWellFounded` theorem is valuable infrastructure for future phases
(M2-B parentMap, M3 IPC transfer) and for callers who want to discharge `hCdtPost`
locally. Changing the hypothesis signatures now would create unnecessary churn in this
phase — the signature change is deferred to Phase 2 (M2-B) where the CDT structure
changes anyway.

##### Subtask M1-C1: Add `addEdge_preserves_edgeWellFounded_fresh` theorem

**Implementation** (completed v0.16.14):
1. In `Model/Object/Structures.lean`, after `edgeWellFounded_sub` (line 767), add:
   ```lean
   /-- WS-H4/M-G03: Adding an edge preserves edge-well-foundedness when neither
   the parent nor the child appears in any existing edge. This covers the common case
   in kernel operations where `ensureCdtNodeForSlot` creates fresh CDT nodes. -/
   theorem addEdge_preserves_edgeWellFounded_fresh
       (cdt : CapDerivationTree) (parent child : CdtNodeId) (op : DerivationOp)
       (hNeq : parent ≠ child)
       (hAcyclic : cdt.edgeWellFounded)
       (hFreshChild : ∀ e ∈ cdt.edges, e.parent ≠ child ∧ e.child ≠ child) :
       (cdt.addEdge parent child op).edgeWellFounded
   ```

**Note**: The general `descendantsOf`-based theorem (`addEdge_preserves_edgeWellFounded`)
requires BFS completeness proof infrastructure that is deferred to Phase 2 (WS-M2).
The `_fresh` variant covers the common kernel pattern where `ensureCdtNodeForSlot`
creates nodes that don't yet participate in any edge.

2. Proof strategy:
   - Introduce the negation: suppose there exists a cyclic path in the extended CDT.
   - Case-split on whether the new edge `(parent, child)` appears in the path.
   - If not: all edges are from the original CDT → contradicts `hAcyclic`.
   - If yes: the path includes parent → child via the new edge, and child → ... →
     parent via original edges → parent ∈ cdt.descendantsOf child → contradicts
     `hNoCycle`.

**Verification**: `lake build` succeeds.

##### Subtask M1-C2: Add `addEdge` documentation and cycle-check helper

**Implementation** (completed v0.16.14):
1. In `Model/Object/Structures.lean`, after the theorem, add:
   ```lean
   /-- Runtime cycle-check: returns `true` if adding edge (parent → child) would NOT
   create a cycle. Checks parent ≠ child AND parent ∉ descendantsOf child. -/
   def addEdgeWouldBeSafe (cdt : CapDerivationTree) (parent child : CdtNodeId) : Bool :=
     parent != child && parent ∉ cdt.descendantsOf child
   ```
   Note: `parent != child` was added because `descendantsOf` uses BFS starting from
   child's neighbors, so it does not include child itself — a self-loop (parent = child)
   would not be caught by the reachability check alone.

2. **Bridge theorem deferred**: The `addEdgeWouldBeSafe_implies_preserves` bridge theorem
   requires the general `addEdge_preserves_edgeWellFounded` theorem (not the `_fresh`
   variant), which needs BFS completeness infrastructure deferred to Phase 2 (WS-M2).
   The bridge will be delivered alongside the general acyclicity theorem in M2-B.

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Model/Object/Structures.lean`

---

#### Task M1-D: Named error-swallowing consistency theorem (M-G04)

**Problem**: `cspaceRevokeCdt` (Operations.lean:649–673) swallows `cspaceDeleteSlot`
errors during descendant traversal. The existing fold proof (`revokeCdtFoldBody_preserves`
at Preservation.lean:594) implicitly covers this — the error branch calls
`capabilityInvariantBundle_of_cdt_update` — but the property is not surfaced as a named,
independently referenceable theorem.

##### Subtask M1-D1: Add named error-swallowing consistency theorem

**Implementation** (completed v0.16.14 — stronger than originally planned):
1. In `Invariant/Preservation.lean`, after `cspaceRevokeCdt_preserves_capabilityInvariantBundle`,
   add a theorem that proves three properties through the error-swallowing path:
   ```lean
   theorem cspaceRevokeCdt_swallowed_error_consistent
       (stAcc stNext : SystemState) (node : CdtNodeId)
       (descAddr : CSpaceAddr) (err : KernelError)
       (hInv : capabilityInvariantBundle stAcc)
       (hSlot : SystemState.lookupCdtSlotOfNode stAcc node = some descAddr)
       (hDelErr : cspaceDeleteSlot descAddr stAcc = .error err)
       (hStep : revokeCdtFoldBody (.ok ((), stAcc)) node = .ok ((), stNext)) :
       capabilityInvariantBundle stNext ∧
       stNext.objects = stAcc.objects ∧
       stNext.cdt.edges ⊆ stAcc.cdt.edges
   ```
   The implementation strengthens the original plan by: (a) binding through
   `revokeCdtFoldBody` directly rather than constructing the state with `{ stAcc with ... }`,
   (b) proving object stability (`stNext.objects = stAcc.objects`), and (c) proving
   edge-set monotonicity (`stNext.cdt.edges ⊆ stAcc.cdt.edges`).
2. Proof: unfold `revokeCdtFoldBody`, simplify with `hSlot`/`hDelErr`, then apply
   `capabilityInvariantBundle_of_cdt_update` + `edgeWellFounded_sub` + `removeNode_edges_sub`.

**Verification**: `lake build` succeeds.

##### Subtask M1-D2: Update `cspaceRevokeCdt` docstring with error-swallowing rationale

**Implementation**:
1. Update the `cspaceRevokeCdt` docstring (Operations.lean:641–648) to document the
   error-swallowing design rationale and reference the new consistency theorem:
   ```lean
   /-- WS-E4/C-04: Revoke all capabilities derived from the source capability
   via CDT traversal, across all CNodes in the system.

   Extends local revoke with CDT-based global traversal:
   1. Perform local revocation (same CNode siblings)
   2. Walk the CDT to find all descendants of the source slot
   3. Delete each descendant's capability from its CNode
   4. Clean up CDT edges for deleted slots

   **Error handling**: Descendant deletion errors are swallowed — the CDT node is
   removed regardless, preventing stale references. This is safe because
   `removeNode` only shrinks the edge set (proven by
   `cspaceRevokeCdt_swallowed_error_consistent`). For callers requiring error
   visibility, use `cspaceRevokeCdtStrict`. -/
   ```

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`,
`SeLe4n/Kernel/Capability/Operations.lean`

---

### Phase 2: Performance Optimization (WS-M2) — COMPLETED (v0.16.15)

**Target version**: 0.16.15
**Files modified**: `Model/State.lean`, `Operations.lean`, `Model/Object/Structures.lean`,
`Invariant/Preservation.lean`, `Invariant/Defs.lean`, `Invariant/Authority.lean`

Phase 2 is subdivided into 12 atomic subtasks across 3 tasks. Each subtask is
independently buildable and testable. Tasks are ordered by dependency: M2-C
(reply lemma extraction) is self-contained with no cross-task deps and ships
first; M2-A (fused revoke) modifies Operations.lean + State.lean; M2-B
(parentMap) has the widest blast radius due to structure change propagation.

---

#### Task M2-A: Fuse revoke fold with capability ref clearing (M-P01)

**Problem**: `cspaceRevoke` (Operations.lean:539–556) constructs a `revokedRefs` list
by folding over the CNode's `HashMap` (O(m)), then passes this list to
`clearCapabilityRefs` which iterates over it again (O(m)). This is two O(m) passes
where m is the number of revoked slots. On a CNode with many same-target siblings,
this doubles the work on the revoke hot path.

**Root cause analysis**: The two-pass pattern exists because `clearCapabilityRefsState`
(State.lean:260–269) is a recursive function that processes a pre-built `List SlotRef`,
while the revoked-refs collection is a `HashMap.fold`. Fusing these requires a single
`HashMap.fold` that performs both the match check AND the ref erasure in each iteration.

**Design decision**: Keep the existing `clearCapabilityRefsState` and `clearCapabilityRefs`
unchanged (they are used by other operations and have 15+ existing preservation theorems).
Instead, introduce a fused helper alongside the existing functions, with an equivalence
theorem bridging the two representations. This avoids cross-subsystem churn.

##### Subtask M2-A1: Define `revokeAndClearRefsState` fused helper

**Implementation**:
1. In `Model/State.lean`, after `clearCapabilityRefs` (line 273), add:
   ```lean
   /-- M-P01: Fused revoke — filter CNode slots matching the revoke target and clear
   their capability refs in a single HashMap.fold pass, eliminating the intermediate
   `revokedRefs` list allocation and the second O(m) traversal through
   `clearCapabilityRefsState`. -/
   def revokeAndClearRefsState
       (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
       (cnodeId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
     cn.slots.fold (fun stAcc s c =>
       if s != sourceSlot && c.target == target then
         { stAcc with lifecycle := { stAcc.lifecycle with
             capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
               { cnode := cnodeId, slot := s } } }
       else stAcc) st
   ```

**Verification**: `lake build` succeeds (definition only, no dependents yet).

**Files**: `SeLe4n/Model/State.lean`

##### Subtask M2-A2: Prove `revokeAndClearRefsState` preserves non-lifecycle fields

**Implementation**:
1. In `Model/State.lean`, after the fused helper, add field-preservation theorems
   matching the existing `clearCapabilityRefsState_preserves_*` family:
   ```lean
   theorem revokeAndClearRefsState_preserves_objects
       (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
       (cnodeId : SeLe4n.ObjId) (st : SystemState) :
       (revokeAndClearRefsState cn sourceSlot target cnodeId st).objects = st.objects

   theorem revokeAndClearRefsState_preserves_scheduler
       (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
       (cnodeId : SeLe4n.ObjId) (st : SystemState) :
       (revokeAndClearRefsState cn sourceSlot target cnodeId st).scheduler = st.scheduler

   theorem revokeAndClearRefsState_cdt_eq
       (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
       (cnodeId : SeLe4n.ObjId) (st : SystemState) :
       (revokeAndClearRefsState cn sourceSlot target cnodeId st).cdt = st.cdt ∧
       (revokeAndClearRefsState cn sourceSlot target cnodeId st).cdtNodeSlot = st.cdtNodeSlot ∧
       (revokeAndClearRefsState cn sourceSlot target cnodeId st).cdtSlotNode = st.cdtSlotNode ∧
       (revokeAndClearRefsState cn sourceSlot target cnodeId st).objects = st.objects
   ```
   Proof strategy: induction on `HashMap.fold` — each step only modifies
   `lifecycle.capabilityRefs`, leaving all other fields unchanged.

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Model/State.lean`

##### Subtask M2-A3: Update `cspaceRevoke` to use fused single-pass path

**Implementation**:
1. In `Operations.lean`, replace the two-pass pattern in `cspaceRevoke` (lines 547–555):
   ```lean
   -- BEFORE (two passes):
   -- let revokedRefs := cn.slots.fold (fun acc s c => ...) []
   -- match storeObject ... with
   -- | .ok (_, st'') => clearCapabilityRefs revokedRefs st''

   -- AFTER (single pass):
   -- match storeObject ... with
   -- | .ok (_, st'') =>
   --     .ok ((), revokeAndClearRefsState cn addr.slot parent.target addr.cnode st'')
   ```
   The `revokedRefs` list construction is eliminated entirely. The fused helper
   performs the equivalent work inside its fold body.

**Verification**: `lake build` succeeds. Existing tests pass (semantically equivalent).

**Files**: `SeLe4n/Kernel/Capability/Operations.lean`

##### Subtask M2-A4: Update `cspaceRevoke` preservation proof for fused path

**Implementation**:
1. In `Invariant/Preservation.lean`, update `cspaceRevoke_preserves_capabilityInvariantBundle`
   (lines 226–307). The proof structure changes because `clearCapabilityRefs` is replaced
   by `revokeAndClearRefsState`. The key proof obligations remain identical:
   - CNode uniqueness: through `storeObject` + fused helper (objects unchanged)
   - Bounded/completeness/acyclicity: through CDT field preservation of fused helper
   Replace references to `clearCapabilityRefs_preserves_objects` with
   `revokeAndClearRefsState_preserves_objects`, and `clearCapabilityRefs_cdt_eq`
   with `revokeAndClearRefsState_cdt_eq`.

2. In `Invariant/Authority.lean`, update the two `cspaceRevoke` authority lemmas
   (lines 86–89, 243–246) that reference `clearCapabilityRefs_preserves_objects`.
   Replace with `revokeAndClearRefsState_preserves_objects`.

**Verification**: `lake build` succeeds. `test_full.sh` passes.

**Files**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`,
`SeLe4n/Kernel/Capability/Invariant/Authority.lean`

**Performance impact**: Eliminates one O(m) pass and one `List SlotRef` allocation
on every `cspaceRevoke` call. The revoke hot path does a single `HashMap.fold`
instead of fold + recursive list traversal.

---

#### Task M2-B: Add CDT `parentMap` index (M-P02, M-P03)

**Problem**: `CapDerivationTree.parentOf` (Structures.lean:676–678) uses `List.find?`
to scan the full edge list (`O(E)`) for a node's parent. `removeAsChild`
(Structures.lean:682–687) filters the entire edge list AND rebuilds `childMap`
from scratch via `HashMap.fold`. `removeAsParent` (Structures.lean:691–694) also
filters the full edge list. With `childMap` already providing O(1) child lookup
(WS-G8/F-P14), a symmetric `parentMap : Std.HashMap CdtNodeId CdtNodeId` would
complete the O(1) picture for both directions.

**Design constraints**:
- CDT is a forest (each child has at most one parent), so `parentMap` maps
  `child → parent` (not `child → List parent` like childMap's inverse).
- The `edges` list remains the proof anchor. Both `childMap` and `parentMap` are
  runtime indices with consistency invariants linking them to `edges`.
- `CapDerivationTree` has exactly one construction site (`.empty`) and is modified
  only through `addEdge`, `removeAsChild`, `removeAsParent`, and `removeNode`.
  The `{ st with cdt := cdt' }` pattern in Preservation.lean constructs CDTs
  indirectly via these operations.

##### Subtask M2-B1: Add `parentMap` field to `CapDerivationTree`

**Implementation**:
1. In `Structures.lean`, extend the structure (line 649–655):
   ```lean
   structure CapDerivationTree where
     edges : List CapDerivationEdge := []
     /-- WS-G8/F-P14: Parent-indexed child map for O(1) `childrenOf` lookup. -/
     childMap : Std.HashMap CdtNodeId (List CdtNodeId) := {}
     /-- M-P02: Child-indexed parent map for O(1) `parentOf` lookup.
     Maps each child node to its unique parent. Symmetric to `childMap`. -/
     parentMap : Std.HashMap CdtNodeId CdtNodeId := {}
     deriving Repr
   ```
2. Update `empty` (line 659):
   ```lean
   def empty : CapDerivationTree := { edges := [], childMap := {}, parentMap := {} }
   ```

**Breaking change note**: Adding a field with a default value (`{}`) means existing
`CapDerivationTree` construction via named fields will compile without changes
(Lean 4 uses the default for omitted fields). However, any pattern match or
structure literal that explicitly lists fields will need updating.

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Model/Object/Structures.lean`

##### Subtask M2-B2: Update `addEdge` to maintain `parentMap`

**Implementation**:
1. In `Structures.lean`, update `addEdge` (lines 663–667):
   ```lean
   def addEdge (cdt : CapDerivationTree) (parent child : CdtNodeId)
       (op : DerivationOp) : CapDerivationTree :=
     let currentChildren := cdt.childMap.get? parent |>.getD []
     { edges := { parent, child, op } :: cdt.edges,
       childMap := cdt.childMap.insert parent (child :: currentChildren),
       parentMap := cdt.parentMap.insert child parent }
   ```
   Cost: one additional `HashMap.insert` — O(1) amortized.

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Model/Object/Structures.lean`

##### Subtask M2-B3: Rewrite `parentOf` to use `parentMap` (O(E) → O(1))

**Implementation**:
1. In `Structures.lean`, replace `parentOf` (lines 676–678):
   ```lean
   /-- Find the parent of a given node, if any.
   M-P02: O(1) lookup via `parentMap` instead of O(E) edge scan. -/
   def parentOf (cdt : CapDerivationTree) (node : CdtNodeId)
       : Option CdtNodeId :=
     cdt.parentMap[node]?
   ```

**Performance impact**: `parentOf` goes from O(E) linear scan to O(1) hash lookup.

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Model/Object/Structures.lean`

##### Subtask M2-B4: Update `removeAsChild` for targeted `parentMap` erasure

**Implementation**:
1. In `Structures.lean`, replace `removeAsChild` (lines 682–687):
   ```lean
   /-- Remove all edges referencing a given node as child (detach from parent).
   M-P03: Uses targeted `parentMap.erase` + `childMap` splice instead of
   full edge-list filter + childMap rebuild. -/
   def removeAsChild (cdt : CapDerivationTree) (node : CdtNodeId)
       : CapDerivationTree :=
     let parentNode? := cdt.parentMap[node]?
     let childMap' := match parentNode? with
       | some p =>
         let siblings := (cdt.childMap.get? p).getD []
         let filtered := siblings.filter (· != node)
         if filtered.isEmpty then cdt.childMap.erase p else cdt.childMap.insert p filtered
       | none => cdt.childMap
     { edges := cdt.edges.filter (fun e => ¬e.isChildOf node),
       childMap := childMap',
       parentMap := cdt.parentMap.erase node }
   ```
   The `edges` list is still filtered (proof anchor), but `childMap` update is
   now a targeted splice of the parent's child list instead of a full rebuild.
   `parentMap` update is a single `erase`.

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Model/Object/Structures.lean`

##### Subtask M2-B5: Update `removeAsParent` and `removeNode` for `parentMap`

**Implementation**:
1. In `Structures.lean`, update `removeAsParent` (lines 691–694):
   ```lean
   def removeAsParent (cdt : CapDerivationTree) (node : CdtNodeId)
       : CapDerivationTree :=
     let children := (cdt.childMap.get? node).getD []
     let parentMap' := children.foldl (fun m c => m.erase c) cdt.parentMap
     { edges := cdt.edges.filter (fun e => ¬e.isParentOf node),
       childMap := cdt.childMap.erase node,
       parentMap := parentMap' }
   ```
   Each child of the removed parent has its `parentMap` entry erased.

2. Update `removeNode` (lines 698–705):
   ```lean
   def removeNode (cdt : CapDerivationTree) (node : CdtNodeId)
       : CapDerivationTree :=
     -- Phase 1: Remove as parent (erase children's parentMap entries + own childMap entry)
     let children := (cdt.childMap.get? node).getD []
     let parentMapWithoutChildren := children.foldl (fun m c => m.erase c) cdt.parentMap
     -- Phase 2: Remove as child (erase own parentMap entry + splice parent's childMap)
     let parentMapFinal := parentMapWithoutChildren.erase node
     let parentNode? := cdt.parentMap[node]?
     let childMapWithoutSelf := cdt.childMap.erase node
     let childMapFinal := match parentNode? with
       | some p =>
         let siblings := (childMapWithoutSelf.get? p).getD []
         let filtered := siblings.filter (· != node)
         if filtered.isEmpty then childMapWithoutSelf.erase p
         else childMapWithoutSelf.insert p filtered
       | none => childMapWithoutSelf
     -- Phase 3: Filter edges (proof anchor)
     let edgesFiltered := cdt.edges.filter
       (fun e => ¬e.isParentOf node ∧ ¬e.isChildOf node)
     { edges := edgesFiltered, childMap := childMapFinal, parentMap := parentMapFinal }
   ```

**Performance impact**: `removeNode` childMap update goes from O(E) full rebuild
to O(children.length) targeted splice. `parentMap` updates are O(children.length)
erasures.

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Model/Object/Structures.lean`

##### Subtask M2-B6: Define `parentMapConsistent` invariant and prove for `empty`

**Implementation**:
1. In `Structures.lean`, after `childMapConsistent` (line 862), add:
   ```lean
   /-- M-P02: Consistency invariant — `parentMap` mirrors the child→parent
   relationship in `edges`. Each child has at most one parent (forest property). -/
   def parentMapConsistent (cdt : CapDerivationTree) : Prop :=
     ∀ child parent,
       cdt.parentMap[child]? = some parent ↔
         ∃ e ∈ cdt.edges, e.parent = parent ∧ e.child = child

   theorem empty_parentMapConsistent : CapDerivationTree.empty.parentMapConsistent := by
     intro child parent
     simp only [CapDerivationTree.empty]
     constructor
     · intro h; rw [HashMap_get?_empty] at h; cases h
     · rintro ⟨_, hMem, _⟩; cases hMem
   ```

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Model/Object/Structures.lean`

##### Subtask M2-B7: Prove `parentMapConsistent` preservation for `addEdge` and `removeNode`

**Implementation**:
1. Prove `addEdge_parentMapConsistent`:
   ```lean
   theorem addEdge_parentMapConsistent
       (cdt : CapDerivationTree) (p c : CdtNodeId) (op : DerivationOp)
       (hCons : cdt.parentMapConsistent)
       (hFresh : cdt.parentMap[c]? = none) :
       (cdt.addEdge p c op).parentMapConsistent
   ```
   Proof: case split on whether `child' = c` (the new child). If yes, the
   `HashMap.insert` gives `some p`, matching the new edge. If no, the insert
   doesn't affect `child'`'s entry, and the old edges + old `parentMap` agree
   by `hCons`. The `hFresh` hypothesis ensures no duplicate parent assignment.

2. Prove `removeNode_parentMapConsistent`:
   ```lean
   theorem removeNode_parentMapConsistent
       (cdt : CapDerivationTree) (node : CdtNodeId)
       (hCons : cdt.parentMapConsistent) :
       (cdt.removeNode node).parentMapConsistent
   ```
   Proof: the filtered edges exclude `node` as parent or child. The parentMap
   erases `node` and all children of `node`. By `hCons`, every remaining
   parentMap entry corresponds to a surviving edge.

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Model/Object/Structures.lean`

##### Subtask M2-B8: Update `edgeWellFounded` proofs for new `parentMap` field

**Implementation**:
1. `edgeWellFounded_sub` (line 759–767): No change needed — it only references
   `cdt.edges` and `cdt'.edges`, not `childMap` or `parentMap`.
2. `addEdge_preserves_edgeWellFounded_fresh` (lines 787–849): Update the
   `simp only [addEdge]` step to account for the new `parentMap` field in the
   `addEdge` unfolding. The proof logic is unchanged — it only reasons about
   edge membership, not map contents.
3. `removeNode_edges_sub` (lines 770–774): No change needed — operates on edges only.

**Verification**: `lake build` succeeds. `test_full.sh` passes.

**Files**: `SeLe4n/Model/Object/Structures.lean`

---

#### Task M2-C: Extract shared reply-preservation lemma (M-P05)

**Problem**: `endpointReply_preserves_capabilityInvariantBundle` (Preservation.lean:
807–888) factors the shared proof body via `suffices` (line 836), but the two
dispatch branches (authorized at lines 839–848, unrestricted at lines 851–859)
still duplicate the `revert`/`cases`/`simp`/`exact this` pattern. Additionally,
the CNode backward-preservation proof (lines 862–876) and the full invariant
reconstruction (lines 877–888) are valuable infrastructure that other reply-like
operations (e.g., M3 IPC transfer reply path) will need.

**Design decision**: Extract the `suffices` body into a named private theorem.
This makes it independently referenceable for M3 (IPC capability transfer) and
reduces the main reply theorem to a thin dispatch wrapper. The two branch
patterns remain in the main theorem (they are short after extraction) but now
just call the extracted lemma instead of inlining the full proof.

##### Subtask M2-C1: Extract `capabilityInvariantBundle_of_storeTcbAndEnsureRunnable`

**Implementation**:
1. In `Invariant/Preservation.lean`, before `endpointReply_preserves_capabilityInvariantBundle`
   (line 807), add:
   ```lean
   /-- M-P05: Shared reply-path infrastructure — if `storeTcbIpcStateAndMessage`
   succeeds and CNodes are backward-preserved (TCB store doesn't modify CNode
   objects), then `ensureRunnable` on the result preserves the capability bundle.

   Extracted from `endpointReply_preserves_capabilityInvariantBundle` to eliminate
   ~40 lines of duplicated proof across the authorized/unrestricted reply branches.
   Also provides reusable infrastructure for M3 (IPC capability transfer). -/
   private theorem capabilityInvariantBundle_of_storeTcbAndEnsureRunnable
       (st st' : SystemState) (target : SeLe4n.ThreadId)
       (ipc : ThreadIpcState) (msg : Option IpcMessage)
       (hInv : capabilityInvariantBundle st)
       (hTcb : storeTcbIpcStateAndMessage st target ipc msg = .ok st')
       (hLookup : lookupTcb st target = some tcb) :
       capabilityInvariantBundle (ensureRunnable st' target)
   ```
   Proof: the body is exactly the current `suffices` proof (lines 861–888),
   with `hCnodeBackward` derived from `hLookup` + `storeTcbIpcStateAndMessage`
   preservation lemmas.

**Verification**: `lake build` succeeds.

##### Subtask M2-C2: Rewrite `endpointReply_preserves_capabilityInvariantBundle`

**Implementation**:
1. Replace the `suffices` block and shared proof body (lines 836–888) with:
   ```lean
   suffices ∀ st1, storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st1 →
       capabilityInvariantBundle (ensureRunnable st1 target) by
     <dispatch to both branches unchanged>
   intro st1 hTcb
   exact capabilityInvariantBundle_of_storeTcbAndEnsureRunnable
     st st1 target .ready (some msg) ⟨hUnique, _, hBounded, hComp, hAcyclic, hDepthPre⟩
     hTcb hLookup
   ```
   This eliminates the inline CNode backward proof and invariant reconstruction,
   replacing ~27 lines with a single `exact` call.

**Verification**: `lake build` succeeds. `test_smoke.sh` passes.

**Files**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`

---

#### M2 Dependency Graph and Execution Order

```
M2-C1 (extract reply lemma)  ─── no deps (self-contained)
M2-C2 (rewrite reply thm)    ─── depends on M2-C1
M2-A1 (fused helper def)     ─── no deps (State.lean only)
M2-A2 (fused preservation)   ─── depends on M2-A1
M2-A3 (update cspaceRevoke)  ─── depends on M2-A1
M2-A4 (update proofs)        ─── depends on M2-A2, M2-A3
M2-B1 (parentMap field)      ─── no deps (Structures.lean only)
M2-B2 (update addEdge)       ─── depends on M2-B1
M2-B3 (rewrite parentOf)     ─── depends on M2-B1
M2-B4 (update removeAsChild) ─── depends on M2-B1
M2-B5 (update removeAsParent/removeNode) ─── depends on M2-B1
M2-B6 (parentMapConsistent)  ─── depends on M2-B1
M2-B7 (consistency proofs)   ─── depends on M2-B2, M2-B5, M2-B6
M2-B8 (edgeWellFounded fixup)─── depends on M2-B2
```

**Optimal execution order**: M2-C1 → M2-C2 → M2-A1 → M2-A2 → M2-A3 → M2-A4 →
M2-B1 → {M2-B2, M2-B3, M2-B4, M2-B5, M2-B6} (parallel) → M2-B7 → M2-B8.
Total: 12 subtasks, 8 sequential steps.

**Deliverables**: `revokeAndClearRefsState` fused helper + 4 preservation theorems,
`capabilityInvariantBundle_of_storeTcbAndEnsureRunnable` extracted lemma,
`parentMap` field + O(1) `parentOf` + `parentMapConsistent` invariant + 3
consistency theorems. ~6 new proved declarations; zero sorry/axiom.

---

### Phase 3: IPC Capability Transfer (WS-M3)

**Target version**: 0.17.2
**Files modified**: `Model/Object/Types.lean`, `Kernel/IPC/Operations/Endpoint.lean`,
`Kernel/Capability/Operations.lean`, `Kernel/Capability/Invariant/Preservation.lean`,
`Kernel/API.lean`

This phase resolves the last deferred item from WS-L (L-T03): capability transfer
during IPC. In seL4, `seL4_Send`/`seL4_Call` can include extra capabilities in the
message that are unwrapped at the receiver's CSpace. This is the mechanism by which
a server can receive capabilities from a client.

#### Task M3-A: Model IPC capability transfer types

**Problem**: `IpcMessage` currently carries `caps : List Capability` but there is no
operation that actually transfers capabilities between CSpaces during IPC. The caps
field is populated but never unwrapped into the receiver's CNode.

**Implementation**:
1. In `Model/Object/Types.lean`, define:
   ```lean
   /-- Result of attempting to unwrap a transferred capability into the receiver's CSpace. -/
   inductive CapTransferResult where
     | inserted : SlotRef → CapTransferResult  -- successfully placed in receiver slot
     | noSlot : CapTransferResult              -- no empty slot in receiver's CNode
     | attenuationFailed : CapTransferResult   -- rights check failed
     deriving Repr, DecidableEq
   ```
2. In `Kernel/Capability/Operations.lean`, define:
   ```lean
   /-- Transfer a capability from the sender's message into the receiver's CSpace.

   The transferred capability is attenuated to the intersection of:
   - The sender's rights on the capability
   - The receiver's rights on the receiving endpoint capability

   This prevents privilege escalation through IPC: the receiver cannot gain
   more authority than both the sender intended and the endpoint grants.

   The destination slot is the first empty slot in the receiver's CSpace root CNode
   starting from `receiverSlotBase`. -/
   def ipcTransferCap
       (senderCap : Capability)
       (receiverRootId : SeLe4n.ObjId)
       (receiverSlotBase : SeLe4n.Slot)
       (endpointRights : AccessRightSet) : Kernel CapTransferResult
   ```
3. Define the slot-scanning helper that finds the first empty slot:
   ```lean
   /-- Find the first empty slot in a CNode starting from `base`, searching up to
   `limit` consecutive slots. Returns `none` if all slots are occupied. -/
   def findFirstEmptySlot (cn : CNode) (base : SeLe4n.Slot) (limit : Nat) :
       Option SeLe4n.Slot
   ```

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Model/Object/Types.lean`,
`SeLe4n/Kernel/Capability/Operations.lean`

#### Task M3-B: Integrate capability transfer into IPC send path

**Problem**: `endpointSendDual` and `endpointCallDual` do not unwrap message
capabilities into the receiver's CSpace.

**Implementation**:
1. Define `endpointSendWithCaps` that extends the send path:
   - After message delivery to the receiver TCB, iterate over `msg.caps`
   - For each cap, call `ipcTransferCap` with the receiver's CSpace root
   - Record transfer results in an extended return type
2. Prove deterministic semantics (each step is explicit success/failure).
3. Prove capability attenuation: transferred caps have rights ⊆ sender rights ∩ endpoint rights.

**Key theorem**:
```lean
theorem ipcTransferCap_attenuates
    (senderCap : Capability) (rootId : SeLe4n.ObjId)
    (base : SeLe4n.Slot) (epRights : AccessRightSet)
    (st st' : SystemState) (result : CapTransferResult)
    (hStep : ipcTransferCap senderCap rootId base epRights st = .ok (result, st')) :
    match result with
    | .inserted ref =>
        ∃ cap, SystemState.lookupSlotCap st' ref = some cap ∧
          (∀ r, r ∈ cap.rights → r ∈ senderCap.rights ∧ r ∈ epRights)
    | _ => True
```

**Verification**: `lake build` succeeds. Run `test_smoke.sh`.

**Files**: `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`,
`SeLe4n/Kernel/Capability/Operations.lean`

#### Task M3-C: Prove invariant preservation for capability transfer

**Implementation**:
1. Prove `ipcTransferCap_preserves_capabilityInvariantBundle` — the transfer is
   a `cspaceInsertSlot` (already proven) conditioned on finding an empty slot.
2. Prove `endpointSendWithCaps_preserves_capabilityInvariantBundle` by composing
   the per-cap transfer preservation over the cap list.
3. Prove badge well-formedness preservation.
4. Update `coreIpcInvariantBundle` preservation if the send path changes.

**Verification**: `lake build` succeeds. Run `test_full.sh`.

**Files**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`,
`SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean`

#### Task M3-D: Add IPC capability transfer test coverage (M-T03)

**Implementation**:
1. In `tests/OperationChainSuite.lean`, add a new chain that:
   - Creates a sender with capabilities in its CSpace
   - Creates a receiver with an endpoint capability
   - Sender sends a message with extra caps
   - Receiver's CSpace gains the transferred capabilities
   - Verify rights attenuation (transferred rights ⊆ sender ∩ endpoint)
   - Verify badge propagation through transfer
2. Add negative test in `NegativeStateSuite.lean`:
   - Transfer to full CNode (no empty slots) → `noSlot` result
   - Transfer with insufficient endpoint rights → `attenuationFailed`
3. Update `tests/fixtures/main_trace_smoke.expected` if trace output changes.

**Verification**: `test_smoke.sh` passes. Fixture matches.

**Files**: `tests/OperationChainSuite.lean`, `tests/NegativeStateSuite.lean`,
`SeLe4n/Testing/MainTraceHarness.lean`

---

### Phase 4: Test Coverage Expansion (WS-M4)

**Target version**: 0.17.3
**Files modified**: `tests/OperationChainSuite.lean`, `tests/NegativeStateSuite.lean`,
`SeLe4n/Testing/MainTraceHarness.lean`

#### Task M4-A: Multi-level resolution edge case tests (M-T01)

**Problem**: `resolveCapAddress` is tested only implicitly via 12-level scenario
fixtures. No standalone tests cover edge cases.

**Implementation**:
1. Add to `NegativeStateSuite.lean`:
   - **M4-A1**: Zero `radixWidth` with non-zero `guardWidth` — verify guard-only
     CNodes resolve correctly (slot index always 0).
   - **M4-A2**: Maximum depth (64 bits) — create a CNode chain consuming exactly
     64 bits across multiple hops, verify resolution succeeds.
   - **M4-A3**: Guard mismatch at intermediate level — create a 3-level chain where
     the middle CNode has a wrong guard, verify `.error .invalidCapability`.
   - **M4-A4**: Partial bit consumption — `bitsRemaining` is not a multiple of
     `guardWidth + radixWidth`, verify `.error .illegalState` when bits run out
     mid-level.
   - **M4-A5**: Single-level resolution (bits consumed in one hop) — verify leaf
     case returns correct `SlotRef`.
2. Add scenario IDs: `SCN-RESOLVE-GUARD-ONLY`, `SCN-RESOLVE-MAX-DEPTH`,
   `SCN-RESOLVE-GUARD-MISMATCH-MID`, `SCN-RESOLVE-PARTIAL-BITS`,
   `SCN-RESOLVE-SINGLE-LEVEL`.

**Verification**: `test_smoke.sh` passes.

**Files**: `tests/NegativeStateSuite.lean`

#### Task M4-B: Strict revocation stress tests (M-T02)

**Problem**: `cspaceRevokeCdtStrict` is exercised only with 3-level derivation chains.

**Implementation**:
1. Add to `OperationChainSuite.lean`:
   - **M4-B1**: Strict revocation with 15+ descendants in a deep chain — verify
     all descendants are deleted and `deletedSlots` list is complete.
   - **M4-B2**: Strict revocation with partial failure — set up a state where
     one descendant's CNode has been deleted (object not found), verify
     `firstFailure` is populated with the correct `offendingNode`, `offendingSlot`,
     and `error`, and that `deletedSlots` contains only the successfully deleted
     slots before the failure.
   - **M4-B3**: `deletedSlots` ordering — verify the returned list is in
     BFS traversal order (reversed by the fold, then re-reversed by the final
     `.reverse` call at line 738).
2. Add scenario IDs: `SCN-REVOKE-STRICT-DEEP`, `SCN-REVOKE-STRICT-PARTIAL-FAIL`,
   `SCN-REVOKE-STRICT-ORDER`.

**Verification**: `test_smoke.sh` passes.

**Files**: `tests/OperationChainSuite.lean`

---

### Phase 5: Streaming Revocation & Documentation (WS-M5)

**Target version**: 0.17.4
**Files modified**: `Operations.lean`, `Invariant/Preservation.lean`, all documentation

#### Task M5-A: Streaming BFS for CDT revocation (M-P04)

**Problem**: `cspaceRevokeCdt` materializes the full descendant list before beginning
deletions. For large derivation trees, this allocates O(N) memory for the descendant
list while the BFS queue itself is much smaller.

**Implementation**:
1. Define `streamingRevokeCdt` that interleaves BFS discovery with deletion:
   ```lean
   /-- Streaming CDT revocation: interleaves BFS discovery with deletion.

   Instead of materializing all descendants first, processes nodes level-by-level:
   1. Initialize queue with direct children of the source CDT node
   2. For each node in the queue:
      a. Look up the node's slot and delete the capability
      b. Add the node's children to the queue
      c. Remove the CDT node
   3. Continue until queue is empty

   Termination: each step removes a CDT node, strictly shrinking the tree.
   The fuel parameter bounds the total number of steps. -/
   def cspaceRevokeCdtStreaming (addr : CSpaceAddr) : Kernel Unit
   ```
2. Prove semantic equivalence with `cspaceRevokeCdt` (same final state for
   acyclic CDTs).
3. Prove `cspaceRevokeCdtStreaming_preserves_capabilityInvariantBundle`.

**Performance impact**: Peak memory goes from O(N) (full descendant list) to
O(max branching factor × depth) (BFS queue).

**Verification**: `lake build` succeeds. Run `test_full.sh`.

**Files**: `SeLe4n/Kernel/Capability/Operations.lean`,
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean`

#### Task M5-B: Documentation synchronization

**Implementation**:
1. **WORKSTREAM_HISTORY.md**: Add WS-M workstream entry with phase summary,
   finding registry link, and completion status for each phase.
2. **CLAIM_EVIDENCE_INDEX.md**: Update capability-related claims:
   - Add M-G01 guard-reject proof completion as evidence
   - Add `cdtMintCompleteness` as new claim
   - Add `addEdge_preserves_acyclicity` as evidence for CDT soundness
   - Add IPC capability transfer as new claim with evidence
3. **DEVELOPMENT.md**: Add development notes for WS-M phases.
4. **docs/spec/SELE4N_SPEC.md**: Update capability subsystem specification:
   - Add IPC capability transfer semantics
   - Update invariant bundle description (cdtMintCompleteness)
   - Update CDT operations (parentMap)
5. **GitBook chapters**:
   - `03-architecture-and-module-map.md`: Add IPC capability transfer to CSpace section
   - `04-project-design-deep-dive.md`: Update CDT model (parentMap), add IPC transfer
   - `05-specification-and-roadmap.md`: Update capability operations spec
   - `07-testing-and-ci.md`: Document new test scenarios
   - `08-kernel-performance-optimization.md`: Document M2 optimizations
   - `11-codebase-reference.md`: Update capability module reference
   - `12-proof-and-invariant-map.md`: Add new theorems (M-G01–G04, M3 transfer)
6. **docs/codebase_map.json**: Regenerate after all code changes.
7. **README.md**: Sync metrics from `docs/codebase_map.json`.

**Verification**: `test_full.sh` passes. `test_docs_sync.sh` passes.

**Files**: All documentation files listed above.

---

## 6. Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| M1-C1 (`addEdge_preserves_edgeWellFounded`) proof is harder than expected due to BFS fuel and path decomposition | Medium | Delays Phase 1 | Fall back to explicit `descendantsOf` induction; keep `hCdtPost` hypothesis pattern as escape hatch; M1-C2 cycle-check helper is independent |
| M2-B (`parentMap`) breaks CDT construction sites across codebase | Low | Mechanical churn | Use `grep` to find all `CapDerivationTree` construction sites; update in single pass |
| M3-A/B (IPC cap transfer) requires IPC subsystem changes that conflict with WS-L proofs | Medium | Cross-subsystem churn | Limit changes to additive new operations; do not modify existing `endpointSendDual` |
| M3-C (transfer preservation) depends on `cspaceInsertSlot` preservation + slot-scanning termination | Low | Proof complexity | Slot scanning has bounded iteration (CNode radixWidth); termination is structural |
| M5-A (streaming BFS) termination proof requires CDT shrinking argument | Medium | Proof complexity | Use fuel = initial edge count; prove each step removes ≥1 edge |

---

## 7. Success Criteria

1. **Zero sorry/axiom** in all new and modified proof surfaces.
2. All findings (M-P01 through M-P05, M-G01 through M-G04, M-T01 through M-T03,
   M-D01, M-D02) resolved or documented with rationale if deferred.
3. `test_full.sh` passes after each phase.
4. All documentation synchronized after Phase 5.
5. `capabilityInvariantBundle` preservation proven for all operations including
   IPC capability transfer.
6. CDT operations have O(1) parent lookup (parentMap) and O(1) child lookup (childMap).
7. L-T03 (capability transfer during IPC) fully modeled, proven, and tested.

---

## 8. Dependency Graph

```
                                Phase 1 Internal Dependencies
                                ────────────────────────────
M1-E (docstring)          ─── no deps (ships first)
M1-A1 (guard match thm)  ─── no deps (self-contained)
M1-A2 (guard docstring)  ─── depends on M1-A1
M1-B1 (mint predicate)   ─── no deps (additive definition)
M1-B2 (mint preservation)─── depends on M1-B1
M1-B3 (mint composition) ─── depends on M1-B1
M1-C1 (addEdge acycl.)   ─── no deps (Structures.lean only)
M1-C2 (cycle check)      ─── depends on M1-C1
M1-D1 (error theorem)    ─── no deps (uses existing infrastructure)
M1-D2 (revokeCdt docs)   ─── depends on M1-D1

                                Cross-Phase Dependencies
                                ────────────────────────
M1-E (docstring)          ─┐
M1-A (guard strengthen)   ─┤
M1-B (mint completeness)  ─┤── M1 complete ── M2-C (reply lemma)   ─┐
M1-C (addEdge acyclicity) ─┤                  M2-A (fuse revoke)   ─┤── M2 complete
M1-D (error theorem)      ─┘                  M2-B (parentMap)     ─┘       │
                                                                              │
                                               M3-A (transfer types) ─┐       │
                                               M3-B (send path)      ─┤── M3 ─┤
                                               M3-C (preservation)   ─┤       │
                                               M3-D (tests)          ─┘       │
                                                                              │
                                               M4-A (resolve tests)  ─┐       │
                                               M4-B (revoke tests)   ─┘── M4 ─┤
                                                                              │
                                               M5-A (streaming BFS)  ─┐       │
                                               M5-B (documentation)  ─┘── M5 ─┘
```

M1 must complete before M2 (M1-C provides `addEdge_preserves_edgeWellFounded` needed
by M2-B's `parentMap` consistency proofs). M3 can proceed in parallel with M2
after M1 completes. M4 can proceed after M3-D (needs IPC transfer tests). M5
depends on all prior phases for documentation completeness.

**Phase 1 optimal execution order**: M1-E → M1-A1 → M1-A2 → M1-B1 → {M1-B2, M1-B3}
(parallel) → M1-C1 → M1-C2 → M1-D1 → M1-D2. Total: 10 subtasks, 8 sequential steps.

**Phase 2 optimal execution order**: M2-C1 → M2-C2 → M2-A1 → M2-A2 → M2-A3 →
M2-A4 → M2-B1 → {M2-B2, M2-B3, M2-B4, M2-B5, M2-B6} (parallel) → M2-B7 →
M2-B8. Total: 12 subtasks, 8 sequential steps.

---

## 9. Workstream Summary Table

| ID | Focus | Priority | Findings |
|----|-------|----------|----------|
| **WS-M1** | Proof strengthening (10 subtasks): guard-match extraction theorem, CDT mint completeness predicate + preservation + composition, addEdge acyclicity + cycle-check helper, error-swallowing consistency theorem, stale docstrings | HIGH | M-G01, M-G02, M-G03, M-G04, M-D02 |
| **WS-M2** | Performance (12 subtasks): fused single-pass revoke fold, CDT `parentMap` O(1) parent lookup + targeted removal, shared reply-preservation lemma extraction | HIGH | M-P01, M-P02, M-P03, M-P05 |
| **WS-M3** | IPC capability transfer: model, integrate, prove, test | MEDIUM | M-D01, M-T03 |
| **WS-M4** | Test coverage: multi-level resolution edge cases, strict revocation stress | MEDIUM | M-T01, M-T02 |
| **WS-M5** | Streaming BFS revocation, full documentation sync | LOW | M-P04 |
