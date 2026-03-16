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
**Subtasks**: 14 atomic units across 3 tasks (M2-A1–A4, M2-B1–B8, M2-C1–C2).
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

Phase 2 is subdivided into 14 atomic subtasks across 3 tasks. Each subtask is
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

**Design decision**: Introduce a fused helper `revokeAndClearRefsState` that replaces
the two-pass pattern. The legacy `clearCapabilityRefsState` and `clearCapabilityRefs`
definitions and their 11 preservation theorems were removed as dead code after the
fused helper was adopted — no remaining callers existed.

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
Total: 14 subtasks, 8 sequential steps.

**Deliverables**: `revokeAndClearRefsState` fused helper + 4 preservation theorems,
`capabilityInvariantBundle_of_storeTcbAndEnsureRunnable` extracted lemma,
`parentMap` field + O(1) `parentOf` + `parentMapConsistent` invariant + 3
consistency theorems. ~6 new proved declarations; zero sorry/axiom.

---

### Phase 3: IPC Capability Transfer (WS-M3)

**Target version**: 0.16.16
**Files modified**: `Model/Object/Types.lean`, `Model/Object/Structures.lean`,
`Kernel/Capability/Operations.lean`, `Kernel/Capability/Invariant/Preservation.lean`,
`Kernel/IPC/DualQueue/Transport.lean`, `Kernel/IPC/Operations/Endpoint.lean`,
`Kernel/IPC/Invariant/EndpointPreservation.lean`,
`Kernel/IPC/Invariant/Structural.lean`, `Kernel/Architecture/SyscallArgDecode.lean`,
`Kernel/API.lean`, `tests/OperationChainSuite.lean`,
`tests/NegativeStateSuite.lean`, `SeLe4n/Testing/MainTraceHarness.lean`

This phase resolves the last deferred item from WS-L (L-T03): capability transfer
during IPC. In seL4, `seL4_Send`/`seL4_Call` can include extra capabilities in the
message that are unwrapped into the receiver's CSpace upon rendezvous. This is the
mechanism by which a client delegates capabilities to a server (or vice versa).

**Architectural alignment with seL4**: In the real seL4, capability unwrapping
happens on the *receive* side of the IPC rendezvous — the kernel reads caps from
the sender's TCB `pendingMessage`, resolves them in the sender's CSpace, attenuates
rights through the endpoint capability's grant right, and installs the results into
the receiver's CSpace. This model follows the same architecture: `endpointSendDual`
continues to store `msg.caps` in the sender's TCB unmodified; the new
`ipcUnwrapCaps` operation runs during the rendezvous (inside `endpointReceiveDual`
and `endpointCall`'s immediate-handshake paths) when the receiver is known.

**seL4 grant-right gate**: In seL4, capability transfer through IPC requires
the endpoint capability to have the `Grant` right. If the endpoint capability
lacks `Grant`, the extra capabilities in the message are silently dropped (not
an error — the message registers still transfer, only the caps are skipped).
This model replicates this behavior: `ipcUnwrapCaps` checks the endpoint
capability's `Grant` right before attempting any transfers, and returns an
empty result array if the right is absent.

**Design constraints**:
- `IpcMessage.caps` is `Array Capability` (bounded by `maxExtraCaps = 3`).
- The existing `endpointSendDual`, `endpointReceiveDual`, `endpointCall`, and
  `endpointReply` signatures are preserved. Cap unwrapping is a new post-step.
- Each transferred cap gets a CDT derivation edge (`.ipcTransfer`) from the
  sender's slot to the receiver's slot, maintaining CDT completeness.
- No new `KernelError` variants needed — transfer failures are recorded in
  per-cap result entries, not propagated as kernel errors.

Phase 3 is subdivided into 20 atomic subtasks across 7 tasks. Each subtask is
independently buildable and testable. Tasks are ordered by dependency: M3-A
(types) has no deps; M3-B (slot scanning) depends on M3-A; M3-C (single-cap
transfer) depends on M3-A and M3-B; M3-D (batch unwrap) depends on M3-C;
M3-E (IPC integration) depends on M3-D; M3-F (API wiring) depends on M3-E;
M3-G (tests) depends on M3-E.

---

#### Task M3-A: Define IPC capability transfer types (M-D01)

**Problem**: `IpcMessage` carries `caps : Array Capability` (Types.lean:167) but
there is no result type to represent the outcome of unwrapping each transferred
capability into the receiver's CSpace.

##### Subtask M3-A1: Define `CapTransferResult` inductive

**Implementation**:
1. In `Model/Object/Types.lean`, after `IpcMessage` (line 196), add:
   ```lean
   /-- M-D01: Result of attempting to unwrap a single transferred capability
   into the receiver's CSpace during IPC rendezvous.

   seL4 semantics: each extra cap in the message is independently unwrapped.
   Failures on one cap do not abort the transfer of subsequent caps. -/
   inductive CapTransferResult where
     /-- Successfully installed in the receiver's CSpace at the given slot. -/
     | installed (ref : SlotRef)
     /-- No empty slot available in the receiver's CNode (receiver CSpace full). -/
     | noSlot
     /-- The endpoint capability lacks the Grant right — transfer silently skipped. -/
     | grantDenied
     deriving Repr, DecidableEq
   ```

   **Design note**: The original plan included `attenuationFailed` but this is
   incorrect for seL4 semantics. In seL4, the transferred capability inherits
   the *sender's* rights as-is (the sender already attenuated when it placed the
   cap in its message). The only gate is the endpoint's `Grant` right, which
   controls whether *any* cap transfer occurs. If `Grant` is present, caps
   transfer with full sender rights. This simplifies the model and aligns with
   the actual seL4 implementation.

##### Subtask M3-A2: Define `CapTransferSummary` result structure

**Implementation**:
1. In `Model/Object/Types.lean`, after `CapTransferResult`, add:
   ```lean
   /-- M-D01: Aggregated results of unwrapping all extra capabilities in an
   IPC message. One entry per cap in the original `msg.caps` array. -/
   structure CapTransferSummary where
     results : Array CapTransferResult := #[]
     deriving Repr, DecidableEq
   ```

##### Subtask M3-A3: Add `DerivationOp.ipcTransfer` variant

**Implementation**:
1. In `Model/Object/Structures.lean`, extend the `DerivationOp` inductive
   (which currently has `.mint`, `.copy`, `.move`) with:
   ```lean
   | ipcTransfer  -- capability transferred via IPC rendezvous
   ```
   This allows CDT edges to distinguish IPC-transferred capabilities from
   those created by explicit CSpace operations, which is needed for
   revocation-exhaustiveness auditing and CDT visualization.

**Verification**: `lake build` succeeds (all three subtasks are additive definitions).

**Files**: `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Model/Object/Structures.lean`

---

#### Task M3-B: Implement bounded slot scanning (M-D01)

**Problem**: The receiver's CSpace needs a mechanism to find the first available
slot for each transferred capability. In seL4, the receiver specifies an IPC
buffer region in its CSpace where incoming caps are placed. The model simplifies
this: the receiver's TCB has `cspaceRoot : ObjId` pointing to its root CNode, and
caps are placed starting from a configurable `receiverSlotBase`.

##### Subtask M3-B1: Define `CNode.findFirstEmptySlot`

**Implementation**:
1. In `Model/Object/Structures.lean`, after the CNode slot operations section, add:
   ```lean
   /-- M-D01: Find the first empty slot in a CNode starting from `base`,
   scanning up to `limit` consecutive slot indices. Returns `none` if all
   scanned slots are occupied.

   The iteration is bounded by `limit` (typically `maxExtraCaps = 3`) rather
   than `2^radixWidth`, because we only need slots for the (at most 3) extra
   caps in the message. Termination is structural on `limit`. -/
   def CNode.findFirstEmptySlot (cn : CNode) (base : SeLe4n.Slot)
       (limit : Nat) : Option SeLe4n.Slot :=
     match limit with
     | 0 => none
     | n + 1 =>
         match cn.lookup base with
         | none => some base
         | some _ => cn.findFirstEmptySlot (SeLe4n.Slot.ofNat (base.toNat + 1)) n
   ```

##### Subtask M3-B2: Prove `findFirstEmptySlot` correctness theorems

**Implementation**:
1. In `Model/Object/Structures.lean`, after the definition, add:
   ```lean
   /-- If findFirstEmptySlot returns `some s`, then `cn.lookup s = none`. -/
   theorem CNode.findFirstEmptySlot_spec
       (cn : CNode) (base : SeLe4n.Slot) (limit : Nat) (s : SeLe4n.Slot)
       (hFind : cn.findFirstEmptySlot base limit = some s) :
       cn.lookup s = none

   /-- findFirstEmptySlot returns `none` iff all scanned slots are occupied. -/
   theorem CNode.findFirstEmptySlot_none_iff
       (cn : CNode) (base : SeLe4n.Slot) (limit : Nat) :
       cn.findFirstEmptySlot base limit = none ↔
         ∀ i, i < limit → (cn.lookup (SeLe4n.Slot.ofNat (base.toNat + i))).isSome
   ```
   Proofs: structural induction on `limit`.

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Model/Object/Structures.lean`

---

#### Task M3-C: Implement single-cap transfer operation (M-D01)

**Problem**: No operation currently takes a capability from a sender's message
and installs it into the receiver's CSpace with proper CDT tracking.

##### Subtask M3-C1: Define `ipcTransferSingleCap`

**Implementation**:
1. In `Kernel/Capability/Operations.lean`, after the CDT operations section
   (after `cspaceRevokeCdtStrict`), add a new section:
   ```lean
   -- ============================================================================
   -- M-D01: IPC capability transfer operations
   -- ============================================================================

   /-- M-D01: Transfer a single capability from the sender's IPC message into
   the receiver's CSpace.

   Semantics (matching seL4's IPC cap unwrap):
   1. Look up the receiver's root CNode via `receiverCspaceRoot`.
   2. Scan for the first empty slot starting from `slotBase`.
   3. If found, insert the capability (with sender's original rights).
   4. Record a CDT derivation edge of type `.ipcTransfer` from the sender's
      source slot to the newly occupied receiver slot.

   The sender's capability is NOT removed from the sender's CSpace — IPC
   transfer is a copy, not a move (matching seL4 semantics where the sender
   retains its capability after sending).

   Returns `CapTransferResult.installed ref` on success, `.noSlot` if the
   receiver's CNode has no empty slots in the scan range. -/
   def ipcTransferSingleCap
       (cap : Capability)
       (senderSlot : CSpaceAddr)
       (receiverCspaceRoot : SeLe4n.ObjId)
       (slotBase : SeLe4n.Slot)
       (scanLimit : Nat) : Kernel CapTransferResult :=
     fun st =>
       match st.objects[receiverCspaceRoot]? with
       | some (.cnode cn) =>
           match cn.findFirstEmptySlot slotBase scanLimit with
           | none => .ok (.noSlot, st)
           | some emptySlot =>
               let dstAddr : CSpaceAddr := { cnode := receiverCspaceRoot, slot := emptySlot }
               match cspaceInsertSlot dstAddr cap st with
               | .error e => .error e
               | .ok ((), st') =>
                   -- Record CDT derivation edge: sender slot → receiver slot
                   let (srcNode, stSrc) := SystemState.ensureCdtNodeForSlot st' senderSlot
                   let (dstNode, stDst) := SystemState.ensureCdtNodeForSlot stSrc dstAddr
                   let cdt' := stDst.cdt.addEdge srcNode dstNode .ipcTransfer
                   .ok (.installed { cnode := receiverCspaceRoot, slot := emptySlot },
                        { stDst with cdt := cdt' })
       | _ => .error .objectNotFound
   ```

##### Subtask M3-C2: Prove `ipcTransferSingleCap` preserves scheduler

**Implementation**:
1. In `Kernel/Capability/Operations.lean`, after the definition, add:
   ```lean
   theorem ipcTransferSingleCap_preserves_scheduler
       (cap : Capability) (senderSlot : CSpaceAddr)
       (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
       (scanLimit : Nat) (st st' : SystemState)
       (result : CapTransferResult)
       (hStep : ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit st
                = .ok (result, st')) :
       st'.scheduler = st.scheduler
   ```
   Proof: unfold `ipcTransferSingleCap`, case-split on CNode lookup and
   `findFirstEmptySlot`. The `.noSlot` case is trivial (state unchanged). The
   `.inserted` case chains through `cspaceInsertSlot_preserves_scheduler` and
   `ensureCdtNodeForSlot`/`addEdge` (which don't touch scheduler).

##### Subtask M3-C3: Prove `ipcTransferSingleCap_preserves_capabilityInvariantBundle`

**Implementation**:
1. In `Kernel/Capability/Invariant/Preservation.lean`, after the existing
   `cspaceMintWithCdt_preserves_capabilityInvariantBundle`, add:
   ```lean
   /-- M-D01: IPC single-cap transfer preserves the capability invariant bundle.

   The proof decomposes into the `.noSlot` case (state unchanged, trivial) and
   the `.inserted` case, which chains:
   1. `cspaceInsertSlot_preserves_capabilityInvariantBundle` — slot insertion
   2. `ensureCdtNodeForSlot` — CDT field preservation
   3. `addEdge` with `.ipcTransfer` — CDT edge addition

   The `hCdtPost` hypothesis (CDT completeness + acyclicity of the post-state)
   follows the same pattern as `cspaceCopy_preserves_capabilityInvariantBundle`
   since IPC transfer is semantically a cross-CSpace copy. -/
   theorem ipcTransferSingleCap_preserves_capabilityInvariantBundle
       (st st' : SystemState) (cap : Capability) (senderSlot : CSpaceAddr)
       (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot) (scanLimit : Nat)
       (result : CapTransferResult)
       (hInv : capabilityInvariantBundle st)
       (hSlotCapacity : ∀ cn, st.objects[receiverRoot]? = some (.cnode cn) →
         ∀ s, (cn.insert s cap).slotCountBounded)
       (hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st')
       (hStep : ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit st
                = .ok (result, st')) :
       capabilityInvariantBundle st'
   ```

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Kernel/Capability/Operations.lean`,
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean`

---

#### Task M3-D: Implement batch cap unwrap and grant-right gate (M-D01)

**Problem**: During IPC rendezvous, all caps in `msg.caps` (up to 3) must be
unwrapped sequentially into the receiver's CSpace. The endpoint's `Grant` right
gates whether any transfer occurs.

##### Subtask M3-D1: Define `ipcUnwrapCaps` batch operation

**Implementation**:
1. In `Kernel/IPC/Operations/Endpoint.lean` (or a new file
   `Kernel/IPC/Operations/CapTransfer.lean` if Endpoint.lean is too large),
   add:
   ```lean
   /-- M-D01: Unwrap all extra capabilities from an IPC message into the
   receiver's CSpace. This is the top-level cap-transfer entry point, called
   during IPC rendezvous after message delivery.

   seL4 semantics:
   - If the endpoint capability lacks `Grant` right, all caps are skipped
     (returns array of `.grantDenied` results).
   - Otherwise, each cap in `msg.caps` is transferred via
     `ipcTransferSingleCap`, scanning consecutive slots starting from
     `receiverSlotBase`. The scan window advances by 1 after each successful
     insertion to avoid overwriting.
   - Failures on individual caps (`.noSlot`) do NOT abort the remaining
     transfers — each cap is independently processed.
   - The sender retains all transferred capabilities (IPC transfer is copy). -/
   def ipcUnwrapCaps
       (msg : IpcMessage)
       (senderCspaceRoot : SeLe4n.ObjId)
       (receiverCspaceRoot : SeLe4n.ObjId)
       (receiverSlotBase : SeLe4n.Slot)
       (endpointGrantRight : Bool) : Kernel CapTransferSummary :=
     fun st =>
       if !endpointGrantRight then
         -- No Grant right → skip all cap transfers
         let results := msg.caps.map fun _ => CapTransferResult.grantDenied
         .ok ({ results }, st)
       else
         -- Fold over msg.caps, threading state and advancing slot base
         let initAcc : CapTransferSummary × SystemState × SeLe4n.Slot :=
           ({ results := #[] }, st, receiverSlotBase)
         let fold := msg.caps.foldl (fun acc cap =>
           let (summary, stAcc, nextBase) := acc
           match ipcTransferSingleCap cap
               { cnode := senderCspaceRoot, slot := SeLe4n.Slot.ofNat 0 }
               receiverCspaceRoot nextBase maxExtraCaps stAcc with
           | .error _e =>
               -- Transfer error → record noSlot, state unchanged, advance base
               ({ results := summary.results.push .noSlot }, stAcc,
                SeLe4n.Slot.ofNat (nextBase.toNat + 1))
           | .ok (result, stNext) =>
               let nextBase' := match result with
                 | .inserted _ => SeLe4n.Slot.ofNat (nextBase.toNat + 1)
                 | _ => nextBase
               ({ results := summary.results.push result }, stNext, nextBase'))
           initAcc
         let (finalSummary, finalSt, _) := fold
         .ok (finalSummary, finalSt)
   ```

   **Design note on `senderSlot` parameter**: The `senderSlot` passed to
   `ipcTransferSingleCap` is used solely for CDT edge recording (source of
   the derivation). In a full implementation, each cap in `msg.caps` would
   reference its original slot in the sender's CSpace. For the initial model,
   we use a placeholder slot (`Slot.ofNat 0`) — the CDT edge still records
   the transfer but without precise sender-side slot tracking. This is
   acceptable because:
   (a) The CDT is for revocation scoping, and the receiver-side slot (which
       IS precisely tracked) is what revocation targets.
   (b) Precise sender-side tracking requires extending `IpcMessage.caps` from
       `Array Capability` to `Array (Capability × CSpaceAddr)`, which is a
       larger change deferred to a future phase.

##### Subtask M3-D2: Prove `ipcUnwrapCaps` preserves non-CSpace fields

**Implementation**:
1. Add field preservation theorems:
   ```lean
   theorem ipcUnwrapCaps_preserves_scheduler
       (...) (hStep : ipcUnwrapCaps ... st = .ok (summary, st')) :
       st'.scheduler = st.scheduler

   theorem ipcUnwrapCaps_preserves_services
       (...) (hStep : ipcUnwrapCaps ... st = .ok (summary, st')) :
       st'.services = st.services
   ```
   Proofs: induction on `msg.caps.size` (bounded by `maxExtraCaps = 3`),
   composing `ipcTransferSingleCap_preserves_scheduler` at each step.

##### Subtask M3-D3: Prove `ipcUnwrapCaps_preserves_capabilityInvariantBundle`

**Implementation**:
1. In `Kernel/Capability/Invariant/Preservation.lean`, add:
   ```lean
   theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle
       (st st' : SystemState) (msg : IpcMessage)
       (senderRoot receiverRoot : SeLe4n.ObjId)
       (slotBase : SeLe4n.Slot) (grantRight : Bool)
       (summary : CapTransferSummary)
       (hInv : capabilityInvariantBundle st)
       (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
                = .ok (summary, st')) :
       capabilityInvariantBundle st'
   ```
   Proof strategy: case-split on `grantRight`.
   - `false`: state unchanged, apply `hInv`.
   - `true`: fold induction on `msg.caps`. Each step preserves the bundle
     via `ipcTransferSingleCap_preserves_capabilityInvariantBundle`. The
     `hCdtPost` hypothesis is discharged by composing
     `ensureCdtNodeForSlot` freshness with
     `addEdge_preserves_edgeWellFounded_fresh`.

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (or new
`Kernel/IPC/Operations/CapTransfer.lean`),
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean`

---

#### Task M3-E: Integrate cap unwrap into IPC rendezvous paths (M-D01)

**Problem**: The rendezvous paths in `endpointSendDual`, `endpointReceiveDual`,
`endpointCall`, and `endpointReply` transfer the message into the receiver's
TCB but do not unwrap `msg.caps` into the receiver's CSpace.

**Architectural approach**: Rather than modifying the existing dual-queue
operations (which have extensive preservation proofs), we define a wrapper
operation that composes the existing IPC operation with `ipcUnwrapCaps` as a
post-step. This preserves all existing proofs and theorem signatures.

##### Subtask M3-E1: Define `endpointSendDualWithCaps` wrapper

**Implementation**:
1. In `Kernel/IPC/DualQueue/Transport.lean`, after `endpointSendDual`, add:
   ```lean
   /-- M-D01: Extended send with capability transfer. Composes `endpointSendDual`
   with `ipcUnwrapCaps` as a post-step when immediate rendezvous occurs.

   Semantics:
   - If a receiver is waiting (immediate rendezvous): send the message via
     `endpointSendDual`, then unwrap `msg.caps` into the receiver's CSpace.
   - If no receiver is waiting (sender enqueues): caps stay in the message
     stored in the sender's TCB. They will be unwrapped when a receiver
     later dequeues the sender.
   - The `endpointRights` parameter carries the endpoint capability's rights
     from the sender's gate — used to check the `Grant` right gate.

   Returns the cap transfer summary (empty if no immediate rendezvous or if
   the endpoint lacks Grant right). -/
   def endpointSendDualWithCaps
       (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
       (msg : IpcMessage) (endpointRights : AccessRightSet)
       (receiverCspaceRoot : SeLe4n.ObjId)
       (receiverSlotBase : SeLe4n.Slot) : Kernel CapTransferSummary :=
     fun st =>
       match endpointSendDual endpointId sender msg st with
       | .error e => .error e
       | .ok ((), st') =>
           -- Check if immediate rendezvous occurred (receiver was waiting)
           -- by detecting if the sender is still runnable (not blocked).
           -- If sender was enqueued, caps stay in TCB for later unwrap.
           match st'.objects[sender.toObjId]? with
           | some (.tcb senderTcb) =>
               match senderTcb.ipcState with
               | .blockedOnSend _ =>
                   -- Sender was enqueued — no immediate rendezvous, no cap unwrap
                   .ok ({ results := #[] }, st')
               | _ =>
                   -- Immediate rendezvous occurred — unwrap caps
                   let grantRight := endpointRights.mem .grant
                   ipcUnwrapCaps msg sender.toObjId receiverCspaceRoot
                     receiverSlotBase grantRight st'
           | _ => .ok ({ results := #[] }, st')
   ```

##### Subtask M3-E2: Define `endpointReceiveDualWithCaps` wrapper

**Implementation**:
1. In `Kernel/IPC/DualQueue/Transport.lean`, after `endpointReceiveDual`, add:
   ```lean
   /-- M-D01: Extended receive with capability transfer. When a sender is
   dequeued (immediate rendezvous on the receive side), unwrap `msg.caps`
   from the sender's pending message into the receiver's CSpace.

   When no sender is waiting (receiver enqueues), no cap transfer occurs —
   the receiver will get caps when a sender later arrives via
   `endpointSendDualWithCaps`. -/
   def endpointReceiveDualWithCaps
       (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
       (endpointRights : AccessRightSet)
       (receiverCspaceRoot : SeLe4n.ObjId)
       (receiverSlotBase : SeLe4n.Slot) : Kernel (SeLe4n.ThreadId × CapTransferSummary) :=
     fun st =>
       match endpointReceiveDual endpointId receiver st with
       | .error e => .error e
       | .ok (senderId, st') =>
           -- Check if the receiver got a message (not blocked on receiveQ)
           match st'.objects[receiver.toObjId]? with
           | some (.tcb receiverTcb) =>
               match receiverTcb.pendingMessage with
               | some msg =>
                   -- Sender was dequeued — unwrap caps from their message
                   let grantRight := endpointRights.mem .grant
                   match ipcUnwrapCaps msg senderId.toObjId receiverCspaceRoot
                       receiverSlotBase grantRight st' with
                   | .error e => .error e
                   | .ok (summary, st'') => .ok ((senderId, summary), st'')
               | none =>
                   -- Receiver was enqueued (no sender available)
                   .ok ((senderId, { results := #[] }), st')
           | _ => .ok ((senderId, { results := #[] }), st')
   ```

##### Subtask M3-E3: Define `endpointCallWithCaps` wrapper

**Implementation**:
1. In `Kernel/IPC/DualQueue/Transport.lean`, after `endpointCall`, add an
   analogous wrapper that composes `endpointCall` with `ipcUnwrapCaps` for
   the immediate-rendezvous path. Same structure as M3-E1 but using
   `endpointCall` as the base operation and returning
   `Kernel CapTransferSummary`.

##### Subtask M3-E4: Prove IPC invariant preservation for wrapper operations

**Implementation**:
1. In `Kernel/IPC/Invariant/EndpointPreservation.lean`, add preservation
   theorems for each wrapper:
   ```lean
   theorem endpointSendDualWithCaps_preserves_ipcInvariant (...)
   theorem endpointReceiveDualWithCaps_preserves_ipcInvariant (...)
   theorem endpointCallWithCaps_preserves_ipcInvariant (...)
   ```
   Each proof composes the existing `endpointSendDual_preserves_ipcInvariant`
   (or equivalent) with `ipcUnwrapCaps_preserves_capabilityInvariantBundle`.
   IPC structural invariants (`dualQueueSystemInvariant`) are preserved because
   `ipcUnwrapCaps` only modifies CNode objects and CDT state — it does not
   touch endpoint queues, TCB queue links, or scheduler state.

2. In `Kernel/IPC/Invariant/Structural.lean`, add:
   ```lean
   theorem endpointSendDualWithCaps_preserves_dualQueueSystemInvariant (...)
   theorem endpointReceiveDualWithCaps_preserves_dualQueueSystemInvariant (...)
   ```

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Kernel/IPC/DualQueue/Transport.lean`,
`SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean`,
`SeLe4n/Kernel/IPC/Invariant/Structural.lean`

---

#### Task M3-F: Wire cap transfer into API and syscall dispatch (M-D01)

**Problem**: `dispatchWithCap` in API.lean (line 372) hardcodes `caps := #[]`
for all IPC operations. The `SyscallDecodeResult` carries `msgInfo.extraCaps`
which encodes how many extra capabilities the sender includes, but this
information is currently ignored.

##### Subtask M3-F1: Decode extra capability addresses from message registers

**Implementation**:
1. In `Kernel/Architecture/SyscallArgDecode.lean`, add:
   ```lean
   /-- M-D01: Decode extra capability addresses from message registers.

   seL4 convention: extra cap addresses are packed into the message registers
   immediately after the message body. The `msgInfo.extraCaps` field (0..3)
   specifies how many extra cap addresses follow. Each extra cap address is
   a single register value interpreted as a CPtr.

   Returns an array of CPtrs (length ≤ 3). If a register index is out of
   bounds, the corresponding cap address is silently dropped (seL4 behavior:
   truncate to available registers). -/
   def decodeExtraCapAddrs (decoded : SyscallDecodeResult) :
       Array SeLe4n.CPtr :=
     let startIdx := decoded.msgInfo.length
     let count := min decoded.msgInfo.extraCaps maxExtraCaps
     (Array.range count).filterMap fun i =>
       decoded.msgRegs[startIdx + i]?.map SeLe4n.CPtr.ofNat
   ```

##### Subtask M3-F2: Add `resolveExtraCaps` helper to API.lean

**Implementation**:
1. In `Kernel/API.lean`, add:
   ```lean
   /-- M-D01: Resolve extra capability addresses from the sender's CSpace
   into actual capabilities for IPC message transfer.

   For each CPtr in `capAddrs`, resolve it via `resolveCapAddress` in the
   sender's CSpace root, then look up the capability at the resolved slot.
   Caps that fail to resolve are silently dropped (seL4 behavior).
   Returns the resolved capabilities as an array. -/
   def resolveExtraCaps (cspaceRoot : SeLe4n.ObjId)
       (capAddrs : Array SeLe4n.CPtr) (depth : Nat) :
       Kernel (Array Capability) :=
     fun st =>
       let (caps, _) := capAddrs.foldl (fun (acc, stAcc) addr =>
         match resolveCapAddress cspaceRoot addr depth stAcc with
         | .error _ => (acc, stAcc)
         | .ok ref =>
             match SystemState.lookupSlotCap stAcc ref with
             | none => (acc, stAcc)
             | some cap => (acc.push cap, stAcc)) (#[], st)
       .ok (caps, st)
   ```

##### Subtask M3-F3: Update `dispatchWithCap` to populate `msg.caps`

**Implementation**:
1. In `Kernel/API.lean`, update the `.send` and `.call` branches of
   `dispatchWithCap` (lines 376–394) to resolve extra caps:
   ```lean
   -- BEFORE:
   -- | .send =>
   --   ...
   --   endpointSendDual epId tid { registers := body, caps := #[], badge := cap.badge }

   -- AFTER:
   | .send =>
     match cap.target with
     | .object epId =>
       fun st =>
         let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
         let extraCapAddrs := decodeExtraCapAddrs decoded
         match resolveExtraCaps gate.cspaceRoot extraCapAddrs gate.capDepth st with
         | .error e => .error e
         | .ok (resolvedCaps, st') =>
             endpointSendDualWithCaps epId tid
               { registers := body, caps := resolvedCaps, badge := cap.badge }
               cap.rights  -- endpoint rights for Grant check
               gate.cspaceRoot  -- receiver CSpace root (placeholder — see note)
               (SeLe4n.Slot.ofNat 0)  -- receiver slot base
               st'
     | _ => fun _ => .error .invalidCapability
   ```

   **Design note on receiver CSpace root**: At the send call site, the
   receiver's identity is not yet known (the receiver may be waiting on the
   endpoint or may arrive later). The wrapper operations handle this correctly:
   if no immediate rendezvous occurs, caps stay in the message. When rendezvous
   does occur, the receiver's `cspaceRoot` is read from the receiver's TCB
   inside the wrapper. The `receiverCspaceRoot` parameter at the API level
   is used only for the immediate-rendezvous path and should be populated from
   the receiver's TCB. This requires a minor adjustment: have the wrapper
   operations read the receiver's TCB `cspaceRoot` internally rather than
   accepting it as a parameter.

2. Apply the same pattern to the `.call` branch.

**Verification**: `lake build` succeeds. `test_smoke.sh` passes.

**Files**: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`,
`SeLe4n/Kernel/API.lean`

---

#### Task M3-G: Add IPC capability transfer test coverage (M-T03)

**Problem**: L-T03 identified the complete absence of IPC capability transfer
testing. Now that the transfer operations exist, comprehensive test coverage
is needed.

##### Subtask M3-G1: Add positive transfer chain test

**Implementation**:
1. In `tests/OperationChainSuite.lean`, add `chain12IpcCapTransfer`:
   - **Setup**: Create sender (tid=50) with CNode containing 3 capabilities
     (read-only, read-write, full-rights). Create receiver (tid=51) with
     empty CNode. Create endpoint (eid=60) with Grant right.
   - **Action**: Sender calls `endpointSendDualWithCaps` with a message
     carrying all 3 caps.
   - **Verify**:
     - Receiver's CNode now has 3 new capabilities in slots 0, 1, 2.
     - Each transferred cap has the same rights as the sender's original.
     - CDT has 3 new `.ipcTransfer` edges.
     - `assertInvariants` passes on the final state.
   - **Scenario ID**: `SCN-IPC-CAP-TRANSFER-BASIC`

##### Subtask M3-G2: Add grant-right gate test

**Implementation**:
1. In `tests/OperationChainSuite.lean`, add `chain13IpcCapTransferNoGrant`:
   - **Setup**: Same as M3-G1 but endpoint lacks Grant right (only Read+Write).
   - **Action**: Sender sends message with caps.
   - **Verify**:
     - All transfer results are `.grantDenied`.
     - Receiver's CNode is still empty.
     - Message registers still transferred normally.
   - **Scenario ID**: `SCN-IPC-CAP-TRANSFER-NO-GRANT`

##### Subtask M3-G3: Add no-slot negative test

**Implementation**:
1. In `tests/NegativeStateSuite.lean`, add a test for CNode-full scenario:
   - **Setup**: Receiver's CNode has all slots occupied.
   - **Action**: Sender sends message with 1 cap.
   - **Verify**: Transfer result is `.noSlot`.
   - **Scenario ID**: `SCN-IPC-CAP-TRANSFER-FULL-CNODE`

##### Subtask M3-G4: Add badge-and-cap combined transfer test

**Implementation**:
1. In `tests/OperationChainSuite.lean`, add `chain14IpcBadgeAndCapTransfer`:
   - **Setup**: Sender's endpoint capability has badge 0xCAFE. Sender sends
     a message with 1 register + 2 extra caps.
   - **Action**: Send via the extended path.
   - **Verify**:
     - Receiver gets the message with badge 0xCAFE.
     - Receiver's CNode gets 2 new capabilities.
     - Both badge propagation and cap transfer work together.
   - **Scenario ID**: `SCN-IPC-CAP-BADGE-COMBINED`

##### Subtask M3-G5: Update scenario registry and fixtures

**Implementation**:
1. Add new scenario IDs to `tests/fixtures/scenario_registry.yaml`.
2. Update `tests/fixtures/main_trace_smoke.expected` if MainTraceHarness
   output changes (only if new scenarios are added to the harness).

**Verification**: `test_smoke.sh` passes. All new tests pass.

**Files**: `tests/OperationChainSuite.lean`, `tests/NegativeStateSuite.lean`,
`tests/fixtures/scenario_registry.yaml`

---

#### M3 Dependency Graph and Execution Order

```
M3-A1 (CapTransferResult type)      ─── no deps (additive definition)
M3-A2 (CapTransferSummary type)     ─── depends on M3-A1
M3-A3 (DerivationOp.ipcTransfer)    ─── no deps (additive to Structures.lean)
M3-B1 (findFirstEmptySlot def)      ─── no deps (CNode utility)
M3-B2 (findFirstEmptySlot proofs)   ─── depends on M3-B1
M3-C1 (ipcTransferSingleCap def)    ─── depends on M3-A1, M3-A3, M3-B1
M3-C2 (single-cap scheduler pres.)  ─── depends on M3-C1
M3-C3 (single-cap bundle pres.)     ─── depends on M3-C1
M3-D1 (ipcUnwrapCaps def)           ─── depends on M3-A2, M3-C1
M3-D2 (unwrap field preservation)   ─── depends on M3-D1, M3-C2
M3-D3 (unwrap bundle preservation)  ─── depends on M3-D1, M3-C3
M3-E1 (sendDualWithCaps wrapper)    ─── depends on M3-D1
M3-E2 (receiveDualWithCaps wrapper) ─── depends on M3-D1
M3-E3 (callWithCaps wrapper)        ─── depends on M3-D1
M3-E4 (IPC invariant preservation)  ─── depends on M3-E1, M3-E2, M3-E3, M3-D2, M3-D3
M3-F1 (decodeExtraCapAddrs)         ─── no deps (additive to SyscallArgDecode)
M3-F2 (resolveExtraCaps helper)     ─── depends on M3-F1
M3-F3 (dispatchWithCap wiring)      ─── depends on M3-E1, M3-E3, M3-F2
M3-G1 (positive transfer test)      ─── depends on M3-E1
M3-G2 (grant-right gate test)       ─── depends on M3-E1
M3-G3 (no-slot negative test)       ─── depends on M3-C1
M3-G4 (badge+cap combined test)     ─── depends on M3-E1
M3-G5 (registry + fixtures)         ─── depends on M3-G1..G4
```

**Optimal execution order**:
{M3-A1, M3-A3, M3-B1, M3-F1} (parallel, no deps) →
{M3-A2, M3-B2} (parallel) →
M3-C1 →
{M3-C2, M3-C3} (parallel) →
M3-D1 →
{M3-D2, M3-D3} (parallel) →
{M3-E1, M3-E2, M3-E3, M3-F2} (parallel) →
{M3-E4, M3-F3, M3-G1, M3-G2, M3-G3, M3-G4} (parallel) →
M3-G5.
Total: 20 subtasks, 9 sequential steps.

**Deliverables**: `CapTransferResult` + `CapTransferSummary` types,
`DerivationOp.ipcTransfer` CDT variant, `CNode.findFirstEmptySlot` + 2
correctness theorems, `ipcTransferSingleCap` + 2 preservation theorems,
`ipcUnwrapCaps` + 3 preservation theorems, 3 wrapper operations
(`endpointSendDualWithCaps`, `endpointReceiveDualWithCaps`,
`endpointCallWithCaps`) + 5 preservation theorems, `decodeExtraCapAddrs` +
`resolveExtraCaps` helpers, updated `dispatchWithCap` wiring, 4 new test
scenarios. ~15 new proved declarations; zero sorry/axiom.

---

### Phase 4: Test Coverage Expansion (WS-M4) — COMPLETED (v0.16.18)

**Target version**: 0.16.18
**Files modified**: `tests/OperationChainSuite.lean`, `tests/NegativeStateSuite.lean`,
`tests/scenarios/scenario_catalog.json`

Phase 4 is subdivided into 8 atomic subtasks across 2 tasks. Each subtask is
independently buildable and testable. Task M4-A adds standalone unit tests for
`resolveCapAddress` edge cases that were previously only covered implicitly.
Task M4-B adds stress tests for `cspaceRevokeCdtStrict` with deeper derivation
chains and failure scenarios.

---

#### Task M4-A: Multi-level resolution edge case tests (M-T01)

**Problem**: `resolveCapAddress` is tested only implicitly via 12-level scenario
fixtures (SCN-CSPACE-DEEP-RADIX). No standalone tests cover edge cases: zero
`radixWidth` with non-zero `guardWidth`, maximum bit depth, guard mismatch at
intermediate levels, partial bit consumption, or single-level leaf resolution.

**Design decision**: All resolution edge case tests are added to
`NegativeStateSuite.lean` in a new `runWSM4ResolveEdgeCaseChecks` section,
following the existing section pattern. Each test constructs a minimal state
with targeted CNode configurations and calls `resolveCapAddress` directly
(not through the kernel monad wrapper), enabling precise error path verification.

##### Subtask M4-A1: Guard-only CNode resolution (zero radixWidth)

**Scenario ID**: `SCN-RESOLVE-GUARD-ONLY`

**Setup**: Create a CNode with `guardWidth := 4`, `radixWidth := 0`,
`guardValue := 0xA`. The slot at index 0 holds a capability (since with
`radixWidth = 0`, the slot index is always `addr % 2^0 = addr % 1 = 0`).

**Action**: Call `resolveCapAddress rootId addr 4 st` where addr encodes
guard value `0xA` in the top 4 bits.

**Verify**:
- Resolution succeeds with `.ok { cnode := rootId, slot := ⟨0⟩ }`.
- The slot index is always 0 regardless of the address value (only the
  guard matters).

**Implementation**: In `NegativeStateSuite.lean`, add test that constructs
the CNode, verifies success, then tests with wrong guard value (0xB instead
of 0xA) and verifies `.error .invalidCapability`.

##### Subtask M4-A2: Maximum depth resolution (64 bits)

**Scenario ID**: `SCN-RESOLVE-MAX-DEPTH`

**Setup**: Create a chain of 8 CNodes, each consuming 8 bits
(`guardWidth := 0`, `radixWidth := 8`). Total = 64 bits. Each CNode at
level `i` has a slot pointing to the next CNode at level `i+1`. The last
CNode (level 7) is the leaf.

**Action**: Call `resolveCapAddress rootId addr 64 st` where addr encodes
the slot indices for each level.

**Verify**:
- Resolution succeeds through all 8 levels.
- The returned `SlotRef` points to the correct leaf CNode and slot.

**Implementation**: Build state with 8 CNodes, verify successful 64-bit
resolution. Also verify that calling with `bitsRemaining := 65` returns
`.error .illegalState` (more bits than the chain can consume).

##### Subtask M4-A3: Guard mismatch at intermediate level

**Scenario ID**: `SCN-RESOLVE-GUARD-MISMATCH-MID`

**Setup**: Create a 3-level CNode chain:
- Level 0: `guardWidth := 2`, `guardValue := 3`, `radixWidth := 2` (consumes 4 bits)
- Level 1: `guardWidth := 2`, `guardValue := 1`, `radixWidth := 2` (consumes 4 bits)
- Level 2: `guardWidth := 0`, `radixWidth := 4` (leaf, consumes 4 bits)

**Action**: Call `resolveCapAddress rootId addr 12 st` where addr has correct
guard at level 0 but wrong guard at level 1 (guard bits = 2, expected 1).

**Verify**: Returns `.error .invalidCapability` (guard mismatch at level 1).
Also verify that with correct guards at all levels, resolution succeeds.

##### Subtask M4-A4: Partial bit consumption (bits exhausted mid-level)

**Scenario ID**: `SCN-RESOLVE-PARTIAL-BITS`

**Setup**: Create a CNode with `guardWidth := 2`, `radixWidth := 4`
(consumes 6 bits per hop).

**Action**: Call `resolveCapAddress rootId addr 4 st` — only 4 bits
available but the CNode needs 6 bits (guardWidth + radixWidth = 6 > 4).

**Verify**: Returns `.error .illegalState` because `bitsRemaining < consumed`.
Also test with `bitsRemaining := 0` → `.error .illegalState` (zero bits).

##### Subtask M4-A5: Single-level leaf resolution

**Scenario ID**: `SCN-RESOLVE-SINGLE-LEVEL`

**Setup**: Create a CNode with `guardWidth := 0`, `radixWidth := 4`
(consumes exactly 4 bits). Slot 5 holds a capability.

**Action**: Call `resolveCapAddress rootId (CPtr.ofNat 5) 4 st`.

**Verify**:
- Returns `.ok { cnode := rootId, slot := ⟨5⟩ }`.
- `bitsRemaining - consumed = 0`, so the leaf branch is taken.
- The correct slot (5) is extracted from the address bits.

**Verification**: `lake build` + `test_smoke.sh` passes after all M4-A subtasks.

**Files**: `tests/NegativeStateSuite.lean`

---

#### Task M4-B: Strict revocation stress tests (M-T02)

**Problem**: `cspaceRevokeCdtStrict` is exercised only with a 3-level derivation
chain in chain9. No tests cover: (a) deep chains with >10 descendants,
(b) partial failure mid-traversal, (c) `deletedSlots` ordering guarantees.

**Design decision**: All strict revocation stress tests are added to
`OperationChainSuite.lean` as new chain functions, following the existing
chain pattern. Each test constructs its own isolated state with unique ObjIds
to avoid cross-test interference.

##### Subtask M4-B1: Deep chain strict revocation (15+ descendants)

**Scenario ID**: `SCN-REVOKE-STRICT-DEEP`

**Setup**: Create a root CNode with a capability, then use `cspaceMintWithCdt`
to build a linear derivation chain of depth 15:
root → child1 → child2 → ... → child15. Each level is a separate CNode
with one minted capability derived from the previous level.

**Action**: Call `cspaceRevokeCdtStrict` on the root slot.

**Verify**:
- Operation succeeds (no `.error`).
- `firstFailure` is `none` (all deletions succeeded).
- `deletedSlots.length = 15` (all descendants deleted).
- All descendant slots are empty after revocation
  (`lookupSlotCap` returns `none` for each).
- Root slot still exists (revocation only affects descendants).
- Invariants hold on the final state.

##### Subtask M4-B2: Partial failure mid-traversal

**Scenario ID**: `SCN-REVOKE-STRICT-PARTIAL-FAIL`

**Setup**: Create a 5-level derivation chain (root → c1 → c2 → c3 → c4 → c5).
After building the chain, delete the CNode object backing c3's slot
(replace it with a non-CNode object, causing `cspaceDeleteSlot` to fail
with `.objectNotFound` when revocation reaches c3).

**Action**: Call `cspaceRevokeCdtStrict` on the root slot.

**Verify**:
- Operation succeeds (returns `.ok`, not `.error`).
- `firstFailure` is `some` with:
  - `offendingSlot` = `some c3Addr` (the slot that couldn't be deleted).
  - `error` = `.objectNotFound`.
- `deletedSlots` contains only the slots deleted *before* c3 in BFS order.
- Slots after c3 in BFS order are NOT deleted (traversal halts at failure).
- Invariants hold on the final state.

##### Subtask M4-B3: `deletedSlots` ordering verification

**Scenario ID**: `SCN-REVOKE-STRICT-ORDER`

**Setup**: Create a branching derivation tree (not just a linear chain):
```
root → A → A1
     → B → B1
          → B2
```
This creates 5 descendants (A, B, A1, B1, B2). `descendantsOf` uses BFS via
`childrenOf` → `childMap` lookup, but sibling ordering is non-deterministic
(HashMap iteration order). Parent-before-child ordering within each sub-chain
is deterministic and verifiable.

**Action**: Call `cspaceRevokeCdtStrict` on the root slot.

**Verify**:
- All 5 descendants deleted (`deletedSlots.length = 5`).
- All deleted slots are from the expected descendant set.
- Parent-before-child ordering holds within each sub-chain (A before A1,
  B before B1, B before B2).
- `firstFailure` is `none`.
- Invariants hold on the final state.

**Verification**: `lake build` + `test_smoke.sh` passes after all M4-B subtasks.

**Files**: `tests/OperationChainSuite.lean`

---

#### M4 Dependency Graph and Execution Order

```
M4-A1 (guard-only CNode)     ─── no deps (standalone)
M4-A2 (max depth 64-bit)     ─── no deps (standalone)
M4-A3 (guard mismatch mid)   ─── no deps (standalone)
M4-A4 (partial bits)          ─── no deps (standalone)
M4-A5 (single-level leaf)    ─── no deps (standalone)
M4-B1 (deep chain 15+)       ─── no deps (standalone)
M4-B2 (partial failure)      ─── no deps (standalone)
M4-B3 (ordering)             ─── no deps (standalone)
```

All subtasks are independent and can be implemented in any order.

**Optimal execution order**: {M4-A1..A5} (parallel) → {M4-B1..B3} (parallel).
Total: 8 subtasks, 2 sequential steps.

**Deliverables**: 5 resolution edge case tests (`SCN-RESOLVE-GUARD-ONLY`,
`SCN-RESOLVE-MAX-DEPTH`, `SCN-RESOLVE-GUARD-MISMATCH-MID`,
`SCN-RESOLVE-PARTIAL-BITS`, `SCN-RESOLVE-SINGLE-LEVEL`), 3 strict revocation
stress tests (`SCN-REVOKE-STRICT-DEEP`, `SCN-REVOKE-STRICT-PARTIAL-FAIL`,
`SCN-REVOKE-STRICT-ORDER`). 8 new test scenarios; zero sorry/axiom (test-only
phase). Updated scenario catalog.

---

### Phase 5: Streaming Revocation & Documentation (WS-M5)

**Target version**: 0.16.19
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
| M3-C/D (IPC cap transfer + batch unwrap) requires cross-subsystem IPC integration | Medium | Cross-subsystem churn | Wrapper pattern (M3-E) composes new ops atop existing `endpointSendDual` without modifying its signature; all existing proofs remain valid |
| M3-E4 (wrapper preservation proofs) depend on composing CSpace + IPC invariant chains | Medium | Proof complexity | Modular composition: each wrapper proof chains existing `endpointSendDual_preserves_*` with `ipcUnwrapCaps_preserves_*`; no novel proof obligations |
| M3-F3 (`dispatchWithCap` wiring) requires receiver CSpace root at send time | Medium | Architectural mismatch | Wrapper operations read receiver TCB `cspaceRoot` internally during rendezvous; API layer passes it only for the immediate-handshake path |
| M3-B1 (findFirstEmptySlot) termination depends on bounded `limit` parameter | Low | Proof complexity | Structural recursion on `limit` (bounded by `maxExtraCaps = 3`); termination is trivial |
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
                                               M3-B (slot scanning)  ─┤       │
                                               M3-C (single-cap op)  ─┤       │
                                               M3-D (batch unwrap)   ─┤── M3 ─┤
                                               M3-E (IPC wrappers)   ─┤       │
                                               M3-F (API wiring)     ─┤       │
                                               M3-G (tests)          ─┘       │
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
M2-B8. Total: 14 subtasks, 8 sequential steps.

**Phase 3 optimal execution order**: {M3-A1, M3-A3, M3-B1, M3-F1} (parallel) →
{M3-A2, M3-B2} (parallel) → M3-C1 → {M3-C2, M3-C3} (parallel) → M3-D1 →
{M3-D2, M3-D3} (parallel) → {M3-E1, M3-E2, M3-E3, M3-F2} (parallel) →
{M3-E4, M3-F3, M3-G1, M3-G2, M3-G3, M3-G4} (parallel) → M3-G5.
Total: 20 subtasks, 9 sequential steps.

---

## 9. Workstream Summary Table

| ID | Focus | Priority | Findings |
|----|-------|----------|----------|
| **WS-M1** | Proof strengthening (10 subtasks): guard-match extraction theorem, CDT mint completeness predicate + preservation + composition, addEdge acyclicity + cycle-check helper, error-swallowing consistency theorem, stale docstrings | HIGH | M-G01, M-G02, M-G03, M-G04, M-D02 |
| **WS-M2** | Performance (14 subtasks): fused single-pass revoke fold, CDT `parentMap` O(1) parent lookup + targeted removal, shared reply-preservation lemma extraction | HIGH | M-P01, M-P02, M-P03, M-P05 |
| **WS-M3** | IPC capability transfer (20 subtasks): `CapTransferResult`/`CapTransferSummary` types, `DerivationOp.ipcTransfer` CDT variant, `findFirstEmptySlot` + correctness theorems, `ipcTransferSingleCap` + preservation, `ipcUnwrapCaps` batch + preservation, 3 IPC wrapper operations + 5 preservation theorems, `decodeExtraCapAddrs`/`resolveExtraCaps` helpers, `dispatchWithCap` wiring, 4 test scenarios | MEDIUM | M-D01, M-T03 |
| **WS-M4** | Test coverage (8 subtasks): multi-level resolution edge cases (guard-only CNode, 64-bit max depth, guard mismatch at intermediate level, partial bit consumption, single-level leaf), strict revocation stress (15+ deep chain, partial failure, BFS ordering) | MEDIUM | M-T01, M-T02 |
| **WS-M5** | Streaming BFS revocation, full documentation sync | LOW | M-P04 |
