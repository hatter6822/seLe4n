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
| M-G01 | HIGH | `Operations.lean:198–218` | `resolveCapAddress_guard_reject` theorem is incomplete — the proof only unfolds the first level and handles the guard mismatch branch, but does not close the remaining `ite` branch for the case where guard check passes. The theorem statement has the correct obligation but the proof ends with an open `split` on the `consumed = 0` branch. This needs to be closed for full guard-correctness assurance. |
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

### Phase 1: Proof Strengthening & Correctness (WS-M1)

**Focus**: Close all proof gaps and strengthen invariant coverage.
**Priority**: HIGH — proof correctness is the project's core value proposition.
**Findings addressed**: M-G01, M-G02, M-G03, M-G04, M-D02.

### Phase 2: Performance Optimization (WS-M2)

**Focus**: Eliminate redundant traversals on CSpace hot paths.
**Priority**: HIGH — directly impacts capability operation throughput.
**Findings addressed**: M-P01, M-P02, M-P03, M-P05.

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

**Target version**: 0.17.0
**Files modified**: `Operations.lean`, `Invariant/Defs.lean`, `Invariant/Authority.lean`,
`Invariant/Preservation.lean`, `Model/Object/Structures.lean`

#### Task M1-A: Complete `resolveCapAddress_guard_reject` proof (M-G01)

**Problem**: The `resolveCapAddress_guard_reject` theorem (Operations.lean:198–218) has
an incomplete proof. The theorem states that when the guard extracted from `addr` does not
match the CNode's `guardValue`, the function returns `.error .invalidCapability`. The
current proof unfolds the function and handles the initial branches but leaves the final
`split` on the `consumed = 0` conditional open.

**Implementation**:
1. Read `Operations.lean:198–218` to identify the exact proof state at the incomplete
   branch.
2. The proof needs to:
   - Handle the `consumed = 0` impossible case (contradicts `hConsPos`).
   - Handle the `bits < consumed` impossible case (contradicts `hFit`).
   - Handle the `guardExtracted ≠ guardValue` case using `hBadGuard`.
3. Close the proof with `simp [hBadGuard]` after eliminating impossible branches with
   `omega`.

**Verification**: `lake build` succeeds. Run `test_smoke.sh`.

**Files**: `SeLe4n/Kernel/Capability/Operations.lean`

#### Task M1-B: Add `cdtMintCompleteness` predicate (M-G02)

**Problem**: `cdtCompleteness` (Defs.lean:80–95) only captures node→object reachability
(CDT nodes point to existing objects). The WS-H4 spec envisions the stronger property:
every derived capability has a CDT edge from parent to child. This mint-tracking
completeness is required to prove that CDT-based revocation is exhaustive — that
`cspaceRevokeCdt` will find and delete *all* derived capabilities, not just those
whose CDT edges happen to exist.

**Implementation**:
1. Define `cdtMintCompleteness` in `Invariant/Defs.lean`:
   ```lean
   /-- Every capability created via `cspaceMintWithCdt` has a corresponding CDT edge
   from the source slot's node to the destination slot's node. -/
   def cdtMintCompleteness (st : SystemState) : Prop :=
     ∀ (src dst : CSpaceAddr) (srcNode dstNode : CdtNodeId),
       st.cdtSlotNode[src]? = some srcNode →
       st.cdtSlotNode[dst]? = some dstNode →
       ∃ edge ∈ st.cdt.edges, edge.parent = srcNode ∧ edge.child = dstNode
   ```
   The exact formulation may need refinement — the predicate should be conditioned on
   the destination capability actually being derived from the source (via target
   equality or CDT creation provenance). Consider:
   ```lean
   def cdtMintCompleteness (st : SystemState) : Prop :=
     ∀ (srcNode dstNode : CdtNodeId) (srcRef dstRef : SlotRef)
       (srcCap dstCap : Capability),
       st.cdtNodeSlot[srcNode]? = some srcRef →
       st.cdtNodeSlot[dstNode]? = some dstRef →
       SystemState.lookupSlotCap st srcRef = some srcCap →
       SystemState.lookupSlotCap st dstRef = some dstCap →
       dstCap.target = srcCap.target →
       srcNode ≠ dstNode →
       (∃ edge ∈ st.cdt.edges, edge.parent = srcNode ∧ edge.child = dstNode) ∨
       (∃ edge ∈ st.cdt.edges, edge.parent = dstNode ∧ edge.child = srcNode)
   ```
   This alternative captures bidirectional edge existence for same-target caps, which
   is more useful for revocation completeness but harder to maintain.

2. Prove `cspaceMintWithCdt` establishes the edge (by construction — `addEdge` is called).
3. Prove preservation through non-CDT operations (trivial — CDT unchanged).
4. Add to `capabilityInvariantBundle` as a 7th conjunct, or keep as a standalone
   predicate with its own preservation theorems to minimize churn on existing proofs.

**Decision point**: Whether to add to the bundle (breaking change to 60+ theorems that
destructure the bundle) or keep standalone. **Recommendation**: Keep standalone with a
named composition theorem `capabilityInvariantBundleFull` that conjoins the bundle with
`cdtMintCompleteness`. This avoids churn while providing the stronger property.

**Verification**: `lake build` succeeds. Run `test_full.sh` (theorem changes).

**Files**: `SeLe4n/Kernel/Capability/Invariant/Defs.lean`,
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean`

#### Task M1-C: Prove `addEdge_preserves_acyclicity` (M-G03)

**Problem**: `cspaceCopy`, `cspaceMove`, and `cspaceMintWithCdt` preservation theorems
require callers to supply `hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st'` as
hypotheses. This defers the cycle-check obligation. The underlying issue is that
`addEdge` can introduce cycles if the child is already an ancestor of the parent.
A theorem conditioned on the child not being an ancestor would make proofs
self-contained.

**Implementation**:
1. In `Model/Object/Structures.lean`, add:
   ```lean
   /-- Adding an edge preserves acyclicity when the child is not a descendant
   of the parent (i.e., no cycle is created). -/
   theorem addEdge_preserves_edgeWellFounded
       (cdt : CapDerivationTree) (parent child : CdtNodeId) (op : DerivationOp)
       (hAcyclic : cdt.edgeWellFounded)
       (hNoCycle : parent ∉ cdt.descendantsOf child) :
       (cdt.addEdge parent child op).edgeWellFounded
   ```
2. The proof proceeds by contradiction: assume a cycle exists in `cdt.addEdge parent child op`.
   The only new edge is `(parent, child)`. A cycle must therefore include this edge.
   But `parent ∉ cdt.descendantsOf child` means there is no path from `child` back to
   `parent` in the original CDT, so the cycle cannot close.

3. Add a companion `descendantsOf_decidable` or `notDescendant_check` runtime function
   that evaluates `parent ∉ cdt.descendantsOf child` as a `Bool` for use in kernel
   operations. This allows `cspaceCopy`/`cspaceMove`/`cspaceMintWithCdt` to check the
   precondition at runtime and return an error (e.g., `.illegalState`) if violated,
   rather than silently deferring to the caller.

4. Update preservation theorems for `cspaceCopy`, `cspaceMove`, `cspaceMintWithCdt` in
   `Preservation.lean` to use the new `addEdge_preserves_edgeWellFounded` theorem instead
   of requiring `hCdtPost` hypotheses. The updated signatures will require
   `hNoCycle : parent ∉ cdt.descendantsOf child` instead, which can be discharged from
   the runtime check.

**Breaking change assessment**: The hypothesis signatures of 3 preservation theorems
change. Callers that currently supply `hCdtPost` will need to supply `hNoCycle` instead.
Since the callers are internal (Preservation.lean, API.lean), the blast radius is
contained.

**Verification**: `lake build` succeeds. Run `test_full.sh`.

**Files**: `SeLe4n/Model/Object/Structures.lean`,
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean`,
`SeLe4n/Kernel/Capability/Operations.lean`

#### Task M1-D: Named error-swallowing consistency theorem (M-G04)

**Problem**: `cspaceRevokeCdt` (Operations.lean:649–673) swallows `cspaceDeleteSlot`
errors during descendant traversal. The fold invariant in Preservation.lean implicitly
covers CDT consistency after swallowed errors, but this is not stated as a named theorem.

**Implementation**:
1. In `Invariant/Preservation.lean`, add:
   ```lean
   /-- When `cspaceRevokeCdt` swallows a `cspaceDeleteSlot` error for a descendant,
   the CDT node is still removed, maintaining tree consistency. The resulting state
   satisfies `capabilityInvariantBundle`. -/
   theorem cspaceRevokeCdt_swallowed_error_consistent
       (stAcc stNext : SystemState) (node : CdtNodeId) (descAddr : CSpaceAddr)
       (hInv : capabilityInvariantBundle stAcc)
       (hSlot : SystemState.lookupCdtSlotOfNode stAcc node = some descAddr)
       (hErr : cspaceDeleteSlot descAddr stAcc = .error e)
       (hNext : stNext = { stAcc with cdt := stAcc.cdt.removeNode node }) :
       capabilityInvariantBundle stNext
   ```
2. The proof follows from `capabilityInvariantBundle_of_cdt_update` with
   `removeNode_edges_sub` providing the edge subset for `edgeWellFounded_sub`.

3. Update the docstring on `cspaceRevokeCdt` to document the error-swallowing design
   rationale: "Descendant deletion errors are swallowed because the CDT node is removed
   regardless, preventing stale CDT references. The strict variant
   `cspaceRevokeCdtStrict` is available for callers requiring error visibility."

**Verification**: `lake build` succeeds. Run `test_smoke.sh`.

**Files**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`,
`SeLe4n/Kernel/Capability/Operations.lean`

#### Task M1-E: Update stale `cspaceRevoke` docstring (M-D02)

**Problem**: `cspaceRevoke` (Operations.lean:486–487) docstring says "derivation-tree
state is still out-of-scope for the active slice" but `cspaceRevokeCdt` (lines 649–673)
already implements full CDT traversal.

**Implementation**:
1. Update the `cspaceRevoke` docstring to:
   ```
   /-- Revoke capabilities with the same target as the source in the containing CNode.

   This is the local (single-CNode) revocation variant. For cross-CNode revocation
   using CDT traversal, see `cspaceRevokeCdt` and `cspaceRevokeCdtStrict`.

   The source slot remains present and sibling slots naming the same target are removed. -/
   ```

**Verification**: `lake build` succeeds.

**Files**: `SeLe4n/Kernel/Capability/Operations.lean`

---

### Phase 2: Performance Optimization (WS-M2)

**Target version**: 0.17.1
**Files modified**: `Operations.lean`, `Model/Object/Structures.lean`,
`Invariant/Preservation.lean`, `Invariant/Defs.lean`

#### Task M2-A: Fuse revoke fold with capability ref clearing (M-P01)

**Problem**: `cspaceRevoke` (Operations.lean:489–505) constructs a `revokedRefs` list
by folding over the CNode's HashMap, then passes this list to `clearCapabilityRefs`
which iterates over it again. This is two O(m) passes where m is the number of revoked
slots.

**Implementation**:
1. Define a fused `revokeAndClearRefs` helper that combines the fold with ref clearing:
   ```lean
   /-- Fused revoke: filter CNode slots and clear capability refs in a single pass. -/
   private def revokeAndClearRefsState
       (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
       (cnodeId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
     cn.slots.fold (fun stAcc s c =>
       if s != sourceSlot && c.target == target then
         { stAcc with lifecycle := { stAcc.lifecycle with
             capabilityRefs := stAcc.lifecycle.capabilityRefs.erase { cnode := cnodeId, slot := s } } }
       else stAcc) st
   ```
2. Prove semantic equivalence:
   ```lean
   theorem revokeAndClearRefsState_eq_clearCapabilityRefsState
       (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
       (cnodeId : SeLe4n.ObjId) (st : SystemState) :
       revokeAndClearRefsState cn sourceSlot target cnodeId st =
       clearCapabilityRefsState (revokedRefsList cn sourceSlot target cnodeId) st
   ```
3. Update `cspaceRevoke` to use the fused path.
4. Re-prove `cspaceRevoke_preserves_capabilityInvariantBundle` using the equivalence
   theorem — the proof should be mechanical (rewrite with the equivalence, then
   apply the existing proof).

**Performance impact**: Eliminates one O(m) pass on every revoke operation.

**Verification**: `lake build` succeeds. Run `test_full.sh`. Verify fixture stability.

**Files**: `SeLe4n/Kernel/Capability/Operations.lean`,
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean`,
`SeLe4n/Kernel/Capability/Invariant/Authority.lean`

#### Task M2-B: Add CDT `parentMap` index (M-P02, M-P03)

**Problem**: `CapDerivationTree.parentOf` scans the full edge list (`O(E)`) to find a
node's parent. `removeAsChild` and `removeAsParent` also scan the full edge list and
rebuild `childMap`. With `childMap` already providing O(1) child lookup, a symmetric
`parentMap` would complete the picture.

**Implementation**:
1. Extend `CapDerivationTree` in `Structures.lean`:
   ```lean
   structure CapDerivationTree where
     edges : List CapDerivationEdge := []
     childMap : Std.HashMap CdtNodeId (List CdtNodeId) := {}
     parentMap : Std.HashMap CdtNodeId CdtNodeId := {}
     deriving Repr
   ```
2. Update `addEdge` to maintain `parentMap`:
   ```lean
   def addEdge (cdt : CapDerivationTree) (parent child : CdtNodeId) (op : DerivationOp) :
       CapDerivationTree :=
     { edges := { parent, child, op } :: cdt.edges,
       childMap := cdt.childMap.alter parent (fun cs => some (child :: (cs.getD []))),
       parentMap := cdt.parentMap.insert child parent }
   ```
3. Rewrite `parentOf` to use `parentMap`:
   ```lean
   def parentOf (cdt : CapDerivationTree) (node : CdtNodeId) : Option CdtNodeId :=
     cdt.parentMap[node]?
   ```
4. Update `removeAsChild`, `removeAsParent`, `removeNode` to maintain `parentMap`
   using targeted erasure/updates rather than full-list rebuilds.
5. Define `parentMapConsistent` invariant (symmetric to `childMapConsistent`):
   ```lean
   def parentMapConsistent (cdt : CapDerivationTree) : Prop :=
     ∀ (child parent : CdtNodeId),
       cdt.parentMap[child]? = some parent ↔
       ∃ edge ∈ cdt.edges, edge.parent = parent ∧ edge.child = child
   ```
6. Prove `addEdge_parentMapConsistent`, `removeNode_parentMapConsistent`.

**Performance impact**: `parentOf` goes from O(E) to O(1). `removeAsChild`/
`removeAsParent` go from O(E) filter + rebuild to O(1) erasure.

**Breaking change**: `CapDerivationTree` gains a new field. All construction sites
(`.empty`, `{ edges := ..., childMap := ... }`) need to add `parentMap`. This is
mechanical but affects `Operations.lean`, `Structures.lean`, and test fixtures.

**Verification**: `lake build` succeeds. Run `test_full.sh`. Verify CDT-related
test scenarios pass.

**Files**: `SeLe4n/Model/Object/Structures.lean`,
`SeLe4n/Kernel/Capability/Operations.lean`,
`SeLe4n/Kernel/Capability/Invariant/Defs.lean`,
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean`

#### Task M2-C: Extract shared reply-preservation lemma (M-P05)

**Problem**: `endpointReply_preserves_capabilityInvariantBundle` (Preservation.lean:
780–864) duplicates the CNode-backward-preservation proof across both reply-target
branches. The shared `suffices` body at line 812 partially addresses this, but the
two branches before it still have redundant `revert`/`cases` patterns.

**Implementation**:
1. Extract:
   ```lean
   private theorem capabilityInvariantBundle_of_storeTcbAndEnsureRunnable
       (st st' : SystemState) (target : SeLe4n.ThreadId)
       (ipc : ThreadIpcState) (msg : Option IpcMessage)
       (hInv : capabilityInvariantBundle st)
       (hTcb : storeTcbIpcStateAndMessage st target ipc msg = .ok st')
       (hCnodeBackward : ∀ cid cn, st'.objects[cid]? = some (.cnode cn) →
         st.objects[cid]? = some (.cnode cn)) :
       capabilityInvariantBundle (ensureRunnable st' target)
   ```
2. Rewrite `endpointReply_preserves_capabilityInvariantBundle` to call this lemma
   in both branches, eliminating ~40 lines of duplicated proof.

**Verification**: `lake build` succeeds. Run `test_smoke.sh`.

**Files**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`

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
| M1-C (`addEdge_preserves_acyclicity`) proof is harder than expected due to BFS fuel | Medium | Delays Phase 1 | Fall back to explicit `descendantsOf` induction; keep hypothesis pattern as escape hatch |
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
M1-A (guard proof)     ─┐
M1-B (mint complete.)  ─┤
M1-C (addEdge acycl.)  ─┤── M1 complete ── M2-A (fuse revoke)   ─┐
M1-D (error theorem)   ─┤                  M2-B (parentMap)      ─┤── M2 complete
M1-E (docstring)       ─┘                  M2-C (reply lemma)    ─┘       │
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

M1 must complete before M2 (M1-C provides `addEdge_preserves_acyclicity` needed
by M2-B's `parentMap` consistency proofs). M3 can proceed in parallel with M2
after M1 completes. M4 can proceed after M3-D (needs IPC transfer tests). M5
depends on all prior phases for documentation completeness.

---

## 9. Workstream Summary Table

| ID | Focus | Priority | Findings |
|----|-------|----------|----------|
| **WS-M1** | Proof strengthening: guard-reject completion, CDT mint completeness, addEdge acyclicity, error-swallowing theorem, stale docstring | HIGH | M-G01, M-G02, M-G03, M-G04, M-D02 |
| **WS-M2** | Performance: fused revoke fold, CDT parentMap index, shared reply lemma | HIGH | M-P01, M-P02, M-P03, M-P05 |
| **WS-M3** | IPC capability transfer: model, integrate, prove, test | MEDIUM | M-D01, M-T03 |
| **WS-M4** | Test coverage: multi-level resolution edge cases, strict revocation stress | MEDIUM | M-T01, M-T02 |
| **WS-M5** | Streaming BFS revocation, full documentation sync | LOW | M-P04 |
