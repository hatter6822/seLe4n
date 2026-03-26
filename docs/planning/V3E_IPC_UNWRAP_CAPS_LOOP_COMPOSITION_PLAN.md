# V3-E: ipcUnwrapCaps Grant=true Loop Composition

**Workstream**: WS-V Phase V3 — Proof Chain Hardening
**Audit Finding**: M-PRF-2 (MEDIUM severity)
**Sub-task**: V3-E (5 sequential units: V3-E1 through V3-E5)
**Dependencies**: V3-D1 (CDT acyclicity audit — complete), V2 (API Surface — complete)
**Gate Conditions**: `lake build` succeeds; zero `sorry`; `test_full.sh` green
**Estimated Scope**: ~200-350 lines Lean proof code across 2 files

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Problem Statement](#2-problem-statement)
3. [Current State Analysis](#3-current-state-analysis)
4. [Technical Design](#4-technical-design)
5. [V3-E1: Expose ipcUnwrapCapsLoop](#5-v3-e1-expose-ipcunwrapcapsloop)
6. [V3-E2: Define Loop Invariant Predicate](#6-v3-e2-define-loop-invariant-predicate)
7. [V3-E3: Prove Base Case](#7-v3-e3-prove-base-case)
8. [V3-E4: Prove Inductive Step](#8-v3-e4-prove-inductive-step)
9. [V3-E5: Compose Full Loop Theorem](#9-v3-e5-compose-full-loop-theorem)
10. [Execution Order and Dependency Graph](#10-execution-order-and-dependency-graph)
11. [Risk Assessment and Mitigations](#11-risk-assessment-and-mitigations)
12. [Testing and Validation Strategy](#12-testing-and-validation-strategy)
13. [Documentation Synchronization](#13-documentation-synchronization)

---

## 1. Executive Summary

The per-step theorem `ipcTransferSingleCap_preserves_capabilityInvariantBundle`
(Preservation.lean:1910-1960) is fully proved for single capability transfers.
However, when `Grant=true`, the IPC rendezvous transfers capabilities in bulk
via the **private** `ipcUnwrapCapsLoop` recursive helper. No composition proof
exists that threads the per-step guarantee across all loop iterations to
establish the end-to-end property:

> **Goal**: `ipcUnwrapCaps msg sender receiver slotBase true st = .ok (summary, st')`
> implies `capabilityInvariantBundle st'` given `capabilityInvariantBundle st`.

This is the only remaining gap in the capability transfer preservation chain.
The `Grant=false` path is already proved trivially
(`ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant`, line 1985).

**The core challenge is threefold**:
1. `ipcUnwrapCapsLoop` is `private`, blocking external reasoning
2. The loop uses fuel-indexed recursion that requires a formal induction proof
3. Two hypotheses (`hSlotCapacity` and `hCdtPost`) must be threaded through
   each iteration, because each `ipcTransferSingleCap` call modifies the state

This plan decomposes the work into 5 sequential units (V3-E1 through V3-E5),
each building on the previous. Total estimated proof code: ~200-350 lines.

---

## 2. Problem Statement

### 2.1. The Proof Gap

The M-PRF-2 audit finding identifies that the `capabilityInvariantBundle`
preservation chain has a composition gap at the IPC cap-transfer loop boundary.
Specifically:

```
ipcUnwrapCaps (Grant=true)
  └── ipcUnwrapCapsLoop       ← private, fuel-indexed recursion
        └── ipcTransferSingleCap  ← per-step preservation PROVED ✓
```

The per-step theorem proves that a single `ipcTransferSingleCap` call preserves
`capabilityInvariantBundle`, but this cannot be composed across the loop because:

1. **Privacy barrier**: `ipcUnwrapCapsLoop` carries Lean's `@[private]` attribute
   (CapTransfer.lean:36), making it invisible to the Lean elaborator outside
   the declaring module. Theorems in `Preservation.lean` cannot reference it.

2. **Hypothesis threading**: Each iteration modifies the state, so the
   `hSlotCapacity` and `hCdtPost` preconditions must be re-established for
   each intermediate state. This requires a formal induction that:
   - Proves `capabilityInvariantBundle stᵢ → capabilityInvariantBundle stᵢ₊₁`
   - Propagates `hSlotCapacity` through the modified CNode (slot count changes)
   - Propagates `hCdtPost` through CDT edge additions (acyclicity changes)

3. **Fuel-indexed termination**: The loop recurses on `fuel : Nat` with
   structural termination. The induction proof must follow this structure:
   match on `fuel`, then handle both the base case (fuel=0 or out-of-bounds
   index) and the inductive step (fuel=n+1 with valid index).

### 2.2. Security Impact

Without this proof, the kernel cannot guarantee that Grant=true IPC transfers
preserve capability invariants. In the worst case, a malicious or buggy sender
could trigger a sequence of cap transfers that violates:
- **Slot uniqueness** (`cspaceSlotUnique`): two caps in the same slot
- **CDT acyclicity** (`cdtAcyclicity`): cyclic derivation chains
- **Slot count bounds** (`cspaceSlotCountBounded`): CNode overflow

Closing this gap is a prerequisite for the end-to-end invariant composition
that covers the full IPC rendezvous path.

### 2.3. Why This Is Non-Trivial

The existing codebase has two proven fuel-indexed induction patterns that serve
as templates (see Section 4.1), but `ipcUnwrapCapsLoop` introduces unique
complexity:

- **CDT-expanding semantics**: Unlike `streamingRevokeBFS` (CDT-shrinking,
  where acyclicity is preserved by edge subset), each loop iteration **adds**
  a CDT edge (`.ipcTransfer`). Acyclicity must be externalized (`hCdtPost`)
  and threaded per-iteration.

- **Slot capacity mutation**: Each successful `.installed` result consumes a
  slot in the receiver's CNode, so `hSlotCapacity` must account for the
  decreasing free-slot count across iterations.

- **Error continuation**: Unlike typical fold patterns, errors in one iteration
  do NOT terminate the loop — the next cap is still processed. The proof must
  handle both the error path (state unchanged by that iteration) and the
  success path (state modified).

---

## 3. Current State Analysis

### 3.1. ipcUnwrapCapsLoop (CapTransfer.lean:36-63)

```lean
private def ipcUnwrapCapsLoop
    (caps : Array Capability)
    (senderCspaceRoot : SeLe4n.ObjId)
    (receiverCspaceRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot)
    (accResults : Array CapTransferResult)
    (fuel : Nat) : Kernel CapTransferSummary
```

**Key semantics**:
- Structural recursion on `fuel` (initialized to `caps.size`)
- Base: `fuel = 0` or `caps[idx]? = none` → return accumulator, state unchanged
- Step: calls `ipcTransferSingleCap`, then recurses with `fuel - 1`
- On error: pushes `.noSlot`, advances `nextBase` by 1, recurses with same state
- On `.installed`: advances `nextBase` by 1, recurses with modified state `stNext`
- On other result: keeps `nextBase` unchanged, recurses with modified state `stNext`

### 3.2. ipcTransferSingleCap Preservation (Preservation.lean:1910-1960)

```lean
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

**Hypothesis analysis**:
- `hInv`: Pre-state bundle — available from the previous iteration's post-state
- `hSlotCapacity`: Receiver CNode can accommodate insertion — must be re-proved
  after each successful insertion modifies the CNode's slot map
- `hCdtPost`: CDT completeness + acyclicity in post-state — externalized; must
  be supplied for each intermediate state in the loop

### 3.3. Existing Fuel-Indexed Induction Patterns

Two proven patterns exist in Preservation.lean that serve as templates:

**Pattern A: `revokeCdtFold_preserves` (lines 885-905)** — List induction
```lean
induction nodes generalizing stInit stFinal with
| nil => exact hInv
| cons node rest ih =>
    cases hStep : revokeCdtFoldBody (.ok ((), stInit)) node with
    | error e => contradiction
    | ok val =>
        have ⟨hInvMid, hKMid⟩ := revokeCdtFoldBody_preserves ...
        exact ih stMid stFinal hInvMid hKMid hFold
```

**Pattern B: `streamingRevokeBFS_preserves` (lines 1129-1154)** — Nat induction on fuel
```lean
induction fuel generalizing queue stInit stFinal with
| zero =>
    cases queue with
    | nil => exact hInv
    | cons _ _ => contradiction
| succ n ih =>
    cases queue with
    | nil => exact hInv
    | cons node rest =>
        cases hProc : processRevokeNode stInit node with
        | error e => contradiction
        | ok stNext =>
            have hStepInv := step_preserves ...
            exact ih _ _ _ hStepInv hKPost hBFS
```

**Key difference for V3-E**: Both patterns are CDT-shrinking (edge removal),
so acyclicity is proven internally via `edgeWellFounded_sub`. The
`ipcUnwrapCapsLoop` is CDT-expanding (edge addition), so acyclicity must be
**externalized** as a per-iteration hypothesis.

### 3.4. Existing Loop Preservation Theorems in CapTransfer.lean

Eight private theorems already prove various properties through the loop via
fuel-indexed induction (CapTransfer.lean:93-494):

| Theorem | Property Preserved |
|---------|-------------------|
| `ipcUnwrapCapsLoop_preserves_scheduler` | `st'.scheduler = st.scheduler` |
| `ipcUnwrapCapsLoop_preserves_services` | `st'.services = st.services` |
| `ipcUnwrapCapsLoop_preserves_objects_ne` | Non-receiver objects unchanged |
| `ipcUnwrapCapsLoop_preserves_ntfn_objects` | Notification objects unchanged |
| `ipcUnwrapCapsLoop_preserves_ep_objects` | Endpoint objects unchanged |
| `ipcUnwrapCapsLoop_preserves_tcb_objects` | TCB objects unchanged |
| `ipcUnwrapCapsLoop_preserves_cnode_at_root` | Receiver stays as CNode |
| `ipcUnwrapCapsLoop_receiverRoot_not_ntfn` | Receiver is not notification |

These theorems prove simpler frame-condition properties (field equality,
type preservation) that do not require threading `hSlotCapacity` or `hCdtPost`.
They demonstrate that the induction structure works, but the
`capabilityInvariantBundle` composition is significantly more complex because
it requires hypothesis propagation through state mutations.

### 3.5. The noGrant Path (Complete)

```lean
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant
    -- ... (Preservation.lean:1985-1996)
    capabilityInvariantBundle st'
```

Trivially proved: when `endpointGrantRight = false`, the state is unchanged.

---

## 4. Technical Design

### 4.1. Overall Proof Architecture

The proof follows the **fuel-indexed induction with externalized CDT hypothesis**
pattern. The architecture mirrors `streamingRevokeBFS_preserves` (Pattern B)
but adapts the hypothesis threading for CDT-expanding operations.

```
ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant  (V3-E5)
  │
  ├── Grant=false case: delegate to existing _noGrant theorem
  │
  └── Grant=true case: unfold ipcUnwrapCaps, apply loop lemma
        │
        └── ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle  (V3-E3/E4)
              │
              ├── Base case (fuel=0 or idx ≥ caps.size):     (V3-E3)
              │     state unchanged, exact hInv
              │
              └── Inductive step (fuel=n+1, valid index):    (V3-E4)
                    │
                    ├── Error path: ipcTransferSingleCap fails
                    │   → state unchanged for this cap
                    │   → recurse with same state, exact ih
                    │
                    └── Success path: ipcTransferSingleCap succeeds
                        │
                        ├── Apply ipcTransferSingleCap_preserves_capabilityInvariantBundle
                        │   → obtain capabilityInvariantBundle stNext
                        │
                        ├── Re-establish hSlotCapacity for stNext
                        │   → use ipcUnwrapCaps_preserves_cnode_at_root
                        │   → use slot count bound propagation
                        │
                        ├── Supply hCdtPost for stNext
                        │   → externalize to caller (same pattern as single-step)
                        │
                        └── Apply inductive hypothesis with stNext
```

### 4.2. Hypothesis Threading Strategy

The critical design decision is how `hSlotCapacity` and `hCdtPost` are handled
across iterations.

**Option A: Fully externalized (chosen)**
Both hypotheses are externalized to the top-level theorem. The loop theorem
takes `hSlotCapacity` and `hCdtPost` as universally-quantified per-state
hypotheses:

```lean
-- hSlotCapacity applies to ANY intermediate state reachable via the loop
(hSlotCapacity : ∀ (stI : SystemState),
    capabilityInvariantBundle stI →
    ∀ cn cap, stI.objects[receiverRoot]? = some (.cnode cn) →
      ∀ s, (cn.insert s cap).slotCountBounded)
-- hCdtPost applies to ANY intermediate state produced by ipcTransferSingleCap
(hCdtPost : ∀ (stI stJ : SystemState) (cap : Capability) ...,
    ipcTransferSingleCap ... stI = .ok (result, stJ) →
    cdtCompleteness stJ ∧ cdtAcyclicity stJ)
```

This is the cleanest approach and matches the established pattern where
CDT-expanding operations externalize their acyclicity hypothesis. The caller
(API layer) is responsible for discharging these obligations.

**Option B: Per-iteration with strengthened invariant (rejected)**
Thread a stronger loop invariant that implies `hSlotCapacity` and `hCdtPost`
at each step. Rejected because:
- `hCdtPost` depends on the **post-state** of each `ipcTransferSingleCap` call,
  which is not known until execution. Strengthening the pre-state invariant to
  imply post-state CDT properties would require proving cycle-freedom of
  arbitrary CDT edge additions — exactly what the externalization pattern avoids.
- Adds unnecessary proof complexity with no benefit over Option A.

### 4.3. Slot Capacity Propagation

Each successful `.installed` result inserts a capability into the receiver's
CNode, consuming one slot. The `hSlotCapacity` hypothesis must account for this.

**Strategy**: Use a universally-quantified `hSlotCapacity` that holds for any
intermediate state where the receiver is still a CNode. This works because:
1. `ipcUnwrapCaps_preserves_cnode_at_root` guarantees the receiver stays as a CNode
2. `cspaceSlotCountBounded` is part of `capabilityInvariantBundle`, so if the
   bundle holds at state `stI`, the slot count is bounded
3. The `hSlotCapacity` hypothesis is stated over any CNode at `receiverRoot`,
   so it applies to the mutated CNode after insertion

The key lemma needed is:
```lean
-- After inserting a cap into the receiver CNode, the NEXT insertion
-- still satisfies slotCountBounded (given the overall bound holds)
```

This follows from `cspaceSlotCountBounded` being part of the bundle: if the
bundle holds at `stᵢ₊₁`, then slot count is already bounded, and the next
insertion's `hSlotCapacity` is satisfiable.

### 4.4. Error Path Handling

When `ipcTransferSingleCap` returns `.error`, the loop pushes `.noSlot` and
recurses with the **original state** `st` (not `stNext`). This is visible in
CapTransfer.lean:53-56:

```lean
| .error _e =>
    ipcUnwrapCapsLoop caps senderCspaceRoot receiverCspaceRoot
      (idx + 1) (SeLe4n.Slot.ofNat (nextBase.toNat + 1))
      (accResults.push .noSlot) fuel' st  -- same st!
```

The proof for this path is trivial: since the state is unchanged, the
inductive hypothesis applies directly with the original `hInv`.

### 4.5. File Placement

| Sub-task | File | Rationale |
|----------|------|-----------|
| V3-E1 | `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean` | Visibility change at source |
| V3-E2 | `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` | Invariant predicates live here |
| V3-E3 | `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` | Base case proof |
| V3-E4 | `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` | Inductive step proof |
| V3-E5 | `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` | Top-level composition |

All proof code lands in `Preservation.lean` after the existing
`ipcTransferSingleCap_preserves_capabilityInvariantBundle` theorem (after
line 1960) and before the `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant`
theorem (line 1985). The comment block at lines 1962-1980 documents this
exact gap and will be replaced by the actual proofs.

---

## 5. V3-E1: Expose ipcUnwrapCapsLoop

**Scope**: Small (~5-10 lines changed)
**File**: `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean`
**Prerequisite**: None

### 5.1. Problem

`ipcUnwrapCapsLoop` is declared with `private def` (line 36), which prevents
the Lean elaborator from resolving the name in any file that imports
`CapTransfer.lean`. All proof theorems in `Preservation.lean` that need to
reason about the loop's recursion structure are blocked.

### 5.2. Approach Options

**Option 1: Remove `private` (recommended)**

Simply change `private def ipcUnwrapCapsLoop` to `def ipcUnwrapCapsLoop`.

Pros:
- Simplest change (1 line)
- Allows direct structural reasoning in proof files
- Matches the existing pattern where the 8 private loop theorems in the same
  file (lines 93-494) already reference `ipcUnwrapCapsLoop` by name
- The function is already effectively part of the module's proof surface since
  the private theorems expose its behavior

Cons:
- Exposes an internal implementation detail to downstream importers
- Mild API surface expansion (but `ipcUnwrapCapsLoop` is not user-facing)

**Option 2: Add a public wrapper with identical signature (not recommended)**

```lean
def ipcUnwrapCapsLoopPub := @ipcUnwrapCapsLoop
```

Rejected because:
- Adds indirection without benefit (proofs must unfold the wrapper anyway)
- The private theorems in the same file already establish behavioral properties
- Lean's `@[private]` is a soft encapsulation, not a security boundary

**Option 3: Add `@[simp]` unfolding lemma (not recommended)**

```lean
@[simp] theorem ipcUnwrapCapsLoop_unfold ...
```

Rejected because:
- The loop has a complex match structure that doesn't simplify well
- `@[simp]` would apply the unfolding globally, potentially causing tactic
  slowdowns in unrelated proofs
- The induction proof needs to `match` on fuel, not unfold via simp

### 5.3. Implementation Steps

1. **Edit CapTransfer.lean line 36**: Change `private def ipcUnwrapCapsLoop` to
   `def ipcUnwrapCapsLoop`
2. **Remove `private` from the 8 loop theorems** (lines 93-494): Since these
   theorems reference `ipcUnwrapCapsLoop` by name and will now be usable
   externally, remove their `private` annotations to make them available as
   helper lemmas for V3-E3/E4. The specific theorems to expose:
   - `ipcUnwrapCapsLoop_preserves_scheduler` (line 93)
   - `ipcUnwrapCapsLoop_preserves_services` (line 139)
   - `ipcUnwrapCapsLoop_preserves_objects_ne` (line 186)
   - `ipcUnwrapCapsLoop_preserves_ntfn_objects` (line 237)
   - `ipcUnwrapCapsLoop_preserves_ep_objects` (line 326)
   - `ipcUnwrapCapsLoop_preserves_tcb_objects` (line 380)
   - `ipcUnwrapCapsLoop_preserves_cnode_at_root` (line 436)
   - `ipcUnwrapCapsLoop_receiverRoot_not_ntfn` (line 454)
3. **Verify build**: `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Operations.CapTransfer`
4. **Verify downstream**: `source ~/.elan/env && lake build SeLe4n.Kernel.Capability.Invariant.Preservation`

### 5.4. Acceptance Criteria

- [ ] `ipcUnwrapCapsLoop` is accessible from `Preservation.lean` without error
- [ ] All 8 loop helper theorems are public
- [ ] Both modules build with zero errors
- [ ] No `sorry` introduced
- [ ] Existing tests (`test_smoke.sh`) pass

---

## 6. V3-E2: Define Loop Invariant Predicate

**Scope**: Small (~15-25 lines)
**File**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Prerequisite**: V3-E1 complete

### 6.1. Design

The loop invariant is **not** a new standalone predicate. Instead, it is the
existing `capabilityInvariantBundle` augmented with two per-iteration
hypotheses that are threaded through the induction. This design was chosen
because:

1. **Minimality**: `capabilityInvariantBundle` already bundles all 7 required
   properties. Adding a wrapper would duplicate the definition.
2. **Composability**: The per-step theorem
   `ipcTransferSingleCap_preserves_capabilityInvariantBundle` already takes
   `capabilityInvariantBundle` as input and produces it as output. Using the
   same predicate eliminates conversion overhead.
3. **Precedent**: The existing `streamingRevokeBFS_preserves` and
   `revokeCdtFold_preserves` patterns use `capabilityInvariantBundle` directly
   as the loop invariant, not a wrapper.

### 6.2. Hypothesis Formalization

The two per-iteration hypotheses that must be threaded are formalized as
universally-quantified predicates over arbitrary intermediate states:

```lean
/-- V3-E: Slot capacity hypothesis — for any intermediate state where the
receiver is a CNode, inserting any capability into any slot keeps the
slot count bounded. This is the per-iteration precondition for
`ipcTransferSingleCap_preserves_capabilityInvariantBundle`. -/
def ipcUnwrapCapsLoop_slotCapacityHyp
    (receiverRoot : SeLe4n.ObjId) (caps : Array Capability) : Prop :=
  ∀ (stI : SystemState) (cap : Capability),
    cap ∈ caps.toList →
    capabilityInvariantBundle stI →
    ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
      ∀ s, (cn.insert s cap).slotCountBounded

/-- V3-E: CDT post-state hypothesis — for any intermediate state pair
where ipcTransferSingleCap succeeds, the post-state has CDT completeness
and acyclicity. This externalizes the CDT proof obligation to the caller. -/
def ipcUnwrapCapsLoop_cdtPostHyp
    (receiverRoot : SeLe4n.ObjId) : Prop :=
  ∀ (stI stJ : SystemState) (cap : Capability) (senderSlot : CSpaceAddr)
    (slotBase : SeLe4n.Slot) (scanLimit : Nat) (result : CapTransferResult),
    capabilityInvariantBundle stI →
    ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit stI
      = .ok (result, stJ) →
    cdtCompleteness stJ ∧ cdtAcyclicity stJ
```

### 6.3. Alternative: Inline Hypotheses (Simpler but Verbose)

Instead of defining named predicates, the hypotheses can be inlined directly
into the loop theorem signature. This avoids new definitions but makes the
theorem statement longer:

```lean
theorem ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle
    ...
    (hSlotCap : ∀ stI cap, cap ∈ caps.toList → capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCdtPost : ∀ stI stJ cap senderSlot slotBase scanLimit result,
        capabilityInvariantBundle stI →
        ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit stI
          = .ok (result, stJ) →
        cdtCompleteness stJ ∧ cdtAcyclicity stJ)
    ...
```

**Decision**: Use the inline approach if the predicate definitions add no
reuse value beyond this single theorem. Use named predicates if V3-E5 or
future theorems need to reference them. The implementation should start with
inline hypotheses and refactor to named predicates only if needed.

### 6.4. Implementation Steps

1. **Read Preservation.lean lines 1960-1997** to identify the exact insertion
   point (between `ipcTransferSingleCap_preserves_capabilityInvariantBundle`
   and the M3-D3 comment block)
2. **Draft the loop theorem signature** with inline hypotheses (do not add
   the proof body yet — use `sorry` temporarily during V3-E2, replaced in
   V3-E3/E4)
3. **Verify build**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`
   — the `sorry` will generate a warning but not an error
4. **Note**: The `sorry` is temporary scaffolding only. It MUST be removed
   by V3-E4 completion. Do not commit with `sorry` in production proof surface.

### 6.5. Acceptance Criteria

- [ ] Loop theorem signature type-checks (with `sorry` body)
- [ ] Hypothesis types correctly capture the per-iteration obligations
- [ ] Module builds without error
- [ ] Signature is consistent with `ipcTransferSingleCap_preserves_capabilityInvariantBundle`

---

## 7. V3-E3: Prove Base Case

**Scope**: Small (~15-25 lines)
**File**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Prerequisite**: V3-E2 complete (theorem signature exists)

### 7.1. Base Cases

The loop has **two** base cases, both trivial:

**Base Case 1: `fuel = 0`**
```lean
match fuel with
| 0 => fun st => .ok ({ results := accResults }, st)
```
When fuel is exhausted, the loop returns the accumulator and the **unchanged**
state. Since `st' = st`, the conclusion `capabilityInvariantBundle st'` follows
directly from `hInv : capabilityInvariantBundle st`.

**Base Case 2: `caps[idx]? = none` (index out of bounds)**
```lean
| fuel' + 1 =>
    match caps[idx]? with
    | none => fun st => .ok ({ results := accResults }, st)
```
When the index exceeds the array bounds, the loop terminates early. Again,
`st' = st`, so the conclusion is immediate.

### 7.2. Proof Sketch

```lean
induction fuel generalizing idx nextBase accResults st with
| zero =>
    -- fuel = 0: loop returns immediately
    simp [ipcUnwrapCapsLoop] at hStep
    obtain ⟨_, rfl⟩ := hStep
    exact hInv
| succ n ih =>
    -- fuel = n + 1: check caps[idx]?
    simp only [ipcUnwrapCapsLoop] at hStep
    cases hCap : caps[idx]? with
    | none =>
        -- Index out of bounds: loop returns immediately
        simp [hCap] at hStep
        obtain ⟨_, rfl⟩ := hStep
        exact hInv
    | some cap =>
        -- Inductive step (V3-E4)
        ...
```

### 7.3. Implementation Steps

1. **Begin the induction proof** in the loop theorem body
2. **Handle the `zero` case**: unfold `ipcUnwrapCapsLoop`, extract state
   equality, apply `hInv`
3. **Handle the `none` case in `succ`**: unfold, case split on `caps[idx]?`,
   handle `none` branch
4. **Leave the `some cap` branch** for V3-E4 (use `sorry` temporarily)
5. **Verify build**: module compiles with the `sorry` in the `some` branch

### 7.4. Validation

The base case proof should be ~10-15 lines. Verify by reading the proof term
and confirming that:
- The `zero` branch produces `exact hInv` (not a tactic chain)
- The `none` branch produces `exact hInv`
- Both branches correctly extract `rfl : st' = st` from the step hypothesis

### 7.5. Acceptance Criteria

- [ ] Base cases (fuel=0 and idx out-of-bounds) are fully proved
- [ ] No `sorry` in base case branches
- [ ] `sorry` remains only in the `some cap` branch (V3-E4 scope)
- [ ] Module builds without error (base case only; `sorry` in inductive step is expected)

---

## 8. V3-E4: Prove Inductive Step

**Scope**: Medium (~80-150 lines)
**File**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Prerequisite**: V3-E3 complete (base cases proved)

This is the most complex sub-task. It handles the `some cap` branch in the
`succ n` case of the fuel induction.

### 8.1. Case Analysis

After matching `caps[idx]? = some cap`, the loop calls `ipcTransferSingleCap`.
The result determines the proof path:

```
ipcTransferSingleCap cap senderSlot receiverRoot nextBase maxExtraCaps st
  │
  ├── .error _e  →  Error path (state unchanged for this cap)
  │     Loop pushes .noSlot and recurses with SAME state `st`
  │     Proof: apply ih directly with original hInv
  │
  └── .ok (result, stNext)  →  Success path (state modified)
        │
        ├── result = .installed cnode slot
        │     nextBase advances by 1
        │     stNext has modified CNode (new cap inserted) and CDT (new edge)
        │
        └── result = .noSlot (or other)
              nextBase unchanged
              stNext still modified (partial state changes before .noSlot)
```

### 8.2. Error Path Proof

```lean
simp [hCap] at hStep
cases hTransfer : ipcTransferSingleCap cap
    { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
    receiverRoot nextBase maxExtraCaps st with
| error e =>
    -- State unchanged: loop recurses with same st
    simp [hTransfer] at hStep
    -- hStep now equates to ipcUnwrapCapsLoop ... fuel' st = .ok (summary, st')
    exact ih (idx + 1) (SeLe4n.Slot.ofNat (nextBase.toNat + 1))
             (accResults.push .noSlot) st hInv hStep
```

This is straightforward: since the error path recurses with the same state
`st`, the inductive hypothesis applies with the original `hInv`.

### 8.3. Success Path Proof — Core Chain

The success path is the heart of V3-E. After `ipcTransferSingleCap` succeeds
with `.ok (result, stNext)`:

**Step 1: Obtain per-step preservation**
```lean
| ok pair =>
    obtain ⟨result, stNext⟩ := pair
    -- Apply the per-step theorem
    have hInvNext := ipcTransferSingleCap_preserves_capabilityInvariantBundle
      st stNext cap { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
      receiverRoot nextBase maxExtraCaps result
      hInv
      (hSlotCap st cap hCapMem hInv)   -- slot capacity for pre-state
      (hCdtPost st stNext cap ... hInv hTransfer)  -- CDT post for this step
      hTransfer
```

**Step 2: Compute nextBase'**
```lean
    let nextBase' := match result with
      | .installed _ _ => SeLe4n.Slot.ofNat (nextBase.toNat + 1)
      | _ => nextBase
```

**Step 3: Apply inductive hypothesis**
```lean
    -- hStep now equates to ipcUnwrapCapsLoop ... fuel' stNext = .ok (summary, st')
    simp [hTransfer] at hStep
    exact ih (idx + 1) nextBase' (accResults.push result) stNext hInvNext hStep
```

### 8.4. Key Proof Obligations in the Success Path

#### 8.4.1. Supplying `hSlotCap` for the Pre-State

The per-step theorem requires:
```lean
hSlotCapacity : ∀ cn, st.objects[receiverRoot]? = some (.cnode cn) →
    ∀ s, (cn.insert s cap).slotCountBounded
```

This is supplied by instantiating the universally-quantified `hSlotCap`
hypothesis with `st` and `cap`:
```lean
hSlotCap st cap hCapMem hInv
```

where `hCapMem : cap ∈ caps.toList` is derived from `caps[idx]? = some cap`
via `Array.getElem?_some_mem` or similar.

#### 8.4.2. Supplying `hCdtPost` for the Per-Step Post-State

The per-step theorem requires:
```lean
hCdtPost : cdtCompleteness stNext ∧ cdtAcyclicity stNext
```

This is supplied by instantiating the universally-quantified `hCdtPost`
hypothesis with `st`, `stNext`, `cap`, and the step evidence:
```lean
hCdtPost st stNext cap ... hInv hTransfer
```

#### 8.4.3. Threading `hSlotCap` to the Inductive Hypothesis

The inductive hypothesis requires `hSlotCap` to hold for `stNext` (not just
`st`). Since `hSlotCap` is universally quantified over all intermediate states,
it applies to `stNext` directly — no re-proving needed.

#### 8.4.4. Threading `hCdtPost` to the Inductive Hypothesis

Similarly, `hCdtPost` is universally quantified over all intermediate state
pairs, so it applies to any future `ipcTransferSingleCap` call starting from
`stNext`.

### 8.5. Potential Complications

#### 8.5.1. `simp` Unfolding Depth

The `ipcUnwrapCapsLoop` definition has nested matches (fuel, then caps[idx]?,
then ipcTransferSingleCap result, then result variant for nextBase'). The
`simp` tactic may not unfold all levels automatically.

**Mitigation**: Use `unfold ipcUnwrapCapsLoop` followed by targeted `simp`
or `cases`/`split` instead of relying on `simp` alone. The existing 8 private
theorems in CapTransfer.lean demonstrate the correct unfolding strategy.

#### 8.5.2. Array Membership Evidence

Deriving `cap ∈ caps.toList` from `caps[idx]? = some cap` requires a lemma
about array indexing. In Lean 4 / Mathlib:
```lean
theorem Array.getElem?_eq_some_iff {a : Array α} {i : Nat} {x : α} :
    a[i]? = some x ↔ ∃ h : i < a.size, a[i] = x
```

From this, `cap ∈ caps.toList` follows via `Array.mem_toList_of_getElem`.
If this exact lemma is not available, a small helper can be proved inline.

#### 8.5.3. `nextBase'` Case Split

The computation of `nextBase'` depends on the result variant. The proof must
handle both `installed` and non-`installed` branches. Since the recursive
call uses `nextBase'` in both cases, a `cases result` or `match result` in
the proof may be needed to align with the definition.

**Mitigation**: After the `ipcTransferSingleCap` case split, further split
on the result to determine `nextBase'`, then apply the inductive hypothesis.
Alternatively, if Lean can unify without the split (because the recursive call
pattern is the same regardless of `nextBase'`), skip the case split.

### 8.6. Reference Implementation Pattern

The closest existing proof pattern is `streamingRevokeBFS_preserves`
(Preservation.lean:1129-1154). Adapting it for V3-E4:

```lean
-- Existing pattern (CDT-shrinking):
| succ n ih =>
    cases hProc : processRevokeNode stInit node with
    | error e => contradiction
    | ok stNext =>
        have hStepInv := step_preserves stInit stNext ...
        exact ih ... stNext hStepInv ...

-- V3-E4 pattern (CDT-expanding):
| succ n ih =>
    cases hCap : caps[idx]? with
    | none => base case (already proved in V3-E3)
    | some cap =>
        cases hTransfer : ipcTransferSingleCap ... st with
        | error e =>
            simp [hCap, hTransfer] at hStep
            exact ih ... st hInv hStep
        | ok pair =>
            obtain ⟨result, stNext⟩ := pair
            have hInvNext := ipcTransferSingleCap_preserves_capabilityInvariantBundle
                st stNext cap ... hInv (hSlotCap ...) (hCdtPost ...) hTransfer
            simp [hCap, hTransfer] at hStep
            -- May need to case split on result for nextBase' computation
            exact ih ... stNext hInvNext hStep
```

### 8.7. Implementation Steps

1. **Read CapTransfer.lean:93-137** for the existing
   `ipcUnwrapCapsLoop_preserves_scheduler` proof to understand the exact
   unfolding and case-splitting strategy
2. **Fill in the `some cap` branch** from V3-E3's `sorry`
3. **Handle the error path** (case split on `ipcTransferSingleCap` result)
4. **Handle the success path**:
   a. Apply `ipcTransferSingleCap_preserves_capabilityInvariantBundle`
   b. Supply `hSlotCap` and `hCdtPost` instantiations
   c. Simplify `hStep` to the recursive form
   d. Apply the inductive hypothesis `ih`
5. **Handle the `nextBase'` case split** if needed
6. **Verify build**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`
7. **Remove all `sorry`** from the loop theorem

### 8.8. Acceptance Criteria

- [ ] Inductive step fully proved (no `sorry`)
- [ ] Error path handled: state unchanged, `ih` applied with original `hInv`
- [ ] Success path handled: per-step preservation applied, hypotheses threaded
- [ ] Both `hSlotCap` and `hCdtPost` correctly instantiated at each step
- [ ] Module builds with zero errors and zero `sorry`
- [ ] The complete `ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle`
  theorem is now fully proved

---

## 9. V3-E5: Compose Full Loop Theorem

**Scope**: Medium (~40-70 lines)
**File**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Prerequisite**: V3-E4 complete (loop theorem fully proved)

### 9.1. Goal

Prove the top-level theorem that composes the loop lemma with the
`ipcUnwrapCaps` entry point to establish end-to-end preservation:

```lean
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant
    (st st' : SystemState) (msg : IpcMessage)
    (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot)
    (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ stI cap, cap ∈ msg.caps.toList →
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCdtPost : ∀ stI stJ cap senderSlot slotBase' scanLimit result,
        capabilityInvariantBundle stI →
        ipcTransferSingleCap cap senderSlot receiverRoot slotBase' scanLimit stI
          = .ok (result, stJ) →
        cdtCompleteness stJ ∧ cdtAcyclicity stJ)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase true st
             = .ok (summary, st')) :
    capabilityInvariantBundle st'
```

### 9.2. Proof Structure

The proof unfolds `ipcUnwrapCaps` for the `Grant=true` path, which delegates
to `ipcUnwrapCapsLoop` with `fuel = msg.caps.size`:

```lean
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant ... := by
  -- Unfold ipcUnwrapCaps for Grant=true path
  simp [ipcUnwrapCaps] at hStep
  -- hStep : ipcUnwrapCapsLoop msg.caps senderRoot receiverRoot
  --           0 slotBase #[] msg.caps.size st = .ok (summary, st')
  exact ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle
    msg.caps senderRoot receiverRoot
    0 slotBase #[] msg.caps.size
    st st' summary hInv hSlotCap hCdtPost hStep
```

### 9.3. Unified Theorem (Optional)

After proving both the Grant=true and Grant=false cases, a unified theorem
can combine them:

```lean
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle
    (st st' : SystemState) (msg : IpcMessage)
    (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot)
    (endpointGrantRight : Bool)
    (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ stI cap, cap ∈ msg.caps.toList →
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCdtPost : ∀ stI stJ cap senderSlot slotBase' scanLimit result,
        capabilityInvariantBundle stI →
        ipcTransferSingleCap cap senderSlot receiverRoot slotBase' scanLimit stI
          = .ok (result, stJ) →
        cdtCompleteness stJ ∧ cdtAcyclicity stJ)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase endpointGrantRight st
             = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  cases endpointGrantRight with
  | false =>
      exact ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant
        st st' msg senderRoot receiverRoot slotBase summary hInv hStep
  | true =>
      exact ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant
        st st' msg senderRoot receiverRoot slotBase summary hInv hSlotCap hCdtPost hStep
```

**Decision**: The unified theorem is highly recommended as it provides a single
entry point for the IPC rendezvous composition chain. The Grant=false path
ignores `hSlotCap` and `hCdtPost` (they are vacuously satisfied since the
state is unchanged).

### 9.4. Integration with Comment Block

The M3-D3 comment block (Preservation.lean:1962-1980) documents this exact gap:

```
-- The grantRight = true case requires per-step induction on the internal
-- ipcUnwrapCapsLoop, threading two preconditions through each iteration:
--   (a) hSlotCapacity: the receiver CNode can accommodate each insert
--   (b) hCdtPost: cdtCompleteness ∧ cdtAcyclicity hold in each intermediate state
-- ... planned for M3-D3b (WS-M4/M5).
```

This comment block should be **replaced** with the actual theorem(s). The
docstring on the new theorem should reference M3-D3b and V3-E as the
resolution.

### 9.5. Downstream Impact

The unified `ipcUnwrapCaps_preserves_capabilityInvariantBundle` theorem can
be immediately used by:

1. **IPC/Invariant/EndpointPreservation.lean**: The IPC rendezvous composition
   chain (`endpointSend_preserves_*`, `endpointCall_preserves_*`) can now
   invoke the unified theorem for the cap-transfer phase, closing the
   preservation gap for the full IPC path.

2. **Kernel/API.lean**: The syscall wrapper for `SyscallSend` and `SyscallCall`
   can reference the theorem as evidence that the full IPC path preserves
   `capabilityInvariantBundle`.

3. **InformationFlow/Invariant/Operations.lean**: Non-interference proofs
   for IPC operations can leverage the preservation guarantee to show that
   cap transfers do not violate information flow policies.

### 9.6. Implementation Steps

1. **Add the Grant=true theorem** after the loop theorem (V3-E4 result)
2. **Add the unified theorem** combining both Grant cases
3. **Replace the M3-D3 comment block** (lines 1962-1980) with the new theorems
4. **Update the docstring** on `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant`
   to cross-reference the Grant=true theorem
5. **Verify build**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`
6. **Run full test suite**: `./scripts/test_full.sh`

### 9.7. Acceptance Criteria

- [ ] `ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant` fully proved
- [ ] Unified `ipcUnwrapCaps_preserves_capabilityInvariantBundle` covers both Grant cases
- [ ] M3-D3 comment block replaced with actual proofs
- [ ] Zero `sorry` in entire `Preservation.lean`
- [ ] `lake build SeLe4n.Kernel.Capability.Invariant.Preservation` succeeds
- [ ] `test_full.sh` passes

---

## 10. Execution Order and Dependency Graph

### 10.1. Strict Sequential Order

```
V3-E1  →  V3-E2  →  V3-E3  →  V3-E4  →  V3-E5
 │          │         │          │          │
 │          │         │          │          └─ Compose top-level theorem
 │          │         │          └─ Prove inductive step (core chain)
 │          │         └─ Prove base cases (fuel=0, idx OOB)
 │          └─ Define theorem signature + hypotheses
 └─ Remove private from ipcUnwrapCapsLoop
```

Each sub-task strictly depends on the previous. No parallelization is possible
within V3-E because each step builds on the proof state from the prior step.

### 10.2. External Dependencies

| Dependency | Status | Required By |
|-----------|--------|-------------|
| V3-D1 (CDT acyclicity audit) | COMPLETE | V3-E4 (hCdtPost threading) |
| V2 (API Surface Completion) | COMPLETE | V3-E5 (downstream integration) |
| `ipcTransferSingleCap_preserves_capabilityInvariantBundle` | PROVED | V3-E4 (per-step lemma) |
| `ipcUnwrapCapsLoop_preserves_scheduler` (+ 7 others) | PROVED | V3-E4 (structural reference) |
| `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant` | PROVED | V3-E5 (Grant=false case) |

All external dependencies are satisfied. V3-E is unblocked.

### 10.3. Estimated Effort Per Sub-Task

| Sub-task | Complexity | Est. Lines | Est. Time |
|----------|-----------|------------|-----------|
| V3-E1 | Small | 5-10 changed | Quick |
| V3-E2 | Small | 15-25 new | Quick |
| V3-E3 | Small | 15-25 new | Quick |
| V3-E4 | Medium | 80-150 new | Primary effort |
| V3-E5 | Medium | 40-70 new | Moderate |
| **Total** | | **~155-280 new** | |

### 10.4. Commit Strategy

Each sub-task should be committed separately for clean git history:

1. `V3-E1: expose ipcUnwrapCapsLoop for external proof composition`
2. `V3-E2: define loop theorem signature for capabilityInvariantBundle preservation`
3. `V3-E3: prove base cases for ipcUnwrapCapsLoop preservation induction`
4. `V3-E4: prove inductive step for ipcUnwrapCapsLoop preservation`
5. `V3-E5: compose ipcUnwrapCaps_preserves_capabilityInvariantBundle (Grant=true)`

**Important**: V3-E2 and V3-E3 may temporarily contain `sorry` in intermediate
commits. The `sorry` MUST be fully eliminated by the V3-E4 commit. Under no
circumstances should a `sorry` persist past V3-E4.

**Alternative**: If intermediate `sorry` commits are undesirable (due to
pre-commit hooks blocking sorry), V3-E2 through V3-E4 can be collapsed into
a single commit: `V3-E2/E3/E4: prove ipcUnwrapCapsLoop preservation induction`.

---

## 11. Risk Assessment and Mitigations

### 11.1. Risk: Lean Elaboration Timeout on Large Proof Terms

**Severity**: Medium
**Likelihood**: Medium (the inductive step involves deeply nested case splits)

**Mitigation**:
- Extract helper lemmas for sub-goals instead of inlining everything
- Use `have` bindings to name intermediate results, reducing term size
- If elaboration exceeds 60 seconds, refactor the proof into separate lemmas:
  - `ipcUnwrapCapsLoop_error_step_preserves` (error path helper)
  - `ipcUnwrapCapsLoop_success_step_preserves` (success path helper)
  - `ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle` (induction shell)

### 11.2. Risk: `simp` Fails to Normalize Loop Step

**Severity**: Low
**Likelihood**: Medium (nested match unfolding can be brittle)

**Mitigation**:
- Study the existing 8 private theorems in CapTransfer.lean for the exact
  `simp`/`unfold`/`cases` strategy that works
- Use `simp only [ipcUnwrapCapsLoop, hCap, hTransfer]` with explicit lemma
  names instead of bare `simp`
- Fall back to `conv` or `rw` for targeted rewriting if `simp` diverges

### 11.3. Risk: Array Membership Lemma Not Available

**Severity**: Low
**Likelihood**: Low (standard Lean 4 library)

**Mitigation**:
- If `Array.mem_toList_of_getElem` or equivalent is not available, prove a
  small helper inline:
  ```lean
  private theorem array_getElem?_mem {a : Array α} {i : Nat} {x : α}
      (h : a[i]? = some x) : x ∈ a.toList := by
    have ⟨hBound, hEq⟩ := Array.getElem?_eq_some.mp h
    exact Array.mem_toList.mpr ⟨i, hBound, hEq⟩
  ```
- This is at most 5 lines of proof and is self-contained

### 11.4. Risk: `nextBase'` Pattern Match Causes Proof Branching

**Severity**: Low
**Likelihood**: Medium

**Mitigation**:
- The `nextBase'` computation only affects the recursive call's arguments,
  not the state or the invariant. The inductive hypothesis is parametric over
  `nextBase`, so both branches should unify.
- If not, case split on `result` before applying `ih`. This adds ~10 lines
  but is straightforward.

### 11.5. Risk: Pre-Commit Hook Blocks Sorry

**Severity**: Low (process risk, not technical)
**Likelihood**: High (hook checks for sorry in staged content)

**Mitigation**:
- Use the collapsed commit strategy (V3-E2/E3/E4 as one commit) to avoid
  ever staging a file with `sorry`
- Or: complete V3-E2 through V3-E4 as a single editing session before committing

---

## 12. Testing and Validation Strategy

### 12.1. Per-Sub-Task Build Verification

After each sub-task, run:
```bash
source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Operations.CapTransfer  # V3-E1
source ~/.elan/env && lake build SeLe4n.Kernel.Capability.Invariant.Preservation  # V3-E2-E5
```

### 12.2. Sorry Audit

After V3-E4 completion, verify zero sorry:
```bash
grep -r "sorry" SeLe4n/Kernel/Capability/Invariant/Preservation.lean
grep -r "sorry" SeLe4n/Kernel/IPC/Operations/CapTransfer.lean
```

Both must return empty.

### 12.3. Tier 0+1 (Fast)

```bash
./scripts/test_fast.sh
```

Run after V3-E1 (visibility change) and V3-E5 (final composition).

### 12.4. Tier 0-2 (Smoke)

```bash
./scripts/test_smoke.sh
```

Run after V3-E5 completion. This is the minimum required before any commit
to the feature branch.

### 12.5. Tier 0-3 (Full)

```bash
./scripts/test_full.sh
```

Run after V3-E5 completion. Required because this work changes theorems and
invariant proofs. Must pass before PR.

### 12.6. Regression Verification

After V3-E1 (removing `private`), verify that:
1. No downstream module breaks due to name conflicts
2. The 8 newly-public theorems are accessible from Preservation.lean
3. Existing public theorems in CapTransfer.lean still resolve correctly

After V3-E5, verify that:
1. The unified theorem is callable from a hypothetical downstream module
2. The existing `_noGrant` theorem still works independently
3. No circular imports were introduced

---

## 13. Documentation Synchronization

### 13.1. Files to Update After V3-E Completion

| File | Update Required |
|------|----------------|
| `docs/audits/AUDIT_v0.21.7_WORKSTREAM_PLAN.md` | Mark V3-E as COMPLETE with version |
| `docs/WORKSTREAM_HISTORY.md` | Record V3-E completion |
| `docs/CLAIM_EVIDENCE_INDEX.md` | Add V3-E theorem as evidence for capability preservation claim |
| `docs/gitbook/12-proof-and-invariant-map.md` | Add `ipcUnwrapCaps_preserves_capabilityInvariantBundle` to theorem index |
| `docs/codebase_map.json` | Regenerate if proof count changes |
| `CHANGELOG.md` | Record V3-E under appropriate version heading |

### 13.2. In-Code Documentation

The new theorems should carry docstrings following the established pattern:

```lean
/-- V3-E / M3-D3b: `ipcUnwrapCapsLoop` preserves `capabilityInvariantBundle`
through fuel-indexed induction. Each iteration delegates to
`ipcTransferSingleCap_preserves_capabilityInvariantBundle`, threading
`hSlotCap` (slot capacity) and `hCdtPost` (CDT completeness + acyclicity)
through the recursive structure.

The `hCdtPost` hypothesis is externalized following the standard pattern for
CDT-expanding operations (see `cspaceCopy_preserves_capabilityInvariantBundle`).
The caller (API layer) is responsible for discharging CDT obligations. -/
```

### 13.3. Comment Block Replacement

The M3-D3 comment block (Preservation.lean:1962-1980) should be replaced with
the actual proof theorems. The comment's planned reference "M3-D3b (WS-M4/M5)"
is resolved by V3-E.
