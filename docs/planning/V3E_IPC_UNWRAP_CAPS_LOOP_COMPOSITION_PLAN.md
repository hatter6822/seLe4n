# V3-E: ipcUnwrapCaps Grant=true Loop Composition

**Workstream**: WS-V Phase V3 — Proof Chain Hardening
**Audit Finding**: M-PRF-2 (MEDIUM severity)
**Sub-task**: V3-E (5 major units, 10 micro-units: V3-E1, E2, E3, E4a/b/c/d, E5a/b/c)
**Dependencies**: V3-D1 (CDT acyclicity audit — complete), V2 (API Surface — complete)
**Gate Conditions**: `lake build` succeeds; zero `sorry`; `test_full.sh` green
**Estimated Scope**: ~115-155 lines new Lean proof code across 2 files

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Problem Statement](#2-problem-statement)
3. [Current State Analysis](#3-current-state-analysis)
4. [Technical Design](#4-technical-design)
5. [V3-E1: Expose ipcUnwrapCapsLoop](#5-v3-e1-expose-ipcunwrapcapsloop)
6. [V3-E2: Define Loop Theorem Signature](#6-v3-e2-define-loop-theorem-signature)
7. [V3-E3: Prove Base Cases](#7-v3-e3-prove-base-cases)
8. [V3-E4: Prove Inductive Step](#8-v3-e4-prove-inductive-step) (V3-E4a/b/c/d)
9. [V3-E5: Compose Full Loop Theorem](#9-v3-e5-compose-full-loop-theorem) (V3-E5a/b/c)
10. [Execution Order and Dependency Graph](#10-execution-order-and-dependency-graph)
11. [Risk Assessment and Mitigations](#11-risk-assessment-and-mitigations)
12. [Testing and Validation Strategy](#12-testing-and-validation-strategy)
13. [Documentation Synchronization](#13-documentation-synchronization)
14. [Appendix A: Reference Proof](#appendix-a-reference-proof--complete-v3-e-tactic-sequence)
15. [Appendix B: Pre-Implementation Checklist](#appendix-b-pre-implementation-checklist)
16. [Appendix C: Glossary](#appendix-c-glossary-of-key-identifiers)

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

This plan decomposes the work into 5 major units (V3-E1 through V3-E5) further
broken into 10 micro-units with exact tactic sequences derived from the 8
existing `ipcUnwrapCapsLoop` proofs. Total estimated proof code: ~115-155 lines.

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

### 4.5. Induction Structure: `generalizing` Clause and IH Shape

The induction must generalize exactly the variables that change across
recursive calls. From the existing `ipcUnwrapCapsLoop` proofs in
CapTransfer.lean (Pattern 1A/1B/1C), the standard `generalizing` clause is:

```lean
induction fuel generalizing idx nextBase accResults st with
```

This generalizes **4 variables** that change on each recursive call:
- `idx` — incremented by 1 each iteration
- `nextBase` — conditionally incremented based on result type
- `accResults` — appended with each iteration's result
- `st` — modified by successful `ipcTransferSingleCap` calls

**The IH shape depends on which hypotheses are NOT generalized.** Variables
NOT in the `generalizing` clause remain fixed across the induction. For V3-E:

- `caps`, `senderRoot`, `receiverRoot` — fixed (loop parameters)
- `st'`, `summary` — the final state/result (bound by `hStep`)
- `hSlotCap`, `hCdtPost` — universally quantified, so they apply to any state

**Critical design point**: `hSlotCap` and `hCdtPost` must NOT be generalized
because they are universally quantified over all states. They remain available
unchanged across all inductive steps. This matches Pattern 1C where `hObjInv`
is NOT generalized but IS threaded: the error path passes the original, and the
success path passes an updated version.

**IH argument count**: The IH will have 4 implicit arguments (from
`generalizing`) plus 1 explicit hypothesis argument (`hInv` for the current
state's bundle), plus the step hypothesis. Total: `ih _ _ _ _ hInvCurrent hStep`.

This matches Pattern 1C (`ih _ _ _ _ hObjInvNext hStep`) where the invariant
is explicitly passed and the 4 generalized variables are inferred by Lean.

### 4.6. Proven Tactic Vocabulary

Based on analysis of all 8 existing `ipcUnwrapCapsLoop` proofs and both
`revokeCdtFold_preserves` and `streamingRevokeBFS_preserves`, the exact tactic
vocabulary for V3-E is:

| Tactic | Usage | Where Used |
|--------|-------|-----------|
| `simp [ipcUnwrapCapsLoop] at hStep` | Unfold loop definition (zero case) | All 8 loop proofs |
| `simp only [ipcUnwrapCapsLoop] at hStep` | Surgical unfold (succ case) | All 8 loop proofs |
| `cases hCap : caps[idx]? with` | Case split on array lookup | All 8 loop proofs |
| `simp [hCap] at hStep` | Normalize after array lookup | All 8 loop proofs |
| `obtain ⟨_, rfl⟩ := hStep` | Extract state equality in base case | All 8 loop proofs |
| `cases hTransfer : ipcTransferSingleCap ...` | Case split on transfer result | All 8 loop proofs |
| `simp [hTransfer] at hStep` | Normalize after transfer result | All 8 loop proofs |
| `rcases pair with ⟨result, stNext⟩` | Destructure success pair | All 8 loop proofs |
| `cases result with` | Case split on CapTransferResult | Patterns 1A/1B/1C |
| `exact ih _ _ _ _ hHyp hStep` | Apply IH with threaded hypothesis | Pattern 1C |
| `rw [ih _ _ _ _ hStep, hProp]` | Rewrite with IH (equational) | Patterns 1A/1B |
| `have hX := lemma ... hTransfer` | Extract single-step preservation | All success paths |

**Key distinction**: Patterns 1A/1B use `rw [ih ..., hProp]` because they prove
**equational** properties (scheduler = scheduler). V3-E4 proves a **predicate**
(`capabilityInvariantBundle st'`), so it will use `exact ih ...` like Pattern
1C, NOT `rw [ih ...]`.

### 4.7. File Placement

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

## 6. V3-E2: Define Loop Theorem Signature

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

### 6.4. Exact Theorem Signature

The following is the precise signature that V3-E2 must produce. It is derived
directly from the `ipcUnwrapCapsLoop` function signature (CapTransfer.lean:36-42)
combined with the hypothesis pattern from
`ipcTransferSingleCap_preserves_capabilityInvariantBundle` (Preservation.lean:1910-1919):

```lean
/-- V3-E / M3-D3b: `ipcUnwrapCapsLoop` preserves `capabilityInvariantBundle`
through fuel-indexed induction. Each iteration delegates to
`ipcTransferSingleCap_preserves_capabilityInvariantBundle`, threading
slot capacity and CDT postcondition hypotheses through the recursive structure.

The `hCdtPost` hypothesis is externalized following the standard pattern for
CDT-expanding operations (see `cspaceCopy_preserves_capabilityInvariantBundle`).
The caller (API layer) is responsible for discharging CDT obligations. -/
theorem ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ (stI : SystemState) (cap : Capability),
        cap ∈ caps.toList →
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCdtPost : ∀ (stI stJ : SystemState) (cap : Capability)
        (senderSlot : CSpaceAddr) (slotBase : SeLe4n.Slot)
        (scanLimit : Nat) (result : CapTransferResult),
        capabilityInvariantBundle stI →
        ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit stI
          = .ok (result, stJ) →
        cdtCompleteness stJ ∧ cdtAcyclicity stJ)
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase
             accResults fuel st = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  sorry
```

**Parameter correspondence to function definition**:

| Theorem param | ipcUnwrapCapsLoop param | Notes |
|--------------|------------------------|-------|
| `caps` | `caps` | Fixed across recursion |
| `senderRoot` | `senderCspaceRoot` | Renamed for consistency |
| `receiverRoot` | `receiverCspaceRoot` | Renamed for consistency |
| `idx` | `idx` | Generalized in induction |
| `nextBase` | `nextBase` | Generalized in induction |
| `accResults` | `accResults` | Generalized in induction |
| `fuel` | `fuel` | Induction variable |
| `st` | (state arg) | Generalized in induction |
| `st'` | (output state) | Bound by `hStep` |
| `summary` | (output summary) | Bound by `hStep` |
| `hInv` | (new) | Pre-state invariant |
| `hSlotCap` | (new) | Per-state slot capacity |
| `hCdtPost` | (new) | Per-step CDT postcondition |
| `hStep` | (new) | Loop execution evidence |

### 6.5. Insertion Location

The theorem is inserted at Preservation.lean between lines 1960 and 1962,
replacing the M3-D3 comment block (lines 1962-1980):

```
Line 1960:  (end of ipcTransferSingleCap_preserves_capabilityInvariantBundle proof)
Line 1961:  (blank line)
Line 1962:  -- ===== M3-D3 comment block (TO BE REPLACED) =====
  ...
Line 1980:  -- ===== end comment block =====
Line 1981:  (blank line)
Line 1982:  (start of ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant)
```

The new theorem replaces lines 1962-1980. The `_noGrant` theorem at line 1982
remains unchanged.

### 6.6. Implementation Steps

1. **Read Preservation.lean lines 1960-1997** to identify the exact insertion
   point (between `ipcTransferSingleCap_preserves_capabilityInvariantBundle`
   and the M3-D3 comment block)
2. **Replace the M3-D3 comment block** (lines 1962-1980) with the exact
   theorem signature from Section 6.4 above, including docstring
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

## 7. V3-E3: Prove Base Cases

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

### 7.2. Exact Tactic Sequence

The base case proof follows the identical pattern from all 8 existing
`ipcUnwrapCapsLoop` proofs (CapTransfer.lean:99-107). The only difference
is the conclusion: instead of `rfl` (equational) we use `exact hInv`
(predicate preservation).

```lean
-- Replace `sorry` with:
  induction fuel generalizing idx nextBase accResults st with
  | zero =>
    -- Base: fuel exhausted → loop returns immediately, state unchanged
    simp [ipcUnwrapCapsLoop] at hStep
    obtain ⟨_, rfl⟩ := hStep
    exact hInv
  | succ n ih =>
    -- Recursive case: unfold one step of the loop
    simp only [ipcUnwrapCapsLoop] at hStep
    -- Case split on array lookup
    cases hCap : caps[idx]? with
    | none =>
      -- Base: index out of bounds → loop returns immediately, state unchanged
      simp [hCap] at hStep
      obtain ⟨_, rfl⟩ := hStep
      exact hInv
    | some cap =>
      -- Inductive step (V3-E4 — filled in next)
      sorry
```

**Tactic-by-tactic explanation**:

1. `simp [ipcUnwrapCapsLoop] at hStep` — Unfolds the `match fuel with | 0 => ...`
   and simplifies the result. In the `zero` case, this reduces `hStep` to
   `(.ok ({ results := accResults }, st)) = .ok (summary, st')`, which `simp`
   normalizes to `summary = { results := accResults } ∧ st' = st`.

2. `obtain ⟨_, rfl⟩ := hStep` — Destructures the conjunction, discarding the
   summary equality (irrelevant to the goal) and substituting `st' := st` into
   the goal via `rfl`. The goal becomes `capabilityInvariantBundle st`.

3. `exact hInv` — Closes the goal directly from the hypothesis.

4. `simp only [ipcUnwrapCapsLoop] at hStep` — In the `succ` case, uses `simp only`
   (not `simp`) to unfold only `ipcUnwrapCapsLoop` without applying other lemmas.
   This is important: bare `simp` might simplify too aggressively and destroy
   the match structure needed for the next `cases` tactic.

5. `cases hCap : caps[idx]?` — Names the case hypothesis `hCap` so it can be
   used with `simp [hCap]` to normalize `hStep` in each branch.

### 7.3. Implementation Steps

1. **Replace `sorry`** in the theorem body with the induction tactic and base
   case handling from Section 7.2 above
2. **Verify the `zero` case** closes with `exact hInv`
3. **Verify the `none` case** closes with `exact hInv`
4. **Leave `sorry`** in the `some cap` branch for V3-E4
5. **Verify build**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`
   — should compile with a single sorry warning

### 7.4. Validation

The base case proof should be exactly 12 lines (matching the pattern from
`ipcUnwrapCapsLoop_preserves_scheduler`). Verify by reading the proof term
and confirming that:
- The `zero` branch uses `simp [ipcUnwrapCapsLoop]` (NOT `simp only`)
- The `succ` case uses `simp only [ipcUnwrapCapsLoop]` (NOT `simp`)
- Both base branches produce `exact hInv`
- Both base branches correctly extract `rfl : st' = st` via `obtain ⟨_, rfl⟩`
- The `generalizing` clause includes exactly `idx nextBase accResults st`

### 7.5. Acceptance Criteria

- [ ] Base cases (fuel=0 and idx out-of-bounds) are fully proved
- [ ] No `sorry` in base case branches
- [ ] `sorry` remains only in the `some cap` branch (V3-E4 scope)
- [ ] Module builds without error (base case only; `sorry` in inductive step is expected)

---

## 8. V3-E4: Prove Inductive Step

**Scope**: Medium-Large (~80-150 lines)
**File**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Prerequisite**: V3-E3 complete (base cases proved)

This is the most complex sub-task. It is decomposed into 4 sequential
micro-units (V3-E4a through V3-E4d) to manage complexity and enable
incremental validation.

### 8.1. Sub-Unit Decomposition

```
V3-E4: Prove Inductive Step
  │
  ├── V3-E4a: Preliminary setup — simp/cases scaffolding       (~10 lines)
  │     Open the `some cap` branch, normalize `hStep`, split on
  │     ipcTransferSingleCap result
  │
  ├── V3-E4b: Error path — state unchanged                     (~5 lines)
  │     When ipcTransferSingleCap returns .error, apply ih with
  │     original hInv
  │
  ├── V3-E4c: Success path — per-step preservation + IH        (~40-80 lines)
  │     When ipcTransferSingleCap returns .ok, chain:
  │     (1) Extract hCapMem from hCap
  │     (2) Instantiate hSlotCap and hCdtPost
  │     (3) Apply ipcTransferSingleCap_preserves_capabilityInvariantBundle
  │     (4) Case split on result for nextBase'
  │     (5) Apply ih with updated hInvNext
  │
  └── V3-E4d: (Contingency) Extract helper lemmas               (~30-50 lines)
        Only if V3-E4c causes elaboration timeout. Factor the
        success path into a separate lemma.
```

### 8.2. V3-E4a: Preliminary Setup

**Goal**: Open the `some cap` branch, normalize the step hypothesis, and set up
the case split on `ipcTransferSingleCap`.

**Exact tactic sequence** (replacing `sorry` from V3-E3):

```lean
    | some cap =>
      -- Normalize hStep after matching caps[idx]? = some cap
      simp [hCap] at hStep
      -- Case split on ipcTransferSingleCap result
      cases hTransfer : ipcTransferSingleCap cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st with
      | error e =>
        sorry  -- V3-E4b
      | ok pair =>
        sorry  -- V3-E4c
```

**Why this exact form**: This matches the tactic sequence from
`ipcUnwrapCapsLoop_preserves_scheduler` (CapTransfer.lean:109-113) exactly.
The `simp [hCap]` normalizes `hStep` by substituting `caps[idx]? = some cap`
into the unfolded loop definition. The `cases hTransfer` then splits on the
result of the single-cap transfer, naming the evidence `hTransfer` for use in
subsequent `simp [hTransfer]` calls.

**Validation**: After V3-E4a, the module should build with exactly 2 `sorry`
warnings (one for each branch of the `cases hTransfer`).

### 8.3. V3-E4b: Error Path

**Goal**: When `ipcTransferSingleCap` returns `.error e`, prove that the loop
still preserves `capabilityInvariantBundle`.

**Key insight**: On error, the loop recurses with the **original state** `st`:
```lean
| .error _e =>
    ipcUnwrapCapsLoop caps senderCspaceRoot receiverCspaceRoot
      (idx + 1) (SeLe4n.Slot.ofNat (nextBase.toNat + 1))
      (accResults.push .noSlot) fuel' st  -- same st!
```

Since `st` is unchanged, the original `hInv : capabilityInvariantBundle st`
applies directly. The IH is invoked with the 4 generalized variables
(all inferred by Lean via underscores) plus `hInv` (unchanged).

**Exact tactic sequence**:

```lean
      | error e =>
        -- Normalize: substitute hTransfer = .error e into hStep
        simp [hTransfer] at hStep
        -- hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot
        --   (idx + 1) (Slot.ofNat (nextBase.toNat + 1))
        --   (accResults.push .noSlot) n st = .ok (summary, st')
        -- Apply IH with same state and same invariant
        exact ih _ _ _ _ hInv hStep
```

**Tactic-by-tactic**:

1. `simp [hTransfer] at hStep` — Substitutes `.error e` for the
   `ipcTransferSingleCap` result in `hStep`. After substitution, `hStep` is a
   recursive call to `ipcUnwrapCapsLoop` with `fuel' = n` (one less than
   `fuel = n + 1`), starting from the same state `st`.

2. `exact ih _ _ _ _ hInv hStep` — Applies the inductive hypothesis.
   - The 4 underscores correspond to the generalized variables: `idx + 1`,
     `Slot.ofNat (nextBase.toNat + 1)`, `accResults.push .noSlot`, `st`.
     Lean infers these from `hStep`.
   - `hInv` is passed explicitly because the pre-state is unchanged.
   - `hStep` provides the loop execution evidence for the remaining iterations.

**This matches Pattern 1A** (CapTransfer.lean:114-116) exactly, with the only
difference being `exact ih` (predicate) instead of `rw [ih ...]` (equational).

**Validation**: After V3-E4b, the module should build with exactly 1 `sorry`
warning (in the `ok pair` branch).

### 8.4. V3-E4c: Success Path — Core Proof Chain

**Goal**: When `ipcTransferSingleCap` returns `.ok (result, stNext)`, prove
`capabilityInvariantBundle st'` by chaining per-step preservation with the IH.

This is the most intricate part of V3-E. It has 5 sequential proof steps:

#### Step 1: Destructure the success pair

```lean
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
```

Uses `rcases` (not `obtain`) to match the existing pattern in all 8 loop
proofs (e.g., CapTransfer.lean:118). `result : CapTransferResult` and
`stNext : SystemState` are now in scope.

#### Step 2: Derive array membership evidence

```lean
        -- Derive: cap ∈ caps.toList (needed for hSlotCap)
        have hCapMem : cap ∈ caps.toList := by
          exact Array.getElem?_mem hCap
```

This derives `cap ∈ caps.toList` from `hCap : caps[idx]? = some cap`.

**Contingency**: If `Array.getElem?_mem` is not available in Lean 4.28.0,
use one of these alternatives:

```lean
-- Alternative 1: Manual proof via getElem? semantics
have hCapMem : cap ∈ caps.toList := by
  have ⟨hBound, hEq⟩ := Array.getElem?_eq_some.mp hCap
  exact Array.mem_toList.mpr ⟨idx, hBound, hEq⟩

-- Alternative 2: Weaken hSlotCap to not require membership
-- (see Section 8.7 Design Alternative)
```

**Important**: If the array membership proof is problematic, consider
reformulating `hSlotCap` to quantify over ALL capabilities (not just those in
`caps.toList`). See Section 8.7 for this alternative design.

#### Step 3: Apply per-step preservation theorem

```lean
        -- Apply ipcTransferSingleCap_preserves_capabilityInvariantBundle
        have hInvNext := ipcTransferSingleCap_preserves_capabilityInvariantBundle
          st stNext cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps result
          hInv                                    -- pre-state invariant
          (hSlotCap st cap hCapMem hInv)          -- slot capacity
          (hCdtPost st stNext cap                 -- CDT postcondition
            { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
            nextBase maxExtraCaps result
            hInv hTransfer)
          hTransfer                               -- step evidence
```

This is the **core proof step**. It instantiates the per-step theorem with:

| Argument | Value | Source |
|----------|-------|--------|
| `st` | `st` | Current pre-state (in scope) |
| `st'` | `stNext` | Post-state (from `rcases`) |
| `cap` | `cap` | Current capability (from `cases hCap`) |
| `senderSlot` | `{ cnode := senderRoot, slot := Slot.ofNat 0 }` | Fixed sender slot |
| `receiverRoot` | `receiverRoot` | Fixed receiver (in scope) |
| `slotBase` | `nextBase` | Current slot base (generalized) |
| `scanLimit` | `maxExtraCaps` | Fixed scan limit |
| `result` | `result` | Transfer result (from `rcases`) |
| `hInv` | `hInv` | Pre-state invariant (in scope) |
| `hSlotCapacity` | `hSlotCap st cap hCapMem hInv` | Instantiated from universal |
| `hCdtPost` | `hCdtPost st stNext cap ... hInv hTransfer` | Instantiated from universal |
| `hStep` | `hTransfer` | Transfer execution evidence |

**Output**: `hInvNext : capabilityInvariantBundle stNext`

#### Step 4: Normalize hStep for the recursive call

```lean
        -- Simplify hStep by substituting the successful transfer result
        simp [hTransfer] at hStep
```

After this, `hStep` contains the recursive `ipcUnwrapCapsLoop` call with
`fuel' = n`, starting from state `stNext`. However, the `nextBase'`
computation (a `match result with | .installed _ _ => ... | _ => ...`) may
still be present in `hStep`, requiring a case split on `result`.

#### Step 5: Case split on result and apply IH

```lean
        -- Case split on result to resolve nextBase' computation
        cases result with
        | installed c s =>
          -- nextBase' = Slot.ofNat (nextBase.toNat + 1)
          exact ih _ _ _ _ hInvNext hStep
        | noSlot =>
          -- nextBase' = nextBase
          exact ih _ _ _ _ hInvNext hStep
        | grantDenied =>
          -- nextBase' = nextBase (unreachable in practice, but must be handled)
          exact ih _ _ _ _ hInvNext hStep
```

This case split resolves the `match result with` in the loop's `nextBase'`
computation. Each branch has an identical proof (`exact ih _ _ _ _ hInvNext hStep`)
because:
- The IH is parametric over `nextBase` (generalized)
- `hInvNext` holds regardless of the result variant
- `hStep` contains the correct recursive call for each branch

**This matches Pattern 1A** (CapTransfer.lean:121-124) which uses the same
3-way case split with identical branches.

**Optimization**: If Lean can unify all three branches without the case split
(i.e., if `simp [hTransfer]` fully resolves the `match result` in `hStep`),
the case split can be omitted:

```lean
        -- Optimistic: if simp resolves nextBase' without case split
        simp [hTransfer] at hStep
        exact ih _ _ _ _ hInvNext hStep
```

Try the optimistic version first. Fall back to the 3-way case split if Lean
reports a unification error.

### 8.5. V3-E4d: (Contingency) Extract Helper Lemmas

**Trigger**: Only needed if V3-E4c causes Lean elaboration timeout (>60s) or
if the proof term becomes too large for the elaborator.

**Strategy**: Factor the success path into a standalone lemma:

```lean
/-- V3-E helper: single-step capability transfer preserves the loop invariant.
Extracts the success-path proof from the inductive step to reduce elaboration
pressure on the main induction. -/
private theorem ipcUnwrapCapsLoop_step_preserves_capabilityInvariantBundle
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot)
    (cap : Capability) (result : CapTransferResult) (st stNext : SystemState)
    (hInv : capabilityInvariantBundle st)
    (hCap : caps[idx]? = some cap)
    (hSlotCap : ∀ (stI : SystemState) (cap : Capability),
        cap ∈ caps.toList →
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCdtPost : ∀ (stI stJ : SystemState) (cap : Capability)
        (senderSlot : CSpaceAddr) (slotBase : SeLe4n.Slot)
        (scanLimit : Nat) (result : CapTransferResult),
        capabilityInvariantBundle stI →
        ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit stI
          = .ok (result, stJ) →
        cdtCompleteness stJ ∧ cdtAcyclicity stJ)
    (hTransfer : ipcTransferSingleCap cap
        { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
        receiverRoot nextBase maxExtraCaps st = .ok (result, stNext)) :
    capabilityInvariantBundle stNext := by
  have hCapMem : cap ∈ caps.toList := Array.getElem?_mem hCap
  exact ipcTransferSingleCap_preserves_capabilityInvariantBundle
    st stNext cap
    { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
    receiverRoot nextBase maxExtraCaps result
    hInv
    (hSlotCap st cap hCapMem hInv)
    (hCdtPost st stNext cap _ nextBase maxExtraCaps result hInv hTransfer)
    hTransfer
```

Then the main induction's success path becomes:

```lean
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hInvNext := ipcUnwrapCapsLoop_step_preserves_capabilityInvariantBundle
          caps senderRoot receiverRoot idx nextBase cap result st stNext
          hInv hCap hSlotCap hCdtPost hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hInvNext hStep
        | noSlot => exact ih _ _ _ _ hInvNext hStep
        | grantDenied => exact ih _ _ _ _ hInvNext hStep
```

This separates the hypothesis-threading complexity from the induction
structure, significantly reducing elaboration pressure.

### 8.6. Complete Tactic Sequence (V3-E4a through V3-E4c Combined)

For reference, here is the complete `some cap` branch proof that replaces the
`sorry` from V3-E3:

```lean
    | some cap =>
      -- V3-E4a: Preliminary setup
      simp [hCap] at hStep
      cases hTransfer : ipcTransferSingleCap cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st with
      -- V3-E4b: Error path
      | error e =>
        simp [hTransfer] at hStep
        exact ih _ _ _ _ hInv hStep
      -- V3-E4c: Success path
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hCapMem : cap ∈ caps.toList := Array.getElem?_mem hCap
        have hInvNext := ipcTransferSingleCap_preserves_capabilityInvariantBundle
          st stNext cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps result
          hInv
          (hSlotCap st cap hCapMem hInv)
          (hCdtPost st stNext cap
            { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
            nextBase maxExtraCaps result hInv hTransfer)
          hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hInvNext hStep
        | noSlot => exact ih _ _ _ _ hInvNext hStep
        | grantDenied => exact ih _ _ _ _ hInvNext hStep
```

**Total line count**: ~25 lines for the `some cap` branch. Combined with the
base cases from V3-E3, the full proof body is ~37 lines.

### 8.7. Design Alternative: Weaken hSlotCap Membership Requirement

If the array membership evidence (`cap ∈ caps.toList`) proves problematic
(see Section 8.4, Step 2 contingency), the `hSlotCap` hypothesis can be
strengthened to quantify over ALL capabilities, not just those in `caps`:

```lean
-- Weakened membership requirement (quantify over all caps):
(hSlotCap : ∀ (stI : SystemState) (cap : Capability),
    capabilityInvariantBundle stI →
    ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
      ∀ s, (cn.insert s cap).slotCountBounded)
```

This removes the `cap ∈ caps.toList` precondition entirely. The caller must
then prove that ANY capability insertion keeps the slot count bounded, which
is a stronger obligation but eliminates the array membership proof entirely.

**Trade-off analysis**:
- **Pro**: Simpler proof (no array membership lemma needed)
- **Pro**: Fewer tactic steps (no `have hCapMem` step)
- **Con**: Stronger caller obligation (must prove for all caps, not just message caps)
- **Con**: Less precise specification (weakly typed)

**Recommendation**: Start with the precise formulation (with membership).
Fall back to the weakened version only if the array membership proof is
genuinely unavailable or excessively complex.

### 8.8. Potential Complications and Mitigations

#### 8.8.1. `simp [hTransfer]` Does Not Fully Resolve `hStep`

**Symptom**: After `simp [hTransfer] at hStep`, the `hStep` hypothesis still
contains unreduced `match` expressions or `let` bindings.

**Mitigation**: Use `simp only [hTransfer]` followed by `simp only []` to
normalize without applying rewrite rules. If still unresolved, try:
```lean
simp [hCap, hTransfer] at hStep  -- provide both hypotheses at once
```
or use `dsimp` for definitional simplification:
```lean
dsimp only [] at hStep
simp [hTransfer] at hStep
```

#### 8.8.2. IH Unification Failure on `nextBase'`

**Symptom**: `exact ih _ _ _ _ hInvNext hStep` fails with a unification error
because Lean cannot determine which `nextBase'` value to use.

**Mitigation**: The 3-way case split on `result` (Section 8.4, Step 5) ensures
that `nextBase'` is fully determined in each branch. This is the same pattern
used in all 8 existing loop proofs and is confirmed to work.

#### 8.8.3. `hCdtPost` Instantiation Argument Mismatch

**Symptom**: The `hCdtPost` instantiation fails because Lean cannot match the
expected argument types.

**Mitigation**: Verify that the `hCdtPost` hypothesis signature in V3-E2
exactly matches the arguments of `ipcTransferSingleCap`. The `senderSlot`
argument in the loop is always `{ cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }`,
which must be a valid `CSpaceAddr`. Ensure the `hCdtPost` quantifier includes
this as a bound variable (not a fixed value).

#### 8.8.4. Lean Elaboration Timeout

**Symptom**: The proof takes >60s to elaborate, or Lean reports a deterministic
timeout error.

**Mitigation**: Apply the V3-E4d contingency plan — extract the success path
into a standalone helper lemma. This is the standard response in this codebase
(see `streamingRevokeBFS_step_preserves`, which is a 3-line wrapper that exists
solely to reduce elaboration pressure on the main induction).

### 8.9. Implementation Steps

1. **V3-E4a**: Replace `sorry` in the `some cap` branch with simp/cases
   scaffolding (Section 8.2). Verify: 2 sorry warnings.
2. **V3-E4b**: Fill the `error e` branch (Section 8.3). Verify: 1 sorry warning.
3. **V3-E4c**: Fill the `ok pair` branch (Section 8.4). Verify: 0 sorry.
4. **V3-E4d**: (Only if needed) Extract helper lemma (Section 8.5).
5. **Final build**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`
   — zero errors, zero sorry.

### 8.10. Acceptance Criteria

- [ ] V3-E4a: `some cap` branch scaffolding compiles (2 sorry)
- [ ] V3-E4b: Error path fully proved, IH applied with original `hInv` (1 sorry)
- [ ] V3-E4c: Success path fully proved:
  - [ ] Array membership evidence derived from `hCap`
  - [ ] `hSlotCap` instantiated for pre-state
  - [ ] `hCdtPost` instantiated for this step's post-state
  - [ ] `ipcTransferSingleCap_preserves_capabilityInvariantBundle` applied
  - [ ] Result case split resolves `nextBase'` computation
  - [ ] IH applied with `hInvNext` and remaining loop evidence
- [ ] Zero `sorry` in the complete loop theorem
- [ ] Module builds with zero errors
- [ ] The complete `ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle`
  theorem is now fully proved

---

## 9. V3-E5: Compose Full Loop Theorem

**Scope**: Medium (~40-70 lines across 3 deliverables)
**File**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Prerequisite**: V3-E4 complete (loop theorem fully proved)

V3-E5 is decomposed into 3 sequential micro-units:

```
V3-E5: Compose Full Loop Theorem
  │
  ├── V3-E5a: Grant=true top-level theorem               (~15 lines)
  │     Unfold ipcUnwrapCaps, delegate to loop theorem
  │
  ├── V3-E5b: Unified Bool-parametric theorem             (~25 lines)
  │     Case split on endpointGrantRight, delegate to
  │     _grant and _noGrant variants
  │
  └── V3-E5c: Comment block cleanup + docstrings          (~10 lines)
        Replace M3-D3 comment block, add docstrings,
        update _noGrant cross-reference
```

### 9.1. V3-E5a: Grant=true Top-Level Theorem

**Goal**: Bridge from `ipcUnwrapCaps` (entry point) to
`ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle` (loop theorem).

**Exact signature and proof**:

```lean
/-- V3-E / M3-D3b: `ipcUnwrapCaps` preserves `capabilityInvariantBundle`
when the endpoint has Grant right (grantRight = true). Delegates to
`ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle` after unfolding
the entry point. -/
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant
    (st st' : SystemState) (msg : IpcMessage)
    (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot)
    (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ (stI : SystemState) (cap : Capability),
        cap ∈ msg.caps.toList →
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCdtPost : ∀ (stI stJ : SystemState) (cap : Capability)
        (senderSlot : CSpaceAddr) (slotBase' : SeLe4n.Slot)
        (scanLimit : Nat) (result : CapTransferResult),
        capabilityInvariantBundle stI →
        ipcTransferSingleCap cap senderSlot receiverRoot slotBase' scanLimit stI
          = .ok (result, stJ) →
        cdtCompleteness stJ ∧ cdtAcyclicity stJ)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase true st
             = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  simp [ipcUnwrapCaps] at hStep
  exact ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle
    msg.caps senderRoot receiverRoot
    0 slotBase #[] msg.caps.size
    st st' summary hInv hSlotCap hCdtPost hStep
```

**Tactic-by-tactic**:

1. `simp [ipcUnwrapCaps] at hStep` — Unfolds `ipcUnwrapCaps` and evaluates
   the `if !true then ...` branch. Since `!true = false`, the `else` branch
   is taken, reducing `hStep` to:
   ```
   ipcUnwrapCapsLoop msg.caps senderRoot receiverRoot
     0 slotBase #[] msg.caps.size st = .ok (summary, st')
   ```

2. `exact ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle ...` — Applies
   the loop theorem with explicit arguments. The initial values are:
   - `idx = 0` (start from the first capability)
   - `accResults = #[]` (empty accumulator)
   - `fuel = msg.caps.size` (one iteration per capability)

**Note on hypothesis forwarding**: The `hSlotCap` hypothesis quantifies over
`msg.caps.toList`, which is the same `caps` array passed to the loop. This is
why the hypotheses forward directly without conversion.

### 9.2. V3-E5b: Unified Bool-Parametric Theorem

**Goal**: Provide a single entry point that covers both Grant cases.

**Exact signature and proof**:

```lean
/-- V3-E / M3-D3b: `ipcUnwrapCaps` preserves `capabilityInvariantBundle`
for any value of `endpointGrantRight`. This is the primary entry point for
the IPC rendezvous composition chain.

- **Grant=false**: State unchanged (no transfers), trivially preserved.
- **Grant=true**: Fuel-indexed induction over `ipcUnwrapCapsLoop`, threading
  slot capacity and CDT postcondition hypotheses per-iteration.

The `hSlotCap` and `hCdtPost` hypotheses are vacuous when Grant=false
(no `ipcTransferSingleCap` calls occur). -/
theorem ipcUnwrapCaps_preserves_capabilityInvariantBundle
    (st st' : SystemState) (msg : IpcMessage)
    (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot)
    (endpointGrantRight : Bool)
    (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ (stI : SystemState) (cap : Capability),
        cap ∈ msg.caps.toList →
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCdtPost : ∀ (stI stJ : SystemState) (cap : Capability)
        (senderSlot : CSpaceAddr) (slotBase' : SeLe4n.Slot)
        (scanLimit : Nat) (result : CapTransferResult),
        capabilityInvariantBundle stI →
        ipcTransferSingleCap cap senderSlot receiverRoot slotBase' scanLimit stI
          = .ok (result, stJ) →
        cdtCompleteness stJ ∧ cdtAcyclicity stJ)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase
             endpointGrantRight st = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  cases endpointGrantRight with
  | false =>
    exact ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant
      st st' msg senderRoot receiverRoot slotBase summary hInv hStep
  | true =>
    exact ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant
      st st' msg senderRoot receiverRoot slotBase summary
      hInv hSlotCap hCdtPost hStep
```

**Tactic-by-tactic**:

1. `cases endpointGrantRight with` — Case split on the Bool. Lean generates
   two goals, one for `false` and one for `true`.

2. `| false =>` — In this branch, `endpointGrantRight = false` is substituted
   into `hStep`, which now matches the `_noGrant` theorem's signature exactly.

3. `| true =>` — In this branch, `endpointGrantRight = true` is substituted
   into `hStep`, which now matches the `_grant` theorem's signature exactly.

### 9.3. V3-E5c: Comment Block Cleanup and Docstrings

**Goal**: Replace the M3-D3 placeholder comment block with the actual theorems
and update cross-references.

**Tasks**:

1. **Delete the M3-D3 comment block** (Preservation.lean:1962-1980):
   ```
   -- ============================================================================
   -- M3-D3: ipcUnwrapCaps preserves capabilityInvariantBundle
   -- ... (18 lines of comments)
   -- ============================================================================
   ```
   This is replaced by the actual `ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle`
   theorem (V3-E2/E3/E4) and the `_grant` + unified theorems (V3-E5a/E5b).

2. **Update the `_noGrant` docstring** (Preservation.lean:1982-1984):
   Change from:
   ```lean
   /-- M3-D3: ipcUnwrapCaps preserves capabilityInvariantBundle when the endpoint
   lacks Grant right (grantRight = false). ...
   ```
   To:
   ```lean
   /-- M3-D3 / V3-E: ipcUnwrapCaps preserves capabilityInvariantBundle when the
   endpoint lacks Grant right (grantRight = false). In this case, all caps are
   silently dropped and the state is unchanged, so the invariant trivially holds.
   See also: `ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant` for the
   Grant=true case, and `ipcUnwrapCaps_preserves_capabilityInvariantBundle` for
   the unified theorem. -/
   ```

3. **Verify the final theorem ordering** in Preservation.lean:
   ```
   ipcTransferSingleCap_preserves_capabilityInvariantBundle  (existing, line 1910)
   ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle      (V3-E2/E3/E4, NEW)
   ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant    (V3-E5a, NEW)
   ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant  (existing, line 1985)
   ipcUnwrapCaps_preserves_capabilityInvariantBundle          (V3-E5b, NEW)
   ```
   The `_noGrant` theorem is kept in place. The new theorems are inserted
   before it (loop + grant) and after it (unified).

### 9.4. Downstream Impact

The unified `ipcUnwrapCaps_preserves_capabilityInvariantBundle` theorem
closes the proof gap for the IPC rendezvous path. Downstream consumers:

| Consumer File | Usage | Priority |
|--------------|-------|----------|
| `IPC/Invariant/EndpointPreservation.lean` | `endpointSend_preserves_*`, `endpointCall_preserves_*` can invoke unified theorem for cap-transfer phase | High |
| `Kernel/API.lean` | Syscall wrappers (`SyscallSend`, `SyscallCall`) reference theorem as cap-transfer evidence | Medium |
| `InformationFlow/Invariant/Operations.lean` | NI proofs for IPC ops leverage preservation guarantee | Medium |
| `Kernel/CrossSubsystem.lean` | Cross-subsystem invariant composition can include cap-transfer path | Low |

**Note**: Downstream integration is NOT part of V3-E scope. These are future
work items that V3-E unblocks.

### 9.5. Implementation Steps

1. **V3-E5a**: Add the `_grant` theorem (Section 9.1) after the loop theorem
2. **V3-E5b**: Add the unified theorem (Section 9.2) after `_noGrant`
3. **V3-E5c**: Delete M3-D3 comment block, update `_noGrant` docstring
4. **Verify build**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`
5. **Sorry audit**: `grep -r "sorry" SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
6. **Run full test suite**: `./scripts/test_full.sh`

### 9.6. Acceptance Criteria

- [ ] V3-E5a: `_grant` theorem fully proved and type-checks
- [ ] V3-E5b: Unified theorem covers both Grant cases
- [ ] V3-E5c: M3-D3 comment block removed; docstrings updated
- [ ] Zero `sorry` in entire `Preservation.lean`
- [ ] `lake build SeLe4n.Kernel.Capability.Invariant.Preservation` succeeds
- [ ] `test_full.sh` passes
- [ ] Theorem ordering in file is logically sequential

---

## 10. Execution Order and Dependency Graph

### 10.1. Detailed Execution Order

```
V3-E1           Remove private from ipcUnwrapCapsLoop + 8 helper theorems
  │
  ▼
V3-E2           Define loop theorem signature (sorry body)
  │
  ▼
V3-E3           Prove base cases (fuel=0, idx OOB). sorry in some cap branch.
  │
  ▼
V3-E4a          Setup: simp/cases scaffolding in some cap branch (2 sorry)
  │
  ▼
V3-E4b          Error path: exact ih _ _ _ _ hInv hStep (1 sorry)
  │
  ▼
V3-E4c          Success path: per-step preservation + IH (0 sorry)
  │
  ├──[if timeout]── V3-E4d: Extract helper lemma, retry V3-E4c
  │
  ▼
V3-E5a          Grant=true top-level theorem (simp + exact loop lemma)
  │
  ▼
V3-E5b          Unified Bool-parametric theorem (cases + exact)
  │
  ▼
V3-E5c          Comment block cleanup + docstring updates
```

### 10.2. Critical Path Analysis

The critical path runs through V3-E4c (success path proof). All other units
are either scaffolding (V3-E1/E2/E3/E4a/E4b) or composition (V3-E5a/E5b/E5c).

**If V3-E4c encounters difficulties**, the contingency path is:
1. Attempt V3-E4c directly (~40-80 lines inline)
2. If elaboration timeout → execute V3-E4d (extract helper) → retry V3-E4c
3. If array membership issue → apply Design Alternative (Section 8.7)
4. If IH unification failure → apply 3-way case split (Section 8.4, Step 5)

### 10.3. External Dependencies

| Dependency | Status | Required By |
|-----------|--------|-------------|
| V3-D1 (CDT acyclicity audit) | COMPLETE | V3-E4c (hCdtPost threading) |
| V2 (API Surface Completion) | COMPLETE | V3-E5 (downstream integration) |
| `ipcTransferSingleCap_preserves_capabilityInvariantBundle` | PROVED (line 1910) | V3-E4c (per-step lemma) |
| 8 `ipcUnwrapCapsLoop_preserves_*` theorems | PROVED (lines 93-494) | V3-E4 (structural reference) |
| `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant` | PROVED (line 1985) | V3-E5b (Grant=false case) |
| `Array.getElem?_mem` or equivalent | Lean 4 stdlib | V3-E4c (array membership) |

All external dependencies are satisfied. V3-E is unblocked.

### 10.4. Estimated Effort Per Unit

| Unit | Complexity | Est. Lines | Description |
|------|-----------|------------|-------------|
| V3-E1 | Trivial | 9 lines changed | Remove `private` keyword (9 occurrences) |
| V3-E2 | Small | 25-30 new | Theorem signature + docstring + `sorry` |
| V3-E3 | Small | 12 new | Base case tactics (2 branches) |
| V3-E4a | Trivial | 5 new | simp + cases scaffolding |
| V3-E4b | Trivial | 3 new | Error path: simp + exact ih |
| V3-E4c | Medium | 20-25 new | Success path: have + exact chain |
| V3-E4d | Small | 25-35 new | (Contingency) Helper lemma extraction |
| V3-E5a | Small | 15 new | Grant=true theorem: simp + exact |
| V3-E5b | Small | 25 new | Unified theorem: cases + exact |
| V3-E5c | Trivial | 10 changed | Comment/docstring cleanup |
| **Total** | | **~115-155 new** (without V3-E4d) | |

### 10.5. Commit Strategy

The pre-commit hook blocks `sorry` in staged content. Therefore, intermediate
sub-tasks that contain `sorry` (V3-E2, V3-E3, V3-E4a, V3-E4b) cannot be
committed individually. The recommended commit strategy groups sorry-free
boundaries:

**Recommended: 3-commit strategy**

| Commit | Units | Sorry-Free? | Message |
|--------|-------|-------------|---------|
| 1 | V3-E1 | Yes | `V3-E1: expose ipcUnwrapCapsLoop for external proof composition` |
| 2 | V3-E2 + V3-E3 + V3-E4 | Yes (all sorry removed by E4) | `V3-E2/E3/E4: prove ipcUnwrapCapsLoop preserves capabilityInvariantBundle` |
| 3 | V3-E5a + V3-E5b + V3-E5c | Yes | `V3-E5: compose ipcUnwrapCaps_preserves_capabilityInvariantBundle` |

**Alternative: 2-commit strategy** (if V3-E1 is small enough to combine)

| Commit | Units | Message |
|--------|-------|---------|
| 1 | V3-E1 + V3-E2 + V3-E3 + V3-E4 | `V3-E: prove ipcUnwrapCapsLoop preserves capabilityInvariantBundle` |
| 2 | V3-E5a + V3-E5b + V3-E5c | `V3-E5: compose ipcUnwrapCaps_preserves_capabilityInvariantBundle` |

**Build verification before each commit**:
```bash
source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Operations.CapTransfer    # Commit 1
source ~/.elan/env && lake build SeLe4n.Kernel.Capability.Invariant.Preservation  # Commits 2, 3
```

---

## 11. Risk Assessment and Mitigations

### 11.1. Risk Matrix

| # | Risk | Severity | Likelihood | Unit | Mitigation | Reference |
|---|------|----------|-----------|------|-----------|-----------|
| R1 | Elaboration timeout on inductive step | Medium | Medium | V3-E4c | Extract helper lemma (V3-E4d) | Section 8.5 |
| R2 | `simp` fails to normalize loop step | Low | Medium | V3-E4a | Use `simp only` + explicit lemma names | Section 8.8.1 |
| R3 | `Array.getElem?_mem` unavailable | Low | Low | V3-E4c | Inline 5-line helper or weaken `hSlotCap` | Section 8.7 |
| R4 | `nextBase'` causes IH unification failure | Low | Medium | V3-E4c | 3-way `cases result` split (confirmed pattern) | Section 8.8.2 |
| R5 | Pre-commit hook blocks `sorry` | Low | High | V3-E2/E3 | Use collapsed commit strategy (Section 10.5) | Section 10.5 |
| R6 | `hCdtPost` argument mismatch | Low | Low | V3-E4c | Verify signature alignment in V3-E2 first | Section 8.8.3 |
| R7 | Downstream name collision after deprivatization | Low | Low | V3-E1 | Check `lake build` on all importers | Section 5.4 |

### 11.2. Highest-Risk Unit: V3-E4c

V3-E4c (success path proof) concentrates all technical risk. The ~20-25 line
proof must correctly:
1. Derive array membership evidence
2. Instantiate 2 universally-quantified hypotheses with 6-8 explicit arguments each
3. Apply a theorem with 12 arguments
4. Resolve a conditional `match` in the recursive call

**Fallback cascade**:
```
Attempt V3-E4c directly (inline, ~25 lines)
  │
  ├── If elaboration timeout → V3-E4d: extract helper lemma
  │
  ├── If Array.getElem?_mem missing → weaken hSlotCap (Section 8.7)
  │
  ├── If IH unification fails → add 3-way cases result split
  │
  └── If hCdtPost mismatch → fix signature in V3-E2, rebuild V3-E3/E4
```

### 11.3. Process Risk: Sorry in Intermediate State

The pre-commit hook blocks `sorry` in staged files. Since V3-E2 introduces
a theorem with `sorry` body that isn't removed until V3-E4c, these units
MUST be completed in a single session and committed together.

**Resolution**: Use the 3-commit strategy from Section 10.5, where Commit 2
groups V3-E2+E3+E4 into a single sorry-free commit.

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

---

## Appendix A: Reference Proof — Complete V3-E Tactic Sequence

This appendix provides the complete, uninterrupted tactic sequence for the
entire V3-E proof chain. This is the concatenation of V3-E3 (base cases) and
V3-E4 (inductive step) into a single proof body. Use this as the reference
implementation.

### A.1. ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle (Full Proof)

```lean
/-- V3-E / M3-D3b: `ipcUnwrapCapsLoop` preserves `capabilityInvariantBundle`
through fuel-indexed induction. Each iteration delegates to
`ipcTransferSingleCap_preserves_capabilityInvariantBundle`, threading
`hSlotCap` (slot capacity) and `hCdtPost` (CDT completeness + acyclicity)
through the recursive structure.

The `hCdtPost` hypothesis is externalized following the standard pattern for
CDT-expanding operations (see `cspaceCopy_preserves_capabilityInvariantBundle`).
The caller (API layer) is responsible for discharging CDT obligations. -/
theorem ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle
    (caps : Array Capability) (senderRoot receiverRoot : SeLe4n.ObjId)
    (idx : Nat) (nextBase : SeLe4n.Slot) (accResults : Array CapTransferResult)
    (fuel : Nat) (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : capabilityInvariantBundle st)
    (hSlotCap : ∀ (stI : SystemState) (cap : Capability),
        cap ∈ caps.toList →
        capabilityInvariantBundle stI →
        ∀ cn, stI.objects[receiverRoot]? = some (.cnode cn) →
          ∀ s, (cn.insert s cap).slotCountBounded)
    (hCdtPost : ∀ (stI stJ : SystemState) (cap : Capability)
        (senderSlot : CSpaceAddr) (slotBase : SeLe4n.Slot)
        (scanLimit : Nat) (result : CapTransferResult),
        capabilityInvariantBundle stI →
        ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit stI
          = .ok (result, stJ) →
        cdtCompleteness stJ ∧ cdtAcyclicity stJ)
    (hStep : ipcUnwrapCapsLoop caps senderRoot receiverRoot idx nextBase
             accResults fuel st = .ok (summary, st')) :
    capabilityInvariantBundle st' := by
  -- ── V3-E3: Induction + base cases ──
  induction fuel generalizing idx nextBase accResults st with
  | zero =>
    simp [ipcUnwrapCapsLoop] at hStep
    obtain ⟨_, rfl⟩ := hStep
    exact hInv
  | succ n ih =>
    simp only [ipcUnwrapCapsLoop] at hStep
    cases hCap : caps[idx]? with
    | none =>
      simp [hCap] at hStep
      obtain ⟨_, rfl⟩ := hStep
      exact hInv
    -- ── V3-E4a: Setup ──
    | some cap =>
      simp [hCap] at hStep
      cases hTransfer : ipcTransferSingleCap cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps st with
      -- ── V3-E4b: Error path ──
      | error e =>
        simp [hTransfer] at hStep
        exact ih _ _ _ _ hInv hStep
      -- ── V3-E4c: Success path ──
      | ok pair =>
        rcases pair with ⟨result, stNext⟩
        have hCapMem : cap ∈ caps.toList := Array.getElem?_mem hCap
        have hInvNext := ipcTransferSingleCap_preserves_capabilityInvariantBundle
          st stNext cap
          { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
          receiverRoot nextBase maxExtraCaps result
          hInv
          (hSlotCap st cap hCapMem hInv)
          (hCdtPost st stNext cap
            { cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0 }
            nextBase maxExtraCaps result hInv hTransfer)
          hTransfer
        simp [hTransfer] at hStep
        cases result with
        | installed c s => exact ih _ _ _ _ hInvNext hStep
        | noSlot => exact ih _ _ _ _ hInvNext hStep
        | grantDenied => exact ih _ _ _ _ hInvNext hStep
```

**Total proof body**: ~37 lines of tactics.

### A.2. Comparison with Closest Existing Proof

The closest structural match is `ipcUnwrapCapsLoop_preserves_objects_ne`
(CapTransfer.lean:186-220), which also threads a hypothesis through the
induction. Key differences:

| Aspect | `_preserves_objects_ne` | V3-E (this proof) |
|--------|------------------------|-------------------|
| Property type | Equational (`st'.objects[oid]? = st.objects[oid]?`) | Predicate (`capabilityInvariantBundle st'`) |
| IH application | `rw [ih ..., hObj]` | `exact ih ...` |
| Threaded hypothesis | `hObjInv : st.objects.invExt` (1 hyp) | `hInv : capabilityInvariantBundle st` (1 hyp) |
| Single-step lemmas | 2 (`_preserves_objects_invExt`, `_preserves_objects_ne`) | 1 (`_preserves_capabilityInvariantBundle`) |
| Additional obligations | None | `hSlotCap` + `hCdtPost` instantiation |
| Error path IH args | `ih _ _ _ _ hObjInv hStep` (5 args) | `ih _ _ _ _ hInv hStep` (5 args) |
| Success path IH args | `ih _ _ _ _ hObjInvNext hStep` (5 args) | `ih _ _ _ _ hInvNext hStep` (5 args) |

The V3-E proof is structurally isomorphic to `_preserves_objects_ne` with
the addition of `hSlotCap`/`hCdtPost` instantiation in the success path.

---

## Appendix B: Pre-Implementation Checklist

Before beginning V3-E implementation, verify each item:

### B.1. Codebase Prerequisites

- [ ] `lake build` succeeds with zero errors on current main
- [ ] `ipcTransferSingleCap_preserves_capabilityInvariantBundle` exists at
  Preservation.lean:1910 with the expected signature
- [ ] The M3-D3 comment block exists at Preservation.lean:1962-1980
- [ ] `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant` exists at
  Preservation.lean:1985
- [ ] `ipcUnwrapCapsLoop` is `private` at CapTransfer.lean:36
- [ ] All 8 `ipcUnwrapCapsLoop_preserves_*` theorems are `private`
- [ ] No existing theorem named `ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle`

### B.2. Lean Toolchain

- [ ] Lean 4.28.0 is active (`lean --version`)
- [ ] `elan` environment is sourced (`source ~/.elan/env`)
- [ ] `Array.getElem?_mem` or equivalent is available in Lean 4.28.0 stdlib
  (test with: `#check @Array.getElem?_mem`)

### B.3. Test Infrastructure

- [ ] `./scripts/test_fast.sh` passes on current codebase
- [ ] `./scripts/test_smoke.sh` passes on current codebase
- [ ] Pre-commit hook is installed and blocks `sorry`

---

## Appendix C: Glossary of Key Identifiers

| Identifier | Type | Location | Description |
|-----------|------|----------|-------------|
| `ipcUnwrapCapsLoop` | `def` | CapTransfer.lean:36 | Private recursive helper for batch cap transfer |
| `ipcUnwrapCaps` | `def` | CapTransfer.lean:79 | Public entry point for IPC cap transfer |
| `ipcTransferSingleCap` | `def` | Capability/Operations.lean | Transfer one capability into receiver CNode |
| `capabilityInvariantBundle` | `def` | Capability/Invariant/Defs.lean | 7-tuple conjunction of capability invariants |
| `cspaceSlotUnique` | `def` | Capability/Invariant/Defs.lean | Per-CNode slot index uniqueness |
| `cspaceLookupSound` | `def` | Capability/Invariant/Defs.lean | Lookup completeness |
| `cspaceSlotCountBounded` | `def` | Capability/Invariant/Defs.lean | Slot count ≤ 2^radixBits |
| `cdtCompleteness` | `def` | Capability/Invariant/Defs.lean | CDT node-slot reachability |
| `cdtAcyclicity` | `def` | Capability/Invariant/Defs.lean | CDT cycle-freedom |
| `cspaceDepthConsistent` | `def` | Capability/Invariant/Defs.lean | CSpace depth bounds |
| `CapTransferResult` | `inductive` | Model/Object/Types.lean | `.installed`, `.noSlot`, `.grantDenied` |
| `CapTransferSummary` | `structure` | Model/Object/Types.lean | Wrapper around `Array CapTransferResult` |
| `maxExtraCaps` | `def` | Model/Object/Types.lean | Constant = 3 (scan limit) |
| `Kernel` | `abbrev` | (Monad) | `SystemState → Except KernelError (α × SystemState)` |
| `hSlotCap` | hypothesis | V3-E (new) | Per-state slot capacity for receiver CNode |
| `hCdtPost` | hypothesis | V3-E (new) | Per-step CDT completeness + acyclicity |
