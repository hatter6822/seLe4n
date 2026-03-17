# WS-N Workstream Plan — IPC & Capability Cross-Audit: Robin Hood Hashing, Determinism & Correctness (v0.17.0)

**Created**: 2026-03-16
**Baseline version**: 0.17.0
**Baseline audit**: End-to-end IPC + Capability subsystem cross-audit (15,000+ LoC, 20+ files)
**Prior portfolios**: WS-M (v0.16.14–v0.17.0, complete), WS-L (v0.16.9–v0.16.13, complete)
**Constraint**: Zero `sorry`/`axiom` in production proof surface
**Hardware target**: Raspberry Pi 5 (ARM64, BCM2712)

---

## 1. Audit Summary

A comprehensive cross-subsystem audit of the IPC and Capability subsystems was
conducted covering 15,000+ lines of Lean 4 code across 20+ source files. The
audit examined every HashMap usage site, every fold/iteration pattern, every
`resolveCapAddress` caller, and every bridge lemma dependency.

**Overall verdict**: Zero `sorry`/`axiom`. All proofs machine-checked. Zero
critical vulnerabilities. Three categories of improvement identified:

### 1.1 Performance (Robin Hood Hashing)

The kernel uses 13+ `Std.HashMap` instances and 3+ `Std.HashSet` instances
across the `SystemState`, `CNode`, `VSpaceRoot`, `CapDerivationTree`,
`RunQueue`, and `LifecycleMetadata` structures. Lean 4's `Std.HashMap` is a
**separate-chaining** hash table: an `Array` of `AssocList` buckets (linked
lists). Each lookup traverses a linked-list bucket — poor cache locality
due to pointer chasing, especially on ARM64 where cache lines are 64 bytes.

Robin Hood hashing with open addressing stores entries **inline** in a flat
`Array`. Lean 4's `Array` compiles to a contiguous C heap allocation with
O(1) random access and in-place mutation when linearly used (FBIP). This
eliminates pointer chasing entirely. Robin Hood displacement bounds
worst-case probe sequences to O(log n) expected, and backward-shift
deletion avoids tombstone pollution.

**Concrete HashMap instances to migrate (13 maps + 3 sets):**

| Location | Key Type | Value Type | Hot Operations | Expected Size |
|----------|----------|------------|----------------|---------------|
| `SystemState.objects` | `ObjId` | `KernelObject` | lookup, insert, erase | 10–1000 |
| `SystemState.lifecycle.objectTypes` | `ObjId` | `KernelObjectType` | lookup, insert | 10–1000 |
| `SystemState.lifecycle.capabilityRefs` | `SlotRef` | `CapTarget` | insert, erase, filter | 10–5000 |
| `SystemState.services` | `ServiceId` | `ServiceGraphEntry` | lookup, insert | 5–50 |
| `SystemState.irqHandlers` | `Irq` | `ObjId` | lookup, insert | 1–64 |
| `SystemState.asidTable` | `ASID` | `ObjId` | lookup, insert, erase | 1–256 |
| `SystemState.cdtSlotNode` | `SlotRef` | `CdtNodeId` | lookup, insert, erase | 10–5000 |
| `SystemState.cdtNodeSlot` | `CdtNodeId` | `SlotRef` | lookup, insert, erase | 10–5000 |
| `CNode.slots` | `Slot` | `Capability` | lookup, insert, erase, fold, filter | 1–4096 |
| `VSpaceRoot.mappings` | `VAddr` | `(PAddr × PagePerms)` | lookup, insert, erase | 1–65536 |
| `CDT.childMap` | `CdtNodeId` | `List CdtNodeId` | lookup, insert, erase | 10–5000 |
| `CDT.parentMap` | `CdtNodeId` | `CdtNodeId` | lookup, insert, erase | 10–5000 |
| `RunQueue.byPriority` | `Priority` | `List ThreadId` | lookup, insert, fold | 1–256 |
| `RunQueue.membership` | `ThreadId` | (set) | contains, insert, erase | 1–256 |
| `RunQueue.threadPriority` | `ThreadId` | `Priority` | lookup, insert, erase | 1–256 |
| `SystemState.objectIndexSet` | `ObjId` | (set) | contains, insert | 10–1000 |

### 1.2 Correctness (`resolveCapAddress` Leaf-Level Asymmetry)

`resolveCapAddress` (`Operations.lean:76–108`) exhibits an asymmetry in slot
occupancy checking between the leaf and recursive paths:

**Leaf path** (line 94–95, `bitsRemaining - consumed = 0`):
```lean
.ok { cnode := rootId, slot := slot }   -- returns SlotRef UNCONDITIONALLY
```

**Recursive path** (line 97–106, bits remain):
```lean
match cn.lookup slot with
| some cap => match cap.target with
  | .object childId => resolveCapAddress childId addr ...  -- recurse
  | _ => .error .invalidCapability
| none => .error .invalidCapability                        -- CHECKS occupancy
```

The intermediate path checks `cn.lookup slot` and fails on empty slots (line
106). The leaf path does **not** check occupancy — it returns a `SlotRef`
regardless of whether the slot holds a capability.

**Impact analysis**: All 3 API-level callers (`syscallLookupCap`,
`resolveExtraCaps`, `cspaceLookupMultiLevel`) defensively check slot occupancy
*after* resolution via `SystemState.lookupSlotCap`. So this asymmetry does not
produce incorrect behavior at the API level. However:

1. **The function's contract is unclear**: Is `resolveCapAddress` meant to return
   slot *addresses* (seL4 semantics) or slot *contents* (capability lookup)?
   The intermediate path checks contents, but the leaf path returns addresses.
2. **Performance waste**: Callers perform a redundant lookup after resolution
   when the leaf slot is empty. The function could fail early.
3. **Missing theorem**: No theorem characterizes the leaf-level occupancy
   behavior. `resolveCapAddress_result_valid_cnode` proves the CNode exists
   but says nothing about the slot.

**Corrective strategy**: Two options exist:

- **Option A (Strict)**: Add `cn.lookup slot` check at the leaf level, matching
  the intermediate path. `resolveCapAddress` becomes a capability-existence
  checker, not just an address resolver. Simplifies all callers.
- **Option B (Document)**: Keep current behavior but add a theorem
  `resolveCapAddress_leaf_slot_unvalidated` documenting that leaf slots are
  unchecked, and `resolveCapAddress_intermediate_requires_occupied` proving
  intermediate slots are checked. Callers remain responsible for occupancy.

**Recommendation**: Option A (Strict). The intermediate path already establishes
the precedent of checking occupancy. Making the leaf path consistent eliminates
a class of caller errors, reduces redundant lookups, and makes the function's
contract self-consistent. The existing theorems (`resolveCapAddress_result_valid_cnode`,
`resolveCapAddress_guard_match`) continue to hold and are strengthened.

### 1.3 Determinism (Comprehensive)

All operations in both subsystems are pure total functions. The audit found:

- **All HashMap fold bodies are order-independent** or are proved via
  `Std.HashMap.fold_eq_foldl_toList` with induction on the list form.
- **No fold body depends on iteration order**: `revokeAndClearRefsState` folds
  with conditional `capabilityRefs.erase` (commutative: order of erasures
  doesn't matter). `recomputeMaxPriority` folds with `max` (commutative).
  `detachCNodeSlots` folds with `detachSlotFromCdt` (each step modifies
  independent CDT entries). `VSpaceRoot.BEq` folds with `&&` (commutative).
  `storeObject` rebuilds `capabilityRefs` via fold (each slot key is unique).
- **`test_tier2_determinism.sh` runs trace twice and diff-compares** — catches
  any observable non-determinism.
- **Robin Hood hashing would change `toList` ordering** but since no proof or
  runtime behavior depends on `toList` ordering, this is safe.

**Determinism risk**: NONE identified. Migration to Robin Hood hashing preserves
all determinism guarantees.

---

## 2. Finding Registry

### Performance Findings

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| N-P01 | HIGH | All `Std.HashMap` sites (76 API calls across 11 files) | Separate-chaining hash tables cause pointer chasing on every lookup. Robin Hood open-addressing with flat `Array` eliminates this entirely. Lean 4's `Array` compiles to contiguous C memory with FBIP in-place mutation. |
| N-P02 | MEDIUM | `Operations.lean:94–95` | `resolveCapAddress` skips leaf-level occupancy check, forcing callers to perform a redundant `lookupSlotCap` that traverses the HashMap again. Early failure at the leaf saves one O(1) amortized HashMap lookup per empty-slot resolution. |
| N-P03 | LOW | `RunQueue.recomputeMaxPriority` (line 52) | Folds over `byPriority` HashMap to find max. With Robin Hood hashing, the fold iterates a flat array — better cache behavior for small priority counts (typically 1–256). |

### Correctness Findings

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| N-C01 | HIGH | `Operations.lean:94–95` vs `97–106` | `resolveCapAddress` leaf path returns `SlotRef` without occupancy check; recursive path checks `cn.lookup slot` and fails on empty. Asymmetric contract. See §1.2. |
| N-C02 | MEDIUM | `Prelude.lean:676–810` | 14 HashMap bridge lemmas delegate to `Std.DHashMap.Const.*`. Robin Hood replacement must provide equivalent lemmas proved against the new implementation. |
| N-C03 | MEDIUM | `Prelude.lean:777–816` | 5 HashSet bridge lemmas delegate to `Std.HashSet.*` / `Std.DHashMap.*`. Must be re-proved for Robin Hood HashSet wrapper. |

### Determinism Findings

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| N-D01 | LOW | `State.lean:265,293+` | `revokeAndClearRefsState` and `detachCNodeSlots` use `HashMap.fold` → `fold_eq_foldl_toList`. The `.toList` ordering changes with Robin Hood but fold bodies are order-independent. New `fold_eq_foldl_toList` bridge needed. |
| N-D02 | LOW | `Structures.lean:294,599` | `VSpaceRoot.BEq` and `CNode.BEq` use `.fold` for entry comparison. Both use `&&` (commutative). Safe under any iteration order. |

### Test Coverage Findings

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| N-T01 | HIGH | New file needed | Robin Hood HashMap needs comprehensive unit tests: insert/lookup/erase correctness, Robin Hood displacement behavior, resize at load factor threshold, backward-shift deletion integrity, pathological collision chains. |
| N-T02 | MEDIUM | `NegativeStateSuite.lean` | `resolveCapAddress` leaf-level empty-slot behavior needs explicit test coverage. Current tests (M4-A8) test via `cspaceLookupMultiLevel` wrapper which catches emptiness downstream. |
| N-T03 | LOW | `test_tier2_determinism.sh` | Could strengthen from 2-run to 3-run comparison for higher confidence. |

---

## 3. Planning Principles

1. **Runtime performance is paramount**: The Robin Hood HashMap must be
   implemented with Lean 4's `Array` (flat C memory, FBIP in-place mutation).
   Not `List`-backed — actual cache locality matters for Raspberry Pi 5.

2. **Proof surface compatibility**: Every `Std.HashMap` bridge lemma used in
   the codebase (14 HashMap + 5 HashSet lemmas, plus `fold_eq_foldl_toList`)
   must have a proven equivalent for the Robin Hood implementation.

3. **Drop-in type replacement**: Define `KernelHashMap`/`KernelHashSet` type
   aliases. All existing code compiles after a type-level swap + lemma rename.

4. **resolveCapAddress strict semantics**: Add leaf-level occupancy check to
   match intermediate-level behavior. Update all theorems accordingly.

5. **Zero sorry/axiom**: Every new theorem fully machine-checked. `sorry` may
   be used as intermediate placeholders during development but must all be
   resolved before the workstream closes.

6. **Deterministic fold order**: Robin Hood iteration follows bucket-index
   order — deterministic for the same operation sequence. Existing fold-based
   proofs transfer via `fold_eq_foldl_toList` bridge.

7. **Coherent slices**: Each phase independently deliverable and testable.
   Full `test_smoke.sh` passes after each phase.

8. **Minimal disruption**: Preserve all existing API signatures. Migration is
   purely internal (type + proof changes, no behavioral changes except the
   `resolveCapAddress` fix).

---

## 4. Phase Overview

| Phase | Focus | Priority | Findings Addressed | Target Version |
|-------|-------|----------|-------------------|----------------|
| **WS-N1** | Robin Hood HashMap: core data structure + bridge lemmas | HIGH | N-P01, N-C02, N-C03, N-D01 | 0.17.1 |
| **WS-N2** | `resolveCapAddress` leaf-level occupancy fix + theorems | HIGH | N-C01, N-P02 | 0.17.2 |
| **WS-N3** | HashMap/HashSet migration across entire codebase | MEDIUM | N-P01 (completion), N-P03, N-D01, N-D02 | 0.17.3 |
| **WS-N4** | Test coverage, determinism validation, sorry resolution | MEDIUM | N-T01, N-T02, N-T03 | 0.17.4 |
| **WS-N5** | Documentation sync, GitBook, codebase map | LOW | (documentation) | 0.17.5 |

---

## 5. Detailed Phase Plans

### Phase 1: Robin Hood HashMap Foundation (WS-N1)

**Target version**: 0.17.1
**Files created**: `SeLe4n/Data/RobinHoodHashMap.lean`
**Files modified**: `SeLe4n/Prelude.lean` (type aliases + bridge lemma re-exports),
`lakefile.toml` (version bump)
**Findings addressed**: N-P01, N-C02, N-C03, N-D01
**Subtasks**: 14 atomic units (N1-A through N1-N)

This phase creates the complete Robin Hood HashMap and HashSet implementations
with all bridge lemmas needed by the existing proof surface. No migration yet —
Phase 1 establishes the foundation; Phase 3 migrates.

**Implementation status**: `SeLe4n/Data/RobinHoodHashMap.lean` has been created
with all definitions compiling and all bridge lemma signatures stated. The file
contains 19 `sorry` placeholders organized into a layered proof architecture.
Tasks N1-A through N1-F define the data structure and operations (COMPLETE).
Tasks N1-G through N1-N resolve the sorry placeholders in dependency order.

---

#### Task N1-A: Core data structure definition (COMPLETE)

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (lines 49–67)
**Status**: Implemented and compiling

Defines `Entry α β` (key, value, inline PSL) and `RobinHoodHashMap α β`:

```lean
structure Entry (α : Type) (β : Type) where
  key : α
  val : β
  psl : Nat     -- probe sequence length (inline, not parallel array)

structure RobinHoodHashMap (α : Type) (β : Type) [BEq α] [Hashable α] where
  buckets  : Array (Option (Entry α β))
  size     : Nat
  capacity : Nat
  hCapPos  : capacity ≥ 4
  hBuckets : buckets.size = capacity
```

**Design decision change from original plan**: Inline PSL (in `Entry`) instead
of a separate `Array UInt8`. This simplifies proofs significantly — each bucket
is self-describing, eliminating the need to maintain two parallel arrays in sync
and prove their coherence. For proof tractability, this is a major win: every
lemma about a bucket operation only needs to reason about one array, not two.
The runtime performance impact is negligible for the kernel's map sizes
(≤ 65536 entries).

---

#### Task N1-B: Core operations — `empty`, `idealIndex`, `nextIdx` (COMPLETE)

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (lines 69–96)
**Status**: Implemented and compiling

- `empty`: Creates map with `Array.mk (List.replicate c none)` where `c = max cap 4`
- `idealIndex`: `(hash k).toUSize.toNat % m.capacity`
- `nextIdx`: `(i + 1) % m.capacity` (wrapping forward)
- `prevIdx`: `(i + m.capacity - 1) % m.capacity` (wrapping backward)

Uses `%` modular arithmetic rather than bitwise `&&&` masking. This is
correct for any capacity (not just power-of-two). Power-of-two optimization
can be added in WS-N3 migration if profiling shows it matters on RPi5.

---

#### Task N1-C: Lookup — `get?` with Robin Hood early termination (COMPLETE)

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (lines 98–121)
**Status**: Implemented and compiling

```lean
def get? (m : RobinHoodHashMap α β) (k : α) : Option β :=
  go (m.idealIndex k) 0 m.capacity
where
  go (idx dist fuel : Nat) : Option β :=
    if fuel = 0 then none
    else if h : idx < m.buckets.size then
      match m.buckets[idx] with
      | none => none
      | some entry =>
        if entry.key == k then some entry.val
        else if entry.psl < dist then none  -- Robin Hood early termination
        else go (m.nextIdx idx) (dist + 1) (fuel - 1)
    else none
```

**Fuel-based termination**: Uses `fuel` (initialized to `capacity`) instead of
`termination_by m.capacity - dist`. This avoids complex termination proof
obligations while guaranteeing the loop visits at most `capacity` buckets.

**Robin Hood early termination**: If `entry.psl < dist`, the target key cannot
exist further along — entries with longer probe distances are never behind
entries with shorter distances. This bounds worst-case lookup to O(max PSL).

---

#### Task N1-D: Insert with Robin Hood displacement (COMPLETE)

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (lines 123–172)
**Status**: Implemented and compiling

Three insertion paths in `insertCore.go`:

1. **Empty bucket** (`none`): Place `⟨curK, curV, dist⟩`, increment `size`.
2. **Key match** (`entry.key == curK`): Update value in place, preserve PSL.
3. **Robin Hood displacement** (`entry.psl < dist`): Swap our entry in,
   continue inserting the displaced entry with `psl + 1`.

`insert` wraps `insertCore` with a load factor check: if `size * 8 ≥ capacity * 7`
(87.5%), call `resize` which doubles capacity and reinserts all entries.

**Structural proof obligations**: All three paths produce valid `hBuckets`
proofs via `Array.size_set` — the array size is unchanged by `set`.

---

#### Task N1-E: Erase with backward-shift deletion (COMPLETE)

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (lines 174–215)
**Status**: Implemented and compiling

1. `findIndex`: Locate the key's bucket (same logic as `get?.go` but
   returns index instead of value).
2. Clear the bucket: `set idx none`, decrement `size`.
3. `backwardShift`: Scan forward from `nextIdx`. For each occupied bucket
   with `psl > 0`, move it backward and decrement its PSL. Stop at empty
   bucket or `psl = 0`.

**Why backward-shift (not tombstones)**: Tombstones degrade lookup over time.
Backward-shift maintains clean probe chains — lookup performance stays optimal.

---

#### Task N1-F: Fold, toList, filter (COMPLETE)

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (lines 217–236)
**Status**: Implemented and compiling

- `fold`: Iterates `buckets` array in index order (0 to capacity−1). Deterministic.
- `toList`: `buckets.toList.filterMap` extracting `(key, val)` from occupied buckets.
- `filter`: Rebuild from filtered `toList` entries. O(n), preserves Robin Hood invariants.

**Deterministic fold order**: `fold` iterates buckets in index order (0 to
capacity−1). Deterministic for the same operation sequence. Ordering differs
from `Std.HashMap` but all fold bodies are order-independent (§1.3).

---

#### Task N1-G: Well-formedness invariant + `empty_wellFormed` (COMPLETE — sorry placeholder)

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (lines 238–283)
**Status**: Defined, proof uses sorry (5 sorry placeholders)

Defines the `WellFormed` predicate with four components:

1. **`pslCorrect`**: Every occupied bucket's PSL equals its actual distance
   from `idealIndex` (modular arithmetic).
2. **`noDuplicateKeys`**: No two occupied buckets hold BEq-equal keys.
3. **`robinHoodOrdering`**: Adjacent occupied buckets satisfy
   `nextEntry.psl ≤ entry.psl + 1` — the Robin Hood property.
4. **`noSpuriousGaps`**: An occupied bucket after an empty bucket has `psl = 0`
   (starts a new probe chain).

`empty_wellFormed`: All buckets are `none`, so all four components hold vacuously.

**Proof path**: Each component for `empty` follows from `List.replicate` producing
all-`none` entries. The key lemma needed:
```
∀ i, (Array.mk (List.replicate n none)).get i = none
```
This follows from `List.getElem_replicate` in Lean 4.28.0.

**Dependencies**: None (foundational).

---

#### Task N1-H: `insertCore_contains_self` — inserted key is retrievable

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (line 305)
**Status**: Stated, sorry placeholder
**Dependencies**: N1-G (empty_wellFormed)

**Theorem**: `(m.insertCore k v).get? k = some v`

**Proof strategy** (decomposed into 3 sub-steps):

1. **Trace `insertCore.go`**: Starting from `idealIndex k` with `dist = 0`,
   the loop terminates by placing `⟨k, v, dist⟩` at some bucket `idx`. There
   are three terminal cases:
   - Empty bucket at `idx`: entry placed directly.
   - Key match at `idx`: entry updated in place (same `idx`, same PSL).
   - Fuel exhaustion: impossible when `WellFormed` (capacity > size ≥ 0).

2. **Show `get?.go` finds it**: `get?.go` starts from the same `idealIndex k`
   and probes forward. At bucket `idx`, it finds `entry.key == k = true`
   and returns `some entry.val = some v`. The key insight: no bucket between
   `idealIndex k` and `idx` (exclusive) contains key `k` (from `noDuplicateKeys`),
   and no bucket in that range has `psl < dist` where `dist` would cause early
   termination before reaching `idx` (from `robinHoodOrdering`).

3. **Handle Robin Hood displacement case**: If displacement occurred at some
   intermediate bucket, `k`'s entry was swapped in at that bucket. The
   displaced entry continues insertion further along. After insertion completes,
   `k` is at the swap-in position with correct PSL, and `get?` finds it there.

**Estimated complexity**: Medium. The proof is an induction on `fuel` matching
the `insertCore.go` loop, with case analysis at each step.

---

#### Task N1-I: `insertCore_preserves_other` — other keys unchanged

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (line 311)
**Status**: Stated, sorry placeholder
**Dependencies**: N1-G, N1-H

**Theorem**: `(k == a) = false → (m.insertCore k v).get? a = m.get? a`

**Proof strategy** (the hardest lemma — decomposed into 4 sub-steps):

1. **Classify `a`'s bucket relative to `k`'s probe chain**:
   - If `idealIndex a ≠ idealIndex k`: `a`'s probe chain doesn't intersect
     `k`'s insertion path. No displacement affects `a`. `get? a` follows the
     same buckets before and after insertion. *Direct.*
   - If `idealIndex a = idealIndex k`: `a` and `k` share a probe chain prefix.
     Displacement analysis needed.

2. **Displacement analysis for shared probe chains**: `insertCore.go` may
   displace entries along the chain. For key `a` at bucket `idx_a` with
   `psl_a`:
   - If `k`'s insertion point is *before* `idx_a`: `k` displaces entries
     forward. `a`'s entry shifts from `idx_a` to `idx_a + 1` with
     `psl_a + 1`. Lookup for `a` still finds it because it probes one
     bucket further (PSL matches).
   - If `k`'s insertion point is *after* `idx_a`: `a`'s entry is untouched.
   - If `k`'s insertion fills an empty bucket: no displacement, `a` untouched.

3. **Prove lookup correctness after displacement**: For each case above,
   show that `get?.go` starting from `idealIndex a` reaches `a`'s (possibly
   shifted) bucket and the PSL/early-termination check passes.

4. **Inductive argument**: By induction on `fuel`, matching `insertCore.go`.
   At each step, case-split on the three insertion paths and show `a`'s
   lookup is preserved.

**Estimated complexity**: High. This is the proof that makes Robin Hood hashing
non-trivial. The key helper lemma needed:

```lean
-- If entry at idx has psl = p, and we insert at idx with higher dist,
-- the displaced entry at idx+1 has psl = p+1, preserving get? for its key.
theorem displacement_preserves_findability ...
```

---

#### Task N1-J: `insertCore_wellFormed` + `resize_wellFormed`

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (lines 322, 328)
**Status**: Stated, sorry placeholders (2)
**Dependencies**: N1-H, N1-I

**Theorem 1**: `WellFormed m → WellFormed (m.insertCore k v)`

Proof by case analysis on each WF component:
- `pslCorrect`: New/updated entry has correct PSL by construction. Displaced
  entries have PSL incremented to match their new position.
- `noDuplicateKeys`: Key match case updates in place (no new key). Empty
  bucket case adds new key. Displacement preserves existing keys.
- `robinHoodOrdering`: Displacement maintains the ordering property by
  construction — we only swap when `entry.psl < dist`.
- `noSpuriousGaps`: Filling empty bucket doesn't create gaps. Displacement
  shifts entries forward, maintaining gap structure.

**Theorem 2**: `WellFormed m → WellFormed m.resize`

By `Array.foldl` induction: start with `empty_wellFormed`, each `insertCore`
preserves WF (from Theorem 1).

---

#### Task N1-K: `erase_removes_self` + `erase_preserves_other` + `erase_wellFormed`

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (lines 334, 340, 347)
**Status**: Stated, sorry placeholders (3)
**Dependencies**: N1-G

**Theorem 1**: `(m.erase k).get? k = none`

`findIndex` locates `k` at bucket `idx`. After clearing bucket `idx` to `none`,
`backwardShift` may move subsequent entries backward but never reintroduces `k`.
`get?.go` starting from `idealIndex k` reaches bucket `idx` (now `none`) and
returns `none`.

**Theorem 2**: `(k == a) = false → (m.erase k).get? a = m.get? a`

Two cases:
- `a`'s bucket is *not* in the backward-shift range: untouched, lookup same.
- `a`'s bucket *is* shifted backward: `a`'s entry moves from `idx_a` to
  `idx_a - 1` with `psl - 1`. Lookup follows the same probe chain and finds
  `a` one position earlier.

**Theorem 3**: `WellFormed m → WellFormed (m.erase k)`

Clear + backwardShift preserves all four WF components. The key insight for
`robinHoodOrdering`: shifting backward and decrementing PSL maintains the
`nextEntry.psl ≤ entry.psl + 1` invariant.

---

#### Task N1-L: `get?_insert`, `get?_erase`, `get?_empty_simp` — bridge composition

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (lines 356–383)
**Status**: Stated, sorry placeholders (4 — in the BEq rewrite cases)
**Dependencies**: N1-H, N1-I, N1-J, N1-K

These compose the decomposition lemmas:

```lean
theorem get?_insert (wf) :
    (m.insert k v).get? a = if k == a then some v else m.get? a
-- Proof: unfold insert, case split on resize, apply
-- insertCore_contains_self / insertCore_preserves_other / resize_preserves_get?

theorem get?_erase (wf) :
    (m.erase k).get? a = if k == a then none else m.get? a
-- Proof: case split on k == a, apply erase_removes_self / erase_preserves_other

theorem get?_empty_simp : (∅ : RobinHoodHashMap α β).get? a = none
-- Proof: unfold get? on all-none buckets
```

The remaining sorry in each `true` branch of `k == a` requires a `BEq`
rewrite: `k == a = true → get? a = get? k`. This follows from `EquivBEq`
and `LawfulHashable`: `k == a → hash k = hash a → idealIndex k = idealIndex a`,
plus the lookup algorithm is deterministic given the same ideal index.

**Helper lemma needed**:
```lean
theorem get?_beq_eq [EquivBEq α] [LawfulHashable α] (m : RobinHoodHashMap α β)
    (k a : α) (h : k == a = true) : m.get? k = m.get? a
```

---

#### Task N1-M: `fold_eq_foldl_toList` + `size_erase_le`

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (lines 385, 391)
**Status**: Stated, sorry placeholders (2)
**Dependencies**: None (self-contained)

**`fold_eq_foldl_toList`**: Convert `Array.foldl` to `List.foldl` via
`Array.foldl_toList` (or manual `Array.size` induction), then show the
`filterMap` transformation commutes with `foldl` by list induction.

**`size_erase_le`**: Unfold `erase`, case split on `findIndex`. If key found,
`size - 1 ≤ size`. `backwardShift` doesn't change `size` (it moves entries,
not adds/removes them).

---

#### Task N1-N: RobinHoodHashSet wrapper + Prelude integration (COMPLETE — sorry placeholders)

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (lines 397–468)
**File**: `SeLe4n/Prelude.lean` (type aliases — pending)
**Status**: HashSet defined, bridge lemma signatures stated, sorry placeholders (5)
**Dependencies**: N1-L (all sorry resolution flows from HashMap bridge lemmas)

**HashSet** (`RobinHoodHashSet`): Thin wrapper over `RobinHoodHashMap α Unit`.
All operations delegate: `insert a = ⟨inner.insert a ()⟩`, `contains = inner.contains`,
`erase = ⟨inner.erase a⟩`, etc.

**Bridge lemmas** (5 stated with sorry):
- `contains_empty`: Unfolds to `get?_empty_simp`
- `contains_insert_iff`: Unfolds to `get?_insert`
- `not_contains_insert`: From `contains_insert_iff`
- `contains_insert_self`: From `contains_insert_iff`
- `contains_erase`: Unfolds to `get?_erase`

All 5 HashSet sorry placeholders resolve automatically once the HashMap bridge
lemmas (N1-L) are proved — they are compositional, not independently difficult.

**Prelude integration** (deferred to just before WS-N3 migration):
```lean
abbrev KernelHashMap (α : Type) (β : Type) [BEq α] [Hashable α] :=
  SeLe4n.Data.RobinHoodHashMap α β
abbrev KernelHashSet (α : Type) [BEq α] [Hashable α] :=
  SeLe4n.Data.RobinHoodHashSet α
```

**Verification**: `lake build` succeeds. New module compiles independently.
Existing code unchanged (no migration yet).

---

#### WS-N1 Sorry Resolution Summary

| Task | Sorry Count | Depends On | Difficulty |
|------|------------|------------|------------|
| N1-G | 5 | — | Low (vacuous on empty) |
| N1-H | 1 | N1-G | Medium |
| N1-I | 1 | N1-G, N1-H | **High** (displacement analysis) |
| N1-J | 2 | N1-H, N1-I | Medium (WF preservation) |
| N1-K | 3 | N1-G | Medium (backward-shift analysis) |
| N1-L | 4 | N1-H–K | Low (composition + BEq rewrite) |
| N1-M | 2 | — | Low (Array/List conversion) |
| N1-N | 5 | N1-L | Low (compositional on HashMap) |
| **Total** | **23** | | |

**Critical path**: N1-G → N1-H → N1-I → N1-J → N1-L → N1-N
**Parallel track**: N1-K (independent of N1-H/I), N1-M (fully independent)

**Recommended resolution order**:
1. N1-G + N1-M (easiest, unblocks everything)
2. N1-K (medium, independent track)
3. N1-H (medium, critical path)
4. N1-I (hardest — budget extra time)
5. N1-J (follows from H+I)
6. N1-L + N1-N (composition, flows naturally)

---

### Phase 2: resolveCapAddress Leaf-Level Occupancy Fix (WS-N2)

**Target version**: 0.17.2
**Files modified**: `SeLe4n/Kernel/Capability/Operations.lean`,
`SeLe4n/Kernel/Capability/Invariant/Defs.lean`,
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Findings addressed**: N-C01, N-P02
**Subtasks**: 5 atomic units (N2-A through N2-E)

---

#### Task N2-A: Add leaf-level occupancy check to `resolveCapAddress`

**File**: `Operations.lean:94–95`

**Current code** (leaf path):
```lean
if bitsRemaining - consumed = 0 then
  .ok { cnode := rootId, slot := slot }   -- NO occupancy check
```

**Corrected code**:
```lean
if bitsRemaining - consumed = 0 then
  match cn.lookup slot with
  | some _ => .ok { cnode := rootId, slot := slot }
  | none => .error .invalidCapability     -- leaf occupancy check
```

This makes the leaf path consistent with the intermediate path (lines 97–106),
which already checks `cn.lookup slot`. The function now checks occupancy at
**every level** of CSpace resolution.

**Impact on callers**:

| Caller | Current Behavior | New Behavior |
|--------|-----------------|--------------|
| `syscallLookupCap` (API.lean:165) | Resolve ok → lookupSlotCap → may fail | Resolve fails early on empty leaf |
| `resolveExtraCaps` (API.lean:368) | Resolve ok → lookupSlotCap → may drop | Resolve fails early on empty leaf |
| `cspaceLookupMultiLevel` (Ops:121) | Resolve ok → cspaceLookupSlot → may fail | Resolve fails early on empty leaf |

All callers already handle `.error .invalidCapability`, so no caller changes
needed. Callers are now **simplified**: after a successful resolve, the slot
is guaranteed to be occupied.

**Termination**: Unchanged — the termination proof uses `bitsRemaining` descent,
which is unaffected by the occupancy check.

---

#### Task N2-B: Update `resolveCapAddress_result_valid_cnode` theorem

**File**: `Operations.lean:152–188`

The existing theorem proves that successful resolution returns a valid CNode.
After the fix, it can be strengthened to also prove the slot is occupied:

```lean
theorem resolveCapAddress_result_valid_cnode_and_slot
    (rootId : ObjId) (addr : CPtr) (bits : Nat) (st : SystemState)
    (ref : SlotRef)
    (hOk : resolveCapAddress rootId addr bits st = .ok ref) :
    ∃ cn : CNode, st.objects[ref.cnode]? = some (.cnode cn) ∧
    ∃ cap : Capability, cn.lookup ref.slot = some cap := by
  ...
```

The proof follows the same strong induction pattern as the current theorem,
with an additional `cn.lookup` extraction at both the leaf and recursive cases.

The original `resolveCapAddress_result_valid_cnode` is retained for backward
compatibility (its conclusion is a weaker consequence of the strengthened
version).

---

#### Task N2-C: Update `resolveCapAddress_guard_match` theorem

**File**: `Operations.lean:243–266`

The guard match theorem's proof unfolds `resolveCapAddress` and traces through
the leaf path. After the fix, the leaf path has an additional `cn.lookup`
match. The proof must be updated to split on this new case — the error branch
is eliminated by the `hOk` hypothesis, and the success branch proceeds as
before.

This is a mechanical proof update: one additional `split at hOk` + `simp at hOk`
for the empty-slot error case.

---

#### Task N2-D: Update invariant preservation theorems

**File**: `Invariant/Preservation.lean`

Any preservation theorem that unfolds `resolveCapAddress` and traces through
the leaf path needs updating. Grep for `resolveCapAddress` in preservation files:

- `resolveCapAddress_result_valid_cnode` (already addressed in N2-B)
- Any theorem composing `resolveCapAddressK` or `cspaceLookupMultiLevel`

Since `cspaceLookupMultiLevel` composes `resolveCapAddress` + `cspaceLookupSlot`,
and the new behavior only adds an additional error path (empty slot → error)
that was already handled by `cspaceLookupSlot`, most composition theorems
remain unchanged. The key change: `cspaceLookupSlot` after a successful resolve
now always succeeds (slot guaranteed occupied), which **simplifies** several
proofs.

---

#### Task N2-E: Update docstring and add characterization theorem

**File**: `Operations.lean:64–75`

Update the `resolveCapAddress` docstring to document the leaf-level occupancy
check:

```lean
/-- WS-N2/N-C01: Multi-level CSpace capability address resolution.

...
4. If all bits are consumed, looks up the slot and returns the resolved slot
   reference if the slot is occupied. Returns `.error .invalidCapability`
   if the leaf slot is empty.
...

Slot occupancy is checked at EVERY level:
- Intermediate: `cn.lookup slot` for child CNode traversal (line 97)
- Leaf: `cn.lookup slot` for final slot validation (new in WS-N2) -/
```

Add a theorem characterizing the strengthened behavior:

```lean
theorem resolveCapAddress_success_implies_occupied
    (rootId : ObjId) (addr : CPtr) (bits : Nat) (st : SystemState)
    (ref : SlotRef)
    (hOk : resolveCapAddress rootId addr bits st = .ok ref) :
    ∃ cn cap, st.objects[ref.cnode]? = some (.cnode cn) ∧
              cn.lookup ref.slot = some cap := by
  exact resolveCapAddress_result_valid_cnode_and_slot rootId addr bits st ref hOk
```

**Verification**: `lake build` succeeds. `test_smoke.sh` passes. All existing
tests remain green (callers already handled the error case).

---

### Phase 3: HashMap/HashSet Migration (WS-N3)

**Target version**: 0.17.3
**Files modified**: 11 source files (76 `Std.HashMap` + 25 `Std.HashSet` call sites)
**Findings addressed**: N-P01 (completion), N-P03, N-D01, N-D02
**Subtasks**: 7 atomic units (N3-A through N3-G)

Phase 3 replaces all `Std.HashMap`/`Std.HashSet` usage with the Robin Hood
implementations from Phase 1. The migration is mechanical: type swaps + bridge
lemma name updates.

---

#### Task N3-A: Migrate `Model/State.lean` (10 `Std.HashMap` call sites)

The `SystemState` structure holds 8 HashMap fields and 1 HashSet field.

**Type changes**:
```lean
-- Before:
objects : Std.HashMap ObjId KernelObject
-- After:
objects : KernelHashMap ObjId KernelObject
```

Apply to all 8 HashMap fields: `objects`, `objectTypes`, `capabilityRefs`,
`services`, `irqHandlers`, `asidTable`, `cdtSlotNode`, `cdtNodeSlot`.

Apply to HashSet field: `objectIndexSet : KernelHashSet ObjId`.

**Proof updates**: 6 `revokeAndClearRefsState` preservation theorems use
`Std.HashMap.fold_eq_foldl_toList`. Replace with
`RobinHoodHashMap.fold_eq_foldl_toList`. The proofs are structurally identical —
both rewrite `fold` into `List.foldl` over `toList`, then induct on the list.

2 `storeObject` lemmas use `Std.HashMap.getElem?_insert`. Replace with
`RobinHoodHashMap.getElem?_insert`.

---

#### Task N3-B: Migrate `Model/Object/Types.lean` and `Structures.lean`

**Types.lean**: `CNode.slots : Std.HashMap Slot Capability` →
`CNode.slots : KernelHashMap Slot Capability`

**Structures.lean (6 call sites)**:
- `VSpaceRoot.mappings : Std.HashMap VAddr (PAddr × PagePermissions)` →
  `KernelHashMap`
- `CNode.mk'` constructor parameter: `Std.HashMap` → `KernelHashMap`
- `CNode.slotCountBounded_remove` uses `Std.HashMap.size_erase_le` → use
  `RobinHoodHashMap.size_erase_le`
- `CNode.slotCountBounded_revokeTargetLocal` uses
  `Std.HashMap.size_filter_le_size` → use `RobinHoodHashMap.size_filter_le`
- `CNode.revokeTargetLocal_source_preserved` uses
  `Std.HashMap.mem_iff_isSome_getElem?` → use Robin Hood equivalent
- `CNode.BEq` and `VSpaceRoot.BEq` use `.fold` — unchanged API

**CDT fields**: `CapDerivationTree.childMap`, `.parentMap` → `KernelHashMap`

---

#### Task N3-C: Migrate `Kernel/Scheduler/RunQueue.lean` (5 `Std.HashMap` + 13 `Std.HashSet`)

The `RunQueue` structure uses:
- `byPriority : Std.HashMap Priority (List ThreadId)` → `KernelHashMap`
- `membership : Std.HashSet ThreadId` → `KernelHashSet`
- `threadPriority : Std.HashMap ThreadId Priority` → `KernelHashMap`

**Proof updates (13 HashSet call sites)**: All RunQueue proofs use
`Std.HashSet.contains_insert`, `Std.HashSet.contains_erase`, etc. Replace with
`RobinHoodHashSet.contains_insert`, etc.

**RunQueue bridge lemmas**: `mem_insert`, `mem_remove`, `mem_rotateHead`,
`mem_rotateToBack`, `not_mem_remove_self`, `not_mem_toList_of_not_mem`,
`mem_toList_iff_mem`. These use `Std.HashSet` API internally — update to
`KernelHashSet` API.

**`recomputeMaxPriority`**: Uses `byPrio.fold` — fold API unchanged.

---

#### Task N3-D: Migrate `Kernel/Capability/Invariant/` (12 call sites)

**Invariant/Defs.lean (6 sites)**: Uses `HashMap_getElem?_erase` (2),
`Std.HashMap.getElem?_erase` (1), `Std.HashMap.mem_iff_isSome_getElem?` (1),
`Std.HashMap.mem_of_mem_filter` (1), `Std.HashMap.getElem_filter` (1).

**Invariant/Authority.lean (6 sites)**: Uses `Std.HashMap.mem_iff_isSome_getElem?`,
`Std.HashMap.mem_filter`, `Std.HashMap.getKey_beq`, `Std.HashMap.getElem_filter`,
`Std.HashMap.getElem?_insert`.

Replace all with `KernelHashMap_*` / `RobinHoodHashMap.*` equivalents.

---

#### Task N3-E: Migrate `Kernel/Scheduler/Operations/Preservation.lean` (~30 call sites)

This is the largest single file for migration. All 30+ uses are
`HashMap_getElem?_insert` in scheduler preservation proofs. Replace with
`KernelHashMap_getElem?_insert`. The proofs are structurally identical —
only the lemma name changes.

---

#### Task N3-F: Migrate remaining files

- `Kernel/Lifecycle/Operations.lean` (3 sites): `Std.HashMap.fold_eq_foldl_toList`
- `Kernel/InformationFlow/Projection.lean` (3 sites): `HashMap_filter_filter_getElem?`,
  `Std.HashSet` projection
- `Kernel/InformationFlow/Invariant/Helpers.lean` (1 site)
- `Kernel/InformationFlow/Invariant/Operations.lean` (5 sites)
- `Kernel/Architecture/VSpaceInvariant.lean` (5 sites)
- `Kernel/Architecture/Invariant.lean` (2 sites)
- `Kernel/Service/Invariant/Acyclicity.lean` (2 HashSet sites)
- `Testing/StateBuilder.lean` (7 sites)
- `Testing/MainTraceHarness.lean` (10 sites)

---

#### Task N3-G: Remove `Std.HashMap`/`Std.HashSet` bridge lemmas from Prelude

After all migration is complete, the `HashMap_*` bridge lemmas in
`Prelude.lean:676–816` can be:
1. **Redirected**: Changed from delegating to `Std.DHashMap.*` to delegating to
   `RobinHoodHashMap.*` — making them aliases for the new implementation.
2. **Or retained as-is**: If `Std.HashMap` is still imported elsewhere, keep
   both sets of lemmas during a transition period.

Recommended: Option 1 (redirect). This eliminates the `Std.HashMap` dependency
from the proof surface entirely.

**Verification**: Full `lake build` succeeds. `test_smoke.sh` passes.
`test_full.sh` passes. No `Std.HashMap` or `Std.HashSet` references remain
in `SeLe4n/` source files (only in imports if any).

---

### Phase 4: Test Coverage & Determinism Validation (WS-N4)

**Target version**: 0.17.4
**Files modified**: `tests/NegativeStateSuite.lean`, `tests/OperationChainSuite.lean`,
`SeLe4n/Testing/MainTraceHarness.lean`, `tests/fixtures/main_trace_smoke.expected`,
`scripts/test_tier2_determinism.sh`
**Findings addressed**: N-T01, N-T02, N-T03
**Subtasks**: 6 atomic units (N4-A through N4-F)

---

#### Task N4-A: Robin Hood HashMap unit tests

**File**: `tests/OperationChainSuite.lean`

Add test scenarios exercising the Robin Hood HashMap implementation:

1. **SCN-RH-INSERT-LOOKUP**: Insert 100 entries with sequential keys, verify
   all are retrievable via `get?`. Verify `size = 100`.

2. **SCN-RH-DISPLACEMENT**: Insert entries with colliding hashes (same ideal
   index). Verify Robin Hood displacement occurs — entries with longer PSL
   displace entries with shorter PSL. Verify all entries remain retrievable.

3. **SCN-RH-ERASE-SHIFT**: Insert entries, erase one from the middle of a
   probe chain. Verify backward-shift correctly moves subsequent entries.
   Verify all remaining entries are still retrievable.

4. **SCN-RH-RESIZE**: Insert entries until load factor exceeds 7/8. Verify
   resize doubles capacity. Verify all entries survive resize and remain
   retrievable.

5. **SCN-RH-COLLISION-CHAIN**: Create a pathological hash collision (all keys
   hash to index 0). Verify the probe chain is bounded and all entries are
   findable. Verify PSL values are monotonically non-decreasing along the chain.

---

#### Task N4-B: resolveCapAddress leaf occupancy tests

**File**: `tests/NegativeStateSuite.lean`

Add test scenarios exercising the new leaf-level occupancy check:

1. **SCN-RESOLVE-LEAF-EMPTY**: Create a CNode with an empty slot at the
   resolved index. Call `resolveCapAddress` with bits that resolve to this
   slot. Verify `.error .invalidCapability` is returned.

2. **SCN-RESOLVE-LEAF-OCCUPIED**: Same setup but with an occupied slot.
   Verify `.ok` with correct `SlotRef`.

3. **SCN-RESOLVE-CONSISTENCY**: Verify that intermediate and leaf paths
   behave identically for empty slots — both return `.error .invalidCapability`.

---

#### Task N4-C: Update test fixture

**File**: `tests/fixtures/main_trace_smoke.expected`

If the `resolveCapAddress` fix changes any trace output (e.g., a scenario that
previously returned a SlotRef for an empty leaf now returns an error), update
the fixture file accordingly. Document the rationale for each fixture change.

---

#### Task N4-D: Determinism strengthening

**File**: `scripts/test_tier2_determinism.sh`

Enhance the determinism test:
- Run trace **3 times** (instead of 2) and verify all 3 outputs are identical.
- Add a comment explaining that Robin Hood hashing maintains deterministic
  iteration order for the same operation sequence.

---

#### Task N4-E: Full test suite validation

Run all test tiers and fix any failures:

```bash
./scripts/test_fast.sh       # Tier 0+1
./scripts/test_smoke.sh      # Tier 0-2
./scripts/test_full.sh       # Tier 0-3
```

**sorry audit**: Grep for `sorry` in all `.lean` files. Zero must remain.
If any were introduced as placeholders during development, resolve them now.

**Warning audit**: Run `lake build 2>&1 | grep -i warning` and fix all
warnings. Zero warnings allowed.

---

#### Task N4-F: Resolve all sorry placeholders

If any `sorry` was used during Phases 1–3 as a development placeholder, this
task resolves them. Each `sorry` must be replaced with a complete proof.

Approach:
1. `grep -rn sorry SeLe4n/ tests/` — list all instances
2. For each, determine the proof strategy from context
3. Replace with machine-checked proof
4. Verify via `lake build` + `test_smoke.sh`

**Zero sorry/axiom in production proof surface** is the project's hard constraint.

**Verification**: `test_full.sh` passes. `grep -rn sorry SeLe4n/` returns zero
results. `grep -rn axiom SeLe4n/` returns zero results (excluding comments).

---

### Phase 5: Documentation Sync (WS-N5)

**Target version**: 0.17.5
**Findings addressed**: (documentation)
**Subtasks**: 6 atomic units (N5-A through N5-F)

---

#### Task N5-A: Update `WORKSTREAM_HISTORY.md`

Add WS-N entry with phase summaries:

```markdown
### WS-N workstream (IPC & Capability cross-audit: Robin Hood hashing, determinism & correctness)

WS-N is a **completed** workstream portfolio (v0.17.1–v0.17.5), created from a
comprehensive cross-subsystem audit of the IPC and Capability subsystems
(15,000+ LoC, 20+ files). The audit found zero sorry/axiom, zero critical
vulnerabilities, but identified performance optimization opportunities via
Robin Hood hashing, a resolveCapAddress leaf-level asymmetry, and test
coverage gaps. All 5 phases delivered.
```

---

#### Task N5-B: Update `SELE4N_SPEC.md`

Document the Robin Hood HashMap as a kernel primitive:
- Add section on HashMap implementation choice (Robin Hood open-addressing)
- Document cache locality rationale for ARM64
- Document deterministic fold order guarantee

Update CSpace section:
- Document `resolveCapAddress` leaf-level occupancy check
- Reference `resolveCapAddress_success_implies_occupied` theorem

---

#### Task N5-C: Update `DEVELOPMENT.md`

Add Robin Hood HashMap to the "Key data structures" section.
Update the "Performance optimizations" section with Robin Hood rationale.
Update the dependency map if `SeLe4n/Data/` is a new module directory.

---

#### Task N5-D: Update `CLAIM_EVIDENCE_INDEX.md`

Add evidence entries:
- Robin Hood HashMap bridge lemma correctness (14+5 lemmas proved)
- `resolveCapAddress` leaf-level occupancy guarantee (new theorem)
- End-to-end determinism (strengthened `test_tier2_determinism.sh`)

---

#### Task N5-E: Update GitBook chapters

Update affected chapters:
- `docs/gitbook/12-proof-and-invariant-map.md`: Add Robin Hood HashMap proofs
- `docs/gitbook/` architecture chapter: Document CSpace resolution fix
- Any chapter referencing HashMap implementation

---

#### Task N5-F: Regenerate codebase map and sync README

```bash
# Regenerate codebase map
python3 scripts/generate_codebase_map.py  # or equivalent
# Sync README metrics
# Update version to 0.17.5 in lakefile.toml
```

**Verification**: `test_smoke.sh` passes (includes `test_docs_sync.sh`).
All documentation cross-references are valid.

---

## 6. Dependency Graph

```
N1-A → N1-B → N1-C → N1-D → N1-E → N1-F → N1-G → N1-H
                                                      ↓
N2-A → N2-B → N2-C → N2-D → N2-E ─────────────────→ N3-A → N3-B → ... → N3-G
                                                                            ↓
                                                      N4-A → N4-B → ... → N4-F
                                                                            ↓
                                                      N5-A → N5-B → ... → N5-F
```

Phase 1 (N1) and Phase 2 (N2) are **independent** and can be developed in
parallel. Phase 3 (N3) depends on both N1 and N2 completing. Phase 4 (N4)
depends on N3. Phase 5 (N5) depends on N4.

Within each phase, subtasks are ordered by dependency and should be completed
sequentially.

---

## 7. Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Robin Hood `getElem?_insert` proof is complex | HIGH | MEDIUM | Proof by strong induction on probe distance. Robin Hood displacement preserves a key invariant: displaced entries' PSL values are updated, so lookup early-termination still works. Budget 2–3 days for this proof. |
| HashMap migration introduces subtle proof breakage | MEDIUM | HIGH | Migrate one file at a time. Run `lake build` after each file. The bridge lemmas have identical signatures — most proofs compile with only name changes. |
| `resolveCapAddress` fix changes observable behavior | LOW | MEDIUM | All API callers already handle `.error .invalidCapability`. The fix only surfaces errors earlier. Update test fixtures if trace output changes. |
| Robin Hood resize invalidates references | LOW | LOW | References in the kernel are to `SlotRef`/`ObjId` (logical keys), not to physical HashMap positions. Resize is transparent to all callers. |
| Performance regression from `filter` rebuild | LOW | LOW | `filter` rebuilds the map from scratch. For kernel CNode sizes (≤ 4096), this is negligible. Profile on RPi5 if concerned. |

---

## 8. Success Criteria

- [ ] Robin Hood HashMap compiles with zero `sorry`/`axiom`
- [ ] All 14 HashMap + 5 HashSet bridge lemmas proved
- [ ] `resolveCapAddress` checks occupancy at leaf level
- [ ] `resolveCapAddress_success_implies_occupied` theorem proved
- [ ] All `Std.HashMap`/`Std.HashSet` replaced with `KernelHashMap`/`KernelHashSet`
- [ ] Zero `sorry`/`axiom` in production proof surface
- [ ] `test_fast.sh` passes (Tier 0+1)
- [ ] `test_smoke.sh` passes (Tier 0–2)
- [ ] `test_full.sh` passes (Tier 0–3)
- [ ] Zero compiler warnings
- [ ] All documentation synchronized
- [ ] GitBook chapters updated
- [ ] Codebase map regenerated
- [ ] README metrics synced
