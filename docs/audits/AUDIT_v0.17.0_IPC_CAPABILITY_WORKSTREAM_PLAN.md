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
**Subtasks**: 10 atomic units (N1-A through N1-J)

This phase creates the complete Robin Hood HashMap and HashSet implementations
with all bridge lemmas needed by the existing proof surface. No migration yet —
Phase 1 establishes the foundation; Phase 3 migrates.

**Key design refinements from original plan**:

1. **Fuel-based termination for insert**: The original plan used
   `termination_by m.capacity - dist` for `insertCore`. This is unsound:
   Robin Hood displacement resets `dist` to `oldPsl + 1 ≤ dist`, so the measure
   is non-strictly decreasing. Changed to fuel-bounded (`fuel := capacity`)
   which is sound and matches the erase strategy.

2. **Unified bucket representation**: Instead of separate `Array (Option (α × β))`
   and `Array UInt8` PSL arrays (requiring two structural invariants), use a
   single `Array (Option (α × β × Nat))` where each bucket stores its PSL
   inline. This halves the structural invariants and simplifies all proofs while
   maintaining the same cache-friendly flat `Array` layout. The PSL is stored as
   `Nat` (not `UInt8`) to avoid `UInt8.toNat` coercion noise in proofs.

3. **Specification-based bridge proofs**: Bridge lemmas are proved via a
   specification function `toAssocList` that extracts the logical key→value
   mapping. Operations are proved correct against this specification, and bridge
   lemmas follow as corollaries.

4. **`contains` and `Membership` instance**: Added as N1-F2, required by
   existing `HashSet.contains` usage patterns (76+ call sites).

5. **Subtask granularity**: N1-D (insert) split into N1-D (insertCore) and
   N1-D2 (resize + public insert). N1-F split into N1-F (fold/toList/filter)
   and N1-F2 (contains/Membership/size). Total: 10 subtasks.

---

#### Task N1-A: Core data structure definition

**File**: `SeLe4n/Data/RobinHoodHashMap.lean`

Define `RobinHoodHashMap` as an open-addressing hash table using Lean 4's
`Array` for flat memory layout.

```lean
structure RobinHoodHashMap (α : Type) (β : Type) [BEq α] [Hashable α] where
  buckets  : Array (Option (α × β × Nat))  -- flat bucket array; none = empty, Nat = PSL
  size     : Nat                            -- number of occupied entries
  capacity : Nat                            -- bucket count (= buckets.size)
  hCapacity : buckets.size = capacity       -- structural invariant
```

**Design decisions**:

1. **Unified bucket representation** (`Array (Option (α × β × Nat))`): PSL is
   stored inline with key-value pairs in a single `Array`. This eliminates the
   need for a separate PSL array and halves structural invariants (one `hCapacity`
   instead of `hBuckets` + `hPsl`). Each bucket is either `none` (empty) or
   `some (key, value, psl)`. The PSL is `Nat` (not `UInt8`) to avoid coercion
   noise in proofs — Lean compiles small `Nat` values efficiently.

2. **`Array`-backed, not `List`-backed**: Lean 4's `Array` compiles to a flat
   C heap allocation. In-place mutation via FBIP when the reference is unique
   (which it always is in our kernel monad). This gives true O(1) random access
   and cache-friendly sequential iteration — matching C `malloc`+index
   performance.

3. **Power-of-two capacity**: `capacity` is always a power of 2, enabling
   `hash % capacity` → `hash &&& (capacity - 1)` bitwise masking. This
   is a standard Robin Hood optimization.

4. **Nat PSL**: Expected maximum PSL is ~O(log n). With n ≤ 65536 (largest
   expected map), max PSL ≈ 16. Using `Nat` over `UInt8` avoids
   `UInt8.toNat` conversions in proofs while Lean's compiler optimizes small
   `Nat` values to unboxed integers.

5. **No well-formedness proof in structure**: Unlike `Std.HashMap` which bundles
   `WF`, we use a single structural size invariant (`hCapacity`) only. The Robin
   Hood displacement invariant is maintained operationally and proved externally
   via bridge lemmas. This avoids proof overhead in hot-path operations.

**Verification**: `lake build` succeeds with the new file. No downstream
dependencies yet.

---

#### Task N1-B: Core operations — `empty`, `bucketIndex`, helpers

**File**: `SeLe4n/Data/RobinHoodHashMap.lean`

```lean
def defaultCapacity : Nat := 16

def nextPowerOfTwo (n : Nat) : Nat :=
  if n ≤ 1 then 1
  else Nat.nextPowerOfTwo n  -- Lean's built-in

def empty (cap : Nat := defaultCapacity) : RobinHoodHashMap α β :=
  let c := nextPowerOfTwo (max cap 4)
  { buckets   := Array.mkArray c none
    size      := 0
    capacity  := c
    hCapacity := Array.size_mkArray c none }

@[inline] def bucketIndex (m : RobinHoodHashMap α β) (k : α)
    (hCap : m.capacity > 0 := by omega) : Nat :=
  (hash k).toUInt64.toNat % m.capacity

@[inline] def wrapIndex (m : RobinHoodHashMap α β) (i : Nat) : Nat :=
  i % m.capacity
```

Index operations use modular arithmetic (`% capacity`). For power-of-two
capacities, the compiler can lower `%` to a bitwise `AND` — a single ARM64
instruction. `wrapIndex` wraps probe positions circularly.

**Helper**: `nextPowerOfTwo` uses Lean's built-in `Nat.nextPowerOfTwo` which
rounds up via bit manipulation.

---

#### Task N1-C: Core operation — `get?` (lookup)

**File**: `SeLe4n/Data/RobinHoodHashMap.lean`

```lean
def get? [BEq α] [Hashable α] (m : RobinHoodHashMap α β) (k : α) : Option β :=
  if h : m.capacity = 0 then none
  else loop (m.bucketIndex k) 0 m.capacity
where
  loop (idx dist fuel : Nat) : Option β :=
    if fuel = 0 then none
    else
      match m.buckets[idx % m.capacity]? with
      | none => none  -- empty bucket = key absent
      | some none => none  -- should not occur at valid idx
      | some (some (k', v, psl)) =>
        if k' == k then some v
        else if psl < dist then none  -- Robin Hood early termination
        else loop ((idx + 1) % m.capacity) (dist + 1) (fuel - 1)
  termination_by fuel
```

**Robin Hood early termination**: The key performance insight. During lookup,
if we encounter an entry whose PSL is less than our current probe distance,
we know the target key cannot exist further along the probe chain. This is
because Robin Hood displacement ensures that entries with longer probe
distances are never "behind" entries with shorter distances. This bounds
worst-case lookup to O(max PSL) which is O(log n) expected.

**Termination**: Proved by strict descent on `fuel`. Fuel is bounded by
`capacity` — lookup terminates in at most `capacity` probes.

---

#### Task N1-D: Core operation — `insertCore` with Robin Hood displacement

**File**: `SeLe4n/Data/RobinHoodHashMap.lean`

```lean
def insertCore (m : RobinHoodHashMap α β) (k : α) (v : β) : RobinHoodHashMap α β :=
  if h : m.capacity = 0 then (empty).insertCore k v
  else loop m (m.bucketIndex k) k v 0 m.capacity
where
  loop (m : RobinHoodHashMap α β) (idx : Nat)
       (curK : α) (curV : β) (dist fuel : Nat) : RobinHoodHashMap α β :=
    if fuel = 0 then m  -- safety: should not occur at load factor < 1
    else
      let i := idx % m.capacity
      match h : m.buckets[i]? with
      | none => -- empty bucket: place entry here
        { m with
          buckets  := m.buckets.set ⟨i, by omega⟩ (some (curK, curV, dist))
          size     := m.size + 1
          hCapacity := by simp [Array.size_set, m.hCapacity] }
      | some none => -- same as empty
        { m with
          buckets  := m.buckets.set ⟨i, by omega⟩ (some (curK, curV, dist))
          size     := m.size + 1
          hCapacity := by simp [Array.size_set, m.hCapacity] }
      | some (some (k', v', psl')) =>
        if k' == curK then -- key exists: update value, keep PSL
          { m with
            buckets  := m.buckets.set ⟨i, by omega⟩ (some (curK, curV, psl'))
            hCapacity := by simp [Array.size_set, m.hCapacity] }
        else if psl' < dist then
          -- Robin Hood displacement: swap and continue with displaced entry
          let m' := { m with
            buckets  := m.buckets.set ⟨i, by omega⟩ (some (curK, curV, dist))
            hCapacity := by simp [Array.size_set, m.hCapacity] }
          loop m' ((idx + 1) % m.capacity) k' v' (psl' + 1) (fuel - 1)
        else
          loop m ((idx + 1) % m.capacity) curK curV (dist + 1) (fuel - 1)
  termination_by fuel
```

**Robin Hood displacement**: When inserting and we find an existing entry with
PSL shorter than our current probe distance, we **swap**. The rich entry (long
PSL) takes the spot; the poor entry (short PSL) gets displaced further along
the chain. This equalizes probe chain lengths across all entries.

**Termination**: Fuel-bounded by `capacity`. The original plan used
`termination_by m.capacity - dist` which is **unsound** for Robin Hood
displacement: when an entry with PSL `p` is displaced, the loop continues with
`dist := p + 1` where `p < dist`, so `dist` can decrease. Fuel-based
termination is always correct and matches the erase strategy (N1-E).

**Key invariant**: After insertion, for any two adjacent occupied buckets at
positions i and i+1, `psl[i+1] ≤ psl[i] + 1`. This is the Robin Hood property.

#### Task N1-D2: Resize and public `insert`

**File**: `SeLe4n/Data/RobinHoodHashMap.lean`

```lean
def resize (m : RobinHoodHashMap α β) : RobinHoodHashMap α β :=
  let newCap := m.capacity * 2
  let base := empty newCap
  m.buckets.foldl (init := base) fun acc bucket =>
    match bucket with
    | some (k, v, _) => acc.insertCore k v
    | none => acc

def insert (m : RobinHoodHashMap α β) (k : α) (v : β) : RobinHoodHashMap α β :=
  let m' := m.insertCore k v
  if m'.size * 8 ≥ m'.capacity * 7 then m'.resize else m'
```

**Load factor resize**: After `insertCore`, check `size * 8 ≥ capacity * 7`
(87.5% load). If exceeded, resize to `capacity * 2` and reinsert all entries.
The resize is amortized O(1) per insertion.

---

#### Task N1-E: Core operation — `erase` with backward-shift deletion

**File**: `SeLe4n/Data/RobinHoodHashMap.lean`

```lean
def erase (m : RobinHoodHashMap α β) (k : α) : RobinHoodHashMap α β :=
  if h : m.capacity = 0 then m
  else
    match findIndex m k with
    | none => m  -- key not found
    | some idx => backwardShift (clearBucket m idx) ((idx + 1) % m.capacity)
where
  findIndex (m : RobinHoodHashMap α β) (k : α) : Option Nat :=
    loop (m.bucketIndex k) 0 m.capacity
  where
    loop (idx dist fuel : Nat) : Option Nat :=
      if fuel = 0 then none
      else
        let i := idx % m.capacity
        match m.buckets[i]? with
        | none => none
        | some none => none
        | some (some (k', _, psl)) =>
          if k' == k then some i
          else if psl < dist then none
          else loop ((idx + 1) % m.capacity) (dist + 1) (fuel - 1)
    termination_by fuel

  clearBucket (m : RobinHoodHashMap α β) (idx : Nat) :
      RobinHoodHashMap α β :=
    { m with
      buckets  := m.buckets.set ⟨idx % m.capacity, by omega⟩ none
      size     := m.size - 1
      hCapacity := by simp [Array.size_set, m.hCapacity] }

  backwardShift (m : RobinHoodHashMap α β) (idx : Nat) :
      RobinHoodHashMap α β :=
    loop m idx m.capacity
  where
    loop (m : RobinHoodHashMap α β) (idx fuel : Nat) :
        RobinHoodHashMap α β :=
      if fuel = 0 then m
      else
        let i := idx % m.capacity
        match m.buckets[i]? with
        | none => m  -- empty bucket: done
        | some none => m
        | some (some (k', v', psl)) =>
          if psl = 0 then m  -- at ideal position: done
          else
            -- Shift backward: move entry to previous bucket, decrement PSL
            let prev := (idx + m.capacity - 1) % m.capacity
            let m' := { m with
              buckets := (m.buckets.set ⟨prev, by omega⟩ (some (k', v', psl - 1)))
                           |>.set ⟨i, by omega⟩ none
              hCapacity := by simp [Array.size_set, m.hCapacity] }
            loop m' ((idx + 1) % m.capacity) (fuel - 1)
    termination_by fuel
```

**Backward-shift deletion** (not tombstones): After removing an entry, scan
forward. For each subsequent occupied entry with PSL > 0, move it one position
backward and decrement its PSL. Stop when encountering an empty bucket or an
entry at its ideal position (PSL = 0).

**Why not tombstones**: Tombstones degrade lookup performance over time as the
table fills with "deleted" markers that must be scanned through. Backward-shift
maintains clean probe chains and ensures lookup performance stays optimal.

**Fuel-bounded termination**: The backward shift terminates when it hits an
empty bucket or PSL=0 entry. Fuel bounds the worst case to `capacity` steps.

---

#### Task N1-F: Fold, toList, filter operations

**File**: `SeLe4n/Data/RobinHoodHashMap.lean`

```lean
def fold {γ : Type _} (m : RobinHoodHashMap α β) (init : γ)
    (f : γ → α → β → γ) : γ :=
  m.buckets.foldl (init := init) fun acc bucket =>
    match bucket with
    | some (k, v, _) => f acc k v
    | none => acc

def toList (m : RobinHoodHashMap α β) : List (α × β) :=
  m.buckets.toList.filterMap fun
    | some (k, v, _) => some (k, v)
    | none => none

def filter (m : RobinHoodHashMap α β) (f : α → β → Bool) :
    RobinHoodHashMap α β :=
  -- Rebuild from filtered entries; preserves Robin Hood invariants
  let kept := m.toList.filter fun (k, v) => f k v
  kept.foldl (init := empty m.capacity) fun acc (k, v) => acc.insert k v
```

#### Task N1-F2: Contains, Membership, isEmpty

**File**: `SeLe4n/Data/RobinHoodHashMap.lean`

```lean
@[inline] def contains (m : RobinHoodHashMap α β) (k : α) : Bool :=
  m.get? k |>.isSome

@[inline] def isEmpty (m : RobinHoodHashMap α β) : Bool :=
  m.size = 0

instance : Membership α (RobinHoodHashMap α β) where
  mem k m := m.contains k = true

instance : GetElem? (RobinHoodHashMap α β) α β (fun _ _ => True) where
  getElem? m k _ := m.get? k
```

These instances enable `k ∈ m` notation and `m[k]?` subscript syntax,
matching `Std.HashMap`'s API surface.

**Deterministic fold order**: `fold` iterates buckets in index order (0 to
capacity−1). This is deterministic for the same sequence of operations — entries
hash to the same positions and Robin Hood displacement is deterministic. The
ordering differs from `Std.HashMap` but since all fold bodies in the codebase
are order-independent (verified in §1.3), this is safe.

**`filter` rebuilds**: Rather than in-place filtering (which would violate
Robin Hood invariants), we collect matching entries and rebuild. This is O(n)
and maintains all structural invariants. For the kernel's use cases (`cspaceRevoke`,
`storeObject` ref clearing), n is typically ≤ 4096 slots.

---

#### Task N1-G: Bridge lemmas (14 HashMap + 5 HashSet equivalents)

**File**: `SeLe4n/Data/RobinHoodHashMap.lean`

The following lemmas must be proved for `RobinHoodHashMap`, matching the exact
signatures of the bridge lemmas in `Prelude.lean:676–816`. Each lemma listed
below corresponds to a `Prelude.lean` lemma that delegates to `Std.DHashMap.*`.

**HashMap bridge lemmas (14 required)**:

| # | Lemma Name | Signature Pattern | Proof Strategy |
|---|-----------|-------------------|----------------|
| 1 | `getElem?_insert` | `(m.insert k v)[a]? = if k == a then some v else m[a]?` | Case analysis on probe chain; Robin Hood displacement preserves lookup of non-displaced keys |
| 2 | `getElem?_empty` | `(∅ : RobinHoodHashMap α β)[a]? = none` | Direct: all buckets are `none` |
| 3 | `getElem?_erase` | `(m.erase k)[a]? = if k == a then none else m[a]?` | Case analysis on backward-shift; erased key not found; other keys preserved |
| 4 | `get?_insert` | Same as #1 via `get?` notation | Follows from #1 |
| 5 | `get?_empty` | Same as #2 via `get?` notation | Follows from #2 |
| 6 | `get?_erase` | Same as #3 via `get?` notation | Follows from #3 |
| 7 | `getElem?_eq_get?` | `m[k]? = m.get? k` | Definitional equality (`rfl`) |
| 8 | `get?_eq_getElem?` | `m.get? k = m[k]?` | Definitional equality (`rfl`) |
| 9 | `fold_eq_foldl_toList` | `m.fold init f = m.toList.foldl ...` | Induction on `m.buckets.toList` |
| 10 | `filter_preserves_key` | `(m.filter f)[k]? = m[k]?` when `f k' v = true` for `k' == k` | Via insert lemma on rebuilt map |
| 11 | `filter_filter_getElem?` | `((m.filter f).filter f)[k]? = (m.filter f)[k]?` | Idempotency of filter predicate |
| 12 | `size_erase_le` | `(m.erase k).size ≤ m.size` | Direct from `size - 1 ≤ size` |
| 13 | `mem_iff_isSome_getElem?` | `k ∈ m ↔ (m[k]?).isSome` | From `contains` definition |
| 14 | `getKey_beq` | `m.getKey k hMem == k` | BEq reflexivity from LawfulBEq |

**HashSet bridge lemmas (5 required)**:

| # | Lemma Name | Signature Pattern |
|---|-----------|-------------------|
| 1 | `contains_empty` | `(∅ : RobinHoodHashSet α).contains a = false` |
| 2 | `contains_insert` | `(s.insert a).contains b = (a == b \|\| s.contains b)` |
| 3 | `contains_insert_iff` | `(s.insert a).contains b = true ↔ b = a ∨ s.contains b = true` |
| 4 | `not_contains_insert` | `(s.insert a).contains b = false ↔ b ≠ a ∧ s.contains b = false` |
| 5 | `contains_erase` | `(s.erase a).contains b = (¬(a == b) && s.contains b)` |

**Proof strategy overview**: The bridge lemmas are proved via a **specification
layer** that relates the Robin Hood HashMap to a logical association list. The
key insight: rather than proving operational properties directly against the
complex Robin Hood displacement logic, we prove:

1. **Specification equivalence**: `m.get? k = m.toAssocList.lookup k` (the
   Robin Hood lookup agrees with a simple list lookup).
2. **Operation correctness on spec**: `(m.insert k v).toAssocList` contains
   `(k, v)` and preserves all other entries.
3. **Bridge lemmas as corollaries**: `getElem?_insert` follows from (1) + (2).

For the simpler lemmas (`getElem?_empty`, `size_erase_le`, `fold_eq_foldl_toList`),
direct proofs are straightforward. For `getElem?_insert` and `getElem?_erase`,
the specification-based approach avoids reasoning about Robin Hood displacement
chains directly.

**Pragmatic approach**: Where direct proof is tractable (empty, erase_le, fold),
prove directly. Where it requires displacement chain reasoning (insert, erase),
use the specification equivalence layer. All proofs must be fully machine-checked
— zero `sorry`.

---

#### Task N1-H: RobinHoodHashSet wrapper + Prelude integration

**File**: `SeLe4n/Data/RobinHoodHashMap.lean` (HashSet section)
**File**: `SeLe4n/Prelude.lean` (type aliases)

**HashSet**:
```lean
structure RobinHoodHashSet (α : Type) [BEq α] [Hashable α] where
  inner : RobinHoodHashMap α Unit
```

Thin wrapper exposing `insert`, `contains`, `erase`, `toList`, `size`.

**Prelude type aliases** (added to `Prelude.lean`):
```lean
abbrev KernelHashMap (α : Type) (β : Type) [BEq α] [Hashable α] :=
  SeLe4n.Data.RobinHoodHashMap α β

abbrev KernelHashSet (α : Type) [BEq α] [Hashable α] :=
  SeLe4n.Data.RobinHoodHashSet α
```

**Bridge lemma re-exports**: In `Prelude.lean`, add aliases for all 14+5 bridge
lemmas under the `KernelHashMap_*` / `KernelHashSet_*` namespace, delegating to
the `RobinHoodHashMap.*` proofs. The existing `HashMap_*` lemmas remain for
backward compatibility during migration.

**Verification**: `lake build` succeeds. New module compiles independently.
Existing code unchanged (no migration yet).

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
