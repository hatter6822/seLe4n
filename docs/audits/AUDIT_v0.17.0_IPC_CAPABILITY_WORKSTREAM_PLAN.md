# WS-N Workstream Plan — Robin Hood Hashing Verified Implementation (v0.17.0)

**Created**: 2026-03-17
**Baseline version**: 0.17.0
**Prior portfolios**: WS-M (v0.17.0, complete), WS-L (v0.16.13, complete)
**Constraint**: Zero `sorry`/`axiom` in production proof surface
**Scope**: Formally verified Robin Hood hash table with kernel integration

---

## 1. Motivation & Background

### 1.1 Problem Statement

The seLe4n kernel uses `Std.HashMap` across 14 production source files
(114 occurrences) and 4 test files (51 occurrences) for O(1) amortized
operations on the following kernel data structures:

| Usage Site | Type Signature | File | Occurrences |
|------------|---------------|------|-------------|
| Object store | `Std.HashMap ObjId KernelObject` | `Model/State.lean` | 19 |
| CNode slots | `Std.HashMap Slot Capability` | `Model/Object/Types.lean` | 2 |
| RunQueue buckets | `Std.HashMap Priority (List ThreadId)` | `Scheduler/RunQueue.lean` | 8 |
| RunQueue thread→priority | `Std.HashMap ThreadId Priority` | `Scheduler/RunQueue.lean` | (shared) |
| VSpace mappings | `Std.HashMap VAddr (PAddr × PagePermissions)` | `Model/Object/Structures.lean` | 16 |
| CDT child map | `Std.HashMap CdtNodeId (List CdtNodeId)` | `Model/Object/Structures.lean` | (shared) |
| CDT parent map | `Std.HashMap CdtNodeId CdtNodeId` | `Model/Object/Structures.lean` | (shared) |
| CDT slot→node | `Std.HashMap SlotRef CdtNodeId` | `Model/State.lean` | (shared) |
| CDT node→slot | `Std.HashMap CdtNodeId SlotRef` | `Model/State.lean` | (shared) |
| ASID table | `Std.HashMap ASID ObjId` | `Model/State.lean` | (shared) |
| IRQ handlers | `Std.HashMap Irq ObjId` | `Model/State.lean` | (shared) |
| Services | `Std.HashMap ServiceId ServiceGraphEntry` | `Model/State.lean` | (shared) |
| Lifecycle objectTypes | `Std.HashMap ObjId KernelObjectType` | `Model/State.lean` | (shared) |
| Lifecycle capabilityRefs | `Std.HashMap SlotRef CapTarget` | `Model/State.lean` | (shared) |
| Object index (set) | `Std.HashSet ObjId` | `Model/State.lean` | (shared) |
| RunQueue membership | `Std.HashSet ThreadId` | `Scheduler/RunQueue.lean` | (shared) |

`Std.HashMap` is a **library type whose internal implementation is not part of
seLe4n's formal proof surface**. While Lean 4.28.0's standard library provides
correctness guarantees through the `LawfulBEq`/`LawfulHashable` typeclass
hierarchy, the hash table's collision resolution strategy, resizing behavior,
bucket-level invariants, and internal array management are opaque to the
kernel's theorem prover. The kernel's proofs interact with `Std.HashMap` only
through its public API lemmas (`getElem?_insert`, `getElem?_erase`,
`getElem?_empty`, `fold_eq_foldl_toList`, `size_erase_le`,
`size_filter_le_size`, `mem_iff_isSome_getElem?`, `mem_filter`, `getKey_beq`,
`getElem_filter`, `getElem?_eq_some_getElem`, `getElem?_eq_none`).

This creates a **trust gap**: the kernel's machine-checked proofs guarantee
correctness *assuming* `Std.HashMap` behaves according to its API spec, but the
map implementation itself (Swiss-table-style hash map in Lean's Std) is not
verified within seLe4n's proof perimeter. For a production microkernel aiming
for seL4-grade assurance, every data structure on the trusted computing base
path should carry machine-checked proofs.

### 1.2 Solution: Robin Hood Hashing

Robin Hood hashing is an open-addressing scheme with linear probing that
minimizes probe-distance variance. On collision, if the incoming entry has a
greater probe distance (displacement from its ideal slot) than the resident
entry, they are swapped — "stealing from the rich (low displacement) to give to
the poor (high displacement)." This policy ensures:

- **Bounded worst-case probes**: The maximum probe distance grows as O(log n)
  with high probability, vs. O(n) for naive linear probing.
- **Cache-friendly layout**: All entries reside in a contiguous array with
  sequential access pattern — no pointer chasing, no linked-list buckets.
- **Proof-friendly invariant**: The key Robin Hood property — probe distances
  are non-decreasing within each contiguous cluster of occupied slots — is a
  local structural invariant that composes cleanly through insert, erase, and
  resize operations.
- **Deterministic behavior**: No amortization variance from bucket-chain
  rebalancing. Every operation touches a bounded contiguous memory region.

### 1.3 Prior Attempt & Lessons Learned

WS-N phases N1–N3 were previously implemented and **reverted** (PRs #453–#455).
Post-mortem analysis identifies four root causes:

**Failure 1 — `partial` functions (termination)**:
The prior `insertLoop` and `get?` used `partial def`, meaning Lean accepted
them without a termination proof. This is forbidden in the production proof
surface because `partial` functions can diverge, and any theorem proved about
a `partial` function is vacuously true if the function doesn't terminate.
The skeleton's `insertLoop` (line 37–47 of the reverted code) had:
```lean
partial def insertLoop (t : Table) (i : USize) (e : Entry) : Table := ...
```
**Fix**: All loops must use a `fuel : Nat` parameter with structural recursion
on `fuel`. The fuel is set to `capacity` (= `slots.size`), which is an upper
bound on probe distance in a non-full table.

**Failure 2 — Unsafe array access (`get!`/`set!`)**:
The prior implementation used `Array.get!` and `Array.set!` throughout:
```lean
match t.data.get! i with ...
let t' := { t with data := t.data.set! i (some e) }
```
These panic on out-of-bounds access and provide no proof obligations. Since
formal verification requires proving that every array access is in-bounds,
these must be replaced with `Array.get`/`Array.set` using explicit index
bounds proofs (`h : i < arr.size`).
**Fix**: Carry `hSlotsLen : slots.size = capacity` in the table structure.
Derive `h : idx < slots.size` from `idx < capacity` (via `idx % capacity`)
and `hSlotsLen`.

**Failure 3 — Missing refinement proofs (`admit` placeholders)**:
The prior plan defined a `repr` relation connecting the spec layer (single
array of `Option SpecEntry`) to the optimized layer (split arrays for keys,
vals, dist, used), but all refinement theorems used `admit`:
```lean
theorem insert_refines ... := by admit
```
**Fix**: This plan abandons the split-array optimization entirely. A single
`Array (Option (RHEntry α β))` serves as both spec and implementation. This
eliminates the refinement layer, removing an entire class of proof obligations.
Performance is still excellent: the `Option`-based layout has identical cache
behavior to split arrays (one cache line per slot).

**Failure 4 — Incorrect cluster-ordering invariant**:
The prior `clusterOrdered` was defined globally:
```lean
def clusterOrdered (t : Table) : Prop :=
  ∀ i j, i ≤ j → (match ... | some e₁, some e₂ => e₁.dist ≤ e₂.dist | ...)
```
This is incorrect for circular tables where clusters wrap around the array
boundary. A cluster at the end of the array wrapping to the beginning has
`slot[capacity-1]` adjacent to `slot[0]`, but `capacity-1 > 0` makes the
global `i ≤ j` ordering false even though the cluster is well-ordered.
**Fix**: Define cluster ordering per-cluster: identify maximal contiguous runs
of occupied slots (using modular arithmetic for wrap-around), and assert
non-decreasing `dist` within each such run.

### 1.4 This Plan's Design Principles

1. **Single-representation architecture**: One `Array (Option (RHEntry α β))`
   — no split arrays, no spec/impl refinement gap. The same data structure is
   both the executable implementation and the verification target.
2. **Fuel-bounded recursion**: Every loop takes `fuel : Nat` with structural
   recursion. Fuel is always `capacity`, which bounds the maximum number of
   probes. No `partial` functions.
3. **Bounds-checked array access**: All `Array.get`/`Array.set` calls carry
   explicit `h : idx < arr.size` proofs derived from `idx % capacity < capacity`
   and `hSlotsLen : slots.size = capacity`.
4. **Modular-arithmetic index advancement**: `nextIdx i cap := (i + 1) % cap`.
   Wrap-around is inherent in the arithmetic — no special-case logic.
5. **Incremental integration**: Phase N4 replaces ONE `Std.HashMap` site
   (`CNode.slots`) as a proof of concept. Remaining 13 sites are planned for
   a subsequent workstream, reducing blast radius.
6. **Zero sorry/axiom**: Every theorem shipped in each phase is fully
   machine-checked. `sorry` may appear during active development but must be
   resolved before the phase version is tagged.


---

## 2. Architecture

### 2.1 Module Structure

```
SeLe4n/Kernel/RobinHood/
  Core.lean              — Data types, hash function, bounded operations
  Invariant.lean         — Well-formedness predicates, preservation proofs
SeLe4n/Kernel/RobinHood.lean  — Re-export hub (thin import file)
```

This follows the project's established Invariant/Operations split pattern
(see CLAUDE.md: "each kernel subsystem has `Operations.lean` and
`Invariant.lean`"). The `Core.lean` file serves as the operations module;
`Invariant.lean` holds all proof-only content.

### 2.2 Data Types (Expanded Pseudocode)

```lean
/-- A single entry in the Robin Hood hash table. -/
structure RHEntry (α β : Type) where
  key   : α
  value : β
  dist  : Nat   -- probe distance from ideal position (hash(key) % capacity)
  deriving Repr

/-- Robin Hood open-addressing hash table.

The `slots` array has exactly `capacity` elements. Each element is either
`none` (empty slot) or `some entry` (occupied). The `size` field caches
the count of occupied slots.

Proof fields `hCapPos` and `hSlotsLen` are erased at runtime (Prop-typed)
but enable bounds-checked array access in all operations.

The `capacity` is always a power of 2, enabling efficient modular index
computation via `i % capacity` (which the compiler can lower to bitwise
AND when capacity is a known power of 2). -/
structure RHTable (α β : Type) [BEq α] [Hashable α] where
  slots    : Array (Option (RHEntry α β))
  size     : Nat
  capacity : Nat
  hCapPos  : 0 < capacity               -- capacity is positive
  hSlotsLen : slots.size = capacity      -- array length matches capacity
  deriving Repr
```

### 2.3 Hash Function

```lean
/-- Compute the ideal slot index for a key.
Uses Lean's built-in `Hashable` instance (which delegates to the
type's `hash` function) and reduces modulo capacity.

The `hCapPos : 0 < capacity` proof ensures `% capacity` is well-defined
(Lean's `Nat.mod` returns 0 for `% 0`, which would be unsound). -/
@[inline] def idealIndex [Hashable α] (k : α) (capacity : Nat)
    (_hCapPos : 0 < capacity) : Nat :=
  (hash k).toNat % capacity
```

### 2.4 Index Advancement

```lean
/-- Advance to the next slot with wrap-around.
`(i + 1) % capacity` handles the boundary: when `i = capacity - 1`,
the next index wraps to 0. -/
@[inline] def nextIndex (i : Nat) (capacity : Nat) : Nat :=
  (i + 1) % capacity

/-- Key lemma: `nextIndex i cap < cap` when `0 < cap`. -/
theorem nextIndex_lt (i : Nat) (cap : Nat) (hPos : 0 < cap) :
    nextIndex i cap < cap :=
  Nat.mod_lt _ hPos

/-- Key lemma: `idealIndex k cap hPos < cap`. -/
theorem idealIndex_lt [Hashable α] (k : α) (cap : Nat) (hPos : 0 < cap) :
    idealIndex k cap hPos < cap :=
  Nat.mod_lt _ hPos
```

### 2.5 Core Operations (Expanded Pseudocode)

#### Empty Table

```lean
/-- Create an empty table with the given capacity (must be positive).
All slots initialized to `none`. -/
def RHTable.empty (cap : Nat) (hPos : 0 < cap := by omega) : RHTable α β :=
  { slots    := Array.mkArray cap none
    size     := 0
    capacity := cap
    hCapPos  := hPos
    hSlotsLen := Array.size_mkArray cap none }
```

#### Bounded Insertion Loop

```lean
/-- Core insertion loop with fuel-bounded recursion.

Parameters:
- `fuel`: structural recursion bound (initialized to `capacity`)
- `idx`: current probe position
- `k, v`: key-value pair to insert
- `d`: current probe distance of the entry being placed
- `slots`: mutable array (threaded through)
- `hLen`: proof that `slots.size = capacity`

Behavior:
- If `slots[idx] = none`: place the entry, return updated slots and `true`
  (size incremented by caller).
- If `slots[idx] = some e` and `e.key == k`: update value in-place (key
  already exists), return updated slots and `false` (size unchanged).
- If `slots[idx] = some e` and `e.dist < d`: Robin Hood swap — place
  current entry at `idx`, continue inserting displaced entry `e` with
  `e.dist + 1`.
- If `slots[idx] = some e` and `e.dist ≥ d`: continue probing at
  `nextIndex idx capacity` with `d + 1`.
- If `fuel = 0`: return original slots unchanged and `false` (table full).

The fuel bound of `capacity` suffices because: in a table with at least one
empty slot, the probe sequence must encounter an empty slot within
`capacity` steps (pigeonhole). The resize trigger at 75% load ensures
at least 25% of slots are empty. -/
def insertLoop [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (v : β) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity)
    : Array (Option (RHEntry α β)) × Bool :=
  match fuel with
  | 0 => (slots, false)
  | fuel' + 1 =>
    let hIdx : idx % capacity < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    let i := idx % capacity
    match slots.get ⟨i, hIdx⟩ with
    | none =>
      let slots' := slots.set ⟨i, hIdx⟩ (some { key := k, value := v, dist := d })
      (slots', true)
    | some e =>
      if e.key == k then
        -- Update existing entry (key match)
        let slots' := slots.set ⟨i, hIdx⟩ (some { key := k, value := v, dist := e.dist })
        (slots', false)
      else if e.dist < d then
        -- Robin Hood swap: displace the "richer" entry
        let slots' := slots.set ⟨i, hIdx⟩ (some { key := k, value := v, dist := d })
        insertLoop fuel' (idx + 1) e.key e.value (e.dist + 1)
          slots' capacity (by rw [Array.size_set]; exact hLen) hCapPos
      else
        -- Continue probing
        insertLoop fuel' (idx + 1) k v (d + 1) slots capacity hLen hCapPos
```

#### Top-Level Insert (with Resize)

```lean
/-- Insert a key-value pair. Triggers resize at 75% load factor.
Returns the updated table. -/
def RHTable.insert (t : RHTable α β) (k : α) (v : β) : RHTable α β :=
  -- Resize if load factor ≥ 75%
  let t' := if t.size * 4 ≥ t.capacity * 3 then t.resize else t
  let start := idealIndex k t'.capacity t'.hCapPos
  let (slots', isNew) := insertLoop t'.capacity start k v 0
    t'.slots t'.capacity t'.hSlotsLen t'.hCapPos
  { t' with
    slots := slots'
    size := if isNew then t'.size + 1 else t'.size
    hSlotsLen := by rw [← t'.hSlotsLen]; exact insertLoop_preserves_size ... }
```

#### Bounded Lookup Loop

```lean
/-- Core lookup loop with fuel-bounded recursion.

Early termination conditions (Robin Hood property):
1. `slots[idx] = none` → key not in table (gap in cluster means key
   would have been placed here or earlier).
2. `slots[idx] = some e` and `e.dist < d` → key not in table (the
   Robin Hood invariant guarantees that if our key were present, its
   probe distance would be ≤ the distance at this slot position).
3. `slots[idx] = some e` and `e.key == k` → found.

Fuel bound: `capacity` steps suffice because condition 1 or 2 must
trigger within one full table scan. -/
def getLoop [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity)
    : Option β :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let hIdx : idx % capacity < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    let i := idx % capacity
    match slots.get ⟨i, hIdx⟩ with
    | none => none
    | some e =>
      if e.key == k then some e.value
      else if e.dist < d then none   -- Robin Hood early termination
      else getLoop fuel' (idx + 1) k (d + 1) slots capacity hLen hCapPos

/-- Look up a key. Returns `some value` if found, `none` otherwise. -/
def RHTable.get? (t : RHTable α β) (k : α) : Option β :=
  let start := idealIndex k t.capacity t.hCapPos
  getLoop t.capacity start k 0 t.slots t.capacity t.hSlotsLen t.hCapPos
```

#### Bounded Erasure (Backward Shift)

```lean
/-- Erase phase 1: find the target slot.
Returns `some idx` if found at slot `idx`, `none` if absent. -/
def findLoop [BEq α] [Hashable α]
    (fuel : Nat) (idx : Nat) (k : α) (d : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity)
    : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let hIdx : idx % capacity < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    let i := idx % capacity
    match slots.get ⟨i, hIdx⟩ with
    | none => none
    | some e =>
      if e.key == k then some i
      else if e.dist < d then none
      else findLoop fuel' (idx + 1) k (d + 1) slots capacity hLen hCapPos

/-- Erase phase 2: backward-shift loop.
After clearing slot `idx`, shift subsequent entries backward to fill the
gap, decrementing their `dist` by 1 each. Stop when hitting an empty
slot or an entry with `dist = 0` (at its ideal position, cannot shift). -/
def backshiftLoop
    (fuel : Nat) (idx : Nat)
    (slots : Array (Option (RHEntry α β)))
    (capacity : Nat) (hLen : slots.size = capacity)
    (hCapPos : 0 < capacity)
    : Array (Option (RHEntry α β)) :=
  match fuel with
  | 0 => slots
  | fuel' + 1 =>
    let nextIdx := (idx + 1) % capacity
    let hNext : nextIdx < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
    match slots.get ⟨nextIdx, hNext⟩ with
    | none => slots   -- gap found; done
    | some e =>
      if e.dist = 0 then slots  -- entry at ideal position; cannot shift
      else
        let hIdx : idx % capacity < slots.size := hLen ▸ Nat.mod_lt _ hCapPos
        let shifted := { e with dist := e.dist - 1 }
        let slots' := (slots.set ⟨idx % capacity, hIdx⟩ (some shifted)).set
          ⟨nextIdx, by rw [Array.size_set]; exact hNext⟩ none
        backshiftLoop fuel' nextIdx slots' capacity
          (by rw [Array.size_set, Array.size_set]; exact hLen) hCapPos

/-- Erase a key from the table. No-op if key is absent. -/
def RHTable.erase (t : RHTable α β) (k : α) : RHTable α β :=
  let start := idealIndex k t.capacity t.hCapPos
  match findLoop t.capacity start k 0 t.slots t.capacity t.hSlotsLen t.hCapPos with
  | none => t
  | some idx =>
    let hIdx : idx < t.slots.size := ... -- derived from findLoop postcondition
    let slots' := t.slots.set ⟨idx, hIdx⟩ none
    let slots'' := backshiftLoop t.capacity idx slots' t.capacity
      (by rw [Array.size_set]; exact t.hSlotsLen) t.hCapPos
    { t with
      slots := slots''
      size := t.size - 1
      hSlotsLen := ... }
```

#### Fold and Utilities

```lean
/-- Fold over all occupied entries in index order. O(capacity). -/
def RHTable.fold (t : RHTable α β) (init : γ) (f : γ → α → β → γ) : γ :=
  t.slots.foldl (fun acc slot =>
    match slot with
    | none => acc
    | some e => f acc e.key e.value) init

/-- Collect all key-value pairs as a list. -/
def RHTable.toList (t : RHTable α β) : List (α × β) :=
  t.fold [] (fun acc k v => (k, v) :: acc)

/-- Check membership. -/
def RHTable.contains (t : RHTable α β) (k : α) : Bool :=
  (t.get? k).isSome

/-- Number of entries. -/
def RHTable.size' (t : RHTable α β) : Nat := t.size

/-- Resize: double capacity and re-insert all entries. -/
def RHTable.resize (t : RHTable α β) : RHTable α β :=
  let newCap := t.capacity * 2
  let empty := RHTable.empty newCap (by omega)
  t.fold empty (fun acc k v => acc.insert k v)

/-- Bracket notation: `t[k]?` -/
instance [BEq α] [Hashable α] : GetElem? (RHTable α β) α β (fun _ _ => True) where
  getElem? t k _ := t.get? k

/-- Membership: `k ∈ t` -/
instance [BEq α] [Hashable α] : Membership α (RHTable α β) where
  mem t k := t.contains k = true
```


---

## 3. Invariant Definitions (Expanded)

### 3.1 Well-Formedness (`wf`)

```lean
/-- Table well-formedness — structural consistency between fields.

(1) Array length matches declared capacity.
(2) Capacity is positive (required for modular arithmetic).
(3) `size` field accurately reflects the count of occupied slots.
(4) Size does not exceed capacity (no overflow). -/
def RHTable.wf (t : RHTable α β) : Prop :=
  t.slots.size = t.capacity ∧
  0 < t.capacity ∧
  t.size = t.slots.foldl (fun acc s => acc + if s.isSome then 1 else 0) 0 ∧
  t.size ≤ t.capacity
```

### 3.2 Probe Distance Correctness (`distCorrect`)

```lean
/-- Every occupied slot's `dist` field accurately reflects its displacement
from the ideal position.

For slot `i` containing entry `e`:
  e.dist = (i - idealIndex e.key capacity hCapPos + capacity) % capacity

The `+ capacity` before `% capacity` handles wrap-around: if the ideal
index is 14 and the actual index is 2 in a capacity-16 table, the
displacement is `(2 - 14 + 16) % 16 = 4`. -/
def RHTable.distCorrect [Hashable α] (t : RHTable α β) : Prop :=
  ∀ (i : Nat) (hi : i < t.capacity) (e : RHEntry α β),
    t.slots.get ⟨i, t.hSlotsLen ▸ hi⟩ = some e →
    e.dist = (i - idealIndex e.key t.capacity t.hCapPos + t.capacity) % t.capacity
```

### 3.3 No Duplicate Keys (`noDupKeys`)

```lean
/-- No two occupied slots contain entries with BEq-equal keys.

This is the hash-map uniqueness property. Combined with `distCorrect`,
it ensures that `get?` returns a unique value for each key. -/
def RHTable.noDupKeys [BEq α] (t : RHTable α β) : Prop :=
  ∀ (i j : Nat) (hi : i < t.capacity) (hj : j < t.capacity)
    (ei ej : RHEntry α β),
    t.slots.get ⟨i, t.hSlotsLen ▸ hi⟩ = some ei →
    t.slots.get ⟨j, t.hSlotsLen ▸ hj⟩ = some ej →
    (ei.key == ej.key) = true →
    i = j
```

### 3.4 Robin Hood Property (`robinHoodOrdered`)

```lean
/-- Within each contiguous cluster of occupied slots, probe distances are
non-decreasing.

A "cluster" is a maximal contiguous run of occupied slots (with
wrap-around). Two adjacent occupied slots `i` and `(i+1) % capacity`
within the same cluster satisfy `dist[i] ≤ dist[(i+1) % capacity]`.

More precisely: for any occupied slot `i` whose successor
`(i+1) % capacity` is also occupied, the successor's distance is
at least the current slot's distance. The successor's distance being
exactly 0 means it starts a new cluster (it's at its ideal position),
which is consistent since a new cluster trivially satisfies the ordering.

This invariant enables early termination in `getLoop`: if we're
searching for key `k` with current search distance `d`, and we encounter
slot with `e.dist < d`, then `k` is not in the table (it would have
been placed at or before this slot during insertion). -/
def RHTable.robinHoodOrdered (t : RHTable α β) : Prop :=
  ∀ (i : Nat) (hi : i < t.capacity)
    (ei : RHEntry α β) (ej : RHEntry α β),
    let j := (i + 1) % t.capacity
    let hj : j < t.capacity := Nat.mod_lt _ t.hCapPos
    t.slots.get ⟨i, t.hSlotsLen ▸ hi⟩ = some ei →
    t.slots.get ⟨j, t.hSlotsLen ▸ hj⟩ = some ej →
    ej.dist = 0 ∨ ei.dist ≤ ej.dist
```

### 3.5 Combined Invariant Bundle

```lean
/-- Full Robin Hood table invariant — conjunction of all four properties.
Every operation must preserve this bundle. -/
def RHTable.invariant [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
  t.wf ∧ t.distCorrect ∧ t.noDupKeys ∧ t.robinHoodOrdered
```

### 3.6 Functional Correctness (`lookupCorrect`)

```lean
/-- Lookup correctness: `get?` returns `some v` iff there exists a slot
containing an entry with matching key and that value.

This is the primary functional specification. It connects the operational
definition of `get?` (loop-based search) to the declarative specification
(existence of a matching entry in the array). -/
def RHTable.lookupCorrect [BEq α] [Hashable α] [LawfulBEq α] (t : RHTable α β) : Prop :=
  ∀ (k : α) (v : β),
    t.get? k = some v ↔
    ∃ (i : Nat) (hi : i < t.capacity) (e : RHEntry α β),
      t.slots.get ⟨i, t.hSlotsLen ▸ hi⟩ = some e ∧
      (e.key == k) = true ∧ e.value = v
```

---

## 4. Phase Overview

| Phase | Focus | Priority | Target | Est. LoC | Deliverables |
|-------|-------|----------|--------|----------|--------------|
| **N1** | Core types + operations | CRITICAL | v0.17.1 | ~350 | `RHEntry`, `RHTable`, `empty`, `insertLoop`, `getLoop`, `findLoop`, `backshiftLoop`, `insert`, `get?`, `erase`, `fold`, `contains`, `resize`; `empty_wf` |
| **N2** | Invariant proofs | HIGH | v0.17.2 | ~500 | `wf` preservation (insert/erase/resize), `distCorrect` preservation, `noDupKeys` preservation, `robinHoodOrdered` preservation, lookup soundness + completeness |
| **N3** | Kernel API bridge | MEDIUM | v0.17.3 | ~200 | `GetElem?`/`Membership` instances, bridge lemmas matching all 12 `Std.HashMap` proof patterns used by kernel (see §6.3), `filter` support, `Inhabited` |
| **N4** | Kernel integration | MEDIUM | v0.17.4 | ~400 (net changes) | Replace `CNode.slots` HashMap; update 5 CNode operations, ~15 CNode theorems, ~20 invariant preservation proofs, test fixtures |
| **N5** | Tests + documentation | LOW | v0.17.5 | ~300 (tests) | 12+ Robin Hood test scenarios, 6+ integration tests, full documentation sync across 8 canonical files + 4 GitBook chapters |

**Total estimated new LoC**: ~1,750
**Total estimated net changes**: ~2,200 (including ~450 lines of modified existing code)

---

## 5. Detailed Phase Plans

### Phase N1: Core Types + Operations

**Target version**: 0.17.1
**Files created**: `SeLe4n/Kernel/RobinHood/Core.lean`, `SeLe4n/Kernel/RobinHood.lean`
**Files modified**: `lakefile.toml` (version bump)
**Constraint**: Zero `sorry`/`axiom`

#### Task N1-A: Core data types (4 subtasks)

| ID | Description | Acceptance |
|----|-------------|------------|
| N1-A1 | Define `RHEntry α β` with `key`, `value`, `dist` fields; derive `Repr` | `#check @RHEntry.mk` compiles |
| N1-A2 | Define `RHTable α β` with `slots`, `size`, `capacity`, `hCapPos`, `hSlotsLen`; derive `Repr` | `#check @RHTable.mk` compiles |
| N1-A3 | Define `idealIndex` and `nextIndex` with `@[inline]` | `#eval idealIndex (hash 42).toNat 16 (by omega)` returns a `Nat < 16` |
| N1-A4 | Prove `idealIndex_lt` and `nextIndex_lt` | Both compile with zero `sorry` |

**Proof strategy for N1-A4**: Both are direct applications of `Nat.mod_lt _ hCapPos`.

#### Task N1-B: Empty table constructor (2 subtasks)

| ID | Description | Acceptance |
|----|-------------|------------|
| N1-B1 | Define `RHTable.empty` using `Array.mkArray cap none` | `#eval (RHTable.empty 16).size` returns `0` |
| N1-B2 | Prove `empty_wf` (all 4 `wf` conjuncts) | Compiles with zero `sorry` |

**Proof strategy for N1-B2**:
- `slots.size = capacity`: `Array.size_mkArray`
- `0 < capacity`: hypothesis `hPos`
- `size = count`: `Array.foldl` over all-`none` array yields 0 = 0 by `simp`
- `size ≤ capacity`: `Nat.zero_le`

#### Task N1-C: Bounded insertion loop (5 subtasks)

| ID | Description | Acceptance |
|----|-------------|------------|
| N1-C1 | Define `insertLoop` with `fuel` parameter and structural recursion on `fuel` | Lean accepts termination without `partial` |
| N1-C2 | Handle empty-slot case: place entry, return `(slots', true)` | Unit test: insert into empty table at ideal slot |
| N1-C3 | Handle key-match case: update value, return `(slots', false)` | Unit test: insert same key twice updates value |
| N1-C4 | Handle Robin Hood swap case: `e.dist < d` → swap and continue | Unit test: insert triggers swap when displacement exceeds resident |
| N1-C5 | Handle continue-probing case: `e.dist ≥ d` → advance index | Unit test: insert probes past occupied slot |

**Proof obligation**: `insertLoop` preserves `slots.size = capacity`.
**Proof strategy**: Each branch either returns `slots` unchanged or uses
`Array.set` which preserves `Array.size` (`Array.size_set`). Thread this
through by induction on `fuel`.

#### Task N1-D: Top-level insert with resize (3 subtasks)

| ID | Description | Acceptance |
|----|-------------|------------|
| N1-D1 | Define `RHTable.insert` composing resize check + `insertLoop` | `#eval` roundtrip: insert then get returns value |
| N1-D2 | Prove `insertLoop_preserves_len : (insertLoop ...).1.size = slots.size` | Compiles with zero `sorry` |
| N1-D3 | Prove `insert_size_le : (t.insert k v).size ≤ t.size + 1` | Compiles with zero `sorry` |

#### Task N1-E: Bounded lookup loop (3 subtasks)

| ID | Description | Acceptance |
|----|-------------|------------|
| N1-E1 | Define `getLoop` with fuel-bounded recursion | Lean accepts termination |
| N1-E2 | Define `RHTable.get?` delegating to `getLoop` | `#eval` returns correct values |
| N1-E3 | Define `RHTable.contains` as `(t.get? k).isSome` | `#eval` boolean check works |

#### Task N1-F: Bounded erasure (4 subtasks)

| ID | Description | Acceptance |
|----|-------------|------------|
| N1-F1 | Define `findLoop` (locate target slot) | Returns `some idx` for present keys, `none` for absent |
| N1-F2 | Define `backshiftLoop` (fill gap after removal) | Shifts entries backward, decrements `dist` |
| N1-F3 | Compose `RHTable.erase` from `findLoop` + `backshiftLoop` | `#eval`: erase then get returns `none` |
| N1-F4 | Prove `backshiftLoop_preserves_len` | Array size unchanged through backward shift |

#### Task N1-G: Fold, resize, and utility operations (4 subtasks)

| ID | Description | Acceptance |
|----|-------------|------------|
| N1-G1 | Define `RHTable.fold` iterating over `slots` | Correct fold over occupied entries |
| N1-G2 | Define `RHTable.toList` via fold | List contains all inserted entries |
| N1-G3 | Define `RHTable.resize` (double capacity, re-insert all) | Resized table has correct size and all entries accessible |
| N1-G4 | Prove `resize_preserves_len : (t.resize).slots.size = t.capacity * 2` | Direct from `empty` + iterated `insert` length preservation |

#### Task N1-H: Re-export hub (1 subtask)

| ID | Description | Acceptance |
|----|-------------|------------|
| N1-H1 | Create `SeLe4n/Kernel/RobinHood.lean` with `import SeLe4n.Kernel.RobinHood.Core` | `import SeLe4n.Kernel.RobinHood` resolves |

**N1 totals**: 26 subtasks, ~350 new LoC, ~8 proved declarations.

---

### Phase N2: Invariant Proofs

**Target version**: 0.17.2
**Files created**: `SeLe4n/Kernel/RobinHood/Invariant.lean`
**Files modified**: `SeLe4n/Kernel/RobinHood.lean` (add import)
**Constraint**: Zero `sorry`/`axiom`

#### Task N2-A: Well-formedness preservation (6 subtasks)

| ID | Description | Proof Strategy |
|----|-------------|---------------|
| N2-A1 | `empty_wf` (from N1-B2, may refine) | Direct: `mkArray` has correct size, zero count |
| N2-A2 | `insertLoop_preserves_wf_conjuncts` | Induction on `fuel`; case split on slot state; `Array.size_set` for (1); count analysis for (3)-(4) |
| N2-A3 | `insert_preserves_wf` | Compose `insertLoop_preserves_wf_conjuncts` with resize `wf` |
| N2-A4 | `erase_preserves_wf` | `findLoop` returns valid index; `backshiftLoop` preserves size; count decrements by 1 |
| N2-A5 | `resize_preserves_wf` | Induction: `empty` is `wf`; each `insert` in `fold` preserves `wf` |
| N2-A6 | `backshiftLoop_preserves_wf` | Induction on fuel; each step preserves array size and entry count |

**Key proof technique**: All `wf` conjuncts are decidable (computable `Nat`
comparisons and array folds), enabling `decide`/`native_decide` as fallback
for base cases.

#### Task N2-B: Probe distance correctness preservation (4 subtasks)

| ID | Description | Proof Strategy |
|----|-------------|---------------|
| N2-B1 | `empty_distCorrect` | Vacuously true: no occupied slots in `mkArray cap none` |
| N2-B2 | `insertLoop_preserves_distCorrect` | Induction on fuel. Placed entry: `dist = 0` at ideal index (base), `dist = d` at probe step `d`. Swapped entry: displaced entry's dist is incremented by 1, matching its new displacement. Unchanged slots: untouched by `Array.set` at a different index. |
| N2-B3 | `erase_preserves_distCorrect` | `backshiftLoop` decrements `dist` by 1 for each entry shifted one slot backward. New displacement is `(i-1 - ideal + cap) % cap = old_displacement - 1`. |
| N2-B4 | `resize_preserves_distCorrect` | After resize, all entries re-inserted from scratch via `insert`, which establishes `distCorrect` for each entry by N2-B2. |

**Key proof technique for N2-B2**: The Robin Hood swap sets
`slots[i] := { key := k, value := v, dist := d }` where `d` is the number
of probe steps from the ideal index to `i`. By construction,
`d = (i - idealIndex k cap hPos + cap) % cap` (invariant maintained by
incrementing `d` at each `nextIndex` step and starting at `d = 0`).

#### Task N2-C: No-duplicate-keys preservation (4 subtasks)

| ID | Description | Proof Strategy |
|----|-------------|---------------|
| N2-C1 | `empty_noDupKeys` | Vacuously true: no occupied slots |
| N2-C2 | `insertLoop_preserves_noDupKeys` | Case 1 (empty slot): new entry's key is fresh (if it matched an existing entry, the key-match branch would have fired earlier in the probe). Case 2 (key match): overwrites same slot, no new key introduced. Case 3 (swap): displaced entry retains its original key; placed entry's key is the one being inserted, which didn't match any slot visited so far (otherwise key-match would have triggered). |
| N2-C3 | `erase_preserves_noDupKeys` | Removing an entry and backward-shifting never introduces new keys. Shifted entries retain their original keys. |
| N2-C4 | `resize_preserves_noDupKeys` | Re-insertion of unique keys produces unique keys (by N2-C2 and induction over `fold`). |

**Key proof technique for N2-C2**: The key insight is that `insertLoop` visits
every slot between the ideal index and the placement index in order. If any
visited slot contained a BEq-matching key, the `if e.key == k` branch would
have executed (returning updated entry, not continuing the probe). Therefore,
the placed entry has a key distinct from all other occupied slots.

#### Task N2-D: Robin Hood ordering preservation (5 subtasks)

| ID | Description | Proof Strategy |
|----|-------------|---------------|
| N2-D1 | `empty_robinHoodOrdered` | Vacuously true: no adjacent occupied pairs |
| N2-D2 | `swap_preserves_local_order` | At swap point `i`: old `e.dist < d`, so new `dist[i] = d > e.dist`. The displaced entry continues with `e.dist + 1`, maintaining the non-decreasing chain. The slot before `i` had `dist ≤ e.dist < d = dist[i]`, so the ordering holds backward. The slot after `i` either: (a) is the destination of the displaced entry, which has `e.dist + 1 ≥ d` only if... we must analyze more carefully (see below). |
| N2-D3 | `insert_preserves_robinHoodOrdered` | Full induction on `insertLoop`. The key lemma is that at each step, the entry being carried has distance ≥ all entries at positions visited so far. The swap maintains this: after swapping at position `i`, the displaced entry has distance `e.dist + 1`, and we know `e.dist ≥ dist[i-1]` (by pre-swap ordering), so `e.dist + 1 ≥ dist[i-1] + 1`. |
| N2-D4 | `backshift_preserves_robinHoodOrdered` | Each backward shift moves an entry from position `j` to `j-1` (mod cap) and decrements its dist by 1. If pre-shift ordering holds at `j-1, j, j+1`, then post-shift at `j-1` the new entry has `dist[j]-1`. Since `dist[j-1] ≤ dist[j]` (pre-ordering), `dist[j]-1 ≥ dist[j-1]-1`. Need to verify this is ≥ the entry now at `j-2`. |
| N2-D5 | `erase_preserves_robinHoodOrdered` | Compose `backshift_preserves_robinHoodOrdered` for each backward-shift step. |

**Key proof technique for N2-D3**: This is the most complex proof in the
workstream. The approach is induction on `fuel` with the loop invariant:
"After placing entry `e` at position `i`, the cluster from
`idealIndex(original_key)` through `i` has non-decreasing distances."
The base case (empty slot) is trivial. The swap case requires showing that
the new entry at `i` has higher distance than the entry at `i-1` (from
pre-swap ordering) and the displaced entry starts with distance that maintains
ordering with respect to position `i+1`.

**Estimated difficulty**: HIGH. This is the critical proof that prior attempts
failed to complete. The plan allocates 40% of N2's effort budget to N2-D.

#### Task N2-E: Lookup correctness (3 subtasks)

| ID | Description | Proof Strategy |
|----|-------------|---------------|
| N2-E1 | `get_after_insert_eq : (t.insert k v).get? k = some v` | After `insert`, the entry with key `k` is in the table at some slot. `getLoop` will find it because: (a) it starts from the ideal index, (b) it follows the same probe sequence, (c) `noDupKeys` ensures it's the only entry with key `k`. |
| N2-E2 | `get_after_insert_ne : k ≠ k' → (t.insert k v).get? k' = t.get? k'` | Inserting `k` only modifies slots in the probe sequence of `k`. For any other key `k'`, either its probe sequence doesn't overlap, or it does but `getLoop` skips entries with non-matching keys. The Robin Hood swap may move `k'`'s entry, but only forward (higher index), and `getLoop` will still find it. |
| N2-E3 | `get_after_erase_eq : (t.erase k).get? k = none` | After erasure, `findLoop` returns `none` for `k` because: (a) the slot where `k` was is now either empty or contains a backward-shifted entry with a different key, (b) the backward shift preserves the Robin Hood property, so early termination correctly concludes `k` is absent. |

**Key proof technique for N2-E1**: Follows from `distCorrect`, `noDupKeys`,
and `robinHoodOrdered` combined. `getLoop` starting at `idealIndex k` walks
forward incrementing search distance `d`. At each step, if `slots[i].dist < d`,
it terminates with `none`. But if the entry is present, `distCorrect` ensures
`entry.dist = displacement`, and `robinHoodOrdered` ensures no entry with
lower distance appears after the entry in the probe sequence. So `getLoop`
must encounter the entry before any `dist < d` termination.

**N2 totals**: 22 subtasks, ~500 new LoC, ~22 proved declarations.

---

### Phase N3: Kernel API Bridge

**Target version**: 0.17.3
**Files modified**: `SeLe4n/Kernel/RobinHood/Core.lean` (add instances + bridge lemmas)
**Constraint**: Zero `sorry`/`axiom`

The kernel's proof surface depends on exactly 12 `Std.HashMap` lemma patterns
(identified by grep across `SeLe4n/Prelude.lean` and all downstream theorem
files). Phase N3 provides equivalent lemmas for `RHTable`.

#### Task N3-A: Typeclass instances (5 subtasks)

| ID | Description | Notes |
|----|-------------|-------|
| N3-A1 | `GetElem?` instance: `t[k]?` syntax | Delegates to `RHTable.get?` |
| N3-A2 | `Membership` instance: `k ∈ t` syntax | `contains k = true` |
| N3-A3 | `Inhabited` instance | `default := RHTable.empty 16` |
| N3-A4 | `BEq` instance (entry-wise) | Fold-based comparison matching `VSpaceRoot`/`CNode` BEq pattern |
| N3-A5 | `Hashable` instance (if needed for nested HashMap) | Fold-based hash combining |

#### Task N3-B: Core bridge lemmas (12 subtasks)

Each lemma mirrors the corresponding `Std.HashMap` lemma used in `Prelude.lean`
bridge infrastructure and downstream kernel proofs.

| ID | Lemma | Mirrors | Used By (files) |
|----|-------|---------|-----------------|
| N3-B1 | `RHTable.getElem?_insert_self` | `HashMap_getElem?_insert` (self case) | 15 files |
| N3-B2 | `RHTable.getElem?_insert_ne` | `HashMap_getElem?_insert` (ne case) | 15 files |
| N3-B3 | `RHTable.getElem?_erase_self` | `HashMap_getElem?_erase` (self case) | `Structures.lean`, `Invariant/Defs.lean` |
| N3-B4 | `RHTable.getElem?_erase_ne` | `HashMap_getElem?_erase` (ne case) | `Structures.lean`, `Invariant/Defs.lean` |
| N3-B5 | `RHTable.getElem?_empty` | `HashMap_getElem?_empty` | `RunQueue.lean`, `State.lean` |
| N3-B6 | `RHTable.size_erase_le` | `Std.HashMap.size_erase_le` | `Structures.lean:537` |
| N3-B7 | `RHTable.size_insert_le` | (new, needed for slot-count bounds) | `Structures.lean` |
| N3-B8 | `RHTable.mem_iff_isSome_getElem?` | `Std.HashMap.mem_iff_isSome_getElem?` | `Structures.lean:454`, `Authority.lean:103` |
| N3-B9 | `RHTable.getElem?_eq_some_getElem` | `Std.HashMap.getElem?_eq_some_getElem` | `Structures.lean:556`, `Authority.lean:110`, `Defs.lean:613` |
| N3-B10 | `RHTable.fold_eq_foldl_toList` | `Std.HashMap.fold_eq_foldl_toList` | `State.lean` (6 occurrences) |
| N3-B11 | `RHTable.filter_preserves_key` | `HashMap_filter_preserves_key` | `Structures.lean:474` |
| N3-B12 | `RHTable.size_filter_le_size` | `Std.HashMap.size_filter_le_size` | `Structures.lean:546` |

**Proof strategy**: Each bridge lemma follows directly from the N2 correctness
proofs. For example:
- `getElem?_insert_self` is `get_after_insert_eq` repackaged with `GetElem?` syntax.
- `getElem?_insert_ne` is `get_after_insert_ne` with negated BEq hypothesis.
- `size_erase_le` follows from `erase_preserves_wf` (size decrements by at most 1).

#### Task N3-C: Filter support (3 subtasks)

The kernel uses `Std.HashMap.filter` in `CNode.revokeTargetLocal`. RHTable
needs an equivalent:

| ID | Description |
|----|-------------|
| N3-C1 | Define `RHTable.filter (f : α → β → Bool) : RHTable α β` — iterate slots, keep matching entries, rebuild via `fold` + `insert` |
| N3-C2 | Prove `filter_preserves_invariant` |
| N3-C3 | Prove `filter_getElem?` — lookup correctness after filter |

**N3 totals**: 20 subtasks, ~200 new LoC, ~15 proved declarations.


---

### Phase N4: Kernel Integration (First Site — CNode.slots)

**Target version**: 0.17.4
**Files modified**: Listed below with per-file change specifications.
**Constraint**: Zero `sorry`/`axiom`. All existing tests pass unchanged.

#### 4.1 Why CNode.slots First

`CNode.slots : Std.HashMap Slot Capability` is the ideal first integration
site because:

1. **Self-contained scope**: CNode operations (`lookup`, `insert`, `remove`,
   `revokeTargetLocal`, `findFirstEmptySlot`) are defined in a single file
   (`Model/Object/Structures.lean`) with clear boundaries.
2. **Moderate proof surface**: ~15 CNode theorems in `Structures.lean` plus
   ~20 references in `Capability/Invariant/*.lean`. Large enough to validate
   the bridge layer, small enough to complete in one phase.
3. **No cross-subsystem dependencies**: CNode operations don't directly use
   other HashMap sites (object store, scheduler, etc.), so the change is
   isolated.
4. **Test coverage**: CNode operations are exercised by all test suites
   (NegativeStateSuite, OperationChainSuite, MainTraceHarness), providing
   strong regression detection.

#### 4.2 Per-File Change Specification

**File: `SeLe4n/Model/Object/Types.lean`** (2 changes)

| Line(s) | Current | New | Rationale |
|----------|---------|-----|-----------|
| 339–344 | `structure CNode where ... slots : Std.HashMap Slot Capability` | `slots : RHTable Slot Capability` | Core type change |
| (import) | `import SeLe4n.Machine` | Add `import SeLe4n.Kernel.RobinHood` | Make RHTable available |

**File: `SeLe4n/Model/Object/Structures.lean`** (~20 changes)

| Function/Theorem | Current HashMap Usage | New RHTable Usage |
|-------------------|----------------------|-------------------|
| `CNode.empty` | `slots := {}` | `slots := RHTable.empty 16` |
| `CNode.mk'` | `s : Std.HashMap Slot Capability := {}` | `s : RHTable Slot Capability := RHTable.empty 16` |
| `CNode.lookup` | `node.slots[slot]?` | `node.slots[slot]?` (via `GetElem?` instance — unchanged syntax) |
| `CNode.insert` | `node.slots.insert slot cap` | `node.slots.insert slot cap` (same API — name matches) |
| `CNode.remove` | `node.slots.erase slot` | `node.slots.erase slot` |
| `CNode.revokeTargetLocal` | `node.slots.filter fun s c => ...` | `node.slots.filter fun s c => ...` (via `RHTable.filter`) |
| `CNode.findFirstEmptySlot` | Uses `CNode.lookup` (unchanged) | Unchanged (delegates to `lookup`) |
| `CNode.slotsUnique` | `True` (trivial for HashMap) | `True` (trivial for RHTable — key uniqueness by `noDupKeys`) |
| `CNode.slotCountBounded` | `cn.slots.size ≤ cn.slotCount` | `cn.slots.size ≤ cn.slotCount` (same — `size` accessor) |
| `lookup_remove_eq_none` | `simp [remove, lookup]` | `simp [remove, lookup, RHTable.getElem?_erase_self]` |
| `lookup_mem_of_some` | `Std.HashMap.mem_iff_isSome_getElem?` | `RHTable.mem_iff_isSome_getElem?` |
| `lookup_insert_eq` | `simp [insert, lookup]` | `simp [insert, lookup, RHTable.getElem?_insert_self]` |
| `lookup_insert_ne` | `Std.HashMap.getElem?_insert` | `RHTable.getElem?_insert_ne` |
| `lookup_remove_ne` | `Std.HashMap.getElem?_erase` | `RHTable.getElem?_erase_ne` |
| `remove_slotCountBounded` | `Std.HashMap.size_erase_le` | `RHTable.size_erase_le` |
| `revokeTargetLocal_slotCountBounded` | `Std.HashMap.size_filter_le_size` | `RHTable.size_filter_le_size` |
| `mem_lookup_of_slotsUnique` | `Std.HashMap.getElem?_eq_some_getElem` | `RHTable.getElem?_eq_some_getElem` |
| `lookup_revokeTargetLocal_source_eq_lookup` | `HashMap_filter_preserves_key` | `RHTable.filter_preserves_key` |
| `BEq CNode` instance | `a.slots.fold ...` | `a.slots.fold ...` (same — `fold` API matches) |
| `CNode.beq_sound` | HashMap-specific proof | RHTable-specific proof (same structure) |

**File: `SeLe4n/Kernel/Capability/Invariant/Defs.lean`** (~6 changes)

| Theorem | HashMap Lemma Used | Replacement |
|---------|-------------------|-------------|
| `badgeRetained_by_revokeTargetLocal` (line ~587) | `Std.HashMap.getElem?_erase` | `RHTable.getElem?_erase_ne` |
| `slotLookupAfterFilter_source` (line ~608-609) | `Std.HashMap.mem_iff_isSome_getElem?`, `Std.HashMap.mem_of_mem_filter` | `RHTable.mem_iff_isSome_getElem?`, `RHTable.mem_of_mem_filter` |
| `slotLookupAfterFilter_eq` (line ~613-617) | `Std.HashMap.getElem?_eq_some_getElem`, `Std.HashMap.getElem_filter` | `RHTable.getElem?_eq_some_getElem`, `RHTable.getElem_filter` |

**File: `SeLe4n/Kernel/Capability/Invariant/Authority.lean`** (~4 changes)

| Line(s) | HashMap Lemma Used | Replacement |
|---------|-------------------|-------------|
| ~103 | `Std.HashMap.mem_iff_isSome_getElem?` | `RHTable.mem_iff_isSome_getElem?` |
| ~105 | `Std.HashMap.mem_filter` | `RHTable.mem_filter` |
| ~107 | `Std.HashMap.getKey_beq` | `RHTable.getKey_beq` |
| ~109-110 | `Std.HashMap.getElem_filter`, `getElem?_eq_some_getElem` | RHTable equivalents |

**File: `SeLe4n/Testing/StateBuilder.lean`** (~2 changes)

CNode construction sites use `Std.HashMap.ofList` for slots:
```lean
-- Current:
slots := Std.HashMap.ofList [(Slot.ofNat 0, cap1), (Slot.ofNat 1, cap2)]
-- New:
slots := RHTable.ofList [(Slot.ofNat 0, cap1), (Slot.ofNat 1, cap2)]
```
Requires adding `RHTable.ofList` in Phase N3 or as part of N4.

**File: `SeLe4n/Testing/MainTraceHarness.lean`** (~10 changes)

All CNode construction sites (lines 69, 284, 926, 1122, 1254, 1292, 1327,
1373, 1642, 1871) replace `Std.HashMap.ofList` with `RHTable.ofList`.

**Files NOT modified** (downstream proof files that reference CNode via
`lookupSlotCap` and `storeObject` but don't directly touch `Std.HashMap`):
- `Kernel/Capability/Invariant/Preservation.lean` — uses `CNode.lookup`/`insert`
  abstraction, not raw HashMap ops. Should compile unchanged.
- `Kernel/Capability/Operations.lean` — uses `CNode.resolveSlot`, `CNode.lookup`,
  `CNode.insert` abstraction. Should compile unchanged.
- `Kernel/IPC/Invariant/*.lean` — operates on endpoints/notifications, not CNodes.
- `Kernel/InformationFlow/Invariant/*.lean` — uses state-level projection, not
  CNode internals.

#### Task N4-A: Type change + operations (5 subtasks)

| ID | Description |
|----|-------------|
| N4-A1 | Add `import SeLe4n.Kernel.RobinHood` to `Model/Object/Types.lean` |
| N4-A2 | Change `CNode.slots` type from `Std.HashMap Slot Capability` to `RHTable Slot Capability` |
| N4-A3 | Update `CNode.empty` and `CNode.mk'` constructors |
| N4-A4 | Add `RHTable.ofList` constructor for test compatibility |
| N4-A5 | Verify `CNode.lookup`, `CNode.insert`, `CNode.remove` compile unchanged (API-compatible) |

#### Task N4-B: Theorem updates (8 subtasks)

| ID | Description |
|----|-------------|
| N4-B1 | Update `lookup_remove_eq_none` proof |
| N4-B2 | Update `lookup_mem_of_some` proof |
| N4-B3 | Update `lookup_insert_eq` and `lookup_insert_ne` proofs |
| N4-B4 | Update `lookup_remove_ne` proof |
| N4-B5 | Update `remove_slotCountBounded` proof |
| N4-B6 | Update `revokeTargetLocal_slotCountBounded` proof |
| N4-B7 | Update `lookup_revokeTargetLocal_source_eq_lookup` proof |
| N4-B8 | Update `BEq CNode` instance and `beq_sound` proof |

#### Task N4-C: Invariant file updates (4 subtasks)

| ID | Description |
|----|-------------|
| N4-C1 | Update `Invariant/Defs.lean` proofs (~3 theorems) |
| N4-C2 | Update `Invariant/Authority.lean` proofs (~4 theorems) |
| N4-C3 | Verify `Invariant/Preservation.lean` compiles unchanged |
| N4-C4 | Verify `Kernel/Capability/Operations.lean` compiles unchanged |

#### Task N4-D: Test fixture updates (3 subtasks)

| ID | Description |
|----|-------------|
| N4-D1 | Update `Testing/StateBuilder.lean` CNode construction |
| N4-D2 | Update `Testing/MainTraceHarness.lean` CNode construction (10 sites) |
| N4-D3 | Verify all test suites pass (`test_smoke.sh`, `test_full.sh`) |

**N4 totals**: 20 subtasks, ~400 LoC net changes across ~6 files.

---

### Phase N5: Test Coverage + Documentation

**Target version**: 0.17.5
**Files created**: `tests/RobinHoodSuite.lean`
**Files modified**: 8 documentation files + 4 GitBook chapters
**Constraint**: Zero `sorry`/`axiom`. All tests pass.

#### Task N5-A: Robin Hood standalone test suite (12 scenarios)

| Scenario ID | Description | Category |
|-------------|-------------|----------|
| RH-001 | Empty table: `get?` returns `none`, `size = 0`, `contains = false` | Smoke |
| RH-002 | Single insert/get roundtrip: `(empty.insert k v).get? k = some v` | Smoke |
| RH-003 | Insert/erase/get: erase then get returns `none` | Smoke |
| RH-004 | Overwrite: insert same key twice, get returns latest value | Correctness |
| RH-005 | Multiple distinct keys: insert 10 keys, verify all retrievable | Correctness |
| RH-006 | Collision handling: keys with same hash (mod capacity), all retrievable | Collision |
| RH-007 | Robin Hood swap verification: insert sequence that triggers swap, verify ordering | Invariant |
| RH-008 | Backward-shift verification: erase from middle of cluster, verify get still works | Erasure |
| RH-009 | Resize trigger: insert until 75% load, verify resize doubles capacity | Resize |
| RH-010 | Post-resize correctness: all entries accessible after resize | Resize |
| RH-011 | Large-scale: insert 200 entries, verify all retrievable, erase 100, verify remaining | Stress |
| RH-012 | Fold/toList: verify fold visits all entries, toList contains all pairs | Utility |

#### Task N5-B: CNode integration regression tests (6 scenarios)

| Scenario ID | Description |
|-------------|-------------|
| RH-INT-001 | CNode lookup/insert/remove with RHTable-backed slots |
| RH-INT-002 | CNode.revokeTargetLocal with RHTable filter |
| RH-INT-003 | CNode.findFirstEmptySlot with RHTable-backed slots |
| RH-INT-004 | CNode slotCountBounded after insert sequence |
| RH-INT-005 | Multi-level CSpace resolution with RHTable-backed CNodes |
| RH-INT-006 | CNode BEq comparison with RHTable slots |

#### Task N5-C: Test infrastructure (3 subtasks)

| ID | Description |
|----|-------------|
| N5-C1 | Add `robin_hood_suite` executable to `lakefile.toml` |
| N5-C2 | Add `RobinHoodSuite` to Tier 2 test script (`test_smoke.sh`) |
| N5-C3 | Update scenario registry YAML with RH-* and RH-INT-* scenario IDs |

#### Task N5-D: Documentation sync (13 subtasks)

| ID | File | Section(s) | Changes |
|----|------|-----------|---------|
| N5-D1 | `lakefile.toml` | version | Bump to 0.17.5 |
| N5-D2 | `README.md` | metrics table (lines 52–68) | Update LoC, theorem count, latest audit reference |
| N5-D3 | `docs/DEVELOPMENT.md` | active workstream (lines 8–14), next workstreams (lines 38–64) | Add WS-N portfolio status and phase breakdown |
| N5-D4 | `docs/spec/SELE4N_SPEC.md` | current state (lines 49–61), milestone history (lines 65–143) | Add WS-N entry, update version and metrics |
| N5-D5 | `docs/WORKSTREAM_HISTORY.md` | What's next section, completed portfolio table | Add WS-N phases N1–N5 with detailed descriptions |
| N5-D6 | `docs/CLAIM_EVIDENCE_INDEX.md` | claims table | Add WS-N claim rows with evidence commands |
| N5-D7 | `docs/gitbook/03-architecture-and-module-map.md` | module list | Add `SeLe4n/Kernel/RobinHood/Core.lean` and `Invariant.lean` module entries |
| N5-D8 | `docs/gitbook/04-project-design-deep-dive.md` | design sections | Add §11: Robin Hood hashing design (single-representation, fuel-bounded, cluster ordering) |
| N5-D9 | `docs/gitbook/05-specification-and-roadmap.md` | milestone history, roadmap | Add WS-N completion entries |
| N5-D10 | `docs/gitbook/12-proof-and-invariant-map.md` | proof surface | Add Robin Hood invariant bundle, preservation theorems, and bridge lemmas |
| N5-D11 | `docs/codebase_map.json` | (regenerate) | Run `./scripts/generate_codebase_map.py --pretty` |
| N5-D12 | `scripts/website_link_manifest.txt` | (if new paths added) | Add `SeLe4n/Kernel/RobinHood/` paths |
| N5-D13 | `CLAUDE.md` | source layout, active workstream, known large files | Add RobinHood module entries, update WS-N status |

**N5 totals**: 34 subtasks, ~300 LoC tests + ~200 LoC documentation changes.

---

## 6. Dependency Graph

```
N1-A (types) ──→ N1-B (empty) ──→ N1-C (insert) ──→ N1-D (insert top-level)
                                  ├──→ N1-E (lookup)
                                  └──→ N1-F (erase) ──→ N1-G (fold/resize)
                                                        ↓
N2-A (wf preservation) ←── N1-*
N2-B (distCorrect) ←── N1-C, N1-F
N2-C (noDupKeys) ←── N1-C, N1-F
N2-D (robinHoodOrdered) ←── N1-C, N1-F  ← CRITICAL PATH
N2-E (lookup correctness) ←── N2-B, N2-C, N2-D
  ↓
N3-A (instances) ←── N1-*
N3-B (bridge lemmas) ←── N2-E
N3-C (filter) ←── N1-G
  ↓
N4-A (type change) ←── N3-B
N4-B (theorem updates) ←── N3-B
N4-C (invariant updates) ←── N4-B
N4-D (test fixtures) ←── N4-A
  ↓
N5-A (standalone tests) ←── N1-*
N5-B (integration tests) ←── N4-D
N5-C (infrastructure) ←── N5-A
N5-D (documentation) ←── N5-B
```

**Critical path**: N1-C → N2-D → N2-E → N3-B → N4-B

---

## 7. HashMap Proof Dependency Catalog

This section catalogs every theorem in the kernel proof surface that directly
depends on `Std.HashMap` semantics, organized by the specific `Std.HashMap`
lemma used. Phase N3 must provide an `RHTable` equivalent for each.

### 7.1 `HashMap_getElem?_insert` / `Std.HashMap.getElem?_insert`

**Definition** (from `Prelude.lean:696–699`):
```lean
(m.insert k v)[a]? = if k == a then some v else m[a]?
```

**Downstream usage** (15 files, ~30 occurrences):
- `Model/State.lean:1062,1068` — `storeObject` (object store insert)
- `Model/Object/Structures.lean:572` — `CNode.lookup_insert_ne`
- `Kernel/Capability/Invariant/Authority.lean:249` — `cspaceRevoke` proof
- `Kernel/Scheduler/Operations/Core.lean` — RunQueue insert
- `Kernel/Scheduler/Operations/Preservation.lean` — RunQueue preservation
- `Kernel/IPC/Invariant/Structural.lean` — endpoint store proofs
- `Kernel/InformationFlow/Invariant/Helpers.lean` — projection preservation
- `Kernel/InformationFlow/Invariant/Operations.lean` — NI operation proofs
- `Kernel/Lifecycle/Invariant.lean` — lifecycle store proofs
- `Kernel/Architecture/VSpaceInvariant.lean` — VSpace mapping proofs
- `Kernel/Service/Invariant/Acyclicity.lean` — service store proofs
- `Kernel/Architecture/Invariant.lean` — architecture invariant proofs

**Phase N4 scope**: Only `Structures.lean` and `Capability/Invariant/*.lean`
references need updating (CNode.slots context). All other sites remain on
`Std.HashMap` and are unaffected.

### 7.2 `HashMap_getElem?_erase` / `Std.HashMap.getElem?_erase`

**Downstream usage**:
- `Model/Object/Structures.lean:584` — `CNode.lookup_remove_ne`
- `Kernel/Capability/Invariant/Defs.lean:587` — `badgeRetained_by_revokeTargetLocal`

### 7.3 `Std.HashMap.size_erase_le`

**Downstream usage**:
- `Model/Object/Structures.lean:537` — `CNode.remove_slotCountBounded`

### 7.4 `Std.HashMap.size_filter_le_size`

**Downstream usage**:
- `Model/Object/Structures.lean:546` — `CNode.revokeTargetLocal_slotCountBounded`

### 7.5 `Std.HashMap.mem_iff_isSome_getElem?`

**Downstream usage**:
- `Model/Object/Structures.lean:454` — `CNode.lookup_mem_of_some`
- `Kernel/Capability/Invariant/Authority.lean:103` — filter membership
- `Kernel/Capability/Invariant/Defs.lean:608` — filter source lookup

### 7.6 `Std.HashMap.getElem?_eq_some_getElem`

**Downstream usage**:
- `Model/Object/Structures.lean:556` — `CNode.mem_lookup_of_slotsUnique`
- `Kernel/Capability/Invariant/Authority.lean:110` — filter element access
- `Kernel/Capability/Invariant/Defs.lean:613–614` — filter lookup equality

### 7.7 `Std.HashMap.fold_eq_foldl_toList`

**Downstream usage**:
- `Model/State.lean:293,335,369,377,385,393,401,409` — `revokeAndClearRefsState` and related fold proofs

**Phase N4 scope**: NOT affected (these are on the object-store HashMap, not CNode.slots).

### 7.8 `HashMap_filter_preserves_key`

**Downstream usage**:
- `Model/Object/Structures.lean:474` — `CNode.lookup_revokeTargetLocal_source_eq_lookup`

### 7.9 Summary: Phase N4 Bridge Lemma Requirements

| Bridge Lemma | CNode Usage Sites | Priority |
|-------------|------------------|----------|
| `getElem?_insert_self` | `lookup_insert_eq` | CRITICAL |
| `getElem?_insert_ne` | `lookup_insert_ne`, `Authority.lean:249` | CRITICAL |
| `getElem?_erase_self` | `lookup_remove_eq_none` | CRITICAL |
| `getElem?_erase_ne` | `lookup_remove_ne`, `Defs.lean:587` | CRITICAL |
| `size_erase_le` | `remove_slotCountBounded` | HIGH |
| `size_filter_le_size` | `revokeTargetLocal_slotCountBounded` | HIGH |
| `mem_iff_isSome_getElem?` | `lookup_mem_of_some`, `Authority.lean:103`, `Defs.lean:608` | HIGH |
| `getElem?_eq_some_getElem` | `mem_lookup_of_slotsUnique`, `Authority.lean:110`, `Defs.lean:613` | HIGH |
| `filter_preserves_key` | `lookup_revokeTargetLocal_source_eq_lookup` | MEDIUM |
| `mem_filter` | `Authority.lean:105`, `Defs.lean:609` | MEDIUM |
| `getKey_beq` | `Authority.lean:107` | MEDIUM |
| `getElem_filter` | `Authority.lean:109`, `Defs.lean:617` | MEDIUM |


---

## 8. Acceptance Criteria

### 8.1 Per-Phase Acceptance

**Phase N1** (Core Implementation):
- [ ] `lake build` succeeds with zero errors
- [ ] No `partial` functions in `RobinHood/Core.lean`
- [ ] All array accesses use bounds-checked `Array.get`/`Array.set`
- [ ] `#eval` roundtrip: `(RHTable.empty 16).insert k v |>.get? k` returns `some v`
- [ ] `#eval` erase: `(t.insert k v |>.erase k).get? k` returns `none`
- [ ] `empty_wf` theorem compiles with zero `sorry`

**Phase N2** (Invariant Proofs):
- [ ] Zero `sorry`/`axiom` in `RobinHood/Invariant.lean`
- [ ] `get_after_insert_eq` compiles: `(t.insert k v).get? k = some v`
- [ ] `get_after_insert_ne` compiles: `k ≠ k' → (t.insert k v).get? k' = t.get? k'`
- [ ] `get_after_erase_eq` compiles: `(t.erase k).get? k = none`
- [ ] `insert_preserves_wf`, `erase_preserves_wf`, `resize_preserves_wf` all compile
- [ ] `insert_preserves_robinHoodOrdered` compiles (critical proof)

**Phase N3** (Bridge Layer):
- [ ] `GetElem?` instance: `t[k]?` syntax works
- [ ] `Membership` instance: `k ∈ t` syntax works
- [ ] All 12 bridge lemmas from §7.9 compile with zero `sorry`
- [ ] `RHTable.filter` defined and `filter_preserves_key` compiles

**Phase N4** (Integration):
- [ ] `CNode.slots` type is `RHTable Slot Capability`
- [ ] All 15 CNode theorems in `Structures.lean` compile
- [ ] All theorems in `Capability/Invariant/Defs.lean` compile
- [ ] All theorems in `Capability/Invariant/Authority.lean` compile
- [ ] `Capability/Invariant/Preservation.lean` compiles unchanged
- [ ] `Capability/Operations.lean` compiles unchanged
- [ ] `test_smoke.sh` passes
- [ ] `test_full.sh` passes
- [ ] Main trace fixture matches expected output

**Phase N5** (Tests + Docs):
- [ ] 12 RH-* standalone test scenarios pass
- [ ] 6 RH-INT-* integration test scenarios pass
- [ ] All 8 canonical documentation files updated
- [ ] All 4 GitBook chapters updated
- [ ] `docs/codebase_map.json` regenerated
- [ ] `scripts/website_link_manifest.txt` updated (if new paths)
- [ ] `CLAUDE.md` source layout and active workstream updated

### 8.2 Global Acceptance

```bash
# Zero sorry in Robin Hood module
rg 'sorry' SeLe4n/Kernel/RobinHood/ && echo "FAIL: sorry found" || echo "PASS"

# Zero axiom in Robin Hood module
rg 'axiom' SeLe4n/Kernel/RobinHood/ && echo "FAIL: axiom found" || echo "PASS"

# Zero partial in Robin Hood module
rg 'partial def' SeLe4n/Kernel/RobinHood/ && echo "FAIL: partial found" || echo "PASS"

# Zero unsafe array access in Robin Hood module
rg 'get!|set!' SeLe4n/Kernel/RobinHood/ && echo "FAIL: unsafe access" || echo "PASS"

# Build succeeds
source ~/.elan/env && lake build

# All proof declarations exist
rg 'theorem.*insert_preserves' SeLe4n/Kernel/RobinHood/
rg 'theorem.*erase_preserves' SeLe4n/Kernel/RobinHood/
rg 'theorem.*get_after_insert' SeLe4n/Kernel/RobinHood/
rg 'theorem.*get_after_erase' SeLe4n/Kernel/RobinHood/
rg 'theorem.*robinHoodOrdered' SeLe4n/Kernel/RobinHood/
rg 'theorem.*noDupKeys' SeLe4n/Kernel/RobinHood/
rg 'theorem.*distCorrect' SeLe4n/Kernel/RobinHood/

# Tests pass (tiered)
./scripts/test_smoke.sh     # Tier 0-2
./scripts/test_full.sh      # Tier 0-3

# Fixture match (no silent behavior change)
diff <(lake exe sele4n 2>&1) tests/fixtures/main_trace_smoke.expected
```

---

## 9. Risk Mitigation

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Robin Hood ordering proof (N2-D3) exceeds complexity budget | MEDIUM | HIGH — blocks N2-E, N3-B, all downstream | Split N2-D3 into sub-lemmas: (1) swap preserves local ordering, (2) non-swap advance preserves ordering, (3) compose via induction. If stuck, weaken to `robinHoodOrdered` as a runtime check (`Bool`) rather than `Prop`, deferring the proof to a follow-up workstream. |
| `RHTable.filter` requires full table rebuild (O(n)) | LOW | MEDIUM — performance regression on `revokeTargetLocal` | Acceptable: `revokeTargetLocal` is already O(m) (`HashMap.filter` is O(n) internally). No asymptotic change. Document in the workstream plan. |
| Integration (N4) breaks proofs in unexpected files | MEDIUM | MEDIUM — scope creep | Run `lake build` after EACH N4 subtask. If `Preservation.lean` or other files break, add them to N4 scope immediately. The bridge lemma names are designed to be drop-in replacements. |
| Resize proof (N2-A5/N2-D) is harder than anticipated | LOW | LOW — resize is deferrable | Fixed-capacity tables with generous initial sizing (e.g., 64 or 256 for CNode slots) are viable for kernel use cases. Defer resize proofs to a follow-up if needed. |
| Performance regression from `Nat` arithmetic vs. `USize` | LOW | LOW — model-level only | seLe4n is a formal model, not a production binary yet. `Nat` arithmetic is correct and proof-friendly. Hardware-targeted optimization (USize, LLVM lowering) is deferred to the RPi5 hardware binding workstream. |
| `LawfulBEq`/`LawfulHashable` requirements differ | LOW | LOW | `RHTable` uses the same typeclass hierarchy as `Std.HashMap`. Existing instances on `ObjId`, `Slot`, etc. satisfy both. |

---

## 10. Future Work (Post-WS-N)

### 10.1 Remaining HashMap Sites

After WS-N completes (replacing `CNode.slots`), 13 `Std.HashMap` usage sites
remain. These are organized by integration complexity for a follow-up workstream:

**Tier 1** (low complexity — self-contained, few downstream proofs):
- `SystemState.irqHandlers : Std.HashMap Irq ObjId` (simple key→value)
- `SystemState.asidTable : Std.HashMap ASID ObjId` (simple key→value)
- `SystemState.services : Std.HashMap ServiceId ServiceGraphEntry`
- `LifecycleMetadata.objectTypes : Std.HashMap ObjId KernelObjectType`
- `LifecycleMetadata.capabilityRefs : Std.HashMap SlotRef CapTarget`

**Tier 2** (moderate complexity — used in invariant proofs):
- `VSpaceRoot.mappings : Std.HashMap VAddr (PAddr × PagePermissions)`
  (~15 theorems in `Structures.lean`, VSpaceInvariant proofs)
- `CDT childMap/parentMap : Std.HashMap CdtNodeId ...`
  (used in CDT operations and acyclicity proofs)
- `SystemState.cdtSlotNode/cdtNodeSlot : Std.HashMap ...`
  (used in CDT lookup paths)

**Tier 3** (high complexity — deep proof surface impact):
- `SystemState.objects : Std.HashMap ObjId KernelObject`
  (the core object store — used by EVERY kernel subsystem; ~50+ downstream
  theorems across ~15 files)
- `RunQueue.byPriority/membership/threadPriority : Std.HashMap/HashSet`
  (scheduler hot path with structural invariants in `RunQueue` proofs)

### 10.2 HashSet Migration

`Std.HashSet` usage (2 sites: `objectIndexSet`, `RunQueue.membership`) would
require either:
- An `RHSet` wrapper around `RHTable α Unit`, or
- Direct `RHTable`-based set with `Unit` values and optimized `contains`.

### 10.3 Performance Optimization Layer

Once all proofs are complete, an optional optimization pass could:
- Replace `Nat` arithmetic with `USize` for hardware targets
- Add `@[inline]` annotations on hot-path operations
- Explore compile-time capacity specialization for known-size tables
- Benchmark against `Std.HashMap` on realistic kernel workloads

---

## 11. Glossary

| Term | Definition |
|------|-----------|
| **Probe distance** | The number of slots between an entry's actual position and its ideal position (hash(key) % capacity). Also called "displacement" or "DIB" (distance from initial bucket). |
| **Cluster** | A maximal contiguous run of occupied slots in the table (with wrap-around). |
| **Robin Hood property** | Within each cluster, probe distances are non-decreasing. Equivalently: no entry is "richer" (closer to ideal) than a later entry in the same cluster. |
| **Backward shift** | The erasure strategy: after removing an entry, shift subsequent entries in the cluster backward by one slot, decrementing their probe distances. This avoids tombstones. |
| **Fuel** | A `Nat` parameter used for structural recursion on loops that would otherwise need `partial`. Initialized to `capacity`, which is an upper bound on probe distance. |
| **Bridge lemma** | A theorem about `RHTable` that mirrors a `Std.HashMap` theorem, enabling drop-in replacement in downstream proofs. |
| **Load factor** | `size / capacity`. Resize is triggered when load factor reaches 75% (3/4). |

---

## 12. Revision History

| Date | Author | Changes |
|------|--------|---------|
| 2026-03-17 | Claude (WS-N planning) | Initial skeleton with Parts 1–3 |
| 2026-03-17 | Claude (WS-N planning) | Expanded into comprehensive 5-phase plan with 122 subtasks, proof strategies, per-file change specs, HashMap dependency catalog, risk mitigation, and documentation sync plan |
