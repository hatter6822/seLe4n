# V3-B Migration Plan — `loadFactorBounded` Integration & `hSize` Elimination

**Created**: 2026-03-26
**Baseline version**: 0.22.0
**Parent workstream**: WS-V Phase V3 (Proof Chain Hardening), sub-tasks V3-A + V3-B
**Finding**: H-RH-1 (HIGH) — `erase_preserves_invExt` requires separate `hSize`
hypothesis not derivable from `invExt`
**Constraint**: Zero `sorry`/`axiom` in production proof surface
**Gate**: `lake build` succeeds for every modified module; `test_full.sh` green

---

## 1. Problem Statement

### 1.1 The Architectural Gap

The Robin Hood hash table's extended invariant bundle (`invExt`) is defined as:

```lean
-- SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean:447-448
def RHTable.invExt [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
  t.WF ∧ t.distCorrect ∧ t.noDupKeys ∧ t.probeChainDominant
```

The `erase` operation's invariant preservation theorem requires an **extra hypothesis**
that is not part of `invExt`:

```lean
-- SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean:2406-2412
theorem RHTable.erase_preserves_invExt [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) (hSize : t.size < t.capacity) :
    (t.erase k).invExt
```

The `hSize : t.size < t.capacity` parameter is **architecturally blocked** — it cannot
be derived from `invExt` alone. Yet every reachable table state satisfies this property
because `RHTable.insert` resizes at 75% load (`size * 4 ≥ capacity * 3` triggers 2x
resize), which implies `size < capacity` for all post-insert states.

### 1.2 The `loadFactorBounded` Definition

```lean
-- SeLe4n/Kernel/RobinHood/Invariant/Defs.lean:48-49
def RHTable.loadFactorBounded (t : RHTable α β) : Prop :=
  t.size * 4 ≤ t.capacity * 3
```

This definition exists but is **not included** in `invExt`. The mathematical implication
is straightforward:

```
loadFactorBounded t ∧ WF t  (where WF includes 0 < capacity)
    ⟹  t.size * 4 ≤ t.capacity * 3
    ⟹  t.size ≤ t.capacity * 3 / 4
    ⟹  t.size < t.capacity        (since capacity > 0 and sizes are Nat)
```

### 1.3 Impact

**23 call sites** across 8 files must independently obtain and pass `hSize` proofs.
This creates:

- **Proof maintenance burden**: Every new erase call site must thread a size hypothesis
- **Redundant structure fields**: `RunQueue` carries 3 `sizeOk` fields; `CNode.slotsUnique`
  bundles `size < capacity` alongside `invExt`; `storeObject_preserves_invariant` takes
  `hAsidSize` as a parameter
- **Signature pollution**: Functions that compose erase with other operations must propagate
  `hSize` through their entire call chain
- **Missed proof obligations**: New kernel modules using RHTables must discover the `hSize`
  requirement by trial and error rather than having it follow from the standard invariant

---

## 2. Design Decision

### 2.1 Options Considered

| Option | Description | Pros | Cons |
|--------|------------|------|------|
| **A: Extend `invExt`** | Add `loadFactorBounded` as 5th conjunct of `invExt` | Single invariant bundle; all callers automatically get `size < capacity`; cleanest API | Requires proving `loadFactorBounded` preservation for insert, erase, resize, filter, insertNoResize, ofList, empty |
| B: New `invExtFull` | Create `invExtFull := invExt ∧ loadFactorBounded` | Non-breaking; existing `invExt` callers untouched | Two bundles to track; callers must choose; doesn't eliminate the root cause |
| C: Lemma only | Add `invExt_implies_size_lt_capacity` assuming `loadFactorBounded` as separate hypothesis | Minimal change | Still requires callers to track `loadFactorBounded` separately |

### 2.2 Selected Approach: Option A — Extend `invExt`

**Rationale**: `loadFactorBounded` is an invariant of the data structure, not a precondition.
Every public constructor (`empty`, `insert`, `resize`, `filter`, `ofList`) maintains it.
No reachable state violates it. Adding it to `invExt` is the correct architectural choice.

The extended definition will be:

```lean
def RHTable.invExt [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
  t.WF ∧ t.distCorrect ∧ t.noDupKeys ∧ t.probeChainDominant ∧ t.loadFactorBounded
```

---

## 3. Call Site Inventory

### 3.1 Complete Enumeration of Affected Call Sites

Every call site that passes `hSize : t.size < t.capacity` to `erase_preserves_invExt`
(or its wrappers) must be updated. Organized by dependency order:

#### Layer 0: Core Definition (2 sites)

| # | File | Line | Theorem/Function | `hSize` Source | Change Required |
|---|------|------|------------------|----------------|-----------------|
| 1 | `RobinHood/Invariant/Preservation.lean` | 2406 | `RHTable.erase_preserves_invExt` | **Signature parameter** | Remove `hSize` param; derive from `hExt.2.2.2.2` |
| 2 | `RobinHood/Invariant/Preservation.lean` | 2412 | (proof body) | `hSize` passed to `erase_preserves_probeChainDominant` | Extract via `have hSize := invExt_implies_size_lt_capacity t hExt` |

#### Layer 1: Wrapper / Re-export (2 sites)

| # | File | Line | Theorem/Function | `hSize` Source | Change Required |
|---|------|------|------------------|----------------|-----------------|
| 3 | `RobinHood/Set.lean` | 126-130 | `RHSet.erase_preserves_invExt` | Parameter `hSize` | Remove `hSize` param; call updated `erase_preserves_invExt` |
| 4 | `Prelude.lean` | 928-932 | `RHTable_erase_preserves_invExt` | Parameter `hSize` | Remove `hSize` param; call updated `erase_preserves_invExt` |

#### Layer 2: Model / Object Layer (9 sites)

| # | File | Line | Theorem/Function | `hSize` Source | Change Required |
|---|------|------|------------------|----------------|-----------------|
| 5 | `Model/Object/Structures.lean` | 647 | `remove_slotsUnique` | `hUniq.2.1` from `CNode.slotsUnique` | Remove `hSize` arg from call |
| 6 | `Model/Object/Structures.lean` | 1287 | `foldl_erase_preserves` (private) | Parameter `hSize` | Remove `hSize` from signature + call |
| 7 | `Model/Object/Structures.lean` | 1306 | `foldl_erase_none` (private) | Parameter `hSize` | Remove `hSize` from signature + call |
| 8 | `Model/Object/Structures.lean` | 1326 | `foldl_erase_mem` (private) | Parameter `hSize` | Remove `hSize` from signature + call |
| 9 | `Model/Object/Structures.lean` | 1365 | `foldl_erase_invExt` (local) | Parameter `hS` | Remove `hS` from signature + call |
| 10 | `Model/Object/Structures.lean` | 1474 | `removeNode_childMapConsistent` | Parameter `hSizeCM` | Remove `hSizeCM` from signature + call |
| 11 | `Model/Object/Structures.lean` | 1494 | `removeNode_childMapConsistent` | `hEraseSize` (derived L1475) | Remove `hEraseSize` derivation + call |
| 12 | `Model/Object/Structures.lean` | 1510 | `removeNode_childMapConsistent` | `hEraseSize` (derived L1475) | Remove `hEraseSize` derivation + call |
| 13 | `Model/State.lean` | 1293 | `storeObject_preserves_invariant` | Parameter `hAsidSize` | Remove `hAsidSize` from signature + call |

#### Layer 3: Builder / Construction Phase (2 sites)

| # | File | Line | Theorem/Function | `hSize` Source | Change Required |
|---|------|------|------------------|----------------|-----------------|
| 14 | `Model/Builder.lean` | 240 | `deleteObject` | Parameters `hObjSize`, `hTypesSize` | Remove both params from signature |
| 15 | `Model/Builder.lean` | 254-256 | (proof body) | `hObjSize`, `hTypesSize` passed to `erase_preserves_invExt` | Remove args from calls |

#### Layer 4: Scheduler (3 sites)

| # | File | Line | Theorem/Function | `hSize` Source | Change Required |
|---|------|------|------------------|----------------|-----------------|
| 16 | `Scheduler/RunQueue.lean` | 233 | `removeThread` | `rq.mem_sizeOk` (struct field) | Remove `hSize` arg; field removable |
| 17 | `Scheduler/RunQueue.lean` | 248 | `removeThread` | `rq.byPrio_sizeOk` (struct field) | Remove `hSize` arg; field removable |
| 18 | `Scheduler/RunQueue.lean` | 250-251 | `removeThread` | `rq.threadPrio_sizeOk` (struct field) | Remove `hSize` arg; field removable |

#### Layer 5: Capability System (3 sites)

| # | File | Line | Theorem/Function | `hSize` Source | Change Required |
|---|------|------|------------------|----------------|-----------------|
| 19 | `Capability/Invariant/Preservation.lean` | 361 | `cspaceDeleteSlotCore_preserves_cdtNodeSlot` | `hSzRef` (derived L359-360) | Remove `hSzRef` derivation + arg |
| 20 | `Capability/Invariant/Preservation.lean` | 799 | nested match case | `hSzDel` (parameter) | Remove `hSzDel` from signature + arg |
| 21 | `Capability/Invariant/Preservation.lean` | 1127 | `processRevokeNode_preserves_capabilityInvariantBundle` | `hNSSzDel` (parameter) | Remove `hNSSzDel` from signature + arg |

#### Layer 6: RobinHood Internal Proofs (1 site)

| # | File | Line | Theorem/Function | `hSize` Source | Change Required |
|---|------|------|------------------|----------------|-----------------|
| 22 | `RobinHood/Invariant/Lookup.lean` | 1956 | `get_after_erase_ne` | Parameter `hSize` | Remove `hSize` from signature + call |

### 3.2 Secondary Structural Changes (Field / Bundle Removal)

After the `hSize` parameter is eliminated from `erase_preserves_invExt`, several
**structural artifacts** become unnecessary. These are not call sites but storage
locations for `size < capacity` proofs that only existed to feed erase:

| # | File | Location | Artifact | Change |
|---|------|----------|----------|--------|
| S1 | `Scheduler/RunQueue.lean` | L34-39 | `mem_sizeOk`, `byPrio_sizeOk`, `threadPrio_sizeOk` fields | **Evaluate for removal** — also used by `insert_size_lt_capacity` |
| S2 | `Model/Object/Structures.lean` | L532-533 | `CNode.slotsUnique` definition | **Evaluate** — `size < capacity` component may remain for `insert_size_lt_capacity` |
| S3 | `Model/Builder.lean` | L240-241 | `deleteObject` parameter list | Remove `hObjSize`, `hTypesSize` params |
| S4 | `Model/State.lean` | L1260+ | `storeObject_preserves_invariant` | Remove `hAsidSize` param |
| S5 | `Capability/Invariant/Preservation.lean` | L367-368 | `cspaceDeleteSlot_preserves_cdtNodeSlot` | Remove `hNodeSlotSize` param |

**Critical Note on S1 and S2**: The `sizeOk` fields and `slotsUnique` bundle contain
`size < capacity` which is also used by `insert_size_lt_capacity` (Bridge.lean:391).
Since `insert_size_lt_capacity` is a separate theorem with its own `hSizeLt` parameter,
these fields **cannot be removed yet**. However, once `loadFactorBounded` is in `invExt`,
a future V7 task could derive `size < capacity` from `invExt` for insert as well. For
V3-B, we **only** remove `hSize` from erase paths; insert paths remain unchanged.

### 3.3 Call Sites That Use `erase_size_lt_capacity` (Unaffected)

The theorem `RHTable.erase_size_lt_capacity` (Bridge.lean:425-435) has its own
`hSizeLt` parameter and is used to **maintain** `size < capacity` in structures
like `RunQueue` after erase. These sites are **not directly affected** by V3-B but
become candidates for future simplification:

- `Model/Object/Structures.lean:648` — `remove_slotsUnique` proof
- `Model/Object/Structures.lean:1365` — `foldl_erase_invExt` inductive step
- `Capability/Invariant/Preservation.lean:362` — `erase_size_lt_capacity` for cdtNodeSlot
- `Scheduler/RunQueue.lean:252-274` — `removeThread` maintaining `sizeOk` fields

---

## 4. Dependency Graph (Revised)

```
Phase 1: Foundation (V3-A) — add size < capacity ∧ 4 ≤ capacity to invExt
  ├─ U1-R: empty_size_lt_capacity                    [DONE — trivial]
  ├─ U3-R: resize_size_lt_capacity                   [new, ~10 lines]
  ├─ U4-R: erase_size_lt_capacity                    [DONE — Bridge.lean]
  ├─ U5-R: filter_size_lt_capacity                   [DONE — Bridge.lean]
  ├─ U6-R: Update invExt definition (add 2 conjuncts)
  │         └─ Depends on: U1-R, U3-R
  └─ U7-R: Add invExt_implies_size_lt_capacity lemma
            └─ Depends on: U6-R

Phase 2: Core Refactor (V3-B Layer 0-1) — update composite proofs & wrappers
  ├─ U8:  Update empty_invExt / empty_invExt'         ← U6-R
  ├─ U9:  Update insert_preserves_invExt              ← U6-R, U7-R
  ├─ U10: Remove hSize from erase_preserves_invExt    ← U6-R, U7-R
  ├─ U11: Update resize_preserves_invariant           ← U3-R, U6-R
  ├─ U12: Update RHSet.erase_preserves_invExt         ← U10
  ├─ U13: Update Prelude.lean re-export               ← U10
  ├─ U14: Update RHSet.insert_preserves_invExt        ← U9
  └─ U15: Update empty_invExt' constructor            ← U6-R

Phase 3: Call Site Migration (V3-B Layers 2-6) — all depend on U10
  ├─ U16:  Structures.lean remove_slotsUnique         ← U10
  ├─ U16b: Simplify CNode.slotsUnique (optional)      ← U9, U10
  ├─ U17:  Structures.lean CDT fold helpers            ← U10
  ├─ U18:  Structures.lean removeNode_childMapConsist. ← U10, U17
  ├─ U19:  State.lean storeObject_preserves_invariant  ← U10
  ├─ U20:  Builder.lean deleteObject                   ← U10
  ├─ U21:  RunQueue.lean removeThread                  ← U10, U12
  ├─ U21b: Remove redundant RunQueue fields (optional) ← U21
  ├─ U22:  Capability/Invariant/Preservation.lean      ← U10
  └─ U23:  RobinHood/Invariant/Lookup.lean             ← U10

Phase 4: Validation & Documentation
  ├─ U24: Build every modified module individually     ← U8-U23
  ├─ U25: Run test_full.sh                             ← U24
  └─ U26: Update documentation                        ← U25
```

---

## 5. Implementation Units

### Phase 1: Foundation — `loadFactorBounded` Preservation Proofs (V3-A)

These units establish that `loadFactorBounded` is preserved by every RHTable operation,
which is the prerequisite for adding it to `invExt`.

#### U1: `empty_loadFactorBounded` (already exists)

- **File**: `RobinHood/Invariant/Defs.lean:52-54`
- **Status**: DONE — theorem `RHTable.empty_loadFactorBounded` already proven
- **Proof**: `simp [loadFactorBounded, RHTable.empty]` (size = 0, trivial)
- **Work required**: None

#### U2: `insertNoResize_preserves_loadFactorBounded`

- **File**: `RobinHood/Invariant/Preservation.lean` (new, near existing insertNoResize proofs)
- **Scope**: Small (~15 lines)
- **Statement**:
  ```lean
  theorem RHTable.insertNoResize_preserves_loadFactorBounded [BEq α] [Hashable α]
      (t : RHTable α β) (k : α) (v : β)
      (hLFB : t.loadFactorBounded) (hWF : t.WF) :
      (t.insertNoResize k v).loadFactorBounded
  ```
- **Proof strategy**: `insertNoResize` either replaces an existing key (size unchanged,
  capacity unchanged → `loadFactorBounded` preserved trivially) or inserts a new key
  (size increases by 1). The caller (`insert`) guarantees that `insertNoResize` is only
  called when `size * 4 < capacity * 3` (the no-resize branch) or after a resize
  (which halves the load factor). In the no-resize branch: `(size+1) * 4 ≤ capacity * 3`
  needs the pre-condition that `size * 4 < capacity * 3`.
- **Key insight**: `insertNoResize` is always called either (a) from `insert` after the
  resize check ensures `size * 4 < capacity * 3`, or (b) from `resize` which starts
  with an empty doubled table. For case (a), we need the strict inequality. The existing
  `loadFactorBounded` (`size * 4 ≤ capacity * 3`) combined with the **negation** of
  the resize trigger (`¬ (size * 4 ≥ capacity * 3)`) gives `size * 4 < capacity * 3`,
  so `(size + 1) * 4 ≤ capacity * 3 + 4 - 4 = capacity * 3`.
- **Risk**: Low — arithmetic on naturals, `omega` should handle it
- **Dependencies**: None (U1 only needs to exist for empty tables)

#### U3: `resize_preserves_loadFactorBounded`

- **File**: `RobinHood/Invariant/Preservation.lean` (new, near existing resize proofs)
- **Scope**: Small (~20 lines)
- **Statement**:
  ```lean
  theorem RHTable.resize_preserves_loadFactorBounded [BEq α] [Hashable α] [LawfulBEq α]
      (t : RHTable α β) (hLFB : t.loadFactorBounded) (hWF : t.WF) :
      (t.resize).loadFactorBounded
  ```
- **Proof strategy**: `resize` doubles capacity and re-inserts all entries. After resize:
  - `capacity' = capacity * 2`
  - `size' = size` (same entries re-inserted, no new entries)
  - `size' * 4 = size * 4 ≤ capacity * 3 ≤ (capacity * 2) * 3 = capacity' * 3`
  - So `loadFactorBounded` is trivially preserved (load factor halved)
- **Note**: May need to thread through `resize` implementation details. The key fact
  is `t.resize.size = t.size` (resize doesn't change entry count) and
  `t.resize.capacity = t.capacity * 2`.
- **Risk**: Low — `resize` size/capacity lemmas may already exist or be straightforward
- **Dependencies**: U2 (resize calls insertNoResize internally, but the top-level
  capacity doubling argument may not need U2 directly)

#### U4: `insert_preserves_loadFactorBounded`

- **File**: `RobinHood/Invariant/Preservation.lean` (new, near existing insert proofs)
- **Scope**: Small (~20 lines)
- **Statement**:
  ```lean
  theorem RHTable.insert_preserves_loadFactorBounded [BEq α] [Hashable α] [LawfulBEq α]
      (t : RHTable α β) (k : α) (v : β)
      (hLFB : t.loadFactorBounded) (hWF : t.WF) :
      (t.insert k v).loadFactorBounded
  ```
- **Proof strategy**: `insert` is defined as:
  ```lean
  let t' := if t.size * 4 ≥ t.capacity * 3 then t.resize else t
  t'.insertNoResize k v
  ```
  Case split on the resize condition:
  - **Resize branch** (`size * 4 ≥ capacity * 3`): `t.resize` produces a table with
    `loadFactorBounded` (by U3). Then `insertNoResize` on that table preserves it (by U2).
  - **No-resize branch** (`size * 4 < capacity * 3`): We have strict inequality
    `size * 4 < capacity * 3`, so `insertNoResize` (which adds at most 1 entry)
    preserves `(size + 1) * 4 ≤ capacity * 3` — need to verify this arithmetic.
    Actually: `size * 4 < cap * 3` means `size * 4 ≤ cap * 3 - 1`, so
    `(size+1)*4 = size*4 + 4 ≤ cap*3 - 1 + 4 = cap*3 + 3`. This is NOT ≤ cap*3.
    **Key nuance**: `insertNoResize` may or may not increase size (if key already exists,
    size unchanged). We need `insertNoResize_size_le` showing `(t.insertNoResize k v).size ≤ t.size + 1`
    AND the capacity doesn't change. The real argument: in the no-resize branch, the
    load factor might temporarily exceed the 75% threshold for a single insertion, but
    the NEXT insert will resize. We need to prove `(insertNoResize k v).loadFactorBounded`
    under the condition that `¬ (size * 4 ≥ capacity * 3)`, i.e., `size * 4 < capacity * 3`.
    If key exists: size unchanged, trivially preserved.
    If key new: size → size + 1. `(size+1)*4 = size*4 + 4`. Since `size*4 ≤ cap*3 - 1`
    (strict less), `(size+1)*4 ≤ cap*3 + 3`. This is **not** ≤ `cap*3`.

    **Resolution**: The load factor bound `size * 4 ≤ capacity * 3` is an **invariant
    on the table state**, not on intermediate states. After `insert`, we have:
    - If resize happened: capacity doubles, so `size * 4 ≤ (2*cap) * 3` holds easily.
    - If no resize: `size * 4 < cap * 3`. After `insertNoResize`, if key is new,
      `size' = size + 1`, so `size' * 4 = size*4 + 4`. Since `size*4 < cap*3` means
      `size*4 ≤ cap*3 - 1`, we get `size'*4 ≤ cap*3 + 3`. This is NOT ≤ cap*3 in
      general. Example: cap=4, size=2. `2*4=8 < 4*3=12`. Insert: size'=3.
      `3*4=12 ≤ 4*3=12`. OK this works. Another: cap=4, size=3. `3*4=12 ≥ 4*3=12`.
      Resize triggered. So the no-resize branch has `size*4 < cap*3`, meaning
      `size*4 ≤ cap*3 - 1`. Then `(size+1)*4 ≤ cap*3 - 1 + 4 = cap*3 + 3`.
      But we need `(size+1)*4 ≤ cap*3`. This FAILS for cap=5, size=3:
      `3*4=12 < 5*3=15`. Insert: `4*4=16 > 5*3=15`. LFB violated!

    **This means `insert` does NOT preserve `loadFactorBounded` as stated!**
    The resize trigger is `≥`, not `>`: `if t.size * 4 ≥ t.capacity * 3 then resize`.
    So after insert without resize, we have `size*4 < cap*3` (strict), and new size
    is at most `size + 1`. `(size+1)*4 ≤ cap*3` iff `size*4 ≤ cap*3 - 4`. But the
    no-resize condition only gives `size*4 ≤ cap*3 - 1`.

    **Corrected analysis**: The load factor bound `size * 4 ≤ capacity * 3` is the
    **pre-insert** invariant. After insert (without resize), the table MAY have
    `size * 4 > capacity * 3` (but will resize on the NEXT insert). The bound is
    restored by the next resize.

    **This changes the design**: `loadFactorBounded` as currently defined is NOT
    preserved by `insert`. We have two options:

    **(A)** Weaken `loadFactorBounded` to `size ≤ capacity` (not load-factor-specific).
    This IS preserved by insert (the resize-at-75% policy guarantees
    `size + 1 ≤ capacity` since `size * 4 < cap * 3` implies `size < cap`).
    Actually, `size * 4 < cap * 3` → `size < cap * 3 / 4 < cap`, so `size + 1 ≤ cap`.
    Wait: `size + 1 ≤ cap` means `size < cap`, and after insertNoResize (which may
    or may not add), `size' ≤ size + 1 ≤ cap`. So `size' ≤ capacity`. But we need
    `size' < capacity` for erase. `size' ≤ capacity` is NOT strict.

    **(B)** Use `size < capacity` as the invariant (NOT `loadFactorBounded`).
    After insert without resize: `size * 4 < cap * 3` → `size < cap * 3/4 < cap` →
    `size + 1 ≤ cap * 3/4 + 1`. Is `size + 1 < cap`? We need `size + 1 < cap`.
    `size * 4 < cap * 3` → `size ≤ (cap * 3 - 1) / 4`. For cap ≥ 2:
    `size + 1 ≤ (cap * 3 - 1) / 4 + 1`. Is this < cap? For cap=4:
    `(12-1)/4 + 1 = 2+1 = 3 < 4`. ✓ For cap=5: `(15-1)/4 + 1 = 3+1 = 4 < 5`. ✓
    For cap=2: `(6-1)/4 + 1 = 1+1 = 2`. NOT < 2. But cap ≥ 4 is required by
    `insert_size_lt_capacity` (Bridge.lean:391). With cap ≥ 4:
    `size * 4 < cap * 3` → `size ≤ cap*3/4 - 1` (integer division). For cap=4:
    size ≤ 2. size+1 ≤ 3 < 4. ✓ This is exactly what `insert_size_lt_capacity` proves!

    **Conclusion**: The correct invariant to add to `invExt` is `t.size < t.capacity`
    (the `sizeUnderCapacity` predicate), NOT `loadFactorBounded`. The `loadFactorBounded`
    property (`size * 4 ≤ cap * 3`) is a pre-insert condition that is temporarily
    violated after insert (restored by next resize). But `size < capacity` IS preserved
    by both insert (with cap ≥ 4) and erase.

    **However**, `insert_size_lt_capacity` requires `cap ≥ 4` AND `size < capacity`
    AND `invExt`. So `size < capacity` is a genuine invariant of the system, maintained
    by all operations under the `cap ≥ 4` assumption. Since all kernel tables start
    with capacity 16, `cap ≥ 4` always holds (resize doubles, so capacity stays ≥ 16).

    **REVISED DESIGN DECISION**: See Section 2.3 below.

- **Risk**: Medium — the arithmetic requires careful case analysis
- **Dependencies**: U2, U3

#### DESIGN REVISION (U4 Analysis Result)

The analysis in U4 reveals that `loadFactorBounded` (`size * 4 ≤ cap * 3`) is NOT
preserved by `insert` — after inserting into a table with `size * 4 = cap * 3 - 1`
(just below the resize threshold), the post-insert table has `size * 4 = cap * 3 + 3`,
violating the bound. The bound is only restored when the next insert triggers a resize.

**However**, the weaker property `size < capacity` IS preserved by all operations:

| Operation | Preserves `size < capacity`? | Condition |
|-----------|------------------------------|-----------|
| `empty` | ✓ | `size = 0, capacity > 0` |
| `insertNoResize` | ✓ (with condition) | Needs `size < capacity` pre-state (guaranteed by `insert`) |
| `resize` | ✓ | Capacity doubles, size unchanged |
| `insert` | ✓ | With `cap ≥ 4` (proven in `insert_size_lt_capacity`) |
| `erase` | ✓ | Size decreases or unchanged, capacity unchanged |
| `filter` | ✓ | Size can only decrease, capacity unchanged |

---

### REVISED Section 2.3: Corrected Design Decision

After detailed analysis (see U4), the correct invariant to add to `invExt` is NOT
`loadFactorBounded` but rather `sizeUnderCapacity`:

```lean
def RHTable.sizeUnderCapacity (t : RHTable α β) : Prop :=
  t.size < t.capacity
```

**Rationale**: `loadFactorBounded` (`size * 4 ≤ cap * 3`) is a trigger condition for
resize, not a post-operation invariant. It is temporarily violated after a non-resizing
insert. By contrast, `size < capacity` is a true operational invariant:

- Empty tables satisfy it (`size = 0, cap > 0`)
- `insert` preserves it (the resize-at-75% policy ensures `size + 1 < capacity`,
  proven in `insert_size_lt_capacity` with `cap ≥ 4`)
- `erase` preserves it (size can only decrease)
- `resize` preserves it (capacity doubles, size unchanged)
- `filter` preserves it (size can only decrease)

Adding `size < capacity` to `invExt` solves the H-RH-1 finding directly: the `hSize`
parameter on `erase_preserves_invExt` becomes derivable from `hExt`.

**However, there is a complication**: `insert_size_lt_capacity` requires `cap ≥ 4` as
a precondition. All kernel tables start at capacity 16, and resize only doubles, so
`cap ≥ 4` always holds in practice. We have two sub-options:

**(A)** Add `size < capacity` to `invExt` and also add `cap ≥ 4`:
```lean
def RHTable.invExt [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
  t.WF ∧ t.distCorrect ∧ t.noDupKeys ∧ t.probeChainDominant ∧
  t.size < t.capacity ∧ 4 ≤ t.capacity
```
This eliminates both `hSize` and `hCapGe4` from all call sites.

**(B)** Add only `size < capacity` to `invExt`:
```lean
def RHTable.invExt [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
  t.WF ∧ t.distCorrect ∧ t.noDupKeys ∧ t.probeChainDominant ∧ t.size < t.capacity
```
This eliminates `hSize` from erase sites. Insert sites still need `hCapGe4`.

**Selected: Option B** — Add only `size < capacity` to `invExt`.

Rationale: The `cap ≥ 4` property is a construction-time guarantee, not an operational
invariant of arbitrary RHTables. A table constructed with `RHTable.empty 1 (by omega)`
has `cap = 1` and would not satisfy `4 ≤ cap`. While kernel tables always have `cap ≥ 16`,
encoding this in `invExt` conflates a system-level policy with a data-structure invariant.
Option A could be pursued in a follow-up (V7), but V3-B should make the minimal correct
change.

**Note on `loadFactorBounded`**: The existing `loadFactorBounded` definition and its
theorems (`empty_loadFactorBounded`, `insert_resizes_at_capacity`,
`insert_fails_at_capacity`) remain useful as specification documentation. They are NOT
deleted — they just don't need to be in `invExt`.

---

### Revised Phase 1: Foundation — `sizeUnderCapacity` Preservation Proofs

With the corrected design, Phase 1 is simpler because `size < capacity` preservation
proofs either already exist or are trivial.

#### U1-R: Verify `empty` satisfies `size < capacity` (already true)

- **File**: `RobinHood/Invariant/Defs.lean` or `Preservation.lean`
- **Scope**: XS (~5 lines)
- **Statement**:
  ```lean
  theorem RHTable.empty_size_lt_capacity (cap : Nat) (hPos : 0 < cap) :
      (RHTable.empty cap hPos : RHTable α β).size < (RHTable.empty cap hPos : RHTable α β).capacity
  ```
- **Proof**: `simp [RHTable.empty]` — size = 0, capacity = cap, and `0 < cap` by hypothesis
- **Risk**: None
- **Dependencies**: None

#### U2-R: `insertNoResize_preserves_size_lt_capacity`

- **File**: `RobinHood/Invariant/Preservation.lean`
- **Scope**: Small (~15 lines)
- **Statement**:
  ```lean
  theorem RHTable.insertNoResize_preserves_size_lt_capacity [BEq α] [Hashable α]
      (t : RHTable α β) (k : α) (v : β)
      (hSizeLt : t.size < t.capacity) (hWF : t.WF)
      (hNotFull : t.size * 4 < t.capacity * 3) :
      (t.insertNoResize k v).size < (t.insertNoResize k v).capacity
  ```
- **Proof strategy**: The `hNotFull` condition from the no-resize branch of `insert`
  gives us room: `size * 4 < cap * 3` → `size < cap * 3/4`. After insertNoResize, size
  increases by at most 1 (if key is new) and capacity is unchanged. Under `cap ≥ 4`
  (which follows from `hNotFull` + `hSizeLt`), `size + 1 < cap`.
- **Note**: This theorem may already exist as `insert_size_lt_capacity` in Bridge.lean.
  Check if it can be reused or if we need a variant without `hCapGe4`.
- **Risk**: Low
- **Dependencies**: None

**Observation**: `insert_size_lt_capacity` (Bridge.lean:391) already proves exactly this
for the `insert` function (not `insertNoResize`). It takes `(hExt : t.invExt)
(hSizeLt : t.size < t.capacity) (hCapGe4 : 4 ≤ t.capacity)`. Since `insert` wraps
`insertNoResize`, and the existing proof handles both resize and no-resize branches,
we may not need U2-R at all — the existing `insert_size_lt_capacity` suffices for
proving that `insert` preserves `size < capacity`.

#### U3-R: `resize_preserves_size_lt_capacity`

- **File**: `RobinHood/Invariant/Preservation.lean`
- **Scope**: Small (~10 lines)
- **Statement**:
  ```lean
  theorem RHTable.resize_size_lt_capacity [BEq α] [Hashable α] [LawfulBEq α]
      (t : RHTable α β) (hWF : t.WF) :
      (t.resize).size < (t.resize).capacity
  ```
- **Proof strategy**: After resize, capacity = 2 * capacity, size = original size.
  Since `size ≤ capacity` (from WF), `size < 2 * capacity = resize.capacity`.
- **Risk**: Low
- **Dependencies**: None

#### U4-R: `erase_preserves_size_lt_capacity` (already exists!)

- **File**: `RobinHood/Bridge.lean:425-435`
- **Status**: DONE — `RHTable.erase_size_lt_capacity` already proven
- **Signature**: `(t : RHTable α β) (k : α) (hSizeLt : t.size < t.capacity) : (t.erase k).size < (t.erase k).capacity`
- **Work required**: None

#### U5-R: `filter_preserves_size_lt_capacity` (already exists!)

- **File**: `RobinHood/Bridge.lean:469-489`
- **Status**: DONE — `RHTable.filter_size_lt_capacity` already proven
- **Work required**: None

#### U6-R: Update `invExt` definition

- **File**: `RobinHood/Invariant/Preservation.lean:447-448`
- **Scope**: Small (~5 lines for definition change)
- **Change**:
  ```lean
  -- Before:
  def RHTable.invExt [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
    t.WF ∧ t.distCorrect ∧ t.noDupKeys ∧ t.probeChainDominant

  -- After:
  def RHTable.invExt [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
    t.WF ∧ t.distCorrect ∧ t.noDupKeys ∧ t.probeChainDominant ∧ t.size < t.capacity
  ```
- **Cascade impact**: Every theorem that constructs or destructs `invExt` must be updated.
  This is the highest-impact change. See Phase 2 for details.
- **Risk**: Medium — large cascade, but each individual change is mechanical
- **Dependencies**: U1-R, U3-R (preservation proofs must exist before we can update
  composite preservation theorems)

#### U7-R: `invExt_implies_size_lt_capacity` derivation lemma

- **File**: `RobinHood/Invariant/Preservation.lean` (new, after invExt definition)
- **Scope**: XS (~5 lines)
- **Statement**:
  ```lean
  theorem RHTable.invExt_implies_size_lt_capacity [BEq α] [Hashable α]
      (t : RHTable α β) (hExt : t.invExt) :
      t.size < t.capacity :=
    hExt.2.2.2.2
  ```
- **Purpose**: Provides a named extraction for `size < capacity` from `invExt`, avoiding
  raw tuple projection `hExt.2.2.2.2` at call sites.
- **Risk**: None
- **Dependencies**: U6-R

---

### Phase 2: Core Refactor — Update Composite Theorems (V3-B Layer 0-1)

With `size < capacity` now part of `invExt`, every theorem that **constructs** an
`invExt` proof (by providing all 5 conjuncts) or **destructs** one (by projecting
components) must be updated. This phase handles the RobinHood module and its
immediate wrappers.

#### U8: Update `empty_invExt`

- **File**: `RobinHood/Invariant/Preservation.lean:451-456`
- **Scope**: XS (~2 lines)
- **Change**: Add 5th conjunct to the proof tuple: `RHTable.empty_size_lt_capacity cap hPos`
- **Before**: `⟨..wf, ..distCorrect, ..noDupKeys, ..probeChainDominant⟩`
- **After**: `⟨..wf, ..distCorrect, ..noDupKeys, ..probeChainDominant, RHTable.empty_size_lt_capacity cap hPos⟩`
- **Risk**: None
- **Dependencies**: U1-R, U6-R

#### U9: Update `insert_preserves_invExt`

- **File**: `RobinHood/Invariant/Preservation.lean:2394-2400`
- **Scope**: Small (~10 lines)
- **Change**: The existing proof constructs a 4-tuple. It must now construct a 5-tuple,
  adding `(t.insert k v).size < (t.insert k v).capacity`. This requires proving that
  `insert` preserves `size < capacity`.
- **Strategy**: Extract `hSizeLt := hExt.2.2.2.2` (old size < capacity) and use
  `insert_size_lt_capacity` if `cap ≥ 4`, OR prove a new variant. Since `insert`
  auto-resizes, the argument is: after insert, if resize happened, capacity doubled
  (so size < cap); if no resize, `size * 4 < cap * 3` implies `size + 1 < cap` for
  cap ≥ 4. The existing `insert_size_lt_capacity` theorem requires `hCapGe4 : 4 ≤ t.capacity`.
  This is NOT in `invExt` (per Option B decision). So we need a weaker preservation
  proof that doesn't require `cap ≥ 4`.

  **Sub-analysis**: Can we prove `insert_preserves_size_lt_capacity` without `cap ≥ 4`?
  - Resize branch: capacity doubles. `size ≤ cap` (from WF). After resize, `cap' = 2*cap`.
    After insertNoResize, `size' ≤ size + 1 ≤ cap + 1`. Is `cap + 1 < 2*cap`? Yes, for
    `cap ≥ 2`. `cap ≥ 2` follows from `cap > 0` (WF) and the fact that resize doubles
    a cap ≥ 1 to ≥ 2. But if `cap = 1` initially, after resize `cap' = 2`, `size' ≤ 2`.
    `2 < 2` is false! So resize from cap=1 could violate the invariant.

    Actually, let's re-check: `resize` re-inserts all entries into a table of `2*cap`.
    The original `size ≤ cap` (from WF). After resize, `resize.size = size` and
    `resize.capacity = 2*cap`. Then `insertNoResize` makes `size' ≤ size + 1 ≤ cap + 1`.
    Is `cap + 1 < 2*cap`? Iff `1 < cap`, i.e., `cap ≥ 2`. So for `cap = 1`:
    `size ≤ 1`, after resize `cap' = 2`, after insert `size' ≤ 2 = cap'`. NOT strict.

  **Resolution**: For `cap ≥ 2` (which covers all kernel tables since they start at 16),
  insert preserves `size < capacity`. For `cap = 1`, it does not. Since `cap ≥ 4` is
  always true in the kernel, and adding it to the proof is the existing pattern, we
  accept this: the `insert_preserves_invExt` proof will need either:

  (a) To strengthen `invExt` to include `cap ≥ 4` (Option A from Section 2.3 — rejected), or
  (b) To prove insert preservation of `size < capacity` only under `hCapGe4`, making
      `insert_preserves_invExt` require `hCapGe4` too.
  (c) To observe that the existing `insert_preserves_invExt` does NOT need `hCapGe4`
      because it doesn't currently prove `size < capacity`. Adding `size < capacity`
      to `invExt` forces us to prove it in `insert_preserves_invExt`, which requires
      `cap ≥ 4`.

  **This is a fundamental tension**: adding `size < capacity` to `invExt` means
  `insert_preserves_invExt` must prove `(t.insert k v).size < (t.insert k v).capacity`,
  which requires `4 ≤ t.capacity`. Currently `insert_preserves_invExt` has signature
  `(t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) : (t.insert k v).invExt`.
  If `invExt` includes `size < capacity`, the proof must establish the new conjunct,
  which needs `cap ≥ 4`.

  **Three resolution paths**:

  **Path 1**: Accept `insert_preserves_invExt` gains `(hCapGe4 : 4 ≤ t.capacity)`.
  This propagates to all insert call sites, adding a new hypothesis. BUT all insert
  call sites already pass `hCapGe4` to `insert_size_lt_capacity`, so this is not a
  new burden — it's just moving it to a different theorem.

  **Path 2**: Include `4 ≤ t.capacity` in `invExt` (Option A). Then
  `insert_preserves_invExt` can extract it from `hExt`. This eliminates `hCapGe4`
  from all call sites. Cost: proving `4 ≤ capacity` is preserved by all operations
  (trivial: capacity only grows via resize, which doubles).

  **Path 3**: Prove insert preservation using the `loadFactorBounded` approach from
  the resize condition. In the no-resize branch, `size * 4 < cap * 3` implies
  `size < cap * 3/4`. `(size+1) < cap` iff `size < cap - 1`, which follows from
  `size < cap * 3/4` when `cap * 3/4 ≤ cap - 1`, i.e., `cap ≥ 4`.

  **FINAL DECISION**: **Path 2** — Include `4 ≤ t.capacity` in `invExt`.

  Rationale: This is the cleanest long-term solution. Every kernel RHTable has
  `cap ≥ 16`. Empty tables are constructed with `cap ≥ 16`. Resize doubles capacity.
  The `cap ≥ 4` property is preserved by all operations. Adding it to `invExt`
  eliminates both `hSize` from erase AND `hCapGe4` from insert at every call site.

  **REVISED `invExt` definition**:
  ```lean
  def RHTable.invExt [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
    t.WF ∧ t.distCorrect ∧ t.noDupKeys ∧ t.probeChainDominant ∧
    t.size < t.capacity ∧ 4 ≤ t.capacity
  ```

  This subsumes:
  - `hSize : t.size < t.capacity` → `hExt.2.2.2.2.1`
  - `hCapGe4 : 4 ≤ t.capacity` → `hExt.2.2.2.2.2`

- **Updated proof**: Extract old `hSizeLt` and `hCapGe4` from `hExt`, apply
  `insert_size_lt_capacity` for size conjunct, prove `4 ≤ (t.insert k v).capacity`
  (capacity only grows, so trivial).
- **Risk**: Low — mechanical update
- **Dependencies**: U6-R (revised), U7-R

#### U10: Update `erase_preserves_invExt` — Remove `hSize` parameter

- **File**: `RobinHood/Invariant/Preservation.lean:2406-2412`
- **Scope**: Small (~5 lines)
- **Change**:
  ```lean
  -- Before:
  theorem RHTable.erase_preserves_invExt [BEq α] [Hashable α] [LawfulBEq α]
      (t : RHTable α β) (k : α) (hExt : t.invExt) (hSize : t.size < t.capacity) :
      (t.erase k).invExt

  -- After:
  theorem RHTable.erase_preserves_invExt [BEq α] [Hashable α] [LawfulBEq α]
      (t : RHTable α β) (k : α) (hExt : t.invExt) :
      (t.erase k).invExt
  ```
- **Proof body**: Extract `hSize := hExt.2.2.2.2.1` for the probeChainDominant call.
  Add `erase_size_lt_capacity t k hSize` for the size conjunct. Add
  `hExt.2.2.2.2.2` (capacity unchanged by erase, so `cap ≥ 4` trivially preserved)
  for the cap conjunct.
- **Risk**: Low
- **Dependencies**: U6-R (revised), U7-R

#### U11: Update `resize_preserves_invariant`

- **File**: `RobinHood/Invariant/Preservation.lean:2414-2420`
- **Scope**: Small (~5 lines)
- **Change**: Add 5th and 6th conjuncts for `size < capacity` and `4 ≤ capacity`
  after resize (capacity doubles, size unchanged).
- **Risk**: None
- **Dependencies**: U3-R, U6-R (revised)

#### U12: Update `RHSet.erase_preserves_invExt` wrapper

- **File**: `RobinHood/Set.lean:126-130`
- **Scope**: XS (~3 lines)
- **Change**: Remove `hSize` parameter from signature and call:
  ```lean
  -- Before:
  theorem RHSet.erase_preserves_invExt [BEq κ] [Hashable κ] [LawfulBEq κ]
      (s : RHSet κ) (k : κ) (hExt : s.table.invExt)
      (hSize : s.table.size < s.table.capacity) :
      (s.erase k).table.invExt :=
    s.table.erase_preserves_invExt k hExt hSize

  -- After:
  theorem RHSet.erase_preserves_invExt [BEq κ] [Hashable κ] [LawfulBEq κ]
      (s : RHSet κ) (k : κ) (hExt : s.table.invExt) :
      (s.erase k).table.invExt :=
    s.table.erase_preserves_invExt k hExt
  ```
- **Risk**: None
- **Dependencies**: U10

#### U13: Update `Prelude.lean` re-export

- **File**: `Prelude.lean:928-932`
- **Scope**: XS (~3 lines)
- **Change**: Remove `hSize` from `RHTable_erase_preserves_invExt` signature and call
- **Risk**: None
- **Dependencies**: U10

#### U14: Update `RHSet.insert_preserves_invExt` (if needed)

- **File**: `RobinHood/Set.lean:120-123`
- **Scope**: XS
- **Note**: `RHSet.insert_preserves_invExt` calls `t.insert_preserves_invExt`. If
  `insert_preserves_invExt` gains a `hCapGe4` parameter (Path 1), this wrapper must
  propagate it. Under Path 2, `hCapGe4` is in `invExt` and no change needed.
- **Risk**: None
- **Dependencies**: U9

#### U15: Update `empty_invExt'` and other constructors

- **File**: `RobinHood/Invariant/Preservation.lean`
- **Scope**: Small
- **Note**: `empty_invExt' cap hPos` constructs `invExt` for empty tables. Must add
  `size < cap` and `4 ≤ cap` conjuncts. The `4 ≤ cap` requirement means
  `empty_invExt' 1 _` would fail — but all kernel uses pass cap = 16.
  Need to update signature to require `4 ≤ cap`.
- **Risk**: Low — check all call sites of `empty_invExt'`
- **Dependencies**: U6-R (revised)

---

### Phase 3: Call Site Migration (V3-B Layers 2-6)

With `erase_preserves_invExt` now taking only `(hExt : t.invExt)`, and
`insert_preserves_invExt` now taking only `(hExt : t.invExt)` (both `hSize` and
`hCapGe4` subsumed), every downstream call site that passed these hypotheses must
be updated to remove them.

**Execution order**: Files are ordered by import dependency. Leaf modules first,
then modules that import them. Within each file, changes are independent.

#### U16: Update `Model/Object/Structures.lean` — `remove_slotsUnique` (line 647)

- **Scope**: XS
- **Change**: Remove `hUniq.2.1` argument from `erase_preserves_invExt` call
- **Before**: `cn.slots.erase_preserves_invExt slot hUniq.1 hUniq.2.1`
- **After**: `cn.slots.erase_preserves_invExt slot hUniq.1`
- **Impact on `slotsUnique`**: The `slotsUnique` definition
  (`cn.slots.invExt ∧ cn.slots.size < cn.slots.capacity ∧ 4 ≤ cn.slots.capacity`)
  can now be **simplified**. Since `invExt` includes both `size < capacity` and
  `4 ≤ capacity`, `slotsUnique` is redundant with `invExt`. However, changing
  `slotsUnique` cascades to all CNode callers — defer to a separate sub-unit (U16b).
- **Dependencies**: U10

#### U16b: Simplify `CNode.slotsUnique` definition

- **File**: `Model/Object/Structures.lean:532-533`
- **Scope**: Medium (~50 lines of cascade updates)
- **Change**:
  ```lean
  -- Before:
  def slotsUnique (cn : CNode) : Prop :=
    cn.slots.invExt ∧ cn.slots.size < cn.slots.capacity ∧ 4 ≤ cn.slots.capacity

  -- After:
  def slotsUnique (cn : CNode) : Prop :=
    cn.slots.invExt
  ```
- **Cascade**: Every theorem that constructs `slotsUnique` (by providing the 3-tuple)
  or destructs it (by projecting `.1`, `.2.1`, `.2.2`) must be updated:
  - `insert_slotsUnique` (L627-639): Remove `insert_size_lt_capacity` and
    `insert_capacity_ge4` calls from the proof; just return `insert_preserves_invExt`
  - `remove_slotsUnique` (L643-650): Same — just `erase_preserves_invExt`
  - `revokeTargetLocal_slotsUnique` (L654-676): Same — just `filter_preserves_invExt`
  - `lookup_remove_eq_none` (L539-543): Uses `hUniq.1` → now just `hUniq`
  - All callers that reference `hUniq.2.1` or `hUniq.2.2` must be updated
- **Risk**: Medium — touches many proof terms, but each is a simplification (removing
  conjuncts, not adding them)
- **Decision**: Execute U16b IF the cascade is tractable. If it involves too many files
  beyond `Structures.lean`, defer to a separate unit and keep `slotsUnique` as-is with
  the redundant conjuncts. The redundancy is harmless.
- **Dependencies**: U9, U10, U6-R (revised)

#### U17: Update `Model/Object/Structures.lean` — CDT fold helpers (lines 1287-1365)

- **File**: `Model/Object/Structures.lean`
- **Scope**: Small (~20 lines across 4 theorems)
- **Affected theorems**:
  - `foldl_erase_preserves` (L1287): Remove `hSize` param + arg
  - `foldl_erase_none` (L1306): Remove `hSize` param + arg
  - `foldl_erase_mem` (L1326): Remove `hSize` param + arg
  - `foldl_erase_invExt` (L1365): Remove `hS` param + arg; also remove
    `m.erase_size_lt_capacity x hS` since `invExt` now carries size bound
- **Cascade**: These are private helpers used by `removeNode_childMapConsistent`.
  Check if removing `hSize` from their signatures requires changes to callers.
- **Risk**: Low
- **Dependencies**: U10

#### U18: Update `Model/Object/Structures.lean` — `removeNode_childMapConsistent` (lines 1474-1510)

- **File**: `Model/Object/Structures.lean`
- **Scope**: Small (~15 lines)
- **Changes**:
  - Remove `hSizeCM` parameter from theorem signature
  - Remove `hEraseSize` derivation (L1475)
  - Remove `hSizeCM` and `hEraseSize` arguments from `erase_preserves_invExt` calls
    (L1474, L1494, L1510)
- **Risk**: Low
- **Dependencies**: U10, U17

#### U19: Update `Model/State.lean` — `storeObject_preserves_invariant` (line 1293)

- **File**: `Model/State.lean:1260-1301`
- **Scope**: XS (~3 lines)
- **Change**: Remove `hAsidSize` parameter from theorem signature and from the
  `erase_preserves_invExt` call at L1293
- **Cascade**: All callers of `storeObject_preserves_invariant` that passed
  `hAsidSize` must remove that argument. Search for callers.
- **Risk**: Low
- **Dependencies**: U10

#### U20: Update `Model/Builder.lean` — `deleteObject` (lines 240-256)

- **File**: `Model/Builder.lean:238-300`
- **Scope**: Small (~10 lines)
- **Changes**:
  - Remove `hObjSize` and `hTypesSize` parameters from `deleteObject` signature (L240-241)
  - Remove these arguments from `erase_preserves_invExt` calls (L254, L256)
  - Also remove from `getElem?_erase_ne` calls (L270, L282, L297-298) — these
    also take `hSize`, which is separate from `erase_preserves_invExt` but uses the
    same parameter. Check if `getElem?_erase_ne` also needs `hSize` removed.
- **Cascade**: All callers of `deleteObject` that passed `hObjSize`/`hTypesSize`
  must remove those arguments. Search for callers.
- **Risk**: Low
- **Dependencies**: U10

#### U21: Update `Scheduler/RunQueue.lean` — `removeThread` (lines 233-251)

- **File**: `Scheduler/RunQueue.lean:210-280`
- **Scope**: Small (~10 lines)
- **Changes**:
  - L233: Remove `rq.mem_sizeOk` from `RHSet.erase_preserves_invExt` call
  - L248: Remove `rq.byPrio_sizeOk` from `erase_preserves_invExt` call
  - L250-251: Remove `rq.threadPrio_sizeOk` from `erase_preserves_invExt` call
- **Structural field analysis**: The `mem_sizeOk`, `byPrio_sizeOk`, `threadPrio_sizeOk`
  fields on `RunQueue` were needed for two purposes:
  1. Feeding `erase_preserves_invExt` (now eliminated)
  2. Feeding `insert_size_lt_capacity` (now eliminated, since `invExt` includes `size < cap`)

  Similarly, `mem_capGe4`, `byPrio_capGe4`, `threadPrio_capGe4` were needed for
  `insert_size_lt_capacity` (now eliminated).

  **All 6 fields are now redundant** with `invExt`. They can be removed from the
  `RunQueue` structure, simplifying it significantly. However, removing structure fields
  is a larger cascade — all constructors and field accesses must be updated.
- **Decision**: Remove the 6 redundant fields in U21b (separate sub-unit).
- **Risk**: Low for U21 (just remove args); Medium for U21b (structure change)
- **Dependencies**: U10, U12

#### U21b: Remove redundant `RunQueue` fields (optional, high-value)

- **File**: `Scheduler/RunQueue.lean`
- **Scope**: Medium (~80 lines)
- **Fields to remove**:
  - `mem_sizeOk : membership.table.size < membership.table.capacity`
  - `byPrio_sizeOk : byPriority.size < byPriority.capacity`
  - `threadPrio_sizeOk : threadPriority.size < threadPriority.capacity`
  - `mem_capGe4 : 4 ≤ membership.table.capacity`
  - `byPrio_capGe4 : 4 ≤ byPriority.capacity`
  - `threadPrio_capGe4 : 4 ≤ threadPriority.capacity`
- **Justification**: All 6 properties are now derivable from `mem_invExt`,
  `byPrio_invExt`, and `threadPrio_invExt` (since `invExt` includes both
  `size < capacity` and `4 ≤ capacity`).
- **Cascade**: `RunQueue.empty`, `RunQueue.insert`, `RunQueue.remove` proofs
  all construct these fields — those lines can be deleted. Any external code
  that reads these fields must be updated to extract from `invExt` instead.
- **Risk**: Medium — structure modification has wide cascade
- **Dependencies**: U21

#### U22: Update `Capability/Invariant/Preservation.lean` (3 sites)

- **File**: `Capability/Invariant/Preservation.lean`
- **Scope**: Small (~15 lines across 3 sites)
- **Changes**:
  - L359-362: Remove `hSzRef` derivation and `hSzRef` arg from `erase_preserves_invExt`.
    Also remove `erase_size_lt_capacity` call (L362) that maintained `hNodeSlotSize`
    — this size bound is now in `invExt`, so `erase_preserves_invExt` returns it.
  - L365-368: Remove `hNodeSlotSize` parameter from `cspaceDeleteSlot_preserves_cdtNodeSlot`
  - L799: Remove `hSzDel` arg from `erase_preserves_invExt` call
  - L1127: Remove `hNSSzDel` arg from `erase_preserves_invExt` call
- **Cascade**: Functions that call `cspaceDeleteSlot_preserves_cdtNodeSlot` and pass
  `hNodeSlotSize` must be updated to remove that argument. These are in the same file
  (capability preservation proofs are self-contained).
- **Risk**: Low
- **Dependencies**: U10

#### U23: Update `RobinHood/Invariant/Lookup.lean` — `get_after_erase_ne` (line 1956)

- **File**: `RobinHood/Invariant/Lookup.lean:1951-2050`
- **Scope**: XS (~3 lines)
- **Change**: Remove `hSize` parameter from `get_after_erase_ne` signature and from
  the `erase_preserves_invExt` call at L1956
- **Cascade**: Check all callers of `get_after_erase_ne` — they must remove the
  `hSize` argument they currently pass.
- **Risk**: Low
- **Dependencies**: U10

---

### Phase 4: Validation & Documentation

#### U24: Build every modified module individually

- **Scope**: XS (scripted)
- **Command**: For each modified `.lean` file, run:
  ```bash
  source ~/.elan/env && lake build <Module.Path>
  ```
- **Modules to build** (in dependency order):
  1. `SeLe4n.Kernel.RobinHood.Invariant.Defs`
  2. `SeLe4n.Kernel.RobinHood.Invariant.Preservation`
  3. `SeLe4n.Kernel.RobinHood.Invariant.Lookup`
  4. `SeLe4n.Kernel.RobinHood.Set`
  5. `SeLe4n.Kernel.RobinHood.Bridge`
  6. `SeLe4n.Prelude`
  7. `SeLe4n.Model.Object.Structures`
  8. `SeLe4n.Model.State`
  9. `SeLe4n.Model.IntermediateState`
  10. `SeLe4n.Model.Builder`
  11. `SeLe4n.Kernel.Scheduler.RunQueue`
  12. `SeLe4n.Kernel.Capability.Invariant.Preservation`
  13. `SeLe4n.Kernel.API`
- **Gate**: All builds must succeed with zero `sorry`
- **Dependencies**: U8-U23

#### U25: Run `test_full.sh`

- **Scope**: XS (automated)
- **Gate**: All tiers (0-3) green
- **Dependencies**: U24

#### U26: Update documentation

- **Scope**: Small (~30 lines across multiple docs)
- **Files to update**:
  1. `docs/gitbook/12-proof-and-invariant-map.md`: Update `invExt` definition description
     to include `size < capacity` and `4 ≤ capacity` conjuncts
  2. `docs/codebase_map.json`: Regenerate (or manually update `erase_preserves_invExt`
     entries to reflect removed `hSize` parameter)
  3. `CHANGELOG.md`: Add V3-A/V3-B entry documenting the migration
  4. `docs/WORKSTREAM_HISTORY.md`: Mark V3-A and V3-B as COMPLETE
  5. `docs/audits/AUDIT_v0.21.7_WORKSTREAM_PLAN.md`: Update V3-A/V3-B status to DONE
- **Dependencies**: U25

---

## 6. Execution Strategy

### 6.1 Recommended Commit Sequence

The migration should be committed in **3 focused commits** to maintain bisectability:

**Commit 1: Foundation** (U1-R through U7-R, U8-U11, U14-U15)
- Add `size < capacity` and `4 ≤ capacity` to `invExt`
- Update all composite preservation proofs (empty, insert, erase, resize, filter)
- Add `invExt_implies_size_lt_capacity` lemma
- Remove `hSize` from `erase_preserves_invExt` core theorem
- Update `resize_preserves_invariant`
- Gate: `lake build SeLe4n.Kernel.RobinHood.Invariant.Preservation` succeeds

**Commit 2: Call site migration** (U12-U13, U16-U23)
- Update all 23 downstream call sites across 8 files
- Remove redundant parameters from function signatures
- Simplify `CNode.slotsUnique` if tractable (U16b)
- Remove redundant `RunQueue` fields if tractable (U21b)
- Gate: `lake build` (full) succeeds; `test_full.sh` green

**Commit 3: Documentation** (U26)
- Update GitBook, codebase_map, CHANGELOG, workstream history
- Gate: `test_full.sh` green (includes doc-anchor checks)

### 6.2 Parallelization Opportunities

Within Phase 3, call site updates across different files are **independent** and can
be done in parallel:

```
U16/U16b (Structures.lean)  ──┐
U17/U18 (Structures.lean)    │  ← same file, sequential
U19 (State.lean)             ──┤
U20 (Builder.lean)           ──┼── all independent, can parallelize
U21/U21b (RunQueue.lean)     ──┤
U22 (Capability/Preservation)─┤
U23 (Lookup.lean)            ──┘
```

**Warning**: Structures.lean changes (U16-U18) must be done sequentially within that
file since they share context. All other files are independent.

### 6.3 Risk Mitigation

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| `invExt` cascade breaks unexpected callers | Medium | High | Build every module before committing; search for `invExt` across entire codebase |
| `empty_invExt'` now requires `4 ≤ cap` | Low | Medium | All kernel uses pass cap=16; grep for `empty_invExt'` to verify |
| `slotsUnique` simplification cascades too far | Medium | Low | Defer U16b if cascade exceeds 5 files; keep redundant definition |
| `RunQueue` field removal cascades too far | Medium | Low | Defer U21b if cascade exceeds RunQueue.lean + 2 files |
| Proof timeouts after `invExt` expansion | Low | Medium | Monitor `maxHeartbeats`; the extra conjunct adds minimal proof term size |

### 6.4 Rollback Plan

If the migration encounters blocking issues (e.g., a preservation proof that cannot
be completed without `sorry`):

1. **Fallback to Option B**: Remove `4 ≤ capacity` from `invExt`, keep only
   `size < capacity`. This still eliminates `hSize` from erase but requires
   `hCapGe4` on insert. Smaller scope, lower risk.
2. **Fallback to Option C**: Don't modify `invExt` at all. Instead, add a standalone
   `invExt_implies_size_lt_capacity` lemma that takes `loadFactorBounded` as a
   separate hypothesis. Least invasive but doesn't solve the root cause.

---

## 7. Summary

| Metric | Value |
|--------|-------|
| **Total units of work** | 26 (U1-R through U7-R, U8-U26) |
| **New Lean code** | ~80 lines (preservation proofs, lemma) |
| **Modified Lean code** | ~200 lines (signature changes, arg removal) |
| **Deleted Lean code** | ~60 lines (redundant hypotheses, derivations, fields) |
| **Files modified** | 12 Lean files + 5 documentation files |
| **Call sites updated** | 23 (erase) + ~15 (insert `hCapGe4`) = ~38 total |
| **Structural simplifications** | `CNode.slotsUnique` (3→1 conjuncts), `RunQueue` (6 fields removable) |
| **Risk level** | Medium (large cascade, but each change is mechanical) |
| **Estimated scope** | ~350 net lines changed |
| **Dependencies** | V3-A (foundation) must complete before V3-B (migration) |
| **Blocks** | V7-A/V7-B (Performance phase depends on RobinHood invariant changes) |

### Key Insight

The original V3-B task description proposed adding `loadFactorBounded` to `invExt`.
Detailed analysis revealed that `loadFactorBounded` (`size * 4 ≤ cap * 3`) is **not**
preserved by `insert` — it is a pre-resize trigger condition, not a post-operation
invariant. The correct invariant to add is `size < capacity ∧ 4 ≤ capacity`, which IS
preserved by all operations and subsumes both the `hSize` parameter on erase AND the
`hCapGe4` parameter on insert. This doubles the simplification benefit of the migration.
