# V3-B Migration Plan — `invExtK` Bundle & `hSize`/`hCapGe4` Elimination

**Created**: 2026-03-26
**Revised**: 2026-03-26 (v2 — design correction, expanded sub-units)
**Baseline version**: 0.22.0
**Parent workstream**: WS-V Phase V3 (Proof Chain Hardening), sub-tasks V3-A + V3-B
**Finding**: H-RH-1 (HIGH) — `erase_preserves_invExt` requires separate `hSize`
hypothesis not derivable from `invExt`
**Constraint**: Zero `sorry`/`axiom` in production proof surface
**Gate**: `lake build` succeeds for every modified module; `test_full.sh` green

---

## 1. Problem Statement

### 1.1 The Architectural Gap

The Robin Hood hash table's extended invariant bundle (`invExt`) is a 4-conjunct
proposition that is preserved by all table operations:

```lean
-- SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean:447-448
def RHTable.invExt [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
  t.WF ∧ t.distCorrect ∧ t.noDupKeys ∧ t.probeChainDominant
```

Two key theorem families require a **separate** `hSize : t.size < t.capacity`
hypothesis that is not derivable from `invExt`:

```lean
-- Erase invariant preservation (Preservation.lean:2406)
theorem RHTable.erase_preserves_invExt ...
    (hExt : t.invExt) (hSize : t.size < t.capacity) : (t.erase k).invExt

-- Erase lookup correctness (Bridge.lean:134)
theorem RHTable.getElem?_erase_ne ...
    (hExt : t.invExt) (hSize : t.size < t.capacity) : (t.erase k).get? k' = t.get? k'
```

Yet every reachable table state satisfies `size < capacity` because `RHTable.insert`
resizes at 75% load (`size * 4 ≥ capacity * 3` triggers 2x resize). The `hSize`
parameter is architecturally blocked — callers must independently obtain and thread it.

### 1.2 Impact

**48+ call sites** across 12 files must independently obtain and pass `hSize` proofs:

- **23 sites** call `erase_preserves_invExt` (or wrappers `RHSet.erase_preserves_invExt`,
  `RHTable_erase_preserves_invExt`)
- **25+ sites** call `getElem?_erase_ne` (or wrappers `RHSet.contains_erase_ne`,
  `RHTable_getElem?_erase_ne`)
- **8 sites** call `insert_size_lt_capacity` with a separate `hCapGe4 : 4 ≤ t.capacity`

This creates:

- **Redundant structure fields**: `RunQueue` carries 6 fields (`mem_sizeOk`, `byPrio_sizeOk`,
  `threadPrio_sizeOk`, `mem_capGe4`, `byPrio_capGe4`, `threadPrio_capGe4`) solely to
  feed these hypotheses
- **Redundant definition conjuncts**: `CNode.slotsUnique` bundles
  `invExt ∧ size < capacity ∧ 4 ≤ capacity` — all three are independently threaded
- **Signature pollution**: Functions like `deleteObject`, `storeObject_preserves_invariant`,
  and `cspaceDeleteSlot_preserves_cdtNodeSlot` carry `hSize` parameters through their
  entire call chain
- **Proof maintenance burden**: Every new erase call site must discover and satisfy
  the `hSize` requirement by trial and error

---

## 2. Design Decision

### 2.1 Options Considered

| Option | Description | Pros | Cons |
|--------|------------|------|------|
| A: Extend `invExt` directly | Add `size < capacity ∧ 4 ≤ capacity` as 5th/6th conjuncts of `invExt` | Single bundle; automatic for all callers | **Breaks `insertNoResize_preserves_invExt`** — see §2.2 |
| **B: Create `invExtK` wrapper** | New kernel-level bundle: `invExt ∧ size < capacity ∧ 4 ≤ capacity` | Zero changes to internal proofs; clean layering | Two invariant names |
| C: Lemma only | Add `invExt_implies_size_lt_capacity` assuming `loadFactorBounded` as separate hypothesis | Minimal change | Still requires callers to track `loadFactorBounded` separately |
| D: Add `loadFactorBounded` to `invExt` | Add `size * 4 ≤ capacity * 3` as 5th conjunct | Spec-aligned | **`loadFactorBounded` is NOT preserved by `insert`** — see §2.3 |

### 2.2 Why Option A Fails: The `insertNoResize` Problem

Adding `size < capacity` to `invExt` breaks `insertNoResize_preserves_invExt`, which
has the signature:

```lean
theorem RHTable.insertNoResize_preserves_invExt
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insertNoResize k v).invExt
```

If `invExt` includes `size < capacity`, the proof must establish
`(t.insertNoResize k v).size < (t.insertNoResize k v).capacity`. When inserting a
**new key**, `size' = size + 1`. With only `size < capacity` (i.e., `size ≤ cap - 1`),
we get `size' ≤ cap`, which is NOT strictly less than `cap`. The theorem cannot prove
`size' < cap` without knowing that there is room for an additional entry beyond the
current occupancy.

This theorem is **actively used** in 10+ sites:
- Bridge.lean filter fold proofs (L459, 573, 650, 670, 778)
- Preservation.lean resize fold proofs (L1352, 1365)
- Lookup.lean insertNoResize correctness (L1489, 2074, 2102)

Adding a precondition like `hRoom : t.size + 1 < t.capacity` would cascade to all
these callers, requiring complex room-tracking proofs through fold iterations.

### 2.3 Why Option D Fails: `loadFactorBounded` Is Not Preserved by `insert`

The `loadFactorBounded` predicate (`size * 4 ≤ capacity * 3`) is a **resize trigger
condition**, not a post-operation invariant. After inserting into a table just below
the threshold:

```
cap = 5, size = 3:  3*4 = 12 < 5*3 = 15  → no resize
After insert:       4*4 = 16 > 5*3 = 15  → loadFactorBounded VIOLATED
```

The bound is restored only when the **next** insert triggers a resize. Therefore
`loadFactorBounded` cannot be added to `invExt`.

### 2.4 Selected Approach: Option B — Create `invExtK` Wrapper Bundle

The correct architecture is a **kernel-level wrapper** in Bridge.lean (the kernel-facing
API layer):

```lean
/-- Kernel-level extended invariant: includes size bounds needed by erase and insert.
    All kernel tables satisfy this. RobinHood internal proofs use `invExt` (unchanged). -/
def RHTable.invExtK [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
  t.invExt ∧ t.size < t.capacity ∧ 4 ≤ t.capacity
```

**Rationale**: This cleanly separates concerns:
- **`invExt`** (Preservation.lean): Data-structure invariant for arbitrary RHTables.
  Preserved by all operations including `insertNoResize`. Used by internal proofs.
- **`invExtK`** (Bridge.lean): Kernel-level invariant asserting the table was constructed
  through the public API (`empty` → `insert`/`erase`/`filter`). Subsumes `hSize` and
  `hCapGe4`. Used by all kernel code.

**Key advantages over Option A**:
- **Zero changes** to `invExt` definition, constructors, or destructors
- **Zero changes** to Preservation.lean (~2300 lines), Lookup.lean (~1200 lines)
- **Zero changes** to invExt projection paths (`.1`, `.2.1`, `.2.2.1`, `.2.2.2`)
- **Zero risk** to `insertNoResize_preserves_invExt` or filter/resize fold proofs
- New wrapper theorems are **trivial compositions** of existing theorems
- `loadFactorBounded` and its theorems remain useful as specification documentation

**Architecture diagram**:
```
┌──────────────────────────────────────────┐
│  Kernel Code (RunQueue, Builder, Cap,    │
│  VSpace, Lifecycle, Service, IPC)        │
│  Uses: invExtK (no separate hSize/hCap)  │
└────────────────┬─────────────────────────┘
                 │
    ┌────────────▼────────────────────────┐
    │  Bridge.lean — Kernel API Layer     │
    │  Defines: invExtK = invExt ∧ ...    │
    │  Provides: _K wrapper theorems      │
    │  (erase_preserves_invExtK, etc.)    │
    └────────────┬────────────────────────┘
                 │ composes
    ┌────────────▼────────────────────────┐
    │  Invariant/ — Internal Proofs       │
    │  Uses: invExt (UNCHANGED)           │
    │  (Preservation.lean, Lookup.lean)   │
    └─────────────────────────────────────┘
```

---

## 3. Complete Affected Site Inventory


### 3.1 Category A: `erase_preserves_invExt` Call Sites (15 kernel-facing sites)

Sites that call `erase_preserves_invExt` or its wrappers `RHSet.erase_preserves_invExt`,
`RHTable_erase_preserves_invExt`, passing an explicit `hSize` hypothesis:

| # | File | Line | Call Pattern | `hSize` Source |
|---|------|------|-------------|----------------|
| A1 | Scheduler/RunQueue.lean | 233 | `RHSet.erase_preserves_invExt rq.membership tid rq.mem_invExt rq.mem_sizeOk` | `rq.mem_sizeOk` field |
| A2 | Scheduler/RunQueue.lean | 248 | `rq.byPriority.erase_preserves_invExt p rq.byPrio_invExt rq.byPrio_sizeOk` | `rq.byPrio_sizeOk` field |
| A3 | Scheduler/RunQueue.lean | 250 | `rq.threadPriority.erase_preserves_invExt tid rq.threadPrio_invExt rq.threadPrio_sizeOk` | `rq.threadPrio_sizeOk` field |
| A4 | Capability/Invariant/Preservation.lean | 361 | `stRef.cdtNodeSlot.erase_preserves_invExt origNode hInvRef hSzRef` | `hSzRef` param |
| A5 | Capability/Invariant/Preservation.lean | 799 | `stDel.cdtNodeSlot.erase_preserves_invExt origNode hInvDel hSzDel` | `hSzDel` param |
| A6 | Capability/Invariant/Preservation.lean | 1127 | `stDel.cdtNodeSlot.erase_preserves_invExt origNode hNSInvDel hNSSzDel` | `hNSSzDel` param |
| A7 | Model/Builder.lean | 254 | `RHTable.erase_preserves_invExt _ _ h.1 hObjSize` | `hObjSize` param |
| A8 | Model/Builder.lean | 256 | `RHTable.erase_preserves_invExt _ _ h.2.2.2.2.2.1 hTypesSize` | `hTypesSize` param |
| A9 | Model/State.lean | 1293 | `RHTable.erase_preserves_invExt st.asidTable r.asid hAsid hAsidSize` | `hAsidSize` param |
| A10 | Model/Object/Structures.lean | 647 | `cn.slots.erase_preserves_invExt slot hUniq.1 hUniq.2.1` | `hUniq.2.1` (slotsUnique) |
| A11 | Model/Object/Structures.lean | 1287 | `m.erase_preserves_invExt x hExt hSize` | `hSize` param |
| A12 | Model/Object/Structures.lean | 1306 | `m.erase_preserves_invExt x hExt hSize` | `hSize` param |
| A13 | Model/Object/Structures.lean | 1326 | `m.erase_preserves_invExt x hExt hSize` | `hSize` param |
| A14 | Model/Object/Structures.lean | 1365 | `m.erase_preserves_invExt x hE hS` | `hS` param |
| A15 | Model/Object/Structures.lean | 1474 | `cdt.childMap.erase_preserves_invExt node hExt hSizeCM` | `hSizeCM` param |
| A16 | Model/Object/Structures.lean | 1494 | `(cdt.childMap.erase node).erase_preserves_invExt p hEraseExt hEraseSize` | `hEraseSize` (derived) |
| A17 | Model/Object/Structures.lean | 1510 | `(cdt.childMap.erase node).erase_preserves_invExt p hEraseExt hEraseSize` | `hEraseSize` (derived) |

**Internal sites** (NOT migrated — they compose the wrapper theorems):

| # | File | Line | Role |
|---|------|------|------|
| I1 | RobinHood/Invariant/Lookup.lean | 1956 | Used inside `get_after_erase_ne` — feeds `getElem?_erase_ne` |
| I2 | RobinHood/Set.lean | 130 | Body of `RHSet.erase_preserves_invExt` wrapper |
| I3 | Prelude.lean | 932 | Body of `RHTable_erase_preserves_invExt` re-export |

### 3.2 Category B: `getElem?_erase_ne` / `contains_erase_ne` Call Sites (32 kernel-facing sites)

Sites that call `getElem?_erase_ne` or wrapper `RHSet.contains_erase_ne`/
`RHTable_getElem?_erase_ne`, passing `hExt` and `hSize`:

| # | File | Line | Call Pattern | `hSize` Source |
|---|------|------|-------------|----------------|
| B1 | Scheduler/RunQueue.lean | 218 | `RHSet.contains_erase_ne ... rq.mem_invExt rq.mem_sizeOk` | `rq.mem_sizeOk` field |
| B2 | Scheduler/RunQueue.lean | 228 | `RHSet.contains_erase_ne ... rq.mem_invExt rq.mem_sizeOk` | `rq.mem_sizeOk` field |
| B3 | Scheduler/RunQueue.lean | 408 | `RHSet.contains_erase_ne ... rq.mem_invExt rq.mem_sizeOk` | `rq.mem_sizeOk` field |
| B4 | Scheduler/RunQueue.lean | 413 | `RHSet.contains_erase_ne ... rq.mem_invExt rq.mem_sizeOk` | `rq.mem_sizeOk` field |
| B5 | Scheduler/RunQueue.lean | 1011 | `RHSet.contains_erase_ne ... rq.mem_invExt rq.mem_sizeOk` | `rq.mem_sizeOk` field |
| B6 | Scheduler/RunQueue.lean | 1027 | `RHSet.contains_erase_ne ... rq.mem_invExt rq.mem_sizeOk` | `rq.mem_sizeOk` field |
| B7 | Scheduler/Invariant.lean | 448 | `RHTable.getElem?_erase_ne rq.threadPriority ... rq.threadPrio_invExt rq.threadPrio_sizeOk` | `rq.threadPrio_sizeOk` field |
| B8 | Scheduler/Invariant.lean | 450 | `RHSet.contains_erase_ne rq.membership ... rq.mem_invExt rq.mem_sizeOk` | `rq.mem_sizeOk` field |
| B9 | Scheduler/Invariant.lean | 462 | `RHSet.contains_erase_ne rq.membership ... rq.mem_invExt rq.mem_sizeOk` | `rq.mem_sizeOk` field |
| B10 | Scheduler/Invariant.lean | 465 | `RHTable.getElem?_erase_ne rq.threadPriority ... rq.threadPrio_invExt rq.threadPrio_sizeOk` | `rq.threadPrio_sizeOk` field |
| B11 | Scheduler/Operations/Preservation.lean | 2572 | `RHTable.getElem?_erase_ne ... threadPriority ...` | RunQueue field (transitive) |
| B12 | Capability/Invariant/Defs.lean | 679 | `RHTable.getElem?_erase_ne cn.slots slot s ... hUniq.1 hUniq.2.1` | `hUniq.2.1` (slotsUnique) |
| B13 | Architecture/VSpaceInvariant.lean | 269 | `RHTable.getElem?_erase_ne mappings vaddr v hBeq hExt hSize` | `hSize` param |
| B14 | Model/Builder.lean | 270 | `RHTable.getElem?_erase_ne ist.state.objects id oid hNe hObjInv hObjSize` | `hObjSize` param |
| B15 | Model/Builder.lean | 282 | `RHTable.getElem?_erase_ne ist.state.objects id oid hNe hObjInv hObjSize` | `hObjSize` param |
| B16 | Model/Builder.lean | 297 | `RHTable.getElem?_erase_ne _ _ _ hNe hObjTypesInv hTypesSize` | `hTypesSize` param |
| B17 | Model/Builder.lean | 298 | `RHTable.getElem?_erase_ne _ _ _ hNe hObjInv hObjSize` | `hObjSize` param |
| B18 | Model/Object/Structures.lean | 331 | `RHTable.getElem?_erase_ne root.mappings vaddr vaddr' ...` | VSpaceRoot param |
| B19 | Model/Object/Structures.lean | 758 | `RHTable.getElem?_erase_ne cn.slots slot slot' ...` | slotsUnique |
| B20 | Model/Object/Structures.lean | 1290 | `RHTable.getElem?_erase_ne m x k ... hExt hSize` | `hSize` param |
| B21 | Model/Object/Structures.lean | 1313 | `RHTable.getElem?_erase_ne m x k hxk hExt hSize` | `hSize` param |
| B22 | Model/Object/Structures.lean | 1383 | `RHTable.getElem?_erase_ne _ node child ... hExt hSize` | CDT helper param |
| B23 | Model/Object/Structures.lean | 1431 | `RHTable.getElem?_erase_ne _ node child ... hExt hSize` | CDT helper param |
| B24 | Model/Object/Structures.lean | 1499 | `RHTable.getElem?_erase_ne _ p node ... hEraseExt hEraseSize` | derived |
| B25 | Model/Object/Structures.lean | 1512 | `RHTable.getElem?_erase_ne _ p parent ... hEraseExt hEraseSize` | derived |
| B26 | Model/Object/Structures.lean | 1513 | `RHTable.getElem?_erase_ne _ node parent ... hExt hSizeCM` | `hSizeCM` param |
| B27 | Model/Object/Structures.lean | 1544 | `RHTable.getElem?_erase_ne _ node p ... hExt hSizeCM` | `hSizeCM` param |
| B28 | Model/Object/Structures.lean | 1566 | `RHTable.getElem?_erase_ne _ node parent ... hExt hSizeCM` | `hSizeCM` param |
| B29 | Model/Object/Structures.lean | 1587 | `RHTable.getElem?_erase_ne _ node parent ... hExt hSizeCM` | `hSizeCM` param |
| B30 | Model/Object/Structures.lean | 1646 | `RHTable.getElem?_erase_ne _ node p ... hExt hSizeCM` | `hSizeCM` param |
| B31 | Model/Object/Structures.lean | 1664 | `RHTable.getElem?_erase_ne _ p parent ... hEraseExt hEraseSize` | derived |
| B32 | Model/Object/Structures.lean | 1665 | `RHTable.getElem?_erase_ne _ node parent ... hExt hSizeCM` | `hSizeCM` param |
| B33 | Model/Object/Structures.lean | 1683 | `RHTable.getElem?_erase_ne _ node p ... hExt hSizeCM` | `hSizeCM` param |
| B34 | Model/Object/Structures.lean | 1689 | `RHTable.getElem?_erase_ne _ node parent ... hExt hSizeCM` | `hSizeCM` param |
| B35 | Model/Object/Structures.lean | 1693 | `RHTable.getElem?_erase_ne _ node parent ... hExt hSizeCM` | `hSizeCM` param |

**Internal sites** (NOT migrated):

| # | File | Line | Role |
|---|------|------|------|
| I4 | Prelude.lean | 856 | Body of `RHTable_getElem?_erase_ne` re-export |
| I5 | Prelude.lean | 882 | Body of second re-export variant |
| I6 | RobinHood/Set.lean | 117 | Body of `RHSet.contains_erase_ne` wrapper |
| I7 | RobinHood/Set.lean | 155 | Internal usage in `contains_erase` |

### 3.3 Category C: `insert_size_lt_capacity` Call Sites (7 kernel-facing sites)

Sites that call `insert_size_lt_capacity`, passing `hExt`, `hSizeLt`, and
`hCapGe4` as separate arguments:

| # | File | Line | Call Pattern | `hCapGe4` Source |
|---|------|------|-------------|------------------|
| C1 | Scheduler/RunQueue.lean | 159 | `rq.membership.table.insert_size_lt_capacity tid () rq.mem_invExt rq.mem_sizeOk rq.mem_capGe4` | `rq.mem_capGe4` field |
| C2 | Scheduler/RunQueue.lean | 161 | `rq.byPriority.insert_size_lt_capacity prio ... rq.byPrio_invExt rq.byPrio_sizeOk rq.byPrio_capGe4` | `rq.byPrio_capGe4` field |
| C3 | Scheduler/RunQueue.lean | 164 | `rq.threadPriority.insert_size_lt_capacity tid prio rq.threadPrio_invExt rq.threadPrio_sizeOk rq.threadPrio_capGe4` | `rq.threadPrio_capGe4` field |
| C4 | Scheduler/RunQueue.lean | 272 | `rq.byPriority.insert_size_lt_capacity p _ rq.byPrio_invExt rq.byPrio_sizeOk rq.byPrio_capGe4` | `rq.byPrio_capGe4` field |
| C5 | Scheduler/RunQueue.lean | 332 | `rq.byPriority.insert_size_lt_capacity prio bucket' rq.byPrio_invExt rq.byPrio_sizeOk rq.byPrio_capGe4` | `rq.byPrio_capGe4` field |
| C6 | Model/Object/Structures.lean | 632 | `cn.slots.insert_size_lt_capacity slot cap hUniq.1 hUniq.2.1 hUniq.2.2` | `hUniq.2.2` (slotsUnique) |
| C7 | Model/Builder.lean | 330 | `RHTable.insert_size_lt_capacity cn.slots slot cap hSU.1 hSU.2.1 hSU.2.2` | `hSU.2.2` (slotsUnique) |

**Internal site** (NOT migrated):

| # | File | Line | Role |
|---|------|------|------|
| I8 | RobinHood/Bridge.lean | 526 | Body of `ofList_size_lt_capacity` (internal fold proof) |

### 3.4 Category D: Structural Redundancy — Fields & Definitions to Simplify

#### D1: `RunQueue` Structure Fields (Scheduler/RunQueue.lean:34-45)

Six fields exist solely to feed `hSize` and `hCapGe4` to Categories A/B/C:

| Field | Type | Used By |
|-------|------|---------|
| `mem_sizeOk` | `membership.table.size < membership.table.capacity` | A1, B1-B6, B8-B9, C1 |
| `byPrio_sizeOk` | `byPriority.size < byPriority.capacity` | A2, C2, C4, C5 |
| `threadPrio_sizeOk` | `threadPriority.size < threadPriority.capacity` | A3, B7, B10, C3 |
| `mem_capGe4` | `4 ≤ membership.table.capacity` | C1 |
| `byPrio_capGe4` | `4 ≤ byPriority.capacity` | C2, C4, C5 |
| `threadPrio_capGe4` | `4 ≤ threadPriority.capacity` | C3 |

**After migration**: All 6 fields are replaced by 3 `invExtK` fields:
- `mem_invExtK : membership.table.invExtK`
- `byPrio_invExtK : byPriority.invExtK`
- `threadPrio_invExtK : threadPriority.invExtK`

The existing 3 `invExt` fields (`mem_invExt`, `byPrio_invExt`, `threadPrio_invExt`)
are also absorbed into the `invExtK` fields, reducing 9 fields → 3 total.

#### D2: `CNode.slotsUnique` Definition (Model/Object/Structures.lean:532-533)

```lean
def slotsUnique (cn : CNode) : Prop :=
  cn.slots.invExt ∧ cn.slots.size < cn.slots.capacity ∧ 4 ≤ cn.slots.capacity
```

**After migration**: This becomes simply `cn.slots.invExtK`. The definition is
rewritten as an alias, and all 4 theorem signatures that destructure `.1`,
`.2.1`, `.2.2` are updated to use `invExtK` projections:
- `empty_slotsUnique` (L617)
- `insert_slotsUnique` (L627)
- `remove_slotsUnique` (L643)
- `revokeTargetLocal_slotsUnique` (L654)

Downstream users: Capability/Invariant/Defs.lean (L29, 665, 679, 694),
Capability/Invariant/Authority.lean (L624), Capability/Invariant/Preservation.lean
(5+ sites), IntermediateState.lean (L37-39), Builder.lean (L159, 329),
Boot.lean (L45, 120), InformationFlow/Projection.lean (L172),
FreezeProofs.lean (L875, 932).

#### D3: `allTablesInvExt` Definition (Model/State.lean:278-300)

16-conjunct predicate asserting `invExt` for all SystemState tables. After
migration this becomes `allTablesInvExtK`, asserting `invExtK` for all tables.

Related proofs:
- `default_allTablesInvExt` → `default_allTablesInvExtK` (L304-320)
- `allTablesInvExt_witness` (L326) — update to match new conjuncts
- `storeObject_preserves_allTablesInvExt` (L1238-1245) — update theorem name and body

Usage sites: IntermediateState.lean (L60, 88, 96), Builder.lean (L27-64, 75-331),
Boot.lean (L120, 142).

### 3.5 Summary Metrics

| Category | Sites | Files | Description |
|----------|-------|-------|-------------|
| A: erase_preserves_invExt | 17 | 5 | `hSize` elimination |
| B: getElem?_erase_ne | 35 | 8 | `hSize` elimination |
| C: insert_size_lt_capacity | 7 | 3 | `hCapGe4` elimination |
| D: Structural | 6 fields + 2 defs | 3 | Redundancy removal |
| Internal (unchanged) | 8 | 3 | Compose wrappers |
| **Total kernel-facing** | **59** | **12** | |


---

## 4. Dependency Graph & Phase Ordering

### 4.1 Module Dependency DAG

```
                    ┌─────────────────────┐
                    │  Phase 1: Foundation │
                    │  Bridge.lean         │
                    │  (invExtK + wrappers)│
                    └──────────┬──────────┘
                               │
              ┌────────────────┼────────────────┐
              │                │                │
    ┌─────────▼─────┐  ┌──────▼───────┐  ┌─────▼──────────┐
    │  Phase 2A     │  │  Phase 2B    │  │  Phase 2C      │
    │  Set.lean     │  │  Prelude.lean│  │  Lookup.lean    │
    │  (wrappers)   │  │  (re-exports)│  │  (internal adj) │
    └───────┬───────┘  └──────┬───────┘  └────────────────┘
            │                 │
            └────────┬────────┘
                     │
    ┌────────────────┼──────────────────────────────┐
    │                │                              │
    ▼                ▼                              ▼
  Phase 3A       Phase 3B                      Phase 3C
  State.lean     Structures.lean               Builder.lean
  (allTables     (slotsUnique → invExtK,       (deleteObject,
   InvExtK)       CDT helpers)                  insertCap)
    │                │                              │
    ▼                ▼                              ▼
  Phase 3D       Phase 4A                      Phase 4B
  Intermediate   Capability/Invariant/         Capability/Invariant/
  State.lean     Defs.lean                     Preservation.lean
    │            (cspaceSlotUnique)             (3 erase sites)
    ▼                │                              │
  Phase 3E           ▼                              ▼
  Boot.lean      Phase 4C                      Phase 4D
                 Scheduler/RunQueue.lean       Scheduler/Invariant.lean
                 (field elimination,            (10 erase_ne sites)
                  9 fields → 3)                     │
                     │                              ▼
                     ▼                         Phase 4E
                 Phase 4F                      Scheduler/Operations/
                 VSpaceInvariant.lean          Preservation.lean
                 (1 site)                      (1 site)
                     │                              │
                     └──────────────────────────────┘
                                    │
                              ┌─────▼──────┐
                              │  Phase 5   │
                              │ Validation │
                              │ & Docs     │
                              └────────────┘
```

### 4.2 Critical Path

```
Phase 1 → Phase 2A/2B → Phase 3B → Phase 4A → Phase 4B
                                                    ↓
(Bridge)   (Set/Prelude)  (Structures)  (Cap/Defs) (Cap/Pres)
```

This is the longest dependency chain (6 sequential steps). All other paths
are shorter or can proceed in parallel.

### 4.3 Parallelization Opportunities

| Parallel Group | Units | Constraint |
|---------------|-------|------------|
| After Phase 1 | 2A, 2B, 2C | All depend only on Bridge.lean |
| After Phase 2 | 3A, 3B, 3C | Disjoint files |
| After Phase 3A | 3D, 3E | IntermediateState depends on State; Boot depends on IntermediateState |
| After Phase 3B | 4A, 4C, 4F | Capability/Defs, RunQueue, VSpace are independent |
| After Phase 4A | 4B | Cap/Preservation depends on Cap/Defs |
| After Phase 4C | 4D, 4E | Scheduler/Invariant and Ops/Preservation depend on RunQueue |

### 4.4 Risk Ordering Principle

Within each phase, migrate sites in this order:

1. **Definition sites first** (new types, new aliases, new wrapper theorems)
2. **Leaf consumers next** (sites with no downstream callers in the migration)
3. **Hub consumers last** (sites whose changes cascade to other migration sites)

This minimizes the blast radius of any individual change.

---

## 5. Implementation Units

### Phase 1: Foundation — `invExtK` Bundle & Wrapper Theorems

**Target file**: `SeLe4n/Kernel/RobinHood/Bridge.lean`
**Dependencies**: None (first phase)
**Build gate**: `lake build SeLe4n.Kernel.RobinHood.Bridge`

#### Unit 1.1: Define `invExtK` and Projection Lemmas

**Goal**: Add the `invExtK` definition and basic projection/construction lemmas.

**Sub-steps**:
1. **1.1a**: Add `invExtK` definition after the existing `invExt`-related section:
   ```lean
   def RHTable.invExtK [BEq α] [Hashable α] (t : RHTable α β) : Prop :=
     t.invExt ∧ t.size < t.capacity ∧ 4 ≤ t.capacity
   ```
2. **1.1b**: Add projection lemmas:
   ```lean
   theorem RHTable.invExtK_invExt (h : t.invExtK) : t.invExt := h.1
   theorem RHTable.invExtK_size_lt_capacity (h : t.invExtK) : t.size < t.capacity := h.2.1
   theorem RHTable.invExtK_capacity_ge4 (h : t.invExtK) : 4 ≤ t.capacity := h.2.2
   ```
3. **1.1c**: Add constructor lemma:
   ```lean
   theorem RHTable.mk_invExtK (hExt : t.invExt) (hSize : t.size < t.capacity)
       (hCap : 4 ≤ t.capacity) : t.invExtK := ⟨hExt, hSize, hCap⟩
   ```

**Lines changed**: ~15
**Risk**: None — purely additive

#### Unit 1.2: `empty_invExtK` Theorem

**Goal**: Prove that `RHTable.empty cap hPos` satisfies `invExtK` when `4 ≤ cap`.

**Sub-steps**:
1. **1.2a**: Add theorem:
   ```lean
   theorem RHTable.empty_invExtK [BEq α] [Hashable α]
       (cap : Nat) (hPos : 0 < cap) (hCapGe4 : 4 ≤ cap) :
       (RHTable.empty cap hPos : RHTable α β).invExtK :=
     ⟨RHTable.empty_invExt' cap hPos,
      RHTable.empty_size_lt_capacity cap hPos,
      RHTable.empty_capacity_ge4 cap hCapGe4⟩
   ```
2. **1.2b**: Verify that `empty_size_lt_capacity` and `empty_capacity_ge4` already
   exist in Bridge.lean. If `empty_capacity_ge4` does not exist, prove it:
   ```lean
   theorem RHTable.empty_capacity_ge4 [BEq α] [Hashable α]
       (cap : Nat) (hCapGe4 : 4 ≤ cap) :
       4 ≤ (RHTable.empty cap (by omega) : RHTable α β).capacity := by
     simp [RHTable.empty, Array.mkArray]; exact hCapGe4
   ```

**Lines changed**: ~15
**Risk**: Low — depends on existing `empty_*` theorems; may need a small helper

#### Unit 1.3: `erase_preserves_invExtK` Wrapper Theorem

**Goal**: Prove erase preserves `invExtK`, composing existing `erase_preserves_invExt`
and `erase_size_lt_capacity`.

**Sub-steps**:
1. **1.3a**: Add theorem:
   ```lean
   theorem RHTable.erase_preserves_invExtK [BEq α] [Hashable α] [LawfulBEq α]
       (t : RHTable α β) (k : α) (hK : t.invExtK) :
       (t.erase k).invExtK :=
     ⟨t.erase_preserves_invExt k hK.1 hK.2.1,
      t.erase_size_lt_capacity k hK.2.1,
      t.erase_capacity_ge4 k hK.2.2⟩
   ```
2. **1.3b**: Verify `erase_capacity_ge4` exists. If not, prove it:
   ```lean
   theorem RHTable.erase_capacity_ge4 [BEq α] [Hashable α]
       (t : RHTable α β) (k : α) (hCap : 4 ≤ t.capacity) :
       4 ≤ (t.erase k).capacity := by
     simp [RHTable.erase]; exact hCap  -- erase does not change capacity
   ```

**Lines changed**: ~15
**Risk**: Low — trivial composition; `erase_size_lt_capacity` already proven at L425

#### Unit 1.4: `insert_preserves_invExtK` Wrapper Theorem

**Goal**: Prove insert preserves `invExtK`.

**Sub-steps**:
1. **1.4a**: Add theorem:
   ```lean
   theorem RHTable.insert_preserves_invExtK [BEq α] [Hashable α] [LawfulBEq α]
       (t : RHTable α β) (k : α) (v : β) (hK : t.invExtK) :
       (t.insert k v).invExtK :=
     ⟨t.insert_preserves_invExt k v hK.1,
      t.insert_size_lt_capacity k v hK.1 hK.2.1 hK.2.2,
      t.insert_capacity_ge4 k v hK.2.2⟩
   ```
2. **1.4b**: Verify `insert_capacity_ge4` exists. If not, prove it (insert either
   keeps capacity or doubles it on resize, so `4 ≤ cap → 4 ≤ cap'`).

**Lines changed**: ~15
**Risk**: Low — `insert_size_lt_capacity` already proven at L391

#### Unit 1.5: `getElem?_erase_ne_K` Wrapper Theorem

**Goal**: Provide a version of `getElem?_erase_ne` that takes `invExtK` instead
of separate `hExt` + `hSize`.

**Sub-steps**:
1. **1.5a**: Add theorem:
   ```lean
   theorem RHTable.getElem?_erase_ne_K [BEq α] [Hashable α] [LawfulBEq α]
       (t : RHTable α β) (k k' : α) (hNe : ¬(k == k') = true)
       (hK : t.invExtK) :
       (t.erase k).get? k' = t.get? k' :=
     t.getElem?_erase_ne k k' hNe hK.1 hK.2.1
   ```

**Lines changed**: ~8
**Risk**: None — trivial projection

#### Unit 1.6: `filter_preserves_invExtK` Wrapper Theorem

**Goal**: Prove filter preserves `invExtK`. `filter_preserves_invExt` already
exists at L443 and does NOT take `hSize` (filter can only decrease size).

**Sub-steps**:
1. **1.6a**: Determine whether `filter_size_lt_capacity` and `filter_capacity_ge4`
   exist. If not, prove them (filter preserves capacity, decreases size).
2. **1.6b**: Add theorem:
   ```lean
   theorem RHTable.filter_preserves_invExtK [BEq α] [Hashable α] [LawfulBEq α]
       (t : RHTable α β) (f : α → β → Bool) (hK : t.invExtK) :
       (t.filter f).invExtK :=
     ⟨t.filter_preserves_invExt f hK.1,
      t.filter_size_lt_capacity f hK.2.1,
      t.filter_capacity_ge4 f hK.2.2⟩
   ```

**Lines changed**: ~15
**Risk**: Low — may need small helper lemmas for filter

#### Unit 1.7: `ofList_invExtK` Wrapper Theorem

**Goal**: Prove `ofList` produces tables satisfying `invExtK` when `4 ≤ cap`.

**Sub-steps**:
1. **1.7a**: Compose from existing `ofList_invExt`, `ofList_size_lt_capacity` (L511):
   ```lean
   theorem RHTable.ofList_invExtK [BEq α] [Hashable α] [LawfulBEq α]
       (entries : List (α × β)) (cap : Nat) (hPos : 0 < cap) (hCapGe4 : 4 ≤ cap) :
       (RHTable.ofList entries cap hPos).invExtK :=
     ⟨RHTable.ofList_invExt entries cap hPos,
      RHTable.ofList_size_lt_capacity entries cap hPos hCapGe4,
      RHTable.ofList_capacity_ge4 entries cap hPos hCapGe4⟩
   ```
2. **1.7b**: Verify `ofList_capacity_ge4` exists; prove if needed.

**Lines changed**: ~12
**Risk**: Low

**Phase 1 total**: ~95 new lines in Bridge.lean, 7 sub-units, zero changes to
existing code.


---

### Phase 2: Wrapper Layer Updates

**Dependencies**: Phase 1 complete
**Parallelizable**: Units 2.1, 2.2, 2.3 are fully independent

#### Unit 2.1: `RHSet` Wrappers (Set.lean)

**Target file**: `SeLe4n/Kernel/RobinHood/Set.lean`
**Build gate**: `lake build SeLe4n.Kernel.RobinHood.Set`

**Sub-steps**:
1. **2.1a**: Add `RHSet.invExtK` alias:
   ```lean
   def RHSet.invExtK [BEq κ] [Hashable κ] (s : RHSet κ) : Prop := s.table.invExtK
   ```
2. **2.1b**: Add `RHSet.erase_preserves_invExtK`:
   ```lean
   theorem RHSet.erase_preserves_invExtK [BEq κ] [Hashable κ] [LawfulBEq κ]
       (s : RHSet κ) (k : κ) (hK : s.table.invExtK) :
       (s.erase k).table.invExtK :=
     s.table.erase_preserves_invExtK k hK
   ```
3. **2.1c**: Add `RHSet.contains_erase_ne_K`:
   ```lean
   theorem RHSet.contains_erase_ne_K [BEq κ] [Hashable κ] [LawfulBEq κ]
       (s : RHSet κ) (k k' : κ) (hNe : ¬(k == k') = true) (hK : s.table.invExtK) :
       (s.erase k).contains k' = s.contains k' := by
     simp [RHSet.contains, RHSet.erase, RHTable.contains,
           RHTable.getElem?_erase_ne_K s.table k k' hNe hK]
   ```
4. **2.1d**: Add `RHSet.insert_preserves_invExtK` and `RHSet.empty_invExtK`.
5. **2.1e**: Retain old signatures (with `hSize` params) for now — they will be
   removed in Phase 6 cleanup after all callers are migrated.

**Lines changed**: ~30 new, 0 modified
**Risk**: None — purely additive

#### Unit 2.2: Prelude Re-exports (Prelude.lean)

**Target file**: `SeLe4n/Prelude.lean`
**Build gate**: `lake build SeLe4n.Prelude`

**Sub-steps**:
1. **2.2a**: Add `RHTable_erase_preserves_invExtK` re-export:
   ```lean
   theorem RHTable_erase_preserves_invExtK {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
       (t : RHTable α β) (k : α) (hK : t.invExtK) :
       (t.erase k).invExtK :=
     t.erase_preserves_invExtK k hK
   ```
2. **2.2b**: Add `RHTable_getElem?_erase_ne_K` re-export:
   ```lean
   theorem RHTable_getElem?_erase_ne_K {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
       (t : RHTable α β) (k k' : α) (hNe : ¬(k == k') = true) (hK : t.invExtK) :
       (t.erase k).get? k' = t.get? k' :=
     t.getElem?_erase_ne_K k k' hNe hK
   ```
3. **2.2c**: Add `RHTable_insert_preserves_invExtK` re-export.
4. **2.2d**: Retain old re-exports for backward compatibility during migration.

**Lines changed**: ~25 new, 0 modified
**Risk**: None — purely additive

#### Unit 2.3: Lookup Internal Adjustment (Lookup.lean)

**Target file**: `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean`
**Build gate**: `lake build SeLe4n.Kernel.RobinHood.Invariant.Lookup`

**Assessment**: No changes needed. The `get_after_erase_ne` theorem at L1951
is an **internal** proof that feeds `getElem?_erase_ne` in Bridge.lean. It
correctly takes separate `hExt` + `hSize` because it operates at the
Invariant layer, not the kernel API layer. The `invExtK` wrapper in Bridge.lean
(Unit 1.5) handles the projection.

**Lines changed**: 0
**Risk**: None

**Phase 2 total**: ~55 new lines across Set.lean and Prelude.lean, zero
modifications to existing code.

---

### Phase 3: Kernel State Layer Migration

**Dependencies**: Phase 2 complete
**Parallelizable**: Units 3.1, 3.2, 3.3 are independent

#### Unit 3.1: `allTablesInvExtK` (State.lean)

**Target file**: `SeLe4n/Model/State.lean`
**Build gate**: `lake build SeLe4n.Model.State`

**Sub-steps**:
1. **3.1a**: Rename `allTablesInvExt` → `allTablesInvExtK` and change each of
   the 16 conjuncts from `.invExt` to `.invExtK`:
   ```lean
   def SystemState.allTablesInvExtK (st : SystemState) : Prop :=
     st.objects.invExtK ∧ st.threadTable.invExtK ∧ ... -- 16 conjuncts
   ```
   Alternatively, keep `allTablesInvExt` as an alias for backward compat
   during migration, then remove after Phase 4.

   **Decision**: Rename in-place. The name `allTablesInvExt` is used in <15
   sites (State.lean, IntermediateState.lean, Builder.lean, Boot.lean), all of
   which are migrated in this phase. A clean rename avoids temporary aliases.

2. **3.1b**: Update `default_allTablesInvExtK` proof — change 16×
   `empty_invExt' 16 (by omega)` to `empty_invExtK 16 (by omega) (by omega)`:
   ```lean
   theorem SystemState.default_allTablesInvExtK :
       (default : SystemState).allTablesInvExtK :=
     ⟨RHTable.empty_invExtK 16 (by omega) (by omega),
      RHTable.empty_invExtK 16 (by omega) (by omega),
      ... ⟩ -- 16 entries
   ```

3. **3.1c**: Update `allTablesInvExtK_witness` theorem (L326) — update the
   16 named conjuncts to destructure `invExtK` instead of `invExt`.

4. **3.1d**: Update `storeObject_preserves_allTablesInvExtK` (L1238-1245):
   - Change signature from `allTablesInvExt` → `allTablesInvExtK`
   - Change body to use `insert_preserves_invExtK` instead of
     `insert_preserves_invExt` + separate `hSize` threading

5. **3.1e**: Update the `storeObject` erase site (L1293):
   - Replace `RHTable.erase_preserves_invExt st.asidTable r.asid hAsid hAsidSize`
     with `RHTable.erase_preserves_invExtK st.asidTable r.asid hAsidK`
   - Remove `hAsidSize` parameter from enclosing function signature
   - The `hAsidK` is obtained from the `allTablesInvExtK` bundle

**Lines changed**: ~80 modified (rename + proof body updates)
**Risk**: Medium — 16-conjunct predicate rewrite; verify each conjunct carefully

#### Unit 3.2: `slotsUnique` Simplification (Structures.lean)

**Target file**: `SeLe4n/Model/Object/Structures.lean`
**Build gate**: `lake build SeLe4n.Model.Object.Structures`

This is the largest and most complex unit. It is broken into sub-units by
functional region.

##### Sub-unit 3.2a: Redefine `slotsUnique`

Replace the 3-conjunct definition with an `invExtK` alias:

```lean
def slotsUnique (cn : CNode) : Prop := cn.slots.invExtK
```

All sites that destructure `hUniq.1` (invExt), `hUniq.2.1` (size < cap),
`hUniq.2.2` (4 ≤ cap) must switch to `hUniq.invExtK_invExt`, etc. However,
since `invExtK` has the same internal structure (`invExt ∧ size < cap ∧ 4 ≤ cap`),
**the projection paths `.1`, `.2.1`, `.2.2` remain valid**. The change is a
transparent alias.

**Lines changed**: 2 (definition only)
**Risk**: None if `invExtK` has same And-structure as old `slotsUnique`

##### Sub-unit 3.2b: Update `slotsUnique` Theorems (L617-660)

Update 4 theorems to use `invExtK` operations:

1. `empty_slotsUnique` (L617): Change proof to use `empty_invExtK`
2. `insert_slotsUnique` (L627): Change proof to use `insert_preserves_invExtK`
   plus `insert_capacity_ge4` — but with `invExtK` wrapper this simplifies to
   just `insert_preserves_invExtK`
3. `remove_slotsUnique` (L643): Change proof to use `erase_preserves_invExtK`
4. `revokeTargetLocal_slotsUnique` (L654): Follows from filter + erase wrappers

**Lines changed**: ~20
**Risk**: Low — each theorem is a 1-3 line proof

##### Sub-unit 3.2c: Update VSpaceRoot Erase Site (L331)

The `getElem?_erase_ne` call at L331 uses VSpaceRoot mapping table params.
Replace `hExt hSize` with `hK` from the VSpaceRoot's `invExtK` field (to be
established during VSpace migration).

**Decision**: Defer to Phase 4F if the `hSize` here comes from VSpaceInvariant.
Check the actual parameter source.

**Lines changed**: ~2
**Risk**: Low

##### Sub-unit 3.2d: Update CNode Lookup Theorems (L720-760)

Sites at L758 (`getElem?_erase_ne cn.slots slot slot'`) — update to use
`getElem?_erase_ne_K` with `slotsUnique` (which is now `invExtK`).

**Lines changed**: ~5
**Risk**: Low

##### Sub-unit 3.2e: Update CDT Helper Theorems — `erase_preserves_invExt` Sites (L1280-1370)

8 call sites (A11-A14) in the CDT helper region. These theorems take explicit
`hExt : m.invExt` and `hSize : m.size < m.capacity` parameters for CDT child
map operations.

**Approach**: Change theorem signatures to take `hK : m.invExtK` instead of
separate `hExt` + `hSize`. Update each call to `erase_preserves_invExt` →
`erase_preserves_invExtK`.

Affected theorems (read each before editing):
- `CDT.eraseChild_preserves_childMapInvariant` (~L1280)
- `CDT.eraseChild_no_new_children` (~L1300)
- `CDT.eraseChild_preserves_parentMap` (~L1320)
- `CDT.eraseChild_fold_preserves` (~L1360)

**Lines changed**: ~30 (4 signatures + 8 call sites)
**Risk**: Medium — CDT helpers have interleaved erase chains; verify each
derived `hEraseSize` is replaced correctly

##### Sub-unit 3.2f: Update CDT Helper Theorems — `getElem?_erase_ne` Sites (L1380-1700)

20+ call sites (B22-B35) in CDT child-map operation proofs. These use
`hExt hSizeCM` or derived `hEraseExt hEraseSize` pairs.

**Approach**: Same as 3.2e — change signatures to take `hK : cdt.childMap.invExtK`,
replace `getElem?_erase_ne` → `getElem?_erase_ne_K`, and use
`erase_preserves_invExtK` to derive the erased table's `invExtK`.

**Sub-sub-steps** (to manage the 20+ sites safely):
1. **3.2f-i**: Update theorems in L1380-1440 region (B22, B23): `removeChild`
   and `removeSubtree` signatures + bodies
2. **3.2f-ii**: Update theorems in L1470-1520 region (A15-A17, B24-B26):
   double-erase chains (`erase node` then `erase p`)
3. **3.2f-iii**: Update theorems in L1540-1600 region (B27-B29): sibling and
   parent lookups after erase
4. **3.2f-iv**: Update theorems in L1640-1700 region (B30-B35): final CDT
   preservation theorems with nested erase chains

**Lines changed**: ~60 (signature changes + 20 call site updates)
**Risk**: High — this is the densest cluster of changes. Each sub-sub-step
should be followed by `lake build SeLe4n.Model.Object.Structures` before
proceeding.

**Phase 3.2 total**: ~120 lines changed across Structures.lean

#### Unit 3.3: Builder.lean Migration

**Target file**: `SeLe4n/Model/Builder.lean`
**Build gate**: `lake build SeLe4n.Model.Builder`

##### Sub-unit 3.3a: Update `allTablesInvExt` Decomposition Helpers (L27-64)

8 private theorems extract individual table `invExt` from the 16-conjunct
bundle. Update to extract `invExtK` instead:

```lean
private theorem allTablesInvExtK_objects (h : st.allTablesInvExtK) :
    st.objects.invExtK := h.1
-- ... (8 total)
```

**Lines changed**: ~40 (8 theorem name + body changes)
**Risk**: Low — mechanical rename

##### Sub-unit 3.3b: Update `deleteObject` (L238-300)

`deleteObject` takes `hObjSize`, `hTypesSize` parameters (sites A7, A8) and
4 `getElem?_erase_ne` calls (B14-B17).

**Sub-sub-steps**:
1. **3.3b-i**: Remove `hObjSize` and `hTypesSize` parameters from `deleteObject`
   signature. Replace with derivation from `allTablesInvExtK`:
   ```lean
   have hObjK := allTablesInvExtK_objects hAllK
   have hTypesK := allTablesInvExtK_objectTypes hAllK
   ```
2. **3.3b-ii**: Replace A7 (`erase_preserves_invExt _ _ h.1 hObjSize`) with
   `erase_preserves_invExtK _ _ hObjK`
3. **3.3b-iii**: Replace A8 similarly for types table
4. **3.3b-iv**: Replace B14-B17 (`getElem?_erase_ne ... hObjInv hObjSize`) with
   `getElem?_erase_ne_K ... hObjK`

**Lines changed**: ~25
**Risk**: Medium — `deleteObject` has ZERO callers (dead code?), but must still
compile

##### Sub-unit 3.3c: Update `insertCap` (L319-333)

`insertCap` destructures `slotsUnique` with `.1`, `.2.1`, `.2.2` (site C7).
After `slotsUnique = invExtK` (Sub-unit 3.2a), the projection paths are the
same, so this may need no change. Verify.

If `insert_slotsUnique` is now proven via `insert_preserves_invExtK`, this
call site is already handled.

**Lines changed**: 0-5
**Risk**: Low

#### Unit 3.4: IntermediateState.lean Migration

**Target file**: `SeLe4n/Model/IntermediateState.lean`
**Build gate**: `lake build SeLe4n.Model.IntermediateState`
**Dependencies**: Unit 3.1 (allTablesInvExtK)

**Sub-steps**:
1. **3.4a**: Change field at L60 from `allTablesInvExt` to `allTablesInvExtK`:
   ```lean
   tablesOk : state.allTablesInvExtK
   ```
2. **3.4b**: Update `mkEmptyIntermediateState` (L88) to use
   `default_allTablesInvExtK`
3. **3.4c**: Update `mkEmptyIntermediateState_valid` (L96) to reference the
   new field name

**Lines changed**: ~10
**Risk**: Low — small file, mechanical rename

#### Unit 3.5: Boot.lean Migration

**Target file**: `SeLe4n/Platform/Boot.lean`
**Build gate**: `lake build SeLe4n.Platform.Boot`
**Dependencies**: Unit 3.4 (IntermediateState)

**Sub-steps**:
1. **3.5a**: Update `bootFromPlatform_allTablesInvExtK` theorem (L120):
   rename and update proof
2. **3.5b**: Update `bootFromPlatform_valid` (L142) to reference new name
3. **3.5c**: Update CNode slotsUnique references (L45) — after slotsUnique
   becomes `invExtK`, these are transparent

**Lines changed**: ~15
**Risk**: Low

**Phase 3 total**: ~290 lines changed across 5 files.


---

### Phase 4: Subsystem Migration

**Dependencies**: Phase 3 complete
**Parallelizable**: Units 4.1, 4.3, 4.6 are independent after Phase 3

#### Unit 4.1: Capability/Invariant/Defs.lean

**Target file**: `SeLe4n/Kernel/Capability/Invariant/Defs.lean`
**Build gate**: `lake build SeLe4n.Kernel.Capability.Invariant.Defs`
**Dependencies**: Unit 3.2a (slotsUnique = invExtK)

**Sub-steps**:
1. **4.1a**: Update `cspaceSlotUnique` predicate (L29) — references
   `cn.slotsUnique` which is now `cn.slots.invExtK`. The predicate body likely
   needs no change since `slotsUnique` is a transparent alias.
2. **4.1b**: Update private theorem at L665 — `getElem?_erase_ne` call (B12):
   ```lean
   -- Before: RHTable.getElem?_erase_ne cn.slots slot s ... hUniq.1 hUniq.2.1
   -- After:  RHTable.getElem?_erase_ne_K cn.slots slot s ... hUniq
   ```
   Since `slotsUnique = invExtK`, `hUniq` is directly an `invExtK` proof.
3. **4.1c**: Update L694 if it has similar erase_ne usage.

**Lines changed**: ~10
**Risk**: Low — small, localized changes

#### Unit 4.2: Capability/Invariant/Preservation.lean

**Target file**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Build gate**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`
**Dependencies**: Unit 4.1 (Defs.lean)

**Sub-steps**:
1. **4.2a**: Update `cspaceDeleteSlot_preserves_cdtNodeSlot` (L361, site A4):
   - Remove `hSzRef` parameter
   - Replace `erase_preserves_invExt ... hInvRef hSzRef` with
     `erase_preserves_invExtK ... hRefK`
   - Obtain `hRefK` from the capability invariant bundle (which carries
     `slotsUnique` → `invExtK` for all CNode tables)
   - **Note**: This theorem has no external callers, so signature change is safe

2. **4.2b**: Update second erase site at L799 (site A5):
   - Same pattern: remove `hSzDel`, use `erase_preserves_invExtK`

3. **4.2c**: Update third erase site at L1127 (site A6):
   - Same pattern: remove `hNSSzDel`, use `erase_preserves_invExtK`

4. **4.2d**: Update any `getElem?_erase_ne` calls that feed from these
   theorems' context. Verify by reading each theorem's full body.

5. **4.2e**: Update preservation theorems at L1456, 1541, 1567, 1598, 1646
   that require new objects to satisfy `slotsUnique` — these should be
   transparent since `slotsUnique = invExtK` is an alias.

**Lines changed**: ~30
**Risk**: Medium — must trace `hSize` provenance through each theorem's
hypothesis chain

#### Unit 4.3: Scheduler/RunQueue.lean — Field Elimination

**Target file**: `SeLe4n/Kernel/Scheduler/RunQueue.lean`
**Build gate**: `lake build SeLe4n.Kernel.Scheduler.RunQueue`
**Dependencies**: Phase 2 (Set.lean wrappers)

This is the **highest-impact structural change**: replacing 9 fields with 3.

##### Sub-unit 4.3a: Replace Structure Fields

Current fields (L34-45):
```lean
  mem_invExt : membership.table.invExt
  byPrio_invExt : byPriority.invExt
  threadPrio_invExt : threadPriority.invExt
  mem_sizeOk : membership.table.size < membership.table.capacity
  byPrio_sizeOk : byPriority.size < byPriority.capacity
  threadPrio_sizeOk : threadPriority.size < threadPriority.capacity
  mem_capGe4 : 4 ≤ membership.table.capacity
  byPrio_capGe4 : 4 ≤ byPriority.capacity
  threadPrio_capGe4 : 4 ≤ threadPriority.capacity
```

Replace with:
```lean
  mem_invExtK : membership.table.invExtK
  byPrio_invExtK : byPriority.invExtK
  threadPrio_invExtK : threadPriority.invExtK
```

Add backward-compatibility projections (temporary, removed in Phase 5):
```lean
theorem RunQueue.mem_invExt (rq : RunQueue) : rq.membership.table.invExt := rq.mem_invExtK.1
theorem RunQueue.mem_sizeOk (rq : RunQueue) : rq.membership.table.size < rq.membership.table.capacity := rq.mem_invExtK.2.1
-- etc.
```

**Decision**: Skip backward-compat projections. Instead, update all callers
in the same unit. The RunQueue file is self-contained for most call sites,
and external callers (Scheduler/Invariant.lean) are migrated in Unit 4.4.

**Lines changed**: ~15 (field definitions)
**Risk**: High — every RunQueue constructor call must be updated

##### Sub-unit 4.3b: Update `RunQueue.default` Constructor (L55-65)

Update the default constructor to provide 3 `invExtK` proofs instead of 9
separate proofs:

```lean
instance : Inhabited RunQueue where
  default := {
    ...
    mem_invExtK := RHSet.empty_invExtK
    byPrio_invExtK := RHTable.empty_invExtK 16 (by omega) (by omega)
    threadPrio_invExtK := RHTable.empty_invExtK 16 (by omega) (by omega)
  }
```

**Lines changed**: ~10
**Risk**: Low

##### Sub-unit 4.3c: Update `RunQueue.insert` (L130-184)

Sites A1(erase), C1, C2, C3 (insert_size_lt_capacity).

**Sub-sub-steps**:
1. **4.3c-i**: Replace construction of `mem_invExt`, `mem_sizeOk`, `mem_capGe4`
   fields with single `mem_invExtK := rq.membership.table.insert_preserves_invExtK
   ... rq.mem_invExtK`
2. **4.3c-ii**: Same for `byPrio_invExtK` and `threadPrio_invExtK`

**Lines changed**: ~25
**Risk**: Medium — the insert constructor is dense

##### Sub-unit 4.3d: Update `RunQueue.removeThread` (L210-280)

Sites A1-A3 (erase_preserves_invExt), B1-B4 (contains_erase_ne), C4 (insert
in erase path).

**Sub-sub-steps**:
1. **4.3d-i**: Replace `RHSet.erase_preserves_invExt rq.membership tid
   rq.mem_invExt rq.mem_sizeOk` with `RHSet.erase_preserves_invExtK
   rq.membership tid rq.mem_invExtK`
2. **4.3d-ii**: Replace all `RHSet.contains_erase_ne ... rq.mem_invExt
   rq.mem_sizeOk` with `RHSet.contains_erase_ne_K ... rq.mem_invExtK`
3. **4.3d-iii**: Replace `byPriority.erase_preserves_invExt` →
   `erase_preserves_invExtK`, `insert_size_lt_capacity` →
   `insert_preserves_invExtK` (the insert-after-erase path)
4. **4.3d-iv**: Update all structure field assignments in the returned RunQueue

**Lines changed**: ~40
**Risk**: Medium — interleaved erase+insert logic

##### Sub-unit 4.3e: Update `RunQueue.dequeue` (L310-340)

Site C5 (`insert_size_lt_capacity` for re-inserting truncated bucket).

Replace:
```lean
byPrio_sizeOk := rq.byPriority.insert_size_lt_capacity prio bucket'
    rq.byPrio_invExt rq.byPrio_sizeOk rq.byPrio_capGe4
```
With:
```lean
byPrio_invExtK := rq.byPriority.insert_preserves_invExtK prio bucket' rq.byPrio_invExtK
```

**Lines changed**: ~15
**Risk**: Low

##### Sub-unit 4.3f: Update Helper Lemmas (L380-430, L1000-1030)

Sites B3-B6, B5-B6 in `removeThread_not_member`, `removeThread_preserves_other`,
and related helper lemmas.

Replace all `rq.mem_invExt rq.mem_sizeOk` pairs with `rq.mem_invExtK` in
`contains_erase_ne_K` calls.

**Lines changed**: ~20
**Risk**: Low — mechanical substitution

**Phase 4.3 total**: ~125 lines changed in RunQueue.lean

#### Unit 4.4: Scheduler/Invariant.lean

**Target file**: `SeLe4n/Kernel/Scheduler/Invariant.lean`
**Build gate**: `lake build SeLe4n.Kernel.Scheduler.Invariant`
**Dependencies**: Unit 4.3 (RunQueue field changes)

**Sub-steps**:
1. **4.4a**: Update site B7 (L448): Replace
   `RHTable.getElem?_erase_ne rq.threadPriority ... rq.threadPrio_invExt rq.threadPrio_sizeOk`
   with `RHTable.getElem?_erase_ne_K rq.threadPriority ... rq.threadPrio_invExtK`
2. **4.4b**: Update site B8 (L450): Replace
   `RHSet.contains_erase_ne ... rq.mem_invExt rq.mem_sizeOk`
   with `RHSet.contains_erase_ne_K ... rq.mem_invExtK`
3. **4.4c**: Update sites B9, B10 (L462, L465) — same pattern
4. **4.4d**: Verify that no other sites in this file reference the old fields

**Lines changed**: ~15
**Risk**: Low — 4 mechanical substitutions

#### Unit 4.5: Scheduler/Operations/Preservation.lean

**Target file**: `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean`
**Build gate**: `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation`
**Dependencies**: Unit 4.4

**Sub-steps**:
1. **4.5a**: Update site B11 (L2572): Replace `RHTable.getElem?_erase_ne`
   with `getElem?_erase_ne_K` using the RunQueue's `threadPrio_invExtK`

**Lines changed**: ~5
**Risk**: Low — single site

#### Unit 4.6: Architecture/VSpaceInvariant.lean

**Target file**: `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`
**Build gate**: `lake build SeLe4n.Kernel.Architecture.VSpaceInvariant`
**Dependencies**: Phase 1 (Bridge.lean wrappers)

**Sub-steps**:
1. **4.6a**: Update site B13 (L269): Replace
   `RHTable.getElem?_erase_ne mappings vaddr v hBeq hExt hSize`
   with `RHTable.getElem?_erase_ne_K mappings vaddr v hBeq hK`
2. **4.6b**: Trace provenance of `hExt` and `hSize` — determine whether the
   enclosing theorem takes these as separate params or derives them. If separate
   params, consolidate into `hK : mappings.invExtK`.
3. **4.6c**: Verify no cascade to callers of this theorem.

**Lines changed**: ~10
**Risk**: Low — single site, self-contained theorem

#### Unit 4.7: Capability/Invariant/Authority.lean

**Target file**: `SeLe4n/Kernel/Capability/Invariant/Authority.lean`
**Build gate**: `lake build SeLe4n.Kernel.Capability.Invariant.Authority`
**Dependencies**: Unit 3.2a (slotsUnique = invExtK)

**Sub-steps**:
1. **4.7a**: Update `cspaceSlotUnique_of_storeObject_cnode` (L624) — this
   theorem requires the new CNode to satisfy `slotsUnique`. Since `slotsUnique`
   is now `invExtK`, verify the proof still type-checks (it should be
   transparent).

**Lines changed**: 0-5
**Risk**: Low — likely transparent

#### Unit 4.8: InformationFlow/Projection.lean

**Target file**: `SeLe4n/Kernel/InformationFlow/Projection.lean`
**Build gate**: `lake build SeLe4n.Kernel.InformationFlow.Projection`
**Dependencies**: Unit 3.2a (slotsUnique = invExtK)

**Sub-steps**:
1. **4.8a**: Update L172 reference to `slotsUnique` — should be transparent
   since `slotsUnique` is now an alias for `invExtK`.

**Lines changed**: 0-5
**Risk**: Low

#### Unit 4.9: FreezeProofs.lean

**Target file**: `SeLe4n/Model/FreezeProofs.lean`
**Build gate**: `lake build SeLe4n.Model.FreezeProofs`
**Dependencies**: Unit 3.2a (slotsUnique = invExtK)

**Sub-steps**:
1. **4.9a**: Update L875, L932 references to `slotsUnique` — should be
   transparent.

**Lines changed**: 0-5
**Risk**: Low

**Phase 4 total**: ~215 lines changed across 8 files.


---

### Phase 5: Dead Code Removal & Cleanup

**Dependencies**: All Phase 4 units complete; all call sites migrated
**Gate**: `lake build` (full) succeeds before any removal

#### Unit 5.1: Remove Old `hSize`-Parameterized Theorems from Bridge.lean

After all callers use `_K` variants, the old signatures with separate
`hExt` + `hSize` parameters are dead code.

**Sub-steps**:
1. **5.1a**: Verify zero callers of old `erase_preserves_invExt` outside
   Invariant/ layer (should only be called from `erase_preserves_invExtK` body)
2. **5.1b**: Verify zero callers of old `getElem?_erase_ne` outside Invariant/
   layer (should only be called from `getElem?_erase_ne_K` body)
3. **5.1c**: Verify zero callers of old `insert_size_lt_capacity` outside
   Invariant/ layer (should only be called from `insert_preserves_invExtK` body)
4. **5.1d**: **Do NOT remove** — these theorems are still needed as the body of
   the `_K` wrappers. They remain as internal API. Mark them with a comment:
   ```lean
   /-- Internal: use `erase_preserves_invExtK` instead for kernel code. -/
   ```

**Decision**: The old theorems are **not dead** — they are the implementation
of the `_K` wrappers. They just lose their kernel-facing role. No removal
needed; optionally add a doc comment.

**Lines changed**: ~5 (doc comments only)
**Risk**: None

#### Unit 5.2: Remove Old Wrappers from Set.lean

**Sub-steps**:
1. **5.2a**: Verify zero kernel callers of `RHSet.erase_preserves_invExt`
   (old, with `hSize` param) — should only be called from `_invExtK` variant
2. **5.2b**: Verify zero kernel callers of `RHSet.contains_erase_ne`
   (old, with `hSize` param)
3. **5.2c**: If confirmed dead to kernel code, remove old wrappers. Keep if
   they're still used in Set.lean's own proof of the `_K` variant.

**Lines changed**: 0-15
**Risk**: Low

#### Unit 5.3: Remove Old Re-exports from Prelude.lean

**Sub-steps**:
1. **5.3a**: Verify zero callers of `RHTable_erase_preserves_invExt` (old)
2. **5.3b**: Verify zero callers of `RHTable_getElem?_erase_ne` (old)
3. **5.3c**: Remove dead re-exports

**Lines changed**: ~15 removed
**Risk**: Low — verify with `lake build` after removal

#### Unit 5.4: Remove Old `allTablesInvExt` References

**Sub-steps**:
1. **5.4a**: Verify no remaining references to old name `allTablesInvExt`
2. **5.4b**: Remove old decomposition helpers in Builder.lean if replaced

**Lines changed**: ~40 removed (if old helpers were retained during Phase 3)
**Risk**: Low

#### Unit 5.5: Verify No Remaining `hSize`/`hCapGe4` Threading

**Sub-steps**:
1. **5.5a**: Grep for `hSize` in all .lean files — verify only internal
   (Invariant/) uses remain
2. **5.5b**: Grep for `hCapGe4` — verify only `insert_size_lt_capacity`
   definition and `ofList_size_lt_capacity` remain
3. **5.5c**: Grep for `sizeOk` in RunQueue.lean — verify field is removed
4. **5.5d**: Grep for `capGe4` in RunQueue.lean — verify field is removed

**Lines changed**: 0
**Risk**: None — verification only

**Phase 5 total**: ~75 lines removed across 3-4 files.

---

### Phase 6: Validation & Documentation

**Dependencies**: Phase 5 complete

#### Unit 6.1: Full Build Verification

**Sub-steps**:
1. **6.1a**: `lake build` — full default target
2. **6.1b**: Build every modified module explicitly:
   ```bash
   lake build SeLe4n.Kernel.RobinHood.Bridge
   lake build SeLe4n.Kernel.RobinHood.Set
   lake build SeLe4n.Prelude
   lake build SeLe4n.Model.State
   lake build SeLe4n.Model.Object.Structures
   lake build SeLe4n.Model.Builder
   lake build SeLe4n.Model.IntermediateState
   lake build SeLe4n.Platform.Boot
   lake build SeLe4n.Kernel.Capability.Invariant.Defs
   lake build SeLe4n.Kernel.Capability.Invariant.Preservation
   lake build SeLe4n.Kernel.Capability.Invariant.Authority
   lake build SeLe4n.Kernel.Scheduler.RunQueue
   lake build SeLe4n.Kernel.Scheduler.Invariant
   lake build SeLe4n.Kernel.Scheduler.Operations.Preservation
   lake build SeLe4n.Kernel.Architecture.VSpaceInvariant
   lake build SeLe4n.Kernel.InformationFlow.Projection
   lake build SeLe4n.Model.FreezeProofs
   ```
3. **6.1c**: `./scripts/test_full.sh` — all tiers green

#### Unit 6.2: Sorry/Axiom Audit

**Sub-steps**:
1. **6.2a**: Grep for `sorry` in all modified .lean files — must find zero
2. **6.2b**: Grep for `axiom` in all modified .lean files — must find zero
3. **6.2c**: Verify no new `sorry` introduced anywhere in the proof surface

#### Unit 6.3: Documentation Updates

**Sub-steps**:
1. **6.3a**: Update `CLAUDE.md` — add `invExtK` to terminology, update any
   references to `allTablesInvExt`, note RunQueue field reduction (9→3)
2. **6.3b**: Update `docs/spec/SELE4N_SPEC.md` — update RobinHood invariant
   description to mention `invExtK` as the kernel-facing bundle
3. **6.3c**: Update `docs/WORKSTREAM_HISTORY.md` — mark V3-B as complete
4. **6.3d**: Update `docs/audits/AUDIT_v0.21.7_WORKSTREAM_PLAN.md` — update
   V3-B status
5. **6.3e**: Update `docs/gitbook/12-proof-and-invariant-map.md` — add
   `invExtK` to the proof chain map
6. **6.3f**: Regenerate `docs/codebase_map.json` if new definitions affect it

#### Unit 6.4: Commit Strategy

Commits should be atomic and bisectable. Recommended sequence:

| Commit | Content | Gate |
|--------|---------|------|
| 1 | Phase 1: `invExtK` definition + wrapper theorems in Bridge.lean | `lake build SeLe4n.Kernel.RobinHood.Bridge` |
| 2 | Phase 2: Set.lean + Prelude.lean wrappers | `lake build SeLe4n.Kernel.RobinHood.Set && lake build SeLe4n.Prelude` |
| 3 | Phase 3.1: `allTablesInvExtK` in State.lean | `lake build SeLe4n.Model.State` |
| 4 | Phase 3.2a-d: `slotsUnique` alias + CNode theorems | `lake build SeLe4n.Model.Object.Structures` |
| 5 | Phase 3.2e-f: CDT helper migration (Structures.lean L1280-1700) | `lake build SeLe4n.Model.Object.Structures` |
| 6 | Phase 3.3: Builder.lean migration | `lake build SeLe4n.Model.Builder` |
| 7 | Phase 3.4-3.5: IntermediateState + Boot | `lake build SeLe4n.Model.IntermediateState && lake build SeLe4n.Platform.Boot` |
| 8 | Phase 4.1-4.2: Capability invariant migration | `lake build SeLe4n.Kernel.Capability.Invariant.Preservation` |
| 9 | Phase 4.3: RunQueue field elimination | `lake build SeLe4n.Kernel.Scheduler.RunQueue` |
| 10 | Phase 4.4-4.5: Scheduler invariant + preservation | `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation` |
| 11 | Phase 4.6-4.9: VSpace, Authority, InfoFlow, FreezeProofs | Per-module build |
| 12 | Phase 5: Dead code cleanup | `lake build` (full) |
| 13 | Phase 6.3: Documentation updates | `test_full.sh` |

Each commit must pass its gate check. If a commit fails, fix forward (do not
revert and restart).

---

## 6. Risk Assessment & Mitigation

### 6.1 Risk Matrix

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| `invExtK` And-structure differs from `slotsUnique` | Low | Medium | Verify projection paths `.1`, `.2.1`, `.2.2` match before Sub-unit 3.2a |
| CDT double-erase chains break (Sub-unit 3.2f) | Medium | High | Build after each sub-sub-step (3.2f-i through 3.2f-iv) |
| RunQueue constructor cascade (Sub-unit 4.3a) | Medium | High | Update default constructor first (4.3b), then operations one at a time |
| Missing helper lemma (e.g., `erase_capacity_ge4`) | Medium | Low | Check existence before Phase 1; trivial to prove |
| `deleteObject` in Builder.lean is dead code | Low | None | Still must compile; migrate for completeness |
| Capability preservation `hSize` provenance is complex | Medium | Medium | Read full theorem body before editing; trace hypothesis chain |
| Scheduler/Operations/Preservation.lean is 2170 lines | Low | Medium | Only 1 site (L2572); use offset/limit reads |
| Documentation links break | Low | Low | Run `check_website_links.sh` after doc updates |

### 6.2 Rollback Strategy

Each commit is independently buildable. To rollback:
- `git revert <commit>` for any single commit
- The wrapper approach means old code paths remain functional until Phase 5
  cleanup, providing a natural rollback point

### 6.3 Testing Strategy

| Phase | Minimum Test | Full Test |
|-------|-------------|-----------|
| 1-2 | `lake build <module>` | — |
| 3 | `lake build <module>` per file | `test_smoke.sh` after Phase 3 complete |
| 4 | `lake build <module>` per file | `test_smoke.sh` after Phase 4 complete |
| 5 | `lake build` (full) | `test_full.sh` |
| 6 | `test_full.sh` | `test_nightly.sh` (optional) |

---

## 7. Summary

### 7.1 Scope

| Metric | Value |
|--------|-------|
| **Total kernel-facing call sites** | 59 |
| **Files modified** | 17 |
| **Structural fields removed** | 6 (RunQueue) |
| **Structural fields added** | 0 (net -6, absorbing existing invExt fields into invExtK reduces 9→3) |
| **Definitions simplified** | 2 (`slotsUnique`, `allTablesInvExt`) |
| **New theorems** | ~15 (invExtK wrappers in Bridge.lean, Set.lean, Prelude.lean) |
| **Lines added** | ~195 (wrapper theorems, projections) |
| **Lines modified** | ~510 (call site migrations) |
| **Lines removed** | ~75 (dead code cleanup) |
| **Net line change** | ~+120 (most additions are small wrapper theorems) |
| **Commits** | 13 |
| **Phases** | 6 |

### 7.2 Key Invariant

After migration, all kernel code uses `invExtK` (which bundles `invExt ∧
size < capacity ∧ 4 ≤ capacity`). The separate `hSize` and `hCapGe4` parameters
are eliminated from all kernel-facing theorem signatures. Internal RobinHood
proofs (Preservation.lean, Lookup.lean) are **completely unchanged**.

### 7.3 What Does NOT Change

- `invExt` definition (Preservation.lean:447-448) — **UNCHANGED**
- `invExt` projection paths (`.1`, `.2.1`, `.2.2.1`, `.2.2.2`) — **UNCHANGED**
- `insertNoResize_preserves_invExt` — **UNCHANGED** (the critical theorem that
  breaks under Option A)
- All 5 composite preservation theorems in Preservation.lean — **UNCHANGED**
- All functional correctness theorems in Lookup.lean — **UNCHANGED**
- `loadFactorBounded` definition and theorems — **UNCHANGED** (retained for
  specification documentation)
- Filter fold proofs in Bridge.lean — **UNCHANGED** (they use `invExt` internally)
- Resize fold proofs in Preservation.lean — **UNCHANGED**

### 7.4 Success Criteria

1. Zero `sorry`/`axiom` in production proof surface
2. `lake build` succeeds for all 17 modified modules
3. `test_full.sh` green
4. Grep for `hSize` in kernel code returns zero hits (only Invariant/ layer)
5. Grep for `hCapGe4` returns only internal definition + `ofList` theorem
6. `RunQueue` structure has exactly 3 invariant fields (down from 9)
7. `CNode.slotsUnique` is defined as `cn.slots.invExtK` (single alias)
8. `allTablesInvExtK` uses `invExtK` for all 16 conjuncts
9. H-RH-1 finding is fully resolved
