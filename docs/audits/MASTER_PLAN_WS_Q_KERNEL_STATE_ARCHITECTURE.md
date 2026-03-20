# WS-Q Master Plan — Two-Phase Kernel State Architecture (v0.17.7+)

**Revision**: 2 (post-audit refinement)
**Created**: 2026-03-20 | **Revised**: 2026-03-20
**Baseline version**: 0.17.4
**Prior portfolios**: WS-N (v0.17.0–0.17.4, N1–N4 complete), WS-M (v0.17.0, complete)
**Absorbed workstreams**: WS-P (Service Interface Layer), WS-O (Syscall Rust Wrappers)
**Hardware target**: Raspberry Pi 5 (AArch64, BCM2712)
**Constraint**: Zero `sorry`/`axiom` in Lean proof surface; zero `unsafe` outside Rust syscall trap

---

## 1. Executive Summary

This master plan unifies three architectural imperatives into a single coherent
execution path for the seLe4n verified microkernel:

1. **Two-Phase State Architecture** — A builder/freeze model that eliminates
   `Std.HashMap` and `Std.HashSet` from the kernel state, replacing them with
   the proven Robin Hood hash table (WS-N, ~4,300 LoC, zero sorry) during
   initialization, then converting to dense arrays with `Fin`-indexed access
   and a verified CNode radix tree for execution.

2. **Service Interface Simplification** (absorbs WS-P) — Replaces the
   orchestration-focused service subsystem (~1,950 lines) with a capability-
   indexed interface enforcement layer. Lifecycle management moves to user space.

3. **Rust Syscall Wrappers** (absorbs WS-O) — A `no_std` userspace library
   (`libsele4n`) exposing seLe4n's verified syscall semantics as safe Rust
   wrappers, cross-validated against Lean trace output.

**Why one plan?** These three efforts are deeply coupled:
- WS-P changes the syscall surface, which WS-O must encode.
- The two-phase architecture replaces every map in `SystemState`, affecting
  every subsystem including the new service registry.
- The CNode radix tree replaces `RHTable`-backed `CNode.slots` (WS-N4),
  which the Rust wrappers address through CSpace syscalls.

---

## 2. Pre-Implementation Audit

This section documents findings from a comprehensive audit of the v0.17.4
codebase performed before finalizing this plan. Every issue identified below
has a corresponding resolution in the phase plan.

### 2.1 Complete Map Inventory

The audit identified **17 map-like collections** across the kernel state
hierarchy — 5 more than the original draft's 12:

**SystemState direct fields (9 maps):**

| # | Field | Type | Key → Value | Location |
|---|-------|------|-------------|----------|
| 1 | `objects` | `Std.HashMap` | `ObjId → KernelObject` | State.lean:129 |
| 2 | `objectIndexSet` | `Std.HashSet` | `ObjId` | State.lean:151 |
| 3 | `services` | `Std.HashMap` | `ServiceId → ServiceGraphEntry` | State.lean:152 |
| 4 | `irqHandlers` | `Std.HashMap` | `Irq → ObjId` | State.lean:157 |
| 5 | `asidTable` | `Std.HashMap` | `ASID → ObjId` | State.lean:163 |
| 6 | `cdtSlotNode` | `Std.HashMap` | `SlotRef → CdtNodeId` | State.lean:165 |
| 7 | `cdtNodeSlot` | `Std.HashMap` | `CdtNodeId → SlotRef` | State.lean:166 |
| 8 | `lifecycle.objectTypes` | `Std.HashMap` | `ObjId → KernelObjectType` | State.lean:104 |
| 9 | `lifecycle.capabilityRefs` | `Std.HashMap` | `SlotRef → CapTarget` | State.lean:105 |

**Nested in CapDerivationTree (2 maps):**

| # | Field | Type | Key → Value | Location |
|---|-------|------|-------------|----------|
| 10 | `cdt.childMap` | `Std.HashMap` | `CdtNodeId → List CdtNodeId` | Structures.lean:776 |
| 11 | `cdt.parentMap` | `Std.HashMap` | `CdtNodeId → CdtNodeId` | Structures.lean:779 |

**Nested in RunQueue (3 maps) — MISSED IN ORIGINAL DRAFT:**

| # | Field | Type | Key → Value | Location |
|---|-------|------|-------------|----------|
| 12 | `runQueue.byPriority` | `Std.HashMap` | `Priority → List ThreadId` | RunQueue.lean |
| 13 | `runQueue.threadPriority` | `Std.HashMap` | `ThreadId → Priority` | RunQueue.lean |
| 14 | `runQueue.membership` | `Std.HashSet` | `ThreadId` | RunQueue.lean |

**Per-object embedded maps (2 maps):**

| # | Field | Type | Key → Value | Location |
|---|-------|------|-------------|----------|
| 15 | `CNode.slots` | `RHTable` | `Slot → Capability` | Structures.lean:346 |
| 16 | `VSpaceRoot.mappings` | `Std.HashMap` | `VAddr → (PAddr × PagePerms)` | Structures.lean:87 |

**Algorithm-local HashSets (not in state, but must be addressed):**

| # | Usage | Type | Location | Count |
|---|-------|------|----------|-------|
| 17a | BFS visited set | `Std.HashSet` | Acyclicity.lean | 16 uses |
| 17b | Observable filtering | `Std.HashSet` | Projection.lean | 8 uses |
| 17c | BFS frontier | `Std.HashSet` | Service/Operations.lean | 2 uses |

### 2.2 Callsite Impact Analysis

| Pattern | Files | Occurrences | Highest-Impact File |
|---------|-------|-------------|---------------------|
| `Std.HashMap` | 12 | 78 | Prelude.lean (28) |
| `Std.HashSet` | 8 | 57 | Acyclicity.lean (16) |
| `.contains` | 15 | 122+ | RunQueue.lean (49) |
| `.toList` | 14 | 35+ | RunQueue.lean (21) |
| `.fold` | 19 | 35+ | State.lean (15) |
| `[key]?` lookup | 44 | 100+ | Prelude.lean (13) |

### 2.3 Prelude Utility Lemma Inventory

`SeLe4n/Prelude.lean` contains **42 utility lemmas** that downstream proofs
depend on:
- **28 `Std.HashMap` lemmas**: get, insert, erase, filter, contains, fold
  patterns used across all subsystem invariant proofs
- **14 `Std.HashSet` lemmas**: contains, insert, erase, membership patterns
  used in scheduler, service, and information flow proofs

**Every one** of these lemmas must have a proven `RHTable`/`RHSet` equivalent
before subsystem migration can begin. This is the critical path for Q2.

### 2.4 Atomic Migration Groups

The audit identified three groups of maps that **must migrate together** due
to shared update functions:

**Group A: Object Store (storeObject atomicity)**
`storeObject` modifies `objects`, `objectIndex`, `objectIndexSet`,
`lifecycle.objectTypes`, `lifecycle.capabilityRefs`, and `asidTable` in a
single function (State.lean:219-244). These 6 fields must be migrated
atomically or `storeObject` won't compile.

**Group B: CDT Dual Index**
`addEdge`, `removeAsChild`, `removeAsParent`, `removeNode` update `childMap`,
`parentMap`, `cdtSlotNode`, and `cdtNodeSlot` together. These 4 fields form
an atomic migration unit.

**Group C: RunQueue Internals**
`byPriority`, `threadPriority`, and `membership` are maintained in lockstep
by RunQueue operations. All 3 must migrate together.

### 2.5 Issues Resolved in This Revision

| # | Issue | Resolution | Phase |
|---|-------|------------|-------|
| 1 | RunQueue maps missing from inventory | Added as maps 12-14; dedicated subphase Q2-G | Q2 |
| 2 | No Prelude lemma migration strategy | Dedicated subphase Q2-A with 42 lemma targets | Q2 |
| 3 | No RHSet type defined | Q2-B defines `RHSet κ` as wrapper around `RHTable κ Unit` | Q2 |
| 4 | Q2 scope underestimated | Expanded to 10 subphases; revised to ~1,800 new lines | Q2 |
| 5 | Algorithm-local HashSets unaddressed | Kept as `Std.HashSet` (temporary, not in state) | Q2 |
| 6 | storeObject atomicity | Group A maps migrate in single subphase Q2-C | Q2 |
| 7 | FrozenMap index contradicts "no hashing" | Clarified: hash at freeze-time only; runtime is array access | Q5 |
| 8 | CDT retained as-is but uses HashMap | CDT maps freeze to FrozenMap in Q5 | Q5 |
| 9 | SchedulerState retained as-is but RunQueue uses HashMap | RunQueue freezes to arrays in Q5 | Q5 |
| 10 | Retype at runtime vs boot-only | Hybrid model: pre-allocated Option slots + overflow | Q7 |
| 11 | Commutativity only for value mutations | Scoped to value-only ops; key-set ops are builder-only | Q7 |
| 12 | RadixTree doesn't match resolveSlot | Aligned to existing guard+radix bit extraction | Q4 |
| 13 | VSpaceRoot frozen representation vague | FrozenMap (consistent with other maps) | Q5 |
| 14 | Q1-E too large (15 files) | Split into Q1-E1 (type removal) + Q1-E2 (NI proof repair) | Q1 |
| 15 | CDT maps must migrate atomically | Group B maps in dedicated subphase Q2-F | Q2 |
| 16 | No pre-allocation/sizing strategy | Explicit capacity planning in Q5 with upper bounds | Q5 |


---

## 3. Architecture

### 3.1 Two-Phase State Model

```
                    ┌──────────────────────────┐
                    │     Boot / Init           │
                    │  (Platform + Untyped)     │
                    └────────────┬──────────────┘
                                 │
                                 ▼
                    ┌──────────────────────────┐
                    │   IntermediateState       │
                    │   (Builder Phase)         │
                    │                           │
                    │  • RHTable for ALL maps   │
                    │  • RHSet for ALL sets     │
                    │  • Fixed hash function    │
                    │  • Deterministic probes   │
                    │  • Dynamic alloc (retype) │
                    └────────────┬──────────────┘
                                 │
                           freeze(·)
                                 │
                                 ▼
                    ┌──────────────────────────┐
                    │   FrozenSystemState       │
                    │   (Execution Phase)       │
                    │                           │
                    │  • Dense Array + Fin idx  │
                    │  • CNode RadixTree        │
                    │  • Pre-alloc Option slots │
                    │  • O(1) array indexing    │
                    │  • Hash at freeze only    │
                    │  • Deterministic image    │
                    └──────────────────────────┘
```

**Builder Phase (IntermediateState):**

All 16 key/value stores (see §2.1) use `RHTable` with a fixed hash function
(Lean's `Hashable` instances — deterministic for all `Nat`-wrapped kernel types),
fixed probe sequence (linear probing with Robin Hood displacement), and
75% load-factor-triggered resize. Every `RHTable` instance satisfies `invExt`
(well-formedness + probe chain dominance + no duplicate keys) — proven in WS-N2
(~3,600 LoC, zero sorry).

All 2 `Std.HashSet` state fields use `RHSet` (a newtype wrapper around
`RHTable κ Unit` defined in Q2-B) with identical hash and probe semantics.

Algorithm-local `Std.HashSet` usage (BFS visited sets in Acyclicity.lean,
observable filtering in Projection.lean) is **retained** — these are temporary
values that exist only during a single function call and never persist in state.

**Freeze Phase:**

`freeze : IntermediateState → FrozenSystemState` converts each `RHTable K V`
into a `FrozenMap K V`:

```lean
structure FrozenMap (κ : Type) (ν : Type) [BEq κ] [Hashable κ] where
  data      : Array ν                        -- dense, contiguous values
  indexMap  : RHTable κ (Fin data.size)      -- key → position (computed ONCE)
  hInject   : ∀ k₁ k₂ i, indexMap.get? k₁ = some i →
                          indexMap.get? k₂ = some i → k₁ == k₂
  hCoverage : ∀ k, (∃ v, original.get? k = some v) →
                   ∃ i, indexMap.get? k = some i
```

**Critical clarification (audit issue #7):** The `indexMap` is an `RHTable`
that performs hash computation **once** during the `freeze` call. After freeze,
all runtime lookups follow a two-step path:

1. `indexMap.get? key` — O(1) amortized RHTable lookup (hashing happens here)
2. `data[idx]` — O(1) array access via the returned `Fin`

This means runtime lookups **do** involve one hash computation per access.
The "no hashing at runtime" guarantee applies specifically to **CNode slot
lookups**, which use the RadixTree (O(depth) with zero hashing). For
non-CNode maps, the performance benefit comes from cache-friendly dense
array storage and verified hash semantics, not from eliminating hashing.

**Execution Phase (FrozenSystemState):**

- **Object mutation**: In-place array update — `data[idx] := updatedObj`
  where `idx : Fin n` is stable (index map never changes after freeze).
- **Object creation at runtime (audit issue #10)**: Pre-allocated `Option`
  slots in the dense array. During freeze, untyped memory regions are
  enumerated to determine maximum object count. Each potential object gets
  an `Option KernelObject` slot. Retype fills a `none` slot; delete clears
  it back to `none`. The index map includes all potential keys at freeze time.
- **CNode lookups**: RadixTree with fixed `2^radixWidth` fanout — O(depth),
  zero hashing, cache-friendly array-backed nodes.
- **Deterministic memory image**: Identical boot config → identical
  `FrozenSystemState` byte-for-byte.

### 3.2 CNode Radix Tree

CNode addressing in seL4 (and seLe4n) is inherently a bit-sliced tree
traversal. The existing `resolveSlot` function (Structures.lean) extracts
`guardWidth` bits for guard matching, then `radixWidth` bits for child
indexing. A radix tree with `2^radixWidth` fanout matches this exactly.

```
CPtr bit decomposition:
┌──────────────┬──────────────┬──────────────┬─────────────────┐
│ Guard (g₁)   │ Radix (r₁)   │ Guard (g₂)   │ Radix (r₂)      │
│ match check  │ 2^r₁ fanout  │ match check  │ 2^r₂ fanout     │
└──────┬───────┴──────┬───────┴──────┬───────┴────────┬────────┘
       │              │              │                │
       ▼              ▼              ▼                ▼
   CNode L1       child[i]      CNode L2         child[j] → Cap
```

The builder-phase CNode retains `RHTable Slot Capability` for flexibility.
The freeze step converts to a radix tree and proves lookup equivalence:
`∀ slot, rhTable.get? slot = radixTree.lookup slot`.

### 3.3 Service Interface (WS-P Absorption)

**Retained (mechanism):**
- `serviceRegisterDependency` — dependency edge with cycle detection
- `serviceHasPathTo` — DFS cycle detection
- Acyclicity proofs (~1,110 lines, minus status-related frame lemmas)

**Added:**
- `InterfaceSpec` — concrete interface spec (no universe polymorphism)
- `ServiceRegistration` — capability-mediated service record
- 4 registry operations + invariants

**Removed (policy → user space):**
- `serviceStart`/`serviceStop`/`serviceRestart`, `ServiceStatus`, `ServiceConfig`

### 3.4 Rust Syscall Wrappers (WS-O Absorption)

Three `no_std` crates — `sele4n-types`, `sele4n-abi`, `sele4n-sys` — encoding
the finalized ABI surface (14 syscalls post-Q1). Cross-validated against Lean
trace output. Single `unsafe` block: inline ARM64 `svc #0`. Independent of
internal state architecture (Q2–Q7), enabling parallel execution.

---

## 4. Phase Plan Overview

| Phase | ID | Focus | Sub-phases | Deps | Target |
|-------|----|-------|------------|------|--------|
| 1 | **Q1** | Service interface simplification | 7 (A–G) | — | v0.17.7 |
| 2 | **Q2** | Universal RHTable migration | 10 (A–J) | Q1 | v0.17.8 |
| 3 | **Q3** | IntermediateState formalization | 3 (A–C) | Q2 | v0.17.9 |
| 4 | **Q4** | CNode radix tree (verified) | 4 (A–D) | Q2 | v0.17.10 |
| 5 | **Q5** | FrozenSystemState + freeze | 4 (A–D) | Q3, Q4 | v0.17.11 |
| 6 | **Q6** | Freeze correctness proofs | 4 (A–D) | Q5 | v0.17.12 |
| 7 | **Q7** | Frozen kernel operations | 5 (A–E) | Q6 | v0.17.13 |
| 8 | **Q8** | Rust syscall wrappers (WS-O) | 4 (A–D) | Q1 | v0.17.13 ∥ |
| 9 | **Q9** | Integration testing + documentation | 4 (A–D) | Q7, Q8 | v0.17.14 |

**Total sub-phases**: 45 atomic units of work.

```
Q1 ──→ Q2 ──→ Q3 ──┬──→ Q5 ──→ Q6 ──→ Q7 ──→ Q9
  │                 │                           ▲
  │                 └──→ Q4 ──┘                 │
  │                                             │
  └──────────────→ Q8 ──────────────────────────┘
```

**Critical path**: Q1 → Q2 → Q3 → Q4 → Q5 → Q6 → Q7 → Q9
**Parallel path**: Q1 → Q8 → Q9


---

## 5. Detailed Phase Plans

### Phase Q1: Service Interface Simplification

**Absorbs**: WS-P phases P1–P5
**Target version**: v0.17.7
**Goal**: Replace lifecycle-focused service orchestration with capability-indexed
interface enforcement, simplifying the type surface before the universal
RHTable migration in Q2.

#### Q1-A: Foundation Types

**New file**: `SeLe4n/Kernel/Service/Interface.lean`
**Modified files**: `SeLe4n/Prelude.lean`, `SeLe4n/Model/Object/Types.lean`

**Tasks:**
1. Define `InterfaceId` in Prelude.lean: `Hashable`, `BEq`, `ofNat`/`toNat`/`sentinel`
2. Define `InterfaceSpec` (concrete, no universe polymorphism):
   ```lean
   structure InterfaceSpec where
     ifaceId         : InterfaceId
     methodCount     : Nat
     maxMessageSize  : Nat
     maxResponseSize : Nat
     requiresGrant   : Bool
   ```
3. Define `ServiceRegistration` with `sid`, `iface`, `endpointCap`
4. Prove `InterfaceId` roundtrip theorems

**Gate**: `lake build` + `test_fast.sh`

#### Q1-B: Registry State and Operations

**New file**: `SeLe4n/Kernel/Service/Registry.lean` (4 operations + 8 theorems)
**Modified**: `SeLe4n/Model/State.lean` (add `serviceRegistry`, `interfaceRegistry`)

**Operations:**
- `registerInterface` — register concrete spec | error: `illegalState` (dup)
- `registerService` — capability-mediated | errors: `illegalState`, `objectNotFound`, `invalidCapability`
- `lookupServiceByCap` — read-only lookup | error: `objectNotFound`
- `revokeService` — remove by ServiceId | error: `objectNotFound`

**Minimum 8 theorems**: error conditions, success post-conditions, frame lemmas.

**Gate**: `lake build` + `test_smoke.sh`

#### Q1-C: Registry Invariants

**New file**: `SeLe4n/Kernel/Service/Registry/Invariant.lean`

**Definitions**: `registryEndpointValid`, `registryInterfaceValid`, `registryInvariant`

**Proofs**: preservation under all 4 operations, cross-subsystem preservation
(lifecycle, capability, scheduler, IPC), `default_registryInvariant`,
`apiInvariantBundle` extension.

**Gate**: `lake build` + `test_smoke.sh` + zero sorry

#### Q1-D: API Integration and Syscall Dispatch

**Modified files (6)**:
- `SeLe4n/Kernel/API.lean` — `apiServiceRegister`, `apiServiceRevoke`, `apiServiceQuery`
- `SeLe4n/Model/Object/Types.lean` — `SyscallId` variants: `.serviceRegister` (11), `.serviceRevoke` (12), `.serviceQuery` (13)
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — `SyscallId.toNat`/`ofNat?` extension
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` — new decode functions
- `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` — `registerServiceChecked`
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` — catalog update

**Gate**: `lake build` + `test_smoke.sh` + zero sorry

#### Q1-E1: Legacy Type Removal

**Strategy**: Rename `services` → `servicesLegacy` to surface all callsites
via compile errors.

**Modified files (~8)**:
- `SeLe4n/Model/Object/Types.lean` — Remove `ServiceStatus`, simplify `ServiceGraphEntry` (drop `status`)
- `SeLe4n/Model/State.lean` — Remove `ServiceConfig`, `serviceConfig` field, `setServiceStatusState`, `dependenciesSatisfied`
- `SeLe4n/Kernel/Service/Operations.lean` — Remove `serviceStart`, `serviceStop`, `serviceRestart` + 11 associated theorems
- `SeLe4n/Kernel/Service/Invariant/Policy.lean` — Remove lifecycle bundle, add registry-policy bridge
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` — Remove status-related frame lemmas
- `SeLe4n/Kernel/API.lean` — Remove `apiServiceStart`/`apiServiceStop`, old dispatch arms
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — Remove old `SyscallId` variants
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` — Remove old decode functions

**Gate**: `lake build` + `test_smoke.sh` + zero sorry

#### Q1-E2: Information Flow Proof Repair

**Modified files (~7)** — separated from Q1-E1 to keep each unit small:
- `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` — Remove `serviceRestartChecked`
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — Replace `projectServiceStatus`
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` — Replace legacy NI proofs
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` — Replace NI step constructors
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` — Update frame lemmas
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` — Update catalog
- `SeLe4n/Kernel/Service/Invariant.lean` — Import updates

**Gate**: `lake build` + `test_smoke.sh` + zero sorry + no `ServiceStatus`/
`ServiceConfig`/`serviceStart`/`serviceStop`/`serviceRestart` anywhere in kernel

#### Q1-F: Test Migration

**Modified files (7)**: MainTraceHarness, StateBuilder, NegativeStateSuite,
OperationChainSuite, InformationFlowSuite, fixtures (2).

**New test scenarios (SRG-001 through SRG-010):**

| ID | Description | Expected |
|----|-------------|----------|
| SRG-001 | Register service with valid endpoint + interface | success |
| SRG-002 | Duplicate service registration | illegalState |
| SRG-003 | Register with unknown interface | objectNotFound |
| SRG-004 | Register with invalid endpoint | invalidCapability |
| SRG-005 | Revoke registered service | success |
| SRG-006 | Revoke non-existent | objectNotFound |
| SRG-007 | Lookup by matching capability | success |
| SRG-008 | Lookup by non-matching capability | objectNotFound |
| SRG-009 | Register interface + service chain | success |
| SRG-010 | Dependency cycle detection still works | cyclicDependency |

**Gate**: `test_smoke.sh` + `test_full.sh` + zero sorry

#### Q1-G: Documentation

Update WORKSTREAM_HISTORY.md, SELE4N_SPEC.md, DEVELOPMENT.md,
CLAIM_EVIDENCE_INDEX.md, affected GitBook chapters. Regenerate codebase map.

**Gate**: `test_full.sh` + `generate_codebase_map.py --pretty --check`

---

### Phase Q2: Universal RHTable Migration

**Target version**: v0.17.8
**Goal**: Replace every `Std.HashMap` and `Std.HashSet` in kernel state with
`RHTable`/`RHSet`, establishing the builder-phase representation.

**Scope (post-audit)**: 16 map fields + 2 set fields across 6 structures,
touching 30+ files, requiring 42+ new Prelude lemmas. This is the largest
and highest-risk phase — broken into 10 atomic subphases with strict ordering.

#### Q2-A: Prelude Lemma Foundation

**Critical path**: All subsequent subphases depend on these lemmas.

**Modified file**: `SeLe4n/Prelude.lean`

**Task**: Create `RHTable` equivalents for all 28 `Std.HashMap` utility lemmas
currently in Prelude.lean. These lemmas are referenced by proofs across every
subsystem. Many will be thin wrappers around existing Bridge.lean theorems.

**Target lemmas (28)** — grouped by operation:

| Category | Count | Examples |
|----------|-------|---------|
| `get?`/`getElem?` | 6 | `get_eq_getElem?`, `getElem?_some_implies_contains` |
| `insert` | 5 | `insert_overrides`, `insert_preserves_other`, `contains_insert_self` |
| `erase` | 4 | `erase_absent_noop`, `erase_preserves_other`, `contains_erase_self` |
| `contains` | 4 | `contains_iff_get_some`, `not_contains_iff_get_none` |
| `filter` | 3 | `filter_subset`, `filter_preserves_match` |
| `fold`/`toList` | 4 | `fold_comm`, `toList_complete`, `toList_noDup` |
| `size` | 2 | `size_insert_bound`, `size_erase_bound` |

**Strategy**: Most bridge lemmas already exist in `Bridge.lean`. The Prelude
equivalents will:
1. Re-export bridge lemmas under the naming convention used by downstream proofs
2. Add `[simp]` attributes where appropriate
3. Provide `Std.HashMap`-compatible signatures to minimize downstream churn

**Gate**: `lake build SeLe4n.Prelude` + zero sorry

#### Q2-B: RHSet Type Definition

**New file**: `SeLe4n/Kernel/RobinHood/Set.lean`

**Definition**:
```lean
/-- A verified hash set backed by RHTable. -/
structure RHSet (κ : Type) [BEq κ] [Hashable κ] where
  table : RHTable κ Unit

def RHSet.empty (cap : Nat := 16) (h : 0 < cap := by omega) : RHSet κ :=
  ⟨RHTable.empty cap h⟩

def RHSet.contains (s : RHSet κ) (k : κ) : Bool := s.table.contains k
def RHSet.insert (s : RHSet κ) (k : κ) : RHSet κ := ⟨s.table.insert k ()⟩
def RHSet.erase (s : RHSet κ) (k : κ) : RHSet κ := ⟨s.table.erase k⟩
def RHSet.toList (s : RHSet κ) : List κ := s.table.toList.map (·.1)
def RHSet.fold (s : RHSet κ) (init : β) (f : β → κ → β) : β :=
  s.table.fold init (fun acc k _ => f acc k)
```

**Bridge lemmas (14)** — matching Prelude's `Std.HashSet` lemma signatures:

| Category | Count | Examples |
|----------|-------|---------|
| `contains` | 5 | `contains_insert_self`, `contains_insert_ne`, `contains_erase_self`, `contains_erase_ne`, `contains_empty` |
| `insert`/`erase` | 4 | `insert_idempotent`, `erase_absent_noop` |
| `membership` | 3 | `mem_iff_contains`, `toList_contains` |
| `invariant` | 2 | `insert_preserves_invExt`, `erase_preserves_invExt` |

**Instances**: `Inhabited`, `BEq`, `Membership`, `EmptyCollection`

**Gate**: `lake build SeLe4n.Kernel.RobinHood.Set` + zero sorry

#### Q2-C: Core SystemState Maps + Object Store

**Migration group A** (storeObject atomicity — must migrate together):
- `objects : Std.HashMap ObjId KernelObject` → `RHTable ObjId KernelObject`
- `objectIndexSet : Std.HashSet ObjId` → `RHSet ObjId`
- `lifecycle.objectTypes : Std.HashMap ObjId KernelObjectType` → `RHTable ObjId KernelObjectType`
- `lifecycle.capabilityRefs : Std.HashMap SlotRef CapTarget` → `RHTable SlotRef CapTarget`
- `asidTable : Std.HashMap ASID ObjId` → `RHTable ASID ObjId`

**Prerequisite**: `SlotRef` must have `Hashable` and `BEq` instances. Currently
has a hash instance via `mixHash` (State.lean:93-94) — verify it works with RHTable.

**Modified files (~12)**:
- `SeLe4n/Model/State.lean` — field type changes + `storeObject` rewrite
- `SeLe4n/Model/Object/Structures.lean` — if LifecycleMetadata is defined here
- All files that call `storeObject`, `lookupObject`, or access these fields
  directly (Scheduler, IPC, Capability, Lifecycle, API subsystems)

**Strategy**: Change field types, then fix every compile error. Most errors
will be `Std.HashMap.get?` → `RHTable.get?` (same signature). The `[key]?`
bracket notation is provided by `GetElem?` instance (already in RHTable).

**Gate**: `lake build` + `test_smoke.sh` + zero sorry

#### Q2-D: Per-Object Maps (VSpaceRoot.mappings)

**Migration**:
- `VSpaceRoot.mappings : Std.HashMap VAddr (PAddr × PagePerms)` → `RHTable VAddr (PAddr × PagePerms)`

**Modified files (~6)**:
- `SeLe4n/Model/Object/Structures.lean` — VSpaceRoot type + operations (lookup, mapPage, unmapPage, noVirtualOverlap, BEq)
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` — 6 HashMap references in invariant proofs
- `SeLe4n/Kernel/Architecture/VSpaceBackend.lean` — interface documentation
- `SeLe4n/Testing/StateBuilder.lean` — VSpaceRoot fixture builders
- Test files referencing VSpaceRoot construction

**Prerequisite**: `VAddr` must have `Hashable` and `BEq` instances (already
present — VAddr wraps Nat).

**Note**: VSpaceRoot is embedded per-object, not at SystemState level. Each
VSpaceRoot in the `objects` map has its own `mappings` RHTable. The `invExt`
predicate for these is tracked per-object in `IntermediateState.hPerObjectMappings`.

**Gate**: `lake build` + `test_smoke.sh` + zero sorry

#### Q2-E: IRQ Handler Map

**Migration**: `irqHandlers : Std.HashMap Irq ObjId` → `RHTable Irq ObjId`

**Modified files (~3)**:
- `SeLe4n/Model/State.lean` — field type
- `SeLe4n/Platform/RPi5/BootContract.lean` — IRQ initialization
- `SeLe4n/Platform/Sim/BootContract.lean` — simulation IRQ setup

**Gate**: `lake build` + `test_smoke.sh`

#### Q2-F: CDT Maps (Atomic Group B)

**Migration group B** (CDT dual index — must migrate together):
- `cdt.childMap : Std.HashMap CdtNodeId (List CdtNodeId)` → `RHTable CdtNodeId (List CdtNodeId)`
- `cdt.parentMap : Std.HashMap CdtNodeId CdtNodeId` → `RHTable CdtNodeId CdtNodeId`
- `cdtSlotNode : Std.HashMap SlotRef CdtNodeId` → `RHTable SlotRef CdtNodeId`
- `cdtNodeSlot : Std.HashMap CdtNodeId SlotRef` → `RHTable CdtNodeId SlotRef`

**Modified files (~5)**:
- `SeLe4n/Model/Object/Structures.lean` — CapDerivationTree type + operations
  (addEdge, childrenOf, parentOf, removeAsChild, removeAsParent, removeNode,
  descendantsOf)
- `SeLe4n/Model/State.lean` — cdtSlotNode/cdtNodeSlot fields + CDT helpers
  (lookupCdtNodeOfSlot, lookupCdtSlotOfNode, attachSlotToCdtNode,
  detachSlotFromCdt, ensureCdtNodeForSlot)
- `SeLe4n/Kernel/Capability/Operations.lean` — CDT manipulation in cap ops
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` — CDT invariant definitions
- `SeLe4n/Kernel/Lifecycle/Operations.lean` — CDT edge creation during retype

**Prerequisite**: `CdtNodeId` already has `Hashable`/`BEq` instances
(Structures.lean:718-745).

**Gate**: `lake build` + `test_smoke.sh` + zero sorry

#### Q2-G: RunQueue Internals (Atomic Group C)

**Migration group C** (RunQueue — must migrate together):
- `runQueue.byPriority : Std.HashMap Priority (List ThreadId)` → `RHTable Priority (List ThreadId)`
- `runQueue.threadPriority : Std.HashMap ThreadId Priority` → `RHTable ThreadId Priority`
- `runQueue.membership : Std.HashSet ThreadId` → `RHSet ThreadId`

**Modified files (~4)**:
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` — **49** `.contains` + **21** `.toList` + **8** HashMap + **14** HashSet = **92 callsites**. This is the single highest-density migration target.
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean` — scheduler transitions
- `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` — thread selection
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` — **2,170 lines** of invariant proofs

**Risk**: RunQueue.lean has the highest callsite density in the codebase.
Scheduler preservation proofs (2,170 lines) depend heavily on HashMap/HashSet
membership semantics.

**Mitigation**: The bridge lemmas from Q2-A/Q2-B provide matching API.
Migrate RunQueue.lean first (internal types), then fix operations, then
preservation proofs. Run `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation`
after each file to catch regressions early.

**Gate**: `lake build` + `test_smoke.sh` + zero sorry

#### Q2-H: Service Maps

**Migration** (note: fields 12-13 from §2.1 are introduced in Q1 and can be
`RHTable` from the start if Q1 and Q2 are sequential):
- `services : Std.HashMap ServiceId ServiceGraphEntry` → `RHTable ServiceId ServiceGraphEntry`
- `serviceRegistry : Std.HashMap → RHTable` (if not already RHTable from Q1)
- `interfaceRegistry : Std.HashMap → RHTable` (if not already RHTable from Q1)

**Modified files (~4)**:
- `SeLe4n/Model/State.lean` — service field types
- `SeLe4n/Kernel/Service/Operations.lean` — service transitions
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` — cycle detection
  (uses `Std.HashSet` for BFS visited set — this is **algorithm-local** and
  retained as `Std.HashSet`, not migrated)
- `SeLe4n/Kernel/Service/Invariant/Policy.lean` — policy predicates

**Gate**: `lake build` + `test_smoke.sh` + zero sorry

#### Q2-I: Std.HashMap/HashSet Elimination Verification

**Task**: Grep the entire codebase for remaining `Std.HashMap` and `Std.HashSet`
in state-persistent positions. Algorithm-local uses are permitted.

**Verification script**:
```bash
# State-persistent HashMap — should return ZERO matches (excluding algorithm-local)
grep -rn "Std\.HashMap" SeLe4n/ --include="*.lean" | grep -v "-- algorithm-local"

# State-persistent HashSet — should return ZERO in state definitions
grep -rn "Std\.HashSet" SeLe4n/Model/ SeLe4n/Kernel/Scheduler/RunQueue.lean
```

**Permitted remaining `Std.HashSet` locations** (algorithm-local only):
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` — BFS visited set
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — observable filtering
- `SeLe4n/Kernel/Service/Operations.lean` — BFS frontier

**Gate**: Zero state-persistent `Std.HashMap`/`Std.HashSet` + `test_smoke.sh`

#### Q2-J: allTablesInvExt Invariant

**New predicate** (in `SeLe4n/Model/State.lean` or new file):

```lean
def SystemState.allTablesInvExt (st : SystemState) : Prop :=
  -- SystemState direct fields
  st.objects.invExt ∧
  st.irqHandlers.invExt ∧
  st.asidTable.invExt ∧
  st.cdtSlotNode.invExt ∧
  st.cdtNodeSlot.invExt ∧
  -- LifecycleMetadata
  st.lifecycle.objectTypes.invExt ∧
  st.lifecycle.capabilityRefs.invExt ∧
  -- CDT
  st.cdt.childMap.invExt ∧
  st.cdt.parentMap.invExt ∧
  -- Service (post-Q1)
  st.serviceRegistry.invExt ∧
  st.interfaceRegistry.invExt ∧
  st.services.invExt ∧
  -- RunQueue
  st.scheduler.runQueue.byPriority.invExt ∧
  st.scheduler.runQueue.threadPriority.invExt ∧
  -- RHSet invExt (via table field)
  st.objectIndexSet.table.invExt ∧
  st.scheduler.runQueue.membership.table.invExt
```

**Proof obligations**:
- `default_allTablesInvExt` — default SystemState satisfies (all tables empty)
- `storeObject_preserves_allTablesInvExt` — main state update preserves
- Per-subsystem: each operation preserves `allTablesInvExt`

**Gate**: `lake build` + `test_full.sh` + zero sorry


---

### Phase Q3: IntermediateState Formalization

**Target version**: v0.19.1
**Goal**: Define `IntermediateState` as the well-typed builder state with
explicit invariant contracts and builder operations.

#### Q3-A: IntermediateState Type

**New file**: `SeLe4n/Model/IntermediateState.lean`

```lean
/-- Builder-phase state: all maps verified, all invariants carried. -/
structure IntermediateState where
  state : SystemState
  hAllTables : state.allTablesInvExt
  hPerObjectSlots : ∀ id cn, state.objects.get? id = some (.cnode cn) →
    cn.slotsUnique
  hPerObjectMappings : ∀ id vs, state.objects.get? id = some (.vspaceRoot vs) →
    vs.mappings.invExt
  hLifecycleConsistent : state.lifecycleMetadataConsistent
```

This ensures every `RHTable` and `RHSet` in the system satisfies its
invariants at all times during the builder phase.

**Gate**: `lake build SeLe4n.Model.IntermediateState`

#### Q3-B: Builder Operations

**New file**: `SeLe4n/Model/Builder.lean`

Builder operations wrap existing kernel operations with `IntermediateState`
preservation. Each takes and returns `IntermediateState`, carrying the
invariant witness forward.

| Builder Op | Wraps | Proves |
|-----------|-------|--------|
| `Builder.createObject` | `storeObject` | `allTablesInvExt` + per-object preserved |
| `Builder.deleteObject` | object erase | `allTablesInvExt` preserved |
| `Builder.registerIrq` | IRQ insert | `allTablesInvExt` preserved |
| `Builder.mapPage` | VSpace insert | per-object `mappings.invExt` preserved |
| `Builder.insertCap` | CNode slot insert | per-object `slotsUnique` preserved |
| `Builder.registerService` | service registration | `allTablesInvExt` preserved |
| `Builder.addCdtEdge` | CDT edge add | CDT map `invExt` preserved |

**Gate**: `lake build SeLe4n.Model.Builder` + zero sorry

#### Q3-C: Boot Sequence

**New file**: `SeLe4n/Platform/Boot.lean`

```lean
def IntermediateState.empty : IntermediateState where
  state := default  -- all RHTables empty, all RHSets empty
  hAllTables := default_allTablesInvExt
  hPerObjectSlots := by intro id cn h; simp [RHTable.getElem?_empty] at h
  hPerObjectMappings := by intro id vs h; simp [RHTable.getElem?_empty] at h
  hLifecycleConsistent := by ...

def bootFromPlatform (config : PlatformConfig) : IntermediateState :=
  let initial := IntermediateState.empty
  let withIrqs := config.irqTable.foldl (fun st (irq, handler) =>
    Builder.registerIrq st irq handler) initial
  let withObjects := config.initialObjects.foldl (fun st (id, obj) =>
    Builder.createObject st id obj) withIrqs
  withObjects
```

**Gate**: `lake build SeLe4n.Platform.Boot` + `test_smoke.sh` + zero sorry

---

### Phase Q4: CNode Radix Tree (Verified)

**Target version**: v0.20.0
**Goal**: Implement a verified radix tree matching seLe4n's existing CNode
addressing semantics (guard match + radix bit extraction from `resolveSlot`
in Structures.lean).

#### Q4-A: Radix Tree Core Types

**New file**: `SeLe4n/Kernel/RadixTree/Core.lean`

The design aligns with the existing `CNode.resolveSlot` implementation, which:
1. Extracts `guardWidth` bits and compares against `guardValue`
2. Extracts `radixWidth` bits as the child index
3. Returns the slot index from the child array

```lean
/-- Bit extraction: get `width` bits starting at `offset` from a slot value. -/
def extractBits (val : Nat) (offset width : Nat) : Fin (2 ^ width) :=
  ⟨(val >>> offset) % (2 ^ width), Nat.mod_lt _ (Nat.two_pow_pos width)⟩

/-- A single radix node with fixed 2^radixWidth children. -/
structure RadixNode (α : Type) where
  guardWidth  : Nat
  guardValue  : Nat
  radixWidth  : Nat
  children    : Array (Option α)
  hChildSize  : children.size = 2 ^ radixWidth

/-- A CNode radix tree: flat array of capability slots. -/
structure CNodeRadix where
  guardWidth  : Nat
  guardValue  : Nat
  radixWidth  : Nat
  slots       : Array (Option Capability)
  hSlotSize   : slots.size = 2 ^ radixWidth
```

**Design note**: seLe4n CNodes are **single-level** — each CNode has one
guard and one radix level. Multi-level CSpace resolution chains through
multiple CNode objects (via `resolveSlot` → lookup → recurse). The radix
tree therefore models a single CNode as a flat `2^radixWidth`-entry array,
not a deep tree. This is simpler than the original draft proposed and
matches the actual codebase semantics exactly.

#### Q4-B: Radix Tree Operations

| Operation | Signature | Complexity |
|-----------|-----------|------------|
| `CNodeRadix.empty` | `(guardW guardV radixW : Nat) → CNodeRadix` | O(2^radixW) |
| `CNodeRadix.lookup` | `(tree : CNodeRadix) → (slot : Slot) → Option Capability` | O(1) |
| `CNodeRadix.insert` | `(tree : CNodeRadix) → (slot : Slot) → (cap : Capability) → CNodeRadix` | O(1) |
| `CNodeRadix.erase` | `(tree : CNodeRadix) → (slot : Slot) → CNodeRadix` | O(1) |
| `CNodeRadix.fold` | `(tree : CNodeRadix) → (init : β) → (f : β → Slot → Capability → β) → β` | O(2^radixW) |
| `CNodeRadix.toList` | `(tree : CNodeRadix) → List (Slot × Capability)` | O(2^radixW) |

**Lookup implementation**:
```lean
def CNodeRadix.lookup (tree : CNodeRadix) (slot : Slot) : Option Capability :=
  let idx := extractBits slot.toNat 0 tree.radixWidth
  tree.slots[idx.val]'(by rw [tree.hSlotSize]; exact idx.isLt)
```

This is a single array access — O(1), zero hashing, Fin-bounded.

**Gate**: `lake build SeLe4n.Kernel.RadixTree.Core` + zero sorry

#### Q4-C: Radix Tree Invariants and Proofs

**New file**: `SeLe4n/Kernel/RadixTree/Invariant.lean`

**Proof obligations (12)**:
- `lookup_insert_self` — after insert, lookup returns inserted value
- `lookup_insert_ne` — insert at slot `s` doesn't affect lookup at `s'` when `s ≠ s'`
- `lookup_erase_self` — after erase, lookup returns `none`
- `lookup_erase_ne` — erase doesn't affect other slots
- `lookup_empty` — empty tree always returns `none`
- `insert_idempotent` — inserting same value twice is identity
- `fold_visits_all` — fold visits every occupied slot exactly once
- `toList_complete` — toList contains every occupied entry
- `toList_noDup` — toList has no duplicate keys
- `size_insert_le` — size increases by at most 1
- `size_erase_le` — size only decreases
- `WF_preserved` — well-formedness preserved by all operations

These proofs are substantially simpler than Robin Hood proofs because:
- No displacement, no backshift, no load factor
- Fixed-size array (no resize)
- Direct indexing via `extractBits` (no probing)

**Gate**: `lake build SeLe4n.Kernel.RadixTree.Invariant` + zero sorry

#### Q4-D: Builder Equivalence Bridge

**New file**: `SeLe4n/Kernel/RadixTree/Bridge.lean`

**Construction function**:
```lean
def buildCNodeRadix (rt : RHTable Slot Capability) (config : CNodeConfig) :
    CNodeRadix :=
  let empty := CNodeRadix.empty config.guardWidth config.guardValue config.radixWidth
  rt.fold empty (fun tree slot cap => tree.insert slot cap)
```

**Core equivalence theorem**:
```lean
theorem buildCNodeRadix_lookup_equiv
    (rt : RHTable Slot Capability) (config : CNodeConfig) (slot : Slot)
    (hInvExt : rt.invExt) (hNoDup : rt.invExt.noDupKeys)
    (hBound : ∀ s, rt.contains s → extractBits s.toNat 0 config.radixWidth
              unique for all keys in rt) :
    rt.get? slot = (buildCNodeRadix rt config).lookup slot
```

**Additional bridge lemmas**:
- `buildCNodeRadix_preserves_size` — entry count preserved
- `buildCNodeRadix_preserves_membership` — `rt.contains k ↔ tree.lookup k ≠ none`
- `buildCNodeRadix_deterministic` — same RHTable + config → same tree

**Gate**: `lake build SeLe4n.Kernel.RadixTree.Bridge` + zero sorry

---

### Phase Q5: FrozenSystemState + Freeze

**Target version**: v0.21.0
**Goal**: Define the frozen execution-phase state representation and implement
the `freeze` function with explicit capacity planning.

#### Q5-A: FrozenMap and FrozenSet Types

**New file**: `SeLe4n/Model/FrozenState.lean`

```lean
/-- A frozen key-value store: dense array + pre-computed index. -/
structure FrozenMap (κ : Type) (ν : Type) [BEq κ] [Hashable κ] where
  data     : Array ν
  indexMap  : RHTable κ (Fin data.size)
  hInject  : ∀ k₁ k₂ i, indexMap.get? k₁ = some i →
                         indexMap.get? k₂ = some i → k₁ == k₂
  hCoverage: ∀ k v, (∃ orig_v, ...) → ∃ i, indexMap.get? k = some i

/-- Runtime lookup: index lookup + array access. -/
def FrozenMap.get? (fm : FrozenMap κ ν) (k : κ) : Option ν :=
  match fm.indexMap.get? k with
  | none => none
  | some idx => some fm.data[idx]

/-- Runtime mutation: in-place array update at existing index. -/
def FrozenMap.set (fm : FrozenMap κ ν) (k : κ) (v : ν) :
    Option (FrozenMap κ ν) :=
  match fm.indexMap.get? k with
  | none => none
  | some idx => some { fm with data := fm.data.set idx v }

/-- A frozen set: membership via FrozenMap's index. -/
def FrozenSet (κ : Type) [BEq κ] [Hashable κ] := FrozenMap κ Unit
```

#### Q5-B: FrozenSystemState Definition

```lean
structure FrozenSystemState where
  -- Core maps (FrozenMap)
  objects           : FrozenMap ObjId KernelObject
  irqHandlers       : FrozenMap Irq ObjId
  asidTable         : FrozenMap ASID ObjId
  serviceRegistry   : FrozenMap ServiceId ServiceRegistration
  interfaceRegistry : FrozenMap InterfaceId InterfaceSpec
  services          : FrozenMap ServiceId ServiceGraphEntry

  -- CDT (FrozenMap — dual index)
  cdtChildMap       : FrozenMap CdtNodeId (List CdtNodeId)
  cdtParentMap      : FrozenMap CdtNodeId CdtNodeId
  cdtSlotNode       : FrozenMap SlotRef CdtNodeId
  cdtNodeSlot       : FrozenMap CdtNodeId SlotRef
  cdtEdges          : List CapDerivationEdge  -- proof anchor (retained)
  cdtNextNode       : CdtNodeId

  -- Scheduler (FrozenMap for RunQueue)
  scheduler         : FrozenSchedulerState

  -- Lifecycle metadata (FrozenMap)
  objectTypes       : FrozenMap ObjId KernelObjectType
  capabilityRefs    : FrozenMap SlotRef CapTarget

  -- Non-map fields (retained as-is)
  machine           : MachineState
  objectIndex       : List ObjId

structure FrozenSchedulerState where
  byPriority      : FrozenMap Priority (List ThreadId)
  threadPriority  : FrozenMap ThreadId Priority
  membership      : FrozenSet ThreadId
  current         : Option ThreadId
  activeDomain    : DomainId
  domainTimeRemaining : Nat
  domainSchedule  : List DomainScheduleEntry
  domainScheduleIndex : Nat
```

**Per-object frozen structures** (embedded in `FrozenMap ObjId KernelObject`):
- CNode: `slots` field is `CNodeRadix` (from Q4) instead of `RHTable`
- VSpaceRoot: `mappings` field is `FrozenMap VAddr (PAddr × PagePerms)`

This requires a `FrozenKernelObject` variant or a `freezeObject` function
that converts per-object embedded maps.

#### Q5-C: Freeze Function

```lean
/-- Convert a builder-phase RHTable to a frozen dense array + index. -/
def freezeMap [BEq κ] [Hashable κ] (rt : RHTable κ ν) (h : rt.invExt) :
    FrozenMap κ ν :=
  let entries := rt.toList
  let data := entries.map (·.2) |>.toArray
  let indexMap := entries.enum.foldl (fun idx (i, (k, _)) =>
    idx.insert k ⟨i, by omega⟩) (RHTable.empty 16)
  { data, indexMap, hInject := by ..., hCoverage := by ... }

/-- Freeze a CNode's slots into a radix array. -/
def freezeCNodeSlots (cn : CNode) (h : cn.slotsUnique) : CNodeRadix :=
  buildCNodeRadix cn.slots ⟨cn.guardWidth, cn.guardValue, cn.radixWidth⟩

/-- Freeze an individual kernel object. -/
def freezeObject (obj : KernelObject) : FrozenKernelObject :=
  match obj with
  | .cnode cn => .cnode (freezeCNode cn)
  | .vspaceRoot vs => .vspaceRoot (freezeVSpaceRoot vs)
  | other => other  -- TCB, Endpoint, Notification, Untyped unchanged

/-- Master freeze function. -/
def freeze (ist : IntermediateState) : FrozenSystemState := ...
```

#### Q5-D: Capacity Planning

**Pre-allocation strategy (audit issue #10, #16)**:

During freeze, the dense arrays are sized based on current population plus
headroom for runtime object creation:

```lean
def objectCapacity (ist : IntermediateState) : Nat :=
  -- Count available untyped memory slots as potential future objects
  let untypedSlots := ist.state.objects.fold 0 (fun acc _ obj =>
    match obj with
    | .untyped u => acc + (u.regionSize / minObjectSize)
    | _ => acc)
  ist.state.objects.size + untypedSlots
```

For maps that don't grow at runtime (irqHandlers, asidTable), the frozen
array is sized exactly to current population.

For maps that may grow (objects, serviceRegistry), the frozen array includes
pre-allocated `none` slots for potential future entries, and the index map
includes mappings for all potential keys.

**Gate**: `lake build` + `test_smoke.sh` + zero sorry

---

### Phase Q6: Freeze Correctness Proofs

**Target version**: v0.21.1
**Goal**: Prove that freeze preserves all lookup semantics and kernel invariants.

#### Q6-A: Per-Map Lookup Equivalence (6+ theorems)

**New file**: `SeLe4n/Model/FreezeProofs.lean`

For each map type, prove:

```lean
theorem lookup_freeze_objects (ist : IntermediateState) (k : ObjId) :
    ist.state.objects.get? k = (freeze ist).objects.get? k

theorem lookup_freeze_irqHandlers (ist : IntermediateState) (k : Irq) :
    ist.state.irqHandlers.get? k = (freeze ist).irqHandlers.get? k

-- ... analogous for asidTable, serviceRegistry, interfaceRegistry,
--     services, cdtChildMap, cdtParentMap, cdtSlotNode, cdtNodeSlot,
--     objectTypes, capabilityRefs (12 theorems total)
```

**Proof strategy**: Each follows the same pattern:
1. `freezeMap` constructs data/index from `toList`
2. `toList` preserves all entries (by `RHTable` bridge lemma `toList_complete`)
3. Index construction maps each key to its `toList` position
4. Array access at that position returns the corresponding value

#### Q6-B: CNode Radix Lookup Equivalence

```lean
theorem lookup_freeze_cnode (cn : CNode) (slot : Slot) (h : cn.slotsUnique) :
    cn.slots.get? slot = (freezeCNodeSlots cn h).lookup slot
```

Follows from `buildCNodeRadix_lookup_equiv` (Q4-D).

#### Q6-C: Structural Properties (5 theorems)

- `freeze_deterministic` — same IntermediateState → same FrozenSystemState
- `freeze_preserves_size` — entry counts preserved for each map
- `freeze_preserves_membership` — contains equivalence for each map
- `freeze_no_duplicates` — follows from `invExt.noDupKeys`
- `freeze_total_coverage` — every builder key maps to a valid `Fin`

#### Q6-D: Invariant Transfer

**Keystone theorem**:
```lean
theorem freeze_preserves_invariants (ist : IntermediateState)
    (hInv : apiInvariantBundle ist.state) :
    apiInvariantBundle_frozen (freeze ist)
```

Each invariant predicate references state through lookups. Since lookup
equivalence is proven (Q6-A/Q6-B), each invariant transfers automatically.
Define `apiInvariantBundle_frozen` that mirrors `apiInvariantBundle` but
over `FrozenSystemState`.

**Gate**: `lake build` + all proofs compile + zero sorry


---

### Phase Q7: Frozen Kernel Operations

**Target version**: v0.22.0
**Goal**: Rewrite kernel transition functions to operate on `FrozenSystemState`,
using `Fin`-indexed array access. Establish the commutativity property between
builder and frozen operations.

#### Q7-A: Frozen Kernel Monad

**New file**: `SeLe4n/Model/FrozenKernel.lean`

```lean
abbrev FrozenKernel := KernelM FrozenSystemState KernelError

def FrozenKernel.lookupObject (id : ObjId) : FrozenKernel KernelObject :=
  fun st =>
    match st.objects.get? id with
    | some obj => .ok obj st
    | none => .error .objectNotFound st
```

**Design constraints**:
1. Use `FrozenMap.get?` for all lookups (index + array access)
2. Use `FrozenMap.set` for mutations (in-place array update at existing index)
3. Index map is **never modified** after freeze
4. All `Fin` accesses are within bounds by construction
5. No fuel needed (no dynamic resizing, no probing)

#### Q7-B: Object Mutation Model

`FrozenMap.set` updates the dense array at an existing index without
modifying the index map:

```lean
def FrozenMap.set (fm : FrozenMap κ ν) (k : κ) (v : ν) :
    Option (FrozenMap κ ν) :=
  match fm.indexMap.get? k with
  | none => none  -- key not in frozen state → error
  | some idx => some { fm with data := fm.data.set idx v }
```

**Value-only mutations (audit issue #11)**:

The commutativity diagram `f(freeze(s)) = freeze(f(s))` holds **only** for
operations that modify values at existing keys, not operations that add or
remove keys from a map. This scopes the frozen operations:

| Operation Type | Examples | Frozen Support | Commutativity |
|---------------|----------|----------------|---------------|
| **Value update** | TCB state change (IPC), endpoint queue update, notification badge | Yes | Proven |
| **Key addition** | `storeObject` (new object), CNode slot insert | Conditional | Pre-allocated slots only |
| **Key removal** | Object deletion, CNode slot erase | Yes (set to `none`) | Proven |
| **Builder-only** | `lifecycleRetype` (new untyped carve-out) | No | N/A |

For **key addition** in frozen state: the object already has a pre-allocated
`none` slot in the dense array (from Q5-D capacity planning). "Adding" an
object is setting its slot from `none` to `some obj`. The index map already
contains the key (mapped at freeze time to a `none` slot).

#### Q7-C: Per-Subsystem Frozen Operations

Each kernel subsystem gets a frozen counterpart:

| Subsystem | Builder Operation | Frozen Operation | Key Change |
|-----------|-------------------|------------------|------------|
| **Scheduler** | `schedule` | `frozenSchedule` | `FrozenMap.get?` for objects |
| **Scheduler** | `handleYield` | `frozenHandleYield` | RunQueue via `FrozenMap` |
| **Scheduler** | `timerTick` | `frozenTimerTick` | Array-indexed thread lookup |
| **IPC** | `endpointSend` | `frozenEndpointSend` | Queue update via `FrozenMap.set` |
| **IPC** | `endpointReceive` | `frozenEndpointReceive` | Message transfer via arrays |
| **IPC** | `endpointCall` | `frozenEndpointCall` | Combined send+receive |
| **IPC** | `endpointReply` | `frozenEndpointReply` | Reply cap resolution |
| **Capability** | `cspaceLookup` | `frozenCspaceLookup` | `CNodeRadix.lookup` (O(1)) |
| **Capability** | `cspaceMint` | `frozenCspaceMint` | Radix insert + `FrozenMap.set` |
| **Capability** | `cspaceDelete` | `frozenCspaceDelete` | Radix erase + `FrozenMap.set` |
| **VSpace** | `vspaceResolve` | `frozenVspaceResolve` | `FrozenMap.get?` for mappings |
| **Service** | `lookupServiceByCap` | `frozenLookupServiceByCap` | `FrozenMap.get?` |
| **Lifecycle** | `lifecycleRetype` | N/A | Builder-only operation |

**CNode frozen lookup** (key optimization):
```lean
def frozenCspaceLookup (st : FrozenSystemState) (cptr : CPtr) (rootId : ObjId) :
    FrozenKernel Capability :=
  match st.objects.get? rootId with
  | some (.cnode cn) =>
    let slotIdx := extractBits cptr.toNat 0 cn.radixWidth
    match cn.frozenSlots.lookup slotIdx with
    | some cap => .ok cap st
    | none => .error .invalidCapability st
  | _ => .error .objectNotFound st
```

#### Q7-D: Commutativity Proofs

For each frozen operation, prove the commutativity diagram:

```lean
/-- Generic commutativity for value-only mutations. -/
theorem frozenOp_commutes_with_freeze
    (ist : IntermediateState) (op_builder : SystemState → SystemState)
    (op_frozen : FrozenSystemState → FrozenSystemState)
    (hValueOnly : ∀ k, (op_builder ist.state).objects.contains k =
                       ist.state.objects.contains k)
    (hEquiv : ∀ k, (op_builder ist.state).objects.get? k =
                   match ist.state.objects.get? k with
                   | some v => some (transform v)
                   | none => none) :
    op_frozen (freeze ist) = freeze (op_builder ist.state) := by ...
```

**Strategy**: Prove a generic `set_freeze_commute` lemma once:
```lean
theorem FrozenMap.set_freeze_commute (rt : RHTable κ ν) (k : κ) (v : ν) :
    (freezeMap rt).set k v = freezeMap (rt.insert k v)
```
Then instantiate per-operation.

#### Q7-E: Frozen Invariant Preservation

For each frozen operation, prove subsystem invariants are preserved:
- `frozenEndpointSend_preserves_ipcInvariant`
- `frozenSchedule_preserves_schedulerInvariant`
- `frozenCspaceMint_preserves_capabilityInvariant`
- etc.

These follow from the commutativity proofs + builder-phase preservation proofs.

**Gate**: `lake build` + `test_full.sh` + zero sorry + all commutativity
diagrams proven for value-update operations

---

### Phase Q8: Rust Syscall Wrappers (WS-O Integration)

**Absorbs**: WS-O phases O1–O8
**Target version**: v0.22.0 (parallel with Q4–Q7)
**Goal**: Deliver `libsele4n`, a `no_std` Rust userspace library with safe
syscall wrappers for all 14 seLe4n syscalls.

**Dependency**: Q8 depends only on Q1 (finalized syscall surface). It is
independent of Q2–Q7, enabling parallel execution.

#### Q8-A: Foundation Crate — `sele4n-types`

**New directory**: `rust/sele4n-types/`

- 14 newtype wrappers: `ObjId`, `ThreadId`, `CPtr`, `Slot`, `DomainId`,
  `Priority`, `Deadline`, `Irq`, `ServiceId`, `Badge`, `Asid`, `VAddr`,
  `PAddr`, `RegValue`
- `KernelError` enum (13+ variants, 1:1 mapping from Lean)
- `AccessRight` enum (5 rights) + `AccessRights` bitmask
- `SyscallId` enum (14 variants — updated post-Q1):
  IPC: Send(0), Receive(1), Call(2), Reply(3);
  CSpace: Mint(4), Copy(5), Move(6), Delete(7);
  Lifecycle: Retype(8); VSpace: Map(9), Unmap(10);
  Service: Register(11), Revoke(12), Query(13)
- `#![no_std]`, `#![deny(unsafe_code)]`, zero external deps

**Gate**: `cargo build --target aarch64-unknown-none`

#### Q8-B: ABI Crate — `sele4n-abi`

**New directory**: `rust/sele4n-abi/`

- `MessageInfo` bitfield (length ≤ 120, extra_caps ≤ 3)
- `SyscallRequest`/`SyscallResponse` register structures
- ARM64 register layout: x0=CPtr, x1=MessageInfo, x2-x5=msg_regs,
  x7=reply/status, x8=SyscallId
- `raw_syscall`: inline `svc #0` (the **single** `unsafe` block)
- `invoke_syscall`: safe wrapper
- Per-syscall argument structures (10 types)
- `TypeTag` enum (6 variants), `PagePerms` bitmask (W^X)
- Round-trip property tests + mock `svc` for host testing

**Gate**: `cargo test --features std` passes

#### Q8-C: Syscall Crate — `sele4n-sys`

**New directory**: `rust/sele4n-sys/`

- `IpcMessage` builder (≤ 120 regs, ≤ 3 caps)
- IPC: `endpoint_send`, `receive`, `call`, `reply`, `reply_receive`
- Notification: `signal` (badge OR), `wait`
- CSpace: `mint` (rights subsetting), `copy`, `move`, `delete`
- Lifecycle: `retype` + convenience constructors
- VSpace: `map` (W^X pre-check), `unmap`
- Service: `register`, `revoke`, `query`
- Phantom-typed caps: `Cap<Obj, Rts>` with sealed traits
- Rights downgrading: `Cap::downgrade::<NewRts>()`
- Zero `unsafe`; `#[must_use]` on all `KernelResult`

**Gate**: All 14 syscalls wrapped, `cargo test --features std`

#### Q8-D: Conformance Testing + CI

- Extend `MainTraceHarness.lean` with `[RUST-XVAL-*]` test vectors
- `rust/tests/conformance.rs` — register-by-register ABI validation
- `scripts/test_rust.sh` — Cargo build + test + conformance
- Integrate into test_smoke.sh (Tier 2)
- `trybuild` compile-fail tests for phantom type safety
- `proptest` property tests for encode/decode roundtrips

**Gate**: Conformance passes for all 14 syscalls, `test_smoke.sh` includes Rust

---

### Phase Q9: Integration Testing + Documentation

**Target version**: v0.23.0
**Goal**: Comprehensive testing of the two-phase architecture, full
documentation sync.

#### Q9-A: Two-Phase Architecture Tests

| ID | Description | Phase | Expected |
|----|-------------|-------|----------|
| TPH-001 | Build IntermediateState from empty + objects | Builder | allTablesInvExt |
| TPH-002 | Freeze empty IntermediateState | Freeze | empty FrozenSystemState |
| TPH-003 | Freeze populated state, verify lookup equiv | Freeze | all lookups match |
| TPH-004 | CNode RHTable → CNodeRadix lookup equiv | Freeze | slot-by-slot match |
| TPH-005 | Frozen IPC send/receive | Execution | correct message transfer |
| TPH-006 | Frozen scheduler tick | Execution | correct thread selection |
| TPH-007 | Frozen CSpace lookup (radix) | Execution | correct capability |
| TPH-008 | Frozen VSpace resolve | Execution | correct page mapping |
| TPH-009 | Frozen service query | Execution | correct registration |
| TPH-010 | Commutativity: builder then freeze = freeze then frozen | Both | equal states |
| TPH-011 | Determinism: freeze twice → identical | Freeze | byte-equal |
| TPH-012 | Pre-allocated slot: retype in frozen state | Execution | slot fills correctly |
| TPH-013 | Delete in frozen state: slot cleared to none | Execution | lookup returns none |
| TPH-014 | RunQueue operations in frozen state | Execution | correct scheduling |

#### Q9-B: Rust Conformance Tests (RUST-XVAL-001 through XVAL-014)

Register-by-register ABI validation for all 14 syscalls.

#### Q9-C: Service Interface Tests (SRG-001 through SRG-010)

Integrated from Q1-F into the two-phase test suite.

#### Q9-D: Documentation Sync

**Modified files (15+)**:

| File | Update |
|------|--------|
| `docs/WORKSTREAM_HISTORY.md` | WS-Q entry (absorbs WS-P, WS-O) |
| `docs/spec/SELE4N_SPEC.md` | Two-phase architecture, service interface, Rust wrappers |
| `docs/DEVELOPMENT.md` | Builder/freeze workflow, Rust build instructions |
| `docs/CLAIM_EVIDENCE_INDEX.md` | Freeze-equivalence claims, radix tree correctness |
| `README.md` | Metrics sync |
| `CLAUDE.md` | Source layout update, active workstream |
| `docs/gitbook/03-architecture-and-module-map.md` | Two-phase diagram |
| `docs/gitbook/04-project-design-deep-dive.md` | Builder/freeze design rationale |
| `docs/gitbook/05-specification-and-roadmap.md` | Milestone table |
| `docs/gitbook/12-proof-and-invariant-map.md` | Freeze proofs, radix invariants |
| `docs/gitbook/15-rust-syscall-wrappers.md` | New chapter |
| `docs/codebase_map.json` | Regenerate |
| `scripts/website_link_manifest.txt` | Verify/update |
| `scripts/test_smoke.sh` | Rust integration (Tier 2) |
| `scripts/test_full.sh` | Two-phase tests (Tier 3) |

**Gate**: `test_full.sh` + `generate_codebase_map.py --pretty --check`


---

## 6. Estimated Scope (Revised)

| Phase | Sub-phases | New Lines | Removed | Modified Files | New Files |
|-------|-----------|-----------|---------|----------------|-----------|
| Q1 | 7 | ~1,150 | ~800 | ~22 | 3 |
| Q2 | 10 | ~1,800 | ~300 | ~35 | 2 |
| Q3 | 3 | ~400 | 0 | 2 | 3 |
| Q4 | 4 | ~800 | 0 | 2 | 3 |
| Q5 | 4 | ~600 | 0 | 3 | 2 |
| Q6 | 4 | ~900 | 0 | 2 | 1 |
| Q7 | 5 | ~1,800 | ~300 | ~20 | 2 |
| Q8 | 4 | ~3,000 | 0 | 3 | ~20 |
| Q9 | 4 | ~500 | ~200 | ~18 | 2 |
| **Total** | **45** | **~10,950** | **~1,600** | **~55 unique** | **~38** |

**Comparison to Rev 1**: +1,300 new lines (primarily Q2 Prelude lemmas + RHSet +
RunQueue migration), reflecting the true scope discovered during audit.

**Lean proof surface expansion**: ~4,100 lines of new proofs
(Q2-A/B: ~500, Q3: ~300, Q4-C/D: ~600, Q6: ~900, Q7-D/E: ~1,800).

**Rust library**: ~3,000 lines across 3 crates (unchanged from Rev 1).

---

## 7. Dependency Graph

```
Q1-A → Q1-B → Q1-C → Q1-D → Q1-E1 → Q1-E2 → Q1-F → Q1-G
  │                                                      │
  └─────────────────────────────→ Q8-A → Q8-B → Q8-C → Q8-D ──┐
                                                                │
Q2-A ──→ Q2-B ──→ Q2-C ──→ Q2-D ──→ Q2-E ──→ Q2-F            │
                    │                   │                       │
                    │                   └──→ Q2-G ──→ Q2-H     │
                    │                                   │       │
                    └────────────────────────────────→ Q2-I     │
                                                        │       │
                                                      Q2-J      │
                                                        │       │
                                                      Q3-A      │
                                                        │       │
                                            ┌──→ Q3-B ──┤       │
                                            │     │     │       │
                                            │   Q3-C    │       │
                                            │           │       │
                                          Q4-A ──→ Q4-B │       │
                                            │       │   │       │
                                          Q4-C ──→ Q4-D │       │
                                            │           │       │
                                            └──→ Q5-A ──┘       │
                                                  │             │
                                            Q5-B → Q5-C → Q5-D │
                                                        │       │
                                                      Q6-A      │
                                                        │       │
                                                Q6-B → Q6-C     │
                                                        │       │
                                                      Q6-D      │
                                                        │       │
                                            Q7-A → Q7-B → Q7-C │
                                                        │       │
                                                Q7-D → Q7-E     │
                                                        │       │
                                                        └───┬───┘
                                                            │
                                                    Q9-A → Q9-D
```

**Critical path length**: 36 sub-phases (Q1×7 → Q2×10 → Q3×3 → Q4×4 →
Q5×4 → Q6×4 → Q7×5 → Q9 selective)

**Parallel path**: Q8×4 (runs alongside Q2–Q7, joins at Q9)

**Q2 internal parallelism**: After Q2-C, subphases Q2-D/Q2-E/Q2-F/Q2-G can
proceed in parallel (they touch disjoint file sets). Q2-H depends on Q2-C
(service maps reference objects map). Q2-I waits for all map migrations.

---

## 8. Risk Analysis

### Risk 1: Q2 Migration Breadth (CRITICAL)

**Description**: Q2 touches 35+ files, 78 HashMap + 57 HashSet occurrences,
requires 42+ new Prelude lemmas. This is the single largest risk in the plan.

**Likelihood**: HIGH | **Impact**: HIGH

**Mitigation**:
- Q2-A (Prelude lemmas) is the critical enabler — complete it first
- Migrate one atomic group at a time (A→B→C→D→E→F→G→H→I→J)
- Run `lake build` after each file change, not just each subphase
- The WS-N4 CNode migration (20+ files) provides a proven template
- RunQueue (Q2-G) is highest-density: isolate it and test exhaustively

### Risk 2: RunQueue Proof Repair (HIGH)

**Description**: RunQueue.lean has 92 callsites and Preservation.lean has
2,170 lines of proofs depending on HashMap/HashSet membership semantics.

**Likelihood**: MEDIUM | **Impact**: HIGH

**Mitigation**:
- RHTable/RHSet bridge lemmas (Q2-A/Q2-B) provide matching API signatures
- Most proofs use `contains_insert_self`/`contains_erase_ne` patterns that
  map directly to existing bridge lemmas
- Budget extra time for Q2-G — it may be the longest single subphase

### Risk 3: Freeze Function Correctness (HIGH)

**Description**: `freezeMap` must produce well-formed `FrozenMap` where every
`Fin` index is valid and every lookup is equivalent. Proof of `lookup_freeze_equiv`
requires reasoning about `toList` ordering, enumeration indexing, and fold
accumulation.

**Likelihood**: MEDIUM | **Impact**: HIGH

**Mitigation**:
- Build `freezeMap` as standalone generic function with its own proof module
- Prove `toList` completeness in Bridge.lean first (extend existing bridge)
- Use `native_decide` for finite-domain equivalence checks in tests
- `invExt.noDupKeys` simplifies injection proofs

### Risk 4: CNode Radix Simplification (LOW — improved from Rev 1)

**Description**: Rev 1 proposed a deep recursive radix tree. The audit revealed
that seLe4n CNodes are single-level (guard + one radix level). Rev 2 uses a
flat `2^radixWidth`-entry array, which is dramatically simpler.

**Likelihood**: LOW | **Impact**: LOW

**Mitigation**: Flat array proofs are trivial (direct `Fin` indexing, no
recursion, no displacement). Most proofs will close with `simp` + `omega`.

### Risk 5: FrozenMap Index Hashing (MEDIUM — new in Rev 2)

**Description**: The `FrozenMap.indexMap` is an `RHTable` that performs hash
computation at lookup time, contradicting the "no runtime hashing" goal for
non-CNode maps.

**Likelihood**: HIGH (by design) | **Impact**: LOW

**Mitigation**: This is an accepted trade-off documented in §3.1. CNode
lookups (the hottest path) use zero-hash radix indexing. Object/service/IRQ
lookups use verified RHTable hashing, which is still O(1) amortized and
superior to `Std.HashMap` (verified vs unverified). Future optimization:
replace `indexMap` with perfect hash function computed at freeze time.

### Risk 6: Pre-Allocation Sizing (MEDIUM)

**Description**: Q5-D pre-allocates `Option` slots for potential future objects.
If the capacity estimate is too small, runtime retype operations fail. If too
large, memory is wasted.

**Likelihood**: MEDIUM | **Impact**: MEDIUM

**Mitigation**: Capacity is derived from actual untyped memory regions (known
at boot time). Over-allocation by a small constant factor (1.1×) provides
headroom. seL4's model bounds total objects by physical memory.

### Risk 7: Commutativity Scope (LOW — scoped in Rev 2)

**Description**: The commutativity diagram only holds for value-update
operations (audit issue #11). Key-set operations are builder-only.

**Likelihood**: LOW (by design) | **Impact**: LOW

**Mitigation**: Rev 2 explicitly scopes commutativity to value-update
operations. Key-set operations (retype, delete) use the pre-allocation
model (setting `none` ↔ `some`), which is a value update on the `Option`
wrapper. No structural key-set changes occur in frozen state.

---

## 9. Success Criteria

### 9.1 Architectural
- [ ] Zero `Std.HashMap`/`Std.HashSet` in any kernel state type
- [ ] Algorithm-local `Std.HashSet` permitted (documented)
- [ ] `IntermediateState` uses `RHTable`/`RHSet` exclusively
- [ ] `FrozenSystemState` uses `FrozenMap`/`FrozenSet` + `CNodeRadix`
- [ ] All 16 RHTable + 2 RHSet instances satisfy `invExt`
- [ ] `allTablesInvExt` predicate defined and proven for default state
- [ ] Service lifecycle removed from kernel; registration is capability-mediated
- [ ] CNode frozen lookup uses O(1) radix indexing (zero hashing)
- [ ] Rust library compiles for `aarch64-unknown-none`

### 9.2 Formal
- [ ] 42+ Prelude lemma equivalents proven for RHTable/RHSet
- [ ] 12+ `lookup_freeze_*` theorems proven (one per map)
- [ ] `lookup_freeze_cnode` (RHTable → CNodeRadix equivalence)
- [ ] `freeze_deterministic`, `freeze_preserves_size`, `freeze_preserves_membership`
- [ ] `freeze_preserves_invariants` (apiInvariantBundle transfer)
- [ ] Commutativity proven for all value-update frozen operations
- [ ] CNodeRadix: 12 correctness proofs (lookup/insert/erase/fold)
- [ ] RHSet: 14 bridge lemmas
- [ ] Registry invariants proven (registryEndpointValid, registryInterfaceValid)
- [ ] Zero `sorry`/`axiom` in production proof surface

### 9.3 Runtime
- [ ] O(1) object lookup in frozen state (FrozenMap: index + array)
- [ ] O(1) CNode slot lookup (CNodeRadix: direct array access)
- [ ] No dynamic memory allocation in frozen kernel operations
- [ ] Cache-friendly dense array storage for all frozen maps
- [ ] Pre-allocated Option slots for runtime object creation
- [ ] Deterministic memory image (identical boot → identical state)

### 9.4 Rust Library
- [ ] 14 syscalls wrapped (updated from WS-O's 13)
- [ ] `cargo build --target aarch64-unknown-none` succeeds
- [ ] Exactly one `unsafe` block (inline `svc #0`)
- [ ] Cross-validation: register-by-register ABI match with Lean
- [ ] Phantom-typed `Cap<Obj, Rts>` prevents wrong-rights at compile time
- [ ] `#[must_use]` on all `KernelResult` returns
- [ ] Zero external dependencies in `sele4n-types`

### 9.5 Documentation
- [ ] WORKSTREAM_HISTORY.md updated with WS-Q entry
- [ ] SELE4N_SPEC.md reflects two-phase architecture
- [ ] DEVELOPMENT.md updated with builder/freeze workflow + Rust build
- [ ] CLAIM_EVIDENCE_INDEX.md updated with freeze-equivalence claims
- [ ] GitBook chapters updated (5 existing + 1 new Rust chapter)
- [ ] codebase_map.json regenerated
- [ ] Website link manifest verified

---

## 10. Verification Commands

**After each sub-phase**:
```bash
source ~/.elan/env && lake build <Module.Path>  # Mandatory per-module
./scripts/test_fast.sh                           # Tier 0+1
```

**After each phase**:
```bash
./scripts/test_smoke.sh                          # Tier 0-2 (minimum)
```

**After Q7 (frozen operations complete)**:
```bash
./scripts/test_full.sh                           # Tier 0-3
```

**After Q8 (Rust wrappers)**:
```bash
cd rust && cargo build --target aarch64-unknown-none
cd rust && cargo test --features std
./scripts/test_rust.sh
```

**After Q9 (documentation)**:
```bash
./scripts/generate_codebase_map.py --pretty --check
./scripts/test_full.sh
```

---

## 11. New Source Layout (Post WS-Q)

```
SeLe4n/
├── Prelude.lean                          Extended: InterfaceId, RHTable lemmas
├── Machine.lean                          Unchanged
├── Model/
│   ├── Object/
│   │   ├── Types.lean                    Updated: ServiceRegistration, no ServiceStatus
│   │   └── Structures.lean               Updated: CNode with CNodeRadix option
│   ├── State.lean                        Updated: all RHTable/RHSet, no Std.HashMap
│   ├── IntermediateState.lean            NEW: builder state + invariant witness
│   ├── FrozenState.lean                  NEW: FrozenMap, FrozenSet, FrozenSystemState
│   ├── FreezeProofs.lean                 NEW: 12+ lookup equivalence proofs
│   ├── FrozenKernel.lean                 NEW: frozen kernel monad + ops
│   └── Builder.lean                      NEW: builder operations
├── Kernel/
│   ├── RobinHood/
│   │   ├── Core.lean                     Unchanged
│   │   ├── Bridge.lean                   Extended: toList completeness
│   │   ├── Set.lean                      NEW: RHSet type + 14 bridge lemmas
│   │   ├── HashPolicy.lean               NEW: determinism proofs
│   │   └── Invariant/                    Unchanged
│   ├── RadixTree/                        NEW (Q4)
│   │   ├── Core.lean                     CNodeRadix type + O(1) operations
│   │   ├── Invariant.lean                12 correctness proofs
│   │   └── Bridge.lean                   RHTable ↔ CNodeRadix equivalence
│   ├── Service/
│   │   ├── Interface.lean                NEW: InterfaceSpec, ServiceRegistration
│   │   ├── Registry.lean                 NEW: 4 registry operations
│   │   ├── Registry/Invariant.lean       NEW: registry invariants
│   │   ├── Operations.lean               Updated: lifecycle ops removed
│   │   └── Invariant/                    Updated: simplified
│   ├── Scheduler/                        Updated: RHTable/RHSet + frozen ops
│   ├── IPC/                              Updated: frozen operations
│   ├── Capability/                       Updated: CNodeRadix lookup
│   ├── Lifecycle/                        Updated: builder-only annotation
│   ├── Architecture/                     Updated: new SyscallIds
│   ├── InformationFlow/                  Updated: service NI proofs
│   └── API.lean                          Updated: new service API
├── Platform/
│   ├── Boot.lean                         NEW: boot → IntermediateState
│   └── ...                               Existing
└── Testing/                              Updated: two-phase + service tests

rust/                                      NEW (Q8)
├── Cargo.toml                            Workspace root
├── sele4n-types/                         Core types (no_std, no unsafe)
├── sele4n-abi/                           Register ABI (1 unsafe block)
├── sele4n-sys/                           Safe wrappers (no unsafe)
└── tests/conformance.rs                  Lean cross-validation
```

---

## 12. Relationship to Hardware Binding (H3)

The two-phase architecture directly enables the Raspberry Pi 5 hardware target:

- **Builder phase**: Runs during boot on BCM2712. Platform config (GIC-400 IRQ
  table, MMIO regions, initial memory layout) populates `IntermediateState`
  via builder operations.
- **Freeze**: Executed once after boot, producing a `FrozenSystemState` with
  deterministic, contiguous memory layout suitable for identity-mapping during
  early boot on Cortex-A76.
- **Execution phase**: Dense array access is cache-friendly for the Cortex-A76
  L1/L2 hierarchy. CNode radix lookups are O(1) with no probing. RunQueue
  operations use pre-computed frozen arrays.
- **Rust wrappers**: `sele4n-abi` encodes the ARM64 `svc #0` trap. H3 builds
  the kernel-side trap handler using the same register ABI.

---

## 13. Design Principles

> **P1. The kernel enforces constraints — it does not decide behavior.**
> Service lifecycle belongs in user space. The kernel enforces capability
> safety and interface contracts.

> **P2. Every data structure in the kernel state must be verified.**
> No `Std.HashMap` in state, no `partial`, no `get!`/`set!`, no axioms.
> Algorithm-local `Std.HashSet` for transient computation is the sole
> documented exception.

> **P3. The two-phase model separates flexibility from performance.**
> Builder: RHTable/RHSet (dynamic, verified). Frozen: dense arrays + radix
> trees (O(1), cache-friendly). The freeze function is the formal bridge.

> **P4. Determinism is non-negotiable.**
> Fixed hash, fixed probe sequence, deterministic iteration order,
> deterministic freeze. Identical boot → identical memory image.

> **P5. The Rust ABI is a contract, not an implementation detail.**
> Register layout, syscall IDs, error codes, and message encoding are
> formally specified in Lean and mechanically cross-validated in Rust.

> **P6. Break large migrations into atomic groups.**
> Maps that are updated together (storeObject's 6 fields, CDT's 4 maps,
> RunQueue's 3 maps) must migrate together. All other migrations are
> independent and can proceed in parallel.

---

**END OF MASTER PLAN (Rev 2)**

