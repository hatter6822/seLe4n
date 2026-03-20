# WS-Q Master Plan — Two-Phase Kernel State Architecture (v0.18.0+)

**Created**: 2026-03-20
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
   `Std.HashMap` from the runtime kernel state, replacing it with dense arrays,
   `Fin`-indexed access, and a verified CNode radix tree. The builder phase uses
   the proven Robin Hood hash table (WS-N, ~4,300 LoC, zero sorry) for all
   key/value stores during initialization; the freeze phase converts to a
   cache-friendly, deterministic memory image for execution.

2. **Service Interface Simplification** (absorbs WS-P) — Replaces the
   orchestration-focused service subsystem (~1,950 lines including ~1,110 lines
   of in-kernel dependency graph acyclicity proofs tied to lifecycle management)
   with a capability-indexed, formally verified interface enforcement layer.
   Lifecycle management (start/stop/restart) moves to user space per the
   microkernel principle of mechanism ≠ policy.

3. **Rust Syscall Wrappers** (absorbs WS-O) — A `no_std` userspace library
   (`libsele4n`) exposing seLe4n's verified Lean syscall semantics as safe Rust
   wrappers, encoding the finalized ABI surface after service interface changes.
   Cross-validated against Lean trace output for register-by-register fidelity.

**Why one plan?** These three efforts are deeply coupled:

- WS-P changes the syscall surface (removes `serviceStart`/`serviceStop`, adds
  `serviceRegister`/`serviceRevoke`/`serviceQuery`), which WS-O must encode.
- The two-phase architecture replaces every `Std.HashMap` in `SystemState`,
  which affects every subsystem including the new service registry from WS-P.
- The CNode radix tree replaces the RHTable-backed `CNode.slots` (WS-N4), which
  the Rust wrappers address through CSpace syscalls.

Executing them independently would require three separate migrations of the same
state types, three rounds of invariant proof repair, and three fixture updates.
Unifying them into a single orchestrated plan eliminates redundant work and
ensures each intermediate state compiles and passes tests.

---

## 2. Motivation & Architecture

### 2.1 Problem Statement

The current `SystemState` (defined in `SeLe4n/Model/State.lean`, ~1,073 lines)
uses `Std.HashMap` for 10+ key/value stores:

| Field | Type | Concern |
|-------|------|---------|
| `objects` | `Std.HashMap ObjId KernelObject` | Unverified hash, nondeterministic iteration |
| `services` | `Std.HashMap ServiceId ServiceGraphEntry` | Lifecycle policy in kernel |
| `irqHandlers` | `Std.HashMap Irq ObjId` | Unverified hash |
| `asidTable` | `Std.HashMap ASID ObjId` | Unverified hash |
| `lifecycle.objectTypes` | `Std.HashMap ObjId KernelObjectType` | Unverified hash |
| `lifecycle.capabilityRefs` | `Std.HashMap SlotRef CapTarget` | Unverified hash |
| `cdtSlotNode` | `Std.HashMap SlotRef CdtNodeId` | Unverified hash |
| `cdtNodeSlot` | `Std.HashMap CdtNodeId SlotRef` | Unverified hash |
| `cdt.childMap` | `HashMap CdtNodeId (List CdtNodeId)` | Unverified hash |
| `cdt.parentMap` | `HashMap CdtNodeId CdtNodeId` | Unverified hash |
| `objectIndexSet` | `Std.HashSet ObjId` | Unverified hash |
| `VSpaceRoot.mappings` | `Std.HashMap VAddr (PAddr × PagePerms)` | Unverified hash |

Only `CNode.slots` has been migrated to the verified `RHTable` (WS-N4). The
remaining 12 stores use `Std.HashMap` with:

- **Nondeterministic iteration order** — `Std.HashMap.fold` order depends on
  internal hash table layout, which is implementation-defined and may vary
  across Lean versions.
- **Unverified hash function** — The hash function's collision behavior is not
  formally analyzed; proofs cannot reason about lookup correctness.
- **No cache-locality guarantees** — Pointer-chasing through hash buckets
  produces unpredictable memory access patterns on ARM64.
- **No formal bridge** — Unlike `RHTable` (10 bridge lemmas, `invExt` invariant,
  3,600+ lines of proofs), `Std.HashMap` operations are trusted axiomatically.

### 2.2 Two-Phase Architecture

```
                    ┌─────────────────────────┐
                    │     Boot / Init          │
                    │  (Platform + Untyped)    │
                    └───────────┬──────────────┘
                                │
                                ▼
                    ┌─────────────────────────┐
                    │   IntermediateState      │
                    │   (Builder Phase)        │
                    │                          │
                    │  • RHTable for ALL maps  │
                    │  • Fixed hash + seed     │
                    │  • Deterministic probes  │
                    │  • Dynamic allocation    │
                    │  • Object retype fills   │
                    └───────────┬──────────────┘
                                │
                          freeze(·)
                                │
                                ▼
                    ┌─────────────────────────┐
                    │   FrozenSystemState      │
                    │   (Execution Phase)      │
                    │                          │
                    │  • Dense Array + Fin     │
                    │  • CNode RadixTree       │
                    │  • O(1) array indexing   │
                    │  • No hashing at runtime │
                    │  • Cache-friendly layout │
                    │  • Deterministic image   │
                    └─────────────────────────┘
```

**Builder Phase (IntermediateState):**
- All key/value stores use `RHTable` with a **fixed** hash function, **fixed**
  seed, and **fixed** probe sequence (Robin Hood linear probing).
- The builder state supports dynamic object creation (retype), capability
  minting, VSpace mapping, and all initialization operations.
- Every RHTable instance satisfies `invExt` (well-formedness + probe chain
  dominance + no duplicate keys) — proven in WS-N2.
- Boot sequence constructs the builder state from platform configuration and
  initial untyped memory regions.

**Freeze Phase:**
- `freeze : IntermediateState → FrozenSystemState` converts all RHTable maps
  into dense arrays with `Fin`-indexed lookup tables.
- For each map `RHTable K V`, freeze produces:
  - `data : Array V` — packed contiguous values
  - `index : K → Option (Fin data.size)` — key-to-index mapping
- CNode slots receive special treatment: converted to a **verified radix tree**
  with fixed fanout and bit-sliced traversal, matching seL4's CSpace addressing.
- The freeze function enforces:
  - **No duplicates** — guaranteed by `RHTable.invExt.noDupKeys`
  - **Total index coverage** — every key in the RHTable maps to a valid `Fin`
  - **Deterministic ordering** — sorted by key (via `Ord` instance) or by
    insertion-order (via `RHTable.toList` stability)

**Execution Phase (FrozenSystemState):**
- All kernel operations (IPC, scheduling, capability lookup, VSpace resolution)
  use `Fin`-indexed array access — no hashing, no probing, no dynamic allocation.
- Object mutation is in-place: `objects[idx] := updated_obj` where `idx : Fin n`.
- New object creation uses pre-allocated `Option` slots in the dense array,
  filled during retype and cleared during delete.
- Memory image is fully deterministic: identical boot configuration produces
  identical `FrozenSystemState` byte-for-byte.

### 2.3 CNode Radix Tree (SlotRef Handling)

The current `CNode.slots : RHTable Slot Capability` (WS-N4) is appropriate for
the builder phase but suboptimal for execution:

- CNode addressing in seL4 is inherently a **bit-sliced tree traversal**: a
  capability pointer is decoded by extracting `guardWidth` bits (guard match),
  then `radixWidth` bits (child index), recursively through CNode levels.
- A radix tree with `2^radixWidth` fanout at each level matches this addressing
  scheme exactly, enabling O(depth) lookup with no hashing.
- Array-backed radix nodes (`Array (Option Child) where Child.size = 2^radixWidth`)
  are cache-friendly and `Fin`-indexable.

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

The radix tree replaces `RHTable Slot Capability` in the frozen CNode. The
builder-phase CNode retains `RHTable` for flexibility during initialization.
The freeze step proves lookup equivalence:

```
∀ slot cap, rhTable.get? slot = some cap ↔ radixTree.lookup slot = some cap
```

### 2.4 Service Interface (WS-P Absorption)

The current service subsystem conflates mechanism with policy. This plan
absorbs WS-P's redesign:

**Retained (mechanism):**
- `serviceRegisterDependency` — dependency edge with cycle detection
- `serviceHasPathTo` — DFS cycle detection
- `serviceBfsFuel` — fuel bound for graph traversal
- ~1,110 lines of acyclicity proofs

**Added (WS-P new):**
- `InterfaceSpec` — concrete interface specification (method count, message bounds)
- `ServiceRegistration` — capability-mediated service record
- `registerInterface` / `registerService` / `lookupServiceByCap` / `revokeService`
- Registry invariants: `registryEndpointValid`, `registryInterfaceValid`

**Removed (policy → user space):**
- `serviceStart` / `serviceStop` / `serviceRestart` — lifecycle management
- `ServiceStatus` — runtime status tracking
- `ServiceConfig` — policy gates (allowStart/allowStop)
- Related frame lemmas and NI proofs

**Net effect:** ~600 line reduction with simpler invariants and a cleaner
type hierarchy that maps naturally to the two-phase architecture.

### 2.5 Rust Syscall Wrappers (WS-O Absorption)

WS-O delivers `libsele4n`, a `no_std` Rust userspace library with three crates:

| Crate | Purpose | Unsafe |
|-------|---------|--------|
| `sele4n-types` | Core typed identifiers, error types, access rights | None (`#![deny(unsafe_code)]`) |
| `sele4n-abi` | Register encoding, MessageInfo bitfield, `svc` trap | One block (inline `svc #0`) |
| `sele4n-sys` | Safe high-level syscall wrappers, IPC helpers, phantom-typed caps | None |

**Key dependency on Q1:** WS-O encodes the finalized syscall ID enumeration.
After Q1, the syscall surface changes:
- **Removed:** `serviceStart` (ID 11), `serviceStop` (ID 12)
- **Added:** `serviceRegister` (ID 11), `serviceRevoke` (ID 12), `serviceQuery` (ID 13)

WS-O is otherwise independent of the internal state architecture (Q2–Q7),
since Rust wrappers operate at the register ABI level. This enables Q8 to
execute in parallel with Q4–Q7.

---

## 3. Phase Plan Overview

| Phase | ID | Focus | Deps | Target |
|-------|----|-------|------|--------|
| 1 | **Q1** | Service interface simplification (WS-P) | — | v0.18.0 |
| 2 | **Q2** | Universal RHTable migration | Q1 | v0.19.0 |
| 3 | **Q3** | IntermediateState formalization | Q2 | v0.19.1 |
| 4 | **Q4** | CNode radix tree (verified) | Q2 | v0.20.0 |
| 5 | **Q5** | FrozenSystemState + freeze | Q3, Q4 | v0.21.0 |
| 6 | **Q6** | Freeze correctness proofs | Q5 | v0.21.1 |
| 7 | **Q7** | Frozen kernel operations | Q6 | v0.22.0 |
| 8 | **Q8** | Rust syscall wrappers (WS-O) | Q1 | v0.22.0 ∥ |
| 9 | **Q9** | Integration testing + documentation | Q7, Q8 | v0.23.0 |

**∥** = Q8 executes in parallel with Q4–Q7 (independent of internal state changes).

```
Q1 ──→ Q2 ──→ Q3 ──→ Q5 ──→ Q6 ──→ Q7 ──→ Q9
  │           │                              ▲
  │           └──→ Q4 ──┘                    │
  │                                          │
  └──────────────→ Q8 ───────────────────────┘
```


---

## 4. Detailed Phase Plans

### Phase Q1: Service Interface Simplification

**Absorbs**: WS-P phases P1–P5
**Target version**: v0.18.0
**Goal**: Replace lifecycle-focused service orchestration with capability-indexed
interface enforcement. This simplifies the type surface before the universal
RHTable migration in Q2.

#### Q1-A: Foundation Types (WS-P P1)

**New files:**
- `SeLe4n/Kernel/Service/Interface.lean` — `InterfaceSpec`, `ServiceRegistration`

**Modified files:**
- `SeLe4n/Prelude.lean` — Add `InterfaceId` typed wrapper
- `SeLe4n/Model/Object/Types.lean` — Add `ServiceRegistration` structure

**Tasks:**
1. `InterfaceId` in Prelude.lean: `Hashable`, `BEq`, `ofNat`/`toNat`/`sentinel`
2. `InterfaceSpec` with concrete fields (no universe polymorphism):
   ```lean
   structure InterfaceSpec where
     ifaceId         : InterfaceId
     methodCount     : Nat
     maxMessageSize  : Nat
     maxResponseSize : Nat
     requiresGrant   : Bool
   ```
3. `ServiceRegistration` with `sid`, `iface : InterfaceSpec`, `endpointCap : Capability`
4. `InterfaceId` roundtrip theorems matching `ServiceId` pattern
5. Verify `lake build` succeeds (purely additive, zero sorry)

**Acceptance gate:** `lake build` + `test_fast.sh`

#### Q1-B: Registry State and Operations (WS-P P2)

**New file:**
- `SeLe4n/Kernel/Service/Registry.lean` — 4 operations + 8 theorems

**Modified files:**
- `SeLe4n/Model/State.lean` — Add `serviceRegistry`, `interfaceRegistry` fields

**Operations:**

| Operation | Purpose | Error Conditions |
|-----------|---------|------------------|
| `registerInterface` | Register concrete interface spec | `illegalState` (duplicate) |
| `registerService` | Capability-mediated registration | `illegalState` (dup), `objectNotFound` (unknown iface), `invalidCapability` (bad endpoint) |
| `lookupServiceByCap` | Capability-indexed lookup (read-only) | `objectNotFound` |
| `revokeService` | Remove registration by ServiceId | `objectNotFound` |

**Minimum 8 theorems:** Error conditions, `registerService_ok_implies_registered`,
`revokeService_removes_registration`, `lookupServiceByCap_state_unchanged`,
frame lemmas (`_preserves_objects`, `_preserves_scheduler`).

**Acceptance gate:** `lake build` + `test_smoke.sh`

#### Q1-C: Registry Invariants (WS-P P3)

**New file:**
- `SeLe4n/Kernel/Service/Registry/Invariant.lean`

**Invariant definitions:**
```lean
def registryEndpointValid (st : SystemState) : Prop :=
  ∀ sid reg, st.serviceRegistry[sid]? = some reg →
    match reg.endpointCap.target with
    | .object epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
    | _ => False

def registryInterfaceValid (st : SystemState) : Prop :=
  ∀ sid reg, st.serviceRegistry[sid]? = some reg →
    st.interfaceRegistry.contains reg.iface.ifaceId

def registryInvariant (st : SystemState) : Prop :=
  registryEndpointValid st ∧ registryInterfaceValid st
```

**Proof obligations:**
- `registerService_preserves_registryInvariant`
- `revokeService_preserves_registryInvariant`
- `registerInterface_preserves_registryInvariant`
- Cross-subsystem preservation (lifecycle, capability, scheduler, IPC)
- `default_registryInvariant`
- `apiInvariantBundle` extension with `registryInvariant`

**Acceptance gate:** `lake build` + `test_smoke.sh` + zero sorry

#### Q1-D: API Integration and Syscall Dispatch (WS-P P4)

**Modified files (6):**
- `SeLe4n/Kernel/API.lean` — `apiServiceRegister`, `apiServiceRevoke`, `apiServiceQuery`
- `SeLe4n/Model/Object/Types.lean` — `SyscallId` variants: `.serviceRegister` (11), `.serviceRevoke` (12), `.serviceQuery` (13)
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — Extend `SyscallId.toNat`/`ofNat?`
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` — Decode functions for new syscalls
- `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` — `registerServiceChecked`
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` — Operation catalog update

**Acceptance gate:** `lake build` + `test_smoke.sh` + zero sorry

#### Q1-E: Legacy Deprecation (WS-P P5)

**Strategy:** Rename `services` → `servicesLegacy` to surface all callsites via
compile errors, then fix each individually.

**Removals:**
- `serviceStart`, `serviceStop`, `serviceRestart` (lifecycle → user space)
- `ServiceStatus` enum (runtime status → user space)
- `ServiceConfig` structure (policy gates → user space)
- `setServiceStatusState`, `dependenciesSatisfied` helpers
- Status-related frame lemmas in `Acyclicity.lean`
- Related NI proofs in Information Flow subsystem

**Retained:**
- `serviceRegisterDependency`, `serviceHasPathTo`, `serviceBfsFuel`
- All acyclicity proofs (~1,110 lines, minus status-related frame lemmas)
- `ServiceGraphEntry` (simplified: drops `status` field)

**Modified files (~15):** Types, State, Operations, Policy, Acyclicity, API,
Wrappers, Projection, Operations (NI), Composition (NI), Helpers (NI),
Soundness, RegisterDecode, SyscallArgDecode.

**Acceptance gate:** `lake build` + `test_smoke.sh` + zero sorry + no
`ServiceStatus`/`ServiceConfig`/`serviceStart`/`serviceStop` in kernel

#### Q1-F: Test Migration

**Modified files (7):** MainTraceHarness, StateBuilder, NegativeStateSuite,
OperationChainSuite, InformationFlowSuite, fixtures.

**New test scenarios (SRG-001 through SRG-010):** Register/revoke/lookup with
valid and invalid inputs, dependency cycle detection continuity.

**Acceptance gate:** `test_smoke.sh` + `test_full.sh` + zero sorry

---

### Phase Q2: Universal RHTable Migration

**Target version**: v0.19.0
**Goal**: Replace every `Std.HashMap` and `Std.HashSet` in `SystemState` with
the verified `RHTable`, establishing the builder-phase representation.

#### Q2-A: Hash Function Standardization

**Objective:** Fix a single deterministic hash function, seed, and probe
sequence for all `RHTable` instantiations in the kernel.

**Design:**
- **Hash function**: Use Lean's existing `Hashable` instances for all key types
  (already deterministic for `Nat`-wrapped types like `ObjId`, `ThreadId`, etc.)
- **Seed**: Not applicable — Robin Hood uses `(hash k).toNat % capacity` directly
- **Probe sequence**: Linear probing with Robin Hood displacement (already fixed
  in `RHTable.nextIndex`)

**Verification:**
- Prove `idealIndex` is deterministic: same key + same capacity → same index
- Prove `insertLoop`/`getLoop` sequences are deterministic given fixed capacity
- Document that `Hashable` instances for all kernel types produce identical
  hashes across Lean compilations (by construction — they delegate to `Nat` hash)

**New file:**
- `SeLe4n/Kernel/RobinHood/HashPolicy.lean` — Determinism proofs, hash policy docs

**Acceptance gate:** `lake build` + determinism proofs compile

#### Q2-B: Core State Migration

**Target maps (in order of migration):**

| # | Field | From | To | Bridge Lemmas Needed |
|---|-------|------|----|---------------------|
| 1 | `objects` | `Std.HashMap ObjId KernelObject` | `RHTable ObjId KernelObject` | get?, insert, erase, fold, contains |
| 2 | `irqHandlers` | `Std.HashMap Irq ObjId` | `RHTable Irq ObjId` | get?, insert, erase |
| 3 | `asidTable` | `Std.HashMap ASID ObjId` | `RHTable ASID ObjId` | get?, insert, erase, contains |
| 4 | `objectIndexSet` | `Std.HashSet ObjId` | Derived from `objects.contains` | membership |
| 5 | `VSpaceRoot.mappings` | `Std.HashMap VAddr (PAddr × PagePerms)` | `RHTable VAddr (PAddr × PagePerms)` | get?, insert, erase |

**Strategy per map:**
1. Change the type declaration in `State.lean` or `Structures.lean`
2. Update all call sites (primarily in operations files)
3. Verify existing theorems still hold (bridge lemmas match `Std.HashMap` API)
4. Run `test_smoke.sh` after each map migration

**objectIndexSet elimination:** Currently `objectIndexSet : Std.HashSet ObjId`
provides O(1) membership. After migration, `objects.contains k` provides the
same guarantee via `RHTable.contains` (O(1) amortized). The separate
`objectIndexSet` can be eliminated if all uses go through `objects.contains`.
The `objectIndex : List ObjId` monotonic proof anchor is retained.

**Acceptance gate:** `lake build` + `test_smoke.sh` + zero sorry

#### Q2-C: Metadata and CDT Migration

| # | Field | From | To |
|---|-------|------|----|
| 6 | `lifecycle.objectTypes` | `Std.HashMap ObjId KernelObjectType` | `RHTable ObjId KernelObjectType` |
| 7 | `lifecycle.capabilityRefs` | `Std.HashMap SlotRef CapTarget` | `RHTable SlotRef CapTarget` |
| 8 | `cdtSlotNode` | `Std.HashMap SlotRef CdtNodeId` | `RHTable SlotRef CdtNodeId` |
| 9 | `cdtNodeSlot` | `Std.HashMap CdtNodeId SlotRef` | `RHTable CdtNodeId SlotRef` |
| 10 | `cdt.childMap` | `HashMap CdtNodeId (List CdtNodeId)` | `RHTable CdtNodeId (List CdtNodeId)` |
| 11 | `cdt.parentMap` | `HashMap CdtNodeId CdtNodeId` | `RHTable CdtNodeId CdtNodeId` |

**Prerequisite:** `SlotRef` and `CdtNodeId` must have `Hashable` and `BEq`
instances. `SlotRef` is a pair `(ObjId × Slot)` — derive or define instances
compositionally.

**CDT considerations:** The `CapDerivationTree` structure uses both `childMap`
and `parentMap` for O(1) traversal. Both must migrate together to maintain
consistency. The `addEdge`/`removeAsChild`/`removeAsParent` operations update
both maps atomically.

**Acceptance gate:** `lake build` + `test_smoke.sh` + zero sorry

#### Q2-D: Service Registry Migration

| # | Field | From | To |
|---|-------|------|----|
| 12 | `serviceRegistry` | `Std.HashMap ServiceId ServiceRegistration` | `RHTable ServiceId ServiceRegistration` |
| 13 | `interfaceRegistry` | `Std.HashMap InterfaceId InterfaceSpec` | `RHTable InterfaceId InterfaceSpec` |
| 14 | `services` (legacy graph) | `Std.HashMap ServiceId ServiceGraphEntry` | `RHTable ServiceId ServiceGraphEntry` |

**Note:** Fields 12–13 are introduced in Q1. Field 14 is the retained
dependency graph (simplified in Q1-E). If Q1 and Q2 execute sequentially,
fields 12–13 can be introduced as `RHTable` from the start (no migration needed).

**Acceptance gate:** `lake build` + `test_smoke.sh` + zero sorry

#### Q2-E: Invariant Repair

After all maps are migrated, verify:
- All subsystem invariants (scheduler, capability, IPC, lifecycle, information
  flow, service) still hold with `RHTable` backing
- All frame lemmas compile
- `apiInvariantBundle_default` holds
- The `invExt` meta-invariant is maintained for every `RHTable` instance
  (add `allTablesInvExt` predicate to `SystemState`)

**New predicate:**
```lean
def SystemState.allTablesInvExt (st : SystemState) : Prop :=
  st.objects.invExt ∧ st.irqHandlers.invExt ∧ st.asidTable.invExt ∧
  st.cdtSlotNode.invExt ∧ st.cdtNodeSlot.invExt ∧
  st.cdt.childMap.invExt ∧ st.cdt.parentMap.invExt ∧
  st.lifecycle.objectTypes.invExt ∧ st.lifecycle.capabilityRefs.invExt ∧
  st.serviceRegistry.invExt ∧ st.interfaceRegistry.invExt ∧
  st.services.invExt
  -- CNode.slots.invExt handled per-object by slotsUnique
  -- VSpaceRoot.mappings.invExt handled per-object
```

**Acceptance gate:** `lake build` + `test_full.sh` + zero sorry

---

### Phase Q3: IntermediateState Formalization

**Target version**: v0.19.1
**Goal**: Define `IntermediateState` as the well-typed builder state with
explicit invariant contracts and builder operations.

#### Q3-A: IntermediateState Type

**New file:**
- `SeLe4n/Model/IntermediateState.lean`

**Design:** `IntermediateState` is a refinement of `SystemState` that bundles
the RHTable-backed state with its invariant witness:

```lean
structure IntermediateState where
  state : SystemState
  hAllTables : state.allTablesInvExt
  hPerObjectSlots : ∀ id cn, state.objects[id]? = some (.cnode cn) →
    cn.slotsUnique
  hPerObjectMappings : ∀ id vs, state.objects[id]? = some (.vspaceRoot vs) →
    vs.mappings.invExt
```

This ensures every RHTable in the system satisfies its well-formedness,
probe-chain-dominance, and no-duplicate-keys invariants at all times during
the builder phase.

#### Q3-B: Builder Operations

**New file:**
- `SeLe4n/Model/Builder.lean`

Builder operations wrap existing kernel operations with `IntermediateState`
preservation:

| Operation | Wraps | Proves |
|-----------|-------|--------|
| `Builder.createObject` | `storeObject` | `allTablesInvExt` preserved |
| `Builder.deleteObject` | object removal | `allTablesInvExt` preserved |
| `Builder.registerIrq` | IRQ handler insert | `allTablesInvExt` preserved |
| `Builder.mapPage` | VSpace page map | per-object `mappings.invExt` preserved |
| `Builder.insertCap` | CNode slot insert | per-object `slotsUnique` preserved |
| `Builder.registerService` | service registration | `allTablesInvExt` preserved |

Each builder operation returns `IntermediateState` (not `SystemState`), carrying
the invariant witness forward.

#### Q3-C: Boot Sequence

**New file:**
- `SeLe4n/Platform/Boot.lean`

The boot sequence constructs an `IntermediateState` from platform configuration:

```lean
def bootFromPlatform (config : PlatformConfig) : IntermediateState :=
  let initial := IntermediateState.empty  -- all tables empty, trivially invExt
  let withIrqs := config.irqTable.foldl (fun st (irq, handler) =>
    Builder.registerIrq st irq handler) initial
  let withObjects := config.initialObjects.foldl (fun st (id, obj) =>
    Builder.createObject st id obj) withIrqs
  -- ... additional initialization
  withObjects
```

**Proof obligation:** `IntermediateState.empty` satisfies all invariants
(trivially — all RHTables are empty, `invExt` holds for empty tables by
`RHTable.empty_invExt`).

**Acceptance gate:** `lake build` + `test_smoke.sh` + zero sorry


---

### Phase Q4: CNode Radix Tree (Verified)

**Target version**: v0.20.0
**Goal**: Implement a verified radix tree with fixed fanout and bit-sliced
traversal for CNode capability addressing. This replaces `RHTable Slot Capability`
in the frozen CNode representation.

#### Q4-A: Radix Tree Core Types

**New file:**
- `SeLe4n/Kernel/RadixTree/Core.lean`

**Type definitions:**

```lean
/-- A radix tree node with fixed 2^width fanout. -/
inductive RadixNode (α : Type) : Nat → Type where
  | leaf (slot : Fin (2^width)) (value : Option α) : RadixNode α 0
  | branch (children : Array (Option (RadixNode α (depth - 1))))
           (hSize : children.size = 2^width) : RadixNode α depth

/-- A CNode radix tree: guard + radix addressing. -/
structure CNodeTree (α : Type) where
  guardWidth  : Nat
  guardValue  : Nat
  radixWidth  : Nat
  depth       : Nat
  root        : RadixNode α depth
  hRadixFanout : ∀ node ∈ allNodes root, nodeWidth node = 2^radixWidth
```

**Design decisions:**
- **Fixed fanout**: Every internal node has exactly `2^radixWidth` children,
  matching seL4's CNode structure. No variable-width nodes.
- **Bit-sliced traversal**: Lookup extracts `radixWidth` bits at each level,
  indexing directly into the child array via `Fin (2^radixWidth)`.
- **Guard matching**: Before descending into children, verify that the guard
  bits in the key match `guardValue`. Mismatch → `none`.
- **Array-backed**: Each node's children array is `Array (Option child)`,
  providing cache-friendly sequential memory layout.

#### Q4-B: Radix Tree Operations

**Operations:**

| Operation | Signature | Complexity |
|-----------|-----------|------------|
| `RadixTree.empty` | `(guardW radixW depth : Nat) → CNodeTree α` | O(2^radixW × depth) |
| `RadixTree.lookup` | `(tree : CNodeTree α) → (key : Slot) → Option α` | O(depth) |
| `RadixTree.insert` | `(tree : CNodeTree α) → (key : Slot) → (val : α) → CNodeTree α` | O(depth) |
| `RadixTree.erase` | `(tree : CNodeTree α) → (key : Slot) → CNodeTree α` | O(depth) |
| `RadixTree.fold` | `(tree : CNodeTree α) → (init : β) → (f : β → Slot → α → β) → β` | O(n) |
| `RadixTree.toList` | `(tree : CNodeTree α) → List (Slot × α)` | O(n) |

**Bit extraction helper:**
```lean
/-- Extract `width` bits starting at bit position `offset` from a slot. -/
def extractBits (slot : Slot) (offset width : Nat) : Fin (2^width) :=
  ⟨(slot.toNat >>> offset) % (2^width), Nat.mod_lt _ (Nat.pos_of_pow2 width)⟩
```

**Lookup implementation (structural recursion on depth):**
```lean
def lookupRec (node : RadixNode α depth) (slot : Slot) (bitPos : Nat) 
    (radixW : Nat) : Option α :=
  match depth, node with
  | 0, .leaf idx val => if extractBits slot bitPos radixW = idx then val else none
  | n+1, .branch children _ =>
    let idx := extractBits slot bitPos radixW
    match children[idx.val]'(by omega) with
    | none => none
    | some child => lookupRec child slot (bitPos + radixW) radixW
```

**Acceptance gate:** `lake build` + all operations compile + zero sorry

#### Q4-C: Radix Tree Invariants

**New file:**
- `SeLe4n/Kernel/RadixTree/Invariant.lean`

**Invariant definitions:**

```lean
/-- Well-formedness: all arrays have correct size, depth is consistent. -/
def RadixTree.WF (tree : CNodeTree α) : Prop := ...

/-- No duplicate keys: each slot maps to at most one value. -/
def RadixTree.noDupKeys (tree : CNodeTree α) : Prop :=
  ∀ s v₁ v₂, tree.lookup s = some v₁ → tree.lookup s = some v₂ → v₁ = v₂

/-- Deterministic traversal: lookup is a total function. -/
def RadixTree.deterministic (tree : CNodeTree α) : Prop :=
  ∀ s, ∃! result, tree.lookup s = result
```

**Proof obligations:**
- `lookup_insert_self`: After `insert k v`, `lookup k = some v`
- `lookup_insert_ne`: Insert at `k` doesn't affect `lookup k'` when `k ≠ k'`
- `lookup_erase_self`: After `erase k`, `lookup k = none`
- `lookup_erase_ne`: Erase at `k` doesn't affect `lookup k'` when `k ≠ k'`
- `WF_preserved_insert`: Insert preserves well-formedness
- `WF_preserved_erase`: Erase preserves well-formedness
- `fold_complete`: `fold` visits every occupied slot exactly once

**Acceptance gate:** `lake build` + all proofs compile + zero sorry

#### Q4-D: Builder Equivalence Bridge

**New file:**
- `SeLe4n/Kernel/RadixTree/Bridge.lean`

**Core proof obligation:**

```lean
/-- Lookup equivalence between RHTable (builder) and RadixTree (frozen). -/
theorem radix_rhtable_equiv
    (rt : RHTable Slot Capability) (tree : CNodeTree Capability)
    (hBuild : tree = buildRadixTree rt cnodeConfig) :
    ∀ slot, rt.get? slot = tree.lookup slot := by ...
```

**Construction function:**
```lean
/-- Build a radix tree from an RHTable, preserving all entries. -/
def buildRadixTree (rt : RHTable Slot Capability) (config : CNodeConfig) :
    CNodeTree Capability :=
  rt.fold (RadixTree.empty config.guardWidth config.radixWidth config.depth)
    (fun tree slot cap => tree.insert slot cap)
```

**Additional bridge lemmas:**
- `buildRadixTree_preserves_size`: Entry count is preserved
- `buildRadixTree_preserves_membership`: `rt.contains k ↔ tree.lookup k ≠ none`
- `buildRadixTree_deterministic`: Same RHTable + same config → same tree

**Acceptance gate:** `lake build` + equivalence proof compiles + zero sorry

---

### Phase Q5: FrozenSystemState + Freeze

**Target version**: v0.21.0
**Goal**: Define the frozen execution-phase state representation with dense
arrays and `Fin`-indexed access. Implement the `freeze` function.

#### Q5-A: Dense Array Representation

**New file:**
- `SeLe4n/Model/FrozenState.lean`

**Core type:**

```lean
/-- A frozen key-value store: dense array + index map. -/
structure FrozenMap (κ : Type) (ν : Type) [BEq κ] [Hashable κ] where
  data    : Array ν
  index   : RHTable κ (Fin data.size)
  hInject : ∀ k₁ k₂ i, index.get? k₁ = some i → index.get? k₂ = some i → k₁ == k₂
  hTotal  : ∀ k i, index.get? k = some i → i.val < data.size
```

**Note on the index map:** The index map itself is an `RHTable`, which may
seem contradictory to "no hashing at runtime." The critical distinction is:
- The index map is computed **once** during `freeze` and never modified
- Runtime lookups use the pre-computed `Fin` index to access the dense array
- The hash computation happens at freeze time, not at syscall time
- For truly zero-hash runtime, the index map can be replaced with a sorted
  array + binary search, or a perfect hash function computed at freeze time

**FrozenSystemState:**

```lean
structure FrozenSystemState where
  objects         : FrozenMap ObjId KernelObject
  irqHandlers     : FrozenMap Irq ObjId
  asidTable       : FrozenMap ASID ObjId
  serviceRegistry : FrozenMap ServiceId ServiceRegistration
  interfaceRegistry : FrozenMap InterfaceId InterfaceSpec
  scheduler       : SchedulerState
  cdt             : CapDerivationTree  -- retained as-is (traversal structure)
  machine         : MachineState
  objectIndex     : List ObjId         -- monotonic proof anchor (retained)

  -- Per-object frozen structures
  -- CNode: slots as RadixTree (from Q4)
  -- VSpaceRoot: mappings as sorted array or FrozenMap
```

#### Q5-B: Freeze Function

**Implementation:**

```lean
/-- Convert a builder-phase RHTable to a frozen dense array + index. -/
def freezeMap [BEq κ] [Hashable κ] (rt : RHTable κ ν) (h : rt.invExt) :
    FrozenMap κ ν :=
  let entries := rt.toList  -- deterministic iteration (slot order)
  let data := entries.map (·.2) |>.toArray
  let index := entries.enum.foldl (fun idx (i, (k, _)) =>
    idx.insert k ⟨i, by omega⟩) (RHTable.empty 16)
  { data, index,
    hInject := by ... -- follows from noDupKeys
    hTotal := by ... }

/-- Freeze a CNode's slots into a radix tree. -/
def freezeCNode (cn : CNode) (h : cn.slotsUnique) : FrozenCNode :=
  { cn with slots := buildRadixTree cn.slots cn.config }

/-- The master freeze function. -/
def freeze (ist : IntermediateState) : FrozenSystemState :=
  { objects := freezeMap ist.state.objects ist.hAllTables.1
  , irqHandlers := freezeMap ist.state.irqHandlers ist.hAllTables.2.1
  , asidTable := freezeMap ist.state.asidTable ist.hAllTables.2.2.1
  , serviceRegistry := freezeMap ist.state.serviceRegistry ...
  , interfaceRegistry := freezeMap ist.state.interfaceRegistry ...
  , scheduler := ist.state.scheduler
  , cdt := ist.state.cdt
  , machine := ist.state.machine
  , objectIndex := ist.state.objectIndex
  }
```

#### Q5-C: Frozen Lookup Operations

```lean
/-- O(1) lookup in a frozen map (index lookup + array access). -/
def FrozenMap.get? (fm : FrozenMap κ ν) (k : κ) : Option ν :=
  match fm.index.get? k with
  | none => none
  | some idx => some fm.data[idx]

/-- O(1) membership check. -/
def FrozenMap.contains (fm : FrozenMap κ ν) (k : κ) : Bool :=
  fm.index.contains k
```

**Acceptance gate:** `lake build` + `test_smoke.sh` + zero sorry

---

### Phase Q6: Freeze Correctness Proofs

**Target version**: v0.21.1
**Goal**: Prove that the freeze function preserves all lookup semantics —
every query that succeeds in the builder state produces identical results
in the frozen state.

#### Q6-A: Core Lookup Equivalence

**New file:**
- `SeLe4n/Model/FreezeProofs.lean`

**Primary theorem:**

```lean
/-- The fundamental correctness theorem: freeze preserves all lookups. -/
theorem lookup_freeze_equiv
    (ist : IntermediateState) (k : ObjId) :
    ist.state.objects.get? k = (freeze ist).objects.get? k := by
  unfold freeze freezeMap FrozenMap.get?
  -- Key insight: toList preserves all entries (from RHTable bridge lemmas)
  -- Index construction maps each key to its position in toList
  -- Array access at that position returns the corresponding value
  ...
```

**Per-map equivalence (6 theorems):**
- `lookup_freeze_objects` — ObjId → KernelObject
- `lookup_freeze_irqHandlers` — Irq → ObjId
- `lookup_freeze_asidTable` — ASID → ObjId
- `lookup_freeze_serviceRegistry` — ServiceId → ServiceRegistration
- `lookup_freeze_interfaceRegistry` — InterfaceId → InterfaceSpec
- `lookup_freeze_cnode_slots` — Slot → Capability (RHTable → RadixTree)

#### Q6-B: CNode Radix Tree Equivalence

```lean
/-- CNode slot lookup is preserved through radix tree conversion. -/
theorem lookup_freeze_cnode
    (cn : CNode) (slot : Slot) (h : cn.slotsUnique) :
    cn.slots.get? slot = (freezeCNode cn h).slots.lookup slot := by
  -- Follows from radix_rhtable_equiv (Q4-D)
  exact radix_rhtable_equiv cn.slots (buildRadixTree cn.slots cn.config) rfl slot
```

#### Q6-C: Structural Properties

**Theorems:**
- `freeze_no_duplicates`: Frozen maps contain no duplicate keys
  (by construction from `invExt.noDupKeys`)
- `freeze_total_coverage`: Every key in builder state maps to a valid `Fin`
  (by construction from `toList` completeness)
- `freeze_deterministic`: Same `IntermediateState` → same `FrozenSystemState`
  (by determinism of `toList` order + `fold` order)
- `freeze_preserves_size`: `(freeze ist).objects.data.size = ist.state.objects.size`
- `freeze_preserves_membership`:
  `ist.state.objects.contains k ↔ (freeze ist).objects.contains k`

#### Q6-D: Cross-Subsystem Invariant Preservation

**Theorem:**
```lean
/-- All kernel invariants are preserved through freeze. -/
theorem freeze_preserves_invariants
    (ist : IntermediateState)
    (hInv : apiInvariantBundle ist.state) :
    apiInvariantBundle_frozen (freeze ist) := by
  -- Each invariant references state through lookups
  -- Lookup equivalence (Q6-A) transfers each invariant
  ...
```

This is the keystone proof: it establishes that the frozen state inherits all
safety properties from the builder state.

**Acceptance gate:** `lake build` + all proofs compile + zero sorry


---

### Phase Q7: Frozen Kernel Operations

**Target version**: v0.22.0
**Goal**: Rewrite all kernel transition functions to operate on
`FrozenSystemState`, using `Fin`-indexed array access with no runtime hashing
and no dynamic allocation.

#### Q7-A: Frozen Kernel Monad

**New file:**
- `SeLe4n/Model/FrozenKernel.lean`

```lean
/-- Kernel monad over frozen state. -/
abbrev FrozenKernel := KernelM FrozenSystemState KernelError

/-- Lift a frozen lookup into the kernel monad. -/
def FrozenKernel.lookupObject (id : ObjId) : FrozenKernel KernelObject :=
  fun st =>
    match st.objects.get? id with
    | some obj => .ok obj st
    | none => .error .objectNotFound st
```

**Design constraint:** Every frozen kernel operation must:
1. Use `FrozenMap.get?` (index lookup + array access) — never raw hash
2. Mutate via `FrozenMap.set` (array set at existing index) — never insert/erase
3. Preserve the `Fin` index mapping invariant
4. Terminate without fuel (structural recursion or `Fin` bounds)

#### Q7-B: Object Mutation in Frozen State

Objects in `FrozenSystemState` are stored in a dense `Array KernelObject`.
Mutations (e.g., updating a TCB's scheduling state during IPC) use in-place
array updates:

```lean
/-- Update an object at its frozen index. -/
def FrozenMap.set (fm : FrozenMap κ ν) (k : κ) (v : ν) :
    Option (FrozenMap κ ν) :=
  match fm.index.get? k with
  | none => none
  | some idx => some { fm with data := fm.data.set idx v }
```

**Critical guarantee:** `set` does not modify the index map. The `Fin` mapping
is immutable after freeze. This means:
- No new objects can be created (retype is a builder-phase operation)
- No objects can be destroyed (delete is a builder-phase operation)
- All runtime operations are pure state transformations on existing objects

**Object lifecycle model:**
- **Boot (builder phase):** Retype creates objects, populating the RHTable
- **Freeze:** Converts to dense array, assigns `Fin` indices
- **Runtime (frozen phase):** All operations mutate existing objects in-place
- **If dynamic creation is needed:** Return to builder phase (unfreeze → modify → refreeze)

This matches seL4's model where the capability space is configured at boot
time by the initial task, and runtime operations modify existing objects.

#### Q7-C: Per-Subsystem Frozen Operations

Each kernel subsystem gets a frozen counterpart:

| Subsystem | Builder Operation | Frozen Operation | Change |
|-----------|-------------------|------------------|--------|
| Scheduler | `schedule` | `frozenSchedule` | `objects.get?` → `FrozenMap.get?` |
| IPC | `endpointSend` | `frozenEndpointSend` | Array mutation via `FrozenMap.set` |
| Capability | `cspaceLookup` | `frozenCspaceLookup` | CNode lookup via `RadixTree.lookup` |
| VSpace | `vspaceResolve` | `frozenVspaceResolve` | Sorted array or FrozenMap lookup |
| Lifecycle | `lifecycleRetype` | N/A (builder-only) | Not available in frozen phase |
| Service | `lookupServiceByCap` | `frozenLookupServiceByCap` | `FrozenMap.get?` |

**CNode frozen lookup (radix tree):**
```lean
def frozenCspaceLookup (st : FrozenSystemState) (cptr : CPtr) (rootId : ObjId) :
    FrozenKernel Capability :=
  match st.objects.get? rootId with
  | some (.cnode cn) =>
    match cn.frozenSlots.lookup (extractSlot cptr cn) with
    | some cap => .ok cap st
    | none => .error .invalidCapability st
  | _ => .error .objectNotFound st
```

#### Q7-D: Frozen Invariant Proofs

For each frozen operation, prove:
1. **Correctness:** Same observable behavior as the builder-phase operation
2. **Index preservation:** `FrozenMap.set` does not modify the index map
3. **Bound safety:** All `Fin` accesses are within bounds (by construction)
4. **Subsystem invariant preservation:** Scheduler, IPC, capability, etc.

**Theorem pattern:**
```lean
theorem frozenEndpointSend_equiv
    (ist : IntermediateState) (tid : ThreadId) (ep : ObjId) (msg : IpcMessage)
    (hInv : apiInvariantBundle ist.state) :
    let builderResult := endpointSend ist.state tid ep msg
    let frozenResult := frozenEndpointSend (freeze ist) tid ep msg
    builderResult.map freeze = frozenResult := by ...
```

This establishes that running an operation on the builder state then freezing
is equivalent to freezing first then running the frozen operation — the
**commutativity diagram** that proves the two-phase model is semantically
transparent.

**Acceptance gate:** `lake build` + `test_full.sh` + zero sorry +
all commutativity diagrams proven

---

### Phase Q8: Rust Syscall Wrappers (WS-O Integration)

**Absorbs**: WS-O phases O1–O8
**Target version**: v0.22.0 (parallel with Q4–Q7)
**Goal**: Deliver `libsele4n`, a `no_std` Rust userspace library exposing
seLe4n's verified Lean syscall semantics as safe Rust wrappers.

**Dependency note:** Q8 depends only on Q1 (finalized syscall surface). It is
independent of Q2–Q7 (internal state architecture), since Rust wrappers operate
at the register ABI level. This enables parallel execution.

#### Q8-A: Foundation Crate — `sele4n-types` (WS-O O1)

**New directory:** `rust/sele4n-types/`

**Deliverables:**
- 14 newtype wrappers: `ObjId`, `ThreadId`, `CPtr`, `Slot`, `DomainId`,
  `Priority`, `Deadline`, `Irq`, `ServiceId`, `Badge`, `Asid`, `VAddr`,
  `PAddr`, `RegValue`
- `KernelError` enum with 1:1 variant mapping from Lean (13+ variants)
- `AccessRight` enum (5 rights) + `AccessRights` bitmask
- `SyscallId` enum with **14 variants** (updated from WS-O's 13):
  - IPC: `Send(0)`, `Receive(1)`, `Call(2)`, `Reply(3)`
  - CSpace: `CSpaceMint(4)`, `CSpaceCopy(5)`, `CSpaceMove(6)`, `CSpaceDelete(7)`
  - Lifecycle: `LifecycleRetype(8)`
  - VSpace: `VSpaceMap(9)`, `VSpaceUnmap(10)`
  - Service: `ServiceRegister(11)`, `ServiceRevoke(12)`, `ServiceQuery(13)`
- `#![no_std]`, `#![deny(unsafe_code)]`, zero external dependencies

#### Q8-B: ABI Crate — `sele4n-abi` (WS-O O2–O3)

**New directory:** `rust/sele4n-abi/`

**Deliverables:**
- `MessageInfo` bitfield: encode/decode with validated bounds (length ≤ 120,
  extra_caps ≤ 3)
- `SyscallRequest` / `SyscallResponse` register structures
- ARM64 register layout:
  ```
  x0: CPtr, x1: MessageInfo, x2-x5: msg_regs[0..3],
  x7: reply badge/status, x8: SyscallId
  ```
- `raw_syscall`: inline `svc #0` assembly (the **single** `unsafe` block)
- `invoke_syscall`: safe wrapper around `raw_syscall`
- Per-syscall argument structures: `CSpaceMintArgs`, `CSpaceCopyArgs`,
  `CSpaceMoveArgs`, `CSpaceDeleteArgs`, `LifecycleRetypeArgs`,
  `VSpaceMapArgs`, `VSpaceUnmapArgs`, `ServiceRegisterArgs`,
  `ServiceRevokeArgs`, `ServiceQueryArgs`
- `TypeTag` enum (6 variants), `PagePerms` bitmask with W^X enforcement
- Round-trip property tests for all encode/decode pairs
- Mock `svc` for host-side testing (`#[cfg(not(target_arch = "aarch64"))]`)

#### Q8-C: Syscall Crate — `sele4n-sys` (WS-O O4–O7)

**New directory:** `rust/sele4n-sys/`

**Deliverables:**
- `IpcMessage` builder: `push_reg`, `push_cap`, bounds checking (≤ 120 regs, ≤ 3 caps)
- IPC wrappers: `endpoint_send`, `endpoint_receive`, `endpoint_call`,
  `endpoint_reply`, `endpoint_reply_receive`
- Notification wrappers: `notification_signal` (badge OR accumulation),
  `notification_wait`
- CSpace wrappers: `cspace_mint` (rights subsetting), `cspace_copy`,
  `cspace_move`, `cspace_delete`
- Lifecycle wrapper: `lifecycle_retype` with `TypeTag` + convenience constructors
- VSpace wrappers: `vspace_map` (W^X pre-check), `vspace_unmap`, `PagePerms` builders
- Service wrappers: `service_register`, `service_revoke`, `service_query`
- Phantom-typed capability handles: `Cap<Obj, Rts>` with compile-time rights
  enforcement via sealed traits (`HasRead`, `HasWrite`, `HasGrant`)
- Rights downgrading: `Cap::downgrade::<NewRts>()` with `SubsetOf` verification
- `CSpaceBuilder` for initialization ergonomics
- Zero `unsafe` in this crate; `#[must_use]` on all `KernelResult` returns

#### Q8-D: Conformance Testing (WS-O O8)

**Deliverables:**
- Lean cross-validation: extend `MainTraceHarness.lean` with register encoding
  test vectors (`[RUST-XVAL-*]` format)
- `rust/tests/conformance.rs`: reads Lean trace output, verifies register-by-register
  encoding equality for all 14 syscalls
- `scripts/test_rust.sh`: Cargo build + unit tests + conformance tests
- Integration into test tier system (Tier 2 in `test_smoke.sh`)
- Compile-fail tests via `trybuild` for phantom type safety
- Property tests via `proptest` for encode/decode roundtrips

**Acceptance gate:** All 14 syscalls wrapped, `cargo build --target aarch64-unknown-none`
succeeds, conformance tests pass, exactly one `unsafe` block, zero sorry in Lean

---

### Phase Q9: Integration Testing + Documentation

**Target version**: v0.23.0
**Goal**: Comprehensive testing of the two-phase architecture, full documentation
sync across all canonical files.

#### Q9-A: Two-Phase Architecture Tests

**New test scenarios:**

| ID | Description | Phase | Expected |
|----|-------------|-------|----------|
| TPH-001 | Build IntermediateState from empty + objects | Builder | allTablesInvExt |
| TPH-002 | Freeze empty IntermediateState | Freeze | empty FrozenSystemState |
| TPH-003 | Freeze populated state, verify lookup equiv | Freeze | all lookups match |
| TPH-004 | CNode RHTable → RadixTree lookup equiv | Freeze | slot-by-slot match |
| TPH-005 | Frozen IPC send/receive | Execution | correct message transfer |
| TPH-006 | Frozen scheduler tick | Execution | correct thread selection |
| TPH-007 | Frozen CSpace lookup (radix tree) | Execution | correct capability |
| TPH-008 | Frozen VSpace resolve | Execution | correct page mapping |
| TPH-009 | Frozen service query | Execution | correct registration |
| TPH-010 | Round-trip: builder op then freeze = freeze then frozen op | Both | commutativity |
| TPH-011 | Determinism: freeze twice → identical result | Freeze | byte-equal |
| TPH-012 | Negative: frozen retype attempt → error | Execution | builderOnlyOp |

#### Q9-B: Service Interface Tests (WS-P P6 absorption)

Test scenarios SRG-001 through SRG-010 (defined in Q1-F) integrated into
the two-phase test suite.

#### Q9-C: Rust Cross-Validation Tests (WS-O O8 absorption)

RUST-XVAL test vectors for all 14 syscalls, verified register-by-register
against Lean trace output.

#### Q9-D: Documentation Sync

**Modified files (15+):**

| File | Update |
|------|--------|
| `docs/WORKSTREAM_HISTORY.md` | Add WS-Q entry (absorbs WS-P, WS-O) |
| `docs/spec/SELE4N_SPEC.md` | Two-phase architecture, service interface, Rust wrappers |
| `docs/DEVELOPMENT.md` | Builder/freeze workflow, Rust build instructions |
| `docs/CLAIM_EVIDENCE_INDEX.md` | WS-Q claims (freeze equivalence, radix tree correctness) |
| `README.md` | Metrics sync (line counts, theorem counts, Rust crate stats) |
| `CLAUDE.md` | Source layout (new files), active workstream update |
| `docs/gitbook/03-architecture-and-module-map.md` | Two-phase architecture diagram |
| `docs/gitbook/04-project-design-deep-dive.md` | Builder/freeze design rationale |
| `docs/gitbook/05-specification-and-roadmap.md` | Updated milestone table |
| `docs/gitbook/12-proof-and-invariant-map.md` | Freeze proofs, radix tree invariants |
| `docs/gitbook/15-rust-syscall-wrappers.md` | New chapter: Rust library docs |
| `docs/codebase_map.json` | Regenerate with new modules |
| `scripts/website_link_manifest.txt` | Verify/update protected paths |
| `scripts/test_smoke.sh` | Integrate Rust tests (Tier 2) |
| `scripts/test_full.sh` | Integrate two-phase tests (Tier 3) |

**Acceptance gate:** `test_full.sh` + `generate_codebase_map.py --pretty --check` +
all documentation reviewed


---

## 5. Estimated Scope

| Phase | New Lines | Removed Lines | Modified Files | New Files | New Dirs |
|-------|-----------|---------------|----------------|-----------|----------|
| Q1 | ~1,150 | ~800 | ~22 | 3 | 1 |
| Q2 | ~600 | ~200 | ~30 | 1 | 0 |
| Q3 | ~400 | 0 | 2 | 3 | 0 |
| Q4 | ~1,200 | 0 | 2 | 3 | 1 |
| Q5 | ~500 | 0 | 3 | 2 | 0 |
| Q6 | ~800 | 0 | 2 | 1 | 0 |
| Q7 | ~1,500 | ~300 | ~20 | 2 | 0 |
| Q8 | ~3,000 | 0 | 3 | ~20 | 4 |
| Q9 | ~500 | ~200 | ~18 | 2 | 0 |
| **Total** | **~9,650** | **~1,500** | **~50 unique** | **~37** | **6** |

**Net effect**: ~8,150 new lines across Lean and Rust, with a substantially
simpler and more principled kernel state architecture.

**Lean proof surface expansion**: ~3,500 lines of new invariant and equivalence
proofs (Q3, Q4-C, Q6, Q7-D).

**Rust library**: ~3,000 lines across 3 crates (types, ABI, syscall wrappers).

---

## 6. Dependency Graph (Detailed)

```
                    Q1 (Service Interface)
                    │
          ┌─────────┼──────────┐
          │         │          │
          ▼         │          ▼
    Q2 (RHTable     │    Q8 (Rust Wrappers)
     Migration)     │     ║  O1→O2→O3
          │         │     ║  O4 ∥ O5 ∥ O6
          ▼         │     ║  O7→O8
    Q3 (Intermediate│     ║
     State)         │     ║
          │         │     ║
     ┌────┴────┐    │     ║
     │         │    │     ║
     ▼         ▼    │     ║
   Q4 (Radix  Q5*   │     ║
    Tree)     waits  │     ║
     │    for Q4     │     ║
     │    ┌────┘     │     ║
     ▼    ▼          │     ║
    Q5 (Frozen       │     ║
     State)          │     ║
          │          │     ║
          ▼          │     ║
    Q6 (Freeze       │     ║
     Proofs)         │     ║
          │          │     ║
          ▼          │     ║
    Q7 (Frozen       │     ║
     Operations)     │     ║
          │          │     ║
          └──────────┴─────╝
                     │
                     ▼
               Q9 (Testing +
                Documentation)
```

**Critical path**: Q1 → Q2 → Q3 → Q4 → Q5 → Q6 → Q7 → Q9
**Parallel path**: Q1 → Q8 → Q9 (joins at Q9)

**Phase Q4 and Q3 parallelism**: Q4 (radix tree) depends on Q2 (RHTable
migration) for the builder-phase CNode representation, but its core type
definitions and proofs can begin in parallel with Q3 (IntermediateState
formalization). Q5 must wait for both Q3 and Q4.

---

## 7. Risk Analysis

### Risk 1: Universal RHTable Migration Breadth (HIGH)

**Description**: Q2 touches 30+ files across every subsystem, replacing
`Std.HashMap` with `RHTable` at every occurrence. Any missed call site or
API mismatch produces compile errors across the entire proof surface.

**Likelihood**: MEDIUM | **Impact**: HIGH

**Mitigation**:
- Migrate one map at a time, running `lake build` after each
- The existing bridge lemmas (10 in Bridge.lean) match `Std.HashMap` API patterns
- Use `Grep` for `Std.HashMap` to find all remaining occurrences
- `test_smoke.sh` at each intermediate commit
- The WS-N4 CNode migration (20+ files, ~25 theorems) provides a proven template

### Risk 2: Freeze Function Complexity (HIGH)

**Description**: The `freeze` function must produce a well-formed
`FrozenSystemState` where every `Fin` index is valid and every lookup is
equivalent. The proof of `lookup_freeze_equiv` is non-trivial — it requires
reasoning about `toList` ordering, `enum` indexing, and `foldl` accumulation.

**Likelihood**: MEDIUM | **Impact**: HIGH

**Mitigation**:
- Build `freezeMap` as a standalone, generic function with its own proof module
- Prove `toList`/`fold` completeness lemmas in `RHTable.Bridge` first
- Use `decide` or `native_decide` for finite-domain equivalence checks in tests
- The `invExt.noDupKeys` invariant simplifies many proof steps

### Risk 3: Radix Tree Verification Effort (MEDIUM)

**Description**: The CNode radix tree is a new verified data structure requiring
~1,200 lines of proofs. Structural recursion on depth is clean but array bounds
reasoning can be tedious in Lean 4.

**Likelihood**: MEDIUM | **Impact**: MEDIUM

**Mitigation**:
- The radix tree is structurally simpler than Robin Hood (no displacement, no
  backshift, no load factor) — proofs should be more straightforward
- Fixed fanout (2^radixWidth) simplifies bounds reasoning
- The `extractBits` + `Fin` pattern provides type-level bounds automatically
- Incremental delivery: core types (Q4-A) → operations (Q4-B) → proofs (Q4-C)
  → bridge (Q4-D), each independently compilable

### Risk 4: Frozen Operation Commutativity (MEDIUM)

**Description**: Q7-D requires proving that `f(freeze(s)) = freeze(f(s))` for
every kernel operation `f`. This commutativity diagram is the formal guarantee
that the two-phase model is semantically transparent, but proving it for ~20
operations is substantial.

**Likelihood**: MEDIUM | **Impact**: MEDIUM

**Mitigation**:
- Most operations only modify one or two objects — the commutativity proof
  reduces to showing that `FrozenMap.set` at a valid index commutes with
  `freeze` applied to an `RHTable.insert` at the same key
- Prove a generic `set_freeze_commute` lemma once, instantiate per-operation
- Operations that don't modify state (lookups) commute trivially

### Risk 5: WS-O ABI Drift (LOW)

**Description**: Q1 changes the syscall ID enumeration. If Q8 begins before
Q1 is finalized, the Rust encoding may not match.

**Likelihood**: LOW | **Impact**: LOW

**Mitigation**:
- Q8 depends on Q1 — Rust work begins only after syscall surface is stable
- Conformance tests (Q8-D) catch any encoding drift automatically
- Version pinning: `sele4n-abi` version tracks the Lean model version

### Risk 6: Builder-Only Operations at Runtime (LOW)

**Description**: The frozen phase deliberately excludes `lifecycleRetype` and
`objectCreate`. If user space needs to create objects at runtime, the kernel
must support an unfreeze → modify → refreeze cycle, which adds complexity.

**Likelihood**: LOW (seL4 model: all objects created at boot by initial task)

**Mitigation**:
- seL4's actual model: all untyped memory is partitioned at boot time; retype
  is invoked by the root task during initialization, not during steady-state
  operation. The frozen phase matches this model.
- If dynamic retype is needed (future requirement), it can be modeled as a
  special transition that extends the dense array (append + index update) rather
  than a full unfreeze/refreeze cycle.

### Risk 7: `objectIndex` Monotonicity in Frozen State (LOW)

**Description**: The `objectIndex : List ObjId` monotonic proof anchor is
retained in `FrozenSystemState`. Since the frozen phase doesn't create new
objects, monotonicity is trivially preserved (the list never changes). But
the list is still carried as proof infrastructure.

**Likelihood**: LOW | **Impact**: LOW

**Mitigation**: No action needed — monotonicity is a "for free" property in
the frozen phase. The list is retained for cross-phase proof continuity.

---

## 8. Success Criteria

### 8.1 Architectural

- [ ] No `Std.HashMap` or `Std.HashSet` in any kernel state type
- [ ] `IntermediateState` uses `RHTable` exclusively for all maps
- [ ] `FrozenSystemState` uses dense arrays + `Fin` indexing for all maps
- [ ] CNode slots use verified radix tree in frozen state
- [ ] All RHTable instances satisfy `invExt` (WF + PCD + noDupKeys)
- [ ] Fixed hash function, fixed seed, fixed probe sequence — no nondeterminism
- [ ] No pointer-heavy structures in frozen execution path
- [ ] Service lifecycle (start/stop/restart) removed from kernel
- [ ] Service registration is capability-mediated
- [ ] Rust syscall library compiles for `aarch64-unknown-none`

### 8.2 Formal

- [ ] `lookup_freeze_equiv` proven for all 6+ map types
- [ ] `lookup_freeze_cnode` proven (RHTable → RadixTree equivalence)
- [ ] `freeze_deterministic` — same builder state → same frozen state
- [ ] `freeze_preserves_invariants` — all `apiInvariantBundle` properties transfer
- [ ] Commutativity: `f(freeze(s)) = freeze(f(s))` for all frozen operations
- [ ] RadixTree lookup/insert/erase correctness proven
- [ ] Registry invariants (`registryEndpointValid`, `registryInterfaceValid`) proven
- [ ] Zero `sorry`/`axiom` in production proof surface
- [ ] All `invExt` preservation proofs for new RHTable instances

### 8.3 Runtime

- [ ] O(1) object lookup in frozen state (array indexing via `Fin`)
- [ ] O(depth) CNode capability lookup (radix tree traversal)
- [ ] No runtime hash computation in frozen kernel operations
- [ ] No dynamic memory allocation in frozen kernel operations
- [ ] Cache-friendly memory layout (dense arrays, radix tree nodes)
- [ ] Deterministic memory image (identical boot → identical frozen state)

### 8.4 Rust Library

- [ ] All 14 syscalls have safe Rust wrappers
- [ ] `cargo build --target aarch64-unknown-none` compiles all three crates
- [ ] Exactly one `unsafe` block (inline `svc #0` in `sele4n-abi`)
- [ ] Cross-validation confirms register-by-register ABI match with Lean
- [ ] Phantom-typed capability handles prevent wrong-rights usage at compile time
- [ ] `#[must_use]` on all `KernelResult` returns
- [ ] Zero external dependencies in `sele4n-types`

### 8.5 Documentation

- [ ] `WORKSTREAM_HISTORY.md` updated with WS-Q entry
- [ ] `SELE4N_SPEC.md` reflects two-phase architecture
- [ ] `DEVELOPMENT.md` updated with builder/freeze workflow
- [ ] `CLAIM_EVIDENCE_INDEX.md` updated with freeze-equivalence claims
- [ ] GitBook chapters updated (architecture, design, roadmap, proof map)
- [ ] New GitBook chapter for Rust syscall wrappers
- [ ] `codebase_map.json` regenerated
- [ ] Website link manifest verified

---

## 9. Verification Commands

**After each phase:**
```bash
source ~/.elan/env && lake build          # Must succeed
./scripts/test_fast.sh                     # Tier 0+1
./scripts/test_smoke.sh                    # Tier 0-2 (minimum before PR)
```

**After Q7 (frozen operations complete):**
```bash
./scripts/test_full.sh                     # Tier 0-3
```

**After Q8 (Rust wrappers):**
```bash
cd rust && cargo build --target aarch64-unknown-none  # Cross-compile
cd rust && cargo test --features std                   # Host tests
./scripts/test_rust.sh                                 # Conformance
```

**After Q9 (documentation):**
```bash
./scripts/generate_codebase_map.py --pretty --check   # Metrics sync
./scripts/test_full.sh                                 # Full validation
```

**Module-level verification (mandatory for all `.lean` changes):**
```bash
source ~/.elan/env && lake build <Module.Path>
```

---

## 10. New Source Layout (Post WS-Q)

```
SeLe4n/
├── Prelude.lean                          Extended: InterfaceId
├── Machine.lean                          Unchanged
├── Model/
│   ├── Object/
│   │   ├── Types.lean                    Updated: ServiceRegistration, no ServiceStatus
│   │   └── Structures.lean              Updated: CNode with RadixTree option
│   ├── State.lean                        Updated: all RHTable, no Std.HashMap
│   ├── IntermediateState.lean            NEW: builder state with invariant witness
│   ├── FrozenState.lean                  NEW: FrozenMap, FrozenSystemState
│   ├── FreezeProofs.lean                 NEW: lookup equivalence proofs
│   ├── FrozenKernel.lean                 NEW: frozen kernel monad
│   └── Builder.lean                      NEW: builder operations
├── Kernel/
│   ├── RobinHood/                        Existing (WS-N)
│   │   ├── Core.lean                     Unchanged
│   │   ├── Bridge.lean                   Extended: toList completeness
│   │   ├── HashPolicy.lean               NEW: determinism proofs
│   │   └── Invariant/                    Unchanged
│   ├── RadixTree/                        NEW (Q4)
│   │   ├── Core.lean                     Types + operations
│   │   ├── Invariant.lean                Correctness proofs
│   │   └── Bridge.lean                   RHTable ↔ RadixTree equivalence
│   ├── Service/
│   │   ├── Interface.lean                NEW (Q1): InterfaceSpec, ServiceRegistration
│   │   ├── Registry.lean                 NEW (Q1): 4 registry operations
│   │   ├── Registry/Invariant.lean       NEW (Q1): registry invariants
│   │   ├── Operations.lean               Updated: lifecycle ops removed
│   │   └── Invariant/                    Updated: simplified
│   ├── Scheduler/                        Updated: frozen operations (Q7)
│   ├── IPC/                              Updated: frozen operations (Q7)
│   ├── Capability/                       Updated: radix tree CNode lookup (Q7)
│   ├── Lifecycle/                        Updated: builder-only annotation (Q7)
│   ├── Architecture/                     Updated: new SyscallIds (Q1)
│   ├── InformationFlow/                  Updated: service NI proofs (Q1)
│   └── API.lean                          Updated: new service API (Q1)
├── Platform/
│   ├── Boot.lean                         NEW (Q3): boot → IntermediateState
│   └── ...                               Existing
└── Testing/                              Updated: two-phase + service tests

rust/                                      NEW (Q8)
├── Cargo.toml                            Workspace root
├── sele4n-types/                         Core types crate
├── sele4n-abi/                           Register ABI crate
├── sele4n-sys/                           Syscall wrappers crate
└── tests/conformance.rs                  Cross-validation
```

---

## 11. Relationship to Hardware Binding (H3)

The two-phase architecture directly supports the Raspberry Pi 5 hardware target:

- **Builder phase**: Runs during boot on the BCM2712 SoC. Platform configuration
  (GIC-400 IRQ table, MMIO regions, initial memory layout) populates the
  `IntermediateState`.
- **Freeze**: Executed once, producing a `FrozenSystemState` with deterministic
  memory layout. On ARM64, this maps naturally to a contiguous memory region
  that can be identity-mapped during early boot.
- **Execution phase**: All kernel operations use cache-friendly array access,
  critical for the Cortex-A76 cores' L1/L2 cache hierarchy. No hash table
  probing or pointer chasing during syscall handling.
- **Rust wrappers**: `sele4n-abi` encodes the ARM64 `svc #0` trap interface.
  The `raw_syscall` function is the exact userspace entry point for RPi5
  applications. H3 builds the kernel-side trap handler that decodes these
  registers using the same ABI.

---

## 12. Design Principles

> **P1. The kernel enforces constraints — it does not decide behavior.**
> Service lifecycle, dependency ordering, naming, and discovery are policy
> decisions that belong in user space.

> **P2. Every data structure in the kernel execution path must be verified.**
> No `Std.HashMap`, no `partial`, no `get!`/`set!`, no axioms. Every lookup,
> insertion, and deletion has a machine-checked correctness proof.

> **P3. The two-phase model separates flexibility from performance.**
> The builder phase prioritizes expressiveness (RHTable with dynamic resizing).
> The frozen phase prioritizes performance (dense arrays with Fin indexing).
> The freeze function is the formally verified bridge between them.

> **P4. Determinism is non-negotiable.**
> Fixed hash function, fixed seed, fixed probe sequence, deterministic
> iteration order, deterministic freeze. Identical boot configuration produces
> an identical byte-level memory image. This is essential for formal reasoning
> and for reproducible hardware deployment.

> **P5. The Rust ABI is a contract, not an implementation detail.**
> Register layout, syscall IDs, error codes, and message encoding are formally
> specified in Lean and mechanically cross-validated against Rust. ABI drift
> is caught by conformance tests, not by debugging deployed hardware.

---

**END OF MASTER PLAN**

