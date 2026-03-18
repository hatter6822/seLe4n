# WS-O Workstream Plan — Verified Service Interface Layer (v0.18.0)

**Created**: 2026-03-18
**Baseline version**: 0.17.1
**Prior portfolios**: WS-N (v0.17.0, active — N1 complete), WS-M (v0.17.0, complete)
**Constraint**: Zero `sorry`/`axiom` in production proof surface
**Scope**: Capability-indexed service interface layer with formal verification
**Skeleton source**: `docs/audits/SERVICE_PLAN_SKELETON.md` (superseded by this document)

---

## 1. Motivation & Background

### 1.1 Problem Statement

The current Service subsystem (4 files, ~1,949 lines) models in-kernel service
orchestration as a first-class kernel abstraction. While this enables
machine-checked reasoning about service properties, the design conflates
**mechanism** (capability enforcement, interface typing) with **policy**
(naming, discovery, dependency orchestration, lifecycle management).

This violates two core microkernel principles:
1. **Mechanism ≠ Policy**: The kernel should enforce safety constraints, not
   decide behavior. Service lifecycle management (start/stop/restart) is policy
   that belongs in user space.
2. **Minimal TCB**: The kernel's trusted computing base should be as small as
   possible. The current ~1,950 lines of service code (including ~1,110 lines
   of acyclicity proofs for an in-kernel dependency graph) expand the TCB
   beyond what is necessary for safety enforcement.

Real seL4 provides **no** kernel-level service management — service lifecycle,
dependency graphs, and orchestration are delegated entirely to user-level
system components (e.g., CAmkES). seLe4n should model the kernel's role as
an enforcement layer, not an orchestration engine.

### 1.2 Current Architecture (What Exists)

| Component | File | Lines | Purpose |
|-----------|------|-------|---------|
| Operations | `Service/Operations.lean` | 442 | `serviceStart`, `serviceStop`, `serviceRestart`, `serviceRegisterDependency`, `serviceHasPathTo` |
| Policy invariants | `Service/Invariant/Policy.lean` | 377 | Policy predicates, cross-subsystem bundle, preservation theorems |
| Acyclicity proofs | `Service/Invariant/Acyclicity.lean` | 1,110 | 4-layer proof infrastructure for dependency graph acyclicity |
| Re-export hub | `Service/Invariant.lean` | 22 | Import barrel |

**Current types** (in `Model/Object/Types.lean`):
- `ServiceStatus` — `stopped | running` (lifecycle state)
- `ServiceIdentity` — `sid`, `backingObject`, `owner`
- `ServiceGraphEntry` — identity, status, dependencies, isolatedFrom

**Current state** (in `Model/State.lean`):
- `services : Std.HashMap ServiceId ServiceGraphEntry`
- `serviceConfig : ServiceConfig` (allowStart/allowStop policy gates)

**Cross-cutting references**: 23 files across the codebase reference Service
types, including information flow (6 files), API (1 file), testing (5 files),
and model (3 files).

### 1.3 Solution: Verified Service Interface Layer

Replace the orchestration-focused service subsystem with a **capability-indexed,
formally verified interface enforcement layer** that:

1. **Registers services** with concrete interface specifications (method count,
   message bounds, required rights) — enforcing that each service has a valid
   endpoint capability
2. **Looks up services** by capability — enabling capability-mediated discovery
   without a global registry
3. **Revokes services** — removing registrations when capabilities are revoked
4. **Retains dependency cycle detection** — keeping the proven acyclicity
   infrastructure for kernel-level safety checks (hybrid approach)
5. **Delegates lifecycle to user space** — removing `serviceStart`/`serviceStop`/
   `serviceRestart` from the kernel

### 1.4 Design Decisions

**DD-1: Concrete types (no universe polymorphism)**

The skeleton proposed `InterfaceSpec` with `Req : Type` and `Resp : Type` fields.
This creates `InterfaceSpec : Type 1`, which would propagate universe constraints
through all kernel state structures. Instead, we use concrete representations:

```lean
structure InterfaceSpec where
  ifaceId         : InterfaceId
  methodCount     : Nat
  maxMessageSize  : Nat
  maxResponseSize : Nat
  requiresGrant   : Bool
```

This stays in `Type 0`, avoids universe issues, and aligns with the microkernel
principle that the kernel does not interpret message contents.

**DD-2: Hybrid dependency approach**

Keep minimal dependency checking (cycle detection via `serviceRegisterDependency`
and `serviceHasPathTo`) in the kernel for safety. Move lifecycle management
(start/stop/restart), naming, discovery, and orchestration to user space.
The ~1,110 lines of acyclicity proofs are retained but status-related frame
lemmas are removed.

**DD-3: Additive-first migration**

Phases O1-O4 are purely additive — new types and operations coexist alongside
legacy infrastructure. Phase O5 performs the legacy removal. This ensures
compilation at every intermediate step.

---

## 2. Architecture

### 2.1 New Type Hierarchy

```
InterfaceId (Prelude.lean)
  └── InterfaceSpec (Service/Interface.lean)
        └── ServiceRegistration (Service/Interface.lean)
              └── serviceRegistry : HashMap ServiceId ServiceRegistration (State.lean)

InterfaceSpec (Service/Interface.lean)
  └── interfaceRegistry : HashMap InterfaceId InterfaceSpec (State.lean)
```

### 2.2 New Operations

| Operation | Purpose | Error Conditions |
|-----------|---------|------------------|
| `registerInterface` | Register a concrete interface spec | `illegalState` (duplicate) |
| `registerService` | Capability-mediated service registration | `illegalState` (duplicate), `objectNotFound` (unknown interface), `invalidCapability` (bad endpoint) |
| `lookupServiceByCap` | Capability-indexed lookup (read-only) | `objectNotFound` |
| `revokeService` | Remove registration by ServiceId | `objectNotFound` |

### 2.3 Retained Operations (Hybrid)

| Operation | Purpose | Status |
|-----------|---------|--------|
| `serviceRegisterDependency` | Dependency edge registration with cycle check | Retained |
| `serviceHasPathTo` | DFS cycle detection with HashSet visited | Retained |
| `serviceBfsFuel` | Fuel bound for graph traversal | Retained |

### 2.4 Removed Operations (→ User Space)

| Operation | Reason for Removal |
|-----------|--------------------|
| `serviceStart` | Lifecycle management is policy, not mechanism |
| `serviceStop` | Lifecycle management is policy, not mechanism |
| `serviceRestart` | Lifecycle management is policy, not mechanism |
| `ServiceConfig` | Policy gates belong in user space |
| `ServiceStatus` | Runtime status tracking belongs in user space |

---

## 3. Invariant Definitions

### 3.1 Registry Invariants (New)

```lean
/-- All registered services reference valid endpoint objects. -/
def registryEndpointValid (st : SystemState) : Prop :=
  ∀ sid reg, st.serviceRegistry[sid]? = some reg →
    match reg.endpointCap.target with
    | .object epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
    | _ => False

/-- All registered services reference registered interfaces. -/
def registryInterfaceValid (st : SystemState) : Prop :=
  ∀ sid reg, st.serviceRegistry[sid]? = some reg →
    st.interfaceRegistry.contains reg.iface.ifaceId

/-- Combined registry invariant. -/
def registryInvariant (st : SystemState) : Prop :=
  registryEndpointValid st ∧ registryInterfaceValid st
```

### 3.2 Retained Invariants

- `serviceDependencyAcyclic` — no service has dependency chain back to itself
- `serviceCountBounded` — reachable nodes fit within fuel budget
- `serviceGraphInvariant` — combines acyclicity + count bound

### 3.3 Removed Invariants

- `servicePolicySurfaceInvariant` — backing object typing (replaced by registry)
- `serviceLifecycleCapabilityInvariantBundle` — lifecycle + capability bundle
- Status-related frame lemmas in Acyclicity.lean

---

## 4. Phase Plan

### Phase O1: Foundation Types (v0.18.0)

**Goal:** Introduce `InterfaceId`, `InterfaceSpec` (concrete), and `ServiceRegistration` types.

**New files:**
- `SeLe4n/Kernel/Service/Interface.lean` — InterfaceSpec, ServiceRegistration

**Modified files:**
- `SeLe4n/Prelude.lean` — Add `InterfaceId` typed wrapper (following `ServiceId` pattern)
- `SeLe4n/Model/Object/Types.lean` — Add `ServiceRegistration` structure

**Tasks:**
1. Define `InterfaceId` in Prelude.lean with `Hashable`, `BEq`, `ofNat`/`toNat`/`sentinel`
2. Define `InterfaceSpec` with concrete fields (no universe polymorphism)
3. Define `ServiceRegistration` with `sid`, `iface`, `endpointCap`
4. Prove `InterfaceId` roundtrip theorems matching `ServiceId` pattern
5. Verify `lake build` succeeds (purely additive, zero sorry)

**Acceptance gate:** `lake build` + `test_fast.sh`

---

### Phase O2: Registry State and Core Operations (v0.18.1)

**Goal:** Add registry fields to `SystemState`; implement 4 registry operations.

**New file:**
- `SeLe4n/Kernel/Service/Registry.lean` — 4 operations + 8 theorems

**Modified files:**
- `SeLe4n/Model/State.lean` — Add `serviceRegistry`, `interfaceRegistry` to SystemState

**Operations:**
- `registerInterface` — register concrete interface spec
- `registerService` — capability-mediated registration with 3-check ordering
- `lookupServiceByCap` — capability-indexed lookup (read-only)
- `revokeService` — remove registration by ServiceId

**Theorems (minimum 8):**
- Error-condition theorems for each operation
- `registerService_ok_implies_registered` — success post-condition
- `revokeService_removes_registration` — revocation correctness
- `lookupServiceByCap_state_unchanged` — read-only guarantee
- Frame lemmas: `registerService_preserves_objects`, `_preserves_scheduler`

**Acceptance gate:** `lake build` + `test_smoke.sh`

---

### Phase O3: Registry Invariants and Preservation Proofs (v0.18.2)

**Goal:** Define registry invariants; prove preservation for all operations.

**New file:**
- `SeLe4n/Kernel/Service/Registry/Invariant.lean`

**Modified files:**
- `SeLe4n/Kernel/Service/Invariant/Policy.lean` — Add registry invariant to bundle
- `SeLe4n/Kernel/Service/Invariant.lean` — Import new Registry/Invariant

**Proof obligations:**
- `registerService_preserves_registryInvariant`
- `revokeService_preserves_registryInvariant`
- `registerInterface_preserves_registryInvariant`
- Cross-subsystem: registry ops preserve lifecycle, capability, scheduler, IPC invariants
- Default state: `default_registryInvariant`
- Integration: `apiInvariantBundle` extended with `registryInvariant`

**Acceptance gate:** `lake build` + `test_smoke.sh` + zero sorry

---

### Phase O4: API Integration and Syscall Dispatch (v0.18.3)

**Goal:** Wire registry operations into kernel API, syscall dispatch, and information flow.

**Modified files (6):**
- `SeLe4n/Kernel/API.lean` — Add `apiServiceRegister`, `apiServiceRevoke`, `apiServiceQuery`
- `SeLe4n/Model/Object/Types.lean` — Add `SyscallId` variants: `.serviceRegister`, `.serviceRevoke`, `.serviceQuery`
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — Extend `SyscallId.toNat`/`ofNat?`
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` — Add decode functions
- `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` — Add `registerServiceChecked`
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` — Update operation catalog

**Acceptance gate:** `lake build` + `test_smoke.sh` + zero sorry

---

### Phase O5: Legacy Deprecation and Migration (v0.18.4)

**Goal:** Remove old lifecycle-based service operations; keep dependency cycle detection.

**Strategy (hybrid approach):**
1. **Keep:** `serviceRegisterDependency`, `serviceHasPathTo`, `serviceBfsFuel`, acyclicity proofs
2. **Remove:** `serviceStart`, `serviceStop`, `serviceRestart`, `ServiceStatus`, `ServiceConfig`
3. **Simplify:** `ServiceGraphEntry` loses `status` field; retains `identity`, `dependencies`, `isolatedFrom`
4. **Migration technique:** Rename `services` → `servicesLegacy` first to find all callsites

**Modified files (~15):**
- `SeLe4n/Model/Object/Types.lean` — Remove `ServiceStatus`, simplify `ServiceGraphEntry`
- `SeLe4n/Model/State.lean` — Remove `serviceConfig`, `setServiceStatusState`, `dependenciesSatisfied`
- `SeLe4n/Kernel/Service/Operations.lean` — Remove lifecycle ops + 11 theorems; keep cycle detection
- `SeLe4n/Kernel/Service/Invariant/Policy.lean` — Remove lifecycle bundle; add registry-policy bridge
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` — Remove status-related frame lemmas
- `SeLe4n/Kernel/API.lean` — Remove `apiServiceStart`/`apiServiceStop`, old dispatch arms
- `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` — Remove `serviceRestartChecked`
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — Replace `projectServiceStatus`
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` — Replace legacy NI proofs
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` — Replace NI step constructors
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` — Update frame lemmas
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` — Update catalog
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — Remove old SyscallId variants
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` — Remove old decode functions

**Acceptance gate:** `lake build` + `test_smoke.sh` + zero sorry + no `ServiceStatus`/`ServiceConfig`/`serviceStart`/`serviceStop`/`serviceRestart` in kernel

---

### Phase O6: Test Migration (v0.18.5)

**Goal:** Update all test infrastructure for the new service model.

**Modified files (7):**
- `SeLe4n/Testing/MainTraceHarness.lean` — Replace SST-series with SRG-series
- `SeLe4n/Testing/StateBuilder.lean` — Add `withServiceRegistration`, `withInterfaceSpec`
- `tests/NegativeStateSuite.lean` — Update service error path tests
- `tests/OperationChainSuite.lean` — Update multi-op service sequences
- `tests/InformationFlowSuite.lean` — Update service NI runtime checks
- `tests/fixtures/main_trace_smoke.expected` — Update fixture
- `tests/fixtures/scenario_registry.yaml` — Update scenario mappings

**New test scenarios:**

| ID | Description | Expected |
|----|-------------|----------|
| SRG-001 | Register service with valid endpoint + interface | success |
| SRG-002 | Register service — duplicate rejection | illegalState |
| SRG-003 | Register service — unknown interface | objectNotFound |
| SRG-004 | Register service — invalid endpoint | invalidCapability |
| SRG-005 | Revoke registered service | success |
| SRG-006 | Revoke non-existent service | objectNotFound |
| SRG-007 | Lookup by matching capability | success + correct reg |
| SRG-008 | Lookup by non-matching capability | objectNotFound |
| SRG-009 | Register interface + service chain | success |
| SRG-010 | Dependency cycle detection still works | cyclicDependency |

**Acceptance gate:** `test_smoke.sh` + `test_full.sh` + zero sorry

---

### Phase O7: Documentation and Cleanup (v0.18.6)

**Goal:** Synchronize all documentation with the new service model.

**Modified files (12+):**
- `docs/WORKSTREAM_HISTORY.md` — Add WS-O entry
- `docs/spec/SELE4N_SPEC.md` — Update service subsystem section
- `docs/DEVELOPMENT.md` — Update service development guidance
- `docs/CLAIM_EVIDENCE_INDEX.md` — Update/add WS-O claims
- `docs/gitbook/03-architecture-and-module-map.md` — Update service architecture
- `docs/gitbook/04-project-design-deep-dive.md` — Update service design rationale
- `docs/gitbook/05-specification-and-roadmap.md` — Update milestone table
- `docs/gitbook/12-proof-and-invariant-map.md` — Update service invariants
- `README.md` — Sync metrics
- `CLAUDE.md` — Update source layout, active workstream context
- `docs/audits/SERVICE_PLAN_SKELETON.md` — Mark as superseded
- `scripts/website_link_manifest.txt` — Verify/update paths

**Regeneration:** `./scripts/generate_codebase_map.py --pretty`

**Acceptance gate:** `test_full.sh` + `generate_codebase_map.py --pretty --check`

---

### Phase O8: Finalize Workstream Plan Document (v0.18.7)

**Goal:** Update this document with implementation details, lessons learned, and final metrics.

**Acceptance gate:** Cross-referenced with WORKSTREAM_HISTORY.md entry

---

## 5. Dependency Order

```
O1 (types) → O2 (operations) → O3 (invariants) → O4 (API) → O5 (migration) → O6 (tests) → O7 (docs) → O8 (finalize)
```

Phases O1-O4: purely additive (no breakage).
Phase O5: destructive migration (highest risk).
Phases O6-O8: cleanup and documentation.
Each phase boundary: `test_smoke.sh` must pass.

---

## 6. Estimated Scope

| Phase | New Lines | Removed Lines | Modified Files | New Files |
|-------|-----------|---------------|----------------|-----------|
| O1 | ~100 | 0 | 2 | 1 |
| O2 | ~250 | 0 | 1 | 1 |
| O3 | ~350 | 0 | 3 | 1 |
| O4 | ~300 | 0 | 6 | 0 |
| O5 | ~150 | ~800 | 15 | 0 |
| O6 | ~300 | ~200 | 7 | 0 |
| O7 | ~150 | ~50 | 12 | 0 |
| O8 | ~50 | 0 | 1 | 0 |
| **Total** | **~1,650** | **~1,050** | **~25 unique** | **3** |

Net effect: ~600 line reduction with substantially simpler invariants.

---

## 7. Risk Analysis

### Risk 1: Phase O5 Breadth (HIGH → mitigated)
The legacy removal touches ~15 files simultaneously.
**Mitigation:** Rename `services` → `servicesLegacy` first to produce compile errors
at every callsite. Fix each callsite individually. Run `test_smoke.sh` at each
intermediate commit.

### Risk 2: NI Proof Migration (MEDIUM → mitigated)
The information-flow subsystem references services in 6 files (~200 lines).
**Mitigation:** The NI proof pattern is well-established (service ops only modify
service state, not objects/scheduler). New registry ops follow the same pattern.
Add new NI proofs in O4 before removing old ones in O5.

### Risk 3: SyscallId Renumbering (MEDIUM → mitigated)
Removing `.serviceStart`/`.serviceStop` and adding `.serviceRegister`/`.serviceRevoke`/
`.serviceQuery` changes the syscall encoding.
**Mitigation:** Reuse IDs 11/12 + add 13 for new syscalls to minimize churn.

### Risk 4: Test Fixture Drift (LOW)
The expected output file has ~20 service-related lines that need updating.
**Mitigation:** Update fixtures atomically with trace harness changes in O6.

### Risk 5: Capability Slot Revocation Cascades (LOW)
When a capability slot is deleted via `cspaceDeleteSlot`, registered services
referencing that slot may become invalid.
**Mitigation:** The registry invariant `registryEndpointValid` captures validity at
the point of invariant assertion, not as a persistent guarantee. This matches
seL4's eventual consistency model for capabilities.

---

## 8. Success Criteria

### Technical
- [ ] All new operations are total, deterministic, and side-effect explicit
- [ ] Registry invariants proven without sorry/axiom
- [ ] Dependency cycle detection retained with existing proof infrastructure
- [ ] `lake build` succeeds at every phase boundary
- [ ] `test_full.sh` passes after all phases complete

### Architectural
- [ ] No lifecycle management (`serviceStart`/`serviceStop`/`serviceRestart`) in kernel
- [ ] No policy configuration (`ServiceConfig`) in kernel
- [ ] Service registration is capability-mediated (no global registry)
- [ ] Interface specs use concrete types (no universe polymorphism)
- [ ] API surface ≤ 7 primitives (register, revoke, lookup, registerInterface, plus retained dependency ops)

### Formal
- [ ] `registryInvariant` preservation proven for all operations
- [ ] Cross-subsystem frame lemmas complete (registry ops preserve all other invariants)
- [ ] NI proofs for registry operations proven
- [ ] `apiInvariantBundle_default` holds with registry invariant included
- [ ] Zero `sorry`/`axiom` in production proof surface

### Documentation
- [ ] WORKSTREAM_HISTORY.md updated with WS-O entry
- [ ] SELE4N_SPEC.md reflects new service architecture
- [ ] GitBook chapters updated
- [ ] CLAIM_EVIDENCE_INDEX.md updated with WS-O claims
- [ ] codebase_map.json regenerated

---

## 9. Verification Commands

After each phase:
```bash
source ~/.elan/env && lake build          # Must succeed
./scripts/test_fast.sh                     # Tier 0+1
./scripts/test_smoke.sh                    # Tier 0-2 (minimum before PR)
```

After Phase O6 (tests complete):
```bash
./scripts/test_full.sh                     # Tier 0-3
```

After Phase O7 (docs complete):
```bash
./scripts/generate_codebase_map.py --pretty --check  # Metrics sync
./scripts/test_full.sh                                # Full validation
```

---

## 10. Final Principle

> The kernel enforces constraints — it does not decide behavior.

Service lifecycle, dependency ordering, naming, and discovery are **policy
decisions** that belong in user space. The kernel's role is to enforce
**capability safety** and **interface contracts** — nothing more.
