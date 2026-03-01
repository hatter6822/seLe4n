# seLe4n Hardware Readiness Audit — v0.12.5

**Date**: 2026-03-01
**Scope**: All 34 `.lean` files (19,483 production LoC, 1,747 test LoC), 16 shell scripts, all documentation
**Build**: Passes (64 jobs, zero warnings) | **All test tiers**: Pass (Tier 0-4)
**Purpose**: Assess readiness to transition from abstract model to Raspberry Pi 5 hardware binding

---

## Executive Summary

seLe4n v0.12.5 has completed all WS-F audit remediation (WS-F1 through WS-F4) and
is ready to begin hardware-specific workstreams. The codebase contains **zero
`sorry`, zero `axiom`** across the entire production proof surface. All 522
machine-checked theorems compile and pass. All four test tiers (hygiene, build,
trace/negative, invariant surface) pass without warnings.

The architecture-boundary layer (Assumptions, Adapter, VSpace) provides clean
separation between platform-independent semantics and platform-specific bindings.
The adapter contract pattern (`RuntimeBoundaryContract`, `AdapterProofHooks`) is
structurally sound and ready for ARM64/BCM2712 instantiation.

**Hardware readiness: H2 COMPLETE, H3 READY TO BEGIN.**

---

## Proof Soundness

| Pattern              | Count | Severity |
|----------------------|-------|----------|
| `sorry`              | 0     | None     |
| `axiom`              | 0     | None     |
| `native_decide`      | 0     | None     |
| `admit`/`unsafe`     | 0     | None     |
| `partial` functions  | 0     | None     |
| Panicking operations | 0     | None     |
| Debug artifacts      | 0     | None     |

**TPI-D annotations**: 9 tracked proof incompleteness markers (TPI-D01 through
TPI-D09), all RESOLVED with formal proofs. No open TPI-D items remain.

---

## Codebase Metrics

| Metric | Value |
|--------|-------|
| Production Lean LoC | 19,483 |
| Test Lean LoC | 1,747 |
| Shell script LoC | 1,663 |
| Lean modules | 34 |
| Proved theorems | 522 |
| Executable test suites | 3 (NegativeState, InformationFlow, TraceSequenceProbe) |
| Test tiers | 4 (Hygiene, Build, Trace/Negative, Invariant Surface) + Nightly |
| Kernel subsystems | 7 (Scheduler, Capability, IPC, Lifecycle, Service, InfoFlow, Architecture) |
| API entry points | 30 stable |
| Invariant bundle conjuncts | 7 (scheduler, capability, IPC, IPC-scheduler, lifecycle, service, VSpace) |

---

## Hardware Readiness Matrix

| Stage | Description | Status | Evidence |
|-------|-------------|--------|----------|
| **H0** | Architecture-neutral semantics | **Complete** | 522 theorems, zero sorry/axiom |
| **H1** | Architecture-boundary interfaces | **Complete** | Assumptions, Adapter, VSpace modules |
| **H2** | Audit-driven proof deepening | **Complete** | WS-F1..F4 all closed |
| **H3** | Platform binding (RPi5) | **Ready to begin** | This audit |
| **H4** | Evidence convergence | Planned | Depends on H3 |

---

## Architecture Layer Assessment

### Machine Primitives (SeLe4n/Machine.lean — 138 lines)

**Status**: Sound abstract foundation, ready for hardware refinement.

| Primitive | Current Model | Hardware Binding Required |
|-----------|--------------|--------------------------|
| `RegName` | `Nat` (abstract) | Map to ARM64 ABI (x0-x30, sp, pc) |
| `RegValue` | `Nat` (unbounded) | Bind to 64-bit word |
| `Memory` | `PAddr → UInt8` (total, zero-default) | Add MMIO regions, partial mapping |
| `RegisterFile` | `{pc, sp, gpr}` | Extend with PSTATE, ELR, SPSR |
| `MachineState.timer` | `Nat` (monotonic counter) | Bind to ARM Generic Timer |

**Strengths**: 14 preservation theorems (read-after-write, frame isolation, zero-init).
**Gap**: No ISA-specific semantics — intentionally abstract for platform independence.

### Architecture Assumptions (Assumptions.lean — 145 lines)

**Status**: Excellent boundary abstraction. All 5 assumptions formally inventoried.

| Assumption | Contract | Consumer | Status |
|-----------|----------|----------|--------|
| `deterministicTimerProgress` | `RuntimeBoundaryContract.timerMonotonic` | `adapterAdvanceTimer` | Proven consumed |
| `deterministicRegisterContext` | `RuntimeBoundaryContract.registerContextStable` | `adapterWriteRegister` | Proven consumed |
| `memoryAccessSafety` | `RuntimeBoundaryContract.memoryAccessAllowed` | `adapterReadMemory` | Proven consumed |
| `bootObjectTyping` | `BootBoundaryContract` | Default state proofs | Proven consumed |
| `irqRoutingTotality` | `InterruptBoundaryContract` | IRQ handler lookup | Structural |

**Key theorem**: `assumptionInventoryComplete_holds` — every declared assumption is in the
canonical inventory. No hidden assumptions.

### Adapter Layer (Adapter.lean — 125 lines)

**Status**: Clean contract-gated adapters with determinism proofs.

Three runtime adapters (`adapterAdvanceTimer`, `adapterWriteRegister`, `adapterReadMemory`)
each check their contract predicate before state mutation. Failure maps to
`KernelError.notImplemented` or `.illegalState`.

**Key theorem**: `adapterAdvanceTimer_deterministic` — same inputs always yield same outputs.

### VSpace (VSpace.lean — 161 lines, VSpaceInvariant.lean — 362 lines)

**Status**: Sound single-level model with ASID binding and round-trip proofs.

| Operation | Invariant Preservation | Round-trip Proof |
|-----------|----------------------|------------------|
| `vspaceMapPage` | ASID-uniqueness + no-overlap | map-then-lookup returns mapped paddr |
| `vspaceUnmapPage` | ASID-uniqueness + no-overlap | unmap-then-lookup returns translationFault |
| `vspaceLookup` | Read-only (no state change) | N/A |

**Gap for H3**: Current model uses flat `List (VAddr × PAddr)` mappings.
Hardware binding requires ARMv8 4-level page tables (L0-L3), permission bits (R/W/X),
and TLB coherency model. The flat model is extensible — `VSpaceRoot` can be
refined without invalidating existing invariant proofs.

### Composed Invariant Bundle (Invariant.lean — 325 lines)

**Status**: 7-conjunct composed bundle with default-state base case.

```
proofLayerInvariantBundle =
  schedulerInvariantBundle ∧
  capabilityInvariantBundle ∧
  coreIpcInvariantBundle ∧
  ipcSchedulerCouplingInvariantBundle ∧
  lifecycleInvariantBundle ∧
  serviceLifecycleCapabilityInvariantBundle ∧
  vspaceInvariantBundle
```

**AdapterProofHooks**: Structure defined for conditional preservation proofs. Currently
uninstantiated — H3 will provide the first concrete instance for RPi5. The existing
conditional theorems (`adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle`, etc.)
will become unconditional once hooks are instantiated.

---

## Kernel Subsystem Assessment

### Scheduler (1,031 lines, 2 files)

**Determinism**: Fully deterministic. All transitions use explicit case analysis.
**Invariant coverage**: schedulerInvariantBundle (queueCurrentConsistent, runQueueUnique,
currentThreadValid) + kernelInvariant (adds currentThreadInActiveDomain).

| Transition | Invariant Preservation | Status |
|------------|----------------------|--------|
| `schedule` | schedulerInvariantBundle + kernelInvariant | Proved |
| `handleYield` | schedulerInvariantBundle | Proved |
| `timerTick` | schedulerInvariantBundle + kernelInvariant | Proved (WS-F4) |
| `switchDomain` | schedulerInvariantBundle | Proved |
| `scheduleDomain` | schedulerInvariantBundle | Proved |
| `chooseThread` | Read-only | N/A |

**H3 consideration**: `defaultTimeSlice = 5` is a model constant. Hardware binding should
make this configurable per-architecture (ARM Generic Timer tick frequency determines
real-time quantum).

### Capability (2,353 lines, 2 files)

**Determinism**: Fully deterministic.
**Invariant coverage**: capabilityInvariantBundle (CNode slot uniqueness, CDT consistency).

| Transition | Invariant Preservation | Status |
|------------|----------------------|--------|
| `cspaceMint` | capabilityInvariantBundle | Proved |
| `cspaceCopy` | capabilityInvariantBundle | Proved |
| `cspaceMove` | capabilityInvariantBundle | Proved |
| `cspaceMutate` | capabilityInvariantBundle | Proved (WS-F4) |
| `cspaceRevokeCdt` | capabilityInvariantBundle | Proved (WS-F4) |
| `cspaceRevokeCdtStrict` | capabilityInvariantBundle | Proved (WS-F4) |
| `cspaceDeleteSlot` | capabilityInvariantBundle | Proved |
| `cspaceInsertSlot` | capabilityInvariantBundle | Proved |

### IPC (6,451 lines, 3 files)

**Determinism**: Fully deterministic.
**Invariant coverage**: coreIpcInvariantBundle + ipcSchedulerCouplingInvariantBundle.

Legacy operations (7) and dual-queue operations (3) each have complete preservation
proofs. Compound operations (`endpointCall`, `endpointReplyRecv`, `endpointReply`)
proved via TPI-D09 (WS-F1). IPC message transfer (`IpcMessage` with registers, caps,
badge) wired into all dual-queue paths (WS-F1).

### Lifecycle (944 lines, 2 files)

**Determinism**: Fully deterministic.
**Invariant coverage**: lifecycleInvariantBundle (identity + capability-ref metadata).

`retypeFromUntyped` (WS-F2) with `UntypedObject` watermark tracking, device
restriction, and 4 untyped memory invariants (watermark, bounds, non-overlap,
unique IDs) all proved.

**H3 consideration**: Object ID freshness is currently a caller assumption. Hardware
binding should include a global ObjId allocator backed by a bounded pool.

### Service (1,468 lines, 2 files)

**Determinism**: Fully deterministic (BFS fuel-bounded).
**Invariant coverage**: serviceLifecycleCapabilityInvariantBundle (acyclicity, dependency
satisfaction).

Cycle detection via fuel-bounded BFS (`serviceBfsFuel = objectIndex.length + 256`).
Fuel exhaustion is conservative (assumes cycle present).

### Information Flow (2,389 lines, 4 files)

**Determinism**: Fully deterministic.
**Coverage**: N-domain parameterized labels (WS-E5), 7-field state projection (WS-F3),
15 non-interference theorems (12 standalone + 3 enforcement-NI bridges), 3 policy-gated
enforcement wrappers.

**Enforcement boundary (M-07)**: `endpointSendChecked`, `cspaceMintChecked`,
`serviceRestartChecked` are policy-gated. Capability-only operations rely on
possession-based authorization.

---

## Test Coverage Assessment

### Tier Results (all pass, zero warnings)

| Tier | Scope | Result |
|------|-------|--------|
| Tier 0 | Hygiene (forbidden markers, regression checks) | PASS |
| Tier 1 | Build (64 jobs, zero warnings) | PASS |
| Tier 2 | Trace fixture + negative-state suite + IF suite | PASS |
| Tier 3 | Invariant surface anchors (100+ theorem anchors) | PASS |
| Tier 4 | Nightly determinism + trace sequence probes (5 seeds) | PASS |

### Test Suite Coverage

| Suite | Tests | Coverage |
|-------|-------|----------|
| MainTraceHarness | 89 positive/negative checks | Scheduler, Capability, IPC, Lifecycle, Service, VSpace, Domain scheduling |
| NegativeStateSuite | 42 negative checks | Error paths for all subsystems including dual-queue, untyped memory |
| InformationFlowSuite | 55 checks | Flow policy, projection, enforcement, parameterized domains, CNode filtering |
| TraceSequenceProbe | 5 seeds × 320 steps | Randomized transition sequencing with expected-failure analysis |

### Coverage Gaps (acceptable for current phase)

1. **No hardware-specific tests**: Expected — H3 has not begun
2. **No stress tests for bounded resources**: objectIndex growth, CDT node allocation
3. **No timing/performance benchmarks**: Model is pure functions, not cycle-accurate

---

## Findings for H3 Planning

### H3-F01: AdapterProofHooks Instantiation Required (HIGH)

**Location**: `SeLe4n/Kernel/Architecture/Invariant.lean:50-66`
**Description**: `AdapterProofHooks` structure is defined but not instantiated. Success-path
preservation theorems are conditional on hook provision. H3 must provide the first concrete
instance for RPi5.
**Impact**: Adapter success paths cannot be used in end-to-end invariant arguments until
instantiated.
**Recommendation**: WS-G1 — Instantiate `AdapterProofHooks` with a proof-carrying RPi5
contract that satisfies `RuntimeBoundaryContract` predicates for ARM Generic Timer,
register context, and memory access.

### H3-F02: VSpace Requires Multi-Level Page Table Refinement (HIGH)

**Location**: `SeLe4n/Model/Object.lean:437-438`, `SeLe4n/Kernel/Architecture/VSpace.lean`
**Description**: Current VSpace uses flat `List (VAddr × PAddr)` mappings. ARMv8 uses
4-level page tables (L0-L3) with permission bits (R/W/X/XN), access/dirty flags.
**Impact**: Cannot model page permissions, TLB invalidation, or address space isolation.
**Recommendation**: WS-G2 — Extend `VSpaceRoot` to hierarchical page table model. Existing
invariant proofs (ASID uniqueness, no-overlap) should be preservable via refinement.

### H3-F03: Register File Needs ARM64 ABI Mapping (MEDIUM)

**Location**: `SeLe4n/Machine.lean:6-9`
**Description**: `RegName := Nat` and `RegValue := Nat` are abstract. ARM64 has 31
general-purpose registers (x0-x30), SP, PC, PSTATE, ELR_EL1, SPSR_EL1.
**Impact**: Cannot model context switch, exception entry/return, or system call ABI.
**Recommendation**: WS-G2 — Define ARM64 register enumeration and extend `RegisterFile`.

### H3-F04: Interrupt Model Needs Transition Semantics (MEDIUM)

**Location**: `SeLe4n/Kernel/Architecture/Assumptions.lean:51-54`
**Description**: `InterruptBoundaryContract` is defined (IRQ line support, handler mapping)
but no interrupt dispatch transitions exist. GIC-400 on RPi5 requires routing model.
**Impact**: Cannot model interrupt-driven preemption or device I/O.
**Recommendation**: WS-G3 — Add interrupt dispatch transitions with IRQ routing through
GIC-400 abstraction.

### H3-F05: Boot Sequence State Construction (MEDIUM)

**Location**: `SeLe4n/Kernel/Architecture/Assumptions.lean:38-41`
**Description**: `BootBoundaryContract` is defined but never instantiated. The default
`SystemState` serves as boot state. Hardware boot requires verified initial state
construction from device tree / memory map.
**Recommendation**: WS-G3 — Define boot sequence as a verified state construction from
BCM2712 device tree, proving the resulting state satisfies `apiInvariantBundle`.

### H3-F06: Bounded Resource Pools (MEDIUM)

**Location**: `SeLe4n/Model/State.lean:89-104` (objectIndex), various
**Description**: Several resources grow without formal bounds: objectIndex (monotonic
append-only, never pruned), CDT node IDs (simple increment), service dependency lists.
On RPi5 with finite RAM, unbounded growth will exhaust memory.
**Impact**: Long-running kernel could exhaust memory without detection.
**Recommendation**: WS-G4 — Define `MAX_OBJECTS`, `MAX_CDT_NODES`, `MAX_DEPENDENCIES`
constants and prove resource pool invariants.

### H3-F07: Memory Model Needs MMIO Separation (LOW)

**Location**: `SeLe4n/Machine.lean:29`
**Description**: `Memory := PAddr → UInt8` is a total function. Hardware has distinct
regions: normal memory, device memory (MMIO), reserved. Device memory has side effects
on read (e.g., clearing interrupt status).
**Recommendation**: WS-G4 — Partition memory model into normal/device/reserved regions
with distinct access semantics.

### H3-F08: Forward Declaration Not Yet Integrated (LOW)

**Location**: `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean:47-51`
**Description**: `boundedAddressTranslation` is declared but not integrated into the
VSpace invariant bundle. States that all translated physical addresses are below a bound.
**Recommendation**: Integrate into `vspaceInvariantBundle` during H3 when physical
address bounds are defined by the RPi5 memory map.

---

## Recommended H3 Workstream Structure

| Workstream | Scope | Priority | Dependencies |
|------------|-------|----------|-------------|
| **WS-G1** | AdapterProofHooks instantiation (RPi5 contract) | Critical | None |
| **WS-G2** | ARM64 register ABI + multi-level VSpace | High | None |
| **WS-G3** | Interrupt dispatch + boot sequence | High | WS-G1 |
| **WS-G4** | Resource bounds + MMIO separation | Medium | WS-G2 |

---

## Conclusion

seLe4n v0.12.5 has achieved the prerequisites for hardware binding:

1. **Zero proof debt**: No sorry, no axiom, all TPI-D items resolved.
2. **Complete audit remediation**: WS-F1 through WS-F4 all closed.
3. **Clean test surface**: All four test tiers pass without warnings.
4. **Sound architecture boundary**: Assumptions, adapters, and contracts provide
   clean extension points for platform-specific binding.
5. **522 machine-checked theorems** across 7 kernel subsystems.

The project is ready to proceed to **H3: Platform binding** for Raspberry Pi 5.
The recommended WS-G workstream structure provides a systematic path from
abstract contracts to concrete hardware interfaces.
