# Codebase Reference (Deep Developer Map)

This chapter maps where semantics, proofs, and execution evidence live in the current repository.

## 1. Repository-level structure

- `SeLe4n.lean`
  - package export root.
- `Main.lean`
  - executable scenario trace harness used by smoke checks.
- `SeLe4n/`
  - model, transition, and theorem modules.
- `scripts/`
  - tiered test runners and support helpers.
- `tests/fixtures/`
  - expected trace fragments for regression checks.

## 2. Module inventory by responsibility

### Foundation layer

- `SeLe4n/Prelude.lean`
  - IDs/aliases and core monadic kernel execution shape.
- `SeLe4n/Machine.lean`
  - machine-level state helpers.
- `SeLe4n/Model/Object.lean`
  - object-level representations (TCB with priority, deadline, timeSlice, domain).
- `SeLe4n/Model/State.lean`
  - global system-state composition and update helpers.

### Kernel transition/invariant families

- `SeLe4n/Kernel/Scheduler/Operations.lean`
- `SeLe4n/Kernel/Scheduler/Invariant.lean`
- `SeLe4n/Kernel/Capability/Operations.lean`
- `SeLe4n/Kernel/Capability/Invariant.lean`
- `SeLe4n/Kernel/IPC/Operations.lean`
- `SeLe4n/Kernel/IPC/Invariant.lean`
- `SeLe4n/Kernel/Lifecycle/Operations.lean`
- `SeLe4n/Kernel/Lifecycle/Invariant.lean`
- `SeLe4n/Kernel/Service/Operations.lean`
- `SeLe4n/Kernel/Service/Invariant.lean`

### Architecture boundary

- `SeLe4n/Kernel/Architecture/Assumptions.lean`
  - named architecture-facing assumption interfaces and contract references.
- `SeLe4n/Kernel/Architecture/Adapter.lean`
  - deterministic adapter entrypoints (`adapterAdvanceTimer`, `adapterReadMemory`, `adapterWriteMemory`).
- `SeLe4n/Kernel/Architecture/VSpace.lean`
  - VSpace address-space operations (`vspaceMapPage`, `vspaceUnmapPage`, `vspaceLookup`),
    ASID root resolution, page-table management.
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`
  - VSpace invariant bundle, success/error preservation theorems, round-trip correctness theorems.
- `SeLe4n/Kernel/Architecture/Invariant.lean`
  - `proofLayerInvariantBundle` connecting adapter assumptions to theorem-layer invariants.

### Information-flow layer

- `SeLe4n/Kernel/InformationFlow/Policy.lean`
  - security labels (`Confidentiality`, `Integrity`, `SecurityLabel`), policy lattice (`securityFlowsTo`).
- `SeLe4n/Kernel/InformationFlow/Projection.lean`
  - observer projection helpers, `lowEquivalent` relation scaffold.
- `SeLe4n/Kernel/InformationFlow/Enforcement.lean`
  - checked kernel operations that wire policy into enforcement boundaries.
- `SeLe4n/Kernel/InformationFlow/Invariant.lean`
  - non-interference preservation theorems across kernel subsystems.

### API

- `SeLe4n/Kernel/API.lean`
  - unified public kernel interface: `KernelAPIInvariant` bundle alias, 20+ entry-point
    abbreviations (`apiSchedule`, `apiCspaceMint`, `apiEndpointSend`, etc.), API-level
    preservation theorems, and `default_satisfies_kernelAPIInvariant`.

### Testing modules

- `SeLe4n/Testing/StateBuilder.lean`
  - test-state construction helpers.
- `SeLe4n/Testing/RuntimeContractFixtures.lean`
  - runtime-contract fixtures for architecture adapter testing.
- `SeLe4n/Testing/InvariantChecks.lean`
  - executable invariant-checking logic for trace harness validation.
- `SeLe4n/Testing/MainTraceHarness.lean`
  - scenario execution engine for trace output and fixture comparisons.

### Evidence and automation

- `scripts/test_tier0_hygiene.sh`
- `scripts/test_tier1_build.sh`
- `scripts/test_tier2_trace.sh`
- `scripts/test_tier3_invariant_surface.sh`
- `scripts/test_tier4_nightly_candidates.sh`
- umbrella runners: `test_fast.sh`, `test_smoke.sh`, `test_full.sh`, `test_nightly.sh`

## 3. M6 closeout (all completed)

### M6 boundary extraction (WS-M6-A) ✅

- `SeLe4n/Kernel/Architecture/Assumptions.lean`
- architecture-facing assumptions isolated into explicit, named interface surfaces.

### M6 adapter semantics (WS-M6-B) ✅

- `SeLe4n/Kernel/Architecture/Adapter.lean`
- deterministic adapter entrypoints with bounded failure mapping.

### M6 proof integration (WS-M6-C) ✅

- `SeLe4n/Kernel/Architecture/Invariant.lean`
- adapter assumptions connected to theorem-layer invariants through `proofLayerInvariantBundle`.

### M6 evidence expansion (WS-M6-D) ✅

- `Main.lean`, `tests/fixtures/main_trace_smoke.expected`
- executable/test evidence for both success and bounded failure behavior.

## 4. Raspberry Pi 5 placement guidance

M6 interfaces are stable. Raspberry Pi 5-specific work should:

1. instantiate interface contracts rather than rewriting core modules,
2. avoid embedding platform details directly into architecture-neutral invariant bundles,
3. preserve import stability from `SeLe4n.lean` and interface discoverability from `Kernel/API.lean`.

## 5. High-signal contributor checklist

Before opening an architecture-boundary PR:

1. identify affected module family and invariant bundle,
2. ensure failure-path semantics are explicit,
3. update tests/fixtures/symbol anchors as needed,
4. synchronize docs (README/spec/DEVELOPMENT/GitBook),
5. include a short "what this unlocks for Raspberry Pi 5 path" note.
