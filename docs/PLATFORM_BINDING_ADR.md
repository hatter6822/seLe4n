# ADR: Platform Binding Architecture (H3 Preparation)

**Status:** Accepted
**Date:** 2026-03-01
**Context:** Pre-H3 structural preparation for hardware-specific implementation
**Relates to:** WS-B1 (VSpace ADR), WS-C7 (Finite Object Store ADR), H3 (Platform binding)

---

## Decision

Introduce a `Platform/` directory with a `PlatformBinding` typeclass, platform-
specific contract stubs, and supporting foundational types (`MachineConfig`,
`MemoryRegion`, `VSpaceBackend`) to structurally prepare the codebase for
hardware-specific implementation without forking the repository.

## Context

seLe4n is transitioning from abstract kernel semantics (H0–H2) toward hardware-
specific implementation on Raspberry Pi 5 (H3). The question was whether to:

1. **Fork** the repository into abstract-kernel and hardware-binding repos, or
2. **Reorganize** with a new `Platform/` namespace in the existing monorepo.

## Analysis

### Why not fork

1. **Proof chain continuity.** The `RuntimeBoundaryContract` instantiation for
   RPi5 must import `SeLe4n.Model.State`, `SeLe4n.Kernel.Architecture.Assumptions`,
   and satisfy invariants defined in `SeLe4n.Kernel.Architecture.Invariant`. A
   cross-repo boundary would require coordinated releases for every change to
   `SystemState`, `KernelError`, or any invariant bundle.

2. **Contract instantiation IS the proof.** The `AdapterProofHooks` structure
   requires the platform to prove preservation of abstract invariant bundles.
   Separate repos mean the platform code compiles against a snapshot, losing the
   guarantee that proofs compose against the live kernel.

3. **Codebase scale.** At ~19K LoC, monorepo tooling is not a bottleneck.

### Why this organization

The `Platform/` namespace provides:

- **Clean import boundaries:** `SeLe4n.Kernel.*` never imports `SeLe4n.Platform.*`.
  Platform modules import `Kernel.Architecture.*` to instantiate contracts.
- **Multiple build targets without repo splits:** Lake handles `SeLe4n`,
  `Platform.Sim`, and `Platform.RPi5` as discoverable library modules.
- **Future multi-platform readiness:** Adding RISC-V or x86 later is just
  `Platform/RiscV/` with new contract instantiations.
- **Structural hygiene enforcement:** Platform test fixtures live in `Platform/Sim/`
  rather than `Testing/`, making the production/test boundary architectural.

## Changes Introduced

### New types (additive to Machine.lean)

- `MemoryKind` — RAM, Device, Reserved
- `MemoryRegion` — base PAddr, size, kind, with `contains`/`overlaps` helpers
- `MachineConfig` — register width, address width, page size, max ASID, memory map

### New typeclass (Platform/Contract.lean)

- `PlatformBinding` — bundles `MachineConfig`, `RuntimeBoundaryContract`,
  `BootBoundaryContract`, `InterruptBoundaryContract` with a platform name

### New abstraction (Architecture/VSpaceBackend.lean)

- `VSpaceBackend` class — abstract page map/unmap/lookup with ASID preservation,
  round-trip correctness, and non-interference obligations
- `listVSpaceBackend` instance — delegates to existing `VSpaceRoot` methods and
  lemmas (zero new proofs required)

### Extended boot contract (additive to Assumptions.lean)

- `ExceptionLevel` — EL1/EL2 enumeration
- `ExtendedBootBoundaryContract extends BootBoundaryContract` — adds entry level,
  MMU state, device tree base, kernel entry point, initial stack pointer

### Platform instantiations

- `Platform/Sim/` — `SimPlatform` with permissive runtime, trivially-true boot,
  64-bit idealized machine config with 256 MiB RAM region
- `Platform/RPi5/` — `RPi5Platform` with BCM2712 memory map, GIC-400 constants,
  ARM64 config (44-bit PA, 16-bit ASID), RAM-only memory access contract

## What was NOT changed

- No existing definitions were moved or renamed
- No existing invariant anchors were broken (all 400+ tier-3 checks pass)
- No existing imports were modified in `SeLe4n/Kernel/` modules
- The `Testing/RuntimeContractFixtures.lean` fixtures remain in place (tier-3
  anchors depend on their exact location)

## Consequences

- H3 hardware binding can now proceed by populating `Platform/RPi5/` stubs
  with hardware-validated contracts and adding an ARMv8 `VSpaceBackend` instance
- The abstract kernel proof surface remains completely unchanged
- New platforms can be added as `Platform/<name>/` without restructuring
- The `PlatformBinding` typeclass enables parameterized adapter operations

## Migration path (future)

1. H3: Populate RPi5 contracts with hardware-validated predicates
2. H3: Implement ARMv8 page table `VSpaceBackend` instance
3. H3: Add ARM Generic Timer and GIC-400 adapter bindings
4. H4: Connect executable trace scenarios to hardware test fixtures
5. Post-H4: Consider `FiniteMap` abstraction for data structure optimization
