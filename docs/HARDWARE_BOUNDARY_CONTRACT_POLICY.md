# Hardware Boundary Contract Policy

This policy defines how runtime hardware-boundary contracts are separated between
production semantics and test-only fixtures.

## 1. Purpose

WS-A5 hardens the boundary between trusted runtime contracts and permissive testing fixtures so
reviewers can quickly detect misuse and contributors can reason about what is safe in production.

## 2. Contract classes

### Production contract surfaces (trusted)

- `SeLe4n/Kernel/Architecture/Assumptions.lean` defines trusted contract interfaces:
  - `BootBoundaryContract`
  - `RuntimeBoundaryContract`
  - `InterruptBoundaryContract`
- `SeLe4n/Kernel/Architecture/Adapter.lean` consumes `RuntimeBoundaryContract`
  through explicit success/error branches.
- `SeLe4n/Kernel/Architecture/Invariant.lean` proves preservation theorems over the same trusted
  contract surface.

### Platform binding layer (H3-prep)

- `SeLe4n/Platform/Contract.lean` defines `PlatformBinding` typeclass bundling
  `MachineConfig`, `RuntimeBoundaryContract`, `BootBoundaryContract`, and
  `InterruptBoundaryContract`.
- `SeLe4n/Platform/Sim/*` provides simulation-target platform contracts
  (permissive/restrictive) for trace harness and test execution.
- `SeLe4n/Platform/RPi5/*` provides Raspberry Pi 5 platform-specific contract
  stubs (BCM2712 memory map, ARM64 config, RAM-only access contract).
- Platform modules import `SeLe4n/Kernel/Architecture/Assumptions.lean` but
  are not imported by any `SeLe4n/Kernel/` module.

### Test-only fixtures (non-production)

- `SeLe4n/Testing/RuntimeContractFixtures.lean` contains permissive fixtures:
  - `SeLe4n.Testing.runtimeContractAcceptAll`
  - `SeLe4n.Testing.runtimeContractDenyAll`
- `SeLe4n/Platform/Sim/RuntimeContract.lean` contains parallel simulation contracts:
  - `SeLe4n.Platform.Sim.simRuntimeContractPermissive`
  - `SeLe4n.Platform.Sim.simRuntimeContractRestrictive`
- These fixtures exist only to drive executable trace scenarios and must not appear in
  production kernel modules under `SeLe4n/Kernel`.

## 3. Import-boundary rule

- Production module rule: files under `SeLe4n/Kernel` must not reference test-only runtime contract
  fixtures.
- Enforcement: `scripts/test_tier0_hygiene.sh` fails if `SeLe4n/Kernel` references
  `SeLe4n.Testing.RuntimeContractFixtures` or `SeLe4n.Testing.runtimeContractAcceptAll` /
  `SeLe4n.Testing.runtimeContractDenyAll`.

## 4. Contributor checklist (WS-A5)

Before merging any PR that touches architecture-boundary semantics:

1. Ensure new runtime contract definitions intended for production live under
   `SeLe4n/Kernel/Architecture/*`.
2. Keep permissive or denial-style fixtures in test-only modules under
   `SeLe4n/Testing/*` or `SeLe4n/Platform/Sim/*` (never in `SeLe4n/Kernel/`).
3. Platform-specific contracts go in `SeLe4n/Platform/<target>/*`.
4. Run `./scripts/test_fast.sh` locally; do not bypass Tier 0 failures.
5. If a new fixture is added, document why it cannot be a production contract.

## 5. Review guidance

A PR should be blocked if any of the following appear:

- a production module under `SeLe4n/Kernel` references `SeLe4n.Testing.RuntimeContractFixtures` or other test-only fixtures,
- permissive contract fixtures are used to justify production theorem assumptions,
- adapter/invariant changes weaken explicit contract checks without corresponding policy updates.
