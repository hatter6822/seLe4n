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

### Test-only fixtures (non-production)

- `SeLe4n/Testing/RuntimeContractFixtures.lean` contains permissive fixtures:
  - `SeLe4n.Testing.runtimeContractAcceptAll`
  - `SeLe4n.Testing.runtimeContractDenyAll`
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
2. Keep permissive or denial-style fixtures in test-only modules under `SeLe4n/Testing/*` (or non-kernel test executables).
3. Run `./scripts/test_fast.sh` locally; do not bypass Tier 0 failures.
4. If a new fixture is added, document why it cannot be a production contract.

## 5. Review guidance

A PR should be blocked if any of the following appear:

- a production module under `SeLe4n/Kernel` references `SeLe4n.Testing.RuntimeContractFixtures` or other test-only fixtures,
- permissive contract fixtures are used to justify production theorem assumptions,
- adapter/invariant changes weaken explicit contract checks without corresponding policy updates.
