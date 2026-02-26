# Project Overview

## 1. Motivation

seLe4n is a Lean 4 formalization effort for an executable, machine-checked model of core
seL4-style microkernel behavior. The project keeps three concerns in one engineering loop:

1. deterministic transition semantics,
2. machine-checked invariant preservation,
3. milestone-oriented delivery with explicit acceptance criteria.

## 2. Why this project matters

seLe4n reduces a common systems-assurance failure mode: drift between code, proof claims, and
planning artifacts. The repository structure and test/documentation workflow are designed to keep
these artifacts synchronized.

## 3. What is implemented today

Closed baseline slices:

- Bootstrap,
- M1 scheduler semantics and preservation,
- M2 capability/CSpace operations + authority invariants,
- M3 IPC seed semantics,
- M3.5 waiting handshake + scheduler coherence,
- M4-A lifecycle/retype foundations,
- M4-B lifecycle-capability composition hardening,
- M5 service-graph and policy-surface completion,
- M6 architecture-boundary assumptions/adapters/invariant hooks,
- M7 audit remediation (WS-A1..WS-A8).

Completed audit portfolios:

- **Comprehensive Audit 2026-02 execution (WS-B portfolio)** with WS-B1 through WS-B11 completed.
- **WS-C portfolio** (v0.9.32 workstream plan): WS-C1..WS-C8 completed.

Completed audit portfolios (continued):

- **WS-D portfolio** (v0.11.0 workstream plan): WS-D1..WS-D4 completed; WS-D5/WS-D6 absorbed into WS-E.

Current active portfolio:

- **WS-E portfolio** (v0.11.6 workstream plan): WS-E1 through WS-E6 completed.

## 4. Architecture mental model

The codebase is organized as layered contracts:

- **Model layer** (`SeLe4n/Model/*`): object/state representation and update helpers.
- **Subsystem transitions** (`SeLe4n/Kernel/*/Operations.lean`): executable behavior with
  explicit error paths.
- **Invariant layer** (`SeLe4n/Kernel/*/Invariant.lean`): named predicates and composed bundles.
- **Executable evidence** (`Main.lean`): scenario traces used by fixture checks.
- **Validation scripts** (`scripts/test_*.sh`): tiered CI contract from hygiene to nightly lanes.

## 5. Current-slice outcomes (WS-E portfolio)

The active slice is successful when contributors deliver all of the following:

1. closure of v0.11.6 audit findings via WS-E workstreams (WS-E1..WS-E6),
2. deterministic CI + trace reproducibility preserved through every workstream increment,
3. theorem/invariant surfaces remain discoverable and preservation-focused,
4. synchronized updates across README/spec/development guide/GitBook + audit planning artifacts.

For full project scope and milestone details, see [`docs/spec/SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md).
For the seL4 microkernel reference, see [`docs/spec/SEL4_SPEC.md`](../spec/SEL4_SPEC.md).

See dedicated execution chapters: [v0.11.6 Audit Workstream Planning](32-v0.11.0-audit-workstream-planning.md) and [Specification & Roadmap](05-specification-and-roadmap.md).

## 6. Hardware trajectory update

The first real hardware architecture focus for seLe4n remains **Raspberry Pi 5**. This direction
now follows completion of the active audit-remediation workstreams and emphasizes incremental
binding without invalidating architecture-neutral proof investment.

See [Path to Real Hardware (Raspberry Pi 5 First)](10-path-to-real-hardware-mobile-first.md).

## 7. Contributor definition-of-done loop

For milestone-moving changes:

1. update transition semantics,
2. add/refine narrow invariant components,
3. prove local preservation,
4. prove composed preservation,
5. expose behavior in executable traces,
6. add symbol/fixture anchors in tests,
7. synchronize spec, README, and GitBook docs.
