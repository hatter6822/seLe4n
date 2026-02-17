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
- M5 service-graph and policy-surface completion.

Current active slice:

- **M7 audit remediation workstreams (WS-A1 through WS-A8)**.

## 4. Architecture mental model

The codebase is organized as layered contracts:

- **Model layer** (`SeLe4n/Model/*`): object/state representation and update helpers.
- **Subsystem transitions** (`SeLe4n/Kernel/*/Operations.lean`): executable behavior with
  explicit error paths.
- **Invariant layer** (`SeLe4n/Kernel/*/Invariant.lean`): named predicates and composed bundles.
- **Executable evidence** (`Main.lean`): scenario traces used by fixture checks.
- **Validation scripts** (`scripts/test_*.sh`): tiered CI contract from hygiene to nightly lanes.

## 5. Current-slice outcomes (M7 audit remediation)

The active remediation slice is successful when contributors deliver all of the following:

1. CI and quality-gate hardening (including Tier 3 promotion and cache/security hygiene),
2. architecture/module cleanup and API boundary refinements,
3. type-safety, testing-depth, and documentation-governance upgrades mapped to audit findings,
4. traceable closure of audit criticisms/recommendations with synchronized code/proof/test/docs evidence.

See dedicated execution chapters: [M7 Current Slice Outcomes and Workstreams](21-m7-current-slice-outcomes-and-workstreams.md) and [Repository Audit Remediation Workstreams](20-repository-audit-remediation-workstreams.md).

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
