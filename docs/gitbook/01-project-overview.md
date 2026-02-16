# Project Overview

## 1. Motivation

seLe4n is a Lean 4 formalization effort for building an executable, machine-checked model of core
seL4-style microkernel behavior. The project exists to make three concerns evolve together in one
engineering loop:

1. deterministic transition semantics,
2. machine-checked invariant preservation,
3. milestone-oriented delivery with explicit acceptance criteria.

This combination is deliberate: high-assurance work is most useful when it remains operationally
iterable by contributors who are not formal-methods specialists.

## 2. Why this project matters

seLe4n addresses a common reliability gap in systems work:

- architecture docs can drift from what code actually does,
- prototype code can drift from proof claims,
- milestone goals can drift from test and CI gates.

The repository structure and documentation strategy are designed to prevent that drift by coupling
semantics, proofs, executable traces, and milestone docs.

## 3. What is implemented today

Closed baseline slices:

- Bootstrap: initial Lean project + model scaffolding,
- M1: scheduler semantics and preservation surfaces,
- M2: CSpace/capability operations + authority invariants,
- M3: IPC seed semantics,
- M3.5: waiting handshake + scheduler coherence predicates,
- M4-A: lifecycle/retype foundations,
- M4-B: lifecycle-capability hardening with stale-reference safety.

Current planning focus:

- M5 kickoff preparation: service graph semantics and policy-oriented authority modeling.

## 4. How to think about the architecture

The codebase is organized as layered contracts:

- **Model layer** (`SeLe4n/Model/*`): object/state representation and typed lookup/update helpers.
- **Subsystem transitions** (`SeLe4n/Kernel/*/Operations.lean`): executable behavior with explicit
  error paths.
- **Invariant layer** (`SeLe4n/Kernel/*/Invariant.lean`): named safety predicates and composed
  bundles.
- **Executable evidence** (`Main.lean`): scenario traces used by Tier 2 fixture checks.
- **Validation scripts** (`scripts/test_*.sh`): tiered CI contract from hygiene to nightly lanes.

## 5. Contributor mental model (definition-of-done loop)

For milestone-moving changes, contributors should follow this sequence:

1. update transition semantics first,
2. add or refine narrow invariant components,
3. prove local preservation,
4. prove composed preservation,
5. expose behavior in executable traces where relevant,
6. wire proof/trace symbols into test tiers,
7. update spec + README + GitBook in the same PR.

## 6. Target outcomes for the next slice (M5)

M5 is intended to convert the M4 lifecycle-capability foundation into service-oriented system
reasoning.

Primary target outcomes:

1. **Service graph model**
   - represent service instances and restart/isolation relationships in a theorem-friendly form.
2. **Policy surfaces**
   - encode policy constraints over capability authority without breaking existing bundle layering.
3. **Failure semantics for orchestration stories**
   - ensure restart/recovery paths are explicit and theorem-covered, not only success paths.
4. **Architecture-binding assumptions**
   - make platform assumptions first-class interfaces so core proofs remain reusable.

## 7. Project technical value for developers

seLe4n can be used today as:

1. a **reference microkernel semantics lab** for experimenting with state-machine changes safely,
2. a **proof-aware regression framework** where theorem symbols and executable traces guard claims,
3. an **onboarding corpus** for learning practical Lean theorem-proving in systems contexts,
4. a **design review artifact** for discussing authority and lifecycle edge cases with precision,
5. a **staging ground for hardware-bound assurance plans** before architecture-specific lock-in.

## 8. Long-horizon direction

The long-horizon objective remains mobile-first hardware relevance through staged refinement:

1. architecture-neutral semantic hardening,
2. explicit architecture binding interfaces,
3. subsystem trust-boundary mapping,
4. integration with platform and test evidence.

See the roadmap and delivery-plan chapters for execution-level details.
