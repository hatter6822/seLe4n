<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/logo_dark.png" />
    <img src="assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.14.5-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  A microkernel written in Lean 4 with machine-checked proofs, inspired by the
  <a href="https://sel4.systems">seL4</a> architecture. First hardware target:
  <strong>Raspberry Pi 5</strong>.
</p>
<p align="center">
  <div align="center">
    Created thoughtfully with the help of:
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>TREAT THIS KERNEL ACCORDINGLY</strong>
  </div>
</p>

---

## What is seLe4n?

seLe4n is a microkernel built from the ground up in Lean 4. Every kernel
transition is an executable pure function. Every invariant is machine-checked
by the Lean type-checker — zero `sorry`, zero `axiom`. The entire proof surface
compiles to native code with no admitted proofs.

The project began as a formalization of seL4 semantics and has evolved into a
novel kernel that preserves seL4's capability-based security model while
introducing substantial architectural improvements:

- **O(1) hash-based kernel hot paths** — all object stores, run queues, CNode slots, VSpace mappings, and IPC queues use `Std.HashMap`/`Std.HashSet`
- **Service orchestration layer** for component lifecycle and dependency management with deterministic partial-failure semantics
- **Node-stable capability derivation tree** with `childMap` HashMap index for O(1) slot transfer, revocation, and descendant lookup
- **Intrusive dual-queue IPC** with per-thread `queuePrev`/`queuePPrev`/`queueNext` links for O(1) enqueue, dequeue, and mid-queue removal
- **Parameterized N-domain information-flow** framework with two-dimensional confidentiality/integrity labels (beyond seL4's binary partition)
- **EDF + priority scheduling** with dequeue-on-dispatch semantics, per-TCB register context with inline context switch, priority-bucketed `RunQueue`, domain-aware partitioning

## Current state

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| Attribute | Value |
|-----------|-------|
| **Version** | `0.14.5` |
| **Lean toolchain** | `v4.28.0` |
| **Production Lean LoC** | 31,295 across 65 files |
| **Test Lean LoC** | 2,413 across 3 test suites |
| **Proved declarations** | 958 theorem/lemma declarations (zero sorry/axiom) |
| **Total declarations** | 1,792 across 68 modules |
| **Target hardware** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Latest audit** | [`AUDIT_CODEBASE_v0.13.6.md`](docs/audits/AUDIT_CODEBASE_v0.13.6.md) — zero critical issues |
| **Codebase map** | [`docs/codebase_map.json`](docs/codebase_map.json) — machine-readable declaration inventory |

Metrics are derived from the codebase by `./scripts/generate_codebase_map.py`
and stored in [`docs/codebase_map.json`](docs/codebase_map.json) under the
`readme_sync` key. Update all documentation together using
`./scripts/report_current_state.py` as a cross-check.

## Quick start

```bash
./scripts/setup_lean_env.sh   # install Lean toolchain
lake build                     # compile all modules
lake exe sele4n                # run trace harness
./scripts/test_smoke.sh        # validate (hygiene + build + trace + negative-state + docs sync)
```

## Onboarding path

New to the project? Follow this reading order:

1. **This README** — project identity, architecture, and source layout
2. [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md) — day-to-day workflow, validation loop, PR checklist
3. [`docs/gitbook/README.md`](docs/gitbook/README.md) — full handbook (architecture deep dives, proofs, hardware path)
4. [`docs/codebase_map.json`](docs/codebase_map.json) — machine-readable module and declaration inventory

For workstream planning and history, see [`docs/WORKSTREAM_HISTORY.md`](docs/WORKSTREAM_HISTORY.md).

## Project documentation

| Document | Purpose |
|----------|---------|
| [`docs/spec/SELE4N_SPEC.md`](docs/spec/SELE4N_SPEC.md) | Project specification and milestones |
| [`docs/spec/SEL4_SPEC.md`](docs/spec/SEL4_SPEC.md) | seL4 reference semantics |
| [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md) | Day-to-day workflow, validation loop, PR checklist |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](docs/TESTING_FRAMEWORK_PLAN.md) | Tiered test gates and CI contract |
| [`docs/WORKSTREAM_HISTORY.md`](docs/WORKSTREAM_HISTORY.md) | Complete workstream history, roadmap, and audit plan index |
| [`docs/gitbook/README.md`](docs/gitbook/README.md) | Full handbook (architecture, design, proofs, hardware path) |
| [`docs/codebase_map.json`](docs/codebase_map.json) | Machine-readable codebase inventory (synced with README) |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | Contribution mechanics and PR requirements |
| [`CHANGELOG.md`](CHANGELOG.md) | Version history |

## Validation commands

```bash
./scripts/test_fast.sh      # Tier 0 + Tier 1 (hygiene + build)
./scripts/test_smoke.sh     # + Tier 2 (trace + negative-state + docs sync)
./scripts/test_full.sh      # + Tier 3 (invariant surface anchors)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4 (nightly determinism)
```

Run at least `test_smoke.sh` before any PR. Run `test_full.sh` when changing
theorems, invariants, or documentation anchors.

## Codebase map

[`docs/codebase_map.json`](docs/codebase_map.json) is the machine-readable
inventory of every module and declaration in the project. It feeds the
[seLe4n.org](https://github.com/hatter6822/hatter6822.github.io) website and
serves as the unified source of truth for project metrics.

```bash
./scripts/generate_codebase_map.py --pretty          # regenerate
./scripts/generate_codebase_map.py --pretty --check   # validate without writing
```

The map includes:
- **`readme_sync`** — project-level metrics (version, LoC, theorem count) used by README and docs
- **`source_sync`** — deterministic SHA256 digest of all Lean sources for cache invalidation
- **`modules`** — per-module declaration inventory with `called` arrays for internal references

The post-merge `.github/workflows/codebase_map_sync.yml` job auto-refreshes the
map on main as a backstop for drift.

## Architecture

seLe4n is organized as layered contracts, each with executable transitions and
machine-checked invariant preservation proofs:

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│   Scheduler  │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│  RunQueue    │  CSpace/CDT │  DualQueue │  Retype   │  Orchestration │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│         Information Flow  (Policy, Projection, Enforcement)          │
├──────────────────────────────────────────────────────────────────────┤
│     Architecture  (VSpace, VSpaceBackend, Adapter, Assumptions)      │
├──────────────────────────────────────────────────────────────────────┤
│                     Model  (Object, State, CDT)                      │
├──────────────────────────────────────────────────────────────────────┤
│             Foundations  (Prelude, Machine, MachineConfig)           │
├──────────────────────────────────────────────────────────────────────┤
│          Platform  (Contract, Sim, RPi5)  ← H3-prep bindings         │
└──────────────────────────────────────────────────────────────────────┘
```

Each kernel subsystem follows the **Operations/Invariant split**: transitions in
`Operations.lean`, proofs in `Invariant.lean`. The unified `apiInvariantBundle`
aggregates all subsystem invariants into a single proof obligation.

## Source layout

```
SeLe4n/Prelude.lean              Typed identifiers, KernelM monad, Hashable instances
SeLe4n/Machine.lean              Register file, memory, timer, MachineConfig
SeLe4n/Model/Object.lean         Re-export hub: TCB, Endpoint, Notification, CNode, VSpaceRoot, CDT
  Object/Types.lean              Core data types through UntypedObject
  Object/Structures.lean         VSpaceRoot, CNode, KernelObject, CDT helpers
SeLe4n/Model/State.lean          SystemState with HashMap-backed stores
SeLe4n/Kernel/Scheduler/*        Priority-bucketed RunQueue, EDF scheduling, domain partitioning
  Operations/Selection.lean      EDF predicates, thread selection, candidate ordering
  Operations/Core.lean           Core transitions (schedule, handleYield, timerTick)
  Operations/Preservation.lean   Scheduler invariant preservation theorems
SeLe4n/Kernel/Capability/*       CSpace lookup/mint/copy/move/delete/revoke with CDT tracking
  Invariant/Defs.lean            Core invariant definitions, transfer theorems
  Invariant/Authority.lean       Authority reduction, badge routing consistency
  Invariant/Preservation.lean    Operation preservation, lifecycle integration
SeLe4n/Kernel/IPC/*              Dual-queue IPC subsystem
  Operations/Endpoint.lean       Core endpoint/notification ops
  Operations/SchedulerLemmas.lean  Scheduler preservation lemmas
  DualQueue/Core.lean            Intrusive dual-queue ops with O(1) removal
  DualQueue/Transport.lean       Dual-queue transport lemmas
  Invariant/Defs.lean            IPC invariant definitions
  Invariant/EndpointPreservation.lean  Endpoint preservation proofs
  Invariant/CallReplyRecv.lean   Call/ReplyRecv preservation proofs
  Invariant/NotificationPreservation.lean  Notification preservation proofs
  Invariant/Structural.lean      Structural invariants, composition theorems
SeLe4n/Kernel/Lifecycle/*        Object retype with lifecycle metadata preservation
SeLe4n/Kernel/Service/*          Service graph with HashSet-backed DFS cycle detection
  Invariant/Policy.lean          Policy surface, bridge theorems
  Invariant/Acyclicity.lean      Dependency acyclicity proofs
SeLe4n/Kernel/Architecture/*     VSpace HashMap map/unmap/lookup, W^X, TLB model, VSpaceBackend
SeLe4n/Kernel/InformationFlow/*  2D security labels, BIBA lattice, 69 NI theorems
  Enforcement/Wrappers.lean      Policy-gated operation wrappers
  Enforcement/Soundness.lean     Correctness theorems, declassification
  Invariant/Helpers.lean         Shared NI proof infrastructure
  Invariant/Operations.lean      Per-operation NI proofs
  Invariant/Composition.lean     Trace composition, 31-constructor NonInterferenceStep
SeLe4n/Kernel/API.lean           Unified public API and apiInvariantBundle
SeLe4n/Platform/Contract.lean    PlatformBinding typeclass
SeLe4n/Platform/Sim/*            Simulation platform (permissive contracts for testing)
SeLe4n/Platform/RPi5/*           Raspberry Pi 5 platform stubs (BCM2712)
SeLe4n/Testing/*                 Test harness, state builder, fixtures
Main.lean                        Executable entry point
tests/                           Negative-state suite, information-flow suite, trace probe
```

## Architectural innovations beyond seL4

| Feature | seL4 | seLe4n |
|---------|------|--------|
| **IPC mechanism** | Single linked-list endpoint queue | Intrusive dual-queue with `queuePPrev` back-pointers for O(1) mid-queue removal |
| **Information flow** | Binary high/low partition | N-domain two-dimensional labels (confidentiality + integrity lattice) |
| **Service management** | Not in kernel | First-class service orchestration with dependency graph and DFS cycle detection |
| **Capability derivation** | CDT with linked-list children | `childMap` HashMap for O(1) children lookup |
| **Scheduler** | Flat priority queue | Priority-bucketed `RunQueue` with inline `maxPriority` tracking and EDF |
| **VSpace** | Hardware page tables | `HashMap VAddr (PAddr x PagePermissions)` with W^X enforcement |
| **Proof methodology** | Isabelle/HOL, post-hoc | Lean 4 type-checker, proofs co-located with transitions |
| **Platform abstraction** | C-level HAL | `PlatformBinding` typeclass with typed boundary contracts |

## What's next

Current priorities and the full workstream history are maintained in
[`docs/WORKSTREAM_HISTORY.md`](docs/WORKSTREAM_HISTORY.md). Summary:

- **WS-H14..H16** — Type safety hardening, platform hardening, testing expansion (Low priority)
- **WS-F5..F8** — Model fidelity, invariant quality, testing, cleanup (Medium/Low priority)
- **Raspberry Pi 5 hardware binding** — populate RPi5 platform stubs with hardware-validated contracts

Prior audits (v0.8.0-v0.9.32), milestone closeouts, and legacy GitBook chapters
are archived in [`docs/dev_history/`](docs/dev_history/README.md).
