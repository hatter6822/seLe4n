<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/logo_dark.png" />
    <img src="assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.20.3-blue" alt="Version" />
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

<p align="center">
  <a href="docs/i18n/zh-CN/README.md">简体中文</a> ·
  <a href="docs/i18n/es/README.md">Español</a> ·
  <a href="docs/i18n/ja/README.md">日本語</a> ·
  <a href="docs/i18n/ko/README.md">한국어</a> ·
  <a href="docs/i18n/ar/README.md">العربية</a> ·
  <a href="docs/i18n/fr/README.md">Français</a> ·
  <a href="docs/i18n/pt-BR/README.md">Português</a> ·
  <a href="docs/i18n/ru/README.md">Русский</a> ·
  <a href="docs/i18n/de/README.md">Deutsch</a> ·
  <a href="docs/i18n/hi/README.md">हिन्दी</a>
</p>

---

## What is seLe4n?

seLe4n is a microkernel built from the ground up in Lean 4. Every kernel
transition is an executable pure function. Every invariant is machine-checked
by the Lean type-checker — zero `sorry`, zero `axiom`. The entire proof surface
compiles to native code with no admitted proofs.

The project utilizes a capability-based security model while introducing novel 
architectural improvements compared to other microkernels:

- **O(1) hash-based kernel hot paths** — all object stores, run queues, CNode slots, VSpace mappings, and IPC queues use formally verified `RHTable`/`RHSet` (Robin Hood hash table with machine-checked invariants, zero `Std.HashMap`/`Std.HashSet` in state)
- **Service orchestration layer** for component lifecycle and dependency management with deterministic partial-failure semantics
- **Node-stable capability derivation tree** with `childMap` + `parentMap` RHTable indices for O(1) slot transfer, revocation, parent lookup, and descendant traversal
- **Intrusive dual-queue IPC** with per-thread `queuePrev`/`queuePPrev`/`queueNext` links for O(1) enqueue, dequeue, and mid-queue removal
- **Parameterized N-domain information-flow** framework with configurable flow policies, generalizing legacy confidentiality/integrity labels (beyond seL4's binary partition)
- **EDF + priority scheduling** with dequeue-on-dispatch semantics, per-TCB register context with inline context switch, priority-bucketed `RunQueue`, domain-aware partitioning

## Current state

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| Attribute | Value |
|-----------|-------|
| **Version** | `0.20.3` |
| **Lean toolchain** | `v4.28.0` |
| **Production Lean LoC** | 60,116 across 100 files |
| **Test Lean LoC** | 7,561 across 10 test suites |
| **Proved declarations** | 1,812 theorem/lemma declarations (zero sorry/axiom) |
| **Target hardware** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Latest audit** | [`AUDIT_COMPREHENSIVE_v0.19.6_DEEP_DIVE.md`](docs/audits/AUDIT_COMPREHENSIVE_v0.19.6_DEEP_DIVE.md) and [`AUDIT_COMPREHENSIVE_v0.19.6_FULL_KERNEL_RUST.md`](docs/audits/AUDIT_COMPREHENSIVE_v0.19.6_FULL_KERNEL_RUST.md) — dual deep-dive audits (4 HIGH, 52 MEDIUM, 56 LOW, 0 Critical) |
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
./scripts/test_fast.sh      # Tier 0 + Tier 1 (hygiene + build, semantic proof-depth L-08)
./scripts/test_smoke.sh     # + Tier 2 (trace + negative-state + docs sync)
./scripts/test_full.sh      # + Tier 3 (invariant surface anchors + Lean #check correctness)
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
  Invariant/Composition.lean     Trace composition, 33-constructor NonInterferenceStep
SeLe4n/Kernel/RobinHood/*       Robin Hood hash table verified implementation
  Core.lean                      Types, operations, proofs (N1 complete)
  Bridge.lean                    Kernel API bridge: instances, bridge lemmas, filter (N3 complete)
  Invariant.lean                 Re-export hub (N2)
    Invariant/Defs.lean          Invariant definitions (distCorrect, noDupKeys, probeChainDominant)
    Invariant/Preservation.lean  WF, distCorrect, noDupKeys, PCD preservation (all ops)
    Invariant/Lookup.lean        Functional correctness (get after insert/erase), key absence
SeLe4n/Kernel/RadixTree/*        CNode radix tree verified flat array (Q4)
  Core.lean                      Types, operations (O(1) lookup/insert/erase via bit extraction)
  Invariant.lean                 24 correctness proofs (lookup, WF, size, toList, fold)
  Bridge.lean                    RHTable→CNodeRadix conversion, freeze integration
SeLe4n/Kernel/API.lean           Unified public API and apiInvariantBundle
SeLe4n/Platform/Contract.lean    PlatformBinding typeclass
SeLe4n/Platform/Sim/*            Simulation platform (permissive contracts for testing)
SeLe4n/Platform/RPi5/*           Raspberry Pi 5 platform stubs (BCM2712)
SeLe4n/Testing/*                 Test harness, state builder, fixtures
Main.lean                        Executable entry point
tests/                           Negative-state, information-flow, trace probe, radix tree suites
```

### Comparison with seL4

| Feature | seL4 | seLe4n |
|---------|------|--------|
| **IPC mechanism** | Single linked-list endpoint queue | Intrusive dual-queue with `queuePPrev` back-pointers for O(1) mid-queue removal |
| **Information flow** | Binary high/low partition | N-domain configurable flow policy (generalizes legacy confidentiality × integrity labels) |
| **Service management** | Not in kernel | First-class service orchestration with dependency graph and DFS cycle detection |
| **Capability derivation** | CDT with linked-list children | `childMap` HashMap for O(1) children lookup |
| **Scheduler** | Flat priority queue | Priority-bucketed `RunQueue` with inline `maxPriority` tracking and EDF |
| **VSpace** | Hardware page tables | `HashMap VAddr (PAddr x PagePermissions)` with W^X enforcement |
| **Proof methodology** | Isabelle/HOL, post-hoc | Lean 4 type-checker, proofs co-located with transitions |
| **Platform abstraction** | C-level HAL | `PlatformBinding` typeclass with typed boundary contracts |

### Comparison with Fiasco.OC (TU Dresden)

| Feature | Fiasco.OC (TU Dresden) | seLe4n |
|---------|-------------------------|--------|
| **IPC mechanism** | L4 message-based endpoint IPC | Intrusive dual-queue endpoint IPC with `queuePPrev` back-pointers for O(1) mid-queue removal |
| **Information flow** | Mechanism/policy isolation (no in-tree machine-checked noninterference layer) | N-domain configurable flow policy with machine-checked low-equivalence/noninterference theorems |
| **Service management** | Not in kernel (external user-space stacks such as L4Re) | First-class service orchestration with dependency graph and DFS cycle detection |
| **Capability derivation** | L4 capability/object model | `childMap` HashMap for O(1) children lookup with typed transitions |
| **Scheduler** | Priority-driven real-time scheduler | Priority-bucketed `RunQueue` with inline `maxPriority` tracking and EDF |
| **VSpace** | Architecture-native page tables/MMU | `HashMap VAddr (PAddr x PagePermissions)` with W^X enforcement |
| **Proof methodology** | Assurance via testing/review/benchmarking | Lean 4 type-checker with proofs co-located with transitions |
| **Platform abstraction** | Architecture/board support via kernel + ecosystem engineering | `PlatformBinding` typeclass with typed boundary contracts |


## What's next

Current priorities and the full workstream history are maintained in
[`docs/WORKSTREAM_HISTORY.md`](docs/WORKSTREAM_HISTORY.md). Summary:

- **WS-T** — Deep-Dive Audit Remediation (8 phases, T1–T8, 94 sub-tasks) **T1–T4 COMPLETE** (v0.20.0–v0.20.3). Phase T4 closes IPC & capability proof chains: `ipcStateQueueConsistent` preservation, `dualQueueSystemInvariant` with acyclicity, WithCaps invariant composition, CDT BFS infrastructure, RadixTree bridge equivalence, run queue maxPriority consistency. Plan: [`AUDIT_v0.19.6_WORKSTREAM_PLAN.md`](docs/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md).
- **WS-S** — Pre-Benchmark Strengthening (7 phases, S1–S7, 83 sub-tasks) **COMPLETE** (v0.19.0–v0.19.6). Plan: [`AUDIT_v0.18.7_WORKSTREAM_PLAN.md`](docs/dev_history/audits/AUDIT_v0.18.7_WORKSTREAM_PLAN.md). Closure: [`WS_S_CLOSURE_REPORT.md`](docs/dev_history/audits/WS_S_CLOSURE_REPORT.md).
- **WS-R** — Comprehensive Audit Remediation (8 phases, R1–R8, 111 sub-tasks) **COMPLETE** (v0.18.0–v0.18.7). Plan: [`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md).
- **Raspberry Pi 5 hardware binding** — ARMv8 page table walk, GIC-400 interrupt routing, boot sequence (next workstream after WS-T)

Prior portfolios (WS-B through WS-R) are all complete. Prior audits (v0.8.0–v0.9.32),
milestone closeouts, and legacy GitBook chapters are archived in
[`docs/dev_history/`](docs/dev_history/README.md).
