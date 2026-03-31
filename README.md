<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/logo_dark.png" />
    <img src="assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.23.20-blue" alt="Version" />
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

- **O(1) hash-based kernel hot paths** — all object stores, run queues, CNode slots, VSpace mappings, and IPC queues use formally verified `RHTable`/`RHSet`
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
| **Version** | `0.23.20` |
| **Lean toolchain** | `v4.28.0` |
| **Production Lean LoC** | 79,419 across 113 files |
| **Test Lean LoC** | 8,759 across 10 test suites |
| **Proved declarations** | 2,281 theorem/lemma declarations (zero sorry/axiom) |
| **Target hardware** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Latest audit** | [`AUDIT_v0.22.17_WORKSTREAM_PLAN.md`](docs/dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md) — pre-release audit remediation (4 CRIT, 9 HIGH, 9 MED, 2 LOW) |
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
│  SchedContext│             │  Donation  │           │                │
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
SeLe4n/Model/State.lean          SystemState with RHTable-backed stores
SeLe4n/Model/IntermediateState.lean  Builder-phase state with invariant witnesses
SeLe4n/Model/Builder.lean        Builder operations (invariant-preserving state construction)
SeLe4n/Model/FrozenState.lean    FrozenMap, FrozenSet, FrozenSystemState, freeze function
SeLe4n/Model/FreezeProofs.lean   Freeze correctness proofs (lookup equiv, invariant transfer)
SeLe4n/Kernel/Scheduler/*        Priority-bucketed RunQueue, EDF scheduling, domain partitioning
  RunQueue.lean                  RunQueue structure, 13 bridge lemmas
  Operations/Selection.lean      EDF predicates, thread selection, candidate ordering
  Operations/Core.lean           Core transitions (schedule, handleYield, timerTick)
  Operations/Preservation.lean   Scheduler invariant preservation theorems
SeLe4n/Kernel/Capability/*       CSpace lookup/mint/copy/move/delete/revoke with CDT tracking
  Operations.lean                CSpace operations
  Invariant/Defs.lean            Core invariant definitions, transfer theorems
  Invariant/Authority.lean       Authority reduction, badge routing consistency
  Invariant/Preservation.lean    Operation preservation, lifecycle integration
SeLe4n/Kernel/IPC/*              Dual-queue IPC subsystem
  Operations/Endpoint.lean       Core endpoint/notification ops
  Operations/CapTransfer.lean    IPC capability transfer
  Operations/Timeout.lean        Budget-driven IPC timeout unblocking (Z6)
  Operations/Donation.lean       SchedContext donation wrappers + preservation (Z7)
  Operations/SchedulerLemmas.lean  Scheduler preservation lemmas
  DualQueue/Core.lean            Intrusive dual-queue ops with O(1) removal
  DualQueue/Transport.lean       Dual-queue transport lemmas
  DualQueue/WithCaps.lean        DualQueue with capability transfer
  Invariant/Defs.lean            IPC invariant definitions
  Invariant/EndpointPreservation.lean  Endpoint preservation proofs
  Invariant/CallReplyRecv.lean   Call/ReplyRecv preservation proofs
  Invariant/NotificationPreservation.lean  Notification preservation proofs
  Invariant/QueueNoDup.lean      No self-loops, send/receive head disjointness
  Invariant/QueueMembership.lean Queue membership consistency proofs
  Invariant/QueueNextBlocking.lean  queueNext blocking consistency proofs
  Invariant/Structural.lean      Structural invariants, composition theorems
SeLe4n/Kernel/Lifecycle/*        Object retype with lifecycle metadata preservation
SeLe4n/Kernel/Service/*          Service graph with HashSet-backed DFS cycle detection
  Interface.lean                 Service interface definitions
  Operations.lean                Service operations
  Registry.lean                  Service registry
  Registry/Invariant.lean        Registry invariant proofs
  Invariant/Policy.lean          Policy surface, bridge theorems
  Invariant/Acyclicity.lean      Dependency acyclicity proofs
SeLe4n/Kernel/Architecture/*     VSpace, TLB model, register decode, platform adapter
  VSpace.lean                    VSpace HashMap map/unmap/lookup, W^X enforcement
  VSpaceBackend.lean             VSpace backend operations
  VSpaceInvariant.lean           VSpace invariant proofs
  TlbModel.lean                  TLB flush model
  Adapter.lean                   Architecture adapter
  Assumptions.lean               Architecture assumptions
  Invariant.lean                 Architecture invariant re-export hub
  RegisterDecode.lean            Total deterministic decode: raw registers → typed kernel IDs
  SyscallArgDecode.lean          Per-syscall typed argument decode (msgRegs → typed structs)
SeLe4n/Kernel/InformationFlow/*  2D security labels, BIBA lattice, 80 NI theorems
  Policy.lean                    Security labels, flow policies, domain flow validation
  Projection.lean                Low-equivalence projection for NI proofs
  Enforcement/Wrappers.lean      25-entry enforcement boundary, policy-gated wrappers
  Enforcement/Soundness.lean     Correctness theorems, declassification
  Invariant/Helpers.lean         Shared NI proof infrastructure
  Invariant/Operations.lean      Per-operation NI proofs
  Invariant/Composition.lean     Trace composition, 32-constructor NonInterferenceStep
SeLe4n/Kernel/RobinHood/*        Robin Hood hash table verified implementation
  Core.lean                      Types, operations, proofs (N1 complete)
  Set.lean                       RHSet type (hash-set wrapper over RHTable)
  Bridge.lean                    Kernel API bridge: instances, bridge lemmas, filter (N3)
  Invariant.lean                 Re-export hub (N2)
    Invariant/Defs.lean          Invariant definitions (distCorrect, noDupKeys, probeChainDominant)
    Invariant/Preservation.lean  WF, distCorrect, noDupKeys, PCD preservation (all ops)
    Invariant/Lookup.lean        Functional correctness (get after insert/erase), key absence
SeLe4n/Kernel/RadixTree/*        CNode radix tree verified flat array (Q4)
  Core.lean                      Types, operations (O(1) lookup/insert/erase via bit extraction)
  Invariant.lean                 24 correctness proofs (lookup, WF, size, toList, fold)
  Bridge.lean                    RHTable→CNodeRadix conversion, freeze integration
SeLe4n/Kernel/SchedContext/*     Scheduling context: CBS budget, replenishment queue (Z1–Z8)
  Types.lean                     Budget, Period, SchedContext, SchedContextBinding
  Budget.lean                    CBS budget operations: consume, replenish, admission control
  ReplenishQueue.lean            Sorted replenishment queue: insert, popDue, remove
  Operations.lean                SchedContext configure/bind/unbind/yieldTo operations (Z5)
  Invariant.lean                 Re-export hub (Z2)
    Invariant/Defs.lean          Invariant definitions, preservation proofs, bandwidth theorems
    Invariant/Preservation.lean  SchedContext operation preservation theorems (Z5)
SeLe4n/Kernel/FrozenOps/*        Frozen kernel operations (Q7)
  Core.lean                      FrozenKernel monad, lookup/store primitives
  Operations.lean                15 per-subsystem frozen operations
  Commutativity.lean             FrozenMap set/get? roundtrip proofs, frame lemmas
  Invariant.lean                 frozenStoreObject preservation theorems
SeLe4n/Kernel/CrossSubsystem.lean  Cross-subsystem invariants
SeLe4n/Kernel/API.lean           Unified public API and apiInvariantBundle
SeLe4n/Platform/Contract.lean    PlatformBinding typeclass
SeLe4n/Platform/DeviceTree.lean  FDT parsing with bounds-checked helpers
SeLe4n/Platform/Boot.lean        Boot sequence (PlatformConfig → IntermediateState)
SeLe4n/Platform/Sim/*            Simulation platform (permissive contracts for testing)
  RuntimeContract.lean           Permissive + restrictive runtime contracts
  BootContract.lean              Boot + interrupt contracts (all True)
  ProofHooks.lean                AdapterProofHooks for restrictive contract
  Contract.lean                  PlatformBinding instance (re-export hub)
SeLe4n/Platform/RPi5/*           Raspberry Pi 5 platform (BCM2712)
  Board.lean                     BCM2712 addresses, MMIO, MachineConfig
  RuntimeContract.lean           Substantive runtime + restrictive contract
  BootContract.lean              Boot + interrupt contracts (GIC-400)
  MmioAdapter.lean               MMIO adapter for RPi5
  ProofHooks.lean                AdapterProofHooks for restrictive contract
  Contract.lean                  PlatformBinding instance (re-export hub)
SeLe4n/Testing/*                 Test harness, state builder, fixtures
  Helpers.lean                   Shared test helpers (expectError, etc.)
  StateBuilder.lean              Test state construction
  InvariantChecks.lean           Runtime invariant check helpers
  MainTraceHarness.lean          Main trace test harness
  RuntimeContractFixtures.lean   Platform contract test fixtures
Main.lean                        Executable entry point
tests/                           10 test suites (negative-state, info-flow, trace, radix, etc.)
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

- **WS-Z** — Composable Performance Objects (8 phases, Z1–Z8) **COMPLETE** (v0.23.0–v0.23.20). SchedContext type foundation, CBS budget engine with 16 preservation theorems, replenishment queue, scheduler integration, capability-controlled thread binding, timeout endpoints, SchedContext donation for passive servers, API surface with 3 error-exclusivity theorems and 4 frozen operations. Enforcement boundary expanded 22→25 entries. Plan: [`WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md`](docs/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md).
- **WS-Y** — Documentation & Cross-Subsystem Hardening (3 phases, Y1–Y3) **PORTFOLIO COMPLETE** (v0.22.23–v0.22.26).
- **WS-X** — Documentation, Hardening & Low-Severity (5 phases, X1–X5) **PORTFOLIO COMPLETE** (v0.22.18–v0.22.22).
- **WS-W** — Pre-Release Audit Remediation (6 phases, W1–W6, 52 sub-tasks) **PORTFOLIO COMPLETE** (v0.22.11–v0.22.17).
- **WS-V** — Deep Audit Remediation (8 phases, V1–V8) **PORTFOLIO COMPLETE** (v0.22.0–v0.22.10).
- **WS-U** — Comprehensive Audit Remediation (8 phases, U1–U8, 97 sub-tasks) **PORTFOLIO COMPLETE** (v0.21.0–v0.21.7).
- **Raspberry Pi 5 hardware binding** — ARMv8 page table walk, GIC-400 interrupt routing, boot sequence (next major milestone)

All prior portfolios (WS-B through WS-T) are complete. Prior audits (v0.8.0–v0.9.32),
milestone closeouts, and legacy GitBook chapters are archived in
[`docs/dev_history/`](docs/dev_history/README.md).
