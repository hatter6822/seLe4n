<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/logo_dark.png" />
    <img src="assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.12.15-blue" alt="Version" />
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
by the Lean type-checker — zero `sorry`, zero `axiom`.

The project began as a formalization of seL4 semantics and is evolving into a
novel kernel that preserves seL4's capability-based security model while
improving on specific architectural aspects:

- **Service orchestration layer** for component lifecycle and dependency management
- **Node-stable capability derivation tree** with O(1) slot transfer and revocation
- **Intrusive dual-queue IPC** with per-thread queue links for O(1) removal
- **Parameterized N-domain information-flow** framework (beyond seL4's binary partition)
- **EDF + priority scheduling** with domain-aware partitioning

## Current state

| Attribute | Value |
|-----------|-------|
| **Version** | `0.12.15` |
| **Lean toolchain** | `4.28.0` |
| **Production Lean LoC** | 16,485 across 34 files |
| **Proved theorems** | 400+ (zero sorry/axiom) |
| **Target hardware** | Raspberry Pi 5 (ARM64) |
| **Active findings** | [`AUDIT_CODEBASE_v0.12.2_v1.md`](docs/audits/AUDIT_CODEBASE_v0.12.2_v1.md), [`v2`](docs/audits/AUDIT_CODEBASE_v0.12.2_v2.md) |
| **Next workstream** | WS-F5..F8 (remaining v0.12.2 audit remediation — model fidelity, invariant quality, testing, cleanup) |
| **Completed** | WS-G (v0.12.15), WS-F1..F4 (v0.12.2), WS-E (v0.11.6), WS-D (v0.11.0), WS-C (v0.9.32), WS-B (v0.9.0) |

## Quick start

```bash
./scripts/setup_lean_env.sh   # install Lean toolchain
lake build                     # compile all 34 modules (64 jobs)
lake exe sele4n                # run trace harness
./scripts/test_smoke.sh        # validate (hygiene + build + trace + negative-state)
```

## Project documentation

| Document | Purpose |
|----------|---------|
| [`docs/spec/SELE4N_SPEC.md`](docs/spec/SELE4N_SPEC.md) | Project specification, milestones, and active workstreams |
| [`docs/spec/SEL4_SPEC.md`](docs/spec/SEL4_SPEC.md) | seL4 reference semantics that seLe4n builds on |
| [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md) | Day-to-day workflow, validation loop, PR checklist |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](docs/TESTING_FRAMEWORK_PLAN.md) | Tiered test gates and CI contract |
| [`docs/gitbook/README.md`](docs/gitbook/README.md) | Full handbook (architecture, design, proofs, hardware path) |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | Contribution mechanics and PR requirements |
| [`CHANGELOG.md`](CHANGELOG.md) | Version history |

## Validation commands

```bash
./scripts/test_fast.sh      # Tier 0 + Tier 1 (hygiene + build)
./scripts/test_smoke.sh     # + Tier 2 (trace + negative-state checks)
./scripts/test_full.sh      # + Tier 3 (invariant surface anchors)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4 (nightly determinism)
```

Run at least `test_smoke.sh` before any PR. Run `test_full.sh` when changing
theorems, invariants, or documentation anchors.

## Architecture

seLe4n is organized as layered contracts, each with executable transitions and
machine-checked invariant preservation proofs:

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│   Scheduler  │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│              │             │            │           │                │
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
`Operations.lean`, proofs in `Invariant.lean`.

| Module | Purpose |
|--------|---------|
| `SeLe4n/Prelude.lean` | Typed identifiers (`ThreadId`, `ObjId`, `CPtr`, etc.) + `KernelM` monad |
| `SeLe4n/Machine.lean` | Register file, memory, timer, `MachineConfig` (with `isPowerOfTwo` page-size validation), `MemoryRegion` |
| `SeLe4n/Model/Object.lean` | `TCB`, `Endpoint`, `Notification`, `CNode`, `VSpaceRoot`, CDT |
| `SeLe4n/Model/State.lean` | `SystemState` with functional maps, lifecycle metadata, CDT slot↔node |
| `SeLe4n/Kernel/Scheduler/*` | Priority + EDF scheduling, domain partitioning, timer tick |
| `SeLe4n/Kernel/Capability/*` | CSpace lookup/mint/copy/move/delete/revoke with CDT tracking |
| `SeLe4n/Kernel/IPC/Operations.lean` | Core endpoint send/receive, notification signal/wait |
| `SeLe4n/Kernel/IPC/DualQueue.lean` | Intrusive dual-queue IPC: send/receive/call/reply with queue links |
| `SeLe4n/Kernel/IPC/Invariant.lean` | IPC invariant preservation proofs |
| `SeLe4n/Kernel/Lifecycle/*` | Object retype with lifecycle metadata preservation |
| `SeLe4n/Kernel/Service/*` | Service graph, dependency tracking, policy enforcement *(extension)* |
| `SeLe4n/Kernel/Architecture/*` | VSpace map/unmap/lookup, `VSpaceBackend` class, adapter contracts, boundary assumptions |
| `SeLe4n/Kernel/InformationFlow/*` | N-domain labels, state projection, non-interference, enforcement |
| `SeLe4n/Kernel/API.lean` | Unified public API surface and invariant bundle aliases |
| `SeLe4n/Platform/Contract.lean` | `PlatformBinding` typeclass — formal interface for hardware targets |
| `SeLe4n/Platform/Sim/*` | Simulation platform binding (permissive contracts for testing) |
| `SeLe4n/Platform/RPi5/*` | Raspberry Pi 5 platform binding (BCM2712/ARM64 H3-prep stubs) |
| `Main.lean` | Executable trace harness |
| `tests/` | Negative-state suite, information-flow suite, trace sequence probe |

## Recently completed: WS-G kernel performance optimization

The WS-G portfolio (v0.12.6–v0.12.15) migrated every kernel hot path from
linear data structures to O(1) hash-based alternatives — eliminating all 14
performance findings from the [v0.12.5 performance audit](docs/audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md).
All invariant proofs were re-verified with zero sorry/axiom.

| Workstream | Optimization | Complexity change |
|------------|-------------|-------------------|
| **WS-G1** | Hashable infrastructure for all typed identifiers | Foundation for O(1) lookups |
| **WS-G2** | Object store `Std.HashMap ObjId KernelObject` | O(n) closure-chain → O(1) |
| **WS-G3** | ASID resolution `Std.HashMap ASID ObjId` | O(n) linear scan → O(1) |
| **WS-G4** | Priority-bucketed `RunQueue` with HashMap + HashSet | O(t) insert/remove → O(1) |
| **WS-G5** | CNode `Std.HashMap Slot Capability` | O(m) list scan → O(1) |
| **WS-G6** | VSpace `Std.HashMap VAddr PAddr` | O(m) list scan → O(1) |
| **WS-G7** | IPC queue + notification O(1) duplicate check | O(n) append/scan → O(1) |
| **WS-G8** | Service DFS + CDT `childMap` HashMap index | O(n^2) BFS → O(n+e) DFS |
| **WS-G9** | Info-flow `computeObservableSet` with HashSet | O(n) per-object re-eval → O(1) |

See [Kernel Performance Optimization](docs/gitbook/08-kernel-performance-optimization.md)
for the full technical breakdown.

## What's next: remaining WS-F workstreams (F5–F8)

The critical WS-F workstreams (F1–F4) are all completed. The remaining
medium/low-priority workstreams close model fidelity and testing gaps identified
by the [v0.12.2 audits](docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md):

| ID | Focus | Priority |
|----|-------|----------|
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low |
| **WS-F8** | Cleanup (dead code, legacy/dual-queue resolution) | Low |

**After WS-F: Raspberry Pi 5 binding (H3).** The `Platform/` directory provides
the structural foundation — `PlatformBinding` typeclass, `MachineConfig`/
`MemoryRegion` types, `VSpaceBackend` abstraction, and RPi5 stubs (BCM2712,
GIC-400, ARM64 config). H3 will populate these with hardware-validated contracts.
See [Path to Real Hardware](docs/gitbook/10-path-to-real-hardware-mobile-first.md).

## Completed workstreams

| Portfolio | Scope | Status |
|-----------|-------|--------|
| **WS-G** (v0.12.15) | Kernel performance: 9 workstreams migrating all hot paths to O(1) hash-based structures | All 9 completed + refinement pass |
| **WS-F1..F4** (v0.12.2) | Critical audit remediation: IPC message transfer, untyped memory, info-flow completeness, proof gaps | All 4 critical workstreams completed |
| **WS-E** (v0.11.6) | Test/CI, proof quality, kernel hardening, capability/IPC, info-flow, completeness | All 6 completed |
| **WS-D** (v0.11.0) | Test validity, info-flow enforcement, proof gaps, kernel design | WS-D1..D4 completed |
| **WS-C** (v0.9.32) | Model structure, documentation, maintainability | WS-C1..C8 completed |
| **WS-B** (v0.9.0) | Comprehensive audit 2026-02 | WS-B1..B11 completed |

Prior audits (v0.8.0–v0.9.32), milestone closeouts, and legacy GitBook chapters
are archived in [`docs/dev_history/`](docs/dev_history/README.md).
