<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/logo_dark.png" />
    <img src="assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.12.6-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  A microkernel written in Lean 4 with machine-checked proofs, inspired by the
  <a href="https://sel4.systems">seL4</a> architecture. First hardware target:
  <strong>Raspberry Pi 5</strong>.
</p>
<p align="center">
  Created thoughtfully with the help of:
  claude :robot: :heart: :robot: codex  
  <strong>TREAT THIS KERNEL ACCORDINGLY</strong>
</p>

---

## What is seLe4n?

seLe4n is a microkernel built from the ground up in Lean 4. Every kernel 
transition is an executable pure function. Every invariantis machine-checked 
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
| **Version** | `0.12.6` |
| **Lean toolchain** | `4.28.0` |
| **Production Lean LoC** | 16,485 across 34 files |
| **Proved theorems** | 400+ (zero sorry/axiom) |
| **Target hardware** | Raspberry Pi 5 (ARM64) |
| **Active findings** | [`KERNEL_PERFORMANCE_AUDIT_v0.12.5.md`](docs/audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md) |
| **Active workstream** | WS-G (kernel performance optimization) — WS-G1 completed |
| **Prior completed** | WS-F (v0.12.2), WS-E (v0.11.6), WS-D (v0.11.0), WS-C (v0.9.32), WS-B (v0.9.0) |

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
| `SeLe4n/Machine.lean` | Register file, memory, timer, `MachineConfig`, `MemoryRegion` |
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

## What's next: v0.12.2 audit remediation (WS-F)

Two independent audits identified the gaps between current proofs and
production-kernel requirements. The immediate priority is resolving these
findings systematically. See the
[WS-F workstream plan](docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) for the
full execution plan.

**Critical priorities:**
1. ~~Integrate `IpcMessage` into IPC operations~~ **(WS-F1 COMPLETED)** — messages now flow through all dual-queue and compound IPC operations with 14 preservation theorems and 7 trace anchors
2. ~~Add Untyped memory model with watermark tracking~~ **(WS-F2 COMPLETED)** — `UntypedObject` with region/watermark, `retypeFromUntyped` operation with allocSize validation, 10+ theorems, 6 negative tests, 8 trace anchors
3. ~~Extend `ObservableState` projection to cover all security-relevant fields~~ **(WS-F3 COMPLETED)** — 3 new fields (activeDomain, irqHandlers, objectIndex), CNode slot filtering via `projectKernelObject`, 15 NI theorems (12 standalone + 3 enforcement-NI bridges), enforcement-NI bridge for `serviceRestartChecked`
4. ~~Close proof gaps for `timerTick`, `cspaceMutate`, notification ops~~ **(WS-F4 COMPLETED)** — `timerTick` scheduler/kernel invariant preservation, `cspaceMutate`/`cspaceRevokeCdt`/`cspaceRevokeCdtStrict` capability invariant preservation, notification signal/wait ipcInvariant + schedulerInvariantBundle + ipcSchedulerContractPredicates preservation; 11 Tier-3 surface anchors

**Path to Raspberry Pi 5:**
The hardware target is Raspberry Pi 5 (ARM64). The `Platform/` directory now
provides the structural foundation for hardware binding: a `PlatformBinding`
typeclass, `MachineConfig`/`MemoryRegion` types, a `VSpaceBackend` abstraction,
and concrete stubs for RPi5 (BCM2712 memory map, GIC-400 IRQ constants, ARM64
runtime contract). Once remaining audit remediation closes, H3 will populate
these stubs with hardware-validated contracts. See
[Path to Real Hardware](docs/gitbook/10-path-to-real-hardware-mobile-first.md).

## Completed workstreams (historical)

| Portfolio | Scope | Status |
|-----------|-------|--------|
| **WS-E** (v0.11.6) | Audit remediation: test/CI, proof quality, kernel hardening, capability/IPC, info-flow, completeness | All 6 workstreams completed |
| **WS-D** (v0.11.0) | Test validity, info-flow enforcement, proof gaps, kernel design | WS-D1..D4 completed; D5/D6 absorbed into WS-E |
| **WS-C** (v0.9.32) | Model structure, documentation, maintainability | WS-C1..C8 completed |
| **WS-B** (v0.9.0) | Comprehensive audit 2026-02 | WS-B1..B11 completed |

Prior audits (v0.8.0–v0.9.32), milestone closeouts, and legacy GitBook chapters
are archived in [`docs/dev_history/`](docs/dev_history/README.md).
