<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/logo_dark.png" />
    <img src="assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.13.6-blue" alt="Version" />
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
compiles to native code via 84 build jobs with no admitted proofs.

The project began as a formalization of seL4 semantics and has evolved into a
novel kernel that preserves seL4's capability-based security model while
introducing substantial architectural improvements:

- **O(1) hash-based kernel hot paths** — all object stores, run queues, CNode slots, VSpace mappings, and IPC queues use `Std.HashMap`/`Std.HashSet` 
- **Service orchestration layer** for component lifecycle and dependency management with deterministic partial-failure semantics
- **Node-stable capability derivation tree** with `childMap` HashMap index for O(1) slot transfer, revocation, and descendant lookup
- **Intrusive dual-queue IPC** with per-thread `queuePrev`/`queuePPrev`/`queueNext` links for O(1) enqueue, dequeue, and mid-queue removal
- **Parameterized N-domain information-flow** framework with two-dimensional confidentiality/integrity labels (beyond seL4's binary partition)
- **EDF + priority scheduling** with priority-bucketed `RunQueue`, domain-aware partitioning, inline `maxPriority` tracking, and bidirectional membership/list consistency (`flat_wf`, `flat_wf_rev`, `mem_toList_iff_mem`)

## Current state

| Attribute | Value |
|-----------|-------|
| **Version** | `0.13.6` |
| **Lean toolchain** | `4.28.0` |
| **Production Lean LoC** | 29,351 across 40 files |
| **Test Lean LoC** | 2,063 across 3 test suites |
| **Proved declarations** | 866 theorem/lemma declarations (zero sorry/axiom) |
| **Build jobs** | 84 |
| **Target hardware** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Active findings** | [`AUDIT_CODEBASE_v0.12.2_v1.md`](docs/audits/AUDIT_CODEBASE_v0.12.2_v1.md), [`v2`](docs/audits/AUDIT_CODEBASE_v0.12.2_v2.md) |
| **Active audit** | [`KERNEL_PERFORMANCE_AUDIT_v0.12.5.md`](docs/audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md) — all 14 findings resolved |
| **Latest audit** | [`AUDIT_CODEBASE_v0.13.6.md`](docs/audits/AUDIT_CODEBASE_v0.13.6.md) — comprehensive end-to-end audit, zero critical issues |
| **Completed** | End-to-end audit (v0.13.6), WS-H10 (v0.13.6), WS-H7/H8/H9 gaps closed (v0.13.5), WS-H9 (v0.13.4), WS-H8 (v0.13.2), WS-H6 (v0.13.1), WS-H5 (v0.12.19), WS-H4 (v0.12.18), WS-H3 (v0.12.17), WS-H2 (v0.12.16), WS-H1 (v0.12.16), WS-G (v0.12.15), WS-F1..F4 (v0.12.2), WS-E (v0.11.6), WS-D (v0.11.0), WS-C (v0.9.32), WS-B (v0.9.0) |
| **Metrics source of truth** | `./scripts/report_current_state.py` (use before updating docs/gitbook) |

All quantitative attributes above are generated from the codebase using
`./scripts/report_current_state.py` and should be updated in README +
`docs/spec/SELE4N_SPEC.md` + GitBook in the same PR.

## Quick start

```bash
./scripts/setup_lean_env.sh   # install Lean toolchain
lake build                     # compile all 40 modules (84 jobs)
lake exe sele4n                # run trace harness
./scripts/test_smoke.sh        # validate (hygiene + build + trace + negative-state + docs sync)
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
./scripts/test_smoke.sh     # + Tier 2 (trace + negative-state + docs sync)
./scripts/test_full.sh      # + Tier 3 (invariant surface anchors)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4 (nightly determinism)
```

Run at least `test_smoke.sh` before any PR. Run `test_full.sh` when changing
theorems, invariants, or documentation anchors.

## Website codebase map feed

Generate the canonical machine-readable codebase map with:

```bash
./scripts/generate_codebase_map.py --pretty
```

Validate that the committed file is in sync without writing:

```bash
./scripts/generate_codebase_map.py --pretty --check
```

`docs/codebase_map.json` carries both: a deterministic `source_sync.source_digest`
(sha256 over Lean source paths + contents) and volatile `repository.head` git
metadata for observability. Each declaration entry now also includes an additive
`called` array that enumerates in-module declaration references for that
declaration (empty when none are detected). `--check` compares only the stable
declaration-surface subset, so it is branch/merge-robust and fails only when Lean
inputs drift.
The post-merge `.github/workflows/codebase_map_sync.yml` job remains as a
backstop for drift.

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

| Module | Purpose |
|--------|---------|
| `SeLe4n/Prelude.lean` | Typed identifiers (`ThreadId`, `ObjId`, `CPtr`, etc.), `KernelM` monad, `Hashable`/`BEq` instances for all 13 typed IDs |
| `SeLe4n/Machine.lean` | Register file, memory, timer, `MachineConfig` (with `isPowerOfTwo` page-size validation), `MemoryRegion` |
| `SeLe4n/Model/Object.lean` | `TCB` (with intrusive queue links), `Endpoint`, `Notification`, `CNode`, `VSpaceRoot`, CDT |
| `SeLe4n/Model/State.lean` | `SystemState` with `Std.HashMap`-backed object store, lifecycle metadata, CDT `childMap` index |
| `SeLe4n/Kernel/Scheduler/*` | Priority-bucketed `RunQueue` with `HashMap`+`HashSet`, EDF scheduling, domain partitioning, timer tick |
| `SeLe4n/Kernel/Capability/*` | CSpace lookup/mint/copy/move/delete/revoke with CDT tracking, guard/radix path resolution |
| `SeLe4n/Kernel/IPC/Operations.lean` | Core endpoint send/receive, notification signal/wait (legacy, deprecated in favor of DualQueue) |
| `SeLe4n/Kernel/IPC/DualQueue.lean` | Intrusive dual-queue IPC: send/receive/call/reply with `queuePPrev` back-pointers for O(1) removal |
| `SeLe4n/Kernel/IPC/Invariant.lean` | 95+ IPC invariant preservation theorems (largest proof module, ~6,600 LoC) |
| `SeLe4n/Kernel/Lifecycle/*` | Object retype with lifecycle metadata preservation, watermark-tracked untyped memory |
| `SeLe4n/Kernel/Service/*` | Service graph with `HashSet`-backed DFS cycle detection, dependency tracking, deterministic partial-failure policy |
| `SeLe4n/Kernel/Architecture/*` | VSpace `HashMap VAddr PAddr` map/unmap/lookup, `VSpaceBackend` class, adapter contracts, boundary assumptions |
| `SeLe4n/Kernel/InformationFlow/*` | Two-dimensional security labels (confidentiality/integrity), BIBA lattice alternatives, `DeclassificationPolicy`, 69 NI theorems covering >80% of kernel operations, 31-constructor `NonInterferenceStep` |
| `SeLe4n/Kernel/API.lean` | Unified public API surface and `apiInvariantBundle` alias |
| `SeLe4n/Platform/Contract.lean` | `PlatformBinding` typeclass — `RuntimeBoundaryContract`, `BootBoundaryContract`, `InterruptBoundaryContract` |
| `SeLe4n/Platform/Sim/*` | Simulation platform binding (permissive contracts for testing) |
| `SeLe4n/Platform/RPi5/*` | Raspberry Pi 5 platform binding — BCM2712 address map, GIC-400, ARM Cortex-A76 config |
| `Main.lean` | Executable trace harness |
| `tests/` | Negative-state suite, information-flow suite, trace sequence probe |

## Kernel optimizations and improvements over seL4

### Performance: O(1) hash-based hot paths (WS-G, v0.12.6–v0.12.15)

The WS-G portfolio migrated every kernel hot path from linear data structures
to O(1) hash-based alternatives — eliminating all 14 findings from the
[v0.12.5 performance audit](docs/audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md).
All theorem/invariant declarations were re-verified with zero sorry/axiom after each migration.

| Workstream | Data structure change | Complexity |
|------------|----------------------|------------|
| **WS-G1** | `Hashable`/`BEq` instances for all 13 typed identifiers + `SlotRef` | Foundation for all hash structures |
| **WS-G2** | Object store → `Std.HashMap ObjId KernelObject` | O(n) → O(1) lookup |
| **WS-G3** | ASID table → `Std.HashMap ASID ObjId` | O(n) → O(1) VSpace resolution |
| **WS-G4** | Run queue → priority-bucketed `RunQueue` with `HashMap` + `HashSet` | O(t) → O(1) scheduler ops |
| **WS-G5** | CNode slots → `Std.HashMap Slot Capability` | O(m) → O(1) capability ops |
| **WS-G6** | VSpace mappings → `Std.HashMap VAddr PAddr` | O(m) → O(1) page lookup |
| **WS-G7** | IPC queues → O(1) `ipcState` duplicate check + list prepend | O(n) → O(1) |
| **WS-G8** | Service graph → `HashSet`-backed DFS; CDT → `childMap` HashMap index | O(n^2) → O(n+e) |
| **WS-G9** | Info-flow → `computeObservableSet` with precomputed `HashSet ObjId` | O(n) repeated → O(1) contains |

### Architectural innovations beyond seL4

| Feature | seL4 | seLe4n |
|---------|------|--------|
| **IPC mechanism** | Single linked-list endpoint queue | Intrusive dual-queue with `queuePPrev` back-pointers for O(1) mid-queue removal (Linux-style `**pprev`) |
| **Information flow** | Binary high/low partition | N-domain two-dimensional labels (confidentiality lattice + integrity lattice) with per-entity labeling context |
| **Service management** | Not in kernel | First-class service orchestration with dependency graph, DFS cycle detection, and deterministic partial-failure semantics |
| **Capability derivation** | CDT with linked-list children | `childMap : HashMap CdtNodeId (List CdtNodeId)` for O(1) children lookup; `descendantsOf` in O(n+e) |
| **Scheduler** | Flat priority queue | Priority-bucketed `RunQueue` with inline `maxPriority` tracking, domain-aware EDF partitioning |
| **VSpace** | Hardware page tables | `HashMap VAddr PAddr` with `VSpaceBackend` typeclass for platform-agnostic lookup |
| **Proof methodology** | Isabelle/HOL, post-hoc | Lean 4 type-checker, proofs co-located with transitions (Operations/Invariant split) |
| **Platform abstraction** | C-level HAL | `PlatformBinding` typeclass with `RuntimeBoundaryContract`, `BootBoundaryContract`, `InterruptBoundaryContract` |

See [Kernel Performance Optimization](docs/gitbook/08-kernel-performance-optimization.md)
for the full technical breakdown.

## What's next

### Remaining WS-H workstreams (H11–H16)

WS-H1..H10 are all completed. The remaining workstreams address Phases 4–5 of
the [v0.12.15 audit plan](docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md):

| ID | Focus | Priority |
|----|-------|----------|
| **WS-H11** | VSpace enrichment (multi-level page walk, ASID lifecycle) | Medium |
| **WS-H12** | Scheduler/IPC semantic alignment (MCS contexts, budget tracking) | Medium |
| **WS-H13** | CSpace/service model enrichment (CDT refinement, service health) | Medium |
| **WS-H14** | Type safety hardening (phantom types, API boundary contracts) | Low |
| **WS-H15** | Platform hardening (RPi5 contract population, boot sequence) | Low |
| **WS-H16** | Testing and documentation expansion | Low |

### Remaining WS-F workstreams (F5–F8)

The critical WS-F workstreams (F1–F4) are all completed. The remaining
medium/low-priority workstreams close model fidelity and testing gaps identified
by the [v0.12.2 audits](docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md):

| ID | Focus | Priority |
|----|-------|----------|
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low |
| **WS-F8** | Cleanup (dead code, legacy/dual-queue resolution) | Low |

### Raspberry Pi 5 hardware binding (H3)

After the remaining workstreams, the next major milestone is populating the RPi5
platform stubs with hardware-validated contracts. The `Platform/` directory
already provides:

- **`PlatformBinding` typeclass** with `RuntimeBoundaryContract`, `BootBoundaryContract`, and `InterruptBoundaryContract`
- **RPi5 board definition** — BCM2712 SoC address map, GIC-400 distributor/CPU interface, PL011 UART, 4 GB memory layout
- **`rpi5MachineConfig`** — 64-bit registers, 48-bit VA / 44-bit PA, 4 KiB granule, 16-bit ASID (65,536 address spaces)
- **`VSpaceBackend` abstraction** — platform-agnostic VSpace operations that H3 will bind to ARM page tables

See [Path to Real Hardware](docs/gitbook/10-path-to-real-hardware-mobile-first.md).

## Completed workstreams

| Portfolio | Version | Scope | Workstreams |
|-----------|---------|-------|-------------|
| **End-to-end audit** | v0.13.6 | Comprehensive codebase audit: zero critical issues, zero sorry/axiom, stale documentation metrics fixed (theorem counts, LoC), audit report produced. 866 proved declarations confirmed | Audit |
| **WS-H10** | v0.13.6 | Security model foundations: `ObservableState` with `machineRegs`, BIBA lattice alternatives, `DeclassificationPolicy`, `endpointFlowPolicyWellFormed`, `InformationFlowConfigInvariant`. Closes C-05/A-38, A-34, A-39, M-16 | H10 |
| **WS-H7/H8/H9 gaps** | v0.13.5 | BEq soundness lemmas, `endpointReceiveDualChecked_NI` bridge, 3 IPC NI theorems, 31-constructor `NonInterferenceStep` | H7/H8/H9 gap closure |
| **WS-H9** | v0.13.4 | Non-interference coverage >80%: 27 new NI theorems, 28-constructor `NonInterferenceStep`, `composedNonInterference_trace`. Closes C-02/A-40 (CRITICAL) | H9 |
| **WS-H8** | v0.13.2 | Enforcement-NI bridge: 5 enforcement soundness meta-theorems, 4 new `*Checked` wrappers, `ObservableState` domain timing metadata. Closes A-35/H-07, A-36/A-37/H-11 | H8 |
| **WS-H6** | v0.13.1 | Scheduler proof completion: `timeSlicePositive` fully proven, EDF domain-aware fix, `schedulerInvariantBundleFull` 5-tuple | H6 |
| **WS-H7** | v0.12.21 | HashMap equality + state-store migration: order-independent `BEq`, closure→HashMap migration for 5 state fields | H7 |
| **WS-H5** | v0.12.19 | IPC dual-queue structural invariant: `intrusiveQueueWellFormed`, `dualQueueSystemInvariant`, `tcbQueueLinkIntegrity`; 13 preservation theorems. Closes C-04/A-22, A-23, A-24 | H5 |
| **WS-H4** | v0.12.18 | Capability invariant redesign: `capabilityInvariantBundle` 7-tuple with `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity` | H4 |
| **WS-H3** | v0.12.17 | Build/CI infrastructure fixes: `run_check` return value fix (H-12), docs sync CI integration (M-19), Tier 3 `rg` guard (M-20) | H3 |
| **WS-H2** | v0.12.16 | Lifecycle safety guards: childId collision/self-overwrite guards, TCB scheduler cleanup, CNode CDT detach, atomic retype | H2 |
| **WS-H1** | v0.12.16 | IPC call-path semantic fix: `blockedOnCall` state, reply-target scoping, 5-conjunct `ipcSchedulerContractPredicates` | H1 |
| **WS-G** | v0.12.6–v0.12.15 | Kernel performance: all hot paths migrated to O(1) hash-based structures, 14 audit findings resolved | G1–G9 + refinement |
| **WS-F1..F4** | v0.12.2–v0.12.5 | Critical audit remediation: IPC message transfer (14 theorems), untyped memory (watermark tracking), info-flow completeness (15 NI theorems), proof gap closure | F1–F4 |
| **WS-E** | v0.11.0–v0.11.6 | Test/CI hardening, proof quality, kernel hardening, capability/IPC, info-flow enforcement, completeness | E1–E6 |
| **WS-D** | v0.11.0 | Test validity, info-flow enforcement, proof gaps, kernel design | D1–D4 |
| **WS-C** | v0.9.32 | Model structure, documentation, maintainability | C1–C8 |
| **WS-B** | v0.9.0 | Comprehensive audit (2026-02) | B1–B11 |

Prior audits (v0.8.0–v0.9.32), milestone closeouts, and legacy GitBook chapters
are archived in [`docs/dev_history/`](docs/dev_history/README.md).
