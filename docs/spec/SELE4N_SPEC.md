# seLe4n Project Specification

This document defines the normative scope, milestone structure, active workstream
portfolio, and acceptance criteria for **seLe4n** — a production-oriented microkernel
written in Lean 4 with machine-checked proofs, improving on seL4 architecture.

For the reference specification of the original seL4 microkernel that seLe4n builds on,
see [`docs/spec/SEL4_SPEC.md`](./SEL4_SPEC.md).

---

## Table of Contents

1. [Project Identity](#1-project-identity)
2. [Current State Snapshot](#2-current-state-snapshot)
3. [Milestone History](#3-milestone-history)
4. [Architectural Improvements over seL4](#4-architectural-improvements-over-sel4)
5. [Active Workstream Portfolio (WS-G)](#5-active-workstream-portfolio-ws-g)
6. [Hardware Target: Raspberry Pi 5](#6-hardware-target-raspberry-pi-5)
7. [Acceptance Expectations](#7-acceptance-expectations)
8. [Non-Negotiable Baseline Contracts](#8-non-negotiable-baseline-contracts)
9. [Audit Baselines](#9-audit-baselines)
10. [Security and Threat Model](#10-security-and-threat-model)

---

## 1. Project Identity

**seLe4n** is a novel microkernel built from the ground up in Lean 4. Every kernel
transition is an executable pure function. Every invariant is machine-checked — zero
`sorry`, zero `axiom` across the entire production proof surface.

The project keeps four concerns in one engineering loop:

1. deterministic transition semantics (executable pure functions),
2. machine-checked invariant preservation (400+ proved theorems),
3. architectural improvements over seL4 where the proof framework enables them,
4. milestone-oriented delivery toward production on **Raspberry Pi 5** (ARM64).

The project began as a formalization of seL4 semantics and is now a production-oriented
kernel that preserves seL4's capability-based security model while introducing novel
improvements in service orchestration, capability management, IPC queuing, information-flow
enforcement, and scheduling.

---

## 2. Current State Snapshot

| Attribute | Value |
|-----------|-------|
| **Package version** | `0.12.9` (`lakefile.toml`) |
| **Lean toolchain** | `4.28.0` |
| **Production LoC** | 16,485 across 34 Lean files |
| **Proved theorems** | 400+ (zero sorry/axiom) |
| **Target hardware** | Raspberry Pi 5 (ARM64) |
| **Active findings** | [`AUDIT_CODEBASE_v0.12.2_v1.md`](../audits/AUDIT_CODEBASE_v0.12.2_v1.md), [`v2`](../audits/AUDIT_CODEBASE_v0.12.2_v2.md), [`KERNEL_PERFORMANCE_AUDIT_v0.12.5.md`](../audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md) |
| **Active portfolio** | WS-G (kernel performance optimization) — WS-G1..G5 completed |
| **Prior completed** | WS-F (v0.12.2), WS-E (v0.11.6), WS-D (v0.11.0), WS-C (v0.9.32), WS-B (v0.9.0) |

---

## 3. Milestone History

seLe4n has been developed through incremental milestone slices, each building on the
semantic and proof foundations of the previous one.

### 3.1 Completed Milestone Slices

| Milestone | Scope | Status |
|-----------|-------|--------|
| **Bootstrap** | Typed identifiers, monad foundations, machine state | Complete |
| **M1** | Scheduler semantics and preservation theorems | Complete |
| **M2** | Capability/CSpace operations + authority invariants | Complete |
| **M3** | IPC seed semantics | Complete |
| **M3.5** | Waiting handshake + scheduler coherence | Complete |
| **M4-A** | Lifecycle/retype foundations | Complete |
| **M4-B** | Lifecycle-capability composition hardening | Complete |
| **M5** | Service-graph and policy-surface completion | Complete |
| **M6** | Architecture-boundary assumptions/adapters/invariant hooks | Complete |
| **M7** | Audit remediation WS-A1..WS-A8 | Complete |

### 3.2 Completed Audit Portfolios

| Portfolio | Scope | Workstreams |
|-----------|-------|-------------|
| **WS-E** (v0.11.6) | Test/CI, proof quality, kernel hardening, capability/IPC, info-flow, completeness | WS-E1..E6 completed |
| **WS-D** (v0.11.0) | Test validity, info-flow enforcement, proof gaps, kernel design | WS-D1..D4 completed; D5/D6 absorbed into WS-E |
| **WS-C** (v0.9.32) | Model structure, documentation, maintainability | WS-C1..C8 completed |
| **WS-B** (v0.9.0) | Comprehensive audit 2026-02 | WS-B1..B11 completed |

### 3.3 Security Hardening (implemented)

- IPC thread-state updates fail with `objectNotFound` for missing/reserved TCBs, preventing ghost queue entries.
- Sentinel ID `0` rejected at IPC boundaries (`lookupTcb`/`storeTcbIpcState`).
- Intrusive dual-queue endpoints with `sendQ`/`receiveQ` and per-thread links for O(1) removal.
- IPC message transfer via `TCB.pendingMessage`: messages (registers, caps, badge) flow through sender→receiver rendezvous with combined state+message helpers (`storeTcbIpcStateAndMessage`).
- Node-stable CDT with bidirectional slot↔node maps and strict revocation error reporting.
- Policy-checked wrappers (`endpointSendChecked`, `cspaceMintChecked`, `serviceRestartChecked`) exercised by default in trace and probe harnesses.
- **WS-G1:** All 13 typed identifiers and the composite `SlotRef` key have `Hashable` instances with `@[inline]` for zero overhead. `Std.Data.HashMap` and `Std.Data.HashSet` imported in `Prelude.lean`, enabling O(1) hash-based data structures for kernel performance optimization (WS-G2..G9).

---

## 4. Architectural Improvements over seL4

seLe4n is not a 1:1 formalization of seL4. It preserves seL4's capability-based
security model while introducing improvements that the Lean 4 proof framework enables:

| Area | seL4 | seLe4n Improvement |
|------|------|-------------------|
| **Service lifecycle** | No kernel-level service concept | Service orchestration layer with dependency graphs, acyclic policy enforcement |
| **CDT representation** | Mutable doubly-linked list | Node-stable CDT with O(1) slot transfer via pointer/backpointer fixup |
| **IPC queuing** | Intrusive linked list | Dual-queue model (`sendQ`/`receiveQ`) with O(1) arbitrary removal |
| **Information flow** | Binary high/low partition | Parameterized N-domain labels with per-endpoint flow policies |
| **Scheduling** | Priority-based round-robin | Priority + EDF scheduling with domain-aware partitioning |
| **Revocation** | Silent error swallowing | Strict variant (`cspaceRevokeCdtStrict`) reporting first failure with context |

These are not abstract research extensions — they are design decisions that will be
carried forward into the production kernel.

---

## 5. Active Workstream Portfolio (WS-G)

The WS-G portfolio addresses kernel performance optimization findings from the
[v0.12.5 performance audit](../audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md).

Authoritative detail:
[`docs/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](../audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md).

### 5.1 Completed — Data Structure Optimization

- **WS-G1:** ~~Typed identifier Hashable instances~~ **COMPLETED** — `Hashable` + `LawfulHashable` for all 13 typed identifiers; `Std.HashMap`/`Std.HashSet` imports; zero-overhead foundation for O(1) lookups (v0.12.6)
- **WS-G2:** ~~Object store & ObjectIndex HashMap~~ **COMPLETED** — `objects : Std.HashMap ObjId KernelObject` replacing closure-chain accumulation; `objectIndexSet : Std.HashSet ObjId` shadow set for O(1) membership; `objectTypes : Std.HashMap ObjId KernelObjectType` lifecycle metadata; 9 bridge lemmas; full proof migration (599 theorems verified); closes F-P01, F-P10, F-P13 (v0.12.7)
- **WS-G3:** ~~ASID Resolution Table~~ **COMPLETED** — `asidTable : Std.HashMap ASID ObjId` in `SystemState`; `resolveAsidRoot` rewritten from O(n) `objectIndex.findSome?` to O(1) HashMap lookup with object-store validation; bidirectional `asidTableConsistent` invariant (soundness + completeness); `vspaceInvariantBundle` extended to 3-conjunct; erase-before-insert maintenance in `storeObject`; 3 bridge lemmas; round-trip theorems simplified; closes F-P06 (v0.12.8)

### 5.2 Completed — Scheduler Optimization

- **WS-G4:** ~~Run queue restructure~~ **COMPLETED** — `RunQueue` structure with `Std.HashMap Priority (List ThreadId)` + `Std.HashSet ThreadId` + `flat_wf` structural invariant; `SchedulerState.runQueue` replaces flat `runnable : List ThreadId`; O(1) `insert`/`remove`/`contains`/`rotateHead`/`rotateToBack`; `chooseBestInBucket` bucket-first scheduling reduces best-candidate selection from O(t) to O(k); `withRunnableQueue`/`runnableHead`/`runnableTail` eliminated; 13 bridge lemmas; 30+ IPC invariant proofs migrated; info-flow projection re-proved; closes F-P02, F-P07, F-P12 (v0.12.9)

### 5.3 Completed — CNode Optimization

- **WS-G5:** ~~CNode slot HashMap~~ **COMPLETED** — `CNode.slots : Std.HashMap Slot Capability` replacing `List (Slot × Capability)`; `lookup`/`insert`/`remove` all O(1) amortized; `slotsUnique` trivially true (HashMap key uniqueness); 2 bridge lemmas (`HashMap_filter_preserves_key`, `HashMap_filter_filter_getElem?`); `projectKernelObject_idempotent` reformulated to slot-level lookup equality; manual `BEq CNode`/`BEq KernelObject` instances; 10 files modified; closes F-P03 (v0.12.10)

### 5.4 Planned — Further Optimization

(No further data-structure workstreams are in active development. WS-G6..G9 remain planned.)

### 5.5 Prior Portfolio: WS-F (completed, v0.12.2)

The WS-F portfolio addressed findings from two independent v0.12.2 codebase audits.
Combined: 6 CRITICAL, 6 HIGH, 12 MEDIUM, 9 LOW findings.

- **WS-F1:** ~~IPC message transfer and dual-queue verification~~ **COMPLETED**
- **WS-F2:** ~~Untyped memory model~~ **COMPLETED**
- **WS-F3:** ~~Information-flow completeness~~ **COMPLETED**
- **WS-F4:** ~~Proof gap closure~~ **COMPLETED**
- **WS-F5–F8:** Medium/Low priority — deferred to future portfolios

---

## 6. Hardware Target: Raspberry Pi 5

The first production hardware target is **Raspberry Pi 5** (ARM64, BCM2712).

### 6.1 Why Raspberry Pi 5

1. Practical ARM64 platform for repeated experiments and bring-up
2. Realistic interrupt/memory/boot profile for architecture-bound modeling
3. Broad tooling availability and community support
4. Good tradeoff between accessibility and systems realism

### 6.2 Path to Hardware

| Stage | Description | Status |
|-------|-------------|--------|
| **H0** | Architecture-neutral semantics and proofs | Complete (M1–M7, WS-B..E) |
| **H1** | Architecture-boundary interfaces and adapters | Complete (M6) |
| **H2** | Audit-driven proof deepening (close critical gaps) | Active (WS-F) |
| **H3** | Platform binding — map interfaces to Raspberry Pi 5 hardware | **H3-prep complete** |
| **H4** | Evidence convergence — connect proofs to platform assumptions | Planned |

**H3 preparation (structural):** The `Platform/` directory now provides the
organizational foundation for hardware binding:

- `PlatformBinding` typeclass (`SeLe4n/Platform/Contract.lean`)
- `MachineConfig` and `MemoryRegion` types (`SeLe4n/Machine.lean`)
- `VSpaceBackend` abstraction with `listVSpaceBackend` instance
- `ExtendedBootBoundaryContract` with platform boot fields
- Simulation platform (`Platform/Sim/`) for testing
- RPi5 stubs (`Platform/RPi5/`) with BCM2712 memory map, GIC-400 constants,
  ARM64 machine config, and platform-specific runtime contract

The critical prerequisite for full H3 execution is closing the remaining WS-F
proof gaps. Untyped memory (WS-F2) and information-flow completeness (WS-F3)
are now complete.

---

## 7. Acceptance Expectations

### 7.1 Per-Workstream Acceptance Gates

Each workstream has defined entry/exit criteria. Common acceptance patterns:

1. implementation compiles and passes tiered validation,
2. new/modified theorems are non-tautological and non-trivial,
3. executable trace evidence captures semantic breadcrumbs,
4. documentation is synchronized across all canonical surfaces,
5. no regressions in previously-completed workstream contracts.

### 7.2 Milestone-Moving PR Requirements

Every milestone-moving PR should include:

1. workstream ID(s) advanced,
2. objective and exit-criterion delta,
3. command evidence,
4. synchronized docs updates (README/spec/development/GitBook as needed),
5. explicit deferrals (if any) and destination workstream.

---

## 8. Non-Negotiable Baseline Contracts

Unless a PR explicitly proposes spec-level change control, preserve:

1. deterministic transition semantics (explicit success/failure branches),
2. M3.5 IPC-scheduler handshake coherence semantics and trace anchors,
3. domain-aware scheduling semantics (`schedule` is active-domain-only; no cross-domain fallback),
4. local + composed invariant layering (including `currentThreadInActiveDomain` in the canonical scheduler bundle),
5. theorem discoverability through stable naming,
   - canonical IPC/lifecycle composition surfaces: `coreIpcInvariantBundle`, `ipcSchedulerCouplingInvariantBundle`, `lifecycleCompositionInvariantBundle`,
   - canonical trace helper surfaces: `runCapabilityIpcTrace`, `runSchedulerTimingDomainTrace`,
6. fixture-backed executable evidence (`Main.lean` + trace fixture),
7. tiered validation command behavior (`test_fast`/`smoke`/`full`/`nightly`),
8. top-level import hygiene: `SeLe4n/Kernel/API.lean` is the canonical aggregate API surface.

---

## 9. Audit Baselines

### 9.1 Active Baselines

| Artifact | Path |
|----------|------|
| Codebase audit v1 (v0.12.2) | [`docs/audits/AUDIT_CODEBASE_v0.12.2_v1.md`](../audits/AUDIT_CODEBASE_v0.12.2_v1.md) |
| Codebase audit v2 (v0.12.2) | [`docs/audits/AUDIT_CODEBASE_v0.12.2_v2.md`](../audits/AUDIT_CODEBASE_v0.12.2_v2.md) |
| Execution baseline (WS-F) | [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) |

### 9.2 Prior Baselines (completed)

| Artifact | Path |
|----------|------|
| Findings baseline (v0.11.6) | [`docs/dev_history/audits/AUDIT_CODEBASE_v0.11.6.md`](../dev_history/audits/AUDIT_CODEBASE_v0.11.6.md) |
| Execution baseline (WS-E) | [`docs/dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md) |
| Findings baseline (v0.11.0) | [`docs/dev_history/audits/AUDIT_v0.11.0.md`](../dev_history/audits/AUDIT_v0.11.0.md) |
| Execution baseline (WS-D) | [`docs/dev_history/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md) |

### 9.3 Historical Baselines

Prior audits and workstream plans are archived in [`docs/dev_history/audits/`](../dev_history/audits/).

---

## 10. Security and Threat Model

Security assumptions and trust boundaries are documented in
[`docs/THREAT_MODEL.md`](../THREAT_MODEL.md).

The hardware-boundary contract policy governing test-only fixture separation and
architecture-assumption interfaces is documented in
[`docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md`](../HARDWARE_BOUNDARY_CONTRACT_POLICY.md).
