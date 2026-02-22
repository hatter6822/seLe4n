# seLe4n Project Specification

This document defines the normative scope, milestone structure, active workstream
portfolio, and acceptance criteria for the **seLe4n** project -- a Lean 4 formalization
of core seL4 microkernel semantics.

For the reference specification of the original seL4 microkernel that seLe4n models,
see [`docs/spec/SEL4_SPEC.md`](./SEL4_SPEC.md).

---

## Table of Contents

1. [Project Identity](#1-project-identity)
2. [Current State Snapshot](#2-current-state-snapshot)
3. [Milestone History](#3-milestone-history)
4. [Active Workstream Portfolio (WS-D)](#4-active-workstream-portfolio-ws-d)
5. [Execution Phases](#5-execution-phases)
6. [Acceptance Expectations](#6-acceptance-expectations)
7. [Non-Negotiable Baseline Contracts](#7-non-negotiable-baseline-contracts)
8. [Audit Baselines](#8-audit-baselines)
9. [Security and Threat Model](#9-security-and-threat-model)

---

## 1. Project Identity

**seLe4n** is a Lean 4 formalization project for an executable, machine-checked model of
core [seL4 microkernel](https://sel4.systems) semantics. The project keeps three concerns
in one engineering loop:

1. deterministic transition semantics,
2. machine-checked invariant preservation,
3. milestone-oriented delivery with explicit acceptance criteria.

The project reduces a common systems-assurance failure mode: drift between code, proof
claims, and planning artifacts.

---

## 2. Current State Snapshot

- **Current package version:** `0.11.6` (`lakefile.toml`)
- **Active findings baseline:** [`docs/audits/AUDIT_v0.11.0.md`](../audits/AUDIT_v0.11.0.md)
- **Active execution baseline:** [`docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md)
- **Current active portfolio:** WS-D1..WS-D6 (v0.11.0 audit remediation)
- **Prior completed portfolio:** WS-C1..WS-C8 (all completed)

---

## 3. Milestone History

seLe4n has been developed through a series of incremental milestone slices, each building
on the semantic and proof foundations of the previous one.

### 3.1 Completed Milestone Slices

| Milestone | Scope | Status |
|---|---|---|
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

- **WS-B portfolio** (v0.9.0 workstream plan): WS-B1 through WS-B11 completed.
- **WS-C portfolio** (v0.9.32 workstream plan): WS-C1 through WS-C8 completed.

### 3.3 Active Audit Portfolio

- **WS-D portfolio** (v0.11.0 workstream plan): WS-D1 through WS-D4 completed; WS-D5, WS-D6 planned.

---

## 4. Active Workstream Portfolio (WS-D)

### 4.1 Critical/High — Test Validity and Security Assurance

- **WS-D1:** Test error handling and validity (critical/high; **completed** — F-01, F-03, F-04)
- **WS-D2:** Information-flow enforcement and proof (high; **completed** — F-02, F-05)

### 4.2 Medium — Proof Completion and Kernel Hardening

- **WS-D3:** Proof gap closure (medium; **completed** — F-06, F-08, F-16; TPI-001 closed)
- **WS-D4:** Kernel design hardening (medium; **completed** — F-07, F-11, F-12). BFS completeness bridge (`bfs_complete_for_nontrivialPath`, TPI-D07-BRIDGE) retains focused `sorry`; completeness proof roadmap in [`M2_BFS_SOUNDNESS.md §6`](../audits/execution_plans/milestones/M2_BFS_SOUNDNESS.md#6-completeness-proof-roadmap--the-harder-path).
- **WS-D5:** Test infrastructure expansion (medium; **planned** — F-09, F-10)

### 4.3 Low — Infrastructure Polish

- **WS-D6:** CI/CD and documentation polish (low; **planned** — F-13, F-14, F-15, F-17)

Authoritative detail for per-workstream goals, dependencies, and evidence gates:
[`docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md).

---

## 5. Execution Phases

- **Phase P0:** Baseline transition — publish v0.11.0 planning backbone, demote WS-C to historical (completed)
- **Phase P1:** WS-D1 test validity restoration (critical/high) — **completed**
- **Phase P2:** WS-D2 information-flow enforcement and proof expansion (high) — **completed**
- **Phase P3:** WS-D3 proof gap closure (**completed**) + WS-D4 kernel design hardening (**completed**)
- **Phase P4:** WS-D5 test infrastructure expansion + WS-D6 CI/documentation polish (medium/low)

---

## 6. Acceptance Expectations

### 6.1 Per-Workstream Acceptance Gates

Each WS-D workstream has defined entry/exit criteria in the canonical workstream plan.
Common acceptance patterns:

1. implementation compiles and passes tiered validation,
2. new/modified theorems are non-tautological and non-trivial,
3. executable trace evidence captures semantic breadcrumbs,
4. documentation is synchronized across all canonical surfaces,
5. no regressions in previously-completed workstream contracts.

### 6.2 Milestone-Moving PR Requirements

Every milestone-moving PR should include:

1. workstream ID(s) advanced,
2. objective and exit-criterion delta,
3. command evidence,
4. synchronized docs updates (README/spec/development/GitBook as needed),
5. explicit deferrals (if any) and destination workstream.

---

## 7. Non-Negotiable Baseline Contracts

Unless a PR explicitly proposes spec-level change control, preserve:

1. deterministic transition semantics (explicit success/failure branches),
2. M3.5 IPC-scheduler handshake coherence semantics and trace anchors,
3. local + composed invariant layering,
4. theorem discoverability through stable naming,
5. fixture-backed executable evidence (`Main.lean` + trace fixture),
6. tiered validation command behavior (`test_fast`/`smoke`/`full`/`nightly`).

---

## 8. Audit Baselines

### 8.1 Active Baselines

| Artifact | Path |
|---|---|
| Findings baseline | [`docs/audits/AUDIT_v0.11.0.md`](../audits/AUDIT_v0.11.0.md) |
| Execution baseline (WS-D) | [`docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md) |
| Tracked theorem obligations | [`docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`](../audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md) |

### 8.2 Historical Baselines (Retained for Traceability)

Prior audits and workstream plans are archived in [`docs/dev_history/audits/`](../dev_history/audits/) for traceability. See [`docs/dev_history/README.md`](../dev_history/README.md) for a full index.

---

## 9. Security and Threat Model

Security assumptions and trust boundaries for active and historical slices are documented
in [`docs/THREAT_MODEL.md`](../THREAT_MODEL.md).

The hardware-boundary contract policy governing test-only fixture separation and
architecture-assumption interfaces is documented in
[`docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md`](../HARDWARE_BOUNDARY_CONTRACT_POLICY.md).
