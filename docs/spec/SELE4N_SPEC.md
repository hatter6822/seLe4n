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

- **Current package version:** `0.11.7` (`lakefile.toml`)
- **Active findings baseline:** [`docs/audits/AUDIT_CODEBASE_v0.11.6.md`](../audits/AUDIT_CODEBASE_v0.11.6.md)
- **Active execution baseline:** [`docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md)
- **Current active portfolio:** WS-E1..WS-E6 (v0.11.6 codebase audit remediation)
- **Prior completed portfolio:** WS-D1..WS-D4 (completed); WS-D5/D6 absorbed into WS-E

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

### 3.3 Completed Audit Portfolio (WS-D)

- **WS-D portfolio** (v0.11.0 workstream plan): WS-D1 through WS-D4 completed. WS-D5/D6 items absorbed into WS-E.

### 3.4 Active Audit Portfolio (WS-E)

- **WS-E portfolio** (v0.11.6 workstream plan): WS-E1, WS-E2 completed; WS-E3 through WS-E6 planned.

---

## 4. Active Workstream Portfolio (WS-E)

The WS-E portfolio addresses 32 findings from the v0.11.6 codebase audit
(4 CRITICAL, 9 HIGH, 11 MEDIUM, 8 LOW), plus carry-forward items from the
WS-D portfolio (WS-D5/D6).

### 4.1 Medium — Test Infrastructure and CI

- **WS-E1:** Test infrastructure and CI hardening (medium; **completed** — M-10, M-11, F-14, L-07, L-08; F-09/F-10/F-15 resolved)

### 4.2 High — Proof Quality and Kernel Hardening

- **WS-E2:** Proof quality and invariant strengthening (high; **completed** — C-01, H-01, H-03)
- **WS-E3:** Kernel semantic hardening (high; **planned** — H-06, H-07, H-08, H-09, M-09, L-06)

### 4.3 Critical — Model Completion

- **WS-E4:** Capability and IPC model completion (critical; **planned** — C-02, C-03, C-04, H-02, M-01, M-02, M-12)

### 4.4 High — Security Assurance

- **WS-E5:** Information-flow maturity (high; **planned** — H-04, H-05, M-07)

### 4.5 Low — Model Completeness and Documentation

- **WS-E6:** Model completeness and documentation (low; **planned** — M-03, M-04, M-05, M-08, F-17, L-01–L-05)

Authoritative detail for per-workstream goals, dependencies, and evidence gates:
[`docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md).

---

## 5. Execution Phases

### 5.1 WS-D Phases (completed)

- **Phase P0:** Baseline transition — publish v0.11.0 planning backbone (completed)
- **Phase P1:** WS-D1 test validity restoration — **completed**
- **Phase P2:** WS-D2 information-flow enforcement and proof — **completed**
- **Phase P3:** WS-D3 proof gap closure + WS-D4 kernel design hardening — **completed**

### 5.2 WS-E Phases (active)

- **Phase P0:** Baseline — close quick fixes, publish WS-E backbone, update docs (**completed**)
- **Phase P1:** WS-E1 (test/CI — **completed**) + WS-E2 (proof quality — **completed**)
- **Phase P2:** WS-E3 (kernel hardening)
- **Phase P3:** WS-E4 (capability/IPC completion)
- **Phase P4:** WS-E5 (information-flow maturity)
- **Phase P5:** WS-E6 (model completeness/docs)

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
| Codebase audit (v0.11.6) | [`docs/audits/AUDIT_CODEBASE_v0.11.6.md`](../audits/AUDIT_CODEBASE_v0.11.6.md) |
| Execution baseline (WS-E) | [`docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md) |

### 8.2 Prior Active Baselines (WS-D, completed)

| Artifact | Path |
|---|---|
| Findings baseline (v0.11.0) | [`docs/audits/AUDIT_v0.11.0.md`](../audits/AUDIT_v0.11.0.md) |
| Execution baseline (WS-D) | [`docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md) |
| Tracked theorem obligations | [`docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`](../audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md) |

### 8.3 Historical Baselines (Retained for Traceability)

Prior audits and workstream plans are archived in [`docs/dev_history/audits/`](../dev_history/audits/) for traceability. See [`docs/dev_history/README.md`](../dev_history/README.md) for a full index.

---

## 9. Security and Threat Model

Security assumptions and trust boundaries for active and historical slices are documented
in [`docs/THREAT_MODEL.md`](../THREAT_MODEL.md).

The hardware-boundary contract policy governing test-only fixture separation and
architecture-assumption interfaces is documented in
[`docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md`](../HARDWARE_BOUNDARY_CONTRACT_POLICY.md).
