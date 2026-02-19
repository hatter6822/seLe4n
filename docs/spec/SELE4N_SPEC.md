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
4. [Active Workstream Portfolio (WS-C)](#4-active-workstream-portfolio-ws-c)
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

- **Current package version:** `0.11.0` (`lakefile.toml`)
- **Active findings baseline:** [`docs/audits/AUDIT_v0.9.32.md`](../audits/AUDIT_v0.9.32.md)
- **Active execution baseline:** [`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md)
- **Current active portfolio:** WS-C1..WS-C8 (all workstreams completed)
- **Current active slice:** comprehensive-audit v0.9.32 WS-C execution (WS-C1 + WS-C2 + WS-C3 + WS-C4 + WS-C5 + WS-C6 + WS-C7 + WS-C8 completed).

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
  Comprehensive Audit 2026-02 execution.

### 3.3 Active Audit Portfolio

- **WS-C portfolio** (v0.9.32 workstream plan): WS-C1 through WS-C8 completed.

---

## 4. Active Workstream Portfolio (WS-C)

### 4.1 Critical/High Correctness and Assurance

- **WS-C1:** IPC handshake correctness (critical; **completed** -- notification badge OR
  accumulation + waiter ipcState transitions validated)
- **WS-C2:** Scheduler semantic fidelity (high; **completed**)
- **WS-C3:** Proof-surface de-tautologization (critical; **completed** -- tautological
  `_deterministic` theorems removed; tracked replacements remain in TPI-001/TPI-002)
- **WS-C4:** Test validity hardening (high; **completed** -- invariant-valid fixtures,
  post-op invariant assertions, and reproducible probe execution)
- **WS-C5:** Information-flow assurance (critical; **completed** -- observer-scoped
  service projection + endpoint-send low-equivalence preservation theorem)

### 4.2 Platform and Sustainability

- **WS-C6:** CI and supply-chain hardening (medium; completed)
- **WS-C7:** Model structure and maintainability (medium; completed)
- **WS-C8:** Documentation and GitBook consolidation (high; **completed**)

Authoritative detail for per-workstream goals, dependencies, and evidence gates:
[`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md).

---

## 5. Execution Phases

- **Phase P0:** WS-C8 baseline reset + active-plan publication (completed)
- **Phase P1:** WS-C4 fixture-repair completion with WS-C3 already closed
  (WS-C1 + WS-C2 + WS-C3 + WS-C4 completed)
- **Phase P2:** WS-C5 assurance expansion (completed)
- **Phase P3:** WS-C7 sustainment hardening (completed)

---

## 6. Acceptance Expectations

### 6.1 Per-Workstream Acceptance Gates

Each WS-C workstream has defined entry/exit criteria in the canonical workstream plan.
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
| Findings baseline | [`docs/audits/AUDIT_v0.9.32.md`](../audits/AUDIT_v0.9.32.md) |
| Execution baseline (WS-C) | [`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md) |
| Tracked theorem obligations | [`docs/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`](../audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md) |

### 8.2 Historical Baselines (Retained for Traceability)

| Artifact | Path |
|---|---|
| Historical findings (v0.9.0) | [`docs/audits/AUDIT_v0.9.0.md`](../audits/AUDIT_v0.9.0.md) |
| Historical execution (WS-B) | [`docs/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md) |
| Historical findings (v0.8.0) | [`docs/audits/AUDIT_v0.8.0.md`](../audits/AUDIT_v0.8.0.md) |

---

## 9. Security and Threat Model

Security assumptions and trust boundaries for active and historical slices are documented
in [`docs/THREAT_MODEL.md`](../THREAT_MODEL.md).

The hardware-boundary contract policy governing test-only fixture separation and
architecture-assumption interfaces is documented in
[`docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md`](../HARDWARE_BOUNDARY_CONTRACT_POLICY.md).
