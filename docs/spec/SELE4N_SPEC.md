# seLe4n Project Specification

This document is the normative scope, milestone, and acceptance-criteria reference for the
seLe4n project -- a Lean 4 formalization of executable, machine-checked seL4 microkernel
semantics.

For the upstream seL4 microkernel specification that seLe4n formalizes, see
[`docs/spec/SEL4_SPEC.md`](./SEL4_SPEC.md).

---

## Table of Contents

1. [Project Identity](#1-project-identity)
2. [Delivered Milestones](#2-delivered-milestones)
3. [Current Active Slice](#3-current-active-slice)
4. [Acceptance Criteria](#4-acceptance-criteria)
5. [Stable Contracts](#5-stable-contracts)
6. [Audit Baselines](#6-audit-baselines)
7. [Security and Threat Model](#7-security-and-threat-model)
8. [Related Documents](#8-related-documents)

---

## 1. Project Identity

- **Name:** seLe4n
- **Language:** Lean 4
- **Purpose:** Executable, machine-checked model of core seL4 microkernel semantics.
- **Package version:** `0.10.0` (see `lakefile.toml`)
- **Repository layout:** layered model/kernel/testing architecture with tiered CI gates.

---

## 2. Delivered Milestones

Each milestone below has been completed and archived. Historical execution details are
retained in the GitBook archive chapters and audit documents for traceability.

| Milestone | Scope | Status |
|---|---|---|
| **Bootstrap** | Typed identifiers, monad foundations, machine state | Complete |
| **M1** | Scheduler semantics and preservation theorems | Complete |
| **M2** | Capability/CSpace operations and authority invariants | Complete |
| **M3** | IPC seed semantics (endpoint send/receive) | Complete |
| **M3.5** | IPC-scheduler waiting handshake + coherence | Complete |
| **M4-A** | Lifecycle/retype foundations | Complete |
| **M4-B** | Lifecycle-capability composition hardening | Complete |
| **M5** | Service graph + policy surfaces + proof package | Complete |
| **M6** | Architecture-boundary assumptions/adapters/invariant hooks | Complete |
| **M7** | Audit remediation (WS-A1 through WS-A8) | Complete |
| **WS-B portfolio** | Comprehensive Audit 2026-02 execution (WS-B1 through WS-B11) | Complete |

---

## 3. Current Active Slice

- **Current completed slice:** Comprehensive Audit 2026-02 execution (WS-B portfolio; WS-B1 through WS-B11 completed).
- **Current active slice:** comprehensive-audit v0.9.32 WS-C execution (WS-C1 + WS-C2 + WS-C3 completed; WS-C4+ follow-on execution in progress).

### 3.1 WS-C Portfolio

| Workstream | Priority | Status |
|---|---|---|
| **WS-C1** | IPC handshake correctness (critical) | Completed -- notification badge OR accumulation + waiter ipcState transitions validated |
| **WS-C2** | Scheduler semantic fidelity (high) | Completed |
| **WS-C3** | Proof-surface de-tautologization (critical) | Completed -- tautological theorems removed; tracked replacements in TPI-001/TPI-002 |
| **WS-C4** | Test validity hardening (high) | Execution beginning |
| **WS-C5** | Information-flow assurance (critical) | Phase P2 target |
| **WS-C6** | CI and supply-chain hardening (medium) | Phase P3 target |
| **WS-C7** | Model structure and maintainability (medium) | Phase P3 target |
| **WS-C8** | Documentation and GitBook consolidation (high) | In progress |

### 3.2 Sequencing Model

- **Phase P0:** WS-C8 baseline reset + active-plan publication (in progress)
- **Phase P1:** WS-C4 fixture-repair continuation (WS-C1 + WS-C2 + WS-C3 complete)
- **Phase P2:** WS-C5 + remaining WS-C4 assurance expansion
- **Phase P3:** WS-C6 + WS-C7 sustainment hardening

### 3.3 Acceptance Expectations for WS-C Work

Authoritative detail for per-workstream goals, dependencies, and evidence gates:
[`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md).

---

## 4. Acceptance Criteria

A milestone or workstream increment is accepted when:

1. Implementation compiles cleanly (`lake build`).
2. Transition semantics are explicit and deterministic (success/failure branches).
3. Invariant/theorem surface remains coherent and discoverable.
4. Fixture-backed executable evidence is intentionally stable or updated with rationale.
5. Tiered validation gates pass for the claimed scope.
6. Documentation reflects exact current state (not intended future state).
7. Audit/workstream status documents are synchronized.

---

## 5. Stable Contracts

Unless a PR explicitly proposes spec-level change control, contributors must preserve:

1. **Deterministic kernel transition behavior** -- explicit success/failure branches.
2. **Layered invariants** + preservation theorem continuity.
3. **Architecture-boundary** assumption/adapter interfaces from M6.
4. **Fixture-backed executable evidence** (`Main.lean` + trace fixture).
5. **Tiered testing gates** used in CI and local workflows.
6. **Theorem discoverability** through stable naming conventions.

---

## 6. Audit Baselines

| Baseline | Document | Role |
|---|---|---|
| Active findings | [`docs/audits/AUDIT_v0.9.32.md`](../audits/AUDIT_v0.9.32.md) | Current independent audit findings |
| Active execution | [`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md) | WS-C portfolio execution plan |
| Tracked obligations | [`docs/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`](../audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md) | Theorem obligations and closure status |
| Historical (WS-B) | [`docs/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md) | Retained for traceability |
| Historical (M7) | [`docs/audits/AUDIT_v0.9.0.md`](../audits/AUDIT_v0.9.0.md) | Retained for traceability |
| Historical (M7 pre) | [`docs/audits/AUDIT_v0.8.0.md`](../audits/AUDIT_v0.8.0.md) | Retained for traceability |

---

## 7. Security and Threat Model

Security assumptions and trust boundaries for active and historical slices are documented
in [`docs/THREAT_MODEL.md`](../THREAT_MODEL.md).

The information-flow proof roadmap is tracked in
[`docs/INFORMATION_FLOW_ROADMAP.md`](../INFORMATION_FLOW_ROADMAP.md).

---

## 8. Related Documents

| Document | Purpose |
|---|---|
| [`docs/spec/SEL4_SPEC.md`](./SEL4_SPEC.md) | Upstream seL4 microkernel specification reference |
| [`docs/DEVELOPMENT.md`](../DEVELOPMENT.md) | Day-to-day contributor workflow |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](../TESTING_FRAMEWORK_PLAN.md) | Testing tier contract |
| [`docs/CI_POLICY.md`](../CI_POLICY.md) | CI/CD policy and required checks |
| [`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](../DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md) | Cross-document synchronization index |
| [`docs/DOCS_DEDUPLICATION_MAP.md`](../DOCS_DEDUPLICATION_MAP.md) | Canonical vs. mirror ownership rules |
| [`CONTRIBUTING.md`](../../CONTRIBUTING.md) | Contributor onboarding guide |
| [`CHANGELOG.md`](../../CHANGELOG.md) | Version history |
