# seLe4n Specification and Milestone Plan

## 1) Purpose

This document is the **normative scope and acceptance source** for milestone state,
active-slice intent, and change-control expectations.

Companion planning and execution documents:

- comprehensive-audit findings:
  [`docs/audits/COMPREHENSIVE_AUDIT_2026_02.md`](./audits/COMPREHENSIVE_AUDIT_2026_02.md)
- comprehensive-audit workstream execution plan:
  [`docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md`](./audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md)

---

## 2) Milestone status map (current)

- **M4-A:** complete (lifecycle/retype foundations)
- **M4-B:** complete (lifecycle-capability composition hardening)
- M4-B (complete) baseline is retained for historical compatibility checks
- **M5:** complete (service graph + policy surfaces + proof package)
- **M6:** complete (architecture-boundary assumptions/adapters/invariant hooks)
- **M7:** complete (audit remediation WS-A1..WS-A8)
- **Current active slice:** post-M7 comprehensive-audit execution portfolio (WS-B4..WS-B11 pending/in progress; WS-B1, WS-B2, and WS-B3 complete).

---

## 3) Stable baseline contracts (must not regress)

1. deterministic transition semantics across scheduler/capability/IPC/lifecycle/service surfaces,
2. M3.5 IPC-scheduler handshake behavior and associated invariant/trace anchors,
3. layered invariants with local and composed preservation theorem entry points,
4. architecture-boundary assumptions and adapter error mapping introduced in M6,
5. fixture-backed executable evidence for key success/failure traces,
6. tiered testing quality gates used by local and CI workflows.

Any intentional deviation requires explicit spec-level change note in the PR.

---

## 4) Active slice specification: comprehensive-audit WS-B portfolio

### 4.1 Slice objective

Close comprehensive-audit recommendations while preserving determinism,
proof hygiene, contributor usability, and hardware-readiness trajectory.

### 4.2 Workstream inventory

- **WS-B1:** VSpace + memory model foundation ✅ completed
- **WS-B2:** Generative + negative testing expansion ✅ completed
- **WS-B3:** Main trace harness refactor ✅ completed
- **WS-B4:** Remaining type-wrapper migration
- **WS-B5:** CSpace semantics completion (guard/radix)
- **WS-B6:** Notification-object IPC completion
- **WS-B7:** Information-flow proof-track start
- **WS-B8:** Documentation automation + consolidation
- **WS-B9:** Threat model and security hardening
- **WS-B10:** CI maturity upgrades
- **WS-B11:** Scenario framework finalization

### 4.3 Sequencing constraints

- **P1:** WS-B4 + WS-B3 + WS-B8
- **P2:** WS-B5 + WS-B6 + WS-B2 (WS-B1/WS-B2 completed)
- **P3:** WS-B7 + WS-B9 + WS-B10 + WS-B11

### 4.4 Acceptance expectations for WS-B work

A workstream-ready PR should include:

1. clear recommendation/workstream mapping,
2. executable/test/proof evidence appropriate to scope,
3. no regression to stable contracts,
4. synchronized documentation and GitBook state,
5. explicit deferred items and owning follow-up workstream.

Authoritative detail for per-workstream goals, dependencies, and evidence gates:
[`docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md`](./audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md).

---

## 5) Current implementation surface inventory

Primary code layout:

- foundational model: `SeLe4n/Prelude.lean`, `SeLe4n/Machine.lean`, `SeLe4n/Model/*`
- kernel semantics:
  - scheduler: `SeLe4n/Kernel/Scheduler/*`
  - capability/CSpace: `SeLe4n/Kernel/Capability/*`
  - IPC/endpoints: `SeLe4n/Kernel/IPC/*`
  - lifecycle/retype: `SeLe4n/Kernel/Lifecycle/*`
  - service orchestration/policy: `SeLe4n/Kernel/Service/*`
  - architecture boundary: `SeLe4n/Kernel/Architecture/*`
- aggregate API entrypoint: `SeLe4n/Kernel/API.lean`
- executable evidence harness: `Main.lean`
- testing/trace anchors: `tests/fixtures/main_trace_smoke.expected`, `scripts/test_tier*.sh`

---

## 6) Change-control policy

For milestone/scope/acceptance changes:

1. update this file first,
2. update README + Development guide + relevant GitBook chapters in the same PR,
3. include rationale, risk note, and evidence commands,
4. avoid “future-tense” status wording when state is not yet delivered.

---

## 7) PR evidence checklist

- [ ] Workstream ID and objective stated.
- [ ] Relevant checks executed and reported.
- [ ] Theorem/invariant/trace surfaces remain coherent.
- [ ] Documentation synchronized.
- [ ] Deferred scope (if any) explicitly recorded.
