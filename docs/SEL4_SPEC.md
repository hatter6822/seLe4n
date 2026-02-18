# seLe4n Specification and Milestone Plan

## 1) Purpose

This document is the **normative scope and acceptance source** for milestone state,
active-slice intent, and change-control expectations.

Companion planning and execution documents:

- comprehensive-audit findings:
  [`docs/audits/AUDIT_v0.9.32.md`](./audits/AUDIT_v0.9.32.md)
- comprehensive-audit workstream execution plan:
  [`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](./audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md)

---

## 2) Milestone status map (current)

- **M4-A:** complete (lifecycle/retype foundations)
- **M4-B:** complete (lifecycle-capability composition hardening)
- M4-B (complete) baseline is retained for historical compatibility checks
- **M5:** complete (service graph + policy surfaces + proof package)
- **M6:** complete (architecture-boundary assumptions/adapters/invariant hooks)
- **M7:** complete (audit remediation WS-A1..WS-A8)
- **Current active slice:** comprehensive-audit v0.9.32 WS-C execution kickoff (Phase P0/P1 transition; execution now beginning on WS-C workstreams).

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

## 4) Active slice specification: comprehensive-audit WS-C portfolio

### 4.1 Slice objective

Close comprehensive-audit recommendations while preserving determinism,
proof hygiene, contributor usability, and hardware-readiness trajectory.

### 4.2 Workstream inventory

- **WS-C1:** IPC handshake correctness (critical; kickoff starting)
- **WS-C2:** Scheduler semantic fidelity (high; queued after correctness blockers)
- **WS-C3:** Proof-surface de-tautologization (critical; kickoff starting)
- **WS-C4:** Test validity hardening (high; kickoff starting)
- **WS-C5:** Information-flow assurance (critical; Phase P2 target)
- **WS-C6:** CI and supply-chain hardening (medium; Phase P3 target)
- **WS-C7:** Model structure and maintainability (medium; Phase P3 target)
- **WS-C8:** Documentation and GitBook consolidation (high; in progress)

### 4.3 Sequencing constraints

- **P0:** WS-C8 baseline reset + active-plan publication (in progress)
- **P1:** WS-C1 + WS-C3 + core WS-C2 + fixture-repair WS-C4 (execution beginning)
- **P2:** WS-C5 + remaining WS-C4 assurance expansion
- **P3:** WS-C6 + WS-C7 sustainment hardening

### 4.4 Acceptance expectations for WS-C work

A workstream-ready PR should include:

1. clear recommendation/workstream mapping,
2. executable/test/proof evidence appropriate to scope,
3. no regression to stable contracts,
4. synchronized documentation and GitBook state,
5. explicit deferred items and owning follow-up workstream.

Authoritative detail for per-workstream goals, dependencies, and evidence gates:
[`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](./audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md).

Security assumptions and trust boundaries for active and historical slices are documented in [`docs/THREAT_MODEL.md`](./THREAT_MODEL.md).

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
