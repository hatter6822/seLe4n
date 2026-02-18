# AUDIT v0.9.32 — Workstream Planning Backbone

This document is the canonical execution plan for closing every recommendation and criticism in [`AUDIT_v0.9.32.md`](./AUDIT_v0.9.32.md).

## 1) Planning objective

Deliver a semantically faithful and evidence-backed seL4 model by:

1. closing all **critical/high** correctness gaps first,
2. restoring confidence in proof/test claims,
3. tightening CI/documentation governance so status and reality stay aligned,
4. preserving deterministic execution and contributor ergonomics.

## 2) Planning principles

- **Truth over optimism:** statuses must reflect current code behavior, not intent.
- **Canonical-first docs:** this file is authoritative for current workstream sequencing and status.
- **Evidence-gated completion:** no workstream can move to completed without linked code/proof/tests.
- **Invariant-valid test entry:** new tests must begin from states satisfying baseline invariants unless explicitly testing invariant violations.
- **No claim without theorem:** security/semantic claims require executable checks or machine-checked theorems.

## 3) Recommendation-to-workstream matrix

| Workstream | Priority | Recommendation coverage from `AUDIT_v0.9.32.md` | Exit evidence |
|---|---|---|---|
| WS-C1 IPC handshake correctness | Critical | Immediate #1, #2, #3 | endpoint/notification semantics implemented; ipcState transitions wired; invariant proofs updated; trace + negative tests updated. |
| WS-C2 Scheduler semantic fidelity | High | Immediate #5 (noninterference dependency), Medium #10, Low #15 | priority-aware `chooseThread`; `handleYield` queue semantics; proofs/tests for runnable ordering. |
| WS-C3 Proof-surface de-tautologization | Critical | Immediate #4 | remove/relabel tautological theorems and replace with meaningful statements over changed state or relation. |
| WS-C4 Test validity hardening | High | High Priority #6, #7, #9 | invariant-valid fixtures, post-step invariant assertions, generative state exploration with reproducible seeds. |
| WS-C5 Information-flow assurance | Critical | Immediate #5, Medium #13 | at least one real `operation_preserves_lowEquivalent` theorem; service filtering by observer clearance in projection; regression tests. |
| WS-C6 CI and supply-chain hardening | Medium | Medium #14, CI §5.2, §5.4, §5.3 | architecture-safe cache keys, toolchain tag sanitization, stronger flake probe defaults, bounded TODO regex. |
| WS-C7 Model structure and maintainability | Medium | Architecture §1.2 (finite map migration, ServiceId wrapper, do-notation adoption, vspace lookup cleanup), Medium #11, #12 | finite object-store design ADR, `ServiceId` wrapper migration, shared lemmas consolidated, kernel op readability improvements. |
| WS-C8 Documentation and GitBook consolidation | High | Low #16, Docs §6.1, §6.2 | right-sized docs hierarchy, explicit “current vs historical” split, claim-audit table, root↔GitBook sync matrix refreshed. |

## 4) Execution phases

### Phase P0 — documentation baseline reset (now)

- Activate WS-C8.
- Publish this v0.9.32 planning backbone.
- Demote prior completed-status claims to historical records.

### Phase P1 — correctness blockers

- WS-C1, WS-C3, WS-C2 (core scheduling semantics), WS-C4 (fixture repairs).
- Goal: eliminate critical correctness and vacuous-proof claims.

### Phase P2 — assurance depth

- WS-C5 + remaining WS-C4 property-based/generative expansion.
- Goal: establish nontrivial information-flow and invariant-preservation evidence.

### Phase P3 — sustainability

- WS-C6 + WS-C7.
- Goal: operational reliability and maintainable model architecture.

## 5) Detailed execution contracts

### WS-C1 — IPC handshake correctness

**Scope**

- implement complete endpoint fast-path semantics (waiting receiver wakeup + runnable queue integration + payload/badge propagation model),
- wire all IPC state transitions on sender/receiver/waiter TCBs,
- correct notification active-state badge semantics (accumulation instead of overwrite).

**Code and proof targets**

- `SeLe4n/Kernel/IPC/Operations.lean`
- `SeLe4n/Kernel/IPC/Invariant.lean`
- scheduler/IPC contract preservation lemmas affected by real `ipcState` updates.

**Validation gates**

- `./scripts/test_tier2_trace.sh`
- `./scripts/test_tier2_negative.sh`
- `./scripts/test_tier3_invariant_surface.sh`

### WS-C2 — Scheduler semantic fidelity

**Scope**

- make `chooseThread` priority-aware,
- implement proper yield behavior (move current thread within runnable queue),
- preserve deterministic tie-breaking and explicit invalid-state failure modes.

**Code and proof targets**

- `SeLe4n/Kernel/Scheduler/Operations.lean`
- `SeLe4n/Kernel/Scheduler/Invariant.lean`
- trace harness expectations dependent on runnable order.

**Validation gates**

- `./scripts/test_tier1_build.sh`
- `./scripts/test_tier2_trace.sh`
- `./scripts/test_tier2_negative.sh`

### WS-C3 — Proof-surface de-tautologization

**Required changes**

1. remove the two tautological `_deterministic` theorems (`vspaceLookup_deterministic`, `projectState_deterministic`),
2. add module-level docstrings in the affected proof modules stating that determinism of pure Lean definitions is a meta-property and tautological `f(x)=f(x)` theorems are non-evidence,
3. replace with tracked semantic obligations and milestone-owned theorem tickets.

**Tracked obligations**

- See [`AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`](./AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md):
  - TPI-001 (VSpace round-trip theorem suite),
  - TPI-002 (noninterference preservation theorem seed).

**Validation gates**

- `./scripts/test_tier0_hygiene.sh`
- `./scripts/test_tier1_build.sh`
- `./scripts/test_tier3_invariant_surface.sh`

### WS-C4 — Test validity hardening

**Scope**

- repair fixture initialization so baseline traces begin from invariant-valid states,
- enforce post-operation invariant assertions in harness/probes,
- add reproducible generative exploration for valid-state transitions.

**Code and proof targets**

- `SeLe4n/Testing/StateBuilder.lean`
- `SeLe4n/Testing/MainTraceHarness.lean`
- `tests/NegativeStateSuite.lean`, `tests/TraceSequenceProbe.lean`, and fixture contracts.

**Validation gates**

- `./scripts/test_smoke.sh`
- `./scripts/test_full.sh`
- `./scripts/test_tier4_nightly_candidates.sh`

### WS-C5 — Information-flow assurance

**Scope**

- introduce real operation-preservation theorems over `lowEquivalent`,
- align observer projection with service-visibility policy,
- provide at least one nontrivial noninterference theorem accepted into Tier-3 anchors.

**Tracked obligation seed**

- TPI-002 in [`AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`](./AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md).

**Validation gates**

- `./scripts/test_tier2_negative.sh`
- `./scripts/test_tier3_invariant_surface.sh`
- `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh`

### WS-C6 — CI and supply-chain hardening

**Scope**

- normalize CI cache-key architecture isolation,
- sanitize toolchain/tag inputs in automation workflows,
- raise flake probe iterations and improve hygiene regex precision.

**Validation gates**

- `./scripts/test_fast.sh`
- `./scripts/test_full.sh`
- CI workflow dry-run checks as applicable.

### WS-C7 — Model structure and maintainability

**Scope**

- design and execute finite object-store migration plan,
- migrate `ServiceId` to typed wrapper,
- consolidate shared lemmas and reduce nested operation structure (do-notation adoption where appropriate),
- remove linear-scan architecture hacks where model allows.

**Outputs**

- ADR + staged migration plan + compatibility notes,
- proof and benchmark deltas for changed data model.

**Validation gates**

- `./scripts/test_full.sh`
- `./scripts/test_nightly.sh`

### WS-C8 — Documentation and GitBook consolidation

**Scope**

- keep active-vs-historical planning boundaries explicit,
- add auditable “claim vs evidence” index for semantics/proofs,
- reduce duplication between root docs and GitBook chapters.

**Validation gates**

- `./scripts/test_docs_sync.sh`
- `./scripts/test_smoke.sh`

## 6) Milestone gates

- **Gate G0 (planning readiness):** this file + README + GitBook chapter 24 + documentation matrix all reference `AUDIT_v0.9.32` as active baseline.
- **Gate G1 (correctness readiness):** WS-C1/C2/C3 critical items merged with passing Tier 0–3.
- **Gate G2 (assurance readiness):** WS-C4/C5 evidence merged; at least one nontrivial noninterference preservation theorem in tree.
- **Gate G3 (sustainment readiness):** WS-C6/C7 merged; CI hardening and architecture ADR accepted.

## 7) Workstream template (apply to each WS-C*)

Each workstream PR must include:

1. **Audit mapping:** exact recommendation IDs closed.
2. **Code diff summary:** semantic changes and failure-mode behavior.
3. **Proof delta:** new/changed theorems and assumptions.
4. **Test evidence:** command outputs from relevant tier scripts.
5. **Doc sync:** updates to root docs + GitBook mirrors.
6. **Deferred items:** explicit carry-forward list.

## 8) Current status dashboard

| Workstream | Status | Owner | Notes |
|---|---|---|---|
| WS-C1 | Completed | Kernel IPC | Notification badge accumulation + waiter ipcState transitions + Tier-2/Tier-3 evidence refreshed. |
| WS-C2 | Planned | Unassigned | Priority scheduling and yield semantics. |
| WS-C3 | Planned | Unassigned | Remove tautological determinism theorems and publish tracked theorem obligations. |
| WS-C4 | Planned | Unassigned | Invariant-valid tests + post-op checks + generators. |
| WS-C5 | Planned | Unassigned | First noninterference preservation theorem. |
| WS-C6 | Planned | Unassigned | CI cache/sanitization/flake/hygiene tightening. |
| WS-C7 | Planned | Unassigned | Finite store + maintainability refactor track. |
| WS-C8 | In Progress | Documentation | Documentation/GitBook re-baseline and detailed workstream specification. |

## 9) Canonical companion documents

- Findings source: [`AUDIT_v0.9.32.md`](./AUDIT_v0.9.32.md)
- Tracked theorem obligations: [`AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`](./AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md)
- Prior historical plan (superseded for active planning): [`AUDIT_v0.9.0_WORKSTREAM_PLAN.md`](./AUDIT_v0.9.0_WORKSTREAM_PLAN.md)
- Documentation synchronization policy: [`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](../DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md)
