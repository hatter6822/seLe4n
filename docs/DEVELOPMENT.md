# seLe4n Development Guide

## 1) Purpose

This guide is the day-to-day operating manual for contributors.

It is aligned to the **current active slice**:

- active: **v0.11.6 Codebase Audit Remediation WS-E portfolio (WS-E1 through WS-E6 completed)**,
- completed predecessor: **WS-D portfolio (WS-D1..WS-D4 completed; WS-D5/D6 absorbed into WS-E)**,
- completed predecessor before that: **WS-C portfolio (WS-C1..WS-C8)**.

Canonical planning source:
[`docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](./audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md).

---

## 2) Non-negotiable baseline contracts

Unless a PR explicitly proposes spec-level change control, preserve:

1. deterministic transition semantics (explicit success/failure branches),
2. M3.5 IPC-scheduler handshake coherence semantics and trace anchors,
3. local + composed invariant layering,
4. theorem discoverability through stable naming,
5. fixture-backed executable evidence (`Main.lean` + trace fixture),
6. tiered validation command behavior (`test_fast`/`smoke`/`full`/`nightly`).

---

## 3) Completed execution slice (WS-E portfolio)

### 3.1 Workstreams and intent

- **WS-E1** — Test infrastructure and CI hardening (**completed** — M-10, M-11, F-14, L-07, L-08)
- **WS-E2** — Proof quality and invariant strengthening (**completed** — C-01, H-01, H-03)
- **WS-E3** — Kernel semantic hardening (**completed** — H-06, H-07, H-08, H-09, M-09, L-06)
- **WS-E4** — Capability and IPC model completion (**completed** — C-02, C-03, C-04, H-02, M-01, M-02, M-12)
- **WS-E5** — Information-flow maturity (**completed** — H-04, H-05, M-07)
- **WS-E6** — Model completeness and documentation (**completed** — M-03, M-04, M-05, M-08, F-17, L-01–L-05)

Canonical detail: [`docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md).

### 3.2 Sequencing model

Use the planning phases from the workstream backbone:

- **Phase P0:** Baseline — close quick fixes, publish WS-E backbone (**completed**)
- **Phase P1:** WS-E1 (test/CI — **completed**) + WS-E2 (proof quality — **completed**) — **completed**
- **Phase P2:** WS-E3 (kernel hardening) — **completed**
- **Phase P3:** WS-E4 (capability/IPC completion) — **completed**
- **Phase P4:** WS-E5 (information-flow maturity) — **completed**
- **Phase P5:** WS-E6 (model completeness/docs) — **completed**

### 3.3 Prior completed portfolios (historical)

- **WS-D1..WS-D4:** completed. WS-D5/D6 absorbed into WS-E. See [`docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md).
- **WS-C1..WS-C8:** completed. See [`docs/dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md).

### 3.4 PR-to-workstream discipline

Every milestone-moving PR should include:

1. workstream ID(s) advanced,
2. objective and exit-criterion delta,
3. command evidence,
4. synchronized docs updates (README/spec/development/GitBook as needed),
5. explicit deferrals (if any) and destination workstream.

---

## 4) Security hardening defaults

- IPC thread-state updates now fail with `objectNotFound` when the target TCB is missing (including reserved thread ID `0`), preventing ghost queue entries in endpoint/notification paths.
- Sentinel ID `0` is rejected at IPC TCB lookup/update boundaries (`lookupTcb`/`storeTcbIpcState`) rather than silently treated as a valid runtime thread identity.
- Trace and probe harnesses now exercise policy-checked wrappers (`endpointSendChecked`, `cspaceMintChecked`, `serviceRestartChecked`) by default; unchecked operations remain available for research experiments.
- WS-E4 dual-queue endpoint operations (`endpointSendDual`/`endpointReceiveDual`) use intrusive-list queue boundaries (`sendQ`/`receiveQ`) with per-thread links stored in `TCB.queuePrev`/`TCB.queueNext`; invariant checks now include `intrusiveQueueWellFormed` validation for both endpoint queues (including head/tail shape, cycle-free traversal, and per-node `queuePrev`/`queueNext` linkage), and `negative_state_suite` adds runtime queue-link assertions for both send-queue and receive-queue FIFO/dequeue paths alongside enqueue/block, rendezvous/dequeue, queue drain, and dual-queue double-wait rejection (`alreadyWaiting`).

## 5) Daily contributor loop

1. Sync branch and choose one coherent WS-E slice (prefer next priority in the active plan, starting with current phase targets).
2. Implement the minimal semantic/proof/doc delta.
3. Run smallest relevant check first, then higher tiers.
4. Update docs in the same commit range.
5. Re-run validation before commit.

Recommended command loop:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
```

Optional nightly/staged checks:

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

Environment note for `./scripts/setup_lean_env.sh` on apt-based systems:

- if a third-party apt mirror is temporarily unavailable, the setup script now retries `apt-get update` with primary distro sources only so required tool installs (`shellcheck`, `ripgrep`) remain reproducible.

---

## 6) Proof engineering standards

1. Keep proofs local-first; compose afterward.
2. Prefer explicit theorem statements and stable names.
3. Keep invariant bundles factored and named.
   - Current canonical IPC composition names:
     - `coreIpcInvariantBundle`
     - `ipcSchedulerCouplingInvariantBundle`
     - `lifecycleCompositionInvariantBundle`
   - Current canonical trace helper names for these slices:
     - `runCapabilityIpcTrace`
     - `runSchedulerTimingDomainTrace`
4. Avoid hidden global simplification behavior.
5. Never add `axiom`/`sorry` to core proof surfaces.
6. BFS completeness proof (TPI-D07-BRIDGE): formally resolved. The core
   completeness theorem (CP1), its equational lemmas (EQ1-EQ5), and closure
   lemmas (CB1-CB4) are all proved. The prerequisite lemma hierarchy in
   [`M2_BFS_SOUNDNESS.md §6`](audits/execution_plans/milestones/M2_BFS_SOUNDNESS.md)
   and its sub-documents ([M2A](audits/execution_plans/milestones/M2A_EQUATIONAL_THEORY.md)–[M2D](audits/execution_plans/milestones/M2D_COMPLETENESS_PROOF.md))
   is fully discharged. No further work is required for this tracking item.

---

## 7) Documentation synchronization rules

For changes that alter behavior, theorem surfaces, or slice status, update in the same PR:

1. `README.md`
2. `docs/spec/SELE4N_SPEC.md` (and `docs/spec/SEL4_SPEC.md` if seL4 reference material changes)
3. `docs/DEVELOPMENT.md`
4. impacted GitBook chapter(s) and `docs/gitbook/SUMMARY.md` if IA changes
5. any directly affected audit/workstream status document

Use [`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](./DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md)
for cross-document synchronization expectations.

---

## 8) Definition of done (milestone-moving changes)

A change is done when all are true:

- implementation compiles,
- trace/fixture behavior is intentionally stable or intentionally updated with rationale,
- theorem/invariant surface remains coherent and discoverable,
- tiered checks pass for the claimed scope,
- docs reflect exact current state (not intended future state).

---

## 9) Quick checklist (copy into PRs)

- [ ] Workstream ID(s) identified.
- [ ] Scope is one coherent slice.
- [ ] Transition semantics are explicit and deterministic.
- [ ] Invariant/theorem updates are paired with implementation changes.
- [ ] Required validation commands were run.
- [ ] Documentation was synchronized.
