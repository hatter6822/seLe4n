# seLe4n Development Guide

## 1) Purpose

This guide is the day-to-day operating manual for contributors to seLe4n — a
production-oriented microkernel written in Lean 4 with machine-checked proofs.

It is aligned to the **current active slice**:

- **active:** WS-G portfolio (kernel performance optimization — WS-G1..G3 completed),
- **findings baseline:** [`KERNEL_PERFORMANCE_AUDIT_v0.12.5.md`](audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md),
- **completed predecessor:** WS-F portfolio (v0.12.2 audit remediation — WS-F1..F4 completed), WS-E (v0.11.6),
- **hardware target:** Raspberry Pi 5 (ARM64).

Canonical planning source:
[`docs/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](./audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md).

---

## 2) Non-negotiable baseline contracts

Unless a PR explicitly proposes spec-level change control, preserve:

1. deterministic transition semantics (explicit success/failure branches),
2. M3.5 IPC-scheduler handshake coherence semantics and trace anchors,
3. local + composed invariant layering (including `currentThreadInActiveDomain` in the canonical scheduler bundle),
4. domain-aware scheduling semantics (`schedule` only chooses from `activeDomain`; `scheduleDomain` switch/tick behavior is regression-tested),
5. theorem discoverability through stable naming,
6. fixture-backed executable evidence (`Main.lean` + trace fixture),
7. tiered validation command behavior (`test_fast`/`smoke`/`full`/`nightly`),
8. top-level import hygiene: keep `SeLe4n.lean` free of duplicate/redundant subsystem imports by relying on `SeLe4n/Kernel/API.lean` as the canonical aggregate surface.

---

## 3) Active workstream (WS-G: Kernel Performance Optimization)

The WS-G portfolio addresses 14 performance findings from the v0.12.5 kernel performance audit.
See [`docs/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md)
for the full execution plan.

### 3.1 Workstream summary

| ID | Focus | Priority | Key findings | Status |
|----|-------|----------|--------------|--------|
| **WS-G1** | Hashable/BEq infrastructure | Prerequisite | (infrastructure) | **Completed** |
| **WS-G2** | Object store HashMap | Critical | F-P01, F-P10, F-P13 | **Completed** |
| **WS-G3** | ASID resolution table | Critical | F-P06 | **Completed** |
| **WS-G4** | Run queue restructure | Critical | F-P02, F-P07, F-P12 | Planning |
| **WS-G5** | CNode slot HashMap | High | F-P03 | Planning |
| **WS-G6** | VSpace mapping HashMap | High | F-P05 | Planning |
| **WS-G7** | IPC queue + notification | High | F-P04, F-P11 | Planning |
| **WS-G8** | Graph traversal optimization | High | F-P08, F-P14 | Planning |
| **WS-G9** | Info-flow projection optimization | High | F-P09 | Planning |

### 3.2 Prior completed portfolios (historical)

- **WS-F1..F4:** completed. See [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md).
- **WS-E1..E6:** all completed. See [`docs/dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md).
- **WS-D1..D4:** completed. See [`docs/dev_history/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md).
- **WS-C1..C8:** completed. See [`docs/dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md).

### 3.3 PR-to-workstream discipline

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
- WS-E4 dual-queue endpoint operations (`endpointSendDual`/`endpointReceiveDual`) use intrusive-list queue boundaries (`sendQ`/`receiveQ`) with per-thread links stored in `TCB.queuePrev`/`TCB.queuePPrev`/`TCB.queueNext`; invariant checks now include `intrusiveQueueWellFormed` validation for both endpoint queues (including head/tail shape, cycle-free traversal, and per-node `queuePrev`/`queuePPrev`/`queueNext` linkage), and `negative_state_suite` adds runtime queue-link assertions for both send-queue and receive-queue FIFO/dequeue paths alongside enqueue/block, rendezvous/dequeue, queue drain, O(1) middle removal via `endpointQueueRemoveDual`, malformed-`queuePPrev` rejection (`illegalState`), and dual-queue double-wait rejection (`alreadyWaiting`).
- WS-E4 CDT representation is node-stable: derivation edges are over stable node IDs and slots map to nodes via bidirectional maps (`cdtSlotNode`, `cdtNodeSlot`). `cspaceMove` updates slot→node ownership/backpointers instead of rewriting every CDT edge, `cspaceDeleteSlot` detaches stale slot↔node mappings on deletion, the observed slot-level CDT is defined as projection of node edges through the slot mapping (`SystemState.observedCdtEdges`), and strict revoke (`cspaceRevokeCdtStrict`) now reports the first descendant deletion failure with offending slot context.

## 5) Daily contributor loop

1. Sync branch and choose one coherent WS-F slice (prefer next priority in the active plan, starting with current phase targets).
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
   [`M2_BFS_SOUNDNESS.md §6`](dev_history/audits/execution_plans/milestones/M2_BFS_SOUNDNESS.md)
   and its sub-documents ([M2A](dev_history/audits/execution_plans/milestones/M2A_EQUATIONAL_THEORY.md)–[M2D](dev_history/audits/execution_plans/milestones/M2D_COMPLETENESS_PROOF.md))
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
