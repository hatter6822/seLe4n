# seLe4n Development Guide

## 1) Purpose

This guide is the day-to-day operating manual for contributors to seLe4n — a
production-oriented microkernel written in Lean 4 with machine-checked proofs.

It is aligned to the **current project state**:

- **next workstream:** WS-F5..F8 (remaining v0.12.2 audit remediation — model fidelity, invariant quality, testing, cleanup),
- **recently completed:** WS-H6 (scheduler proof-surface completion, v0.12.20), WS-H5 (IPC dual-queue structural invariant, v0.12.19), WS-H4 (capability invariant redesign, v0.12.18), WS-H3 (build/CI infrastructure fixes, v0.12.17), WS-H2 (lifecycle safety guards, v0.12.16), WS-H1 (IPC call-path semantic fix, v0.12.16), WS-G (kernel performance optimization — all 9 workstreams + refinement, v0.12.15), WS-F1..F4 (critical audit remediation),
- **findings baseline:** [`AUDIT_CODEBASE_v0.12.2_v1.md`](audits/AUDIT_CODEBASE_v0.12.2_v1.md), [`v2`](audits/AUDIT_CODEBASE_v0.12.2_v2.md),
- **hardware target:** Raspberry Pi 5 (ARM64).

Canonical planning source:
[`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](./audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md).

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

## 3) Next workstream: remaining WS-F (F5–F8)

The critical WS-F workstreams (F1–F4) and the WS-G performance optimization
portfolio are completed. The next focus is the remaining medium/low-priority
WS-F workstreams.

See [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md)
for the full execution plan.

### 3.1 Remaining workstreams

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium | Next |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium | Next |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low | Planned |
| **WS-F8** | Cleanup (dead code, legacy/dual-queue resolution) | Low | Planned |

### 3.2 Completed portfolios

- **WS-H6:** completed (v0.12.20). Scheduler proof-surface completion — reverse `RunQueue` invariant `flat_wf_rev`, bidirectional membership/list lemmas `membership_implies_flat` + `mem_toList_iff_mem`, scheduler ordering theorem `isBetterCandidate_transitive`, and definitional equivalence anchor `bucketFirst_fullScan_equivalence`; scheduler membership validation now uses O(1) `runQueue` membership checks.
- **WS-H5:** completed (v0.12.19). IPC dual-queue structural invariant — `intrusiveQueueWellFormed`, `dualQueueSystemInvariant`, `tcbQueueLinkIntegrity`; 13 preservation theorems for all dual-queue operations. Closes C-04/A-22 (CRITICAL), A-23 (HIGH), A-24 (HIGH). See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-H4:** completed (v0.12.18). Capability invariant redesign — `capabilityInvariantBundle` extended from trivially-true 4-tuple to meaningful 7-tuple with `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity`. All preservation theorems re-proved. C-03, M-08/A-20, M-03. See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-H3:** completed (v0.12.17). Build/CI infrastructure fixes — `run_check` return value fix (H-12), `test_docs_sync.sh` CI integration (M-19), Tier 3 `rg` availability guard with `grep -P` fallback (M-20). See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-H2:** completed (v0.12.16). Lifecycle safety guards — childId collision/self-overwrite guards, TCB scheduler cleanup on retype, CNode CDT detach, atomic retype. See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-H1:** completed (v0.12.16). IPC call-path semantic fix — `blockedOnCall` variant, reply-target scoping, 5-conjunct `ipcSchedulerContractPredicates`. See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-G1..G9:** all completed (v0.12.6–v0.12.15). See [`docs/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md).
- **WS-F1..F4:** completed. See [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md).
- **WS-E1..E6:** all completed (historical archive).
- **WS-D1..D4:** completed (historical archive).
- **WS-C1..C8:** completed (historical archive).

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

1. Sync branch and choose one coherent WS-F5..F8 slice (prefer next priority in the active plan, starting with P3 targets).
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

Before touching any `Current state` numbers, run `./scripts/report_current_state.py`
and propagate the output verbatim to README/spec/GitBook mirrors in the same PR.
At minimum keep these attributes synchronized across all three surfaces: version,
Lean toolchain, production/test LoC, theorem+lemma count, build jobs, active
findings/audit references, and completed/next workstream status.

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
- [ ] For WS-H7/A-07 updates, verify `BEq VSpaceRoot` and `BEq CNode` avoid `HashMap.toList` order dependence (use size + fold checks).
