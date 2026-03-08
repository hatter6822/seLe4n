# seLe4n Development Guide

## 1) Purpose

This guide is the day-to-day operating manual for contributors to seLe4n — a
production-oriented microkernel written in Lean 4 with machine-checked proofs.

It is aligned to the **current project state**:

- **next workstream:** WS-H12..H16 (remaining v0.12.15 audit remediation — scheduler/IPC alignment, CSpace/service enrichment, type safety, platform hardening, testing/docs),
- **recently completed:** WS-H11 (v0.13.7, VSpace & architecture enrichment — PagePermissions with W^X enforcement, vspaceMapPageChecked with ARM64 52-bit address bounds, vspaceInvariantBundle 5-conjunct preservation, TLB/cache maintenance model, VSpaceBackend typeclass abstraction, 876 proved declarations), End-to-end audit (v0.13.6, comprehensive codebase audit — zero critical issues across 29,351 production LoC and 866 proved declarations, stale documentation metrics fixed, audit report produced at [`AUDIT_CODEBASE_v0.13.6.md`](audits/AUDIT_CODEBASE_v0.13.6.md)), WS-H10 (v0.13.6, security model foundations — MachineState in ObservableState, BIBA lattice alternatives, declassification model, endpoint flow policy well-formedness, 866 proved declarations), WS-H7/H8/H9 gaps closed (v0.13.5, BEq soundness lemmas, endpointReceiveDualChecked_NI bridge, 3 IPC NI theorems, 31-constructor NonInterferenceStep), WS-H9 (non-interference coverage extension >80% — 28-constructor NonInterferenceStep, 69 NI theorems, scheduler/IPC/CSpace/VSpace NI proofs, v0.13.4), WS-H8 (enforcement-NI bridge & missing wrappers — enforcement soundness meta-theorems, 4 new *Checked wrappers, projection hardening, v0.13.2), WS-H6 (scheduler proof completion — timeSlicePositive fully proven, EDF invariant domain-fixed, candidate optimality, v0.13.1), WS-H5 (IPC dual-queue structural invariant, v0.12.19), WS-H4 (capability invariant redesign, v0.12.18), WS-H3 (build/CI infrastructure fixes, v0.12.17), WS-H2 (lifecycle safety guards, v0.12.16), WS-H1 (IPC call-path semantic fix, v0.12.16), WS-G (kernel performance optimization — all 9 workstreams + refinement, v0.12.15), WS-F1..F4 (critical audit remediation),
- **findings baseline:** [`AUDIT_CODEBASE_v0.12.2_v1.md`](audits/AUDIT_CODEBASE_v0.12.2_v1.md), [`v2`](audits/AUDIT_CODEBASE_v0.12.2_v2.md),
- **latest audit:** [`AUDIT_CODEBASE_v0.13.6.md`](audits/AUDIT_CODEBASE_v0.13.6.md) — comprehensive end-to-end audit, zero critical issues,
- **hardware target:** Raspberry Pi 5 (ARM64).

Canonical planning source:
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](./audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

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

## 3) Next workstreams

Two workstream portfolios remain active. The primary focus is the remaining
WS-H workstreams from the v0.12.15 audit (Phases 4–5), with secondary focus
on the remaining WS-F workstreams from the v0.12.2 audit.

### 3.1 WS-H11..H16 — Remaining v0.12.15 audit remediation

See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md)
for the full execution plan.

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-H11** | VSpace & architecture enrichment (PagePermissions, W^X, TLB model) | Medium | **Completed** |
| **WS-H12** | Scheduler/IPC semantic alignment (MCS contexts, budget tracking) | Medium | Next |
| **WS-H13** | CSpace/service model enrichment (CDT refinement, service health) | Medium | Planned |
| **WS-H14** | Type safety hardening (phantom types, API boundary contracts) | Low | Planned |
| **WS-H15** | Platform hardening (RPi5 contract population, boot sequence) | Low | Planned |
| **WS-H16** | Testing and documentation expansion | Low | Planned |

### 3.2 WS-F5..F8 — Remaining v0.12.2 audit remediation

See [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md)
for the full execution plan.

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium | Next |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium | Next |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low | Planned |
| **WS-F8** | Cleanup (dead code, legacy/dual-queue resolution) | Low | Planned |

### 3.3 Completed portfolios

- **WS-H11:** completed (v0.13.7). VSpace & architecture enrichment — `PagePermissions` structure with `read`/`write`/`execute`/`user`/`cacheable` fields and `wxCompliant` W^X enforcement; `VSpaceRoot.mappings` enriched from `HashMap VAddr PAddr` to `HashMap VAddr (PAddr × PagePermissions)`; `vspaceMapPage` enforces W^X at insertion (`policyDenied` on violation); `vspaceLookupFull` returns `(PAddr × PagePermissions)`; `vspaceInvariantBundle` extended from 3 to 5 conjuncts (`wxExclusiveInvariant`, `boundedAddressTranslation` integrated); `VSpaceBackend` typeclass enriched with permissions; `MemoryRegion.wellFormed` and `MachineConfig.wellFormed` enforce `endAddr ≤ 2^physicalAddressWidth`; `TlbState`/`TlbEntry` abstract TLB model with `adapterFlushTlb`/`adapterFlushTlbByAsid` operations; `tlbConsistent` invariant with flush-restoration and composition theorems. Closes H-02/A-32 (HIGH), H-10 (HIGH), A-05/M-12 (HIGH), A-12 (HIGH), M-14 (MEDIUM).
- **WS-H10:** completed (v0.13.6). Security model foundations — `ObservableState` extended with `machineRegs` (domain-gated register file projection); machine timer excluded as covert timing channel; `bibaIntegrityFlowsTo`/`bibaSecurityFlowsTo`/`bibaPolicy` standard BIBA alternatives with refl/trans proofs; `DeclassificationPolicy` with `declassifyStore` enforcement operation (5 theorems) and `declassifyStore_NI` non-interference proof; `endpointFlowPolicyWellFormed` predicate with reflexivity/transitivity inheritance proofs; `InformationFlowConfigInvariant` bundle. Closes C-05/A-38 (CRITICAL), A-34 (CRITICAL), A-39 (MEDIUM), M-16 (MEDIUM). 866 proved declarations.
- **WS-H7/H8/H9 gap closure:** completed (v0.13.5). Comprehensive audit remediation — `VSpaceRoot.beq_sound`/`CNode.beq_sound` BEq soundness lemmas (WS-H7), `endpointReceiveDualChecked_NI` enforcement bridge (WS-H8), `endpointReceiveDual_preserves_lowEquivalent`/`endpointCall_preserves_lowEquivalent`/`endpointReplyRecv_preserves_lowEquivalent` hypothesis-based IPC NI theorems (WS-H9), `NonInterferenceStep` extended to 31 constructors with `endpointReceiveDualHigh`/`endpointCallHigh`/`endpointReplyRecvHigh`. 840 proved declarations.
- **WS-H9:** completed (v0.13.4). Non-interference coverage extension >80% of kernel operations — 27 new NI preservation theorems, `NonInterferenceStep` extended from 11 to 28 constructors, scheduler/IPC/CSpace/VSpace/observable-state NI proofs, `switchDomain_preserves_lowEquivalent` two-sided proof, `composedNonInterference_trace` covers all constructors. Closes C-02/A-40 (CRITICAL), M-15 (MEDIUM).
- **WS-H8:** completed (v0.13.2). Enforcement-NI bridge & missing wrappers — enforcement soundness meta-theorems connecting `securityFlowsTo` checks to non-interference; 4 new policy-checked wrappers (`notificationSignalChecked`, `cspaceCopyChecked`, `cspaceMoveChecked`, `endpointReceiveDualChecked`); `ObservableState` extended with domain timing metadata (`domainTimeRemaining`, `domainSchedule`, `domainScheduleIndex`); NI bridge theorems for all new wrappers. Closes A-35/H-07 (CRITICAL), H-07 (HIGH), A-36/A-37/H-11 (HIGH). 26 new theorems; 779 total.
- **WS-H6:** completed (v0.13.1). Scheduler proof completion — `timeSlicePositive` preservation proven for all 6 scheduler operations (`setCurrentThread`, `chooseThread`, `schedule`, `handleYield`, `switchDomain`, `timerTick`); `edfCurrentHasEarliestDeadline` fixed to be domain-aware (closing false-assurance gap); `chooseBestRunnableBy_optimal` (fold-based candidate optimality), `noBetter_implies_edf` (bridge to EDF invariant), `isBetterCandidate_not_better_trans` (negation transitivity); `schedulerInvariantBundleFull` (5-tuple bundle with projection and composition); plus earlier Part D/E work (`flat_wf_rev`, `mem_toList_iff_mem`, `isBetterCandidate_transitive`, `bucketFirst_fullScan_equivalence`).
- **WS-H7:** completed (v0.12.21). HashMap equality + state-store migration — `BEq VSpaceRoot`/`BEq CNode` switched from `toList` order-sensitive checks to size+fold order-independent checks; `services`, `irqHandlers`, `lifecycle.capabilityRefs`, `cdtSlotNode`, and `cdtNodeSlot` migrated from closure functions to `Std.HashMap`, removing O(k) closure-chain accumulation.
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
- WS-E4 dual-queue endpoint operations (`endpointSendDual`/`endpointReceiveDual`) use intrusive-list queue boundaries (`sendQ`/`receiveQ`) with per-thread links stored in `TCB.queuePrev`/`TCB.queuePPrev`/`TCB.queueNext`; invariant checks now include `intrusiveQueueWellFormed` validation for both endpoint queues (including head/tail shape, cycle-free traversal, and per-node `queuePrev`/`queuePPrev`/`queueNext` linkage), and `negative_state_suite` adds runtime queue-link assertions for both send-queue and receive-queue FIFO/dequeue paths alongside enqueue/block, rendezvous/dequeue, queue drain, O(1) middle removal via `endpointQueueRemoveDual`, malformed-`queuePPrev` rejection (`illegalState`), and dual-queue double-wait rejection (`alreadyWaiting`).
- WS-E4 CDT representation is node-stable: derivation edges are over stable node IDs and slots map to nodes via bidirectional maps (`cdtSlotNode`, `cdtNodeSlot`). `cspaceMove` updates slot→node ownership/backpointers instead of rewriting every CDT edge, `cspaceDeleteSlot` detaches stale slot↔node mappings on deletion, the observed slot-level CDT is defined as projection of node edges through the slot mapping (`SystemState.observedCdtEdges`), and strict revoke (`cspaceRevokeCdtStrict`) now reports the first descendant deletion failure with offending slot context.

## 5) Daily contributor loop

1. Sync branch and choose one coherent slice from the active plans (WS-H11..H16 or WS-F5..F8; prefer the highest-priority pending item).
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

For website codebase-map synchronization, run `./scripts/generate_codebase_map.py --pretty`
whenever Lean module/declaration surfaces change, then validate with
`./scripts/generate_codebase_map.py --pretty --check`. The generated
`docs/codebase_map.json` contains stable `source_sync.source_digest`
(sha256 over Lean source paths + contents) plus volatile `repository.head` git
metadata. Each declaration record includes an additive `called` array
listing in-module declaration references (or `[]` when none are detected), which
preserves backward compatibility for consumers that ignore unknown keys. Website
clients should invalidate local cache entries on `source_sync.source_digest`
changes. `--check` compares only the stable subset,
keeping CI robust across branch/merge-only commits while still detecting real
declaration-surface drift. Post-merge enforcement runs in
`.github/workflows/codebase_map_sync.yml`, which auto-regenerates and commits
the map on `main` when drift is detected.

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
