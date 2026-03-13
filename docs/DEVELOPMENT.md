# seLe4n Development Guide

## 1) Purpose

This guide is the day-to-day operating manual for contributors to seLe4n — a
production-oriented microkernel written in Lean 4 with machine-checked proofs.

It is aligned to the **current project state**:

- **next workstream:** WS-I4/WS-I5 (remaining v0.14.9 improvement portfolio slices). WS-I3 is now completed, and WS-F portfolio is fully completed (F1..F8),
- **recently completed:** WS-H15 (v0.14.7, platform & API hardening — `InterruptBoundaryContract` decidability, RPi5 contract hardening with substantive predicates, 13 capability-gated syscall wrappers, `AdapterProofHooks` concrete instantiation for Sim/RPi5, MMIO disjointness proof; closes A-33, A-41, A-42, M-13), WS-H14 (v0.14.6, type safety & Prelude foundations — `EquivBEq`/`LawfulBEq` for 14 identifier types, `LawfulMonad` for `KernelM`, `isPowerOfTwo` correctness proof, identifier roundtrip/injectivity theorems, `OfNat` instance removal for type-safety enforcement, sentinel predicate completion), Module restructuring (v0.14.5, decomposed 9 monolithic files into 24 focused submodules via re-export hub pattern; zero code loss, 50 new helper theorems extracted, 209 Tier 3 anchor checks updated), WS-H13 (v0.14.4, CSpace/service model enrichment — `cspaceDepthConsistent` invariant, `resolveCapAddress` theorems, `serviceStop` backing-object verification, `serviceGraphInvariant` preservation, `cspaceMove` atomicity; addresses H-01, A-21, A-29, A-30, M-17/A-31), WS-H12f (v0.14.3, test harness update & documentation sync — dequeue-on-dispatch, context switch, and bounded message trace scenarios; legacy `endpointInvariant` comment cleanup; expected fixture updated; Tier 3 anchors added; documentation synchronized), WS-H12e (v0.14.2, cross-subsystem invariant reconciliation), WS-H12d (v0.14.1, IPC message payload bounds — A-09 closed), WS-H12c (v0.14.0, per-TCB register context with inline context switch — H-03 closed), WS-H12b (v0.13.9, dequeue-on-dispatch scheduler semantics — H-04 closed), WS-H12a (v0.13.8, legacy endpoint removal), WS-H11 (v0.13.7, VSpace & architecture enrichment), End-to-end audit (v0.13.6), WS-H10 (v0.13.6, security model foundations), WS-H7/H8/H9 gaps closed (v0.13.5), WS-H9 (v0.13.4, NI coverage >80%), WS-H8 (v0.13.2, enforcement-NI bridge), WS-H6 (v0.13.1, scheduler proof completion), WS-H5 (v0.12.19, IPC dual-queue invariant), WS-H4 (v0.12.18, capability invariant redesign), WS-H3 (v0.12.17, build/CI), WS-H2 (v0.12.16, lifecycle safety), WS-H1 (v0.12.16, IPC call-path fix), WS-G (v0.12.15, kernel performance), WS-F1..F4 (critical audit remediation),
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

The WS-F portfolio (v0.12.2 audit) is fully complete — all 33 findings closed.
The active improvement portfolio is WS-I (v0.14.9). WS-I1 and WS-I2 are completed;
remaining follow-up workstreams are WS-I4..WS-I5.

### 3.1 WS-H11..H16 — Remaining v0.12.15 audit remediation

See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md)
for the full execution plan.

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-H11** | VSpace & architecture enrichment (PagePermissions, W^X, TLB model) | Medium | **Completed** |
| **WS-H12a** | Legacy endpoint field & operation removal | Medium | **Completed** |
| **WS-H12b** | Dequeue-on-dispatch scheduler semantics | Medium | **Completed** |
| **WS-H12c** | Per-TCB register context with inline context switch | Medium | **Completed** |
| **WS-H12d** | IPC message payload bounds | Medium | **Completed** |
| **WS-H12e** | Cross-subsystem invariant reconciliation | Medium | **Completed** |
| **WS-H12f** | Test harness update & documentation sync | Medium | **Completed** |
| **WS-H13** | CSpace/service model enrichment (multi-level resolution, backing-object verification, serviceCountBounded) | Medium | **Completed** |
| **WS-H14** | Type safety hardening: EquivBEq/LawfulBEq instances, LawfulMonad proofs, isPowerOfTwo verification, OfNat removal, sentinel completion | Low | **Completed** |
| **WS-H15** | Platform & API hardening (RPi5 contracts, syscall capability wrappers, AdapterProofHooks) | Low | **Completed** |
| **WS-H16** | Testing and documentation expansion | Low | Planned |

### 3.2 WS-F5..F8 — Remaining v0.12.2 audit remediation

See [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md)
for the full execution plan.

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium | **Completed** |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium | **Completed** |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low | **Completed** |
| **WS-F8** | Cleanup (dead type constructors, extension labeling, finding closure) | Low | **Completed** |

### 3.3 Completed portfolios

- **WS-I1:** completed (v0.15.0). Critical testing infrastructure — 17 inter-transition invariant assertions across all 13 trace functions (R-01), mandatory Tier 2 determinism validation (R-02), scenario ID traceability with 121 tagged trace lines, pipe-delimited fixture format, scenario registry YAML with Tier 0 validation (R-03). Phase 1 of the WS-I improvement portfolio. Closes R-01/R-02/R-03.
- **WS-I3:** completed (v0.15.2). Test coverage expansion — new `tests/OperationChainSuite.lean` with 6 multi-operation chains (retype→mint→revoke, send→send→receive FIFO, map→lookup→unmap→lookup, service start/stop dependency behavior, copy→move→delete, notification badge accumulation) plus scheduler stress checks (16-thread repeated scheduling, same-priority determinism, multi-domain scheduling). Added WS-I3/R-08 declassification runtime checks to `tests/InformationFlowSuite.lean` and integrated `OperationChainSuite` into Tier 2 (`scripts/test_tier2_negative.sh`). Closes R-06/R-07/R-08.
- **WS-F8:** completed. Cleanup — removed dead `ServiceStatus.failed`/`isolated` constructors, labeled Service subsystem as seLe4n extension with module docstrings (MED-17), closed F-14 (endpointInvariant already removed in WS-H12a), closed F-01 (legacy endpoint fields already removed in WS-H12a), closed MED-04 (domain lattice alive and exercised — finding misidentified). Completes 100% of v0.12.2 audit findings (33/33). Closes MED-04, MED-17, F-01, F-14, F-19.
- **WS-F7:** completed. Testing expansion — 4 new runtime invariant checks (`blockedOnSendNotRunnable`, `blockedOnReceiveNotRunnable`, `currentThreadInActiveDomain`, `uniqueWaiters`) added to `InvariantChecks.lean`; `TraceSequenceProbe` extended from 3 to 7 operation families (+ notification signal/wait, schedule, capability lookup) with blocked-thread guard; `runtimeContractTimerOnly` and `runtimeContractReadOnlyMemory` fixtures exercised in `MainTraceHarness` with 6 deterministic trace assertions; CDT `childMapConsistentCheck` confirmed already delivered. Zero sorry, zero axiom. Closes MED-08, F-24, F-25, F-26.
- **WS-F6:** completed (v0.14.9). Invariant quality — tautology reclassification, cross-subsystem coupling, adapter proof hooks. `capabilityInvariantBundle` reduced from 8-tuple to 6-tuple (removed tautological `cspaceInvariant`/`badgeInvariant`); `blockedOnNotificationNotRunnable` predicate added to `ipcSchedulerContractPredicates` (6-conjunct); `runnableThreadsAreTCBs` predicate added to `schedulerInvariantBundleFull` (6-conjunct) with 4 preservation theorems (`switchDomain`, `schedule`, `handleYield`, `timerTick`); `vspaceCrossAsidIsolation` added to `vspaceInvariantBundle` (6-conjunct) with `mapPage`/`unmapPage` proofs; `default_serviceCountBounded` and `default_serviceGraphInvariant` proved for service graph; bundle coherence verified across all subsystems. Zero sorry, zero axiom.
- **WS-H12f:** completed (v0.14.3). Test harness update & documentation sync — `runDequeueOnDispatchTrace` (dequeue-on-dispatch lifecycle with preemption re-enqueue), `runInlineContextSwitchTrace` (inline context save/restore verification through `handleYield` → `schedule`), `runBoundedMessageExtendedTrace` (zero-length, sub-boundary, max-caps acceptance); legacy `endpointInvariant` comment cleanup; expected fixture updated (108 lines); 9 new Tier 3 anchors; documentation synchronized. Completes WS-H12 composite workstream.
- **WS-H12e:** completed (v0.14.2). Cross-subsystem invariant reconciliation — `coreIpcInvariantBundle` upgraded from `ipcInvariant` to `ipcInvariantFull` (includes `dualQueueSystemInvariant` and `allPendingMessagesBounded`); `schedulerInvariantBundleFull` extended with `contextMatchesCurrent` (5-conjunct); `ipcSchedulerCouplingInvariantBundle` extended with `contextMatchesCurrent` and `currentThreadDequeueCoherent`; `proofLayerInvariantBundle` uses `schedulerInvariantBundleFull` (full bundle) instead of bare `schedulerInvariantBundle`; extraction theorems added; `switchDomain_preserves_contextMatchesCurrent` new preservation theorem; 8 `allPendingMessagesBounded` frame lemmas for primitive ops; 3 compound `*_preserves_allPendingMessagesBounded` theorems (notificationSignal, notificationWait, endpointReply); 7 composed `*_preserves_ipcInvariantFull` theorems for all IPC operations; all `*_preserves_schedulerInvariantBundleFull` theorems updated; default state proofs extended; Tier 3 invariant surface anchors updated. Completes deferred WS-H12d preservation theorems. Closes systemic invariant composition gaps from WS-H12a–d.
- **WS-H12d:** completed (v0.14.1). IPC message payload bounds — `IpcMessage` registers/caps migrated from `List` to `Array` with `maxMessageRegisters`(120)/`maxExtraCaps`(3), bounds enforcement at all 4 send boundaries, 4 `*_message_bounded` theorems, `allPendingMessagesBounded` system invariant, A-09 closed.
- **WS-H12c:** completed (v0.14.0). Per-TCB register context with inline context switch — `registerContext` field on TCB, `saveOutgoingContext`/`restoreIncomingContext` in `schedule`, information-flow projection strips register context, `endpointInvariant` removed, H-03 closed.
- **WS-H12b:** completed (v0.13.9). Dequeue-on-dispatch scheduler semantics — `queueCurrentConsistent` inverted from `current ∈ runnable` to `current ∉ runnable`, matching seL4's `switchToThread`/`tcbSchedDequeue`. `schedule` dequeues chosen thread before dispatch; `handleYield` inserts+rotates current thread before scheduling; `timerTick` re-enqueues on preemption; `switchDomain` re-enqueues before domain switch. Added `currentTimeSlicePositive` predicate to `schedulerInvariantBundleFull`; added `schedulerPriorityMatch` with `RunQueue.insert_preserves_wellFormed` and `insert_threadPriority` theorems. IPC predicates added: `currentThreadIpcReady`, `currentNotEndpointQueueHead`, `currentNotOnNotificationWaitList`, `currentThreadDequeueCoherent`. Helper lemmas `ensureRunnable_not_mem_of_not_mem`, `removeRunnable_not_mem_of_not_mem`, `ThreadId.ext`. ~1800 lines of preservation proofs re-proved. Closes H-04 (HIGH).
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
- Trace and probe harnesses now exercise policy-checked wrappers (`endpointSendDualChecked`, `cspaceMintChecked`, `serviceRestartChecked`) by default; unchecked operations remain available for research experiments.
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

For codebase-map synchronization, run `./scripts/generate_codebase_map.py --pretty`
whenever Lean module/declaration surfaces change, then validate with
`./scripts/generate_codebase_map.py --pretty --check`. The generated
`docs/codebase_map.json` contains:

- **`readme_sync`** — project-level metrics (version, LoC, theorem count,
  hardware target) used by README.md, SELE4N_SPEC.md, and GitBook chapters.
- **`source_sync`** — stable `source_digest` (SHA256 over Lean source paths +
  contents) plus volatile `repository.head` git metadata.
- **`modules`** — per-module declaration inventory. Each declaration record
  includes an additive `called` array listing in-module declaration references
  (or `[]` when none are detected).

Website clients should invalidate local cache entries on
`source_sync.source_digest` changes. `--check` compares only the stable subset,
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
