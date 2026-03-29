# Testing and CI

Current stage context: **All prior workstreams completed through WS-U Phase U8 (v0.21.7). Testing tiers enforce regression protection and evidence continuity across 64,229 production LoC, 8,316 test LoC, and 1,878 proved declarations.**

## Tier model

- **Tier 0 (hygiene)**
  - marker scan for forbidden placeholders (`axiom|sorry|TODO`) in tracked proof surface,
  - fixture-isolation guard (test-only contracts must not leak into production kernel modules),
  - wrapper-structure regression guard (scalar wrappers must remain structure-based),
  - theorem-body semantic depth check (L-08: Python analyzer flags `sorry` and trivial/single-tactic `preserves` proofs, with regex fallback),
  - SHA-pinning regression guard (F-14: all GitHub Actions must be SHA-pinned),
  - optional shell-quality checks.
- **Tier 1 (build/proof compile)**
  - full `lake build` to verify definitions, theorem scripts, and module integration.
- **Tier 2 (trace/behavior)**
  - executable scenario (`lake exe sele4n`) checked against stable fixture fragments,
  - **mandatory determinism validation** (WS-I1/R-02): `scripts/test_tier2_determinism.sh` runs trace twice and diffs output, failing on any divergence,
  - malformed/negative and IF-M1 runtime suites (`lake exe negative_state_suite`, `lake exe information_flow_suite`) run under `scripts/test_tier2_negative.sh`,
  - R8-D (I-M04): frozen/radix correctness suites (`radix_tree_suite`, `frozen_state_suite`, `freeze_proof_suite`, `frozen_ops_suite`) now execute in Tier 2 negative tests (67 scenarios),
  - fixture lines use pipe-delimited format with scenario IDs (`SCENARIO_ID | SUBSYSTEM | expected_trace_fragment`) for audit traceability (WS-I1/R-03),
  - all 121 trace output lines tagged with unique scenario IDs across 15 prefix families (ENT, CAT, SST, LEP, CIC, IMT, IMB, DDT, ICS, BME, STD, UMT, SGT, RCF, ITR, PTY),
  - 38 inter-transition invariant assertions (WS-I1/R-01, V8-C) check invariant families after every major transition group including post-mutation checks,
  - fixtures include WS-A4 scale scenarios for deep CNode radix, large runnable queues, multi-endpoint IPC, depth-5 service dependencies, and boundary memory addresses.
  - WS-B11 scenario metadata is maintained in `tests/scenarios/scenario_catalog.json` and validated by `scripts/scenario_catalog.py` in smoke/nightly gates.
  - scenario registry (`tests/fixtures/scenario_registry.yaml`) maps all scenario IDs to source functions; validated bidirectionally in Tier 0 hygiene,
  - V8-F: SHA-256 fixture drift detection (`main_trace_smoke.expected.sha256`) verified in Tier 2 trace,
  - V8-A: end-to-end `syscallEntryChecked` pipeline test (PIP-001..006) covering register decode → checked dispatch → invariant preservation → trace equivalence,
  - V8-B: `cspaceMove` end-to-end test (MOV-001..004) covering decode → move → source/dest verification,
  - V8-G: `ThreadState` consistency check (`threadStateConsistentChecks`) validates TCB `threadState` field matches inferred state from queue membership and IPC blocking state.
- **Tier 3 (invariant surface anchors + type-correctness #check gate)**
  - validates critical theorem/bundle/trace anchors expected for active milestone slices,
  - includes executable-trace anchor checks for milestone-critical lifecycle fragments.
- **Tier 4 (nightly staged extension candidates)**
  - `./scripts/test_tier4_nightly_candidates.sh` stages repeat-run determinism + seeded sequence-diversity candidates,
  - `./scripts/test_nightly.sh` uses mode-aware status messaging (default extension-point guidance vs explicit executed signal when `NIGHTLY_ENABLE_EXPERIMENTAL=1`),
  - includes seeded `trace_sequence_probe` sequence-diversity checks in experimental mode,
  - default remains explicit extension-point behavior unless `NIGHTLY_ENABLE_EXPERIMENTAL=1` is set.

## Entrypoints and intent

- `./scripts/test_fast.sh`
  - fast local confidence gate (Tier 0 + Tier 1).
- `./scripts/test_smoke.sh`
  - semantic smoke path (Tier 0 + Tier 1 + Tier 2).
- `./scripts/test_full.sh`
  - broader local verification (smoke + Tier 3 anchor coverage).
- `./scripts/test_nightly.sh`
  - full + Tier 4 staged-candidate wrapper (explicit opt-in by environment flag).

CI should execute these repository scripts directly to avoid local/CI drift.

Required branch-protection checks and reproducible setup instructions are documented in [`docs/CI_POLICY.md`](../CI_POLICY.md). CI jobs run each tier incrementally (earlier tiers gated by job dependencies) to eliminate redundant re-execution.

Documentation sync (`scripts/test_docs_sync.sh`) is integrated into the smoke CI job and the `test_smoke.sh` entrypoint (WS-H3/M-19), catching documentation navigation/link drift on every PR.

WS-A8 baseline maturity automation is implemented in `.github/workflows/platform_security_baseline.yml`, adding an ARM64 fast-gate CI signal and automated baseline security scanning controls.

## Shared test library behavior

All test entrypoints use `scripts/test_lib.sh` for:

1. common argument handling (`--continue`; disables `set -e` in continue mode per WS-H3/H-12),
2. command execution wrappers (`run_check` — returns 0 on success, 1 on failure),
3. centralized pass/fail accounting and final report,
4. optional automatic Lean setup helper path if `lake` is missing.

### Color-coded prefixes

The shared logger now colorizes output when running in an interactive terminal:

- category prefix colors (`[META]`, `[TRACE]`, `[HYGIENE]`, `[BUILD]`, `[INVARIANT]`),
- message-status colors for `RUN`, `PASS`, and `FAIL`,
- automatic fallback to plain text when output is non-interactive or `NO_COLOR` is set.

This keeps CI output clean while making local debugging much easier to scan.

## Why fixture checks matter

Type-checking alone can miss semantic regressions. Tier 2 trace + negative-state checks ensure critical runtime
stories remain visible and intentional, especially for milestone claims tied to executable behavior
(e.g., mint/revoke/delete and IPC handshake flows).

## Milestone testing trajectory

- **M4-A:** lifecycle semantic trace fragments are landed and fixture-backed in Tier 2 smoke coverage.
- **M4-B:** all M4-B workstreams complete, including Tier 3 M4-B symbol anchors and staged Tier 4 nightly candidates.
- **M5 (complete):** Tier 2/Tier 3 cover service restart/policy-denial/dependency-failure/isolation evidence, with Tier 4 candidates checking determinism plus M5 evidence-line anchors.
- **M6 (complete):** architecture-boundary assumption/adapter/invariant hook coverage in Tier 2 traces and Tier 3 anchors.
- **M7 (complete):** audit-remediation coverage (WS-A1..WS-A8) fully integrated into tiered gates.
- **WS-D (completed):** WS-D1 test validity, WS-D2 information-flow enforcement, WS-D3 proof gaps, WS-D4 kernel hardening all landed with updated Tier 2/3 coverage. WS-D5/WS-D6 absorbed into WS-E.
- **WS-E (completed):** v0.11.6 audit remediation workstreams (WS-E1..WS-E6) all completed.
- **WS-E1 (completed):** Test infrastructure and CI hardening — SHA-pinned all GitHub Actions (F-14), added 5 runtime invariant check families (M-11: CSpace coherency, capability rights, lifecycle metadata, service acyclicity, VSpace ASID uniqueness), parameterized test topologies with 3 configurations (M-10), structured trace format with scenario/risk metadata (L-07), and theorem-body spot-check validation (L-08).
- **WS-G refinement (v0.12.15):** Runtime invariant checks expanded with `runQueueThreadPriorityConsistentB` (RunQueue membership ↔ threadPriority consistency) and `cdtChildMapConsistentCheck` (CDT childMap ↔ edges bidirectional). `NegativeStateSuite` extended with `endpointReplyRecv` (2 negative + 1 positive) and `cspaceMutate` (2 negative + 2 positive) audit coverage checks. `StateBuilder.build` uses actual TCB priorities for RunQueue bucketing.
- **WS-H3 (v0.12.17):** Build/CI infrastructure fixes — `run_check` returns non-zero on failure in continue mode (H-12); `test_docs_sync.sh` integrated into smoke CI and `test_smoke.sh` (M-19); Tier 3 `rg` availability guard with `grep -P` fallback shim (M-20).
- **WS-H4 (v0.12.18):** Capability invariant redesign — `capabilityInvariantBundle` extended from 4-tuple to 7-tuple with `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity`. All 25+ preservation theorems re-proved against non-trivial predicates. Foundation lemmas added to `Model/Object.lean`. Default-state constructions in `Architecture/Invariant.lean` refactored with extracted helper.
- **WS-H5 (v0.12.19):** IPC dual-queue structural invariant — `intrusiveQueueWellFormed`, `dualQueueSystemInvariant`, `tcbQueueLinkIntegrity` predicates defined; 13 preservation theorems for all dual-queue operations (`endpointQueuePopHead`, `endpointQueueEnqueue`, `endpointSendDual`, `endpointReceiveDual`, `endpointCall`, `endpointReply`, `endpointReplyRecv`, `endpointAwaitReceive`, plus 5 state-only ops). Runtime `intrusiveQueueWellFormedB` checker integrated into endpoint invariant checks. Closes C-04/A-22 (CRITICAL), A-23 (HIGH), A-24 (HIGH). 734 theorem/lemma declarations total (zero sorry/axiom).
- **WS-H6 (v0.13.1):** Scheduler proof completion — `timeSlicePositive` preservation proven for all 6 scheduler operations; `edfCurrentHasEarliestDeadline` fixed to be domain-aware; `chooseBestRunnableBy_optimal` (fold optimality), `noBetter_implies_edf` (bridge lemma), `schedulerInvariantBundleFull` (5-tuple bundle with composition). 13 new theorems. 752 theorem/lemma declarations total (zero sorry/axiom).
- **WS-H8 (v0.13.2):** Enforcement-NI bridge & missing wrappers — 5 enforcement soundness meta-theorems connecting `securityFlowsTo` checks to NI hypotheses; 4 new `*Checked` wrappers (`notificationSignalChecked`, `cspaceCopyChecked`, `cspaceMoveChecked`, `endpointReceiveDualChecked`); `ObservableState` extended with `domainTimeRemaining`, `domainSchedule`, `domainScheduleIndex`; NI bridge theorems; 12 new executable tests in `InformationFlowSuite.lean`. 26 new theorems. 779 theorem/lemma declarations total (zero sorry/axiom).
- **WS-H9 (v0.13.4):** Non-interference coverage extension — 27 new NI preservation theorems across scheduler, IPC, CSpace, VSpace, and observable-state operations; `NonInterferenceStep` extended from 11 to 28 constructors; `composedNonInterference_trace` covers all constructors; NI coverage exceeds >80% of kernel operations. Closes C-02/A-40 (CRITICAL), M-15 (MEDIUM). 813 theorem/lemma declarations (zero sorry/axiom).
- **WS-H7/H8/H9 gap closure (v0.13.5):** BEq soundness lemmas, `endpointReceiveDualChecked_NI` bridge, 3 IPC NI theorems, `NonInterferenceStep` extended to 31 constructors. 840 theorem/lemma declarations (zero sorry/axiom).
- **WS-H10 (v0.13.6):** Security model foundations — `ObservableState` extended with domain-gated `machineRegs`; BIBA lattice alternatives; `DeclassificationPolicy` with `declassifyStore_NI`; `endpointFlowPolicyWellFormed`; `InformationFlowConfigInvariant` bundle. Closes C-05/A-38 (CRITICAL), A-34 (CRITICAL), A-39 (MEDIUM), M-16 (MEDIUM). 866 theorem/lemma declarations (zero sorry/axiom).
- **End-to-end audit (v0.13.6):** Comprehensive codebase audit covering all 40 production files (29,351 LoC), 866 theorem/lemma declarations, 3 test suites (2,063 LoC), build scripts, and platform bindings. Zero critical issues found. Stale documentation metrics corrected (theorem counts, LoC). Audit report: [`AUDIT_CODEBASE_v0.13.6.md`](../dev_history/audits/AUDIT_CODEBASE_v0.13.6.md).
- **WS-H11 (v0.13.7):** VSpace & architecture enrichment — `PagePermissions` with W^X enforcement, bounded address translation (ARM64 52-bit), `TlbState` abstract model with per-ASID and per-VAddr flush, cross-ASID isolation theorem, `VSpaceBackend` typeclass, `vspaceInvariantBundle` 5-conjunct composition. Proof deduplication via extracted helper lemmas. 20 negative tests for VSpace/TLB operations. 889 theorem/lemma declarations (zero sorry/axiom).
- **WS-H12a (v0.13.8):** Legacy endpoint removal — `EndpointState` type and legacy fields (`state`, `queue`, `waitingReceiver`) deleted from `Endpoint` structure. Legacy IPC operations (`endpointSend`, `endpointReceive`, `endpointAwaitReceive`) and `endpointSendChecked` removed. ~60 dead theorems cleaned from `IPC/Invariant.lean`, `Capability/Invariant.lean`, and `InformationFlow/Invariant.lean`. `endpointReplyRecv` migrated to `endpointReceiveDual`. Tests and tier-3 anchors updated. Closes A-08 (HIGH), M-01 (MEDIUM), A-25 (MEDIUM). 838 theorem/lemma declarations (zero sorry/axiom).
- **WS-H12b (v0.13.9):** Dequeue-on-dispatch scheduler semantics — inverted `queueCurrentConsistent` from `current ∈ runnable` to `current ∉ runnable`, matching seL4's `switchToThread`/`tcbSchedDequeue` pattern. `schedule` dequeues dispatched thread; `handleYield`, `timerTick`, and `switchDomain` re-enqueue before rescheduling. New predicates: `currentTimeSlicePositive`, `schedulerPriorityMatch`, plus 4 IPC dequeue-coherence predicates. ~1,800 lines of preservation proofs re-proved across scheduler, IPC, and information-flow invariant files. Closes H-04 (HIGH). 855 theorem/lemma declarations (zero sorry/axiom).
- **WS-F7 (testing expansion):** D1 — 4 new runtime invariant check families added to `InvariantChecks.lean`: `blockedOnSendNotRunnable` (includes `blockedOnCall`), `blockedOnReceiveNotRunnable` (includes `blockedOnReply`, `blockedOnNotification`), `currentThreadInActiveDomainB`, `uniqueWaitersCheck` — 17 check families total in `stateInvariantChecksFor`. D2 — `TraceSequenceProbe` extended from 3 to 7 `ProbeOp` variants (`notifySignal`, `notifyWait`, `scheduleOp`, `capLookup`) with notification + CNode objects in probe base state and blocked-thread guard. D3 — `runRuntimeContractFixtureTrace` exercises `runtimeContractTimerOnly` and `runtimeContractReadOnlyMemory` with 6 deterministic trace assertions. D4 — CDT `cdtChildMapConsistentCheck` confirmed already delivered. Closes MED-08, F-24, F-25, F-26.
- **WS-I1 (critical testing infrastructure, v0.15.0):** R-01 — 17 inter-transition invariant assertions across all 13 trace functions using `checkInvariants` helper with `IO.Ref Nat` counter tracking; R-02 — mandatory Tier 2 determinism validation (`test_tier2_determinism.sh`) integrated into smoke gate; R-03 — 121 trace lines tagged with unique scenario IDs (15 prefix families), pipe-delimited fixture format, `scenario_registry.yaml` with bidirectional Tier 0 validation. Closes R-01, R-02, R-03.
- **WS-I3 (operations coverage expansion, v0.15.2):** R-06 — new `tests/OperationChainSuite.lean` adds six multi-operation chain tests covering compositional transition sequences; R-07 — scheduler stress checks cover 16-thread repeated schedule/yield, same-priority deterministic selection, and multi-domain isolation under `switchDomain`+`schedule`; R-08 — `tests/InformationFlowSuite.lean` now validates `declassifyStore` paths (authorized downgrade success, normal-flow rejection, policy-denied rejection, and 3-domain lattice behavior). Tier 2 negative gate now runs `OperationChainSuite`. Policy-denied declassification now uses a dedicated `declassificationDenied` error path in runtime checks.
- **WS-I4 (subsystem coverage expansion, v0.15.3):** R-09 — `OperationChainSuite` adds shared-page multi-ASID VSpace tests validating cross-ASID coherency and per-ASID permission independence; R-10 — adds interleaved endpoint IPC checks (three-sender FIFO and alternating send/receive queue integrity); R-11 — adds lifecycle chain tests covering root→child→grandchild attenuation and strict cascading revoke cleanup in CDT-backed derivation trees.
- **WS-J1 (register-indexed authoritative namespaces, v0.15.4–v0.15.10):** Typed register wrappers (`RegName`/`RegValue`), `RegisterDecode.lean` module with total deterministic decode functions, `SyscallId` inductive (13 syscalls), `syscallEntry` register-sourced dispatch, `SyscallDecodeResult` with `msgRegs`, NI integration (2 new `NonInterferenceStep` constructors), 18 negative decode tests, 5 register-decode trace scenarios (RDT-002–RDT-010), 13 Tier 3 anchors. All 16 kernel identifiers now typed wrappers. 6 phases (J1-A through J1-F) complete.
- **WS-K (full syscall dispatch completion, v0.16.0–v0.16.8):** Per-syscall argument decode (`SyscallArgDecode.lean` with 10 structures (WS-Q1: +`ServiceRegisterArgs`, `ServiceRevokeArgs`, `ServiceQueryArgs`), 10 decode functions, 10 encode functions, 14 theorems), all 13 syscalls wired through `dispatchWithCap` using decoded message register arguments (zero `.illegalState` stubs), IPC message body population from decoded registers, round-trip proofs, lifecycle/VSpace NI completion (`retypeFromUntyped_preserves_lowEquivalent`, `lifecycleRevokeDeleteRetype_preserves_lowEquivalent`), `NonInterferenceStep` extended to 34 constructors, `syscallNI_coverage_witness`. 8 phases (K-A through K-H) complete. 1,198 theorem/lemma declarations (zero sorry/axiom).
- **WS-L (IPC subsystem audit, v0.16.9–v0.16.13 — PORTFOLIO COMPLETE):** End-to-end audit of 12 IPC files (9,195 LoC). Zero critical issues. All 5 phases delivered: L1 (performance), L2 (code quality), L3 (proof strengthening — 22 theorems), L4 (test coverage), L5 (documentation & closeout). Superseded WS-I5.
- **WS-M (Capability subsystem audit, v0.16.13–v0.17.0 — PORTFOLIO COMPLETE):** End-to-end audit of 5 Capability files (3,520 LoC). 14 findings: M-P01–P05 (performance), M-G01–G04 (proof gaps), M-T01–T03 (test coverage), M-D01–D02 (documentation). All 14 findings resolved across 5 phases. Phase M1 (v0.16.14): proof strengthening — 7 new proved declarations. Phase M2 (v0.16.15): performance optimization — M2-A fused revoke (`revokeAndClearRefsState` single-pass), M2-B CDT `parentMap` index for O(1) `parentOf` lookup, M2-C reply lemma extraction and new field preservation lemmas for NI proofs; `parentMapConsistent` runtime check; M-P01/P02/P03/P05 resolved. Phase M3 (v0.16.17): IPC capability transfer completed — `CapTransferResult`/`CapTransferSummary` types, `ipcTransferSingleCap`/`ipcUnwrapCaps` with preservation proofs, `endpointSendDualWithCaps`/`endpointReceiveDualWithCaps`/`endpointCallWithCaps` wrappers with IPC invariant preservation proofs, `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant`, API wiring, 4 test scenarios (SCN-IPC-CAP-TRANSFER-BASIC, SCN-IPC-CAP-TRANSFER-NO-GRANT, SCN-IPC-CAP-TRANSFER-FULL-CNODE, SCN-IPC-CAP-BADGE-COMBINED). Resolves L-T03. Phase M4 (v0.16.18): test coverage expansion — 5 `resolveCapAddress` edge case tests (guard-only CNode, 64-bit max depth, guard mismatch at intermediate level, partial bits, single-level leaf) + 3 `cspaceRevokeCdtStrict` stress tests (15+ deep chain, partial failure mid-traversal, branching BFS ordering). 8 new test scenarios addressing M-T01/M-T02. Phase M5 (v0.16.19–v0.17.0): streaming BFS optimization — `processRevokeNode` shared helper (DRY), `streamingRevokeBFS`/`cspaceRevokeCdtStreaming` operations, `processRevokeNode_preserves_capabilityInvariantBundle` shared proof, 4 test scenarios (branching, empty, deep chain, equivalence). Resolves M-P04. See [WS-M workstream plan](../dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md).

- **WS-N (Robin Hood hashing, v0.17.0–v0.17.5 — PORTFOLIO COMPLETE):** `RobinHoodSuite.lean` with 12 standalone + 6 integration tests covering insert/get/erase, collision chains, table growth, and kernel API bridge operations. All N1–N5 phases delivered.
- **WS-Q (Kernel State Architecture, v0.17.7–v0.17.14 — PORTFOLIO COMPLETE):** 9 phases covering the full two-phase architecture. Key test additions: `RadixTreeSuite.lean` (12 scenarios, 43 checks), `FrozenStateSuite.lean` (15 scenarios, 49 checks), `FreezeProofSuite.lean` (22 scenarios, 60 checks), `FrozenOpsSuite.lean` (15 scenarios, TPH-005–TPH-014), `TwoPhaseArchSuite.lean` (14 integration tests, 41 checks, builder→freeze→execution pipeline). Rust conformance: 64 unit tests + 25 conformance tests in `libsele4n` crates.
- **WS-R (Comprehensive Audit Remediation, v0.18.0–v0.18.7 — PORTFOLIO COMPLETE):** All 8 phases (R1–R8) delivered. Test additions include operation-chain suite extensions, cross-subsystem invariant tests, TLB flush validation, typed retype decode boundary tests, and R8-D execution of 4 frozen/radix suites (64 scenarios, 171 checks) in Tier 2.
- **WS-S Phase S2 (Test Hardening, v0.19.1):** Replaced 101 `reprStr` with `toString` (S2-A/B/C, U-H4); determinism checks converted to structural `==` via `BEq Except` instance — zero string-based comparisons in assertions. Added `buildChecked` with 8 runtime invariant checks, migrated primary test states (S2-F, U-L11). Added 11 error-path tests: full-CNode copy, 5-deep CDT revoke, region exhaustion, rights attenuation, device restriction, occupied slot, child ID collision (S2-G/H, U-L12). Created `Testing/Helpers.lean` shared module imported via `MainTraceHarness` for library reachability (S2-I, U-L13). Migrated deprecated `api*` wrappers to `syscallInvoke` (S2-J, U-M05).
- **WS-W Phase W5 (Test Infrastructure & Coverage, v0.22.16):** Consolidated 3 duplicate `expectError` implementations into shared `Helpers.lean` with `msgPrefix` parameter (W5-A). Documented 11-suite OID range table (W5-B). Added chain33 service lifecycle tests — 25 assertions covering `registerInterface`, `registerService` (5 error paths), `serviceRegisterDependency` (acyclic + cycle + nonexistent source/target), `revokeService` (success + registry/graph removal + cleanup + nonexistent), 3 `assertInvariants` calls (W5-C). Improved `buildChecked` error reporting with check numbers (W5-D). Added mutation testing assertions to chain1/chain5 (W5-E). Removed unused `_hCap` parameter (W5-F). Documented `resolveExtraCaps` silent-drop behavior (W5-G).
- **WS-W Phase W6 (Code Quality & Documentation, v0.22.17):** TCB existence invariant documented for `removeThreadFromQueue` (W6-A). Factored redundant lifecycle preservation proofs into bundled theorems (W6-B). Removed unused `crossSubsystemPredicates` list (W6-C). Documented two-tier API dispatch design (W6-D). Extracted `default_objects_none`/`default_objects_absurd` helpers (W6-E). Added `RHSet.invExtK` public API wrappers (W6-F). Added compile-time Lean-Rust constant sync assertions (W6-G). Documented `set_mr`/`get_mr` API asymmetry (W6-H). Documented CDT edge theorem suite as specification surface (W6-I). Documented RHTable specification surface theorems (W6-J). Documented lifecycle metadata enforcement chain (W6-K). **WS-W PORTFOLIO COMPLETE.**

## Practical failure triage

- **Tier 0 fails:** remove placeholder markers or fix script-level lint/hygiene issues.
- **Tier 1 fails:** resolve first Lean compile/proof failure before chasing downstream errors.
- **Tier 2 fails:** if `test_tier2_trace.sh` fails, inspect missing fixture lines; if `test_tier2_negative.sh` fails, inspect malformed-state or IF-M1 runtime assertions (`negative_state_suite` / `information_flow_suite`) and expected branch behavior.
- **Tier 3 fails (`./scripts/test_tier3_invariant_surface.sh`):** verify theorem/bundle/trace anchor names are still present after refactor, then repair the exact missing anchor in the referenced file.
- **Tier 4 fails (`./scripts/test_nightly.sh` / `./scripts/test_tier4_nightly_candidates.sh`):** inspect `tests/artifacts/nightly/` traces + determinism diff and decide whether the drift is semantic regression or an intentional behavior change that needs fixture updates.
