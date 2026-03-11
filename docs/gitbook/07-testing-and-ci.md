# Testing and CI

Current stage context: **WS-H Phase 1–12f (v0.12.15 audit remediation) complete through WS-H12f (v0.14.3); WS-F1..F5 completed (WS-F6..F8 remaining); testing tiers enforce regression protection and evidence continuity across active workstreams.**

## Tier model

- **Tier 0 (hygiene)**
  - marker scan for forbidden placeholders (`axiom|sorry|TODO`) in tracked proof surface,
  - fixture-isolation guard (test-only contracts must not leak into production kernel modules),
  - wrapper-structure regression guard (scalar wrappers must remain structure-based),
  - theorem-body spot-check (L-08: no `sorry`, no trivial `rfl`-only preservation theorems),
  - SHA-pinning regression guard (F-14: all GitHub Actions must be SHA-pinned),
  - optional shell-quality checks.
- **Tier 1 (build/proof compile)**
  - full `lake build` to verify definitions, theorem scripts, and module integration.
- **Tier 2 (trace/behavior)**
  - executable scenario (`lake exe sele4n`) checked against stable fixture fragments,
  - malformed/negative and IF-M1 runtime suites (`lake exe negative_state_suite`, `lake exe information_flow_suite`) run under `scripts/test_tier2_negative.sh`,
  - fixture lines support scenario/risk tags (`scenario_id | risk_class | expected_trace_fragment`) for audit traceability.
  - fixtures include WS-A4 scale scenarios for deep CNode radix, large runnable queues, multi-endpoint IPC, depth-5 service dependencies, and boundary memory addresses.
  - WS-B11 scenario metadata is maintained in `tests/scenarios/scenario_catalog.json` and validated by `scripts/scenario_catalog.py` in smoke/nightly gates.
- **Tier 3 (invariant surface anchors)**
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
- **End-to-end audit (v0.13.6):** Comprehensive codebase audit covering all 40 production files (29,351 LoC), 866 theorem/lemma declarations, 3 test suites (2,063 LoC), build scripts, and platform bindings. Zero critical issues found. Stale documentation metrics corrected (theorem counts, LoC). Audit report: [`AUDIT_CODEBASE_v0.13.6.md`](../audits/AUDIT_CODEBASE_v0.13.6.md).
- **WS-H11 (v0.13.7):** VSpace & architecture enrichment — `PagePermissions` with W^X enforcement, bounded address translation (ARM64 52-bit), `TlbState` abstract model with per-ASID and per-VAddr flush, cross-ASID isolation theorem, `VSpaceBackend` typeclass, `vspaceInvariantBundle` 5-conjunct composition. Proof deduplication via extracted helper lemmas. 20 negative tests for VSpace/TLB operations. 889 theorem/lemma declarations (zero sorry/axiom).
- **WS-H12a (v0.13.8):** Legacy endpoint removal — `EndpointState` type and legacy fields (`state`, `queue`, `waitingReceiver`) deleted from `Endpoint` structure. Legacy IPC operations (`endpointSend`, `endpointReceive`, `endpointAwaitReceive`) and `endpointSendChecked` removed. ~60 dead theorems cleaned from `IPC/Invariant.lean`, `Capability/Invariant.lean`, and `InformationFlow/Invariant.lean`. `endpointReplyRecv` migrated to `endpointReceiveDual`. Tests and tier-3 anchors updated. Closes A-08 (HIGH), M-01 (MEDIUM), A-25 (MEDIUM). 838 theorem/lemma declarations (zero sorry/axiom).
- **WS-H12b (v0.13.9):** Dequeue-on-dispatch scheduler semantics — inverted `queueCurrentConsistent` from `current ∈ runnable` to `current ∉ runnable`, matching seL4's `switchToThread`/`tcbSchedDequeue` pattern. `schedule` dequeues dispatched thread; `handleYield`, `timerTick`, and `switchDomain` re-enqueue before rescheduling. New predicates: `currentTimeSlicePositive`, `schedulerPriorityMatch`, plus 4 IPC dequeue-coherence predicates. ~1,800 lines of preservation proofs re-proved across scheduler, IPC, and information-flow invariant files. Closes H-04 (HIGH). 855 theorem/lemma declarations (zero sorry/axiom).

## Practical failure triage

- **Tier 0 fails:** remove placeholder markers or fix script-level lint/hygiene issues.
- **Tier 1 fails:** resolve first Lean compile/proof failure before chasing downstream errors.
- **Tier 2 fails:** if `test_tier2_trace.sh` fails, inspect missing fixture lines; if `test_tier2_negative.sh` fails, inspect malformed-state or IF-M1 runtime assertions (`negative_state_suite` / `information_flow_suite`) and expected branch behavior.
- **Tier 3 fails (`./scripts/test_tier3_invariant_surface.sh`):** verify theorem/bundle/trace anchor names are still present after refactor, then repair the exact missing anchor in the referenced file.
- **Tier 4 fails (`./scripts/test_nightly.sh` / `./scripts/test_tier4_nightly_candidates.sh`):** inspect `tests/artifacts/nightly/` traces + determinism diff and decide whether the drift is semantic regression or an intentional behavior change that needs fixture updates.
