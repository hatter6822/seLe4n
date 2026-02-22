# AUDIT v0.11.0 — Workstream Planning Backbone

This document is the canonical execution plan for closing every recommendation and criticism in [`AUDIT_v0.11.0.md`](./AUDIT_v0.11.0.md).

It supersedes the WS-C portfolio (`AUDIT_v0.9.32_WORKSTREAM_PLAN.md`) as the active execution baseline. The WS-C portfolio is retained as a completed historical record.

## 1) Planning objective

Close all 17 findings (F-01 through F-17) identified in the v0.11.0 end-to-end repository audit by:

1. eliminating critical test-validity failures that create false confidence,
2. closing high-severity proof and enforcement gaps in the information-flow layer,
3. hardening kernel design semantics (cycle detection, atomicity, double-wait prevention),
4. expanding test infrastructure beyond binary extremes and bounded discovery,
5. polishing CI supply-chain and documentation governance.

## 2) Planning principles

- **Truth over optimism:** statuses must reflect current code behavior, not intent.
- **Canonical-first docs:** this file is authoritative for current workstream sequencing and status.
- **Evidence-gated completion:** no workstream can move to completed without linked code/proof/tests.
- **Invariant-valid test entry:** new tests must begin from states satisfying baseline invariants unless explicitly testing invariant violations.
- **No claim without theorem:** security/semantic claims require executable checks or machine-checked theorems.
- **Continuity:** carry forward open obligations from WS-C (TPI-001 VSpace round-trip theorems remain open).

## 3) Finding-to-workstream matrix

| Finding | Severity | Description | Workstream |
|---|---|---|---|
| F-01 | **Critical** | TraceSequenceProbe silently ignores operation errors | WS-D1 |
| F-02 | **High** | Information-flow policy defined but never enforced | WS-D2 |
| F-03 | **High** | NegativeStateSuite incomplete state-mutation verification | WS-D1 |
| F-04 | **High** | InformationFlowSuite tautological assertions | WS-D1 |
| F-05 | **High** | No non-interference proof for kernel operations beyond endpoint send | WS-D2 |
| F-06 | **Medium** | Badge override in cspaceMint lacks safety proof | WS-D3 |
| F-07 | **Medium** | Service dependency cycles not prevented | WS-D4 |
| F-08 | **Medium** | VSpace successful-operation preservation not proven | WS-D3 |
| F-09 | **Medium** | RuntimeContractFixtures only accept-all / deny-all | WS-D5 |
| F-10 | **Medium** | InvariantChecks bounded to ObjId < 512 | WS-D5 |
| F-11 | **Medium** | serviceRestart is non-atomic | WS-D4 |
| F-12 | **Medium** | No double-wait prevention in notifications | WS-D4 |
| F-13 | **Low** | README version badge discrepancy | WS-D6 |
| F-14 | **Low** | GitHub Actions use floating tags | WS-D6 |
| F-15 | **Low** | lean_action_ci.yml lacks permissions block | WS-D6 |
| F-16 | **Low** | Trivial error-preservation proofs inflate theorem count | WS-D3 |
| F-17 | **Low** | List-based data structures give O(n) lookups | WS-D6 |

## 4) Execution phases

### Phase P0 — baseline transition (completed)

- Publish this v0.11.0 planning backbone.
- Demote WS-C portfolio to completed historical record.
- Update all cross-references (README, spec, GitBook, sync matrix).

### Phase P1 — test validity restoration (completed)

- **WS-D1:** Fix all three broken/weak executable test suites. **Completed.**
- All three findings (F-01, F-03, F-04) resolved. Tier 0-3 gates pass.

### Phase P2 — information-flow enforcement and proof (completed)

- **WS-D2:** Wire policy enforcement into kernel operations; extend non-interference proofs beyond endpoint send. **Completed.**
- All acceptance criteria met: `securityFlowsTo` enforced in three operations (`endpointSendChecked`, `cspaceMintChecked`, `serviceRestartChecked`), four additional non-interference theorems proved (`chooseThread`, `cspaceMint`, `cspaceRevoke`, `lifecycleRetypeObject`), enforcement boundary documented. Tier 0-3 gates pass.

### Phase P3 — proof completion and kernel hardening (completed)

- **WS-D3:** Close remaining proof gaps (badge safety, VSpace success preservation). **Completed.**
- All three findings (F-06, F-08, F-16) resolved. TPI-D04 and TPI-D05 closed. TPI-001 obligations from WS-C fully discharged. Four round-trip theorems proved. Seven Invariant.lean files annotated with proof-scope docstrings. Tier 0-3 gates pass.
- **WS-D4:** Harden kernel design (cycle detection, failure semantics, double-wait). **Completed.**
- All three findings (F-07, F-11, F-12) resolved. TPI-D06 closed. TPI-D07 closed (Risk 0 resolved: declarative acyclicity with Layers 0-4; sole deferred `sorry` on BFS bridge TPI-D07-BRIDGE). Tier 0-3 gates pass.

### Phase P4 — infrastructure expansion (Medium/Low)

- **WS-D5:** Expand test infrastructure (intermediate fixtures, unbounded ID discovery).
- **WS-D6:** CI supply-chain polish and documentation governance.
- Goal: sustainable infrastructure and complete audit closure.

## 5) Detailed execution contracts

### WS-D1 — Test Error Handling and Validity

**Priority:** Critical/High
**Findings closed:** F-01, F-03, F-04

**Scope**

1. **F-01 — Fix TraceSequenceProbe error suppression.**
   - Replace the silent `| .error _ => st` pattern in `stepOp` with error-aware handling.
   - Classify operations into expected failures (e.g., sending to a full endpoint, operating on missing objects in a sparse state) and unexpected failures.
   - Record and report unexpected failures; count expected failures separately.
   - Make the seed configurable (current hardcoded `7`) while preserving deterministic reproducibility.
   - Ensure post-step invariant checks run after *actual state mutations*, not after no-ops.

2. **F-03 — Add state-mutation assertions to NegativeStateSuite.**
   - Badge accumulation test: assert the badge value *before* the final signal, not just after.
   - VSpace map test: verify the mapping was actually created via a subsequent lookup.
   - Yield test: verify which thread is `current` after rotation, not just list membership.
   - Notification wait: consistently check TCB `ipcState` across all wait-test variants.

3. **F-04 — Replace tautological assertions in InformationFlowSuite.**
   - Remove `lowEquivalent st st` reflexivity-only witness; replace with comparison of *different* states that should project identically for a low observer.
   - Service projection test: use a state where the service *exists* and is *below* the observer, confirming the projection returns meaningful data.
   - Add `projectServiceStatus` explicit coverage.
   - Add observer discrimination test: high-clearance observer sees more than low-clearance observer on the same state.

**Code targets**

- `tests/TraceSequenceProbe.lean`
- `tests/NegativeStateSuite.lean`
- `tests/InformationFlowSuite.lean`

**Validation gates**

- `./scripts/test_smoke.sh` (Tier 0-2)
- `./scripts/test_full.sh` (Tier 0-3)
- `./scripts/test_tier2_trace.sh`
- `./scripts/test_tier2_negative.sh`

**Acceptance criteria**

- TraceSequenceProbe reports unexpected failures instead of swallowing them.
- NegativeStateSuite checks pre-conditions and post-conditions for every state mutation.
- InformationFlowSuite compares distinct states and tests observer discrimination.
- All tier 0-3 tests pass.

**Completion evidence**

All acceptance criteria met. Summary of changes:

1. **F-01 (TraceSequenceProbe):** Replaced silent `| .error _ => st` with structured
   `StepOutcome` type (`mutated | expectedFailure | unexpectedFailure`). Error classification
   distinguishes expected state-mismatch errors from unexpected objectNotFound/invalidCapability
   errors. Invariant checks run only after actual state mutations, not after no-ops. Seed is
   configurable via CLI arguments. Probe reports mutation/expected/unexpected counts.

2. **F-03 (NegativeStateSuite):** Added badge precondition assertion (badge=66 verified
   before accumulation with badge=5). VSpace map test verifies mapping creation via subsequent
   `vspaceLookup`. Yield test asserts which thread is `current` after rotation. Notification
   wait #2 checks TCB `ipcState` is `.ready` after consuming badge. Signal wake checks waiter
   TCB `ipcState` transitions to `.ready`.

3. **F-04 (InformationFlowSuite):** Removed tautological `lowEquivalent st st` reflexivity
   witness. Replaced with distinct-state comparison (`sampleState` vs `altState`) that differs
   in secret components but projects identically for a public observer. Added public-visible
   service entry (`publicServiceEntry`) with explicit `projectServiceStatus` coverage. Added
   observer discrimination tests verifying admin sees objects/services/threads that public
   observer cannot.

Validation gates: `./scripts/test_full.sh --continue` passes Tier 0-3.

---

### WS-D2 — Information-Flow Enforcement and Proof

**Priority:** High
**Findings closed:** F-02, F-05

**Scope**

1. **F-02 — Wire information-flow policy enforcement into kernel operations.**
   - `securityFlowsTo` in `Policy.lean` is defined but never called by any kernel operation.
   - Add policy checks at a minimum to `endpointSend` (sender→receiver flow), `cspaceMint` (authority→target flow), and `serviceRestart` (orchestrator→service flow).
   - Define a clear enforcement boundary: which operations check policy vs. which rely on capability-based authority alone. Document this decision as an ADR or in the spec.

2. **F-05 — Extend non-interference proofs beyond endpoint send.**
   - `endpointSend_preserves_lowEquivalent` is the only non-interference theorem.
   - Add non-interference preservation theorems for:
     - `schedulerChooseThread` (scheduler must not leak high-domain scheduling decisions to low observers),
     - `cspaceRevoke` / `cspaceMint` (capability operations must preserve low-equivalence for unrelated observers),
     - `lifecycleRetypeObject` (lifecycle operations must not leak metadata to unauthorized observers).
   - Each theorem follows the pattern: if two states are low-equivalent for an observer and the actor is not observable by that observer, then the post-states remain low-equivalent.

**Code and proof targets**

- `SeLe4n/Kernel/InformationFlow/Policy.lean`
- `SeLe4n/Kernel/InformationFlow/Invariant.lean`
- `SeLe4n/Kernel/IPC/Operations.lean` (enforcement hook)
- `SeLe4n/Kernel/Capability/Operations.lean` (enforcement hook)
- `SeLe4n/Kernel/Service/Operations.lean` (enforcement hook)

**Validation gates**

- `./scripts/test_tier1_build.sh`
- `./scripts/test_tier2_negative.sh`
- `./scripts/test_tier3_invariant_surface.sh`
- `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh`

**Acceptance criteria**

- `securityFlowsTo` is called in at least three kernel operations with documented enforcement semantics.
- At least three non-interference preservation theorems exist (beyond `endpointSend`), each proved without `sorry`.
- Enforcement boundary is documented.

**Dependencies:** WS-D1 should be completed first so test suites can validate the enforcement hooks.

---

### WS-D3 — Proof Gap Closure

**Priority:** Medium
**Findings closed:** F-06, F-08, F-16
**Carries forward:** TPI-001 from WS-C (VSpace round-trip theorems)

**Scope**

1. **F-06 — Prove badge-override safety in cspaceMint.**
   - `cspaceMint` allows a caller to set a badge on a derived capability that differs from the parent badge.
   - Prove that the derived capability's rights are a subset of the parent's rights (attenuation holds even with badge override).
   - Prove that badge override cannot enable a capability holder to access objects outside the authority granted by the parent.

2. **F-08 — Prove VSpace successful-operation preservation.**
   - Currently only error cases are proven for `vspaceMapPage` and `vspaceUnmapPage`.
   - Prove that a *successful* `vspaceMapPage` preserves `vspaceInvariantBundle`.
   - Prove that a *successful* `vspaceUnmapPage` preserves `vspaceInvariantBundle`.
   - Close TPI-001 obligations (carried from WS-C):
     - `vspaceLookup_after_map`: mapping then looking up yields the mapped address.
     - `vspaceLookup_map_other`: mapping vaddr does not affect lookup of a different vaddr'.
     - `vspaceLookup_after_unmap`: after unmap, lookup fails with `translationFault`.

3. **F-16 — Document trivial error-preservation proof scope.**
   - Add module-level docstrings to all `Invariant.lean` files clarifying that error-case preservation theorems are trivially true because the error path returns the unchanged state.
   - Distinguish these from meaningful preservation theorems in the proof map documentation.
   - Update the claim-evidence index to separate trivial preservation from substantive theorems.

**Code and proof targets**

- `SeLe4n/Kernel/Capability/Invariant.lean`
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`
- `SeLe4n/Kernel/Architecture/VSpace.lean`
- All `Invariant.lean` files (docstring updates)
- `docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`

**Validation gates**

- `./scripts/test_tier1_build.sh`
- `./scripts/test_tier3_invariant_surface.sh`
- `./scripts/test_full.sh`

**Acceptance criteria**

- Badge attenuation proof holds with arbitrary badge override in `cspaceMint`.
- VSpace invariant bundle preservation proven for both success and error cases of map/unmap.
- TPI-001 obligations closed with three round-trip theorems proved without `sorry`.
- Each `Invariant.lean` file has a module docstring distinguishing trivial from substantive proofs.

**Dependencies:** None (proof work is independent of test fixes).

**Completion evidence**

All acceptance criteria met. Summary of changes:

1. **F-06 (Badge-override safety in cspaceMint):** Three badge-safety theorems added
   to `Capability/Invariant.lean`: `mintDerivedCap_rights_attenuated_with_badge_override`
   (rights attenuation holds regardless of badge), `mintDerivedCap_target_preserved_with_badge_override`
   (target identity preserved regardless of badge), and `cspaceMint_badge_override_safe`
   (composed kernel-operation-level safety: badge override in cspaceMint cannot escalate privilege).
   All proved without `sorry`. TPI-D04 closed.

2. **F-08 (VSpace successful-operation preservation):** Two success-path preservation
   theorems added to `VSpaceInvariant.lean`: `vspaceMapPage_success_preserves_vspaceInvariantBundle`
   and `vspaceUnmapPage_success_preserves_vspaceInvariantBundle`. Both prove invariant
   preservation over genuinely modified state. Supporting infrastructure added:
   - `resolveAsidRoot_some_implies` and `resolveAsidRoot_of_unique_root` (VSpace.lean)
   - `storeObject_objectIndex_eq_of_mem` (VSpace.lean)
   - VSpaceRoot helper theorems: `mapPage_asid_eq`, `unmapPage_asid_eq`, `lookup_eq_none_not_mem`,
     `mapPage_noVirtualOverlap`, `unmapPage_noVirtualOverlap`, `lookup_mapPage_ne`, `lookup_unmapPage_ne`
     (Object.lean)
   Four TPI-001 round-trip theorems proved: `vspaceLookup_after_map`, `vspaceLookup_map_other`,
   `vspaceLookup_after_unmap`, `vspaceLookup_unmap_other`. All proved without `sorry`. TPI-D05 and
   TPI-001 closed.

3. **F-16 (Document trivial error-preservation proof scope):** Module-level `/-! ... -/`
   docstrings added to all seven `Invariant.lean` files (Scheduler, IPC, Capability,
   Lifecycle, InformationFlow, Service, Architecture, VSpaceInvariant). Each docstring
   classifies every theorem as substantive preservation, error-case preservation (trivially
   true), structural/bridge, non-interference, or badge-safety. Claim-evidence index updated.

---

### WS-D4 — Kernel Design Hardening

**Priority:** Medium
**Findings closed:** F-07, F-11, F-12

**Scope**

1. **F-07 — Add service dependency cycle detection.**
   - Add a cycle check to `serviceRegisterDependency` that rejects registrations that would create circular dependencies.
   - Prove that the absence of cycles is an invariant: if the dependency graph is acyclic before registration, it remains acyclic after a successful registration.
   - Alternative (if full cycle detection is too complex for the abstract model): document the design decision to defer cycle detection and add it as a tracked obligation for hardware-targeted slices.

2. **F-11 — Make serviceRestart atomic or document failure semantics.**
   - Current behavior: `serviceRestart` calls stop then start. If stop succeeds but start fails, the service remains stopped.
   - Option A: make restart atomic by rolling back on start failure.
   - Option B: document the intentional partial-failure semantics as an explicit design decision with justification (e.g., "a failed restart leaves the service stopped to prevent running in an inconsistent state").
   - Either way, prove the invariant is preserved across the chosen semantics.

3. **F-12 — Add double-wait prevention in notifications.**
   - Check whether a thread is already in a waiting state before allowing `notificationWait` to add it to the waiting list.
   - Return a clear error (`alreadyWaiting` or equivalent) if the thread is already waiting.
   - Prove that the waiting list never contains duplicates as an invariant.

**Code and proof targets**

- `SeLe4n/Kernel/Service/Operations.lean`
- `SeLe4n/Kernel/Service/Invariant.lean`
- `SeLe4n/Kernel/IPC/Operations.lean`
- `SeLe4n/Kernel/IPC/Invariant.lean`
- `SeLe4n/Model/State.lean` (if new error variants are needed)

**Validation gates**

- `./scripts/test_tier1_build.sh`
- `./scripts/test_tier2_negative.sh`
- `./scripts/test_tier3_invariant_surface.sh`
- `./scripts/test_full.sh`

**Acceptance criteria**

- Cyclic service dependency registration is rejected (or deferral is formally documented).
- serviceRestart either rolls back on failure or has documented partial-failure semantics with invariant proof.
- Double-wait on notification is rejected with an explicit error; waiting-list uniqueness proved.

**Dependencies:** WS-D1 (test fixes) should be complete so negative-state tests can validate rejection paths.

**Completion evidence**

All acceptance criteria met. Summary of changes:

1. **F-07 (Service dependency cycle detection):** Added `serviceRegisterDependency` with
   deterministic check ordering: service lookup, self-dependency check, idempotent edge check,
   BFS cycle detection via `serviceHasPathTo`, then edge insertion. BFS fuel bound uses
   `serviceBfsFuel` (objectIndex.length + 256). `cyclicDependency` error variant added to
   `KernelError`. Self-loop rejection theorem (`serviceRegisterDependency_error_self_loop`)
   proved without `sorry`. **Risk 0 resolved (TPI-D07 closed):** The vacuous BFS-based
   acyclicity invariant was replaced with a declarative definition using `serviceNontrivialPath`.
   The preservation theorem (`serviceRegisterDependency_preserves_acyclicity`) is proved via
   post-insertion path decomposition and BFS contradiction — the main theorem is sorry-free.
   The sole deferred obligation is `bfs_complete_for_nontrivialPath` (TPI-D07-BRIDGE), a
   focused BFS completeness bridge validated by executable tests. NegativeStateSuite validates
   self-loop, missing-target, cycle, and idempotent re-registration paths.
   Full execution plan in `docs/audits/execution_plans/`; M0 baseline lock completed.

2. **F-11 (serviceRestart failure semantics):** Partial-failure semantics documented as an
   explicit design decision (Option B): a failed restart leaves the service stopped to prevent
   running in a potentially inconsistent state. The error monad ensures no intermediate state
   is accessible to the caller. Failure-semantics theorem (`serviceRestart_error_discards_state`)
   and functional decomposition theorem (`serviceRestart_error_from_start_phase`) added to
   Service/Invariant.lean. Existing staged-step decomposition theorems retained.

3. **F-12 (Double-wait prevention):** Added `alreadyWaiting` error variant to `KernelError`.
   `notificationWait` now checks `waiter ∈ ntfn.waitingThreads` before appending. Rejection
   theorem (`notificationWait_error_alreadyWaiting`) proved without `sorry`. Decomposition
   lemmas added (`notificationWait_badge_path_notification`, `notificationWait_wait_path_notification`)
   for post-state notification tracking through `storeTcbIpcState` and `removeRunnable`.
   `uniqueWaiters` invariant defined in IPC/Invariant.lean; preservation theorem
   (`notificationWait_preserves_uniqueWaiters`) proved without `sorry`. Helper lemmas added:
   `storeTcbIpcState_preserves_objects_ne`, `storeTcbIpcState_preserves_notification`,
   `removeRunnable_preserves_objects`. NegativeStateSuite validates double-wait rejection.

Validation gates: `./scripts/test_full.sh` passes Tier 0-3.

---

### WS-D5 — Test Infrastructure Expansion

**Priority:** Medium
**Findings closed:** F-09, F-10

**Scope**

1. **F-09 — Add intermediate RuntimeContractFixtures.**
   - Create at least two intermediate access-control fixtures:
     - `runtimeContractTimerOnly`: allows timer operations, denies memory read/write.
     - `runtimeContractReadOnlyMemory`: allows memory reads, denies writes and timer operations.
   - Use these fixtures in the trace harness or test suites to verify that the adapter layer correctly enforces partial permission policies.

2. **F-10 — Remove 512-ID bound from InvariantChecks.**
   - Replace `(List.range 512).map ObjId.ofNat` with a discovery function that derives the check list from the actual `objectIndex` in `SystemState`.
   - Ensure all objects in the store are covered by invariant checks regardless of their ID values.
   - Add a meta-check that verifies the discovery function covers the same set as `objectIndex`.

**Code targets**

- `SeLe4n/Testing/RuntimeContractFixtures.lean`
- `SeLe4n/Testing/InvariantChecks.lean`
- `SeLe4n/Testing/MainTraceHarness.lean` (if updated to use new fixtures)

**Validation gates**

- `./scripts/test_smoke.sh`
- `./scripts/test_full.sh`
- `./scripts/test_tier3_invariant_surface.sh`

**Acceptance criteria**

- At least two intermediate contract fixtures exist and are exercised in tests.
- InvariantChecks uses the actual object index, not a hardcoded range.
- All tier 0-3 tests pass with expanded coverage.

**Dependencies:** WS-D1 (so that expanded tests are built on a sound test foundation).

---

### WS-D6 — CI/CD and Documentation Polish

**Priority:** Low
**Findings closed:** F-13, F-14, F-15, F-17

**Scope**

1. **F-13 — Version badge discrepancy.**
   - The v0.11.0 audit reported `README.md` showed version `0.10.5`. Current `README.md` already shows `0.11.0`. Verify this finding is resolved and mark closed at intake.

2. **F-14 — SHA-pin GitHub Actions.**
   - Replace floating tags (`actions/checkout@v6`, `actions/cache@v5`, etc.) with SHA-pinned versions in all workflow files.
   - Add a comment next to each pinned SHA noting the tag it corresponds to for maintainability.
   - Consider adding Dependabot configuration for automated action version updates.

3. **F-15 — Add explicit permissions block to lean_action_ci.yml.**
   - Add a top-level `permissions:` block that restricts to minimum required permissions (typically `contents: read`).
   - Match the pattern already used in `platform_security_baseline.yml`.

4. **F-17 — Document O(n) data structure design decision.**
   - Add a design note (in the project spec or as an ADR) explaining that list-based O(n) lookups are an intentional choice for the abstract formal model.
   - Justify: the formalization prioritizes semantic clarity and proof tractability over algorithmic complexity. Real-kernel-scale performance is out of scope for the abstract model.
   - Note that a future hardware-targeted slice may introduce `HashMap`/`RBMap` for performance-critical paths.

**Code targets**

- `.github/workflows/lean_action_ci.yml`
- `.github/workflows/lean_toolchain_update_proposal.yml`
- `.github/workflows/nightly_determinism.yml`
- `.github/workflows/platform_security_baseline.yml`
- `docs/spec/SELE4N_SPEC.md` (or new ADR)

**Validation gates**

- `./scripts/test_fast.sh`
- `./scripts/test_docs_sync.sh`

**Acceptance criteria**

- All GitHub Actions use SHA-pinned versions with tag comments.
- `lean_action_ci.yml` has an explicit `permissions:` block.
- O(n) design decision is documented with rationale and future migration path.
- F-13 verified as already resolved.

**Dependencies:** None (independent of all other workstreams).

## 6) Milestone gates

- **Gate G0 (planning readiness):** this file + README + spec + GitBook all reference `AUDIT_v0.11.0` as active baseline; WS-C portfolio demoted to historical.
- **Gate G1 (test validity):** WS-D1 merged with passing Tier 0-3. No silent error suppression, no tautological assertions.
- **Gate G2 (security assurance):** WS-D2 merged. Information-flow policy enforced in at least three kernel operations. At least three additional non-interference theorems.
- **Gate G3 (proof and design maturity):** WS-D3 + WS-D4 merged. Badge safety proved. VSpace round-trip theorems closed. Kernel design hardened against cycles and double-waits.
- **Gate G4 (infrastructure closure):** WS-D5 + WS-D6 merged. All 17 findings closed or formally deferred with documented rationale.

## 7) Workstream template (apply to each WS-D*)

Each workstream PR must include:

1. **Audit mapping:** exact finding IDs (F-xx) closed.
2. **Code diff summary:** semantic changes and failure-mode behavior.
3. **Proof delta:** new/changed theorems and assumptions.
4. **Test evidence:** command outputs from relevant tier scripts.
5. **Doc sync:** updates to root docs + GitBook mirrors.
6. **Deferred items:** explicit carry-forward list with destination.

## 8) Current status dashboard

| Workstream | Status | Priority | Findings | Notes |
|---|---|---|---|---|
| WS-D1 | **Completed** | Critical/High | F-01, F-03, F-04 | Test error handling and validity restoration. Gate G1 passed: Tier 0-3 clean. |
| WS-D2 | **Completed** | High | F-02, F-05 | Information-flow enforcement and non-interference proof expansion. Gate G2 passed: enforcement in 3 operations, 4 additional non-interference theorems. |
| WS-D3 | **Completed** | Medium | F-06, F-08, F-16 | Proof gap closure (badge safety, VSpace preservation, proof documentation). TPI-001 closed. Gate G3 (proof) passed. |
| WS-D4 | **Completed** | Medium | F-07, F-11, F-12 | Kernel design hardening (cycles, failure semantics, double-wait). TPI-D06 closed. TPI-D07 closed (Risk 0 resolved: declarative acyclicity with Layers 0-4; sole deferred `sorry` on BFS bridge TPI-D07-BRIDGE). |
| WS-D5 | Planned | Medium | F-09, F-10 | Test infrastructure expansion (fixtures, ID bounds). |
| WS-D6 | Planned | Low | F-13, F-14, F-15, F-17 | CI/CD polish and documentation governance. F-13 likely already resolved. |

## 9) Dependency graph

```
Phase P0 (done)        Phase P1 (done)  Phase P2 (done)  Phase P3 (done)       Phase P4 (next)
───────────────        ────────         ────────         ──────────            ────────
Baseline transition → WS-D1 ─────────→ WS-D2 ─────────→ WS-D3 ──────────────→ WS-D5
                      (completed)       (completed)      WS-D4 (parallel) ────→ WS-D6
                                        │                  ↑
                                        └──────────────────┘
```

- WS-D1 is the prerequisite for WS-D2, WS-D4, and WS-D5 (test foundation must be sound).
- WS-D2 requires WS-D1 (enforcement hooks need working test suites for validation).
- WS-D3 is independent (proof work has no test-suite dependency).
- WS-D4 requires WS-D1 (negative-state tests validate rejection paths).
- WS-D5 requires WS-D1 (expanded test infrastructure must build on sound foundation).
- WS-D6 is independent.

## 10) Canonical companion documents

- Findings source: [`AUDIT_v0.11.0.md`](./AUDIT_v0.11.0.md)
- Tracked proof obligations: [`AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`](./AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md)
- Prior completed portfolio (WS-C): [`docs/dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md)
- Documentation synchronization policy: [`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](../DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md)
- Claim/evidence audit index: [`docs/CLAIM_EVIDENCE_INDEX.md`](../CLAIM_EVIDENCE_INDEX.md)
