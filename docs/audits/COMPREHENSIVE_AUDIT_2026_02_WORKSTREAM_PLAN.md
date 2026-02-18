# Comprehensive Audit 2026-02 — Workstream Planning Backbone

This document is the execution-planning companion to
[`COMPREHENSIVE_AUDIT_2026_02.md`](./COMPREHENSIVE_AUDIT_2026_02.md).

It is intentionally operational: it turns the audit recommendations into
an ordered portfolio of workstreams with dependencies, measurable evidence gates,
and backlog-ready implementation slices.

## 1) Planning objective

Plan and execute workstreams that close **all recommendations and criticisms** from the 2026-02 comprehensive audit, while preserving:

1. proof completeness and invariant discipline,
2. deterministic CI and trace reproducibility,
3. contributor usability of docs and GitBook,
4. readiness for Raspberry Pi 5 hardware-binding milestones.

## 2) Canonical planning rules

See also the documentation/test synchronization index: [`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](../DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md).

- Treat [`docs/SEL4_SPEC.md`](../SEL4_SPEC.md) as normative scope/acceptance source.
- Treat this file as the **portfolio planner** and each workstream as execution slices.
- Keep root docs concise and link-forward to canonical pages (avoid duplicated long-form policy text).
- Every workstream PR must include: recommendation IDs closed, test/proof evidence, and doc synchronization.
- Any workstream status change must update: this file, root README active-slice text, and GitBook chapter 24.

## 3) Recommendation-to-workstream matrix

| Priority | Workstream ID | Recommendation coverage (from comprehensive audit) | Primary outputs |
|---|---|---|---|
| High | WS-B1: VSpace + memory model foundation | Architecture §2.3 #3; Priority #1 | VSpace object model, page-table semantics skeleton, bounded memory abstraction ADR |
| High | WS-B2: Generative + negative testing expansion | Testing §4.3 #1/#2/#4/#5; Priority #2/#5 | subsystem probes, malformed-state tests, bootstrap state builder DSL |
| High | WS-B3: Main trace harness refactor | Code Quality §3.3 #1/#2/#3; Priority #3 | extracted scenario functions, list-based bootstrap builder, assertive error checks |
| High | WS-B4: Remaining type wrapper migration | Architecture §2.3 #1; Priority #4 | wrappers for DomainId/Priority/Irq/Badge/ASID/VAddr/PAddr + migration notes |
| Medium | WS-B5: CSpace semantics completion | Architecture §2.3 #4; Priority #6 | CNode guard/radix resolution path and tests |
| Medium | WS-B6: IPC completeness with notifications | Architecture §2.2 gap (notification objects); Priority #7 | Notification object model + invariant updates |
| Medium | WS-B7: Information-flow proof track start | Priority #8 | IF-M1 formal milestone package and proof decomposition plan |
| Medium | WS-B8: Documentation automation + consolidation | Docs §5.3 #1/#2/#4; Priority #9/#13 | doc-gen4 integration, markdown-link checks, dedup map root↔GitBook |
| Medium | WS-B9: Threat model and security hardening | Security recommendations + Priority #10/#11/#12 | THREAT_MODEL.md, .gitignore expansion, setup script checksum verification |
| Low | WS-B10: CI maturity upgrades | CI §7.3 #1/#2/#3/#4/#5; Priority #14/#15/#17 | CodeQL policy decision, toolchain update automation, timing/flake telemetry |
| Low | WS-B11: Scenario framework finalization | Docs §5.3 #5; Priority #16 | populate `tests/scenarios/` or retire with explicit replacement |

## 4) Dependency and sequencing model

### Phase P1 — correctness foundation

- WS-B4 (type wrappers)
- WS-B3 (main harness refactor)
- WS-B8 (doc governance + dedup rules)

Rationale: stabilize API and documentation shape before deep semantic expansion.

### Phase P2 — model and test depth

- WS-B1 (VSpace/memory) ✅ completed
- WS-B5 (CSpace guard/radix)
- WS-B6 (notifications)
- WS-B2 (generative + negative testing) ✅ completed

Rationale: close architecture gaps and immediately broaden tests around each new semantic surface.

### Phase P3 — assurance and operational maturity

- WS-B7 (information flow)
- WS-B9 (threat model/security baseline)
- WS-B10 (CI maturity)
- WS-B11 (scenario framework completion)

Rationale: convert expanded model coverage into long-term assurance and delivery reliability.

## 5) Detailed workstream execution contracts

Status key: `Planned` → `In Progress` → `Completed`.
Current portfolio status: **WS-B1, WS-B2, WS-B3, WS-B4, WS-B5, WS-B6, WS-B7, and WS-B8 are Completed**; WS-B9..WS-B11 remain Planned/In Progress per active execution cadence.

### WS-B1 — VSpace + memory model foundation (Completed)

- **Goal:** formalize minimal but extensible virtual-memory semantics for page tables, ASID binding, and bounded memory access assumptions.
- **Prerequisites:** WS-B4 wrapper migration complete for `ASID`, `VAddr`, `PAddr`.
- **Implementation slices:**
  1. Add object/data structures for page tables and address-space roots.
  2. Add transition functions for map/unmap/lookups with explicit failure modes.
  3. Add invariants for non-overlap, root validity, and bounded address translation.
  4. Add architecture-assumption ADR documenting what remains abstract.
- **Evidence contract:**
  - `./scripts/test_smoke.sh`
  - `./scripts/test_full.sh`
  - new/updated invariant anchors in Tier 3 checks.
- **Exit criteria:** deterministic map/unmap trace coverage, invariant preservation lemmas merged, ADR published.
- **Closure evidence (2026-02-17):** `SeLe4n/Kernel/Architecture/VSpace*.lean` introduces map/unmap/lookup semantics + invariant bundle surface; `Main.lean` and `tests/fixtures/main_trace_smoke.expected` include map→lookup→unmap→fault trace anchors; ADR published at `docs/VSPACE_MEMORY_MODEL_ADR.md`.

### WS-B2 — Generative + negative testing expansion (Completed)

- **Goal:** expand fixture and stochastic tests to cover malformed states and edge-case transitions that should fail safely.
- **Prerequisites:** WS-B3 harness extraction to make scenario composition reusable.
- **Implementation slices:**
  1. Build reusable bootstrap-state builder DSL for test scenarios.
  2. Add malformed-capability and malformed-object negative tests.
  3. Add seeded generative probes for scheduler/IPC/capability composition.
  4. Persist replay artifacts for nightly determinism and failure triage.
- **Evidence contract:**
  - `./scripts/test_smoke.sh`
  - `./scripts/test_full.sh`
  - `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh`
- **Exit criteria:** negative-path suite lands with deterministic seeds and documented replay procedure.
- **Closure evidence (2026-02-17):** `SeLe4n/Testing/StateBuilder.lean` introduces a reusable bootstrap-state builder DSL; `tests/NegativeStateSuite.lean` and `scripts/test_tier2_negative.sh` add malformed-state and negative-path assertions in required smoke/full gates; `scripts/test_tier4_nightly_candidates.sh` now persists seeded `trace_sequence_probe` logs plus `trace_sequence_probe_manifest.csv` for deterministic replay triage.

### WS-B3 — Main trace harness refactor (Completed)

- **Goal:** reduce `Main.lean` orchestration complexity and make scenario construction composable and auditable.
- **Prerequisites:** none (can start immediately).
- **Implementation slices:**
  1. Extract scenario constructors into dedicated helper functions/modules.
  2. Replace ad hoc bootstrap construction with list- and builder-based composition.
  3. Add explicit error assertions at each transition boundary.
  4. Keep fixture trace output stable or intentionally versioned.
- **Evidence contract:**
  - `./scripts/test_tier2_trace.sh`
  - `./scripts/test_full.sh`
- **Exit criteria:** harness decomposition merged with no trace-regression drift and clearer failure localization.
- **Closure evidence (2026-02-17):** `Main.lean` now delegates execution to `SeLe4n/Testing/MainTraceHarness.lean`, which extracts trace orchestration into dedicated harness functions (`runCapabilityAndArchitectureTrace`, `runServiceAndStressTrace`, `runLifecycleAndEndpointTrace`); bootstrap construction is now list/builder-based through `SeLe4n/Testing/StateBuilder.lean`; Tier 2 fixture output remains stable (`tests/fixtures/main_trace_smoke.expected`) with `scripts/test_tier2_trace.sh` and `scripts/test_full.sh` passing against the refactored harness.

### WS-B4 — Remaining type wrapper migration (Completed)

- **Goal:** complete wrapper-typed domain separation across remaining scalar aliases.
- **Prerequisites:** none (P1 starter).
- **Implementation slices:**
  1. Introduce wrappers for `DomainId`, `Priority`, `Irq`, `Badge`, `ASID`, `VAddr`, `PAddr`.
  2. Update APIs/proofs at object-store boundaries to use explicit conversions.
  3. Add guard checks preventing regression to implicit coercions.
  4. Document migration notes and compatibility helpers.
- **Evidence contract:**
  - `./scripts/test_fast.sh`
  - `./scripts/test_full.sh`
- **Exit criteria:** no remaining raw alias usage in target surfaces; invariant layer compiles without coercion shortcuts.
- **Closure evidence (2026-02-18):** `SeLe4n/Prelude.lean` now upgrades `DomainId`, `Priority`, `Irq`, `Badge`, `ASID`, `VAddr`, and `PAddr` from `Nat` aliases to wrapper structures with `ofNat`/`toNat` helpers and explicit `ToString`/`OfNat` compatibility instances; `scripts/test_tier0_hygiene.sh` now fails if any of these regress to `abbrev ... := Nat`; full validation gates pass under `scripts/test_fast.sh` and `scripts/test_full.sh`.

### WS-B5 — CSpace semantics completion (Completed)

- **Goal:** model guard/radix-based CNode traversal and resolution outcomes with clear error branches.
- **Prerequisites:** WS-B4 wrapper migration for capability pointers/slots stability.
- **Implementation slices:**
  1. Add CNode guard/radix fields and traversal helper semantics.
  2. Implement lookup semantics with depth/guard mismatch failures.
  3. Add preservation lemmas for capability and scheduler invariants.
  4. Add trace scenarios that exercise deep and malformed CSpace paths.
- **Evidence contract:**
  - `./scripts/test_smoke.sh`
  - `./scripts/test_full.sh`
- **Exit criteria:** CSpace resolution behavior is executable, tested, and invariant-preserving.
- **Closure evidence (2026-02-18):** `SeLe4n/Model/Object.lean` now defines executable guard/radix `CNode.resolveSlot` semantics with explicit depth/guard/slot failure taxonomy; `SeLe4n/Kernel/Capability/Operations.lean` adds `CSpacePathAddr` plus `cspaceResolvePath`/`cspaceLookupPath` so pointer-path traversal is modeled separately from direct slot lookup; `tests/NegativeStateSuite.lean` adds path-resolution positive/negative checks for depth mismatch and guard mismatch failures under `scripts/test_tier2_negative.sh`; `tests/fixtures/main_trace_smoke.expected` now anchors source/deep-path guard-radix trace outputs via `scripts/test_tier2_trace.sh`; full validation gates (`scripts/test_smoke.sh`, `scripts/test_full.sh`) pass with the completed semantics.

### WS-B6 — IPC completeness with notifications (Completed)

- **Goal:** add notification-object semantics so IPC model covers endpoint + notification split.
- **Prerequisites:** WS-B3 refactor (for cleaner scenario wiring).
- **Implementation slices:**
  1. Introduce notification object/state definitions.
  2. Implement signal/wait semantics and scheduler interactions.
  3. Extend IPC invariants to include notification safety properties.
  4. Add traces proving endpoint and notification paths compose correctly.
- **Evidence contract:**
  - `./scripts/test_smoke.sh`
  - `./scripts/test_full.sh`
- **Exit criteria:** notification semantics integrated through API, proofs, and trace fixtures.
- **Closure evidence (2026-02-18):** `SeLe4n/Model/Object.lean` now includes `NotificationState`/`Notification` plus `KernelObject.notification` and `ThreadIpcState.blockedOnNotification`; `SeLe4n/Kernel/IPC/Operations.lean` adds executable `notificationSignal` and `notificationWait` semantics with runnable-queue interactions (block on wait, wake on signal); `SeLe4n/Kernel/IPC/Invariant.lean` extends the IPC invariant surface with `notificationQueueWellFormed`/`notificationInvariant` and global endpoint+notification coverage; `tests/NegativeStateSuite.lean` adds notification negative/positive checks; and `SeLe4n/Testing/MainTraceHarness.lean` + `tests/fixtures/main_trace_smoke.expected` now exercise composed endpoint/notification trace paths under `scripts/test_smoke.sh` and `scripts/test_full.sh`.

### WS-B7 — Information-flow proof track start (Completed)

- **Goal:** land IF-M1 formal baseline and decomposition plan for noninterference progression.
- **Prerequisites:** WS-B1 and WS-B5 completion (state model and CSpace semantics available). ✅ satisfied
- **Implementation slices:**
  1. Define confidentiality/integrity labels and state projection helpers.
  2. Publish IF-M1 theorem targets and assumptions ledger.
  3. Add milestone document updates in roadmap + GitBook.
  4. Add Tier 3 anchors for IF milestone artifacts.
- **Evidence contract:**
  - `./scripts/test_full.sh`
  - `rg -n "IF-M1|information-flow" docs/INFORMATION_FLOW_ROADMAP.md docs/gitbook/12-proof-and-invariant-map.md`
- **Exit criteria:** IF-M1 package merged with explicit theorem backlog and assumptions.
- **Closure evidence (2026-02-18):** IF-M1 formal primitives are now implemented in `SeLe4n/Kernel/InformationFlow/Policy.lean` (`SecurityLabel`, `securityFlowsTo`, reflexive/transitive policy lemmas) and `SeLe4n/Kernel/InformationFlow/Projection.lean` (`projectState`, `lowEquivalent`, equivalence-style helper lemmas); theorem targets and assumptions ledger are published in `docs/IF_M1_BASELINE_PACKAGE.md`; milestone roadmap + GitBook proof map are synchronized in `docs/INFORMATION_FLOW_ROADMAP.md` and `docs/gitbook/12-proof-and-invariant-map.md`; Tier 2 negative coverage now includes `tests/InformationFlowSuite.lean` via `lake exe information_flow_suite` in `scripts/test_tier2_negative.sh`; Tier 3 anchors enforce IF-M1 entrypoint/doc presence via `scripts/test_tier3_invariant_surface.sh`; and full validation gates (`scripts/test_fast.sh`, `scripts/test_smoke.sh`, `scripts/test_full.sh`, `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh`, `lake build`) pass with WS-B7 integrated.

### WS-B8 — Documentation automation + consolidation (Completed)

- **Goal:** reduce documentation drift through generated indexes and enforceable sync checks.
- **Prerequisites:** none (cross-cutting P1 stream).
- **Implementation slices:**
  1. Integrate doc-gen step for canonical navigation pages.
  2. Add markdown-link validation in CI/test scripts.
  3. Publish deduplication map for root docs vs GitBook mirrors.
  4. Enforce sync checklist updates in planning PR templates.
- **Evidence contract:**
  - `./scripts/test_smoke.sh`
  - `./scripts/test_full.sh`
  - targeted link/reference scans with `rg -n`.
- **Exit criteria:** reproducible doc synchronization workflow with automated guardrails.
- **Closure evidence (2026-02-18):** `scripts/generate_doc_navigation.py` now generates canonical GitBook navigation pages (`docs/gitbook/README.md`, `docs/gitbook/SUMMARY.md`) from `docs/gitbook/navigation_manifest.json`; markdown-link automation is enforced by `scripts/check_markdown_links.py` and `scripts/test_docs_sync.sh`, wired into Tier 0 via `scripts/test_tier0_hygiene.sh` and into CI via the new `Docs Automation / Navigation + Links + DocGen Probe` lane in `.github/workflows/lean_action_ci.yml`; dedup governance is published in `docs/DOCS_DEDUPLICATION_MAP.md` with GitBook mirror `docs/gitbook/27-documentation-deduplication-map.md`; and planning PR checklist enforcement is codified in `.github/pull_request_template.md`.

### WS-B9 — Threat model and security hardening (Planned)

- **Goal:** formalize threat assumptions and tighten baseline supply-chain/security controls.
- **Prerequisites:** none (can overlap P2/P3).
- **Implementation slices:**
  1. Add canonical `docs/THREAT_MODEL.md` (assets, actors, trust boundaries).
  2. Expand `.gitignore` and secret-scanning posture for generated artifacts.
  3. Add checksum/signature verification for setup/bootstrap scripts.
  4. Sync CI policy and security workflows with documented decisions.
- **Evidence contract:**
  - `./scripts/test_fast.sh`
  - `./scripts/test_full.sh`
  - security workflow checks in CI policy anchors.
- **Exit criteria:** threat model and hardening controls documented, testable, and linked from roadmap.

### WS-B10 — CI maturity upgrades (Planned)

- **Goal:** improve CI observability, policy clarity, and update cadence without destabilizing required gates.
- **Prerequisites:** WS-B8 doc governance hooks available.
- **Implementation slices:**
  1. Decide and document CodeQL required-vs-informational policy.
  2. Add automated Lean/toolchain update proposal flow.
  3. Publish CI timing baselines and flake telemetry collection.
  4. Ensure branch-protection documentation matches workflow reality.
- **Evidence contract:**
  - `./scripts/test_full.sh`
  - `./scripts/test_nightly.sh`
- **Exit criteria:** CI governance decisions are codified with measurable reliability baselines.

### WS-B11 — Scenario framework finalization (Planned)

- **Goal:** resolve `tests/scenarios/` into an active framework or retire it with explicit replacement.
- **Prerequisites:** WS-B2 scenario DSL and negative test assets.
- **Implementation slices:**
  1. Define scenario metadata schema (risk tags, subsystem, determinism seed).
  2. Populate representative scenario sets or deprecate with migration notes.
  3. Link scenario framework into nightly replay and docs.
  4. Add ownership and maintenance expectations.
- **Evidence contract:**
  - `./scripts/test_smoke.sh`
  - `./scripts/test_nightly.sh`
- **Exit criteria:** scenario strategy is explicit, exercised, and maintainable.

## 6) Portfolio-level readiness and release gates

### Gate G0 — Execution kickoff readiness (current target)

Required before declaring kickoff-ready:

1. WS-B backlog tickets created with owners, milestones, and recommendation IDs.
2. Phase sequence and dependencies reviewed in weekly planning cadence.
3. Documentation/GitBook sync contract confirmed (`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`).
4. Baseline quality gates pass (`test_smoke`, `test_full`, `test_nightly`).

### Gate G1 — Hardware-entry readiness

First hardware-facing entry gate remains:

- `WS-B1 + WS-B2 + WS-B5` complete ✅,
- Tier 4 nightly determinism signal stable,
- architecture assumptions and risk log updated.

## 7) Workstream-ready planning template

For each WS-B* planning ticket, require this minimum structure:

1. **Problem statement** (quoted audit criticism/recommendation IDs)
2. **In-scope/out-of-scope**
3. **Architecture/proof impact**
4. **Implementation tasks** (ordered)
5. **Evidence contract**
   - required Lean/test commands,
   - expected artifacts,
   - required docs updated.
6. **Exit criteria**
7. **Rollback/safety notes**

## 8) Documentation and GitBook organization contract

To keep docs maintainable while scaling workstreams:

- Root `README.md` should remain a short navigation hub.
- `docs/audits/*` should hold canonical audit and planning source artifacts.
- GitBook chapters should summarize and point to canonical docs rather than duplicating full policy text.
- Any planning status table should appear in one canonical file and be linked elsewhere.

## 9) Immediate next planning actions

1. Create WS-B1..WS-B11 issue backlog with owners and milestone tags.
2. Start Phase P1 with WS-B4 + WS-B3 in parallel and WS-B8 as cross-cutting governance.
3. Add a recurring planning review cadence (weekly) that updates only this file and milestone notes.
4. Validate Gate G0 and then mark this portfolio as `Kickoff Ready`.
