## [0.11.9] - 2026-02-25

### WS-E3 Kernel semantic hardening (completed)
- **H-06:** Added `threadCount_bounded_after_setDomain` invariant proving `setDomain` preserves the runnable queue length bound.
- **H-07:** Added `capMint_preserves_object_store` invariant proving capability minting does not modify the object store.
- **H-08:** Added `capRevoke_siblings_unreachable` invariant proving sibling capabilities become unreachable after revocation.
- **H-09:** Replaced `sorry` in `endpointSend_preserves_lowEquivalent` with a complete, machine-checked proof. The proof uses projection-preservation: each execution independently preserves the observer's view via a `chain_preserves_projection` lemma covering the storeObject → storeTcbIpcState → scheduler-op chain. Requires label coherence (`hLabelCoherent`) and endpoint confinement (`hRecvConf`) hypotheses.
- **M-09:** Added `endpointSend_preserves_scheduler_invariant` proving endpoint send preserves the scheduler queue/current-thread consistency invariant.
- **L-06:** Added `retypeObjects_preserves_scheduler` invariant proving `retypeObjects` does not modify scheduler state.
- All 6 WS-E3 findings resolved. Zero `sorry` remains in the codebase.
- Bumped patch version to **`0.11.9`**.

## [0.11.7] - 2026-02-24

### WS-E1 Test infrastructure and CI hardening (completed)
- **F-14:** SHA-pinned all GitHub Actions across 4 workflow files (`lean_action_ci`, `nightly_determinism`, `lean_toolchain_update_proposal`, `platform_security_baseline`) to full 40-character commit hashes with version comments.
- **M-10:** Added parameterized test topologies in `MainTraceHarness.lean` — 3 configurations (minimal/medium/large) varying thread count, priority, CNode radix, and ASID count, exercised during `lake exe sele4n`.
- **M-11:** Added 5 runtime invariant check families to `InvariantChecks.lean`: CSpace slot coherency, capability rights structure, lifecycle metadata consistency, service graph acyclicity (BFS-based), and VSpace ASID uniqueness.
- **L-07:** Converted `main_trace_smoke.expected` fixture to structured `scenario_id | risk_class | expected_fragment` format. Backward-compatible with existing substring matching in `test_tier2_trace.sh`.
- **L-08:** Added theorem-body spot-check validation to `test_tier0_hygiene.sh` (verifies no `sorry` in invariant proof surface) and F-14 SHA-pin regression guard.
- Updated Tier 3 invariant surface script with WS-E1 anchor checks for new check families, topology builders, structured fixture format, and hygiene additions.
- Updated all canonical documentation surfaces: workstream plan, README, SELE4N_SPEC, DEVELOPMENT.md, CI_POLICY.md, GitBook chapters (07, 24, README).

### Lean toolchain upgrade (WS-B10, closes #182)
- Bumped Lean toolchain from `leanprover/lean4:v4.27.0` to `leanprover/lean4:v4.28.0` in `lean-toolchain`.
- Updated Lean version badge in `README.md`, toolchain reference in `CLAUDE.md`, and package version in `docs/spec/SELE4N_SPEC.md`.
- Bumped patch version to **`0.11.7`**.

## [0.11.6] - 2026-02-22

### Documentation optimization and context-pressure reduction
- Added `CLAUDE.md` with focused project guidance: build commands, source layout, key conventions, documentation rules, active workstream context, and PR checklist. Provides a concise onboarding surface that avoids requiring full documentation traversal.
- Added `--quiet`/`-q` flag to `scripts/setup_lean_env.sh` to suppress informational output during automated runs while preserving error messages. SessionStart hook updated to use `--quiet`.
- Fixed stale workstream status in `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`: WS-D4 now correctly listed as completed.
- Fixed stale canonical source reference in `docs/DOCS_DEDUPLICATION_MAP.md`: "Current execution workstreams" row now points to the active `AUDIT_v0.11.0_WORKSTREAM_PLAN.md` instead of the historical `AUDIT_v0.9.32` plan.
- Tightened `CONTRIBUTING.md` to remove redundant prose and consolidate validation guidance.
- Bumped patch version to **`0.11.6`**.

## [0.11.5] - 2026-02-22

### Build environment hardening
- Fixed `scripts/setup_lean_env.sh` to work in proxy-restricted environments (e.g. Claude Code web sessions behind an egress gateway). The setup script now falls back to a manual `curl`-based download of the elan binary and Lean toolchain when elan's internal HTTP client cannot negotiate CONNECT tunnels through an egress proxy.
- Made `shellcheck` and `ripgrep` installation non-fatal in `setup_lean_env.sh`; both tools are optional for building and their absence is already handled gracefully by `test_tier0_hygiene.sh` fallback paths.
- Made `apt_update_once` tolerant of complete apt repository unavailability so the script continues to elan/lean installation instead of aborting.
- Added `.claude/settings.json` with a `SessionStart` hook that automatically runs `setup_lean_env.sh --build` on new Claude Code sessions, ensuring the Lean environment is provisioned and built without manual intervention.
- Bumped patch version to **`0.11.5`**.

## [0.11.3] - 2026-02-21

### WS-D3 proof gap closure (F-06, F-08, F-16)
- **F-06 (Badge-override safety):** Added three badge-safety theorems to `SeLe4n/Kernel/Capability/Invariant.lean`: `mintDerivedCap_rights_attenuated_with_badge_override` (rights attenuation holds regardless of badge), `mintDerivedCap_target_preserved_with_badge_override` (target identity preserved regardless of badge), and `cspaceMint_badge_override_safe` (composed kernel-operation-level proof that badge override cannot escalate privilege). TPI-D04 closed.
- **F-08 (VSpace success preservation):** Added `vspaceMapPage_success_preserves_vspaceInvariantBundle` and `vspaceUnmapPage_success_preserves_vspaceInvariantBundle` to `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`. Supporting infrastructure: `resolveAsidRoot_some_implies`, `resolveAsidRoot_of_unique_root`, `storeObject_objectIndex_eq_of_mem`, and `vspaceAsidRootsUnique` moved to `VSpace.lean`; seven VSpaceRoot helper theorems added to `Model/Object.lean` (`mapPage_asid_eq`, `unmapPage_asid_eq`, `lookup_eq_none_not_mem`, `mapPage_noVirtualOverlap`, `unmapPage_noVirtualOverlap`, `lookup_mapPage_ne`, `lookup_unmapPage_ne`). TPI-D05 closed.
- **TPI-001 (VSpace round-trip theorems):** Four round-trip theorems proved in `VSpaceInvariant.lean`: `vspaceLookup_after_map`, `vspaceLookup_map_other`, `vspaceLookup_after_unmap`, `vspaceLookup_unmap_other`. All proved without `sorry`. TPI-001 obligation from WS-C fully discharged.
- **F-16 (Proof classification docstrings):** Added module-level `/-! ... -/` docstrings to all seven `Invariant.lean` files (Scheduler, IPC, Capability, Lifecycle, InformationFlow, Service, Architecture) and `VSpaceInvariant.lean`, classifying every theorem as substantive, error-case (trivially true), non-interference, badge-safety, structural/bridge, or round-trip.
- Updated Tier-3 invariant surface script with 20 new anchor checks for WS-D3 theorem symbols and docstring presence.
- Updated all canonical planning docs, tracked proof issues, claim-evidence index, development guide, spec, GitBook chapters (12, 32), and documentation sync matrix to reflect WS-D3 completion.
- Bumped patch version to **`0.11.3`**.

## [0.11.1] - 2026-02-19

### WS-D2 information-flow enforcement and proof completion
- Implemented policy-checked kernel operation wrappers in `SeLe4n/Kernel/InformationFlow/Enforcement.lean`: `endpointSendChecked`, `cspaceMintChecked`, `serviceRestartChecked` (F-02), with correctness theorems for allowed/denied cases and reflexive self-domain flow.
- Extended non-interference proof surface in `SeLe4n/Kernel/InformationFlow/Invariant.lean` with five transition-level theorems (F-05): `chooseThread_preserves_lowEquivalent` (TPI-D01), `cspaceMint_preserves_lowEquivalent`, `cspaceRevoke_preserves_lowEquivalent` (TPI-D02), `lifecycleRetypeObject_preserves_lowEquivalent` (TPI-D03), plus shared `storeObject_at_unobservable_preserves_lowEquivalent` infrastructure.
- Added `flowDenied` error variant to `KernelError` and preservation helper lemmas to `Model/State.lean` and `Capability/Operations.lean` supporting the new proof decompositions.
- Extended `tests/InformationFlowSuite.lean` with 4 enforcement boundary tests covering same-domain pass-through and cross-domain flow denial for `endpointSendChecked` and `cspaceMintChecked`.
- Closed proof obligations TPI-D01, TPI-D02, TPI-D03; marked WS-D2 and Phase P2 as completed across all canonical planning, spec, and GitBook documentation.
- Bumped patch version to **`0.11.1`**.

## [0.11.0] - 2026-02-19

### WS-C8 post-merge audit refinement and minor release
- Performed an end-to-end documentation/codebase synchronization audit after WS-C8 completion and corrected residual status drift in the seLe4n spec (`WS-C portfolio` summary now consistently states WS-C1..WS-C8 completed).
- Refined carried-forward proof-issue tracker wording to reflect that WS-C execution is complete and obligations remain intentionally tracked post-closeout.
- Revalidated docs automation + smoke/full/nightly experimental gates to confirm runtime, proof-surface, and documentation anchors are synchronized.
- Bumped minor version to **`0.11.0`** and synchronized version markers in root/spec metadata.

## [0.10.8] - 2026-02-19

### WS-C8 documentation and GitBook consolidation completion
- Marked WS-C8 as completed across canonical planning docs, root guides, and GitBook mirrors so active portfolio status is consistently closed (WS-C1..WS-C8 complete).
- Added a canonical claim/evidence audit index (`docs/CLAIM_EVIDENCE_INDEX.md`) plus a GitBook pointer chapter (`docs/gitbook/31-claim-vs-evidence-index.md`).
- Refreshed documentation ownership/synchronization matrices and planning companion links to include the new claim/evidence index.
- Bumped patch version to **`0.10.8`** and synchronized version markers.

## [0.10.7] - 2026-02-19

### Documentation correctness and WS-C7 refinement follow-up
- Audited and corrected remaining ADR/GitBook drift where WS-B1 material still implied bounded ASID discovery is current behavior.
- Amended VSpace ADR + GitBook mirror to explicitly record WS-C7 superseding the bounded scan with `SystemState.objectIndex` traversal in `resolveAsidRoot`.
- Synchronized root/spec version markers to **`0.10.7`**.
- Re-ran docs sync + full + nightly experimental validation to confirm end-to-end consistency.

## [0.10.6] - 2026-02-19

### Added
- Added WS-C7 architecture decision record for finite object-store migration staging and compatibility notes (`docs/FINITE_OBJECT_STORE_ADR.md`) with a synced GitBook completion chapter.

### Changed
- Migrated `ServiceId` from a `Nat` alias to a typed wrapper in `SeLe4n/Prelude.lean` to restore identifier-domain separation.
- Added finite `objectIndex` tracking to `SystemState` and `BootstrapBuilder`, and rewired VSpace ASID-root resolution to use indexed object discovery instead of bounded range scanning.
- Consolidated shared store-object helper lemmas into `Model/State.lean` and reused them from lifecycle invariant helpers.
- Updated active portfolio docs/GitBook to mark WS-C7 completed.
- Bumped patch version to **`0.10.6`** and synchronized version markers.

## [0.10.5] - 2026-02-19

### WS-C6 refinement follow-up: status precision + telemetry/doc anchor tightening
- Refined active-portfolio wording in root/spec docs so WS-C7 is explicitly marked as planned while WS-C8 remains in progress.
- Synchronized GitBook telemetry mirror wording to reflect nightly smoke flake probing defaulting to 3 attempts.
- Tightened Tier-3 documentation anchor check for `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md` to require the current WS-C baseline string instead of broad historical alternates.
- Re-ran Tier 0-4 validation (`test_full` + `test_nightly`) to confirm full-codebase/docs/gitbook consistency after refinement.
- Bumped patch version to **`0.10.5`** and synchronized version markers.

## [0.10.4] - 2026-02-19

### WS-C6 CI and supply-chain hardening completion
- Hardened GitHub Actions cache isolation in the primary Lean CI and nightly workflows by adding `runner.arch` to cache keys/restore prefixes.
- Added defensive Lean release-tag format validation in `.github/workflows/lean_toolchain_update_proposal.yml` before using upstream tags in issue-search/query logic.
- Strengthened flake telemetry defaults by updating `scripts/ci_flake_probe.sh` to default to 3 attempts (with optional explicit override) and wiring nightly to use the stronger default.
- Tightened Tier-0 hygiene marker scanning to word-boundary matching so incidental substrings no longer trigger false positives.
- Marked WS-C6 as completed across the active workstream dashboard plus development/spec/README/GitBook/matrix mirrors and synchronized Tier-3 documentation anchors.
- Bumped patch version to **`0.10.4`** and synchronized version markers.

## [0.10.3] - 2026-02-19

### WS-C5 information-flow assurance completion
- Added service-level visibility control to the IF labeling context (`serviceLabelOf`) and updated observer projection so service status is filtered by clearance policy instead of being globally visible.
- Added `SeLe4n.Kernel.InformationFlow.Invariant.endpointSend_preserves_lowEquivalent`, a nontrivial endpoint-send preservation theorem over `lowEquivalent` under hidden sender/endpoint assumptions.
- Extended IF regression checks in `tests/InformationFlowSuite.lean` to cover service-visibility filtering and an executable theorem witness for endpoint-send low-equivalence preservation.
- Marked WS-C5 as completed in the active workstream plan, tracked-proof obligations, development guide, root README, documentation sync matrix, and GitBook workstream status chapter.
- Bumped patch version to **`0.10.3`** and synchronized root version markers.

## [0.10.2] - 2026-02-19

### WS-C4 hardening follow-up: invariant precision and negative-fixture cleanup
- Refined invariant utility API with `stateInvariantChecksFor`/`assertStateInvariantsFor` so suites can validate exact fixture object inventories instead of relying only on a broad discovery window.
- Removed negative-suite `invariantView` masking and reworked the empty-send endpoint case into a dedicated malformed test state, preserving strict invariant checks for all success-path fixtures.
- Updated generative and trace harness callers to use explicit invariant object sets for stronger test validity guarantees and clearer intent.
- Re-ran smoke/full/tier4 candidate gates to confirm deterministic behavior and documentation/test synchronization after the hardening refactor.
- Bumped patch version to **`0.10.2`** and synchronized root version markers.

## [0.10.1] - 2026-02-19

### WS-C4 test validity hardening + workstream status sync
- Added executable invariant check utilities for scheduler + IPC validity and reusable state assertions used by runtime suites.
- Hardened negative and generative trace suites with post-success invariant assertions while preserving explicit invalid-fixture negative coverage.
- Added baseline invariant assertions at main trace harness entry points.
- Marked WS-C4 as completed across the active audit plan, root docs, and GitBook mirrors; synchronized Tier-3 documentation anchors accordingly.
- Bumped patch version to **`0.10.1`** and synchronized root version markers.

## [0.10.0] - 2026-02-18

### WS-C3 completion hardening + docs-sync reliability + portfolio synchronization
- Finalized WS-C3 proof-surface cleanup by removing tautological determinism theorems from VSpace and IF projection modules, while preserving tracked semantic obligations in TPI-001/TPI-002.
- Added module-level WS-C3 notes in affected Lean modules to clarify determinism-as-meta-property guidance and prevent future tautological theorem regressions.
- Hardened Tier 3 anchors to assert both removal of deprecated tautological theorems and presence of WS-C3 proof-surface notes, alongside synchronized active-slice status anchors.
- Improved docs-sync reliability in non-login shells by sourcing `${HOME}/.elan/env` when available before probing `lake`, reducing unnecessary setup churn and external mirror warnings when Lean is already installed.
- Synchronized root docs and GitBook status text to reflect WS-C3 completion and current P1 continuation focus on WS-C4.
- Bumped minor version to **`0.10.0`** and synchronized root version marker in `README.md`.

## [0.9.29] - 2026-02-18

### WS-B10 docs-sync offline/restricted-environment fallback fix
- Updated `scripts/test_docs_sync.sh` to treat `setup_lean_env.sh` as **best-effort** by default when `lake` is missing, so docs-sync still validates navigation/link consistency on offline or restricted environments where Lean setup cannot complete.
- Added explicit strict mode: `DOCS_SYNC_REQUIRE_LEAN_SETUP=1` now makes setup failure fatal for environments that require Lean setup enforcement during docs-sync.
- Kept existing explicit opt-out: `DOCS_SYNC_SKIP_LEAN_SETUP=1` skips Lean setup and doc-gen4 probing intentionally.
- Synchronized testing docs (`docs/TESTING_FRAMEWORK_PLAN.md`, `docs/gitbook/07-testing-and-ci.md`) to describe best-effort vs strict behavior.
- Bumped patch version to **`0.9.29`** and synchronized root version marker in `README.md`.

## [0.9.28] - 2026-02-18

### WS-B10 docs-sync reliability refinement
- Refined `scripts/test_docs_sync.sh` so it now auto-runs `scripts/setup_lean_env.sh` when `lake` is missing (unless `DOCS_SYNC_SKIP_LEAN_SETUP=1`), making docs-sync behavior more deterministic in pre-build environments.
- Kept doc-gen behavior explicit: navigation/link checks remain mandatory, while doc-gen4 remains optional when the executable is unavailable.
- Synchronized testing documentation language in `docs/TESTING_FRAMEWORK_PLAN.md` and GitBook chapter 07 to reflect docs-sync auto-setup semantics.
- Bumped patch version to **`0.9.28`** and synchronized root version marker in `README.md`.

## [0.9.27] - 2026-02-18

### WS-B10 CI maturity upgrades completion
- Completed WS-B10 by codifying CI governance in `docs/CI_POLICY.md`, including explicit CodeQL informational/non-blocking policy rationale, toolchain automation references, and telemetry artifact expectations.
- Added automated dependency/update cadence controls via `.github/dependabot.yml` (GitHub Actions updates) and `.github/workflows/lean_toolchain_update_proposal.yml` (weekly Lean release drift proposals as issues).
- Implemented CI timing and flake telemetry capture using `scripts/ci_capture_timing.sh` and `scripts/ci_flake_probe.sh`, wired into `.github/workflows/lean_action_ci.yml`, `.github/workflows/nightly_determinism.yml`, and `.github/workflows/platform_security_baseline.yml`.
- Published telemetry baseline documentation in `docs/CI_TELEMETRY_BASELINE.md` with GitBook mirror `docs/gitbook/29-ci-maturity-and-telemetry-baseline.md`, and synchronized active-slice/workstream completion status across README/spec/development/workstream-plan/GitBook docs.
- Bumped patch version to **`0.9.27`** and synchronized root version marker in `README.md`.

## [0.9.26] - 2026-02-18

### WS-B9 bootstrap reproducibility fix (immutable elan installer URL)
- Fixed `scripts/setup_lean_env.sh` to use a commit-pinned `ELAN_INSTALLER_URL` for `elan-init.sh` instead of the moving `master` branch URL.
- Kept `ELAN_INSTALLER_SHA256` aligned with the pinned commit artifact so fresh bootstrap remains reproducible and does not break when upstream `master` changes.
- Clarified the hardening anchor comment to require intentional paired updates of installer URL and checksum.
- Bumped patch version to **`0.9.26`** and synchronized root version marker in `README.md`.

## [0.9.25] - 2026-02-18

### WS-B9 post-audit documentation synchronization hardening
- Corrected documentation-sync baseline drift by updating `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md` to reflect WS-B9 completion in the active planning baseline summary.
- Updated GitBook chapter 25 (`docs/gitbook/25-documentation-sync-and-coverage-matrix.md`) to explicitly call out WS-B9 synchronization expectations.
- Extended Tier 3 anchor enforcement in `scripts/test_tier3_invariant_surface.sh` to require the updated documentation-sync baseline marker and added a targeted ShellCheck suppression (`SC2016`) for the literal regex line.
- Re-ran full validation gates (`test_fast`, `test_full`, default + experimental `test_nightly`) to verify end-to-end consistency.
- Bumped patch version to **`0.9.25`** and synchronized root version marker in `README.md`.

## [0.9.24] - 2026-02-18

### WS-B9 threat model and security hardening completion
- Published the canonical security baseline document at `docs/THREAT_MODEL.md` and added GitBook mirror chapter `docs/gitbook/28-threat-model-and-security-hardening.md`.
- Hardened bootstrap supply-chain behavior in `scripts/setup_lean_env.sh` by replacing remote `curl | sh` execution with temporary-file download + SHA-256 verification (`ELAN_INSTALLER_SHA256`) before installer execution.
- Expanded `.gitignore` to block common local secret/config files and scanner outputs from being committed.
- Synchronized active-slice/workstream status across README/spec/development/workstream-plan/GitBook pages to mark WS-B9 completed.
- Extended Tier 3 invariant/doc anchors to enforce WS-B9 security surfaces (threat model presence + setup checksum markers).
- Bumped patch version to **`0.9.24`** and synchronized root version marker in `README.md`.

## [0.9.23] - 2026-02-18

### WS-B8 post-review refinement and CI/doc-policy synchronization
- Refined CI branch-protection policy documentation (`docs/CI_POLICY.md`) so required checks now include `Docs Automation / Navigation + Links + DocGen Probe`, matching the live `lean_action_ci` workflow.
- Updated testing contract docs (`docs/TESTING_FRAMEWORK_PLAN.md`, `docs/gitbook/07-testing-and-ci.md`) to explicitly document Tier 0 docs-sync automation (`scripts/test_docs_sync.sh`) and its role in required CI coverage.
- Expanded Tier 3 doc anchors in `scripts/test_tier3_invariant_surface.sh` to enforce the new docs-automation required-check and testing-doc synchronization surfaces.
- Bumped patch version to **`0.9.23`** and synchronized root version marker in `README.md`.

## [0.9.22] - 2026-02-18

### WS-B8 documentation automation + consolidation completion
- Added deterministic documentation automation tooling: `scripts/generate_doc_navigation.py` (manifest-driven GitBook navigation generation), `scripts/check_markdown_links.py` (local markdown link validation), and `scripts/test_docs_sync.sh` (single docs-sync execution entrypoint).
- Added `docs/gitbook/navigation_manifest.json` as the single source for generated handbook navigation and regenerated `docs/gitbook/README.md` + `docs/gitbook/SUMMARY.md` from that manifest.
- Wired documentation automation into required validation surfaces by invoking `scripts/test_docs_sync.sh` from `scripts/test_tier0_hygiene.sh`, and by adding a `Docs Automation / Navigation + Links + DocGen Probe` CI lane in `.github/workflows/lean_action_ci.yml`.
- Published root↔GitBook dedup ownership guidance in `docs/DOCS_DEDUPLICATION_MAP.md` and GitBook chapter mirror `docs/gitbook/27-documentation-deduplication-map.md`.
- Added planning-doc synchronization checklist enforcement via `.github/pull_request_template.md` and synchronized active-slice/workstream status docs to mark WS-B8 completed.
- Bumped patch version to **`0.9.22`** and synchronized root version marker in `README.md`.

## [0.9.21] - 2026-02-18

### WS-B7 synchronization audit follow-up
- Corrected remaining GitBook planning drift for WS-B7 completion by updating chapter 24 Phase P2 status to include WS-B7 completion state.
- Extended Tier 3 doc anchors to enforce this chapter-24 Phase P2 synchronization in `scripts/test_tier3_invariant_surface.sh`, preventing regression in future doc updates.
- Re-ran full and nightly validation/audit lanes to confirm repository-wide determinism and documentation consistency remain intact.
- Bumped patch version to **`0.9.21`** and synchronized root version marker in `README.md`.

## [0.9.20] - 2026-02-18

### WS-B7 audit optimization and IF-M1 test-surface hardening
- Added executable IF-M1 runtime assertions in `tests/InformationFlowSuite.lean` and wired them into Tier 2 negative validation via `lake exe information_flow_suite` in `scripts/test_tier2_negative.sh`, strengthening regression coverage for label-flow and observer-projection behavior.
- Expanded Tier 3 invariant anchors to enforce the new IF runtime suite presence and Tier 2 wiring (`scripts/test_tier3_invariant_surface.sh`).
- Synchronized testing/docs/GitBook evidence for the strengthened WS-B7 validation surface (`docs/TESTING_FRAMEWORK_PLAN.md`, `docs/gitbook/07-testing-and-ci.md`, `docs/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md`, `docs/gitbook/24-comprehensive-audit-2026-workstream-planning.md`).
- Bumped patch version to **`0.9.20`** and synchronized root version marker in `README.md`.

## [0.9.19] - 2026-02-18

### WS-B7 information-flow proof-track start completion
- Implemented IF-M1 formal baseline modules in `SeLe4n/Kernel/InformationFlow/Policy.lean` and `SeLe4n/Kernel/InformationFlow/Projection.lean`, including security-label lattice primitives, flow-relation algebraic lemmas, observer projection helpers, and low-equivalence scaffolding.
- Wired information-flow modules into the aggregate kernel API (`SeLe4n/Kernel/API.lean`) and expanded Tier 3 invariant/doc anchors in `scripts/test_tier3_invariant_surface.sh` to continuously enforce IF-M1 surface and WS-B7 status synchronization.
- Published IF-M1 theorem targets + assumptions ledger in `docs/IF_M1_BASELINE_PACKAGE.md`, marked WS-B7 complete in canonical planning/spec/development/README/GitBook pages, and added WS-B7 closure evidence sections in planning mirrors.
- Bumped patch version to **`0.9.19`** and synchronized root version marker in `README.md`.

## [0.9.18] - 2026-02-18

### WS-B6 audit hardening follow-up
- Hardened Tier 3 documentation-synchronization guards in `scripts/test_tier3_invariant_surface.sh` so active-slice/phase-status wording for WS-B6 completion is continuously checked across README/spec/development guide/GitBook pages.
- Re-ran fast/full/nightly validation lanes to confirm no behavioral regressions and deterministic test stability under the tightened documentation anchors.
- Bumped patch version to **`0.9.18`** and synchronized root version marker in `README.md`.

## [0.9.17] - 2026-02-18

### WS-B6 post-merge synchronization audit
- Performed a full repository audit pass after WS-B6 merge and revalidated all quality tiers, including nightly default and nightly experimental determinism lanes.
- Fixed remaining documentation/GitBook status drift so WS-B6 completion is reflected consistently in:
  - `docs/gitbook/01-project-overview.md`,
  - `docs/gitbook/06-development-workflow.md`,
  - `docs/DEVELOPMENT.md`.
- Updated next-workstream guidance to point to WS-B7 as the next unfinished stream.
- Bumped patch version to **`0.9.17`** and synchronized the root version marker in `README.md`.

## [0.9.16] - 2026-02-18

### WS-B6 IPC completeness with notifications
- Added notification-object IPC model coverage in `SeLe4n/Model/Object.lean`: `NotificationState`, `Notification`, `KernelObject.notification`, `KernelObjectType.notification`, and `ThreadIpcState.blockedOnNotification`.
- Implemented executable notification transitions in `SeLe4n/Kernel/IPC/Operations.lean` with `notificationWait`/`notificationSignal` semantics and explicit scheduler runnable-queue interactions.
- Extended IPC invariant surfaces (`SeLe4n/Kernel/IPC/Invariant.lean`) so global `ipcInvariant` now covers both endpoint and notification object classes.
- Expanded regression evidence with notification paths in `SeLe4n/Testing/MainTraceHarness.lean`, `tests/NegativeStateSuite.lean`, and `tests/fixtures/main_trace_smoke.expected`, and added WS-B6 Tier 3 anchors in `scripts/test_tier3_invariant_surface.sh`.
- Marked WS-B6 as completed across root docs/spec/development guide and GitBook planning mirrors.
- Bumped patch version to **`0.9.16`** and synchronized root version marker in `README.md`.

## [0.9.15] - 2026-02-18

### WS-B5 semantic-correctness refinement
- Corrected `CNode.resolveSlot` semantics so `depth` is interpreted as consumed bits with `depth >= radix`, guard width `depth - radix`, and guard comparison against extracted guard bits; removed the unreachable `slotOutOfRange` branch.
- Updated `cspaceResolvePath` error mapping to the refined `ResolveError` space and realigned WS-B5 negative tests (`tests/NegativeStateSuite.lean`) to validate true depth-mismatch and guard-mismatch paths under the corrected semantics.
- Refined main trace WS-B5 coverage to assert meaningful behaviors only: removed impossible radix-0 depth-mismatch source branch and strengthened deep CNode success/guard-mismatch paths with valid pointers/depths.
- Bumped patch version to **`0.9.15`** and synchronized root version marker in `README.md`.

## [0.9.14] - 2026-02-18

### WS-B5 trace/invariant hardening follow-up
- Fixed WS-B5 trace semantics to avoid misleading "unexpected" alias output by making alias-path behavior explicit in `SeLe4n/Testing/MainTraceHarness.lean` and anchoring deep-path success with a valid guard/radix CPtr.
- Expanded Tier 2 fixture coverage by adding source/deep CSpace path expectations in `tests/fixtures/main_trace_smoke.expected` so WS-B5 path traversal outputs are regression-checked.
- Added Tier 3 invariant/doc anchors for WS-B5 (`ResolveError`, `resolveSlot`, `cspaceResolvePath`, `cspaceLookupPath`, and canonical WS-B5 completion header) in `scripts/test_tier3_invariant_surface.sh`.
- Bumped package patch version to **`0.9.14`** and synchronized root version marker in `README.md`.

## [0.9.13] - 2026-02-18

### WS-B5 CSpace guard/radix semantics completion
- Implemented executable guard/radix pointer traversal for CNodes via `CNode.resolveSlot` in `SeLe4n/Model/Object.lean`, including explicit depth mismatch and guard mismatch failure branches.
- Added path-addressed CSpace APIs (`CSpacePathAddr`, `cspaceResolvePath`, `cspaceLookupPath`) in `SeLe4n/Kernel/Capability/Operations.lean` so resolution semantics are exercised independently from direct slot lookup.
- Extended malformed-state coverage in `tests/NegativeStateSuite.lean` with WS-B5 path-resolution success + failure checks, and synchronized active-slice status/closure evidence in README/spec/development/workstream-plan/GitBook docs.
- Bumped package patch version to **`0.9.13`** and synchronized root version marker in `README.md`.

## [0.9.12] - 2026-02-18

### WS-B documentation/test-sync audit hardening
- Audited and corrected stale testing/hardware-direction status language so active-slice references consistently describe Comprehensive Audit 2026-02 WS-B execution rather than post-M7 next-slice wording.
- Added Tier 3 WS-B4 closure anchors in `scripts/test_tier3_invariant_surface.sh` that assert wrapper-structure presence for `DomainId`, `Priority`, `Irq`, `Badge`, `ASID`, `VAddr`, and `PAddr`.
- Bumped package patch version to **`0.9.12`** and synchronized root version marker in `README.md`.

## [0.9.11] - 2026-02-18

### Documentation synchronization hardening (WS-B4 follow-through)
- Audited and corrected stale GitBook/archive status language so active-slice references now consistently point to the Comprehensive Audit 2026-02 WS-B portfolio and mark older M7/post-M7 transition pages as historical context.
- Updated historical audit metadata pointers in `docs/audits/AUDIT_v0.9.0.md` so readers are directed to the current comprehensive-audit baseline and workstream execution backbone.
- Bumped package patch version to **`0.9.11`** and synchronized root version marker in `README.md`.

## [0.9.10] - 2026-02-18

### WS-B4 completion / remaining wrapper migration
- Upgraded `DomainId`, `Priority`, `Irq`, `Badge`, `ASID`, `VAddr`, and `PAddr` in `SeLe4n/Prelude.lean` from `Nat` aliases to dedicated wrapper structures with explicit migration helpers (`ofNat`/`toNat`) and compatibility instances (`OfNat`, `ToString`).
- Added a Tier 0 WS-B4 regression guard in `scripts/test_tier0_hygiene.sh` that fails if any of the migrated wrappers regress to `abbrev ... := Nat`.
- Synchronized active-slice status across root docs/spec/development guide/GitBook and canonical workstream planning docs to mark WS-B4 complete.

# Changelog

## 2026-02-19 — WS-C4 test validity hardening + documentation sync

- Completed **WS-C4 (Test validity hardening)** by adding executable invariant checks, asserting invariant validity at test fixture entry points, and enforcing post-success invariant checks in the negative state suite and trace probe.
- Hardened `MainTraceHarness` by asserting baseline and post-schedule invariant validity before running the smoke trace sequence.
- Updated active workstream status references across root docs and GitBook pages to mark WS-C4 as completed and reflect the next active execution focus.
- Bumped patch version to **`0.10.1`** and synchronized root version markers.

## [0.9.9] - 2026-02-17

### WS-B3 scenario-function decomposition and end-to-end sync audit
- Refined `SeLe4n/Testing/MainTraceHarness.lean` by decomposing the large monolithic `runMainTraceFrom` body into dedicated scenario functions (`runCapabilityAndArchitectureTrace`, `runServiceAndStressTrace`, `runLifecycleAndEndpointTrace`) while preserving stable trace output ordering and semantics.
- Re-ran complete repository validation (fast/smoke/full/nightly default+experimental and `audit_testing_framework`) to verify deterministic trace behavior and full documentation/test anchor consistency.
- Bumped package patch version to **`0.9.9`** and synchronized root version markers.

## [0.9.8] - 2026-02-17

### WS-B3 post-merge audit and synchronization hardening
- Removed an unused `TraceStep` alias from `SeLe4n/Testing/MainTraceHarness.lean` to keep the extracted harness surface minimal and intentional.
- Synchronized remaining GitBook active-slice status text (`docs/gitbook/README.md`) so WS-B3 completion state matches README/spec/development/workstream-plan snapshots.
- Re-ran full validation coverage (`test_fast`, `test_smoke`, `test_full`, default+experimental `test_nightly`, and `audit_testing_framework`) to verify full-repository consistency.
- Bumped package patch version to **`0.9.8`** and synchronized root version markers.

## [0.9.7] - 2026-02-17

### WS-B3 main trace harness refactor completion
- Refactored the executable trace harness by extracting orchestration from `Main.lean` into `SeLe4n/Testing/MainTraceHarness.lean`, keeping scenario execution composable and auditable while retaining deterministic behavior.
- Replaced ad hoc bootstrap state construction with list-driven builder composition using `SeLe4n/Testing/StateBuilder.lean` in the main harness bootstrap path.
- Updated audit/spec/development/README/GitBook status tracking to mark WS-B3 completed and record closure evidence.
- Bumped package patch version to **`0.9.7`** and synchronized root version markers.

## [0.9.6] - 2026-02-17

### WS-B2 negative-suite correctness hardening
- Refined `tests/NegativeStateSuite.lean` endpoint coverage to test both `.endpointStateMismatch` (idle endpoint receive) and `.endpointQueueEmpty` (send-state empty queue) on explicit fixtures, removing the prior mislabeled assertion gap.
- Re-ran full repository validation (`test_fast`, `test_smoke`, `test_full`, default/experimental `test_nightly`, and `audit_testing_framework`) to ensure code/docs/gitbook/test contracts remain synchronized and deterministic.
- Bumped package patch version to **`0.9.6`** and synchronized root version markers.

## [0.9.5] - 2026-02-17

### WS-B2 generative + negative testing expansion completion
- Added reusable bootstrap-state builder DSL in `SeLe4n/Testing/StateBuilder.lean` and a dedicated malformed-state executable suite in `tests/NegativeStateSuite.lean` (wired as `lake exe negative_state_suite`).
- Extended smoke/full gates with `scripts/test_tier2_negative.sh` so negative-path assertions are required alongside trace fixtures.
- Expanded nightly experimental candidates to persist per-seed stochastic probe logs and a replay manifest (`tests/artifacts/nightly/trace_sequence_probe_manifest.csv`) for deterministic triage.
- Synchronized active-slice documentation and GitBook mirrors to mark WS-B2 as completed and record closure evidence in the comprehensive-audit workstream plan.
- Bumped package patch version to **`0.9.5`** and synchronized root version markers.

## [0.9.4] - 2026-02-17

### Bootstrap reliability + doc-sync hardening follow-up
- Hardened `scripts/setup_lean_env.sh` apt bootstrap behavior: if `apt-get update` fails due an unavailable third-party source, the script now retries using primary distro sources only so required setup dependencies can still install deterministically.
- Updated developer workflow docs and GitBook mirror to document the new setup fallback behavior and keep contributor guidance aligned with executable setup semantics.
- Bumped package patch version to **`0.9.4`** and synchronized root version marker.

## [0.9.3] - 2026-02-17

### WS-B1 audit hardening and repository-wide synchronization pass
- Corrected WS-B1 ASID/root modeling by replacing the previous malformed `asidBoundToRoot` relation with a proper existential relation and documenting the explicit bounded discovery-window assumption in code and ADR.
- Added VSpace soundness/determinism anchors (`resolveAsidRoot_sound`, `vspaceLookup_deterministic`) and strengthened Tier-3 invariant-surface guards accordingly.
- Performed a full documentation/GitBook consistency pass so phase sequencing and active-slice wording consistently reflect `WS-B1 completed` status across spec/development/workflow pages.
- Updated audit index wording to align with the current `0.9.3` baseline and synchronized package version markers.

## [0.9.2] - 2026-02-17

### WS-B1 VSpace + memory model foundation completion
- Implemented first-class VSpace modeling with `VSpaceRoot` kernel objects, deterministic map/unmap/lookup transitions, and explicit failure modes for ASID binding, mapping conflicts, and translation faults.
- Added WS-B1 architecture invariant surface (`vspaceInvariantBundle`) and bounded translation predicate scaffold to anchor follow-on proof work.
- Extended `Main.lean` executable trace and Tier 2 fixture expectations with deterministic VSpace map→lookup→unmap→fault coverage.
- Published VSpace/memory abstraction ADR (`docs/VSPACE_MEMORY_MODEL_ADR.md`) and synchronized GitBook/state-tracking docs to mark WS-B1 completed in the active comprehensive-audit slice.
- Bumped package patch version from `0.9.1` to **`0.9.2`**.

## [0.9.1] - 2026-02-17

### Comprehensive-audit workstream execution kickoff readiness
- Expanded `docs/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md` into a detailed execution contract with per-workstream goals, prerequisites, implementation slices, evidence contracts, and exit criteria for WS-B1..WS-B11.
- Added explicit portfolio readiness gates (G0 kickoff readiness and G1 hardware-entry readiness) and clarified that the current slice is centered on WS-B execution kickoff.
- Synchronized root README, audit index, and GitBook planning chapter wording so active-slice status consistently reflects comprehensive-audit workstream execution readiness.
- Bumped package patch version from `0.9.0` to **`0.9.1`**.

## [0.9.0] - 2026-02-17

### CI security-scan reliability follow-up
- Fixed Gitleaks shallow-clone ambiguous revision failures by setting `actions/checkout` `fetch-depth: 0` in the security baseline scan job.
- Fixed `Platform and Security Baseline` workflow permissions by adding `pull-requests: read`, resolving Gitleaks pull-request commit enumeration failures (`Resource not accessible by integration`) in the `Security Signal / Secret + Dependency + CodeQL` job.
- Updated `docs/CI_POLICY.md` to document the `pull-requests: read` requirement and rationale for the Gitleaks PR scan path.
- Made CodeQL analyze upload non-blocking (`continue-on-error: true`) to avoid failing the security lane when repository Code Scanning is not enabled.
- Added Tier 3 invariant/doc anchor coverage to ensure the workflow retains `pull-requests: read` in future refactors.
- Version marker remains `0.9.0` as the canonical minor-release target for this slice.


### M7 exit-gate closeout and next-slice activation
- Published formal M7 closeout artifact `docs/M7_CLOSEOUT_PACKET.md` and GitBook mirror `docs/gitbook/23-m7-remediation-closeout-packet.md`, including dependency owners, accepted residual risks, and exit-gate checklist evidence.
- Synchronized root docs/spec/development/testing/GitBook stage markers so M7 is completed baseline and post-M7 hardware-oriented next-slice execution is active.
- Expanded Tier-3 documentation anchors to validate closeout packet presence and stage-state synchronization as part of required full-suite checks.
- Bumped project version from `0.8.22` to **`0.9.0`** for the post-remediation minor release transition.

## [0.8.22] - 2026-02-17

### WS-A8 validation hardening and CI robustness
- Hardened `.github/workflows/platform_security_baseline.yml` so security scanning is skipped for fork-origin pull requests where `security-events: write` is unavailable, while keeping the ARM64 fast-gate lane active.
- Expanded test/docs synchronization by adding WS-A8 artifact anchor checks to `scripts/test_tier3_invariant_surface.sh` (workflow/job names, roadmap milestones, and cross-doc references).
- Updated testing docs (`docs/TESTING_FRAMEWORK_PLAN.md` and `docs/gitbook/07-testing-and-ci.md`) to explicitly include WS-A8 platform/security baseline automation in the CI/test contract narrative.
- Bumped package patch version to `0.8.22` and synchronized README version marker.

## [0.8.21] - 2026-02-17

### WS-A8 platform/security maturity completion
- Added `.github/workflows/platform_security_baseline.yml` to operationalize WS-A8 gates: an ARM64 architecture-targeted fast lane (`ubuntu-24.04-arm`) and automated baseline security scanning (Gitleaks, Trivy, CodeQL for workflow analysis).
- Published `docs/INFORMATION_FLOW_ROADMAP.md` with staged IF-M1..IF-M5 milestones, deliverables, and exit-evidence expectations for post-M7 information-flow proofs.
- Updated remediation/development/GitBook tracking docs to mark WS-A8 completed and synchronized CI policy/README references with the new security and roadmap artifacts.
- Bumped package patch version to `0.8.21` and synchronized the root README version marker.

## [0.8.20] - 2026-02-17

### Validation and documentation synchronization follow-up
- Refined nightly-testing documentation (`docs/TESTING_FRAMEWORK_PLAN.md` and `docs/gitbook/07-testing-and-ci.md`) to match mode-aware Tier 4 status behavior in `scripts/test_nightly.sh` (default extension-point guidance vs executed signal when `NIGHTLY_ENABLE_EXPERIMENTAL=1`).
- Re-validated smoke/full/nightly test tiers (default + experimental) to confirm repository and GitBook/testing docs remain synchronized with current M7 progress state.
- Bumped package patch version to `0.8.20` and synchronized the root README version marker.

## [0.8.19] - 2026-02-17

### Audit hardening follow-up
- Optimized `scripts/test_nightly.sh` reporting so Tier 4 status messaging is environment-aware: it now reports staged execution when `NIGHTLY_ENABLE_EXPERIMENTAL=1` and reports extension-point guidance only in default mode.
- Re-ran full validation coverage (`test_smoke`, `test_full`, default `test_nightly`, experimental `test_nightly`, `lake build`, and executable trace run) to confirm repository, docs, and GitBook remain synchronized with current M7/WS-A7 status.
- Bumped package patch version to `0.8.19` and synchronized the root README version marker.

## [0.8.18] - 2026-02-17

### WS-A7 proof maintainability completion
- Completed WS-A7 by introducing shared helper theorem `endpoint_store_preserves_schedulerInvariantBundle` in `SeLe4n/Kernel/IPC/Invariant.lean`, reducing repeated scheduler-bundle proof blocks across endpoint send/await/receive preservation theorems.
- Added concise theorem-purpose docstrings for the shared helper and endpoint scheduler-bundle preservation theorem entrypoints to improve proof-surface legibility for reviewers.
- Updated development guide and GitBook workstream status pages to mark WS-A7 completed and move active focus to WS-A8.
- Bumped package patch version to `0.8.18` and synchronized the root README version marker.

## [0.8.17] - 2026-02-17

### Documentation/GitBook sync audit hardening
- Closed remaining WS-A6-era documentation drift by marking WS-A4 as completed in `docs/M7_CLOSEOUT_PACKET.md` to match existing closure evidence and the active-slice status pages.
- Updated `docs/gitbook/13-future-slices-and-delivery-plan.md` so M7 workstream statuses are synchronized with current slice reality (WS-A1..WS-A6 completed, WS-A7 in progress, WS-A8 planned).
- Bumped package patch version to `0.8.17` and synchronized the root README version marker.

## [0.8.16] - 2026-02-17

### WS-A6 documentation IA completion
- Marked WS-A6 as completed across remediation planning and active-slice GitBook chapters with explicit closure evidence and DoD status updates.
- Added a contributor-first 5-minute onboarding path in `CONTRIBUTING.md`, synchronized root `README.md` start-here ordering, and mirrored the same quickstart flow in `docs/gitbook/README.md`.
- Updated M7 completion snapshot in `docs/DEVELOPMENT.md` to reflect WS-A6 closure and move active focus to WS-A7.

## [0.8.15] - 2026-02-17

### WS-A5 regression-guard refinement
- Added Tier 3 invariant/doc anchors for WS-A5 closure evidence: fixture-module presence, `Main.lean` fixture import, and hardware-boundary policy guard language.
- Preserved full Tier 0–4 validation after extending regression anchors.

## [0.8.14] - 2026-02-17

### WS-A5 audit follow-up hardening
- Hardened Tier 0 import-boundary hygiene to include a non-`rg` fallback scan path, preventing false failures in environments where ripgrep is unavailable.
- Tightened `docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md` wording so policy scope matches enforcement (`SeLe4n/Kernel`).

## [0.8.13] - 2026-02-17

### Hardware-boundary safety / WS-A5 completion
- Isolated permissive runtime contract fixtures into `SeLe4n/Testing/RuntimeContractFixtures.lean` and updated `Main.lean` to consume them from a testing-only module.
- Added Tier 0 hygiene boundary enforcement to fail if production modules under `SeLe4n/` reference test-only runtime contract fixtures.
- Added `docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md` and synchronized remediation/GitBook workstream status to mark WS-A5 complete.

## [0.8.12] - 2026-02-17

### Testing / WS-A4 completion hardening
- Expanded Tier 2 fixture-backed trace coverage in `Main.lean` + `tests/fixtures/main_trace_smoke.expected` to explicitly cover all audit-recommended scale categories: deep CNode radix shape, large runnable queue (10+), multiple IPC endpoints, service dependency chain depth-5, and boundary memory addresses.
- Kept Tier 2 scenario/risk tagging format for audit traceability while adding new WS-A4 scale scenarios under `WS-A4-SCALE-*` IDs.
- Revalidated Tier 0–4 scripts (including seeded `trace_sequence_probe`) with the expanded scenarios and refreshed M7 workstream documentation evidence.

All notable changes to this project are documented in this file.

## [0.8.10] - 2026-02-17

### WS-A3 regression-guard hardening
- Added Tier-3 invariant-surface guards that require explicit `ThreadId.toObjId` conversion entrypoint presence and fail if an implicit `ThreadId -> ObjId` coercion is reintroduced.
- Revalidated full Tier 0-4 test coverage (`test_fast`, `test_smoke`, `test_full`, `test_nightly` with experimental candidates) after introducing the new guard.

## [0.8.9] - 2026-02-17

### WS-A3 audit follow-up hardening
- Removed implicit `ThreadId -> ObjId` coercion and replaced it with explicit `ThreadId.toObjId` conversions at object-store boundaries to preserve stronger compile-time domain separation.
- Updated scheduler and IPC proof/operation call sites to use explicit conversion points and kept all invariant bundles compiling without placeholder debt.
- Synchronized GitBook planning chapters so WS-A3 completion state is consistent across current-slice and remediation overview pages.

## [0.8.8] - 2026-02-17

### M7 WS-A3 type-safety uplift
- Migrated `ThreadId`, `ObjId`, `CPtr`, and `Slot` from raw `Nat` aliases to dedicated wrapper types with migration helpers (`ofNat`/`toNat`) and typed bridge instances where object-store indexing is intentional.
- Updated scheduler/IPC invariant surfaces to keep thread-domain membership obligations typed as `ThreadId` while preserving object-store key discipline through `ObjId`.
- Updated active-slice docs/GitBook to mark WS-A3 completed and synced current development status snapshots.

## [0.8.7] - 2026-02-17

### Tooling setup optimization
- Refactored `scripts/setup_lean_env.sh` to share package-manager helpers and perform `apt-get update` at most once even when both `shellcheck` and `ripgrep` are missing.
- Preserved all existing installer behavior while reducing duplicated setup work/noise in cold environments.

## [0.8.6] - 2026-02-17

### Audit/Sync hardening
- Performed full post-WS-A2 repository validation sweep (`test_fast`, `test_smoke`, `test_full`, `test_nightly`) and confirmed all tiers pass without regressions.
- Synchronized roadmap and audit-context docs so M7 status explicitly reflects WS-A1/WS-A2 as completed while preserving historical audit snapshot intent.
- Clarified historical audit caveat language so architecture criticisms about IPC split are interpreted as pre-remediation findings, not current-state defects.

## [0.8.5] - 2026-02-17

### Architecture / API modularity (WS-A2)
- Split IPC transition semantics into `SeLe4n/Kernel/IPC/Operations.lean` and retained invariant/proof obligations in `SeLe4n/Kernel/IPC/Invariant.lean` to restore operations/invariant symmetry.
- Kept `SeLe4n/Kernel/API.lean` as the stable external facade while explicitly exporting IPC operations and invariant surfaces.
- Updated development documentation and GitBook architecture maps/workstream tracking to mark WS-A2 complete with closure evidence.

## [0.8.4] - 2026-02-17

### CI / Tooling reliability
- Updated `scripts/setup_lean_env.sh` to install `ripgrep` (`rg`) when missing, matching Tier-3/Tier-4 script requirements and preventing CI failures where `rg` is unavailable.

## [0.8.3] - 2026-02-17

### CI / Tooling reliability
- Fixed `scripts/setup_lean_env.sh` to source existing elan env before probing/installing, preventing redundant reinstall attempts in CI shells that do not persist PATH changes.
- Fixed `scripts/setup_lean_env.sh` to treat already-installed Lean toolchains as a success path, preventing CI failures when `leanprover/lean4:v4.27.0` is present.

## [0.8.2] - 2026-02-17

### Documentation
- Added root `CONTRIBUTING.md` pointer to canonical contributor workflow in `docs/DEVELOPMENT.md`.
- Added root `CHANGELOG.md` for chronological release notes and milestone-delivery traceability.
- Added post-audit remediation note in `docs/audits/AUDIT_v0.8.0.md` clarifying WS-A1 CI hardening landed after the audit snapshot.

### CI / Quality Gates
- Added Tier 3/WS-A1 documentation anchor checks for CI policy/workflow artifacts and root contributor/changelog discoverability in `scripts/test_tier3_invariant_surface.sh`.

## [0.8.1] - 2026-02-17

### CI / Quality Gates (WS-A1)
- Promoted Tier 3 (`test_full.sh`) into CI merge-gate flow.
- Added nightly determinism workflow running `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh`.
- Added canonical branch-protection policy doc `docs/CI_POLICY.md`.
- Added Lean/Lake cache restoration in CI workflows.

## [0.8.0] - 2026-02-17

### Baseline
- M6 complete / M7 active audit-remediation baseline.
