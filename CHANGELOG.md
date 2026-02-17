# Changelog

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
- Expanded `docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md` into a detailed execution contract with per-workstream goals, prerequisites, implementation slices, evidence contracts, and exit criteria for WS-B1..WS-B11.
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
- Closed remaining WS-A6-era documentation drift by marking WS-A4 as completed in `docs/audits/AUDIT_REMEDIATION_WORKSTREAMS.md` to match existing closure evidence and the active-slice status pages.
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
- Added post-audit remediation note in `docs/audits/REPOSITORY_AUDIT.md` clarifying WS-A1 CI hardening landed after the audit snapshot.

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
