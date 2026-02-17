# Changelog

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
- Added post-audit remediation note in `docs/REPOSITORY_AUDIT.md` clarifying WS-A1 CI hardening landed after the audit snapshot.

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
