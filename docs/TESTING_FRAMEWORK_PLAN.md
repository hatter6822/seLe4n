# seLe4n Testing Framework Plan

## 1. Purpose

This document defines the active testing baseline and near-term expansion path after M5 closeout.

Current stage context: **All prior workstreams completed through WS-K (v0.16.8). Active workstream: WS-L (IPC subsystem audit & remediation). Testing surface: 37,245 production LoC, 4,098 test LoC, 1,198 proved declarations (zero sorry/axiom). 4-tier CI enforces regression protection across 69 production files and 4 test suites.**

## 2. Current enforced tiers

- **Tier 0** hygiene (`scripts/test_tier0_hygiene.sh`: forbidden-marker scan, fixture-isolation guard, wrapper-structure regression, theorem-body spot-check, SHA-pinning regression, optional shellcheck)
- **Tier 1** build/theorem compile (`scripts/test_tier1_build.sh`)
- **Tier 2** executable smoke (`scripts/test_tier2_trace.sh` + `scripts/test_tier2_negative.sh`, including `negative_state_suite` + `information_flow_suite`)
- **Tier 3** invariant surface checks (`scripts/test_tier3_invariant_surface.sh`, via full suite),
  including code/theorem/trace anchor verification for all milestone surfaces.
- **Tier 4** staged nightly candidates (`scripts/test_tier4_nightly_candidates.sh` via `scripts/test_nightly.sh`; explicit opt-in extension point with mode-aware status messaging for default vs enabled runs)

Documentation sync (`scripts/test_docs_sync.sh`) verifies GitBook navigation generation, markdown link integrity, and optional doc-gen4 probes. It is integrated into the `test_smoke.sh` entrypoint and the smoke CI job (WS-H3/M-19), catching documentation navigation/link drift on every PR.

## 3. Required entrypoints and CI contract

Required local/CI entrypoints:

- `./scripts/test_fast.sh` (Tier 0 + Tier 1)
- `./scripts/test_smoke.sh` (Tier 0 + Tier 1 + Tier 2 trace + Tier 2 negative-state checks + documentation sync)
- `./scripts/test_full.sh` (Tier 0 + Tier 1 + Tier 2 + Tier 3)

Nightly deterministic replay entrypoint:

- `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` (Tier 0..4 staged replay/diff checks + seeded sequence-diversity probe with persisted seed logs/manifest replay artifacts)

Recommended audit entrypoint for release/closeout confidence:

- `./scripts/audit_testing_framework.sh` (baseline tier stack + Tier 4 experimental candidate execution + Tier 2 negative-control mismatch assertion)

PR CI must call repository scripts directly and keep workflow logic thin.

Branch-protection and required-check policy is documented in `docs/CI_POLICY.md`.

WS-A8 platform/security baseline automation is provided by `.github/workflows/platform_security_baseline.yml` (ARM64 fast gate + baseline security scanning controls).

Root contributor discoverability artifacts are `CONTRIBUTING.md` and `CHANGELOG.md`.

## 4. Baseline testing objectives inherited from M4-A

1. Keep baseline M1-M3.5 behavior stable.
2. Add fixture fragments for lifecycle output once lifecycle scenarios become executable.
3. Keep Tier 3 anchors for lifecycle transition/invariant theorem surfaces (including metadata-coherence anchors).
4. Keep Tier 3 milestone-closure anchors for M1 scheduler and M2 capability transition/preservation surfaces so completed milestones remain continuously verified.
5. Preserve category-labeled failure output (`HYGIENE`, `BUILD`, `TRACE`, `INVARIANT`, `META`).

## 5. M5 evidence/testing closure status (WS-M5-E complete)

1. Service-graph restart/isolation/dependency-failure fixture fragments are present in `tests/fixtures/main_trace_smoke.expected`.
2. Tier 3 includes grouped M5 service/policy theorem and bundle symbol checks plus trace anchors.
3. Tier 4 staged nightly candidates now assert determinism and M5 evidence-line presence before full-suite replay.
4. Artifact names remain standardized under `tests/artifacts/nightly/` for CI triage.

## 6. Fixture policy

Source of truth: `tests/fixtures/main_trace_smoke.expected`.

Rules:

1. Assert stable semantic substrings only.
2. Update fixture only when executable behavior intentionally changes.
3. Re-run `./scripts/test_tier2_trace.sh` and `./scripts/test_smoke.sh` after fixture edits.
4. Explain fixture changes in PR notes.

## 7. Operational checklist for contributors

- [ ] Ran `./scripts/test_fast.sh`.
- [ ] Ran `./scripts/test_smoke.sh`.
- [ ] Ran `lake build` and `lake exe sele4n` when transition semantics changed.
- [ ] Updated fixture intentionally (if needed) with rationale.
- [ ] Updated docs when testing expectations changed.

## 8. Signal map: what each tier protects

### Tier 0 (hygiene)

Primary risk protected:

- accidental introduction of unresolved proof placeholders or hygiene debt in tracked proof surface.

### Tier 1 (build/theorem compile)

Primary risks protected:

- transition API drift,
- theorem-entrypoint breakage,
- bundle composition breakage across modules.

### Tier 2 (trace fixture)

Primary risks protected:

- executable semantic drift in integration scenarios,
- stale milestone claims not reflected in runtime evidence.

### Tier 3 (invariant surface anchors)

Primary risks protected:

- silent loss of required theorem/bundle/trace symbols used as milestone acceptance anchors.

### Tier 4 (nightly extension)

Primary risks to target next:

- determinism regressions,
- scenario breadth gaps,
- long-horizon confidence blind spots.

## 9. M5-specific testing growth plan (completed baseline)

1. add service-orchestration fixture fragments that remain stable across formatting changes,
2. add grouped service/policy theorem anchor checks in Tier 3,
3. add failure-path scenarios for dependency violation and policy denial behavior,
4. record any new artifact outputs with consistent naming for CI triage.


## 10. M5 test implementation baseline (achieved)

1. **Phase T1 — service scenario seeds** ✅
   - includes service start/restart success trace anchors,
   - includes policy-denial and dependency-failure trace anchors.
2. **Phase T2 — fixture hardening** ✅
   - fixture captures stable semantic fragments,
   - avoids formatting-dependent expectations.
3. **Phase T3 — Tier 3 anchor expansion** ✅
   - includes M5 invariant/preservation symbol anchors,
   - keeps anchor groups organized by milestone objective for triage clarity.
4. **Phase T4 — nightly evolution** ✅
   - Tier 4 default remains an explicit extension point in `./scripts/test_nightly.sh`,
   - staged candidates in `./scripts/test_tier4_nightly_candidates.sh` run determinism + evidence checks + seeded `trace_sequence_probe` sequence-diversity checks + full-suite replay,
   - candidate execution remains opt-in (`NIGHTLY_ENABLE_EXPERIMENTAL=1`) for stable required mainline gates.

## 11. Coverage model and "full coverage" interpretation

Because seLe4n is a Lean theorem/proof-oriented project, coverage is tracked as **obligation coverage** rather than conventional statement-percentage metrics.

Current coverage obligations:

1. **Compile/build closure**: all tracked modules and executable build in Tier 1.
2. **Executable semantic anchor coverage**: Tier 2 fixture checks assert stable integration-trace semantics.
3. **Theorem/invariant surface coverage**: Tier 3 anchor checks ensure required milestone symbols remain present.
4. **Nightly determinism candidate coverage**: Tier 4 staged repeat-run + replay checks are available and exercised during audit in experimental mode.
5. **Failure-detection coverage**: audit-level negative control verifies Tier 2 correctly fails on intentionally impossible fixture expectations.

For future milestones, expand this model by adding new proof/trace obligations at the same time new semantics are introduced.


## 12. M7 WS-A4 closure evidence (completed)

1. Tier 2 fixture entries are scenario-labeled with `scenario_id | risk_class | expected_trace_fragment` so risk mapping is auditable at a glance.
2. Tier 2 parser emits concise scenario/risk-tagged failures and ignores comment/blank fixture lines for readability.
3. Tier 4 nightly candidates execute seeded `trace_sequence_probe` runs to provide stochastic/property-style sequence diversity checks over IPC endpoint-state consistency.

## 13. v0.11.6 audit findings and WS-E1 testing growth plan

The v0.11.6 codebase audit identified the following testing-specific gaps:

| Finding | Severity | Description | WS-E1 action |
|---------|----------|-------------|-------------|
| M-10 | MEDIUM | All tests use hardcoded fixtures; ~0.05% input space coverage | Add parameterized topologies varying thread count, priorities, CNode radix, ASID |
| M-11 | MEDIUM | Runtime invariant checks miss CSpace coherency, capability attenuation, lifecycle metadata, service acyclicity, VSpace ASID uniqueness | Extend `InvariantChecks.lean` with new predicate functions |
| L-07 | LOW | `grep -Fq` substring matching is fragile against repr format changes | Add structured trace format alongside current validation |
| L-08 | LOW | Tier 3 anchor presence does not verify proof correctness | Add spot-check theorem-body validation (no `sorry`, no trivial `rfl`-only) |
| F-14 | LOW | GitHub Actions use floating version tags | SHA-pin all actions with tag comments |

Quick fixes already applied in P0 baseline:

- **F-09:** Added `runtimeContractTimerOnly` and `runtimeContractReadOnlyMemory` intermediate fixtures.
- **F-10:** Replaced hardcoded 512-ID bound with `st.objectIndex` discovery.
- **F-15:** Added explicit `permissions: contents: read` to CI workflows.
