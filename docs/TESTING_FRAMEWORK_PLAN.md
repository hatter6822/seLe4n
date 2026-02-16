# seLe4n Testing Framework Plan

## 1. Purpose

This document defines the active testing baseline and near-term expansion path for the M5 stage.

Current stage context: **M5 service-graph + policy surface delivery active (with M4-B fully closed)**.

## 2. Current enforced tiers

- **Tier 0** hygiene (`scripts/test_tier0_hygiene.sh`)
- **Tier 1** build/theorem compile (`scripts/test_tier1_build.sh`)
- **Tier 2** fixture-backed executable smoke (`scripts/test_tier2_trace.sh`)
- **Tier 3** invariant/doc-surface checks (`scripts/test_tier3_invariant_surface.sh`, via full suite),
  including M4-A executable-anchor checks for lifecycle unauthorized/illegal-state/success trace fragments.
- **Tier 4** staged nightly candidates (`scripts/test_tier4_nightly_candidates.sh` via `scripts/test_nightly.sh`; explicit opt-in extension point)

## 3. Required entrypoints and CI contract

Required local/CI entrypoints:

- `./scripts/test_fast.sh` (Tier 0 + Tier 1)
- `./scripts/test_smoke.sh` (Tier 0 + Tier 1 + Tier 2)

Recommended audit entrypoint for release/closeout confidence:

- `./scripts/audit_testing_framework.sh` (baseline tier stack + Tier 4 experimental candidate execution + Tier 2 negative-control mismatch assertion)

PR CI must call repository scripts directly and keep workflow logic thin.

## 4. Baseline testing objectives inherited from M4-A

1. Keep baseline M1-M3.5 behavior stable.
2. Add fixture fragments for lifecycle output once lifecycle scenarios become executable.
3. Keep Tier 3 anchors for lifecycle transition/invariant theorem surfaces (including metadata-coherence anchors).
4. Keep Tier 3 milestone-closure anchors for M1 scheduler and M2 capability transition/preservation surfaces so completed milestones remain continuously verified.
5. Preserve category-labeled failure output (`HYGIENE`, `BUILD`, `TRACE`, `INVARIANT`, `META`).

## 5. Active M5 testing expansion targets

1. Add service-graph restart/isolation/dependency-failure scenario fixtures.
2. Add grouped Tier 3 checks for M5 service/policy theorem and bundle symbols.
3. Expand nightly checks toward repeat-run determinism and broader scenario sweeps.
4. Standardize new artifact names for debugging service/policy regression failures.

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

### Tier 3 (invariant/doc-surface anchors)

Primary risks protected:

- silent loss of required theorem/bundle/doc symbols used as milestone acceptance anchors.

### Tier 4 (nightly extension)

Primary risks to target next:

- determinism regressions,
- scenario breadth gaps,
- long-horizon confidence blind spots.

## 9. M5-specific testing growth plan

1. add service-orchestration fixture fragments that remain stable across formatting changes,
2. add grouped service/policy theorem anchor checks in Tier 3,
3. add failure-path scenarios for dependency violation and policy denial behavior,
4. record any new artifact outputs with consistent naming for CI triage.


## 10. M5 test implementation plan (detailed)

1. **Phase T1 — service scenario seeds**
   - add at least one service start/restart success trace,
   - add at least one policy/dependency failure trace.
2. **Phase T2 — fixture hardening**
   - capture stable semantic fragments only,
   - avoid transient formatting-dependent assertions.
3. **Phase T3 — Tier 3 anchor expansion**
   - add symbol anchors for M5 invariant and preservation theorem surfaces,
   - keep anchors grouped by milestone objective for triage clarity.
4. **Phase T4 — nightly evolution**
   - preserve explicit Tier 4 extension-point behavior by default in `./scripts/test_nightly.sh`,
   - stage repeat-run determinism + full-suite replay candidates in `./scripts/test_tier4_nightly_candidates.sh`,
   - keep candidate execution opt-in (`NIGHTLY_ENABLE_EXPERIMENTAL=1`) so required mainline gates remain stable.

## 11. Coverage model and "full coverage" interpretation

Because seLe4n is a Lean theorem/proof-oriented project, coverage is tracked as **obligation coverage** rather than conventional statement-percentage metrics.

Current coverage obligations:

1. **Compile/build closure**: all tracked modules and executable build in Tier 1.
2. **Executable semantic anchor coverage**: Tier 2 fixture checks assert stable integration-trace semantics.
3. **Theorem/invariant surface coverage**: Tier 3 anchor checks ensure required milestone symbols remain present.
4. **Nightly determinism candidate coverage**: Tier 4 staged repeat-run + replay checks are available and exercised during audit in experimental mode.
5. **Failure-detection coverage**: audit-level negative control verifies Tier 2 correctly fails on intentionally impossible fixture expectations.

For future milestones, expand this model by adding new proof/trace obligations at the same time new semantics are introduced.
