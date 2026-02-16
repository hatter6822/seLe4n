# seLe4n Testing Framework Plan

## 1. Purpose

This document defines the active testing baseline and near-term expansion path for the M4 stage.

Current stage context: **M4-B lifecycle-capability composition hardening active (M4-A + WS-A + WS-B complete)**.

## 2. Current enforced tiers

- **Tier 0** hygiene (`scripts/test_tier0_hygiene.sh`)
- **Tier 1** build/theorem compile (`scripts/test_tier1_build.sh`)
- **Tier 2** fixture-backed executable smoke (`scripts/test_tier2_trace.sh`)
- **Tier 3** invariant/doc-surface checks (`scripts/test_tier3_invariant_surface.sh`, via full suite),
  including M4-A executable-anchor checks for lifecycle unauthorized/illegal-state/success trace fragments.
- **Tier 4** extension hook (nightly wrapper currently documents expansion point)

## 3. Required entrypoints and CI contract

Required local/CI entrypoints:

- `./scripts/test_fast.sh` (Tier 0 + Tier 1)
- `./scripts/test_smoke.sh` (Tier 0 + Tier 1 + Tier 2)

PR CI must call repository scripts directly and keep workflow logic thin.

## 4. Baseline testing objectives inherited from M4-A

1. Keep baseline M1-M3.5 behavior stable.
2. Add fixture fragments for lifecycle output once lifecycle scenarios become executable.
3. Keep Tier 3 anchors for lifecycle transition/invariant theorem surfaces (including metadata-coherence anchors).
4. Keep Tier 3 milestone-closure anchors for M1 scheduler and M2 capability transition/preservation surfaces so completed milestones remain continuously verified.
5. Preserve category-labeled failure output (`HYGIENE`, `BUILD`, `TRACE`, `INVARIANT`, `META`).

## 5. Active M4-B testing expansion targets

1. Add success + failure lifecycle scenario fixtures.
2. Add grouped Tier 3 checks for lifecycle-capability composition symbols.
3. Expand nightly checks toward repeat-run determinism and broader scenario sweeps.
4. Standardize new artifact names for debugging lifecycle regression failures.

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

## 9. M4-specific testing growth plan

1. add lifecycle scenario fixture fragments that remain stable across formatting changes,
2. add grouped lifecycle theorem anchor checks in Tier 3,
3. add at least one failure-path scenario for lifecycle invalid-object/invalid-authority behavior,
4. record any new artifact outputs with consistent naming for CI triage.


## 10. M4-B test implementation plan (detailed)

1. **Phase T1 — composition scenario seeds**
   - add at least one composed lifecycle+capability success trace,
   - add at least one composed failure trace (stale or authority failure).
2. **Phase T2 — fixture hardening**
   - capture stable semantic fragments only,
   - avoid transient formatting-dependent assertions.
3. **Phase T3 — Tier 3 anchor expansion**
   - add symbol anchors for M4-B invariant and preservation theorem surfaces,
   - keep anchors grouped by milestone objective for triage clarity.
4. **Phase T4 — nightly evolution**
   - preserve current Tier 4 extension hook behavior,
   - stage repeat-run determinism checks as follow-on without destabilizing mainline gates.
