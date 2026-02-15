# seLe4n Testing Framework Implementation Plan (Current Baseline + Next Expansion)

## 1. Purpose

This document is the testing framework baseline for seLe4n. It captures what is already enforced,
what remains intentionally optional, and what next expansion steps should be taken as the project
moves from M3.5 to M4.

### 1.1 Implementation status snapshot

Current repository status:

- ✅ Work package A (script scaffold) implemented.
- ✅ Work package B (fixture-backed executable smoke baseline) implemented.
- ✅ Work package C (CI wiring to script entrypoints) implemented.
- ✅ Work package D (docs integration) implemented.
- ✅ Work package E (Tier 3 invariant/doc-surface checks) implemented, including M3.5 step-1 through step-6 theorem/lemma surface anchors.

---

## 2. Quality bar and outcomes

The framework is successful only if all of the following remain true.

1. **Proof-surface stability**
   - `lake build` keeps theorem entrypoints compiling.
   - No committed `axiom`, `sorry`, or unresolved work markers in core scope.

2. **Executable behavior stability**
   - `lake exe sele4n` remains operational.
   - Stable output fragments are guarded by fixture checks.

3. **Milestone regression resistance**
   - M1/M2/M3 guarantees remain protected while M3.5 evolves.
   - Future M4 additions can be integrated without replacing baseline tiers.

4. **Fast local loop + deterministic CI gates**
   - contributors can run required checks quickly,
   - CI runs the same repository entrypoints used locally.

5. **Actionable failures**
   - failures identify category (`HYGIENE`, `BUILD`, `TRACE`, `INVARIANT`, `META`) and likely next action.

---

## 3. Current enforced scope

### 3.1 Active required tiers

- **Tier 0** hygiene check (`scripts/test_tier0_hygiene.sh`)
- **Tier 1** build/theorem check (`scripts/test_tier1_build.sh`)
- **Tier 2** fixture-backed executable smoke (`scripts/test_tier2_trace.sh`)

### 3.2 Aggregated required entrypoints

- `./scripts/test_fast.sh` = Tier 0 + Tier 1
- `./scripts/test_smoke.sh` = Tier 0 + Tier 1 + Tier 2

Both are required pull-request CI jobs.

### 3.3 Full/nightly tiers

- `./scripts/test_full.sh` runs Tier 3 invariant/doc-surface checks.
- `./scripts/test_nightly.sh` runs full plus Tier 4 extension notice.

Tier 3 is now active in the full suite and includes milestone-surface anchors through current M3.5 step-6 local-first preservation theorem layer; Tier 4 remains the next expansion hook.

---

## 4. Script contract (implemented baseline)

All test scripts should continue to:

- use `set -euo pipefail`,
- resolve repository root robustly,
- auto-source `$HOME/.elan/env` when available,
- emit section-prefixed logs,
- fail deterministically with clear category messages.

Shared helper behaviors are centralized in `scripts/test_lib.sh` to avoid drift.

---

## 5. Fixture regression policy

### 5.1 Fixture source of truth

- Expected trace fragments: `tests/fixtures/main_trace_smoke.expected`.
- Comparison mode: line-oriented substring matching for each non-empty fixture line.

### 5.2 Intentional behavior change workflow

1. Run `lake exe sele4n` and validate behavior change intent.
2. Update only stable semantic fixture lines.
3. Re-run `./scripts/test_tier2_trace.sh` and `./scripts/test_smoke.sh`.
4. Explain fixture updates in PR notes.

### 5.3 Failure diagnostics

On mismatch, Tier 2 reports missing fragments on `[TRACE]` lines. CI can additionally archive:

- `main_trace_smoke.actual.log`,
- `main_trace_smoke.missing.txt`,
- expected fixture file.

---

## 6. CI contract

Required PR jobs execute:

1. `./scripts/test_fast.sh`
2. `./scripts/test_smoke.sh`

CI must continue calling repository scripts directly; avoid duplicating gate logic in workflow YAML.

---

## 7. Next expansion steps (post-M3.5 to M4 readiness)

These are the prioritized testing next steps once M3.5 semantics begin landing.

1. **Tier 2 fixture growth for M3.5 stories**
   - add stable trace fragments for waiting/handshake behavior.

2. **Tier 3 invariant-group deepening**
   - extend current invariant/doc-surface checks into richer milestone-bundle grouped checks.

3. **Artifact ergonomics**
   - standardize artifact naming for any new tier scripts.

4. **Nightly confidence checks (Tier 4)**
   - add repeat-run determinism and broader scenario sweeps.

5. **Contributor guidance hardening**
   - keep README + DEVELOPMENT + scenarios docs synchronized with any new tier requirements.

---

## 8. Definition of done for current framework stage

Current stage is healthy when all conditions below hold:

1. `test_fast` and `test_smoke` remain stable and required.
2. Tier 0/1/2 checks are enforced in PR CI.
3. Fixture-backed trace regression check remains active and reviewable.
4. Contributor docs explain run/debug/update workflow consistently.
5. Failure output remains category-labeled and actionable.

---

## 9. Operational checklist (for PR authors touching tests/docs)

- [ ] Updated relevant docs when changing test behavior or tier requirements.
- [ ] Verified `./scripts/test_fast.sh`.
- [ ] Verified `./scripts/test_smoke.sh`.
- [ ] Verified direct `lake build` and `lake exe sele4n` as needed.
- [ ] Documented fixture intent when expected trace fragments changed.

---

## 10. Risks and mitigations

1. **Fixture brittleness**
   - Mitigation: assert stable semantic fragments, not volatile formatting.

2. **Script drift across tiers**
   - Mitigation: continue shared helper usage in `test_lib.sh`.

3. **CI/local divergence**
   - Mitigation: CI must invoke repository scripts directly.

4. **Runtime inflation**
   - Mitigation: keep required loop minimal; push heavier checks to full/nightly.

5. **Unclear maintenance ownership**
   - Mitigation: maintain shared ownership expectations in `docs/DEVELOPMENT.md`.
