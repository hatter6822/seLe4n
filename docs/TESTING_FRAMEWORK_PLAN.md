# seLe4n Testing Framework Plan

## 1. Purpose

This document defines a staged plan for building a comprehensive testing framework for seLe4n.
The objective is to add repeatable, automated confidence checks that complement Lean proof
obligations with executable behavior checks, regression detection, and contributor ergonomics.

This is a planning artifact only. Implementation will be delivered in follow-up slices.

---

## 2. Testing goals and quality bar

The framework should ensure:

1. **Proof surface stability**
   - Existing milestone theorem entrypoints continue to compile.
   - No accidental reintroduction of `axiom`/`sorry` in core modules.

2. **Executable behavior stability**
   - The `Main.lean` scenario remains runnable and deterministic enough for CI checks.
   - Expected high-level state transitions are validated through output-oriented smoke tests.

3. **Regression resistance for milestone slices**
   - M1/M2/M3 guarantees remain covered as M3.5 evolves.
   - Invariant bundle boundaries are tested at module and integration levels.

4. **Fast local feedback + reliable CI enforcement**
   - Contributors can run a short pre-commit suite quickly.
   - CI runs an expanded suite with stronger guarantees.

5. **Actionable failures**
   - Failures should pinpoint class of regression (proof compile break, trace mismatch,
     hygiene issue, style/lint issue, or performance drift).

---

## 3. Scope

### In scope

- Standardized command entrypoints (scripts or `lake` aliases) for test tiers.
- Baseline gates for build, executable run, and hygiene checks.
- Structured organization for theorem-preservation and scenario regression tests.
- CI pipeline design with clear tiers and failure policy.
- Contributor documentation and PR checklist integration.

### Out of scope (initial rollout)

- Full formal benchmarking/latency dashboards.
- Heavy randomized theorem generation infrastructure.
- Broad architecture-specific or kernel-configuration matrix testing.

---

## 4. Test taxonomy (target end-state)

### 4.1 Tier 0 — Hygiene and structural checks (fastest)

Purpose: catch obvious defects before expensive checks.

Proposed checks:

- forbidden markers scan: `axiom|sorry|TODO` in core model/kernel files,
- formatting/style policy checks (if formatter/lint rules are adopted),
- docs drift checks for required milestone sections (optional later enhancement).

Expected runtime: ~seconds.

### 4.2 Tier 1 — Build and theorem compile checks

Purpose: guarantee theorem surfaces still compile.

Proposed checks:

- `lake build` for full project compile,
- optional focused module build targets for rapid feedback,
- optional explicit compile list for theorem-entrypoint modules.

Expected runtime: short-to-medium.

### 4.3 Tier 2 — Executable scenario regression checks

Purpose: validate operational behavior alongside proofs.

Proposed checks:

- run `lake exe sele4n`,
- compare output against approved golden patterns (not necessarily byte-for-byte unless stable),
- include at least one IPC waiting-to-delivery scenario once M3.5 trace lands.

Expected runtime: short.

### 4.4 Tier 3 — Invariant-focused integration checks

Purpose: ensure composed milestone bundles remain coherent under representative transitions.

Proposed checks:

- curated “transition script” scenarios that exercise scheduler + CSpace + IPC flows,
- integration proofs/build targets grouped by bundle (`M1`, `M2`, `M3`, `M3.5`).

Expected runtime: medium.

### 4.5 Tier 4 — Stress/extended checks (CI nightly or manual)

Purpose: catch edge regressions without slowing day-to-day loops.

Proposed checks:

- expanded scenario matrix,
- optional determinism/repeatability checks over repeated executable runs,
- optional future property-based generators for state-transition sequences.

Expected runtime: longest.

---

## 5. Execution model

## 5.1 Standard command interface

Define stable entrypoints so developers and CI use the same commands.

Proposed command families:

- `scripts/test_fast.sh` → Tier 0 + Tier 1 minimal,
- `scripts/test_smoke.sh` → Tier 0 + Tier 1 + Tier 2,
- `scripts/test_full.sh` → all standard tiers except optional nightly,
- `scripts/test_nightly.sh` → Tier 4 extended checks (optional at first).

Implementation note: keep scripts composable and avoid duplicated command logic.

### 5.2 Exit codes and reporting

- Non-zero on first failure by default.
- Optional `--continue` mode to collect all failures for local debugging.
- Prefix output lines with category labels (`[HYGIENE]`, `[BUILD]`, `[TRACE]`, `[INVARIANT]`).

### 5.3 Test data and fixtures

- Keep expected-output fixtures under `tests/fixtures/`.
- Keep scenario scripts under `tests/scenarios/`.
- Prefer minimal, human-readable fixture files.

---

## 6. CI strategy

## 6.1 Pull request gating

Required on every PR:

1. Tier 0 hygiene checks,
2. Tier 1 full build,
3. Tier 2 executable smoke check.

Optional initially, then promoted to required:

4. selected Tier 3 integration checks.

### 6.2 Main-branch/nightly jobs

- run full tier suite,
- run extended Tier 4 checks,
- archive artifacts for trace regressions (logs, output diffs).

### 6.3 Failure policy

- Required jobs block merge on failure.
- Flaky checks must be downgraded or fixed quickly; no prolonged flaky required job.

---

## 7. Proposed rollout plan

### Phase 1 — Baseline framework bootstrap

Deliverables:

- test script skeletons,
- Tier 0 forbidden-marker scan,
- Tier 1 `lake build`,
- Tier 2 `lake exe sele4n` smoke run,
- documentation update in `README.md` + `docs/DEVELOPMENT.md`.

Success criteria:

- one-command local smoke test,
- CI equivalent of local smoke test.

### Phase 2 — Regression fixtures and scenario checks

Deliverables:

- approved output fixtures,
- comparison helper for trace outputs,
- at least one scenario fixture per completed milestone bundle.

Success criteria:

- intentional behavior changes require explicit fixture updates.

### Phase 3 — Invariant-bundle integration harness

Deliverables:

- grouped integration check entrypoints (`M1`, `M2`, `M3`, `M3.5`),
- documentation for adding new invariant checks,
- CI promotion of selected Tier 3 checks to required.

Success criteria:

- regressions are attributable to specific bundle groupings.

### Phase 4 — Extended reliability and maintainability

Deliverables:

- optional nightly matrix/stress jobs,
- performance/runtime tracking over time,
- contributor troubleshooting guide for common failures.

Success criteria:

- predictable maintenance burden with low test flakiness.

---

## 8. Ownership and maintenance model

- Every PR touching transitions/invariants must update or validate relevant tests.
- New milestone slice docs should include test impact notes.
- Test scripts must remain shellcheck-clean (if shellcheck adopted).
- CI config ownership should be explicit in contributor docs.

---

## 9. Risks and mitigations

1. **Risk:** Test runtime becomes too slow.
   - **Mitigation:** tiered model with fast default local path.

2. **Risk:** brittle output comparisons.
   - **Mitigation:** compare structured key lines/patterns over unstable text sections.

3. **Risk:** proof compile and scenario checks diverge in intent.
   - **Mitigation:** require both proof and executable evidence in PR checklist.

4. **Risk:** CI-only logic diverges from local workflows.
   - **Mitigation:** enforce script-based entrypoints used by both CI and contributors.

---

## 10. Definition of done for the framework (v1)

The testing framework v1 is complete when:

1. documented tiered testing model is implemented,
2. local `test_fast` and `test_smoke` commands are stable,
3. CI gates Tier 0/1/2 on PRs,
4. at least one regression fixture-backed scenario is enforced,
5. contributor docs clearly explain how to run, debug, and extend tests.

---

## 11. Immediate next implementation tasks

1. Add script entrypoints for Tier 0/1/2 baseline.
2. Add fixture directory and first executable output expectation file.
3. Wire baseline smoke suite into CI.
4. Update README and development checklist to reference new commands.
5. Add follow-up issue list for Tier 3 and Tier 4 expansion.
