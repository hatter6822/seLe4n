# seLe4n Testing Framework Implementation Plan (Implementation-Ready)

## 1. Purpose

## 1.1 Implementation status snapshot

Current repository status against this plan:

- ✅ Work package A (script scaffold) is implemented.
- ✅ Work package B (fixture-backed executable smoke baseline) is implemented.
- ✅ Work package C (CI wiring to script entrypoints) is implemented.
- ✅ Work package D (final doc integration pass) is implemented and tracks script/CI reality.
- ⏳ Work package E (Tier 3 hooks) is partially prepared via explicit extension points.

---

This document is the implementation-ready plan for building and enforcing a tiered testing
framework for seLe4n. It translates testing goals into concrete files, scripts, CI jobs,
acceptance criteria, and rollout steps so contributors can begin implementation immediately.

The framework complements Lean theorem checks with executable-behavior regression coverage,
hygiene gates, and contributor-friendly workflows.

---

## 2. Outcomes and non-negotiable quality bar

The framework is successful only if it guarantees all of the following:

1. **Proof surface stability**
   - Existing milestone theorem entrypoints continue to compile via `lake build`.
   - Core modules do not gain new `axiom`, `sorry`, or unresolved work markers in committed code.

2. **Executable behavior stability**
   - `Main.lean` runnable trace (`lake exe sele4n`) remains operational.
   - Deterministic, reviewed output expectations guard against accidental behavior drift.

3. **Milestone regression resistance**
   - M1/M2/M3 guarantees remain enforced while M3.5 evolves.
   - Integration checks are grouped by invariant bundle boundary (M1/M2/M3/M3.5).

4. **Fast local loop + deterministic CI gate**
   - Contributors can run a <2 minute default local suite.
   - CI uses the exact same script entrypoints as local development.

5. **Actionable failures**
   - Failing checks clearly identify class and location of regression (`HYGIENE`, `BUILD`, `TRACE`,
     `INVARIANT`, `CI-CONFIG`).

---

## 3. Scope definition

### 3.1 In scope (v1)

- Scripted test entrypoints under `scripts/` for all baseline tiers.
- Fixture-backed executable smoke regression checks.
- CI workflow updates to run required tiers on pull requests.
- Documentation updates (README + development guide + this plan).
- Contributor and reviewer checklist alignment.

### 3.2 Out of scope (v1)

- Full performance benchmark dashboards.
- Architecture matrix or hardware-specific execution matrix.
- Property-based random transition generation infrastructure.

---

## 4. Target architecture

## 4.1 Directory and file layout to create

```
scripts/
  test_lib.sh                  # shared helpers (logging, fail/exit behavior)
  test_tier0_hygiene.sh        # marker scans, structural checks
  test_tier1_build.sh          # lake build gates
  test_tier2_trace.sh          # exe + fixture comparison
  test_fast.sh                 # Tier 0 + Tier 1 (default local pre-commit)
  test_smoke.sh                # Tier 0 + Tier 1 + Tier 2 (required PR gate)
  test_full.sh                 # smoke + integration hooks (Tier 3 when enabled)
  test_nightly.sh              # optional Tier 4 expansion

tests/
  fixtures/
    main_trace_smoke.expected  # approved key-line expectations
  scenarios/
    README.md                  # how to add scenario fixtures/checks

.github/workflows/
  lean_action_ci.yml           # updated to run script entrypoints
```

## 4.2 Tier model and required checks

### Tier 0 — Hygiene/structural checks (required)

Checks:
- Marker scan command: `rg -n "axiom|sorry|TODO" SeLe4n Main.lean`.
- Optional shell script lint hook (only if shellcheck is present in environment).

Pass criteria:
- No forbidden marker matches in scope.

### Tier 1 — Build/theorem compile checks (required)

Checks:
- `lake build`.

Pass criteria:
- Full compile succeeds with zero errors.

### Tier 2 — Executable regression smoke (required)

Checks:
- Run `lake exe sele4n` and capture output.
- Compare selected stable lines against `tests/fixtures/main_trace_smoke.expected`.

Pass criteria:
- Command exits successfully.
- Fixture comparison helper reports no mismatches.

### Tier 3 — Invariant-bundle integration checks (initially optional, then required)

Checks:
- Bundle-focused integration entrypoints grouped by `M1`, `M2`, `M3`, `M3.5`.

Pass criteria:
- Selected integration groups succeed in CI.

### Tier 4 — Extended/nightly checks (optional)

Checks:
- Repeat-run determinism checks.
- Larger scenario matrix.

Pass criteria:
- Nightly signal remains stable; failures create issues and are triaged.

---

## 5. Script contract (implementation detail)

## 5.1 Common behavior for all scripts

All scripts must:
- Use `set -euo pipefail`.
- Resolve repository root reliably (work when run from any cwd inside repo).
- Print section-prefixed logs:
  - `[HYGIENE]`
  - `[BUILD]`
  - `[TRACE]`
  - `[INVARIANT]`
  - `[META]`
- Exit non-zero on first failure by default.
- Support `--continue` mode for aggregated local diagnostics (best effort: run all checks and
  summarize failed categories at end).

## 5.2 `scripts/test_lib.sh` helper API (minimum)

Implement reusable helpers:
- `log_section <CATEGORY> <message>`
- `run_check <CATEGORY> <command...>`
- `record_failure <CATEGORY> <message>`
- `finalize_report` (handles `--continue` summary and exit code)

This avoids duplicated error handling across tier scripts.

## 5.3 Tier entrypoint responsibilities

- `test_tier0_hygiene.sh`: marker scan + optional structural checks.
- `test_tier1_build.sh`: build check only.
- `test_tier2_trace.sh`: executable run, capture, fixture compare.
- `test_fast.sh`: call Tier 0 then Tier 1.
- `test_smoke.sh`: call Tier 0 → Tier 1 → Tier 2.
- `test_full.sh`: smoke + Tier 3 hooks.
- `test_nightly.sh`: full + Tier 4 extended checks.

---

## 6. Fixture and comparison strategy

## 6.1 Fixture design constraints

- Keep fixtures concise and human-reviewable.
- Compare stable semantic lines, not fragile timestamps/format noise.
- Use deterministic ordering if output can be re-sequenced.

## 6.2 `main_trace_smoke.expected` format (v1)

Line-oriented expected fragments, one per line, e.g.:

```
[TRACE] Scheduler transition succeeded
[TRACE] CSpace mint succeeded
[TRACE] Endpoint send/receive path succeeded
```

(Use actual current `lake exe sele4n` output during implementation.)

## 6.3 Comparison policy

- Substring/contains matching per expected line (not full-file byte equality).
- Report missing lines with context and suggested action:
  - if intended behavior change: update fixture in same PR with rationale.
  - if unintended: fix code.

---

## 7. CI implementation blueprint

## 7.1 Pull request required checks (v1)

Update `.github/workflows/lean_action_ci.yml` to run:

1. `./scripts/test_fast.sh`
2. `./scripts/test_smoke.sh`

(If runtime is redundant, smoke may subsume fast; keep both only if they provide distinct signal.)

Status: implemented in `.github/workflows/lean_action_ci.yml` with explicit `test-fast` and
`test-smoke` jobs.

## 7.2 Main/nightly follow-up checks

Add separate jobs (or future workflow file) for:
- `./scripts/test_full.sh`
- `./scripts/test_nightly.sh` (scheduled)

Artifacts to upload on trace failure:
- actual output log,
- expected fixture,
- diff report.

## 7.3 CI failure policy

- Required jobs block merge.
- Any flaky required job must be fixed or downgraded within 48 hours.
- CI logic must call repository scripts directly; avoid inlining test commands in workflow YAML.

---

## 8. Implementation backlog (ordered, directly actionable)

## 8.1 Work package A — Script scaffold (day 1)

Tasks:
1. Create `scripts/test_lib.sh` with shared logging/runner helpers.
2. Create Tier 0/1/2 scripts and orchestration scripts (`test_fast.sh`, `test_smoke.sh`,
   `test_full.sh`, `test_nightly.sh`).
3. Add executable permissions (`chmod +x`).

Acceptance criteria:
- Each script runs independently.
- `./scripts/test_fast.sh` executes Tier 0 + Tier 1 in order.
- `./scripts/test_smoke.sh` executes Tier 0 + Tier 1 + Tier 2 in order.

## 8.2 Work package B — Fixture baseline (day 1-2)

Tasks:
1. Create `tests/fixtures/` and `tests/scenarios/README.md`.
2. Capture current `lake exe sele4n` output.
3. Derive and commit `main_trace_smoke.expected` containing stable semantic lines.
4. Implement fixture comparison logic in `test_tier2_trace.sh`.

Acceptance criteria:
- Tier 2 passes on current baseline branch.
- Artificially removing one expected line triggers deterministic failure.
- Failure output reports missing expectation lines and fixture-update guidance.

## 8.3 Work package C — CI wiring (day 2)

Tasks:
1. Update `.github/workflows/lean_action_ci.yml` to run smoke gate scripts.
2. Ensure script paths and permissions are valid in CI.
3. Emit readable grouped logs with category prefixes.

Acceptance criteria:
- PR workflow fails when any tier script fails.
- CI and local script behavior match for pass/fail outcomes.

Implementation status:
- `.github/workflows/lean_action_ci.yml` runs `./scripts/test_fast.sh` and `./scripts/test_smoke.sh` as separate jobs on `pull_request`, with smoke depending on fast.

## 8.4 Work package D — Documentation integration (day 2)

Tasks:
1. Update `README.md` with test command quick reference.
2. Update `docs/DEVELOPMENT.md` validation loop to reference script entrypoints.
3. Add “how to update fixture intentionally” section to `tests/scenarios/README.md`.

Acceptance criteria:
- New contributor can run documented commands without reading CI YAML.
- Docs and scripts reference identical command names.

## 8.5 Work package E — Tier 3 hook preparation (day 3, optional in initial PR)

Tasks:
1. Stub `test_tier3_invariants.sh` or Tier 3 section in `test_full.sh` behind feature flag.
2. Add TODO issue list for M1/M2/M3/M3.5 grouped checks.

Acceptance criteria:
- `test_full.sh` has explicit extension point for integration checks.

---

## 9. Definition of done (v1 launch gate)

The framework v1 is complete when all conditions below hold:

1. `scripts/test_fast.sh` and `scripts/test_smoke.sh` are implemented and stable.
2. Tier 0/1/2 checks are enforced in PR CI.
3. At least one fixture-backed executable regression check is active.
4. Contributor docs explain run/debug/update workflows.
5. Regression failures are category-labeled and actionable.

---

## 10. PR checklist for testing-framework implementation

Copy into implementation PR(s):

- [ ] Added script entrypoints for Tier 0/1/2.
- [ ] Added shared script helper library (or equivalent dedup strategy).
- [ ] Added fixture directory and baseline expected trace file.
- [ ] Implemented trace comparison and clear mismatch diagnostics.
- [ ] Updated CI workflow to call repository test scripts.
- [ ] Updated README and development docs.
- [ ] Ran local verification commands listed below.

Required local verification commands before merging:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
lake build
lake exe sele4n
```

---

## 11. Risks and mitigations (implementation-phase)

1. **Risk: fixture brittleness causes false failures.**
   - Mitigation: assert stable semantic substrings, not volatile formatting.

2. **Risk: duplicated logic across scripts drifts over time.**
   - Mitigation: centralize runner/logging behavior in `test_lib.sh`.

3. **Risk: CI and local checks diverge.**
   - Mitigation: CI invokes same scripts, no bespoke workflow-only commands.

4. **Risk: runtime inflation hurts contributor productivity.**
   - Mitigation: keep fast tier minimal; move heavy checks to full/nightly tiers.

5. **Risk: unclear ownership of failing tests.**
   - Mitigation: assign default ownership in `docs/DEVELOPMENT.md` for CI/test maintenance.
