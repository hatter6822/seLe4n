# CI Policy and Branch-Protection Contract

This document is the canonical WS-A1 policy artifact for CI hardening.

## 1. Required checks (Tier 0–3)

For pull requests into `main`, branch protection should require all of the following checks:

1. `Tiered Tests / Fast (Tier 0 + Tier 1)`
2. `Tiered Tests / Smoke (Tier 0 + Tier 1 + Tier 2)`
3. `Tiered Tests / Full (Tier 0 + Tier 1 + Tier 2 + Tier 3)`

These checks are produced by `.github/workflows/lean_action_ci.yml` and enforce the repository test scripts directly:

- `./scripts/test_fast.sh`
- `./scripts/test_smoke.sh`
- `./scripts/test_full.sh`

## 2. Deterministic replay evidence (Tier 4)

Determinism checks run in the `Nightly Determinism` workflow (`.github/workflows/nightly_determinism.yml`) using:

- `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh`

This includes staged Tier 4 repeat-run replay/diff checks and uploads nightly artifacts from `tests/artifacts/nightly/`.

## 3. Caching and reproducibility policy

CI jobs restore shared caches for:

- `~/.elan`
- `.lake/packages`
- `.lake/build`

Cache keys are derived from `lean-toolchain`, `lake-manifest.json`, `lakefile.toml`, and `scripts/setup_lean_env.sh` so toolchain/dependency/setup changes invalidate stale state.

## 4. Manual branch-protection setup checklist

In GitHub repository settings for `main`:

1. Enable **Require a pull request before merging**.
2. Enable **Require status checks to pass before merging**.
3. Mark these checks as required:
   - `Tiered Tests / Fast (Tier 0 + Tier 1)`
   - `Tiered Tests / Smoke (Tier 0 + Tier 1 + Tier 2)`
   - `Tiered Tests / Full (Tier 0 + Tier 1 + Tier 2 + Tier 3)`
4. Enable **Require branches to be up to date before merging**.
5. Disable direct pushes to `main` for non-admin contributors.

## 5. Failure diagnostics expectations

- Tier 2 failures upload fixture diagnostics as CI artifacts.
- Nightly determinism failures upload replay traces and diffs.
- All tier scripts emit category-labeled output (`META`, `HYGIENE`, `BUILD`, `TRACE`, `INVARIANT`) for fast triage.
