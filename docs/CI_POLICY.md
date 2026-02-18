# CI Policy and Branch-Protection Contract

This document is the canonical CI policy artifact for WS-A1 and WS-A8 maturity gates.

## 1. Required checks (Tier 0–3)

For pull requests into `main`, branch protection should require all of the following checks:

1. `Docs Automation / Navigation + Links + DocGen Probe`
2. `Tiered Tests / Fast (Tier 0 + Tier 1)`
3. `Tiered Tests / Smoke (Tier 0 + Tier 1 + Tier 2)`
4. `Tiered Tests / Full (Tier 0 + Tier 1 + Tier 2 + Tier 3)`

These checks are produced by `.github/workflows/lean_action_ci.yml` and enforce the repository scripts directly:

- `./scripts/test_docs_sync.sh`
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
   - `Docs Automation / Navigation + Links + DocGen Probe`
   - `Tiered Tests / Fast (Tier 0 + Tier 1)`
   - `Tiered Tests / Smoke (Tier 0 + Tier 1 + Tier 2)`
   - `Tiered Tests / Full (Tier 0 + Tier 1 + Tier 2 + Tier 3)`
4. Enable **Require branches to be up to date before merging**.
5. Disable direct pushes to `main` for non-admin contributors.

## 5. Failure diagnostics expectations

- Tier 2 failures upload fixture diagnostics as CI artifacts.
- Nightly determinism failures upload replay traces and diffs.
- All tier scripts emit category-labeled output (`META`, `HYGIENE`, `BUILD`, `TRACE`, `INVARIANT`) for fast triage.

## 6. Platform and security baseline gates (WS-A8)

The `Platform and Security Baseline` workflow (`.github/workflows/platform_security_baseline.yml`) provides:

1. **Architecture-targeted CI signal** via `Platform Signal / ARM64 Fast Gate` on `ubuntu-24.04-arm` running `./scripts/test_fast.sh`.
2. **Automated baseline security scanning** via `Security Signal / Secret + Dependency + CodeQL`, including:
   - Gitleaks secret scanning,
   - Trivy filesystem vulnerability scanning (HIGH/CRITICAL severities),
   - CodeQL analysis for GitHub Actions workflows.

This workflow runs on pull requests, pushes to `main`, weekly schedule, and manual dispatch.
For fork-origin pull requests, the security-scan job is conditionally skipped because `security-events: write` permissions are unavailable in that context; architecture-targeted fast-gate coverage still runs.
The workflow permissions include `pull-requests: read` so the Gitleaks PR commit-diff scan path can read pull request commits without `Resource not accessible by integration` failures.
The security scan job performs a full-history checkout (`actions/checkout` with `fetch-depth: 0`) so Gitleaks PR commit-range scans do not fail with ambiguous revision errors on shallow clones.
CodeQL analysis remains in the workflow for baseline static checks, but the analyze upload step is marked `continue-on-error` so repositories without Code Scanning enabled do not hard-fail the entire security lane.


## 7. WS-B9 threat-model baseline linkage

Threat assumptions and trust-boundary controls for setup/bootstrap and repository hygiene are
tracked in [`docs/THREAT_MODEL.md`](./THREAT_MODEL.md).

The setup bootstrap path now requires checksum verification for the downloaded elan installer
(`scripts/setup_lean_env.sh`: `ELAN_INSTALLER_SHA256`) before execution.
