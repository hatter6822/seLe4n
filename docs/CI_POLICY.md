# CI Policy and Branch-Protection Contract

This document is the canonical CI policy artifact for WS-A1, WS-A8, and WS-B10 CI maturity gates.

## 1. Required checks (Tier 0–3)

For pull requests into `main`, branch protection should require all of the following checks:

1. `Tiered Tests / Fast (Tier 0 + Tier 1)`
2. `Tiered Tests / Smoke (Tier 2)`
3. `Tiered Tests / Full (Tier 3)`

These checks are produced by `.github/workflows/lean_action_ci.yml`. Each CI job runs only its incremental tier; earlier tiers are gated by job dependencies:

- `test-fast`: `./scripts/test_fast.sh` (Tier 0 + Tier 1)
- `test-smoke` (after test-fast): `./scripts/test_tier2_trace.sh` + `./scripts/test_tier2_negative.sh`
- `test-full` (after test-smoke): `./scripts/test_tier3_invariant_surface.sh`

Documentation sync (`./scripts/test_docs_sync.sh`) is available for local use but is not part of CI gates.

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
   - `Tiered Tests / Smoke (Tier 2)`
   - `Tiered Tests / Full (Tier 3)`
4. Enable **Require branches to be up to date before merging**.
5. Disable direct pushes to `main` for non-admin contributors.

## 5. Failure diagnostics expectations

- Tier 2 failures upload fixture diagnostics as CI artifacts.
- Nightly determinism failures upload replay traces and diffs.
- All tier scripts emit category-labeled output (`META`, `HYGIENE`, `BUILD`, `TRACE`, `INVARIANT`) for fast triage.
- WS-B10 telemetry artifacts must be uploaded from CI lanes to `.ci-artifacts/telemetry/` and include `timing.jsonl` entries produced by `scripts/ci_capture_timing.sh`.
- Nightly telemetry must include repeat-run flake probe output (`flake_probe.jsonl`, `flake_summary.txt`) produced by `scripts/ci_flake_probe.sh`.

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


## 8. WS-B10 CodeQL policy decision

CodeQL remains **informational/non-blocking** in the security baseline workflow.

Rationale:

1. repository-level Code Scanning enablement is not guaranteed in every execution environment,
2. failing hard on analyze upload would create false-negative CI reliability without improving code correctness signal,
3. Gitleaks + Trivy still provide hard-fail security gates for secrets and HIGH/CRITICAL findings.

Re-evaluation trigger:

- Once Code Scanning availability is guaranteed for this repository across required environments, `continue-on-error` should be removed and CodeQL promoted to a required blocking gate.

## 9. WS-E1 GitHub Actions SHA-pinning policy (F-14)

All third-party GitHub Actions in workflow files must be pinned to full 40-character
commit SHA hashes, not mutable version tags. Each `uses:` reference carries a
trailing `# vX.Y.Z` comment documenting the version at pin time.

Covered workflows:
- `.github/workflows/lean_action_ci.yml`
- `.github/workflows/nightly_determinism.yml`
- `.github/workflows/lean_toolchain_update_proposal.yml`
- `.github/workflows/platform_security_baseline.yml`

Tier 0 hygiene (`test_tier0_hygiene.sh`) includes a regression guard that fails if
any workflow action reference is not SHA-pinned.

## 10. WS-B10 toolchain update automation

Toolchain-update cadence is automated through:

- `.github/dependabot.yml` for GitHub Actions dependency updates,
- `.github/workflows/lean_toolchain_update_proposal.yml` for weekly Lean release drift proposals (issue creation when `lean-toolchain` lags upstream).

## 11. WS-B10 timing + flake telemetry baseline

Canonical telemetry baseline documentation is published in `docs/CI_TELEMETRY_BASELINE.md`
with GitBook mirror `docs/gitbook/29-ci-maturity-and-telemetry-baseline.md`.
