# CI Maturity and Telemetry Baseline (WS-B10)

Canonical source: [`docs/CI_TELEMETRY_BASELINE.md`](../CI_TELEMETRY_BASELINE.md).

## What WS-B10 added

- command-level CI timing capture (`scripts/ci_capture_timing.sh`),
- repeated-lane flake probe logging (`scripts/ci_flake_probe.sh`),
- telemetry artifact uploads from Lean CI lanes, nightly, and ARM64 fast-gate lanes,
- weekly Lean toolchain drift proposal automation and Dependabot tracking,
- explicit CodeQL policy rationale (informational/non-blocking) in `docs/CI_POLICY.md`.

## Where to inspect telemetry

- CI artifacts under `.ci-artifacts/telemetry/`,
- `timing.jsonl` for durations and exits,
- `flake_probe.jsonl` + `flake_summary.txt` for repeat-run stability signals.

## Policy

Treat this page as a navigational mirror; update the canonical root doc first,
then keep this chapter synchronized in the same PR.
