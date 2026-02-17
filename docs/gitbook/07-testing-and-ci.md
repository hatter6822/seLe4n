# Testing and CI

## Tier model

- **Tier 0 (hygiene)**
  - marker scan for forbidden placeholders (`axiom|sorry|TODO`) in tracked proof surface,
  - optional shell-quality checks.
- **Tier 1 (build/proof compile)**
  - full `lake build` to verify definitions, theorem scripts, and module integration.
- **Tier 2 (trace/behavior)**
  - executable scenario (`lake exe sele4n`) checked against stable fixture fragments,
  - fixture lines support scenario/risk tags (`scenario_id | risk_class | expected_trace_fragment`) for audit traceability.
- **Tier 3 (invariant and documentation anchor surface)**
  - validates critical theorem/bundle/doc anchors expected for active milestone slices,
  - includes executable-trace anchor checks for milestone-critical lifecycle fragments.
- **Tier 4 (nightly staged extension candidates)**
  - `./scripts/test_tier4_nightly_candidates.sh` stages repeat-run determinism + full-suite replay candidates,
  - includes seeded `trace_sequence_probe` sequence-diversity checks in experimental mode,
  - default remains explicit extension-point behavior unless `NIGHTLY_ENABLE_EXPERIMENTAL=1` is set.

## Entrypoints and intent

- `./scripts/test_fast.sh`
  - fast local confidence gate (Tier 0 + Tier 1).
- `./scripts/test_smoke.sh`
  - semantic smoke path (Tier 0 + Tier 1 + Tier 2).
- `./scripts/test_full.sh`
  - broader local verification (smoke + Tier 3 anchor coverage).
- `./scripts/test_nightly.sh`
  - full + Tier 4 staged-candidate wrapper (explicit opt-in by environment flag).

CI should execute these repository scripts directly to avoid local/CI drift.

Required branch-protection checks and reproducible setup instructions are documented in [`docs/CI_POLICY.md`](../CI_POLICY.md).

## Shared test library behavior

All test entrypoints use `scripts/test_lib.sh` for:

1. common argument handling (`--continue`),
2. command execution wrappers (`run_check`),
3. centralized pass/fail accounting and final report,
4. optional automatic Lean setup helper path if `lake` is missing.

### Color-coded prefixes

The shared logger now colorizes output when running in an interactive terminal:

- category prefix colors (`[META]`, `[TRACE]`, `[HYGIENE]`, `[BUILD]`, `[INVARIANT]`),
- message-status colors for `RUN`, `PASS`, and `FAIL`,
- automatic fallback to plain text when output is non-interactive or `NO_COLOR` is set.

This keeps CI output clean while making local debugging much easier to scan.

## Why fixture checks matter

Type-checking alone can miss semantic regressions. Tier 2 fixture checks ensure critical runtime
stories remain visible and intentional, especially for milestone claims tied to executable behavior
(e.g., mint/revoke/delete and IPC handshake flows).

## M4-B and M5 closeout testing trajectory

- **M4-A:** lifecycle semantic trace fragments are landed and fixture-backed in Tier 2 smoke coverage.
- **M4-B:** WS-A/WS-B/WS-C/WS-D/WS-E are complete, including Tier 3 M4-B symbol anchors and staged Tier 4 nightly candidates.
- **M5 (complete; WS-M5-F complete):** Tier 2/Tier 3 cover service restart/policy-denial/dependency-failure/isolation evidence, with Tier 4 candidates checking determinism plus M5 evidence-line anchors as preserved baselines for M6.

## Practical failure triage

- **Tier 0 fails:** remove placeholder markers or fix script-level lint/hygiene issues.
- **Tier 1 fails:** resolve first Lean compile/proof failure before chasing downstream errors.
- **Tier 2 fails:** inspect missing fixture lines and decide if behavior change was accidental or
  intentional.
- **Tier 3 fails (`./scripts/test_tier3_invariant_surface.sh`):** verify theorem/bundle/doc anchor names are still present after refactor, then repair the exact missing anchor in the referenced file.
- **Tier 4 fails (`./scripts/test_nightly.sh` / `./scripts/test_tier4_nightly_candidates.sh`):** inspect `tests/artifacts/nightly/` traces + determinism diff and decide whether the drift is semantic regression or an intentional behavior change that needs fixture/doc updates.
