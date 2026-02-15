# Testing and CI

## Tier model

- **Tier 0 (hygiene)**
  - marker scan for forbidden placeholders (`axiom|sorry|TODO`) in tracked proof surface,
  - optional shell-quality checks.
- **Tier 1 (build/proof compile)**
  - full `lake build` to verify definitions, theorem scripts, and module integration.
- **Tier 2 (trace/behavior)**
  - executable scenario (`lake exe sele4n`) checked against stable fixture fragments.
- **Tier 3 (invariant and documentation anchor surface)**
  - validates critical theorem/bundle/doc anchors expected for active milestone slices.
- **Tier 4 (nightly extension point)**
  - explicitly reserved for heavier future checks.

## Entrypoints and intent

- `./scripts/test_fast.sh`
  - fast local confidence gate (Tier 0 + Tier 1).
- `./scripts/test_smoke.sh`
  - semantic smoke path (Tier 0 + Tier 1 + Tier 2).
- `./scripts/test_full.sh`
  - broader local verification (smoke + Tier 3 anchor coverage).
- `./scripts/test_nightly.sh`
  - full + nightly extension placeholder.

CI should execute these repository scripts directly to avoid local/CI drift.

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

## M4 testing trajectory

- **M4-A:** add lifecycle semantic trace fragments once lifecycle scenarios land.
- **M4-B:** add lifecycle-capability composition success/failure traces and stronger Tier 3 anchors.

## Practical failure triage

- **Tier 0 fails:** remove placeholder markers or fix script-level lint/hygiene issues.
- **Tier 1 fails:** resolve first Lean compile/proof failure before chasing downstream errors.
- **Tier 2 fails:** inspect missing fixture lines and decide if behavior change was accidental or
  intentional.
- **Tier 3 fails:** verify theorem/bundle/doc anchor names are still present after refactor.
