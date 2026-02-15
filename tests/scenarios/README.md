# Test scenarios and fixture maintenance

This directory documents fixture-backed trace checks for `scripts/test_tier2_trace.sh`.

## Current fixture

- `tests/fixtures/main_trace_smoke.expected`
  - line-oriented expected *substrings* for the `lake exe sele4n` smoke trace.
  - each non-empty line must appear somewhere in actual output.

## Intentional fixture update workflow

When executable behavior changes intentionally:

1. Run the executable and inspect output:
   ```bash
   source "$HOME/.elan/env"
   lake exe sele4n
   ```
2. Update `tests/fixtures/main_trace_smoke.expected` with stable semantic lines only
   (avoid timestamps / ordering-noise-sensitive strings).
3. Re-run:
   ```bash
   ./scripts/test_tier2_trace.sh
   ./scripts/test_smoke.sh
   ```
4. In your PR description, explain why fixture changes are expected.

## Control-data audit tip

Use an intentionally bad fixture line to verify deterministic failure behavior:

```bash
TMP_FIXTURE="$(mktemp)"
cp tests/fixtures/main_trace_smoke.expected "$TMP_FIXTURE"
echo "this line should never match" >> "$TMP_FIXTURE"
TRACE_FIXTURE_PATH="$TMP_FIXTURE" ./scripts/test_tier2_trace.sh
```

The command should fail and report the missing expected line.

## Failure diagnostics contract

`./scripts/test_tier2_trace.sh` reports:

- total matched vs expected fragment count,
- each missing expected fragment on its own `[TRACE]` line,
- a reminder to update fixture + PR rationale when drift is intentional.

This contract keeps smoke regressions deterministic and reviewable in both local runs and CI logs.

## CI trace artifacts

CI can set `TRACE_ARTIFACT_DIR` when running `./scripts/test_tier2_trace.sh`. When set, the script
writes:

- `main_trace_smoke.actual.log` (captured executable output),
- `main_trace_smoke.missing.txt` (one missing expectation per line).

The pull-request workflow uploads those files plus the expected fixture on failure.
