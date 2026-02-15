# Test scenarios and fixture maintenance

This directory documents fixture-backed trace checks for `scripts/test_tier2_trace.sh` and how to
keep them aligned with the active milestone stage.

## Current stage alignment

- Most recently closed slice: **M3.5 IPC handshake + scheduler interaction**.
- Fixture expectations preserve stable M1/M2/M3 behavior while capturing intentional M3.5
  executable semantics (including waiting-receiver handshake evidence).

## Current fixture

- `tests/fixtures/main_trace_smoke.expected`
  - line-oriented expected *substrings* for `lake exe sele4n` smoke trace,
  - each non-empty line must appear somewhere in actual output.

## Intentional fixture update workflow

When executable behavior changes intentionally:

1. Run executable and inspect output:
   ```bash
   source "$HOME/.elan/env"
   lake exe sele4n
   ```
2. Update `tests/fixtures/main_trace_smoke.expected` with stable semantic lines only
   (avoid timestamps/ordering-noise-sensitive strings).
3. Re-run:
   ```bash
   ./scripts/test_tier2_trace.sh
   ./scripts/test_smoke.sh
   ```
4. In PR description, explain why fixture changes are expected and which milestone slice they
   correspond to (current slice vs next slice prep).

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
- reminder to update fixture + PR rationale when drift is intentional.

This keeps smoke regressions deterministic and reviewable in local runs and CI logs.

## CI trace artifacts

CI can set `TRACE_ARTIFACT_DIR` when running `./scripts/test_tier2_trace.sh`. When set, the script
writes:

- `main_trace_smoke.actual.log` (captured executable output),
- `main_trace_smoke.missing.txt` (one missing expectation per line).

PR workflow uploads those files plus expected fixture on failure.
