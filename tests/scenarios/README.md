# Test scenarios and fixture maintenance

This directory tracks fixture-backed executable trace checks used by
`scripts/test_tier2_trace.sh`.

## Stage alignment

- Closed baseline: M1-M3.5 (scheduler, capability, IPC handshake coherence).
- Active stage: M4-A lifecycle/retype foundations.
- Next stage: M4-B lifecycle-capability composition hardening.

## Fixture source

- `tests/fixtures/main_trace_smoke.expected`
  - each non-empty line is a required output substring,
  - matching is line-oriented and order-agnostic.

## Intentional update workflow

1. Run executable:
   ```bash
   source "$HOME/.elan/env"
   lake exe sele4n
   ```
2. Update fixture with stable semantic fragments only.
3. Re-run:
   ```bash
   ./scripts/test_tier2_trace.sh
   ./scripts/test_smoke.sh
   ```
4. Document why fixture changes are expected and which slice they support (M4-A or M4-B).

## Diagnostics behavior

On mismatch, Tier 2 reports:

- expected vs matched fragment counts,
- missing lines with `[TRACE]` prefixes,
- reminder to update fixture intentionally when behavior changed by design.

When `TRACE_ARTIFACT_DIR` is set, diagnostics files are written:

- `main_trace_smoke.actual.log`
- `main_trace_smoke.missing.txt`
