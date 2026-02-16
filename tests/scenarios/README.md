# Test scenarios and fixture maintenance

This directory tracks fixture-backed executable trace checks used by
`scripts/test_tier2_trace.sh`.

## Stage alignment

- Closed baseline: M1-M3.5 (scheduler, capability, IPC handshake coherence).
- Active stage: M5 service-graph + policy surface development.
- Previous stage (closed): M4-B lifecycle-capability composition hardening (WS-A..WS-E complete).

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
4. Document why fixture changes are expected and which slice they support (M4-B closeout or M5 execution).


## Current fixture rationale notes (M4-B closeout baseline)

The smoke fixture captures stable semantic anchors rather than formatting-dependent text:

- `lifecycle retype unauthorized branch` and `lifecycle retype illegal-state branch` prove lifecycle
  failure branches stay externally visible in the executable trace.
- `composed transition alias guard (expected error)` and
  `composed transition unauthorized branch` prove the composed lifecycle+capability helper rejects both
  state-aliasing misuse and authority misuse.
- `composed revoke/delete/retype success` proves the positive composition path still executes after
  failure probes.
- `post-revoke sibling lookup` and `post-delete lookup (expected error)` prove cleanup side-effects are
  observable and stable.

If any fragment changes, update `tests/fixtures/main_trace_smoke.expected` in the same PR and add a
short rationale entry describing why the changed fragment still represents stable semantics.

## Diagnostics behavior

On mismatch, Tier 2 reports:

- expected vs matched fragment counts,
- missing lines with `[TRACE]` prefixes,
- reminder to update fixture intentionally when behavior changed by design.

When `TRACE_ARTIFACT_DIR` is set, diagnostics files are written:

- `main_trace_smoke.actual.log`
- `main_trace_smoke.missing.txt`
