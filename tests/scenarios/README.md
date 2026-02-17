# Test scenarios and fixture maintenance

This directory tracks fixture-backed executable trace checks used by
`scripts/test_tier2_trace.sh`.

## Stage alignment

- Closed baseline: M1–M3.5 (scheduler, capability, IPC handshake coherence).
- Previous completed slices: M4-A, M4-B, M5, and M6.
- Active stage: M7 audit remediation workstreams (WS-A1 through WS-A8), with WS-A4 test architecture expansion now implemented.

## Fixture source

- `tests/fixtures/main_trace_smoke.expected`
  - supports comment lines (`# ...`) and blank lines,
  - expectation lines may be plain fragments or `scenario_id | risk_class | expected_trace_fragment`,
  - matching is line-oriented and order-agnostic on `expected_trace_fragment`.

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
4. Document why fixture changes are expected and which workstream/slice they support (M7 WS-A* IDs).



## Current fixture rationale notes (M7 WS-A4-maintained baseline)

The maintained baseline keeps architecture-boundary adapter trace anchors while retaining prior M5 service-policy closure lines and M4-B lifecycle/IPC anchors:

- `adapter timer success path value` and `adapter read success path byte` pin successful boundary-visible behavior.
- `adapter timer invalid-context branch`, `adapter timer unsupported branch`, and `adapter read denied branch` pin bounded failure semantics.
- `adapter register write success path value` and `adapter register write unsupported branch` pin deterministic register boundary behavior across success/failure branches.
- `service restart status`, `service start denied branch`, `service stop denied branch`, and dependency/isolation lines remain as M5 regression anchors to ensure no service-policy drift while M7 remediation work progresses.

## Historical fixture rationale notes (M4-B closeout baseline)

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
- missing lines with `[TRACE]` prefixes (including scenario/risk metadata when provided),
- reminder to update fixture intentionally when behavior changed by design.

When `TRACE_ARTIFACT_DIR` is set, diagnostics files are written:

- `main_trace_smoke.actual.log`
- `main_trace_smoke.missing.txt`


## WS-A4 traceability additions

- `main_trace_smoke.expected` now supports `scenario_id | risk_class | expected_trace_fragment` entries.
- Tier 2 parser ignores comment/blank lines and reports scenario+risk metadata on failures for faster triage.
- Tier 4 nightly candidates include `trace_sequence_probe` seeded sequence-diversity runs to add stochastic/property-style IPC state-consistency checking.
