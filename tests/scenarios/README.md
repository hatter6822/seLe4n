# Scenario framework (WS-B11)

This directory is the canonical scenario framework for executable trace replay.

## Scope

The framework now defines and enforces:

- scenario metadata schema (ID, subsystem, risk tags, replay tier, deterministic seed for nightly),
- representative scenario catalog entries tied to stable fixture fragments,
- nightly-seed extraction for deterministic replay,
- ownership and maintenance cadence.

## Files

- `tests/scenarios/scenario_catalog.json`
  - canonical scenario metadata and ownership record.
- `scripts/scenario_catalog.py`
  - `validate`: schema + fixture-anchor verification.
  - `nightly-seeds`: deterministic seed export for nightly replay.

## Metadata contract

Each scenario entry includes:

- `id` — immutable scenario identifier,
- `subsystem` — owning semantic area (ipc, cspace, service, architecture, etc.),
- `risk_tags` — auditable risk classification tags,
- `replay_tier` — `smoke` or `nightly`,
- `deterministic_seed` — required for `nightly` scenarios,
- `expected_trace_fragment` — stable semantic fragment anchored in
  `tests/fixtures/main_trace_smoke.expected`.

## Test integration

- Smoke gate: `scripts/test_smoke.sh` runs catalog validation before Tier 2 trace checks.
- Nightly gate: `scripts/test_tier4_nightly_candidates.sh` validates the catalog,
  materializes nightly seeds from metadata, and replays `trace_sequence_probe` using
  those generated seeds.

## Ownership and maintenance expectations

Owner: `testing-maintainers`

Cadence: `per-slice` (at least once per active slice boundary and on any scenario or
fixture change).

When adding/changing scenarios:

1. update `tests/scenarios/scenario_catalog.json`,
2. update `tests/fixtures/main_trace_smoke.expected` if semantic anchors changed,
3. run:
   ```bash
   python3 scripts/scenario_catalog.py validate
   ./scripts/test_smoke.sh
   NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_tier4_nightly_candidates.sh
   ```
4. document rationale in the active workstream/audit docs.
