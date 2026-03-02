# Development Workflow

Canonical source: [`docs/DEVELOPMENT.md`](../DEVELOPMENT.md).

## Daily contributor loop

1. Pick one coherent WS-G target (prioritize current phase workstreams).
2. Implement minimal code/proof changes.
3. Run tiered checks from smallest scope upward.
4. Synchronize docs in the same PR.
5. Re-run validations before merge.

## Required validation path

```bash
./scripts/test_fast.sh      # Tier 0+1 (hygiene + build)
./scripts/test_smoke.sh     # Tier 0-2 (+ trace + negative-state)
./scripts/test_full.sh      # Tier 0-3 (+ invariant surface anchors)
```

Optional nightly:

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

## Current slice operating rules

For milestone-moving PRs:

- include WS-F workstream ID(s) (WS-F1..F8),
- show evidence commands,
- map changes to workstream outcomes,
- record deferrals and destination workstreams,
- keep README/spec/development/GitBook status text synchronized.

## Active workstream sequence (WS-F)

| Phase | Workstreams | Description |
|-------|-------------|-------------|
| **P0** | — | Publish WS-F backbone, update docs |
| **P1** | WS-F1, WS-F2, WS-F4 | Critical IPC/memory + proof gaps (**WS-F1, WS-F2 completed**) |
| **P2** | WS-F3 | Information-flow completeness (**Completed**) |
| **P3** | WS-F5, WS-F6 | Model fidelity + invariant quality |
| **P4** | WS-F7, WS-F8 | Testing + cleanup |

See [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) for details.

## Failure triage

When checks fail:

1. classify by tier (`HYGIENE`, `BUILD`, `TRACE`, `INVARIANT`),
2. fix semantic/proof root cause first,
3. only then update fixtures or docs if behavior intentionally changed,
4. re-run from smallest relevant tier upward.

## Documentation synchronization rule

Any behavior/proof/slice status change must update all impacted docs in one PR:

- `README.md`
- `docs/spec/SELE4N_SPEC.md`
- `docs/DEVELOPMENT.md`
- affected GitBook chapter(s)
