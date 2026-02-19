# Development Workflow

## Daily contributor loop

1. Pick one coherent WS-C target (prioritize Phase P1 blockers first).
2. Implement minimal code/proof changes.
3. Run tiered checks from smallest scope upward.
4. Synchronize docs in the same PR.
5. Re-run validations before merge.

## Required validation path

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
```

Optional staged nightly path:

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

Setup reliability note:

- `./scripts/setup_lean_env.sh` retries `apt-get update` with primary distro sources if a third-party mirror is unavailable, reducing bootstrap friction in CI/dev containers.

## Current slice operating rules

For milestone-moving PRs:

- include WS-C ID(s),
- show evidence commands,
- map changes to workstream outcomes,
- record deferrals and owner workstreams,
- keep README/spec/development/GitBook status text synchronized.

## Workstream sequence

- **Phase P0:** WS-C8 baseline reset/documentation synchronization (in progress)
- **Phase P1:** WS-C4 fixture repairs complete (WS-C1 + WS-C2 + WS-C3 + WS-C4 complete)
- **Phase P2:** WS-C5 assurance expansion (completed)
- **Phase P3:** WS-C6 + WS-C7 sustainability hardening

## Failure triage

When checks fail:

1. classify by tier (`HYGIENE`, `BUILD`, `TRACE`, `INVARIANT`),
2. fix semantic/proof root cause first,
3. only then update fixtures or docs if behavior intentionally changed,
4. re-run from smallest relevant tier upward.

## Documentation synchronization rule

Any behavior/proof/slice status change must update all impacted docs in one PR,
including at minimum:

- `README.md`
- `docs/SEL4_SPEC.md`
- `docs/DEVELOPMENT.md`
- affected GitBook chapter(s)
