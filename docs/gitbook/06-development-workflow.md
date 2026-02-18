# Development Workflow

## Daily contributor loop

1. Pick one coherent WS-B target.
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

- include WS-B ID(s),
- show evidence commands,
- map changes to workstream outcomes,
- record deferrals and owner workstreams,
- keep README/spec/development/GitBook status text synchronized.

## Workstream sequence

- **Phase P1:** WS-B4, WS-B3, WS-B8 (WS-B3/WS-B4/WS-B8 completed)
- **Phase P2:** WS-B5, WS-B6, WS-B2 (WS-B1/WS-B2/WS-B5/WS-B6 complete; WS-B7 completed)
- **Phase P3:** WS-B7, WS-B9, WS-B10, WS-B11 (WS-B7/WS-B9 completed)

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
