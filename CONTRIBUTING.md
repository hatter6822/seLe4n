# Contributing to seLe4n

Thanks for contributing to seLe4n.

## 5-minute contributor path (WS-A6)

If you are new to the repository, use this order:

1. **Workflow + standards:** [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)
2. **Testing tiers + expectations:** [`docs/TESTING_FRAMEWORK_PLAN.md`](docs/TESTING_FRAMEWORK_PLAN.md)
3. **CI required checks policy:** [`docs/CI_POLICY.md`](docs/CI_POLICY.md)
4. **Current M7 slice outcomes:** [`docs/gitbook/21-m7-current-slice-outcomes-and-workstreams.md`](docs/gitbook/21-m7-current-slice-outcomes-and-workstreams.md)
5. **Execution workstream definitions:** [`docs/AUDIT_REMEDIATION_WORKSTREAMS.md`](docs/AUDIT_REMEDIATION_WORKSTREAMS.md)

For a full chapter map, use the handbook index in [`docs/gitbook/README.md`](docs/gitbook/README.md).

The canonical development workflow, validation loop, and PR checklist live in:

- [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)

For CI/branch-protection policy (WS-A1), see:

- [`docs/CI_POLICY.md`](docs/CI_POLICY.md)

Quick required validation before opening a PR:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
```

Recommended additional validation:

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```
