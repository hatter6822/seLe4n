# Contributing to seLe4n

Thanks for contributing to seLe4n.

## 5-minute onboarding path

If you are new to the repository, read these in order:

1. **Project scope and milestones:** [`docs/spec/SELE4N_SPEC.md`](docs/spec/SELE4N_SPEC.md)
2. **Development workflow:** [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)
3. **Testing tiers and CI contract:** [`docs/TESTING_FRAMEWORK_PLAN.md`](docs/TESTING_FRAMEWORK_PLAN.md)
4. **CI required checks policy:** [`docs/CI_POLICY.md`](docs/CI_POLICY.md)
5. **Active workstream plan:** [`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md)

For the upstream seL4 microkernel reference: [`docs/spec/SEL4_SPEC.md`](docs/spec/SEL4_SPEC.md).

For a full chapter map, use the handbook index in [`docs/gitbook/README.md`](docs/gitbook/README.md).

## Quick setup

```bash
./scripts/setup_lean_env.sh
lake build
lake exe sele4n
```

## Required validation before opening a PR

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
```

Recommended additional validation:

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

## PR discipline

Every milestone-moving PR should include:

1. workstream ID(s) advanced,
2. validation evidence (commands run + output),
3. synchronized documentation updates,
4. explicit deferrals (if any) and destination workstream.

Use the [PR template](.github/pull_request_template.md) checklist.

## Documentation synchronization

For changes that alter behavior, theorem surfaces, or slice status, update in the same PR:

1. `README.md`
2. `docs/spec/SELE4N_SPEC.md`
3. `docs/DEVELOPMENT.md`
4. impacted GitBook chapter(s)
5. any directly affected audit/workstream status document

See [`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md) for the full cross-document synchronization index.
