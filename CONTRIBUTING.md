# Contributing to seLe4n

Thanks for contributing to seLe4n.

## 5-minute contributor path

1. **Workflow + standards:** [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)
2. **Testing tiers:** [`docs/TESTING_FRAMEWORK_PLAN.md`](docs/TESTING_FRAMEWORK_PLAN.md)
3. **CI policy:** [`docs/CI_POLICY.md`](docs/CI_POLICY.md)
4. **Project scope + workstreams:** [`docs/spec/SELE4N_SPEC.md`](docs/spec/SELE4N_SPEC.md)
5. **Workstream execution plan:** [`docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md)

Full handbook: [`docs/gitbook/README.md`](docs/gitbook/README.md)

## Required validation before opening a PR

```bash
./scripts/test_smoke.sh     # minimum gate (Tier 0-2)
./scripts/test_full.sh      # required for theorem/invariant/doc changes (Tier 0-3)
```

## PR requirements

- Identify workstream ID(s) advanced
- Keep scope to one coherent slice
- Synchronize documentation in the same PR
- See full checklist in [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)
