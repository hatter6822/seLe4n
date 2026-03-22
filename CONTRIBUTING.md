# Contributing to seLe4n

Thanks for contributing to seLe4n — a production-oriented microkernel written in
Lean 4 with machine-checked proofs.

## License

seLe4n is licensed under the [GNU General Public License v3.0 or later](LICENSE).
By submitting a pull request or contributing code to this project, you agree that
your contributions will be licensed under the same GPL-3.0-or-later license. You
also certify that you have the right to submit the contribution under this license.

## 5-minute contributor path

1. **Workflow + standards:** [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)
2. **Testing tiers:** [`docs/TESTING_FRAMEWORK_PLAN.md`](docs/TESTING_FRAMEWORK_PLAN.md)
3. **CI policy:** [`docs/CI_POLICY.md`](docs/CI_POLICY.md)
4. **Project scope + workstreams:** [`docs/spec/SELE4N_SPEC.md`](docs/spec/SELE4N_SPEC.md)
5. **Active audit findings:** [`docs/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](docs/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md)
6. **Workstream history:** [`docs/WORKSTREAM_HISTORY.md`](docs/WORKSTREAM_HISTORY.md)

Full handbook: [`docs/gitbook/README.md`](docs/gitbook/README.md)

## Required validation before opening a PR

```bash
./scripts/test_smoke.sh     # minimum gate (Tier 0-2)
./scripts/test_full.sh      # required for theorem/invariant changes (Tier 0-3)
```

## PR requirements

- Identify workstream ID(s) advanced (WS-F1..F8 for current portfolio)
- Keep scope to one coherent slice
- Transitions must be deterministic (explicit success/failure)
- Invariant/theorem updates paired with implementation changes
- Synchronize documentation in the same PR
- See full checklist in [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)
