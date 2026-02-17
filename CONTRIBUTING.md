# Contributing to seLe4n

Thanks for contributing to seLe4n.

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
