# Development Workflow

## Daily contributor loop

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
```

Recommended deeper checks:

```bash
lake build
lake exe sele4n
rg -n "axiom|sorry|TODO" SeLe4n Main.lean
./scripts/test_full.sh
```

## Implementation pattern

1. update/introduce transition,
2. define/refine local invariant components,
3. add helper lemmas near transition,
4. prove local preservation,
5. prove composed preservation,
6. update executable scenario/fixture,
7. update docs in same commit range.

## Documentation synchronization rule

When semantics or milestone boundaries change, keep these in sync:

- `README.md`,
- `docs/SEL4_SPEC.md`,
- `docs/DEVELOPMENT.md`,
- `docs/TESTING_FRAMEWORK_PLAN.md`,
- related `docs/gitbook/*` pages.
