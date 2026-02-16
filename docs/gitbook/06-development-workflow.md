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

Bootstrap note: `./scripts/setup_lean_env.sh` retries `shellcheck` installation even when `apt-get update` is partially unavailable (for example, blocked optional third-party repos), reducing setup friction in restricted CI/container environments.

## Milestone-oriented implementation pattern

1. update/introduce transition,
2. define/refine local invariant components,
3. add helper lemmas near transition,
4. prove local preservation,
5. prove composed preservation,
6. update executable scenario/fixture,
7. update docs in same commit range,
8. state “what this unlocks next” for the roadmap.

## Documentation synchronization rule

When semantics or milestone boundaries change, keep these in sync:

- `README.md`,
- `docs/SEL4_SPEC.md`,
- `docs/DEVELOPMENT.md`,
- `docs/TESTING_FRAMEWORK_PLAN.md`,
- related `docs/gitbook/*` pages.

## Current focus and immediate next focus

- **Completed baseline slice:** M5 service-graph + policy surfaces.
- **Current delivery slice:** M6 architecture-binding interface preparation.
- **Historical predecessor slice:** M4-B lifecycle-capability composition hardening.

Contributors should treat M1–M5 theorem surfaces as stable interfaces and layer M6 architecture
binding work on top, rather than reshaping already-closed contracts.

## Definition of done for milestone-moving PRs

A PR that claims milestone movement should include:

1. deterministic transition behavior,
2. named invariant components,
3. local and composed preservation theorem entrypoints,
4. executable evidence and any fixture rationale,
5. explicit deferred-work note tied to next slice.


## M6 execution rhythm (recommended)

For active-slice work, use a weekly rhythm:

1. **Early week**: land semantic changes and local helper lemmas.
2. **Mid week**: land local preservation theorem work.
3. **Late week**: land composed preservation + executable/fixture updates.
4. **Closeout**: run full test stack and sync all milestone docs.

## Failure triage flow

When a validation command fails:

1. Identify tier (`HYGIENE`, `BUILD`, `TRACE`, `INVARIANT`).
2. Confirm whether failure is semantic drift, proof breakage, fixture drift, or missing anchor.
3. Fix the root cause first; avoid patching fixture/tests before semantics stabilize.
4. Re-run from smallest relevant tier upward (`test_fast` → `test_smoke` → `test_full`).

## Milestone drift prevention checklist

Before merging PRs that mention roadmap/slice movement:

- update status markers in README/spec/development docs,
- update GitBook slice chapter labels and navigation text,
- ensure testing plan reflects current slice objectives,
- state explicit deferred work and destination milestone.
