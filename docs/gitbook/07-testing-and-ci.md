# Testing and CI

## Tier model

- Tier 0: hygiene markers and shell-quality checks.
- Tier 1: full Lean build/theorem compile.
- Tier 2: fixture-backed executable smoke trace.
- Tier 3: invariant/doc-surface anchors (full suite).
- Tier 4: nightly extension point.

## Required gates

- `./scripts/test_fast.sh`
- `./scripts/test_smoke.sh`

CI should execute repository scripts directly to avoid local/CI divergence.

## Why fixture checks matter

The fixture check ensures that executable behavior supporting milestone claims remains visible and
reviewable. It catches semantic drift that pure type-checking may miss.

## M4 testing trajectory

- M4-A: add lifecycle semantic trace fragments once lifecycle scenarios land.
- M4-B: add success/failure lifecycle composition traces and stronger Tier 3 anchors.
