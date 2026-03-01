# Development Workflow

Canonical source: [`docs/DEVELOPMENT.md`](../DEVELOPMENT.md).

## Daily contributor loop

1. Pick one coherent WS-G target (prioritize hardware binding workstreams).
2. Implement minimal code/proof changes.
3. Run tiered checks from smallest scope upward.
4. Synchronize docs in the same PR.
5. Re-run validations before merge.

## Required validation path

```bash
./scripts/test_fast.sh      # Tier 0+1 (hygiene + build)
./scripts/test_smoke.sh     # Tier 0-2 (+ trace + negative-state)
./scripts/test_full.sh      # Tier 0-3 (+ invariant surface anchors)
```

Optional nightly:

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

## Current slice operating rules

For milestone-moving PRs:

- include WS-G workstream ID(s) (WS-G1..G4) for hardware binding work,
- show evidence commands,
- map changes to workstream outcomes,
- record deferrals and destination workstreams,
- keep README/spec/development/GitBook status text synchronized.

## Active workstream sequence (WS-G: Hardware Binding)

| Workstream | Scope | Priority | Status |
|------------|-------|----------|--------|
| **WS-G1** | Instantiate `AdapterProofHooks` with RPi5-specific contracts | Critical | Ready |
| **WS-G2** | ARM64 register ABI + multi-level VSpace page tables | High | Ready |
| **WS-G3** | Interrupt dispatch transitions + verified boot sequence | High | Blocked on WS-G1 |
| **WS-G4** | Bounded resource pools + MMIO memory separation | Medium | Blocked on WS-G2 |

See [`docs/audits/AUDIT_HARDWARE_READINESS_v0.12.5.md`](../audits/AUDIT_HARDWARE_READINESS_v0.12.5.md) for details.

## Failure triage

When checks fail:

1. classify by tier (`HYGIENE`, `BUILD`, `TRACE`, `INVARIANT`),
2. fix semantic/proof root cause first,
3. only then update fixtures or docs if behavior intentionally changed,
4. re-run from smallest relevant tier upward.

## Documentation synchronization rule

Any behavior/proof/slice status change must update all impacted docs in one PR:

- `README.md`
- `docs/spec/SELE4N_SPEC.md`
- `docs/DEVELOPMENT.md`
- affected GitBook chapter(s)
