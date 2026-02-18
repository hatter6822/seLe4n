# seLe4n

seLe4n is a Lean 4 formalization project for an executable, machine-checked model of core
[seL4 microkernel](https://sel4.systems) semantics.

## Current state (authoritative snapshot)

- **Active findings baseline:** `docs/audits/AUDIT_v0.9.32.md`
- **Active execution baseline:** `docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`
- **Current package version:** `0.9.32` (`lakefile.toml`)
- **Current active portfolio:** WS-C1..WS-C8 (WS-C8 documentation consolidation in progress)

Normative scope and acceptance criteria live in [`docs/SEL4_SPEC.md`](docs/SEL4_SPEC.md).

## Start here (new contributors)

1. **Development workflow:** [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)
2. **Testing and CI contract:** [`docs/TESTING_FRAMEWORK_PLAN.md`](docs/TESTING_FRAMEWORK_PLAN.md)
3. **Current audit workstream plan:**
   [`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md)
4. **GitBook navigation hub:** [`docs/gitbook/README.md`](docs/gitbook/README.md)
5. **Contribution mechanics:**

- Contribution guide (root pointer): [`CONTRIBUTING.md`](CONTRIBUTING.md)
- Change history: [`CHANGELOG.md`](CHANGELOG.md)

## Active workstreams (WS-C)

Use this as a quick index. Full contracts and dependencies are in the v0.9.32 planning backbone.

- **WS-C1:** IPC handshake correctness ✅ completed (notification badge accumulation + waiter ipcState transitions landed)
- **WS-C2:** Scheduler semantic fidelity
- **WS-C3:** Proof-surface de-tautologization (remove tautological `_deterministic` theorems and track semantic replacements)
- **WS-C4:** Test validity hardening
- **WS-C5:** Information-flow assurance
- **WS-C6:** CI and supply-chain hardening
- **WS-C7:** Model structure and maintainability
- **WS-C8:** Documentation and GitBook consolidation (in progress)

Primary references:
- [`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md)
- [`docs/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`](docs/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md)

## Historical note

WS-B (`docs/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md`) and earlier M7/M6/M5/M4 slices remain available for historical traceability, but are not the active planning baseline.

## Quick setup

```bash
./scripts/setup_lean_env.sh
lake build
lake exe sele4n
```

## Validation commands

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
./scripts/test_nightly.sh
```

## Codebase map

- `SeLe4n/Prelude.lean` — typed identifiers + monad foundations
- `SeLe4n/Machine.lean` — machine state and primitive update helpers
- `SeLe4n/Model/Object.lean`, `SeLe4n/Model/State.lean` — core model entities and kernel/system state
- `SeLe4n/Kernel/Scheduler/*` — scheduler transitions and invariants
- `SeLe4n/Kernel/Capability/*` — CSpace/capability transitions and invariants
- `SeLe4n/Kernel/IPC/*` — endpoint IPC transitions and invariants
- `SeLe4n/Kernel/Lifecycle/*` — lifecycle/retype transitions and invariants
- `SeLe4n/Kernel/Service/*` — service orchestration, policy checks, composed invariants
- `SeLe4n/Kernel/Architecture/*` — architecture assumptions, adapter semantics, boundary invariants
- `Main.lean` — executable trace/demo harness
- `tests/fixtures/main_trace_smoke.expected` — stable trace expectation anchors
- `scripts/test_tier*.sh` — tiered quality gates used by CI and local workflows
