# seLe4n

seLe4n is a Lean 4 formalization project for an executable, machine-checked model of core
[seL4 microkernel](https://sel4.systems) semantics.

## Current state (authoritative snapshot)

- **Active findings baseline:** `docs/audits/AUDIT_v0.9.32.md`
- **Active execution baseline:** `docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`
- **Current package version:** `0.10.7` (`lakefile.toml`)
- **Current active portfolio:** WS-C1..WS-C8 (WS-C1..WS-C7 completed; WS-C8 documentation consolidation in progress)

## Specifications

The project maintains two specification documents:

- **seL4 microkernel reference:** [`docs/spec/SEL4_SPEC.md`](docs/spec/SEL4_SPEC.md) -- detailed summary of the original seL4 kernel semantics that seLe4n models.
- **seLe4n project spec:** [`docs/spec/SELE4N_SPEC.md`](docs/spec/SELE4N_SPEC.md) -- normative scope, milestones, active workstreams, and acceptance criteria for the seLe4n formalization project.

## Quick setup

```bash
./scripts/setup_lean_env.sh
lake build
lake exe sele4n
```

## Start here (new contributors)

| Step | Document | What you learn |
|------|----------|----------------|
| 1 | [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md) | Day-to-day workflow, validation loop, PR checklist |
| 2 | [`docs/TESTING_FRAMEWORK_PLAN.md`](docs/TESTING_FRAMEWORK_PLAN.md) | Tiered testing gates and CI contract |
| 3 | [`docs/spec/SELE4N_SPEC.md`](docs/spec/SELE4N_SPEC.md) | Project scope, milestones, active workstreams |
| 4 | [`docs/gitbook/README.md`](docs/gitbook/README.md) | Full handbook navigation hub |
| 5 | [`CONTRIBUTING.md`](CONTRIBUTING.md) | Contribution mechanics and PR requirements |

Additional resources:

- Contribution guide: [`CONTRIBUTING.md`](CONTRIBUTING.md)
- Change history: [`CHANGELOG.md`](CHANGELOG.md)

## Validation commands

```bash
./scripts/test_fast.sh      # Tier 0 + Tier 1 (hygiene + build)
./scripts/test_smoke.sh     # + Tier 2 (trace + negative-state checks)
./scripts/test_full.sh      # + Tier 3 (invariant/doc anchor surface)
./scripts/test_nightly.sh   # + Tier 4 (staged nightly; opt-in via NIGHTLY_ENABLE_EXPERIMENTAL=1)
```

## Active workstreams (WS-C)

Quick index. Full contracts and dependencies are in the v0.9.32 planning backbone.

- **WS-C1:** IPC handshake correctness -- completed
- **WS-C2:** Scheduler semantic fidelity -- completed
- **WS-C3:** Proof-surface de-tautologization -- completed
- **WS-C4:** Test validity hardening -- completed
- **WS-C5:** Information-flow assurance -- completed
- **WS-C6:** CI and supply-chain hardening -- completed
- **WS-C7:** Model structure and maintainability -- completed
- **WS-C8:** Documentation and GitBook consolidation (in progress)

Primary references:
- [`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md)
- [`docs/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`](docs/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md)

## Codebase map

| Module | Purpose |
|--------|---------|
| `SeLe4n/Prelude.lean` | Typed identifiers + monad foundations |
| `SeLe4n/Machine.lean` | Machine state and primitive update helpers |
| `SeLe4n/Model/Object.lean`, `Model/State.lean` | Core model entities and kernel/system state |
| `SeLe4n/Kernel/Scheduler/*` | Scheduler transitions and invariants |
| `SeLe4n/Kernel/Capability/*` | CSpace/capability transitions and invariants |
| `SeLe4n/Kernel/IPC/*` | Endpoint IPC transitions and invariants |
| `SeLe4n/Kernel/Lifecycle/*` | Lifecycle/retype transitions and invariants |
| `SeLe4n/Kernel/Service/*` | Service orchestration, policy checks, composed invariants |
| `SeLe4n/Kernel/Architecture/*` | Architecture assumptions, adapter semantics, boundary invariants |
| `SeLe4n/Kernel/InformationFlow/*` | Information-flow policy, projection, and low-equivalence |
| `Main.lean` | Executable trace/demo harness |
| `tests/fixtures/main_trace_smoke.expected` | Stable trace expectation anchors |
| `scripts/test_tier*.sh` | Tiered quality gates used by CI and local workflows |

## Historical note

WS-B (`docs/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md`) and earlier M7/M6/M5/M4 slices remain available for historical traceability, but are not the active planning baseline. See the GitBook Historical Archive section for full context.
