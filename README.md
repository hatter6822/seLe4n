# seLe4n

seLe4n is a Lean 4 formalization project for an executable, machine-checked model of core
[seL4 microkernel](https://sel4.systems) semantics.

## Current state (authoritative snapshot)

- **Active development slice:** Comprehensive Audit 2026-02 execution (WS-B portfolio; WS-B1, WS-B2, WS-B3, WS-B4, WS-B5, and WS-B6 completed).
- **Most recently completed slice:** M7 audit remediation (WS-A1..WS-A8 complete).
- **Previous completed slice:** M6 architecture-boundary assumptions/adapters.
- **Current package version:** `0.9.18` (`lakefile.toml`).

Normative scope and acceptance criteria live in [`docs/SEL4_SPEC.md`](docs/SEL4_SPEC.md).

## Start here (new contributors)

1. **Development workflow:** [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)
2. **Testing and CI contract:** [`docs/TESTING_FRAMEWORK_PLAN.md`](docs/TESTING_FRAMEWORK_PLAN.md)
3. **Comprehensive audit workstream plan (current slice):**
   [`docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md`](docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md)
4. **GitBook navigation hub:** [`docs/gitbook/README.md`](docs/gitbook/README.md)
5. **Contribution mechanics:** [`CONTRIBUTING.md`](CONTRIBUTING.md)

- Contribution guide (root pointer): [`CONTRIBUTING.md`](CONTRIBUTING.md)
- Change history: [`CHANGELOG.md`](CHANGELOG.md)

## Current slice workstreams (WS-B)

Use this as the quick index. Full contracts and dependencies are in the audit planning backbone.

- **WS-B1:** VSpace + memory model foundation ✅ completed
- **WS-B2:** Generative + negative testing expansion ✅ completed
- **WS-B3:** Main trace harness refactor ✅ completed
- **WS-B4:** Remaining type-wrapper migration ✅ completed
- **WS-B5:** CSpace guard/radix semantics completion ✅ completed
- **WS-B6:** Notification-object IPC completion ✅ completed
- **WS-B7:** Information-flow proof-track start
- **WS-B8:** Documentation automation/consolidation
- **WS-B9:** Threat model + security hardening
- **WS-B10:** CI maturity upgrades
- **WS-B11:** Scenario framework finalization

Primary reference:
[`docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md`](docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md).


## Legacy semantic anchor note

The M3.5 IPC-scheduler handshake semantics remain part of the stable regression surface and are still exercised through `Main.lean` trace fixtures and Tier 3 anchor checks.

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

