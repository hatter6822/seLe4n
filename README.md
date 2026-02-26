<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/logo_dark.png" />
    <img src="assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.12.0-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  A Lean 4 formalization project for an executable, machine-checked model of core
  <a href="https://sel4.systems">seL4 microkernel</a> semantics.
</p>

## Current state (authoritative snapshot)

- **Active findings baseline:** `docs/audits/AUDIT_CODEBASE_v0.11.6.md`
- **Active execution baseline:** `docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`
- **Current package version:** `0.12.0` (`lakefile.toml`)
- **Current active portfolio:** WS-E1..WS-E6 (v0.11.6 codebase audit remediation)
- **Prior completed portfolio:** WS-D1..WS-D4 (completed); WS-D5/D6 absorbed into WS-E

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

## Security hardening defaults

- IPC thread-state updates now fail with `objectNotFound` when the target TCB is missing (including reserved thread ID `0`), preventing ghost queue entries in endpoint/notification paths.
- Sentinel ID `0` is rejected at IPC TCB lookup/update boundaries (`lookupTcb`/`storeTcbIpcState`) rather than silently treated as a valid runtime thread identity.
- Trace and probe harnesses now exercise policy-checked wrappers (`endpointSendChecked`, `cspaceMintChecked`, `serviceRestartChecked`) by default; unchecked operations remain available for research experiments.

## Active workstreams (WS-E)

Quick index. Full contracts and dependencies are in the v0.11.6 planning backbone.

- **WS-E1:** Test infrastructure and CI hardening -- **completed** (Medium; M-10, M-11, F-14, L-07, L-08)
- **WS-E2:** Proof quality and invariant strengthening -- **completed** (High; C-01, H-01, H-03)
- **WS-E3:** Kernel semantic hardening -- **completed** (High; H-06, H-07, H-08, H-09, M-09, L-06)
- **WS-E4:** Capability and IPC model completion -- **completed** (Critical; C-02, C-03, C-04, H-02, M-01, M-02, M-12)
- **WS-E5:** Information-flow maturity -- **completed** (High; H-04, H-05, M-07)
- **WS-E6:** Model completeness and documentation -- **completed** (Low; M-03, M-04, M-05, M-08, F-17, L-01–L-05)

Primary references:
- [`docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md)
- [`docs/audits/AUDIT_CODEBASE_v0.11.6.md`](docs/audits/AUDIT_CODEBASE_v0.11.6.md)

## Completed workstreams (WS-D, historical)

- **WS-D1..WS-D4:** all completed. WS-D5/D6 items absorbed into WS-E. See [`docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md).
- **WS-C1..WS-C8:** all completed. See [`docs/dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](docs/dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md).

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
| `SeLe4n/Kernel/API.lean` | Unified public API surface, invariant bundle alias, stability table |
| `Main.lean` | Executable trace/demo harness |
| `tests/fixtures/main_trace_smoke.expected` | Stable trace expectation anchors |
| `scripts/test_tier*.sh` | Tiered quality gates used by CI and local workflows |

## Historical note

Prior workstream plans (WS-C, WS-B), older audits (v0.8.0–v0.9.32), milestone closeouts, and legacy GitBook chapters are archived in [`docs/dev_history/`](docs/dev_history/README.md) for traceability.
