# seLe4n

seLe4n is a Lean 4 formalization project for an executable, machine-checked model of core
[seL4 microkernel](https://sel4.systems) semantics.

## Current development stage

- **Active slice:** M7 audit remediation workstreams (WS-A1 through WS-A8) with outcome-driven closure targets across CI, architecture, type-safety, testing, and documentation hardening.
- **Most recently completed slice:** M6 architecture-binding interfaces and hardware-facing assumption hardening (WS-M6-A through WS-M6-E completed).
- **First real-hardware architecture focus:** Raspberry Pi 5 (post-remediation binding path).

For normative milestones, acceptance criteria, and scope decisions, use
[`docs/SEL4_SPEC.md`](docs/SEL4_SPEC.md) as the source of truth.

- **Current package version:** `0.8.16` (see `lakefile.toml`).

### Current slice target outcomes (M7)

1. enforce Tier 0–3 quality gates with deterministic and reproducible CI evidence,
2. complete architecture/API boundary cleanup and preserve stable public surfaces,
3. migrate high-risk identity/pointer aliases toward stronger type safety,
4. broaden scenario/test evidence for scale and adversarial-style paths,
5. isolate test-only permissive contracts from runtime-facing modules,
6. align root docs and GitBook around active + next-slice execution plans.

For workstream-level details and closure criteria, use [`docs/AUDIT_REMEDIATION_WORKSTREAMS.md`](docs/AUDIT_REMEDIATION_WORKSTREAMS.md) and GitBook chapter [`docs/gitbook/21-m7-current-slice-outcomes-and-workstreams.md`](docs/gitbook/21-m7-current-slice-outcomes-and-workstreams.md).

## Start here (contributor IA)

- **1) Developer setup + workflow:** [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)
- **2) Contribution guide:** [`CONTRIBUTING.md`](CONTRIBUTING.md)
- **3) Change history:** [`CHANGELOG.md`](CHANGELOG.md)
- **4) Testing tiers + CI contract:** [`docs/TESTING_FRAMEWORK_PLAN.md`](docs/TESTING_FRAMEWORK_PLAN.md)
- **5) Branch protection + required checks policy (WS-A1):** [`docs/CI_POLICY.md`](docs/CI_POLICY.md)
- **Hardware-boundary contract policy (WS-A5):** [`docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md`](docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md)
- **Historical end-to-end audit snapshot (superseded):** [`docs/PROJECT_AUDIT.md`](docs/PROJECT_AUDIT.md)
- **Current repository audit baseline (architecture/code/test/docs/CI/security):** [`docs/REPOSITORY_AUDIT.md`](docs/REPOSITORY_AUDIT.md)
- **M7 execution outcomes and workstreams (active slice):** [`docs/gitbook/21-m7-current-slice-outcomes-and-workstreams.md`](docs/gitbook/21-m7-current-slice-outcomes-and-workstreams.md)
- **Audit remediation workstreams (M7+ execution plan):** [`docs/AUDIT_REMEDIATION_WORKSTREAMS.md`](docs/AUDIT_REMEDIATION_WORKSTREAMS.md)
- **Long-form handbook (GitBook):** [`docs/gitbook/README.md`](docs/gitbook/README.md)
- **M6 execution plan (completed slice):** [`docs/gitbook/18-m6-execution-plan-and-workstreams.md`](docs/gitbook/18-m6-execution-plan-and-workstreams.md)
- **M5 closeout snapshot chapter:** [`docs/gitbook/09-m5-closeout-snapshot.md`](docs/gitbook/09-m5-closeout-snapshot.md)
- **Completed slice archive (M4-B):** [`docs/gitbook/16-completed-slice-m4b.md`](docs/gitbook/16-completed-slice-m4b.md)
- **Next slice development path (post-M7):** [`docs/gitbook/22-next-slice-development-path.md`](docs/gitbook/22-next-slice-development-path.md)
- **Project usage/value guide:** [`docs/gitbook/17-project-usage-value.md`](docs/gitbook/17-project-usage-value.md)
- **Architecture and module map:** [`docs/gitbook/03-architecture-and-module-map.md`](docs/gitbook/03-architecture-and-module-map.md)
- **Codebase deep reference:** [`docs/gitbook/11-codebase-reference.md`](docs/gitbook/11-codebase-reference.md)
- **Proof and invariant map:** [`docs/gitbook/12-proof-and-invariant-map.md`](docs/gitbook/12-proof-and-invariant-map.md)
- **Hardware direction (Raspberry Pi 5 first):** [`docs/gitbook/10-path-to-real-hardware-mobile-first.md`](docs/gitbook/10-path-to-real-hardware-mobile-first.md)

## Quick start

### 1) Install Lean tooling

```bash
./scripts/setup_lean_env.sh
```

### 2) Build and run

```bash
lake build
lake exe sele4n
```

### 3) Validate changes

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
./scripts/test_nightly.sh
```

## Repository map

- `SeLe4n/Prelude.lean` — IDs, aliases, kernel monad foundations.
- `SeLe4n/Machine.lean` — abstract machine state and primitive updates.
- `SeLe4n/Model/Object.lean` / `SeLe4n/Model/State.lean` — object/state semantics.
- `SeLe4n/Kernel/Scheduler/*.lean` — scheduler operations and invariants.
- `SeLe4n/Kernel/Capability/*.lean` — capability/CSpace operations and invariants.
- `SeLe4n/Kernel/IPC/*.lean` — endpoint IPC semantics and invariants.
- `SeLe4n/Kernel/Lifecycle/*.lean` — lifecycle/retype semantics and invariants.
- `SeLe4n/Kernel/Service/*.lean` — service orchestration transitions and policy-surface invariants.
- `SeLe4n/Kernel/Architecture/Assumptions.lean` — WS-M6-A assumption inventory, typed contract references (`ContractRef`), architecture-boundary contract skeletons, and runtime-branch decidability witnesses used by adapters.
- `SeLe4n/Kernel/Architecture/Adapter.lean` — WS-M6-B deterministic adapter APIs (`adapterAdvanceTimer`, `adapterWriteRegister`, `adapterReadMemory`) with explicit bound-context error mapping.
- `SeLe4n/Kernel/Architecture/Invariant.lean` — WS-M6-C proof-layer integration hooks (`proofLayerInvariantBundle`) and local/composed preservation theorems for adapter success/failure paths.
- `Main.lean` — executable scenario traces.

## License

This project is licensed under the MIT License. See [`LICENSE`](./LICENSE).
