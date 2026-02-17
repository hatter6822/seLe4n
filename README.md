# seLe4n

seLe4n is a Lean 4 formalization project for an executable, machine-checked model of core
[seL4 microkernel](https://sel4.systems) semantics.

## Current development stage

- **Active slice:** M7 audit remediation workstreams (WS-A1 through WS-A8) with CI, architecture, type-safety, testing, and documentation hardening as the immediate execution focus.
- **Most recently completed slice:** M6 architecture-binding interfaces and hardware-facing assumption hardening (WS-M6-A through WS-M6-E completed).
- **First real-hardware architecture focus:** Raspberry Pi 5 (post-remediation binding path).

For normative milestones, acceptance criteria, and scope decisions, use
[`docs/SEL4_SPEC.md`](docs/SEL4_SPEC.md) as the source of truth.

## Start here

- **Developer setup + workflow:** [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)
- **Testing tiers + CI contract:** [`docs/TESTING_FRAMEWORK_PLAN.md`](docs/TESTING_FRAMEWORK_PLAN.md)
- **Historical end-to-end audit snapshot (superseded):** [`docs/PROJECT_AUDIT.md`](docs/PROJECT_AUDIT.md)
- **Current repository audit baseline (architecture/code/test/docs/CI/security):** [`docs/REPOSITORY_AUDIT.md`](docs/REPOSITORY_AUDIT.md)
- **Audit remediation workstreams (M7+ execution plan):** [`docs/AUDIT_REMEDIATION_WORKSTREAMS.md`](docs/AUDIT_REMEDIATION_WORKSTREAMS.md)
- **Long-form handbook (GitBook):** [`docs/gitbook/README.md`](docs/gitbook/README.md)
- **M6 execution plan (completed slice):** [`docs/gitbook/18-m6-execution-plan-and-workstreams.md`](docs/gitbook/18-m6-execution-plan-and-workstreams.md)
- **M5 closeout snapshot chapter:** [`docs/gitbook/09-m5-closeout-snapshot.md`](docs/gitbook/09-m5-closeout-snapshot.md)
- **Completed slice archive (M4-B):** [`docs/gitbook/16-completed-slice-m4b.md`](docs/gitbook/16-completed-slice-m4b.md)
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
