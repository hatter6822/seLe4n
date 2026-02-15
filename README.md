# seLe4n

A Lean 4 formalization project for building an executable and machine-checked model of key
[seL4 microkernel](https://sel4.systems) semantics.

## Project status snapshot

seLe4n is currently in a **post-M3 IPC seed** stage:

- ✅ M1 scheduler integrity invariants are implemented and proved.
- ✅ M2 capability/CSpace semantics and lifecycle transitions are implemented and proved.
- ✅ M3 endpoint IPC seed (send/receive + invariant-preservation entrypoints) is implemented and
  proved.
- ✅ `Main.lean` executable trace demonstrates scheduler, CSpace lifecycle, and IPC seed behavior.

The active planning target is **M3.5 IPC handshake + scheduler interaction**, which will add a
narrow blocking/wakeup IPC contract while preserving existing M1/M2/M3 guarantees.

Testing framework status: Tier 0 (hygiene), Tier 1 (build), and Tier 2 (fixture-backed executable
smoke regression checks) are implemented and usable via `scripts/test_*.sh` entrypoints. Pull
requests are gated in CI by `./scripts/test_fast.sh` and `./scripts/test_smoke.sh`.

## Quick start

### 1) Install Lean tooling

Use the repository bootstrap script (recommended):

```bash
./scripts/setup_lean_env.sh
```

Or install manually:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"
```

### 2) Build and run

```bash
lake build
lake exe sele4n
```

## Repository layout

- `SeLe4n.lean` — library export root.
- `SeLe4n/Prelude.lean` — shared IDs, aliases, and kernel monad definitions.
- `SeLe4n/Machine.lean` — abstract machine state and primitive updates.
- `SeLe4n/Model/Object.lean` — kernel object types (`TCB`, `Endpoint`, `CNode`, `Capability`).
- `SeLe4n/Model/State.lean` — global system state and typed lookup helpers.
- `SeLe4n/Kernel/API.lean` — executable transitions, invariants, and preservation theorem
  entrypoints.
- `Main.lean` — runnable integration trace.
- `docs/SEL4_SPEC.md` — normative milestone spec, acceptance criteria, and next-slice outcomes.
- `docs/DEVELOPMENT.md` — implementation workflow, proof standards, and review checklist.
- `scripts/setup_lean_env.sh` — one-command Lean/elán bootstrap for local development environments.

## Milestone view

### Completed milestones

1. **Bootstrap**
   - state/object model,
   - executable kernel monad shape,
   - base transition/error scaffolding.

2. **M1 Scheduler Integrity Bundle v1**
   - queue uniqueness,
   - current-thread validity,
   - queue/current consistency,
   - preservation through core scheduler transitions.

3. **M2 Capability & CSpace Semantics**
   - typed slot addressing and lookup,
   - insert/mint/delete/revoke transitions,
   - rights attenuation and lifecycle authority monotonicity,
   - composed capability invariant bundle preservation.

4. **M3 IPC seed**
   - minimal endpoint state model,
   - `endpointSend` / `endpointReceive` transitions,
   - endpoint/IPC invariant definitions,
   - preservation theorems including composed `m3IpcSeedInvariantBundle`.

### Next slice (M3.5) target outcomes

The next development slice should deliver:

1. Endpoint protocol-state refinement for waiting directions.
2. Minimal blocking/wakeup behavior in endpoint transitions.
3. Scheduler-facing coherence predicates for IPC-touched threads.
4. Preservation theorem entrypoints for updated transitions and bundle composition.
5. Executable trace evidence for one waiting-to-delivery IPC scenario.

## Testing quick reference

Use the tiered test entrypoints for local validation:

```bash
./scripts/test_fast.sh      # Tier 0 + Tier 1
./scripts/test_smoke.sh     # Tier 0 + Tier 1 + Tier 2 (fixture-backed trace gate)
./scripts/test_full.sh      # smoke + explicit Tier 3 extension-point notice
./scripts/test_nightly.sh   # full + explicit Tier 4 extension-point notice
./scripts/audit_testing_framework.sh
```

The test scripts automatically source `$HOME/.elan/env` when present so `lake` is available even in
fresh shells after running `./scripts/setup_lean_env.sh`. CI uses the same script entrypoints via
`.github/workflows/lean_action_ci.yml` to prevent local-vs-CI drift.

## Daily contributor verification loop

Run this as a minimum before opening a PR:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
```

When debugging locally, you can still run individual commands:

```bash
lake build
lake exe sele4n
rg -n "axiom|sorry|TODO" SeLe4n Main.lean
```

## Where to look next

- Specification and acceptance gates: `docs/SEL4_SPEC.md`
- Development workflow and PR checklist: `docs/DEVELOPMENT.md`
