# seLe4n

A Lean 4 formalization project for building an executable and machine-checked model of key
[seL4 microkernel](https://sel4.systems) semantics.

## Project status snapshot

seLe4n is currently in a **post-M3.5 handshake / pre-M4 lifecycle** stage.

### Milestone board (authoritative)

- ✅ **Bootstrap complete**: executable kernel monad, core object/state model, transition scaffolding.
- ✅ **M1 complete**: scheduler integrity invariants and preservation entrypoints.
- ✅ **M2 complete**: capability + CSpace operations, attenuation/lifecycle rules, composed invariants.
- ✅ **M3 complete**: endpoint IPC seed (`endpointSend`/`endpointReceive`) plus preservation theorem surface.
- ✅ **M3.5 complete**: typed waiting/handshake behavior, scheduler coherence contract predicates, composed IPC+scheduler invariant bundle, local-first preservation theorem layering, and executable waiting-to-delivery demonstration in `Main.lean`.
- 📌 **Current active slice (M4)**: object lifecycle/retype safety and capability-object interaction invariants.

Testing framework status:

- ✅ Tier 0 hygiene gate (`axiom|sorry|TODO` scan).
- ✅ Tier 1 build/theorem gate (`lake build`).
- ✅ Tier 2 fixture-backed executable smoke regression gate.
- ✅ Tier 3 invariant/doc-surface checks are wired via `test_full.sh`.
- 🧩 Tier 4 nightly extension point remains documented for broader confidence checks.

CI status:

- Required pull-request jobs call repository script entrypoints directly via
  `.github/workflows/lean_action_ci.yml`.
- Required jobs today: `./scripts/test_fast.sh` and `./scripts/test_smoke.sh`.

---

## What is now closed (M3.5)

The active engineering objective is **IPC handshake + scheduler interaction** with minimal, explicit
state changes that can be proved and executed.

### Current-slice target outcomes (must all land for M3.5 close)

1. Endpoint protocol-state refinement with explicit waiting direction(s).
2. Narrow blocking/wakeup transition behavior in IPC send/receive paths.
3. Scheduler-facing coherence predicate(s) for runnable-vs-blocked IPC thread state.
4. Invariant bundle extension layered on top of M3 seed IPC invariants.
5. Preservation theorem entrypoints for each changed/new transition.
6. `Main.lean` evidence path showing at least one waiting-to-delivery story.

### Current-slice constraints

- Keep changes architecture-neutral.
- Preserve M1/M2/M3 theorem surfaces unless intentionally revised and documented.
- Avoid reply-cap protocol completeness and policy redesign in this slice.

---

## What comes immediately after (next slice: M4)

After M3.5 closure, the planned next delivery slice is **M4 object lifecycle / retype safety**.

### Next-slice target outcomes (planning baseline)

1. Typed object creation/retype transition model.
2. Object identity and aliasing constraints suitable for machine proofs.
3. Capability/object lifecycle coupling invariants.
4. Preservation entrypoints for retype lifecycle transitions.
5. Executable scenario coverage showing safe object lifecycle evolution.

M4 planning is intentionally bounded so we can preserve the same incremental proof style used in
M1-M3.5.

---

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

---

## Repository layout

- `SeLe4n.lean` — library export root.
- `SeLe4n/Prelude.lean` — shared IDs, aliases, kernel monad definitions.
- `SeLe4n/Machine.lean` — abstract machine state and primitive updates.
- `SeLe4n/Model/Object.lean` — kernel object types (`TCB`, `Endpoint`, `CNode`, `Capability`).
- `SeLe4n/Model/State.lean` — global system state and typed lookup helpers.
- `SeLe4n/Kernel/API.lean` — compatibility barrel that re-exports the kernel surface.
- `SeLe4n/Kernel/Scheduler/Invariant.lean` — scheduler invariant definitions and base lemmas.
- `SeLe4n/Kernel/Scheduler/Operations.lean` — scheduler transitions and preservation theorems.
- `SeLe4n/Kernel/Capability/Operations.lean` — CSpace/capability executable operations.
- `SeLe4n/Kernel/Capability/Invariant.lean` — capability invariant bundles and M3 composition proofs.
- `SeLe4n/Kernel/IPC/Invariant.lean` — endpoint IPC transitions and IPC invariant preservation.
- `Main.lean` — runnable integration trace.
- `docs/SEL4_SPEC.md` — normative milestone spec and acceptance criteria.
- `docs/DEVELOPMENT.md` — implementation workflow, proof standards, PR checklist.
- `docs/TESTING_FRAMEWORK_PLAN.md` — testing tiers, CI strategy, and expansion path.
- `docs/PROJECT_AUDIT.md` — current deep audit of code, tests, documentation, and roadmap.
- `tests/scenarios/README.md` — fixture maintenance and trace regression workflow.

---

## Milestone detail

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

### Completed milestone (M3.5)

Delivered: queue-only seed semantics were extended to an explicit waiting/handshake contract
between endpoint behavior and scheduler-visible thread coherence, with machine-checked
preservation theorem entrypoints and executable trace evidence.

### Active milestone (M4)

Focus: introduce object lifecycle/retype transitions and prove capability/object lifecycle safety
properties without destabilizing existing scheduler/capability/IPC theorem bundles.

---

## Testing quick reference

Use the tiered test entrypoints for local validation:

```bash
./scripts/test_fast.sh      # Tier 0 + Tier 1
./scripts/test_smoke.sh     # Tier 0 + Tier 1 + Tier 2 (fixture-backed trace gate)
./scripts/test_full.sh      # smoke + Tier 3 invariant/doc-surface gate
./scripts/test_nightly.sh   # full + explicit Tier 4 extension-point notice
./scripts/audit_testing_framework.sh
```

The test scripts auto-source `$HOME/.elan/env` when present so `lake` is available in fresh shells
after `./scripts/setup_lean_env.sh`.

---

## CI gates (pull requests)

Pull requests must pass both required CI jobs:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
```

On smoke-trace failures, CI uploads diagnostics:

- `main_trace_smoke.actual.log`
- `main_trace_smoke.missing.txt`
- `tests/fixtures/main_trace_smoke.expected`

---

## License

This project is licensed under the MIT License. See [`LICENSE`](./LICENSE).

### Provenance policy

- Do not copy third-party code or text into this repository without explicit attribution.
- Confirm incoming third-party material is license-compatible with MIT before committing it.

---

## Daily contributor verification loop

Run this minimum loop before opening a PR:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
```

Useful direct commands for local debugging:

```bash
lake build
lake exe sele4n
rg -n "axiom|sorry|TODO" SeLe4n Main.lean
```

---

## Where to look next

- Normative scope and acceptance gates: `docs/SEL4_SPEC.md`
- Implementation workflow and review checklist: `docs/DEVELOPMENT.md`
- Testing framework roadmap and ownership guidance: `docs/TESTING_FRAMEWORK_PLAN.md`
