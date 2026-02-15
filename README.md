# seLe4n

A Lean 4 formalization project for building an executable and provable model of key
[seL4 microkernel](https://sel4.systems) semantics.

The repository is currently at the point where:

- Scheduler integrity (M1) is implemented and machine-checked.
- Capability-space foundation + lifecycle transitions (M2) are implemented and machine-checked.
- The executable demo path in `Main.lean` exercises scheduling, mint, revoke, and delete.

The immediate focus is now completing the next milestone slice (M3 IPC seed) without regressing the
existing M1/M2 proof surface. The model-first minimal IPC state, typed endpoint transition
entrypoints, and first IPC invariant preservation proofs are now in place.

## Quick start

### 1) Install Lean tooling

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
- `SeLe4n/Prelude.lean` — shared IDs, aliases, and the kernel monad definition.
- `SeLe4n/Machine.lean` — abstract machine state and primitive state updates.
- `SeLe4n/Model/Object.lean` — kernel object types (`TCB`, `Endpoint`, `CNode`, `Capability`).
- `SeLe4n/Model/State.lean` — global state model + typed CSpace lookup helpers.
- `SeLe4n/Kernel/API.lean` — executable transitions + preservation and policy theorems.
- `Main.lean` — runnable transition trace used as an executable integration sanity check.
- `docs/SEL4_SPEC.md` — milestone specification, status, and acceptance criteria.
- `docs/DEVELOPMENT.md` — implementation workflow, proof hygiene, and review checklist.

## Current development stage

### Completed milestones

- **Bootstrap**: project wiring, state/object model, kernel transition skeleton.
- **M1 Scheduler Integrity Bundle v1**:
  - queue/current consistency,
  - runnable queue uniqueness,
  - current-thread object validity,
  - preservation across `chooseThread`, `schedule`, and `handleYield`.
- **M2 Capability & CSpace Semantics (current completion boundary)**:
  - typed slot lookup/insert,
  - mint-like derivation with rights attenuation,
  - lifecycle transitions (`cspaceDeleteSlot`, `cspaceRevoke`),
  - lifecycle-aware authority monotonicity claims,
  - composed capability invariant bundle entrypoints and preservation theorems.

### Active planning target

The next implementation slice is **M3 IPC seed**: the minimal endpoint state model and typed
endpoint send/receive transition entrypoints now have a first IPC safety invariant and
preservation theorems; the remaining M3 work is extending executable IPC trace coverage while
preserving the established M1/M2 theorem surface.

See:

- `docs/SEL4_SPEC.md` for normative target outcomes and acceptance gates.
- `docs/DEVELOPMENT.md` for the recommended implementation sequence and PR checklist.

## Daily contributor loop

```bash
lake build
lake exe sele4n
rg -n "axiom|sorry|TODO" SeLe4n Main.lean
```

Use this loop as a minimum pre-PR verification baseline.
