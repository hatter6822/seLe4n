# seLe4n

A Lean 4 development environment and formalization scaffold for implementing and verifying
key parts of the [seL4 microkernel](https://sel4.systems).

This repository now contains:

- A working Lean 4 / Lake project that builds locally.
- A typed, executable high-level model skeleton for core seL4 concepts.
- A formal specification roadmap in `docs/SEL4_SPEC.md`.
- Development conventions in `docs/DEVELOPMENT.md`.

## Quick start

### 1) Install Lean tooling (Elan)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
```

Then open a new shell (or source Elan env):

```bash
source "$HOME/.elan/env"
```

### 2) Build

```bash
lake build
```

### 3) Run the sample executable

```bash
lake exe sele4n
```

## Repository layout

- `SeLe4n.lean`: library root exports.
- `SeLe4n/Prelude.lean`: shared base definitions.
- `SeLe4n/Machine.lean`: abstract machine/model primitives.
- `SeLe4n/Model/`: high-level state and kernel object model.
- `SeLe4n/Kernel/`: kernel interface skeleton and invariants.
- `docs/SEL4_SPEC.md`: complete implementation specification.
- `docs/DEVELOPMENT.md`: coding/testing/documentation guidance.

## Current status

Bootstrap goals are complete and validated in code. The project is now entering the M1
invariant-strengthening phase (scheduler integrity and richer preservation proofs), with the
version advanced to `0.2.3` after landing Scheduler Invariant Bundle v1 (including an explicit strict queue/current consistency policy).
