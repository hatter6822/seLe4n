# seLe4

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
lake exe sele4
```

## Repository layout

- `SeLe4.lean`: library root exports.
- `SeLe4/Prelude.lean`: shared base definitions.
- `SeLe4/Machine.lean`: abstract machine/model primitives.
- `SeLe4/Model/`: high-level state and kernel object model.
- `SeLe4/Kernel/`: kernel interface skeleton and invariants.
- `docs/SEL4_SPEC.md`: complete initial implementation specification.
- `docs/DEVELOPMENT.md`: coding/testing/documentation guidance.

## Current status

This is a bootstrap formalization stage. The model is intentionally minimal but coherent,
compiles under Lean, and is ready for iterative refinement toward concrete seL4 behavior and
proof obligations.
