# seLe4: seL4-in-Lean Bootstrapping Repository

This repository provides a complete starter environment for implementing and
formally specifying core seL4 microkernel behavior in Lean 4.

## What is included

- Lean 4 project scaffold (`lakefile.toml`, `lean-toolchain`, `Main.lean`).
- A modular namespace layout for kernel model, execution semantics, invariants,
  and refinement proofs.
- A thorough implementation specification and roadmap in `docs/SPECIFICATION.md`.
- Contributor and environment setup documentation in `docs/ENVIRONMENT.md` and
  `CONTRIBUTING.md`.
- CI workflow for basic Lean build validation.

## Quick start

1. Install Lean tooling with `elan`.
2. Run `lake build`.
3. Read `docs/SPECIFICATION.md` and pick the next milestone.

See `docs/ENVIRONMENT.md` for full setup details.
