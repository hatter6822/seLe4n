# Development Guide

## Goals

- Maintain an executable Lean model while progressively increasing fidelity to seL4.
- Keep specifications and code synchronized.
- Prefer total functions and explicit error channels (`Except`) over partial definitions.

## Workflow

1. Add or refine specification text in `docs/SEL4_SPEC.md`.
2. Add/modify Lean model definitions.
3. Add theorem statements and proofs for preserved invariants.
4. Run `lake build` after every cohesive change.

## Suggested next milestones

- Introduce typed CSpace trees and capability derivation rules.
- Add endpoint IPC send/receive transition semantics.
- Model untyped memory and retype operations.
- Encode a refinement relation between abstract and executable states.

## Coding conventions

- Use namespaces to separate abstract model layers:
  - `SeLe4.Model` for objects/state/semantics.
  - `SeLe4.Kernel` for kernel-facing operations and invariants.
- Keep theorem names descriptive, e.g. `schedule_preserves_wellFormed`.
- Document non-obvious design choices with short comments.

## Validation

Minimum required check before commit:

```bash
lake build
```
