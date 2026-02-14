# Development Guide

## 1. Current phase

The project has completed bootstrap and is now in **M1: Scheduler Integrity**.
Development should prioritize invariant strengthening and proof coverage for existing scheduling
transitions before adding major new subsystems.

## 2. Working agreement

1. Spec-first: update `docs/SEL4_SPEC.md` when scope or acceptance criteria change.
2. Keep executable behavior intact (`Main.lean` path should remain runnable).
3. Prove before broadening: land small, composable invariants with corresponding proofs.
4. Prefer total functions and explicit error channels (`Except`) over partial definitions.

## 3. Recommended workflow per change

1. Confirm milestone impact (M1-only vs. future milestone prep).
2. Update spec text if acceptance criteria/scope move.
3. Implement Lean model/theorem changes in smallest coherent slices.
4. Run checks:
   - `lake build`
   - `lake exe sele4n` (when transition behavior is affected)
5. Summarize proof obligations completed and remaining in PR notes.

## 4. Coding conventions

- Namespaces:
  - `SeLe4n.Model` for state/object definitions,
  - `SeLe4n.Kernel` for transitions/invariants/proofs.
- Theorem naming:
  - use `<transition>_preserves_<invariant>` style where practical.
- Proof structure:
  - isolate helper lemmas for list/set facts,
  - keep theorem statements stable and refactor proof terms beneath them.
- Documentation:
  - add short comments when a design choice is non-obvious or policy-based.

## 5. Milestone-oriented checklist

Before merging work intended for M1, verify:

- [ ] invariant definition is explicit and compositional,
- [ ] theorem(s) use the invariant in transition preservation,
- [ ] no new `axiom` introduced,
- [ ] `lake build` passes,
- [ ] docs reflect the new state of completion.

## 6. Anti-patterns to avoid

- Expanding into IPC/MMU/retype semantics before M1 proofs stabilize.
- Embedding milestone assumptions in code without documenting them in the spec.
- Monolithic proof scripts that block incremental refactoring.
