# Contributing to seLe4

## Branching and commits

- Use focused branches per theorem-feature or subsystem change.
- Keep commits small and proof-cohesive.
- Include Lean file and docs updates together when semantics change.

## Coding guidance

- Maintain namespace hierarchy under `SeL4`.
- Prefer total functions and explicit result types.
- Avoid introducing axioms except where explicitly documented and reviewed.

## Proof guidance

- Start with theorem statements and `by` blocks that compile.
- Decompose large goals into helper lemmas in `SeL4/Proofs`.
- Minimize fragile `simp` usage across entire records; target fields directly.

## PR checklist

- [ ] `lake build` passes locally.
- [ ] New definitions have doc comments.
- [ ] New invariants include at least one supporting lemma.
- [ ] `docs/SPECIFICATION.md` updated for boundary or roadmap shifts.
