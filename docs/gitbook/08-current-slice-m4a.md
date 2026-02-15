# Current Slice: M4-A Lifecycle/Retype Foundations

## Objective

Add first-class lifecycle/retype semantics to the executable model and prove that capability/object
relationships remain coherent through those updates.

## Detailed target outcomes

1. **Transition surface**
   - at least one lifecycle operation with explicit success/error outcomes.
2. **Identity discipline**
   - invariants preventing illegal identity reuse and invalid aliasing.
3. **Capability coherence**
   - invariants ensuring capabilities remain target-valid/type-compatible after transitions.
4. **Proof surface**
   - transition-level preservation theorem entrypoints.
5. **Executable evidence**
   - scenario extension in `Main.lean` and fixture updates where behavior changes intentionally.

## Review heuristics

- are failure branches explicit and deterministic?
- are invariants narrow and named?
- are preservation proofs layered local-first?
- is executable output still meaningful and stable?
