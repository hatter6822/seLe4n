# Completed Slice: M4-A Lifecycle/Retype Foundations

## Objective

Add first-class lifecycle/retype semantics to the executable model and prove that capability/object
relationships remain coherent through those updates.

## Slice status

M4-A is complete for its planned six-step scope and now serves as the stable launch point for M4-B.

## Detailed target outcomes

1. **Transition surface**
   - at least one lifecycle operation with explicit success/error outcomes,
   - deterministic semantics suitable for theorem-driven reasoning.

2. **Identity discipline**
   - invariants preventing illegal identity reuse and invalid aliasing,
   - clean separation between identity constraints and capability-reference constraints.

3. **Capability coherence**
   - invariants ensuring capabilities remain target-valid/type-compatible after transitions,
   - authority assumptions preserved from M2 contracts.

4. **Proof surface**
   - transition-level preservation theorem entrypoints,
   - composed lifecycle+existing-bundle theorem surface.

5. **Executable evidence**
   - scenario extension in `Main.lean`,
   - fixture updates where behavior changes intentionally.

## Implementation status snapshot

- ✅ Step 1 complete: state-model lifecycle metadata is explicit for object identity and
  capability-reference ownership mapping.
- ✅ Step 2 complete: `lifecycleRetypeObject` includes deterministic success/error branches,
  including illegal-state and illegal-authority behavior.
- ✅ Step 3 complete: lifecycle invariants are narrow named components (`identity/aliasing` and
  `capability-reference` families).
- ✅ Step 4 complete: transition-local helper lemmas package lookup and membership transport facts.
- ✅ Step 5 complete: local lifecycle preservation and composed bundle preservation entrypoints are
  machine-checked.
- ✅ Step 6 complete: executable traces and fixture anchors cover unauthorized, illegal-state, and
  success paths.

## What this slice unlocks

M4-A unlocks M4-B by providing:

1. stable lifecycle transition semantics to compose with capability revocation/deletion,
2. reusable theorem entrypoints for stale-reference exclusion proofs,
3. regression-friendly trace evidence that can be extended without rewriting baseline semantics.

## Known deferrals (intentional)

These remain out of scope for M4-A and should not be backfilled silently:

- allocator policy internals,
- architecture-specific MMU/ASID details,
- large policy-engine redesign.

## Review heuristics

- are failure branches explicit and deterministic?
- are invariants narrow and named?
- are preservation proofs layered local-first then composed?
- is executable output still meaningful and stable?
- does the PR state what it unlocks in M4-B?
