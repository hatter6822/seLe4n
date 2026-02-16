# Current Slice: M4-A Lifecycle/Retype Foundations

## Objective

Add first-class lifecycle/retype semantics to the executable model and prove that capability/object
relationships remain coherent through those updates.

## Detailed target outcomes

## Implementation status

- ✅ Step 1 complete: state-model lifecycle metadata is now explicit for object identity and
  capability reference ownership mapping (including revoke-path sibling cleanup).
- ✅ Step 2 complete: `lifecycleRetypeObject` adds deterministic success/error branching with
  explicit `KernelError.illegalState` and `KernelError.illegalAuthority` branches, and executable
  traces now cover both failure branches plus success.
- ✅ Step 3 complete: lifecycle invariants are now defined as narrow named components with explicit
  separation between identity/aliasing (`lifecycleIdentityAliasingInvariant`) and
  capability-reference (`lifecycleCapabilityReferenceInvariant`) constraints.
- ✅ Step 4 complete: transition-local helper lemmas now package lifecycle retype lookup and
  runnable-membership transport facts near lifecycle operations, avoiding duplicated transition
  case-analysis in downstream proofs.
- ✅ Step 5 complete: lifecycle preservation theorem entrypoints now prove local lifecycle bundle
  preservation first and compose with scheduler/capability/IPC bundles via an M4-A composed bundle
  surface (`m4aLifecycleInvariantBundle`) with explicit endpoint/scheduler side-condition hooks.


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
