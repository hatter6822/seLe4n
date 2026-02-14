# Development Guide

## 1. Current phase

The project has completed bootstrap and is now in **M1: Scheduler Integrity**.
Development should prioritize invariant strengthening and proof coverage for existing scheduling
transitions before adding major new subsystems.

### Current objective slice (next step)

The active implementation target is **Scheduler Invariant Bundle v1**.

Current status:

- ✅ Step 1 complete: runnable queue uniqueness (`runQueueUnique`) is defined and preserved,
- ✅ Step 2 complete: current-thread object validity (`currentThreadValid`) is defined and preserved,
- ✅ Step 3 complete: explicit strict queue/current policy (`queueCurrentConsistent`) is defined and preserved,
- ✅ Composed preservation coverage over `chooseThread`, `schedule`, and `handleYield` is complete for v1 bundle.

## 2. Working agreement

1. Spec-first: update `docs/SEL4_SPEC.md` when scope or acceptance criteria change.
2. Keep executable behavior intact (`Main.lean` path should remain runnable).
3. Prove before broadening: land small, composable invariants with corresponding proofs.
4. Prefer total functions and explicit error channels (`Except`) over partial definitions.

Additional M1-specific agreements:

5. Keep theorem statements stable once introduced; iterate via helper lemmas first.
6. Make policy choices explicit near definitions (not only in PR text).
7. When a proof blocks, land minimal supporting lemmas rather than broad refactors.

## 3. Recommended workflow per change

1. Confirm milestone impact (M1-only vs. future milestone prep).
2. Update spec text if acceptance criteria/scope move.
3. Implement Lean model/theorem changes in smallest coherent slices.
4. Run checks:
   - `lake build`
   - `lake exe sele4n` (when transition behavior is affected)
5. Summarize proof obligations completed and remaining in PR notes.

### 3.1 Suggested micro-slice workflow for M1

For each invariant component:

1. Add/adjust predicate definition.
2. Add one small sanity lemma (shape/property) to constrain later proof drift.
3. Add transition-specific preservation lemma(s).
4. Fold result into composed invariant preservation theorem.
5. Re-run build and executable checks.

This sequence keeps each change reviewable and reduces proof breakage fan-out.

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

M1 proof hygiene conventions:

- Prefer explicit theorem names for bundle members, e.g.:
  - `runQueueUnique`,
  - `currentThreadValid`,
  - `queueCurrentConsistent`.
- Group helper lemmas by subject (`runQueue`, object lookup, transition step facts).
- Keep `simp` sets predictable; avoid global simp attributes unless broadly safe.
- Avoid introducing abstractions that hide transition state updates during M1.

## 5. Acceptance-driven delivery checklist (M1)

Before merging work intended for M1, verify:

- [x] invariant bundle entrypoint exists and includes queue/current consistency + runQueue uniqueness + current-thread object validity,
- [x] queue/current policy is documented in-code and in spec,
- [x] preservation lemmas exist for `chooseThread`, `schedule`, and `handleYield` for all bundle components,
- [x] no new `axiom` introduced,
- [x] `lake build` passes,
- [x] `lake exe sele4n` still demonstrates scheduler execution,
- [x] docs reflect both progress and remaining proof debt.

## 6. Development path ahead (post-next-step preview)

After Scheduler Invariant Bundle v1 is complete, expected follow-on work is:

1. Strengthen scheduler model edges (idle/blocked transitions as needed).
2. Begin M2 prep by isolating capability/CSpace interfaces from scheduler proofs.
3. Carry forward reusable proof utilities while keeping scheduler theorems stable.

This preview is directional only; M1 completion criteria remain authoritative.

## 7. Anti-patterns to avoid

- Expanding into IPC/MMU/retype semantics before M1 proofs stabilize.
- Embedding milestone assumptions in code without documenting them in the spec.
- Monolithic proof scripts that block incremental refactoring.
- Deferring policy decisions (strict vs. relaxed consistency) until late in proof work.
