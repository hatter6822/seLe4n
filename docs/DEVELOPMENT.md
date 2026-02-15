# Development Guide

## 1. Current phase

The project has completed bootstrap and **M1: Scheduler Integrity**.
Development has completed the **M2 Foundation Slice: typed CSpace lookup and mint model** and now focuses on post-foundation capability lifecycle work.

### Current objective slice (next step)

The active implementation target is capability-lifecycle expansion beyond the completed M2 foundation slice.

Audited outcomes from the completed M2 foundation slice:

- ✅ typed capability operations exist for lookup and write/update paths,
- ✅ state/model helpers exist for slot-level capability ownership representation,
- ✅ initial capability invariants are defined and composed,
- ✅ preservation is proven for at least one read and one write transition,
- ✅ executable behavior and existing scheduler proofs remain stable.

Next target outcomes for the active slice:

- add revoke/delete transitions over typed CSpace addresses,
- define lifecycle-aware authority monotonicity constraints,
- prove preservation of the capability invariant bundle across lifecycle transitions.

### 1.1 Current audit evidence snapshot

Latest repository-wide audit commands and expected outcomes:

- `lake build` passes (current run: passes, with one non-blocking linter hint in `SeLe4n/Kernel/API.lean`),
- `lake exe sele4n` runs scheduler + CSpace demonstration path,
- `rg -n "axiom|TODO|sorry" SeLe4n Main.lean` returns no unresolved proof escapes or stale TODO markers.

## 2. Working agreement

1. Spec-first: update `docs/SEL4_SPEC.md` when scope or acceptance criteria change.
2. Keep executable behavior intact (`Main.lean` path should remain runnable).
3. Prove before broadening: land small, composable invariants with corresponding proofs.
4. Prefer total functions and explicit error channels (`Except`) over partial definitions.

Additional milestone agreements:

5. Keep theorem statements stable once introduced; iterate via helper lemmas first.
6. Make policy choices explicit near definitions (not only in commit/PR text).
7. When a proof blocks, land minimal supporting lemmas rather than broad refactors.
8. Do not regress completed M1 scheduler invariants while extending M2 semantics.

## 3. Recommended workflow per change

1. Confirm milestone impact (M2 foundation-only vs. future milestone prep).
2. Update spec text if acceptance criteria/scope move.
3. Implement Lean model/theorem changes in smallest coherent slices.
4. Run checks:
   - `lake build`
   - `lake exe sele4n` (when transition behavior is affected)
   - targeted repository scans (`rg -n "axiom|TODO|sorry"`) before merge
5. Summarize obligations completed and remaining in commit/PR notes.

### 3.1 Suggested micro-slice workflow for M2 foundation

For each capability invariant component:

1. Add/adjust predicate definition.
2. Add one sanity lemma constraining theorem drift.
3. Add read-path preservation lemma (`lookup`-style).
4. Add write-path preservation lemma (`insert`/`mint`-style).
5. Fold results into composed invariant theorem.
6. Re-run build and executable checks.

This sequence keeps each change reviewable and reduces proof breakage fan-out.

## 4. Coding and proof conventions

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

M2 proof hygiene conventions:

- Use explicit names for bundle members and avoid anonymous conjunctions without aliases.
- Group helper lemmas by subject (`lookup`, slot mutations, rights attenuation facts).
- Keep `simp` sets predictable; avoid global simp attributes unless broadly safe.
- Avoid introducing abstractions that hide state updates while invariants are still evolving.

## 5. Repository readability checklist

When touching a module, check the following to keep codebase comprehension high:

- exported names are discoverable from `SeLe4n.lean`,
- top-level doc comments exist for new public definitions,
- transition semantics are accompanied by at least one theorem use-site,
- docs reference the same milestone terminology as the code,
- examples in `Main.lean` remain concrete and executable.

## 6. Acceptance-driven delivery checklist (M2 foundation)

Before merging work intended for the active M2 slice, verify:

- [x] capability invariant bundle entrypoint exists and includes uniqueness + lookup soundness + attenuation rule,
- [x] attenuation policy is documented in code and spec,
- [x] preservation lemmas exist for one read and one write transition,
- [x] completed M1 scheduler theorems still build unchanged,
- [x] no new `axiom`/`sorry` introduced,
- [x] `lake build` passes,
- [x] `lake exe sele4n` demonstrates executable transition behavior,
- [x] docs reflect progress and remaining proof debt.

## 7. Audit protocol for milestone completion claims

When marking any milestone item complete, record evidence in the same commit range:

1. **Code evidence**: definitions and theorem statements exist in tracked Lean modules.
2. **Proof evidence**: preservation theorem(s) compile under `lake build`.
3. **Executable evidence**: runnable example path (`lake exe sele4n` or equivalent).
4. **Hygiene evidence**: no unresolved proof escapes (`axiom`, `sorry`) and no stale TODO markers
   in Lean code.

Recommended command set:

- `lake build`
- `lake exe sele4n`
- `rg -n "axiom|TODO|sorry" SeLe4n Main.lean`

## 8. Development path ahead

Near-term sequence after the completed M2 foundation slice:

1. Expand CSpace operations to revoke/delete and prove local authority constraints.
2. Start M3 IPC semantics with endpoint transition definitions.
3. Lift reusable capability and scheduler proof utilities into stable helper modules.

Longer-term sequence:

4. Object lifecycle/retype safety (M4).
5. Refinement and correspondence track (M5+).

## 9. Anti-patterns to avoid

- Expanding into IPC/MMU/retype semantics before current-slice proofs stabilize.
- Embedding milestone assumptions in code without documenting them in the spec.
- Monolithic proof scripts that block incremental refactoring.
- Deferring policy decisions (e.g., attenuation constraints) until late in proof work.
