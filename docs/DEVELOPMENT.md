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

### 1.1 Active-slice outcome details (implementation-ready)

To keep scope tight and proofs composable, treat the current slice as three explicit outcomes.

1. **Typed lifecycle transitions (`revoke`/`delete`)**
   - Operate on typed CSpace addresses (`SlotRef`/equivalent typed slot handle).
   - Keep failure behavior explicit via existing kernel error channels.
   - Reuse existing lookup/insert helper style to avoid branching state-access idioms.
2. **Lifecycle-aware authority monotonicity**
   - Capture that lifecycle operations cannot increase rights or introduce stronger authority.
   - Distinguish local attenuation constraints from global non-escalation constraints.
   - Document policy near definitions to keep theorem intent reviewable.
3. **Capability bundle preservation over lifecycle transitions**
   - Extend bundle composition rather than replacing existing components.
   - Add dedicated preservation theorem entrypoints for lifecycle operations.
   - Preserve existing read/write preservation results and scheduler proof stability.

### 1.2 Current audit evidence snapshot

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
9. For lifecycle transitions, prefer one transition = one clearly stated policy obligation,
   followed by helper lemmas and then composed-bundle preservation.
10. Avoid broad state-model rewrites while active-slice authority properties are still settling.

## 3. Recommended workflow per change

1. Confirm milestone impact (M2 foundation-only vs. future milestone prep).
2. Update spec text if acceptance criteria/scope move.
3. Implement Lean model/theorem changes in smallest coherent slices.
4. Run checks:
   - `lake build`
   - `lake exe sele4n` (when transition behavior is affected)
   - targeted repository scans (`rg -n "axiom|TODO|sorry"`) before merge
5. Summarize obligations completed and remaining in commit/PR notes.

### 3.1 Suggested micro-slice workflow for the active lifecycle slice

For each lifecycle transition (`delete`, `revoke`) and each authority rule:

1. Add/adjust predicate definition (authority + lifecycle safety component).
2. Add one local sanity lemma constraining theorem drift.
3. Add transition-local preservation theorem (`<transition>_preserves_<component>`).
4. Fold transition result into composed invariant theorem.
5. Re-run build and executable checks.

This sequence keeps each change reviewable and reduces proof breakage fan-out.

### 3.2 Recommended implementation order for active-slice delivery

1. Land typed delete transition and local lemmas.
2. Land typed revoke transition and local lemmas.
3. Introduce lifecycle-aware authority monotonicity predicates.
4. Extend composed capability invariant bundle.
5. Add composed preservation theorems for new transitions.
6. Refresh executable demonstration path and docs.

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
- For lifecycle operations, separate “address resolution” lemmas from “authority effect” lemmas.
- Keep revoke/delete proofs structurally parallel where possible to minimize maintenance burden.

## 5. Repository readability checklist

When touching a module, check the following to keep codebase comprehension high:

- exported names are discoverable from `SeLe4n.lean`,
- top-level doc comments exist for new public definitions,
- transition semantics are accompanied by at least one theorem use-site,
- docs reference the same milestone terminology as the code,
- examples in `Main.lean` remain concrete and executable.

## 6. Acceptance-driven delivery checklist (M2 active lifecycle slice)

Before merging work intended for the active M2 slice, verify:

- [x] capability invariant bundle entrypoint exists and includes uniqueness + lookup soundness + attenuation rule,
- [x] attenuation policy is documented in code and spec,
- [x] preservation lemmas exist for one read and one write transition,
- [x] completed M1 scheduler theorems still build unchanged,
- [x] no new `axiom`/`sorry` introduced,
- [x] `lake build` passes,
- [x] `lake exe sele4n` demonstrates executable transition behavior,
- [x] docs reflect progress and remaining proof debt.

Additional active-slice closure checks:

- [ ] typed revoke/delete transitions compile and use typed CSpace addresses,
- [ ] lifecycle-aware authority monotonicity predicates are defined and used in theorem statements,
- [ ] composed capability bundle includes lifecycle clauses,
- [ ] at least one lifecycle preservation theorem is proven for the composed bundle,
- [ ] executable example includes a lifecycle transition trace.

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

1. Expand CSpace operations to revoke/delete over typed addresses.
2. Land lifecycle-aware authority monotonicity constraints and helper lemmas.
3. Prove composed capability bundle preservation for lifecycle transitions.
4. Start M3 IPC semantics with endpoint transition definitions.
5. Lift reusable capability and scheduler proof utilities into stable helper modules.

Longer-term sequence:

6. Object lifecycle/retype safety (M4).
7. Refinement and correspondence track (M5+).

## 9. PR and review notes for the active slice

When submitting lifecycle-slice changes, include a short “proof-impact summary” in PR text:

1. New/changed transitions.
2. New/changed invariant components.
3. New/changed preservation theorem entrypoints.
4. Any intentional proof debt carried to next increment.

## 10. Anti-patterns to avoid

- Expanding into IPC/MMU/retype semantics before current-slice proofs stabilize.
- Embedding milestone assumptions in code without documenting them in the spec.
- Monolithic proof scripts that block incremental refactoring.
- Deferring policy decisions (e.g., attenuation constraints) until late in proof work.
