# seLe4n Development Guide

## 1. Purpose

This guide defines the day-to-day implementation workflow for seLe4n, with emphasis on:

- maintaining executable semantics,
- preserving established theorem surfaces,
- delivering milestones in small, reviewable proof slices.

The codebase is currently in a **post-M2 / pre-M3** phase.

---

## 2. Current baseline and active focus

### 2.1 Baseline guarantees to keep stable

The following are considered stable and must not regress:

1. M1 scheduler invariant bundle entrypoints and preservation behavior.
2. M2 capability lifecycle transitions (`lookup`, `insert`, `mint`, `delete`, `revoke`).
3. Capability invariant bundle structure and lifecycle authority monotonicity entrypoints.
4. Executable sanity path in `Main.lean`.

### 2.2 Active focus: M3 IPC seed

Current development should prioritize a small endpoint IPC seed with theorem-backed invariants.
Keep changes narrow and compositional so M1/M2 proof obligations remain intact.

---

## 3. Recommended implementation sequence (M3 IPC seed)

Work in this order unless a blocking dependency requires adjustment:

1. **Model-first minimal IPC state**
   - Add only the endpoint state required for one send/receive story.
   - Favor explicit, typed fields over generic maps when possible.

2. **Transitions second**
   - Implement one send transition and one receive transition.
   - Keep transition semantics deterministic and easy to unfold in proofs.
   - Current status: typed endpoint entrypoints (`endpointSend`, `endpointReceive`) are present;
     continue by proving IPC-specific invariants against them.

3. **Invariant components third**
   - Define one endpoint queue well-formedness predicate.
   - Define one endpoint/object validity predicate.
   - Bundle under a clearly named IPC invariant entrypoint.

4. **Local helper lemmas fourth**
   - Add lookup/update lemmas close to transition definitions.
   - Keep helper statements small and reusable.

5. **Preservation theorems fifth**
   - Prove send preserves IPC invariant bundle.
   - Prove receive preserves IPC invariant bundle.
   - Compose with existing M1/M2 bundle entrypoints only after local proofs are stable.

6. **Executable demonstration last**
   - Extend `Main.lean` trace to include IPC behavior.
   - Confirm current demo behavior still executes.

---

## 4. Proof hygiene standards

1. Prefer theorem names in `<transition>_preserves_<invariant>` form.
2. Keep conjunction-heavy invariant bundles factored with named components.
3. Avoid broad global simp attribute changes; use local `simp` scopes.
4. Keep proof scripts short and layered:
   - unfold transition,
   - split success/error branches,
   - dispatch local helper lemmas.
5. Preserve theorem statement stability when refactoring internals.
6. Do not introduce `axiom` or `sorry` into core Lean modules.

---

## 5. Documentation update requirements

Any PR that changes transitions or invariant composition must update docs in the same commit range:

1. `docs/SEL4_SPEC.md`:
   - scope/status,
   - acceptance criteria,
   - next-slice outcomes.
2. `docs/DEVELOPMENT.md`:
   - implementation order,
   - proof workflow,
   - review checklist.
3. `README.md`:
   - current milestone stage summary,
   - quick contributor verification loop.

---

## 6. Validation commands

Run this minimum command set before opening a PR:

```bash
lake build
lake exe sele4n
rg -n "axiom|sorry|TODO" SeLe4n Main.lean
```

If a command cannot be run due to environment constraints, document the limitation explicitly in
PR notes.

---

## 7. PR checklist (required)

Include this checklist in your PR description and mark each item:

- [ ] Scope is limited to one coherent milestone slice.
- [ ] New transitions have explicit error branches.
- [ ] New invariant components are named and documented.
- [ ] Preservation theorem entrypoints compile.
- [ ] `lake build` executed.
- [ ] `lake exe sele4n` executed.
- [ ] Hygiene scan (`axiom|sorry|TODO`) executed.
- [ ] Docs updated to match current implementation stage.
- [ ] Remaining proof debt is explicitly identified.

---

## 8. Review heuristics for maintainers

Reviewers should verify:

1. Transition semantics are readable without deep tactic archaeology.
2. Helper lemmas match transition granularity (not overly generic).
3. Invariant bundle changes are justified and scoped.
4. New executable examples provide concrete behavior evidence.
5. Milestone claims in docs match the code present in the same range.

---

## 9. Anti-patterns to avoid

- Mixing large model redesign with new proof obligations in one PR.
- Introducing IPC/MMU/retype details simultaneously during M3 seed.
- Hiding semantics in abstraction layers that make transition unfolding opaque.
- Deferring policy decisions that proofs depend on.
- Marking milestone completion without executable and theorem evidence.
