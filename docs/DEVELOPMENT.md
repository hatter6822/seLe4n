# seLe4n Development Guide

## 1. Purpose

This guide defines day-to-day implementation workflow and proof-engineering expectations.

Current stage: **M4-A lifecycle/retype foundations (all six implementation steps completed)**.

Primary goals for contributors:

- keep semantics executable and understandable,
- preserve theorem-entrypoint continuity across milestones,
- ship narrow, reviewable slices,
- keep docs synchronized with active and next slice plans.

---

## 2. Baseline contracts to preserve

Unless intentionally redesigned and documented, preserve:

1. M1 scheduler bundle + preservation theorem entrypoints.
2. M2 capability/CSpace transition surfaces and capability invariant composition.
3. M3 endpoint seed APIs and invariant entrypoints.
4. M3.5 handshake/scheduler coherence predicates and composed bundle surfaces.
5. Tier 0/1/2 required test gates and CI entrypoint parity.

---

## 3. Current slice implementation plan: M4-A

### 3.1 M4-A target outcomes (implementation contract)

1. Add typed lifecycle/retype transition API.
2. Add object identity + aliasing lifecycle invariants.
3. Add capability-object coherence invariants.
4. Add preservation theorem entrypoints for new lifecycle transitions.
5. Add executable evidence in `Main.lean` and fixture-backed smoke coverage.

### 3.2 Recommended implementation sequence (M4-A)

1. **State-model preparation** ✅ **completed**
   - lifecycle metadata introduced for first transition story only,
   - ownership remains explicit via object-store identity metadata and capability reference mapping.

2. **Lifecycle transition(s)** ✅ **completed**
   - deterministic success/error branching implemented via `lifecycleRetypeObject`,
   - illegal-state and illegal-authority branches are explicit via `KernelError.illegalState` and `KernelError.illegalAuthority`.

3. **Invariant definitions** ✅ **completed**
   - narrow, named lifecycle invariants are defined in `SeLe4n/Kernel/Lifecycle/Invariant.lean`,
   - identity/aliasing constraints are separated from capability-reference constraints via
     `lifecycleIdentityAliasingInvariant` and `lifecycleCapabilityReferenceInvariant`.

4. **Local helper lemmas** ✅ **completed**
   - transition-local lookup/membership lemmas are now defined near lifecycle transition code,
   - lifecycle proofs reuse helper theorems instead of repeating transition case-analysis.

5. **Preservation theorem entrypoints** ✅ **completed**
   - local lifecycle component preservation entrypoints are now machine-checked,
   - composed entrypoints now bridge lifecycle with existing scheduler/capability/IPC bundle layers.

6. **Executable demonstration + fixture update** ✅ **completed**
   - extend `Main.lean` for lifecycle success path,
   - add fixture lines only for stable semantic output.

### 3.3 M4-A non-goals

Do not include in this slice unless explicitly approved:

- full allocator internals,
- architecture-specific memory internals,
- broad policy redesign,
- unrelated IPC protocol expansion.

---

## 4. Next slice preparation: M4-B

### 4.1 M4-B target outcomes

1. Compose lifecycle with revoke/delete semantics.
2. Add stale-reference exclusion invariants.
3. Prove cross-bundle preservation theorems.
4. Add failure-path theorem coverage for lifecycle-capability interactions.
5. Expand Tier 3 checks and scenario coverage for lifecycle composition.

### 4.2 Design guardrails for M4-B readiness

- preserve clean invariant layering;
- keep lifecycle assumptions out of unrelated IPC predicates;
- avoid monolithic “mega invariant” definitions that block review.

---

## 5. Proof engineering standards

1. Prefer explicit theorem statements and local proof structure over brittle tactic compression.
2. Keep conjunction-heavy invariants factored into named components.
3. Use local simplification blocks; avoid global `simp` side effects.
4. Structure proofs by:
   - transition unfold,
   - result-case split,
   - local helper lemma application,
   - invariant component discharge.
5. Keep helper lemmas physically near transitions they support.
6. Do not introduce `axiom` or `sorry` in core modules.

---

## 6. Documentation responsibilities

Any PR changing transitions, invariants, milestone scope, or tests must update docs in the same
commit range:

1. `docs/SEL4_SPEC.md`
2. `docs/DEVELOPMENT.md`
3. `README.md`
4. `docs/TESTING_FRAMEWORK_PLAN.md` and/or `tests/scenarios/README.md` as needed
5. `docs/gitbook/*` pages impacted by the change

---

## 7. Required contributor validation loop

Run before opening a PR:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
```

Recommended additional checks:

```bash
lake build
lake exe sele4n
rg -n "axiom|sorry|TODO" SeLe4n Main.lean
./scripts/test_full.sh
```

If a command is blocked by environment limitations, report the limitation and impact.

---

## 8. PR checklist (copy into PR descriptions)

- [ ] Scope fits one coherent milestone slice.
- [ ] Transition APIs expose explicit success/error branching.
- [ ] New invariants are named and documented.
- [x] Preservation theorem entrypoints compile.
- [ ] `lake build` executed.
- [ ] `lake exe sele4n` executed.
- [ ] Hygiene scan executed.
- [ ] `test_fast` and `test_smoke` executed.
- [ ] Docs (including GitBook pages) updated in same commit range.
- [ ] Remaining proof debt identified explicitly.

---

## 9. Codebase touch matrix (what to update when)

This section helps avoid partial updates when changing a subsystem.

### 9.1 Scheduler behavior changes

Touch at least:

- `SeLe4n/Kernel/Scheduler/Operations.lean` (transition semantics),
- `SeLe4n/Kernel/Scheduler/Invariant.lean` (component/bundle reasoning),
- any composed bundle module that imports scheduler invariants,
- docs (`README`, `SEL4_SPEC`, `DEVELOPMENT`, relevant GitBook chapters).

Validation focus:

- queue/current consistency remains explicit,
- `*_preserves_schedulerInvariantBundle` theorem surfaces still compile,
- executable trace remains coherent if scheduling output changed.

### 9.2 Capability/CSpace changes

Touch at least:

- `SeLe4n/Kernel/Capability/Operations.lean`,
- `SeLe4n/Kernel/Capability/Invariant.lean`,
- fixture/docs if executable output semantics changed.

Validation focus:

- attenuation properties preserved,
- lifecycle authority monotonicity still valid,
- composed bundle aliases remain stable.

### 9.3 IPC changes

Touch at least:

- `SeLe4n/Kernel/IPC/Invariant.lean` (transitions + invariants + proofs),
- composed invariant/bundle module references,
- `Main.lean` scenario if behavior surface changed,
- Tier 2 fixture if output changed intentionally.

Validation focus:

- endpoint object validity + queue well-formedness,
- scheduler coherence predicates,
- local-first and composed preservation theorem layering.

### 9.4 Lifecycle/retype (M4) changes

Touch at least:

- model files when object metadata evolves,
- lifecycle transition implementation module(s),
- lifecycle invariant components,
- cross-bundle composition entrypoints,
- milestone docs and GitBook M4 chapters.

Validation focus:

- identity/aliasing safety,
- capability-object coherence,
- deterministic error-path behavior,
- fixture signal quality for lifecycle scenarios.

---

## 10. Proof review checklist (maintainers)

When reviewing theorem changes, verify:

1. transition-level theorem statements still mirror executable semantics,
2. helper lemmas are local and narrowly scoped,
3. no hidden global simp behavior introduced,
4. composed bundle theorem depends on named components (not ad hoc unfolding),
5. theorem naming follows searchable `<transition>_preserves_<target>` pattern.

---

## 11. Documentation depth contract

For any milestone movement, docs should answer all of:

1. **What exists now?**
2. **What is being added in this slice?**
3. **What is intentionally deferred?**
4. **Which commands validate the change?**
5. **How does this affect composed invariant architecture?**

If a doc update does not answer these five, it is incomplete.
