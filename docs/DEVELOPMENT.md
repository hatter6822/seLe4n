# seLe4n Development Guide

## 1. Purpose

This guide defines day-to-day implementation workflow and proof-engineering expectations.

Current stage: **M6 architecture-binding interface preparation is complete (WS-M6-A through WS-M6-E closed), and the active M7 slice focuses on repository-audit remediation workstreams (WS-A1 through WS-A8)**.
M4-B lifecycle-capability composition hardening is closed and treated as a stable dependency
baseline.

Primary goals for contributors:

- keep semantics executable and understandable,
- preserve theorem-entrypoint continuity across milestones,
- ship narrow, reviewable slices,
- keep docs synchronized with active and next slice plans,
- deliver audit-remediation hardening without regressing closed M1–M6 contracts.

---

## 2. Baseline contracts to preserve

Unless intentionally redesigned and documented, preserve:

1. M1 scheduler bundle + preservation theorem entrypoints.
2. M2 capability/CSpace transition surfaces and capability invariant composition.
3. M3 endpoint seed APIs and invariant entrypoints.
4. M3.5 handshake/scheduler coherence predicates and composed bundle surfaces.
5. Tier 0/1/2 required test gates and CI entrypoint parity.

---

## 3. Completed slice baseline: M4-A

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
   - illegal-state and illegal-authority branches are explicit via `KernelError.illegalState` and
     `KernelError.illegalAuthority`.

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
   - `Main.lean` includes lifecycle success/failure evidence,
   - fixture lines capture stable semantic intent only.

### 3.3 M4-A closeout expectations

Before calling follow-up work “M4-B ready,” maintainers should verify:

1. lifecycle transition branches are deterministic,
2. failure-path semantics are documented and traceable,
3. composed theorem entrypoints are easy to discover and reuse,
4. docs state what remains deferred.

### 3.4 M4-A non-goals

Do not include in this slice unless explicitly approved:

- full allocator internals,
- architecture-specific memory internals,
- broad policy redesign,
- unrelated IPC protocol expansion.

---

## 4. Completed predecessor slice baseline: M4-B

### 4.1 M4-B target outcomes (all complete)

1. Compose lifecycle with revoke/delete semantics.
2. Add stale-reference exclusion invariants.
3. Prove cross-bundle preservation theorems.
4. Add failure-path theorem coverage for lifecycle-capability interactions.
5. Expand Tier 3 checks and scenario coverage for lifecycle composition.

### 4.2 Delivery sequence used for M4-B closeout

1. **Transition composition pass**
   - introduce helper transitions and theorem statements for lifecycle+capability interactions.
2. **Invariant hardening pass**
   - define stale-reference exclusion and connect it to aliasing and authority constraints.
3. **Proof pass**
   - prove local preservation first, then cross-bundle theorems.
4. **Executable/test pass**
   - add trace stories for success/failure, then stabilize fixture anchors.
5. **Documentation pass**
   - update spec, development guide, and GitBook slices with exact outcome/deferred mapping.

### 4.3 Design guardrails retained from M4-B closeout

- preserve clean invariant layering;
- keep lifecycle assumptions out of unrelated IPC predicates;
- avoid monolithic “mega invariant” definitions that block review;
- keep theorem names searchable with `<transition>_preserves_<target>` style.


### 4.4 M4-B work package archive

Use narrow PR-sized work packages to reduce review risk:

1. **WP-1 transition composition**
   - introduce composition transitions + explicit failure semantics.
2. **WP-2 stale-reference invariants**
   - add stale-reference exclusion components + helper lemmas.
3. **WP-3 local preservation**
   - prove per-transition preservation over new components.
4. **WP-4 composed preservation**
   - prove cross-bundle composition theorems and failure-path preservation.
5. **WP-5 executable and fixture growth**
   - extend `Main.lean` scenarios and fixture anchors with rationale.
6. **WP-6 Tier 3/test anchor updates**
   - add symbol-level guardrails for newly introduced theorem surfaces.
7. **WP-7 doc closeout**
   - sync README/spec/development/testing/GitBook and state M5 deferrals.

### 4.5 Exit readiness signals used for M4-B

Before maintainers mark M4-B complete, verify:

- composed lifecycle+capability semantics are deterministic,
- stale-reference exclusion holds in machine-checked proofs,
- failure-path theorem surfaces exist and are reviewed,
- executable traces cover both success and failure composition stories,
- Tier 3 anchors include all newly claimed theorem/bundle names.

---

## 5. Transition planning discipline (M6 closeout → M7 start)

To reduce milestone thrash, each milestone-moving PR should state which closed outcomes it preserves and what next-slice outcomes it advances:

1. architecture-assumption interfaces that remain explicit and reviewable,
2. adapter-surface theorem hooks that preserve M1–M5 layering,
3. hardware-facing boundary assumptions documented as contracts.

A lightweight “what this unlocks next” paragraph is now expected in milestone-moving PRs.


### 5.1 Milestone narrative standard

For each milestone-moving PR, include a short section that states:

1. what concrete outcome moved (M6 closeout or M7 forward work),
2. what evidence command validates that movement,
3. what downstream dependency is now unblocked.

### 5.2 M6 workstream model

Use this workstream mapping for implementation planning and review checklists:

1. **WS-M6-A — assumption inventory and boundary extraction** ✅ **completed**
   - architecture assumptions are now explicit interface artifacts in `SeLe4n/Kernel/Architecture/Assumptions.lean` (`ArchAssumption`, `ContractRef`),
   - extracted assumptions are mapped to transition and invariant surfaces for reviewable boundary ownership.
2. **WS-M6-B — interface API and adapter semantics** ✅ **completed**
   - deterministic adapter APIs are now explicit in `SeLe4n/Kernel/Architecture/Adapter.lean`,
   - unsupported/invalid bound-context cases map through `mapAdapterError`,
   - runtime contracts carry explicit decidability witnesses for executable branch selection,
   - boundary state updates are deterministic via `advanceTimerState` and `writeRegisterState`.
3. **WS-M6-C — proof-layer integration** ✅ **completed**
   - local + composed preservation hooks over adapter assumptions are implemented in `SeLe4n/Kernel/Architecture/Invariant.lean` (`proofLayerInvariantBundle` and adapter preservation/failure theorems).
4. **WS-M6-D — evidence and test-surface expansion** ✅ **completed**
   - executable trace coverage now includes boundary success/failure branches in `Main.lean`,
   - fixture semantics and rationale are documented in `tests/scenarios/README.md` and anchored by `tests/fixtures/main_trace_smoke.expected`,
   - Tier 3 symbol/trace anchors now gate architecture-boundary evidence continuity.
5. **WS-M6-E — docs and handoff packaging** ✅ **completed**
   - README/spec/development/GitBook stage markers are synchronized,
   - explicit post-M6 unlocks and M7 deferrals are documented,
   - risk register updates are tied directly to architecture-boundary contracts.

### 5.3 Hardware direction note

The first real hardware architecture focus after M6 is **Raspberry Pi 5**.
M6 contributors should explicitly describe which Raspberry Pi 5 follow-on dependency each
milestone-moving PR unblocks.

---

## 6. Proof engineering standards

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

## 7. Documentation responsibilities

Any PR changing transitions, invariants, milestone scope, or tests must update docs in the same
commit range:

1. `docs/SEL4_SPEC.md`
2. `docs/DEVELOPMENT.md`
3. `README.md`
4. `docs/TESTING_FRAMEWORK_PLAN.md` and/or `tests/scenarios/README.md` as needed
5. `docs/gitbook/*` pages impacted by the change

Docs should explicitly answer:

- what exists now,
- what was added in this PR,
- what is deferred to next slice,
- what command evidence validates the change,
- what future slice this unlocks.

---

## 8. Required contributor validation loop

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

## 9. PR checklist (copy into PR descriptions)

- [ ] Scope fits one coherent milestone slice.
- [ ] Transition APIs expose explicit success/error branching.
- [ ] New invariants are named and documented.
- [ ] Preservation theorem entrypoints compile.
- [ ] `lake build` executed.
- [ ] `lake exe sele4n` executed.
- [ ] Hygiene scan executed.
- [ ] `test_fast` and `test_smoke` executed.
- [ ] Docs (including GitBook pages) updated in same commit range.
- [ ] Remaining proof debt identified explicitly.
- [ ] “Unlocks next slice” note included.

---

## 10. Codebase touch matrix (what to update when)

This section helps avoid partial updates when changing a subsystem.

### 10.1 Scheduler behavior changes

Touch at least:

- `SeLe4n/Kernel/Scheduler/Operations.lean` (transition semantics),
- `SeLe4n/Kernel/Scheduler/Invariant.lean` (component/bundle reasoning),
- any composed bundle module that imports scheduler invariants,
- docs (`README`, `SEL4_SPEC`, `DEVELOPMENT`, relevant GitBook chapters).

Validation focus:

- queue/current consistency remains explicit,
- scheduler theorem entrypoints remain discoverable,
- fixture/docs are updated if executable output semantics changed.

### 10.2 Capability changes

Touch at least:

- `SeLe4n/Kernel/Capability/Operations.lean` (transition semantics),
- `SeLe4n/Kernel/Capability/Invariant.lean` (invariant components + proofs),
- composed bundle references if interfaces changed,
- fixture/docs if executable output semantics changed.

Validation focus:

- attenuation properties preserved,
- lifecycle authority monotonicity still valid,
- composed bundle aliases remain stable.

### 10.3 IPC changes

Touch at least:

- `SeLe4n/Kernel/IPC/Operations.lean` and `SeLe4n/Kernel/IPC/Invariant.lean`,
- composed invariant/bundle module references,
- `Main.lean` scenario if behavior surface changed,
- Tier 2 fixture if output changed intentionally.

Validation focus:

- endpoint object validity + queue well-formedness,
- scheduler coherence predicates,
- local-first and composed preservation theorem layering.

### 10.4 Lifecycle/retype (M4) changes

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

## 11. Proof review checklist (maintainers)

When reviewing theorem changes, verify:

1. transition-level theorem statements still mirror executable semantics,
2. helper lemmas are local and narrowly scoped,
3. no hidden global simp behavior introduced,
4. composed bundle theorem depends on named components (not ad hoc unfolding),
5. theorem naming follows searchable `<transition>_preserves_<target>` pattern.

---

## 12. Documentation depth contract

For any milestone movement, docs should answer all of:

1. **What exists now?**
2. **What is being added in this slice?**
3. **What is intentionally deferred?**
4. **Which commands validate the change?**
5. **How does this affect composed invariant architecture?**
6. **What does this unlock for the next slice?**

If a doc update does not answer these questions, it is incomplete.
