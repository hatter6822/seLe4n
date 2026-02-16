# seLe4n Specification and Milestone Plan

## 1. Purpose

This document is the normative specification baseline for seLe4n.

It defines:

1. What milestone behavior is already closed and considered stable.
2. The **current delivery slice** (M5) with concrete target outcomes.
3. The **next delivery slice** preview (M6-directional) so work continues without roadmap drift.
4. Acceptance criteria and non-goals for focused, reviewable implementation.
5. Change-control expectations for code, proofs, executable traces, and docs.
6. A forward plan for the next milestone family so contributors can stage work intentionally.

Current stage: **M5 service-graph semantics and policy-oriented authority layering (active; WS-M5-A, WS-M5-B, WS-M5-C, WS-M5-D, and WS-M5-E complete; WS-M5-F closeout in progress)**.

---

## 2. Milestone map

- **Bootstrap (complete)**: executable model skeleton and transition style.
- **M1 (complete)**: scheduler integrity bundle and preservation.
- **M2 (complete)**: typed CSpace operations + capability lifecycle authority invariants.
- **M3 (complete)**: endpoint send/receive seed semantics + IPC invariant seed bundle.
- **M3.5 (complete)**: waiting/handshake IPC semantics + scheduler coherence contract.
- **M4-A (complete)**: lifecycle/retype transition foundations + initial lifecycle invariants.
- **M4-B (complete)**: lifecycle-capability composition hardening and richer scenario coverage.
- **M5 (current slice)**: service-graph semantics and policy-oriented authority constraints.
- **M6 (next slice preview)**: architecture-binding interfaces and hardware-facing assumption hardening.

---

## 3. Stable baseline contracts (must not regress)

The following contracts are considered stable and preserved while M5 evolves:

1. M1 scheduler invariant bundle and entrypoint preservation theorems.
2. M2 capability/CSpace transition APIs (`lookup`, `insert`, `mint`, `delete`, `revoke`) and
   composed capability invariant bundle.
3. M3 endpoint APIs (`endpointSend`, `endpointReceive`) and IPC seed invariant layering.
4. M3.5 waiting-receiver handshake behavior and scheduler-contract predicate surfaces.
5. Tier 0/1/2 required test gates and CI invocation through repository scripts.

Any intentional baseline changes must be documented in this file, `docs/DEVELOPMENT.md`, and
`README.md` in the same commit range.

---

## 4. Completed slice baseline: M4-A lifecycle/retype foundations

### 4.1 Objective

Introduce the first deterministic object lifecycle/retype transition surface and machine-checked
safety scaffolding that connects object-store evolution with capability references.

### 4.2 Why now

M3.5 established IPC-scheduler coherence. The next major safety risk is object lifecycle evolution:
without typed lifecycle transitions and invariants, capability reasoning can drift away from object
state evolution.

### 4.3 M4-A target outcomes (all required)

1. **Lifecycle transition API**
   - add at least one executable lifecycle/retype operation with explicit success/error outcomes,
   - ensure deterministic state updates and architecture-neutral semantics,
   - ensure unauthorized and illegal-state failures are first-class, testable branches.

2. **Object identity + aliasing invariants**
   - define invariants preventing invalid object identity reuse in active scope,
   - define invariants constraining aliasing after lifecycle transitions,
   - separate identity constraints from capability-reference constraints for compositional proofs.

3. **Capability-object coherence invariants**
   - specify that capability references remain type-compatible and target-valid after lifecycle
     updates,
   - ensure lifecycle updates preserve authority monotonicity assumptions already used by M2,
   - expose these constraints as reusable theorem assumptions for next-slice composition.

4. **Local helper lemmas + preservation theorem entrypoints**
   - provide transition-local lookup/membership helper lemmas near lifecycle transitions to keep
     proof scripts concise,
   - provide machine-checked `<transition>_preserves_<invariant>` entrypoints for each new
     lifecycle transition,
   - include at least one composed theorem over lifecycle + existing capability invariant bundle.

5. **Executable + fixture evidence**
   - extend `Main.lean` with lifecycle success and failure stories,
   - update `tests/fixtures/main_trace_smoke.expected` with stable semantic fragments if behavior
     output changes intentionally,
   - keep traces readable enough for regression triage by non-authors.

### 4.4 M4-A delivery quality bar

A change is M4-A complete only when all of the following are true:

1. transition semantics compile and are deterministic,
2. invariants are named, factored, and directly referenced by preservation theorems,
3. executable trace evidence demonstrates behavior shape for at least one success and one failure,
4. docs identify deferred work explicitly rather than implying hidden completion.

### 4.5 M4-A acceptance criteria

1. `./scripts/test_fast.sh` succeeds.
2. `./scripts/test_smoke.sh` succeeds.
3. `lake build` succeeds.
4. `lake exe sele4n` succeeds and includes lifecycle behavior evidence.
5. Hygiene scan is clean:
   - `rg -n "axiom|sorry|TODO" SeLe4n Main.lean`.
6. Lifecycle invariants are named, documented, and composed with existing bundle structure.
7. Preservation theorem entrypoints compile without introducing proof placeholders.

### 4.6 Explicit non-goals (M4-A)

- Full allocator/heap policy modeling.
- Architecture-specific MMU/ASID internals.
- Full reply-cap protocol redesign.
- End-to-end C refinement correspondence.
- General policy engine redesign.

---

## 5. Completed predecessor slice: M4-B lifecycle-capability composition hardening

### 5.1 Objective

Strengthen lifecycle semantics by integrating lifecycle updates with capability revocation/deletion
flows and proving stronger stale-reference exclusion properties.

### 5.2 M4-B target outcomes

1. **Lifecycle + revoke/delete composition**
   - define at least one composed transition story where lifecycle and capability lifecycle
     operations interact explicitly,
   - prove semantic ordering assumptions (retype-before-delete, delete-before-reuse) through
     executable transition contracts.

2. **Stale reference exclusion invariants**
   - add invariants ruling out stale capability references to retired/retyped object identities,
   - connect stale-reference exclusion to existing aliasing and authority constraints.

3. **Cross-bundle preservation theorem surface**
   - prove composed preservation covering lifecycle invariants plus capability lifecycle authority
     invariants,
   - keep theorem surfaces layered so M5 policy reasoning can reuse them without rewrite.

4. **Error-path completeness**
   - include explicit failure-path theorems (invalid type, stale object reference, illegal
     authority),
   - ensure error paths preserve baseline invariant bundles and do not silently weaken assumptions.

5. **Scenario + testing growth**
   - expand executable scenarios to include success and failure lifecycle stories,
   - extend Tier 3 checks with M4-specific theorem/bundle anchors,
   - document scenario intent in docs so failures are diagnosable by milestone.

### 5.3 M4-B acceptance baseline

1. Existing required gates remain green (`test_fast`, `test_smoke`).
2. M4-A lifecycle contracts remain intact while M4-B features land.
3. Tier 2 fixture remains stable and intentional.
4. Tier 3 includes lifecycle-capability composition anchors.
5. Documentation clearly updates next-slice roadmap direction (M5 preview).

### 5.4 M4-B planned delivery sequence

1. introduce composeable lifecycle/capability transition helpers,
2. codify stale-reference invariants and local helper lemmas,
3. prove local preservation for new helpers,
4. prove composed cross-bundle preservation,
5. extend executable traces and fixture anchors,
6. publish docs updates and remaining M5 debt.


### 5.5 M4-B workstream acceptance matrix

For review clarity, M4-B evidence should map to these five workstreams:

1. **WS-A semantics** ✅ **completed**: lifecycle-capability composed transition behavior is deterministic and
   includes explicit failure branches.
2. **WS-B invariants** ✅ **completed**: stale-reference exclusion is formalized as named components
   and linked to identity/authority assumptions.
3. **WS-C proofs** ✅ **completed**: local-first preservation is complete, then composed cross-bundle preservation is
   proven without placeholder debt.
4. **WS-D executable evidence** ✅ **completed**: `Main.lean` includes composition success/failure scenarios and Tier
   2 fixture anchors capture stable semantics.
5. **WS-E testing anchors** ✅ **completed**: Tier 3 includes M4-B theorem/bundle symbols, nightly extension
   candidates are staged in Tier 4 entrypoints, and failure triage references exact script commands.

### 5.6 M4-B completion evidence checklist

A PR series claiming M4-B completion should include all of:

- explicit transition semantics covering lifecycle + revoke/delete interaction,
- stale-reference exclusion invariants and helper lemmas,
- success-path and failure-path preservation theorem entrypoints,
- fixture-backed executable scenarios for composed behavior,
- Tier 3 anchor updates for new theorem/bundle surfaces,
- synchronized docs describing what is complete and what is deferred to M5.

---

## 6. Current slice: M5 service graph + policy surfaces

### 6.1 M5 target direction: service graph + policy surfaces

The active milestone family (M5) targets operational realism while preserving theorem layering:

1. model service restart/isolation stories that exercise lifecycle+IPC+capability composition,
2. introduce policy-friendly authority constraints without replacing existing invariants,
3. prepare architecture-binding interfaces as explicit assumptions rather than implicit behavior.

### 6.2 M5 entry requirements (already satisfied)

- M4-B stale-reference properties are merged and stable,
- lifecycle-capability composition traces are fixture-backed,
- invariant bundles expose reusable theorem surfaces for policy composition.


### 6.3 M5 execution tracks (active)

1. **Service-graph modeling track** ✅ **completed baseline**
   - service identity/status/dependency/isolation model and deterministic state helpers are implemented,
   - orchestration and policy work consume this stable surface.
2. **Orchestration transition track** ✅ **completed baseline**
   - deterministic `serviceStart`, `serviceStop`, and `serviceRestart` transitions are implemented,
   - explicit `policyDenied`, `dependencyViolation`, and `illegalState` branches are executable,
   - staged success/failure ordering helper theorems are available for restart composition.
3. **Policy decomposition track** ✅ **completed baseline**
   - reusable policy predicates and authority surfaces are implemented in
     `SeLe4n/Kernel/Service/Invariant.lean`,
   - bridge lemmas connect policy assumptions to lifecycle/capability bundles,
   - policy denial branches are explicitly represented as check-only (non-mutation) outcomes.
4. **Proof-package track (WS-M5-D)** ✅ **completed baseline**
   - local preservation theorem entrypoints are available for `serviceStart`, `serviceStop`, and
     `serviceRestart`,
   - composed service+lifecycle+capability preservation is exposed via
     `serviceLifecycleCapabilityInvariantBundle`,
   - explicit failure-path preservation theorem coverage exists for start/stop/restart branches.
5. **Evidence/testing track (WS-M5-E)** ✅ **completed baseline**
   - executable trace coverage includes service restart success, policy denial, dependency failure,
     and explicit isolation-edge checks,
   - fixture anchors in `tests/fixtures/main_trace_smoke.expected` are updated with semantic intent
     rationale in `tests/scenarios/README.md`,
   - Tier 3 and Tier 4 candidate checks include M5 evidence-line anchors.
6. **Architecture-binding track (M6 preview)**
   - catalog architecture assumptions currently abstracted and define interface surfaces for future
     binding work.

### 6.4 Risks and mitigations for the M4-B → M5 handoff

1. **Risk: composition proofs become monolithic and brittle**
   - mitigation: require local-first preservation entrypoints before composed proof merges.
2. **Risk: executable traces lag theorem behavior**
   - mitigation: gate composed semantic changes with fixture updates in same PR range.
3. **Risk: roadmap claims outrun test coverage**
   - mitigation: require Tier 3 symbol anchors for each newly claimed bundle surface.

---

## 7. Change-control policy

When milestone scope or theorem/API surfaces change:

1. Update docs in the same commit range.
2. Keep stage markers synchronized across README, spec, development guide, and GitBook roadmap.
3. Record deferred work and destination milestone explicitly.
4. Do not claim slice completion without executable + theorem evidence.
5. Keep acceptance criteria actionable and command-verifiable.

---

## 8. PR evidence checklist

- [ ] New/updated transition definitions for claimed slice are present.
- [ ] Invariant components are named and integrated into bundle structure.
- [x] Preservation theorem entrypoints compile.
- [ ] `lake build` executed successfully.
- [ ] `lake exe sele4n` executed successfully.
- [ ] Hygiene scan (`axiom|sorry|TODO`) executed and clean.
- [ ] `./scripts/test_fast.sh` and `./scripts/test_smoke.sh` executed.
- [ ] Docs updated to match current and next slice.
- [ ] Remaining proof debt (if any) is explicitly stated.

---

## 9. Implementation surface inventory (for contributors)

The current milestone contract spans these concrete module families:

1. **Foundations**
   - `Prelude` (IDs + kernel monad),
   - `Machine` (machine-state helpers),
   - `Model/Object`, `Model/State` (typed object store and global system state).

2. **Scheduler contract**
   - scheduler transitions and M1 invariants/bundle surfaces.

3. **Capability contract**
   - CSpace lookup/insert/mint/delete/revoke,
   - attenuation + lifecycle authority component invariants,
   - capability bundle preservation entrypoints.

4. **IPC contract**
   - endpoint send/await-receive/receive transitions,
   - endpoint/IPC invariants,
   - M3.5 scheduler coherence predicates and bundle composition.

5. **Lifecycle contract (M4)**
   - lifecycle/retype transition operation(s),
   - lifecycle identity/aliasing + capability-reference invariant components,
   - local + composed lifecycle preservation entrypoints.

6. **Executable evidence contract**
   - `Main.lean` scenario path,
   - Tier 2 fixture-backed semantic fragment checks.

M4 work must extend this surface without regressing any closed milestone contract.

---

## 10. Documentation acceptance expectations

A PR claiming meaningful M4-B progress must include:

1. updates to normative docs (`README`, spec, development guide),
2. updates to GitBook roadmap and slice pages affected by semantic change,
3. explicit mention of whether fixture changes were required,
4. explicit mention of which invariant bundles were touched and why,
5. explicit statement of remaining proof debt, if any,
6. explicit note about post-slice path (what lands next and what remains deferred).
