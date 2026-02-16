# seLe4n Specification and Milestone Plan

## 1. Purpose

This document is the normative specification baseline for seLe4n.

It defines:

1. What milestone behavior is already closed and considered stable.
2. The **current delivery slice** (M4-A) with concrete target outcomes.
3. The **next delivery slice** (M4-B) so work continues without roadmap drift.
4. Acceptance criteria and non-goals for focused, reviewable implementation.
5. Change-control expectations for code, proofs, executable traces, and docs.

Current stage: **active M4-A lifecycle/retype foundations (steps 1-6 complete)**.

---

## 2. Milestone map

- **Bootstrap (complete)**: executable model skeleton and transition style.
- **M1 (complete)**: scheduler integrity bundle and preservation.
- **M2 (complete)**: typed CSpace operations + capability lifecycle authority invariants.
- **M3 (complete)**: endpoint send/receive seed semantics + IPC invariant seed bundle.
- **M3.5 (complete)**: waiting/handshake IPC semantics + scheduler coherence contract.
- **M4-A (current slice)**: lifecycle/retype transition foundations + initial lifecycle invariants.
- **M4-B (next slice)**: lifecycle-capability composition hardening and richer scenario coverage.

---

## 3. Stable baseline contracts (must not regress)

The following contracts are considered stable and preserved while M4 evolves:

1. M1 scheduler invariant bundle and entrypoint preservation theorems.
2. M2 capability/CSpace transition APIs (`lookup`, `insert`, `mint`, `delete`, `revoke`) and
   composed capability invariant bundle.
3. M3 endpoint APIs (`endpointSend`, `endpointReceive`) and IPC seed invariant layering.
4. M3.5 waiting-receiver handshake behavior and scheduler-contract predicate surfaces.
5. Tier 0/1/2 required test gates and CI invocation through repository scripts.

Any intentional baseline changes must be documented in this file, `docs/DEVELOPMENT.md`, and
`README.md` in the same commit range.

---

## 4. Current slice: M4-A lifecycle/retype foundations

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
   - ensure deterministic state updates and architecture-neutral semantics.

2. **Object identity + aliasing invariants**
   - define invariants preventing invalid object identity reuse in active scope,
   - define invariants constraining aliasing after lifecycle transitions.

3. **Capability-object coherence invariants**
   - specify that capability references remain type-compatible and target-valid after lifecycle
     updates,
   - ensure lifecycle updates preserve authority monotonicity assumptions already used by M2.

4. **Local helper lemmas + preservation theorem entrypoints**
   - provide transition-local lookup/membership helper lemmas near lifecycle transitions to keep
     proof scripts concise,
   - provide machine-checked `<transition>_preserves_<invariant>` entrypoints for each new
     lifecycle transition,
   - include at least one composed theorem over lifecycle + existing capability invariant bundle.

5. **Executable + fixture evidence**
   - extend `Main.lean` with at least one lifecycle scenario,
   - update `tests/fixtures/main_trace_smoke.expected` with stable semantic fragments if behavior
     output changes intentionally.

### 4.4 M4-A acceptance criteria

1. `./scripts/test_fast.sh` succeeds.
2. `./scripts/test_smoke.sh` succeeds.
3. `lake build` succeeds.
4. `lake exe sele4n` succeeds and includes lifecycle behavior evidence.
5. Hygiene scan is clean:
   - `rg -n "axiom|sorry|TODO" SeLe4n Main.lean`.
6. Lifecycle invariants are named, documented, and composed with existing bundle structure.
7. Preservation theorem entrypoints compile without introducing proof placeholders.

### 4.5 Explicit non-goals (M4-A)

- Full allocator/heap policy modeling.
- Architecture-specific MMU/ASID internals.
- Full reply-cap protocol redesign.
- End-to-end C refinement correspondence.
- General policy engine redesign.

---

## 5. Next slice: M4-B lifecycle-capability composition hardening

### 5.1 Objective

Strengthen lifecycle semantics by integrating lifecycle updates with capability revocation/deletion
flows and proving stronger stale-reference exclusion properties.

### 5.2 M4-B target outcomes

1. **Lifecycle + revoke/delete composition**
   - define at least one composed transition story where lifecycle and capability lifecycle
     operations interact explicitly.

2. **Stale reference exclusion invariants**
   - add invariants ruling out stale capability references to retired/retyped object identities.

3. **Cross-bundle preservation theorem surface**
   - prove composed preservation covering lifecycle invariants plus capability lifecycle authority
     invariants.

4. **Error-path completeness**
   - include explicit failure-path theorems (invalid type, stale object reference, illegal
     authority).

5. **Scenario + testing growth**
   - expand executable scenarios to include success and failure lifecycle stories,
   - extend Tier 3 checks with M4-specific theorem/bundle anchors.

### 5.3 Provisional M4-B acceptance baseline

1. Existing required gates remain green (`test_fast`, `test_smoke`).
2. M4-A lifecycle contracts remain intact while M4-B features land.
3. Tier 2 fixture remains stable and intentional.
4. Tier 3 includes lifecycle-capability composition anchors.
5. Documentation clearly updates post-M4 roadmap direction (M5 preview).

---

## 6. Change-control policy

When milestone scope or theorem/API surfaces change:

1. Update docs in the same commit range.
2. Keep stage markers synchronized across README, spec, and development guide.
3. Record deferred work and destination milestone explicitly.
4. Do not claim slice completion without executable + theorem evidence.
5. Keep acceptance criteria actionable and command-verifiable.

---

## 7. PR evidence checklist

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

## 8. Implementation surface inventory (for contributors)

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

5. **Executable evidence contract**
   - `Main.lean` scenario path,
   - Tier 2 fixture-backed semantic fragment checks.

M4 work must extend this surface without regressing any closed milestone contract.

---

## 9. M4 documentation acceptance expectations

A PR claiming meaningful M4 progress must include:

1. updates to normative docs (`README`, spec, development guide),
2. updates to GitBook deep-dive pages affected by the semantic change,
3. explicit mention of whether fixture changes were required,
4. explicit mention of which invariant bundles were touched and why,
5. explicit statement of remaining proof debt, if any.
