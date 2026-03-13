# seLe4n Workstream Plan — Register-Indexed Authoritative Namespaces (WS-J1)

**Version target:** v0.15.4+
**Status:** Planned
**Priority:** High
**Estimated effort:** 3–5 days
**Dependencies:** WS-I1..WS-I5 complete baseline, no additional blockers
**Primary scope:** Replace the current `RegName := Nat` / `RegValue := Nat` modeling path for namespace references with a typed, authoritative register-namespace indexing model.

---

## 1. Executive summary

`SeLe4n/Machine.lean` currently models register names/values with `abbrev Nat`.
That decision kept the abstract machine lightweight, but it limits the model’s
ability to express hardware-mediated authority transfer where register payloads
index kernel namespaces directly (e.g., CSpace roots, endpoint IDs, ASID roots,
or service handles).

This workstream introduces a **typed register namespace index layer** so register
values can carry and resolve **authoritative namespace references** with explicit
validation rules, deterministic error outcomes, and preservation proofs.

The migration is split into small, reviewable units to reduce proof breakage and
keep CI feedback fast.

---

## 2. Problem statement and design goal

### 2.1 Current limitation

WS-I5 Part A documented why `RegName` / `RegValue` were left as bare `Nat` in
the abstract machine model. That is acceptable for local read/write lemmas, but
it is too weak for upcoming hardware-binding and syscall-gate realism:

1. Register payloads that represent authority remain untyped until deep in API
   wrappers.
2. Namespace confusion (wrong identifier class in a register channel) is
   prevented by conventions rather than type-level structure.
3. Proof obligations about authority resolution are duplicated across subsystem
   wrappers instead of concentrated in one decode/resolve layer.

### 2.2 Target capability

Add a register-namespace mechanism where:

- Register values can be decoded as **typed namespace indices**.
- Resolution against authoritative maps is total and deterministic (`ok/error`).
- Authority-bearing operations consume resolved typed references, not raw `Nat`.
- Existing abstract-machine lemmas remain available via compatibility shims.

---

## 3. Scope and non-goals

### In scope

- New typed structures and decoding APIs for register namespace references.
- Authoritative namespace registries in kernel state (minimal initial set).
- API/adapter integration for capability-gated operations that consume register
  references.
- Invariant and non-interference updates for the new resolution path.
- Tiered tests and trace fixtures for successful and failing decode/resolve paths.
- Documentation and GitBook synchronization.

### Out of scope (this workstream)

- Full hardware MMU/register-file implementation for Raspberry Pi 5.
- ISA-level binary encoding fidelity for all ARM64 registers.
- Multi-core register-bank semantics.

---

## 4. Architecture proposal

### 4.1 New core types

Introduce (names indicative; final names should remain semantics-first):

- `RegRefKind` — namespace discriminator (e.g., cspace, endpoint, notification,
  asidRoot, service).
- `RegNamespaceIndex` — typed payload containing kind + bounded index token.
- `RegPayload` — register value algebra (`word`, `namespaceRef`, future variants).
- `RegisterFile` update path preserving deterministic semantics.

### 4.2 Authoritative namespace layer

Add a state-owned registry for resolvable namespace references, e.g.:

- `NamespaceRegistry` in `Model.State` (or subsystem-owned projections),
- total resolver: `resolveRegNamespace : KernelState → RegNamespaceIndex → Except KernelError ResolvedRef`.

### 4.3 Determinism and safety contract

Every decode/resolve function must:

- return explicit errors on malformed/unknown/stale references,
- preserve no-`sorry` / no-`axiom` policy,
- avoid partial functions and non-deterministic branches.

---

## 5. Work breakdown structure (small execution units)

## WS-J1-A — Type introduction and compatibility bridge

**Goal:** Add new types without changing behavior of existing call paths.

Tasks:
1. Add `RegRefKind`, `RegNamespaceIndex`, and `RegPayload` in machine/model layer.
2. Keep `readReg`/`writeReg` behavior stable via compatibility conversion APIs.
3. Prove bridge lemmas showing legacy `Nat` paths remain observationally equivalent for plain word registers.

Exit criteria:
- `lake build` passes.
- Existing smoke suite unchanged.

---

## WS-J1-B — Authoritative namespace registry foundations

**Goal:** Introduce canonical namespace ownership and resolver.

Tasks:
1. Add `NamespaceRegistry` structure and initialization defaults.
2. Implement total resolver with explicit `KernelError` mapping.
3. Add preservation lemmas for unaffected subsystems.

Exit criteria:
- Resolver round-trip/uniqueness lemmas proved.
- Negative tests for unknown index and kind mismatch.

---

## WS-J1-C — API and transition-path adoption

**Goal:** Move authority-bearing transitions from raw register `Nat` decode to typed resolution.

Tasks:
1. Update syscall boundary wrappers that pull IDs from registers.
2. Route capability and IPC entry points through typed resolver.
3. Preserve determinism and capability checks in the same transition step.

Exit criteria:
- Existing API soundness theorems re-proved.
- Trace harness includes successful + denied resolution scenarios.

---

## WS-J1-D — Invariant and information-flow integration

**Goal:** Make namespace indexing first-class in proof surfaces.

Tasks:
1. Add/extend invariants for namespace registry well-formedness.
2. Extend NI bridge lemmas for resolver-observable behavior.
3. Add composition coverage for new step variants.

Exit criteria:
- `test_full.sh` passes.
- NI theorem surface remains sorry-free.

---

## WS-J1-E — Evidence, migration cleanup, and docs sync

**Goal:** Finalize migration and documentation coherence.

Tasks:
1. Remove temporary compatibility shims that are no longer needed.
2. Update fixtures (if trace output changes) with rationale.
3. Synchronize canonical docs + GitBook mirror + claim/evidence links.

Exit criteria:
- `test_smoke.sh` (minimum) and `test_full.sh` pass.
- Documentation index references WS-J1 and its evidence.

---

## 6. File impact map (expected)

### Core model and machine
- `SeLe4n/Machine.lean`
- `SeLe4n/Model/State.lean`
- `SeLe4n/Prelude.lean` (if additional typed wrappers are needed)

### Kernel transition surfaces (expected first adopters)
- `SeLe4n/Kernel/API.lean`
- `SeLe4n/Kernel/Capability/*`
- `SeLe4n/Kernel/IPC/*`
- `SeLe4n/Kernel/Architecture/*` (if ASID/VSpace references are register-fed)

### Proof/test surfaces
- `SeLe4n/Kernel/*/Invariant*.lean`
- `SeLe4n/Kernel/InformationFlow/*`
- `SeLe4n/Testing/MainTraceHarness.lean`
- `tests/OperationChainSuite.lean`
- `tests/NegativeStateSuite.lean`

### Documentation surfaces
- `README.md`
- `docs/DEVELOPMENT.md`
- `docs/spec/SELE4N_SPEC.md`
- `docs/WORKSTREAM_HISTORY.md`
- `docs/CLAIM_EVIDENCE_INDEX.md`
- `docs/gitbook/*` roadmap pages

---

## 7. Risk register and mitigations

1. **Proof churn in large invariant files** (High)
   - Mitigation: adopt WS-J1-A/B first with compatibility bridge; only then migrate call paths.
2. **Namespace/model over-coupling** (Medium)
   - Mitigation: keep resolver interface minimal and subsystem-neutral.
3. **Trace fixture instability** (Medium)
   - Mitigation: stage fixture updates in WS-J1-E with diff rationale.
4. **Performance regressions in hot paths** (Low/Medium)
   - Mitigation: use O(1) map lookup structures and avoid repeated decode passes.

---

## 8. Validation plan

Minimum gate per slice:

```bash
./scripts/test_smoke.sh
```

Required for theorem/invariant slices:

```bash
./scripts/test_full.sh
```

Nightly confidence (optional when touching NI composition broadly):

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

Additionally for this workstream:
- Resolver property tests (success/failure determinism).
- Cross-subsystem negative tests for namespace mismatch.
- Trace scenario IDs for decode/resolve failures.

---

## 9. Completion evidence checklist

- [ ] Typed register-namespace model merged with no `sorry`/`axiom`.
- [ ] All authority-bearing register decode sites migrated.
- [ ] Invariant and NI surfaces updated and passing.
- [ ] Fixture updates (if any) justified and reviewed.
- [ ] Canonical docs and GitBook mirrors synchronized.

---

## 10. Relationship to WS-I5 Part A

WS-I5 Part A intentionally documented the prior `abbrev Nat` choice as a
low-risk simplification. WS-J1 supersedes that simplification for authority
resolution paths by introducing typed, authoritative register namespace
indexing while preserving deterministic semantics and proof ergonomics.

Both statements remain consistent:
- WS-I5 Part A explains why the old model was reasonable at that stage.
- WS-J1 defines the migration path now that deeper hardware-binding realism and
  namespace authority modeling are priority.
