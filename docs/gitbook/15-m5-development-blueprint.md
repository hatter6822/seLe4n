# M5 Development Blueprint

This chapter is the execution-ready blueprint for starting M5.

## 1. Scope and objective

M5 introduces service-level operational semantics on top of stabilized M4 lifecycle-capability
contracts.

### M5 objective

Model deterministic service orchestration flows (start/stop/restart/isolation), constrain them with
policy predicates, and prove preservation across service + lifecycle + capability bundles (including
failure paths).

### Out of scope for M5

- architecture-binding implementation details,
- allocator-policy redesign,
- platform-specific MMU/ASID modeling.

## 2. Development entry checklist (required before coding)

1. confirm acceptance criteria in [`docs/SEL4_SPEC.md`](../SEL4_SPEC.md),
2. map planned changes to one or more M5 workstreams,
3. define theorem names and invariant component names up front,
4. define expected trace outputs before modifying fixtures,
5. identify exact files/modules touched and expected review owners.

## 3. Workstreams, deliverables, and file touch map

### WS-M5-A — Service graph model ✅ **completed**

**Deliverables**
- service identity/status/dependency types,
- helper queries for dependency and isolation checks,
- deterministic state-update helpers.

**Completion status**
- implemented in `SeLe4n/Model/Object.lean` and `SeLe4n/Model/State.lean`,
- deterministic service graph read/write helper theorems are machine-checked,
- remaining M5 workstreams now build on this stabilized state-model surface.

**Expected file touch areas**
- `SeLe4n/Model/Object.lean`
- `SeLe4n/Model/State.lean`
- `SeLe4n/Kernel/Lifecycle/*` (only if bridge helpers are required)

### WS-M5-B — Orchestration transitions ✅ **completed**

**Deliverables**
- start/stop/restart transition helpers,
- explicit failure outcomes (policy denial, dependency violation, invalid state),
- deterministic transition-order assumptions.

**Completion status**
- implemented in `SeLe4n/Kernel/Service/Operations.lean` as `serviceStart`, `serviceStop`, and `serviceRestart`,
- explicit `policyDenied` and `dependencyViolation` outcomes are now modeled in `KernelError`,
- staged-order theorem coverage now includes both success and error composition helpers for restart.

**Expected file touch areas**
- `SeLe4n/Kernel/*/Operations.lean` (new service module or existing integration layer)
- `SeLe4n/Kernel/API.lean`

### WS-M5-C — Policy surfaces

**Deliverables**
- reusable policy predicates,
- bridge lemmas connecting policy to lifecycle/capability assumptions,
- explicit separation between policy checks and state mutation.

**Expected file touch areas**
- `SeLe4n/Kernel/*/Invariant.lean`
- `SeLe4n/Kernel/Capability/Invariant.lean`
- `SeLe4n/Kernel/Lifecycle/Invariant.lean`

### WS-M5-D — Proof package

**Deliverables**
- local preservation theorem entrypoint per transition,
- composed preservation theorem(s) over service + lifecycle + capability bundles,
- failure-path preservation theorem coverage.

**Expected file touch areas**
- `SeLe4n/Kernel/*/Invariant.lean`
- `docs/gitbook/12-proof-and-invariant-map.md`

### WS-M5-E — Evidence and validation

**Deliverables**
- executable scenarios in `Main.lean`,
- fixture updates with semantic intent notes,
- Tier 3 symbol checks for theorem/bundle surface additions.

**Expected file touch areas**
- `Main.lean`
- `tests/fixtures/*`
- `scripts/test_tier3_invariant_surface.sh`

### WS-M5-F — Documentation closeout

**Deliverables**
- synchronized updates across spec/README/GitBook,
- explicit M5 achieved outcomes + M6 deferrals,
- updated cross-linking for current vs historical slice docs.

## 4. Recommended implementation sequence (PR-ready)

1. **PR1 (WS-A):** service graph types + read-only helpers.
2. **PR2 (WS-B):** first deterministic transition (`serviceStart`) with explicit error branches.
3. **PR3 (WS-C):** policy predicate bundle + bridge lemmas.
4. **PR4 (WS-D):** local preservation theorem(s) for PR2 transitions.
5. **PR5 (WS-D):** first composed service+lifecycle+capability preservation theorem.
6. **PR6 (WS-E):** executable scenario + fixture anchor + Tier 3 surface additions.
7. **PR7 (WS-F):** docs/spec closeout + deferral statement.

## 5. Definition of done (slice exit criteria)

M5 is complete only when all are true:

1. declared transitions compile and are deterministic over success/failure branches,
2. theorem surfaces include both local and composed preservation,
3. failure paths are explicit in semantics, theorem statements, and traces,
4. Tier 3 checks include all newly claimed theorem/bundle symbols,
5. docs include achieved outcomes, residual risks, and M6 deferrals.

## 6. PR checklist template for M5 contributors

Copy this into M5 PR descriptions:

- workstream(s) advanced: `WS-M5-*`
- target outcome(s) advanced:
- theorem/invariant names introduced or updated:
- fixture or trace changes and semantic intent:
- commands executed and results:
- explicit deferrals (if any):
- next PR unlocked:

## 7. Cross-references

- Current-slice status: [Current Slice: M5](09-current-slice-m5.md)
- Historical predecessor: [Completed Slice: M4-B](16-completed-slice-m4b.md)
- Development workflow standards: [Development Workflow](06-development-workflow.md)
- Testing contract: [Testing & CI](07-testing-and-ci.md)


## 8. Fast-start command bundle (recommended per PR)

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_tier3_invariant_surface.sh
./scripts/audit_testing_framework.sh
```

Use this sequence whenever an M5 PR adds or changes theorem/invariant claims so exit-readiness
signals remain continuously provable.

## 9. Coverage obligations matrix for M5

Treat “full coverage” in this project as obligation coverage across these layers:

1. **Build/proof closure:** `lake build` through Tier 1.
2. **Executable semantic closure:** Tier 2 fixture anchors covering M5 stories.
3. **Surface-anchor closure:** Tier 3 symbol checks for every new theorem/bundle/predicate claim.
4. **Nightly confidence closure:** Tier 4 candidate replay/determinism checks during audits.
5. **Negative-control closure:** audit script verifies Tier 2 fails on impossible expectations.

A milestone claim is incomplete if any one obligation is missing, even if other layers pass.
