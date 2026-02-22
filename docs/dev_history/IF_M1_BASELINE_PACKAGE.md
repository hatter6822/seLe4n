# IF-M1 Baseline Package (WS-B7)

This document records the WS-B7 deliverable package for the
**Information-flow proof track start**.

## 1) Scope delivered in IF-M1

WS-B7 delivers the formal baseline only:

1. policy lattice primitives for confidentiality/integrity,
2. security-label flow relation and algebraic lemmas,
3. state projection helpers and low-equivalence scaffolding,
4. explicit theorem-target backlog and assumptions ledger.

No IF-M2+ relational transition proofs are claimed in this package.

## 2) Implemented theorem entrypoints

Code entrypoints:

- `SeLe4n/Kernel/InformationFlow/Policy.lean`
  - `confidentialityFlowsTo`
  - `integrityFlowsTo`
  - `securityFlowsTo`
  - `securityFlowsTo_refl`
  - `securityFlowsTo_trans`
- `SeLe4n/Kernel/InformationFlow/Projection.lean`
  - `projectState`
  - `lowEquivalent`
  - `lowEquivalent_refl`
  - `lowEquivalent_symm`
  - `lowEquivalent_trans`

These are the canonical IF-M1 theorem and definition anchors.

## 3) IF-M1 theorem targets (completed)

1. **Label relation reflexivity/transitivity**
   - complete for confidentiality, integrity, and combined security flow relation.
2. **Deterministic observer projection API**
   - complete via `projectState` and deterministic equality statement.
3. **Low-equivalence relation shape**
   - complete as an equivalence-style scaffold (`refl/symm/trans`) over projected states.

## 4) Assumptions ledger

The IF-M1 baseline intentionally carries the following assumptions for future milestones:

1. **Trusted labeling context assumption**
   - `LabelingContext` functions (`objectLabelOf`, `threadLabelOf`, `endpointLabelOf`) are
     externally supplied and treated as trusted policy inputs.
2. **Observer model simplification**
   - observer projections currently include object visibility and scheduler-visible thread identities,
     plus service status summaries.
3. **No microarchitectural channel modeling**
   - cache/timing/speculative channels remain out of scope.
4. **No transition-level noninterference theorem claims yet**
   - IF-M3 is where operation-level two-run theorems begin.

## 5) Decomposition plan into IF-M2 and IF-M3

1. **IF-M2 step:** instantiate relational projection lemmas per subsystem state carrier
   (objects, scheduler queues, endpoints/notifications, capability metadata).
2. **IF-M3 step:** prove seed noninterference for selected operations
   (scheduler choose/yield, endpoint send/receive/wait, one capability mutation path).
3. **Composition note:** retain local-first theorem naming and avoid global monolithic
   statements until IF-M4 composition stage.

## 6) Validation commands used for WS-B7 closeout

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
lake build
```
