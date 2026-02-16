# Specification and Roadmap

This chapter translates the normative spec (`docs/SEL4_SPEC.md`) into contributor-oriented
planning and delivery guidance.

## 1. Baseline status

M4 foundation status for planning purposes:

- **M4-A complete**: lifecycle/retype semantics, lifecycle invariants, and baseline preservation.
- **M4-B complete**: lifecycle-capability composition hardening and stale-reference safety.

That means M5 planning should build on existing transition and theorem surfaces rather than
restructuring them.

## 2. M4 outcomes that are now assumed stable

Contributors should treat these as established contracts:

1. deterministic lifecycle transition/error behavior,
2. lifecycle identity/aliasing and capability-reference invariant components,
3. lifecycle + capability composed preservation entrypoints,
4. executable trace anchors for lifecycle and composition stories,
5. Tier 3 symbol checks for critical theorem/bundle surfaces.

## 3. Completed slice definition: M5

M5 scope is to model **service-level operational stories** on top of M4 semantics.

### M5 target outcomes

1. **Service-graph semantics**
   - model services, dependencies, and restart/isolation boundaries.
2. **Policy-oriented authority constraints**
   - represent policy checks as reusable theorem-facing predicates.
3. **Composed preservation over orchestration paths**
   - prove safety across start/stop/restart and dependency transitions.
4. **Failure-path completeness**
   - include denied-policy, missing-dependency, and stale-reference-style failures.
5. **Executable scenario coverage**
   - add `Main.lean` stories showing service lifecycle success and failure.

### Non-goals for M5 (to prevent scope drift)

- no architecture-specific memory-model lock-in,
- no full seL4 boot pipeline modeling,
- no replacement of M1-M4 theorem interfaces unless required for soundness.

## 4. M5 closeout summary (all workstreams complete)

### Workstream A — Service graph model and transition API

Deliver:

- service node/state representation,
- dependency edges and restart policy shape,
- deterministic transition helpers for activation/deactivation/restart.

Exit signal:

- transitions compile and return explicit `KernelError`-compatible failures.

### Workstream B — Policy surfaces and authority decomposition

Deliver:

- policy predicates that constrain capability actions in service context,
- theorem-friendly decomposition (small components, then bundle),
- bridge lemmas connecting policy predicates to existing capability invariants.

Exit signal:

- policy logic can be reused without importing unrelated service internals.

### Workstream C — Proof layering for service operations

Deliver:

- local preservation per service transition,
- composed preservation across service + lifecycle + capability bundles,
- failure-path preservation theorems.

Exit signal:

- proof naming and locality follow existing conventions; no `sorry`/`axiom` debt.

### Workstream D — Trace/test expansion

Deliver:

- executable service scenarios (good and bad paths),
- fixture anchors with semantic intent notes,
- Tier 3 symbol anchors for new theorem surfaces.

Exit signal:

- `test_smoke` + `test_full` remain green with stable, intentional fixture deltas.

### Workstream E — Documentation + milestone closeout ✅ **complete**

Deliver:

- synchronized updates across spec, README, GitBook,
- explicit M6 deferrals and assumptions,
- short risk log for unresolved architectural unknowns.

Exit signal:

- docs consistently describe active/next slice and accepted deferrals.

## 5. Evidence map (what reviewers should require)

For each M5 target outcome, require concrete evidence:

1. transition code + theorem entrypoint,
2. executable trace or symbol anchor,
3. test command output in PR notes,
4. explicit deferred items.

## 6. Suggested checkpoint cadence

- **M5-C1**: service graph definitions + initial transitions,
- **M5-C2**: policy predicate set + bridge lemmas,
- **M5-C3**: local preservation completion,
- **M5-C4**: composed/failure-path preservation,
- **M5-C5**: trace/fixture/Tier 3 completion,
- **M5-C6**: docs and closeout memo.

## 7. Delivery model (kept from prior slices)

1. semantics first,
2. invariants second,
3. proofs third,
4. executable evidence fourth,
5. docs and acceptance closeout final.

This sequencing minimizes churn and keeps proof updates aligned with behavior changes.

## 8. Cross-reference index

For current execution planning, use M6-focused roadmap chapters after this M5 closeout baseline.

- [M5 Closeout Snapshot](09-m5-closeout-snapshot.md)
- [Completed Slice: M4-B](16-completed-slice-m4b.md)
- [Future Slices and Delivery Plan](13-future-slices-and-delivery-plan.md)
- [M4-B Execution Playbook](14-m4b-execution-playbook.md)
- [M5 Development Blueprint](15-m5-development-blueprint.md)
- [Project Usage and Value](17-project-usage-value.md)
