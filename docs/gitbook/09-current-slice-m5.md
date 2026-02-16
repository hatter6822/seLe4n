# Current Slice: M5 Service-Graph and Policy Surfaces

## Objective

M5 builds service-level operational semantics on top of the stabilized M4 lifecycle-capability
foundation.

## Current status

- **Slice state:** active implementation (WS-M5-A, WS-M5-B, and WS-M5-C completed; WS-M5-D onward in progress).
- **Baseline assumption:** M4-B theorem and invariant surfaces are stable and should be consumed as
  dependency contracts.

## Target outcomes for this slice

1. service dependency graph representation and deterministic transition helpers,
2. policy-aware authority predicates connected to lifecycle/capability checks,
3. local and composed preservation theorems (including failure-path branches),
4. executable traces and fixture anchors for restart/stop-policy/isolation/dependency-failure stories,
5. Tier 3 symbol anchors for M5 theorem and invariant surfaces.

## Workstream map

### WS-M5-A — service graph model ✅ **completed**

Service identity, status, dependency, isolation, and deterministic state helpers are now implemented in the model layer.

### WS-M5-B — orchestration transitions ✅ **completed**

Deterministic `serviceStart`, `serviceStop`, and `serviceRestart` transitions are implemented with
explicit `policyDenied`, `dependencyViolation`, and `illegalState` failure branches.

### WS-M5-C — policy and authority layer ✅ **completed**

Reusable policy predicates and bridge lemmas are implemented in `SeLe4n/Kernel/Service/Invariant.lean`
without coupling policy logic to service-state mutation helpers.

### WS-M5-D — proof completion

Land local preservation first, then composed preservation across service + lifecycle + capability
bundles.

### WS-M5-E — evidence and testing

Expose scenarios in `Main.lean`, refresh fixtures intentionally, and extend Tier 3/Tier 4 coverage.

### WS-M5-F — documentation and closeout

Keep README/spec/GitBook synchronized in the same PR sequence as semantics/proofs/tests.

## Entry and guardrails

Before landing M5 PRs, verify:

1. changes map to one or more M5 workstreams,
2. new invariants are narrow and named,
3. failure paths are explicit in semantics and theorem statements,
4. trace/fixture deltas explain semantic intent,
5. docs state what M5 target outcome advanced.

## Related chapters

- historical context: [Completed Slice: M4-A](08-completed-slice-m4a.md)
- immediate predecessor contracts: [Completed Slice: M4-B](16-completed-slice-m4b.md)
- normative scope and acceptance criteria: [`docs/SEL4_SPEC.md`](../SEL4_SPEC.md)
- broader roadmap: [Future Slices and Delivery Plan](13-future-slices-and-delivery-plan.md)


## M5 execution dashboard (optimized handoff)

Use this compact checklist at the top of every M5 PR:

- **Model surface (WS-M5-A/B):** service graph state + deterministic transition branch shape.
- **Policy surface (WS-M5-C):** policy predicates are explicit, named, and separable from mutation.
- **Proof surface (WS-M5-D):** local + composed preservation theorem entrypoints include failure paths.
- **Evidence surface (WS-M5-E):** `Main.lean` traces and `tests/fixtures/main_trace_smoke.expected` anchors updated intentionally.
- **Validation surface:** Tier 0/1/2 required gates pass; Tier 3 anchor additions reflect every new theorem/invariant claim.

## M5 exit-readiness signals

M5 should be marked complete only when all are true:

1. service orchestration transitions are deterministic and expose denial/error branches,
2. policy predicates bridge cleanly to lifecycle/capability invariants,
3. local and composed theorem surfaces are machine-checked and discoverable,
4. fixture-backed traces cover success and failure operational stories,
5. Tier 3 includes all M5 symbol anchors and docs state M6 deferrals explicitly.
