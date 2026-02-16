# Current Slice: M5 Service-Graph and Policy Surfaces

## Objective

M5 builds service-level operational semantics on top of the stabilized M4 lifecycle-capability
foundation.

## Current status

- **Slice state:** active planning + incremental implementation.
- **Baseline assumption:** M4-B theorem and invariant surfaces are stable and should be consumed as
  dependency contracts.

## Target outcomes for this slice

1. service dependency graph representation and deterministic transition helpers,
2. policy-aware authority predicates connected to lifecycle/capability checks,
3. local and composed preservation theorems (including failure-path branches),
4. executable traces and fixture anchors for restart/isolation/dependency-failure stories,
5. Tier 3 symbol anchors for M5 theorem and invariant surfaces.

## Workstream map

### WS-M5-A — service graph model

Define service identity, status, dependencies, and deterministic lifecycle helpers.

### WS-M5-B — policy and authority layer

Introduce narrow policy predicates and explicit denial behavior without coupling policy to single
service stories.

### WS-M5-C — proof completion

Land local preservation first, then composed preservation across service + lifecycle + capability
bundles.

### WS-M5-D — evidence and testing

Expose scenarios in `Main.lean`, refresh fixtures intentionally, and extend Tier 3/Tier 4 coverage.

### WS-M5-E — documentation and closeout

Keep README/spec/GitBook synchronized in the same PR sequence as semantics/proofs/tests.

## Entry and guardrails

Before landing M5 PRs, verify:

1. changes map to one or more M5 workstreams,
2. new invariants are narrow and named,
3. failure paths are explicit in semantics and theorem statements,
4. trace/fixture deltas explain semantic intent,
5. docs state what M5 target outcome advanced.

## Related chapters

- historical context: [Completed Slice: M4-A](08-current-slice-m4a.md)
- immediate predecessor contracts: [Completed Slice: M4-B](16-completed-slice-m4b.md)
- normative scope and acceptance criteria: [`docs/SEL4_SPEC.md`](../SEL4_SPEC.md)
- broader roadmap: [Future Slices and Delivery Plan](13-future-slices-and-delivery-plan.md)
