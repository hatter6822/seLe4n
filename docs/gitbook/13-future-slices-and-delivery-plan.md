# Future Slices and Delivery Plan

This chapter describes where the project is heading beyond the immediate M4-A/M4-B pair and how to
get there without roadmap drift.

## Planning principles

1. keep slices narrow enough for one coherent review thread,
2. preserve theorem layering (local first, composed second),
3. treat executable traces as contract evidence, not demo-only output,
4. require docs to state both achieved outcomes and explicit deferrals.

## Near-term path (M4 completion)

### M4-A (complete foundation)

Delivered:

- lifecycle/retype transition baseline,
- identity/aliasing + capability-reference invariant seeds,
- local/composed preservation entrypoints,
- executable lifecycle traces.

### M4-B (active next target)

To deliver:

- lifecycle + revoke/delete composed semantics,
- stale-reference exclusion properties,
- cross-bundle preservation and failure-path theorem coverage,
- expanded Tier 3 and scenario anchors.

## Mid-term path (M5 preview)

M5 is expected to focus on service-graph semantics and policy-friendly authority constraints.
Indicative outcomes:

1. model service restart and isolation semantics using M4 composition surfaces,
2. refine authority decomposition for realistic multi-service topologies,
3. prepare architecture-binding interfaces as explicit assumptions.

## Long-term path (hardware relevance)

The hardware trajectory (mobile-first) stays staged:

1. semantic hardening in architecture-neutral model,
2. architecture binding interfaces,
3. boot/platform contract alignment,
4. subsystem decomposition and trust-boundary mapping,
5. prototype integration and traceability to system tests.

See [Path to Real Hardware (Mobile-First)](10-path-to-real-hardware-mobile-first.md) for details.

## How contributors should use this plan

When opening milestone-moving PRs, include a short note answering:

1. What slice outcome does this PR land now?
2. What next-slice outcome does it unlock?
3. What remains deferred and why?

That discipline keeps implementation, proofs, tests, and documentation aligned over time.



## Milestone transition criteria (quality gates)

### M4-B → M5 transition gate

Only transition once all are true:

1. M4-B composition semantics are merged and fixture-backed.
2. Stale-reference exclusion is theorem-backed with failure-path coverage.
3. Tier 3 anchors cover newly claimed M4-B theorem surfaces.
4. Docs explicitly list M5 assumptions and deferred risk items.

### M5 → hardware-alignment transition gate (preview)

Only transition once all are true:

1. service-graph semantics support realistic restart/isolation stories,
2. policy decomposition surfaces are stable enough for reuse,
3. architecture-binding assumptions are explicit and reviewable.

## Suggested planning cadence

1. **Per PR**: state current-slice movement + next-slice unlock.
2. **Per week**: publish checkpoint status against active slice outcomes.
3. **Per milestone**: publish closeout summary including deferred items and rationale.

## Roadmap risk register (lightweight)

1. **Semantic/proof skew risk**
   - symptom: theorem surfaces diverge from executable traces.
   - mitigation: require fixture evidence with semantic transitions.
2. **Documentation drift risk**
   - symptom: README/spec/gitbook describe different active slices.
   - mitigation: enforce same-PR status marker synchronization.
3. **Test blind-spot risk**
   - symptom: new theorem surfaces lack Tier 3 anchors.
   - mitigation: treat anchor addition as part of definition-of-done.
