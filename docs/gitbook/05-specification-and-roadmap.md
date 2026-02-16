# Specification and Roadmap

This chapter complements `docs/SEL4_SPEC.md` and provides the contributor-facing interpretation
of current/next milestones.

## Completed slice baseline: M4-A

M4-A focuses on introducing lifecycle/retype semantics with clear theorem and executable surfaces.
All six planned implementation steps are complete, so this chapter now acts as the baseline for
follow-on work.

### M4-A target outcomes (what must already be true)

1. lifecycle transition API with deterministic success/error branching,
2. identity/aliasing invariants for lifecycle transitions,
3. capability-object coherence invariants,
4. lifecycle preservation theorem entrypoints and composed bundle entrypoints,
5. executable trace evidence with fixture-backed semantic anchors.

### M4-A closeout outcomes

At this point, contributors should treat M4-A as the “stable foundation” layer:

- new work should build on lifecycle theorem surfaces instead of replacing them,
- failure branches should remain explicit and regression-testable,
- docs should reference M4-A as complete and avoid re-opening its non-goals.

## Current slice: M4-B

M4-B hardens lifecycle semantics through capability-lifecycle composition.

### M4-B target outcomes

1. lifecycle + revoke/delete interaction stories,
2. stale-reference exclusion invariants,
3. cross-bundle preservation theorems,
4. explicit failure-path theorem coverage,
5. expanded scenario/Tier 3 checks.

### M4-B implementation sequencing

1. define transition composition helpers,
2. encode stale-reference properties,
3. prove local then composed preservation,
4. extend executable stories,
5. lock fixture intent and update docs.

## Delivery model for upcoming slices

The project now follows a predictable slice template:

1. **Semantics first**: add deterministic transition behavior.
2. **Invariants second**: codify named safety components.
3. **Proofs third**: prove local, then composed preservation.
4. **Executable evidence fourth**: extend `Main.lean` and fixtures.
5. **Docs and roadmap finalization**: update spec + development guide + GitBook.

This keeps the codebase reviewable while preserving clear milestone boundaries.

## Next-slice direction (M5 preview)

After M4-A/M4-B, likely focus areas include:

- service-graph and restart-oriented semantics,
- policy and authority decomposition hardening,
- architecture binding strategy with explicit assumptions,
- and pre-deployment constraints for hardware execution paths.

See also:

- [Completed Slice: M4-A](08-current-slice-m4a.md)
- [Current Slice: M4-B](09-next-slice-m4b.md)
- [Future Slices and Delivery Plan](13-future-slices-and-delivery-plan.md)


## Detailed M4-B outcome framing

To keep reviews crisp, each M4-B target should be tied to concrete evidence:

1. **Transition composition**
   - Evidence: deterministic lifecycle+capability transition(s) with explicit errors.
2. **Stale-reference exclusion**
   - Evidence: named invariants + helper lemmas showing exclusion properties.
3. **Cross-bundle preservation**
   - Evidence: local-first then composed theorem entrypoints in compile-checked modules.
4. **Failure-path completeness**
   - Evidence: theorem statements covering invalid authority/state/reference outcomes.
5. **Executable and testing growth**
   - Evidence: trace scenario + fixture anchor + Tier 3 symbol checks.

## Near-term roadmap checkpoints (M4-B)

Suggested checkpoint structure:

- **Checkpoint B1 (semantics ready)**: composed transition APIs merged and deterministic.
- **Checkpoint B2 (invariants ready)** ✅ completed: stale-reference components + local helpers merged.
- **Checkpoint B3 (proof-ready)**: local and composed preservation theorem surfaces merged.
- **Checkpoint B4 (evidence-ready)**: executable/fixture/Tier 3 updates merged.
- **Checkpoint B5 (closeout-ready)**: docs synchronized and M5 deferrals explicitly listed.

## M5 preview: what “ready to start” should mean

M5 should not start because of calendar pressure; it should start when:

1. M4-B composed behavior is regression-protected by tests and fixture anchors,
2. theorem surfaces are reusable without significant refactoring,
3. roadmap docs list concrete M5 assumptions and constraints.
