# Current Slice: M4-B Lifecycle-Capability Hardening

## Objective

Move from foundational lifecycle semantics to stronger composition with capability deletion/revocation
and stale-reference safety.

## Why M4-B matters

M4-A made lifecycle transitions explicit and provable. M4-B ensures those transitions remain safe
when they interact with authority-changing capability operations in realistic workflows.

## Detailed target outcomes

1. lifecycle + capability lifecycle interaction semantics,
2. stale-reference exclusion invariants,
3. cross-bundle preservation theorems,
4. failure-path theorem coverage,
5. expanded executable/test anchors.

## Proposed execution plan

### Phase 1: semantic composition ✅ completed

- codified a deterministic transition story spanning lifecycle and revoke/delete behavior,
- made ordering assumptions explicit in transition API and theorem statements.

### Phase 2: invariant hardening ✅ completed

- define stale-reference exclusion invariants,
- tie those invariants to existing identity/aliasing and authority components.

### Phase 3: theorem expansion ✅ completed

- prove local preservation for new composition helpers,
- prove composed preservation across lifecycle + capability bundles.

### Phase 4: executable + testing growth

- add M4-B success/failure traces in `Main.lean`,
- extend Tier 3 anchors to include M4-B theorem surfaces,
- keep fixture updates minimal and intentional.

### Phase 5: documentation closeout

- update spec/development guide/GitBook pages,
- publish explicit note on what is deferred to M5.

## Exit signals for M4-B

- required gates remain green,
- lifecycle-capability composition theorem surfaces compile,
- fixture updates are intentional and explained,
- docs include post-M4 direction and M5 preparation notes.

## M4-B success outcomes for the broader roadmap

When M4-B exits successfully, the project should be ready to:

1. model service restart/isolation workflows with stronger safety assumptions,
2. introduce policy-facing authority constraints with less theorem churn,
3. move architecture-binding work into explicit interfaces rather than hidden assumptions.


## Detailed deliverable map

### D1. Composition transition API surface

Expected characteristics:

- explicit authority/state/reference validation order,
- deterministic result shape for success and each failure case,
- helper theorems that make result-case proof scripts concise.

### D2. Stale-reference exclusion invariant family

Expected characteristics:

- narrow invariant components instead of one mega definition,
- explicit dependency links to lifecycle identity/aliasing and capability authority invariants,
- theorem assumptions phrased for reuse in M5 policy layering.

### D3. Proof surface completion

Expected characteristics:

- local preservation theorem per transition,
- composed preservation theorem(s) over lifecycle + capability bundles,
- explicit failure-path preservation statements.

### D4. Evidence and regression guardrails

Expected characteristics:

- executable scenarios for composed success/failure behavior,
- fixture anchors for stable semantic fragments,
- Tier 3 symbol anchors for new M4-B theorem surfaces.

## Dependencies and critical path

1. D1 must land before D3 can stabilize.
2. D2 should land before final composed theorem statements are frozen.
3. D4 should land after D1/D3 behavior settles to minimize fixture churn.

## Exit review questions

Maintainers should be able to answer “yes” to all:

1. Are stale references excluded after lifecycle+capability composition transitions?
2. Are failure paths as rigorously preserved as success paths?
3. Does executable evidence clearly represent composed behavior?
4. Are M4-B claims continuously protected by Tier 3 anchors?
