# Future Slices and Delivery Plan

This chapter describes the forward path beyond M4 closeout and provides execution structure to keep
implementation, proofs, tests, and docs aligned.

## 1. Planning principles

1. keep each slice reviewable in one coherent thread,
2. preserve theorem layering (local first, composed second),
3. treat executable traces as contract evidence,
4. ship docs and deferrals with each milestone change,
5. preserve deterministic semantics before broadening scope.

## 2. Immediate next slice (M5)

M5 theme: **service-oriented semantics built on M4 lifecycle-capability hardening**.

### M5 target outcomes

1. service dependency graph representation and transition semantics,
2. policy-aware authority constraints integrated with capability surfaces,
3. preservation theorems for restart/isolation and failure paths,
4. executable scenario evidence for orchestration behaviors,
5. Tier 3 anchors for M5 theorem/bundle surfaces.

### M5 implementation workstreams

#### WS-M5-A — Service graph model

- define service identity, status, and dependency structure,
- model restart intent and isolation boundaries,
- expose deterministic helper transitions.

#### WS-M5-B — Orchestration transitions ✅ **completed**

- implement deterministic start/stop/restart transitions,
- expose policy-denial/dependency-violation/invalid-state branches explicitly,
- codify staged restart ordering in theorem surface.

#### WS-M5-C — Policy and authority layer ✅ **completed**

- reusable policy predicates are encoded over service/lifecycle/capability surfaces,
- bridge policy checks are connected to existing invariant bundles,
- policy predicates remain separated from service-state mutation scripts.

#### WS-M5-D — Proof completion

- local preservation for each service transition,
- composed preservation across service + lifecycle + capability bundles,
- failure-path theorem completion.

#### WS-M5-E — Evidence and testing

- add scenario traces for restart and dependency failures,
- add/adjust fixtures with rationale notes,
- add Tier 3 anchors and nightly candidates.

#### WS-M5-F — Documentation and closeout

- align spec/README/GitBook with shipped behavior,
- record M6 assumptions and deferred items,
- publish slice closeout summary and risk notes.

## 3. Mid-term slice preview (M6)

M6 theme: **architecture binding interface preparation**.

Indicative outcomes:

1. explicit architecture assumptions represented as stable interfaces,
2. proof-carrying adapters from architecture-neutral semantics,
3. platform contract checklist for boot/runtime boundary expectations.

## 4. Long-horizon trajectory (mobile-first relevance)

1. architecture-neutral semantic hardening (M1-M5),
2. architecture-binding interface stabilization (M6+),
3. subsystem trust-boundary mapping,
4. prototype integration with traceability back to theorem claims,
5. hardware-oriented validation strategy alignment.

See [Path to Real Hardware (Mobile-First)](10-path-to-real-hardware-mobile-first.md).

## 5. Transition gates

### Gate: M4 → M5

Require all:

1. M4-B semantics/theorems merged and fixture-backed,
2. stale-reference and failure-path coverage in place,
3. Tier 3 anchors cover M4-B claims,
4. docs explicitly describe M5 assumptions.

### Gate: M5 → M6

Require all:

1. service graph semantics cover realistic restart/isolation stories,
2. policy surfaces prove reusable across multiple service scenarios,
3. architecture-binding assumptions are explicit and reviewable.

## 6. Risk register (active)

1. **Semantic/proof skew**
   - risk: transitions evolve without theorem updates.
   - mitigation: enforce transition + theorem pairing in PR checklist.
2. **Trace/fixture fragility**
   - risk: fixtures reflect formatting noise instead of semantics.
   - mitigation: document semantic intent per fixture delta.
3. **Roadmap drift**
   - risk: docs describe different active slices.
   - mitigation: synchronize README/spec/GitBook in same PR.
4. **Policy overcoupling**
   - risk: policy model entangles service internals and capability internals.
   - mitigation: require bridge lemmas and module boundary review.

## 7. Contributor operating cadence

1. **Per PR**: state current-slice outcome moved + next-slice unlock.
2. **Per checkpoint**: map progress to M5 workstreams A-F.
3. **Per milestone closeout**: publish delivered outcomes, deferrals, and risk notes.
