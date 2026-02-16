# Future Slices and Delivery Plan

This chapter describes the forward path beyond M4 closeout and provides execution structure to keep
implementation, proofs, tests, and docs aligned.

## 1. Planning principles

1. keep each slice reviewable in one coherent thread,
2. preserve theorem layering (local first, composed second),
3. treat executable traces as contract evidence,
4. ship docs and deferrals with each milestone change,
5. preserve deterministic semantics before broadening scope.

## 2. Immediate next slice (M6)

M6 theme: **architecture-binding interfaces built on completed M5 service/policy semantics**.

### M6 target outcomes

1. explicit architecture assumptions represented as stable interface artifacts,
2. proof-carrying adapter surfaces from architecture-neutral semantics to architecture-bound contexts,
3. platform contract checklist coverage for boot/runtime boundary expectations,
4. preservation-proof hooks that keep M1–M5 theorem layering reusable during binding,
5. fixture/test-plan extensions that validate interface assumptions without weakening existing gates.

### M5 closeout baseline consumed by M6

#### WS-M5-A — Service graph model ✅ **completed**

- service identity, status, dependency, isolation, and deterministic state helpers are stable.

#### WS-M5-B — Orchestration transitions ✅ **completed**

- deterministic start/stop/restart transitions with explicit failure branches are stable.

#### WS-M5-C — Policy and authority layer ✅ **completed**

- reusable policy predicates and bridge lemmas to lifecycle/capability surfaces are stable.

#### WS-M5-D — Proof completion ✅ **completed**

- local and composed preservation theorem entrypoints (including failure-path coverage) are stable.

#### WS-M5-E — Evidence and testing ✅ **completed**

- executable traces, fixtures, and Tier 3/4 anchor coverage for M5 scenarios are stable.

#### WS-M5-F — Documentation and closeout ✅ **completed**

- spec/README/GitBook now consistently mark M5 complete and document M6 deferrals.

## 3. Mid-term slice preview (M7+)

Post-M6 themes are intentionally deferred until architecture-binding interfaces stabilize.

Indicative outcomes:

1. subsystem integration plans that consume M6 interface contracts,
2. refinement-oriented evidence packaging over architecture-bound assumptions,
3. platform-specific validation strategy increments gated by M6 artifacts.

## 4. Long-horizon trajectory (mobile-first relevance)

1. architecture-neutral semantic hardening (M1-M5),
2. architecture-binding interface stabilization (M6+),
3. subsystem trust-boundary mapping,
4. prototype integration with traceability back to theorem claims,
5. hardware-oriented validation strategy alignment.

See [Path to Real Hardware (Mobile-First)](10-path-to-real-hardware-mobile-first.md).

## 5. Transition gates

### Gate: M5 closeout (completed)

Verified signals:

1. service-graph semantics, policy surfaces, and proof package are merged and stable,
2. success/failure orchestration scenarios are fixture-backed,
3. Tier 3 anchors include claimed M5 theorem/invariant symbols,
4. docs explicitly mark M5 completion and M6 deferrals.

### Gate: M5 → M6 (active entry gate)

Require all:

1. architecture-binding assumptions are explicit and reviewable,
2. interface artifacts preserve M1–M5 theorem layering contracts,
3. new testing obligations are added without regressing Tier 0–3 required gates.

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
