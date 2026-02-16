# Specification and Roadmap

This chapter translates the normative spec (`docs/SEL4_SPEC.md`) into contributor-oriented
planning and delivery guidance.

## 1. Baseline status

Milestone status for planning purposes:

- M4-A complete,
- M4-B complete,
- M5 complete,
- **M6 active**.

M6 planning should build on existing transition and theorem surfaces rather than restructuring
closed milestone contracts.

## 2. Stable outcomes now treated as contracts

Contributors should treat these as stable unless a spec-level change is explicitly approved:

1. deterministic lifecycle/capability/service transition behavior,
2. layered invariant composition across scheduler/capability/IPC/lifecycle/service modules,
3. local + composed preservation entrypoints for established transitions,
4. fixture-backed executable traces for core success/failure stories,
5. Tier 3 theorem/invariant symbol anchors for claimed surfaces.

## 3. Current slice definition: M6

M6 scope: **architecture-binding interfaces and hardware-facing assumption hardening**.

### M6 target outcomes

1. **Assumption extraction and interface definition**
   - architecture-facing assumptions become explicit interfaces.
2. **Adapter semantics and bounded error surfaces**
   - adapter operations remain deterministic and failure-explicit.
3. **Composed proof continuity**
   - adapters connect to existing invariant bundles without flattening proof layering.
4. **Hardware-boundary contract hardening**
   - boot/runtime obligations are represented as concrete contracts.
5. **Evidence continuity**
   - tests and traces expand with no Tier 0–3 contract regression.

### M6 workstreams

- **WS-M6-A:** assumption inventory and boundary extraction ✅ completed (`SeLe4n/Kernel/Architecture/Assumptions.lean`),
- **WS-M6-B:** interface API + adapter semantics,
- **WS-M6-C:** proof integration with existing bundles,
- **WS-M6-D:** executable evidence and test-anchor expansion,
- **WS-M6-E:** documentation synchronization and handoff packaging.

Detailed execution guidance: [M6 Execution Plan and Workstreams](18-m6-execution-plan-and-workstreams.md).

### Non-goals for M6

- full platform bring-up,
- architecture-specific performance tuning,
- replacing M1–M5 theorem APIs unless required for soundness,
- broad subsystem redesign not required for architecture-boundary clarity.

## 4. Next-slice preview (post-M6)

Immediate next-slice direction is **Raspberry Pi 5-first binding and validation planning**.

Indicative outcomes:

1. instantiate M6 adapter contracts for Raspberry Pi 5 assumptions,
2. add platform-constraint evidence stories grounded in current model behavior,
3. map trust boundaries for a minimal realistic deployment partition.

## 5. Transition gates

### Gate: M5 closeout (completed)

Verified signals:

1. service semantics and policy surfaces merged and stable,
2. success/failure scenarios fixture-backed,
3. Tier 3 anchors include M5 theorem/invariant symbols,
4. docs synchronized for M5 closure.

### Gate: M5 → M6 (active, in progress)

Progress snapshot:

1. architecture assumptions explicit and reviewable ✅ (WS-M6-A complete),
2. interface artifacts preserve M1–M5 theorem layering (in progress; WS-M6-B/C),
3. test obligations added without regressing required gates (in progress; WS-M6-D/E).

### Gate: M6 → Raspberry Pi 5 binding slice (planned)

Require all:

1. boundary contracts can be instantiated without hidden assumptions,
2. adapter failure semantics are explicit and theorem-addressed,
3. documentation identifies platform obligations vs model guarantees.

## 6. Risk register (active)

1. **Semantic/proof skew**
   - risk: adapter semantics change without theorem updates,
   - mitigation: enforce transition + theorem pairing in PR templates.
2. **Roadmap drift**
   - risk: docs describe conflicting active slices,
   - mitigation: synchronize README/spec/DEVELOPMENT/GitBook in one PR.
3. **Boundary overcoupling**
   - risk: architecture interfaces leak into unrelated invariants,
   - mitigation: require local interface contracts + bridge lemmas.
4. **Hardware-path premature lock-in**
   - risk: overfitting before contracts stabilize,
   - mitigation: keep Raspberry Pi 5 work post-M6 and contract-driven.

## 7. Contributor operating cadence

1. per PR: state M6 workstream advanced + next unlock,
2. per checkpoint: map changes to M6 outcome matrix,
3. per milestone closeout: publish delivered outcomes, deferrals, and risk updates.
