# Specification and Roadmap

This chapter translates the normative spec (`docs/SEL4_SPEC.md`) into contributor-oriented
planning and delivery guidance.

## 1. Baseline status

Milestone status for planning purposes:

- M4-A complete,
- M4-B complete,
- M5 complete,
- **M6 complete**.

Post-M6 planning should build on existing transition and theorem surfaces rather than restructuring
closed milestone contracts.

## 2. Stable outcomes now treated as contracts

Contributors should treat these as stable unless a spec-level change is explicitly approved:

1. deterministic lifecycle/capability/service transition behavior,
2. layered invariant composition across scheduler/capability/IPC/lifecycle/service modules,
3. local + composed preservation entrypoints for established transitions,
4. fixture-backed executable traces for core success/failure stories,
5. Tier 3 theorem/invariant symbol anchors for claimed surfaces.

## 3. Completed predecessor slice recap: M6

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
- **WS-M6-B:** interface API + adapter semantics ✅ completed (`SeLe4n/Kernel/Architecture/Adapter.lean`),
- **WS-M6-C:** proof integration with existing bundles ✅ completed (`SeLe4n/Kernel/Architecture/Invariant.lean`),
- **WS-M6-D:** executable evidence and test-anchor expansion ✅ completed (`Main.lean`, `tests/fixtures/main_trace_smoke.expected`, `scripts/test_tier3_invariant_surface.sh`),
- **WS-M6-E:** documentation synchronization and handoff packaging ✅ completed.

Detailed execution guidance: [M6 Execution Plan and Workstreams](18-m6-execution-plan-and-workstreams.md).

### Non-goals for M6

- full platform bring-up,
- architecture-specific performance tuning,
- replacing M1–M5 theorem APIs unless required for soundness,
- broad subsystem redesign not required for architecture-boundary clarity.

## 4. M6 closeout handoff signals

1. WS-M6-A through WS-M6-E are complete and traceable from docs to code/proofs/tests.
2. Boundary contracts are explicit enough to support Raspberry Pi 5-first instantiation work.
3. Risk controls now focus on contract-instantiation discipline rather than boundary extraction.

## 5. Current active slice preview: M7 audit remediation

Current active direction is **repository-audit remediation workstreams (WS-A1 through WS-A8)**.

Indicative outcomes:

1. promote CI/test gates and harden delivery controls,
2. complete architecture and API-surface cleanup identified by the audit,
3. improve type safety and test-scale coverage without regressing M1–M6 proofs,
4. synchronize documentation and governance artifacts as measurable closure evidence.

## 6. Transition gates

### Gate: M5 closeout (completed)

Verified signals:

1. service semantics and policy surfaces merged and stable,
2. success/failure scenarios fixture-backed,
3. Tier 3 anchors include M5 theorem/invariant symbols,
4. docs synchronized for M5 closure.

### Gate: M5 → M6 (completed)

Progress snapshot:

1. architecture assumptions explicit and reviewable ✅ (WS-M6-A complete),
2. interface artifacts preserve M1–M5 theorem layering ✅ (WS-M6-B and WS-M6-C complete),
3. test obligations added without regressing required gates ✅ (WS-M6-D and WS-M6-E complete).

### Gate: audit remediation → Raspberry Pi 5 binding slice (planned)

Require all:

1. high-priority remediation workstreams are closed with evidence,
2. CI and test obligations (including promoted proof-surface gates) are stable,
3. documentation consistently marks audit remediation as complete and hardware-binding as next.

## 7. Risk register (post-M6 / remediation-active updated)

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
   - risk: overfitting before remediation controls stabilize,
   - mitigation: keep Raspberry Pi 5 work post-remediation and contract-driven.

## 8. Contributor operating cadence

1. per PR: state M6 workstream advanced + next unlock,
2. per checkpoint: map changes to M6 outcome matrix,
3. per milestone closeout: publish delivered outcomes, deferrals, and risk updates.
