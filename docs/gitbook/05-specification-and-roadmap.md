# Specification and Roadmap

This chapter translates the normative spec (`docs/SEL4_SPEC.md`) into contributor-oriented
planning and delivery guidance.

## 1. Baseline status

Milestone status for planning purposes:

- M4-A complete,
- M4-B complete,
- M5 complete,
- **M6 complete**,
- **M7 complete (audit remediation workstreams)**.

Post-M6 planning should build on existing transition and theorem surfaces rather than restructuring
closed milestone contracts.

## 2. Stable outcomes now treated as contracts

Contributors should treat these as stable unless a spec-level change is explicitly approved:

1. deterministic lifecycle/capability/service transition behavior,
2. layered invariant composition across scheduler/capability/IPC/lifecycle/service modules,
3. local + composed preservation entrypoints for established transitions,
4. fixture-backed executable traces for core success/failure stories,
5. Tier 3 theorem/invariant symbol anchors for claimed surfaces,
6. explicit architecture-boundary assumptions and adapter preservation hooks from M6.

## 3. Completed predecessor slice recap: M6

M6 scope: **architecture-binding interfaces and hardware-facing assumption hardening**.

### M6 target outcomes (all complete)

1. assumption extraction and interface definition,
2. adapter semantics and bounded error surfaces,
3. composed proof continuity,
4. hardware-boundary contract hardening,
5. evidence continuity across test tiers.

Detailed archive: [M6 Execution Plan and Workstreams](18-m6-execution-plan-and-workstreams.md).

## 4. Completed remediation slice: M7 audit remediation

M7 remediation (WS-A1 through WS-A8) is now complete and serves as the immediate predecessor baseline for next-slice hardware-oriented work.

### M7 slice objectives

1. harden CI/test gates and branch-policy evidence,
2. improve architecture API clarity and module symmetry,
3. complete high-value type-safety migration,
4. expand test depth for scale and edge-heavy scenarios,
5. isolate test-only contracts from runtime-facing paths,
6. align root docs + handbook for current/next-slice clarity,
7. improve proof maintainability and theorem explainability,
8. establish platform/security readiness for the next slice.

### M7 planning links

- [M7 Current Slice Outcomes and Workstreams](21-m7-current-slice-outcomes-and-workstreams.md)
- [Repository Audit Remediation Workstreams](20-repository-audit-remediation-workstreams.md)
- [`docs/AUDIT_REMEDIATION_WORKSTREAMS.md`](../AUDIT_REMEDIATION_WORKSTREAMS.md)

## 5. Next-slice preview (post-M7)

After M7 closes, planned direction is a **hardware-oriented expansion slice** with Raspberry Pi 5
as first architecture focus.

Primary goals for that slice:

1. bind explicit assumptions to platform-facing constraints,
2. evolve adapters with architecture-specific specialization while preserving determinism,
3. add architecture-targeted evidence tracks in CI/test layers,
4. publish staged information-flow/security proof milestones.

See [Next Slice Development Path (Post-M7)](22-next-slice-development-path.md).

## 6. Transition gates

### Gate: M5 closeout (completed)

Verified signals:

1. service semantics and policy surfaces merged and stable,
2. success/failure scenarios fixture-backed,
3. Tier 3 anchors include M5 theorem/invariant symbols,
4. docs synchronized for M5 closure.

### Gate: M6 closeout (completed)

Verified signals:

1. architecture assumptions explicit and reviewable,
2. interface artifacts preserve M1–M5 theorem layering,
3. test obligations added without regressing required gates,
4. WS-M6-D and WS-M6-E complete (including documentation synchronization and handoff packaging ✅ completed).

### Gate: M7 → next slice (completed)

Verified signals:

1. high-priority remediation workstreams are closed with reproducible evidence,
2. CI and test obligations (including promoted proof-surface gates) are stable,
3. documentation consistently marks M7 as complete and next-slice path as active,
4. hardware-path assumptions and ownership table are published.
5. M7 closeout packet published (`docs/M7_CLOSEOUT_PACKET.md`).

## 7. Risk register (next-slice activation)

1. **Semantic/proof skew**
   - risk: transition changes land without theorem updates,
   - mitigation: enforce transition + theorem pairing and Tier 3 anchors.
2. **Roadmap drift**
   - risk: docs describe conflicting active slices,
   - mitigation: synchronize README/spec/DEVELOPMENT/GitBook in one PR.
3. **Boundary overcoupling**
   - risk: architecture interfaces leak into unrelated invariants,
   - mitigation: require local interface contracts + bridge lemmas.
4. **Hardware-path premature lock-in**
   - risk: overfitting before remediation controls stabilize,
   - mitigation: keep platform work contract-driven and simulation-backed initially.

## 8. Contributor operating cadence

1. per PR: state workstream advanced + target outcome moved,
2. per checkpoint: map changes to current-slice outcome matrix,
3. per milestone closeout: publish delivered outcomes, deferrals, and risk updates.
