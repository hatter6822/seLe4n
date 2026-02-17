# Comprehensive Audit 2026 Workstream Planning

This is the GitBook mirror of the canonical planning backbone:
[`docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md`](../audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md).

## 1) Why this chapter exists

- make the active slice obvious for new contributors,
- provide one-page navigation for WS-B workstreams,
- keep handbook structure aligned with the normative/audit docs.

## 2) Active workstream index (WS-B)

### High priority

- **WS-B1:** VSpace + memory model foundation ✅ completed
- **WS-B2:** Generative + negative testing expansion ✅ completed
- **WS-B3:** Main trace harness refactor
- **WS-B4:** Remaining type-wrapper migration

### Medium priority

- **WS-B5:** CSpace guard/radix semantics completion
- **WS-B6:** Notification-object IPC completion
- **WS-B7:** Information-flow proof-track start
- **WS-B8:** Documentation automation + consolidation
- **WS-B9:** Threat model and security hardening

### Low priority

- **WS-B10:** CI maturity upgrades
- **WS-B11:** Scenario framework finalization

## 3) Sequencing

- **Phase P1:** WS-B4 + WS-B3 + WS-B8
- **Phase P2:** WS-B5 + WS-B6 + WS-B2 (WS-B1/WS-B2 completed)
- **Phase P3:** WS-B7 + WS-B9 + WS-B10 + WS-B11

## 4) Evidence expectations for milestone-moving PRs

- workstream ID mapping,
- implementation/proof/test evidence,
- docs synchronization,
- explicit deferred items,
- no regression of stable M4–M7 baseline contracts.

## 5) Where to update status

When status changes, update together:

1. `docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md` (canonical)
2. `README.md` active-slice snapshot
3. `docs/SEL4_SPEC.md` milestone state
4. this chapter


## 6) WS-B1 closure evidence

- executable VSpace transitions: `SeLe4n/Kernel/Architecture/VSpace.lean`,
- VSpace invariant bundle and preservation anchors: `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`,
- deterministic map/unmap trace path in `Main.lean` + fixture update,
- ADR published: [`docs/VSPACE_MEMORY_MODEL_ADR.md`](../VSPACE_MEMORY_MODEL_ADR.md).

## 7) WS-B2 closure evidence

- bootstrap-state builder DSL published in `SeLe4n/Testing/StateBuilder.lean`,
- malformed-state negative suite published in `tests/NegativeStateSuite.lean` and enforced in smoke/full gates via `scripts/test_tier2_negative.sh`,
- nightly experimental replay now persists stochastic seed logs and `trace_sequence_probe_manifest.csv` for deterministic triage.
