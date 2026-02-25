# Comprehensive Audit 2026 Workstream Planning

## Active planning (v0.11.6 — WS-E)

The current active execution baseline is the **WS-E portfolio** based on the v0.11.6 audit.

- Findings baseline: [`docs/audits/AUDIT_CODEBASE_v0.11.6.md`](../audits/AUDIT_CODEBASE_v0.11.6.md)
- Canonical planning source: [`docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md)

See the workstream plan for WS-E1..WS-E6 details and phase sequencing.

### WS-E1 completed summary

**WS-E1 — Test infrastructure and CI hardening** has been completed. All 8 findings resolved:

- **F-14:** SHA-pinned all GitHub Actions across 4 workflow files to full 40-character commit hashes.
- **M-10:** Added parameterized test topologies (3 configurations varying thread count, priority, CNode radix, ASID count).
- **M-11:** Added 5 runtime invariant check families: CSpace coherency, capability rights structure, lifecycle metadata consistency, service graph acyclicity, VSpace ASID uniqueness.
- **L-07:** Converted fixture to structured `scenario_id | risk_class | expected_fragment` format (backward-compatible).
- **L-08:** Added theorem-body spot-check validation and F-14 regression guard to Tier 0 hygiene.
- F-09, F-10, F-15: previously resolved.

### WS-E2 completed summary

**WS-E2 — Proof quality and invariant strengthening** has been completed. All 3 findings resolved:

- **C-01:** Reformulated tautological invariant proofs to require genuine structural witnesses.
- **H-01:** Refactored all preservation proofs to compositional pattern using operation-specific transfer lemmas.
- **H-03:** Closed badge override safety gap with `badge_notification_routing_consistent` end-to-end chain proof.

### WS-E3 completed summary

**WS-E3 — Kernel semantic hardening** has been completed. All 6 findings resolved:

- **H-06:** Added `threadCount_bounded_after_setDomain` invariant; sentinel ID 0 convention enforced in Prelude.
- **H-07:** Added `capMint_preserves_object_store` invariant proving capability minting does not modify the object store.
- **H-08:** Added `capRevoke_siblings_unreachable` invariant; BFS fuel-exhaustion now returns conservative `true`.
- **H-09:** Replaced `sorry` in `endpointSend_preserves_lowEquivalent` with complete machine-checked proof using projection-preservation strategy. Endpoint send/receive transitions now enforce thread IPC state changes.
- **M-09:** Added `endpointSend_preserves_scheduler_invariant` proving endpoint send preserves scheduler queue/current-thread consistency.
- **L-06:** Added `retypeObjects_preserves_scheduler` proving retype does not modify scheduler state.

Zero `sorry` remains in the entire codebase.

## Historical: WS-D portfolio (v0.11.0 — completed)

The WS-D portfolio has been completed (WS-D1..WS-D4) with WS-D5/WS-D6 absorbed into WS-E. It is retained for traceability.

- Historical planning source: [`docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md)
- Historical proof obligations: [`docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md`](../audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md)

### WS-D completed summary

| Workstream | Priority | Findings | Status |
|---|---|---|---|
| WS-D1 Test error handling and validity | Critical/High | F-01, F-03, F-04 | **Completed** |
| WS-D2 Information-flow enforcement and proof | High | F-02, F-05 | **Completed** |
| WS-D3 Proof gap closure | Medium | F-06, F-08, F-16 | **Completed** |
| WS-D4 Kernel design hardening | Medium | F-07, F-11, F-12 | **Completed** |
| WS-D5 Test infrastructure expansion | Medium | F-09, F-10 | Absorbed into WS-E |
| WS-D6 CI/CD and documentation polish | Low | F-13, F-14, F-15, F-17 | Absorbed into WS-E |

## Historical: WS-C portfolio (v0.9.32 — completed)

The WS-C portfolio has been completed and is retained for traceability.

- Historical planning source: [`docs/dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md)
- Historical proof obligations: [`docs/dev_history/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`](../dev_history/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md)

### WS-C completed summary

- **WS-C1:** IPC handshake correctness -- completed
- **WS-C2:** Scheduler semantic fidelity -- completed
- **WS-C3:** Proof-surface de-tautologization -- completed
- **WS-C4:** Test validity hardening -- completed
- **WS-C5:** Information-flow assurance -- completed
- **WS-C6:** CI and supply-chain hardening -- completed
- **WS-C7:** Model structure and maintainability -- completed
- **WS-C8:** Documentation and GitBook consolidation -- completed

## Updating status

When any WS-E status changes, update all surfaces listed in the v0.11.6 workstream plan.

## Historical references

The WS-B portfolio (`AUDIT_v0.9.0_WORKSTREAM_PLAN.md`) is retained for provenance and completed-history context only.
