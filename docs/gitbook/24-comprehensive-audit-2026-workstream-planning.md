# Comprehensive Audit 2026 Workstream Planning

## Active planning (v0.11.6 — WS-E)

The current active execution baseline is the **WS-E portfolio** based on the v0.11.6 audit.

- Findings baseline: [`docs/audits/AUDIT_CODEBASE_v0.11.6.md`](../audits/AUDIT_CODEBASE_v0.11.6.md)
- Canonical planning source: [`docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md)

See the workstream plan for WS-E1..WS-E6 details and phase sequencing. WS-E1 through WS-E6 are completed.

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

- **C-01:** Tautological proofs reformulated to structural invariants with real witnesses (`cspaceSlotUnique` encodes CNode slot-index uniqueness via `CNode.slotsUnique`).
- **H-01:** Non-compositional proofs refactored to derive post-state from pre-state via transfer lemmas.
- **H-03:** Badge safety gap closed with end-to-end chain from `mintDerivedCap_badge_propagated` through `badge_notification_routing_consistent`.

### WS-E3 completed summary

**WS-E3 — Kernel semantic hardening** has been completed (v0.11.10). All 6 findings resolved:

- **H-06:** Sentinel ID convention established — ID 0 reserved for all identifier types. Added `isReserved`, `sentinel`, `ObjId.valid` predicates and identity theorems. `ThreadId.toObjId_injective` proven.
- **H-07:** `vspaceInvariantBundle` composed into `proofLayerInvariantBundle`, closing the gap where VSpace invariants were isolated from the global proof layer. Adapter preservation theorems added.
- **H-08:** BFS `serviceHasPathTo` returns `true` on fuel exhaustion (conservative for cycle detection). Soundness theorems: `serviceHasPathTo_fuel_zero_is_true`, `serviceHasPathTo_false_implies_not_fuel_exhaustion`, `serviceBfsFuel_adequate`.
- **H-09:** Endpoint operations (`endpointSend`, `endpointAwaitReceive`, `endpointReceive`) now perform compound 3-step transitions: `storeObject` → `storeTcbIpcState` → `removeRunnable`/`ensureRunnable`. IPC-scheduler contract predicates are now non-vacuous. All invariant preservation proofs rewritten for compound transitions.
- **M-09:** Metadata sync correctness proven for type-changing `storeObject`: `storeObject_metadata_sync_type_change` and `storeObject_metadata_sync_capref_at_stored`.
- **L-06:** Default `SystemState` initialization proof: `default_systemState_lifecycleConsistent` and `default_system_state_proofLayerInvariantBundle`.

### WS-E4 completed summary

**WS-E4 — Capability and IPC model completion** has been completed (v0.11.11). All 7 findings resolved:

- **C-02, C-03, C-04:** Capability model completeness — CNode operations, slot management, and authority tracking gaps closed.
- **H-02:** IPC completion — endpoint/notification operations fully covered with invariant preservation.
- **M-01, M-02, M-12:** Model refinements — object metadata, type safety, and reference tracking.

### WS-E5 completed summary

**WS-E5 — Information-flow maturity** has been completed (v0.11.12). All 3 findings resolved:

- **H-04:** Parameterized security labels supporting ≥3 domains — `SecurityDomain` (Nat-indexed), `DomainFlowPolicy` with reflexive/transitive well-formedness proofs, `GenericLabelingContext`, `EndpointFlowPolicy` per-endpoint overrides, `embedLegacyLabel` backward-compatibility with preservation proof, `threeDomainExample` validation.
- **H-05:** Composed bundle-level non-interference — `NonInterferenceStep` inductive (5 kernel operations), `composedNonInterference_step` single-step theorem, `NonInterferenceTrace` multi-step lift, `composedNonInterference_trace`, `errorAction_preserves_lowEquiv`. Completes IF-M4 milestone.
- **M-07:** Enforcement boundary specification — `EnforcementClass` 3-way classification (`policyGated`/`capabilityOnly`/`readOnly`), exhaustive 17-entry `enforcementBoundary` table, denial preservation theorems, complete-disjunction sufficiency proofs.

### WS-E6 completed summary

**WS-E6 — Model completeness and documentation** has been completed (v0.12.0). All 10 findings resolved:

- **M-03:** Three-level EDF scheduling (`isBetterCandidate`: priority > deadline > FIFO) with `isBetterCandidate_irrefl`/`_asymm` algebraic theorems. `Deadline` typed identifier. `TCB.deadline` field.
- **M-04:** Time-slice preemption via `timerTick` operation (decrement/reset+reschedule). `TCB.timeSlice` field. `defaultTimeSlice` constant. `timeSlicePositive` invariant.
- **M-05:** Domain scheduling with `DomainScheduleEntry`, `filterByDomain`, `chooseThreadInDomain`, `switchDomain`, `scheduleDomain`. `currentThreadInActiveDomain` invariant. Preservation theorems include `switchDomain_preserves_schedulerInvariantBundle`, `chooseThreadInDomain_preserves_schedulerInvariantBundle`, and `scheduleDomain_preserves_schedulerInvariantBundle`.
- **M-08:** Architecture assumption consumption bridges connecting structural axioms to adapter preservation proofs.
- **F-17:** O(n) design decision ADR with rationale, scope note, and migration path.
- **L-01:** Unified `API.lean` with `apiInvariantBundle` alias, base-case theorem, and 30+ entry-point stability table.
- **L-02:** Memory zero-default semantics documented with 4 theorems.
- **L-03:** `KernelM` monad helpers with 6 correctness theorems.
- **L-04:** `toObjIdChecked` safe variant with correctness theorem; deferred-check design documented.
- **L-05:** Monotonic `objectIndex` design documented with monotonicity theorem.

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
