# Claim vs Evidence Index

This index makes current semantic/proof/documentation claims auditable by linking each claim to executable or inspectable evidence.

## Active baseline claims

| Claim | Canonical source | Evidence command(s) | Evidence artifact(s) |
|---|---|---|---|
| Active findings baseline is `AUDIT_CODEBASE_v0.11.6.md`. | `README.md`, `docs/spec/SELE4N_SPEC.md`, `docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md` | `./scripts/test_tier3_invariant_surface.sh` | Tier-3 doc-anchor checks over README/spec/planning references. |
| WS-E portfolio status (WS-E1 through WS-E6 completed). | `docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md` (status dashboard) | `./scripts/test_full.sh` | Includes Tier-3 anchor validation + build + Tier-2 runtime checks. |
| WS-D portfolio is complete (WS-D1..WS-D4 completed; WS-D5/D6 absorbed into WS-E). | `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md` (status dashboard) | `./scripts/test_full.sh` | Historical; evidence preserved in prior tier runs. |
| WS-C portfolio status is complete (WS-C1..WS-C8). | `docs/dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md` (status dashboard) | `./scripts/test_full.sh` | Historical; evidence preserved in prior tier runs. |
| Root docs and GitBook mirrors stay synchronized via canonical-first rules. | `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`, `docs/DOCS_DEDUPLICATION_MAP.md` | `./scripts/test_docs_sync.sh` | Regenerated navigation + markdown link validation + doc-gen probe when available. |
| IPC/scheduler/capability/info-flow invariants remain in active proof surface. | Kernel modules and invariant suites listed in `scripts/test_tier3_invariant_surface.sh` | `./scripts/test_tier3_invariant_surface.sh` | Direct symbol + theorem + doc anchor checks. |
| Executable behavior remains fixture-backed and malformed-state safe. | `tests/fixtures/main_trace_smoke.expected`, negative/IF suites | `./scripts/test_tier2_trace.sh`, `./scripts/test_tier2_negative.sh` | Stable trace fragments + negative/IF runtime checks. |
| Queue ownership metadata is now embedded in core kernel objects (`SchedulerState.runnableHead`/`runnableTail`, `TCB.queuePrev`/`queueNext`) with runtime intrusive-queue consistency checks over endpoint `sendQ`/`receiveQ`. | `SeLe4n/Model/State.lean`, `SeLe4n/Model/Object.lean`, `SeLe4n/Kernel/IPC/Operations.lean`, `SeLe4n/Testing/InvariantChecks.lean`, `tests/NegativeStateSuite.lean` | `source ~/.elan/env && lake build`, `./scripts/test_smoke.sh`, `./scripts/test_full.sh` | Build + smoke/full tiers validate intrusive queue link invariants and dual-queue runtime behavior. |

## Proof claim qualification (WS-D3/F-16, updated by v0.11.6 audit C-01/H-01; C-01/H-01 resolved by WS-E2)

The following categories of theorems exist in the proof surface. Claims about proof coverage should distinguish between them:

| Category | Description | Assurance level |
|---|---|---|
| **Substantive preservation** | Proves that a *successful* operation preserves an invariant over *changed* state. | High |
| **Error-case preservation** | Proves that a *failed* operation preserves an invariant by returning unchanged state. Trivially true. | Low (technically correct but not security evidence) |
| **Compositional preservation** | Derives post-state invariant from pre-state through operation-specific transfer lemmas (`cspaceSlotUnique_of_storeObject_*`, `CNode.insert_slotsUnique`, etc.). (WS-E2 H-01 resolved: all preservation proofs refactored to this pattern.) | High |
| **Structural invariant** | Proves a genuine structural property requiring a witness (e.g., `capabilityInvariantBundle_of_slotUnique` requires `CNode.slotsUnique` evidence). (WS-E2 C-01 resolved: former tautological proofs reformulated.) | High |
| **End-to-end chain** | Proves a multi-step semantic property across subsystem boundaries (e.g., `badge_notification_routing_consistent` — badge propagation from mint through notification signal/wait). (WS-E2 H-03 resolved.) | High |
| **Non-interference** | Proves that a high-domain operation preserves low-equivalence for unrelated observers. | Critical for security assurance |

### Resolved proof qualification findings (WS-E2)

| Finding | Prior category | Resolution |
|---|---|---|
| C-01 (Tautological proofs) | Tautological (assurance: None) | Reformulated to **Structural invariant**: `cspaceSlotUnique` now encodes CNode slot-index uniqueness via `CNode.slotsUnique`; `cspaceLookupSound` proves lookup completeness; bridge theorem `cspaceLookupSound_of_cspaceSlotUnique` connects them; `capabilityInvariantBundle_of_slotUnique` replaces tautological `capabilityInvariantBundle_holds`. |
| H-01 (Non-compositional proofs) | Non-compositional preservation (assurance: Medium) | Refactored to **Compositional preservation**: all preservation proofs derive post-state from pre-state via transfer lemmas. CNode operations use `CNode.insert_slotsUnique`, `CNode.remove_slotsUnique`, `CNode.revokeTargetLocal_slotsUnique`. |
| H-03 (Badge safety gap) | Gap (no theorem) | Closed with **End-to-end chain**: `mintDerivedCap_badge_propagated` -> `cspaceMint_child_badge_preserved` -> `notificationSignal_badge_stored_fresh` -> `notificationWait_recovers_pending_badge` -> `badge_notification_routing_consistent`; plus `badge_merge_idempotent`. |

## Closed proof obligations (WS-D tracked issues)

| ID | Description | Workstream | Status |
|---|---|---|---|
| TPI-D01 | Scheduler non-interference preservation | WS-D2 | CLOSED |
| TPI-D02 | Capability operations non-interference preservation | WS-D2 | CLOSED |
| TPI-D03 | Lifecycle operations non-interference preservation | WS-D2 | CLOSED |
| TPI-D04 | Badge-override safety in cspaceMint | WS-D3 | CLOSED |
| TPI-D05 | VSpace successful-operation preservation + round-trip theorems | WS-D3 | CLOSED |
| TPI-D06 | Waiting-list uniqueness invariant | WS-D4 | CLOSED |
| TPI-D07 | Service dependency acyclicity invariant (Risk 0 resolved: vacuous definition fixed, declarative proof complete; BFS completeness bridge formally proved — TPI-D07-BRIDGE resolved). **BFS completeness proof:** the sole remaining `sorry` has been eliminated via a loop-invariant argument using `serviceCountBounded` as a precondition, establishing that BFS exploration with bounded fuel covers all reachable service nodes. No `sorry` remains in the acyclicity proof surface. | WS-D4 | CLOSED |

## Update policy

When a claim changes:

1. update canonical root source first,
2. update GitBook mirror(s) in the same PR,
3. refresh this table row(s) for changed claims,
4. run `./scripts/test_docs_sync.sh` and at least `./scripts/test_smoke.sh` (`./scripts/test_full.sh` when Tier-3 anchors/policies changed).
