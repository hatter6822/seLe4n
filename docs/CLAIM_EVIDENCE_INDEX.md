# Claim vs Evidence Index

This index makes current semantic/proof/documentation claims auditable by linking each claim to executable or inspectable evidence.

## Active baseline claims

| Claim | Canonical source | Evidence command(s) | Evidence artifact(s) |
|---|---|---|---|
| Active findings baseline is `AUDIT_CODEBASE_v0.11.6.md`. | `README.md`, `docs/spec/SELE4N_SPEC.md`, `docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md` | `./scripts/test_tier3_invariant_surface.sh` | Tier-3 doc-anchor checks over README/spec/planning references. |
| WS-E portfolio status (WS-E1 completed; WS-E2 completed; WS-E3..WS-E6 planned). | `docs/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md` (status dashboard) | `./scripts/test_full.sh` | Includes Tier-3 anchor validation + build + Tier-2 runtime checks. |
| WS-D portfolio is complete (WS-D1..WS-D4 completed; WS-D5/D6 absorbed into WS-E). | `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md` (status dashboard) | `./scripts/test_full.sh` | Historical; evidence preserved in prior tier runs. |
| WS-C portfolio status is complete (WS-C1..WS-C8). | `docs/dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md` (status dashboard) | `./scripts/test_full.sh` | Historical; evidence preserved in prior tier runs. |
| Root docs and GitBook mirrors stay synchronized via canonical-first rules. | `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`, `docs/DOCS_DEDUPLICATION_MAP.md` | `./scripts/test_docs_sync.sh` | Regenerated navigation + markdown link validation + doc-gen probe when available. |
| IPC/scheduler/capability/info-flow invariants remain in active proof surface. | Kernel modules and invariant suites listed in `scripts/test_tier3_invariant_surface.sh` | `./scripts/test_tier3_invariant_surface.sh` | Direct symbol + theorem + doc anchor checks. |
| Executable behavior remains fixture-backed and malformed-state safe. | `tests/fixtures/main_trace_smoke.expected`, negative/IF suites | `./scripts/test_tier2_trace.sh`, `./scripts/test_tier2_negative.sh` | Stable trace fragments + negative/IF runtime checks. |

## Proof claim qualification (WS-D3/F-16, updated by v0.11.6 audit C-01/H-01)

The following categories of theorems exist in the proof surface. Claims about proof coverage should distinguish between them:

| Category | Description | Assurance level |
|---|---|---|
| **Substantive preservation** | Proves that a *successful* operation preserves an invariant over *changed* state. | High |
| **Error-case preservation** | Proves that a *failed* operation preserves an invariant by returning unchanged state. Trivially true. | Low (technically correct but not security evidence) |
| **Non-compositional preservation** | Proves preservation by re-proving invariant components from scratch on post-state, discarding pre-state evidence. Structurally valid but masks lack of engagement with the operation's state transformation. (Identified by v0.11.6 audit H-01; targeted by WS-E2.) | Medium (weaker than compositional proofs) |
| **Tautological** | Proves a property that holds for *all* states by construction (e.g., `cspaceSlotUnique_holds` exploiting pure-function determinism). (Identified by v0.11.6 audit C-01; targeted by WS-E2.) | None (should be reformulated or documented as meta-properties) |
| **Non-interference** | Proves that a high-domain operation preserves low-equivalence for unrelated observers. | Critical for security assurance |

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
