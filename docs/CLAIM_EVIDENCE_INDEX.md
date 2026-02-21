# Claim vs Evidence Index

This index makes current semantic/proof/documentation claims auditable by linking each claim to executable or inspectable evidence.

## Active baseline claims

| Claim | Canonical source | Evidence command(s) | Evidence artifact(s) |
|---|---|---|---|
| Active findings baseline is `AUDIT_v0.11.0.md`. | `README.md`, `docs/spec/SELE4N_SPEC.md`, `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md` | `./scripts/test_tier3_invariant_surface.sh` | Tier-3 doc-anchor checks over README/spec/planning references. |
| WS-D portfolio status (WS-D1, WS-D2, WS-D3 completed; WS-D4..WS-D6 planned). | `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md` (status dashboard) | `./scripts/test_full.sh` | Includes Tier-3 anchor validation + build + Tier-2 runtime checks. |
| WS-C portfolio status is complete (WS-C1..WS-C8). | `docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md` (status dashboard) | `./scripts/test_full.sh` | Historical; evidence preserved in prior tier runs. |
| Root docs and GitBook mirrors stay synchronized via canonical-first rules. | `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`, `docs/DOCS_DEDUPLICATION_MAP.md` | `./scripts/test_docs_sync.sh` | Regenerated navigation + markdown link validation + doc-gen probe when available. |
| IPC/scheduler/capability/info-flow invariants remain in active proof surface. | Kernel modules and invariant suites listed in `scripts/test_tier3_invariant_surface.sh` | `./scripts/test_tier3_invariant_surface.sh` | Direct symbol + theorem + doc anchor checks. |
| Executable behavior remains fixture-backed and malformed-state safe. | `tests/fixtures/main_trace_smoke.expected`, negative/IF suites | `./scripts/test_tier2_trace.sh`, `./scripts/test_tier2_negative.sh` | Stable trace fragments + negative/IF runtime checks. |

## Proof claim qualification (WS-D3/F-16)

The following categories of theorems exist in the proof surface. Claims about proof coverage should distinguish between them:

| Category | Description | Assurance level |
|---|---|---|
| **Substantive preservation** | Proves that a *successful* operation preserves an invariant over *changed* state. | High |
| **Error-case preservation** | Proves that a *failed* operation preserves an invariant by returning unchanged state. Trivially true. | Low (technically correct but not security evidence) |
| **Reflexivity/tautological** | Proves `f(x) = f(x)` or compares a state to itself. | None (removed in WS-C3; should not recur) |
| **Non-interference** | Proves that a high-domain operation preserves low-equivalence for unrelated observers. | Critical for security assurance |

## Open proof obligations (WS-D tracked issues)

| ID | Description | Workstream | Status |
|---|---|---|---|
| TPI-D01 | Scheduler non-interference preservation | WS-D2 | CLOSED |
| TPI-D02 | Capability operations non-interference preservation | WS-D2 | CLOSED |
| TPI-D03 | Lifecycle operations non-interference preservation | WS-D2 | CLOSED |
| TPI-D04 | Badge-override safety in cspaceMint | WS-D3 | CLOSED |
| TPI-D05 | VSpace successful-operation preservation + round-trip theorems | WS-D3 | CLOSED |
| TPI-D06 | Waiting-list uniqueness invariant | WS-D4 | OPEN |
| TPI-D07 | Service dependency acyclicity invariant | WS-D4 | OPEN |

## Update policy

When a claim changes:

1. update canonical root source first,
2. update GitBook mirror(s) in the same PR,
3. refresh this table row(s) for changed claims,
4. run `./scripts/test_docs_sync.sh` and at least `./scripts/test_smoke.sh` (`./scripts/test_full.sh` when Tier-3 anchors/policies changed).
