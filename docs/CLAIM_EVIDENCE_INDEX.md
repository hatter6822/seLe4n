# Claim vs Evidence Index (WS-C8)

This index makes current semantic/proof/documentation claims auditable by linking each claim to executable or inspectable evidence.

## Active baseline claims

| Claim | Canonical source | Evidence command(s) | Evidence artifact(s) |
|---|---|---|---|
| Active findings baseline is `AUDIT_v0.9.32.md`. | `README.md`, `docs/spec/SELE4N_SPEC.md`, `docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md` | `./scripts/test_tier3_invariant_surface.sh` | Tier-3 doc-anchor checks over README/spec/planning references. |
| WS-C portfolio status is complete (WS-C1..WS-C8). | `docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md` (status dashboard) | `./scripts/test_full.sh` | Includes Tier-3 anchor validation + build + Tier-2 runtime checks. |
| Root docs and GitBook mirrors stay synchronized via canonical-first rules. | `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`, `docs/DOCS_DEDUPLICATION_MAP.md` | `./scripts/test_docs_sync.sh` | Regenerated navigation + markdown link validation + doc-gen probe when available. |
| IPC/scheduler/capability/info-flow invariants remain in active proof surface. | Kernel modules and invariant suites listed in `scripts/test_tier3_invariant_surface.sh` | `./scripts/test_tier3_invariant_surface.sh` | Direct symbol + theorem + doc anchor checks. |
| Executable behavior remains fixture-backed and malformed-state safe. | `tests/fixtures/main_trace_smoke.expected`, negative/IF suites | `./scripts/test_tier2_trace.sh`, `./scripts/test_tier2_negative.sh` | Stable trace fragments + negative/IF runtime checks. |

## Update policy

When a claim changes:

1. update canonical root source first,
2. update GitBook mirror(s) in the same PR,
3. refresh this table row(s) for changed claims,
4. run `./scripts/test_docs_sync.sh` and at least `./scripts/test_smoke.sh` (`./scripts/test_full.sh` when Tier-3 anchors/policies changed).
