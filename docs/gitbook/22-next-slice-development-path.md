# Next Development Path

## Current state

**Version:** 0.13.7 (Lean 4.28.0)

**Verified metrics snapshot (from `./scripts/report_current_state.py`):**
- Production LoC: 29,985 across 41 files
- Test LoC: 2,255 across 3 suites
- Proved declarations: 889 theorem/lemma declarations (zero sorry/axiom)
- Build jobs: 86

Four major portfolios are completed:

- **WS-H Phase 1–11** (v0.12.16–v0.13.7): Critical correctness fixes,
  security foundations, and VSpace enrichment — IPC call-path semantic fix
  (WS-H1), lifecycle safety guards (WS-H2), build/CI infrastructure hardening
  (WS-H3), capability invariant redesign (WS-H4), IPC dual-queue structural
  invariant (WS-H5), scheduler proof completion (WS-H6), HashMap equality +
  state-store migration (WS-H7), enforcement-NI bridge (WS-H8),
  non-interference coverage extension >80% (WS-H9), security model foundations
  including BIBA lattice, declassification model, and endpoint flow policy
  (WS-H10), VSpace & architecture enrichment with PagePermissions, W^X, TLB
  model, address bounds, and cross-ASID isolation (WS-H11).
  See [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-G** (v0.12.6–v0.12.15): All 14 kernel performance findings closed.
  Every hot path migrated to O(1) hash-based structures. See
  [Kernel Performance Optimization](08-kernel-performance-optimization.md).
- **WS-F1..F4** (v0.12.2–v0.12.5): All critical/high-priority audit findings
  resolved — IPC message transfer, untyped memory model, information-flow
  completeness, and proof gap closure.
- **WS-E, WS-D, WS-C, WS-B** (v0.9.0–v0.11.6): All earlier audit portfolios
  completed — test/CI hardening, proof quality, kernel design, model structure.

## Immediate next: WS-H12..H16 and WS-F5..F8

### WS-H12..H16 — Remaining v0.12.15 audit remediation

The remaining WS-H workstreams address Phases 4–5 of the v0.12.15 audit plan:

| ID | Focus | Priority |
|----|-------|----------|
| **WS-H11** | VSpace & architecture enrichment (PagePermissions, W^X, TLB model) | Medium — **Completed** |
| **WS-H12** | Scheduler/IPC semantic alignment (MCS contexts, budget tracking) | Medium |
| **WS-H13** | CSpace/service model enrichment (CDT refinement, service health) | Medium |
| **WS-H14** | Type safety hardening (phantom types, API boundary contracts) | Low |
| **WS-H15** | Platform hardening (RPi5 contract population, boot sequence) | Low |
| **WS-H16** | Testing and documentation expansion | Low |

See [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md)
for the full execution plan.

### WS-F5..F8 — Remaining v0.12.2 audit remediation

The remaining WS-F workstreams address medium/low-priority findings from the
v0.12.2 audits:

| ID | Focus | Priority |
|----|-------|----------|
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low |
| **WS-F8** | Cleanup (dead code, legacy/dual-queue resolution) | Low |

See [v0.12.2 Audit Remediation (WS-F)](24-comprehensive-audit-2026-workstream-planning.md)
for the full execution plan.

## After remaining workstreams: Raspberry Pi 5 binding (H3)

Once WS-F closes remaining proof and model gaps:

1. Populate RPi5 runtime contract with hardware-validated predicates.
2. Implement ARMv8 multi-level page table walk as a `VSpaceBackend` instance.
3. Implement GIC-400 interrupt routing with IRQ acknowledgment.
4. Bind timer adapter to ARM Generic Timer (CNTPCT_EL0).
5. Define boot sequence as a verified initial state construction.

The `Platform/RPi5/` stubs (BCM2712 memory map, GIC-400 constants, ARM64
config) are already in place from H3-prep.

## Long-horizon items

- MCS scheduling contexts (budget/period/replenishments).
- Multi-core support (per-core kernel instances).
- Device memory and IOMMU modeling.
- Cryptographic attestation of kernel image.
- Side-channel analysis at hardware binding layer.

## Related chapters

- Performance: [Kernel Performance Optimization (WS-G)](08-kernel-performance-optimization.md)
- Specification: [Specification & Roadmap](05-specification-and-roadmap.md)
- Hardware path: [Path to Real Hardware (Raspberry Pi 5)](10-path-to-real-hardware-mobile-first.md)
- Audit findings: [End-to-End Audit and Quality Gates](19-end-to-end-audit-and-quality-gates.md)
