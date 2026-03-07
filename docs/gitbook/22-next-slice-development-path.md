# Next Development Path

## Current state

**Version:** 0.13.3 (Lean 4.28.0)

**Verified metrics snapshot (from `./scripts/report_current_state.py`):**
- Production LoC: 26,861 across 40 files
- Test LoC: 2,063 across 3 suites
- Proved declarations: 801 theorem/lemma declarations (zero sorry/axiom)
- Build jobs: 84

Three major portfolios are completed:

- **WS-H Phase 1–8** (v0.12.16–v0.13.2): Critical correctness fixes — IPC
  call-path semantic bug (WS-H1), lifecycle safety guards (WS-H2), build/CI
  infrastructure hardening (WS-H3), capability invariant redesign (WS-H4),
  IPC dual-queue structural invariant (WS-H5), scheduler proof completion
  with EDF invariant domain-fix and timeSlicePositive preservation (WS-H6),
  enforcement-NI bridge with 4 new enforcement wrappers and projection
  hardening (WS-H8). See
  [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-G** (v0.12.6–v0.12.15): All 14 kernel performance findings closed.
  Every hot path migrated to O(1) hash-based structures. See
  [Kernel Performance Optimization](08-kernel-performance-optimization.md).
- **WS-F1..F4** (v0.12.2–v0.12.5): All critical/high-priority audit findings
  resolved — IPC message transfer, untyped memory model, information-flow
  completeness, and proof gap closure.

## Immediate next: WS-F5..F8

The remaining WS-F workstreams address medium/low-priority findings from the
v0.12.2 audits. These are organized into two phases:

### P3 — Model fidelity and invariant quality (WS-F5, WS-F6)

- **WS-F5** (Model fidelity): Notification badge bitmask semantics, per-thread
  register state, multi-level CSpace lookups.
- **WS-F6** (Invariant quality): Reclassify remaining tautological invariants,
  instantiate adapter proof hooks with structural witnesses.

### P4 — Testing and cleanup (WS-F7, WS-F8)

- **WS-F7** (Testing expansion): Extend runtime oracle and trace probe
  coverage. Add fixture scenarios for newly optimized data structures.
- **WS-F8** (Cleanup): Resolve legacy/dual-queue API divergence, remove dead
  code paths, consolidate deprecated operations.

See [v0.12.2 Audit Remediation (WS-F)](24-comprehensive-audit-2026-workstream-planning.md)
for the full execution plan.

## After WS-F: Raspberry Pi 5 binding (H3)

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
