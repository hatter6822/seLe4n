# Next Development Path

## Current state

**Version:** 0.14.10 (Lean v4.28.0)

**Verified metrics snapshot (from [`docs/codebase_map.json`](../../docs/codebase_map.json) `readme_sync`):**
- Production LoC: 34,171 across 67 files
- Test LoC: 2,886 across 3 suites
- Proved declarations: 1,086 theorem/lemma declarations (zero sorry/axiom)
- Total declarations: 2,006 across 70 modules

Four major portfolios are completed:

- **WS-H Phase 1–12f** (v0.12.16–v0.14.3): Critical correctness fixes,
  security foundations, VSpace enrichment, legacy cleanup, scheduler
  semantic alignment, and full WS-H12 completion — IPC call-path semantic
  fix (WS-H1), lifecycle safety guards (WS-H2), build/CI infrastructure
  hardening (WS-H3), capability invariant redesign (WS-H4), IPC dual-queue
  structural invariant (WS-H5), scheduler proof completion (WS-H6), HashMap
  equality + state-store migration (WS-H7), enforcement-NI bridge (WS-H8),
  non-interference coverage extension >80% (WS-H9), security model
  foundations including BIBA lattice, declassification model, and endpoint
  flow policy (WS-H10), VSpace & architecture enrichment with
  PagePermissions, W^X, TLB model, address bounds, and cross-ASID isolation
  (WS-H11), legacy endpoint field and operation removal (WS-H12a),
  dequeue-on-dispatch scheduler semantics matching seL4's
  `switchToThread`/`tcbSchedDequeue` (WS-H12b), per-TCB register context
  with inline context switch (WS-H12c), bounded IPC message payloads
  matching seL4 limits (WS-H12d), cross-subsystem invariant reconciliation
  (WS-H12e), and test harness + documentation sync (WS-H12f).
  See [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-G** (v0.12.6–v0.12.15): All 14 kernel performance findings closed.
  Every hot path migrated to O(1) hash-based structures. See
  [Kernel Performance Optimization](08-kernel-performance-optimization.md).
- **WS-F1..F4** (v0.12.2–v0.12.5): All critical/high-priority audit findings
  resolved — IPC message transfer, untyped memory model, information-flow
  completeness, and proof gap closure.
- **WS-E, WS-D, WS-C, WS-B** (v0.9.0–v0.11.6): All earlier audit portfolios
  completed — test/CI hardening, proof quality, kernel design, model structure.

## Immediate next: WS-F8

### Remaining WS-H workstreams — v0.12.15 audit remediation

WS-H1..H15 are all completed. The remaining workstream addresses Phase 5:

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-H14** | Type safety hardening: EquivBEq/LawfulBEq instances, LawfulMonad proofs, isPowerOfTwo verification, OfNat removal, sentinel completion | Low | **COMPLETED** |
| **WS-H15** | Platform & API hardening: InterruptBoundaryContract decidability, RPi5 contract hardening, syscall capability wrappers, AdapterProofHooks instantiation | Low | **COMPLETED** |
| **WS-H16** | Testing and documentation expansion | Low | Pending |

See [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md)
for the full execution plan.

### WS-F8 — Remaining v0.12.2 audit remediation

WS-F5 (model fidelity) completed in v0.14.9. WS-F6 (invariant quality) completed
in v0.14.9. WS-F7 (testing expansion) completed. The remaining WS-F workstream
addresses low-priority findings from the v0.12.2 audits:

| ID | Focus | Priority |
|----|-------|----------|
| **WS-F5** | Model fidelity (word-bounded badge, order-independent rights, deferred ops) | Medium — **COMPLETED** (v0.14.9) |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium — **COMPLETED** (v0.14.9) |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low — **COMPLETED** |
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
