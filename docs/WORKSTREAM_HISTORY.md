# Workstream History

This document is the canonical record of all completed and planned workstreams
for the seLe4n project. It consolidates workstream information that was
previously spread across README.md, GitBook chapters, and audit plans.

## How to use this document

- **New contributors**: skim the "What's next" section to understand current
  priorities, then jump to the linked audit plans for details.
- **Returning contributors**: check "What's next" for the current slice, then
  review the completed workstream closest to your area of interest.
- **Auditors**: use the portfolio table as a traceability index linking each
  workstream to its version, scope, and evidence.

## What's next

### Remaining WS-H workstreams (H14-H16)

WS-H1..H13 are all completed. The remaining workstreams address Phases 4-5 of
the [v0.12.15 audit plan](audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md):

| ID | Focus | Priority |
|----|-------|----------|
| **WS-H14** | Type safety hardening (phantom types, API boundary contracts) | Low |
| **WS-H15** | Platform hardening (RPi5 contract population, boot sequence) | Low |
| **WS-H16** | Testing and documentation expansion | Low |

### Remaining WS-F workstreams (F5-F8)

The critical WS-F workstreams (F1-F4) are all completed. The remaining
medium/low-priority workstreams close model fidelity and testing gaps identified
by the [v0.12.2 audits](audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md):

| ID | Focus | Priority |
|----|-------|----------|
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low |
| **WS-F8** | Cleanup (dead code, legacy/dual-queue resolution) | Low |

### Raspberry Pi 5 hardware binding

After the remaining workstreams, the next major milestone is populating the RPi5
platform stubs with hardware-validated contracts:

1. Populate RPi5 runtime contract with hardware-validated predicates.
2. Implement ARMv8 multi-level page table walk as a `VSpaceBackend` instance.
3. Implement GIC-400 interrupt routing with IRQ acknowledgment.
4. Bind timer adapter to ARM Generic Timer (CNTPCT_EL0).
5. Define boot sequence as a verified initial state construction.

### Long-horizon items

- MCS scheduling contexts (budget/period/replenishments).
- Multi-core support (per-core kernel instances).
- Device memory and IOMMU modeling.
- Cryptographic attestation of kernel image.
- Side-channel analysis at hardware binding layer.

## Completed workstream portfolio

| Portfolio | Version | Scope | Workstreams |
|-----------|---------|-------|-------------|
| **Restructuring** | v0.14.5 | Module decomposition: 9 monolithic files (1K-5.8K lines) split into 24 focused submodules via re-export hub pattern. 15 private defs tightened after cross-module audit. 209 Tier 3 anchor checks updated. Zero sorry/axiom | Structural |
| **WS-H13** | v0.14.4 | CSpace/service model enrichment: multi-level CSpace resolution, backing-object verification, `serviceCountBounded` | H13 |
| **WS-H12f** | v0.14.3 | Test harness update & documentation sync: 3 new trace scenarios, fixture update, 9 new Tier 3 anchors | H12f |
| **WS-H12e** | v0.14.2 | Cross-subsystem invariant reconciliation: `coreIpcInvariantBundle` upgraded to `ipcInvariantFull` 3-conjunct, `schedulerInvariantBundleFull` extended to 5-tuple, 8 frame lemmas + 3 compound preservation theorems | H12e |
| **WS-H12d** | v0.14.1 | IPC message payload bounds: `IpcMessage` Array migration, `maxMessageRegisters`(120)/`maxExtraCaps`(3), 4 bounds theorems, `allPendingMessagesBounded` system invariant. Closes A-09 | H12d |
| **WS-H12c** | v0.14.0 | Per-TCB register context with inline context switch: `registerContext` field, `contextMatchesCurrent` invariant, IF projection stripping. Closes H-03 | H12c |
| **WS-H12b** | v0.13.9 | Dequeue-on-dispatch scheduler semantics matching seL4's `switchToThread`/`tcbSchedDequeue`, ~1800 lines re-proved. Closes H-04 | H12b |
| **WS-H12a** | v0.13.8 | Legacy endpoint field & operation removal | H12a |
| **WS-H11** | v0.13.7 | VSpace & architecture enrichment: PagePermissions with W^X enforcement, TLB/cache model, `VSpaceBackend` typeclass, 23 new theorems | H11 |
| **End-to-end audit** | v0.13.6 | Comprehensive codebase audit: zero critical issues, zero sorry/axiom, stale documentation metrics fixed | Audit |
| **WS-H10** | v0.13.6 | Security model foundations: `ObservableState`, BIBA lattice alternatives, `DeclassificationPolicy`, `InformationFlowConfigInvariant` | H10 |
| **WS-H9** | v0.13.4 | Non-interference coverage >80%: 27 new NI theorems, 28-constructor `NonInterferenceStep`, `composedNonInterference_trace`. Closes C-02/A-40 (CRITICAL) | H9 |
| **WS-H8** | v0.13.2 | Enforcement-NI bridge: 5 enforcement soundness meta-theorems, 4 `*Checked` wrappers. Closes A-35/H-07, A-36/A-37/H-11 | H8 |
| **WS-H7** | v0.12.21 | HashMap equality + state-store migration: order-independent `BEq`, closure-to-HashMap migration for 5 state fields | H7 |
| **WS-H6** | v0.13.1 | Scheduler proof completion: `timeSlicePositive` fully proven, EDF domain-aware fix, `schedulerInvariantBundleFull` 5-tuple | H6 |
| **WS-H5** | v0.12.19 | IPC dual-queue structural invariant: `intrusiveQueueWellFormed`, `dualQueueSystemInvariant`, 13 preservation theorems. Closes C-04/A-22..A-24 | H5 |
| **WS-H4** | v0.12.18 | Capability invariant redesign: `capabilityInvariantBundle` 7-tuple with `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity` | H4 |
| **WS-H3** | v0.12.17 | Build/CI infrastructure: `run_check` return value fix (H-12), docs sync CI integration (M-19), Tier 3 `rg` guard (M-20) | H3 |
| **WS-H2** | v0.12.16 | Lifecycle safety guards: childId collision/self-overwrite guards, TCB scheduler cleanup, atomic retype | H2 |
| **WS-H1** | v0.12.16 | IPC call-path semantic fix: `blockedOnCall` state, reply-target scoping, 5-conjunct `ipcSchedulerContractPredicates` | H1 |
| **WS-G** | v0.12.6-v0.12.15 | Kernel performance: all hot paths migrated to O(1) hash-based structures, 14 audit findings resolved | G1-G9 + refinement |
| **WS-F1..F4** | v0.12.2-v0.12.5 | Critical audit remediation: IPC message transfer (14 theorems), untyped memory (watermark tracking), info-flow completeness (15 NI theorems), proof gap closure | F1-F4 |
| **WS-E** | v0.11.0-v0.11.6 | Test/CI hardening, proof quality, kernel hardening, capability/IPC, info-flow enforcement, completeness | E1-E6 |
| **WS-D** | v0.11.0 | Test validity, info-flow enforcement, proof gaps, kernel design | D1-D4 |
| **WS-C** | v0.9.32 | Model structure, documentation, maintainability | C1-C8 |
| **WS-B** | v0.9.0 | Comprehensive audit (2026-02) | B1-B11 |

Prior audits (v0.8.0-v0.9.32), milestone closeouts, and legacy GitBook chapters
are archived in [`docs/dev_history/`](dev_history/README.md).

## Audit plans (canonical sources)

| Plan | Scope |
|------|-------|
| [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md) | WS-H portfolio (v0.12.15 audit findings) |
| [`AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) | WS-F portfolio (v0.12.2 audit findings) |
| [`KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md) | WS-G portfolio (performance optimization) |
| [`KERNEL_PERFORMANCE_AUDIT_v0.12.5.md`](audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md) | Performance audit baseline |
| [`AUDIT_CODEBASE_v0.13.6.md`](audits/AUDIT_CODEBASE_v0.13.6.md) | Latest end-to-end audit |
