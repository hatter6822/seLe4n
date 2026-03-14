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

### Remaining WS-H workstreams

WS-H1..H16 are all completed. No remaining WS-H workstreams.

### WS-F workstreams (F1-F8) — ALL COMPLETED

All WS-F workstreams are completed. The v0.12.2 audit remediation portfolio is
100% closed (33/33 findings). See the
[workstream plan](audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) for details.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-F5** | Model fidelity (word-bounded badge, order-independent rights, deferred ops) | Medium — **COMPLETED** (v0.14.9) |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium — **COMPLETED** |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low — **COMPLETED** |
| **WS-F8** | Cleanup (dead code, dead type constructors, extension labeling) | Low — **COMPLETED** |

### WS-I workstreams (I1-I5) — Improvement recommendations from v0.14.9 audit

The v0.14.9 comprehensive codebase audit identified 18 non-blocking improvement
recommendations across testing, proof quality, documentation, code quality, and
coverage expansion. These are organized into 5 workstreams across 3 phases. See
the [workstream plan](audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md) for
full details.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-I1** | Test infrastructure hardening (inter-transition assertions, determinism promotion, scenario ID traceability) | HIGH — **COMPLETED** (v0.15.0) |
| **WS-I2** | Proof & hygiene strengthening (semantic L-08 validation, Tier 3 correctness anchors, VSpace memory ownership projection) | HIGH — **COMPLETED** (v0.15.1) |
| **WS-I3** | Operations coverage expansion (multi-operation chains, scheduler stress, declassification checks) | MEDIUM — **COMPLETED** (v0.15.2) |
| **WS-I4** | Subsystem coverage expansion (VSpace multi-ASID, IPC interleaving, lifecycle cascading revoke chains) | LOW — **COMPLETED** (v0.15.3) |
| **WS-I5** | Documentation and code-quality polish (remaining low-priority recommendations) | LOW — pending |

### WS-J1 workstream (register-indexed authoritative namespaces)

WS-J1 supersedes the WS-I5 Part A documentation-only treatment of
`RegName`/`RegValue`. A comprehensive audit revealed that bare `Nat`
abbreviations are insufficient: the syscall API bypasses the machine register
file entirely, omitting the decode path where untrusted user-space register
values become trusted kernel references. WS-J1 addresses this by:

1. Replacing `RegName`/`RegValue` with typed wrapper structures.
2. Introducing a `RegisterDecode.lean` module with total, deterministic decode
   functions from raw register words to typed kernel identifiers.
3. Adding `syscallEntry` as a register-sourced syscall dispatch path.
4. Wrapping `CdtNodeId` (secondary bare-Nat alias) for consistency.
5. Proving decode correctness, invariant preservation, and NI properties.

See [`AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md)
for the full workstream plan (6 phases: J1-A through J1-F).

| ID | Focus | Priority |
|----|-------|----------|
| **WS-J1** | Replace `abbrev Nat` register types with typed wrappers, add syscall argument decode layer bridging machine registers to typed kernel operations, wrap `CdtNodeId`, prove decode correctness and NI | HIGH — **J1-A COMPLETED** (v0.15.4), **J1-B COMPLETED** (v0.15.5), **J1-C COMPLETED** (v0.15.6), J1-D..F pending |

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
| **WS-J1-C** | v0.15.6 | Syscall entry point and dispatch: `syscallEntry` top-level user-space entry point reading current thread's register file and dispatching via capability-gated `syscallInvoke`, `lookupThreadRegisterContext` for TCB register context extraction, `dispatchSyscall` routing decoded arguments through `SyscallGate` to internal kernel operations, `dispatchWithCap` per-syscall routing for all 13 syscalls (IPC send/receive/call/reply, CSpace mint/copy/move/delete, lifecycle retype, VSpace map/unmap, service start/stop), `syscallRequiredRight` total right mapping, `MachineConfig.registerCount` promoted to configurable field (default 32). Soundness theorems: `syscallEntry_requires_valid_decode`, `syscallEntry_implies_capability_held`, `dispatchSyscall_requires_right`, `lookupThreadRegisterContext_state_unchanged`, `syscallRequiredRight_total`. Zero sorry/axiom. Closes WS-J1 Phase C | J1-C |
| **WS-J1-B** | v0.15.5 | Register decode layer: `SyscallId` inductive (13 modeled syscalls with injective `toNat`/total `ofNat?`, round-trip and injectivity theorems), `MessageInfo` structure (seL4 message-info word bit-field layout with `encode`/`decode`), `SyscallDecodeResult` (typed decode output), total deterministic decode functions (`decodeCapPtr`, `decodeMsgInfo`, `decodeSyscallId`, `validateRegBound`, `decodeSyscallArgs`) in new `RegisterDecode.lean` module, `SyscallRegisterLayout` with `arm64DefaultLayout` (x0–x7 convention), `MachineConfig.registerCount`, 3 new `KernelError` variants (`invalidRegister`, `invalidSyscallNumber`, `invalidMessageInfo`), round-trip lemmas (`decodeCapPtr_roundtrip`, `decodeSyscallId_roundtrip`), determinism theorem, error exclusivity theorems, universal CPtr success theorem. Self-contained module with no kernel subsystem imports. Zero sorry/axiom. Closes WS-J1 Phase B | J1-B |
| **WS-J1-A** | v0.15.4 | Typed register wrappers: replaced `abbrev RegName := Nat` and `abbrev RegValue := Nat` with typed wrapper structures (`structure RegName where val : Nat` / `structure RegValue where val : Nat`) in `Machine.lean`; added full instance suites (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`, `LawfulBEq`, `Repr`, `ToString`, `ofNat`/`toNat`, roundtrip/injectivity proofs); updated `RegisterFile.gpr` type signature from `Nat → Nat` to `RegName → RegValue`; re-proved all 10 existing machine lemmas; fixed all downstream compilation (Architecture adapter/invariant, Platform Sim/RPi5 proof hooks, Testing trace harness); zero sorry/axiom; zero behavior change. Closes WS-J1 Phase A | J1-A |
| **WS-I1** | v0.15.0 | Critical testing infrastructure: 17 inter-transition invariant assertions across all 13 trace functions (R-01), mandatory Tier 2 determinism validation via `test_tier2_determinism.sh` (R-02), scenario ID traceability with 121 tagged trace lines in pipe-delimited format, scenario registry YAML with Tier 0 validation (R-03). Zero sorry/axiom. Closes R-01/R-02/R-03 | I1 |
| **WS-F8** | v0.14.9 | Cleanup: removed dead `ServiceStatus.failed`/`isolated` constructors (D1), labeled Service subsystem as seLe4n extension with module docstrings (D2/MED-17), closed F-14 (endpointInvariant already removed in WS-H12a), closed F-01 (legacy endpoint fields already removed in WS-H12a), closed MED-04 (domain lattice alive and exercised, finding misidentified). Completes 100% of v0.12.2 audit findings (33/33). Closes MED-04/MED-17/F-01/F-14/F-19 | F8 |
| **WS-F5** | v0.14.9 | Model fidelity: word-bounded `Badge` with `ofNatMasked`/`bor`/validity theorems (F5-D1/CRIT-06), order-independent `AccessRightSet` bitmask replacing list-based rights (F5-D2/HIGH-04), deferred operations documented with rationale (F5-D3/MED-03), `badgeWellFormed` invariant with `notificationBadgesWellFormed`/`capabilityBadgesWellFormed` predicates and preservation proofs for `notificationSignal`/`notificationWait`/`cspaceMint`/`cspaceMutate`. Closes CRIT-06/HIGH-04/MED-03 | F5 |
| **WS-H16** | v0.14.8 | Testing, documentation & cleanup: 10 lifecycle negative tests (M-18), 13 semantic Tier 3 assertions (A-43), `objectIndexLive` liveness invariant with preservation proof (A-13), `runQueueThreadPriorityConsistent` predicate with default theorem (A-19), O(1) membership audit confirmation (A-18), documentation metrics sync (M-21/A-45). Closes M-18/A-43/A-13/A-18/A-19/M-21/A-45 | H16 |
| **WS-H15** | v0.14.7 | Platform & API hardening: InterruptBoundaryContract decidability + consistency theorems (H15a), RPi5 MMIO disjointness/boot contract hardening (H15b), syscall capability-checking wrappers with 3 soundness theorems and 13 `api*` entry points (H15c), generic timer-invariant preservation + concrete `AdapterProofHooks` for Sim and RPi5 restrictive contracts with 6 end-to-end theorems (H15d), 31 Tier 3 anchors + 5 trace scenarios + 6 negative tests (H15e). Closes A-33/A-41/A-42/M-13 | H15a-e |
| **WS-H14** | v0.14.6 | Type safety & Prelude foundations: `EquivBEq`/`LawfulBEq` for 14 identifier types, `LawfulMonad` for `KernelM`, `isPowerOfTwo` correctness proof, identifier roundtrip/injectivity theorems, `OfNat` instance removal (type-safety enforcement), sentinel predicate completion. Closes A-01/A-02/A-03/A-04/A-06/M-09/M-10/M-11 | H14 |
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
| [`AUDIT_CODEBASE_v0.13.6.md`](audits/AUDIT_CODEBASE_v0.13.6.md) | Prior end-to-end audit (v0.13.6) |
| [`AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md) | WS-I portfolio (v0.14.9 improvement recommendations) |
| [`AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md) | WS-J1 register-indexed authoritative namespaces (6 phases) |
