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

### WS-L workstream (IPC subsystem audit & remediation)

WS-L is the active workstream, created from a comprehensive end-to-end audit of
the IPC subsystem (9,195 LoC, 12 files). The audit found zero critical issues,
zero sorry/axiom, but identified 3 performance optimization opportunities, 5
proof strengthening opportunities, and 5 test coverage gaps. WS-L also resolves
all deferred WS-I5 items.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-L1** | IPC performance optimization: eliminate redundant TCB lookups in endpointReceiveDual, endpointReply, notificationWait | HIGH — **COMPLETED** (v0.16.9) |
| **WS-L2** | Code quality: HashMap.fold migration — eliminate all `.toList.foldl/foldr` anti-patterns (closes WS-I5/R-17) | MEDIUM — **COMPLETED** (v0.16.10) |
| **WS-L3** | Proof strengthening: enqueue-dequeue round-trip, queue link integrity, ipcState-queue consistency, tail preservation, reply contract preservation | MEDIUM — **COMPLETED** (v0.16.11) |
| **WS-L4** | Test coverage: ReplyRecv positive-path, blocked thread rejection, multi-endpoint interleaving | MEDIUM — **PARTIALLY COMPLETE** |
| **WS-L5** | Documentation: IF readers' guide, fixture update process, metrics automation, full doc sync (closes WS-I5/R-13/R-14/R-18) | LOW — **IN PROGRESS** |

**WS-L1** (v0.16.9): Eliminated 4 redundant TCB lookups on IPC hot paths.
L1-A: changed `endpointQueuePopHead` return type to `(ThreadId × TCB × SystemState)`,
providing pre-dequeue TCB to callers and eliminating redundant `lookupTcb` in
`endpointReceiveDual`. L1-B: added `storeTcbIpcStateAndMessage_fromTcb` with
equivalence theorem, eliminating redundant lookups in `endpointReply` and
`endpointReplyRecv`. L1-C: added `storeTcbIpcState_fromTcb` with equivalence
theorem, eliminating redundant lookup in `notificationWait`. Added
`lookupTcb_preserved_by_storeObject_notification` helper for cross-store TCB
stability. ~18 mechanical pattern-match updates across 6 invariant files. Zero
sorry/axiom; all proofs machine-checked.

**WS-L2** (v0.16.10): Eliminated all 4 `Std.HashMap.toList.foldl/foldr`
anti-patterns across the codebase. L2-A: migrated 3 fold patterns in
`Testing/InvariantChecks.lean` (`cspaceSlotCoherencyChecks`,
`capabilityRightsStructuralChecks`, `cdtChildMapConsistentCheck`) from
`.toList.foldr` to direct `HashMap.fold`. L2-B: migrated `detachCNodeSlots`
in `Kernel/Lifecycle/Operations.lean` from `.toList.foldl` to `HashMap.fold`,
updated 3 preservation proofs (`_objects_eq`, `_lifecycle_eq`, `_scheduler_eq`)
using `Std.HashMap.fold_eq_foldl_toList` bridge lemma. Refined WS-L2 workstream
plan with expanded scope covering all 4 sites (original plan only covered 1).
Zero sorry/axiom; all proofs machine-checked.

**WS-L3** (v0.16.11): Proof strengthening for IPC dual-queue subsystem.
L3-A: enqueue-dequeue round-trip theorem — `endpointQueueEnqueue_empty_sets_head`
(postcondition), `endpointQueueEnqueue_empty_queueNext_none` (TCB state),
`endpointQueueEnqueue_then_popHead_succeeds` (composed round-trip).
L3-B: standalone `tcbQueueLinkIntegrity` preservation for popHead and enqueue
(extracted from bundled `dualQueueSystemInvariant`).
L3-C: `ipcStateQueueConsistent` invariant definition (blocked → endpoint exists)
plus queue-operation preservation (popHead, enqueue). Forward endpoint preservation
helpers (`storeTcbQueueLinks_endpoint_forward`, `endpointQueuePopHead_endpoint_forward`,
`endpointQueueEnqueue_endpoint_forward`).
L3-C3: high-level `ipcStateQueueConsistent` preservation for `endpointSendDual`,
`endpointReceiveDual`, `endpointReply` — plus 5 sub-operation helpers
(`ensureRunnable`, `removeRunnable`, `storeTcbIpcStateAndMessage`,
`storeTcbIpcState`, `storeTcbPendingMessage`).
L3-D: tail consistency for `endpointQueueRemoveDual` — non-tail removal preserves
tail (`_preserves_tail_of_nonTail`), tail removal characterization (`_tail_update`).
L3-E: already resolved (pre-existing in `CallReplyRecv.lean:797`).
22 new theorems, 1 new invariant definition. Zero sorry/axiom; all proofs
machine-checked.

See [`AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md)
for the full workstream plan (5 phases: L1 through L5).

### Remaining WS-H workstreams

WS-H1..H16 are all completed. No remaining WS-H workstreams.

### WS-F workstreams (F1-F8) — ALL COMPLETED

All WS-F workstreams are completed. The v0.12.2 audit remediation portfolio is
100% closed (33/33 findings). See the
[workstream plan](dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) for details.

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
the [workstream plan](dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md) for
full details.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-I1** | Test infrastructure hardening (inter-transition assertions, determinism promotion, scenario ID traceability) | HIGH — **COMPLETED** (v0.15.0) |
| **WS-I2** | Proof & hygiene strengthening (semantic L-08 validation, Tier 3 correctness anchors, VSpace memory ownership projection) | HIGH — **COMPLETED** (v0.15.1) |
| **WS-I3** | Operations coverage expansion (multi-operation chains, scheduler stress, declassification checks) | MEDIUM — **COMPLETED** (v0.15.2) |
| **WS-I4** | Subsystem coverage expansion (VSpace multi-ASID, IPC interleaving, lifecycle cascading revoke chains) | LOW — **COMPLETED** (v0.15.3) |
| **WS-I5** | Documentation and code-quality polish (remaining low-priority recommendations) | LOW — **SUPERSEDED by WS-L** (all R-12..R-18 items resolved within WS-L) |

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

See [`AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md)
for the full workstream plan (6 phases: J1-A through J1-F).

| ID | Focus | Priority |
|----|-------|----------|
| **WS-J1** | Replace `abbrev Nat` register types with typed wrappers, add syscall argument decode layer bridging machine registers to typed kernel operations, wrap `CdtNodeId`, prove decode correctness and NI | HIGH — **J1-A COMPLETED** (v0.15.4), **J1-B COMPLETED** (v0.15.5), **J1-C COMPLETED** (v0.15.6; audit refinements v0.15.7), **J1-D COMPLETED** (v0.15.8), **J1-E COMPLETED** (v0.15.9), **J1-F COMPLETED** (v0.15.10) — **PORTFOLIO COMPLETE** |

### WS-K workstream (full syscall dispatch completion)

WS-K completed the syscall surface that WS-J1 established. WS-J1 built the
typed register decode layer and 13-case dispatch skeleton, but 7 syscalls
returned `.illegalState` (CSpace mint/copy/move/delete, lifecycle retype,
VSpace map/unmap), 2 service syscalls used `(fun _ => true)` policy stubs,
and IPC messages carried empty register payloads. WS-K addressed all of these:

1. Extending `SyscallDecodeResult` with message register values (x2–x5).
2. Per-syscall argument structures with total decode functions.
3. Full dispatch for all 13 syscalls (zero `.illegalState` stubs).
4. Configuration-sourced service policy replacing permissive stubs.
5. IPC message body population from decoded register contents.
6. Round-trip proofs, NI integration, and deferred proof completion.

See [`AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md)
for the full workstream plan (8 phases: K-A through K-H).

| ID | Focus | Priority |
|----|-------|----------|
| **WS-K** | Extend `SyscallDecodeResult` with msgRegs, implement per-syscall argument decode, wire all 13 syscalls through dispatch, replace service policy stubs, populate IPC message bodies, prove round-trip correctness and NI, comprehensive testing and documentation | CRITICAL — **K-A COMPLETED** (v0.16.0), **K-B COMPLETED** (v0.16.1), **K-C COMPLETED** (v0.16.2), **K-D COMPLETED** (v0.16.3), **K-E COMPLETED** (v0.16.4), **K-F COMPLETED** (v0.16.5), **K-G COMPLETED** (v0.16.7), **K-H COMPLETED** (v0.16.8) — **PORTFOLIO COMPLETE** |

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
| **WS-K-H** | v0.16.8 | Documentation sync and workstream closeout: updated `WORKSTREAM_HISTORY.md` with WS-K portfolio completion (K-A through K-H, v0.16.0–v0.16.8); updated `SELE4N_SPEC.md` current state snapshot with v0.16.8 version, updated metrics (37,139 production LoC, 4,037 test LoC, 1,198 proved declarations), and WS-K portfolio complete status; updated `DEVELOPMENT.md` active workstream to show WS-K complete, next priority as RPi5 hardware binding; updated `CLAIM_EVIDENCE_INDEX.md` WS-K claim row with comprehensive K-A through K-H deliverables and evidence commands; updated GitBook chapters: `03-architecture-and-module-map.md` (added `SyscallArgDecode.lean` module entry with 7 structures, 7 decode functions, 7 encode functions, 14 theorems), `04-project-design-deep-dive.md` (added section 1.7 documenting two-layer syscall argument decode architecture), `05-specification-and-roadmap.md` (version and roadmap update, WS-K complete, RPi5 next), `12-proof-and-invariant-map.md` (added WS-K proof surface: layer-2 round-trip proofs, delegation theorems, NI coverage extension to 34 constructors); regenerated `docs/codebase_map.json`; synced `README.md` metrics from `readme_sync`; bumped `lakefile.toml` version to 0.16.8; refined WS-K-H workstream plan from 9 flat tasks into 13 granular subtasks (K-H.1 through K-H.13) with dependency ordering, per-file change specifications, and explicit acceptance criteria; updated completion evidence checklist from 5 to 13 K-H items. Zero sorry/axiom. Closes WS-K Phase H. WS-K portfolio fully complete. | K-H |
| **WS-K-G** | v0.16.7 | Lifecycle NI proof completion and deferred proof resolution: added `cspaceRevoke_preserves_projection` standalone theorem in `InformationFlow/Invariant/Operations.lean` extracted from inline proof for compositional reuse; added `lifecycleRevokeDeleteRetype_preserves_projection` theorem chaining projection preservation across `cspaceRevoke`, `cspaceDeleteSlot`, and `lifecycleRetypeObject` sub-operations; added `lifecycleRevokeDeleteRetype_preserves_lowEquivalent` two-run NI theorem completing the previously deferred `lifecycleRevokeDeleteRetype` NI proof using compositional projection-preservation reasoning; extended `NonInterferenceStep` inductive with `lifecycleRevokeDeleteRetype` constructor (34 constructors total, up from 33); updated `step_preserves_projection` with the new constructor case; updated `syscallNI_coverage_witness` documentation to reflect 34-constructor exhaustive match. Zero sorry/axiom. Closes WS-K Phase G | K-G |
| **WS-K-F** | v0.16.5 | Proofs: round-trip, preservation, and NI integration: added 7 encode functions in `SyscallArgDecode.lean` (`encodeCSpaceMintArgs` through `encodeVSpaceUnmapArgs`) completing encode/decode symmetry for all layer-2 structures; proved 7 round-trip theorems via structure eta reduction (`rcases + rfl`) with `decode_layer2_roundtrip_all` composed conjunction; added `extractMessageRegisters_roundtrip` in `RegisterDecode.lean` closing the layer-1 extraction round-trip gap; added `dispatchWithCap_layer2_decode_pure` proving decode functions depend only on `msgRegs` (two results with same `msgRegs` produce identical decode) and `dispatchWithCap_preservation_composition_witness` structural preservation theorem in `API.lean`; added `retypeFromUntyped_preserves_lowEquivalent` NI theorem completing the last deferred NI proof via two-stage `storeObject_at_unobservable_preserves_lowEquivalent` composition; added `syscallNI_coverage_witness` in `Composition.lean` witnessing decode-error NI step availability, step→trace composition, and `step_preserves_projection` totality over all 33 constructors; refined WS-K-F plan into 6 granular sub-phases (K-F1 through K-F6). Zero sorry/axiom. Closes WS-K Phase F | K-F |
| **WS-K-E** | v0.16.4 | Service policy and IPC message population: added `ServiceConfig` structure with `Inhabited` default (permissive `fun _ => true`) in `Model/State.lean`; extended `SystemState` with `serviceConfig : ServiceConfig := default` field; replaced `(fun _ => true)` service policy stubs in `dispatchWithCap` with `st.serviceConfig.allowStart`/`st.serviceConfig.allowStop` — service operations now read policy from system state configuration; added `extractMessageRegisters` in `RegisterDecode.lean` that converts `Array RegValue` → `Array Nat` (matching `IpcMessage.registers : Array Nat`) with triple bound (`info.length`, `maxMessageRegisters`, `msgRegs.size`); updated `.send`/`.call`/`.reply` IPC dispatch arms to populate message bodies from decoded message registers instead of empty arrays; proved `extractMessageRegisters_length` (result size ≤ `maxMessageRegisters`), `extractMessageRegisters_ipc_bounded` (constructed `IpcMessage` satisfies `bounded`), `extractMessageRegisters_deterministic`; 5 delegation theorems (`dispatchWithCap_serviceStart_uses_config`, `dispatchWithCap_serviceStop_uses_config`, `dispatchWithCap_send_populates_msg`, `dispatchWithCap_call_populates_msg`, `dispatchWithCap_reply_populates_msg`); all existing soundness theorems compile unchanged; `BootstrapBuilder` extended with `serviceConfig` field and `withServiceConfig` combinator; 11 Tier 3 invariant surface anchors (5 `rg` + 11 `#check`). Zero `(fun _ => true)` stubs remain. Zero `registers := #[]` in IPC dispatch. Zero sorry/axiom. Closes WS-K Phase E | K-E |
| **WS-K-D** | v0.16.3 | Lifecycle and VSpace syscall dispatch: wired all 3 remaining syscall stubs (`lifecycleRetype`, `vspaceMap`, `vspaceUnmap`) through `dispatchWithCap` — zero `.illegalState` stubs remain, all 13 syscalls fully dispatch; added `objectOfTypeTag` total type-tag decoder with dedicated `invalidTypeTag` error variant, `lifecycleRetypeDirect` pre-resolved authority companion, `PagePermissions.ofNat`/`toNat` bitfield codec with round-trip theorem; 3 delegation theorems, 3 error-decomposition theorems, equivalence theorem linking `lifecycleRetypeDirect` to `lifecycleRetypeObject`; Tier 3 anchors. Zero sorry/axiom. Closes WS-K Phase D | K-D |
| **WS-K-C** | v0.16.2 | CSpace syscall dispatch: wired all 4 CSpace syscalls (`cspaceMint`, `cspaceCopy`, `cspaceMove`, `cspaceDelete`) through `dispatchWithCap` using decoded message register arguments from `SyscallArgDecode`; changed `dispatchWithCap` signature from `SyscallId` to `SyscallDecodeResult`; `cspaceMint` dispatch decodes srcSlot, dstSlot, rights bitmask, badge from 4 message registers with badge=0→none seL4 convention; `cspaceCopy`/`cspaceMove` dispatch decodes srcSlot and dstSlot from 2 message registers; `cspaceDelete` dispatch decodes targetSlot from 1 message register; 4 delegation theorems proved (`dispatchWithCap_cspaceMint_delegates`, `dispatchWithCap_cspaceCopy_delegates`, `dispatchWithCap_cspaceMove_delegates`, `dispatchWithCap_cspaceDelete_delegates`); all 3 existing soundness theorems compile unchanged; refined WS-K-C workstream plan with 8 detailed subtasks (K-C.1–K-C.8). Zero sorry/axiom. Closes WS-K Phase C | K-C |
| **WS-K-B** | v0.16.1 | Per-syscall argument decode layer: added `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` implementing layer 2 of the two-layer syscall decode architecture; 7 typed argument structures (`CSpaceMintArgs`, `CSpaceCopyArgs`, `CSpaceMoveArgs`, `CSpaceDeleteArgs`, `LifecycleRetypeArgs`, `VSpaceMapArgs`, `VSpaceUnmapArgs`) with `DecidableEq` and `Repr`; shared `requireMsgReg` bounds-checked indexing helper; 7 total decode functions with explicit `Except KernelError` error handling via `do` notation; 7 determinism theorems (trivial `rfl`); 7 error-exclusivity theorems (`decode fails ↔ msgRegs.size < N`) using `by_cases`/`dif_pos`/`nomatch` proof strategy; helper theorems `requireMsgReg_unfold_ok` and `requireMsgReg_unfold_err` for rewriting `dite` in mpr direction; integrated into `API.lean` import graph. Zero sorry/axiom. Closes WS-K Phase B | K-B |
| **WS-K-A** | v0.16.0 | Message register extraction into SyscallDecodeResult: added `msgRegs : Array RegValue := #[]` field to `SyscallDecodeResult` in `Model/Object/Types.lean`; updated `decodeSyscallArgs` in `RegisterDecode.lean` to validate and read message registers (x2–x5) in single pass via `Array.mapM`; added `encodeMsgRegs` identity encoder; proved `decodeMsgRegs_length` (output size = layout size) via novel `list_mapM_except_length`/`array_mapM_except_size` helpers; proved `decodeMsgRegs_roundtrip`; extended `decode_components_roundtrip` to 4-conjunct; NegativeStateSuite J1-NEG-17 verifies `msgRegs.size = 4`; RDT-002 trace includes msgRegs count; 4 new Tier 3 anchors; WS-K-A plan refined into 8 detailed subtasks. Zero sorry/axiom. Closes WS-K Phase A | K-A |
| **WS-J1-F** | v0.15.10 | CdtNodeId cleanup and documentation sync: replaced `abbrev CdtNodeId := Nat` with `structure CdtNodeId where val : Nat` in `Model/Object/Structures.lean`; added full instance suite (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`, `LawfulBEq`, `Repr`, `ToString`, `Inhabited`, `ofNat`/`toNat`); fixed downstream compilation (`SystemState` defaults, monotone allocator, test literals); all documentation synchronized across canonical sources and GitBook chapters; codebase map regenerated. All 16 kernel identifiers are now typed wrappers. Zero sorry/axiom. Closes WS-J1 Phase F. **WS-J1 portfolio fully completed** | J1-F |
| **WS-J1-E** | v0.15.9 | Testing and trace evidence: 18 negative decode tests in `NegativeStateSuite.lean`; 5 register-decode trace scenarios (RDT-002 through RDT-010) in `MainTraceHarness.lean`; 2 operation-chain tests in `OperationChainSuite.lean`; fixture and scenario registry updates; 13 Tier 3 invariant surface anchors for RegisterDecode definitions and theorems. Zero sorry/axiom. Closes WS-J1 Phase E | J1-E |
| **WS-J1-D** | v0.15.8 | Invariant and information-flow integration: `registerDecodeConsistent` predicate bridging decode layer to kernel object store validity (implied by `schedulerInvariantBundleFull` via `currentThreadValid`), `syscallEntry_preserves_proofLayerInvariantBundle` compositional preservation theorem for success and error paths, `syscallEntry_error_preserves_proofLayerInvariantBundle` trivial error-path preservation, `decodeSyscallArgs_preserves_lowEquivalent` NI theorem for pure decode, `syscallEntry_preserves_projection` projection-preservation theorem, two new `NonInterferenceStep` constructors (`syscallDecodeError` for failed decode/state unchanged, `syscallDispatchHigh` for high-domain dispatch with projection preservation), `step_preserves_projection` extended with new constructor cases, `syscallEntry_error_yields_NI_step` and `syscallEntry_success_yields_NI_step` bridge theorems from API to NI composition framework. Default-state, timer, and register-write preservation theorems for `registerDecodeConsistent`. Tier 3 anchor entries for all new definitions and theorems (13 grep anchors + 7 `#check` anchors). Zero sorry/axiom. Closes WS-J1 Phase D | J1-D |
| **WS-J1-C** | v0.15.6; refinements v0.15.7 | Syscall entry point and dispatch: `syscallEntry` top-level user-space entry point reading current thread's register file and dispatching via capability-gated `syscallInvoke`, `lookupThreadRegisterContext` for TCB register context extraction, `dispatchSyscall` routing decoded arguments through `SyscallGate` to internal kernel operations, `dispatchWithCap` per-syscall routing for all 13 syscalls (IPC send/receive/call/reply, CSpace mint/copy/move/delete, lifecycle retype, VSpace map/unmap, service start/stop), `syscallRequiredRight` total right mapping, `MachineConfig.registerCount` promoted to configurable field (default 32). Audit refinements (v0.15.7): CSpace/lifecycle/VSpace dispatch returns `illegalState` for MR-dependent ops, `syscallEntry` accepts `regCount` parameter, `syscallEntry_implies_capability_held` strengthened to full capability-resolution chain. Soundness theorems: `syscallEntry_requires_valid_decode`, `syscallEntry_implies_capability_held`, `dispatchSyscall_requires_right`, `lookupThreadRegisterContext_state_unchanged`, `syscallRequiredRight_total`. Zero sorry/axiom. Closes WS-J1 Phase C | J1-C |
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
| [`AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md) | **WS-L** IPC subsystem audit & remediation (5 phases) — **active** |
| [`AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md) | WS-K full syscall dispatch completion (8 phases) — completed |
| [`AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md) | WS-J1 register-indexed authoritative namespaces (6 phases) — completed |
| [`AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md) | WS-I portfolio (v0.14.9 improvement recommendations) — completed |
| [`AUDIT_CODEBASE_v0.13.6.md`](dev_history/audits/AUDIT_CODEBASE_v0.13.6.md) | End-to-end audit (v0.13.6) — completed |
| [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md) | WS-H portfolio (v0.12.15 audit findings) — completed |
| [`KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md) | WS-G portfolio (performance optimization) — completed |
| [`AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) | WS-F portfolio (v0.12.2 audit findings) — completed |
