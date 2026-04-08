# Specification & Roadmap

This chapter summarizes the project specification. For the normative document:
[`docs/spec/SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md).

## Project identity

seLe4n is a **production-oriented microkernel** written in Lean 4 with
machine-checked proofs, improving on seL4 architecture. First hardware target:
**Raspberry Pi 5** (ARM64).

## Current state

| Attribute | Value |
|-----------|-------|
| Version | `0.25.25` |
| Lean toolchain | `v4.28.0` |
| Production LoC | 87,043 across 133 Lean files |
| Test LoC | 11,359 across 16 suites |
| Proved declarations | 2,581 theorem/lemma declarations (zero sorry/axiom) |
| Latest audit | [`AUDIT_COMPREHENSIVE_v0.23.21`](../dev_history/AUDIT_COMPREHENSIVE_v0.23.21_LEAN_RUST_KERNEL.md) — full-kernel Lean + Rust audit (0 CRIT, 5 HIGH, 8 MED, 30 LOW) |
| Active workstream | **WS-AF Phase AF4 COMPLETE** (v0.25.25). Information Flow, Cross-Subsystem & SchedContext — all `native_decide` eliminated (TCB reduction), fuel-sufficiency documentation, deployment cross-references. Prior: AF3 (v0.25.24), AF2 (v0.25.23), AF1 (v0.25.22), WS-AE (v0.25.15–v0.25.21), WS-AD (v0.25.11–v0.25.14), WS-AC (v0.25.3–v0.25.10), WS-B through WS-AB (v0.9.0–v0.25.5). **Next: Raspberry Pi 5 hardware binding.** |
| Workstream history | [`docs/WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md) |
| Metrics source of truth | [`docs/codebase_map.json`](../../docs/codebase_map.json) (`readme_sync` key) |

## Milestone history

Bootstrap → M1 (scheduler) → M2 (capability) → M3/M3.5 (IPC) → M4-A/M4-B
(lifecycle) → M5 (service graph) → M6 (architecture boundary) → M7 (audit
remediation) → WS-B..F1-F4 (5 audit portfolios, all completed) → WS-G
(performance optimization, completed) → WS-H1 (IPC call-path semantic fix, completed) →
WS-H2 (lifecycle safety guards, completed) → WS-H3 (build/CI infrastructure, completed) →
WS-H4 (capability invariant redesign, completed) → WS-H5 (IPC dual-queue structural
invariant, completed) → WS-H6 (scheduler proof completion, completed) →
WS-H8 (enforcement-NI bridge & missing wrappers, completed) →
WS-H9 (non-interference coverage extension, completed) →
WS-H7/H8/H9 gap closure (comprehensive audit, v0.13.5) →
WS-H10 (security model foundations, v0.13.6) →
End-to-end codebase audit (v0.13.6) →
WS-H11 (VSpace & architecture enrichment, v0.13.7) →
WS-H12a (legacy endpoint removal, v0.13.8) →
WS-H12b (dequeue-on-dispatch scheduler semantics, v0.13.9) →
WS-H12c (per-TCB register context, v0.14.0) →
WS-H12d (IPC message payload bounds, v0.14.1) →
WS-H12e (cross-subsystem invariant reconciliation, v0.14.2) →
WS-H12f (test harness & docs sync, v0.14.3) →
WS-H13 (CSpace/service enrichment, v0.14.4) →
Module restructuring (24 focused submodules, v0.14.5) →
WS-H14 (type safety & Prelude foundations, v0.14.6) →
WS-H15 (platform/API hardening, v0.14.7) →
WS-H16 (testing/documentation cleanup, v0.14.8) →
WS-F5..F8 (model fidelity, invariant quality, testing, cleanup, v0.14.9) →
WS-I1 (critical testing infrastructure, v0.15.0) →
WS-J1-A (typed register wrappers, v0.15.4) →
WS-J1-B (register decode layer, v0.15.5) →
WS-J1-C (syscall entry point and dispatch, v0.15.6; audit refinements, v0.15.7) →
WS-J1-D (invariant/NI integration, v0.15.8) →
WS-J1-E (testing and trace evidence, v0.15.9) →
WS-J1-F (CdtNodeId cleanup + documentation sync, v0.15.10) →
**WS-K (full syscall dispatch completion, v0.16.0–v0.16.8) — PORTFOLIO COMPLETE.** →
WS-L1 (IPC performance optimization, v0.16.9) →
WS-L2 (code quality — HashMap.fold migration, v0.16.10) →
WS-L3 (proof strengthening — 22 theorems, v0.16.11) →
WS-L4 (test coverage expansion, v0.16.12) →
**WS-L5 (documentation & closeout, v0.16.13) — WS-L PORTFOLIO COMPLETE.** →
**WS-M1 (proof strengthening, v0.16.14) — COMPLETED.** →
**WS-M2 (performance optimization, v0.16.15) — COMPLETED.** →
**WS-M3 (IPC cap transfer, v0.16.17) — COMPLETED.** →
**WS-M4 (test coverage expansion, v0.16.18) — COMPLETED.** →
**WS-M5 (streaming BFS optimization, v0.16.19–v0.17.0) — COMPLETED. WS-M PORTFOLIO COMPLETE.** →
**WS-N (Robin Hood hashing, v0.17.0–v0.17.5) — PORTFOLIO COMPLETE.** →
**WS-Q1 (Service interface simplification, v0.17.7) — COMPLETED.** →
**WS-Q2 (Universal RHTable migration, v0.17.8) — COMPLETED.** →
**WS-Q3 (IntermediateState formalization, v0.17.9) — COMPLETED.** →
**WS-Q4 (CNode radix tree, v0.17.10) — COMPLETED.** →
**WS-Q5 (FrozenSystemState + freeze, v0.17.11) — COMPLETED.** →
**WS-Q6..Q9 (Freeze proofs, frozen ops, Rust wrappers, integration, v0.17.12–v0.17.14) — WS-Q PORTFOLIO COMPLETE.** →
**WS-R (Comprehensive audit remediation, v0.18.0–v0.18.7) — PORTFOLIO COMPLETE.** →
**WS-S (Pre-benchmark strengthening, v0.19.0–v0.19.6) — PORTFOLIO COMPLETE.** →
**WS-T (Deep-dive audit remediation, v0.20.0–v0.20.7) — PORTFOLIO COMPLETE.** →
**WS-U (Comprehensive audit remediation, v0.21.0–v0.21.7) — PORTFOLIO COMPLETE.** →
**WS-V (Deep audit remediation, v0.22.0–v0.22.10) — PORTFOLIO COMPLETE.** →
**WS-W (Pre-release audit remediation, v0.22.11–v0.22.17) — PORTFOLIO COMPLETE.** →
**WS-X (Documentation & hardening, v0.22.18–v0.22.22) — PORTFOLIO COMPLETE.** →
**WS-Y (Cross-subsystem hardening, v0.22.23–v0.22.26) — PORTFOLIO COMPLETE.** →
**WS-Z (Composable performance objects, v0.23.0–v0.23.20) — PORTFOLIO COMPLETE.** →
**WS-AA (Comprehensive audit remediation, v0.23.21) — PORTFOLIO COMPLETE.** →
**WS-AB (Deferred operations & liveness completion, v0.24.0–v0.25.5) — PORTFOLIO COMPLETE.**

## Completed: WS-AB Deferred Operations & Liveness Completion (v0.24.0–v0.25.5, PORTFOLIO COMPLETE)

6 phases (D1–D6) completing all seL4 deferred operations and formalizing liveness
guarantees that depend on the SchedContext infrastructure from WS-Z.

- **D1** (v0.24.0–v0.24.2): Thread suspension/resumption — `suspendThread`/`resumeThread` with run-queue cleanup, transport lemmas.
- **D2** (v0.24.3–v0.24.5): Priority management — `setPriorityOp`/`setMCPriorityOp` with MCP authority validation, run-queue migration, `authority_nonEscalation`.
- **D3** (v0.24.6–v0.24.7): IPC buffer configuration — `setIPCBufferOp` with VSpace bounds checking.
- **D4** (v0.24.8–v0.25.0): Priority Inheritance Protocol — `BlockingGraph`, `blockingChainAcyclic`, `blockingDepthBound`, transitive propagation, `wcrt_parametric_bound`.
- **D5** (v0.25.0–v0.25.1): Bounded Latency Theorem — WCRT = D×L_max + N×(B+P) across 7 liveness modules (TimerTick, Replenishment, Yield, BandExhaustion, DomainRotation, WCRT).
- **D6** (v0.25.2–v0.25.5): API surface integration — 5 deferred operations in kernel API, enforcement boundary 25→30, Rust ABI sync (SyscallId 25, KernelError 44).

Plan: [`WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md`](../dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md).

## Completed: WS-Z Composable Performance Objects (v0.23.0–v0.23.20, PORTFOLIO COMPLETE)

9 phases (Z1–Z9) delivering the complete SchedContext subsystem — CBS budget
engine, replenishment queue, scheduler integration, capability-controlled thread
binding, timeout endpoints, SchedContext donation for passive servers, full
API surface with frozen operations, and cross-subsystem invariant composition.

- **Z1** (v0.23.0): SchedContext type foundation — SchedContextId, Budget/Period types, 7th KernelObject variant, 24-file ripple fix.
- **Z2** (v0.23.1–v0.23.4): CBS budget engine — consumeBudget, replenish, admission control, 16 preservation theorems, `cbs_bandwidth_bounded`.
- **Z3** (v0.23.5–v0.23.6): Replenishment queue — sorted insert, popDue, remove, 13 theorems.
- **Z4** (v0.23.7–v0.23.8): Scheduler integration — `schedulerInvariantBundleExtended` (15-tuple), 6 new invariants.
- **Z5** (v0.23.9–v0.23.11): Capability-controlled binding — 3 new SyscallId variants, configure/bind/unbind/yieldTo, 7 preservation theorems.
- **Z6** (v0.23.12–v0.23.14): Timeout endpoints — budget-driven IPC timeout, `endpointQueueRemove`, `blockedThreadTimeoutConsistent` invariant.
- **Z7** (v0.23.15–v0.23.16): SchedContext donation — `donateSchedContext`, donation-aware IPC wrappers, 4 new invariants, `ipcInvariantFull` extended to 14 conjuncts.
- **Z8** (v0.23.17–v0.23.18): API surface — 3 error-exclusivity theorems, 4 frozen operations, enforcement boundary 22→25.
- **Z9** (v0.23.20): Invariant composition — `crossSubsystemInvariant` 5→8 predicates, `proofLayerInvariantBundle` 9→10 conjuncts, 14 disjointness witnesses, 3 frame lemmas, boot/operation preservation.

Plan: [`WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md`](../dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md).

## Completed: WS-V Phase V1 Rust ABI Hardening (v0.22.0)

12 sub-tasks hardening the Rust ABI boundary: u64→u32 truncation guard in
`decode_response` (H-RS-1), `LifecycleRetypeArgs.new_type` changed to validated
`TypeTag` (M-RS-1), 13 `unwrap()` calls replaced with compile-time validated
`new_const()` (M-RS-2), error variants corrected for `IpcBuffer::get_mr` and
`CSpaceMintArgs::decode` (M-RS-3/M-RS-4), W^X `checked_bitor` for `PagePerms`
(M-RS-5), validation methods for `Slot`/`DomainId`/`Priority` (M-RS-7),
`ServiceRegisterArgs` bounds validation (L-RS-2), 10 new conformance tests.
157 Rust tests pass, zero warnings.

## Completed: WS-U Phase U8 (v0.21.7)

Documentation & Closure — 8 sub-tasks (U8-A through U8-H). WS-U PORTFOLIO COMPLETE.

## Completed: WS-U Phase U7 Dead Code & Proof Hygiene (v0.21.6)

Dead code removal, proof hygiene improvements, BEq symmetry fix, native_decide migration, and builder/frozen commutativity proofs.

## Completed: WS-U Phase U6 Architecture & Platform Fidelity (v0.21.5)

Architecture and platform fidelity improvements for the Raspberry Pi 5 hardware target.

## Completed: WS-U Phase U5 API & Dispatch Integrity (v0.21.4)

Refactored API dispatch enforcement, fixed error codes, added enforcement
wrappers, and documented design-intentional behaviors. 14 sub-tasks (U5-A
through U5-N). Key outcomes:

- U5-A/D: 7 machine-checked structural equivalence theorems proving checked/unchecked dispatch identity for capability-only syscalls
- U5-B/C: `.call` and `.reply` routed through enforcement wrappers (`endpointCallChecked`, `endpointReplyChecked`)
- U5-E: `decodeVSpaceMapArgs` error corrected from `.policyDenied` to `.invalidArgument`
- U5-F/G: `capabilityOnlyOperations` definition with security rationale
- U5-H–N: Design-intentional behavior documentation (badge-0, message handling, notification overwrite, slot 0, GrantReply, CDT tracking, deferred notificationSignal)

## Completed: WS-U Phase U4 Proof Chain & Invariant Composition (v0.21.3)

Internalized non-interference projection proofs and composed cross-subsystem
invariants. 3 sub-task groups (U4-A/B/C/D, U4-K, U4-N). Key outcomes:

- U4-A/B/C/D: Replaced externalized `hProjection` hypotheses with semantic queue domain isolation hypotheses in 4 IPC NonInterferenceStep constructors
- U4-K: Composed `ipcInvariantFull` (IPC + badge + bounded), integrated `serviceGraphInvariant` into `crossSubsystemInvariant`, added `canonicalAddressInvariant` to VSpace bundle
- U4-N: BFS positional queue lemma (`descendantsOf_go_queue_pos_children_found`) and queue membership variant for CDT transitive closure

## Completed: WS-U Phase U3 Rust ABI Hardening (v0.21.2)

Hardened the Rust userspace ABI layer with construction-time validation and
safety improvements. 10 sub-tasks (U3-A through U3-J). Key outcomes:

- `clobber_abi("C")` on `svc #0` inline assembly for ARM64 ABI compliance
- `MessageInfo` field privacy with validated constructors
- `AccessRights` `TryFrom` validation rejecting invalid bitmasks
- `KernelError` `#[non_exhaustive]` for forward compatibility
- `RegisterFile` safe bounds-checked access eliminating index panics
- `IpcBuffer` compile-time layout assertions
- Conformance test runner (`test_rust_conformance.sh`)

## Completed: WS-U Phase U2 Safety Boundary Hardening (v0.21.1)

Hardened safety boundaries across the kernel's input validation and type safety
surface. 14 sub-tasks (U2-A through U2-N). Key outcomes:

- VAddr canonical address checks (48-bit upper bound) in VSpace and decode paths
- Parameterized physical address width via `MachineConfig.physicalAddressWidth`
- ASID validation in syscall argument decode with updated roundtrip proofs
- `AccessRightSet.mk_checked` proof-carrying constructor (`bits < 2^5`)
- `allTablesInvExt_witness` compile-time completeness check (16 RHTables)
- Three-category `storeObject` callsite audit documentation
- Negative `LawfulBEq` instances for `RegisterFile` and `TCB`

## Completed: WS-U Phase U1 Correctness Fixes (v0.21.0)

Addressed 7 correctness findings (U-H01–U-H04, U-H13, U-H14, U-M39) from the
v0.20.7 audit. 13 sub-tasks (U1-A through U1-M). Key outcomes:

- Frozen queue link safety (`queuePPrev` cleared on pop, enabling multi-round IPC)
- Retype page-alignment re-verification after watermark advance
- API dispatch routes through `lifecycleRetypeWithCleanup`
- Authority right aligned (`.write` to `.retype`) matching `requiredRight` mapping
- IPC CSpace root fallback returns explicit error instead of silent fallback
- CDT deletion guard (`cspaceDeleteSlotCore` extraction + `hasCdtChildren` check)
- Domain switch saves outgoing context before clearing `current`

Plan: [`AUDIT_v0.20.7_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md).

## Completed: WS-T Deep-Dive Audit Remediation (v0.20.0–v0.20.7, PORTFOLIO COMPLETE)

Addressed all 72 findings (4 HIGH, 52 MEDIUM, 16 selected LOW) from dual v0.19.6
deep-dive audits. 8 phases (T1–T8), 94 sub-tasks. Key outcomes:

- **T1 (v0.20.0)**: Frozen IPC queue enqueue semantics, Rust KernelError ABI alignment.
- **T2 (v0.20.1)**: CDT access control (private constructor), AccessRightSet validity, frozen TLB, storeObject bundled preservation.
- **T3 (v0.20.2)**: Rust ABI hardening — `MessageInfo::encode()` Result, typed PagePerms, strict bool decode.
- **T4 (v0.20.3)**: IPC & capability proof closure — ipcStateQueueConsistent, dualQueueSystemInvariant, ipcInvariantFull preservation.
- **T5 (v0.20.4)**: Lifecycle safety, KernelObject.wellFormed, intrusive queue mid-node fix, stale reference detection.
- **T6 (v0.20.5)**: MMIO adapter, checked dispatch, VSpace least-privilege defaults, TLB flush ops, DTB parsing.
- **T7 (v0.20.6)**: buildChecked migration, 31 invariant checks, frozen IPC queue tests, pre-commit hardening, CI Rust job.
- **T8 (v0.20.7)**: Documentation synchronization, test validation, closure report.

Closure report: [`WS_T_CLOSURE_REPORT.md`](../dev_history/audits/WS_T_CLOSURE_REPORT.md).

## Completed: WS-Q Kernel State Architecture (v0.17.7–v0.17.14, PORTFOLIO COMPLETE)

Multi-phase plan unifying two-phase state architecture, service interface
simplification (WS-P absorbed), and Rust syscall wrappers (WS-O absorbed).
9 phases (Q1–Q9, 45 atomic units). See [`MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](../dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md).

**WS-Q1 (v0.17.7) — COMPLETED:** Service interface simplification. Stateless
registry model replacing lifecycle-based `ServiceStatus`/`ServiceConfig`.

**WS-Q2 (v0.17.8) — COMPLETED:** Universal RHTable migration. Replaced all
`Std.HashMap`/`Std.HashSet` in kernel state with verified `RHTable`/`RHSet`.
16 map fields + 2 set fields across 6 structures, 30+ files, 10 atomic
subphases (Q2-A through Q2-J). `allTablesInvExt` global invariant predicate.
Zero sorry/axiom, all tests pass.

**WS-Q3 (v0.17.9) — COMPLETED:** IntermediateState formalization. `IntermediateState`
type wrapping `SystemState` with four invariant witnesses (`allTablesInvExt`,
`perObjectSlotsInvariant`, `perObjectMappingsInvariant`, `lifecycleMetadataConsistent`).
7 builder operations (`registerIrq`, `registerService`, `addServiceGraph`,
`createObject`, `deleteObject`, `insertCap`, `mapPage`). Boot sequence
(`bootFromPlatform`) with master validity theorem. Zero sorry/axiom, 1,479
proved declarations, all tests pass.

**WS-Q4 (v0.17.10) — COMPLETED:** CNode radix tree (verified). `CNodeRadix`
flat radix array for CNode capability slots with O(1) zero-hash lookup via
`extractBits`. 24 correctness proofs, `buildCNodeRadix` equivalence bridge,
`freezeCNodeSlots` Q5 integration, 12-scenario test suite. Zero sorry/axiom.

**WS-Q5 (v0.17.11) — COMPLETED:** FrozenSystemState + freeze. `FrozenMap`/
`FrozenSet` types, per-object frozen representations, `freeze` function
(IntermediateState → FrozenSystemState), capacity planning. 20+ theorems,
15-scenario test suite. Zero sorry/axiom.

**WS-Q6 (v0.17.12) — COMPLETED:** Freeze correctness proofs. Machine-checked
proofs that `freeze` preserves lookup semantics and kernel invariants. Core
`freezeMap_get?_eq` + 13 per-field lookup equivalence theorems (Q6-A). CNode
radix equivalence via generic fold helpers (Q6-B). 5 structural property
theorems (Q6-C). Invariant transfer with `freeze_preserves_invariants` keystone
(Q6-D). 31 theorems, 22-scenario test suite. Zero sorry/axiom.

## Completed: WS-N Robin Hood Hashing (v0.17.0–v0.17.5)

Formally verified Robin Hood hash table closing the trust gap between seLe4n's
machine-checked proof surface and the unverified `Std.HashMap` library type.
Single-representation architecture with fuel-bounded recursion, bounds-checked
array access, and per-cluster modular-arithmetic ordering. 5 phases (N1–N5,
122 subtasks). Portfolio **COMPLETE**.
See [`AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md).

**WS-N1 (v0.17.1) — COMPLETED:** `RHEntry`/`RHTable` core types, `idealIndex`/
`nextIndex` with bound proofs, `empty` constructor with `empty_wf` 4-conjunct
proof, fuel-bounded `insertLoop`/`getLoop`/`findLoop`/`backshiftLoop`,
`insert`/`get?`/`erase`/`fold`/`resize` operations, `insertLoop_preserves_len`/
`backshiftLoop_preserves_len` array-size preservation proofs, `Membership`
instance. 379 lines in `SeLe4n/Kernel/RobinHood/Core.lean`. Zero sorry/axiom.

**WS-N2 (v0.17.2) — COMPLETED:** Full invariant proofs — `distCorrect`,
`noDupKeys`, `probeChainDominant` preservation through insert/erase/resize;
lookup correctness (`get_after_insert_eq`, `get_after_insert_ne`,
`get_after_erase_eq`). All 6 TPI-D items complete (D1–D6), ~4,655 LoC across
`SeLe4n/Kernel/RobinHood/Invariant/`. Key innovation: `relaxedPCD` framework
for erase PCD preservation. Zero sorry/axiom.

**WS-N3 (v0.17.3) — COMPLETED:** Kernel API bridge — `Inhabited`/`BEq`
typeclass instances, 12 bridge lemmas matching `Std.HashMap` patterns
(`getElem?_empty`, `getElem?_insert_self/ne`, `getElem?_erase_self/ne`,
`size_insert_le`, `size_erase_le`, `mem_iff_isSome_getElem?`,
`getElem?_eq_some_getElem`, `fold_eq_slots_foldl`), `filter` support with
`size_filter_le_capacity`/`size_filter_le_size`, `ofList` constructor,
`get_after_erase_ne` proof (+247 lines in Lookup.lean). ~358 LoC in
`SeLe4n/Kernel/RobinHood/Bridge.lean`. Zero sorry/axiom.

**WS-N4 (v0.17.4) — COMPLETED:** Kernel integration (first site — CNode.slots)
— replaced `CNode.slots : Std.HashMap Slot Capability` with `RHTable Slot
Capability` across the entire kernel. Updated CNode operations (`lookup`,
`insert`, `remove`, `revokeTargetLocal`), `slotsUnique` repurposed from `True`
to substantive `invExt ∧ size < capacity ∧ 4 ≤ capacity` invariant, ~25
CNode/capability theorems updated, ~15 invariant proofs across
Capability/InformationFlow subsystems, 3 new bridge lemmas
(`filter_fold_absent_by_pred`, `filter_get_pred`, `filter_filter_getElem?`),
all test fixtures updated. 20+ files modified. Zero sorry/axiom.

**WS-N5 (v0.17.5) — COMPLETED:** Test coverage + documentation — 12 standalone
Robin Hood test scenarios (`RobinHoodSuite.lean`: empty table, insert/get roundtrip,
erase, overwrite, multi-key, collision handling, Robin Hood swap, backward-shift,
resize trigger, post-resize correctness, large-scale 200-entry stress, fold/toList)
+ 6 CNode integration tests (lookup/insert/remove, revokeTargetLocal, findFirstEmptySlot,
slotCountBounded, CSpace resolution, BEq). `robin_hood_suite` executable added to
`lakefile.toml`, Tier 2 test coverage, 18 scenario IDs registered. Full documentation
sync across 8 canonical files + 4 GitBook chapters. ~300 LoC tests. Zero sorry/axiom.
**WS-N portfolio COMPLETE** (v0.17.0–v0.17.5).

## Completed: WS-M Capability Subsystem Audit & Remediation (v0.16.13–v0.17.0, PORTFOLIO COMPLETE)

End-to-end audit of the Capability subsystem (3,520 LoC, 5 files) identified
14 findings across 4 categories: 5 performance optimizations (M-P01–P05),
4 proof gaps (M-G01–G04), 3 test coverage gaps (M-T01–T03), and 2 documentation
items (M-D01–D02). Also resolves deferred L-T03 (IPC capability transfer model).
All 5 phases (M1–M5) delivered across v0.16.14–v0.17.0. All 14 findings resolved.
Phase 1 (WS-M1, proof strengthening) completed at v0.16.14: 7 new proved
declarations including `resolveCapAddress_guard_match`, `cdtMintCompleteness`,
`addEdge_preserves_edgeWellFounded_fresh`, `cspaceRevokeCdt_swallowed_error_consistent`.
Phase 2 (WS-M2, performance optimization) completed at v0.16.15:
- M2-A: fused revoke (`revokeAndClearRefsState` single-pass replacing the prior two-pass fold),
- M2-B: CDT `parentMap` index for O(1) `parentOf` lookup (replacing O(E) edge scan),
- M2-C: reply lemma extraction and new field preservation lemmas for NI proofs,
- `parentMapConsistent` runtime check added to invariant surface.
Findings M-P01, M-P02, M-P03, M-P05 resolved at v0.16.15.
Phase 3 (WS-M3, IPC capability transfer) completed at v0.16.17:
- 20 atomic subtasks across 7 tasks: types, slot scanning, single-cap transfer, batch unwrap, IPC wrappers, API wiring, tests
- seL4-aligned architecture: cap unwrapping on receive side, Grant-right gate, CDT `.ipcTransfer` edge tracking
- Wrapper pattern preserves all existing IPC operation signatures and proofs
- `ipcTransferSingleCap`/`ipcUnwrapCaps` operations with preservation proofs
- `endpointSendDualWithCaps`/`endpointReceiveDualWithCaps`/`endpointCallWithCaps` wrappers
- IPC invariant preservation proofs for all wrappers; `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant`
- `decodeExtraCapAddrs`/`resolveExtraCaps` API wiring, 4 test scenarios (basic, no-grant, full-CNode, badge+cap combined)
- Resolves L-T03 (capability transfer during IPC); 12+ new proved declarations
Phase 4 (WS-M4, test coverage expansion) completed at v0.16.18: 8 new test
scenarios addressing M-T01/M-T02.
Phase 5 (WS-M5, streaming BFS optimization) completed at v0.16.19, optimized v0.17.0:
`processRevokeNode` shared helper (DRY refactor), `streamingRevokeBFS`/`cspaceRevokeCdtStreaming`
operations, `processRevokeNode_preserves_capabilityInvariantBundle` shared proof,
`streamingRevokeBFS_preserves` induction, `cspaceRevokeCdtStreaming_preserves_capabilityInvariantBundle`
top-level preservation. 4 test scenarios (branching, empty, deep chain, equivalence). Resolves M-P04.
See [WS-M workstream plan](../dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md).

## Completed: WS-K Full Syscall Dispatch Completion (v0.16.0–v0.16.8)

Completed the syscall surface established by WS-J1. Extended
`SyscallDecodeResult` with message register values (x2–x5), defined per-syscall
argument structures with total decode functions, wired all 13 syscalls through
`dispatchWithCap` (replacing 7 `.illegalState` stubs), replaced service policy
stubs with configuration-sourced predicates, populated IPC message bodies from
decoded registers, and proved round-trip correctness, invariant preservation,
and NI coverage for all new paths. All 8 phases (K-A through K-H) completed
(v0.16.0–v0.16.8). See
[workstream plan](../dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md).

## Completed: WS-L IPC Subsystem Audit & Remediation (v0.16.9–v0.16.13, PORTFOLIO COMPLETE)

A comprehensive end-to-end audit of the IPC subsystem (9,195 LoC, 12 files).
All 5 phases delivered. 12 of 13 findings resolved; 1 intentionally deferred
(L-T03: resolved by WS-M3 IPC capability transfer).

| Phase | Focus | Priority | Status |
|-------|-------|----------|--------|
| **WS-L1** | IPC performance optimization (redundant TCB lookups) | HIGH | **Completed** |
| **WS-L2** | Code quality: HashMap.fold migration | MEDIUM | **Completed** |
| **WS-L3** | Proof strengthening: round-trip, consistency, preservation | MEDIUM | **Completed** |
| **WS-L4** | Test coverage: ReplyRecv, blocked-thread, interleaving | MEDIUM | **Completed** |
| **WS-L5** | Documentation: IF readers' guide, fixture process, metrics | LOW | **Completed** |

See [WS-L workstream plan](../dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md).

## Next: Raspberry Pi 5 Hardware Binding

The next major milestone is populating the RPi5 platform stubs with
hardware-validated contracts:

1. Populate RPi5 runtime contract with hardware-validated predicates.
2. Implement ARMv8 multi-level page table walk as a `VSpaceBackend` instance.
3. Implement GIC-400 interrupt routing with IRQ acknowledgment.
4. Bind timer adapter to ARM Generic Timer (CNTPCT_EL0).
5. Define boot sequence as a verified initial state construction.

## Completed: WS-J1-F CdtNodeId Cleanup and Documentation Sync (v0.15.10)

Final cleanup phase of WS-J1. Replaced `abbrev CdtNodeId := Nat` with
`structure CdtNodeId where val : Nat` in `Model/Object/Structures.lean`,
matching the typed wrapper pattern used by all other kernel identifiers. Added
full instance suite (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`,
`LawfulBEq`, `Repr`, `ToString`, `Inhabited`, `ofNat`/`toNat`) co-located with
the type definition. Fixed downstream compilation: `SystemState` field defaults
(`cdtNextNode := ⟨0⟩`), monotone allocator (`⟨node.val + 1⟩`), test literals
in `NegativeStateSuite.lean`. All documentation synchronized across canonical
sources and GitBook chapters. Codebase map regenerated. All 16 kernel identifiers
are now typed wrappers. Zero sorry/axiom. Closes WS-J1 Phase F.
**WS-J1 portfolio fully completed.**

## Completed: WS-J1-E Testing and Trace Evidence (v0.15.9)

Testing and trace evidence for the register decode layer. 18 negative decode
tests in `NegativeStateSuite.lean` covering `validateRegBound`, `decodeSyscallId`,
`decodeMsgInfo`, `decodeCapPtr`, `decodeSyscallArgs`, and `syscallEntry` error
paths. 5 register-decode trace scenarios (RDT-002 through RDT-010) in
`MainTraceHarness.lean`: standalone decode success, full `syscallEntry` send via
register decode, invalid syscall number, malformed message info, out-of-bounds
register layout. 2 operation-chain tests (`chain10RegisterDecodeMultiSyscall`,
`chain11RegisterDecodeIpcTransfer`) in `OperationChainSuite.lean`. Fixture and
scenario registry updates. 13 Tier 3 invariant surface anchors for
RegisterDecode definitions and theorems. Zero sorry/axiom. Closes WS-J1 Phase E.

## Completed: WS-J1-D Invariant and NI Integration (v0.15.8)

Invariant and information-flow integration for the register decode path.
`registerDecodeConsistent` predicate bridging the decode layer to the kernel
object store. Invariant preservation through `syscallEntry` (compositional:
decode is pure, lookup is read-only). Non-interference: `decodeSyscallArgs_preserves_lowEquivalent`,
`lookupThreadRegisterContext_preserves_lowEquivalent/projection`,
`syscallEntry_preserves_projection`. Two new `NonInterferenceStep` constructors:
`syscallDecodeError` and `syscallDispatchHigh`. Bridge theorems connecting
`syscallEntry` outcomes to NI steps. Zero sorry/axiom. Closes WS-J1 Phase D.

## Completed: WS-J1-C Syscall Entry Point and Dispatch (v0.15.6; refinements v0.15.7)

Wired the register decode layer into a register-sourced syscall entry point.
`syscallEntry` reads the current thread's saved register context via
`lookupThreadRegisterContext`, decodes raw register values via `decodeSyscallArgs`
(with configurable `regCount` parameter, default 32 for ARM64), and dispatches
through capability-gated `syscallInvoke` to the appropriate internal kernel
operation. `dispatchSyscall` constructs a `SyscallGate` from the caller's TCB and
CSpace root CNode, while `dispatchWithCap` routes all 13 modeled syscalls: IPC
ops (send/receive/call/reply) and service ops extract targets from the resolved
capability, while CSpace ops (mint/copy/move/delete), lifecycle retype, and
VSpace ops (map/unmap) return `illegalState` as they require message-register
data not yet available in the decode path (full MR extraction deferred to
WS-J1-E). `syscallRequiredRight` provides a total mapping from `SyscallId` to
`AccessRight`. `MachineConfig.registerCount` promoted from computed def to
configurable structure field (default 32 for ARM64). Five soundness theorems
proved: `syscallEntry_requires_valid_decode`,
`syscallEntry_implies_capability_held` (full capability-resolution chain from
TCB/CSpace lookup to resolved cap with required right),
`dispatchSyscall_requires_right`, `lookupThreadRegisterContext_state_unchanged`,
`syscallRequiredRight_total`. Zero sorry/axiom. Closes WS-J1 Phase C.

## Completed: WS-J1-B Register Decode Layer (v0.15.5)

Register decode layer closing the gap between raw machine registers and typed
kernel operations. `SyscallId` inductive (13 modeled syscalls with injective
encoding and round-trip proofs), `MessageInfo` structure (seL4 message-info
bit-field layout with `encode`/`decode`), `SyscallDecodeResult` typed output,
total deterministic decode functions (`decodeCapPtr`, `decodeMsgInfo`,
`decodeSyscallId`, `validateRegBound`, `decodeSyscallArgs`) in self-contained
`RegisterDecode.lean` module, `SyscallRegisterLayout` with `arm64DefaultLayout`
(x0–x7 convention), `MachineConfig.registerCount`, 3 new `KernelError` variants
(`invalidRegister`, `invalidSyscallNumber`, `invalidMessageInfo`), round-trip
lemmas, determinism theorem, error exclusivity theorems. Zero sorry/axiom.
Closes WS-J1 Phase B.

## Completed: WS-H12e Cross-Subsystem Invariant Reconciliation (v0.14.2)

Reconciled all subsystem invariant compositions after WS-H12a–d changes.
`coreIpcInvariantBundle` upgraded from `ipcInvariant` to `ipcInvariantFull`
(3-conjunct: `ipcInvariant ∧ dualQueueSystemInvariant ∧ allPendingMessagesBounded`);
`schedulerInvariantBundleFull` extended from 4 to 5 conjuncts (+ `contextMatchesCurrent`);
`ipcSchedulerCouplingInvariantBundle` extended with `contextMatchesCurrent` and
`currentThreadDequeueCoherent`; `proofLayerInvariantBundle` uses full scheduler bundle;
8 frame lemmas + 3 compound preservation theorems + 7 composed `ipcInvariantFull`
preservation theorems; all `*_preserves_schedulerInvariantBundleFull` theorems updated;
default state proofs extended. Closes systemic invariant composition gaps from WS-H12a–d.

## Completed: WS-H12d IPC Message Payload Bounds (v0.14.1)

`IpcMessage` registers/caps migrated from `List` to `Array` with
`maxMessageRegisters`(120)/`maxExtraCaps`(3). Bounds enforcement at all 4 send
boundaries (`endpointSendDual`/`endpointCall`/`endpointReply`/`endpointReplyRecv`).
4 `*_message_bounded` theorems. `allPendingMessagesBounded` system invariant
integrated into `ipcInvariantFull` bundle (now 9-conjunct as of V3-G6/J/K). `checkBounds_iff_bounded`
decidability bridge. Information-flow enforcement updated with bounds-before-flow
ordering. Closes A-09 (HIGH).

## Completed: WS-I3 Operations Coverage Expansion (v0.15.2)

Phase 3 (operations-focused) of the WS-I improvement portfolio:

- `tests/OperationChainSuite.lean` adds six compositional chain tests spanning lifecycle, CSpace, IPC, VSpace, service sequencing, and notifications.
- Scheduler stress section adds 16-thread repeated scheduling, same-priority deterministic selection checks, and multi-domain isolation checks with `switchDomain` + `schedule`.
- Tier 2 negative gate now executes `OperationChainSuite` via `scripts/test_tier2_negative.sh`.
- `tests/InformationFlowSuite.lean` adds declassification runtime coverage for authorized downgrade, normal-flow rejection, policy-denied rejection, and a 3-domain lattice scenario; policy-denied downgrade now reports distinct `declassificationDenied`.

## Completed: WS-I1 Critical Testing Infrastructure (v0.15.0)

Phase 1 of the WS-I improvement portfolio, addressing three critical testing
infrastructure recommendations from the v0.14.9 audit:

- **R-01 (inter-transition assertions):** 17 `checkInvariants` calls across all
  13 trace functions, invoking 17 invariant check families (scheduler, CSpace, IPC,
  lifecycle, service, VSpace, CDT, ASID, untyped, notification, blocked-thread, domain)
  after every major transition group. `IO.Ref Nat` counter tracking with `[ITR-001]`
  summary output.
- **R-02 (mandatory determinism):** `test_tier2_determinism.sh` runs trace twice
  and diffs output, integrated into `test_smoke.sh` Tier 2 gate. Determinism is now
  a mandatory CI property rather than an optional Tier 4 extension.
- **R-03 (scenario ID traceability):** 121 trace lines tagged with unique IDs
  across 15 prefix families. Pipe-delimited fixture format. Scenario registry YAML
  with bidirectional Tier 0 validation.

## Completed: WS-H12f Test Harness Update & Documentation Sync (v0.14.3)

Three new trace scenarios added to `MainTraceHarness.lean`:
`runDequeueOnDispatchTrace` (dequeue-on-dispatch lifecycle with preemption
re-enqueue), `runInlineContextSwitchTrace` (inline context save/restore through
`handleYield` → `schedule`), `runBoundedMessageExtendedTrace` (zero-length,
sub-boundary, max-caps message acceptance). Legacy `endpointInvariant` comments
cleaned up in `IPC/Invariant.lean`. Expected fixture updated (108 lines, 11 new
output lines). 9 new Tier 3 anchors. Documentation synchronized across all
canonical sources and GitBook chapters. Completes WS-H12 composite workstream.

## Completed: WS-H12c Per-TCB Register Context (v0.14.0)

Per-TCB `registerContext` field on TCB with inline `saveOutgoingContext`/
`restoreIncomingContext` in `schedule`. `contextMatchesCurrent` invariant with
preservation proofs for all scheduler and IPC operations. Information-flow
projection strips register context. `endpointInvariant` removed (vacuous since
WS-H12a). Closes H-03 (HIGH).

## Completed: WS-H12b Dequeue-on-Dispatch Scheduler Semantics (v0.13.9)

Inverted `queueCurrentConsistent` from `current ∈ runnable` to
`current ∉ runnable`, matching seL4's `switchToThread`/`tcbSchedDequeue`
dequeue-on-dispatch semantics. `schedule` dequeues chosen thread before
dispatch; `handleYield` inserts+rotates current thread; `timerTick`
re-enqueues on preemption; `switchDomain` re-enqueues before domain switch.
Added `currentTimeSlicePositive`, `schedulerPriorityMatch`, and IPC coherence
predicates. ~1800 lines of proofs re-proved. Closes H-04 (HIGH).

## Completed: WS-H12a Legacy Endpoint Removal (v0.13.8)

Deleted `EndpointState` type and legacy endpoint fields (`state`, `queue`,
`waitingReceiver`). Removed legacy IPC operations (`endpointSend`,
`endpointReceive`, `endpointAwaitReceive`) and ~60 associated dead theorems.
All IPC now uses exclusively the O(1) dual-queue path. `endpointReplyRecv`
migrated from legacy `endpointAwaitReceive` to `endpointReceiveDual`. Tests
and tier-3 anchors updated. Closes A-08 (HIGH), M-01 (MEDIUM), A-25 (MEDIUM).

## Completed: WS-H11 VSpace & Architecture Enrichment (v0.13.7)

PagePermissions struct with W^X enforcement at insertion time. Address bounds
checking via `vspaceMapPageChecked` (ARM64 52-bit PA bound). TLB/cache
maintenance model with `TlbState`, `adapterFlushTlb`, and `adapterFlushTlbByAsid`.
`VSpaceBackend` typeclass for platform-agnostic page table operations.
Per-VAddr TLB flush (`adapterFlushTlbByVAddr`) and cross-ASID TLB isolation
theorem. `vspaceInvariantBundle` extended to 5-conjunct preservation across all
VSpace transitions. 889 proved declarations, zero sorry/axiom.

## Completed: WS-H10 Security Model Foundations (v0.13.6)

Extended `ObservableState` with domain-gated machine register file projection
(`machineRegs`). Machine timer deliberately excluded to prevent covert timing
channels. Added standard BIBA security lattice alternatives (`bibaPolicy`,
`bibaSecurityFlowsTo`) with reflexivity/transitivity proofs. Introduced
`DeclassificationPolicy` with `declassifyStore` enforcement operation (5
theorems). Added `endpointFlowPolicyWellFormed` predicate with reflexivity and
transitivity inheritance proofs. Closes C-05/A-38 (CRITICAL), A-34 (CRITICAL),
A-39 (MEDIUM), M-16 (MEDIUM). Added `declassifyStore_NI` (non-interference for
controlled declassification) and `InformationFlowConfigInvariant` bundle. 866
proved declarations.

## Completed: WS-H7/H8/H9 Audit Gap Closure (v0.13.5)

Comprehensive codebase audit identified and closed remaining gaps in WS-H7, WS-H8,
and WS-H9: BEq soundness lemmas (`VSpaceRoot.beq_sound`, `CNode.beq_sound`),
`endpointReceiveDualChecked_NI` enforcement bridge theorem, 3 IPC NI theorems
(`endpointReceiveDual_preserves_lowEquivalent`, `endpointCall_preserves_lowEquivalent`,
`endpointReplyRecv_preserves_lowEquivalent`), and `NonInterferenceStep` extended
to 31 constructors. Zero sorry/axiom. All tests pass.

## Completed: WS-H9 Non-Interference Coverage Extension (v0.13.4)

WS-H9 extends NI coverage from ~25% to >80% of kernel operations (C-02/A-40 CRITICAL),
adding 27 new NI preservation theorems across scheduler, IPC, CSpace, VSpace, and
observable-state operations. `NonInterferenceStep` inductive extended from 11 to 28
constructors. `composedNonInterference_trace` covers all constructors. See
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-H5 IPC Dual-Queue Structural Invariant (v0.12.19)

WS-H5 defines and proves a formal structural well-formedness invariant for the
intrusive dual-queue IPC implementation, closing C-04/A-22 (CRITICAL), A-23
(HIGH), and A-24 (HIGH). Core predicates: `intrusiveQueueWellFormed` (head/tail
emptiness iff, boundary link consistency, TCB existence), `dualQueueSystemInvariant`
(all endpoints well-formed + `tcbQueueLinkIntegrity` doubly-linked forward/reverse
consistency). 13 preservation theorems cover all dual-queue operations. See
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-H3 Build/CI Infrastructure Fixes (v0.12.17)

WS-H3 addresses build and CI infrastructure gaps identified in the v0.12.15
audit: `run_check` return value fix (H-12) so failure is correctly signaled in
continue mode, `test_docs_sync.sh` integration into the smoke CI job and
`test_smoke.sh` entrypoint (M-19), and a `rg` availability guard with `grep -P`
fallback in Tier 3 (M-20). See
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-H2 Lifecycle Safety Guards (v0.12.16)

WS-H2 addresses lifecycle safety gaps identified in the v0.12.15 audit:
childId self-overwrite and collision guards in `retypeFromUntyped`, TCB scheduler
cleanup on retype via `lifecycleRetypeWithCleanup`, CNode CDT slot detach, and
atomic dual-store retype. Proved `lifecycleRetypeWithCleanup_ok_runnable_no_dangling`
— no dangling run queue entries after TCB retype. See
[`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-H1 IPC call-path semantic fix (v0.12.16)

WS-H1 addresses the IPC call-path semantic gap identified in the v0.12.15 audit:
`blockedOnCall` state for call/reply semantics, reply-target scoping to prevent
confused-deputy attacks, and 5-conjunct `ipcSchedulerContractPredicates` with full
invariant proof maintenance. See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).

## Completed: WS-G kernel performance optimization

The WS-G portfolio (v0.12.6–v0.12.15) closed all 14 findings from the
[v0.12.5 performance audit](../dev_history/audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md),
migrating every kernel hot path to O(1) hash-based structures. All proofs
re-verified — zero sorry/axiom.

See [Kernel Performance Optimization (WS-G)](08-kernel-performance-optimization.md)
for the full technical breakdown.

## Next: WS-J1 and Raspberry Pi 5 hardware binding

All WS-F and WS-H remediation workstreams are completed. The active
workstream was **WS-J1** (register-indexed authoritative namespace migration).
All 6 phases (J1-A through J1-F) are completed (v0.15.4–v0.15.10): typed register
wrappers, decode layer, syscall entry point, invariant/NI integration, testing/trace
evidence, and CdtNodeId cleanup. **WS-J1 portfolio fully completed.**

See [`docs/WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md),
[`docs/audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md),
and [Next Development Path](../dev_history/gitbook/22-next-slice-development-path.md).

## Hardware roadmap

H0 (neutral semantics, complete) → H1 (boundary interfaces, complete) →
H2 (proof deepening, complete) → H3 (Raspberry Pi 5 binding) →
H4 (evidence convergence).

See [Path to Real Hardware](10-path-to-real-hardware-mobile-first.md).

## Non-negotiable baseline contracts

1. Deterministic transition semantics (explicit success/failure).
2. IPC-scheduler handshake coherence.
3. Domain-aware scheduling (active-domain-only).
4. Local + composed invariant layering.
5. Stable theorem naming.
6. Fixture-backed executable evidence.
7. Tiered validation commands.
8. Import hygiene (`API.lean` as canonical aggregate).
