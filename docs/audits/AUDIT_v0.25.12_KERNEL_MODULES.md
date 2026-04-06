# seLe4n Kernel Module Audit v0.25.12

**Audit Date**: 2026-04-06
**Codebase Version**: v0.25.12 (Lean 4.28.0, Lake 0.25.12)
**Scope**: Complete line-by-line audit of all 150 Lean modules, 30 Rust source files, CI/build scripts, and test infrastructure
**Auditor**: Claude Opus 4.6 (automated, multi-agent)
**Classification**: Pre-release comprehensive audit

---

## Executive Summary

This audit reviewed **every line of code** across 180 source files (~45,000+ lines) comprising the seLe4n microkernel. The codebase was partitioned into 9 audit domains and analyzed in parallel for correctness, security, performance, proof soundness, and ABI consistency.

**Overall Assessment: STRONG — Production-Ready with Noted Caveats**

The kernel demonstrates exceptional formal verification discipline. **Zero `sorry` or `axiom` instances** exist across the entire Lean codebase. All kernel transitions are deterministic pure functions. The Rust ABI layer is `#![no_std]`-compatible with a single justified `unsafe` block. The proof surface is genuine and substantial — not tautological.

### Aggregate Finding Counts

| Severity | Count | Description |
|----------|-------|-------------|
| CRITICAL | 0 | No exploitable vulnerabilities found |
| HIGH | 6 | Design-level gaps requiring attention before hardware binding |
| MEDIUM | 38 | Assurance gaps, defense-in-depth improvements, maintenance risks |
| LOW | 50 | Minor inconsistencies, documentation debt, style issues |
| INFO | 72+ | Positive findings, design validations, confirmed correctness |

**No vulnerabilities warranting CVE designation were discovered.**

---

## Table of Contents

1. [Foundation Layer (Prelude, Machine, Model)](#1-foundation-layer)
2. [Scheduler Subsystem](#2-scheduler-subsystem)
3. [IPC Subsystem](#3-ipc-subsystem)
4. [Capability Subsystem](#4-capability-subsystem)
5. [Information Flow Subsystem](#5-information-flow-subsystem)
6. [Architecture & Platform Layer](#6-architecture--platform-layer)
7. [Data Structures (RobinHood, RadixTree, FrozenOps)](#7-data-structures)
8. [SchedContext, Lifecycle, Service, CrossSubsystem](#8-schedcontext-lifecycle-service-crosssubsystem)
9. [Rust Implementation](#9-rust-implementation)
10. [Test Infrastructure & Build System](#10-test-infrastructure--build-system)
11. [Cross-Cutting Analysis](#11-cross-cutting-analysis)
12. [Consolidated HIGH Findings](#12-consolidated-high-findings)
13. [Recommendations](#13-recommendations)

---


## 1. Foundation Layer

**Files**: `SeLe4n/Prelude.lean`, `SeLe4n/Machine.lean`, `SeLe4n/Model/Object/*`, `SeLe4n/Model/State.lean`, `SeLe4n/Model/IntermediateState.lean`, `SeLe4n/Model/Builder.lean`, `SeLe4n/Model/FrozenState.lean`, `SeLe4n/Model/FreezeProofs.lean`
**Lines audited**: ~6,500+
**sorry/axiom**: Zero

### Findings

| ID | Severity | File | Description |
|----|----------|------|-------------|
| F-S04 | MEDIUM | Object/Structures.lean:1018 | CDT `descendantsOf` BFS fuel = `edges.length` may be insufficient for completeness; `edgeWellFounded` is the operationally-used predicate, so kernel safety unaffected |
| F-P02 | LOW | Prelude.lean:172 | `Membership` instance argument order reversed in naming (correct in implementation) |
| F-M03 | LOW | Machine.lean:577 | `MachineConfig.wellFormed` returns `Bool` while `MemoryRegion.wellFormed` returns `Prop` — inconsistency |
| F-T03 | LOW | Object/Types.lean:1153 | `MessageInfo.decode` label extraction unbounded before bounds check (safe — check follows immediately) |
| F-S02 | LOW | Object/Structures.lean:495 | `CNode.resolveSlot` does not enforce `bitsRemaining ≤ 64` (mitigated by `cnodeWellFormed`) |
| F-ST02 | LOW | State.lean:229 | `objectIndex` is append-only `List ObjId` with O(n) iteration (acceptable for 65K max objects) |
| F-ST04 | LOW | State.lean:482 | `storeObject` capabilityRefs clear+rebuild is O(R+S) per store |
| F-B02 | LOW | Builder.lean:170 | `createObject` does not update `capabilityRefs` or `asidTable` (valid only during builder phase) |

### Positive Findings

- Complete `LawfulMonad` instance for `KernelM` with all laws proven
- `freezeMap_get?_eq` keystone theorem is sound — lookup equivalence between RHTable and FrozenMap
- 12 per-field freeze equivalence theorems, all machine-checked
- All typed identifiers use consistent sentinel = 0 convention
- Non-lawful `BEq` instances (RegisterFile, TCB, VSpaceRoot) all have formal negative witnesses


---

## 2. Scheduler Subsystem

**Files**: 20 files under `SeLe4n/Kernel/Scheduler/` (~8,700 lines)
**sorry/axiom**: Zero

### Findings

| ID | Severity | File | Description |
|----|----------|------|-------------|
| S-01 | MEDIUM | PriorityInheritance/Propagate.lean:68 | PIP reads `blockingServer` from pre-update state — currently safe because `updatePipBoost` only modifies `pipBoost`/`runQueue`, but fragile coupling |
| S-02 | MEDIUM | Operations/Core.lean:500-515 | `timeoutBlockedThreads` O(n) scan over entire object store on budget exhaustion |
| S-03 | MEDIUM | Operations/Core.lean:512 | Silent error swallowing in `timeoutBlockedThreads` — `.error _ => acc` masks potential invariant violations |
| S-04 | MEDIUM | Scheduler/Invariant.lean:73 | `currentThreadInActiveDomain` vacuous for non-TCB objects (safe under `currentThreadValid`, but fragile if invariant dropped from composition) |
| S-05 | MEDIUM | PriorityInheritance/BlockingGraph.lean:78-88 | `blockingChain` silent truncation on fuel exhaustion; depends on external `blockingAcyclic` invariant from CrossSubsystem |
| S-06 | MEDIUM | PriorityInheritance/BoundedInversion.lean:39-43 | PIP inversion bound uses `objectIndex.length` (all objects) instead of `countTCBs` — overly conservative |
| S-07 | MEDIUM | Liveness/WCRT.lean:132-139 | Main WCRT theorem is definitional; actual liveness depends on two unproven external hypotheses (`hDomainActiveRunnable`, `hBandProgress`) |
| S-08 | LOW | Operations/Core.lean:700-704 | `handleYieldWithBudget` fallback masks missing SchedContext violation |
| S-09 | LOW | RunQueue.lean:104-110 | `recomputeMaxPriority` O(p) fold (acceptable for p ≤ 256) |
| S-10 | LOW | Liveness/TraceModel.lean:103-112 | `stepPost` reimplements replenishment inline (divergence risk with real implementation) |
| S-11 | LOW | BoundedInversion.lean:53-67 | Trivial determinism theorems proved by `subst; rfl` — add no meaningful assurance |
| S-12 | LOW | Operations/Core.lean:586-587 | Missing SchedContext fallback runs thread without budget accounting (unreachable under invariant) |

### Positive Findings

- Three-level `isBetterCandidate` predicate: irreflexivity, asymmetry, transitivity all proven
- 15-tuple `schedulerInvariantBundleExtended` with complete preservation chain
- EDF tie-breaking correctly scoped to same-domain, same-priority (WS-H6 fix)
- CBS timing correctly uses pre-tick time for replenishment scheduling
- No starvation freedom — correctly documented as delegated to user-level policy (matches seL4)


---

## 3. IPC Subsystem

**Files**: 20 files under `SeLe4n/Kernel/IPC/` (~22,000+ lines)
**sorry/axiom**: Zero

### Findings

| ID | Severity | File | Description |
|----|----------|------|-------------|
| I-T01 | MEDIUM | Operations/Timeout.lean:23,111 | Timeout detection via magic register value `0xFFFFFFFF` (line 23: `timeoutErrorCode`) combined with `ipcState = .ready` check (line 111). The composite AND condition mitigates false positives — both the register value AND ready state must hold simultaneously. Still recommended to replace with an out-of-band `timedOut : Bool` TCB field for hardware binding. |
| I-TR02 | MEDIUM | DualQueue/Transport.lean:1648 | `endpointReceiveDual` reads `pendingMessage`/`ipcState` from pre-dequeue TCB — proven safe by transport lemmas but fragile if PopHead semantics change |
| I-WC01 | MEDIUM | DualQueue/WithCaps.lean:28-33 | All capability transfers target `Slot.ofNat 0` — simplification that overwrites previous transfers; must be generalized for hardware binding |
| I-ST01 | MEDIUM | Invariant/Structural.lean:4752-4774 | `ipcInvariantFull` preservation requires 11 externalized post-state hypotheses — proof obligations deferred to cross-subsystem layer |
| I-E01 | LOW | Operations/Endpoint.lean:336 | Stale comment claims no formal `pendingMessage = none` invariant exists (it now does: `waitingThreadsPendingMessageNone`) |
| I-E02 | LOW | Operations/Endpoint.lean:389-392 | Notification wait uses prepend (LIFO) instead of FIFO append — matches seL4 abstract model |
| I-C02 | LOW | Operations/CapTransfer.lean:86-97 | Short-circuit on error pads remaining caps with `.noSlot` — documented and correct |
| I-T02 | LOW | Operations/Timeout.lean:104 | Unused `_endpointId` parameter reserved for future validation |
| I-D02 | LOW | Operations/Donation.lean:79,170,189 | Error paths silently return unchanged state on donation failure |
| I-DQ02 | LOW | DualQueue/Core.lean:313-316 | Duplicate enqueue prevention relies on callers clearing queue links first |
| I-WC02 | LOW | DualQueue/WithCaps.lean:37-42 | CDT tracking imprecision causes over-revocation (safe direction) |
| I-CC03 | LOW | Cross-cutting | No formal O(n) bound verification for queue operations (bounded by `maxExtraCaps` in practice) |

### Positive Findings

- 14-conjunct `ipcInvariantFull` bundle covers all critical IPC properties
- Confused-deputy prevention: `endpointReply` validates `replier == replyTarget`
- `donationBudgetTransfer` prevents CPU budget double-spending
- Grant right gate correctly checked before any capability transfer
- All send paths enforce `maxMessageRegisters` and `maxExtraCaps` bounds
- Single-core, interrupts-disabled model eliminates concurrency races


---

## 4. Capability Subsystem

**Files**: 5 files under `SeLe4n/Kernel/Capability/` (~3,800+ lines)
**sorry/axiom**: Zero

### Findings

| ID | Severity | File | Description |
|----|----------|------|-------------|
| C-CAP01 | MEDIUM | Operations.lean:77-84 | CSpace traversal rights check intentionally omitted (seL4 divergence); rights enforced at operation layer; not machine-checked across all call sites |
| C-CAP06 | MEDIUM | Invariant/Defs.lean:87-119 | `cdtMintCompleteness` not included in main `capabilityInvariantBundle`; revocation via `cspaceRevokeCdt` may miss orphaned capabilities if mint-tracking preservation is incomplete |
| C-CAP07 | MEDIUM | Invariant/Defs.lean:162-168 | CDT acyclicity via externalized post-state hypothesis — deferred to cross-subsystem composition layer |
| C-CAP03 | LOW | Operations.lean:856-875 | `cspaceRevokeCdt` materializes full descendant list (O(maxObjects) memory); streaming variant exists |
| C-CAP04 | LOW | Operations.lean:695-714 | `cspaceMove` delete-before-CDT-fix ordering is correct by construction; atomicity theorem proves error-path safety |

### Positive Findings

- Authority monotonicity proven: `mintDerivedCap` always produces attenuated capabilities
- Badge OR-merge idempotency proven end-to-end through mint→signal→wait path
- Complete preservation coverage: all 14 major CSpace operations have preservation theorems
- `lifecycleAuthorityMonotonicity_holds` formally proves delete leaves no authority in deleted slot


---

## 5. Information Flow Subsystem

**Files**: 8 files under `SeLe4n/Kernel/InformationFlow/` (~5,800+ lines)
**sorry/axiom**: Zero

### Findings

| ID | Severity | File | Description |
|----|----------|------|-------------|
| IF-01 | MEDIUM | Policy.lean:49-79 | **Non-standard integrity model (intentional, not BIBA)**: `integrityFlowsTo` is called with reversed arguments in `securityFlowsTo` (`dst.integrity, src.integrity`), allowing trusted destinations to accept untrusted sources. This is a **deliberate documented design choice** for authority-delegation semantics, NOT a vulnerability. Formally proved different from BIBA (`integrityFlowsTo_is_not_biba`, line 115) and proved to prevent escalation (`integrityFlowsTo_prevents_escalation`, line 157). `DomainFlowPolicy` provides standard BIBA alternative. **Deployment risk**: system integrators expecting standard BIBA will get different integrity guarantees. |
| IF-02 | **HIGH** | Policy.lean:219-226 | **Default labeling context defeats all IF enforcement**: assigns `publicLabel` to all entities, making `securityFlowsTo` trivially true for all pairs (proven by `defaultLabelingContext_insecure`, line 240). Code includes explicit production warning (lines 215-219). Production deployments MUST override. |
| IF-03 | MEDIUM | Projection.lean:256-288 | Scheduling state covert channel (accepted): 4 scheduling fields unconditionally visible to ALL observers; bandwidth bounded to <400 bits/second; matches seL4 design |
| IF-04 | MEDIUM | Projection.lean:106-122 | Service registry projection coverage gap: service-layer internal state not captured by NI projection model |
| IF-13 | MEDIUM | Invariant/Composition.lean:312-476 | NI proof structure is one-sided (projection preservation); sound for current operation set but extending to operations that modify observable state differently based on non-observable state requires different proof strategy |
| IF-14 | MEDIUM | Invariant/Composition.lean:535-592 | `LabelingContextValid` coherence is deployment requirement, NOT enforced at runtime |
| IF-07 | LOW | Enforcement/Wrappers.lean:286 | `native_decide` used for enforcement completeness (technically weaker than `decide` but sound in Lean 4) |
| IF-09 | LOW | Enforcement/Wrappers.lean:28-43 | Bounds checked before flow check — attacker can distinguish "bounds exceeded" from "flow denied" (1-bit leakage, minimal) |

### Positive Findings

- All 11 policy-gated wrappers have 5-property enforcement soundness proofs
- 32-constructor `NonInterferenceStep` covers all operation types
- Declassification requires normal flow to be DENIED — prevents misuse
- TCB register context correctly stripped during projection
- Machine timer correctly excluded from `ObservableState` (prevents timing channel)


---

## 6. Architecture & Platform Layer

**Files**: 10 Architecture files, 13 Platform files (~3,500+ lines)
**sorry/axiom**: Zero

### Findings

| ID | Severity | File | Description |
|----|----------|------|-------------|
| A-T01 | **HIGH** | TlbModel.lean:168-188 | Full TLB flush on every map/unmap; no production entry point uses targeted flushes. When transitioning to per-ASID/per-VAddr flush for H3, composition theorems for targeted variants do not yet exist — risk of introducing bugs not caught by current proof surface. |
| A-SA01 | **HIGH** | SyscallArgDecode.lean:228-237 | `decodeVSpaceUnmapArgs` does NOT validate VAddr canonicity (unlike `decodeVSpaceMapArgs`). Non-canonical VAddr fails safely (returns `translationFault`), but defense-in-depth gap. |
| A-V01 | MEDIUM | VSpace.lean:192-198 | `vspaceMapPageCheckedWithFlush` uses model-default 2^52 PA bound, not platform-specific; the non-platform-aware variant is public and accessible |
| A-IB01 | MEDIUM | IpcBufferValidation.lean:49-70 | No explicit check that IPC buffer region (`addr` to `addr + ipcBufferSize`) fits within a single mapped page |
| A-SA02 | MEDIUM | SyscallArgDecode.lean:146 | `Slot.ofNat` may silently accept out-of-range values depending on Prelude definition |
| A-SA03 | MEDIUM | SyscallArgDecode.lean:148 | `AccessRightSet.ofNat` silently masks to 5 bits (inconsistent with `PagePermissions.ofNat?` which rejects) |
| A-V02 | LOW | VSpace.lean:90 | Default permission is `readOnly` — safe (least privilege, W^X compliant) |
| A-VI02 | LOW | VSpaceInvariant.lean:293-305 | Success-path preservation requires many external preconditions |
| A-IB02 | LOW | IpcBufferValidation.lean:86-104 | Double TCB lookup (harmless in pure model) |
| A-RD01 | LOW | RegisterDecode.lean:78-80 | Word64 bound check is model-only (trivially satisfied on ARM64 hardware) |
| A-RC01 | LOW | RPi5/RuntimeContract.lean:79 | Pre-state parameter unused (documented, correct) |

### Positive Findings

- W^X enforcement: `PagePermissions.ofNat?` rejects at decode, `wxCompliant` proven for `readOnly` default
- All BCM2712 addresses validated against datasheets with disjointness proofs
- RegisterDecode is total and deterministic over all 25 SyscallId variants
- Triple-bounded message register extraction (defense-in-depth)
- Boot sequence is deterministic with checked variant rejecting duplicate IRQs/OIDs
- All platform contracts (Sim + RPi5) have complete proof hooks


---

## 7. Data Structures

**Files**: 14 files (RobinHood 7, RadixTree 4, FrozenOps 5) (~7,500 lines)
**sorry/axiom**: Zero

### Findings

| ID | Severity | File | Description |
|----|----------|------|-------------|
| D-RH01 | **HIGH** | RobinHood/Bridge.lean:361,858 | `insert_size_lt_capacity` requires `4 ≤ capacity` — not enforced at construction. `RHTable.empty` accepts `cap = 1`. Kernel code uses `invExtK` (which includes the guard), but the public `invExt` API lacks it. |
| D-RT01 | **HIGH** | RadixTree/Bridge.lean:317,420 | `buildCNodeRadix_lookup_equiv` requires `UniqueRadixIndices` + `hNoPhantom` — discharge depends on caller-side key boundedness not enforced by the type system |
| D-RH02 | MEDIUM | RobinHood/Core.lean:119,179,233 | Fuel exhaustion returns silent defaults (dropping entries, returning none) — correct under invariants but no defense-in-depth |
| D-RH03 | MEDIUM | RobinHood/Bridge.lean:666,746 | Proofs requiring 400K–800K heartbeats indicate fragility to Lean version upgrades |
| D-RH04 | MEDIUM | RobinHood/Invariant/Preservation.lean:1772-2110 | `relaxedPCD` technique (340 lines) is correct but lacks strategic documentation for maintainability |
| D-FO01 | MEDIUM | FrozenOps/Core.lean:181-230 | `frozenQueuePushTailObjects` partial mutation on intermediate failure (lookups fail after some writes applied) |
| D-RH05 | LOW | RobinHood/Core.lean:291 | `erase` unchecked `size - 1` (safe under WF invariant, Nat floors at 0) |
| D-RH06 | LOW | RobinHood/Invariant/Lookup.lean:1026-1200 | Verbose 174-line case analysis (maintenance burden) |
| D-RT02 | LOW | RadixTree/Core.lean:32 | `extractBits` correctness verified — `extractBits_lt` and `extractBits_identity` both proven |

### Positive Findings

- `probeChainDominant` correctly supersedes `robinHoodOrdered` for erase preservation
- Two-phase builder→frozen architecture provides strong immutability guarantees
- FrozenMap `set/get?` roundtrip proofs are complete
- All 24 RadixTree correctness theorems machine-checked
- Frozen operations correctly exclude 5 builder-only SyscallId arms


---

## 8. SchedContext, Lifecycle, Service, CrossSubsystem

**Files**: 25 files (~6,500 lines)
**sorry/axiom**: Zero

### Findings

| ID | Severity | File | Description |
|----|----------|------|-------------|
| SC-02 | MEDIUM | SchedContext/Invariant/Defs.lean:441-470 | CBS bandwidth bound is 8x budget (not 1x) due to `maxReplenishments = 8`; admission control itself is correct |
| SC-03 | MEDIUM | SchedContext/Operations.lean:146-151 | `schedContextBind` doesn't check thread state before run queue migration (relies on external `runnableThreadsAreReady`) |
| SC-04 | MEDIUM | Lifecycle/Suspend.lean:157-158 | Defensive TCB re-lookup after IPC cleanup uses fallback to stale TCB on lookup failure |
| SC-01 | MEDIUM | SchedContext/Types.lean:46 | `Budget.decrement` saturating semantics — verified correct by `consumeBudget_budgetRemaining_le` theorem |
| SC-L01 | LOW | SchedContext/Types.lean:50 | `Budget.refill` name misleading — caps down, not refills up (unused by CBS engine) |
| SC-L03 | LOW | SchedContext/Operations.lean:219 | `schedContextYieldTo` is pure function, not `Kernel` monad — silent-failure semantics differ from other ops |
| SC-L04 | LOW | SchedContext/Operations.lean:105 | `schedContextConfigure` resets `budgetRemaining` to full budget — capability-gated, but allows runtime window extension |
| SC-L06 | LOW | Lifecycle/Suspend.lean:210-211 | `resumeThread` uses TCB priority instead of effective priority for preemption check — worst case is missed preemption corrected at next tick |
| SC-L07 | LOW | Service/Operations.lean:149 | `serviceHasPathTo` self-match returns true (correct for cycle detection use case) |
| SV-01 | LOW | Service/Invariant/Acyclicity.lean | Acyclicity preservation proof chain is genuine and complete |
| CS-01 | LOW | CrossSubsystem.lean | `collectQueueMembers` fuel sufficiency is informal — `QueueNextPath` connection deferred |

### Positive Findings

- 8-predicate `crossSubsystemInvariant` with 28 pairwise field-disjointness analysis verified by `native_decide`
- MCP authority validation sound (`validatePriorityAuthority`)
- Service registry acyclicity proven via BFS completeness bridge
- All 25 SyscallId variants wired in API dispatch (dead wildcard arm documented)
- Replenishment queue sorted-insert invariant preserved by all operations
- `lifecyclePreRetypeCleanup` correctly orders SchedContext donation cleanup before TCB reference cleanup


---

## 9. Rust Implementation

**Files**: 30 files across 3 crates (`sele4n-types`, `sele4n-abi`, `sele4n-sys`)
**unsafe blocks**: 1 (justified `svc #0` trap)

### ABI Consistency Verification

| Type | Lean | Rust | Status |
|------|------|------|--------|
| KernelError | 44 variants (0-43) | 44 variants `#[repr(u32)]` | **MATCH** |
| SyscallId | 25 variants (0-24) | 25 variants `#[repr(u64)]` | **MATCH** |
| AccessRight | 5 variants, toBit 0-4 | 5 variants, `#[repr(u8)]` | **MATCH** |
| KernelObjectType | 7 variants (0-6) | TypeTag 7 variants `#[repr(u64)]` | **MATCH** |
| MessageInfo bits | len[0:6], ec[7:8], label[9:28] | Identical | **MATCH** |
| Register layout | x0=cap, x1=msginfo, x2-5=msg, x7=syscall | Identical (idx 6 = x7) | **MATCH** |
| maxMessageRegisters | 120 | MAX_MSG_LENGTH = 120 | **MATCH** |
| maxExtraCaps | 3 | MAX_EXTRA_CAPS = 3 | **MATCH** |
| maxLabel | 2^20 - 1 | MAX_LABEL = (1<<20)-1 | **MATCH** |

### Findings

| ID | Severity | File | Description |
|----|----------|------|-------------|
| R-F01 | MEDIUM | sele4n-abi/args/sched_context.rs:16,29 | Register mapping comment says "x6=domain" but x6 is not in the ABI register array (`[x0,x1,x2-x5,x7]` — x6 skipped). The 5th field (domain) is correctly handled on the Lean side via IPC buffer overflow (`requireMsgReg decoded.msgRegs 4`). Rust `encode()` returns `[u64; 5]` but `SyscallRequest.msg_regs` is `[u64; 4]` — `sele4n-sys` wrapper must use IPC buffer overflow pattern. Comment should read "overflow[0]=domain". |
| R-F02 | MEDIUM | sele4n-sys/tcb.rs:49-98 | `tcb_set_priority`, `tcb_set_mcp`, `tcb_set_ipc_buffer` pass raw `u64` without client-side validation — causes unnecessary kernel traps for invalid inputs |
| R-F03 | MEDIUM | sele4n-sys/service.rs:31-46 | `service_register` does not validate `method_count` bounds client-side |
| R-F04 | LOW | sele4n-sys/ipc.rs:180 | `endpoint_reply_recv` sends stale register values beyond `msg.length` (no security impact) |
| R-F05 | LOW | sele4n-abi/decode.rs:42 | Unknown kernel error codes conflated with `InvalidSyscallNumber` |
| R-F06 | LOW | sele4n-sys/lifecycle.rs:15 | Doc comment omits SchedContext (TypeTag variant 6) |
| R-F07 | LOW | sele4n-types/identifiers.rs:102 | `Slot::MAX_VALID = u32::MAX` is Rust-side modeling assumption |
| R-F08 | LOW | sele4n-abi/ipc_buffer.rs:55 | `IpcBuffer` is 960 bytes on stack — document placement guidance for embedded |

### Positive Findings

- All GitHub Actions SHA-pinned; all downloads SHA-256 verified
- Single `unsafe` block is sound (ARM64 `svc #0` with correct clobber spec)
- `#![no_std]`, `#![deny(unsafe_code)]` on all crates; zero heap allocations
- `decode_response()` correctly guards against u64→u32 truncation
- `PagePerms::validate_wx()` enforced before VSpace syscalls
- Phantom-typed capability handles with sealed trait pattern


---

## 10. Test Infrastructure & Build System

**Files**: 16 test suites, 5 testing helpers, 10+ scripts, lakefile, CI workflow
**sorry/axiom in tests**: Zero

### Findings

| ID | Severity | File | Description |
|----|----------|------|-------------|
| T-F01 | **HIGH** | lakefile.toml / all test scripts | **PriorityInheritanceSuite is compiled but NEVER executed** by any test tier. 20+ PIP tests covering propagation, blocking chains, reversion, and SchedContext integration are dead tests. Any regression in PIP behavior goes undetected. |
| T-F02 | MEDIUM | tests/TraceSequenceProbe.lean:63-70 | State built with raw struct construction, bypassing `buildChecked` validation |
| T-F03 | MEDIUM | tests/SuspendResumeSuite.lean:38 + PriorityManagementSuite.lean:43 | `mkState` uses unchecked `.build` instead of `.buildChecked` |
| T-F05 | MEDIUM | tests/LivenessSuite.lean | All 58 "tests" are `#check` anchors only — no behavioral execution; catches signature regressions but not behavioral regressions |
| T-F08 | MEDIUM | scripts/test_tier2_trace.sh:30 | `TRACE_ARTIFACT_DIR` not path-validated (accepts any path; theoretical write to arbitrary locations) |
| T-F17 | MEDIUM | scripts/test_rust.sh:19-27 | Silently exits 0 when `cargo` is missing — Rust ABI tests skipped without failing CI |
| T-F04 | LOW | tests/NegativeStateSuite.lean:1722 | Intentional `.build` use for mismatch state could use clearer annotation |
| T-F06 | LOW | scripts/pre-commit-lean-build.sh:82-84 | Test files (`tests/*`) excluded from pre-commit module-build check |
| T-F07 | LOW | scripts/setup_lean_env.sh:128-134 | Generic `sudo` wrapper (current usage safe with hardcoded args) |
| T-F09 | LOW | scripts/test_tier4_nightly_candidates.sh:26 | Fixed artifact path instead of `mktemp` (stale artifacts on interruption) |
| T-F11 | LOW | Testing/StateBuilder.lean:163 | `.toNat` comparison instead of structural `==` for ThreadId |
| T-F20 | LOW | scripts/test_tier0_hygiene.sh:20 | `bash -lc` wrapper may source unexpected profiles |

### Positive Findings

- All GitHub Actions SHA-pinned with version comments
- elan installer + toolchain downloads SHA-256 verified (supply-chain hardening)
- All scripts use `set -euo pipefail` consistently
- `BootstrapBuilder` provides checked/unchecked/validated construction paths
- Fixture hash integrity check in trace tests (SHA-256 companion file)
- Zero external Lean dependencies — eliminates supply-chain risk
- Cache keys include `lean-toolchain`, `lake-manifest.json`, `lakefile.toml`, `setup_lean_env.sh`


---

## 11. Cross-Cutting Analysis

### 11.1 sorry/axiom Compliance

**PASS** — Zero instances across all 150 Lean source files. Verified by automated grep across the entire `SeLe4n/` directory and all test files.

### 11.2 native_decide Usage

Limited to two justified cases:
1. `Enforcement/Wrappers.lean:286` — enforcement boundary completeness over finite `SyscallId` enum
2. `CrossSubsystem.lean` — field-disjointness analysis over 28 pairwise relationships

Both operate on finite, compile-time-bounded types. Sound in Lean 4's proof system.

### 11.3 Deterministic Semantics

All kernel transitions are pure functions returning explicit success/failure. No `IO`, no `StateT IO`, no randomness. The only `IO` usage is in `Main.lean` (test harness entry point) and test executables. The kernel model is fully deterministic.

### 11.4 Invariant Architecture

The kernel uses a layered invariant composition:
- **Per-subsystem bundles**: `schedulerInvariantBundleExtended` (15), `ipcInvariantFull` (14), `capabilityInvariantBundle` (6), `vspaceInvariantBundle` (5), `proofLayerInvariantBundle` (10), `schedContextInvariantBundle` (4)
- **Cross-subsystem**: `crossSubsystemInvariant` (8) with 28 pairwise field-disjointness analysis
- **Frozen-phase**: `apiInvariantBundle_frozenDirect` for post-freeze mutations

Preservation chains exist for all major operations. The externalized-hypothesis pattern (IPC, Capability, Architecture) defers some proof obligations to the cross-subsystem/API layer, which is architecturally correct but creates a distributed proof burden.

### 11.5 Covert Channel Summary

| Channel | Status | Bandwidth |
|---------|--------|-----------|
| Scheduling state (domain, timer) | Accepted | <400 bits/s |
| Service registry | Not modeled | Unknown |
| Machine timer | Excluded from projection | Blocked |
| TCB register context | Stripped in projection | Blocked |

### 11.6 Concurrency Model

Single-core, interrupts disabled during kernel transitions. No concurrency races possible in the formal model. Hardware binding must enforce this assumption (GIC-400 interrupt masking on RPi5).

### 11.7 Verification Methodology

All HIGH findings and selected MEDIUM findings were independently verified in a second pass:
- Each finding's cited line numbers were re-read against the actual source code
- Code snippets were extracted and compared to the finding's characterization
- One finding (IF-01, non-standard BIBA) was **downgraded from HIGH to MEDIUM** after verification revealed it is an intentional, formally-witnessed design choice — not a flaw
- One finding (R-F01, SchedContext register mapping) was **refined** after verification confirmed the comment is incorrect about x6 but the Lean kernel correctly handles the 5th field via IPC buffer overflow
- One finding (I-T01, timeout magic value) was **refined** to note the composite AND condition (register + state) that mitigates false positives
- All other HIGH findings were confirmed accurate with exact code citations added

---

## 12. Consolidated HIGH Findings

### HIGH-1: Default Labeling Context Insecure (IF-02)
- **Location**: `InformationFlow/Policy.lean:219-226`
- **Impact**: All IF enforcement is trivially defeated with default labels. Proven by `defaultLabelingContext_insecure` (line 240).
- **Mitigation**: Formal insecurity witness exists. SA-2 advisory referenced. Production MUST override.
- **Verified**: Code at lines 220-226 assigns `publicLabel` to all entities. Theorem at line 240 proves `securityFlowsTo` is trivially true for all pairs.

### HIGH-2: TLB Targeted Flush Transition Risk (A-T01)
- **Location**: `Architecture/TlbModel.lean:168-188`
- **Impact**: `vspaceMapPageWithFlush` (line 168) and `vspaceUnmapPageWithFlush` (line 183) both use `adapterFlushTlb` (full TLB invalidation). Targeted variants (`adapterFlushTlbByAsid`, `adapterFlushTlbByVAddr`) exist but no production entry point uses them. Transitioning to targeted flushes for H3 requires composition theorems that do not yet exist.
- **Mitigation**: Current behavior is conservative (full flush). Add targeted flush composition theorems before H3.
- **Verified**: Lines 168-174 and 183-188 both call `adapterFlushTlb`. Comment at lines 181-182 acknowledges conservatism.

### HIGH-3: VAddr Canonicity Not Checked on Unmap (A-SA01)
- **Location**: `Architecture/SyscallArgDecode.lean:228-237`
- **Impact**: `decodeVSpaceMapArgs` validates canonicity (line 213: `if !vaddr.isCanonical`), but `decodeVSpaceUnmapArgs` does not (line 237: constructs result directly with `VAddr.ofNat r1.val`). Non-canonical VAddr fails safely via `translationFault` in VSpace layer, but produces a confusing error rather than `addressOutOfBounds`.
- **Mitigation**: Add `if !vaddr.isCanonical then .error .addressOutOfBounds` for consistency.
- **Verified**: Map decode has canonicity check at line 213; unmap decode at line 237 lacks it.

### HIGH-4: RobinHood `invExt` API Lacks `4 ≤ capacity` Guard (D-RH01)
- **Location**: `RobinHood/Bridge.lean:361,858`, `RobinHood/Core.lean:91`
- **Impact**: `insert_size_lt_capacity` (line 361) requires `hCapGe4 : 4 ≤ t.capacity`. `invExtK` (line 858) includes this guard. But `RHTable.empty` (Core.lean:91) accepts any `cap > 0`, and `invExt` (Preservation.lean:447) does not include the `4 ≤ capacity` constraint. A table created with `cap = 1` using `invExt` would bypass the guard.
- **Mitigation**: Unify on `invExtK` or add `4 ≤ cap` to `RHTable.empty`.
- **Verified**: All four code locations confirmed.

### HIGH-5: RadixTree Bridge Precondition Not Type-Enforced (D-RT01)
- **Location**: `RadixTree/Bridge.lean:317-324,420-434`
- **Impact**: `buildCNodeRadix_lookup_equiv` (line 317) requires `UniqueRadixIndices` and `hNoPhantom`. `uniqueRadixIndices_sufficient` (line 420) shows these are automatically satisfied when keys are bounded by `2^radixWidth`, but this bound is NOT enforced by the type system — it is a caller-side proof obligation.
- **Mitigation**: Add bounded key type or runtime check in `buildCNodeRadix`.
- **Verified**: Lines 406-419 document the sufficiency chain explicitly.

### HIGH-6: PriorityInheritanceSuite Never Executed (T-F01)
- **Location**: `lakefile.toml:75-78`, `scripts/test_tier2_negative.sh`
- **Impact**: `priority_inheritance_suite` is registered as an executable (lakefile.toml:76) but never invoked by any test script. `test_tier2_negative.sh` executes D1 (suspend_resume), D2 (priority_management), D3 (ipc_buffer), and D5 (liveness) suites, but **skips D4** entirely. 20+ PIP tests are dead.
- **Mitigation**: Add `run_check "TRACE" lake exe priority_inheritance_suite` to `test_tier2_negative.sh`.
- **Verified**: Grep for `priority_inheritance` across all scripts returns zero hits. Gap visible in test_tier2_negative.sh between D3 and D5.

---

## 13. Recommendations

### Priority 1 — Before Hardware Binding (H3)

1. **[HIGH-6] Execute PriorityInheritanceSuite**: Add to Tier 2 test script. Single-line fix with immediate coverage gain for a security-critical subsystem.
2. **[HIGH-3] Add VAddr canonicity check to `decodeVSpaceUnmapArgs`**: One `if !vaddr.isCanonical` guard for consistency with map decode.
3. **[HIGH-2] Add targeted TLB flush composition theorems**: Required before switching from full-flush to per-ASID/per-VAddr.
4. **[HIGH-4] Unify RobinHood on `invExtK`**: Either mark `invExt` private or add `4 ≤ capacity` to `RHTable.empty`.
5. **[HIGH-5] Add key bounds enforcement to `buildCNodeRadix`**: Runtime check or refined key type.

### Priority 2 — Before Production Deployment

6. **[HIGH-1] Override default labeling**: Deployment guide must prominently document mandatory labeling override and the non-standard integrity model (IF-01: `DomainFlowPolicy` provides standard BIBA alternative).
7. **[I-T01] Replace timeout magic value**: Use out-of-band `timedOut : Bool` TCB field instead of `0xFFFFFFFF` sentinel. The current composite check (register + state) mitigates false positives but is fragile for hardware binding.
8. **[I-WC01] Generalize cap transfer slot**: Address slot-0-only simplification for real CSpace usage.
9. **[R-F01] Fix SchedContext args register comment**: Change "x6=domain" to document IPC buffer overflow for 5th field. Ensure `sele4n-sys` wrapper follows `service_register()` overflow pattern.
10. **[S-07] Strengthen WCRT liveness**: Prove or document the two external hypotheses (`hDomainActiveRunnable`, `hBandProgress`).

### Priority 3 — Assurance Strengthening

11. **[C-CAP06] Include `cdtMintCompleteness` in main bundle** or verify preservation for all CDT-modifying operations.
12. **[D-FO01] Refactor `frozenQueuePushTailObjects`**: Validate all lookups before performing writes to prevent partial state corruption on intermediate failure.
13. **[SC-L04] Preserve `min(oldBudgetRemaining, newBudget)` on reconfigure** to prevent capability-gated runtime window extension.
14. **[SC-L06] Use `getCurrentPriority` for preemption check** in `resumeThread` (currently uses TCB priority, missing SchedContext effective priority).
15. **[S-06] Tighten PIP inversion bound** to use `countTCBs` or `maxBlockingDepth` instead of `objectIndex.length`.

### Priority 4 — Maintenance & Documentation

16. Update `CLAUDE.md` large-file size for `Structural.lean` (now ~7591 lines, documented as ~2345).
17. Add strategic documentation to `relaxedPCD` technique (10-15 line block comment explaining gap-and-backshift proof strategy).
18. Factor high-heartbeat proofs (400K-800K) into intermediate lemmas to reduce Lean version upgrade fragility.
19. Change test suites to use `buildChecked` (T-F02, T-F03) — `TraceSequenceProbe`, `SuspendResumeSuite`, `PriorityManagementSuite`.
20. Add at least one `assertStateInvariantsWithoutSync` test per subsystem to detect operational drift.

---

## Appendix: Files Audited

**Lean modules**: 150 files (all `.lean` files excluding `.lake/`)
**Rust source**: 30 files across `sele4n-types`, `sele4n-abi`, `sele4n-sys`
**Scripts**: 10+ shell scripts under `scripts/`
**CI**: `.github/workflows/lean_action_ci.yml`
**Build**: `lakefile.toml`, `lean-toolchain`

---

*This audit was conducted as a pre-release comprehensive review of the seLe4n v0.25.12 kernel, covering all 150 Lean modules, 30 Rust source files, test infrastructure, and build system. Every HIGH finding was independently verified against source code after initial discovery. The audit found zero `sorry`/`axiom` usage, zero CVE-worthy vulnerabilities, and a mature verification infrastructure. The 6 HIGH findings are defense-in-depth gaps (4), a deployment requirement (1), and a test coverage gap (1) — none are exploitable vulnerabilities in the current codebase.*

