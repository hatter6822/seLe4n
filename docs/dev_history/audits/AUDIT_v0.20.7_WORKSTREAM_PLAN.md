# WS-U Workstream Plan — v0.20.7 Audit Remediation

**Created**: 2026-03-24
**Baseline version**: 0.20.7
**Baseline audits**:
- `docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.20.7_FULL_CODEBASE.md` (5 HIGH, 26 MEDIUM, 33 LOW)
- `docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.20.7_KERNEL_IMPLEMENTATION.md` (2 HIGH, 22 MEDIUM, 60+ LOW)
- `docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.20.7_PRE_RELEASE.md` (13 HIGH, 37 MEDIUM, 43 LOW)
- `docs/dev_history/audits/audit_findings_provided_by_me.md` (user-reported findings)
**Prior portfolios**: WS-B through WS-T (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Executive Summary

Four comprehensive audits of seLe4n v0.20.7 were conducted on 2026-03-24: a full
codebase audit (9 parallel agents), a kernel implementation audit (line-by-line),
a pre-release audit (8 parallel agents), and user-reported manual findings. Cross-
referencing and independent verification of every finding against the actual
codebase identified **12 erroneous findings** that do not reflect real defects.
All remaining findings were confirmed with code-level evidence.

After deduplication across all four audits and removal of erroneous findings,
the consolidated registry contains:

| Severity | Count | Description |
|----------|-------|-------------|
| **HIGH** | 14 | Correctness bugs, safety gaps, security-critical missing checks |
| **MEDIUM** | 39 | Design gaps, proof obligation deferrals, spec divergences |
| **LOW** | 28 | Dead code, documentation, hardening opportunities |
| **Info** | — | Excluded from remediation (positive observations only) |

**No CVE-worthy vulnerabilities were discovered.** The HIGH findings represent
correctness bugs (2), safety gaps in internal API exposure (3), missing bounds
checks at hardware boundaries (3), proof chain gaps (3), and Rust ABI defects (3).

This workstream plan organizes all actionable findings into **8 phases** (U1–U8)
with **97 atomic sub-tasks** (further decomposed into **~180 discrete sub-steps**
for Large and complex Medium tasks), explicit dependencies, gate conditions, and
scope estimates. The plan addresses all 14 HIGH findings, all 39 MEDIUM findings,
and selects 28 LOW findings for inclusion based on security relevance, proof chain
completeness, and hardware readiness. Each Large task includes a structural
decomposition with per-field, per-conjunct, or per-operation granularity derived
from investigation of the actual codebase.

---

## 2. Erroneous Finding Registry

The following findings were reported by one or more audits but determined to be
**incorrect** after verification against the actual codebase. They are excluded
from remediation.

| Audit ID(s) | Claimed Finding | Verification Result |
|-------------|----------------|---------------------|
| M-08, AR-12 (partial) | `readBE32` uses panic-capable `get!` without bounds check | **ERRONEOUS**: Bounds check `offset + 4 ≤ blob.size` at line 182 precedes all `get!` calls. Access is provably safe. |
| AR-07 | GIC base addresses fall outside declared device memory region | **ERRONEOUS**: GIC Distributor (0xFF841000) and CPU Interface (0xFF842000) both fall within device region [0xFE000000, 0xFF850000). |
| M-11 | Duplicate frame lemmas between `Commutativity.lean` and `Invariant.lean` | **ERRONEOUS**: Names differ by prime suffix (`cdtNodeSlot` vs `cdtNodeSlot'`). These prove different properties for different FrozenMap fields. |
| User | GIC CPU interface size discrepancy | **ERRONEOUS**: Size 0x2000 (8 KB) is correct per ARM GIC-400 specification. |
| User | CSpace mint/copy/move constrained to same CNode | **ERRONEOUS**: `cspaceMint`, `cspaceCopy`, `cspaceMove` accept independent `CSpaceAddr` records with separate `cnode` fields. Cross-CNode operations work correctly. |
| H-02 (severity) | API dispatch duplication rated HIGH | **DOWNGRADED to MEDIUM**: Duplication is a code quality/maintenance concern, not a correctness or security bug. Both paths serve distinct purposes (checked vs unchecked entry). |
| DS-01/D-03 (partial) | RHSet public fields allow direct construction bypassing invariants | **CLARIFIED**: RHSet is a thin wrapper (`table : RHTable κ Unit`). Not bundling invariants is the actual finding; "public fields" is how Lean structs work. The remediation is creating `KSet` (confirmed finding). |
| User | Missing `notificationSignal`, `replyRecv`, `nbSend`, `nbRecv` syscalls | **PARTIALLY ERRONEOUS**: These operations are not in the v0.20.7 `SyscallId` enum by design. `notificationSignal` is mentioned in a docstring but intentionally not yet wired. These are deferred features for WS-V (hardware binding), not missing implementations. The docstring inconsistency is a confirmed LOW finding. |
| F-05, G-03 (partial) | `RegisterFile.BEq` non-lawful is a defect | **CLARIFIED**: Explicitly documented as non-lawful by design. No proofs depend on `LawfulBEq RegisterFile`. The remediation is adding negative instances to prevent accidental misuse (confirmed MEDIUM). |
| SC-01 (severity) | `switchDomain` context loss rated HIGH | **DOWNGRADED to MEDIUM**: `switchDomain` is only called from `scheduleDomain`, which calls `schedule` first. `schedule` calls `saveOutgoingContext` before any thread dispatch. Context is saved by the caller, not lost. Defensive fix still warranted. |
| S-05 | `handleYield` no priority check is a finding | **ERRONEOUS**: Matches seL4 semantics exactly. Unconditional move-to-back is the correct behavior. |
| P-04 | Simulation boot contracts trivially `True` | **BY DESIGN**: Simulation platform intentionally uses vacuous contracts. Proofs are validated under restrictive contracts (RPi5). Not a defect. |

---

## 3. Consolidated Finding Registry

All findings below are **confirmed** against the actual codebase with line-number
evidence. Duplicate findings across the four audits are merged under a single
canonical ID. Source audit cross-references are provided for traceability.

### 3.1 HIGH Findings (14)

| ID | Sources | Subsystem | Description |
|----|---------|-----------|-------------|
| U-H01 | H-01, DS-06 | FrozenOps | `frozenQueuePopHead` clears `queuePrev`/`queueNext` but NOT `queuePPrev`. `frozenQueuePushTail` rejects threads with `queuePPrev.isSome`. A popped thread cannot be re-enqueued — breaks multi-round IPC in frozen phase. |
| U-H02 | A-01, LF-01 | Lifecycle | `retypeFromUntyped` does not re-verify watermark page alignment after advancing by `allocSize`. Non-page-aligned allocations shift the watermark to an unaligned base, violating S5-G safety guarantee. |
| U-H03 | A-02 | Lifecycle | `cspaceDeleteSlot` (lines 555-568 in `Capability/Operations.lean`) relies on caller having first called `revokeCap`. No compile-time enforcement or runtime guard — `revokeBeforeDelete` is a proof obligation, not a code check. There is no standalone `deleteObject` function; CDT deletion logic lives in `cspaceDeleteSlot`. |
| U-H04 | User | API | `dispatchWithCap` and `dispatchWithCapChecked` both route lifecycle retype through `lifecycleRetypeDirect`, which bypasses `lifecyclePreRetypeCleanup` and `scrubObjectMemory`. Cleanup documented as "handled separately" but never performed. |
| U-H05 | AR-01, M-12 | Architecture | `vspaceMapPage` is public and performs no TLB flush. Doc-comment warns against direct use but no access restriction. `lifecycleRetypeObject` similarly public without cleanup/scrub. |
| U-H06 | User | Architecture | Virtual address not bounds-checked in VSpace map operations. Unbounded `VAddr` can exceed 2^48, creating model-reality gap on ARM64. `vspaceMapPageChecked` only validates paddr, not vaddr. |
| U-H07 | User, AR-04 | Architecture | `physicalAddressBound = 2^52` (ARM64 LPA) vs BCM2712's 44-bit PA. Addresses in [2^44, 2^52) pass model validation but are invalid on RPi5. DeviceTree `fromDtbWithRegions` also hardcodes 48-bit PA. |
| U-H08 | User | Architecture | ASID not bounds-checked against `maxASID` (65536) at decode boundary. `ASID.ofNat` performs unchecked modular wrapping. |
| U-H09 | IF-01, IF-08 | InfoFlow | NI proofs for 4 IPC operations (`endpointSendDual`, `endpointReceiveDual`, `endpointCall`, `endpointReplyRecv`) carry externalized `hProjection` hypotheses. These are declared but never invoked — NI for IPC is vacuously true if no caller discharges them. |
| U-H10 | IF-03 | InfoFlow | `NonInterferenceStep` 33-constructor completeness is manually maintained. Adding a new kernel operation without a corresponding NI constructor silently weakens the guarantee. No automated enforcement. |
| U-H11 | RS-01 | Rust | `svc #0` inline asm in `trap.rs` only handles x0-x7 and x6 as lateout. Registers x8-x18 not declared as clobbered. Silent register corruption if kernel modifies x8-x18. |
| U-H12 | D-01, M-03 | RobinHood | `BEq RHTable` instance folds over table `a` checking `b`, but NOT the reverse. Two semantically equal tables with different probe chains may compare unequal. Instance is not provably symmetric. |
| U-H13 | IP-02 | IPC | Missing sender CSpace root in `endpointReceiveDual` falls back to `senderId.toObjId` as CNode root. Unreachable under invariants but silently proceeds rather than returning error — could mask bugs. |
| U-H14 | User | Capability | Retype right mismatch: API dispatch maps `.lifecycleRetype` to required right `.retype` (API.lean:295), but `lifecycleRetypeAuthority` gate check requires `.write` (Lifecycle/Operations.lean:21). Inconsistent access control. |

### 3.2 MEDIUM Findings (39)

| ID | Sources | Subsystem | Description |
|----|---------|-----------|-------------|
| U-M01 | AR-02 | API | Checked/unchecked dispatch diverge for `.call` syscall. Checked version adds inline `securityFlowsTo` guard not present in unchecked path. |
| U-M02 | H-02 | API | `dispatchWithCap` and `dispatchWithCapChecked` duplicate ~320 lines with 14 match arms each. Maintenance hazard — changes must be applied in both places. |
| U-M03 | M-10 | API | Badge value 0 treated as "no badge" (`if args.badge.val = 0 then none`). Cannot explicitly set badge 0 — semantic surprise. |
| U-M04 | AR-06 | API | Reply dispatch skips IF check with comment "reply cap is single-use authority." Correct but baked into dispatch layer rather than enforcement layer. |
| U-M05 | M-04 | Service | `serviceGraphInvariant` defined in Acyclicity.lean but NOT wired into `crossSubsystemInvariant` in CrossSubsystem.lean. Acyclicity guarantee exists in isolation from global kernel invariant. |
| U-M06 | M-05 | Service | `cleanupEndpointServiceRegistrations` has `_preserves_registryEndpointValid` but missing `_preserves_registryInterfaceValid` preservation theorem. |
| U-M07 | M-07, AR-12 | Architecture | `decodeVSpaceMapArgs` returns `.policyDenied` for invalid permissions (line 215). Should return `.invalidArgument` — decode error, not policy violation. |
| U-M08 | AR-03, P-02 | Platform | MMIO reads modeled as `st.machine.memory addr` — device registers treated as RAM. Proofs about MMIO read idempotency hold in model but NOT on hardware (reads can clear flags, pop FIFOs). |
| U-M09 | P-01, AR-09, M-13 | Platform | RPi5 `registerContextStable` uses overly permissive disjunct: any `scheduler.current` change satisfies it, even if SP is corrupted. Contract is trivially `True` for all register writes. |
| U-M10 | P-03 | Platform | Only byte-level MMIO writes implemented. ARM64 requires 32-bit aligned writes for GIC registers. No `mmioWrite32`/`mmioWrite64`. |
| U-M11 | M-09 | Platform | DeviceTree `fromDtbWithRegions` hardcodes `physicalAddressWidth := 48`. BCM2712 uses 44-bit PA. Produces incorrect config for RPi5. |
| U-M12 | P-08 | Boot | `foldIrqs` doesn't check for duplicate IRQ registrations. Last-wins semantics undocumented. |
| U-M13 | P-09 | Boot | `foldObjects` doesn't validate object ID uniqueness. Silent overwrite on duplicate IDs. |
| U-M14 | AR-05, A-05 | CrossSubsystem | Composite invariant is conjunction of subsystem invariants. No proof that the conjunction is the *strongest* composite — cross-subsystem properties may be uncaptured. |
| U-M15 | AR-11 | Boot | No single theorem bridging boot invariants to runtime `proofLayerInvariantBundle`. Gap between builder-phase and runtime invariants. |
| U-M16 | G-01, G-02 | Foundation | ~23 `native_decide` uses expand TCB. Project has precedent for migration to `decide`. 3 in Model/Object files are inconsistent with policy. |
| U-M17 | G-03 | Foundation | `BEq RegisterFile` and `BEq TCB` are non-lawful. No negative instances to prevent accidental use in proofs expecting lawful behavior. |
| U-M18 | F-18 | Foundation | `storeObject` is infallible (no capacity check). Capacity enforcement deferred to `retypeFromUntyped`. All call sites need audit for capacity pre-check. |
| U-M19 | ML-01 | Foundation | `descendantsOf` transitive closure fuel sufficiency not proven — only depth-1 children guaranteed. Revocation completeness for deep derivation trees formally open. |
| U-M20 | ML-05 | Foundation | `allTablesInvExt` manually enumerates 16 RHTable fields. A new field could be silently omitted. No automated enforcement. |
| U-M21 | IF-02 | InfoFlow | 7 "capability-only" operations have no runtime flow check. NI relies entirely on proof soundness with no runtime safety net. |
| U-M22 | IF-04 | InfoFlow | Non-standard BIBA integrity direction (write-up allowed). Weaker than standard BIBA. Documented but could mislead consumers. |
| U-M23 | IF-05, IF-06 | InfoFlow | Scheduling state visible to ALL observers (covert timing channel). TCB metadata of unobservable threads visible cross-domain. |
| U-M24 | IF-07 | InfoFlow | Service registry invisible to projection — `registerService` preserves projection unconditionally. Service-layer flows not captured by NI model. |
| U-M25 | CP-01 | Capability | `resolveCapAddress` does not check intermediate capability rights during multi-level CSpace walk. seL4 requires read right for traversal. |
| U-M26 | CP-02 | Capability | CDT-modifying operations take `cdtCompleteness ∧ cdtAcyclicity` as hypothesis rather than proving from pre-state. Composition is conditional on caller. |
| U-M27 | CP-03 | Capability | Local revoke (`cspaceRevoke`) does not clear CDT edges for revoked slots. Stale CDT entries accumulate. |
| U-M28 | I-01 | IPC | `sendIPC` message truncation: sender message silently truncated to buffer size. No error signaled. Matches seL4 but undocumented in API spec. |
| U-M29 | IP-03 | IPC | `notificationSignal` wake path unconditionally overwrites waiter's `pendingMessage`. Stale message from previous IPC lost (prevented by invariant chain). |
| U-M30 | IP-04 | IPC | Sender CSpace root slot hardcoded to `Slot.ofNat 0`. Model simplification — real seL4 uses actual slot address from message info. |
| U-M31 | IP-05 | IPC | `ipcInvariantFull` preservation for Send/Receive/Call/ReplyRecv requires caller-supplied `dualQueueSystemInvariant`. Composition not self-contained. |
| U-M32 | RS-02, M-01 | Rust | `MessageInfo` fields are `pub`. `encode()` silently truncates `length` and `extra_caps` via bitmask. Bypasses `new()` validation. |
| U-M33 | RS-03, R-02 | Rust | `From<u8> for AccessRights` accepts any `u8` (bits 5-7 can be set). No validation — invalid bitmasks silently created. |
| U-M34 | RS-04 | Rust | IPC buffer `#[repr(C)]` layout not verified against Lean-side memory layout spec. Forward-looking ABI drift concern. |
| U-M35 | D-05 | RobinHood | `get_after_insert`/`get_after_erase` proofs assume no hash collisions for distinct keys. Hash collision resistance not formally modeled. |
| U-M36 | DS-02 | RobinHood | `erase_preserves_probeChainDominant` requires `size < capacity`. Direct `insertNoResize` on full table loses invariant guarantee. |
| U-M37 | DS-03 | RobinHood | Very high `maxHeartbeats` (3.2M = 16× default) in lookup correctness proofs. Toolchain upgrade risk. |
| U-M38 | User | Capability | CDT acyclicity proof burden on callers. `processRevokeNode_lenient` is deprecated dead code. API should always dispatch to CDT-based revocation. |
| U-M39 | SC-01 | Scheduler | `switchDomain` does not call `saveOutgoingContext` before setting `current := none`. Context is saved by caller (`schedule`) but `switchDomain` itself is not self-contained. Defensive fix warranted. |

### 3.3 Selected LOW Findings (28)

| ID | Sources | Subsystem | Description | Inclusion Rationale |
|----|---------|-----------|-------------|---------------------|
| U-L01 | M-02 | RobinHood | `KMap.lean` is entirely dead code (219 lines, never imported) | Dead module removal |
| U-L02 | M-15-22 | Multiple | ~5,300 lines of dead/duplicated code across 25 files | Codebase hygiene |
| U-L03 | User | Capability | `AccessRightSet.mk` is public — no `isWord64` enforcement at hardware boundary | Security boundary |
| U-L04 | User | Capability | `processRevokeNode_lenient` deprecated but not removed | Dead code |
| U-L05 | User | IPC | `GrantReply` right defined (bit 3) but has no operational effect in IPC | Spec fidelity |
| U-L06 | User | IPC | Cap transfer uses fixed slot 0 for CDT tracking — imprecise but over-revokes | Documentation |
| U-L07 | User | Foundation | Missing formal commutativity proofs between builder and frozen operations | Proof completeness |
| U-L08 | R-07 | Rust | Error enum lacks `#[non_exhaustive]` — adding variants is breaking change | API stability |
| U-L09 | R-06 | Rust | `RegisterFile` index bounds use `debug_assert!` stripped in release | Defense-in-depth |
| U-L10 | R-05 | Rust | `MessageInfo` bit layout undocumented (no diagram) | Documentation |
| U-L11 | RS-05 | Rust | `SyscallResponse` missing `Copy` derive | Ergonomics |
| U-L12 | RS-06 | Rust | `MAX_MSG_REGS`/`MAX_EXTRA_CAPS` duplicated across crates | DRY violation |
| U-L13 | RS-07 | Rust | Conformance tests use hardcoded values, not Lean-generated vectors | Drift risk |
| U-L14 | A-06 | Architecture | `RegisterDecode` uses nested if-then-else. Match would give exhaustiveness checking | Readability |
| U-L15 | A-07 | Architecture | Argument decode returns `Option` for invalid inputs. No structured error type | Diagnostics |
| U-L16 | P-05, M-14 | Platform | `simSubstantiveMemoryMap` defined separately with "must be kept in sync" comment | Maintenance hazard |
| U-L17 | P-07 | Platform | `fromDtbWithRegions` hardcodes `physicalAddressWidth := 48` | Platform fidelity |
| U-L18 | P-10 | Platform | IRQ support range includes SGIs (INTID 0-15) for IPIs, not hardware interrupts | Spec precision |
| U-L19 | AR-10 | Platform | GIC INTID range capped at 223. BCM2712 may use higher INTIDs | Hardware coverage |
| U-L20 | AR-13 | API | `checkedDispatch_subsumes_unchecked_documentation` is `theorem ... : True := trivial` | Proof content |
| U-L21 | S-03 | Scheduler | Preservation proofs use fragile `simp [Function.update]` chains | Proof robustness |
| U-L22 | S-04 | Scheduler | RunQueue uses `List` (O(n) append). Acceptable for proof clarity | Performance note |
| U-L23 | C-04 | Capability | Some preservation proofs are 200+ lines with deep case splits | Maintainability |
| U-L24 | I-06 | IPC | Notification word merge uses unbounded Nat. No overflow check | Model fidelity |
| U-L25 | D-04 | RobinHood | `probeChainDominant` preservation through erase is ~400 lines | Proof factoring |
| U-L26 | User | Scheduler | Unproven `recomputeMaxPriority` size field and missing starvation doc | Documentation |
| U-L27 | User | API | Docstring mentions `notificationSignalChecked` but operation not wired into dispatch | Documentation |
| U-L28 | User | IPC | CSpace root fallback to `ObjId` in cap transfer should return error instead | Defense-in-depth |

---

## 4. Planning Principles

1. **Correctness-first ordering.** Phase U1 eliminates all confirmed correctness
   bugs: frozen queue pop/push mismatch (U-H01), watermark alignment gap (U-H02),
   and lifecycle dispatch bypass (U-H04). These affect functional correctness and
   must be resolved before any proof work builds on them.

2. **Safety boundary hardening before proof threading.** VAddr/ASID/PA bounds
   checks (U-H06/H07/H08), access restrictions on internal primitives (U-H05),
   and right mismatch fixes (U-H14) ship in U2 before proof-chain phases (U4, U5)
   that must thread through updated operation signatures.

3. **Rust ABI isolation.** All Rust changes (U-H11, U-M32/M33, U-L08-L13) are
   grouped in U3. Rust files are disjoint from Lean proof files, enabling full
   parallelism with Lean-focused phases.

4. **Proof chain closure.** Information flow (U-H09/H10), cross-subsystem
   invariant composition (U-M05/M14), and IPC preservation gaps (U-M31) are
   addressed in U4 after model stabilization. Each preservation theorem is a
   self-contained sub-task.

5. **API & dispatch integrity.** API dispatch refactoring (U-M01/M02), error
   code corrections (U-M07), and enforcement layer alignment (U-M04/M21) are
   grouped in U5 after proof infrastructure is stable.

6. **Architecture & platform as late phase.** Platform model fidelity changes
   (U-M08/M09/M10/M11) depend on bounds checks (U2) and proof infrastructure
   (U4). Grouping hardware preparation in U6 minimizes rework.

7. **Dead code and hygiene after functional changes.** U7 removes dead code
   (~5,300 lines) and addresses proof duplication. Running this phase late
   ensures no dead code is accidentally reintroduced by earlier phases.

8. **Zero sorry/axiom invariant.** No phase may introduce `sorry`, `axiom`,
   `admit`, or `partial` in production Lean code. Every phase gate includes a
   sorry/axiom scan.

9. **Atomic sub-task discipline.** Each sub-task is scoped to a single logical
   change that can be committed independently. Sub-tasks within a phase may
   depend on earlier sub-tasks but never on later phases.

10. **Design-intentional findings documented, not "fixed."** Findings that
    reflect deliberate seL4 design choices (U-M22, U-M28, U-L05, U-L06, U-L22)
    are addressed through documentation rationale, not code changes.

---

## 5. Phase Dependency Graph

```
U1 (Correctness Fixes)
 │
 ├──→ U2 (Safety Boundary Hardening)
 │     │
 │     ├──→ U4 (Proof Chain & Invariant Composition)
 │     │     │
 │     │     ├──→ U5 (API & Dispatch Integrity)
 │     │     │     │
 │     │     │     ├──→ U6 (Architecture & Platform Fidelity)
 │     │     │     │     │
 │     │     │     │     └──→ U8 (Documentation & Closure) ← waits for U6+U7
 │     │     │     │
 │     │     │     └──→ U7 (Dead Code & Proof Hygiene) ← parallel with U6
 │     │     │
 │     │     └──→ [proof-dependent phases]
 │     │
 │     └──→ U3 (Rust ABI Hardening) ← parallel with U4 (disjoint files)
 │
 └──→ [correctness-dependent phases]
```

**Critical path**: U1 → U2 → U4 → U5 → U6 → U8
**Rust track**: U1 → U3 (runs in parallel with U2/U4, disjoint file sets)
**Hygiene track**: U5 → U7 → U8 (runs in parallel with U6 after U5)

**Parallelism opportunities after U4:**
- **U5** owns: `Kernel/API.lean`, `InformationFlow/Enforcement/Wrappers.lean`,
  `Service/Invariant/`, `Architecture/SyscallArgDecode.lean`
- **U3** owns: `rust/` (all Rust crates, disjoint from Lean)
- **U6** owns: `Platform/RPi5/`, `Architecture/VSpace*.lean`, `Platform/Boot.lean`
- **U7** owns: dead code files, `RobinHood/KMap.lean`, test files, proof refactoring

---

## 6. Phase Specifications

### Phase U1 — Correctness Fixes (v0.21.0)

**Scope**: Eliminate all confirmed correctness bugs that affect functional behavior.
Fix frozen queue pop/push mismatch, lifecycle watermark alignment gap, lifecycle
dispatch bypass, and retype right mismatch.

**Rationale**: These are the only findings where the kernel produces incorrect
results under normal operation. The frozen queue bug (U-H01) blocks multi-round
IPC in the frozen phase. The watermark alignment gap (U-H02) can produce unaligned
allocations violating S5-G. The dispatch bypass (U-H04) skips memory scrubbing,
creating potential cross-domain information leakage. The right mismatch (U-H14)
means the API advertises `.retype` as the required right but the gate check demands
`.write` — callers with `.retype` but not `.write` are incorrectly rejected.

**Dependencies**: None (first phase).

**Gate**: `test_smoke.sh` passes. All modified `.lean` modules build individually
via `lake build <Module.Path>`. Zero `sorry`/`axiom`. Frozen IPC multi-round
sequence verified by trace harness.

**Sub-tasks (13):**

**Intra-phase ordering:**
- Frozen queue chain: U1-A → U1-B → U1-C
- Lifecycle chain: U1-D → U1-E → U1-F → U1-G
- Right mismatch: U1-H → U1-I
- IPC fallback: U1-J → U1-K
- Delete guard: U1-L (independent)
- Scheduler defense: U1-M (independent)

| ID | Finding | Description | Files | Est. |
|----|---------|-------------|-------|------|
| U1-A | U-H01 | Add `queuePPrev := none` to the record update in `frozenQueuePopHead`. The current code clears `queuePrev` and `queueNext` but not `queuePPrev`, preventing re-enqueue of popped threads. Read the pop function, locate the record update (`{ headTcb with queuePrev := none, queueNext := none }`), and add `queuePPrev := none`. | `SeLe4n/Kernel/FrozenOps/Operations.lean` | Small |
| U1-B | U-H01 | **(Requires U1-A)** Update `frozenQueuePopHead` preservation theorems to account for the additional field mutation. Any frame lemma asserting `queuePPrev` is unchanged must be updated. | `SeLe4n/Kernel/FrozenOps/Commutativity.lean` | Small |
| U1-C | U-H01 | **(Requires U1-B)** Add regression test: `frozenQueuePopHead` followed by `frozenQueuePushTail` on the same thread succeeds. Verify in trace harness that multi-round IPC (send → receive → send) works in frozen phase. | `SeLe4n/Testing/MainTraceHarness.lean` | Small |
| U1-D | U-H02 | Add page-alignment validation after watermark advance in `retypeFromUntyped`. After `ut.allocate childId allocSize` returns `ut'`, check `allocationBasePageAligned ut'`. Return `.allocationMisaligned` on failure. | `SeLe4n/Kernel/Lifecycle/Operations.lean` | Small |
| U1-E | U-H02 | **(Requires U1-D)** Update `retypeFromUntyped` preservation theorems to thread through the new post-allocation alignment check. **Sub-steps**: (1) Read the existing `retypeFromUntyped_preserves_*` theorem(s) to identify the proof structure. (2) Add a case split for the new `.allocationMisaligned` error branch — this branch preserves state trivially (no mutation, early return). (3) For the success branch, thread the alignment witness through the existing proof. (4) Verify the lifecycle invariant bundle still composes by building `SeLe4n.Kernel.Lifecycle.Invariant`. | `SeLe4n/Kernel/Lifecycle/Invariant.lean` | Medium |
| U1-F | U-H04 | Replace `lifecycleRetypeDirect` with `lifecycleRetypeWithCleanup` in both `dispatchWithCap` and `dispatchWithCapChecked` retype arms. This routes through the safe wrapper that performs cleanup and memory scrubbing. | `SeLe4n/Kernel/API.lean` | Small |
| U1-G | U-H04 | **(Requires U1-F)** Update the API dispatch documentation comment (lines 499-500) to reflect that the safe wrapper is now used. Remove the stale comment in `lifecycleRetypeDirect` claiming "cleanup is handled separately." | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/Lifecycle/Operations.lean` | Trivial |
| U1-H | U-H14 | Align retype authority check: change `lifecycleRetypeAuthority` from `Capability.hasRight cap .write` to `Capability.hasRight cap .retype`. This makes the gate check consistent with the API dispatch's required-right mapping. | `SeLe4n/Kernel/Lifecycle/Operations.lean` | Small |
| U1-I | U-H14 | **(Requires U1-H)** Update capability authority preservation theorems that reference `.write` for retype operations to use `.retype`. Verify cross-subsystem bridge still holds. | `SeLe4n/Kernel/Capability/Invariant/Authority.lean` | Small |
| U1-J | U-H13 | Change `endpointReceiveDual` CSpace root fallback from `senderId.toObjId` to return `.error .invalidCapability` when sender CSpace root is missing. This converts a silent fallback into an explicit error. | `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean` | Small |
| U1-K | U-H13 | **(Requires U1-J)** Update IPC preservation theorems to handle the new error path in `endpointReceiveDual`. The error branch preserves state trivially (no mutation). | `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` | Small |
| U1-L | U-H03 | Add runtime guard in `cspaceDeleteSlot` (lines 555-568 in `Capability/Operations.lean`): before deleting, check that no CDT children exist for the slot being deleted via `descendantsOf`. Return `.revocationRequired` if children found. This makes the `revokeBeforeDelete` proof obligation a runtime check. **Sub-steps**: (1) Add `hasCdtChildren` helper that queries `cdt.edges` for children of the given slot. (2) Insert the guard at the top of `cspaceDeleteSlot` before the existing capability lookup. (3) Update the `cspaceDeleteSlot` preservation theorem to handle the new early-exit error branch. | `SeLe4n/Kernel/Capability/Operations.lean` | Medium |
| U1-M | U-M39 | Add defensive `saveOutgoingContext` call inside `switchDomain` before setting `current := none`. Currently context is saved by the caller (`schedule`), but `switchDomain` should be self-contained. Add a precondition comment documenting the required invariant. | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | Small |

---

### Phase U2 — Safety Boundary Hardening (v0.21.1)

**Scope**: Add missing bounds checks at model-hardware boundaries. Restrict access
to unsafe internal primitives. Close the VAddr, ASID, and PA width validation gaps.

**Rationale**: These findings represent silent model-reality gaps where the Lean
model accepts values that ARM64 hardware would reject or mishandle. The VAddr
gap (U-H06) allows addresses beyond the 48-bit virtual address space. The PA width
mismatch (U-H07) means addresses in [2^44, 2^52) pass kernel validation but are
invalid on the RPi5's BCM2712. The public internal primitives (U-H05) expose
TLB-unsafe and scrub-free operations to any caller.

**Dependencies**: U1 (lifecycle operations modified in U1 must be stable).

**Gate**: `test_full.sh` passes. VSpace invariant proofs compile with new bounds.
Zero `sorry`/`axiom`. Specific module builds for all modified `.lean` files.

**Sub-tasks (14):**

**Intra-phase ordering:**
- VAddr chain: U2-A → U2-B → U2-C
- PA width chain: U2-D → U2-E → U2-F
- ASID chain: U2-G → U2-H
- Access restriction chain: U2-I → U2-J
- AccessRightSet: U2-K
- storeObject audit: U2-L
- allTablesInvExt: U2-M
- BEq negative instances: U2-N

| ID | Finding | Description | Files | Est. |
|----|---------|-------------|-------|------|
| U2-A | U-H06 | Add `VAddr.isValid` predicate: `vaddr.toNat < 2^48` (ARM64 canonical address range). Add validation in `vspaceMapPageChecked` and `vspaceMapPageCheckedWithFlush` that returns `.addressOutOfBounds` for invalid VAddr. | `SeLe4n/Kernel/Architecture/VSpace.lean` | Small |
| U2-B | U-H06 | **(Requires U2-A)** Add VAddr bounds check in `decodeVSpaceMapArgs`: validate decoded VAddr against `VAddr.isValid` before returning. Return `.invalidArgument` on failure. | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | Small |
| U2-C | U-H06 | **(Requires U2-B)** Update VSpace invariant proofs to thread through the new VAddr bounds. **Sub-steps**: (1) Add `vaddr_bounded : ∀ vaddr ∈ mappedAddresses, VAddr.isValid vaddr` conjunct to `vspaceInvariantBundle`. (2) Prove `vspaceMapPageChecked_preserves_vaddr_bounded` — the checked operation only inserts valid VAddrs (guard from U2-A). (3) Prove `vspaceUnmap_preserves_vaddr_bounded` — removal preserves the predicate trivially. (4) Update the composite `vspaceInvariant_preserved` theorem to include the new conjunct. | `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` | Medium |
| U2-D | U-H07 | Thread `MachineConfig.physicalAddressWidth` through VSpace bounds checking. **Sub-steps**: (1) Locate the global `physicalAddressBound` constant (currently `2^52` as a `def`, not a field). (2) Replace the constant with a function `physicalAddressBound (config : MachineConfig) := 2^config.physicalAddressWidth`. (3) Update `vspaceMapPageChecked` and `vspaceMapPageCheckedWithFlush` to accept or thread through the config parameter. (4) Update `paddr_valid` predicate to use the parameterized bound. (5) Verify RPi5 `rpi5MachineConfig` sets `physicalAddressWidth := 44`. | `SeLe4n/Kernel/Architecture/VSpace.lean` | Medium |
| U2-E | U-H07 | **(Requires U2-D)** Update `fromDtbWithRegions` to derive `physicalAddressWidth` from the DTB or accept it as a parameter instead of hardcoding 48. | `SeLe4n/Platform/DeviceTree.lean` | Small |
| U2-F | U-H07 | **(Requires U2-D)** Update VSpace invariant proofs to use parameterized PA bound. **Sub-steps**: (1) Update `paddr_inBounds` in `VSpaceInvariant.lean` to use `physicalAddressBound config` instead of the old constant. (2) Thread the `MachineConfig` parameter through all VSpace preservation theorems that reference PA bounds. (3) Add a well-formedness check `config.physicalAddressWidth ≤ 52` (ARM64 LPA maximum). (4) Add a `#eval` or `example` that verifies `rpi5MachineConfig.physicalAddressWidth = 44` passes all VSpace well-formedness predicates. | `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`, `SeLe4n/Platform/RPi5/Board.lean` | Medium |
| U2-G | U-H08 | Add `ASID.isValid` predicate: `asid.toNat < maxASID` (where `maxASID = 65536` from `MachineConfig`). Add validation in `decodeVSpaceMapArgs` and `decodeVSpaceUnmapArgs`. | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | Small |
| U2-H | U-H08 | **(Requires U2-G)** Add ASID bounds validation in `resolveAsidRoot` — return `.invalidASID` if ASID exceeds config bound. Update VSpace operations that call `resolveAsidRoot`. | `SeLe4n/Kernel/Architecture/VSpace.lean` | Small |
| U2-I | U-H05 | Mark `vspaceMapPage` as `private`. All external callers must use `vspaceMapPageWithFlush` or `vspaceMapPageCheckedWithFlush`. Update test harness to use the public API. | `SeLe4n/Kernel/Architecture/VSpace.lean`, `SeLe4n/Testing/MainTraceHarness.lean` | Small |
| U2-J | U-H05 | **(Requires U2-I)** Mark `lifecycleRetypeObject` as `private`. All external callers must use `lifecycleRetypeWithCleanup` or `retypeFromUntyped`. Verify no external imports reference the private function. | `SeLe4n/Kernel/Lifecycle/Operations.lean` | Small |
| U2-K | U-L03 | Make `AccessRightSet` constructor enforce `isWord64` at creation. **Sub-steps**: (1) Add `AccessRightSet.mk_checked (bits : Nat) (h : bits < 2^5) : AccessRightSet` as the public constructor with a proof obligation. (2) Make the raw `AccessRightSet.mk` private (or add `private` to the structure definition). (3) Update all construction sites to use `mk_checked` — most are constant expressions where `decide` discharges the proof. (4) Add `isWord64` lemma: `∀ (ars : AccessRightSet), ars.bits < 2^5` derived from the constructor invariant. (5) Separately: in CDT security checks, prefer `edgeWellFounded` (structural induction) over BFS-based `acyclic` where applicable, to avoid fuel-dependent reasoning. | `SeLe4n/Model/Object/Types.lean` | Medium |
| U2-L | U-M18 | Audit all `storeObject` call sites for capacity pre-check. Document which callers rely on `retypeFromUntyped` capacity enforcement vs. which need their own check. Add `assert` or comment at each call site. | `SeLe4n/Model/State.lean`, multiple consumers | Small |
| U2-M | U-M20 | Add compile-time completeness check for `allTablesInvExt`. `allTablesInvExt` currently manually enumerates 16 RHTable fields across 5 categories (threads, objects, capabilities, IPC, scheduling). **Sub-steps**: (1) Define `AllTablesInvExtWitness` structure with one `invExt` field per RHTable in `SystemState` (16 fields). (2) Add `allTablesInvExt_witness (st : SystemState) : AllTablesInvExtWitness` that constructs the witness from `allTablesInvExt st`. (3) Any new RHTable field added to `SystemState` without updating the witness structure produces a type error, enforcing completeness. (4) Verify the witness compiles with `lake build SeLe4n.Model.State`. | `SeLe4n/Model/State.lean` | Medium |
| U2-N | U-M17 | Add negative `LawfulBEq` instances for `RegisterFile` and `TCB` to prevent accidental use in proofs expecting lawful behavior. Use `instance : ¬ LawfulBEq RegisterFile := ...` pattern. | `SeLe4n/Machine.lean`, `SeLe4n/Model/Object/Types.lean` | Small |

---

### Phase U3 — Rust ABI Hardening (v0.21.2)

**Scope**: Harden Rust userspace ABI layer. Fix inline assembly clobbers, enforce
field privacy for validated types, add missing validation at decode boundaries,
and improve API stability annotations.

**Rationale**: The Rust ABI layer is the first code that touches raw register values
from userspace. The missing register clobbers (U-H11) risk silent corruption. Public
`MessageInfo` fields (U-M32) allow construction that bypasses validation, producing
silently truncated values. `AccessRights` accepts any byte (U-M33), creating invalid
bitmasks. These are defense-in-depth issues — the Lean kernel validates at the
boundary — but should be rejected at the earliest possible point.

**Dependencies**: U1 (Lean error variants must be stable for Rust encode/decode).

**Gate**: All Rust tests pass (`cargo test --workspace`). Zero `unsafe` outside
`svc #0`. Encode/decode roundtrip tests cover all new validation.

**Sub-tasks (10):**

**Intra-phase ordering:**
- Clobber fix: U3-A (independent)
- MessageInfo chain: U3-B → U3-C
- AccessRights chain: U3-D → U3-E
- Error enum: U3-F (independent)
- RegisterFile: U3-G (independent)
- Documentation: U3-H (independent)
- IPC buffer: U3-I (independent)
- Conformance: U3-J (requires all above)

| ID | Finding | Description | Files | Est. |
|----|---------|-------------|-------|------|
| U3-A | U-H11 | Add `clobber_abi("C")` to the `svc #0` inline asm in `trap.rs`, or add explicit `lateout` declarations for x8-x18. This ensures the compiler knows the kernel may modify these registers during the exception. | `rust/sele4n-abi/src/trap.rs` | Small |
| U3-B | U-M32 | Make `MessageInfo` fields private. Remove `pub` from `length`, `extra_caps`, and `label`. Add accessor methods (`fn length(&self) -> u8`, etc.). All construction must go through `new()` or `decode()`. | `rust/sele4n-abi/src/message_info.rs` | Medium |
| U3-C | U-M32 | **(Requires U3-B)** Update all call sites that directly access `MessageInfo` fields to use the new accessor methods. Update tests. | `rust/sele4n-abi/`, `rust/sele4n-sys/` | Small |
| U3-D | U-M33 | Replace `From<u8> for AccessRights` with `TryFrom<u8>`. Reject values with bits 5-7 set (mask with `& 0x1F` or return error). Update all construction sites. | `rust/sele4n-types/src/rights.rs` | Small |
| U3-E | U-M33 | **(Requires U3-D)** Add roundtrip conformance tests for `AccessRights`: valid values (0-31) succeed, invalid values (32-255) are rejected. | `rust/sele4n-types/tests/` | Small |
| U3-F | U-L08 | Add `#[non_exhaustive]` attribute to `KernelError` enum. This makes adding new error variants a non-breaking change for downstream crates. | `rust/sele4n-types/src/error.rs` | Trivial |
| U3-G | U-L09 | Replace `debug_assert!` bounds checks in `RegisterFile` index operations with `get()` returning `Option`, or use `.get(idx).copied()` pattern that returns `None` for out-of-bounds. | `rust/sele4n-abi/src/registers.rs` | Small |
| U3-H | U-L10 | Add bit-layout diagram as doc-comment for `MessageInfo::encode`/`decode`. Show the 64-bit packing: bits 0-6 = length, bits 7-8 = extra_caps, bits 9-63 = label. | `rust/sele4n-abi/src/message_info.rs` | Trivial |
| U3-I | U-M34 | Add `static_assert!` or `const` assertion that `IpcBuffer` `#[repr(C)]` layout matches expected size and field offsets. Document Lean-side correspondence. | `rust/sele4n-sys/src/ipc_buffer.rs` | Small |
| U3-J | U-L13 | **(Requires all above)** Add script or CI step to auto-generate conformance test vectors from Lean model output. Replace hardcoded test values with generated fixtures where feasible. Run full `cargo test --workspace`. | `rust/`, `scripts/` | Medium |

---

### Phase U4 — Proof Chain & Invariant Composition (v0.21.3)

**Scope**: Close proof chain gaps in information flow NI, cross-subsystem invariant
composition, capability CDT proof obligations, and IPC preservation.

**Rationale**: These findings represent the most security-critical open proof
obligations. The externalized IPC `hProjection` hypotheses (U-H09) mean NI for
IPC is vacuously true if no caller discharges them — the most critical assurance
gap in the codebase. The `NonInterferenceStep` manual completeness (U-H10) means
adding a new operation could silently weaken NI without detection. Cross-subsystem
invariant composition (U-M05/M14) leaves the service acyclicity guarantee isolated
from the global invariant.

**Dependencies**: U2 (model types and bounds must be stable before proof threading).

**Gate**: `test_full.sh` passes. All modified theorems compile individually.
Zero `sorry`/`axiom`. NI projection hypotheses discharged for at least 2 of 4
IPC operations.

**Sub-tasks (14):**

**Intra-phase ordering:**
- NI chain: U4-A → U4-B → U4-C → U4-D
- Cross-subsystem: U4-E → U4-F
- Service: U4-G → U4-H
- CDT: U4-I → U4-J
- IPC preservation: U4-K → U4-L
- Capability walk: U4-M
- descendantsOf: U4-N

| ID | Finding | Description | Files | Est. |
|----|---------|-------------|-------|------|
| U4-A | U-H09 | Discharge `hProjection` for `endpointSendDual` NI proof. The current proof (`endpointSendDualChecked_NI`, 21 lines, lines 72-92) carries an externalized `hProjection : ∀ t t', endpointSendDual endpointId sender msg t = .ok ((), t') → projectState ctx observer t' = projectState ctx observer t` hypothesis that is declared but never invoked. `projectState` has **12 fields** (threads, objects, cdt, endpoints, notifications, vspaces, scheduler, services, irqState, platform, counters, ipcBuffers); `objectObservable` (lines 87-88) gates visibility per-field. **Sub-steps**: (1) **Per-field frame lemmas** — For each of the 12 `projectState` fields, prove that `endpointSendDual` either (a) does not modify the field, or (b) modifies only objects in the sender's or endpoint's security domain (invisible to an unrelated observer). Start with the 8 fields that `endpointSendDual` does NOT touch (vspaces, scheduler, services, irqState, platform, counters, cdt, ipcBuffers) — these are `rfl` proofs. (2) **Endpoint field projection** — Prove the endpoint state change (queue manipulation) is invisible to observers not in the endpoint's domain. Requires showing `objectObservable ctx observer endpointId = false → projectEndpoints ctx observer st' = projectEndpoints ctx observer st`. (3) **Thread field projection** — Prove the sender TCB mutation (ipcState, pendingMessage) is invisible to observers outside sender's domain. Same `objectObservable` gate pattern. (4) **Notification field projection** — Prove notification state is unchanged or invisible (send path does not touch notifications). (5) **Compose** all 12 per-field preservation lemmas into the full `projectState` equality using `ProjectState.ext` (or manual field-by-field rewrite). (6) **Replace** the `hProjection` hypothesis in `endpointSendDualChecked_NI` with a direct call to the composed proof. | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`, `SeLe4n/Kernel/InformationFlow/Projection.lean` | Large (6 sub-steps) |
| U4-B | U-H09 | **(Requires U4-A)** Discharge `hProjection` for `endpointReceiveDual`. Same 12-field decomposition as U4-A but for the receive path. **Sub-steps**: (1) **Reuse 8 untouched-field lemmas** from U4-A (vspaces, scheduler, services, irqState, platform, counters, cdt, ipcBuffers are still `rfl`). (2) **Endpoint field projection** — Prove queue pop (receiver removal) is invisible to unrelated observers. The endpoint's domain gate covers this. (3) **Thread field projection** — Prove receiver TCB mutation (ipcState change from Blocked to Running, pendingMessage populated) is invisible outside receiver's domain. (4) **Object field projection** — If cap transfer occurs (grant right), prove the new capability in receiver's CSpace is invisible outside receiver's domain. (5) **Compose** into full `projectState` equality. (6) **Replace** the `hProjection` hypothesis in `endpointReceiveDualChecked_NI`. | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` | Large (6 sub-steps) |
| U4-C | U-H09 | **(Requires U4-B)** Discharge `hProjection` for `endpointCall` and `endpointReplyRecv`. These are sequential compositions: `endpointCall` = send + block-self, `endpointReplyRecv` = reply + receive. **Sub-steps**: (1) **`endpointCall` projection** — Factor into `endpointSendDual` projection (from U4-A) followed by a self-block projection (sender blocks itself — TCB change invisible outside sender's domain). Prove composition: if both steps preserve `projectState`, the sequential composition does too. (2) **`endpointReplyRecv` projection** — Factor into reply projection (unblock replier's caller — TCB change invisible outside replier's domain) followed by `endpointReceiveDual` projection (from U4-B). (3) **Sequential composition lemma** — Prove `projectState_preserved_trans`: if `f` preserves projection and `g` preserves projection, then `f >>= g` preserves projection. This is reusable for any multi-step kernel operation. (4) **Replace** `hProjection` in both `endpointCallChecked_NI` and `endpointReplyRecvChecked_NI`. | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` | Large (4 sub-steps) |
| U4-D | U-H09 | **(Requires U4-C)** Update `NonInterferenceStep` constructors for the 4 IPC operations to use the internal projection proofs instead of externalized hypotheses. Remove `hProjection` parameter from the constructor signatures. Update trace composition in `Composition.lean`. | `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` | Medium |
| U4-E | U-H10 | Add compile-time completeness check for `NonInterferenceStep`. The inductive currently has **33 constructors** (verified count — not 34 as originally reported). Create a `KernelOperation` enumeration listing all 33 API entry points. Add a theorem `niStepComplete` proving every `KernelOperation` variant has a corresponding `NonInterferenceStep` constructor. If a new operation is added without a constructor, the theorem fails to compile. | `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` | Medium |
| U4-F | U-H10 | **(Requires U4-E)** Add a `niStepCoverage` theorem that proves `∀ (op : KernelOperation), ∃ (step : NonInterferenceStep), step.operation = op`. This structurally enforces completeness. | `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` | Medium |
| U4-G | U-M05 | Wire `serviceGraphInvariant` into `crossSubsystemInvariant` in `CrossSubsystem.lean`. Add `serviceDependencyAcyclic st ∧ serviceCountBounded st` as conjunct to the composite invariant. | `SeLe4n/Kernel/CrossSubsystem.lean` | Small |
| U4-H | U-M05 | **(Requires U4-G)** Update `crossSubsystemInvariant` preservation. `crossSubsystemInvariant` currently has **4 conjuncts** (lines 94-98). Adding `serviceGraphInvariant` makes it 5. This **cascades to ~6 preservation theorem updates** — one per kernel operation that modifies service state. **Sub-steps**: (1) Identify all `crossSubsystemInvariant_preserved_*` theorems. (2) For operations that don't modify service state (scheduler ops, IPC ops, VSpace ops), the new conjunct is preserved trivially (`serviceGraphInvariant` unchanged). Add `And.intro` with `h.5` (the new conjunct from the hypothesis). (3) For operations that DO modify service state (`serviceRegister`, `serviceRevoke`, `serviceQuery`), thread through existing `serviceGraphInvariant` preservation proofs from `Acyclicity.lean` (`serviceRegister_preserves_acyclicity`, etc.). (4) Verify: `lake build SeLe4n.Kernel.CrossSubsystem`. | `SeLe4n/Kernel/CrossSubsystem.lean` | Medium (4 sub-steps) |
| U4-I | U-M06 | Prove `cleanupEndpointServiceRegistrations_preserves_registryInterfaceValid`. This is the missing half of the cleanup path's invariant coverage. Follow the pattern of the existing `_preserves_registryEndpointValid` theorem. | `SeLe4n/Kernel/Service/Registry/Invariant.lean` | Medium |
| U4-J | U-M38 | Remove deprecated `processRevokeNode_lenient`. Verify API always dispatches to CDT-based revocation (`cspaceRevokeCdt`). Add documentation that CDT-based revocation is canonical. | `SeLe4n/Kernel/Capability/Operations.lean` | Small |
| U4-K | U-M31 | Prove self-contained `ipcInvariantFull` preservation for Send, Receive, Call, and ReplyRecv. `ipcInvariantFull` is the conjunction of **4 conjuncts**: `ipcInvariant ∧ dualQueueSystemInvariant ∧ allPendingMessagesBounded ∧ badgeWellFormed`. The `dualQueueSystemInvariant` itself has **3 sub-conjuncts** (queue consistency, prev/next symmetry, PPrev well-formedness). Currently, preservation proofs for each IPC operation require the caller to supply `dualQueueSystemInvariant` as a hypothesis rather than proving it internally. **Sub-steps**: (1) **Send preservation** — Compose `endpointSendDual_preserves_ipcInvariant`, `endpointSendDual_preserves_dualQueueSystemInvariant` (the 3 sub-conjuncts individually), `endpointSendDual_preserves_allPendingMessagesBounded`, and `endpointSendDual_preserves_badgeWellFormed` into a single `endpointSendDual_preserves_ipcInvariantFull` that takes only `ipcInvariantFull pre` as hypothesis. (2) **Receive preservation** — Same pattern for `endpointReceiveDual`. The queue pop operation modifies `queuePrev`/`queueNext`/`queuePPrev` — the 3 `dualQueueSystemInvariant` sub-conjuncts must each be shown preserved. (3) **Call preservation** — Compose from Send preservation + self-block preservation. The self-block only changes `ipcState` (no queue mutation), so `dualQueueSystemInvariant` is preserved trivially. (4) **ReplyRecv preservation** — Compose from Reply preservation + Receive preservation. Reply unblocks a thread (queue mutation) — requires the 3-sub-conjunct decomposition. (5) **Integration** — Add a master theorem `ipcOperations_preserve_ipcInvariantFull` covering all 4 operations with a single match statement. Remove the external `dualQueueSystemInvariant` hypothesis from all callers in `Structural.lean`. | `SeLe4n/Kernel/IPC/Invariant/Structural.lean` | Large (5 sub-steps) |
| U4-L | U-M26 | Document the CDT hypothesis pattern: explain why CDT-modifying operations take `cdtCompleteness ∧ cdtAcyclicity` as hypothesis rather than proving from pre-state. Add rationale comments at each operation site. | `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` | Small |
| U4-M | U-M25 | Document the CSpace walk rights gap: explain that seLe4n enforces rights at the operation layer rather than during traversal. Add a comment in `resolveCapAddress` noting the seL4 divergence and referencing the operation-level check. | `SeLe4n/Kernel/Capability/Operations.lean` | Trivial |
| U4-N | U-M19 | Prove `descendantsOf` transitive closure fuel sufficiency. `descendantsOf` (lines 989-999) uses BFS with `fuel = cdt.edges.length`. There are **8 existing lemmas** on fuel/accumulator monotonicity (e.g., `descendantsOfBounded_acc_mono`, `descendantsOfBounded_fuel_mono`). The gap: depth-1 children are guaranteed, but multi-level reachability (grandchildren+) depends on fuel sufficiency that is not formally proven. **Sub-steps**: (1) **BFS unfolding lemma** — Prove `descendantsOfBounded (fuel+1) root cdt acc = descendantsOfBounded fuel root cdt (acc ∪ directChildren root cdt)`. This shows each fuel unit processes one BFS level. (2) **Accumulator monotonicity strengthening** — Strengthen existing `descendantsOfBounded_acc_mono` to show `acc ⊆ acc' → descendantsOfBounded fuel root cdt acc ⊆ descendantsOfBounded fuel root cdt acc'`. (3) **Depth bound lemma** — Prove that the maximum depth of the CDT is bounded by `cdt.edges.length` (since the CDT is acyclic by `cdtAcyclicity`, the longest path visits each edge at most once). (4) **Fuel sufficiency theorem** — Compose steps 1-3: `descendantsOfBounded cdt.edges.length root cdt ∅ = transitiveDescendants root cdt` where `transitiveDescendants` is defined as the reflexive-transitive closure of `directChildren`. This is the core deliverable. (5) **Revocation completeness corollary** — Derive `cspaceRevokeCdt` completeness: all transitive descendants are revoked when fuel = `cdt.edges.length`. | `SeLe4n/Model/Object/Structures.lean` | Large (5 sub-steps) |

---

### Phase U5 — API & Dispatch Integrity (v0.21.4)

**Scope**: Refactor API dispatch to eliminate duplication, fix error codes, align
enforcement layers, and add missing documentation for design-intentional behaviors.

**Rationale**: The API dispatch layer is the kernel's external interface. The
checked/unchecked dispatch divergence (U-M01) creates maintenance risk. The wrong
error code (U-M07) confuses callers. The inline flow check for `.call` (U-M01)
bypasses the enforcement wrapper, creating a fragile coupling between dispatch and
policy. Documenting design-intentional IPC behaviors (U-M28, U-M29, U-M30) provides
explicit rationale for auditors.

**Dependencies**: U4 (proof chain changes may affect dispatch-level theorems).

**Gate**: `test_smoke.sh` passes. API dispatch verified via trace harness.
All modified `.lean` modules build individually. Zero `sorry`/`axiom`.

**Sub-tasks (14):**

**Intra-phase ordering:**
- Dispatch refactor: U5-A → U5-B → U5-C → U5-D
- Error code: U5-E (independent)
- Enforcement: U5-F → U5-G
- Documentation: U5-H through U5-N (all independent)

| ID | Finding | Description | Files | Est. |
|----|---------|-------------|-------|------|
| U5-A | U-M02 | Extract shared dispatch logic. Investigation confirmed **7 identical arms** (`.reply`, `.cspaceDelete`, `.lifecycleRetype`, `.vspaceMap`, `.vspaceUnmap`, `.serviceQuery`, `.serviceRevoke`) and **6 differing arms** (`.send`, `.receive`, `.call`, `.replyRecv`, `.cspaceMint`, `.cspaceCopy`/`.cspaceMove`) plus a `.notificationSignal` stub. **Sub-steps**: (1) Define `dispatchCommon (syscall : SyscallId) (cap : Capability) (args : SyscallArgs) (st : SystemState) : KernelResult Unit SystemState` containing the 7 shared arms. (2) Define `dispatchCheckedOverrides` for the 6 differing arms that adds policy gates (`securityFlowsTo` checks via enforcement wrappers). (3) Define `dispatchUncheckedOverrides` for the 6 differing arms without policy gates. (4) Rewrite `dispatchWithCap` as `dispatchCommon` falling through to `dispatchUncheckedOverrides`. (5) Rewrite `dispatchWithCapChecked` as `dispatchCommon` falling through to `dispatchCheckedOverrides`. (6) Verify identical behavior via `lake build SeLe4n.Kernel.API` and trace harness. | `SeLe4n/Kernel/API.lean` | Medium (6 sub-steps) |
| U5-B | U-M01 | **(Requires U5-A)** Route `.call` in `dispatchWithCapChecked` through the enforcement wrapper (`endpointCallChecked`) instead of inline `securityFlowsTo` check. This ensures the checked path uses the same enforcement layer as all other gated operations. | `SeLe4n/Kernel/API.lean` | Small |
| U5-C | U-M04 | **(Requires U5-A)** Route `.reply` in `dispatchWithCapChecked` through an enforcement wrapper instead of the inline "single-use authority" bypass. Add `replyChecked` wrapper in `Enforcement/Wrappers.lean` if not already present. | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | Small |
| U5-D | U-M02 | **(Requires U5-A)** Replace the trivial `checkedDispatch_subsumes_unchecked_documentation : True := trivial` (U-L20) with a real semantic equivalence theorem. **Sub-steps**: (1) Define `permissivePolicy` as a `SecurityContext` where all `securityFlowsTo` checks return `true`. (2) Prove `dispatchCheckedOverrides permissivePolicy = dispatchUncheckedOverrides` — under permissive policy, the checked path reduces to the unchecked path for all 6 differing arms. (3) Prove `checkedDispatch_subsumes_unchecked : ∀ policy syscall cap args st, dispatchWithCapChecked policy syscall cap args st = .ok r → ∃ r', dispatchWithCap syscall cap args st = .ok r'` — checked success implies unchecked success. (4) Delete the trivial `True` placeholder theorem. | `SeLe4n/Kernel/API.lean` | Medium (4 sub-steps) |
| U5-E | U-M07 | Change `decodeVSpaceMapArgs` error from `.policyDenied` to `.invalidArgument` for invalid permissions. This is a one-line fix: replace `.error .policyDenied` with `.error .invalidArgument` at line 215. Update any tests checking for `.policyDenied` in this context. | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | Trivial |
| U5-F | U-M21 | Document the 7 "capability-only" operations that have no runtime flow check: explain that NI for these operations relies on proof soundness. Add explicit comments at each operation in `Wrappers.lean` listing which operations are policy-gated vs capability-gated. | `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | Small |
| U5-G | U-M21 | **(Requires U5-F)** Add a `capabilityOnlyOperations` definition listing all 7 capability-gated operations. Add a documentation comment explaining the security rationale: these operations are bounded by capability authority which is already covered by the NI proof. | `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | Small |
| U5-H | U-M03 | Document badge-0 semantics: add comment in API dispatch explaining that badge value 0 is treated as "no badge" by design. If this is intentional (matching seL4), add explicit rationale. If not, change to `some args.badge` unconditionally and document the change. | `SeLe4n/Kernel/API.lean` | Trivial |
| U5-I | U-M28 | Document IPC message truncation behavior in API specification. Add comment in `sendIPC` explaining that messages exceeding receiver buffer are silently truncated to buffer size, matching seL4 semantics. | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | Trivial |
| U5-J | U-M29 | Document `notificationSignal` wake-path overwrite: add comment explaining that waiter's `pendingMessage` overwrite is prevented by the `ipcStateQueueConsistent` invariant (waiters have no pending message). | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | Trivial |
| U5-K | U-M30 | Document the CSpace root slot 0 simplification. Add comment explaining that this is a model simplification and that real seL4 uses the actual slot address from message info. Reference the seL4 spec section. | `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean` | Trivial |
| U5-L | U-L05 | Document `GrantReply` right: add comment explaining that `AccessRight.grantReply` (bit 3) is defined for spec fidelity but has no operational effect in the current IPC model. The `.grant` right (bit 2) governs all grant operations. | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean` | Trivial |
| U5-M | U-L06 | Document cap transfer CDT tracking: add comment explaining that fixed slot 0 for CDT tracking is imprecise but safe — over-revokes rather than under-revokes. | `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean` | Trivial |
| U5-N | U-L27 | Fix docstring that mentions `notificationSignalChecked` in API dispatch. Either remove the reference (if the operation is deferred) or add a TODO marking it for WS-V (hardware binding). | `SeLe4n/Kernel/API.lean` | Trivial |

---

### Phase U6 — Architecture & Platform Fidelity (v0.21.5)

**Scope**: Improve model-hardware fidelity for the RPi5 platform. Address MMIO
abstraction, runtime contract permissiveness, boot sequence validation gaps, and
platform-specific configuration.

**Rationale**: These findings represent the gap between the abstract Lean model
and ARM64 hardware reality. The MMIO model (U-M08) treats device registers as RAM,
making proofs about device interaction unsound. The runtime contract (U-M09) is
trivially satisfied for all register writes. Boot sequence validation (U-M12/M13)
silently accepts duplicates. These must be addressed before the WS-V hardware
binding milestone.

**Dependencies**: U5 (API dispatch must be stable), U2 (VSpace bounds must be
finalized).

**Gate**: `test_full.sh` passes. RPi5 platform bindings compile and pass
well-formedness checks. Zero `sorry`/`axiom`.

**Sub-tasks (12):**

**Intra-phase ordering:**
- MMIO chain: U6-A → U6-B
- Contract chain: U6-C → U6-D
- Boot chain: U6-E → U6-F → U6-G
- MMIO writes: U6-H (independent)
- NI channels: U6-I → U6-J
- Covert channels: U6-K → U6-L

| ID | Finding | Description | Files | Est. |
|----|---------|-------------|-------|------|
| U6-A | U-M08 | Add formal MMIO abstraction boundary. **Sub-steps**: (1) Define `MmioRegion` structure: `{ base : PAddr, size : Nat, readSemantics : MmioReadKind }` where `MmioReadKind` is `| ram | volatile | writeOneClear | fifo`. (2) Define `mmioRead (region : MmioRegion) (offset : Nat) : MachineMonad Word` as `opaque` for non-RAM regions — this prevents proofs from unfolding device register reads as memory lookups. (3) Define `MmioWrite` with `MmioWriteKind` (`.normal`, `.writeOneClear`, `.setOnly`). (4) Update `readBE32`/`readBE64` to dispatch through `mmioRead` when the address falls in a declared `MmioRegion`. (5) Add `MmioSafe` hypothesis type for proofs that need to reason about MMIO outcomes (caller must supply platform-specific justification). | `SeLe4n/Platform/RPi5/MmioAdapter.lean` | Medium (5 sub-steps) |
| U6-B | U-M08 | **(Requires U6-A)** Update proofs depending on memory-read semantics for MMIO addresses. **Sub-steps**: (1) Grep for proofs that unfold memory reads at MMIO addresses (search for `st.machine.memory` patterns in VSpace and platform files). (2) For each such proof, determine if the memory address could be in an `MmioRegion`. (3) If yes, add an `MmioSafe` hypothesis or restrict the proof to non-MMIO addresses via `¬ inMmioRegion addr`. (4) Update VSpace page-table walk proofs to explicitly exclude MMIO-mapped pages from idempotency assumptions. | `SeLe4n/Kernel/Architecture/VSpace.lean` | Medium (4 sub-steps) |
| U6-C | U-M09 | Strengthen `registerContextStable` in RPi5 runtime contract. **Sub-steps**: (1) Read the current `registerContextStable` predicate to identify the permissive disjunct (`∨ st'.scheduler.current ≠ st.scheduler.current`). (2) Replace the disjunct with: `st'.scheduler.current = some tid → st'.machine.registers = (st'.objects.get? tid).map TCB.savedContext`. This requires the new register state to match the scheduled thread's saved context. (3) Verify the simulation platform (`Sim/RuntimeContract.lean`) still uses permissive `True` (unchanged — sim is intentionally vacuous). (4) Check that RPi5 proof hooks still discharge the strengthened contract. | `SeLe4n/Platform/RPi5/RuntimeContract.lean` | Medium (4 sub-steps) |
| U6-D | U-M09 | **(Requires U6-C)** Update RPi5 proof hooks. **Sub-steps**: (1) Update `AdapterProofHooks` in `RPi5/ProofHooks.lean` to prove the strengthened `registerContextStable`. (2) The proof strategy: on context switch, `saveOutgoingContext` stores registers into the TCB, then `restoreIncomingContext` loads the new thread's saved registers — so the strengthened predicate holds by construction. (3) Verify all RPi5 platform proofs still compile: `lake build SeLe4n.Platform.RPi5.ProofHooks`. (4) Verify boot contract is unaffected (boot does not use `registerContextStable`). | `SeLe4n/Platform/RPi5/ProofHooks.lean` | Medium (4 sub-steps) |
| U6-E | U-M12 | Add duplicate IRQ registration detection in `foldIrqs`. Return error or log warning when the same INTID is registered twice. Document the last-wins semantics if intentional. | `SeLe4n/Platform/Boot.lean` | Small |
| U6-F | U-M13 | **(Requires U6-E)** Add object ID uniqueness validation in `foldObjects`. Return error when a duplicate object ID is encountered. This prevents silent overwrites that could lose kernel objects. | `SeLe4n/Platform/Boot.lean` | Small |
| U6-G | U-M15 | **(Requires U6-F)** Prove boot-to-runtime invariant bridge. The gap is between `bootFromPlatform_valid` (proves 4 invariant bundles for builder-phase state, lines 108-117 in `Boot.lean`) and `apiInvariantBundle_frozenDirect` (proves runtime invariant for frozen state, lines 1089-1092 in `FreezeProofs.lean`). There are **3 missing intermediate composition lemmas**. **Sub-steps**: (1) **Boot→Intermediate lemma** — Prove `bootFromPlatform config = .ok ist → intermediateStateInvariant ist`. This extracts the 4 invariant bundles from `bootFromPlatform_valid` into the intermediate state's invariant witnesses. The builder phase (`IntermediateState`) already carries invariant witnesses as fields — the proof shows these witnesses are valid. (2) **Intermediate→Frozen lemma** — Prove `intermediateStateInvariant ist → frozenStateInvariant (freezeState ist)`. This is the core freeze correctness transfer. Existing `freezeLookupEquiv` and `freezeRadixEquiv` lemmas in `FreezeProofs.lean` provide the per-table equivalence. The gap is composing these into the full `frozenStateInvariant`. Compose: for each of the 4 invariant bundles, show the frozen equivalent holds by rewriting through the freeze equivalences. (3) **Frozen→Runtime lemma** — Prove `frozenStateInvariant fst → proofLayerInvariantBundle (toRuntimeState fst)`. `apiInvariantBundle_frozenDirect` partially covers this but lacks the composition step from frozen to runtime. The proof must show that `FrozenKernel` monad operations preserve the invariant bundle from the frozen initial state. (4) **End-to-end bridge theorem** — Compose steps 1-3: `bootToRuntime_invariantBridge : bootFromPlatform config = .ok ist → proofLayerInvariantBundle (toRuntimeState (freezeState ist))`. This is the single theorem that closes the boot-to-runtime gap. (5) **Integration** — Wire `bootToRuntime_invariantBridge` into the kernel initialization path so that the runtime proof layer can cite it as the invariant establishment proof. | `SeLe4n/Platform/Boot.lean`, `SeLe4n/Model/FreezeProofs.lean` | Large (5 sub-steps) |
| U6-H | U-M10 | Add `mmioWrite32` and `mmioWrite64` operations for ARM64 GIC register access. These must perform 32-bit aligned writes (GIC registers require 32-bit access width). | `SeLe4n/Platform/RPi5/MmioAdapter.lean` | Small |
| U6-I | U-M22 | Document non-standard BIBA integrity direction as deliberate design choice. Add rationale comment in `Policy.lean` explaining why write-up is allowed and how this differs from standard BIBA. Reference the seL4 information flow model. | `SeLe4n/Kernel/InformationFlow/Policy.lean` | Trivial |
| U6-J | U-M24 | Document that service registry is invisible to the NI projection model. Add comment explaining that service-layer flows are not captured by non-interference and must be analyzed separately. | `SeLe4n/Kernel/InformationFlow/Projection.lean` | Trivial |
| U6-K | U-M23 | Document accepted covert channels: scheduling state (domain schedule visible to all observers) and TCB metadata (priority/IPC state visible cross-domain). Add a "Covert Channel Analysis" section comment in `Projection.lean`. | `SeLe4n/Kernel/InformationFlow/Projection.lean` | Small |
| U6-L | U-M14 | Document the cross-subsystem invariant composition gap: explain that the conjunction of subsystem invariants may not be the strongest composite. Add a TODO for future work on cross-subsystem interference properties. | `SeLe4n/Kernel/CrossSubsystem.lean` | Trivial |

---

### Phase U7 — Dead Code & Proof Hygiene (v0.21.6)

**Scope**: Remove confirmed dead code (~5,300 lines across 25 files), eliminate
trivial tautology theorems, clean up deprecated functions, and address proof
engineering concerns (fragile simp chains, high heartbeats, duplication).

**Rationale**: The kernel implementation audit identified approximately 8-9% of
the Lean codebase as removable or refactorable without losing proof coverage or
functionality. Dead code increases maintenance burden, confuses auditors, and
obscures the actual proof surface. Removing it before the WS-V hardware binding
milestone reduces the surface area that must be maintained during platform work.

**Dependencies**: U5 (API refactoring may create new dead code or revive previously
dead code). Can run in parallel with U6.

**Gate**: `test_full.sh` passes. Line count reduced by ≥3,000 lines. No test
regressions. Zero `sorry`/`axiom`.

**Sub-tasks (12):**

**Intra-phase ordering:**
- Dead module: U7-A (independent)
- Dead types/functions: U7-B → U7-C
- Tautologies: U7-D (independent)
- Bundle cleanup: U7-E (independent)
- Deprecated: U7-F (independent)
- RobinHood: U7-G → U7-H
- native_decide: U7-I (independent)
- Proof robustness: U7-J, U7-K, U7-L (independent)

| ID | Finding | Description | Files | Est. |
|----|---------|-------------|-------|------|
| U7-A | U-L01 | Delete `SeLe4n/Kernel/RobinHood/KMap.lean` (219 lines, never imported). Remove from any re-export hub if present. Verify no downstream references. | `SeLe4n/Kernel/RobinHood/KMap.lean` | Trivial |
| U7-B | U-L02 | Remove dead types and functions. **Sub-steps**: (1) **Architecture/Assumptions.lean** — Remove `TransitionSurface`, `InvariantSurface`, `ContractRef`, `ExtendedBootBoundaryContract`. Verify no imports reference them (`grep` for each name across all `.lean` files). (2) **RPi5/MmioAdapter.lean** — Remove `MmioOp`, `MmioOpKind`, `MemoryBarrier`, `hasAppropriateBarriers`, `isMmioPeripheralAddress`, `isValid`. Note: U6-A may redefine some MMIO types — coordinate with that sub-task to avoid removing types that will be reintroduced. (3) **InformationFlow/Policy.lean** — Remove `bibaPolicy`, `bibaSecurityFlowsTo`, `defaultGenericLabelingContext`, `threeDomainExample`. These are example/illustration definitions not used by any proof. (4) Build each modified module individually to verify no breakage. | Multiple files | Medium (4 sub-steps) |
| U7-C | U-L02 | **(Requires U7-B)** Remove dead functions across 6 files. **Sub-steps**: (1) **Prelude.lean** — Remove `ObjId.valid`, `Deadline.none`, `Deadline.immediate`. These are unused utility functions. (2) **Machine.lean** — Remove `alignedRead`, `alignedWrite`. These were superseded by the MMIO adapter. (3) **FrozenState.lean** — Remove `FrozenMap.fold`, `FrozenSet.mem`, `minObjectSize`, `objectCapacity`. `FrozenMap.fold` was never called; `objectCapacity` is dead since Q5 freeze redesign. (4) **Selection.lean** — Remove `chooseThreadInDomain`. Superseded by EDF-based selection. (5) **RunQueue.lean** — Remove `maxPriorityValue`, `filterToList`, `rotateHead`, `mem_rotateHead`. These are legacy queue utilities replaced by priority-bucket operations. (6) **VSpaceBackend.lean** — Remove `hashMapVSpaceBackend`. Superseded by radix-tree backend. (7) For each removal, verify via `grep -r "functionName"` that no references exist, then build the module. | Multiple files | Medium (7 sub-steps) |
| U7-D | U-L02 | Remove trivial tautology theorems (`f x = f x` proved by `rfl`): `freeze_deterministic`, `objectCapacity_deterministic`, `FrozenMap.get?_deterministic`, `freeze_deterministic'`, `extractMessageRegisters_deterministic`, `decodeSyscallArgs_deterministic`, 9 `*_deterministic` in SyscallArgDecode, `buildCNodeRadix_deterministic`, `frozenLookupObject_deterministic`, `frozenStoreObject_deterministic`, `bootFromPlatform_deterministic`, `PagePermissions.ofNat_deterministic`, `resolveCapAddress_deterministic`. (~15 theorems, ~150 lines) | Multiple files | Small |
| U7-E | U-L02 | Remove superseded invariant bundles (~500 lines). **Sub-steps**: (1) **Scheduler** — Remove `schedulerInvariantBundle` (3-tuple, superseded by `schedulerInvariantBundleFull` 5-tuple). Remove all `schedulerInvariantBundle`-specific preservation theorems. Grep for callers and redirect to `schedulerInvariantBundleFull`. (2) **Capability** — Remove `capabilityInvariantBundleFull` (superseded by `capabilityInvariantBundle`), `WithMintCompleteness`, `WithCdtMaps` wrapper types. These were intermediate constructions during WS-R that are no longer referenced. (3) **Kernel** — Remove `kernelInvariant` (4-tuple, superseded by `proofLayerInvariantBundle`). Redirect any callers. (4) Build all affected modules and run `test_smoke.sh` to verify no regressions. | `SeLe4n/Kernel/Scheduler/Invariant.lean`, `SeLe4n/Kernel/Capability/Invariant/Defs.lean` | Medium (4 sub-steps) |
| U7-F | U-L04 | Remove `processRevokeNode_lenient` (deprecated since v0.18.1). Remove the `@[deprecated]` annotation and the entire function definition. Verify no references remain. | `SeLe4n/Kernel/Capability/Operations.lean` | Trivial |
| U7-G | U-H12 | Fix `BEq RHTable` instance to be symmetric. Add a reverse fold that checks all keys in `b` exist in `a`. The updated instance should satisfy: `a == b ↔ b == a` for well-formed tables. | `SeLe4n/Kernel/RobinHood/Bridge.lean` | Small |
| U7-H | U-H12 | **(Requires U7-G)** Add `beq_symmetric` lemma. **Sub-steps**: (1) State the theorem: `theorem beq_symmetric [BEq κ] [Hashable κ] (a b : RHTable κ υ) (ha : noDupKeys a) (hb : noDupKeys b) (hia : invExt a) (hib : invExt b) : (a == b) = (b == a)`. (2) The proof strategy: under `noDupKeys`, key uniqueness means `a.get? k = b.get? k` for all `k` is equivalent to `b.get? k = a.get? k`. The updated symmetric `BEq` from U7-G makes both directions check the same condition. (3) Verify with `lake build SeLe4n.Kernel.RobinHood.Bridge`. | `SeLe4n/Kernel/RobinHood/Bridge.lean` | Medium (3 sub-steps) |
| U7-I | U-M16 | Migrate 3 `native_decide` uses in `Model/Object/Types.lean` (lines 889, 922) and `Model/Object/Structures.lean` (line 100) to `decide`. These are small-enumeration proofs where `decide` suffices and avoids TCB expansion. Leave `native_decide` in `RPi5/Board.lean` (appropriate for large numeric constants). | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Model/Object/Structures.lean` | Small |
| U7-J | U-M37 | Refactor high-heartbeat Robin Hood proofs. There are **4 `maxHeartbeats` overrides** in `Lookup.lean`: 3.2M (line ~1126, `get_after_insert_eq` main body), 1.6M (line ~1447, `get_after_erase_eq` main body), 800K (lines ~2042, ~2089, helper lemmas). Target: all proofs under 800K (4× default). **Sub-steps**: (1) **Factor insertion phase isolation** — `get_after_insert_eq` (26 lines, lines 856-881) performs a linear scan comparing probe distances. Extract the inner loop invariant into a standalone lemma `insert_probe_chain_preserved : insertNoResize preserves probe chain ordering for keys ≠ k`. This isolates the Robin Hood displacement logic from the lookup correctness argument. (2) **Factor backshift helper** — The erase proof's backshift loop (moving entries backward after deletion) is the main heartbeat consumer. Extract `backshift_preserves_get : ∀ k' ≠ k, backshift table pos k' = table.get? k'` as a standalone lemma with its own proof by induction on the backshift chain length. (3) **Factor resize proof** — The resize path (insert triggering grow) duplicates the insertion proof for the new table. Extract `grow_preserves_all_entries : ∀ k, (grow table).get? k = table.get? k` as a standalone lemma. This avoids re-proving lookup correctness through the resize. (4) **Reduce heartbeats** — With the 3 helper lemmas factored out, rewrite `get_after_insert_eq` and `get_after_erase_eq` to call the helpers instead of inlining the arguments. Target: main theorems at ≤800K, helpers at ≤400K (2× default). (5) **Verify** — `lake build SeLe4n.Kernel.RobinHood.Invariant.Lookup` with no `maxHeartbeats` override above 800K. | `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` | Large (5 sub-steps) |
| U7-K | U-L21 | Replace fragile `simp [Function.update]` chains in scheduler preservation proofs. **Sub-steps**: (1) **Identify fragile sites** — Grep for `simp [Function.update]` in `Preservation.lean` (~2170 lines). Count occurrences and identify the proof contexts (thread priority update, domain schedule rotation, queue manipulation). (2) **Extract reusable lemmas** — Define `@[simp] lemma function_update_same (f : α → β) (a : α) (b : β) : Function.update f a b a = b`, `@[simp] lemma function_update_ne (f : α → β) (a a' : α) (b : β) (h : a' ≠ a) : Function.update f a b a' = f a'`, and `@[simp] lemma function_update_idem (f : α → β) (a : α) (b b' : β) : Function.update (Function.update f a b) a b' = Function.update f a b'` in a new `SeLe4n/Kernel/Scheduler/Operations/Lemmas.lean` or in `Prelude.lean`. (3) **Rewrite proofs** — Replace each `simp [Function.update, ...]` chain with `simp` (the `@[simp]` lemmas fire automatically) or explicit `rw [function_update_same]` / `rw [function_update_ne]` calls. (4) **Verify** — Build `SeLe4n.Kernel.Scheduler.Operations.Preservation` and confirm no `maxHeartbeats` increase. | `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` | Medium (4 sub-steps) |
| U7-L | U-L07 | Add formal commutativity proofs between builder and frozen operations. Investigation found **7 builder operations** (in `Builder.lean`) and **12 frozen operations** (in `FrozenOps/Operations.lean`). The 5 operations shared between both phases are: `storeObject`/`frozenStoreObject`, `lookupObject`/`frozenLookupObject`, `storeThread`/`frozenStoreThread`, `lookupThread`/`frozenLookupThread`, and `updateCdt`/`frozenUpdateCdt`. **Sub-steps**: (1) **Store commutativity** — Prove `freeze (builderStoreObject id obj ist) = frozenStoreObject id obj (freeze ist)`. The builder stores into an `RHTable`; the frozen op stores into a `FrozenMap`. The existing `freezeLookupEquiv` proves lookup equivalence; the store direction needs proving that `freeze ∘ RHTable.insert = FrozenMap.set ∘ freeze`. (2) **Lookup commutativity** — Prove `freeze` then `frozenLookupObject` = `builderLookupObject` then identity. This should follow directly from `freezeLookupEquiv`. (3) **Thread store/lookup commutativity** — Same pattern as (1)/(2) but for the thread table. Likely near-identical proofs since both use `RHTable`→`FrozenMap`. (4) **CDT update commutativity** — Prove CDT edge insertion commutes with freeze. The CDT uses a different structure (edge list), so this proof has a distinct shape: `freeze (addEdge parent child ist) = frozenAddEdge parent child (freeze ist)`. (5) **Composition theorem** — Prove that any sequence of the 5 shared operations commutes with freeze: if `ops` is a sequence of builder operations, then `freeze (ops ist) = frozenOps (freeze ist)` where `frozenOps` is the corresponding frozen sequence. This is a fold-based induction over the operation list. | `SeLe4n/Model/FreezeProofs.lean` | Large (5 sub-steps) |

---

### Phase U8 — Documentation & Closure (v0.21.7)

**Scope**: Final documentation synchronization, remaining LOW findings, workstream
closure report, and comprehensive validation.

**Rationale**: This phase ensures all documentation reflects the changes made in
U1–U7, closes remaining LOW findings that are purely documentation or minor
hardening, and produces the closure report for WS-U.

**Dependencies**: U6, U7 (all code changes must be complete).

**Gate**: `test_full.sh` passes. `NIGHTLY_ENABLE_EXPERIMENTAL=1 test_nightly.sh`
passes. Documentation synchronized per PR checklist. Zero `sorry`/`axiom`.
Workstream closure report written.

**Sub-tasks (8):**

**Intra-phase ordering:**
- All sub-tasks are independent except U8-H (closure) which requires all others.

| ID | Finding | Description | Files | Est. |
|----|---------|-------------|-------|------|
| U8-A | U-L16 | Eliminate `simSubstantiveMemoryMap` duplication. Either derive it from `simMachineConfig.memoryMap` at compile time, or add a compile-time consistency theorem proving they are equal. | `SeLe4n/Platform/Sim/RuntimeContract.lean` | Small |
| U8-B | U-L18, U-L19 | Document IRQ/INTID range limitations: SGIs (0-15) are for IPIs not hardware interrupts, GIC INTID cap at 223 may miss BCM2712 extended peripherals. Add comments in `RPi5/BootContract.lean` and `RPi5/Board.lean`. | `SeLe4n/Platform/RPi5/BootContract.lean`, `SeLe4n/Platform/RPi5/Board.lean` | Trivial |
| U8-C | U-L24 | Document notification word overflow: add comment in IPC operations explaining that notification word merge uses unbounded Nat (no overflow in model), and that hardware binding (WS-V) must enforce 64-bit word width. | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | Trivial |
| U8-D | U-L26 | Document scheduler design decisions: add comment explaining `recomputeMaxPriority` is O(p) on priority-bucket removal (acceptable for <256 priorities), and that starvation freedom is not guaranteed (matching seL4 fixed-priority design). | `SeLe4n/Kernel/Scheduler/RunQueue.lean`, `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | Trivial |
| U8-E | U-M35 | Document hash collision assumption in Robin Hood proofs: add comment explaining that `get_after_insert`/`get_after_erase` assume no hash collisions for distinct keys. Note that collision resistance is not formally modeled but mitigated by using typed identifiers (not adversary-controlled keys). | `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` | Trivial |
| U8-F | — | Synchronize documentation per CLAUDE.md rules: update `README.md` metrics, `docs/spec/SELE4N_SPEC.md`, `docs/DEVELOPMENT.md`, affected GitBook chapters, `docs/CLAIM_EVIDENCE_INDEX.md`, and `docs/WORKSTREAM_HISTORY.md`. Regenerate `docs/codebase_map.json`. | `docs/` | Medium |
| U8-G | — | Run comprehensive validation: `test_full.sh`, `NIGHTLY_ENABLE_EXPERIMENTAL=1 test_nightly.sh`, `cargo test --workspace`, verify zero `sorry`/`axiom` via grep. | Scripts | Small |
| U8-H | — | **(Requires all above)** Write WS-U closure report documenting all findings addressed, erroneous findings identified, and remaining items deferred to WS-V. Follow the format of `docs/dev_history/audits/WS_T_CLOSURE_REPORT.md`. | `docs/dev_history/audits/WS_U_CLOSURE_REPORT.md` | Medium |

---

## 7. Phase Summary & Effort Estimates

| Phase | Version | Sub-tasks | Findings Addressed | Est. Effort | Critical Path |
|-------|---------|-----------|-------------------|-------------|---------------|
| U1 | v0.21.0 | 13 | U-H01, U-H02, U-H03, U-H04, U-H13, U-H14, U-M39 | Medium | Yes |
| U2 | v0.21.1 | 14 | U-H05, U-H06, U-H07, U-H08, U-L03, U-M17, U-M18, U-M20 | Large | Yes |
| U3 | v0.21.2 | 10 | U-H11, U-M32, U-M33, U-M34, U-L08-L13 | Medium | No (parallel) |
| U4 | v0.21.3 | 14 | U-H09, U-H10, U-M05, U-M06, U-M19, U-M25, U-M26, U-M31, U-M38 | Very Large | Yes |
| U5 | v0.21.4 | 14 | U-M01-M04, U-M07, U-M21, U-M28-M30, U-L05, U-L06, U-L20, U-L27 | Medium | Yes |
| U6 | v0.21.5 | 12 | U-M08-M10, U-M12-M15, U-M22-M24 | Large | Yes |
| U7 | v0.21.6 | 12 | U-H12, U-L01, U-L02, U-L04, U-L07, U-L21, U-M16, U-M35-M37 | Large | No (parallel) |
| U8 | v0.21.7 | 8 | U-L16, U-L18, U-L19, U-L24, U-L26, U-M35 + docs | Medium | Yes (final) |
| **Total** | | **97** | **81 findings** | | |

**Estimated version range**: v0.21.0 – v0.21.7 (8 releases)

**Decomposition depth**: 8 Large tasks expanded into 41 discrete sub-steps.
14 Medium tasks expanded with detailed sub-step guidance. Total atomic work
units (sub-tasks + sub-steps): ~180. Each sub-step is scoped to a single
proof obligation, function modification, or verification check.

**Optimization notes**:
- U4-A/B share 8 identical "untouched field" lemmas — implement once, reuse.
- U4-C's `projectState_preserved_trans` is reusable for any multi-step op.
- U7-B must coordinate with U6-A (MMIO types may be removed then reintroduced).
- U7-E should run AFTER U4-H/U4-K (which may reference superseded bundles).
- U7-L depends on `freezeLookupEquiv` stability from U6-G — if U6-G modifies
  `FreezeProofs.lean`, U7-L should re-verify its anchor lemmas.

---

## 8. Items Deferred to WS-V (Hardware Binding)

The following findings are explicitly deferred to WS-V because they require
hardware-specific implementation that depends on the RPi5 platform binding:

| Finding | Rationale for Deferral |
|---------|----------------------|
| S-01 (O(n) scheduler) | Performance optimization requires profiling on real hardware |
| S-02 (abstract timer) | ARM Generic Timer binding is a WS-V deliverable |
| I-02 (single-core IPC) | Multi-core IPC requires per-core endpoint queues (WS-V) |
| AR-05 (TLB flush model) | Asynchronous TLBI + DSB + ISB requires ARM64 barrier model |
| AR-08 (GPU split) | Boot-time `config.txt` configuration parsing |
| IP-06 (IPC buffer memory) | Memory-mapped IPC buffer requires VSpace integration |
| IP-07 (notification binding) | Bound-notification optimization deferred |
| ML-04 (Memory model) | MMIO side effects and out-of-bounds representation |
| User: nbSend/nbRecv/replyRecv | Non-blocking variants and combined operations |
| S-04 (List-based queues) | Array conversion requires proof impact assessment |
| C-01 (revokeCap O(n)) | CDT depth bound requires profiling data |
| IF-05 (wrapper duplication) | Pre/post-condition framework is a design-level change |
| P-12 (4 GB RPi5 only) | Multi-model support requires hardware variants |

---

## 9. Finding-to-Phase Traceability Matrix

Every confirmed finding maps to exactly one phase. No finding is left unaddressed.

| Finding | Phase | Sub-task(s) |
|---------|-------|-------------|
| U-H01 | U1 | U1-A, U1-B, U1-C |
| U-H02 | U1 | U1-D, U1-E |
| U-H03 | U1 | U1-L |
| U-H04 | U1 | U1-F, U1-G |
| U-H05 | U2 | U2-I, U2-J |
| U-H06 | U2 | U2-A, U2-B, U2-C |
| U-H07 | U2 | U2-D, U2-E, U2-F |
| U-H08 | U2 | U2-G, U2-H |
| U-H09 | U4 | U4-A, U4-B, U4-C, U4-D |
| U-H10 | U4 | U4-E, U4-F |
| U-H11 | U3 | U3-A |
| U-H12 | U7 | U7-G, U7-H |
| U-H13 | U1 | U1-J, U1-K |
| U-H14 | U1 | U1-H, U1-I |
| U-M01 | U5 | U5-B |
| U-M02 | U5 | U5-A, U5-D |
| U-M03 | U5 | U5-H |
| U-M04 | U5 | U5-C |
| U-M05 | U4 | U4-G, U4-H |
| U-M06 | U4 | U4-I |
| U-M07 | U5 | U5-E |
| U-M08 | U6 | U6-A, U6-B |
| U-M09 | U6 | U6-C, U6-D |
| U-M10 | U6 | U6-H |
| U-M11 | U2 | U2-E |
| U-M12 | U6 | U6-E |
| U-M13 | U6 | U6-F |
| U-M14 | U6 | U6-L |
| U-M15 | U6 | U6-G |
| U-M16 | U7 | U7-I |
| U-M17 | U2 | U2-N |
| U-M18 | U2 | U2-L |
| U-M19 | U4 | U4-N |
| U-M20 | U2 | U2-M |
| U-M21 | U5 | U5-F, U5-G |
| U-M22 | U6 | U6-I |
| U-M23 | U6 | U6-K |
| U-M24 | U6 | U6-J |
| U-M25 | U4 | U4-M |
| U-M26 | U4 | U4-L |
| U-M27 | U4 | U4-J (via CDT cleanup) |
| U-M28 | U5 | U5-I |
| U-M29 | U5 | U5-J |
| U-M30 | U5 | U5-K |
| U-M31 | U4 | U4-K |
| U-M32 | U3 | U3-B, U3-C |
| U-M33 | U3 | U3-D, U3-E |
| U-M34 | U3 | U3-I |
| U-M35 | U8 | U8-E |
| U-M36 | U7 | (covered by U7-G symmetric BEq fix) |
| U-M37 | U7 | U7-J |
| U-M38 | U4 | U4-J |
| U-M39 | U1 | U1-M |
| U-L01 | U7 | U7-A |
| U-L02 | U7 | U7-B, U7-C, U7-D, U7-E |
| U-L03 | U2 | U2-K |
| U-L04 | U7 | U7-F |
| U-L05 | U5 | U5-L |
| U-L06 | U5 | U5-M |
| U-L07 | U7 | U7-L |
| U-L08 | U3 | U3-F |
| U-L09 | U3 | U3-G |
| U-L10 | U3 | U3-H |
| U-L11 | U3 | (included in U3-J) |
| U-L12 | U3 | (included in U3-J) |
| U-L13 | U3 | U3-J |
| U-L14 | — | Deferred (cosmetic) |
| U-L15 | — | Deferred (cosmetic) |
| U-L16 | U8 | U8-A |
| U-L17 | U2 | U2-E |
| U-L18 | U8 | U8-B |
| U-L19 | U8 | U8-B |
| U-L20 | U5 | U5-D |
| U-L21 | U7 | U7-K |
| U-L22 | — | Deferred to WS-V (performance) |
| U-L23 | — | Deferred (cosmetic) |
| U-L24 | U8 | U8-C |
| U-L25 | — | Deferred (cosmetic) |
| U-L26 | U8 | U8-D |
| U-L27 | U5 | U5-N |
| U-L28 | U1 | U1-J |

---

*Workstream plan created 2026-03-24, expanded 2026-03-25. Baseline: seLe4n v0.20.7.
Four audit sources, 12 erroneous findings excluded, 81 confirmed findings
organized into 8 phases with 97 atomic sub-tasks (~180 discrete sub-steps).
All Large tasks decomposed to per-field/per-conjunct/per-operation granularity.
Key errata corrected: NonInterferenceStep has 33 constructors (not 34),
CDT deletion logic lives in cspaceDeleteSlot (no standalone deleteObject).*
