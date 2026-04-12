# Comprehensive Pre-Release Audit — v0.27.6

**Date**: 2026-04-12
**Scope**: Full codebase (159 Lean files, 48 Rust files)
**Auditor**: Claude (Opus 4.6)
**Methodology**: Line-by-line review of every kernel module via parallel subsystem audits

## Executive Summary

This audit covers every Lean module and every Rust source file in the seLe4n
microkernel ahead of the first major release and benchmarking phase. The audit
specifically targets:

1. **Production reachability** — identifying modules that exist but are not
   transitively imported by the production entry point
2. **Security vulnerabilities** — capability escalation, information leaks, W^X
   violations, side channels
3. **Correctness gaps** — proof incompleteness, externalized hypotheses, silent
   error swallowing
4. **Dead code** — functions tested but never called from production dispatch
5. **Deferred work** — cataloguing all WS-V and other deferred items
6. **Documentation accuracy** — verifying that comments match code behavior
7. **Lean–Rust ABI alignment** — verifying type, enum, and constant parity

**Policy Compliance**: Zero `sorry`, zero `axiom`, zero `native_decide` in all
159 Lean files. The codebase is fully machine-checked.

**Version Consistency**: All version references (lakefile.toml, Cargo workspace,
KERNEL_VERSION, crate versions) are synchronized at `0.27.6`.

---

## Table of Contents

1. [Production Reachability Analysis](#1-production-reachability-analysis)
2. [Findings by Severity](#2-findings-by-severity)
3. [Subsystem Audit Details](#3-subsystem-audit-details)
4. [Lean–Rust ABI Alignment](#4-leanrust-abi-alignment)
5. [Deferred Work Inventory](#5-deferred-work-inventory)
6. [Recommendations](#6-recommendations)

---

## 1. Production Reachability Analysis

The production entry point is `SeLe4n.lean` (imported by `Main.lean`). Modules
reachable transitively from this root constitute the "production chain." Modules
that exist on disk but are NOT in this chain are either test-only, experimental,
or dead code.

### 1.1 Unreachable Modules (Not in Production Chain)

| Module | Category | Status |
|--------|----------|--------|
| `SeLe4n.Platform.FFI` | Hardware bridge | **17 @[extern] declarations with zero callers** |
| `SeLe4n.Kernel.FrozenOps` (+ 4 submodules) | Experimental | Test-only (imported by 5 test suites) |
| `SeLe4n.Kernel.Architecture.AsidManager` | Hardware model | Not imported by any module |
| `SeLe4n.Kernel.Architecture.CacheModel` | Hardware model | Not imported by any module |
| `SeLe4n.Kernel.Architecture.ExceptionModel` | Hardware model | Not imported by any module |
| `SeLe4n.Kernel.Architecture.InterruptDispatch` | Hardware model | Not imported by any module |
| `SeLe4n.Kernel.Architecture.PageTable` | Hardware model | Not imported by any module |
| `SeLe4n.Kernel.Architecture.TimerModel` | Hardware model | Not imported by any module |
| `SeLe4n.Kernel.Architecture.VSpaceARMv8` | Hardware model | Not imported by any module |
| `SeLe4n.Kernel.Scheduler.PriorityInheritance` (hub) | Re-export hub | Submodules imported directly; hub unused |

**Key observation**: 7 Architecture modules (AG3–AG8 deliverables) representing
substantial work in exception handling, interrupt dispatch, page tables, ASID
management, cache coherency, timer binding, and ARMv8 VSpace are completely
disconnected from the production kernel. These were built during hardware binding
phases but never wired into the production import chain.

### 1.2 Dead Code in Production Modules

| Function | File | Evidence |
|----------|------|----------|
| `cleanupPreReceiveDonation` | `IPC/Operations/Donation.lean:191` | Tested in MainTraceHarness but zero callers in API dispatch |
| `syncThreadStates` / `inferThreadState` | `Scheduler/Operations/Core.lean` | Test-only (InvariantChecks, MainTraceHarness) |
| `storeObjectChecked` | `Model/State.lean` | Defined but unused in production |
| `DeviceTree.fromDtb` | `Platform/DeviceTree.lean:139` | Stub that always returns `none` |

### 1.3 Re-export Hub Audit

All 15 re-export hubs were verified. The `Scheduler/Liveness.lean` hub imports
only `WCRT` but is functionally correct because the Liveness submodules form a
linear import chain (WCRT → DomainRotation → BandExhaustion → Yield →
Replenishment → TimerTick → TraceModel). This is a style inconsistency compared
to other hubs that import all submodules explicitly.

## 2. Findings by Severity

### 2.1 HIGH Severity

| ID | Subsystem | File | Description |
|----|-----------|------|-------------|
| H-01 | Platform | `Sim/BootContract.lean` | Simulation boot contract is vacuously `True` for all 4 predicates — tests never validate boot invariants |
| H-02 | Platform | `Sim/BootContract.lean` | Simulation interrupt contract accepts ALL IRQs — IRQ validation bugs invisible in testing |
| H-03 | Architecture | `InterruptDispatch.lean:127` | Missing EOI on interrupt handle error — GIC becomes interrupt-deaf (unreachable in production) |
| H-04 | Rust | `sele4n-hal/src/trap.rs:159` | Syscall dispatch handler is a no-op stub — primary Lean–Rust integration point is dead |
| H-05 | Rust | `sele4n-hal/src/trap.rs:178` | Exception handler returns wrong error codes: alignment/unknown → 43 (`alignmentError`) instead of 45 (`userException`) — Lean model mismatch |

### 2.2 MEDIUM Severity

| ID | Subsystem | File | Description |
|----|-----------|------|-------------|
| M-01 | IPC | `Donation.lean:191` | `cleanupPreReceiveDonation` tested but never called from production API dispatch — donated SchedContext can leak on abnormal receive-without-reply path |
| M-02 | Scheduler | `API.lean` | `resolveExtraCaps` silently drops unresolvable extra caps without error indication |
| M-03 | Scheduler | `RunQueue.lean` | `RunQueue.size` field not proof-linked to actual bucket lengths |
| M-04 | Scheduler | `Core.lean` | `handleYield` re-enqueues at base priority instead of effective (PIP-aware) priority |
| M-05 | Scheduler | `Core.lean` | `timeoutBlockedThreads` discards per-thread timeout errors |
| M-06 | Platform | `FFI.lean` | 17 `@[extern]` FFI declarations with zero production importers — entire hardware bridge disconnected |
| M-07 | Platform | `Boot.lean:503` | Boot invariant bridge proven only for empty `PlatformConfig`; general config requires `bootSafe` |
| M-08 | Platform | `DeviceTree.lean:139` | `fromDtb` stub always returns `none`; `fromDtbFull` exists alongside unused |
| M-09 | Platform | `DeviceTree.lean:618` | DTB parser fuel=2000 — silently drops all peripherals on large DTBs |
| M-10 | Platform | `MmioAdapter.lean:351` | MMIO read returns RAM semantics for volatile registers |
| M-11 | Platform | `Boot.lean:962` | `bootSafeObject` excludes VSpaceRoots — no pre-configured address spaces at boot |
| M-12 | Capability | `Operations.lean:85` | `resolveCapAddress` skips intermediate CNode read-right checks — side-channel vs seL4 |
| M-13 | Architecture | `VSpace.lean:192` | Physical address bounds default to 2^52 instead of platform-specific width |
| M-14 | Architecture | `VSpaceARMv8.lean:189` | `unmapPage` silently succeeds when HW walk fails — shadow/HW divergence |
| M-15 | Architecture | `AsidManager.lean:90` | ASID reuse path has no type-level TLB flush enforcement |
| M-16 | Architecture | `CacheModel.lean:269` | D-cache → I-cache pipeline ordering not modeled |
| M-17 | Architecture | `Adapter.lean:136` | Context switch state doesn't model TLB/ASID maintenance |
| M-18 | Architecture | Multiple | No cross-module composition for TLB + cache + page table invariants |
| M-19 | InfoFlow | `Policy.lean:219` | `defaultLabelingContext` defeats all security with no runtime guard |
| M-20 | Lifecycle | `Suspend.lean:150` | `suspendThread` transient metadata inconsistency during donation return |
| M-21 | Model | `Structures.lean:2246` | CDT `descendantsOf` fuel sufficiency proven only to depth 1 |
| M-22 | SchedContext | `PriorityManagement.lean:99` | `migrateRunQueueBucket` ignores PIP boost during priority change |
| M-23 | Liveness | `BlockingGraph.lean:79` | `blockingChain` silent truncation on fuel exhaustion — no cycle detection |
| M-24 | Liveness | `BandExhaustion.lean:34` | `eventuallyExits` hypothesis unproven for unbound threads |
| M-25 | Liveness | `WCRT.lean:167` | Main WCRT theorem has two externalized hypotheses not derived from kernel invariants |
| M-26 | Rust | `ffi.rs:40` / `trap.rs:196` | Dual timer reprogram path could double-count ticks when Lean FFI is wired |
| M-27 | Rust | `uart.rs:179` | `static mut BOOT_UART` is `pub` with no synchronization — UB after interrupts enabled |

### 2.3 LOW Severity

| ID | Subsystem | Description |
|----|-----------|-------------|
| L-01 | Model | Unbounded `Nat` identifiers — ABI bridge must bounds-check |
| L-02 | Model | `allTablesInvExtK` 17-deep tuple projection fragility |
| L-03 | IPC | Notification wait is LIFO not FIFO (spec-compliant) |
| L-04 | IPC | `donateSchedContext` doesn't independently check server binding |
| L-05 | IPC | `timeoutAwareReceive` unused `_endpointId` parameter |
| L-06 | Capability | CDT acyclicity externalized for expanding operations |
| L-07 | Capability | `cspaceRevokeCdt` materializes full descendant list upfront |
| L-08 | Capability | Arbitrary badge values possible through mint (matches seL4) |
| L-09 | Scheduler | `saveOutgoingContext` silent failure on TCB lookup miss |
| L-10 | Scheduler | `configDefaultTimeSlice` positivity not structurally enforced |
| L-11 | SchedContext | `schedContextYieldTo` silent no-op on missing objects |
| L-12 | SchedContext | Truncation drops nearest-eligible replenishments |
| L-13 | SchedContext | `schedContextBind` doesn't check thread state |
| L-14 | SchedContext | `pip_bounded_inversion` uses object count not thread count |
| L-15 | Liveness | Stale documentation references non-existent `maxBlockingDepth` |
| L-16 | Liveness | CBS bandwidth bound 8× weaker than ideal (documented) |
| L-17 | Liveness | Admission control ~6.4% over-admission from integer truncation |
| L-18 | Architecture | Bump allocator has no page table memory reclamation |
| L-19 | Architecture | InterruptId bound hardcoded to BCM2712 (not parameterized) |
| L-20 | Architecture | Timer division truncation not guarded |
| L-21 | Architecture | Targeted TLB flush not wired into production paths |
| L-22 | Platform | `extractPeripherals` limited to 2-level DTB depth |
| L-23 | Platform | `bootFromPlatform` accepts empty config without validation |
| L-24 | Platform | RPi5 RuntimeContract doc says "stub" despite being substantive |
| L-25 | InfoFlow | `pendingMessage` visibility formal bridge to declassification not proven |
| L-26 | Lifecycle | `lifecycleRetypeObject` public despite internal-only intent |
| L-27 | RadixTree | `lookup_insert_ne` requires distinct radix indices, not just distinct keys |
| L-28 | Testing | StateBuilder does not check IPC/SchedContext/CDT invariants |

## 3. Subsystem Audit Details

### 3.1 Prelude + Model Layer (10 files, ~10,822 lines)

**Status**: Sound. Zero sorry/axiom/admit. All typed identifiers use wrapper
structures (not `Nat` aliases). Non-lawful `BEq` instances formally documented
with negative witnesses. CDT acyclicity proven via `edgeWellFounded`. Freeze
correctness comprehensive (per-field lookup equivalence, CNode radix equivalence,
invariant transfer, builder-frozen commutativity).

**Key concern**: CDT `descendantsOf` fuel sufficiency proven only to depth 1
(M-21). The transitive closure proof connecting `edgeWellFounded` to BFS
termination is deferred.

### 3.2 API + Scheduler (7 files, ~8,500 lines)

**Status**: Sound. All 25 SyscallId variants handled in dispatch. Wildcard
unreachability proven. All transitions are pure functions — no TOCTOU possible.
`isBetterCandidate` proven irreflexive, asymmetric, transitive.

**Key concerns**: `handleYield` uses base priority instead of effective priority
(M-04); `resolveExtraCaps` silently drops unresolvable caps (M-02);
`timeoutBlockedThreads` discards per-thread errors (M-05).

### 3.3 IPC Subsystem (20 files, ~22,000 lines)

**Status**: Sound. 15-conjunct `ipcInvariantFull` with machine-checked
composition. Proper message payload bounds at every IPC boundary. Reply-target
authorization prevents confused-deputy. Donation atomicity formally proven.
Queue link integrity doubly-linked with acyclicity proofs.

**Key concern**: `cleanupPreReceiveDonation` is tested in MainTraceHarness but
has zero callers in API dispatch (M-01). On the abnormal path where a server
does `.receive` without replying to a previous `.call`, the donated
SchedContext leaks.

### 3.4 Capability Subsystem (5 files, ~5,780 lines)

**Status**: Sound. Mint authority attenuation machine-checked bidirectionally.
Occupied-slot guard prevents capability overwrite. Revoke source preservation
proven. Complete preservation proof coverage for all operations. CPtr masking
at 64-bit boundary for model-hardware consistency.

**Key concern**: `resolveCapAddress` skips intermediate CNode read-right checks
(M-12), creating an information side-channel compared to seL4.

### 3.5 Architecture Subsystem (17 files, ~6,500 lines)

**Status**: Mixed. Production-reachable modules (VSpace, VSpaceBackend, TlbModel,
RegisterDecode, SyscallArgDecode) are sound. 7 unreachable modules (PageTable,
VSpaceARMv8, AsidManager, CacheModel, ExceptionModel, InterruptDispatch,
TimerModel) contain substantial work but are disconnected from production.

**Key concerns**: Missing EOI on interrupt error (H-03, unreachable); shadow/HW
divergence on unmapPage failure (M-14); ASID reuse without flush enforcement
(M-15); context switch doesn't model TLB/ASID (M-17).

### 3.6 Information Flow (9 files, ~10,000 lines)

**Status**: Excellent. 35-operation NI coverage verified at compile time with
injective and surjective witnesses. Enforcement boundary completeness
machine-checked via `decide`. Declassification boundary well-defined.

**Key concern**: `defaultLabelingContext` defeats all security (M-19). No
runtime guard prevents deployment with the insecure default.

### 3.7 Service Subsystem (7 files, ~3,200 lines)

**Status**: Sound. Dependency acyclicity proven with BFS completeness bridge.
Registry endpoint uniqueness enforced. DFS cycle detection conservative (returns
`true` on fuel exhaustion — never misses cycles).

### 3.8 Lifecycle Subsystem (4 files, ~2,800 lines)

**Status**: Sound. 10-guard chain in `retypeFromUntyped`. Dangling-reference
prevention proven. Memory scrubbing on retype. `suspendThread` 5-step
composite correctly sequences PIP revert, donation cleanup, state clear.

**Key concern**: Transient metadata inconsistency during `suspendThread` donation
return (M-20) — safe in sequential model, concern for hardware binding.

### 3.9 SchedContext + PIP + Liveness (24 files, ~7,000 lines)

**Status**: Sound with documented proof gaps. CBS budget operations correct.
PIP propagation bounded by object index length. WCRT formula correctly
composes domain and band sub-bounds.

**Key concerns**: WCRT theorem has two externalized hypotheses (M-25);
`eventuallyExits` unproven for unbound threads (M-24); blocking chain
silently truncates on fuel exhaustion (M-23).

### 3.10 RobinHood + RadixTree + FrozenOps (18 files, ~12,000 lines)

**Status**: Sound. Robin Hood displacement algorithm correct with comprehensive
PCD preservation. RadixTree bit extraction proven. FrozenOps confirmed
experimental/test-only. Cross-subsystem invariant has complete 10-predicate
bundle with bridge coverage for all 34 operations.

### 3.11 Platform + Testing (19 files, ~8,000 lines)

**Status**: Mixed. Boot sequence structurally correct. RPi5 platform binding
substantive. Device tree parser has proper bounds checking. Test infrastructure
uses `buildChecked` for state construction.

**Key concerns**: FFI.lean completely disconnected (M-06); simulation contracts
vacuously true (H-01, H-02); DTB parser fuel exhaustion silent (M-09).

### 3.12 Rust Workspace (4 crates, 48 files, ~7,500 lines)

**Status**: Mostly sound. 362 tests pass, 0 clippy warnings. SyscallId and
KernelError discriminants match Lean exactly. GIC-400, PL011, MMU, TLB flush
sequences verified correct against ARM reference manuals. Unsafe code properly
confined to `sele4n-hal` with `#[cfg(target_arch = "aarch64")]` guards.
Speculation barriers (CSDB) correctly placed in security-critical paths.

**Key concern**: `trap.rs` exception handler returns wrong error codes for
alignment faults and unknown exceptions — uses discriminant 43
(`alignmentError`) where Lean model specifies 45 (`userException`). This is a
refinement gap between the verified model and hardware-facing runtime (H-05).
Also: dual timer reprogram path could double-count ticks when Lean FFI is
wired (M-26); `static mut BOOT_UART` is unsound after interrupts are enabled
(M-27).

## 4. Lean–Rust ABI Alignment

### 4.1 SyscallId (25 variants, 0–24)

All 25 Lean `SyscallId` variants match Rust `SyscallId` `#[repr(u64)]`
discriminants exactly. `syscallRequiredRight` in `API.lean` matches
`SyscallId::required_right()` in `syscall.rs` for all 25 arms.

### 4.2 KernelError (49 variants, 0–48)

All 49 Lean `KernelError` variants match Rust `KernelError` `#[repr(u32)]`
discriminants 0–48. Rust adds `UnknownKernelError = 255` as a forward-
compatibility sentinel (AF6-A). Gap 49–254 correctly returns `None`.

### 4.3 Version Consistency

| Source | Version |
|--------|---------|
| `lakefile.toml` | 0.27.6 |
| `rust/Cargo.toml` (workspace) | 0.27.6 |
| `KERNEL_VERSION` (boot.rs) | 0.27.6 |
| All 4 crate `Cargo.toml` | `version.workspace = true` (inherits 0.27.6) |

### 4.4 AccessRight

Lean `AccessRight` = {read, write, grant, retype} maps to Rust `AccessRight`
`#[repr(u32)]` = {Read=1, Write=2, Grant=4, Retype=8}. Bit positions align.

## 5. Deferred Work Inventory

### 5.1 WS-V / Future Workstream (29 items)

**HIGH priority (1 item)**:
- Syscall dispatch stub in `trap.rs` — must be implemented before hardware
  bring-up

**MEDIUM priority (12 items)**:
- CDT `descendantsOf` fuel sufficiency formal proof (AG8-E)
- Donation chain k>2 formal bridge (AG8-F)
- Cross-subsystem composition proof (10 predicates × 33 operations)
- Memory projection for NI model (WS-H11 dependency)
- Boot invariant bridge for general configs
- MMIO read result opacity
- VM fault handler in `trap.rs`
- 7 Architecture modules not wired into production (~3,500 lines proven code)
- ARMv8 VSpace simulation relation proofs
- IPC cap transfer loop inductive composition
- IPC buffer receiver slot base (defaults to slot 0)
- Speculation mitigations (PAC/BTI/Shadow stack)

**LOW priority (16 items)**:
- FrozenOps promotion from experimental status
- Service orchestration NI
- `pendingMessage` NI unreachability proof
- Boot minimum-configuration validation
- VSpaceRoot boot support
- Tuple-to-structure invariant refactoring
- `DeviceTree.fromDtb` stub wiring
- MMIO write semantics refinement
- Memory barrier multi-core semantics
- Context-switch register proof hooks
- GIC SPI count extension
- Notification word 64-bit enforcement
- BumpAllocator reclamation
- Thread-level time slices (MCS)
- Bounded-memory / GC semantics
- VSpaceBackend and targeted TLB flush production wiring

### 5.2 Tracked Proof Items (TPI-D Series)

| TPI | Status | Description |
|-----|--------|-------------|
| TPI-D04 | CLOSED | Badge-override safety in cspaceMint |
| TPI-D05 | CLOSED | VSpace invariant preservation |
| TPI-D07 | CLOSED | Service dependency acyclicity |
| TPI-D08 | CLOSED | Dual-queue preservation |
| TPI-D09 | Open | Compound operation preservation |
| TPI-D12 | Open | TCB-existence helpers for scheduler preservation |
| TPI-DOC | Open | `collectQueueMembers` fuel sufficiency formal bridge |

### 5.3 Rust Stubs Requiring Implementation

| File | Line | Description | Severity |
|------|------|-------------|----------|
| `trap.rs` | 159 | SVC handler returns 0 (no-op) | HIGH |
| `trap.rs` | 140 | Data/Instruction Abort placeholder | MEDIUM |
| `vectors.S` | 37–116 | 8 exception vectors → WFE loop | MEDIUM |
| `ipc.rs` | 21 | IPC buffer >4 registers not modeled | MEDIUM |

## 6. Recommendations

### 6.1 Critical Path for Hardware Bring-up

1. **Wire FFI.lean into production** — Import `SeLe4n.Platform.FFI` from
   RPi5 platform binding. Verify `@[extern]` signatures match `ffi.rs`.
2. **Wire 7 Architecture modules** — Import AsidManager, ExceptionModel,
   InterruptDispatch, PageTable, TimerModel, CacheModel, VSpaceARMv8 from
   appropriate production modules.
3. **Implement syscall dispatch stub** — Replace `trap.rs:159` no-op with
   actual Lean FFI dispatch.
4. **Fix EOI-on-error** — `InterruptDispatch.lean:127` must send EOI before
   returning error.
5. **Wire `cleanupPreReceiveDonation` into production** — Add call before
   server blocks on receive in API.lean `.receive` dispatch path.

### 6.2 Proof Gap Closure

1. CDT `descendantsOf` transitive fuel sufficiency (M-21)
2. Donation chain k>2 formal bridge (AG8-F)
3. WCRT externalized hypotheses documentation (M-25)
4. Cross-module TLB + cache + page table composition (M-18)

### 6.3 Testing Improvements

1. Create substantive simulation boot/interrupt contracts (H-01, H-02)
2. Add IPC/SchedContext/CDT invariant checks to StateBuilder (L-28)
3. Wire RPi5 restrictive contracts into simulation test configuration
4. Add runtime `assertProofLayerInvariantBundle` to checked boot path

### 6.4 Scheduler Correctness

1. Migrate `handleYield` to effective priority re-enqueue (M-04)
2. Propagate `timeoutBlockedThreads` errors (M-05)
3. Add `migrateRunQueueBucket` PIP awareness (M-22)

---

**Finding Count Summary**:
- CRITICAL: 0
- HIGH: 5 (2 platform design risk, 1 architecture unreachable, 2 Rust)
- MEDIUM: 27
- LOW: 28
- INFO: 12+

**Positive Assessment**: The seLe4n codebase demonstrates exceptional formal
verification discipline. Zero sorry/axiom across 159 Lean files (~90,000 lines).
35-operation NI coverage with compile-time surjectivity. Comprehensive invariant
preservation proofs across all subsystems. The Lean–Rust ABI alignment is exact.
The findings above are predominantly about modules not yet wired into production
(hardware binding gap) and proof precision gaps (externalized hypotheses), not
about fundamental soundness issues in the verified core.
