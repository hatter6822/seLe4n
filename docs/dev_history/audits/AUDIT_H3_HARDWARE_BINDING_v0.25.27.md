# AUDIT: H3 Hardware Binding Readiness — seLe4n v0.25.27

**Auditor**: Claude (Opus 4.6)
**Date**: 2026-04-08
**Scope**: Full codebase audit — every Lean kernel module + Rust ABI layer
**Purpose**: Pre-H3 hardware binding readiness assessment for Raspberry Pi 5 (BCM2712/ARM64)
**Branch**: `claude/audit-lean-rust-kernel-RT1E4`

---

## Executive Summary

The seLe4n codebase at v0.25.27 is in strong shape for beginning the H3 hardware
binding phase. **Zero sorry/axiom instances** exist in the production proof
surface. All 25 syscalls are fully dispatched with proven invariant preservation.
The formal model is architecturally sound, with clear separation between platform-
specific and platform-agnostic concerns.

This audit identifies **47 specific tasks** required for a complete Raspberry Pi 5
hardware binding, organized into 7 priority tiers. Critical path items center on:
(1) ARM64 exception handling and trap entry, (2) ARMv8 page table walk, (3)
GIC-400 interrupt controller driver, (4) production AdapterProofHooks, and (5)
Rust ABI kernel-side FFI bridge.

**Overall Assessment**: READY TO BEGIN H3 with the workstream plan below.

---

## Table of Contents

1. [Codebase Metrics](#1-codebase-metrics)
2. [Per-Subsystem Audit Summary](#2-per-subsystem-audit-summary)
3. [Rust ABI Layer Audit](#3-rust-abi-layer-audit)
4. [Platform/RPi5 Readiness Assessment](#4-platformrpi5-readiness-assessment)
5. [Deferred H3 Work Inventory](#5-deferred-h3-work-inventory)
6. [Critical Findings](#6-critical-findings)
7. [Security Analysis for Hardware](#7-security-analysis-for-hardware)
8. [Performance Considerations](#8-performance-considerations)
9. [H3 Workstream Task List](#9-h3-workstream-task-list)
10. [Risk Assessment](#10-risk-assessment)

---

## 1. Codebase Metrics

### Lean Kernel (Production)

| Metric | Value |
|--------|-------|
| Total .lean files | ~120+ |
| Sorry count | **0** |
| Axiom count | **0** |
| Syscall coverage | 25/25 (100%) |
| Cross-subsystem bridge lemmas | 33/33 operations covered |
| Cross-subsystem invariant predicates | 10 |
| Invariant preservation theorems | 60+ per-operation |
| Scheduler invariant bundle | 11-predicate composition |
| IPC invariant bundle | 14-predicate composition |
| Capability invariant bundle | 6+1 optional component |
| VSpace invariant bundle | 7-predicate composition |
| Information flow NI proofs | Per-operation + trace composition |

### Rust ABI Layer

| Metric | Value |
|--------|-------|
| Crates | 3 (sele4n-types, sele4n-abi, sele4n-sys) |
| Total .rs files | 30 |
| Unsafe blocks | **1** (svc #0 trap only) |
| `#![deny(unsafe_code)]` | All 3 crates |
| `#![no_std]` | All 3 crates |
| KernelError variants | 44 + 1 sentinel (0-43 + 255) |
| SyscallId variants | 25 |
| Typed identifiers | 14 newtype wrappers |
| Conformance tests | sele4n-abi/tests/conformance.rs |
| IpcBuffer layout assertions | Compile-time (960 bytes, 8-byte align) |

---

## 2. Per-Subsystem Audit Summary

### 2.1 Model/Prelude (SeLe4n/Prelude.lean, Machine.lean, Model/*)

**Status**: Complete, production-ready

- **14 typed identifiers**: ObjId, ThreadId, CPtr, Slot, DomainId, Priority,
  Deadline, Irq, ServiceId, InterfaceId, Badge, ASID, VAddr, PAddr
- **MachineState**: 64-bit register file (32 GPRs), timer, memory HashMap
- **MachineConfig**: registerWidth, virtualAddressWidth, physicalAddressWidth,
  pageSize, maxASID, memoryMap
- **KernelObject**: 7 variants (TCB, CNode, Endpoint, Notification, VSpaceRoot,
  Untyped, SchedContext)
- **SystemState**: objects (RHTable), scheduler, lifecycle, serviceRegistry,
  irqHandlers, machine, cdt, asidTable
- **Builder pattern**: IntermediateState with invariant witnesses for safe construction
- **FrozenState**: Immutable snapshot for two-phase architecture (experimental)

**H3 Gaps**:
- RegisterFile models 32 GPRs but not NEON/SVE (v0-v31), system registers
  (ELR_EL1, ESR_EL1, SPSR_EL1), or PSTATE flags
- MachineState.memory is HashMap-backed; real hardware uses physical memory
- No cache state model (D-cache, I-cache, TLB as separate coherence domain)
- Timer is abstract Nat; needs binding to CNTPCT_EL0 counter

### 2.2 Scheduler (SeLe4n/Kernel/Scheduler/*)

**Status**: Complete, production-ready. ~8,500 lines across 20 files.

**Key Properties Proven**:
- EDF selection correctness with CBS budget integration
- Priority inheritance protocol (PIP): blocking graph acyclicity, bounded depth,
  deterministic priority computation, frame lemmas across all subsystems
- WCRT bound: `WCRT = D * L_max + N * (B + P)` with PIP enhancement
- Liveness: timer-tick budget monotonicity, replenishment bounds, yield semantics,
  band exhaustion analysis, domain rotation bounds

**H3 Gaps**:
- Timer tick driven by abstract `timerTick` call; needs binding to ARM Generic
  Timer interrupt (INTID 30) via GIC-400
- `handleYield` gap documented (S-03): yield from only ready thread leaves empty
  run queue — correct per seL4 semantics but needs hardware-level test
- Domain scheduling fallback documented (AF-10/AF-11); hardware timer precision
  may affect domain schedule accuracy
- Run queue uses RHTable (hash-based); cache performance on Cortex-A76 untested
- No multi-core scheduling model (single-core only for initial H3)

### 2.3 IPC (SeLe4n/Kernel/IPC/*)

**Status**: Complete, production-ready. ~19,000 lines across 20 files.

**Key Properties Proven**:
- 14-predicate IPC invariant bundle with full preservation
- Intrusive dual-queue correctness (push/pop/remove O(1))
- Capability transfer with Grant-right gating
- Timeout-driven unblocking (Z6)
- SchedContext donation (Z7) with acyclicity

**H3 Gaps**:
- Badge overflow: `Badge.bor` uses unbounded Nat in Lean; Rust ABI masks to u64
  — verified equivalent but hardware behavior depends on register width
- IPC buffer layout: `receiverSlotBase` defaults to slot 0; per-slot targeting
  pending IPC buffer memory layout definition in VSpace
- Timeout sentinel (AF5-B): uses composite check `gpr x0 = 0xFFFFFFFF ∧ ipcState = .ready`;
  migration to explicit `timedOut: Bool` TCB field deferred to H3
- Atomicity of 2-step `donateSchedContext` relies on interrupts-disabled —
  not formally modeled in proof

### 2.4 Capability (SeLe4n/Kernel/Capability/*)

**Status**: Complete, production-ready. 5,418 lines, zero sorry/axiom.

**Key Properties Proven**:
- 6+1 component invariant bundle with all preservation theorems
- CDT completeness, acyclicity, mint-tracking
- Authority reduction (delete, revoke local/global)
- Capability forgery prevention via guard bits
- Rights escalation prevention via attenuation

**H3 Gaps**:
- CPtr masking to 64-bit (AE4-A/U-17) proven but hardware register interaction
  needs validation on real ARM64
- CDT acyclicity for `addEdge` assumed via fresh-node argument — not proven
  for arbitrary CDT state (safe because fresh IDs guaranteed unique)

### 2.5 Information Flow (SeLe4n/Kernel/InformationFlow/*)

**Status**: Complete, production-ready. ~7,500 lines across 7 files.

**Key Properties Proven**:
- Per-operation non-interference for all 25 syscalls
- Trace-level NI composition
- Declassification model with controlled downgrading
- Policy completeness over enforcement boundary

**H3 Gaps**:
- Covert channel analysis not modeled: timing channels, cache channels,
  speculative execution channels (Spectre/Meltdown)
- `LabelingContextValid` is a deployment requirement, not kernel-enforced —
  deployment-time validation needed for RPi5
- No hardware side-channel mitigation (KPTI, CSV2) in model

### 2.6 Architecture (SeLe4n/Kernel/Architecture/*)

**Status**: Complete model layer; H3 integration pending. ~4,100 lines.

**Key Properties Proven**:
- VSpace 7-predicate invariant bundle with full preservation
- W^X enforcement on all mapping operations
- TLB consistency model with full/targeted flush theorems
- Register decode round-trip for all 25 syscalls
- IPC buffer 6-step validation pipeline

**H3 Gaps** (CRITICAL — largest H3 work area):
- VSpace uses HashMap; needs ARMv8 hierarchical page table backend
- TLB targeted flush theorems exist but NOT wired into production paths
- No ISB/DMB/DSB instruction model for real memory barriers
- No exception level (EL0/EL1/EL2) model
- No ASID generation/rollover handling
- VSpaceBackend typeclass stub — hashMapVSpaceBackend incomplete
- Physical address width platform-specific validation exists but must be
  enforced at every API dispatch path

### 2.7 SchedContext (SeLe4n/Kernel/SchedContext/*)

**Status**: Complete, production-ready. ~3,400 lines across 10 files.

**Key Properties Proven**:
- CBS budget operations (consume, replenish, admission control)
- Replenishment queue sorted insert, popDue, remove
- Per-operation invariant preservation (Z5)
- Priority management with MCP authority validation

**H3 Gaps**:
- CBS budget enforcement depends on timer tick granularity — RPi5 54 MHz
  crystal gives ~18.5 ns resolution; sufficient but needs empirical validation
- Replenishment queue uses linear insert (O(n)); for large queue sizes on
  real hardware, may need optimization
- `schedContextYieldTo` is kernel-internal only (AF-30/AF-47) — no user-facing
  syscall, by design

### 2.8 RobinHood / RadixTree (SeLe4n/Kernel/RobinHood/*, RadixTree/*)

**Status**: Complete, production-ready. ~8,000+ lines combined.

**Key Properties Proven**:
- RobinHood: WF, distCorrect, noDupKeys, PCD preservation for all ops
- RobinHood: Functional correctness (get after insert/erase)
- RadixTree: 24 correctness proofs, O(1) operations
- Bridge: RHTable → CNodeRadix conversion, freeze

**H3 Gaps**:
- RHTable minimum capacity enforcement (4 ≤ capacity, AE2-A) — verified
- Cache line behavior of Robin Hood probing on Cortex-A76 L1/L2 untested
- RadixTree flat array may cause TLB pressure for large CNodes

### 2.9 Lifecycle / Service (SeLe4n/Kernel/Lifecycle/*, Service/*)

**Status**: Complete, production-ready.

- Lifecycle: suspend/resume, retype, with invariant preservation
- Service: registry with endpoint uniqueness, dependency acyclicity

**H3 Gaps**: Minimal — lifecycle and service are platform-agnostic.

### 2.10 CrossSubsystem / API (SeLe4n/Kernel/CrossSubsystem.lean, API.lean)

**Status**: Complete, production-ready. ~4,200 lines combined.

- 10-predicate cross-subsystem invariant with 33 operation bridges
- 25-syscall dispatch with capability gating
- Master NI theorem (AE1-G3) for checked dispatch

**H3 Gaps**:
- Syscall entry/exit trap handler not implemented (model only)
- No IRQ dispatch integration in API layer
- FrozenOps (24 operations) experimental — zero production consumers

### 2.11 FrozenOps (SeLe4n/Kernel/FrozenOps/*)

**Status**: Experimental, not in production chain. 1,734 lines.

- 24 frozen subsystem operations with roundtrip proofs
- Intended as runtime monad for H3 hardware binding

**H3 Decision Required**: Integrate FrozenOps into production chain or defer.


---

## 3. Rust ABI Layer Audit

### 3.1 Architecture (3 crates, 30 files)

```
rust/
├── Cargo.toml              (workspace: resolver "2", version 0.25.6)
├── sele4n-types/           (zero-dep, no_std, deny(unsafe_code))
│   └── src/
│       ├── lib.rs          — Re-exports
│       ├── identifiers.rs  — 14 newtype wrappers (#[repr(transparent)] over u64)
│       ├── error.rs        — 45-variant KernelError (#[repr(u32)], #[non_exhaustive])
│       ├── rights.rs       — AccessRight (5 variants) + AccessRights (bitmask)
│       └── syscall.rs      — 25-variant SyscallId (#[repr(u64)])
├── sele4n-abi/             (depends on sele4n-types, no_std, deny(unsafe_code))
│   └── src/
│       ├── lib.rs          — Re-exports
│       ├── encode.rs       — SyscallRequest → [u64; 7] register packing
│       ├── decode.rs       — [u64; 7] → SyscallResponse unpacking
│       ├── trap.rs         — raw_syscall (svc #0) — ONLY unsafe block
│       ├── message_info.rs — MessageInfo bitfield (20-bit label, 6-bit length, etc.)
│       ├── ipc_buffer.rs   — IpcBuffer (960 bytes, #[repr(C)], compile-time asserts)
│       ├── registers.rs    — RegisterFile (bounds-checked [u64; 7] wrapper)
│       └── args/           — Per-syscall typed argument encode/decode
│           ├── cspace.rs, vspace.rs, lifecycle.rs, service.rs
│           ├── tcb.rs, sched_context.rs, page_perms.rs, type_tag.rs
│           └── mod.rs
└── sele4n-sys/             (high-level safe wrappers)
    └── src/
        ├── lib.rs, cap.rs, cspace.rs, vspace.rs
        ├── lifecycle.rs, service.rs, tcb.rs, ipc.rs
```

### 3.2 Safety Assessment

**Unsafe Audit**: Exactly ONE `unsafe` block in the entire Rust codebase:

```rust
// rust/sele4n-abi/src/trap.rs:40-52
core::arch::asm!(
    "svc #0",
    inout("x0") regs[0],
    inout("x1") regs[1],
    inout("x2") regs[2],
    inout("x3") regs[3],
    inout("x4") regs[4],
    inout("x5") regs[5],
    in("x7") regs[6],
    lateout("x6") _,
    clobber_abi("C"),
    options(nostack),
);
```

**Assessment**: Sound. The `clobber_abi("C")` correctly declares all AAPCS64
caller-saved registers as potentially modified. The `options(nostack)` is correct
since `svc #0` does not modify the user-space stack pointer. The `lateout("x6")`
discards x6 which may be clobbered by the kernel.

**FINDING-RUST-01** (LOW): Mock `raw_syscall` for non-AArch64 targets returns
`InvalidSyscallNumber` error code directly in `regs[0]` as `u64`. This is
correct for testing but should be documented as not matching the exact kernel ABI
(which uses `u32` error codes in the low 32 bits of x0).

### 3.3 ABI Compatibility Verification

| Lean Model | Rust ABI | Match? | Notes |
|------------|----------|--------|-------|
| KernelError (44 variants) | KernelError (44 + sentinel) | ✓ | Discriminants 0-43 match; 255 = UnknownKernelError |
| SyscallId (25 variants) | SyscallId (25 variants) | ✓ | repr(u64), discriminants 0-24 |
| AccessRight (5 variants) | AccessRight (5 variants) | ✓ | Bit positions 0-4 |
| AccessRightSet (bitmask) | AccessRights (bitmask) | ✓ | TryFrom<u8> rejects bits 5-7 |
| ObjId, ThreadId, etc. | 14 newtype wrappers | ✓ | repr(transparent) over u64 |
| MessageInfo (bitfield) | MessageInfo (bitfield) | ✓ | 20-bit label, 6-bit length, extra caps |
| RegisterFile (32 GPRs) | RegisterFile (7 ABI regs) | ⚠ | Lean: full 32-GPR context; Rust: 7-register syscall ABI |
| IPC buffer (120 msg regs) | IpcBuffer (116 overflow) | ✓ | 4 inline + 116 overflow = 120 total |

**FINDING-RUST-02** (MEDIUM): The Rust `RegisterFile` in `registers.rs` wraps 7
registers (the syscall ABI window: x0-x5, x7), while the Lean `RegisterFile` in
`Machine.lean` is the full 32-GPR ARM64 context. This is correct (different
abstraction levels) but the H3 kernel-side trap handler must bridge these two
representations — loading the 7 ABI registers from the full 32-register saved
context and writing results back.

### 3.4 H3 Rust Work Required

**FINDING-RUST-03** (HIGH): No kernel-side Rust code exists. The entire Rust
layer is user-space facing (`svc #0` trap entry). For H3, the kernel must:

1. **Exception vector table** (Rust + assembly): EL1 vector table for
   synchronous exceptions (SVC), IRQ, FIQ, SError
2. **Trap entry/exit** (assembly): Save full register context to kernel stack,
   extract syscall parameters, call Lean kernel dispatch
3. **Lean-Rust FFI bridge**: `extern "C"` functions callable from Lean compiled
   code for hardware operations (MMIO, TLB flush, cache ops)
4. **Interrupt handler**: GIC-400 acknowledge + dispatch to kernel IRQ handler
5. **Timer driver**: ARM Generic Timer configuration (CNTV_CTL_EL0, CNTV_CVAL_EL0)
6. **Boot sequence**: ATF → U-Boot → kernel entry in Rust, then handoff to Lean

**FINDING-RUST-04** (MEDIUM): Workspace version is 0.25.6 while Lean project is
at 0.25.27. Version should be synchronized.

---

## 4. Platform/RPi5 Readiness Assessment

### 4.1 What's Implemented

| Component | File | Status | Lines |
|-----------|------|--------|-------|
| Board constants | Board.lean | **Complete** | 333 |
| Memory map | Board.lean | **Complete** (1/2/4/8 GB) | — |
| MMIO regions | Board.lean | **Complete** (3 regions) | — |
| GIC-400 IRQ constants | Board.lean | **Complete** | — |
| Machine config | Board.lean | **Complete** | — |
| Runtime contract | RuntimeContract.lean | **Complete** | 183 |
| Boot contract | BootContract.lean | **Complete** | 98 |
| Interrupt contract | BootContract.lean | **Complete** | — |
| MMIO adapter | MmioAdapter.lean | **Complete** (model) | 400+ |
| Proof hooks | ProofHooks.lean | **Restrictive only** | 115 |
| Platform binding | Contract.lean | **Complete** (struct) | 58 |
| Device tree | Board.lean | **Static path only** | — |

### 4.2 What's Missing for H3

**FINDING-PLAT-01** (HIGH): All board constants have been validated against
BCM2712 documentation (S5-F/S6-G checklist — all 14 entries marked "Validated").
This is excellent. However, the validation was against publicly available docs
which may be incomplete. Live hardware cross-check required during H3.

**FINDING-PLAT-02** (HIGH): `AdapterProofHooks` only instantiated for the
**restrictive** contract (`rpi5RuntimeContractRestrictive`), which denies ALL
register writes and context switches (vacuously satisfying proofs). The production
contract (`rpi5RuntimeContract`) has no proof hooks — this is the single largest
proof gap for H3.

**FINDING-PLAT-03** (HIGH): MMIO adapter is model-only. Operations defined with
barrier annotations (DMB/DSB/ISB) but no actual hardware execution. The
`MmioReadOutcome` type correctly models volatile vs idempotent semantics, which
is excellent formal groundwork.

**FINDING-PLAT-04** (MEDIUM): Device tree is static path only
(`fromBoardConstants`). Runtime DTB parsing exists (`parseFdtNodes` in
DeviceTree.lean) but uses fuel-bounded traversal. For RPi5, the static path is
sufficient since BCM2712 addresses are fixed; runtime DTB parsing is a nice-to-
have for future board revisions.

**FINDING-PLAT-05** (MEDIUM): Boot sequence (`Platform/Boot.lean`) constructs
`IntermediateState` from `PlatformConfig` but is model-level only. Real boot
requires:
- ATF/U-Boot handoff protocol
- MMU initialization (identity map → kernel map transition)
- Stack setup for EL1
- BSS zeroing verification
- Device tree blob (DTB) location from bootloader

---

## 5. Deferred H3 Work Inventory

Every deferred H3 item found in the codebase, organized by subsystem:

### 5.1 Architecture / VSpace

| ID | Description | Location | Priority |
|----|-------------|----------|----------|
| H3-ARCH-01 | ARMv8 hierarchical page table walk | VSpaceBackend.lean | **CRITICAL** |
| H3-ARCH-02 | Targeted TLB flush integration | VSpace.lean, TlbModel.lean | HIGH |
| H3-ARCH-03 | ISB after TLBI instruction | TlbModel.lean | HIGH |
| H3-ARCH-04 | ASID generation and rollover handling | VSpace.lean | HIGH |
| H3-ARCH-05 | Exception level model (EL0/EL1) | Assumptions.lean | MEDIUM |
| H3-ARCH-06 | System register model (ELR, ESR, SPSR) | Machine.lean | MEDIUM |
| H3-ARCH-07 | Cache coherency model (D/I-cache) | NEW | MEDIUM |
| H3-ARCH-08 | Memory barrier semantics (DMB/DSB/ISB) | MmioAdapter.lean (model exists) | MEDIUM |
| H3-ARCH-09 | NEON/SVE register context save/restore | Machine.lean | LOW |
| H3-ARCH-10 | VSpaceBackend hashMap instance completion | VSpaceBackend.lean:141-145 | LOW |

### 5.2 Platform / RPi5

| ID | Description | Location | Priority |
|----|-------------|----------|----------|
| H3-PLAT-01 | Production AdapterProofHooks (non-restrictive) | ProofHooks.lean | **CRITICAL** |
| H3-PLAT-02 | GIC-400 interrupt controller driver | NEW | **CRITICAL** |
| H3-PLAT-03 | ARM Generic Timer driver (CNTPCT_EL0 binding) | NEW | **CRITICAL** |
| H3-PLAT-04 | Exception vector table (EL1) | NEW (Rust/asm) | **CRITICAL** |
| H3-PLAT-05 | MMU initialization (TTBR0/TTBR1 setup) | NEW | **CRITICAL** |
| H3-PLAT-06 | UART PL011 driver for debug console | NEW (Rust) | HIGH |
| H3-PLAT-07 | Live hardware constant cross-check | Board.lean | HIGH |
| H3-PLAT-08 | Boot sequence (ATF → U-Boot → kernel) | NEW (Rust/asm) | HIGH |
| H3-PLAT-09 | MMIO operation execution (model → hardware) | MmioAdapter.lean | HIGH |
| H3-PLAT-10 | Runtime DTB parsing for board detection | DeviceTree.lean | LOW |

### 5.3 Rust / FFI

| ID | Description | Location | Priority |
|----|-------------|----------|----------|
| H3-RUST-01 | Kernel-side exception vector table | NEW | **CRITICAL** |
| H3-RUST-02 | Trap entry/exit assembly (register save/restore) | NEW | **CRITICAL** |
| H3-RUST-03 | Lean-Rust FFI bridge for hardware ops | NEW | **CRITICAL** |
| H3-RUST-04 | GIC-400 interrupt acknowledge/dispatch | NEW | **CRITICAL** |
| H3-RUST-05 | TLB flush instruction wrappers (TLBI) | NEW | HIGH |
| H3-RUST-06 | Cache maintenance operations (DC CIVAC, IC IALLU) | NEW | HIGH |
| H3-RUST-07 | System register accessors (MRS/MSR) | NEW | HIGH |
| H3-RUST-08 | MMIO volatile read/write primitives | NEW | HIGH |
| H3-RUST-09 | Workspace version sync (0.25.6 → 0.25.27) | Cargo.toml | LOW |
| H3-RUST-10 | Kernel linker script for RPi5 | NEW | HIGH |

### 5.4 Scheduler / Real-Time

| ID | Description | Location | Priority |
|----|-------------|----------|----------|
| H3-SCHED-01 | Timer interrupt → timerTick binding | Scheduler/Core.lean | HIGH |
| H3-SCHED-02 | Interrupt-disabled regions for atomicity | API.lean | HIGH |
| H3-SCHED-03 | Run queue cache performance validation | RunQueue.lean | MEDIUM |
| H3-SCHED-04 | Domain schedule hardware timer precision | Scheduler/Core.lean | MEDIUM |
| H3-SCHED-05 | WCRT empirical validation on Cortex-A76 | Liveness/WCRT.lean | LOW |

### 5.5 IPC / Communication

| ID | Description | Location | Priority |
|----|-------------|----------|----------|
| H3-IPC-01 | Timeout sentinel → explicit TCB field migration | IPC/Operations/Timeout.lean | HIGH |
| H3-IPC-02 | IPC buffer memory layout in VSpace | IPC/ipc_buffer.rs ↔ Types.lean | HIGH |
| H3-IPC-03 | Badge overflow hardware behavior validation | IPC/Operations/Endpoint.lean | LOW |
| H3-IPC-04 | Atomicity of donation (interrupt-disabled proof) | IPC/Operations/Donation.lean | MEDIUM |

### 5.6 Proof / Formal Verification

| ID | Description | Location | Priority |
|----|-------------|----------|----------|
| H3-PROOF-01 | Production AdapterProofHooks for rpi5RuntimeContract | ProofHooks.lean | **CRITICAL** |
| H3-PROOF-02 | Targeted TLB flush composition theorems | TlbModel.lean | HIGH |
| H3-PROOF-03 | Donation chain k>2 cycle prevention formalization | IPC/Invariant/Structural.lean | MEDIUM |
| H3-PROOF-04 | collectQueueMembers fuel sufficiency formalization | CrossSubsystem.lean | LOW |
| H3-PROOF-05 | FrozenOps production integration decision | FrozenOps/ | MEDIUM |


---

## 6. Critical Findings

### FINDING-01 (CRITICAL): No Kernel-Side Hardware Abstraction Layer

The entire seLe4n kernel is a pure Lean 4 model. There is no kernel-side code
that executes hardware instructions. The Rust crate is exclusively user-space
(syscall entry via `svc #0`). H3 must create the entire kernel-side HAL:

- Exception vector table (ARM64 EL1 vectors)
- Register save/restore (full 32-GPR + system register context)
- Hardware instruction wrappers (TLBI, DC, IC, DMB, DSB, ISB, MRS, MSR)
- GIC-400 register access (GICD, GICC)
- ARM Generic Timer configuration

**Recommendation**: Create a new `rust/sele4n-hal/` crate with `#![no_std]` and
carefully scoped `unsafe` blocks for each hardware instruction. Maintain the
single-unsafe-block-per-operation discipline. All unsafe blocks must have safety
comments referencing the ARM Architecture Reference Manual section.

### FINDING-02 (CRITICAL): Restrictive-Only Proof Hooks

`rpi5RestrictiveAdapterProofHooks` denies register writes and context switches,
making all proofs vacuously true for those paths. The production contract
(`rpi5RuntimeContract`) with substantive `registerContextStablePred` has NO
proof hooks.

**Impact**: On real hardware, context switches ARE register writes. The kernel
cannot prove invariant preservation through context switches until production
proof hooks exist.

**Recommendation**: Implement `rpi5ProductionAdapterProofHooks` by:
1. Proving that `adapterContextSwitch` (X1-F atomic operation) preserves
   `registerContextStablePred` when the new register file matches the new
   thread's saved context
2. Leveraging `contextSwitchState_preserves_contextMatchesCurrent` (already
   proven in Adapter.lean)
3. Individual register writes remain denied (context switches use atomic path)

### FINDING-03 (CRITICAL): VSpace is HashMap-Only

The VSpace implementation uses `HashMap VAddr (PAddr × PagePermissions)` for
page table modeling. ARM64 uses a 4-level hierarchical page table (L0-L3) with
specific descriptor formats. H3 must:

1. Implement `VSpaceBackend` typeclass for ARMv8 page tables
2. Prove that the ARMv8 backend satisfies all VSpace invariants
3. Implement TTBR0/TTBR1 setup for kernel/user split
4. Add page table walk logic with proper descriptor parsing

**Recommendation**: Keep HashMap model as the specification and prove ARMv8
implementation refines it. This preserves all existing proofs while adding
hardware-specific implementation.

### FINDING-04 (HIGH): No Exception Handling Model

The model has no concept of exceptions (synchronous or asynchronous). ARM64
defines 4 exception types (Synchronous, IRQ, FIQ, SError) × 4 exception levels
× 4 execution states = 16 vector entries. The model's `syscallEntry` is a pure
function call, not a trap handler.

**Recommendation**: Create `SeLe4n/Kernel/Architecture/ExceptionModel.lean` with:
- `ExceptionType` inductive (Synchronous, IRQ, FIQ, SError)
- `ExceptionContext` structure (ESR_EL1, ELR_EL1, SPSR_EL1, FAR_EL1)
- Exception dispatch function mapping exception type to kernel handler
- Prove exception dispatch preserves invariants

### FINDING-05 (HIGH): No Multi-Core Model

The scheduler operates on a single core. RPi5 has 4 Cortex-A76 cores. While
single-core operation is valid for initial H3, the model should document this
limitation and plan for SMP:

- Per-core run queues
- IPI (inter-processor interrupt) for cross-core scheduling
- Spinlock / ticket lock for shared kernel state
- Cache coherency protocol (MOESI on Cortex-A76)

**Recommendation**: Document single-core limitation in H3. Plan SMP as WS-V
follow-on work.

### FINDING-06 (HIGH): Interrupt Handling Gap

The model defines `rpi5InterruptContract` with IRQ line support (INTIDs 0-223)
and handler mapping requirements. However, there is no interrupt dispatch path
in the kernel:

- No `handleInterrupt` operation in API.lean
- No GIC-400 acknowledge sequence (read GICC_IAR → dispatch → write GICC_EOIR)
- No interrupt priority management
- No interrupt masking model (DAIF flags in PSTATE)

**Recommendation**: Add `handleInterrupt` to API.lean syscall dispatch, with
GIC-400 acknowledge/end-of-interrupt sequence.

### FINDING-07 (MEDIUM): IPC Buffer Alignment Mismatch

Lean model: IPC buffer aligned to 512 bytes (`ipcBufferAlignment = 512`).
Rust ABI: `IpcBuffer` is 960 bytes, `#[repr(C)]`, 8-byte aligned.
ARM64: Cache line is 64 bytes on Cortex-A76.

The Lean alignment check (`addr % 512 = 0`) ensures the buffer doesn't cross a
page boundary (proven in `ipcBuffer_within_page`). On hardware, 512-byte
alignment also provides good cache behavior (8 cache lines). This is correct
but should be documented as a performance decision.

### FINDING-08 (MEDIUM): Timer Model Abstraction Gap

The Lean timer is an abstract `Nat` incremented by `timerTick`. ARM64 uses:
- `CNTPCT_EL0`: Physical counter (54 MHz, read-only)
- `CNTP_CVAL_EL0`: Physical timer comparator (generates IRQ when counter ≥ value)
- `CNTP_CTL_EL0`: Physical timer control (enable, mask, status)

The mapping from abstract `timerTick` to real timer interrupts needs:
1. Configure comparator for desired tick rate
2. On timer IRQ: acknowledge, call `timerTick`, reprogram comparator
3. Prove timer monotonicity from hardware counter monotonicity

---

## 7. Security Analysis for Hardware

### 7.1 Privilege Separation

**Current Model**: No distinction between EL0 (user) and EL1 (kernel). All code
runs at the same privilege level in the model.

**Hardware Reality**: ARM64 enforces EL0/EL1 separation via:
- Page table AP (Access Permission) bits
- PXN/UXN (Privileged/Unprivileged Execute Never) bits
- System register access controls (EL0 cannot write TTBR, SCTLR, etc.)

**H3 Requirement**: Model must ensure:
- User-space code cannot access kernel memory (page table AP configuration)
- User-space code cannot execute kernel pages (UXN set on kernel mappings)
- Kernel cannot execute user-space pages (PXN set on user mappings)
- W^X enforcement extends to AP/UXN/PXN bits (currently W^X only checks
  `PagePermissions.wxCompliant`)

### 7.2 Speculative Execution Mitigations

Cortex-A76 is susceptible to:
- **Spectre v1** (bounds check bypass): Mitigated by speculation barriers (CSDB)
  after bounds checks. Relevant for capability resolution and array access.
- **Spectre v2** (branch target injection): Mitigated by CSV2 (if available) or
  retpoline. Relevant for indirect branches in dispatch tables.
- **Meltdown**: Cortex-A76 is NOT susceptible (ARMv8.2-A with CSV3). KPTI not
  required.

**H3 Requirement**: Add speculation barriers after:
- `resolveCapAddress` bounds checks (capability address masking)
- Run queue array indexing (priority-based selection)
- VSpace page table walk (level extraction)

### 7.3 Memory Tagging (MTE)

Cortex-A76 does NOT support MTE (Memory Tagging Extension — ARMv8.5-A). MTE is
not applicable for RPi5 H3. Future targets with ARMv8.5+ should consider MTE
integration.

### 7.4 Pointer Authentication (PAC)

Cortex-A76 supports PAC (ARMv8.3-A). H3 could use PAC for:
- Return address protection on kernel stack
- Function pointer integrity in dispatch tables

**Recommendation**: Defer PAC to post-H3 hardening phase. Document as security
enhancement opportunity.

### 7.5 Branch Target Identification (BTI)

Cortex-A76 supports BTI (ARMv8.5-A). H3 could use BTI for control-flow
integrity on indirect branches.

**Recommendation**: Enable BTI in linker flags and add `bti c` landing pads to
all indirect branch targets. Low effort, high value.

---

## 8. Performance Considerations

### 8.1 IPC Fast Path

seL4's key performance metric is IPC latency. The seLe4n model currently has no
fast path — every IPC goes through the full capability resolution, dispatch, and
invariant checking path.

**H3 Consideration**: For initial bring-up, the full path is correct and
sufficient. Performance optimization (fast path bypass for common Send/Receive
patterns) should be deferred to post-H3.

### 8.2 TLB Management

The model uses full TLB flush (`adapterFlushTlb`) for all VSpace operations.
Targeted flush theorems exist but are not wired in.

**H3 Impact**: Full TLB flush on every map/unmap is O(TLB size) and invalidates
entries for ALL address spaces. On Cortex-A76 with a 1024-entry TLB, this is
expensive during rapid VSpace operations.

**Recommendation**: Wire targeted flush (per-ASID, per-VAddr) in H3 phase 2
after basic bring-up. The theorems already exist — integration is primarily
engineering work.

### 8.3 RobinHood Hash Table Cache Behavior

RobinHood probing has good average-case performance but potentially poor cache
behavior due to linear probing across cache lines. Cortex-A76 has:
- L1 data cache: 64 KB, 4-way, 64-byte lines
- L2 cache: 512 KB (per-core), 8-way
- L3 cache: 2 MB (shared), 16-way

**H3 Consideration**: Profile RHTable operations on RPi5 hardware. If probe
chains regularly exceed 4-5 entries (crossing cache lines), consider:
- Increasing table capacity to reduce load factor
- Caching hot entries (object store, scheduler state)

### 8.4 Scheduler Latency

The proven WCRT bound is `D * L_max + N * (B + P)`. On RPi5:
- D (domains): Typically 1-16
- L_max (max domain length): Implementation-specific
- N (threads per priority band): Bounded by maxObjects
- B (max blocking time): PIP-bounded
- P (preemption bound): Timer tick granularity

**H3 Consideration**: Empirically measure scheduling latency on RPi5 to validate
the WCRT bound. This requires the timer driver and interrupt handler.

---

## 9. H3 Workstream Task List

### Phase H3-1: Foundation (Boot + Exception Handling)

| Task | ID | Priority | Est. Complexity |
|------|----|----------|-----------------|
| Create `rust/sele4n-hal/` crate for kernel-side HAL | H3-RUST-01 | CRITICAL | Medium |
| Implement ARM64 exception vector table (EL1) | H3-PLAT-04 | CRITICAL | High |
| Implement trap entry/exit assembly (register save/restore) | H3-RUST-02 | CRITICAL | High |
| Implement kernel linker script for RPi5 | H3-RUST-10 | HIGH | Medium |
| Implement boot sequence (ATF → U-Boot → kernel entry) | H3-PLAT-08 | HIGH | High |
| MMU initialization (TTBR0/TTBR1, identity map → kernel map) | H3-PLAT-05 | CRITICAL | High |
| UART PL011 driver for debug console | H3-PLAT-06 | HIGH | Low |
| Stack setup for EL1 | (part of boot) | CRITICAL | Low |

### Phase H3-2: Interrupts + Timer

| Task | ID | Priority | Est. Complexity |
|------|----|----------|-----------------|
| GIC-400 distributor initialization | H3-PLAT-02 | CRITICAL | Medium |
| GIC-400 CPU interface initialization | H3-PLAT-02 | CRITICAL | Medium |
| GIC-400 IRQ acknowledge/dispatch/EOI | H3-RUST-04 | CRITICAL | Medium |
| ARM Generic Timer driver (CNTPCT_EL0/CNTP_CVAL_EL0) | H3-PLAT-03 | CRITICAL | Medium |
| Timer interrupt → timerTick binding | H3-SCHED-01 | HIGH | Medium |
| handleInterrupt API integration | FINDING-06 | HIGH | Medium |
| Interrupt-disabled region enforcement | H3-SCHED-02 | HIGH | Medium |

### Phase H3-3: Memory Management

| Task | ID | Priority | Est. Complexity |
|------|----|----------|-----------------|
| ARMv8 page table descriptor format | H3-ARCH-01 | CRITICAL | High |
| 4-level page table walk implementation | H3-ARCH-01 | CRITICAL | High |
| VSpaceBackend ARMv8 instance | H3-ARCH-10 | CRITICAL | High |
| TTBR0/TTBR1 switching for process isolation | (part of MMU) | CRITICAL | Medium |
| TLB flush instruction wrappers (TLBI) | H3-RUST-05 | HIGH | Low |
| Targeted TLB flush integration | H3-ARCH-02 | HIGH | Medium |
| ISB after TLBI | H3-ARCH-03 | HIGH | Low |
| ASID generation and management | H3-ARCH-04 | HIGH | Medium |
| Cache maintenance operations | H3-RUST-06 | HIGH | Medium |

### Phase H3-4: Lean-Rust FFI Bridge

| Task | ID | Priority | Est. Complexity |
|------|----|----------|-----------------|
| Lean → Rust FFI for hardware ops (MMIO, TLB, timer) | H3-RUST-03 | CRITICAL | High |
| Lean → Rust FFI for syscall dispatch result | H3-RUST-03 | CRITICAL | High |
| System register accessors (MRS/MSR) | H3-RUST-07 | HIGH | Low |
| MMIO volatile read/write primitives | H3-RUST-08 | HIGH | Low |
| Production AdapterProofHooks | H3-PROOF-01 | CRITICAL | High |

### Phase H3-5: Integration + Proof Closure

| Task | ID | Priority | Est. Complexity |
|------|----|----------|-----------------|
| Timeout sentinel → explicit TCB field | H3-IPC-01 | HIGH | Medium |
| Exception context model (ESR_EL1, ELR_EL1) | H3-ARCH-06 | MEDIUM | Medium |
| Exception level model (EL0/EL1) | H3-ARCH-05 | MEDIUM | Medium |
| Targeted flush composition theorems | H3-PROOF-02 | HIGH | Medium |
| FrozenOps production integration decision | H3-PROOF-05 | MEDIUM | Low |
| Live hardware constant cross-check | H3-PLAT-07 | HIGH | Low |

### Phase H3-6: Testing + Validation

| Task | ID | Priority | Est. Complexity |
|------|----|----------|-----------------|
| Run queue cache performance profiling | H3-SCHED-03 | MEDIUM | Medium |
| WCRT empirical validation | H3-SCHED-05 | LOW | Medium |
| IPC latency measurement | (new) | MEDIUM | Medium |
| Full test suite on RPi5 hardware | (new) | HIGH | High |
| Security hardening (BTI, speculation barriers) | Sec §7.2, §7.5 | LOW | Medium |
| Rust workspace version sync | H3-RUST-09 | LOW | Trivial |

### Phase H3-7: Documentation + Closure

| Task | ID | Priority | Est. Complexity |
|------|----|----------|-----------------|
| H3 workstream plan (formal) | (new) | HIGH | Low |
| Architecture assumptions update for ARM64 | H3-ARCH-05 | MEDIUM | Low |
| Memory barrier documentation | H3-ARCH-08 | MEDIUM | Low |
| Multi-core limitation documentation | FINDING-05 | LOW | Low |
| SELE4N_SPEC.md update for hardware binding | (doc) | HIGH | Medium |

---

## 10. Risk Assessment

### 10.1 Technical Risks

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Lean 4 compiled code performance on ARM64 | Medium | HIGH | Profile early; optimize critical paths in Rust if needed |
| Lean-Rust FFI complexity | Medium | HIGH | Prototype FFI bridge before full integration |
| ARMv8 page table proof complexity | Low | MEDIUM | Keep HashMap model as spec; prove refinement |
| GIC-400 timing sensitivity | Low | MEDIUM | Conservative IRQ acknowledge sequence |
| Cache coherency issues | Medium | MEDIUM | Use DSB/ISB barriers conservatively |
| Boot sequence fragility | Medium | HIGH | Test on QEMU emulation before hardware |

### 10.2 Process Risks

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| BCM2712 datasheet gaps | Medium | MEDIUM | Cross-reference with Linux kernel driver source |
| Lean 4 toolchain bugs on ARM64 | Low | HIGH | Test Lean compiler on ARM64 target early |
| Proof regression during H3 | Low | MEDIUM | Run `test_full.sh` on every change |

### 10.3 Recommended Approach

1. **Start with QEMU**: Use `qemu-system-aarch64 -machine raspi4b` (closest to
   RPi5) for initial development and testing. Move to real hardware only after
   basic boot + UART works in QEMU.

2. **Prototype FFI early**: The Lean-Rust FFI bridge is the highest-risk
   technical item. Build a minimal prototype (Lean calls Rust UART write) before
   committing to the full integration architecture.

3. **Keep model pure**: Do NOT modify existing Lean kernel proofs for H3. Add
   new modules for hardware abstraction. Existing proofs should remain valid.

4. **Single-core first**: Document and enforce single-core operation. SMP is a
   separate workstream.

5. **Iterative validation**: After each H3 phase, run `test_full.sh` to ensure
   no proof regression.

---

## Appendix A: Files Audited

Every file in the following directories was read and audited line-by-line:

- `SeLe4n/Prelude.lean`, `SeLe4n/Machine.lean`
- `SeLe4n/Model/` (all 8 files)
- `SeLe4n/Kernel/Architecture/` (all 10 files)
- `SeLe4n/Kernel/Scheduler/` (all 20 files)
- `SeLe4n/Kernel/IPC/` (all 20 files)
- `SeLe4n/Kernel/Capability/` (all 5 files)
- `SeLe4n/Kernel/InformationFlow/` (all 7 files)
- `SeLe4n/Kernel/SchedContext/` (all 10 files)
- `SeLe4n/Kernel/RobinHood/` (all 7 files)
- `SeLe4n/Kernel/RadixTree/` (all 3 files)
- `SeLe4n/Kernel/Lifecycle/` (all 3 files)
- `SeLe4n/Kernel/Service/` (all 7 files)
- `SeLe4n/Kernel/FrozenOps/` (all 4 files)
- `SeLe4n/Kernel/CrossSubsystem.lean`
- `SeLe4n/Kernel/API.lean`
- `SeLe4n/Platform/` (all 13 files)
- `SeLe4n/Testing/` (all 5 files)
- `rust/` (all 30 .rs files + 4 Cargo.toml)
- `Main.lean`
- `scripts/` (test scripts, setup, CI)

**Total**: ~120+ Lean files, 30 Rust files, 10+ shell scripts.

---

## Appendix B: Audit Methodology

1. **Automated scans**: `sorry`/`axiom` grep across all .lean files (result: 0)
2. **Per-file manual review**: Every file read in ≤500-line chunks, recording
   TODOs, FIXMEs, deferred work markers, H3 references, stubs, and placeholders
3. **Cross-reference validation**: Lean ↔ Rust ABI correspondence checked for
   all shared types (KernelError, SyscallId, AccessRight, identifiers, IpcBuffer)
4. **Security analysis**: OWASP-inspired review for capability forgery, privilege
   escalation, information leakage, and timing channels
5. **Hardware gap analysis**: Each module assessed against ARM Architecture
   Reference Manual (ARMv8-A) requirements for real execution
6. **Proof surface analysis**: All invariant bundles, preservation theorems, and
   cross-subsystem bridges cataloged and verified for completeness

---

*End of audit report.*
