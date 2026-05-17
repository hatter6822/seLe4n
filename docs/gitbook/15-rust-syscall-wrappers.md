# 15 — Rust Syscall Wrappers

## Overview

`libsele4n` is a `no_std` Rust userspace library providing safe, typed wrappers
around all 25 seLe4n syscalls. It mirrors the verified Lean ABI surface exactly,
enabling Rust userspace programs to invoke kernel operations with compile-time
type safety and zero `unsafe` code outside the syscall trap instruction.

## Crate Architecture

```
User-space crates:
  sele4n-sys           (safe high-level wrappers)
    └── sele4n-abi     (register encoding + svc trap)
          └── sele4n-types  (core types, no unsafe)

Kernel-side crate:
  sele4n-hal           (ARM64 HAL — boot, MMU, UART, trap, vectors)
```

### sele4n-types

Core type definitions with zero `unsafe` and zero external dependencies:

- **14 newtype identifiers**: `ObjId`, `ThreadId`, `CPtr`, `Slot`, `DomainId`,
  `Priority`, `Deadline`, `Irq`, `ServiceId`, `InterfaceId`, `Badge`, `Asid`,
  `VAddr`, `PAddr`, `RegValue` — inner fields are `pub(crate)` with `.raw()`
  accessors (R8-E/L-11 encapsulation)
- **`KernelError`**: 49-variant `#[non_exhaustive]` enum (1:1 with Lean
  `KernelError`; AG3: +VmFault, +UserException, +HardwareFault, +NotSupported, +InvalidIrq)
- **`AccessRight` / `AccessRights`**: 5-right bitmask (O(1) operations).
  `TryFrom<u8>` rejects invalid bytes with bits 5–7 set (U3-D)
- **`AccessRightsError`**: Error type for invalid `AccessRights` construction
- **`SyscallId`**: 25-variant enum (0–24), including notificationSignal, notificationWait, replyRecv (V2-A/D), schedContextConfigure/Bind/Unbind (AA1/Z5), tcbSuspend/Resume (D1), tcbSetPriority/SetMCPriority (D2), tcbSetIPCBuffer (D3)

### sele4n-abi

ARM64 register ABI layer with exactly one `unsafe` block:

- **`MessageInfo`**: Bitfield encode/decode (7-bit length, 2-bit extraCaps,
  20-bit label, seL4 convention). Fields are private (U3-B); construct via `new()` or `decode()`,
  access via `length()`, `extra_caps()`, `label()` accessors
- **`SyscallRequest` / `SyscallResponse`**: Register structures
- **`raw_syscall`**: Inline `svc #0` — the single `unsafe` function. Uses
  `clobber_abi("C")` to declare all caller-saved registers clobbered (U3-A)
- **`RegisterFile`**: Safe bounds-checked wrapper for the 7-element register
  array; `get()`/`set()` return `Option` (U3-G)
- **Per-syscall argument structures**: CSpace (4), Lifecycle (1), VSpace (2),
  Service (3), SchedContext (3: Configure, Bind, Unbind), TCB (5: Suspend, Resume,
  SetPriority, SetMCPriority, SetIPCBuffer)
- **`TypeTag`**: 7 retype variants (TCB=0, Endpoint=1, ..., Untyped=5, SchedContext=6)
- **`PagePerms`**: Permission bitmask with W^X enforcement
- **`IpcBuffer`**: Overflow message registers (4–119) for messages exceeding
  the 4 inline ARM64 registers. Compile-time layout assertions verify 960-byte
  `#[repr(C)]` size and 8-byte alignment (U3-I)

### sele4n-sys

Safe high-level wrappers for all 25 syscalls:

| Subsystem | Operations |
|-----------|-----------|
| IPC | `endpoint_send`, `endpoint_receive`, `endpoint_call`, `endpoint_reply`, `notification_signal`, `notification_wait`, `endpoint_reply_recv` |
| CSpace | `cspace_mint`, `cspace_copy`, `cspace_move`, `cspace_delete` |
| Lifecycle | `lifecycle_retype`, `retype_tcb`, `retype_endpoint`, `retype_notification`, `retype_cnode`, `retype_vspace_root` |
| VSpace | `vspace_map` (W^X pre-check), `vspace_unmap` |
| Service | `service_register`, `service_revoke`, `service_query` |
| SchedContext | `sched_context_configure`, `sched_context_bind`, `sched_context_unbind` |
| TCB | `tcb_suspend`, `tcb_resume`, `tcb_set_priority`, `tcb_set_mcp`, `tcb_set_ipc_buffer` |

### Phantom-Typed Capabilities

`Cap<Obj, Rts>` provides compile-time tracking of object type and access rights:

```rust
let full: Cap<CNode, FullRights> = Cap::from_cptr(CPtr(10));
let ro: Cap<CNode, ReadOnly> = full.to_read_only(); // safe for standard rights
let restricted = full.restrict(AccessRights::READ | AccessRights::WRITE); // runtime-checked
```

Object markers: `Endpoint`, `Notification`, `CNode`, `Tcb`, `VSpaceRoot`, `Untyped`
Rights markers: `FullRights`, `ReadOnly`, `ReadWrite`, `GrantRights`, `Restricted`

**R1-A/H-01 fix (v0.18.0):** The former `downgrade()` method was removed because
it performed no subset check, allowing `Cap<Endpoint, ReadOnly>` to be converted
to `Cap<Endpoint, FullRights>`. Use `to_read_only()` for safe restriction (panics
if READ is not in current rights — safe for all standard rights descriptors), or
`restrict(mask)` for runtime-checked restriction to an arbitrary mask (panics if
mask is not a subset of current rights).

## Register ABI (ARM64)

```
x0  → CPtr (capability address)
x1  → MessageInfo (encoded bitfield)
x2–x5 → Message registers [0..3]
x7  → Syscall number (SyscallId)
```

Syscalls requiring more than 4 message registers (e.g., `service_register`,
`sched_context_configure`) write the 5th+ values to the IPC buffer overflow
slots via `buf.set_mr(index, value)`. The kernel reads these via
`requireMsgReg` which falls through to the IPC buffer when the inline array
has only 4 entries. These wrappers take `&mut IpcBuffer` as an additional
parameter.

## Testing

- **367 unit tests** across 4 crates (91 abi + 93 conformance + 121 hal + 13 sys + 49 types)
- **93 conformance tests** (RUST-XVAL-001..019 + property tests + W1 ABI tests + AA1 SchedContext/IpcTimeout tests + D6 TCB/AlignmentError tests + AG2-A domain boundary tests + AG2-B wrapper export tests)
- **4 Lean cross-validation vectors** (XVAL-001..004 in MainTraceHarness)
- CI: `scripts/test_rust.sh` integrated into `test_smoke.sh` (Tier 2).
  AA2: Rust toolchain SHA-pinned via `dtolnay/rust-toolchain` (v1, 1.82.0)
- AA1 ABI drift detection: variant count assertions for KernelError (49) and
  SyscallId (25), TypeTag (7), compile-time constant checks for MAX_LABEL,
  MAX_MSG_LENGTH, MAX_EXTRA_CAPS
- AG2-A domain conformance: MAX_DOMAIN matches Lean `numDomainsVal = 16`
  (zero-indexed 0..=15), exhaustive valid/invalid domain boundary tests

### sele4n-hal (AG4, v0.26.5)

Kernel-side ARM64 Hardware Abstraction Layer (`#![no_std]`, `#![allow(unsafe_code)]`).
Unlike the user-space crates, the HAL inherently requires unsafe code for hardware
instructions. Each `unsafe` block carries a `// SAFETY:` comment referencing the
ARM Architecture Reference Manual.

| Module | Purpose | Key Items |
|--------|---------|-----------|
| `cpu` | CPU instructions | `wfe`, `wfi`, `nop`, `eret`, `current_core_id`, **`MPIDR_CORE_ID_MASK_SYM`** shared linker symbol (AN8-B v0.30.9 — H-18), **`wfe_bounded(max_ticks)`** + `WFE_DEFAULT_TIMEOUT_TICKS` (AN9-G v0.30.10 — DEF-R-HAL-L17); **`sev` / `sevl` wrappers + `idle_wait` / `idle_wait_bounded` per-core idle primitives + ~140-line SEV / WFE coordination docstring** (WS-SM SM1.I.3 + SM1.I.5 v0.31.8 — local event register semantics, IS-domain broadcast scope, kernel policy for SEV emission) |
| `barriers` | Memory barriers | `dmb_ish/sy`, `dsb_ish/sy`, `isb`, **`dsb_ishst`**, **`dsb_osh`**, **`dsb_oshst`** + parameterised **`BarrierKind`** enum with `emit()` + composite emitters `emit_armv8_page_table_update` / `emit_tlb_invalidation_bracket` / `emit_mmio_cross_cluster_barrier` (AN9-H/I v0.30.10 — DEF-R-HAL-L18/L19) |
| `svc_dispatch` | SVC typed dispatch | `SyscallArgs::from_trap_frame`, 25-variant `SyscallId` enum, `dispatch_svc(id, args) -> Result<u64, DispatchError>` (AN9-F v0.30.10 — DEF-R-HAL-L14; replaces `NOT_IMPLEMENTED` SVC stub) |
| `psci` | Power State Coordination Interface | `cpu_on`, `cpu_off`, `affinity_info` (+ `AffinityInfoState`), `psci_version` (+ `PsciVersion`), `migrate_info_type` (+ `MigrateInfoType`), `system_off`, `system_reset` — full DEN0022D §5 surface with compile-time function-id pinning (Fast call + SMC32/64 + OEN=4) (AN9-J.1 v0.30.10 — DEF-R-HAL-L20 + WS-SM SM1.A v0.31.9) |
| `smp` | Secondary-core bring-up | `SMP_ENABLED: AtomicBool` (default `false` at module load; Phase 5 stores parsed cmdline value), `CORE_READY: [AtomicBool; 4]`, `bring_up_secondaries`, **`bring_up_secondaries_with_limit(max_cores)`** (WS-SM SM1.D.6 v0.31.6 — limit-aware variant), `rust_secondary_main` (SM1.C full per-core init pipeline: MMU → VBAR → GIC → timer → IRQ → Lean kernel via `lean_secondary_kernel_main`); SM1.B back-compat re-exports of `PerCpuData`, `PER_CPU_DATA`, `PER_CPU_DATA_SLOT_SIZE*`, `per_cpu_slot_addr` (AN9-J v0.30.10 — DEF-R-HAL-L20; SM1.C v0.31.5 closes SMP-C2; SM1.D v0.31.6 wires the cmdline-driven Phase 5; v1.0.0 ships SMP enabled by default via `CmdlineConfig::default()`) |
| `cmdline` | DTB cmdline parser + Phase 5 helpers | `CmdlineConfig { smp_enabled: bool, smp_max_cores: usize }` with `Default::default() = { true, 4 }` (SM1.D.3 — maintainer decision #7); `parse_cmdline(s: &str) -> CmdlineConfig` (robust key=value / quoted / flag-only token parser; unknown keys ignored, malformed values keep default); self-contained DTB walker (`parse_fdt_header`, `validate_fdt_header`, `find_bootargs_in_dtb`, `extract_bootargs_into`, `extract_bootargs_from_blob_into`) with `FDT_WALK_FUEL = 4096` / `FDT_MAX_DEPTH = 32` / `MAX_DTB_SIZE = 2 MiB` / `FDT_PARSER_VERSION = 17` bounds; only direct `/chosen/bootargs` matched (depth-bounded — audit-pass-1 closes the `/chosen/sub/bootargs` exploit); `checked_add` arithmetic throughout for overflow safety; one-shot `parse_cmdline_from_dtb(dtb_ptr: u64) -> CmdlineConfig` (Phase 5 entry); `apply_cmdline_and_start_smp(&CmdlineConfig) -> u32` (writes SMP_ENABLED + dispatches `bring_up_secondaries_with_limit`); audit-pass-1 `pub(crate) fn apply_cmdline_and_start_smp_inner` for test isolation (WS-SM SM1.D v0.31.6) |
| `per_cpu` | Per-CPU data block + TPIDR_EL1 accessors | `PerCpuData` (`core_id: u64` + 56-byte reserved tail, cache-line aligned), `PER_CPU_DATA: [PerCpuData; 4]` (each slot pre-populated with its index as `core_id`), `PER_CPU_DATA_SLOT_SIZE` / `PER_CPU_DATA_SLOT_SIZE_SYM` (asm-visible stride), `per_cpu_slot_addr(context_id)`, `current_per_cpu() -> &'static PerCpuData`, `current_core_id_from_tpidr() -> u64`, `check_per_cpu_invariants()` boot gate (WS-SM SM1.B v0.31.9 — closes SMP-M4) |
| `ffi::ffi_current_core_id` | Lean FFI: current core id via TPIDR_EL1 | `#[no_mangle] pub extern "C" fn ffi_current_core_id() -> u64`; Lean side: `@[extern] opaque Platform.FFI.ffiCurrentCoreId : BaseIO UInt64` + typed wrapper `Concurrency.currentCoreId : BaseIO CoreId` in `SeLe4n/Kernel/Concurrency/Runtime.lean` (WS-SM SM1.B.5 v0.31.9) |
| `registers` | System register I/O | `read_sysreg!`/`write_sysreg!` macros, 11 typed accessors |
| `uart` | PL011 UART driver | `Uart` struct, `kprint!`/`kprintln!` macros, 0xFE201000 base, `UartLock` spinlock (AI1-D), `UnsafeCell`-based safe static (AJ5-B), **`UartGuard<'a>` RAII pattern** (AN8-A v0.30.9 — H-17), **`kprintln_core!` / `kprint_core!` per-core macros** (WS-SM SM1.G.4 v0.31.7 — prefix every line with `[core N]` read from TPIDR_EL1); UartLock SMP-correctness audit block in file header documents Acquire/Release semantics + per-acquire DAIF mask + the FIFO-fairness gap that SM2's `TicketLock` will close at SM2.B (WS-SM SM1.G.1 v0.31.7) |
| `mmu` | MMU configuration | MAIR/TCR/TTBR/SCTLR, identity-mapped L1 boot tables; `init_mmu` (primary) + `init_mmu_per_core(core_id)` (shared helper) + `init_mmu_secondary(core_id)` (WS-SM SM1.C.1 v0.31.5 — secondary cores reuse the primary's boot L1 table) |
| `trap` | Exception dispatch | `TrapFrame` (272 bytes), ESR EC routing, SVC/IRQ/SError handlers, `error_code` constants (AI1-A/B); **`handle_irq_per_core(&mut TrapFrame)` SM5 landing seam** (WS-SM SM1.I.1 v0.31.8 — reads TPIDR_EL1, records per-core IRQ / timer-tick / SGI stats via `per_cpu_stats::record_*`, dispatches via `gic::dispatch_irq` with per-core attribution; build-script scanner `scan_trap_rs_handle_irq_per_core_intact` pins the 4-property contract); **per-core counter wiring in `handle_synchronous_exception`** (WS-SM SM1.I.4 v0.31.8 — each EC branch increments its category counter: SVC → syscall_count; DABT/IABT → vmfault_count; alignment/unknown → user_exception_count) |
| `boot` | Boot sequence | Six phases: Phase 1 (`init_boot_uart` + `check_per_cpu_invariants`; SM1.D.5 moved the per-CPU check here from Phase 4), Phase 2 (`init_mmu` + `install_exception_vectors`), Phase 3 (`init_gic` + `init_timer`), Phase 4 (TPIDR_EL1 + `enable_irq`), Phase 5 (WS-SM SM1.D v0.31.6 — `cmdline::parse_cmdline_from_dtb` + `cmdline::apply_cmdline_and_start_smp` driving secondary-core bring-up), Phase 6 (handoff to Lean kernel main); `install_exception_vectors()` (WS-SM SM1.C.2 v0.31.5 — extracted from formerly-private `set_vbar`, shared with `smp::rust_secondary_main`); `KERNEL_VERSION` bumped to `0.31.8` |
| `gic` | GIC-400 driver | Distributor + CPU interface init, acknowledge/dispatch/EOI, `dispatch_irq<F>()` (AG5), **EOI-before-handler ordering** (AN8-C v0.30.9 — H-19, audit Option b), boot-time `self_check_distributor` (AN8-D RUST-M05); `init_cpu_interface_secondary(core_id)` (WS-SM SM1.C.3 v0.31.5 — per-core CPU interface init for secondaries); **WS-SM SM1.F v0.31.7 — SGI primitive surface**: `GICD_SGIR` constant + 16-INTID bound + 3 TargetListFilter discriminants; `send_sgi(target_mask, intid)` / `send_sgi_to_self(intid)` / `send_sgi_to_all_but_self(intid)` (each emits `dsb ish` BEFORE the SGIR write per ARM ARM B2.7.5; new build-script scanner pins the ordering); `SgiHandler = fn(intid: u8, source_cpu: u8)` type + `SGI_HANDLERS` per-INTID handler table + `register_sgi_handler` / `lookup_sgi_handler` / `dispatch_sgi` infrastructure; `iar_source_cpu(iar)` extracts source-CPU bits [12:10] from a raw GICC_IAR per GIC-400 §4.4.4 |
| `timer` | ARM Generic Timer | 54 MHz counter, 1000 Hz tick, `reprogram_timer()`, `increment_tick_count()` (AG5), `TimerError` result type (AJ5-C), `pub(crate)` tick visibility (AJ5-D); `init_timer_secondary(tick_hz)` (WS-SM SM1.C.4 v0.31.5 — per-core timer arm without resetting primary's `TICK_COUNT`) |
| `interrupts` | Interrupt management | `disable_interrupts`/`restore_interrupts`/`enable_irq`, DAIF register (AG5); **WS-SM SM1.I.2 v0.31.8 — per-PE DAIF.I scoping documentation** (module header explains DAIF.I as per-PE per ARM ARM C5.2.5 composing with the per-core GICC_PMR layer for two-layer per-core IRQ masking, no software lock required) |
| `tlb` | TLB maintenance | Local non-broadcast: TLBI VMALLE1/VAE1/ASIDE1/VALE1 + DSB ISH + ISB (AG6).  **WS-SM SM1.E v0.31.7 — broadcast variants**: 4 IS-variant wrappers (`tlbi_vmalle1is`, `tlbi_vae1is`, `tlbi_aside1is`, `tlbi_vale1is`) for inner-shareable broadcast (DSB ISH bracket); 4 OS-variant wrappers (`tlbi_vmalle1os` etc.) for outer-shareable broadcast (DSB OSH bracket); `pub enum SharingDomain { Inner, Outer }` mirrors the Lean SM0.F enum; `pub enum TlbInvalidation { Vmalle1, Vae1, Aside1, Vale1 }` typed op selector; `tlbi_for_sharing(domain, op)` dispatcher routes to one of the 8 underlying IS/OS variants — single entry point that production kernel code under SMP must use |
| `cache` | Cache maintenance | DC CIVAC/CVAC/IVAC/ZVA, IC IALLU/IALLUIS, aligned `cache_range` (AG6), **`memory_fence()`** pure DSB ISH helper (AN8-D v0.30.9 — RUST-M07) |
| `mmio` | MMIO volatile I/O | `mmio_read32/write32/read64/write64`, runtime alignment `assert!` (AJ5-A) |
| `ffi` | Lean FFI bridge | 31 `#[no_mangle] extern "C"` exports for timer, GIC, TLB, MMIO, UART, interrupts, suspendThread bracket, cache+TLB composition, per-CPU core id (`ffi_current_core_id` at SM1.B.5), **`ffi_tlbi_for_sharing` / `ffi_send_sgi*` (WS-SM SM1.E.4 + SM1.F.6 v0.31.7)**, **`ffi_idle_wait` / `ffi_idle_wait_bounded` (WS-SM SM1.I.3 v0.31.8)** + **`ffi_per_core_irq_count` / `ffi_per_core_timer_tick_count` / `ffi_per_core_sgi_count` / `ffi_per_core_syscall_count` (WS-SM SM1.I.4 v0.31.8 — each performs a defense-in-depth u64 bound check before the `as usize` cast)** (AG7 + AN9-A/D + WS-SM SM1.B/E/F/I) |
| `per_cpu_stats` | Per-core exception / interrupt statistics | **WS-SM SM1.I.4 v0.31.8 — NEW MODULE** (~700 LoC).  `PerCpuStats` `#[repr(C, align(64))]` cache-line-aligned struct (6 AtomicU64 counters: `irq_count` / `timer_tick_count` / `sgi_count` / `syscall_count` / `vmfault_count` / `user_exception_count` + 2-slot reserved tail for SM5+ growth); `PER_CPU_STATS: [PerCpuStats; 4]` global array; compile-time `const _: ()` assertions pin size + alignment.  Write path: `record_*` functions (Relaxed atomics, `fetch_add(1).wrapping_add(1)` overflow-safe at u64::MAX boundary, wait-free); read path: `*_count_for(core_id: usize)` Relaxed-snapshot accessors with defensive out-of-range return-0 contract; inner forms `record_*_in_slice` for unit-testing cross-core scenarios without racing on the global static; aggregate `total_irq_count` / `total_syscall_count` helpers |
| `profiling` | Performance profiling | `LatencyStats`, PMCCNTR_EL0 cycle counter (AG9) |

Assembly files: `boot.S` (entry point), `vectors.S` (exception vector table),
`trap.S` (context save/restore). Linker script: `link.ld` (0x80000 entry).

All AArch64-specific code gated behind `cfg(target_arch = "aarch64")` for
cross-platform compilation and testing on x86_64.

## Canonical Sources

- Master plan: `docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md` (Q8)
- Lean ABI: `SeLe4n/Kernel/Architecture/RegisterDecode.lean`
- Lean args: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`
- Rust source: `rust/sele4n-types/`, `rust/sele4n-abi/`, `rust/sele4n-sys/`, `rust/sele4n-hal/`
