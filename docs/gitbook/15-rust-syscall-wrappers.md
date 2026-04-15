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
| `cpu` | CPU instructions | `wfe`, `wfi`, `nop`, `eret`, `current_core_id` |
| `barriers` | Memory barriers | `dmb_ish/sy`, `dsb_ish/sy`, `isb` |
| `registers` | System register I/O | `read_sysreg!`/`write_sysreg!` macros, 11 typed accessors |
| `uart` | PL011 UART driver | `Uart` struct, `kprint!`/`kprintln!` macros, 0xFE201000 base, `UartLock` spinlock (AI1-D), `UnsafeCell`-based safe static (AJ5-B) |
| `mmu` | MMU configuration | MAIR/TCR/TTBR/SCTLR, identity-mapped L1 boot tables |
| `trap` | Exception dispatch | `TrapFrame` (272 bytes), ESR EC routing, SVC/IRQ/SError handlers, `error_code` constants (AI1-A/B) |
| `boot` | Boot sequence | `_start` → BSS zero → stack → UART → MMU → VBAR → idle |
| `gic` | GIC-400 driver | Distributor + CPU interface init, acknowledge/dispatch/EOI, `dispatch_irq<F>()` (AG5) |
| `timer` | ARM Generic Timer | 54 MHz counter, 1000 Hz tick, `reprogram_timer()`, `increment_tick_count()` (AG5), `TimerError` result type (AJ5-C), `pub(crate)` tick visibility (AJ5-D) |
| `interrupts` | Interrupt management | `disable_interrupts`/`restore_interrupts`/`enable_irq`, DAIF register (AG5) |
| `tlb` | TLB maintenance | TLBI VMALLE1/VAE1/ASIDE1/VALE1 + DSB ISH + ISB (AG6) |
| `cache` | Cache maintenance | DC CIVAC/CVAC/IVAC/ZVA, IC IALLU/IALLUIS, aligned `cache_range` (AG6) |
| `mmio` | MMIO volatile I/O | `mmio_read32/write32/read64/write64`, runtime alignment `assert!` (AJ5-A) |
| `ffi` | Lean FFI bridge | 17 `#[no_mangle] extern "C"` exports for timer, GIC, TLB, MMIO, UART, interrupts (AG7) |
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
