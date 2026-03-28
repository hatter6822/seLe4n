# 15 — Rust Syscall Wrappers

## Overview

`libsele4n` is a `no_std` Rust userspace library providing safe, typed wrappers
around all 17 seLe4n syscalls. It mirrors the verified Lean ABI surface exactly,
enabling Rust userspace programs to invoke kernel operations with compile-time
type safety and zero `unsafe` code outside the syscall trap instruction.

## Crate Architecture

```
sele4n-sys           (safe high-level wrappers)
  └── sele4n-abi     (register encoding + svc trap)
        └── sele4n-types  (core types, no unsafe)
```

### sele4n-types

Core type definitions with zero `unsafe` and zero external dependencies:

- **14 newtype identifiers**: `ObjId`, `ThreadId`, `CPtr`, `Slot`, `DomainId`,
  `Priority`, `Deadline`, `Irq`, `ServiceId`, `InterfaceId`, `Badge`, `Asid`,
  `VAddr`, `PAddr`, `RegValue` — inner fields are `pub(crate)` with `.raw()`
  accessors (R8-E/L-11 encapsulation)
- **`KernelError`**: 41-variant `#[non_exhaustive]` enum (1:1 with Lean
  `KernelError`; U3-F, W1-D: +MmioUnaligned)
- **`AccessRight` / `AccessRights`**: 5-right bitmask (O(1) operations).
  `TryFrom<u8>` rejects invalid bytes with bits 5–7 set (U3-D)
- **`AccessRightsError`**: Error type for invalid `AccessRights` construction
- **`SyscallId`**: 17-variant enum (0–16), including notificationSignal, notificationWait, replyRecv (V2-A/D)

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
  Service (3)
- **`TypeTag`**: 6 retype variants (TCB=0, Endpoint=1, ..., Untyped=5)
- **`PagePerms`**: Permission bitmask with W^X enforcement
- **`IpcBuffer`**: Overflow message registers (4–119) for messages exceeding
  the 4 inline ARM64 registers. Compile-time layout assertions verify 960-byte
  `#[repr(C)]` size and 8-byte alignment (U3-I)

### sele4n-sys

Safe high-level wrappers for all 17 syscalls:

| Subsystem | Operations |
|-----------|-----------|
| IPC | `endpoint_send`, `endpoint_receive`, `endpoint_call`, `endpoint_reply`, `notification_signal`, `notification_wait`, `endpoint_reply_recv` |
| CSpace | `cspace_mint`, `cspace_copy`, `cspace_move`, `cspace_delete` |
| Lifecycle | `lifecycle_retype`, `retype_tcb`, `retype_endpoint`, `retype_notification`, `retype_cnode`, `retype_vspace_root` |
| VSpace | `vspace_map` (W^X pre-check), `vspace_unmap` |
| Service | `service_register`, `service_revoke`, `service_query` |

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

## Testing

- **168 unit tests** across 3 crates (68 abi + 55 conformance + 12 sys + 33 types)
- **25+ conformance tests** (RUST-XVAL-001..019 + property tests + W1 ABI tests)
- **4 Lean cross-validation vectors** (XVAL-001..004 in MainTraceHarness)
- CI: `scripts/test_rust.sh` integrated into `test_smoke.sh` (Tier 2)
- W1 ABI drift detection: variant count assertions for KernelError (41) and
  SyscallId (17), compile-time constant checks for MAX_LABEL, MAX_MSG_LENGTH,
  MAX_EXTRA_CAPS

## Canonical Sources

- Master plan: `docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md` (Q8)
- Lean ABI: `SeLe4n/Kernel/Architecture/RegisterDecode.lean`
- Lean args: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`
- Rust source: `rust/sele4n-types/`, `rust/sele4n-abi/`, `rust/sele4n-sys/`
