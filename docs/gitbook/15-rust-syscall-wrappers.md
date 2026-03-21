# 15 — Rust Syscall Wrappers

## Overview

`libsele4n` is a `no_std` Rust userspace library providing safe, typed wrappers
around all 14 seLe4n syscalls. It mirrors the verified Lean ABI surface exactly,
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
  `VAddr`, `PAddr`, `RegValue`
- **`KernelError`**: 34-variant enum (1:1 with Lean `KernelError`)
- **`AccessRight` / `AccessRights`**: 5-right bitmask (O(1) operations)
- **`SyscallId`**: 14-variant enum (0–13)

### sele4n-abi

ARM64 register ABI layer with exactly one `unsafe` block:

- **`MessageInfo`**: Bitfield encode/decode (7-bit length, 2-bit extraCaps)
- **`SyscallRequest` / `SyscallResponse`**: Register structures
- **`raw_syscall`**: Inline `svc #0` — the single `unsafe` function
- **Per-syscall argument structures**: CSpace (4), Lifecycle (1), VSpace (2),
  Service (3)
- **`TypeTag`**: 6 retype variants (TCB=0, Endpoint=1, ..., Untyped=5)
- **`PagePerms`**: Permission bitmask with W^X enforcement
- **`IpcBuffer`**: Overflow message registers (4–119) for messages exceeding
  the 4 inline ARM64 registers

### sele4n-sys

Safe high-level wrappers for all 14 syscalls:

| Subsystem | Operations |
|-----------|-----------|
| IPC | `endpoint_send`, `endpoint_receive`, `endpoint_call`, `endpoint_reply`, `notification_signal`, `notification_wait` |
| CSpace | `cspace_mint`, `cspace_copy`, `cspace_move`, `cspace_delete` |
| Lifecycle | `lifecycle_retype`, `retype_tcb`, `retype_endpoint`, `retype_notification`, `retype_cnode`, `retype_vspace_root` |
| VSpace | `vspace_map` (W^X pre-check), `vspace_unmap` |
| Service | `service_register`, `service_revoke`, `service_query` |

### Phantom-Typed Capabilities

`Cap<Obj, Rts>` provides compile-time tracking of object type and access rights:

```rust
let full: Cap<CNode, FullRights> = Cap::from_cptr(CPtr(10));
let ro: Cap<CNode, ReadOnly> = full.to_read_only(); // always safe
let restricted = full.restrict(AccessRights::READ | AccessRights::WRITE); // runtime-checked
```

Object markers: `Endpoint`, `Notification`, `CNode`, `Tcb`, `VSpaceRoot`, `Untyped`
Rights markers: `FullRights`, `ReadOnly`, `ReadWrite`, `GrantRights`, `Restricted`

**R1-A/H-01 fix (v0.18.0):** The former `downgrade()` method was removed because
it performed no subset check, allowing `Cap<Endpoint, ReadOnly>` to be converted
to `Cap<Endpoint, FullRights>`. Use `to_read_only()` for safe unconditional
restriction, or `restrict(mask)` for runtime-checked restriction to an arbitrary
mask (panics if mask is not a subset of current rights).

## Register ABI (ARM64)

```
x0  → CPtr (capability address)
x1  → MessageInfo (encoded bitfield)
x2–x5 → Message registers [0..3]
x7  → Syscall number (SyscallId)
```

## Testing

- **64 unit tests** across 3 crates
- **25 conformance tests** (RUST-XVAL-001..019 + property tests)
- **4 Lean cross-validation vectors** (XVAL-001..004 in MainTraceHarness)
- CI: `scripts/test_rust.sh` integrated into `test_smoke.sh` (Tier 2)

## Canonical Sources

- Master plan: `docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md` (Q8)
- Lean ABI: `SeLe4n/Kernel/Architecture/RegisterDecode.lean`
- Lean args: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`
- Rust source: `rust/sele4n-types/`, `rust/sele4n-abi/`, `rust/sele4n-sys/`
