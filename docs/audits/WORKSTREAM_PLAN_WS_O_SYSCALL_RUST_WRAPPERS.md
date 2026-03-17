# WS-O Workstream Plan — Syscall Rust Wrappers (v0.17.0)

**Created**: 2026-03-17
**Baseline version**: 0.17.0
**Scope**: Expose seLe4n's verified Lean syscall semantics as safe Rust wrappers
**Prior portfolios**: WS-M (v0.17.0, complete), WS-L (v0.16.13, complete), WS-K (v0.16.8, complete)
**Hardware target**: Raspberry Pi 5 (AArch64, BCM2712)
**Constraint**: Zero `unsafe` outside the syscall invocation boundary; zero `sorry`/`axiom` in Lean proof surface

---

## 1. Motivation & Scope

seLe4n defines every kernel transition as an executable pure function in Lean 4
with machine-checked proofs. The syscall entry path flows through three verified
layers:

1. **RegisterDecode** — raw ARM64 registers → `SyscallDecodeResult` (deterministic, total)
2. **SyscallArgDecode** — message registers → per-syscall typed argument structs (7 structures)
3. **API dispatch** — capability-gated invocation of kernel operations (13 syscalls)

All three layers have round-trip theorems, error-exclusivity proofs, and
determinism guarantees. The information-flow enforcement layer adds 7
policy-checked wrappers with soundness theorems.

**This workstream** builds the inverse path: a `no_std` Rust userspace library
(`libsele4n`) that encodes typed Rust structures into the exact register layout
the kernel expects, invokes the `svc` trap, and decodes the kernel's response.
Every Rust type, constant, and encoding function is derived directly from the
Lean source, ensuring the Rust ABI is a faithful mirror of the verified
semantics.

### What this workstream delivers

- A `no_std` Rust workspace (`rust/`) with three crates:
  - `sele4n-types` — core typed identifiers, error types, capability types
  - `sele4n-abi` — register-level syscall encoding/decoding, inline `svc` trap
  - `sele4n-sys` — safe high-level syscall wrappers, IPC helpers, capability handles
- Type-safe Rust newtypes mirroring every Lean typed identifier
- Per-syscall argument encoding matching `SyscallArgDecode.lean` round-trip properties
- Safe wrappers for all 13 syscalls with compile-time right verification where possible
- Phantom-typed capability handles enforcing access rights at the Rust type level
- Conformance test suite cross-validating Rust encoding against Lean decoding
- Integration with the existing Lake build and test tier system

### What this workstream does NOT deliver

- Kernel-side FFI (deferred to H3 hardware binding workstream)
- Lean-to-Rust extraction/compilation (the kernel remains pure Lean)
- Runtime information-flow enforcement in Rust (kernel-side responsibility)
- VSpaceBackend or MMU driver implementation (H3 scope)

---

## 2. Architectural Overview

### 2.1 Register ABI (ARM64)

The seLe4n syscall ABI follows the seL4 ARM64 convention defined in
`RegisterDecode.lean`:

```
Register    Purpose                     Lean Field
────────    ───────                     ──────────
x0          Capability address (CPtr)   decoded.capAddr
x1          MessageInfo (bitfield)      decoded.msgInfo
x2–x5       Message registers [0..3]    decoded.msgRegs[0..3]
x7          Reply badge / status        (return value)
x8          Syscall ID                  decoded.syscallId
```

MessageInfo bitfield layout (from `decodeMsgInfo`):
- Bits 0–6: message length (0..120)
- Bits 7–8: extra caps count (0..3)
- Bits 9+: user label

### 2.2 Syscall ID Enumeration

From `SyscallId` in `RegisterDecode.lean`:

| ID | Syscall | Required Right | Lean Entry Point |
|----|---------|----------------|------------------|
| 0  | `Send` | `.write` | `apiEndpointSend` |
| 1  | `Receive` | `.read` | `apiEndpointReceive` |
| 2  | `Call` | `.write` | `apiEndpointCall` |
| 3  | `Reply` | `.write` | `apiEndpointReply` |
| 4  | `CSpaceMint` | `.grant` | `apiCspaceMint` |
| 5  | `CSpaceCopy` | `.grant` | `apiCspaceCopy` |
| 6  | `CSpaceMove` | `.grant` | `apiCspaceMove` |
| 7  | `CSpaceDelete` | `.write` | `apiCspaceDelete` |
| 8  | `LifecycleRetype` | `.retype` | `apiLifecycleRetype` |
| 9  | `VSpaceMap` | `.write` | `apiVspaceMap` |
| 10 | `VSpaceUnmap` | `.write` | `apiVspaceUnmap` |
| 11 | `ServiceStart` | `.write` | `apiServiceStart` |
| 12 | `ServiceStop` | `.write` | `apiServiceStop` |

### 2.3 Crate Dependency Graph

```
sele4n-sys          (safe high-level wrappers)
  └── sele4n-abi    (register encoding + svc trap)
        └── sele4n-types  (core types, no unsafe)
```

### 2.4 Lean ↔ Rust Type Correspondence

| Lean Type | Rust Type | Crate | Notes |
|-----------|-----------|-------|-------|
| `ObjId` | `ObjId(u64)` | `sele4n-types` | Newtype, `#[repr(transparent)]` |
| `ThreadId` | `ThreadId(u64)` | `sele4n-types` | `.to_obj_id()` preserves injection |
| `CPtr` | `CPtr(u64)` | `sele4n-types` | Null = `CPtr(0)` sentinel |
| `Slot` | `Slot(u64)` | `sele4n-types` | Within CNode address space |
| `DomainId` | `DomainId(u64)` | `sele4n-types` | Scheduling domain |
| `Priority` | `Priority(u64)` | `sele4n-types` | Run queue insertion key |
| `Badge` | `Badge(u64)` | `sele4n-types` | IPC notification badge |
| `ASID` | `Asid(u64)` | `sele4n-types` | VSpace lookup key |
| `VAddr` | `VAddr(u64)` | `sele4n-types` | Virtual address |
| `PAddr` | `PAddr(u64)` | `sele4n-types` | Physical address |
| `RegValue` | `RegValue(u64)` | `sele4n-types` | Raw machine word |
| `AccessRight` | `AccessRight` enum | `sele4n-types` | 5 variants |
| `AccessRightSet` | `AccessRights(u8)` | `sele4n-types` | Bitmask, same bit positions |
| `KernelError` | `KernelError` enum | `sele4n-types` | 1:1 variant mapping |
| `SyscallId` | `SyscallId` enum | `sele4n-types` | `#[repr(u64)]`, 13 variants |
| `MessageInfo` | `MessageInfo` | `sele4n-abi` | Bitfield encode/decode |
| `IpcMessage` | `IpcMessage` | `sele4n-sys` | Builder pattern, bounds-checked |
| `Capability` | `Cap<Obj, Rights>` | `sele4n-sys` | Phantom-typed handle |

---

## 3. Planning Principles

1. **Semantic fidelity**: Every Rust constant, encoding function, and type must be
   derivable from the Lean source. Where the Lean model defines a round-trip
   theorem, the Rust encoding must satisfy the same property.
2. **Minimal unsafe surface**: `unsafe` is permitted only for the `svc` inline
   assembly trap in `sele4n-abi`. All other code is safe Rust.
3. **no_std by default**: All three crates target `#![no_std]` for bare-metal
   AArch64 deployment. Optional `std` feature for host-side testing.
4. **Type-level safety where possible**: Use Rust's type system (phantom types,
   const generics, sealed traits) to enforce capability rights at compile time.
   Fall back to runtime checks only where compile-time enforcement is impossible.
5. **Incremental delivery**: Each phase is independently compilable and testable.
   Earlier phases provide building blocks for later ones.
6. **Cross-validation**: Conformance tests encode values in Rust and verify that
   the Lean decoder produces identical results, and vice versa.
7. **Zero Lean regression**: No changes to existing Lean proof surface. New Lean
   code (if any) is limited to test harness extensions for cross-validation.
8. **Coherent with H3**: The crate structure anticipates the H3 hardware binding
   workstream. `sele4n-abi` will serve as the foundation for kernel-side trap
   handling when H3 lands.

---

## 4. Phase Overview

| Phase | ID | Focus | Priority | Target Version | Estimated Subtasks |
|-------|----|-------|----------|----------------|--------------------|
| 1 | **WS-O1** | Foundation: Cargo workspace, core types crate, error types, access rights | HIGH | v0.17.1 | 12 |
| 2 | **WS-O2** | Register ABI: MessageInfo bitfield, syscall encoding, `svc` trap, raw invoke | HIGH | v0.17.2 | 14 |
| 3 | **WS-O3** | Argument structures: per-syscall typed args, encode functions, validation | HIGH | v0.17.3 | 10 |
| 4 | **WS-O4** | IPC wrappers: send, receive, call, reply, notification signal/wait | MEDIUM | v0.17.4 | 12 |
| 5 | **WS-O5** | CSpace wrappers: mint, copy, move, delete with rights enforcement | MEDIUM | v0.17.5 | 10 |
| 6 | **WS-O6** | Lifecycle & VSpace wrappers: retype, map, unmap, service start/stop | MEDIUM | v0.17.6 | 10 |
| 7 | **WS-O7** | Type-safe capability handles: phantom types, builder patterns, ergonomics | LOW | v0.17.7 | 11 |
| 8 | **WS-O8** | Conformance testing, CI integration, documentation | LOW | v0.17.8 | 10 |

**Total**: 8 phases, ~89 atomic subtasks.

---

## 5. Detailed Phase Plans

### Phase 1: Foundation — Core Types Crate (WS-O1)

**Focus**: Establish the Rust workspace and define all core types that mirror
the Lean typed identifiers in `Prelude.lean`, `Model/Object/Types.lean`, and
`Model/State.lean`.

**Priority**: HIGH — all subsequent phases depend on these types.
**Target version**: v0.17.1
**Files created**: `rust/Cargo.toml`, `rust/sele4n-types/Cargo.toml`,
`rust/sele4n-types/src/lib.rs`, `rust/sele4n-types/src/identifiers.rs`,
`rust/sele4n-types/src/error.rs`, `rust/sele4n-types/src/rights.rs`,
`rust/sele4n-types/src/syscall.rs`
**Lean files referenced** (read-only): `SeLe4n/Prelude.lean`,
`SeLe4n/Model/Object/Types.lean`, `SeLe4n/Model/State.lean`

#### O1-A: Cargo Workspace Scaffold (3 subtasks)

**O1-A1**: Create `rust/Cargo.toml` workspace manifest with three members:
`sele4n-types`, `sele4n-abi`, `sele4n-sys`. Set `resolver = "2"`, shared
`[profile]` for size optimization (`opt-level = "z"`, `lto = true` for release).
Target: `aarch64-unknown-none` (bare-metal ARM64).

**O1-A2**: Create `rust/sele4n-types/Cargo.toml` with `#![no_std]` default,
optional `std` feature for testing. No dependencies beyond `core`. Set
`version = "0.1.0"`, `edition = "2021"`.

**O1-A3**: Create `rust/sele4n-types/src/lib.rs` with `#![no_std]`,
`#![deny(unsafe_code)]` (this crate has zero unsafe), module declarations.
Add `#![cfg_attr(not(feature = "std"), no_std)]` for conditional std support.

#### O1-B: Typed Identifiers (3 subtasks)

**O1-B1**: Define newtype wrappers in `rust/sele4n-types/src/identifiers.rs`
for all 14 Lean typed identifiers:

```rust
/// Lean: `structure ObjId where val : Nat` (Prelude.lean:47)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ObjId(pub u64);

/// Lean: `structure ThreadId where val : Nat` (Prelude.lean:75)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ThreadId(pub u64);

// ... CPtr, Slot, DomainId, Priority, Deadline, Irq, ServiceId,
//     Badge, Asid, VAddr, PAddr, RegValue
```

Each newtype gets:
- `#[repr(transparent)]` for zero-cost ABI compatibility
- `From<u64>` and `Into<u64>` conversions (matching `.ofNat`/`.toNat`)
- `const SENTINEL: Self` where applicable (ObjId(0), CPtr(0), ServiceId(0))
- Doc comments referencing the exact Lean source location

**O1-B2**: Implement `ThreadId::to_obj_id(&self) -> ObjId` preserving the
Lean injection property (`ThreadId.toObjId_injective`). Document that distinct
`ThreadId` values map to distinct `ObjId` values.

**O1-B3**: Implement `Badge::bor(self, other: Badge) -> Badge` matching the
Lean `Badge.bor` accumulation semantics used in notification signaling
(WS-F5/D1c). This is bitwise OR on the inner `u64`.

#### O1-C: Error Types (2 subtasks)

**O1-C1**: Define `KernelError` enum in `rust/sele4n-types/src/error.rs`
with exact 1:1 variant mapping from `Model/State.lean:15–50`:

```rust
/// Lean: `inductive KernelError` (Model/State.lean:15)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum KernelError {
    InvalidCapability = 0,
    ObjectNotFound = 1,
    IllegalState = 2,
    IllegalAuthority = 3,
    FlowDenied = 4,
    DeclassificationDenied = 5,
    InvalidRegister = 6,
    InvalidSyscallNumber = 7,
    InvalidMessageInfo = 8,
    IpcMessageTooLarge = 9,
    IpcMessageTooManyCaps = 10,
    InvalidTypeTag = 11,
    AddressOutOfBounds = 12,
    // ... all variants from KernelError
}
```

Include `#[repr(u32)]` for stable ABI encoding in return registers. Add
`Display` impl for human-readable error messages.

**O1-C2**: Define `pub type KernelResult<T> = Result<T, KernelError>` as the
standard return type for all syscall wrappers. This mirrors
`Except KernelError α` in the Lean model.

#### O1-D: Access Rights & Syscall IDs (4 subtasks)

**O1-D1**: Define `AccessRight` enum in `rust/sele4n-types/src/rights.rs`:

```rust
/// Lean: `inductive AccessRight` (Model/Object/Types.lean)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AccessRight {
    Read,
    Write,
    Grant,
    GrantReply,
    Retype,
}
```

**O1-D2**: Define `AccessRights` bitmask struct matching `AccessRightSet`:

```rust
/// Lean: `structure AccessRightSet where bits : Nat` (Model/Object/Types.lean)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct AccessRights(u8);

impl AccessRights {
    pub const READ: Self = Self(1 << 0);
    pub const WRITE: Self = Self(1 << 1);
    pub const GRANT: Self = Self(1 << 2);
    pub const GRANT_REPLY: Self = Self(1 << 3);
    pub const RETYPE: Self = Self(1 << 4);
    pub const ALL: Self = Self(0x1F);
    pub const EMPTY: Self = Self(0);

    pub const fn contains(self, right: AccessRight) -> bool { ... }
    pub const fn union(self, other: Self) -> Self { ... }
    pub const fn intersection(self, other: Self) -> Self { ... }
    pub const fn is_subset_of(self, other: Self) -> bool { ... }
}
```

Bit positions must match the Lean `AccessRightSet.singleton` encoding exactly.

**O1-D3**: Define `SyscallId` enum in `rust/sele4n-types/src/syscall.rs`:

```rust
/// Lean: `inductive SyscallId` (RegisterDecode.lean)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u64)]
pub enum SyscallId {
    Send = 0,
    Receive = 1,
    Call = 2,
    Reply = 3,
    CSpaceMint = 4,
    CSpaceCopy = 5,
    CSpaceMove = 6,
    CSpaceDelete = 7,
    LifecycleRetype = 8,
    VSpaceMap = 9,
    VSpaceUnmap = 10,
    ServiceStart = 11,
    ServiceStop = 12,
}
```

Include `TryFrom<u64>` returning `Err(KernelError::InvalidSyscallNumber)` for
values outside 0–12, matching `decodeSyscallId` error behavior.

**O1-D4**: Define the `syscall_required_right` mapping function:

```rust
/// Lean: `syscallRequiredRight` (API.lean:155)
pub const fn syscall_required_right(id: SyscallId) -> AccessRight {
    match id {
        SyscallId::Send | SyscallId::Call | SyscallId::Reply => AccessRight::Write,
        SyscallId::Receive => AccessRight::Read,
        SyscallId::CSpaceMint | SyscallId::CSpaceCopy | SyscallId::CSpaceMove => AccessRight::Grant,
        SyscallId::CSpaceDelete => AccessRight::Write,
        SyscallId::LifecycleRetype => AccessRight::Retype,
        SyscallId::VSpaceMap | SyscallId::VSpaceUnmap => AccessRight::Write,
        SyscallId::ServiceStart | SyscallId::ServiceStop => AccessRight::Write,
    }
}
```

#### O1 Verification

- `cargo build --target aarch64-unknown-none` compiles with zero warnings
- `cargo test --features std` passes on host (x86_64)
- All `#[repr]` attributes verified against Lean type sizes
- Doc comments reference exact Lean source file and line number

---

### Phase 2: Register ABI — Encoding & Trap (WS-O2)

**Focus**: Implement the register-level syscall encoding/decoding layer and the
raw `svc` trap instruction. This is the only phase that introduces `unsafe` code.

**Priority**: HIGH — the ABI layer is the bridge between Rust userspace and the
Lean-verified kernel.
**Target version**: v0.17.2
**Files created**: `rust/sele4n-abi/Cargo.toml`, `rust/sele4n-abi/src/lib.rs`,
`rust/sele4n-abi/src/message_info.rs`, `rust/sele4n-abi/src/encode.rs`,
`rust/sele4n-abi/src/decode.rs`, `rust/sele4n-abi/src/trap.rs`
**Lean files referenced** (read-only): `SeLe4n/Kernel/Architecture/RegisterDecode.lean`

#### O2-A: Crate Scaffold (2 subtasks)

**O2-A1**: Create `rust/sele4n-abi/Cargo.toml` with dependency on `sele4n-types`.
`#![no_std]`, `#![forbid(unsafe_code)]` at crate level with a targeted
`#![allow(unsafe_code)]` only in `trap.rs`. Optional `std` feature for testing.

**O2-A2**: Create `rust/sele4n-abi/src/lib.rs` with module declarations and
re-exports. Public API surface: `MessageInfo`, `SyscallRequest`, `SyscallResponse`,
`encode_syscall`, `decode_response`, `raw_syscall` (the only unsafe fn).

#### O2-B: MessageInfo Bitfield (3 subtasks)

**O2-B1**: Implement `MessageInfo` encoding in `rust/sele4n-abi/src/message_info.rs`:

```rust
/// Lean: `structure MessageInfo` (Model/Object/Types.lean)
/// Bitfield: bits 0–6 = length, bits 7–8 = extraCaps, bits 9+ = label
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MessageInfo {
    length: u8,      // 0..=120 (validated)
    extra_caps: u8,  // 0..=3 (validated)
    label: u64,      // user-specified
}
```

Constructor validates bounds: `length ≤ 120`, `extra_caps ≤ 3` (matching
`decodeMsgInfo` validation in `RegisterDecode.lean:95–102`). Returns
`Err(KernelError::InvalidMessageInfo)` on violation.

**O2-B2**: Implement `MessageInfo::encode(&self) -> u64` producing the bitfield
word that goes into register x1. Must match the Lean `encodeMsgInfo` function
exactly (bits 0–6: length, bits 7–8: extra_caps, bits 9+: label).

**O2-B3**: Implement `MessageInfo::decode(raw: u64) -> KernelResult<Self>` for
parsing the kernel's response. Must match `decodeMsgInfo` semantics: extract
length (bits 0–6), validate ≤ 120; extract extra_caps (bits 7–8), validate ≤ 3;
extract label (bits 9+).

Add property test: `∀ mi, MessageInfo::decode(mi.encode()) == Ok(mi)` — this is
the Rust equivalent of `decodeMsgInfo_roundtrip`.

#### O2-C: Syscall Request/Response Encoding (4 subtasks)

**O2-C1**: Define `SyscallRequest` structure:

```rust
/// Mirrors `SyscallDecodeResult` (RegisterDecode.lean) but in encode direction.
pub struct SyscallRequest {
    pub cap_addr: CPtr,          // → x0
    pub msg_info: MessageInfo,   // → x1 (encoded as bitfield)
    pub msg_regs: [u64; 4],      // → x2, x3, x4, x5
    pub syscall_id: SyscallId,   // → x8
}
```

**O2-C2**: Implement `encode_syscall(req: &SyscallRequest) -> [u64; 7]` that
packs the request into the register array `[x0, x1, x2, x3, x4, x5, x8]`.
This is the inverse of `decodeSyscallArgs`.

**O2-C3**: Define `SyscallResponse` structure for parsing kernel return values:

```rust
pub struct SyscallResponse {
    pub error: Option<KernelError>,  // x0: 0 = success, nonzero = error code
    pub badge: Option<Badge>,         // x1: IPC badge (for receive/wait)
    pub msg_info: Option<MessageInfo>, // x1: message info (for receive)
    pub msg_regs: [u64; 4],           // x2–x5: message registers (receive path)
}
```

**O2-C4**: Implement `decode_response(regs: [u64; 7]) -> KernelResult<SyscallResponse>`
for parsing the kernel's register state after `svc` returns.

#### O2-D: SVC Trap (3 subtasks)

**O2-D1**: Implement `raw_syscall` in `rust/sele4n-abi/src/trap.rs`:

```rust
/// # Safety
/// Caller must ensure registers contain a valid syscall encoding.
/// This is the ONLY unsafe function in the entire libsele4n crate family.
#[inline(always)]
pub unsafe fn raw_syscall(regs: &mut [u64; 7]) {
    core::arch::asm!(
        "svc #0",
        inout("x0") regs[0],
        inout("x1") regs[1],
        inout("x2") regs[2],
        inout("x3") regs[3],
        inout("x4") regs[4],
        inout("x5") regs[5],
        in("x8") regs[6],
        // Clobbers: x6, x7 (caller-saved per AAPCS64)
        lateout("x6") _,
        lateout("x7") _,
    );
}
```

**O2-D2**: Implement safe wrapper `invoke_syscall(req: SyscallRequest) -> KernelResult<SyscallResponse>`:

```rust
/// Safe syscall invocation. Encodes request, traps to kernel, decodes response.
pub fn invoke_syscall(req: SyscallRequest) -> KernelResult<SyscallResponse> {
    let mut regs = encode_syscall(&req);
    // SAFETY: encode_syscall produces a valid register encoding that mirrors
    // the exact layout expected by decodeSyscallArgs in RegisterDecode.lean.
    unsafe { raw_syscall(&mut regs) };
    decode_response(regs)
}
```

This is the single point where `unsafe` is used, and it is wrapped in a safe
public API. All callers above this layer are fully safe Rust.

**O2-D3**: Add `#[cfg(not(target_arch = "aarch64"))]` mock implementation for
host-side testing that returns configurable responses. This enables the full
test suite to run on x86_64 development machines.

#### O2-E: Round-Trip Property Tests (2 subtasks)

**O2-E1**: Property tests for `MessageInfo`:
- `encode_decode_roundtrip`: `∀ mi (valid), decode(encode(mi)) == Ok(mi)`
- `decode_rejects_oversized_length`: length > 120 → error
- `decode_rejects_oversized_extra_caps`: extra_caps > 3 → error
- These mirror `decodeMsgInfo_roundtrip` from `RegisterDecode.lean:170`.

**O2-E2**: Property tests for `SyscallRequest` encoding:
- `encode_matches_lean_layout`: verify register positions match `SyscallRegisterLayout`
- `syscall_id_roundtrip`: `∀ id, TryFrom::try_from(id as u64) == Ok(id)`
- These mirror `decodeSyscallArgs_deterministic` from `RegisterDecode.lean:258`.

#### O2 Verification

- `cargo build --target aarch64-unknown-none` compiles (svc inline asm accepted)
- `cargo test --features std` passes all property tests on host
- Only `trap.rs` contains `unsafe`; crate-level `#[forbid(unsafe_code)]` with
  module-level override verified
- Encoding constants match Lean `SyscallRegisterLayout` field by field

---

### Phase 3: Per-Syscall Argument Structures (WS-O3)

**Focus**: Define typed argument structures for each syscall and their encoding
into message registers, mirroring `SyscallArgDecode.lean`.

**Priority**: HIGH — required before any high-level syscall wrapper can be built.
**Target version**: v0.17.3
**Files created**: `rust/sele4n-abi/src/args.rs`,
`rust/sele4n-abi/src/args/cspace.rs`, `rust/sele4n-abi/src/args/lifecycle.rs`,
`rust/sele4n-abi/src/args/vspace.rs`
**Lean files referenced** (read-only): `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`

#### O3-A: CSpace Argument Structures (4 subtasks)

**O3-A1**: Define `CSpaceMintArgs` matching `SyscallArgDecode.lean:30–46`:

```rust
/// Lean: `structure CSpaceMintArgs` (SyscallArgDecode.lean:30)
/// Requires 4 message registers (x2–x5).
pub struct CSpaceMintArgs {
    pub src_slot: Slot,          // x2
    pub dst_slot: Slot,          // x3
    pub rights: AccessRights,    // x4
    pub badge: Badge,            // x5
}
```

Implement `encode(&self) -> [u64; 4]` producing the message register array.
Implement `decode(regs: &[u64]) -> KernelResult<Self>` matching
`decodeCSpaceMintArgs` (requires `regs.len() >= 4`).

**O3-A2**: Define `CSpaceCopyArgs` (2 registers: src_slot, dst_slot),
`CSpaceMoveArgs` (2 registers: src_slot, dst_slot), and `CSpaceDeleteArgs`
(1 register: target_slot). Each gets `encode`/`decode` pair.

Source: `decodeCSpaceCopyArgs` (line 61), `decodeCSpaceMoveArgs` (line 80),
`decodeCSpaceDeleteArgs` (line 99).

**O3-A3**: Define the `ExtraCapAddrs` type for IPC capability transfer:

```rust
/// Lean: `decodeExtraCapAddrs` (SyscallArgDecode.lean:220)
/// Extracted from msgRegs[length..length+extraCaps].
pub struct ExtraCapAddrs {
    addrs: [CPtr; 3],  // max 3 extra caps (seL4_MsgMaxExtraCaps)
    count: u8,          // actual count (0..=3)
}
```

Implement `encode` that writes capability addresses into the message register
positions after the message body, matching `decodeExtraCapAddrs` semantics.
Out-of-bounds indices are silently dropped per seL4 convention.

**O3-A4**: Round-trip tests for all CSpace argument types:
- `mint_args_roundtrip`: `∀ args, decode(encode(args)) == Ok(args)`
- `copy_args_roundtrip`, `move_args_roundtrip`, `delete_args_roundtrip`
- Error-exclusivity tests: `decode` fails iff insufficient registers
  (matching `decodeCSpaceMintArgs_error_iff` etc.)

#### O3-B: Lifecycle & VSpace Argument Structures (3 subtasks)

**O3-B1**: Define `LifecycleRetypeArgs` matching `SyscallArgDecode.lean:118–133`:

```rust
/// Lean: `structure LifecycleRetypeArgs` (SyscallArgDecode.lean:118)
/// Requires 3 message registers (x2–x4).
pub struct LifecycleRetypeArgs {
    pub target_obj: ObjId,    // x2
    pub type_tag: TypeTag,    // x3 (validated: 0–5)
    pub size_hint: u64,       // x4
}
```

Define `TypeTag` enum matching `objectOfTypeTag` in `API.lean`:
```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u64)]
pub enum TypeTag {
    Tcb = 0,
    Endpoint = 1,
    Notification = 2,
    CNode = 3,
    VSpaceRoot = 4,
    Untyped = 5,
}
```

`TryFrom<u64>` returns `Err(KernelError::InvalidTypeTag)` for values > 5.

**O3-B2**: Define `VSpaceMapArgs` (4 registers: asid, vaddr, paddr, perms)
and `VSpaceUnmapArgs` (2 registers: asid, vaddr):

```rust
/// Lean: `structure VSpaceMapArgs` (SyscallArgDecode.lean:151)
pub struct VSpaceMapArgs {
    pub asid: Asid,           // x2
    pub vaddr: VAddr,         // x3
    pub paddr: PAddr,         // x4
    pub perms: PagePerms,     // x5 (bitmask)
}

/// Lean: `structure VSpaceUnmapArgs` (SyscallArgDecode.lean:181)
pub struct VSpaceUnmapArgs {
    pub asid: Asid,           // x2
    pub vaddr: VAddr,         // x3
}
```

Define `PagePerms` bitmask:
```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PagePerms(u8);
impl PagePerms {
    pub const READ: Self = Self(1 << 0);
    pub const WRITE: Self = Self(1 << 1);
    pub const EXECUTE: Self = Self(1 << 2);
    pub const USER: Self = Self(1 << 3);
    pub const CACHEABLE: Self = Self(1 << 4);
}
```

**O3-B3**: Round-trip and validation tests:
- `retype_args_roundtrip`, `vspace_map_args_roundtrip`, `vspace_unmap_args_roundtrip`
- `retype_rejects_invalid_type_tag`: tags > 5 → `InvalidTypeTag`
- `vspace_map_rejects_wx`: `WRITE | EXECUTE` combination → `AddressOutOfBounds`
  (W^X enforcement at encoding layer as defense-in-depth; kernel also checks)

#### O3-C: Argument Encoding Integration (3 subtasks)

**O3-C1**: Implement `SyscallRequest::for_cspace_mint(cap: CPtr, args: CSpaceMintArgs) -> Self`
and equivalent constructors for all 13 syscall types. Each constructor:
- Sets the correct `SyscallId`
- Encodes arguments into the `msg_regs` array
- Constructs the appropriate `MessageInfo` (length based on arg count)

**O3-C2**: Implement `SyscallRequest::msg_reg_count(id: SyscallId) -> u8` returning
the expected message register count for each syscall (matching the `requireMsgReg`
validation in `SyscallArgDecode.lean`):

| Syscall | Msg Regs |
|---------|----------|
| Send, Receive, Call, Reply | 0 (payload in IPC buffer) |
| CSpaceMint | 4 |
| CSpaceCopy, CSpaceMove | 2 |
| CSpaceDelete | 1 |
| LifecycleRetype | 3 |
| VSpaceMap | 4 |
| VSpaceUnmap | 2 |
| ServiceStart, ServiceStop | 0 |

**O3-C3**: Integration test: construct every syscall type, encode to registers,
verify register count and positions match the Lean `SyscallRegisterLayout`.

#### O3 Verification

- All argument types compile on `aarch64-unknown-none`
- Round-trip property tests pass for all 7 argument structures
- Error-exclusivity tests match Lean `_error_iff` theorems
- TypeTag validation matches `objectOfTypeTag` domain
- W^X check present in `VSpaceMapArgs` construction

---

### Phase 4: IPC Syscall Wrappers (WS-O4)

**Focus**: Build safe, high-level wrappers for IPC operations (send, receive,
call, reply, notification signal/wait) in the `sele4n-sys` crate.

**Priority**: MEDIUM — IPC is the most-used syscall family in a microkernel.
**Target version**: v0.17.4
**Files created**: `rust/sele4n-sys/Cargo.toml`, `rust/sele4n-sys/src/lib.rs`,
`rust/sele4n-sys/src/ipc.rs`, `rust/sele4n-sys/src/ipc/message.rs`,
`rust/sele4n-sys/src/ipc/endpoint.rs`, `rust/sele4n-sys/src/ipc/notification.rs`
**Lean files referenced** (read-only): `SeLe4n/Kernel/API.lean` (lines 390–524),
`SeLe4n/Kernel/IPC/Operations/Endpoint.lean`

#### O4-A: Crate Scaffold & IPC Message Builder (3 subtasks)

**O4-A1**: Create `rust/sele4n-sys/Cargo.toml` depending on `sele4n-types` and
`sele4n-abi`. `#![no_std]`, `#![deny(unsafe_code)]` (this crate is fully safe).

**O4-A2**: Implement `IpcMessage` builder in `rust/sele4n-sys/src/ipc/message.rs`:

```rust
/// Safe IPC message builder with compile-time and runtime bounds checking.
/// Lean: `structure IpcMessage` (Model/Object/Types.lean)
pub struct IpcMessage {
    registers: [u64; MAX_MSG_REGS],  // max 120
    length: u8,
    extra_cap_addrs: [CPtr; 3],      // max 3 extra capabilities
    extra_cap_count: u8,
    label: u64,
}

impl IpcMessage {
    pub fn new() -> Self { ... }
    pub fn with_label(label: u64) -> Self { ... }
    pub fn push_reg(&mut self, val: u64) -> KernelResult<()> { ... }
    pub fn push_cap(&mut self, cap: CPtr) -> KernelResult<()> { ... }
    pub fn label(&self) -> u64 { ... }
    pub fn reg(&self, idx: usize) -> Option<u64> { ... }
    pub fn cap(&self, idx: usize) -> Option<CPtr> { ... }
    pub fn length(&self) -> u8 { ... }
    pub fn extra_caps(&self) -> u8 { ... }
}
```

`push_reg` returns `IpcMessageTooLarge` if length would exceed 120.
`push_cap` returns `IpcMessageTooManyCaps` if count would exceed 3.
These match the bounds checks in `endpointSendDualChecked`
(`Enforcement/Wrappers.lean:29–31`).

**O4-A3**: Implement `IpcMessage::to_syscall_request` and
`IpcMessage::from_syscall_response` for converting between the high-level
message type and the low-level register encoding. Message registers are
packed into msg_regs[0..3] for inline transfer; longer messages use the
IPC buffer (address obtained from `ThreadId` context).

#### O4-B: Endpoint Wrappers (5 subtasks)

**O4-B1**: Implement `endpoint_send`:

```rust
/// Send a message to an endpoint. Blocks if no receiver is waiting.
/// Lean: `apiEndpointSend` (API.lean:240)
/// Required right: Write on endpoint capability.
pub fn endpoint_send(ep: CPtr, msg: &IpcMessage) -> KernelResult<()> {
    let req = SyscallRequest::for_send(ep, msg);
    let resp = invoke_syscall(req)?;
    // Send returns no payload on success
    Ok(())
}
```

**O4-B2**: Implement `endpoint_receive`:

```rust
/// Receive a message from an endpoint. Blocks if no sender is waiting.
/// Lean: `apiEndpointReceive` (API.lean:254)
/// Required right: Read on endpoint capability.
/// Returns: received message with sender badge.
pub fn endpoint_receive(ep: CPtr) -> KernelResult<(IpcMessage, Option<Badge>)> {
    let req = SyscallRequest::for_receive(ep);
    let resp = invoke_syscall(req)?;
    let msg = IpcMessage::from_syscall_response(&resp)?;
    Ok((msg, resp.badge))
}
```

**O4-B3**: Implement `endpoint_call`:

```rust
/// Combined send-then-receive (RPC pattern). Creates one-shot reply cap.
/// Lean: `apiEndpointCall` (API.lean:268)
/// Required right: Write on endpoint capability.
/// Returns: reply message with server badge.
pub fn endpoint_call(ep: CPtr, msg: &IpcMessage) -> KernelResult<(IpcMessage, Option<Badge>)> {
    let req = SyscallRequest::for_call(ep, msg);
    let resp = invoke_syscall(req)?;
    let reply = IpcMessage::from_syscall_response(&resp)?;
    Ok((reply, resp.badge))
}
```

**O4-B4**: Implement `endpoint_reply`:

```rust
/// Reply to a caller (consumes one-shot reply cap).
/// Lean: `apiEndpointReply` (API.lean:282)
/// Required right: Write on reply capability.
pub fn endpoint_reply(reply_cap: CPtr, msg: &IpcMessage) -> KernelResult<()> {
    let req = SyscallRequest::for_reply(reply_cap, msg);
    invoke_syscall(req)?;
    Ok(())
}
```

**O4-B5**: Implement `endpoint_reply_receive` (combined reply+receive for
server loops — maps to `ReplyRecv` in seL4):

```rust
/// Reply to current caller then immediately wait for next message.
/// This is the standard server loop operation (seL4_ReplyRecv pattern).
/// Lean: dispatches to apiEndpointReply then apiEndpointReceive atomically.
pub fn endpoint_reply_receive(
    ep: CPtr,
    reply_cap: CPtr,
    reply_msg: &IpcMessage,
) -> KernelResult<(IpcMessage, Option<Badge>)> {
    // Implementation: sequential reply then receive at the wrapper level.
    // Kernel atomicity for ReplyRecv is maintained by the Lean dispatch path.
    endpoint_reply(reply_cap, reply_msg)?;
    endpoint_receive(ep)
}
```

#### O4-C: Notification Wrappers (2 subtasks)

**O4-C1**: Implement `notification_signal`:

```rust
/// Signal a notification object (bitwise-OR badge accumulation).
/// Lean: `notificationSignal` (IPC/Operations/Endpoint.lean)
/// The badge is OR'd into the notification's pending badge (Badge.bor).
pub fn notification_signal(ntfn: CPtr, badge: Badge) -> KernelResult<()> {
    let req = SyscallRequest::for_send(ntfn, &IpcMessage::with_badge(badge));
    invoke_syscall(req)?;
    Ok(())
}
```

**O4-C2**: Implement `notification_wait`:

```rust
/// Wait for a notification. Returns accumulated badge on wakeup.
/// Lean: `notificationWait` (IPC/Operations/Endpoint.lean)
pub fn notification_wait(ntfn: CPtr) -> KernelResult<Badge> {
    let req = SyscallRequest::for_receive(ntfn);
    let resp = invoke_syscall(req)?;
    Ok(resp.badge.unwrap_or(Badge(0)))
}
```

#### O4-D: Tests (2 subtasks)

**O4-D1**: Unit tests for `IpcMessage` builder:
- Bounds enforcement: 121st register push → `IpcMessageTooLarge`
- Bounds enforcement: 4th cap push → `IpcMessageTooManyCaps`
- Round-trip: build message → encode → decode → compare

**O4-D2**: Integration tests for endpoint wrappers (using mock trap):
- Send/receive rendezvous (mock kernel delivers message)
- Call/reply round-trip (mock kernel echoes message)
- Notification signal/wait badge accumulation

#### O4 Verification

- All IPC wrappers compile on `aarch64-unknown-none`
- Zero `unsafe` in `sele4n-sys` crate
- Message bounds match Lean constants (120 regs, 3 caps)
- Badge accumulation uses bitwise OR matching `Badge.bor`

---

### Phase 5: CSpace Syscall Wrappers (WS-O5)

**Focus**: Build safe wrappers for CSpace (capability space) operations:
mint, copy, move, delete.

**Priority**: MEDIUM — CSpace ops are the capability management API.
**Target version**: v0.17.5
**Files created**: `rust/sele4n-sys/src/cspace.rs`
**Lean files referenced** (read-only): `SeLe4n/Kernel/API.lean` (lines 292–312),
`SeLe4n/Kernel/Capability/Operations.lean`

#### O5-A: CSpace Address Types (2 subtasks)

**O5-A1**: Define `CSpaceAddr` for identifying a slot within a CNode:

```rust
/// A fully-resolved CSpace address: CNode object + slot index.
/// Lean: `structure CSpaceAddr` (Capability/Operations.lean)
pub struct CSpaceAddr {
    pub cnode: CPtr,   // Capability pointing to the CNode
    pub slot: Slot,    // Slot within the CNode
}
```

**O5-A2**: Define `CSpacePath` for multi-level resolution addresses:

```rust
/// Multi-level CSpace path for deep CNode hierarchies.
/// Used when the target slot is in a nested CNode.
pub struct CSpacePath {
    pub root: CPtr,     // Root CNode capability
    pub path: CPtr,     // Path bits for guard/radix traversal
    pub depth: u8,      // Resolution depth (bits to consume)
}
```

#### O5-B: CSpace Operation Wrappers (4 subtasks)

**O5-B1**: Implement `cspace_mint`:

```rust
/// Mint a new capability with reduced rights and/or badge.
/// Lean: `apiCspaceMint` (API.lean:292)
/// Required right: Grant on source capability.
///
/// Creates a derived capability in dst with rights ⊆ source rights and
/// an optional badge for IPC identification.
pub fn cspace_mint(
    authority: CPtr,
    src_slot: Slot,
    dst_slot: Slot,
    rights: AccessRights,
    badge: Badge,
) -> KernelResult<()> {
    let args = CSpaceMintArgs { src_slot, dst_slot, rights, badge };
    let req = SyscallRequest::for_cspace_mint(authority, args);
    invoke_syscall(req)?;
    Ok(())
}
```

**O5-B2**: Implement `cspace_copy`:

```rust
/// Copy a capability to a new slot (same rights, no badge change).
/// Lean: `apiCspaceCopy` (API.lean:298)
/// Required right: Grant on source capability.
pub fn cspace_copy(
    authority: CPtr,
    src_slot: Slot,
    dst_slot: Slot,
) -> KernelResult<()> {
    let args = CSpaceCopyArgs { src_slot, dst_slot };
    let req = SyscallRequest::for_cspace_copy(authority, args);
    invoke_syscall(req)?;
    Ok(())
}
```

**O5-B3**: Implement `cspace_move`:

```rust
/// Move a capability from one slot to another (source slot becomes empty).
/// Lean: `apiCspaceMove` (API.lean:304)
/// Required right: Grant on source capability.
pub fn cspace_move(
    authority: CPtr,
    src_slot: Slot,
    dst_slot: Slot,
) -> KernelResult<()> {
    let args = CSpaceMoveArgs { src_slot, dst_slot };
    let req = SyscallRequest::for_cspace_move(authority, args);
    invoke_syscall(req)?;
    Ok(())
}
```

**O5-B4**: Implement `cspace_delete`:

```rust
/// Delete a capability from a slot.
/// Lean: `apiCspaceDelete` (API.lean:310)
/// Required right: Write on CNode capability.
pub fn cspace_delete(authority: CPtr, target_slot: Slot) -> KernelResult<()> {
    let args = CSpaceDeleteArgs { target_slot };
    let req = SyscallRequest::for_cspace_delete(authority, args);
    invoke_syscall(req)?;
    Ok(())
}
```

#### O5-C: Compile-Time Rights Documentation (2 subtasks)

**O5-C1**: Add comprehensive doc comments to each wrapper documenting:
- The required access right (from `syscallRequiredRight`)
- What kernel error is returned if the right is absent (`IllegalAuthority`)
- The capability derivation semantics (for mint: rights ⊆ parent rights)
- Cross-reference to the Lean source (file:line)

**O5-C2**: Add `#[must_use]` attributes and `Result` return types to enforce
that callers handle potential errors. Document each `KernelError` variant that
can be returned by each operation.

#### O5-D: Tests (2 subtasks)

**O5-D1**: Unit tests for argument encoding:
- `CSpaceMintArgs` with various rights combinations
- `CSpaceCopyArgs`/`CSpaceMoveArgs` slot encoding
- `CSpaceDeleteArgs` single-register encoding

**O5-D2**: Integration tests (mock trap):
- Mint with reduced rights succeeds
- Mint with rights ⊄ source rights → `IllegalAuthority`
- Delete of empty slot → `InvalidCapability`
- Move then access old slot → `InvalidCapability`

#### O5 Verification

- All CSpace wrappers compile on `aarch64-unknown-none`
- Argument encoding matches Lean `decodeCSpace*Args` expectations
- Doc comments reference correct Lean source locations
- `#[must_use]` on all `KernelResult` returns

---

### Phase 6: Lifecycle, VSpace & Service Wrappers (WS-O6)

**Focus**: Complete the syscall wrapper surface with lifecycle (retype),
VSpace (map/unmap), and service (start/stop) operations.

**Priority**: MEDIUM — completes the full 13-syscall coverage.
**Target version**: v0.17.6
**Files created**: `rust/sele4n-sys/src/lifecycle.rs`,
`rust/sele4n-sys/src/vspace.rs`, `rust/sele4n-sys/src/service.rs`
**Lean files referenced** (read-only): `SeLe4n/Kernel/API.lean` (lines 420–524),
`SeLe4n/Kernel/Lifecycle/Operations.lean`,
`SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`

#### O6-A: Lifecycle Retype Wrapper (3 subtasks)

**O6-A1**: Implement `lifecycle_retype`:

```rust
/// Retype an untyped memory object into a specific kernel object type.
/// Lean: `apiLifecycleRetype` (API.lean:420)
/// Required right: Retype on authority capability.
///
/// # Type Tags
/// - `Tcb` (0): Thread Control Block
/// - `Endpoint` (1): IPC endpoint
/// - `Notification` (2): Notification object
/// - `CNode` (3): Capability node (size_hint = radix bits)
/// - `VSpaceRoot` (4): Virtual address space root
/// - `Untyped` (5): Sub-untyped region (size_hint = region size)
///
/// # Errors
/// - `InvalidTypeTag`: type_tag not in 0–5
/// - `IllegalAuthority`: caller lacks Retype right
/// - `IllegalState`: target already typed (not untyped)
pub fn lifecycle_retype(
    authority: CPtr,
    target: ObjId,
    type_tag: TypeTag,
    size_hint: u64,
) -> KernelResult<()> {
    let args = LifecycleRetypeArgs { target_obj: target, type_tag, size_hint };
    let req = SyscallRequest::for_lifecycle_retype(authority, args);
    invoke_syscall(req)?;
    Ok(())
}
```

**O6-A2**: Define convenience constructors for common retype patterns:

```rust
/// Retype untyped memory into a new TCB.
pub fn retype_tcb(authority: CPtr, target: ObjId) -> KernelResult<()> {
    lifecycle_retype(authority, target, TypeTag::Tcb, 0)
}

/// Retype untyped memory into a CNode with given radix width.
pub fn retype_cnode(authority: CPtr, target: ObjId, radix_bits: u64) -> KernelResult<()> {
    lifecycle_retype(authority, target, TypeTag::CNode, radix_bits)
}

// ... retype_endpoint, retype_notification, retype_vspace_root, retype_untyped
```

**O6-A3**: Tests for lifecycle wrapper:
- Valid retype of each TypeTag succeeds (mock)
- Invalid TypeTag (6+) → `InvalidTypeTag` at encode time (never reaches kernel)
- Missing Retype right → `IllegalAuthority`

#### O6-B: VSpace Wrappers (4 subtasks)

**O6-B1**: Implement `vspace_map`:

```rust
/// Map a physical page into a virtual address space.
/// Lean: `apiVspaceMap` → `vspaceMapPageChecked` (API.lean:470)
/// Required right: Write on VSpace capability.
///
/// # W^X Enforcement
/// The kernel enforces W^X (Write XOR Execute): a page cannot be both
/// writable and executable. This wrapper performs a client-side pre-check
/// as defense-in-depth; the kernel independently enforces this invariant
/// (`wxExclusiveInvariant` in VSpaceInvariant.lean).
///
/// # Address Bounds
/// Physical addresses must fit within the platform's physical address width
/// (44-bit for RPi5, 52-bit for model). Violations return `AddressOutOfBounds`.
pub fn vspace_map(
    authority: CPtr,
    asid: Asid,
    vaddr: VAddr,
    paddr: PAddr,
    perms: PagePerms,
) -> KernelResult<()> {
    // Client-side W^X pre-check (defense in depth)
    if perms.contains(PagePerms::WRITE) && perms.contains(PagePerms::EXECUTE) {
        return Err(KernelError::AddressOutOfBounds);
    }
    let args = VSpaceMapArgs { asid, vaddr, paddr, perms };
    let req = SyscallRequest::for_vspace_map(authority, args);
    invoke_syscall(req)?;
    Ok(())
}
```

**O6-B2**: Implement `vspace_unmap`:

```rust
/// Unmap a virtual page from an address space.
/// Lean: `apiVspaceUnmap` → `Architecture.vspaceUnmapPage` (API.lean:500)
/// Required right: Write on VSpace capability.
pub fn vspace_unmap(
    authority: CPtr,
    asid: Asid,
    vaddr: VAddr,
) -> KernelResult<()> {
    let args = VSpaceUnmapArgs { asid, vaddr };
    let req = SyscallRequest::for_vspace_unmap(authority, args);
    invoke_syscall(req)?;
    Ok(())
}
```

**O6-B3**: Define `PagePerms` builder with W^X enforcement:

```rust
impl PagePerms {
    /// Create read-only permissions.
    pub const fn read_only() -> Self { Self(Self::READ.0 | Self::CACHEABLE.0) }

    /// Create read-write permissions (no execute — W^X safe).
    pub const fn read_write() -> Self { Self(Self::READ.0 | Self::WRITE.0 | Self::CACHEABLE.0) }

    /// Create read-execute permissions (no write — W^X safe).
    pub const fn read_execute() -> Self { Self(Self::READ.0 | Self::EXECUTE.0 | Self::CACHEABLE.0) }

    /// User-accessible variant of any permission set.
    pub const fn user(self) -> Self { Self(self.0 | Self::USER.0) }
}
```

No `read_write_execute()` constructor exists — W^X is enforced by API design.

**O6-B4**: Tests:
- Map with W^X-safe perms succeeds
- Map with WRITE+EXECUTE → `AddressOutOfBounds` (client-side pre-check)
- Unmap of mapped page succeeds
- Map of already-mapped vaddr → appropriate kernel error

#### O6-C: Service Wrappers (3 subtasks)

**O6-C1**: Implement `service_start` and `service_stop`:

```rust
/// Start a service (gated by serviceConfig.allowStart policy).
/// Lean: `apiServiceStart` (API.lean:510)
/// Required right: Write on service capability.
pub fn service_start(authority: CPtr) -> KernelResult<()> {
    let req = SyscallRequest::for_service_start(authority);
    invoke_syscall(req)?;
    Ok(())
}

/// Stop a service (gated by serviceConfig.allowStop policy).
/// Lean: `apiServiceStop` (API.lean:520)
/// Required right: Write on service capability.
pub fn service_stop(authority: CPtr) -> KernelResult<()> {
    let req = SyscallRequest::for_service_stop(authority);
    invoke_syscall(req)?;
    Ok(())
}
```

**O6-C2**: Document that service start/stop are policy-gated: the kernel's
`ServiceConfig` determines whether each operation is permitted. These wrappers
have no client-side policy checks — all enforcement is kernel-side.

**O6-C3**: Tests:
- Service start/stop with permitted policy → success
- Service start with denied policy → kernel error

#### O6 Verification

- Full 13-syscall coverage achieved (all `SyscallId` variants have wrappers)
- W^X enforcement present in both `PagePerms` API design and `vspace_map` pre-check
- `TypeTag` exhaustively covers all 6 Lean object types
- Zero unsafe in `sele4n-sys`

---

### Phase 7: Type-Safe Capability Handles (WS-O7)

**Focus**: Add phantom-typed capability handles that encode object type and
access rights at the Rust type level, enabling compile-time verification of
capability usage.

**Priority**: LOW — ergonomic improvement over raw `CPtr`, not required for
correctness (runtime checks still present).
**Target version**: v0.17.7
**Files created**: `rust/sele4n-sys/src/cap.rs`, `rust/sele4n-sys/src/cap/rights.rs`,
`rust/sele4n-sys/src/cap/objects.rs`
**Lean files referenced** (read-only): `SeLe4n/Model/Object/Types.lean` (Capability,
CapTarget, AccessRight)

#### O7-A: Marker Types & Sealed Traits (3 subtasks)

**O7-A1**: Define marker types for kernel object kinds:

```rust
/// Marker types for kernel object kinds (zero-sized, no runtime cost).
pub mod obj {
    pub struct Endpoint;
    pub struct Notification;
    pub struct CNode;
    pub struct Tcb;
    pub struct VSpaceRoot;
    pub struct Untyped;
}
```

**O7-A2**: Define marker types for access right combinations:

```rust
/// Sealed trait for compile-time access right verification.
pub trait Rights: private::Sealed {
    const RIGHTS: AccessRights;
}

/// Marker: capability with Read right.
pub struct R;
impl Rights for R { const RIGHTS: AccessRights = AccessRights::READ; }

/// Marker: capability with Write right.
pub struct W;
impl Rights for W { const RIGHTS: AccessRights = AccessRights::WRITE; }

/// Marker: capability with Read + Write rights.
pub struct RW;
impl Rights for RW {
    const RIGHTS: AccessRights = AccessRights(AccessRights::READ.0 | AccessRights::WRITE.0);
}

/// Marker: capability with Grant right.
pub struct G;
impl Rights for G { const RIGHTS: AccessRights = AccessRights::GRANT; }

/// Marker: full rights.
pub struct Full;
impl Rights for Full { const RIGHTS: AccessRights = AccessRights::ALL; }
```

**O7-A3**: Use a sealed trait pattern to prevent external implementations:

```rust
mod private {
    pub trait Sealed {}
    impl Sealed for super::R {}
    impl Sealed for super::W {}
    impl Sealed for super::RW {}
    impl Sealed for super::G {}
    impl Sealed for super::Full {}
}
```

#### O7-B: Cap<Obj, Rights> Handle (4 subtasks)

**O7-B1**: Define the phantom-typed capability handle:

```rust
/// A capability handle with compile-time object type and rights verification.
///
/// `Cap<Endpoint, W>` is a write-capable endpoint capability.
/// `Cap<CNode, G>` is a grant-capable CNode capability.
///
/// The inner CPtr is the runtime capability address. Phantom types provide
/// compile-time enforcement that the correct rights are available for each
/// operation. The kernel still performs runtime checks.
#[derive(Clone, Copy)]
pub struct Cap<Obj, Rts: Rights> {
    ptr: CPtr,
    _obj: core::marker::PhantomData<Obj>,
    _rights: core::marker::PhantomData<Rts>,
}

impl<Obj, Rts: Rights> Cap<Obj, Rts> {
    /// Create a capability handle from a raw CPtr.
    /// # Safety contract (logical, not memory):
    /// Caller asserts that the CPtr refers to an object of type `Obj`
    /// with at least the rights encoded in `Rts`.
    pub const fn from_raw(ptr: CPtr) -> Self { ... }

    /// Get the raw CPtr.
    pub const fn raw(&self) -> CPtr { self.ptr }
}
```

**O7-B2**: Implement typed endpoint operations:

```rust
impl<Rts: Rights> Cap<obj::Endpoint, Rts> {
    /// Send requires Write right — only available on Cap<Endpoint, W> or Cap<Endpoint, RW>.
    pub fn send(&self, msg: &IpcMessage) -> KernelResult<()>
    where Rts: HasWrite  // compile-time Write right requirement
    {
        endpoint_send(self.ptr, msg)
    }

    /// Receive requires Read right.
    pub fn receive(&self) -> KernelResult<(IpcMessage, Option<Badge>)>
    where Rts: HasRead
    {
        endpoint_receive(self.ptr)
    }

    /// Call requires Write right.
    pub fn call(&self, msg: &IpcMessage) -> KernelResult<(IpcMessage, Option<Badge>)>
    where Rts: HasWrite
    {
        endpoint_call(self.ptr, msg)
    }
}
```

Where `HasWrite` and `HasRead` are sealed marker traits implemented only for
right combinations that include the required right.

**O7-B3**: Implement typed CSpace operations:

```rust
impl<Rts: Rights> Cap<obj::CNode, Rts> {
    /// Mint requires Grant right.
    pub fn mint(&self, src: Slot, dst: Slot, rights: AccessRights, badge: Badge)
        -> KernelResult<()>
    where Rts: HasGrant
    {
        cspace_mint(self.ptr, src, dst, rights, badge)
    }

    /// Delete requires Write right.
    pub fn delete(&self, slot: Slot) -> KernelResult<()>
    where Rts: HasWrite
    {
        cspace_delete(self.ptr, slot)
    }
}
```

**O7-B4**: Implement rights downgrading (matching Lean `mintDerivedCap`):

```rust
impl<Obj, Rts: Rights> Cap<Obj, Rts> {
    /// Downgrade rights to a subset. This is a compile-time operation.
    /// Lean: `mintDerivedCap` rights attenuation (Capability/Operations.lean)
    pub fn downgrade<NewRts: Rights>(self) -> Cap<Obj, NewRts>
    where NewRts: SubsetOf<Rts>  // compile-time subset verification
    {
        Cap::from_raw(self.ptr)
    }
}
```

#### O7-C: Ergonomic Helpers (4 subtasks)

**O7-C1**: Implement a capability table builder for initialization:

```rust
/// Helper for building an initial CSpace layout during process setup.
pub struct CSpaceBuilder {
    root: Cap<obj::CNode, Full>,
    next_slot: Slot,
}

impl CSpaceBuilder {
    pub fn new(root: Cap<obj::CNode, Full>) -> Self { ... }
    pub fn alloc_slot(&mut self) -> Slot { ... }
    pub fn mint_endpoint(&mut self, src: Slot, rights: AccessRights)
        -> KernelResult<Cap<obj::Endpoint, W>> { ... }
    // ... other typed mint helpers
}
```

**O7-C2**: Implement `Display` and `Debug` for `Cap` that shows the object type
and rights without exposing the raw CPtr (security-conscious formatting):

```rust
impl<Obj: ObjName, Rts: Rights> core::fmt::Debug for Cap<Obj, Rts> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "Cap<{}, {:?}>", Obj::NAME, Rts::RIGHTS)
    }
}
```

**O7-C3**: Implement `From<Cap<Obj, Full>>` conversions for common downgrade
patterns (Full → W, Full → R, Full → G) so users can pass full-rights
capabilities to functions expecting reduced rights.

**O7-C4**: Comprehensive tests:
- Compile-time right verification: `Cap<Endpoint, R>::send()` should fail to compile
- Downgrading from Full to W succeeds
- CSpaceBuilder allocates sequential slots
- Display format shows type and rights

#### O7 Verification

- All phantom type operations are zero-cost (verify via `size_of::<Cap<_, _>>() == 8`)
- Compile-fail tests for wrong-rights usage (use `trybuild` crate)
- Downgrade preserves raw CPtr
- No runtime overhead compared to raw `CPtr` wrappers

---

### Phase 8: Conformance Testing & Documentation (WS-O8)

**Focus**: Cross-validate Rust encoding against Lean decoding, integrate with
the existing test tier system, and complete documentation.

**Priority**: LOW — validation and polish phase.
**Target version**: v0.17.8
**Files created**: `rust/tests/conformance.rs`, `scripts/test_rust.sh`,
`docs/gitbook/15-rust-syscall-wrappers.md` (or next available chapter number)
**Lean files modified**: `SeLe4n/Testing/MainTraceHarness.lean` (extension),
`tests/fixtures/main_trace_smoke.expected` (extension)

#### O8-A: Lean Cross-Validation Harness (3 subtasks)

**O8-A1**: Extend `MainTraceHarness.lean` with a new trace function that outputs
encoding test vectors: for each syscall type, print the register values that
the Lean decoder expects for a canonical set of inputs. Format:

```
[RUST-XVAL-001] send|x0=42|x1=7|x2=100|x3=0|x4=0|x5=0|x8=0
[RUST-XVAL-002] receive|x0=42|x1=0|x8=1
...
```

**O8-A2**: Add corresponding fixture entries to `main_trace_smoke.expected`.

**O8-A3**: Create a Rust test (`rust/tests/conformance.rs`) that:
1. Reads the Lean trace output (from fixture or piped from `lake exe sele4n`)
2. For each test vector, encodes the same inputs using Rust functions
3. Asserts register-by-register equality between Lean and Rust encodings

This provides machine-verified ABI compatibility: if the Lean model changes
its register layout, the conformance tests will fail.

#### O8-B: CI Integration (3 subtasks)

**O8-B1**: Create `scripts/test_rust.sh` that:
- Installs Rust toolchain if not present (`rustup target add aarch64-unknown-none`)
- Runs `cargo build --target aarch64-unknown-none` (compile check)
- Runs `cargo test --features std` (unit + property tests)
- Runs `cargo test --test conformance --features std` (cross-validation)

**O8-B2**: Integrate `test_rust.sh` into the existing test tier system:
- Add to `test_smoke.sh` as a Tier 2 check (after Lean trace, before negative state)
- Add to `test_full.sh` as well
- The Rust tests should not block Tier 0/1 (hygiene/build) which remain Lean-only

**O8-B3**: Update `scripts/test_lib.sh` with Rust-specific color output
(e.g., `RUST` category) and Cargo availability check.

#### O8-C: Documentation (4 subtasks)

**O8-C1**: Create GitBook chapter `docs/gitbook/15-rust-syscall-wrappers.md` covering:
- Architectural overview (Lean semantics → Rust wrappers)
- Crate structure and dependency graph
- Usage examples for each syscall family (IPC, CSpace, Lifecycle, VSpace)
- Phantom-typed capability handles tutorial
- Cross-validation methodology

**O8-C2**: Update `docs/spec/SELE4N_SPEC.md` with Rust wrapper section:
- List all 13 syscall wrappers with Lean ↔ Rust signature correspondence
- Document the ABI contract (register layout, encoding, error codes)
- Reference the conformance test suite

**O8-C3**: Update `docs/DEVELOPMENT.md` with:
- Rust build instructions (`cargo build --target aarch64-unknown-none`)
- How to run Rust tests
- How to add new syscall wrappers (workflow guide)

**O8-C4**: Update `README.md` metrics to include Rust LoC count and crate
information. Update `docs/codebase_map.json` with Rust source files.

#### O8 Verification

- `test_smoke.sh` passes with Rust integration
- Cross-validation test produces register-by-register match for all 13 syscalls
- GitBook chapter renders correctly
- `codebase_map.json` includes Rust files
- README metrics are current

---

## 6. Cross-Cutting Concerns

### 6.1 Unsafe Code Audit Trail

The entire `libsele4n` Rust crate family contains exactly **one** `unsafe` block:
the `svc` inline assembly in `sele4n-abi/src/trap.rs`. This is auditable by
inspection and justified by the following argument:

1. The caller (`invoke_syscall`) passes registers produced by `encode_syscall`.
2. `encode_syscall` produces values that are structurally identical to what
   `decodeSyscallArgs` in `RegisterDecode.lean` expects.
3. The Lean decoder is total and deterministic — it either succeeds or returns
   a `KernelError`.
4. The `svc` instruction traps to EL1 where the Lean kernel's verified entry
   point processes the registers.
5. On return, registers contain the kernel's response (success/error + payload).

The safety argument is: **the ABI contract is verified in Lean, and the Rust
encoding is cross-validated against the Lean decoding via conformance tests**.

### 6.2 ABI Versioning

The register layout is defined by `SyscallRegisterLayout` in `RegisterDecode.lean`.
If the Lean model changes this layout (e.g., adding new registers or reordering),
the Rust encoding must be updated in lockstep. The conformance test suite (O8-A)
catches any drift automatically.

**Versioning strategy**: The `sele4n-abi` crate version tracks the Lean model
version. Breaking ABI changes require a major version bump in both.

### 6.3 no_std Constraints

All three crates are `#![no_std]` by default. This means:
- No heap allocation (`alloc` crate not used)
- `IpcMessage` uses fixed-size arrays, not `Vec`
- Error types are `Copy` (no `String` messages)
- Tests use `#[cfg(feature = "std")]` for property testing with `proptest`

The `std` feature is for host-side development only and must never be enabled
in the bare-metal target.

### 6.4 Dependency Policy

- `sele4n-types`: zero external dependencies (only `core`)
- `sele4n-abi`: depends only on `sele4n-types` (only `core`)
- `sele4n-sys`: depends only on `sele4n-types` + `sele4n-abi` (only `core`)
- Dev dependencies (test-only): `proptest`, `trybuild` (behind `std` feature)

No `alloc`, no `std`, no third-party runtime dependencies. This minimizes the
TCB (Trusted Computing Base) for the userspace syscall interface.

### 6.5 Relationship to H3 Hardware Binding

WS-O builds the **userspace** half of the syscall interface. The H3 workstream
will build the **kernel-side** half:

```
┌─────────────────────────────────────────────┐
│  User Space (EL0)                           │
│  ┌─────────────┐   ┌──────────────┐        │
│  │ sele4n-sys  │──▶│ sele4n-abi   │        │  ← WS-O (this workstream)
│  │ (safe API)  │   │ (encode+svc) │        │
│  └─────────────┘   └──────┬───────┘        │
│                           │ svc #0          │
├───────────────────────────┼─────────────────┤
│  Kernel (EL1)             ▼                 │
│  ┌──────────────────────────────────┐       │
│  │ Vector Table Entry               │       │  ← H3 (future)
│  │  → Save registers to TCB         │       │
│  │  → decodeSyscallArgs (Lean)      │       │
│  │  → dispatchSyscall (Lean)        │       │
│  │  → Store result registers        │       │
│  │  → eret                          │       │
│  └──────────────────────────────────┘       │
└─────────────────────────────────────────────┘
```

The `sele4n-abi` crate's encoding functions will be reused by H3's trap handler
for the decode direction. The `SyscallRequest`/`SyscallResponse` types serve as
the shared ABI contract between userspace and kernel.

### 6.6 Error Handling Philosophy

seLe4n's Lean kernel returns errors via `Except KernelError` — a tagged union
where every failure mode is enumerated and every success path is explicit. The
Rust wrappers mirror this exactly with `Result<T, KernelError>`.

**Key principles**:
- No panics in library code (`#![deny(clippy::panic)]`)
- No unwinding (bare-metal target, `panic = "abort"` in Cargo profile)
- Every `KernelError` variant maps to a documented recovery strategy
- `#[must_use]` on all `KernelResult` returns prevents silent error ignoring

### 6.7 Thread Safety

The syscall wrappers are inherently thread-safe because:
1. Each `svc` invocation is atomic from the caller's perspective
2. The kernel serializes all syscalls (single-threaded kernel model)
3. No shared mutable state exists in the Rust library (all functions are pure
   transformations on arguments → registers → results)

`IpcMessage` is `Send + Sync` because it contains only `Copy` types.
`Cap<Obj, Rts>` is `Send + Sync + Copy` because it's just a `CPtr` wrapper.

---

## 7. Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Lean ABI changes break Rust encoding | LOW | HIGH | Conformance test suite (O8-A) catches drift automatically |
| `svc` inline assembly incorrect on specific ARM64 variants | LOW | HIGH | Test on RPi5 hardware; review AAPCS64 calling convention |
| Phantom type system too restrictive for some use cases | MEDIUM | LOW | Provide `Cap::from_raw` escape hatch for advanced users |
| no_std constraint prevents useful testing patterns | LOW | MEDIUM | `std` feature gate for host-side testing; mock trap for CI |
| Register clobber list incomplete in `raw_syscall` | LOW | HIGH | Audit against ARM64 SVC convention; add x6/x7 clobbers |
| Cross-validation test coverage insufficient | MEDIUM | MEDIUM | Cover all 13 syscalls × error paths in conformance suite |

---

## 8. Dependency Graph & Ordering

```
O1 (types) ──────────────────────────────────────────────┐
  │                                                       │
  ▼                                                       │
O2 (ABI) ──────────────────────────────────┐              │
  │                                         │              │
  ▼                                         │              │
O3 (args) ─────────────┐                   │              │
  │                     │                   │              │
  ▼                     ▼                   ▼              ▼
O4 (IPC)    O5 (CSpace)    O6 (Lifecycle)   O7 (Phantom)
  │              │              │              │
  └──────────────┴──────────────┴──────────────┘
                        │
                        ▼
                   O8 (Testing + Docs)
```

- **O1 → O2 → O3**: strictly sequential (each builds on the prior)
- **O4, O5, O6**: parallelizable (independent syscall families, all depend on O3)
- **O7**: depends on O4+O5+O6 (wraps their types in phantom handles)
- **O8**: depends on all prior phases (integration testing)

---

## 9. Success Criteria

The WS-O workstream is complete when:

1. All 13 seLe4n syscalls have safe Rust wrappers in `sele4n-sys`
2. `cargo build --target aarch64-unknown-none` compiles all three crates
3. `cargo test --features std` passes all unit, property, and conformance tests
4. Cross-validation confirms register-by-register ABI match with Lean decoding
5. Exactly one `unsafe` block exists (the `svc` trap in `sele4n-abi`)
6. Phantom-typed capability handles prevent wrong-rights usage at compile time
7. All documentation updated (GitBook, spec, development guide, README)
8. Test tier integration passes (`test_smoke.sh` includes Rust checks)
9. Zero `sorry`/`axiom` introduced in Lean proof surface
10. No existing Lean test regressions

---

## 10. Files Created Summary

### Rust Workspace (`rust/`)

```
rust/
├── Cargo.toml                          # Workspace manifest
├── sele4n-types/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs                      # Crate root, #![no_std]
│       ├── identifiers.rs             # ObjId, ThreadId, CPtr, Slot, ...
│       ├── error.rs                    # KernelError, KernelResult
│       ├── rights.rs                   # AccessRight, AccessRights
│       └── syscall.rs                  # SyscallId, TypeTag, PagePerms
├── sele4n-abi/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs                      # Crate root
│       ├── message_info.rs            # MessageInfo bitfield encode/decode
│       ├── encode.rs                   # SyscallRequest encoding
│       ├── decode.rs                   # SyscallResponse decoding
│       ├── trap.rs                     # raw_syscall (svc #0) — ONLY unsafe
│       └── args/
│           ├── mod.rs                  # Argument module root
│           ├── cspace.rs              # CSpaceMint/Copy/Move/DeleteArgs
│           ├── lifecycle.rs           # LifecycleRetypeArgs
│           └── vspace.rs              # VSpaceMap/UnmapArgs
├── sele4n-sys/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs                      # Crate root, re-exports
│       ├── ipc/
│       │   ├── mod.rs
│       │   ├── message.rs             # IpcMessage builder
│       │   ├── endpoint.rs            # send, receive, call, reply
│       │   └── notification.rs        # signal, wait
│       ├── cspace.rs                   # mint, copy, move, delete
│       ├── lifecycle.rs               # retype + convenience constructors
│       ├── vspace.rs                   # map, unmap + PagePerms builder
│       ├── service.rs                  # start, stop
│       └── cap/
│           ├── mod.rs
│           ├── rights.rs              # Marker traits: HasRead, HasWrite, ...
│           └── objects.rs             # Marker types: obj::Endpoint, ...
└── tests/
    └── conformance.rs                  # Lean ↔ Rust cross-validation
```

### Scripts & Documentation

```
scripts/test_rust.sh                    # Rust build + test runner
docs/gitbook/15-rust-syscall-wrappers.md  # GitBook chapter
```

### Lean Extensions (minimal)

```
SeLe4n/Testing/MainTraceHarness.lean    # Extended: cross-validation test vectors
tests/fixtures/main_trace_smoke.expected # Extended: RUST-XVAL-* entries
```
