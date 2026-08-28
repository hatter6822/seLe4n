// SPDX-License-Identifier: GPL-3.0-or-later
//! Core types for the seLe4n verified microkernel.
//!
//! This crate provides the foundational type definitions that mirror the Lean 4
//! kernel model exactly:
//!
//! - **15 newtype identifiers**: `ObjId`, `ThreadId`, `CPtr`, `Slot`,
//!   `SchedContextId`, etc. (AK4-C / R-ABI-L2 — `SchedContextId` added in v0.29.8;
//!   `RegValue` is a register-value wrapper counted separately).
//! - **`KernelError`**: 58-variant error enum matching `SeLe4n.Model.KernelError`
//!   (57 kernel variants at discriminants 0–56, plus `UnknownKernelError` sentinel at 255)
//! - **`AccessRight` / `AccessRights`**: Capability rights with bitmask operations
//! - **`SyscallId`**: 34-variant syscall identifier enum
//!
//! # Safety
//!
//! This crate contains zero `unsafe` code.
//!
//! # Example
//!
//! ```
//! use sele4n_types::{ThreadId, AccessRights, AccessRight};
//!
//! // Newtype identifiers wrap raw u64 with strong typing.
//! let tid = ThreadId::from(42u64);
//! assert_eq!(tid.raw(), 42);
//! assert!(!tid.is_reserved());
//! assert!(ThreadId::SENTINEL.is_reserved());
//!
//! // Access rights are a 5-bit mask with a functional (immutable) API.
//! let read_write = AccessRights::READ.union(AccessRights::WRITE);
//! assert!(read_write.contains(AccessRight::Read));
//! assert!(read_write.contains(AccessRight::Write));
//! assert!(!read_write.contains(AccessRight::Grant));
//! assert!(read_write.is_subset_of(&AccessRights::ALL));
//! ```

#![no_std]
#![deny(unsafe_code)]

#[cfg(feature = "std")]
extern crate std;

pub mod error;
pub mod identifiers;
pub mod rights;
pub mod syscall;

pub use error::{KernelError, KernelResult};
pub use identifiers::*;
pub use rights::{AccessRight, AccessRights, AccessRightsError};

/// WS-RA: the syscall **return** ABI version — the canonical Rust-side
/// pin (plan §3.6).
///
/// * Version **1** — the retired bit-63 protocol: one status word in
///   `x0`, bit 63 the error flag, values masked to 63 bits.
/// * Version **2** — the seL4 frame convention: `x0` the full-width
///   value, `x1` a `MessageInfo` whose **offset** label carries the
///   error (`0` = success, `d + 1` = `KernelError` discriminant `d`),
///   `x2`-`x5` message registers.
///
/// Mirrored by Lean's `Architecture.syscallAbiVersion` and the HAL's
/// `svc_dispatch::SYSCALL_ABI_VERSION`; each side's conformance suite
/// pins its own constant to the same literal, so a half-bumped tree
/// fails its own suite rather than mis-decoding at runtime.
pub const SYSCALL_ABI_VERSION: u64 = 2;
pub use syscall::SyscallId;

// AN8-E (R-HAL-L2): The 52-line AK4-H audit-notes block previously inlined
// here is canonical-archived in `docs/AUDIT_NOTES.md` so this file stays
// lean. Cross-references for the current `KernelError` discriminants and
// `SyscallId` variants live next to their source-of-truth definitions in
// `error.rs` and `syscall.rs` respectively.
