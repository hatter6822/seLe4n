// SPDX-License-Identifier: GPL-3.0-or-later
//! Core types for the seLe4n verified microkernel.
//!
//! This crate provides the foundational type definitions that mirror the Lean 4
//! kernel model exactly:
//!
//! - **15 newtype identifiers**: `ObjId`, `ThreadId`, `CPtr`, `Slot`,
//!   `SchedContextId`, etc. (AK4-C / R-ABI-L2 — `SchedContextId` added in v0.29.8).
//! - **`KernelError`**: 50-variant error enum matching `SeLe4n.Model.KernelError`
//!   (49 kernel variants at discriminants 0–48, plus `UnknownKernelError` sentinel at 255)
//! - **`AccessRight` / `AccessRights`**: Capability rights with bitmask operations
//! - **`SyscallId`**: 25-variant syscall identifier enum
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

pub mod identifiers;
pub mod error;
pub mod rights;
pub mod syscall;

pub use identifiers::*;
pub use error::{KernelError, KernelResult};
pub use rights::{AccessRight, AccessRights, AccessRightsError};
pub use syscall::SyscallId;

// AN8-E (R-HAL-L2): The 52-line AK4-H audit-notes block previously inlined
// here is canonical-archived in `docs/AUDIT_NOTES.md` so this file stays
// lean. Cross-references for the current `KernelError` discriminants and
// `SyscallId` variants live next to their source-of-truth definitions in
// `error.rs` and `syscall.rs` respectively.
