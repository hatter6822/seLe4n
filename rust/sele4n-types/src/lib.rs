// SPDX-License-Identifier: GPL-3.0-or-later
//! Core types for the seLe4n verified microkernel.
//!
//! This crate provides the foundational type definitions that mirror the Lean 4
//! kernel model exactly:
//!
//! - **15 newtype identifiers**: `ObjId`, `ThreadId`, `CPtr`, `Slot`,
//!   `SchedContextId`, etc. (AK4-C / R-ABI-L2 — `SchedContextId` added in v0.29.8;
//!   `RegValue` is a register-value wrapper counted separately).
//! - **`KernelError`**: 59-variant error enum (discriminants 0–60, 35 and 37 retired) matching `SeLe4n.Model.KernelError`
//!   (plus the `UnknownKernelError` sentinel at 255)
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

pub use error::{KernelError, KernelResult, LookupFault, SyscallError};
pub use identifiers::*;
pub use rights::{AccessRight, AccessRights, AccessRightsError};

/// WS-RA: the syscall **return** ABI version — the canonical Rust-side
/// pin (plan §3.6).
///
/// * Version **1** — the retired bit-63 protocol: one status word in
///   `x0`, bit 63 the error flag, values masked to 63 bits.
/// * Version **2** — the seL4 frame convention: `x0` the full-width
///   value, `x1` a `MessageInfo` whose label carried the error **offset by
///   one** (`d + 1`), `x2`-`x5` message registers.  Retired at WS-RR RR4:
///   a delivered fault message's `seL4_Fault_tag` label (1, 2, 3, 6)
///   decoded as a kernel error, so no fault handler could be written
///   against the decoder.
/// * Version **3** — the same frame with kernel status in the **top** of
///   the 20-bit label range: `0` = success, `ERROR_LABEL_BASE + d` =
///   `KernelError` discriminant `d`, and every label below
///   [`ERROR_LABEL_BASE`] is a delivered message's own label (a fault
///   handler's `seL4_Fault_tag`, for one).
/// * Version **4** — seL4's `seL4_MessageInfo_t` layout: `capsUnwrapped`
///   in bits 9-11 and the label from bit 12, and the IPC buffer's receive
///   path (`receive_cnode`, `receive_index`, `receive_depth`) after its
///   `caps_or_badges` words.
/// * Version **5** — an error frame carries seL4's error payload
///   (`setMRs_syscall_error`): `x1`'s length is the payload's word count,
///   `x2`-`x5` its first four words (MR0-MR3), and a guard mismatch's fifth
///   word is written to the caller's IPC buffer `msg[4]`, counted only when
///   written ([`SyscallError`]).
///
/// Mirrored by Lean's `Architecture.syscallAbiVersion` and the HAL's
/// `svc_dispatch::SYSCALL_ABI_VERSION`; each side's conformance suite
/// pins its own constant to the same literal, so a half-bumped tree
/// fails its own suite rather than mis-decoding at runtime.
pub const SYSCALL_ABI_VERSION: u64 = 5;

/// WS-RR RR4 (ABI v3): the first kernel-status label.  A `MessageInfo`
/// label at or above this value in `x1` is a kernel error (discriminant
/// `label - ERROR_LABEL_BASE`); a label below it is the delivered
/// message's own.  The range holds 256 labels, so the blocked-resume
/// sentinel (`MAX_LABEL`, `2^52 - 1`) is its last member and names
/// discriminant 255 — absent from the Lean `KernelError` and reserved here
/// for the forward-compatibility sentinel `UnknownKernelError`, so the
/// sentinel decodes to that variant by construction.  Mirrors Lean's
/// `Architecture.errorLabelBase` (`errorLabelBase_eq`) and the HAL's
/// hand-duplicated `svc_dispatch::ERROR_LABEL_BASE`.
pub const ERROR_LABEL_BASE: u64 = (1 << 52) - 256;

// The range is exactly the top of seL4's 52-bit label field.
const _: () = assert!(ERROR_LABEL_BASE == 0xF_FFFF_FFFF_FF00);
const _: () = assert!(ERROR_LABEL_BASE + 255 == (1 << 52) - 1);
pub use syscall::SyscallId;

// AN8-E (R-HAL-L2): The 52-line AK4-H audit-notes block previously inlined
// here is canonical-archived in `docs/AUDIT_NOTES.md` so this file stays
// lean. Cross-references for the current `KernelError` discriminants and
// `SyscallId` variants live next to their source-of-truth definitions in
// `error.rs` and `syscall.rs` respectively.
