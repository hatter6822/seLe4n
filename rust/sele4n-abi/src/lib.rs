// SPDX-License-Identifier: GPL-3.0-or-later
//! ARM64 register ABI layer for the seLe4n verified microkernel.
//!
//! This crate provides:
//! - `MessageInfo` bitfield encoding/decoding (seL4 convention)
//! - `SyscallRequest`/`SyscallResponse` register structures
//! - `raw_syscall`: inline ARM64 `svc #0` (the crate's one unsafe operation)
//! - `invoke_syscall`: safe wrapper
//! - Per-syscall typed argument structures with encode/decode
//! - `TypeTag` enum (8 retype variants, including SchedContext and Reply) and `PagePerms` bitmask
//! - `IpcBuffer` for messages exceeding the 4 inline ARM64 registers
//!
//! # Safety
//!
//! This crate contains exactly **one** unsafe operation: the inline `svc #0`
//! instruction in `trap::raw_syscall`. It reaches the reader in two places —
//! the `unsafe` block around the `asm!` itself, and the `unsafe` block at the
//! one call site, `trap::invoke_syscall` — and there is exactly one `unsafe fn`
//! in any single compilation. All other code is safe Rust.
//!
//! The earlier wording here said "exactly one `unsafe` block: the inline
//! `svc #0` instruction in `trap::raw_syscall`", and that block did not exist:
//! under edition 2021 an `unsafe fn` body is *implicitly* an unsafe context, so
//! the `asm!` carried no block and the crate's only real one was in
//! `invoke_syscall`. `unsafe_op_in_unsafe_fn` below removes the implicit
//! context, so every unsafe operation now sits in a block a reader can see and
//! the compiler can count — which is also what makes the host mock's "performs
//! no unsafe operation" claim checkable rather than asserted (it compiles with
//! no block at all).

// S1-H: Deny unsafe code crate-wide. The single `svc #0` instruction in
// `trap::raw_syscall` has a targeted `#[allow(unsafe_code)]`.
#![no_std]
#![deny(unsafe_code)]
// An `unsafe fn` is a contract on the CALLER; it is not a licence for the body.
// Edition 2021 conflates the two, which is how the module claimed an `unsafe`
// block it did not contain. Denying this lint restores the distinction — and it
// is edition 2024's default, so the crate is already at the behaviour it will
// otherwise acquire silently at the next edition bump.
#![deny(unsafe_op_in_unsafe_fn)]

#[cfg(feature = "std")]
extern crate std;

pub mod args;
pub mod decode;
pub mod encode;
pub mod ipc_buffer;
pub mod message_info;
pub mod registers;
pub mod trap;

pub use args::*;
pub use decode::{decode_response, SyscallResponse};
pub use encode::{encode_syscall, SyscallRequest};
pub use ipc_buffer::IpcBuffer;
pub use message_info::MessageInfo;
pub use registers::RegisterFile;
pub use trap::invoke_syscall;

pub use sele4n_types;
