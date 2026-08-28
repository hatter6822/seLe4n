// SPDX-License-Identifier: GPL-3.0-or-later
//! ARM64 register ABI layer for the seLe4n verified microkernel.
//!
//! This crate provides:
//! - `MessageInfo` bitfield encoding/decoding (seL4 convention)
//! - `SyscallRequest`/`SyscallResponse` register structures
//! - `raw_syscall`: inline ARM64 `svc #0` (the **single** `unsafe` block)
//! - `invoke_syscall`: safe wrapper
//! - Per-syscall typed argument structures with encode/decode
//! - `TypeTag` enum (8 retype variants, including SchedContext and Reply) and `PagePerms` bitmask
//! - `IpcBuffer` for messages exceeding the 4 inline ARM64 registers
//!
//! # Safety
//!
//! This crate contains exactly **one** `unsafe` block: the inline `svc #0`
//! instruction in `trap::raw_syscall`. All other code is safe Rust.

// S1-H: Deny unsafe code crate-wide. The single `svc #0` instruction in
// `trap::raw_syscall` has a targeted `#[allow(unsafe_code)]`.
#![no_std]
#![deny(unsafe_code)]

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
