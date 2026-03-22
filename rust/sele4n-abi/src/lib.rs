//! ARM64 register ABI layer for the seLe4n verified microkernel.
//!
//! This crate provides:
//! - `MessageInfo` bitfield encoding/decoding (seL4 convention)
//! - `SyscallRequest`/`SyscallResponse` register structures
//! - `raw_syscall`: inline ARM64 `svc #0` (the **single** `unsafe` block)
//! - `invoke_syscall`: safe wrapper
//! - Per-syscall typed argument structures with encode/decode
//! - `TypeTag` enum (6 retype variants) and `PagePerms` bitmask
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

pub mod message_info;
pub mod encode;
pub mod decode;
pub mod trap;
pub mod args;
pub mod ipc_buffer;

pub use message_info::MessageInfo;
pub use encode::{SyscallRequest, encode_syscall};
pub use decode::{SyscallResponse, decode_response};
pub use trap::invoke_syscall;
pub use args::*;
pub use ipc_buffer::IpcBuffer;

pub use sele4n_types;
