//! Safe high-level syscall wrappers for the seLe4n verified microkernel.
//!
//! This crate provides ergonomic, fully safe wrappers around all 20 seLe4n
//! syscalls. Each wrapper encodes typed arguments into the ARM64 register ABI,
//! invokes the syscall via `sele4n_abi::invoke_syscall`, and decodes the result.
//!
//! # Modules
//!
//! - `ipc` — IPC operations: endpoint send/receive/call/reply,
//!   notification signal/wait, reply+receive compound operation
//! - `cspace` — CSpace operations: mint, copy, move, delete
//! - `lifecycle` — Object lifecycle: retype with type tag validation
//! - `vspace` — VSpace operations: map (with W^X enforcement), unmap
//! - `service` — Service registry: register, revoke, query
//! - `cap` — Phantom-typed capability handles (`Cap<Obj, Rts>`)
//!
//! # Safety
//!
//! This crate contains zero `unsafe` code. All unsafe operations are
//! confined to `sele4n_abi::trap::raw_syscall`.

#![no_std]
#![deny(unsafe_code)]

#[cfg(feature = "std")]
extern crate std;

pub mod ipc;
pub mod cspace;
pub mod lifecycle;
pub mod vspace;
pub mod service;
pub mod cap;

pub use sele4n_abi;
pub use sele4n_types;
