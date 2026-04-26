// SPDX-License-Identifier: GPL-3.0-or-later
//! Safe high-level syscall wrappers for the seLe4n verified microkernel.
//!
//! This crate provides ergonomic, fully safe wrappers around all 25 seLe4n
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
//! - `tcb` — TCB operations: suspend, resume, set priority/MCP, set IPC buffer
//! - `sched_context` — SchedContext operations: configure, bind, unbind
//! - `cap` — Phantom-typed capability handles (`Cap<Obj, Rts>`)
//!
//! # Safety
//!
//! This crate contains zero `unsafe` code. All unsafe operations are
//! confined to `sele4n_abi::trap::raw_syscall`.
//!
//! # Example
//!
//! Capability handles are phantom-typed so the type system prevents passing
//! a TCB capability where an endpoint was expected. Construction is a plain
//! `const fn`; the actual syscall (`svc #0`) only fires when an operation
//! method is invoked.
//!
//! ```
//! use sele4n_sys::cap::{Cap, Endpoint, FullRights, ReadOnly};
//! use sele4n_types::CPtr;
//!
//! // Bind a CPtr to an endpoint with full rights.
//! let ep: Cap<Endpoint, FullRights> = Cap::from_cptr(CPtr::from(7u64));
//! assert_eq!(ep.cptr(), CPtr::from(7u64));
//!
//! // Derive a read-only view of the same endpoint — rights-monotonic at
//! // compile time (no downgrade of `ReadOnly` to `FullRights` possible).
//! let ro: Cap<Endpoint, ReadOnly> = ep.to_read_only().unwrap();
//! assert_eq!(ro.cptr(), CPtr::from(7u64));
//! ```

#![no_std]
#![deny(unsafe_code)]

#[cfg(feature = "std")]
extern crate std;

pub mod ipc;
pub mod cspace;
pub mod lifecycle;
pub mod vspace;
pub mod service;
pub mod tcb;
pub mod sched_context;
pub mod cap;

pub use sele4n_abi;
pub use sele4n_types;
