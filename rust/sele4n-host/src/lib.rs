// SPDX-License-Identifier: GPL-3.0-or-later
//! # sele4n-host — Host-side runtime for the seLe4n verified microkernel
//!
//! This crate is the **host-side** companion to the `no_std` workspace
//! members (`sele4n-types`, `sele4n-abi`, `sele4n-sys`, `sele4n-hal`).
//! It is built and executed on the developer workstation (Linux,
//! macOS, Windows) and provides a foundation for:
//!
//! 1. **Fixture construction** — declarative builders that produce
//!    register-file snapshots compatible with the ARM64 syscall ABI
//!    encoded by `sele4n-abi`.
//! 2. **Outcome decoding** — host-side decode of the bit-63-flagged
//!    `UInt64` return contract emitted by the verified Lean kernel
//!    via `SeLe4n.Platform.FFI.syscallDispatchFromAbi`.
//! 3. **State scaffolding** — a placeholder type for the host-side
//!    mirror of the kernel's `SystemState`.  Later WS-RH phases
//!    populate the field set; the foundation phase only carries the
//!    shape.
//! 4. **Runtime metadata** — workspace-pinned version + version
//!    consistency assertions used by the integration test harness
//!    to catch silent version drift between the Lean lakefile and
//!    the Rust workspace.
//!
//! ## Crate distinction
//!
//! `sele4n-host` is **not** a syscall facade.  It never traps.  The
//! `sele4n-sys` crate is the guest-side TCB syscall facade and lives
//! in `no_std`; it issues `svc #0` via `sele4n-abi::trap::raw_syscall`.
//! `sele4n-host` is host-side and never issues a syscall instruction —
//! it composes register files for off-target testing.
//!
//! ## TCB invariance
//!
//! `sele4n-host` is **not part of the kernel Trusted Computing Base**.
//! The kernel binary is linked from `sele4n-hal` (kernel-side) and
//! transitively depends only on the `no_std` workspace members.
//! Cargo's path-based dependency graph statically enforces this
//! partition; the host crate has zero reverse dependencies inside
//! the workspace.
//!
//! ## Safety
//!
//! This crate contains zero `unsafe` code.  All host-side operations
//! are pure-Rust value transformations over types defined in
//! `sele4n-types` and `sele4n-abi`.
//!
//! ## Workstream
//!
//! Foundation phase: **WS-RH RH-H** ("Workspace and CI harness").
//! See [`docs/planning/rust_host_runtime_plan.md`] for the
//! per-phase decomposition.
//!
//! [`docs/planning/rust_host_runtime_plan.md`]: https://github.com/hatter6822/seLe4n/blob/main/docs/planning/rust_host_runtime_plan.md
//!
//! # Example
//!
//! ```
//! use sele4n_host::{HostRuntime, FixtureBuilder, DispatchOutcome};
//! use sele4n_types::SyscallId;
//! use sele4n_abi::MessageInfo;
//!
//! // The host runtime carries workspace-pinned metadata.
//! let rt = HostRuntime::new();
//! assert!(!rt.version().is_empty());
//!
//! // Build a register-file fixture from a high-level description.
//! let info = MessageInfo::new(0, 0, 0).unwrap();
//! let snapshot = FixtureBuilder::new()
//!     .with_syscall_id(SyscallId::Send)
//!     .with_message_info(info)
//!     .build();
//! assert_eq!(snapshot.registers().len(), 8);
//!
//! // Decode a kernel-emitted UInt64 return value.
//! //
//! // Bit 63 clear: success path; the remaining 63 bits carry the
//! // success-encoded payload.  Bit 63 set: error path; the low 32
//! // bits carry the `KernelError` discriminant.
//! let outcome = DispatchOutcome::decode(0x0000_0000_0000_002A);
//! assert!(matches!(outcome, DispatchOutcome::Ok(42)));
//! ```

#![deny(unsafe_code)]
#![deny(missing_docs)]
#![deny(rust_2018_idioms)]

pub mod runtime;
pub mod dispatch;
pub mod state;
pub mod fixture;

pub use runtime::HostRuntime;
pub use dispatch::{DispatchOutcome, DispatcherInternalError};
pub use state::{HostState, HostStateError};
pub use fixture::{FixtureBuilder, FixtureSnapshot};

pub use sele4n_abi;
pub use sele4n_types;
