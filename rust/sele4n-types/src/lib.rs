//! Core types for the seLe4n verified microkernel.
//!
//! This crate provides the foundational type definitions that mirror the Lean 4
//! kernel model exactly:
//!
//! - **14 newtype identifiers**: `ObjId`, `ThreadId`, `CPtr`, `Slot`, etc.
//! - **`KernelError`**: 34-variant error enum matching `SeLe4n.Model.KernelError`
//! - **`AccessRight` / `AccessRights`**: Capability rights with bitmask operations
//! - **`SyscallId`**: 14-variant syscall identifier enum
//!
//! # Safety
//!
//! This crate contains zero `unsafe` code.

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
