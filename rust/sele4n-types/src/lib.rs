//! Core types for the seLe4n verified microkernel.
//!
//! This crate provides the foundational type definitions that mirror the Lean 4
//! kernel model exactly:
//!
//! - **15 newtype identifiers**: `ObjId`, `ThreadId`, `CPtr`, `Slot`,
//!   `SchedContextId`, etc. (AK4-C / R-ABI-L2 — `SchedContextId` added in v0.29.6).
//! - **`KernelError`**: 50-variant error enum matching `SeLe4n.Model.KernelError`
//!   (49 kernel variants at discriminants 0–48, plus `UnknownKernelError` sentinel at 255)
//! - **`AccessRight` / `AccessRights`**: Capability rights with bitmask operations
//! - **`SyscallId`**: 25-variant syscall identifier enum
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

// ============================================================================
// AK4-H: LOW-tier ABI cleanup notes (R-ABI-L1..L8)
// ============================================================================
//
// Most LOW-tier findings from the v0.29.0 audit are documented at their
// original call sites. Centralised cross-references:
//
// * R-ABI-L1 (lifecycle.rs:14 docstring) — addressed in `args/lifecycle.rs`:
//   the full 7-variant `TypeTag` list is now enumerated in the
//   `LifecycleRetypeArgs` doc comment.
//
// * R-ABI-L2 (lib.rs:6 count) — docstring updated to "15 newtype
//   identifiers" (see line above) when `SchedContextId` was added in
//   AK4-C.
//
// * R-ABI-L3 (`RegValue` exported but unused by non-test code) — kept
//   public because it is the canonical wrapper for ARM64 register words
//   and will be consumed by the (H3/WS-V) hardware-binding FFI layer.
//   No `#[cfg(test)]` gating applied.
//
// * R-ABI-L4 (`ServiceQueryArgs` empty struct) — intentionally kept as
//   a marker type so per-syscall dispatch code can treat service-query
//   the same way it treats argument-bearing syscalls. Lean mirror:
//   `ServiceQueryArgs` in `SyscallArgDecode.lean`.
//
// * R-ABI-L5 (`lateout("x6") _` in `trap.rs`) — annotated with a comment
//   explaining the `clobber_abi("C")` redundancy. Removing it is a no-op.
//
// * R-ABI-L6 (constants duplicated across crates) — deferred to WS-V
//   to avoid churn during the Pre-1.0 hardening window. Canonical
//   ownership already lives in `sele4n-abi` (e.g., `MAX_METHOD_COUNT`,
//   `MAX_PRIORITY`) and `sele4n-types` (identifiers + error enums).
//
// * R-ABI-L7 (`ThreadId::SENTINEL` vs `CPtr::NULL`) — both names
//   retained; `CPtr::NULL` mirrors the `seL4_CapNull` convention and
//   removing it would break external-facing Rust code. No deprecation
//   shim added.
//
// * R-ABI-L8 (`Hash` derive on typed IDs) — `#[derive(Hash)]` is safe
//   because all identifier wrappers are `#[repr(transparent)] u64`; the
//   underlying hash is identical to `hash(&u64)`. Cross-reference:
//   AJ2-D in `docs/spec/SELE4N_SPEC.md` §8.12.
