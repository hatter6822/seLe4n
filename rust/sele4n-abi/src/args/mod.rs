// SPDX-License-Identifier: GPL-3.0-or-later
//! Per-syscall typed argument structures with encode/decode.
//!
//! Mirrors `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` exactly.

pub mod cspace;
pub mod lifecycle;
pub mod page_perms;
pub mod sched_context;
pub mod service;
pub mod tcb;
pub mod type_tag;
pub mod vspace;

pub use cspace::*;
pub use lifecycle::*;
pub use page_perms::PagePerms;
pub use sched_context::*;
pub use service::*;
pub use tcb::*;
pub use type_tag::TypeTag;
pub use vspace::*;
