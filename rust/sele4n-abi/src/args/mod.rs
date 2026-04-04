//! Per-syscall typed argument structures with encode/decode.
//!
//! Mirrors `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` exactly.

pub mod cspace;
pub mod lifecycle;
pub mod vspace;
pub mod service;
pub mod sched_context;
pub mod tcb;
pub mod type_tag;
pub mod page_perms;

pub use cspace::*;
pub use lifecycle::*;
pub use vspace::*;
pub use service::*;
pub use sched_context::*;
pub use tcb::*;
pub use type_tag::TypeTag;
pub use page_perms::PagePerms;
