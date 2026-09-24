// SPDX-License-Identifier: GPL-3.0-or-later
//! SchedContext syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 894–911.
//! Three capability-controlled operations for scheduling context management
//! added in WS-Z Phase Z5.

use sele4n_types::{CPtr, KernelError, KernelResult};

/// Maximum configurable priority value (8-bit, matching Lean scheduler).
pub const MAX_PRIORITY: u64 = 255;

/// Maximum configurable domain value (zero-indexed).
/// Matches Lean `numDomainsVal = 16`, so valid domains are 0..=15.
pub const MAX_DOMAIN: u64 = 15;

/// Arguments for `schedContextConfigure` (syscall 17).
/// Register mapping: regs[0]=budget, regs[1]=period, regs[2]=priority, regs[3]=deadline, regs[4]=domain.
///
/// Lean: `SchedContextConfigureArgs` (SyscallArgDecode.lean:894–900)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SchedContextConfigureArgs {
    pub budget: u64,
    pub period: u64,
    pub priority: u64,
    pub deadline: u64,
    pub domain: u64,
}

impl SchedContextConfigureArgs {
    pub const fn encode(&self) -> [u64; 5] {
        [
            self.budget,
            self.period,
            self.priority,
            self.deadline,
            self.domain,
        ]
    }

    /// Decode from message registers. Requires 5 registers.
    ///
    /// Validates priority ≤ 255 and domain ≤ 15 at the decode boundary.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 5 {
            return Err(KernelError::InvalidMessageInfo);
        }
        if regs[2] > MAX_PRIORITY {
            return Err(KernelError::InvalidSyscallArgument);
        }
        if regs[4] > MAX_DOMAIN {
            return Err(KernelError::InvalidSyscallArgument);
        }
        Ok(Self {
            budget: regs[0],
            period: regs[1],
            priority: regs[2],
            deadline: regs[3],
            domain: regs[4],
        })
    }
}

/// Arguments for `schedContextBind` (syscall 18).
/// Register mapping: regs[0]=tcbCPtr — the **capability address**, in the
/// caller's own CSpace, of the TCB to bind to the invoked SchedContext.
///
/// `v0.35.204`: this was `thread_id: ThreadId`, a raw thread id the kernel
/// bound directly under the SchedContext capability alone — so a holder of one
/// could bind it to any thread it could name and, through the bind's priority
/// propagation, rewrite that thread's base priority.  seL4-MCS's
/// `seL4_SchedContext_Bind` takes the TCB as a capability; the kernel's
/// `resolveSchedContextBindThread` now resolves MR0 through the caller's CSpace
/// requiring `.write`, exactly as `tcbBindNotification` resolves its
/// notification.  Typed `CPtr` so the wrapper cannot be handed a thread id.
///
/// Lean: `SchedContextBindArgs` (`SyscallArgDecode.lean`)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SchedContextBindArgs {
    pub tcb_cap: CPtr,
}

impl SchedContextBindArgs {
    pub const fn encode(&self) -> [u64; 1] {
        [self.tcb_cap.raw()]
    }

    /// Decode from message registers. Requires 1 register.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.is_empty() {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            tcb_cap: CPtr::from(regs[0]),
        })
    }
}

/// Arguments for `schedContextUnbind` (syscall 19).
/// No additional arguments — the SchedContext is identified by the capability target.
///
/// Lean: `SchedContextUnbindArgs` (SyscallArgDecode.lean:910–911)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SchedContextUnbindArgs;

impl SchedContextUnbindArgs {
    pub const fn encode(&self) -> [u64; 0] {
        []
    }

    /// Decode from message registers. No registers required.
    pub fn decode(_regs: &[u64]) -> KernelResult<Self> {
        Ok(Self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn configure_roundtrip() {
        let args = SchedContextConfigureArgs {
            budget: 1000,
            period: 5000,
            priority: 128,
            deadline: 10000,
            domain: 0,
        };
        assert_eq!(
            SchedContextConfigureArgs::decode(&args.encode()).unwrap(),
            args
        );
    }

    #[test]
    fn configure_insufficient_regs() {
        assert_eq!(
            SchedContextConfigureArgs::decode(&[1, 2, 3, 4]),
            Err(KernelError::InvalidMessageInfo)
        );
    }

    #[test]
    fn configure_priority_out_of_range() {
        assert_eq!(
            SchedContextConfigureArgs::decode(&[1000, 5000, 256, 10000, 0]),
            Err(KernelError::InvalidSyscallArgument)
        );
    }

    #[test]
    fn configure_domain_out_of_range() {
        // Domain 16 is the first invalid value (numDomainsVal = 16, zero-indexed 0..=15)
        assert_eq!(
            SchedContextConfigureArgs::decode(&[1000, 5000, 128, 10000, 16]),
            Err(KernelError::InvalidSyscallArgument)
        );
        // Domain 256 is also invalid (original boundary)
        assert_eq!(
            SchedContextConfigureArgs::decode(&[1000, 5000, 128, 10000, 256]),
            Err(KernelError::InvalidSyscallArgument)
        );
    }

    #[test]
    fn configure_max_valid_priority_and_domain() {
        // Priority max = 255, domain max = 15 (Lean numDomainsVal = 16)
        let args = SchedContextConfigureArgs::decode(&[1000, 5000, 255, 10000, 15]).unwrap();
        assert_eq!(args.priority, 255);
        assert_eq!(args.domain, 15);
    }

    #[test]
    fn bind_roundtrip() {
        let args = SchedContextBindArgs {
            tcb_cap: CPtr::from(42u64),
        };
        assert_eq!(SchedContextBindArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn bind_insufficient_regs() {
        assert_eq!(
            SchedContextBindArgs::decode(&[]),
            Err(KernelError::InvalidMessageInfo)
        );
    }

    #[test]
    fn unbind_roundtrip() {
        assert_eq!(
            SchedContextUnbindArgs::decode(&[]).unwrap(),
            SchedContextUnbindArgs
        );
        // Extra registers are ignored
        assert_eq!(
            SchedContextUnbindArgs::decode(&[1, 2, 3]).unwrap(),
            SchedContextUnbindArgs
        );
    }
}
