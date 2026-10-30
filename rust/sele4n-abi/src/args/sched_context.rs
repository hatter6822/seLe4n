// SPDX-License-Identifier: GPL-3.0-or-later
//! SchedContext syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`.
//! Three capability-controlled operations for scheduling context management
//! added in WS-Z Phase Z5.

use sele4n_types::{CPtr, KernelError, KernelResult};

/// Maximum configurable priority value (8-bit, matching Lean scheduler).
pub const MAX_PRIORITY: u64 = 255;

/// Maximum configurable domain value (zero-indexed).
/// Matches Lean `numDomainsVal = 16`, so valid domains are 0..=15.
pub const MAX_DOMAIN: u64 = 15;

/// Bit position of the domain in the configure's parameter word: the priority
/// is bits 0–7, the domain bits 8–11, and any higher bit is refused.
pub const SCHED_PARAMS_DOMAIN_SHIFT: u32 = 8;

/// The first parameter word the kernel refuses: `16 << 8`, the first word whose
/// domain is out of range or which sets a bit above the domain's.
pub const SCHED_PARAMS_LIMIT: u64 = (MAX_DOMAIN + 1) << SCHED_PARAMS_DOMAIN_SHIFT;

/// Arguments for `schedContextConfigure` (syscall 17).
///
/// WS-ZA ZA6.4: the configure is invoked on a core's **scheduling-control**
/// capability (seL4-MCS's `SchedControl`, the only authority to set a context's
/// budget and period), and the context to configure is a capability the caller
/// holds, named by its address, as seL4-MCS's `seL4_SchedControl_ConfigureFlags`
/// takes the context as an extra capability.  A scheduling-context capability
/// configures nothing.
///
/// Register mapping: regs[0]=sched_context (the context capability's address),
/// regs[1]=budget, regs[2]=period, regs[3]=priority | domain << 8,
/// regs[4]=deadline.  Priority and domain share one word so the call keeps five
/// words.
///
/// Lean: `SchedContextConfigureArgs` (`SyscallArgDecode.lean`)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SchedContextConfigureArgs {
    pub sched_context: CPtr,
    pub budget: u64,
    pub period: u64,
    pub priority: u64,
    pub deadline: u64,
    pub domain: u64,
}

impl SchedContextConfigureArgs {
    /// Encode into message registers.  The parameter word carries the priority's
    /// low byte and the domain's low four bits; [`Self::decode`] and the kernel
    /// refuse a word with any higher bit set.
    pub const fn encode(&self) -> [u64; 5] {
        [
            self.sched_context.raw(),
            self.budget,
            self.period,
            (self.priority & MAX_PRIORITY)
                | ((self.domain & MAX_DOMAIN) << SCHED_PARAMS_DOMAIN_SHIFT),
            self.deadline,
        ]
    }

    /// Decode from message registers. Requires 5 registers.
    ///
    /// Validates the parameter word (priority ≤ 255 and domain ≤ 15, no higher
    /// bit) at the decode boundary.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 5 {
            return Err(KernelError::InvalidMessageInfo);
        }
        if regs[3] >= SCHED_PARAMS_LIMIT {
            return Err(KernelError::InvalidSyscallArgument);
        }
        Ok(Self {
            sched_context: CPtr::from(regs[0]),
            budget: regs[1],
            period: regs[2],
            priority: regs[3] & MAX_PRIORITY,
            deadline: regs[4],
            domain: regs[3] >> SCHED_PARAMS_DOMAIN_SHIFT,
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
            sched_context: CPtr::from(7u64),
            budget: 1000,
            period: 5000,
            priority: 128,
            deadline: 10000,
            domain: 3,
        };
        assert_eq!(
            SchedContextConfigureArgs::decode(&args.encode()).unwrap(),
            args
        );
    }

    #[test]
    fn configure_packs_priority_and_domain() {
        let args = SchedContextConfigureArgs {
            sched_context: CPtr::from(7u64),
            budget: 1,
            period: 2,
            priority: 0x2a,
            deadline: 3,
            domain: 5,
        };
        assert_eq!(args.encode(), [7, 1, 2, 0x52a, 3]);
    }

    #[test]
    fn configure_insufficient_regs() {
        assert_eq!(
            SchedContextConfigureArgs::decode(&[1, 2, 3, 4]),
            Err(KernelError::InvalidMessageInfo)
        );
    }

    #[test]
    fn configure_domain_out_of_range() {
        // Domain 16 is the first invalid value (numDomainsVal = 16, zero-indexed 0..=15)
        assert_eq!(
            SchedContextConfigureArgs::decode(&[7, 1000, 5000, 16 << 8, 10000]),
            Err(KernelError::InvalidSyscallArgument)
        );
        // A bit above the domain's is refused too
        assert_eq!(
            SchedContextConfigureArgs::decode(&[7, 1000, 5000, 1 << 40, 10000]),
            Err(KernelError::InvalidSyscallArgument)
        );
    }

    #[test]
    fn configure_max_valid_priority_and_domain() {
        // Priority max = 255, domain max = 15 (Lean numDomainsVal = 16)
        let args =
            SchedContextConfigureArgs::decode(&[7, 1000, 5000, 255 | (15 << 8), 10000]).unwrap();
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
