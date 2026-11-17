// SPDX-License-Identifier: GPL-3.0-or-later
//! SchedContext syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`.
//! Three capability-controlled operations for scheduling context management
//! added in WS-Z Phase Z5.

use sele4n_types::{KernelError, KernelResult};

/// Arguments for `schedContextConfigure` (syscall 17) — seL4-MCS's
/// `seL4_SchedControl_ConfigureFlags`.
///
/// WS-ZA ZA6.4: the configure is invoked on a core's **scheduling-control**
/// capability (seL4-MCS's `SchedControl`, the only authority to set a context's
/// budget and period).  WS-SX SX6.4: the context to configure is the message's
/// extra capability 0 (`caps_or_badges[0]` of the caller's IPC buffer), as
/// seL4-MCS's `decodeSchedControl_ConfigureFlags` reads `excaprefs[0]`; no
/// message word names it.  A scheduling-context capability configures nothing.
///
/// Register mapping (seL4-MCS's, one-word times): regs[0]=budget,
/// regs[1]=period, regs[2]=extra_refills, regs[3]=badge, regs[4]=flags (bit 0
/// is `seL4_SchedContext_Sporadic`).  A context carries no priority, deadline
/// or domain: those are the thread's.
///
/// Lean: `SchedContextConfigureArgs` (`SyscallArgDecode.lean`)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SchedContextConfigureArgs {
    pub budget: u64,
    pub period: u64,
    pub extra_refills: u64,
    pub badge: u64,
    pub flags: u64,
}

impl SchedContextConfigureArgs {
    /// Encode into message registers.  Every word is carried verbatim: the
    /// kernel range-checks the budget, period and extra refills and stores the
    /// badge and flags as given.
    pub const fn encode(&self) -> [u64; 5] {
        [
            self.budget,
            self.period,
            self.extra_refills,
            self.badge,
            self.flags,
        ]
    }

    /// Decode from message registers. Requires 5 registers.
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 5 {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok(Self {
            budget: regs[0],
            period: regs[1],
            extra_refills: regs[2],
            badge: regs[3],
            flags: regs[4],
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
            extra_refills: 2,
            badge: 0xFEED_FACE_CAFE_BEEF,
            flags: 1,
        };
        assert_eq!(args.encode(), [1000, 5000, 2, 0xFEED_FACE_CAFE_BEEF, 1]);
        assert_eq!(SchedContextConfigureArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn configure_carries_every_word_verbatim() {
        // No bit of the badge or flags is masked or refused: seL4-MCS stores
        // the badge word and reads bit 0 of the flags.
        let regs = [1, 1, u64::MAX, u64::MAX, u64::MAX];
        let args = SchedContextConfigureArgs::decode(&regs).unwrap();
        assert_eq!(args.encode(), regs);
    }

    #[test]
    fn configure_insufficient_regs() {
        assert_eq!(
            SchedContextConfigureArgs::decode(&[1, 2, 3, 4]),
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
