// SPDX-License-Identifier: GPL-3.0-or-later
//! Syscall request encoding — packs typed arguments into ARM64 registers.
//!
//! Register layout (from `SeLe4n.Machine.arm64DefaultLayout`):
//! - x0: capability pointer (CPtr)
//! - x1: MessageInfo (encoded as 64-bit word)
//! - x2–x5: message registers [0..3]
//! - x7: seL4's syscall word (`Syscall::word`, `-1` for `Call` to `-11` for
//!   `Yield`)
//!
//! An operation is not a syscall (WS-SX SX7): an invocation is a `Call` on its
//! capability with the operation's invocation label in the message-info word
//! (`SyscallId::label`), and the kernel selects the operation from the
//! syscall, the capability's type and the label.  The IPC operations carry the
//! caller's own label, which the receiver reads.

use crate::MessageInfo;
#[cfg(test)]
use sele4n_types::Syscall;
use sele4n_types::{CPtr, KernelError, SyscallId};

/// A syscall request, ready to be encoded into registers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyscallRequest {
    /// Capability address (→ x0).
    pub cap_addr: CPtr,
    /// Message info (→ x1, encoded).
    pub msg_info: MessageInfo,
    /// Message registers (→ x2–x5). At most 4 inline registers.
    pub msg_regs: [u64; 4],
    /// The operation (→ x7 as its syscall's word, `SyscallId::syscall`, and,
    /// for a labelled operation, its label in x1, `SyscallId::label`).
    pub syscall_id: SyscallId,
}

/// Register array indices for the ARM64 ABI.
///
/// `arm64DefaultLayout` reads the syscall word from x7, as seL4's aarch64
/// ABI does (distinct from Linux's x8).
pub const REG_CAP_ADDR: usize = 0; // x0
pub const REG_MSG_INFO: usize = 1; // x1
pub const REG_MSG_BASE: usize = 2; // x2–x5
pub const REG_SYSCALL_NUM: usize = 6; // x7 (mapped to array index 6)

/// Encode a typed syscall request into a 7-element register array.
///
/// Layout: `[x0, x1, x2, x3, x4, x5, x7]`
///
/// The syscall word is placed at index 6, corresponding to x7: the word of
/// the syscall the operation is issued by (`SyscallId::syscall`).  A labelled
/// operation's label replaces the message info's (`SyscallId::label`); an IPC
/// operation keeps the caller's.
///
/// Returns `InvalidMessageInfo` if the MessageInfo label exceeds seL4's
/// 52-bit field.
#[inline]
pub fn encode_syscall(req: &SyscallRequest) -> Result<[u64; 7], KernelError> {
    let msg_info = match req.syscall_id.label() {
        Some(label) => MessageInfo::new(req.msg_info.length(), req.msg_info.extra_caps(), label)?,
        None => req.msg_info,
    };
    Ok([
        req.cap_addr.raw(),              // x0: CPtr
        msg_info.encode()?,              // x1: MessageInfo
        req.msg_regs[0],                 // x2: msg_reg[0]
        req.msg_regs[1],                 // x3: msg_reg[1]
        req.msg_regs[2],                 // x4: msg_reg[2]
        req.msg_regs[3],                 // x5: msg_reg[3]
        req.syscall_id.syscall().word(), // x7: seL4's syscall word
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_basic() {
        let req = SyscallRequest {
            cap_addr: CPtr::from(100u64),
            msg_info: MessageInfo::new(2, 0, 0).unwrap(),
            msg_regs: [10, 20, 0, 0],
            syscall_id: SyscallId::Send,
        };
        let regs = encode_syscall(&req).unwrap();
        assert_eq!(regs[0], 100); // x0 = CPtr
        assert_eq!(regs[1], 2); // x1 = MessageInfo(length=2)
        assert_eq!(regs[2], 10); // x2 = msg_reg[0]
        assert_eq!(regs[3], 20); // x3 = msg_reg[1]
        assert_eq!(regs[6], Syscall::Send.word()); // x7 = seL4_SysSend, -5
    }

    #[test]
    fn encode_cspace_mint() {
        let req = SyscallRequest {
            cap_addr: CPtr::from(42u64),
            // destIndex, destDepth, srcIndex, srcDepth; the rights and the
            // badge are the fifth and sixth words, in the IPC buffer, and the
            // source root is extra capability 0.
            msg_info: MessageInfo::new(6, 1, 0).unwrap(),
            msg_regs: [1, 2, 3, 4],
            syscall_id: SyscallId::CSpaceMint,
        };
        let regs = encode_syscall(&req).unwrap();
        assert_eq!(regs[6], Syscall::Call.word()); // x7 = seL4_SysCall, -1
        assert_eq!(regs[1] >> 12, 22); // CNodeMint's invocation label
    }

    #[test]
    fn encode_rejects_oversized_label() {
        // Construction of invalid MessageInfo must go through new(), which
        // rejects labels >= 2^52 (seL4's field). We verify the error path via
        // new().
        assert_eq!(
            MessageInfo::new(0, 0, 1u64 << 52),
            Err(KernelError::InvalidMessageInfo)
        );
    }
}
