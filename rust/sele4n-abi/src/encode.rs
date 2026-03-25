//! Syscall request encoding — packs typed arguments into ARM64 registers.
//!
//! Register layout (from `SeLe4n.Machine.arm64DefaultLayout`):
//! - x0: capability pointer (CPtr)
//! - x1: MessageInfo (encoded as 64-bit word)
//! - x2–x5: message registers [0..3]
//! - x7: syscall number (SyscallId.toNat)

use sele4n_types::{CPtr, SyscallId, KernelError};
use crate::MessageInfo;

/// A syscall request, ready to be encoded into registers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyscallRequest {
    /// Capability address (→ x0).
    pub cap_addr: CPtr,
    /// Message info (→ x1, encoded).
    pub msg_info: MessageInfo,
    /// Message registers (→ x2–x5). At most 4 inline registers.
    pub msg_regs: [u64; 4],
    /// Syscall identifier (→ x7).
    pub syscall_id: SyscallId,
}

/// Register array indices for the ARM64 ABI.
///
/// Note: The actual `arm64DefaultLayout` in Lean uses x7 for the syscall
/// number register, matching the seLe4n convention (distinct from Linux's x8).
pub const REG_CAP_ADDR: usize = 0;    // x0
pub const REG_MSG_INFO: usize = 1;    // x1
pub const REG_MSG_BASE: usize = 2;    // x2–x5
pub const REG_SYSCALL_NUM: usize = 6; // x7 (mapped to array index 6)

/// Encode a typed syscall request into a 7-element register array.
///
/// Layout: `[x0, x1, x2, x3, x4, x5, x7]`
///
/// The syscall number is placed at index 6, corresponding to x7 in the
/// ARM64 convention (seLe4n uses x7, not x8).
///
/// V2-H: Returns `InvalidMessageInfo` if the MessageInfo label exceeds
/// the 20-bit encoding limit.
#[inline]
pub fn encode_syscall(req: &SyscallRequest) -> Result<[u64; 7], KernelError> {
    Ok([
        req.cap_addr.raw(),              // x0: CPtr
        req.msg_info.encode()?,          // x1: MessageInfo
        req.msg_regs[0],                 // x2: msg_reg[0]
        req.msg_regs[1],                 // x3: msg_reg[1]
        req.msg_regs[2],                 // x4: msg_reg[2]
        req.msg_regs[3],                 // x5: msg_reg[3]
        req.syscall_id.to_u64(),         // x7: syscall number
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
        assert_eq!(regs[0], 100);  // x0 = CPtr
        assert_eq!(regs[1], 2);    // x1 = MessageInfo(length=2)
        assert_eq!(regs[2], 10);   // x2 = msg_reg[0]
        assert_eq!(regs[3], 20);   // x3 = msg_reg[1]
        assert_eq!(regs[6], 0);    // x7 = SyscallId::Send = 0
    }

    #[test]
    fn encode_cspace_mint() {
        let req = SyscallRequest {
            cap_addr: CPtr::from(42u64),
            msg_info: MessageInfo::new(4, 0, 0).unwrap(),
            msg_regs: [1, 2, 3, 4], // srcSlot, dstSlot, rights, badge
            syscall_id: SyscallId::CSpaceMint,
        };
        let regs = encode_syscall(&req).unwrap();
        assert_eq!(regs[6], 4); // CSpaceMint = 4
    }

    #[test]
    fn encode_rejects_oversized_label() {
        // V2-H: Construction of invalid MessageInfo must go through new(),
        // which rejects labels >= 2^20. We verify the error path via new().
        assert_eq!(MessageInfo::new(0, 0, 1u64 << 20), Err(KernelError::InvalidMessageInfo));
    }
}
