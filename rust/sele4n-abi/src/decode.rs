//! Syscall response decoding — unpacks ARM64 registers into typed results.

use sele4n_types::{KernelError, KernelResult, Badge};
use crate::MessageInfo;

/// A decoded syscall response from the kernel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyscallResponse {
    /// Error code from x0. `None` means success (x0 == 0).
    pub error: Option<KernelError>,
    /// IPC badge from x1 (present on receive path).
    pub badge: Badge,
    /// Message info from x1 (present on receive path, decoded separately).
    pub msg_info_raw: u64,
    /// Message registers from x2–x5.
    pub msg_regs: [u64; 4],
}

/// Decode a 7-element register array into a `SyscallResponse`.
///
/// Layout: `[x0, x1, x2, x3, x4, x5, x7]`
///
/// - x0: error code (0 = success)
/// - x1: badge or message info (context-dependent)
/// - x2–x5: return message registers
pub fn decode_response(regs: [u64; 7]) -> KernelResult<SyscallResponse> {
    let error = if regs[0] == 0 {
        None
    } else {
        let err = KernelError::from_u32(regs[0] as u32)
            .unwrap_or(KernelError::NotImplemented);
        return Err(err);
    };

    Ok(SyscallResponse {
        error,
        badge: Badge(regs[1]),
        msg_info_raw: regs[1],
        msg_regs: [regs[2], regs[3], regs[4], regs[5]],
    })
}

impl SyscallResponse {
    /// Decode the message info from the raw x1 register value.
    pub fn decode_msg_info(&self) -> KernelResult<MessageInfo> {
        MessageInfo::decode(self.msg_info_raw).map_err(|_| KernelError::InvalidMessageInfo)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_success() {
        let regs = [0, 42, 1, 2, 3, 4, 0];
        let resp = decode_response(regs).unwrap();
        assert!(resp.error.is_none());
        assert_eq!(resp.badge, Badge(42));
        assert_eq!(resp.msg_regs, [1, 2, 3, 4]);
    }

    #[test]
    fn decode_error() {
        // error code 1 = ObjectNotFound
        let regs = [1, 0, 0, 0, 0, 0, 0];
        let result = decode_response(regs);
        assert_eq!(result, Err(KernelError::ObjectNotFound));
    }
}
