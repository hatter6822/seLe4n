//! Syscall response decoding — unpacks ARM64 registers into typed results.

use sele4n_types::{KernelError, KernelResult, Badge};
use crate::MessageInfo;

/// A decoded syscall response from the kernel.
///
/// R-M03 fix: the x1 register carries context-dependent data (badge on
/// receive path, message info on send/call/reply path). Instead of
/// exposing both interpretations as public fields, a single `x1_raw`
/// field is stored and typed accessor methods disambiguate the semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyscallResponse {
    /// Error code from x0. `None` means success (x0 == 0).
    pub error: Option<KernelError>,
    /// Raw x1 register value — context-dependent (badge or message info).
    /// Use `badge()` or `msg_info()` to interpret.
    x1_raw: u64,
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
#[inline]
pub fn decode_response(regs: [u64; 7]) -> KernelResult<SyscallResponse> {
    if regs[0] != 0 {
        // Truncate u64 → u32 is safe: kernel error codes are 0–33.
        // Unrecognized codes map to InvalidSyscallNumber (protocol violation).
        let err = KernelError::from_u32(regs[0] as u32)
            .unwrap_or(KernelError::InvalidSyscallNumber);
        return Err(err);
    }

    Ok(SyscallResponse {
        error: None,
        x1_raw: regs[1],
        msg_regs: [regs[2], regs[3], regs[4], regs[5]],
    })
}

impl SyscallResponse {
    /// Interpret x1 as an IPC badge (valid for Receive/ReplyRecv syscalls).
    pub const fn badge(&self) -> Badge { Badge(self.x1_raw) }

    /// Interpret x1 as message info (valid for Send/Call/Reply syscalls).
    pub fn msg_info(&self) -> KernelResult<MessageInfo> {
        MessageInfo::decode(self.x1_raw).map_err(|_| KernelError::InvalidMessageInfo)
    }

    /// Get the raw x1 register value for direct inspection.
    pub const fn x1_raw(&self) -> u64 { self.x1_raw }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_success() {
        let regs = [0, 42, 1, 2, 3, 4, 0];
        let resp = decode_response(regs).unwrap();
        assert!(resp.error.is_none());
        assert_eq!(resp.badge(), Badge(42));
        assert_eq!(resp.x1_raw(), 42);
        assert_eq!(resp.msg_regs, [1, 2, 3, 4]);
    }

    #[test]
    fn decode_error() {
        // error code 1 = ObjectNotFound
        let regs = [1, 0, 0, 0, 0, 0, 0];
        let result = decode_response(regs);
        assert_eq!(result, Err(KernelError::ObjectNotFound));
    }

    #[test]
    fn badge_and_msg_info_from_same_x1() {
        let regs = [0, 0xBEEF, 0, 0, 0, 0, 0];
        let resp = decode_response(regs).unwrap();
        assert_eq!(resp.badge(), Badge(0xBEEF));
        // msg_info() interprets the same x1 differently
        assert_eq!(resp.x1_raw(), 0xBEEF);
    }
}
