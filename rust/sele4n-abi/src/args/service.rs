//! Service syscall argument structures (WS-Q1-D).
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 496–694.

use sele4n_types::{InterfaceId, ServiceId, KernelError, KernelResult};

/// Arguments for `serviceRegister` (syscall 11).
/// Register mapping: x2=interfaceId, x3=methodCount, x4=maxMessageSize,
/// x5=maxResponseSize, x6=requiresGrant (0 or 1).
///
/// Lean: `ServiceRegisterArgs` (SyscallArgDecode.lean:502)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ServiceRegisterArgs {
    pub interface_id: InterfaceId,
    pub method_count: u64,
    pub max_message_size: u64,
    pub max_response_size: u64,
    pub requires_grant: bool,
}

impl ServiceRegisterArgs {
    pub const fn encode(&self) -> [u64; 5] {
        [
            self.interface_id.0,
            self.method_count,
            self.max_message_size,
            self.max_response_size,
            if self.requires_grant { 1 } else { 0 },
        ]
    }

    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 5 { return Err(KernelError::InvalidMessageInfo); }
        Ok(Self {
            interface_id: InterfaceId(regs[0]),
            method_count: regs[1],
            max_message_size: regs[2],
            max_response_size: regs[3],
            requires_grant: regs[4] != 0,
        })
    }
}

/// Arguments for `serviceRevoke` (syscall 12).
/// Register mapping: x2=serviceId.
///
/// Lean: `ServiceRevokeArgs` (SyscallArgDecode.lean:512)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ServiceRevokeArgs {
    pub target_service: ServiceId,
}

impl ServiceRevokeArgs {
    pub const fn encode(&self) -> [u64; 1] {
        [self.target_service.0]
    }

    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.is_empty() { return Err(KernelError::InvalidMessageInfo); }
        Ok(Self { target_service: ServiceId(regs[0]) })
    }
}

/// Arguments for `serviceQuery` (syscall 13).
/// No additional message registers — the endpoint object ID comes from the
/// capability target.
///
/// Lean: `ServiceQueryArgs` (SyscallArgDecode.lean:519)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ServiceQueryArgs;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn register_roundtrip() {
        let args = ServiceRegisterArgs {
            interface_id: InterfaceId(7),
            method_count: 5,
            max_message_size: 256,
            max_response_size: 128,
            requires_grant: true,
        };
        assert_eq!(ServiceRegisterArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn register_requires_grant_false() {
        let args = ServiceRegisterArgs {
            interface_id: InterfaceId(1),
            method_count: 1,
            max_message_size: 64,
            max_response_size: 64,
            requires_grant: false,
        };
        let decoded = ServiceRegisterArgs::decode(&args.encode()).unwrap();
        assert!(!decoded.requires_grant);
    }

    #[test]
    fn revoke_roundtrip() {
        let args = ServiceRevokeArgs { target_service: ServiceId(42) };
        assert_eq!(ServiceRevokeArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn register_insufficient_regs() {
        assert_eq!(ServiceRegisterArgs::decode(&[1, 2, 3, 4]), Err(KernelError::InvalidMessageInfo));
    }
}
