// SPDX-License-Identifier: GPL-3.0-or-later
//! Service syscall argument structures (WS-Q1-D).
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 496–694.

use sele4n_types::{InterfaceId, ServiceId, KernelError, KernelResult};

/// Maximum method count for a service registration.
/// Lean: service registrations are bounded to prevent resource exhaustion.
pub const MAX_METHOD_COUNT: u64 = 1024;

/// Maximum message/response size for a service registration (in bytes).
/// Lean: bounded by IPC buffer capacity.
pub const MAX_SERVICE_MESSAGE_SIZE: u64 = 120 * 8; // 120 registers × 8 bytes

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
            self.interface_id.raw(),
            self.method_count,
            self.max_message_size,
            self.max_response_size,
            if self.requires_grant { 1 } else { 0 },
        ]
    }

    /// Decode register values into typed ServiceRegisterArgs.
    ///
    /// T3-E/M-NEW-11: The `requires_grant` field uses strict boolean parsing:
    /// `regs[4] == 0` → false, `regs[4] == 1` → true, any other value
    /// returns `InvalidMessageInfo`. This prevents corrupted register
    /// contents from being silently accepted as `true`.
    /// V1-I (L-RS-2): Added bounds validation for `method_count` (≤ 1024)
    /// and `max_message_size`/`max_response_size` (≤ 960 bytes = 120 regs × 8).
    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 5 { return Err(KernelError::InvalidMessageInfo); }
        if regs[1] > MAX_METHOD_COUNT {
            return Err(KernelError::InvalidArgument);
        }
        if regs[2] > MAX_SERVICE_MESSAGE_SIZE {
            return Err(KernelError::InvalidArgument);
        }
        if regs[3] > MAX_SERVICE_MESSAGE_SIZE {
            return Err(KernelError::InvalidArgument);
        }
        let requires_grant = match regs[4] {
            0 => false,
            1 => true,
            _ => return Err(KernelError::InvalidMessageInfo),
        };
        Ok(Self {
            interface_id: InterfaceId::from(regs[0]),
            method_count: regs[1],
            max_message_size: regs[2],
            max_response_size: regs[3],
            requires_grant,
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
        [self.target_service.raw()]
    }

    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.is_empty() { return Err(KernelError::InvalidMessageInfo); }
        Ok(Self { target_service: ServiceId::from(regs[0]) })
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
            interface_id: InterfaceId::from(7u64),
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
            interface_id: InterfaceId::from(1u64),
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
        let args = ServiceRevokeArgs { target_service: ServiceId::from(42u64) };
        assert_eq!(ServiceRevokeArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn register_insufficient_regs() {
        assert_eq!(ServiceRegisterArgs::decode(&[1, 2, 3, 4]), Err(KernelError::InvalidMessageInfo));
    }

    // V1-I: bounds validation
    #[test]
    fn register_method_count_too_large() {
        assert_eq!(
            ServiceRegisterArgs::decode(&[1, MAX_METHOD_COUNT + 1, 64, 64, 0]),
            Err(KernelError::InvalidArgument)
        );
    }

    #[test]
    fn register_max_message_size_too_large() {
        assert_eq!(
            ServiceRegisterArgs::decode(&[1, 5, MAX_SERVICE_MESSAGE_SIZE + 1, 64, 0]),
            Err(KernelError::InvalidArgument)
        );
    }

    #[test]
    fn register_max_response_size_too_large() {
        assert_eq!(
            ServiceRegisterArgs::decode(&[1, 5, 64, MAX_SERVICE_MESSAGE_SIZE + 1, 0]),
            Err(KernelError::InvalidArgument)
        );
    }

    #[test]
    fn register_boundary_values_accepted() {
        let args = ServiceRegisterArgs::decode(&[1, MAX_METHOD_COUNT, MAX_SERVICE_MESSAGE_SIZE, MAX_SERVICE_MESSAGE_SIZE, 1]);
        assert!(args.is_ok());
    }
}
