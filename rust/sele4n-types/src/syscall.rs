//! Syscall identifier enumeration — 1:1 mapping from `SeLe4n.Model.SyscallId`.
//!
//! Lean source: `SeLe4n/Model/Object/Types.lean` lines 601–710.

use crate::rights::AccessRight;

/// Syscall identifier. 17 variants matching the Lean `SyscallId` inductive.
///
/// The `toNat` encoding from Lean is reflected in the `#[repr(u64)]` discriminants.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u64)]
pub enum SyscallId {
    // IPC
    Send = 0,
    Receive = 1,
    Call = 2,
    Reply = 3,
    // CSpace
    CSpaceMint = 4,
    CSpaceCopy = 5,
    CSpaceMove = 6,
    CSpaceDelete = 7,
    // Lifecycle
    LifecycleRetype = 8,
    // VSpace
    VSpaceMap = 9,
    VSpaceUnmap = 10,
    // Service (WS-Q1-D)
    ServiceRegister = 11,
    ServiceRevoke = 12,
    ServiceQuery = 13,
    // Notification (V2-A)
    NotificationSignal = 14,
    NotificationWait = 15,
    // Compound IPC (V2-C)
    ReplyRecv = 16,
}

impl SyscallId {
    /// Total number of modeled syscalls.
    pub const COUNT: usize = 17;

    /// Convert from a raw `u64` value. Returns `None` for out-of-range.
    /// Lean: `SyscallId.ofNat?`
    pub const fn from_u64(v: u64) -> Option<Self> {
        match v {
            0 => Some(Self::Send),
            1 => Some(Self::Receive),
            2 => Some(Self::Call),
            3 => Some(Self::Reply),
            4 => Some(Self::CSpaceMint),
            5 => Some(Self::CSpaceCopy),
            6 => Some(Self::CSpaceMove),
            7 => Some(Self::CSpaceDelete),
            8 => Some(Self::LifecycleRetype),
            9 => Some(Self::VSpaceMap),
            10 => Some(Self::VSpaceUnmap),
            11 => Some(Self::ServiceRegister),
            12 => Some(Self::ServiceRevoke),
            13 => Some(Self::ServiceQuery),
            14 => Some(Self::NotificationSignal),
            15 => Some(Self::NotificationWait),
            16 => Some(Self::ReplyRecv),
            _ => None,
        }
    }

    /// Convert to raw `u64`. Lean: `SyscallId.toNat`.
    #[inline]
    pub const fn to_u64(self) -> u64 { self as u64 }

    /// Required access right for this syscall.
    ///
    /// Matches the `SyscallGate.requiredRight` usage in `SeLe4n/Kernel/API.lean`.
    pub const fn required_right(self) -> AccessRight {
        match self {
            Self::Send | Self::Call | Self::Reply => AccessRight::Write,
            Self::Receive => AccessRight::Read,
            Self::CSpaceMint | Self::CSpaceCopy | Self::CSpaceMove => AccessRight::Grant,
            Self::CSpaceDelete => AccessRight::Write,
            Self::LifecycleRetype => AccessRight::Retype,
            Self::VSpaceMap | Self::VSpaceUnmap => AccessRight::Write,
            Self::ServiceRegister | Self::ServiceRevoke => AccessRight::Write,
            Self::ServiceQuery => AccessRight::Read,
            Self::NotificationSignal => AccessRight::Write,
            Self::NotificationWait => AccessRight::Read,
            Self::ReplyRecv => AccessRight::Read,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_u64_roundtrip() {
        for i in 0..17u64 {
            let sid = SyscallId::from_u64(i).unwrap();
            assert_eq!(sid.to_u64(), i);
        }
    }

    #[test]
    fn from_u64_out_of_range() {
        assert!(SyscallId::from_u64(17).is_none());
        assert!(SyscallId::from_u64(255).is_none());
    }

    #[test]
    fn injective() {
        // All 17 variants produce distinct values
        let mut seen = [false; 17];
        for i in 0..17u64 {
            let sid = SyscallId::from_u64(i).unwrap();
            let idx = sid.to_u64() as usize;
            assert!(!seen[idx]);
            seen[idx] = true;
        }
    }

    #[test]
    fn required_right_ipc() {
        assert_eq!(SyscallId::Send.required_right(), AccessRight::Write);
        assert_eq!(SyscallId::Receive.required_right(), AccessRight::Read);
        assert_eq!(SyscallId::Call.required_right(), AccessRight::Write);
        assert_eq!(SyscallId::Reply.required_right(), AccessRight::Write);
    }

    #[test]
    fn required_right_cspace() {
        assert_eq!(SyscallId::CSpaceMint.required_right(), AccessRight::Grant);
        assert_eq!(SyscallId::CSpaceCopy.required_right(), AccessRight::Grant);
        assert_eq!(SyscallId::CSpaceMove.required_right(), AccessRight::Grant);
        assert_eq!(SyscallId::CSpaceDelete.required_right(), AccessRight::Write);
    }

    #[test]
    fn required_right_lifecycle() {
        assert_eq!(SyscallId::LifecycleRetype.required_right(), AccessRight::Retype);
    }

    #[test]
    fn required_right_vspace() {
        assert_eq!(SyscallId::VSpaceMap.required_right(), AccessRight::Write);
        assert_eq!(SyscallId::VSpaceUnmap.required_right(), AccessRight::Write);
    }

    #[test]
    fn required_right_service() {
        assert_eq!(SyscallId::ServiceRegister.required_right(), AccessRight::Write);
        assert_eq!(SyscallId::ServiceRevoke.required_right(), AccessRight::Write);
        // ServiceQuery requires Read (not Write) — Lean API.lean:318
        assert_eq!(SyscallId::ServiceQuery.required_right(), AccessRight::Read);
    }

    #[test]
    fn required_right_notification() {
        assert_eq!(SyscallId::NotificationSignal.required_right(), AccessRight::Write);
        assert_eq!(SyscallId::NotificationWait.required_right(), AccessRight::Read);
    }

    #[test]
    fn required_right_reply_recv() {
        assert_eq!(SyscallId::ReplyRecv.required_right(), AccessRight::Read);
    }
}
