//\! MessageInfo bitfield — matches `SeLe4n.Model.MessageInfo` encoding.
//\!
//\! Lean source: `SeLe4n/Model/Object/Types.lean` lines 717–860.
//\!
//\! Bit layout (seL4 convention):
//\! - bits 0–6:  length (7 bits, max 120)
//\! - bits 7–8:  extraCaps (2 bits, max 3)
//\! - bits 9+:   label (user-defined)

use sele4n_types::KernelError;

/// Maximum message length in registers (seL4_MsgMaxLength).
pub const MAX_MSG_LENGTH: u64 = 120;

/// Maximum extra capabilities per message (seL4_MsgMaxExtraCaps).
pub const MAX_EXTRA_CAPS: u64 = 3;

/// Decoded message-info word, matching `seL4_MessageInfo_t`.
///
/// Lean: `SeLe4n.Model.MessageInfo` (Types.lean:717)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MessageInfo {
    /// Number of message registers (0..=120).
    pub length: u8,
    /// Number of extra capability addresses (0..=3).
    pub extra_caps: u8,
    /// User-defined label.
    pub label: u64,
}

impl MessageInfo {
    /// Create a new MessageInfo with bounds checking.
    pub const fn new(length: u8, extra_caps: u8, label: u64) -> Result<Self, KernelError> {
        if length as u64 > MAX_MSG_LENGTH || extra_caps as u64 > MAX_EXTRA_CAPS {
            Err(KernelError::InvalidMessageInfo)
        } else {
            Ok(Self { length, extra_caps, label })
        }
    }

    /// Encode into a single 64-bit register word.
    ///
    /// Lean: `MessageInfo.encode` (Types.lean:737)
    #[inline]
    pub const fn encode(&self) -> u64 {
        (self.length as u64 & 0x7F)
            | ((self.extra_caps as u64 & 0x3) << 7)
            | (self.label << 9)
    }

    /// Decode a raw 64-bit word into MessageInfo.
    /// Returns `InvalidMessageInfo` if length > 120 or extraCaps > 3.
    ///
    /// Lean: `MessageInfo.decode` (Types.lean:742)
    #[inline]
    pub const fn decode(raw: u64) -> Result<Self, KernelError> {
        let length = (raw & 0x7F) as u8;
        let extra_caps = ((raw >> 7) & 0x3) as u8;
        let label = raw >> 9;
        if length as u64 <= MAX_MSG_LENGTH && extra_caps as u64 <= MAX_EXTRA_CAPS {
            Ok(Self { length, extra_caps, label })
        } else {
            Err(KernelError::InvalidMessageInfo)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_decode_roundtrip() {
        let mi = MessageInfo { length: 42, extra_caps: 2, label: 0x1234 };
        let encoded = mi.encode();
        let decoded = MessageInfo::decode(encoded).unwrap();
        assert_eq!(decoded, mi);
    }

    #[test]
    fn roundtrip_zero() {
        let mi = MessageInfo { length: 0, extra_caps: 0, label: 0 };
        assert_eq!(MessageInfo::decode(mi.encode()).unwrap(), mi);
    }

    #[test]
    fn roundtrip_max_valid() {
        let mi = MessageInfo { length: 120, extra_caps: 3, label: 0xFFFF };
        assert_eq!(MessageInfo::decode(mi.encode()).unwrap(), mi);
    }

    #[test]
    fn decode_invalid_length() {
        // length = 127 (0x7F) > 120
        let raw: u64 = 127;
        assert_eq!(MessageInfo::decode(raw), Err(KernelError::InvalidMessageInfo));
    }

    #[test]
    fn bit_layout_length() {
        let mi = MessageInfo { length: 42, extra_caps: 0, label: 0 };
        assert_eq!(mi.encode(), 42);
    }

    #[test]
    fn bit_layout_extra_caps() {
        let mi = MessageInfo { length: 0, extra_caps: 3, label: 0 };
        assert_eq!(mi.encode(), 3 << 7);
    }

    #[test]
    fn bit_layout_label() {
        let mi = MessageInfo { length: 0, extra_caps: 0, label: 5 };
        assert_eq!(mi.encode(), 5 << 9);
    }

    #[test]
    fn new_bounds_check() {
        assert!(MessageInfo::new(120, 3, 0).is_ok());
        assert!(MessageInfo::new(121, 0, 0).is_err());
        assert!(MessageInfo::new(0, 4, 0).is_err());
    }
}
