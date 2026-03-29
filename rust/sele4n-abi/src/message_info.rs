//! MessageInfo bitfield — matches `SeLe4n.Model.MessageInfo` encoding.
//!
//! Lean source: `SeLe4n/Model/Object/Types.lean` lines 717–860.
//!
//! Bit layout (seL4 convention):
//! - bits 0–6:  length (7 bits, max 120)
//! - bits 7–8:  extraCaps (2 bits, max 3)
//! - bits 9–28: label (20 bits, user-defined; seL4 convention)

use sele4n_types::KernelError;

/// Maximum message length in registers (seL4_MsgMaxLength).
pub const MAX_MSG_LENGTH: u64 = 120;

/// Maximum extra capabilities per message (seL4_MsgMaxExtraCaps).
pub const MAX_EXTRA_CAPS: u64 = 3;

/// V2-H (M-API-3): Maximum label value: 2^20 - 1 (20 bits), matching seL4's
/// `seL4_MessageInfo_t` label field width.
///
/// Previously 2^55 - 1 (55 bits), which diverged from seL4's 20-bit limit.
/// The encode and decode methods now enforce this stricter bound.
pub const MAX_LABEL: u64 = (1u64 << 20) - 1;

// W6-G (LOW-1): Compile-time assertions ensuring Lean-Rust ABI constant sync.
// If `maxLabel`, `maxMessageRegisters`, or `maxExtraCaps` change on the Lean side
// (in `SeLe4n/Model/Object/Types.lean`), these assertions will fail at compile time,
// preventing silent divergence between the Lean model and Rust FFI layer.
const _: () = {
    assert!(MAX_LABEL == 1_048_575, "MAX_LABEL must be 2^20 - 1 (Lean: maxLabel)");
    assert!(MAX_MSG_LENGTH == 120, "MAX_MSG_LENGTH must be 120 (Lean: maxMessageRegisters)");
    assert!(MAX_EXTRA_CAPS == 3, "MAX_EXTRA_CAPS must be 3 (Lean: maxExtraCaps)");
};

/// Decoded message-info word, matching `seL4_MessageInfo_t`.
///
/// U3-B / U-M32: Fields are private to enforce construction through
/// validated paths (`new()` or `decode()`) only. Direct struct literal
/// construction is no longer possible, preventing silent truncation of
/// out-of-range values via bitmask in `encode()`.
///
/// Lean: `SeLe4n.Model.MessageInfo` (Types.lean:717)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MessageInfo {
    /// Number of message registers (0..=120).
    length: u8,
    /// Number of extra capability addresses (0..=3).
    extra_caps: u8,
    /// User-defined label (must fit in 20 bits: 0..=2^20-1; seL4 convention).
    label: u64,
}

impl MessageInfo {
    /// Create a new MessageInfo with bounds checking.
    ///
    /// Returns `InvalidMessageInfo` if length > 120, extraCaps > 3,
    /// or label >= 2^20.
    pub const fn new(length: u8, extra_caps: u8, label: u64) -> Result<Self, KernelError> {
        if length as u64 > MAX_MSG_LENGTH || extra_caps as u64 > MAX_EXTRA_CAPS || label > MAX_LABEL {
            Err(KernelError::InvalidMessageInfo)
        } else {
            Ok(Self { length, extra_caps, label })
        }
    }

    /// V1-D (M-RS-2): Infallible constructor for compile-time-known-valid
    /// arguments. Panics at compile time (const eval) if bounds are violated,
    /// but this can never happen for valid constant arguments.
    ///
    /// This replaces 13 `MessageInfo::new(...).unwrap()` calls in `sele4n-sys`
    /// where all arguments are known-valid constants (e.g., length ≤ 5,
    /// extra_caps = 0, label = 0).
    pub const fn new_const(length: u8, extra_caps: u8, label: u64) -> Self {
        assert!(length as u64 <= MAX_MSG_LENGTH, "length exceeds MAX_MSG_LENGTH");
        assert!(extra_caps as u64 <= MAX_EXTRA_CAPS, "extra_caps exceeds MAX_EXTRA_CAPS");
        assert!(label <= MAX_LABEL, "label exceeds MAX_LABEL");
        Self { length, extra_caps, label }
    }

    /// Number of message registers (0..=120).
    ///
    /// U3-B: Read-only accessor replacing the former `pub` field.
    #[inline]
    pub const fn length(&self) -> u8 { self.length }

    /// Number of extra capability addresses (0..=3).
    ///
    /// U3-B: Read-only accessor replacing the former `pub` field.
    #[inline]
    pub const fn extra_caps(&self) -> u8 { self.extra_caps }

    /// User-defined label (0..=2^20-1; seL4 20-bit convention).
    ///
    /// U3-B: Read-only accessor replacing the former `pub` field.
    #[inline]
    pub const fn label(&self) -> u64 { self.label }

    /// Encode into a single 64-bit register word.
    ///
    /// ## Bit layout (U3-H / U-L10)
    ///
    /// ```text
    /// 63         29 28                  9  8  7  6                  0
    /// ┌──────────┬────────────────────────┬────┬────────────────────┐
    /// │ reserved │    label (20 bits)     │ ec │  length (7 bits)   │
    /// └──────────┴────────────────────────┴────┴────────────────────┘
    ///              bits 9–28: label        7–8   bits 0–6: length
    ///              (user-defined)          extra_caps (2 bits)
    /// ```
    ///
    /// V2-H/M-API-3: Returns `InvalidMessageInfo` if `self.label >= 2^20`,
    /// matching seL4's 20-bit label field.
    ///
    /// Lean: `MessageInfo.encode` (Types.lean:737)
    #[inline]
    pub const fn encode(&self) -> Result<u64, KernelError> {
        if self.label > MAX_LABEL {
            return Err(KernelError::InvalidMessageInfo);
        }
        Ok((self.length as u64 & 0x7F)
            | ((self.extra_caps as u64 & 0x3) << 7)
            | (self.label << 9))
    }

    /// Decode a raw 64-bit word into MessageInfo.
    ///
    /// ## Bit layout (V2-H / M-API-3)
    ///
    /// ```text
    /// 63         29 28                  9  8  7  6                  0
    /// ┌──────────┬────────────────────────┬────┬────────────────────┐
    /// │ reserved │    label (20 bits)     │ ec │  length (7 bits)   │
    /// └──────────┴────────────────────────┴────┴────────────────────┘
    /// ```
    ///
    /// Returns `InvalidMessageInfo` if length > 120, extraCaps > 3, or
    /// label >= 2^20 (V2-H: enforces seL4's 20-bit label field).
    ///
    /// Lean: `MessageInfo.decode` (Types.lean:742)
    #[inline]
    pub const fn decode(raw: u64) -> Result<Self, KernelError> {
        let length = (raw & 0x7F) as u8;
        let extra_caps = ((raw >> 7) & 0x3) as u8;
        let label = raw >> 9;
        if length as u64 <= MAX_MSG_LENGTH && extra_caps as u64 <= MAX_EXTRA_CAPS && label <= MAX_LABEL {
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
        let mi = MessageInfo::new(42, 2, 0x1234).unwrap();
        let encoded = mi.encode().unwrap();
        let decoded = MessageInfo::decode(encoded).unwrap();
        assert_eq!(decoded, mi);
    }

    #[test]
    fn roundtrip_zero() {
        let mi = MessageInfo::new(0, 0, 0).unwrap();
        assert_eq!(MessageInfo::decode(mi.encode().unwrap()).unwrap(), mi);
    }

    #[test]
    fn roundtrip_max_valid() {
        let mi = MessageInfo::new(120, 3, 0xFFFF).unwrap();
        assert_eq!(MessageInfo::decode(mi.encode().unwrap()).unwrap(), mi);
    }

    #[test]
    fn decode_invalid_length() {
        // length = 127 (0x7F) > 120
        let raw: u64 = 127;
        assert_eq!(MessageInfo::decode(raw), Err(KernelError::InvalidMessageInfo));
    }

    #[test]
    fn bit_layout_length() {
        let mi = MessageInfo::new(42, 0, 0).unwrap();
        assert_eq!(mi.encode().unwrap(), 42);
    }

    #[test]
    fn bit_layout_extra_caps() {
        let mi = MessageInfo::new(0, 3, 0).unwrap();
        assert_eq!(mi.encode().unwrap(), 3 << 7);
    }

    #[test]
    fn bit_layout_label() {
        let mi = MessageInfo::new(0, 0, 5).unwrap();
        assert_eq!(mi.encode().unwrap(), 5 << 9);
    }

    #[test]
    fn new_bounds_check() {
        assert!(MessageInfo::new(120, 3, 0).is_ok());
        assert!(MessageInfo::new(121, 0, 0).is_err());
        assert!(MessageInfo::new(0, 4, 0).is_err());
    }

    // V2-H/M-API-3: Label bound enforcement tests (20-bit limit)
    #[test]
    fn new_rejects_oversized_label() {
        assert!(MessageInfo::new(0, 0, MAX_LABEL).is_ok());
        assert!(MessageInfo::new(0, 0, MAX_LABEL + 1).is_err());
        assert!(MessageInfo::new(0, 0, 1u64 << 20).is_err());
        assert!(MessageInfo::new(0, 0, u64::MAX).is_err());
    }

    #[test]
    fn encode_max_label_succeeds() {
        let mi = MessageInfo::new(0, 0, MAX_LABEL).unwrap();
        assert!(mi.encode().is_ok());
    }

    // V2-H: Decode also rejects oversized labels
    #[test]
    fn decode_rejects_oversized_label() {
        // Encode a raw word with label = 2^20 (just over the limit)
        let raw: u64 = (1u64 << 20) << 9; // label field starts at bit 9
        assert_eq!(MessageInfo::decode(raw), Err(KernelError::InvalidMessageInfo));
    }

    // U3-B: Accessor method tests
    #[test]
    fn accessor_methods() {
        let mi = MessageInfo::new(42, 2, 0x1234).unwrap();
        assert_eq!(mi.length(), 42);
        assert_eq!(mi.extra_caps(), 2);
        assert_eq!(mi.label(), 0x1234);
    }
}
