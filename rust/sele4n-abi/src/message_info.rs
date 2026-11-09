// SPDX-License-Identifier: GPL-3.0-or-later
//! MessageInfo bitfield — matches `SeLe4n.Model.MessageInfo` encoding.
//!
//! Lean source: `SeLe4n/Model/Object/Types.lean` lines 717–860.
//!
//! Bit layout (seL4's `seL4_MessageInfo_t`):
//! - bits 0–6:   length (7 bits, max 120)
//! - bits 7–8:   extraCaps (2 bits, max 3)
//! - bits 9–11:  capsUnwrapped (3 bits, set by the kernel on delivery)
//! - bits 12–31: label (20 bits, user-defined)

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

// W6-G (LOW-1): compile-time pins on the three bounds' values.  They do NOT read
// the Lean model, so on their own they cannot notice a Lean-side change: what
// ties these constants — and the encoder's field layout — to
// `SeLe4n/Model/Object/Types.lean` is WS-BP BP0.3's shared table
// `tests/fixtures/abi_layout.expected`, which the Lean suite emits and
// `tests/conformance.rs::abi_layout_matches_the_lean_table` renders from this
// crate and compares byte for byte.
const _: () = {
    assert!(
        MAX_LABEL == 1_048_575,
        "MAX_LABEL must be 2^20 - 1 (Lean: maxLabel)"
    );
    assert!(
        MAX_MSG_LENGTH == 120,
        "MAX_MSG_LENGTH must be 120 (Lean: maxMessageRegisters)"
    );
    assert!(
        MAX_EXTRA_CAPS == 3,
        "MAX_EXTRA_CAPS must be 3 (Lean: maxExtraCaps)"
    );
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
    /// Which extra capabilities the kernel unwrapped to their badge on
    /// delivery (bit `i` for capability `i`), seL4's `capsUnwrapped`.  A
    /// sender's value is ignored by the kernel.
    caps_unwrapped: u8,
}

impl MessageInfo {
    /// Create a new MessageInfo with bounds checking.
    ///
    /// Returns `InvalidMessageInfo` if length > 120, extraCaps > 3,
    /// or label >= 2^20.
    pub const fn new(length: u8, extra_caps: u8, label: u64) -> Result<Self, KernelError> {
        if length as u64 > MAX_MSG_LENGTH || extra_caps as u64 > MAX_EXTRA_CAPS || label > MAX_LABEL
        {
            Err(KernelError::InvalidMessageInfo)
        } else {
            Ok(Self {
                length,
                extra_caps,
                label,
                caps_unwrapped: 0,
            })
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
        assert!(
            length as u64 <= MAX_MSG_LENGTH,
            "length exceeds MAX_MSG_LENGTH"
        );
        assert!(
            extra_caps as u64 <= MAX_EXTRA_CAPS,
            "extra_caps exceeds MAX_EXTRA_CAPS"
        );
        assert!(label <= MAX_LABEL, "label exceeds MAX_LABEL");
        Self {
            length,
            extra_caps,
            label,
            caps_unwrapped: 0,
        }
    }

    /// Number of message registers (0..=120).
    ///
    /// U3-B: Read-only accessor replacing the former `pub` field.
    #[inline]
    pub const fn length(&self) -> u8 {
        self.length
    }

    /// Number of extra capability addresses (0..=3).
    ///
    /// U3-B: Read-only accessor replacing the former `pub` field.
    #[inline]
    pub const fn extra_caps(&self) -> u8 {
        self.extra_caps
    }

    /// User-defined label (0..=2^20-1; seL4 20-bit convention).
    ///
    /// U3-B: Read-only accessor replacing the former `pub` field.
    #[inline]
    pub const fn label(&self) -> u64 {
        self.label
    }

    /// Which extra capabilities a delivery unwrapped to their badge (bit `i`
    /// for capability `i`); the badge is in the receiver's IPC buffer's
    /// `caps_or_badges[i]`.
    #[inline]
    pub const fn caps_unwrapped(&self) -> u8 {
        self.caps_unwrapped
    }

    /// Encode into a single 64-bit register word.
    ///
    /// ## Bit layout (U3-H / U-L10)
    ///
    /// ```text
    /// 63         32 31                 12 11  9  8  7  6                  0
    /// ┌──────────┬────────────────────────┬─────┬────┬────────────────────┐
    /// │ reserved │    label (20 bits)     │ cu  │ ec │  length (7 bits)   │
    /// └──────────┴────────────────────────┴─────┴────┴────────────────────┘
    ///              bits 12–31: label      9–11   7–8   bits 0–6: length
    ///                                     caps_unwrapped, extra_caps
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
            | ((self.caps_unwrapped as u64 & 0x7) << 9)
            | (self.label << 12))
    }

    /// Decode a raw 64-bit word into MessageInfo.
    ///
    /// ## Bit layout (V2-H / M-API-3)
    ///
    /// ```text
    /// 63         32 31                 12 11  9  8  7  6                  0
    /// ┌──────────┬────────────────────────┬─────┬────┬────────────────────┐
    /// │ reserved │    label (20 bits)     │ cu  │ ec │  length (7 bits)   │
    /// └──────────┴────────────────────────┴─────┴────┴────────────────────┘
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
        let caps_unwrapped = ((raw >> 9) & 0x7) as u8;
        let label = raw >> 12;
        if length as u64 <= MAX_MSG_LENGTH
            && extra_caps as u64 <= MAX_EXTRA_CAPS
            && label <= MAX_LABEL
        {
            Ok(Self {
                length,
                extra_caps,
                label,
                caps_unwrapped,
            })
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
        assert_eq!(
            MessageInfo::decode(raw),
            Err(KernelError::InvalidMessageInfo)
        );
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
        assert_eq!(mi.encode().unwrap(), 5 << 12);
    }

    #[test]
    fn caps_unwrapped_decodes_and_reencodes() {
        let raw: u64 = (0x1234 << 12) | (0b101 << 9) | (2 << 7) | 3;
        let mi = MessageInfo::decode(raw).unwrap();
        assert_eq!(mi.caps_unwrapped(), 0b101);
        assert_eq!(mi.extra_caps(), 2);
        assert_eq!(mi.label(), 0x1234);
        assert_eq!(mi.encode().unwrap(), raw);
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
        let raw: u64 = (1u64 << 20) << 12; // label field starts at bit 12
        assert_eq!(
            MessageInfo::decode(raw),
            Err(KernelError::InvalidMessageInfo)
        );
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
