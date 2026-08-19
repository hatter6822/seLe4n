// SPDX-License-Identifier: GPL-3.0-or-later
//! Syscall response decoding — unpacks ARM64 registers into typed results.
//!
//! WS-RA: this is **the single decode point** for the seL4 return
//! convention (plan §3.2) — every `sele4n-sys` wrapper funnels through
//! [`decode_response`] via `invoke_syscall`:
//!
//! * `x0` — the primary return value: a full-width badge, a queried word,
//!   or `0` for `Unit`-returning syscalls.
//! * `x1` — a `MessageInfo` whose **label** carries the error status:
//!   label `0` = success, label `d + 1` = `KernelError` discriminant `d`
//!   (the `+ 1` offset exists because discriminant `0` is
//!   `InvalidCapability`, a real error — a direct-carriage label would
//!   alias it with success).
//! * `x2`-`x5` — message registers.
//!
//! The pre-WS-RA convention — `regs[0] != 0` *is* the error discriminant,
//! everything else the caller's own stale registers — is retired.

use crate::MessageInfo;
use sele4n_types::{Badge, KernelError, KernelResult};

/// A decoded successful syscall response.
///
/// Exists only on the success path: an error rides `Err(KernelError)` out
/// of [`decode_response`], so there is no vestigial error field (the
/// pre-WS-RA `error: Option<KernelError>` was `None` on every constructed
/// value).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyscallResponse {
    /// The primary return value from `x0` — full 64-bit width (the bit-63
    /// status flag is retired, so a badge may use every bit).
    x0: u64,
    /// The decoded `MessageInfo` from `x1`.  Its label is `0` here by
    /// construction (a nonzero label decoded as an `Err`).
    msg_info: MessageInfo,
    /// Message registers from x2–x5.
    pub msg_regs: [u64; 4],
}

/// Decode a 7-element register array into a `SyscallResponse`.
///
/// Layout: `[x0, x1, x2, x3, x4, x5, x7]`
///
/// Fail-closed twice over (the posture the retired `regs[0] > u32::MAX`
/// guard had, relocated to the register that now carries status):
/// an `x1` that does not decode as a well-formed `MessageInfo` (over-wide
/// label bits, out-of-range length/extraCaps) is `InvalidMessageInfo`,
/// and an in-range label naming an unknown discriminant collapses to
/// `UnknownKernelError` — either way an `Err`, never a false success.
#[inline]
pub fn decode_response(regs: [u64; 7]) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo::decode(regs[1]).map_err(|_| KernelError::InvalidMessageInfo)?;
    match msg_info.label() {
        0 => Ok(SyscallResponse {
            x0: regs[0],
            msg_info,
            msg_regs: [regs[2], regs[3], regs[4], regs[5]],
        }),
        label => {
            // The offset carriage: label `d + 1` names discriminant `d`.
            // The label is ≤ 20 bits by `MessageInfo::decode`, so the cast
            // cannot truncate a discriminant into a different one.
            let disc = (label - 1) as u32;
            Err(KernelError::from_u32(disc).unwrap_or(KernelError::UnknownKernelError))
        }
    }
}

impl SyscallResponse {
    /// The returned badge — read from **`x0`** (`.notificationWait`,
    /// `.receive`, `.call`, `.replyRecv`).  Pre-WS-RA this read `x1`,
    /// which the kernel never wrote back.
    pub fn badge(&self) -> Badge {
        Badge::from(self.x0)
    }

    /// The primary return value word from `x0` (`.serviceQuery`'s resolved
    /// `ServiceId`; `0` for `Unit`-returning syscalls).
    pub const fn value(&self) -> u64 {
        self.x0
    }

    /// The returned `MessageInfo` (its `length` is the delivered inline
    /// message-register count, `extraCaps` the transferred capability
    /// count; the label is `0` on every constructed response).
    pub const fn msg_info(&self) -> MessageInfo {
        self.msg_info
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The offset error label in `x1` position: discriminant → `(d+1) << 9`.
    fn error_x1(disc: u64) -> u64 {
        (disc + 1) << 9
    }

    #[test]
    fn decode_success_full_width_badge() {
        // WS-RA regression witness: a NONZERO x0 is a VALUE, not an error
        // — including one with bit 63 set, which the retired protocol
        // could not represent (encodeOk masked it).
        let badge = 0x8000_0000_0000_0042u64;
        let regs = [badge, 0, 1, 2, 3, 4, 0];
        let resp = decode_response(regs).unwrap();
        assert_eq!(resp.badge(), Badge::from(badge));
        assert_eq!(resp.value(), badge);
        assert_eq!(resp.msg_regs, [1, 2, 3, 4]);
        assert_eq!(resp.msg_info().label(), 0);
    }

    #[test]
    fn decode_success_message() {
        // x1 = MessageInfo { length 4, extraCaps 0, label 0 } = 4.
        let regs = [7, 4, 10, 20, 30, 40, 0];
        let resp = decode_response(regs).unwrap();
        assert_eq!(resp.value(), 7);
        assert_eq!(resp.msg_info().length(), 4);
        assert_eq!(resp.msg_regs, [10, 20, 30, 40]);
    }

    #[test]
    fn decode_error_rides_the_label() {
        // discriminant 1 = ObjectNotFound rides as label 2; x0 is 0 and
        // ignored.
        let regs = [0, error_x1(1), 0, 0, 0, 0, 0];
        assert_eq!(decode_response(regs), Err(KernelError::ObjectNotFound));
    }

    #[test]
    fn decode_discriminant_zero_does_not_alias_success() {
        // The reason the label is OFFSET: discriminant 0 is
        // InvalidCapability, a real error, and label 0 is success.
        let regs = [0, error_x1(0), 0, 0, 0, 0, 0];
        assert_eq!(decode_response(regs), Err(KernelError::InvalidCapability));
        // ... while a genuinely zero label is a success.
        assert!(decode_response([0, 0, 0, 0, 0, 0, 0]).is_ok());
    }

    #[test]
    fn decode_over_wide_x1_rejected() {
        // The fail-closed width check that replaced the retired
        // `regs[0] > u32::MAX` guard (RA.C.7): label bits beyond the
        // 20-bit field make x1 undecodable, never a silent truncation.
        let regs = [0, u64::MAX, 0, 0, 0, 0, 0];
        assert_eq!(decode_response(regs), Err(KernelError::InvalidMessageInfo));
    }

    #[test]
    fn decode_unknown_error_label() {
        // WS-SM SM9.C.1: 56 is DeclassificationDeniedAtReceiver.  The first
        // unrecognized discriminant is 57 (label 58) → UnknownKernelError,
        // still an Err — fail-closed.
        let regs = [0, error_x1(57), 0, 0, 0, 0, 0];
        assert_eq!(decode_response(regs), Err(KernelError::UnknownKernelError));
    }

    #[test]
    fn decode_declassification_denied_at_receiver_error() {
        // WS-SM SM9.C.1: discriminant 56 survives the label round trip.  The
        // distinction it carries is the whole reason it is not folded into
        // DeclassificationDenied: an unauthorized caller and an authorized
        // caller aimed at an unauthorized sink call for opposite responses.
        let regs = [0, error_x1(56), 0, 0, 0, 0, 0];
        assert_eq!(
            decode_response(regs),
            Err(KernelError::DeclassificationDeniedAtReceiver)
        );
    }

    #[test]
    fn decode_audit_field_too_large_error() {
        // WS-SM SM9.A.2: discriminant 55 survives the label round trip.  The
        // reader **refuses** a value too wide to export rather than truncating
        // it, so this discriminant is the difference between a monitor knowing
        // it did not get the value and silently reading a wrong one.
        let regs = [0, error_x1(55), 0, 0, 0, 0, 0];
        assert_eq!(decode_response(regs), Err(KernelError::AuditFieldTooLarge));
    }

    #[test]
    fn decode_missing_sched_context_error() {
        // R5.E (DEEP-SCH-04): discriminant 52 survives the label round trip.
        let regs = [0, error_x1(52), 0, 0, 0, 0, 0];
        assert_eq!(decode_response(regs), Err(KernelError::MissingSchedContext));
    }

    #[test]
    fn decode_thread_on_different_core_error() {
        // WS-SM SM5.B.4: discriminant 53 survives the label round trip.
        let regs = [0, error_x1(53), 0, 0, 0, 0, 0];
        assert_eq!(
            decode_response(regs),
            Err(KernelError::ThreadOnDifferentCore)
        );
    }

    #[test]
    fn decode_every_discriminant_roundtrips() {
        // RA.E.3 (Rust half): every KernelError discriminant 0..=54
        // survives the offset label round trip, by enumeration.
        for disc in 0..=54u32 {
            let expected = KernelError::from_u32(disc).expect("0..=54 are all valid");
            let regs = [0, error_x1(disc as u64), 0, 0, 0, 0, 0];
            assert_eq!(decode_response(regs), Err(expected), "discriminant {disc}");
        }
    }

    #[test]
    fn badge_and_value_read_x0() {
        // WS-RA: badge() reads x0 (pre-WS-RA it read x1, which the kernel
        // never wrote back — the SM9.C.0 defect's userspace half).
        let regs = [0xBEEF, 0, 0, 0, 0, 0, 0];
        let resp = decode_response(regs).unwrap();
        assert_eq!(resp.badge(), Badge::from(0xBEEFu64));
        assert_eq!(resp.value(), 0xBEEF);
    }
}
