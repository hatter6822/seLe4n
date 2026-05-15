// SPDX-License-Identifier: GPL-3.0-or-later
//! Host-side outcome decoding for the seLe4n syscall return contract.
//!
//! The verified Lean kernel emits its syscall return value through
//! the bit-63-flagged `UInt64` contract defined in
//! `SeLe4n.Platform.FFI.encodeOk` / `encodeError`:
//!
//! ```text
//!   bit 63        — error flag (1 = error, 0 = success)
//!   bits [62: 0]  — success payload  (when bit 63 == 0)
//!   bits [31: 0]  — KernelError discriminant (when bit 63 == 1)
//! ```
//!
//! On bare metal, `rust/sele4n-hal/src/svc_dispatch.rs::dispatch_svc`
//! decodes this contract for the kernel-side trap handler.  The
//! host runtime provides the **same decoding** so that off-target
//! integration tests (which capture the raw `UInt64` produced by a
//! Lean `lake exe` invocation, or by direct invocation of the
//! verified `syscallDispatchFromAbi` function) can interpret the
//! result without round-tripping through the HAL crate.
//!
//! ## Outcome shape
//!
//! [`DispatchOutcome`] has three variants:
//!
//! 1. [`DispatchOutcome::Ok`] — success.  The kernel's
//!    `encodeOk` masks bit 63, so the payload is the low 63 bits.
//! 2. [`DispatchOutcome::KernelError`] — the verified kernel
//!    rejected the syscall with a `KernelError` discriminant.
//! 3. [`DispatchOutcome::DispatcherInternal`] — the surrounding
//!    dispatcher rejected the syscall *before* the kernel saw it
//!    (invalid syscall id, malformed argument count, ABI mismatch).
//!    [`decode`](DispatchOutcome::decode) never produces this
//!    variant; callers construct it explicitly when the dispatcher
//!    itself raises an error.
//!
//! The split between `KernelError` and `DispatcherInternal` mirrors
//! the `sele4n-hal::svc_dispatch::DispatchError` shape so that
//! off-target tests can construct the same shape the on-target
//! handler emits.

use sele4n_types::KernelError;

/// Bit 63 of the kernel return-value contract.
///
/// Public so that downstream tests can construct a malformed return
/// value (e.g., `ERROR_FLAG_MASK | (KernelError as u32 as u64)`)
/// without duplicating the mask literal.  Equal to `1u64 << 63`.
pub const ERROR_FLAG_MASK: u64 = 1u64 << 63;

/// Mask for the 32-bit `KernelError` discriminant carried in the low
/// bits of an error-encoded return value.
///
/// Equal to `0x0000_0000_FFFF_FFFF`.
pub const ERROR_DISCRIMINANT_MASK: u64 = u32::MAX as u64;

/// Mask for the success payload's 63 bits.
///
/// Equal to `0x7FFF_FFFF_FFFF_FFFF`.
pub const SUCCESS_PAYLOAD_MASK: u64 = !ERROR_FLAG_MASK;

/// Host-side mirror of the kernel-side dispatch outcome.
///
/// See the module docstring for the bit-layout contract.  This type
/// is the **structured shape** that callers consume after decoding a
/// raw kernel return value; it is the host-runtime equivalent of
/// `sele4n-hal::svc_dispatch::Result<u64, DispatchError>`.
///
/// `#[non_exhaustive]` is applied for forward compatibility: later
/// WS-RH phases may add new variants (e.g., a host-side trap
/// surface for ahead-of-time validation failures).  External
/// `match` statements must include a wildcard arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DispatchOutcome {
    /// The kernel returned success.  The payload is the low 63 bits
    /// of the encoded return value.
    ///
    /// Per the kernel's `encodeOk` contract, bit 63 is always clear
    /// here; the payload is never `>= 2^63`.
    Ok(u64),
    /// The verified kernel rejected the syscall with the given
    /// `KernelError` discriminant.
    ///
    /// The wrapped [`KernelError`] is the structured variant — if the
    /// raw discriminant is outside the known 0..=52 range it decodes
    /// to [`KernelError::UnknownKernelError`] (the 255 sentinel).
    KernelError(KernelError),
    /// The surrounding dispatcher rejected the syscall before the
    /// kernel saw it.
    ///
    /// [`DispatchOutcome::decode`] never produces this variant; it is
    /// constructed at the dispatch seam by callers who model the
    /// host-side dispatch pipeline.  Mirrors
    /// `sele4n-hal::svc_dispatch::DispatchError::InvalidSyscallId`
    /// and `InvalidArgument`.
    DispatcherInternal(DispatcherInternalError),
}

/// Dispatcher-internal error variants.
///
/// These arise from host-side validation that runs **before** the
/// kernel sees the syscall.  They are not encoded in the kernel
/// return-value `UInt64` (the kernel never sees the syscall when
/// these fire); the dispatcher emits them locally.
///
/// `#[non_exhaustive]` is applied for forward compatibility: later
/// WS-RH phases may add new pre-kernel validation paths (e.g.,
/// capability-shape validation in RH-E).  External `match`
/// statements must include a wildcard arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum DispatcherInternalError {
    /// The caller passed a syscall id outside the valid 0..=24 range.
    ///
    /// Wire discriminant `7` (matches
    /// `sele4n-hal::svc_dispatch::DispatchError::InvalidSyscallId`).
    InvalidSyscallId,
    /// The caller passed an argument count that did not match the
    /// syscall's expected inline-arg minimum, or the
    /// `MessageInfo` failed structural validation.
    ///
    /// Wire discriminant `6` (matches
    /// `sele4n-hal::svc_dispatch::DispatchError::InvalidArgument`).
    InvalidArgument,
    /// The host-side dispatcher detected an ABI mismatch between the
    /// caller's view of the register layout and the kernel's expected
    /// layout (e.g., `msg_info != x1` per the post-WS-RC R2 ABI
    /// consistency gate).
    ///
    /// Wire discriminant equals
    /// `KernelError::InvalidSyscallArgument` (`41`), which is the
    /// canonical kernel-side discriminant for this condition; the
    /// host-side dispatcher emits the same discriminant for parity.
    AbiMismatch,
}

impl DispatcherInternalError {
    /// Wire-level `u32` discriminant the host-side dispatcher would
    /// write to `x0` on the syscall return path.
    ///
    /// Matches the on-target encoding produced by
    /// `sele4n-hal::svc_dispatch::DispatchError::to_u32`.
    #[inline]
    pub const fn to_u32(self) -> u32 {
        match self {
            DispatcherInternalError::InvalidSyscallId => 7,
            DispatcherInternalError::InvalidArgument => 6,
            // `KernelError::InvalidSyscallArgument` lives at
            // discriminant 41 per `rust/sele4n-types/src/error.rs`.
            // Re-using that discriminant keeps host-side and
            // kernel-side rejection codes aligned so user-mode sees
            // a single canonical "this argument is malformed"
            // signal regardless of which side caught it.
            DispatcherInternalError::AbiMismatch => 41,
        }
    }
}

impl DispatchOutcome {
    /// Decode a raw kernel return value into the structured outcome.
    ///
    /// Per the `SeLe4n.Platform.FFI` contract:
    ///
    /// - If bit 63 is set, the low 32 bits hold the `KernelError`
    ///   discriminant.  Discriminants outside the 0..=52 range
    ///   (other than the 255 sentinel) decode to
    ///   [`KernelError::UnknownKernelError`].
    /// - If bit 63 is clear, the value is the success payload.
    ///
    /// `decode` is total and infallible — every `u64` decodes to a
    /// well-formed `DispatchOutcome`.  Note that this function
    /// **never** produces [`DispatchOutcome::DispatcherInternal`];
    /// dispatcher-internal errors arise outside the kernel return
    /// path.
    pub const fn decode(raw: u64) -> Self {
        if (raw & ERROR_FLAG_MASK) != 0 {
            // Error path.  The low 32 bits are the discriminant.
            // `from_u32` returns Some for the 53 known variants
            // (0..=52) and Some(UnknownKernelError) for 255; any
            // other value maps to the sentinel.
            let disc = (raw & ERROR_DISCRIMINANT_MASK) as u32;
            let err = match KernelError::from_u32(disc) {
                Some(e) => e,
                None => KernelError::UnknownKernelError,
            };
            DispatchOutcome::KernelError(err)
        } else {
            // Success path.  Bit 63 is clear, so the value is itself
            // the payload.
            DispatchOutcome::Ok(raw)
        }
    }

    /// Encode the outcome back into a raw `u64`, matching the kernel
    /// contract.
    ///
    /// For [`DispatchOutcome::DispatcherInternal`] (which the kernel
    /// itself would never emit) the encoding falls back to the
    /// dispatcher-internal `u32` discriminant set with the error
    /// flag, so that round-trip through [`decode`](Self::decode)
    /// reproduces a well-formed `KernelError` outcome carrying the
    /// discriminant the dispatcher would have written on the wire.
    /// This is a documented one-way mapping:
    /// `DispatcherInternal(e).encode().decode()` does NOT reproduce
    /// the original `DispatcherInternal` variant; it produces a
    /// `KernelError` with the discriminant the dispatcher would
    /// have written on the wire.
    pub const fn encode(&self) -> u64 {
        match self {
            DispatchOutcome::Ok(payload) => *payload & SUCCESS_PAYLOAD_MASK,
            // `KernelError` is `#[repr(u32)]`, so the `as u64` cast
            // returns the discriminant value (e.g.,
            // `KernelError::IllegalState as u64 == 2`).  This is the
            // canonical way to extract a `#[repr(uN)]` enum's
            // discriminant per the Rust reference, and matches
            // `KernelError::from_u32`'s inverse mapping.
            DispatchOutcome::KernelError(e) => ERROR_FLAG_MASK | (*e as u64),
            DispatchOutcome::DispatcherInternal(d) => ERROR_FLAG_MASK | (d.to_u32() as u64),
        }
    }

    /// Returns `true` if the outcome is a kernel-side success.
    #[inline]
    pub const fn is_ok(&self) -> bool {
        matches!(self, DispatchOutcome::Ok(_))
    }

    /// Returns `true` if the outcome is a kernel-side error.
    #[inline]
    pub const fn is_kernel_error(&self) -> bool {
        matches!(self, DispatchOutcome::KernelError(_))
    }

    /// Returns `true` if the outcome is a dispatcher-internal error.
    #[inline]
    pub const fn is_dispatcher_internal(&self) -> bool {
        matches!(self, DispatchOutcome::DispatcherInternal(_))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_ok_zero() {
        assert_eq!(DispatchOutcome::decode(0), DispatchOutcome::Ok(0));
    }

    #[test]
    fn decode_ok_max_payload() {
        // 2^63 - 1 = 0x7FFF_FFFF_FFFF_FFFF — bit 63 clear.
        let raw = SUCCESS_PAYLOAD_MASK;
        assert_eq!(DispatchOutcome::decode(raw), DispatchOutcome::Ok(raw));
    }

    #[test]
    fn decode_error_invalid_capability() {
        let raw = ERROR_FLAG_MASK; // KernelError::InvalidCapability == 0
        assert_eq!(
            DispatchOutcome::decode(raw),
            DispatchOutcome::KernelError(KernelError::InvalidCapability)
        );
    }

    #[test]
    fn decode_error_max_known() {
        // KernelError::MissingSchedContext == 52 (post-WS-RC R5.E).
        let raw = ERROR_FLAG_MASK | 52;
        assert_eq!(
            DispatchOutcome::decode(raw),
            DispatchOutcome::KernelError(KernelError::MissingSchedContext)
        );
    }

    #[test]
    fn decode_error_sentinel() {
        let raw = ERROR_FLAG_MASK | 255; // UnknownKernelError sentinel
        assert_eq!(
            DispatchOutcome::decode(raw),
            DispatchOutcome::KernelError(KernelError::UnknownKernelError)
        );
    }

    #[test]
    fn decode_error_unknown_discriminant_routes_to_sentinel() {
        // 100 is in the unknown-discriminant gap (53..=254).
        let raw = ERROR_FLAG_MASK | 100;
        assert_eq!(
            DispatchOutcome::decode(raw),
            DispatchOutcome::KernelError(KernelError::UnknownKernelError)
        );
    }

    #[test]
    fn decode_total_for_all_known_discriminants() {
        // Sweep every known KernelError discriminant (0..=52).
        for disc in 0u32..=52 {
            let raw = ERROR_FLAG_MASK | u64::from(disc);
            let outcome = DispatchOutcome::decode(raw);
            match outcome {
                DispatchOutcome::KernelError(e) => {
                    assert_eq!(
                        KernelError::from_u32(disc),
                        Some(e),
                        "discriminant {disc} did not round-trip via from_u32"
                    );
                }
                _ => panic!("discriminant {disc} decoded outside the error path"),
            }
        }
    }

    #[test]
    fn encode_ok_clears_bit_63() {
        let outcome = DispatchOutcome::Ok(42);
        let raw = outcome.encode();
        assert_eq!(raw & ERROR_FLAG_MASK, 0);
        assert_eq!(raw, 42);
    }

    #[test]
    fn encode_ok_masks_high_bit() {
        // A payload with bit 63 set would corrupt the error flag;
        // encode masks it off, matching the Lean `encodeOk` contract.
        let outcome = DispatchOutcome::Ok(u64::MAX);
        let raw = outcome.encode();
        assert_eq!(raw & ERROR_FLAG_MASK, 0);
        assert_eq!(raw, SUCCESS_PAYLOAD_MASK);
    }

    #[test]
    fn encode_kernel_error_sets_bit_63() {
        let outcome = DispatchOutcome::KernelError(KernelError::IllegalState);
        let raw = outcome.encode();
        assert_eq!(raw & ERROR_FLAG_MASK, ERROR_FLAG_MASK);
        assert_eq!(raw & ERROR_DISCRIMINANT_MASK, 2); // IllegalState == 2
    }

    #[test]
    fn encode_dispatcher_internal_sets_bit_63() {
        for variant in [
            DispatcherInternalError::InvalidSyscallId,
            DispatcherInternalError::InvalidArgument,
            DispatcherInternalError::AbiMismatch,
        ] {
            let outcome = DispatchOutcome::DispatcherInternal(variant);
            let raw = outcome.encode();
            assert_eq!(raw & ERROR_FLAG_MASK, ERROR_FLAG_MASK);
            assert_eq!(raw & ERROR_DISCRIMINANT_MASK, u64::from(variant.to_u32()));
        }
    }

    #[test]
    fn round_trip_ok() {
        for v in [0u64, 1, 42, 1 << 30, SUCCESS_PAYLOAD_MASK] {
            let outcome = DispatchOutcome::Ok(v);
            assert_eq!(DispatchOutcome::decode(outcome.encode()), outcome);
        }
    }

    #[test]
    fn round_trip_known_kernel_errors() {
        let cases = [
            KernelError::InvalidCapability,
            KernelError::IllegalState,
            KernelError::PolicyDenied,
            KernelError::NotImplemented,
            KernelError::InvalidSyscallArgument,
            KernelError::MissingSchedContext,
            KernelError::UnknownKernelError,
        ];
        for e in cases {
            let outcome = DispatchOutcome::KernelError(e);
            assert_eq!(DispatchOutcome::decode(outcome.encode()), outcome);
        }
    }

    #[test]
    fn encode_known_kernel_errors_sweep_all_discriminants() {
        // Comprehensive encode-side sweep complementing
        // `decode_total_for_all_known_discriminants`: for every
        // discriminant 0..=52, construct the matching `KernelError`
        // via `from_u32`, encode the outcome, and verify the
        // resulting `u64` has bit 63 set AND its low 32 bits equal
        // the original discriminant.  This pins the round-trip
        // identity `from_u32(e as u32) == Some(e)` for every
        // variant.
        for disc in 0u32..=52 {
            let e = KernelError::from_u32(disc).expect("known discriminant");
            let outcome = DispatchOutcome::KernelError(e);
            let raw = outcome.encode();
            assert_eq!(
                raw & ERROR_FLAG_MASK,
                ERROR_FLAG_MASK,
                "discriminant {disc} did not set the error flag"
            );
            assert_eq!(
                raw & ERROR_DISCRIMINANT_MASK,
                u64::from(disc),
                "discriminant {disc} encode produced wrong low 32 bits"
            );
            // Full round-trip identity for the structured variant.
            assert_eq!(
                DispatchOutcome::decode(raw),
                outcome,
                "discriminant {disc} did not round-trip"
            );
        }
    }

    #[test]
    fn decode_u64_max_routes_to_unknown_kernel_error() {
        // u64::MAX has bit 63 set, so it enters the error path.
        // The low 32 bits are u32::MAX = 0xFFFF_FFFF, which is
        // outside the known 0..=52 + 255 range, so it routes to
        // UnknownKernelError.
        assert_eq!(
            DispatchOutcome::decode(u64::MAX),
            DispatchOutcome::KernelError(KernelError::UnknownKernelError)
        );
    }

    #[test]
    fn decode_ignores_bits_32_through_62_on_error_path() {
        // Per the encodeError contract, the high bits 32..=62 are
        // always zero on emit (the discriminant fits in u32).  A
        // malformed caller might still send bits 32..=62 set; the
        // decoder ignores them and extracts only the low 32 bits.
        // This matches the HAL dispatcher's `raw as u32` truncation.
        //
        // Construct `raw = ERROR_FLAG_MASK | (junk << 32) | disc`
        // and verify decode produces the variant for `disc`,
        // ignoring the junk in bits 32..=62.
        let disc: u64 = 2; // IllegalState
        let junk_high: u64 = 0xFFFF; // bits 32..=47 set
        let raw = ERROR_FLAG_MASK | (junk_high << 32) | disc;
        // raw == 0x8000_FFFF_0000_0002; low 32 == 0x0000_0002 == 2
        assert_eq!(raw & ERROR_DISCRIMINANT_MASK, disc);
        let outcome = DispatchOutcome::decode(raw);
        assert_eq!(
            outcome,
            DispatchOutcome::KernelError(KernelError::IllegalState)
        );
    }

    #[test]
    fn dispatcher_internal_to_u32_aligns_with_hal_legacy_discriminants() {
        assert_eq!(DispatcherInternalError::InvalidSyscallId.to_u32(), 7);
        assert_eq!(DispatcherInternalError::InvalidArgument.to_u32(), 6);
        // AbiMismatch uses the canonical KernelError::InvalidSyscallArgument
        // discriminant (41), since the kernel-side variant exists and the
        // host emits the same wire value.
        assert_eq!(DispatcherInternalError::AbiMismatch.to_u32(), 41);
    }

    #[test]
    fn predicates_partition_outcome_space() {
        let ok = DispatchOutcome::Ok(1);
        assert!(ok.is_ok());
        assert!(!ok.is_kernel_error());
        assert!(!ok.is_dispatcher_internal());

        let kerr = DispatchOutcome::KernelError(KernelError::IllegalState);
        assert!(!kerr.is_ok());
        assert!(kerr.is_kernel_error());
        assert!(!kerr.is_dispatcher_internal());

        let disp = DispatchOutcome::DispatcherInternal(DispatcherInternalError::InvalidSyscallId);
        assert!(!disp.is_ok());
        assert!(!disp.is_kernel_error());
        assert!(disp.is_dispatcher_internal());
    }

    #[test]
    fn dispatcher_internal_variants_are_distinct() {
        let v = [
            DispatcherInternalError::InvalidSyscallId,
            DispatcherInternalError::InvalidArgument,
            DispatcherInternalError::AbiMismatch,
        ];
        for i in 0..v.len() {
            for j in (i + 1)..v.len() {
                assert_ne!(v[i], v[j], "variants {i} and {j} are equal");
                assert_ne!(
                    v[i].to_u32(),
                    v[j].to_u32(),
                    "variants {i} and {j} share a wire discriminant",
                );
            }
        }
    }

    #[test]
    fn const_decode_works_at_compile_time() {
        // Verify that `decode` is callable in a `const` context.
        const OK_OUTCOME: DispatchOutcome = DispatchOutcome::decode(7);
        const ERR_OUTCOME: DispatchOutcome = DispatchOutcome::decode(ERROR_FLAG_MASK | 2);
        assert_eq!(OK_OUTCOME, DispatchOutcome::Ok(7));
        assert_eq!(
            ERR_OUTCOME,
            DispatchOutcome::KernelError(KernelError::IllegalState)
        );
    }

    #[test]
    fn const_encode_works_at_compile_time() {
        // Verify that `encode` is callable in a `const` context.
        const RAW: u64 = DispatchOutcome::Ok(42).encode();
        const ERR_RAW: u64 = DispatchOutcome::KernelError(KernelError::IllegalState).encode();
        assert_eq!(RAW, 42);
        assert_eq!(ERR_RAW, ERROR_FLAG_MASK | 2);
    }
}
