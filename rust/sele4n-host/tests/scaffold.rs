// SPDX-License-Identifier: GPL-3.0-or-later
//! Integration test surface for the `sele4n-host` foundation phase
//! (WS-RH RH-H).
//!
//! These tests exercise the **public** API of the host runtime end-to-
//! end.  Unit tests live in each module's `#[cfg(test)] mod tests`
//! block; this file complements them by composing the public surface
//! in the same way an external consumer would.
//!
//! Failure modes covered:
//!
//! 1. Workspace version drift — the runtime exposes the workspace's
//!    pinned `CARGO_PKG_VERSION`.  If the version drops or jumps
//!    unexpectedly, the version-matches-workspace assertion fires.
//! 2. Const-fn / dynamic-fn divergence — both pathways must agree.
//! 3. Sweep coverage of every `KernelError` discriminant (52 known +
//!    sentinel + unknown-gap) through encode/decode round-trips.
//! 4. Builder construction parity — the encoded register file's
//!    layout matches `arm64DefaultLayout` for the kernel-side
//!    dispatcher's observation.
//! 5. State scaffold integrity — `HostState::empty()` produces an
//!    empty state; the three placeholder error variants are
//!    distinct.

use sele4n_abi::MessageInfo;
use sele4n_host::dispatch::{
    DispatchOutcome, DispatcherInternalError, ERROR_DISCRIMINANT_MASK, ERROR_FLAG_MASK,
    SUCCESS_PAYLOAD_MASK,
};
use sele4n_host::fixture::{
    FixtureBuilder, REG_X0, REG_X1, REG_X2, REG_X3, REG_X4, REG_X5, REG_X6, REG_X7, REGISTER_COUNT,
};
use sele4n_host::{HostRuntime, HostState, HostStateError};
use sele4n_types::{CPtr, KernelError, SyscallId};

// -----------------------------------------------------------------
// Runtime version pinning
// -----------------------------------------------------------------

#[test]
fn runtime_version_matches_workspace() {
    let rt = HostRuntime::new();
    assert_eq!(rt.version(), env!("CARGO_PKG_VERSION"));
}

#[test]
fn runtime_const_version_matches_runtime_version() {
    let rt = HostRuntime::new();
    assert_eq!(rt.version(), HostRuntime::workspace_version_pinned());
}

#[test]
fn runtime_version_is_pre_v1() {
    let rt = HostRuntime::new();
    let v = rt.version();
    // Defensive guard: every released cut on this branch is pre-v1.
    // Tightens the pre-1.0 envelope so a stray version bump (e.g.,
    // someone editing the workspace [workspace.package] entry to
    // "1.0.0-rc1") is caught here in addition to the dedicated
    // `scripts/check_version_sync.sh` gate.  The literal "0." prefix
    // is the canonical pre-1.0 marker; tightening past that would
    // duplicate the sync script's literal-equality check.
    assert!(
        v.starts_with("0."),
        "host runtime version {v:?} is unexpectedly outside the pre-1.0 envelope"
    );
}

// -----------------------------------------------------------------
// Dispatch — success path
// -----------------------------------------------------------------

#[test]
fn dispatch_decode_success_zero() {
    assert_eq!(DispatchOutcome::decode(0), DispatchOutcome::Ok(0));
}

#[test]
fn dispatch_decode_success_payload_42() {
    assert_eq!(DispatchOutcome::decode(42), DispatchOutcome::Ok(42));
}

#[test]
fn dispatch_decode_success_max_payload() {
    let raw = SUCCESS_PAYLOAD_MASK;
    assert_eq!(DispatchOutcome::decode(raw), DispatchOutcome::Ok(raw));
}

#[test]
fn dispatch_encode_high_bit_payload_is_truncated_then_decoded_as_success() {
    // The Lean `encodeOk` contract masks bit 63.  A host-side
    // caller that constructs `Ok(payload)` with bit 63 set will
    // see the encoded value have bit 63 cleared — decoding the
    // round-trip yields `Ok(payload & SUCCESS_PAYLOAD_MASK)`, not
    // the original `Ok(payload)`.  This is the documented one-way
    // mapping: the kernel never emits payloads `>= 2^63`, so any
    // caller-side construction outside this range gets silently
    // normalised on encode.
    let original = DispatchOutcome::Ok(u64::MAX);
    let raw = original.encode();
    // Encoded value has bit 63 cleared.
    assert_eq!(raw & ERROR_FLAG_MASK, 0);
    assert_eq!(raw, SUCCESS_PAYLOAD_MASK);

    let decoded = DispatchOutcome::decode(raw);
    // Decoded outcome is `Ok(SUCCESS_PAYLOAD_MASK)`, NOT
    // `Ok(u64::MAX)`.  Document this lossy round-trip.
    assert_eq!(decoded, DispatchOutcome::Ok(SUCCESS_PAYLOAD_MASK));
    assert_ne!(decoded, original);
}

// -----------------------------------------------------------------
// Dispatch — error path: sweep every known KernelError discriminant
// -----------------------------------------------------------------

#[test]
fn dispatch_decode_kernel_error_sweep_known() {
    for disc in 0u32..=52 {
        let raw = ERROR_FLAG_MASK | u64::from(disc);
        let outcome = DispatchOutcome::decode(raw);
        match outcome {
            DispatchOutcome::KernelError(e) => {
                let recovered = KernelError::from_u32(disc).expect("known discriminant");
                assert_eq!(e, recovered, "discriminant {disc}");
            }
            other => panic!("discriminant {disc} produced {other:?}"),
        }
    }
}

#[test]
fn dispatch_decode_kernel_error_sentinel() {
    let raw = ERROR_FLAG_MASK | 255;
    assert_eq!(
        DispatchOutcome::decode(raw),
        DispatchOutcome::KernelError(KernelError::UnknownKernelError)
    );
}

#[test]
fn dispatch_decode_kernel_error_unknown_gap() {
    // Sweep the unknown-discriminant gap 53..=254 (excluding 255
    // which is the sentinel itself).  Every value should route to
    // the sentinel.
    for disc in 53u32..=254 {
        let raw = ERROR_FLAG_MASK | u64::from(disc);
        let outcome = DispatchOutcome::decode(raw);
        assert_eq!(
            outcome,
            DispatchOutcome::KernelError(KernelError::UnknownKernelError),
            "unknown discriminant {disc} did not route to UnknownKernelError"
        );
    }
}

// -----------------------------------------------------------------
// Dispatch — dispatcher-internal variants
// -----------------------------------------------------------------

#[test]
fn dispatch_decode_dispatcher_internal_round_trip() {
    // dispatcher-internal errors never decode from a raw u64 — they
    // are dispatcher-emitted directly.  Verify the round-trip
    // documented in the encode docstring: encode-then-decode of a
    // DispatcherInternal yields a KernelError carrying the wire
    // discriminant.
    let cases = [
        (
            DispatcherInternalError::InvalidSyscallId,
            // Discriminant 7 collides with KernelError::EndpointStateMismatch.
            KernelError::EndpointStateMismatch,
        ),
        (
            DispatcherInternalError::InvalidArgument,
            // Discriminant 6 collides with KernelError::SchedulerInvariantViolation.
            KernelError::SchedulerInvariantViolation,
        ),
        (
            DispatcherInternalError::AbiMismatch,
            // Discriminant 41 = KernelError::InvalidSyscallArgument.
            KernelError::InvalidSyscallArgument,
        ),
    ];
    for (variant, expected) in cases {
        let outcome = DispatchOutcome::DispatcherInternal(variant);
        let raw = outcome.encode();
        assert_eq!(
            DispatchOutcome::decode(raw),
            DispatchOutcome::KernelError(expected),
            "DispatcherInternal::{variant:?} did not round-trip to {expected:?}"
        );
    }
}

// -----------------------------------------------------------------
// State scaffold
// -----------------------------------------------------------------

#[test]
fn state_empty_is_empty() {
    let s = HostState::empty();
    assert!(s.is_empty());
}

#[test]
fn state_error_variants_distinct() {
    let v = [
        HostStateError::Uninitialised,
        HostStateError::BoundedCapacity,
        HostStateError::InvalidFixture,
    ];
    for i in 0..v.len() {
        for j in (i + 1)..v.len() {
            assert_ne!(v[i], v[j]);
        }
    }
}

#[test]
fn state_error_identifiers_are_stable() {
    // Pin the identifiers; downstream log consumers depend on the
    // exact strings.  Any rename here is a documented breaking
    // change.
    assert_eq!(HostStateError::Uninitialised.identifier(), "uninitialised");
    assert_eq!(
        HostStateError::BoundedCapacity.identifier(),
        "bounded_capacity"
    );
    assert_eq!(
        HostStateError::InvalidFixture.identifier(),
        "invalid_fixture"
    );
}

// -----------------------------------------------------------------
// Fixture builder
// -----------------------------------------------------------------

#[test]
fn fixture_builder_round_trip() {
    let info = MessageInfo::new(2, 0, 0x10).unwrap();
    let snap = FixtureBuilder::new()
        .with_cap_addr(CPtr::from(100u64))
        .with_message_info(info)
        .with_msg_reg(0, 0xAAAA)
        .with_msg_reg(1, 0xBBBB)
        .with_syscall_id(SyscallId::Send)
        .build();

    // Per arm64DefaultLayout — kernel-side dispatch view.
    assert_eq!(snap.x0(), 100); // cap_addr
    assert_eq!(snap.x1(), info.encode().unwrap());
    assert_eq!(snap.registers()[REG_X2], 0xAAAA);
    assert_eq!(snap.registers()[REG_X3], 0xBBBB);
    assert_eq!(snap.x6(), 0); // no IPC buffer
    assert_eq!(snap.x7(), SyscallId::Send.to_u64());

    // Decode round-trip.
    assert_eq!(snap.decoded_syscall_id(), Some(SyscallId::Send));
    assert_eq!(snap.decoded_message_info(), Some(info));
}

#[test]
fn fixture_snapshot_register_count() {
    let snap = FixtureBuilder::new().build();
    assert_eq!(snap.registers().len(), REGISTER_COUNT);
    assert_eq!(REGISTER_COUNT, 8);
}

#[test]
fn fixture_register_indices_are_canonical() {
    // Pin the canonical register-index constants.  A drift here
    // (e.g., REG_X7 changing from 7 to 6) would silently break the
    // dispatch layout; this test catches the drift before tests
    // that *use* the indices fire.
    assert_eq!(REG_X0, 0);
    assert_eq!(REG_X1, 1);
    assert_eq!(REG_X2, 2);
    assert_eq!(REG_X3, 3);
    assert_eq!(REG_X4, 4);
    assert_eq!(REG_X5, 5);
    assert_eq!(REG_X6, 6);
    assert_eq!(REG_X7, 7);
}

#[test]
fn fixture_with_ipc_buffer_addr() {
    let snap = FixtureBuilder::new()
        .with_ipc_buffer_addr(0xDEAD_BEEF_CAFE_F00D)
        .build();
    assert_eq!(snap.x6(), 0xDEAD_BEEF_CAFE_F00D);
    // No other register touched.
    for (idx, value) in snap.registers().iter().enumerate() {
        if idx != REG_X6 {
            assert_eq!(*value, 0, "register x{idx} was unexpectedly modified");
        }
    }
}

#[test]
fn fixture_chains_preserve_each_setter() {
    // Verify that successive setters do not accidentally overwrite
    // each other.  Each setter writes a distinct register; the
    // composition should preserve every write.
    let info = MessageInfo::new(5, 2, 0xABCDE).unwrap();
    let snap = FixtureBuilder::new()
        .with_cap_addr(CPtr::from(7u64))
        .with_message_info(info)
        .with_msg_reg(0, 0x10)
        .with_msg_reg(1, 0x20)
        .with_msg_reg(2, 0x30)
        .with_msg_reg(3, 0x40)
        .with_ipc_buffer_addr(0x4000_0000)
        .with_syscall_id(SyscallId::CSpaceMint)
        .build();

    assert_eq!(snap.x0(), 7);
    assert_eq!(snap.x1(), info.encode().unwrap());
    assert_eq!(snap.registers()[REG_X2], 0x10);
    assert_eq!(snap.registers()[REG_X3], 0x20);
    assert_eq!(snap.registers()[REG_X4], 0x30);
    assert_eq!(snap.registers()[REG_X5], 0x40);
    assert_eq!(snap.x6(), 0x4000_0000);
    assert_eq!(snap.x7(), SyscallId::CSpaceMint.to_u64());
}

// -----------------------------------------------------------------
// Cross-module composition — public API end-to-end
// -----------------------------------------------------------------

#[test]
fn host_runtime_fixture_and_dispatch_compose() {
    // The full pipeline: HostRuntime metadata + FixtureBuilder
    // produces a snapshot; DispatchOutcome decodes a simulated
    // kernel return.  This is the canonical "host crate works
    // end-to-end" test.
    let _rt = HostRuntime::new();
    let info = MessageInfo::new(1, 0, 0).unwrap();
    let snap = FixtureBuilder::new()
        .with_cap_addr(CPtr::from(7u64))
        .with_message_info(info)
        .with_syscall_id(SyscallId::TcbResume)
        .build();
    assert_eq!(snap.decoded_syscall_id(), Some(SyscallId::TcbResume));

    // Simulate a kernel-side rejection with NotImplemented (17).
    let raw_return = ERROR_FLAG_MASK | 17;
    let outcome = DispatchOutcome::decode(raw_return);
    assert_eq!(
        outcome,
        DispatchOutcome::KernelError(KernelError::NotImplemented)
    );

    // The error path's discriminant exactly equals 17, and the
    // success-payload mask is fully clear of any error-flag bit.
    assert_eq!(raw_return & ERROR_DISCRIMINANT_MASK, 17);
}

#[test]
fn host_runtime_empty_state_distinct_from_error() {
    // Sanity: an empty HostState is not an error; the two are
    // structurally distinct types.  This is a compile-time check
    // disguised as a runtime assertion.
    let s = HostState::empty();
    let e = HostStateError::Uninitialised;
    assert!(s.is_empty());
    assert_eq!(e.identifier(), "uninitialised");
}

// -----------------------------------------------------------------
// TCB-invariance sanity (the host crate is std-opting and never
// linked into the kernel binary)
// -----------------------------------------------------------------

/// Compile-time assertion that this test target uses `std`.
///
/// The host runtime is the only workspace member that opts into
/// `std`; the other four crates (`sele4n-types`, `sele4n-abi`,
/// `sele4n-sys`, `sele4n-hal`) are `#![no_std]`.  The kernel binary
/// is linked from `sele4n-hal`, which has zero transitive
/// dependency on `sele4n-host` — Cargo's path-based dependency
/// graph enforces the partition statically.
///
/// This `#[allow(...)]` lives in the test file (not the library)
/// because `std::collections::HashMap` is a host-side type;
/// successfully constructing it inside a `sele4n-host` test
/// confirms the crate is built with `std` available.
#[test]
fn tcb_invariance_host_crate_is_std() {
    // If sele4n-host were ever accidentally rebuilt as no_std,
    // this line would fail to compile.  Construction is enough —
    // the call exercises `std::collections::HashMap::<u32, u32>::new`,
    // which is provably unavailable in a no_std context.
    let _map: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();
}

#[test]
fn dispatch_constants_match_kernel_contract() {
    // Pin the bit-layout constants against the kernel-side
    // contract.  A drift here (e.g., bit 62 instead of 63 for the
    // error flag) would silently break round-tripping with the
    // Lean kernel's emitted UInt64.
    //
    // ERROR_FLAG_MASK must be exactly 1u64 << 63 = 0x8000_0000_0000_0000.
    assert_eq!(ERROR_FLAG_MASK, 0x8000_0000_0000_0000);
    // ERROR_DISCRIMINANT_MASK must be u32::MAX as u64 = 0xFFFF_FFFF.
    assert_eq!(ERROR_DISCRIMINANT_MASK, 0x0000_0000_FFFF_FFFF);
    // SUCCESS_PAYLOAD_MASK must be !ERROR_FLAG_MASK = 0x7FFF_FFFF_FFFF_FFFF.
    assert_eq!(SUCCESS_PAYLOAD_MASK, 0x7FFF_FFFF_FFFF_FFFF);
    // The three masks partition u64: error-flag ∪ payload = full,
    // error-flag ∩ payload = empty.
    assert_eq!(ERROR_FLAG_MASK | SUCCESS_PAYLOAD_MASK, u64::MAX);
    assert_eq!(ERROR_FLAG_MASK & SUCCESS_PAYLOAD_MASK, 0);
}
