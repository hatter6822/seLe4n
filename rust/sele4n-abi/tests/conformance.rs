//! Register-by-register ABI conformance tests.
//!
//! RUST-XVAL-001 through RUST-XVAL-019: Validates that Rust encoding matches
//! the Lean decode layer register-by-register.
//!
//! These tests verify the exact register contents produced by each Rust encode
//! function against the expected layout defined in the Lean ABI specification:
//!
//! - `SeLe4n/Kernel/Architecture/RegisterDecode.lean`
//! - `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`

use sele4n_types::*;
use sele4n_abi::*;
use sele4n_abi::args::{cspace, lifecycle, vspace, service, TypeTag, PagePerms};

/// Helper: encode a syscall request and verify register contents.
fn verify_regs(req: &SyscallRequest, expected: &[(usize, u64, &str)]) {
    let regs = encode_syscall(req);
    for &(idx, expected_val, name) in expected {
        assert_eq!(
            regs[idx], expected_val,
            "Register index {} ({}) mismatch: got {}, expected {}",
            idx, name, regs[idx], expected_val
        );
    }
}

// ============================================================================
// IPC syscalls (RUST-XVAL-001 through RUST-XVAL-004)
// ============================================================================

/// RUST-XVAL-001: Endpoint send register layout.
#[test]
fn xval_001_endpoint_send() {
    let req = SyscallRequest {
        cap_addr: CPtr::from(100u64),
        msg_info: MessageInfo { length: 2, extra_caps: 0, label: 0x10 },
        msg_regs: [0xAAAA, 0xBBBB, 0, 0],
        syscall_id: SyscallId::Send,
    };
    verify_regs(&req, &[
        (0, 100, "x0=CPtr"),
        (1, 2 | (0x10 << 9), "x1=MessageInfo"),
        (2, 0xAAAA, "x2=msg_reg[0]"),
        (3, 0xBBBB, "x3=msg_reg[1]"),
        (6, 0, "x7=SyscallId::Send"),
    ]);
}

/// RUST-XVAL-002: Endpoint receive register layout.
#[test]
fn xval_002_endpoint_receive() {
    let req = SyscallRequest {
        cap_addr: CPtr::from(200u64),
        msg_info: MessageInfo { length: 0, extra_caps: 0, label: 0 },
        msg_regs: [0; 4],
        syscall_id: SyscallId::Receive,
    };
    verify_regs(&req, &[
        (0, 200, "x0=CPtr"),
        (1, 0, "x1=MessageInfo(empty)"),
        (6, 1, "x7=SyscallId::Receive"),
    ]);
}

/// RUST-XVAL-003: Endpoint call register layout.
#[test]
fn xval_003_endpoint_call() {
    let req = SyscallRequest {
        cap_addr: CPtr::from(300u64),
        msg_info: MessageInfo { length: 1, extra_caps: 0, label: 42 },
        msg_regs: [0xDEAD, 0, 0, 0],
        syscall_id: SyscallId::Call,
    };
    verify_regs(&req, &[
        (0, 300, "x0=CPtr"),
        (1, 1 | (42 << 9), "x1=MessageInfo"),
        (2, 0xDEAD, "x2=msg_reg[0]"),
        (6, 2, "x7=SyscallId::Call"),
    ]);
}

/// RUST-XVAL-004: Endpoint reply register layout.
#[test]
fn xval_004_endpoint_reply() {
    let req = SyscallRequest {
        cap_addr: CPtr::from(400u64),
        msg_info: MessageInfo { length: 0, extra_caps: 0, label: 0 },
        msg_regs: [0; 4],
        syscall_id: SyscallId::Reply,
    };
    verify_regs(&req, &[
        (0, 400, "x0=CPtr"),
        (6, 3, "x7=SyscallId::Reply"),
    ]);
}

// ============================================================================
// CSpace syscalls (RUST-XVAL-005 through RUST-XVAL-008)
// ============================================================================

/// RUST-XVAL-005: CSpace mint register layout.
#[test]
fn xval_005_cspace_mint() {
    let args = cspace::CSpaceMintArgs {
        src_slot: Slot::from(10u64),
        dst_slot: Slot::from(20u64),
        rights: AccessRights::from(0x07u8), // read|write|grant
        badge: Badge::from(999u64),
    };
    let encoded = args.encode();
    let req = SyscallRequest {
        cap_addr: CPtr::from(500u64),
        msg_info: MessageInfo { length: 4, extra_caps: 0, label: 0 },
        msg_regs: encoded,
        syscall_id: SyscallId::CSpaceMint,
    };
    verify_regs(&req, &[
        (0, 500, "x0=CPtr"),
        (2, 10, "x2=srcSlot"),
        (3, 20, "x3=dstSlot"),
        (4, 0x07, "x4=rights"),
        (5, 999, "x5=badge"),
        (6, 4, "x7=SyscallId::CSpaceMint"),
    ]);
}

/// RUST-XVAL-006: CSpace copy register layout.
#[test]
fn xval_006_cspace_copy() {
    let args = cspace::CSpaceCopyArgs { src_slot: Slot::from(5u64), dst_slot: Slot::from(15u64) };
    let encoded = args.encode();
    let req = SyscallRequest {
        cap_addr: CPtr::from(600u64),
        msg_info: MessageInfo { length: 2, extra_caps: 0, label: 0 },
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::CSpaceCopy,
    };
    verify_regs(&req, &[
        (2, 5, "x2=srcSlot"),
        (3, 15, "x3=dstSlot"),
        (6, 5, "x7=SyscallId::CSpaceCopy"),
    ]);
}

/// RUST-XVAL-007: CSpace move register layout.
#[test]
fn xval_007_cspace_move() {
    let args = cspace::CSpaceMoveArgs { src_slot: Slot::from(7u64), dst_slot: Slot::from(14u64) };
    let encoded = args.encode();
    let req = SyscallRequest {
        cap_addr: CPtr::from(700u64),
        msg_info: MessageInfo { length: 2, extra_caps: 0, label: 0 },
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::CSpaceMove,
    };
    verify_regs(&req, &[
        (2, 7, "x2=srcSlot"),
        (3, 14, "x3=dstSlot"),
        (6, 6, "x7=SyscallId::CSpaceMove"),
    ]);
}

/// RUST-XVAL-008: CSpace delete register layout.
#[test]
fn xval_008_cspace_delete() {
    let args = cspace::CSpaceDeleteArgs { target_slot: Slot::from(99u64) };
    let encoded = args.encode();
    let req = SyscallRequest {
        cap_addr: CPtr::from(800u64),
        msg_info: MessageInfo { length: 1, extra_caps: 0, label: 0 },
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::CSpaceDelete,
    };
    verify_regs(&req, &[
        (2, 99, "x2=targetSlot"),
        (6, 7, "x7=SyscallId::CSpaceDelete"),
    ]);
}

// ============================================================================
// Lifecycle syscall (RUST-XVAL-009)
// ============================================================================

/// RUST-XVAL-009: Lifecycle retype register layout.
#[test]
fn xval_009_lifecycle_retype() {
    let args = lifecycle::LifecycleRetypeArgs {
        target_obj: ObjId::from(42u64),
        new_type: 2, // Notification
        size: 0,
    };
    let encoded = args.encode();
    let req = SyscallRequest {
        cap_addr: CPtr::from(900u64),
        msg_info: MessageInfo { length: 3, extra_caps: 0, label: 0 },
        msg_regs: [encoded[0], encoded[1], encoded[2], 0],
        syscall_id: SyscallId::LifecycleRetype,
    };
    verify_regs(&req, &[
        (2, 42, "x2=targetObj"),
        (3, 2, "x3=newType(Notification)"),
        (4, 0, "x4=size"),
        (6, 8, "x7=SyscallId::LifecycleRetype"),
    ]);
}

// ============================================================================
// VSpace syscalls (RUST-XVAL-010 through RUST-XVAL-011)
// ============================================================================

/// RUST-XVAL-010: VSpace map register layout.
#[test]
fn xval_010_vspace_map() {
    let args = vspace::VSpaceMapArgs {
        asid: Asid::from(1u64),
        vaddr: VAddr::from(0x1000u64),
        paddr: PAddr::from(0x2000u64),
        perms: 0x05, // read|execute
    };
    let encoded = args.encode();
    let req = SyscallRequest {
        cap_addr: CPtr::from(1000u64),
        msg_info: MessageInfo { length: 4, extra_caps: 0, label: 0 },
        msg_regs: encoded,
        syscall_id: SyscallId::VSpaceMap,
    };
    verify_regs(&req, &[
        (2, 1, "x2=asid"),
        (3, 0x1000, "x3=vaddr"),
        (4, 0x2000, "x4=paddr"),
        (5, 0x05, "x5=perms"),
        (6, 9, "x7=SyscallId::VSpaceMap"),
    ]);
}

/// RUST-XVAL-011: VSpace unmap register layout.
#[test]
fn xval_011_vspace_unmap() {
    let args = vspace::VSpaceUnmapArgs { asid: Asid::from(2u64), vaddr: VAddr::from(0x3000u64) };
    let encoded = args.encode();
    let req = SyscallRequest {
        cap_addr: CPtr::from(1100u64),
        msg_info: MessageInfo { length: 2, extra_caps: 0, label: 0 },
        msg_regs: [encoded[0], encoded[1], 0, 0],
        syscall_id: SyscallId::VSpaceUnmap,
    };
    verify_regs(&req, &[
        (2, 2, "x2=asid"),
        (3, 0x3000, "x3=vaddr"),
        (6, 10, "x7=SyscallId::VSpaceUnmap"),
    ]);
}

// ============================================================================
// Service syscalls (RUST-XVAL-012 through RUST-XVAL-014)
// ============================================================================

/// RUST-XVAL-012: Service register register layout with IPC buffer overflow.
#[test]
fn xval_012_service_register() {
    let args = service::ServiceRegisterArgs {
        interface_id: InterfaceId::from(7u64),
        method_count: 5,
        max_message_size: 256,
        max_response_size: 128,
        requires_grant: true,
    };
    let encoded = args.encode();
    // Service register needs 5 msg regs: 4 inline + 1 IPC buffer overflow.
    let mut buf = IpcBuffer::new();
    buf.set_mr(4, encoded[4]).unwrap();
    let req = SyscallRequest {
        cap_addr: CPtr::from(1200u64),
        msg_info: MessageInfo { length: 5, extra_caps: 0, label: 0 },
        msg_regs: [encoded[0], encoded[1], encoded[2], encoded[3]],
        syscall_id: SyscallId::ServiceRegister,
    };
    verify_regs(&req, &[
        (2, 7, "x2=interfaceId"),
        (3, 5, "x3=methodCount"),
        (4, 256, "x4=maxMessageSize"),
        (5, 128, "x5=maxResponseSize"),
        (6, 11, "x7=SyscallId::ServiceRegister"),
    ]);
    // Verify 5th parameter in IPC buffer overflow slot
    assert_eq!(buf.get_mr(4).unwrap(), 1, "IPC buffer[4]=requiresGrant(true)");
}

/// RUST-XVAL-013: Service revoke register layout.
#[test]
fn xval_013_service_revoke() {
    let args = service::ServiceRevokeArgs { target_service: ServiceId::from(42u64) };
    let encoded = args.encode();
    let req = SyscallRequest {
        cap_addr: CPtr::from(1300u64),
        msg_info: MessageInfo { length: 1, extra_caps: 0, label: 0 },
        msg_regs: [encoded[0], 0, 0, 0],
        syscall_id: SyscallId::ServiceRevoke,
    };
    verify_regs(&req, &[
        (2, 42, "x2=targetService"),
        (6, 12, "x7=SyscallId::ServiceRevoke"),
    ]);
}

/// RUST-XVAL-014: Service query register layout.
#[test]
fn xval_014_service_query() {
    let req = SyscallRequest {
        cap_addr: CPtr::from(1400u64),
        msg_info: MessageInfo { length: 0, extra_caps: 0, label: 0 },
        msg_regs: [0; 4],
        syscall_id: SyscallId::ServiceQuery,
    };
    verify_regs(&req, &[
        (0, 1400, "x0=CPtr"),
        (1, 0, "x1=MessageInfo(empty)"),
        (6, 13, "x7=SyscallId::ServiceQuery"),
    ]);
}

// ============================================================================
// Notification syscalls (RUST-XVAL-015 through RUST-XVAL-016)
// ============================================================================

/// RUST-XVAL-015: Notification signal register layout.
///
/// Badge is NOT passed by the caller — it comes from the resolved capability.
/// msg_regs must be zeroed (no payload for notification signal).
/// Lean: `notificationSignal` (Endpoint.lean) — badge from capability.
/// seL4 equivalent: `seL4_Signal(dest)`.
#[test]
fn xval_015_notification_signal() {
    let req = SyscallRequest {
        cap_addr: CPtr::from(500u64),
        msg_info: MessageInfo { length: 0, extra_caps: 0, label: 0 },
        msg_regs: [0; 4],
        syscall_id: SyscallId::Send,
    };
    let regs = encode_syscall(&req);
    // Verify no payload: all msg_regs must be zero
    assert_eq!(regs[0], 500, "x0=CPtr(notification)");
    assert_eq!(regs[1], 0, "x1=MessageInfo(empty)");
    assert_eq!(regs[2], 0, "x2=msg_regs[0] must be zero (badge comes from capability)");
    assert_eq!(regs[3], 0, "x3=msg_regs[1] must be zero");
    assert_eq!(regs[4], 0, "x4=msg_regs[2] must be zero");
    assert_eq!(regs[5], 0, "x5=msg_regs[3] must be zero");
    assert_eq!(regs[6], SyscallId::Send.to_u64(), "x7=SyscallId::Send");
}

/// RUST-XVAL-016: Notification wait register layout.
///
/// Badge is returned in x1 (context-dependent: badge for notification wait,
/// MessageInfo for endpoint receive).
/// Lean: `notificationWait` (Endpoint.lean) — returns accumulated badge.
#[test]
fn xval_016_notification_wait() {
    let req = SyscallRequest {
        cap_addr: CPtr::from(600u64),
        msg_info: MessageInfo { length: 0, extra_caps: 0, label: 0 },
        msg_regs: [0; 4],
        syscall_id: SyscallId::Receive,
    };
    let regs = encode_syscall(&req);
    assert_eq!(regs[0], 600, "x0=CPtr(notification)");
    assert_eq!(regs[6], SyscallId::Receive.to_u64(), "x7=SyscallId::Receive");

    // Simulate kernel response: badge=0xBEEF in x1
    let response_regs: [u64; 7] = [0, 0xBEEF, 0, 0, 0, 0, 0];
    let resp = decode_response(response_regs).unwrap();
    assert_eq!(resp.badge(), Badge::from(0xBEEFu64), "Badge from x1");
}

// ============================================================================
// IPC buffer overflow tests (RUST-XVAL-017 through RUST-XVAL-019)
// ============================================================================

/// RUST-XVAL-017: IPC buffer set/get roundtrip for all overflow slots.
#[test]
fn xval_017_ipc_buffer_overflow_roundtrip() {
    let mut buf = IpcBuffer::new();
    // Write to first and last overflow slots
    buf.set_mr(4, 0xAAAA).unwrap();
    buf.set_mr(119, 0xBBBB).unwrap();
    assert_eq!(buf.get_mr(4).unwrap(), 0xAAAA);
    assert_eq!(buf.get_mr(119).unwrap(), 0xBBBB);
    // Inline indices return false (not written to buffer)
    assert_eq!(buf.set_mr(0, 42), Ok(false));
    assert_eq!(buf.set_mr(3, 42), Ok(false));
}

/// RUST-XVAL-018: IPC buffer bounds enforcement.
#[test]
fn xval_018_ipc_buffer_bounds() {
    let mut buf = IpcBuffer::new();
    assert!(buf.set_mr(120, 1).is_err());
    assert!(buf.set_mr(usize::MAX, 1).is_err());
    assert!(buf.get_mr(120).is_err());
}

/// RUST-XVAL-019: Service register with IPC buffer overflow verified.
#[test]
fn xval_019_service_register_ipc_buffer() {
    let args = service::ServiceRegisterArgs {
        interface_id: InterfaceId::from(10u64),
        method_count: 8,
        max_message_size: 512,
        max_response_size: 256,
        requires_grant: false,
    };
    let encoded = args.encode();
    let mut buf = IpcBuffer::new();
    // Simulate what service_register does: write 5th param to buffer
    buf.set_mr(4, encoded[4]).unwrap();
    // Verify: requiresGrant=false encodes as 0
    assert_eq!(buf.get_mr(4).unwrap(), 0, "requiresGrant=false → 0 in IPC buffer");

    // Now test with requires_grant=true
    let args_grant = service::ServiceRegisterArgs {
        interface_id: InterfaceId::from(10u64),
        method_count: 8,
        max_message_size: 512,
        max_response_size: 256,
        requires_grant: true,
    };
    let encoded_grant = args_grant.encode();
    buf.set_mr(4, encoded_grant[4]).unwrap();
    assert_eq!(buf.get_mr(4).unwrap(), 1, "requiresGrant=true → 1 in IPC buffer");
}

// ============================================================================
// Cross-cutting ABI property tests
// ============================================================================

/// Verify MessageInfo encode/decode roundtrip for all valid bound combinations.
#[test]
fn message_info_exhaustive_bounds() {
    for len in [0u8, 1, 60, 119, 120] {
        for caps in [0u8, 1, 2, 3] {
            for label in [0u64, 1, 0xFFFF, 0x7FFFFF] {
                let mi = MessageInfo { length: len, extra_caps: caps, label };
                let decoded = MessageInfo::decode(mi.encode()).unwrap();
                assert_eq!(decoded, mi, "Roundtrip failed for len={}, caps={}, label={}", len, caps, label);
            }
        }
    }
}

/// Verify SyscallId roundtrip for all 14 variants.
#[test]
fn syscall_id_exhaustive_roundtrip() {
    for i in 0..14u64 {
        let sid = SyscallId::from_u64(i).expect("valid syscall id");
        assert_eq!(sid.to_u64(), i);
    }
    assert!(SyscallId::from_u64(14).is_none());
}

/// Verify KernelError roundtrip for all 38 variants (T1-F/H-4: 4 new at 34-37).
#[test]
fn kernel_error_exhaustive_roundtrip() {
    for i in 0..=37u32 {
        let err = KernelError::from_u32(i).expect(&format!("valid error for discriminant {i}"));
        assert_eq!(err as u32, i);
    }
    assert!(KernelError::from_u32(38).is_none());
}

/// Verify TypeTag roundtrip for all 6 variants.
#[test]
fn type_tag_exhaustive_roundtrip() {
    for i in 0..=5u64 {
        let tag = TypeTag::from_u64(i).expect("valid type tag");
        assert_eq!(tag.to_u64(), i);
    }
    assert!(TypeTag::from_u64(6).is_err());
}

/// Verify all CSpace arg structures roundtrip.
#[test]
fn cspace_args_roundtrip_all() {
    let mint = cspace::CSpaceMintArgs {
        src_slot: Slot::from(1u64), dst_slot: Slot::from(2u64),
        rights: AccessRights::from(0x1Fu8), badge: Badge::from(0xDEADu64),
    };
    assert_eq!(cspace::CSpaceMintArgs::decode(&mint.encode()).unwrap(), mint);

    let copy = cspace::CSpaceCopyArgs { src_slot: Slot::from(3u64), dst_slot: Slot::from(4u64) };
    assert_eq!(cspace::CSpaceCopyArgs::decode(&copy.encode()).unwrap(), copy);

    let mv = cspace::CSpaceMoveArgs { src_slot: Slot::from(5u64), dst_slot: Slot::from(6u64) };
    assert_eq!(cspace::CSpaceMoveArgs::decode(&mv.encode()).unwrap(), mv);

    let del = cspace::CSpaceDeleteArgs { target_slot: Slot::from(7u64) };
    assert_eq!(cspace::CSpaceDeleteArgs::decode(&del.encode()).unwrap(), del);
}

/// Verify W^X enforcement in PagePerms.
#[test]
fn page_perms_wx_enforcement() {
    // Safe combinations
    assert!(PagePerms::try_from(0x01u64).unwrap().is_wx_safe()); // R
    assert!(PagePerms::try_from(0x02u64).unwrap().is_wx_safe()); // W
    assert!(PagePerms::try_from(0x04u64).unwrap().is_wx_safe()); // X
    assert!(PagePerms::try_from(0x03u64).unwrap().is_wx_safe()); // RW
    assert!(PagePerms::try_from(0x05u64).unwrap().is_wx_safe()); // RX

    // Unsafe: W+X
    assert!(!PagePerms::try_from(0x06u64).unwrap().is_wx_safe()); // WX
    assert!(!PagePerms::try_from(0x07u64).unwrap().is_wx_safe()); // RWX
}
