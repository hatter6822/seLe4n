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
    let regs = encode_syscall(req).unwrap();
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
        msg_info: MessageInfo::new(2, 0, 0x10).unwrap(),
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
        msg_info: MessageInfo::new(0, 0, 0).unwrap(),
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
        msg_info: MessageInfo::new(1, 0, 42).unwrap(),
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
        msg_info: MessageInfo::new(0, 0, 0).unwrap(),
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
        rights: AccessRights::try_from(0x07u8).unwrap(), // read|write|grant
        badge: Badge::from(999u64),
    };
    let encoded = args.encode();
    let req = SyscallRequest {
        cap_addr: CPtr::from(500u64),
        msg_info: MessageInfo::new(4, 0, 0).unwrap(),
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
        msg_info: MessageInfo::new(2, 0, 0).unwrap(),
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
        msg_info: MessageInfo::new(2, 0, 0).unwrap(),
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
        msg_info: MessageInfo::new(1, 0, 0).unwrap(),
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
        new_type: TypeTag::Notification, // V1-C: now TypeTag
        size: 0,
    };
    let encoded = args.encode();
    let req = SyscallRequest {
        cap_addr: CPtr::from(900u64),
        msg_info: MessageInfo::new(3, 0, 0).unwrap(),
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
        perms: PagePerms::try_from(0x05u64).unwrap(), // read|execute
    };
    let encoded = args.encode();
    let req = SyscallRequest {
        cap_addr: CPtr::from(1000u64),
        msg_info: MessageInfo::new(4, 0, 0).unwrap(),
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
        msg_info: MessageInfo::new(2, 0, 0).unwrap(),
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
        msg_info: MessageInfo::new(5, 0, 0).unwrap(),
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
        msg_info: MessageInfo::new(1, 0, 0).unwrap(),
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
        msg_info: MessageInfo::new(0, 0, 0).unwrap(),
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
/// Badge is passed via MR[0] (x2), per Lean `decodeNotificationSignalArgs`
/// (SyscallArgDecode.lean:869-872) which reads `badge := Badge.ofNatMasked
/// (requireMsgReg msgRegs 0).val`. MessageInfo.length=1 to indicate one
/// message register is populated.
#[test]
fn xval_015_notification_signal() {
    let badge_val: u64 = 0xDEAD_BEEF;
    let req = SyscallRequest {
        cap_addr: CPtr::from(500u64),
        msg_info: MessageInfo::new(1, 0, 0).unwrap(),
        msg_regs: [badge_val, 0, 0, 0],
        syscall_id: SyscallId::NotificationSignal,
    };
    let regs = encode_syscall(&req).unwrap();
    assert_eq!(regs[0], 500, "x0=CPtr(notification)");
    assert_eq!(regs[1], 1, "x1=MessageInfo(length=1)");
    assert_eq!(regs[2], badge_val, "x2=msg_regs[0] carries badge value");
    assert_eq!(regs[3], 0, "x3=msg_regs[1] must be zero");
    assert_eq!(regs[4], 0, "x4=msg_regs[2] must be zero");
    assert_eq!(regs[5], 0, "x5=msg_regs[3] must be zero");
    assert_eq!(regs[6], SyscallId::NotificationSignal.to_u64(), "x7=SyscallId::NotificationSignal");
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
        msg_info: MessageInfo::new(0, 0, 0).unwrap(),
        msg_regs: [0; 4],
        syscall_id: SyscallId::NotificationWait,
    };
    let regs = encode_syscall(&req).unwrap();
    assert_eq!(regs[0], 600, "x0=CPtr(notification)");
    assert_eq!(regs[6], SyscallId::NotificationWait.to_u64(), "x7=SyscallId::NotificationWait");

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
    // AK4-F (R-ABI-M04): Inline indices now return `Err(InvalidArgument)`
    // for symmetry with `get_mr`. Legacy `Ok(false)` semantics available
    // via `set_mr_overflow`.
    assert_eq!(buf.set_mr(0, 42), Err(sele4n_types::KernelError::InvalidArgument));
    assert_eq!(buf.set_mr(3, 42), Err(sele4n_types::KernelError::InvalidArgument));
    assert_eq!(buf.set_mr_overflow(0, 42), Ok(()));
    assert_eq!(buf.set_mr_overflow(3, 42), Ok(()));
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
/// V2-H: Label values updated to fit 20-bit limit (max 0xFFFFF).
#[test]
fn message_info_exhaustive_bounds() {
    for len in [0u8, 1, 60, 119, 120] {
        for caps in [0u8, 1, 2, 3] {
            for label in [0u64, 1, 0xFFFF, 0xFFFFF] {
                let mi = MessageInfo::new(len, caps, label).unwrap();
                let decoded = MessageInfo::decode(mi.encode().unwrap()).unwrap();
                assert_eq!(decoded, mi, "Roundtrip failed for len={}, caps={}, label={}", len, caps, label);
            }
        }
    }
}

/// Verify SyscallId roundtrip for all 25 variants (D6: +D1/D2/D3 TCB ops).
#[test]
fn syscall_id_exhaustive_roundtrip() {
    for i in 0..25u64 {
        let sid = SyscallId::from_u64(i).expect("valid syscall id");
        assert_eq!(sid.to_u64(), i);
    }
    assert!(SyscallId::from_u64(25).is_none());
}

/// Verify KernelError roundtrip for all 51 variants
/// (AL1b/WS-AL: NullCapability at 50 extends AL6's range of 0..=49).
#[test]
fn kernel_error_exhaustive_roundtrip() {
    for i in 0..=50u32 {
        let err = KernelError::from_u32(i).expect(&format!("valid error for discriminant {i}"));
        assert_eq!(err as u32, i);
    }
    assert!(KernelError::from_u32(51).is_none());
}

/// Verify TypeTag roundtrip for all 7 variants (0–6, including SchedContext).
#[test]
fn type_tag_exhaustive_roundtrip() {
    for i in 0..=6u64 {
        let tag = TypeTag::from_u64(i).expect("valid type tag");
        assert_eq!(tag.to_u64(), i);
    }
    assert!(TypeTag::from_u64(7).is_err());
}

/// Verify all CSpace arg structures roundtrip.
#[test]
fn cspace_args_roundtrip_all() {
    let mint = cspace::CSpaceMintArgs {
        src_slot: Slot::from(1u64), dst_slot: Slot::from(2u64),
        rights: AccessRights::try_from(0x1Fu8).unwrap(), badge: Badge::from(0xDEADu64),
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

// ============================================================================
// T3 — Rust ABI Hardening conformance tests
// ============================================================================

/// V2-H/M-API-3: MessageInfo label 20-bit bound enforcement.
///
/// Verify that encode(decode(x)) == x for boundary values and that
/// encode returns error for labels >= 2^20.
#[test]
fn t3b_message_info_label_boundary_roundtrip() {
    use sele4n_abi::message_info::MAX_LABEL;

    // Boundary value: label = 0 (minimum)
    let mi_zero = MessageInfo::new(0, 0, 0).unwrap();
    let encoded = mi_zero.encode().unwrap();
    assert_eq!(MessageInfo::decode(encoded).unwrap(), mi_zero);

    // Boundary value: label = 2^20 - 1 (maximum valid)
    let mi_max = MessageInfo::new(0, 0, MAX_LABEL).unwrap();
    let encoded = mi_max.encode().unwrap();
    assert_eq!(MessageInfo::decode(encoded).unwrap(), mi_max);

    // Boundary value: label = 2^20 (first invalid — new() must reject)
    assert_eq!(MessageInfo::new(0, 0, 1u64 << 20), Err(KernelError::InvalidMessageInfo));

    // Extreme: label = u64::MAX (new() must reject)
    assert_eq!(MessageInfo::new(0, 0, u64::MAX), Err(KernelError::InvalidMessageInfo));
}

/// V2-H: MessageInfo::new rejects oversized labels (U3-B: struct literals no longer possible).
#[test]
fn t3b_encode_syscall_rejects_oversized_label() {
    // U3-B: With private fields, invalid MessageInfo can no longer be constructed.
    // We verify the rejection happens at new() instead.
    assert_eq!(MessageInfo::new(0, 0, 1u64 << 20), Err(KernelError::InvalidMessageInfo));
}

/// T3-B: MessageInfo::new rejects oversized labels.
#[test]
fn t3b_message_info_new_rejects_oversized_label() {
    use sele4n_abi::message_info::MAX_LABEL;
    assert!(MessageInfo::new(0, 0, MAX_LABEL).is_ok());
    assert_eq!(MessageInfo::new(0, 0, MAX_LABEL + 1), Err(KernelError::InvalidMessageInfo));
}

/// T3-D/M-NEW-10: VSpaceMapArgs perms validation at decode boundary.
///
/// Verify valid permission values roundtrip correctly and invalid values
/// are rejected at decode.
#[test]
fn t3d_vspace_map_args_perms_roundtrip() {
    // All valid 5-bit values (0x00 through 0x1F) roundtrip correctly
    for perm_val in 0..=0x1Fu64 {
        let args = vspace::VSpaceMapArgs {
            asid: Asid::from(1u64),
            vaddr: VAddr::from(0x1000u64),
            paddr: PAddr::from(0x2000u64),
            perms: PagePerms::try_from(perm_val).unwrap(),
        };
        let decoded = vspace::VSpaceMapArgs::decode(&args.encode()).unwrap();
        assert_eq!(decoded, args, "Roundtrip failed for perms=0x{:02x}", perm_val);
    }
}

/// T3-D: Invalid permission values are rejected at decode.
/// V1-F consistency: returns InvalidArgument (not InvalidMessageInfo)
/// because the message structure is correct — the argument value is invalid.
#[test]
fn t3d_vspace_map_args_invalid_perms_rejected() {
    // 0x20 — first value outside 5-bit range
    assert_eq!(
        vspace::VSpaceMapArgs::decode(&[1, 0x1000, 0x2000, 0x20]),
        Err(KernelError::InvalidArgument)
    );

    // 0xFF — common garbage value
    assert_eq!(
        vspace::VSpaceMapArgs::decode(&[1, 0x1000, 0x2000, 0xFF]),
        Err(KernelError::InvalidArgument)
    );

    // u64::MAX — extreme case
    assert_eq!(
        vspace::VSpaceMapArgs::decode(&[1, 0x1000, 0x2000, u64::MAX]),
        Err(KernelError::InvalidArgument)
    );
}

/// T3-F/M-NEW-11: ServiceRegisterArgs strict boolean conformance.
///
/// Verify that regs[4] = 0 → false, regs[4] = 1 → true, and values
/// 2, 0xFFFFFFFFFFFFFFFF are rejected.
#[test]
fn t3f_service_register_strict_bool() {
    let base = [7u64, 5, 256, 128];

    // regs[4] = 0 → false
    let mut regs = [base[0], base[1], base[2], base[3], 0];
    let args = service::ServiceRegisterArgs::decode(&regs).unwrap();
    assert!(!args.requires_grant, "regs[4]=0 must decode to false");

    // regs[4] = 1 → true
    regs[4] = 1;
    let args = service::ServiceRegisterArgs::decode(&regs).unwrap();
    assert!(args.requires_grant, "regs[4]=1 must decode to true");

    // regs[4] = 2 → rejected
    regs[4] = 2;
    assert_eq!(
        service::ServiceRegisterArgs::decode(&regs),
        Err(KernelError::InvalidMessageInfo),
        "regs[4]=2 must be rejected"
    );

    // regs[4] = 0xFFFFFFFFFFFFFFFF → rejected
    regs[4] = u64::MAX;
    assert_eq!(
        service::ServiceRegisterArgs::decode(&regs),
        Err(KernelError::InvalidMessageInfo),
        "regs[4]=u64::MAX must be rejected"
    );
}

/// T3-F: ServiceRegisterArgs roundtrip with strict bool.
#[test]
fn t3f_service_register_roundtrip_strict() {
    let args_true = service::ServiceRegisterArgs {
        interface_id: InterfaceId::from(7u64),
        method_count: 5,
        max_message_size: 256,
        max_response_size: 128,
        requires_grant: true,
    };
    assert_eq!(service::ServiceRegisterArgs::decode(&args_true.encode()).unwrap(), args_true);

    let args_false = service::ServiceRegisterArgs {
        interface_id: InterfaceId::from(7u64),
        method_count: 5,
        max_message_size: 256,
        max_response_size: 128,
        requires_grant: false,
    };
    assert_eq!(service::ServiceRegisterArgs::decode(&args_false.encode()).unwrap(), args_false);
}

// ============================================================================
// U3 — Rust ABI Hardening conformance tests
// ============================================================================

/// U3-B: Verify MessageInfo private fields enforce validated construction.
///
/// After U3-B, the only way to create MessageInfo is through `new()` or
/// `decode()`, both of which validate bounds. This test verifies the
/// accessor methods return the values passed to `new()`.
#[test]
fn u3b_message_info_private_fields_accessors() {
    let mi = MessageInfo::new(42, 2, 0x1234).unwrap();
    assert_eq!(mi.length(), 42);
    assert_eq!(mi.extra_caps(), 2);
    assert_eq!(mi.label(), 0x1234);

    // Decoded values also accessible via accessors
    let decoded = MessageInfo::decode(mi.encode().unwrap()).unwrap();
    assert_eq!(decoded.length(), 42);
    assert_eq!(decoded.extra_caps(), 2);
    assert_eq!(decoded.label(), 0x1234);
}

/// U3-D/E: AccessRights TryFrom<u8> roundtrip conformance.
///
/// Valid values (0–31) succeed, invalid values (32–255) are rejected.
#[test]
fn u3de_access_rights_try_from_valid() {
    for v in 0..=0x1Fu8 {
        let rights = AccessRights::try_from(v).unwrap();
        assert_eq!(rights.raw(), v);
        // Roundtrip through u8
        let back: u8 = rights.into();
        assert_eq!(back, v);
    }
}

#[test]
fn u3de_access_rights_try_from_invalid() {
    for v in 0x20..=0xFFu8 {
        assert!(
            AccessRights::try_from(v).is_err(),
            "AccessRights::try_from({:#04x}) should fail (bits 5-7 set)", v
        );
    }
}

/// U3-D/E: AccessRights bitmask operations preserve validity.
#[test]
fn u3de_access_rights_ops_preserve_validity() {
    // Union of valid rights stays valid
    let rw = AccessRights::READ | AccessRights::WRITE;
    assert!(rw.raw() <= 0x1F);
    // Intersection stays valid
    let r = rw & AccessRights::READ;
    assert!(r.raw() <= 0x1F);
    assert!(r.contains(AccessRight::Read));
    assert!(!r.contains(AccessRight::Write));
}

/// U3-F: KernelError has #[non_exhaustive] — external matches require wildcard.
///
/// This test validates that `from_u32` still works for all known variants
/// and that unknown discriminants return None (forward-compatible).
#[test]
fn u3f_kernel_error_non_exhaustive() {
    // AL1b (WS-AL / AK7-I.cascade): 51 variants (0–50) roundtrip.
    for i in 0..=50u32 {
        let e = KernelError::from_u32(i).unwrap();
        assert_eq!(e as u32, i);
    }
    // Future discriminants return None
    assert!(KernelError::from_u32(51).is_none());
    assert!(KernelError::from_u32(100).is_none());
    assert!(KernelError::from_u32(u32::MAX).is_none());
}

/// U3-G: RegisterFile safe bounds checking.
#[test]
fn u3g_register_file_bounds() {
    use sele4n_abi::RegisterFile;

    let mut rf = RegisterFile::new();
    // Valid indices (0-6) succeed
    for i in 0..7 {
        assert!(rf.set(i, i as u64 * 10).is_some());
    }
    for i in 0..7 {
        assert_eq!(rf.get(i), Some(i as u64 * 10));
    }
    // Out of bounds returns None (not panic)
    assert_eq!(rf.get(7), None);
    assert_eq!(rf.get(usize::MAX), None);
    assert_eq!(rf.set(7, 42), None);
}

/// U3-I: IpcBuffer layout matches expected size and alignment.
#[test]
fn u3i_ipc_buffer_layout() {
    assert_eq!(core::mem::size_of::<IpcBuffer>(), 960);
    assert_eq!(core::mem::align_of::<IpcBuffer>(), 8);
}

// ============================================================================
// V1 — Rust ABI Hardening conformance tests (Phase V1, WS-V)
// ============================================================================

/// V1-A (H-RS-1): decode_response must reject u64 values exceeding u32::MAX.
/// Without the range guard, 0x1_0000_0000 truncates to 0 (false success).
#[test]
fn v1a_decode_response_u64_overflow() {
    use sele4n_abi::decode_response;

    // Value that would truncate to 0 (success) without guard
    let regs = [0x1_0000_0000u64, 0, 0, 0, 0, 0, 0];
    assert_eq!(decode_response(regs), Err(KernelError::InvalidSyscallNumber));

    // u64::MAX
    let regs = [u64::MAX, 0, 0, 0, 0, 0, 0];
    assert_eq!(decode_response(regs), Err(KernelError::InvalidSyscallNumber));

    // Just above u32::MAX
    let regs = [u32::MAX as u64 + 1, 0, 0, 0, 0, 0, 0];
    assert_eq!(decode_response(regs), Err(KernelError::InvalidSyscallNumber));
}

/// AF6-A + AL1b: Unrecognized kernel error codes (≥51 after AL1b added
/// NullCapability at 50) map to UnknownKernelError.
#[test]
fn af6a_unknown_kernel_error_fallback() {
    use sele4n_abi::decode_response;

    // Error code 51 — first unrecognized code after NullCapability (50)
    let regs = [51, 0, 0, 0, 0, 0, 0];
    assert_eq!(decode_response(regs), Err(KernelError::UnknownKernelError));

    // Error code 100 — arbitrary unrecognized code
    let regs = [100, 0, 0, 0, 0, 0, 0];
    assert_eq!(decode_response(regs), Err(KernelError::UnknownKernelError));

    // Error code 254 — just below sentinel
    let regs = [254, 0, 0, 0, 0, 0, 0];
    assert_eq!(decode_response(regs), Err(KernelError::UnknownKernelError));

    // Error code 255 — sentinel value resolves to UnknownKernelError directly
    let regs = [255, 0, 0, 0, 0, 0, 0];
    assert_eq!(decode_response(regs), Err(KernelError::UnknownKernelError));
}

/// V1-C (M-RS-1): LifecycleRetypeArgs rejects invalid type tags at decode.
#[test]
fn v1c_lifecycle_retype_invalid_type_tag() {
    // Type tag 7 (first invalid, after SchedContext = 6)
    assert_eq!(
        lifecycle::LifecycleRetypeArgs::decode(&[42, 7, 0]),
        Err(KernelError::InvalidTypeTag)
    );

    // Type tag u64::MAX
    assert_eq!(
        lifecycle::LifecycleRetypeArgs::decode(&[42, u64::MAX, 0]),
        Err(KernelError::InvalidTypeTag)
    );

    // All valid tags (0-6, including SchedContext) must succeed
    for i in 0..=6u64 {
        assert!(lifecycle::LifecycleRetypeArgs::decode(&[42, i, 0]).is_ok());
    }
}

/// V1-E (M-RS-3): IpcBuffer.get_mr returns InvalidArgument for inline indices.
#[test]
fn v1e_ipc_buffer_inline_error_variant() {
    let buf = IpcBuffer::new();
    for i in 0..4 {
        assert_eq!(buf.get_mr(i), Err(KernelError::InvalidArgument));
    }
}

/// V1-F (M-RS-4): CSpaceMintArgs decode returns InvalidArgument for invalid rights.
#[test]
fn v1f_cspace_mint_invalid_rights_error_variant() {
    assert_eq!(
        cspace::CSpaceMintArgs::decode(&[1, 2, 0x20, 42]),
        Err(KernelError::InvalidArgument)
    );
    assert_eq!(
        cspace::CSpaceMintArgs::decode(&[1, 2, u64::MAX, 42]),
        Err(KernelError::InvalidArgument)
    );
}

/// V1-G (M-RS-5): PagePerms checked_bitor rejects W^X violations.
#[test]
fn v1g_page_perms_checked_bitor_wx() {
    use sele4n_abi::args::PagePerms;

    // Safe combinations
    assert!(PagePerms::READ.checked_bitor(PagePerms::WRITE).is_ok());
    assert!(PagePerms::READ.checked_bitor(PagePerms::EXECUTE).is_ok());
    assert!(PagePerms::READ.checked_bitor(PagePerms::USER).is_ok());

    // W^X violation
    assert_eq!(
        PagePerms::WRITE.checked_bitor(PagePerms::EXECUTE),
        Err(KernelError::PolicyDenied)
    );

    // Transitive W^X violation
    let rw = PagePerms::READ.checked_bitor(PagePerms::WRITE).unwrap();
    assert_eq!(
        rw.checked_bitor(PagePerms::EXECUTE),
        Err(KernelError::PolicyDenied)
    );
}

/// V1-I (L-RS-2): ServiceRegisterArgs rejects out-of-bounds method_count/message_size.
#[test]
fn v1i_service_register_bounds() {
    use sele4n_abi::args::service::{MAX_METHOD_COUNT, MAX_SERVICE_MESSAGE_SIZE};

    // method_count too large
    assert_eq!(
        service::ServiceRegisterArgs::decode(&[1, MAX_METHOD_COUNT + 1, 64, 64, 0]),
        Err(KernelError::InvalidArgument)
    );

    // max_message_size too large
    assert_eq!(
        service::ServiceRegisterArgs::decode(&[1, 5, MAX_SERVICE_MESSAGE_SIZE + 1, 64, 0]),
        Err(KernelError::InvalidArgument)
    );

    // Boundary values accepted
    assert!(
        service::ServiceRegisterArgs::decode(&[1, MAX_METHOD_COUNT, MAX_SERVICE_MESSAGE_SIZE, MAX_SERVICE_MESSAGE_SIZE, 1]).is_ok()
    );
}

/// V1-D (M-RS-2): MessageInfo::new_const is infallible for valid constants.
#[test]
fn v1d_message_info_new_const() {
    let mi = MessageInfo::new_const(0, 0, 0);
    assert_eq!(mi.length(), 0);
    assert_eq!(mi.extra_caps(), 0);
    assert_eq!(mi.label(), 0);

    let mi = MessageInfo::new_const(120, 3, 0xFFFF);
    assert_eq!(mi.length(), 120);
    assert_eq!(mi.extra_caps(), 3);
    assert_eq!(mi.label(), 0xFFFF);
}

/// V1-H (M-RS-7): Identifier validation methods.
#[test]
fn v1h_identifier_validation() {
    use sele4n_types::{Slot, DomainId, Priority};

    assert!(Slot::from(0u64).is_valid());
    assert!(!Slot::from(u32::MAX as u64 + 1).is_valid());

    assert!(DomainId::from(255u64).is_valid());
    assert!(!DomainId::from(256u64).is_valid());

    assert!(Priority::from(255u64).is_valid());
    assert!(!Priority::from(256u64).is_valid());
}

// ============================================================================
// W1 — Critical Rust ABI Fix conformance tests
// ============================================================================

/// W1-H / AA1 / AG3 / AL6 / AL1b: KernelError variant count matches Lean
/// (51 variants, 0-50 after AL1b added NullCapability at 50).
/// Detects Lean-Rust enum divergence automatically.
#[test]
fn w1h_kernel_error_variant_count() {
    const KERNEL_ERROR_COUNT: u32 = 51;
    // All expected variants exist
    for i in 0..KERNEL_ERROR_COUNT {
        assert!(
            KernelError::from_u32(i).is_some(),
            "KernelError variant missing at discriminant {i}"
        );
    }
    // Next discriminant is out of range
    assert!(
        KernelError::from_u32(KERNEL_ERROR_COUNT).is_none(),
        "Unexpected KernelError variant at discriminant {KERNEL_ERROR_COUNT}"
    );
}

/// W1-H / AA1 / D6: SyscallId variant count matches Lean (25 variants, 0-24).
#[test]
fn w1h_syscall_id_variant_count() {
    const SYSCALL_COUNT: u64 = 25;
    assert_eq!(SyscallId::COUNT, SYSCALL_COUNT as usize);
    for i in 0..SYSCALL_COUNT {
        assert!(
            SyscallId::from_u64(i).is_some(),
            "SyscallId variant missing at discriminant {i}"
        );
    }
    assert!(
        SyscallId::from_u64(SYSCALL_COUNT).is_none(),
        "Unexpected SyscallId variant at discriminant {SYSCALL_COUNT}"
    );
}

/// W1-H: Compile-time ABI constant assertions.
#[test]
fn w1h_abi_constants_match_lean() {
    use sele4n_abi::message_info::{MAX_LABEL, MAX_MSG_LENGTH, MAX_EXTRA_CAPS};
    assert_eq!(MAX_LABEL, 1_048_575, "MAX_LABEL must be 2^20 - 1");
    assert_eq!(MAX_MSG_LENGTH, 120, "MAX_MSG_LENGTH must be 120");
    assert_eq!(MAX_EXTRA_CAPS, 3, "MAX_EXTRA_CAPS must be 3");
}

/// W1-F-1: notification_signal encodes SyscallId::NotificationSignal (14)
/// and places badge in msg_regs[0].
#[test]
fn w1f_notification_signal_encoding() {
    let badge_val: u64 = 0xCAFE_BABE;
    let req = SyscallRequest {
        cap_addr: CPtr::from(42u64),
        msg_info: MessageInfo::new(1, 0, 0).unwrap(),
        msg_regs: [badge_val, 0, 0, 0],
        syscall_id: SyscallId::NotificationSignal,
    };
    let regs = encode_syscall(&req).unwrap();
    assert_eq!(regs[6], 14, "x7=SyscallId::NotificationSignal must be 14");
    assert_eq!(regs[2], badge_val, "x2=msg_regs[0] must carry badge");
}

/// W1-F-1: notification_wait encodes SyscallId::NotificationWait (15).
#[test]
fn w1f_notification_wait_encoding() {
    let req = SyscallRequest {
        cap_addr: CPtr::from(99u64),
        msg_info: MessageInfo::new(0, 0, 0).unwrap(),
        msg_regs: [0; 4],
        syscall_id: SyscallId::NotificationWait,
    };
    let regs = encode_syscall(&req).unwrap();
    assert_eq!(regs[6], 15, "x7=SyscallId::NotificationWait must be 15");
}

/// W1-F-1: endpoint_reply_recv encodes SyscallId::ReplyRecv (16)
/// and places reply_target in msg_regs[0].
#[test]
fn w1f_endpoint_reply_recv_encoding() {
    let reply_target: u64 = 7;
    let req = SyscallRequest {
        cap_addr: CPtr::from(200u64),
        msg_info: MessageInfo::new(1, 0, 0).unwrap(),
        msg_regs: [reply_target, 0, 0, 0],
        syscall_id: SyscallId::ReplyRecv,
    };
    let regs = encode_syscall(&req).unwrap();
    assert_eq!(regs[6], 16, "x7=SyscallId::ReplyRecv must be 16");
    assert_eq!(regs[2], reply_target, "x2=msg_regs[0] must carry reply_target");
}

/// W1-D: MmioUnaligned variant exists at discriminant 40.
#[test]
fn w1d_mmio_unaligned_variant() {
    let err = KernelError::from_u32(40).unwrap();
    assert_eq!(err, KernelError::MmioUnaligned);
    assert_eq!(err as u32, 40);
}

/// W1-E audit: endpoint_reply_recv places reply_target in MR[0] and user
/// data in MR[1..3]. MessageInfo.length = user_length + 1 (for reply_target).
#[test]
fn w1e_endpoint_reply_recv_register_layout() {
    // Simulate: user wants 2 registers of reply data + reply_target
    let reply_target: u64 = 7;
    let user_data_0: u64 = 0xAAAA;
    let user_data_1: u64 = 0xBBBB;
    // Kernel should encode: MR[0]=reply_target, MR[1]=user_data_0, MR[2]=user_data_1
    // MessageInfo.length = 2 + 1 = 3
    let req = SyscallRequest {
        cap_addr: CPtr::from(200u64),
        msg_info: MessageInfo::new(3, 0, 0).unwrap(), // 2 user regs + 1 reply_target
        msg_regs: [reply_target, user_data_0, user_data_1, 0],
        syscall_id: SyscallId::ReplyRecv,
    };
    let regs = encode_syscall(&req).unwrap();
    assert_eq!(regs[2], reply_target, "x2=MR[0] must be reply_target");
    assert_eq!(regs[3], user_data_0, "x3=MR[1] must be user data[0]");
    assert_eq!(regs[4], user_data_1, "x4=MR[2] must be user data[1]");
    assert_eq!(regs[6], 16, "x7=SyscallId::ReplyRecv");
}

// ============================================================================
// AA1 — Rust ABI Type Synchronization conformance tests
// ============================================================================

// --- AA1-B: SyscallId SchedContext variant conformance ---

/// AA1-B-1: SchedContextConfigure roundtrip (discriminant 17).
#[test]
fn aa1b_sched_context_configure_discriminant() {
    let sid = SyscallId::from_u64(17).expect("SchedContextConfigure must exist");
    assert_eq!(sid, SyscallId::SchedContextConfigure);
    assert_eq!(sid.to_u64(), 17);
}

/// AA1-B-2: SchedContextBind roundtrip (discriminant 18).
#[test]
fn aa1b_sched_context_bind_discriminant() {
    let sid = SyscallId::from_u64(18).expect("SchedContextBind must exist");
    assert_eq!(sid, SyscallId::SchedContextBind);
    assert_eq!(sid.to_u64(), 18);
}

/// AA1-B-3: SchedContextUnbind roundtrip (discriminant 19).
#[test]
fn aa1b_sched_context_unbind_discriminant() {
    let sid = SyscallId::from_u64(19).expect("SchedContextUnbind must exist");
    assert_eq!(sid, SyscallId::SchedContextUnbind);
    assert_eq!(sid.to_u64(), 19);
}

/// AA1-B-4/D6: Boundary — discriminant 20 is now TcbSuspend (D1), not out of range.
/// SchedContext range ends at 19; D1/D2/D3 TCB ops occupy 20-24.
#[test]
fn aa1b_sched_context_boundary() {
    // SchedContextUnbind is the last SchedContext variant (19)
    assert_eq!(SyscallId::from_u64(19).unwrap(), SyscallId::SchedContextUnbind);
    // 20 is now TcbSuspend (D1), not out of range
    assert_eq!(SyscallId::from_u64(20).unwrap(), SyscallId::TcbSuspend);
}

/// AA1-B-5: COUNT is updated to 20.
#[test]
fn aa1b_syscall_count_updated() {
    assert_eq!(SyscallId::COUNT, 25);
}

/// AA1-B-6: SchedContext syscalls require Write access (API.lean:381-383).
#[test]
fn aa1b_sched_context_required_rights() {
    use sele4n_types::rights::AccessRight;
    assert_eq!(SyscallId::SchedContextConfigure.required_right(), AccessRight::Write);
    assert_eq!(SyscallId::SchedContextBind.required_right(), AccessRight::Write);
    assert_eq!(SyscallId::SchedContextUnbind.required_right(), AccessRight::Write);
}

// --- AA1-F: SchedContext arg decode conformance ---

/// AA1-F-1: SchedContextConfigureArgs encode/decode roundtrip.
#[test]
fn aa1f_sched_context_configure_roundtrip() {
    use sele4n_abi::args::sched_context::SchedContextConfigureArgs;
    let args = SchedContextConfigureArgs {
        budget: 1000, period: 5000, priority: 200, deadline: 10000, domain: 3,
    };
    let encoded = args.encode();
    let decoded = SchedContextConfigureArgs::decode(&encoded).unwrap();
    assert_eq!(decoded, args);
}

/// AA1-F-2: SchedContextBindArgs encode/decode roundtrip.
#[test]
fn aa1f_sched_context_bind_roundtrip() {
    use sele4n_abi::args::sched_context::SchedContextBindArgs;
    use sele4n_types::ThreadId;
    // AK4-C (R-ABI-H01): `thread_id` is typed `ThreadId` (was raw `u64`).
    let args = SchedContextBindArgs { thread_id: ThreadId::from(42u64) };
    let encoded = args.encode();
    let decoded = SchedContextBindArgs::decode(&encoded).unwrap();
    assert_eq!(decoded, args);
}

/// AA1-F-3: SchedContextUnbindArgs encode/decode roundtrip.
#[test]
fn aa1f_sched_context_unbind_roundtrip() {
    use sele4n_abi::args::sched_context::SchedContextUnbindArgs;
    assert_eq!(SchedContextUnbindArgs::decode(&[]).unwrap(), SchedContextUnbindArgs);
}

/// AA1-F-4: SchedContextConfigureArgs boundary — insufficient registers.
#[test]
fn aa1f_sched_context_configure_insufficient_regs() {
    use sele4n_abi::args::sched_context::SchedContextConfigureArgs;
    assert_eq!(SchedContextConfigureArgs::decode(&[1, 2, 3, 4]), Err(KernelError::InvalidMessageInfo));
}

/// AA1-F-5: SchedContextConfigureArgs boundary — invalid priority.
#[test]
fn aa1f_sched_context_configure_invalid_priority() {
    use sele4n_abi::args::sched_context::SchedContextConfigureArgs;
    assert_eq!(
        SchedContextConfigureArgs::decode(&[1000, 5000, 256, 10000, 0]),
        Err(KernelError::InvalidSyscallArgument)
    );
}

/// AA1-F-6: SchedContextBindArgs boundary — empty registers.
#[test]
fn aa1f_sched_context_bind_insufficient_regs() {
    use sele4n_abi::args::sched_context::SchedContextBindArgs;
    assert_eq!(SchedContextBindArgs::decode(&[]), Err(KernelError::InvalidMessageInfo));
}

/// AA1-F-7: SchedContextConfigureArgs boundary — invalid domain.
/// AG2-A: Domain 16 is first invalid (Lean numDomainsVal = 16, zero-indexed 0..=15).
#[test]
fn aa1f_sched_context_configure_invalid_domain() {
    use sele4n_abi::args::sched_context::SchedContextConfigureArgs;
    // Domain 16 is the first invalid value
    assert_eq!(
        SchedContextConfigureArgs::decode(&[1000, 5000, 128, 10000, 16]),
        Err(KernelError::InvalidSyscallArgument)
    );
    // Domain 256 is also invalid (well beyond range)
    assert_eq!(
        SchedContextConfigureArgs::decode(&[1000, 5000, 128, 10000, 256]),
        Err(KernelError::InvalidSyscallArgument)
    );
}

/// AA1-F-8: SchedContextConfigureArgs — max valid priority (255) and domain (15).
/// AG2-A: Domain max updated from 255 to 15 to match Lean numDomainsVal = 16.
#[test]
fn aa1f_sched_context_configure_max_valid() {
    use sele4n_abi::args::sched_context::SchedContextConfigureArgs;
    let args = SchedContextConfigureArgs::decode(&[1000, 5000, 255, 10000, 15]).unwrap();
    assert_eq!(args.priority, 255);
    assert_eq!(args.domain, 15);
    assert_eq!(args.budget, 1000);
    assert_eq!(args.period, 5000);
    assert_eq!(args.deadline, 10000);
}

/// AA1-F-9: SchedContextConfigureArgs — zero-valued fields accepted.
#[test]
fn aa1f_sched_context_configure_zero_values() {
    use sele4n_abi::args::sched_context::SchedContextConfigureArgs;
    let args = SchedContextConfigureArgs::decode(&[0, 0, 0, 0, 0]).unwrap();
    assert_eq!(args.budget, 0);
    assert_eq!(args.period, 0);
    assert_eq!(args.priority, 0);
    assert_eq!(args.deadline, 0);
    assert_eq!(args.domain, 0);
}

// --- AA1-G: SchedContext TypeTag retype conformance ---

/// AA1-G-1: LifecycleRetypeArgs with TypeTag::SchedContext (discriminant 6).
#[test]
fn aa1g_lifecycle_retype_sched_context() {
    let args = lifecycle::LifecycleRetypeArgs {
        target_obj: ObjId::from(42u64),
        new_type: TypeTag::SchedContext,
        size: 0,
    };
    let encoded = args.encode();
    assert_eq!(encoded[1], 6, "TypeTag::SchedContext must encode as 6");
    let decoded = lifecycle::LifecycleRetypeArgs::decode(&encoded).unwrap();
    assert_eq!(decoded.new_type, TypeTag::SchedContext);
}

/// AA1-G-2: TypeTag boundary — 7 is first invalid value.
#[test]
fn aa1g_type_tag_boundary() {
    assert_eq!(TypeTag::from_u64(7), Err(KernelError::InvalidTypeTag));
    assert_eq!(TypeTag::from_u64(u64::MAX), Err(KernelError::InvalidTypeTag));
}

// --- AA1-H: IpcTimeout error handling conformance ---

/// AA1-H-1: KernelError::IpcTimeout roundtrip (discriminant 42).
#[test]
fn aa1h_ipc_timeout_roundtrip() {
    let err = KernelError::from_u32(42).expect("IpcTimeout must exist at discriminant 42");
    assert_eq!(err, KernelError::IpcTimeout);
    assert_eq!(err as u32, 42);
}

/// AA1-H-2: KernelError::IpcTimeout is distinct from all other variants.
#[test]
fn aa1h_ipc_timeout_distinct() {
    let timeout = KernelError::IpcTimeout;
    for i in 0..42u32 {
        let other = KernelError::from_u32(i).unwrap();
        assert_ne!(timeout, other, "IpcTimeout must be distinct from discriminant {i}");
    }
}

/// AA1-H-3: KernelResult correctly wraps IpcTimeout.
#[test]
fn aa1h_ipc_timeout_result() {
    let result: KernelResult<()> = Err(KernelError::IpcTimeout);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), KernelError::IpcTimeout);
}

/// AA1-H-4/AG3 + AL1b/WS-AL: Boundary — discriminant 51 is out of range
/// (InvalidIrq at 48, InvalidObjectType at 49, NullCapability at 50).
#[test]
fn aa1h_error_boundary_after_invalid_irq() {
    assert!(KernelError::from_u32(48).is_some()); // InvalidIrq
    assert!(KernelError::from_u32(49).is_some()); // InvalidObjectType (AL6)
    assert!(KernelError::from_u32(50).is_some()); // NullCapability (AL1b)
    assert!(KernelError::from_u32(51).is_none());
}

// --- D6: TCB operation conformance ---

/// D6-D1: TcbSuspend roundtrip (discriminant 20).
#[test]
fn d6_tcb_suspend_roundtrip() {
    let sid = SyscallId::from_u64(20).expect("TcbSuspend must exist");
    assert_eq!(sid, SyscallId::TcbSuspend);
    assert_eq!(sid.to_u64(), 20);
}

/// D6-D1: TcbResume roundtrip (discriminant 21).
#[test]
fn d6_tcb_resume_roundtrip() {
    let sid = SyscallId::from_u64(21).expect("TcbResume must exist");
    assert_eq!(sid, SyscallId::TcbResume);
    assert_eq!(sid.to_u64(), 21);
}

/// D6-D1: TcbSetPriority roundtrip (discriminant 22).
#[test]
fn d6_tcb_set_priority_roundtrip() {
    let sid = SyscallId::from_u64(22).expect("TcbSetPriority must exist");
    assert_eq!(sid, SyscallId::TcbSetPriority);
    assert_eq!(sid.to_u64(), 22);
}

/// D6-D1: TcbSetMCPriority roundtrip (discriminant 23).
#[test]
fn d6_tcb_set_mcp_roundtrip() {
    let sid = SyscallId::from_u64(23).expect("TcbSetMCPriority must exist");
    assert_eq!(sid, SyscallId::TcbSetMCPriority);
    assert_eq!(sid.to_u64(), 23);
}

/// D6-D1: TcbSetIPCBuffer roundtrip (discriminant 24).
#[test]
fn d6_tcb_set_ipc_buffer_roundtrip() {
    let sid = SyscallId::from_u64(24).expect("TcbSetIPCBuffer must exist");
    assert_eq!(sid, SyscallId::TcbSetIPCBuffer);
    assert_eq!(sid.to_u64(), 24);
}

/// D6-D5: Boundary — discriminant 25 is out of range for SyscallId.
#[test]
fn d6_syscall_boundary() {
    assert!(SyscallId::from_u64(24).is_some()); // Last valid
    assert!(SyscallId::from_u64(25).is_none()); // First invalid
    assert_eq!(SyscallId::COUNT, 25);
}

/// D6-D6: All TCB operations require Write access (API.lean:387-391).
#[test]
fn d6_tcb_ops_require_write() {
    assert_eq!(SyscallId::TcbSuspend.required_right(), AccessRight::Write);
    assert_eq!(SyscallId::TcbResume.required_right(), AccessRight::Write);
    assert_eq!(SyscallId::TcbSetPriority.required_right(), AccessRight::Write);
    assert_eq!(SyscallId::TcbSetMCPriority.required_right(), AccessRight::Write);
    assert_eq!(SyscallId::TcbSetIPCBuffer.required_right(), AccessRight::Write);
}

/// D6-D3: AlignmentError roundtrip (discriminant 43).
#[test]
fn d6_alignment_error_roundtrip() {
    let err = KernelError::from_u32(43).expect("AlignmentError must exist");
    assert_eq!(err, KernelError::AlignmentError);
    assert_eq!(err as u32, 43);
}

/// D6-F: TCB arg decode conformance.
#[test]
fn d6_tcb_args_roundtrip() {
    use sele4n_abi::args::tcb::*;

    // D1: Suspend/Resume — no arguments
    assert_eq!(SuspendArgs::decode(&[]).unwrap(), SuspendArgs);
    assert_eq!(ResumeArgs::decode(&[]).unwrap(), ResumeArgs);

    // D2: SetPriority/SetMCPriority — priority from MR[0]
    let prio = SetPriorityArgs { new_priority: 128 };
    assert_eq!(SetPriorityArgs::decode(&prio.encode()).unwrap(), prio);
    let mcp = SetMCPriorityArgs { new_mcp: 64 };
    assert_eq!(SetMCPriorityArgs::decode(&mcp.encode()).unwrap(), mcp);

    // D3: SetIPCBuffer — buffer address from MR[0]
    let buf = SetIPCBufferArgs { buffer_addr: 1024 };
    assert_eq!(SetIPCBufferArgs::decode(&buf.encode()).unwrap(), buf);
}

/// D6-F: TCB arg decode error paths.
#[test]
fn d6_tcb_args_errors() {
    use sele4n_abi::args::tcb::*;

    // D2: Priority out of range — Lean returns .invalidArgument (discriminant 39)
    assert_eq!(SetPriorityArgs::decode(&[256]), Err(KernelError::InvalidArgument));
    assert_eq!(SetMCPriorityArgs::decode(&[256]), Err(KernelError::InvalidArgument));

    // D2: Insufficient registers
    assert_eq!(SetPriorityArgs::decode(&[]), Err(KernelError::InvalidMessageInfo));
    assert_eq!(SetMCPriorityArgs::decode(&[]), Err(KernelError::InvalidMessageInfo));

    // D3: Unaligned address
    assert_eq!(SetIPCBufferArgs::decode(&[513]), Err(KernelError::AlignmentError));
    assert_eq!(SetIPCBufferArgs::decode(&[]), Err(KernelError::InvalidMessageInfo));
}

/// D6-G: sele4n-sys TCB wrapper module exists and exports all 5 operations.
#[test]
fn d6_sys_tcb_module_exports() {
    // Verify that the sele4n-sys crate re-exports the tcb module.
    // We can't invoke the actual syscalls (no kernel), but we verify the
    // function signatures exist by referencing them as fn pointers.
    let _suspend: fn(CPtr) -> KernelResult<SyscallResponse> = sele4n_sys::tcb::tcb_suspend;
    let _resume: fn(CPtr) -> KernelResult<SyscallResponse> = sele4n_sys::tcb::tcb_resume;
    let _set_prio: fn(CPtr, u64) -> KernelResult<SyscallResponse> = sele4n_sys::tcb::tcb_set_priority;
    let _set_mcp: fn(CPtr, u64) -> KernelResult<SyscallResponse> = sele4n_sys::tcb::tcb_set_mcp;
    let _set_buf: fn(CPtr, u64) -> KernelResult<SyscallResponse> = sele4n_sys::tcb::tcb_set_ipc_buffer;
}

// ============================================================================
// AG2 — Pre-Hardware Rust ABI Fixes conformance tests
// ============================================================================

/// AG2-A-1: MAX_DOMAIN matches Lean numDomainsVal = 16 (zero-indexed 0..=15).
#[test]
fn ag2a_max_domain_matches_lean() {
    use sele4n_abi::args::sched_context::MAX_DOMAIN;
    assert_eq!(MAX_DOMAIN, 15, "MAX_DOMAIN must be 15 (Lean numDomainsVal = 16, zero-indexed)");
}

/// AG2-A-2: Domain 15 accepted, domain 16 rejected at decode boundary.
#[test]
fn ag2a_domain_boundary_validation() {
    use sele4n_abi::args::sched_context::SchedContextConfigureArgs;

    // Domain 15 (max valid) — accepted
    let args = SchedContextConfigureArgs::decode(&[1000, 5000, 128, 10000, 15]).unwrap();
    assert_eq!(args.domain, 15);

    // Domain 16 (first invalid) — rejected
    assert_eq!(
        SchedContextConfigureArgs::decode(&[1000, 5000, 128, 10000, 16]),
        Err(KernelError::InvalidSyscallArgument)
    );
}

/// AG2-A-3: All valid domain values (0..=15) accepted at decode.
#[test]
fn ag2a_all_valid_domains_accepted() {
    use sele4n_abi::args::sched_context::SchedContextConfigureArgs;
    for domain in 0..=15u64 {
        let result = SchedContextConfigureArgs::decode(&[1000, 5000, 128, 10000, domain]);
        assert!(result.is_ok(), "Domain {} should be accepted", domain);
        assert_eq!(result.unwrap().domain, domain);
    }
}

/// AG2-A-4: All invalid domain values (16..=255 and beyond) rejected at decode.
#[test]
fn ag2a_invalid_domains_rejected() {
    use sele4n_abi::args::sched_context::SchedContextConfigureArgs;
    for domain in [16u64, 17, 100, 255, 256, u64::MAX] {
        assert_eq!(
            SchedContextConfigureArgs::decode(&[1000, 5000, 128, 10000, domain]),
            Err(KernelError::InvalidSyscallArgument),
            "Domain {} should be rejected", domain
        );
    }
}

/// AG2-B: sele4n-sys SchedContext wrapper module exists and exports all 3 operations.
#[test]
fn ag2b_sys_sched_context_module_exports() {
    use sele4n_types::ThreadId;
    let _configure: fn(CPtr, u64, u64, u64, u64, u64, &mut IpcBuffer) -> KernelResult<SyscallResponse> =
        sele4n_sys::sched_context::sched_context_configure;
    // AK4-C: `sched_context_bind` now takes a typed `ThreadId`, matching the
    // Lean `SchedContextBindArgs.threadId : ThreadId` signature.
    let _bind: fn(CPtr, ThreadId) -> KernelResult<SyscallResponse> =
        sele4n_sys::sched_context::sched_context_bind;
    let _unbind: fn(CPtr) -> KernelResult<SyscallResponse> =
        sele4n_sys::sched_context::sched_context_unbind;
}
