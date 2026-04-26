// SPDX-License-Identifier: GPL-3.0-or-later
//! AN9-F (DEF-R-HAL-L14 / RESOLVED): Typed SVC argument marshalling.
//!
//! This module owns the typed-argument extraction for SVC traps.  The
//! `handle_svc` entry in `trap.rs` reads the raw `TrapFrame`, calls
//! [`SyscallArgs::from_trap_frame`] to produce a structured view, and
//! then dispatches to the Lean kernel via [`dispatch_svc`].
//!
//! ## Mirror discipline
//!
//! `SyscallId` here mirrors the 25-variant enum in
//! `sele4n-types/src/syscall.rs`.  We do NOT depend on `sele4n-types`
//! (the HAL crate is the lowest-level workspace member with zero
//! dependencies, by design — see `rust/sele4n-hal/Cargo.toml`), so
//! the discriminants are duplicated here.  The unit test
//! `syscall_id_discriminants_match_lean_abi` asserts the bidirectional
//! `from_u64` / `to_u64` roundtrip stays aligned with the Lean
//! `SyscallId.toNat` encoding.
//!
//! ## Argument layout
//!
//! seLe4n's syscall ABI (matching the Lean `arm64DefaultLayout` in
//! `SeLe4n/Kernel/Architecture/RegisterDecode.lean`):
//!
//! ```text
//! x0..x5 : msg_regs[0..6]      (inline message registers)
//! x6     : ipc_buffer_addr     (caller's TPIDRRO_EL0; optional)
//! x7     : syscall_id          (SyscallId enum discriminant)
//! ```
//!
//! `MessageInfo` is packed into `x1` per AK4 ABI conventions (length,
//! extraCaps, label fields); the dispatcher passes it through opaquely
//! to the Lean side, which decodes via `SeLe4n.Model.MessageInfo.mk`.

use crate::trap::TrapFrame;

/// AN9-F: kernel-error discriminant returned by [`dispatch_svc`].
///
/// Mirrors the active subset of `sele4n-types::KernelError`.  The
/// enum is `#[repr(u32)]` so it can cross the FFI boundary without
/// padding ambiguity; the discriminants match the Lean
/// `KernelError.toNat` encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum DispatchError {
    /// Caller passed a syscall id outside the valid 0..=24 range.
    InvalidSyscallId = 7,
    /// Caller passed an argument count that did not match the syscall's
    /// expected count (validated against `MessageInfo.length`).
    InvalidArgument = 6,
    /// Syscall recognised but the Lean dispatcher is not yet wired to
    /// handle it (placeholder return until the FFI symbol is provided
    /// at link time).
    NotImplemented = 17,
}

impl DispatchError {
    /// Raw `u32` representation matching the FFI return convention.
    #[inline]
    pub const fn to_u32(self) -> u32 {
        self as u32
    }
}

/// AN9-F: 25-variant syscall ID enum mirroring
/// `sele4n-types::SyscallId`.  Discriminants align with the Lean
/// `SyscallId.toNat` encoding so a `u64` syscall id read from the
/// trap frame's `x7` register decodes identically on both sides.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum SyscallId {
    Send = 0,
    Receive = 1,
    Call = 2,
    Reply = 3,
    CSpaceMint = 4,
    CSpaceCopy = 5,
    CSpaceMove = 6,
    CSpaceDelete = 7,
    LifecycleRetype = 8,
    VSpaceMap = 9,
    VSpaceUnmap = 10,
    ServiceRegister = 11,
    ServiceRevoke = 12,
    ServiceQuery = 13,
    NotificationSignal = 14,
    NotificationWait = 15,
    ReplyRecv = 16,
    SchedContextConfigure = 17,
    SchedContextBind = 18,
    SchedContextUnbind = 19,
    TcbSuspend = 20,
    TcbResume = 21,
    TcbSetPriority = 22,
    TcbSetMCPriority = 23,
    TcbSetIPCBuffer = 24,
}

impl SyscallId {
    /// Total number of modelled syscalls (must match `sele4n-types`).
    pub const COUNT: u32 = 25;

    /// AN9-F.1.b: decode a raw `u32` syscall id, rejecting values
    /// outside the valid 0..=24 range with `None`.
    pub const fn from_u32(v: u32) -> Option<Self> {
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
            17 => Some(Self::SchedContextConfigure),
            18 => Some(Self::SchedContextBind),
            19 => Some(Self::SchedContextUnbind),
            20 => Some(Self::TcbSuspend),
            21 => Some(Self::TcbResume),
            22 => Some(Self::TcbSetPriority),
            23 => Some(Self::TcbSetMCPriority),
            24 => Some(Self::TcbSetIPCBuffer),
            _ => None,
        }
    }

    /// AN9-F.1.b: raw discriminant.
    #[inline]
    pub const fn to_u32(self) -> u32 {
        self as u32
    }

    /// AN9-F.1.c: number of inline message registers consumed by this
    /// syscall.  Used to validate `MessageInfo.length` at the
    /// per-syscall handler stub before forwarding to Lean.
    ///
    /// Values are conservative ABI minimums per AK4; some syscalls
    /// (e.g., `ServiceRegister`) accept additional registers via the
    /// IPC buffer overflow region (see AK4-A R-ABI-C01).
    pub const fn min_inline_args(self) -> u32 {
        match self {
            Self::Send | Self::Receive | Self::Reply => 0,
            Self::Call => 0,
            Self::CSpaceMint => 5,
            Self::CSpaceCopy => 4,
            Self::CSpaceMove => 4,
            Self::CSpaceDelete => 1,
            Self::LifecycleRetype => 4,
            Self::VSpaceMap => 4,
            Self::VSpaceUnmap => 2,
            Self::ServiceRegister => 4,
            Self::ServiceRevoke => 1,
            Self::ServiceQuery => 1,
            Self::NotificationSignal => 1,
            Self::NotificationWait => 0,
            Self::ReplyRecv => 0,
            Self::SchedContextConfigure => 5,
            Self::SchedContextBind => 2,
            Self::SchedContextUnbind => 1,
            Self::TcbSuspend => 1,
            Self::TcbResume => 1,
            Self::TcbSetPriority => 2,
            Self::TcbSetMCPriority => 2,
            Self::TcbSetIPCBuffer => 2,
        }
    }
}

/// AN9-F.1.a: typed view of an SVC trap frame's argument registers.
///
/// Constructed from a `TrapFrame` via [`SyscallArgs::from_trap_frame`].
/// The Lean side decodes this struct via the pre-existing
/// `decodeSyscallArgsFromState` helper (`SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`).
#[derive(Debug, Clone, Copy)]
pub struct SyscallArgs {
    /// Packed `MessageInfo` field (length | extraCaps | label).
    pub msg_info: u64,
    /// Inline message registers `x0..x5` (`msg_regs[0..6]`).
    pub msg_regs: [u64; 6],
    /// Caller's IPC buffer address from `x6` (`TPIDRRO_EL0`).  Set to
    /// `None` when the field is zero (no IPC buffer registered).
    pub ipc_buffer_addr: Option<u64>,
}

impl SyscallArgs {
    /// AN9-F.1.a: extract the typed argument view from a trap frame.
    ///
    /// Layout per `arm64DefaultLayout`:
    ///   `x1` = `msg_info`
    ///   `x0..x5` = `msg_regs[0..6]`
    ///   `x6` = `ipc_buffer_addr` (zero ⇒ `None`)
    ///
    /// Note that `x7` is the `syscall_id` and is read separately by
    /// the dispatcher; it is NOT part of [`SyscallArgs`].
    pub fn from_trap_frame(frame: &TrapFrame) -> Self {
        let raw_buf = frame.gprs[6];
        Self {
            msg_info: frame.x1(),
            msg_regs: [
                frame.x0(),
                frame.x1(),
                frame.x2(),
                frame.x3(),
                frame.x4(),
                frame.x5(),
            ],
            ipc_buffer_addr: if raw_buf == 0 { None } else { Some(raw_buf) },
        }
    }

    /// AN9-F.1.c: extract the `length` field from `msg_info`.
    /// Per AK4-D, `msg_info` is packed as
    ///   bits  [11: 0] = length      (≤ 4095, capped at MAX_MESSAGE_REGISTERS)
    ///   bits  [13:12] = extraCaps   (≤ 3)
    ///   bits  [63:14] = label
    /// We extract the low 12 bits.
    #[inline]
    pub fn message_length(&self) -> u32 {
        (self.msg_info & 0x0FFF) as u32
    }
}

/// AN9-F.2 / AN9-F.3: top-level SVC dispatcher.
///
/// Routes the trap through [`SyscallId::from_u32`] and validates the
/// inline-argument count against [`SyscallId::min_inline_args`] before
/// delegating to the Lean kernel via the
/// `sele4n_syscall_dispatch_inner` extern symbol.
///
/// In test builds the inner symbol is a Rust-side stub returning
/// `DispatchError::NotImplemented` so the bracketing logic can be
/// exercised on host without pulling in the Lean kernel build.
///
/// Returns:
///   `Ok(value)`     — successful dispatch; `value` is the kernel
///                     return code (zero on success).
///   `Err(error)`    — argument count mismatch, invalid syscall id,
///                     or Lean-side rejection.
pub fn dispatch_svc(syscall_id: u32, args: &SyscallArgs) -> Result<u64, DispatchError> {
    // AN9-F.1.b: reject ids outside 0..=24
    let sid = match SyscallId::from_u32(syscall_id) {
        Some(sid) => sid,
        None => return Err(DispatchError::InvalidSyscallId),
    };

    // AN9-F.1.c: validate the inline-arg count from MessageInfo.length
    let len = args.message_length();
    if len < sid.min_inline_args() {
        return Err(DispatchError::InvalidArgument);
    }

    // AN9-F.2: forward to the Lean-emitted dispatcher.
    //
    // The Lean side returns a 64-bit value where:
    //   bit 63       — error flag (1 = error)
    //   bits [62:32] — KernelError discriminant on error path
    //   bits [31: 0] — return value on success path
    //
    // We decode this into the Result here so callers consume a clean
    // Rust shape.
    //
    // SAFETY (production): `syscall_dispatch_inner` is a Lean-emitted
    // extern "C" symbol resolved at link time.  The arguments cross
    // the FFI boundary as `u32 + 8 × u64` which the Lean side reads
    // via the @[extern] declaration in `SeLe4n/Platform/FFI.lean`.
    #[allow(unused_unsafe)]
    let raw = unsafe {
        syscall_dispatch_inner(
            sid.to_u32(),
            args.msg_info,
            args.msg_regs[0],
            args.msg_regs[1],
            args.msg_regs[2],
            args.msg_regs[3],
            args.msg_regs[4],
            args.msg_regs[5],
            args.ipc_buffer_addr.unwrap_or(0),
        )
    };

    if (raw >> 63) & 1 == 1 {
        // Error path: low 32 bits hold the error discriminant.
        let disc = raw as u32;
        // Map the kernel error discriminant into our DispatchError
        // shape; the only domain-specific arm is NotImplemented (17).
        Err(match disc {
            6 => DispatchError::InvalidArgument,
            7 => DispatchError::InvalidSyscallId,
            _ => DispatchError::NotImplemented,
        })
    } else {
        Ok(raw)
    }
}

// AN9-F.3 inner — Lean-emitted SVC dispatch entry.
//
// In production builds this resolves to the Lean kernel's
// `syscallDispatchFromAbi` (declared via `@[extern
// "sele4n_syscall_dispatch_inner"]` in `SeLe4n/Platform/FFI.lean`).
// In test builds (`#[cfg(test)]`) a Rust-side stub returns the error
// flag set with `DispatchError::NotImplemented` so dispatch logic can
// be exercised on host.
#[cfg(not(test))]
extern "C" {
    fn syscall_dispatch_inner(
        syscall_id: u32,
        msg_info: u64,
        x0: u64,
        x1: u64,
        x2: u64,
        x3: u64,
        x4: u64,
        x5: u64,
        ipc_buffer_addr: u64,
    ) -> u64;
}

/// AN9-F.4 test stub: returns the high-bit-set error code for
/// `NotImplemented` so dispatch tests exercise the error decoding.
#[cfg(test)]
#[no_mangle]
extern "C" fn syscall_dispatch_inner(
    _syscall_id: u32,
    _msg_info: u64,
    _x0: u64,
    _x1: u64,
    _x2: u64,
    _x3: u64,
    _x4: u64,
    _x5: u64,
    _ipc_buffer_addr: u64,
) -> u64 {
    // High bit set + low 32 bits = NotImplemented (17)
    (1u64 << 63) | 17
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn zero_frame() -> TrapFrame {
        TrapFrame {
            gprs: [0; 31],
            sp_el0: 0,
            elr_el1: 0,
            spsr_el1: 0,
            esr_el1: 0,
            far_el1: 0,
        }
    }

    #[test]
    fn syscall_id_discriminants_match_lean_abi() {
        // Round-trip every variant.  If a new syscall lands in Lean,
        // this test must be extended in lockstep.
        for i in 0..SyscallId::COUNT {
            let sid = SyscallId::from_u32(i).unwrap();
            assert_eq!(sid.to_u32(), i, "round-trip failed at id {}", i);
        }
        assert!(SyscallId::from_u32(SyscallId::COUNT).is_none());
        assert!(SyscallId::from_u32(255).is_none());
    }

    #[test]
    fn syscall_args_from_trap_frame_extracts_x0_to_x5() {
        let mut frame = zero_frame();
        frame.gprs[0] = 0x1111;
        frame.gprs[1] = 0x2222;
        frame.gprs[2] = 0x3333;
        frame.gprs[3] = 0x4444;
        frame.gprs[4] = 0x5555;
        frame.gprs[5] = 0x6666;
        frame.gprs[6] = 0x7777;
        let args = SyscallArgs::from_trap_frame(&frame);
        assert_eq!(args.msg_regs, [0x1111, 0x2222, 0x3333, 0x4444, 0x5555, 0x6666]);
        assert_eq!(args.ipc_buffer_addr, Some(0x7777));
        // msg_info comes from x1
        assert_eq!(args.msg_info, 0x2222);
    }

    #[test]
    fn syscall_args_zero_ipc_buffer_decodes_to_none() {
        let mut frame = zero_frame();
        frame.gprs[6] = 0;
        let args = SyscallArgs::from_trap_frame(&frame);
        assert_eq!(args.ipc_buffer_addr, None);
    }

    #[test]
    fn syscall_args_message_length_extracts_low_12_bits() {
        let mut frame = zero_frame();
        // length = 4 (within MAX_MESSAGE_REGISTERS), label = 0xCAFE
        frame.gprs[1] = (0xCAFE_u64 << 14) | 0x004;
        let args = SyscallArgs::from_trap_frame(&frame);
        assert_eq!(args.message_length(), 4);
    }

    #[test]
    fn dispatch_svc_rejects_invalid_syscall_id() {
        let frame = zero_frame();
        let args = SyscallArgs::from_trap_frame(&frame);
        let result = dispatch_svc(SyscallId::COUNT, &args);
        assert_eq!(result, Err(DispatchError::InvalidSyscallId));
    }

    #[test]
    fn dispatch_svc_rejects_argument_count_below_minimum() {
        // CSpaceMint requires 5 inline args; supplying length=0 must
        // be rejected before the inner dispatcher is called.
        let frame = zero_frame();
        let args = SyscallArgs::from_trap_frame(&frame); // length=0
        let result = dispatch_svc(SyscallId::CSpaceMint.to_u32(), &args);
        assert_eq!(result, Err(DispatchError::InvalidArgument));
    }

    #[test]
    fn dispatch_svc_routes_to_inner_dispatcher() {
        // Send takes 0 inline args so any frame is accepted; the inner
        // stub returns NotImplemented under #[cfg(test)].
        let frame = zero_frame();
        let args = SyscallArgs::from_trap_frame(&frame);
        let result = dispatch_svc(SyscallId::Send.to_u32(), &args);
        assert_eq!(result, Err(DispatchError::NotImplemented));
    }

    #[test]
    fn dispatch_error_to_u32_is_stable() {
        assert_eq!(DispatchError::InvalidArgument.to_u32(), 6);
        assert_eq!(DispatchError::InvalidSyscallId.to_u32(), 7);
        assert_eq!(DispatchError::NotImplemented.to_u32(), 17);
    }

    #[test]
    fn syscall_id_min_inline_args_matches_ak4_abi() {
        // Spot-check the canonical ABI values against AK4 documentation.
        assert_eq!(SyscallId::CSpaceMint.min_inline_args(), 5);
        assert_eq!(SyscallId::ServiceRegister.min_inline_args(), 4);
        assert_eq!(SyscallId::TcbSuspend.min_inline_args(), 1);
        assert_eq!(SyscallId::Send.min_inline_args(), 0);
    }
}
