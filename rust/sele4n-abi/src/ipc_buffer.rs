// SPDX-License-Identifier: GPL-3.0-or-later
//! IPC buffer — shared memory region for extended IPC operations.
//!
//! When a message exceeds the 4 inline ARM64 registers (x2–x5),
//! overflow registers are stored in this buffer. The kernel reads
//! registers 4..N from the buffer during syscall processing.
//!
//! # Register Mapping
//!
//! | Index  | Location                                        |
//! |--------|-------------------------------------------------|
//! | 0–3    | Inline ARM64 registers x2–x5 (`msg[0..4]` unused) |
//! | 4–119  | IPC buffer `msg[4..120]`                        |
//!
//! The layout is seL4's `seL4_IPCBuffer`, 128 words (1024 bytes): the `tag`
//! word, the 120 `msg` words, then `user_data`, `caps_or_badges` (where the
//! kernel writes the badge of each capability a delivery unwrapped) and the
//! receive path (`receive_cnode`, `receive_index`, `receive_depth`): the slot
//! a receive installs a transferred capability into, seL4's
//! `seL4_SetCapReceivePath`.
//!
//! # Memory Layout
//!
//! The buffer must reside in a page mapped into the thread's virtual
//! address space. Its address is stored in the thread's TCB
//! (`ipcBuffer : VAddr` in Lean).
//!
//! Lean: `SeLe4n/Model/Object/Types.lean` — `TCB.ipcBuffer : VAddr`.
//!
//! # AN8-D (RUST-M08) consumer status
//!
//! The audit's RUST-M08 asked whether `IpcBuffer` is still a stub or has
//! a live consumer. The answer is **live**: this type is consumed by the
//! production syscall wrappers
//! - `sele4n_sys::sched_context_configure` (writes the 5th argument
//!   `deadline` into IPC buffer overflow slot 0 — see
//!   `rust/sele4n-sys/src/sched_context.rs`),
//! - `sele4n_sys::service_register` (writes the 5th argument
//!   `requires_grant` into IPC buffer overflow slot 0 — see
//!   `rust/sele4n-sys/src/service.rs`).
//!
//! Both follow the AK4-A IPC-buffer overflow merge contract documented
//! in `SeLe4n/Kernel/Architecture/IpcBufferRead.lean`. The type is NOT
//! gated behind a feature flag.

use sele4n_types::KernelError;

/// Number of inline message registers on ARM64 (x2–x5).
pub const INLINE_REGS: usize = 4;

/// Maximum total message registers (inline + overflow).
/// Lean: `maxMessageRegisters = 120`.
pub const MAX_MSG_REGS: usize = 120;

/// Number of overflow slots in the IPC buffer.
pub const OVERFLOW_SLOTS: usize = MAX_MSG_REGS - INLINE_REGS;

/// Maximum capability transfer slots per message.
/// Lean: `maxExtraCaps = 3`.
pub const MAX_CAPS: usize = 3;

/// IPC buffer for messages exceeding 4 inline registers.
///
/// seL4's `seL4_IPCBuffer` structure, word for word. All message registers
/// (0..120) are logically part of the IPC message and `msg[i]` is register
/// `i`; the first 4 are passed in ARM64 registers for speed, while registers
/// 4–119 are read/written from this buffer.
///
/// # Example
///
/// ```
/// use sele4n_abi::ipc_buffer::IpcBuffer;
/// let mut buf = IpcBuffer::new();
/// // Write message register 4 (`msg[4]`).
/// buf.set_mr(4, 0xDEAD).unwrap();
/// assert_eq!(buf.get_mr(4).unwrap(), 0xDEAD);
/// // Inline registers 0–3 are carried via `SyscallRequest.msg_regs`,
/// // not through this buffer.
/// ```
#[repr(C)]
#[derive(Clone)]
pub struct IpcBuffer {
    /// The message tag word (seL4's `tag`). The kernel reads the message
    /// info from x1, not from here.
    pub tag: u64,
    /// Message registers: `msg[i]` holds message register `i`. Registers
    /// 0–3 travel in x2–x5, so the kernel reads and writes `msg[4..120]`.
    pub msg: [u64; MAX_MSG_REGS],
    /// User data word (application-defined, not used by kernel).
    pub user_data: u64,
    /// Capability transfer badges: on a delivery, `caps_or_badges[i]` holds
    /// the badge of extra capability `i` when the kernel unwrapped it (the
    /// `MessageInfo`'s `caps_unwrapped` bit `i`).
    pub caps_or_badges: [u64; MAX_CAPS],
    /// The CNode capability, in this thread's CSpace, that the receive slot
    /// is addressed in (seL4's `receiveCNode`).
    pub receive_cnode: u64,
    /// The receive slot's address within that CNode (seL4's `receiveIndex`).
    pub receive_index: u64,
    /// How many bits of `receive_index` resolve the slot (seL4's
    /// `receiveDepth`).
    pub receive_depth: u64,
}

impl Default for IpcBuffer {
    fn default() -> Self {
        Self::new()
    }
}

impl IpcBuffer {
    /// Create a zeroed IPC buffer.
    pub const fn new() -> Self {
        Self {
            tag: 0,
            msg: [0; MAX_MSG_REGS],
            user_data: 0,
            caps_or_badges: [0; MAX_CAPS],
            receive_cnode: 0,
            receive_index: 0,
            receive_depth: 0,
        }
    }

    /// Name the slot a receive installs a transferred capability into: the
    /// slot `index` resolved `depth` bits deep in the CNode that `cnode`
    /// names in this thread's CSpace (seL4's `seL4_SetCapReceivePath`).  A
    /// path that does not resolve to an empty slot receives no capability;
    /// the transfer stops there without a fault, as in seL4.
    #[inline]
    pub fn set_cap_receive_path(&mut self, cnode: u64, index: u64, depth: u64) {
        self.receive_cnode = cnode;
        self.receive_index = index;
        self.receive_depth = depth;
    }

    /// Set a message register by absolute index (0..120).
    ///
    /// AK4-F (R-ABI-M04 / MEDIUM): The historical `set_mr` returned
    /// `Ok(false)` for indices 0..3, which was asymmetric with
    /// [`get_mr`](Self::get_mr) (which returns `Err(InvalidArgument)` for
    /// those indices). `set_mr` now returns `Err(InvalidArgument)` for
    /// indices 0..3 so the two APIs have matching error semantics.
    ///
    /// - Indices 0–3: returns `Err(InvalidArgument)` — inline registers
    ///   live in `SyscallRequest.msg_regs`, not in the buffer.
    /// - Indices 4–119: writes to the overflow buffer, returns `Ok(())`.
    /// - Index ≥ 120: returns `Err(IpcMessageTooLarge)`.
    ///
    /// For callers that explicitly want the legacy overflow-only write,
    /// use [`set_mr_overflow`](Self::set_mr_overflow).
    #[inline]
    pub fn set_mr(&mut self, index: usize, value: u64) -> Result<(), KernelError> {
        if index < INLINE_REGS {
            Err(KernelError::InvalidArgument)
        } else if index < MAX_MSG_REGS {
            self.msg[index] = value;
            Ok(())
        } else {
            Err(KernelError::IpcMessageTooLarge)
        }
    }

    /// AK4-F (R-ABI-M04): Explicit overflow-only write. Unlike `set_mr`,
    /// this accepts indices 0..3 as a no-op (returns `Ok(())` without
    /// touching the buffer, since inline registers are not stored here).
    /// Kept for callers that formerly relied on the "pretend-write" branch
    /// of the legacy `set_mr` API — primarily internal sele4n-sys
    /// wrappers that mirror the full 120-register message.
    #[inline]
    pub fn set_mr_overflow(&mut self, index: usize, value: u64) -> Result<(), KernelError> {
        if index < INLINE_REGS {
            Ok(())
        } else if index < MAX_MSG_REGS {
            self.msg[index] = value;
            Ok(())
        } else {
            Err(KernelError::IpcMessageTooLarge)
        }
    }

    /// Get a message register by absolute index (0..120).
    ///
    /// - Indices 0–3: returns `Err(InvalidArgument)` — those live in
    ///   ARM64 registers, not in the buffer (V1-E/V1-J: corrected from
    ///   `InvalidMessageInfo` which was semantically imprecise).
    /// - Indices 4–119: reads from the overflow buffer.
    /// - Index ≥ 120: returns `Err(IpcMessageTooLarge)`.
    #[inline]
    pub fn get_mr(&self, index: usize) -> Result<u64, KernelError> {
        if index < INLINE_REGS {
            Err(KernelError::InvalidArgument)
        } else if index < MAX_MSG_REGS {
            Ok(self.msg[index])
        } else {
            Err(KernelError::IpcMessageTooLarge)
        }
    }

    /// Clear all message registers to zero.
    pub fn clear_msg(&mut self) {
        self.msg = [0; MAX_MSG_REGS];
    }
}

// U3-I / U-M34: Compile-time layout assertions for `#[repr(C)]` IPC buffer.
//
// These const assertions verify that the IPC buffer layout matches the
// expected memory layout at compile time. If the layout changes (e.g., due
// to struct reordering or field type changes), compilation will fail.
//
// Lean correspondence: `SeLe4n/Model/Object/Types.lean` — `TCB.ipcBuffer`
// is a `VAddr` pointing to this buffer's `tag` word in the thread's virtual
// address space; `IpcBufferRead.ipcBufferOverflowBaseWord` places message
// register 4 at word 5.
const _: () = {
    // Total size: seL4's `seL4_IPCBuffer`, 1 tag + 120 msg + 1 user_data +
    // 3 caps_or_badges + 3 receive-path u64s = 128 u64s = 1024 bytes, the
    // aligned buffer (`args::tcb::IPC_BUFFER_ALIGNMENT`).
    assert!(core::mem::size_of::<IpcBuffer>() == 1024);
    assert!(core::mem::offset_of!(IpcBuffer, tag) == 0);
    assert!(core::mem::offset_of!(IpcBuffer, msg) == 8);
    assert!(core::mem::offset_of!(IpcBuffer, user_data) == 968);
    assert!(core::mem::offset_of!(IpcBuffer, caps_or_badges) == 976);
    assert!(core::mem::offset_of!(IpcBuffer, receive_cnode) == 1000);
    assert!(core::mem::offset_of!(IpcBuffer, receive_index) == 1008);
    assert!(core::mem::offset_of!(IpcBuffer, receive_depth) == 1016);
    assert!(core::mem::align_of::<IpcBuffer>() == 8);
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_is_zeroed() {
        let buf = IpcBuffer::new();
        assert_eq!(buf.tag, 0);
        assert!(buf.msg.iter().all(|&v| v == 0));
        assert_eq!(buf.user_data, 0);
        assert_eq!(buf.caps_or_badges, [0; 3]);
        assert_eq!(
            (buf.receive_cnode, buf.receive_index, buf.receive_depth),
            (0, 0, 0)
        );
    }

    #[test]
    fn set_cap_receive_path_writes_the_three_words() {
        let mut buf = IpcBuffer::new();
        buf.set_cap_receive_path(7, 0x2a, 64);
        assert_eq!(
            (buf.receive_cnode, buf.receive_index, buf.receive_depth),
            (7, 0x2a, 64)
        );
    }

    // AK4-F (R-ABI-M04): `set_mr(0..3)` now returns `Err(InvalidArgument)`
    // for symmetry with `get_mr`. Use `set_mr_overflow` for the legacy
    // no-op-on-inline-index behaviour.
    #[test]
    fn set_mr_inline_returns_error() {
        let mut buf = IpcBuffer::new();
        for i in 0..4 {
            assert_eq!(buf.set_mr(i, 42), Err(KernelError::InvalidArgument));
        }
        // Buffer should be untouched
        assert!(buf.msg.iter().all(|&v| v == 0));
    }

    #[test]
    fn set_mr_overflow_inline_noop() {
        let mut buf = IpcBuffer::new();
        for i in 0..4 {
            assert_eq!(buf.set_mr_overflow(i, 42), Ok(()));
        }
        // Buffer should be untouched
        assert!(buf.msg.iter().all(|&v| v == 0));
    }

    #[test]
    fn set_get_overflow() {
        let mut buf = IpcBuffer::new();
        assert_eq!(buf.set_mr(4, 0xAABB), Ok(()));
        assert_eq!(buf.set_mr(119, 0xCCDD), Ok(()));
        assert_eq!(buf.get_mr(4), Ok(0xAABB));
        assert_eq!(buf.get_mr(119), Ok(0xCCDD));
    }

    #[test]
    fn set_mr_overflow_writes_buffer() {
        let mut buf = IpcBuffer::new();
        assert_eq!(buf.set_mr_overflow(5, 0x1234), Ok(()));
        assert_eq!(buf.get_mr(5), Ok(0x1234));
    }

    #[test]
    fn out_of_bounds() {
        let mut buf = IpcBuffer::new();
        assert_eq!(buf.set_mr(120, 1), Err(KernelError::IpcMessageTooLarge));
        assert_eq!(
            buf.set_mr_overflow(120, 1),
            Err(KernelError::IpcMessageTooLarge)
        );
        assert_eq!(buf.get_mr(120), Err(KernelError::IpcMessageTooLarge));
    }

    #[test]
    fn get_inline_returns_error() {
        let buf = IpcBuffer::new();
        // V1-E/V1-J: inline indices return InvalidArgument (not InvalidMessageInfo)
        for i in 0..4 {
            assert_eq!(buf.get_mr(i), Err(KernelError::InvalidArgument));
        }
    }

    #[test]
    fn clear_msg() {
        let mut buf = IpcBuffer::new();
        buf.set_mr(4, 42).unwrap();
        buf.set_mr(50, 99).unwrap();
        buf.clear_msg();
        assert_eq!(buf.get_mr(4), Ok(0));
        assert_eq!(buf.get_mr(50), Ok(0));
    }

    // AK4-F (R-ABI-M04): Explicit symmetry check — `set_mr(i) = Err(_)`
    // for inline indices iff `get_mr(i) = Err(_)`.
    #[test]
    fn set_get_error_symmetry_inline() {
        let mut buf = IpcBuffer::new();
        for i in 0..INLINE_REGS {
            assert!(buf.set_mr(i, 0).is_err());
            assert!(buf.get_mr(i).is_err());
        }
    }
}
