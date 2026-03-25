//! IPC buffer — shared memory region for extended IPC operations.
//!
//! When a message exceeds the 4 inline ARM64 registers (x2–x5),
//! overflow registers are stored in this buffer. The kernel reads
//! registers 4..N from the buffer during syscall processing.
//!
//! # Register Mapping
//!
//! | Index  | Location                          |
//! |--------|-----------------------------------|
//! | 0–3    | Inline ARM64 registers x2–x5      |
//! | 4–119  | IPC buffer `msg[0..116]`          |
//!
//! # Memory Layout
//!
//! The buffer must reside in a page mapped into the thread's virtual
//! address space. Its address is stored in the thread's TCB
//! (`ipcBuffer : VAddr` in Lean).
//!
//! Lean: `SeLe4n/Model/Object/Types.lean` — `TCB.ipcBuffer : VAddr`.

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
/// Mirrors seL4's `seL4_IPCBuffer` structure. All message registers
/// (0..120) are logically part of the IPC message; the first 4 are
/// passed in ARM64 registers for speed, while registers 4–119 are
/// read/written from this buffer.
///
/// # Example
///
/// ```ignore
/// let mut buf = IpcBuffer::new();
/// // Write overflow register 4 (index 0 in buffer)
/// buf.set_mr(4, 0xDEAD).unwrap();
/// // Inline registers 0–3 go via SyscallRequest.msg_regs
/// ```
#[repr(C)]
#[derive(Clone)]
pub struct IpcBuffer {
    /// Overflow message registers.
    /// `msg[i]` holds message register `i + 4`.
    pub msg: [u64; OVERFLOW_SLOTS],
    /// User data word (application-defined, not used by kernel).
    pub user_data: u64,
    /// Capability transfer badges/addresses.
    pub caps_or_badges: [u64; MAX_CAPS],
}

impl Default for IpcBuffer {
    fn default() -> Self { Self::new() }
}

impl IpcBuffer {
    /// Create a zeroed IPC buffer.
    pub const fn new() -> Self {
        Self {
            msg: [0; OVERFLOW_SLOTS],
            user_data: 0,
            caps_or_badges: [0; MAX_CAPS],
        }
    }

    /// Set a message register by absolute index (0..120).
    ///
    /// - Indices 0–3: returns `Ok(false)` — caller must place these in
    ///   `SyscallRequest.msg_regs` (inline ARM64 registers).
    /// - Indices 4–119: writes to the overflow buffer, returns `Ok(true)`.
    /// - Index ≥ 120: returns `Err(IpcMessageTooLarge)`.
    #[inline]
    pub fn set_mr(&mut self, index: usize, value: u64) -> Result<bool, KernelError> {
        if index < INLINE_REGS {
            Ok(false)
        } else if index < MAX_MSG_REGS {
            self.msg[index - INLINE_REGS] = value;
            Ok(true)
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
            Ok(self.msg[index - INLINE_REGS])
        } else {
            Err(KernelError::IpcMessageTooLarge)
        }
    }

    /// Clear all overflow message registers to zero.
    pub fn clear_msg(&mut self) {
        self.msg = [0; OVERFLOW_SLOTS];
    }
}

// U3-I / U-M34: Compile-time layout assertions for `#[repr(C)]` IPC buffer.
//
// These const assertions verify that the IPC buffer layout matches the
// expected memory layout at compile time. If the layout changes (e.g., due
// to struct reordering or field type changes), compilation will fail.
//
// Lean correspondence: `SeLe4n/Model/Object/Types.lean` — `TCB.ipcBuffer`
// is a `VAddr` pointing to this buffer in the thread's virtual address space.
// The kernel reads overflow message registers starting at offset 0.
const _: () = {
    // Total size: 116 overflow u64s + 1 user_data u64 + 3 caps u64s = 120 u64s = 960 bytes
    assert!(core::mem::size_of::<IpcBuffer>() == 960);
    // Alignment: u64 = 8 bytes
    assert!(core::mem::align_of::<IpcBuffer>() == 8);
    // Field offset: msg starts at offset 0 (first field in repr(C))
    // Field offset: user_data at 116 * 8 = 928
    // Field offset: caps_or_badges at 928 + 8 = 936
    // Verify total: 116 * 8 + 8 + 3 * 8 = 928 + 8 + 24 = 960 ✓
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_is_zeroed() {
        let buf = IpcBuffer::new();
        assert!(buf.msg.iter().all(|&v| v == 0));
        assert_eq!(buf.user_data, 0);
        assert_eq!(buf.caps_or_badges, [0; 3]);
    }

    #[test]
    fn set_mr_inline_returns_false() {
        let mut buf = IpcBuffer::new();
        for i in 0..4 {
            assert_eq!(buf.set_mr(i, 42), Ok(false));
        }
        // Buffer should be untouched
        assert!(buf.msg.iter().all(|&v| v == 0));
    }

    #[test]
    fn set_get_overflow() {
        let mut buf = IpcBuffer::new();
        assert_eq!(buf.set_mr(4, 0xAABB), Ok(true));
        assert_eq!(buf.set_mr(119, 0xCCDD), Ok(true));
        assert_eq!(buf.get_mr(4), Ok(0xAABB));
        assert_eq!(buf.get_mr(119), Ok(0xCCDD));
    }

    #[test]
    fn out_of_bounds() {
        let mut buf = IpcBuffer::new();
        assert_eq!(buf.set_mr(120, 1), Err(KernelError::IpcMessageTooLarge));
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
}
