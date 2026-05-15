// SPDX-License-Identifier: GPL-3.0-or-later
//! Fixture builder for host-side syscall register snapshots.
//!
//! `FixtureBuilder` is the host-runtime entry point for declarative
//! construction of register-file snapshots compatible with the
//! `arm64DefaultLayout` register convention (the kernel-side view of
//! a syscall trap frame's argument registers).
//!
//! Layout per `arm64DefaultLayout`:
//!
//! ```text
//!   index 0 = x0   (cap_addr or msg_regs[0])
//!   index 1 = x1   (msg_info — encoded bitfield)
//!   index 2 = x2   (msg_regs[1])
//!   index 3 = x3   (msg_regs[2])
//!   index 4 = x4   (msg_regs[3])
//!   index 5 = x5   (msg_regs[4])
//!   index 6 = x6   (ipc_buffer_addr)
//!   index 7 = x7   (syscall_id)
//! ```
//!
//! At the foundation phase (RH-H) the builder exposes the minimal
//! surface needed to compose a snapshot:
//!
//! - `with_syscall_id(id)` — sets `x7`.
//! - `with_message_info(info)` — sets `x1` to the encoded bitfield.
//! - `with_cap_addr(addr)` — sets `x0`.
//! - `with_msg_reg(idx, value)` — sets `x[idx + 1]` for `idx in 0..5`.
//! - `with_ipc_buffer_addr(addr)` — sets `x6`.
//! - `build()` — produces a [`FixtureSnapshot`].
//!
//! Later WS-RH phases (RH-B: declarative fixture format; RH-D:
//! structured trace replay) extend the builder with typed-argument
//! convenience methods.

use sele4n_abi::MessageInfo;
use sele4n_types::{CPtr, SyscallId};

/// Number of registers in the kernel-side syscall snapshot
/// (`arm64DefaultLayout`).
///
/// Equal to 8 (`x0..x7`).
pub const REGISTER_COUNT: usize = 8;

/// Register index for `x0` — capability address or first message register.
pub const REG_X0: usize = 0;
/// Register index for `x1` — encoded `MessageInfo`.
pub const REG_X1: usize = 1;
/// Register index for `x2` — `msg_regs[1]`.
pub const REG_X2: usize = 2;
/// Register index for `x3` — `msg_regs[2]`.
pub const REG_X3: usize = 3;
/// Register index for `x4` — `msg_regs[3]`.
pub const REG_X4: usize = 4;
/// Register index for `x5` — `msg_regs[4]`.
pub const REG_X5: usize = 5;
/// Register index for `x6` — IPC-buffer address (TPIDRRO_EL0).
pub const REG_X6: usize = 6;
/// Register index for `x7` — syscall id.
pub const REG_X7: usize = 7;

/// Declarative builder for a [`FixtureSnapshot`].
///
/// Construction is fluent and `&mut self`-based.  All setters are
/// total and infallible; encoding errors (e.g., a malformed
/// `MessageInfo`) are caught at the source (the `MessageInfo` type
/// is constructed via `MessageInfo::new`, which performs bounds
/// checks).
///
/// The builder starts with all registers zeroed.  Calling
/// `build()` consumes the builder and returns a snapshot; the
/// builder may be reused after `clone()` if multiple snapshots
/// from a shared base are needed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixtureBuilder {
    registers: [u64; REGISTER_COUNT],
}

impl FixtureBuilder {
    /// Construct a builder with all registers zeroed.
    pub const fn new() -> Self {
        Self {
            registers: [0; REGISTER_COUNT],
        }
    }

    /// Set the syscall id (`x7`).
    pub fn with_syscall_id(mut self, id: SyscallId) -> Self {
        self.registers[REG_X7] = id.to_u64();
        self
    }

    /// Set the message info (`x1`).
    ///
    /// The provided [`MessageInfo`] is encoded via
    /// [`MessageInfo::encode`].  Encoding is infallible for a
    /// `MessageInfo` constructed via `MessageInfo::new`, which
    /// performs bounds checks on the label/length/extra_caps
    /// fields; the builder therefore propagates the encoded value
    /// directly into `x1` without re-validation.
    ///
    /// If the `MessageInfo` was constructed via a non-validated
    /// path (e.g., direct field assignment in an internal helper),
    /// `encode()` may fail; the builder treats that as a programmer
    /// error and stores zero in `x1` to make the failure
    /// observable in tests.  In production paths, this branch
    /// never fires because `MessageInfo` carries its bounds
    /// invariants by construction.
    pub fn with_message_info(mut self, info: MessageInfo) -> Self {
        self.registers[REG_X1] = info.encode().unwrap_or(0);
        self
    }

    /// Set the capability address (`x0`).
    pub fn with_cap_addr(mut self, addr: CPtr) -> Self {
        self.registers[REG_X0] = addr.raw();
        self
    }

    /// Set a message register.
    ///
    /// `idx` selects the message register slot in the
    /// `msg_regs[0..5]` window mapped to `x2..x6` per
    /// `arm64DefaultLayout`.  Valid range is `0..=4`.  Out-of-range
    /// indices are silently ignored to preserve the fluent API
    /// (no error path); the unit test
    /// `with_msg_reg_out_of_range_no_op` documents this contract.
    ///
    /// `msg_regs[0]` is conventionally placed in `x2` (per
    /// `arm64DefaultLayout`'s offset-by-2 convention); index 0 is
    /// therefore stored at `REG_X2`.
    pub fn with_msg_reg(mut self, idx: usize, value: u64) -> Self {
        let reg_idx = match idx {
            0 => REG_X2,
            1 => REG_X3,
            2 => REG_X4,
            3 => REG_X5,
            // RH-H scaffold: msg_regs[4] would land in x6, which is
            // ipc_buffer_addr.  The convention reserves x6 for the
            // IPC buffer so we stop the message-register window at
            // index 3.  Indices 4+ are silently ignored.
            _ => return self,
        };
        self.registers[reg_idx] = value;
        self
    }

    /// Set the IPC-buffer address (`x6`).
    ///
    /// Per `arm64DefaultLayout`, `x6` carries the caller's IPC
    /// buffer address (read from `TPIDRRO_EL0` on hardware).  A
    /// zero value signals "no IPC buffer registered" — the
    /// kernel-side dispatcher converts this to `Option::None`
    /// (see `sele4n-hal::svc_dispatch::SyscallArgs::from_trap_frame`).
    pub fn with_ipc_buffer_addr(mut self, addr: u64) -> Self {
        self.registers[REG_X6] = addr;
        self
    }

    /// Consume the builder and produce a [`FixtureSnapshot`].
    pub const fn build(self) -> FixtureSnapshot {
        FixtureSnapshot {
            registers: self.registers,
        }
    }
}

impl Default for FixtureBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Immutable register-file snapshot produced by [`FixtureBuilder`].
///
/// The snapshot owns its `[u64; 8]` register array.  Read access is
/// via [`Self::registers`] or per-register accessors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FixtureSnapshot {
    registers: [u64; REGISTER_COUNT],
}

impl FixtureSnapshot {
    /// The full `[u64; 8]` register array.
    ///
    /// Per `arm64DefaultLayout`:
    /// - `[0]` = `x0` (cap_addr)
    /// - `[1]` = `x1` (encoded message info)
    /// - `[2..6]` = `x2..x5` (message registers)
    /// - `[6]` = `x6` (IPC-buffer address)
    /// - `[7]` = `x7` (syscall id)
    #[inline]
    pub const fn registers(&self) -> &[u64; REGISTER_COUNT] {
        &self.registers
    }

    /// Get a single register by index.  Returns `None` for out-of-
    /// range indices.
    #[inline]
    pub fn register(&self, idx: usize) -> Option<u64> {
        self.registers.get(idx).copied()
    }

    /// Get `x0` (cap_addr).
    #[inline]
    pub const fn x0(&self) -> u64 {
        self.registers[REG_X0]
    }

    /// Get `x1` (encoded message info).
    #[inline]
    pub const fn x1(&self) -> u64 {
        self.registers[REG_X1]
    }

    /// Get `x6` (IPC-buffer address).
    #[inline]
    pub const fn x6(&self) -> u64 {
        self.registers[REG_X6]
    }

    /// Get `x7` (syscall id).
    #[inline]
    pub const fn x7(&self) -> u64 {
        self.registers[REG_X7]
    }

    /// Decode `x7` into a [`SyscallId`] when it is a valid syscall
    /// discriminant.
    ///
    /// Returns `None` if `x7` is outside the valid 0..=24 range
    /// (the same gate the kernel-side dispatcher applies via
    /// `SyscallId::from_u64`).
    pub fn decoded_syscall_id(&self) -> Option<SyscallId> {
        SyscallId::from_u64(self.x7())
    }

    /// Decode `x1` into a [`MessageInfo`] when it is a valid
    /// encoding.
    ///
    /// Returns `None` if the encoded word's `length`, `extra_caps`,
    /// or `label` field exceeds their respective bounds (the
    /// same gate the kernel-side dispatcher applies via
    /// `MessageInfo::decode`).
    pub fn decoded_message_info(&self) -> Option<MessageInfo> {
        MessageInfo::decode(self.x1()).ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_builder_has_zero_registers() {
        let snap = FixtureBuilder::new().build();
        for r in snap.registers() {
            assert_eq!(*r, 0);
        }
    }

    #[test]
    fn default_builder_matches_new() {
        let a = FixtureBuilder::default().build();
        let b = FixtureBuilder::new().build();
        assert_eq!(a, b);
    }

    #[test]
    fn with_syscall_id_sets_x7() {
        let snap = FixtureBuilder::new()
            .with_syscall_id(SyscallId::CSpaceMint)
            .build();
        // SyscallId::CSpaceMint == 4 per sele4n-types
        assert_eq!(snap.x7(), 4);
    }

    #[test]
    fn with_message_info_sets_x1() {
        let info = MessageInfo::new(2, 1, 0x100).unwrap();
        let snap = FixtureBuilder::new().with_message_info(info).build();
        assert_eq!(snap.x1(), info.encode().unwrap());
    }

    #[test]
    fn with_cap_addr_sets_x0() {
        let snap = FixtureBuilder::new()
            .with_cap_addr(CPtr::from(42u64))
            .build();
        assert_eq!(snap.x0(), 42);
    }

    #[test]
    fn with_ipc_buffer_addr_sets_x6() {
        let snap = FixtureBuilder::new()
            .with_ipc_buffer_addr(0xDEAD_BEEF)
            .build();
        assert_eq!(snap.x6(), 0xDEAD_BEEF);
    }

    #[test]
    fn with_msg_reg_maps_to_x2_through_x5() {
        let snap = FixtureBuilder::new()
            .with_msg_reg(0, 0xAAAA)
            .with_msg_reg(1, 0xBBBB)
            .with_msg_reg(2, 0xCCCC)
            .with_msg_reg(3, 0xDDDD)
            .build();
        assert_eq!(snap.registers()[REG_X2], 0xAAAA);
        assert_eq!(snap.registers()[REG_X3], 0xBBBB);
        assert_eq!(snap.registers()[REG_X4], 0xCCCC);
        assert_eq!(snap.registers()[REG_X5], 0xDDDD);
    }

    #[test]
    fn with_msg_reg_out_of_range_no_op() {
        let baseline = FixtureBuilder::new().build();
        let mutated = FixtureBuilder::new().with_msg_reg(99, 0xFFFF).build();
        assert_eq!(baseline, mutated);
    }

    #[test]
    fn register_count_is_eight() {
        let snap = FixtureBuilder::new().build();
        assert_eq!(snap.registers().len(), 8);
    }

    #[test]
    fn register_out_of_range_returns_none() {
        let snap = FixtureBuilder::new().build();
        assert_eq!(snap.register(8), None);
        assert_eq!(snap.register(usize::MAX), None);
    }

    #[test]
    fn register_in_range_returns_some() {
        let snap = FixtureBuilder::new().with_cap_addr(CPtr::from(99u64)).build();
        assert_eq!(snap.register(0), Some(99));
        assert_eq!(snap.register(1), Some(0));
        assert_eq!(snap.register(7), Some(0));
    }

    #[test]
    fn decoded_syscall_id_round_trips() {
        for sid in [
            SyscallId::Send,
            SyscallId::Receive,
            SyscallId::CSpaceMint,
            SyscallId::TcbSuspend,
        ] {
            let snap = FixtureBuilder::new().with_syscall_id(sid).build();
            assert_eq!(snap.decoded_syscall_id(), Some(sid));
        }
    }

    #[test]
    fn decoded_syscall_id_returns_none_for_invalid() {
        // 25 is outside the valid 0..=24 range.
        let mut builder = FixtureBuilder::new();
        builder.registers[REG_X7] = 25;
        let snap = builder.build();
        assert_eq!(snap.decoded_syscall_id(), None);
    }

    #[test]
    fn decoded_message_info_round_trips() {
        let info = MessageInfo::new(5, 2, 0xABCDE).unwrap();
        let snap = FixtureBuilder::new().with_message_info(info).build();
        assert_eq!(snap.decoded_message_info(), Some(info));
    }

    #[test]
    fn decoded_message_info_returns_none_for_invalid() {
        // A raw word whose length field exceeds MAX_MSG_LENGTH
        // (120) does not decode to a valid MessageInfo.
        let mut builder = FixtureBuilder::new();
        // length = 125 (> 120), extra_caps = 0, label = 0.
        builder.registers[REG_X1] = 125;
        let snap = builder.build();
        assert_eq!(snap.decoded_message_info(), None);
    }

    #[test]
    fn fluent_builder_chains_multiple_setters() {
        let info = MessageInfo::new(3, 1, 0x123).unwrap();
        let snap = FixtureBuilder::new()
            .with_cap_addr(CPtr::from(7u64))
            .with_message_info(info)
            .with_msg_reg(0, 0x10)
            .with_msg_reg(1, 0x20)
            .with_ipc_buffer_addr(0x40000000)
            .with_syscall_id(SyscallId::Send)
            .build();
        assert_eq!(snap.x0(), 7);
        assert_eq!(snap.x1(), info.encode().unwrap());
        assert_eq!(snap.registers()[REG_X2], 0x10);
        assert_eq!(snap.registers()[REG_X3], 0x20);
        assert_eq!(snap.x6(), 0x40000000);
        assert_eq!(snap.x7(), 0); // SyscallId::Send == 0
    }
}
