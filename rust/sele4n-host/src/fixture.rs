// SPDX-License-Identifier: GPL-3.0-or-later
//! Fixture builder for host-side syscall register snapshots.
//!
//! `FixtureBuilder` is the host-runtime entry point for declarative
//! construction of register-file snapshots compatible with the
//! `arm64DefaultLayout` register convention (the encoder-side view
//! of a syscall trap frame's argument registers).
//!
//! ## Register layout
//!
//! The Lean source `SeLe4n.arm64DefaultLayout`
//! (`SeLe4n/Machine.lean:971`) declares four canonical register
//! slots:
//!
//! ```text
//!   x0 = capPtrReg     (cap_addr)
//!   x1 = msgInfoReg    (encoded MessageInfo bitfield)
//!   x2..x5 = msgRegs   (4 inline message registers)
//!   x7 = syscallNumReg (syscall id)
//! ```
//!
//! `arm64DefaultLayout` does not assign `x6` an encoder-side
//! meaning.  The kernel-side trap handler
//! (`sele4n-hal::svc_dispatch::SyscallArgs::from_trap_frame`)
//! repurposes `x6` to carry the caller's IPC-buffer address (read
//! from `TPIDRRO_EL0`), and the host fixture mirrors that
//! convention so an off-target test can reconstruct the kernel-side
//! trap-frame observation register-by-register.
//!
//! ## Snapshot index → register mapping
//!
//! The snapshot is a `[u64; 8]` flat array indexed by the canonical
//! `x`-register number:
//!
//! ```text
//!   snapshot[0] = x0  (cap_addr)
//!   snapshot[1] = x1  (encoded msg_info)
//!   snapshot[2] = x2  (msg_regs[0])      ← idx 0 in `with_msg_reg`
//!   snapshot[3] = x3  (msg_regs[1])      ← idx 1 in `with_msg_reg`
//!   snapshot[4] = x4  (msg_regs[2])      ← idx 2 in `with_msg_reg`
//!   snapshot[5] = x5  (msg_regs[3])      ← idx 3 in `with_msg_reg`
//!   snapshot[6] = x6  (ipc_buffer_addr; kernel-side, not in
//!                       arm64DefaultLayout)
//!   snapshot[7] = x7  (syscall_id)
//! ```
//!
//! The `msg_regs[i]` numbering follows the
//! `sele4n-abi::SyscallRequest::msg_regs` convention
//! (`[u64; 4]` indexed 0..=3, mapped to `x(i+2)`).  The Lean side
//! refers to these as `arm64DefaultLayout.msgRegs` (`#[⟨2⟩, ⟨3⟩,
//! ⟨4⟩, ⟨5⟩]`).
//!
//! ## Builder surface (RH-H)
//!
//! - `with_cap_addr(addr)` — sets `x0`.
//! - `with_message_info(info)` — sets `x1` to the encoded bitfield.
//! - `with_msg_reg(idx, value)` — sets `x(idx + 2)` for
//!   `idx in 0..=3` (panics on out-of-range).
//! - `with_ipc_buffer_addr(addr)` — sets `x6`.
//! - `with_syscall_id(id)` — sets `x7`.
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

/// Register index for `x0` — `cap_addr` (capability pointer).
pub const REG_X0: usize = 0;
/// Register index for `x1` — encoded `MessageInfo` bitfield.
pub const REG_X1: usize = 1;
/// Register index for `x2` — `msg_regs[0]` (first inline message register).
pub const REG_X2: usize = 2;
/// Register index for `x3` — `msg_regs[1]`.
pub const REG_X3: usize = 3;
/// Register index for `x4` — `msg_regs[2]`.
pub const REG_X4: usize = 4;
/// Register index for `x5` — `msg_regs[3]` (last inline message register).
pub const REG_X5: usize = 5;
/// Register index for `x6` — IPC-buffer address (read from `TPIDRRO_EL0`
/// on hardware).  Not part of `arm64DefaultLayout` proper; populated
/// by the kernel-side trap handler.
pub const REG_X6: usize = 6;
/// Register index for `x7` — `syscall_id` discriminant.
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
    /// [`MessageInfo::encode`].  Encoding is infallible for any
    /// `MessageInfo` value reachable through the public API —
    /// `MessageInfo::new`, `new_const`, and `decode` all enforce
    /// the bounds (`length ≤ 120`, `extra_caps ≤ 3`,
    /// `label < 2^20`) at construction time, so the `encode()`
    /// `Result` is always `Ok`.
    ///
    /// # Panics
    ///
    /// Panics if `info.encode()` returns `Err`.  This is
    /// unreachable for any `MessageInfo` constructed through the
    /// public API; the explicit panic protects against a future
    /// internal helper that bypasses validation.
    pub fn with_message_info(mut self, info: MessageInfo) -> Self {
        self.registers[REG_X1] = info
            .encode()
            .expect("MessageInfo constructed via the public API always encodes");
        self
    }

    /// Set the capability address (`x0`).
    pub fn with_cap_addr(mut self, addr: CPtr) -> Self {
        self.registers[REG_X0] = addr.raw();
        self
    }

    /// Set a message register.
    ///
    /// `idx` selects one of the four inline `msg_regs[0..=3]` slots
    /// per the `sele4n-abi::SyscallRequest` convention.  The slots
    /// map to ARM64 registers `x2..=x5` per `arm64DefaultLayout`:
    /// `idx 0 → x2`, `idx 1 → x3`, `idx 2 → x4`, `idx 3 → x5`.
    ///
    /// # Panics
    ///
    /// Panics if `idx > 3`.  Out-of-range indices are a programmer
    /// error and cannot be silently accepted without producing a
    /// fixture that diverges from `arm64DefaultLayout`.  The
    /// panic message names the offending index for diagnostics.
    pub fn with_msg_reg(mut self, idx: usize, value: u64) -> Self {
        let reg_idx = match idx {
            0 => REG_X2,
            1 => REG_X3,
            2 => REG_X4,
            3 => REG_X5,
            _ => panic!(
                "with_msg_reg: idx {idx} out of range; arm64DefaultLayout \
                 has exactly 4 inline message registers (idx 0..=3 mapped to x2..=x5)"
            ),
        };
        self.registers[reg_idx] = value;
        self
    }

    /// Set the IPC-buffer address (`x6`).
    ///
    /// The kernel-side trap handler
    /// (`sele4n-hal::svc_dispatch::SyscallArgs::from_trap_frame`)
    /// reads `x6` as the caller's IPC buffer address (set from
    /// `TPIDRRO_EL0` on hardware).  This slot is **not** part of
    /// `arm64DefaultLayout` (which only declares `x0`, `x1`,
    /// `x2..x5`, and `x7`); it lives in the trap-frame layer
    /// above the syscall-register layout.
    ///
    /// A zero value signals "no IPC buffer registered" — the
    /// kernel-side dispatcher converts this to `Option::None`.
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
    /// Per `arm64DefaultLayout` + trap-frame convention:
    /// - `[0]` = `x0` (cap_addr)
    /// - `[1]` = `x1` (encoded message info)
    /// - `[2..=5]` = `x2..=x5` (`msg_regs[0..=3]`, 4 inline message registers)
    /// - `[6]` = `x6` (IPC-buffer address, kernel-side trap-frame field)
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
    #[should_panic(expected = "with_msg_reg: idx 4 out of range")]
    fn with_msg_reg_idx_4_panics() {
        // idx=4 is the first invalid index — arm64DefaultLayout has
        // exactly 4 message registers (idx 0..=3 → x2..=x5).  An
        // attempt to set idx=4 must panic loudly so the caller's
        // mismatched expectation surfaces immediately.
        let _ = FixtureBuilder::new().with_msg_reg(4, 0xFFFF);
    }

    #[test]
    #[should_panic(expected = "with_msg_reg: idx 99 out of range")]
    fn with_msg_reg_large_idx_panics() {
        let _ = FixtureBuilder::new().with_msg_reg(99, 0xFFFF);
    }

    #[test]
    #[should_panic(expected = "out of range")]
    fn with_msg_reg_usize_max_panics() {
        let _ = FixtureBuilder::new().with_msg_reg(usize::MAX, 0xFFFF);
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
