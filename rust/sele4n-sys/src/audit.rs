// SPDX-License-Identifier: GPL-3.0-or-later
//! Declassification audit trail — the privileged reader and drain.
//!
//! Lean: `SeLe4n/Kernel/InformationFlow/AuditRead.lean` — `auditReadFromCore`
//! and `auditDrainVisiblePrefix`, reached through `API.dispatchWithCapChecked`'s
//! `.auditRead` / `.auditDrain` arms.  Added in WS-SM SM9.A.
//!
//! # Why two syscalls
//!
//! Authority is keyed on the `SyscallId`, so splitting read from drain lets a
//! monitoring deployment mint a **read-only** audit capability that provably
//! cannot remove evidence (Lean: `auditTrailRead_cannot_drain`).
//!
//! # What a caller must hold
//!
//! Three gates, and the first is the one that matters:
//!
//! 1. a capability whose **target** is the audit trail — not merely one
//!    carrying the required right.  `syscallLookupCap` never constrains a
//!    capability's target, so a rights-only gate would be reachable by any
//!    thread holding any readable capability, which in practice is every
//!    thread (its own TCB suffices);
//! 2. the right — `read` for the reader, `write` for the drain; and
//! 3. for the drain and for global entry identities, the deployment's
//!    configured audit-monitor clearance.
//!
//! An unconfigured deployment mints no audit capability and names no monitor,
//! so it has no audit reader at all.
//!
//! # The read protocol
//!
//! Every index is an index into the **caller's own filtered view**, never into
//! the global trail, so hidden entries cannot be counted through index gaps.
//! Unbounded fields are read through a 32-bit chunk protocol: ask for the chunk
//! count, then read the chunks, then fold them back little-endian.  Folding
//! recovers the value exactly (Lean: `auditReadField_reconstructs`); a value
//! too wide to export is **refused** with `AuditFieldTooLarge` rather than
//! truncated.

use sele4n_abi::{invoke_syscall, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{CPtr, KernelResult, SyscallId};

/// Number of `audit_read` sub-operation opcodes.  Mirrors Lean's
/// `auditReadOpcodeCount`; a divergence would surface as
/// `InvalidSyscallArgument` on a valid request rather than as a decode bug.
pub const AUDIT_READ_OPCODE_COUNT: u64 = 12;

/// The `audit_read` sub-operations, mirroring Lean's `AuditReadOp`.
///
/// The sub-operation and the record field it selects share the opcode, because
/// `Field` needs three coordinates (view index, field, chunk index) and the
/// field space is four values while the opcode space is free.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u64)]
pub enum AuditReadOpcode {
    /// Visible length, and — for the configured monitor only — the drain
    /// generation.  One call, because a split read of the two components can
    /// assemble a pair that corresponds to no state at all.
    Status = 0,
    /// Chunk count for the entry's source domain.
    SrcDomainChunks = 1,
    /// Chunk count for the entry's destination domain.
    DstDomainChunks = 2,
    /// Chunk count for the entry's target object id.
    TargetObjectChunks = 3,
    /// Chunk count for the entry's timestamp (a view-local index for a partial
    /// reader; the global identity for the configured monitor).
    TimestampChunks = 4,
    /// One chunk of the entry's source domain.
    SrcDomain = 5,
    /// One chunk of the entry's destination domain.
    DstDomain = 6,
    /// One chunk of the entry's target object id.
    TargetObject = 7,
    /// One chunk of the entry's timestamp.
    Timestamp = 8,
    /// The entry's originating core packed with the kernel-issued trust bit.
    CoreAndTrust = 9,
    /// Byte length of the entry's authorization-basis designation.
    BasisByteCount = 10,
    /// One four-byte chunk of the entry's basis designation.
    BasisChunk = 11,
}

impl AuditReadOpcode {
    /// Raw operand value.
    #[inline]
    pub const fn to_u64(self) -> u64 {
        self as u64
    }
}

/// The chunk radix the reader exports numeric fields in — 2^32, so a chunk is
/// a 32-bit payload inside the 64-bit return word.  Mirrors Lean's
/// `auditFieldChunkModulus`.
pub const AUDIT_FIELD_CHUNK_MODULUS: u128 = 1u128 << 32;

/// Maximum number of chunks the reader will export for one numeric field.
/// Mirrors Lean's `maxAuditFieldChunks`; above it the read is **refused**
/// (`AuditFieldTooLarge`) rather than truncated.
pub const MAX_AUDIT_FIELD_CHUNKS: u64 = 4;

/// The status word's low field width, in distinct values.  Mirrors Lean's
/// `auditStatusLengthSlots`; the visible length occupies the low nine bits and
/// the drain generation the rest.
pub const AUDIT_STATUS_LENGTH_SLOTS: u64 = 512;

/// Read one word of the declassification audit trail.
///
/// # Arguments
///
/// * `audit_cap` — a capability whose target is the audit trail, carrying the
///   `read` right.
/// * `opcode` — which sub-operation, and for the field operations which field.
/// * `index` — the entry's index **in the caller's own filtered view**.
/// * `chunk` — the chunk index, for the chunked field and basis operations;
///   ignored otherwise.
///
/// # Errors
///
/// * `InvalidCapability` — the capability does not target the audit trail.
///   This is the gate that makes the reader unreachable by right alone.
/// * `IllegalAuthority` — the capability does not carry `read`.
/// * `IllegalState` — the executing core is running no thread, so there is no
///   subject whose clearance would select a view.
/// * `InvalidArgument` — the index is past the end of the caller's own view, or
///   the chunk index is past the field's width.  An entry the caller cannot see
///   is indistinguishable from one that does not exist.
/// * `InvalidSyscallArgument` — the opcode is not one this ABI defines.
/// * `AuditFieldTooLarge` — the value needs more than `MAX_AUDIT_FIELD_CHUNKS`
///   chunks (or the designation exceeds the exported byte width), so the kernel
///   refused the read rather than returning a truncated value.
#[inline]
pub fn audit_read(
    audit_cap: CPtr,
    opcode: AuditReadOpcode,
    index: u64,
    chunk: u64,
) -> KernelResult<u64> {
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: audit_cap,
        msg_info: MessageInfo::new_const(3, 0, 0),
        msg_regs: [opcode.to_u64(), index, chunk, 0],
        syscall_id: SyscallId::AuditRead,
    })?;
    Ok(resp.value())
}

/// Decode the status word's visible-entry count.
#[inline]
pub const fn audit_status_visible_length(status: u64) -> u64 {
    status % AUDIT_STATUS_LENGTH_SLOTS
}

/// Decode the status word's drain generation.  Always `0` for a caller that is
/// not the configured audit monitor — a partial reader is told nothing about
/// how many entries have been drained, because that count includes entries it
/// cannot see.
#[inline]
pub const fn audit_status_generation(status: u64) -> u64 {
    status / AUDIT_STATUS_LENGTH_SLOTS
}

/// Fold a numeric field's chunks back into its value, little-endian in base
/// 2^32.  Mirrors Lean's `auditFoldChunks`, whose `auditReadField_reconstructs`
/// says the fold recovers the value **exactly** over the domain the reader
/// accepts.
///
/// Returns `None` if more chunks are supplied than the reader can export
/// (beyond that width the value would not have been exported at all), **or**
/// if any chunk is at or above the radix.  The kernel never emits a chunk
/// `>= 2^32` — each is `v / 2^(32i) % 2^32` — so an out-of-radix chunk is
/// malformed input, and refusing it is what keeps the accumulation provably
/// in-range: with every chunk below the radix the folded value is at most
/// `2^128 - 1`, where an unvalidated `u64` chunk at position 3 would overflow
/// `u128` (panic in debug, silent wrap in release — a silently wrong value,
/// which is exactly what this module must never hand a monitor).
pub fn audit_fold_chunks(chunks: &[u64]) -> Option<u128> {
    if chunks.len() as u64 > MAX_AUDIT_FIELD_CHUNKS {
        return None;
    }
    let mut value: u128 = 0;
    for (i, chunk) in chunks.iter().enumerate() {
        if (*chunk as u128) >= AUDIT_FIELD_CHUNK_MODULUS {
            return None;
        }
        value += (*chunk as u128) * AUDIT_FIELD_CHUNK_MODULUS.pow(i as u32);
    }
    Some(value)
}

/// Extract one byte from a basis-designation chunk (`k < 4`), little-endian.
/// Mirrors Lean's `auditBasisByteOfChunk`.
#[inline]
pub const fn audit_basis_byte_of_chunk(chunk: u64, k: u32) -> u8 {
    ((chunk >> (8 * k)) & 0xFF) as u8
}

/// Drain a prefix of the declassification audit trail, returning the new
/// visible length.
///
/// This is what makes the fail-closed 256-entry capacity bound survivable: a
/// deployment that performs that many authorized downgrades without draining
/// stops being able to declassify at all.
///
/// # Arguments
///
/// * `audit_cap` — a capability whose target is the audit trail, carrying the
///   `write` right.
/// * `count` — how many entries to remove.  A count at or above the trail's
///   length clears it, which is the call a monitor recovering from the cliff
///   makes.
///
/// # Errors
///
/// * `InvalidCapability` — the capability does not target the audit trail.
/// * `IllegalAuthority` — the capability does not carry `write`, **or** the
///   caller is not the deployment's configured audit monitor.  An unconfigured
///   deployment gets this on every call: draining is authorized only for a
///   caller that dominates the configured monitor clearance, and the default is
///   to name none.
#[inline]
pub fn audit_drain(audit_cap: CPtr, count: u64) -> KernelResult<u64> {
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: audit_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [count, 0, 0, 0],
        syscall_id: SyscallId::AuditDrain,
    })?;
    Ok(resp.value())
}

/// Drain the whole trail.  Convenience over [`audit_drain`] with a count the
/// trail cannot exceed.
#[inline]
pub fn audit_drain_all(audit_cap: CPtr) -> KernelResult<u64> {
    audit_drain(audit_cap, u64::MAX)
}

/// Raw-response form of [`audit_read`], for callers that want the whole
/// [`SyscallResponse`] rather than just the returned word.
#[inline]
pub fn audit_read_raw(
    audit_cap: CPtr,
    opcode: AuditReadOpcode,
    index: u64,
    chunk: u64,
) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: audit_cap,
        msg_info: MessageInfo::new_const(3, 0, 0),
        msg_regs: [opcode.to_u64(), index, chunk, 0],
        syscall_id: SyscallId::AuditRead,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The opcode table matches the Lean `decodeAuditReadOp` domain.
    #[test]
    fn opcode_values_match_lean() {
        assert_eq!(AuditReadOpcode::Status.to_u64(), 0);
        assert_eq!(AuditReadOpcode::SrcDomainChunks.to_u64(), 1);
        assert_eq!(AuditReadOpcode::DstDomainChunks.to_u64(), 2);
        assert_eq!(AuditReadOpcode::TargetObjectChunks.to_u64(), 3);
        assert_eq!(AuditReadOpcode::TimestampChunks.to_u64(), 4);
        assert_eq!(AuditReadOpcode::SrcDomain.to_u64(), 5);
        assert_eq!(AuditReadOpcode::DstDomain.to_u64(), 6);
        assert_eq!(AuditReadOpcode::TargetObject.to_u64(), 7);
        assert_eq!(AuditReadOpcode::Timestamp.to_u64(), 8);
        assert_eq!(AuditReadOpcode::CoreAndTrust.to_u64(), 9);
        assert_eq!(AuditReadOpcode::BasisByteCount.to_u64(), 10);
        assert_eq!(AuditReadOpcode::BasisChunk.to_u64(), 11);
        // Every opcode is below the count, and the count is the first value the
        // kernel refuses.
        assert_eq!(
            AuditReadOpcode::BasisChunk.to_u64() + 1,
            AUDIT_READ_OPCODE_COUNT
        );
    }

    /// Folding chunks recovers the value — the Rust side of Lean's
    /// `auditReadField_reconstructs`.
    #[test]
    fn fold_chunks_reconstructs() {
        // A value that needs two chunks: 2^32 + 7.
        let value: u128 = (1u128 << 32) + 7;
        let low = (value % AUDIT_FIELD_CHUNK_MODULUS) as u64;
        let high = ((value / AUDIT_FIELD_CHUNK_MODULUS) % AUDIT_FIELD_CHUNK_MODULUS) as u64;
        assert_eq!(audit_fold_chunks(&[low, high]), Some(value));
        // And a single-chunk value.
        assert_eq!(audit_fold_chunks(&[42]), Some(42u128));
        // Empty is zero, matching Lean's `auditFoldChunks 0`.
        assert_eq!(audit_fold_chunks(&[]), Some(0));
    }

    /// The fold refuses more chunks than the reader can export, rather than
    /// silently accepting a width the kernel would have refused.
    #[test]
    fn fold_chunks_refuses_over_width() {
        let too_many = [0u64; (MAX_AUDIT_FIELD_CHUNKS as usize) + 1];
        assert_eq!(audit_fold_chunks(&too_many), None);
    }

    /// The fold refuses an out-of-radix chunk — the SM9.A audit's regression
    /// witness.  The kernel never emits a chunk `>= 2^32`, so such input is
    /// malformed, and before the radix guard the position-3 multiplication
    /// `chunk * 2^96` overflowed `u128` on it: a panic in debug builds, a
    /// silently wrong fold in release — in a monitor's own toolkit.
    #[test]
    fn fold_chunks_refuses_out_of_radix_chunk() {
        // The overflow shape itself: u64::MAX at position 3.
        assert_eq!(audit_fold_chunks(&[0, 0, 0, u64::MAX]), None);
        // The boundary from both sides: 2^32 is refused, 2^32 - 1 folds.
        assert_eq!(audit_fold_chunks(&[1u64 << 32]), None);
        assert_eq!(
            audit_fold_chunks(&[(1u64 << 32) - 1]),
            Some((1u128 << 32) - 1)
        );
        // The maximal well-formed input folds to exactly 2^128 - 1 = u128::MAX
        // — the accumulation stays in range once every chunk is below the
        // radix, and the reader's export bound is tight against it.
        let max_chunk = (1u64 << 32) - 1;
        assert_eq!(
            audit_fold_chunks(&[max_chunk, max_chunk, max_chunk, max_chunk]),
            Some(u128::MAX)
        );
    }

    /// The status word's two components decode independently — the Rust side of
    /// Lean's `auditStatusWord_roundtrip`.
    #[test]
    fn status_word_roundtrip() {
        for &(len, generation) in &[(0u64, 0u64), (1, 0), (256, 7), (511, 1_000_000)] {
            let word = len + generation * AUDIT_STATUS_LENGTH_SLOTS;
            assert_eq!(audit_status_visible_length(word), len);
            assert_eq!(audit_status_generation(word), generation);
        }
    }

    /// Basis-designation bytes extract in the order the kernel packed them.
    #[test]
    fn basis_chunk_byte_extraction() {
        let chunk: u64 = 0x44_33_22_11;
        assert_eq!(audit_basis_byte_of_chunk(chunk, 0), 0x11);
        assert_eq!(audit_basis_byte_of_chunk(chunk, 1), 0x22);
        assert_eq!(audit_basis_byte_of_chunk(chunk, 2), 0x33);
        assert_eq!(audit_basis_byte_of_chunk(chunk, 3), 0x44);
    }

    /// The two audit syscalls carry different required rights, which is what
    /// lets a deployment mint a reader that cannot drain.
    #[test]
    fn read_and_drain_require_different_rights() {
        use sele4n_types::AccessRight;
        assert_eq!(SyscallId::AuditRead.required_right(), AccessRight::Read);
        assert_eq!(SyscallId::AuditDrain.required_right(), AccessRight::Write);
    }
}
