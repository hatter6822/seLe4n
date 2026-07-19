// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-SM SM7.A.3**: per-core TLB-shootdown acknowledgment flags.
//!
//! The runtime realisation of the Lean model's
//! `TlbShootdownState.shootdownAck : Vector Bool numCores`
//! (`SeLe4n/Kernel/Architecture/TlbShootdown.lean`).  One
//! cache-line-aligned [`AtomicBool`] per core, polled by the shootdown
//! initiator and set by each target's `.tlbShootdownReq` SGI handler
//! (INTID 1; see the SGI reservation table in [`crate::gic`]).
//!
//! ## Protocol role (SMP_TLB_SHOOTDOWN_PLAN.md §3.2, §4.2)
//!
//! A shootdown round for `(asid, vaddr)` initiated by core `c₀`:
//!
//! 1. `c₀` calls [`reset_for_round`]`(c₀)` — every **online** core's
//!    flag drops to `false` except `c₀`'s own (the initiator
//!    invalidates locally and is never waited on).  Offline cores stay
//!    born-acknowledged — they can never take the SGI, and they come
//!    online with an empty TLB (`tlbi vmalle1` in
//!    [`crate::mmu::init_mmu_secondary`]) — see
//!    [`reset_for_round_in_slice_masked`] (PR #838 review P1).
//! 2. `c₀` posts one descriptor per target into the Lean-side pending
//!    queues, then fires a `.tlbShootdownReq` SGI per target.
//!    [`crate::gic::send_sgi`] emits `dsb ish` **before** the GICD_SGIR
//!    write (SM1.F.8), so the flag clears from step 1 — and the queue
//!    writes — are globally observable before any target can take the
//!    interrupt.
//! 3. Each target's handler drains its queue, executes one local TLBI
//!    per descriptor, retires them (`dsb`), and only then calls
//!    [`ack_set`] — a **release**-store.
//! 4. `c₀` polls [`all_acked`] (**acquire**-loads, WFE-paced at
//!    SM7.B.5).  The release-acquire pairing guarantees that when `c₀`
//!    observes a target's `true`, that target's TLBI completion
//!    happens-before the observation — the synchronisation edge
//!    Theorem 3.3.1's remote-core case rests on (formalised against
//!    the SM2.A memory model at SM7.B.4, `shootdownAck_release_acquire`).
//!
//! ## Why `Relaxed` suffices for the round reset
//!
//! [`reset_for_round`]'s stores are `Relaxed` because both consumers
//! are already ordered by stronger mechanisms:
//!
//! * **Targets** never load their own flag — the clear only has to be
//!   visible before the target's handler *sets* the flag, and the
//!   `dsb ish` inside [`crate::gic::send_sgi`] orders the clear before
//!   the SGI that triggers the handler (ARM ARM B2.7: DSB completes
//!   all prior accesses before the SGIR write is issued).
//! * **The initiator's own poll** observes its prior store by
//!   same-location program-order coherence.
//!
//! Cross-round interference is excluded structurally by the **global
//! shootdown-round lock** (`ShootdownRoundLockId` on the Lean side; an
//! SM7.B.7 obligation registered by the SM7.A audit): rounds must be
//! serialised system-wide because [`SHOOTDOWN_ACK`] carries no round
//! identity.  The per-VSpace VSpaceRoot lock of the plan's §3.2
//! precondition is NOT sufficient — two initiators shooting down
//! different VSpaces hold different VSpaceRoot locks, and an
//! interleaved `reset_for_round` would (a) mark the second initiator's
//! own flag `true` while the first still waits on that core (early
//! `all_acked` exit with a stale TLB entry live — the SMP-C4 hazard)
//! and (b) clear the first initiator's born-`true` flag (a mutual hang
//! if it polls with IRQs masked).  Under the round lock, a new round's
//! reset happens-after every previous-round ack-set (the previous
//! initiator only released the round lock after its acquire-poll
//! observed every ack, which synchronises-with each release-set), so a
//! straggling handler from round *N* cannot overwrite round *N+1*'s
//! reset.
//!
//! ## Boot state
//!
//! All flags boot `true` — the quiescent "no round in flight, nobody
//! waited on" state, matching the Lean model's
//! `TlbShootdownState.initial` (`initial_ackOnCore`) so the very first
//! [`all_acked`] poll before any round would trivially succeed rather
//! than deadlock.
//!
//! ## Layout
//!
//! Each flag owns a full 64-byte cache line ([`ShootdownAckFlag`],
//! `repr(C, align(64))`) so a target's release-store does not
//! ping-pong the line under the initiator's poll of *other* targets'
//! flags — the same false-sharing discipline as
//! [`crate::per_cpu_stats::PerCpuStats`] and [`crate::per_cpu::PerCpuData`].
//!
//! ## Host (non-aarch64) behaviour
//!
//! Everything here is portable atomics — every entry point compiles
//! and executes identically under host `cargo test`.  Unit tests
//! mutate stack-local slices via the `_in_slice` inner forms (the
//! global [`SHOOTDOWN_ACK`] is only read, so parallel test threads
//! never race on it).
//!
//! ## Lean ↔ Rust conformance pairing
//!
//! Each Lean SM7.A ack-flag theorem
//! (`SeLe4n/Kernel/Architecture/TlbShootdown.lean`) has a Rust unit
//! test below exercising the same fact on this realisation, so the
//! two sides are auditable claim-by-claim (the FFI seam itself is
//! `ffi_shootdown_*` in `ffi.rs`, called through the typed `CoreId`
//! wrappers in `SeLe4n/Kernel/Concurrency/Runtime.lean`):
//!
//! | Lean theorem | Rust test |
//! |--------------|-----------|
//! | `initial_ackOnCore` / `initial_allAcked` | `sm7a3_shootdown_ack_boots_quiescent_all_acknowledged` |
//! | `beginShootdownRound_ackOnCore_iff` | `sm7a3_reset_for_round_marks_only_initiator_acknowledged`, `sm7a3_reset_for_round_works_for_every_initiator` |
//! | `acknowledgeShootdown_ackOnCore_self` + `_ne` | `sm7a3_ack_set_marks_exactly_the_named_core` |
//! | `acknowledgeShootdown_monotone` (idempotence) | `sm7a3_ack_set_is_idempotent` |
//! | `allAcked` (∀-core conjunction, all 2⁴ states) | `sm7a3_all_acked_matches_conjunction_exhaustively` |
//! | `allCores_foldl_acknowledgeShootdown_allAcked` | `sm7a3_full_round_trip_reaches_all_acked` |
//! | round reset after `shootdownRound_restores_quiescent` | `sm7a3_back_to_back_rounds_reset_cleanly` |
//! | fail-closed bounds (`CoreId` typing on the Lean side) | `sm7a3_*_panics_on_out_of_range_*` + the `ffi.rs` panic tests |
//! | `TlbInvalidation.toOpTag` decode (SM7.B debt (1)) | `sm7b_op_tag_decode_conformance` |
//! | `handleTlbShootdownReqOnCore` per-descriptor effect | `sm7b_retire_per_descriptor_counts_operands`, `sm7b_mailbox_publish_snapshot_roundtrip` |
//! | coalescing / fail-safe fallback (`collapseShootdownOps`) | `sm7b_mailbox_overflow_collapses_to_vmalle1`, `sm7b_retire_torn_read_falls_back_to_full_flush` |

use core::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering};

use crate::smp::MAX_SECONDARY_CORES;

/// **WS-SM SM7.A.3**: one core's shootdown-acknowledgment flag,
/// padded to a full cache line (64 bytes on Cortex-A76) to eliminate
/// false sharing between the per-core flags.
///
/// The explicit `_reserved` tail keeps every byte of the slot
/// deterministically initialised (no padding-byte hazards) and pins
/// the size independently of the alignment attribute.
#[repr(C, align(64))]
pub struct ShootdownAckFlag {
    /// `true` once this core has completed (and locally retired) every
    /// invalidation of the current shootdown round.  Set with
    /// `Ordering::Release` by the owning core's SGI handler; polled
    /// with `Ordering::Acquire` by the round initiator.
    pub acked: AtomicBool,
    /// Padding to a full cache line; reserved for SM7.B+ additions
    /// (e.g., a per-core drained-descriptor diagnostic counter).
    _reserved: [u8; 63],
}

impl ShootdownAckFlag {
    /// **WS-SM SM7.A.3**: const constructor with an explicit initial
    /// value.  `const fn` because [`SHOOTDOWN_ACK`] is a `static`.
    #[inline]
    pub const fn new(initial: bool) -> Self {
        Self {
            acked: AtomicBool::new(initial),
            _reserved: [0; 63],
        }
    }

    /// **WS-SM SM7.A.3**: the boot value — acknowledged (`true`),
    /// i.e. quiescent: no shootdown round is in flight, so nobody is
    /// waited on.  Matches the Lean `TlbShootdownState.initial`
    /// (`initial_ackOnCore = true`).
    #[inline]
    pub const fn acked_at_boot() -> Self {
        Self::new(true)
    }
}

/// **WS-SM SM7.A.3**: the per-core shootdown-acknowledgment flags,
/// one cache-line-aligned slot per core, indexed by `core_id`
/// (0..=`MAX_SECONDARY_CORES`).  All slots boot `true` (quiescent).
///
/// `#[no_mangle]` + `#[used]` preserve the symbol so a hardware-side
/// debug probe can resolve it via the linker map, mirroring
/// [`crate::per_cpu_stats::PER_CPU_STATS`].
#[no_mangle]
#[used]
pub static SHOOTDOWN_ACK: [ShootdownAckFlag; MAX_SECONDARY_CORES + 1] = [
    ShootdownAckFlag::acked_at_boot(),
    ShootdownAckFlag::acked_at_boot(),
    ShootdownAckFlag::acked_at_boot(),
    ShootdownAckFlag::acked_at_boot(),
];

// Compile-time pin: each flag owns exactly one cache line.  Growing the
// struct past 64 bytes (e.g. adding a field without shrinking the
// `_reserved` tail) fails the build here with a clear diagnostic.
const _: () = assert!(
    core::mem::size_of::<ShootdownAckFlag>() == 64,
    "WS-SM SM7.A.3: ShootdownAckFlag must be one cache line (64 bytes); \
     shrink the `_reserved` tail when adding a field to stay within budget"
);

// Compile-time pin: cache-line aligned to avoid false sharing between
// adjacent cores' flags.
const _: () = assert!(
    core::mem::align_of::<ShootdownAckFlag>() == 64,
    "WS-SM SM7.A.3: ShootdownAckFlag must be 64-byte aligned to avoid \
     false sharing"
);

// ============================================================================
// Inner forms — testable variants taking explicit slice references
// ============================================================================
//
// The production accessors below operate on the global [`SHOOTDOWN_ACK`]
// array.  Host unit tests exercise cross-core round lifecycles on
// stack-local arrays through these `_in_slice` forms so parallel test
// threads never mutate shared state; the production wrappers delegate
// here so the tested logic and the shipped logic are the same code.

/// **WS-SM SM7.A.3** (testable inner form): release-set one core's
/// acknowledgment flag in an explicit slice.
///
/// Out-of-range `core_id` is a protocol violation and panics
/// (fail-closed): silently ignoring the set would leave the initiator
/// waiting forever; aliasing to another slot would falsely acknowledge
/// a core whose TLB may still hold the stale entry — the exact SMP-C4
/// hazard SM7 exists to close.  Callers routed from the Lean side pass
/// a `CoreId = Fin numCores`, so the panic arm is structurally
/// unreachable from well-typed kernel code.
#[inline]
pub fn ack_set_in_slice(slots: &[ShootdownAckFlag], core_id: usize) {
    assert!(
        core_id < slots.len(),
        "WS-SM SM7.A.3: ack_set_in_slice: core_id {} out of range (expected < {})",
        core_id,
        slots.len()
    );
    slots[core_id].acked.store(true, Ordering::Release);
}

/// **WS-SM SM7.A.3** (testable inner form): acquire-load one core's
/// acknowledgment flag from an explicit slice.
///
/// Panics on out-of-range `core_id` (fail-closed; see
/// [`ack_set_in_slice`]).
#[inline]
pub fn ack_is_set_in_slice(slots: &[ShootdownAckFlag], core_id: usize) -> bool {
    assert!(
        core_id < slots.len(),
        "WS-SM SM7.A.3: ack_is_set_in_slice: core_id {} out of range (expected < {})",
        core_id,
        slots.len()
    );
    slots[core_id].acked.load(Ordering::Acquire)
}

/// **WS-SM SM7.A.3** (testable inner form): open a new shootdown round
/// in an explicit slice — every flag drops to `false` except the
/// initiator's own, which is born-`true` (the initiator invalidates
/// locally and is never waited on).  Mirrors the Lean
/// `beginShootdownRound` exactly (`beginShootdownRound_ackOnCore_iff`)
/// — the fully-online configuration; partial-core boots go through
/// [`reset_for_round_in_slice_masked`].
///
/// Stores are `Relaxed`; see the module docs for why the `dsb ish`
/// inside [`crate::gic::send_sgi`] (SM1.F.8) plus same-location
/// coherence make that sufficient.  Panics on out-of-range `initiator`
/// (fail-closed).
#[inline]
pub fn reset_for_round_in_slice(slots: &[ShootdownAckFlag], initiator: usize) {
    assert!(
        initiator < slots.len(),
        "WS-SM SM7.A.3: reset_for_round_in_slice: initiator {} out of range (expected < {})",
        initiator,
        slots.len()
    );
    for (i, slot) in slots.iter().enumerate() {
        slot.acked.store(i == initiator, Ordering::Relaxed);
    }
}

/// **WS-SM SM7.A.3** (testable inner form; PR #838 review P1): open a
/// new shootdown round with an explicit **online mask** — a flag drops
/// to `false` only when its core is online and not the initiator;
/// offline cores stay **born-acknowledged**.
///
/// Rationale (liveness): in a partial-core boot (`smp_enabled=false` —
/// the v1.0.0 default — an `smp_max_cores` cap, or a PSCI CPU_ON
/// rejection leaving only a prefix of secondaries online), an offline
/// core can never receive the `.tlbShootdownReq` SGI and call
/// [`ack_set`]; clearing its flag would make [`all_acked`] permanently
/// unreachable and hang the initiator's wait loop.
///
/// Rationale (safety): an offline core holds no stale translations —
/// every secondary bring-up path runs `tlbi vmalle1` + DSB + ISB
/// before enabling its MMU ([`crate::mmu::init_mmu_secondary`]), so a
/// core that comes online *after* a round it was excluded from starts
/// with an empty TLB.  SM7.B's target-set computation must likewise
/// target online cores only, and rounds must not race core bring-up
/// (bring-up completes during boot, before any user mapping exists to
/// shoot down).
///
/// Mirrors the Lean `beginShootdownRoundFor` (targets = the online
/// non-initiator cores; `beginShootdownRoundFor_ackOnCore_iff`).
/// Panics on out-of-range `initiator` or a mask/slot length mismatch
/// (fail-closed).
#[inline]
pub fn reset_for_round_in_slice_masked(
    slots: &[ShootdownAckFlag],
    initiator: usize,
    online: &[bool],
) {
    assert!(
        initiator < slots.len(),
        "WS-SM SM7.A.3: reset_for_round_in_slice_masked: initiator {} out of range (expected < {})",
        initiator,
        slots.len()
    );
    assert!(
        online.len() == slots.len(),
        "WS-SM SM7.A.3: reset_for_round_in_slice_masked: online mask length {} != slot count {}",
        online.len(),
        slots.len()
    );
    for (i, slot) in slots.iter().enumerate() {
        slot.acked
            .store(i == initiator || !online[i], Ordering::Relaxed);
    }
}

/// **WS-SM SM7.A.3** (testable inner form): acquire-poll every flag in
/// an explicit slice — the initiator wait-loop's exit condition
/// (plan §3.2 step 5).  Mirrors the Lean `allAcked` predicate.
#[inline]
pub fn all_acked_in_slice(slots: &[ShootdownAckFlag]) -> bool {
    slots.iter().all(|s| s.acked.load(Ordering::Acquire))
}

// ============================================================================
// Production accessors over the global SHOOTDOWN_ACK array
// ============================================================================

/// **WS-SM SM7.A.3**: release-set the given core's acknowledgment flag
/// in [`SHOOTDOWN_ACK`].
///
/// Called by a target core's `.tlbShootdownReq` SGI handler (SM7.B.3)
/// only *after* its drained invalidations have retired locally — the
/// release edge of the SM7.B.4 release-acquire pairing.  Panics on
/// out-of-range `core_id` (fail-closed; see [`ack_set_in_slice`]).
#[inline]
pub fn ack_set(core_id: usize) {
    ack_set_in_slice(&SHOOTDOWN_ACK, core_id);
}

/// **WS-SM SM7.A.3**: acquire-load the given core's acknowledgment
/// flag from [`SHOOTDOWN_ACK`].  Panics on out-of-range `core_id`
/// (fail-closed).
#[inline]
pub fn ack_is_set(core_id: usize) -> bool {
    ack_is_set_in_slice(&SHOOTDOWN_ACK, core_id)
}

/// **WS-SM SM7.A.3**: open a new shootdown round in [`SHOOTDOWN_ACK`]
/// — the runtime realisation of the Lean `beginShootdownRound` /
/// `beginShootdownRoundFor` (plan §3.2 step 1).  Must only be called
/// by the round initiator under the global shootdown-round lock (the
/// module-header round-serialisation contract; SM7.B.7 — the
/// per-VSpace VSpaceRoot lock alone is NOT sufficient); panics on
/// out-of-range `initiator` (fail-closed).
///
/// **Offline / not-IRQ-ready cores stay born-acknowledged** (PR #838
/// review P1 + PR #839 review P1): the online set is read from
/// [`crate::smp::CORE_IRQ_READY`] — the *IRQ-serviceable* flag a
/// secondary sets **itself** after `enable_irq`, NOT the primary's
/// [`crate::smp::CORE_READY`] release handshake — so a partial-core
/// boot (`smp_enabled=false`, an `smp_max_cores` cap, a PSCI rejection),
/// a secondary still mid-bring-up, or one wedged in the timer-init-
/// failure halt loop cannot hang the initiator's [`all_acked`] wait on
/// a core that can never take the SGI.  Safety of excluding such a core
/// (it holds no invalidatable TLB entry): see
/// [`crate::smp::CORE_IRQ_READY`].  The SM7.B target-set obligation:
/// see [`reset_for_round_in_slice_masked`].
#[inline]
pub fn reset_for_round(initiator: usize) {
    reset_for_round_in_slice_masked(&SHOOTDOWN_ACK, initiator, &irq_ready_online());
}

/// **WS-SM SM7.B (PR #839 review P1)**: snapshot the per-core
/// IRQ-serviceable set from [`crate::smp::CORE_IRQ_READY`] (Acquire),
/// the single source of truth for both the round reset mask
/// ([`reset_for_round`]) and the SGI target mask ([`online_mask`]).
/// One read of each slot; the caller takes a stable snapshot per round
/// (the SM7.A P1 contract forbids a round concurrent with bring-up, so
/// the set does not move underfoot within a round).
#[inline]
fn irq_ready_online() -> [bool; MAX_SECONDARY_CORES + 1] {
    [
        crate::smp::CORE_IRQ_READY[0].load(Ordering::Acquire),
        crate::smp::CORE_IRQ_READY[1].load(Ordering::Acquire),
        crate::smp::CORE_IRQ_READY[2].load(Ordering::Acquire),
        crate::smp::CORE_IRQ_READY[3].load(Ordering::Acquire),
    ]
}

/// **WS-SM SM7.A.3**: acquire-poll every flag in [`SHOOTDOWN_ACK`] —
/// the initiator wait-loop's exit condition (plan §3.2 step 5;
/// WFE-paced by SM7.B.5's bounded wait).
#[inline]
pub fn all_acked() -> bool {
    all_acked_in_slice(&SHOOTDOWN_ACK)
}

// ============================================================================
// Tests
// ============================================================================

// ============================================================================
// WS-SM SM7.B.7 — THE global shootdown-round lock
// ============================================================================

/// **WS-SM SM7.B.7**: THE single global shootdown-round lock — the
/// runtime realisation of the Lean `ShootdownRoundLockId` (fieldless,
/// provably unique).  `false` = free, `true` = a round is in flight.
///
/// **Contract (the SM7.A audit's round-serialisation obligation)**: the
/// ack flags above carry NO round identity, so at most one shootdown
/// round may be in flight system-wide.  An initiator MUST hold this
/// lock across the entire hardware round — [`reset_for_round`], the
/// `.tlbShootdownReq` SGI fires, its local broadcast TLBI, and the
/// [`wait_all_acked_bounded`] poll — and release it only after
/// observing `all_acked` (or immediately before the timeout path's
/// fail-closed panic).  Interleaved rounds on the shared flag vector
/// would permit an early `all_acked` exit with a stale TLB entry live
/// on a target (the SMP-C4 hazard) plus a mutual-hang mode — see the
/// Lean module header (`TlbShootdown.lean`, "Round serialisation
/// contract").
///
/// **Why a CAS try-lock and not the verified `TicketLock`**: a waiter
/// spinning for this lock is (with IRQs masked in the SVC path) unable
/// to take the holder's `.tlbShootdownReq` SGI — yet the holder's
/// round WAITS on that waiter's acknowledgment.  A blind spin would
/// therefore deadlock into the wait-timeout panic (holder waits on
/// waiter's ack; waiter waits on holder's release).  The acquire loop
/// must interleave lock attempts with **servicing the waiter's own
/// pending obligation** (its ack flag is down ⇒ some in-flight round
/// targets it ⇒ invalidate locally, `ack_set`, retry) — which needs
/// try-acquire semantics a ticket lock cannot provide (taking a ticket
/// commits to the queue).  The Lean seam's cooperative loop
/// (`SyscallDispatchEntry.completeShootdownRounds`) is the sole
/// acquirer.  Fairness is not load-bearing: rounds are rare
/// (unmap-family syscalls only) and sub-microsecond.
pub static SHOOTDOWN_ROUND_LOCK: AtomicBool = AtomicBool::new(false);

/// **WS-SM SM7.B.7** (testable inner form): the round-lock CAS over an
/// explicit lock cell — `compare_exchange(false, true, Acquire,
/// Relaxed)`.  The pure state machine is the Lean
/// `roundLockTryAcquire` (`TlbShootdownWait.lean`: success iff free,
/// held afterwards either way, two consecutive attempts never both
/// succeed); the multithreaded exclusivity stress
/// (`sm7b7_round_lock_mutex_stress`) exercises this form on a local
/// cell so it can hammer the CAS without perturbing the global lock
/// other tests observe.
#[inline]
pub fn round_lock_try_acquire_in(lock: &AtomicBool) -> bool {
    lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
        .is_ok()
}

/// **WS-SM SM7.B.7** (testable inner form): the release store over an
/// explicit lock cell (Release ordering).
#[inline]
pub fn round_lock_release_in(lock: &AtomicBool) {
    lock.store(false, Ordering::Release);
}

/// **WS-SM SM7.B.7**: try to acquire the global round lock.  `true` =
/// acquired (Acquire ordering — the previous round's writes, including
/// its final flag state, are visible).  Never blocks.
pub fn round_lock_try_acquire() -> bool {
    round_lock_try_acquire_in(&SHOOTDOWN_ROUND_LOCK)
}

/// **WS-SM SM7.B.7**: release the global round lock (Release ordering —
/// publishes the completed round's writes to the next acquirer).
pub fn round_lock_release() {
    round_lock_release_in(&SHOOTDOWN_ROUND_LOCK)
}

// ============================================================================
// WS-SM SM7.B (debt (1)) — Per-descriptor operand mailbox
// ============================================================================
//
// The `.tlbShootdownReq` handler retires the round's EXACT operands
// locally (one `tlbi` per descriptor) instead of a blanket
// `tlbi vmalle1`, matching the Lean model's per-descriptor
// `applyTlbInvalidations` (`handleTlbShootdownReqOnCore`).  The initiator
// publishes the round's collapsed operands here — under the global round
// lock, BEFORE it fires the `.tlbShootdownReq` SGIs — and the `dsb ish`
// inside `gic::send_sgi` (SM1.F.8) orders the publish before any target
// can take the interrupt, so a target reads a fully-written snapshot.
//
// **Fail-safe by construction.**  A seqlock guards against a torn read
// (a spurious/duplicate SGI arriving while a *later* serialised round is
// mid-publish): the reader that observes instability — or an operand it
// cannot decode, or a published length above capacity — falls back to the
// conservative local `tlbi vmalle1`.  Over-invalidation is always safe
// (an absent entry re-walks the page tables); the ONLY hazard is
// UNDER-invalidation, and the fallback can never under-invalidate.  A
// stale but *consistent* snapshot (a spurious SGI after the round closed)
// re-flushes already-retired operands — a harmless no-op.

/// **WS-SM SM7.B**: operand-mailbox capacity.  A round posting more than
/// this many distinct operands collapses to a single `vmalle1` both at
/// the Lean `collapseShootdownOps` layer and here (defense in depth), so
/// the mailbox never overflows on a well-formed round.
pub const SHOOTDOWN_OP_CAPACITY: usize = 8;

/// **WS-SM SM7.B**: one published invalidation operand — the runtime
/// mirror of a Lean `Architecture.TlbInvalidation`.  `op_tag` matches
/// `TlbInvalidation.toOpTag` (0=Vmalle1, 1=Vae1, 2=Aside1, 3=Vale1);
/// unused fields are `0` (as `toAsid`/`toVaddr` return for them).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ShootdownOp {
    pub op_tag: u32,
    pub asid: u16,
    pub vaddr: u64,
}

impl ShootdownOp {
    /// The conservative full-flush operand — the fallback and the
    /// coalesced-round sentinel.
    pub const VMALLE1: ShootdownOp = ShootdownOp {
        op_tag: 0,
        asid: 0,
        vaddr: 0,
    };
}

/// **WS-SM SM7.B**: the round's operand mailbox — a seqlock-guarded
/// fixed array.  Single writer (the round initiator, under the round
/// lock); many readers (the target handlers).
pub struct ShootdownOpMailbox {
    /// Seqlock sequence: even = stable, odd = mid-publish.
    seq: AtomicU32,
    /// Number of valid operands (`≤ SHOOTDOWN_OP_CAPACITY`).
    len: AtomicUsize,
    /// Packed `(op_tag << 32) | asid` per slot.
    meta: [AtomicU64; SHOOTDOWN_OP_CAPACITY],
    /// The `vaddr` operand per slot.
    vaddr: [AtomicU64; SHOOTDOWN_OP_CAPACITY],
}

impl ShootdownOpMailbox {
    /// A quiescent (empty) mailbox — boots with `len = 0`, so a read
    /// before any round yields the empty operand list ⇒ the handler
    /// falls back to `vmalle1` (safe).
    pub const fn new() -> Self {
        ShootdownOpMailbox {
            seq: AtomicU32::new(0),
            len: AtomicUsize::new(0),
            meta: [const { AtomicU64::new(0) }; SHOOTDOWN_OP_CAPACITY],
            vaddr: [const { AtomicU64::new(0) }; SHOOTDOWN_OP_CAPACITY],
        }
    }
}

impl Default for ShootdownOpMailbox {
    fn default() -> Self {
        Self::new()
    }
}

/// **WS-SM SM7.B**: the global operand mailbox published by the live
/// `completeShootdownRounds` seam.
#[no_mangle]
#[used]
pub static SHOOTDOWN_OPS: ShootdownOpMailbox = ShootdownOpMailbox::new();

/// **WS-SM SM7.B** (testable inner form): begin a publish — bump the
/// seqlock to odd (writers-in-progress).  Relaxed here; the closing
/// `publish_commit_in` Release publishes every interior write.
pub fn publish_begin_in(mb: &ShootdownOpMailbox) {
    let s = mb.seq.load(Ordering::Relaxed);
    mb.seq.store(s.wrapping_add(1), Ordering::Relaxed);
    core::sync::atomic::fence(Ordering::Release);
}

/// **WS-SM SM7.B** (testable inner form): write one operand at an
/// explicit slot index (the initiator loops over the round's collapsed
/// operands, supplying the index).  Out-of-range indices are dropped —
/// the matching `publish_commit_in` collapses an over-length round to a
/// single `vmalle1`, so no operand is ever silently lost.
pub fn publish_slot_in(mb: &ShootdownOpMailbox, index: usize, op: ShootdownOp) {
    if index < SHOOTDOWN_OP_CAPACITY {
        mb.meta[index].store(
            ((op.op_tag as u64) << 32) | (op.asid as u64),
            Ordering::Relaxed,
        );
        mb.vaddr[index].store(op.vaddr, Ordering::Relaxed);
    }
}

/// **WS-SM SM7.B** (testable inner form): commit a publish of `len`
/// operands — bump the seqlock to even (stable) with Release ordering.
/// A `len` above capacity collapses to a single `vmalle1` (matching the
/// Lean `collapseShootdownOps` / `enqueueShootdownOrCoalesce` escape);
/// `len == 0` leaves the mailbox empty so the handler falls back to
/// `vmalle1` (safe).
pub fn publish_commit_in(mb: &ShootdownOpMailbox, len: usize) {
    if len > SHOOTDOWN_OP_CAPACITY {
        mb.meta[0].store(0, Ordering::Relaxed); // vmalle1
        mb.vaddr[0].store(0, Ordering::Relaxed);
        mb.len.store(1, Ordering::Relaxed);
    } else {
        mb.len.store(len, Ordering::Relaxed);
    }
    // The begin bumped to odd; +1 restores even (stable), Release so a
    // reader's Acquire load observes all interior writes.
    let cur = mb.seq.load(Ordering::Relaxed);
    mb.seq.store(cur.wrapping_add(1), Ordering::Release);
}

/// **WS-SM SM7.B** (testable batch helper): publish a whole operand slice
/// under the seqlock discipline.  A slice longer than capacity collapses
/// to one `vmalle1`.
pub fn publish_round_ops_in(mb: &ShootdownOpMailbox, ops: &[ShootdownOp]) {
    publish_begin_in(mb);
    let n = ops.len();
    if n <= SHOOTDOWN_OP_CAPACITY {
        for (i, op) in ops.iter().enumerate() {
            publish_slot_in(mb, i, *op);
        }
    }
    publish_commit_in(mb, n);
}

/// **WS-SM SM7.B**: publish into the global mailbox.
pub fn publish_round_ops(ops: &[ShootdownOp]) {
    publish_round_ops_in(&SHOOTDOWN_OPS, ops);
}

/// **WS-SM SM7.B** (testable inner form): read a stable snapshot of an
/// explicit mailbox.  Returns `None` on a torn read (the seqlock was odd,
/// or the sequence advanced mid-read) or a length above capacity — the
/// caller must then fall back to the conservative `tlbi vmalle1`.
pub fn snapshot_round_ops_in(mb: &ShootdownOpMailbox) -> Option<([ShootdownOp; SHOOTDOWN_OP_CAPACITY], usize)> {
    let s1 = mb.seq.load(Ordering::Acquire);
    if s1 & 1 != 0 {
        return None; // a publish is in progress
    }
    let len = mb.len.load(Ordering::Relaxed);
    if len > SHOOTDOWN_OP_CAPACITY {
        return None; // impossible on a well-formed publish → fail safe
    }
    let mut out = [ShootdownOp::VMALLE1; SHOOTDOWN_OP_CAPACITY];
    for (i, slot) in out.iter_mut().enumerate().take(len) {
        let meta = mb.meta[i].load(Ordering::Relaxed);
        let vaddr = mb.vaddr[i].load(Ordering::Relaxed);
        *slot = ShootdownOp {
            op_tag: (meta >> 32) as u32,
            asid: (meta & 0xFFFF) as u16,
            vaddr,
        };
    }
    core::sync::atomic::fence(Ordering::Acquire);
    let s2 = mb.seq.load(Ordering::Relaxed);
    if s1 == s2 {
        Some((out, len))
    } else {
        None // the sequence moved under us → torn read
    }
}

/// **WS-SM SM7.B**: retire the published round operands on the LOCAL PE
/// (one `tlbi` per descriptor), from an explicit mailbox.  Returns the
/// number of per-descriptor invalidations issued, or `None` if it fell
/// back to a single conservative `tlbi vmalle1` (torn read, empty round,
/// or an undecodable operand).  Testable inner form of the handler's
/// TLB-effect step.
pub fn retire_round_ops_in(mb: &ShootdownOpMailbox) -> Option<usize> {
    match snapshot_round_ops_in(mb) {
        Some((ops, len)) if len > 0 => {
            for op in ops.iter().take(len) {
                match crate::tlb::decode_tlb_invalidation(op.op_tag, op.asid, op.vaddr) {
                    Some(decoded) => crate::tlb::tlbi_local(decoded),
                    None => {
                        // An operand we cannot decode → fail safe.
                        crate::tlb::tlbi_vmalle1();
                        return None;
                    }
                }
            }
            Some(len)
        }
        // Empty round or torn read → conservative local full flush.
        _ => {
            crate::tlb::tlbi_vmalle1();
            None
        }
    }
}

// ============================================================================
// WS-SM SM7.B.5 + B.6 — Bounded all-acked wait
// ============================================================================

/// **WS-SM SM7.B.5 (testable inner form)**: bounded poll for
/// all-acknowledged over an explicit flag slice, with an injected
/// monotonic clock.
///
/// Spins (with [`core::hint::spin_loop`]) re-checking
/// [`all_acked_in_slice`] until it holds or `timeout_ticks` have
/// elapsed on `now`.  Returns `true` on observed all-acked, `false`
/// on timeout — the exact verdict semantics the Lean
/// `shootdown_timeout_handling` certifies (a `false` can only be a
/// genuine timeout; a completed round always yields `true`).
///
/// **Why a spin rather than `wfe`**: the plan §3.2 sketch paces the
/// wait with `wfe_bounded`, but a bare `wfe` blocks until an event or
/// interrupt — with IRQs masked in the SVC path and no architectural
/// guarantee that a remote `stlr` generates an event, a hung target
/// would leave the initiator asleep FOREVER, making the timeout (and
/// its diagnosable fail-closed panic) unreachable.  A counted spin is
/// strictly more robust: the round completes in < 1 µs on the 4-core
/// BCM2712 (plan §3.4), so the loop is short-lived, and the 10 ms
/// budget stays enforceable.  (The targets' handlers still emit `sev`
/// after their release-store — free, and it keeps any future
/// event-paced waiter honest.)
pub fn wait_all_acked_bounded_in<C: FnMut() -> u64>(
    slots: &[ShootdownAckFlag],
    timeout_ticks: u64,
    mut now: C,
) -> bool {
    let start = now();
    loop {
        if all_acked_in_slice(slots) {
            return true;
        }
        if now().saturating_sub(start) >= timeout_ticks {
            // One final check: the acks may have landed between the
            // last poll and the deadline read (verdict exactness —
            // never report a timeout on a completed round).
            return all_acked_in_slice(slots);
        }
        core::hint::spin_loop();
    }
}

/// **WS-SM SM7.B.5 + B.6**: bounded poll for all-acknowledged over the
/// production flags, clocked by the generic timer (`CNTPCT_EL0`).
/// `true` = all acked; `false` = timeout (the caller's fail-closed
/// panic trigger — a silently skipped invalidation would be the
/// SMP-C4 stale-TLB hazard).
pub fn wait_all_acked_bounded(timeout_ticks: u64) -> bool {
    wait_all_acked_bounded_in(&SHOOTDOWN_ACK, timeout_ticks, crate::timer::read_counter)
}

// ============================================================================
// WS-SM SM7.B.3 — The .tlbShootdownReq SGI handler
// ============================================================================

/// **WS-SM SM7.B.3**: the `.tlbShootdownReq` INTID (GIC-400 SGI 1) —
/// pinned to the Lean `SgiKind.tlbShootdownReq_intid` (= 1) and the
/// [`crate::gic`] reservation table; conformance-tested below.
pub const TLB_SHOOTDOWN_REQ_INTID: u8 = 1;

/// **WS-SM SM7.B.3**: the `.tlbShootdownReq` SGI handler — the target
/// core's side of the shootdown round (plan §3.2 step 4).
///
/// Sequence on the interrupted core:
///
/// 1. **Invalidate the local TLB — completely** (`tlbi vmalle1`, the
///    LOCAL variant: the handler's obligation is its own core's TLB;
///    the primitive's trailing `dsb ish; isb` retires the invalidation
///    before the next step).  The full flush conservatively covers
///    every descriptor the initiator posted for this core — the Lean
///    ledger (`drainShootdowns` + per-descriptor
///    `applyTlbInvalidation`) records the *precise* obligation, and
///    over-invalidation is always safe (an absent entry re-walks the
///    page tables); the refinement direction is
///    "runtime removes ⊇ model removes", so Theorem 3.3.1's per-core
///    absence conclusion carries over.  This also keeps the IRQ
///    handler free of any Lean-runtime call (the pending queues are
///    Lean state; draining them from a secondary core's IRQ context
///    would require a reentrant per-core Lean runtime, which does not
///    exist — the initiator's catch-up commit drains the ledger after
///    the acks certify hardware retirement).
/// 2. **Acknowledge** — [`ack_set`] (release-store), the SM7.B.4
///    release edge: publishes the TLBI retirement to the initiator's
///    acquire-poll.
/// 3. **`sev`** — wakes any event-paced waiter (free; the production
///    poll spins, see [`wait_all_acked_bounded_in`]).
///
/// Fail-closed: if the executing core id is somehow out of range the
/// handler acknowledges NOTHING (the initiator times out and panics —
/// diagnosable), rather than acknowledging the wrong slot (which
/// would let the initiator proceed with a target's TLB still stale).
///
/// `_source_cpu` (the SGI originator from `GICC_IAR[12:10]`) is
/// accepted per the [`crate::gic::SgiHandler`] signature; the primary
/// ack channel is the shared flag vector, so it is used only for the
/// optional direct-ack extension (plan §3.2 step 4d, not implemented
/// at v1.0.0).
#[deny(clippy::panic, clippy::unreachable, clippy::todo)]
pub fn tlb_shootdown_req_handler(_intid: u8, _source_cpu: u8) {
    tlb_shootdown_req_handler_in(
        &SHOOTDOWN_ACK,
        crate::per_cpu::current_core_id_from_tpidr() as usize,
    );
}

/// **WS-SM SM7.B.3** (testable inner form): the handler body over an
/// explicit flag slice and executing-core id.  Tests reset a *local*
/// slice first and assert the genuine `false → true` ack transition —
/// the global [`SHOOTDOWN_ACK`] boots all-`true`, so asserting on it
/// alone cannot distinguish "the handler acked" from "the flag was
/// never down" (the SM7.B test-hardening cut closed exactly that
/// vacuity).
#[deny(clippy::panic, clippy::unreachable, clippy::todo)]
pub fn tlb_shootdown_req_handler_in(slots: &[ShootdownAckFlag], core_id: usize) {
    if core_id >= slots.len() {
        // Fail closed: no ack (see docstring).  Unreachable on
        // correctly-initialised hardware (TPIDR_EL1 is set to the
        // core id at boot, always < 4 on BCM2712).
        return;
    }
    // Step 1 (WS-SM SM7.B debt (1)): retire the round's EXACT operands
    // locally (one `tlbi` per descriptor), matching the Lean model's
    // per-descriptor `applyTlbInvalidations`.  A torn read / empty round
    // / undecodable operand falls back to the conservative local
    // `tlbi vmalle1` — over-invalidation is always safe.  Each `tlbi_*`
    // retires with its own `dsb ish; isb`, so the drained invalidations
    // are complete before the ack.
    retire_round_ops_in(&SHOOTDOWN_OPS);
    // Step 2: the release edge.
    ack_set_in_slice(slots, core_id);
    // Step 3: wake event-paced waiters.
    crate::cpu::sev();
}

/// **WS-SM SM7.B.3**: register the `.tlbShootdownReq` handler in the
/// SM1.F.5 SGI handler table.
///
/// # Safety
///
/// Must be called during single-core boot with IRQs disabled, before
/// `bring_up_secondaries` (the [`crate::gic::register_sgi_handler`]
/// contract — the table is write-once-at-boot, read-only after).
pub unsafe fn register_tlb_shootdown_handler() {
    unsafe {
        crate::gic::register_sgi_handler(TLB_SHOOTDOWN_REQ_INTID, tlb_shootdown_req_handler);
    }
}

// ============================================================================
// WS-SM SM7.B.2 — Online-core mask (the runtime SGI target mask)
// ============================================================================

/// **WS-SM SM7.B.2**: the online-core bitmask — bit `c` set ⇔ core `c`
/// is *IRQ-serviceable* (the boot core is always online; secondaries
/// per `smp::CORE_IRQ_READY`, Acquire — the flag published after
/// `enable_irq`, NOT the primary's `CORE_READY` release; PR #839 review
/// P1).  The SM7.A PR #838 P1 obligation's "target-set computation must
/// enumerate online cores only" at the SGI-fire site: the Lean entry
/// masks its `.tlbShootdownReq` fires by this, matching
/// [`reset_for_round`]'s masked reset (both route through
/// [`irq_ready_online`]) — a core that cannot yet take the SGI is
/// neither reset, nor poked, nor waited on.
pub fn online_mask() -> u64 {
    online_mask_of(&irq_ready_online())
}

/// **WS-SM SM7.B.2** (testable core): fold an IRQ-serviceable boolean
/// snapshot into the online bitmask.  Bit `c` set ⇔ `online[c]`.
/// Factored out of [`online_mask`] so the masking logic is exercised
/// without touching the `smp::CORE_IRQ_READY` global.
#[inline]
pub fn online_mask_of(online: &[bool]) -> u64 {
    let mut mask: u64 = 0;
    for (i, &ready) in online.iter().enumerate() {
        if ready {
            mask |= 1u64 << i;
        }
    }
    mask
}

#[cfg(test)]
mod tests {
    // The crate is `no_std`; tests may use std (threads for the SM7.B.7
    // mutex stress) — same pattern as the gic.rs / rw_lock.rs test mods.
    extern crate std;

    use super::*;

    // ------------------------------------------------------------------------
    // SM7.A.3.A — struct layout invariants
    // ------------------------------------------------------------------------

    #[test]
    fn sm7a3_shootdown_ack_flag_is_one_cache_line() {
        // The module-scope assertion is compile-time; this confirms the
        // runtime observation matches.
        assert_eq!(core::mem::size_of::<ShootdownAckFlag>(), 64);
    }

    #[test]
    fn sm7a3_shootdown_ack_flag_is_64_byte_aligned() {
        assert_eq!(core::mem::align_of::<ShootdownAckFlag>(), 64);
    }

    #[test]
    fn sm7a3_new_constructor_sets_requested_initial_value() {
        let t = ShootdownAckFlag::new(true);
        let f = ShootdownAckFlag::new(false);
        assert!(t.acked.load(Ordering::Acquire));
        assert!(!f.acked.load(Ordering::Acquire));
    }

    #[test]
    fn sm7a3_boot_constructor_is_acknowledged() {
        // Quiescent boot: `true` = "no round in flight, nobody waited
        // on", matching Lean `TlbShootdownState.initial_ackOnCore`.
        let s = ShootdownAckFlag::acked_at_boot();
        assert!(s.acked.load(Ordering::Acquire));
    }

    // ------------------------------------------------------------------------
    // SM7.A.3.B — global array population (read-only: parallel tests
    // must never mutate SHOOTDOWN_ACK)
    // ------------------------------------------------------------------------

    #[test]
    fn sm7a3_shootdown_ack_array_has_one_slot_per_core() {
        assert_eq!(SHOOTDOWN_ACK.len(), MAX_SECONDARY_CORES + 1);
        assert_eq!(SHOOTDOWN_ACK.len(), 4);
    }

    #[test]
    fn sm7a3_shootdown_ack_boots_quiescent_all_acknowledged() {
        // No test in this binary mutates the global array (all
        // behaviour tests use stack-local slices), so the boot values
        // are stable under parallel test execution.
        assert!(all_acked());
        for core_id in 0..SHOOTDOWN_ACK.len() {
            assert!(
                ack_is_set(core_id),
                "core {} must boot acknowledged",
                core_id
            );
        }
    }

    #[test]
    fn sm7a3_shootdown_ack_array_slots_are_distinct_cache_lines() {
        let addrs: [usize; 4] = [
            &SHOOTDOWN_ACK[0] as *const ShootdownAckFlag as usize,
            &SHOOTDOWN_ACK[1] as *const ShootdownAckFlag as usize,
            &SHOOTDOWN_ACK[2] as *const ShootdownAckFlag as usize,
            &SHOOTDOWN_ACK[3] as *const ShootdownAckFlag as usize,
        ];
        for (i, &ai) in addrs.iter().enumerate() {
            assert_eq!(
                ai % 64,
                0,
                "SHOOTDOWN_ACK[{}] = {:#x} not 64-byte aligned",
                i,
                ai
            );
            for (j, &aj) in addrs.iter().enumerate().skip(i + 1) {
                assert_ne!(
                    ai, aj,
                    "SHOOTDOWN_ACK[{}] and SHOOTDOWN_ACK[{}] alias",
                    i, j
                );
            }
        }
    }

    #[test]
    fn sm7a3_shootdown_ack_array_stride_matches_struct_size() {
        let addrs: [usize; 4] = [
            &SHOOTDOWN_ACK[0] as *const ShootdownAckFlag as usize,
            &SHOOTDOWN_ACK[1] as *const ShootdownAckFlag as usize,
            &SHOOTDOWN_ACK[2] as *const ShootdownAckFlag as usize,
            &SHOOTDOWN_ACK[3] as *const ShootdownAckFlag as usize,
        ];
        for (i, w) in addrs.windows(2).enumerate() {
            assert_eq!(
                w[1] - w[0],
                core::mem::size_of::<ShootdownAckFlag>(),
                "SHOOTDOWN_ACK stride between slots {} and {}",
                i,
                i + 1
            );
        }
    }

    // ------------------------------------------------------------------------
    // SM7.A.3.C — round lifecycle on stack-local slices
    // ------------------------------------------------------------------------

    fn fresh_boot_flags() -> [ShootdownAckFlag; 4] {
        [
            ShootdownAckFlag::acked_at_boot(),
            ShootdownAckFlag::acked_at_boot(),
            ShootdownAckFlag::acked_at_boot(),
            ShootdownAckFlag::acked_at_boot(),
        ]
    }

    #[test]
    fn sm7a3_reset_for_round_marks_only_initiator_acknowledged() {
        // Mirrors Lean `beginShootdownRound_ackOnCore_iff`: acked ⟺
        // core == initiator.
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 0);
        assert!(ack_is_set_in_slice(&slots, 0));
        assert!(!ack_is_set_in_slice(&slots, 1));
        assert!(!ack_is_set_in_slice(&slots, 2));
        assert!(!ack_is_set_in_slice(&slots, 3));
    }

    #[test]
    fn sm7a3_reset_for_round_works_for_every_initiator() {
        for initiator in 0..4usize {
            let slots = fresh_boot_flags();
            reset_for_round_in_slice(&slots, initiator);
            for (core, slot) in slots.iter().enumerate() {
                assert_eq!(
                    slot.acked.load(Ordering::Acquire),
                    core == initiator,
                    "round by initiator {}: core {} flag wrong",
                    initiator,
                    core
                );
            }
        }
    }

    #[test]
    fn sm7a3_ack_set_marks_exactly_the_named_core() {
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 0);
        ack_set_in_slice(&slots, 2);
        assert!(
            ack_is_set_in_slice(&slots, 0),
            "initiator stays acknowledged"
        );
        assert!(!ack_is_set_in_slice(&slots, 1), "core 1 untouched");
        assert!(ack_is_set_in_slice(&slots, 2), "core 2 now acknowledged");
        assert!(!ack_is_set_in_slice(&slots, 3), "core 3 untouched");
    }

    #[test]
    fn sm7a3_ack_set_is_idempotent() {
        // A spurious duplicate .tlbShootdownReq SGI re-acknowledges
        // harmlessly (its drain returns nothing; the re-set is a no-op).
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 1);
        ack_set_in_slice(&slots, 3);
        ack_set_in_slice(&slots, 3);
        assert!(ack_is_set_in_slice(&slots, 3));
        assert!(!ack_is_set_in_slice(&slots, 0));
        assert!(!ack_is_set_in_slice(&slots, 2));
    }

    #[test]
    fn sm7a3_all_acked_false_while_any_target_outstanding() {
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 0);
        assert!(!all_acked_in_slice(&slots), "3 targets outstanding");
        ack_set_in_slice(&slots, 1);
        assert!(!all_acked_in_slice(&slots), "2 targets outstanding");
        ack_set_in_slice(&slots, 2);
        assert!(!all_acked_in_slice(&slots), "1 target outstanding");
    }

    #[test]
    fn sm7a3_full_round_trip_reaches_all_acked() {
        // The wait-loop termination anchor at runtime: reset, then
        // every target acknowledges → all_acked.  Mirrors the Lean
        // `allCores_foldl_acknowledgeShootdown_allAcked`.
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 2);
        for target in [0usize, 1, 3] {
            ack_set_in_slice(&slots, target);
        }
        assert!(all_acked_in_slice(&slots));
    }

    #[test]
    fn sm7a3_back_to_back_rounds_reset_cleanly() {
        // Round N completes, round N+1 (different initiator) must see
        // a clean reset — no acknowledgment leaks across rounds.
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 0);
        for target in [1usize, 2, 3] {
            ack_set_in_slice(&slots, target);
        }
        assert!(all_acked_in_slice(&slots), "round N complete");
        reset_for_round_in_slice(&slots, 3);
        assert!(!all_acked_in_slice(&slots), "round N+1 freshly open");
        assert!(
            ack_is_set_in_slice(&slots, 3),
            "new initiator born-acknowledged"
        );
        assert!(
            !ack_is_set_in_slice(&slots, 0),
            "previous initiator now a target"
        );
    }

    #[test]
    fn sm7a3_masked_reset_keeps_offline_cores_acknowledged() {
        // PR #838 review P1: a partial-core boot must not let a round
        // wait on a core that can never take the SGI.  Boot core 0
        // online, cores 2 and 3 offline (e.g. smp_max_cores=2).
        let slots = fresh_boot_flags();
        reset_for_round_in_slice_masked(&slots, 0, &[true, true, false, false]);
        assert!(
            ack_is_set_in_slice(&slots, 0),
            "initiator born-acknowledged"
        );
        assert!(
            !ack_is_set_in_slice(&slots, 1),
            "online target starts unacked"
        );
        assert!(
            ack_is_set_in_slice(&slots, 2),
            "offline core stays acknowledged"
        );
        assert!(
            ack_is_set_in_slice(&slots, 3),
            "offline core stays acknowledged"
        );
    }

    #[test]
    fn sm7a3_masked_round_trip_reaches_all_acked_with_partial_online() {
        // Only the online target must acknowledge for the round to
        // complete — the liveness half of the review-P1 fix.
        let slots = fresh_boot_flags();
        reset_for_round_in_slice_masked(&slots, 0, &[true, true, false, false]);
        assert!(!all_acked_in_slice(&slots), "online target outstanding");
        ack_set_in_slice(&slots, 1);
        assert!(
            all_acked_in_slice(&slots),
            "round completes without offline cores 2/3 ever acking"
        );
    }

    #[test]
    fn sm7a3_masked_reset_single_core_boot_is_immediately_all_acked() {
        // smp_enabled=false (the v1.0.0 default): only the boot core is
        // online, so a round has no remote targets and completes at
        // once — the wait loop must not spin on cores 1..3.
        let slots = fresh_boot_flags();
        reset_for_round_in_slice_masked(&slots, 0, &[true, false, false, false]);
        assert!(all_acked_in_slice(&slots));
    }

    #[test]
    fn sm7a3_masked_reset_all_online_equals_unmasked_reset() {
        // With every core online the masked form is exactly the
        // fully-online reset (the Lean beginShootdownRoundFor-allCores
        // = beginShootdownRound bridge, mechanically).
        let masked = fresh_boot_flags();
        let unmasked = fresh_boot_flags();
        reset_for_round_in_slice_masked(&masked, 2, &[true, true, true, true]);
        reset_for_round_in_slice(&unmasked, 2);
        for core in 0..4 {
            assert_eq!(
                ack_is_set_in_slice(&masked, core),
                ack_is_set_in_slice(&unmasked, core),
                "core {} differs between masked(all-online) and unmasked",
                core
            );
        }
    }

    #[test]
    #[should_panic(expected = "online mask length 3 != slot count 4")]
    fn sm7a3_masked_reset_panics_on_mask_length_mismatch() {
        let slots = fresh_boot_flags();
        reset_for_round_in_slice_masked(&slots, 0, &[true, true, false]);
    }

    #[test]
    fn sm7a3_all_acked_matches_conjunction_exhaustively() {
        // Mechanical conformance with the Lean `allAcked` predicate
        // (∀ c, ackOnCore c = true): for every one of the 2^4 flag
        // assignments, `all_acked_in_slice` agrees with the full
        // conjunction.  Exhaustive over the whole 4-core state space,
        // so no flag combination can diverge from the model.
        for bits in 0u32..16 {
            let slots = [
                ShootdownAckFlag::new(bits & 1 != 0),
                ShootdownAckFlag::new(bits & 2 != 0),
                ShootdownAckFlag::new(bits & 4 != 0),
                ShootdownAckFlag::new(bits & 8 != 0),
            ];
            let expected = bits == 0b1111;
            assert_eq!(
                all_acked_in_slice(&slots),
                expected,
                "flag assignment {:#06b}",
                bits
            );
        }
    }

    #[test]
    fn sm7a3_empty_slice_is_vacuously_all_acked() {
        // Degenerate input: `all` over an empty iterator is true.  The
        // production array is never empty (4 slots), but the inner form
        // must be total.
        let slots: [ShootdownAckFlag; 0] = [];
        assert!(all_acked_in_slice(&slots));
    }

    // ------------------------------------------------------------------------
    // SM7.A.3.D — fail-closed bounds enforcement
    // ------------------------------------------------------------------------

    #[test]
    #[should_panic(expected = "ack_set_in_slice: core_id 4 out of range")]
    fn sm7a3_ack_set_panics_on_out_of_range_core() {
        let slots = fresh_boot_flags();
        ack_set_in_slice(&slots, 4);
    }

    #[test]
    #[should_panic(expected = "ack_is_set_in_slice: core_id 7 out of range")]
    fn sm7a3_ack_is_set_panics_on_out_of_range_core() {
        let slots = fresh_boot_flags();
        let _ = ack_is_set_in_slice(&slots, 7);
    }

    #[test]
    #[should_panic(expected = "reset_for_round_in_slice: initiator 4 out of range")]
    fn sm7a3_reset_for_round_panics_on_out_of_range_initiator() {
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 4);
    }

    // ------------------------------------------------------------------------
    // WS-SM SM7.B — round lock, bounded wait, SGI handler, online mask
    // ------------------------------------------------------------------------

    /// SM7.B.3: the reserved INTID is pinned to the Lean
    /// `SgiKind.tlbShootdownReq_intid` (= 1) and the gic.rs SGI
    /// reservation table.
    #[test]
    fn sm7b3_tlb_shootdown_req_intid_matches_lean() {
        assert_eq!(TLB_SHOOTDOWN_REQ_INTID, 1);
    }

    /// SM7.B.6: the Lean `shootdownWaitTimeoutTicks` (540 000) mirrors
    /// the HAL's established bounded-wait budget (10 ms at 54 MHz).
    #[test]
    fn sm7b_wait_timeout_matches_wfe_default() {
        assert_eq!(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS, 540_000);
    }

    /// SM7.B.7: the global round lock is exclusive and re-acquirable —
    /// a second try-acquire fails while held, succeeds after release.
    /// (Serialised via the lock itself: this test owns the global for
    /// its scope because it is the only test touching it.)
    #[test]
    fn sm7b7_round_lock_try_acquire_exclusive_roundtrip() {
        assert!(round_lock_try_acquire(), "free lock must be acquirable");
        assert!(
            !round_lock_try_acquire(),
            "a held round lock must reject a second acquirer"
        );
        round_lock_release();
        assert!(round_lock_try_acquire(), "released lock re-acquirable");
        round_lock_release();
    }

    /// SM7.B.5: an already-all-acked round satisfies the bounded wait
    /// immediately — the clock is never consulted past the start read.
    #[test]
    fn sm7b5_wait_immediate_when_all_acked() {
        let slots = fresh_boot_flags(); // boots all-true
        let mut clock_reads = 0u32;
        let ok = wait_all_acked_bounded_in(&slots, 10, || {
            clock_reads += 1;
            0
        });
        assert!(ok);
        assert_eq!(clock_reads, 1, "only the start-of-wait read happens");
    }

    /// SM7.B.5: a late acknowledgment is observed, not misreported as
    /// a timeout — the poll re-checks after every clock read.
    #[test]
    fn sm7b5_wait_observes_late_ack() {
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 0); // cores 1..3 drop
        ack_set_in_slice(&slots, 1);
        ack_set_in_slice(&slots, 2);
        let mut ticks = 0u64;
        let ok = wait_all_acked_bounded_in(&slots, 1_000, || {
            ticks += 1;
            if ticks == 5 {
                // the last target acks mid-wait
                ack_set_in_slice(&slots, 3);
            }
            ticks
        });
        assert!(ok, "the late ack must be observed within the budget");
    }

    /// SM7.B.6: a round that never completes is a genuine timeout —
    /// the wait returns false once the budget elapses.
    #[test]
    fn sm7b6_wait_times_out_when_never_acked() {
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 0);
        let mut ticks = 0u64;
        let ok = wait_all_acked_bounded_in(&slots, 100, || {
            ticks += 200; // jump straight past the budget
            ticks
        });
        assert!(!ok, "an unacknowledged round must time out");
    }

    /// SM7.B.6 (verdict exactness): an ack landing exactly at the
    /// deadline is still reported as success — the deadline path
    /// re-checks the flags before returning, so a completed round can
    /// never be reported as a timeout.
    #[test]
    fn sm7b6_wait_final_check_at_deadline() {
        let slots = fresh_boot_flags();
        reset_for_round_in_slice(&slots, 0);
        let mut ticks = 0u64;
        let ok = wait_all_acked_bounded_in(&slots, 100, || {
            ticks += 200;
            if ticks >= 200 {
                for c in 1..4 {
                    ack_set_in_slice(&slots, c);
                }
            }
            ticks
        });
        assert!(ok, "acks at the deadline must be observed, not dropped");
    }

    /// SM7.B.3: the handler acknowledges the executing core (host
    /// TPIDR stub = core 0) after its (host no-op) local flush.
    /// Global-path smoke only — the genuine `false → true` transition
    /// is pinned by the `_in`-form tests below (the global vector
    /// boots all-`true`, so this assertion alone would be vacuous).
    #[test]
    fn sm7b3_handler_acks_executing_core() {
        tlb_shootdown_req_handler(TLB_SHOOTDOWN_REQ_INTID, 2);
        assert!(ack_is_set(0), "the handler release-sets its own flag");
    }

    /// SM7.B.3 (test-hardening cut): the handler performs a GENUINE
    /// `false → true` ack transition on its own core and touches no
    /// other core's flag — asserted on a local slice reset first, so
    /// the boot-`true` global vector cannot mask a no-op handler.
    #[test]
    fn sm7b3_handler_in_genuine_ack_transition_own_flag_only() {
        let slots: [ShootdownAckFlag; 4] = [
            ShootdownAckFlag::acked_at_boot(),
            ShootdownAckFlag::acked_at_boot(),
            ShootdownAckFlag::acked_at_boot(),
            ShootdownAckFlag::acked_at_boot(),
        ];
        // Round opened by core 3: cores 0..=2 genuinely down.
        reset_for_round_in_slice(&slots, 3);
        assert!(!ack_is_set_in_slice(&slots, 0), "precondition: flag down");
        assert!(!ack_is_set_in_slice(&slots, 1), "precondition: flag down");
        tlb_shootdown_req_handler_in(&slots, 0);
        assert!(
            ack_is_set_in_slice(&slots, 0),
            "the handler must release-set its own flag (false → true)"
        );
        assert!(
            !ack_is_set_in_slice(&slots, 1) && !ack_is_set_in_slice(&slots, 2),
            "the handler must not acknowledge on behalf of other targets"
        );
        assert!(ack_is_set_in_slice(&slots, 3), "initiator born-acknowledged");
    }

    /// SM7.B.3 (test-hardening cut): an out-of-range executing-core id
    /// acknowledges NOTHING — the fail-closed arm leaves every flag
    /// exactly as the reset put it (the initiator then times out and
    /// panics diagnosably, rather than proceeding over a stale TLB).
    #[test]
    fn sm7b3_handler_in_out_of_range_acks_nothing() {
        let slots: [ShootdownAckFlag; 4] = [
            ShootdownAckFlag::acked_at_boot(),
            ShootdownAckFlag::acked_at_boot(),
            ShootdownAckFlag::acked_at_boot(),
            ShootdownAckFlag::acked_at_boot(),
        ];
        reset_for_round_in_slice(&slots, 0);
        tlb_shootdown_req_handler_in(&slots, 7);
        assert!(
            !ack_is_set_in_slice(&slots, 1)
                && !ack_is_set_in_slice(&slots, 2)
                && !ack_is_set_in_slice(&slots, 3),
            "an out-of-range core id must not acknowledge any slot"
        );
    }

    // ------------------------------------------------------------------------
    // SM7.B debt (1) — per-descriptor operand mailbox
    // ------------------------------------------------------------------------

    /// SM7.B: a published operand list round-trips through the seqlock —
    /// the handler reads back EXACTLY what the initiator published.
    #[test]
    fn sm7b_mailbox_publish_snapshot_roundtrip() {
        let mb = ShootdownOpMailbox::new();
        let ops = [
            ShootdownOp {
                op_tag: 1, // Vae1
                asid: 0x2A,
                vaddr: 0x1000,
            },
            ShootdownOp {
                op_tag: 2, // Aside1
                asid: 0x2A,
                vaddr: 0,
            },
        ];
        publish_round_ops_in(&mb, &ops);
        let (snap, len) = snapshot_round_ops_in(&mb).expect("stable snapshot");
        assert_eq!(len, 2);
        assert_eq!(snap[0], ops[0]);
        assert_eq!(snap[1], ops[1]);
    }

    /// SM7.B: an in-progress publish (seqlock odd) is a torn read — the
    /// snapshot fails, so the handler falls back to the safe full flush.
    #[test]
    fn sm7b_mailbox_torn_read_during_publish_is_none() {
        let mb = ShootdownOpMailbox::new();
        publish_begin_in(&mb); // seqlock now odd — no matching commit
        assert!(
            snapshot_round_ops_in(&mb).is_none(),
            "a publish-in-progress must read as torn (None)"
        );
        // A commit restores a readable snapshot.
        publish_slot_in(&mb, 0, ShootdownOp::VMALLE1);
        publish_commit_in(&mb, 1);
        assert!(snapshot_round_ops_in(&mb).is_some());
    }

    /// SM7.B: an over-capacity commit collapses to a single `vmalle1`
    /// (the coalescing escape) rather than overflowing.
    #[test]
    fn sm7b_mailbox_overflow_collapses_to_vmalle1() {
        let mb = ShootdownOpMailbox::new();
        publish_begin_in(&mb);
        publish_commit_in(&mb, SHOOTDOWN_OP_CAPACITY + 5);
        let (snap, len) = snapshot_round_ops_in(&mb).expect("stable");
        assert_eq!(len, 1);
        assert_eq!(snap[0], ShootdownOp::VMALLE1);
    }

    /// SM7.B: retiring a per-descriptor round issues one local TLBI per
    /// operand (host: the `tlbi_*` are no-ops, so we assert the returned
    /// count) — the fidelity close vs the former blanket `vmalle1`.
    #[test]
    fn sm7b_retire_per_descriptor_counts_operands() {
        let mb = ShootdownOpMailbox::new();
        publish_round_ops_in(
            &mb,
            &[
                ShootdownOp {
                    op_tag: 1,
                    asid: 5,
                    vaddr: 0x4000,
                },
                ShootdownOp {
                    op_tag: 3, // Vale1
                    asid: 5,
                    vaddr: 0x5000,
                },
            ],
        );
        assert_eq!(
            retire_round_ops_in(&mb),
            Some(2),
            "two operands ⇒ two per-descriptor local TLBIs"
        );
    }

    /// SM7.B: an empty round (nothing published) retires as a
    /// conservative local full flush (fallback, `None`).
    #[test]
    fn sm7b_retire_empty_round_falls_back_to_full_flush() {
        let mb = ShootdownOpMailbox::new();
        publish_round_ops_in(&mb, &[]);
        assert_eq!(
            retire_round_ops_in(&mb),
            None,
            "an empty round ⇒ conservative local vmalle1 fallback"
        );
    }

    /// SM7.B: a torn read retires as the conservative full flush — the
    /// handler can never under-invalidate on a bad mailbox snapshot.
    #[test]
    fn sm7b_retire_torn_read_falls_back_to_full_flush() {
        let mb = ShootdownOpMailbox::new();
        publish_begin_in(&mb); // odd — torn
        assert_eq!(
            retire_round_ops_in(&mb),
            None,
            "a torn read ⇒ conservative local vmalle1 fallback"
        );
    }

    /// SM7.B: a published `vmalle1` operand retires as a per-descriptor
    /// step (the coalesced-round case) — one local full flush, counted.
    #[test]
    fn sm7b_retire_vmalle1_operand_is_one_step() {
        let mb = ShootdownOpMailbox::new();
        publish_round_ops_in(&mb, &[ShootdownOp::VMALLE1]);
        assert_eq!(retire_round_ops_in(&mb), Some(1));
    }

    /// SM7.B conformance: the mailbox op-tag encoding matches the Lean
    /// `Architecture.TlbInvalidation.toOpTag` decode — every valid tag
    /// decodes to the expected typed operand, and an out-of-range tag
    /// decodes to `None` (fail-safe in the handler).
    #[test]
    fn sm7b_op_tag_decode_conformance() {
        use crate::tlb::{decode_tlb_invalidation, TlbInvalidation};
        assert_eq!(
            decode_tlb_invalidation(0, 7, 0x10),
            Some(TlbInvalidation::Vmalle1)
        );
        assert_eq!(
            decode_tlb_invalidation(1, 7, 0x10),
            Some(TlbInvalidation::Vae1 {
                asid: 7,
                vaddr: 0x10
            })
        );
        assert_eq!(
            decode_tlb_invalidation(2, 7, 0x10),
            Some(TlbInvalidation::Aside1 { asid: 7 })
        );
        assert_eq!(
            decode_tlb_invalidation(3, 7, 0x10),
            Some(TlbInvalidation::Vale1 {
                asid: 7,
                vaddr: 0x10
            })
        );
        assert_eq!(decode_tlb_invalidation(4, 0, 0), None);
        assert_eq!(decode_tlb_invalidation(u32::MAX, 0, 0), None);
    }

    /// SM7.B.7 (test-hardening cut): multithreaded CAS-lock exclusivity
    /// stress — 8 threads hammer `round_lock_try_acquire_in` /
    /// `round_lock_release_in` on a LOCAL lock cell; an atomic
    /// critical-section occupancy counter proves at-most-one-holder at
    /// every instant, and the acquisition count proves the lock stays
    /// live (releases re-enable acquisition, the Lean
    /// `roundLockTryAcquire_after_release`).
    #[test]
    fn sm7b7_round_lock_mutex_stress() {
        // Cap contenders at the host's real parallelism (min 2 so the
        // exclusivity race is genuinely exercised) — a try-lock stress
        // does not need pathological oversubscription, and capping keeps
        // the host-test cooperative-yield path from starving under a
        // small CI core count (WS-SM SM7.B debt (7)).
        let threads = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .clamp(2, 8);
        let lock = AtomicBool::new(false);
        let in_crit = AtomicU32::new(0);
        let max_seen = AtomicU32::new(0);
        let acquisitions = AtomicUsize::new(0);
        std::thread::scope(|s| {
            for _ in 0..threads {
                s.spawn(|| {
                    for _ in 0..1000 {
                        if round_lock_try_acquire_in(&lock) {
                            let now = in_crit.fetch_add(1, Ordering::SeqCst) + 1;
                            max_seen.fetch_max(now, Ordering::SeqCst);
                            in_crit.fetch_sub(1, Ordering::SeqCst);
                            acquisitions.fetch_add(1, Ordering::SeqCst);
                            round_lock_release_in(&lock);
                        } else {
                            std::thread::yield_now();
                        }
                    }
                });
            }
        });
        assert_eq!(
            max_seen.load(Ordering::SeqCst),
            1,
            "at most one thread may ever hold the round lock"
        );
        assert!(
            acquisitions.load(Ordering::SeqCst) >= 1,
            "the lock must remain acquirable across releases"
        );
    }

    /// SM7.B.3: the handler registers into the SM1.F.5 table shape and
    /// dispatches through it (local table — no shared static).
    #[test]
    fn sm7b3_handler_registration_and_dispatch() {
        let mut table: [Option<crate::gic::SgiHandler>; 16] = [None; 16];
        crate::gic::register_sgi_handler_in(
            &mut table,
            TLB_SHOOTDOWN_REQ_INTID,
            tlb_shootdown_req_handler,
        );
        assert!(crate::gic::lookup_sgi_handler_in(&table, TLB_SHOOTDOWN_REQ_INTID).is_some());
        // dispatch through the table: the handler runs (host: no-op
        // flush + ack of core 0) without panicking.
        crate::gic::dispatch_sgi_in(&table, TLB_SHOOTDOWN_REQ_INTID, 3);
        assert!(ack_is_set(0));
    }

    /// SM7.B.2: the boot core is always in the online mask.
    #[test]
    fn sm7b2_online_mask_boot_core_always_set() {
        assert_eq!(online_mask() & 1, 1, "bit 0 (boot core) always set");
    }

    /// SM7.B.2 (PR #839 review P1): `online_mask_of` sets exactly the
    /// bits of the IRQ-serviceable snapshot — a released-but-not-yet-
    /// IRQ-ready secondary (its `CORE_IRQ_READY` slot still `false`) is
    /// excluded, so it is never a shootdown target.
    #[test]
    fn sm7b2_online_mask_of_excludes_not_irq_ready() {
        // Boot core + core 2 IRQ-ready; cores 1 and 3 released but not
        // yet past `enable_irq` (or timer-dead).
        assert_eq!(
            online_mask_of(&[true, false, true, false]),
            0b0101,
            "only IRQ-serviceable cores appear in the mask"
        );
        // All four serviceable.
        assert_eq!(online_mask_of(&[true, true, true, true]), 0b1111);
        // Boot core only (single-online-core v1.0.0 default boot).
        assert_eq!(online_mask_of(&[true, false, false, false]), 0b0001);
    }

    /// SM7.B.2 (PR #839 review P1): the reset mask and the SGI target
    /// mask are computed from the *same* IRQ-serviceable snapshot, so a
    /// not-IRQ-ready core is consistently excluded from BOTH the ack
    /// reset (stays born-acknowledged) and the SGI poke — it can never
    /// hold a reset flag it cannot clear, which is the hang the fix
    /// prevents.  Here we drive the shared masked reset with the same
    /// snapshot shape `online_mask_of` would fold.
    #[test]
    fn sm7b2_reset_and_target_masks_agree_on_not_irq_ready() {
        let online = [true, true, false, false]; // cores 2,3 not serviceable
        let mask = online_mask_of(&online);
        assert_eq!(mask, 0b0011, "cores 2 and 3 excluded from the SGI mask");
        // The masked reset over the same snapshot leaves the excluded
        // cores born-acknowledged, so the initiator's wait is not hung
        // on a core it never poked.
        let slots = [
            ShootdownAckFlag::new(false),
            ShootdownAckFlag::new(false),
            ShootdownAckFlag::new(false),
            ShootdownAckFlag::new(false),
        ];
        reset_for_round_in_slice_masked(&slots, 0, &online);
        // Cores 2 and 3 (not serviceable) stay acked; only cores 0,1
        // await their SGI.
        assert!(ack_is_set_in_slice(&slots, 0), "initiator born-acked");
        assert!(!ack_is_set_in_slice(&slots, 1), "core 1 awaits SGI");
        assert!(ack_is_set_in_slice(&slots, 2), "core 2 not-serviceable ⇒ born-acked");
        assert!(ack_is_set_in_slice(&slots, 3), "core 3 not-serviceable ⇒ born-acked");
    }
}
