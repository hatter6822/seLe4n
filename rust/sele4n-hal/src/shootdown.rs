// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-SM SM7.A.3**: per-core TLB-shootdown acknowledgment flags.
//!
//! The runtime realisation of the Lean model's
//! `TlbShootdownState.shootdownAck : Vector Nat numCores`
//! (`SeLe4n/Kernel/Architecture/TlbShootdown.lean`).  One
//! cache-line-aligned generation slot per core ([`ShootdownAckSlot`],
//! an [`AtomicU64`]) holding the highest round generation that core has
//! discharged: advanced by a release `fetch_max` in each target's
//! `.tlbShootdownReq` SGI handler (INTID 1; see the SGI reservation
//! table in [`crate::gic`]) and polled by the initiator, which waits
//! for `acked_gen[c] >= gen` rather than for a flag.
//!
//! Slots boot at 0 and are never cleared.  Both properties are load
//! bearing (SM7.F.3): an acknowledgment names the round it discharged,
//! so a `.tlbShootdownReq` SGI left pending by an earlier round cannot
//! satisfy a later round's wait, and with nothing to reset there is no
//! window between opening a round and publishing its operands.  The
//! Boolean flag vector this replaced had both hazards.
//!
//! ## Protocol role (SMP_TLB_SHOOTDOWN_PLAN.md §3.2, §4.2)
//!
//! A shootdown round for `(asid, vaddr)` initiated by core `c₀`:
//!
//! 1. `c₀` publishes the round's operands **and its generation** into
//!    [`SHOOTDOWN_OPS`] ([`publish_begin_in`] → [`publish_slot_in`] →
//!    [`publish_commit_in`], generation last) under the global round
//!    lock.  There is deliberately **no ack reset** — see
//!    "Round identity" below.
//! 2. `c₀` posts one descriptor per target into the Lean-side pending
//!    queues, then fires a `.tlbShootdownReq` SGI per online target.
//!    [`crate::gic::send_sgi`] emits `dsb ish` **before** the GICD_SGIR
//!    write (SM1.F.8), so the publish — and the queue writes — are
//!    globally observable before any target can take the interrupt.
//! 3. Each target's handler ([`tlb_shootdown_req_service_in`]) latches
//!    the published generation, retires that round's invalidations
//!    locally (`dsb`-completed), and only then calls [`ack_round`] — a
//!    monotone **release** `fetch_max`.
//! 4. `c₀` polls [`all_acked_for_round`] (**acquire**-loads, bounded by
//!    SM7.B.5's wait).  The release-acquire pairing guarantees that when
//!    `c₀` observes a target's generation, that target's TLBI completion
//!    happens-before the observation — the synchronisation edge
//!    Theorem 3.3.1's remote-core case rests on (formalised against the
//!    SM2.A memory model at SM7.B.4, `shootdownAck_release_acquire`).
//!
//! ## Round identity — why an acknowledgment carries a generation
//!
//! Under the SM7.A design each slot was a `bool`, a round opened by
//! *clearing* every online target's flag, and the handler set its flag
//! unconditionally after retiring whatever the mailbox held.  That is
//! unsound in the presence of a **stale SGI**: the cooperative
//! round-lock acquire ([`SHOOTDOWN_ROUND_LOCK`]) lets a waiter discharge
//! its own obligation without consuming the pending interrupt, and IRQs
//! are masked on the SVC path, so a `.tlbShootdownReq` SGI from an
//! earlier round can be delivered much later — including inside a
//! subsequent round's `reset → publish` window.  Its handler would then
//! retire the *previous* round's operands and acknowledge, satisfying
//! the new round's wait with that target's TLB still holding the
//! translation the round was meant to retire: an under-invalidation,
//! the SMP-C4 stale-TLB hazard.
//!
//! WS-SM SM7.F.3 makes an acknowledgment *name the round it
//! discharged*.  Each slot holds a monotone `acked_gen` advanced by
//! `fetch_max`; the mailbox publishes the round's generation; and the
//! handler reads that generation **before** any TLB maintenance, so
//! whichever branch it takes — the precise per-descriptor retire, or
//! the conservative `tlbi vmalle1` fallback on a torn read, a
//! generation mismatch, an empty round or an undecodable operand — the
//! work provably discharges the generation it acknowledges (the round's
//! page-table changes happened-before its publish, which happened-before
//! the read, which happens-before the flush).  A stale delivery can then
//! only re-affirm an older generation.
//!
//! With the round identified by its generation there is nothing to clear
//! before it opens, so the reset is gone — and with it the window the
//! hazard lived in.  The PR #838 review-P1 online mask moves from the
//! reset to the **wait** ([`all_acked_for_round_in_slice`]), which is
//! where it belongs: a core that cannot take the SGI is simply not
//! waited on.
//!
//! Rounds are still serialised system-wide by [`SHOOTDOWN_ROUND_LOCK`],
//! because [`SHOOTDOWN_OPS`] is a single-round resource: one mailbox
//! holds one round's operands, so a second publication would overwrite
//! operands a target has not yet retired.  The generation makes the
//! *acknowledgment channel* robust rather than replacing that
//! serialisation.  It does **not** bound the Lean-side pending queues
//! to one round per target — posting happens in the pure transition,
//! before the lock, and the catch-up drain after it, so those queues
//! can hold several rounds' descriptors and the drain is
//! window-restricted accordingly (`drainShootdownsInWindow`).
//!
//! ## Boot state
//!
//! All slots boot at generation `0`, and no round ever carries
//! generation `0` — [`allocate_round_generation`] returns
//! pre-increment + 1 from [`SHOOTDOWN_ROUND_SEQ`], which boots at `0`,
//! so the first round it hands out is `1`.  So before the first round
//! nobody is outstanding and a wait would trivially succeed rather than
//! deadlock.  The Lean `TlbShootdownState.initial` boots the same way
//! (`initial_roundGeneration = 0`), but its counter orders *commits* and
//! is not what these slots are compared against — see
//! [`allocate_round_generation_in`].
//!
//! ## Layout
//!
//! Each slot owns a full 64-byte cache line ([`ShootdownAckSlot`],
//! `repr(C, align(64))`) so a target's release-store does not
//! ping-pong the line under the initiator's poll of *other* targets'
//! slots — the same false-sharing discipline as
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
//! | `initial_ackOnCore` / `initial_allAcked` / `initial_roundGeneration` | `shootdown_ack_boots_quiescent_generation_zero` |
//! | `beginShootdownRoundFor_ackOnCore_iff` | `round_open_needs_no_reset_and_starts_outstanding`, `round_completes_for_every_initiator`, `initiator_is_never_waited_on` |
//! | `acknowledgeShootdown_ackOnCore_self` + `_ne` | `ack_round_marks_exactly_the_named_core` |
//! | `acknowledgeShootdown_monotone` (idempotence) | `ack_round_is_idempotent_and_monotone` |
//! | `allAcked` (∀-target conjunction, all 2⁴ × 4 states) | `wait_matches_conjunction_exhaustively` |
//! | `allCores_foldl_acknowledgeShootdown_allAcked` | `round_completes_for_every_initiator` |
//! | round identity after `shootdownRound_restores_quiescent` | `back_to_back_rounds_need_fresh_acknowledgments` |
//! | SM7.F.3 stale-SGI closure (no Lean counterpart — a runtime-only hazard) | `stale_acknowledgment_cannot_satisfy_a_later_round`, `wait_times_out_on_stale_acknowledgments_only` |
//! | fail-closed bounds (`CoreId` typing on the Lean side) | `*_panics_on_out_of_range_*` + the `ffi.rs` `shootdown_core_id_checked_*` panic tests |
//! | `TlbInvalidation.toOpTag` decode (SM7.B debt (1)) | `op_tag_decode_conformance` |
//! | `handleTlbShootdownReqOnCore` per-descriptor effect | `retire_per_descriptor_counts_operands`, `mailbox_publish_snapshot_roundtrip` |
//! | coalescing / fail-safe fallback (`collapseShootdownOps`) | `mailbox_overflow_collapses_to_vmalle1`, `retire_torn_read_falls_back_to_full_flush` |

use core::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering};

use crate::smp::MAX_SECONDARY_CORES;

/// **WS-SM SM7.A.3 + SM7.F.3**: one core's shootdown acknowledgment —
/// the **highest round generation** that core has serviced — padded to
/// a full cache line (64 bytes on Cortex-A76) to eliminate false
/// sharing between the per-core slots.
///
/// The explicit `_reserved` tail keeps every byte of the slot
/// deterministically initialised (no padding-byte hazards) and pins
/// the size independently of the alignment attribute.
#[repr(C, align(64))]
pub struct ShootdownAckSlot {
    /// The highest round generation this core has completed (and
    /// locally retired every invalidation of).  Advanced monotonically
    /// with `fetch_max(gen, Release)` by the owning core's SGI handler;
    /// read with `Ordering::Acquire` by a round initiator, which waits
    /// for `acked_gen >= its own generation`.
    ///
    /// Monotonicity is what makes the channel round-identified: an
    /// acknowledgment names the round it discharged, so a *stale* SGI —
    /// one left pending by an earlier round that the cooperative
    /// round-lock acquire self-serviced — can only ever re-affirm that
    /// earlier generation and can never satisfy a later round's wait.
    pub acked_gen: AtomicU64,
    /// Padding to a full cache line; reserved for SM7.B+ additions
    /// (e.g., a per-core drained-descriptor diagnostic counter).
    _reserved: [u8; 56],
}

impl ShootdownAckSlot {
    /// **WS-SM SM7.F.3**: const constructor with an explicit initial
    /// generation.  `const fn` because [`SHOOTDOWN_ACK`] is a `static`.
    #[inline]
    pub const fn new(initial: u64) -> Self {
        Self {
            acked_gen: AtomicU64::new(initial),
            _reserved: [0; 56],
        }
    }

    /// **WS-SM SM7.F.3**: the boot value — generation `0`, i.e.
    /// quiescent.  Runtime round generations are allocated from `1`
    /// upwards by [`allocate_round_generation`], so at boot there is no
    /// round for which any core is outstanding and the very first wait
    /// would trivially succeed rather than deadlock.  The Lean
    /// `TlbShootdownState.initial` is quiescent at boot for the same
    /// reason (`initial_roundGeneration = 0`, `initial_allAcked`),
    /// though its counter orders commits rather than hardware rounds.
    #[inline]
    pub const fn quiescent_at_boot() -> Self {
        Self::new(0)
    }
}

/// **WS-SM SM7.A.3 + SM7.F.3**: the per-core shootdown acknowledgment
/// slots, one cache-line-aligned slot per core, indexed by `core_id`
/// (0..=`MAX_SECONDARY_CORES`).  All slots boot at generation `0`
/// (quiescent).
///
/// `#[no_mangle]` + `#[used]` preserve the symbol so a hardware-side
/// debug probe can resolve it via the linker map, mirroring
/// [`crate::per_cpu_stats::PER_CPU_STATS`].
#[no_mangle]
#[used]
pub static SHOOTDOWN_ACK: [ShootdownAckSlot; MAX_SECONDARY_CORES + 1] = [
    ShootdownAckSlot::quiescent_at_boot(),
    ShootdownAckSlot::quiescent_at_boot(),
    ShootdownAckSlot::quiescent_at_boot(),
    ShootdownAckSlot::quiescent_at_boot(),
];

// Compile-time pin: each slot owns exactly one cache line.  Growing the
// struct past 64 bytes (e.g. adding a field without shrinking the
// `_reserved` tail) fails the build here with a clear diagnostic.
const _: () = assert!(
    core::mem::size_of::<ShootdownAckSlot>() == 64,
    "WS-SM SM7.A.3: ShootdownAckSlot must be one cache line (64 bytes); \
     shrink the `_reserved` tail when adding a field to stay within budget"
);

// Compile-time pin: cache-line aligned to avoid false sharing between
// adjacent cores' slots.
const _: () = assert!(
    core::mem::align_of::<ShootdownAckSlot>() == 64,
    "WS-SM SM7.A.3: ShootdownAckSlot must be 64-byte aligned to avoid \
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

/// **WS-SM SM7.F.3** (testable inner form): acknowledge round
/// generation `gen` for one core in an explicit slice — a monotone
/// `fetch_max` with `Release` ordering.
///
/// `fetch_max` rather than a plain store so an acknowledgment can never
/// *regress*: a stale handler run that services an older generation
/// leaves a newer round's already-recorded acknowledgment intact, and a
/// duplicate SGI for the same generation is idempotent.
///
/// Out-of-range `core_id` is a protocol violation and panics
/// (fail-closed): silently ignoring the acknowledgment would leave the
/// initiator waiting forever; aliasing to another slot would falsely
/// acknowledge a core whose TLB may still hold the stale entry — the
/// exact SMP-C4 hazard SM7 exists to close.  Callers routed from the
/// Lean side pass a `CoreId = Fin numCores`, so the panic arm is
/// structurally unreachable from well-typed kernel code.
#[inline]
pub fn ack_round_in_slice(slots: &[ShootdownAckSlot], core_id: usize, gen: u64) {
    assert!(
        core_id < slots.len(),
        "WS-SM SM7.F.3: ack_round_in_slice: core_id {} out of range (expected < {})",
        core_id,
        slots.len()
    );
    slots[core_id].acked_gen.fetch_max(gen, Ordering::Release);
}

/// **WS-SM SM7.F.3** (testable inner form): acquire-load the highest
/// round generation one core has acknowledged, from an explicit slice.
///
/// Panics on out-of-range `core_id` (fail-closed; see
/// [`ack_round_in_slice`]).
#[inline]
pub fn acked_gen_in_slice(slots: &[ShootdownAckSlot], core_id: usize) -> u64 {
    assert!(
        core_id < slots.len(),
        "WS-SM SM7.F.3: acked_gen_in_slice: core_id {} out of range (expected < {})",
        core_id,
        slots.len()
    );
    slots[core_id].acked_gen.load(Ordering::Acquire)
}

/// **WS-SM SM7.F.3** (testable inner form): has every core that can
/// service the round acknowledged generation `gen`?  The initiator
/// wait-loop's exit condition (plan §3.2 step 5), replacing the SM7.A
/// Boolean `all_acked`.
///
/// A core is waited on iff it is **online** (IRQ-serviceable) and not
/// the initiator itself; every other core is treated as satisfied.
/// This is the exact analogue of the Lean `beginShootdownRoundFor`
/// target mask (`beginShootdownRoundFor_ackOnCore_iff`) — but expressed
/// as a *wait* mask rather than a reset, which is what removes the
/// SM7.A reset step entirely and with it the window in which a stale
/// acknowledgment could be mistaken for a fresh one.
///
/// Rationale (liveness): in a partial-core boot (`smp_enabled=false` —
/// the v1.0.0 default — an `smp_max_cores` cap, or a PSCI CPU_ON
/// rejection leaving only a prefix of secondaries online), a not-yet-
/// IRQ-serviceable core can never take the `.tlbShootdownReq` SGI and
/// advance its generation; waiting on it would hang the initiator.
///
/// Rationale (safety): such a core holds no stale translation — every
/// secondary bring-up path runs `tlbi vmalle1` + DSB + ISB before
/// enabling its MMU ([`crate::mmu::init_mmu_secondary`]), so a core
/// that comes online *after* a round it was excluded from starts with
/// an empty TLB.  See [`crate::smp::CORE_IRQ_READY`].
///
/// Panics on a mask/slot length mismatch (fail-closed).
#[inline]
pub fn all_acked_for_round_in_slice(
    slots: &[ShootdownAckSlot],
    gen: u64,
    initiator: usize,
    online: &[bool],
) -> bool {
    assert!(
        online.len() == slots.len(),
        "WS-SM SM7.F.3: all_acked_for_round_in_slice: online mask length {} != slot count {}",
        online.len(),
        slots.len()
    );
    slots
        .iter()
        .enumerate()
        .all(|(i, s)| i == initiator || !online[i] || s.acked_gen.load(Ordering::Acquire) >= gen)
}

// ============================================================================
// Production accessors over the global SHOOTDOWN_ACK array
// ============================================================================

/// **WS-SM SM7.F.3**: acknowledge round generation `gen` for the given
/// core in [`SHOOTDOWN_ACK`].
///
/// Called by a target core's `.tlbShootdownReq` SGI handler (SM7.B.3)
/// only *after* the invalidations for `gen` have retired locally — the
/// release edge of the SM7.B.4 release-acquire pairing.  Panics on
/// out-of-range `core_id` (fail-closed; see [`ack_round_in_slice`]).
#[inline]
pub fn ack_round(core_id: usize, gen: u64) {
    ack_round_in_slice(&SHOOTDOWN_ACK, core_id, gen);
}

/// **WS-SM SM7.F.3**: acquire-load the highest round generation the
/// given core has acknowledged.  Panics on out-of-range `core_id`
/// (fail-closed).
#[inline]
pub fn acked_gen(core_id: usize) -> u64 {
    acked_gen_in_slice(&SHOOTDOWN_ACK, core_id)
}

/// **WS-SM SM7.B (PR #839 review P1)**: snapshot the per-core
/// IRQ-serviceable set from [`crate::smp::CORE_IRQ_READY`] (Acquire),
/// the single source of truth for both the round wait mask
/// ([`all_acked_for_round`]) and the SGI target mask ([`online_mask`]).
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

/// **WS-SM SM7.F.3**: has every IRQ-serviceable non-initiator core
/// acknowledged round generation `gen`?  The initiator wait-loop's exit
/// condition (plan §3.2 step 5; polled by SM7.B.5's bounded wait).
#[inline]
pub fn all_acked_for_round(gen: u64, initiator: usize) -> bool {
    all_acked_for_round_in_slice(&SHOOTDOWN_ACK, gen, initiator, &irq_ready_online())
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
/// **Contract (the SM7.A audit's round-serialisation obligation)**: at
/// most one shootdown round may be in flight system-wide.  An initiator
/// MUST hold this
/// lock across the entire hardware round — the operand+generation
/// publish, the `.tlbShootdownReq` SGI fires, its local broadcast TLBI,
/// and the [`wait_all_acked_bounded`] poll — and release it **only on
/// observing all-acked**.
///
/// **On timeout the lock is retained, permanently and deliberately**
/// (PR #854 review): a round that timed out has an invalidation no
/// target ever certified, so the correct end state is a quarantined
/// subsystem, not a freed lock.  Keeping it held means no other core
/// can reuse the mailbox or open a round on top of the uncertified one
/// in the window before [`crate::gic::halt_all`] takes effect — that
/// broadcast is best-effort, since a core with interrupts masked takes
/// the SGI only when it unmasks.  An earlier revision released the lock
/// immediately before the fail-closed path; do not restore that.  The
/// live seam is `completeShootdownRounds` in
/// `SeLe4n/Kernel/SyscallDispatchEntry.lean`, whose timeout arm calls
/// `haltFailClosed` **without** a preceding
/// `Concurrency.shootdownRoundLockRelease`.
///
/// The mailbox is a single-round resource and the
/// Lean capacity argument assumes one round's descriptors per target at
/// a time, so interleaved rounds would break both — see the Lean module
/// header (`TlbShootdown.lean`, "Round serialisation contract").
/// (Since SM7.F.3 the *acknowledgment channel* is no longer part of that
/// argument: acknowledgments carry the generation they discharged, so an
/// interleaving cannot make one round's ack satisfy another's wait.)
///
/// **Why a CAS try-lock and not the verified `TicketLock`**: a waiter
/// spinning for this lock is (with IRQs masked in the SVC path) unable
/// to take the holder's `.tlbShootdownReq` SGI — yet the holder's
/// round WAITS on that waiter's acknowledgment.  A blind spin would
/// therefore deadlock into the wait-timeout panic (holder waits on
/// waiter's ack; waiter waits on holder's release).  The acquire loop
/// must interleave lock attempts with **servicing the waiter's own
/// pending obligation** (its acknowledged generation is below the published round ⇒ some in-flight round
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
/// (`round_lock_mutex_stress`) exercises this form on a local
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

/// **WS-SM SM5.I**: is the global round lock currently held?
///
/// Diagnostic only — the value is a snapshot and any caller that
/// *acted* on it would be racing. Its one use is
/// `kernel_entry::assert_not_holding_round_lock`, the lock-order
/// tripwire: the kernel-entry lock is acquired strictly outside this
/// one, and taking them in the other order is the single edge that
/// would close a cycle.
#[must_use]
pub fn round_lock_is_held() -> bool {
    SHOOTDOWN_ROUND_LOCK.load(Ordering::Acquire)
}

// ============================================================================
// WS-SM SM7.F.3 (PR #854 review P1) — Runtime round-generation allocator
// ============================================================================
//
// The acknowledgment test is monotone (`acked_gen >= gen`, [`fetch_max`]),
// so a round's generation must order it against the rounds that can
// satisfy its wait — that is, against **hardware execution order**.
//
// The Lean model's `TlbShootdownState.roundGeneration` does NOT: it is
// advanced by the pure transition, inside the atomic state commit, while
// the hardware round is bracketed by [`SHOOTDOWN_ROUND_LOCK`] which the
// initiator acquires *afterwards*.  Nothing ties the two orders together,
// so with two cores committing shootdown-bearing syscalls concurrently:
//
//   - core A commits generation N, then stalls before the lock;
//   - core B commits N+1, wins the lock, runs its round to completion,
//     and every target's `acked_gen` reaches N+1;
//   - A finally takes the lock, publishes N, and waits for `>= N` —
//     which B's acknowledgments *already* satisfy.
//
// A would then return from a round no target ever serviced, with its
// operands still resident in every remote TLB: an under-invalidation,
// the SMP-C4 stale-TLB hazard, and precisely the failure SM7.F.3's
// generation tagging exists to prevent (it closed the same hazard for a
// *stale* acknowledgment; this is the *premature* one).
//
// The fix separates the two identities, because they answer different
// questions.  The model generation answers "which descriptors belong to
// this commit?" and must be allocated at commit time to key the window
// drain.  The runtime generation answers "which hardware round is this,
// relative to the rounds whose acknowledgments could satisfy it?" and is
// therefore allocated HERE — by a `fetch_add` performed while holding the
// round lock, so allocation order **is** execution order by construction,
// and an older round can no longer be certified by a newer round's acks.
//
// Being lock-held, the counter needs no ordering strength of its own; it
// is atomic so the FFI boundary stays sound if a future caller allocates
// outside the lock, and `AcqRel` keeps that hypothetical honest.

/// **WS-SM SM7.F.3** (PR #854 review P1): the monotone runtime
/// round-generation counter.  Starts at 0, so the first allocated
/// generation is 1 — never the vacuously-satisfied 0 (a slot's initial
/// `acked_gen` is 0, and `0 >= 0` would pass the wait with nothing
/// serviced).
pub static SHOOTDOWN_ROUND_SEQ: AtomicU64 = AtomicU64::new(0);

/// **WS-SM SM7.F.3** (testable inner form): allocate the next runtime
/// round generation from an explicit counter cell.
///
/// Must be called with the round lock held — that is what makes the
/// returned order the hardware execution order.
///
/// Fails closed on wrap: at `u64::MAX` allocations the counter would
/// return 0 and every subsequent wait would be satisfied vacuously by
/// the targets' retained high `acked_gen` values.  Unreachable in
/// practice (~584,000 years at one round per microsecond), but the
/// aliasing is exactly the class the generation tagging exists to
/// exclude, so it is rejected structurally rather than argued away.
///
/// **The halt is system-wide** (PR #854 review).  This branch used a
/// bare `assert!`, which takes the ordinary panic/abort path — and the
/// repository defines no `#[panic_handler]` at all, so what that path
/// does is decided by a final binary crate that does not exist until
/// SM9.E.  Meanwhile the caller has already committed its page-table
/// transition and holds the round lock, and has published neither
/// operands nor SGIs, so the other PEs hold stale translations that
/// nothing will ever invalidate.  Stopping this PE alone does not
/// address that; [`crate::gic::halt_all`] does, and it is defined
/// today.  Every other shootdown barrier reaches the same halt.
#[inline]
pub fn allocate_round_generation_in(seq: &AtomicU64) -> u64 {
    let generation = seq.fetch_add(1, Ordering::AcqRel).wrapping_add(1);
    if generation == 0 {
        // Diagnostic first, best-effort, then the halt -- the same split
        // the Lean `haltFailClosed` uses: the message is worth emitting,
        // but it is not what stops anything.
        crate::kprintln!(
            "WS-SM SM7.F.3: shootdown round generation counter wrapped; \
             halting fail-closed system-wide (a wrapped generation would \
             let stale acknowledgments satisfy every later round -- the \
             SMP-C4 stale-TLB hazard)"
        );
        crate::gic::halt_all()
    }
    generation
}

/// **WS-SM SM7.F.3** (PR #854 review P1): allocate the next runtime round
/// generation.  The Lean seam calls this immediately after acquiring the
/// round lock and uses the result for both the mailbox publish and the
/// acknowledgment wait.
pub fn allocate_round_generation() -> u64 {
    allocate_round_generation_in(&SHOOTDOWN_ROUND_SEQ)
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
    /// **WS-SM SM7.F.3**: the round generation these operands belong to
    /// — the **runtime** generation from [`SHOOTDOWN_ROUND_SEQ`], allocated
    /// by the initiator under the round lock, published with the operands
    /// and read by every handler *before* it does any TLB work.  It is
    /// what a handler acknowledges, so an acknowledgment always names the
    /// round whose operands (or a conservative superset) it actually
    /// retired.
    ///
    /// **Not** the Lean `TlbShootdownState.roundGeneration` (PR #854
    /// review P1).  The two order different things on purpose: the model
    /// generation orders *commits* and keys the window drain, this one
    /// orders *hardware rounds* and keys the acknowledgment channel.
    /// Under concurrency those orders differ, and publishing the
    /// commit-time value here is exactly what let a newer round's
    /// acknowledgments certify an older round nobody had executed — see
    /// [`allocate_round_generation_in`].
    ///
    /// Published outside the seqlock body with its own `Release` store
    /// so a handler can read "which round is current" without having to
    /// take a consistent snapshot of the whole operand array first.
    generation: AtomicU64,
    /// Number of valid operands (`≤ SHOOTDOWN_OP_CAPACITY`).
    len: AtomicUsize,
    /// Packed `(op_tag << 32) | asid` per slot.
    meta: [AtomicU64; SHOOTDOWN_OP_CAPACITY],
    /// The `vaddr` operand per slot.
    vaddr: [AtomicU64; SHOOTDOWN_OP_CAPACITY],
    /// The generation *inside* the seqlock body, so a stable snapshot
    /// can be checked against the generation the reader latched first.
    /// A mismatch means a newer round published between the two reads —
    /// the reader then falls back to the conservative full flush.
    body_generation: AtomicU64,
}

impl ShootdownOpMailbox {
    /// A quiescent (empty) mailbox — boots with `len = 0` and
    /// generation `0`, so a read before any round yields the empty
    /// operand list ⇒ the handler falls back to `vmalle1` (safe).
    pub const fn new() -> Self {
        ShootdownOpMailbox {
            seq: AtomicU32::new(0),
            generation: AtomicU64::new(0),
            len: AtomicUsize::new(0),
            meta: [const { AtomicU64::new(0) }; SHOOTDOWN_OP_CAPACITY],
            vaddr: [const { AtomicU64::new(0) }; SHOOTDOWN_OP_CAPACITY],
            body_generation: AtomicU64::new(0),
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

/// **WS-SM SM7.B + SM7.F.3** (testable inner form): commit a publish of
/// `len` operands belonging to round generation `gen` — bump the
/// seqlock to even (stable) with Release ordering, then publish the
/// generation itself (also Release, and *after* the body, so a handler
/// that observes `gen` is guaranteed to observe the operands it names).
///
/// A `len` above capacity collapses to a single `vmalle1` (matching the
/// Lean `collapseShootdownOps` / `enqueueShootdownOrCoalesce` escape);
/// `len == 0` leaves the mailbox empty so the handler falls back to
/// `vmalle1` (safe).
pub fn publish_commit_in(mb: &ShootdownOpMailbox, len: usize, gen: u64) {
    if len > SHOOTDOWN_OP_CAPACITY {
        mb.meta[0].store(0, Ordering::Relaxed); // vmalle1
        mb.vaddr[0].store(0, Ordering::Relaxed);
        mb.len.store(1, Ordering::Relaxed);
    } else {
        mb.len.store(len, Ordering::Relaxed);
    }
    mb.body_generation.store(gen, Ordering::Relaxed);
    // The begin bumped to odd; +1 restores even (stable), Release so a
    // reader's Acquire load observes all interior writes.
    let cur = mb.seq.load(Ordering::Relaxed);
    mb.seq.store(cur.wrapping_add(1), Ordering::Release);
    // Publish the generation LAST: a handler latches this first, and
    // everything it names is already visible by the Release above.
    mb.generation.store(gen, Ordering::Release);
}

/// **WS-SM SM7.B + SM7.F.3** (testable batch helper): publish a whole
/// operand slice for round generation `gen` under the seqlock
/// discipline.  A slice longer than capacity collapses to one
/// `vmalle1`.
///
/// This is the batch form the unit tests exercise; it exists only to
/// compose [`publish_begin_in`] / [`publish_slot_in`] /
/// [`publish_commit_in`] in one call.  The live path deliberately has
/// **no** global batch wrapper — the Lean seam
/// (`Architecture.publishShootdownOps`) walks its operand list across
/// the FFI boundary and drives those three entry points directly
/// (`ffi_shootdown_publish_{begin,slot,commit}`), since it never holds
/// a Rust slice to hand over.
pub fn publish_round_ops_in(mb: &ShootdownOpMailbox, ops: &[ShootdownOp], gen: u64) {
    publish_begin_in(mb);
    let n = ops.len();
    if n <= SHOOTDOWN_OP_CAPACITY {
        for (i, op) in ops.iter().enumerate() {
            publish_slot_in(mb, i, *op);
        }
    }
    publish_commit_in(mb, n, gen);
}

/// **WS-SM SM7.F.3** (testable inner form): acquire-load the round
/// generation currently published in an explicit mailbox.
///
/// A handler reads this **first**, before any TLB maintenance, and
/// acknowledges exactly this generation afterwards.  That ordering is
/// what makes the acknowledgment sound in every branch: the round's
/// page-table changes happened-before its publish, which happened-before
/// this read, which happens-before the local invalidation — so whatever
/// the handler ends up executing (the precise operands or the
/// conservative full flush) discharges generation `gen`.
#[inline]
pub fn current_generation_in(mb: &ShootdownOpMailbox) -> u64 {
    mb.generation.load(Ordering::Acquire)
}

/// **WS-SM SM7.F.3**: the round generation currently published in the
/// global mailbox.
#[inline]
pub fn current_generation() -> u64 {
    current_generation_in(&SHOOTDOWN_OPS)
}

/// **WS-SM SM7.B** (testable inner form): read a stable snapshot of an
/// explicit mailbox, together with the generation recorded inside the
/// seqlock body.  Returns `None` on a torn read (the seqlock was odd,
/// or the sequence advanced mid-read) or a length above capacity — the
/// caller must then fall back to the conservative `tlbi vmalle1`.
pub fn snapshot_round_ops_in(
    mb: &ShootdownOpMailbox,
) -> Option<([ShootdownOp; SHOOTDOWN_OP_CAPACITY], usize, u64)> {
    let s1 = mb.seq.load(Ordering::Acquire);
    if s1 & 1 != 0 {
        return None; // a publish is in progress
    }
    let len = mb.len.load(Ordering::Relaxed);
    if len > SHOOTDOWN_OP_CAPACITY {
        return None; // impossible on a well-formed publish → fail safe
    }
    let body_gen = mb.body_generation.load(Ordering::Relaxed);
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
        Some((out, len, body_gen))
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
pub fn retire_round_ops_in(mb: &ShootdownOpMailbox, expected_gen: u64) -> Option<usize> {
    match snapshot_round_ops_in(mb) {
        // The precise path requires the snapshot to belong to the round
        // the caller latched.  A mismatch means a newer round published
        // between the generation read and the snapshot, so the snapshot's
        // operands do not discharge `expected_gen` — fall back.
        Some((ops, len, body_gen)) if len > 0 && body_gen == expected_gen => {
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
        // Empty round, torn read, or a generation mismatch → conservative
        // local full flush.  Sound for `expected_gen` because the caller
        // read that generation *before* calling, so the round's page-table
        // changes happened-before this flush and no entry it retires can
        // be re-walked.
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
/// [`all_acked_for_round_in_slice`] until it holds or `timeout_ticks` have
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
    slots: &[ShootdownAckSlot],
    gen: u64,
    initiator: usize,
    online: &[bool],
    timeout_ticks: u64,
    mut now: C,
) -> bool {
    let start = now();
    loop {
        if all_acked_for_round_in_slice(slots, gen, initiator, online) {
            return true;
        }
        if now().saturating_sub(start) >= timeout_ticks {
            // One final check: the acks may have landed between the
            // last poll and the deadline read (verdict exactness —
            // never report a timeout on a completed round).
            return all_acked_for_round_in_slice(slots, gen, initiator, online);
        }
        core::hint::spin_loop();
    }
}

/// **WS-SM SM7.B.5 + B.6 + SM7.F.3**: bounded poll for
/// round-`gen`-acknowledged over the production slots, clocked by the
/// generic timer (`CNTPCT_EL0`).  `true` = every IRQ-serviceable
/// non-initiator core has acknowledged `gen`; `false` = timeout (the
/// caller's fail-closed panic trigger — a silently skipped invalidation
/// would be the SMP-C4 stale-TLB hazard).
pub fn wait_all_acked_bounded(
    gen: u64,
    initiator: usize,
    online_mask: u64,
    timeout_ticks: u64,
) -> bool {
    // PR #854 review: the mask is the round's OWN snapshot, taken once by
    // the Lean seam and used for both the SGI loop and this wait.  Re-reading
    // `CORE_IRQ_READY` here would let a secondary that became serviceable
    // between the two reads be waited on without ever having been poked.
    wait_all_acked_bounded_in(
        &SHOOTDOWN_ACK,
        gen,
        initiator,
        &online_from_mask(online_mask),
        timeout_ticks,
        crate::timer::read_counter,
    )
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
/// 1. **Retire the round's invalidations locally** — the published
///    operands, one `tlbi` each, or the conservative local
///    `tlbi vmalle1` on any doubt (each primitive's trailing
///    `dsb ish; isb` retires the invalidation before the next step).
///    Over-invalidation is always safe (an absent entry re-walks the
///    page tables); the refinement direction is
///    "runtime removes ⊇ model removes", so Theorem 3.3.1's per-core
///    absence conclusion carries over.  The handler stays free of any
///    Lean-runtime call (the pending queues are Lean state; draining
///    them from a secondary core's IRQ context would require a
///    reentrant per-core Lean runtime, which does not exist — the
///    initiator's catch-up commit drains the ledger after the
///    acknowledgments certify hardware retirement).
/// 2. **Acknowledge** — [`ack_round`] (monotone release `fetch_max`),
///    the SM7.B.4 release edge: publishes the TLBI retirement to the
///    initiator's acquire-poll, naming the round it discharged.
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
/// explicit slot slice and executing-core id.  Tests drive a *local*
/// slice so they can assert the genuine generation advance — the global
/// [`SHOOTDOWN_ACK`] boots at 0 and only ever moves forward, so
/// asserting on it alone cannot distinguish "the handler acked this
/// round" from "some earlier round already left the slot high" (the
/// SM7.B test-hardening cut closed exactly that vacuity, and SM7.F.3
/// re-based it from flags onto generations).
#[deny(clippy::panic, clippy::unreachable, clippy::todo)]
pub fn tlb_shootdown_req_handler_in(slots: &[ShootdownAckSlot], core_id: usize) {
    if core_id >= slots.len() {
        // Fail closed: no ack (see docstring).  Unreachable on
        // correctly-initialised hardware (TPIDR_EL1 is set to the
        // core id at boot, always < 4 on BCM2712).
        return;
    }
    tlb_shootdown_req_service_in(&SHOOTDOWN_OPS, slots, core_id);
}

/// **WS-SM SM7.B.3 + SM7.F.3** (testable inner form over both an
/// explicit mailbox and an explicit slot slice): latch the round
/// generation, retire that round's invalidations locally, acknowledge
/// exactly that generation.
///
/// **The ordering is the correctness argument.**  The generation is
/// read *first*, before any TLB maintenance:
///
/// * round `gen`'s page-table changes happened-before its publish
///   (the initiator commits the pure transition, then publishes), and
/// * its publish happened-before this Acquire read, and
/// * this read happens-before the local invalidation below.
///
/// So whichever branch [`retire_round_ops_in`] takes — the precise
/// per-descriptor retire when the snapshot belongs to `gen`, or the
/// conservative `tlbi vmalle1` on a torn read, a generation mismatch,
/// an empty round or an undecodable operand — the work discharges
/// `gen`, and no invalidated entry can be re-walked (the mapping is
/// already gone from the page tables).  Acknowledging `gen` is
/// therefore always earned.
///
/// This is what closes the stale-SGI hazard the SM7.A Boolean flag had:
/// a `.tlbShootdownReq` SGI left pending by an earlier round (the
/// cooperative round-lock acquire self-acknowledges without consuming
/// the interrupt) can now only re-affirm the generation it actually
/// serviced.  Under the old scheme its unconditional `ack_set` could
/// land after a *later* round's reset and satisfy that round's wait
/// without ever retiring its operands.
#[deny(clippy::panic, clippy::unreachable, clippy::todo)]
pub fn tlb_shootdown_req_service_in(
    mb: &ShootdownOpMailbox,
    slots: &[ShootdownAckSlot],
    core_id: usize,
) {
    if core_id >= slots.len() {
        return; // fail closed, as above
    }
    // Step 0 (WS-SM SM7.F.3): latch the round identity BEFORE any TLB work.
    let gen = current_generation_in(mb);
    // Step 1 (WS-SM SM7.B debt (1)): retire the round's EXACT operands
    // locally (one `tlbi` per descriptor), matching the Lean model's
    // per-descriptor `applyTlbInvalidations`.  Each `tlbi_*` retires with
    // its own `dsb ish; isb`, so the invalidations are complete before
    // the acknowledgment.
    retire_round_ops_in(mb, gen);
    // Step 2: the release edge — monotone, and it names the round.
    ack_round_in_slice(slots, core_id, gen);
    // Step 3: wake event-paced waiters.
    crate::cpu::sev();
}

/// **WS-SM SM7.B.7 + SM7.F.3** (testable inner form): the cooperative
/// round-lock acquire's self-service arm — a core spinning for the
/// round lock discharges its own outstanding obligation so the in-flight
/// round's initiator (which waits on *this* core's acknowledgment) can
/// make progress.
///
/// Returns `true` when it serviced a round.  IRQs are masked on the SVC
/// path, so this core cannot take the initiator's `.tlbShootdownReq`
/// SGI; the flush is therefore issued directly here.  It is the LOCAL
/// full flush (`tlbi vmalle1`), not a broadcast: the obligation is this
/// core's own view, and the in-flight round's initiator owns the
/// broadcast step.  A full flush is a superset of any operand set, so —
/// with the generation latched first, as in
/// [`tlb_shootdown_req_service_in`] — acknowledging it is earned.
///
/// The SGI this core was sent stays pending and will be delivered later;
/// that stale delivery is harmless precisely because the acknowledgment
/// it then makes names the generation it re-services, not whichever
/// round happens to be in flight.
pub fn self_service_round_in(
    mb: &ShootdownOpMailbox,
    slots: &[ShootdownAckSlot],
    core_id: usize,
) -> bool {
    if core_id >= slots.len() {
        return false; // fail closed
    }
    let gen = current_generation_in(mb);
    if acked_gen_in_slice(slots, core_id) >= gen {
        return false; // nothing outstanding for this core
    }
    crate::tlb::tlbi_vmalle1();
    ack_round_in_slice(slots, core_id, gen);
    crate::cpu::sev();
    true
}

/// **WS-SM SM7.B.7 + SM7.F.3**: the production self-service arm over the
/// global mailbox and acknowledgment slots.
pub fn self_service_round(core_id: usize) -> bool {
    self_service_round_in(&SHOOTDOWN_OPS, &SHOOTDOWN_ACK, core_id)
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
/// [`all_acked_for_round`]'s masked wait (both route through
/// `irq_ready_online`) — a core that cannot yet take the SGI is
/// neither poked nor waited on.
pub fn online_mask() -> u64 {
    online_mask_of(&irq_ready_online())
}

/// **WS-SM SM7.B.2 (PR #854 review)**: the inverse of [`online_mask_of`]
/// — expand a round's captured online bitmask back into the per-core
/// boolean form the wait predicate consumes.
///
/// This exists so the acknowledgment wait can be driven by the **same
/// snapshot** the SGI loop targeted, rather than re-reading
/// `CORE_IRQ_READY`.  A secondary that publishes IRQ-readiness between
/// the two reads would otherwise be absent from the SGI loop (so it is
/// never poked) yet present in the wait (so it is required to
/// acknowledge) — a round that can only time out, and since v0.32.117
/// a timeout genuinely halts the core.  `bring_up_secondaries_inner`
/// returns after its `CPU_ON` calls without waiting for secondaries to
/// publish, so the window is reachable during ordinary boot.
#[inline]
pub fn online_from_mask(mask: u64) -> [bool; MAX_SECONDARY_CORES + 1] {
    let mut online = [false; MAX_SECONDARY_CORES + 1];
    for (i, slot) in online.iter_mut().enumerate() {
        *slot = mask & (1u64 << i) != 0;
    }
    online
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
    fn shootdown_ack_slot_is_one_cache_line() {
        // The module-scope assertion is compile-time; this confirms the
        // runtime observation matches.
        assert_eq!(core::mem::size_of::<ShootdownAckSlot>(), 64);
    }

    #[test]
    fn shootdown_ack_slot_is_64_byte_aligned() {
        assert_eq!(core::mem::align_of::<ShootdownAckSlot>(), 64);
    }

    #[test]
    fn new_constructor_sets_requested_initial_generation() {
        let zero = ShootdownAckSlot::new(0);
        let seven = ShootdownAckSlot::new(7);
        assert_eq!(zero.acked_gen.load(Ordering::Acquire), 0);
        assert_eq!(seven.acked_gen.load(Ordering::Acquire), 7);
    }

    #[test]
    fn boot_constructor_is_generation_zero() {
        // Quiescent boot: generation 0, and no round ever carries
        // generation 0 (`allocate_round_generation` returns
        // pre-increment + 1 from a counter that boots at 0), so no core
        // is outstanding for any round before the first one opens.
        let s = ShootdownAckSlot::quiescent_at_boot();
        assert_eq!(s.acked_gen.load(Ordering::Acquire), 0);
    }

    // ------------------------------------------------------------------------
    // SM7.A.3.B — global array population (read-only: parallel tests
    // must never mutate SHOOTDOWN_ACK)
    // ------------------------------------------------------------------------

    #[test]
    fn shootdown_ack_array_has_one_slot_per_core() {
        assert_eq!(SHOOTDOWN_ACK.len(), MAX_SECONDARY_CORES + 1);
        assert_eq!(SHOOTDOWN_ACK.len(), 4);
    }

    #[test]
    fn shootdown_ack_boots_quiescent_generation_zero() {
        // No test in this binary mutates the global array (all
        // behaviour tests use stack-local slices), so the boot values
        // are stable under parallel test execution.
        for core_id in 0..SHOOTDOWN_ACK.len() {
            assert_eq!(
                acked_gen(core_id),
                0,
                "core {} must boot at generation 0",
                core_id
            );
        }
        // Generation 0 is trivially satisfied — the first wait before any
        // round would exit at once rather than deadlock.
        assert!(all_acked_for_round(0, 0));
    }

    #[test]
    fn shootdown_ack_array_slots_are_distinct_cache_lines() {
        let addrs: [usize; 4] = [
            &SHOOTDOWN_ACK[0] as *const ShootdownAckSlot as usize,
            &SHOOTDOWN_ACK[1] as *const ShootdownAckSlot as usize,
            &SHOOTDOWN_ACK[2] as *const ShootdownAckSlot as usize,
            &SHOOTDOWN_ACK[3] as *const ShootdownAckSlot as usize,
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
    fn shootdown_ack_array_stride_matches_struct_size() {
        let addrs: [usize; 4] = [
            &SHOOTDOWN_ACK[0] as *const ShootdownAckSlot as usize,
            &SHOOTDOWN_ACK[1] as *const ShootdownAckSlot as usize,
            &SHOOTDOWN_ACK[2] as *const ShootdownAckSlot as usize,
            &SHOOTDOWN_ACK[3] as *const ShootdownAckSlot as usize,
        ];
        for (i, w) in addrs.windows(2).enumerate() {
            assert_eq!(
                w[1] - w[0],
                core::mem::size_of::<ShootdownAckSlot>(),
                "SHOOTDOWN_ACK stride between slots {} and {}",
                i,
                i + 1
            );
        }
    }

    // ------------------------------------------------------------------------
    // SM7.F.3 — round lifecycle on stack-local slices
    // ------------------------------------------------------------------------

    fn fresh_boot_slots() -> [ShootdownAckSlot; 4] {
        [
            ShootdownAckSlot::quiescent_at_boot(),
            ShootdownAckSlot::quiescent_at_boot(),
            ShootdownAckSlot::quiescent_at_boot(),
            ShootdownAckSlot::quiescent_at_boot(),
        ]
    }

    /// Every core online — the fully-populated wait mask.
    const ALL_ONLINE: [bool; 4] = [true, true, true, true];

    #[test]
    fn round_open_needs_no_reset_and_starts_outstanding() {
        // Mirrors Lean `beginShootdownRoundFor_ackOnCore_iff`: at round
        // open the initiator is satisfied and every online target is
        // outstanding.  There is NO reset step — the round is simply a
        // higher generation than anyone has acknowledged.
        let slots = fresh_boot_slots();
        assert!(!all_acked_for_round_in_slice(&slots, 1, 0, &ALL_ONLINE));
        for target in [1usize, 2, 3] {
            assert!(
                acked_gen_in_slice(&slots, target) < 1,
                "core {} must start outstanding for generation 1",
                target
            );
        }
    }

    #[test]
    fn round_completes_for_every_initiator() {
        for initiator in 0..4usize {
            let slots = fresh_boot_slots();
            assert!(
                all_acked_for_round_in_slice(&slots, 0, initiator, &ALL_ONLINE),
                "generation 0 is vacuously satisfied"
            );
            assert!(!all_acked_for_round_in_slice(
                &slots,
                1,
                initiator,
                &ALL_ONLINE
            ));
            for target in 0..4usize {
                if target != initiator {
                    ack_round_in_slice(&slots, target, 1);
                }
            }
            assert!(
                all_acked_for_round_in_slice(&slots, 1, initiator, &ALL_ONLINE),
                "round by initiator {} must complete once every target acked",
                initiator
            );
        }
    }

    #[test]
    fn ack_round_marks_exactly_the_named_core() {
        let slots = fresh_boot_slots();
        ack_round_in_slice(&slots, 2, 1);
        assert_eq!(acked_gen_in_slice(&slots, 0), 0, "core 0 untouched");
        assert_eq!(acked_gen_in_slice(&slots, 1), 0, "core 1 untouched");
        assert_eq!(acked_gen_in_slice(&slots, 2), 1, "core 2 acknowledged");
        assert_eq!(acked_gen_in_slice(&slots, 3), 0, "core 3 untouched");
    }

    #[test]
    fn ack_round_is_idempotent_and_monotone() {
        // A spurious duplicate .tlbShootdownReq SGI re-acknowledges
        // harmlessly, and an OLDER generation can never lower the
        // recorded one (`fetch_max`) — the property that makes a stale
        // handler run safe.
        let slots = fresh_boot_slots();
        ack_round_in_slice(&slots, 3, 5);
        ack_round_in_slice(&slots, 3, 5);
        assert_eq!(acked_gen_in_slice(&slots, 3), 5);
        ack_round_in_slice(&slots, 3, 2);
        assert_eq!(
            acked_gen_in_slice(&slots, 3),
            5,
            "a stale acknowledgment must not regress the recorded generation"
        );
        ack_round_in_slice(&slots, 3, 9);
        assert_eq!(acked_gen_in_slice(&slots, 3), 9);
    }

    #[test]
    fn wait_false_while_any_target_outstanding() {
        let slots = fresh_boot_slots();
        assert!(!all_acked_for_round_in_slice(&slots, 1, 0, &ALL_ONLINE));
        ack_round_in_slice(&slots, 1, 1);
        assert!(!all_acked_for_round_in_slice(&slots, 1, 0, &ALL_ONLINE));
        ack_round_in_slice(&slots, 2, 1);
        assert!(!all_acked_for_round_in_slice(&slots, 1, 0, &ALL_ONLINE));
        ack_round_in_slice(&slots, 3, 1);
        assert!(all_acked_for_round_in_slice(&slots, 1, 0, &ALL_ONLINE));
    }

    #[test]
    fn back_to_back_rounds_need_fresh_acknowledgments() {
        // Round N completes; round N+1 (a different initiator) must not
        // inherit it — the "no acknowledgment leaks across rounds"
        // property, now structural rather than reset-enforced.
        let slots = fresh_boot_slots();
        for target in [1usize, 2, 3] {
            ack_round_in_slice(&slots, target, 1);
        }
        assert!(all_acked_for_round_in_slice(&slots, 1, 0, &ALL_ONLINE));
        assert!(
            !all_acked_for_round_in_slice(&slots, 2, 3, &ALL_ONLINE),
            "round N+1 starts with every target outstanding"
        );
        for target in [0usize, 1, 2] {
            ack_round_in_slice(&slots, target, 2);
        }
        assert!(all_acked_for_round_in_slice(&slots, 2, 3, &ALL_ONLINE));
    }

    #[test]
    fn stale_acknowledgment_cannot_satisfy_a_later_round() {
        // THE regression test for the SM7.F.3 security fix.  Under the
        // SM7.A Boolean scheme a `.tlbShootdownReq` SGI left pending by
        // round 1 (self-serviced by the cooperative round-lock acquire)
        // could be delivered inside round 2's reset→publish window; its
        // unconditional `ack_set` then satisfied round 2's wait without
        // round 2's operands ever having been retired on that core.
        //
        // With generation-carrying acknowledgments the stale handler run
        // re-affirms generation 1 and round 2 keeps waiting.
        let slots = fresh_boot_slots();
        // Round 1 (initiator 0): core 1 self-services, cores 2/3 handle.
        for target in [1usize, 2, 3] {
            ack_round_in_slice(&slots, target, 1);
        }
        assert!(all_acked_for_round_in_slice(&slots, 1, 0, &ALL_ONLINE));
        // Round 2 (initiator 3) opens.  Core 1's STALE round-1 SGI now
        // fires and its handler acknowledges the round it serviced.
        ack_round_in_slice(&slots, 1, 1);
        assert!(
            !all_acked_for_round_in_slice(&slots, 2, 3, &ALL_ONLINE),
            "a stale round-1 acknowledgment must NOT satisfy round 2"
        );
        // Only the genuine round-2 service satisfies it.
        for target in [0usize, 1, 2] {
            ack_round_in_slice(&slots, target, 2);
        }
        assert!(all_acked_for_round_in_slice(&slots, 2, 3, &ALL_ONLINE));
    }

    #[test]
    fn wait_mask_keeps_offline_cores_out_of_the_round() {
        // PR #838 review P1, restated as a wait mask: a partial-core
        // boot must not let a round wait on a core that can never take
        // the SGI.  Boot core 0 online, cores 2 and 3 offline
        // (e.g. smp_max_cores=2).
        let slots = fresh_boot_slots();
        let online = [true, true, false, false];
        assert!(!all_acked_for_round_in_slice(&slots, 1, 0, &online));
        ack_round_in_slice(&slots, 1, 1);
        assert!(
            all_acked_for_round_in_slice(&slots, 1, 0, &online),
            "round completes without offline cores 2/3 ever acknowledging"
        );
    }

    #[test]
    fn single_core_boot_round_is_immediately_satisfied() {
        // smp_enabled=false (the v1.0.0 default): only the boot core is
        // online, so a round has no remote targets and completes at
        // once — the wait loop must not spin on cores 1..3.
        let slots = fresh_boot_slots();
        assert!(all_acked_for_round_in_slice(
            &slots,
            1,
            0,
            &[true, false, false, false]
        ));
    }

    #[test]
    fn initiator_is_never_waited_on() {
        // The initiator retires locally (the `tlbiForSharing` broadcast
        // reaches the issuing PE) and is never a target of its own
        // round — the Lean `beginShootdownRoundFor_ackOnCore_iff`
        // initiator arm.
        let slots = fresh_boot_slots();
        for target in [0usize, 1, 3] {
            ack_round_in_slice(&slots, target, 4);
        }
        assert!(
            all_acked_for_round_in_slice(&slots, 4, 2, &ALL_ONLINE),
            "core 2 as initiator need not acknowledge its own round"
        );
        assert_eq!(acked_gen_in_slice(&slots, 2), 0);
    }

    #[test]
    #[should_panic(expected = "online mask length 3 != slot count 4")]
    fn wait_panics_on_mask_length_mismatch() {
        let slots = fresh_boot_slots();
        let _ = all_acked_for_round_in_slice(&slots, 1, 0, &[true, true, false]);
    }

    #[test]
    fn wait_matches_conjunction_exhaustively() {
        // Mechanical conformance with the Lean `allAcked` predicate
        // restricted to the round's target set: for every one of the 2^4
        // acknowledged/outstanding assignments, the wait predicate agrees
        // with the explicit conjunction over online non-initiator cores.
        // Exhaustive over the whole 4-core state space.
        for bits in 0u32..16 {
            for initiator in 0..4usize {
                let slots = [
                    ShootdownAckSlot::new(if bits & 1 != 0 { 1 } else { 0 }),
                    ShootdownAckSlot::new(if bits & 2 != 0 { 1 } else { 0 }),
                    ShootdownAckSlot::new(if bits & 4 != 0 { 1 } else { 0 }),
                    ShootdownAckSlot::new(if bits & 8 != 0 { 1 } else { 0 }),
                ];
                let expected = (0..4usize).all(|c| c == initiator || (bits >> c) & 1 != 0);
                assert_eq!(
                    all_acked_for_round_in_slice(&slots, 1, initiator, &ALL_ONLINE),
                    expected,
                    "assignment {:#06b} with initiator {}",
                    bits,
                    initiator
                );
            }
        }
    }

    #[test]
    fn wait_on_empty_slice_is_vacuously_satisfied() {
        // Degenerate input: `all` over an empty iterator is true.  The
        // production array is never empty (4 slots), but the inner form
        // must be total.
        let slots: [ShootdownAckSlot; 0] = [];
        assert!(all_acked_for_round_in_slice(&slots, 7, 0, &[]));
    }

    // ------------------------------------------------------------------------
    // SM7.A.3.D — fail-closed bounds enforcement
    // ------------------------------------------------------------------------

    #[test]
    #[should_panic(expected = "ack_round_in_slice: core_id 4 out of range")]
    fn ack_round_panics_on_out_of_range_core() {
        let slots = fresh_boot_slots();
        ack_round_in_slice(&slots, 4, 1);
    }

    #[test]
    #[should_panic(expected = "acked_gen_in_slice: core_id 7 out of range")]
    fn acked_gen_panics_on_out_of_range_core() {
        let slots = fresh_boot_slots();
        let _ = acked_gen_in_slice(&slots, 7);
    }

    // ------------------------------------------------------------------------
    // WS-SM SM7.B — round lock, bounded wait, SGI handler, online mask
    // ------------------------------------------------------------------------

    /// SM7.B.3: the reserved INTID is pinned to the Lean
    /// `SgiKind.tlbShootdownReq_intid` (= 1) and the gic.rs SGI
    /// reservation table.
    #[test]
    fn tlb_shootdown_req_intid_matches_lean() {
        assert_eq!(TLB_SHOOTDOWN_REQ_INTID, 1);
    }

    /// SM7.B.6: the Lean `shootdownWaitTimeoutTicks` (540 000) mirrors
    /// the HAL's established bounded-wait budget (10 ms at 54 MHz).
    #[test]
    fn wait_timeout_matches_wfe_default() {
        assert_eq!(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS, 540_000);
    }

    /// SM7.B.7: the global round lock is exclusive and re-acquirable —
    /// a second try-acquire fails while held, succeeds after release.
    /// (Serialised via the lock itself: this test owns the global for
    /// its scope because it is the only test touching it.)
    #[test]
    fn round_lock_try_acquire_exclusive_roundtrip() {
        assert!(round_lock_try_acquire(), "free lock must be acquirable");
        assert!(
            !round_lock_try_acquire(),
            "a held round lock must reject a second acquirer"
        );
        round_lock_release();
        assert!(round_lock_try_acquire(), "released lock re-acquirable");
        round_lock_release();
    }

    /// SM7.F.3 (PR #854 review P1): the runtime generation allocator is
    /// strictly increasing and starts at 1 — never the vacuously-
    /// satisfied 0, which a slot's initial `acked_gen` would already
    /// satisfy.
    /// **PR #854 review**: the wrap branch reaches the *system-wide*
    /// fail-closed halt, not a bare panic.
    ///
    /// Seeded one below wrap, so the next allocation returns 0. The halt
    /// is non-returning on both targets: on AArch64 `gic::halt_all`
    /// broadcasts `haltAll` and parks; on host `cpu::fatal_halt` panics
    /// (MMIO is a no-op off-target), which is what `should_panic`
    /// observes. The expected text is `fatal_halt`'s, so this fails if
    /// the branch ever reverts to the local `assert!` -- that carried a
    /// different message and, with no `#[panic_handler]` in the tree,
    /// no defined halt behaviour.
    #[test]
    #[should_panic(expected = "fail-closed halt reached")]
    fn round_generation_wrap_reaches_the_system_wide_halt() {
        let seq = AtomicU64::new(u64::MAX);
        let _ = allocate_round_generation_in(&seq);
    }

    /// The wrap guard does not fire on ordinary allocations -- the
    /// companion positive, so the test above cannot pass vacuously.
    #[test]
    fn round_generation_near_wrap_still_allocates() {
        let seq = AtomicU64::new(u64::MAX - 2);
        assert_eq!(allocate_round_generation_in(&seq), u64::MAX - 1);
        assert_eq!(allocate_round_generation_in(&seq), u64::MAX);
    }

    #[test]
    fn round_generation_allocator_is_strictly_increasing_from_one() {
        let seq = AtomicU64::new(0);
        let mut previous = 0u64;
        for expected in 1..=64u64 {
            let generation = allocate_round_generation_in(&seq);
            assert_eq!(
                generation, expected,
                "allocation {expected} must be dense and 1-based"
            );
            assert!(
                generation > previous,
                "allocations must be strictly increasing"
            );
            previous = generation;
        }
    }

    /// SM7.F.3 (PR #854 review P1) — the regression witness for the
    /// **premature**-acknowledgment hazard, the dual of the stale one
    /// pinned by `stale_acknowledgment_cannot_satisfy_a_later_round`.
    ///
    /// Two cores commit shootdown-bearing syscalls concurrently.  Core A
    /// commits first (model generation N) but stalls before the round
    /// lock; core B commits second (N+1), wins the lock, and runs its
    /// round to completion, so every target's `acked_gen` reaches B's
    /// generation.  Core A then takes the lock and waits.
    ///
    /// Keying A's wait on the *commit-time* model generation is what the
    /// review found: B's acks satisfy it instantly, so A returns from a
    /// round no target serviced — the operands still live in every
    /// remote TLB.  Allocating under the lock instead orders A after B,
    /// so A's wait correctly does NOT pass until A's own round is
    /// acknowledged.
    #[test]
    fn newer_round_acks_cannot_satisfy_an_older_unexecuted_round() {
        // Cores: A = 0 (the victim), B = 1, C = 2.  Three rounds are
        // needed, not two: a round's initiator never acknowledges its
        // own slot, so B's round alone always leaves B's slot behind and
        // A would block on it regardless.  It takes a THIRD round — one
        // whose targets include B — to lift every one of A's targets to
        // a generation at or above A's.  That is the steady state on a
        // busy system, where unmap-family syscalls are frequent.
        let (core_a, core_b, core_c) = (0usize, 1usize, 2usize);

        // --- The defect: keying the round on its commit-time generation.
        //
        // Commit order A(1) → B(2) → C(3); execution order B → C → A.
        let old_scheme = fresh_boot_slots();
        for target in [0usize, 2, 3] {
            ack_round_in_slice(&old_scheme, target, 2); // B's round
        }
        for target in [0usize, 1, 3] {
            ack_round_in_slice(&old_scheme, target, 3); // C's round
        }
        // A now runs its round, keyed on the generation it committed
        // with (1).  Every target has acknowledged some LATER round, so
        // the monotone test passes instantly — A returns believing its
        // operands are retired everywhere, while no core has so much as
        // read A's mailbox.
        assert!(
            all_acked_for_round_in_slice(&old_scheme, 1, core_a, &ALL_ONLINE),
            "regression witness: commit-time keying lets other rounds' acks \
             certify A's unexecuted round (the SMP-C4 under-invalidation)"
        );

        // --- The fix: allocate under the round lock, so allocation order
        // is execution order.  B and C ran first, so they hold 1 and 2
        // and A necessarily draws 3.
        let fixed = fresh_boot_slots();
        let seq = AtomicU64::new(0);
        let generation_b = allocate_round_generation_in(&seq);
        for target in [0usize, 2, 3] {
            ack_round_in_slice(&fixed, target, generation_b);
        }
        let generation_c = allocate_round_generation_in(&seq);
        for target in [0usize, 1, 3] {
            ack_round_in_slice(&fixed, target, generation_c);
        }
        let generation_a = allocate_round_generation_in(&seq);
        assert!(
            generation_a > generation_c && generation_c > generation_b,
            "lock-held allocation orders A after the rounds that ran first, \
             regardless of the commit order"
        );
        assert!(
            !all_acked_for_round_in_slice(&fixed, generation_a, core_a, &ALL_ONLINE),
            "SM7.F.3: no combination of earlier rounds' acks may certify a \
             round that no target has serviced"
        );

        // ...and it passes once A's own targets genuinely service it.
        for target in [core_b, core_c, 3] {
            ack_round_in_slice(&fixed, target, generation_a);
        }
        assert!(
            all_acked_for_round_in_slice(&fixed, generation_a, core_a, &ALL_ONLINE),
            "A's round completes once its own targets acknowledge it"
        );
    }

    /// SM7.B.5: an already-satisfied round satisfies the bounded wait
    /// immediately — the clock is never consulted past the start read.
    #[test]
    fn wait_immediate_when_all_acked() {
        let slots = fresh_boot_slots();
        let mut clock_reads = 0u32;
        // Generation 0 is vacuously satisfied at boot.
        let ok = wait_all_acked_bounded_in(&slots, 0, 0, &ALL_ONLINE, 10, || {
            clock_reads += 1;
            0
        });
        assert!(ok);
        assert_eq!(clock_reads, 1, "only the start-of-wait read happens");
    }

    /// **PR #854 review**: the round's captured online mask expands back
    /// to the snapshot it was folded from, so carrying it across the
    /// FFI loses nothing.
    #[test]
    fn online_mask_roundtrips_through_expansion() {
        for bits in 0u64..16 {
            let online = online_from_mask(bits);
            assert_eq!(
                online_mask_of(&online),
                bits,
                "mask {bits:#06b} must survive fold-then-expand"
            );
        }
    }

    /// **PR #854 review (regression witness)**: a core that becomes
    /// IRQ-serviceable *after* the round captured its target mask must
    /// not be waited on.
    ///
    /// The round poked exactly the cores in its own snapshot; a core
    /// absent from it received no SGI and so will never acknowledge.
    /// Before the fix the wait re-read `CORE_IRQ_READY`, picked that
    /// core up, and could only time out — and since v0.32.117 a timeout
    /// halts the machine. `bring_up_secondaries_inner` returns without
    /// waiting for secondaries to publish, so this is ordinary boot, not
    /// a contrived interleaving.
    #[test]
    fn a_core_outside_the_rounds_mask_is_not_waited_on() {
        let slots = fresh_boot_slots();
        // The round saw cores 0..2 online and poked 1 and 2; core 3 came
        // up afterwards and never got an SGI.
        let round_mask = online_mask_of(&[true, true, true, false]);
        ack_round_in_slice(&slots, 1, 7);
        ack_round_in_slice(&slots, 2, 7);

        let mut ticks = 0u64;
        assert!(
            wait_all_acked_bounded_in(&slots, 7, 0, &online_from_mask(round_mask), 1_000, || {
                ticks += 1;
                ticks
            }),
            "the round must complete on the targets it actually poked"
        );

        // The load-bearing negative: the pre-fix behaviour, i.e. waiting
        // against a fresh snapshot that now includes core 3.
        let mut ticks2 = 0u64;
        assert!(
            !wait_all_acked_bounded_in(&slots, 7, 0, &[true, true, true, true], 1_000, || {
                ticks2 += 1;
                ticks2
            }),
            "re-snapshotting picks up a core that was never poked, so the \
             round can only time out — the halt-on-boot regression"
        );
    }

    /// SM7.B.5: a late acknowledgment is observed, not misreported as
    /// a timeout — the poll re-checks after every clock read.
    #[test]
    fn wait_observes_late_ack() {
        let slots = fresh_boot_slots();
        ack_round_in_slice(&slots, 1, 1);
        ack_round_in_slice(&slots, 2, 1);
        let mut ticks = 0u64;
        let ok = wait_all_acked_bounded_in(&slots, 1, 0, &ALL_ONLINE, 1_000, || {
            ticks += 1;
            if ticks == 5 {
                // the last target acks mid-wait
                ack_round_in_slice(&slots, 3, 1);
            }
            ticks
        });
        assert!(ok, "the late ack must be observed within the budget");
    }

    /// SM7.B.6: a round that never completes is a genuine timeout —
    /// the wait returns false once the budget elapses.
    #[test]
    fn wait_times_out_when_never_acked() {
        let slots = fresh_boot_slots();
        let mut ticks = 0u64;
        let ok = wait_all_acked_bounded_in(&slots, 1, 0, &ALL_ONLINE, 100, || {
            ticks += 200; // jump straight past the budget
            ticks
        });
        assert!(!ok, "an unacknowledged round must time out");
    }

    /// SM7.B.6 (verdict exactness): an ack landing exactly at the
    /// deadline is still reported as success — the deadline path
    /// re-checks the slots before returning, so a completed round can
    /// never be reported as a timeout.
    #[test]
    fn wait_final_check_at_deadline() {
        let slots = fresh_boot_slots();
        let mut ticks = 0u64;
        let ok = wait_all_acked_bounded_in(&slots, 1, 0, &ALL_ONLINE, 100, || {
            ticks += 200;
            if ticks >= 200 {
                for c in 1..4 {
                    ack_round_in_slice(&slots, c, 1);
                }
            }
            ticks
        });
        assert!(ok, "acks at the deadline must be observed, not dropped");
    }

    /// SM7.B.6 (fail-closed): a *stale* acknowledgment does not rescue a
    /// round from timing out.  The regression companion of
    /// `stale_acknowledgment_cannot_satisfy_a_later_round`, at the
    /// wait-loop level: the pre-fix Boolean scheme would have exited
    /// successfully here with the target's TLB still stale.
    #[test]
    fn wait_times_out_on_stale_acknowledgments_only() {
        let slots = fresh_boot_slots();
        for c in 1..4usize {
            ack_round_in_slice(&slots, c, 1); // an EARLIER round
        }
        let mut ticks = 0u64;
        let ok = wait_all_acked_bounded_in(&slots, 2, 0, &ALL_ONLINE, 100, || {
            ticks += 200;
            ticks
        });
        assert!(
            !ok,
            "round 2 must time out while only round-1 acknowledgments exist"
        );
    }

    /// SM7.B.3: the handler acknowledges the executing core (host
    /// TPIDR stub = core 0) for the currently published generation.
    /// Global-path smoke only — the genuine outstanding → acknowledged
    /// transition is pinned by the `_in`-form tests below.
    #[test]
    fn handler_acks_executing_core() {
        tlb_shootdown_req_handler(TLB_SHOOTDOWN_REQ_INTID, 2);
        assert!(
            acked_gen(0) >= current_generation(),
            "the handler acknowledges at least the published generation"
        );
    }

    /// SM7.B.3 (test-hardening cut): the handler performs a GENUINE
    /// outstanding → acknowledged transition on its own core and
    /// touches no other core's slot — asserted on local state so a
    /// no-op handler cannot pass.
    #[test]
    fn handler_in_genuine_ack_transition_own_slot_only() {
        let mb = ShootdownOpMailbox::new();
        publish_round_ops_in(&mb, &[ShootdownOp::VMALLE1], 9);
        let slots = fresh_boot_slots();
        // Round 9 opened by core 3: cores 0..=2 genuinely outstanding.
        assert!(!all_acked_for_round_in_slice(&slots, 9, 3, &ALL_ONLINE));
        assert_eq!(
            acked_gen_in_slice(&slots, 0),
            0,
            "precondition: outstanding"
        );
        tlb_shootdown_req_service_in(&mb, &slots, 0);
        assert_eq!(
            acked_gen_in_slice(&slots, 0),
            9,
            "the handler must acknowledge the published generation"
        );
        assert_eq!(
            acked_gen_in_slice(&slots, 1),
            0,
            "the handler must not acknowledge on behalf of other targets"
        );
        assert_eq!(acked_gen_in_slice(&slots, 2), 0);
        assert_eq!(acked_gen_in_slice(&slots, 3), 0);
    }

    /// SM7.F.3: the handler acknowledges the generation it *serviced*,
    /// not an unrelated one — a handler running while the mailbox still
    /// holds an older round can only re-affirm that older round.
    #[test]
    fn handler_acknowledges_only_the_published_generation() {
        let mb = ShootdownOpMailbox::new();
        publish_round_ops_in(&mb, &[ShootdownOp::VMALLE1], 3);
        let slots = fresh_boot_slots();
        tlb_shootdown_req_service_in(&mb, &slots, 1);
        assert_eq!(acked_gen_in_slice(&slots, 1), 3);
        assert!(
            !all_acked_for_round_in_slice(&slots, 4, 0, &ALL_ONLINE),
            "servicing round 3 must not satisfy round 4"
        );
    }

    /// SM7.B.3 (test-hardening cut): an out-of-range executing-core id
    /// acknowledges NOTHING — the fail-closed arm leaves every slot
    /// untouched (the initiator then times out and panics diagnosably,
    /// rather than proceeding over a stale TLB).
    #[test]
    fn handler_in_out_of_range_acks_nothing() {
        let mb = ShootdownOpMailbox::new();
        publish_round_ops_in(&mb, &[ShootdownOp::VMALLE1], 5);
        let slots = fresh_boot_slots();
        tlb_shootdown_req_service_in(&mb, &slots, 7);
        for c in 0..4usize {
            assert_eq!(
                acked_gen_in_slice(&slots, c),
                0,
                "an out-of-range core id must not acknowledge any slot"
            );
        }
    }

    /// SM7.B.7 + SM7.F.3: the cooperative self-service arm discharges
    /// exactly this core's outstanding obligation, once.
    #[test]
    fn self_service_round_discharges_once() {
        let mb = ShootdownOpMailbox::new();
        publish_round_ops_in(&mb, &[ShootdownOp::VMALLE1], 6);
        let slots = fresh_boot_slots();
        assert!(
            self_service_round_in(&mb, &slots, 2),
            "an outstanding obligation must be serviced"
        );
        assert_eq!(acked_gen_in_slice(&slots, 2), 6);
        assert!(
            !self_service_round_in(&mb, &slots, 2),
            "a second call has nothing outstanding to service"
        );
        assert_eq!(acked_gen_in_slice(&slots, 2), 6);
    }

    /// SM7.F.3: self-service is fail-closed on an out-of-range core id.
    #[test]
    fn self_service_round_out_of_range_is_inert() {
        let mb = ShootdownOpMailbox::new();
        publish_round_ops_in(&mb, &[ShootdownOp::VMALLE1], 6);
        let slots = fresh_boot_slots();
        assert!(!self_service_round_in(&mb, &slots, 9));
        for c in 0..4usize {
            assert_eq!(acked_gen_in_slice(&slots, c), 0);
        }
    }

    // ------------------------------------------------------------------------
    // SM7.B debt (1) — per-descriptor operand mailbox
    // ------------------------------------------------------------------------

    /// SM7.B: a published operand list round-trips through the seqlock —
    /// the handler reads back EXACTLY what the initiator published.
    #[test]
    fn mailbox_publish_snapshot_roundtrip() {
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
        publish_round_ops_in(&mb, &ops, 11);
        let (snap, len, gen) = snapshot_round_ops_in(&mb).expect("stable snapshot");
        assert_eq!(len, 2);
        assert_eq!(gen, 11, "the snapshot carries the round's generation");
        assert_eq!(snap[0], ops[0]);
        assert_eq!(snap[1], ops[1]);
    }

    /// SM7.B: an in-progress publish (seqlock odd) is a torn read — the
    /// snapshot fails, so the handler falls back to the safe full flush.
    #[test]
    fn mailbox_torn_read_during_publish_is_none() {
        let mb = ShootdownOpMailbox::new();
        publish_begin_in(&mb); // seqlock now odd — no matching commit
        assert!(
            snapshot_round_ops_in(&mb).is_none(),
            "a publish-in-progress must read as torn (None)"
        );
        // A commit restores a readable snapshot.
        publish_slot_in(&mb, 0, ShootdownOp::VMALLE1);
        publish_commit_in(&mb, 1, 1);
        assert!(snapshot_round_ops_in(&mb).is_some());
    }

    /// SM7.B: an over-capacity commit collapses to a single `vmalle1`
    /// (the coalescing escape) rather than overflowing.
    #[test]
    fn mailbox_overflow_collapses_to_vmalle1() {
        let mb = ShootdownOpMailbox::new();
        publish_begin_in(&mb);
        publish_commit_in(&mb, SHOOTDOWN_OP_CAPACITY + 5, 1);
        let (snap, len, _gen) = snapshot_round_ops_in(&mb).expect("stable");
        assert_eq!(len, 1);
        assert_eq!(snap[0], ShootdownOp::VMALLE1);
    }

    /// SM7.B: retiring a per-descriptor round issues one local TLBI per
    /// operand (host: the `tlbi_*` are no-ops, so we assert the returned
    /// count) — the fidelity close vs the former blanket `vmalle1`.
    #[test]
    fn retire_per_descriptor_counts_operands() {
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
            2,
        );
        assert_eq!(
            retire_round_ops_in(&mb, 2),
            Some(2),
            "two operands ⇒ two per-descriptor local TLBIs"
        );
    }

    /// SM7.B: an empty round (nothing published) retires as a
    /// conservative local full flush (fallback, `None`).
    #[test]
    fn retire_empty_round_falls_back_to_full_flush() {
        let mb = ShootdownOpMailbox::new();
        publish_round_ops_in(&mb, &[], 1);
        assert_eq!(
            retire_round_ops_in(&mb, 1),
            None,
            "an empty round ⇒ conservative local vmalle1 fallback"
        );
    }

    /// SM7.B: a torn read retires as the conservative full flush — the
    /// handler can never under-invalidate on a bad mailbox snapshot.
    #[test]
    fn retire_torn_read_falls_back_to_full_flush() {
        let mb = ShootdownOpMailbox::new();
        publish_begin_in(&mb); // odd — torn
        assert_eq!(
            retire_round_ops_in(&mb, 1),
            None,
            "a torn read ⇒ conservative local vmalle1 fallback"
        );
    }

    /// SM7.B: a published `vmalle1` operand retires as a per-descriptor
    /// step (the coalesced-round case) — one local full flush, counted.
    #[test]
    fn retire_vmalle1_operand_is_one_step() {
        let mb = ShootdownOpMailbox::new();
        publish_round_ops_in(&mb, &[ShootdownOp::VMALLE1], 1);
        assert_eq!(retire_round_ops_in(&mb, 1), Some(1));

        // SM7.F.3: retiring against a DIFFERENT generation falls back to
        // the conservative local full flush — the snapshot's operands do
        // not discharge the generation the caller latched.
        assert_eq!(
            retire_round_ops_in(&mb, 2),
            None,
            "a generation mismatch ⇒ conservative local vmalle1 fallback"
        );
    }

    /// SM7.B conformance: the mailbox op-tag encoding matches the Lean
    /// `Architecture.TlbInvalidation.toOpTag` decode — every valid tag
    /// decodes to the expected typed operand, and an out-of-range tag
    /// decodes to `None` (fail-safe in the handler).
    #[test]
    fn op_tag_decode_conformance() {
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
    fn round_lock_mutex_stress() {
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
    fn handler_registration_and_dispatch() {
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
        assert!(acked_gen(0) >= current_generation());
    }

    /// SM7.B.2: the boot core is always in the online mask.
    #[test]
    fn online_mask_boot_core_always_set() {
        assert_eq!(online_mask() & 1, 1, "bit 0 (boot core) always set");
    }

    /// SM7.B.2 (PR #839 review P1): `online_mask_of` sets exactly the
    /// bits of the IRQ-serviceable snapshot — a released-but-not-yet-
    /// IRQ-ready secondary (its `CORE_IRQ_READY` slot still `false`) is
    /// excluded, so it is never a shootdown target.
    #[test]
    fn online_mask_of_excludes_not_irq_ready() {
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

    /// SM7.B.2 (PR #839 review P1): the wait mask and the SGI target
    /// mask are computed from the *same* IRQ-serviceable snapshot, so a
    /// not-IRQ-ready core is consistently excluded from BOTH — it can
    /// never be waited on for an SGI it was never sent, which is the
    /// hang the fix prevents.  Here we drive the shared wait predicate
    /// with the same snapshot shape `online_mask_of` would fold.
    #[test]
    fn wait_and_target_masks_agree_on_not_irq_ready() {
        let online = [true, true, false, false]; // cores 2,3 not serviceable
        let mask = online_mask_of(&online);
        assert_eq!(mask, 0b0011, "cores 2 and 3 excluded from the SGI mask");
        // The wait over the same snapshot never blocks on the excluded
        // cores, so the initiator is not hung on a core it never poked.
        let slots = fresh_boot_slots();
        assert!(
            !all_acked_for_round_in_slice(&slots, 1, 0, &online),
            "core 1 (serviceable, poked) is genuinely outstanding"
        );
        ack_round_in_slice(&slots, 1, 1);
        assert!(
            all_acked_for_round_in_slice(&slots, 1, 0, &online),
            "cores 2 and 3 (not serviceable ⇒ never poked) are never waited on"
        );
    }
}
