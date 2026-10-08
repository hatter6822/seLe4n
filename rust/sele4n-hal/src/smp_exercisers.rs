// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-BP BP8.4 — the Tier-4 in-image exercisers.**
//!
//! The drivers behind the four QEMU gates `scripts/test_qemu_smp_sgi_roundtrip.sh`,
//! `scripts/test_qemu_smp_kprintln_stress.sh`, `scripts/test_qemu_smp_shootdown.sh`
//! and `scripts/test_qemu_smp_shootdown_stress.sh`.  Until this module existed
//! every one of them SKIPped on every run: each looked for a banner in the
//! image with `strings`, found none, and reported that the driver was "not
//! yet wired".  The drivers are wired here, and they are wired **into a test
//! image only**: this module compiles under the `smp_exercisers` feature,
//! which the Raspberry Pi 5 image never carries — `scripts/build_rpi5_image.sh`
//! and the archive lane's image builds name their features, a Tier 3 negative
//! holds the feature out of every packaging command, and the exercisers'
//! window and SGI handler therefore exist in no image a board boots.
//!
//! What runs, on the boot core after Phase 7 (every declared PE serves the
//! kernel; the boot core has not yet handed itself to the idle wait, so a tick
//! taken here returns to the driver rather than replacing its frame —
//! `trap::IdleHandoffFlags`):
//!
//! * **The agent** ([`AgentSlot`], [`AGENTS`]): one command slot per core.
//!   The boot core writes a command and its argument, publishes a sequence
//!   number and sends the agent SGI ([`AGENT_SGI_INTID`]); the target's
//!   handler services the slot in IRQ context and publishes the result under
//!   the same sequence number.  The slot is the only channel the drivers use
//!   between cores, so every cross-core effect the gates observe was carried by
//!   a real SGI through the real GIC.
//! * **The window**: one page per core at [`window_address`], mapped through
//!   a level-2 and a level-3 table of this module's own hung off the kernel's
//!   boot level-1 table (`mmu::install_exerciser_window`).  Each core's page
//!   ping-pongs between two backing pages holding distinguishable patterns
//!   ([`pattern`]); a **remap** is break-before-make — the entry cleared, a
//!   shootdown round run, the entry rewritten — so a reader that still
//!   translates through the old entry reads the old pattern, which is the
//!   stale translation the SM7 protocol exists to remove.  The window hangs
//!   off level-0 entry 0's subtree deliberately: every thread's address space
//!   carries the kernel's entry 0 (`user_translation::kernel_window_entry`),
//!   so the window is translatable under whichever root a probing core has in
//!   `TTBR0_EL1`, and its entries are global, so a stale one survives the
//!   idle restore's `TTBR0_EL1` writes.
//! * **The round** ([`run_round_in`]): the initiator side of the shootdown
//!   protocol in exactly the order the Lean seam
//!   `SyscallDispatchEntry.completeShootdownRounds` runs it, and under the same
//!   bracket: [`run_round`] takes the kernel-entry lock first (`v0.36.38`), so
//!   a concurrent initiator waits on that lock — self-servicing the round in
//!   flight, as a core entering the kernel does — and no target sits in a
//!   kernel entry of its own through the wait.  Inside it: acquire the
//!   round lock, self-servicing the round in flight while spinning, under
//!   [`ROUND_LOCK_ACQUIRE_FUEL`]; allocate the generation under the lock;
//!   publish the operands; SGI the online targets; broadcast the
//!   invalidation; wait, bounded by the seam's own budget, for every target's
//!   acknowledgment; release.  A timeout keeps the lock and halts the system,
//!   as the seam's `haltFailClosed` does.  [`ROUNDS_IN_FLIGHT`] is the
//!   mutual-exclusion witness: a second initiator inside the critical section
//!   is reported as [`RoundOutcome::SerialisationBroken`], which is the
//!   "shootdown-round-serialisation break" WS-SM SM7 §8 names
//!   as a failure of SM7.
//!
//! **What QEMU can and cannot show.**  QEMU implements a broadcast `TLBI` as
//! a flush of every vCPU's TLB, so on QEMU the inner-shareable invalidation
//! alone removes a stale translation, and the SGI round's contribution — the
//! acknowledgment that every PE has retired its own view — is what the gates
//! observe through the acknowledged generations and the in-flight witness.
//! The stale-translation probe is decisive all the same: a round mutated to
//! invalidate **locally** (`tlbi_local`, no broadcast) leaves the other vCPUs'
//! TLBs untouched, and the probe then reads the old pattern.  The window's
//! entries are never read speculatively into a TLB between the break and the
//! make by these drivers themselves — no probe runs while a remap is in
//! flight — and a data abort on the window is an EL1-origin fault, which the
//! trap handler halts on rather than delivering, so a defect here fails the
//! gate rather than passing it.
//!
//! **What this module never does.**  It calls one Lean upcall only
//! (`lean_stats_component`, BP8.5, with IRQs masked and inside the kernel-entry
//! bracket), and its SGI handler touches no kernel state — it takes the
//! kernel-entry lock only to run a round under it, as the seam does; it never
//! enters the kernel while holding the round lock (the initiator runs its
//! round with IRQs masked, and a secondary runs one only inside its SGI
//! handler, where they already are), and it emits no local TLB invalidation
//! (`scripts/check_tlbi_broadcast_discipline.py` holds it to
//! `tlbi_for_sharing`).

use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};

use crate::shootdown::{ShootdownAckSlot, ShootdownOp, ShootdownOpMailbox};
use crate::smp::MAX_SECONDARY_CORES;

/// The PEs the exercisers drive: every core the HAL models.
pub const CORE_COUNT: usize = MAX_SECONDARY_CORES + 1;

/// The exercisers' SGI: the highest of the sixteen, above every INTID the
/// kernel reserves (`SgiKind`, WS-SM SM0.H: `0..=4`).
pub const AGENT_SGI_INTID: u8 = 15;
const _: () = assert!(AGENT_SGI_INTID > crate::gic::HALT_ALL_INTID);
const _: () = assert!(AGENT_SGI_INTID < crate::gic::MAX_SGI_INTID);

// ============================================================================
// The agent: one command slot per core
// ============================================================================

/// No command.
pub const COMMAND_IDLE: u32 = 0;
/// Print the SGI's arrival and send an [`COMMAND_ACK`] back to the boot core.
pub const COMMAND_PING: u32 = 1;
/// Print the acknowledgment (serviced on the boot core; `arg` names the core
/// that sent it).
pub const COMMAND_ACK: u32 = 2;
/// Print `arg` lines through `kprintln_core!`.
pub const COMMAND_STRESS: u32 = 3;
/// Read the window word at address `arg`.
pub const COMMAND_PROBE: u32 = 4;
/// Read every core's window page and compare it with generation `arg`'s
/// pattern; the result is the mask of cores whose page read stale.
pub const COMMAND_PROBE_ALL: u32 = 5;
/// Remap this core's own window page to generation `arg` through a shootdown
/// round; the result is the round's [`RoundOutcome::code`].
pub const COMMAND_ROUND: u32 = 6;

/// One core's command slot: one cache line, written by the issuer (the boot
/// core, or a secondary acknowledging a ping into slot 0) and by the servicing
/// core, never by two issuers at once — every driver awaits a slot's result
/// before it issues that slot's next command.
#[repr(C, align(64))]
pub struct AgentSlot {
    command: AtomicU32,
    arg: AtomicU64,
    result: AtomicU64,
    /// Advanced by the issuer with `Release` after `command` and `arg`.
    sequence_issued: AtomicU64,
    /// Set to the serviced sequence by the servicing core with `Release`
    /// after `result`.
    sequence_done: AtomicU64,
    _reserved: [u64; 3],
}

impl AgentSlot {
    /// An idle slot.
    pub const fn new() -> Self {
        Self {
            command: AtomicU32::new(COMMAND_IDLE),
            arg: AtomicU64::new(0),
            result: AtomicU64::new(0),
            sequence_issued: AtomicU64::new(0),
            sequence_done: AtomicU64::new(0),
            _reserved: [0; 3],
        }
    }
}

impl Default for AgentSlot {
    fn default() -> Self {
        Self::new()
    }
}

const _: () = assert!(core::mem::size_of::<AgentSlot>() == 64);
const _: () = assert!(core::mem::align_of::<AgentSlot>() == 64);

/// The slots, indexed by core id.
pub static AGENTS: [AgentSlot; CORE_COUNT] = [const { AgentSlot::new() }; CORE_COUNT];

/// Issue `command` with `arg` into `core`'s slot; returns the sequence number
/// the service will complete.  The command and its argument are published by
/// the `Release` store of the sequence, which the servicing core's `Acquire`
/// load pairs with.
pub fn agent_issue_in(slots: &[AgentSlot], core: usize, command: u32, arg: u64) -> u64 {
    let slot = &slots[core];
    slot.arg.store(arg, Ordering::Relaxed);
    slot.command.store(command, Ordering::Relaxed);
    let sequence = slot.sequence_issued.load(Ordering::Relaxed) + 1;
    slot.sequence_issued.store(sequence, Ordering::Release);
    sequence
}

/// Service `core`'s slot: run `execute` on the outstanding command, if any,
/// and publish its result under the issued sequence.  `false` when nothing
/// was outstanding — a spurious or repeated SGI services nothing twice.
pub fn agent_service_in(
    slots: &[AgentSlot],
    core: usize,
    execute: impl FnOnce(u32, u64) -> u64,
) -> bool {
    let slot = &slots[core];
    let issued = slot.sequence_issued.load(Ordering::Acquire);
    if issued == slot.sequence_done.load(Ordering::Relaxed) {
        return false;
    }
    let command = slot.command.load(Ordering::Relaxed);
    let arg = slot.arg.load(Ordering::Relaxed);
    let result = execute(command, arg);
    slot.result.store(result, Ordering::Relaxed);
    slot.sequence_done.store(issued, Ordering::Release);
    true
}

/// Wait, bounded by `timeout_ticks` of the clock `now`, for `core`'s slot to
/// have completed `sequence`; the result, or `None` on timeout.  A counted
/// spin with one final read at the deadline, the shape every bounded wait in
/// this tree takes (`shootdown::wait_all_acked_bounded_in`): a result landing
/// between the last poll and the deadline read is never reported as a
/// timeout.
pub fn agent_await_in<C: FnMut() -> u64>(
    slots: &[AgentSlot],
    core: usize,
    sequence: u64,
    timeout_ticks: u64,
    mut now: C,
) -> Option<u64> {
    let slot = &slots[core];
    let done = || slot.sequence_done.load(Ordering::Acquire) >= sequence;
    let start = now();
    loop {
        if done() {
            return Some(slot.result.load(Ordering::Relaxed));
        }
        if now().saturating_sub(start) >= timeout_ticks {
            return done().then(|| slot.result.load(Ordering::Relaxed));
        }
        core::hint::spin_loop();
    }
}

// ============================================================================
// The window: one page per core, remapped through shootdown rounds
// ============================================================================

const TABLE_ENTRIES: usize = 512;
const PAGE_WORDS: usize = 512;
const PAGE_BYTES: u64 = 4096;

/// Where the window starts: the first byte of the level-1 entry
/// `mmu::install_exerciser_window` hangs this module's tables off.
pub const WINDOW_BASE: u64 = crate::mmu::EXERCISER_WINDOW_BASE;

/// The address of `core`'s window page.
#[must_use]
pub const fn window_address(core: usize) -> u64 {
    WINDOW_BASE + core as u64 * PAGE_BYTES
}

/// The word `core`'s page holds at `generation`: the core in bits `[16, 24)`
/// and the generation's parity in bit 0, under a tag no boot pattern carries.
/// Two generations of one core differ, and so do two cores at one generation;
/// a page's content is fixed for the life of the image (the generation only
/// selects which of the two backing pages the window shows), so a stale
/// translation reads the previous generation's parity, never a torn word.
#[must_use]
pub const fn pattern(core: usize, generation: u64) -> u64 {
    0x5E4E_C0DE_0000_0000 | ((core as u64) << 16) | (generation & 1)
}

/// The backing page `core`'s window shows at `generation`.
#[must_use]
pub const fn backing_page(core: usize, generation: u64) -> usize {
    core * 2 + (generation & 1) as usize
}

/// This module's own translation tables: a level-2 table whose entry 0 names
/// the level-3 table, whose entry `c` names core `c`'s backing page.  Both are
/// 4 KiB tables at 4 KiB alignment, as `TTBR`-reachable tables must be.
#[repr(C, align(4096))]
pub struct WindowTables {
    l2: [u64; TABLE_ENTRIES],
    l3: [u64; TABLE_ENTRIES],
}

/// Two backing pages per core.
#[repr(C, align(4096))]
pub struct BackingPages([[u64; PAGE_WORDS]; 2 * CORE_COUNT]);

/// Interior-mutable storage for the tables and pages.
///
/// Every Rust access to the contents is a volatile access through a raw
/// pointer, never a reference.  The boot core fills every page and every
/// entry at the install, before any other core reaches the window; after it
/// the only Rust writes are a core's own level-3 entry, written by the page's
/// owner alone — on the boot core for its page, in a secondary's own agent
/// handler for that secondary's (`COMMAND_ROUND`) — so no two cores write one
/// location.  Every other access is the hardware's: the translation-table
/// walker reading the tables, and a core's probe reading a page through the
/// window alias, a volatile load through an address the walker resolves.
pub struct ExerciserCell<T>(UnsafeCell<T>);

// SAFETY: see the type's docstring — no Rust reference to the contents is
// ever formed, every write is a volatile write to a location one core owns
// (the install's, before any other core touches the window; afterwards a
// core's own level-3 entry), so no two cores write one location and no
// reference can alias a write.
unsafe impl<T> Sync for ExerciserCell<T> {}

static TABLES: ExerciserCell<WindowTables> = ExerciserCell(UnsafeCell::new(WindowTables {
    l2: [0; TABLE_ENTRIES],
    l3: [0; TABLE_ENTRIES],
}));

static PAGES: ExerciserCell<BackingPages> = ExerciserCell(UnsafeCell::new(BackingPages(
    [[0; PAGE_WORDS]; 2 * CORE_COUNT],
)));

/// The level-2 table's first entry.
fn level2_table_pointer() -> *mut u64 {
    TABLES.0.get().cast::<u64>()
}

/// The level-3 table's first entry — `WindowTables` is `#[repr(C)]`, so the
/// level-3 table follows the level-2 table's 512 entries.
fn level3_table_pointer() -> *mut u64 {
    level2_table_pointer().wrapping_add(TABLE_ENTRIES)
}

/// The first word of backing page `index`.
fn backing_page_pointer(index: usize) -> *mut u64 {
    PAGES.0.get().cast::<u64>().wrapping_add(index * PAGE_WORDS)
}

/// The physical address of an object of the kernel image: the kernel window
/// is an identity map (`mmu::boot_mapping_for`).
fn physical_address<T>(pointer: *mut T) -> u64 {
    pointer as usize as u64
}

/// Write `core`'s level-3 entry and publish it to the walker with the
/// ARMv8 page-table-update bracket (`dsb ishst; dc cvac; dsb ish; isb`).
fn store_window_entry(core: usize, descriptor: u64) {
    let entry = level3_table_pointer().wrapping_add(core);
    // SAFETY: `entry` is `core`'s own level-3 entry inside `TABLES`, at an
    // aligned `u64`, written by the page's owner alone once the install is
    // done (`ExerciserCell`'s discipline); the write is volatile because the
    // walker reads the table behind the compiler's back.
    unsafe { entry.write_volatile(descriptor) };
    crate::barriers::BarrierKind::emit_armv8_page_table_update(physical_address(entry));
}

/// Read one word of the window through the hardware translation of
/// `address` — a `TLB` hit here is exactly what a shootdown round must have
/// removed.
fn read_window_word(address: u64) -> u64 {
    let pointer = address as usize as *const u64;
    // SAFETY: `address` is a window address `install_window` mapped, readable
    // at EL1 for the life of the image once installed; the load is volatile
    // because the translation, not the compiler, decides which backing page
    // it reads.
    unsafe { pointer.read_volatile() }
}

static WINDOW_INSTALLED: AtomicU32 = AtomicU32::new(0);

/// Fill the backing pages with their patterns, map every core's page at its
/// generation-0 backing page and hang the tables off the boot map.  Idempotent.
fn install_window() -> Result<(), crate::mmu::ExerciserWindowRefusal> {
    if WINDOW_INSTALLED.load(Ordering::Acquire) != 0 {
        return Ok(());
    }
    for core in 0..CORE_COUNT {
        for parity in 0..2u64 {
            let page = backing_page_pointer(backing_page(core, parity));
            let value = pattern(core, parity);
            for word in 0..PAGE_WORDS {
                // SAFETY: inside `PAGES`, a static this core alone writes, at an
                // aligned `u64`; volatile because other cores read the page
                // through the window alias.
                unsafe { page.wrapping_add(word).write_volatile(value) };
            }
        }
    }
    for core in 0..CORE_COUNT {
        let page = backing_page_pointer(backing_page(core, 0));
        store_window_entry(
            core,
            crate::mmu::exerciser_page_descriptor(physical_address(page)),
        );
    }
    let l2 = level2_table_pointer();
    // SAFETY: entry 0 of `TABLES`' level-2 table, written by this core alone;
    // volatile for the walker's sake.
    unsafe {
        l2.write_volatile(crate::mmu::exerciser_table_descriptor(physical_address(
            level3_table_pointer(),
        )));
    }
    // Every table entry is visible to the walker before the level-1 entry
    // makes the subtree reachable.
    crate::barriers::dsb_ish();
    crate::mmu::install_exerciser_window(physical_address(l2))?;
    WINDOW_INSTALLED.store(1, Ordering::Release);
    Ok(())
}

/// The invalidation a remap of `core`'s page broadcasts: the page, at ASID 0
/// — the window's entries are global, and a `VAE1` invalidation of a global
/// entry ignores the ASID (ARM ARM D8.14).
#[must_use]
pub fn window_operand(core: usize) -> ShootdownOp {
    ShootdownOp {
        op_tag: 1,
        asid: 0,
        vaddr: window_address(core),
    }
}

// ============================================================================
// The round: the initiator side of the shootdown protocol
// ============================================================================

/// How a round ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RoundOutcome {
    /// Every online target acknowledged the round's generation; the lock is
    /// released.
    Complete,
    /// The round lock was not acquired within [`ROUND_LOCK_ACQUIRE_FUEL`]
    /// attempts; nothing was published and the lock was not touched.
    LockWedged,
    /// Another initiator was inside the round-lock critical section when this
    /// one entered it: the lock does not serialise rounds.  Nothing was
    /// published; the lock is released.
    SerialisationBroken,
    /// A target did not acknowledge within the wait budget.  The lock is
    /// **kept**, as the Lean seam keeps it before `haltFailClosed`.
    TimedOut,
}

impl RoundOutcome {
    /// The outcome as an agent result.
    #[must_use]
    pub const fn code(self) -> u64 {
        match self {
            RoundOutcome::Complete => 0,
            RoundOutcome::LockWedged => 1,
            RoundOutcome::SerialisationBroken => 2,
            RoundOutcome::TimedOut => 3,
        }
    }

    /// The inverse of [`RoundOutcome::code`].
    #[must_use]
    pub const fn from_code(code: u64) -> Option<Self> {
        match code {
            0 => Some(RoundOutcome::Complete),
            1 => Some(RoundOutcome::LockWedged),
            2 => Some(RoundOutcome::SerialisationBroken),
            3 => Some(RoundOutcome::TimedOut),
            _ => None,
        }
    }
}

/// How many acquisition attempts the initiator makes before it reports the
/// lock wedged — the Lean seam's `shootdownRoundLockAcquireFuel`, which a
/// Tier 3 anchor holds equal to this literal.
pub const ROUND_LOCK_ACQUIRE_FUEL: u64 = 1_000_000;

/// How long the initiator waits for the acknowledgments — the Lean seam's
/// `Architecture.shootdownWaitTimeoutTicks`, which is
/// `cpu::WFE_DEFAULT_TIMEOUT_TICKS` on both sides.
pub const ROUND_WAIT_TIMEOUT_TICKS: u64 = crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS;

/// The protocol state a round runs over: the production statics, or a test's
/// own cells.
pub struct RoundProtocol<'a> {
    /// The round lock (`shootdown::SHOOTDOWN_ROUND_LOCK`).
    pub lock: &'a AtomicUsize,
    /// The generation counter (`shootdown::SHOOTDOWN_ROUND_SEQ`).
    pub generations: &'a AtomicU64,
    /// The operand mailbox (`shootdown::SHOOTDOWN_OPS`).
    pub mailbox: &'a ShootdownOpMailbox,
    /// The acknowledgment slots (`shootdown::SHOOTDOWN_ACK`).
    pub slots: &'a [ShootdownAckSlot],
    /// The mutual-exclusion witness ([`ROUNDS_IN_FLIGHT`]).
    pub in_flight: &'a AtomicU32,
    /// How many acquisition attempts before the lock is reported wedged
    /// ([`ROUND_LOCK_ACQUIRE_FUEL`] on the production protocol).
    pub acquire_fuel: u64,
}

/// What a round does to the hardware, injected so the round is testable on
/// the host.
pub struct RoundHardware<S, T, C> {
    /// Send the `.tlbShootdownReq` SGI to one target core.
    pub send_request: S,
    /// Broadcast the invalidation from the initiator.
    pub broadcast_invalidate: T,
    /// The clock the wait is bounded by.
    pub now: C,
}

/// How many initiators are inside the round-lock critical section.  The lock
/// serialises rounds exactly when this never exceeds one.
pub static ROUNDS_IN_FLIGHT: AtomicU32 = AtomicU32::new(0);

/// Run one round as `initiator` over `protocol`, targeting every core `online`
/// names but the initiator, in the order the Lean seam runs it.  Returns the
/// generation the round used (0 when none was allocated) and its outcome.
pub fn run_round_in<S, T, C>(
    protocol: &RoundProtocol<'_>,
    online: &[bool],
    initiator: usize,
    op: ShootdownOp,
    wait_timeout_ticks: u64,
    hardware: &mut RoundHardware<S, T, C>,
) -> (u64, RoundOutcome)
where
    S: FnMut(usize),
    T: FnMut(ShootdownOp),
    C: FnMut() -> u64,
{
    // 1. Acquire, self-servicing the round in flight while spinning — the
    //    cooperative acquire of SM7.B.7, under the protocol's fuel.
    let mut fuel = protocol.acquire_fuel;
    while !crate::shootdown::round_lock_try_acquire_in(protocol.lock, initiator) {
        crate::shootdown::self_service_round_in(protocol.mailbox, protocol.slots, initiator);
        fuel -= 1;
        if fuel == 0 {
            return (0, RoundOutcome::LockWedged);
        }
        core::hint::spin_loop();
    }
    // The witness: nobody else may be inside.
    if protocol.in_flight.fetch_add(1, Ordering::AcqRel) != 0 {
        protocol.in_flight.fetch_sub(1, Ordering::AcqRel);
        crate::shootdown::round_lock_release_in(protocol.lock);
        return (0, RoundOutcome::SerialisationBroken);
    }
    // 2. The generation, allocated under the lock.
    let generation = crate::shootdown::allocate_round_generation_in(protocol.generations);
    // 3. The operands, published under that generation.
    crate::shootdown::publish_round_ops_in(protocol.mailbox, &[op], generation);
    // 4. The request, to every online target but the initiator.
    for (target, &is_online) in online.iter().enumerate() {
        if is_online && target != initiator {
            (hardware.send_request)(target);
        }
    }
    // 5. The initiator's own broadcast invalidation.
    (hardware.broadcast_invalidate)(op);
    // 6. The bounded wait.  A timeout keeps the lock: the seam halts here.
    let acknowledged = crate::shootdown::wait_all_acked_bounded_in(
        protocol.slots,
        generation,
        initiator,
        online,
        wait_timeout_ticks,
        &mut hardware.now,
    );
    if !acknowledged {
        return (generation, RoundOutcome::TimedOut);
    }
    // 7. Release.
    protocol.in_flight.fetch_sub(1, Ordering::AcqRel);
    crate::shootdown::round_lock_release_in(protocol.lock);
    (generation, RoundOutcome::Complete)
}

/// The production protocol state.
#[must_use]
pub fn production_protocol() -> RoundProtocol<'static> {
    RoundProtocol {
        lock: &crate::shootdown::SHOOTDOWN_ROUND_LOCK,
        generations: &crate::shootdown::SHOOTDOWN_ROUND_SEQ,
        mailbox: &crate::shootdown::SHOOTDOWN_OPS,
        slots: &crate::shootdown::SHOOTDOWN_ACK,
        in_flight: &ROUNDS_IN_FLIGHT,
        acquire_fuel: ROUND_LOCK_ACQUIRE_FUEL,
    }
}

/// Run one round on the hardware as `initiator`, with IRQs masked for its
/// duration: an initiator that took an interrupt while holding the round
/// lock would enter the kernel holding it, which the kernel-entry tripwire
/// halts on.  A timeout halts the system here, with the lock still held and
/// IRQs still masked — the seam's own posture — after naming the round.
///
/// **Inside the kernel-entry bracket, as the seam runs it** (`v0.36.38`).  The
/// production seam runs every round inside `with_kernel_entry`, so no target
/// can be inside a kernel entry of its own while the initiator waits: a target
/// that wants one spins on the entry lock, and that spin self-services the
/// round.  Running the round outside the bracket let a target sit in a Lean
/// timer tick — IRQs masked, the entry lock held, over a million instructions
/// under `-icount` — through the whole bounded wait, which timed round 14 out
/// in CI run 36512379153 with the target's tick finishing just after.  That
/// was a posture only the exerciser had; the bracket makes it the seam's.
fn run_round(initiator: usize, op: ShootdownOp) -> (u64, RoundOutcome) {
    let online = crate::shootdown::online_from_mask(crate::shootdown::online_mask());
    let mut hardware = RoundHardware {
        send_request: |target: usize| {
            crate::gic::send_sgi(1u8 << target, crate::shootdown::TLB_SHOOTDOWN_REQ_INTID);
        },
        broadcast_invalidate: |op: ShootdownOp| {
            // An operand this module did not build decodes to the full flush,
            // a superset — the request handler's own fallback.
            let invalidation = crate::tlb::decode_tlb_invalidation(op.op_tag, op.asid, op.vaddr)
                .unwrap_or(crate::tlb::TlbInvalidation::Vmalle1);
            crate::tlb::tlbi_for_sharing(crate::tlb::SharingDomain::Inner, invalidation);
        },
        now: crate::timer::read_counter,
    };
    let saved = crate::interrupts::disable_interrupts();
    let (generation, outcome) = crate::kernel_entry::with_kernel_entry(initiator, || {
        let (generation, outcome) = run_round_in(
            &production_protocol(),
            &online,
            initiator,
            op,
            ROUND_WAIT_TIMEOUT_TICKS,
            &mut hardware,
        );
        if outcome == RoundOutcome::TimedOut {
            let acknowledged: [u64; CORE_COUNT] = core::array::from_fn(crate::shootdown::acked_gen);
            crate::kprintln!(
                "[smp-test] FATAL: shootdown round {generation} from core {initiator} timed out \
                 after {ROUND_WAIT_TIMEOUT_TICKS} ticks; acknowledged generations \
                 {acknowledged:?}, online {online:?}; halting fail-closed system-wide"
            );
            crate::gic::halt_all();
        }
        (generation, outcome)
    });
    crate::interrupts::restore_interrupts(saved);
    (generation, outcome)
}

/// Remap `core`'s window page to `generation`'s backing page,
/// break-before-make: clear the entry, run a round for the page, write the
/// new entry.
fn remap_and_round(core: usize, generation: u64) -> (u64, RoundOutcome) {
    store_window_entry(core, 0);
    let outcome = run_round(core, window_operand(core));
    let page = backing_page_pointer(backing_page(core, generation));
    store_window_entry(
        core,
        crate::mmu::exerciser_page_descriptor(physical_address(page)),
    );
    outcome
}

/// Print a round's outcome under `label`; `true` when it completed.
fn report_round(
    label: &str,
    core: usize,
    generation: u64,
    round: u64,
    outcome: RoundOutcome,
) -> bool {
    match outcome {
        RoundOutcome::Complete => {
            crate::kprintln!(
                "[smp-test] {label}: core {core} generation {generation}: round {round} complete"
            );
            true
        }
        RoundOutcome::LockWedged => {
            crate::kprintln!(
                "[smp-test] FAIL: {label}: core {core} generation {generation}: the round lock was \
                 not acquired within {ROUND_LOCK_ACQUIRE_FUEL} attempts"
            );
            false
        }
        RoundOutcome::SerialisationBroken => {
            crate::kprintln!(
                "[smp-test] FAIL: {label}: core {core} generation {generation}: a second initiator \
                 was inside the round-lock critical section"
            );
            false
        }
        // `run_round` halts on a timeout; this arm is unreachable from it.
        RoundOutcome::TimedOut => {
            crate::kprintln!(
                "[smp-test] FAIL: {label}: core {core} generation {generation}: round {round} timed out"
            );
            false
        }
    }
}

// ============================================================================
// The agent's handler: what a core does with a command
// ============================================================================

/// Read every core's window page on `core` and compare each with
/// `generation`'s pattern; the mask of cores whose page read stale.
fn probe_all(core: usize, generation: u64) -> u64 {
    let mut stale = 0u64;
    for owner in 0..CORE_COUNT {
        let read = read_window_word(window_address(owner));
        let expected = pattern(owner, generation);
        if read != expected {
            stale |= 1 << owner;
            crate::kprintln!(
                "[smp-test] tlb-shootdown-stress: stale translation on core {core} for core \
                 {owner}'s page: read {read:#x}, expected {expected:#x}"
            );
        }
    }
    stale
}

/// Execute `command` on `core`, where `source_cpu` is the GIC's attribution
/// of the SGI that carried it.
fn execute(core: usize, source_cpu: u8, command: u32, arg: u64) -> u64 {
    match command {
        COMMAND_PING => {
            crate::kprintln!(
                "[smp-test] core {core}: received SGI {AGENT_SGI_INTID} from core {source_cpu}, \
                 sending ack"
            );
            let _sequence = agent_issue_in(&AGENTS, 0, COMMAND_ACK, core as u64);
            crate::gic::send_sgi(1, AGENT_SGI_INTID);
            1
        }
        COMMAND_ACK => {
            crate::kprintln!(
                "[smp-test] core {core}: ack received from core {arg} (SGI source {source_cpu})"
            );
            1
        }
        COMMAND_STRESS => {
            for line in 0..arg {
                crate::kprintln_core!("stress iter {line}");
            }
            arg
        }
        COMMAND_PROBE => read_window_word(arg),
        COMMAND_PROBE_ALL => probe_all(core, arg),
        COMMAND_ROUND => {
            let (round, outcome) = remap_and_round(core, arg);
            report_round("tlb-shootdown-stress", core, arg, round, outcome);
            outcome.code()
        }
        _ => u64::MAX,
    }
}

/// The agent SGI's handler: service the executing core's slot.
fn agent_sgi_handler(_intid: u8, source_cpu: u8) {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    if core >= CORE_COUNT {
        return;
    }
    let _serviced = agent_service_in(&AGENTS, core, |command, arg| {
        execute(core, source_cpu, command, arg)
    });
}

/// Register the agent SGI's handler at [`AGENT_SGI_INTID`].
///
/// # Safety
///
/// `gic::register_sgi_handler`'s contract: boot, on the primary core alone,
/// with IRQs masked, before any secondary is released — the SGI handler table
/// is write-once-at-boot and unsynchronised.
pub unsafe fn register_agent_handler() {
    // SAFETY: this function's own `# Safety` contract is exactly
    // `register_sgi_handler`'s, and the boot's Phase 3 is where it holds.
    unsafe {
        crate::gic::register_sgi_handler(AGENT_SGI_INTID, agent_sgi_handler);
    }
}

// ============================================================================
// The drivers, run on the boot core
// ============================================================================

/// How long the boot core waits for a command: two seconds of the counter.
fn command_timeout_ticks() -> u64 {
    u64::from(crate::timer::read_frequency()) * 2
}

/// Issue `code` with `arg` to `core`, poke it, and wait for its result.
fn command(core: usize, code: u32, arg: u64) -> Option<u64> {
    let sequence = agent_issue_in(&AGENTS, core, code, arg);
    crate::gic::send_sgi(1u8 << core, AGENT_SGI_INTID);
    agent_await_in(
        &AGENTS,
        core,
        sequence,
        command_timeout_ticks(),
        crate::timer::read_counter,
    )
}

/// Issue `code` with `arg` to every secondary at once, run `own` as the boot
/// core's share, and collect every result by core.
fn command_all(code: u32, arg: u64, own: impl FnOnce() -> u64) -> [Option<u64>; CORE_COUNT] {
    let mut sequences = [0u64; CORE_COUNT];
    for (core, sequence) in sequences.iter_mut().enumerate().skip(1) {
        *sequence = agent_issue_in(&AGENTS, core, code, arg);
        crate::gic::send_sgi(1u8 << core, AGENT_SGI_INTID);
    }
    let mut results = [None; CORE_COUNT];
    results[0] = Some(own());
    for (core, sequence) in sequences.iter().enumerate().skip(1) {
        results[core] = agent_await_in(
            &AGENTS,
            core,
            *sequence,
            command_timeout_ticks(),
            crate::timer::read_counter,
        );
    }
    results
}

/// `test_qemu_smp_sgi_roundtrip.sh`: the boot core pings each secondary over
/// the agent SGI, the secondary answers with an SGI of its own, and the
/// per-core SGI counters move on both ends.
fn sgi_round_trip() -> bool {
    let mut pass = true;
    for core in 1..CORE_COUNT {
        let target_sgis = crate::per_cpu_stats::sgi_count_for(core);
        let boot_sgis = crate::per_cpu_stats::sgi_count_for(0);
        let acks_before = AGENTS[0].sequence_done.load(Ordering::Acquire);
        crate::kprintln!(
            "[smp-test] sgi-round-trip: core 0 sending SGI {AGENT_SGI_INTID} to core {core}"
        );
        let ponged = command(core, COMMAND_PING, 0) == Some(1);
        // The ack is serviced on this core, in its own agent handler.
        let acked = agent_await_in(
            &AGENTS,
            0,
            acks_before + 1,
            command_timeout_ticks(),
            crate::timer::read_counter,
        )
        .is_some();
        let target_delta = crate::per_cpu_stats::sgi_count_for(core).saturating_sub(target_sgis);
        let boot_delta = crate::per_cpu_stats::sgi_count_for(0).saturating_sub(boot_sgis);
        crate::kprintln!(
            "[smp-test] sgi-round-trip: core {core} SGI count +{target_delta}, core 0 SGI count \
             +{boot_delta}"
        );
        if !(ponged && acked && target_delta >= 1 && boot_delta >= 1) {
            pass = false;
            crate::kprintln!(
                "[smp-test] FAIL: sgi-round-trip: core {core}: ponged {ponged}, acked {acked}"
            );
        }
    }
    if pass {
        crate::kprintln!("[smp-test] SGI round-trip complete");
    }
    pass
}

/// How many lines each core prints under the console stress.
pub const STRESS_LINES: u64 = 32;

/// `test_qemu_smp_kprintln_stress.sh`: every core prints [`STRESS_LINES`]
/// lines at once through `kprintln_core!`; the gate requires every line whole.
fn kprintln_stress() -> bool {
    let results = command_all(COMMAND_STRESS, STRESS_LINES, || {
        for line in 0..STRESS_LINES {
            crate::kprintln_core!("stress iter {line}");
        }
        STRESS_LINES
    });
    let pass = results.iter().all(|result| *result == Some(STRESS_LINES));
    if pass {
        crate::kprintln!("[smp-test] kprintln-stress: every core printed {STRESS_LINES} lines");
    } else {
        crate::kprintln!("[smp-test] FAIL: kprintln-stress: results by core {results:?}");
    }
    pass
}

/// `test_qemu_smp_shootdown.sh`: core 1 translates core 0's page, core 0
/// remaps it through a round, and core 1's next read sees the new page.
fn shootdown_round_trip() -> bool {
    let primed = command(1, COMMAND_PROBE, window_address(0));
    if primed != Some(pattern(0, 0)) {
        crate::kprintln!(
            "[smp-test] FAIL: tlb-shootdown: core 1 read {primed:?} before the remap, expected {:#x}",
            pattern(0, 0)
        );
        return false;
    }
    let (round, outcome) = remap_and_round(0, 1);
    if !report_round("tlb-shootdown", 0, 1, round, outcome) {
        return false;
    }
    let acknowledged: [u64; CORE_COUNT] = core::array::from_fn(crate::shootdown::acked_gen);
    crate::kprintln!(
        "[smp-test] tlb-shootdown: round generation {round} acknowledged: core 1 at {}, core 2 \
         at {}, core 3 at {}",
        acknowledged[1],
        acknowledged[2],
        acknowledged[3]
    );
    let after = command(1, COMMAND_PROBE, window_address(0));
    if after == Some(pattern(0, 1)) {
        crate::kprintln!("[smp-test] tlb-shootdown: stale translation removed");
        true
    } else {
        crate::kprintln!(
            "[smp-test] FAIL: tlb-shootdown: stale translation on core 1: read {after:?}, \
             expected {:#x}",
            pattern(0, 1)
        );
        false
    }
}

/// How many generations the stress runs; every core remaps its own page and
/// initiates a round at each, so four initiators contend for the round lock
/// at once.
pub const STRESS_ROUNDS: u64 = 8;

/// The first stress generation: even, so every core's page — core 0's is at
/// generation 1 after [`shootdown_round_trip`] — is brought to the same
/// parity by the first remap.
const STRESS_FIRST_GENERATION: u64 = 2;

/// `test_qemu_smp_shootdown_stress.sh`: [`STRESS_ROUNDS`] generations of
/// four concurrent initiators, each followed by every core reading every
/// page.
fn shootdown_stress() -> bool {
    let mut pass = true;
    for generation in STRESS_FIRST_GENERATION..STRESS_FIRST_GENERATION + STRESS_ROUNDS {
        let rounds = command_all(COMMAND_ROUND, generation, || {
            let (round, outcome) = remap_and_round(0, generation);
            report_round("tlb-shootdown-stress", 0, generation, round, outcome);
            outcome.code()
        });
        for (core, result) in rounds.iter().enumerate() {
            if *result != Some(RoundOutcome::Complete.code()) {
                pass = false;
                crate::kprintln!(
                    "[smp-test] FAIL: tlb-shootdown-stress: core {core} generation \
                     {generation}: round result {result:?}"
                );
            }
        }
        let probes = command_all(COMMAND_PROBE_ALL, generation, || probe_all(0, generation));
        for (core, result) in probes.iter().enumerate() {
            if *result != Some(0) {
                pass = false;
                crate::kprintln!(
                    "[smp-test] FAIL: tlb-shootdown-stress: core {core} generation \
                     {generation}: stale mask {result:?}"
                );
            }
        }
    }
    if pass {
        crate::kprintln!(
            "[smp-test] tlb-shootdown-stress: all cores completed ({STRESS_ROUNDS} generations, {} \
             rounds)",
            STRESS_ROUNDS * CORE_COUNT as u64
        );
    }
    pass
}

/// How many drivers this image runs: the four of BP8.4 on every image, and
/// the per-core counter check on the image that links the kernel (BP8.5).
const DRIVER_COUNT: u32 = if cfg!(feature = "hw_target") { 5 } else { 4 };

/// How long the boot core waits for every PE to become IRQ-serviceable: one
/// second of the counter.
fn serviceable_wait_ticks() -> u64 {
    u64::from(crate::timer::read_frequency())
}

/// Run the drivers on the boot core, after Phase 7.  Every PE must be
/// IRQ-serviceable (the shootdown protocol's own online set); a machine with
/// fewer reports that and runs nothing, which is what a gate reads as NOT RUN.
pub fn run_on_boot_core(smp_enabled: bool) {
    crate::kprintln!("[smp-test] exercisers: test image; the Tier-4 in-image drivers follow");
    if !smp_enabled {
        crate::kprintln!("[smp-test] exercisers: not run (SMP disabled by cmdline)");
        return;
    }
    let serviceable = crate::smp::serving_core_count_within_in(
        CORE_COUNT as u32,
        serviceable_wait_ticks(),
        crate::timer::read_counter,
        |core| crate::shootdown::online_from_mask(crate::shootdown::online_mask())[core],
    );
    if serviceable as usize != CORE_COUNT {
        crate::kprintln!(
            "[smp-test] exercisers: not run ({serviceable} of {CORE_COUNT} PEs IRQ-serviceable)"
        );
        return;
    }
    if let Err(refusal) = install_window() {
        crate::kprintln!("[smp-test] FAIL: exercisers: the window was refused: {refusal:?}");
        crate::kprintln!("[smp-test] exercisers: 0 passed, {DRIVER_COUNT} failed");
        return;
    }
    crate::kprintln!(
        "[smp-test] exercisers: window installed at {WINDOW_BASE:#x} ({CORE_COUNT} pages)"
    );
    let mut passed = 0u32;
    let mut failed = 0u32;
    let mut tally = |name: &str, ok: bool| {
        if ok {
            passed += 1;
        } else {
            failed += 1;
            crate::kprintln!("[smp-test] FAIL: {name}");
        }
    };
    tally("sgi-round-trip", sgi_round_trip());
    tally("kprintln-stress", kprintln_stress());
    tally("tlb-shootdown", shootdown_round_trip());
    tally("tlb-shootdown-stress", shootdown_stress());
    // WS-BP BP8.5: the counters, read through the Lean seam on an image that
    // links the kernel; the HAL-only image reports it not run and counts it in
    // neither column.
    if let Some(ok) = per_core_stats() {
        tally("per-core-stats", ok);
    }
    // WS-CV CV0.1: the heap allocations of one syscall round trip, on the
    // Lean-linked image only, like the counters above.
    if let Some(ok) = heap_allocations_per_syscall() {
        tally("heap-allocations-per-syscall", ok);
    }
    crate::kprintln!("[smp-test] exercisers: {passed} passed, {failed} failed");
}

// ============================================================================
// WS-BP BP8.5 — the counters read on the booted machine
// ============================================================================

/// The selectors `lean_per_core_stats_component` answers, in the order
/// `perCoreStatsSelect` declares them (`SeLe4n/Kernel/Concurrency/Runtime.lean`):
/// the four counters, then the plausibility verdict.
pub const STATS_IRQS: u64 = 0;
/// The timer-tick word (`PerCoreStatsSnapshot.timerTicks`).
pub const STATS_TIMER_TICKS: u64 = 1;
/// The SGI word (`PerCoreStatsSnapshot.sgis`).
pub const STATS_SGIS: u64 = 2;
/// The syscall word (`PerCoreStatsSnapshot.syscalls`).
pub const STATS_SYSCALLS: u64 = 3;
/// The verdict: `1` when `perCoreStatsPlausible` holds of the snapshot read
/// for this call, `0` when it does not.
pub const STATS_PLAUSIBLE: u64 = 4;
/// What the seam answers for a core the model does not have or a selector it
/// does not define (`perCoreStatsRefused`): every bit set, which no counter
/// reaches and neither verdict is.  A not-ready core answers it too.
pub const STATS_REFUSED: u64 = u64::MAX;
/// The least gap between the SGI counts of two cores adjacent in core order
/// that the driver establishes before any snapshot, so the four slots are
/// pairwise distinguishable by that word: a snapshot read off ANOTHER core's
/// slot — an accessor resolving to the wrong slot, which is what the counters
/// were declared to catch — then cannot fall inside its own core's bracket.
/// The timer-tick counts alone could not tell the slots apart: the four cores
/// tick at one rate from nearly one instant.  Sixty-four leaves room for the
/// stray SGIs a running kernel may send between the spread and the snapshots.
pub const STATS_SGI_SPREAD: u64 = 64;
/// The most commands the spread sends one core before giving up on it — a
/// bound on the driver's running time rather than a budget a healthy run
/// approaches, since each core needs about [`STATS_SGI_SPREAD`] commands plus
/// whatever the earlier drivers left the core before it ahead by.
pub const STATS_SPREAD_FUEL: u64 = 4096;

/// One core's four counters.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CounterSnapshot {
    /// Every IRQ the core's handler dispatched.
    pub irqs: u64,
    /// The timer PPI alone; a subset of `irqs`.
    pub timer_ticks: u64,
    /// The SGIs alone; a subset of `irqs`, disjoint from the timer PPI.
    pub sgis: u64,
    /// `SVC` dispatches; not an interrupt.
    pub syscalls: u64,
}

impl CounterSnapshot {
    /// Component-wise `self <= other`.  The counters only grow, so a snapshot
    /// taken before another is at most it, component by component — which is
    /// what makes a read between two Rust reads of the same slot checkable
    /// without an atomic snapshot of four words.
    pub const fn le(&self, other: &CounterSnapshot) -> bool {
        self.irqs <= other.irqs
            && self.timer_ticks <= other.timer_ticks
            && self.sgis <= other.sgis
            && self.syscalls <= other.syscalls
    }
}

/// A core's counters read on the Rust side, in the order the Lean reader takes
/// them — the subtypes first, the total last (`perCoreStats`, PR #892 review
/// round 2) — so this snapshot satisfies the containment for the same reason:
/// every subtype increment it observes was preceded by a total increment the
/// later total read includes.  Read by the driver alone, which runs on the
/// Lean-linked image alone.
#[cfg(feature = "hw_target")]
fn rust_counters(core: usize) -> CounterSnapshot {
    let timer_ticks = crate::per_cpu_stats::timer_tick_count_for(core);
    let sgis = crate::per_cpu_stats::sgi_count_for(core);
    let irqs = crate::per_cpu_stats::irq_count_for(core);
    let syscalls = crate::per_cpu_stats::syscall_count_for(core);
    CounterSnapshot {
        irqs,
        timer_ticks,
        sgis,
        syscalls,
    }
}

/// A core's snapshot as the Lean seam reports it: the four words and the
/// verdict, each from a read of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LeanSnapshot {
    /// The four words.
    pub counters: CounterSnapshot,
    /// The verdict word: `1`, `0`, or [`STATS_REFUSED`].
    pub plausible: u64,
}

/// Why a core's snapshot fails the gate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatsFailure {
    /// The seam refused a read: a core the model does not have, or a core
    /// whose runtime is not ready.
    Refused,
    /// The verdict is not `1`: the snapshot cannot have come from a coherent
    /// slot.
    NotPlausible,
    /// A serving core reports no IRQ at all, though it ticks.
    NoIrqs,
    /// A serving core reports no timer tick.
    NoTicks,
    /// A word the seam reported is below the Rust read before it or above the
    /// Rust read after it — the two reads bracket every read of the SAME slot,
    /// so a word outside them was read off another.
    OutsideBracket,
}

/// The verdict on one core, decided on three reads — the Rust counters before,
/// the Lean words, the Rust counters after: what BP8.5 requires of a core of
/// the booted machine.  Pure, so it is tested on the host.
pub fn stats_verdict(
    before: &CounterSnapshot,
    lean: &LeanSnapshot,
    after: &CounterSnapshot,
) -> Result<(), StatsFailure> {
    let words = lean.counters;
    if [
        words.irqs,
        words.timer_ticks,
        words.sgis,
        words.syscalls,
        lean.plausible,
    ]
    .contains(&STATS_REFUSED)
    {
        return Err(StatsFailure::Refused);
    }
    if lean.plausible != 1 {
        return Err(StatsFailure::NotPlausible);
    }
    if words.irqs == 0 {
        return Err(StatsFailure::NoIrqs);
    }
    if words.timer_ticks == 0 {
        return Err(StatsFailure::NoTicks);
    }
    if !(before.le(&words) && words.le(after)) {
        return Err(StatsFailure::OutsideBracket);
    }
    Ok(())
}

/// One word of `core`'s snapshot through the Lean seam — `perCoreStats` on the
/// booted machine — or [`STATS_REFUSED`] on a core whose runtime is not ready,
/// which the boot core is not once it has passed Phase 7.  The call is behind
/// the readiness gate like every Lean upcall (`LEAN_READY_GATED_SEAMS` in
/// `build.rs`): the contract in `lean_ready.rs` admits no exception for a pure
/// read, since it is about the symbol, not the function.
#[cfg(feature = "hw_target")]
fn lean_stats_component(core: usize, selector: u64) -> u64 {
    let core_id = crate::per_cpu::current_core_id_from_tpidr();
    if crate::lean_ready::lean_ready(core_id as usize) {
        extern "C" {
            /// # Safety
            ///
            /// Sound only on a core whose Lean runtime is initialised —
            /// `lean_ready(current_core_id_from_tpidr())` must have returned
            /// `true` on *this* PE, which the enclosing branch has just
            /// checked.  It reads the per-core counters through this crate's
            /// four `ffi_per_core_*_count` accessors, allocates the snapshot
            /// on the kernel's Lean heap and frees it, and commits nothing.
            fn lean_per_core_stats_component(core_id: u64, selector: u64) -> u64;
        }
        // The call runs with IRQs masked and under the kernel-entry lock, as
        // every other Lean upcall runs.  It commits nothing, and that is not
        // the question: the kernel's Lean runtime runs one core at a time,
        // and its heap is behind a leaf lock that does not mask IRQs.  This
        // driver runs on the boot core in thread context with IRQs unmasked,
        // so a bare call can be preempted by a tick while it holds the heap
        // lock; the tick's own Lean call then spins on that lock forever, or
        // another core holding the kernel-entry lock does, and every core
        // runs out of kernel-entry fuel (Lean Action CI run 36499869963).
        let saved_daif = crate::interrupts::disable_interrupts();
        let word = crate::kernel_entry::with_kernel_entry(core_id as usize, || {
            // SAFETY: `lean_per_core_stats_component` is the C-callable
            // wrapper the Lean compiler emits for
            // `Concurrency.perCoreStatsComponentExport`: two `u64` in, a `u64`
            // out (a `BaseIO UInt64` crosses as `uint64_t`, which
            // `scripts/check_kernel_entry_exports.py` holds this declaration
            // to), reading the counters through this crate's own accessors and
            // touching no kernel state; this core's Lean runtime is
            // initialised — the `lean_ready` gate just checked — and no other
            // core runs Lean while this one holds the kernel-entry lock, so
            // entering the symbol is within the runtime's contract.
            unsafe { lean_per_core_stats_component(core as u64, selector) }
        });
        crate::interrupts::restore_interrupts(saved_daif);
        word
    } else {
        STATS_REFUSED
    }
}

/// WS-BP BP8.5: read every core's counters through the Lean seam on the booted
/// machine and hold them to what the counters were declared for.  `Some(pass)`
/// on an image that links the kernel.
///
/// Each core's snapshot is read between two Rust reads of the same slot, so
/// every word Lean reports must lie inside the bracket — a word outside it was
/// read off another slot.  The words are asked for in the reader's own order
/// (the subtypes, the total, the syscalls), each from a later snapshot than the
/// one before, so `ticks + sgis <= irqs` holds of the reported words too, the
/// counters being monotone; the verdict is asked last, of a snapshot of its own.
/// Before any snapshot the four slots are made pairwise distinguishable by
/// their SGI counts ([`STATS_SGI_SPREAD`] apart, in core order), because the
/// timer alone cannot tell them apart.
#[cfg(feature = "hw_target")]
fn per_core_stats() -> Option<bool> {
    // 1. Tell the four slots apart: make their SGI counts strictly increasing
    //    in core order, each at least `STATS_SGI_SPREAD` above the core before
    //    it, by sending each secondary's agent commands until its own count —
    //    read on this side, through the Rust twin of the accessor under test —
    //    is there.  Every command is one SGI to that core, nothing else sends
    //    one while this driver runs, and the count is read live, so the loop
    //    ends with the count where it must be whatever the earlier drivers
    //    left in each slot; a core that stops answering, or whose count does
    //    not get there within `STATS_SPREAD_FUEL` commands, fails the driver
    //    rather than hanging it.  The boot core's own count is the floor the
    //    chain starts from: the driver cannot raise it without an SGI to
    //    itself.
    let mut floor = crate::per_cpu_stats::sgi_count_for(0);
    for core in 1..CORE_COUNT {
        let target = floor.saturating_add(STATS_SGI_SPREAD);
        let mut sent = 0u64;
        while crate::per_cpu_stats::sgi_count_for(core) < target {
            if sent == STATS_SPREAD_FUEL {
                crate::kprintln!(
                    "[smp-test] FAIL: per-core-stats: core {core}'s SGI count did not reach \
                     {target} within {STATS_SPREAD_FUEL} commands"
                );
                return Some(false);
            }
            if command(core, COMMAND_PROBE, window_address(core)).is_none() {
                crate::kprintln!(
                    "[smp-test] FAIL: per-core-stats: core {core} did not answer a spread command"
                );
                return Some(false);
            }
            sent += 1;
        }
        floor = crate::per_cpu_stats::sgi_count_for(core);
    }
    // 2. Each core's snapshot, through the seam, between two Rust reads.
    let mut pass = true;
    let mut sgi_counts = [0u64; CORE_COUNT];
    for (core, sgi_count) in sgi_counts.iter_mut().enumerate() {
        let before = rust_counters(core);
        let timer_ticks = lean_stats_component(core, STATS_TIMER_TICKS);
        let sgis = lean_stats_component(core, STATS_SGIS);
        let irqs = lean_stats_component(core, STATS_IRQS);
        let syscalls = lean_stats_component(core, STATS_SYSCALLS);
        let plausible = lean_stats_component(core, STATS_PLAUSIBLE);
        let after = rust_counters(core);
        let lean = LeanSnapshot {
            counters: CounterSnapshot {
                irqs,
                timer_ticks,
                sgis,
                syscalls,
            },
            plausible,
        };
        crate::kprintln!(
            "[smp-test] per-core-stats: core {core}: lean irqs={irqs} timer-ticks={timer_ticks} \
             sgis={sgis} syscalls={syscalls} plausible={plausible}"
        );
        crate::kprintln!(
            "[smp-test] per-core-stats: core {core}: rust before irqs={} timer-ticks={} sgis={} \
             syscalls={} after irqs={} timer-ticks={} sgis={} syscalls={}",
            before.irqs,
            before.timer_ticks,
            before.sgis,
            before.syscalls,
            after.irqs,
            after.timer_ticks,
            after.sgis,
            after.syscalls,
        );
        if let Err(why) = stats_verdict(&before, &lean, &after) {
            crate::kprintln!("[smp-test] FAIL: per-core-stats: core {core}: {why:?}");
            pass = false;
        }
        *sgi_count = sgis;
    }
    // 3. The slots are told apart by their SGI counts.
    for a in 0..CORE_COUNT {
        for b in (a + 1)..CORE_COUNT {
            if sgi_counts[a] == sgi_counts[b] {
                crate::kprintln!(
                    "[smp-test] FAIL: per-core-stats: cores {a} and {b} report one SGI count ({}), \
                     so a wrong slot could not be told from the right one",
                    sgi_counts[a]
                );
                pass = false;
            }
        }
    }
    if pass {
        crate::kprintln!(
            "[smp-test] per-core-stats: every core's snapshot is plausible, ticked, and inside \
             its own slot's bracket"
        );
    }
    Some(pass)
}

/// The HAL-only image links no Lean kernel: the reader and the verdict are the
/// kernel's, so there is nothing to execute here, and the driver says so rather
/// than counting in either column.
#[cfg(not(feature = "hw_target"))]
fn per_core_stats() -> Option<bool> {
    crate::kprintln!(
        "[smp-test] per-core-stats: not run (no Lean kernel linked; the reader and the verdict \
         are Lean's)"
    );
    None
}

// ============================================================================
// WS-CV CV0.1 — the heap allocations of one syscall round trip
// ============================================================================

/// The syscall the round trip issues: `NotificationSignal` (`SyscallId` 14),
/// which continues its caller — no switch, no block — when nobody waits.
#[cfg(feature = "hw_target")]
const ROUND_TRIP_SYSCALL: u64 = 14;
/// Its capability address: slot 4 of the QEMU `virt` root task's CNode, the
/// interrupt notification (`Platform/QemuVirt/Deployment.lean`,
/// `qemuVirtRootTaskCNode`).
#[cfg(feature = "hw_target")]
const ROUND_TRIP_CPTR: u64 = 4;
/// Its `MessageInfo`: one message register (the badge, in `x2`).
#[cfg(feature = "hw_target")]
const ROUND_TRIP_MSG_INFO: u64 = 1;
/// `ESR_EL1` of an `SVC` from AArch64 (exception class `0x15`).
#[cfg(feature = "hw_target")]
const ROUND_TRIP_ESR: u64 = 0x15 << 26;
/// The badge signalled.
#[cfg(feature = "hw_target")]
const ROUND_TRIP_BADGE: u64 = 1;
/// `SPSR_EL1` of the frame: `EL0t` with DAIF clear, the state a thread's `SVC`
/// is taken from.  The mode is what makes the round trip a thread's syscall:
/// `trapFromEl0` admits only `M[3:0] = 0`, so an EL0 frame is saved into the
/// running thread and the core's register bank (`saveTrapFrameOnCore`) and the
/// thread is restored over the frame on the way out (`trap::restore_commit`),
/// which is the work every syscall from userspace does and an EL1 frame skips.
#[cfg(feature = "hw_target")]
const ROUND_TRIP_SPSR: u64 = 0;

/// The executing core's heap-allocation counter (`lean_heap`'s
/// `allocations_by_core`), or `None` if the heap cannot be read.
#[cfg(feature = "hw_target")]
fn own_heap_allocations(core: usize) -> Option<u64> {
    crate::lean_heap::kernel_allocations_on(core).ok()
}

/// **WS-CV CV0.1**: the heap allocations one syscall round trip makes, through
/// the Lean kernel, on the boot core.  The driver publishes a frame carrying a
/// `NotificationSignal` as the in-flight frame, classifies its syndrome and
/// dispatches it through the syscall seam (`svc_dispatch::dispatch_svc`), as
/// the `SVC` arm does, reading
/// this core's own heap counter before and after with IRQs masked across both
/// reads — the heap is one for every core, and a tick taken in between would
/// charge its own allocations to the syscall.  The number is evidence, read by
/// review (the plan's baseline and its CV5.1 re-reading); the verdict is only
/// that both reads happened, the counter did not go back, and the round trip
/// returned a frame.
#[cfg(feature = "hw_target")]
fn heap_allocations_per_syscall() -> Option<bool> {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    let mut frame = crate::trap::TrapFrame {
        gprs: [0; 31],
        sp_el0: 0,
        elr_el1: 0,
        spsr_el1: ROUND_TRIP_SPSR,
        esr_el1: ROUND_TRIP_ESR,
        far_el1: 0,
        tpidr_el0: 0,
        reserved: 0,
    };
    frame.gprs[0] = ROUND_TRIP_CPTR;
    frame.gprs[1] = ROUND_TRIP_MSG_INFO;
    frame.gprs[2] = ROUND_TRIP_BADGE;
    frame.gprs[7] = ROUND_TRIP_SYSCALL;
    let args = crate::svc_dispatch::SyscallArgs::from_trap_frame(&frame);
    let saved_daif = crate::interrupts::disable_interrupts();
    let before = own_heap_allocations(core);
    let (dispatched, restored) = {
        let _in_flight = crate::trap::InFlightFrame::publish(&mut frame);
        // The `SVC` arm's own order: the classification, then the dispatch.
        let class = crate::trap::classify_synchronous_exception(ROUND_TRIP_ESR);
        let dispatched = if class == crate::trap::sync_class::SVC {
            crate::svc_dispatch::dispatch_svc(ROUND_TRIP_SYSCALL as u32, &args)
        } else {
            Err(crate::svc_dispatch::DispatchError::InvalidSyscallId)
        };
        (dispatched, crate::trap::take_restored())
    };
    let after = own_heap_allocations(core);
    crate::interrupts::restore_interrupts(saved_daif);
    let (Some(before), Some(after)) = (before, after) else {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: the heap counter could not be read"
        );
        return Some(false);
    };
    let outcome = match dispatched {
        // A refusal is an ordinary frame too, its status in the `x1` label
        // (`error_frame_regs`): only label 0, the unit success a signal
        // returns, measures the syscall the gate names.
        Ok(crate::svc_dispatch::SvcOutcome::Frame(regs)) if regs[1] >> 9 == 0 => {
            crate::kprintln!(
                "[smp-test] heap-allocations-per-syscall: core {core}: returned x0={:#x} x1={:#x}",
                regs[0],
                regs[1]
            );
            true
        }
        Ok(crate::svc_dispatch::SvcOutcome::Frame(regs)) => {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: the signal was refused (x1 label {:#x})",
                regs[1] >> 9
            );
            false
        }
        Ok(other) => {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: the round trip did not return: {other:?}"
            );
            false
        }
        Err(error) => {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: the round trip was refused: {error:?}"
            );
            false
        }
    };
    // The restore installed the resumed thread's translation and set the
    // FP/SIMD trap for it.  This core goes on with its bring-up, so both go
    // back: the boot tables (whose kernel window every address space shares,
    // so the bring-up never stopped running) and the armed trap the boot
    // prologue leaves (`CPACR_EL1 = 0`).
    crate::user_translation::install_translation(crate::user_translation::Translation::Kernel);
    crate::fp_context::set_trap_for_resume(false);
    if !restored {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: the round trip resumed no thread"
        );
        return Some(false);
    }
    if after < before {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: the counter went back ({before} -> {after})"
        );
        return Some(false);
    }
    if !outcome {
        return Some(false);
    }
    crate::kprintln!(
        "[smp-test] heap-allocations-per-syscall: core {core}: before={before} after={after} \
         delta={}",
        after - before
    );
    Some(true)
}

/// The HAL-only image links no Lean kernel, so there is no syscall to measure.
#[cfg(not(feature = "hw_target"))]
fn heap_allocations_per_syscall() -> Option<bool> {
    crate::kprintln!("[smp-test] heap-allocations-per-syscall: not run (no Lean kernel linked)");
    None
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use crate::shootdown::{
        ack_round_in_slice, acked_gen_in_slice, current_generation_in, publish_round_ops_in,
        round_lock_held_by_in, round_lock_release_in, round_lock_try_acquire_in, ROUND_LOCK_FREE,
    };
    use core::cell::Cell;

    /// A clock that advances one tick per read.
    fn ticking() -> impl FnMut() -> u64 {
        let mut tick = 0u64;
        move || {
            tick += 1;
            tick
        }
    }

    #[test]
    fn an_agent_slot_is_one_cache_line() {
        assert_eq!(core::mem::size_of::<AgentSlot>(), 64);
        assert_eq!(core::mem::align_of::<AgentSlot>(), 64);
        assert_eq!(core::mem::size_of_val(&AGENTS), 64 * CORE_COUNT);
    }

    #[test]
    fn a_command_is_serviced_once_and_its_result_awaited() {
        let slots = [AgentSlot::new(), AgentSlot::new()];
        let sequence = agent_issue_in(&slots, 1, COMMAND_PROBE, 0x1234);
        assert_eq!(sequence, 1);
        let seen = Cell::new(None);
        assert!(agent_service_in(&slots, 1, |command, arg| {
            seen.set(Some((command, arg)));
            7
        }));
        assert_eq!(seen.get(), Some((COMMAND_PROBE, 0x1234)));
        assert!(
            !agent_service_in(&slots, 1, |_, _| panic!("serviced twice")),
            "a repeated SGI services nothing"
        );
        assert!(
            !agent_service_in(&slots, 0, |_, _| panic!("the other slot is idle")),
            "slots are independent"
        );
        assert_eq!(agent_await_in(&slots, 1, sequence, 10, ticking()), Some(7));
    }

    #[test]
    fn sequences_advance_per_issue_and_an_earlier_sequence_is_satisfied_by_a_later_one() {
        let slots = [AgentSlot::new()];
        let first = agent_issue_in(&slots, 0, COMMAND_PING, 0);
        assert!(agent_service_in(&slots, 0, |_, _| 1));
        let second = agent_issue_in(&slots, 0, COMMAND_PING, 0);
        assert_eq!((first, second), (1, 2));
        assert!(agent_service_in(&slots, 0, |_, _| 2));
        assert_eq!(agent_await_in(&slots, 0, first, 1, ticking()), Some(2));
        assert_eq!(agent_await_in(&slots, 0, second, 1, ticking()), Some(2));
    }

    #[test]
    fn awaiting_an_unserviced_command_times_out_after_the_budget() {
        let slots = [AgentSlot::new()];
        let sequence = agent_issue_in(&slots, 0, COMMAND_PING, 0);
        let reads = Cell::new(0u64);
        let result = agent_await_in(&slots, 0, sequence, 5, || {
            reads.set(reads.get() + 1);
            reads.get()
        });
        assert_eq!(result, None);
        // One read for the start, then one per poll until the deadline.
        assert_eq!(reads.get(), 6);
    }

    #[test]
    fn a_result_landing_at_the_deadline_is_taken() {
        let slots = [AgentSlot::new()];
        let sequence = agent_issue_in(&slots, 0, COMMAND_PING, 0);
        let reads = Cell::new(0u64);
        let result = agent_await_in(&slots, 0, sequence, 3, || {
            reads.set(reads.get() + 1);
            if reads.get() == 4 {
                // The deadline read: the result lands as the budget expires.
                assert!(agent_service_in(&slots, 0, |_, _| 9));
            }
            reads.get()
        });
        assert_eq!(result, Some(9));
    }

    #[test]
    fn patterns_are_distinct_across_cores_and_parities_and_depend_on_parity_alone() {
        let mut seen = std::vec::Vec::new();
        for core in 0..CORE_COUNT {
            for generation in 0..2u64 {
                let value = pattern(core, generation);
                assert!(!seen.contains(&value), "pattern {value:#x} repeats");
                seen.push(value);
                assert_eq!(value, pattern(core, generation + 2));
                assert_eq!(value >> 32, 0x5E4E_C0DE);
            }
        }
        assert_eq!(seen.len(), 2 * CORE_COUNT);
    }

    #[test]
    fn window_pages_are_page_apart_inside_one_level2_entry() {
        assert_eq!(WINDOW_BASE, crate::mmu::EXERCISER_WINDOW_BASE);
        assert!(
            WINDOW_BASE.is_multiple_of(1 << 30),
            "a level-1 entry's first byte"
        );
        for core in 0..CORE_COUNT {
            let address = window_address(core);
            assert_eq!(address, WINDOW_BASE + core as u64 * 4096);
            assert!(
                address - WINDOW_BASE < 1 << 21,
                "inside the level-2 table's entry 0"
            );
        }
    }

    #[test]
    fn backing_pages_alternate_by_parity_and_never_collide() {
        let mut seen = std::vec::Vec::new();
        for core in 0..CORE_COUNT {
            assert_eq!(backing_page(core, 0), 2 * core);
            assert_eq!(backing_page(core, 1), 2 * core + 1);
            assert_eq!(backing_page(core, 7), backing_page(core, 1));
            for generation in 0..2u64 {
                let page = backing_page(core, generation);
                assert!(page < 2 * CORE_COUNT);
                assert!(!seen.contains(&page));
                seen.push(page);
            }
        }
    }

    #[test]
    fn round_outcome_codes_round_trip() {
        for outcome in [
            RoundOutcome::Complete,
            RoundOutcome::LockWedged,
            RoundOutcome::SerialisationBroken,
            RoundOutcome::TimedOut,
        ] {
            assert_eq!(RoundOutcome::from_code(outcome.code()), Some(outcome));
        }
        assert_eq!(RoundOutcome::from_code(4), None);
        assert_eq!(
            RoundOutcome::Complete.code(),
            0,
            "the success code the stress requires"
        );
    }

    fn snapshot(irqs: u64, timer_ticks: u64, sgis: u64, syscalls: u64) -> CounterSnapshot {
        CounterSnapshot {
            irqs,
            timer_ticks,
            sgis,
            syscalls,
        }
    }

    #[test]
    fn a_counter_snapshot_is_ordered_component_by_component() {
        let low = snapshot(5, 3, 2, 0);
        let high = snapshot(9, 3, 4, 1);
        assert!(low.le(&low));
        assert!(low.le(&high));
        assert!(!high.le(&low));
        // One component below is enough: the order is not the total's.
        let mixed = snapshot(100, 2, 2, 0);
        assert!(!low.le(&mixed));
        assert!(!mixed.le(&low));
    }

    #[test]
    fn the_selectors_are_the_lean_readers_order_and_the_refusal_is_no_counter() {
        // `perCoreStatsSelect`'s arms, in order, and `perCoreStatsRefused`
        // (`SeLe4n/Kernel/Concurrency/Runtime.lean`); Tier 3 pins the Lean side.
        assert_eq!(STATS_IRQS, 0);
        assert_eq!(STATS_TIMER_TICKS, 1);
        assert_eq!(STATS_SGIS, 2);
        assert_eq!(STATS_SYSCALLS, 3);
        assert_eq!(STATS_PLAUSIBLE, 4);
        assert_eq!(STATS_REFUSED, u64::MAX);
        assert_eq!(STATS_SGI_SPREAD, 64);
        assert_eq!(STATS_SPREAD_FUEL, 4096);
    }

    #[test]
    fn the_stats_verdict_accepts_a_plausible_ticked_snapshot_inside_its_bracket() {
        let before = snapshot(10, 4, 3, 1);
        let lean = LeanSnapshot {
            counters: snapshot(12, 5, 3, 1),
            plausible: 1,
        };
        let after = snapshot(12, 5, 4, 2);
        assert_eq!(stats_verdict(&before, &lean, &after), Ok(()));
        // A bracket in which nothing moved is a bracket.
        let still = LeanSnapshot {
            counters: before,
            plausible: 1,
        };
        assert_eq!(stats_verdict(&before, &still, &before), Ok(()));
    }

    #[test]
    fn the_stats_verdict_names_each_failure_and_decides_them_in_order() {
        let before = snapshot(10, 4, 3, 1);
        let after = snapshot(12, 5, 4, 2);
        let good = snapshot(12, 5, 3, 1);
        let verdict = |counters, plausible| {
            stats_verdict(
                &before,
                &LeanSnapshot {
                    counters,
                    plausible,
                },
                &after,
            )
        };
        // A refused word in any position is the seam refusing, decided before
        // any relation between the words is asked.
        for refused in [
            snapshot(STATS_REFUSED, 5, 3, 1),
            snapshot(12, STATS_REFUSED, 3, 1),
            snapshot(12, 5, STATS_REFUSED, 1),
            snapshot(12, 5, 3, STATS_REFUSED),
        ] {
            assert_eq!(verdict(refused, 1), Err(StatsFailure::Refused));
        }
        assert_eq!(verdict(good, STATS_REFUSED), Err(StatsFailure::Refused));
        // The verdict word is `1` or the snapshot is refused as implausible.
        assert_eq!(verdict(good, 0), Err(StatsFailure::NotPlausible));
        assert_eq!(verdict(good, 2), Err(StatsFailure::NotPlausible));
        // A serving core that took no interrupt, then one that never ticked.
        let idle = snapshot(0, 0, 0, 0);
        let idle_lean = LeanSnapshot {
            counters: idle,
            plausible: 1,
        };
        assert_eq!(
            stats_verdict(&idle, &idle_lean, &idle),
            Err(StatsFailure::NoIrqs)
        );
        let sgis_only = snapshot(3, 0, 3, 0);
        let sgis_only_lean = LeanSnapshot {
            counters: sgis_only,
            plausible: 1,
        };
        assert_eq!(
            stats_verdict(&sgis_only, &sgis_only_lean, &sgis_only),
            Err(StatsFailure::NoTicks)
        );
        // A word below the read before it, or above the read after it, on any
        // one component, is a word read off another slot.
        for outside in [
            snapshot(9, 5, 3, 1),
            snapshot(12, 3, 3, 1),
            snapshot(12, 5, 2, 1),
            snapshot(12, 5, 3, 0),
            snapshot(13, 5, 3, 1),
            snapshot(12, 6, 3, 1),
            snapshot(12, 5, 5, 1),
            snapshot(12, 5, 3, 3),
            // Another core's whole snapshot: plausible and ticked, and caught
            // by the bracket alone.
            snapshot(200, 50, 140, 0),
        ] {
            assert_eq!(verdict(outside, 1), Err(StatsFailure::OutsideBracket));
        }
    }

    #[test]
    fn the_production_budgets_are_the_seams() {
        assert_eq!(ROUND_LOCK_ACQUIRE_FUEL, 1_000_000);
        assert_eq!(production_protocol().acquire_fuel, ROUND_LOCK_ACQUIRE_FUEL);
        assert_eq!(
            ROUND_WAIT_TIMEOUT_TICKS,
            crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS
        );
    }

    #[test]
    fn the_production_protocol_is_the_shootdown_modules_statics() {
        let protocol = production_protocol();
        assert!(core::ptr::eq(
            protocol.lock,
            &crate::shootdown::SHOOTDOWN_ROUND_LOCK
        ));
        assert!(core::ptr::eq(
            protocol.generations,
            &crate::shootdown::SHOOTDOWN_ROUND_SEQ
        ));
        assert!(core::ptr::eq(
            protocol.mailbox,
            &crate::shootdown::SHOOTDOWN_OPS
        ));
        assert!(core::ptr::eq(
            protocol.slots.as_ptr(),
            crate::shootdown::SHOOTDOWN_ACK.as_ptr()
        ));
        assert!(core::ptr::eq(protocol.in_flight, &ROUNDS_IN_FLIGHT));
    }

    /// A test's own protocol state.
    struct Protocol {
        lock: AtomicUsize,
        generations: AtomicU64,
        mailbox: ShootdownOpMailbox,
        slots: [ShootdownAckSlot; CORE_COUNT],
        in_flight: AtomicU32,
        acquire_fuel: u64,
    }

    impl Protocol {
        fn new() -> Self {
            Protocol {
                lock: AtomicUsize::new(ROUND_LOCK_FREE),
                generations: AtomicU64::new(0),
                mailbox: ShootdownOpMailbox::new(),
                slots: [const { ShootdownAckSlot::quiescent_at_boot() }; CORE_COUNT],
                in_flight: AtomicU32::new(0),
                acquire_fuel: ROUND_LOCK_ACQUIRE_FUEL,
            }
        }

        fn view(&self) -> RoundProtocol<'_> {
            RoundProtocol {
                lock: &self.lock,
                generations: &self.generations,
                mailbox: &self.mailbox,
                slots: &self.slots,
                in_flight: &self.in_flight,
                acquire_fuel: self.acquire_fuel,
            }
        }
    }

    fn inert_hardware(
    ) -> RoundHardware<impl FnMut(usize), impl FnMut(ShootdownOp), impl FnMut() -> u64> {
        RoundHardware {
            send_request: |_target: usize| {},
            broadcast_invalidate: |_op: ShootdownOp| {},
            now: ticking(),
        }
    }

    #[test]
    fn a_round_requests_every_online_target_but_the_initiator_and_completes_on_their_acks() {
        let protocol = Protocol::new();
        let online = [true, true, true, false];
        let requested = core::cell::RefCell::new(std::vec::Vec::new());
        let broadcast = core::cell::RefCell::new(std::vec::Vec::new());
        let mut hardware = RoundHardware {
            send_request: |target: usize| {
                requested.borrow_mut().push(target);
                // The target services the request: it acknowledges the
                // generation the mailbox names, as `tlb_shootdown_req_service_in` does.
                let generation = current_generation_in(&protocol.mailbox);
                ack_round_in_slice(&protocol.slots, target, generation);
            },
            broadcast_invalidate: |op: ShootdownOp| broadcast.borrow_mut().push(op),
            now: ticking(),
        };
        let outcome = run_round_in(
            &protocol.view(),
            &online,
            0,
            window_operand(0),
            100,
            &mut hardware,
        );
        assert_eq!(outcome, (1, RoundOutcome::Complete));
        assert_eq!(
            *requested.borrow(),
            [1, 2],
            "every online target but the initiator"
        );
        assert_eq!(*broadcast.borrow(), [window_operand(0)]);
        assert_eq!(protocol.lock.load(Ordering::Acquire), ROUND_LOCK_FREE);
        assert_eq!(protocol.in_flight.load(Ordering::Acquire), 0);
        assert_eq!(
            current_generation_in(&protocol.mailbox),
            1,
            "the operands were published under the round's generation"
        );
        assert_eq!(
            acked_gen_in_slice(&protocol.slots, 3),
            0,
            "an offline core is neither requested nor waited on"
        );
        assert_eq!(
            acked_gen_in_slice(&protocol.slots, 0),
            0,
            "the initiator never acknowledges its own round"
        );
    }

    #[test]
    fn a_round_nobody_acknowledges_times_out_and_keeps_the_lock() {
        let protocol = Protocol::new();
        let mut hardware = inert_hardware();
        let outcome = run_round_in(
            &protocol.view(),
            &[true, true, false, false],
            0,
            window_operand(0),
            25,
            &mut hardware,
        );
        assert_eq!(outcome, (1, RoundOutcome::TimedOut));
        assert!(
            round_lock_held_by_in(&protocol.lock, 0),
            "the seam halts with the lock held"
        );
        assert_eq!(protocol.in_flight.load(Ordering::Acquire), 1);
    }

    #[test]
    fn a_second_initiator_inside_the_critical_section_is_reported() {
        let protocol = Protocol::new();
        // Another initiator is inside.
        protocol.in_flight.store(1, Ordering::Release);
        let sent = Cell::new(0u32);
        let mut hardware = RoundHardware {
            send_request: |_target: usize| sent.set(sent.get() + 1),
            broadcast_invalidate: |_op: ShootdownOp| panic!("nothing is broadcast"),
            now: ticking(),
        };
        let outcome = run_round_in(
            &protocol.view(),
            &[true; CORE_COUNT],
            2,
            window_operand(2),
            10,
            &mut hardware,
        );
        assert_eq!(outcome, (0, RoundOutcome::SerialisationBroken));
        assert_eq!(sent.get(), 0, "nothing is published");
        assert_eq!(
            protocol.generations.load(Ordering::Acquire),
            0,
            "no generation is allocated"
        );
        assert_eq!(
            protocol.lock.load(Ordering::Acquire),
            ROUND_LOCK_FREE,
            "the lock is given back"
        );
        assert_eq!(
            protocol.in_flight.load(Ordering::Acquire),
            1,
            "the other initiator's count stands"
        );
    }

    #[test]
    fn a_lock_held_by_another_core_for_ever_is_reported_wedged_without_touching_it() {
        let mut protocol = Protocol::new();
        protocol.acquire_fuel = 1_000;
        assert!(round_lock_try_acquire_in(&protocol.lock, 3));
        let mut hardware = inert_hardware();
        let outcome = run_round_in(
            &protocol.view(),
            &[true; CORE_COUNT],
            0,
            window_operand(0),
            10,
            &mut hardware,
        );
        assert_eq!(outcome, (0, RoundOutcome::LockWedged));
        assert!(
            round_lock_held_by_in(&protocol.lock, 3),
            "the holder's lock is not touched"
        );
        assert_eq!(protocol.in_flight.load(Ordering::Acquire), 0);
        assert_eq!(protocol.generations.load(Ordering::Acquire), 0);
    }

    #[test]
    fn a_waiter_self_services_the_round_in_flight_and_acquires_after_the_release() {
        let mut protocol = Protocol::new();
        // The host scheduler, not the fuel, decides when the holder runs.
        protocol.acquire_fuel = u64::MAX;
        // Core 1 holds the lock with generation 5 published and core 0's
        // acknowledgment outstanding.
        assert!(round_lock_try_acquire_in(&protocol.lock, 1));
        protocol.generations.store(5, Ordering::Release);
        publish_round_ops_in(&protocol.mailbox, &[window_operand(1)], 5);
        let protocol = &protocol;
        std::thread::scope(|scope| {
            scope.spawn(move || {
                // Core 1's initiator: it waits for core 0's acknowledgment of
                // generation 5 — which only core 0's self-service can give,
                // since it is spinning for the lock with IRQs masked — then
                // releases.
                while acked_gen_in_slice(&protocol.slots, 0) < 5 {
                    std::thread::yield_now();
                }
                round_lock_release_in(&protocol.lock);
            });
            let mut hardware = inert_hardware();
            let outcome = run_round_in(
                &protocol.view(),
                &[true, false, false, false],
                0,
                window_operand(0),
                10,
                &mut hardware,
            );
            assert_eq!(outcome, (6, RoundOutcome::Complete));
        });
        assert_eq!(
            acked_gen_in_slice(&protocol.slots, 0),
            5,
            "core 0 acknowledged the round it self-serviced, and no other"
        );
        assert_eq!(protocol.lock.load(Ordering::Acquire), ROUND_LOCK_FREE);
        assert_eq!(protocol.in_flight.load(Ordering::Acquire), 0);
    }

    #[test]
    fn the_window_operand_is_a_page_invalidation_of_the_window() {
        let op = window_operand(2);
        assert_eq!(
            crate::tlb::decode_tlb_invalidation(op.op_tag, op.asid, op.vaddr),
            Some(crate::tlb::TlbInvalidation::Vae1 {
                asid: 0,
                vaddr: window_address(2)
            })
        );
    }

    #[test]
    fn the_agent_handler_has_the_sgi_handler_signature() {
        let handler: crate::gic::SgiHandler = agent_sgi_handler;
        let _ = handler;
    }

    #[test]
    fn the_window_is_admitted_only_sealed_aligned_inside_the_kernel_at_a_free_entry() {
        use crate::mmu::{exerciser_window_admissible, ExerciserWindowRefusal as Refusal};
        let kernel = (0x4008_0000, 0x0100_0000);
        assert_eq!(
            exerciser_window_admissible(0x4010_0000, true, 0, kernel),
            Ok(())
        );
        assert_eq!(
            exerciser_window_admissible(0x4107_F000, true, 0, kernel),
            Ok(()),
            "the last page of the extent"
        );
        assert_eq!(
            exerciser_window_admissible(0x4010_0000, false, 0, kernel),
            Err(Refusal::NotSealed)
        );
        assert_eq!(
            exerciser_window_admissible(0x4010_0800, true, 0, kernel),
            Err(Refusal::TableUnaligned)
        );
        assert_eq!(
            exerciser_window_admissible(0x4000_0000, true, 0, kernel),
            Err(Refusal::TableOutsideKernelExtent),
            "below the image"
        );
        assert_eq!(
            exerciser_window_admissible(0x4108_0000, true, 0, kernel),
            Err(Refusal::TableOutsideKernelExtent),
            "one page past the image"
        );
        assert_eq!(
            exerciser_window_admissible(0x4010_0000, true, 0x4000_0000 | 0b11, kernel),
            Err(Refusal::EntryInUse)
        );
        assert_eq!(
            exerciser_window_admissible(0x4010_0000, true, 0x4000_0000 | 0b01, kernel),
            Err(Refusal::EntryInUse),
            "a block entry is in use too"
        );
    }

    #[test]
    fn the_exerciser_descriptors_are_global_kernel_only_and_never_executable() {
        let page = crate::mmu::exerciser_page_descriptor(0x4020_0000);
        assert_eq!(page & 0b11, 0b11, "a valid page descriptor");
        assert_eq!(
            page & (1 << 11),
            0,
            "nG clear: a global entry, which the idle restore's TTBR0 writes keep"
        );
        assert_ne!(page & (1 << 53), 0, "PXN");
        assert_ne!(page & (1 << 54), 0, "UXN");
        assert_eq!(page & (0b11 << 6), 0, "AP: EL1 read-write, no EL0 access");
        assert_ne!(
            page & (1 << 10),
            0,
            "AF: no access flag fault on the first probe"
        );
        assert_eq!(page & 0x0000_FFFF_FFFF_F000, 0x4020_0000);
        let table = crate::mmu::exerciser_table_descriptor(0x4030_0000);
        assert_eq!(table, 0x4030_0000 | 0b11);
    }
}
