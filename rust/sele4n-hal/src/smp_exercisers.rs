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
use core::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering};

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
/// Request a remote-core stall of this core (`remote_stall::stall_if_changed_in`)
/// and run its exit gate check (`remote_stall::enter_user`), clearing the user
/// flag the gate sets.  Both run inside this core's agent handler, with its
/// IRQs masked, so no kernel entry of this core (a reschedule or a tick, which
/// meets and clears a request under the kernel-entry lock) can run between
/// them.  The result is `0` when the request found the core in the kernel and
/// the gate refused the return to EL0, `1` when the gate let it return, and
/// `2` when the request did not find the core in the kernel.
pub const COMMAND_EXIT_GATE: u32 = 7;
/// Hold this core in its agent handler, its IRQs masked, until the boot core
/// releases it ([`HOLD_RELEASED`]) or two seconds pass.  The handler raises
/// [`HOLD_ENTERED`] first, so once the boot core sees it no kernel entry of
/// this core (a reschedule SGI, a tick) runs before the release: a thread the
/// boot core wakes on this core's home stays queued and is never run here.
/// The result is `1` when released, `0` on the timeout.
pub const COMMAND_HOLD: u32 = 8;

/// Raised by a core entering [`COMMAND_HOLD`]'s wait.
pub static HOLD_ENTERED: AtomicBool = AtomicBool::new(false);
/// Raised by the boot core to end [`COMMAND_HOLD`]'s wait.
pub static HOLD_RELEASED: AtomicBool = AtomicBool::new(false);

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
        COMMAND_EXIT_GATE => {
            let requested = crate::remote_stall::stall_if_changed_in(
                &crate::remote_stall::AT_USER,
                &crate::remote_stall::STALL_REQUESTED,
                core,
                true,
                0,
                |_| {},
            );
            if requested != crate::remote_stall::StallOutcome::NotAtUser {
                return 2;
            }
            let allowed = crate::remote_stall::enter_user(core);
            // This core is in an interrupt handler, not at EL0.
            crate::remote_stall::note_kernel_entry();
            u64::from(allowed)
        }
        COMMAND_HOLD => {
            HOLD_ENTERED.store(true, Ordering::Release);
            let start = crate::timer::read_counter();
            let timeout = command_timeout_ticks();
            loop {
                if HOLD_RELEASED.load(Ordering::Acquire) {
                    return 1;
                }
                if crate::timer::read_counter().saturating_sub(start) >= timeout {
                    return u64::from(HOLD_RELEASED.load(Ordering::Acquire));
                }
                core::hint::spin_loop();
            }
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

/// The remote-core stall (seL4's `remoteTCBStall`), driven between the boot
/// core and each secondary through the real flags, SGI and handlers:
///
/// 1. the secondary marked at user, the boot core's stall pokes it with the
///    `.reschedule` SGI and waits; the secondary's interrupt entry
///    (`note_kernel_entry`) is what ends the wait (`StallOutcome::Left`);
/// 2. the secondary in the kernel, the stall requests and does not wait
///    (`NotAtUser`), and the secondary's own exit gate then refuses its return
///    to EL0.  Both run on the secondary in one agent command
///    ([`COMMAND_EXIT_GATE`]), so no kernel entry of the secondary can meet
///    the request between them;
/// 3. on the Lean-linked image, the secondary's next kernel entry under the
///    kernel-entry lock (its reschedule) meets the request and advances the
///    secondary's save epoch, the count a stall's save wait reads
///    (`remote_stall::await_remote_saves_in`).
///
/// A secondary's tick may end step 1's wait before the poke does, which is
/// the protocol too (`NotAtUser`), so step 1 is retried until the poke is what
/// ended it.  A wait that times out fails the driver.
fn remote_stall() -> bool {
    use crate::remote_stall::{StallOutcome, AT_USER, STALL_REQUESTED};
    let poke = |target: usize| crate::gic::send_sgi(1u8 << target, crate::trap::RESCHEDULE_INTID);
    let mut pass = true;
    for core in 1..CORE_COUNT {
        let mut left = false;
        for _ in 0..16 {
            AT_USER[core].store(true, Ordering::SeqCst);
            let fuel = crate::remote_stall::STALL_WAIT_FUEL;
            match crate::remote_stall::stall_if_changed_in(
                &AT_USER,
                &STALL_REQUESTED,
                core,
                true,
                fuel,
                poke,
            ) {
                StallOutcome::Left => {
                    left = true;
                    break;
                }
                StallOutcome::TimedOut => break,
                StallOutcome::NotAtUser | StallOutcome::Unchanged => {}
            }
        }
        AT_USER[core].store(false, Ordering::SeqCst);
        if left {
            crate::kprintln!("[smp-test] remote-stall: core {core}: at user, poked, entered the kernel before the stall returned");
        }
        // The request and the gate run together on the secondary: a request
        // made here could be met by a kernel entry of the secondary still in
        // flight (step 1's reschedule, or a tick) before the gate ran.
        let refused = command(core, COMMAND_EXIT_GATE, 0) == Some(0);
        if refused {
            crate::kprintln!("[smp-test] remote-stall: core {core}: in the kernel, requested; its exit gate refused the return to user");
        }
        let met = if cfg!(feature = "hw_target") {
            // WS-ZA ZA6.11: the entry that meets the request is a locked entry,
            // so it advances the core's save epoch too — the epoch a stall's
            // save wait reads.
            let epoch = crate::remote_stall::SAVE_EPOCH[core].load(Ordering::Acquire);
            poke(core);
            let deadline = crate::timer::read_counter().saturating_add(command_timeout_ticks());
            while (STALL_REQUESTED[core].load(Ordering::SeqCst)
                || crate::remote_stall::SAVE_EPOCH[core].load(Ordering::Acquire) == epoch)
                && crate::timer::read_counter() < deadline
            {
                core::hint::spin_loop();
            }
            let met = !STALL_REQUESTED[core].load(Ordering::SeqCst)
                && crate::remote_stall::SAVE_EPOCH[core].load(Ordering::Acquire) != epoch;
            if met {
                crate::kprintln!(
                    "[smp-test] remote-stall: core {core}: its next kernel entry met the request"
                );
            }
            met
        } else {
            true
        };
        crate::remote_stall::clear_stall_request(core);
        if !(left && refused && met) {
            pass = false;
            crate::kprintln!("[smp-test] FAIL: remote-stall: core {core}: left {left}, refused {refused}, met {met}");
        }
    }
    if pass {
        crate::kprintln!(
            "[smp-test] remote-stall: every core left user mode before the stall returned"
        );
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
const DRIVER_COUNT: u32 = if cfg!(feature = "hw_target") { 7 } else { 5 };

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
    // The remote-core stall's protocol between the boot core and each
    // secondary, last, so its extra SGIs reach no counter a driver above reads.
    tally("remote-stall", remote_stall());
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

/// One syscall the driver issues as whichever thread is current on core 0: the
/// root task, or the partner thread the deployment configures beside it
/// (`Platform/QemuVirt/Deployment.lean`, `qemuVirtPartnerTcbId`).  The capability
/// addresses name slots of the root task's CNode, which the partner shares
/// (`qemuVirtRootTaskCNode`), through its guard ([`cap_address`]).
#[cfg(feature = "hw_target")]
struct RoundTrip {
    /// The name its printed lines carry.
    name: &'static str,
    /// The `SyscallId` in `x7`.
    syscall: u64,
    /// The capability address in `x0`.
    cptr: u64,
    /// The message length in `x1`'s `MessageInfo`: at most 4, except for the
    /// scheduling-context configure, the service register and the mint, whose
    /// fifth word the kernel reads from the root task's IPC buffer (the boot's,
    /// [`ROOT_IPC_BUFFER`], or the window's page while a scenario points the
    /// buffer there), and the long send, whose words past the fourth it reads
    /// from the sender's.
    msg_len: u64,
    /// The message registers `x2` to `x5`.
    msg: [u64; 4],
    /// A signal through this notification capability issued first and not
    /// measured, so a wait finds the capability's badge pending and consumes
    /// it without blocking.
    primed: Option<u64>,
    /// Whether the caller blocks: the dispatch answers `Blocked` and restores
    /// the other thread, instead of a frame to the caller.
    blocks: bool,
    /// The frame's `x1` and, where known, its `x2`-`x5` that the round trip
    /// must return (a refusal's payload, seL4's MR0-MR3); `None` checks only
    /// that the call succeeded.
    returns: Option<(u64, [Option<u64>; 4])>,
    /// The extra-capability addresses a capability-carrying send, call or
    /// reply names, and, when given, the receive path after them, written
    /// unmeasured, before the call, into the `caps_or_badges` and, for the
    /// path, `receive_cnode`, `receive_index` and `receive_depth` words of the
    /// IPC buffer at this address (seL4's `seL4_SetCap` and
    /// `seL4_SetCapReceivePath`; the kernel reads them with `lookupExtraCaps`
    /// and `getReceiveSlots`).  The two threads share the buffer, so the
    /// receive path is the receiver's as well.
    caps_or_badges: Option<(u64, [u64; 3], Option<[u64; 3]>)>,
    /// The first overflow word of a message longer than the four registers
    /// carry (`IpcBufferRead.ipcBufferOverflowBaseWord`, word 5 of the
    /// buffer), written unmeasured before the call into the IPC buffer at
    /// this address, the caller's own, and cleared after it, so a later
    /// call reading that word still finds the zero the kernel scrubbed: a
    /// mint's badge (seL4's `seL4_CNode_Mint`, whose fifth argument is
    /// read from the buffer).
    overflow: Option<(u64, u64)>,
}

/// `Send` (`SyscallId` 0).
#[cfg(feature = "hw_target")]
const SEND: u64 = 0;
/// `Receive` (`SyscallId` 1).
#[cfg(feature = "hw_target")]
const RECEIVE: u64 = 1;
/// `Call` (`SyscallId` 2).
#[cfg(feature = "hw_target")]
const CALL: u64 = 2;
/// `Reply` (`SyscallId` 3).
#[cfg(feature = "hw_target")]
const REPLY: u64 = 3;
/// `ReplyRecv` (`SyscallId` 16).
#[cfg(feature = "hw_target")]
const REPLY_RECV: u64 = 16;
/// `NotificationSignal` (`SyscallId` 14).
#[cfg(feature = "hw_target")]
const SIGNAL: u64 = 14;
/// `NotificationWait` (`SyscallId` 15).
#[cfg(feature = "hw_target")]
const WAIT: u64 = 15;
/// `TcbSuspend` (`SyscallId` 20).
#[cfg(feature = "hw_target")]
const TCB_SUSPEND: u64 = 20;
/// `TcbResume` (`SyscallId` 21).
#[cfg(feature = "hw_target")]
const TCB_RESUME: u64 = 21;
/// `MintReplyCap` (`SyscallId` 28).
#[cfg(feature = "hw_target")]
const MINT_REPLY_CAP: u64 = 28;
/// The capability invocations the invocation scenarios issue (WS-ZA ZA5.1),
/// by `SyscallId`.
#[cfg(feature = "hw_target")]
const CSPACE_MINT: u64 = 4;
#[cfg(feature = "hw_target")]
const CSPACE_COPY: u64 = 5;
#[cfg(feature = "hw_target")]
const CSPACE_MOVE: u64 = 6;
#[cfg(feature = "hw_target")]
const CSPACE_DELETE: u64 = 7;
#[cfg(feature = "hw_target")]
const VSPACE_MAP: u64 = 9;
#[cfg(feature = "hw_target")]
const VSPACE_UNMAP: u64 = 10;
/// `ServiceRegister` (`SyscallId` 11).
#[cfg(feature = "hw_target")]
const SERVICE_REGISTER: u64 = 11;
/// `ServiceRevoke` (`SyscallId` 12).
#[cfg(feature = "hw_target")]
const SERVICE_REVOKE: u64 = 12;
/// `ServiceQuery` (`SyscallId` 13).
#[cfg(feature = "hw_target")]
const SERVICE_QUERY: u64 = 13;
#[cfg(feature = "hw_target")]
const SCHED_CONTEXT_CONFIGURE: u64 = 17;
#[cfg(feature = "hw_target")]
const SCHED_CONTEXT_BIND: u64 = 18;
#[cfg(feature = "hw_target")]
const SCHED_CONTEXT_UNBIND: u64 = 19;
#[cfg(feature = "hw_target")]
const TCB_SET_PRIORITY: u64 = 22;
#[cfg(feature = "hw_target")]
const TCB_SET_MC_PRIORITY: u64 = 23;
#[cfg(feature = "hw_target")]
const TCB_SET_IPC_BUFFER: u64 = 24;
#[cfg(feature = "hw_target")]
const TCB_SET_AFFINITY: u64 = 25;
#[cfg(feature = "hw_target")]
const TCB_BIND_NOTIFICATION: u64 = 26;
#[cfg(feature = "hw_target")]
const TCB_UNBIND_NOTIFICATION: u64 = 27;
#[cfg(feature = "hw_target")]
const VSPACE_UNIFY_INSTRUCTION: u64 = 29;
#[cfg(feature = "hw_target")]
const TCB_SET_FAULT_HANDLER: u64 = 34;
#[cfg(feature = "hw_target")]
const CSPACE_REVOKE: u64 = 35;
#[cfg(feature = "hw_target")]
const UNTYPED_RETYPE: u64 = 36;
#[cfg(feature = "hw_target")]
const UNTYPED_RESET: u64 = 37;
#[cfg(feature = "hw_target")]
const TCB_SET_SPACE: u64 = 38;
#[cfg(feature = "hw_target")]
const PAGE_TABLE_MAP: u64 = 39;
#[cfg(feature = "hw_target")]
const PAGE_TABLE_UNMAP: u64 = 40;
/// `Yield` (`SyscallId` 41).
#[cfg(feature = "hw_target")]
const YIELD: u64 = 41;
/// `SchedContextConsumed` (`SyscallId` 42, WS-ZA ZA6.9).
#[cfg(feature = "hw_target")]
const SCHED_CONTEXT_CONSUMED: u64 = 42;
/// `SchedContextYieldTo` (`SyscallId` 43, WS-ZA ZA6.29).
#[cfg(feature = "hw_target")]
const SCHED_CONTEXT_YIELD_TO: u64 = 43;
/// `IrqHandlerAck` (`SyscallId` 44, WS-ZA ZA6.32).
#[cfg(feature = "hw_target")]
const IRQ_HANDLER_ACK: u64 = 44;
/// `IrqControlGet` (`SyscallId` 45, WS-ZA ZA6.32).
#[cfg(feature = "hw_target")]
const IRQ_CONTROL_GET: u64 = 45;
/// `IrqHandlerSetNotification` (`SyscallId` 46, WS-ZA ZA6.32).
#[cfg(feature = "hw_target")]
const IRQ_HANDLER_SET_NOTIFICATION: u64 = 46;
/// `IrqHandlerClear` (`SyscallId` 47, WS-ZA ZA6.32).
#[cfg(feature = "hw_target")]
const IRQ_HANDLER_CLEAR: u64 = 47;
/// **WS-ZA ZA6.2**: the steps of a scenario that are not syscalls, by a
/// `syscall` no `SyscallId` takes.  A timer tick is entered as
/// `handle_irq_per_core`'s timer branch enters it and measured as the kernel
/// entries are ([`heap_allocations_kernel_entry`]); the two masks bracket the
/// steps no real tick may come between, and are neither measured nor printed.
#[cfg(feature = "hw_target")]
const TIMER_TICK_STEP: u64 = u64::MAX;
#[cfg(feature = "hw_target")]
const MASK_TICKS_STEP: u64 = u64::MAX - 1;
#[cfg(feature = "hw_target")]
const UNMASK_TICKS_STEP: u64 = u64::MAX - 2;
/// The second core held in its agent handler ([`COMMAND_HOLD`]) and released:
/// the steps between wake a thread homed there, which the second core must
/// not run, since a round-trip thread's frame starts at address 0.  Neither is
/// measured nor printed.
#[cfg(feature = "hw_target")]
const HOLD_SECOND_CORE_STEP: u64 = u64::MAX - 3;
#[cfg(feature = "hw_target")]
const RELEASE_SECOND_CORE_STEP: u64 = u64::MAX - 4;
/// The receive path of the IPC buffer at the step's `cptr` set, unmeasured
/// and unprinted, to the step's first three message words (`receive_cnode`,
/// `receive_index`, `receive_depth`; seL4's `seL4_SetCapReceivePath`), the
/// slot the kernel's `getReceiveSlots` reads at a transfer to that buffer's
/// thread.  A depth of 0 names no slot.
#[cfg(feature = "hw_target")]
const RECEIVE_PATH_STEP: u64 = u64::MAX - 5;

/// The granting reply carrying one capability, measured: through the reply
/// capability, granting, naming the notification capability in
/// `caps_or_badges[0]`, to a caller whose receive path a [`RECEIVE_PATH_STEP`]
/// set; the transfer installs it in place (`performReplyCapsDelivered`).
#[cfg(feature = "hw_target")]
const INSTALLING_REPLY: RoundTrip = with_caps_keeping_path(
    partner_step(
        "grant-reply-installs-cap",
        REPLY,
        REPLY_CAP,
        ONE_EXTRA_CAP | 1,
        [0x80, 0],
        false,
    ),
    TAIL_IPC_BUFFER,
    [NOTIFICATION_CAP, 0, 0],
);

/// The receive path step setting the IPC buffer at `buffer`'s receive path to
/// `words` ([`RECEIVE_PATH_STEP`]).
#[cfg(feature = "hw_target")]
const fn receive_path(name: &'static str, buffer: u64, words: [u64; 3]) -> RoundTrip {
    RoundTrip {
        cptr: buffer,
        msg: [words[0], words[1], words[2], 0],
        ..kernel_step(name, RECEIVE_PATH_STEP)
    }
}

/// Hold `core` in its agent handler ([`COMMAND_HOLD`]); the sequence to await
/// at the release, once the core has entered the wait.
#[cfg(feature = "hw_target")]
fn hold_core(core: usize) -> Option<u64> {
    HOLD_RELEASED.store(false, Ordering::Release);
    HOLD_ENTERED.store(false, Ordering::Release);
    let sequence = agent_issue_in(&AGENTS, core, COMMAND_HOLD, 0);
    crate::gic::send_sgi(1u8 << core, AGENT_SGI_INTID);
    let start = crate::timer::read_counter();
    let timeout = command_timeout_ticks();
    loop {
        if HOLD_ENTERED.load(Ordering::Acquire) {
            return Some(sequence);
        }
        if crate::timer::read_counter().saturating_sub(start) >= timeout {
            HOLD_RELEASED.store(true, Ordering::Release);
            return HOLD_ENTERED.load(Ordering::Acquire).then_some(sequence);
        }
        core::hint::spin_loop();
    }
}

/// Release the core [`hold_core`] held; whether it reports the release.
#[cfg(feature = "hw_target")]
fn release_core(core: usize, sequence: u64) -> bool {
    HOLD_RELEASED.store(true, Ordering::Release);
    agent_await_in(
        &AGENTS,
        core,
        sequence,
        command_timeout_ticks(),
        crate::timer::read_counter,
    ) == Some(1)
}

/// A scenario step of kind `syscall`, one of the three above.
#[cfg(feature = "hw_target")]
const fn kernel_step(name: &'static str, syscall: u64) -> RoundTrip {
    RoundTrip {
        name,
        syscall,
        cptr: 0,
        msg_len: 0,
        msg: [0, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    }
}

/// The refill scenario's scheduling context: a budget of one tick a period of
/// two, so the refill a forfeit schedules falls due on the second tick after it.
#[cfg(feature = "hw_target")]
const REFILL_BUDGET: u64 = 1;
#[cfg(feature = "hw_target")]
const REFILL_PERIOD: u64 = 2;
/// The declassification and audit calls (WS-ZA ZA5.13), by `SyscallId`.
#[cfg(feature = "hw_target")]
const DECLASSIFY: u64 = 30;
#[cfg(feature = "hw_target")]
const AUDIT_READ: u64 = 31;
#[cfg(feature = "hw_target")]
const AUDIT_DRAIN: u64 = 32;
#[cfg(feature = "hw_target")]
const DECLASSIFY_SIGNAL: u64 = 33;

/// The root CNode's guard bit (the top bit of its 58-bit guard over a 64-slot
/// radix, `qemuVirtExerciserRootCNodeOf`): a slot's capability address is the
/// slot with bit 63 set, so
/// every address the round trips resolve is a word `≥ 2^63`, read without a
/// heap number at the decode and at every guard and slot extraction of the
/// lookup (WS-ZA ZA4.8).
#[cfg(feature = "hw_target")]
const ROOT_CNODE_GUARD: u64 = 1 << 63;

/// The capability address of the root task's CNode slot `slot`.
#[cfg(feature = "hw_target")]
const fn cap_address(slot: u64) -> u64 {
    ROOT_CNODE_GUARD | slot
}

/// **The root task's IPC buffer**, which the boot maps and sets
/// (`qemuVirtExerciserRootIpcBufferVAddr`, seL4's initial-thread IPC buffer):
/// the first page under level-0 index 2 of the root task's address space,
/// beside the scenarios' window ([`FRAME_VADDR`], index 1).  A scenario that
/// points the root task's buffer elsewhere points it back here when it is
/// done (`root-ipc-buffer-back`).
#[cfg(feature = "hw_target")]
const ROOT_IPC_BUFFER: u64 = 2 << 39;

/// The CNode operation word (`sele4n_abi::args::cspace::cnode_op_word`) of a
/// copy or a move between two of the root task's slots: both resolved at the
/// root CNode's whole depth, its 58-bit guard and its 6-bit radix.
#[cfg(feature = "hw_target")]
const ROOT_SLOT_DEPTHS: u64 = 64 | (64 << 8);

/// A move's four words from root slot `src` to root slot `dest` (seL4's
/// `seL4_CNode_Move` addressing): the destination index in the invoked root
/// CNode, the source root (the root task's own CNode capability), the source
/// index, and both depths.
#[cfg(feature = "hw_target")]
const fn root_slot_pair(src: u64, dest: u64) -> [u64; 4] {
    root_slot_masked(src, dest, 0)
}

/// Every access right, as a copy's or a mint's rights mask (seL4's
/// `seL4_AllRights`): read, write, grant, grant-reply and retype.
#[cfg(feature = "hw_target")]
const ALL_RIGHTS: u64 = 0x1f;

/// A copy's four words from root slot `src` to root slot `dest` (seL4's
/// `seL4_CNode_Copy`): [`root_slot_pair`]'s addressing with every right in the
/// mask, so the copy keeps the source's rights.
#[cfg(feature = "hw_target")]
const fn root_slot_copy(src: u64, dest: u64) -> [u64; 4] {
    root_slot_masked(src, dest, ALL_RIGHTS)
}

/// [`root_slot_pair`]'s addressing with `rights` in the operation word's
/// rights field (`sele4n_abi::args::cspace::cnode_op_word::RIGHTS_SHIFT`).
#[cfg(feature = "hw_target")]
const fn root_slot_masked(src: u64, dest: u64, rights: u64) -> [u64; 4] {
    [
        cap_address(dest),
        cap_address(CNODE_SLOT),
        cap_address(src),
        ROOT_SLOT_DEPTHS | (rights << 16),
    ]
}

/// **The CNode mint** (seL4's `seL4_CNode_Mint`) from root slot `src` to
/// root slot `dest`, its capability masked by `rights` and badged `badge`:
/// five words, [`root_slot_masked`]'s four and the badge, which the kernel
/// reads from the root task's IPC buffer at `buffer`
/// ([`RoundTrip::overflow`]).
#[cfg(feature = "hw_target")]
const fn mint(
    name: &'static str,
    src: u64,
    dest: u64,
    rights: u64,
    badge: u64,
    buffer: u64,
) -> RoundTrip {
    RoundTrip {
        msg_len: 5,
        overflow: Some((buffer, badge)),
        ..invocation(
            name,
            CSPACE_MINT,
            CNODE_CAP,
            root_slot_masked(src, dest, rights),
        )
    }
}

/// The root task's CNode slots the round trips name.
#[cfg(feature = "hw_target")]
const ROOT_TCB_SLOT: u64 = 1;
#[cfg(feature = "hw_target")]
const CNODE_SLOT: u64 = 2;
#[cfg(feature = "hw_target")]
const NOTIFICATION_SLOT: u64 = 4;
#[cfg(feature = "hw_target")]
const PARTNER_TCB_SLOT: u64 = 6;
#[cfg(feature = "hw_target")]
const ENDPOINT_SLOT: u64 = 7;
#[cfg(feature = "hw_target")]
const REPLY_OBJECT_SLOT: u64 = 8;
/// The free slot the reply capability is minted into.
#[cfg(feature = "hw_target")]
const REPLY_CAP_SLOT: u64 = 9;
#[cfg(feature = "hw_target")]
const VSPACE_SLOT: u64 = 3;
#[cfg(feature = "hw_target")]
const UNTYPED_SLOT: u64 = 5;
/// Free slots the invocation scenarios fill and empty again.
#[cfg(feature = "hw_target")]
const COPY_SLOT: u64 = 10;
#[cfg(feature = "hw_target")]
const MOVE_SLOT: u64 = 11;
#[cfg(feature = "hw_target")]
const MINT_SLOT: u64 = 12;
#[cfg(feature = "hw_target")]
const FRAME_SLOT: u64 = 13;
/// The three intermediate page tables' slots; the last is the copy slot, free
/// again once the copy sequence has deleted what it moved.
#[cfg(feature = "hw_target")]
const PAGE_TABLE_SLOTS: [u64; 3] = [14, 15, COPY_SLOT];
/// The boot-configured scheduling context's slot, the one slot of the first
/// sixteen no other object or scenario uses.
#[cfg(feature = "hw_target")]
const SCHED_CONTEXT_SLOT: u64 = 0;
/// The slot of core 0's scheduling-control capability
/// (`qemuVirtSchedControlSlot`, WS-ZA ZA6.4): the authority every configure
/// round trip invokes, the context it configures named at MR0.
#[cfg(feature = "hw_target")]
const SCHED_CONTROL_SLOT: u64 = 16;
/// The slot of the exerciser image's boot audit capability
/// (`qemuVirtExerciserAuditSlot`, WS-ZA ZA5.13): the copy slot, deleted once
/// the declassification scenario ends.  Its next use is the invocation
/// scenarios' copy, which writes the copied capability's target over the
/// slot's record and its target cell.
#[cfg(feature = "hw_target")]
const AUDIT_SLOT: u64 = COPY_SLOT;
/// The slot of the root task's interrupt-control capability
/// (`qemuVirtIrqControlSlot`, WS-ZA ZA6.32): the authority every handler the
/// exerciser holds is issued from (`seL4_IRQControl_Get`).
#[cfg(feature = "hw_target")]
const IRQ_CONTROL_SLOT: u64 = 20;
/// The rights the boot gives the interrupt-control capability (`write` alone,
/// `Capability.irqControl`), as a mint's rights word.
#[cfg(feature = "hw_target")]
const IRQ_CONTROL_RIGHTS: u64 = 0x2;
/// The badge a badged mint of the interrupt-control capability writes.
#[cfg(feature = "hw_target")]
const IRQ_CONTROL_BADGE: u64 = 7;
/// The free slots the exerciser issues its two interrupt-handler capabilities
/// into (WS-ZA ZA6.32): the bound line's and the unbound line's.  The boot
/// issues no handler (`bootIssuesNoInterruptHandler`), as seL4's does not.
#[cfg(feature = "hw_target")]
const IRQ_BOUND_HANDLER_SLOT: u64 = 24;
#[cfg(feature = "hw_target")]
const IRQ_UNBOUND_HANDLER_SLOT: u64 = 25;

/// The free slots the donation-chain scenario (WS-ZA ZA6.33) carves its
/// server thread, its reply object and that reply's capability into.
#[cfg(feature = "hw_target")]
const CHAIN_TCB_SLOT: u64 = 22;
#[cfg(feature = "hw_target")]
const CHAIN_REPLY_OBJECT_SLOT: u64 = 23;
#[cfg(feature = "hw_target")]
const CHAIN_REPLY_CAP_SLOT: u64 = 26;
/// The boot-domain ids that scenario carves its thread and reply at.
#[cfg(feature = "hw_target")]
const CHAIN_CHILD_IDS: [u64; 2] = [33, 34];
/// The free slots the reply-stack scenarios (WS-ZA ZA6.34) carve a fourth
/// thread, the top of a three-frame stack, and its reply object and that
/// reply's capability into, and the boot-domain ids they carve them at.
#[cfg(feature = "hw_target")]
const STACK_TOP_TCB_SLOT: u64 = 28;
#[cfg(feature = "hw_target")]
const STACK_TOP_REPLY_OBJECT_SLOT: u64 = 29;
#[cfg(feature = "hw_target")]
const STACK_TOP_REPLY_CAP_SLOT: u64 = 30;
#[cfg(feature = "hw_target")]
const STACK_TOP_CHILD_IDS: [u64; 2] = [36, 37];
#[cfg(feature = "hw_target")]
const STACK_TOP_TCB_CAP: u64 = cap_address(STACK_TOP_TCB_SLOT);
#[cfg(feature = "hw_target")]
const STACK_TOP_REPLY_CAP: u64 = cap_address(STACK_TOP_REPLY_CAP_SLOT);
/// The second core (`TCB_SetAffinity`'s word for core 1) and the word that
/// clears an affinity (`affinityUnbindMarker`, the core count).
#[cfg(feature = "hw_target")]
const SECOND_CORE_AFFINITY: u64 = 1;
#[cfg(feature = "hw_target")]
const AFFINITY_UNBIND: u64 = 4;

/// The capability addresses of those slots.
#[cfg(feature = "hw_target")]
const ROOT_TCB_CAP: u64 = cap_address(ROOT_TCB_SLOT);
#[cfg(feature = "hw_target")]
const CHAIN_TCB_CAP: u64 = cap_address(CHAIN_TCB_SLOT);
#[cfg(feature = "hw_target")]
const CHAIN_REPLY_CAP: u64 = cap_address(CHAIN_REPLY_CAP_SLOT);
#[cfg(feature = "hw_target")]
const CNODE_CAP: u64 = cap_address(CNODE_SLOT);
#[cfg(feature = "hw_target")]
const SCHED_CONTEXT_CAP: u64 = cap_address(SCHED_CONTEXT_SLOT);
#[cfg(feature = "hw_target")]
const SCHED_CONTROL_CAP: u64 = cap_address(SCHED_CONTROL_SLOT);
#[cfg(feature = "hw_target")]
const IRQ_CONTROL_CAP: u64 = cap_address(IRQ_CONTROL_SLOT);
#[cfg(feature = "hw_target")]
const NOTIFICATION_CAP: u64 = cap_address(NOTIFICATION_SLOT);
#[cfg(feature = "hw_target")]
const PARTNER_TCB_CAP: u64 = cap_address(PARTNER_TCB_SLOT);
#[cfg(feature = "hw_target")]
const ENDPOINT_CAP: u64 = cap_address(ENDPOINT_SLOT);
#[cfg(feature = "hw_target")]
const REPLY_CAP: u64 = cap_address(REPLY_CAP_SLOT);
/// A badged copy of the endpoint capability, minted into the mint slot for the
/// partner scenarios and deleted before the invocation scenarios use the slot.
#[cfg(feature = "hw_target")]
const BADGED_ENDPOINT_CAP: u64 = cap_address(MINT_SLOT);
/// Its badge: a word above `2^63`, so a badge carried as a number would box.
#[cfg(feature = "hw_target")]
const ENDPOINT_BADGE: u64 = 0x8000_0000_0000_0007;
/// Read, write, grant and grant-reply: the endpoint capability's own rights.
#[cfg(feature = "hw_target")]
const ENDPOINT_RIGHTS: u64 = 0xf;
#[cfg(feature = "hw_target")]
const VSPACE_CAP: u64 = cap_address(VSPACE_SLOT);
#[cfg(feature = "hw_target")]
const UNTYPED_CAP: u64 = cap_address(UNTYPED_SLOT);
#[cfg(feature = "hw_target")]
const FRAME_CAP: u64 = cap_address(FRAME_SLOT);
/// The mint slot's capability, where the thread-finalising scenarios carve a
/// scheduling context.
#[cfg(feature = "hw_target")]
const MINT_CAP: u64 = cap_address(MINT_SLOT);
/// The frame capability's copy, in the move slot, while the revoke scenario
/// maps it.
#[cfg(feature = "hw_target")]
const MOVE_CAP: u64 = cap_address(MOVE_SLOT);
/// The boot audit capability (WS-ZA ZA5.13).
#[cfg(feature = "hw_target")]
const AUDIT_CAP: u64 = cap_address(AUDIT_SLOT);
#[cfg(feature = "hw_target")]
const PAGE_TABLE_CAPS: [u64; 3] = [
    cap_address(PAGE_TABLE_SLOTS[0]),
    cap_address(PAGE_TABLE_SLOTS[1]),
    cap_address(PAGE_TABLE_SLOTS[2]),
];

/// A signal on the interrupt notification: seL4's `seL4_Signal`, an empty
/// message, the badge ORed in the one minted into the capability (the boot's
/// notification capability is unbadged, so 0), never a caller-chosen word.
#[cfg(feature = "hw_target")]
const fn signal(name: &'static str) -> RoundTrip {
    RoundTrip {
        name,
        syscall: SIGNAL,
        cptr: NOTIFICATION_CAP,
        msg_len: 0,
        msg: [0, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    }
}

/// The notification capability minted, measured, into the mint slot with a
/// badge that does not fit a scalar `Nat` ([`WIDE_SIGNAL_BADGE`]) for the
/// round trips one thread makes alone, and deleted before the partner setup
/// mints the badged endpoint there ([`WIDE_BADGE_SETUP`],
/// [`WIDE_BADGE_TEARDOWN`]).
#[cfg(feature = "hw_target")]
const WIDE_BADGED_NOTIFICATION_CAP: u64 = cap_address(MINT_SLOT);
/// Its badge: `2^63`, so a badge carried as a number would box.  A signal
/// through the capability ORs exactly this word in (seL4's `capNtfnBadge`).
#[cfg(feature = "hw_target")]
const WIDE_SIGNAL_BADGE: u64 = 1 << 63;
/// Read and write: a signal needs the write right.
#[cfg(feature = "hw_target")]
const NOTIFICATION_MINT_RIGHTS: u64 = 0x3;
/// The badged notification capability's mint (measured twice, a delete
/// between, before the round trips one thread makes alone).
#[cfg(feature = "hw_target")]
const WIDE_BADGE_SETUP: [RoundTrip; 1] = [mint(
    "mint-wide-badged-notification",
    NOTIFICATION_SLOT,
    MINT_SLOT,
    NOTIFICATION_MINT_RIGHTS,
    WIDE_SIGNAL_BADGE,
    ROOT_IPC_BUFFER,
)];
/// Its delete (unmeasured, after them), so the mint slot is empty again.
#[cfg(feature = "hw_target")]
const WIDE_BADGE_TEARDOWN: [RoundTrip; 1] = [invocation(
    "delete-wide-badged-notification",
    CSPACE_DELETE,
    CNODE_CAP,
    [MINT_SLOT, 0, 0, 0],
)];

/// The round trips one thread makes alone (WS-ZA ZA4.1): the signal, a signal
/// whose capability's badge does not fit a scalar `Nat` (`≥ 2^63`), a wait
/// that consumes a pending badge, and a yield (WS-ZA ZA4.3), which invokes no
/// capability: the root task is unbound and alone on its core while these run,
/// so it ends its time slice and is chosen again.  Each continues its caller.
#[cfg(feature = "hw_target")]
const ROUND_TRIPS: [RoundTrip; 4] = [
    signal("signal"),
    RoundTrip {
        cptr: WIDE_BADGED_NOTIFICATION_CAP,
        ..signal("signal-wide-badge")
    },
    RoundTrip {
        name: "wait-pending",
        syscall: WAIT,
        cptr: NOTIFICATION_CAP,
        msg_len: 1,
        msg: [0, 0, 0, 0],
        primed: Some(NOTIFICATION_CAP),
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    RoundTrip {
        name: "yield",
        syscall: YIELD,
        cptr: 0,
        msg_len: 0,
        msg: [0, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
];

/// A step on the exerciser endpoint, or the notification, for the partner
/// scenarios.
#[cfg(feature = "hw_target")]
const fn partner_step(
    name: &'static str,
    syscall: u64,
    cptr: u64,
    msg_len: u64,
    msg: [u64; 2],
    blocks: bool,
) -> RoundTrip {
    RoundTrip {
        name,
        syscall,
        cptr,
        msg_len,
        msg: [msg[0], msg[1], 0, 0],
        primed: None,
        blocks,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    }
}

/// `trip`, naming the extra-capability addresses `words` in the caller's IPC
/// buffer at `buffer` (`RoundTrip::caps_or_badges`), and no receive slot
/// (a `receive_depth` of 0).
#[cfg(feature = "hw_target")]
const fn with_caps(trip: RoundTrip, buffer: u64, words: [u64; 3]) -> RoundTrip {
    with_caps_receiving(trip, buffer, words, [0; 3])
}

/// `trip`, naming the extra-capability addresses `words` and the receive path
/// `path` (`receive_cnode`, `receive_index`, `receive_depth`) in the IPC
/// buffer at `buffer`.
#[cfg(feature = "hw_target")]
const fn with_caps_receiving(
    trip: RoundTrip,
    buffer: u64,
    words: [u64; 3],
    path: [u64; 3],
) -> RoundTrip {
    RoundTrip {
        caps_or_badges: Some((buffer, words, Some(path))),
        ..trip
    }
}

/// `trip`, naming the extra-capability addresses `words` in the IPC buffer at
/// `buffer` and leaving the buffer's receive path as a [`RECEIVE_PATH_STEP`]
/// set it.
#[cfg(feature = "hw_target")]
const fn with_caps_keeping_path(trip: RoundTrip, buffer: u64, words: [u64; 3]) -> RoundTrip {
    RoundTrip {
        caps_or_badges: Some((buffer, words, None)),
        ..trip
    }
}

/// The receive path that names the root CNode's slot `slot`: the CNode's own
/// capability, the slot's full-word address and the word's 64 bits.
#[cfg(feature = "hw_target")]
const fn receive_slot_path(slot: u64) -> [u64; 3] {
    [CNODE_CAP, cap_address(slot), 64]
}

/// The index of the IPC buffer's `caps_or_badges[0]` word: seL4's
/// `seL4_IPCBuffer` puts it after the `tag`, the 120 `msg` words and
/// `userData` (`IpcBufferRead.ipcBufferCapsOrBadgesWord 0` past
/// `ipcBufferOverflowBaseWord`; `sele4n_abi::IpcBuffer::caps_or_badges`,
/// pinned by `caps_or_badges_word_is_the_abi_layout`).
#[cfg(any(feature = "hw_target", test))]
const CAPS_OR_BADGES_WORD: u64 = 122;
/// The IPC buffer's first overflow word, message register 4
/// (`IpcBufferRead.ipcBufferOverflowBaseWord`, `sele4n_abi::IpcBuffer::msg`
/// past the four registers): word 5, after the tag and `msg[0..4]`.
#[cfg(feature = "hw_target")]
const OVERFLOW_BASE_WORD: u64 = 5;

/// The index of the IPC buffer's `receive_cnode` word, the first of the three
/// receive-path words (`IpcBufferRead.ipcBufferReceiveCNodeWord`;
/// `sele4n_abi::IpcBuffer::receive_cnode`, pinned by
/// `receive_path_word_is_the_abi_layout`).
#[cfg(any(feature = "hw_target", test))]
const RECEIVE_PATH_WORD: u64 = 125;

/// The round trips that need a second thread (WS-ZA ZA4.1), each a sequence
/// issued as whichever thread is current.  A step that blocks the current
/// thread makes core 0 switch to the other (the only other runnable thread
/// there), which the next step runs as: whichever thread started, the sequence
/// is the same, so a tick that switched the two between sequences changes
/// nothing.  The IPC sequences open with such a step; the finalising deletes
/// carve first, and the bound notification's blocks no thread.
/// - a receive that blocks, then a send that finds the receiver waiting and
///   continues;
/// - a wait that blocks, then a signal that wakes the waiter and continues;
/// - a receive that blocks holding the reply capability, then a call that
///   wakes it and blocks for the answer, then a reply-receive that answers it
///   and blocks for the next caller (WS-ZA ZA4.7), a second call that wakes
///   the server through that reply object, then the reply, which continues;
/// - a send that blocks, then a receive that takes the blocked sender's
///   message and continues (WS-ZA ZA4.7);
/// - the send to a waiting receiver, the send that blocks and the call again,
///   each through the badged endpoint capability (WS-ZA ZA5.3: a capability
///   holds its badge as a word and a flag, which the send hands on as they
///   are);
/// - an endpoint carved, a receive on it that blocks, and its only capability
///   deleted by the other thread, which cancels the blocked receive (seL4's
///   `cancelAllIPC`), wakes the receiver and retires the endpoint (WS-ZA ZA5.4
///   part 23);
/// - the same of a notification and a wait (`cancelAllSignals`);
/// - a notification carved, bound to the partner thread, and its only
///   capability deleted, which unbinds it (`unbindMaybeNotification`) and
///   retires it.
///
/// Each carve's object is its own id ([`FINALISED_CHILD_IDS`]) in the frame
/// slot, which the invocation scenarios fill only later; the delete empties it.
#[cfg(feature = "hw_target")]
const PARTNER_SCENARIOS: [&[RoundTrip]; 12] = [
    &[
        partner_step("receive-blocks", RECEIVE, ENDPOINT_CAP, 0, [0, 0], true),
        partner_step("send-to-receiver", SEND, ENDPOINT_CAP, 1, [0x55, 0], false),
    ],
    &[
        partner_step("wait-blocks", WAIT, NOTIFICATION_CAP, 0, [0, 0], true),
        partner_step(
            "signal-to-waiter",
            SIGNAL,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            false,
        ),
    ],
    &[
        partner_step(
            "receive-for-call",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step("call", CALL, ENDPOINT_CAP, 1, [0x66, 0], true),
        partner_step(
            "reply-recv",
            REPLY_RECV,
            ENDPOINT_CAP,
            2,
            [REPLY_CAP, 0x99],
            true,
        ),
        partner_step(
            "call-to-reply-receiver",
            CALL,
            ENDPOINT_CAP,
            1,
            [0xaa, 0],
            true,
        ),
        partner_step("reply", REPLY, REPLY_CAP, 1, [0x77, 0], false),
    ],
    &[
        partner_step("send-blocks", SEND, ENDPOINT_CAP, 1, [0x88, 0], true),
        partner_step(
            "receive-from-sender",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            false,
        ),
    ],
    &[
        partner_step(
            "receive-for-badged-send",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            true,
        ),
        partner_step(
            "badged-send-to-receiver",
            SEND,
            BADGED_ENDPOINT_CAP,
            1,
            [0x55, 0],
            false,
        ),
    ],
    &[
        partner_step(
            "badged-send-blocks",
            SEND,
            BADGED_ENDPOINT_CAP,
            1,
            [0x88, 0],
            true,
        ),
        partner_step(
            "receive-from-badged-sender",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            false,
        ),
    ],
    &[
        partner_step(
            "receive-for-badged-call",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step("badged-call", CALL, BADGED_ENDPOINT_CAP, 1, [0x66, 0], true),
        partner_step(
            "reply-to-badged-call",
            REPLY,
            REPLY_CAP,
            1,
            [0x77, 0],
            false,
        ),
    ],
    // WS-ZA ZA5.4 part 23: the final delete of a busy endpoint, of a busy
    // notification, and of a bound one.
    &[
        invocation(
            "untyped-retype-busy-endpoint",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [ENDPOINT_TYPE, FINALISED_CHILD_IDS[0], CNODE_CAP, FRAME_SLOT],
        ),
        partner_step("receive-on-carved", RECEIVE, FRAME_CAP, 0, [0, 0], true),
        invocation(
            "busy-endpoint-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
    ],
    &[
        invocation(
            "untyped-retype-busy-notification",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                NOTIFICATION_TYPE,
                FINALISED_CHILD_IDS[1],
                CNODE_CAP,
                FRAME_SLOT,
            ],
        ),
        partner_step("wait-on-carved", WAIT, FRAME_CAP, 0, [0, 0], true),
        invocation(
            "busy-notification-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
    ],
    // The final delete of an endpoint a sender is blocked on, and of one a
    // caller is blocked on: the sender pass of the endpoint's queue cancel
    // (seL4's `cancelAllIPC`), which restarts each.
    &[
        invocation(
            "untyped-retype-send-endpoint",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [ENDPOINT_TYPE, FINALISED_CHILD_IDS[0], CNODE_CAP, FRAME_SLOT],
        ),
        partner_step("send-on-carved", SEND, FRAME_CAP, 1, [0x88, 0], true),
        invocation(
            "sender-endpoint-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
    ],
    &[
        invocation(
            "untyped-retype-call-endpoint",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [ENDPOINT_TYPE, FINALISED_CHILD_IDS[0], CNODE_CAP, FRAME_SLOT],
        ),
        partner_step("call-on-carved", CALL, FRAME_CAP, 1, [0x66, 0], true),
        invocation(
            "caller-endpoint-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
    ],
    &[
        invocation(
            "untyped-retype-bound-notification",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                NOTIFICATION_TYPE,
                FINALISED_CHILD_IDS[2],
                CNODE_CAP,
                FRAME_SLOT,
            ],
        ),
        invocation(
            "bind-carved-notification",
            TCB_BIND_NOTIFICATION,
            PARTNER_TCB_CAP,
            [FRAME_CAP, 0, 0, 0],
        ),
        invocation(
            "bound-notification-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
    ],
];

/// A capability invocation with all four message registers inline, which
/// continues its caller.
#[cfg(feature = "hw_target")]
const fn invocation(name: &'static str, syscall: u64, cptr: u64, msg: [u64; 4]) -> RoundTrip {
    RoundTrip {
        name,
        syscall,
        cptr,
        msg_len: 4,
        msg,
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    }
}

/// `KernelError.invalidTypeTag`'s discriminant (`sele4n-types`).
#[cfg(feature = "hw_target")]
const INVALID_TYPE_TAG: u64 = 33;

/// A call past its inline words (WS-UC coverage of the long messages), five
/// words with the root task's IPC buffer mapped: only a five-word invocation
/// reads the overflow words (the `overflowed` route), every other syscall
/// here its inline words alone (its short route).  Each is on a capability
/// whose type the syscall does not take (or, for the untyped calls, with an argument
/// the decode or the object refuses), so the gate or the arm refuses with
/// `code` and changes nothing.
#[cfg(feature = "hw_target")]
const fn overflowed(
    name: &'static str,
    syscall: u64,
    cptr: u64,
    msg_len: u64,
    code: u64,
) -> RoundTrip {
    RoundTrip {
        name,
        syscall,
        cptr,
        msg_len,
        msg: [0; 4],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: refused(code),
    }
}

/// A CNode Copy on the root CNode refused with `returns`, its four words `msg`.
#[cfg(feature = "hw_target")]
const fn cnode_refusal(
    name: &'static str,
    msg: [u64; 4],
    returns: Option<(u64, [Option<u64>; 4])>,
) -> RoundTrip {
    RoundTrip {
        name,
        syscall: CSPACE_COPY,
        cptr: CNODE_CAP,
        msg_len: 4,
        msg,
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns,
    }
}

/// `trip` refused for a second capability whose address misses the root
/// CNode's guard: `seL4_FailedLookup`, not the source, `GuardMismatch` (4),
/// 64 bits left and the root's guard, its width (58) the fifth word, written
/// to the root task's buffer `msg[4]` while the window's frame is that buffer
/// ([`RoundTrip::overflow`], as `failed-lookup-guard-mismatch`).
#[cfg(feature = "hw_target")]
const fn guard_mismatch_refusal(trip: RoundTrip) -> RoundTrip {
    RoundTrip {
        overflow: Some((FRAME_VADDR, 0)),
        returns: refused_with(
            FAILED_LOOKUP,
            5,
            [Some(0), Some(4), Some(64), Some(ROOT_CNODE_GUARD >> 6)],
        ),
        ..trip
    }
}

/// A root slot no scenario fills: the empty source a Copy is refused from.
#[cfg(feature = "hw_target")]
const EMPTY_SOURCE_SLOT: u64 = 48;

/// A root slot no scenario fills: the destination of the empty-source Copy.
/// seL4's `decodeCNodeInvocation` refuses an occupied destination before it
/// looks the source up, and the copy slot still holds the boot audit
/// capability (`AUDIT_SLOT`) when the refusal scenarios run.
#[cfg(feature = "hw_target")]
const EMPTY_DEST_SLOT: u64 = 49;

/// The root slots of the multi-level walk: the root CNode's capability minted
/// with a 52-bit guard, minted with none, and the walk's copy.  None is filled
/// at boot (the boot's own slots end at 36) and each is emptied again.
#[cfg(feature = "hw_target")]
const GUARDED_CNODE_SLOT: u64 = 50;
#[cfg(feature = "hw_target")]
const GUARDLESS_CNODE_SLOT: u64 = 51;
#[cfg(feature = "hw_target")]
const WALK_COPY_SLOT: u64 = 52;

/// A CNode capability's data word (seL4's `seL4_CNode_CapData`): the guard
/// in bits 63:6 and its size in bits 5:0.  The 52-bit guard has its top bit
/// set, so a guarded index is a word `≥ 2^63`.
#[cfg(feature = "hw_target")]
const GUARDED_CNODE_GUARD: u64 = 1 << 51;
#[cfg(feature = "hw_target")]
const GUARDED_CNODE_DATA: u64 = (GUARDED_CNODE_GUARD << 6) | 52;

/// The root CNode's own guard and size as a data word: a SetSpace with it
/// gives the partner's CSpace root the geometry it had.
#[cfg(feature = "hw_target")]
const ROOT_CNODE_DATA: u64 = ((ROOT_CNODE_GUARD >> 6) << 6) | 58;

/// A 64-bit source index through the 52-bit-guarded capability: its guard,
/// then `first` (the guarded level's slot), then `second` (the next level's).
#[cfg(feature = "hw_target")]
const fn guarded_index(first: u64, second: u64) -> u64 {
    (GUARDED_CNODE_GUARD << 12) | (first << 6) | second
}

/// The long send's message length: four words in the sender's registers and
/// two in its IPC buffer's overflow slots 0 and 1, which share a page.
#[cfg(feature = "hw_target")]
const LONG_SEND_LENGTH: u64 = 6;

/// `KernelError.invalidMessageInfo`'s discriminant (`sele4n-types`'
/// `InvalidMessageInfo`), and the refusal frame's `x1` that carries it.
#[cfg(feature = "hw_target")]
const INVALID_MESSAGE_INFO: u64 = 32;
#[cfg(feature = "hw_target")]
const REFUSED_MESSAGE_INFO: Option<(u64, [Option<u64>; 4])> = Some((
    (crate::svc_dispatch::ERROR_LABEL_BASE + INVALID_MESSAGE_INFO) << 12,
    [None; 4],
));

/// `KernelError.truncatedMessage`'s discriminant (`sele4n-types`'
/// `TruncatedMessage`, seL4's `seL4_TruncatedMessage`).
#[cfg(feature = "hw_target")]
const TRUNCATED_MESSAGE: u64 = 58;

/// An invocation `msg_len` words long, shorter than its arguments
/// (`truncationMinimum`), on a capability of the kind it reads them under: the
/// capability is found, then the message refused `TruncatedMessage` before any
/// argument word is read, and nothing changes.
#[cfg(feature = "hw_target")]
const fn truncated(name: &'static str, syscall: u64, cptr: u64, msg_len: u64) -> RoundTrip {
    RoundTrip {
        name,
        syscall,
        cptr,
        msg_len,
        msg: [0; 4],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: refused(TRUNCATED_MESSAGE),
    }
}

/// A message length past the most message registers a message has (120),
/// which the message-info decode refuses.
#[cfg(feature = "hw_target")]
const BAD_MESSAGE_LENGTH: u64 = 127;

/// A one-word message-info word with its top bit set, in a word no `Nat`
/// scalar holds: its label is bits 12-63 (seL4's `seL4_MessageInfo`), so the
/// top bit is a label bit and the decode takes it, as seL4's does.
#[cfg(feature = "hw_target")]
const HIGH_MESSAGE_INFO: u64 = (1 << 63) | 1;

/// The Consumed invocation's success word in `x1`: `MessageInfo` length 1,
/// label 0 (Lean's `consumedInfoWord`).
#[cfg(feature = "hw_target")]
const CONSUMED_INFO_WORD: u64 = 1;

/// The Consumed invocation on the context capability: it must succeed with
/// `x1` the consumed-info word and, when `reading` is given, `x2` that reading.
#[cfg(feature = "hw_target")]
const fn consumed(name: &'static str, reading: Option<u64>) -> RoundTrip {
    RoundTrip {
        name,
        syscall: SCHED_CONTEXT_CONSUMED,
        cptr: SCHED_CONTEXT_CAP,
        msg_len: 0,
        msg: [0; 4],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: Some((CONSUMED_INFO_WORD, [reading, None, None, None])),
    }
}

/// The yieldTo invocation on the context capability (WS-ZA ZA6.29): it must
/// succeed and return the consumed time now, with `x1` the consumed-info word
/// (`setConsumed`'s, as the Consumed invocation's).
#[cfg(feature = "hw_target")]
const fn yield_to(name: &'static str) -> RoundTrip {
    RoundTrip {
        name,
        syscall: SCHED_CONTEXT_YIELD_TO,
        cptr: SCHED_CONTEXT_CAP,
        msg_len: 0,
        msg: [0; 4],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: Some((CONSUMED_INFO_WORD, [None; 4])),
    }
}

/// The scheduling-context configure (WS-ZA ZA6.4): invoked on core 0's
/// scheduling control, the context's capability at MR0, then the budget, the
/// period and the priority-and-domain word (`priority | domain << 8`); the fifth
/// word (the deadline) is read from the root task's IPC buffer, which the
/// kernel's model of memory holds as zero, so deadline 0.
#[cfg(feature = "hw_target")]
const fn configure(name: &'static str, msg: [u64; 4]) -> RoundTrip {
    RoundTrip {
        name,
        syscall: SCHED_CONTEXT_CONFIGURE,
        cptr: SCHED_CONTROL_CAP,
        msg_len: 5,
        msg,
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    }
}

/// The service register: five message words, the fifth (whether invoking the
/// interface needs the grant right) read from the root task's IPC buffer,
/// which the kernel's model of memory holds as zero, so no grant.
#[cfg(feature = "hw_target")]
const fn service_register(name: &'static str, cptr: u64, msg: [u64; 4]) -> RoundTrip {
    RoundTrip {
        name,
        syscall: SERVICE_REGISTER,
        cptr,
        msg_len: 5,
        msg,
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    }
}

/// The interface the `virt` binding installs at boot
/// (`qemuVirtExerciserInterface`, `Platform/QemuVirt/Contract.lean`): id 1,
/// one method, four-word requests and responses.
#[cfg(feature = "hw_target")]
const SERVICE_INTERFACE: [u64; 4] = [1, 1, 4, 4];

/// The object ids the untyped scenarios carve a frame and three page tables
/// at: boot-domain ids no boot object holds.
#[cfg(feature = "hw_target")]
const FRAME_CHILD_ID: u64 = 16;
#[cfg(feature = "hw_target")]
const PAGE_TABLE_CHILD_IDS: [u64; 3] = [17, 18, 19];
/// The ids the passive kinds are carved at, one per kind: an endpoint, a
/// notification, a reply and a CNode, each retired by its capability's delete
/// before the next is carved.
#[cfg(feature = "hw_target")]
const PASSIVE_CHILD_IDS: [u64; 4] = [20, 21, 22, 23];
/// The ids the finalising-delete scenarios carve at: an endpoint a receive
/// blocks on, a notification a wait blocks on, and a notification bound to the
/// partner, each finalised and retired by its only capability's delete.
#[cfg(feature = "hw_target")]
const FINALISED_CHILD_IDS: [u64; 3] = [24, 25, 26];
/// The ids the thread-finalising scenarios carve at: an inactive thread, a
/// thread bound to the boot notification, a scheduling context and the thread
/// it is bound to, and two threads resumed onto one run queue, each finalised
/// and retired by its only capability's delete.
#[cfg(feature = "hw_target")]
const THREAD_CHILD_IDS: [u64; 6] = [27, 28, 29, 30, 31, 32];
/// The ids a VSpace root and a child untyped are carved at, each retired by
/// its only capability's delete before the untyped's reset.
#[cfg(feature = "hw_target")]
const VSPACE_ROOT_CHILD_ID: u64 = 38;
#[cfg(feature = "hw_target")]
const UNTYPED_CHILD_ID: u64 = 39;
/// `KernelObjectType` tags of a thread and a scheduling context, the context's
/// size bits (7: the least the carve takes) in the tag word's upper bits.
#[cfg(feature = "hw_target")]
const TCB_TYPE: u64 = 0;
#[cfg(feature = "hw_target")]
const SCHED_CONTEXT_TYPE: u64 = 6 + (7 << 8);
/// `KernelObjectType` tags of the passive kinds; the CNode's size bits (its
/// radix, 2: four slots) in the tag word's upper bits.
#[cfg(feature = "hw_target")]
const ENDPOINT_TYPE: u64 = 1;
#[cfg(feature = "hw_target")]
const NOTIFICATION_TYPE: u64 = 2;
#[cfg(feature = "hw_target")]
const REPLY_TYPE: u64 = 7;
#[cfg(feature = "hw_target")]
const CNODE_TYPE: u64 = 3 + (2 << 8);
/// `KernelObjectType` tags of a frame and a page table, each one page (size
/// bits 0 in the tag word's upper bits).
#[cfg(feature = "hw_target")]
const FRAME_TYPE: u64 = 8;
#[cfg(feature = "hw_target")]
const PAGE_TABLE_TYPE: u64 = 9;
/// `KernelObjectType` tags of a VSpace root (one page, size bits 0) and a
/// child untyped, its size bits (12, one page: `minUntypedSizeBits`) in the
/// tag word's upper bits.
#[cfg(feature = "hw_target")]
const VSPACE_ROOT_TYPE: u64 = 4;
#[cfg(feature = "hw_target")]
const UNTYPED_TYPE: u64 = 5 + (12 << 8);
/// A child untyped of 2^46 bytes, more than any region the exerciser holds:
/// the carve the region refuses (`untyped-retype-region-exhausted`).
#[cfg(feature = "hw_target")]
const UNTYPED_REGION_EXHAUSTED_TYPE: u64 = 5 + (46 << 8);
/// The root task's ASID and the user address the frame is mapped at: the
/// first page of the user window (`VAddr.userWindowBase`, 2^39), whose walk
/// the three page tables complete.
#[cfg(feature = "hw_target")]
const ROOT_ASID: u64 = 1;
#[cfg(feature = "hw_target")]
const FRAME_VADDR: u64 = 1 << 39;
/// The page after it, where the frame's copy is mapped before the revoke that
/// destroys the copy and so unmaps it.
#[cfg(feature = "hw_target")]
const FRAME_COPY_VADDR: u64 = FRAME_VADDR + 0x1000;
/// An IPC buffer in the frame's last 1024 bytes (`ipcBufferAlignment`, the
/// buffer's size, seL4's 128-word `seL4_IPCBuffer`): its last word,
/// `receiveDepth`, is the page's last, so a full-length message reads and
/// writes the whole overflow region (`msg[4..120]`) on the frame.
#[cfg(feature = "hw_target")]
const TAIL_IPC_BUFFER: u64 = FRAME_VADDR + 0x1000 - 0x400;
/// An address 512 bytes short of the frame's end: aligned to 512 but not to
/// 1024, so a buffer there would cross the page.  The validator refuses it.
#[cfg(feature = "hw_target")]
const HALF_ALIGNED_IPC_BUFFER: u64 = FRAME_VADDR + 0x1000 - 0x200;
/// A full-length message: four words in registers, 116 in overflow slots.
#[cfg(feature = "hw_target")]
const TAIL_MESSAGE_LENGTH: u64 = 120;
/// A message-info word's one extra capability (seL4's `extraCaps`, bits 7..8).
#[cfg(feature = "hw_target")]
const ONE_EXTRA_CAP: u64 = 1 << 7;
/// Three capabilities, the most a message carries (`seL4_MsgMaxExtraCaps`).
#[cfg(feature = "hw_target")]
const THREE_EXTRA_CAPS: u64 = 3 << 7;
/// The root CNode slot a capability transfer's receive path names, free while
/// the transfer scenarios run.
#[cfg(feature = "hw_target")]
const TRANSFER_RECEIVE_SLOT: u64 = 27;
/// The root CNode slot an endpoint capability without the grant right is
/// minted into for the no-grant transfer scenario, free while it runs.
#[cfg(feature = "hw_target")]
const NO_GRANT_ENDPOINT_SLOT: u64 = 21;
#[cfg(feature = "hw_target")]
const NO_GRANT_ENDPOINT_CAP: u64 = cap_address(NO_GRANT_ENDPOINT_SLOT);
/// Read and write without grant, as a mint's rights word.
#[cfg(feature = "hw_target")]
const READ_WRITE_RIGHTS: u64 = 0x3;
/// Write alone, as a mint's rights word: an endpoint capability that may send
/// and may not receive.
#[cfg(feature = "hw_target")]
const WRITE_ONLY_RIGHTS: u64 = 0x2;
/// `KernelError.alignmentError`'s discriminant (`sele4n-types`'
/// `AlignmentError`), and the refusal frame's `x1` that carries it.
#[cfg(feature = "hw_target")]
const ALIGNMENT_ERROR: u64 = 43;
/// Read, write, user and cacheable (`PagePermissions.ofNat`).
#[cfg(feature = "hw_target")]
const FRAME_PERMS: u64 = 0b11011;
/// The scheduling context's budget and period (one tenth of the processor)
/// and its priority: the partner's, as the TCB scenarios leave it, since a
/// bind writes the reservation's priority into the bound thread and the
/// unbind keeps it.
#[cfg(feature = "hw_target")]
const SCHED_CONTEXT_BUDGET: u64 = 1_000;
#[cfg(feature = "hw_target")]
const SCHED_CONTEXT_PERIOD: u64 = 10_000;
#[cfg(feature = "hw_target")]
const PARTNER_PRIORITY: u64 = 255;

/// The capability invocations outside IPC (WS-ZA ZA5.1), each sequence issued
/// by the root task with the partner suspended, and each leaving the state it
/// found, so its second run is its steady state:
/// - a copy, a move of the copy and a delete of it;
/// - a mint of a badged copy and a revoke of the source that destroys it;
/// - the reply capability deleted and minted again from the reply object;
/// - the partner thread's priority, maximum priority, affinity and fault
///   handler set, a notification bound to it and unbound, its CSpace and
///   VSpace set while it is suspended, then resumed and suspended;
/// - three page tables carved from the untyped and installed in the root
///   task's VSpace, one per level of the walk to the frame's address; a frame
///   carved, mapped, its instruction cache unified, its mapped capability
///   copied (the copy records no mapping) and the copy deleted, copied
///   again, the copy mapped at the next page and the frame's capability
///   revoked, which destroys the copy and unmaps that page, a reply
///   capability minted over the record the copy left (its target shared with
///   the frame's capability) and deleted, named as the partner's IPC buffer,
///   unmapped and deleted; the tables taken out deepest first and
///   deleted; the interrupt-control capability copied, and minted with its
///   own rights, with none and with a badge, into the frame's slot, each
///   deleted; an endpoint, a notification, a reply and a CNode each carved
///   and its only capability deleted, which retires it; and the untyped
///   reset.  While the frame is mapped it is also the
///   root task's IPC buffer, and the image's scheduling context is first
///   configured to a one-tick budget every two ticks and bound to the root
///   task, which yields its budget away and is refilled by the second of two
///   kernel-entered timer ticks (the timer masked across them) and unbound;
///   then configured (its fifth word read from that buffer), bound to the
///   suspended partner and unbound, then bound again and held while the partner is resumed and
///   suspended, which leaves it bound (seL4's suspend unbinds nothing), and
///   unbound.  A service is registered on the image's
///   endpoint against the interface the boot installs (its fifth word read
///   from that buffer), queried and revoked.
#[cfg(feature = "hw_target")]
const INVOCATION_SCENARIOS: [&[RoundTrip]; 9] = [
    &[
        invocation(
            "cspace-copy",
            CSPACE_COPY,
            CNODE_CAP,
            root_slot_copy(NOTIFICATION_SLOT, COPY_SLOT),
        ),
        invocation(
            "cspace-move",
            CSPACE_MOVE,
            CNODE_CAP,
            root_slot_pair(COPY_SLOT, MOVE_SLOT),
        ),
        invocation(
            "cspace-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [MOVE_SLOT, 0, 0, 0],
        ),
    ],
    &[
        mint(
            "cspace-mint",
            NOTIFICATION_SLOT,
            MINT_SLOT,
            READ_WRITE_RIGHTS,
            5,
            ROOT_IPC_BUFFER,
        ),
        invocation(
            "cspace-revoke",
            CSPACE_REVOKE,
            CNODE_CAP,
            [NOTIFICATION_SLOT, 0, 0, 0],
        ),
    ],
    // seL4's `updateCapData` under Mint and `resolveAddressBits` over more
    // than one level: the root CNode's capability minted with a 52-bit guard
    // (its top bit set) and with none, so a source index of the guard, the
    // guardless capability's slot and a slot of the second level resolves
    // through both to the notification, which is copied out and the copy
    // deleted; an index naming the notification at the first level stops
    // there with six bits left, a depth mismatch for a CNode operation
    // (`lookupSlotForCNodeOp`).  Then a badged endpoint capability minted
    // again with another badge, and with data zero, both refused (seL4's
    // `updateCapData` answers a null capability for a badged endpoint,
    // `IllegalOperation`): a badge is never rewritten nor stripped.
    &[
        mint(
            "cnode-mint-guard",
            CNODE_SLOT,
            GUARDED_CNODE_SLOT,
            ALL_RIGHTS,
            GUARDED_CNODE_DATA,
            ROOT_IPC_BUFFER,
        ),
        mint(
            "cnode-mint-guardless",
            CNODE_SLOT,
            GUARDLESS_CNODE_SLOT,
            ALL_RIGHTS,
            0,
            ROOT_IPC_BUFFER,
        ),
        invocation(
            "cnode-multi-level-copy",
            CSPACE_COPY,
            CNODE_CAP,
            [
                cap_address(WALK_COPY_SLOT),
                cap_address(GUARDED_CNODE_SLOT),
                guarded_index(GUARDLESS_CNODE_SLOT, NOTIFICATION_SLOT),
                ROOT_SLOT_DEPTHS | (ALL_RIGHTS << 16),
            ],
        ),
        invocation(
            "cnode-multi-level-copy-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [WALK_COPY_SLOT, 0, 0, 0],
        ),
        cnode_refusal(
            "lookup-stops-at-non-cnode",
            [
                cap_address(WALK_COPY_SLOT),
                cap_address(GUARDED_CNODE_SLOT),
                guarded_index(NOTIFICATION_SLOT, 0),
                ROOT_SLOT_DEPTHS | (ALL_RIGHTS << 16),
            ],
            // The source; DepthMismatch (3), six bits left, none found.
            refused_with(FAILED_LOOKUP, 4, [Some(1), Some(3), Some(6), Some(0)]),
        ),
        invocation(
            "cnode-mint-guardless-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [GUARDLESS_CNODE_SLOT, 0, 0, 0],
        ),
        invocation(
            "cnode-mint-guard-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [GUARDED_CNODE_SLOT, 0, 0, 0],
        ),
        mint(
            "cnode-mint-badged-endpoint",
            ENDPOINT_SLOT,
            GUARDED_CNODE_SLOT,
            ALL_RIGHTS,
            5,
            ROOT_IPC_BUFFER,
        ),
        RoundTrip {
            returns: refused(ILLEGAL_STATE),
            ..mint(
                "cnode-mint-rebadge-refused",
                GUARDED_CNODE_SLOT,
                GUARDLESS_CNODE_SLOT,
                ALL_RIGHTS,
                6,
                ROOT_IPC_BUFFER,
            )
        },
        RoundTrip {
            returns: refused(ILLEGAL_STATE),
            ..mint(
                "cnode-mint-unbadge-refused",
                GUARDED_CNODE_SLOT,
                GUARDLESS_CNODE_SLOT,
                ALL_RIGHTS,
                0,
                ROOT_IPC_BUFFER,
            )
        },
        invocation(
            "cnode-mint-badged-endpoint-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [GUARDED_CNODE_SLOT, 0, 0, 0],
        ),
    ],
    &[
        invocation(
            "reply-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [REPLY_OBJECT_SLOT, REPLY_CAP_SLOT, 0, 0],
        ),
    ],
    &[
        invocation(
            "tcb-set-priority",
            TCB_SET_PRIORITY,
            PARTNER_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "tcb-set-mc-priority",
            TCB_SET_MC_PRIORITY,
            PARTNER_TCB_CAP,
            [255, 0, 0, 0],
        ),
        invocation(
            "tcb-set-affinity",
            TCB_SET_AFFINITY,
            PARTNER_TCB_CAP,
            [0, 0, 0, 0],
        ),
        invocation(
            "tcb-set-fault-handler",
            TCB_SET_FAULT_HANDLER,
            PARTNER_TCB_CAP,
            [ENDPOINT_CAP, 0, 0, 0],
        ),
        invocation(
            "tcb-bind-notification",
            TCB_BIND_NOTIFICATION,
            PARTNER_TCB_CAP,
            [NOTIFICATION_CAP, 0, 0, 0],
        ),
        invocation(
            "tcb-unbind-notification",
            TCB_UNBIND_NOTIFICATION,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "tcb-set-space",
            TCB_SET_SPACE,
            PARTNER_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        // The CSpace root's guard taken from `cspace_root_data` (seL4's
        // `updateCapData` in `decodeSetSpace`): the root's own 58-bit guard,
        // so the partner's addresses resolve as before; then a guard size
        // that does not fit beside the radix, refused.
        invocation(
            "set-space-root-data",
            TCB_SET_SPACE,
            PARTNER_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, ROOT_CNODE_DATA, 0],
        ),
        RoundTrip {
            returns: refused(ILLEGAL_STATE),
            ..invocation(
                "set-space-root-data-refused",
                TCB_SET_SPACE,
                PARTNER_TCB_CAP,
                [CNODE_CAP, VSPACE_CAP, 59, 0],
            )
        },
        invocation("tcb-resume", TCB_RESUME, PARTNER_TCB_CAP, [0; 4]),
        invocation("tcb-suspend", TCB_SUSPEND, PARTNER_TCB_CAP, [0; 4]),
    ],
    // WS-ZA ZA5.4 part 24: a carved thread's last capability deleted while it
    // is inactive, and while it is bound to the boot notification; a carved
    // scheduling context's while it is bound to a carved thread, then that
    // thread's; a carved thread's once it is suspended off a run queue it
    // shared; and a carved thread's while it is queued to run.  Each delete
    // finalises its object (seL4's `finaliseCap`) and retires it.
    &[
        invocation(
            "untyped-retype-tcb",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, THREAD_CHILD_IDS[0], CNODE_CAP, FRAME_SLOT],
        ),
        invocation(
            "inactive-tcb-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-bound-tcb",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, THREAD_CHILD_IDS[1], CNODE_CAP, FRAME_SLOT],
        ),
        invocation(
            "bind-carved-tcb",
            TCB_BIND_NOTIFICATION,
            FRAME_CAP,
            [NOTIFICATION_CAP, 0, 0, 0],
        ),
        invocation(
            "bound-tcb-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-sched-context",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                SCHED_CONTEXT_TYPE,
                THREAD_CHILD_IDS[2],
                CNODE_CAP,
                MINT_SLOT,
            ],
        ),
        invocation(
            "untyped-retype-sc-thread",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, THREAD_CHILD_IDS[3], CNODE_CAP, FRAME_SLOT],
        ),
        invocation(
            "bind-carved-sched-context",
            SCHED_CONTEXT_BIND,
            MINT_CAP,
            [FRAME_CAP, 0, 0, 0],
        ),
        invocation(
            "bound-sched-context-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [MINT_SLOT, 0, 0, 0],
        ),
        invocation(
            "unbound-tcb-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        // Two carved threads resumed, so queued one behind the other where
        // their placement puts them; the first suspended, which takes it off
        // that queue and leaves it no run link, then its last capability
        // deleted, which retires it (the steady-state run carves its id
        // again); then the second's, which the finalisation suspends, taking
        // it off the queue in place, and retires.
        invocation(
            "untyped-retype-queued-tcb",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, THREAD_CHILD_IDS[4], CNODE_CAP, FRAME_SLOT],
        ),
        invocation("resume-carved-tcb", TCB_RESUME, FRAME_CAP, [0; 4]),
        invocation(
            "untyped-retype-shared-tcb",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, THREAD_CHILD_IDS[5], CNODE_CAP, MINT_SLOT],
        ),
        invocation("resume-shared-tcb", TCB_RESUME, MINT_CAP, [0; 4]),
        invocation("suspend-queued-tcb", TCB_SUSPEND, FRAME_CAP, [0; 4]),
        invocation(
            "suspended-tcb-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        invocation(
            "queued-tcb-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [MINT_SLOT, 0, 0, 0],
        ),
    ],
    // WS-ZA ZA6.33: seL4's suspend of a blocked thread (`cancelIPC`, then
    // `tcbSchedDequeue`, `tcbReleaseRemove`, `schedContext_cancelYieldTo` and
    // `Inactive`), run as the root task: the partner resumed, the root task's
    // receive that blocks so the partner runs, the partner's send that wakes
    // it, and the partner's own blocking step, which leaves the root task
    // current; then the suspend.  Each arm's cancel writes its queue and the
    // partner's links in their slots, so the second run finds the state the
    // first did.  The timer is masked across the sequence, so no tick
    // switches the two threads between steps and the roles stay fixed.  The
    // partner blocked on a receive:
    &[
        kernel_step("mask-ticks", MASK_TICKS_STEP),
        invocation("suspend-recv-resume", TCB_RESUME, PARTNER_TCB_CAP, [0; 4]),
        partner_step(
            "suspend-recv-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            true,
        ),
        partner_step(
            "suspend-recv-wake-root",
            SEND,
            ENDPOINT_CAP,
            1,
            [0x55, 0],
            false,
        ),
        partner_step(
            "suspend-recv-partner-receives",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "tcb-suspend-receive-blocked",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // ...on a send:
        invocation("suspend-send-resume", TCB_RESUME, PARTNER_TCB_CAP, [0; 4]),
        partner_step(
            "suspend-send-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            true,
        ),
        partner_step(
            "suspend-send-wake-root",
            SEND,
            ENDPOINT_CAP,
            1,
            [0x55, 0],
            false,
        ),
        partner_step(
            "suspend-send-partner-sends",
            SEND,
            ENDPOINT_CAP,
            1,
            [0x88, 0],
            true,
        ),
        invocation(
            "tcb-suspend-send-blocked",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // ...on the notification wait:
        invocation("suspend-wait-resume", TCB_RESUME, PARTNER_TCB_CAP, [0; 4]),
        partner_step(
            "suspend-wait-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            true,
        ),
        partner_step(
            "suspend-wait-wake-root",
            SEND,
            ENDPOINT_CAP,
            1,
            [0x55, 0],
            false,
        ),
        partner_step(
            "suspend-wait-partner-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "tcb-suspend-wait-blocked",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // ...and on the reply, its call taken by the root task's receive through
        // the reply capability: the suspend's reply arm is seL4's
        // `reply_remove_tcb`, which unlinks the reply from the caller.
        invocation("suspend-reply-resume", TCB_RESUME, PARTNER_TCB_CAP, [0; 4]),
        partner_step(
            "suspend-reply-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "suspend-reply-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x66, 0],
            true,
        ),
        invocation(
            "tcb-suspend-reply-blocked",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        kernel_step("unmask-ticks", UNMASK_TICKS_STEP),
    ],
    &[
        invocation(
            "untyped-retype-page-table-1",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                PAGE_TABLE_TYPE,
                PAGE_TABLE_CHILD_IDS[0],
                CNODE_CAP,
                PAGE_TABLE_SLOTS[0],
            ],
        ),
        invocation(
            "page-table-map-1",
            PAGE_TABLE_MAP,
            PAGE_TABLE_CAPS[0],
            [VSPACE_CAP, FRAME_VADDR, 0, 0],
        ),
        invocation(
            "untyped-retype-page-table-2",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                PAGE_TABLE_TYPE,
                PAGE_TABLE_CHILD_IDS[1],
                CNODE_CAP,
                PAGE_TABLE_SLOTS[1],
            ],
        ),
        invocation(
            "page-table-map-2",
            PAGE_TABLE_MAP,
            PAGE_TABLE_CAPS[1],
            [VSPACE_CAP, FRAME_VADDR, 0, 0],
        ),
        invocation(
            "untyped-retype-page-table-3",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                PAGE_TABLE_TYPE,
                PAGE_TABLE_CHILD_IDS[2],
                CNODE_CAP,
                PAGE_TABLE_SLOTS[2],
            ],
        ),
        invocation(
            "page-table-map-3",
            PAGE_TABLE_MAP,
            PAGE_TABLE_CAPS[2],
            [VSPACE_CAP, FRAME_VADDR, 0, 0],
        ),
        invocation(
            "untyped-retype-frame",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [FRAME_TYPE, FRAME_CHILD_ID, CNODE_CAP, FRAME_SLOT],
        ),
        invocation(
            "vspace-map",
            VSPACE_MAP,
            VSPACE_CAP,
            [ROOT_ASID, FRAME_VADDR, FRAME_CAP, FRAME_PERMS],
        ),
        // The first page unmap after boot, before any teardown has retired a
        // shootdown round: the round writes over the spares the boot seeded.
        // Then the frame mapped again over the cells that unmap took out.
        invocation(
            "vspace-unmap-first",
            VSPACE_UNMAP,
            VSPACE_CAP,
            [ROOT_ASID, FRAME_VADDR, 0, 0],
        ),
        invocation(
            "vspace-map-again",
            VSPACE_MAP,
            VSPACE_CAP,
            [ROOT_ASID, FRAME_VADDR, FRAME_CAP, FRAME_PERMS],
        ),
        invocation(
            "vspace-unify-instruction",
            VSPACE_UNIFY_INSTRUCTION,
            VSPACE_CAP,
            [ROOT_ASID, FRAME_VADDR, 0, 0],
        ),
        invocation(
            "frame-copy-mapped",
            CSPACE_COPY,
            CNODE_CAP,
            root_slot_copy(FRAME_SLOT, MOVE_SLOT),
        ),
        invocation(
            "frame-copy-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [MOVE_SLOT, 0, 0, 0],
        ),
        invocation(
            "frame-copy-for-revoke",
            CSPACE_COPY,
            CNODE_CAP,
            root_slot_copy(FRAME_SLOT, MOVE_SLOT),
        ),
        invocation(
            "vspace-map-copy",
            VSPACE_MAP,
            VSPACE_CAP,
            [ROOT_ASID, FRAME_COPY_VADDR, MOVE_CAP, FRAME_PERMS],
        ),
        invocation(
            "frame-revoke",
            CSPACE_REVOKE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        invocation(
            "reply-cap-mint-over-copy",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [REPLY_OBJECT_SLOT, MOVE_SLOT, 0, 0],
        ),
        invocation(
            "reply-cap-over-copy-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [MOVE_SLOT, 0, 0, 0],
        ),
        invocation(
            "tcb-set-ipc-buffer",
            TCB_SET_IPC_BUFFER,
            PARTNER_TCB_CAP,
            [FRAME_VADDR, 0, 0, 0],
        ),
        invocation(
            "root-set-ipc-buffer",
            TCB_SET_IPC_BUFFER,
            ROOT_TCB_CAP,
            [FRAME_VADDR, 0, 0, 0],
        ),
        // WS-ZA ZA6.2: a tick that drains a due refill.  The context is
        // configured to a one-tick budget every two ticks and bound to the
        // root task, which yields: the forfeit spends the budget and queues
        // its refill two ticks on, the yield returns its frame to the root
        // task (ready, but ineligible), and core 0 runs its idle thread.  The
        // first tick finds nothing due; the second drains the refill, which
        // makes the root task eligible again, and the tick's own decision
        // (the flag the refill raised) switches back to it, which the unbind
        // then runs as.  No real tick may come between the bind and the
        // drain, so the timer is masked across them.
        kernel_step("mask-ticks", MASK_TICKS_STEP),
        configure(
            "refill-configure",
            [
                SCHED_CONTEXT_CAP,
                REFILL_BUDGET,
                REFILL_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        invocation(
            "refill-bind-root",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [ROOT_TCB_CAP, 0, 0, 0],
        ),
        RoundTrip {
            name: "refill-yield",
            syscall: YIELD,
            cptr: 0,
            msg_len: 0,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        kernel_step("refill-wait-tick", TIMER_TICK_STEP),
        kernel_step("refill-drain-tick", TIMER_TICK_STEP),
        // WS-ZA ZA6.3: a tick that exhausts a bound budget.  The drain left the
        // root task current with its one-tick budget refilled; the next tick
        // charges it, exhausts it, queues its refill (the context linked into
        // core 0's release queue in place) and runs the idle thread.  Under
        // seL4's refill semantics (WS-ZA ZA6.4) the used refill is due one
        // period after it was released, which is the next tick: that tick
        // drains it and switches back to the root task, as above.
        kernel_step("exhaust-tick", TIMER_TICK_STEP),
        kernel_step("exhaust-drain-tick", TIMER_TICK_STEP),
        kernel_step("unmask-ticks", UNMASK_TICKS_STEP),
        invocation(
            "refill-unbind-root",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        configure(
            "sched-context-configure",
            [
                SCHED_CONTEXT_CAP,
                SCHED_CONTEXT_BUDGET,
                SCHED_CONTEXT_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        service_register("service-register", ENDPOINT_CAP, SERVICE_INTERFACE),
        invocation("service-query", SERVICE_QUERY, ENDPOINT_CAP, [0; 4]),
        invocation("service-revoke", SERVICE_REVOKE, ENDPOINT_CAP, [0; 4]),
        // A carved endpoint registered as the service, then its only
        // capability deleted: the final delete drops the registration
        // (`releaseFinalRegistration`, seL4's endpoint finalisation with the
        // registry's back-link) and retires the endpoint.
        invocation(
            "untyped-retype-registered-endpoint",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [ENDPOINT_TYPE, PASSIVE_CHILD_IDS[0], CNODE_CAP, MINT_SLOT],
        ),
        service_register("registered-endpoint-register", MINT_CAP, SERVICE_INTERFACE),
        invocation(
            "registered-endpoint-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [MINT_SLOT, 0, 0, 0],
        ),
        // The long, short-argument and refused forms, each routed past the
        // named syscalls, the root task's IPC buffer mapped for the words
        // past the fourth: every invocation one word shorter than its
        // arguments (`truncationMinimum`), refused `TruncatedMessage` once its
        // capability is found (seL4's `seL4_TruncatedMessage`; the interrupt
        // invocations' are measured where their capabilities exist,
        // `interrupt_handlers_issued`); a configure one word long; a signal
        // and a wait one word long, the wait taking the badge the signal
        // left; an invocation one word long; a message-info word whose length
        // no message has, refused; one whose top bit is set, refused; and a
        // yield one word long.
        truncated("service-register-short", SERVICE_REGISTER, ENDPOINT_CAP, 4),
        truncated(
            "sched-context-configure-short",
            SCHED_CONTEXT_CONFIGURE,
            SCHED_CONTROL_CAP,
            4,
        ),
        // seL4's error payloads (`setMRs_syscall_error`), each a Copy
        // refused before any write: a destination depth
        // past 64 (`RangeError(1, 64)`), a destination index whose guard
        // matches but whose depth stops inside the root's level (a depth
        // mismatch), an empty source (`MissingCapability`, seL4's
        // `cnode.c`), and a destination index whose guard bits differ (a
        // guard mismatch, five words, the fifth written to the root task's
        // IPC buffer `msg[4]` and counted in the length).
        cnode_refusal(
            "range-error-payload",
            [
                cap_address(COPY_SLOT),
                cap_address(CNODE_SLOT),
                cap_address(NOTIFICATION_SLOT),
                65 | (64 << 8) | (ALL_RIGHTS << 16),
            ],
            refused_with(RANGE_ERROR, 2, [Some(1), Some(64), None, None]),
        ),
        cnode_refusal(
            "failed-lookup-depth-mismatch",
            [
                ROOT_CNODE_GUARD >> 4,
                cap_address(CNODE_SLOT),
                cap_address(NOTIFICATION_SLOT),
                60 | (64 << 8) | (ALL_RIGHTS << 16),
            ],
            // Not the source; DepthMismatch (3), 60 bits left, the level's 64.
            refused_with(FAILED_LOOKUP, 4, [Some(0), Some(3), Some(60), Some(64)]),
        ),
        cnode_refusal(
            "failed-lookup-missing-source",
            root_slot_copy(EMPTY_SOURCE_SLOT, EMPTY_DEST_SLOT),
            // The source; MissingCapability (2), the source's depth, 64.
            refused_with(FAILED_LOOKUP, 3, [Some(1), Some(2), Some(64), None]),
        ),
        // The fifth word lands in the root task's buffer `msg[4]`, the word
        // a later five-word call (a configure's deadline, a service
        // register's grant flag) reads as its argument, so the round trip
        // names the buffer ([`RoundTrip::overflow`]) and the word goes back
        // to the boot's zero after the measured window.  The root task's
        // buffer here is the window's frame ([`FRAME_VADDR`]), where
        // `root-set-ipc-buffer` pointed it; the tail's configures read the
        // same page once `tail-root-ipc-buffer-back` points it there again.
        RoundTrip {
            overflow: Some((FRAME_VADDR, 0)),
            ..cnode_refusal(
                "failed-lookup-guard-mismatch",
                [
                    COPY_SLOT,
                    cap_address(CNODE_SLOT),
                    cap_address(NOTIFICATION_SLOT),
                    ROOT_SLOT_DEPTHS | (ALL_RIGHTS << 16),
                ],
                // Not the source; GuardMismatch (4), 64 bits left, the root's
                // guard; its width (58) is the fifth word, in the buffer.
                refused_with(
                    FAILED_LOOKUP,
                    5,
                    [Some(0), Some(4), Some(64), Some(ROOT_CNODE_GUARD >> 6)],
                ),
            )
        },
        // A second capability whose address misses the root CNode's guard,
        // one per arm that resolves one (seL4's `lookupCap` of an argument,
        // `seL4_FailedLookup` with the guard-mismatch words): the configure's
        // scheduling context (the `.overflowOne` route), and the SetSpace
        // CSpace root and the bound notification an invocation resolves.
        // Each is refused before anything changes, its fifth word in the
        // buffer as above.  A receive's reply capability is not here: its
        // failed lookup is the receive's capability fault (seL4-MCS
        // `lookupReply`), which `receive_side_faults` reaches.
        guard_mismatch_refusal(configure(
            "configure-sched-context-guard-mismatch",
            [
                SCHED_CONTEXT_SLOT,
                SCHED_CONTEXT_BUDGET,
                SCHED_CONTEXT_PERIOD,
                PARTNER_PRIORITY,
            ],
        )),
        guard_mismatch_refusal(invocation(
            "set-space-root-guard-mismatch",
            TCB_SET_SPACE,
            PARTNER_TCB_CAP,
            [CNODE_SLOT, VSPACE_CAP, 0, 0],
        )),
        guard_mismatch_refusal(invocation(
            "bind-notification-guard-mismatch",
            TCB_BIND_NOTIFICATION,
            PARTNER_TCB_CAP,
            [NOTIFICATION_SLOT, 0, 0, 0],
        )),
        // Argument words at or above `2^63`, each refused on the word before
        // it is made a number: an ASID past the configured bound
        // (`AsidNotBound`), an address past the canonical bound
        // (`AddressOutOfBounds`), a permission word past five bits
        // (`InvalidSyscallArgument`), and an affinity past the cores and the
        // unbind marker (`InvalidArgument 0`).
        RoundTrip {
            returns: refused(ASID_NOT_BOUND),
            ..invocation(
                "vspace-map-wide-asid",
                VSPACE_MAP,
                VSPACE_CAP,
                [WIDE_WORD, FRAME_VADDR, FRAME_CAP, FRAME_PERMS],
            )
        },
        RoundTrip {
            returns: refused(ADDRESS_OUT_OF_BOUNDS),
            ..invocation(
                "vspace-map-wide-vaddr",
                VSPACE_MAP,
                VSPACE_CAP,
                [ROOT_ASID, WIDE_WORD, FRAME_CAP, FRAME_PERMS],
            )
        },
        RoundTrip {
            returns: refused(INVALID_SYSCALL_ARGUMENT),
            ..invocation(
                "vspace-map-wide-perms",
                VSPACE_MAP,
                VSPACE_CAP,
                [ROOT_ASID, FRAME_VADDR, FRAME_CAP, WIDE_WORD],
            )
        },
        RoundTrip {
            returns: refused(ADDRESS_OUT_OF_BOUNDS),
            ..invocation(
                "vspace-unmap-wide-vaddr",
                VSPACE_UNMAP,
                VSPACE_CAP,
                [ROOT_ASID, WIDE_WORD, 0, 0],
            )
        },
        RoundTrip {
            returns: refused_with(INVALID_ARGUMENT, 1, [Some(0), None, None, None]),
            ..invocation(
                "tcb-set-affinity-wide",
                TCB_SET_AFFINITY,
                ROOT_TCB_CAP,
                [WIDE_WORD, 0, 0, 0],
            )
        },
        truncated("cspace-mint-short", CSPACE_MINT, CNODE_CAP, 4),
        truncated("cspace-copy-short", CSPACE_COPY, CNODE_CAP, 1),
        truncated("cspace-move-short", CSPACE_MOVE, CNODE_CAP, 1),
        truncated("cspace-delete-short", CSPACE_DELETE, CNODE_CAP, 0),
        truncated("cspace-revoke-short", CSPACE_REVOKE, CNODE_CAP, 0),
        truncated("mint-reply-cap-short", MINT_REPLY_CAP, CNODE_CAP, 1),
        truncated("untyped-retype-short", UNTYPED_RETYPE, UNTYPED_CAP, 3),
        truncated("vspace-map-short", VSPACE_MAP, VSPACE_CAP, 3),
        truncated("vspace-unmap-short", VSPACE_UNMAP, VSPACE_CAP, 1),
        truncated(
            "vspace-unify-instruction-short",
            VSPACE_UNIFY_INSTRUCTION,
            VSPACE_CAP,
            1,
        ),
        truncated(
            "page-table-map-short",
            PAGE_TABLE_MAP,
            PAGE_TABLE_CAPS[0],
            1,
        ),
        truncated(
            "sched-context-bind-short",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            0,
        ),
        truncated(
            "tcb-bind-notification-short",
            TCB_BIND_NOTIFICATION,
            PARTNER_TCB_CAP,
            0,
        ),
        truncated(
            "tcb-set-priority-short",
            TCB_SET_PRIORITY,
            PARTNER_TCB_CAP,
            0,
        ),
        truncated(
            "tcb-set-mc-priority-short",
            TCB_SET_MC_PRIORITY,
            PARTNER_TCB_CAP,
            0,
        ),
        truncated(
            "tcb-set-ipc-buffer-short",
            TCB_SET_IPC_BUFFER,
            PARTNER_TCB_CAP,
            0,
        ),
        truncated(
            "tcb-set-affinity-short",
            TCB_SET_AFFINITY,
            PARTNER_TCB_CAP,
            0,
        ),
        truncated(
            "tcb-set-fault-handler-short",
            TCB_SET_FAULT_HANDLER,
            PARTNER_TCB_CAP,
            0,
        ),
        truncated("tcb-set-space-short", TCB_SET_SPACE, PARTNER_TCB_CAP, 2),
        RoundTrip {
            msg_len: 6,
            ..configure(
                "sched-context-configure-long",
                [
                    SCHED_CONTEXT_CAP,
                    SCHED_CONTEXT_BUDGET,
                    SCHED_CONTEXT_PERIOD,
                    PARTNER_PRIORITY,
                ],
            )
        },
        RoundTrip {
            msg_len: 5,
            ..signal("signal-long-message")
        },
        RoundTrip {
            name: "wait-long-message",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: 5,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        RoundTrip {
            msg_len: 5,
            ..invocation(
                "invocation-long-message",
                TCB_SET_MC_PRIORITY,
                PARTNER_TCB_CAP,
                [255, 0, 0, 0],
            )
        },
        RoundTrip {
            caps_or_badges: None,
            overflow: None,
            returns: REFUSED_MESSAGE_INFO,
            msg_len: BAD_MESSAGE_LENGTH,
            ..signal("bad-message-info")
        },
        RoundTrip {
            caps_or_badges: None,
            overflow: None,
            msg_len: HIGH_MESSAGE_INFO,
            ..signal("high-message-info")
        },
        RoundTrip {
            name: "yield-long-message",
            syscall: YIELD,
            cptr: 0,
            msg_len: 5,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        // Every other syscall with a message past its inline words, five
        // words (six for the service register, whose fifth is its own
        // argument, routed `overflowed`; the rest read their inline words
        // alone), each on a capability of a type it does
        // not take, so the gate refuses it `InvalidCapability` before any
        // right and changes nothing (the receive's, a fault, is queued with
        // the other capability faults, `overflow_cap_faults`): the untyped reset
        // on the untyped while its frame child lives, the declassifications on
        // the boot endpoint, whose flow the base lattice already permits.
        overflowed(
            "overflowed-cspace-mint",
            CSPACE_MINT,
            NOTIFICATION_CAP,
            6,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-cspace-copy",
            CSPACE_COPY,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-cspace-move",
            CSPACE_MOVE,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-cspace-delete",
            CSPACE_DELETE,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-cspace-revoke",
            CSPACE_REVOKE,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-vspace-map",
            VSPACE_MAP,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-vspace-unmap",
            VSPACE_UNMAP,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-vspace-unify-instruction",
            VSPACE_UNIFY_INSTRUCTION,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-service-revoke",
            SERVICE_REVOKE,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-service-query",
            SERVICE_QUERY,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-sched-context-bind",
            SCHED_CONTEXT_BIND,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-sched-context-unbind",
            SCHED_CONTEXT_UNBIND,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-sched-context-consumed",
            SCHED_CONTEXT_CONSUMED,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-sched-context-yield-to",
            SCHED_CONTEXT_YIELD_TO,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-tcb-suspend",
            TCB_SUSPEND,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-tcb-resume",
            TCB_RESUME,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-tcb-set-priority",
            TCB_SET_PRIORITY,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-tcb-set-ipc-buffer",
            TCB_SET_IPC_BUFFER,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-tcb-set-affinity",
            TCB_SET_AFFINITY,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-tcb-bind-notification",
            TCB_BIND_NOTIFICATION,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-tcb-unbind-notification",
            TCB_UNBIND_NOTIFICATION,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-tcb-set-fault-handler",
            TCB_SET_FAULT_HANDLER,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-tcb-set-space",
            TCB_SET_SPACE,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-mint-reply-cap",
            MINT_REPLY_CAP,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-irq-handler-ack",
            IRQ_HANDLER_ACK,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-irq-control-get",
            IRQ_CONTROL_GET,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-irq-handler-set-notification",
            IRQ_HANDLER_SET_NOTIFICATION,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-irq-handler-clear",
            IRQ_HANDLER_CLEAR,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-page-table-map",
            PAGE_TABLE_MAP,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-page-table-unmap",
            PAGE_TABLE_UNMAP,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-audit-read",
            AUDIT_READ,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-audit-drain",
            AUDIT_DRAIN,
            NOTIFICATION_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-service-register",
            SERVICE_REGISTER,
            NOTIFICATION_CAP,
            6,
            INVALID_CAPABILITY,
        ),
        overflowed(
            "overflowed-untyped-reset",
            UNTYPED_RESET,
            UNTYPED_CAP,
            5,
            REVOCATION_REQUIRED,
        ),
        overflowed(
            "overflowed-declassify",
            DECLASSIFY,
            ENDPOINT_CAP,
            5,
            FLOW_DENIED,
        ),
        // A declassified signal reads no word past its inline registers
        // (seL4's `seL4_Signal` reads no message), so a long one takes the
        // audited route and reads no IPC-buffer word; refused on its type.
        overflowed(
            "long-declassify-signal",
            DECLASSIFY_SIGNAL,
            ENDPOINT_CAP,
            5,
            INVALID_CAPABILITY,
        ),
        // The untyped retype past its inline words, its type tag one no
        // object kind has, refused by the argument decode.
        RoundTrip {
            msg: [0xff, 0, 0, 0],
            ..overflowed(
                "overflowed-untyped-retype",
                UNTYPED_RETYPE,
                UNTYPED_CAP,
                5,
                INVALID_TYPE_TAG,
            )
        },
        invocation(
            "sched-context-bind",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        invocation(
            "sched-context-unbind",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        // WS-ZA ZA6.9: the Consumed invocation reads the context's consumed
        // time into the caller's saved registers and resets it in place.  The
        // first reading is whatever the context accrued; the second, with the
        // context unbound and nothing charged between them, must read 0.
        consumed("sched-context-consumed", None),
        consumed("sched-context-consumed-reset", Some(0)),
        invocation(
            "sched-context-rebind",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        // WS-ZA ZA6.29: the yieldTo invocation on the context bound to the
        // partner, which is not yet resumed: the checks pass, the context's
        // resume places nothing, and an unschedulable target is neither
        // requeued nor linked, so the consumed time returns at once.
        yield_to("sched-context-yield-to"),
        invocation("tcb-resume-bound", TCB_RESUME, PARTNER_TCB_CAP, [0; 4]),
        invocation("tcb-suspend-bound", TCB_SUSPEND, PARTNER_TCB_CAP, [0; 4]),
        // WS-ZA ZA6.33: seL4's suspend leaves the context bound to the
        // suspended thread, so the context's own unbind releases it.
        invocation(
            "sched-context-unbind-suspended",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        // WS-ZA ZA6.33: the release-queued and donated suspends run here, where
        // both threads' IPC buffers are set (a configure reads its fifth word
        // from the root task's) and the context is configured and unbound.  The
        // postpone runs first, so the donated suspend's configure leaves the
        // context as the yieldTo setup below expects it.
        // seL4's resume of a thread whose context's refill is not yet due
        // (`restart`, `schedContext_resume`: `refill_unblock_check`, then the
        // postpone onto the release queue).  The partner, bound to the context
        // configured to a one-tick budget every two ticks, resumed and run (the
        // root task's receive blocks, the partner's send wakes it); its yield
        // forfeits the budget and queues its refill two ticks on, which leaves the
        // root task current.  The suspend of the release-queued partner takes the
        // context off the release queue; the resume finds the refill not due and
        // postpones the context, which is not placed on a run queue; then the
        // partner is suspended again and the context unbound.  No tick may come
        // between the forfeit and the resume, so the timer is masked throughout.
        kernel_step("mask-ticks", MASK_TICKS_STEP),
        configure(
            "postpone-configure",
            [
                SCHED_CONTEXT_CAP,
                REFILL_BUDGET,
                REFILL_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        invocation(
            "postpone-bind-partner",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        invocation(
            "postpone-resume-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "postpone-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            true,
        ),
        partner_step(
            "postpone-wake-root",
            SEND,
            ENDPOINT_CAP,
            1,
            [0x55, 0],
            false,
        ),
        kernel_step("postpone-partner-yield", YIELD),
        invocation(
            "tcb-suspend-release-queued",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation("tcb-resume-postpone", TCB_RESUME, PARTNER_TCB_CAP, [0; 4]),
        invocation("postpone-suspend", TCB_SUSPEND, PARTNER_TCB_CAP, [0; 4]),
        invocation(
            "postpone-unbind",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        kernel_step("unmask-ticks", UNMASK_TICKS_STEP),
        // WS-ZA ZA6.35: a send of more than the inline words to a waiting
        // receiver (seL4's `doNormalTransfer`, `copyMRs`): the partner's six
        // words, four in its registers and two in its IPC buffer, which the
        // send copies into the receiver's registers and the receiver's own
        // buffer slots in place.  Both threads' buffers are set here, and the
        // partner is run as the postpone above runs it: resumed bound to the
        // one-tick context, the root task's receive blocks, the partner's long
        // send wakes it, and the partner's yield forfeits the budget, which
        // leaves the root task current to suspend the partner and unbind.
        kernel_step("mask-ticks", MASK_TICKS_STEP),
        configure(
            "long-send-configure",
            [
                SCHED_CONTEXT_CAP,
                REFILL_BUDGET,
                REFILL_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        invocation(
            "long-send-bind-partner",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        invocation(
            "long-send-resume-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "long-send-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            true,
        ),
        partner_step(
            "long-send-to-receiver",
            SEND,
            ENDPOINT_CAP,
            LONG_SEND_LENGTH,
            [0x55, 0x56],
            false,
        ),
        kernel_step("long-send-partner-yield", YIELD),
        invocation("long-send-suspend", TCB_SUSPEND, PARTNER_TCB_CAP, [0; 4]),
        invocation(
            "long-send-unbind",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        kernel_step("unmask-ticks", UNMASK_TICKS_STEP),
        // An IPC buffer the validator refuses: aligned to 512 but not to the
        // buffer's 1024-byte size, so it would cross the frame's end (seL4
        // requires the buffer to lie in one frame).  Then full-length forms
        // with both threads' buffers in the frame's last 1024 bytes: a signal
        // and a wait (routed as overflowed, the wait taking the badge the
        // signal left), and the long send to a waiting receiver, which reads
        // all 116 of the sender's overflow words and writes the receiver's in
        // place; then the buffers put back.
        RoundTrip {
            caps_or_badges: None,
            overflow: None,
            returns: Some((
                (crate::svc_dispatch::ERROR_LABEL_BASE + ALIGNMENT_ERROR) << 12,
                [None; 4],
            )),
            ..invocation(
                "half-aligned-ipc-buffer",
                TCB_SET_IPC_BUFFER,
                ROOT_TCB_CAP,
                [HALF_ALIGNED_IPC_BUFFER, 0, 0, 0],
            )
        },
        invocation(
            "tail-root-ipc-buffer",
            TCB_SET_IPC_BUFFER,
            ROOT_TCB_CAP,
            [TAIL_IPC_BUFFER, 0, 0, 0],
        ),
        invocation(
            "tail-partner-ipc-buffer",
            TCB_SET_IPC_BUFFER,
            PARTNER_TCB_CAP,
            [TAIL_IPC_BUFFER, 0, 0, 0],
        ),
        RoundTrip {
            msg_len: TAIL_MESSAGE_LENGTH,
            ..signal("signal-tail-buffer")
        },
        RoundTrip {
            name: "wait-tail-buffer",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: TAIL_MESSAGE_LENGTH,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        kernel_step("mask-ticks", MASK_TICKS_STEP),
        // The long call to a waiting receiver, which copies all 116 of the
        // caller's overflow words into the receiver's buffer in place and
        // blocks the caller for the reply, the suspend answering it; then the
        // long call that blocks with no receiver waiting (seL4 leaves its
        // words in its registers and buffer), the receive that copies them
        // and the full-length reply that answers it, copying the partner's
        // overflow words into the caller's buffer in place.
        invocation("tail-call-resume", TCB_RESUME, PARTNER_TCB_CAP, [0; 4]),
        partner_step(
            "tail-call-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "tail-call-to-receiver",
            CALL,
            ENDPOINT_CAP,
            TAIL_MESSAGE_LENGTH,
            [0x66, 0x67],
            true,
        ),
        invocation("tail-call-suspend", TCB_SUSPEND, PARTNER_TCB_CAP, [0; 4]),
        invocation(
            "tail-call-resume-again",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "tail-call-blocks",
            CALL,
            ENDPOINT_CAP,
            TAIL_MESSAGE_LENGTH,
            [0x68, 0x69],
            true,
        ),
        partner_step(
            "tail-call-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            false,
        ),
        partner_step(
            "tail-call-partner-replies",
            REPLY,
            REPLY_CAP,
            TAIL_MESSAGE_LENGTH,
            [0x77, 0x78],
            false,
        ),
        kernel_step("tail-call-partner-yield", YIELD),
        invocation(
            "tail-call-suspend-again",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // The short call that blocks with no receiver waiting, and the receive
        // that takes it, staging the caller's message and reply object in
        // place beside the long-call take above.
        invocation(
            "short-call-take-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "short-call-blocks",
            CALL,
            ENDPOINT_CAP,
            2,
            [0x71, 0x72],
            true,
        ),
        partner_step(
            "short-call-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            false,
        ),
        partner_step(
            "short-call-partner-replies",
            REPLY,
            REPLY_CAP,
            1,
            [0x73, 0],
            false,
        ),
        kernel_step("short-call-partner-yield", YIELD),
        invocation(
            "short-call-take-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // The long send that blocks with no receiver waiting, and the receive
        // that takes it, copying the sender's overflow words into its own
        // buffer in place.
        invocation(
            "tail-send-blocks-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "tail-send-blocks",
            SEND,
            ENDPOINT_CAP,
            TAIL_MESSAGE_LENGTH,
            [0x58, 0x59],
            true,
        ),
        partner_step(
            "tail-send-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            false,
        ),
        kernel_step("tail-send-blocks-partner-yield", YIELD),
        invocation(
            "tail-send-blocks-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // The long send that blocks with no receiver waiting (its overflow
        // words read again at the receive that takes it, from the sender's
        // buffer), at the one-page length beside the full-length form above.
        invocation(
            "long-send-blocks-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "long-send-blocks",
            SEND,
            ENDPOINT_CAP,
            LONG_SEND_LENGTH,
            [0x57, 0x58],
            true,
        ),
        partner_step(
            "long-send-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            false,
        ),
        kernel_step("long-send-blocks-partner-yield", YIELD),
        invocation(
            "long-send-blocks-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // The long call answered by a full-length reply-receive that then blocks
        // on the endpoint with no sender waiting, copying the partner's
        // overflow words, from its slot 1 on, into the caller's buffer in
        // place (the reply-receive's MR0 names the reply capability).
        invocation(
            "tail-reply-recv-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "tail-reply-recv-call",
            CALL,
            ENDPOINT_CAP,
            TAIL_MESSAGE_LENGTH,
            [0x6a, 0x6b],
            true,
        ),
        partner_step(
            "tail-reply-recv-takes",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            false,
        ),
        partner_step(
            "tail-reply-recv-blocks",
            REPLY_RECV,
            ENDPOINT_CAP,
            TAIL_MESSAGE_LENGTH,
            [REPLY_CAP, 0x7a],
            true,
        ),
        invocation(
            "tail-reply-recv-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // A send and a call carrying one capability, each within the inline
        // words and at full length, that block with no receiver waiting: seL4
        // looks a message's capabilities up only at the rendezvous, so the
        // blocked sender holds its request and nothing is transferred.  The
        // partner then suspends the root task, which cancels its send, and
        // restarts it before suspending itself.
        invocation(
            "caps-send-blocks-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        with_caps(
            partner_step(
                "caps-send-blocks",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 2,
                [0x5a, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [0; 3],
        ),
        invocation(
            "caps-send-blocks-suspend-root",
            TCB_SUSPEND,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-send-blocks-resume-root",
            TCB_RESUME,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-send-blocks-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-send-blocks-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        with_caps(
            partner_step(
                "caps-long-send-blocks",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [0x5c, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [0; 3],
        ),
        invocation(
            "caps-long-send-blocks-suspend-root",
            TCB_SUSPEND,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-send-blocks-resume-root",
            TCB_RESUME,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-send-blocks-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-call-blocks-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        with_caps(
            partner_step(
                "caps-call-blocks",
                CALL,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 2,
                [0x6c, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [0; 3],
        ),
        invocation(
            "caps-call-blocks-suspend-root",
            TCB_SUSPEND,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-call-blocks-resume-root",
            TCB_RESUME,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-call-blocks-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-call-blocks-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        with_caps(
            partner_step(
                "caps-long-call-blocks",
                CALL,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [0x6e, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [0; 3],
        ),
        invocation(
            "caps-long-call-blocks-suspend-root",
            TCB_SUSPEND,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-call-blocks-resume-root",
            TCB_RESUME,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-call-blocks-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // A send carrying one capability (a notification, named in the
        // sender's `caps_or_badges[0]`) to a waiting receiver whose IPC buffer
        // names no receive slot (its `receive_depth` word is 0): seL4's
        // `transferCaps` installs nothing, and the rendezvous writes in place.
        invocation(
            "caps-send-rendezvous-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-send-rendezvous-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps(
            partner_step(
                "caps-send-rendezvous-to-receiver",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x74, 0],
                false,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
        ),
        kernel_step("caps-send-rendezvous-yield", YIELD),
        invocation(
            "caps-send-rendezvous-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // The same with three capabilities, the most a message carries.
        invocation(
            "caps-three-send-rendezvous-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-three-send-rendezvous-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps(
            partner_step(
                "caps-three-send-rendezvous-to-receiver",
                SEND,
                ENDPOINT_CAP,
                THREE_EXTRA_CAPS | 1,
                [0x75, 0],
                false,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
        ),
        kernel_step("caps-three-send-rendezvous-yield", YIELD),
        invocation(
            "caps-three-send-rendezvous-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // A call carrying one capability to a waiting receiver whose buffer
        // names no receive slot, blocking the caller for the reply, the
        // suspend answering it.
        invocation(
            "caps-call-rendezvous-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-call-rendezvous-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps(
            partner_step(
                "caps-call-rendezvous-to-receiver",
                CALL,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x76, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
        ),
        invocation(
            "caps-call-rendezvous-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // The same with three capabilities.
        invocation(
            "caps-three-call-rendezvous-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-three-call-rendezvous-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps(
            partner_step(
                "caps-three-call-rendezvous-to-receiver",
                CALL,
                ENDPOINT_CAP,
                THREE_EXTRA_CAPS | 1,
                [0x77, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
        ),
        invocation(
            "caps-three-call-rendezvous-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // A send carrying a notification capability to a waiting receiver
        // whose IPC buffer names an empty slot of its CSpace: seL4's
        // `transferCaps` derives the capability and installs it there, a CDT
        // child of the sender's slot.  The installed copy is deleted after.
        invocation(
            "caps-install-send-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-install-send-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-install-send-to-receiver",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x79, 0],
                false,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        kernel_step("caps-install-send-yield", YIELD),
        invocation(
            "caps-install-send-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-install-send-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [TRANSFER_RECEIVE_SLOT, 0, 0, 0],
        ),
        // A send carrying the capability of the endpoint it is sent on:
        // seL4 unwraps it, delivering its badge in the receiver's
        // `caps_or_badges[0]` word, and installs nothing.
        invocation(
            "caps-unwrap-send-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-unwrap-send-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-unwrap-send-to-receiver",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x7b, 0],
                false,
            ),
            TAIL_IPC_BUFFER,
            [ENDPOINT_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        kernel_step("caps-unwrap-send-yield", YIELD),
        invocation(
            "caps-unwrap-send-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // Three capabilities: the first installed, the second unwrapped, and
        // the third stopping the transfer, the receive slot used up.
        invocation(
            "caps-three-install-send-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-three-install-send-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-three-install-send-to-receiver",
                SEND,
                ENDPOINT_CAP,
                THREE_EXTRA_CAPS | 1,
                [0x7c, 0],
                false,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, ENDPOINT_CAP, NOTIFICATION_CAP],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        kernel_step("caps-three-install-send-yield", YIELD),
        invocation(
            "caps-three-install-send-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-three-install-send-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [TRANSFER_RECEIVE_SLOT, 0, 0, 0],
        ),
        // A receive path naming an occupied slot names no receive slot, and
        // one whose CNode word names an endpoint names none either: the
        // transfer installs nothing, with no fault.
        invocation(
            "caps-occupied-slot-send-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-occupied-slot-send-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-occupied-slot-send-to-receiver",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x7d, 0],
                false,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
            receive_slot_path(NOTIFICATION_SLOT),
        ),
        kernel_step("caps-occupied-slot-send-yield", YIELD),
        invocation(
            "caps-occupied-slot-send-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-invalid-path-send-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-invalid-path-send-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-invalid-path-send-to-receiver",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x7e, 0],
                false,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
            [ENDPOINT_CAP, cap_address(TRANSFER_RECEIVE_SLOT), 64],
        ),
        kernel_step("caps-invalid-path-send-yield", YIELD),
        invocation(
            "caps-invalid-path-send-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // A send through an endpoint capability without the grant right: seL4
        // transfers no capability, whatever the message names.
        mint(
            "caps-no-grant-send-mint",
            ENDPOINT_SLOT,
            NO_GRANT_ENDPOINT_SLOT,
            READ_WRITE_RIGHTS,
            0,
            TAIL_IPC_BUFFER,
        ),
        invocation(
            "caps-no-grant-send-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-no-grant-send-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-no-grant-send-to-receiver",
                SEND,
                NO_GRANT_ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x7f, 0],
                false,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        kernel_step("caps-no-grant-send-yield", YIELD),
        invocation(
            "caps-no-grant-send-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-no-grant-send-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [NO_GRANT_ENDPOINT_SLOT, 0, 0, 0],
        ),
        // A call carrying a notification capability to a waiting receiver
        // whose buffer names an empty slot: installed there, the caller
        // blocked for the reply the suspend answers; the copy deleted after.
        invocation(
            "caps-install-call-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-install-call-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-install-call-to-receiver",
                CALL,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x81, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        invocation(
            "caps-install-call-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-install-call-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [TRANSFER_RECEIVE_SLOT, 0, 0, 0],
        ),
        // A call carrying the capability of the endpoint it is made on: unwrapped.
        invocation(
            "caps-unwrap-call-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-unwrap-call-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-unwrap-call-to-receiver",
                CALL,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x82, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [ENDPOINT_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        invocation(
            "caps-unwrap-call-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // A call whose receiver's receive path names an occupied slot.
        invocation(
            "caps-occupied-slot-call-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-occupied-slot-call-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-occupied-slot-call-to-receiver",
                CALL,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x83, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
            receive_slot_path(NOTIFICATION_SLOT),
        ),
        invocation(
            "caps-occupied-slot-call-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // A send carrying a notification capability that blocks, and the
        // receive that takes it, its buffer naming an empty slot: the take
        // installs the capability there; the copy deleted after.
        invocation(
            "caps-install-take-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        with_caps_receiving(
            partner_step(
                "caps-install-take-send-blocks",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x84, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        partner_step(
            "caps-install-take-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            false,
        ),
        kernel_step("caps-install-take-partner-yield", YIELD),
        invocation(
            "caps-install-take-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-install-take-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [TRANSFER_RECEIVE_SLOT, 0, 0, 0],
        ),
        // The same carrying the endpoint's own capability: unwrapped.
        invocation(
            "caps-unwrap-take-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        with_caps_receiving(
            partner_step(
                "caps-unwrap-take-send-blocks",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x85, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [ENDPOINT_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        partner_step(
            "caps-unwrap-take-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            false,
        ),
        kernel_step("caps-unwrap-take-partner-yield", YIELD),
        invocation(
            "caps-unwrap-take-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // A call carrying a notification capability that blocks with no receiver
        // waiting, and the receive that takes it, installing the capability in the
        // receive slot its buffer names.
        invocation(
            "caps-install-call-take-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        with_caps_receiving(
            partner_step(
                "caps-install-call-take-blocks",
                CALL,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x86, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        partner_step(
            "caps-install-call-take-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            false,
        ),
        partner_step(
            "caps-install-call-take-partner-replies",
            REPLY,
            REPLY_CAP,
            1,
            [0x88, 0],
            false,
        ),
        kernel_step("caps-install-call-take-partner-yield", YIELD),
        invocation(
            "caps-install-call-take-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-install-call-take-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [TRANSFER_RECEIVE_SLOT, 0, 0, 0],
        ),
        // The same carrying the endpoint's own capability: unwrapped.
        invocation(
            "caps-unwrap-call-take-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        with_caps_receiving(
            partner_step(
                "caps-unwrap-call-take-blocks",
                CALL,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x87, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [ENDPOINT_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        partner_step(
            "caps-unwrap-call-take-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            false,
        ),
        partner_step(
            "caps-unwrap-call-take-partner-replies",
            REPLY,
            REPLY_CAP,
            1,
            [0x88, 0],
            false,
        ),
        kernel_step("caps-unwrap-call-take-partner-yield", YIELD),
        invocation(
            "caps-unwrap-call-take-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // The install and unwrap forms above at the longest message, 120
        // words: the four inline words in registers and the rest copied from
        // the sender's IPC buffer into the receiver's, the transfer running in
        // place before the long frame (`performSendCapsDeliveredLong`,
        // `performCallCapsDeliveredLong`, `performTakeCapsDeliveredLong`,
        // `performCallTakeCapsDeliveredLong`).
        invocation(
            "caps-long-install-send-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-long-install-send-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-long-install-send-to-receiver",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [0x79, 0],
                false,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        kernel_step("caps-long-install-send-yield", YIELD),
        invocation(
            "caps-long-install-send-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-install-send-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [TRANSFER_RECEIVE_SLOT, 0, 0, 0],
        ),
        invocation(
            "caps-long-unwrap-send-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-long-unwrap-send-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-long-unwrap-send-to-receiver",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [0x7b, 0],
                false,
            ),
            TAIL_IPC_BUFFER,
            [ENDPOINT_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        kernel_step("caps-long-unwrap-send-yield", YIELD),
        invocation(
            "caps-long-unwrap-send-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-install-call-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-long-install-call-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-long-install-call-to-receiver",
                CALL,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [0x81, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        invocation(
            "caps-long-install-call-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-install-call-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [TRANSFER_RECEIVE_SLOT, 0, 0, 0],
        ),
        invocation(
            "caps-long-unwrap-call-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "caps-long-unwrap-call-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        with_caps_receiving(
            partner_step(
                "caps-long-unwrap-call-to-receiver",
                CALL,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [0x82, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [ENDPOINT_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        invocation(
            "caps-long-unwrap-call-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-install-take-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        with_caps_receiving(
            partner_step(
                "caps-long-install-take-send-blocks",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [0x84, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        partner_step(
            "caps-long-install-take-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            false,
        ),
        kernel_step("caps-long-install-take-partner-yield", YIELD),
        invocation(
            "caps-long-install-take-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-install-take-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [TRANSFER_RECEIVE_SLOT, 0, 0, 0],
        ),
        invocation(
            "caps-long-unwrap-take-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        with_caps_receiving(
            partner_step(
                "caps-long-unwrap-take-send-blocks",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [0x85, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [ENDPOINT_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        partner_step(
            "caps-long-unwrap-take-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            false,
        ),
        kernel_step("caps-long-unwrap-take-partner-yield", YIELD),
        invocation(
            "caps-long-unwrap-take-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-install-call-take-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        with_caps_receiving(
            partner_step(
                "caps-long-install-call-take-blocks",
                CALL,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [0x86, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        partner_step(
            "caps-long-install-call-take-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            false,
        ),
        partner_step(
            "caps-long-install-call-take-partner-replies",
            REPLY,
            REPLY_CAP,
            1,
            [0x88, 0],
            false,
        ),
        kernel_step("caps-long-install-call-take-partner-yield", YIELD),
        invocation(
            "caps-long-install-call-take-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "caps-long-install-call-take-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [TRANSFER_RECEIVE_SLOT, 0, 0, 0],
        ),
        invocation(
            "caps-long-unwrap-call-take-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        with_caps_receiving(
            partner_step(
                "caps-long-unwrap-call-take-blocks",
                CALL,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [0x87, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [ENDPOINT_CAP, 0, 0],
            receive_slot_path(TRANSFER_RECEIVE_SLOT),
        ),
        partner_step(
            "caps-long-unwrap-call-take-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            false,
        ),
        partner_step(
            "caps-long-unwrap-call-take-partner-replies",
            REPLY,
            REPLY_CAP,
            1,
            [0x88, 0],
            false,
        ),
        kernel_step("caps-long-unwrap-call-take-partner-yield", YIELD),
        invocation(
            "caps-long-unwrap-call-take-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // A send carrying a capability that blocks with no receiver waiting,
        // and the receive that takes it with no receive slot named.
        invocation("caps-take-resume", TCB_RESUME, PARTNER_TCB_CAP, [0; 4]),
        with_caps(
            partner_step(
                "caps-take-send-blocks",
                SEND,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 1,
                [0x78, 0],
                true,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
        ),
        partner_step(
            "caps-take-partner-takes",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            false,
        ),
        kernel_step("caps-take-partner-yield", YIELD),
        invocation("caps-take-suspend", TCB_SUSPEND, PARTNER_TCB_CAP, [0; 4]),
        // Granting replies (the reply capability minted from the reply
        // object's grant-bearing capability carries seL4-MCS's
        // `capReplyCanGrant`) to a caller whose IPC buffer names a valid,
        // empty receive slot: a reply-receive and a reply carrying no
        // capability, which install nothing and answer in place (seL4's
        // `doReplyTransfer` with `grant` set and no extra capability), then
        // a reply carrying one, which installs a copy of the notification
        // capability in that slot ([`INSTALLING_REPLY`], measured); a signal through
        // the installed copy shows it is there, the wait takes its badge, and
        // the copy is deleted.  Both threads' buffers are the one at
        // `TAIL_IPC_BUFFER`; its receive path is closed again last.
        receive_path(
            "grant-reply-receive-path",
            TAIL_IPC_BUFFER,
            [CNODE_CAP, cap_address(EMPTY_SLOT), 64],
        ),
        invocation("grant-reply-resume", TCB_RESUME, PARTNER_TCB_CAP, [0; 4]),
        partner_step(
            "grant-reply-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "grant-reply-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x7b, 0],
            true,
        ),
        partner_step(
            "grant-reply-recv",
            REPLY_RECV,
            ENDPOINT_CAP,
            2,
            [REPLY_CAP, 0x7c],
            true,
        ),
        partner_step(
            "grant-reply-partner-calls-again",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x7d, 0],
            true,
        ),
        partner_step("grant-reply", REPLY, REPLY_CAP, 1, [0x7e, 0], false),
        partner_step(
            "grant-reply-cap-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "grant-reply-cap-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x7f, 0],
            true,
        ),
        INSTALLING_REPLY,
        RoundTrip {
            cptr: cap_address(EMPTY_SLOT),
            ..signal("grant-reply-installed-signal")
        },
        RoundTrip {
            name: "grant-reply-installed-wait",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: 1,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        invocation(
            "grant-reply-installed-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [EMPTY_SLOT, 0, 0, 0],
        ),
        // The same granting reply at the longest message, 120 words: the
        // transfer runs in place before the long frame copies the overflow
        // words (`performReplyCapsDeliveredLong`).
        partner_step(
            "grant-long-reply-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "grant-long-reply-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x81, 0],
            true,
        ),
        with_caps_keeping_path(
            partner_step(
                "grant-long-reply-installs-cap",
                REPLY,
                REPLY_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [0x82, 0],
                false,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
        ),
        RoundTrip {
            cptr: cap_address(EMPTY_SLOT),
            ..signal("grant-long-reply-installed-signal")
        },
        RoundTrip {
            name: "grant-long-reply-installed-wait",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: 1,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        invocation(
            "grant-long-reply-installed-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [EMPTY_SLOT, 0, 0, 0],
        ),
        // A granting reply-receive whose reply leg installs: the root task
        // answers the partner's call naming the notification capability and
        // blocks on the endpoint; the transfer runs in place between the
        // reply's writes and the receive (seL4-MCS's `doReplyTransfer`, then
        // `receiveIPC`; `performReplyRecvBlockCapsDelivered`).  The partner,
        // answered, signals through the installed copy, the wait takes its
        // badge, and the copy is deleted; its second call wakes the root task,
        // which replies.  Then the same at the longest message, 120 words
        // (`performReplyRecvBlockCapsDeliveredLong`).
        partner_step(
            "grant-reply-recv-cap-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "grant-reply-recv-cap-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x83, 0],
            true,
        ),
        with_caps_keeping_path(
            partner_step(
                "grant-reply-recv-cap-installs-cap",
                REPLY_RECV,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 2,
                [REPLY_CAP, 0x84],
                true,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
        ),
        RoundTrip {
            cptr: cap_address(EMPTY_SLOT),
            ..signal("grant-reply-recv-cap-installed-signal")
        },
        RoundTrip {
            name: "grant-reply-recv-cap-installed-wait",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: 1,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        invocation(
            "grant-reply-recv-cap-installed-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [EMPTY_SLOT, 0, 0, 0],
        ),
        partner_step(
            "grant-reply-recv-cap-partner-calls-again",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x85, 0],
            true,
        ),
        partner_step(
            "grant-reply-recv-cap-root-replies",
            REPLY,
            REPLY_CAP,
            1,
            [0x86, 0],
            false,
        ),
        partner_step(
            "grant-long-reply-recv-cap-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "grant-long-reply-recv-cap-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x87, 0],
            true,
        ),
        with_caps_keeping_path(
            partner_step(
                "grant-long-reply-recv-cap-installs-cap",
                REPLY_RECV,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [REPLY_CAP, 0x88],
                true,
            ),
            TAIL_IPC_BUFFER,
            [NOTIFICATION_CAP, 0, 0],
        ),
        RoundTrip {
            cptr: cap_address(EMPTY_SLOT),
            ..signal("grant-long-reply-recv-cap-installed-signal")
        },
        RoundTrip {
            name: "grant-long-reply-recv-cap-installed-wait",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: 1,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        invocation(
            "grant-long-reply-recv-cap-installed-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [EMPTY_SLOT, 0, 0, 0],
        ),
        partner_step(
            "grant-long-reply-recv-cap-partner-calls-again",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x89, 0],
            true,
        ),
        partner_step(
            "grant-long-reply-recv-cap-root-replies",
            REPLY,
            REPLY_CAP,
            1,
            [0x8a, 0],
            false,
        ),
        invocation("grant-reply-suspend", TCB_SUSPEND, PARTNER_TCB_CAP, [0; 4]),
        receive_path("grant-reply-receive-path-closed", TAIL_IPC_BUFFER, [0; 3]),
        configure(
            "tail-send-configure",
            [
                SCHED_CONTEXT_CAP,
                REFILL_BUDGET,
                REFILL_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        invocation(
            "tail-send-bind-partner",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        invocation(
            "tail-send-resume-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "tail-send-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            0,
            [0, 0],
            true,
        ),
        partner_step(
            "tail-send-to-receiver",
            SEND,
            ENDPOINT_CAP,
            TAIL_MESSAGE_LENGTH,
            [0x55, 0x56],
            false,
        ),
        kernel_step("tail-send-partner-yield", YIELD),
        invocation("tail-send-suspend", TCB_SUSPEND, PARTNER_TCB_CAP, [0; 4]),
        invocation(
            "tail-send-unbind",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        kernel_step("unmask-ticks", UNMASK_TICKS_STEP),
        invocation(
            "tail-root-ipc-buffer-back",
            TCB_SET_IPC_BUFFER,
            ROOT_TCB_CAP,
            [FRAME_VADDR, 0, 0, 0],
        ),
        invocation(
            "tail-partner-ipc-buffer-back",
            TCB_SET_IPC_BUFFER,
            PARTNER_TCB_CAP,
            [FRAME_VADDR, 0, 0, 0],
        ),
        // The same with the partner holding the image's scheduling context, so its
        // call donates the context to the root task: the suspend's reply arm takes
        // the reply off the context's reply stack and leaves the context with the
        // server, now its bound holder (seL4 returns no loan on a suspend).  The
        // context's real unbind then takes it from the root task.  The timer is
        // masked across the sequence, so no tick switches the threads between steps.
        kernel_step("mask-ticks", MASK_TICKS_STEP),
        configure(
            "suspend-donated-configure",
            [
                SCHED_CONTEXT_CAP,
                SCHED_CONTEXT_BUDGET,
                SCHED_CONTEXT_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        invocation(
            "suspend-donated-bind-partner",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        invocation(
            "suspend-donated-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "suspend-donated-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "suspend-donated-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x66, 0],
            true,
        ),
        invocation(
            "tcb-suspend-reply-donated",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "suspend-donated-unbind",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        // A granting reply on a donated reply object that installs: the
        // partner, holding the image's scheduling context, calls and lends it
        // to the root task; the root task's reply, naming the notification
        // capability, hands the context back down the stack in place, then
        // installs the capability in the empty slot the partner's buffer names
        // (`performReplyDonatedCapsDelivered`).  A signal through the copy
        // shows it is there, the wait takes its badge, and the copy is
        // deleted; the partner restarts the root task and suspends itself,
        // and the root task unbinds the context.
        configure(
            "donated-reply-caps-configure",
            [
                SCHED_CONTEXT_CAP,
                SCHED_CONTEXT_BUDGET,
                SCHED_CONTEXT_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        invocation(
            "donated-reply-caps-bind-partner",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        receive_path(
            "donated-reply-caps-receive-path",
            FRAME_VADDR,
            [CNODE_CAP, cap_address(EMPTY_SLOT), 64],
        ),
        invocation(
            "donated-reply-caps-resume",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "donated-reply-caps-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "donated-reply-caps-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x68, 0],
            true,
        ),
        with_caps_keeping_path(
            partner_step(
                "donated-reply-installs-cap",
                REPLY,
                REPLY_CAP,
                ONE_EXTRA_CAP | 1,
                [0x69, 0],
                false,
            ),
            FRAME_VADDR,
            [NOTIFICATION_CAP, 0, 0],
        ),
        RoundTrip {
            cptr: cap_address(EMPTY_SLOT),
            ..signal("donated-reply-installed-signal")
        },
        RoundTrip {
            name: "donated-reply-installed-wait",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: 1,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        invocation(
            "donated-reply-installed-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [EMPTY_SLOT, 0, 0, 0],
        ),
        // The reply handed the context back and took the root task off its
        // core, so the partner, running on the context, restarts it before
        // suspending itself: the root task runs the teardown.
        invocation(
            "donated-reply-caps-suspend-root",
            TCB_SUSPEND,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "donated-reply-caps-resume-root",
            TCB_RESUME,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "donated-reply-caps-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "donated-reply-caps-unbind",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        receive_path(
            "donated-reply-caps-receive-path-closed",
            FRAME_VADDR,
            [0; 3],
        ),
        // WS-ZA ZA6.33: a donation across two home cores, then a donation down
        // a chain.  A server thread and its reply are carved; the partner,
        // holding the context, and the server are resumed; the root task's
        // receive blocks and the partner runs.  Core 1 is held in its agent
        // handler while the partner homes the blocked root task on core 1 and
        // calls it: the context is donated from core 0's home to core 1's and
        // its replenishment migrated with it, and the server runs on core 0
        // and homes the root task back (moving the context back) before core
        // 1 is released, so core 1 never runs the woken root task, whose
        // frame starts at address 0.  The server receives, so the root task
        // runs.  The root task,
        // the context still on loan, calls the server: the donation pushes the
        // server's reply onto a stack that already holds the root task's.
        // The server answers and receives again, the root task answers the
        // partner, and everything is taken down.  The timer is still masked.
        invocation(
            "untyped-retype-chain-tcb",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, CHAIN_CHILD_IDS[0], CNODE_CAP, CHAIN_TCB_SLOT],
        ),
        invocation(
            "chain-tcb-set-space",
            TCB_SET_SPACE,
            CHAIN_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "chain-tcb-set-priority",
            TCB_SET_PRIORITY,
            CHAIN_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-chain-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                REPLY_TYPE,
                CHAIN_CHILD_IDS[1],
                CNODE_CAP,
                CHAIN_REPLY_OBJECT_SLOT,
            ],
        ),
        invocation(
            "chain-reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, CHAIN_REPLY_CAP_SLOT, 0, 0],
        ),
        configure(
            "chain-configure",
            [
                SCHED_CONTEXT_CAP,
                SCHED_CONTEXT_BUDGET,
                SCHED_CONTEXT_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        invocation(
            "chain-bind-partner",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        invocation("chain-resume-partner", TCB_RESUME, PARTNER_TCB_CAP, [0; 4]),
        invocation("chain-resume-server", TCB_RESUME, CHAIN_TCB_CAP, [0; 4]),
        partner_step(
            "chain-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        kernel_step("hold-second-core", HOLD_SECOND_CORE_STEP),
        invocation(
            "cross-core-home-root",
            TCB_SET_AFFINITY,
            ROOT_TCB_CAP,
            [SECOND_CORE_AFFINITY, 0, 0, 0],
        ),
        partner_step(
            "cross-core-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x66, 0],
            true,
        ),
        invocation(
            "cross-core-home-root-back",
            TCB_SET_AFFINITY,
            ROOT_TCB_CAP,
            [AFFINITY_UNBIND, 0, 0, 0],
        ),
        kernel_step("release-second-core", RELEASE_SECOND_CORE_STEP),
        partner_step(
            "chain-server-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [CHAIN_REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "chain-root-calls-server",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x67, 0],
            true,
        ),
        partner_step(
            "chain-server-reply-recv",
            REPLY_RECV,
            ENDPOINT_CAP,
            2,
            [CHAIN_REPLY_CAP, 0x98],
            true,
        ),
        // The same donated reply-receive whose reply leg installs: the server
        // is given the root task's IPC buffer, the root task's buffer names
        // the empty slot, and the root task calls the server again, lending
        // it the context; the server's reply-receive, naming the notification
        // capability, hands the context back down the stack in place,
        // installs the capability in that slot and blocks the server
        // (`performReplyRecvDonatedCapsDelivered`).  The root task signals
        // through the copy, the wait takes its badge, and the copy is deleted.
        invocation(
            "chain-caps-server-ipc-buffer",
            TCB_SET_IPC_BUFFER,
            CHAIN_TCB_CAP,
            [FRAME_VADDR, 0, 0, 0],
        ),
        receive_path(
            "chain-caps-receive-path",
            FRAME_VADDR,
            [CNODE_CAP, cap_address(EMPTY_SLOT), 64],
        ),
        partner_step(
            "chain-caps-root-calls-server",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x9a, 0],
            true,
        ),
        with_caps_keeping_path(
            partner_step(
                "chain-server-reply-recv-installs-cap",
                REPLY_RECV,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 2,
                [CHAIN_REPLY_CAP, 0x9b],
                true,
            ),
            FRAME_VADDR,
            [NOTIFICATION_CAP, 0, 0],
        ),
        RoundTrip {
            cptr: cap_address(EMPTY_SLOT),
            ..signal("chain-reply-recv-installed-signal")
        },
        RoundTrip {
            name: "chain-reply-recv-installed-wait",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: 1,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        invocation(
            "chain-reply-recv-installed-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [EMPTY_SLOT, 0, 0, 0],
        ),
        receive_path("chain-caps-receive-path-closed", FRAME_VADDR, [0; 3]),
        // The same donated reply-receive at the longest message, 120 words,
        // its overflow words copied from the server's buffer into the root
        // task's: transferring nothing, then installing the notification
        // capability in the empty slot the root task's buffer names.
        partner_step(
            "chain-long-root-calls-server",
            CALL,
            ENDPOINT_CAP,
            1,
            [0xb0, 0],
            true,
        ),
        partner_step(
            "chain-server-long-reply-recv",
            REPLY_RECV,
            ENDPOINT_CAP,
            TAIL_MESSAGE_LENGTH,
            [CHAIN_REPLY_CAP, 0xb1],
            true,
        ),
        receive_path(
            "chain-long-caps-receive-path",
            FRAME_VADDR,
            [CNODE_CAP, cap_address(EMPTY_SLOT), 64],
        ),
        partner_step(
            "chain-long-caps-root-calls-server",
            CALL,
            ENDPOINT_CAP,
            1,
            [0xb2, 0],
            true,
        ),
        with_caps_keeping_path(
            partner_step(
                "chain-server-long-reply-recv-installs-cap",
                REPLY_RECV,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [CHAIN_REPLY_CAP, 0xb3],
                true,
            ),
            FRAME_VADDR,
            [NOTIFICATION_CAP, 0, 0],
        ),
        RoundTrip {
            cptr: cap_address(EMPTY_SLOT),
            ..signal("chain-long-reply-recv-installed-signal")
        },
        RoundTrip {
            name: "chain-long-reply-recv-installed-wait",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: 1,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        invocation(
            "chain-long-reply-recv-installed-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [EMPTY_SLOT, 0, 0, 0],
        ),
        receive_path("chain-long-caps-receive-path-closed", FRAME_VADDR, [0; 3]),
        partner_step("chain-root-replies", REPLY, REPLY_CAP, 1, [0x77, 0], false),
        invocation("chain-suspend-server", TCB_SUSPEND, CHAIN_TCB_CAP, [0; 4]),
        // The root task's reply handed the context back and took it off its
        // core (seL4's `schedContext_donate`), so the partner restarts it
        // before suspending itself: the root task runs the teardown.
        invocation("chain-suspend-root", TCB_SUSPEND, ROOT_TCB_CAP, [0; 4]),
        invocation("chain-resume-root", TCB_RESUME, ROOT_TCB_CAP, [0; 4]),
        invocation(
            "chain-suspend-partner",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "chain-unbind",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        invocation(
            "chain-tcb-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_TCB_SLOT, 0, 0, 0],
        ),
        invocation(
            "chain-reply-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "chain-reply-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, 0, 0, 0],
        ),
        // WS-ZA ZA6.34: a third thread issues the final deletes that stop the
        // two threads they are about.  The server and its reply are carved
        // again and the context bound to the partner; the root task waits on
        // the notification, so the server runs (the partner is suspended), and
        // at each switch below exactly one thread is runnable.  The server
        // resumes the partner and receives; the partner's call lends it the
        // context, the server's reply heading its stack; the server wakes the
        // root task and waits on the notification.  The root task deletes the
        // reply's last capability: seL4-MCS's `reply_remove` pops the head,
        // the context back to the partner, which is left `Inactive`, and taken
        // from the server.  Then the same lend through the root task's reply
        // object, and the root task deletes the server's last capability: the
        // loan goes back to its lender, who is ended as the server's waiter,
        // and the server's wait is cancelled before it is retired.  The
        // context's unbind leaves the state the scenario found.
        invocation(
            "untyped-retype-third-tcb",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, CHAIN_CHILD_IDS[0], CNODE_CAP, CHAIN_TCB_SLOT],
        ),
        invocation(
            "third-tcb-set-space",
            TCB_SET_SPACE,
            CHAIN_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "third-tcb-set-priority",
            TCB_SET_PRIORITY,
            CHAIN_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-third-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                REPLY_TYPE,
                CHAIN_CHILD_IDS[1],
                CNODE_CAP,
                CHAIN_REPLY_OBJECT_SLOT,
            ],
        ),
        invocation(
            "third-reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, CHAIN_REPLY_CAP_SLOT, 0, 0],
        ),
        configure(
            "third-configure",
            [
                SCHED_CONTEXT_CAP,
                SCHED_CONTEXT_BUDGET,
                SCHED_CONTEXT_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        invocation(
            "third-bind-partner",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        invocation("third-resume-server", TCB_RESUME, CHAIN_TCB_CAP, [0; 4]),
        partner_step("third-root-waits", WAIT, NOTIFICATION_CAP, 0, [0, 0], true),
        invocation(
            "head-server-resumes-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "head-server-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [CHAIN_REPLY_CAP, 0],
            true,
        ),
        partner_step("head-partner-calls", CALL, ENDPOINT_CAP, 1, [0x68, 0], true),
        signal("head-server-wakes-root"),
        partner_step("head-server-waits", WAIT, NOTIFICATION_CAP, 0, [0, 0], true),
        invocation(
            "head-reply-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "head-reply-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, 0, 0, 0],
        ),
        // The server's reply carved again, so the call it answers is on a
        // reply the root task can delete.
        invocation(
            "untyped-retype-waited-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                REPLY_TYPE,
                CHAIN_CHILD_IDS[1],
                CNODE_CAP,
                CHAIN_REPLY_OBJECT_SLOT,
            ],
        ),
        invocation(
            "waited-reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, CHAIN_REPLY_CAP_SLOT, 0, 0],
        ),
        signal("waited-wake-server"),
        partner_step("waited-root-waits", WAIT, NOTIFICATION_CAP, 0, [0, 0], true),
        invocation(
            "waited-server-resumes-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "waited-server-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [CHAIN_REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "waited-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x69, 0],
            true,
        ),
        signal("waited-server-wakes-root"),
        partner_step(
            "waited-server-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "waited-server-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_TCB_SLOT, 0, 0, 0],
        ),
        // WS-ZA ZA6.34: the server's delete orphaned the partner, blocked on
        // the carved reply, which still heads the context the server held
        // (seL4-MCS's `finaliseCap` → `schedContext_unbindTCB`).  The root
        // task deletes that reply's minted capability, then its last:
        // seL4-MCS's `reply_remove` pops it (`reply_pop`: the context to the
        // partner, which holds none) and `reply_unlink` ends the partner's
        // call.
        invocation(
            "orphan-reply-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "orphan-head-reply-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, 0, 0, 0],
        ),
        // A granting reply to a caller recording no server that installs: the
        // first orphan's set-up again, the server deleted while the partner is
        // blocked on its carved reply, then the root task's reply through that
        // reply's capability, naming the notification capability, hands the
        // context back to the partner in place and installs the capability in
        // the empty slot the partner's buffer names
        // (`performReplyUnheldCapsDelivered`).  A signal through the copy shows
        // it is there; the copy, the partner's run and the reply are removed,
        // leaving the state the first orphan left.
        invocation(
            "untyped-retype-unheld-caps-server",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, CHAIN_CHILD_IDS[0], CNODE_CAP, CHAIN_TCB_SLOT],
        ),
        invocation(
            "unheld-caps-server-set-space",
            TCB_SET_SPACE,
            CHAIN_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "unheld-caps-server-set-priority",
            TCB_SET_PRIORITY,
            CHAIN_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-unheld-caps-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                REPLY_TYPE,
                CHAIN_CHILD_IDS[1],
                CNODE_CAP,
                CHAIN_REPLY_OBJECT_SLOT,
            ],
        ),
        invocation(
            "unheld-caps-reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, CHAIN_REPLY_CAP_SLOT, 0, 0],
        ),
        invocation(
            "unheld-caps-resume-server",
            TCB_RESUME,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "unheld-caps-root-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "unheld-caps-server-resumes-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "unheld-caps-server-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [CHAIN_REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "unheld-caps-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x6a, 0],
            true,
        ),
        signal("unheld-caps-server-wakes-root"),
        partner_step(
            "unheld-caps-server-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "unheld-caps-server-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_TCB_SLOT, 0, 0, 0],
        ),
        receive_path(
            "unheld-caps-receive-path",
            FRAME_VADDR,
            [CNODE_CAP, cap_address(EMPTY_SLOT), 64],
        ),
        with_caps_keeping_path(
            partner_step(
                "unheld-reply-installs-cap",
                REPLY,
                CHAIN_REPLY_CAP,
                ONE_EXTRA_CAP | 1,
                [0x6b, 0],
                false,
            ),
            FRAME_VADDR,
            [NOTIFICATION_CAP, 0, 0],
        ),
        RoundTrip {
            cptr: cap_address(EMPTY_SLOT),
            ..signal("unheld-reply-installed-signal")
        },
        RoundTrip {
            name: "unheld-reply-installed-wait",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: 1,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        invocation(
            "unheld-reply-installed-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [EMPTY_SLOT, 0, 0, 0],
        ),
        receive_path("unheld-caps-receive-path-closed", FRAME_VADDR, [0; 3]),
        invocation(
            "unheld-caps-suspend-partner",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "unheld-caps-reply-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "unheld-caps-reply-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, 0, 0, 0],
        ),
        // WS-ZA ZA6.34: a second orphan, answered by a reply-receive.  The
        // server is carved again with a reply, and the root task waits, so the
        // server runs (the partner is `Inactive`): it resumes the partner and
        // receives, the partner's call lends it the context, and it wakes the
        // root task and waits.  The root task deletes it, orphaning the
        // partner on the carved reply, which heads the context with no holder.
        // The root task's reply-receive through that reply's capability
        // answers the partner (`doReplyTransfer`, then `reply_pop`: the
        // context to the partner, which holds none) and blocks it on the
        // endpoint; the partner's send wakes it and the partner waits.  The
        // root task suspends the partner and deletes the reply, leaving the
        // state the first orphan left.
        invocation(
            "untyped-retype-orphan-recv-server",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, CHAIN_CHILD_IDS[0], CNODE_CAP, CHAIN_TCB_SLOT],
        ),
        invocation(
            "orphan-recv-server-set-space",
            TCB_SET_SPACE,
            CHAIN_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "orphan-recv-server-set-priority",
            TCB_SET_PRIORITY,
            CHAIN_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-orphan-recv-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                REPLY_TYPE,
                CHAIN_CHILD_IDS[1],
                CNODE_CAP,
                CHAIN_REPLY_OBJECT_SLOT,
            ],
        ),
        invocation(
            "orphan-recv-reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, CHAIN_REPLY_CAP_SLOT, 0, 0],
        ),
        invocation(
            "orphan-recv-resume-server",
            TCB_RESUME,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "orphan-recv-root-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "orphan-recv-server-resumes-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "orphan-recv-server-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [CHAIN_REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "orphan-recv-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x72, 0],
            true,
        ),
        signal("orphan-recv-server-wakes-root"),
        partner_step(
            "orphan-recv-server-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "orphan-recv-server-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_TCB_SLOT, 0, 0, 0],
        ),
        partner_step(
            "orphan-reply-recv",
            REPLY_RECV,
            ENDPOINT_CAP,
            2,
            [CHAIN_REPLY_CAP, 0x73],
            true,
        ),
        partner_step(
            "orphan-recv-partner-wakes-root",
            SEND,
            ENDPOINT_CAP,
            1,
            [0x74, 0],
            false,
        ),
        partner_step(
            "orphan-recv-partner-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "orphan-recv-suspend-partner",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "orphan-recv-reply-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "orphan-recv-reply-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, 0, 0, 0],
        ),
        // The same orphaned caller answered by a reply-receive whose reply leg
        // installs: the second orphan's set-up again, the partner's buffer
        // naming the empty slot, then the root task's reply-receive through
        // the carved reply's capability, naming the notification capability,
        // hands the context to the partner in place, installs the capability
        // in that slot and blocks the root task on the endpoint
        // (`performReplyRecvUnheldCapsDelivered`).  The partner signals
        // through the copy, the wait takes its badge, and the copy is
        // deleted; its send wakes the root task, and it waits.
        invocation(
            "untyped-retype-unheld-recv-caps-server",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, CHAIN_CHILD_IDS[0], CNODE_CAP, CHAIN_TCB_SLOT],
        ),
        invocation(
            "unheld-recv-caps-server-set-space",
            TCB_SET_SPACE,
            CHAIN_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "unheld-recv-caps-server-set-priority",
            TCB_SET_PRIORITY,
            CHAIN_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-unheld-recv-caps-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                REPLY_TYPE,
                CHAIN_CHILD_IDS[1],
                CNODE_CAP,
                CHAIN_REPLY_OBJECT_SLOT,
            ],
        ),
        invocation(
            "unheld-recv-caps-reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, CHAIN_REPLY_CAP_SLOT, 0, 0],
        ),
        invocation(
            "unheld-recv-caps-resume-server",
            TCB_RESUME,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "unheld-recv-caps-root-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "unheld-recv-caps-server-resumes-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "unheld-recv-caps-server-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [CHAIN_REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "unheld-recv-caps-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x9c, 0],
            true,
        ),
        signal("unheld-recv-caps-server-wakes-root"),
        partner_step(
            "unheld-recv-caps-server-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "unheld-recv-caps-server-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_TCB_SLOT, 0, 0, 0],
        ),
        receive_path(
            "unheld-recv-caps-receive-path",
            FRAME_VADDR,
            [CNODE_CAP, cap_address(EMPTY_SLOT), 64],
        ),
        with_caps_keeping_path(
            partner_step(
                "unheld-reply-recv-installs-cap",
                REPLY_RECV,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 2,
                [CHAIN_REPLY_CAP, 0x9d],
                true,
            ),
            FRAME_VADDR,
            [NOTIFICATION_CAP, 0, 0],
        ),
        RoundTrip {
            cptr: cap_address(EMPTY_SLOT),
            ..signal("unheld-reply-recv-installed-signal")
        },
        RoundTrip {
            name: "unheld-reply-recv-installed-wait",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: 1,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        invocation(
            "unheld-reply-recv-installed-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [EMPTY_SLOT, 0, 0, 0],
        ),
        receive_path("unheld-recv-caps-receive-path-closed", FRAME_VADDR, [0; 3]),
        partner_step(
            "unheld-recv-caps-partner-wakes-root",
            SEND,
            ENDPOINT_CAP,
            1,
            [0x9e, 0],
            false,
        ),
        partner_step(
            "unheld-recv-caps-partner-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "unheld-recv-caps-suspend-partner",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "unheld-recv-caps-reply-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "unheld-recv-caps-reply-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, 0, 0, 0],
        ),
        // The orphaned caller answered by a reply-receive at the longest
        // message, 120 words: transferring nothing, then installing the
        // notification capability in the empty slot the partner's buffer
        // names; each with the second orphan's set-up again.
        invocation(
            "untyped-retype-unheld-long-recv-server",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, CHAIN_CHILD_IDS[0], CNODE_CAP, CHAIN_TCB_SLOT],
        ),
        invocation(
            "unheld-long-recv-server-set-space",
            TCB_SET_SPACE,
            CHAIN_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "unheld-long-recv-server-set-priority",
            TCB_SET_PRIORITY,
            CHAIN_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-unheld-long-recv-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                REPLY_TYPE,
                CHAIN_CHILD_IDS[1],
                CNODE_CAP,
                CHAIN_REPLY_OBJECT_SLOT,
            ],
        ),
        invocation(
            "unheld-long-recv-reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, CHAIN_REPLY_CAP_SLOT, 0, 0],
        ),
        invocation(
            "unheld-long-recv-resume-server",
            TCB_RESUME,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "unheld-long-recv-root-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "unheld-long-recv-server-resumes-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "unheld-long-recv-server-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [CHAIN_REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "unheld-long-recv-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0xb7, 0],
            true,
        ),
        signal("unheld-long-recv-server-wakes-root"),
        partner_step(
            "unheld-long-recv-server-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "unheld-long-recv-server-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_TCB_SLOT, 0, 0, 0],
        ),
        partner_step(
            "unheld-long-reply-recv",
            REPLY_RECV,
            ENDPOINT_CAP,
            TAIL_MESSAGE_LENGTH,
            [CHAIN_REPLY_CAP, 0xb8],
            true,
        ),
        partner_step(
            "unheld-long-recv-partner-wakes-root",
            SEND,
            ENDPOINT_CAP,
            1,
            [0xb9, 0],
            false,
        ),
        partner_step(
            "unheld-long-recv-partner-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "unheld-long-recv-suspend-partner",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "unheld-long-recv-reply-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "unheld-long-recv-reply-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-unheld-long-recv-caps-server",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, CHAIN_CHILD_IDS[0], CNODE_CAP, CHAIN_TCB_SLOT],
        ),
        invocation(
            "unheld-long-recv-caps-server-set-space",
            TCB_SET_SPACE,
            CHAIN_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "unheld-long-recv-caps-server-set-priority",
            TCB_SET_PRIORITY,
            CHAIN_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-unheld-long-recv-caps-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                REPLY_TYPE,
                CHAIN_CHILD_IDS[1],
                CNODE_CAP,
                CHAIN_REPLY_OBJECT_SLOT,
            ],
        ),
        invocation(
            "unheld-long-recv-caps-reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, CHAIN_REPLY_CAP_SLOT, 0, 0],
        ),
        invocation(
            "unheld-long-recv-caps-resume-server",
            TCB_RESUME,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "unheld-long-recv-caps-root-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "unheld-long-recv-caps-server-resumes-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "unheld-long-recv-caps-server-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [CHAIN_REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "unheld-long-recv-caps-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0xb4, 0],
            true,
        ),
        signal("unheld-long-recv-caps-server-wakes-root"),
        partner_step(
            "unheld-long-recv-caps-server-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "unheld-long-recv-caps-server-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_TCB_SLOT, 0, 0, 0],
        ),
        receive_path(
            "unheld-long-recv-caps-receive-path",
            FRAME_VADDR,
            [CNODE_CAP, cap_address(EMPTY_SLOT), 64],
        ),
        with_caps_keeping_path(
            partner_step(
                "unheld-long-reply-recv-installs-cap",
                REPLY_RECV,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | TAIL_MESSAGE_LENGTH,
                [CHAIN_REPLY_CAP, 0xb5],
                true,
            ),
            FRAME_VADDR,
            [NOTIFICATION_CAP, 0, 0],
        ),
        RoundTrip {
            cptr: cap_address(EMPTY_SLOT),
            ..signal("unheld-long-recv-caps-installed-signal")
        },
        RoundTrip {
            name: "unheld-long-recv-caps-installed-wait",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: 1,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        invocation(
            "unheld-long-recv-caps-installed-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [EMPTY_SLOT, 0, 0, 0],
        ),
        receive_path(
            "unheld-long-recv-caps-receive-path-closed",
            FRAME_VADDR,
            [0; 3],
        ),
        partner_step(
            "unheld-long-recv-caps-partner-wakes-root",
            SEND,
            ENDPOINT_CAP,
            1,
            [0xb6, 0],
            false,
        ),
        partner_step(
            "unheld-long-recv-caps-partner-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "unheld-long-recv-caps-suspend-partner",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "unheld-long-recv-caps-reply-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "unheld-long-recv-caps-reply-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, 0, 0, 0],
        ),
        invocation(
            "third-unbind",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        // The ordinary server loop with a client already queued: the root
        // task takes the partner's call, then a third thread's send queues on
        // the endpoint while the root task waits; the root task's
        // reply-receive answers the partner and its receive leg takes the
        // queued send at once (seL4-MCS's `handleReplyRecv`: `doReplyTransfer`,
        // then `receiveIPC` meeting a waiting sender), and returns.  Then the
        // same with the reply naming the notification capability, installed
        // in the empty slot the partner's buffer names; a signal through the
        // copy, the wait and the delete follow.  At each switch exactly one
        // thread is runnable.
        invocation(
            "untyped-retype-queued-sender",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, CHAIN_CHILD_IDS[0], CNODE_CAP, CHAIN_TCB_SLOT],
        ),
        invocation(
            "queued-sender-set-space",
            TCB_SET_SPACE,
            CHAIN_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "queued-sender-set-priority",
            TCB_SET_PRIORITY,
            CHAIN_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "queued-sender-resume-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "queued-sender-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "queued-sender-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0xa0, 0],
            true,
        ),
        invocation(
            "queued-sender-resume-sender",
            TCB_RESUME,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "queued-sender-root-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        signal("queued-sender-sender-wakes-root"),
        partner_step(
            "queued-sender-sender-sends",
            SEND,
            ENDPOINT_CAP,
            1,
            [0xa2, 0],
            true,
        ),
        partner_step(
            "queued-sender-reply-recv",
            REPLY_RECV,
            ENDPOINT_CAP,
            2,
            [REPLY_CAP, 0xa3],
            false,
        ),
        invocation(
            "queued-sender-suspend-sender",
            TCB_SUSPEND,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-sender-suspend-partner",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-sender-caps-resume-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "queued-sender-caps-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "queued-sender-caps-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0xa4, 0],
            true,
        ),
        invocation(
            "queued-sender-caps-resume-sender",
            TCB_RESUME,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "queued-sender-caps-root-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        signal("queued-sender-caps-sender-wakes-root"),
        partner_step(
            "queued-sender-caps-sender-sends",
            SEND,
            ENDPOINT_CAP,
            1,
            [0xa6, 0],
            true,
        ),
        receive_path(
            "queued-sender-caps-receive-path",
            FRAME_VADDR,
            [CNODE_CAP, cap_address(EMPTY_SLOT), 64],
        ),
        with_caps_keeping_path(
            partner_step(
                "queued-sender-caps-reply-recv-installs-cap",
                REPLY_RECV,
                ENDPOINT_CAP,
                ONE_EXTRA_CAP | 2,
                [REPLY_CAP, 0xa7],
                false,
            ),
            FRAME_VADDR,
            [NOTIFICATION_CAP, 0, 0],
        ),
        RoundTrip {
            cptr: cap_address(EMPTY_SLOT),
            ..signal("queued-sender-caps-installed-signal")
        },
        RoundTrip {
            name: "queued-sender-caps-installed-wait",
            syscall: WAIT,
            cptr: NOTIFICATION_CAP,
            msg_len: 1,
            msg: [0, 0, 0, 0],
            primed: None,
            blocks: false,
            caps_or_badges: None,
            overflow: None,
            returns: None,
        },
        invocation(
            "queued-sender-caps-installed-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [EMPTY_SLOT, 0, 0, 0],
        ),
        receive_path(
            "queued-sender-caps-receive-path-closed",
            FRAME_VADDR,
            [0; 3],
        ),
        invocation(
            "queued-sender-caps-suspend-sender",
            TCB_SUSPEND,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-sender-caps-suspend-partner",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-sender-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_TCB_SLOT, 0, 0, 0],
        ),
        // The call that queues with no receiver waiting, and the receive that
        // takes it: a third thread, holding the image's scheduling context,
        // calls the endpoint while the root task waits on the notification it
        // has just signalled, so the call is queued on the endpoint's send
        // queue (seL4's `sendIPC` with no receiver: the caller blocks on
        // send, `canDonate` held); the root task's receive then dequeues the
        // caller, binds the reply object to it and takes its context (seL4-MCS
        // `receiveIPC` meeting a waiting caller: `reply_push` and
        // `schedContext_donate`, the root task holding none), and its reply
        // hands the context back.  Then the server loop with a caller queued
        // behind a client it is answering: the partner's call taken, the
        // third thread resumed and its priority set while it is ready and
        // queued (lowered below the root task's and raised back, each
        // re-queued in place), the root task lowering its own priority below
        // the ready thread (rescheduled at once, seL4's `setPriority` of the
        // current thread), the third thread's call queued, the root task
        // raising its own priority back, and its reply-receive answering the
        // partner and taking the queued caller at once, its context lent to the
        // root task again until the root task's reply.  The ticks are masked
        // across the whole sequence, so no budget runs out between steps, and
        // at each switch exactly one thread is runnable.
        kernel_step("mask-ticks", MASK_TICKS_STEP),
        invocation(
            "untyped-retype-queued-caller",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, CHAIN_CHILD_IDS[0], CNODE_CAP, CHAIN_TCB_SLOT],
        ),
        invocation(
            "queued-caller-set-space",
            TCB_SET_SPACE,
            CHAIN_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "queued-caller-set-priority",
            TCB_SET_PRIORITY,
            CHAIN_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "queued-caller-bind",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [CHAIN_TCB_CAP, 0, 0, 0],
        ),
        invocation(
            "queued-caller-resume-caller",
            TCB_RESUME,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "queued-caller-root-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        signal("queued-caller-caller-wakes-root"),
        partner_step(
            "queued-caller-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0xb2, 0],
            true,
        ),
        partner_step(
            "queued-caller-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            false,
        ),
        partner_step(
            "queued-caller-root-replies",
            REPLY,
            REPLY_CAP,
            1,
            [0xb3, 0],
            false,
        ),
        // The reply handed the context back and took the root task off its
        // core (seL4-MCS: a server whose context returns to its caller no
        // longer runs), so the third thread restarts it before suspending
        // itself, which leaves the root task current.
        invocation(
            "queued-caller-suspend-root",
            TCB_SUSPEND,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-caller-resume-root",
            TCB_RESUME,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-caller-suspend-caller",
            TCB_SUSPEND,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        // The root task, serving no one, lowers its own priority below the
        // ready third thread: rescheduled at once (seL4's `setPriority` of the
        // current thread), its own result staged as it is switched out
        // (`stageCallerReturn_stages_switched_out`), so the round trip returns
        // and the third thread is current after it.  The third thread waits,
        // and the root task raises its own priority back and wakes it.
        invocation(
            "queued-caller-resume-lowered",
            TCB_RESUME,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-caller-root-lowers-self",
            TCB_SET_PRIORITY,
            ROOT_TCB_CAP,
            [PARTNER_PRIORITY - 1, 0, 0, 0],
        ),
        partner_step(
            "queued-caller-caller-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "queued-caller-root-raises-self",
            TCB_SET_PRIORITY,
            ROOT_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        signal("queued-caller-root-wakes-caller"),
        invocation(
            "queued-caller-suspend-lowered",
            TCB_SUSPEND,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-caller-resume-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "queued-caller-root-takes-partner",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "queued-caller-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0xb4, 0],
            true,
        ),
        invocation(
            "queued-caller-resume-caller-again",
            TCB_RESUME,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-caller-lower-ready",
            TCB_SET_PRIORITY,
            CHAIN_TCB_CAP,
            [PARTNER_PRIORITY - 1, 0, 0, 0],
        ),
        invocation(
            "queued-caller-raise-ready",
            TCB_SET_PRIORITY,
            CHAIN_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        partner_step(
            "queued-caller-root-waits-again",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        signal("queued-caller-caller-wakes-root-again"),
        partner_step(
            "queued-caller-calls-again",
            CALL,
            ENDPOINT_CAP,
            1,
            [0xb5, 0],
            true,
        ),
        partner_step(
            "queued-caller-reply-recv",
            REPLY_RECV,
            ENDPOINT_CAP,
            2,
            [REPLY_CAP, 0xb6],
            false,
        ),
        partner_step(
            "queued-caller-root-replies-again",
            REPLY,
            REPLY_CAP,
            1,
            [0xb7, 0],
            false,
        ),
        // The context back with the third thread and the root task off its
        // core again: the third thread suspends the partner, restarts the root
        // task and suspends itself.
        invocation(
            "queued-caller-suspend-partner",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-caller-suspend-root-again",
            TCB_SUSPEND,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-caller-resume-root-again",
            TCB_RESUME,
            ROOT_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-caller-suspend-caller-again",
            TCB_SUSPEND,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "queued-caller-unbind",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        invocation(
            "queued-caller-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_TCB_SLOT, 0, 0, 0],
        ),
        kernel_step("unmask-ticks", UNMASK_TICKS_STEP),
        // WS-ZA ZA6.34: a reply stack three frames deep, and a final delete
        // of its middle reply.  The server is carved again, with a fourth
        // thread and a reply for each; the root task, the server and the
        // fourth thread receive on the endpoint in that order, each resuming
        // the next, and the partner's call lends the context down the chain:
        // the partner to the root task, the root task to the server, the
        // server to the fourth thread, which runs holding it.  It deletes the
        // server's reply, the middle frame: seL4-MCS's `reply_remove` severs
        // the stack there and ends the root task, its caller.  The fourth
        // thread resumes the root task and waits; the root task suspends the
        // three others (the server's frame heads the context, which its
        // holder keeps as its own) and unbinds the context.
        invocation(
            "untyped-retype-stack-server",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, CHAIN_CHILD_IDS[0], CNODE_CAP, CHAIN_TCB_SLOT],
        ),
        invocation(
            "stack-server-set-space",
            TCB_SET_SPACE,
            CHAIN_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "stack-server-set-priority",
            TCB_SET_PRIORITY,
            CHAIN_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-stack-top",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                TCB_TYPE,
                STACK_TOP_CHILD_IDS[0],
                CNODE_CAP,
                STACK_TOP_TCB_SLOT,
            ],
        ),
        invocation(
            "stack-top-set-space",
            TCB_SET_SPACE,
            STACK_TOP_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "stack-top-set-priority",
            TCB_SET_PRIORITY,
            STACK_TOP_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-stack-server-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                REPLY_TYPE,
                CHAIN_CHILD_IDS[1],
                CNODE_CAP,
                CHAIN_REPLY_OBJECT_SLOT,
            ],
        ),
        invocation(
            "stack-server-reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, CHAIN_REPLY_CAP_SLOT, 0, 0],
        ),
        invocation(
            "untyped-retype-stack-top-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                REPLY_TYPE,
                STACK_TOP_CHILD_IDS[1],
                CNODE_CAP,
                STACK_TOP_REPLY_OBJECT_SLOT,
            ],
        ),
        invocation(
            "stack-top-reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [STACK_TOP_REPLY_OBJECT_SLOT, STACK_TOP_REPLY_CAP_SLOT, 0, 0],
        ),
        configure(
            "stack-configure",
            [
                SCHED_CONTEXT_CAP,
                SCHED_CONTEXT_BUDGET,
                SCHED_CONTEXT_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        invocation(
            "stack-bind-partner",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        invocation("stack-resume-server", TCB_RESUME, CHAIN_TCB_CAP, [0; 4]),
        partner_step(
            "stack-root-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        invocation(
            "stack-server-resumes-top",
            TCB_RESUME,
            STACK_TOP_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "stack-server-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [CHAIN_REPLY_CAP, 0],
            true,
        ),
        invocation(
            "stack-top-resumes-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "stack-top-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [STACK_TOP_REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "stack-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x6a, 0],
            true,
        ),
        partner_step("stack-root-calls", CALL, ENDPOINT_CAP, 1, [0x6b, 0], true),
        partner_step("stack-server-calls", CALL, ENDPOINT_CAP, 1, [0x6c, 0], true),
        invocation(
            "middle-reply-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "middle-reply-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, 0, 0, 0],
        ),
        invocation("stack-top-resumes-root", TCB_RESUME, ROOT_TCB_CAP, [0; 4]),
        partner_step("stack-top-waits", WAIT, NOTIFICATION_CAP, 0, [0, 0], true),
        invocation("stack-suspend-server", TCB_SUSPEND, CHAIN_TCB_CAP, [0; 4]),
        invocation(
            "stack-suspend-partner",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation("stack-suspend-top", TCB_SUSPEND, STACK_TOP_TCB_CAP, [0; 4]),
        invocation(
            "stack-unbind",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        // A context deleted under a two-frame stack, then the final delete of
        // the stack's old top.  A context is carved, configured and bound to
        // the partner; the server and the fourth thread receive, the
        // partner's call lends the context to the server, whose call lends it
        // on to the fourth thread, which wakes the root task and waits.  The
        // root task deletes the context's last capability (seL4's
        // `schedContext_unbindReply` lets go of the stack, and the holder is
        // unbound), then the top reply's: its caller, the server, is ended
        // and the frame below loses its link up to it.  The partner and the
        // fourth thread are suspended and the two carved threads deleted.
        invocation(
            "untyped-retype-stack-context",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [SCHED_CONTEXT_TYPE, MOVE_SC_ID, CNODE_CAP, MOVE_SC_SLOT],
        ),
        configure(
            "stack-context-configure",
            [
                MOVE_SC_CAP,
                SCHED_CONTEXT_BUDGET,
                SCHED_CONTEXT_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        invocation(
            "stack-context-bind-partner",
            SCHED_CONTEXT_BIND,
            MOVE_SC_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        invocation(
            "contextless-resume-server",
            TCB_RESUME,
            CHAIN_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "contextless-root-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "contextless-server-resumes-top",
            TCB_RESUME,
            STACK_TOP_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "contextless-server-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [REPLY_CAP, 0],
            true,
        ),
        invocation(
            "contextless-top-resumes-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "contextless-top-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [STACK_TOP_REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "contextless-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x6d, 0],
            true,
        ),
        partner_step(
            "contextless-server-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x6e, 0],
            true,
        ),
        signal("contextless-top-wakes-root"),
        partner_step(
            "contextless-top-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "contextless-context-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [MOVE_SC_SLOT, 0, 0, 0],
        ),
        invocation(
            "contextless-top-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [STACK_TOP_REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "contextless-top-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [STACK_TOP_REPLY_OBJECT_SLOT, 0, 0, 0],
        ),
        invocation(
            "contextless-suspend-partner",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "contextless-suspend-top",
            TCB_SUSPEND,
            STACK_TOP_TCB_CAP,
            [0; 4],
        ),
        // WS-ZA ZA6.34: the final delete of an endpoint two threads wait on
        // (seL4's `cancelAllIPC` over a queue whose head has a successor).  An
        // endpoint is carved where the deleted context was; the fourth thread
        // and the partner receive on it, the partner waking the root task
        // first; the root task deletes it, which cancels both receives, and
        // suspends the two threads again.
        invocation(
            "untyped-retype-queue-endpoint",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [ENDPOINT_TYPE, MOVE_SC_ID, CNODE_CAP, MOVE_SC_SLOT],
        ),
        invocation("queue-resume-top", TCB_RESUME, STACK_TOP_TCB_CAP, [0; 4]),
        partner_step("queue-root-waits", WAIT, NOTIFICATION_CAP, 0, [0, 0], true),
        invocation(
            "queue-top-resumes-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step("queue-top-receives", RECEIVE, MOVE_SC_CAP, 0, [0, 0], true),
        signal("queue-partner-wakes-root"),
        partner_step(
            "queue-partner-receives",
            RECEIVE,
            MOVE_SC_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation(
            "queue-endpoint-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [MOVE_SC_SLOT, 0, 0, 0],
        ),
        invocation("queue-suspend-top", TCB_SUSPEND, STACK_TOP_TCB_CAP, [0; 4]),
        invocation(
            "queue-suspend-partner",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        // WS-ZA ZA6.34: a holder's final delete under a two-frame stack, then
        // the orphans it leaves.  The context is bound to the partner and a
        // reply carved for each of the server and the fourth thread; the
        // server and the fourth thread receive, the partner's call lends the
        // context to the server, whose call lends it on to the fourth thread,
        // which wakes the root task and waits.  The root task deletes the
        // fourth thread (seL4-MCS's `finaliseCap`: its wait cancelled, the
        // context unbound, heading the stack with its two callers left
        // blocked).  It deletes the partner's reply, the frame below the head
        // (`reply_remove` severs the stack there and ends the partner), then
        // answers the server through the head reply's capability
        // (`doReplyTransfer`, then `reply_pop`: the context to the server,
        // which holds none).  The server wakes the root task and waits; the
        // root task suspends it, unbinds the context, deletes the head reply
        // and carves the fourth thread again.
        configure(
            "orphan-stack-configure",
            [
                SCHED_CONTEXT_CAP,
                SCHED_CONTEXT_BUDGET,
                SCHED_CONTEXT_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        invocation(
            "orphan-stack-bind-partner",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-orphan-server-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                REPLY_TYPE,
                CHAIN_CHILD_IDS[1],
                CNODE_CAP,
                CHAIN_REPLY_OBJECT_SLOT,
            ],
        ),
        invocation(
            "orphan-server-reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, CHAIN_REPLY_CAP_SLOT, 0, 0],
        ),
        invocation(
            "untyped-retype-orphan-top-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                REPLY_TYPE,
                STACK_TOP_CHILD_IDS[1],
                CNODE_CAP,
                STACK_TOP_REPLY_OBJECT_SLOT,
            ],
        ),
        invocation(
            "orphan-top-reply-cap-mint",
            MINT_REPLY_CAP,
            CNODE_CAP,
            [STACK_TOP_REPLY_OBJECT_SLOT, STACK_TOP_REPLY_CAP_SLOT, 0, 0],
        ),
        invocation("orphan-resume-server", TCB_RESUME, CHAIN_TCB_CAP, [0; 4]),
        partner_step("orphan-root-waits", WAIT, NOTIFICATION_CAP, 0, [0, 0], true),
        invocation(
            "orphan-server-resumes-top",
            TCB_RESUME,
            STACK_TOP_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "orphan-server-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [CHAIN_REPLY_CAP, 0],
            true,
        ),
        invocation(
            "orphan-top-resumes-partner",
            TCB_RESUME,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        partner_step(
            "orphan-top-receives",
            RECEIVE,
            ENDPOINT_CAP,
            1,
            [STACK_TOP_REPLY_CAP, 0],
            true,
        ),
        partner_step(
            "orphan-partner-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x6f, 0],
            true,
        ),
        partner_step(
            "orphan-server-calls",
            CALL,
            ENDPOINT_CAP,
            1,
            [0x70, 0],
            true,
        ),
        signal("orphan-top-wakes-root"),
        partner_step("orphan-top-waits", WAIT, NOTIFICATION_CAP, 0, [0, 0], true),
        invocation(
            "orphan-holder-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [STACK_TOP_TCB_SLOT, 0, 0, 0],
        ),
        invocation(
            "orphan-middle-reply-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "orphan-middle-reply-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_REPLY_OBJECT_SLOT, 0, 0, 0],
        ),
        partner_step(
            "orphan-root-answers-server",
            REPLY,
            STACK_TOP_REPLY_CAP,
            1,
            [0x71, 0],
            false,
        ),
        partner_step(
            "orphan-root-waits-server",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        signal("orphan-server-wakes-root"),
        partner_step(
            "orphan-server-waits",
            WAIT,
            NOTIFICATION_CAP,
            0,
            [0, 0],
            true,
        ),
        invocation("orphan-suspend-server", TCB_SUSPEND, CHAIN_TCB_CAP, [0; 4]),
        invocation(
            "orphan-stack-unbind",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
        invocation(
            "orphan-top-reply-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [STACK_TOP_REPLY_CAP_SLOT, 0, 0, 0],
        ),
        invocation(
            "orphan-top-reply-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [STACK_TOP_REPLY_OBJECT_SLOT, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-orphan-top",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                TCB_TYPE,
                STACK_TOP_CHILD_IDS[0],
                CNODE_CAP,
                STACK_TOP_TCB_SLOT,
            ],
        ),
        invocation(
            "orphan-top-set-space",
            TCB_SET_SPACE,
            STACK_TOP_TCB_CAP,
            [CNODE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "orphan-top-set-priority",
            TCB_SET_PRIORITY,
            STACK_TOP_TCB_CAP,
            [PARTNER_PRIORITY, 0, 0, 0],
        ),
        invocation(
            "stack-server-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [CHAIN_TCB_SLOT, 0, 0, 0],
        ),
        invocation(
            "stack-top-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [STACK_TOP_TCB_SLOT, 0, 0, 0],
        ),
        kernel_step("unmask-ticks", UNMASK_TICKS_STEP),
        invocation(
            "vspace-unmap",
            VSPACE_UNMAP,
            VSPACE_CAP,
            [ROOT_ASID, FRAME_VADDR, 0, 0],
        ),
        // The frame mapped again at an address the unmap did not free (the
        // copy's page, which the revoke unmapped), so the map writes over the
        // translation and epoch cells the unmap took out rather than over an
        // entry left at its own address; then unmapped again.
        invocation(
            "vspace-map-moved",
            VSPACE_MAP,
            VSPACE_CAP,
            [ROOT_ASID, FRAME_COPY_VADDR, FRAME_CAP, FRAME_PERMS],
        ),
        invocation(
            "vspace-unmap-moved",
            VSPACE_UNMAP,
            VSPACE_CAP,
            [ROOT_ASID, FRAME_COPY_VADDR, 0, 0],
        ),
        invocation(
            "frame-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        invocation(
            "page-table-unmap-3",
            PAGE_TABLE_UNMAP,
            PAGE_TABLE_CAPS[2],
            [0; 4],
        ),
        invocation(
            "page-table-delete-3",
            CSPACE_DELETE,
            CNODE_CAP,
            [PAGE_TABLE_SLOTS[2], 0, 0, 0],
        ),
        invocation(
            "page-table-unmap-2",
            PAGE_TABLE_UNMAP,
            PAGE_TABLE_CAPS[1],
            [0; 4],
        ),
        invocation(
            "page-table-delete-2",
            CSPACE_DELETE,
            CNODE_CAP,
            [PAGE_TABLE_SLOTS[1], 0, 0, 0],
        ),
        invocation(
            "page-table-unmap-1",
            PAGE_TABLE_UNMAP,
            PAGE_TABLE_CAPS[0],
            [0; 4],
        ),
        // The window's page is gone, so the root task's buffer goes back to
        // the one the boot gave it, where the mints below read their badges.
        invocation(
            "root-ipc-buffer-back",
            TCB_SET_IPC_BUFFER,
            ROOT_TCB_CAP,
            [ROOT_IPC_BUFFER, 0, 0, 0],
        ),
        invocation(
            "page-table-delete-1",
            CSPACE_DELETE,
            CNODE_CAP,
            [PAGE_TABLE_SLOTS[0], 0, 0, 0],
        ),
        // WS-ZA ZA6.35: the root task's interrupt-control capability copied,
        // minted with its own rights, with none and with a badge, into the slot
        // the next carve reuses, and deleted each time; the carve's pin reads
        // that slot's record after.
        invocation(
            "irq-control-copy",
            CSPACE_COPY,
            CNODE_CAP,
            root_slot_copy(IRQ_CONTROL_SLOT, FRAME_SLOT),
        ),
        invocation(
            "irq-control-copy-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        mint(
            "irq-control-mint",
            IRQ_CONTROL_SLOT,
            FRAME_SLOT,
            IRQ_CONTROL_RIGHTS,
            0,
            ROOT_IPC_BUFFER,
        ),
        invocation(
            "irq-control-mint-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        mint(
            "irq-control-mint-attenuated",
            IRQ_CONTROL_SLOT,
            FRAME_SLOT,
            0,
            0,
            ROOT_IPC_BUFFER,
        ),
        invocation(
            "irq-control-mint-attenuated-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        mint(
            "irq-control-mint-badged",
            IRQ_CONTROL_SLOT,
            FRAME_SLOT,
            IRQ_CONTROL_RIGHTS,
            IRQ_CONTROL_BADGE,
            ROOT_IPC_BUFFER,
        ),
        invocation(
            "irq-control-mint-badged-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        // WS-ZA ZA5.4 part 22: each passive kernel kind carved and its only
        // capability deleted, which retires it, quiescent and unreferenced.
        invocation(
            "untyped-retype-endpoint",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [ENDPOINT_TYPE, PASSIVE_CHILD_IDS[0], CNODE_CAP, FRAME_SLOT],
        ),
        invocation(
            "endpoint-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-notification",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                NOTIFICATION_TYPE,
                PASSIVE_CHILD_IDS[1],
                CNODE_CAP,
                FRAME_SLOT,
            ],
        ),
        invocation(
            "notification-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-reply",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [REPLY_TYPE, PASSIVE_CHILD_IDS[2], CNODE_CAP, FRAME_SLOT],
        ),
        invocation(
            "reply-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-cnode",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [CNODE_TYPE, PASSIVE_CHILD_IDS[3], CNODE_CAP, FRAME_SLOT],
        ),
        invocation(
            "cnode-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        // WS-ZA ZA5.4 part 26: a carved CNode holding an endpoint's only
        // capability, its own only capability deleted: the delete empties
        // the CNode slot by slot (the zombie loop, seL4's `finaliseSlot`),
        // which retires the endpoint, then retires the CNode.
        invocation(
            "untyped-retype-populated-cnode",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [CNODE_TYPE, PASSIVE_CHILD_IDS[3], CNODE_CAP, FRAME_SLOT],
        ),
        invocation(
            "untyped-retype-into-cnode",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [ENDPOINT_TYPE, PASSIVE_CHILD_IDS[0], FRAME_CAP, 0],
        ),
        invocation(
            "populated-cnode-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        // A carved thread given a carved CNode as its CSpace root and the
        // boot VSpace root, the CNode's other capability deleted so the
        // thread's slot holds its last, then the thread's only capability
        // deleted: the finalisation leaves its space slots, which the loop
        // then deletes, retiring the CNode, and the thread is retired.
        invocation(
            "untyped-retype-spaced-tcb",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [TCB_TYPE, THREAD_CHILD_IDS[0], CNODE_CAP, FRAME_SLOT],
        ),
        invocation(
            "untyped-retype-space-cnode",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [CNODE_TYPE, PASSIVE_CHILD_IDS[3], CNODE_CAP, MOVE_SLOT],
        ),
        invocation(
            "set-carved-tcb-space",
            TCB_SET_SPACE,
            FRAME_CAP,
            [MOVE_CAP, VSPACE_CAP, 0, 0],
        ),
        invocation(
            "space-cnode-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [MOVE_SLOT, 0, 0, 0],
        ),
        invocation(
            "spaced-tcb-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        // WS-UC UC1: the two kinds no other scenario carves, each carved and
        // its only capability deleted, which retires it: a VSpace root (one
        // page, its top-level table, under the least free ASID) and a child
        // untyped of one page (seL4's `Untyped_Retype` to an untyped).
        invocation(
            "untyped-retype-vspace-root",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                VSPACE_ROOT_TYPE,
                VSPACE_ROOT_CHILD_ID,
                CNODE_CAP,
                FRAME_SLOT,
            ],
        ),
        invocation(
            "vspace-root-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        // seL4's `seL4_NotEnoughMemory` from the region: a child untyped of
        // 2^46 bytes, more than the root task's untyped holds past its free
        // index, refused before any write with the bytes left in MR0 (which
        // the carves before it set, so not pinned here).
        RoundTrip {
            returns: refused(UNTYPED_REGION_EXHAUSTED),
            ..invocation(
                "untyped-retype-region-exhausted",
                UNTYPED_RETYPE,
                UNTYPED_CAP,
                [
                    UNTYPED_REGION_EXHAUSTED_TYPE,
                    UNTYPED_CHILD_ID,
                    CNODE_CAP,
                    FRAME_SLOT,
                ],
            )
        },
        // A carve into an occupied slot (the untyped's own): refused
        // `targetSlotOccupied` from the checks' words, as every carve refusal
        // after the heap's is, without decoding the invocation again.
        RoundTrip {
            returns: refused(TARGET_SLOT_OCCUPIED),
            ..invocation(
                "untyped-retype-slot-occupied",
                UNTYPED_RETYPE,
                UNTYPED_CAP,
                [UNTYPED_TYPE, UNTYPED_CHILD_ID, CNODE_CAP, UNTYPED_SLOT],
            )
        },
        invocation(
            "untyped-retype-untyped",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [UNTYPED_TYPE, UNTYPED_CHILD_ID, CNODE_CAP, FRAME_SLOT],
        ),
        invocation(
            "child-untyped-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        invocation("untyped-reset", UNTYPED_RESET, UNTYPED_CAP, [0; 4]),
    ],
    &LIFECYCLE_SCENARIO,
];

/// **WS-UC UC4: a carve owns its cells, and the retire returns them.**  A
/// CNode carved and a capability (the boot endpoint's) copied into one of its
/// slots; that capability copied out of the carved CNode into a root slot,
/// where it outlives the CNode; the carved slot emptied (a CNode retires only
/// once every slot is empty) and the carved capability deleted, which retires
/// the CNode.  After the window the escaped copy is moved (refused with no
/// capability in its slot, so its success shows the copy outlived the
/// retire) and deleted, and the boot untyped reset, so the next run carves
/// where this one did.  Each step is a measured reading; across the first
/// five, [`carved_cnode_retire`] also reads this core's frees, and the
/// host-side gate holds both the cells allocated and the cells freed to the
/// CNode's carve pin: every cell the carve made comes back, the escaped copy
/// holding none of them, and no other.
#[cfg(feature = "hw_target")]
const CARVED_CNODE_RETIRE: [RoundTrip; 8] = [
    invocation(
        "untyped-retype-owned-cnode",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [CNODE_TYPE, PASSIVE_CHILD_IDS[3], CNODE_CAP, FRAME_SLOT],
    ),
    invocation(
        "owned-cnode-fill",
        CSPACE_COPY,
        cap_address(FRAME_SLOT),
        [
            CARVED_CNODE_SLOT,
            cap_address(CNODE_SLOT),
            cap_address(ENDPOINT_SLOT),
            CARVED_CNODE_RADIX | (64 << 8) | (ALL_RIGHTS << 16),
        ],
    ),
    invocation(
        "owned-cnode-copy-out",
        CSPACE_COPY,
        CNODE_CAP,
        [
            cap_address(MOVE_SLOT),
            cap_address(FRAME_SLOT),
            CARVED_CNODE_SLOT,
            64 | (CARVED_CNODE_RADIX << 8) | (ALL_RIGHTS << 16),
        ],
    ),
    invocation(
        "owned-cnode-slot-delete",
        CSPACE_DELETE,
        cap_address(FRAME_SLOT),
        [CARVED_CNODE_SLOT, 0, 0, 0],
    ),
    invocation(
        "owned-cnode-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [FRAME_SLOT, 0, 0, 0],
    ),
    invocation(
        "owned-cnode-escaped-move",
        CSPACE_MOVE,
        CNODE_CAP,
        root_slot_pair(MOVE_SLOT, MINT_SLOT),
    ),
    invocation(
        "owned-cnode-escaped-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MINT_SLOT, 0, 0, 0],
    ),
    invocation(
        "owned-cnode-untyped-reset",
        UNTYPED_RESET,
        UNTYPED_CAP,
        [0; 4],
    ),
];

/// The carved CNode's radix ([`CNODE_TYPE`]'s size bits; the carve gives it
/// no guard), the depth that names one of its slots from its own capability.
#[cfg(feature = "hw_target")]
const CARVED_CNODE_RADIX: u64 = CNODE_TYPE >> 8;

/// The carved CNode's slot the escaping capability is copied through.
#[cfg(feature = "hw_target")]
const CARVED_CNODE_SLOT: u64 = 1;

/// The steps of [`CARVED_CNODE_RETIRE`] its window reads across: the carve to
/// the retire.
#[cfg(feature = "hw_target")]
const CARVED_CNODE_WINDOW: usize = 5;

/// The carve-to-retire window of [`CARVED_CNODE_RETIRE`]: its steps measured
/// one by one, and across the carve, the fill, the copy out, the slot's
/// delete and the carved capability's delete this core's allocations and
/// frees, read under one mask so no tick's cells are
/// charged to it.  Printed as `owned-cnode-retire: … allocated A freed F`;
/// the host-side gate holds `A` and `F` each to the CNode's carve pin.
#[cfg(feature = "hw_target")]
fn carved_cnode_retire(which: &str) -> Option<bool> {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    let read = || {
        let allocated = crate::lean_heap::kernel_allocation_totals_on(core).ok()?.0;
        let freed = crate::lean_heap::kernel_frees_on(core).ok()?;
        Some((allocated, freed))
    };
    let saved = crate::interrupts::disable_interrupts();
    let before = read();
    let (window, rest) = CARVED_CNODE_RETIRE.split_at(CARVED_CNODE_WINDOW);
    let mut ok = window
        .iter()
        .all(|step| heap_allocations_round_trip(step, which) == Some(true));
    let after = read();
    if ok {
        ok = rest
            .iter()
            .all(|step| heap_allocations_round_trip(step, which) == Some(true));
    }
    crate::interrupts::restore_interrupts(saved);
    if !ok {
        return Some(false);
    }
    let (Some((a0, f0)), Some((a1, f1))) = (before, after) else {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: owned-cnode-retire: the heap counters could not be read"
        );
        return Some(false);
    };
    if a1 < a0 || f1 < f0 {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: owned-cnode-retire: a counter went back"
        );
        return Some(false);
    }
    crate::kprintln!(
        "[smp-test] heap-allocations-per-syscall: owned-cnode-retire: core {core}{which}: allocated {} freed {}",
        a1 - a0,
        f1 - f0
    );
    Some(true)
}

/// **The lifecycle branches no other scenario reaches**: the final deletes,
/// retires and refusals of untypeds, moved parents, bound threads, threads'
/// space slots, page tables, mapped frames and used VSpace roots, run as the
/// root task with the partner inactive, after the invocation
/// scenarios above have retired everything they carved.  Each step is
/// measured; the last rewinds the boot untyped, so the steady-state run
/// starts where the first did.
#[cfg(feature = "hw_target")]
static LIFECYCLE_SCENARIO: [RoundTrip; 82] = [
    // A child untyped carved, and an endpoint carved from it (its recorder a
    // carved untyped, not the boot one); its reset refused while the
    // endpoint's capability is its derivation child; its revoke, which deletes
    // that capability, the endpoint's last, so finalises and retires it; a
    // notification carved from it; a revoke of that notification's capability,
    // which has no child; then the untyped's last capability deleted while the
    // notification lives, so the boot untyped adopts the child and its
    // capability, whose delete retires it.
    invocation(
        "untyped-retype-parent-untyped",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [UNTYPED_TYPE, UNTYPED_CHILD_ID, CNODE_CAP, FRAME_SLOT],
    ),
    invocation(
        "child-retype-endpoint",
        UNTYPED_RETYPE,
        FRAME_CAP,
        [ENDPOINT_TYPE, PASSIVE_CHILD_IDS[0], CNODE_CAP, MOVE_SLOT],
    ),
    RoundTrip {
        returns: refused(REVOCATION_REQUIRED),
        ..invocation(
            "child-untyped-reset-refused",
            UNTYPED_RESET,
            FRAME_CAP,
            [0, 0, 0, 0],
        )
    },
    invocation(
        "child-untyped-revoke",
        CSPACE_REVOKE,
        CNODE_CAP,
        [FRAME_SLOT, 0, 0, 0],
    ),
    invocation(
        "child-retype-notification",
        UNTYPED_RETYPE,
        FRAME_CAP,
        [
            NOTIFICATION_TYPE,
            PASSIVE_CHILD_IDS[1],
            CNODE_CAP,
            MOVE_SLOT,
        ],
    ),
    invocation(
        "childless-revoke",
        CSPACE_REVOKE,
        CNODE_CAP,
        [MOVE_SLOT, 0, 0, 0],
    ),
    invocation(
        "parent-untyped-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [FRAME_SLOT, 0, 0, 0],
    ),
    invocation(
        "adopted-notification-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MOVE_SLOT, 0, 0, 0],
    ),
    // A capability with a derivation child moved: the child stays linked below
    // it in its new slot; the child deleted, then the moved capability, the
    // last.
    invocation(
        "untyped-retype-moved-parent",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            NOTIFICATION_TYPE,
            PASSIVE_CHILD_IDS[1],
            CNODE_CAP,
            FRAME_SLOT,
        ],
    ),
    invocation(
        "moved-parent-copy",
        CSPACE_COPY,
        CNODE_CAP,
        root_slot_copy(FRAME_SLOT, COPY_SLOT),
    ),
    invocation(
        "parent-cap-move",
        CSPACE_MOVE,
        CNODE_CAP,
        root_slot_pair(FRAME_SLOT, MINT_SLOT),
    ),
    invocation(
        "moved-parent-child-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [COPY_SLOT, 0, 0, 0],
    ),
    invocation(
        "moved-parent-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MINT_SLOT, 0, 0, 0],
    ),
    // A carved thread's last capability deleted while its scheduling context
    // is still bound to it: the finalisation unbinds the context (seL4's
    // `schedContext_unbindTCB`), which the context's own delete then retires.
    invocation(
        "untyped-retype-bound-context",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            SCHED_CONTEXT_TYPE,
            THREAD_CHILD_IDS[2],
            CNODE_CAP,
            MINT_SLOT,
        ],
    ),
    invocation(
        "untyped-retype-context-thread",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [TCB_TYPE, THREAD_CHILD_IDS[3], CNODE_CAP, FRAME_SLOT],
    ),
    invocation(
        "bind-context-thread",
        SCHED_CONTEXT_BIND,
        MINT_CAP,
        [FRAME_CAP, 0, 0, 0],
    ),
    invocation(
        "context-bound-tcb-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [FRAME_SLOT, 0, 0, 0],
    ),
    invocation(
        "released-context-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MINT_SLOT, 0, 0, 0],
    ),
    // A carved thread whose space slots hold the last capabilities to what
    // they name, replaced or destroyed: a carved VSpace root replaced by the
    // boot root (`threadSlotSet` retires the carved root and releases its
    // ASID); an empty carved CNode replaced; a carved CNode holding an
    // endpoint's only capability replaced (the zombie loop empties it first);
    // the same CNode as the thread's CSpace root when the thread's own last
    // capability is deleted (the loop goes down two levels, thread to CNode to
    // endpoint); and a carved VSpace root as its VSpace root then.
    invocation(
        "untyped-retype-space-tcb",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [TCB_TYPE, THREAD_CHILD_IDS[0], CNODE_CAP, FRAME_SLOT],
    ),
    invocation(
        "untyped-retype-space-root",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [VSPACE_ROOT_TYPE, VSPACE_ROOT_CHILD_ID, CNODE_CAP, MOVE_SLOT],
    ),
    invocation(
        "space-root-set-space",
        TCB_SET_SPACE,
        FRAME_CAP,
        [CNODE_CAP, MOVE_CAP, 0, 0],
    ),
    invocation(
        "space-root-cap-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MOVE_SLOT, 0, 0, 0],
    ),
    invocation(
        "space-root-replaced",
        TCB_SET_SPACE,
        FRAME_CAP,
        [CNODE_CAP, VSPACE_CAP, 0, 0],
    ),
    invocation(
        "untyped-retype-replaced-cnode",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [CNODE_TYPE, PASSIVE_CHILD_IDS[3], CNODE_CAP, MOVE_SLOT],
    ),
    invocation(
        "replaced-cnode-set-space",
        TCB_SET_SPACE,
        FRAME_CAP,
        [MOVE_CAP, VSPACE_CAP, 0, 0],
    ),
    invocation(
        "replaced-cnode-cap-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MOVE_SLOT, 0, 0, 0],
    ),
    invocation(
        "replaced-cnode-retired",
        TCB_SET_SPACE,
        FRAME_CAP,
        [CNODE_CAP, VSPACE_CAP, 0, 0],
    ),
    invocation(
        "untyped-retype-zombie-cnode",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [CNODE_TYPE, PASSIVE_CHILD_IDS[3], CNODE_CAP, MOVE_SLOT],
    ),
    invocation(
        "untyped-retype-zombie-endpoint",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [ENDPOINT_TYPE, PASSIVE_CHILD_IDS[0], MOVE_CAP, 0],
    ),
    invocation(
        "zombie-cnode-set-space",
        TCB_SET_SPACE,
        FRAME_CAP,
        [MOVE_CAP, VSPACE_CAP, 0, 0],
    ),
    invocation(
        "zombie-cnode-cap-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MOVE_SLOT, 0, 0, 0],
    ),
    invocation(
        "zombie-cnode-replaced",
        TCB_SET_SPACE,
        FRAME_CAP,
        [CNODE_CAP, VSPACE_CAP, 0, 0],
    ),
    invocation(
        "untyped-retype-nested-cnode",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [CNODE_TYPE, PASSIVE_CHILD_IDS[3], CNODE_CAP, MOVE_SLOT],
    ),
    invocation(
        "untyped-retype-nested-endpoint",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [ENDPOINT_TYPE, PASSIVE_CHILD_IDS[0], MOVE_CAP, 0],
    ),
    invocation(
        "nested-cnode-set-space",
        TCB_SET_SPACE,
        FRAME_CAP,
        [MOVE_CAP, VSPACE_CAP, 0, 0],
    ),
    invocation(
        "nested-cnode-cap-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MOVE_SLOT, 0, 0, 0],
    ),
    invocation(
        "nested-space-tcb-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [FRAME_SLOT, 0, 0, 0],
    ),
    invocation(
        "untyped-retype-rooted-tcb",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [TCB_TYPE, THREAD_CHILD_IDS[0], CNODE_CAP, FRAME_SLOT],
    ),
    invocation(
        "untyped-retype-thread-root",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [VSPACE_ROOT_TYPE, VSPACE_ROOT_CHILD_ID, CNODE_CAP, MOVE_SLOT],
    ),
    invocation(
        "thread-root-set-space",
        TCB_SET_SPACE,
        FRAME_CAP,
        [CNODE_CAP, MOVE_CAP, 0, 0],
    ),
    invocation(
        "thread-root-cap-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MOVE_SLOT, 0, 0, 0],
    ),
    invocation(
        "rooted-tcb-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [FRAME_SLOT, 0, 0, 0],
    ),
    // Three tables installed in the root task's space; the first's unmap
    // refused while the second hangs below it; a frame carved and mapped under
    // them, mapped again at the same ASID and address with other rights (a
    // remap, as seL4's `Page_Map` allows, here to code), mapped at another
    // address (refused: the capability records its mapping), its code unified
    // and unmapped (the executable unmap's instruction-cache maintenance) and
    // the frame mapped again, an address with no mapping unmapped (refused),
    // and the frame's last
    // capability deleted while it is mapped, which unmaps it; then the first
    // table's last capability deleted while it is installed with the others
    // below it, which takes the subtree out; the second's unmap, its record
    // stale, and both deleted; and a table never installed unmapped and
    // deleted.
    invocation(
        "untyped-retype-installed-table-1",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            PAGE_TABLE_TYPE,
            PAGE_TABLE_CHILD_IDS[0],
            CNODE_CAP,
            PAGE_TABLE_SLOTS[0],
        ],
    ),
    invocation(
        "installed-table-map-1",
        PAGE_TABLE_MAP,
        PAGE_TABLE_CAPS[0],
        [VSPACE_CAP, FRAME_VADDR, 0, 0],
    ),
    invocation(
        "untyped-retype-installed-table-2",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            PAGE_TABLE_TYPE,
            PAGE_TABLE_CHILD_IDS[1],
            CNODE_CAP,
            PAGE_TABLE_SLOTS[1],
        ],
    ),
    invocation(
        "installed-table-map-2",
        PAGE_TABLE_MAP,
        PAGE_TABLE_CAPS[1],
        [VSPACE_CAP, FRAME_VADDR, 0, 0],
    ),
    invocation(
        "untyped-retype-installed-table-3",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            PAGE_TABLE_TYPE,
            PAGE_TABLE_CHILD_IDS[2],
            CNODE_CAP,
            PAGE_TABLE_SLOTS[2],
        ],
    ),
    invocation(
        "installed-table-map-3",
        PAGE_TABLE_MAP,
        PAGE_TABLE_CAPS[2],
        [VSPACE_CAP, FRAME_VADDR, 0, 0],
    ),
    RoundTrip {
        returns: refused(REVOCATION_REQUIRED),
        ..invocation(
            "installed-table-unmap-refused",
            PAGE_TABLE_UNMAP,
            PAGE_TABLE_CAPS[0],
            [0, 0, 0, 0],
        )
    },
    invocation(
        "untyped-retype-mapped-frame",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [FRAME_TYPE, FRAME_CHILD_ID, CNODE_CAP, MOVE_SLOT],
    ),
    invocation(
        "mapped-frame-map",
        VSPACE_MAP,
        VSPACE_CAP,
        [ROOT_ASID, FRAME_VADDR, MOVE_CAP, FRAME_PERMS],
    ),
    invocation(
        "mapped-frame-remap",
        VSPACE_MAP,
        VSPACE_CAP,
        [ROOT_ASID, FRAME_VADDR, MOVE_CAP, CODE_PERMS],
    ),
    RoundTrip {
        returns: refused(INVALID_ARGUMENT),
        ..invocation(
            "mapped-frame-remap-other-vaddr",
            VSPACE_MAP,
            VSPACE_CAP,
            [ROOT_ASID, FRAME_COPY_VADDR, MOVE_CAP, FRAME_PERMS],
        )
    },
    invocation(
        "mapped-frame-unify",
        VSPACE_UNIFY_INSTRUCTION,
        VSPACE_CAP,
        [ROOT_ASID, FRAME_VADDR, 0, 0],
    ),
    invocation(
        "mapped-frame-unmap-code",
        VSPACE_UNMAP,
        VSPACE_CAP,
        [ROOT_ASID, FRAME_VADDR, 0, 0],
    ),
    invocation(
        "mapped-frame-map-again",
        VSPACE_MAP,
        VSPACE_CAP,
        [ROOT_ASID, FRAME_VADDR, MOVE_CAP, FRAME_PERMS],
    ),
    RoundTrip {
        returns: refused(TRANSLATION_FAULT),
        ..invocation(
            "unmap-nothing",
            VSPACE_UNMAP,
            VSPACE_CAP,
            [ROOT_ASID, FRAME_COPY_VADDR, 0, 0],
        )
    },
    invocation(
        "mapped-frame-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MOVE_SLOT, 0, 0, 0],
    ),
    invocation(
        "installed-table-delete-1",
        CSPACE_DELETE,
        CNODE_CAP,
        [PAGE_TABLE_SLOTS[0], 0, 0, 0],
    ),
    invocation(
        "stale-table-unmap-2",
        PAGE_TABLE_UNMAP,
        PAGE_TABLE_CAPS[1],
        [0, 0, 0, 0],
    ),
    invocation(
        "stale-table-delete-2",
        CSPACE_DELETE,
        CNODE_CAP,
        [PAGE_TABLE_SLOTS[1], 0, 0, 0],
    ),
    invocation(
        "stale-table-delete-3",
        CSPACE_DELETE,
        CNODE_CAP,
        [PAGE_TABLE_SLOTS[2], 0, 0, 0],
    ),
    invocation(
        "untyped-retype-uninstalled-table",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            PAGE_TABLE_TYPE,
            PAGE_TABLE_CHILD_IDS[0],
            CNODE_CAP,
            PAGE_TABLE_SLOTS[0],
        ],
    ),
    invocation(
        "uninstalled-table-unmap",
        PAGE_TABLE_UNMAP,
        PAGE_TABLE_CAPS[0],
        [0, 0, 0, 0],
    ),
    invocation(
        "uninstalled-table-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [PAGE_TABLE_SLOTS[0], 0, 0, 0],
    ),
    // A carved VSpace root with three tables installed and a frame mapped, its
    // last capability deleted: the ASID released with its tables attached; the
    // deepest table's unmap, its root gone; the tables' and the frame's last
    // capabilities deleted, each naming the gone root.
    invocation(
        "untyped-retype-tabled-root",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            VSPACE_ROOT_TYPE,
            VSPACE_ROOT_CHILD_ID,
            CNODE_CAP,
            FRAME_SLOT,
        ],
    ),
    invocation(
        "untyped-retype-tabled-root-table-1",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            PAGE_TABLE_TYPE,
            PAGE_TABLE_CHILD_IDS[0],
            CNODE_CAP,
            PAGE_TABLE_SLOTS[0],
        ],
    ),
    invocation(
        "tabled-root-table-map-1",
        PAGE_TABLE_MAP,
        PAGE_TABLE_CAPS[0],
        [FRAME_CAP, FRAME_VADDR, 0, 0],
    ),
    invocation(
        "untyped-retype-tabled-root-table-2",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            PAGE_TABLE_TYPE,
            PAGE_TABLE_CHILD_IDS[1],
            CNODE_CAP,
            PAGE_TABLE_SLOTS[1],
        ],
    ),
    invocation(
        "tabled-root-table-map-2",
        PAGE_TABLE_MAP,
        PAGE_TABLE_CAPS[1],
        [FRAME_CAP, FRAME_VADDR, 0, 0],
    ),
    invocation(
        "untyped-retype-tabled-root-table-3",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            PAGE_TABLE_TYPE,
            PAGE_TABLE_CHILD_IDS[2],
            CNODE_CAP,
            PAGE_TABLE_SLOTS[2],
        ],
    ),
    invocation(
        "tabled-root-table-map-3",
        PAGE_TABLE_MAP,
        PAGE_TABLE_CAPS[2],
        [FRAME_CAP, FRAME_VADDR, 0, 0],
    ),
    invocation(
        "untyped-retype-tabled-root-frame",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [FRAME_TYPE, FRAME_CHILD_ID, CNODE_CAP, MOVE_SLOT],
    ),
    invocation(
        "tabled-root-map",
        VSPACE_MAP,
        FRAME_CAP,
        [CARVED_ROOT_ASID, FRAME_VADDR, MOVE_CAP, FRAME_PERMS],
    ),
    // The frame mapped in the carved root's address space, mapped through the
    // root task's own: refused, the capability's mapping is in another ASID.
    RoundTrip {
        returns: refused(INVALID_CAPABILITY),
        ..invocation(
            "tabled-root-frame-other-asid",
            VSPACE_MAP,
            VSPACE_CAP,
            [ROOT_ASID, FRAME_VADDR, MOVE_CAP, FRAME_PERMS],
        )
    },
    invocation(
        "tabled-root-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [FRAME_SLOT, 0, 0, 0],
    ),
    invocation(
        "orphaned-table-unmap-3",
        PAGE_TABLE_UNMAP,
        PAGE_TABLE_CAPS[2],
        [0, 0, 0, 0],
    ),
    invocation(
        "orphaned-table-delete-3",
        CSPACE_DELETE,
        CNODE_CAP,
        [PAGE_TABLE_SLOTS[2], 0, 0, 0],
    ),
    invocation(
        "orphaned-table-delete-2",
        CSPACE_DELETE,
        CNODE_CAP,
        [PAGE_TABLE_SLOTS[1], 0, 0, 0],
    ),
    invocation(
        "orphaned-table-delete-1",
        CSPACE_DELETE,
        CNODE_CAP,
        [PAGE_TABLE_SLOTS[0], 0, 0, 0],
    ),
    invocation(
        "orphaned-frame-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MOVE_SLOT, 0, 0, 0],
    ),
    // The boot untyped rewound, every object carved from it retired, so the
    // steady-state run carves where the first did.
    invocation(
        "lifecycle-untyped-reset",
        UNTYPED_RESET,
        UNTYPED_CAP,
        [0, 0, 0, 0],
    ),
];

/// The refusal frame's `x1` for `KernelError` discriminant `code`: its label
/// and its message length, the word count of the code's payload (seL4's
/// `setMRs_syscall_error`: one for `InvalidCapability`, `InvalidArgument` and
/// `UntypedRegionExhausted`, two for `RangeError`, none for a code without a
/// payload).  A failed lookup's length depends on its fault
/// ([`refused_with`]).
#[cfg(feature = "hw_target")]
const fn refused(code: u64) -> Option<(u64, [Option<u64>; 4])> {
    let length = match code {
        INVALID_CAPABILITY | INVALID_ARGUMENT | UNTYPED_REGION_EXHAUSTED => 1,
        RANGE_ERROR => 2,
        _ => 0,
    };
    refused_with(code, length, [None; 4])
}

/// The refusal frame for `code` with message length `length` and the payload
/// words `mrs` expected in `x2`-`x5` (`None` where not checked).
#[cfg(feature = "hw_target")]
const fn refused_with(
    code: u64,
    length: u64,
    mrs: [Option<u64>; 4],
) -> Option<(u64, [Option<u64>; 4])> {
    Some((
        ((crate::svc_dispatch::ERROR_LABEL_BASE + code) << 12) | length,
        mrs,
    ))
}

/// `KernelError.rangeError` and `.failedLookup`'s discriminants (seL4's
/// `seL4_RangeError` and `seL4_FailedLookup`).
#[cfg(feature = "hw_target")]
const RANGE_ERROR: u64 = 59;
#[cfg(feature = "hw_target")]
const FAILED_LOOKUP: u64 = 60;
/// The least budget a configure admits (`configureMinBudget`, seL4-MCS's
/// `MIN_BUDGET`): the `rangeErrorMin` of a configure's budget refusal.
#[cfg(feature = "hw_target")]
const CONFIGURE_MIN_BUDGET: u64 = 1;
/// The greatest budget or period a configure admits (`configureMaxPeriod`,
/// seL4-MCS's `MAX_PERIOD_US` in ticks, `UINT64_MAX / 8`): the
/// `rangeErrorMax` of a configure's budget or period refusal.
#[cfg(feature = "hw_target")]
const CONFIGURE_MAX_PERIOD: u64 = 0x1FFF_FFFF_FFFF_FFFF;
/// A period past `2^63` (its top bit set), above `CONFIGURE_MAX_PERIOD`.
#[cfg(feature = "hw_target")]
const WIDE_PERIOD: u64 = 1 << 63;
/// An argument word at or above `2^63`, the least word a `Nat` holds only as
/// a heap number.
#[cfg(feature = "hw_target")]
const WIDE_WORD: u64 = 1 << 63;
/// `KernelError.asidNotBound`, `.addressOutOfBounds` and
/// `.invalidSyscallArgument`'s discriminants (`sele4n-types`).
#[cfg(feature = "hw_target")]
const ASID_NOT_BOUND: u64 = 9;
#[cfg(feature = "hw_target")]
const ADDRESS_OUT_OF_BOUNDS: u64 = 26;
#[cfg(feature = "hw_target")]
const INVALID_SYSCALL_ARGUMENT: u64 = 41;
/// `KernelError.invalidCapability`, `.translationFault`, `.revocationRequired`
/// and `.invalidArgument`'s discriminants (`sele4n-types`).
#[cfg(feature = "hw_target")]
const INVALID_CAPABILITY: u64 = 0;
#[cfg(feature = "hw_target")]
const TRANSLATION_FAULT: u64 = 12;
#[cfg(feature = "hw_target")]
const TARGET_SLOT_OCCUPIED: u64 = 18;
#[cfg(feature = "hw_target")]
const REVOCATION_REQUIRED: u64 = 38;
#[cfg(feature = "hw_target")]
const INVALID_ARGUMENT: u64 = 39;
/// The ASID a carved VSpace root is given (`freshAsid?`, the least free one
/// from 1): the root task's space holds ASID 1 and the untrusted partition's
/// ASID 2, so the first carved root takes 3.
#[cfg(feature = "hw_target")]
const CARVED_ROOT_ASID: u64 = 3;

/// **WS-ZA ZA5.4 part 25: the final delete of a reply whose caller still waits
/// on it**, run as the root task once the partner is suspended (so the roles
/// are fixed): a reply carved, a reply capability minted from it into the mint
/// slot, a receive through that capability that blocks, the partner's call
/// that wakes the root task holding the reply and blocks for the answer, the
/// minted capability's delete (not final), then the carved one's, which
/// cancels the partner's call (seL4's `reply_remove`), makes it `.Inactive`
/// and retires the reply.  The partner ends where the suspend left it.
#[cfg(feature = "hw_target")]
const BUSY_REPLY_SCENARIO: [RoundTrip; 6] = [
    invocation(
        "untyped-retype-busy-reply",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [REPLY_TYPE, PASSIVE_CHILD_IDS[2], CNODE_CAP, FRAME_SLOT],
    ),
    partner_step(
        "mint-busy-reply-cap",
        MINT_REPLY_CAP,
        CNODE_CAP,
        2,
        [FRAME_SLOT, MINT_SLOT],
        false,
    ),
    partner_step(
        "receive-with-carved-reply",
        RECEIVE,
        ENDPOINT_CAP,
        1,
        [MINT_CAP, 0],
        true,
    ),
    partner_step(
        "call-to-carved-reply",
        CALL,
        ENDPOINT_CAP,
        1,
        [0x66, 0],
        true,
    ),
    invocation(
        "busy-reply-cap-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MINT_SLOT, 0, 0, 0],
    ),
    invocation(
        "busy-reply-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [FRAME_SLOT, 0, 0, 0],
    ),
];

/// **WS-ZA ZA5.4 part 25: the final delete of a reply a blocked receiver has
/// stashed**, run as the root task with the partner resumed: a reply carved, a
/// reply capability minted from it into the mint slot, a receive through that
/// capability that blocks holding the reply stashed, then, as the partner, the
/// minted capability's delete (not final) and the carved one's, which clears
/// the root task's stash (seL4's `reply_unlink`) and retires the reply, and a
/// send that finds the root task still waiting and continues.  The partner is
/// then suspended, unmeasured.
#[cfg(feature = "hw_target")]
const STASHED_REPLY_SCENARIO: [RoundTrip; 6] = [
    invocation(
        "untyped-retype-stashed-reply",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [REPLY_TYPE, PASSIVE_CHILD_IDS[2], CNODE_CAP, FRAME_SLOT],
    ),
    partner_step(
        "mint-stashed-reply-cap",
        MINT_REPLY_CAP,
        CNODE_CAP,
        2,
        [FRAME_SLOT, MINT_SLOT],
        false,
    ),
    partner_step(
        "receive-stashing-reply",
        RECEIVE,
        ENDPOINT_CAP,
        1,
        [MINT_CAP, 0],
        true,
    ),
    invocation(
        "stashed-reply-cap-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MINT_SLOT, 0, 0, 0],
    ),
    invocation(
        "stashed-reply-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [FRAME_SLOT, 0, 0, 0],
    ),
    partner_step(
        "send-to-unstashed-receiver",
        SEND,
        ENDPOINT_CAP,
        1,
        [0x77, 0],
        false,
    ),
];

/// The partner scenarios' setup, issued once and not measured: the partner
/// thread resumed onto core 0's run queue, the reply capability minted from
/// the reply object into its free slot, and the badged endpoint capability
/// minted from the endpoint's.
/// **WS-ZA ZA5.13: the declassification scenario**, run on the exerciser
/// image's labeling (`SeLe4n.Platform.QemuVirt.Exerciser`): its boot domain is
/// the top of the lattice and its downgrades are from there to the upper
/// domain and from the upper domain to the low band (WS-ZA ZA6.35, used by
/// [`bound_declassified_signals`]).  A notification is carved at an upper id
/// ([`UPPER_NOTIFICATION_ID`], unmeasured, into the frame slot), then, as
/// whichever thread is current:
/// - the notification declassified (one audit record, and the caller tagged
///   with its timestamp);
/// - a declassified signal on it (one more record: no thread waits, so the
///   one hop is the caller's into the notification);
/// - a send that blocks carrying the caller's tags, and the other thread's
///   receive that takes the message — and the tags — from it: the tainted
///   path, IPC whose content carries a declassification's provenance;
/// - a wait that takes the stored badge, a wait on the notification that
///   blocks, and the other thread's declassified signal that wakes it (one more record, the second hop an
///   ordinary flow);
/// - a refused declassification, unmeasured, then the audit monitor's drain
///   and reads ([`AUDIT_SCENARIO`]) and the carved notification's only
///   capability deleted.
///
/// Run twice like every scenario: the second run's caller and receiver are
/// already tagged, so it is the steady state of the tainted path too.
#[cfg(feature = "hw_target")]
const DECLASSIFICATION_SCENARIO: [RoundTrip; 7] = [
    RoundTrip {
        name: "declassify",
        syscall: DECLASSIFY,
        cptr: FRAME_CAP,
        msg_len: 0,
        msg: [0; 4],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    RoundTrip {
        name: "declassified-signal",
        syscall: DECLASSIFY_SIGNAL,
        cptr: FRAME_CAP,
        msg_len: 0,
        msg: [0, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    partner_step(
        "send-tainted-blocks",
        SEND,
        ENDPOINT_CAP,
        1,
        [0x77, 0],
        true,
    ),
    partner_step("receive-tainted", RECEIVE, ENDPOINT_CAP, 0, [0, 0], false),
    // WS-ZA ZA6.35: the stored badge taken by a wait, then a declassified
    // signal that wakes the notification's next waiter: its first hop the
    // caller's downgrade into the notification (one record), its second the
    // notification's ordinary flow into the waiter.
    partner_step(
        "declassified-wait-pending",
        WAIT,
        FRAME_CAP,
        0,
        [0, 0],
        false,
    ),
    partner_step("declassified-wait-blocks", WAIT, FRAME_CAP, 0, [0, 0], true),
    partner_step(
        "declassified-signal-wakes",
        DECLASSIFY_SIGNAL,
        FRAME_CAP,
        0,
        [0, 0],
        false,
    ),
];
/// A refused declassification (WS-ZA ZA6.35), measured, and it gives the
/// refusal ledger a slot for the audit reads to read: the boot domain's endpoint
/// is in the caller's own domain, a flow the base lattice already permits,
/// which `.declassify` refuses (`flowDenied`) and the seam records.
#[cfg(feature = "hw_target")]
const DECLASSIFICATION_REFUSAL: RoundTrip = RoundTrip {
    name: "declassify-refused",
    syscall: DECLASSIFY,
    cptr: ENDPOINT_CAP,
    msg_len: 0,
    msg: [0; 4],
    primed: None,
    blocks: false,
    caps_or_badges: None,
    overflow: None,
    returns: Some((
        (crate::svc_dispatch::ERROR_LABEL_BASE + FLOW_DENIED) << 12,
        [None; 4],
    )),
};
/// `KernelError::FlowDenied`'s discriminant.
#[cfg(feature = "hw_target")]
const FLOW_DENIED: u64 = 13;
/// A declassification whose capability address misses the root guard, measured:
/// a refused lookup whose error carries a payload (a guard mismatch) recorded in
/// the refusal ledger from its words, so neither the error nor the record is
/// built on the entry path.  The address is a bare slot number, below the root
/// guard.  The fifth word (`GuardFound`'s size) goes to the root task's IPC
/// buffer, so the length is 5; the buffer is not at `FRAME_VADDR` in this
/// phase, so the word itself is not probed.
#[cfg(feature = "hw_target")]
const DECLASSIFICATION_LOOKUP_REFUSAL: RoundTrip = RoundTrip {
    name: "declassify-guard-mismatch-refused",
    cptr: 1,
    returns: refused_with(
        FAILED_LOOKUP,
        5,
        [Some(0), Some(4), Some(64), Some(ROOT_CNODE_GUARD >> 6)],
    ),
    ..DECLASSIFICATION_REFUSAL
};
/// **The audit monitor's reads** (WS-ZA ZA5.13, every opcode family at
/// ZA6.35), through the boot audit capability ([`AUDIT_CAP`]): the trail's
/// first entry drained, so the trail has an epoch for the archived verdict to
/// read below; the status, an entry's field, its authorization basis (a chunk
/// past the first among them), the refusal ledger's status, counters and the
/// refused declassification's slot, and the causality verdicts; then the
/// whole trail drained and the carved notification's only capability deleted.
#[cfg(feature = "hw_target")]
const AUDIT_SCENARIO: [RoundTrip; 22] = [
    // A drain and a read a word short of their arguments, through the audit
    // capability: refused `TruncatedMessage` once the target and the right
    // are checked, the trail untouched.
    truncated("audit-drain-short", AUDIT_DRAIN, AUDIT_CAP, 0),
    truncated("audit-read-short", AUDIT_READ, AUDIT_CAP, 2),
    RoundTrip {
        name: "audit-drain-first",
        syscall: AUDIT_DRAIN,
        cptr: AUDIT_CAP,
        msg_len: 1,
        msg: [1, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // The trail's status.
    RoundTrip {
        name: "audit-read-status",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [0, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // The target object of the first visible entry, chunk 0.
    RoundTrip {
        name: "audit-read-entry",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [7, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // The first visible entry's authorization basis: its byte count.
    RoundTrip {
        name: "audit-read-basis-count",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [10, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // Its second chunk: a chunk past the first.
    RoundTrip {
        name: "audit-read-basis-chunk",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [11, 0, 1, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // The refusal ledger's status.
    RoundTrip {
        name: "audit-read-refusal-status",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [12, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // Its counters.
    RoundTrip {
        name: "audit-read-refusal-counters",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [13, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // Slot 0's refusal: its tags.
    RoundTrip {
        name: "audit-read-refusal-tags",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [14, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // Its subject's chunk count.
    RoundTrip {
        name: "audit-read-refusal-subject-count",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [15, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // Its subject domain's chunk count.
    RoundTrip {
        name: "audit-read-refusal-domain-count",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [16, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // Its requested target's chunk count.
    RoundTrip {
        name: "audit-read-refusal-target-count",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [17, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // Its subject, chunk 0.
    RoundTrip {
        name: "audit-read-refusal-subject",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [18, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // Its subject domain, chunk 0.
    RoundTrip {
        name: "audit-read-refusal-domain",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [19, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // Its requested target, chunk 0.
    RoundTrip {
        name: "audit-read-refusal-target",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [20, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // Its refused receiver's chunk count (none: 0).
    RoundTrip {
        name: "audit-read-refusal-receiver-count",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [25, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // Whether the second visible entry names the first.
    RoundTrip {
        name: "audit-read-chain-predecessor",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [27, 1, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // The same verdict over the pair named in full.
    RoundTrip {
        name: "audit-read-chain-entry",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [28, 1, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    // Whether the first visible entry names the drained timestamp 0 of its run.
    RoundTrip {
        name: "audit-read-chain-archived",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [29, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    RoundTrip {
        name: "audit-drain",
        syscall: AUDIT_DRAIN,
        cptr: AUDIT_CAP,
        msg_len: 1,
        msg: [256, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    },
    invocation(
        "upper-notification-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [FRAME_SLOT, 0, 0, 0],
    ),
];
/// The id the declassification scenario carves its notification at: past the
/// exerciser labeling's boundary (`qemuVirtUpperDomainBase`, `0x10_0000`), so
/// the notification is in the upper domain.
#[cfg(feature = "hw_target")]
const UPPER_NOTIFICATION_ID: u64 = 0x10_0010;
/// The declassification scenario's carve, unmeasured.
#[cfg(feature = "hw_target")]
const UPPER_NOTIFICATION_CARVE: RoundTrip = invocation(
    "untyped-retype-upper-notification",
    UNTYPED_RETYPE,
    UNTYPED_CAP,
    [
        NOTIFICATION_TYPE,
        UPPER_NOTIFICATION_ID,
        CNODE_CAP,
        FRAME_SLOT,
    ],
);
/// The low band's thread: its id in the exerciser labeling's lower trusted
/// domain.
#[cfg(feature = "hw_target")]
const LOW_THREAD_ID: u64 = 0x8_0000;
/// The low band's endpoint, the one the low thread receives on.
#[cfg(feature = "hw_target")]
const LOW_ENDPOINT_ID: u64 = 0x8_0001;
/// The boot-domain notification bound to the root task, then to the low thread.
#[cfg(feature = "hw_target")]
const BOOT_DOMAIN_NOTIFICATION_ID: u64 = PASSIVE_CHILD_IDS[1];
#[cfg(feature = "hw_target")]
const LOW_THREAD_CAP: u64 = CHAIN_TCB_CAP;
#[cfg(feature = "hw_target")]
const LOW_ENDPOINT_CAP: u64 = STACK_TOP_TCB_CAP;
/// `KernelError::DeclassificationDeniedAtReceiver`'s discriminant.
#[cfg(feature = "hw_target")]
const DECLASSIFICATION_DENIED_AT_RECEIVER: u64 = 56;
/// The refusal ledger's ring size (`refusalRingSize`).
#[cfg(feature = "hw_target")]
const REFUSAL_RING_SIZE: u64 = 32;
/// The bound scenario's setup, unmeasured.
#[cfg(feature = "hw_target")]
const BOUND_SIGNAL_SETUP: [RoundTrip; 10] = [
    invocation(
        "untyped-retype-low-thread",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [TCB_TYPE, LOW_THREAD_ID, CNODE_CAP, CHAIN_TCB_SLOT],
    ),
    invocation(
        "low-thread-set-space",
        TCB_SET_SPACE,
        LOW_THREAD_CAP,
        [CNODE_CAP, VSPACE_CAP, 0, 0],
    ),
    invocation(
        "low-thread-set-priority",
        TCB_SET_PRIORITY,
        LOW_THREAD_CAP,
        [PARTNER_PRIORITY, 0, 0, 0],
    ),
    invocation(
        "untyped-retype-low-endpoint",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            ENDPOINT_TYPE,
            LOW_ENDPOINT_ID,
            CNODE_CAP,
            STACK_TOP_TCB_SLOT,
        ],
    ),
    invocation(
        "untyped-retype-boot-domain-notification",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            NOTIFICATION_TYPE,
            BOOT_DOMAIN_NOTIFICATION_ID,
            CNODE_CAP,
            MOVE_SLOT,
        ],
    ),
    UPPER_NOTIFICATION_CARVE,
    invocation(
        "root-bind-boot-domain-notification",
        TCB_BIND_NOTIFICATION,
        ROOT_TCB_CAP,
        [MOVE_CAP, 0, 0, 0],
    ),
    invocation(
        "bound-irq-control-get",
        IRQ_CONTROL_GET,
        IRQ_CONTROL_CAP,
        [IRQ_BOUND_LINE as u64, CNODE_CAP, IRQ_BOUND_HANDLER_SLOT, 0],
    ),
    invocation(
        "bound-irq-handler-set-notification",
        IRQ_HANDLER_SET_NOTIFICATION,
        cap_address(IRQ_BOUND_HANDLER_SLOT),
        [MOVE_CAP, 0, 0, 0],
    ),
    invocation("low-thread-resume", TCB_RESUME, LOW_THREAD_CAP, [0; 4]),
];
/// The root task's receive on the boot endpoint, which blocks and runs the
/// low thread, unmeasured.
#[cfg(feature = "hw_target")]
const BOUND_ROOT_RECEIVES: RoundTrip = partner_step(
    "bound-root-receives",
    RECEIVE,
    ENDPOINT_CAP,
    0,
    [0, 0],
    true,
);
/// The low thread's declassified signal to the root task, bound and blocked.
#[cfg(feature = "hw_target")]
const DECLASSIFIED_SIGNAL_BOUND: RoundTrip = partner_step(
    "declassified-signal-bound",
    DECLASSIFY_SIGNAL,
    MOVE_CAP,
    0,
    [0, 0],
    false,
);
/// The low thread's plain signal to the root task, bound and blocked.
#[cfg(feature = "hw_target")]
const SIGNAL_BOUND: RoundTrip = partner_step("signal-bound", SIGNAL, MOVE_CAP, 1, [6, 0], false);
/// The low thread's yield, which runs the woken root task, unmeasured.
#[cfg(feature = "hw_target")]
const LOW_THREAD_YIELDS: RoundTrip = kernel_step("low-thread-yields", YIELD);
/// The bound line's acknowledge after its signal, unmeasured.
#[cfg(feature = "hw_target")]
const BOUND_IRQ_ACK: RoundTrip = irq_handler_ack("bound-irq-handler-ack", IRQ_BOUND_HANDLER_SLOT);
/// The low thread's receive on its endpoint, which blocks and runs the root
/// task, unmeasured.
#[cfg(feature = "hw_target")]
const LOW_THREAD_RECEIVES: RoundTrip = partner_step(
    "low-thread-receives",
    RECEIVE,
    LOW_ENDPOINT_CAP,
    0,
    [0, 0],
    true,
);
/// The upper notification bound to the low thread, unmeasured.
#[cfg(feature = "hw_target")]
const BIND_UPPER_TO_LOW_THREAD: RoundTrip = invocation(
    "low-thread-bind-upper-notification",
    TCB_BIND_NOTIFICATION,
    LOW_THREAD_CAP,
    [FRAME_CAP, 0, 0, 0],
);
/// The root task's declassified signal on the upper notification, both hops
/// downgrades.
#[cfg(feature = "hw_target")]
const DECLASSIFIED_SIGNAL_TWO_HOP: RoundTrip = partner_step(
    "declassified-signal-two-hop",
    DECLASSIFY_SIGNAL,
    FRAME_CAP,
    0,
    [0, 0],
    false,
);
/// The root task's yield, which runs the woken low thread, unmeasured.
#[cfg(feature = "hw_target")]
const BOUND_ROOT_YIELDS: RoundTrip = kernel_step("bound-root-yields", YIELD);
/// The notifications swapped, unmeasured: the upper one unbound from the low
/// thread, the boot domain's from the root task and bound to the low thread.
#[cfg(feature = "hw_target")]
const BOUND_SIGNAL_SWAP: [RoundTrip; 3] = [
    invocation(
        "low-thread-unbind-upper-notification",
        TCB_UNBIND_NOTIFICATION,
        LOW_THREAD_CAP,
        [0; 4],
    ),
    invocation(
        "root-unbind-boot-domain-notification",
        TCB_UNBIND_NOTIFICATION,
        ROOT_TCB_CAP,
        [0; 4],
    ),
    invocation(
        "low-thread-bind-boot-domain-notification",
        TCB_BIND_NOTIFICATION,
        LOW_THREAD_CAP,
        [MOVE_CAP, 0, 0, 0],
    ),
];
/// The root task's declassified signal refused at its second hop, measured.
#[cfg(feature = "hw_target")]
const DECLASSIFIED_SIGNAL_REFUSED_AT_RECEIVER: RoundTrip = RoundTrip {
    name: "declassified-signal-refused-at-receiver",
    syscall: DECLASSIFY_SIGNAL,
    cptr: MOVE_CAP,
    msg_len: 0,
    msg: [0, 0, 0, 0],
    primed: None,
    blocks: false,
    caps_or_badges: None,
    overflow: None,
    returns: Some((
        (crate::svc_dispatch::ERROR_LABEL_BASE + DECLASSIFICATION_DENIED_AT_RECEIVER) << 12,
        [None; 4],
    )),
};
/// The refusal ledger's status, read unmeasured for the refusal's slot.
#[cfg(feature = "hw_target")]
const BOUND_REFUSAL_STATUS: RoundTrip = RoundTrip {
    name: "bound-refusal-status",
    syscall: AUDIT_READ,
    cptr: AUDIT_CAP,
    msg_len: 3,
    msg: [12, 0, 0, 0],
    primed: None,
    blocks: false,
    caps_or_badges: None,
    overflow: None,
    returns: None,
};
/// The slots emptied again, unmeasured: the bound line's handler cleared and
/// deleted, the low thread's capability deleted (its finalisation cancels its
/// receive and unbinds its notification), then the endpoint's and the two
/// notifications'.
#[cfg(feature = "hw_target")]
const BOUND_SIGNAL_TEARDOWN: [RoundTrip; 6] = [
    invocation(
        "bound-irq-handler-clear",
        IRQ_HANDLER_CLEAR,
        cap_address(IRQ_BOUND_HANDLER_SLOT),
        [0; 4],
    ),
    invocation(
        "bound-irq-handler-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [IRQ_BOUND_HANDLER_SLOT, 0, 0, 0],
    ),
    invocation(
        "low-thread-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [CHAIN_TCB_SLOT, 0, 0, 0],
    ),
    invocation(
        "low-endpoint-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [STACK_TOP_TCB_SLOT, 0, 0, 0],
    ),
    invocation(
        "boot-domain-notification-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MOVE_SLOT, 0, 0, 0],
    ),
    invocation(
        "upper-notification-delete-again",
        CSPACE_DELETE,
        CNODE_CAP,
        [FRAME_SLOT, 0, 0, 0],
    ),
];

/// **WS-ZA ZA6.35: a declassified signal's bound delivery, its two-hop
/// downgrade and its refused second hop**, on the exerciser labeling's low
/// band (`qemuVirtExerciserInLowBand`): a thread carved at [`LOW_THREAD_ID`],
/// given the root task's spaces and priority, and an endpoint carved at
/// [`LOW_ENDPOINT_ID`], both in the lower trusted domain, beside a
/// notification in the boot domain (in the move slot) bound to the root task
/// and the upper-domain one (in the frame slot).  With the partner suspended
/// and the timer masked, the two threads are the core's only runnable ones,
/// so a step that blocks one restores the other.  Then:
/// - the root task's receive on the boot endpoint blocks, and the low thread's
///   declassified signal on the root task's notification delivers to it, bound
///   and blocked receiving (seL4's `sendSignal` bound arm: both hops ordinary
///   flows, no record); the low thread's yield runs the root task, whose
///   receive blocks again, and the low thread's plain signal delivers the
///   same way; once more, and the bound line's interrupt (its handler issued
///   and bound to that notification) delivers the same way, and its
///   acknowledge follows; the low thread's receive on its endpoint blocks;
/// - the upper notification bound to the low thread, and the root task's
///   declassified signal on it delivers to the low thread, the first hop the
///   downgrade from the boot domain to the upper one and the second the upper
///   domain's downgrade to the lower one (two records, the second stamped
///   with the first's words); the root task's yield runs the low thread, whose
///   receive blocks again;
/// - the notifications swapped, the boot domain's bound to the low thread, and
///   the root task's declassified signal on it is refused at its second hop
///   (`declassificationDeniedAtReceiver`: the boot domain does not flow to the
///   lower one and the policy authorizes no such downgrade), which the
///   refusal ledger records naming the receiver;
/// - the audit monitor's read of that refusal's receiver chunk (opcode 26),
///   its slot read off the ledger's status first, its word checked to be the
///   low thread's id.
///
/// The four deliveries, the refusal and the read are measured; the setup, the
/// switches and the deletes that leave the slots empty again are not.
///
/// One run (`which` names the first call); the caller masks the timer across
/// it.
#[cfg(feature = "hw_target")]
fn bound_declassified_signals(which: &str) -> bool {
    let irq_bound = KernelEntry {
        name: "irq-signal-bound",
        enter: irq_bound_line_entry,
    };
    // A capability fault to a handler waiting with no reply object: the low
    // thread names the boot endpoint as its fault handler, the root task's
    // receive on it (no reply object, message length 0) blocks it, and the
    // low thread's fault finds the handler holding no reply to link it to, so
    // it is suspended with the fault recorded (seL4's `sendFaultIPC` failing
    // into `handleDoubleFault`), the handler left waiting.  The bound line's
    // interrupt wakes the root task through its bound notification, and the
    // low thread is resumed.
    let set_low_handler = invocation(
        "low-thread-set-fault-handler",
        TCB_SET_FAULT_HANDLER,
        LOW_THREAD_CAP,
        [ENDPOINT_CAP, 0, 0, 0],
    );
    let irq_wakes_handler = KernelEntry {
        name: "irq-wakes-handler-without-reply",
        enter: irq_bound_line_entry,
    };
    let resume_low = invocation(
        "low-thread-resume-after-fault",
        TCB_RESUME,
        LOW_THREAD_CAP,
        [0; 4],
    );
    if !unmeasured_all(&BOUND_SIGNAL_SETUP, "the bound scenario's setup failed")
        || !unmeasured(
            &set_low_handler,
            "the low thread's fault handler was not set",
        )
        || !unmeasured(
            &BOUND_ROOT_RECEIVES,
            "the root task's receive did not block",
        )
        || heap_allocations_trap(&cap_fault("cap-fault-to-handler-without-reply"), which)
            != Some(true)
        || !fault_not_delivered("cap-fault-to-handler-without-reply")
        || !heap_allocations_interrupt(&irq_wakes_handler, which)
        || !unmeasured(&BOUND_IRQ_ACK, "the bound line was not acknowledged")
        || !unmeasured(&resume_low, "the low thread was not resumed")
        || !unmeasured(
            &BOUND_ROOT_RECEIVES,
            "the root task's receive did not block",
        )
        || heap_allocations_round_trip(&DECLASSIFIED_SIGNAL_BOUND, which) != Some(true)
        || !unmeasured(&LOW_THREAD_YIELDS, "the low thread's yield failed")
        || !unmeasured(
            &BOUND_ROOT_RECEIVES,
            "the root task's receive did not block",
        )
        || heap_allocations_round_trip(&SIGNAL_BOUND, which) != Some(true)
        || !unmeasured(&LOW_THREAD_YIELDS, "the low thread's yield failed")
        || !unmeasured(
            &BOUND_ROOT_RECEIVES,
            "the root task's receive did not block",
        )
        || !heap_allocations_interrupt(&irq_bound, which)
        || !unmeasured(&BOUND_IRQ_ACK, "the bound line was not acknowledged")
        || !unmeasured(
            &LOW_THREAD_RECEIVES,
            "the low thread's receive did not block",
        )
        || !unmeasured(
            &BIND_UPPER_TO_LOW_THREAD,
            "the upper notification was not bound",
        )
        || heap_allocations_round_trip(&DECLASSIFIED_SIGNAL_TWO_HOP, which) != Some(true)
        || !unmeasured(&BOUND_ROOT_YIELDS, "the root task's yield failed")
        || !unmeasured(
            &LOW_THREAD_RECEIVES,
            "the low thread's receive did not block",
        )
        || !unmeasured_all(&BOUND_SIGNAL_SWAP, "the notifications were not swapped")
        || heap_allocations_round_trip(&DECLASSIFIED_SIGNAL_REFUSED_AT_RECEIVER, which)
            != Some(true)
    {
        return false;
    }
    let Dispatched::Returned(status) = dispatch_round_trip(&BOUND_REFUSAL_STATUS).0 else {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: bound-refusal-status: the refusal ledger's status was not read"
        );
        return false;
    };
    // The status word is the next slot plus the version times the ring size:
    // the refusal just recorded is in the slot before the next.
    let slot = (status[0] % REFUSAL_RING_SIZE + REFUSAL_RING_SIZE - 1) % REFUSAL_RING_SIZE;
    let read = RoundTrip {
        name: "audit-read-refusal-receiver",
        syscall: AUDIT_READ,
        cptr: AUDIT_CAP,
        msg_len: 3,
        msg: [26, slot, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    };
    if heap_allocations_round_trip(&read, which) != Some(true) {
        return false;
    }
    match dispatch_round_trip(&read).0 {
        Dispatched::Returned(regs) if regs[0] == LOW_THREAD_ID => {}
        Dispatched::Returned(regs) => {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: audit-read-refusal-receiver: slot {slot} names {:#x}, not the low thread",
                regs[0]
            );
            return false;
        }
        _ => return false,
    }
    unmeasured_all(
        &BOUND_SIGNAL_TEARDOWN,
        "the bound scenario's slots were not emptied",
    )
}

/// **WS-ZA ZA6.29's two other branches** (added at ZA6.30): the yieldTo
/// invocation on the context bound to a schedulable partner, issued by the
/// root task with the timer masked across the whole sequence, so no tick
/// switches the two threads between steps.  The setup binds the context to
/// the suspended partner, lowers the partner one priority below the root
/// task and resumes it on core 0 (its affinity, as the TCB scenarios leave
/// it): the bind unmeasured, the priority change and the resume measured.
#[cfg(feature = "hw_target")]
const YIELD_TO_SETUP: [RoundTrip; 3] = [
    invocation(
        "yield-to-bind-partner",
        SCHED_CONTEXT_BIND,
        SCHED_CONTEXT_CAP,
        [PARTNER_TCB_CAP, 0, 0, 0],
    ),
    invocation(
        "yield-to-lower-partner",
        TCB_SET_PRIORITY,
        PARTNER_TCB_CAP,
        [PARTNER_PRIORITY - 1, 0, 0, 0],
    ),
    invocation(
        "yield-to-resume-partner",
        TCB_RESUME,
        PARTNER_TCB_CAP,
        [0; 4],
    ),
];
/// The requeue branch: the partner ranks below the caller, so it is requeued
/// at its band's head and the consumed time returns at once.
#[cfg(feature = "hw_target")]
const YIELD_TO_REQUEUE: RoundTrip = yield_to("sched-context-yield-to-requeue");
/// The partner raised to the root task's priority while it is ready and
/// queued, measured.
#[cfg(feature = "hw_target")]
const YIELD_TO_RAISE: RoundTrip = invocation(
    "yield-to-raise-partner",
    TCB_SET_PRIORITY,
    PARTNER_TCB_CAP,
    [PARTNER_PRIORITY, 0, 0, 0],
);
/// The linked branch's first half: the partner ranks with the caller on the
/// caller's core, so the yield is linked and core 0 switches to the partner.
/// The caller's frame is staged now and its consumed time is not: `x1` is the
/// caller's own spill, never the consumed-info word.
#[cfg(feature = "hw_target")]
const YIELD_TO_LINK: RoundTrip = RoundTrip {
    name: "sched-context-yield-to-linked",
    syscall: SCHED_CONTEXT_YIELD_TO,
    cptr: SCHED_CONTEXT_CAP,
    msg_len: 0,
    msg: [0; 4],
    primed: None,
    blocks: false,
    caps_or_badges: None,
    overflow: None,
    returns: None,
};
/// ...and its second: the partner, now current, blocks on the notification,
/// so core 0 switches back to the root task, whose activation completes the
/// link and writes the consumed time into its frame.
#[cfg(feature = "hw_target")]
const YIELD_TO_PARTNER_BLOCKS: RoundTrip = partner_step(
    "sched-context-yield-to-linked",
    WAIT,
    NOTIFICATION_CAP,
    0,
    [0, 0],
    true,
);
/// **The suspend of a blocked partner** (WS-ZA ZA6.33): the partner, blocked on
/// the notification wait and holding the bound context, suspended by the root
/// task.  The suspend cancels the wait (the notification's queue and the
/// partner's own links, each in its slot) and sets the partner inactive; as in
/// seL4 the context stays bound to it, so the context's unbind follows
/// ([`UNBIND_SUSPENDED_PARTNER`]) and the second run finds the state the first
/// did.
#[cfg(feature = "hw_target")]
const SUSPEND_WAITING_PARTNER: RoundTrip =
    invocation("tcb-suspend-waiting", TCB_SUSPEND, PARTNER_TCB_CAP, [0; 4]);
/// The context's unbind from the suspended partner, measured.
#[cfg(feature = "hw_target")]
const UNBIND_SUSPENDED_PARTNER: RoundTrip = invocation(
    "sched-context-unbind-waiting",
    SCHED_CONTEXT_UNBIND,
    SCHED_CONTEXT_CAP,
    [0; 4],
);
/// The link cleared: a caller with a pending yield is refused, so a second
/// yieldTo (the partner blocked, so not schedulable) succeeds only if the
/// activation cleared the root task's end of the link.  Unmeasured.
#[cfg(feature = "hw_target")]
const YIELD_TO_CLEARED: RoundTrip = yield_to("yield-to-link-cleared");

#[cfg(feature = "hw_target")]
const PARTNER_SETUP: [RoundTrip; 3] = [
    partner_step(
        "resume-partner",
        TCB_RESUME,
        PARTNER_TCB_CAP,
        0,
        [0, 0],
        false,
    ),
    partner_step(
        "mint-reply-cap",
        MINT_REPLY_CAP,
        CNODE_CAP,
        2,
        [REPLY_OBJECT_SLOT, REPLY_CAP_SLOT],
        false,
    ),
    mint(
        "mint-badged-endpoint",
        ENDPOINT_SLOT,
        MINT_SLOT,
        ENDPOINT_RIGHTS,
        ENDPOINT_BADGE,
        ROOT_IPC_BUFFER,
    ),
];
/// `ESR_EL1` of an `SVC` from AArch64 (exception class `0x15`).
#[cfg(feature = "hw_target")]
const ROUND_TRIP_ESR: u64 = 0x15 << 26;
/// `SPSR_EL1` of the frame: `EL0t` with DAIF clear, the state a thread's `SVC`
/// is taken from.  The mode is what makes the round trip a thread's syscall:
/// `trapFromEl0` admits only `M[3:0] = 0`, so an EL0 frame is saved into the
/// running thread and the core's register bank (`saveTrapFrameOnCore`) and the
/// thread is restored over the frame on the way out (`trap::restore_commit`),
/// which is the work every syscall from userspace does and an EL1 frame skips.
#[cfg(feature = "hw_target")]
const ROUND_TRIP_SPSR: u64 = 0;

/// The executing core's heap-allocation counter (`lean_heap`'s
/// `allocations_by_core`), or `None` if the heap cannot be read.  Each read
/// also samples the virtual count (`CNTVCT_EL0`, behind an `isb` so the read
/// is not taken early), so the pair of reads around a measured entry also
/// gives the counter ticks between them ([`window_ticks_since`]).
///
/// The same read takes the core's allocated bytes (`allocated_bytes_by_core`),
/// kept with the count for the last two reads ([`WINDOW_TOTALS`]), so a
/// reading over a window longer than the heap's size record still prints its
/// bytes ([`ReadingBytes`]).
#[cfg(feature = "hw_target")]
fn own_heap_allocations(core: usize) -> Option<u64> {
    let totals = crate::lean_heap::kernel_allocation_totals_on(core).ok();
    note_entered_sites(core, totals.map_or(u64::MAX, |(count, _)| count));
    crate::barriers::isb();
    let now = crate::read_sysreg!("cntvct_el0");
    WINDOW_TICKS[0].store(WINDOW_TICKS[1].load(Ordering::Relaxed), Ordering::Relaxed);
    WINDOW_TICKS[1].store(now, Ordering::Relaxed);
    let (count, bytes) = totals.unwrap_or((u64::MAX, 0));
    for (i, value) in [count, bytes].into_iter().enumerate() {
        WINDOW_TOTALS[0][i].store(
            WINDOW_TOTALS[1][i].load(Ordering::Relaxed),
            Ordering::Relaxed,
        );
        WINDOW_TOTALS[1][i].store(value, Ordering::Relaxed);
    }
    totals.map(|(count, _)| count)
}

/// The allocation count and allocated bytes at the last two heap-counter
/// reads, older first; a failed read stores the count `u64::MAX`, which no
/// reading's count equals.
#[cfg(feature = "hw_target")]
static WINDOW_TOTALS: [[AtomicU64; 2]; 2] = [
    [AtomicU64::new(u64::MAX), AtomicU64::new(0)],
    [AtomicU64::new(u64::MAX), AtomicU64::new(0)],
];

/// The bytes allocated between the last two heap-counter reads, when their
/// counts are `before` and `after`: a reading's window exactly.
#[cfg(feature = "hw_target")]
fn window_bytes(before: u64, after: u64) -> Option<u64> {
    let read = |i: usize, j: usize| WINDOW_TOTALS[i][j].load(Ordering::Relaxed);
    (read(0, 0) == before && read(1, 0) == after).then(|| read(1, 1).wrapping_sub(read(0, 1)))
}

/// The heap-counter reads [`ENTERED_SITES`] keeps per core.
#[cfg(feature = "hw_target")]
const ENTERED_SITES_KEPT: usize = 8;

/// A core's kernel-entry tally ([`crate::kernel_entry::entered_sites`]) at
/// each of its last [`ENTERED_SITES_KEPT`] heap-counter reads, beside the
/// count that read gave and its sequence number (0 for a slot never written):
/// what a reading's window entered is the difference between the read that
/// gave its `before` and its last read ([`entered_in_window`]).  Written only
/// by the boot core's driver, which reads every core's counter itself.
#[cfg(feature = "hw_target")]
static ENTERED_SITES: [[EnteredSitesRead; ENTERED_SITES_KEPT]; CORE_COUNT] =
    [const { [const { EnteredSitesRead::new() }; ENTERED_SITES_KEPT] }; CORE_COUNT];

/// The reads [`ENTERED_SITES`] has numbered, across every core.
#[cfg(feature = "hw_target")]
static ENTERED_SITES_SEQUENCE: AtomicU64 = AtomicU64::new(0);

/// One heap-counter read's slot of [`ENTERED_SITES`].
#[cfg(feature = "hw_target")]
struct EnteredSitesRead {
    sequence: AtomicU64,
    count: AtomicU64,
    tally: [core::sync::atomic::AtomicU32;
        crate::kernel_entry::entered_sites::KERNEL_ENTRY_SITE_SLOTS],
}

#[cfg(feature = "hw_target")]
impl EnteredSitesRead {
    const fn new() -> Self {
        Self {
            sequence: AtomicU64::new(0),
            count: AtomicU64::new(u64::MAX),
            tally: [const { core::sync::atomic::AtomicU32::new(0) };
                crate::kernel_entry::entered_sites::KERNEL_ENTRY_SITE_SLOTS],
        }
    }
}

/// Keep `core`'s tally at a heap-counter read that gave `count`, over the
/// oldest of its kept reads.
#[cfg(feature = "hw_target")]
fn note_entered_sites(core: usize, count: u64) {
    let Some(ring) = ENTERED_SITES.get(core) else {
        return;
    };
    let tally = crate::kernel_entry::entered_sites::snapshot(core);
    let slot = ring
        .iter()
        .min_by_key(|r| r.sequence.load(Ordering::Relaxed))
        .expect("the ring is not empty");
    for (kept, now) in slot.tally.iter().zip(tally) {
        kept.store(now, Ordering::Relaxed);
    }
    slot.count.store(count, Ordering::Relaxed);
    slot.sequence.store(
        ENTERED_SITES_SEQUENCE.fetch_add(1, Ordering::Relaxed) + 1,
        Ordering::Relaxed,
    );
}

/// The sites a reading on `core` from `before` to `after` entered: the
/// difference between `core`'s last kept read, which must have given
/// `after`, and the latest earlier read that gave `before`.  For a window
/// whose count did not move that is the read just before the last, so a
/// reading spanning several dispatches is attributed only its last one's
/// entries: the gate may be told less than a window entered, never more.
/// `None` when the kept reads do not hold the window.
#[cfg(feature = "hw_target")]
fn entered_in_window(
    core: usize,
    before: u64,
    after: u64,
) -> Option<crate::kernel_entry::entered_sites::Entered> {
    let ring = ENTERED_SITES.get(core)?;
    let mut reads: [(u64, u64, usize); ENTERED_SITES_KEPT] = [(0, 0, 0); ENTERED_SITES_KEPT];
    for (i, r) in ring.iter().enumerate() {
        reads[i] = (
            r.sequence.load(Ordering::Relaxed),
            r.count.load(Ordering::Relaxed),
            i,
        );
    }
    reads.sort_unstable_by_key(|r| core::cmp::Reverse(r.0));
    let (last_sequence, last_count, last) = reads[0];
    if last_sequence == 0 || last_count != after {
        return None;
    }
    let &(_, _, first) = reads[1..].iter().find(|r| r.0 != 0 && r.1 == before)?;
    let load = |i: usize| {
        let mut out = [0; crate::kernel_entry::entered_sites::KERNEL_ENTRY_SITE_SLOTS];
        for (o, c) in out.iter_mut().zip(&ring[i].tally) {
            *o = c.load(Ordering::Relaxed);
        }
        out
    };
    Some(crate::kernel_entry::entered_sites::Entered(
        load(first),
        load(last),
    ))
}

/// The virtual count at the last two heap-counter reads, older first.
#[cfg(feature = "hw_target")]
static WINDOW_TICKS: [AtomicU64; 2] = [AtomicU64::new(0), AtomicU64::new(0)];

/// The virtual count at the older of the last two heap-counter reads: the
/// start of the window just read.  A reading that spans several dispatches
/// takes it after the first one and measures to the last
/// ([`window_ticks_since`]).
#[cfg(feature = "hw_target")]
fn window_start() -> u64 {
    WINDOW_TICKS[0].load(Ordering::Relaxed)
}

/// The counter ticks from `start` to the last heap-counter read.  Printed
/// beside each reading, never gated: under QEMU the count follows the host's
/// clock, not the emulated cycles, so it compares two builds only as an
/// indication.
#[cfg(feature = "hw_target")]
fn window_ticks_since(start: u64) -> u64 {
    WINDOW_TICKS[1].load(Ordering::Relaxed).wrapping_sub(start)
}

/// The bytes of a reading's allocations, by size, as its line prints them:
/// `bytes=<total> sizes=<size>x<count>,…` ascending, `sizes=none` for an
/// empty window, and `sizes=unrecorded` when the heap's size record no longer
/// holds the whole window ([`crate::lean_heap::RECORDED_ALLOCATIONS`]), which
/// the host-side gate refuses.  The bytes of such a window are still printed
/// when the reading's counts are the last two heap-counter reads, from their
/// byte totals ([`window_bytes`]); `bytes=unrecorded` otherwise.
#[cfg(feature = "hw_target")]
struct ReadingBytes(Option<crate::lean_heap::AllocationSizes>, Option<u64>);

#[cfg(feature = "hw_target")]
impl core::fmt::Display for ReadingBytes {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let Some(window) = &self.0 else {
            return match self.1 {
                Some(bytes) => write!(f, "bytes={bytes} sizes=unrecorded"),
                None => f.write_str("bytes=unrecorded sizes=unrecorded"),
            };
        };
        write!(f, "bytes={} sizes=", window.bytes())?;
        let (groups, n) = window.by_size();
        if n == 0 {
            return f.write_str("none");
        }
        for (i, (size, count)) in groups[..n].iter().enumerate() {
            let sep = if i == 0 { "" } else { "," };
            write!(f, "{sep}{size}x{count}")?;
        }
        Ok(())
    }
}

/// The words the kernel routed a measured round trip by, as its frame carried
/// them (`x7` the syscall number, `x1` the message-info word): the host-side
/// gate routes them with the kernel's own router to tell which syscall arm the
/// reading measured (`scripts/exerciser_route_coverage.lean`), and the label
/// word it was answered with (`x1`), or `blocked` for a trip that blocked.
#[cfg(feature = "hw_target")]
fn print_routed(trip: &RoundTrip, core: usize, which: &str, outcome: &Dispatched) {
    let (x7, x1) = (trip.syscall, trip.msg_len);
    let name = trip.name;
    match outcome {
        Dispatched::Returned(regs) => crate::kprintln!(
            "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: routed x7={x7:#x} x1={x1:#x} answered {:#x}",
            regs[1]
        ),
        _ => crate::kprintln!(
            "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: routed x7={x7:#x} x1={x1:#x} answered blocked"
        ),
    }
}

/// The reading of one measured entry — its cells, and their bytes by size
/// beside the count (WS-UC UC1) — and the ticks of
/// its window (from `start`, [`window_start`]) on a line of its own
/// (`entry-ticks`, which the host-side gate does not read).
#[cfg(feature = "hw_target")]
fn print_reading(name: &str, core: usize, which: &str, before: u64, after: u64, start: u64) {
    let ticks = window_ticks_since(start);
    let bytes = ReadingBytes(
        crate::lean_heap::kernel_allocation_sizes_on(core, before, after)
            .ok()
            .flatten(),
        window_bytes(before, after),
    );
    crate::kprintln!(
        "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: before={before} after={after} \
         delta={} {bytes}",
        after - before
    );
    crate::kprintln!(
        "[smp-test] entry-ticks: {name}: core {core}{which}: ticks={ticks} frequency={}",
        crate::timer::read_frequency()
    );
    match entered_in_window(core, before, after) {
        Some(entered) => crate::kprintln!(
            "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: entered {entered}"
        ),
        None => crate::kprintln!(
            "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: entered unattributed"
        ),
    }
}

/// What one dispatched round trip did.
#[cfg(feature = "hw_target")]
enum Dispatched {
    /// A success frame returned to the caller.
    Returned([u64; 6]),
    /// The caller blocked and the other thread was restored.
    Blocked,
    /// Anything else (printed where it was found).
    Failed,
}

/// The context a round trip's restore resumed: the thread's `x0` to `x5` and
/// the PC it resumes at.
#[cfg(feature = "hw_target")]
#[derive(Clone, Copy)]
struct Resumed {
    regs: [u64; 6],
    pc: u64,
}

/// Issue `trip` unmeasured, failing the driver with `why` unless it did what
/// the trip says it does.
#[cfg(feature = "hw_target")]
fn unmeasured(trip: &RoundTrip, why: &str) -> bool {
    let ok = match dispatch_round_trip(trip).0 {
        Dispatched::Returned(_) => !trip.blocks,
        Dispatched::Blocked => trip.blocks,
        Dispatched::Failed => false,
    };
    if !ok {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {}: {why}",
            trip.name
        );
    }
    ok
}

/// **WS-CV CV0.1, WS-ZA ZA4.1**: the heap allocations of syscall round trips
/// through the Lean kernel, on the boot core.  For each round trip the driver
/// publishes a frame carrying the syscall as the in-flight frame, classifies
/// its syndrome and dispatches it through the syscall seam
/// (`svc_dispatch::dispatch_svc`), as the `SVC` arm does, reading this core's
/// own heap counter before and after with IRQs masked across both reads — the
/// heap is one for every core, and a tick taken in between would charge its
/// own allocations to the syscall.  The driver's own verdict is that both reads
/// happened, the counter did not go back, and the round trip did what it says
/// (returned a success frame, or blocked and restored the other thread); the
/// readings themselves are judged by the host-side gate.
///
/// Each round trip, and each partner sequence, runs twice, and both runs are
/// measured: the first is the first syscall to touch the objects the boot (or
/// the partner setup) built, the second the steady state every later syscall
/// sees.  The host-side gate (`scripts/qemu_exerciser_lib.sh`) fails on any
/// reading but zero.
#[cfg(feature = "hw_target")]
fn heap_allocations_per_syscall() -> Option<bool> {
    // The kernel-entry sites, as `build.rs` derived them from the code: the
    // host-side gate requires each production site to be entered by a
    // measured reading (the `entered` line beside each).
    for (path, line) in crate::kernel_entry::entered_sites::KERNEL_ENTRY_SITES {
        crate::kprintln!(
            "[smp-test] heap-allocations-per-syscall: kernel-entry site {path}:{line}"
        );
    }
    if !secondary_core_windows(" (first call)") {
        return Some(false);
    }
    // The mint of a badge at `2^63`, measured twice like every round trip:
    // its badge is tested as a word, so the mint builds no heap number.  The
    // slot is emptied (unmeasured) between the two runs, and the second mint
    // stays for the round trips below.
    for first in [true, false] {
        if !first {
            for step in WIDE_BADGE_TEARDOWN.iter() {
                if !unmeasured(step, "the wide-badge delete failed") {
                    return Some(false);
                }
            }
        }
        let which = if first { " (first call)" } else { "" };
        for step in WIDE_BADGE_SETUP.iter() {
            if heap_allocations_round_trip(step, which) != Some(true) {
                return Some(false);
            }
        }
    }
    for trip in ROUND_TRIPS.iter() {
        for first in [true, false] {
            if let Some(ntfn) = trip.primed {
                let priming = RoundTrip {
                    cptr: ntfn,
                    ..signal(trip.name)
                };
                if !unmeasured(&priming, "the priming signal failed") {
                    return Some(false);
                }
            }
            let which = if first { " (first call)" } else { "" };
            if heap_allocations_round_trip(trip, which) != Some(true) {
                return Some(false);
            }
        }
    }
    for step in WIDE_BADGE_TEARDOWN.iter() {
        if !unmeasured(step, "the wide-badge delete failed") {
            return Some(false);
        }
    }
    for step in PARTNER_SETUP.iter() {
        if !unmeasured(step, "the partner setup failed") {
            return Some(false);
        }
    }
    for scenario in PARTNER_SCENARIOS.iter() {
        for first in [true, false] {
            let which = if first { " (first call)" } else { "" };
            for step in scenario.iter() {
                if heap_allocations_round_trip(step, which) != Some(true) {
                    return Some(false);
                }
            }
        }
    }
    // WS-ZA ZA6.32: the interrupt entry's branches, the partner runnable, the
    // two lines raised above every other line's priority.
    crate::gic::set_interrupt_line_priority(IRQ_BOUND_LINE, IRQ_EXERCISER_PRIORITY);
    crate::gic::set_interrupt_line_priority(IRQ_UNBOUND_LINE, IRQ_EXERCISER_PRIORITY);
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        if !interrupt_handlers_issued(which)
            || !interrupt_entries(which)
            || !interrupt_binding_revoked(which)
            || !interrupt_notification_finalised(which)
            || !interrupt_handlers_retired(which)
        {
            return Some(false);
        }
    }
    // WS-ZA ZA5.13: the declassification scenario, the partner runnable.
    for first in [true, false] {
        if !unmeasured(
            &UPPER_NOTIFICATION_CARVE,
            "the upper-domain notification was not carved",
        ) {
            return Some(false);
        }
        let which = if first { " (first call)" } else { "" };
        for step in DECLASSIFICATION_SCENARIO.iter() {
            if heap_allocations_round_trip(step, which) != Some(true) {
                return Some(false);
            }
        }
        if heap_allocations_round_trip(&DECLASSIFICATION_REFUSAL, which) != Some(true) {
            return Some(false);
        }
        if heap_allocations_round_trip(&DECLASSIFICATION_LOOKUP_REFUSAL, which) != Some(true) {
            return Some(false);
        }
        for step in AUDIT_SCENARIO.iter() {
            if heap_allocations_round_trip(step, which) != Some(true) {
                return Some(false);
            }
        }
    }
    // The partner goes back to `.Inactive`: suspended from its own core's queue
    // when the root task is current, or suspending itself when it is.
    let suspend = partner_step(
        "suspend-partner",
        TCB_SUSPEND,
        PARTNER_TCB_CAP,
        0,
        [0, 0],
        false,
    );
    if let Dispatched::Failed = dispatch_round_trip(&suspend).0 {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: suspend-partner: the partner was not suspended"
        );
        return Some(false);
    }
    // WS-ZA ZA6.35: the declassified signal's bound delivery, its two-hop
    // downgrade and its refused second hop, the partner suspended and the
    // timer masked across each run; then the boot audit capability deleted so
    // its slot is the copy's again.
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        let saved = crate::interrupts::disable_interrupts();
        let ok = bound_declassified_signals(which);
        crate::interrupts::restore_interrupts(saved);
        if !ok {
            return Some(false);
        }
    }
    let delete_audit = invocation(
        "delete-audit-capability",
        CSPACE_DELETE,
        CNODE_CAP,
        [AUDIT_SLOT, 0, 0, 0],
    );
    if !unmeasured(&delete_audit, "the boot audit capability was not deleted") {
        return Some(false);
    }
    // The mint slot is the invocation scenarios' own again.
    let delete_badged = invocation(
        "delete-badged-endpoint",
        CSPACE_DELETE,
        CNODE_CAP,
        [MINT_SLOT, 0, 0, 0],
    );
    if !unmeasured(
        &delete_badged,
        "the badged endpoint capability was not deleted",
    ) {
        return Some(false);
    }
    // The busy reply's final delete, run twice as the root task: the partner
    // resumed (unmeasured) each time, and inactive again after the delete;
    // then the stashed reply's, the partner resumed and suspended around it.
    for first in [true, false] {
        if !unmeasured(&PARTNER_SETUP[0], "the partner was not resumed") {
            return Some(false);
        }
        let which = if first { " (first call)" } else { "" };
        for step in BUSY_REPLY_SCENARIO.iter() {
            if heap_allocations_round_trip(step, which) != Some(true) {
                return Some(false);
            }
        }
        // The stashed reply's final delete: the partner resumed again, and
        // suspending itself after its send leaves the root task current.
        if !unmeasured(&PARTNER_SETUP[0], "the partner was not resumed") {
            return Some(false);
        }
        for step in STASHED_REPLY_SCENARIO.iter() {
            if heap_allocations_round_trip(step, which) != Some(true) {
                return Some(false);
            }
        }
        if let Dispatched::Failed = dispatch_round_trip(&suspend).0 {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: suspend-partner: the partner was not suspended"
            );
            return Some(false);
        }
    }
    for scenario in INVOCATION_SCENARIOS.iter() {
        for first in [true, false] {
            let which = if first { " (first call)" } else { "" };
            let mut masked = None;
            let mut held = None;
            for step in scenario.iter() {
                let ok = match step.syscall {
                    HOLD_SECOND_CORE_STEP => {
                        held = hold_core(1);
                        if held.is_none() {
                            crate::kprintln!(
                                "[smp-test] FAIL: heap-allocations-per-syscall: {}: core 1 was not held",
                                step.name
                            );
                        }
                        held.is_some()
                    }
                    RELEASE_SECOND_CORE_STEP => match held.take() {
                        Some(sequence) => {
                            let released = release_core(1, sequence);
                            if !released {
                                crate::kprintln!(
                                    "[smp-test] FAIL: heap-allocations-per-syscall: {}: core 1 did not report its release",
                                    step.name
                                );
                            }
                            released
                        }
                        None => false,
                    },
                    MASK_TICKS_STEP => {
                        masked = Some(crate::interrupts::disable_interrupts());
                        true
                    }
                    RECEIVE_PATH_STEP => {
                        let words = [step.msg[0], step.msg[1], step.msg[2]];
                        let written = write_buffer_words(step.cptr, RECEIVE_PATH_WORD, &words);
                        if !written {
                            crate::kprintln!(
                                "[smp-test] FAIL: heap-allocations-per-syscall: {}: the receive path was not written",
                                step.name
                            );
                        }
                        written
                    }
                    UNMASK_TICKS_STEP => {
                        if let Some(saved) = masked.take() {
                            crate::interrupts::restore_interrupts(saved);
                        }
                        true
                    }
                    TIMER_TICK_STEP => {
                        let entry = KernelEntry {
                            name: step.name,
                            enter: crate::timer::per_core_timer_tick_isr,
                        };
                        heap_allocations_kernel_entry(&entry, which) == Some(true)
                    }
                    _ => heap_allocations_round_trip(step, which) == Some(true),
                };
                if !ok {
                    if let Some(sequence) = held.take() {
                        let _released = release_core(1, sequence);
                    }
                    if let Some(saved) = masked.take() {
                        crate::interrupts::restore_interrupts(saved);
                    }
                    return Some(false);
                }
            }
        }
    }
    // WS-UC UC4: a carved CNode's cells, every one returned by its retire.
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        if carved_cnode_retire(which) != Some(true) {
            return Some(false);
        }
    }
    // WS-ZA ZA6.33: the affinity change of a thread running on core 1, the
    // timer masked across the whole section.
    let saved = crate::interrupts::disable_interrupts();
    let ok = affinity_move_running();
    crate::interrupts::restore_interrupts(saved);
    if ok != Some(true) {
        return Some(false);
    }
    // The final delete of a running thread: by itself on core 0, and by the
    // root task while it runs on core 1, each run set up afresh, the timer
    // masked across each.
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        for remote in [false, true] {
            let saved = crate::interrupts::disable_interrupts();
            let ok = running_thread_delete(remote, which);
            crate::interrupts::restore_interrupts(saved);
            if ok != Some(true) {
                return Some(false);
            }
        }
    }
    // The entries a remote core's work reaches: a shootdown with a remote
    // target, a syscall on a core another core vacated, an FP/SIMD access
    // whose values another core holds; each run set up afresh, the timer
    // masked across each.
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        let saved = crate::interrupts::disable_interrupts();
        let ok = remote_core_entries(which);
        crate::interrupts::restore_interrupts(saved);
        if ok != Some(true) {
            return Some(false);
        }
    }
    // WS-ZA ZA6.29's requeue and linked branches (added at ZA6.30), twice,
    // the timer masked across each run.
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        let saved = crate::interrupts::disable_interrupts();
        let ok = yield_to_branches(which);
        crate::interrupts::restore_interrupts(saved);
        if ok != Some(true) {
            return Some(false);
        }
    }
    // WS-ZA ZA6.1: the kernel entries that are not syscalls, each entered as
    // its trap handler enters it, twice.
    for entry in KERNEL_ENTRIES.iter() {
        for first in [true, false] {
            let which = if first { " (first call)" } else { "" };
            if heap_allocations_kernel_entry(entry, which) != Some(true) {
                return Some(false);
            }
        }
    }
    // The fault entries, each entered through the synchronous-exception
    // handler, the timer masked across the whole section.
    let saved = crate::interrupts::disable_interrupts();
    let ok = fault_entries();
    crate::interrupts::restore_interrupts(saved);
    if ok != Some(true) {
        return ok;
    }
    if !secondary_core_windows("") {
        return Some(false);
    }
    // The retype the kernel heap cannot hold, twice, last: its confirming
    // carve and delete run unmeasured and touch nothing a later reading sees.
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        if !heap_refused_retype(which) {
            return Some(false);
        }
    }
    Some(true)
}

/// The ticks a secondary's tick window waits for.
#[cfg(feature = "hw_target")]
const SECONDARY_WINDOW_TICKS: u64 = 3;

/// **The kernel entries of cores 1 to 3 once they are up**: on each
/// secondary, that core's own slot of the heap counter read across a window in
/// which it takes [`SECONDARY_WINDOW_TICKS`] timer ticks (`lean_per_core_timer_tick`
/// on its idle thread), and across one `.reschedule` SGI the boot core sends it
/// (`lean_per_core_reschedule`).  Nothing else enters the kernel on an idle
/// secondary, so each window holds those entries alone; the host-side gate
/// holds each to 0, at the driver's start (`which` the first call) and at its
/// end (the steady state).
#[cfg(feature = "hw_target")]
fn secondary_core_windows(which: &str) -> bool {
    for core in 1..CORE_COUNT {
        let ticks = crate::per_cpu_stats::timer_tick_count_for(core);
        let Some(before) = own_heap_allocations(core) else {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: secondary-ticks: core {core}: the heap counter could not be read"
            );
            return false;
        };
        let start = window_start();
        let ticked = wait_until(|| {
            crate::per_cpu_stats::timer_tick_count_for(core) >= ticks + SECONDARY_WINDOW_TICKS
        });
        let Some(after) = own_heap_allocations(core) else {
            return false;
        };
        if !ticked || after < before {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: secondary-ticks: core {core}: \
                 no {SECONDARY_WINDOW_TICKS} ticks, or the counter went back ({before} -> {after})"
            );
            return false;
        }
        crate::kprintln!(
            "[smp-test] heap-allocations-per-syscall: secondary-ticks: core {core}{which}: took {} ticks",
            crate::per_cpu_stats::timer_tick_count_for(core) - ticks
        );
        print_reading("secondary-ticks", core, which, before, after, start);
        let sgis = crate::per_cpu_stats::sgi_count_for(core);
        let Some(before) = own_heap_allocations(core) else {
            return false;
        };
        let start = window_start();
        crate::gic::send_sgi(1u8 << core, crate::trap::RESCHEDULE_INTID);
        let taken = wait_until(|| crate::per_cpu_stats::sgi_count_for(core) > sgis);
        // The count moves as the handler is entered: a millisecond more for
        // the reschedule entry to finish.
        let settle = crate::timer::read_counter()
            .saturating_add(u64::from(crate::timer::read_frequency()) / 1000);
        while crate::timer::read_counter() < settle {
            core::hint::spin_loop();
        }
        let Some(after) = own_heap_allocations(core) else {
            return false;
        };
        if !taken || after < before {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: secondary-reschedule: core {core}: \
                 the SGI was not taken, or the counter went back ({before} -> {after})"
            );
            return false;
        }
        crate::kprintln!(
            "[smp-test] heap-allocations-per-syscall: secondary-reschedule: core {core}{which}: took the SGI"
        );
        print_reading("secondary-reschedule", core, which, before, after, start);
    }
    true
}

/// `KernelError.untypedRegionExhausted`'s discriminant (`sele4n-types`'
/// `UntypedRegionExhausted`): the refusal of a carve the kernel heap cannot
/// hold, as seL4's `seL4_NotEnoughMemory`.
#[cfg(feature = "hw_target")]
const UNTYPED_REGION_EXHAUSTED: u64 = 20;

/// The free bytes the kernel is told while the heap refusal is measured: one
/// page, below what any carve asks (`retypeHeapReserveBytes` alone is 64 KiB),
/// so the heap is never filled to reach the refusal.
#[cfg(feature = "hw_target")]
const HEAP_REFUSED_CEILING: u64 = 4096;

/// An endpoint carve into the frame slot, the passive endpoint's id.
#[cfg(feature = "hw_target")]
const HEAP_RETYPE_MSG: [u64; 4] = [ENDPOINT_TYPE, PASSIVE_CHILD_IDS[0], CNODE_CAP, FRAME_SLOT];

/// That carve, with the heap's capacity capped below it: refused with
/// `untypedRegionExhausted` before any write, so it allocates nothing.
#[cfg(feature = "hw_target")]
const HEAP_REFUSED_RETYPE: RoundTrip = RoundTrip {
    name: "untyped-retype-heap-refused",
    syscall: UNTYPED_RETYPE,
    cptr: UNTYPED_CAP,
    msg_len: 4,
    msg: HEAP_RETYPE_MSG,
    primed: None,
    blocks: false,
    caps_or_badges: None,
    overflow: None,
    // seL4's `seL4_NotEnoughMemory`: MR0 the memory left, the kernel heap's
    // free bytes the refusal read.
    returns: refused_with(
        UNTYPED_REGION_EXHAUSTED,
        1,
        [Some(HEAP_REFUSED_CEILING), None, None, None],
    ),
};

/// **The kernel heap's refusal of a retype**: the free bytes the kernel is
/// told capped at [`HEAP_REFUSED_CEILING`] (`lean_heap`'s exerciser hook), the
/// carve measured and refused with `untypedRegionExhausted`, the cap lifted;
/// then the same carve, unmeasured, succeeds on the heap's own free bytes and
/// its capability is deleted, which retires the endpoint — so the refusal was
/// the heap's, not some other check's, and the state is as it was.
#[cfg(feature = "hw_target")]
fn heap_refused_retype(which: &str) -> bool {
    crate::lean_heap::set_reported_free_bytes_ceiling(Some(HEAP_REFUSED_CEILING));
    let refused = heap_allocations_round_trip(&HEAP_REFUSED_RETYPE, which) == Some(true);
    crate::lean_heap::set_reported_free_bytes_ceiling(None);
    refused
        && unmeasured(
            &invocation(
                "untyped-retype-heap-admitted",
                UNTYPED_RETYPE,
                UNTYPED_CAP,
                HEAP_RETYPE_MSG,
            ),
            "the carve the heap refused did not succeed on the heap's own capacity",
        )
        && unmeasured(
            &invocation(
                "heap-admitted-endpoint-delete",
                CSPACE_DELETE,
                CNODE_CAP,
                [FRAME_SLOT, 0, 0, 0],
            ),
            "the admitted carve's endpoint was not deleted",
        )
}

/// **WS-ZA ZA6.32**: the shared peripheral interrupts the exerciser raises —
/// one with a handler bound to it (its handler is the interrupt notification
/// in [`NOTIFICATION_SLOT`]) and one with none.  `virt` wires neither to a device.
#[cfg(feature = "hw_target")]
const IRQ_BOUND_LINE: u32 = 250;
#[cfg(feature = "hw_target")]
const IRQ_UNBOUND_LINE: u32 = 251;
/// The INTID the interrupt entry's spurious branch is entered with: the GIC's
/// "no interrupt pending" acknowledge, which no handler capability names.
#[cfg(feature = "hw_target")]
const IRQ_SPURIOUS_INTID: u32 = 1023;
/// The priority the exerciser's lines are raised at: above the `0xA0` every
/// other line is programmed at (`init_distributor`), so the acknowledge after
/// the set-pending names the raised line and not a pending tick or SGI.
#[cfg(feature = "hw_target")]
const IRQ_EXERCISER_PRIORITY: u8 = 0x80;

/// Whether the last [`raise_and_take`] acknowledged the line it raised.
#[cfg(feature = "hw_target")]
static IRQ_LINE_TAKEN: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(false);

/// **WS-ZA ZA6.32: a device interrupt taken as `handle_irq_per_core` takes
/// it**: the line set pending at the distributor (`GICD_ISPENDR`), then
/// acknowledged and its end of interrupt written by `dispatch_irq_with_iar`,
/// and the acknowledged line entered through the trap's device seam
/// (`trap::device_interrupt`, the verified `lean_handle_interrupt`).  Anything
/// else acknowledged is routed as the trap routes it and recorded as a miss.
#[cfg(feature = "hw_target")]
fn raise_and_take(core: u64, line: u32) {
    IRQ_LINE_TAKEN.store(false, Ordering::SeqCst);
    crate::gic::set_interrupt_line_pending(line);
    let _ = crate::gic::dispatch_irq_with_iar(|intid, source_cpu| {
        if intid == line {
            IRQ_LINE_TAKEN.store(true, Ordering::SeqCst);
            crate::trap::device_interrupt(intid);
        } else if intid == crate::gic::TIMER_PPI_ID {
            crate::timer::per_core_timer_tick_isr(core);
        } else if intid < u32::from(crate::gic::MAX_SGI_INTID) {
            #[allow(clippy::cast_possible_truncation)]
            crate::gic::dispatch_sgi(intid as u8, source_cpu);
        } else {
            crate::trap::device_interrupt(intid);
        }
    });
}

/// The bound line taken: its notification signalled, the line masked.
#[cfg(feature = "hw_target")]
fn irq_bound_line_entry(core: u64) {
    raise_and_take(core, IRQ_BOUND_LINE);
}

/// The unbound line taken: the line masked.
#[cfg(feature = "hw_target")]
fn irq_unbound_line_entry(core: u64) {
    raise_and_take(core, IRQ_UNBOUND_LINE);
}

/// The interrupt entry with the spurious INTID: it names no device line, so the
/// entry delivers and masks nothing (seL4's `handleSpuriousIRQ`), and only the
/// save, the settle and the activation run.
#[cfg(feature = "hw_target")]
fn irq_spurious_entry(_core: u64) {
    IRQ_LINE_TAKEN.store(true, Ordering::SeqCst);
    crate::trap::device_interrupt(IRQ_SPURIOUS_INTID);
}

/// The acknowledge of a line's handler capability (`seL4_IRQHandler_Ack`): it
/// must succeed and returns nothing.
#[cfg(feature = "hw_target")]
const fn irq_handler_ack(name: &'static str, slot: u64) -> RoundTrip {
    RoundTrip {
        name,
        syscall: IRQ_HANDLER_ACK,
        cptr: cap_address(slot),
        msg_len: 0,
        msg: [0; 4],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    }
}

/// One measured interrupt entry: the entry, then the check that it took the
/// line it raised.
#[cfg(feature = "hw_target")]
fn heap_allocations_interrupt(entry: &KernelEntry, which: &str) -> bool {
    if heap_allocations_kernel_entry(entry, which) != Some(true) {
        return false;
    }
    if !IRQ_LINE_TAKEN.load(Ordering::SeqCst) {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {}: the raised line was not the one acknowledged",
            entry.name
        );
        return false;
    }
    true
}

/// **WS-ZA ZA6.32: the handlers issued and bound**, each measured: the bound
/// line's handler issued from the interrupt control into
/// [`IRQ_BOUND_HANDLER_SLOT`] (`seL4_IRQControl_Get`, the line put at
/// `IRQSignal`), the unbound line's into [`IRQ_UNBOUND_HANDLER_SLOT`], and the
/// interrupt notification bound to the first (`seL4_IRQHandler_SetNotification`).
#[cfg(feature = "hw_target")]
fn interrupt_handlers_issued(which: &str) -> bool {
    let get_bound = invocation(
        "irq-control-get",
        IRQ_CONTROL_GET,
        IRQ_CONTROL_CAP,
        [
            u64::from(IRQ_BOUND_LINE),
            CNODE_CAP,
            IRQ_BOUND_HANDLER_SLOT,
            0,
        ],
    );
    let get_unbound = invocation(
        "irq-control-get-unbound",
        IRQ_CONTROL_GET,
        IRQ_CONTROL_CAP,
        [
            u64::from(IRQ_UNBOUND_LINE),
            CNODE_CAP,
            IRQ_UNBOUND_HANDLER_SLOT,
            0,
        ],
    );
    let bind = invocation(
        "irq-handler-set-notification",
        IRQ_HANDLER_SET_NOTIFICATION,
        cap_address(IRQ_BOUND_HANDLER_SLOT),
        [NOTIFICATION_CAP, 0, 0, 0],
    );
    // Each one word shorter than its arguments, on the capability it reads
    // them under: refused `TruncatedMessage` once the capability is found.
    let get_short = truncated("irq-control-get-short", IRQ_CONTROL_GET, IRQ_CONTROL_CAP, 2);
    let bind_short = truncated(
        "irq-handler-set-notification-short",
        IRQ_HANDLER_SET_NOTIFICATION,
        cap_address(IRQ_BOUND_HANDLER_SLOT),
        0,
    );
    heap_allocations_round_trip(&get_short, which) == Some(true)
        && heap_allocations_round_trip(&get_bound, which) == Some(true)
        && heap_allocations_round_trip(&get_unbound, which) == Some(true)
        && heap_allocations_round_trip(&bind_short, which) == Some(true)
        && heap_allocations_round_trip(&bind, which) == Some(true)
}

/// **WS-ZA ZA6.32: a revoke ends the binding**, each step measured: the
/// interrupt notification's slot revoked (`seL4_CNode_Revoke`), which deletes
/// its derivation children, the copy in the bound line's node among them, so
/// the line is bound to nothing; then the bound line raised, which the entry
/// now takes as an unbound line and masks.  That the line signalled nothing is
/// checked unmeasured: its acknowledge, then a wait on the notification that
/// must block (no badge is pending) and the signal that wakes it.  The
/// notification is bound to the line again, unmeasured, so the clear after
/// empties a bound node slot as on the first pass.
#[cfg(feature = "hw_target")]
fn interrupt_binding_revoked(which: &str) -> bool {
    let revoke = invocation(
        "irq-notification-revoke",
        CSPACE_REVOKE,
        CNODE_CAP,
        [NOTIFICATION_SLOT, 0, 0, 0],
    );
    let revoked_line = KernelEntry {
        name: "irq-revoked-line",
        enter: irq_bound_line_entry,
    };
    let block = partner_step(
        "irq-revoked-wait-blocks",
        WAIT,
        NOTIFICATION_CAP,
        0,
        [0, 0],
        true,
    );
    let wake = partner_step(
        "irq-revoked-signal",
        SIGNAL,
        NOTIFICATION_CAP,
        1,
        [1, 0],
        false,
    );
    let rebind = invocation(
        "irq-handler-set-notification-again",
        IRQ_HANDLER_SET_NOTIFICATION,
        cap_address(IRQ_BOUND_HANDLER_SLOT),
        [NOTIFICATION_CAP, 0, 0, 0],
    );
    heap_allocations_round_trip(&revoke, which) == Some(true)
        && heap_allocations_interrupt(&revoked_line, which)
        && unmeasured(
            &irq_handler_ack("irq-revoked-ack", IRQ_BOUND_HANDLER_SLOT),
            "the revoked line was not acknowledged",
        )
        && unmeasured(&block, "the revoked line signalled the notification")
        && unmeasured(&wake, "the waiter on the notification was not woken")
        && heap_allocations_round_trip(&rebind, which) == Some(true)
}

/// **A handler's node holding the last capability to its notification**, each
/// step measured, on the unbound line's handler: a notification carved, bound
/// to the line (the node holds a copy), its own capability deleted, so the
/// node's copy is the last; the boot notification bound over it, which deletes
/// the node's capability first (seL4's `cteDeleteOne`), finalising and
/// retiring the carved notification, then copies; a second carved
/// notification bound over that copy, its capability deleted, and the handler
/// cleared, whose delete of the node's capability is again final.  The node
/// is empty after, as before.
#[cfg(feature = "hw_target")]
fn interrupt_notification_finalised(which: &str) -> bool {
    let handler = cap_address(IRQ_UNBOUND_HANDLER_SLOT);
    let steps = [
        invocation(
            "untyped-retype-irq-notification",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                NOTIFICATION_TYPE,
                FINALISED_CHILD_IDS[1],
                CNODE_CAP,
                FRAME_SLOT,
            ],
        ),
        invocation(
            "irq-handler-set-carved-notification",
            IRQ_HANDLER_SET_NOTIFICATION,
            handler,
            [FRAME_CAP, 0, 0, 0],
        ),
        invocation(
            "irq-notification-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        invocation(
            "irq-handler-set-notification-over-last",
            IRQ_HANDLER_SET_NOTIFICATION,
            handler,
            [NOTIFICATION_CAP, 0, 0, 0],
        ),
        invocation(
            "untyped-retype-irq-cleared-notification",
            UNTYPED_RETYPE,
            UNTYPED_CAP,
            [
                NOTIFICATION_TYPE,
                FINALISED_CHILD_IDS[1],
                CNODE_CAP,
                FRAME_SLOT,
            ],
        ),
        invocation(
            "irq-handler-set-notification-over-copy",
            IRQ_HANDLER_SET_NOTIFICATION,
            handler,
            [FRAME_CAP, 0, 0, 0],
        ),
        invocation(
            "irq-cleared-notification-cap-delete",
            CSPACE_DELETE,
            CNODE_CAP,
            [FRAME_SLOT, 0, 0, 0],
        ),
        invocation("irq-handler-clear-last", IRQ_HANDLER_CLEAR, handler, [0; 4]),
    ];
    steps
        .iter()
        .all(|step| heap_allocations_round_trip(step, which) == Some(true))
}

/// **WS-ZA ZA6.32: the handlers cleared and deleted**, each measured: the bound
/// handler's notification cleared (`seL4_IRQHandler_Clear`), then each
/// handler's only capability deleted, whose finalisation retires its line to
/// `IRQInactive` (`deletingIRQHandler`, `deletedIRQHandler`), so the next pass
/// issues both again.
#[cfg(feature = "hw_target")]
fn interrupt_handlers_retired(which: &str) -> bool {
    let clear = invocation(
        "irq-handler-clear",
        IRQ_HANDLER_CLEAR,
        cap_address(IRQ_BOUND_HANDLER_SLOT),
        [0; 4],
    );
    let delete_bound = invocation(
        "irq-handler-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [IRQ_BOUND_HANDLER_SLOT, 0, 0, 0],
    );
    let delete_unbound = invocation(
        "irq-handler-delete-unbound",
        CSPACE_DELETE,
        CNODE_CAP,
        [IRQ_UNBOUND_HANDLER_SLOT, 0, 0, 0],
    );
    heap_allocations_round_trip(&clear, which) == Some(true)
        && heap_allocations_round_trip(&delete_bound, which) == Some(true)
        && unmeasured(
            &delete_unbound,
            "the unbound line's handler was not deleted",
        )
}

/// **WS-ZA ZA6.32: the interrupt entry's branches**, each measured: the bound
/// line's signal to a notification with no waiter (the badge accumulates) and
/// the handler's acknowledge; the signal to a thread waiting on it (a wait
/// blocks first, the other thread restored) and its acknowledge, unmeasured;
/// the unbound line, masked, and its acknowledge, unmeasured; and the spurious
/// INTID.  Each acknowledge leaves its line unmasked again and the wait after
/// the first signal consumes its badge, so the steady-state pass starts where
/// the first did.
#[cfg(feature = "hw_target")]
fn interrupt_entries(which: &str) -> bool {
    let no_waiter = KernelEntry {
        name: "irq-signal-no-waiter",
        enter: irq_bound_line_entry,
    };
    let waiter = KernelEntry {
        name: "irq-signal-waiter",
        enter: irq_bound_line_entry,
    };
    let unbound = KernelEntry {
        name: "irq-unbound",
        enter: irq_unbound_line_entry,
    };
    let spurious = KernelEntry {
        name: "irq-spurious",
        enter: irq_spurious_entry,
    };
    let consume = RoundTrip {
        name: "irq-wait-pending",
        syscall: WAIT,
        cptr: NOTIFICATION_CAP,
        msg_len: 1,
        msg: [0; 4],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: None,
    };
    let block = partner_step("irq-wait-blocks", WAIT, NOTIFICATION_CAP, 0, [0, 0], true);
    heap_allocations_interrupt(&no_waiter, which)
        && heap_allocations_round_trip(
            &irq_handler_ack("irq-handler-ack", IRQ_BOUND_HANDLER_SLOT),
            which,
        ) == Some(true)
        && unmeasured(&consume, "the interrupt's badge was not received")
        && unmeasured(&block, "the wait did not block")
        && heap_allocations_interrupt(&waiter, which)
        && unmeasured(
            &irq_handler_ack("irq-handler-ack-after-wake", IRQ_BOUND_HANDLER_SLOT),
            "the bound line was not acknowledged",
        )
        && heap_allocations_interrupt(&unbound, which)
        && heap_allocations_round_trip(
            &irq_handler_ack("irq-unbound-ack", IRQ_UNBOUND_HANDLER_SLOT),
            which,
        ) == Some(true)
        && heap_allocations_interrupt(&spurious, which)
}

/// **WS-ZA ZA6.1**: a kernel entry the allocation exerciser drives that is not
/// a syscall: its name and the handler that enters it.
#[cfg(feature = "hw_target")]
struct KernelEntry {
    name: &'static str,
    enter: fn(u64),
}

/// The timer tick as `handle_irq_per_core`'s timer branch takes it
/// (`timer::per_core_timer_tick_isr`), and the `.reschedule` SGI as its
/// handler takes it (`trap::reschedule_sgi_handler`).
#[cfg(feature = "hw_target")]
const KERNEL_ENTRIES: [KernelEntry; 2] = [
    KernelEntry {
        name: "timer-tick",
        enter: crate::timer::per_core_timer_tick_isr,
    },
    KernelEntry {
        name: "reschedule-sgi",
        enter: crate::trap::reschedule_sgi_entry,
    },
];

/// One measured entry of `heap_allocations_per_syscall`: an EL0 frame
/// published as the in-flight frame, the entry taken with IRQs masked, and
/// this core's heap counter read before and after.  The entry must restore a
/// thread over the frame, as it does on the way back to user.
#[cfg(feature = "hw_target")]
fn heap_allocations_kernel_entry(entry: &KernelEntry, which: &str) -> Option<bool> {
    let core = crate::per_cpu::current_core_id_from_tpidr();
    let name = entry.name;
    let mut frame = crate::trap::TrapFrame {
        gprs: [0; 31],
        sp_el0: 0,
        elr_el1: 0,
        spsr_el1: ROUND_TRIP_SPSR,
        esr_el1: 0,
        far_el1: 0,
        tpidr_el0: 0,
        reserved: 0,
    };
    let saved_daif = crate::interrupts::disable_interrupts();
    let before = own_heap_allocations(core as usize);
    let restored = {
        let _in_flight = crate::trap::InFlightFrame::publish(&mut frame);
        (entry.enter)(core);
        crate::trap::take_restored()
    };
    let after = own_heap_allocations(core as usize);
    crate::interrupts::restore_interrupts(saved_daif);
    crate::user_translation::install_translation(crate::user_translation::Translation::Kernel);
    crate::fp_context::set_trap_for_resume(false);
    let (Some(before), Some(after)) = (before, after) else {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the heap counter could not be read"
        );
        return Some(false);
    };
    if !restored {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: resumed no thread"
        );
        return Some(false);
    }
    crate::kprintln!(
        "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: entered, a thread restored"
    );
    if after < before {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the counter went back ({before} -> {after})"
        );
        return Some(false);
    }
    print_reading(name, core as usize, which, before, after, window_start());
    Some(true)
}

/// A trap the fault scenarios take through the synchronous-exception handler
/// (`trap::handle_synchronous_exception`), as an EL0 thread raises it: the
/// syndrome and fault-address words, the PC it trapped at, and `x0`, `x1` and
/// `x7` (the capability address, the message info and the syscall number of
/// an `SVC`), with `x2` the first message register (a receive's reply
/// capability address).
#[cfg(feature = "hw_target")]
struct TrapTrip {
    name: &'static str,
    esr: u64,
    far: u64,
    elr: u64,
    x0: u64,
    x1: u64,
    x2: u64,
    x7: u64,
}

/// The PC a fault scenario's thread traps at: an EL0 address of the user
/// window, which nothing maps (the trap is synthesised, never executed).
#[cfg(feature = "hw_target")]
const FAULT_PC: u64 = (1 << 39) + 0x40;
/// `ESR_EL1.IL`: a 32-bit instruction.
#[cfg(feature = "hw_target")]
const ESR_IL: u64 = 1 << 25;
/// A translation fault at level 3, the abort's status code.
#[cfg(feature = "hw_target")]
const ESR_TRANSLATION_FAULT_L3: u64 = 0x07;

/// A data abort from EL0 at a kernel address: a word `≥ 2^63`, so a fault
/// address carried as a number would box.
#[cfg(feature = "hw_target")]
const fn data_abort(name: &'static str) -> TrapTrip {
    TrapTrip {
        name,
        esr: (0x24 << 26) | ESR_IL | ESR_TRANSLATION_FAULT_L3,
        far: 0xffff_0000_dead_0000,
        elr: FAULT_PC,
        x0: 0,
        x1: 0,
        x2: 0,
        x7: 0,
    }
}

/// An instruction abort from EL0 at its own PC.
#[cfg(feature = "hw_target")]
const fn instruction_abort(name: &'static str) -> TrapTrip {
    TrapTrip {
        name,
        esr: (0x20 << 26) | ESR_IL | ESR_TRANSLATION_FAULT_L3,
        far: FAULT_PC,
        elr: FAULT_PC,
        x0: 0,
        x1: 0,
        x2: 0,
        x7: 0,
    }
}

/// A PC alignment fault (`userException`).
#[cfg(feature = "hw_target")]
const fn pc_alignment(name: &'static str) -> TrapTrip {
    TrapTrip {
        name,
        esr: (0x22 << 26) | ESR_IL,
        far: FAULT_PC + 2,
        elr: FAULT_PC + 2,
        x0: 0,
        x1: 0,
        x2: 0,
        x7: 0,
    }
}

/// An `SVC` whose `x7` names no syscall: a word `≥ 2^63`, which no `u32`
/// narrows, delivered as seL4's `UnknownSyscall` with the full word.
#[cfg(feature = "hw_target")]
const UNKNOWN_SYSCALL_NUMBER: u64 = 0x8000_0000_0000_0005;
#[cfg(feature = "hw_target")]
const fn unknown_syscall(name: &'static str) -> TrapTrip {
    TrapTrip {
        name,
        esr: ROUND_TRIP_ESR,
        far: 0,
        elr: FAULT_PC + 4,
        x0: 0,
        x1: 0,
        x2: 0,
        x7: UNKNOWN_SYSCALL_NUMBER,
    }
}

/// An empty slot of the root CNode: its capability address is `2^63 + 31`.
#[cfg(feature = "hw_target")]
const EMPTY_SLOT: u64 = 31;
/// A send through the empty slot's address: the lookup finds no capability,
/// which seL4 raises as a capability fault carrying the address.
#[cfg(feature = "hw_target")]
const fn cap_fault(name: &'static str) -> TrapTrip {
    TrapTrip {
        name,
        esr: ROUND_TRIP_ESR,
        far: 0,
        elr: FAULT_PC + 4,
        x0: cap_address(EMPTY_SLOT),
        x1: 0,
        x2: 0,
        x7: SEND,
    }
}

/// An FP/SIMD access from EL0 with the core's trap armed.
#[cfg(feature = "hw_target")]
const fn fp_access(name: &'static str) -> TrapTrip {
    TrapTrip {
        name,
        esr: (0x07 << 26) | ESR_IL,
        far: 0,
        elr: FAULT_PC,
        x0: 0,
        x1: 0,
        x2: 0,
        x7: 0,
    }
}

/// The slot the two threads' fault handler names: empty while the
/// fail-closed scenarios run, a copy of the exerciser endpoint's capability
/// while the delivered ones do.  Slot 20 holds the interrupt-control
/// capability (`IRQ_CONTROL_SLOT`), so the handler takes the next free slot.
#[cfg(feature = "hw_target")]
const FAULT_HANDLER_SLOT: u64 = 21;
#[cfg(feature = "hw_target")]
const FAULT_HANDLER_CAP: u64 = cap_address(FAULT_HANDLER_SLOT);
/// `x1` of the frame a VM fault reaches its handler with: the VM-fault tag
/// (`seL4_Fault_VMFault`, 6, the MCS layout's) as the label and its four
/// words as the length.
#[cfg(feature = "hw_target")]
const VM_FAULT_MESSAGE_INFO: u64 = (6 << 12) | 4;

/// The five faults each fault scenario raises: a data abort and an
/// instruction abort (seL4's `handleVMFaultEvent`), a capability fault at an
/// address `≥ 2^63` (`handleInvocation`'s lookup failure), an unknown syscall
/// (`handleUnknownSyscall`) and a user exception (`handleUserLevelFault`).
#[cfg(feature = "hw_target")]
const FAULT_KINDS: [&str; 5] = [
    "vm-fault-data",
    "vm-fault-instruction",
    "cap-fault",
    "unknown-syscall",
    "user-exception",
];

/// The trap of fault kind `kind` (an entry of [`FAULT_KINDS`]), named `name`.
#[cfg(feature = "hw_target")]
const fn fault_trip(kind: usize, name: &'static str) -> TrapTrip {
    match kind {
        0 => data_abort(name),
        1 => instruction_abort(name),
        2 => cap_fault(name),
        3 => unknown_syscall(name),
        _ => pc_alignment(name),
    }
}

/// Each kind's scenario names: with no handler, the resume of the thread that
/// suspended, delivered to a handler waiting on the endpoint, and that
/// handler's reply.
#[cfg(feature = "hw_target")]
const FAULT_SUSPENDS: [&str; 5] = [
    "vm-fault-data-suspends",
    "vm-fault-instruction-suspends",
    "cap-fault-suspends",
    "unknown-syscall-suspends",
    "user-exception-suspends",
];
#[cfg(feature = "hw_target")]
const FAULT_RESUMES: [&str; 5] = [
    "vm-fault-data-resume",
    "vm-fault-instruction-resume",
    "cap-fault-resume",
    "unknown-syscall-resume",
    "user-exception-resume",
];
#[cfg(feature = "hw_target")]
const FAULT_DELIVERED: [&str; 5] = [
    "vm-fault-data-delivered",
    "vm-fault-instruction-delivered",
    "cap-fault-delivered",
    "unknown-syscall-delivered",
    "user-exception-delivered",
];
#[cfg(feature = "hw_target")]
const FAULT_REPLIES: [&str; 5] = [
    "vm-fault-data-reply",
    "vm-fault-instruction-reply",
    "cap-fault-reply",
    "unknown-syscall-reply",
    "user-exception-reply",
];

/// A syscall the register file routes past the operand dispatch, through the
/// empty slot: the root task's `x7`, `x1` and `x0` as an `SVC` traps with them.
#[cfg(feature = "hw_target")]
const fn overflow_cap_fault(name: &'static str, syscall: u64, length: u64) -> TrapTrip {
    TrapTrip {
        x1: length,
        x2: 0,
        x7: syscall,
        ..cap_fault(name)
    }
}

/// The `x1` a capability fault reaches its receiver with: `seL4_Fault_CapFault`
/// (1) as the label and the words `setMR` wrote as the length.  An empty
/// slot's fault is seL4's five `seL4_CapFault_*` words (`IP`, `Addr`,
/// `InRecvPhase`, `LookupFailureType`, `BitsLeft` of `seL4_MissingCapability`);
/// the fifth lands in the receiving partner's IPC buffer, the window's page
/// (`tcb-set-ipc-buffer`), so while that page is mapped the length is five.
#[cfg(feature = "hw_target")]
const CAP_FAULT_MESSAGE_INFO: u64 = (1 << 12) | 5;

/// The same fault while the partner's buffer page is unmapped: the fifth word
/// has nowhere to go, so the length is the four message registers (seL4's
/// `setMR` with no buffer answers `n_msgRegisters`).
#[cfg(feature = "hw_target")]
const CAP_FAULT_UNMAPPED_BUFFER_INFO: u64 = (1 << 12) | 4;

/// One overflow capability fault queued and answered: the partner resumed,
/// the root task's trap queued on its handler's endpoint, the partner's
/// receive taking the fault and its reply restarting the root task, the
/// partner suspended again.
#[cfg(feature = "hw_target")]
fn queued_overflow_cap_fault(
    trap: &TrapTrip,
    receive: &'static str,
    reply: &'static str,
    info: u64,
    which: &str,
) -> bool {
    let receive = RoundTrip {
        name: receive,
        syscall: RECEIVE,
        cptr: ENDPOINT_CAP,
        msg_len: 1,
        msg: [REPLY_CAP, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: Some((info, [None; 4])),
    };
    let reply = partner_step(reply, REPLY, REPLY_CAP, 0, [0, 0], false);
    unmeasured(&PARTNER_SETUP[0], "the partner was not resumed")
        && heap_allocations_trap(trap, which) == Some(true)
        && heap_allocations_round_trip(&receive, which) == Some(true)
        && heap_allocations_round_trip(&reply, which) == Some(true)
        && suspend_partner()
}

/// **The refusals the entry turns into capability faults, and the IPC
/// buffer's TLB fill either side of them** (seL4's `handleInvocation`: a
/// failed lookup of the invoked capability raises a capability fault).  The
/// configure, the service register (each one word past the registers, read
/// from the root task's IPC buffer: the `.overflowOne` route) and a long send
/// each name the empty slot, so the operand's lookup fails inside the routed
/// arm and the entry's refusal seam reads it as the fault
/// (`syscallCapFaultOf`, delivered by `deliverSyscallCapFault`); with the
/// partner runnable and not waiting, each is queued on the handler's endpoint.
/// The buffer's page is unmapped and mapped again first, so its translation is
/// on no core's TLB (between the two, the messages past the inline words are
/// clamped to them, as seL4 clamps a message with no IPC buffer): the first configure refused for its arguments and the
/// first fault take the arm that fills the entry and takes the fill back
/// (`tlbFillIpcBufferOnCore`, `tlbUndoFillOnCore`); the configure that then
/// succeeds fills it and keeps it; the second fault and refusal and the
/// configure after them find it held.
#[cfg(feature = "hw_target")]
fn overflow_cap_faults(map_buffer_page: &RoundTrip, which: &str) -> bool {
    let unmap_buffer_page = invocation(
        "fault-long-unmap-buffer",
        VSPACE_UNMAP,
        VSPACE_CAP,
        [ROOT_ASID, FRAME_VADDR, 0, 0],
    );
    let refused_args = [
        SCHED_CONTEXT_CAP,
        SCHED_CONTEXT_PERIOD + 1,
        SCHED_CONTEXT_PERIOD,
        PARTNER_PRIORITY,
    ];
    let admitted_args = [
        SCHED_CONTEXT_CAP,
        SCHED_CONTEXT_BUDGET,
        SCHED_CONTEXT_PERIOD,
        PARTNER_PRIORITY,
    ];
    // A budget above its period is seL4-MCS's `seL4_RangeError` with
    // `MIN_BUDGET` and the period (`decodeSchedControl_ConfigureFlags`): the
    // payload carries the period the caller passed, a word read at the entry.
    let budget_over_period = refused_with(
        RANGE_ERROR,
        2,
        [
            Some(CONFIGURE_MIN_BUDGET),
            Some(SCHED_CONTEXT_PERIOD),
            None,
            None,
        ],
    );
    let refused_fills = RoundTrip {
        returns: budget_over_period,
        ..configure("configure-refused-fills", refused_args)
    };
    let refused_held = RoundTrip {
        returns: budget_over_period,
        ..configure("configure-refused-held", refused_args)
    };
    // seL4-MCS's bounds (`decodeSchedControl_ConfigureFlags`): a budget or
    // period below `MIN_BUDGET` or above `MAX_PERIOD` answers `MIN_BUDGET` and
    // `MAX_PERIOD`.  A budget of zero; a budget of `2^64 - 1` over a period
    // past `2^63`; a budget and a period both past `2^63`; and a deadline past
    // `2^63`, the fifth word, read from the buffer (`invalidArgument 4`).
    // Each argument word past `2^63` is tested as a word, so none is made a
    // heap number.
    let max_period_refusal = refused_with(
        RANGE_ERROR,
        2,
        [
            Some(CONFIGURE_MIN_BUDGET),
            Some(CONFIGURE_MAX_PERIOD),
            None,
            None,
        ],
    );
    let zero_budget = RoundTrip {
        returns: max_period_refusal,
        ..configure(
            "configure-zero-budget-max-period",
            [SCHED_CONTEXT_CAP, 0, SCHED_CONTEXT_PERIOD, PARTNER_PRIORITY],
        )
    };
    let wide_period = RoundTrip {
        returns: max_period_refusal,
        ..configure(
            "configure-budget-over-wide-period",
            [SCHED_CONTEXT_CAP, u64::MAX, WIDE_PERIOD, PARTNER_PRIORITY],
        )
    };
    let wide_budget_and_period = RoundTrip {
        returns: max_period_refusal,
        ..configure(
            "configure-wide-budget-and-period",
            [
                SCHED_CONTEXT_CAP,
                WIDE_PERIOD,
                WIDE_PERIOD,
                PARTNER_PRIORITY,
            ],
        )
    };
    let wide_deadline = RoundTrip {
        returns: refused_with(INVALID_ARGUMENT, 1, [Some(4), None, None, None]),
        overflow: Some((FRAME_VADDR, WIDE_WORD)),
        ..configure("configure-wide-deadline", admitted_args)
    };
    let fills = configure("configure-fills-ipc-buffer", admitted_args);
    let held = configure("configure-held-ipc-buffer", admitted_args);
    // With the buffer's page unmapped, a message past the inline words is
    // clamped to them (seL4's `handleInvocation`: `length > n_msgRegisters &&
    // !buffer` gives `n_msgRegisters`): the configure, one word past and two
    // words past, is then short of its fifth argument and refused
    // `TruncatedMessage` once its capability is found; the long send and the
    // long call on the empty slot run as the short ones and fault on the
    // lookup; and a long receive reads no overflow word at all, so it faults
    // on the CNode capability as the short receive does.
    let clamped_one_word = RoundTrip {
        returns: refused(TRUNCATED_MESSAGE),
        ..configure("configure-one-word-unmapped-buffer", admitted_args)
    };
    let clamped_long = RoundTrip {
        msg_len: 6,
        returns: refused(TRUNCATED_MESSAGE),
        ..configure("configure-long-unmapped-buffer", admitted_args)
    };
    unmeasured(&unmap_buffer_page, "the buffer's page was not unmapped")
        && heap_allocations_round_trip(&clamped_one_word, which) == Some(true)
        && heap_allocations_round_trip(&clamped_long, which) == Some(true)
        && queued_overflow_cap_fault(
            &overflow_cap_fault(
                "long-send-unmapped-buffer-cap-fault",
                SEND,
                LONG_SEND_LENGTH,
            ),
            "receive-long-send-unmapped-buffer-cap-fault",
            "reply-long-send-unmapped-buffer-cap-fault",
            CAP_FAULT_UNMAPPED_BUFFER_INFO,
            which,
        )
        && queued_overflow_cap_fault(
            &overflow_cap_fault(
                "long-call-unmapped-buffer-cap-fault",
                CALL,
                LONG_SEND_LENGTH,
            ),
            "receive-long-call-unmapped-buffer-cap-fault",
            "reply-long-call-unmapped-buffer-cap-fault",
            CAP_FAULT_UNMAPPED_BUFFER_INFO,
            which,
        )
        && queued_overflow_cap_fault(
            &TrapTrip {
                x0: CNODE_CAP,
                ..overflow_cap_fault("long-receive-unmapped-buffer-cap-fault", RECEIVE, 5)
            },
            "receive-long-receive-unmapped-buffer-cap-fault",
            "reply-long-receive-unmapped-buffer-cap-fault",
            CAP_FAULT_UNMAPPED_BUFFER_INFO,
            which,
        )
        && unmeasured(map_buffer_page, "the buffer's page was not mapped again")
        && heap_allocations_round_trip(&refused_fills, which) == Some(true)
        && queued_overflow_cap_fault(
            &overflow_cap_fault("configure-cap-fault-fills", SCHED_CONTEXT_CONFIGURE, 5),
            "receive-configure-cap-fault",
            "reply-configure-cap-fault",
            CAP_FAULT_MESSAGE_INFO,
            which,
        )
        && heap_allocations_round_trip(&fills, which) == Some(true)
        && queued_overflow_cap_fault(
            &overflow_cap_fault("configure-cap-fault-held", SCHED_CONTEXT_CONFIGURE, 5),
            "receive-configure-cap-fault-held",
            "reply-configure-cap-fault-held",
            CAP_FAULT_MESSAGE_INFO,
            which,
        )
        && heap_allocations_round_trip(&refused_held, which) == Some(true)
        && heap_allocations_round_trip(&zero_budget, which) == Some(true)
        && heap_allocations_round_trip(&wide_period, which) == Some(true)
        && heap_allocations_round_trip(&wide_budget_and_period, which) == Some(true)
        && heap_allocations_round_trip(&wide_deadline, which) == Some(true)
        && heap_allocations_round_trip(&held, which) == Some(true)
        && queued_overflow_cap_fault(
            &overflow_cap_fault("service-register-cap-fault", SERVICE_REGISTER, 5),
            "receive-service-register-cap-fault",
            "reply-service-register-cap-fault",
            CAP_FAULT_MESSAGE_INFO,
            which,
        )
        && queued_overflow_cap_fault(
            &overflow_cap_fault("long-send-cap-fault", SEND, LONG_SEND_LENGTH),
            "receive-long-send-cap-fault",
            "reply-long-send-cap-fault",
            CAP_FAULT_MESSAGE_INFO,
            which,
        )
        // A receive past its inline words on the CNode capability: seL4's
        // `handleRecv` faults on a capability that is not an endpoint or
        // notification, in the receive phase, as on a failed lookup.
        && queued_overflow_cap_fault(
            &TrapTrip {
                x0: CNODE_CAP,
                ..overflow_cap_fault("overflowed-receive-cap-fault", RECEIVE, 5)
            },
            "receive-overflowed-receive-cap-fault",
            "reply-overflowed-receive-cap-fault",
            CAP_FAULT_MESSAGE_INFO,
            which,
        )
        && receive_phase_cap_faults(which)
}

/// A receive-phase trap: the root task's `SVC` with `x7` the syscall, `x0`
/// the capability it receives on and no message words.
#[cfg(feature = "hw_target")]
const fn receive_phase_cap_fault(name: &'static str, syscall: u64, cptr: u64) -> TrapTrip {
    TrapTrip {
        x0: cptr,
        x1: 0,
        x2: 0,
        x7: syscall,
        ..cap_fault(name)
    }
}

/// The slot the write-only endpoint capability takes for the receive-phase
/// fault without the right: the empty slot, filled for that one fault and
/// emptied after (the no-grant slot holds the fault handler's endpoint here,
/// `FAULT_HANDLER_SLOT`).
#[cfg(feature = "hw_target")]
const RECEIVE_NO_RIGHT_SLOT: u64 = EMPTY_SLOT;

/// **The receive phase's capability faults** (seL4's `handleRecv`): a
/// receive, a wait and a reply-receive whose capability resolves but is not an
/// endpoint or notification, and a receive on an endpoint capability without
/// the right to receive, each raise a capability fault in the receive phase
/// exactly as a failed lookup does, queued on the handler's endpoint and
/// answered.  The capability without the right is an endpoint capability
/// minted with the write right alone, deleted after.
#[cfg(feature = "hw_target")]
fn receive_phase_cap_faults(which: &str) -> bool {
    let mint_no_receive = mint(
        "receive-no-right-mint",
        ENDPOINT_SLOT,
        RECEIVE_NO_RIGHT_SLOT,
        WRITE_ONLY_RIGHTS,
        0,
        FRAME_VADDR,
    );
    let delete_no_receive = invocation(
        "receive-no-right-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [RECEIVE_NO_RIGHT_SLOT, 0, 0, 0],
    );
    queued_overflow_cap_fault(
        &receive_phase_cap_fault("receive-wrong-type-cap-fault", RECEIVE, CNODE_CAP),
        "receive-receive-wrong-type-cap-fault",
        "reply-receive-wrong-type-cap-fault",
        CAP_FAULT_MESSAGE_INFO,
        which,
    ) && queued_overflow_cap_fault(
        &receive_phase_cap_fault("wait-wrong-type-cap-fault", WAIT, CNODE_CAP),
        "receive-wait-wrong-type-cap-fault",
        "reply-wait-wrong-type-cap-fault",
        CAP_FAULT_MESSAGE_INFO,
        which,
    ) && queued_overflow_cap_fault(
        &receive_phase_cap_fault("reply-recv-wrong-type-cap-fault", REPLY_RECV, CNODE_CAP),
        "receive-reply-recv-wrong-type-cap-fault",
        "reply-reply-recv-wrong-type-cap-fault",
        CAP_FAULT_MESSAGE_INFO,
        which,
    ) && heap_allocations_round_trip(&mint_no_receive, which) == Some(true)
        && queued_overflow_cap_fault(
            &receive_phase_cap_fault(
                "receive-no-right-cap-fault",
                RECEIVE,
                cap_address(RECEIVE_NO_RIGHT_SLOT),
            ),
            "receive-receive-no-right-cap-fault",
            "reply-receive-no-right-cap-fault",
            CAP_FAULT_MESSAGE_INFO,
            which,
        )
        && heap_allocations_round_trip(&delete_no_receive, which) == Some(true)
}

/// Each kind's queued scenario: the trap raised while no handler waits, the
/// partner's receive that takes it, and its reply (the data abort's are the
/// boot pins `vm-fault-queued`, `receive-queued-fault`, `reply-queued-fault`).
#[cfg(feature = "hw_target")]
const FAULT_QUEUED: [&str; 5] = [
    "vm-fault-queued",
    "vm-fault-instruction-queued",
    "cap-fault-queued",
    "unknown-syscall-queued",
    "user-exception-queued",
];
#[cfg(feature = "hw_target")]
const FAULT_QUEUED_RECEIVES: [&str; 5] = [
    "receive-queued-fault",
    "receive-queued-instruction-fault",
    "receive-queued-cap-fault",
    "receive-queued-unknown-syscall",
    "receive-queued-user-exception",
];
#[cfg(feature = "hw_target")]
const FAULT_QUEUED_REPLIES: [&str; 5] = [
    "reply-queued-fault",
    "reply-queued-instruction-fault",
    "reply-queued-cap-fault",
    "reply-queued-unknown-syscall",
    "reply-queued-user-exception",
];
/// The `x1` each queued kind reaches the receiver with: the kind's
/// `seL4_Fault_tag` as the label (VM 6, capability 1, unknown syscall 2, user
/// exception 3) and the four words of the frame as the length.
#[cfg(feature = "hw_target")]
const FAULT_QUEUED_INFO: [u64; 5] = [
    VM_FAULT_MESSAGE_INFO,
    VM_FAULT_MESSAGE_INFO,
    (1 << 12) | 4,
    (2 << 12) | 4,
    (3 << 12) | 4,
];

/// The word a fault handler's answer supplies as its first reply word: the
/// restart PC of a user exception and the restart `x0` of an unknown syscall
/// (seL4's `handleFaultReply`).  An EL0 address, so no restart frame of either
/// kind could read it by accident.
#[cfg(feature = "hw_target")]
const FAULT_REPLY_WORD: u64 = FAULT_PC + 0x100;

/// What a faulted thread restarts with once its handler answers with label 0
/// and the one reply word [`FAULT_REPLY_WORD`]: its PC, `x0` and `x1`.
#[cfg(feature = "hw_target")]
#[derive(Clone, Copy)]
struct FaultRestart {
    pc: u64,
    x0: u64,
    x1: u64,
}

/// The restart of fault kind `kind`: a VM or capability fault resumes its own
/// context whatever the reply says; an unknown syscall takes the reply's first
/// word as `x0`; a user exception takes it as its PC.  The PC a restart keeps
/// is the fault IP the model recorded, seL4's `FaultIP`: a VM fault's is the
/// faulting instruction (the abort's `ELR_EL1`), and a fault an `SVC` raised
/// (the capability fault and the unknown syscall) records the `SVC` itself,
/// one instruction before the `ELR_EL1` its trap saved (`svcFaultIP`, as seL4's
/// `lel_syscall` stores `ELR - 4`).  A reply that leaves the PC alone
/// therefore re-issues the syscall; these replies carry no PC word.
#[cfg(feature = "hw_target")]
const fn fault_restart(kind: usize) -> FaultRestart {
    let trip = fault_trip(kind, "");
    let restart_pc = if kind == 2 || kind == 3 {
        trip.elr - 4
    } else {
        trip.elr
    };
    match kind {
        3 => FaultRestart {
            pc: restart_pc,
            x0: FAULT_REPLY_WORD,
            x1: trip.x1,
        },
        4 => FaultRestart {
            pc: FAULT_REPLY_WORD,
            x0: trip.x0,
            x1: trip.x1,
        },
        _ => FaultRestart {
            pc: restart_pc,
            x0: trip.x0,
            x1: trip.x1,
        },
    }
}

/// Whether the thread a fault answer restored resumed as its restart says,
/// printing why not.
#[cfg(feature = "hw_target")]
fn restarted_as(name: &str, resumed: &Resumed, expected: FaultRestart) -> bool {
    let ok = resumed.pc == expected.pc
        && resumed.regs[0] == expected.x0
        && resumed.regs[1] == expected.x1;
    if !ok {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the faulted thread resumed at \
             pc={:#x} x0={:#x} x1={:#x}, its restart is pc={:#x} x0={:#x} x1={:#x}",
            resumed.pc,
            resumed.regs[0],
            resumed.regs[1],
            expected.pc,
            expected.x0,
            expected.x1
        );
    }
    ok
}

/// Each kind's scenario names when the handler answers with `Reply`: the
/// fault delivered to the waiting handler, and its reply.
#[cfg(feature = "hw_target")]
const FAULT_DELIVERED_TO_REPLY: [&str; 5] = [
    "vm-fault-data-delivered-to-reply",
    "vm-fault-instruction-delivered-to-reply",
    "cap-fault-delivered-to-reply",
    "unknown-syscall-delivered-to-reply",
    "user-exception-delivered-to-reply",
];
#[cfg(feature = "hw_target")]
const FAULT_PLAIN_REPLIES: [&str; 5] = [
    "vm-fault-data-plain-reply",
    "vm-fault-instruction-plain-reply",
    "cap-fault-plain-reply",
    "unknown-syscall-plain-reply",
    "user-exception-plain-reply",
];

/// One measured trap: the frame published as an EL0 thread's, the
/// synchronous-exception handler entered with IRQs masked, and this core's
/// heap counter read before and after.  The handler returns only through a
/// context the kernel restored (it halts the core otherwise).
/// Whether the thread a capability-fault trap restored is its handler,
/// woken holding the fault: its `x1` carries `seL4_Fault_CapFault`'s tag (1).
#[cfg(feature = "hw_target")]
fn restored_cap_fault() -> bool {
    TRAP_RESTORED_X1.load(Ordering::SeqCst) >> 12 == 1
}

/// The trap named `name` delivered its capability fault to the handler.
#[cfg(feature = "hw_target")]
fn fault_delivered(name: &str) -> bool {
    if !restored_cap_fault() {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the handler was not woken with the fault (x1={:#x})",
            TRAP_RESTORED_X1.load(Ordering::SeqCst)
        );
        return false;
    }
    true
}

/// The trap named `name` did not deliver its capability fault: the handler
/// was left waiting.
#[cfg(feature = "hw_target")]
fn fault_not_delivered(name: &str) -> bool {
    if restored_cap_fault() {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the handler was woken with the fault"
        );
        return false;
    }
    true
}

#[cfg(feature = "hw_target")]
fn heap_allocations_trap(trip: &TrapTrip, which: &str) -> Option<bool> {
    let core = crate::per_cpu::current_core_id_from_tpidr();
    let name = trip.name;
    let mut frame = crate::trap::TrapFrame {
        gprs: [0; 31],
        sp_el0: 0,
        elr_el1: trip.elr,
        spsr_el1: ROUND_TRIP_SPSR,
        esr_el1: trip.esr,
        far_el1: trip.far,
        tpidr_el0: 0,
        reserved: 0,
    };
    frame.gprs[0] = trip.x0;
    frame.gprs[1] = trip.x1;
    frame.gprs[2] = trip.x2;
    frame.gprs[7] = trip.x7;
    let saved_daif = crate::interrupts::disable_interrupts();
    let before = own_heap_allocations(core as usize);
    let loads = crate::fp_context::load_commits_on(core as usize);
    crate::trap::handle_synchronous_exception(&mut frame);
    // Whether the entry loaded an FP/SIMD context (an access answered
    // `.load`); a `.retry` loads none.
    TRAP_LOADED_FP.store(
        crate::fp_context::load_commits_on(core as usize) != loads,
        Ordering::SeqCst,
    );
    let after = own_heap_allocations(core as usize);
    TRAP_RESTORED_X1.store(frame.gprs[1], Ordering::SeqCst);
    TRAP_RESTORED_X3.store(frame.gprs[3], Ordering::SeqCst);
    TRAP_RESTORED_X4.store(frame.gprs[4], Ordering::SeqCst);
    TRAP_RESTORED_X5.store(frame.gprs[5], Ordering::SeqCst);
    crate::interrupts::restore_interrupts(saved_daif);
    crate::user_translation::install_translation(crate::user_translation::Translation::Kernel);
    crate::fp_context::set_trap_for_resume(false);
    let (Some(before), Some(after)) = (before, after) else {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the heap counter could not be read"
        );
        return Some(false);
    };
    crate::kprintln!(
        "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: entered, a thread restored"
    );
    // A syscall trap is routed by the kernel's router as a round trip is:
    // its words go to the route coverage, the trapping thread answered by
    // no return (a capability fault blocks it on its handler).
    if trip.esr == ROUND_TRIP_ESR {
        crate::kprintln!(
            "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: routed x7={:#x} x1={:#x} answered blocked",
            trip.x7,
            trip.x1
        );
    }
    if after < before {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the counter went back ({before} -> {after})"
        );
        return Some(false);
    }
    print_reading(name, core as usize, which, before, after, window_start());
    Some(true)
}

/// `x1` and `x3`–`x5` of the context the last [`heap_allocations_trap`]'s
/// entry restored: a delivered fault's message info and its second to fourth
/// message words (a capability fault's `Addr`, `InRecvPhase` and
/// `LookupFailureType`).
#[cfg(feature = "hw_target")]
static TRAP_RESTORED_X1: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);
#[cfg(feature = "hw_target")]
static TRAP_RESTORED_X3: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);
#[cfg(feature = "hw_target")]
static TRAP_RESTORED_X4: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);
#[cfg(feature = "hw_target")]
static TRAP_RESTORED_X5: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);

/// The `x1` a guard-mismatch capability fault reaches a handler with an IPC
/// buffer: `seL4_Fault_CapFault` (1) and its seven words.
#[cfg(feature = "hw_target")]
const CAP_FAULT_GUARD_MISMATCH_INFO: u64 = (1 << 12) | 7;

/// Whether the last [`heap_allocations_trap`]'s entry loaded an FP/SIMD
/// context: an access answered `.load`, where one answered `.retry` loads
/// none.
#[cfg(feature = "hw_target")]
static TRAP_LOADED_FP: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(false);

/// The partner suspended, unmeasured, which leaves the root task current:
/// by the root task, or by the partner itself when a step left it current
/// (a resumed or restarted thread of its priority may be switched to).
#[cfg(feature = "hw_target")]
fn suspend_partner() -> bool {
    let suspend = partner_step(
        "suspend-partner",
        TCB_SUSPEND,
        PARTNER_TCB_CAP,
        0,
        [0, 0],
        false,
    );
    if let Dispatched::Failed = dispatch_round_trip(&suspend).0 {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: suspend-partner: the partner was not suspended"
        );
        return false;
    }
    true
}

/// A receive-side capability fault the partner raises (seL4-MCS
/// `handleRecv`): the trap, the address the fault names and its
/// `LookupFailureType`, and the message info the handler receives.
#[cfg(feature = "hw_target")]
struct ReceiveFault {
    trip: TrapTrip,
    addr: u64,
    lookup_type: u64,
    info: u64,
}

/// A receive trap of the partner: syscall `x7` on capability `x0`, its message
/// info `x1` and first message register `x2`.
#[cfg(feature = "hw_target")]
const fn receive_trap(name: &'static str, x7: u64, x0: u64, x1: u64, x2: u64) -> TrapTrip {
    TrapTrip {
        name,
        esr: ROUND_TRIP_ESR,
        far: 0,
        elr: FAULT_PC + 4,
        x0,
        x1,
        x2,
        x7,
    }
}

/// **The receive side's capability faults** (seL4-MCS `handleRecv`,
/// `lookupReply`): a receive and a reply-receive whose reply capability's
/// address misses the root CNode's guard, each fault carrying the reply
/// capability's address and the guard-mismatch words; a receive and a
/// reply-receive whose reply capability's slot holds another kind of
/// capability, `MissingCapability`; and a wait on a notification bound to
/// another thread (the root task), `MissingCapability` at the notification's
/// address.  Each is delivered to the handler in the receive phase, answered,
/// and restarts the partner's context.
#[cfg(feature = "hw_target")]
fn receive_side_faults(
    handler_waits: &RoundTrip,
    handler_waits_again: &RoundTrip,
    wake_handler: &RoundTrip,
) -> bool {
    let faults = [
        ReceiveFault {
            trip: receive_trap(
                "receive-reply-cap-guard-mismatch",
                RECEIVE,
                ENDPOINT_CAP,
                1,
                REPLY_CAP_SLOT,
            ),
            addr: REPLY_CAP_SLOT,
            lookup_type: 4,
            info: CAP_FAULT_GUARD_MISMATCH_INFO,
        },
        ReceiveFault {
            trip: receive_trap(
                "reply-recv-reply-cap-guard-mismatch",
                REPLY_RECV,
                ENDPOINT_CAP,
                2,
                REPLY_CAP_SLOT,
            ),
            addr: REPLY_CAP_SLOT,
            lookup_type: 4,
            info: CAP_FAULT_GUARD_MISMATCH_INFO,
        },
        ReceiveFault {
            trip: receive_trap(
                "receive-reply-cap-wrong-kind",
                RECEIVE,
                ENDPOINT_CAP,
                1,
                CNODE_CAP,
            ),
            addr: CNODE_CAP,
            lookup_type: 2,
            info: CAP_FAULT_MESSAGE_INFO,
        },
        ReceiveFault {
            trip: receive_trap(
                "reply-recv-reply-cap-wrong-kind",
                REPLY_RECV,
                ENDPOINT_CAP,
                1,
                CNODE_CAP,
            ),
            addr: CNODE_CAP,
            lookup_type: 2,
            info: CAP_FAULT_MESSAGE_INFO,
        },
        ReceiveFault {
            trip: receive_trap(
                "wait-notification-bound-elsewhere",
                WAIT,
                NOTIFICATION_CAP,
                0,
                0,
            ),
            addr: NOTIFICATION_CAP,
            lookup_type: 2,
            info: CAP_FAULT_MESSAGE_INFO,
        },
    ];
    let bind_root = invocation(
        "bind-root-notification",
        TCB_BIND_NOTIFICATION,
        ROOT_TCB_CAP,
        [NOTIFICATION_CAP, 0, 0, 0],
    );
    let unbind_root = invocation(
        "unbind-root-notification",
        TCB_UNBIND_NOTIFICATION,
        ROOT_TCB_CAP,
        [0; 4],
    );
    let reply = partner_step(
        "receive-side-fault-reply",
        REPLY,
        REPLY_CAP,
        1,
        [FAULT_REPLY_WORD, 0],
        false,
    );
    for (index, fault) in faults.iter().enumerate() {
        let name = fault.trip.name;
        let bound = fault.trip.x7 == WAIT;
        if bound && !unmeasured(&bind_root, "the root task's notification was not bound") {
            return false;
        }
        for first in [true, false] {
            let which = if first { " (first call)" } else { "" };
            if !unmeasured(&PARTNER_SETUP[0], "the partner was not resumed")
                || !unmeasured(handler_waits, "the handler did not wait on the endpoint")
                || heap_allocations_trap(&fault.trip, which) != Some(true)
            {
                return false;
            }
            let info = TRAP_RESTORED_X1.load(Ordering::SeqCst);
            let addr = TRAP_RESTORED_X3.load(Ordering::SeqCst);
            let in_recv = TRAP_RESTORED_X4.load(Ordering::SeqCst);
            let lookup_type = TRAP_RESTORED_X5.load(Ordering::SeqCst);
            if info != fault.info
                || addr != fault.addr
                || in_recv != 1
                || lookup_type != fault.lookup_type
            {
                crate::kprintln!(
                    "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the handler received x1={:#x} x3={:#x} x4={:#x} x5={:#x}",
                    info,
                    addr,
                    in_recv,
                    lookup_type
                );
                return false;
            }
            if fault.info == CAP_FAULT_GUARD_MISMATCH_INFO
                && !write_buffer_words(FRAME_VADDR, OVERFLOW_BASE_WORD, &[0, 0, 0])
            {
                return false;
            }
            // The handler's reply is one scenario, measured after the first
            // fault and run unmeasured after the others.
            let replied = if index == 0 {
                heap_allocations_round_trip(&reply, which) == Some(true)
            } else {
                unmeasured(&reply, "the handler's reply did not return")
            };
            if !replied {
                return false;
            }
            let (waited, _, _, resumed) = dispatch_round_trip(handler_waits_again);
            if !matches!(waited, Dispatched::Blocked) {
                crate::kprintln!(
                    "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the handler did not wait again"
                );
                return false;
            }
            // A capability fault resumes its own context: the receive it
            // trapped with, re-issued from its `SVC`.
            let restart = FaultRestart {
                pc: fault.trip.elr - 4,
                x0: fault.trip.x0,
                x1: fault.trip.x1,
            };
            if !restarted_as(name, &resumed, restart)
                || !unmeasured(wake_handler, "the waiting handler was not woken")
                || !suspend_partner()
            {
                return false;
            }
        }
        if bound && !unmeasured(&unbind_root, "the root task's notification was not unbound") {
            return false;
        }
    }
    true
}

/// **The fault entries** (seL4's `handleFault` from each of its producers:
/// `handleVMFaultEvent`, `handleUserLevelFault`, `handleUnknownSyscall` and the
/// capability fault a syscall's lookup raises), and the FP/SIMD access trap,
/// each scenario run twice, at first call and at steady state:
/// - with no handler (its capability's slot empty), each fault suspends the
///   root task fail-closed; the partner, which then runs, resumes it
///   (measured: the resume answers the fault the thread carries, restarting
///   it at the faulting instruction), and the root task,
///   chosen over the partner whenever both are runnable, suspends the partner;
/// - a VM fault raised while the handler is not waiting queues the root task
///   on the endpoint, and the partner's receive takes the fault message and its
///   reply restarts the thread;
/// - with the root task waiting on the endpoint as the handler, each fault the
///   partner raises is delivered to it at once, and its reply-receive restarts
///   the partner and waits again;
/// - an FP/SIMD access loads the root task's context; its receive blocks it
///   and the switch to the partner releases the core's registers into the root
///   task's saved context; the partner's access loads its own, and its send
///   wakes the root task, which takes the core and releases the partner's.
#[cfg(feature = "hw_target")]
fn fault_entries() -> Option<bool> {
    let set_handler = |name, tcb| {
        invocation(
            name,
            TCB_SET_FAULT_HANDLER,
            tcb,
            [FAULT_HANDLER_CAP, 0, 0, 0],
        )
    };
    let copy_handler = invocation(
        "copy-fault-handler",
        CSPACE_COPY,
        CNODE_CAP,
        root_slot_copy(ENDPOINT_SLOT, FAULT_HANDLER_SLOT),
    );
    let delete_handler = invocation(
        "delete-fault-handler",
        CSPACE_DELETE,
        CNODE_CAP,
        [FAULT_HANDLER_SLOT, 0, 0, 0],
    );
    if !unmeasured(
        &copy_handler,
        "the fault handler's capability was not copied",
    ) || !unmeasured(
        &set_handler("set-root-fault-handler", ROOT_TCB_CAP),
        "the root task's fault handler was not set",
    ) || !unmeasured(
        &set_handler("set-partner-fault-handler", PARTNER_TCB_CAP),
        "the partner's fault handler was not set",
    ) || !unmeasured(
        &delete_handler,
        "the fault handler's capability was not deleted",
    ) {
        return Some(false);
    }
    for (kind, name) in FAULT_SUSPENDS.iter().enumerate() {
        let resume_root = invocation(FAULT_RESUMES[kind], TCB_RESUME, ROOT_TCB_CAP, [0; 4]);
        for first in [true, false] {
            let which = if first { " (first call)" } else { "" };
            if !unmeasured(&PARTNER_SETUP[0], "the partner was not resumed")
                || heap_allocations_trap(&fault_trip(kind, name), which) != Some(true)
                || heap_allocations_round_trip(&resume_root, which) != Some(true)
                || !suspend_partner()
            {
                return Some(false);
            }
        }
    }
    if !unmeasured(
        &copy_handler,
        "the fault handler's capability was not copied",
    ) {
        return Some(false);
    }
    let receive_fault = RoundTrip {
        name: "receive-queued-fault",
        syscall: RECEIVE,
        cptr: ENDPOINT_CAP,
        msg_len: 1,
        msg: [REPLY_CAP, 0, 0, 0],
        primed: None,
        blocks: false,
        caps_or_badges: None,
        overflow: None,
        returns: Some((VM_FAULT_MESSAGE_INFO, [None; 4])),
    };
    let reply_fault = partner_step("reply-queued-fault", REPLY, REPLY_CAP, 0, [0, 0], false);
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        if !unmeasured(&PARTNER_SETUP[0], "the partner was not resumed")
            || heap_allocations_trap(&data_abort("vm-fault-queued"), which) != Some(true)
            || heap_allocations_round_trip(&receive_fault, which) != Some(true)
            || heap_allocations_round_trip(&reply_fault, which) != Some(true)
            || !suspend_partner()
        {
            return Some(false);
        }
    }
    // The other four kinds queued the same way: each raised by the root task
    // while no handler waits, so the root task is queued on the handler's
    // endpoint (seL4's `sendFaultIPC` with no receiver); the partner's receive
    // takes the fault message (its label the kind's tag, its length the
    // frame's four words: no buffer is mapped for the rest) and its reply
    // restarts the root task.
    for kind in 1..FAULT_KINDS.len() {
        let receive = RoundTrip {
            name: FAULT_QUEUED_RECEIVES[kind],
            returns: Some((FAULT_QUEUED_INFO[kind], [None; 4])),
            ..receive_fault
        };
        let reply = partner_step(
            FAULT_QUEUED_REPLIES[kind],
            REPLY,
            REPLY_CAP,
            0,
            [0, 0],
            false,
        );
        for first in [true, false] {
            let which = if first { " (first call)" } else { "" };
            if !unmeasured(&PARTNER_SETUP[0], "the partner was not resumed")
                || heap_allocations_trap(&fault_trip(kind, FAULT_QUEUED[kind]), which) != Some(true)
                || heap_allocations_round_trip(&receive, which) != Some(true)
                || heap_allocations_round_trip(&reply, which) != Some(true)
                || !suspend_partner()
            {
                return Some(false);
            }
        }
    }
    // The handler waits first: the root task's receive blocks it, and the
    // partner, current in its place, faults to it (the root task is chosen
    // over the partner whenever both are runnable).
    let handler_waits = partner_step(
        "handler-waits",
        RECEIVE,
        ENDPOINT_CAP,
        1,
        [REPLY_CAP, 0],
        true,
    );
    let wake_handler = partner_step("wake-handler", SEND, ENDPOINT_CAP, 1, [0x55, 0], false);
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        if !unmeasured(&PARTNER_SETUP[0], "the partner was not resumed")
            || !unmeasured(&handler_waits, "the handler did not wait on the endpoint")
        {
            return Some(false);
        }
        for kind in 0..FAULT_KINDS.len() {
            let reply = partner_step(
                FAULT_REPLIES[kind],
                REPLY_RECV,
                ENDPOINT_CAP,
                2,
                [REPLY_CAP, FAULT_REPLY_WORD],
                true,
            );
            if heap_allocations_trap(&fault_trip(kind, FAULT_DELIVERED[kind]), which) != Some(true)
                || heap_allocations_round_trip_resuming(&reply, which, Some(fault_restart(kind)))
                    != Some(true)
            {
                return Some(false);
            }
        }
        if !unmeasured(&wake_handler, "the waiting handler was not woken") || !suspend_partner() {
            return Some(false);
        }
    }
    // The handler answers with `Reply` instead: it returns, the faulted
    // thread restarted behind it, and its next receive blocks it and resumes
    // that thread as its restart says.
    let handler_waits_again = partner_step(
        "handler-waits-again",
        RECEIVE,
        ENDPOINT_CAP,
        1,
        [REPLY_CAP, 0],
        true,
    );
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        if !unmeasured(&PARTNER_SETUP[0], "the partner was not resumed")
            || !unmeasured(&handler_waits, "the handler did not wait on the endpoint")
        {
            return Some(false);
        }
        for kind in 0..FAULT_KINDS.len() {
            let reply = partner_step(
                FAULT_PLAIN_REPLIES[kind],
                REPLY,
                REPLY_CAP,
                1,
                [FAULT_REPLY_WORD, 0],
                false,
            );
            if heap_allocations_trap(&fault_trip(kind, FAULT_DELIVERED_TO_REPLY[kind]), which)
                != Some(true)
                || heap_allocations_round_trip(&reply, which) != Some(true)
            {
                return Some(false);
            }
            let (waited, _, _, resumed) = dispatch_round_trip(&handler_waits_again);
            if !matches!(waited, Dispatched::Blocked) {
                crate::kprintln!(
                    "[smp-test] FAIL: heap-allocations-per-syscall: {}: the handler did not wait again",
                    FAULT_PLAIN_REPLIES[kind]
                );
                return Some(false);
            }
            if !restarted_as(FAULT_PLAIN_REPLIES[kind], &resumed, fault_restart(kind)) {
                return Some(false);
            }
        }
        if !unmeasured(&wake_handler, "the waiting handler was not woken") || !suspend_partner() {
            return Some(false);
        }
    }
    // A capability fault from a thread running on a scheduling context, to a
    // passive handler waiting with a reply object: the fault's call lends the
    // faulting thread's context to the handler (seL4-MCS `sendFaultIPC`, the
    // call's `schedContext_donate`), each write in its slot.  The handler's
    // reply hands the context back and restarts the faulting thread, which is
    // then suspended and the context unbound from it.  The timer is
    // masked across the sequence, so no tick switches the threads between steps.
    let donating_setup = [
        configure(
            "fault-donating-configure",
            [
                SCHED_CONTEXT_CAP,
                SCHED_CONTEXT_BUDGET,
                SCHED_CONTEXT_PERIOD,
                PARTNER_PRIORITY,
            ],
        ),
        invocation(
            "fault-donating-bind-partner",
            SCHED_CONTEXT_BIND,
            SCHED_CONTEXT_CAP,
            [PARTNER_TCB_CAP, 0, 0, 0],
        ),
        invocation("fault-donating-resume", TCB_RESUME, PARTNER_TCB_CAP, [0; 4]),
    ];
    let donating_reply = partner_step(
        "cap-fault-donating-reply",
        REPLY,
        REPLY_CAP,
        1,
        [FAULT_REPLY_WORD, 0],
        false,
    );
    let donating_teardown = [
        invocation(
            "fault-donating-suspend",
            TCB_SUSPEND,
            PARTNER_TCB_CAP,
            [0; 4],
        ),
        invocation(
            "fault-donating-unbind",
            SCHED_CONTEXT_UNBIND,
            SCHED_CONTEXT_CAP,
            [0; 4],
        ),
    ];
    let ticks = crate::interrupts::disable_interrupts();
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        if !unmeasured_all(&donating_setup, "the donating fault's setup failed")
            || !unmeasured(&handler_waits, "the handler did not wait on the endpoint")
            || heap_allocations_trap(&fault_trip(2, "cap-fault-donating-delivered"), which)
                != Some(true)
            || !fault_delivered("cap-fault-donating-delivered")
            || heap_allocations_round_trip(&donating_reply, which) != Some(true)
            || !unmeasured_all(&donating_teardown, "the donating fault's teardown failed")
        {
            return Some(false);
        }
    }
    crate::interrupts::restore_interrupts(ticks);
    // A capability fault answered by a reply at the longest message, 120
    // words, and then by a reply-receive at that length: the reply's words
    // past the fourth are read from the handler's IPC buffer, so a page is
    // mapped there for the run (unmeasured) and taken down after it.  The
    // faulted thread restarts as the fault reply says (seL4's
    // `handleFaultReply`).
    let map_buffer_page = invocation(
        "fault-long-map-buffer",
        VSPACE_MAP,
        VSPACE_CAP,
        [ROOT_ASID, FRAME_VADDR, FRAME_CAP, FRAME_PERMS],
    );
    let root_buffer = invocation(
        "fault-long-root-ipc-buffer",
        TCB_SET_IPC_BUFFER,
        ROOT_TCB_CAP,
        [FRAME_VADDR, 0, 0, 0],
    );
    if !unmeasured_all(&MOVE_SETUP_PAGE, "the long fault reply's page setup failed")
        || !unmeasured(
            &map_buffer_page,
            "the long fault reply's page was not mapped",
        )
        || !unmeasured(&root_buffer, "the handler's IPC buffer was not set")
    {
        return Some(false);
    }
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        if !overflow_cap_faults(&map_buffer_page, which) {
            return Some(false);
        }
    }
    let long_reply = partner_step(
        "cap-fault-long-reply",
        REPLY,
        REPLY_CAP,
        TAIL_MESSAGE_LENGTH,
        [FAULT_REPLY_WORD, 0],
        false,
    );
    let long_reply_recv = partner_step(
        "cap-fault-long-reply-recv",
        REPLY_RECV,
        ENDPOINT_CAP,
        TAIL_MESSAGE_LENGTH,
        [REPLY_CAP, FAULT_REPLY_WORD],
        true,
    );
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        if !unmeasured(&PARTNER_SETUP[0], "the partner was not resumed")
            || !unmeasured(&handler_waits, "the handler did not wait on the endpoint")
            || heap_allocations_trap(&fault_trip(2, "cap-fault-delivered-to-long-reply"), which)
                != Some(true)
            || heap_allocations_round_trip(&long_reply, which) != Some(true)
        {
            return Some(false);
        }
        let (waited, _, _, resumed) = dispatch_round_trip(&handler_waits_again);
        if !matches!(waited, Dispatched::Blocked) {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: cap-fault-long-reply: the handler did not wait again"
            );
            return Some(false);
        }
        if !restarted_as("cap-fault-long-reply", &resumed, fault_restart(2))
            || heap_allocations_trap(
                &fault_trip(2, "cap-fault-delivered-to-long-reply-recv"),
                which,
            ) != Some(true)
            || heap_allocations_round_trip_resuming(&long_reply_recv, which, Some(fault_restart(2)))
                != Some(true)
            || !unmeasured(&wake_handler, "the waiting handler was not woken")
            || !suspend_partner()
        {
            return Some(false);
        }
    }
    // A capability fault on an address that misses the root CNode's guard
    // (seL4's `seL4_GuardMismatch`): delivered to the handler while its IPC
    // buffer is mapped, so all seven `seL4_CapFault_*` words reach it (`IP`,
    // `Addr`, `InRecvPhase`, `LookupFailureType`, then `BitsLeft`,
    // `GuardMismatch_GuardFound` and `GuardMismatch_BitsFound` in the
    // buffer), the length seven and `LookupFailureType` GuardMismatch (4).
    // The three buffer words go back to zero before the handler's reply.
    let guard_mismatch_reply = partner_step(
        "cap-fault-guard-mismatch-reply",
        REPLY,
        REPLY_CAP,
        1,
        [FAULT_REPLY_WORD, 0],
        false,
    );
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        if !unmeasured(&PARTNER_SETUP[0], "the partner was not resumed")
            || !unmeasured(&handler_waits, "the handler did not wait on the endpoint")
            || heap_allocations_trap(
                &TrapTrip {
                    x0: EMPTY_SLOT,
                    ..cap_fault("cap-fault-guard-mismatch")
                },
                which,
            ) != Some(true)
        {
            return Some(false);
        }
        let info = TRAP_RESTORED_X1.load(Ordering::SeqCst);
        let lookup_type = TRAP_RESTORED_X5.load(Ordering::SeqCst);
        if info != CAP_FAULT_GUARD_MISMATCH_INFO || lookup_type != 4 {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: cap-fault-guard-mismatch: the handler received x1={:#x} x5={:#x}",
                info,
                lookup_type
            );
            return Some(false);
        }
        if !write_buffer_words(FRAME_VADDR, OVERFLOW_BASE_WORD, &[0, 0, 0])
            || heap_allocations_round_trip(&guard_mismatch_reply, which) != Some(true)
        {
            return Some(false);
        }
        let (waited, _, _, resumed) = dispatch_round_trip(&handler_waits_again);
        if !matches!(waited, Dispatched::Blocked) {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: cap-fault-guard-mismatch-reply: the handler did not wait again"
            );
            return Some(false);
        }
        // A capability fault resumes its own context: the guard-mismatched
        // address it trapped with in `x0`.
        let restart = FaultRestart {
            x0: EMPTY_SLOT,
            ..fault_restart(2)
        };
        if !restarted_as("cap-fault-guard-mismatch-reply", &resumed, restart)
            || !unmeasured(&wake_handler, "the waiting handler was not woken")
            || !suspend_partner()
        {
            return Some(false);
        }
    }
    if !receive_side_faults(&handler_waits, &handler_waits_again, &wake_handler) {
        return Some(false);
    }
    let root_buffer_back = invocation(
        "fault-long-root-ipc-buffer-back",
        TCB_SET_IPC_BUFFER,
        ROOT_TCB_CAP,
        [ROOT_IPC_BUFFER, 0, 0, 0],
    );
    if !unmeasured_all(
        &MOVE_TEARDOWN[4..],
        "the long fault reply's page teardown failed",
    ) || !unmeasured(
        &root_buffer_back,
        "the root task's IPC buffer was not set back",
    ) {
        return Some(false);
    }
    // The root task's access loads its context; its receive blocks it and
    // releases the core's registers to its saved context; the partner's
    // access loads the partner's; its send wakes the root task, which takes
    // the core and releases the partner's.
    let fp_blocks = partner_step("fp-owner-blocks", RECEIVE, ENDPOINT_CAP, 0, [0, 0], true);
    let fp_wakes = partner_step(
        "fp-owner-wakes-root",
        SEND,
        ENDPOINT_CAP,
        1,
        [0x55, 0],
        false,
    );
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        if !unmeasured(&PARTNER_SETUP[0], "the partner was not resumed")
            || heap_allocations_trap(&fp_access("fp-access"), which) != Some(true)
            || heap_allocations_round_trip(&fp_blocks, which) != Some(true)
            || heap_allocations_trap(&fp_access("fp-access-partner"), which) != Some(true)
            || heap_allocations_round_trip(&fp_wakes, which) != Some(true)
            || !suspend_partner()
        {
            return Some(false);
        }
    }
    if !unmeasured(
        &delete_handler,
        "the fault handler's capability was not deleted",
    ) {
        return Some(false);
    }
    Some(true)
}

/// Dispatch one round trip through the syscall seam with IRQs masked, reading
/// this core's heap counter before and after: what it did (printing why when
/// it did neither of the two things a round trip may do), and the two readings.
#[cfg(feature = "hw_target")]
fn dispatch_round_trip(trip: &RoundTrip) -> (Dispatched, Option<u64>, Option<u64>, Resumed) {
    dispatch_round_trip_at(trip, 0)
}

/// [`dispatch_round_trip`] with the frame's return address `pc`: the address
/// the issuing thread resumes at, saved into its TCB when the syscall switches
/// it out.
#[cfg(feature = "hw_target")]
fn dispatch_round_trip_at(
    trip: &RoundTrip,
    pc: u64,
) -> (Dispatched, Option<u64>, Option<u64>, Resumed) {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    let mut frame = crate::trap::TrapFrame {
        gprs: [0; 31],
        sp_el0: 0,
        elr_el1: pc,
        spsr_el1: ROUND_TRIP_SPSR,
        esr_el1: ROUND_TRIP_ESR,
        far_el1: 0,
        tpidr_el0: 0,
        reserved: 0,
    };
    frame.gprs[0] = trip.cptr;
    frame.gprs[1] = trip.msg_len;
    frame.gprs[2] = trip.msg[0];
    frame.gprs[3] = trip.msg[1];
    frame.gprs[4] = trip.msg[2];
    frame.gprs[5] = trip.msg[3];
    frame.gprs[7] = trip.syscall;
    if let Some((buffer, word)) = trip.overflow {
        if !write_buffer_words(buffer, OVERFLOW_BASE_WORD, &[word]) {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: {}: the IPC buffer at \
                 {buffer:#x} has no translation",
                trip.name
            );
            return (
                Dispatched::Failed,
                None,
                None,
                Resumed {
                    regs: [0; 6],
                    pc: 0,
                },
            );
        }
    }
    let saved_daif = crate::interrupts::disable_interrupts();
    let before = own_heap_allocations(core);
    let (dispatched, restored) = {
        let _in_flight = crate::trap::InFlightFrame::publish(&mut frame);
        // The `SVC` arm's own order: the classification, then the dispatch.
        let class = crate::trap::classify_synchronous_exception(ROUND_TRIP_ESR);
        let dispatched = if class == crate::trap::sync_class::SVC {
            crate::svc_dispatch::dispatch_svc(trip.syscall as u32)
        } else {
            Err(crate::svc_dispatch::DispatchError::InvalidSyscallId)
        };
        (dispatched, crate::trap::take_restored())
    };
    let after = own_heap_allocations(core);
    if let Some((buffer, _)) = trip.overflow {
        // The word back to the zero the boot's scrub left, outside the
        // measured window; the page was mapped a moment ago, so this write
        // finds it again.
        let _ = write_buffer_words(buffer, OVERFLOW_BASE_WORD, &[0]);
    }
    // The restore replaced the published frame with the resumed thread's
    // context: its `x0` to `x5` and its PC are what that thread resumes with.
    let mut resumed = Resumed {
        regs: [0u64; 6],
        pc: frame.elr_el1,
    };
    resumed.regs.copy_from_slice(&frame.gprs[..6]);
    crate::interrupts::restore_interrupts(saved_daif);
    // The restore installed the resumed thread's translation and set the
    // FP/SIMD trap for it.  This core goes on with its bring-up, so both go
    // back: the boot tables (whose kernel window every address space shares,
    // so the bring-up never stopped running) and the armed trap the boot
    // prologue leaves (`CPACR_EL1 = 0`).
    crate::user_translation::install_translation(crate::user_translation::Translation::Kernel);
    crate::fp_context::set_trap_for_resume(false);
    let name = trip.name;
    if !restored {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: resumed no thread"
        );
        return (Dispatched::Failed, before, after, resumed);
    }
    let outcome = match dispatched {
        // A refusal is an ordinary frame too, its status in the `x1` label
        // (`error_frame_regs`): only label 0, the success, measures the
        // syscall the gate names.  A receive that takes a fault message
        // returns the fault's tag as its label, which the round trip names
        // exactly (`returns`).
        Ok(crate::svc_dispatch::SvcOutcome::Frame(regs))
            if regs[1] >> 12 == 0 || trip.returns.is_some_and(|(x1, _)| regs[1] == x1) =>
        {
            Dispatched::Returned(regs)
        }
        Ok(crate::svc_dispatch::SvcOutcome::Frame(regs)) => {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: {name}: refused (x1 label {:#x})",
                regs[1] >> 12
            );
            Dispatched::Failed
        }
        Ok(crate::svc_dispatch::SvcOutcome::Blocked) => Dispatched::Blocked,
        Ok(other) => {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: {name}: did not return: {other:?}"
            );
            Dispatched::Failed
        }
        Err(error) => {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: {name}: refused: {error:?}"
            );
            Dispatched::Failed
        }
    };
    (outcome, before, after, resumed)
}

/// **WS-ZA ZA6.29's requeue and linked branches**: the setup, the measured
/// requeue, the partner raised, the measured linked round trip, the link's
/// clearing checked, and the partner, blocked on the notification wait,
/// suspended and the context unbound from it (each measured), so the second
/// run finds the state the first did.
#[cfg(feature = "hw_target")]
fn yield_to_branches(which: &str) -> Option<bool> {
    // The bind unmeasured; the partner's priority lowered while it is
    // suspended and its resume, measured.
    if !unmeasured(&YIELD_TO_SETUP[0], "the yieldTo setup failed") {
        return Some(false);
    }
    for step in YIELD_TO_SETUP[1..].iter() {
        if heap_allocations_round_trip(step, which) != Some(true) {
            return Some(false);
        }
    }
    if heap_allocations_round_trip(&YIELD_TO_REQUEUE, which) != Some(true) {
        return Some(false);
    }
    // The partner, ready and queued on core 0 below the root task, raised to
    // the root task's priority: re-queued in its new band in place.
    if heap_allocations_round_trip(&YIELD_TO_RAISE, which) != Some(true) {
        return Some(false);
    }
    if heap_allocations_yield_to_linked(which) != Some(true) {
        return Some(false);
    }
    if !unmeasured(
        &YIELD_TO_CLEARED,
        "the root task's yield link was not cleared",
    ) {
        return Some(false);
    }
    // WS-ZA ZA6.33: the partner, blocked on the notification wait and holding
    // the bound context, is suspended through the routed arm (its wait
    // cancelled in place, the context left bound), then the context unbound,
    // each measured.
    if heap_allocations_round_trip(&SUSPEND_WAITING_PARTNER, which) != Some(true) {
        return Some(false);
    }
    if heap_allocations_round_trip(&UNBIND_SUSPENDED_PARTNER, which) != Some(true) {
        return Some(false);
    }
    Some(true)
}

/// **WS-ZA ZA6.33: an affinity change that moves a thread off the core it is
/// running on** (seL4's `remoteTCBStall` before the thread is migrated).  A
/// thread carved for it, bound to a scheduling context of
/// its own (the image context's tenth of the processor, which the thread
/// spends only in core 1's ticks and does not use up across the section) below
/// the root task's priority, resumes at a frame of real code: one page holding
/// `b .`, mapped user-executable at the user window's first page.  Homed on
/// core 1 it runs there at EL0, and the root task's affinity change homes it
/// back while it runs, which vacates core 1 (its current slot cleared, a
/// reschedule raised) and stalls core 1 until it has left the thread and saved
/// it.  Each call is measured; the thread is homed on core 1 again between
/// them, unmeasured.  The carved objects reuse the frame scenarios' ids and
/// slots and the chain's thread id and slot, all free again by here.
#[cfg(feature = "hw_target")]
const MOVE_SC_ID: u64 = 35;
#[cfg(feature = "hw_target")]
const MOVE_SC_SLOT: u64 = 27;
#[cfg(feature = "hw_target")]
const MOVE_SC_CAP: u64 = cap_address(MOVE_SC_SLOT);
/// The moved thread's priority (its context's): below the root task's, so the
/// root task keeps core 0 whenever both are ready there.
#[cfg(feature = "hw_target")]
const MOVE_PRIORITY: u64 = 100;
/// Read, execute, user and cacheable (`PagePermissions.ofNat`).
#[cfg(feature = "hw_target")]
const CODE_PERMS: u64 = 0b11101;
/// Two `b .` instructions, the word the code page starts with.
#[cfg(feature = "hw_target")]
const SPIN_CODE_WORD: u64 = 0x1400_0000_1400_0000;
/// The word the moved thread's send carries, which the root task's receive
/// returns in `x2` once the thread's receive switches core 0 back to it.
#[cfg(feature = "hw_target")]
const MOVE_MARKER: u64 = 0x6d6f_7665;
/// The thread's setup, once the code page is mapped: the context carved,
/// configured and bound to the carved thread, whose space is the root task's.
#[cfg(feature = "hw_target")]
const MOVE_SETUP_THREAD: [RoundTrip; 5] = [
    invocation(
        "move-retype-sched-context",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [SCHED_CONTEXT_TYPE, MOVE_SC_ID, CNODE_CAP, MOVE_SC_SLOT],
    ),
    configure(
        "move-configure",
        [
            MOVE_SC_CAP,
            SCHED_CONTEXT_BUDGET,
            SCHED_CONTEXT_PERIOD,
            MOVE_PRIORITY,
        ],
    ),
    invocation(
        "move-retype-tcb",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [TCB_TYPE, CHAIN_CHILD_IDS[0], CNODE_CAP, CHAIN_TCB_SLOT],
    ),
    invocation(
        "move-tcb-set-space",
        TCB_SET_SPACE,
        CHAIN_TCB_CAP,
        [CNODE_CAP, VSPACE_CAP, 0, 0],
    ),
    invocation(
        "move-bind",
        SCHED_CONTEXT_BIND,
        MOVE_SC_CAP,
        [CHAIN_TCB_CAP, 0, 0, 0],
    ),
];
/// The code page: three tables completing the walk to the user window's
/// first page, a frame carved and mapped there user-executable.
#[cfg(feature = "hw_target")]
const MOVE_SETUP_PAGE: [RoundTrip; 7] = [
    invocation(
        "move-retype-page-table-1",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            PAGE_TABLE_TYPE,
            PAGE_TABLE_CHILD_IDS[0],
            CNODE_CAP,
            PAGE_TABLE_SLOTS[0],
        ],
    ),
    invocation(
        "move-page-table-map-1",
        PAGE_TABLE_MAP,
        PAGE_TABLE_CAPS[0],
        [VSPACE_CAP, FRAME_VADDR, 0, 0],
    ),
    invocation(
        "move-retype-page-table-2",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            PAGE_TABLE_TYPE,
            PAGE_TABLE_CHILD_IDS[1],
            CNODE_CAP,
            PAGE_TABLE_SLOTS[1],
        ],
    ),
    invocation(
        "move-page-table-map-2",
        PAGE_TABLE_MAP,
        PAGE_TABLE_CAPS[1],
        [VSPACE_CAP, FRAME_VADDR, 0, 0],
    ),
    invocation(
        "move-retype-page-table-3",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [
            PAGE_TABLE_TYPE,
            PAGE_TABLE_CHILD_IDS[2],
            CNODE_CAP,
            PAGE_TABLE_SLOTS[2],
        ],
    ),
    invocation(
        "move-page-table-map-3",
        PAGE_TABLE_MAP,
        PAGE_TABLE_CAPS[2],
        [VSPACE_CAP, FRAME_VADDR, 0, 0],
    ),
    invocation(
        "move-retype-frame",
        UNTYPED_RETYPE,
        UNTYPED_CAP,
        [FRAME_TYPE, FRAME_CHILD_ID, CNODE_CAP, FRAME_SLOT],
    ),
];
/// The frame mapped user-executable, after its code is written.
#[cfg(feature = "hw_target")]
const MOVE_MAP_CODE: RoundTrip = invocation(
    "move-map-code",
    VSPACE_MAP,
    VSPACE_CAP,
    [ROOT_ASID, FRAME_VADDR, FRAME_CAP, CODE_PERMS],
);
/// The written code published to instruction fetch.
#[cfg(feature = "hw_target")]
const MOVE_UNIFY: RoundTrip = invocation(
    "move-unify-instruction",
    VSPACE_UNIFY_INSTRUCTION,
    VSPACE_CAP,
    [ROOT_ASID, FRAME_VADDR, 0, 0],
);
/// The thread resumed (ready on core 0, below the root task); the root task's
/// receive, which blocks and switches core 0 to the thread; the thread's send,
/// which readies the root task and continues the thread; and the thread's
/// receive from the code page's address, which blocks it there and switches
/// core 0 back to the root task.  Homed on core 1, the thread is then woken by
/// the root task's send and runs on core 1 from that address.
#[cfg(feature = "hw_target")]
const MOVE_RESUME: RoundTrip = invocation("move-resume", TCB_RESUME, CHAIN_TCB_CAP, [0; 4]);
#[cfg(feature = "hw_target")]
const MOVE_ROOT_RECEIVES: RoundTrip =
    partner_step("move-root-receives", RECEIVE, ENDPOINT_CAP, 0, [0, 0], true);
#[cfg(feature = "hw_target")]
const MOVE_THREAD_SENDS: RoundTrip = partner_step(
    "move-thread-sends",
    SEND,
    ENDPOINT_CAP,
    1,
    [MOVE_MARKER, 0],
    false,
);
#[cfg(feature = "hw_target")]
const MOVE_THREAD_RECEIVES: RoundTrip = partner_step(
    "move-thread-receives",
    RECEIVE,
    ENDPOINT_CAP,
    0,
    [0, 0],
    true,
);
#[cfg(feature = "hw_target")]
const MOVE_ROOT_WAKES: RoundTrip =
    partner_step("move-root-wakes", SEND, ENDPOINT_CAP, 1, [0, 0], false);
/// The thread homed on core 1, where it runs; and the measured change that
/// homes it back while it runs there.
#[cfg(feature = "hw_target")]
const MOVE_HOME_SECOND: RoundTrip = invocation(
    "move-home-second-core",
    TCB_SET_AFFINITY,
    CHAIN_TCB_CAP,
    [SECOND_CORE_AFFINITY, 0, 0, 0],
);
#[cfg(feature = "hw_target")]
const MOVE_RUNNING: RoundTrip = invocation(
    "tcb-set-affinity-running",
    TCB_SET_AFFINITY,
    CHAIN_TCB_CAP,
    [AFFINITY_UNBIND, 0, 0, 0],
);
/// Everything taken down again: the thread suspended (on core 0's run queue
/// by then), the context unbound, both deleted, the page unmapped and deleted,
/// and the tables taken out deepest first and deleted.
#[cfg(feature = "hw_target")]
const MOVE_TEARDOWN: [RoundTrip; 12] = [
    invocation("move-suspend", TCB_SUSPEND, CHAIN_TCB_CAP, [0; 4]),
    invocation("move-unbind", SCHED_CONTEXT_UNBIND, MOVE_SC_CAP, [0; 4]),
    invocation(
        "move-sc-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [MOVE_SC_SLOT, 0, 0, 0],
    ),
    invocation(
        "move-tcb-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [CHAIN_TCB_SLOT, 0, 0, 0],
    ),
    invocation(
        "move-unmap-code",
        VSPACE_UNMAP,
        VSPACE_CAP,
        [ROOT_ASID, FRAME_VADDR, 0, 0],
    ),
    invocation(
        "move-frame-delete",
        CSPACE_DELETE,
        CNODE_CAP,
        [FRAME_SLOT, 0, 0, 0],
    ),
    invocation(
        "move-page-table-unmap-3",
        PAGE_TABLE_UNMAP,
        PAGE_TABLE_CAPS[2],
        [0; 4],
    ),
    invocation(
        "move-page-table-delete-3",
        CSPACE_DELETE,
        CNODE_CAP,
        [PAGE_TABLE_SLOTS[2], 0, 0, 0],
    ),
    invocation(
        "move-page-table-unmap-2",
        PAGE_TABLE_UNMAP,
        PAGE_TABLE_CAPS[1],
        [0; 4],
    ),
    invocation(
        "move-page-table-delete-2",
        CSPACE_DELETE,
        CNODE_CAP,
        [PAGE_TABLE_SLOTS[1], 0, 0, 0],
    ),
    invocation(
        "move-page-table-unmap-1",
        PAGE_TABLE_UNMAP,
        PAGE_TABLE_CAPS[0],
        [0; 4],
    ),
    invocation(
        "move-page-table-delete-1",
        CSPACE_DELETE,
        CNODE_CAP,
        [PAGE_TABLE_SLOTS[0], 0, 0, 0],
    ),
];

/// The physical page the root task's address space maps at `vaddr`, read off
/// the hardware tables the kernel wrote (four levels from the root's table in
/// the boot pool), or `None` where a level holds no valid descriptor.
#[cfg(feature = "hw_target")]
fn root_user_page(vaddr: u64) -> Option<u64> {
    const OUTPUT_ADDRESS: u64 = 0x0000_FFFF_FFFF_F000;
    let mut table = crate::mmu::BOOT_TABLE_POOL_BASE;
    for level in 0..4u64 {
        let index = (vaddr >> (39 - 9 * level)) & 0x1FF;
        // SAFETY: `table` is the root's pool page or a table page a valid
        // descriptor names, RAM under the kernel's identity map; one aligned
        // 64-bit load of one of its 512 entries.
        let descriptor = unsafe { core::ptr::read_volatile((table + index * 8) as *const u64) };
        if descriptor & 0b11 != 0b11 {
            return None;
        }
        table = descriptor & OUTPUT_ADDRESS;
    }
    Some(table)
}

/// Write `words` into the `caps_or_badges` and receive-path words of the IPC
/// buffer the root task's tables map at `buffer`, where a capability-carrying
/// send names its extra capabilities and a receiver its receive slot (seL4's
/// `seL4_SetCap` and `seL4_SetCapReceivePath`); `false` when the buffer's
/// page has no translation to RAM past the kernel's extent.
#[cfg(feature = "hw_target")]
fn write_caps_or_badges(buffer: u64, words: [u64; 3]) -> bool {
    write_buffer_words(buffer, CAPS_OR_BADGES_WORD, &words)
}

/// Write `words` (at most three) into the IPC buffer the root task's tables
/// map at `buffer` from word `first` on: its `caps_or_badges`
/// ([`write_caps_or_badges`]), its receive path ([`RECEIVE_PATH_STEP`]) or a
/// message's first overflow word ([`RoundTrip::overflow`]).
#[cfg(feature = "hw_target")]
fn write_buffer_words(buffer: u64, first: u64, words: &[u64]) -> bool {
    if words.len() > 3 {
        return false;
    }
    let Some(page) = root_user_page(buffer & !0xFFF) else {
        return false;
    };
    if page < crate::mmu::KERNEL_RESERVED_END || !page.is_multiple_of(4096) {
        return false;
    }
    let base = page + (buffer & 0xFFF) + first * 8;
    for (i, word) in words.iter().enumerate() {
        // SAFETY: `base` and the five words after it are inside the
        // 1024-byte buffer the root task's tables map onto `page`, RAM past the kernel's extent under the
        // identity map; no thread runs while the issuing core writes it; one
        // aligned 64-bit store per word.
        unsafe { core::ptr::write_volatile((base + 8 * i as u64) as *mut u64, *word) };
    }
    core::sync::atomic::fence(Ordering::SeqCst);
    true
}

/// Wait, bounded by the command timeout, for `ready` to hold.
#[cfg(feature = "hw_target")]
fn wait_until(mut ready: impl FnMut() -> bool) -> bool {
    let start = crate::timer::read_counter();
    let timeout = command_timeout_ticks();
    loop {
        if ready() {
            return true;
        }
        if crate::timer::read_counter().saturating_sub(start) >= timeout {
            return ready();
        }
        core::hint::spin_loop();
    }
}

/// Whether core 1 is running a thread at EL0, seen twice a millisecond apart
/// (a tick on core 1 between the two returns it to the same thread).
#[cfg(feature = "hw_target")]
fn second_core_at_user() -> bool {
    let at_user = || crate::remote_stall::AT_USER[1].load(Ordering::SeqCst);
    if !wait_until(at_user) {
        return false;
    }
    let settle = crate::timer::read_counter()
        .saturating_add(u64::from(crate::timer::read_frequency()) / 1000);
    while crate::timer::read_counter() < settle {
        core::hint::spin_loop();
    }
    wait_until(at_user)
}

/// Whether core 1 has left EL0 for good: not at user, seen twice a
/// millisecond apart.
#[cfg(feature = "hw_target")]
fn second_core_left_user() -> bool {
    let left = || !crate::remote_stall::AT_USER[1].load(Ordering::SeqCst);
    if !wait_until(left) {
        return false;
    }
    let settle = crate::timer::read_counter()
        .saturating_add(u64::from(crate::timer::read_frequency()) / 1000);
    while crate::timer::read_counter() < settle {
        core::hint::spin_loop();
    }
    left()
}

/// Run `steps` unmeasured, naming `why` on the first that fails.
#[cfg(feature = "hw_target")]
fn unmeasured_all(steps: &[RoundTrip], why: &str) -> bool {
    steps.iter().all(|step| unmeasured(step, why))
}

/// Report `why` for the running-thread move and fail.
#[cfg(feature = "hw_target")]
fn move_failed(why: &str) -> Option<bool> {
    crate::kprintln!(
        "[smp-test] FAIL: heap-allocations-per-syscall: tcb-set-affinity-running: {why}"
    );
    Some(false)
}

/// The affinity change of a thread running on core 1, first call and steady
/// state ([`MOVE_RUNNING`]); the timer masked by the caller.
#[cfg(feature = "hw_target")]
fn affinity_move_running() -> Option<bool> {
    // The page first, at the scenarios' window; the configure reads its
    // fifth word from the root task's own buffer (`ROOT_IPC_BUFFER`), which
    // the boot scrubbed.
    if !unmeasured_all(&MOVE_SETUP_PAGE, "the code page's setup failed")
        || !unmeasured(&MOVE_MAP_CODE, "the code page was not mapped")
        || !unmeasured_all(&MOVE_SETUP_THREAD, "the moved thread's setup failed")
    {
        return Some(false);
    }
    let Some(page) = root_user_page(FRAME_VADDR) else {
        return move_failed("the code page has no translation");
    };
    if page < crate::mmu::KERNEL_RESERVED_END || !page.is_multiple_of(4096) {
        return move_failed("the code page's translation names no frame");
    }
    // SAFETY: `page` is the frame the root task's tables map at the code
    // address, RAM past the kernel's extent under the identity map, which no
    // thread runs yet; one aligned 64-bit store.
    unsafe { core::ptr::write_volatile(page as *mut u64, SPIN_CODE_WORD) };
    core::sync::atomic::fence(Ordering::SeqCst);
    if !unmeasured(&MOVE_UNIFY, "the code page was not unified")
        || !unmeasured(&MOVE_RESUME, "the moved thread was not resumed")
        || !unmeasured(&MOVE_ROOT_RECEIVES, "the root task's receive did not block")
    {
        return Some(false);
    }
    if !unmeasured(&MOVE_THREAD_SENDS, "the thread's send failed") {
        return Some(false);
    }
    let (received, _, _, resumed) = dispatch_round_trip_at(&MOVE_THREAD_RECEIVES, FRAME_VADDR);
    if !matches!(received, Dispatched::Blocked) || resumed.regs[2] != MOVE_MARKER {
        return move_failed("the thread's receive did not switch core 0 back to the root task");
    }
    if !unmeasured(&MOVE_HOME_SECOND, "the thread was not homed on core 1")
        || !unmeasured(&MOVE_ROOT_WAKES, "the root task's send failed")
    {
        return Some(false);
    }
    for first in [true, false] {
        let which = if first { " (first call)" } else { "" };
        if !first && !unmeasured(&MOVE_HOME_SECOND, "the thread was not homed on core 1") {
            return Some(false);
        }
        if !second_core_at_user() {
            return move_failed("core 1 did not run the thread at EL0");
        }
        if heap_allocations_round_trip(&MOVE_RUNNING, which) != Some(true) {
            return Some(false);
        }
        if !second_core_left_user() {
            return move_failed("core 1 still runs the thread");
        }
    }
    Some(unmeasured_all(&MOVE_TEARDOWN, "the move's teardown failed"))
}

/// The moved thread's own delete of its only capability, issued as that
/// thread while it runs on core 0: the delete finalises the caller itself
/// (its context still bound), so the dispatch restores the root task, whose
/// receive the thread's send completed.
#[cfg(feature = "hw_target")]
const SELF_TCB_DELETE: RoundTrip = invocation(
    "self-tcb-delete",
    CSPACE_DELETE,
    CNODE_CAP,
    [CHAIN_TCB_SLOT, 0, 0, 0],
);
/// The root task's delete of the moved thread's only capability while the
/// thread runs on core 1: the finalisation takes it off that core
/// (`finaliseThreadReleaseCores`) with its context still bound.
#[cfg(feature = "hw_target")]
const REMOTE_TCB_DELETE: RoundTrip = invocation(
    "remote-running-tcb-delete",
    CSPACE_DELETE,
    CNODE_CAP,
    [CHAIN_TCB_SLOT, 0, 0, 0],
);
/// [`SELF_TCB_DELETE`] measured: the dispatch answers the success it computed
/// for the caller, but the context it installed is the root task's, its
/// receive's frame carrying the thread's marker (the trap layer returns through
/// that context and drops the answer, `trap.rs`'s `take_restored`).
#[cfg(feature = "hw_target")]
fn heap_allocations_self_delete(which: &str) -> Option<bool> {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    let name = SELF_TCB_DELETE.name;
    let (outcome, before, after, resumed) = dispatch_round_trip(&SELF_TCB_DELETE);
    print_routed(&SELF_TCB_DELETE, core, which, &outcome);
    let (Some(before), Some(after)) = (before, after) else {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the heap counter could not be read"
        );
        return Some(false);
    };
    let Dispatched::Returned(regs) = outcome else {
        crate::kprintln!("[smp-test] FAIL: heap-allocations-per-syscall: {name}: did not return");
        return Some(false);
    };
    if resumed.regs[2] != MOVE_MARKER {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the root task was not restored"
        );
        return Some(false);
    }
    crate::kprintln!(
        "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: returned x0={:#x} x1={:#x}",
        regs[0],
        regs[1]
    );
    crate::kprintln!(
        "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: deleted {:#x}/{}",
        SELF_TCB_DELETE.cptr,
        SELF_TCB_DELETE.msg[0]
    );
    if after < before {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the counter went back ({before} -> {after})"
        );
        return Some(false);
    }
    print_reading(name, core, which, before, after, window_start());
    Some(true)
}

/// What the move's teardown leaves once the thread is gone: its context's
/// delete, the page unmapped and deleted, and the tables taken out deepest
/// first and deleted.
#[cfg(feature = "hw_target")]
fn deleted_thread_teardown() -> bool {
    unmeasured(
        &MOVE_TEARDOWN[2],
        "the deleted thread's context was not deleted",
    ) && unmeasured_all(
        &MOVE_TEARDOWN[4..],
        "the deleted thread's page was not taken down",
    )
}

/// **The final delete of a running thread**, measured once per call: the
/// moved thread set up as [`affinity_move_running`] sets it up, resumed, and
/// running on core 0 once the root task's receive blocks; then either its own
/// delete of its capability ([`SELF_TCB_DELETE`]) or, once it has blocked,
/// been homed on core 1 and woken there, the root task's
/// ([`REMOTE_TCB_DELETE`]).  The timer is masked by the caller.
#[cfg(feature = "hw_target")]
fn running_thread_delete(remote: bool, which: &str) -> Option<bool> {
    if !unmeasured_all(&MOVE_SETUP_PAGE, "the code page's setup failed")
        || !unmeasured(&MOVE_MAP_CODE, "the code page was not mapped")
        || !unmeasured_all(&MOVE_SETUP_THREAD, "the moved thread's setup failed")
    {
        return Some(false);
    }
    let Some(page) = root_user_page(FRAME_VADDR) else {
        return move_failed("the code page has no translation");
    };
    if page < crate::mmu::KERNEL_RESERVED_END || !page.is_multiple_of(4096) {
        return move_failed("the code page's translation names no frame");
    }
    // SAFETY: as in `affinity_move_running`: the frame the root task's tables
    // map at the code address, which no thread runs yet; one aligned store.
    unsafe { core::ptr::write_volatile(page as *mut u64, SPIN_CODE_WORD) };
    core::sync::atomic::fence(Ordering::SeqCst);
    if !unmeasured(&MOVE_UNIFY, "the code page was not unified")
        || !unmeasured(&MOVE_RESUME, "the moved thread was not resumed")
        || !unmeasured(&MOVE_ROOT_RECEIVES, "the root task's receive did not block")
        || !unmeasured(&MOVE_THREAD_SENDS, "the thread's send failed")
    {
        return Some(false);
    }
    if !remote {
        if heap_allocations_self_delete(which) != Some(true) {
            return Some(false);
        }
        return Some(deleted_thread_teardown());
    }
    let (received, _, _, resumed) = dispatch_round_trip_at(&MOVE_THREAD_RECEIVES, FRAME_VADDR);
    if !matches!(received, Dispatched::Blocked) || resumed.regs[2] != MOVE_MARKER {
        return move_failed("the thread's receive did not switch core 0 back to the root task");
    }
    if !unmeasured(&MOVE_HOME_SECOND, "the thread was not homed on core 1")
        || !unmeasured(&MOVE_ROOT_WAKES, "the root task's send failed")
    {
        return Some(false);
    }
    if !second_core_at_user() {
        return move_failed("core 1 did not run the thread at EL0");
    }
    if heap_allocations_round_trip(&REMOTE_TCB_DELETE, which) != Some(true) {
        return Some(false);
    }
    if !second_core_left_user() {
        return move_failed("core 1 still runs the deleted thread");
    }
    Some(deleted_thread_teardown())
}

/// **The remote thread's program** for [`remote_core_entries`], at the code
/// page's start: an FP/SIMD instruction (its first trap on core 1 makes core 1
/// its FP owner), then a wait for the stage word at [`REMOTE_STAGE_OFFSET`] to
/// reach 1, a `TCB_Suspend` of the root task's TCB, a wait for stage 2, a
/// `TCB_Resume` of it, and a spin.
///
/// ```text
///   0: fmov d0, xzr
///   4: ldr x9, stage ; cmp x9, #1 ; b.lo 4
///  10: mov x0, #1 ; movk x0, #0x8000, lsl #48 ; mov x1, #4 ; mov x7, #20 ; svc #0
///  24: ldr x9, stage ; cmp x9, #2 ; b.lo 24
///  30: mov x0, #1 ; movk x0, #0x8000, lsl #48 ; mov x1, #4 ; mov x7, #21 ; svc #0
///  44: b .
/// ```
#[cfg(feature = "hw_target")]
const REMOTE_PROGRAM: [u32; 18] = [
    0x9e67_03e0,
    0x5800_3fe9,
    0xf100_053f,
    0x54ff_ffc3,
    0xd280_0020,
    0xf2f0_0000,
    0xd280_0081,
    0xd280_0287,
    0xd400_0001,
    0x5800_3ee9,
    0xf100_093f,
    0x54ff_ffc3,
    0xd280_0020,
    0xf2f0_0000,
    0xd280_0081,
    0xd280_02a7,
    0xd400_0001,
    0x1400_0000,
];
/// The stage word's offset in the code page (the program's `ldr` literal).
#[cfg(feature = "hw_target")]
const REMOTE_STAGE_OFFSET: u64 = 0x800;

/// Store `stage` into the remote thread's stage word, in the code page
/// `page` (its physical frame, under the kernel's identity map).
#[cfg(feature = "hw_target")]
fn remote_stage(page: u64, stage: u64) {
    // SAFETY: `page` is the frame the root task's tables map at the code
    // address, RAM past the kernel's extent; the stage word is the program's
    // literal, which the thread only reads; one aligned 64-bit store.
    unsafe { core::ptr::write_volatile((page + REMOTE_STAGE_OFFSET) as *mut u64, stage) };
    core::sync::atomic::fence(Ordering::SeqCst);
}

/// Report `why` for the remote-core scenario and fail.
#[cfg(feature = "hw_target")]
fn remote_failed(why: &str) -> Option<bool> {
    crate::kprintln!("[smp-test] FAIL: heap-allocations-per-syscall: remote-core: {why}");
    Some(false)
}

/// The frame's copy mapped at the next page and unmapped while the root
/// task's address space is live on core 1, and the copy's capability.
#[cfg(feature = "hw_target")]
const REMOTE_COPY: RoundTrip = invocation(
    "remote-asid-frame-copy",
    CSPACE_COPY,
    CNODE_CAP,
    root_slot_copy(FRAME_SLOT, MOVE_SLOT),
);
#[cfg(feature = "hw_target")]
const REMOTE_MAP: RoundTrip = invocation(
    "remote-asid-map",
    VSPACE_MAP,
    VSPACE_CAP,
    [ROOT_ASID, FRAME_COPY_VADDR, MOVE_CAP, FRAME_PERMS],
);
#[cfg(feature = "hw_target")]
const REMOTE_UNMAP: RoundTrip = invocation(
    "remote-asid-unmap",
    VSPACE_UNMAP,
    VSPACE_CAP,
    [ROOT_ASID, FRAME_COPY_VADDR, 0, 0],
);
#[cfg(feature = "hw_target")]
const REMOTE_COPY_DELETE: RoundTrip = invocation(
    "remote-asid-frame-copy-delete",
    CSPACE_DELETE,
    CNODE_CAP,
    [MOVE_SLOT, 0, 0, 0],
);
/// The root task's syscall on core 0 once core 1 has taken it off core 0: a
/// yield, which the entry does not run (`vacatedCore_next_syscall_rejected`):
/// it answers `illegalState`.
#[cfg(feature = "hw_target")]
const VACATED_CORE_SYSCALL: RoundTrip = RoundTrip {
    returns: refused(ILLEGAL_STATE),
    ..kernel_step("vacated-core-syscall", YIELD)
};
/// `KernelError.illegalState`'s discriminant: the vacated core's answer, which
/// no thread receives (its restore resumes the successor, and the root task's
/// frame is rewound to its `SVC`).
#[cfg(feature = "hw_target")]
const ILLEGAL_STATE: u64 = 2;
/// The moved thread homed back on core 0 while core 1, held, still owns its
/// FP/SIMD values; then the root task's receive, which blocks.
#[cfg(feature = "hw_target")]
const FP_DEFERRED_HOME_BACK: RoundTrip = invocation(
    "fp-deferred-home-back",
    TCB_SET_AFFINITY,
    CHAIN_TCB_CAP,
    [AFFINITY_UNBIND, 0, 0, 0],
);
#[cfg(feature = "hw_target")]
const FP_DEFERRED_ROOT_RECEIVES: RoundTrip = partner_step(
    "fp-deferred-root-receives",
    RECEIVE,
    ENDPOINT_CAP,
    0,
    [0, 0],
    true,
);

/// Wait until core 1 has issued `count` syscalls, then a millisecond more.
#[cfg(feature = "hw_target")]
fn second_core_syscalls_reach(count: u64) -> bool {
    let reached = wait_until(|| crate::per_cpu_stats::syscall_count_for(1) >= count);
    let settle = crate::timer::read_counter()
        .saturating_add(u64::from(crate::timer::read_frequency()) / 1000);
    while crate::timer::read_counter() < settle {
        core::hint::spin_loop();
    }
    reached
}

/// A round trip measured whatever its restore resumed: the vacated core's
/// syscall, which the entry answers by dispatching a successor.
#[cfg(feature = "hw_target")]
fn heap_allocations_any_restore(trip: &RoundTrip, which: &str) -> Option<bool> {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    let name = trip.name;
    let (outcome, before, after, _) = dispatch_round_trip(trip);
    let (Some(before), Some(after)) = (before, after) else {
        return remote_failed("the heap counter could not be read");
    };
    if matches!(outcome, Dispatched::Failed) {
        return Some(false);
    }
    crate::kprintln!(
        "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: entered, a thread restored"
    );
    if after < before {
        return remote_failed("the counter went back");
    }
    print_routed(trip, core, which, &outcome);
    print_reading(name, core, which, before, after, window_start());
    Some(true)
}

/// **The kernel entries a remote core's work reaches**, measured once per
/// call (the timer masked by the caller).  The moved thread is set up as
/// [`affinity_move_running`] sets it up, its code [`REMOTE_PROGRAM`], and runs
/// on core 1 in the root task's address space, having made core 1 its FP/SIMD
/// owner.  Then, each measured on core 0:
/// - a map and an unmap of the frame's copy at the next page while that
///   address space is live on core 1, so the unmap's shootdown round has a
///   remote target (seL4's `invalidateTLBByASID` across the cores the ASID
///   ran on);
/// - the root task's syscall once the thread's `TCB_Suspend` on core 1 has
///   taken the root task off core 0 (the vacated core's entry: the frame saved
///   to the resident thread rewound to its `SVC`, the syscall not run, a
///   successor dispatched), and, once the thread's `TCB_Resume` has made it
///   ready again, the reschedule that runs it;
/// - with core 1 held in its agent handler, the thread homed back on core 0
///   and the root task's receive, which blocks: core 0 does not resume the
///   thread, still resident on core 1 (`deferResidentElsewhere`), so an
///   FP/SIMD access there loads nothing; then, core 1 released (its entry
///   saves the thread, releases its live values and pokes core 0), the
///   reschedule that runs the thread on core 0 and its access, which loads
///   the values core 1 saved.  The residency deferral is what keeps
///   `fpAccessOnCore`'s `.retry` arm (`fpOwnedElsewhere`) from being reached:
///   a thread is resumed only where no other core still holds it, and a
///   core's FP/SIMD owner is its resident until the entry that releases both.
#[cfg(feature = "hw_target")]
fn remote_core_entries(which: &str) -> Option<bool> {
    if !unmeasured_all(&MOVE_SETUP_PAGE, "the code page's setup failed")
        || !unmeasured(&MOVE_MAP_CODE, "the code page was not mapped")
        || !unmeasured_all(&MOVE_SETUP_THREAD, "the moved thread's setup failed")
    {
        return Some(false);
    }
    let Some(page) = root_user_page(FRAME_VADDR) else {
        return remote_failed("the code page has no translation");
    };
    if page < crate::mmu::KERNEL_RESERVED_END || !page.is_multiple_of(4096) {
        return remote_failed("the code page's translation names no frame");
    }
    for (i, word) in REMOTE_PROGRAM.iter().enumerate() {
        // SAFETY: as in `affinity_move_running`: the frame the root task's
        // tables map at the code address, which no thread runs yet; one
        // aligned 32-bit store per instruction, inside the page.
        unsafe { core::ptr::write_volatile((page + 4 * i as u64) as *mut u32, *word) };
    }
    remote_stage(page, 0);
    if !unmeasured(&MOVE_UNIFY, "the code page was not unified")
        || !unmeasured(&MOVE_RESUME, "the moved thread was not resumed")
        || !unmeasured(&MOVE_ROOT_RECEIVES, "the root task's receive did not block")
        || !unmeasured(&MOVE_THREAD_SENDS, "the thread's send failed")
    {
        return Some(false);
    }
    let (received, _, _, resumed) = dispatch_round_trip_at(&MOVE_THREAD_RECEIVES, FRAME_VADDR);
    if !matches!(received, Dispatched::Blocked) || resumed.regs[2] != MOVE_MARKER {
        return remote_failed("the thread's receive did not switch core 0 back to the root task");
    }
    if !unmeasured(&MOVE_HOME_SECOND, "the thread was not homed on core 1")
        || !unmeasured(&MOVE_ROOT_WAKES, "the root task's send failed")
    {
        return Some(false);
    }
    if !second_core_at_user() {
        return remote_failed("core 1 did not run the thread at EL0");
    }
    if !unmeasured(&REMOTE_COPY, "the frame was not copied")
        || heap_allocations_round_trip(&REMOTE_MAP, which) != Some(true)
        || heap_allocations_round_trip(&REMOTE_UNMAP, which) != Some(true)
        || !unmeasured(&REMOTE_COPY_DELETE, "the frame's copy was not deleted")
    {
        return Some(false);
    }
    let syscalls = crate::per_cpu_stats::syscall_count_for(1);
    remote_stage(page, 1);
    if !second_core_syscalls_reach(syscalls + 1)
        || !wait_until(|| crate::remote_stall::STALL_REQUESTED[0].load(Ordering::SeqCst))
    {
        return remote_failed("the thread's suspend of the root task did not reach core 0");
    }
    if heap_allocations_any_restore(&VACATED_CORE_SYSCALL, which) != Some(true) {
        return Some(false);
    }
    if !second_core_at_user() {
        return remote_failed("core 1 did not return to the thread after its suspend");
    }
    remote_stage(page, 2);
    if !second_core_syscalls_reach(syscalls + 2) || !second_core_at_user() {
        return remote_failed("the thread's resume of the root task did not complete");
    }
    let reschedule = KernelEntry {
        name: "vacated-core-reschedule",
        enter: crate::trap::reschedule_sgi_entry,
    };
    if heap_allocations_kernel_entry(&reschedule, which) != Some(true) {
        return Some(false);
    }
    let Some(held) = hold_core(1) else {
        return remote_failed("core 1 was not held");
    };
    if heap_allocations_round_trip(&FP_DEFERRED_HOME_BACK, which) != Some(true)
        || heap_allocations_round_trip(&FP_DEFERRED_ROOT_RECEIVES, which) != Some(true)
        || heap_allocations_trap(&fp_access("fp-access-deferred"), which) != Some(true)
    {
        let _released = release_core(1, held);
        return Some(false);
    }
    let deferred = !TRAP_LOADED_FP.load(Ordering::SeqCst);
    if !release_core(1, held) {
        return remote_failed("core 1 did not report its release");
    }
    if !second_core_left_user() {
        return remote_failed("core 1 still runs the thread");
    }
    if !deferred {
        return remote_failed("core 0 loaded FP/SIMD values while core 1 held the thread");
    }
    let released = KernelEntry {
        name: "fp-released-reschedule",
        enter: crate::trap::reschedule_sgi_entry,
    };
    if heap_allocations_kernel_entry(&released, which) != Some(true)
        || heap_allocations_trap(&fp_access("fp-access-released"), which) != Some(true)
    {
        return Some(false);
    }
    if !TRAP_LOADED_FP.load(Ordering::SeqCst) {
        return remote_failed("the FP/SIMD access did not load once core 1 released the values");
    }
    if !unmeasured(&MOVE_THREAD_SENDS, "the thread's send failed") {
        return Some(false);
    }
    let (received, _, _, _) = dispatch_round_trip_at(&MOVE_THREAD_RECEIVES, FRAME_VADDR);
    if !matches!(received, Dispatched::Blocked) {
        return remote_failed("the thread's receive did not switch core 0 back to the root task");
    }
    Some(unmeasured_all(
        &MOVE_TEARDOWN,
        "the remote scenario's teardown failed",
    ))
}

/// **The linked yieldTo, measured across its whole round trip**: the root
/// task's yieldTo, which links the yield and switches core 0 to the partner,
/// then the partner's wait, which blocks it and switches back to the root
/// task, whose activation completes the link.  One reading spans both
/// dispatches (the timer is masked by the caller), and the round trip's
/// return is the root task's frame as it resumes: the consumed-info word in
/// `x1`, written by the activation.
#[cfg(feature = "hw_target")]
fn heap_allocations_yield_to_linked(which: &str) -> Option<bool> {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    let name = YIELD_TO_LINK.name;
    let (linked, before, _, _) = dispatch_round_trip(&YIELD_TO_LINK);
    let start = window_start();
    match linked {
        Dispatched::Returned(regs) if regs[1] != CONSUMED_INFO_WORD => {}
        Dispatched::Returned(_) => {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the consumed time returned at once, so the yield was not linked"
            );
            return Some(false);
        }
        Dispatched::Blocked => {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the yieldTo blocked its caller"
            );
            return Some(false);
        }
        Dispatched::Failed => return Some(false),
    }
    print_routed(&YIELD_TO_LINK, core, which, &linked);
    let (blocked, _, after, resumed) = dispatch_round_trip(&YIELD_TO_PARTNER_BLOCKS);
    print_routed(&YIELD_TO_PARTNER_BLOCKS, core, which, &blocked);
    if !matches!(blocked, Dispatched::Blocked) {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the partner's wait did not block"
        );
        return Some(false);
    }
    let (Some(before), Some(after)) = (before, after) else {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the heap counter could not be read"
        );
        return Some(false);
    };
    if resumed.regs[1] != CONSUMED_INFO_WORD {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the caller resumed with x1={:#x}, expected the consumed-info word {CONSUMED_INFO_WORD:#x}",
            resumed.regs[1]
        );
        return Some(false);
    }
    crate::kprintln!(
        "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: returned x0={:#x} x1={:#x}",
        resumed.regs[0],
        resumed.regs[1]
    );
    if after < before {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the counter went back ({before} -> {after})"
        );
        return Some(false);
    }
    print_reading(name, core, which, before, after, start);
    Some(true)
}

/// One measured round trip of `heap_allocations_per_syscall`; `which` labels
/// its printed lines.
#[cfg(feature = "hw_target")]
fn heap_allocations_round_trip(trip: &RoundTrip, which: &str) -> Option<bool> {
    heap_allocations_round_trip_resuming(trip, which, None)
}

/// [`heap_allocations_round_trip`] of a round trip that blocks and resumes
/// the other thread at `resumes`' PC with its `x0` and `x1`, when given: a
/// fault answer's restart.
#[cfg(feature = "hw_target")]
fn heap_allocations_round_trip_resuming(
    trip: &RoundTrip,
    which: &str,
    resumes: Option<FaultRestart>,
) -> Option<bool> {
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    let name = trip.name;
    if let Some((buffer, words, path)) = trip.caps_or_badges {
        let path_written = match path {
            Some(path) => write_buffer_words(buffer, RECEIVE_PATH_WORD, &path),
            None => true,
        };
        if !(write_caps_or_badges(buffer, words) && path_written) {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the IPC buffer at \
                 {buffer:#x} has no translation"
            );
            return Some(false);
        }
    }
    let (outcome, before, after, resumed) = dispatch_round_trip(trip);
    if let (Dispatched::Blocked, Some(expected)) = (&outcome, resumes) {
        if !restarted_as(name, &resumed, expected) {
            return Some(false);
        }
    }
    let (Some(before), Some(after)) = (before, after) else {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the heap counter could not be read"
        );
        return Some(false);
    };
    if let (Dispatched::Returned(regs), Some((x1, mrs))) = (&outcome, trip.returns) {
        let mrs_match = mrs
            .iter()
            .enumerate()
            .all(|(i, mr)| mr.is_none_or(|mr| regs[2 + i] == mr));
        if regs[1] != x1 || !mrs_match {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: {name}: returned x1={:#x} \
                 x2..x5={:#x?}, expected x1={x1:#x} x2..x5={mrs:?}",
                regs[1],
                &regs[2..6]
            );
            return Some(false);
        }
    }
    print_routed(trip, core, which, &outcome);
    match outcome {
        Dispatched::Returned(regs) if !trip.blocks => {
            crate::kprintln!(
                "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: returned x0={:#x} x1={:#x}",
                regs[0],
                regs[1]
            );
            // A retype that succeeded names the object it carved, its kind and
            // its size bits as the tag word gave them: the host-side gate holds
            // the reading to that object's own cells.  It names the object's id
            // and the slot its capability went to, and a delete that succeeded
            // names the slot it emptied, so the gate can relate each carved
            // kind to the delete of its capability (WS-UC UC1).
            if trip.syscall == UNTYPED_RETYPE
                && regs[1] >> 12 < crate::svc_dispatch::ERROR_LABEL_BASE
            {
                crate::kprintln!(
                    "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: carved {}/{} at {} into {:#x}/{}",
                    carved_kind(trip.msg[0] & 0xff),
                    trip.msg[0] >> 8,
                    trip.msg[1],
                    trip.msg[2],
                    trip.msg[3]
                );
            }
            if trip.syscall == CSPACE_DELETE
                && regs[1] >> 12 < crate::svc_dispatch::ERROR_LABEL_BASE
            {
                crate::kprintln!(
                    "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: deleted {:#x}/{}",
                    trip.cptr,
                    trip.msg[0]
                );
            }
        }
        Dispatched::Blocked if trip.blocks => crate::kprintln!(
            "[smp-test] heap-allocations-per-syscall: {name}: core {core}{which}: blocked, the other thread restored"
        ),
        Dispatched::Failed => return Some(false),
        Dispatched::Returned(regs) => {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: {name}: did not block, returned x0={:#x} x1={:#x}",
                regs[0],
                regs[1]
            );
            return Some(false);
        }
        Dispatched::Blocked => {
            crate::kprintln!(
                "[smp-test] FAIL: heap-allocations-per-syscall: {name}: did not return"
            );
            return Some(false);
        }
    }
    if after < before {
        crate::kprintln!(
            "[smp-test] FAIL: heap-allocations-per-syscall: {name}: the counter went back ({before} -> {after})"
        );
        return Some(false);
    }
    print_reading(name, core, which, before, after, window_start());
    Some(true)
}

/// The name of a `KernelObjectType` tag (Lean's `KernelObjectType.ofNat?`).
#[cfg(feature = "hw_target")]
const fn carved_kind(tag: u64) -> &'static str {
    match tag {
        0 => "tcb",
        1 => "endpoint",
        2 => "notification",
        3 => "cnode",
        4 => "vspace-root",
        5 => "untyped",
        6 => "sched-context",
        7 => "reply",
        8 => "frame",
        9 => "page-table",
        _ => "unknown",
    }
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

    /// The harness's `caps_or_badges` word is the ABI's `IpcBuffer` field,
    /// and the receive path's three words follow its three.
    #[test]
    fn caps_or_badges_word_is_the_abi_layout() {
        assert_eq!(
            CAPS_OR_BADGES_WORD as usize * 8,
            core::mem::offset_of!(sele4n_abi::IpcBuffer, caps_or_badges)
        );
        assert_eq!(
            (CAPS_OR_BADGES_WORD as usize + 3) * 8,
            core::mem::offset_of!(sele4n_abi::IpcBuffer, receive_cnode)
        );
        assert_eq!(
            (CAPS_OR_BADGES_WORD as usize + 5) * 8,
            core::mem::offset_of!(sele4n_abi::IpcBuffer, receive_depth)
        );
    }

    /// The harness's receive-path word is the ABI's `IpcBuffer` field.
    #[test]
    fn receive_path_word_is_the_abi_layout() {
        assert_eq!(
            RECEIVE_PATH_WORD as usize * 8,
            core::mem::offset_of!(sele4n_abi::IpcBuffer, receive_cnode)
        );
    }

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
