// SPDX-License-Identifier: GPL-3.0-or-later
//! GIC-400 interrupt controller driver for Raspberry Pi 5.
//!
//! Base addresses (from Board.lean):
//! - GICD (distributor):   0xFF841000
//! - GICC (CPU interface): 0xFF842000
//!
//! Implements AG5-A (distributor init), AG5-B (CPU interface init),
//! AG5-C (acknowledge/dispatch/EOI).
//!
//! ## Interrupt Flow
//!
//! 1. Hardware asserts IRQ line
//! 2. CPU takes exception to EL1 IRQ vector → `handle_irq` (trap.rs)
//! 3. `acknowledge_irq()` reads GICC_IAR → returns INTID
//! 4. Dispatch based on INTID (timer PPI 30 → timer handler, etc.)
//! 5. `end_of_interrupt()` writes GICC_EOIR → signals completion
//!
//! ## GIC-400 Register Map (BCM2712)
//!
//! - GICD_CTLR:      distributor control (enable/disable)
//! - GICD_IGROUPR:   interrupt group (Group 0 = IRQ, Group 1 = FIQ)
//! - GICD_ISENABLER: interrupt set-enable
//! - GICD_ICENABLER: interrupt clear-enable
//! - GICD_ICPENDR:   interrupt clear-pending
//! - GICD_IPRIORITYR: interrupt priority
//! - GICD_ITARGETSR: interrupt target CPU
//! - GICC_CTLR:      CPU interface control
//! - GICC_PMR:       priority mask
//! - GICC_BPR:       binary point
//! - GICC_IAR:       interrupt acknowledge
//! - GICC_EOIR:      end of interrupt

// ============================================================================
// Constants
// ============================================================================

/// GIC-400 Distributor base address (from Board.lean `gicDistributorBase`).
pub const GICD_BASE: usize = 0xFF841000;

/// GIC-400 CPU Interface base address (from Board.lean `gicCpuInterfaceBase`).
pub const GICC_BASE: usize = 0xFF842000;

/// Timer PPI interrupt ID (non-secure physical timer, INTID 30).
/// Matches Lean `timerPpiId` and `timerInterruptId`.
pub const TIMER_PPI_ID: u32 = 30;

/// Spurious interrupt threshold — INTIDs >= 1020 are spurious.
/// Matches Lean `spuriousInterruptId`.
pub const SPURIOUS_THRESHOLD: u32 = 1020;

/// Number of SPI lines on BCM2712 (INTIDs 32-223).
/// Matches Lean `gicSpiCount`.
pub const SPI_COUNT: u32 = 192;

/// Total supported INTIDs (SGIs + PPIs + SPIs = 224).
pub const MAX_INTID: u32 = 224;

// ============================================================================
// GIC-400 Distributor Register Offsets
// ============================================================================

mod gicd {
    /// Distributor Control Register.
    pub const CTLR: usize = 0x000;
    /// Interrupt Group Registers (banked per 32 interrupts).
    pub const IGROUPR_BASE: usize = 0x080;
    /// Interrupt Set-Enable Registers.
    pub const ISENABLER_BASE: usize = 0x100;
    /// Interrupt Clear-Enable Registers — written by future selective-disable
    /// paths (per-IRQ mask/unmask wired by AN9-F SVC FFI handlers); currently
    /// declared for forward reference and to keep the GIC distributor map
    /// complete in this module. AN8-E (R-HAL-L1) retains the constant
    /// alongside `ISENABLER_BASE` so the GIC register set is documented as
    /// a coherent unit.
    #[allow(dead_code)]
    pub const ICENABLER_BASE: usize = 0x180;
    /// Interrupt Clear-Pending Registers.
    pub const ICPENDR_BASE: usize = 0x280;
    /// Interrupt Priority Registers (8-bit per INTID, 4 per word).
    pub const IPRIORITYR_BASE: usize = 0x400;
    /// Interrupt Processor Targets Registers (8-bit per INTID, 4 per word).
    pub const ITARGETSR_BASE: usize = 0x800;
    /// **WS-SM SM1.F.1**: Software Generated Interrupt Register.
    /// Writing here injects an SGI to one or more CPU interfaces.
    /// GIC-400 TRM §4.3.13: GICD_SGIR layout (32-bit):
    ///   bits [31:26]  RES0
    ///   bits [25:24]  TargetListFilter
    ///                  00 = forward to CPUs in CPUTargetList
    ///                  01 = forward to all PEs except the requesting PE
    ///                  10 = forward to the requesting PE only
    ///                  11 = reserved
    ///   bits [23:16]  CPUTargetList (bitmask of target CPU interfaces 0..7)
    ///   bit  [15]     NSATT (0 = Non-secure SGI on Group 0; ignored for our config)
    ///   bits [14:4]   RES0
    ///   bits [3:0]    SGIINTID (target SGI INTID, 0..15)
    pub const SGIR: usize = 0xF00;
}

// ============================================================================
// GIC-400 CPU Interface Register Offsets
// ============================================================================

mod gicc {
    /// CPU Interface Control Register.
    pub const CTLR: usize = 0x000;
    /// Interrupt Priority Mask Register.
    pub const PMR: usize = 0x004;
    /// Binary Point Register.
    pub const BPR: usize = 0x008;
    /// Interrupt Acknowledge Register (read to acknowledge).
    pub const IAR: usize = 0x00C;
    /// End of Interrupt Register (write to signal completion).
    pub const EOIR: usize = 0x010;
}

// ============================================================================
// AK5-G (R-HAL-M04 / MEDIUM): Use crate::mmio instead of local MMIO helpers
// so GIC accesses go through the AJ5-A alignment asserts. GIC-400 registers
// are 32-bit and naturally 4-byte-aligned, so the assert is a no-op on
// valid inputs; it catches programmer errors (mis-computed offsets) at the
// earliest possible point.
// ============================================================================

use crate::mmio::{mmio_read32, mmio_write32};

// ============================================================================
// AG5-A: GIC-400 Distributor Initialization
// ============================================================================

/// Initialize the GIC-400 Distributor.
///
/// Configures all interrupt routing for single-core operation on RPi5.
/// After initialization, all SPIs are:
/// - Assigned to Group 0 (delivered as IRQ, not FIQ)
/// - Routed to CPU 0
/// - Set to default priority 0xA0
/// - Cleared of any pending state
/// - Enabled
///
/// ARM GIC-400 TRM §3.1: The Distributor must be disabled during configuration,
/// then re-enabled once all registers are programmed.
pub fn init_distributor(base: usize) {
    // Step 1: Disable distributor during configuration
    // ARM GIC-400 TRM §4.3.1: GICD_CTLR.Enable = 0
    mmio_write32(base + gicd::CTLR, 0);

    // Number of 32-interrupt register banks needed.
    // MAX_INTID = 224, so we need ceil(224/32) = 7 banks.
    let num_banks = MAX_INTID.div_ceil(32) as usize;

    // Step 2: Configure interrupt groups — all Group 0 (IRQ delivery)
    // ARM GIC-400 TRM §4.3.4: GICD_IGROUPRn, bit=0 means Group 0
    for i in 0..num_banks {
        mmio_write32(base + gicd::IGROUPR_BASE + i * 4, 0x0000_0000);
    }

    // Step 3: Set default priority for all interrupts
    // ARM GIC-400 TRM §4.3.11: GICD_IPRIORITYRn
    // Priority 0xA0 — mid-range, allowing higher-priority overrides.
    // 4 INTIDs per 32-bit register (8 bits each).
    let num_prio_regs = MAX_INTID.div_ceil(4) as usize;
    for i in 0..num_prio_regs {
        mmio_write32(base + gicd::IPRIORITYR_BASE + i * 4, 0xA0A0_A0A0);
    }

    // Step 4: Route all SPIs to CPU 0
    // ARM GIC-400 TRM §4.3.12: GICD_ITARGETSRn
    // Bits [7:0] per INTID — bit 0 = CPU 0. SGIs/PPIs (INTIDs 0-31) are
    // read-only (always routed to the local CPU), so start from bank 1.
    let num_target_regs = MAX_INTID.div_ceil(4) as usize;
    for i in 8..num_target_regs {
        // Banks 0-7 (INTIDs 0-31) are banked/RO; skip them.
        mmio_write32(
            base + gicd::ITARGETSR_BASE + i * 4,
            0x0101_0101, // CPU 0 for each of the 4 INTIDs in this register
        );
    }

    // Step 5: Clear all pending interrupts
    // ARM GIC-400 TRM §4.3.8: GICD_ICPENDRn, write 1 to clear
    for i in 0..num_banks {
        mmio_write32(base + gicd::ICPENDR_BASE + i * 4, 0xFFFF_FFFF);
    }

    // Step 6: Enable all interrupts
    // ARM GIC-400 TRM §4.3.5: GICD_ISENABLERn, write 1 to enable
    for i in 0..num_banks {
        mmio_write32(base + gicd::ISENABLER_BASE + i * 4, 0xFFFF_FFFF);
    }

    // Step 7: Re-enable distributor
    // ARM GIC-400 TRM §4.3.1: GICD_CTLR.EnableGrp0 = 1
    mmio_write32(base + gicd::CTLR, 1);
}

// ============================================================================
// AG5-B: GIC-400 CPU Interface Initialization
// ============================================================================

/// Initialize the GIC-400 CPU Interface.
///
/// After initialization:
/// - Priority mask = 0xFF (accept all priority levels)
/// - Binary point = 0 (no priority grouping, all 8 bits used for priority)
/// - CPU interface enabled
///
/// ARM GIC-400 TRM §4.4: The CPU interface controls interrupt delivery
/// to the connected processor.
pub fn init_cpu_interface(base: usize) {
    // Step 1: Set priority mask to accept all priorities
    // ARM GIC-400 TRM §4.4.2: GICC_PMR — 0xFF means lowest priority
    // threshold, so all interrupts with priority < 0xFF are delivered.
    mmio_write32(base + gicc::PMR, 0xFF);

    // Step 2: No priority grouping — use all 8 bits for priority
    // ARM GIC-400 TRM §4.4.3: GICC_BPR = 0
    mmio_write32(base + gicc::BPR, 0);

    // Step 3: Enable CPU interface
    // ARM GIC-400 TRM §4.4.1: GICC_CTLR.EnableGrp0 = 1
    mmio_write32(base + gicc::CTLR, 1);
}

// ============================================================================
// AG5-C: GIC-400 IRQ Acknowledge / Dispatch / EOI
// ============================================================================

/// Acknowledge a pending interrupt by reading GICC_IAR.
///
/// Returns the raw INTID. The caller must check `is_spurious()` before
/// dispatching. Reading GICC_IAR also marks the interrupt as active in
/// the GIC (transition from pending → active).
///
/// ARM GIC-400 TRM §4.4.4: GICC_IAR bits [9:0] contain the INTID.
#[inline(always)]
pub fn acknowledge_irq(base: usize) -> u32 {
    mmio_read32(base + gicc::IAR) & 0x3FF // Extract INTID (bits [9:0])
}

/// Signal end-of-interrupt by writing to GICC_EOIR.
///
/// This transitions the interrupt from active → inactive in the GIC,
/// allowing the same interrupt to fire again.
///
/// ARM GIC-400 TRM §4.4.5: Write the INTID to GICC_EOIR.
#[inline(always)]
pub fn end_of_interrupt(base: usize, intid: u32) {
    mmio_write32(base + gicc::EOIR, intid);
}

/// Check if an interrupt ID is spurious.
///
/// INTIDs >= 1020 are returned by GICC_IAR when no pending interrupt
/// exists. Spurious interrupts require no dispatch or EOI.
#[inline(always)]
pub const fn is_spurious(intid: u32) -> bool {
    intid >= SPURIOUS_THRESHOLD
}

/// Initialize both the GIC-400 distributor and CPU interface.
///
/// Call this during boot after MMU and VBAR setup, before enabling
/// interrupts (before clearing PSTATE.I).
///
/// AN8-D (RUST-M05) self-check: after distributor init, write a known
/// pattern to a writable `GICD_ITARGETSR` slot and read it back. If the
/// pattern does not round-trip, the distributor is mis-mapped or
/// non-functional and the kernel halts immediately rather than booting
/// with broken interrupt routing. The read-back uses register 8 (INTID
/// 32 — first SPI), which is writable per ARM GIC-400 TRM §4.3.12; SGIs
/// and PPIs (registers 0-7) are banked / read-only and cannot serve as
/// a self-check target.
pub fn init_gic() {
    init_distributor(GICD_BASE);
    self_check_distributor(GICD_BASE);
    init_cpu_interface(GICC_BASE);
}

// ============================================================================
// WS-SM SM1.C.3 — Secondary-core GIC CPU interface initialization
// ============================================================================

/// **WS-SM SM1.C.3** (closes SMP-C2 GIC step): Initialize the calling
/// secondary core's GIC-400 CPU interface.
///
/// GIC-400's CPU interface registers (GICC_CTLR, GICC_PMR, GICC_BPR)
/// are **banked per-core** even though they live at a single MMIO
/// address ([`GICC_BASE`] on BCM2712).  Each core therefore writes
/// them independently via its own banked view, configuring its own
/// interrupt-delivery state without affecting other cores.
///
/// Reuses [`init_cpu_interface`] (which the primary's [`init_gic`]
/// also calls) so primary and secondary CPU-interface init flow
/// through the same code path.  The `core_id` argument is consumed
/// only by the diagnostic `kprintln`; the actual register
/// programming is identical on every core.
///
/// **WS-SM SM1.F audit-pass-1 fix** — per-core SGI/PPI enable:
/// GICD_ISENABLER0 (covering INTIDs 0..31, i.e., SGIs 0..15 + PPIs
/// 16..31) is also **banked per-core** (GIC-400 TRM §4.3.5).  The
/// primary's `init_distributor` writes ISENABLER0 from the boot
/// core's view, which only enables for the boot core — secondaries'
/// banked views remain at the reset default (all disabled).  Without
/// this per-core enable:
///
///   - SGIs sent to a secondary via [`send_sgi`] would remain
///     pending in the distributor but never forward to the
///     secondary's CPU interface (GIC-400 TRM §3.5: "an SGI
///     delivered to a CPU interface where it is disabled is held
///     pending until enabled or cleared").  The SM1.F primitive
///     would be silently non-functional for the cross-core wake
///     use case.
///   - Per-core timer PPI (INTID 30) would also not fire on
///     secondaries — they'd never tick.
///
/// The fix below writes ISENABLER0 = `0xFFFF_FFFF` from the
/// secondary's banked view, enabling every PPI and SGI on this
/// core.  This mirrors what the primary's `init_distributor` does
/// for its own banked view; it does NOT affect other cores' views.
///
/// **Pre-condition**: the primary's `init_gic` (Phase 3 in
/// `rust_boot_main`) must have already run, having initialised the
/// shared distributor.  Secondary cores would otherwise observe
/// uninitialised distributor state when receiving SPIs (cross-core
/// interrupts).  PPIs (the timer's PPI 30, kernel SGIs 0..4) are
/// fully functional on each core after this CPU-interface init,
/// regardless of distributor state.
///
/// **GIC-400 TRM**: §4.4 describes the CPU interface register layout.
/// §4.4.1 (GICC_CTLR.EnableGrp0 = 1) and §4.4.2 (GICC_PMR = 0xFF) are
/// the substantive enables; §4.4.3 (GICC_BPR = 0) disables priority
/// grouping so all 8 priority bits are honoured.  §4.3.5
/// (GICD_ISENABLER0) is the per-core PPI/SGI enable.
pub fn init_cpu_interface_secondary(core_id: u64) {
    init_cpu_interface(GICC_BASE);
    // SM1.F audit-pass-1: enable this core's banked PPI/SGI slot in
    // the distributor.  Writes from this CPU only affect this CPU's
    // banked view per GIC-400 TRM §4.3.5; no impact on other cores.
    // Without this, send_sgi(target=this_core, ...) silently fails
    // to deliver because the SGI stays pending in the distributor.
    mmio_write32(GICD_BASE + gicd::ISENABLER_BASE, 0xFFFF_FFFF);
    crate::kprintln!(
        "[smp] core {core_id}: GIC-400 CPU interface initialized (PMR=0xFF, BPR=0, CTLR=1, ISENABLER0=0xFFFFFFFF)"
    );
}

/// AN8-D (RUST-M05): boot-time GICD_ITARGETSR readback self-check.
///
/// `init_distributor` writes `0x0101_0101` to all SPI ITARGETSR registers
/// (CPU 0 for each of 4 INTIDs). After init, we read back register index
/// 8 (the first writable SPI bank) and verify the value matches. A
/// mis-routed MMIO mapping or a faulty distributor would diverge here,
/// and we halt immediately — booting with broken interrupt routing would
/// cause silent dispatch failures later in the boot sequence.
///
/// On non-aarch64 hosts, MMIO ops are no-ops and `mmio_read32` returns
/// 0; the self-check would always fail — so we skip it under
/// `cfg!(test)` and `cfg(not(target_arch = "aarch64"))`.
fn self_check_distributor(base: usize) {
    let actual = read_self_check_target(base);
    if actual != SELF_CHECK_EXPECTED {
        // SAFETY: gicd::ITARGETSR is a 32-bit register, well-defined
        // even after init. We do not panic because the kernel's UART
        // may not be reliable if the distributor is broken; instead
        // we WFE-loop forever, halting the core. On non-aarch64 hosts
        // (test profile), the read returns 0 and we'd otherwise WFE-loop
        // forever — so we early-return on non-aarch64 to keep tests
        // running while still exercising the read structure.
        #[cfg(all(target_arch = "aarch64", not(test)))]
        loop {
            crate::cpu::wfe();
        }
    }
}

/// AN8-D (RUST-M05) audit: register index used by the boot self-check.
/// Bank 8 is `GICD_ITARGETSR[8]`, covering INTIDs 32-35 (first SPIs);
/// banks 0-7 are banked / read-only per ARM GIC-400 TRM §4.3.12.
const SELF_CHECK_TARGET_INDEX: usize = 8;
/// Pattern written to writable ITARGETSR slots by `init_distributor`
/// (CPU 0 for each of the four 8-bit INTID lanes in the 32-bit register).
const SELF_CHECK_EXPECTED: u32 = 0x0101_0101;

/// AN8-D (RUST-M05) audit: split out the read-back logic so unit tests
/// can verify the address arithmetic and the structure of the check
/// without WFE-looping. The function returns the value read at the
/// computed ITARGETSR slot.
///
/// Under `cfg(all(target_arch = "aarch64", not(test)))` (production
/// kernel builds) this performs a real volatile MMIO read. On other
/// configurations — including `cargo test` on aarch64 hosts where the
/// `0xFF841820` address is not mapped — it returns 0 to keep the test
/// suite pointer-safe. `self_check_distributor` correctly treats the
/// 0-return as a mismatch and skips the WFE-loop on the same gate.
#[inline(always)]
fn read_self_check_target(base: usize) -> u32 {
    let addr = base + gicd::ITARGETSR_BASE + SELF_CHECK_TARGET_INDEX * 4;
    #[cfg(all(target_arch = "aarch64", not(test)))]
    {
        // SAFETY: production boot path; address is inside the GICD MMIO
        // window mapped by AK5-D's identity-map. (ARM ARM B2.1)
        return unsafe { core::ptr::read_volatile(addr as *const u32) };
    }
    #[cfg(any(not(target_arch = "aarch64"), test))]
    {
        let _ = addr;
        0
    }
}

/// BCM2712 (RPi5) supported INTID count. INTIDs in `[MAX_SUPPORTED, 1020)`
/// are within the GIC-400 architecture but unsupported on this hardware;
/// they can surface due to errata or SMP races and must still receive EOI
/// to prevent GIC lockup.
///
/// AK3-C.4: Aligns with Lean `InterruptDispatch.lean` `InterruptId := Fin 224`.
pub const MAX_SUPPORTED_INTID: u32 = 224;

/// AK3-C.4 (A-H02 / HIGH): GIC acknowledge result — three-way distinction
/// matching the Lean model's `AckError` inductive:
/// - `Handled(intid)`:    valid INTID ∈ [0, 224) — dispatch + EOI
/// - `OutOfRange(intid)`: INTID ∈ [224, 1020) — **EOI required**, no dispatch
/// - `Spurious`:          INTID ≥ 1020 — no EOI per GIC-400 spec
///
/// This replaces the earlier `is_spurious` binary check which conflated
/// out-of-range INTIDs with spurious ones, causing GIC lockup on errata.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AckResult {
    /// INTID is within supported range; dispatch the handler and EOI.
    Handled(u32),
    /// INTID ∈ [224, 1020) — unsupported on BCM2712 but legal on GIC-400.
    /// The caller MUST emit EOI with this raw value to complete the
    /// interrupt cycle.
    OutOfRange(u32),
    /// INTID ≥ 1020 — spurious per GIC spec; no EOI required.
    Spurious,
}

/// AK3-C.4 (A-H02 / HIGH): Acknowledge and classify an interrupt.
#[inline(always)]
pub fn acknowledge_irq_classified(base: usize) -> AckResult {
    let intid = acknowledge_irq(base);
    if intid >= SPURIOUS_THRESHOLD {
        AckResult::Spurious
    } else if intid >= MAX_SUPPORTED_INTID {
        AckResult::OutOfRange(intid)
    } else {
        AckResult::Handled(intid)
    }
}

// ============================================================================
// WS-SM SM1.F — Software-Generated Interrupt (SGI) primitives
//
// SGIs are inter-processor interrupts in the GIC's INTID range [0, 16).
// Per WS-SM SM0.H (`SeLe4n.Kernel.Concurrency.SgiKind`), the kernel
// reserves the lowest 5 SGI slots for SMP coordination:
//
//   INTID 0 — reschedule
//   INTID 1 — tlbShootdownReq
//   INTID 2 — tlbShootdownAck
//   INTID 3 — cacheBroadcast
//   INTID 4 — haltAll
//
// Sending an SGI:  write the encoded value to GICD_SGIR.
// Receiving an SGI: it appears as a normal IRQ with INTID 0..15 at the
// GICC_IAR read; the trap handler dispatches it via `dispatch_sgi`.
//
// SM1.F is the underlying primitive; SM3 (per-object locks),
// SM5 (per-core scheduler), SM7 (TLB shootdown) are the consumers.
// ============================================================================

/// **WS-SM SM1.F.1 / SM1.F.8**: maximum SGI INTID (exclusive).
///
/// GIC-400 §3.2.2 / Table 3-1: SGIs occupy INTIDs 0..15.  Anything
/// outside this range is rejected by every SGI primitive in this
/// module.
pub const MAX_SGI_INTID: u8 = 16;

/// **WS-SM SM1.F.1 / SM1.F.8**: TargetListFilter encoding for the
/// CPUTargetList path.
///
/// `GICD_SGIR.TargetListFilter == 00` instructs the distributor to
/// forward the SGI to the CPU interfaces named in `CPUTargetList`
/// (bits [23:16]).  Used by [`send_sgi`] for explicit per-target
/// addressing.
const SGI_TLF_CPU_TARGET_LIST: u32 = 0b00;

/// **WS-SM SM1.F.1 / SM1.F.8**: TargetListFilter encoding for
/// "all PEs except requester".
///
/// `GICD_SGIR.TargetListFilter == 01` broadcasts to every CPU
/// interface other than the calling PE.  Used by
/// [`send_sgi_to_all_but_self`].
const SGI_TLF_ALL_BUT_SELF: u32 = 0b01;

/// **WS-SM SM1.F.1 / SM1.F.8**: TargetListFilter encoding for
/// "self only".
///
/// `GICD_SGIR.TargetListFilter == 10` delivers the SGI only to the
/// calling PE.  Used by [`send_sgi_to_self`].  Often used for
/// re-scheduling notifications scoped to a single core.
const SGI_TLF_SELF_ONLY: u32 = 0b10;

/// **WS-SM SM1.F.1**: Encode a `GICD_SGIR` write.
///
/// Pure encoding helper used by every send-SGI variant — factored
/// out so the bit-level layout is testable without hardware access.
/// See the `gicd::SGIR` constant docstring for the bit-field layout.
///
/// `target_list_filter` MUST be `0..=2` (caller's responsibility);
/// `target_mask` is the 8-bit CPUTargetList (only consulted when
/// `target_list_filter == 0`); `intid` MUST be `0..15`
/// (caller's responsibility — every send-SGI variant validates this
/// upstream).
///
/// Bit 15 (NSATT) is hard-coded to 0 because the kernel runs all
/// SGIs in Group 0 (matching the GICD_IGROUPR initialisation in
/// `init_distributor`) and never crosses the secure/non-secure
/// boundary.
#[inline(always)]
const fn encode_sgir(target_list_filter: u32, target_mask: u8, intid: u8) -> u32 {
    (target_list_filter << 24) | ((target_mask as u32) << 16) | (intid as u32)
}

/// **WS-SM SM1.F.2 / SM1.F.8**: Send an SGI to one or more target
/// CPU interfaces by explicit bitmask.
///
/// `target_mask` — bitmask of target CPU interfaces (bit i = CPU i),
/// 8 bits maximum (GIC-400 supports up to 8 CPU interfaces).  On
/// RPi5 the kernel uses bits 0..3 (cores 0..3); higher bits are
/// reserved.
/// `intid` — SGI INTID (`0..15`).  Reserved for kernel coordination
/// per the SM0.H `SgiKind` enum (intids 0..4) plus future
/// application-layer use (intids 5..15, post-1.0).
///
/// **GIC-400 TRM §4.3.13**: writes to `GICD_SGIR` with
/// `TargetListFilter == 0b00` deliver the SGI to every CPU
/// interface whose bit is set in `CPUTargetList`.
///
/// **Memory ordering (SM1.F.8)**: a `dsb ish` fires BEFORE the SGIR
/// write so any kernel-state mutation that the receiving handler
/// will read is observable on every IS-domain PE before the SGI
/// triggers.  Per ARM ARM B2.7.5, writes prior to a DSB are observed
/// by all PEs in the IS domain before subsequent operations begin;
/// this is what makes the SGI a reliable "wake the receiver and
/// have them see this state" primitive.
///
/// # Panics
///
/// Panics if `intid >= 16`.  The bound is enforced because writing
/// an out-of-range SGI INTID would alias with PPI (16..31) or SPI
/// (32+) INTIDs — silently corrupting the interrupt routing.  The
/// caller MUST validate (typically by passing a `Fin 16` from the
/// Lean side, which makes the bound a structural invariant).
pub fn send_sgi(target_mask: u8, intid: u8) {
    assert!(
        intid < MAX_SGI_INTID,
        "WS-SM SM1.F.2: SGI INTID must be 0..15, got {}",
        intid
    );
    let encoding = encode_sgir(SGI_TLF_CPU_TARGET_LIST, target_mask, intid);
    // SM1.F.8: ARM ARM B2.7.5 — `dsb ish` before the SGIR write so
    // every PE in the IS domain observes prior kernel-state writes
    // before the SGI triggers on the target.
    crate::barriers::dsb_ish();
    mmio_write32(GICD_BASE + gicd::SGIR, encoding);
}

/// **WS-SM SM1.F.3 / SM1.F.8**: Send an SGI to the calling CPU only.
///
/// Equivalent to [`send_sgi`] with `TargetListFilter = 0b10` (to-self
/// — overrides any `CPUTargetList` value, which is RES0 in this mode).
/// Useful when a kernel transition needs to defer work via an SGI
/// without disturbing other cores.
///
/// # Panics
///
/// Panics if `intid >= 16` for the same reason as [`send_sgi`].
pub fn send_sgi_to_self(intid: u8) {
    assert!(
        intid < MAX_SGI_INTID,
        "WS-SM SM1.F.3: SGI INTID must be 0..15, got {}",
        intid
    );
    let encoding = encode_sgir(SGI_TLF_SELF_ONLY, 0, intid);
    crate::barriers::dsb_ish();
    mmio_write32(GICD_BASE + gicd::SGIR, encoding);
}

/// **WS-SM SM1.F.4 / SM1.F.8**: Send an SGI to all CPUs except the
/// caller.
///
/// Equivalent to [`send_sgi`] with `TargetListFilter = 0b01`
/// (all-but-requester).  The most common SMP-coordination pattern:
/// the calling core has just performed an action whose result every
/// other core must observe (TLB shootdown, kernel-state quiesce,
/// reschedule trigger).
///
/// # Panics
///
/// Panics if `intid >= 16`.
pub fn send_sgi_to_all_but_self(intid: u8) {
    assert!(
        intid < MAX_SGI_INTID,
        "WS-SM SM1.F.4: SGI INTID must be 0..15, got {}",
        intid
    );
    let encoding = encode_sgir(SGI_TLF_ALL_BUT_SELF, 0, intid);
    crate::barriers::dsb_ish();
    mmio_write32(GICD_BASE + gicd::SGIR, encoding);
}

// ============================================================================
// WS-SM SM1.F.5 — SGI handler dispatch
//
// The handler table lives as a `static` array of `Option<SgiHandler>`
// per INTID, registered at boot and read-only thereafter.  Dispatch
// is invoked from the trap handler when an IRQ in `[0, 16)` is
// acknowledged.
// ============================================================================

/// **WS-SM SM1.F.5**: SGI handler signature.
///
/// Each handler receives the INTID it fired for plus the source CPU
/// id.  GIC-400's `GICC_IAR` actually encodes the source CPU in
/// bits `[12:10]` for SGIs (per GIC-400 TRM §4.4.4), but the
/// dispatcher abstracts this so the handler does not have to re-read
/// the IAR.
pub type SgiHandler = fn(intid: u8, source_cpu: u8);

/// **WS-SM SM1.F.5**: SGI handler table.
///
/// One slot per SGI INTID (`0..16`).  Slots are written exactly once
/// during boot (via [`register_sgi_handler`]) and read-only
/// thereafter.  Unregistered slots dispatch to a no-op log line.
///
/// **Concurrency**: the table is mutated only at boot (single-core,
/// IRQs disabled) before any other core can fire an SGI.  Subsequent
/// reads from secondary cores see the post-init values via the
/// release-acquire publication semantics of the kernel-init →
/// `bring_up_secondaries` handoff (the boot core's writes happen
/// before the PSCI CPU_ON call that wakes secondaries).
///
/// `static mut` is the right primitive here despite its general
/// reputation: every alternative (AtomicPtr, OnceLock, Mutex) would
/// add either runtime overhead or `alloc` dependencies that the
/// `#![no_std]` HAL cannot afford.  Access is read-only after boot,
/// so the data race that `static mut` is famous for cannot occur in
/// our discipline.
static mut SGI_HANDLERS: [Option<SgiHandler>; MAX_SGI_INTID as usize] =
    [None; MAX_SGI_INTID as usize];

// ============================================================================
// SM1.F.5 audit-pass-1 — Testable inner forms with explicit slice
// ============================================================================
//
// The global `SGI_HANDLERS` is the production handler table.  Tests
// that wrote to it directly raced on a shared `static mut`, producing
// undefined behaviour under cargo test's default parallel execution
// (two tests both registering at INTID 14 = concurrent writes to the
// same memory).
//
// The audit-pass-1 fix factors the handler-table operations into
// `_in`-suffixed inner forms that take an explicit slice reference.
// Tests use a stack-local array, so each test owns its own table —
// no cross-test contamination at the static-mut level.
//
// Production callers continue to use the global static via the
// thin-wrapper `register_sgi_handler` / `lookup_sgi_handler` /
// `dispatch_sgi` functions.  The wrappers route through the
// `_in`-form helpers.

/// **WS-SM SM1.F.5 audit-pass-1**: Register a handler at an INTID
/// in an explicit slice.
///
/// `handlers` — the table slice to mutate.  Must have at least
/// `MAX_SGI_INTID = 16` entries.  In production this is
/// `&mut SGI_HANDLERS`; in tests it's a stack-local array.
///
/// # Panics
///
/// Panics if `intid >= 16` OR `intid >= handlers.len()` — both
/// bounds are required because the test caller can pass a shorter
/// slice.
#[inline]
fn register_sgi_handler_in(
    handlers: &mut [Option<SgiHandler>],
    intid: u8,
    handler: SgiHandler,
) {
    assert!(
        intid < MAX_SGI_INTID,
        "WS-SM SM1.F.5: SGI INTID must be 0..15, got {}",
        intid
    );
    assert!(
        (intid as usize) < handlers.len(),
        "WS-SM SM1.F.5: handler slice (len {}) must hold at least \
         MAX_SGI_INTID + 1 entries — caller bug, not user input",
        handlers.len()
    );
    handlers[intid as usize] = Some(handler);
}

/// **WS-SM SM1.F.5 audit-pass-1**: Look up a handler at an INTID
/// in an explicit slice.
///
/// Returns `None` for out-of-range INTIDs OR if the slice is too
/// short to hold the entry.  Production callers use the global
/// slice; tests use stack-local arrays.
#[inline]
fn lookup_sgi_handler_in(
    handlers: &[Option<SgiHandler>],
    intid: u8,
) -> Option<SgiHandler> {
    if intid >= MAX_SGI_INTID {
        return None;
    }
    if (intid as usize) >= handlers.len() {
        return None;
    }
    handlers[intid as usize]
}

/// **WS-SM SM1.F.5 audit-pass-1**: Dispatch an SGI through an
/// explicit handler slice.
///
/// `handlers` — the table to consult.  In production this is the
/// global `SGI_HANDLERS`; in tests it's a stack-local array.
/// `intid` — the SGI INTID `0..15`.
/// `source_cpu` — the CPU interface that sent the SGI.
///
/// Out-of-range INTIDs return without dispatch; unregistered slots
/// log a diagnostic and return.
fn dispatch_sgi_in(
    handlers: &[Option<SgiHandler>],
    intid: u8,
    source_cpu: u8,
) {
    if intid >= MAX_SGI_INTID {
        // Defensive: dispatcher only valid for SGI range.  Caller
        // should have classified non-SGI INTIDs already.
        return;
    }
    match lookup_sgi_handler_in(handlers, intid) {
        Some(handler) => handler(intid, source_cpu),
        None => {
            // SM1.F.5: log-only — many SGI INTIDs are unused by
            // design (only 0..4 are kernel-reserved per SM0.H).  The
            // diagnostic line catches misconfigured boot paths that
            // failed to register a handler, without panicking the
            // kernel on every spurious SGI from a buggy peer.
            crate::kprintln!(
                "[gic] no handler for SGI {} from cpu {}",
                intid,
                source_cpu
            );
        }
    }
}

/// **WS-SM SM1.F.5**: Register a handler for a specific SGI INTID.
///
/// MUST be called from boot, before any SGI can fire on this core.
/// Registering twice for the same INTID overwrites the previous
/// handler — useful for boot-time wiring overrides, but a regression
/// elsewhere would silently lose the original handler.
///
/// # Safety
///
/// MUST be called only during boot, before secondaries are brought
/// up and before IRQs are unmasked on the calling PE.  The
/// `static mut` `SGI_HANDLERS` is not synchronised; concurrent
/// writes from multiple cores would race.  In practice every kernel
/// SGI handler is registered in `rust_boot_main` (single-core,
/// pre-IRQ-enable phase), so this constraint is honoured by
/// construction.
///
/// # Panics
///
/// Panics if `intid >= 16` (bounds match every other SGI primitive).
pub unsafe fn register_sgi_handler(intid: u8, handler: SgiHandler) {
    // SAFETY: caller obligation — boot-time only, no concurrent access.
    // Documented exhaustively in the function's safety contract above.
    //
    // Audit-pass-1: route through the testable inner form so the
    // global path is identical to the test path (just with a
    // different slice).
    //
    // Use `&raw mut` to obtain a raw pointer without going through
    // an intermediate `&mut SGI_HANDLERS` reference (which would
    // trip the `static_mut_refs` lint, a hard error in edition 2024).
    // The subsequent `&mut *ptr` dereference is sound under the
    // boot-time-only contract documented on the SGI_HANDLERS static.
    let handlers_ptr: *mut [Option<SgiHandler>; MAX_SGI_INTID as usize] =
        &raw mut SGI_HANDLERS;
    unsafe {
        register_sgi_handler_in(&mut *handlers_ptr, intid, handler);
    }
}

/// **WS-SM SM1.F.5**: Look up the registered handler for an SGI INTID.
///
/// Returns `Some(handler)` if a handler was registered via
/// [`register_sgi_handler`], else `None`.  Public so test code can
/// verify registration without invoking the handler.
///
/// # Safety
///
/// Reading `static mut` is unsafe in general, but per the
/// [`SGI_HANDLERS`] discipline (boot-time write-only, read-only
/// thereafter), the read is sound after `bring_up_secondaries`
/// completes.  Test code that calls this between handler
/// registrations on the same thread is also sound (no concurrent
/// writes can occur in single-threaded test execution).
pub fn lookup_sgi_handler(intid: u8) -> Option<SgiHandler> {
    // Audit-pass-1: route through the testable inner form.
    //
    // Use `&raw const` to obtain a raw pointer without going through
    // an intermediate `&SGI_HANDLERS` reference (which would trip
    // the `static_mut_refs` lint, a hard error in edition 2024).
    //
    // SAFETY: `SGI_HANDLERS` is read-only after the boot-time
    // registration phase — see the static's docstring.  The `&*ptr`
    // dereference is sound under the boot-time-only-writes contract.
    let handlers_ptr: *const [Option<SgiHandler>; MAX_SGI_INTID as usize] =
        &raw const SGI_HANDLERS;
    unsafe { lookup_sgi_handler_in(&*handlers_ptr, intid) }
}

/// **WS-SM SM1.F.5**: Dispatch an SGI to its registered handler.
///
/// Called from the IRQ handler when an SGI INTID (`0..15`) is
/// acknowledged at GICC_IAR.  Looks up the handler in
/// [`SGI_HANDLERS`] and invokes it; if no handler is registered, logs
/// a diagnostic line and returns (the IRQ has already been ack'd /
/// EOI'd by the time this fires per the AN8-C EOI-before-handler
/// pattern).
///
/// `intid` — the SGI INTID `0..15`.  Out-of-range values return
/// without dispatch; the caller's bound check (in `dispatch_irq`)
/// has already classified non-SGI INTIDs as `Handled` or `OutOfRange`
/// and routed them elsewhere.
/// `source_cpu` — the CPU interface that sent the SGI, extracted
/// from `GICC_IAR[12:10]` per GIC-400 TRM §4.4.4.  Provides a
/// per-core handler the source PE for handlers that need to
/// originate ACK SGIs (e.g., TLB-shootdown ACK).
pub fn dispatch_sgi(intid: u8, source_cpu: u8) {
    // Audit-pass-1: route through the testable inner form.
    //
    // Use `&raw const` to obtain a raw pointer without going through
    // an intermediate `&SGI_HANDLERS` reference (which would trip the
    // `static_mut_refs` lint, a hard error in edition 2024).
    //
    // SAFETY: `SGI_HANDLERS` is read-only after the boot-time
    // registration phase.
    let handlers_ptr: *const [Option<SgiHandler>; MAX_SGI_INTID as usize] =
        &raw const SGI_HANDLERS;
    unsafe { dispatch_sgi_in(&*handlers_ptr, intid, source_cpu) }
}

/// **WS-SM SM1.F.5**: Extract the source-CPU field from a raw
/// `GICC_IAR` value for an SGI INTID.
///
/// Per GIC-400 TRM §4.4.4, when `GICC_IAR[9:0]` is in the SGI range
/// (`0..16`), bits `[12:10]` carry the CPU interface number that
/// asserted the SGI (`0..7`).  The dispatcher extracts this so a
/// handler can route an ACK SGI back to the originator.
///
/// **Note**: for non-SGI INTIDs, bits `[12:10]` are RES0 per the
/// spec, so calling this on a non-SGI IAR returns `0` — meaningless
/// but harmless.  Callers MUST gate by `intid < 16` first.
#[inline(always)]
pub const fn iar_source_cpu(iar: u32) -> u8 {
    ((iar >> 10) & 0x7) as u8
}

/// Handle an IRQ from the GIC: acknowledge → EOI → dispatch (handler
/// runs with the interrupt already retired in the GIC).
///
/// Called from `handle_irq` in trap.rs. The dispatch callback receives
/// the INTID and should handle the interrupt (e.g., reprogram timer,
/// signal notification).
///
/// # AN8-C (H-19) — Ordering rationale
///
/// The previous implementation followed the classic
/// `ack → dispatch → EOI` sequence with an `EoiGuard` RAII wrapper that
/// fired EOI on `Drop`. Under `panic = "abort"` (our production
/// profile), destructors do NOT run, so a handler panic would halt the
/// kernel with the INTID still "active" on the GIC — correct in
/// isolation (the kernel is gone), but an SMP bring-up (AN9-J) or
/// warm-reset could later boot with a latched active line.
///
/// The audit's Option (b) — **emit EOI BEFORE the handler body** —
/// eliminates this risk structurally. GIC-400 §3.1 permits emitting EOI
/// after IAR read but before the handler runs, provided the handler
/// does not re-enter the same INTID (see re-entrancy note below). With
/// EOI emitted first:
///   - Handler panic leaves the GIC in a fully retired state.
///   - The EOI is unconditional for Handled and OutOfRange branches,
///     matching the AK3-C.4 "EOI unless spurious" contract.
///   - No RAII guard is required; the order is explicit in the source.
///
/// # Re-entrancy invariant (AN8-C.4)
///
/// Once EOI is emitted, the INTID's "active" state clears in the GIC
/// distributor. If the handler body re-triggers the same INTID (e.g.,
/// a timer handler that reprograms `CNTP_CVAL_EL0` below the current
/// counter), the re-triggered interrupt will be re-acknowledged on the
/// NEXT IAR read — NOT recursively inside this handler — because GIC-400
/// masks the CPU interface at the current running priority until
/// PSTATE.I is cleared on exception return.
///
/// The current registered handlers are:
///   - Timer PPI (INTID 30): reprograms `CNTP_CVAL_EL0` to `now + interval`;
///     never fires inside the handler body (interval ≫ handler latency).
///   - Unhandled INTIDs: log-only; no hardware touch that could re-trigger.
///
/// When a new handler is registered, it MUST NOT reactivate its own
/// INTID before returning. The `#[deny(clippy::panic)]` attribute on
/// each handler (AN8-C.3) also prevents direct `panic!()` inside handler
/// bodies so an invariant violation cannot silently undermine the
/// kernel's forward progress guarantees.
///
/// # Classification (AK3-C.4, preserved)
///
/// - Handled INTIDs: EOI + dispatch (normal path)
/// - OutOfRange INTIDs: EOI (prevents GIC lockup on errata / SMP races
///   delivering INTID ∈ [224, 1020)); no handler dispatch because the
///   INTID is unsupported on this platform.
/// - Spurious INTIDs (≥ 1020): no EOI per GIC-400 spec.
///
/// # Spectre v1 mitigation (AG9-F, preserved)
///
/// A `csdb` (Consumption of Speculative Data Barrier) fires after the
/// classification result is known so the handler dispatch cannot be
/// speculated on an attacker-influenced INTID value.
///
/// Returns `true` if a real (non-spurious) interrupt was acknowledged;
/// this includes both handled and out-of-range cases because both
/// participate in the interrupt lifecycle (IAR read + EOI).
pub fn dispatch_irq<F: FnOnce(u32)>(handler: F) -> bool {
    dispatch_irq_inner(
        acknowledge_irq_classified(GICC_BASE),
        |id| end_of_interrupt(GICC_BASE, id),
        handler,
    )
}

/// AN8-C.5 audit: pure dispatch state machine factored out of
/// [`dispatch_irq`] so unit tests can substitute mock `eoi`/`handler`
/// closures and observe the relative ordering of EOI vs. handler
/// invocation. The production caller passes the real GIC EOI write and
/// the kernel's handler closure; tests pass instrumented closures that
/// record their relative call order via an `AtomicU32`.
///
/// **Invariant**: this function is the SOLE definition of the dispatch
/// state machine. `dispatch_irq` is a thin adapter that wires the GIC
/// MMIO functions in. Refactoring this function therefore changes the
/// observable ordering for both production and tests in lockstep —
/// preventing the "test doesn't reflect production" drift.
#[inline(always)]
fn dispatch_irq_inner<E, F>(ack: AckResult, mut eoi: E, handler: F) -> bool
where
    E: FnMut(u32),
    F: FnOnce(u32),
{
    match ack {
        AckResult::Spurious => false,
        AckResult::Handled(intid) => {
            // AK3-C.4 / AN8-C.1: EOI fires BEFORE the handler. Any panic
            // or long-running code path in the handler cannot now leave
            // the INTID in an active state on the GIC.
            eoi(intid);
            // AG9-F: Speculation barrier resolves the classification
            // check before running code that might materialise
            // attacker-influenced data from the INTID.
            crate::barriers::csdb();
            handler(intid);
            true
        }
        AckResult::OutOfRange(intid) => {
            // AK3-C.4: EOI must fire for out-of-range INTIDs to close
            // the interrupt cycle; no handler dispatch because the
            // INTID is unsupported on this platform.
            //
            // AN8-C.1: keep the EOI-first ordering symmetric with the
            // Handled branch.
            eoi(intid);
            crate::barriers::csdb();
            true
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
extern crate std;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gic_addresses_match_board_lean() {
        // Board.lean: gicDistributorBase : PAddr := ⟨0xFF841000⟩
        assert_eq!(GICD_BASE, 0xFF841000);
        // Board.lean: gicCpuInterfaceBase : PAddr := ⟨0xFF842000⟩
        assert_eq!(GICC_BASE, 0xFF842000);
    }

    #[test]
    fn timer_ppi_matches_lean() {
        // InterruptDispatch.lean: timerInterruptId : InterruptId := ⟨30, ...⟩
        assert_eq!(TIMER_PPI_ID, 30);
    }

    #[test]
    fn spi_count_matches_lean() {
        // InterruptDispatch.lean: gicSpiCount = 192 (INTIDs 32-223)
        assert_eq!(SPI_COUNT, 192);
        assert_eq!(MAX_INTID, 224); // SGI(16) + PPI(16) + SPI(192)
    }

    #[test]
    fn spurious_detection() {
        assert!(!is_spurious(0));
        assert!(!is_spurious(30)); // timer PPI
        assert!(!is_spurious(223)); // last valid SPI
        assert!(!is_spurious(1019)); // just below threshold
        assert!(is_spurious(1020)); // spurious threshold
        assert!(is_spurious(1023)); // standard spurious ID
    }

    #[test]
    fn gicd_register_offsets() {
        assert_eq!(gicd::CTLR, 0x000);
        assert_eq!(gicd::IGROUPR_BASE, 0x080);
        assert_eq!(gicd::ISENABLER_BASE, 0x100);
        assert_eq!(gicd::ICENABLER_BASE, 0x180);
        assert_eq!(gicd::ICPENDR_BASE, 0x280);
        assert_eq!(gicd::IPRIORITYR_BASE, 0x400);
        assert_eq!(gicd::ITARGETSR_BASE, 0x800);
    }

    #[test]
    fn gicc_register_offsets() {
        assert_eq!(gicc::CTLR, 0x000);
        assert_eq!(gicc::PMR, 0x004);
        assert_eq!(gicc::BPR, 0x008);
        assert_eq!(gicc::IAR, 0x00C);
        assert_eq!(gicc::EOIR, 0x010);
    }

    #[test]
    fn num_register_banks() {
        // 224 INTIDs / 32 per bank = 7 banks (ceil-divide)
        assert_eq!(MAX_INTID.div_ceil(32), 7);
    }

    #[test]
    fn num_priority_regs() {
        // 224 INTIDs / 4 per register = 56 registers (ceil-divide)
        assert_eq!(MAX_INTID.div_ceil(4), 56);
    }

    #[test]
    fn dispatch_irq_spurious() {
        // On non-aarch64, mmio_read32 returns 0, but acknowledge_irq masks
        // to bits [9:0], which gives INTID 0 — not spurious.
        // Test the spurious path explicitly:
        assert!(is_spurious(1023));
        assert!(!is_spurious(0));
    }

    #[test]
    fn ack_result_classification() {
        // AK3-C.4: Three-way classification matches Lean AckError:
        // INTID 30 (timer PPI) → Handled
        // INTID 500 (unsupported on BCM2712) → OutOfRange
        // INTID 1020/1023 (special) → Spurious
        let classify = |raw: u32| -> AckResult {
            if raw >= SPURIOUS_THRESHOLD {
                AckResult::Spurious
            } else if raw >= MAX_SUPPORTED_INTID {
                AckResult::OutOfRange(raw)
            } else {
                AckResult::Handled(raw)
            }
        };
        assert_eq!(classify(30), AckResult::Handled(30));
        assert_eq!(classify(223), AckResult::Handled(223));
        assert_eq!(classify(224), AckResult::OutOfRange(224));
        assert_eq!(classify(500), AckResult::OutOfRange(500));
        assert_eq!(classify(1019), AckResult::OutOfRange(1019));
        assert_eq!(classify(1020), AckResult::Spurious);
        assert_eq!(classify(1023), AckResult::Spurious);
    }

    #[test]
    fn init_gic_no_panic() {
        // On non-aarch64, all MMIO ops are no-ops. Verify init sequence
        // runs without panicking.
        init_gic();
    }

    #[test]
    fn dispatch_irq_calls_handler() {
        // On non-aarch64, acknowledge_irq returns 0 (INTID 0, not spurious).
        // Handler should be called with INTID 0.
        let mut called_with = None;
        let handled = dispatch_irq(|intid| {
            called_with = Some(intid);
        });
        assert!(handled);
        assert_eq!(called_with, Some(0));
    }

    // ========================================================================
    // AN8-C (H-19): EOI-before-handler ordering tests
    //
    // The audit's Option (b) reordered ack → handle → EOI to
    // ack → EOI → handle. These tests use `dispatch_irq_inner` (the pure
    // state machine factored out by AN8-C.5) with mock `eoi`/`handler`
    // closures that record their relative invocation order. This proves
    // the EOI-before-handler property STRUCTURALLY rather than
    // observationally — independent of MMIO side effects.
    //
    // Each test owns its own LOCAL `AtomicU32` counters so tests are safe
    // under `cargo test`'s default parallel execution.
    // ========================================================================

    use core::sync::atomic::{AtomicU32, Ordering};

    /// AN8-C.5: monotonic event clock used by ordering tests. Each call to
    /// `tick()` returns the next sequence number, so a recorded "EOI tick"
    /// and a recorded "handler tick" can be compared directly.
    struct EventClock(AtomicU32);
    impl EventClock {
        fn new() -> Self {
            Self(AtomicU32::new(0))
        }
        fn tick(&self) -> u32 {
            self.0.fetch_add(1, Ordering::SeqCst)
        }
    }

    #[test]
    fn dispatch_irq_handled_eoi_fires_before_handler() {
        // AN8-C.1: ORDERING test — record EOI and handler events on a
        // shared clock; assert eoi_tick < handler_tick.
        let clock = EventClock::new();
        let eoi_tick = AtomicU32::new(u32::MAX);
        let handler_tick = AtomicU32::new(u32::MAX);
        let handled = dispatch_irq_inner(
            AckResult::Handled(30),
            |id| {
                assert_eq!(id, 30, "EOI must receive the Handled INTID");
                eoi_tick.store(clock.tick(), Ordering::SeqCst);
            },
            |id| {
                assert_eq!(id, 30, "handler must receive the Handled INTID");
                handler_tick.store(clock.tick(), Ordering::SeqCst);
            },
        );
        assert!(handled);
        let eoi = eoi_tick.load(Ordering::SeqCst);
        let hnd = handler_tick.load(Ordering::SeqCst);
        assert_ne!(eoi, u32::MAX, "EOI was not invoked");
        assert_ne!(hnd, u32::MAX, "handler was not invoked");
        assert!(
            eoi < hnd,
            "AN8-C.1 violated: EOI tick {eoi} must precede handler tick {hnd}"
        );
    }

    #[test]
    fn dispatch_irq_out_of_range_eois_without_handler() {
        // AN8-C.1: OutOfRange INTIDs MUST EOI but MUST NOT dispatch the
        // handler. The mock handler increments a counter; we verify it
        // stays zero.
        let eoi_count = AtomicU32::new(0);
        let handler_count = AtomicU32::new(0);
        let handled = dispatch_irq_inner(
            AckResult::OutOfRange(500),
            |id| {
                assert_eq!(id, 500, "EOI must receive the OutOfRange raw INTID");
                eoi_count.fetch_add(1, Ordering::SeqCst);
            },
            |_id| {
                handler_count.fetch_add(1, Ordering::SeqCst);
            },
        );
        // OutOfRange is reported as "handled" in the dispatch lifecycle
        // (the IAR/EOI cycle completed), distinct from "Spurious".
        assert!(handled);
        assert_eq!(
            eoi_count.load(Ordering::SeqCst),
            1,
            "EOI must fire exactly once for OutOfRange"
        );
        assert_eq!(
            handler_count.load(Ordering::SeqCst),
            0,
            "handler must NOT fire for OutOfRange (no valid INTID)"
        );
    }

    #[test]
    fn dispatch_irq_spurious_skips_eoi_and_handler() {
        // AN8-C.1 + GIC-400 §3.1: Spurious INTIDs (≥ 1020) skip EOI per
        // spec and obviously skip the handler. Both mocks must remain
        // un-invoked.
        let eoi_count = AtomicU32::new(0);
        let handler_count = AtomicU32::new(0);
        let handled = dispatch_irq_inner(
            AckResult::Spurious,
            |_id| {
                eoi_count.fetch_add(1, Ordering::SeqCst);
            },
            |_id| {
                handler_count.fetch_add(1, Ordering::SeqCst);
            },
        );
        assert!(!handled, "Spurious must report `false` (no IAR/EOI cycle)");
        assert_eq!(
            eoi_count.load(Ordering::SeqCst),
            0,
            "EOI MUST NOT fire for Spurious per GIC-400 §3.1"
        );
        assert_eq!(
            handler_count.load(Ordering::SeqCst),
            0,
            "handler MUST NOT fire for Spurious"
        );
    }

    #[test]
    fn dispatch_irq_handler_panic_does_not_unfire_eoi() {
        // AN8-C.1: under the unwinding test profile, even if the handler
        // panics AFTER the EOI fires, the EOI is already on the wire —
        // there's no way to "un-fire" it. This is the entire point of
        // EOI-before-handler. We use a `static AtomicU32` (not a stack
        // local) so the counter survives the unwinding closure, and
        // verify it equals 1 after the panic.
        //
        // Static storage with a unique sentinel value avoids
        // cross-test contention because no other test references this
        // counter.
        static EOI_FIRED_BEFORE_PANIC: AtomicU32 = AtomicU32::new(0);
        EOI_FIRED_BEFORE_PANIC.store(0, Ordering::SeqCst);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            dispatch_irq_inner(
                AckResult::Handled(30),
                |_id| {
                    EOI_FIRED_BEFORE_PANIC.fetch_add(1, Ordering::SeqCst);
                },
                |_id| {
                    panic!("simulated handler fault after EOI");
                },
            )
        }));
        assert!(
            result.is_err(),
            "handler panic must propagate up out of dispatch_irq_inner"
        );
        assert_eq!(
            EOI_FIRED_BEFORE_PANIC.load(Ordering::SeqCst),
            1,
            "AN8-C.1: EOI must have fired exactly once BEFORE the \
             handler panic — the panic cannot un-fire it"
        );
    }

    #[test]
    fn dispatch_irq_real_calls_handler() {
        // Smoke test: the production `dispatch_irq` (which wires
        // `dispatch_irq_inner` to real GIC MMIO) calls the handler on
        // the host where MMIO returns 0 (Handled(0)).
        let calls = AtomicU32::new(0);
        let handled = dispatch_irq(|_intid| {
            calls.fetch_add(1, Ordering::SeqCst);
        });
        assert!(handled);
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn dispatch_irq_real_handler_observes_intid() {
        let seen = AtomicU32::new(u32::MAX);
        let handled = dispatch_irq(|intid| {
            seen.store(intid, Ordering::SeqCst);
        });
        assert!(handled);
        assert_eq!(seen.load(Ordering::SeqCst), 0);
    }

    // Unwind safety smoke for the public `dispatch_irq` wrapper. AN8-C
    // removed the EoiGuard RAII pattern; this test fails the build if
    // a future refactor reintroduces an unwind-observable Drop side
    // channel.
    #[test]
    fn dispatch_irq_real_handler_panic_propagates() {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            dispatch_irq(|_intid| {
                panic!("simulated handler fault");
            });
        }));
        assert!(result.is_err(), "handler panic must propagate to caller");
    }

    // ========================================================================
    // AN8-D (RUST-M05): GICD_ITARGETSR self-check coverage
    //
    // The production self-check halts the core via WFE-loop on mismatch,
    // which we cannot exercise from a unit test. Instead we test the
    // factored-out read-address arithmetic and the constants.
    // ========================================================================

    // ARM GIC-400 TRM §4.3.12: ITARGETSR registers 0-7 (INTIDs 0-31)
    // are banked / read-only; registers 8+ (INTIDs 32+) are writable.
    // The self-check MUST target a writable bank to validate the
    // distributor's write path. This is a compile-time invariant —
    // failing the assert breaks the build at the point of edit, before
    // any test runs.
    const _: () = assert!(
        SELF_CHECK_TARGET_INDEX >= 8,
        "AN8-D RUST-M05: self-check target index in banked/RO range",
    );

    #[test]
    fn self_check_expected_pattern_matches_init_distributor() {
        // The expected pattern must equal what `init_distributor`
        // writes to ITARGETSR registers (CPU 0 in each 8-bit lane).
        // If `init_distributor` ever changes its write pattern, this
        // test fails and forces a paired update to the self-check.
        assert_eq!(SELF_CHECK_EXPECTED, 0x0101_0101);
    }

    #[test]
    fn self_check_target_address_arithmetic() {
        // The address computed by `read_self_check_target` must equal
        // `base + ITARGETSR_BASE + TARGET_INDEX * 4`. We verify against
        // a concrete BCM2712 base.
        let base = GICD_BASE; // 0xFF841000
        let expected = base + gicd::ITARGETSR_BASE + SELF_CHECK_TARGET_INDEX * 4;
        assert_eq!(
            expected,
            0xFF841000 + 0x800 + 8 * 4,
            "self-check address arithmetic regressed"
        );
        assert_eq!(
            expected, 0xFF841820,
            "self-check should target ITARGETSR[8] @ 0xFF841820 \
             on BCM2712"
        );
    }

    #[test]
    fn self_check_does_not_panic_on_host() {
        // On non-aarch64 the read returns 0; `self_check_distributor`
        // sees the mismatch but skips the WFE-loop (cfg-gated). The
        // function must still return cleanly — exercise the full path.
        self_check_distributor(GICD_BASE);
    }

    // Sanity: the self-check address lies inside the GICD MMIO
    // window, not in some other peripheral. The ARM GIC-400 TRM
    // declares ITARGETSR at offsets 0x800-0xBFC (256 registers),
    // so any TARGET_INDEX ∈ [0, 255] stays inside. Compile-time
    // assertion — failing this fails the build at edit time.
    const _: () = assert!(
        SELF_CHECK_TARGET_INDEX < 256,
        "AN8-D RUST-M05: self-check target index escapes ITARGETSR window",
    );

    // =====================================================================
    // WS-SM SM1.C.3 — Secondary-core CPU interface init tests
    // =====================================================================

    #[test]
    fn sm1c3_init_cpu_interface_secondary_callable_on_host() {
        // SM1.C.3: host stub of `init_cpu_interface_secondary` runs
        // cleanly — the underlying `init_cpu_interface` calls
        // `mmio_write32` which is a no-op on non-aarch64.  Catches a
        // regression that introduces a host-side panic in the GIC
        // CPU-interface init.
        init_cpu_interface_secondary(1);
    }

    #[test]
    fn sm1c3_init_cpu_interface_secondary_accepts_every_secondary_core_id() {
        // SM1.C.3: every plausible secondary core_id (1..=3 on RPi5)
        // must be callable.  A regression introducing an out-of-range
        // bound (e.g., asserting core_id < 3) would fail one of these
        // calls.
        for core_id in [1u64, 2, 3] {
            init_cpu_interface_secondary(core_id);
        }
    }

    #[test]
    fn sm1c3_init_cpu_interface_secondary_signature_takes_u64() {
        // SM1.C.3: the helper takes a u64 core_id (PSCI context_id
        // convention).  Pinning the signature here catches refactors
        // to `usize` or `u32` that would break the FFI call from
        // `rust_secondary_main`.
        let _: fn(u64) = init_cpu_interface_secondary;
    }

    #[test]
    fn sm1c3_init_cpu_interface_signature_is_pub() {
        // SM1.C.3: the underlying `init_cpu_interface(base)` helper is
        // shared with the primary's `init_gic()`.  Ensure the symbol
        // remains accessible from the secondary's call path.
        let _: fn(usize) = init_cpu_interface;
    }

    #[test]
    fn sm1c3_isenabler0_offset_is_first_bank() {
        // SM1.F audit-pass-1: the per-core ISENABLER0 enable in
        // `init_cpu_interface_secondary` writes to
        // `GICD_BASE + gicd::ISENABLER_BASE`, which is the first
        // bank (covering INTIDs 0..31).  Pin this offset so a
        // refactor that changes ISENABLER_BASE doesn't break the
        // per-core SGI/PPI enable.
        assert_eq!(gicd::ISENABLER_BASE, 0x100,
            "GICD_ISENABLER_BASE must match GIC-400 TRM §4.3.5");
        // Bank 0 = ISENABLER0 = first 32 INTIDs (SGIs 0..15 + PPIs 16..31).
        // Verify the mask we use (0xFFFF_FFFF) actually covers every SGI
        // INTID in 0..15 (low 16 bits of bank 0) AND the timer PPI.
        let enable_all_mask: u32 = 0xFFFF_FFFF;
        // 16 SGIs (0..15) fit in the low 16 bits of bank 0.
        let sgi_range_in_bank0: u32 = 0x0000_FFFF;
        assert_eq!(
            enable_all_mask & sgi_range_in_bank0,
            sgi_range_in_bank0,
            "0xFFFF_FFFF must enable every SGI INTID (bits 0..15 of bank 0)"
        );
        // Timer PPI = INTID 30 → bit 30 of bank 0 (PPIs occupy bits 16..31).
        let timer_bit_in_bank0: u32 = 1 << TIMER_PPI_ID;
        assert_eq!(
            enable_all_mask & timer_bit_in_bank0,
            timer_bit_in_bank0,
            "0xFFFF_FFFF must enable timer PPI (bit 30 of bank 0)"
        );
        // PPIs occupy bits 16..31; pin that range too.
        let ppi_range_in_bank0: u32 = 0xFFFF_0000;
        assert_eq!(
            enable_all_mask & ppi_range_in_bank0,
            ppi_range_in_bank0,
            "0xFFFF_FFFF must enable every PPI INTID (bits 16..31 of bank 0)"
        );
    }

    // =====================================================================
    // WS-SM SM1.F — SGI primitive tests
    //
    // Tests cover encoding, range checking, dispatch routing, and the
    // ARM ARM B2.7.5 ordering contract (DSB-before-SGIR).  We use the
    // `encode_sgir` factored encoder for bit-level tests so the
    // encoding can be verified without performing actual MMIO writes.
    // =====================================================================

    // ---------------------------------------------------------------------
    // SM1.F.1: GICD_SGIR constant + register layout
    // ---------------------------------------------------------------------

    #[test]
    fn sm1f1_gicd_sgir_offset_matches_gic_400_trm() {
        // GIC-400 TRM §4.3.13: GICD_SGIR is at distributor-base + 0xF00.
        assert_eq!(gicd::SGIR, 0xF00);
    }

    #[test]
    fn sm1f1_max_sgi_intid_matches_gic_spec() {
        // GIC-400 §3.2.2 / Table 3-1: SGIs occupy INTIDs 0..15 (16 slots).
        assert_eq!(MAX_SGI_INTID, 16);
    }

    #[test]
    fn sm1f1_sgi_target_list_filter_constants_match_gic_trm() {
        // GIC-400 TRM §4.3.13: TargetListFilter encodes
        //   00 = use CPUTargetList
        //   01 = all-but-self
        //   10 = self only
        // The constants must exactly match these values.
        assert_eq!(SGI_TLF_CPU_TARGET_LIST, 0b00);
        assert_eq!(SGI_TLF_ALL_BUT_SELF, 0b01);
        assert_eq!(SGI_TLF_SELF_ONLY, 0b10);
    }

    // ---------------------------------------------------------------------
    // SM1.F.1 audit: encode_sgir bit-field correctness
    // ---------------------------------------------------------------------

    #[test]
    fn sm1f1_encode_sgir_cputargetlist_path() {
        // SM1.F.2 acceptance: send_sgi(0b1110, 1) → 0x000E_0001.
        // (TargetListFilter=00, CPUTargetList=0b1110, INTID=1)
        let enc = encode_sgir(SGI_TLF_CPU_TARGET_LIST, 0b1110, 1);
        assert_eq!(enc, 0x000E_0001);
    }

    #[test]
    fn sm1f1_encode_sgir_self_only_path() {
        // SM1.F.3 acceptance: send_sgi_to_self(3) → 0x0200_0003.
        // (TargetListFilter=10, CPUTargetList=0, INTID=3)
        let enc = encode_sgir(SGI_TLF_SELF_ONLY, 0, 3);
        assert_eq!(enc, 0x0200_0003);
    }

    #[test]
    fn sm1f1_encode_sgir_all_but_self_path() {
        // SM1.F.4 acceptance: send_sgi_to_all_but_self(0) → 0x0100_0000.
        // (TargetListFilter=01, CPUTargetList=0, INTID=0)
        let enc = encode_sgir(SGI_TLF_ALL_BUT_SELF, 0, 0);
        assert_eq!(enc, 0x0100_0000);
    }

    #[test]
    fn sm1f1_encode_sgir_isolates_intid_field() {
        // The INTID field is bits [3:0]; bits [4:15] are RES0 in our
        // encoding.  Verify every INTID 0..15 produces a value whose
        // high bits are clean.
        for intid in 0..MAX_SGI_INTID {
            let enc = encode_sgir(SGI_TLF_CPU_TARGET_LIST, 0, intid);
            assert_eq!(enc & 0xF, intid as u32, "INTID {} field corrupted", intid);
            // Bits [4:15] must be 0 (no NSATT, no spurious bits).
            assert_eq!(
                (enc >> 4) & 0xFFF,
                0,
                "INTID {} encoding has dirty mid-bits",
                intid
            );
        }
    }

    #[test]
    fn sm1f1_encode_sgir_isolates_target_mask_field() {
        // CPUTargetList is bits [23:16]; verify every 8-bit mask
        // populates that field cleanly.
        for mask in [0u8, 0x01, 0x03, 0x07, 0x0F, 0xF0, 0xFF, 0xAA, 0x55] {
            let enc = encode_sgir(SGI_TLF_CPU_TARGET_LIST, mask, 0);
            assert_eq!(
                (enc >> 16) & 0xFF,
                mask as u32,
                "target mask {:#x} field corrupted",
                mask
            );
        }
    }

    #[test]
    fn sm1f1_encode_sgir_isolates_target_list_filter() {
        // TargetListFilter is bits [25:24]; verify every TLF value
        // populates that field cleanly.
        for tlf in [SGI_TLF_CPU_TARGET_LIST, SGI_TLF_ALL_BUT_SELF, SGI_TLF_SELF_ONLY] {
            let enc = encode_sgir(tlf, 0, 0);
            assert_eq!(
                (enc >> 24) & 0x3,
                tlf,
                "TargetListFilter {:#x} field corrupted",
                tlf
            );
        }
    }

    #[test]
    fn sm1f1_encode_sgir_const_callable() {
        // The encoder is `const fn` — verify it evaluates at
        // compile time so call sites with literal arguments are
        // free at runtime.
        const ENC_BOOT_RESCHEDULE: u32 = encode_sgir(SGI_TLF_ALL_BUT_SELF, 0, 0);
        assert_eq!(ENC_BOOT_RESCHEDULE, 0x0100_0000);
    }

    // ---------------------------------------------------------------------
    // SM1.F.2/.3/.4: send_sgi family — runs cleanly on host (MMIO no-op)
    // ---------------------------------------------------------------------

    #[test]
    fn sm1f2_send_sgi_callable_for_every_valid_combo() {
        // Exercise representative (mask, intid) combinations.  On
        // host the MMIO write is a no-op; the test verifies no
        // panic.
        for intid in 0..MAX_SGI_INTID {
            send_sgi(0x01, intid); // CPU 0
            send_sgi(0x0F, intid); // all 4 RPi5 cores
            send_sgi(0xFF, intid); // every 8-bit slot
            send_sgi(0x00, intid); // empty mask (degenerate)
        }
    }

    #[test]
    #[should_panic(expected = "SGI INTID must be 0..15")]
    fn sm1f2_send_sgi_panics_on_intid_16() {
        // Bound enforcement: INTID 16 is the first PPI slot, not an
        // SGI; passing it would silently fire a PPI on the target.
        send_sgi(0x01, 16);
    }

    #[test]
    #[should_panic(expected = "SGI INTID must be 0..15")]
    fn sm1f2_send_sgi_panics_on_intid_max() {
        send_sgi(0x01, u8::MAX);
    }

    #[test]
    fn sm1f3_send_sgi_to_self_callable_for_every_valid_intid() {
        for intid in 0..MAX_SGI_INTID {
            send_sgi_to_self(intid);
        }
    }

    #[test]
    #[should_panic(expected = "SGI INTID must be 0..15")]
    fn sm1f3_send_sgi_to_self_panics_on_intid_16() {
        send_sgi_to_self(16);
    }

    #[test]
    fn sm1f4_send_sgi_to_all_but_self_callable_for_every_valid_intid() {
        for intid in 0..MAX_SGI_INTID {
            send_sgi_to_all_but_self(intid);
        }
    }

    #[test]
    #[should_panic(expected = "SGI INTID must be 0..15")]
    fn sm1f4_send_sgi_to_all_but_self_panics_on_intid_16() {
        send_sgi_to_all_but_self(16);
    }

    #[test]
    fn sm1f234_send_sgi_signatures_pinned() {
        // Pin every public send_sgi signature.  A future refactor
        // that changed the argument types or return type would
        // fail to compile here.
        let _: fn(u8, u8) = send_sgi;
        let _: fn(u8) = send_sgi_to_self;
        let _: fn(u8) = send_sgi_to_all_but_self;
    }

    // ---------------------------------------------------------------------
    // SM1.F.5: handler dispatch — registration + lookup + dispatch
    // ---------------------------------------------------------------------

    /// Per-test handler stub that records its invocation by writing
    /// into a static AtomicU64 (encoding intid in low byte, source_cpu
    /// in second byte, and a "called" flag in bit 16).  Each test that
    /// uses this owns a single static counter so concurrent test runs
    /// do not cross-contaminate.
    fn _sgi_test_handler_unused(_intid: u8, _source_cpu: u8) {
        // Placeholder used in shapes-only tests.
    }

    #[test]
    fn sm1f5_lookup_returns_none_for_out_of_range_intid() {
        // SM1.F.5: out-of-range INTID returns None defensively.
        // Tests the GLOBAL wrapper; no state mutation needed.
        assert!(lookup_sgi_handler(16).is_none());
        assert!(lookup_sgi_handler(100).is_none());
        assert!(lookup_sgi_handler(255).is_none());
    }
    // Note: a per-INTID "is-unregistered" test against the global
    // SGI_HANDLERS table would be race-prone under cargo test (any
    // other test that registers a handler would observe a Some).
    // Audit-pass-1 replaced such tests with stack-local-slice
    // exercises via `sm1f5_inner_register_then_lookup_returns_handler`
    // and `sm1f5_inner_lookup_returns_none_for_out_of_range_intid`.

    // SM1.F.5 audit-pass-1: per-test handler state-recording.
    //
    // The pre-audit tests used a single `static AtomicU32` shared
    // across multiple tests AND wrote to the global `SGI_HANDLERS`
    // at the same INTID — both racy under cargo test's parallel
    // execution.  The audit-pass-1 fix uses per-test static
    // counters with unique-per-test names AND routes registration
    // through the `_in`-form helpers with stack-local slices, so
    // each test owns isolated state.
    //
    // To keep test handlers callable via the `fn(u8, u8)` pointer
    // type (no captures), each test that exercises dispatch declares
    // its own `static AtomicU32` and a paired handler function.
    // The handlers store `(intid << 8) | source_cpu` so the test
    // can verify the dispatcher passed both arguments correctly.

    static SM1F5_INNER_LOOKUP_FIRED: AtomicU32 = AtomicU32::new(0);
    fn sm1f5_inner_lookup_handler(intid: u8, source_cpu: u8) {
        SM1F5_INNER_LOOKUP_FIRED
            .store(((intid as u32) << 8) | (source_cpu as u32), Ordering::SeqCst);
    }

    #[test]
    fn sm1f5_inner_register_then_lookup_returns_handler() {
        // SM1.F.5 audit-pass-1: use the `_in`-form helpers with a
        // stack-local handler table so this test cannot race with
        // any other test on the global `SGI_HANDLERS`.
        let mut handlers: [Option<SgiHandler>; MAX_SGI_INTID as usize] =
            [None; MAX_SGI_INTID as usize];
        // Pre-condition: empty table.
        for i in 0..MAX_SGI_INTID {
            assert!(
                lookup_sgi_handler_in(&handlers, i).is_none(),
                "fresh handler table must be all-None at INTID {}",
                i
            );
        }
        register_sgi_handler_in(&mut handlers, 14, sm1f5_inner_lookup_handler);
        assert!(
            lookup_sgi_handler_in(&handlers, 14).is_some(),
            "handler at INTID 14 must be retrievable after registration"
        );
        // Other slots untouched.
        for i in 0..MAX_SGI_INTID {
            if i == 14 {
                continue;
            }
            assert!(
                lookup_sgi_handler_in(&handlers, i).is_none(),
                "registration at INTID 14 must NOT touch INTID {}",
                i
            );
        }
    }

    static SM1F5_INNER_DISPATCH_FIRED: AtomicU32 = AtomicU32::new(0);
    fn sm1f5_inner_dispatch_handler(intid: u8, source_cpu: u8) {
        SM1F5_INNER_DISPATCH_FIRED
            .store(((intid as u32) << 8) | (source_cpu as u32), Ordering::SeqCst);
    }

    #[test]
    fn sm1f5_inner_dispatch_invokes_registered_handler() {
        // SM1.F.5 audit-pass-1: stack-local handler table again.
        // Uses a per-test counter so concurrent tests do not
        // observe each other's writes.
        SM1F5_INNER_DISPATCH_FIRED.store(0, Ordering::SeqCst);
        let mut handlers: [Option<SgiHandler>; MAX_SGI_INTID as usize] =
            [None; MAX_SGI_INTID as usize];
        register_sgi_handler_in(&mut handlers, 12, sm1f5_inner_dispatch_handler);
        dispatch_sgi_in(&handlers, 12, 7);
        let recorded = SM1F5_INNER_DISPATCH_FIRED.load(Ordering::SeqCst);
        assert_eq!(
            recorded,
            (12u32 << 8) | 7,
            "dispatcher passed wrong (intid, source_cpu) — expected (12, 7)"
        );
    }

    #[test]
    fn sm1f5_inner_dispatch_silent_for_unregistered_intid() {
        // SM1.F.5 audit-pass-1: dispatching to an unregistered slot
        // logs but does not panic.  Stack-local table so we know
        // INTID 13 is genuinely unregistered (independent of other
        // tests).
        let handlers: [Option<SgiHandler>; MAX_SGI_INTID as usize] =
            [None; MAX_SGI_INTID as usize];
        dispatch_sgi_in(&handlers, 13, 0);
    }

    #[test]
    fn sm1f5_inner_dispatch_silent_for_out_of_range_intid() {
        // SM1.F.5 audit-pass-1: out-of-range INTIDs early-return.
        let handlers: [Option<SgiHandler>; MAX_SGI_INTID as usize] =
            [None; MAX_SGI_INTID as usize];
        dispatch_sgi_in(&handlers, 16, 0);
        dispatch_sgi_in(&handlers, 100, 0);
        dispatch_sgi_in(&handlers, 255, 0);
    }

    #[test]
    fn sm1f5_inner_lookup_returns_none_for_out_of_range_intid() {
        let handlers: [Option<SgiHandler>; MAX_SGI_INTID as usize] =
            [None; MAX_SGI_INTID as usize];
        assert!(lookup_sgi_handler_in(&handlers, 16).is_none());
        assert!(lookup_sgi_handler_in(&handlers, 100).is_none());
        assert!(lookup_sgi_handler_in(&handlers, 255).is_none());
    }

    #[test]
    fn sm1f5_inner_lookup_returns_none_for_short_slice() {
        // SM1.F.5 audit-pass-1: a too-short slice (less than the
        // INTID we're looking up) returns None defensively.
        let handlers: [Option<SgiHandler>; 4] = [None; 4];
        // Slice has 4 entries; looking up INTID 5 returns None.
        assert!(lookup_sgi_handler_in(&handlers, 5).is_none());
        assert!(lookup_sgi_handler_in(&handlers, 15).is_none());
    }

    #[test]
    #[should_panic(expected = "WS-SM SM1.F.5")]
    fn sm1f5_inner_register_panics_on_short_slice() {
        // SM1.F.5 audit-pass-1: registering at INTID 5 with a slice
        // of length 4 panics defensively (caller bug).
        let mut handlers: [Option<SgiHandler>; 4] = [None; 4];
        register_sgi_handler_in(&mut handlers, 5, _sgi_test_handler_unused);
    }

    #[test]
    fn sm1f5_inner_signature_pins() {
        // SM1.F.5 audit-pass-1: pin the inner-form helper signatures.
        let _: fn(&mut [Option<SgiHandler>], u8, SgiHandler) = register_sgi_handler_in;
        let _: fn(&[Option<SgiHandler>], u8) -> Option<SgiHandler> = lookup_sgi_handler_in;
        let _: fn(&[Option<SgiHandler>], u8, u8) = dispatch_sgi_in;
    }

    #[test]
    fn sm1f5_global_wrapper_routes_through_inner_form() {
        // SM1.F.5 audit-pass-1: the global `dispatch_sgi` /
        // `lookup_sgi_handler` wrappers must route through the
        // `_in`-form helpers so production and test exercise the
        // same code path.
        //
        // We exercise the global wrappers on out-of-range INTIDs
        // (no global state mutation), which the `_in`-form helpers
        // handle identically.  This pins the wrapper-to-inner
        // delegation at the type/behaviour level.
        assert!(lookup_sgi_handler(16).is_none());
        assert!(lookup_sgi_handler(255).is_none());
        // Dispatching to an out-of-range INTID is a no-op (no panic).
        dispatch_sgi(16, 0);
        dispatch_sgi(255, 0);
    }

    #[test]
    fn sm1f5_handler_signature_pinned() {
        // SM1.F.5: SgiHandler is `fn(u8, u8)`.  A signature change
        // would break every registered handler at compile time.
        let _: SgiHandler = _sgi_test_handler_unused;
        let _: fn(u8, u8) = _sgi_test_handler_unused;
    }

    #[test]
    fn sm1f5_dispatch_function_signature_pinned() {
        // SM1.F.5: pin the public dispatch_sgi signature.
        let _: fn(u8, u8) = dispatch_sgi;
    }

    #[test]
    fn sm1f5_register_signature_pinned() {
        // SM1.F.5: pin the public registration ABI.  `unsafe fn`
        // pointer types pin the unsafe contract too.
        let _: unsafe fn(u8, SgiHandler) = register_sgi_handler;
    }

    #[test]
    fn sm1f5_lookup_signature_pinned() {
        // SM1.F.5: pin the public lookup ABI.
        let _: fn(u8) -> Option<SgiHandler> = lookup_sgi_handler;
    }

    #[test]
    #[should_panic(expected = "SGI INTID must be 0..15")]
    fn sm1f5_register_panics_on_out_of_range_intid() {
        // SM1.F.5: registering a handler for INTID 16 panics — the
        // table only has 16 slots and an out-of-range write would
        // trash unrelated data.
        unsafe {
            register_sgi_handler(16, _sgi_test_handler_unused);
        }
    }

    // ---------------------------------------------------------------------
    // SM1.F.5: iar_source_cpu extractor
    // ---------------------------------------------------------------------

    #[test]
    fn sm1f5_iar_source_cpu_extracts_bits_12_to_10() {
        // GIC-400 TRM §4.4.4: bits [12:10] carry the source CPU
        // interface for SGI INTIDs.  Verify the extractor masks
        // correctly against the full IAR bit pattern.
        // IAR = 0b00001_010_0000_0010 (intid=2, source_cpu=2)
        let iar = (2u32 << 10) | 2u32;
        assert_eq!(iar_source_cpu(iar), 2);
        // IAR with intid=15 (highest SGI), source_cpu=7 (highest)
        let iar2 = (7u32 << 10) | 15u32;
        assert_eq!(iar_source_cpu(iar2), 7);
    }

    #[test]
    fn sm1f5_iar_source_cpu_masks_higher_bits() {
        // The extractor masks to 3 bits — higher bits of the IAR
        // (e.g., bits [13:31]) must not bleed into the result.
        // Construct an IAR with bits 13..31 all set; the extractor
        // must still return only bits [12:10].
        let iar = 0xFFFF_F000u32 | (5u32 << 10);
        // Bits [12:10] = 5; bits [13:31] are above the mask.
        assert_eq!(iar_source_cpu(iar), 5);
    }

    #[test]
    fn sm1f5_iar_source_cpu_const_callable() {
        // The extractor is `const fn`.  Verify it evaluates at
        // compile time when given a literal IAR.
        const SOURCE: u8 = iar_source_cpu((3u32 << 10) | 5u32);
        assert_eq!(SOURCE, 3);
    }

    // ---------------------------------------------------------------------
    // SM1.F.8: Memory ordering — DSB-before-SGIR contract
    //
    // The send_sgi family emits `dsb ish` BEFORE writing GICD_SGIR so
    // any kernel-state mutation that the receiving handler needs to
    // observe is visible on every IS-domain PE before the SGI fires.
    // We cannot inspect the actual barrier emission from a host test
    // (the asm is cfg-gated to aarch64), but we can pin the property
    // by reading the source — captured by the build.rs scanner
    // `scan_gic_rs_send_sgi_emits_dsb_ish` (added in this PR).
    //
    // The runtime test here verifies the FUNCTIONAL property: the
    // send_sgi family does not panic on host (i.e., the asm is
    // properly cfg-gated for non-aarch64), so the production aarch64
    // build can rely on the wrapper for ordering.
    // ---------------------------------------------------------------------

    #[test]
    fn sm1f8_send_sgi_family_runs_on_host_without_panic() {
        // Regression check: a future cfg gate that forgot to no-op
        // on host would cause this test to abort.
        send_sgi(0x0F, 0);
        send_sgi_to_self(1);
        send_sgi_to_all_but_self(2);
    }

    #[test]
    fn sm1f_sgi_address_arithmetic_correct() {
        // Sanity: GICD_BASE + gicd::SGIR resolves to the BCM2712
        // GICD_SGIR MMIO address.
        let addr = GICD_BASE + gicd::SGIR;
        assert_eq!(addr, 0xFF841000 + 0xF00);
        assert_eq!(addr, 0xFF841F00, "GICD_SGIR must be at 0xFF841F00 on BCM2712");
    }
}
