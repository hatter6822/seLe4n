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
    /// Interrupt Clear-Enable Registers (used for selective disable in AG9).
    #[allow(dead_code)]
    pub const ICENABLER_BASE: usize = 0x180;
    /// Interrupt Clear-Pending Registers.
    pub const ICPENDR_BASE: usize = 0x280;
    /// Interrupt Priority Registers (8-bit per INTID, 4 per word).
    pub const IPRIORITYR_BASE: usize = 0x400;
    /// Interrupt Processor Targets Registers (8-bit per INTID, 4 per word).
    pub const ITARGETSR_BASE: usize = 0x800;
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
// MMIO Helpers
// ============================================================================

/// Write a 32-bit value to an MMIO register.
#[inline(always)]
fn mmio_write32(addr: usize, val: u32) {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: The caller provides a valid GIC MMIO address within the
        // mapped device memory region (0xFF841000-0xFF843FFF: distributor
        // 0x1000 + CPU interface 0x2000). Volatile write ensures the write
        // reaches the device. (ARM GIC-400 TRM §4.1)
        unsafe { core::ptr::write_volatile(addr as *mut u32, val) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = (addr, val);
    }
}

/// Read a 32-bit value from an MMIO register.
#[inline(always)]
fn mmio_read32(addr: usize) -> u32 {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: The caller provides a valid GIC MMIO address within the
        // mapped device memory region. Volatile read ensures we get the
        // current hardware value. (ARM GIC-400 TRM §4.1)
        unsafe { core::ptr::read_volatile(addr as *const u32) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = addr;
        0
    }
}

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
        mmio_write32(
            base + gicd::IPRIORITYR_BASE + i * 4,
            0xA0A0_A0A0,
        );
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
pub fn init_gic() {
    init_distributor(GICD_BASE);
    init_cpu_interface(GICC_BASE);
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

/// Handle an IRQ from the GIC: acknowledge → dispatch → EOI.
///
/// Called from `handle_irq` in trap.rs. The dispatch callback receives
/// the INTID and should handle the interrupt (e.g., reprogram timer,
/// signal notification).
///
/// AG9-F: CSDB after INTID classification prevents speculative dispatch
/// of attacker-controlled INTID values (Spectre v1 mitigation).
///
/// AK3-C.4 (A-H02 / HIGH): Now distinguishes three failure modes:
/// - Handled INTIDs: dispatch + EOI (normal path)
/// - OutOfRange INTIDs: **EOI but no dispatch** (prevents GIC lockup on
///   errata or SMP races delivering INTID ∈ [224, 1020))
/// - Spurious INTIDs (≥ 1020): no EOI per GIC-400 spec
///
/// Returns `true` if a real (non-spurious) interrupt was acknowledged;
/// this includes both handled and out-of-range cases because both
/// participate in the interrupt lifecycle (IAR read + EOI).
pub fn dispatch_irq<F: FnOnce(u32)>(handler: F) -> bool {
    match acknowledge_irq_classified(GICC_BASE) {
        AckResult::Spurious => false,
        AckResult::Handled(intid) => {
            // AG9-F: Speculation barrier resolves the classification
            // check before dispatching attacker-influenced INTIDs.
            crate::barriers::csdb();
            handler(intid);
            end_of_interrupt(GICC_BASE, intid);
            true
        }
        AckResult::OutOfRange(intid) => {
            // AK3-C.4: EOI must fire for out-of-range INTIDs to close
            // the interrupt cycle; no handler dispatch because the
            // INTID is unsupported on this platform.
            crate::barriers::csdb();
            end_of_interrupt(GICC_BASE, intid);
            true
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

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
        assert!(!is_spurious(30));    // timer PPI
        assert!(!is_spurious(223));   // last valid SPI
        assert!(!is_spurious(1019));  // just below threshold
        assert!(is_spurious(1020));   // spurious threshold
        assert!(is_spurious(1023));   // standard spurious ID
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
        // 224 INTIDs / 32 per bank = 7 banks
        assert_eq!((MAX_INTID + 31) / 32, 7);
    }

    #[test]
    fn num_priority_regs() {
        // 224 INTIDs / 4 per register = 56 registers
        assert_eq!((MAX_INTID + 3) / 4, 56);
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
}
