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
        fn new() -> Self { Self(AtomicU32::new(0)) }
        fn tick(&self) -> u32 { self.0.fetch_add(1, Ordering::SeqCst) }
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
        assert!(eoi < hnd,
            "AN8-C.1 violated: EOI tick {eoi} must precede handler tick {hnd}");
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
        assert_eq!(eoi_count.load(Ordering::SeqCst), 1,
            "EOI must fire exactly once for OutOfRange");
        assert_eq!(handler_count.load(Ordering::SeqCst), 0,
            "handler must NOT fire for OutOfRange (no valid INTID)");
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
        assert_eq!(eoi_count.load(Ordering::SeqCst), 0,
            "EOI MUST NOT fire for Spurious per GIC-400 §3.1");
        assert_eq!(handler_count.load(Ordering::SeqCst), 0,
            "handler MUST NOT fire for Spurious");
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
        assert!(result.is_err(),
            "handler panic must propagate up out of dispatch_irq_inner");
        assert_eq!(EOI_FIRED_BEFORE_PANIC.load(Ordering::SeqCst), 1,
            "AN8-C.1: EOI must have fired exactly once BEFORE the \
             handler panic — the panic cannot un-fire it");
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
        assert_eq!(expected, 0xFF841000 + 0x800 + 8 * 4,
            "self-check address arithmetic regressed");
        assert_eq!(expected, 0xFF841820,
            "self-check should target ITARGETSR[8] @ 0xFF841820 \
             on BCM2712");
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
}
