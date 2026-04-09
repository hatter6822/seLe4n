//! GIC-400 interrupt controller driver for Raspberry Pi 5.
//!
//! Base addresses (from Board.lean):
//! - GICD (distributor):   0xFF841000
//! - GICC (CPU interface): 0xFF842000
//!
//! Stub implementation for AG4. Full initialization, acknowledge/dispatch/EOI
//! sequence implemented in AG5 (AG5-A through AG5-C).

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

/// Check if an interrupt ID is spurious.
#[inline(always)]
pub const fn is_spurious(intid: u32) -> bool {
    intid >= SPURIOUS_THRESHOLD
}
