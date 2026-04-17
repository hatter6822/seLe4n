//! # sele4n-hal — ARM64 Hardware Abstraction Layer
//!
//! Kernel-side HAL for the seLe4n verified microkernel targeting Raspberry Pi 5
//! (BCM2712, Cortex-A76, ARMv8-A). Provides scoped `unsafe` wrappers around
//! hardware instructions with `// SAFETY:` annotations referencing the ARM
//! Architecture Reference Manual.
//!
//! ## Module overview
//!
//! - `cpu`       — CPU instruction wrappers (WFE, WFI, NOP, ERET)
//! - `barriers`  — Memory barrier wrappers (DMB, DSB, ISB)
//! - `registers` — System register accessors (MRS/MSR)
//! - `uart`      — PL011 UART driver for debug console
//! - `mmu`       — MMU configuration (MAIR, TCR, TTBR, SCTLR)
//! - `trap`      — Trap frame and handler dispatch
//! - `boot`      — Boot sequence (BSS zero, stack, hardware init)
//! - `gic`        — GIC-400 interrupt controller driver (AG5-A/B/C)
//! - `timer`      — ARM Generic Timer driver (AG5-D)
//! - `interrupts` — Interrupt management / critical sections (AG5-G)
//! - `tlb`        — TLB maintenance instruction wrappers (AG6-E)
//! - `cache`      — Cache maintenance operations (AG6-I)
//! - `mmio`       — MMIO volatile read/write primitives (AG7-C)
//! - `ffi`        — Lean FFI bridge exports (AG7-A)

#![no_std]
// HAL crate requires unsafe code for hardware instructions (MRS/MSR, MMIO,
// inline assembly). Each unsafe block carries a // SAFETY: comment referencing
// the ARM Architecture Reference Manual. We deny at the module level where
// possible and allow where hardware access is required.
#![allow(unsafe_code)]

// ============================================================================
// AK5-N: LOW-tier HAL batch documentation (R-HAL-L1..L16)
// ============================================================================
//
// Audit §8.1 LOW items that are addressed as annotations rather than code
// changes. Each L-n is cross-referenced to the relevant site so auditors
// can trace the observation → resolution without re-reading the plan.
//
// - R-HAL-L1  Signature fixes in `trap.rs`:
//             `handle_serror` now declares `-> !` (AK5-K/M12). `handle_irq`
//             and `handle_synchronous_exception` intentionally take
//             `&mut TrapFrame` so userspace registers can be modified on
//             return (e.g., to surface the syscall result via `set_x0`).
// - R-HAL-L2  Comment accuracy: TrapFrame-layout docstrings (`trap.rs`,
//             `trap.S`) now read 288 bytes across all sites (AK5-F).
// - R-HAL-L3  `const fn` promotion: `is_spurious` in `gic.rs` and
//             `compute_sctlr_el1_bitmap` in `mmu.rs` are `const fn`
//             (compile-time evaluable). Promoting `current_core_id` is
//             blocked by inline asm (non-const-fn).
// - R-HAL-L4  SMP readiness flags: `MPIDR_CORE_ID_MASK` in `cpu.rs`
//             (AK5-I) and the `.L_secondary_spin` parking loop in
//             `boot.S` document the SMP-unready invariant.
// - R-HAL-L5  Redundant DAIF bits: the `disable_interrupts` immediate
//             `#0xf` sets D|A|I|F together. Although D|A are already
//             masked by ARM64 exception entry, keeping F in the mask
//             documents the "all maskable exceptions" intent; changing
//             the immediate would require a plan update.
// - R-HAL-L6  Spinlock backoff tuning: `UartLock::with` in `uart.rs`
//             uses `core::hint::spin_loop()` inside the CAS loop. On
//             ARMv8.0 this maps to `yield`; on ARMv8.1+ with FEAT_WFxT
//             a bounded WFE hint would be cheaper. Deferred to WS-V.
// - R-HAL-L7  `dc_zva` options: `cache::dc_zva` uses
//             `options(nostack)` without `preserves_flags` because
//             hardware semantics for DC ZVA do not touch PSTATE flags
//             (ARM ARM C6.2.62). The current encoding is correct.
// - R-HAL-L8  Hard-coded GIC base: `GICD_BASE`/`GICC_BASE` are BCM2712
//             constants (`Board.lean`). A generic `PlatformConfig` API
//             would parameterize these; deferred to WS-V (H3-PLAT).
// - R-HAL-L9  Secondary core wake-storm risk: `.L_secondary_spin` wakes
//             on any SEV (e.g., from WFE-aware spinlocks elsewhere).
//             Current kernel never issues SEV, so this is latent.
//             Documented in `boot.S`.
// - R-HAL-L10 SP0 vector stub: vectors for "Current EL with SP0" in
//             `vectors.S` are unreachable (seLe4n always uses SPx at
//             EL1). Annotated accordingly.
// - R-HAL-L11 Alignment check bit A (SCTLR.A, bit 1): not set in the
//             bitmap because data-memory alignment checks would trigger
//             false faults on `memcpy`-style unaligned byte sequences
//             inside the kernel. WXN + SA + SA0 provide the security-
//             relevant checks.
// - R-HAL-L12 SMP-aware DSB / DMB: current HAL uses ISH domain which
//             is correct for single-cluster boot (AK5-I). SMP bring-up
//             in WS-V may need to widen selected barriers to OSH.
// - R-HAL-L13 TLB maintenance granularity: AG6-E/G already emits DSB
//             ISH + ISB after TLBI. No tightening needed.
// - R-HAL-L14 SVC `_syscall_id` FFI wiring deferred to WS-V/AG10.
//             Annotation in `trap.rs::handle_synchronous_exception`
//             SVC arm documents the TODO.
// - R-HAL-L15 MPIDR mask: handled by AK5-I.
// - R-HAL-L16 Secondary core bring-up: deferred to WS-V.

pub mod cpu;
pub mod barriers;
pub mod registers;
pub mod uart;
pub mod mmu;
pub mod trap;
pub mod boot;
pub mod gic;
pub mod timer;
pub mod interrupts;
pub mod tlb;
pub mod cache;
pub mod mmio;
pub mod ffi;
pub mod profiling;
