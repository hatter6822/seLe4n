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

#![no_std]
// HAL crate requires unsafe code for hardware instructions (MRS/MSR, MMIO,
// inline assembly). Each unsafe block carries a // SAFETY: comment referencing
// the ARM Architecture Reference Manual. We deny at the module level where
// possible and allow where hardware access is required.
#![allow(unsafe_code)]

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
