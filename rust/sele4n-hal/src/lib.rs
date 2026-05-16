// SPDX-License-Identifier: GPL-3.0-or-later
//! # sele4n-hal — ARM64 Hardware Abstraction Layer
//!
//! Kernel-side HAL for the seLe4n verified microkernel targeting Raspberry Pi 5
//! (BCM2712, Cortex-A76, ARMv8-A). Provides scoped `unsafe` wrappers around
//! hardware instructions with `// SAFETY:` annotations referencing the ARM
//! Architecture Reference Manual.
//!
//! ## Module overview
//!
//! - `cpu` — CPU instruction wrappers (WFE, WFI, NOP, ERET,
//!   bounded WFE primitive, MPIDR core-id read)
//! - `barriers` — Memory barrier wrappers (DMB, DSB, ISB) and the
//!   `BarrierKind` algebra (AN9-C/H/I)
//! - `registers` — System register accessors (MRS/MSR), including
//!   `read_tpidr_el1` / `write_tpidr_el1` (WS-SM SM0.N)
//! - `uart` — PL011 UART driver for debug console
//! - `mmu` — MMU configuration (MAIR, TCR, TTBR, SCTLR)
//! - `trap` — Trap frame and handler dispatch
//! - `boot` — Boot sequence (BSS zero, stack, hardware init,
//!   TPIDR_EL1 setup, IRQ enable)
//! - `gic` — GIC-400 interrupt controller driver (AG5-A/B/C)
//! - `timer` — ARM Generic Timer driver (AG5-D)
//! - `interrupts` — Interrupt management / critical sections (AG5-G)
//! - `tlb` — TLB maintenance instruction wrappers (AG6-E)
//! - `cache` — Cache maintenance operations (AG6-I)
//! - `mmio` — MMIO volatile read/write primitives (AG7-C)
//! - `ffi` — Lean FFI bridge exports (AG7-A + AN9-A/D +
//!   WS-SM SM1.B.5 `ffi_current_core_id`)
//! - `profiling` — Performance profiling (PMCCNTR_EL0 cycle counter,
//!   AG9)
//! - `svc_dispatch` — Typed SVC argument marshalling (AN9-F / DEF-R-HAL-L14)
//! - `psci` — Power State Coordination Interface wrappers
//!   (AN9-J.1 `cpu_on` + WS-SM SM1.A full DEN0022D §5 surface)
//! - `smp` — SMP secondary-core scaffolding (AN9-J), runtime-gated
//!   by `SMP_ENABLED` (default `false` at v1.0.0)
//! - `per_cpu` — Per-CPU data block + TPIDR_EL1 accessors
//!   (WS-SM SM1.B; closes SMP-M4)

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
//             a bounded WFE hint would be cheaper.
//             CLOSED at AN9-G (DEF-R-HAL-L17): bounded WFE primitive
//             `cpu::wfe_bounded` and `cpu::WFE_DEFAULT_TIMEOUT_TICKS`
//             provide the required interrupt-wait timeout guard.
// - R-HAL-L7  `dc_zva` options: `cache::dc_zva` uses
//             `options(nostack)` without `preserves_flags` because
//             hardware semantics for DC ZVA do not touch PSTATE flags
//             (ARM ARM C6.2.62). The current encoding is correct.
// - R-HAL-L8  Hard-coded GIC base: `GICD_BASE`/`GICC_BASE` are BCM2712
//             constants (`Board.lean`). A generic `PlatformConfig` API
//             would parameterize these.
//             CLOSED at AN9-H (DEF-R-HAL-L18): the parameterised
//             `barriers::BarrierKind` enum + `emit()` method lets
//             generic HAL code accept a BarrierKind instead of
//             selecting a specific dsb/isb helper at the call site.
//             MMIO base-address parameterisation remains a separate
//             post-1.0 hardening item; the BarrierKind closure is
//             the substantive AN9-H deliverable.
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
//             is correct for single-cluster boot (AK5-I).
//             CLOSED at AN9-I (DEF-R-HAL-L19): outer-shareable
//             barriers `barriers::dsb_osh` / `barriers::dsb_oshst`
//             plus `BarrierKind::DsbOsh` / `DsbOshst` variants.
//             `BarrierKind::emit_mmio_cross_cluster_barrier` is the
//             named entry point for cross-cluster MMIO writes (e.g.,
//             PSCI CPU_ON for AN9-J SMP bring-up).
// - R-HAL-L13 TLB maintenance granularity: AG6-E/G already emits DSB
//             ISH + ISB after TLBI. No tightening needed.
// - R-HAL-L14 SVC `_syscall_id` FFI wiring: CLOSED at AN9-F
//             (DEF-R-HAL-L14).  The new `svc_dispatch` module owns
//             typed argument marshalling (`SyscallArgs`,
//             `SyscallId`, `dispatch_svc`); `trap.rs::handle_svc`
//             routes through it instead of the previous
//             NotImplemented stub.
// - R-HAL-L15 MPIDR mask: handled by AK5-I.
// - R-HAL-L16 Secondary core bring-up: CLOSED at AN9-J (DEF-R-HAL-L20).
//             The `psci` module exposes `cpu_on` (PSCI CPU_ON wrapper)
//             and the `smp` module exposes `SMP_ENABLED` (runtime gate),
//             `bring_up_secondaries` (primary-core entry), and
//             `rust_secondary_main` (secondary-core entry).  Default
//             at v1.0.0 is `SMP_ENABLED = false` so single-core boot
//             is preserved; opting in is a kernel-command-line flag.
//             QEMU `-smp 4` validation is gated on firmware PSCI
//             support; host tests cover the call graph with stubs.
//
//             WS-SM SM1.A completes the PSCI surface beyond `cpu_on`:
//             the module now wraps the full DEN0022D §5 subset the
//             kernel needs — `cpu_off`, `affinity_info` (with
//             `AffinityInfoState`), `psci_version` (with
//             `PsciVersion`), `migrate_info_type` (with
//             `MigrateInfoType`), `system_off`, `system_reset`.
//             Compile-time assertions pin every function id to its
//             ARM SMCCC encoding (Fast call + SMC32/64 + OEN=4 +
//             reserved-bits-clear).  See `psci.rs` module docstring
//             for the complete function-id map.
//
//             WS-SM SM1.B (closes SMP-M4) completes the per-CPU data
//             block + TPIDR_EL1 contract introduced as a stub at
//             SM0.N.  `per_cpu.rs` owns the `PerCpuData` struct (with
//             a populated `core_id` field instead of the SM0.N
//             `_reserved` placeholder), the `current_per_cpu()` /
//             `current_core_id_from_tpidr()` accessors, and the
//             `check_per_cpu_invariants()` boot gate.  `ffi.rs`
//             exposes `ffi_current_core_id` for the Lean kernel; the
//             Lean side wraps it as `Concurrency.currentCoreId :
//             BaseIO CoreId` with a range check that recovers the
//             typed `Fin numCores` identifier.

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
// AN9-F (DEF-R-HAL-L14): typed SVC argument marshalling
pub mod svc_dispatch;
// AN9-J.1 (DEF-R-HAL-L20): PSCI wrapper for secondary-core bring-up.
// WS-SM SM1.A extends this to the full DEN0022D §5 surface
// (cpu_off, affinity_info, psci_version, migrate_info_type,
// system_off, system_reset); see psci.rs module docstring for the
// function-id map.
pub mod psci;
// AN9-J (DEF-R-HAL-L20): SMP secondary-core scaffolding (off by default)
pub mod smp;
// WS-SM SM1.B (closes SMP-M4): per-CPU data block + TPIDR_EL1
// accessors.  The `PerCpuData` struct, the global `PER_CPU_DATA`
// array, and the slot-stride symbols (`PER_CPU_DATA_SLOT_SIZE_SYM`)
// live here; `boot.S::secondary_entry` resolves the asm-visible
// names against this module's `#[no_mangle] static` items.  See the
// module docstring in `per_cpu.rs` for the boot-ordering contract.
pub mod per_cpu;
