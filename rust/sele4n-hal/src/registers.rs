//! System register accessor macros and wrappers for ARMv8-A.
//!
//! Provides type-safe read/write access to AArch64 system registers via
//! MRS/MSR instructions. Each accessor references the ARM Architecture
//! Reference Manual section for the corresponding register.
//!
//! On non-AArch64 hosts, read functions return 0 and write functions are
//! no-ops, enabling compilation and testing on x86_64.

/// Read a system register via MRS (AArch64 only; returns 0 on other targets).
///
/// ARM ARM C5.2: MRS reads a system register into a general-purpose register.
#[macro_export]
macro_rules! read_sysreg {
    ($reg:tt) => {{
        #[cfg(target_arch = "aarch64")]
        {
            let val: u64;
            // SAFETY: MRS reads a system register. Reading system registers at
            // EL1 is always safe. (ARM ARM C5.2)
            unsafe {
                core::arch::asm!(
                    concat!("mrs {}, ", $reg),
                    out(reg) val,
                    options(nomem, nostack, preserves_flags)
                );
            }
            val
        }
        #[cfg(not(target_arch = "aarch64"))]
        { 0u64 }
    }};
}

/// Write a system register via MSR (AArch64 only; no-op on other targets).
///
/// ARM ARM C5.2: MSR writes a general-purpose register to a system register.
#[macro_export]
macro_rules! write_sysreg {
    ($reg:tt, $val:expr) => {{
        let _v: u64 = $val;
        #[cfg(target_arch = "aarch64")]
        {
            // SAFETY: MSR writes a system register. The caller is responsible
            // for ensuring the value is valid. (ARM ARM C5.2)
            unsafe {
                core::arch::asm!(
                    concat!("msr ", $reg, ", {}"),
                    in(reg) _v,
                    options(nomem, nostack, preserves_flags)
                );
            }
        }
    }};
}

/// Read SCTLR_EL1 — System Control Register.
/// ARM ARM D17.2.120: Controls EL1&0 translation, alignment, caching.
#[inline(always)]
pub fn read_sctlr_el1() -> u64 {
    read_sysreg!("sctlr_el1")
}

/// Write SCTLR_EL1 — System Control Register.
/// Must be followed by ISB to synchronize.
/// ARM ARM D17.2.120.
#[inline(always)]
pub fn write_sctlr_el1(val: u64) {
    write_sysreg!("sctlr_el1", val);
}

/// Read TCR_EL1 — Translation Control Register.
/// ARM ARM D17.2.136: Controls translation table walks for EL1&0.
#[inline(always)]
pub fn read_tcr_el1() -> u64 {
    read_sysreg!("tcr_el1")
}

/// Write TCR_EL1.
#[inline(always)]
pub fn write_tcr_el1(val: u64) {
    write_sysreg!("tcr_el1", val);
}

/// Write TTBR0_EL1 — Translation Table Base Register 0 (user space).
/// ARM ARM D17.2.144.
#[inline(always)]
pub fn write_ttbr0_el1(val: u64) {
    write_sysreg!("ttbr0_el1", val);
}

/// Write TTBR1_EL1 — Translation Table Base Register 1 (kernel space).
/// ARM ARM D17.2.145.
#[inline(always)]
pub fn write_ttbr1_el1(val: u64) {
    write_sysreg!("ttbr1_el1", val);
}

/// Write MAIR_EL1 — Memory Attribute Indirection Register.
/// ARM ARM D17.2.95: Defines memory attribute encodings for page tables.
#[inline(always)]
pub fn write_mair_el1(val: u64) {
    write_sysreg!("mair_el1", val);
}

/// Write VBAR_EL1 — Vector Base Address Register.
/// ARM ARM D17.2.147: Base address of the EL1 exception vector table.
/// Must be 2048-byte aligned.
#[inline(always)]
pub fn write_vbar_el1(val: u64) {
    write_sysreg!("vbar_el1", val);
}

/// Read DAIF — Interrupt mask bits.
/// ARM ARM C5.2.5: D (Debug), A (SError), I (IRQ), F (FIQ) mask bits.
#[inline(always)]
pub fn read_daif() -> u64 {
    read_sysreg!("daif")
}

/// Write DAIF — Interrupt mask bits.
#[inline(always)]
pub fn write_daif(val: u64) {
    write_sysreg!("daif", val);
}

/// Read CurrentEL — Current Exception Level.
/// ARM ARM D17.2.18: Bits [3:2] contain the current EL (0-3).
#[inline(always)]
pub fn read_current_el() -> u64 {
    let val = read_sysreg!("CurrentEL");
    (val >> 2) & 0x3
}
