//! TLB (Translation Lookaside Buffer) flush instruction wrappers for ARMv8-A.
//!
//! Each TLBI instruction is followed by DSB ISH + ISB per ARM ARM D8.11:
//! "A TLB maintenance instruction is only guaranteed to be complete after the
//! execution of a DSB instruction." The ISB ensures the pipeline sees the new
//! translations.
//!
//! AG6-E: TLB flush instruction wrappers (H3-ARCH-02/RUST-05)
//! AG6-G: ISB after TLBI per ARM ARM requirement (H3-ARCH-03)
//!
//! On non-AArch64 hosts, functions are no-ops for compilation and testing.
//!
//! References:
//! - ARM ARM C6.2.311–316: TLBI instructions
//! - ARM ARM D8.11: TLB maintenance requirements

use crate::barriers;

/// Flush all TLB entries at EL1 (TLBI VMALLE1).
///
/// Invalidates all stage 1 translations used at EL0 and EL1 for the
/// current VMID. Used for full address space flushes (e.g., after TTBR switch).
///
/// ARM ARM C6.2.316: TLBI VMALLE1
#[inline(always)]
pub fn tlbi_vmalle1() {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI VMALLE1 is a TLB maintenance instruction that
        // invalidates cached translations. No memory corruption — only forces
        // re-walk from page tables. (ARM ARM C6.2.316)
        unsafe {
            core::arch::asm!("tlbi vmalle1", options(nostack, preserves_flags));
        }
    }
    // AG6-G: DSB ISH + ISB after TLBI per ARM ARM D8.11
    barriers::dsb_ish();
    barriers::isb();
}

/// Flush TLB entries by virtual address at EL1 (TLBI VAE1).
///
/// Invalidates all stage 1 translations for the specified virtual address
/// and ASID. The address must be right-shifted by 12 (page-aligned) and
/// the ASID occupies bits [63:48] of the operand.
///
/// ARM ARM C6.2.311: TLBI VAE1, Xt
#[inline(always)]
pub fn tlbi_vae1(asid: u16, vaddr: u64) {
    let _operand = ((asid as u64) << 48) | ((vaddr >> 12) & 0xFFFF_FFFF_FFFF);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI VAE1 invalidates TLB entries matching the specified
        // VA and ASID. No memory corruption. (ARM ARM C6.2.311)
        unsafe {
            core::arch::asm!("tlbi vae1, {0}", in(reg) _operand, options(nostack, preserves_flags));
        }
    }
    barriers::dsb_ish();
    barriers::isb();
}

/// Flush TLB entries by ASID at EL1 (TLBI ASIDE1).
///
/// Invalidates all stage 1 translations for the specified ASID.
/// The ASID occupies bits [63:48] of the operand.
///
/// ARM ARM C6.2.312: TLBI ASIDE1, Xt
#[inline(always)]
pub fn tlbi_aside1(asid: u16) {
    let _operand = (asid as u64) << 48;
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI ASIDE1 invalidates TLB entries matching the ASID.
        // No memory corruption. (ARM ARM C6.2.312)
        unsafe {
            core::arch::asm!("tlbi aside1, {0}", in(reg) _operand, options(nostack, preserves_flags));
        }
    }
    barriers::dsb_ish();
    barriers::isb();
}

/// Flush last-level TLB entries by VA at EL1 (TLBI VALE1).
///
/// Like VAE1 but only invalidates last-level (L3 page) TLB entries,
/// leaving intermediate level entries cached. More efficient for single
/// page unmap operations.
///
/// ARM ARM C6.2.313: TLBI VALE1, Xt
#[inline(always)]
pub fn tlbi_vale1(asid: u16, vaddr: u64) {
    let _operand = ((asid as u64) << 48) | ((vaddr >> 12) & 0xFFFF_FFFF_FFFF);
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: TLBI VALE1 invalidates last-level TLB entries matching the
        // specified VA and ASID. No memory corruption. (ARM ARM C6.2.313)
        unsafe {
            core::arch::asm!("tlbi vale1, {0}", in(reg) _operand, options(nostack, preserves_flags));
        }
    }
    barriers::dsb_ish();
    barriers::isb();
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tlbi_vmalle1_compiles() {
        // On non-aarch64, this is a no-op but must compile
        tlbi_vmalle1();
    }

    #[test]
    fn test_tlbi_vae1_compiles() {
        tlbi_vae1(42, 0x1000);
    }

    #[test]
    fn test_tlbi_aside1_compiles() {
        tlbi_aside1(42);
    }

    #[test]
    fn test_tlbi_vale1_compiles() {
        tlbi_vale1(42, 0x1000);
    }

    #[test]
    fn test_vae1_operand_encoding() {
        // ASID=5, VA=0x12345000
        // Expected: ASID in bits [63:48], VA>>12 in bits [47:0]
        let asid: u16 = 5;
        let vaddr: u64 = 0x12345000;
        let operand = ((asid as u64) << 48) | ((vaddr >> 12) & 0xFFFF_FFFF_FFFF);
        assert_eq!(operand >> 48, 5);
        assert_eq!(operand & 0xFFFF_FFFF_FFFF, 0x12345);
    }

    #[test]
    fn test_aside1_operand_encoding() {
        let asid: u16 = 0xABCD;
        let operand = (asid as u64) << 48;
        assert_eq!(operand >> 48, 0xABCD);
        assert_eq!(operand & 0x0000_FFFF_FFFF_FFFF, 0);
    }
}
