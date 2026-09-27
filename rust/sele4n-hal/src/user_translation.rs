//! **WS-BP BP7.2: a thread's translation, in memory and in `TTBR0_EL1`.**
//!
//! The Lean kernel's transitions are pure, so a transition that changes an
//! address space — a mapping, an installed table, a page carved for a thread —
//! records the store that makes physical memory agree
//! (`SeLe4n.Kernel.Architecture.PhysicalWrite`, drained by the syscall seam after the commit
//! and before the shootdown round), and this module performs it.  It also
//! installs an address space: `TTBR0_EL1` takes the root's table page and its
//! ASID, and the root's top-level entry `0` takes the **kernel window** — the
//! kernel's own level-1 table, which is how the kernel, running identity-mapped
//! in the `TTBR0` half, stays translated under every thread's address space.
//!
//! # What is refused
//!
//! Every operand is validated before anything is written, and a refusal halts
//! the system: the Lean kernel only names pages it owns, so an operand outside
//! them is a kernel defect, and writing it would corrupt memory the kernel did
//! not mean to touch.  A page is **admissible** when it is page-aligned and
//! either one of the boot's table-page pool pages or a whole page of RAM
//! outside the kernel's reserved extent that the boot map covers.
//!
//! # The kernel window
//!
//! Top-level entry `0` covers virtual addresses `[0, 2^39)`, which hold every
//! byte the kernel maps.  The Lean model refuses a thread's mapping or table
//! there (`Architecture.userWindowBase`), so the entry is always the kernel's.
//! It is written with the boot tables' own entry `0` plus two hierarchical
//! controls (ARM ARM D8.3.1): **UXNTable** (no instruction fetched at EL0
//! through it) and **APTable = 0b01** (no EL0 access through it), so the
//! kernel's pages are unreachable from EL0 whatever their own descriptors say.
//!
//! # TLB discipline
//!
//! Every thread translation is **non-global** (nG) and tagged with its address
//! space's ASID, and `TCR_EL1.AS` selects 16-bit ASIDs, so a root change needs
//! no invalidation — only the `ISB` that makes the new `TTBR0_EL1` take effect.
//! What does need one is an ASID's translations going stale while the ASID
//! lives on: a cleared table descriptor (the walk caches intermediate levels,
//! which a leaf `TLBI` does not name) and an ASID handed to a new address space.
//! The Lean kernel records both as `invalidateAsid`, performed here as
//! `TLBI ASIDE1IS`.

/// Tag of a page zeroing (`PhysicalWrite.zeroPage`).
pub const PHYSICAL_WRITE_ZERO_PAGE: u64 = 0;
/// Tag of a descriptor store (`PhysicalWrite.storeDescriptor`).
pub const PHYSICAL_WRITE_STORE_DESCRIPTOR: u64 = 1;
/// Tag of an ASID invalidation (`PhysicalWrite.invalidateAsid`).
pub const PHYSICAL_WRITE_INVALIDATE_ASID: u64 = 2;

/// Bytes in one page.
const PAGE_BYTES: u64 = 4096;

/// The number of ASIDs a 16-bit ASID space holds (`TCR_EL1.AS = 1`), which the
/// Lean model's `maxASID` matches.
pub const ASID_COUNT: u64 = 1 << 16;

/// **UXNTable** (bit 60) of a table descriptor.
pub const UXN_TABLE: u64 = 1 << 60;
/// **APTable = 0b01** (bits [62:61]): no EL0 access through the table.
pub const AP_TABLE_NO_EL0: u64 = 1 << 61;

/// A physical write, decoded and validated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PhysicalWrite {
    /// Zero the page at this address.
    ZeroPage(u64),
    /// Store this descriptor at this entry address.
    StoreDescriptor { entry: u64, value: u64 },
    /// Invalidate every translation tagged with this ASID.
    InvalidateAsid(u16),
}

/// Why a physical write was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PhysicalWriteRefusal {
    /// The tag names no operation.
    UnknownTag(u64),
    /// The address is not aligned to what it names (a page, or an entry).
    Misaligned(u64),
    /// The page is not one the kernel hands to a thread.
    NotAThreadPage(u64),
    /// The ASID is outside the 16-bit ASID space, or is the kernel's (0).
    AsidOutOfRange(u64),
}

/// **Is the page at `page` one the kernel may write for a thread?**  A pool
/// page, or a whole page of RAM past the kernel's reserved extent that
/// `covered` (the boot map's RAM) contains.
#[must_use]
pub fn thread_page_admissible(page: u64, covered: impl Fn(u64, u64) -> bool) -> bool {
    use crate::mmu::{BOOT_TABLE_POOL_BASE, KERNEL_RESERVED_END};
    if !page.is_multiple_of(PAGE_BYTES) {
        return false;
    }
    let in_pool = (BOOT_TABLE_POOL_BASE..KERNEL_RESERVED_END).contains(&page);
    let in_ram = page >= KERNEL_RESERVED_END && covered(page, PAGE_BYTES);
    in_pool || in_ram
}

/// Decode and validate one physical write.
pub fn decode_physical_write(
    tag: u64,
    addr: u64,
    value: u64,
    covered: impl Fn(u64, u64) -> bool,
) -> Result<PhysicalWrite, PhysicalWriteRefusal> {
    match tag {
        PHYSICAL_WRITE_ZERO_PAGE => {
            if !addr.is_multiple_of(PAGE_BYTES) {
                Err(PhysicalWriteRefusal::Misaligned(addr))
            } else if !thread_page_admissible(addr, covered) {
                Err(PhysicalWriteRefusal::NotAThreadPage(addr))
            } else {
                Ok(PhysicalWrite::ZeroPage(addr))
            }
        }
        PHYSICAL_WRITE_STORE_DESCRIPTOR => {
            if !addr.is_multiple_of(8) {
                Err(PhysicalWriteRefusal::Misaligned(addr))
            } else if !thread_page_admissible(addr & !(PAGE_BYTES - 1), covered) {
                Err(PhysicalWriteRefusal::NotAThreadPage(addr))
            } else {
                Ok(PhysicalWrite::StoreDescriptor { entry: addr, value })
            }
        }
        PHYSICAL_WRITE_INVALIDATE_ASID => {
            if addr == 0 || addr >= ASID_COUNT {
                Err(PhysicalWriteRefusal::AsidOutOfRange(addr))
            } else {
                Ok(PhysicalWrite::InvalidateAsid(addr as u16))
            }
        }
        other => Err(PhysicalWriteRefusal::UnknownTag(other)),
    }
}

/// Perform one validated physical write.
///
/// Zeroing and descriptor stores go through the kernel's identity map — every
/// admissible page is Normal write-back RAM the boot map covers — and end in
/// `DSB ISH`, after which the store is visible to every PE's table walker (the
/// walk is coherent with the data cache under `TCR_EL1`'s write-back
/// `IRGN`/`ORGN`, inner shareable).  The ASID invalidation is the broadcast
/// `TLBI ASIDE1IS` with its own barriers.  The host performs nothing: it has
/// no kernel identity map, and the host tests drive [`decode_physical_write`].
pub fn apply_physical_write(write: PhysicalWrite) {
    match write {
        PhysicalWrite::ZeroPage(page) => {
            #[cfg(target_arch = "aarch64")]
            {
                // SAFETY: `page` passed `thread_page_admissible`: one
                // page-aligned page of RAM outside the kernel image, mapped
                // Normal write-back by the kernel's identity map, which no
                // Rust reference aliases (the kernel owns it as a thread's page
                // and the Lean kernel names it only while carving it).
                unsafe {
                    core::ptr::write_bytes(page as *mut u8, 0, PAGE_BYTES as usize);
                }
            }
            #[cfg(not(target_arch = "aarch64"))]
            let _ = page;
            crate::barriers::dsb_ish();
        }
        PhysicalWrite::StoreDescriptor { entry, value } => {
            #[cfg(target_arch = "aarch64")]
            {
                // SAFETY: `entry` is eight-byte aligned inside an admissible
                // page (see above), and a descriptor store is a single aligned
                // 64-bit write, single-copy atomic for the walker (ARM ARM
                // B2.2.1), so no PE's walk observes a torn descriptor.
                unsafe {
                    core::ptr::write_volatile(entry as *mut u64, value);
                }
            }
            #[cfg(not(target_arch = "aarch64"))]
            let _ = (entry, value);
            crate::barriers::dsb_ish();
        }
        PhysicalWrite::InvalidateAsid(asid) => crate::tlb::tlbi_aside1is(asid),
    }
}

/// **The value `TTBR0_EL1` takes for an address space**: its table page in
/// `BADDR` and its ASID in bits [63:48] (ARM ARM D17.2.144, `TCR_EL1.A1 = 0`).
#[must_use]
pub const fn user_ttbr0_value(table_base: u64, asid: u16) -> u64 {
    (table_base & crate::mmu::TTBR_BAADDR_MASK) | ((asid as u64) << 48)
}

/// Why an install was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InstallRefusal {
    /// The table page is not a page the kernel owns for a thread.
    NotAThreadPage(u64),
    /// The ASID is the kernel's, or outside the ASID space.
    AsidOutOfRange(u64),
}

/// A translation to install on a PE, decoded and validated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Translation {
    /// The kernel's own boot tables, under ASID 0: a core running no thread's
    /// address space (an idle thread, or a thread whose root has no page).
    Kernel,
    /// An address space: its top-level table page and its ASID.
    User {
        /// The top-level table page.
        table_base: u64,
        /// The address space's ASID (never 0).
        asid: u16,
    },
}

/// Decode and validate an install's operands.  `(0, 0)` is the kernel's own
/// translation — the encoding `Platform.FFI.threadTranslationOperands` uses for
/// a thread with no installable root — and anything else must name a thread
/// page and a non-kernel ASID.
pub fn decode_install(
    table_base: u64,
    asid: u64,
    covered: impl Fn(u64, u64) -> bool,
) -> Result<Translation, InstallRefusal> {
    if table_base == 0 && asid == 0 {
        Ok(Translation::Kernel)
    } else if !thread_page_admissible(table_base, covered) {
        Err(InstallRefusal::NotAThreadPage(table_base))
    } else if asid == 0 || asid >= ASID_COUNT {
        Err(InstallRefusal::AsidOutOfRange(asid))
    } else {
        Ok(Translation::User {
            table_base,
            asid: asid as u16,
        })
    }
}

/// The kernel-window entry an address space's top-level entry `0` holds: the
/// boot tables' own entry `0`, with no EL0 access and no EL0 fetch beneath it.
#[must_use]
pub const fn kernel_window_entry(boot_l0_entry0: u64) -> u64 {
    boot_l0_entry0 | UXN_TABLE | AP_TABLE_NO_EL0
}

/// **Install a translation on the executing PE.**  For an address space: its
/// top-level entry `0` holds the kernel window (written, and made visible to
/// the walker, if it does not), then `TTBR0_EL1` takes [`user_ttbr0_value`],
/// then `ISB`.  For the kernel: `TTBR0_EL1` takes the boot tables under ASID 0.
/// No TLB invalidation either way: every thread translation is ASID-tagged and
/// every kernel translation is global (see the module docs).
pub fn install_translation(translation: Translation) {
    let value = match translation {
        Translation::Kernel => crate::mmu::boot_ttbr0_value(),
        Translation::User { table_base, asid } => {
            let window = kernel_window_entry(crate::mmu::boot_l0_entry0());
            #[cfg(target_arch = "aarch64")]
            {
                let slot = table_base as *mut u64;
                // SAFETY: `table_base` passed `thread_page_admissible` (in
                // `decode_install`): a page-aligned page of RAM the kernel owns
                // as an address space's top-level table and identity-maps
                // Normal write-back; entry 0 is its first eight bytes, aligned,
                // and an aligned 64-bit store is single-copy atomic for the
                // walker (ARM ARM B2.2.1).
                unsafe {
                    if core::ptr::read_volatile(slot) != window {
                        core::ptr::write_volatile(slot, window);
                        crate::barriers::dsb_ish();
                    }
                }
            }
            #[cfg(not(target_arch = "aarch64"))]
            let _ = window;
            user_ttbr0_value(table_base, asid)
        }
    };
    #[cfg(target_arch = "aarch64")]
    {
        crate::registers::write_ttbr0_el1(value);
        crate::barriers::isb();
    }
    #[cfg(not(target_arch = "aarch64"))]
    let _ = value;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mmu::{BOOT_TABLE_POOL_BASE, KERNEL_RESERVED_END};

    /// A stand-in for the boot map's RAM: `[KERNEL_RESERVED_END, 2 GiB)`.
    fn covered(base: u64, size: u64) -> bool {
        base.checked_add(size).is_some_and(|end| end <= 0x8000_0000)
    }

    const RAM_PAGE: u64 = KERNEL_RESERVED_END + 0x5000;

    #[test]
    fn the_tags_are_the_lean_encoding() {
        // `PhysicalWrite.tag` in `SeLe4n/Kernel/Architecture/PhysicalWrite.lean`.
        assert_eq!(PHYSICAL_WRITE_ZERO_PAGE, 0);
        assert_eq!(PHYSICAL_WRITE_STORE_DESCRIPTOR, 1);
        assert_eq!(PHYSICAL_WRITE_INVALIDATE_ASID, 2);
    }

    #[test]
    fn a_thread_page_is_a_pool_page_or_ram_past_the_kernel() {
        assert!(thread_page_admissible(BOOT_TABLE_POOL_BASE, covered));
        assert!(thread_page_admissible(KERNEL_RESERVED_END - 4096, covered));
        assert!(thread_page_admissible(RAM_PAGE, covered));
        // The kernel's own image and heap are never a thread's page.
        assert!(!thread_page_admissible(0x8_0000, covered));
        assert!(!thread_page_admissible(
            BOOT_TABLE_POOL_BASE - 4096,
            covered
        ));
        // RAM the boot map does not cover is not either.
        assert!(!thread_page_admissible(0x8000_0000, covered));
        // Nor is a page not on a page boundary.
        assert!(!thread_page_admissible(RAM_PAGE + 8, covered));
    }

    #[test]
    fn every_write_is_decoded_or_refused() {
        assert_eq!(
            decode_physical_write(0, RAM_PAGE, 0, covered),
            Ok(PhysicalWrite::ZeroPage(RAM_PAGE))
        );
        assert_eq!(
            decode_physical_write(0, RAM_PAGE + 8, 0, covered),
            Err(PhysicalWriteRefusal::Misaligned(RAM_PAGE + 8))
        );
        assert_eq!(
            decode_physical_write(0, 0x8_0000, 0, covered),
            Err(PhysicalWriteRefusal::NotAThreadPage(0x8_0000))
        );
        assert_eq!(
            decode_physical_write(1, RAM_PAGE + 0x18, 0xdead_0003, covered),
            Ok(PhysicalWrite::StoreDescriptor {
                entry: RAM_PAGE + 0x18,
                value: 0xdead_0003
            })
        );
        assert_eq!(
            decode_physical_write(1, RAM_PAGE + 4, 1, covered),
            Err(PhysicalWriteRefusal::Misaligned(RAM_PAGE + 4))
        );
        // A descriptor store into the kernel image is refused by its page.
        assert_eq!(
            decode_physical_write(1, 0x8_0010, 1, covered),
            Err(PhysicalWriteRefusal::NotAThreadPage(0x8_0010))
        );
        assert_eq!(
            decode_physical_write(2, 7, 0, covered),
            Ok(PhysicalWrite::InvalidateAsid(7))
        );
        assert_eq!(
            decode_physical_write(2, 0, 0, covered),
            Err(PhysicalWriteRefusal::AsidOutOfRange(0))
        );
        assert_eq!(
            decode_physical_write(2, ASID_COUNT, 0, covered),
            Err(PhysicalWriteRefusal::AsidOutOfRange(ASID_COUNT))
        );
        assert_eq!(
            decode_physical_write(3, RAM_PAGE, 0, covered),
            Err(PhysicalWriteRefusal::UnknownTag(3))
        );
    }

    #[test]
    fn an_install_is_the_kernel_or_an_owned_root() {
        assert_eq!(decode_install(0, 0, covered), Ok(Translation::Kernel));
        assert_eq!(
            decode_install(BOOT_TABLE_POOL_BASE, 1, covered),
            Ok(Translation::User {
                table_base: BOOT_TABLE_POOL_BASE,
                asid: 1
            })
        );
        assert_eq!(
            decode_install(RAM_PAGE, 0, covered),
            Err(InstallRefusal::AsidOutOfRange(0))
        );
        assert_eq!(
            decode_install(RAM_PAGE, ASID_COUNT, covered),
            Err(InstallRefusal::AsidOutOfRange(ASID_COUNT))
        );
        // A root may not be the kernel's own tables, nor half of the pair `(0, 0)`.
        assert_eq!(
            decode_install(0, 5, covered),
            Err(InstallRefusal::NotAThreadPage(0))
        );
        assert_eq!(
            decode_install(0x8_0000, 5, covered),
            Err(InstallRefusal::NotAThreadPage(0x8_0000))
        );
    }

    #[test]
    fn a_user_ttbr0_carries_the_asid_in_the_top_sixteen_bits() {
        assert_eq!(user_ttbr0_value(0x1234_5000, 0xBEEF), 0xBEEF_0000_1234_5000);
        // The base is masked to BADDR: a CnP bit or a stray low bit is dropped.
        assert_eq!(user_ttbr0_value(0x1234_5FFF, 1), 0x0001_0000_1234_5000);
    }

    #[test]
    fn the_kernel_window_denies_el0_access_and_fetch_beneath_it() {
        let entry = kernel_window_entry(0x0000_0000_4000_0003);
        assert_eq!(entry & UXN_TABLE, UXN_TABLE);
        assert_eq!(entry & (0b11 << 61), AP_TABLE_NO_EL0);
        // The table descriptor itself is carried unchanged.
        assert_eq!(
            entry & !(UXN_TABLE | AP_TABLE_NO_EL0),
            0x0000_0000_4000_0003
        );
        // PXNTable is clear: the kernel executes through the window.
        assert_eq!(entry & (1 << 59), 0);
    }

    #[test]
    fn the_kernel_window_is_the_boot_tables_entry_zero() {
        let entry0 = crate::mmu::boot_l0_entry0();
        assert_eq!(
            kernel_window_entry(entry0) & !(UXN_TABLE | AP_TABLE_NO_EL0),
            entry0
        );
    }
}
