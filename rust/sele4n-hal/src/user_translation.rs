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
/// Tag of a user-word store (`PhysicalWrite.storeUserWord`, WS-BP BP7.8).
pub const PHYSICAL_WRITE_STORE_USER_WORD: u64 = 3;
/// Tag of a table-descriptor store (`PhysicalWrite.storeTableDescriptor`,
/// PR #904 `v0.36.41`): an entry of a level 0–2 table page.
pub const PHYSICAL_WRITE_STORE_TABLE_DESCRIPTOR: u64 = 4;

/// Bits `[1:0]` of a valid page (level 3) or table (levels 0–2) descriptor.
const DESC_PAGE_OR_TABLE: u64 = 0b11;
/// A descriptor's output address, bits `[47:12]`.
const DESC_OUTPUT_ADDRESS: u64 = 0x0000_FFFF_FFFF_F000;
/// `AttrIndx`, bits `[4:2]` of a page descriptor.
const DESC_ATTR_INDEX: u64 = 0b111 << 2;
/// `AttrIndx = 0`: Normal write-back (MAIR index 0).
const DESC_ATTR_NORMAL: u64 = 0;
/// `AttrIndx = 1`: Device-nGnRnE (MAIR index 1).
const DESC_ATTR_DEVICE: u64 = 1 << 2;
/// `AP`, bits `[7:6]`.
const DESC_AP: u64 = 0b11 << 6;
/// `SH`, bits `[9:8]`.
const DESC_SH: u64 = 0b11 << 8;
/// The access flag.
const DESC_AF: u64 = 1 << 10;
/// Not-global: the translation is tagged with the ASID.
const DESC_NG: u64 = 1 << 11;
/// Privileged execute-never.
const DESC_PXN: u64 = 1 << 53;
/// Unprivileged execute-never.
const DESC_UXN: u64 = 1 << 54;
/// Every bit a thread's page descriptor may carry
/// (`Architecture.userPageDescriptorValue`).
const DESC_PAGE_BITS: u64 = DESC_OUTPUT_ADDRESS
    | DESC_ATTR_INDEX
    | DESC_AP
    | DESC_SH
    | DESC_AF
    | DESC_NG
    | DESC_PXN
    | DESC_UXN
    | DESC_PAGE_OR_TABLE;
/// Every bit a table descriptor may carry (`Architecture.tableDescriptorValue`):
/// no hierarchical control, so the table's own entries decide.
const DESC_TABLE_BITS: u64 = DESC_OUTPUT_ADDRESS | DESC_PAGE_OR_TABLE;

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
    /// Store this level-3 page descriptor at this entry address.
    StoreDescriptor { entry: u64, value: u64 },
    /// Store this table descriptor at this entry of a level 0–2 table page.
    StoreTableDescriptor { entry: u64, value: u64 },
    /// Invalidate every translation tagged with this ASID.
    InvalidateAsid(u16),
    /// Store this word at this address of a thread's RAM page (WS-BP BP7.8).
    StoreUserWord { addr: u64, value: u64 },
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
    /// The descriptor is not one the Lean kernel writes: a page naming memory
    /// no thread may map, or with attributes a thread's page never carries; a
    /// table naming a page that is not a thread's table page (PR #904).
    DescriptorRefused(u64),
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

/// **Is the word at `addr` one the kernel may read or write for a thread?**
/// (WS-BP BP7.8.)  An eight-byte aligned word in a whole page of RAM past the
/// kernel's reserved extent that `covered` contains — a thread's own frame.
/// Deliberately **not** a pool page: the pool holds the configured roots'
/// translation tables, and a user word stored there would be a descriptor
/// nobody wrote.  That refusal covers the **pool** only: a page table or VSpace
/// root carved from an untyped (WS-BP BP7.1) is RAM past the extent like any
/// frame, and this check cannot tell the two apart.  What keeps a message
/// register out of a carved table is the Lean side — the address is resolved
/// through the thread's own VSpace (`ipcBufferSlotPAddr?`), which maps only
/// frames, and carves are disjoint, so no mapped page is ever a table page.
#[must_use]
pub fn user_word_admissible(addr: u64, covered: impl Fn(u64, u64) -> bool) -> bool {
    use crate::mmu::KERNEL_RESERVED_END;
    let page = addr & !(PAGE_BYTES - 1);
    addr.is_multiple_of(8) && page >= KERNEL_RESERVED_END && covered(page, PAGE_BYTES)
}

/// **Is `value` a level-3 descriptor the Lean kernel writes?** (PR #904,
/// `v0.36.41`.)  The clear (`0`), or a page descriptor
/// (`Architecture.userPageDescriptorValue`) carrying no bit outside
/// [`DESC_PAGE_BITS`], with the access flag, not-global and privileged
/// execute-never set, whose output address is either
///
/// * a thread's **RAM** frame — a whole page of RAM past the kernel's reserved
///   extent that `covered` contains, and **not** a table-pool page — mapped
///   Normal write-back (`AttrIndx 0`), the type the kernel's own identity map
///   gives it; or
/// * a page of the **device window**, mapped Device (`AttrIndx 1`) and never
///   executable at EL0.
///
/// So a descriptor the model mis-recorded — a leaf naming the kernel's image,
/// its heap or a translation table, a writable-at-EL1-executable page, an
/// uncached alias of RAM — is refused before it reaches a table.
#[must_use]
pub fn page_descriptor_admissible(value: u64, covered: impl Fn(u64, u64) -> bool) -> bool {
    use crate::mmu::{DEVICE_WINDOW_BASE, DEVICE_WINDOW_TOP, KERNEL_RESERVED_END};
    if value == 0 {
        return true;
    }
    let required = DESC_PAGE_OR_TABLE | DESC_AF | DESC_NG | DESC_PXN;
    if value & !DESC_PAGE_BITS != 0 || value & required != required {
        return false;
    }
    let oa = value & DESC_OUTPUT_ADDRESS;
    match value & DESC_ATTR_INDEX {
        DESC_ATTR_NORMAL => oa >= KERNEL_RESERVED_END && covered(oa, PAGE_BYTES),
        DESC_ATTR_DEVICE => {
            value & DESC_UXN != 0
                && oa >= DEVICE_WINDOW_BASE
                && oa
                    .checked_add(PAGE_BYTES)
                    .is_some_and(|end| end <= DEVICE_WINDOW_TOP)
        }
        _ => false,
    }
}

/// **Is `value` a level 0–2 descriptor the Lean kernel writes?** (PR #904,
/// `v0.36.41`.)  The clear (`0`), or a table descriptor
/// (`Architecture.tableDescriptorValue`) carrying no bit outside
/// [`DESC_TABLE_BITS`] whose output address is a thread table page
/// ([`thread_page_admissible`]: a pool page or a carved page of RAM).
#[must_use]
pub fn table_descriptor_admissible(value: u64, covered: impl Fn(u64, u64) -> bool) -> bool {
    value == 0
        || (value & !DESC_TABLE_BITS == 0
            && value & DESC_PAGE_OR_TABLE == DESC_PAGE_OR_TABLE
            && thread_page_admissible(value & DESC_OUTPUT_ADDRESS, covered))
}

/// Decode and validate one physical write — where it lands **and** what it
/// writes.
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
            } else if !thread_page_admissible(addr & !(PAGE_BYTES - 1), &covered) {
                Err(PhysicalWriteRefusal::NotAThreadPage(addr))
            } else if !page_descriptor_admissible(value, &covered) {
                Err(PhysicalWriteRefusal::DescriptorRefused(value))
            } else {
                Ok(PhysicalWrite::StoreDescriptor { entry: addr, value })
            }
        }
        PHYSICAL_WRITE_STORE_TABLE_DESCRIPTOR => {
            if !addr.is_multiple_of(8) {
                Err(PhysicalWriteRefusal::Misaligned(addr))
            } else if !thread_page_admissible(addr & !(PAGE_BYTES - 1), &covered) {
                Err(PhysicalWriteRefusal::NotAThreadPage(addr))
            } else if !table_descriptor_admissible(value, &covered) {
                Err(PhysicalWriteRefusal::DescriptorRefused(value))
            } else {
                Ok(PhysicalWrite::StoreTableDescriptor { entry: addr, value })
            }
        }
        PHYSICAL_WRITE_INVALIDATE_ASID => {
            if addr == 0 || addr >= ASID_COUNT {
                Err(PhysicalWriteRefusal::AsidOutOfRange(addr))
            } else {
                Ok(PhysicalWrite::InvalidateAsid(addr as u16))
            }
        }
        PHYSICAL_WRITE_STORE_USER_WORD => {
            if !addr.is_multiple_of(8) {
                Err(PhysicalWriteRefusal::Misaligned(addr))
            } else if !user_word_admissible(addr, covered) {
                Err(PhysicalWriteRefusal::NotAThreadPage(addr))
            } else {
                Ok(PhysicalWrite::StoreUserWord { addr, value })
            }
        }
        other => Err(PhysicalWriteRefusal::UnknownTag(other)),
    }
}

/// **WS-BP post-landing audit (`v0.36.32`): the instruction-cache maintenance a
/// physical write owes**, performed as the last step of
/// [`apply_physical_write`].
///
/// Lean model: `Architecture.PhysicalWrite.icacheMaintenance`.  A page zeroing
/// is a data write to a page a thread may later map **executable** (the carve
/// of a frame zeroes it before any capability to it exists), and the
/// Cortex-A76 has `CTR_EL0.IDC = DIC = 0`: the zeroes sit in the data cache
/// while the page's previous contents stay reachable at the Point of
/// Unification and in any instruction line still holding them.  So the zeroing
/// is followed by a clean of the page to the PoU and an `IC IALLUIS` —
/// `CleanRangeIallu`, the operand `zeroPage_discharges_obligation` proves
/// discharges the `.carveScrub` obligation.  Every other write owes nothing:
/// a descriptor and a user word land in pages no thread fetches from without a
/// later carve's own zeroing, and an ASID invalidation writes no memory.
#[must_use]
pub const fn icache_maintenance(write: PhysicalWrite) -> Option<crate::cache::ICacheInvalidation> {
    match write {
        PhysicalWrite::ZeroPage(page) => Some(crate::cache::ICacheInvalidation::CleanRangeIallu(
            page, PAGE_BYTES,
        )),
        PhysicalWrite::StoreDescriptor { .. }
        | PhysicalWrite::StoreTableDescriptor { .. }
        | PhysicalWrite::InvalidateAsid(_)
        | PhysicalWrite::StoreUserWord { .. } => None,
    }
}

/// Perform one validated physical write, then the instruction-cache maintenance
/// it owes ([`icache_maintenance`]).
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
        PhysicalWrite::StoreDescriptor { entry, value }
        | PhysicalWrite::StoreTableDescriptor { entry, value } => {
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
        PhysicalWrite::StoreUserWord { addr, value } => {
            #[cfg(target_arch = "aarch64")]
            {
                // SAFETY: `addr` passed `user_word_admissible`: an eight-byte
                // aligned word of a page of RAM past the kernel's reserved
                // extent, mapped Normal write-back by the kernel's identity
                // map.  No Rust reference aliases a thread's frame, and the
                // store is one aligned 64-bit write.
                unsafe {
                    core::ptr::write_volatile(addr as *mut u64, value);
                }
            }
            #[cfg(not(target_arch = "aarch64"))]
            let _ = (addr, value);
            crate::barriers::dsb_ish();
        }
    }
    // The maintenance follows the store and its `DSB ISH`, so the clean reads
    // the zeroes rather than the page's previous contents.  The host performs
    // none: `apply_icache_invalidation`'s host arms are no-ops too.
    if let Some(op) = icache_maintenance(write) {
        crate::cache::apply_icache_invalidation(op);
    }
}

/// **WS-BP BP7.8: read the user word at `addr`** — a sender's message register
/// past the four the trap frame carries, read out of its IPC buffer so the Lean
/// kernel decodes what the thread wrote rather than its model of memory.
///
/// **`v0.36.47` audit: a run, not a word.**  `[base, base + 8 · count)` is
/// admissible when `base` is a [`user_word_admissible`] word and the run stays
/// in `base`'s page (`base % PAGE_BYTES + 8 · count ≤ PAGE_BYTES`), so one
/// translation of the base covers every word of it and every word is itself
/// admissible.  The Lean kernel groups a sender's overflow slots into exactly
/// such runs (`IpcBufferRead.wordRuns`, with `wordRuns_within_page` the proof
/// that it never asks for a run leaving the page), so a refusal here is a
/// kernel defect and the caller halts.  A zero-length run at an admissible
/// base reads nothing.
#[must_use]
pub fn user_word_run_admissible(base: u64, count: u64, covered: impl Fn(u64, u64) -> bool) -> bool {
    let Some(bytes) = count.checked_mul(8) else {
        return false;
    };
    let Some(end_in_page) = (base % PAGE_BYTES).checked_add(bytes) else {
        return false;
    };
    user_word_admissible(base, covered) && end_in_page <= PAGE_BYTES
}

/// Read the admissible run `[base, base + 8 · count)` into `out` as `8 · count`
/// little-endian bytes, word by word.  `None` when the run is not
/// [`user_word_run_admissible`] or `out` is not exactly the run's size; the
/// caller halts.  On a host build the words read as zero, as the single-word
/// reader's did.
#[must_use]
pub fn read_user_words(
    base: u64,
    count: u64,
    covered: impl Fn(u64, u64) -> bool,
    out: &mut [u8],
) -> Option<()> {
    if !user_word_run_admissible(base, count, covered) {
        return None;
    }
    let Ok(count) = usize::try_from(count) else {
        return None;
    };
    if out.len() != count.checked_mul(8)? {
        return None;
    }
    for (i, slot) in out.chunks_exact_mut(8).enumerate() {
        #[allow(unused_variables)]
        let addr = base + 8 * i as u64;
        #[cfg(target_arch = "aarch64")]
        // SAFETY: as `apply_physical_write`'s user-word store: an admissible,
        // aligned word of a thread's RAM frame under the identity map — the
        // run check above admits every word of the run — one aligned 64-bit
        // load.
        let word = unsafe { core::ptr::read_volatile(addr as *const u64) };
        #[cfg(not(target_arch = "aarch64"))]
        let word = 0u64;
        slot.copy_from_slice(&word.to_le_bytes());
    }
    Some(())
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
        assert_eq!(PHYSICAL_WRITE_STORE_USER_WORD, 3);
        assert_eq!(PHYSICAL_WRITE_STORE_TABLE_DESCRIPTOR, 4);
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
            decode_physical_write(1, RAM_PAGE + 0x18, 0, covered),
            Ok(PhysicalWrite::StoreDescriptor {
                entry: RAM_PAGE + 0x18,
                value: 0
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
            decode_physical_write(4, RAM_PAGE + 8, 0, covered),
            Ok(PhysicalWrite::StoreTableDescriptor {
                entry: RAM_PAGE + 8,
                value: 0
            })
        );
        assert_eq!(
            decode_physical_write(5, RAM_PAGE, 0, covered),
            Err(PhysicalWriteRefusal::UnknownTag(5))
        );
    }

    /// A thread's page descriptor as the Lean kernel writes it
    /// (`Architecture.userPageDescriptorValue`): valid page, `AP`, inner
    /// shareable, access flag, not-global, PXN.
    fn user_page(oa: u64, attr: u64, uxn: bool) -> u64 {
        oa | DESC_PAGE_OR_TABLE
            | attr
            | (0b01 << 6)
            | DESC_SH
            | DESC_AF
            | DESC_NG
            | DESC_PXN
            | if uxn { DESC_UXN } else { 0 }
    }

    /// **PR #904 (`v0.36.41`): the HAL validates what a descriptor says.**
    /// Every case keeps the store's *address* admissible and changes only the
    /// value, so each refusal is the value check's and not the address's.
    #[test]
    fn a_descriptor_names_only_memory_a_thread_may_reach() {
        use crate::mmu::{BOOT_TABLE_POOL_BASE, DEVICE_WINDOW_BASE};
        let entry = RAM_PAGE + 0x18;
        let frame = RAM_PAGE + 0x3000;
        // CONTROL: a thread's RAM frame, Normal, as the model encodes it.
        let good = user_page(frame, DESC_ATTR_NORMAL, false);
        assert_eq!(
            decode_physical_write(1, entry, good, covered),
            Ok(PhysicalWrite::StoreDescriptor { entry, value: good })
        );
        // CONTROL: a device page, Device and execute-never.
        let dev = user_page(DEVICE_WINDOW_BASE, DESC_ATTR_DEVICE, true);
        assert!(page_descriptor_admissible(dev, covered));
        let refused = |v: u64| {
            decode_physical_write(1, entry, v, covered)
                == Err(PhysicalWriteRefusal::DescriptorRefused(v))
        };
        // A leaf naming the kernel's image, or a translation-table pool page.
        assert!(refused(user_page(0x8_0000, DESC_ATTR_NORMAL, true)));
        assert!(refused(user_page(
            BOOT_TABLE_POOL_BASE,
            DESC_ATTR_NORMAL,
            true
        )));
        // RAM mapped Device: an uncached alias of memory the kernel caches.
        assert!(refused(user_page(frame, DESC_ATTR_DEVICE, true)));
        // The device window mapped Normal, or executable at EL0.
        assert!(refused(user_page(
            DEVICE_WINDOW_BASE,
            DESC_ATTR_NORMAL,
            true
        )));
        assert!(refused(user_page(
            DEVICE_WINDOW_BASE,
            DESC_ATTR_DEVICE,
            false
        )));
        // Missing the access flag, not-global or PXN.
        assert!(refused(good & !DESC_AF));
        assert!(refused(good & !DESC_NG));
        assert!(refused(good & !DESC_PXN));
        // A block (`0b01`), an invalid non-zero value, and a stray bit.
        assert!(refused((good & !DESC_PAGE_OR_TABLE) | 0b01));
        assert!(refused(good & !1));
        assert!(refused(good | (1 << 52)));
        // An unknown memory type.
        assert!(refused(user_page(frame, 2 << 2, true)));
    }

    /// **PR #904 (`v0.36.41`)**: a table descriptor names a thread table page
    /// and carries nothing else — the walker would read any other page as a
    /// table of translations.
    #[test]
    fn a_table_descriptor_names_only_a_thread_table_page() {
        use crate::mmu::BOOT_TABLE_POOL_BASE;
        let entry = BOOT_TABLE_POOL_BASE + 8;
        for table in [BOOT_TABLE_POOL_BASE + 0x1000, RAM_PAGE] {
            let v = table | DESC_PAGE_OR_TABLE;
            assert_eq!(
                decode_physical_write(4, entry, v, covered),
                Ok(PhysicalWrite::StoreTableDescriptor { entry, value: v })
            );
        }
        let refused = |v: u64| {
            decode_physical_write(4, entry, v, covered)
                == Err(PhysicalWriteRefusal::DescriptorRefused(v))
        };
        // The kernel's image as a table, and RAM the boot map does not cover.
        assert!(refused(0x8_0000 | DESC_PAGE_OR_TABLE));
        assert!(refused(0x8000_0000 | DESC_PAGE_OR_TABLE));
        // A leaf-shaped value in a table entry: the walker would read the
        // frame it names as a table.
        assert!(refused(user_page(RAM_PAGE, DESC_ATTR_NORMAL, true)));
        // A hierarchical control the model never sets, and a block.
        assert!(refused(RAM_PAGE | DESC_PAGE_OR_TABLE | (1 << 63)));
        assert!(refused(RAM_PAGE | 0b01));
    }

    /// The carve's scrub owes a clean to the PoU and a domain-wide
    /// instruction-cache invalidation over exactly the zeroed page, and no
    /// other write owes any maintenance (`PhysicalWrite.icacheMaintenance`).
    #[test]
    fn a_zeroed_page_owes_a_clean_to_the_point_of_unification() {
        use crate::cache::ICacheInvalidation;
        assert_eq!(
            icache_maintenance(PhysicalWrite::ZeroPage(RAM_PAGE)),
            Some(ICacheInvalidation::CleanRangeIallu(RAM_PAGE, 4096))
        );
        assert_eq!(
            icache_maintenance(PhysicalWrite::StoreDescriptor {
                entry: RAM_PAGE,
                value: 3
            }),
            None
        );
        assert_eq!(icache_maintenance(PhysicalWrite::InvalidateAsid(7)), None);
        assert_eq!(
            icache_maintenance(PhysicalWrite::StoreUserWord {
                addr: RAM_PAGE,
                value: 1
            }),
            None
        );
    }

    /// Every page a zeroing may name is one the maintenance can reach, so the
    /// halt in `apply_icache_invalidation` is unreachable from this path: the
    /// decode admits a page by the same boot-map coverage the maintenance
    /// checks.  Exercised on a table-pool page, which lies inside the kernel's
    /// reserved extent the constant map always covers.
    #[test]
    fn an_admitted_zeroing_is_always_maintainable() {
        use crate::mmu::BOOT_TABLE_POOL_BASE;
        let pool_page = BOOT_TABLE_POOL_BASE;
        let write = decode_physical_write(0, pool_page, 0, crate::mmu::is_boot_cacheable_range)
            .expect("a pool page is a thread page");
        let op = icache_maintenance(write).expect("a zeroing owes maintenance");
        assert!(crate::cache::icache_operand_within_identity_map(op));
    }

    #[test]
    fn a_user_word_lands_only_in_a_thread_ram_page() {
        // WS-BP BP7.8: tag 3 is `PhysicalWrite.storeUserWord`.
        assert_eq!(PHYSICAL_WRITE_STORE_USER_WORD, 3);
        assert_eq!(
            decode_physical_write(3, RAM_PAGE + 0x20, 0x5c, covered),
            Ok(PhysicalWrite::StoreUserWord {
                addr: RAM_PAGE + 0x20,
                value: 0x5c
            })
        );
        assert_eq!(
            decode_physical_write(3, RAM_PAGE + 4, 1, covered),
            Err(PhysicalWriteRefusal::Misaligned(RAM_PAGE + 4))
        );
        // The kernel image, and a translation-table pool page, are refused:
        // a message register must never become a descriptor.
        assert_eq!(
            decode_physical_write(3, 0x8_0010, 1, covered),
            Err(PhysicalWriteRefusal::NotAThreadPage(0x8_0010))
        );
        let pool = crate::mmu::BOOT_TABLE_POOL_BASE;
        assert!(thread_page_admissible(pool, covered));
        assert_eq!(
            decode_physical_write(3, pool + 8, 1, covered),
            Err(PhysicalWriteRefusal::NotAThreadPage(pool + 8))
        );
        // RAM the boot map does not cover is refused.
        assert!(!user_word_admissible(RAM_PAGE, |_, _| false));
        // The read side answers exactly where the write side admits.
        let mut one = [0xAAu8; 8];
        assert_eq!(
            read_user_words(RAM_PAGE + 8, 1, covered, &mut one),
            Some(())
        );
        assert_eq!(one, [0u8; 8]);
        assert_eq!(read_user_words(pool, 1, covered, &mut one), None);
        assert_eq!(read_user_words(RAM_PAGE + 3, 1, covered, &mut one), None);
    }

    /// `v0.36.47` audit: a run of user words is admitted exactly when its base
    /// is an admissible word and the run stays in the base's page — the bound
    /// the Lean side proves it never exceeds (`wordRuns_within_page`).
    #[test]
    fn a_user_word_run_is_bounded_by_its_page() {
        // The exact run: 116 words (the longest overflow message) ending on
        // the last byte of the page.
        let exact = RAM_PAGE + PAGE_BYTES - 8 * 116;
        assert!(user_word_run_admissible(exact, 116, covered));
        let mut words = [0xAAu8; 8 * 116];
        assert_eq!(read_user_words(exact, 116, covered, &mut words), Some(()));
        assert!(words.iter().all(|b| *b == 0));
        // One word further: the run leaves the page and is refused, although
        // its base and all but its last word are admissible.
        let crossing = exact + 8;
        assert!(user_word_admissible(crossing, covered));
        assert!(user_word_admissible(crossing + 8 * 114, covered));
        assert!(!user_word_run_admissible(crossing, 116, covered));
        assert_eq!(read_user_words(crossing, 116, covered, &mut words), None);
        // Clipped to the page it is admitted again.
        assert!(user_word_run_admissible(crossing, 115, covered));
        // A zero-length run reads nothing — admitted at an admissible base,
        // refused where a single word would be.
        let mut none: [u8; 0] = [];
        assert!(user_word_run_admissible(RAM_PAGE, 0, covered));
        assert_eq!(read_user_words(RAM_PAGE, 0, covered, &mut none), Some(()));
        assert!(!user_word_run_admissible(RAM_PAGE + 4, 0, covered));
        assert!(!user_word_run_admissible(
            crate::mmu::BOOT_TABLE_POOL_BASE,
            0,
            covered
        ));
        // A buffer of the wrong size is refused rather than partly filled.
        let mut short = [0u8; 8];
        assert_eq!(read_user_words(RAM_PAGE, 2, covered, &mut short), None);
        // A count whose byte size overflows is refused, not wrapped.
        assert!(!user_word_run_admissible(RAM_PAGE, u64::MAX / 4, covered));
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
