// SPDX-License-Identifier: GPL-3.0-or-later
//! **The region allocator**: cells a carve builds in its untyped's own
//! memory, as seL4 builds an object in the untyped it is retyped from.
//!
//! A **range** is a naturally aligned power-of-two block of RAM, at least
//! [`map::GRANULE`] bytes, which one carve's cells are bumped into.  The range
//! starts with its **header**, a set of 8-byte words:
//!
//! | word | holds |
//! |------|-------|
//! | 0 | the range's log2 size |
//! | 1 | the **live count**: the range's cells not yet freed (atomic) |
//! | 2 | the **bump cursor**: the offset of the next cell |
//! | 3 .. 3 + W | the **cell-start bitmap**: bit `i` set when a cell starts at offset `8i` |
//! | 3 + W .. 3 + 2W | the **live bitmap**: bit `i` set while that cell is live |
//!
//! `W` is [`bitmap_words`], one bit per 8 bytes of the range, so the header is
//! [`header_bytes`] bytes, `24 + size / 32`.  Under the kernel's
//! `LEAN_SMALL_ALLOCATOR` configuration a Lean object's header has no spare
//! bits (`m_cs_sz = 0`).  So the start bitmap is the only record of a region
//! cell's size: a cell ends where the next one starts, or at the cursor.
//!
//! **The map** ([`map`]) is what finds a range.  It keeps a byte per
//! granule, outside every range, and nothing in a range's own bytes decides
//! which range an address is in.  A recorded range's header holds only what
//! [`Region::begin_range`] wrote there.
//!
//! **A free decrements the live count without a lock and never reuses the
//! bytes.**  It clears the cell's live bit with one atomic `fetch_and`, which
//! also refuses a double free, and then decrements the count.  The bytes
//! return only when the range is begun again, as seL4's `resetUntypedCap`
//! returns an untyped's bytes.
//!
//! **The backstop.**  Bytes are handed out again in two places: a new range's
//! header is initialised over them ([`Region::begin_range`]), or a page is
//! zeroed for a frame ([`admit_page_zero`]).  Each asks the map for every
//! recorded range meeting the bytes.  If any of those ranges has a live count
//! above 0, the request halts.  Otherwise the ranges are unrecorded.  The
//! carve's design makes this unreachable; the halt is only a backstop.
//!
//! **The allocation context.**  Each core has one word: `0`, or the base of
//! the range its allocations go to.  `lean_heap`'s allocation entries consult
//! it, and the heap serves the allocation when the word is `0`.  It is set
//! only through [`enter_context`], which masks interrupts until its guard is
//! dropped, so an interrupt's allocations cannot land in a carve's range.

pub mod map;

#[cfg(test)]
pub(crate) mod tests;

use core::sync::atomic::{AtomicU64, AtomicU8, AtomicUsize, Ordering};

use self::map::{MapRefusal, Range, RangeMap};
use crate::lean_heap::HEAP_COUNTED_CORES;
use crate::ticket_lock::TicketLock;

/// Every cell starts at a multiple of this, and every cell's size is one.
pub const CELL_ALIGN: usize = 8;

/// Words of each of a range's two bitmaps: one bit per [`CELL_ALIGN`] bytes.
#[must_use]
pub const fn bitmap_words(log2: u32) -> usize {
    ((1usize << log2) / CELL_ALIGN).div_ceil(64)
}

/// Words of a range's header (the module's table).
#[must_use]
pub const fn header_words(log2: u32) -> usize {
    3 + 2 * bitmap_words(log2)
}

/// Bytes of a range's header: the offset of its first cell.
#[must_use]
pub const fn header_bytes(log2: u32) -> usize {
    header_words(log2) * 8
}

const LOG2_WORD: usize = 0;
const LIVE_WORD: usize = 1;
const CURSOR_WORD: usize = 2;
const STARTS_WORD: usize = 3;

/// Why a region request was refused.  On the image every one halts the
/// system; the host tests read them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegionFault {
    /// The address is in no recorded range.
    NotRegion,
    /// The range's base is not a multiple of its size, or its size is out of
    /// bounds.
    Misaligned,
    /// The range is not wholly inside RAM the region map covers.
    Uncovered,
    /// The address is not the start of a cell of its range.
    NotAtStart,
    /// The cell was freed already.
    NotLive,
    /// A header disagrees with the map or with itself.
    Corrupt,
    /// The backstop: bytes about to be handed out again lie in a recorded
    /// range whose live count is above 0.
    LiveRange {
        /// The live range's base.
        base: usize,
        /// Its log2 size.
        log2: u32,
        /// Its live count.
        live: u64,
    },
    /// A bump would pass the range's end.
    PastEnd {
        /// The range's base.
        base: usize,
        /// Its log2 size.
        log2: u32,
        /// The cursor before the bump.
        cursor: usize,
        /// The bytes asked for.
        size: usize,
    },
    /// An alignment beyond [`CELL_ALIGN`] was asked for.
    Alignment,
    /// The core already has an allocation context.
    ContextBusy,
    /// The map has no room for another extent of RAM.
    MapFull,
    /// The map's storage could not be allocated.
    MapStorage,
}

impl From<MapRefusal> for RegionFault {
    fn from(refusal: MapRefusal) -> Self {
        match refusal {
            MapRefusal::Uncovered => Self::Uncovered,
            MapRefusal::Overlap | MapRefusal::NotRecorded => Self::Corrupt,
        }
    }
}

/// A recorded range's header, as words.
struct Header<'r> {
    range: Range,
    words: &'r [AtomicU64],
}

impl Header<'_> {
    fn bitmap(&self) -> usize {
        bitmap_words(self.range.log2)
    }

    fn start_word(&self, index: usize) -> &AtomicU64 {
        &self.words[STARTS_WORD + index / 64]
    }

    fn live_word(&self, index: usize) -> &AtomicU64 {
        &self.words[STARTS_WORD + self.bitmap() + index / 64]
    }

    fn cursor(&self) -> usize {
        self.words[CURSOR_WORD].load(Ordering::Acquire) as usize
    }

    fn live(&self) -> u64 {
        self.words[LIVE_WORD].load(Ordering::Acquire)
    }

    fn is_start(&self, index: usize) -> bool {
        self.start_word(index).load(Ordering::Acquire) & (1 << (index % 64)) != 0
    }

    fn is_live(&self, index: usize) -> bool {
        self.live_word(index).load(Ordering::Acquire) & (1 << (index % 64)) != 0
    }
}

/// The allocator over the RAM one [`RangeMap`] covers.
pub struct Region<'a> {
    map: RangeMap<'a>,
}

impl<'a> Region<'a> {
    /// The allocator over `map`'s RAM.
    ///
    /// # Safety
    ///
    /// Every byte `map` covers must be memory this allocator may read and
    /// write for as long as it lives, and no Rust reference may alias it.  A
    /// range's header is written only through this allocator.  Its cells are
    /// handed to Lean code, which writes inside them only.
    #[must_use]
    pub const unsafe fn new(map: RangeMap<'a>) -> Self {
        Self { map }
    }

    /// The header of `range`, which the map records.
    fn header(&self, range: Range) -> Header<'a> {
        // SAFETY: `range` is covered by the map (it was recorded, or it is
        // being begun and `begin_range` checked coverage).  `Region::new`'s
        // contract makes covered memory ours to access, and its first
        // `header_bytes` bytes are the header, which only this allocator
        // touches.  `AtomicU64` has the size and alignment of `u64`, and every
        // range base is at least 512-byte aligned.
        let words = unsafe {
            core::slice::from_raw_parts(range.base as *const AtomicU64, header_words(range.log2))
        };
        Header { range, words }
    }

    /// Calls `f` with each recorded range meeting `[lo, hi)` whose live count
    /// is above 0, and that count.  This is the backstop's query.  It finds
    /// ranges through the map only, so bytes outside every recorded range,
    /// such as padding, stale contents or a forged header, are never read.
    pub fn for_each_live_range(&self, lo: usize, hi: usize, mut f: impl FnMut(Range, u64)) {
        self.map.for_each_meeting(lo, hi, |range| {
            let live = self.header(range).live();
            if live > 0 {
                f(range, live);
            }
        });
    }

    /// The backstop.  It refuses to hand out `[lo, hi)` again while any
    /// recorded range meeting it has a live count above 0.  Otherwise it
    /// unrecords every range meeting it.
    ///
    /// # Errors
    ///
    /// `LiveRange` naming the first live range, with nothing changed.
    pub fn retire_meeting(&self, lo: usize, hi: usize) -> Result<(), RegionFault> {
        let mut first = None;
        self.for_each_live_range(lo, hi, |range, live| {
            first.get_or_insert(RegionFault::LiveRange {
                base: range.base,
                log2: range.log2,
                live,
            });
        });
        if let Some(fault) = first {
            return Err(fault);
        }
        let mut refused = None;
        self.map.for_each_meeting(lo, hi, |range| {
            if let Err(e) = self.map.unrecord(range) {
                refused.get_or_insert(RegionFault::from(e));
            }
        });
        refused.map_or(Ok(()), Err)
    }

    /// Begins the range of `2^log2` bytes at `base`.  The backstop runs
    /// first ([`Region::retire_meeting`]).  Then the header is initialised,
    /// with a live count of 0, empty bitmaps and the cursor just past the
    /// header, and the range is recorded.
    ///
    /// # Errors
    ///
    /// `Misaligned` or `Uncovered` for a range the map cannot hold.
    /// `LiveRange` from the backstop.  On every error nothing is written.
    pub fn begin_range(&self, base: usize, log2: u32) -> Result<Range, RegionFault> {
        let range = Range::new(base, log2).ok_or(RegionFault::Misaligned)?;
        if !self.map.covers(range.base, range.end()) {
            return Err(RegionFault::Uncovered);
        }
        self.retire_meeting(range.base, range.end())?;
        let header = self.header(range);
        header.words[LOG2_WORD].store(u64::from(log2), Ordering::Relaxed);
        header.words[LIVE_WORD].store(0, Ordering::Relaxed);
        for word in &header.words[STARTS_WORD..] {
            word.store(0, Ordering::Relaxed);
        }
        header.words[CURSOR_WORD].store(header_bytes(log2) as u64, Ordering::Release);
        self.map.record(range)?;
        Ok(range)
    }

    /// The recorded range whose base is `base`, with its header checked
    /// against the map.
    fn recorded(&self, base: usize) -> Result<Header<'a>, RegionFault> {
        let range = self.map.range_of(base).ok_or(RegionFault::NotRegion)?;
        if range.base != base {
            return Err(RegionFault::NotRegion);
        }
        self.checked_header(range)
    }

    fn checked_header(&self, range: Range) -> Result<Header<'a>, RegionFault> {
        let header = self.header(range);
        let cursor = header.cursor();
        if header.words[LOG2_WORD].load(Ordering::Relaxed) != u64::from(range.log2)
            || cursor < header_bytes(range.log2)
            || cursor > range.size()
        {
            return Err(RegionFault::Corrupt);
        }
        Ok(header)
    }

    /// The live count of the range recorded at `base`.
    ///
    /// # Errors
    ///
    /// `NotRegion` when no range is recorded there.
    pub fn live_count(&self, base: usize) -> Result<u64, RegionFault> {
        Ok(self.recorded(base)?.live())
    }

    /// Bumps a cell of `size` bytes, rounded up to [`CELL_ALIGN`], into the
    /// range recorded at `base`.  Only the core whose context names the range
    /// allocates into it.
    ///
    /// # Errors
    ///
    /// `NotRegion` when no range is recorded at `base`.  `PastEnd` when the
    /// cell would pass the range's end; a cell that ends exactly at the end
    /// is served.
    pub fn alloc(&self, base: usize, size: usize) -> Result<usize, RegionFault> {
        let header = self.recorded(base)?;
        let cursor = header.cursor();
        let past_end = RegionFault::PastEnd {
            base,
            log2: header.range.log2,
            cursor,
            size,
        };
        let bytes = size
            .max(1)
            .checked_next_multiple_of(CELL_ALIGN)
            .ok_or(past_end)?;
        let end = cursor.checked_add(bytes).ok_or(past_end)?;
        if end > header.range.size() {
            return Err(past_end);
        }
        let index = cursor / CELL_ALIGN;
        let bit = 1u64 << (index % 64);
        header.start_word(index).fetch_or(bit, Ordering::AcqRel);
        header.live_word(index).fetch_or(bit, Ordering::AcqRel);
        header.words[LIVE_WORD].fetch_add(1, Ordering::AcqRel);
        header.words[CURSOR_WORD].store(end as u64, Ordering::Release);
        Ok(base + cursor)
    }

    /// The header and bitmap index of the live cell starting at `addr`.
    fn live_cell(&self, addr: usize) -> Result<(Header<'a>, usize), RegionFault> {
        let range = self.map.range_of(addr).ok_or(RegionFault::NotRegion)?;
        let header = self.checked_header(range)?;
        let offset = addr - range.base;
        if !offset.is_multiple_of(CELL_ALIGN)
            || offset < header_bytes(range.log2)
            || offset >= header.cursor()
            || !header.is_start(offset / CELL_ALIGN)
        {
            return Err(RegionFault::NotAtStart);
        }
        Ok((header, offset / CELL_ALIGN))
    }

    /// Frees the live cell at `addr`.  The cell's live bit is cleared and the
    /// range's live count decremented, both with atomics and no lock.  The
    /// bytes are never handed out again until the range is begun again.
    ///
    /// # Errors
    ///
    /// `NotRegion`, `NotAtStart`, or `NotLive` for a cell freed already, with
    /// nothing changed.  `Corrupt` when the count is already 0.
    pub fn free(&self, addr: usize) -> Result<(), RegionFault> {
        let (header, index) = self.live_cell(addr)?;
        let bit = 1u64 << (index % 64);
        if header.live_word(index).fetch_and(!bit, Ordering::AcqRel) & bit == 0 {
            return Err(RegionFault::NotLive);
        }
        let counted =
            header.words[LIVE_WORD].fetch_update(Ordering::AcqRel, Ordering::Acquire, |live| {
                live.checked_sub(1)
            });
        counted.map(|_| ()).map_err(|_| RegionFault::Corrupt)
    }

    /// The bytes of the live cell at `addr`: from its start to the next
    /// cell's start, or to the cursor when it is the last cell.
    ///
    /// # Errors
    ///
    /// `NotRegion`, `NotAtStart`, or `NotLive` for a freed cell.
    pub fn cell_size(&self, addr: usize) -> Result<usize, RegionFault> {
        let (header, index) = self.live_cell(addr)?;
        if !header.is_live(index) {
            return Err(RegionFault::NotLive);
        }
        let last = header.cursor() / CELL_ALIGN;
        let mut next = index + 1;
        while next < last {
            let word = header.start_word(next).load(Ordering::Acquire) >> (next % 64);
            if word != 0 {
                next += word.trailing_zeros() as usize;
                break;
            }
            next = (next / 64 + 1) * 64;
        }
        Ok((next.min(last) - index) * CELL_ALIGN)
    }
}

// ==========================================================================
// The kernel's region: one map segment per extent of RAM the boot map covers
// ==========================================================================

/// The extents of RAM the kernel's map can cover: one per boot RAM extension
/// (`mmu::MAX_RAM_EXTENSIONS`).
pub const MAX_SEGMENTS: usize = crate::mmu::MAX_RAM_EXTENSIONS;

/// One covered extent: its base, its length and its map's storage.  Written
/// once at boot, before [`SEGMENT_COUNT`] publishes it.
struct Segment {
    base: AtomicUsize,
    len: AtomicUsize,
    storage: AtomicUsize,
}

#[allow(clippy::declare_interior_mutable_const)]
const EMPTY_SEGMENT: Segment = Segment {
    base: AtomicUsize::new(0),
    len: AtomicUsize::new(0),
    storage: AtomicUsize::new(0),
};

static SEGMENTS: [Segment; MAX_SEGMENTS] = [EMPTY_SEGMENT; MAX_SEGMENTS];
static SEGMENT_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Serialises the kernel region's changes: registering RAM, beginning a
/// range and admitting a zero.  A leaf lock that frees never take.
static CHANGE_LOCK: TicketLock = TicketLock::new();

/// Per core, the base of the range its allocations go to, or `0`.
#[allow(clippy::declare_interior_mutable_const)]
const NO_CONTEXT: AtomicUsize = AtomicUsize::new(0);
static CONTEXT: [AtomicUsize; HEAP_COUNTED_CORES] = [NO_CONTEXT; HEAP_COUNTED_CORES];

/// The kernel region over segment `i`, which is published.
fn segment(i: usize) -> Option<Region<'static>> {
    let s = &SEGMENTS[i];
    let base = s.base.load(Ordering::Relaxed);
    let granules = RangeMap::storage_bytes(s.len.load(Ordering::Relaxed));
    let storage = s.storage.load(Ordering::Relaxed) as *const AtomicU8;
    // SAFETY: a published segment's storage is `granules` bytes that
    // `register_ram` took for the map and nothing else names.
    let granules = unsafe { core::slice::from_raw_parts(storage, granules) };
    // SAFETY: `register_ram`'s contract makes the segment's RAM the region's.
    RangeMap::new(base, granules).map(|map| unsafe { Region::new(map) })
}

/// Every published segment's region.
fn segments() -> impl Iterator<Item = Region<'static>> {
    let count = SEGMENT_COUNT.load(Ordering::Acquire).min(MAX_SEGMENTS);
    (0..count).filter_map(segment)
}

/// The published segment's region covering every byte of `[lo, hi)`.
fn segment_covering(lo: usize, hi: usize) -> Option<Region<'static>> {
    segments().find(|region| region.map.covers(lo, hi))
}

/// Runs `f` under [`CHANGE_LOCK`] with interrupts masked, as the heap's own
/// lock runs: a ticket lock is not re-entrant.
fn with_change_lock<R>(f: impl FnOnce() -> R) -> R {
    let saved_daif = crate::interrupts::disable_interrupts();
    let result = CHANGE_LOCK.with_lock(f);
    crate::interrupts::restore_interrupts(saved_daif);
    result
}

/// Puts `[base, base + len)` under the kernel's map, with `storage` as the
/// map's `len / GRANULE` bytes, which must read as zero.
///
/// # Safety
///
/// `[base, base + len)` must be RAM the kernel may read and write at its own
/// address for the rest of its life, which no Rust reference aliases.
/// `storage` must be that many bytes nothing else will ever name.
///
/// # Errors
///
/// `Misaligned` for an extent that is not whole granules, `Uncovered` for
/// one meeting a registered extent, `MapFull` with every segment taken.
pub unsafe fn register_ram(base: usize, len: usize, storage: usize) -> Result<(), RegionFault> {
    with_change_lock(|| {
        let count = SEGMENT_COUNT.load(Ordering::Acquire);
        if count >= MAX_SEGMENTS {
            return Err(RegionFault::MapFull);
        }
        if !base.is_multiple_of(map::GRANULE)
            || !len.is_multiple_of(map::GRANULE)
            || base.checked_add(len).is_none()
        {
            return Err(RegionFault::Misaligned);
        }
        if segments().any(|r| base < r.map.end() && r.map.base() < base + len) {
            return Err(RegionFault::Uncovered);
        }
        let s = &SEGMENTS[count];
        s.base.store(base, Ordering::Relaxed);
        s.len.store(len, Ordering::Relaxed);
        s.storage.store(storage, Ordering::Relaxed);
        SEGMENT_COUNT.store(count + 1, Ordering::Release);
        Ok(())
    })
}

/// Puts a boot RAM extension under the kernel's map, taking the map's
/// storage from the kernel heap: [`map::RangeMap::storage_bytes`] of it,
/// whole pages, zeroed.  `ffi_extend_boot_ram_map` calls it once per
/// extension, after the boot map covers the extension.
///
/// # Safety
///
/// As [`register_ram`] for `[base, base + len)`.
///
/// # Errors
///
/// `MapStorage` when the heap cannot serve the storage, and
/// [`register_ram`]'s refusals.
pub unsafe fn register_boot_ram(base: usize, len: usize) -> Result<(), RegionFault> {
    let bytes = RangeMap::storage_bytes(len);
    if bytes == 0 {
        return Err(RegionFault::Misaligned);
    }
    let storage = crate::lean_heap::kernel_alloc(bytes, crate::lean_heap::PAGE_SIZE)
        .map_err(|_| RegionFault::MapStorage)?;
    // SAFETY: `storage` is a live heap allocation of at least `bytes` bytes,
    // which this function owns and never frees.
    unsafe { core::ptr::write_bytes(storage as *mut u8, 0, bytes) };
    // SAFETY: the caller's contract, and `storage` is ours alone.
    unsafe { register_ram(base, len, storage) }
}

/// The backstop at a page's zeroing (`user_translation::apply_physical_write`):
/// it refuses while any recorded range meeting `[page, page + len)` has a
/// live count above 0, and otherwise unrecords them, so a frame's contents
/// can never be read as a range's header.
///
/// # Errors
///
/// `LiveRange` naming the first live range, with nothing changed.
pub fn admit_page_zero(page: usize, len: usize) -> Result<(), RegionFault> {
    let hi = page.saturating_add(len);
    with_change_lock(|| {
        let mut first = None;
        for region in segments() {
            region.for_each_live_range(page, hi, |range, live| {
                first.get_or_insert(RegionFault::LiveRange {
                    base: range.base,
                    log2: range.log2,
                    live,
                });
            });
        }
        if let Some(fault) = first {
            return Err(fault);
        }
        segments().try_for_each(|region| region.retire_meeting(page, hi))
    })
}

/// This core's slot of [`CONTEXT`].
fn this_core_context() -> Option<&'static AtomicUsize> {
    CONTEXT.get(crate::per_cpu::current_core_id_from_tpidr() as usize)
}

/// A core's allocation context while it is held: this core's allocations go
/// to one range, with interrupts masked.  Dropping it clears the context and
/// restores the interrupt mask.
#[must_use = "the context ends when the guard is dropped"]
pub struct ContextGuard {
    slot: &'static AtomicUsize,
    saved_daif: u64,
}

impl Drop for ContextGuard {
    fn drop(&mut self) {
        self.slot.store(0, Ordering::Release);
        crate::interrupts::restore_interrupts(self.saved_daif);
    }
}

/// Begins the range of `2^log2` bytes at `base` ([`Region::begin_range`])
/// and sends this core's allocations to it until the guard is dropped.
///
/// # Errors
///
/// `ContextBusy` when this core already holds a context.  Otherwise
/// [`Region::begin_range`]'s refusals, or `Uncovered` when no segment covers
/// the range.  On every error the context and the interrupt mask are as
/// they were.
pub fn enter_context(base: usize, log2: u32) -> Result<ContextGuard, RegionFault> {
    let saved_daif = crate::interrupts::disable_interrupts();
    let begun = this_core_context()
        .filter(|slot| slot.load(Ordering::Acquire) == 0)
        .ok_or(RegionFault::ContextBusy)
        .and_then(|slot| {
            let range = Range::new(base, log2).ok_or(RegionFault::Misaligned)?;
            with_change_lock(|| {
                segment_covering(range.base, range.end())
                    .ok_or(RegionFault::Uncovered)?
                    .begin_range(base, log2)
            })?;
            slot.store(base, Ordering::Release);
            Ok(slot)
        });
    match begun {
        Ok(slot) => Ok(ContextGuard { slot, saved_daif }),
        Err(fault) => {
            crate::interrupts::restore_interrupts(saved_daif);
            Err(fault)
        }
    }
}

/// The allocation entries' question: when this core has a context, a cell of
/// `size` bytes aligned to `align` from its range (`Some`); otherwise
/// `None`, and the heap serves the request.  A refused request takes nothing.
#[must_use]
pub fn context_alloc(size: usize, align: usize) -> Option<Result<usize, RegionFault>> {
    let base = this_core_context()?.load(Ordering::Acquire);
    if base == 0 {
        return None;
    }
    if align > CELL_ALIGN {
        return Some(Err(RegionFault::Alignment));
    }
    Some(
        segment_covering(base, base + 1)
            .ok_or(RegionFault::NotRegion)
            .and_then(|region| region.alloc(base, size)),
    )
}

/// The kernel region's segment holding `addr`.
fn holding(addr: usize) -> Result<Region<'static>, RegionFault> {
    segment_covering(addr, addr.checked_add(1).ok_or(RegionFault::NotRegion)?)
        .ok_or(RegionFault::NotRegion)
}

/// Frees the region cell at `addr` ([`Region::free`]), with no lock.
///
/// # Errors
///
/// As [`Region::free`]; `NotRegion` when no segment covers `addr`.
pub fn kernel_free(addr: usize) -> Result<(), RegionFault> {
    holding(addr)?.free(addr)
}

/// The bytes of the region cell at `addr` ([`Region::cell_size`]).
///
/// # Errors
///
/// As [`Region::cell_size`]; `NotRegion` when no segment covers `addr`.
pub fn kernel_cell_size(addr: usize) -> Result<usize, RegionFault> {
    holding(addr)?.cell_size(addr)
}

/// The live count of the kernel range recorded at `base`.
///
/// # Errors
///
/// `NotRegion` when none is recorded there.
pub fn kernel_live_count(base: usize) -> Result<u64, RegionFault> {
    holding(base)?.live_count(base)
}

/// The fail-closed end of a region refusal on the image: name it and halt
/// the system, as the heap halts on its own faults.  The host has no system
/// to halt, so a host build panics.
pub fn halt(fault: RegionFault) -> ! {
    crate::kprintln!("[region] FATAL: {:?}", fault);
    #[cfg(target_arch = "aarch64")]
    {
        crate::gic::halt_all()
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        panic!("region fault: {fault:?}")
    }
}
