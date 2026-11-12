// SPDX-License-Identifier: GPL-3.0-or-later
//! **The region map**: which recorded range, if any, holds an address of
//! region RAM.  It is the only thing the allocator asks to find a range, and
//! it is the only module that would change under another map design.
//!
//! The map keeps **one byte per [`GRANULE`] of covered RAM**.  The byte is `0`
//! when no recorded range covers the granule.  Otherwise it is the log2 size
//! of the range that does.  A range is a naturally aligned power-of-two block
//! of at least one granule, so a granule lies in at most one range.  The
//! range's base is the address with its low `log2` bits cleared.
//!
//! The map never reads the memory it describes.  Lookups and changes are
//! arithmetic on addresses plus loads and stores of the map's own bytes.  A
//! range's bytes, and the padding between ranges, can hold anything (stale
//! frame contents, a thread's saved registers), and none of it can make an
//! address resolve to a range that was not recorded.
//!
//! **The map's invariant**: every granule of a recorded range holds that
//! range's log2, and every nonzero byte belongs to a range recorded with that
//! log2.  [`RangeMap::record`] refuses a range that meets a recorded one, and
//! [`RangeMap::unrecord`] clears a whole range, so neither can leave a range
//! half described.

use core::sync::atomic::{AtomicU8, Ordering};

/// Log2 of the map's granule: 512 bytes, which is also the smallest range.
pub const GRANULE_LOG2: u32 = 9;
/// The map's granule, in bytes.
pub const GRANULE: usize = 1 << GRANULE_LOG2;
/// Log2 of the smallest range the map records: one granule.
pub const MIN_RANGE_LOG2: u32 = GRANULE_LOG2;
/// Log2 of the largest range the map records: a 48-bit physical space.
pub const MAX_RANGE_LOG2: u32 = 47;

/// A naturally aligned block of `2^log2` bytes at `base`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range {
    /// The first byte: a multiple of the range's size.
    pub base: usize,
    /// Log2 of the range's size, in `MIN_RANGE_LOG2..=MAX_RANGE_LOG2`.
    pub log2: u32,
}

impl Range {
    /// The range at `base` of `2^log2` bytes, or `None` when the size is out
    /// of bounds, the base is not a multiple of it, or the end wraps.
    #[must_use]
    pub fn new(base: usize, log2: u32) -> Option<Self> {
        if !(MIN_RANGE_LOG2..=MAX_RANGE_LOG2).contains(&log2)
            || log2 >= usize::BITS
            || base & ((1usize << log2) - 1) != 0
        {
            return None;
        }
        base.checked_add(1usize << log2)?;
        Some(Self { base, log2 })
    }

    /// The range's bytes.
    #[must_use]
    pub const fn size(&self) -> usize {
        1 << self.log2
    }

    /// One past the range's last byte.
    #[must_use]
    pub const fn end(&self) -> usize {
        self.base + self.size()
    }

    /// Whether `addr` lies in the range.
    #[must_use]
    pub const fn contains(&self, addr: usize) -> bool {
        self.base <= addr && addr < self.end()
    }
}

/// Why the map refused a change.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MapRefusal {
    /// The range is not wholly inside the RAM this map covers.
    Uncovered,
    /// A recorded range meets the range to be recorded.
    Overlap,
    /// The range to unrecord is not recorded as given.
    NotRecorded,
}

/// The map over `[base, base + granules.len() * GRANULE)`.
pub struct RangeMap<'a> {
    base: usize,
    granules: &'a [AtomicU8],
}

impl<'a> RangeMap<'a> {
    /// The bytes of map storage that `len` bytes of covered RAM need.
    #[must_use]
    pub const fn storage_bytes(len: usize) -> usize {
        len >> GRANULE_LOG2
    }

    /// A map over the RAM at `base` that `granules` describes, one byte per
    /// granule, or `None` when `base` is not granule-aligned or the extent
    /// wraps.  The bytes are taken as they are, so a fresh map is zeroed
    /// storage.
    #[must_use]
    pub fn new(base: usize, granules: &'a [AtomicU8]) -> Option<Self> {
        if !base.is_multiple_of(GRANULE) {
            return None;
        }
        granules.len().checked_mul(GRANULE)?.checked_add(base)?;
        Some(Self { base, granules })
    }

    /// The first covered byte.
    #[must_use]
    pub const fn base(&self) -> usize {
        self.base
    }

    /// One past the last covered byte.
    #[must_use]
    pub fn end(&self) -> usize {
        self.base + self.granules.len() * GRANULE
    }

    /// Whether every byte of `[lo, hi)` is covered.
    #[must_use]
    pub fn covers(&self, lo: usize, hi: usize) -> bool {
        self.base <= lo && lo <= hi && hi <= self.end()
    }

    fn granule(&self, addr: usize) -> &AtomicU8 {
        &self.granules[(addr - self.base) >> GRANULE_LOG2]
    }

    /// The recorded range holding `addr`, or `None` when no recorded range
    /// does or the map does not cover `addr`.
    #[must_use]
    pub fn range_of(&self, addr: usize) -> Option<Range> {
        if !self.covers(addr, addr.checked_add(1)?) {
            return None;
        }
        let log2 = u32::from(self.granule(addr).load(Ordering::Acquire));
        if log2 == 0 {
            return None;
        }
        Range::new(addr & !((1usize << log2) - 1), log2)
    }

    /// Calls `f` once for each recorded range that meets `[lo, hi)`, in
    /// address order.  The part of `[lo, hi)` the map does not cover holds no
    /// recorded range.
    pub fn for_each_meeting(&self, lo: usize, hi: usize, mut f: impl FnMut(Range)) {
        let mut at = lo.max(self.base) & !(GRANULE - 1);
        let hi = hi.min(self.end());
        while at < hi {
            match self.range_of(at) {
                Some(range) => {
                    f(range);
                    at = range.end();
                }
                None => at += GRANULE,
            }
        }
    }

    /// Records `range`.
    ///
    /// # Errors
    ///
    /// `Uncovered` when the map does not cover it, `Overlap` when a recorded
    /// range meets it.  Either way nothing is written.
    pub fn record(&self, range: Range) -> Result<(), MapRefusal> {
        if !self.covers(range.base, range.end()) {
            return Err(MapRefusal::Uncovered);
        }
        let mut meets = false;
        self.for_each_meeting(range.base, range.end(), |_| meets = true);
        if meets {
            return Err(MapRefusal::Overlap);
        }
        // `log2 <= MAX_RANGE_LOG2 < 256`, so it fits in the byte.
        let byte = range.log2 as u8;
        let mut at = range.base;
        while at < range.end() {
            self.granule(at).store(byte, Ordering::Release);
            at += GRANULE;
        }
        Ok(())
    }

    /// Unrecords `range`, which must be recorded exactly as given.
    ///
    /// # Errors
    ///
    /// `NotRecorded` otherwise, with nothing written.
    pub fn unrecord(&self, range: Range) -> Result<(), MapRefusal> {
        if self.range_of(range.base) != Some(range) {
            return Err(MapRefusal::NotRecorded);
        }
        let mut at = range.base;
        while at < range.end() {
            self.granule(at).store(0, Ordering::Release);
            at += GRANULE;
        }
        Ok(())
    }
}
