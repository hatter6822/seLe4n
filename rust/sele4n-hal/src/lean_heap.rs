//! **WS-BP BP2.1**: the Lean heap — an arena the linker script places, and the
//! allocator behind the Lean runtime's small-object API.
//!
//! The kernel's Lean object code is compiled against
//! `rust/sele4n-hal/lean_include/lean/config.h`, which selects
//! `LEAN_SMALL_ALLOCATOR` (BP1.2).  Under that configuration every inline
//! allocation path in `lean.h` — `lean_alloc_small_object`,
//! `lean_alloc_ctor_memory`, `lean_free_small_object`, `lean_small_object_size`
//! — calls exactly three functions, and this module is where they live:
//!
//! | `lean.h` declaration | Here |
//! |----------------------|------|
//! | `void * lean_alloc_small(unsigned sz, unsigned slot_idx)` | [`Heap::alloc_small`] |
//! | `void lean_free_small(void * p)` | [`Heap::free_small`] |
//! | `unsigned lean_small_mem_size(void * p)` | [`Heap::small_size`] |
//!
//! Objects above `LEAN_MAX_SMALL_OBJECT_SIZE` go through the runtime's
//! `lean_alloc_object`, whose big path is `malloc`; that is BP2.2's libc surface,
//! and it is served by [`Heap::alloc`] / [`Heap::free`] from **the same arena**,
//! so the kernel has one heap and one exhaustion condition, never two.
//!
//! # The arena is a link-time constant
//!
//! `link.ld` places a `NOLOAD` section `.lean_heap` and names its bounds
//! `__lean_heap_start` / `__lean_heap_end`.  The extent is decided when the
//! image is linked — not negotiated with firmware, not read from a device tree —
//! and `link.ld` refuses (`ASSERT`) an image whose arena does not end inside
//! the smallest Raspberry Pi 5's RAM, so "the heap does not fit" is a link error
//! rather than a boot-time surprise.  Everything the allocator needs is derived
//! from those two symbols: [`ArenaLayout::of`] carves its metadata from the
//! arena's leading pages and serves the rest.
//!
//! # All allocator state is out of band
//!
//! A page map, a free-page bitmap and a per-page occupancy bitmap live in the
//! arena's metadata pages; **no allocator state is stored inside an object**.
//! Three consequences, each the reason for the choice:
//!
//! * **The allocator never dereferences the memory it hands out.**  Every
//!   operation is arithmetic on addresses and safe indexing into the metadata
//!   slices, so the only `unsafe` in the module is the one place the metadata
//!   slices are formed over the arena ([`Heap::from_arena`]).  A Lean object that
//!   writes past its end corrupts its neighbour, never the allocator.
//! * **Every free is checked, in release builds.**  An address outside the arena,
//!   inside a free page, not at an object boundary, or naming an object that is
//!   not live is a [`HeapFault`]; a double free is therefore detected rather than
//!   silently corrupting a free list.  The Lean-facing wrappers halt on one.
//! * **Every operation is bounded.**  A small allocation scans at most eight
//!   words of one page's occupancy map; a page allocation scans the free-page
//!   bitmap from a hint below which no page is free.  There is no free list whose
//!   length depends on history.
//!
//! # Pages and size classes
//!
//! The arena is cut into 4 KiB pages (the MMU granule).  A page is free, a
//! **small page** holding objects of one size class, or part of a **run** — a
//! contiguous block of pages serving one big allocation.  The 512 size classes
//! are the multiples of `LEAN_OBJECT_SIZE_DELTA` (8) up to
//! `LEAN_MAX_SMALL_OBJECT_SIZE` (4096), indexed exactly as `lean_get_slot_idx`
//! indexes them, so `lean_alloc_small`'s `slot_idx` needs no translation.  Objects
//! of class size `s` sit at offsets `k·s` of a page-aligned page, so an object is
//! aligned to every power of two dividing `s` — which is how [`Heap::alloc`]
//! honours an alignment request without a header.
//!
//! When a small page's last object is freed the page returns to the free pool,
//! so memory does not stay pinned to the size class that first used it.
//!
//! # Concurrency
//!
//! One heap serves every core, behind a leaf [`TicketLock`](crate::ticket_lock::TicketLock).
//! Kernel entry is already serialised by the global entry lock, so the lock is
//! uncontended on every path this tree has today; it is here so the allocator's
//! soundness does not depend on that — the boot install runs outside the entry
//! lock — and it is a leaf: nothing is acquired while it is held, and the
//! wrappers release it before they halt.

use core::cell::UnsafeCell;

use crate::ticket_lock::TicketLock;

/// The page size of the arena: the MMU's 4 KiB granule.
pub const PAGE_SIZE: usize = 4096;
/// `LEAN_OBJECT_SIZE_DELTA` in `lean.h`: every small-object size is a multiple.
pub const OBJECT_SIZE_DELTA: usize = 8;
/// `LEAN_MAX_SMALL_OBJECT_SIZE` in `lean.h`: the largest small object.
pub const MAX_SMALL_OBJECT_SIZE: usize = 4096;
/// The number of small size classes, which is `lean_get_slot_idx`'s range.
pub const SLOT_COUNT: usize = MAX_SMALL_OBJECT_SIZE / OBJECT_SIZE_DELTA;
/// The largest arena, in pages, the page map can describe: a run's page count
/// shares its word with two tag bits.
pub const MAX_PAGES: usize = 1 << 29;

/// Words of a small page's occupancy bitmap: one bit per object, and the
/// smallest class (8 bytes) puts 512 objects in a page.
const OCCUPANCY_WORDS: usize = PAGE_SIZE / OBJECT_SIZE_DELTA / 64;
/// Link sentinel for the per-class partial-page lists.
const NO_PAGE: u32 = u32::MAX;

// Page-map encoding.  `0` is a free page; `1..=SLOT_COUNT` a small page of slot
// `state - 1`; `RUN_HEAD | n` the first page of an `n`-page run; `RUN_TAIL` any
// later page of a run.  The tags are disjoint from the slot range and from each
// other because `MAX_PAGES` keeps `n` below `RUN_TAIL`.
const STATE_FREE: u32 = 0;
const RUN_HEAD: u32 = 1 << 31;
const RUN_TAIL: u32 = 1 << 30;

/// What one page of the arena is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PageState {
    Free,
    Small(usize),
    RunHead(usize),
    RunTail,
}

impl PageState {
    fn decode(word: u32) -> Option<Self> {
        match word {
            STATE_FREE => Some(Self::Free),
            RUN_TAIL => Some(Self::RunTail),
            w if w & RUN_HEAD != 0 => {
                let n = (w & !RUN_HEAD) as usize;
                (n != 0 && n < MAX_PAGES).then_some(Self::RunHead(n))
            }
            w if (w as usize) <= SLOT_COUNT => Some(Self::Small(w as usize - 1)),
            _ => None,
        }
    }

    fn encode(self) -> u32 {
        match self {
            Self::Free => STATE_FREE,
            // Both casts are in range: a slot is below `SLOT_COUNT` and a run
            // below `MAX_PAGES`, which `Heap::new` bounds the arena by.
            Self::Small(slot) => (slot + 1) as u32,
            Self::RunHead(n) => RUN_HEAD | n as u32,
            Self::RunTail => RUN_TAIL,
        }
    }
}

/// The metadata of one arena page.  Plain integers, so every bit pattern is a
/// value and the arena's metadata pages may be zeroed and then initialised.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct PageMeta {
    /// The encoded [`PageState`].
    state: u32,
    /// Small page: the number of live objects.
    live: u16,
    _reserved: u16,
    /// Small page with a free object: the next page of its class's list.
    next: u32,
    /// Small page with a free object: the previous page of its class's list.
    prev: u32,
    /// Small page: bit `k` set iff object `k` is live, **or** `k` is past the
    /// page's capacity — so a clear bit is exactly an allocatable object.
    occupancy: [u64; OCCUPANCY_WORDS],
}

/// Why a pointer was refused.  Each is a contract violation by the caller; the
/// Lean-facing wrappers halt on every one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeapFault {
    /// The address is not inside the arena's data pages.
    OutsideArena,
    /// The address is in a page no allocation owns.
    FreePage,
    /// A small-object operation named an address in a run, or a run operation
    /// an address in a small page.
    WrongKind,
    /// The address is inside an object or a run rather than at its start.
    NotAtStart,
    /// The object is not live — freed already, or never allocated.
    NotLive,
    /// `lean_alloc_small` was called with a size that is not its slot's size.
    SlotMismatch,
    /// The page map holds a word no state encodes.
    Corrupt,
}

/// Why an arena could not be taken into service.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeapInitError {
    /// The arena's start or length is not page-aligned, or it wraps.
    Misaligned,
    /// The arena has no room for one data page beside its metadata.
    TooSmall,
    /// The arena exceeds what the page map describes.
    TooLarge,
    /// The metadata slices do not have the lengths the page count implies.
    MetadataShape,
}

/// Where an arena's metadata and data pages lie.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ArenaLayout {
    /// Byte offset of the free-page bitmap from the arena start.
    pub bitmap_offset: usize,
    /// Byte offset of the first data page from the arena start.
    pub data_offset: usize,
    /// The number of data pages.
    pub pages: usize,
}

/// Words of a free-page bitmap over `pages` pages.
#[must_use]
pub const fn bitmap_words(pages: usize) -> usize {
    pages.div_ceil(64)
}

impl ArenaLayout {
    /// The metadata bytes `pages` data pages need, rounded up to whole pages:
    /// the page map, then the bitmap at an 8-byte boundary.
    const fn metadata_pages(pages: usize) -> usize {
        let map = pages * core::mem::size_of::<PageMeta>();
        (map + bitmap_words(pages) * 8).div_ceil(PAGE_SIZE)
    }

    /// The layout of an arena of `len` bytes at `start`: as many data pages as
    /// fit beside the metadata describing them, and the metadata first.
    ///
    /// # Errors
    ///
    /// `Misaligned` for an unaligned or wrapping extent, `TooSmall` when no
    /// data page fits, `TooLarge` beyond [`MAX_PAGES`].
    pub fn of(start: usize, len: usize) -> Result<Self, HeapInitError> {
        if !start.is_multiple_of(PAGE_SIZE)
            || !len.is_multiple_of(PAGE_SIZE)
            || start.checked_add(len).is_none()
        {
            return Err(HeapInitError::Misaligned);
        }
        let total = len / PAGE_SIZE;
        // Each data page costs one page plus its share of the metadata, so the
        // estimate below is never short by more than the rounding the loops fix.
        let per_page = PAGE_SIZE + core::mem::size_of::<PageMeta>() + 1;
        let mut pages = total * PAGE_SIZE / per_page;
        while pages + Self::metadata_pages(pages) > total && pages > 0 {
            pages -= 1;
        }
        while pages + 1 + Self::metadata_pages(pages + 1) <= total {
            pages += 1;
        }
        if pages == 0 {
            return Err(HeapInitError::TooSmall);
        }
        if pages > MAX_PAGES {
            return Err(HeapInitError::TooLarge);
        }
        Ok(Self {
            bitmap_offset: pages * core::mem::size_of::<PageMeta>(),
            data_offset: Self::metadata_pages(pages) * PAGE_SIZE,
            pages,
        })
    }
}

/// Counters describing the heap, for tests and diagnostics.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HeapStats {
    /// Data pages in the arena.
    pub pages: usize,
    /// Data pages no allocation owns.
    pub free_pages: usize,
}

/// The allocator over one arena.  `'a` is the lifetime of its metadata.
pub struct Heap<'a> {
    /// The address of data page 0.
    data_base: usize,
    meta: &'a mut [PageMeta],
    /// Bit `i` of word `i / 64` is set iff data page `i` is free.
    free_bits: &'a mut [u64],
    /// The first bitmap word with a set bit, or the word count when none has.
    free_hint: usize,
    free_pages: usize,
    /// Per size class: the first small page with an allocatable object.
    partial: [u32; SLOT_COUNT],
}

/// The class size of slot `slot`.
const fn slot_size(slot: usize) -> usize {
    (slot + 1) * OBJECT_SIZE_DELTA
}

/// How many objects of slot `slot` one page holds.
const fn slot_capacity(slot: usize) -> usize {
    PAGE_SIZE / slot_size(slot)
}

impl<'a> Heap<'a> {
    /// A heap over data pages starting at `data_base`, described by `meta` (one
    /// entry per page) and `free_bits` (one bit per page).  Every page starts
    /// free.  The data pages themselves are never read or written.
    ///
    /// # Errors
    ///
    /// `Misaligned` for an unaligned, null or wrapping data extent, `TooSmall`
    /// for no pages, `TooLarge` beyond [`MAX_PAGES`], `MetadataShape` when
    /// `free_bits` is not [`bitmap_words`]`(meta.len())` words.
    pub fn new(
        data_base: usize,
        meta: &'a mut [PageMeta],
        free_bits: &'a mut [u64],
    ) -> Result<Self, HeapInitError> {
        let pages = meta.len();
        if pages == 0 {
            return Err(HeapInitError::TooSmall);
        }
        if pages > MAX_PAGES {
            return Err(HeapInitError::TooLarge);
        }
        if free_bits.len() != bitmap_words(pages) {
            return Err(HeapInitError::MetadataShape);
        }
        if data_base == 0
            || !data_base.is_multiple_of(PAGE_SIZE)
            || pages
                .checked_mul(PAGE_SIZE)
                .and_then(|bytes| data_base.checked_add(bytes))
                .is_none()
        {
            return Err(HeapInitError::Misaligned);
        }
        for entry in meta.iter_mut() {
            *entry = PageMeta::default();
        }
        for (w, word) in free_bits.iter_mut().enumerate() {
            let covered = pages.saturating_sub(w * 64).min(64);
            *word = if covered == 64 {
                u64::MAX
            } else {
                (1u64 << covered) - 1
            };
        }
        Ok(Self {
            data_base,
            meta,
            free_bits,
            free_hint: 0,
            free_pages: pages,
            partial: [NO_PAGE; SLOT_COUNT],
        })
    }

    /// Takes the arena `[start, start + len)` into service: carves the metadata
    /// from its leading pages per [`ArenaLayout::of`] and serves the rest.
    ///
    /// # Safety
    ///
    /// The whole range must be memory this heap owns exclusively for `'static`
    /// — mapped, writable, and neither read nor written by anything else for
    /// the life of the returned heap.  The linker's `.lean_heap` section is such
    /// a range: nothing else in the image names it.
    ///
    /// # Errors
    ///
    /// As [`ArenaLayout::of`].
    pub unsafe fn from_arena(start: usize, len: usize) -> Result<Heap<'static>, HeapInitError> {
        let layout = ArenaLayout::of(start, len)?;
        let meta_ptr = start as *mut PageMeta;
        let bits_ptr = (start + layout.bitmap_offset) as *mut u64;
        let words = bitmap_words(layout.pages);
        // SAFETY: the caller grants exclusive ownership of `[start, start + len)`;
        // `ArenaLayout::of` placed the page map at `start` (page-aligned, so
        // aligned for `PageMeta`) and the bitmap at an 8-byte boundary after it,
        // both inside `data_offset ≤ len`.  Zeroing first makes every element a
        // value — all fields are plain integers, for which all-zero is valid —
        // so the slices are formed over initialised memory, and `Heap::new`
        // then writes the real initial state.  The two ranges do not overlap:
        // the bitmap begins where the page map ends.
        let (meta, bits) = unsafe {
            core::ptr::write_bytes(meta_ptr, 0, layout.pages);
            core::ptr::write_bytes(bits_ptr, 0, words);
            (
                core::slice::from_raw_parts_mut(meta_ptr, layout.pages),
                core::slice::from_raw_parts_mut(bits_ptr, words),
            )
        };
        Heap::new(start + layout.data_offset, meta, bits)
    }

    /// The heap's counters.
    #[must_use]
    pub fn stats(&self) -> HeapStats {
        HeapStats {
            pages: self.meta.len(),
            free_pages: self.free_pages,
        }
    }

    /// The number of live allocations: small objects plus page runs.  A leak
    /// check reads this before and after the code it audits.
    #[must_use]
    pub fn live_allocations(&self) -> usize {
        self.meta
            .iter()
            .map(|m| match PageState::decode(m.state) {
                Some(PageState::Small(_)) => usize::from(m.live),
                Some(PageState::RunHead(_)) => 1,
                _ => 0,
            })
            .sum()
    }

    fn page_addr(&self, page: usize) -> usize {
        self.data_base + page * PAGE_SIZE
    }

    fn state(&self, page: usize) -> Result<PageState, HeapFault> {
        PageState::decode(self.meta[page].state).ok_or(HeapFault::Corrupt)
    }

    /// The page an address lies in, and its offset within the page.
    fn locate(&self, addr: usize) -> Result<(usize, usize), HeapFault> {
        let offset = addr
            .checked_sub(self.data_base)
            .ok_or(HeapFault::OutsideArena)?;
        let page = offset / PAGE_SIZE;
        if page >= self.meta.len() {
            return Err(HeapFault::OutsideArena);
        }
        Ok((page, offset % PAGE_SIZE))
    }

    // ----------------------------------------------------------------------
    // Page runs
    // ----------------------------------------------------------------------

    /// The lowest free run of `n` pages, or `None`.
    fn find_run(&self, n: usize) -> Option<usize> {
        let pages = self.meta.len();
        let mut run = 0usize;
        let mut i = self.free_hint * 64;
        while i < pages {
            let (w, b) = (i / 64, i % 64);
            let word = self.free_bits[w];
            if b == 0 && word == 0 {
                run = 0;
                i += 64;
                continue;
            }
            // A full word is 64 free pages: bits past the last page are never
            // set (invariant 1), so a full word cannot straddle the arena's end.
            if b == 0 && word == u64::MAX {
                run += 64;
                i += 64;
            } else {
                if word >> b & 1 == 1 {
                    run += 1;
                } else {
                    run = 0;
                }
                i += 1;
            }
            if run >= n {
                return Some(i - run);
            }
        }
        None
    }

    fn set_free_bit(&mut self, page: usize, free: bool) {
        let (w, b) = (page / 64, page % 64);
        if free {
            self.free_bits[w] |= 1 << b;
        } else {
            self.free_bits[w] &= !(1 << b);
        }
    }

    /// Takes the lowest free run of `n` pages, marks it `state` at its head and
    /// `RunTail` behind (a small page is a run of one), and returns its index.
    fn take_pages(&mut self, n: usize, head: PageState) -> Option<usize> {
        if n == 0 || n > self.free_pages {
            return None;
        }
        let first = self.find_run(n)?;
        for page in first..first + n {
            self.set_free_bit(page, false);
            self.meta[page] = PageMeta {
                state: if page == first {
                    head.encode()
                } else {
                    RUN_TAIL
                },
                ..PageMeta::default()
            };
        }
        self.free_pages -= n;
        while self.free_hint < self.free_bits.len() && self.free_bits[self.free_hint] == 0 {
            self.free_hint += 1;
        }
        Some(first)
    }

    /// Returns `n` pages starting at `first` to the pool.
    fn release_pages(&mut self, first: usize, n: usize) {
        for page in first..first + n {
            self.meta[page] = PageMeta::default();
            self.set_free_bit(page, true);
        }
        self.free_pages += n;
        self.free_hint = self.free_hint.min(first / 64);
    }

    // ----------------------------------------------------------------------
    // Small pages
    // ----------------------------------------------------------------------

    fn list_push(&mut self, slot: usize, page: usize) {
        let head = self.partial[slot];
        self.meta[page].prev = NO_PAGE;
        self.meta[page].next = head;
        if head != NO_PAGE {
            self.meta[head as usize].prev = page as u32;
        }
        self.partial[slot] = page as u32;
    }

    fn list_remove(&mut self, slot: usize, page: usize) {
        let PageMeta { next, prev, .. } = self.meta[page];
        if prev == NO_PAGE {
            self.partial[slot] = next;
        } else {
            self.meta[prev as usize].next = next;
        }
        if next != NO_PAGE {
            self.meta[next as usize].prev = prev;
        }
        self.meta[page].next = NO_PAGE;
        self.meta[page].prev = NO_PAGE;
    }

    /// A new small page of `slot`, on its class's list, with every bit past the
    /// capacity set so the occupancy scan can never select one.
    fn new_small_page(&mut self, slot: usize) -> Option<usize> {
        let page = self.take_pages(1, PageState::Small(slot))?;
        let capacity = slot_capacity(slot);
        for (w, word) in self.meta[page].occupancy.iter_mut().enumerate() {
            let usable = capacity.saturating_sub(w * 64).min(64);
            *word = if usable == 64 {
                0
            } else {
                !((1u64 << usable) - 1)
            };
        }
        self.list_push(slot, page);
        Some(page)
    }

    /// The small-object allocation `lean_alloc_small(sz, slot_idx)` performs.
    /// `size` must be the slot's own size — `lean.h` computes both from one
    /// aligned size, so a mismatch is a caller defect, not a request to round.
    ///
    /// # Errors
    ///
    /// `SlotMismatch` for a slot out of range or a size that is not its size;
    /// `Ok(None)` when the arena has no page left for the class.
    pub fn alloc_small(&mut self, size: usize, slot: usize) -> Result<Option<usize>, HeapFault> {
        if slot >= SLOT_COUNT || size != slot_size(slot) {
            return Err(HeapFault::SlotMismatch);
        }
        let page = match self.partial[slot] {
            NO_PAGE => match self.new_small_page(slot) {
                Some(page) => page,
                None => return Ok(None),
            },
            page => page as usize,
        };
        let entry = &mut self.meta[page];
        let (w, word) = entry
            .occupancy
            .iter()
            .copied()
            .enumerate()
            .find(|(_, word)| *word != u64::MAX)
            .ok_or(HeapFault::Corrupt)?;
        let bit = (!word).trailing_zeros() as usize;
        entry.occupancy[w] |= 1 << bit;
        entry.live += 1;
        if usize::from(entry.live) == slot_capacity(slot) {
            self.list_remove(slot, page);
        }
        Ok(Some(self.page_addr(page) + (w * 64 + bit) * size))
    }

    /// The small page, slot and object index of a live small object.
    fn small_object(&self, addr: usize) -> Result<(usize, usize, usize), HeapFault> {
        let (page, offset) = self.locate(addr)?;
        let slot = match self.state(page)? {
            PageState::Small(slot) => slot,
            PageState::Free => return Err(HeapFault::FreePage),
            PageState::RunHead(_) | PageState::RunTail => return Err(HeapFault::WrongKind),
        };
        let size = slot_size(slot);
        if offset % size != 0 {
            return Err(HeapFault::NotAtStart);
        }
        let index = offset / size;
        if index >= slot_capacity(slot)
            || self.meta[page].occupancy[index / 64] >> (index % 64) & 1 == 0
        {
            return Err(HeapFault::NotLive);
        }
        Ok((page, slot, index))
    }

    /// `lean_small_mem_size(p)`: the class size of the live small object at `addr`.
    ///
    /// # Errors
    ///
    /// Any [`HeapFault`] but `SlotMismatch`, when `addr` is not a live small object.
    pub fn small_size(&self, addr: usize) -> Result<usize, HeapFault> {
        self.small_object(addr).map(|(_, slot, _)| slot_size(slot))
    }

    /// `lean_free_small(p)`: frees the live small object at `addr`, returning its
    /// page to the pool when it was the page's last.
    ///
    /// # Errors
    ///
    /// Any [`HeapFault`] but `SlotMismatch`, when `addr` is not a live small
    /// object — which includes the second free of one.
    pub fn free_small(&mut self, addr: usize) -> Result<(), HeapFault> {
        let (page, slot, index) = self.small_object(addr)?;
        let was_full = usize::from(self.meta[page].live) == slot_capacity(slot);
        let entry = &mut self.meta[page];
        entry.occupancy[index / 64] &= !(1 << (index % 64));
        entry.live -= 1;
        if entry.live == 0 {
            if !was_full {
                self.list_remove(slot, page);
            }
            self.release_pages(page, 1);
        } else if was_full {
            self.list_push(slot, page);
        }
        Ok(())
    }

    // ----------------------------------------------------------------------
    // The general interface: `malloc`'s shape, served from the same arena
    // ----------------------------------------------------------------------

    /// An allocation of `size` bytes aligned to `align`.  A size and alignment a
    /// small class can hold go to the smallest class whose size is a multiple of
    /// `align`; anything larger is a run of whole pages.  A zero-byte request is
    /// served as one byte, so every success is a distinct live address.
    ///
    /// `None` when `align` is not a power of two, exceeds [`PAGE_SIZE`], or the
    /// arena cannot serve the request.
    #[must_use]
    pub fn alloc(&mut self, size: usize, align: usize) -> Option<usize> {
        if !align.is_power_of_two() || align > PAGE_SIZE {
            return None;
        }
        let quantum = align.max(OBJECT_SIZE_DELTA);
        let class = size.max(1).checked_next_multiple_of(quantum)?;
        if class <= MAX_SMALL_OBJECT_SIZE {
            let slot = class / OBJECT_SIZE_DELTA - 1;
            return self.alloc_small(class, slot).ok().flatten();
        }
        let pages = size.div_ceil(PAGE_SIZE);
        let first = self.take_pages(pages, PageState::RunHead(pages))?;
        Some(self.page_addr(first))
    }

    /// Frees any live allocation — a small object or a run — at `addr`.
    ///
    /// # Errors
    ///
    /// Any [`HeapFault`] but `SlotMismatch`, when `addr` is not a live allocation.
    pub fn free(&mut self, addr: usize) -> Result<(), HeapFault> {
        let (page, offset) = self.locate(addr)?;
        match self.state(page)? {
            PageState::Small(_) => self.free_small(addr),
            PageState::RunHead(n) if offset == 0 => {
                self.release_pages(page, n);
                Ok(())
            }
            PageState::RunHead(_) | PageState::RunTail => Err(HeapFault::NotAtStart),
            PageState::Free => Err(HeapFault::FreePage),
        }
    }

    /// The usable size of the live allocation at `addr`: its class size, or its
    /// run's whole pages.
    ///
    /// # Errors
    ///
    /// Any [`HeapFault`] but `SlotMismatch`, when `addr` is not a live allocation.
    pub fn usable_size(&self, addr: usize) -> Result<usize, HeapFault> {
        let (page, offset) = self.locate(addr)?;
        match self.state(page)? {
            PageState::Small(_) => self.small_size(addr),
            PageState::RunHead(n) if offset == 0 => Ok(n * PAGE_SIZE),
            PageState::RunHead(_) | PageState::RunTail => Err(HeapFault::NotAtStart),
            PageState::Free => Err(HeapFault::FreePage),
        }
    }

    // ----------------------------------------------------------------------
    // The invariant, stated once and checked by the witness suite
    // ----------------------------------------------------------------------

    /// Checks every invariant the operations maintain, naming the first that
    /// fails:
    ///
    /// 1. a page's free bit is set iff its state is `Free`, bits past the last
    ///    page are clear, and `free_pages` counts the set bits;
    /// 2. `free_hint` is the first bitmap word with a set bit (the word count
    ///    when there is none), so a page search starts at the first free page;
    /// 3. every run head of `n` pages is followed by exactly `n - 1` tails inside
    ///    the arena, and every tail belongs to a head;
    /// 4. every small page has `live` equal to its occupied objects, at least one
    ///    and at most its capacity, and every bit past the capacity set;
    /// 5. a small page is on its class's list iff it has a free object, and each
    ///    list is doubly linked, headed by a page with no predecessor, acyclic.
    ///
    /// # Errors
    ///
    /// A description of the first violated invariant.
    pub fn check_invariants(&self) -> Result<(), &'static str> {
        let pages = self.meta.len();
        let mut free = 0usize;
        let mut page = 0usize;
        while page < pages {
            let is_free_bit = self.free_bits[page / 64] >> (page % 64) & 1 == 1;
            let state = self
                .state(page)
                .map_err(|_| "a page-map word encodes no state")?;
            if is_free_bit != (state == PageState::Free) {
                return Err("a free bit disagrees with its page's state");
            }
            match state {
                PageState::Free => {
                    free += 1;
                    page += 1;
                }
                PageState::RunTail => return Err("a run tail has no head"),
                PageState::RunHead(n) => {
                    if page + n > pages {
                        return Err("a run extends past the arena");
                    }
                    for tail in page + 1..page + n {
                        if self.meta[tail].state != RUN_TAIL
                            || self.free_bits[tail / 64] >> (tail % 64) & 1 == 1
                        {
                            return Err("a run's pages are not all tails");
                        }
                    }
                    page += n;
                }
                PageState::Small(slot) => {
                    let entry = &self.meta[page];
                    let capacity = slot_capacity(slot);
                    for k in capacity..OCCUPANCY_WORDS * 64 {
                        if entry.occupancy[k / 64] >> (k % 64) & 1 == 0 {
                            return Err("a small page has a clear bit past its capacity");
                        }
                    }
                    // Every bit past the capacity is set, so the occupied
                    // objects are the set bits less those.
                    let occupied: usize = entry
                        .occupancy
                        .iter()
                        .map(|w| w.count_ones() as usize)
                        .sum::<usize>()
                        - (OCCUPANCY_WORDS * 64 - capacity);
                    let live = usize::from(entry.live);
                    if occupied != live {
                        return Err("a small page's live count disagrees with its occupancy");
                    }
                    if live == 0 || live > capacity {
                        return Err("a small page's live count is out of range");
                    }
                    page += 1;
                }
            }
        }
        for w in 0..self.free_bits.len() {
            let covered = pages.saturating_sub(w * 64).min(64);
            let tail = if covered == 64 {
                0
            } else {
                !((1u64 << covered) - 1)
            };
            if self.free_bits[w] & tail != 0 {
                return Err("a free bit is set past the last page");
            }
            if w < self.free_hint && self.free_bits[w] != 0 {
                return Err("a bitmap word below the hint has a free page");
            }
        }
        if self.free_hint < self.free_bits.len() && self.free_bits[self.free_hint] == 0 {
            return Err("the hint is past the first word with a free page");
        }
        if self.free_hint > self.free_bits.len() {
            return Err("the hint is past the bitmap");
        }
        if free != self.free_pages {
            return Err("free_pages disagrees with the bitmap");
        }
        let mut on_list = 0usize;
        for (slot, &head) in self.partial.iter().enumerate() {
            let mut prev = NO_PAGE;
            let mut cursor = head;
            let mut steps = 0usize;
            while cursor != NO_PAGE {
                let p = cursor as usize;
                if p >= pages || self.state(p) != Ok(PageState::Small(slot)) {
                    return Err("a class list names a page not of its class");
                }
                if self.meta[p].prev != prev {
                    return Err("a class list's back-link is wrong");
                }
                if usize::from(self.meta[p].live) >= slot_capacity(slot) {
                    return Err("a full page is on its class list");
                }
                steps += 1;
                if steps > pages {
                    return Err("a class list is cyclic");
                }
                prev = cursor;
                cursor = self.meta[p].next;
            }
            on_list += steps;
        }
        let with_room = (0..pages)
            .filter(|&p| match self.state(p) {
                Ok(PageState::Small(slot)) => usize::from(self.meta[p].live) < slot_capacity(slot),
                _ => false,
            })
            .count();
        if with_room != on_list {
            return Err("a small page with a free object is on no class list");
        }
        Ok(())
    }
}

// ==========================================================================
// The kernel's heap: one per image, over the linker's `.lean_heap` section
// ==========================================================================

/// Why the kernel heap could not serve a Lean runtime call.  The C-ABI entry
/// points halt on every one of these; the Rust functions that compute them are
/// the testable half.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelHeapError {
    /// The arena could not be taken into service.
    Init(HeapInitError),
    /// The call violated the allocator's contract.
    Fault(HeapFault),
    /// The arena has no memory left for the request.
    Exhausted,
}

/// The kernel heap: taken into service on first use, from the extent the
/// linker placed, and never again.
struct KernelHeap {
    lock: TicketLock,
    heap: UnsafeCell<Option<Result<Heap<'static>, HeapInitError>>>,
}

// SAFETY: `heap` is read and written only inside `with_kernel_heap`, with `lock`
// held for the whole access, so no two cores ever hold a reference to it at
// once; `Heap`'s own fields are plain data and slices into memory the heap owns.
unsafe impl Sync for KernelHeap {}

static KERNEL_HEAP: KernelHeap = KernelHeap {
    lock: TicketLock::new(),
    heap: UnsafeCell::new(None),
};

/// The arena's extent: the linker's `__lean_heap_start` / `__lean_heap_end`.
/// Only the symbols' addresses are taken, which forms no access.
#[cfg(target_arch = "aarch64")]
pub(crate) fn arena_extent() -> (usize, usize) {
    extern "C" {
        static __lean_heap_start: u8;
        static __lean_heap_end: u8;
    }
    let start = &raw const __lean_heap_start as usize;
    let end = &raw const __lean_heap_end as usize;
    (start, end.saturating_sub(start))
}

/// The host has no link script.  A test build serves the kernel heap from a
/// static buffer standing in for the section; any other host build has an
/// empty extent, which `ArenaLayout::of` refuses, so the heap is never taken
/// into service over memory it does not own.
#[cfg(not(target_arch = "aarch64"))]
fn arena_extent() -> (usize, usize) {
    #[cfg(test)]
    {
        host_arena::extent()
    }
    #[cfg(not(test))]
    {
        (0, 0)
    }
}

#[cfg(all(test, not(target_arch = "aarch64")))]
mod host_arena {
    use core::cell::UnsafeCell;

    /// Bytes of the host stand-in for `.lean_heap`.
    pub const LEN: usize = 256 * super::PAGE_SIZE;

    #[repr(C, align(4096))]
    struct Arena(UnsafeCell<[u8; LEN]>);

    // SAFETY: the buffer is handed to `Heap::from_arena` exactly once, under the
    // kernel heap's lock, and nothing else ever names it.
    unsafe impl Sync for Arena {}

    static ARENA: Arena = Arena(UnsafeCell::new([0; LEN]));

    pub fn extent() -> (usize, usize) {
        (ARENA.0.get() as usize, LEN)
    }
}

/// Runs `f` on the kernel heap with its lock held, taking the heap into service
/// first if this is the first call.  The lock is released before this returns,
/// so a caller that must halt on the result does so without holding it.
fn with_kernel_heap<R>(f: impl FnOnce(&mut Heap<'static>) -> R) -> Result<R, KernelHeapError> {
    KERNEL_HEAP.lock.with_lock(|| {
        // SAFETY: `KERNEL_HEAP.lock` is held for the whole of this closure, and
        // this closure is the only place `heap` is accessed, so this is the only
        // live reference to it.
        let slot = unsafe { &mut *KERNEL_HEAP.heap.get() };
        let heap = slot.get_or_insert_with(|| {
            let (start, len) = arena_extent();
            // SAFETY: the extent is the linker's `.lean_heap` section (or, in a
            // host test build, the static buffer standing in for it): memory no
            // other code in the image names, taken into service exactly once
            // because the result is stored in `slot` under the lock.
            unsafe { Heap::from_arena(start, len) }
        });
        match heap {
            Ok(heap) => Ok(f(heap)),
            Err(e) => Err(KernelHeapError::Init(*e)),
        }
    })
}

/// `lean_alloc_small(sz, slot_idx)` on the kernel heap.
///
/// # Errors
///
/// `Init` if the arena cannot be taken into service, `Fault(SlotMismatch)` for a
/// size that is not its slot's, `Exhausted` when no page is left.
pub fn kernel_alloc_small(size: u32, slot: u32) -> Result<usize, KernelHeapError> {
    with_kernel_heap(|heap| heap.alloc_small(size as usize, slot as usize))?
        .map_err(KernelHeapError::Fault)?
        .ok_or(KernelHeapError::Exhausted)
}

/// `size` bytes aligned to `align` on the kernel heap — the general request the
/// Lean runtime's big-object path and its scratch buffers make.
///
/// # Errors
///
/// `Init` if the arena cannot be taken into service, `Exhausted` when the heap
/// cannot serve the request (including an alignment beyond a page).
pub fn kernel_alloc(size: usize, align: usize) -> Result<usize, KernelHeapError> {
    with_kernel_heap(|heap| heap.alloc(size, align))?.ok_or(KernelHeapError::Exhausted)
}

/// Frees any live kernel-heap allocation at `addr`.
///
/// # Errors
///
/// `Init` if the arena cannot be taken into service; `Fault` when `addr` is not
/// a live allocation.
pub fn kernel_free(addr: usize) -> Result<(), KernelHeapError> {
    with_kernel_heap(|heap| heap.free(addr))?.map_err(KernelHeapError::Fault)
}

/// The usable size of the live kernel-heap allocation at `addr`.
///
/// # Errors
///
/// `Init` if the arena cannot be taken into service; `Fault` when `addr` is not
/// a live allocation.
pub fn kernel_usable_size(addr: usize) -> Result<usize, KernelHeapError> {
    with_kernel_heap(|heap| heap.usable_size(addr))?.map_err(KernelHeapError::Fault)
}

/// `lean_free_small(p)` on the kernel heap.
///
/// # Errors
///
/// `Init` if the arena cannot be taken into service; `Fault` when `addr` is not
/// a live small object.
pub fn kernel_free_small(addr: usize) -> Result<(), KernelHeapError> {
    with_kernel_heap(|heap| heap.free_small(addr))?.map_err(KernelHeapError::Fault)
}

/// `lean_small_mem_size(p)` on the kernel heap.
///
/// # Errors
///
/// `Init` if the arena cannot be taken into service; `Fault` when `addr` is not
/// a live small object.
pub fn kernel_small_size(addr: usize) -> Result<u32, KernelHeapError> {
    let size = with_kernel_heap(|heap| heap.small_size(addr))?.map_err(KernelHeapError::Fault)?;
    // A class size is at most `MAX_SMALL_OBJECT_SIZE`, so it fits.
    Ok(size as u32)
}

/// The fail-closed end of every Lean-facing heap call: the Lean runtime cannot
/// recover from a failed small allocation — `lean.h`'s inline paths do not test
/// the result — and a contract violation means an object's lifetime is already
/// wrong, so the PE parks rather than continue with memory it cannot trust.
#[cfg(feature = "hw_target")]
fn heap_halt(error: KernelHeapError) -> ! {
    crate::kprintln!("[lean_heap] FATAL: {:?}", error);
    crate::cpu::fatal_halt()
}

/// `lean.h`: `void * lean_alloc_small(unsigned sz, unsigned slot_idx)`.  Halts
/// on exhaustion and on a contract violation; never returns null.
#[cfg(feature = "hw_target")]
#[no_mangle]
pub extern "C" fn lean_alloc_small(sz: u32, slot_idx: u32) -> *mut core::ffi::c_void {
    match kernel_alloc_small(sz, slot_idx) {
        Ok(addr) => addr as *mut core::ffi::c_void,
        Err(error) => heap_halt(error),
    }
}

/// `lean.h`: `void lean_free_small(void * p)`.  Halts on a pointer that is not a
/// live small object.
#[cfg(feature = "hw_target")]
#[no_mangle]
pub extern "C" fn lean_free_small(p: *mut core::ffi::c_void) {
    if let Err(error) = kernel_free_small(p as usize) {
        heap_halt(error);
    }
}

/// `lean.h`: `unsigned lean_small_mem_size(void * p)`.  Halts on a pointer that
/// is not a live small object.
#[cfg(feature = "hw_target")]
#[no_mangle]
pub extern "C" fn lean_small_mem_size(p: *mut core::ffi::c_void) -> u32 {
    match kernel_small_size(p as usize) {
        Ok(size) => size,
        Err(error) => heap_halt(error),
    }
}

// ==========================================================================
// WS-BP BP2.5: the witness suite — the arena's bounds, exhaustion, alignment
// ==========================================================================
//
// The first place this allocator runs for real is a board with no debugger
// attached, so its every claim is exercised here on the host.  The heap never
// dereferences the memory it serves, so most cases need no memory at all: the
// data base is an address and only the metadata is real.  `check_invariants`
// runs after every mutation, so a case that passes has also shown the state it
// left behind is one the invariant admits.
#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use std::collections::BTreeMap;
    use std::vec;
    use std::vec::Vec;

    /// A page-aligned data base that is not an address the host maps, which is
    /// the point: the heap must not touch it.
    const BASE: usize = 0x4000_0000;

    fn metadata(pages: usize) -> (Vec<PageMeta>, Vec<u64>) {
        (
            vec![PageMeta::default(); pages],
            vec![0; bitmap_words(pages)],
        )
    }

    fn heap<'a>(meta: &'a mut [PageMeta], bits: &'a mut [u64]) -> Heap<'a> {
        let heap = Heap::new(BASE, meta, bits).expect("fixture heap");
        heap.check_invariants()
            .expect("a fresh heap satisfies the invariant");
        heap
    }

    fn ok(heap: &Heap<'_>) {
        if let Err(why) = heap.check_invariants() {
            panic!("invariant violated: {why}");
        }
    }

    // -- the page-map encoding -------------------------------------------

    #[test]
    fn page_states_round_trip_and_garbage_is_refused() {
        for state in [
            PageState::Free,
            PageState::Small(0),
            PageState::Small(SLOT_COUNT - 1),
            PageState::RunHead(1),
            PageState::RunHead(MAX_PAGES - 1),
            PageState::RunTail,
        ] {
            assert_eq!(PageState::decode(state.encode()), Some(state));
        }
        // Past the last slot, a run of zero pages, and both tags at once.
        for word in [
            SLOT_COUNT as u32 + 1,
            RUN_HEAD,
            RUN_HEAD | RUN_TAIL | 1,
            RUN_TAIL | 1,
        ] {
            assert_eq!(PageState::decode(word), None, "word {word:#x}");
        }
    }

    // -- the arena layout ----------------------------------------------------

    #[test]
    fn layout_is_maximal_and_disjoint() {
        for total in [2usize, 3, 64, 65, 200, 4096, 16384] {
            let layout = ArenaLayout::of(BASE, total * PAGE_SIZE).expect("layout");
            let meta_end = layout.bitmap_offset + bitmap_words(layout.pages) * 8;
            assert_eq!(
                layout.bitmap_offset,
                layout.pages * core::mem::size_of::<PageMeta>()
            );
            assert!(
                meta_end <= layout.data_offset,
                "metadata overlaps data at {total} pages"
            );
            assert_eq!(layout.data_offset % PAGE_SIZE, 0);
            assert!(layout.data_offset + layout.pages * PAGE_SIZE <= total * PAGE_SIZE);
            // Maximal: one more data page would not fit beside its metadata.
            let more = layout.pages + 1;
            assert!(
                more + ArenaLayout::metadata_pages(more) > total,
                "not maximal at {total}"
            );
        }
    }

    #[test]
    fn layout_refuses_what_it_cannot_serve() {
        assert_eq!(
            ArenaLayout::of(BASE + 8, 16 * PAGE_SIZE),
            Err(HeapInitError::Misaligned)
        );
        assert_eq!(
            ArenaLayout::of(BASE, 16 * PAGE_SIZE + 8),
            Err(HeapInitError::Misaligned)
        );
        assert_eq!(
            ArenaLayout::of(usize::MAX - PAGE_SIZE + 1, 2 * PAGE_SIZE),
            Err(HeapInitError::Misaligned)
        );
        assert_eq!(ArenaLayout::of(BASE, 0), Err(HeapInitError::TooSmall));
        assert_eq!(
            ArenaLayout::of(BASE, PAGE_SIZE),
            Err(HeapInitError::TooSmall)
        );
    }

    #[test]
    fn new_refuses_malformed_metadata() {
        let (mut meta, mut bits) = metadata(10);
        assert_eq!(
            Heap::new(BASE + 1, &mut meta, &mut bits).err(),
            Some(HeapInitError::Misaligned)
        );
        assert_eq!(
            Heap::new(0, &mut meta, &mut bits).err(),
            Some(HeapInitError::Misaligned)
        );
        let (mut meta, mut bits) = metadata(10);
        let mut short = vec![0u64; 0];
        assert_eq!(
            Heap::new(BASE, &mut meta, &mut short).err(),
            Some(HeapInitError::MetadataShape)
        );
        let mut none: Vec<PageMeta> = Vec::new();
        assert_eq!(
            Heap::new(BASE, &mut none, &mut bits).err(),
            Some(HeapInitError::TooSmall)
        );
        assert_eq!(
            Heap::new(usize::MAX - 3 * PAGE_SIZE + 1, &mut meta, &mut bits).err(),
            Some(HeapInitError::Misaligned)
        );
    }

    #[test]
    fn from_arena_places_metadata_first_and_serves_the_rest() {
        #[repr(C, align(4096))]
        struct Arena([u8; 64 * PAGE_SIZE]);
        let arena: &'static mut Arena =
            std::boxed::Box::leak(std::boxed::Box::new(Arena([0xa5; 64 * PAGE_SIZE])));
        let start = arena.0.as_mut_ptr() as usize;
        let layout = ArenaLayout::of(start, 64 * PAGE_SIZE).expect("layout");
        // SAFETY: `arena` is leaked, so this heap owns it for `'static`.
        let mut heap = unsafe { Heap::from_arena(start, 64 * PAGE_SIZE) }.expect("heap");
        ok(&heap);
        assert_eq!(heap.stats().pages, layout.pages);
        assert_eq!(heap.stats().free_pages, layout.pages);
        let first = heap.alloc_small(8, 0).unwrap().unwrap();
        assert_eq!(
            first,
            start + layout.data_offset,
            "the first object is the first data page's first byte"
        );
        // Taking the arena into service wrote only the metadata pages.
        assert!(arena.0[layout.data_offset..].iter().all(|b| *b == 0xa5));
    }

    // -- small objects: the `lean.h` contract ------------------------------

    #[test]
    fn every_slot_serves_its_own_size_aligned_to_the_delta() {
        let (mut meta, mut bits) = metadata(SLOT_COUNT + 4);
        let mut heap = heap(&mut meta, &mut bits);
        for slot in 0..SLOT_COUNT {
            let size = slot_size(slot);
            let a = heap.alloc_small(size, slot).unwrap().expect("room");
            let b = heap.alloc_small(size, slot).unwrap();
            assert_eq!(a % OBJECT_SIZE_DELTA, 0);
            assert_eq!(
                heap.small_size(a),
                Ok(size),
                "lean_small_mem_size reports the class"
            );
            let b = b.expect("room");
            if slot_capacity(slot) >= 2 {
                assert_eq!(
                    b,
                    a + size,
                    "the second object follows the first in its page"
                );
            } else {
                assert_eq!(
                    b,
                    a + PAGE_SIZE,
                    "a one-object page is full, so the next opens a page"
                );
            }
            heap.free_small(b).unwrap();
            heap.free_small(a).unwrap();
        }
        ok(&heap);
        assert_eq!(
            heap.stats().free_pages,
            heap.stats().pages,
            "every page came back"
        );
    }

    #[test]
    fn a_slot_mismatch_is_a_fault_not_a_rounding() {
        let (mut meta, mut bits) = metadata(4);
        let mut heap = heap(&mut meta, &mut bits);
        assert_eq!(heap.alloc_small(16, 0), Err(HeapFault::SlotMismatch));
        assert_eq!(heap.alloc_small(12, 1), Err(HeapFault::SlotMismatch));
        assert_eq!(
            heap.alloc_small(4104, SLOT_COUNT),
            Err(HeapFault::SlotMismatch)
        );
        assert_eq!(heap.stats().free_pages, 4, "a refused call takes nothing");
        ok(&heap);
    }

    #[test]
    fn a_page_fills_to_capacity_and_the_next_object_opens_a_page() {
        for slot in [0usize, 2, 4, 48, 255, 511] {
            let (mut meta, mut bits) = metadata(3);
            let mut heap = heap(&mut meta, &mut bits);
            let size = slot_size(slot);
            let cap = slot_capacity(slot);
            let objects: Vec<usize> = (0..cap)
                .map(|_| heap.alloc_small(size, slot).unwrap().unwrap())
                .collect();
            ok(&heap);
            assert_eq!(
                heap.stats().free_pages,
                2,
                "one page holds {cap} objects of {size}"
            );
            assert!(objects.iter().all(|a| (a - BASE) / PAGE_SIZE == 0));
            let next = heap.alloc_small(size, slot).unwrap().unwrap();
            assert_eq!(next, BASE + PAGE_SIZE, "a full page leaves its class list");
            ok(&heap);
        }
    }

    #[test]
    fn a_freed_object_is_reused_before_a_new_page_is_opened() {
        let (mut meta, mut bits) = metadata(4);
        let mut heap = heap(&mut meta, &mut bits);
        let objs: Vec<usize> = (0..slot_capacity(7))
            .map(|_| heap.alloc_small(64, 7).unwrap().unwrap())
            .collect();
        heap.free_small(objs[5]).unwrap();
        ok(&heap);
        assert_eq!(
            heap.alloc_small(64, 7),
            Ok(Some(objs[5])),
            "the freed slot, not a new page"
        );
        assert_eq!(heap.stats().free_pages, 3);
        ok(&heap);
    }

    #[test]
    fn the_last_free_returns_the_page_to_the_pool() {
        let (mut meta, mut bits) = metadata(2);
        let mut heap = heap(&mut meta, &mut bits);
        let a = heap.alloc_small(24, 2).unwrap().unwrap();
        let b = heap.alloc_small(24, 2).unwrap().unwrap();
        assert_eq!(heap.stats().free_pages, 1);
        heap.free_small(a).unwrap();
        assert_eq!(heap.stats().free_pages, 1, "the page still holds b");
        heap.free_small(b).unwrap();
        assert_eq!(heap.stats().free_pages, 2);
        ok(&heap);
        // The page now serves another class: memory is not pinned to the first.
        let c = heap.alloc_small(4096, SLOT_COUNT - 1).unwrap().unwrap();
        assert_eq!(c, BASE);
        ok(&heap);
    }

    // -- every free is checked -----------------------------------------------

    #[test]
    fn a_bad_free_is_a_fault_and_changes_nothing() {
        let (mut meta, mut bits) = metadata(4);
        let mut heap = heap(&mut meta, &mut bits);
        let a = heap.alloc_small(32, 3).unwrap().unwrap();
        let b = heap.alloc_small(32, 3).unwrap().unwrap();
        let run = heap.alloc(3 * PAGE_SIZE, 16).unwrap();
        let before = heap.stats();
        for (addr, fault) in [
            (BASE - 8, HeapFault::OutsideArena),
            (BASE + 4 * PAGE_SIZE, HeapFault::OutsideArena),
            (a + 8, HeapFault::NotAtStart),
            (b + 32, HeapFault::NotLive),
            (run, HeapFault::WrongKind),
            (run + PAGE_SIZE, HeapFault::WrongKind),
        ] {
            assert_eq!(heap.free_small(addr), Err(fault), "free_small({addr:#x})");
        }
        assert_eq!(heap.free(run + PAGE_SIZE), Err(HeapFault::NotAtStart));
        assert_eq!(heap.free(run + 16), Err(HeapFault::NotAtStart));
        assert_eq!(heap.stats(), before);
        ok(&heap);
        heap.free_small(a).unwrap();
        assert_eq!(
            heap.free_small(a),
            Err(HeapFault::NotLive),
            "a double free is detected"
        );
        assert_eq!(heap.small_size(a), Err(HeapFault::NotLive));
        heap.free_small(b).unwrap();
        assert_eq!(
            heap.free_small(a),
            Err(HeapFault::FreePage),
            "the page went back to the pool"
        );
        heap.free(run).unwrap();
        assert_eq!(heap.free(run), Err(HeapFault::FreePage));
        ok(&heap);
        assert_eq!(heap.stats().free_pages, 4);
    }

    #[test]
    fn a_corrupt_page_map_word_is_reported_not_decoded() {
        let (mut meta, mut bits) = metadata(2);
        let mut heap = heap(&mut meta, &mut bits);
        let a = heap.alloc_small(8, 0).unwrap().unwrap();
        heap.meta[0].state = RUN_HEAD; // a run of zero pages encodes nothing
        assert_eq!(heap.free(a), Err(HeapFault::Corrupt));
        assert!(heap.check_invariants().is_err());
    }

    // -- the general interface: alignment and runs -----------------------------

    #[test]
    fn every_alignment_up_to_a_page_is_honoured() {
        let (mut meta, mut bits) = metadata(2048);
        let mut heap = heap(&mut meta, &mut bits);
        let mut live = Vec::new();
        for shift in 0..=12u32 {
            let align = 1usize << shift;
            for size in [
                0usize, 1, 7, 8, 15, 16, 17, 100, 511, 1000, 4000, 4096, 4097, 9000, 70_000,
            ] {
                let addr = heap.alloc(size, align).expect("room");
                assert_eq!(addr % align, 0, "size {size} align {align}");
                let usable = heap.usable_size(addr).unwrap();
                assert!(usable >= size.max(1), "size {size}: usable {usable}");
                live.push(addr);
            }
        }
        ok(&heap);
        for addr in live {
            heap.free(addr).unwrap();
        }
        ok(&heap);
        assert_eq!(heap.stats().free_pages, heap.stats().pages);
    }

    #[test]
    fn an_impossible_alignment_is_refused() {
        let (mut meta, mut bits) = metadata(16);
        let mut heap = heap(&mut meta, &mut bits);
        assert_eq!(heap.alloc(8, 3), None);
        assert_eq!(heap.alloc(8, 0), None);
        assert_eq!(heap.alloc(8, 2 * PAGE_SIZE), None);
        assert_eq!(heap.alloc(usize::MAX, 8), None);
        assert_eq!(heap.stats().free_pages, 16);
    }

    #[test]
    fn freed_runs_coalesce_by_construction() {
        let (mut meta, mut bits) = metadata(10);
        let mut heap = heap(&mut meta, &mut bits);
        let a = heap.alloc(3 * PAGE_SIZE, 16).unwrap();
        let b = heap.alloc(2 * PAGE_SIZE, 16).unwrap();
        let c = heap.alloc(5 * PAGE_SIZE, 16).unwrap();
        assert_eq!(
            (a, b, c),
            (BASE, BASE + 3 * PAGE_SIZE, BASE + 5 * PAGE_SIZE)
        );
        assert_eq!(heap.alloc(PAGE_SIZE + 1, 16), None, "the arena is full");
        heap.free(b).unwrap();
        heap.free(a).unwrap();
        ok(&heap);
        // The two freed runs are one five-page hole, with no merge step.
        assert_eq!(heap.alloc(5 * PAGE_SIZE, 16), Some(BASE));
        ok(&heap);
    }

    #[test]
    fn a_run_never_spans_a_fully_used_bitmap_word() {
        // One free page at 63, the whole of word 1 (pages 64..128) in use, and
        // free pages from 128: a search that skipped the used word without
        // resetting its count would join page 63 to page 128.
        let (mut meta, mut bits) = metadata(192);
        let mut heap = heap(&mut meta, &mut bits);
        assert_eq!(heap.alloc(63 * PAGE_SIZE, 16), Some(BASE));
        let lone = heap.alloc(PAGE_SIZE, 16).unwrap();
        assert_eq!(heap.alloc(64 * PAGE_SIZE, 16), Some(BASE + 64 * PAGE_SIZE));
        heap.free(lone).unwrap();
        ok(&heap);
        assert_eq!(heap.alloc(2 * PAGE_SIZE, 16), Some(BASE + 128 * PAGE_SIZE));
        assert_eq!(
            heap.alloc(PAGE_SIZE, 16),
            Some(lone),
            "the lone page still serves one"
        );
        ok(&heap);
    }

    // -- exhaustion ----------------------------------------------------------

    #[test]
    fn exhaustion_is_reported_and_recoverable() {
        let (mut meta, mut bits) = metadata(3);
        let mut heap = heap(&mut meta, &mut bits);
        let mut live = Vec::new();
        while let Some(addr) = heap.alloc_small(2048, 255).unwrap() {
            live.push(addr);
        }
        assert_eq!(live.len(), 3 * 2);
        assert_eq!(heap.stats().free_pages, 0);
        assert_eq!(
            heap.alloc_small(8, 0),
            Ok(None),
            "no page left for another class"
        );
        assert_eq!(heap.alloc(1, 1), None);
        ok(&heap);
        heap.free_small(live[3]).unwrap();
        assert_eq!(heap.alloc_small(2048, 255), Ok(Some(live[3])));
        ok(&heap);
    }

    // -- a long random trace against a model -----------------------------------

    /// A deterministic xorshift, so a failure reproduces.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Mixed small, aligned and run allocations and frees, checked after every
    /// step against a model of the live set: no two live allocations overlap,
    /// every one lies inside the data pages, and the invariant holds.
    #[test]
    fn a_random_trace_never_overlaps_and_returns_every_page() {
        const PAGES: usize = 96;
        let (mut meta, mut bits) = metadata(PAGES);
        let mut heap = heap(&mut meta, &mut bits);
        let mut rng = Rng(0x5eed_1e4e_0b91_2001);
        let mut live: BTreeMap<usize, usize> = BTreeMap::new();
        for step in 0..30_000u32 {
            let grow = live.is_empty() || rng.below(100) < 55;
            if grow {
                let addr = match rng.below(4) {
                    0 | 1 => {
                        let slot = rng.below(SLOT_COUNT as u64) as usize;
                        heap.alloc_small(slot_size(slot), slot).unwrap()
                    }
                    2 => {
                        let size = rng.below(6000) as usize;
                        heap.alloc(size, 1 << rng.below(13))
                    }
                    _ => heap.alloc(rng.below(6 * PAGE_SIZE as u64) as usize + 1, 16),
                };
                let Some(addr) = addr else { continue };
                let size = heap.usable_size(addr).unwrap();
                assert!(
                    addr >= BASE && addr + size <= BASE + PAGES * PAGE_SIZE,
                    "step {step}"
                );
                if let Some((&prev, &prev_size)) = live.range(..addr).next_back() {
                    assert!(
                        prev + prev_size <= addr,
                        "step {step}: overlaps its predecessor"
                    );
                }
                if let Some((&next, _)) = live.range(addr..).next() {
                    assert!(addr + size <= next, "step {step}: overlaps its successor");
                }
                live.insert(addr, size);
            } else {
                let index = rng.below(live.len() as u64) as usize;
                let addr = *live.keys().nth(index).unwrap();
                heap.free(addr).unwrap();
                live.remove(&addr);
            }
            ok(&heap);
        }
        for addr in live.keys().copied().collect::<Vec<_>>() {
            heap.free(addr).unwrap();
        }
        ok(&heap);
        assert_eq!(heap.stats().free_pages, PAGES, "every page came back");
        assert!(
            heap.partial.iter().all(|&p| p == NO_PAGE),
            "every class list is empty"
        );
    }

    // -- the kernel heap, over the host stand-in for `.lean_heap` ---------------

    #[test]
    fn the_kernel_heap_serves_the_lean_contract() {
        let a = kernel_alloc_small(40, 4).expect("the kernel heap takes the arena into service");
        let b = kernel_alloc_small(40, 4).expect("room");
        let (start, len) = arena_extent();
        assert!(a >= start && a < start + len, "served from the arena");
        assert_eq!(kernel_small_size(a), Ok(40));
        assert_eq!(kernel_free_small(a), Ok(()));
        assert_eq!(
            kernel_free_small(a),
            Err(KernelHeapError::Fault(HeapFault::NotLive))
        );
        assert_eq!(kernel_free_small(b), Ok(()));
        assert_eq!(
            kernel_alloc_small(40, 3),
            Err(KernelHeapError::Fault(HeapFault::SlotMismatch))
        );
        assert_eq!(
            kernel_small_size(start),
            Err(KernelHeapError::Fault(HeapFault::OutsideArena))
        );

        // Exhaustion: the condition `lean_alloc_small` halts on is reported,
        // takes nothing, and clears when memory comes back.  This is the only
        // test that touches the kernel heap, so it may fill it.
        let mut live = Vec::new();
        let exhausted = loop {
            match kernel_alloc_small(4096, (SLOT_COUNT - 1) as u32) {
                Ok(addr) => live.push(addr),
                Err(e) => break e,
            }
        };
        assert_eq!(exhausted, KernelHeapError::Exhausted);
        let layout = ArenaLayout::of(start, len).unwrap();
        assert_eq!(
            live.len(),
            layout.pages,
            "one 4 KiB object per data page, every page served"
        );
        assert_eq!(kernel_alloc_small(8, 0), Err(KernelHeapError::Exhausted));
        for addr in live {
            assert_eq!(kernel_free_small(addr), Ok(()));
        }
        assert!(
            kernel_alloc_small(8, 0).is_ok(),
            "freed memory serves again"
        );
    }
}
