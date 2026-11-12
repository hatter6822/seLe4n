// SPDX-License-Identifier: GPL-3.0-or-later
//! Host tests of the region map and allocator: every boundary of the
//! allocator's rules, the backstop with a planted leaked cell, and the map's
//! independence from the bytes it describes.

extern crate std;

use core::sync::atomic::{AtomicU8, Ordering};
use std::alloc::{alloc_zeroed, dealloc, Layout};
use std::boxed::Box;
use std::vec::Vec;

use super::map::{MapRefusal, Range, RangeMap, GRANULE};
use super::*;

/// RAM for one test: a zeroed, size-aligned host buffer and its map storage.
struct Ram {
    base: usize,
    layout: Layout,
    storage: Box<[AtomicU8]>,
}

impl Ram {
    fn new(len: usize) -> Self {
        let layout = Layout::from_size_align(len, len).unwrap();
        // SAFETY: `layout` has a nonzero size.
        let base = unsafe { alloc_zeroed(layout) } as usize;
        assert_ne!(base, 0);
        let storage = (0..RangeMap::storage_bytes(len))
            .map(|_| AtomicU8::new(0))
            .collect::<Vec<_>>()
            .into_boxed_slice();
        Self {
            base,
            layout,
            storage,
        }
    }

    fn map(&self) -> RangeMap<'_> {
        RangeMap::new(self.base, &self.storage).unwrap()
    }

    fn region(&self) -> Region<'_> {
        // SAFETY: the buffer is this test's own, named only through the region.
        unsafe { Region::new(self.map()) }
    }

    /// Fills `[off, off + len)` with `byte`, as stale or user-written bytes.
    fn scribble(&self, off: usize, len: usize, byte: u8) {
        // SAFETY: inside this test's own buffer.
        unsafe { core::ptr::write_bytes((self.base + off) as *mut u8, byte, len) };
    }

    /// Writes `word` at `off`, as a forged header word.
    fn forge(&self, off: usize, word: u64) {
        // SAFETY: an aligned word inside this test's own buffer.
        unsafe { ((self.base + off) as *mut u64).write(word) };
    }
}

impl Drop for Ram {
    fn drop(&mut self) {
        // SAFETY: allocated in `Ram::new` with this layout.
        unsafe { dealloc(self.base as *mut u8, self.layout) };
    }
}

const PAGE: usize = 4096;

#[test]
fn a_range_is_aligned_and_at_least_a_granule() {
    assert_eq!(GRANULE, 512);
    assert!(Range::new(0x1000, 9).is_some());
    assert!(Range::new(0x1200, 9).is_some());
    assert!(
        Range::new(0x1100, 9).is_none(),
        "not a multiple of its size"
    );
    assert!(Range::new(0x1000, 8).is_none(), "below a granule");
    assert!(Range::new(0x2000, 13).is_some());
    assert!(Range::new(0x1000, 13).is_none());
    assert!(Range::new(usize::MAX & !511, 9).is_none(), "the end wraps");
    assert_eq!(header_bytes(9), 40, "24 + 512 / 32");
    assert_eq!(header_bytes(12), 152, "24 + 4096 / 32");
}

#[test]
fn the_map_records_whole_ranges_and_refuses_overlaps() {
    let ram = Ram::new(16 * PAGE);
    let map = ram.map();
    let b = ram.base;
    let big = Range::new(b + 2 * PAGE, 13).unwrap();
    assert_eq!(map.record(big), Ok(()));
    for addr in [big.base, big.base + 700, big.end() - 1] {
        assert_eq!(map.range_of(addr), Some(big));
    }
    assert_eq!(map.range_of(big.end()), None);
    assert_eq!(map.range_of(big.base - 1), None);
    let inside = Range::new(b + 3 * PAGE, 9).unwrap();
    assert_eq!(map.record(inside), Err(MapRefusal::Overlap));
    let around = Range::new(b, 15).unwrap();
    assert_eq!(map.record(around), Err(MapRefusal::Overlap));
    assert_eq!(
        map.range_of(big.base),
        Some(big),
        "a refusal writes nothing"
    );
    let outside = Range::new(b + 16 * PAGE, 9).unwrap();
    assert_eq!(map.record(outside), Err(MapRefusal::Uncovered));
    assert_eq!(map.unrecord(inside), Err(MapRefusal::NotRecorded));
    assert_eq!(map.unrecord(big), Ok(()));
    assert_eq!(map.range_of(big.base + 700), None);
    assert_eq!(map.record(inside), Ok(()));
    let mut met = Vec::new();
    map.for_each_meeting(b, b + 16 * PAGE, |r| met.push(r));
    assert_eq!(met, [inside]);
}

#[test]
fn a_cell_is_bumped_sized_by_the_next_start_and_freed_once() {
    let ram = Ram::new(16 * PAGE);
    let region = ram.region();
    let base = ram.base + PAGE;
    let range = region.begin_range(base, 10).unwrap();
    assert_eq!(range, Range::new(base, 10).unwrap());
    assert_eq!(region.live_count(base), Ok(0));
    let first = region.alloc(base, 24).unwrap();
    assert_eq!(first, base + header_bytes(10), "the header's successor");
    let second = region.alloc(base, 13).unwrap();
    assert_eq!(second, first + 24);
    let third = region.alloc(base, 64).unwrap();
    assert_eq!(third, second + 16, "13 bytes take 16");
    assert_eq!(region.live_count(base), Ok(3));
    assert_eq!(region.cell_size(first), Ok(24));
    assert_eq!(region.cell_size(second), Ok(16));
    assert_eq!(
        region.cell_size(third),
        Ok(64),
        "the last cell ends at the cursor"
    );
    assert_eq!(region.free(second + 8), Err(RegionFault::NotAtStart));
    assert_eq!(
        region.free(base),
        Err(RegionFault::NotAtStart),
        "the header"
    );
    assert_eq!(
        region.free(third + 64),
        Err(RegionFault::NotAtStart),
        "past the cursor"
    );
    assert_eq!(region.free(ram.base), Err(RegionFault::NotRegion));
    assert_eq!(region.free(second), Ok(()));
    assert_eq!(region.live_count(base), Ok(2));
    assert_eq!(
        region.free(second),
        Err(RegionFault::NotLive),
        "a double free"
    );
    assert_eq!(region.cell_size(second), Err(RegionFault::NotLive));
    assert_eq!(
        region.live_count(base),
        Ok(2),
        "a refused free counts nothing"
    );
    assert_eq!(
        region.cell_size(first),
        Ok(24),
        "a freed neighbour keeps its start"
    );
    // The bytes are never reused: the next cell follows the cursor.
    let fourth = region.alloc(base, 8).unwrap();
    assert_eq!(fourth, third + 64);
    assert_eq!(region.alloc(ram.base, 8), Err(RegionFault::NotRegion));
    assert_eq!(
        region.alloc(base + 512, 8),
        Err(RegionFault::NotRegion),
        "not a base"
    );
}

#[test]
fn a_bump_may_end_at_the_range_end_and_never_pass_it() {
    let ram = Ram::new(4 * PAGE);
    let region = ram.region();
    let base = ram.base;
    region.begin_range(base, 9).unwrap();
    let room = 512 - header_bytes(9);
    let fault = RegionFault::PastEnd {
        base,
        log2: 9,
        cursor: header_bytes(9),
        size: room + 1,
    };
    assert_eq!(
        region.alloc(base, room + 1),
        Err(fault),
        "one byte past the end"
    );
    assert_eq!(
        region.live_count(base),
        Ok(0),
        "a refused bump takes nothing"
    );
    let last = region.alloc(base, room).unwrap();
    assert_eq!(
        last + room,
        base + 512,
        "the last cell ends at the range's end"
    );
    assert!(matches!(
        region.alloc(base, 1),
        Err(RegionFault::PastEnd { .. })
    ));
    assert_eq!(region.cell_size(last), Ok(room));
}

#[test]
fn a_zero_over_a_live_count_of_one_halts_and_over_zero_passes() {
    let ram = Ram::new(4 * PAGE);
    let region = ram.region();
    let page = ram.base + PAGE;
    region.begin_range(page + 1024, 9).unwrap();
    let cell = region.alloc(page + 1024, 32).unwrap();
    let live = RegionFault::LiveRange {
        base: page + 1024,
        log2: 9,
        live: 1,
    };
    assert_eq!(region.retire_meeting(page, page + PAGE), Err(live));
    assert_eq!(
        region.live_count(page + 1024),
        Ok(1),
        "the refusal changes nothing"
    );
    assert_eq!(region.free(cell), Ok(()));
    assert_eq!(region.retire_meeting(page, page + PAGE), Ok(()));
    assert_eq!(
        region.live_count(page + 1024),
        Err(RegionFault::NotRegion),
        "unrecorded"
    );
}

#[test]
fn a_planted_leaked_cell_halts_the_reset_and_the_zero_until_it_is_freed() {
    let ram = Ram::new(16 * PAGE);
    let region = ram.region();
    let base = ram.base + 4 * PAGE;
    region.begin_range(base, 13).unwrap();
    let cells: Vec<_> = (0..5).map(|_| region.alloc(base, 200).unwrap()).collect();
    for &cell in &cells[..4] {
        region.free(cell).unwrap();
    }
    // The leak: one cell outlives its object's delete.
    let leaked = RegionFault::LiveRange {
        base,
        log2: 13,
        live: 1,
    };
    assert_eq!(
        region.begin_range(base, 13),
        Err(leaked),
        "a reset over the leak"
    );
    assert_eq!(
        region.begin_range(base + PAGE, 9),
        Err(leaked),
        "a smaller carve over it"
    );
    assert_eq!(
        region.begin_range(ram.base, 15),
        Err(leaked),
        "a larger carve over it"
    );
    assert_eq!(
        region.retire_meeting(base + PAGE, base + 2 * PAGE),
        Err(leaked),
        "a zero"
    );
    assert_eq!(
        region.live_count(base),
        Ok(1),
        "every refusal changes nothing"
    );
    assert_eq!(region.cell_size(cells[4]), Ok(200));
    region.free(cells[4]).unwrap();
    assert_eq!(
        region.begin_range(base + PAGE, 9).map(|r| r.base),
        Ok(base + PAGE)
    );
    // The dead 8 KiB range is unrecorded whole, not only the granule begun.
    assert_eq!(region.live_count(base), Err(RegionFault::NotRegion));
    assert_eq!(ram.map().range_of(base + 5000), None);
}

/// Writes, at every granule of `[off, off + len)`, a header claiming a
/// 512-byte range with a live count of 7, a cursor at its end and every
/// cell started and live: what a user could leave in a frame, or in a
/// thread's saved registers, before the bytes become padding.
fn forge_headers(ram: &Ram, off: usize, len: usize) {
    let mut at = off;
    while at < off + len {
        ram.forge(at, 9);
        ram.forge(at + 8, 7);
        ram.forge(at + 16, 512);
        ram.forge(at + 24, u64::MAX);
        ram.forge(at + 32, u64::MAX);
        at += GRANULE;
    }
}

#[test]
fn the_backstop_query_reads_the_map_not_forged_bytes_in_padding() {
    let ram = Ram::new(8 * PAGE);
    ram.scribble(0, 8 * PAGE, 0xA5);
    forge_headers(&ram, 0, 8 * PAGE);
    let region = ram.region();
    let page = ram.base + 2 * PAGE;
    // A page of mixed sizes, as bump carves leave it: a 512-byte range at +0,
    // padding at +512, a 1 KiB range at +1024 whose cells are all freed,
    // padding at +2048, and a 512-byte range at +3072.
    let a = region.begin_range(page, 9).unwrap();
    region.alloc(a.base, 64).unwrap();
    let b = region.begin_range(page + 1024, 10).unwrap();
    let dead = region.alloc(b.base, 64).unwrap();
    region.free(dead).unwrap();
    let c = region.begin_range(page + 3072, 9).unwrap();
    region.alloc(c.base, 16).unwrap();
    region.alloc(c.base, 16).unwrap();
    let mut live = Vec::new();
    region.for_each_live_range(page, page + PAGE, |r, n| live.push((r, n)));
    assert_eq!(live, [(a, 1), (c, 2)], "exactly the recorded live ranges");
    let mut beyond = Vec::new();
    region.for_each_live_range(ram.base, page, |r, n| beyond.push((r, n)));
    assert!(beyond.is_empty(), "forged pages hold no range");
    // A forged cell in the padding is no cell.
    for forged in [page + 512, page + 512 + 40, page + 2048 + 40, ram.base + 40] {
        assert_eq!(region.free(forged), Err(RegionFault::NotRegion));
        assert_eq!(region.cell_size(forged), Err(RegionFault::NotRegion));
        assert_eq!(region.live_count(forged), Err(RegionFault::NotRegion));
    }
    // The zero names the first live range in address order.
    assert_eq!(
        region.retire_meeting(page, page + PAGE),
        Err(RegionFault::LiveRange {
            base: a.base,
            log2: 9,
            live: 1
        })
    );
    // A carve over forged padding passes: the forged live count is not read.
    assert_eq!(
        region.begin_range(page + 512, 9),
        Ok(Range::new(page + 512, 9).unwrap())
    );
    assert_eq!(
        region.live_count(page + 512),
        Ok(0),
        "its header is the begin's own"
    );
    // A carve over the dead 1 KiB range passes and unrecords it whole.
    assert!(region.begin_range(page + 1536, 9).is_ok());
    assert_eq!(region.live_count(b.base), Err(RegionFault::NotRegion));
    // A carve meeting a live neighbour's range is refused.
    assert!(matches!(
        region.begin_range(page + 2048, 11),
        Err(RegionFault::LiveRange { base, .. }) if base == c.base
    ));
}

/// The kernel's entries with the region in service: an allocation goes to
/// the core's context range while it is held and to the heap otherwise, and
/// a free or a size query goes by address.  Run from the kernel heap's own
/// test, the only one that touches the kernel heap's entries, because the
/// context sends the host core's allocations to the range.
pub(crate) fn kernel_entries_route_by_context_and_address() {
    use crate::lean_heap::{self, KernelHeapError};
    let ram: &'static Ram = Box::leak(Box::new(Ram::new(16 * PAGE)));
    let (base, len) = (ram.base, 16 * PAGE);
    let storage = ram.storage.as_ptr() as usize;
    // SAFETY: a leaked buffer and its leaked map storage, named only here.
    assert_eq!(unsafe { register_ram(base, len, storage, 0) }, Ok(()));
    // SAFETY: refused before anything is written.
    let again = unsafe { register_ram(base + PAGE, PAGE, storage, 0) };
    assert_eq!(
        again,
        Err(RegionFault::ReservationOverlap),
        "a registered extent"
    );
    reservations_are_excluded_and_never_overlap(base, len);
    let counted = lean_heap::kernel_allocations_on(0).unwrap();
    let range = base + 2 * PAGE;
    let guard = enter_context(range, 10).expect("the range begins");
    assert_eq!(enter_context(base, 9).err(), Some(RegionFault::ContextBusy));
    let cell = lean_heap::kernel_alloc_small(40, 4).unwrap();
    assert_eq!(cell, range + header_bytes(10), "the range's first cell");
    let big = lean_heap::kernel_alloc(100, 8).unwrap();
    assert_eq!(big, cell + 40);
    assert_eq!(
        lean_heap::kernel_alloc(16, 16),
        Err(KernelHeapError::Region(RegionFault::Alignment))
    );
    assert_eq!(
        lean_heap::kernel_alloc_small(40, 3),
        Err(KernelHeapError::Fault(
            crate::lean_heap::HeapFault::SlotMismatch
        ))
    );
    assert_eq!(
        lean_heap::kernel_allocations_on(0).unwrap(),
        counted,
        "the heap served none"
    );
    assert_eq!(lean_heap::kernel_small_size(cell), Ok(40));
    assert_eq!(lean_heap::kernel_usable_size(big), Ok(104));
    assert_eq!(
        admit_page_zero(range, PAGE),
        Err(RegionFault::LiveRange {
            base: range,
            log2: 10,
            live: 2
        })
    );
    drop(guard);
    let heap_cell = lean_heap::kernel_alloc_small(40, 4).unwrap();
    assert!(
        !Range::new(base, 16).unwrap().contains(heap_cell),
        "the heap again"
    );
    assert_eq!(lean_heap::kernel_allocations_on(0).unwrap(), counted + 1);
    assert_eq!(lean_heap::kernel_free_small(heap_cell), Ok(()));
    assert_eq!(lean_heap::kernel_free_small(cell), Ok(()));
    assert_eq!(lean_heap::kernel_free(big), Ok(()));
    assert_eq!(
        lean_heap::kernel_free_small(cell),
        Err(KernelHeapError::Region(RegionFault::NotLive))
    );
    assert_eq!(
        lean_heap::kernel_free(base + 40),
        Err(KernelHeapError::Region(RegionFault::NotRegion))
    );
    assert_eq!(kernel_live_count(range), Ok(0));
    assert_eq!(admit_page_zero(range, PAGE), Ok(()));
    assert_eq!(
        kernel_live_count(range),
        Err(RegionFault::NotRegion),
        "unrecorded"
    );
    assert_eq!(ram.storage[0].load(Ordering::Relaxed), 0);
}

/// A second extent registered as the boot registers one, with its map in a
/// reservation at its top: the reservation is excluded from thread RAM, its
/// covered RAM is not, and no later extent or reservation may meet either it
/// or the first extent `[first, first + first_len)`.  Called from the routing
/// test, the one test that registers segments.
fn reservations_are_excluded_and_never_overlap(first: usize, first_len: usize) {
    let ram: &'static Ram = Box::leak(Box::new(Ram::new(4 * PAGE)));
    let (covered, map_base) = (ram.base, ram.base + 3 * PAGE);
    // SAFETY: a leaked, zeroed buffer named only here; its top page holds the
    // map of the three below.
    let registered = unsafe { register_ram(covered, 3 * PAGE, map_base, PAGE) };
    assert_eq!(registered, Ok(()));
    assert!(meets_reservation(map_base, PAGE));
    assert!(meets_reservation(map_base + PAGE - 1, 1));
    assert!(
        meets_reservation(covered + 2 * PAGE, 2 * PAGE),
        "a page across its start"
    );
    assert!(
        !meets_reservation(covered, 3 * PAGE),
        "the covered RAM is a thread's"
    );
    assert!(!meets_reservation(first, first_len));
    assert!(!meets_reservation(map_base + PAGE, PAGE), "past its end");
    // SAFETY: each is refused before anything is written.
    unsafe {
        assert_eq!(
            register_ram(map_base, PAGE, map_base + PAGE, PAGE),
            Err(RegionFault::ReservationOverlap),
            "an extent over a reservation"
        );
        assert_eq!(
            register_ram(map_base + PAGE, PAGE, first + PAGE, PAGE),
            Err(RegionFault::ReservationOverlap),
            "a reservation in a covered extent"
        );
        assert_eq!(
            register_ram(map_base + PAGE, PAGE, map_base, PAGE),
            Err(RegionFault::ReservationOverlap),
            "a reservation over a reservation"
        );
        assert_eq!(
            register_ram(map_base + PAGE, PAGE, map_base + PAGE, PAGE),
            Err(RegionFault::ReservationOverlap),
            "a reservation in its own extent"
        );
        assert_eq!(
            register_ram(map_base + PAGE, 0, map_base + 2 * PAGE, PAGE),
            Err(RegionFault::Misaligned)
        );
    }
    // The registered map serves the covered RAM's last granule from the
    // reservation's bytes.
    let range = covered + 3 * PAGE - GRANULE;
    let guard = enter_context(range, 9).expect("the last granule begins");
    drop(guard);
    assert_eq!(kernel_live_count(range), Ok(0));
    assert_eq!(admit_page_zero(covered + 2 * PAGE, PAGE), Ok(()));
    assert_eq!(kernel_live_count(range), Err(RegionFault::NotRegion));
    assert_eq!(
        enter_context(map_base, 9).err(),
        Some(RegionFault::Uncovered)
    );
}

/// The QEMU boot's extension `[0x5000_0000, 0x8000_0000)` as the Lean boot
/// lays it out (`qemuVirtRegionMap_layout`): the untyped covers up to
/// `0x7FE8_0000`, and the map's 1569792 bytes take the 384 pages above.
#[test]
fn the_reservation_layout_matches_the_boot_and_fits_the_extension() {
    let mapped = |b: u64, l: u64| b >= 0x5000_0000 && b + l <= 0x8000_0000;
    let layout = reservation_layout(0x5000_0000, 0x2FE8_0000, 0x7FE8_0000, mapped);
    assert_eq!(
        layout,
        Ok(Reservation {
            covered_base: 0x5000_0000,
            covered_len: 0x2FE8_0000,
            map_base: 0x7FE8_0000,
            storage_len: 1_569_792,
            reserved_len: 0x18_0000,
        })
    );
    // The map's last page ends at the extension's end, and a map one page
    // higher is refused, not truncated.
    assert_eq!(0x7FE8_0000_usize + 0x18_0000, 0x8000_0000);
    assert_eq!(
        reservation_layout(0x5000_0000, 0x2FE8_0000, 0x7FE8_1000, mapped),
        Err(RegionFault::ReservationUnmapped)
    );
    // Covered RAM past the mapped RAM is refused.
    assert_eq!(
        reservation_layout(0x5000_0000, 0x3000_0000, 0x8000_0000, mapped),
        Err(RegionFault::ReservationUnmapped)
    );
    // A map meeting its covered RAM is refused.
    assert_eq!(
        reservation_layout(0x5000_0000, 0x2FE8_0000, 0x7FE7_F000, mapped),
        Err(RegionFault::ReservationOverlap)
    );
    assert_eq!(
        reservation_layout(0x5000_0000, 0x2FE8_0000, 0x4FFF_F000, mapped),
        Err(RegionFault::ReservationOverlap),
        "a map below its RAM that runs into it"
    );
    // Unaligned or empty input is refused.
    for (base, len, map) in [
        (0x5000_0200, 0x1000, 0x7FE8_0000),
        (0x5000_0000, 0x1200, 0x7FE8_0000),
        (0x5000_0000, 0x1000, 0x7FE8_0200),
        (0x5000_0000, 0, 0x7FE8_0000),
    ] {
        assert_eq!(
            reservation_layout(base, len, map, mapped),
            Err(RegionFault::Misaligned)
        );
    }
}

/// The map, kept in the top page of its extension as the boot keeps it,
/// describes every granule of the covered RAM below and nothing above it, and
/// its bytes are the reservation's alone.
#[test]
fn the_reserved_map_finds_ranges_over_all_covered_ram() {
    let ram = Ram::new(64 * PAGE);
    let covered = 63 * PAGE;
    let reserved = reservation_layout(ram.base, covered, ram.base + covered, |_, _| true)
        .expect("the layout fits");
    assert_eq!(reserved.storage_len, covered / GRANULE);
    assert_eq!(reserved.reserved_len, PAGE);
    // SAFETY: the buffer's top page, zeroed and named only as the map.
    let storage = unsafe {
        core::slice::from_raw_parts(
            (ram.base + covered) as *const AtomicU8,
            reserved.storage_len,
        )
    };
    let map = RangeMap::new(ram.base, storage).unwrap();
    assert_eq!(map.end(), ram.base + covered);
    let first = Range::new(ram.base, 9).unwrap();
    let last = Range::new(ram.base + covered - GRANULE, 9).unwrap();
    let middle = Range::new(ram.base + 32 * PAGE, 15).unwrap();
    for range in [first, last, middle] {
        assert_eq!(map.record(range), Ok(()));
    }
    assert_eq!(map.range_of(ram.base), Some(first));
    assert_eq!(map.range_of(ram.base + covered - 1), Some(last));
    assert_eq!(map.range_of(ram.base + 40 * PAGE - 8), Some(middle));
    assert_eq!(map.range_of(ram.base + covered), None, "the reservation");
    assert_eq!(
        map.record(Range::new(ram.base + covered, 9).unwrap()),
        Err(MapRefusal::Uncovered)
    );
    assert_eq!(
        map.record(Range::new(ram.base, 18).unwrap()),
        Err(MapRefusal::Uncovered),
        "a range running into the reservation"
    );
    // The map's bytes are in the reservation: the covered RAM reads as zero.
    // SAFETY: inside this test's own buffer.
    let below = unsafe { core::slice::from_raw_parts(ram.base as *const u8, covered) };
    assert!(below.iter().all(|&b| b == 0));
    assert_eq!(storage[0].load(Ordering::Relaxed), 9);
    assert_eq!(storage[reserved.storage_len - 1].load(Ordering::Relaxed), 9);
}
