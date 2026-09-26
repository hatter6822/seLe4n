//! Where the runtime's memory comes from.
//!
//! On the image every object lives in the kernel heap (`crate::lean_heap`), the
//! one arena `lean.h`'s inline small-object paths also allocate from — so an
//! object allocated inline and freed here, or allocated here and freed inline,
//! meets the same allocator.  A host test build gives each test thread a private
//! heap instead: the tests exercise exhaustion, and a shared arena would let one
//! test's exhaustion fail another's allocation.
//!
//! Every function here answers `None` / `Err` rather than halting; deciding that
//! a failure is fatal belongs to the caller, which knows which Lean contract the
//! failure breaks.

/// Bytes a request is aligned to.  Every Lean object is word-aligned and nothing
/// the runtime allocates asks for more.
const ALIGN: usize = 8;

#[cfg(test)]
pub use backend::live_allocations;

/// `size` bytes, word-aligned, or `None` when the heap cannot serve them.
pub fn alloc(size: usize) -> Option<usize> {
    backend::alloc(size.max(1))
}

/// Returns `addr` to the heap.  `false` when `addr` is not a live allocation —
/// a lifetime error the caller must not continue past.
#[must_use]
pub fn free(addr: usize) -> bool {
    backend::free(addr).is_ok()
}

/// The usable size of the live allocation at `addr` — for a small object its
/// class size, which is what upstream's `lean_small_object_size` reports.
#[must_use]
pub fn usable_size(addr: usize) -> Option<usize> {
    backend::usable_size(addr)
}

#[cfg(not(test))]
mod backend {
    use crate::lean_heap::{self, KernelHeapError};

    pub fn alloc(size: usize) -> Option<usize> {
        lean_heap::kernel_alloc(size, super::ALIGN).ok()
    }

    pub fn free(addr: usize) -> Result<(), KernelHeapError> {
        lean_heap::kernel_free(addr)
    }

    pub fn usable_size(addr: usize) -> Option<usize> {
        lean_heap::kernel_usable_size(addr).ok()
    }
}

#[cfg(test)]
mod backend {
    extern crate std;
    use crate::lean_heap::{Heap, HeapFault, PAGE_SIZE};
    use core::cell::RefCell;
    use std::boxed::Box;
    use std::vec;

    /// Pages in each test thread's private heap: 16 MiB, zero-filled lazily by
    /// the host, which is enough for the largest operand the tests build.
    pub const PAGES: usize = 4096;

    std::thread_local! {
        static HEAP: RefCell<Heap<'static>> = RefCell::new(private_heap());
    }

    fn private_heap() -> Heap<'static> {
        // One page of slack so the page-aligned start fits inside the buffer.
        let bytes = vec![0u8; (PAGES + 1) * PAGE_SIZE].into_boxed_slice();
        let base = Box::leak(bytes).as_mut_ptr() as usize;
        let start = (base + PAGE_SIZE - 1) & !(PAGE_SIZE - 1);
        // SAFETY: `[start, start + PAGES * PAGE_SIZE)` lies inside a buffer that
        // was just leaked, so it is valid for the life of the program and no
        // other code names it.
        unsafe { Heap::from_arena(start, PAGES * PAGE_SIZE) }.expect("private test heap")
    }

    pub fn alloc(size: usize) -> Option<usize> {
        HEAP.with(|h| h.borrow_mut().alloc(size, super::ALIGN))
    }

    pub fn free(addr: usize) -> Result<(), HeapFault> {
        HEAP.with(|h| h.borrow_mut().free(addr))
    }

    pub fn usable_size(addr: usize) -> Option<usize> {
        HEAP.with(|h| h.borrow().usable_size(addr).ok())
    }

    /// Live allocations in this thread's heap, for leak checks.
    pub fn live_allocations() -> usize {
        HEAP.with(|h| h.borrow().live_allocations())
    }
}
