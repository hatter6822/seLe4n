//! Objects: allocation, the last reference's release, persistence, panics,
//! `ST.Ref` and the runtime's two hash functions.
//!
//! Ported from `src/runtime/object.cpp`, `io.cpp` and `hash.{h,cpp}` of the
//! `lean4` release the toolchain was built from.  Each function says which
//! upstream function it is and where it departs, if it does.

use super::{
    dec, diagnostic, fatal, header, inc, is_scalar, mem, tag, ArrayObject, ClosureObject,
    ExternalObject, LeanObject, Obj, RefObject, ThunkObject, MAX_CTOR_TAG, TAG_ARRAY, TAG_CLOSURE,
    TAG_EXTERNAL, TAG_MPZ, TAG_REF, TAG_SCALAR_ARRAY, TAG_STRING, TAG_THUNK,
};

// ==========================================================================
// Allocation
// ==========================================================================

/// `lean_alloc_object(sz)`: `sz` bytes for an object whose header the caller
/// writes.  Upstream's small-allocator build serves requests up to
/// `LEAN_MAX_SMALL_OBJECT_SIZE` from the small classes and larger ones from the
/// system heap; the kernel heap does both, from one arena.  Halts on exhaustion
/// (`lean_internal_panic_out_of_memory`), since no caller tests the result.
#[must_use]
pub fn alloc_object(sz: usize) -> Obj {
    match mem::alloc(sz) {
        Some(addr) => addr as Obj,
        None => internal_panic_out_of_memory(),
    }
}

/// `lean_free_object(o)`: returns `o`'s memory without touching the objects it
/// refers to.  Upstream dispatches on the kind to compute the size its
/// deallocator wants; the kernel heap finds the size from the address.
///
/// # Safety
///
/// `o` must be a live heap object no reference will be used again.
pub unsafe fn free_object(o: Obj) {
    if !mem::free(o as usize) {
        fatal("lean_free_object: not a live object");
    }
}

// ==========================================================================
// Releasing the last reference
// ==========================================================================
//
// `lean_dec_ref_cold` must not recurse: a list of a million cells is a chain a
// million deep.  Upstream threads a to-do list through the headers of the
// objects being freed — an object whose count has reached zero has no other
// use for `m_rc` and `m_cs_sz`, whose 48 bits hold the next pointer, while
// `m_other` and `m_tag` stay readable — and this does the same.

const NEXT_MASK: u64 = (1 << 48) - 1;

/// The next object on the to-do list threaded through `o`'s header.
///
/// # Safety
///
/// `o` must be on the to-do list: a heap object whose count reached zero and
/// whose header word the release owns.
unsafe fn get_next(o: Obj) -> Obj {
    // SAFETY: `o` is on the to-do list by this function's contract.
    let word = unsafe { o.cast::<u64>().read() };
    (word & NEXT_MASK) as usize as Obj
}

/// Threads `next` through `o`'s header word, keeping `m_other` and `m_tag`.
///
/// # Safety
///
/// `o` must be a live heap object whose count has reached zero, so the release
/// owns its header word.
unsafe fn set_next(o: Obj, next: Obj) {
    let n = next as usize as u64;
    if n & !NEXT_MASK != 0 {
        fatal("lean_dec_ref_cold: object address beyond 48 bits");
    }
    // SAFETY: by this function's contract the release owns `o`'s header word.
    unsafe {
        let word = o.cast::<u64>().read();
        o.cast::<u64>().write((word & !NEXT_MASK) | n);
    }
}

/// `dec(o, todo)` of `object.cpp`: drop one reference to a child of an object
/// being freed, queueing the child when that was its last.
///
/// # Safety
///
/// `o` must be a scalar or a live object, the field of an object being freed.
unsafe fn release_child(o: Obj, todo: &mut Obj) {
    if is_scalar(o) {
        return;
    }
    // SAFETY: by this function's contract `o` is a live object, scalars having
    // returned above.
    let h = unsafe { header(o) };
    match h.rc {
        rc if rc > 1 => h.rc = rc - 1,
        1 => {
            // SAFETY: `o`'s count has just reached zero, so the release owns its
            // header word.
            unsafe { set_next(o, *todo) };
            *todo = o;
        }
        0 => {}
        _ => fatal("lean_dec_ref_cold: multi-threaded object"),
    }
}

/// The `n` object slots starting `offset` bytes into `o`.
///
/// # Safety
///
/// `o` must be a live object holding `n` object fields at `offset`, and stay
/// live while the iterator is consumed.
unsafe fn slots(o: Obj, offset: usize, n: usize) -> impl Iterator<Item = Obj> {
    (0..n).map(move |i| {
        // SAFETY: `o` holds `n` object fields at `offset` by `slots`'s contract.
        unsafe { o.cast::<u8>().add(offset).cast::<Obj>().add(i).read() }
    })
}

/// `lean_del_core`: frees `o`, whose count has reached zero, queueing each child
/// that loses its last reference.
///
/// # Safety
///
/// `o` must be a live object whose count has reached zero.
unsafe fn del_core(o: Obj, todo: &mut Obj) {
    // SAFETY: `o` is live by this function's contract; its kind decides its
    // layout below.
    let (kind, other) = unsafe { (tag(o), header(o).other) };
    match kind {
        t if t <= MAX_CTOR_TAG => {
            // SAFETY: a constructor holds `other` object fields after its
            // header, each a scalar or a live object.
            unsafe {
                for child in slots(o, super::HEADER_BYTES, usize::from(other)) {
                    release_child(child, todo);
                }
            }
        }
        TAG_CLOSURE => {
            // SAFETY: `o` is a live closure.
            let fixed = unsafe { (*o.cast::<ClosureObject>()).num_fixed };
            // SAFETY: a closure holds `num_fixed` object fields after its fixed
            // part, each a scalar or a live object.
            unsafe {
                for child in slots(o, super::CLOSURE_BYTES, usize::from(fixed)) {
                    release_child(child, todo);
                }
            }
        }
        TAG_ARRAY => {
            // SAFETY: `o` is a live array.
            let size = unsafe { (*o.cast::<ArrayObject>()).size };
            // SAFETY: an array holds `size` elements, each a scalar or a live
            // object.
            unsafe {
                for child in slots(o, super::ARRAY_BYTES, size) {
                    release_child(child, todo);
                }
            }
        }
        TAG_SCALAR_ARRAY | TAG_STRING | TAG_MPZ => {}
        TAG_THUNK => {
            // SAFETY: `o` is a live thunk.
            let t = unsafe { &*o.cast::<ThunkObject>() };
            for child in [t.closure, t.value] {
                if !child.is_null() {
                    // SAFETY: a non-null thunk field is a scalar or a live object.
                    unsafe { release_child(child, todo) };
                }
            }
        }
        TAG_REF => {
            // SAFETY: `o` is a live reference cell.
            let v = unsafe { (*o.cast::<RefObject>()).value };
            if !v.is_null() {
                // SAFETY: a non-null cell value is a scalar or a live object.
                unsafe { release_child(v, todo) };
            }
        }
        TAG_EXTERNAL => {
            // SAFETY: `o` is a live external object whose class was registered
            // by the code that created it.
            unsafe {
                let e = &*o.cast::<ExternalObject>();
                ((*e.class).finalize)(e.data);
            }
        }
        _ => fatal("lean_dec_ref_cold: task, promise or unknown object kind"),
    }
    // SAFETY: every reference `o` held has been released above.
    unsafe { free_object(o) };
}

/// `lean_dec_ref_cold(o)`: `lean.h`'s `lean_dec_ref` calls this when `o`'s count
/// is not above one.  At one, `o` and everything only it reaches are freed; a
/// persistent object is left alone.
///
/// # Safety
///
/// `o` must be a live heap object and the caller's reference to it is consumed.
pub unsafe fn dec_ref_cold(o: Obj) {
    // SAFETY: forwarded from the caller.
    let rc = unsafe { header(o).rc };
    match rc {
        1 => {}
        0 => return,
        rc if rc < 0 => fatal("lean_dec_ref_cold: multi-threaded object"),
        _ => {
            // `lean.h` only calls here at or below one; honour the count anyway.
            // SAFETY: forwarded from the caller.
            unsafe { header(o).rc = rc - 1 };
            return;
        }
    }
    let mut todo: Obj = core::ptr::null_mut();
    let mut current = o;
    loop {
        // SAFETY: `current` is `o`, whose count the caller's reference held at
        // one, or came off the to-do list, where only objects whose count
        // reached zero are queued.
        unsafe { del_core(current, &mut todo) };
        if todo.is_null() {
            return;
        }
        current = todo;
        // SAFETY: `current` is on the to-do list.
        todo = unsafe { get_next(current) };
    }
}

// ==========================================================================
// Persistence
// ==========================================================================

/// A stack of objects in kernel-heap pages, for the one traversal that needs an
/// unbounded worklist: marking an object graph persistent sets every count to
/// zero, which is the "already visited" test, so no header bit is left to
/// thread a list through.  Upstream uses a `std::vector`.
struct WorkStack {
    top: *mut Chunk,
}

const CHUNK_ITEMS: usize = 510;

#[repr(C)]
struct Chunk {
    prev: *mut Chunk,
    len: usize,
    items: [Obj; CHUNK_ITEMS],
}

const _: () = assert!(core::mem::size_of::<Chunk>() == 4096);

impl WorkStack {
    fn new() -> Self {
        Self {
            top: core::ptr::null_mut(),
        }
    }

    fn push(&mut self, o: Obj) {
        // SAFETY: `top` is null or a chunk this stack allocated and owns.
        let full = self.top.is_null() || unsafe { (*self.top).len == CHUNK_ITEMS };
        if full {
            let chunk = alloc_object(core::mem::size_of::<Chunk>()).cast::<Chunk>();
            // SAFETY: `chunk` is a fresh allocation of a chunk's size.
            unsafe {
                (*chunk).prev = self.top;
                (*chunk).len = 0;
            }
            self.top = chunk;
        }
        // SAFETY: `top` is a chunk this stack owns, with room for one more item.
        unsafe {
            let c = &mut *self.top;
            c.items[c.len] = o;
            c.len += 1;
        }
    }

    fn pop(&mut self) -> Option<Obj> {
        loop {
            if self.top.is_null() {
                return None;
            }
            // SAFETY: `top` is a chunk this stack allocated and owns.
            let c = unsafe { &mut *self.top };
            if c.len > 0 {
                c.len -= 1;
                return Some(c.items[c.len]);
            }
            let prev = c.prev;
            // SAFETY: the chunk is empty and nothing else refers to it.
            unsafe { free_object(self.top.cast()) };
            self.top = prev;
        }
    }
}

/// The closure body `mark_persistent` applies to an external object's
/// children through the class's `foreach`.
///
/// # Safety
///
/// `o` is a scalar or a live heap object: what an external class's `foreach`
/// hands the closure it is given.
unsafe extern "C" fn mark_persistent_fn(o: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe { mark_persistent(o) };
    super::boxed(0)
}

/// `lean_mark_persistent(o)`: sets the count of `o` and of every object it
/// reaches to zero, so reference counting no longer touches them.  The library
/// initializer calls this on every global it computes.
///
/// # Safety
///
/// `o` must be a scalar or a live heap object.
pub unsafe fn mark_persistent(o: Obj) {
    let mut todo = WorkStack::new();
    todo.push(o);
    while let Some(o) = todo.pop() {
        if is_scalar(o) {
            continue;
        }
        // SAFETY: every pushed pointer is a field of a live object, hence live.
        let h = unsafe { header(o) };
        if h.rc == 0 {
            continue;
        }
        h.rc = 0;
        let (kind, other) = (h.tag, h.other);
        // The object fields of `o`, by the layout of its own kind.
        let fields = match kind {
            t if t <= MAX_CTOR_TAG => Some((super::HEADER_BYTES, usize::from(other))),
            TAG_CLOSURE => {
                // SAFETY: `o` is a live closure.
                let fixed = unsafe { (*o.cast::<ClosureObject>()).num_fixed };
                Some((super::CLOSURE_BYTES, usize::from(fixed)))
            }
            TAG_ARRAY => {
                // SAFETY: `o` is a live array.
                let size = unsafe { (*o.cast::<ArrayObject>()).size };
                Some((super::ARRAY_BYTES, size))
            }
            _ => None,
        };
        if let Some((offset, n)) = fields {
            // SAFETY: `o` is live and holds `n` object fields at `offset`, the
            // layout of its kind computed above.
            for child in unsafe { slots(o, offset, n) } {
                todo.push(child);
            }
            continue;
        }
        match kind {
            TAG_SCALAR_ARRAY | TAG_STRING | TAG_MPZ => {}
            TAG_THUNK => {
                // SAFETY: `o` is a live thunk.
                let t = unsafe { &*o.cast::<ThunkObject>() };
                for child in [t.closure, t.value] {
                    if !child.is_null() {
                        todo.push(child);
                    }
                }
            }
            TAG_REF => {
                // SAFETY: `o` is a live reference cell.
                let v = unsafe { (*o.cast::<RefObject>()).value };
                if !v.is_null() {
                    todo.push(v);
                }
            }
            TAG_EXTERNAL => {
                let f = super::apply::alloc_closure(mark_persistent_fn as *const (), 1, 0);
                // SAFETY: `o` is a live external object; its class's `foreach`
                // applies `f` to each object the data holds and borrows `f`.
                unsafe {
                    let e = &*o.cast::<ExternalObject>();
                    ((*e.class).foreach)(e.data, f);
                    dec(f);
                }
            }
            _ => fatal("lean_mark_persistent: task, promise or unknown object kind"),
        }
    }
}

// ==========================================================================
// Panics
// ==========================================================================

/// `lean_panic_fn(default, msg)`: reports `msg` and returns `default`.
///
/// This is what upstream does — and it is what the kernel's proofs describe:
/// `panic! msg : α` is `default` by its reference implementation, so every
/// theorem about a function containing one is a theorem about the function
/// returning `default` there.  Halting instead would make the running kernel
/// diverge from its own model on exactly the paths the model covers.  The
/// report goes to the boot UART.
///
/// # Safety
///
/// `msg` must be a live string whose reference this call consumes.
pub unsafe fn panic_fn(default: Obj, msg: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    diagnostic("PANIC: ", unsafe { super::string::bytes(msg) });
    // SAFETY: forwarded from the caller.
    unsafe { dec(msg) };
    default
}

/// `lean_internal_panic_out_of_memory`.
pub fn internal_panic_out_of_memory() -> ! {
    fatal("out of memory")
}

/// `lean_internal_panic_unreachable`.
pub fn internal_panic_unreachable() -> ! {
    fatal("unreachable code has been reached")
}

// ==========================================================================
// ST.Ref
// ==========================================================================
//
// Upstream treats a reference cell that is persistent (created by an
// initializer) as possibly shared between threads and goes through atomics.
// No Lean code in the kernel runs on two cores at once, so every cell is read
// and written directly; a cell whose value is taken when it is read is a
// contract violation rather than another thread's write in flight.

/// `lean_st_mk_ref(a)`.
#[must_use]
pub fn st_mk_ref(a: Obj) -> Obj {
    let o = alloc_object(core::mem::size_of::<RefObject>());
    // SAFETY: `o` is a fresh allocation of a reference cell's size.
    unsafe {
        o.cast::<RefObject>().write(RefObject {
            header: LeanObject {
                rc: 1,
                cs_sz: 0,
                other: 0,
                tag: TAG_REF,
            },
            value: a,
        });
    }
    o
}

/// The reference-cell record of `r`.
///
/// # Safety
///
/// `r` must be a live reference cell, not otherwise referenced for `'a`.
unsafe fn ref_cell<'a>(r: Obj) -> &'a mut RefObject {
    // SAFETY: `r` is a live reference cell by this function's contract.
    unsafe { &mut *r.cast::<RefObject>() }
}

/// `lean_st_ref_get(ref)`: the value, with a new reference to it.
///
/// # Safety
///
/// `r` must be a live reference cell.
pub unsafe fn st_ref_get(r: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    let v = unsafe { ref_cell(r).value };
    if v.is_null() {
        fatal("ST.Ref read while its value is taken");
    }
    // SAFETY: the cell holds a reference to `v`, so it is live.
    unsafe { inc(v) };
    v
}

/// `lean_st_ref_take(ref)`: the value, leaving the cell empty.
///
/// # Safety
///
/// `r` must be a live reference cell.
pub unsafe fn st_ref_take(r: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    let cell = unsafe { ref_cell(r) };
    let v = cell.value;
    if v.is_null() {
        fatal("ST.Ref taken twice");
    }
    cell.value = core::ptr::null_mut();
    v
}

/// `lean_st_ref_set(ref, a)`: stores `a`, releasing the old value.
///
/// # Safety
///
/// `r` must be a live reference cell; the reference to `a` is consumed.
pub unsafe fn st_ref_set(r: Obj, a: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    let cell = unsafe { ref_cell(r) };
    let old = core::mem::replace(&mut cell.value, a);
    if !old.is_null() {
        // SAFETY: the cell held a reference to `old`, now released.
        unsafe { dec(old) };
    }
    super::boxed(0)
}

// ==========================================================================
// Hashing
// ==========================================================================

const MURMUR_M: u64 = 0xc6a4_a793_5bd1_e995;

/// `hash(h, k)` of `hash.h` — `lean_uint64_mix_hash`.  The second step is
/// `k ^= m`, not `k *= m`: that is upstream's function, and every hash table the
/// kernel's Lean code builds depends on it.
#[must_use]
pub fn mix_hash(h: u64, k: u64) -> u64 {
    let mut k = k.wrapping_mul(MURMUR_M);
    k ^= k >> 47;
    k ^= MURMUR_M;
    (h ^ k).wrapping_mul(MURMUR_M)
}

/// `hash_str` of `hash.cpp`: MurmurHash64A over `bytes` with `seed`.
#[must_use]
pub fn hash_bytes(bytes: &[u8], seed: u64) -> u64 {
    let len = bytes.len() as u64;
    let mut h = seed ^ len.wrapping_mul(MURMUR_M);
    let mut chunks = bytes.chunks_exact(8);
    for chunk in &mut chunks {
        let mut word = [0u8; 8];
        word.copy_from_slice(chunk);
        let mut k = u64::from_le_bytes(word).wrapping_mul(MURMUR_M);
        k ^= k >> 47;
        k = k.wrapping_mul(MURMUR_M);
        h ^= k;
        h = h.wrapping_mul(MURMUR_M);
    }
    let tail = chunks.remainder();
    if !tail.is_empty() {
        for (i, &b) in tail.iter().enumerate() {
            h ^= u64::from(b) << (8 * i);
        }
        h = h.wrapping_mul(MURMUR_M);
    }
    h ^= h >> 47;
    h = h.wrapping_mul(MURMUR_M);
    h ^ (h >> 47)
}

// ==========================================================================
// Names and structural sharing
// ==========================================================================

/// `lean_name_eq(n1, n2)`: `Name` equality, short-cut by the hash each name
/// cell caches after its two object fields.
///
/// # Safety
///
/// Both must be `Name`s (a scalar for the anonymous name), borrowed.
#[must_use]
pub unsafe fn name_eq(mut n1: Obj, mut n2: Obj) -> bool {
    if n1 == n2 {
        return true;
    }
    if is_scalar(n1) != is_scalar(n2) {
        return false;
    }
    // SAFETY: both are name cells (the scalar case returned above); the cached
    // hash is the scalar field at offset 16.
    if unsafe { super::ctor_get_u64(n1, 16) != super::ctor_get_u64(n2, 16) } {
        return false;
    }
    loop {
        // SAFETY: both are live name cells: `str p s` (tag 1) or `num p k`.
        unsafe {
            if tag(n1) != tag(n2) {
                return false;
            }
            let (f1, f2) = (super::ctor_get(n1, 1), super::ctor_get(n2, 1));
            let same = if tag(n1) == 1 {
                f1 == f2
                    || (super::string::bytes(f1).len() == super::string::bytes(f2).len()
                        && super::string::eq_cold(f1, f2))
            } else {
                (is_scalar(f1) && is_scalar(f2) && f1 == f2)
                    || (!(is_scalar(f1) && is_scalar(f2))
                        && super::nat::nat_big_cmp(f1, f2) == core::cmp::Ordering::Equal)
            };
            if !same {
                return false;
            }
            n1 = super::ctor_get(n1, 0);
            n2 = super::ctor_get(n2, 0);
        }
        if n1 == n2 {
            return true;
        }
        if is_scalar(n1) != is_scalar(n2) {
            return false;
        }
    }
}

/// `lean_object_data_byte_size(o)`: the bytes of `o` that carry its value.
///
/// # Safety
///
/// `o` must be a live heap object.
unsafe fn data_byte_size(o: Obj) -> usize {
    // SAFETY: forwarded from the caller; each arm reads the kind it matched.
    unsafe {
        match tag(o) {
            TAG_ARRAY => super::ARRAY_BYTES + 8 * (*o.cast::<ArrayObject>()).size,
            TAG_SCALAR_ARRAY => {
                let a = &*o.cast::<super::SArrayObject>();
                core::mem::size_of::<super::SArrayObject>() + a.size * usize::from(a.header.other)
            }
            TAG_STRING => super::STRING_BYTES + (*o.cast::<super::StringObject>()).size,
            TAG_CLOSURE => {
                super::CLOSURE_BYTES + 8 * usize::from((*o.cast::<ClosureObject>()).num_fixed)
            }
            _ => mem::usable_size(o as usize)
                .unwrap_or_else(|| fatal("lean_object_data_byte_size: not a live object")),
        }
    }
}

/// `lean_sharecommon_eq(o1, o2)`: whether two objects have the same kind and
/// the same bytes (for a big number, the same value).  `ShareCommon` uses it to
/// merge structurally equal objects.
///
/// # Safety
///
/// Both must be live heap objects, borrowed.
#[must_use]
pub unsafe fn sharecommon_eq(o1: Obj, o2: Obj) -> bool {
    // SAFETY: forwarded from the caller.
    unsafe {
        if tag(o1) != tag(o2) || header(o1).other != header(o2).other {
            return false;
        }
        // The v0.36.2 audit: a big number is compared by VALUE before any
        // size is read.  `data_byte_size` answers a number's allocation class,
        // and `Building::new` sizes a number by the *capacity* its producer
        // could need (`nat_shiftl`, `nat_pow`, `divrem`, `cstr_to_nat` all
        // over-reserve), so two equal values routinely live in different
        // classes and a size test first answered `false` for them.
        if tag(o1) == TAG_MPZ {
            return super::nat::nat_big_cmp(o1, o2) == core::cmp::Ordering::Equal
                && super::nat::int_big_nonneg(o1) == super::nat::int_big_nonneg(o2);
        }
        let (sz1, sz2) = (data_byte_size(o1), data_byte_size(o2));
        if sz1 != sz2 {
            return false;
        }
        let h = super::HEADER_BYTES;
        let b1 = core::slice::from_raw_parts(o1.cast::<u8>().add(h), sz1 - h);
        let b2 = core::slice::from_raw_parts(o2.cast::<u8>().add(h), sz2 - h);
        b1 == b2
    }
}

/// `lean_sharecommon_hash(o)`: a hash consistent with [`sharecommon_eq`].  A big
/// number hashes its sign and its `size` limbs — the value, never the
/// capacity limbs behind it (the v0.36.2 audit: hashing the whole allocation
/// gave equal values different hashes whenever their producers reserved
/// differently); upstream hashes GMP's representation, which no two builds
/// need agree on, so only consistency is owed here.
///
/// # Safety
///
/// `o` must be a live heap object, borrowed.
#[must_use]
pub unsafe fn sharecommon_hash(o: Obj) -> u64 {
    // SAFETY: forwarded from the caller.
    unsafe {
        let t = tag(o);
        if t == TAG_MPZ {
            let (neg, limbs) = super::nat::mpz_parts(o);
            return limbs
                .iter()
                .fold(mix_hash(u64::from(t), u64::from(neg)), |h, &limb| {
                    mix_hash(h, limb)
                });
        }
        let sz = data_byte_size(o);
        let init = mix_hash(u64::from(t), u64::from(header(o).other));
        let h = super::HEADER_BYTES;
        hash_bytes(
            core::slice::from_raw_parts(o.cast::<u8>().add(h), sz - h),
            init & 0xffff_ffff,
        )
    }
}

// ==========================================================================
// The exported names
// ==========================================================================

#[cfg(feature = "hw_target")]
mod exports {
    use super::*;

    /// `lean_alloc_object`.
    #[no_mangle]
    pub extern "C" fn lean_alloc_object(sz: usize) -> Obj {
        alloc_object(sz)
    }

    /// `lean_free_object`.
    ///
    /// # Safety
    ///
    /// `o` is a live heap object that no reference will be used again: `lean.h`'s `lean_free_object` contract.
    #[no_mangle]
    pub unsafe extern "C" fn lean_free_object(o: Obj) {
        // SAFETY: `lean.h`'s contract: `o` is live and dead after this call.
        unsafe { free_object(o) }
    }

    /// `lean_dec_ref_cold`.
    ///
    /// # Safety
    ///
    /// `o` is an owned reference to a live object, which this call consumes; `lean.h`'s inline `lean_dec_ref` is the caller.
    #[no_mangle]
    pub unsafe extern "C" fn lean_dec_ref_cold(o: Obj) {
        // SAFETY: `lean.h` calls this with an owned reference to a live object.
        unsafe { dec_ref_cold(o) }
    }

    /// `lean_mark_persistent`.
    ///
    /// # Safety
    ///
    /// `o` is a scalar or a live heap object the module initializer just computed and will never release.
    #[no_mangle]
    pub unsafe extern "C" fn lean_mark_persistent(o: Obj) {
        // SAFETY: the initializer passes a global it just computed.
        unsafe { mark_persistent(o) }
    }

    /// `lean_panic_fn`.
    ///
    /// # Safety
    ///
    /// `default` is an owned object and `msg` an owned live string, as the compiled `panic!` passes them.
    #[no_mangle]
    pub unsafe extern "C" fn lean_panic_fn(default: Obj, msg: Obj) -> Obj {
        // SAFETY: the compiled `panic!` passes an owned message string.
        unsafe { panic_fn(default, msg) }
    }

    /// `lean_internal_panic`.
    ///
    /// # Safety
    ///
    /// `msg` must point to a zero-terminated string.
    #[no_mangle]
    pub unsafe extern "C" fn lean_internal_panic(msg: *const u8) -> ! {
        // SAFETY: forwarded from the caller.
        let text = unsafe { core::ffi::CStr::from_ptr(msg.cast()) };
        diagnostic("INTERNAL PANIC: ", text.to_bytes());
        fatal("lean_internal_panic")
    }

    /// `lean_internal_panic_out_of_memory`.
    #[no_mangle]
    pub extern "C" fn lean_internal_panic_out_of_memory() -> ! {
        internal_panic_out_of_memory()
    }

    /// `lean_internal_panic_unreachable`.
    #[no_mangle]
    pub extern "C" fn lean_internal_panic_unreachable() -> ! {
        internal_panic_unreachable()
    }

    /// `lean_internal_panic_rc_overflow`.
    #[no_mangle]
    pub extern "C" fn lean_internal_panic_rc_overflow() -> ! {
        fatal("reference count overflow")
    }

    /// `lean_st_mk_ref`.
    #[no_mangle]
    pub extern "C" fn lean_st_mk_ref(a: Obj) -> Obj {
        st_mk_ref(a)
    }

    /// `lean_st_ref_get`.
    ///
    /// # Safety
    ///
    /// The caller passes a borrowed reference cell.
    #[no_mangle]
    pub unsafe extern "C" fn lean_st_ref_get(r: Obj) -> Obj {
        // SAFETY: a borrowed reference cell.
        unsafe { st_ref_get(r) }
    }

    /// `lean_st_ref_take`.
    ///
    /// # Safety
    ///
    /// The caller passes a borrowed reference cell.
    #[no_mangle]
    pub unsafe extern "C" fn lean_st_ref_take(r: Obj) -> Obj {
        // SAFETY: a borrowed reference cell.
        unsafe { st_ref_take(r) }
    }

    /// `lean_st_ref_set`.
    ///
    /// # Safety
    ///
    /// The caller passes a borrowed reference cell and an owned value.
    #[no_mangle]
    pub unsafe extern "C" fn lean_st_ref_set(r: Obj, a: Obj) -> Obj {
        // SAFETY: a borrowed reference cell and an owned value.
        unsafe { st_ref_set(r, a) }
    }

    /// `lean_name_eq`.
    ///
    /// # Safety
    ///
    /// The caller passes two borrowed names.
    #[no_mangle]
    pub unsafe extern "C" fn lean_name_eq(n1: Obj, n2: Obj) -> u8 {
        // SAFETY: two borrowed names.
        u8::from(unsafe { name_eq(n1, n2) })
    }

    /// `lean_sharecommon_eq`.
    ///
    /// # Safety
    ///
    /// The caller passes two borrowed objects.
    #[no_mangle]
    pub unsafe extern "C" fn lean_sharecommon_eq(o1: Obj, o2: Obj) -> u8 {
        // SAFETY: two borrowed objects.
        u8::from(unsafe { sharecommon_eq(o1, o2) })
    }

    /// `lean_sharecommon_hash`.
    ///
    /// # Safety
    ///
    /// The caller passes a borrowed object.
    #[no_mangle]
    pub unsafe extern "C" fn lean_sharecommon_hash(o: Obj) -> u64 {
        // SAFETY: a borrowed object.
        unsafe { sharecommon_hash(o) }
    }

    /// `lean_uint64_mix_hash`.
    #[no_mangle]
    pub extern "C" fn lean_uint64_mix_hash(a1: u64, a2: u64) -> u64 {
        mix_hash(a1, a2)
    }
}
