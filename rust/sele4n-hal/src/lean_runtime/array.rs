//! Arrays and scalar arrays.
//!
//! Ported from the array and byte-array sections of `src/runtime/object.cpp`.
//! `Array.mk` and `Array.toList` are `lean_array_mk` / `lean_array_to_list`,
//! which upstream forwards to two `@[export]`ed Lean definitions; they are
//! written here directly — the same list walk — so the runtime does not call
//! back into the program it is serving.

use super::{
    alloc_ctor, boxed, ctor_get, ctor_set, dec, inc, is_exclusive, is_scalar, object,
    set_st_header, unbox, ArrayObject, Obj, SArrayObject, ARRAY_BYTES, TAG_ARRAY, TAG_SCALAR_ARRAY,
};

/// The array record of `o`.
///
/// # Safety
///
/// `o` must be a live array object, not otherwise referenced for `'a`.
unsafe fn array<'a>(o: Obj) -> &'a mut ArrayObject {
    // SAFETY: `o` is a live array by this function's contract.
    unsafe { &mut *o.cast::<ArrayObject>() }
}

/// The scalar-array record of `o`.
///
/// # Safety
///
/// `o` must be a live scalar array object, not otherwise referenced for `'a`.
unsafe fn sarray<'a>(o: Obj) -> &'a mut SArrayObject {
    // SAFETY: `o` is a live scalar array by this function's contract.
    unsafe { &mut *o.cast::<SArrayObject>() }
}

fn elements_ptr(o: Obj) -> *mut Obj {
    o.cast::<u8>().wrapping_add(ARRAY_BYTES).cast()
}

fn sdata(o: Obj) -> *mut u8 {
    o.cast::<u8>()
        .wrapping_add(core::mem::size_of::<SArrayObject>())
}

/// `lean_alloc_array(size, capacity)`.
#[must_use]
pub fn alloc_array(size: usize, capacity: usize) -> Obj {
    let bytes = capacity
        .checked_mul(8)
        .and_then(|b| b.checked_add(ARRAY_BYTES))
        .unwrap_or_else(|| object::internal_panic_out_of_memory());
    let o = object::alloc_object(bytes);
    // SAFETY: `o` is a fresh array, referenced nowhere else.
    let a = unsafe {
        set_st_header(o, TAG_ARRAY, 0);
        array(o)
    };
    a.size = size;
    a.capacity = capacity;
    o
}

/// `lean_alloc_sarray(elem_size, size, capacity)`.
#[must_use]
pub fn alloc_sarray(elem_size: u8, size: usize, capacity: usize) -> Obj {
    let bytes = capacity
        .checked_mul(usize::from(elem_size))
        .and_then(|b| b.checked_add(core::mem::size_of::<SArrayObject>()))
        .unwrap_or_else(|| object::internal_panic_out_of_memory());
    let o = object::alloc_object(bytes);
    // SAFETY: `o` is a fresh allocation of the scalar array's size, referenced
    // nowhere else.
    let a = unsafe {
        set_st_header(o, TAG_SCALAR_ARRAY, elem_size);
        sarray(o)
    };
    a.size = size;
    a.capacity = capacity;
    o
}

/// A fresh `ByteArray` holding a copy of `bytes`, its one reference owned by the
/// caller.
///
/// WS-BP BP4.3: how the firmware's device tree reaches Lean — the kernel entry
/// takes a `ByteArray`, and the blob lives in memory the kernel neither owns
/// nor keeps, so the kernel's copy is on its own heap.
#[must_use]
pub fn byte_array_of(bytes: &[u8]) -> Obj {
    let o = alloc_sarray(1, bytes.len(), bytes.len());
    // SAFETY: `o` is the fresh scalar array just allocated with `bytes.len()`
    // one-byte elements, referenced nowhere else.
    unsafe { sarray_bytes_mut(o) }.copy_from_slice(bytes);
    o
}

/// The bytes of a scalar array's elements in use.
///
/// # Safety
///
/// `o` must be a live scalar array, outliving the slice.
#[must_use]
pub unsafe fn sarray_bytes<'a>(o: Obj) -> &'a [u8] {
    // SAFETY: `o` is a live scalar array by the caller's contract, which holds
    // `size` elements of `other` bytes each.
    unsafe {
        let a = sarray(o);
        core::slice::from_raw_parts(sdata(o), a.size * usize::from(a.header.other))
    }
}

/// Mutable [`sarray_bytes`].
///
/// # Safety
///
/// `o` must be a live scalar array this caller owns exclusively.
#[must_use]
pub unsafe fn sarray_bytes_mut<'a>(o: Obj) -> &'a mut [u8] {
    // SAFETY: as for `sarray_bytes`, and the caller owns `o` exclusively.
    unsafe {
        let a = sarray(o);
        core::slice::from_raw_parts_mut(sdata(o), a.size * usize::from(a.header.other))
    }
}

/// The elements of an array.
///
/// # Safety
///
/// `o` must be a live array, outliving the slice.
#[must_use]
pub unsafe fn elements<'a>(o: Obj) -> &'a [Obj] {
    // SAFETY: an array holds `size` elements.
    unsafe { core::slice::from_raw_parts(elements_ptr(o), array(o).size) }
}

/// `lean_array_mk(lst)`: the array of a list, consuming it.
///
/// # Safety
///
/// `lst` must be a live `List`; consumed.
pub unsafe fn array_mk(lst: Obj) -> Obj {
    let mut n = 0usize;
    let mut o = lst;
    while !is_scalar(o) {
        n += 1;
        // SAFETY: a list cell's second field is its tail.
        o = unsafe { ctor_get(o, 1) };
    }
    let r = alloc_array(n, n);
    let mut o = lst;
    for i in 0..n {
        // SAFETY: `o` is the `i`-th live cell; its head gains the array's
        // reference, the list's own released below.
        unsafe {
            let head = ctor_get(o, 0);
            inc(head);
            elements_ptr(r).add(i).write(head);
            o = ctor_get(o, 1);
        }
    }
    // SAFETY: forwarded from the caller.
    unsafe { dec(lst) };
    r
}

/// `lean_array_to_list(a)`: the list of an array's elements, consuming it.
///
/// # Safety
///
/// `a` must be a live array; consumed.
pub unsafe fn array_to_list(a: Obj) -> Obj {
    let mut r = boxed(0);
    // SAFETY: forwarded from the caller.
    let elems = unsafe { elements(a) };
    for &v in elems.iter().rev() {
        let cell = alloc_ctor(1, 2, 0);
        // SAFETY: `cell` has two fields; `v` is held by the live array.
        unsafe {
            inc(v);
            ctor_set(cell, 0, v);
            ctor_set(cell, 1, r);
        }
        r = cell;
    }
    // SAFETY: forwarded from the caller.
    unsafe { dec(a) };
    r
}

/// `lean_nat_to_size_t`: a size, consuming a big `Nat`.  A `Nat` beyond
/// `usize` is reported as out of memory, as upstream reports it.
///
/// # Safety
///
/// `n` must be a `Nat`; a big one's reference is consumed.
unsafe fn nat_to_size(n: Obj) -> usize {
    if is_scalar(n) {
        return unbox(n);
    }
    // SAFETY: forwarded from the caller.
    match unsafe { super::nat::nat_to_usize(n) } {
        Some(sz) => {
            // SAFETY: forwarded from the caller.
            unsafe { dec(n) };
            sz
        }
        None => object::internal_panic_out_of_memory(),
    }
}

/// `lean_mk_array(n, v)`: `n` copies of `v`, consuming both.
///
/// # Safety
///
/// `n` must be a `Nat` and `v` a live object or scalar; both consumed.
pub unsafe fn mk_array(n: Obj, v: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    let sz = unsafe { nat_to_size(n) };
    let r = alloc_array(sz, sz);
    for i in 0..sz {
        // SAFETY: `r` holds `sz` elements.
        unsafe { elements_ptr(r).add(i).write(v) };
    }
    // SAFETY: `v` arrived with one reference and now has `sz`.
    unsafe {
        if sz == 0 {
            dec(v);
        } else {
            for _ in 1..sz {
                inc(v);
            }
        }
    }
    r
}

/// `lean_copy_expand_array(a, expand)`: a copy of `a`, with a larger capacity
/// when `expand`, consuming `a`.
///
/// # Safety
///
/// `a` must be a live array; consumed.
pub unsafe fn copy_expand_array(a: Obj, expand: bool) -> Obj {
    // SAFETY: forwarded from the caller.
    let (size, mut cap) = unsafe { (array(a).size, array(a).capacity) };
    if expand {
        cap = (cap + 1) * 2;
    }
    let r = alloc_array(size, cap);
    // SAFETY: both arrays are live; `r` has room for `size` elements.  An
    // exclusive `a` hands its references over; a shared one keeps its own.
    unsafe {
        core::ptr::copy_nonoverlapping(elements_ptr(a), elements_ptr(r), size);
        if is_exclusive(a) {
            object::free_object(a);
        } else {
            for &v in elements(r) {
                inc(v);
            }
            dec(a);
        }
    }
    r
}

/// `lean_array_push(a, v)`, consuming both.
///
/// # Safety
///
/// `a` must be a live array and `v` a live object or scalar; both consumed.
pub unsafe fn array_push(a: Obj, v: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    let (size, cap) = unsafe { (array(a).size, array(a).capacity) };
    // SAFETY: forwarded from the caller.
    let r = unsafe {
        if is_exclusive(a) {
            if cap > size {
                a
            } else {
                copy_expand_array(a, true)
            }
        } else {
            copy_expand_array(a, cap < 2 * size + 1)
        }
    };
    // SAFETY: `r` is a live, exclusive array with capacity above its size.
    unsafe {
        let ra = array(r);
        elements_ptr(r).add(ra.size).write(v);
        ra.size += 1;
    }
    r
}

/// `lean_array_get_panic(def)`: the out-of-bounds report for `a[i]!`.
///
/// # Safety
///
/// `def` must be an owned object or scalar.
pub unsafe fn array_get_panic(def: Obj) -> Obj {
    let msg = super::string::from_bytes_unchecked(b"Error: index out of bounds", 26);
    // SAFETY: `msg` is a fresh string.
    unsafe { object::panic_fn(def, msg) }
}

/// `lean_copy_sarray(a, cap)`: a copy with capacity `cap`, consuming `a`.
///
/// # Safety
///
/// `a` must be a live scalar array with `cap` at least its size; consumed.
unsafe fn copy_sarray(a: Obj, cap: usize) -> Obj {
    // SAFETY: forwarded from the caller.
    let (elem, size) = unsafe {
        let s = sarray(a);
        (s.header.other, s.size)
    };
    let r = alloc_sarray(elem, size, cap);
    // SAFETY: both live; `r` holds as many elements as `a` uses.
    unsafe {
        sarray_bytes_mut(r).copy_from_slice(sarray_bytes(a));
        dec(a);
    }
    r
}

/// `lean_byte_array_data(a)`: the bytes as an `Array UInt8`, consuming `a`.
///
/// # Safety
///
/// `a` must be a live byte array; consumed.
pub unsafe fn byte_array_data(a: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    let b = unsafe { sarray_bytes(a) };
    let r = alloc_array(b.len(), b.len());
    for (i, &x) in b.iter().enumerate() {
        // SAFETY: `r` holds `b.len()` elements.
        unsafe { elements_ptr(r).add(i).write(boxed(usize::from(x))) };
    }
    // SAFETY: forwarded from the caller.
    unsafe { dec(a) };
    r
}

/// `lean_float_array_data(a)`: the doubles as an `Array Float`, each boxed as
/// its bits, consuming `a`.  No floating-point arithmetic is performed.
///
/// # Safety
///
/// `a` must be a live float array; consumed.
pub unsafe fn float_array_data(a: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    let b = unsafe { sarray_bytes(a) };
    let n = b.len() / 8;
    let r = alloc_array(n, n);
    for (i, chunk) in b.chunks_exact(8).enumerate() {
        let boxed_float = alloc_ctor(0, 0, 8);
        // SAFETY: `boxed_float` holds eight scalar bytes; `r` holds `n` elements.
        unsafe {
            core::ptr::copy_nonoverlapping(
                chunk.as_ptr(),
                boxed_float.cast::<u8>().add(super::HEADER_BYTES),
                8,
            );
            elements_ptr(r).add(i).write(boxed_float);
        }
    }
    // SAFETY: forwarded from the caller.
    unsafe { dec(a) };
    r
}

/// `lean_byte_array_copy_slice(src, src_off, dest, dest_off, len, exact)`:
/// copies up to `len` bytes of `src` from `src_off` into `dest` at `dest_off`
/// (clamped to `dest`'s size), growing `dest` as needed.
///
/// # Safety
///
/// `src` a live byte array (borrowed), `dest` a live byte array (consumed),
/// the offsets and length `Nat`s (consumed).
pub unsafe fn byte_array_copy_slice(
    src: Obj,
    src_off: Obj,
    dest: Obj,
    dest_off: Obj,
    len: Obj,
    exact: bool,
) -> Obj {
    // SAFETY: forwarded from the caller.
    let (ssz, dsz) = unsafe { (sarray_bytes(src).len(), sarray_bytes(dest).len()) };
    // SAFETY: forwarded from the caller.
    let src_off = unsafe { nat_to_size(src_off) };
    if src_off > ssz {
        return dest;
    }
    // SAFETY: forwarded from the caller.
    let n = unsafe { nat_to_size(len) }.min(ssz - src_off);
    // SAFETY: forwarded from the caller.
    let dest_off = unsafe { nat_to_size(dest_off) }.min(dsz);
    let new_dsz = dsz.max(dest_off + n);
    // SAFETY: forwarded from the caller.
    let cap = unsafe { sarray(dest).capacity };
    // SAFETY: forwarded from the caller; each step keeps `r` a live byte array.
    unsafe {
        let mut r = if new_dsz <= cap {
            dest
        } else {
            copy_sarray(dest, if exact { new_dsz } else { new_dsz * 2 })
        };
        if !is_exclusive(r) {
            r = copy_sarray(r, sarray(r).capacity);
        }
        sarray(r).size = new_dsz;
        let from = sarray_bytes(src).as_ptr().add(src_off);
        core::ptr::copy_nonoverlapping(from, sdata(r).add(dest_off), n);
        r
    }
}

/// `lean_byte_array_hash(a)`.
///
/// # Safety
///
/// `a` must be a live byte array, borrowed.
#[must_use]
pub unsafe fn byte_array_hash(a: Obj) -> u64 {
    // SAFETY: forwarded from the caller.
    object::hash_bytes(unsafe { sarray_bytes(a) }, 11)
}

#[cfg(feature = "hw_target")]
mod exports {
    use super::*;

    /// `lean_array_mk`.
    #[no_mangle]
    pub extern "C" fn lean_array_mk(lst: Obj) -> Obj {
        // SAFETY: an owned list.
        unsafe { array_mk(lst) }
    }

    /// `lean_array_to_list`.
    #[no_mangle]
    pub extern "C" fn lean_array_to_list(a: Obj) -> Obj {
        // SAFETY: an owned array.
        unsafe { array_to_list(a) }
    }

    /// `lean_mk_array`.
    #[no_mangle]
    pub extern "C" fn lean_mk_array(n: Obj, v: Obj) -> Obj {
        // SAFETY: an owned size and value.
        unsafe { mk_array(n, v) }
    }

    /// `lean_copy_expand_array`.
    #[no_mangle]
    pub extern "C" fn lean_copy_expand_array(a: Obj, expand: bool) -> Obj {
        // SAFETY: an owned array.
        unsafe { copy_expand_array(a, expand) }
    }

    /// `lean_copy_expand_array_nonlinear`: the out-of-line spelling `lean.h`
    /// uses on a shared array.
    #[no_mangle]
    pub extern "C" fn lean_copy_expand_array_nonlinear(a: Obj, expand: bool) -> Obj {
        // SAFETY: an owned array.
        unsafe { copy_expand_array(a, expand) }
    }

    /// `lean_array_push`.
    #[no_mangle]
    pub extern "C" fn lean_array_push(a: Obj, v: Obj) -> Obj {
        // SAFETY: an owned array and value.
        unsafe { array_push(a, v) }
    }

    /// `lean_array_get_panic`.
    #[no_mangle]
    pub extern "C" fn lean_array_get_panic(def: Obj) -> Obj {
        // SAFETY: an owned default.
        unsafe { array_get_panic(def) }
    }

    /// `lean_byte_array_data`.
    #[no_mangle]
    pub extern "C" fn lean_byte_array_data(a: Obj) -> Obj {
        // SAFETY: an owned byte array.
        unsafe { byte_array_data(a) }
    }

    /// `lean_float_array_data`.
    #[no_mangle]
    pub extern "C" fn lean_float_array_data(a: Obj) -> Obj {
        // SAFETY: an owned float array.
        unsafe { float_array_data(a) }
    }

    /// `lean_byte_array_copy_slice`.
    #[no_mangle]
    pub extern "C" fn lean_byte_array_copy_slice(
        src: Obj,
        src_off: Obj,
        dest: Obj,
        dest_off: Obj,
        len: Obj,
        exact: u8,
    ) -> Obj {
        // `exact` crosses as the generated C's `uint8_t`, so it is read as a
        // byte and compared rather than received as a Rust `bool`, whose
        // validity a caller's byte of `2` would break.
        // SAFETY: the Lean calling convention for this primitive.
        unsafe { byte_array_copy_slice(src, src_off, dest, dest_off, len, exact != 0) }
    }

    /// `lean_byte_array_hash`.
    #[no_mangle]
    pub extern "C" fn lean_byte_array_hash(a: Obj) -> u64 {
        // SAFETY: a borrowed byte array.
        unsafe { byte_array_hash(a) }
    }
}
