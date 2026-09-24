//! Strings: construction, UTF-8 navigation, comparison and hashing.
//!
//! Ported from the string section of `src/runtime/object.cpp` and from
//! `src/runtime/utf8.cpp`.  A string object holds its bytes followed by a zero
//! terminator: `size` counts the terminator, `length` the UTF-8 characters.
//! Positions are byte offsets, and every function answers for any position —
//! including one inside a character or past the end — exactly as upstream
//! does, because `String` is a structure over a byte array whose positions the
//! type system does not constrain.

use super::{
    array, dec, fatal, is_exclusive, is_scalar, object, set_st_header, unbox, Obj, StringObject,
    STRING_BYTES, TAG_STRING,
};

/// The string record of `o`.
///
/// # Safety
///
/// `o` must be a live string object, not otherwise referenced for `'a`.
unsafe fn string<'a>(o: Obj) -> &'a mut StringObject {
    // SAFETY: `o` is a live string by this function's contract.
    unsafe { &mut *o.cast::<StringObject>() }
}

fn data(o: Obj) -> *mut u8 {
    o.cast::<u8>().wrapping_add(STRING_BYTES)
}

/// The bytes of a string, without its terminator.
///
/// # Safety
///
/// `o` must be a live string object, which outlives the returned slice.
#[must_use]
pub unsafe fn bytes<'a>(o: Obj) -> &'a [u8] {
    // SAFETY: `o` is a live string by the caller's contract, holding `size`
    // bytes of data, the last its terminator.
    unsafe {
        let size = string(o).size;
        core::slice::from_raw_parts(data(o), size.saturating_sub(1))
    }
}

/// `lean_alloc_string(size, capacity, len)`.
#[must_use]
pub fn alloc_string(size: usize, capacity: usize, len: usize) -> Obj {
    let bytes = STRING_BYTES
        .checked_add(capacity)
        .unwrap_or_else(|| object::internal_panic_out_of_memory());
    let o = object::alloc_object(bytes);
    // SAFETY: `o` is a fresh allocation of a string with `capacity` bytes.
    unsafe {
        set_st_header(o, TAG_STRING, 0);
        let s = &mut *o.cast::<StringObject>();
        s.size = size;
        s.capacity = capacity;
        s.length = len;
    }
    o
}

/// A string holding `content`, which is `len` characters (`lean_mk_string_unchecked`).
#[must_use]
pub fn from_bytes_unchecked(content: &[u8], len: usize) -> Obj {
    let size = content.len() + 1;
    let o = alloc_string(size, size, len);
    // SAFETY: `o` has room for `size` bytes.
    unsafe {
        core::ptr::copy_nonoverlapping(content.as_ptr(), data(o), content.len());
        data(o).add(content.len()).write(0);
    }
    o
}

/// `get_utf8_size`: the length a leading byte announces; one for anything else.
fn utf8_size(c: u8) -> usize {
    match c {
        c if c & 0x80 == 0 => 1,
        c if c & 0xe0 == 0xc0 => 2,
        c if c & 0xf0 == 0xe0 => 3,
        c if c & 0xf8 == 0xf0 => 4,
        c if c & 0xfc == 0xf8 => 5,
        c if c & 0xfe == 0xfc => 6,
        _ => 1,
    }
}

/// `lean_utf8_n_strlen`: characters in `content` by the leading bytes alone.
#[must_use]
pub fn utf8_strlen(content: &[u8]) -> usize {
    let (mut i, mut n) = (0, 0);
    while i < content.len() {
        i += utf8_size(content[i]);
        n += 1;
    }
    n
}

/// `validate_utf8_one`: whether a well-formed scalar value starts at `pos`, and
/// where the next begins.
#[must_use]
pub fn validate_one(s: &[u8], pos: usize) -> Option<usize> {
    let c = u32::from(s[pos]);
    let cont = |k: usize| {
        s.get(pos + k)
            .map(|&b| u32::from(b))
            .filter(|b| b & 0xc0 == 0x80)
    };
    if c & 0x80 == 0 {
        Some(pos + 1)
    } else if c & 0xe0 == 0xc0 {
        let r = ((c & 0x1f) << 6) | (cont(1)? & 0x3f);
        (r >= 0x80).then_some(pos + 2)
    } else if c & 0xf0 == 0xe0 {
        let r = ((c & 0x0f) << 12) | ((cont(1)? & 0x3f) << 6) | (cont(2)? & 0x3f);
        (r >= 0x800 && !(0xD800..=0xDFFF).contains(&r)).then_some(pos + 3)
    } else if c & 0xf8 == 0xf0 {
        let r = ((c & 0x07) << 18)
            | ((cont(1)? & 0x3f) << 12)
            | ((cont(2)? & 0x3f) << 6)
            | (cont(3)? & 0x3f);
        (0x10000..=0x10FFFF).contains(&r).then_some(pos + 4)
    } else {
        None
    }
}

/// `push_unicode_scalar`: the UTF-8 encoding of `code` into `out`, returning
/// its length.  Upstream encodes whatever it is given; a `Char` is a scalar
/// value by construction, so nothing here narrows that.
pub fn encode(code: u32, out: &mut [u8; 4]) -> usize {
    if code < 0x80 {
        out[0] = code as u8;
        1
    } else if code < 0x800 {
        out[0] = ((code >> 6) & 0x1f) as u8 | 0xc0;
        out[1] = (code & 0x3f) as u8 | 0x80;
        2
    } else if code < 0x10000 {
        out[0] = ((code >> 12) & 0x0f) as u8 | 0xe0;
        out[1] = ((code >> 6) & 0x3f) as u8 | 0x80;
        out[2] = (code & 0x3f) as u8 | 0x80;
        3
    } else {
        out[0] = ((code >> 18) & 0x07) as u8 | 0xf0;
        out[1] = ((code >> 12) & 0x3f) as u8 | 0x80;
        out[2] = ((code >> 6) & 0x3f) as u8 | 0x80;
        out[3] = (code & 0x3f) as u8 | 0x80;
        4
    }
}

const REPLACEMENT: [u8; 3] = [0xef, 0xbf, 0xbd];

/// `lean_mk_string_from_bytes`: a string of `s`, each ill-formed sequence
/// replaced by U+FFFD as `lean_mk_string_lossy_recover` replaces it.
#[must_use]
pub fn from_bytes(s: &[u8]) -> Obj {
    // One pass sizes the result, the second writes it.
    let mut sized = 0usize;
    let mut chars = 0usize;
    walk_lossy(s, |piece| sized += piece.len(), &mut chars);
    let o = alloc_string(sized + 1, sized + 1, chars);
    let mut at = 0usize;
    let mut ignored = 0usize;
    walk_lossy(
        s,
        |piece| {
            // SAFETY: the first pass sized `o` for exactly these pieces.
            unsafe { core::ptr::copy_nonoverlapping(piece.as_ptr(), data(o).add(at), piece.len()) };
            at += piece.len();
        },
        &mut ignored,
    );
    // SAFETY: `o` has `sized + 1` bytes.
    unsafe { data(o).add(sized).write(0) };
    o
}

/// The pieces of `s` with replacement characters for ill-formed sequences.
fn walk_lossy(s: &[u8], mut emit: impl FnMut(&[u8]), chars: &mut usize) {
    let (mut pos, mut start) = (0usize, 0usize);
    while pos < s.len() {
        match validate_one(s, pos) {
            Some(next) => pos = next,
            None => {
                emit(&s[start..pos]);
                emit(&REPLACEMENT);
                pos += 1;
                while pos < s.len() && s[pos] & 0xc0 == 0x80 {
                    pos += 1;
                }
                start = pos;
            }
        }
        *chars += 1;
    }
    emit(&s[start..pos]);
}

/// `string_ensure_capacity`: an exclusive `o` with room for `extra` more bytes.
///
/// # Safety
///
/// `o` must be a live, exclusive string; its reference is consumed.
unsafe fn ensure_capacity(o: Obj, extra: usize) -> Obj {
    // SAFETY: `o` is a live string by this function's contract.
    let (size, cap, len) = unsafe { (string(o).size, string(o).capacity, string(o).length) };
    if size + extra <= cap {
        return o;
    }
    let r = alloc_string(size, cap + size + extra, len);
    // SAFETY: both are live strings, `r` with room for `size` bytes; `o` is
    // exclusive, so its memory is released without touching any reference.
    unsafe {
        core::ptr::copy_nonoverlapping(data(o), data(r), size);
        object::free_object(o);
    }
    r
}

/// `lean_string_push(s, c)`.
///
/// # Safety
///
/// `s` must be a live string; its reference is consumed.
pub unsafe fn push(s: Obj, c: u32) -> Obj {
    // SAFETY: forwarded from the caller.
    let (size, len) = unsafe { (string(s).size, string(s).length) };
    // SAFETY: forwarded from the caller.
    let r = if unsafe { is_exclusive(s) } {
        // SAFETY: `s` is live and exclusive; its reference is handed over.
        unsafe { ensure_capacity(s, 5) }
    } else {
        let r = alloc_string(size, (size + 5) * 2, len);
        // SAFETY: both live; `r` has room for the copied bytes.
        unsafe {
            core::ptr::copy_nonoverlapping(data(s), data(r), size - 1);
            dec(s);
        }
        r
    };
    let mut enc = [0u8; 4];
    let n = encode(c, &mut enc);
    // SAFETY: `r` has capacity for `size + 4` bytes after the reserve above.
    unsafe {
        core::ptr::copy_nonoverlapping(enc.as_ptr(), data(r).add(size - 1), n);
        data(r).add(size - 1 + n).write(0);
    }
    // SAFETY: `r` is a live string this function owns exclusively.
    let rs = unsafe { string(r) };
    rs.size = size + n;
    rs.length += 1;
    r
}

/// `lean_string_append(s1, s2)`.
///
/// # Safety
///
/// Both must be live strings; `s1`'s reference is consumed, `s2` is borrowed.
pub unsafe fn append(s1: Obj, s2: Obj) -> Obj {
    // SAFETY: forwarded from the caller; each record is read and released
    // before the next is formed, since `s1` and `s2` may be one object.
    let (sz1, len1) = unsafe { (string(s1).size, string(s1).length) };
    // SAFETY: as above.
    let (sz2, len2) = unsafe { (string(s2).size, string(s2).length) };
    let new_len = len1 + len2;
    let new_sz = sz1 + sz2 - 1;
    // SAFETY: forwarded from the caller.
    let r = if unsafe { is_exclusive(s1) } {
        if s1 == s2 {
            fatal("lean_string_append: an exclusive string appended to itself");
        }
        // SAFETY: `s1` is live and exclusive; its reference is handed over.
        unsafe { ensure_capacity(s1, sz2 - 1) }
    } else {
        let r = alloc_string(new_sz, new_sz * 2, new_len);
        // SAFETY: both live; `r` has room for the copied bytes.
        unsafe {
            core::ptr::copy_nonoverlapping(data(s1), data(r), sz1 - 1);
            dec(s1);
        }
        r
    };
    // SAFETY: `r` has capacity for `new_sz` bytes; `s2` is live and distinct
    // from `r` (an exclusive `s1` is not `s2`, and a fresh `r` is neither).
    unsafe {
        core::ptr::copy_nonoverlapping(data(s2), data(r).add(sz1 - 1), sz2 - 1);
        data(r).add(new_sz - 1).write(0);
    }
    // SAFETY: `r` is a live string this function owns exclusively.
    let rs = unsafe { string(r) };
    rs.size = new_sz;
    rs.length = new_len;
    r
}

/// `lean_string_eq_cold`: byte equality, after `lean.h` has compared sizes.
///
/// # Safety
///
/// Both must be live strings.
#[must_use]
pub unsafe fn eq_cold(s1: Obj, s2: Obj) -> bool {
    // SAFETY: forwarded from the caller.
    unsafe { bytes(s1) == bytes(s2) }
}

/// `lean_string_lt`: lexicographic on bytes.
///
/// # Safety
///
/// Both must be live strings.
#[must_use]
pub unsafe fn lt(s1: Obj, s2: Obj) -> bool {
    // SAFETY: forwarded from the caller.
    unsafe { bytes(s1) < bytes(s2) }
}

/// `lean_string_hash`.
///
/// # Safety
///
/// `s` must be a live string.
#[must_use]
pub unsafe fn hash(s: Obj) -> u64 {
    // SAFETY: forwarded from the caller.
    object::hash_bytes(unsafe { bytes(s) }, 11)
}

/// `lean_string_of_usize(n)`: the decimal numeral.
#[must_use]
pub fn of_usize(mut n: usize) -> Obj {
    let mut buf = [0u8; 20];
    let mut at = buf.len();
    loop {
        at -= 1;
        buf[at] = b'0' + (n % 10) as u8;
        n /= 10;
        if n == 0 {
            break;
        }
    }
    let digits = &buf[at..];
    from_bytes_unchecked(digits, digits.len())
}

/// `lean_string_mk(cs)`: the string of a `List Char`, consuming it.
///
/// # Safety
///
/// `cs` must be a live `List Char` (a scalar for the empty list); consumed.
pub unsafe fn mk(cs: Obj) -> Obj {
    let chars = || {
        let mut o = cs;
        core::iter::from_fn(move || {
            if is_scalar(o) {
                return None;
            }
            // SAFETY: a list cell has the head and the tail as its fields.
            let (head, tail) = unsafe { (super::ctor_get(o, 0), super::ctor_get(o, 1)) };
            o = tail;
            Some(unbox(head) as u32)
        })
    };
    let mut enc = [0u8; 4];
    let (size, len) = chars().fold((0usize, 0usize), |(s, l), c| {
        (s + encode(c, &mut enc), l + 1)
    });
    let r = alloc_string(size + 1, size + 1, len);
    let mut at = 0usize;
    for c in chars() {
        let n = encode(c, &mut enc);
        // SAFETY: `r` was sized from the same characters.
        unsafe { core::ptr::copy_nonoverlapping(enc.as_ptr(), data(r).add(at), n) };
        at += n;
    }
    // SAFETY: `r` has `size + 1` bytes; the list is released only after its
    // last character was read.
    unsafe {
        data(r).add(size).write(0);
        dec(cs);
    }
    r
}

/// `lean_string_to_utf8(s)`: the bytes as a `ByteArray`.
///
/// # Safety
///
/// `s` must be a live string, borrowed.
#[must_use]
pub unsafe fn to_utf8(s: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    let b = unsafe { bytes(s) };
    let r = array::alloc_sarray(1, b.len(), b.len());
    // SAFETY: `r` holds `b.len()` bytes.
    unsafe { array::sarray_bytes_mut(r).copy_from_slice(b) };
    r
}

/// `lean_string_memcmp(s1, s2, lstart, rstart, len)`: whether the two ranges
/// hold the same bytes.  The caller's proofs keep both ranges in bounds; a
/// range that is not is refused rather than read.
///
/// # Safety
///
/// Both must be live strings and the three numbers scalars.
#[must_use]
pub unsafe fn memcmp(s1: Obj, s2: Obj, lstart: Obj, rstart: Obj, len: Obj) -> bool {
    // SAFETY: forwarded from the caller.
    let (a, b) = unsafe { (bytes(s1), bytes(s2)) };
    let (l, r, n) = (unbox(lstart), unbox(rstart), unbox(len));
    match (a.get(l..l.saturating_add(n)), b.get(r..r.saturating_add(n))) {
        (Some(x), Some(y)) => x == y,
        _ => fatal("lean_string_memcmp: a range outside its string"),
    }
}

/// The bytes a `String.Slice` spans: its string's bytes from `start` to `stop`.
///
/// # Safety
///
/// `slice` must be a live slice whose string field is live.
unsafe fn slice_bytes<'a>(slice: Obj) -> &'a [u8] {
    // SAFETY: a slice's fields are its string and two scalar positions.
    let (s, start, stop) = unsafe {
        (
            super::ctor_get(slice, 0),
            unbox(super::ctor_get(slice, 1)),
            unbox(super::ctor_get(slice, 2)),
        )
    };
    // SAFETY: forwarded from the caller.
    let b = unsafe { bytes(s) };
    b.get(start..stop)
        .unwrap_or_else(|| fatal("String.Slice: a range outside its string"))
}

/// `lean_slice_hash`.
///
/// # Safety
///
/// `slice` must be a live `String.Slice`.
#[must_use]
pub unsafe fn slice_hash(slice: Obj) -> u64 {
    // SAFETY: forwarded from the caller.
    object::hash_bytes(unsafe { slice_bytes(slice) }, 11)
}

/// `lean_slice_dec_lt`.
///
/// # Safety
///
/// Both must be live `String.Slice`s.
#[must_use]
pub unsafe fn slice_lt(s1: Obj, s2: Obj) -> bool {
    // SAFETY: forwarded from the caller.
    unsafe { slice_bytes(s1) < slice_bytes(s2) }
}

/// `lean_char_default_value`.
const DEFAULT_CHAR: u32 = 'A' as u32;

/// `lean_string_utf8_get_core`: the scalar value starting at `i`, if one does.
fn decode_at(s: &[u8], i: usize) -> Option<u32> {
    let c = u32::from(s[i]);
    if c & 0x80 == 0 {
        return Some(c);
    }
    let at = |k: usize| s.get(i + k).map(|&b| u32::from(b));
    if c & 0xe0 == 0xc0 {
        if let Some(c1) = at(1) {
            let r = ((c & 0x1f) << 6) | (c1 & 0x3f);
            if r >= 0x80 {
                return Some(r);
            }
        }
    }
    if c & 0xf0 == 0xe0 {
        if let (Some(c1), Some(c2)) = (at(1), at(2)) {
            let r = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
            if r >= 0x800 && !(0xD800..=0xDFFF).contains(&r) {
                return Some(r);
            }
        }
    }
    if c & 0xf8 == 0xf0 {
        if let (Some(c1), Some(c2), Some(c3)) = (at(1), at(2), at(3)) {
            let r = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
            if (0x10000..=0x10FFFF).contains(&r) {
                return Some(r);
            }
        }
    }
    None
}

/// `lean_string_utf8_get(s, i)`: the character at byte `i`, `'A'` where none
/// starts.
///
/// # Safety
///
/// `s` must be a live string and `i` a `Nat`, both borrowed.
#[must_use]
pub unsafe fn utf8_get(s: Obj, i: Obj) -> u32 {
    if !is_scalar(i) {
        return DEFAULT_CHAR;
    }
    // SAFETY: forwarded from the caller.
    let b = unsafe { bytes(s) };
    let i = unbox(i);
    if i >= b.len() {
        return DEFAULT_CHAR;
    }
    decode_at(b, i).unwrap_or(DEFAULT_CHAR)
}

/// `lean_string_utf8_get_fast_cold(str, i, size, c)`: the multi-byte half of
/// `lean.h`'s inline `String.get`, entered with the leading byte `c` at `i`.
///
/// # Safety
///
/// `str` must point to `size` readable bytes with `i < size`.
#[must_use]
pub unsafe fn utf8_get_fast_cold(str: *const u8, i: usize, size: usize, c: u8) -> u32 {
    // SAFETY: forwarded from the caller.
    let b = unsafe { core::slice::from_raw_parts(str, size) };
    if b.get(i) != Some(&c) {
        fatal("lean_string_utf8_get_fast_cold: leading byte mismatch");
    }
    decode_at(b, i).unwrap_or(DEFAULT_CHAR)
}

/// `lean_string_utf8_next(s, i)`: the position after the character at `i`,
/// counting an ill-formed or out-of-range position as one byte.
///
/// # Safety
///
/// `s` must be a live string and `i` a `Nat`, both borrowed.
#[must_use]
pub unsafe fn utf8_next(s: Obj, i: Obj) -> Obj {
    if !is_scalar(i) {
        // SAFETY: `i` is a live big `Nat`, borrowed.
        return unsafe { super::nat::nat_big_add(i, super::boxed(1)) };
    }
    let i = unbox(i);
    // SAFETY: forwarded from the caller.
    let b = unsafe { bytes(s) };
    if i >= b.len() {
        return super::nat::big_u64_to_nat(i as u64 + 1);
    }
    super::boxed(i + next_width(b[i]))
}

/// The byte width `String.next` gives a leading byte (`utf8_next`'s table).
fn next_width(c: u8) -> usize {
    match c {
        c if c & 0x80 == 0 => 1,
        c if c & 0xe0 == 0xc0 => 2,
        c if c & 0xf0 == 0xe0 => 3,
        c if c & 0xf8 == 0xf0 => 4,
        _ => 1,
    }
}

/// `lean_string_utf8_next_fast_cold(i, c)`.
#[must_use]
pub fn utf8_next_fast_cold(i: usize, c: u8) -> Obj {
    super::boxed(i + next_width(c))
}

fn is_first_byte(c: u8) -> bool {
    c & 0x80 == 0 || c & 0xe0 == 0xc0 || c & 0xf0 == 0xe0 || c & 0xf8 == 0xf0
}

/// `lean_string_is_valid_pos(s, i)`.
///
/// # Safety
///
/// `s` must be a live string and `i` a `Nat`, both borrowed.
#[must_use]
pub unsafe fn is_valid_pos(s: Obj, i: Obj) -> bool {
    if !is_scalar(i) {
        return false;
    }
    // SAFETY: forwarded from the caller.
    let b = unsafe { bytes(s) };
    let i = unbox(i);
    i == b.len() || b.get(i).is_some_and(|&c| is_first_byte(c))
}

/// `lean_string_utf8_extract(s, b, e)`: the bytes from `b` to `e`, with
/// upstream's clamping — empty unless `b` starts a character, and `e` moved to
/// the end when it does not start one.
///
/// Where a position is too big to be a scalar upstream returns `s` itself
/// **without** a new reference, although `s` is borrowed and the result owned —
/// an unreachable reference-count error (no string has 2^63 bytes).  This
/// returns `s` with a new reference, which is the result the contract asks for.
///
/// # Safety
///
/// `s` must be a live string and both positions `Nat`s, all borrowed.
#[must_use]
pub unsafe fn utf8_extract(s: Obj, b0: Obj, e0: Obj) -> Obj {
    if !is_scalar(b0) || !is_scalar(e0) {
        // SAFETY: `s` is live and borrowed; the result is a new reference.
        unsafe { super::inc(s) };
        return s;
    }
    // SAFETY: forwarded from the caller.
    let bs = unsafe { bytes(s) };
    let (b, mut e) = (unbox(b0), unbox(e0));
    let sz = bs.len();
    if b >= e || b >= sz || !is_first_byte(bs[b]) {
        return from_bytes_unchecked(&[], 0);
    }
    e = e.min(sz);
    if e < sz && !is_first_byte(bs[e]) {
        e = sz;
    }
    let piece = &bs[b..e];
    from_bytes_unchecked(piece, utf8_strlen(piece))
}

/// `lean_string_utf8_set(s, i, c)`: `s` with the character at `i` replaced.
///
/// # Safety
///
/// `s` must be a live string whose reference is consumed; `i` a borrowed `Nat`.
pub unsafe fn utf8_set(s: Obj, i: Obj, c: u32) -> Obj {
    if !is_scalar(i) {
        return s;
    }
    let i = unbox(i);
    // SAFETY: forwarded from the caller.
    let bs = unsafe { bytes(s) };
    if i >= bs.len() {
        return s;
    }
    // SAFETY: forwarded from the caller.
    if unsafe { is_exclusive(s) } && bs[i] < 0x80 && c < 0x80 {
        // SAFETY: `s` is exclusive and `i` is inside it.
        unsafe { data(s).add(i).write(c as u8) };
        return s;
    }
    if !is_first_byte(bs[i]) {
        return s;
    }
    let old = next_width(bs[i]).min(bs.len() - i);
    let mut enc = [0u8; 4];
    let n = encode(c, &mut enc);
    let new_sz = bs.len() - old + n;
    // SAFETY: forwarded from the caller.
    let len = unsafe { string(s).length };
    let r = alloc_string(new_sz + 1, new_sz + 1, len);
    // SAFETY: `r` has `new_sz + 1` bytes; `s` stays live until after the copy.
    unsafe {
        let d = data(r);
        core::ptr::copy_nonoverlapping(bs.as_ptr(), d, i);
        core::ptr::copy_nonoverlapping(enc.as_ptr(), d.add(i), n);
        core::ptr::copy_nonoverlapping(bs.as_ptr().add(i + old), d.add(i + n), bs.len() - i - old);
        d.add(new_sz).write(0);
        dec(s);
    }
    r
}

// ==========================================================================
// The exported names
// ==========================================================================

#[cfg(feature = "hw_target")]
mod exports {
    use super::*;

    /// `lean_mk_string_unchecked`.
    ///
    /// # Safety
    ///
    /// `s` must point to `sz` readable bytes of well-formed UTF-8.
    #[no_mangle]
    pub unsafe extern "C" fn lean_mk_string_unchecked(s: *const u8, sz: usize, len: usize) -> Obj {
        // SAFETY: forwarded from the caller.
        from_bytes_unchecked(unsafe { core::slice::from_raw_parts(s, sz) }, len)
    }

    /// `lean_mk_string_from_bytes`.
    ///
    /// # Safety
    ///
    /// `s` must point to `sz` readable bytes.
    #[no_mangle]
    pub unsafe extern "C" fn lean_mk_string_from_bytes(s: *const u8, sz: usize) -> Obj {
        // SAFETY: forwarded from the caller.
        from_bytes(unsafe { core::slice::from_raw_parts(s, sz) })
    }

    /// `lean_mk_string_from_bytes_unchecked`.
    ///
    /// # Safety
    ///
    /// `s` must point to `sz` readable bytes of well-formed UTF-8.
    #[no_mangle]
    pub unsafe extern "C" fn lean_mk_string_from_bytes_unchecked(s: *const u8, sz: usize) -> Obj {
        // SAFETY: forwarded from the caller.
        let b = unsafe { core::slice::from_raw_parts(s, sz) };
        from_bytes_unchecked(b, utf8_strlen(b))
    }

    /// `lean_mk_string`.
    ///
    /// # Safety
    ///
    /// `s` must point to a zero-terminated string.
    #[no_mangle]
    pub unsafe extern "C" fn lean_mk_string(s: *const u8) -> Obj {
        // SAFETY: forwarded from the caller.
        from_bytes(unsafe { core::ffi::CStr::from_ptr(s.cast()) }.to_bytes())
    }

    /// `lean_mk_ascii_string_unchecked`.
    ///
    /// # Safety
    ///
    /// `s` must point to a zero-terminated ASCII string.
    #[no_mangle]
    pub unsafe extern "C" fn lean_mk_ascii_string_unchecked(s: *const u8) -> Obj {
        // SAFETY: forwarded from the caller.
        let b = unsafe { core::ffi::CStr::from_ptr(s.cast()) }.to_bytes();
        from_bytes_unchecked(b, b.len())
    }

    /// `lean_string_push`.
    #[no_mangle]
    pub extern "C" fn lean_string_push(s: Obj, c: u32) -> Obj {
        // SAFETY: an owned string.
        unsafe { push(s, c) }
    }

    /// `lean_string_append`.
    #[no_mangle]
    pub extern "C" fn lean_string_append(s1: Obj, s2: Obj) -> Obj {
        // SAFETY: an owned and a borrowed string.
        unsafe { append(s1, s2) }
    }

    /// `lean_string_eq_cold`.
    #[no_mangle]
    pub extern "C" fn lean_string_eq_cold(s1: Obj, s2: Obj) -> bool {
        // SAFETY: two borrowed strings.
        unsafe { eq_cold(s1, s2) }
    }

    /// `lean_string_lt`.
    #[no_mangle]
    pub extern "C" fn lean_string_lt(s1: Obj, s2: Obj) -> bool {
        // SAFETY: two borrowed strings.
        unsafe { lt(s1, s2) }
    }

    /// `lean_string_hash`.
    #[no_mangle]
    pub extern "C" fn lean_string_hash(s: Obj) -> u64 {
        // SAFETY: a borrowed string.
        unsafe { hash(s) }
    }

    /// `lean_string_of_usize`.
    #[no_mangle]
    pub extern "C" fn lean_string_of_usize(n: usize) -> Obj {
        of_usize(n)
    }

    /// `lean_string_mk`.
    #[no_mangle]
    pub extern "C" fn lean_string_mk(cs: Obj) -> Obj {
        // SAFETY: an owned `List Char`.
        unsafe { mk(cs) }
    }

    /// `lean_string_to_utf8`.
    #[no_mangle]
    pub extern "C" fn lean_string_to_utf8(s: Obj) -> Obj {
        // SAFETY: a borrowed string.
        unsafe { to_utf8(s) }
    }

    /// `lean_string_memcmp`.
    #[no_mangle]
    pub extern "C" fn lean_string_memcmp(s1: Obj, s2: Obj, l: Obj, r: Obj, n: Obj) -> bool {
        // SAFETY: borrowed strings and positions.
        unsafe { memcmp(s1, s2, l, r, n) }
    }

    /// `lean_slice_hash`.
    #[no_mangle]
    pub extern "C" fn lean_slice_hash(s: Obj) -> u64 {
        // SAFETY: a borrowed slice.
        unsafe { slice_hash(s) }
    }

    /// `lean_slice_dec_lt`.
    #[no_mangle]
    pub extern "C" fn lean_slice_dec_lt(s1: Obj, s2: Obj) -> bool {
        // SAFETY: two borrowed slices.
        unsafe { slice_lt(s1, s2) }
    }

    /// `lean_string_utf8_get`.
    #[no_mangle]
    pub extern "C" fn lean_string_utf8_get(s: Obj, i: Obj) -> u32 {
        // SAFETY: a borrowed string and position.
        unsafe { utf8_get(s, i) }
    }

    /// `lean_string_utf8_get_fast_cold`.
    ///
    /// # Safety
    ///
    /// `str` must point to `size` readable bytes with `i < size`.
    #[no_mangle]
    pub unsafe extern "C" fn lean_string_utf8_get_fast_cold(
        str: *const u8,
        i: usize,
        size: usize,
        c: u8,
    ) -> u32 {
        // SAFETY: forwarded from the caller.
        unsafe { utf8_get_fast_cold(str, i, size, c) }
    }

    /// `lean_string_utf8_next`.
    #[no_mangle]
    pub extern "C" fn lean_string_utf8_next(s: Obj, i: Obj) -> Obj {
        // SAFETY: a borrowed string and position.
        unsafe { utf8_next(s, i) }
    }

    /// `lean_string_utf8_next_fast_cold`.
    #[no_mangle]
    pub extern "C" fn lean_string_utf8_next_fast_cold(i: usize, c: u8) -> Obj {
        utf8_next_fast_cold(i, c)
    }

    /// `lean_string_is_valid_pos`.
    #[no_mangle]
    pub extern "C" fn lean_string_is_valid_pos(s: Obj, i: Obj) -> bool {
        // SAFETY: a borrowed string and position.
        unsafe { is_valid_pos(s, i) }
    }

    /// `lean_string_utf8_extract`.
    #[no_mangle]
    pub extern "C" fn lean_string_utf8_extract(s: Obj, b: Obj, e: Obj) -> Obj {
        // SAFETY: a borrowed string and positions.
        unsafe { utf8_extract(s, b, e) }
    }

    /// `lean_string_utf8_set`.
    #[no_mangle]
    pub extern "C" fn lean_string_utf8_set(s: Obj, i: Obj, c: u32) -> Obj {
        // SAFETY: an owned string and a borrowed position.
        unsafe { utf8_set(s, i, c) }
    }
}
