//! Arbitrary-precision `Nat` and `Int`.
//!
//! A `Nat` at most `MAX_SMALL_NAT` and an `Int` inside `i32` are boxed
//! scalars; `lean.h` computes on those inline and calls here only when an
//! operand is big or a result may be.  A big number is an [`MpzObject`] in sign
//! and magnitude.  Two invariants make the representation canonical, and every
//! result below restores them: a big `Nat` exceeds `MAX_SMALL_NAT`, and a big
//! `Int` lies outside `i32` — so equal values have equal representations and
//! the comparisons below may answer from the representation alone, as upstream
//! does.  (A `Nat` object is also a valid `Int`: `lean_nat_to_int` returns a big
//! `Nat` unchanged, and one above `MAX_SMALL_NAT` is far outside `i32`.)
//!
//! Upstream computes with GMP; the semantics here are GMP's as upstream uses
//! them — truncating division for `Int.div`/`Int.mod`, the Euclidean pair
//! built on it for `Int.ediv`/`Int.emod`, two's-complement residues for the
//! fixed-width conversions — and the shared conformance fixture checks each
//! against the upstream runtime.
//!
//! The magnitude algorithms are in [`limbs`], over plain slices and free of
//! `unsafe`; this module is only their object-level glue.

use super::{
    box_int, boxed, dec, fatal, is_scalar, mem, object, scalar_to_int, set_st_header, tag, unbox,
    MpzObject, Obj, MAX_SMALL_INT, MAX_SMALL_NAT, MIN_SMALL_INT, MPZ_BYTES, TAG_MPZ,
};
use core::cmp::Ordering;

pub mod limbs;

#[cfg(test)]
extern crate std;

// ==========================================================================
// Views of operands
// ==========================================================================

/// An operand's value: sign and magnitude, the magnitude borrowed from a big
/// object or held in `store` for a scalar.
struct Val<'a> {
    neg: bool,
    mag: &'a [u64],
}

/// The sign and limbs of a big number.
///
/// # Safety
///
/// `o` must be a live number object, unchanged for `'a`.
pub(super) unsafe fn mpz_parts<'a>(o: Obj) -> (bool, &'a [u64]) {
    // SAFETY: `o` is a live number object by this function's contract, whose
    // `size` limbs follow its fixed part.
    unsafe {
        let m = &*o.cast::<MpzObject>();
        let base = o.cast::<u8>().add(MPZ_BYTES).cast::<u64>();
        (m.neg != 0, core::slice::from_raw_parts(base, m.size))
    }
}

/// Refuses a non-scalar operand that is not a number object.
///
/// # Safety
///
/// `o` must be a scalar or a live heap object.
unsafe fn check_mpz(o: Obj) {
    // SAFETY: `o` is a live heap object once it is not a scalar.
    if is_scalar(o) || unsafe { tag(o) } != TAG_MPZ {
        fatal("big number operand is not a number object");
    }
}

/// A `Nat` operand.
///
/// # Safety
///
/// `o` must be a `Nat`: a scalar, or a live number object unchanged while
/// the view is used.
unsafe fn nat_val(o: Obj, store: &mut [u64; 1]) -> Val<'_> {
    if is_scalar(o) {
        store[0] = unbox(o) as u64;
        let len = usize::from(store[0] != 0);
        Val {
            neg: false,
            mag: &store[..len],
        }
    } else {
        // SAFETY: `o` is a scalar or a live number object by this function's
        // contract, and not a scalar here.
        let (neg, mag) = unsafe {
            check_mpz(o);
            mpz_parts(o)
        };
        Val { neg, mag }
    }
}

/// An `Int` operand.
///
/// # Safety
///
/// `o` must be an `Int`: a scalar, or a live number object unchanged while
/// the view is used.
unsafe fn int_val(o: Obj, store: &mut [u64; 1]) -> Val<'_> {
    if is_scalar(o) {
        let v = i64::from(scalar_to_int(o));
        store[0] = v.unsigned_abs();
        let len = usize::from(v != 0);
        Val {
            neg: v < 0,
            mag: &store[..len],
        }
    } else {
        // SAFETY: `o` is a scalar or a live number object by this function's
        // contract, and not a scalar here.
        let (neg, mag) = unsafe {
            check_mpz(o);
            mpz_parts(o)
        };
        Val { neg, mag }
    }
}

// ==========================================================================
// Results
// ==========================================================================

/// A big-number object under construction: `cap` zeroed limbs.
struct Building {
    o: Obj,
    cap: usize,
}

impl Building {
    fn new(cap: usize) -> Self {
        let cap = cap.max(1);
        let bytes = cap
            .checked_mul(8)
            .and_then(|b| b.checked_add(MPZ_BYTES))
            .unwrap_or_else(|| object::internal_panic_out_of_memory());
        let o = object::alloc_object(bytes);
        // SAFETY: `o` is a fresh allocation of `bytes` bytes.
        unsafe {
            set_st_header(o, TAG_MPZ, 0);
            let m = &mut *o.cast::<MpzObject>();
            m.size = cap;
            m.neg = 0;
        }
        let mut b = Self { o, cap };
        b.limbs().fill(0);
        b
    }

    fn limbs(&mut self) -> &mut [u64] {
        // SAFETY: `o` holds `cap` limbs after its fixed part and this builder
        // is its only owner.
        unsafe {
            let base = self.o.cast::<u8>().add(MPZ_BYTES).cast::<u64>();
            core::slice::from_raw_parts_mut(base, self.cap)
        }
    }

    /// The object holding `neg` and the first `len` limbs, always big.
    fn object(mut self, neg: bool, len: usize) -> Obj {
        let len = limbs::normalized_len(&self.limbs()[..len]);
        if len == 0 {
            fatal("big number result is zero where one is required");
        }
        // SAFETY: this builder owns `o`.
        unsafe {
            let m = &mut *self.o.cast::<MpzObject>();
            m.size = len;
            m.neg = usize::from(neg);
        }
        self.o
    }

    /// The canonical `Nat` for the first `len` limbs: boxed when it fits.
    fn nat(mut self, len: usize) -> Obj {
        let len = limbs::normalized_len(&self.limbs()[..len]);
        let v = self.limbs().first().copied().unwrap_or(0);
        if len == 0 || (len == 1 && v <= MAX_SMALL_NAT as u64) {
            self.discard();
            return boxed(if len == 0 { 0 } else { v as usize });
        }
        self.object(false, len)
    }

    /// The canonical `Int` for `neg` and the first `len` limbs.
    fn int(mut self, neg: bool, len: usize) -> Obj {
        let len = limbs::normalized_len(&self.limbs()[..len]);
        if len == 0 {
            self.discard();
            return box_int(0);
        }
        let v = self.limbs()[0];
        if len == 1 {
            let fits = if neg {
                v <= MIN_SMALL_INT.unsigned_abs()
            } else {
                v <= MAX_SMALL_INT as u64
            };
            if fits {
                self.discard();
                let signed = if neg {
                    (v as i64).wrapping_neg()
                } else {
                    v as i64
                };
                return box_int(signed as i32);
            }
        }
        self.object(neg, len)
    }

    fn discard(self) {
        // SAFETY: the object was never handed out.
        unsafe { object::free_object(self.o) };
    }
}

/// Scratch limbs from the kernel heap, freed on drop.
pub(super) struct Scratch {
    addr: usize,
    len: usize,
}

impl Scratch {
    pub(super) fn new(len: usize) -> Self {
        let len = len.max(1);
        let addr = len
            .checked_mul(8)
            .and_then(mem::alloc)
            .unwrap_or_else(|| object::internal_panic_out_of_memory());
        let mut s = Self { addr, len };
        s.slice().fill(0);
        s
    }

    pub(super) fn slice(&mut self) -> &mut [u64] {
        // SAFETY: `addr` is a live allocation of `len` limbs this scratch owns.
        unsafe { core::slice::from_raw_parts_mut(self.addr as *mut u64, self.len) }
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        if !mem::free(self.addr) {
            fatal("big number scratch lost");
        }
    }
}

/// A `Nat` from a native value, boxed when it fits (`mpz_to_nat`).
fn nat_of_u128(v: u128) -> Obj {
    if v <= MAX_SMALL_NAT as u128 {
        return boxed(v as usize);
    }
    let mut b = Building::new(2);
    b.limbs()[0] = v as u64;
    b.limbs()[1] = (v >> 64) as u64;
    b.nat(2)
}

/// A big number from a native value, **never** boxed (upstream's `alloc_mpz`).
fn mpz_of_i128(v: i128) -> Obj {
    let m = v.unsigned_abs();
    let mut b = Building::new(2);
    b.limbs()[0] = m as u64;
    b.limbs()[1] = (m >> 64) as u64;
    b.object(v < 0, 2)
}

/// An `Int` from a native value (`mpz_to_int`).
fn int_of_i128(v: i128) -> Obj {
    if (i128::from(MIN_SMALL_INT)..=i128::from(MAX_SMALL_INT)).contains(&v) {
        return box_int(v as i32);
    }
    mpz_of_i128(v)
}

// ==========================================================================
// Signed arithmetic on magnitudes
// ==========================================================================

fn signed_cmp(a: &Val<'_>, b: &Val<'_>) -> Ordering {
    let a_neg = a.neg && !a.mag.is_empty();
    let b_neg = b.neg && !b.mag.is_empty();
    match (a_neg, b_neg) {
        (false, true) => Ordering::Greater,
        (true, false) => Ordering::Less,
        (false, false) => limbs::cmp(a.mag, b.mag),
        (true, true) => limbs::cmp(b.mag, a.mag),
    }
}

/// `a + b` (or `a - b` when `negate_b`) as an `Int`.
fn int_add(a: &Val<'_>, b: &Val<'_>, negate_b: bool) -> Obj {
    let b_neg = b.neg != negate_b;
    let mut r = Building::new(a.mag.len().max(b.mag.len()) + 1);
    if a.neg == b_neg {
        let n = limbs::add(a.mag, b.mag, r.limbs());
        return r.int(a.neg, n);
    }
    match limbs::cmp(a.mag, b.mag) {
        Ordering::Less => {
            let n = limbs::sub(b.mag, a.mag, r.limbs());
            r.int(b_neg, n)
        }
        _ => {
            let n = limbs::sub(a.mag, b.mag, r.limbs());
            r.int(a.neg, n)
        }
    }
}

fn int_mul(a: &Val<'_>, b: &Val<'_>) -> Obj {
    let mut r = Building::new(a.mag.len() + b.mag.len());
    let n = limbs::mul(a.mag, b.mag, r.limbs());
    r.int(a.neg != b.neg, n)
}

/// Truncating quotient and remainder magnitudes of nonzero `b`, into fresh
/// builders.  The quotient has one spare limb, for the Euclidean adjustment.
fn divrem_mags(a: &[u64], b: &[u64]) -> (Building, usize, Building, usize) {
    let mut q = Building::new(a.len().saturating_sub(b.len()) + 2);
    let mut r = Building::new(b.len());
    let (qn, rn) = limbs::divrem(a, b, q.limbs(), r.limbs());
    (q, qn, r, rn)
}

/// The division family on `Int`s, for a nonzero divisor.
#[derive(Clone, Copy)]
enum IntDiv {
    /// `Int.div`: truncating quotient (`mpz_tdiv_q`).
    TDiv,
    /// `Int.mod`: truncating remainder, sign of the dividend (`mpz_tdiv_r`).
    TMod,
    /// `Int.ediv`: Euclidean quotient (`mpz::ediv`).
    EDiv,
    /// `Int.emod`: Euclidean remainder, never negative (`mpz::emod`).
    EMod,
}

/// `a` divided by nonzero `b`.  `mpz::ediv` adjusts the truncating quotient
/// away from zero by one exactly when the truncating remainder is negative —
/// the dividend negative and the division inexact — and `mpz::emod` adds `|b|`
/// to that remainder, which is `|b|` minus the magnitude remainder.
fn int_div(a: &Val<'_>, b: &Val<'_>, op: IntDiv) -> Obj {
    if b.mag.is_empty() {
        fatal("Int division by a big zero");
    }
    let (mut q, qn, mut r, rn) = divrem_mags(a.mag, b.mag);
    let a_neg = a.neg && !a.mag.is_empty();
    let rn = limbs::normalized_len(&r.limbs()[..rn]);
    let inexact_negative = a_neg && rn != 0;
    let q_neg = a_neg != b.neg;
    match op {
        IntDiv::TDiv => {
            r.discard();
            q.int(q_neg, qn)
        }
        IntDiv::TMod => {
            q.discard();
            r.int(a_neg, rn)
        }
        IntDiv::EDiv => {
            r.discard();
            let n = if inexact_negative {
                limbs::increment(q.limbs(), qn)
            } else {
                qn
            };
            q.int(q_neg, n)
        }
        IntDiv::EMod => {
            q.discard();
            if inexact_negative {
                let mut e = Building::new(b.mag.len());
                let n = limbs::sub(b.mag, &r.limbs()[..rn], e.limbs());
                r.discard();
                e.int(false, n)
            } else {
                r.int(false, rn)
            }
        }
    }
}

// ==========================================================================
// Nat
// ==========================================================================

/// `lean_cstr_to_nat(s)`: a decimal literal the compiler emitted.
///
/// # Safety
///
/// `s` must point to a zero-terminated string.
pub unsafe fn cstr_to_nat(s: *const u8) -> Obj {
    // SAFETY: forwarded from the caller.
    let digits = unsafe { core::ffi::CStr::from_ptr(s.cast()) }.to_bytes();
    // Each 64-bit limb holds more than 19 decimal digits.
    let mut b = Building::new(digits.len() / 19 + 1);
    match limbs::parse_decimal(digits, b.limbs()) {
        Some(n) => b.nat(n),
        None => fatal("lean_cstr_to_nat: not a decimal literal"),
    }
}

/// `lean_big_usize_to_nat` / `lean_big_uint64_to_nat`.
#[must_use]
pub fn big_u64_to_nat(n: u64) -> Obj {
    nat_of_u128(u128::from(n))
}

/// `lean_nat_overflow_mul(a1, a2)`: the product of two small `Nat`s whose
/// inline multiplication overflowed.
#[must_use]
pub fn nat_overflow_mul(a1: usize, a2: usize) -> Obj {
    nat_of_u128(a1 as u128 * a2 as u128)
}

/// Runs `f` on the views of two borrowed `Nat` operands.
///
/// # Safety
///
/// Both arguments must be `Nat`s — scalars or live big numbers — and are
/// borrowed for the call.
unsafe fn with_nats(a1: Obj, a2: Obj, f: impl FnOnce(Val<'_>, Val<'_>) -> Obj) -> Obj {
    let (mut s1, mut s2) = ([0u64; 1], [0u64; 1]);
    // SAFETY: both are `Nat`s by this function's contract, borrowed for `f`.
    let (a, b) = unsafe { (nat_val(a1, &mut s1), nat_val(a2, &mut s2)) };
    f(a, b)
}

/// `lean_nat_big_add`.
///
/// # Safety
///
/// Both arguments must be `Nat`s — scalars or live big numbers — and are
/// borrowed.
pub unsafe fn nat_big_add(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe {
        with_nats(a1, a2, |a, b| {
            let mut r = Building::new(a.mag.len().max(b.mag.len()) + 1);
            let n = limbs::add(a.mag, b.mag, r.limbs());
            r.nat(n)
        })
    }
}

/// `lean_nat_big_sub`: truncated at zero.
///
/// # Safety
///
/// Both arguments must be `Nat`s — scalars or live big numbers — and are
/// borrowed.
pub unsafe fn nat_big_sub(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe {
        with_nats(a1, a2, |a, b| {
            if limbs::cmp(a.mag, b.mag) == Ordering::Less {
                return boxed(0);
            }
            let mut r = Building::new(a.mag.len());
            let n = limbs::sub(a.mag, b.mag, r.limbs());
            r.nat(n)
        })
    }
}

/// `lean_nat_big_mul`.
///
/// # Safety
///
/// Both arguments must be `Nat`s — scalars or live big numbers — and are
/// borrowed.
pub unsafe fn nat_big_mul(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe {
        with_nats(a1, a2, |a, b| {
            let mut r = Building::new(a.mag.len() + b.mag.len());
            let n = limbs::mul(a.mag, b.mag, r.limbs());
            r.nat(n)
        })
    }
}

/// `lean_nat_big_land`.
///
/// # Safety
///
/// Both arguments must be `Nat`s — scalars or live big numbers — and are
/// borrowed.
pub unsafe fn nat_big_land(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe {
        with_nats(a1, a2, |a, b| {
            let mut r = Building::new(a.mag.len().min(b.mag.len()));
            let n = limbs::bitwise(a.mag, b.mag, r.limbs(), |x, y| x & y);
            r.nat(n)
        })
    }
}

/// `lean_nat_big_lor`.
///
/// # Safety
///
/// Both arguments must be `Nat`s — scalars or live big numbers — and are
/// borrowed.
pub unsafe fn nat_big_lor(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe {
        with_nats(a1, a2, |a, b| {
            let mut r = Building::new(a.mag.len().max(b.mag.len()));
            let n = limbs::bitwise(a.mag, b.mag, r.limbs(), |x, y| x | y);
            r.nat(n)
        })
    }
}

/// `lean_nat_big_xor`.
///
/// # Safety
///
/// Both arguments must be `Nat`s — scalars or live big numbers — and are
/// borrowed.
pub unsafe fn nat_big_xor(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe {
        with_nats(a1, a2, |a, b| {
            let mut r = Building::new(a.mag.len().max(b.mag.len()));
            let n = limbs::bitwise(a.mag, b.mag, r.limbs(), |x, y| x ^ y);
            r.nat(n)
        })
    }
}

/// `lean_nat_gcd`.
///
/// # Safety
///
/// Both arguments must be `Nat`s — scalars or live big numbers — and are
/// borrowed.
pub unsafe fn nat_gcd(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe {
        with_nats(a1, a2, |a, b| {
            let mut r = Building::new(a.mag.len().max(b.mag.len()));
            let n = limbs::gcd(a.mag, b.mag, r.limbs());
            r.nat(n)
        })
    }
}

/// `lean_nat_big_div`: division by zero is zero; `a2` itself is returned then,
/// as upstream does (it is the scalar zero).
///
/// # Safety
///
/// Both arguments must be `Nat`s and are borrowed.
pub unsafe fn nat_big_div(a1: Obj, a2: Obj) -> Obj {
    if is_scalar(a2) && unbox(a2) == 0 {
        return a2;
    }
    let (mut s1, mut s2) = ([0u64; 1], [0u64; 1]);
    // SAFETY: forwarded from the caller.
    let (a, b) = unsafe { (nat_val(a1, &mut s1), nat_val(a2, &mut s2)) };
    let (q, qn, r, _) = divrem_mags(a.mag, b.mag);
    r.discard();
    q.nat(qn)
}

/// `lean_nat_big_div_exact`: the quotient of a division the caller knows to
/// be exact; computed as the ordinary quotient, which it then equals.
///
/// # Safety
///
/// As [`nat_big_div`], with a nonzero divisor.
pub unsafe fn nat_big_div_exact(a1: Obj, a2: Obj) -> Obj {
    if is_scalar(a2) && unbox(a2) == 0 {
        fatal("Nat.divExact by zero");
    }
    // SAFETY: forwarded from the caller.
    unsafe { nat_big_div(a1, a2) }
}

/// `lean_nat_big_mod`: `a mod 0 = a`, returned with a new reference.
///
/// # Safety
///
/// Both arguments must be `Nat`s and are borrowed.
pub unsafe fn nat_big_mod(a1: Obj, a2: Obj) -> Obj {
    if is_scalar(a2) && unbox(a2) == 0 {
        // SAFETY: `a1` is a live `Nat` borrowed from the caller.
        unsafe { super::inc(a1) };
        return a1;
    }
    let (mut s1, mut s2) = ([0u64; 1], [0u64; 1]);
    // SAFETY: forwarded from the caller.
    let (a, b) = unsafe { (nat_val(a1, &mut s1), nat_val(a2, &mut s2)) };
    let (q, _, r, rn) = divrem_mags(a.mag, b.mag);
    q.discard();
    r.nat(rn)
}

/// The three `Nat` comparisons.
///
/// # Safety
///
/// Both arguments must be `Nat`s and are borrowed.
pub unsafe fn nat_big_cmp(a1: Obj, a2: Obj) -> Ordering {
    let (mut s1, mut s2) = ([0u64; 1], [0u64; 1]);
    // SAFETY: forwarded from the caller.
    unsafe { limbs::cmp(nat_val(a1, &mut s1).mag, nat_val(a2, &mut s2).mag) }
}

/// `lean_nat_big_succ`.
///
/// # Safety
///
/// `a` must be a live big `Nat`, borrowed.
pub unsafe fn nat_big_succ(a: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe { nat_big_add(a, boxed(1)) }
}

/// Shift amounts and exponents above this are refused, as upstream refuses
/// anything that does not fit an `unsigned`.
const MAX_EXPONENT: usize = u32::MAX as usize;

/// `lean_nat_shiftl(a1, a2)`.
///
/// # Safety
///
/// Both arguments must be `Nat`s and are borrowed.
pub unsafe fn nat_shiftl(a1: Obj, a2: Obj) -> Obj {
    if is_scalar(a1) && unbox(a1) == 0 {
        return boxed(0);
    }
    if !is_scalar(a2) || unbox(a2) > MAX_EXPONENT {
        fatal("Nat.shiftl exponent is too big");
    }
    let s = unbox(a2);
    let mut s1 = [0u64; 1];
    // SAFETY: forwarded from the caller.
    let a = unsafe { nat_val(a1, &mut s1) };
    let mut r = Building::new(a.mag.len() + s / 64 + 1);
    let n = limbs::shl(a.mag, s, r.limbs());
    r.nat(n)
}

/// `lean_nat_big_shiftr(a1, a2)`.
///
/// # Safety
///
/// Both arguments must be `Nat`s and are borrowed.
pub unsafe fn nat_big_shiftr(a1: Obj, a2: Obj) -> Obj {
    if !is_scalar(a2) {
        return boxed(0);
    }
    let s = unbox(a2);
    let mut s1 = [0u64; 1];
    // SAFETY: forwarded from the caller.
    let a = unsafe { nat_val(a1, &mut s1) };
    if s > MAX_EXPONENT {
        if limbs::log2(a.mag) >= s {
            fatal("Nat.shiftr exponent is too big");
        }
        return boxed(0);
    }
    let mut r = Building::new(a.mag.len());
    let n = limbs::shr(a.mag, s, r.limbs());
    r.nat(n)
}

/// `lean_nat_pow(a1, a2)`.
///
/// # Safety
///
/// Both arguments must be `Nat`s and are borrowed.
pub unsafe fn nat_pow(a1: Obj, a2: Obj) -> Obj {
    if !is_scalar(a2) || unbox(a2) > MAX_EXPONENT {
        fatal("Nat.pow exponent is too big");
    }
    let e = unbox(a2);
    let mut s1 = [0u64; 1];
    // SAFETY: forwarded from the caller.
    let a = unsafe { nat_val(a1, &mut s1) };
    let bits = (limbs::log2(a.mag) + 1)
        .checked_mul(e)
        .unwrap_or_else(|| object::internal_panic_out_of_memory());
    let mut r = Building::new(bits / 64 + 1);
    let n = limbs::pow(a.mag, e, r.limbs());
    r.nat(n)
}

/// `lean_nat_log2(a)`: zero for zero.
///
/// # Safety
///
/// `a` must be a `Nat`, borrowed.
pub unsafe fn nat_log2(a: Obj) -> Obj {
    let mut s = [0u64; 1];
    // SAFETY: forwarded from the caller.
    unsafe { boxed(limbs::log2(nat_val(a, &mut s).mag)) }
}

/// The low 64 bits of a `Nat`'s value (`mpz::mod64`, `get_size_t`): the
/// `UIntN.ofNat` and `USize.ofNat` conversions truncate this further.
///
/// # Safety
///
/// `a` must be a live big `Nat`, borrowed.
pub unsafe fn nat_low_u64(a: Obj) -> u64 {
    let mut s = [0u64; 1];
    // SAFETY: forwarded from the caller.
    unsafe { nat_val(a, &mut s).mag.first().copied().unwrap_or(0) }
}

/// The canonical `Nat` (`neg == false`) or `Int` for a sign and magnitude —
/// the constructor the tests build operands with.
#[cfg(test)]
pub(super) fn canonical(neg: bool, mag: &[u64], int: bool) -> Obj {
    let mut b = Building::new(mag.len());
    b.limbs()[..mag.len()].copy_from_slice(mag);
    if int {
        b.int(neg, mag.len())
    } else {
        b.nat(mag.len())
    }
}

/// A number's sign and magnitude, and whether it is boxed.
///
/// # Safety
///
/// `o` must be an `Int` when `int` holds and a `Nat` otherwise, borrowed.
#[cfg(test)]
pub(super) unsafe fn parts(o: Obj, int: bool) -> (bool, std::vec::Vec<u64>, bool) {
    let mut s = [0u64; 1];
    // SAFETY: forwarded from the caller.
    let v = unsafe {
        if int {
            int_val(o, &mut s)
        } else {
            nat_val(o, &mut s)
        }
    };
    (v.neg && !v.mag.is_empty(), v.mag.to_vec(), is_scalar(o))
}

/// A big `Nat` that fits a `usize` (`mpz::is_size_t` / `get_size_t`), borrowed.
///
/// # Safety
///
/// `a` must be a live big `Nat`.
#[must_use]
pub unsafe fn nat_to_usize(a: Obj) -> Option<usize> {
    let mut s = [0u64; 1];
    // SAFETY: forwarded from the caller.
    match unsafe { nat_val(a, &mut s).mag } {
        [] => Some(0),
        [x] => Some(*x as usize),
        _ => None,
    }
}

// ==========================================================================
// Int
// ==========================================================================

/// `lean_big_int64_to_int(n)`.
#[must_use]
pub fn big_int64_to_int(n: i64) -> Obj {
    int_of_i128(i128::from(n))
}

/// `lean_big_size_t_to_int(n)`: always a big number, as upstream allocates
/// one unconditionally (`lean.h` calls it only above `MAX_SMALL_INT`).
#[must_use]
pub fn big_size_t_to_int(n: usize) -> Obj {
    mpz_of_i128(n as i128)
}

/// `lean_big_int_to_int(n)`: always a big number (only reached on a 32-bit
/// target, where `lean.h` does not box every `int`).
#[must_use]
pub fn big_int_to_int(n: i32) -> Obj {
    mpz_of_i128(i128::from(n))
}

/// `lean_big_int_to_nat(a)`: a non-negative big `Int` as a `Nat`, consuming
/// `a`.  `lean.h` asserts the sign before calling; a negative value is a
/// broken contract, and the kernel does not compute on it.
///
/// # Safety
///
/// `a` must be a live big `Int`; the reference is consumed.
pub unsafe fn big_int_to_nat(a: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe { check_mpz(a) };
    // SAFETY: forwarded from the caller.
    let (neg, mag) = unsafe { mpz_parts(a) };
    if neg {
        fatal("Int.toNat of a negative big number");
    }
    let mut r = Building::new(mag.len());
    r.limbs()[..mag.len()].copy_from_slice(mag);
    let n = mag.len();
    let out = r.nat(n);
    // SAFETY: forwarded from the caller.
    unsafe { dec(a) };
    out
}

/// `lean_int_big_neg(a)`.
///
/// # Safety
///
/// `a` must be an `Int`, borrowed.
pub unsafe fn int_big_neg(a: Obj) -> Obj {
    let mut s = [0u64; 1];
    // SAFETY: forwarded from the caller.
    let v = unsafe { int_val(a, &mut s) };
    let mut r = Building::new(v.mag.len());
    r.limbs()[..v.mag.len()].copy_from_slice(v.mag);
    r.int(!v.neg, v.mag.len())
}

/// Runs `f` on the views of two borrowed `Int` operands.
///
/// # Safety
///
/// Both arguments must be `Int`s — scalars or live big numbers — and are
/// borrowed for the call.
unsafe fn with_ints(a1: Obj, a2: Obj, f: impl FnOnce(Val<'_>, Val<'_>) -> Obj) -> Obj {
    let (mut s1, mut s2) = ([0u64; 1], [0u64; 1]);
    // SAFETY: both are `Int`s by this function's contract, borrowed for `f`.
    let (a, b) = unsafe { (int_val(a1, &mut s1), int_val(a2, &mut s2)) };
    f(a, b)
}

/// `lean_int_big_add`.
///
/// # Safety
///
/// Both arguments must be `Int`s — scalars or live big numbers — and are
/// borrowed.
pub unsafe fn int_big_add(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe { with_ints(a1, a2, |a, b| int_add(&a, &b, false)) }
}

/// `lean_int_big_sub`.
///
/// # Safety
///
/// Both arguments must be `Int`s — scalars or live big numbers — and are
/// borrowed.
pub unsafe fn int_big_sub(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe { with_ints(a1, a2, |a, b| int_add(&a, &b, true)) }
}

/// `lean_int_big_mul`.
///
/// # Safety
///
/// Both arguments must be `Int`s — scalars or live big numbers — and are
/// borrowed.
pub unsafe fn int_big_mul(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe { with_ints(a1, a2, |a, b| int_mul(&a, &b)) }
}

/// The `Int` division family: division by zero answers as upstream does —
/// `a2` itself for the quotients, `a1` with a new reference for the
/// remainders.
///
/// # Safety
///
/// Both arguments must be `Int`s and are borrowed.
unsafe fn int_big_divide(a1: Obj, a2: Obj, op: IntDiv) -> Obj {
    if is_scalar(a2) && scalar_to_int(a2) == 0 {
        return match op {
            IntDiv::TDiv | IntDiv::EDiv => a2,
            IntDiv::TMod | IntDiv::EMod => {
                // SAFETY: `a1` is a live `Int` borrowed from the caller.
                unsafe { super::inc(a1) };
                a1
            }
        };
    }
    let (mut s1, mut s2) = ([0u64; 1], [0u64; 1]);
    // SAFETY: forwarded from the caller.
    unsafe { int_div(&int_val(a1, &mut s1), &int_val(a2, &mut s2), op) }
}

/// `lean_int_big_div`.
///
/// # Safety
///
/// Both arguments must be `Int`s and are borrowed.
pub unsafe fn int_big_div(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe { int_big_divide(a1, a2, IntDiv::TDiv) }
}

/// `lean_int_big_mod`.
///
/// # Safety
///
/// Both arguments must be `Int`s and are borrowed.
pub unsafe fn int_big_mod(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe { int_big_divide(a1, a2, IntDiv::TMod) }
}

/// `lean_int_big_ediv`.
///
/// # Safety
///
/// Both arguments must be `Int`s and are borrowed.
pub unsafe fn int_big_ediv(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe { int_big_divide(a1, a2, IntDiv::EDiv) }
}

/// `lean_int_big_emod`.
///
/// # Safety
///
/// Both arguments must be `Int`s and are borrowed.
pub unsafe fn int_big_emod(a1: Obj, a2: Obj) -> Obj {
    // SAFETY: forwarded from the caller.
    unsafe { int_big_divide(a1, a2, IntDiv::EMod) }
}

/// `lean_int_big_div_exact`: the quotient of a division the caller knows to be
/// exact, and so the truncating quotient.
///
/// # Safety
///
/// Both arguments must be `Int`s, borrowed, the divisor nonzero.
pub unsafe fn int_big_div_exact(a1: Obj, a2: Obj) -> Obj {
    if is_scalar(a2) && scalar_to_int(a2) == 0 {
        fatal("Int.divExact by zero");
    }
    // SAFETY: forwarded from the caller.
    unsafe { int_big_divide(a1, a2, IntDiv::TDiv) }
}

/// The `Int` comparisons.
///
/// # Safety
///
/// Both arguments must be `Int`s and are borrowed.
pub unsafe fn int_big_cmp(a1: Obj, a2: Obj) -> Ordering {
    let (mut s1, mut s2) = ([0u64; 1], [0u64; 1]);
    // SAFETY: forwarded from the caller.
    unsafe { signed_cmp(&int_val(a1, &mut s1), &int_val(a2, &mut s2)) }
}

/// `lean_int_big_nonneg(a)`.
///
/// # Safety
///
/// `a` must be an `Int`, borrowed.
pub unsafe fn int_big_nonneg(a: Obj) -> bool {
    let mut s = [0u64; 1];
    // SAFETY: forwarded from the caller.
    let v = unsafe { int_val(a, &mut s) };
    !v.neg || v.mag.is_empty()
}

/// The low 64 bits of an `Int`'s two's-complement value (`mpz::mod64` over
/// `mpz_fdiv_r_2exp`): the `IntN.ofInt` and `ISize.ofInt` conversions truncate
/// this further.
///
/// # Safety
///
/// `a` must be an `Int`, borrowed.
pub unsafe fn int_low_u64(a: Obj) -> u64 {
    let mut s = [0u64; 1];
    // SAFETY: forwarded from the caller.
    let v = unsafe { int_val(a, &mut s) };
    let low = v.mag.first().copied().unwrap_or(0);
    if v.neg {
        low.wrapping_neg()
    } else {
        low
    }
}

// ==========================================================================
// The exported names
// ==========================================================================

#[cfg(feature = "hw_target")]
mod exports {
    use super::*;
    use core::cmp::Ordering;

    macro_rules! borrowed2 {
        ($($name:ident => $f:ident;)+) => {$(
            /// A two-argument `Nat`/`Int` export of `lean.h`'s, minted by `borrowed2`.
            ///
            /// # Safety
            ///
            /// Both arguments are `Nat`s or `Int`s — scalars or live big numbers — borrowed for the call, as `lean.h`'s inline fast paths pass them.
            #[no_mangle]
            pub unsafe extern "C" fn $name(a1: Obj, a2: Obj) -> Obj {
                // SAFETY: `lean.h`'s calling convention: both borrowed numbers.
                unsafe { $f(a1, a2) }
            }
        )+};
    }

    borrowed2! {
        lean_nat_big_add => nat_big_add;
        lean_nat_big_sub => nat_big_sub;
        lean_nat_big_mul => nat_big_mul;
        lean_nat_big_div => nat_big_div;
        lean_nat_big_div_exact => nat_big_div_exact;
        lean_nat_big_mod => nat_big_mod;
        lean_nat_big_land => nat_big_land;
        lean_nat_big_lor => nat_big_lor;
        lean_nat_big_xor => nat_big_xor;
        lean_nat_shiftl => nat_shiftl;
        lean_nat_big_shiftr => nat_big_shiftr;
        lean_nat_pow => nat_pow;
        lean_nat_gcd => nat_gcd;
        lean_int_big_add => int_big_add;
        lean_int_big_sub => int_big_sub;
        lean_int_big_mul => int_big_mul;
        lean_int_big_div => int_big_div;
        lean_int_big_mod => int_big_mod;
        lean_int_big_ediv => int_big_ediv;
        lean_int_big_emod => int_big_emod;
        lean_int_big_div_exact => int_big_div_exact;
    }

    macro_rules! compare {
        ($($name:ident => $cmp:ident, |$o:ident| $test:expr;)+) => {$(
            /// A `Nat`/`Int` comparison export of `lean.h`'s, minted by `compare`.
            ///
            /// # Safety
            ///
            /// Both arguments are `Nat`s or `Int`s — scalars or live big numbers — borrowed for the call, as `lean.h`'s inline fast paths pass them.
            #[no_mangle]
            pub unsafe extern "C" fn $name(a1: Obj, a2: Obj) -> bool {
                // SAFETY: `lean.h`'s calling convention: both borrowed numbers.
                let $o: Ordering = unsafe { $cmp(a1, a2) };
                $test
            }
        )+};
    }

    compare! {
        lean_nat_big_eq => nat_big_cmp, |o| o.is_eq();
        lean_nat_big_le => nat_big_cmp, |o| o.is_le();
        lean_nat_big_lt => nat_big_cmp, |o| o.is_lt();
        lean_int_big_eq => int_big_cmp, |o| o.is_eq();
        lean_int_big_le => int_big_cmp, |o| o.is_le();
        lean_int_big_lt => int_big_cmp, |o| o.is_lt();
    }

    /// `lean_nat_big_succ`.
    ///
    /// # Safety
    ///
    /// The caller passes a borrowed big `Nat`.
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_big_succ(a: Obj) -> Obj {
        // SAFETY: a borrowed big `Nat`.
        unsafe { nat_big_succ(a) }
    }

    /// `lean_nat_log2`.
    ///
    /// # Safety
    ///
    /// The caller passes a borrowed `Nat`.
    #[no_mangle]
    pub unsafe extern "C" fn lean_nat_log2(a: Obj) -> Obj {
        // SAFETY: a borrowed `Nat`.
        unsafe { nat_log2(a) }
    }

    /// `lean_nat_overflow_mul`.
    #[no_mangle]
    pub extern "C" fn lean_nat_overflow_mul(a1: usize, a2: usize) -> Obj {
        nat_overflow_mul(a1, a2)
    }

    /// `lean_cstr_to_nat`.
    ///
    /// # Safety
    ///
    /// `s` must be a zero-terminated decimal literal.
    #[no_mangle]
    pub unsafe extern "C" fn lean_cstr_to_nat(s: *const u8) -> Obj {
        // SAFETY: forwarded from the caller.
        unsafe { cstr_to_nat(s) }
    }

    /// `lean_big_usize_to_nat`.
    #[no_mangle]
    pub extern "C" fn lean_big_usize_to_nat(n: usize) -> Obj {
        big_u64_to_nat(n as u64)
    }

    /// `lean_big_uint64_to_nat`.
    #[no_mangle]
    pub extern "C" fn lean_big_uint64_to_nat(n: u64) -> Obj {
        big_u64_to_nat(n)
    }

    /// `lean_big_int64_to_int`.
    #[no_mangle]
    pub extern "C" fn lean_big_int64_to_int(n: i64) -> Obj {
        big_int64_to_int(n)
    }

    /// `lean_big_size_t_to_int`.
    #[no_mangle]
    pub extern "C" fn lean_big_size_t_to_int(n: usize) -> Obj {
        big_size_t_to_int(n)
    }

    /// `lean_big_int_to_int`.
    #[no_mangle]
    pub extern "C" fn lean_big_int_to_int(n: i32) -> Obj {
        big_int_to_int(n)
    }

    /// `lean_big_int_to_nat`.
    ///
    /// # Safety
    ///
    /// The caller passes an owned big `Int`.
    #[no_mangle]
    pub unsafe extern "C" fn lean_big_int_to_nat(a: Obj) -> Obj {
        // SAFETY: an owned big `Int`.
        unsafe { big_int_to_nat(a) }
    }

    /// `lean_int_big_neg`.
    ///
    /// # Safety
    ///
    /// The caller passes a borrowed `Int`.
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_neg(a: Obj) -> Obj {
        // SAFETY: a borrowed `Int`.
        unsafe { int_big_neg(a) }
    }

    /// `lean_int_big_nonneg`.
    ///
    /// # Safety
    ///
    /// The caller passes a borrowed `Int`.
    #[no_mangle]
    pub unsafe extern "C" fn lean_int_big_nonneg(a: Obj) -> bool {
        // SAFETY: a borrowed `Int`.
        unsafe { int_big_nonneg(a) }
    }

    macro_rules! narrow {
        ($($name:ident => $f:ident as $t:ty;)+) => {$(
            /// A narrowing export of `lean.h`'s, minted by `narrow`: the value's low bits.
            ///
            /// # Safety
            ///
            /// The argument is a borrowed number of the kind the underlying primitive reads (a `Nat` for the `Nat` exports, an `Int` for the `Int` ones): a scalar or a live big number.
            #[no_mangle]
            pub unsafe extern "C" fn $name(a: Obj) -> $t {
                // SAFETY: a borrowed number of the kind `$f` reads.
                unsafe { $f(a) as $t }
            }
        )+};
    }

    narrow! {
        lean_uint8_of_big_nat => nat_low_u64 as u8;
        lean_uint16_of_big_nat => nat_low_u64 as u16;
        lean_uint32_of_big_nat => nat_low_u64 as u32;
        lean_uint64_of_big_nat => nat_low_u64 as u64;
        lean_usize_of_big_nat => nat_low_u64 as usize;
        lean_int8_of_big_int => int_low_u64 as i8;
        lean_int16_of_big_int => int_low_u64 as i16;
        lean_int32_of_big_int => int_low_u64 as i32;
        lean_int64_of_big_int => int_low_u64 as i64;
        lean_isize_of_big_int => int_low_u64 as isize;
    }
}
