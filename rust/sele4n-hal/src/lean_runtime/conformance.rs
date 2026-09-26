//! The shared conformance fixture, recomputed with this runtime.
//!
//! `tests/fixtures/lean_runtime_conformance.expected` is produced by
//! `tests/LeanRuntimeConformanceSuite.lean` running on upstream's runtime, and
//! that suite checks the file is exactly what upstream computes.  Here every
//! line is recomputed with the kernel's runtime and compared.  The corpus
//! operands are rebuilt from their hexadecimal digits by a parser that shares
//! nothing with the arithmetic under test, and every result is also checked to
//! be canonical — boxed exactly when it fits — since two representations of one
//! value would break the comparisons that answer from the representation.
//!
//! Each mutating string operation runs twice, on an exclusive and on a shared
//! argument, because those are different code paths with one required answer;
//! and the whole run ends with the heap holding exactly what it held at the
//! start, so a leaked or doubly released reference fails the test.

extern crate std;

use super::{array, boxed, dec, inc, io, is_scalar, nat, object, string, unbox, Obj};
use core::cmp::Ordering;
use std::collections::HashMap;
use std::string::String;
use std::string::ToString;
use std::vec::Vec;

const FIXTURE: &str = include_str!("../../../../tests/fixtures/lean_runtime_conformance.expected");

/// Hexadecimal digits (`0x…`, `-0x…`) to sign and limbs.
fn parse_hex_number(s: &str) -> (bool, Vec<u64>) {
    let (neg, digits) = match s.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, s),
    };
    let digits = digits.strip_prefix("0x").expect("hex number");
    let mut limbs = Vec::new();
    let bytes = digits.as_bytes();
    let mut end = bytes.len();
    while end > 0 {
        let start = end.saturating_sub(16);
        let chunk = core::str::from_utf8(&bytes[start..end]).unwrap();
        limbs.push(u64::from_str_radix(chunk, 16).expect("hex digits"));
        end = start;
    }
    while limbs.last() == Some(&0) {
        limbs.pop();
    }
    (neg && !limbs.is_empty(), limbs)
}

fn parse_hex_bytes(s: &str) -> Vec<u8> {
    if s == "-" {
        return Vec::new();
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// A number result, compared with its expected hex and checked canonical.
///
/// # Safety
///
/// `o` must be an `Int` when `int` holds and a `Nat` otherwise, borrowed.
unsafe fn check_number(line: &str, o: Obj, expected: &str, int: bool) {
    let (neg, mag) = parse_hex_number(expected);
    // SAFETY: forwarded from the caller.
    let (got_neg, got_mag, boxed_now) = unsafe { nat::parts(o, int) };
    assert_eq!((got_neg, &got_mag), (neg, &mag), "value differs: {line}");
    let fits = if int {
        let v: i128 = match mag.as_slice() {
            [] => 0,
            [x] => i128::from(*x),
            _ => i128::MAX,
        };
        let v = if neg { -v } else { v };
        (i128::from(i32::MIN)..=i128::from(i32::MAX)).contains(&v)
    } else {
        mag.len() <= 1
            && mag
                .first()
                .is_none_or(|&x| x <= super::MAX_SMALL_NAT as u64)
    };
    assert_eq!(boxed_now, fits, "representation not canonical: {line}");
}

fn ordering_word(o: Ordering) -> &'static str {
    match o {
        Ordering::Less => "lt",
        Ordering::Equal => "eq",
        Ordering::Greater => "gt",
    }
}

/// The bytes of a string.
///
/// # Safety
///
/// `o` must be a live string, borrowed.
unsafe fn string_bytes(o: Obj) -> Vec<u8> {
    // SAFETY: `o` is a live string by this function's contract.
    unsafe { string::bytes(o) }.to_vec()
}

fn hex_bytes(b: &[u8]) -> String {
    if b.is_empty() {
        return String::from("-");
    }
    b.iter().map(|x| std::format!("{x:02x}")).collect()
}

/// A result string's character count, which `String.length` reads without
/// scanning, agrees with its bytes.
///
/// # Safety
///
/// `r` must be a live string, borrowed.
unsafe fn assert_length_consistent(line: &str, r: Obj) {
    // SAFETY: `r` is a live string by this function's contract.
    let len = unsafe { (*r.cast::<super::StringObject>()).length };
    // SAFETY: as above.
    let bytes = unsafe { string_bytes(r) };
    assert_eq!(len, string::utf8_strlen(&bytes), "length field: {line}");
}

/// A mutating string operation run on a fresh exclusive copy and on a shared
/// one; both must produce `expected`.
///
/// # Safety
///
/// `s` must be a live string, borrowed; `op` must consume a live string and
/// return an owned one.
unsafe fn both_paths(line: &str, s: Obj, expected: &str, op: impl Fn(Obj) -> Obj) {
    // SAFETY: `s` is a live string by this function's contract.
    let bytes = unsafe { string::bytes(s) }.to_vec();
    let fresh = string::from_bytes_unchecked(&bytes, string::utf8_strlen(&bytes));
    let r = op(fresh);
    // SAFETY: `r` is the operation's owned string result.
    unsafe {
        assert_eq!(
            hex_bytes(&string_bytes(r)),
            expected,
            "exclusive path: {line}"
        );
        assert_length_consistent(line, r);
    }
    // SAFETY: `r` is the operation's owned result.
    unsafe { dec(r) };
    // SAFETY: `s` is live; the extra reference makes it shared for the call,
    // which consumes it.
    unsafe { inc(s) };
    let r = op(s);
    // SAFETY: `r` is the operation's owned string result.
    unsafe {
        assert_eq!(hex_bytes(&string_bytes(r)), expected, "shared path: {line}");
        assert_length_consistent(line, r);
    }
    // SAFETY: as above.
    unsafe { dec(r) };
}

#[test]
fn every_fixture_line_is_what_upstream_computes() {
    let before = super::mem::live_allocations();
    let mut nats: HashMap<usize, Obj> = HashMap::new();
    let mut ints: HashMap<usize, Obj> = HashMap::new();
    let mut strs: HashMap<usize, Obj> = HashMap::new();
    let mut chars: HashMap<usize, u32> = HashMap::new();
    let mut bytes: HashMap<usize, Obj> = HashMap::new();
    let mut checked = 0usize;
    for line in FIXTURE.lines() {
        let f: Vec<&str> = line.split(' ').collect();
        let idx = |k: usize| f[k].parse::<usize>().unwrap();
        // SAFETY: over the whole match, every object handed to the runtime is a live
        // corpus operand or a fresh result, released once below.
        unsafe {
            match f[0] {
                "nat" => {
                    let (_, mag) = parse_hex_number(f[2]);
                    let o = nat::canonical(false, &mag, false);
                    check_number(line, o, f[2], false);
                    nats.insert(idx(1), o);
                }
                "int" => {
                    let (neg, mag) = parse_hex_number(f[2]);
                    let o = nat::canonical(neg, &mag, true);
                    check_number(line, o, f[2], true);
                    ints.insert(idx(1), o);
                }
                "str" => {
                    let b = parse_hex_bytes(f[2]);
                    strs.insert(
                        idx(1),
                        string::from_bytes_unchecked(&b, string::utf8_strlen(&b)),
                    );
                }
                "char" => {
                    chars.insert(idx(1), f[2].parse().unwrap());
                }
                "bytes" => {
                    let b = parse_hex_bytes(f[2]);
                    let o = array::alloc_sarray(1, b.len(), b.len());
                    array::sarray_bytes_mut(o).copy_from_slice(&b);
                    bytes.insert(idx(1), o);
                }
                op @ ("nat_add" | "nat_sub" | "nat_mul" | "nat_div" | "nat_mod" | "nat_land"
                | "nat_lor" | "nat_xor" | "nat_gcd") => {
                    let (a, b) = (nats[&idx(1)], nats[&idx(2)]);
                    let r = match op {
                        "nat_add" => nat::nat_big_add(a, b),
                        "nat_sub" => nat::nat_big_sub(a, b),
                        "nat_mul" => nat::nat_big_mul(a, b),
                        "nat_div" => nat::nat_big_div(a, b),
                        "nat_mod" => nat::nat_big_mod(a, b),
                        "nat_land" => nat::nat_big_land(a, b),
                        "nat_lor" => nat::nat_big_lor(a, b),
                        "nat_xor" => nat::nat_big_xor(a, b),
                        _ => nat::nat_gcd(a, b),
                    };
                    check_number(line, r, f[3], false);
                    dec(r);
                }
                "nat_cmp" => {
                    let o = nat::nat_big_cmp(nats[&idx(1)], nats[&idx(2)]);
                    assert_eq!(ordering_word(o), f[3], "{line}");
                }
                op @ ("nat_shiftl" | "nat_shiftr" | "nat_pow") => {
                    let (a, s) = (nats[&idx(1)], boxed(idx(2)));
                    let r = match op {
                        "nat_shiftl" => nat::nat_shiftl(a, s),
                        "nat_shiftr" => nat::nat_big_shiftr(a, s),
                        _ => nat::nat_pow(a, s),
                    };
                    check_number(line, r, f[3], false);
                    dec(r);
                }
                "nat_log2" => {
                    let r = nat::nat_log2(nats[&idx(1)]);
                    check_number(line, r, f[2], false);
                }
                "nat_low" => {
                    let a = nats[&idx(1)];
                    let low = if is_scalar(a) {
                        unbox(a) as u64
                    } else {
                        nat::nat_low_u64(a)
                    };
                    let want: Vec<u64> = f[2..].iter().map(|x| x.parse().unwrap()).collect();
                    let got = [
                        u64::from(low as u8),
                        u64::from(low as u16),
                        u64::from(low as u32),
                        low,
                        low as usize as u64,
                    ];
                    assert_eq!(got.as_slice(), want.as_slice(), "{line}");
                }
                "nat_decimal" => {
                    let c = std::ffi::CString::new(f[2]).unwrap();
                    let r = nat::cstr_to_nat(c.as_ptr().cast());
                    let (_, want, _) = nat::parts(nats[&idx(1)], false);
                    let (_, got, _) = nat::parts(r, false);
                    assert_eq!(got, want, "{line}");
                    dec(r);
                }
                op @ ("int_add" | "int_sub" | "int_mul" | "int_tdiv" | "int_tmod" | "int_ediv"
                | "int_emod") => {
                    let (a, b) = (ints[&idx(1)], ints[&idx(2)]);
                    let r = match op {
                        "int_add" => nat::int_big_add(a, b),
                        "int_sub" => nat::int_big_sub(a, b),
                        "int_mul" => nat::int_big_mul(a, b),
                        "int_tdiv" => nat::int_big_div(a, b),
                        "int_tmod" => nat::int_big_mod(a, b),
                        "int_ediv" => nat::int_big_ediv(a, b),
                        _ => nat::int_big_emod(a, b),
                    };
                    check_number(line, r, f[3], true);
                    dec(r);
                }
                "int_cmp" => {
                    let o = nat::int_big_cmp(ints[&idx(1)], ints[&idx(2)]);
                    assert_eq!(ordering_word(o), f[3], "{line}");
                }
                "int_neg" => {
                    let r = nat::int_big_neg(ints[&idx(1)]);
                    check_number(line, r, f[2], true);
                    dec(r);
                }
                "int_low" => {
                    let low = nat::int_low_u64(ints[&idx(1)]);
                    let want: Vec<i64> = f[2..].iter().map(|x| x.parse().unwrap()).collect();
                    let got = [
                        i64::from(low as i8),
                        i64::from(low as i16),
                        i64::from(low as i32),
                        low as i64,
                        low as isize as i64,
                    ];
                    assert_eq!(got.as_slice(), want.as_slice(), "{line}");
                }
                "int_to_nat" => {
                    // `lean.h` calls the runtime for a non-negative big `Int`
                    // only; the rest are inline.
                    let a = ints[&idx(1)];
                    if !is_scalar(a) && nat::int_big_nonneg(a) {
                        inc(a);
                        let r = nat::big_int_to_nat(a);
                        check_number(line, r, f[2], false);
                        dec(r);
                    }
                }
                "str_hash" => {
                    assert_eq!(string::hash(strs[&idx(1)]).to_string(), f[2], "{line}");
                }
                "str_length" => {
                    let s = &*strs[&idx(1)].cast::<super::StringObject>();
                    assert_eq!(s.length.to_string(), f[2], "{line}");
                }
                "str_get" => {
                    let c = string::utf8_get(strs[&idx(1)], boxed(idx(2)));
                    assert_eq!(c.to_string(), f[3], "{line}");
                }
                "str_next" => {
                    let r = string::utf8_next(strs[&idx(1)], boxed(idx(2)));
                    assert_eq!(unbox(r).to_string(), f[3], "{line}");
                }
                "str_valid" => {
                    let v = string::is_valid_pos(strs[&idx(1)], boxed(idx(2)));
                    assert_eq!(v.to_string(), f[3], "{line}");
                }
                "str_set" => {
                    let c = chars[&idx(3)];
                    let p = boxed(idx(2));
                    both_paths(line, strs[&idx(1)], f[4], |s| string::utf8_set(s, p, c));
                }
                "str_extract" => {
                    let r = string::utf8_extract(strs[&idx(1)], boxed(idx(2)), boxed(idx(3)));
                    assert_eq!(hex_bytes(&string_bytes(r)), f[4], "{line}");
                    let len = (*r.cast::<super::StringObject>()).length;
                    assert_eq!(len, string::utf8_strlen(&string_bytes(r)), "{line}");
                    dec(r);
                }
                "str_push" => {
                    let c = chars[&idx(2)];
                    both_paths(line, strs[&idx(1)], f[3], |s| string::push(s, c));
                }
                "str_append" => {
                    let t = strs[&idx(2)];
                    both_paths(line, strs[&idx(1)], f[3], |s| {
                        // An exclusive `s` appended to itself is refused; the
                        // shared call is Lean's `s ++ s`.
                        if s == t {
                            inc(t);
                            let r = string::append(s, t);
                            dec(t);
                            r
                        } else {
                            string::append(s, t)
                        }
                    });
                }
                "str_lt" => {
                    let v = string::lt(strs[&idx(1)], strs[&idx(2)]);
                    assert_eq!(v.to_string(), f[3], "{line}");
                }
                "bytes_hash" => {
                    assert_eq!(
                        array::byte_array_hash(bytes[&idx(1)]).to_string(),
                        f[2],
                        "{line}"
                    );
                }
                "mix_hash" => {
                    let (x, y): (u64, u64) = (f[1].parse().unwrap(), f[2].parse().unwrap());
                    assert_eq!(object::mix_hash(x, y).to_string(), f[3], "{line}");
                }
                "platform_nbits" => {
                    assert_eq!(unbox(io::platform_nbits()).to_string(), f[1], "{line}");
                }
                "io_error_unsupported_operation_ctor" => {
                    assert_eq!(
                        io::IO_ERROR_UNSUPPORTED_OPERATION.to_string(),
                        f[1],
                        "{line}"
                    );
                }
                other => panic!("fixture line kind the runtime tests do not know: {other}"),
            }
        }
        checked += 1;
    }
    assert!(
        checked > 9000,
        "the fixture was read whole ({checked} lines)"
    );
    for o in nats
        .values()
        .chain(ints.values())
        .chain(strs.values())
        .chain(bytes.values())
    {
        // SAFETY: each corpus operand holds one reference, released here.
        unsafe { dec(*o) };
    }
    assert_eq!(
        super::mem::live_allocations(),
        before,
        "the run leaked or double-freed"
    );
}
