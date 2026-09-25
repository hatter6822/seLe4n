//! Witnesses for what the shared fixture cannot reach: object lifetimes,
//! closures, arrays, the lossy UTF-8 decoder, reference cells, names, the
//! limb algorithms on random operands, and every fail-closed path.  Each test
//! that allocates ends by checking the heap holds what it held at the start.

extern crate std;

use super::*;
use std::vec::Vec;

fn live() -> usize {
    mem::live_allocations()
}

/// A list of `n` boxed numbers, `[0, 1, …, n - 1]`.
fn list_of(n: usize) -> Obj {
    let mut l = boxed(0);
    for i in (0..n).rev() {
        let cell = alloc_ctor(1, 2, 0);
        // SAFETY: `cell` has two fields.
        unsafe {
            ctor_set(cell, 0, boxed(i));
            ctor_set(cell, 1, l);
        }
        l = cell;
    }
    l
}

/// The reference count of `o`.
///
/// # Safety
///
/// `o` must be a live heap object.
unsafe fn rc(o: Obj) -> i32 {
    // SAFETY: `o` is a live heap object by this function's contract.
    unsafe { header(o).rc }
}

#[test]
fn releasing_a_long_list_frees_every_cell_without_recursing() {
    let before = live();
    // Deep enough that a recursive release would exhaust a test thread's stack.
    let l = list_of(200_000);
    assert_eq!(live(), before + 200_000);
    // SAFETY: `l` is owned.
    unsafe { dec(l) };
    assert_eq!(live(), before);
}

#[test]
fn a_shared_child_survives_its_first_parent() {
    let before = live();
    let child = alloc_ctor(0, 0, 8);
    let p1 = alloc_ctor(0, 1, 0);
    let p2 = alloc_ctor(0, 1, 0);
    // SAFETY: fresh objects; the child gains one reference per parent.
    unsafe {
        inc(child);
        ctor_set(p1, 0, child);
        ctor_set(p2, 0, child);
        dec(p1);
        assert_eq!(rc(child), 1);
        dec(p2);
    }
    assert_eq!(live(), before);
}

#[test]
fn a_persistent_object_is_never_freed_and_marking_reaches_everything() {
    let before = live();
    let l = list_of(1000);
    let arr = array::alloc_array(2, 2);
    // SAFETY: `arr` has room for two elements; `l` is shared by both slots.
    unsafe {
        inc(l);
        (*array::elements(arr).as_ptr().cast_mut()) = l;
        *array::elements(arr).as_ptr().cast_mut().add(1) = l;
        object::mark_persistent(arr);
        assert_eq!(rc(arr), 0);
        let mut o = l;
        while !is_scalar(o) {
            assert_eq!(rc(o), 0, "every reachable cell is persistent");
            o = ctor_get(o, 1);
        }
        // Reference counting no longer touches them.
        dec(arr);
        inc(l);
        dec(l);
        dec(l);
    }
    assert_eq!(live(), before + 1001, "persistent objects stay allocated");
}

static FINALIZED: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);
extern "C" fn finalize(_data: *mut core::ffi::c_void) {
    FINALIZED.fetch_add(1, core::sync::atomic::Ordering::SeqCst);
}
extern "C" fn foreach(_data: *mut core::ffi::c_void, _f: Obj) {}
static CLASS: ExternalClass = ExternalClass { finalize, foreach };

#[test]
fn an_external_object_is_finalized_by_its_class() {
    let before = live();
    let o = object::alloc_object(core::mem::size_of::<ExternalObject>());
    // SAFETY: `o` is a fresh allocation of an external object's size.
    unsafe {
        set_st_header(o, TAG_EXTERNAL, 0);
        (*o.cast::<ExternalObject>()).class = &CLASS;
        (*o.cast::<ExternalObject>()).data = core::ptr::null_mut();
        let n = FINALIZED.load(core::sync::atomic::Ordering::SeqCst);
        dec(o);
        assert_eq!(FINALIZED.load(core::sync::atomic::Ordering::SeqCst), n + 1);
    }
    assert_eq!(live(), before);
}

#[test]
#[should_panic(expected = "multi-threaded")]
fn a_multi_threaded_object_is_refused() {
    let o = alloc_ctor(0, 0, 0);
    // SAFETY: `o` is live; the negative count is the state being refused.
    unsafe {
        header(o).rc = -1;
        object::dec_ref_cold(o);
    }
}

#[test]
#[should_panic(expected = "task, promise")]
fn a_task_object_is_refused() {
    let o = alloc_ctor(0, 0, 8);
    // SAFETY: `o` is live; the task tag is the state being refused.
    unsafe {
        header(o).tag = TAG_TASK;
        object::dec_ref_cold(o);
    }
}

// --------------------------------------------------------------------------
// Closures
// --------------------------------------------------------------------------

/// Sums its boxed arguments, consuming them (they are scalars).
macro_rules! summing {
    ($name:ident($($a:ident),+)) => {
        extern "C" fn $name($($a: Obj),+) -> Obj {
            boxed(0 $(+ unbox($a))+)
        }
    };
}
summing!(sum1(a));
summing!(sum2(a, b));
summing!(sum3(a, b, c));
summing!(sum5(a, b, c, d, e));
summing!(sum16(a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p));

extern "C" fn sum20(args: *mut Obj) -> Obj {
    // SAFETY: the runtime passes an array of the function's twenty arguments.
    let a = unsafe { core::slice::from_raw_parts(args, 20) };
    boxed(a.iter().map(|&x| unbox(x)).sum())
}

/// Returns a closure that adds its argument to `k` (over-application target).
extern "C" fn adder(k: Obj) -> Obj {
    let c = apply::alloc_closure(sum2 as *const (), 2, 1);
    // SAFETY: `c` has one fixed field.
    unsafe { *c.cast::<u8>().add(CLOSURE_BYTES).cast::<Obj>() = k };
    c
}

/// Applies `f` to scalar arguments, returning the scalar result.
///
/// # Safety
///
/// `f` must be an owned closure over scalars returning a scalar; consumed.
unsafe fn call(f: Obj, args: &[usize]) -> usize {
    let a: Vec<Obj> = args.iter().map(|&x| boxed(x)).collect();
    // SAFETY: `f` is an owned closure by this function's contract; the
    // arguments are scalars.
    unbox(unsafe { apply::apply(f, &a) })
}

#[test]
fn exact_under_and_over_application_agree_at_every_arity() {
    let before = live();
    let cases: [(*const (), u16); 6] = [
        (sum1 as *const (), 1),
        (sum2 as *const (), 2),
        (sum3 as *const (), 3),
        (sum5 as *const (), 5),
        (sum16 as *const (), 16),
        (sum20 as *const (), 20),
    ];
    for (fun, arity) in cases {
        let n = usize::from(arity);
        let args: Vec<usize> = (1..=n).collect();
        let want: usize = args.iter().sum();
        // Exact, on an exclusive closure.
        // SAFETY: a fresh closure over scalars, handed over.
        let got = unsafe { call(apply::alloc_closure(fun, arity, 0), &args) };
        assert_eq!(got, want);
        // Exact, on a shared closure (it survives the call).
        let f = apply::alloc_closure(fun, arity, 0);
        // SAFETY: `f` is live; the extra reference keeps it alive.
        unsafe { inc(f) };
        // SAFETY: one of `f`'s two references is handed over; the other keeps
        // it live for the count read.
        unsafe {
            assert_eq!(call(f, &args), want);
            assert_eq!(rc(f), 1);
        }
        // One argument at a time: every under-application in turn.
        let mut g = f;
        for (i, &x) in args.iter().enumerate() {
            // SAFETY: `g` is owned.
            let r = unsafe { apply::apply(g, &[boxed(x)]) };
            if i + 1 < n {
                g = r;
            } else {
                assert_eq!(unbox(r), want);
            }
        }
    }
    // Over-application: `adder 5` returns a closure the rest is applied to.
    // SAFETY: a fresh closure over scalars, handed over.
    let got = unsafe { call(apply::alloc_closure(adder as *const (), 1, 0), &[5, 7]) };
    assert_eq!(got, 12);
    // An erased proof applied to anything is itself.
    // SAFETY: a scalar function and scalar arguments.
    let erased = unsafe { apply::apply(boxed(3), &[boxed(1), boxed(2)]) };
    assert_eq!(erased, boxed(3));
    assert_eq!(live(), before);
}

#[test]
fn a_shared_partial_application_keeps_its_fixed_arguments_alive() {
    let before = live();
    let payload = alloc_ctor(0, 0, 8);
    extern "C" fn first(a: Obj, b: Obj) -> Obj {
        // SAFETY: `b` is an owned scalar or object; this function consumes it.
        unsafe { dec(b) };
        a
    }
    let f = apply::alloc_closure(first as *const (), 2, 1);
    // SAFETY: `f` has one fixed field, which takes the payload's reference.
    unsafe {
        *f.cast::<u8>().add(CLOSURE_BYTES).cast::<Obj>() = payload;
        inc(f);
        let r = apply::apply(f, &[boxed(0)]);
        assert_eq!(r, payload);
        assert_eq!(rc(payload), 2, "the closure and the result each hold it");
        dec(r);
        dec(f);
    }
    assert_eq!(live(), before);
}

// --------------------------------------------------------------------------
// Arrays
// --------------------------------------------------------------------------

#[test]
fn arrays_round_trip_through_lists_and_grow_by_push() {
    let before = live();
    // SAFETY: owned values throughout.
    unsafe {
        let a = array::array_mk(list_of(50));
        let e: Vec<usize> = array::elements(a).iter().map(|&x| unbox(x)).collect();
        assert_eq!(e, (0..50).collect::<Vec<_>>());
        let mut a = a;
        for i in 50..300 {
            a = array::array_push(a, boxed(i));
        }
        assert_eq!(array::elements(a).len(), 300);
        let l = array::array_to_list(a);
        let mut o = l;
        let mut k = 0;
        while !is_scalar(o) {
            assert_eq!(unbox(ctor_get(o, 0)), k);
            k += 1;
            o = ctor_get(o, 1);
        }
        assert_eq!(k, 300);
        dec(l);
        // A shared array pushes onto a copy and keeps its own contents.
        let s = array::mk_array(boxed(3), boxed(9));
        inc(s);
        let t = array::array_push(s, boxed(1));
        assert_eq!(array::elements(s).len(), 3);
        assert_eq!(array::elements(t).len(), 4);
        dec(s);
        dec(t);
        // `mk_array` of an object holds it once per element.
        let v = alloc_ctor(0, 0, 8);
        let m = array::mk_array(boxed(4), v);
        assert_eq!(rc(v), 4);
        dec(m);
    }
    assert_eq!(live(), before);
}

#[test]
fn copy_slice_clamps_and_grows_as_upstream() {
    let before = live();
    let mk = |b: &[u8]| {
        let o = array::alloc_sarray(1, b.len(), b.len());
        // SAFETY: `o` holds `b.len()` bytes.
        unsafe { array::sarray_bytes_mut(o).copy_from_slice(b) };
        o
    };
    // (src, src_off, dest, dest_off, len, expected)
    type Case<'a> = (&'a [u8], usize, &'a [u8], usize, usize, &'a [u8]);
    let cases: [Case<'_>; 5] = [
        (b"abcdef", 1, b"xyz", 1, 3, b"xbcd"),
        (b"abcdef", 9, b"xyz", 0, 3, b"xyz"),
        (b"abcdef", 4, b"xyz", 9, 9, b"xyzef"),
        (b"abc", 0, b"", 0, 3, b"abc"),
        (b"abc", 1, b"xyz", 0, 1, b"byz"),
    ];
    for (src, so, dest, dof, len, want) in cases {
        let (s, d) = (mk(src), mk(dest));
        // SAFETY: owned and borrowed byte arrays and scalar positions.
        unsafe {
            let r = array::byte_array_copy_slice(s, boxed(so), d, boxed(dof), boxed(len), true);
            assert_eq!(array::sarray_bytes(r), want);
            dec(r);
            dec(s);
        }
    }
    assert_eq!(live(), before);
}

// --------------------------------------------------------------------------
// Strings
// --------------------------------------------------------------------------

/// The bytes of a string.
///
/// # Safety
///
/// `o` must be a live string, borrowed.
unsafe fn text(o: Obj) -> Vec<u8> {
    // SAFETY: `o` is a live string by this function's contract.
    unsafe { string::bytes(o) }.to_vec()
}

#[test]
fn ill_formed_utf8_is_replaced_as_upstream_replaces_it() {
    let before = live();
    // Upstream replaces an ill-formed leading byte and the continuation bytes
    // after it with one U+FFFD.
    let cases: [(&[u8], &[u8], usize); 6] = [
        (b"ok", b"ok", 2),
        (b"a\xffb", b"a\xef\xbf\xbdb", 3),
        (b"\xc3", b"\xef\xbf\xbd", 1),
        (b"\xe6\x97", b"\xef\xbf\xbd", 1),
        (b"\xed\xa0\x80z", b"\xef\xbf\xbdz", 2),
        (b"\xc0\x80\xe6\x97\xa5", b"\xef\xbf\xbd\xe6\x97\xa5", 2),
    ];
    for (input, want, len) in cases {
        let s = string::from_bytes(input);
        // SAFETY: `s` is a live string.
        assert_eq!(unsafe { text(s) }, want, "{input:?}");
        // SAFETY: `s` is a live string.
        assert_eq!(unsafe { (*s.cast::<StringObject>()).length }, len);
        // SAFETY: owned.
        unsafe { dec(s) };
    }
    assert_eq!(live(), before);
}

#[test]
fn strings_of_lists_numbers_and_bytes() {
    let before = live();
    // SAFETY: owned values throughout.
    unsafe {
        let mut l = boxed(0);
        for c in ['z', '😀', 'é', 'a'] {
            let cell = alloc_ctor(1, 2, 0);
            ctor_set(cell, 0, boxed(c as usize));
            ctor_set(cell, 1, l);
            l = cell;
        }
        let s = string::mk(l);
        assert_eq!(text(s), "aé😀z".as_bytes());
        let b = string::to_utf8(s);
        assert_eq!(array::sarray_bytes(b), "aé😀z".as_bytes());
        dec(b);
        dec(s);
        for n in [0usize, 7, 10, 12345, usize::MAX] {
            let s = string::of_usize(n);
            assert_eq!(text(s), std::format!("{n}").as_bytes());
            dec(s);
        }
    }
    assert_eq!(live(), before);
}

#[test]
fn memcmp_slices_and_the_fast_paths() {
    let before = live();
    let s = string::from_bytes("héllo héllo".as_bytes());
    // SAFETY: `s` is a live string; positions are scalars.
    unsafe {
        assert!(string::memcmp(s, s, boxed(0), boxed(7), boxed(6)));
        assert!(!string::memcmp(s, s, boxed(0), boxed(1), boxed(3)));
        let bytes = string::bytes(s);
        let size = bytes.len() + 1;
        assert_eq!(
            string::utf8_get_fast_cold(bytes.as_ptr(), 1, size, bytes[1]),
            'é' as u32
        );
        assert_eq!(unbox(string::utf8_next_fast_cold(1, bytes[1])), 3);
        // Two slices over the same string.
        let mk_slice = |a: usize, b: usize| {
            let sl = alloc_ctor(0, 3, 0);
            inc(s);
            ctor_set(sl, 0, s);
            ctor_set(sl, 1, boxed(a));
            ctor_set(sl, 2, boxed(b));
            sl
        };
        let (x, y) = (mk_slice(0, 6), mk_slice(7, 13));
        assert_eq!(string::slice_hash(x), string::slice_hash(y));
        assert_eq!(
            string::slice_hash(x),
            object::hash_bytes("héllo".as_bytes(), 11)
        );
        assert!(!string::slice_lt(x, y));
        let z = mk_slice(0, 3);
        assert!(string::slice_lt(z, x));
        dec(x);
        dec(y);
        dec(z);
        dec(s);
    }
    assert_eq!(live(), before);
}

#[test]
#[should_panic(expected = "outside its string")]
fn memcmp_refuses_a_range_past_the_end() {
    let s = string::from_bytes(b"abc");
    // SAFETY: a live string and scalar positions.
    let _ = unsafe { string::memcmp(s, s, boxed(2), boxed(0), boxed(2)) };
}

// --------------------------------------------------------------------------
// Reference cells, names, structural sharing, the environment
// --------------------------------------------------------------------------

#[test]
fn reference_cells_hand_values_in_and_out() {
    let before = live();
    let v = alloc_ctor(0, 0, 8);
    let r = object::st_mk_ref(v);
    // SAFETY: owned values throughout.
    unsafe {
        let got = object::st_ref_get(r);
        assert_eq!((got, rc(v)), (v, 2));
        dec(got);
        let taken = object::st_ref_take(r);
        assert_eq!(taken, v);
        object::st_ref_set(r, taken);
        let w = alloc_ctor(0, 0, 8);
        object::st_ref_set(r, w);
        dec(r);
    }
    assert_eq!(
        live(),
        before,
        "the replaced and the final value are both released"
    );
}

#[test]
#[should_panic(expected = "taken")]
fn a_taken_cell_cannot_be_read() {
    let r = object::st_mk_ref(boxed(1));
    // SAFETY: a live cell.
    unsafe {
        let _ = object::st_ref_take(r);
        let _ = object::st_ref_get(r);
    }
}

/// `Name.str p s` / `Name.num p k` with a cached hash.
fn name(p: Obj, component: Obj, is_str: bool, hash: u64) -> Obj {
    let n = alloc_ctor(if is_str { 1 } else { 2 }, 2, 8);
    // SAFETY: two object fields and eight scalar bytes.
    unsafe {
        ctor_set(n, 0, p);
        ctor_set(n, 1, component);
        n.cast::<u8>()
            .add(HEADER_BYTES + 16)
            .cast::<u64>()
            .write(hash);
    }
    n
}

#[test]
fn names_compare_by_structure_short_cut_by_their_hash() {
    let before = live();
    let a = name(
        name(boxed(0), string::from_bytes(b"Foo"), true, 1),
        boxed(3),
        false,
        2,
    );
    let b = name(
        name(boxed(0), string::from_bytes(b"Foo"), true, 1),
        boxed(3),
        false,
        2,
    );
    let c = name(
        name(boxed(0), string::from_bytes(b"Bar"), true, 1),
        boxed(3),
        false,
        2,
    );
    let d = name(
        name(boxed(0), string::from_bytes(b"Foo"), true, 1),
        boxed(3),
        false,
        9,
    );
    // SAFETY: live names.
    unsafe {
        assert!(object::name_eq(a, b));
        assert!(!object::name_eq(a, c), "same hash, different component");
        assert!(!object::name_eq(a, d), "different hash");
        assert!(object::name_eq(boxed(0), boxed(0)));
        assert!(!object::name_eq(a, boxed(0)));
        for n in [a, b, c, d] {
            dec(n);
        }
    }
    assert_eq!(live(), before);
}

#[test]
fn sharecommon_equality_implies_equal_hashes() {
    let before = live();
    // SAFETY: live objects throughout.
    unsafe {
        let x = string::from_bytes(b"shared");
        let y = string::from_bytes(b"shared");
        let z = string::from_bytes(b"sharee");
        assert!(object::sharecommon_eq(x, y));
        assert_eq!(object::sharecommon_hash(x), object::sharecommon_hash(y));
        assert!(!object::sharecommon_eq(x, z));
        let n1 = nat::canonical(false, &[1, 2, 3], false);
        let n2 = nat::canonical(false, &[1, 2, 3], false);
        let n3 = nat::canonical(true, &[1, 2, 3], true);
        assert!(object::sharecommon_eq(n1, n2));
        assert_eq!(object::sharecommon_hash(n1), object::sharecommon_hash(n2));
        assert!(!object::sharecommon_eq(n1, n3), "sign distinguishes");
        for o in [x, y, z, n1, n2, n3] {
            dec(o);
        }
    }
    assert_eq!(live(), before);
}

#[test]
fn the_environment_answers() {
    let before = live();
    // SAFETY: owned results throughout.
    unsafe {
        let r = io::random_bytes(8);
        assert_eq!(header(r).tag, 0, "an ok result");
        assert_eq!(array::sarray_bytes(ctor_get(r, 0)), &[0u8; 8]);
        dec(r);
        let e = io::unsupported_operation(io::ENOSYS, b"no fs");
        assert_eq!(
            (header(e).tag, header(e).other),
            (io::IO_ERROR_UNSUPPORTED_OPERATION, 1)
        );
        assert_eq!(text(ctor_get(e, 0)), b"no fs");
        assert_eq!(
            e.cast::<u8>().add(HEADER_BYTES + 8).cast::<u32>().read(),
            io::ENOSYS
        );
        dec(e);
        let v = alloc_ctor(0, 0, 8);
        let some = alloc_ctor(1, 1, 0);
        ctor_set(some, 0, v);
        let got = io::option_get_or_block(some);
        assert_eq!((got, rc(got)), (v, 1));
        dec(got);
    }
    assert_eq!(live(), before);
}

#[test]
#[should_panic(expected = "dropped")]
fn an_unresolved_promise_halts() {
    // SAFETY: `none`.
    let _ = unsafe { io::option_get_or_block(boxed(0)) };
}

#[test]
fn a_panic_returns_the_default_and_releases_the_message() {
    let before = live();
    let msg = string::from_bytes(b"boom");
    let def = alloc_ctor(0, 0, 8);
    // SAFETY: an owned message and default.
    let r = unsafe { object::panic_fn(def, msg) };
    assert_eq!(r, def);
    // SAFETY: owned.
    unsafe { dec(r) };
    assert_eq!(live(), before);
}

// --------------------------------------------------------------------------
// The limb algorithms on random operands
// --------------------------------------------------------------------------

struct XorShift(u64);
impl XorShift {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn limbs(&mut self, max: usize) -> Vec<u64> {
        let n = (self.next() as usize) % (max + 1);
        let mut v: Vec<u64> = (0..n)
            .map(|_| match self.next() % 5 {
                0 => 0,
                1 => u64::MAX,
                _ => self.next(),
            })
            .collect();
        while v.last() == Some(&0) {
            v.pop();
        }
        v
    }
}

fn buf(n: usize) -> Vec<u64> {
    std::vec![0; n + 2]
}

#[test]
fn division_satisfies_its_definition_on_random_operands() {
    let mut rng = XorShift(0x9e37_79b9_7f4a_7c15);
    for _ in 0..3000 {
        let a = rng.limbs(9);
        let b = rng.limbs(6);
        if b.is_empty() {
            continue;
        }
        let (mut q, mut r) = (buf(a.len()), buf(b.len()));
        let (qn, rn) = nat::limbs::divrem(&a, &b, &mut q, &mut r);
        let (q, r) = (&q[..qn], &r[..rn]);
        assert_eq!(nat::limbs::cmp(r, &b), core::cmp::Ordering::Less, "r < b");
        let mut prod = buf(q.len() + b.len());
        let pn = nat::limbs::mul(q, &b, &mut prod);
        let mut sum = buf(pn.max(rn) + 1);
        let sn = nat::limbs::add(&prod[..pn], r, &mut sum);
        assert_eq!(&sum[..sn], a.as_slice(), "q * b + r = a");
    }
}

#[test]
fn shifts_invert_and_bitwise_operations_match_u128() {
    let mut rng = XorShift(12345);
    for _ in 0..2000 {
        let a = rng.limbs(5);
        let s = (rng.next() % 300) as usize;
        let mut l = buf(a.len() + s / 64 + 1);
        let ln = nat::limbs::shl(&a, s, &mut l);
        let mut r = buf(ln);
        let rn = nat::limbs::shr(&l[..ln], s, &mut r);
        assert_eq!(&r[..rn], a.as_slice());
        let (x, y) = (
            u128::from(rng.next()) << 64 | u128::from(rng.next()),
            u128::from(rng.next()),
        );
        let xl = [x as u64, (x >> 64) as u64];
        let yl = [y as u64];
        let xs = &xl[..nat::limbs::normalized_len(&xl)];
        let ys = &yl[..nat::limbs::normalized_len(&yl)];
        for (op, want) in [(0, x & y), (1, x | y), (2, x ^ y)] {
            let mut o = buf(2);
            let n = nat::limbs::bitwise(xs, ys, &mut o[..2], |p, q| match op {
                0 => p & q,
                1 => p | q,
                _ => p ^ q,
            });
            let got = u128::from(o[0]) | u128::from(o[1]) << 64;
            assert_eq!(got, want);
            assert_eq!(n, nat::limbs::normalized_len(&o[..2]));
        }
    }
}

#[test]
fn gcd_and_pow_agree_with_their_definitions() {
    let mut rng = XorShift(777);
    for _ in 0..500 {
        let (x, y) = (rng.next() % 1_000_000, rng.next() % 1_000_000);
        let mut o = buf(1);
        let xl: Vec<u64> = if x == 0 { Vec::new() } else { std::vec![x] };
        let yl: Vec<u64> = if y == 0 { Vec::new() } else { std::vec![y] };
        let n = nat::limbs::gcd(&xl, &yl, &mut o);
        let (mut a, mut b) = (x, y);
        while b != 0 {
            (a, b) = (b, a % b);
        }
        assert_eq!(if n == 0 { 0 } else { o[0] }, a);
    }
    for base in [0u64, 1, 2, 3, 10, 255] {
        for e in 0..16usize {
            let bl: Vec<u64> = if base == 0 {
                Vec::new()
            } else {
                std::vec![base]
            };
            let mut o = buf(4);
            let n = nat::limbs::pow(&bl, e, &mut o);
            let want = (base as u128).checked_pow(e as u32).unwrap();
            let got = if n == 0 {
                0
            } else {
                u128::from(o[0]) | u128::from(o[1]) << 64
            };
            assert_eq!(got, want, "{base}^{e}");
        }
    }
}

#[test]
fn every_scratch_buffer_is_returned() {
    let before = live();
    let a = nat::canonical(false, &[7; 12], false);
    let b = nat::canonical(false, &[3, 5, 9], false);
    // SAFETY: borrowed numbers; owned results released.
    unsafe {
        for r in [
            nat::nat_big_div(a, b),
            nat::nat_big_mod(a, b),
            nat::nat_gcd(a, b),
            nat::nat_pow(b, boxed(9)),
        ] {
            dec(r);
        }
        dec(a);
        dec(b);
    }
    assert_eq!(live(), before);
}

#[test]
#[should_panic(expected = "exponent is too big")]
fn an_exponent_beyond_an_unsigned_is_refused() {
    let big = nat::canonical(false, &[0, 1], false);
    // SAFETY: borrowed numbers.
    let _ = unsafe { nat::nat_pow(boxed(2), big) };
}

#[test]
#[should_panic(expected = "negative")]
fn a_negative_int_is_not_a_nat() {
    let n = nat::canonical(true, &[0, 1], true);
    // SAFETY: an owned big `Int`.
    let _ = unsafe { nat::big_int_to_nat(n) };
}

// --------------------------------------------------------------------------
// Ill-formed bytes, which a `String` never holds but the runtime is still
// called on — through the fast paths, and on strings built unchecked
// --------------------------------------------------------------------------

#[test]
fn the_decoder_refuses_what_upstream_refuses() {
    // (bytes, position, what upstream's `lean_string_utf8_get_core` answers)
    let a = 'A' as u32;
    let cases: [(&[u8], usize, u32); 9] = [
        (b"\xed\x9f\xbf", 0, 0xD7FF),
        (b"\xed\xa0\x80", 0, a),
        (b"\xed\xbf\xbf", 0, a),
        (b"\xee\x80\x80", 0, 0xE000),
        (b"\xc0\x80", 0, a),
        (b"\xe0\x9f\xbf", 0, a),
        (b"\xf4\x90\x80\x80", 0, a),
        (b"\xf4\x8f\xbf\xbf", 0, 0x10FFFF),
        (b"\xe6\x97", 0, a),
    ];
    for (bytes, i, want) in cases {
        // SAFETY: `bytes` is readable for its length.
        let got = unsafe { string::utf8_get_fast_cold(bytes.as_ptr(), i, bytes.len(), bytes[i]) };
        assert_eq!(got, want, "{bytes:?}");
    }
}

#[test]
fn setting_a_truncated_last_character_replaces_what_is_there() {
    let before = live();
    // "ab" then a leading byte announcing three bytes with one present.
    let s = string::from_bytes_unchecked(b"ab\xe6", 3);
    // SAFETY: an owned string and a scalar position.
    let r = unsafe { string::utf8_set(s, boxed(2), 'z' as u32) };
    // SAFETY: `r` is a live string.
    assert_eq!(unsafe { text(r) }, b"abz");
    // SAFETY: owned.
    unsafe { dec(r) };
    assert_eq!(live(), before);
}

#[test]
fn an_exclusive_array_with_room_is_pushed_onto_in_place() {
    let before = live();
    // SAFETY: owned values.
    unsafe {
        let a = array::alloc_array(0, 4);
        let b = array::array_push(a, boxed(1));
        assert_eq!(a, b, "no copy when the array is exclusive and has room");
        let full = array::array_push(
            array::array_push(array::array_push(b, boxed(2)), boxed(3)),
            boxed(4),
        );
        assert_eq!(full, a);
        let grown = array::array_push(full, boxed(5));
        assert_ne!(grown, a, "a full array is copied to a larger one");
        dec(grown);
    }
    assert_eq!(live(), before);
}

/// Binary long division, one bit at a time: an algorithm sharing nothing with
/// Knuth's but the comparison and subtraction it is built from.
fn reference_divrem(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let bits = a.len() * 64;
    let mut q = std::vec![0u64; a.len().max(1)];
    let mut r: Vec<u64> = Vec::new();
    for bit in (0..bits).rev() {
        // r = 2r + bit
        let mut shifted = std::vec![0u64; r.len() + 1];
        let n = nat::limbs::shl(&r, 1, &mut shifted);
        shifted.truncate(n);
        if a[bit / 64] >> (bit % 64) & 1 == 1 {
            if shifted.is_empty() {
                shifted.push(1);
            } else {
                shifted[0] |= 1;
            }
        }
        r = shifted;
        if nat::limbs::cmp(&r, b) != core::cmp::Ordering::Less {
            let mut d = std::vec![0u64; r.len()];
            let n = nat::limbs::sub(&r, b, &mut d);
            d.truncate(n);
            r = d;
            q[bit / 64] |= 1 << (bit % 64);
        }
    }
    let qn = nat::limbs::normalized_len(&q);
    q.truncate(qn);
    (q, r)
}

#[test]
fn knuth_division_agrees_with_bitwise_long_division_on_structured_operands() {
    let mut rng = XorShift(0xdead_beef_cafe_f00d);
    // Divisor top limbs that stress the quotient estimate: tiny, one below a
    // power of two, exactly a power of two, and random.
    let tops = [
        1u64,
        2,
        3,
        0x7fff_ffff_ffff_ffff,
        0x8000_0000_0000_0000,
        u64::MAX,
    ];
    for _ in 0..600 {
        for &top in &tops {
            let mut b = rng.limbs(3);
            b.push(top);
            let mut a = rng.limbs(6);
            a.extend(std::iter::repeat_n(u64::MAX, (rng.next() % 3) as usize));
            a.push(rng.next() | 1);
            let (mut q, mut r) = (buf(a.len()), buf(b.len()));
            let (qn, rn) = nat::limbs::divrem(&a, &b, &mut q, &mut r);
            let (wq, wr) = reference_divrem(&a, &b);
            assert_eq!(
                (&q[..qn], &r[..rn]),
                (wq.as_slice(), wr.as_slice()),
                "{a:x?} / {b:x?}"
            );
        }
    }
}

#[test]
fn the_census_decides_exactly_the_symbols_this_runtime_does_not_provide() {
    const CENSUS: &str = include_str!("../../../../SeLe4n/Testing/RuntimeEnvironmentCensus.lean");
    let start = CENSUS
        .find("def runtimeUnprovidedSymbols : List String :=")
        .expect("the census declares its symbol list");
    let body = &CENSUS[start..];
    let list = &body[body.find('[').unwrap() + 1..body.find(']').unwrap()];
    let mut census: Vec<&str> = list
        .split(',')
        .map(|s| s.trim().trim_matches('"'))
        .collect();
    let mut ours: Vec<&str> = io::UNPROVIDED_SEMANTICS.to_vec();
    census.sort_unstable();
    ours.sort_unstable();
    assert_eq!(
        census, ours,
        "the Lean census and the Rust runtime disagree about the list"
    );
}

/// A `BaseIO` export's result, discharged, leaves the heap as it was: the one
/// reference the call returned is released.  This is the leak the HAL's six
/// `BaseIO` seams had while their declarations dropped the result — one object
/// per call, on the per-tick path.
#[test]
fn a_discharged_base_io_result_is_released() {
    let before = live();
    for _ in 0..1000 {
        let res = io_result_mk_ok(boxed(0));
        // SAFETY: `res` is a fresh `IO` result owned here.
        unsafe { discharge_base_io(LeanIoResult(res), "test_export") };
    }
    assert_eq!(live(), before, "discharging an `ok` result must free it");
}

/// The classification `discharge_base_io` decides by: only a tag-0 heap
/// constructor is `ok`, and every heap object is released whatever it held.
#[test]
fn an_io_result_is_classified_and_released() {
    let before = live();
    // SAFETY: each argument is a fresh object or a scalar, owned here.
    unsafe {
        assert_eq!(consume_io_result(io_result_mk_ok(boxed(0))), Ok(()));
        assert_eq!(
            consume_io_result(io_result_mk_error(boxed(0))),
            Err(IoResultRefused::Error)
        );
        assert_eq!(
            consume_io_result(alloc_ctor(7, 0, 0)),
            Err(IoResultRefused::Malformed { tag: Some(7) })
        );
        assert_eq!(
            consume_io_result(boxed(0)),
            Err(IoResultRefused::Malformed { tag: None })
        );
    }
    assert_eq!(live(), before, "every classified result must be freed");
}

/// `BaseIO` cannot fail, so an error result means the boundary is broken, and
/// the discharge refuses to continue.  On the host `fatal` panics, which is the
/// observable.
#[test]
#[should_panic(expected = "a BaseIO export returned a result BaseIO cannot produce")]
fn a_non_ok_base_io_result_halts() {
    // SAFETY: a fresh `IO` error result owned here.
    unsafe { discharge_base_io(LeanIoResult(io_result_mk_error(boxed(0))), "test_export") };
}
