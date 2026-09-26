//! Closures: allocation and application.
//!
//! Upstream's `apply.cpp` is generated — one function per argument count, each
//! a sixteen-way switch on the closure's arity.  Every one of them is the same
//! algorithm, which is written here once: exact application calls the function,
//! under-application makes a closure with more arguments fixed, and
//! over-application calls the function on as many arguments as it takes and
//! applies the result to the rest.  The exported `lean_apply_<n>` entry points
//! are instances of it.
//!
//! A function that takes up to `LEAN_CLOSURE_MAX_ARGS` (16) arguments is called
//! with them in registers; one that takes more is called with a pointer to an
//! array of them, which is how the Lean compiler emits it.

use super::{
    dec, fatal, inc, is_exclusive, is_scalar, mem, object, set_st_header, ClosureObject, Obj,
    CLOSURE_BYTES, TAG_CLOSURE,
};

/// `LEAN_CLOSURE_MAX_ARGS`.
pub const CLOSURE_MAX_ARGS: usize = 16;

/// `lean_alloc_closure(fun, arity, num_fixed)`.
#[must_use]
pub fn alloc_closure(fun: *const (), arity: u16, num_fixed: u16) -> Obj {
    if arity == 0 || num_fixed >= arity {
        fatal("lean_alloc_closure: bad arity");
    }
    let o = object::alloc_object(CLOSURE_BYTES + 8 * usize::from(num_fixed));
    // SAFETY: `o` is a fresh allocation of the closure's size.
    unsafe {
        set_st_header(o, TAG_CLOSURE, 0);
        let c = &mut *o.cast::<ClosureObject>();
        c.fun = fun;
        c.arity = arity;
        c.num_fixed = num_fixed;
    }
    o
}

/// The closure record of `f`.
///
/// # Safety
///
/// `f` must be a live closure object that stays live for `'a`.
unsafe fn closure<'a>(f: Obj) -> &'a ClosureObject {
    // SAFETY: `f` is a live closure by this function's contract.
    unsafe { &*f.cast::<ClosureObject>() }
}

fn fixed_slot(f: Obj, i: usize) -> *mut Obj {
    f.cast::<u8>()
        .wrapping_add(CLOSURE_BYTES)
        .cast::<Obj>()
        .wrapping_add(i)
}

type Fn1 = extern "C" fn(Obj) -> Obj;
type Fn2 = extern "C" fn(Obj, Obj) -> Obj;
type Fn3 = extern "C" fn(Obj, Obj, Obj) -> Obj;
type Fn4 = extern "C" fn(Obj, Obj, Obj, Obj) -> Obj;
type Fn5 = extern "C" fn(Obj, Obj, Obj, Obj, Obj) -> Obj;
type Fn6 = extern "C" fn(Obj, Obj, Obj, Obj, Obj, Obj) -> Obj;
type Fn7 = extern "C" fn(Obj, Obj, Obj, Obj, Obj, Obj, Obj) -> Obj;
type Fn8 = extern "C" fn(Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) -> Obj;
type Fn9 = extern "C" fn(Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) -> Obj;
type Fn10 = extern "C" fn(Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) -> Obj;
type Fn11 = extern "C" fn(Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) -> Obj;
type Fn12 = extern "C" fn(Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) -> Obj;
type Fn13 = extern "C" fn(Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) -> Obj;
type Fn14 =
    extern "C" fn(Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) -> Obj;
type Fn15 =
    extern "C" fn(Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj) -> Obj;
type Fn16 = extern "C" fn(
    Obj,
    Obj,
    Obj,
    Obj,
    Obj,
    Obj,
    Obj,
    Obj,
    Obj,
    Obj,
    Obj,
    Obj,
    Obj,
    Obj,
    Obj,
    Obj,
) -> Obj;
type FnN = extern "C" fn(*mut Obj) -> Obj;

/// `curry` of `apply.cpp`: calls `fun` on exactly `args`, which is its arity.
///
/// # Safety
///
/// `fun` must be a function of `args.len()` object arguments (or, above
/// sixteen, of one pointer to them) that consumes each argument.
unsafe fn call(fun: *const (), args: &mut [Obj]) -> Obj {
    let a = &*args;
    // SAFETY: in every arm, the caller guarantees `fun` has this signature; a
    // function pointer and a data pointer have the same representation on
    // every target this crate builds for.
    unsafe {
        match a.len() {
            1 => core::mem::transmute::<*const (), Fn1>(fun)(a[0]),
            2 => core::mem::transmute::<*const (), Fn2>(fun)(a[0], a[1]),
            3 => core::mem::transmute::<*const (), Fn3>(fun)(a[0], a[1], a[2]),
            4 => core::mem::transmute::<*const (), Fn4>(fun)(a[0], a[1], a[2], a[3]),
            5 => core::mem::transmute::<*const (), Fn5>(fun)(a[0], a[1], a[2], a[3], a[4]),
            6 => core::mem::transmute::<*const (), Fn6>(fun)(a[0], a[1], a[2], a[3], a[4], a[5]),
            7 => core::mem::transmute::<*const (), Fn7>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6],
            ),
            8 => core::mem::transmute::<*const (), Fn8>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7],
            ),
            9 => core::mem::transmute::<*const (), Fn9>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8],
            ),
            10 => core::mem::transmute::<*const (), Fn10>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9],
            ),
            11 => core::mem::transmute::<*const (), Fn11>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10],
            ),
            12 => core::mem::transmute::<*const (), Fn12>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11],
            ),
            13 => core::mem::transmute::<*const (), Fn13>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12],
            ),
            14 => core::mem::transmute::<*const (), Fn14>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12],
                a[13],
            ),
            15 => core::mem::transmute::<*const (), Fn15>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12],
                a[13], a[14],
            ),
            16 => core::mem::transmute::<*const (), Fn16>(fun)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12],
                a[13], a[14], a[15],
            ),
            0 => fatal("lean_apply: a call with no arguments"),
            _ => core::mem::transmute::<*const (), FnN>(fun)(args.as_mut_ptr()),
        }
    }
}

/// An argument buffer of `len` objects: on the stack up to the register limit,
/// in the kernel heap above it (upstream uses `alloca`).
struct Args {
    inline: [Obj; CLOSURE_MAX_ARGS],
    heap: usize,
    len: usize,
}

impl Args {
    fn new(len: usize) -> Self {
        let heap = if len > CLOSURE_MAX_ARGS {
            mem::alloc(len * 8).unwrap_or_else(|| object::internal_panic_out_of_memory())
        } else {
            0
        };
        Self {
            inline: [core::ptr::null_mut(); CLOSURE_MAX_ARGS],
            heap,
            len,
        }
    }

    fn slice(&mut self) -> &mut [Obj] {
        if self.heap == 0 {
            &mut self.inline[..self.len]
        } else {
            // SAFETY: `heap` is a live allocation of `len` words this buffer owns.
            unsafe { core::slice::from_raw_parts_mut(self.heap as *mut Obj, self.len) }
        }
    }
}

impl Drop for Args {
    fn drop(&mut self) {
        if self.heap != 0 && !mem::free(self.heap) {
            fatal("lean_apply: argument buffer lost");
        }
    }
}

/// `fix_args`: a closure with `args` fixed after `f`'s own, consuming `f`.
///
/// # Safety
///
/// `f` must be a live closure with more than `args.len()` arguments still
/// missing; the references to `f` and to each argument are consumed.
unsafe fn fix_args(f: Obj, args: &[Obj]) -> Obj {
    // SAFETY: `f` is a live closure by this function's contract.
    let c = unsafe { closure(f) };
    let (fun, arity, fixed) = (c.fun, c.arity, usize::from(c.num_fixed));
    let new_fixed = fixed + args.len();
    let r = alloc_closure(fun, arity, new_fixed as u16);
    // SAFETY: `f` is live and exclusive or shared as tested; `r` has room for
    // `new_fixed` fields.
    unsafe {
        let exclusive = is_exclusive(f);
        for i in 0..fixed {
            let v = fixed_slot(f, i).read();
            if !exclusive {
                inc(v);
            }
            fixed_slot(r, i).write(v);
        }
        if exclusive {
            object::free_object(f);
        } else {
            dec(f);
        }
        for (i, &a) in args.iter().enumerate() {
            fixed_slot(r, fixed + i).write(a);
        }
    }
    r
}

/// Applies `f` to `args`, consuming `f` and every argument: `lean_apply_n`.
///
/// # Safety
///
/// `f` must be a scalar (an erased proof) or a live closure; every element of
/// `args` a scalar or a live object; each reference is consumed.
pub unsafe fn apply(f: Obj, args: &[Obj]) -> Obj {
    if args.is_empty() {
        fatal("lean_apply: no arguments");
    }
    if is_scalar(f) {
        for &a in args {
            // SAFETY: forwarded from the caller.
            unsafe { dec(a) };
        }
        return f;
    }
    // SAFETY: `f` is not a scalar, so it is a live closure by the contract.
    let c = unsafe { closure(f) };
    let (fun, arity, fixed) = (c.fun, usize::from(c.arity), usize::from(c.num_fixed));
    let n = args.len();
    if fixed + n < arity {
        // SAFETY: forwarded from the caller; the closure still misses more
        // arguments than `args` supplies.
        return unsafe { fix_args(f, args) };
    }
    let take = arity - fixed;
    let mut buf = Args::new(arity);
    let all = buf.slice();
    // SAFETY: `f` is a live closure with `fixed` fields.
    let exclusive = unsafe { is_exclusive(f) };
    for (i, slot) in all.iter_mut().take(fixed).enumerate() {
        // SAFETY: field `i < fixed` of the live closure `f`.
        let v = unsafe { fixed_slot(f, i).read() };
        if !exclusive {
            // SAFETY: `v` is held by `f`, so it is live.
            unsafe { inc(v) };
        }
        *slot = v;
    }
    all[fixed..].copy_from_slice(&args[..take]);
    // SAFETY: `fun` takes exactly `arity` arguments, now all present.
    let r = unsafe { call(fun, all) };
    // SAFETY: the fields were moved out (exclusive) or duplicated (shared).
    unsafe {
        if exclusive {
            object::free_object(f);
        } else {
            dec(f);
        }
    }
    drop(buf);
    if take == n {
        r
    } else {
        // SAFETY: the rest of the arguments are the caller's, still owned.
        unsafe { apply(r, &args[take..]) }
    }
}

#[cfg(feature = "hw_target")]
mod exports {
    use super::*;

    macro_rules! export_apply {
        ($($name:ident($($a:ident),+);)+) => {$(
            /// One of `lean.h`'s fixed-arity application exports, minted by
            /// `export_apply`: [`apply`] to the listed arguments.
            ///
            /// # Safety
            ///
            /// `f` and every argument are owned references to live objects, which the application consumes (the Lean calling convention).
            #[no_mangle]
            pub unsafe extern "C" fn $name(f: Obj, $($a: Obj),+) -> Obj {
                // SAFETY: the Lean calling convention: `f` and every argument are
                // owned references the callee consumes.
                unsafe { apply(f, &[$($a),+]) }
            }
        )+};
    }

    export_apply! {
        lean_apply_1(a1);
        lean_apply_2(a1, a2);
        lean_apply_3(a1, a2, a3);
        lean_apply_4(a1, a2, a3, a4);
        lean_apply_5(a1, a2, a3, a4, a5);
        lean_apply_6(a1, a2, a3, a4, a5, a6);
        lean_apply_7(a1, a2, a3, a4, a5, a6, a7);
        lean_apply_8(a1, a2, a3, a4, a5, a6, a7, a8);
        lean_apply_9(a1, a2, a3, a4, a5, a6, a7, a8, a9);
        lean_apply_10(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
        lean_apply_11(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
        lean_apply_12(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12);
        lean_apply_13(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13);
        lean_apply_14(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14);
        lean_apply_15(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15);
        lean_apply_16(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16);
    }

    /// `lean_apply_n(f, n, args)` and `lean_apply_m`: [`apply`] to `n` arguments
    /// read from `args`.
    ///
    /// # Safety
    ///
    /// `args` must point to `n` owned object references.
    #[no_mangle]
    pub unsafe extern "C" fn lean_apply_n(f: Obj, n: u32, args: *const Obj) -> Obj {
        // SAFETY: the caller supplies `n` arguments at `args`.
        unsafe { apply(f, core::slice::from_raw_parts(args, n as usize)) }
    }

    /// `lean_apply_m`: [`lean_apply_n`] for more than sixteen arguments.
    ///
    /// # Safety
    ///
    /// As [`lean_apply_n`].
    #[no_mangle]
    pub unsafe extern "C" fn lean_apply_m(f: Obj, n: u32, args: *const Obj) -> Obj {
        // SAFETY: forwarded from the caller.
        unsafe { lean_apply_n(f, n, args) }
    }
}
