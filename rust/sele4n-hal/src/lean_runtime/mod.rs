//! WS-BP BP2.2: the kernel's own Lean runtime.
//!
//! Lean compiles every module to C that calls into a runtime for everything the
//! language needs beneath the program's logic: allocating, freeing and
//! reference-counting heap objects, applying closures, arbitrary-precision
//! `Nat` and `Int`, strings, arrays, `ST.Ref`.  Upstream ships that runtime as
//! `libleanrt` — C++ over the C++ standard library, threads and an operating
//! system — which a freestanding kernel image cannot link.  This module is the
//! kernel's implementation of the part the kernel's Lean objects reach, in Rust,
//! so the image contains Lean-generated C and Rust and nothing else.
//!
//! **What "the part the kernel reaches" is, is measured, not chosen.**  The Lean
//! archive lane links `libsele4n.a` rooted at the library initializer and every
//! production `@[export]`, and the symbols that link leaves undefined are the
//! surface this module must provide; `scripts/build_lean_aarch64_archive.py`
//! holds the provided set to that derivation.  Each symbol is one of three
//! kinds, and the kind is recorded where it is defined:
//!
//! * **faithful** — the upstream semantics, ported from the `lean4` sources at
//!   the toolchain's own commit and checked against the upstream runtime by a
//!   shared fixture (`tests/fixtures/lean_runtime_conformance.expected`, which a
//!   Lean suite running on upstream's runtime and the Rust tests here both read);
//! * **environmental** — an operation whose upstream answer comes from the
//!   operating system (the platform queries, the build's git hash, entropy,
//!   temporary files), answered for the environment the kernel actually runs in;
//! * **fail-closed** — floating-point formatting and transcendental arithmetic,
//!   which the kernel never performs and whose upstream results depend on the
//!   host C library; each halts the core, naming itself, if it is ever called.
//!
//! **Invariants the runtime keeps, and relies on.**  No object is ever
//! multi-threaded (`m_rc < 0`): nothing here marks one, the kernel's Lean code
//! runs one core at a time under the kernel-entry lock, and every path that
//! would meet one halts.  No task or promise object exists, for the same
//! reason.  Persistent objects (`m_rc == 0`) are never freed.
//!
//! The object layouts are `lean.h`'s, byte for byte: the inline paths in every
//! compiled object read and write these structures directly, so they are a
//! contract with the C compiler rather than a choice of this module.

mod mem;

pub mod apply;
pub mod array;
pub mod io;
pub mod nat;
pub mod object;
pub mod string;

#[cfg(test)]
mod conformance;
#[cfg(test)]
mod tests;

use core::ptr;

// ==========================================================================
// lean.h: tags and the object header
// ==========================================================================

/// The largest constructor tag; tags above it name the special object kinds.
pub const MAX_CTOR_TAG: u8 = 243;
/// `LeanPromise`.
pub const TAG_PROMISE: u8 = 244;
/// `LeanClosure`.
pub const TAG_CLOSURE: u8 = 245;
/// `LeanArray`.
pub const TAG_ARRAY: u8 = 246;
/// `LeanStructArray` (reserved upstream; never allocated).
pub const TAG_STRUCT_ARRAY: u8 = 247;
/// `LeanScalarArray`.
pub const TAG_SCALAR_ARRAY: u8 = 248;
/// `LeanString`.
pub const TAG_STRING: u8 = 249;
/// `LeanMPZ`: a `Nat` above `MAX_SMALL_NAT` or an `Int` outside `i32`.
pub const TAG_MPZ: u8 = 250;
/// `LeanThunk`.
pub const TAG_THUNK: u8 = 251;
/// `LeanTask`.
pub const TAG_TASK: u8 = 252;
/// `LeanRef`.
pub const TAG_REF: u8 = 253;
/// `LeanExternal`.
pub const TAG_EXTERNAL: u8 = 254;

/// `LEAN_MAX_SMALL_NAT`: the largest `Nat` stored unboxed.
pub const MAX_SMALL_NAT: usize = usize::MAX >> 1;
/// `LEAN_MAX_SMALL_INT` on a 64-bit target.
pub const MAX_SMALL_INT: i64 = i32::MAX as i64;
/// `LEAN_MIN_SMALL_INT` on a 64-bit target.
pub const MIN_SMALL_INT: i64 = i32::MIN as i64;

/// `lean_object`: the header every heap object starts with.  `lean.h` declares
/// it as `int m_rc; unsigned m_cs_sz:16; unsigned m_other:8; unsigned m_tag:8;`,
/// which both C compilers the kernel is built with lay out least-significant
/// bit first — so byte 6 is `m_other` and byte 7 is `m_tag`, as `lean.h`'s own
/// `LEAN_BYTE(header, 7)` assumes.
#[repr(C)]
#[derive(Debug)]
pub struct LeanObject {
    /// Reference count: `> 0` single-threaded, `0` persistent, `< 0` shared
    /// across threads (never produced by this runtime).
    pub rc: i32,
    /// Unused by this runtime's allocator; reused for the deletion list.
    pub cs_sz: u16,
    /// Constructor field count, or a scalar array's element size.
    pub other: u8,
    /// The object kind.
    pub tag: u8,
}

/// `lean_ctor_object`.
#[repr(C)]
pub struct CtorObject {
    /// The header.
    pub header: LeanObject,
    // `lean_object * m_objs[]` follows.
}

/// `lean_array_object`.
#[repr(C)]
pub struct ArrayObject {
    /// The header.
    pub header: LeanObject,
    /// Elements in use.
    pub size: usize,
    /// Elements the allocation holds.
    pub capacity: usize,
    // `lean_object * m_data[]` follows.
}

/// `lean_sarray_object`.
#[repr(C)]
pub struct SArrayObject {
    /// The header; `other` is the element size.
    pub header: LeanObject,
    /// Elements in use.
    pub size: usize,
    /// Elements the allocation holds.
    pub capacity: usize,
    // `uint8_t m_data[]` follows.
}

/// `lean_string_object`.
#[repr(C)]
pub struct StringObject {
    /// The header.
    pub header: LeanObject,
    /// Bytes in use, including the terminating zero.
    pub size: usize,
    /// Bytes the allocation holds.
    pub capacity: usize,
    /// UTF-8 characters.
    pub length: usize,
    // `char m_data[]` follows.
}

/// `lean_closure_object`.
#[repr(C)]
pub struct ClosureObject {
    /// The header.
    pub header: LeanObject,
    /// The function the closure applies.
    pub fun: *const (),
    /// Arguments the function expects.
    pub arity: u16,
    /// Arguments already fixed.
    pub num_fixed: u16,
    // `lean_object * m_objs[]` follows (at offset 24).
}

/// `lean_ref_object`.
#[repr(C)]
pub struct RefObject {
    /// The header.
    pub header: LeanObject,
    /// The value; null while taken.
    pub value: *mut LeanObject,
}

/// `lean_thunk_object`.
#[repr(C)]
pub struct ThunkObject {
    /// The header.
    pub header: LeanObject,
    /// The value, once forced.
    pub value: *mut LeanObject,
    /// The closure, until forced.
    pub closure: *mut LeanObject,
}

/// `lean_external_class`.
#[repr(C)]
pub struct ExternalClass {
    /// Frees the external data.
    pub finalize: extern "C" fn(*mut core::ffi::c_void),
    /// Applies a closure to every Lean object the data holds.
    pub foreach: extern "C" fn(*mut core::ffi::c_void, *mut LeanObject),
}

/// `lean_external_object`.
#[repr(C)]
pub struct ExternalObject {
    /// The header.
    pub header: LeanObject,
    /// The class.
    pub class: *const ExternalClass,
    /// The data.
    pub data: *mut core::ffi::c_void,
}

/// This runtime's `LeanMPZ` object.  `lean.h` never looks inside one — every
/// operation on a big number is a runtime call — so the representation is this
/// module's: sign and magnitude, the magnitude in little-endian 64-bit limbs
/// with no leading zero limb.
#[repr(C)]
pub struct MpzObject {
    /// The header.
    pub header: LeanObject,
    /// Limbs in the magnitude; at least one.
    pub size: usize,
    /// `1` for a negative value, `0` otherwise.
    pub neg: usize,
    // `u64 limbs[]` follows.
}

/// Size in bytes of each fixed part, as `lean.h`'s `sizeof` computes it.  The
/// shared layout fixture pins these against the C compiler.
pub const HEADER_BYTES: usize = core::mem::size_of::<LeanObject>();
/// `sizeof(lean_array_object)`.
pub const ARRAY_BYTES: usize = core::mem::size_of::<ArrayObject>();
/// `sizeof(lean_string_object)`.
pub const STRING_BYTES: usize = core::mem::size_of::<StringObject>();
/// `sizeof(lean_closure_object)`.
pub const CLOSURE_BYTES: usize = core::mem::size_of::<ClosureObject>();
/// The fixed part of this runtime's big number.
pub const MPZ_BYTES: usize = core::mem::size_of::<MpzObject>();

const _: () = assert!(HEADER_BYTES == 8);
const _: () = assert!(ARRAY_BYTES == 24);
const _: () = assert!(STRING_BYTES == 32);
const _: () = assert!(CLOSURE_BYTES == 24);
const _: () = assert!(core::mem::size_of::<RefObject>() == 16);
const _: () = assert!(core::mem::size_of::<ThunkObject>() == 24);
const _: () = assert!(MPZ_BYTES == 24);

/// A Lean object reference: a boxed scalar (low bit set) or a heap object.
pub type Obj = *mut LeanObject;

// ==========================================================================
// Scalars
// ==========================================================================

/// `lean_is_scalar`.
#[must_use]
pub fn is_scalar(o: Obj) -> bool {
    (o as usize) & 1 == 1
}

/// `lean_box`.
#[must_use]
pub fn boxed(n: usize) -> Obj {
    ptr::without_provenance_mut((n << 1) | 1)
}

/// `lean_unbox`.
#[must_use]
pub fn unbox(o: Obj) -> usize {
    (o as usize) >> 1
}

/// `lean_scalar_to_int` on a 64-bit target: the boxed `Int`'s low 32 bits.
#[must_use]
pub fn scalar_to_int(o: Obj) -> i32 {
    unbox(o) as u32 as i32
}

/// `lean_box((unsigned)n)`: a boxed `Int`.
#[must_use]
pub fn box_int(n: i32) -> Obj {
    boxed(n as u32 as usize)
}

// ==========================================================================
// The fail-closed end
// ==========================================================================

/// Writes a diagnostic line.  The boot UART on the image; nothing on the host,
/// where the test harness reports the panic `fatal` raises instead.
pub fn diagnostic(prefix: &str, message: &[u8]) {
    #[cfg(feature = "hw_target")]
    {
        let text = core::str::from_utf8(message).unwrap_or("<non-UTF-8 message>");
        crate::kprintln!("[lean_runtime] {}{}", prefix, text);
    }
    #[cfg(not(feature = "hw_target"))]
    {
        let _ = (prefix, message);
    }
}

/// Parks the core after naming why.  Every contract violation, exhausted heap
/// and fail-closed operation in this runtime ends here: the Lean program has no
/// recovery path for any of them, and continuing would compute with a value
/// the program's own semantics does not describe.
pub fn fatal(reason: &str) -> ! {
    diagnostic("FATAL: ", reason.as_bytes());
    #[cfg(not(target_arch = "aarch64"))]
    {
        panic!("lean_runtime fatal: {reason}");
    }
    #[cfg(target_arch = "aarch64")]
    {
        crate::cpu::fatal_halt()
    }
}

// ==========================================================================
// Header access
// ==========================================================================
//
// Every function below takes a pointer to a live heap object — never a boxed
// scalar — owned by the Lean program that passed it.  They are the only places
// this runtime dereferences an object pointer directly; the operations are
// written against them.

/// The header of `o`.
///
/// # Safety
///
/// `o` must point to a live heap object.
#[must_use]
pub unsafe fn header<'a>(o: Obj) -> &'a mut LeanObject {
    // SAFETY: the caller guarantees `o` is a live heap object, whose first
    // eight bytes are its header.
    unsafe { &mut *o }
}

/// `lean_ptr_tag`.
///
/// # Safety
///
/// `o` must point to a live heap object.
#[must_use]
pub unsafe fn tag(o: Obj) -> u8 {
    // SAFETY: forwarded from the caller.
    unsafe { header(o).tag }
}

/// `lean_set_st_header`: a fresh single-threaded object of kind `tag`.
///
/// # Safety
///
/// `o` must point to at least a header's worth of writable memory.
pub unsafe fn set_st_header(o: Obj, tag: u8, other: u8) {
    // SAFETY: forwarded from the caller.
    unsafe {
        o.write(LeanObject {
            rc: 1,
            cs_sz: 0,
            other,
            tag,
        });
    }
}

/// `lean_is_exclusive`.
///
/// # Safety
///
/// `o` must point to a live heap object.
#[must_use]
pub unsafe fn is_exclusive(o: Obj) -> bool {
    // SAFETY: forwarded from the caller.
    unsafe { header(o).rc == 1 }
}

/// `lean_inc`: a no-op on a scalar or a persistent object.
///
/// # Safety
///
/// `o` must be a scalar or point to a live heap object.
pub unsafe fn inc(o: Obj) {
    if is_scalar(o) {
        return;
    }
    // SAFETY: `o` is a heap object by the caller's contract and the test above.
    let h = unsafe { header(o) };
    match h.rc {
        rc if rc > 0 => h.rc = rc + 1,
        0 => {}
        _ => fatal("lean_inc: multi-threaded object"),
    }
}

/// `lean_dec`: a no-op on a scalar or a persistent object; frees `o` and every
/// object only it kept alive when this was the last reference.
///
/// # Safety
///
/// `o` must be a scalar or point to a live heap object the caller owns a
/// reference to, which this call consumes.
pub unsafe fn dec(o: Obj) {
    if is_scalar(o) {
        return;
    }
    // SAFETY: `o` is a heap object by the caller's contract and the test above.
    let h = unsafe { header(o) };
    if h.rc > 1 {
        h.rc -= 1;
    } else if h.rc != 0 {
        // SAFETY: forwarded from the caller.
        unsafe { object::dec_ref_cold(o) };
    }
}

// ==========================================================================
// Field access
// ==========================================================================

/// Pointer to the `i`-th word after the header.
fn word_after_header(o: Obj, i: usize) -> *mut Obj {
    o.cast::<u8>().wrapping_add(HEADER_BYTES + i * 8).cast()
}

/// `lean_ctor_get`.
///
/// # Safety
///
/// `o` must be a live constructor object with more than `i` object fields.
#[must_use]
pub unsafe fn ctor_get(o: Obj, i: usize) -> Obj {
    // SAFETY: the caller guarantees field `i` exists; fields start right after
    // the header.
    unsafe { word_after_header(o, i).read() }
}

/// `lean_ctor_set`.
///
/// # Safety
///
/// `o` must be a live constructor object with more than `i` object fields.
pub unsafe fn ctor_set(o: Obj, i: usize, v: Obj) {
    // SAFETY: as for `ctor_get`.
    unsafe { word_after_header(o, i).write(v) }
}

/// `lean_ctor_get_uint64(o, offset)`: a scalar field `offset` bytes past the
/// object fields' start.
///
/// # Safety
///
/// `o` must be a live constructor object with eight scalar bytes at `offset`.
#[must_use]
pub unsafe fn ctor_get_u64(o: Obj, offset: usize) -> u64 {
    // SAFETY: forwarded from the caller; constructor scalars are 8-aligned here
    // because every caller's offset is a multiple of eight.
    unsafe {
        o.cast::<u8>()
            .add(HEADER_BYTES + offset)
            .cast::<u64>()
            .read_unaligned()
    }
}

/// `lean_alloc_ctor(tag, num_objs, scalar_sz)`.  Halts when the heap is
/// exhausted, as `lean.h`'s own allocation paths do.
#[must_use]
pub fn alloc_ctor(tag: u8, num_objs: u8, scalar_sz: usize) -> Obj {
    debug_assert!(tag <= MAX_CTOR_TAG);
    let o = object::alloc_object(HEADER_BYTES + 8 * usize::from(num_objs) + scalar_sz);
    // SAFETY: `alloc_object` returned at least a header's worth of memory.
    unsafe { set_st_header(o, tag, num_objs) };
    o
}

/// `lean_io_result_mk_ok`.
///
/// `value` is stored, never dereferenced, which is why this is not `unsafe`.
#[must_use]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub fn io_result_mk_ok(value: Obj) -> Obj {
    let r = alloc_ctor(0, 1, 0);
    // SAFETY: `r` was just allocated with one object field.
    unsafe { ctor_set(r, 0, value) };
    r
}

/// `lean_io_result_mk_error`.
///
/// `error` is stored, never dereferenced, which is why this is not `unsafe`.
#[must_use]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub fn io_result_mk_error(error: Obj) -> Obj {
    let r = alloc_ctor(1, 1, 0);
    // SAFETY: `r` was just allocated with one object field.
    unsafe { ctor_set(r, 0, error) };
    r
}

/// The `IO` result a Lean **module initializer** (`initialize_<pkg>_<Module>`)
/// returns across the C boundary: an owned heap constructor, tag 0 for `ok` and
/// tag 1 for `error` (`lean_io_result_mk_ok` / `lean_io_result_mk_error`).
///
/// Only initializers return one.  Lean 4.28 compiles every *other* `IO` /
/// `BaseIO` function without a world argument and without a result wrapper:
/// it returns the action's value directly, so a `BaseIO Unit` export returns
/// `lean_box(0)` and is declared [`LeanBaseIoUnit`].  The two are distinct
/// types because reading one as the other is the defect the post-BP4.5 ABI
/// audit found — every `BaseIO Unit` export's scalar was refused as a
/// malformed `IO` result, so the first tick on a ready core would have halted
/// it.  `#[must_use]` makes a dropped result an error under the crate's
/// `-D warnings`; `#[repr(transparent)]` makes it the pointer at the ABI.
#[must_use = "a Lean initializer's `IO` result owns a heap object: pass it to \
              `consume_io_result`"]
#[repr(transparent)]
#[derive(Debug)]
pub struct LeanIoResult(Obj);

impl LeanIoResult {
    /// The object, handed over: the caller now owns its one reference.
    pub fn into_obj(self) -> Obj {
        self.0
    }
}

/// The value a Lean `BaseIO Unit` function returns across the C boundary.
///
/// Lean 4.28 returns an `IO` / `BaseIO` action's value directly — no world
/// argument, no `IO` result constructor — so this is `Unit`'s boxed
/// representation, `lean_box(0)`, a scalar with nothing to release.  It is a
/// distinct `#[must_use]` type rather than a bare [`Obj`] so a call's result
/// cannot be ignored unchecked: [`discharge_base_io`] holds it to `lean_box(0)`
/// and halts on anything else, which is the one signal a mis-declared export
/// (one whose Lean type is not `BaseIO Unit`) can give at the boundary.
/// `scripts/check_kernel_entry_exports.py` holds every HAL declaration of a
/// non-initializer Lean export returning `lean_object*` to this type.
#[must_use = "a `BaseIO Unit` export's value must be checked: pass it to `discharge_base_io`"]
#[repr(transparent)]
#[derive(Debug)]
pub struct LeanBaseIoUnit(Obj);

impl LeanBaseIoUnit {
    /// The value, handed over.
    pub fn into_obj(self) -> Obj {
        self.0
    }
}

/// `Unit`'s boxed representation, `lean_box(0)`: what a HAL `@[extern]` whose
/// Lean type is `BaseIO Unit` (or any `… → BaseIO Unit`) must return.
///
/// The generated C declares every such extern `lean_object* f(…)` and uses the
/// value — returns it upward or `lean_dec`s it — so a Rust definition that
/// returns nothing leaves whatever the last computation put in `x0` to be read
/// as an object reference.  The post-BP4.5 ABI audit found thirty-three HAL
/// externs doing exactly that.  `scripts/check_kernel_entry_exports.py` holds
/// every HAL definition of a Lean-called symbol to the C prototype the Lean
/// compiler generated for it, return type included.
#[must_use]
pub fn base_io_unit() -> Obj {
    boxed(0)
}

/// Why an `IO` result is not `ok`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IoResultRefused {
    /// An `IO` error (constructor tag 1).  The error object is released
    /// without being read, because reading it would mean calling back into
    /// Lean, and the runtime never does that.
    Error,
    /// A scalar, or a constructor whose tag is neither `ok` (0) nor `error`
    /// (1).  No generated initializer returns one, so it is refused as a
    /// malformed result rather than read as success.
    Malformed {
        /// The tag found, or `None` for a scalar.
        tag: Option<u8>,
    },
}

/// Classify and consume a module initializer's `IO` result ([`LeanIoResult`]):
/// `Ok(())` exactly for a heap constructor with tag 0 (`lean.h`'s
/// `lean_io_result_is_ok`).  Not for any other export: those return their
/// value directly, and a `BaseIO Unit` one goes to [`discharge_base_io`].  Every heap
/// object, whatever its tag, has the one reference it arrived with released.
///
/// # Safety
///
/// `res` must be a scalar or a live heap object whose one reference the caller
/// owns; this call consumes it.
pub unsafe fn consume_io_result(res: Obj) -> Result<(), IoResultRefused> {
    if is_scalar(res) {
        return Err(IoResultRefused::Malformed { tag: None });
    }
    // SAFETY: `res` is a live heap object by the caller's contract and the
    // test above.
    let tag = unsafe { self::tag(res) };
    // SAFETY: the reference is the caller's to hand over, and nothing below
    // reads `res` again.
    unsafe { dec(res) };
    match tag {
        0 => Ok(()),
        1 => Err(IoResultRefused::Error),
        other => Err(IoResultRefused::Malformed { tag: Some(other) }),
    }
}

/// Check the value a `BaseIO Unit` export the HAL called returned, or halt.
///
/// Lean 4.28 returns the action's value directly, so the only value a
/// `BaseIO Unit` function can return is `lean_box(0)`, a scalar that owns
/// nothing.  Anything else means the boundary is broken — the export's Lean
/// type is not the one its declaration claims — and that halts rather than
/// continues; a heap object is released first so the report is the only
/// effect.  `symbol` names the export in the report.
///
/// # Safety
///
/// `res` must be the value an export just returned to this caller; if it is a
/// heap object, this call consumes its one reference.
pub unsafe fn discharge_base_io(res: LeanBaseIoUnit, symbol: &str) {
    let o = res.into_obj();
    if is_scalar(o) && unbox(o) == 0 {
        return;
    }
    if !is_scalar(o) {
        // SAFETY: a heap object the caller handed over by its contract.
        unsafe { dec(o) };
    }
    diagnostic(
        "BaseIO Unit export returned a value other than lean_box(0): ",
        symbol.as_bytes(),
    );
    fatal("a BaseIO Unit export returned a value BaseIO Unit cannot produce");
}
