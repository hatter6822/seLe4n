//! The environment: what upstream asks the operating system, answered for the
//! machine the kernel runs on — and the operations the kernel never performs,
//! which fail closed.
//!
//! **Environmental answers.**  The platform queries describe this target
//! (64-bit, not Windows, macOS or Emscripten), which is also what they answer
//! on the host the conformance fixture is generated on, so the fixture pins
//! them.  `Lean.githash` is the commit the toolchain was built from.  Creating
//! a temporary file or directory fails with an `unsupportedOperation` error,
//! because the kernel image has no file system — an `IO` action's contract
//! includes failure, so this is an answer rather than a refusal.
//!
//! **Entropy.**  `IO.getRandomBytes` reads "a system entropy source"; the
//! kernel image has none.  The one call the kernel makes is the library
//! initializer seeding `IO.stdGenRef`, a generator only `IO.rand` reads, and a
//! failed read there would abort initialization.  So this answers with zero
//! bytes, and the claim that makes that sound is checked rather than assumed:
//! `SeLe4n/Testing/RuntimeEnvironmentCensus.lean` (Tier 1) proves no kernel
//! entry point reaches `IO.stdGenRef`, `IO.rand` or `IO.getRandomBytes`, so the
//! value is dead.  A kernel feature that wants randomness needs a hardware
//! entropy source first, and that census fails the day the need is written.
//!
//! **Fail-closed.**  Formatting a `Float` and the transcendental `pow` depend on
//! the host C library, and the kernel is FP-free: no transition computes a
//! `Float`.  Each halts, naming itself, if it is ever called.

use super::{boxed, ctor_get, dec, fatal, inc, is_scalar, Obj};

/// The commit the Lean toolchain was built from (`lean --githash`).  The Lean
/// archive lane checks this equals the toolchain's own answer, so a toolchain
/// bump that forgets it fails there.
pub const LEAN_GITHASH: &str = "7e01a1bf5c70fc6167d49c345d3bf80596e9a79b";

/// The C symbols this runtime answers environmentally (entropy, temporary
/// files) or refuses (floating-point formatting and arithmetic): the upstream
/// semantics it does not provide.  `SeLe4n/Testing/RuntimeEnvironmentCensus.lean`
/// proves no kernel entry reaches any of them, and a test holds its list equal
/// to this one.
pub const UNPROVIDED_SEMANTICS: [&str; 9] = [
    "lean_io_get_random_bytes",
    "lean_io_create_tempfile",
    "lean_io_create_tempdir",
    "lean_float_to_string",
    "lean_float32_to_string",
    "lean_float_scaleb",
    "lean_float32_scaleb",
    "pow",
    "powf",
];

/// `ENOSYS`: the operating-system error code for "not implemented".
pub const ENOSYS: u32 = 38;

/// The constructor index of `IO.Error.unsupportedOperation` — its position in
/// the inductive's declaration, which is the tag the Lean compiler gives it.
/// The conformance fixture carries the index Lean computes (`ctorIdx`), and the
/// Rust tests hold this constant to it.
pub const IO_ERROR_UNSUPPORTED_OPERATION: u8 = 4;

/// `IO.Error.unsupportedOperation code details`: one object field (`details`)
/// followed by the `UInt32` code in the scalar area, as the Lean compiler lays
/// out a constructor — built here rather than through the `@[export]`ed
/// `mkUnsupportedOperation`, because the runtime never calls back into the
/// program it serves.
#[must_use]
pub fn unsupported_operation(code: u32, details: &[u8]) -> Obj {
    let text = super::string::from_bytes_unchecked(details, super::string::utf8_strlen(details));
    let e = super::alloc_ctor(IO_ERROR_UNSUPPORTED_OPERATION, 1, 4);
    // SAFETY: `e` has one object field and four scalar bytes after it.
    unsafe {
        super::ctor_set(e, 0, text);
        e.cast::<u8>()
            .add(super::HEADER_BYTES + 8)
            .cast::<u32>()
            .write_unaligned(code);
    }
    e
}

/// `lean_system_platform_nbits`.
#[must_use]
pub fn platform_nbits() -> Obj {
    boxed(usize::BITS as usize)
}

/// `lean_io_get_random_bytes(n)`: `n` zero bytes (see the module docs).
#[must_use]
pub fn random_bytes(n: usize) -> Obj {
    let r = super::array::alloc_sarray(1, n, n);
    // SAFETY: `r` is a fresh byte array of `n` bytes.
    unsafe { super::array::sarray_bytes_mut(r).fill(0) };
    super::io_result_mk_ok(r)
}

/// `lean_option_get_or_block(opt)`: the value of a resolved promise's result,
/// consuming the option.  An unresolved promise is one whose resolver was
/// dropped; upstream panics and blocks forever, and the kernel halts.
///
/// # Safety
///
/// `opt` must be a live `Option`; consumed.
pub unsafe fn option_get_or_block(opt: Obj) -> Obj {
    if is_scalar(opt) {
        fatal("Promise.result!: promise has been dropped without ever being resolved");
    }
    // SAFETY: `some v` has `v` as its only field; the value outlives the cell
    // because it gains a reference before the cell loses its own.
    unsafe {
        let v = ctor_get(opt, 0);
        inc(v);
        dec(opt);
        v
    }
}

#[cfg(feature = "hw_target")]
mod exports {
    use super::*;

    /// `lean_system_platform_nbits`.
    #[no_mangle]
    pub extern "C" fn lean_system_platform_nbits(_unit: Obj) -> Obj {
        platform_nbits()
    }

    /// `lean_system_platform_windows`.
    #[no_mangle]
    pub extern "C" fn lean_system_platform_windows(_unit: Obj) -> u8 {
        0
    }

    /// `lean_system_platform_osx`.
    #[no_mangle]
    pub extern "C" fn lean_system_platform_osx(_unit: Obj) -> u8 {
        0
    }

    /// `lean_system_platform_emscripten`.
    #[no_mangle]
    pub extern "C" fn lean_system_platform_emscripten(_unit: Obj) -> u8 {
        0
    }

    /// `lean_get_githash`.
    #[no_mangle]
    pub extern "C" fn lean_get_githash(_unit: Obj) -> Obj {
        crate::lean_runtime::string::from_bytes_unchecked(
            LEAN_GITHASH.as_bytes(),
            LEAN_GITHASH.len(),
        )
    }

    /// `lean_io_get_random_bytes`.
    #[no_mangle]
    pub extern "C" fn lean_io_get_random_bytes(n: usize) -> Obj {
        random_bytes(n)
    }

    fn no_file_system(what: &[u8]) -> Obj {
        crate::lean_runtime::io_result_mk_error(unsupported_operation(ENOSYS, what))
    }

    /// `lean_io_create_tempfile`: fails, the kernel image has no file system.
    #[no_mangle]
    pub extern "C" fn lean_io_create_tempfile(_unit: Obj) -> Obj {
        no_file_system(b"the kernel image has no file system to create a temporary file in")
    }

    /// `lean_io_create_tempdir`: fails, the kernel image has no file system.
    #[no_mangle]
    pub extern "C" fn lean_io_create_tempdir(_unit: Obj) -> Obj {
        no_file_system(b"the kernel image has no file system to create a temporary directory in")
    }

    /// `lean_option_get_or_block`.
    #[no_mangle]
    pub extern "C" fn lean_option_get_or_block(opt: Obj) -> Obj {
        // SAFETY: an owned option.
        unsafe { option_get_or_block(opt) }
    }

    /// `lean_float_to_string`: fail-closed.
    #[no_mangle]
    pub extern "C" fn lean_float_to_string(_a: f64) -> Obj {
        fatal("Float.toString: the kernel performs no floating-point formatting")
    }

    /// `lean_float32_to_string`: fail-closed.
    #[no_mangle]
    pub extern "C" fn lean_float32_to_string(_a: f32) -> Obj {
        fatal("Float32.toString: the kernel performs no floating-point formatting")
    }

    /// `lean_float_scaleb`: fail-closed.
    #[no_mangle]
    pub extern "C" fn lean_float_scaleb(_a: f64, _b: Obj) -> f64 {
        fatal("Float.scaleB: the kernel performs no floating-point arithmetic")
    }

    /// `lean_float32_scaleb`: fail-closed.
    #[no_mangle]
    pub extern "C" fn lean_float32_scaleb(_a: f32, _b: Obj) -> f32 {
        fatal("Float32.scaleB: the kernel performs no floating-point arithmetic")
    }

    /// libm's `pow`, which `Float.pow` is: fail-closed.
    #[no_mangle]
    pub extern "C" fn pow(_a: f64, _b: f64) -> f64 {
        fatal("Float.pow: the kernel performs no floating-point arithmetic")
    }

    /// libm's `powf`, which `Float32.pow` is: fail-closed.
    #[no_mangle]
    pub extern "C" fn powf(_a: f32, _b: f32) -> f32 {
        fatal("Float32.pow: the kernel performs no floating-point arithmetic")
    }
}
