// SPDX-License-Identifier: GPL-3.0-or-later
// seLe4n  - A Lean Microkernel
// Copyright (C) 2026  Adam Hall
// This program comes with ABSOLUTELY NO WARRANTY.
// This is free software, and you are welcome to redistribute it
// under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE

//! **The boundary-layout test's host side**: the compiled Lean kernel, its
//! toolchain runtime and the test-only probes of
//! `SeLe4n/Testing/BoundaryProbes.lean`, reachable from a Rust test.
//!
//! The two contexts that cross the Lean boundary whole — the general-purpose
//! `SeLe4n.RegisterFile` (35 `UInt64` fields) and the FP/SIMD `FpContext`
//! (66) — are read and written by the HAL at scalar offset `8 · i` for field
//! `i` (`rust/sele4n-hal/src/ffi.rs`, `scalar_words_to_lean` /
//! `scalar_words_of_lean`).  The Lean proofs (`RegisterFile.word_ofWords`,
//! `FpContext.word_ofWords`) pin that declared position `i` is layout word
//! `i`, and the HAL's exact-size refusal catches a field added or removed on
//! one side; neither reaches a same-size permutation applied consistently on
//! one side, or a compiler that lays scalar fields out other than in
//! declaration order.  `tests/layout.rs` executes that: an object built here
//! at the HAL's offsets is read by the compiled Lean's `word`, and an object
//! the compiled Lean built is read back here at the same offsets.
//!
//! Objects are built with the toolchain's own `lean.h` operations
//! (`shim.c`), not the HAL's runtime: the test is of the compiled Lean against
//! `lean.h`'s offsets, which the HAL's runtime reproduces byte for byte and
//! its own tests hold it to.
//!
//! Without the compiled archives (`cfg(sele4n_lean_host_archive)` unset, see
//! `build.rs`) this module is empty and the test fails, naming what is
//! missing.

// The HAL's unsafe-documentation discipline, enforced by the same front-ends:
// every `unsafe` block carries a `// SAFETY:` comment and every unsafe
// declaration a `# Safety` section.
#![deny(unsafe_op_in_unsafe_fn)]
#![deny(clippy::undocumented_unsafe_blocks)]
#![deny(clippy::missing_safety_doc)]

#[cfg(sele4n_lean_host_archive)]
pub mod lean {
    use std::ffi::c_void;
    use std::sync::Once;

    /// An opaque `lean_object *`.
    type RawObj = *mut c_void;

    extern "C" {
        // shim.c — the toolchain's object operations.
        /// # Safety
        ///
        /// Call once per process, before any other entry here; it runs the
        /// runtime's own start-up sequence.
        fn sele4n_boundary_initialize() -> i32;
        /// # Safety
        ///
        /// `scalar_bytes` must be below `lean.h`'s `LEAN_MAX_CTOR_SCALARS_SIZE`;
        /// the runtime must be initialised.  The object answered is owned by the
        /// caller.
        fn sele4n_boundary_alloc_scalar_ctor(scalar_bytes: u32) -> RawObj;
        /// # Safety
        ///
        /// `o` must be a live constructor with no object fields whose scalar
        /// area holds `[offset, offset + 8)`.
        fn sele4n_boundary_ctor_set_u64(o: RawObj, offset: u32, v: u64);
        /// # Safety
        ///
        /// `o` must be a live constructor with no object fields whose scalar
        /// area holds `[offset, offset + 8)`.
        fn sele4n_boundary_ctor_get_u64(o: RawObj, offset: u32) -> u64;
        /// # Safety
        ///
        /// `o` must be a live heap object.
        fn sele4n_boundary_tag(o: RawObj) -> u8;
        /// # Safety
        ///
        /// `o` must be a live constructor object.
        fn sele4n_boundary_num_objs(o: RawObj) -> u32;
        /// # Safety
        ///
        /// `o` must be a live heap object.
        fn sele4n_boundary_byte_size(o: RawObj) -> usize;
        /// # Safety
        ///
        /// Any object reference; nothing is dereferenced.
        fn sele4n_boundary_is_scalar(o: RawObj) -> bool;
        /// # Safety
        ///
        /// `n` must fit a boxed scalar (below `2^63`); nothing is allocated.
        fn sele4n_boundary_box(n: usize) -> RawObj;
        /// # Safety
        ///
        /// `v` must be an owned reference, which the cell answered takes over;
        /// the runtime must be initialised.
        fn sele4n_boundary_some(v: RawObj) -> RawObj;
        /// # Safety
        ///
        /// `o` must be a live heap object.
        fn sele4n_boundary_inc(o: RawObj);
        /// # Safety
        ///
        /// `o` must be an owned reference to a live heap object, which this
        /// call releases; it must not be used afterwards.
        fn sele4n_boundary_dec(o: RawObj);

        // SeLe4n/Testing/BoundaryProbes.lean — the compiled Lean.
        /// # Safety
        ///
        /// `c` must be an owned reference to a live `RegisterFile`, which the
        /// probe consumes; the module must be initialised.
        fn sele4n_probe_trap_context_word(c: RawObj, i: u64) -> u64;
        /// # Safety
        ///
        /// `c` must be an owned reference to a live `RegisterFile`, consumed;
        /// the object answered is owned by the caller.
        fn sele4n_probe_trap_context_round_trip(c: RawObj) -> RawObj;
        /// # Safety
        ///
        /// The module must be initialised; the object answered is owned by
        /// the caller.
        fn sele4n_probe_trap_context_of_seed(seed: u64) -> RawObj;
        /// # Safety
        ///
        /// The module must be initialised; the object answered is owned by
        /// the caller.
        fn sele4n_probe_in_flight_context_of_seed(seed: u64) -> RawObj;
        /// # Safety
        ///
        /// `c` must be an owned reference to a live `InFlightContext` and `rf`
        /// to a live `RegisterFile`, both consumed; the file answered is owned
        /// by the caller.
        fn sele4n_probe_snapshot_into(c: RawObj, rf: RawObj) -> RawObj;
        /// # Safety
        ///
        /// `c` must be an owned reference to a live `InFlightContext`,
        /// consumed; the file answered is owned by the caller.
        fn sele4n_probe_snapshot(c: RawObj) -> RawObj;
        /// # Safety
        ///
        /// `c` must be an owned reference to a live `Option RegisterFile` —
        /// the boxed scalar `0` or a tag-1 cell holding a `RegisterFile` —
        /// which the probe consumes.
        fn sele4n_probe_option_trap_context_word(c: RawObj, i: u64) -> u64;
        /// # Safety
        ///
        /// `c` must be an owned reference to a live `FpContext`, which the
        /// probe consumes; the module must be initialised.
        fn sele4n_probe_fp_context_word(c: RawObj, i: u64) -> u64;
        /// # Safety
        ///
        /// `c` must be an owned reference to a live `FpContext`, consumed; the
        /// object answered is owned by the caller.
        fn sele4n_probe_fp_context_round_trip(c: RawObj) -> RawObj;
        /// # Safety
        ///
        /// The module must be initialised; the object answered is owned by
        /// the caller.
        fn sele4n_probe_fp_context_of_seed(seed: u64) -> RawObj;
        /// # Safety
        ///
        /// The module must be initialised; the state answered is owned by the
        /// caller.
        fn sele4n_probe_save_state(tid: u64) -> RawObj;
        /// # Safety
        ///
        /// `st` must be an owned reference to a live `SystemState` and `c` to
        /// a live `InFlightContext`, both consumed; the state answered is
        /// owned by the caller.
        fn sele4n_probe_save_captured_syscall_frame(st: RawObj, c: RawObj) -> RawObj;
        /// # Safety
        ///
        /// `st` must be an owned reference to a live `SystemState`, which the
        /// probe consumes.
        fn sele4n_probe_saved_context_word(st: RawObj, tid: u64, i: u64) -> u64;
    }

    static RUNTIME: Once = Once::new();

    /// Initialise the Lean runtime and the probes module, once per process.
    /// Every entry below calls it first, so a test needs no setup.
    pub fn initialize() {
        RUNTIME.call_once(|| {
            // SAFETY: the runtime's documented start-up sequence, run once.
            let rc = unsafe { sele4n_boundary_initialize() };
            assert_eq!(rc, 0, "the Lean module initialisation refused");
        });
    }

    /// An owned Lean object reference, released on drop.
    pub struct Object(RawObj);

    impl Drop for Object {
        fn drop(&mut self) {
            // SAFETY: `self.0` is a reference this wrapper owns.
            unsafe { sele4n_boundary_dec(self.0) };
        }
    }

    impl Object {
        /// A constructor of `words.len()` `UInt64` fields — tag `0`, no
        /// object fields, `8 · words.len()` scalar bytes — holding `words[i]`
        /// at scalar offset `8 · i`: the shape and offsets the HAL writes
        /// (`ffi::scalar_words_to_lean`).
        #[must_use]
        pub fn scalar_words(words: &[u64]) -> Self {
            initialize();
            let scalar_bytes = u32::try_from(8 * words.len()).expect("a small object");
            // SAFETY: a fresh constructor with that many scalar bytes; each
            // offset written lies inside them.
            unsafe {
                let o = sele4n_boundary_alloc_scalar_ctor(scalar_bytes);
                for (i, word) in words.iter().enumerate() {
                    sele4n_boundary_ctor_set_u64(o, u32::try_from(8 * i).expect("offset"), *word);
                }
                Self(o)
            }
        }

        /// `some self`, in the `Option` encoding the HAL answers for
        /// `ffiTrapContext`: constructor tag `1` with one object field.
        #[must_use]
        pub fn some(self) -> Self {
            // SAFETY: `self` is handed over to the new cell, which owns it.
            let s = unsafe { sele4n_boundary_some(self.into_raw()) };
            Self(s)
        }

        /// `none`: `lean_box(0)`, a scalar.
        #[must_use]
        pub fn none() -> Self {
            initialize();
            // SAFETY: a boxed scalar is a valid object reference.
            Self(unsafe { sele4n_boundary_box(0) })
        }

        /// The `UInt64` at scalar offset `offset` — what the HAL reads with
        /// `ctor_get_u64`.
        #[must_use]
        pub fn u64_at(&self, offset: usize) -> u64 {
            // SAFETY: a live constructor; the caller's offset is inside its
            // scalar area by the test's construction.
            unsafe { sele4n_boundary_ctor_get_u64(self.0, u32::try_from(offset).expect("offset")) }
        }

        /// The constructor tag.
        #[must_use]
        pub fn tag(&self) -> u8 {
            // SAFETY: a live object.
            unsafe { sele4n_boundary_tag(self.0) }
        }

        /// The number of object fields.
        #[must_use]
        pub fn num_objs(&self) -> u32 {
            // SAFETY: a live constructor.
            unsafe { sele4n_boundary_num_objs(self.0) }
        }

        /// The bytes the runtime allocated for the object.
        #[must_use]
        pub fn byte_size(&self) -> usize {
            // SAFETY: a live object.
            unsafe { sele4n_boundary_byte_size(self.0) }
        }

        /// Whether the reference is a boxed scalar.
        #[must_use]
        pub fn is_scalar(&self) -> bool {
            // SAFETY: any reference.
            unsafe { sele4n_boundary_is_scalar(self.0) }
        }

        /// Overwrite the scalar word at byte `offset` in place, whoever else
        /// holds the object — what the HAL does to the per-core context
        /// object it reuses for the next trap.
        ///
        /// # Panics
        ///
        /// When the word would lie outside the object's scalar area.
        pub fn set_u64_at(&self, offset: usize, v: u64) {
            assert!(
                !self.is_scalar() && self.num_objs() == 0,
                "a scalar-only constructor"
            );
            assert!(
                offset.is_multiple_of(8) && offset + 8 <= self.byte_size() - 8,
                "offset {offset}"
            );
            // SAFETY: a live constructor with no object fields whose scalar
            // area holds the word at `offset` (checked above).
            unsafe {
                sele4n_boundary_ctor_set_u64(self.0, u32::try_from(offset).expect("offset"), v);
            }
        }

        /// A second owned reference to the same object.
        #[must_use]
        pub fn share(&self) -> Self {
            // SAFETY: a live object; the new reference is accounted for.
            unsafe { sele4n_boundary_inc(self.0) };
            Self(self.0)
        }

        fn into_raw(self) -> RawObj {
            let raw = self.0;
            std::mem::forget(self);
            raw
        }

        /// A reference for a probe to consume: every `@[export]` parameter
        /// is owned (a `@&` on one is ignored), so each call is handed its
        /// own counted reference and this wrapper keeps the object.
        fn handed_over(&self) -> RawObj {
            // SAFETY: a live object; the probe releases the reference.
            unsafe { sele4n_boundary_inc(self.0) };
            self.0
        }

        /// `RegisterFile.word self i`, read by the compiled Lean.
        #[must_use]
        pub fn trap_context_word(&self, i: u64) -> u64 {
            // SAFETY: the probe consumes the reference handed over.
            unsafe { sele4n_probe_trap_context_word(self.handed_over(), i) }
        }

        /// `RegisterFile.ofWords self.word`, a
        /// fresh object the compiled Lean built.
        #[must_use]
        pub fn trap_context_round_trip(self) -> Self {
            // SAFETY: the probe consumes its argument and answers an owned
            // object.
            Self(unsafe { sele4n_probe_trap_context_round_trip(self.into_raw()) })
        }

        /// `RegisterFile.ofWords fun i => seed + i · 0x0101`, built by the
        /// compiled Lean.
        #[must_use]
        pub fn trap_context_of_seed(seed: u64) -> Self {
            initialize();
            // SAFETY: an owned object is answered.
            Self(unsafe { sele4n_probe_trap_context_of_seed(seed) })
        }

        /// An in-flight context built by the Lean side: word `i` is
        /// `seed + i · 0x0101` (`inFlightContextOfSeed`).
        #[must_use]
        pub fn in_flight_context_of_seed(seed: u64) -> Self {
            initialize();
            // SAFETY: an owned object is answered.
            Self(unsafe { sele4n_probe_in_flight_context_of_seed(seed) })
        }

        /// `InFlightContext.snapshotInto self dest`: `self`'s words written
        /// into `dest`, which is consumed — in `dest`'s own object when this
        /// is its only reference.
        #[must_use]
        pub fn snapshot_into(&self, dest: Object) -> Self {
            // SAFETY: the probe consumes both references and answers an owned
            // file.
            Self(unsafe { sele4n_probe_snapshot_into(self.handed_over(), dest.into_raw()) })
        }

        /// `InFlightContext.snapshot self`: `self`'s words as a register file.
        #[must_use]
        pub fn snapshot(&self) -> Self {
            // SAFETY: the probe consumes the reference and answers an owned
            // file.
            Self(unsafe { sele4n_probe_snapshot(self.handed_over()) })
        }

        /// The object's address, to tell whether two references, held at
        /// different times, name one object.
        #[must_use]
        pub fn addr(&self) -> usize {
            self.0 as usize
        }

        /// Word `i` of an `Option RegisterFile`, or every bit set for `none`.
        #[must_use]
        pub fn option_trap_context_word(&self, i: u64) -> u64 {
            // SAFETY: the probe consumes the reference handed over.
            unsafe { sele4n_probe_option_trap_context_word(self.handed_over(), i) }
        }

        /// `FpContext.word self i`, read by the compiled Lean.
        #[must_use]
        pub fn fp_context_word(&self, i: u64) -> u64 {
            // SAFETY: the probe consumes the reference handed over.
            unsafe { sele4n_probe_fp_context_word(self.handed_over(), i) }
        }

        /// `FpContext.ofWords self.word`, a fresh object the compiled Lean
        /// built.
        #[must_use]
        pub fn fp_context_round_trip(self) -> Self {
            // SAFETY: the probe consumes its argument and answers an owned
            // object.
            Self(unsafe { sele4n_probe_fp_context_round_trip(self.into_raw()) })
        }

        /// `FpContext.ofWords fun i => seed + i · 0x0101`, built by the
        /// compiled Lean.
        #[must_use]
        pub fn fp_context_of_seed(seed: u64) -> Self {
            initialize();
            // SAFETY: an owned object is answered.
            Self(unsafe { sele4n_probe_fp_context_of_seed(seed) })
        }

        /// The save probe's state: thread `tid` current on the boot core,
        /// built by the compiled Lean.
        #[must_use]
        pub fn save_probe_state(tid: u64) -> Self {
            initialize();
            // SAFETY: an owned object is answered.
            Self(unsafe { sele4n_probe_save_state(tid) })
        }

        /// The syscall entry's save (`saveCapturedSyscallFrame`) of the
        /// context `c` on the boot core of the state `self`; `c` is handed a
        /// reference of its own, so the caller keeps the object.
        #[must_use]
        pub fn save_captured_syscall_frame(self, c: &Object) -> Self {
            // SAFETY: the probe consumes both references and answers an owned
            // state.
            Self(unsafe {
                sele4n_probe_save_captured_syscall_frame(self.into_raw(), c.handed_over())
            })
        }

        /// Word `i` of thread `tid`'s saved context in the state `self`, or
        /// every bit set when `tid` has no TCB.
        #[must_use]
        pub fn saved_context_word(&self, tid: u64, i: u64) -> u64 {
            // SAFETY: the probe consumes the reference handed over.
            unsafe { sele4n_probe_saved_context_word(self.handed_over(), tid, i) }
        }
    }
}
