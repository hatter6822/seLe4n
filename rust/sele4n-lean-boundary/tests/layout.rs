// SPDX-License-Identifier: GPL-3.0-or-later
// seLe4n  - A Lean Microkernel
// Copyright (C) 2026  Adam Hall
// This program comes with ABSOLUTELY NO WARRANTY.
// This is free software, and you are welcome to redistribute it
// under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE

//! **The compiled Lean places field `i` of a scalar-words context at offset
//! `8 · i`** — executed, in both directions, for both contexts.
//!
//! The HAL's side of the layout is a pair of constants it `const`-asserts
//! (`rust/sele4n-hal/src/ffi.rs`: 35 words / 288 bytes for `RegisterFile`, 66
//! words / 536 bytes for `FpContext`); the same numbers are the pins here,
//! and the object the compiled Lean builds is held to them.  Every word of
//! every context is distinct, so a word read from the wrong position fails.
//!
//! A same-size permutation on the Lean side alone (two fields of the
//! structure swapped, `word` and `ofWords` with them, which every proof
//! survives) fails `..._word_i_is_the_hals_word_i`: the HAL's word `i` lands
//! at offset `8 · i`, which the permuted `word i` no longer reads.

#![cfg(sele4n_lean_host_archive)]

use sele4n_lean_boundary::lean::Object;

/// `trap::TRAP_FRAME_CONTEXT_WORDS`, the HAL's `RegisterFile` word count.
const TRAP_CONTEXT_WORDS: usize = 35;
/// `fp_context::FP_CONTEXT_WORDS`, the HAL's `FpContext` word count.
const FP_CONTEXT_WORDS: usize = 66;
/// `lean.h`'s object header.
const HEADER_BYTES: usize = 8;

/// A distinct value for every word: the top bit set so no word is a small
/// number, and `i` both high and low.
fn distinct(words: usize) -> Vec<u64> {
    (0..words)
        .map(|i| 0x8000_0000_0000_0000 | ((i as u64) << 40) | (0x0123_4567 ^ i as u64))
        .collect()
}

fn assert_scalar_ctor_shape(o: &Object, words: usize) {
    assert!(!o.is_scalar());
    assert_eq!(o.tag(), 0, "constructor tag");
    assert_eq!(o.num_objs(), 0, "no object fields");
    assert_eq!(o.byte_size(), HEADER_BYTES + 8 * words, "allocated bytes");
}

// --------------------------------------------------------------------------
// RegisterFile
// --------------------------------------------------------------------------

/// Rust → Lean: an object built at the HAL's offsets reads, by `RegisterFile.word`
/// in the compiled Lean, as the HAL's words — `word i` is what was put at
/// `8 · i`, and nothing past the layout.
#[test]
fn trap_context_word_i_is_the_hals_word_i() {
    let words = distinct(TRAP_CONTEXT_WORDS);
    let o = Object::scalar_words(&words);
    assert_scalar_ctor_shape(&o, TRAP_CONTEXT_WORDS);
    for (i, word) in words.iter().enumerate() {
        assert_eq!(o.trap_context_word(i as u64), *word, "word {i}");
    }
    assert_eq!(o.trap_context_word(TRAP_CONTEXT_WORDS as u64), 0);
}

/// Rust → Lean → Rust: the save and restore conversions composed on an object
/// the HAL built answer an object with every word unchanged at its offset,
/// of the constructor's shape and size.
#[test]
fn trap_context_round_trips_through_the_kernels_conversions() {
    let words = distinct(TRAP_CONTEXT_WORDS);
    let o = Object::scalar_words(&words);
    let back = o.share().trap_context_round_trip();
    assert_scalar_ctor_shape(&back, TRAP_CONTEXT_WORDS);
    for (i, word) in words.iter().enumerate() {
        assert_eq!(back.u64_at(8 * i), *word, "word {i} after the round trip");
        assert_eq!(back.trap_context_word(i as u64), *word);
    }
}

/// Lean → Rust: an object the compiled Lean built (`RegisterFile.ofWords`)
/// holds word `i` at offset `8 · i`, where the HAL reads it, and is exactly
/// the HAL's 288 bytes — the direction that needs no object Rust wrote.
#[test]
fn trap_context_the_lean_side_built_reads_at_the_hals_offsets() {
    let seed = 0x5EED_0000_0000_1000;
    let o = Object::trap_context_of_seed(seed);
    assert_scalar_ctor_shape(&o, TRAP_CONTEXT_WORDS);
    for i in 0..TRAP_CONTEXT_WORDS {
        assert_eq!(o.u64_at(8 * i), seed + (i as u64) * 0x0101, "word {i}");
    }
}

/// The `Option RegisterFile` encoding `ffiTrapContext` answers: `none` is the
/// boxed scalar `0`, `some c` a tag-1 constructor with one object field
/// holding `c` — and the compiled Lean reads `c`'s words through it.
#[test]
fn option_trap_context_is_decoded_as_the_hal_encodes_it() {
    let none = Object::none();
    assert!(none.is_scalar());
    assert_eq!(none.option_trap_context_word(0), u64::MAX);
    let words = distinct(TRAP_CONTEXT_WORDS);
    let some = Object::scalar_words(&words).some();
    assert!(!some.is_scalar());
    assert_eq!(some.tag(), 1);
    assert_eq!(some.num_objs(), 1);
    for (i, word) in words.iter().enumerate() {
        assert_eq!(some.option_trap_context_word(i as u64), *word, "word {i}");
    }
}

// --------------------------------------------------------------------------
// FpContext
// --------------------------------------------------------------------------

/// Rust → Lean, for the 66-word FP/SIMD context.
#[test]
fn fp_context_word_i_is_the_hals_word_i() {
    let words = distinct(FP_CONTEXT_WORDS);
    let o = Object::scalar_words(&words);
    assert_scalar_ctor_shape(&o, FP_CONTEXT_WORDS);
    for (i, word) in words.iter().enumerate() {
        assert_eq!(o.fp_context_word(i as u64), *word, "word {i}");
    }
    assert_eq!(o.fp_context_word(FP_CONTEXT_WORDS as u64), 0);
}

/// Rust → Lean → Rust: `FpContext.ofWords` on `FpContext.word` of an object
/// the HAL built answers an object with every word unchanged at its offset.
#[test]
fn fp_context_round_trips_through_the_kernels_conversions() {
    let words = distinct(FP_CONTEXT_WORDS);
    let o = Object::scalar_words(&words);
    let back = o.share().fp_context_round_trip();
    assert_scalar_ctor_shape(&back, FP_CONTEXT_WORDS);
    for (i, word) in words.iter().enumerate() {
        assert_eq!(back.u64_at(8 * i), *word, "word {i} after the round trip");
        assert_eq!(back.fp_context_word(i as u64), *word);
    }
}

/// Lean → Rust: an object the compiled Lean built holds word `i` at `8 · i`
/// and is exactly the HAL's 536 bytes.
#[test]
fn fp_context_the_lean_side_built_reads_at_the_hals_offsets() {
    let seed = 0x5EED_0000_0000_2000;
    let o = Object::fp_context_of_seed(seed);
    assert_scalar_ctor_shape(&o, FP_CONTEXT_WORDS);
    for i in 0..FP_CONTEXT_WORDS {
        assert_eq!(o.u64_at(8 * i), seed + (i as u64) * 0x0101, "word {i}");
    }
}

/// The two contexts are not confusable by size: the sizes the HAL refuses
/// each other on differ, and neither is the other's.
#[test]
fn the_two_contexts_differ_in_size() {
    let trap = Object::trap_context_of_seed(1);
    let fp = Object::fp_context_of_seed(1);
    assert_eq!(trap.byte_size(), 288);
    assert_eq!(fp.byte_size(), 536);
}
