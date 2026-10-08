// SPDX-License-Identifier: GPL-3.0-or-later
// seLe4n  - A Lean Microkernel
// Copyright (C) 2026  Adam Hall
// This program comes with ABSOLUTELY NO WARRANTY.
// This is free software, and you are welcome to redistribute it
// under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE

//! **The two-trap hazard, through the compiled save path.**
//!
//! Trap 1's context is saved into a thread by the syscall entry's save
//! (`saveCapturedSyscallFrame`); trap 2's context is a second object; the
//! thread's saved context is read back.
//!
//! Until WS-CV CV1.1 the saved register file kept the general-purpose
//! registers as a closure over the trap object, so a per-core object reused
//! for trap 2 would have rewritten trap 1's saved registers.  CV1.1 made the
//! save a copy into a new 35-word file; CV2.1 made the boundary type that file
//! itself, so the save stores the object it is handed — sound because the HAL
//! builds a fresh object per trap and keeps no reference (`ffi_trap_context`).
//! This test therefore pins the save over fresh objects: trap 1's words are
//! saved word for word, and trap 2's object reaches none of them.  CV3.1 is
//! the row that reuses one object per core, together with the copy that makes
//! reuse sound (`snapshotInto`), and CV3.4 restores the write-into-the-same-
//! object half of this test over it.

#![cfg(sele4n_lean_host_archive)]

use sele4n_lean_boundary::lean::Object;

/// `trap::TRAP_FRAME_CONTEXT_WORDS`, the register file's word count.
const TRAP_CONTEXT_WORDS: usize = 35;
/// The probe thread's id.
const TID: u64 = 7;
/// Trap 1's seed (`trapContextOfSeed`: word `i` is `seed + i · 0x0101`).  Its
/// low nibble is `0xF`, so word 33 (`pstate`, `0xF + 33 · 0x0101`) has a low
/// nibble of `0` — `EL0t`, a trap from a thread, which the save requires.
const TRAP1_SEED: u64 = 0x5EED_0000_0000_100F;

/// Trap 2's words: distinct from each other and from every word of trap 1
/// (the top nibble differs), `pstate` again from `EL0t`.
fn trap2_words() -> Vec<u64> {
    (0..TRAP_CONTEXT_WORDS)
        .map(|i| 0xA000_0000_0000_0000 | ((i as u64) << 32) | 0x0000_0000_C0DE_0000)
        .collect()
}

#[test]
fn a_saved_context_is_the_trap_it_was_saved_from() {
    let trap1 = Object::trap_context_of_seed(TRAP1_SEED);
    let trap1_words: Vec<u64> = (0..TRAP_CONTEXT_WORDS)
        .map(|i| trap1.u64_at(8 * i))
        .collect();
    assert!(
        trap1_words[33].is_multiple_of(16),
        "trap 1 is taken from EL0"
    );
    let trap2_expected = trap2_words();
    assert!(
        trap2_expected[33].is_multiple_of(16),
        "trap 2 is taken from EL0"
    );
    for (i, w) in trap2_expected.iter().enumerate() {
        assert!(
            !trap1_words.contains(w),
            "trap 2's word {i} is distinct from trap 1's"
        );
    }

    let st = Object::save_probe_state(TID);
    // Before the save the thread's context is the default, not trap 1's.
    assert_ne!(
        st.saved_context_word(TID, 0),
        trap1_words[0],
        "nothing saved yet"
    );
    let st = st.save_captured_syscall_frame(&trap1);
    drop(trap1);

    // Trap 2 arrives in a fresh object, as `ffi_trap_context` builds one.
    let trap2 = Object::trap_context_of_seed(0);
    for (i, w) in trap2_expected.iter().enumerate() {
        trap2.set_u64_at(8 * i, *w);
    }

    for (i, (t1, t2)) in trap1_words.iter().zip(&trap2_expected).enumerate() {
        let saved = st.saved_context_word(TID, i as u64);
        assert_eq!(trap2.u64_at(8 * i), *t2, "trap 2's word {i} is written");
        assert_eq!(saved, *t1, "word {i} is trap 1's, saved word for word");
    }
}
