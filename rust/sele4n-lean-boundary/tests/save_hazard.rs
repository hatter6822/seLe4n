// SPDX-License-Identifier: GPL-3.0-or-later
// seLe4n  - A Lean Microkernel
// Copyright (C) 2026  Adam Hall
// This program comes with ABSOLUTELY NO WARRANTY.
// This is free software, and you are welcome to redistribute it
// under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE

//! **The two-trap hazard, through the compiled save path.**
//!
//! Trap 1's context is saved into a thread by the syscall entry's save
//! (`saveCapturedSyscallFrame`, over `registerFileOfTrapContext`); trap 2's
//! words are then written into **the same object**, as the HAL does to a
//! per-core context it reuses; the thread's saved context is read back.
//!
//! Today the saved register file keeps the general-purpose registers as a
//! closure over the object, while `sp`, `pc`, `pstate` and `tpidr` (words
//! 31–34) are read when the file is built, so the read splits at word 31:
//! words 0–30 follow the object to trap 2, words 31–34 stay trap 1's.  This
//! test pins that split word for word — the witness of the hazard the
//! context-by-value workstream (WS-CV) removes; its CV3.4 flips the
//! post-overwrite assertion to every word equal to trap 1's.

#![cfg(sele4n_lean_host_archive)]

use sele4n_lean_boundary::lean::Object;

/// `trap::TRAP_FRAME_CONTEXT_WORDS`, the HAL's `TrapContext` word count.
const TRAP_CONTEXT_WORDS: usize = 35;
/// The first word the register file reads when it is built (`sp`), not
/// through the object.
const FIRST_EAGER_WORD: usize = 31;
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
fn a_saved_context_follows_the_reused_object_in_its_gprs_only() {
    let trap1 = Object::trap_context_of_seed(TRAP1_SEED);
    let trap1_words: Vec<u64> = (0..TRAP_CONTEXT_WORDS)
        .map(|i| trap1.u64_at(8 * i))
        .collect();
    assert!(
        trap1_words[33].is_multiple_of(16),
        "trap 1 is taken from EL0"
    );
    let trap2 = trap2_words();
    assert!(trap2[33].is_multiple_of(16), "trap 2 is taken from EL0");
    for (i, w) in trap2.iter().enumerate() {
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
    for (i, w) in trap1_words.iter().enumerate() {
        assert_eq!(
            st.saved_context_word(TID, i as u64),
            *w,
            "word {i} saved from trap 1"
        );
    }

    // Trap 2 arrives in the same object.
    for (i, w) in trap2.iter().enumerate() {
        trap1.set_u64_at(8 * i, *w);
    }

    for (i, (t1, t2)) in trap1_words.iter().zip(&trap2).enumerate() {
        let saved = st.saved_context_word(TID, i as u64);
        if i < FIRST_EAGER_WORD {
            assert_eq!(
                saved, *t2,
                "gpr word {i} reads the reused object (the hazard)"
            );
        } else {
            assert_eq!(saved, *t1, "word {i} was read when the file was built");
        }
    }
}
