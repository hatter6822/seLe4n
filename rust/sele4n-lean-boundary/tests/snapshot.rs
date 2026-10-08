// SPDX-License-Identifier: GPL-3.0-or-later
// seLe4n  - A Lean Microkernel
// Copyright (C) 2026  Adam Hall
// This program comes with ABSOLUTELY NO WARRANTY.
// This is free software, and you are welcome to redistribute it
// under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE

//! **The in-flight context's two copies, as compiled** (WS-CV CV3.2).
//!
//! `InFlightContext.snapshotInto` must write the context's words into the
//! register file it is handed, in that file's own object when it holds the
//! only reference — the property that lets the save allocate nothing — and
//! `snapshot` must answer a different object with the same words, so the state
//! never holds the core's in-flight object.

#![cfg(sele4n_lean_host_archive)]

use sele4n_lean_boundary::lean::Object;

/// `trap::TRAP_FRAME_CONTEXT_WORDS`, the register file's word count.
const TRAP_CONTEXT_WORDS: usize = 35;

fn words(o: &Object) -> Vec<u64> {
    (0..TRAP_CONTEXT_WORDS).map(|i| o.u64_at(8 * i)).collect()
}

#[test]
fn snapshot_into_writes_the_destination_it_owns() {
    let context = Object::in_flight_context_of_seed(0x1000);
    let dest = Object::trap_context_of_seed(0x9000);
    let dest_words = words(&dest);
    assert_ne!(words(&context), dest_words, "the two start apart");
    // The destination's only reference is handed over: written in place.
    let addr = dest.addr();
    let written = context.snapshot_into(dest);
    assert_eq!(
        written.addr(),
        addr,
        "an owned destination is written in place"
    );
    assert_eq!(
        words(&written),
        words(&context),
        "every word is the context's"
    );

    // A shared destination is not written: the answer is a new object and the
    // destination keeps its words.
    let shared = Object::trap_context_of_seed(0x9000);
    let copy = context.snapshot_into(shared.share());
    assert_ne!(copy.addr(), shared.addr(), "a shared destination is copied");
    assert_eq!(words(&copy), words(&context));
    assert_eq!(
        words(&shared),
        dest_words,
        "the shared destination is untouched"
    );
}

#[test]
fn snapshot_answers_a_new_object_with_the_same_words() {
    let context = Object::in_flight_context_of_seed(0x2000);
    let file = context.snapshot();
    assert_ne!(
        file.addr(),
        context.addr(),
        "the state never holds the in-flight object"
    );
    assert_eq!(words(&file), words(&context));
    // Rewriting the in-flight object leaves the snapshot alone.
    context.set_u64_at(0, 0xDEAD);
    assert_eq!(file.u64_at(0), 0x2000);
}
