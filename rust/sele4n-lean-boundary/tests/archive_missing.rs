// SPDX-License-Identifier: GPL-3.0-or-later
// seLe4n  - A Lean Microkernel
// Copyright (C) 2026  Adam Hall
// This program comes with ABSOLUTELY NO WARRANTY.
// This is free software, and you are welcome to redistribute it
// under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE

//! Without the compiled host Lean archives the layout test cannot link, and
//! it is not skipped: this one test fails, naming what to run.

#![cfg(not(sele4n_lean_host_archive))]

#[test]
fn the_boundary_layout_test_needs_the_compiled_lean_archives() {
    panic!(
        "sele4n-lean-boundary: the compiled host Lean archives or the Lean toolchain were not \
         found when this crate was built, so the boundary layout test did not run.  Run \
         `scripts/test_lean_boundary_layout.sh`, which builds `SeLe4n:static` and \
         `SeLe4nBoundaryProbes:static` and points the crate at them (SELE4N_LAKE_LIB_DIR, \
         SELE4N_LEAN_LIBDIR)."
    );
}
