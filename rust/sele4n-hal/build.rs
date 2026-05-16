// SPDX-License-Identifier: GPL-3.0-or-later
/// Build script for sele4n-hal: assembles ARM64 .S files via the `cc` crate.
///
/// Assembly sources:
/// - src/boot.S    — Boot entry point (_start, BSS zeroing, stack setup)
/// - src/vectors.S — ARM64 exception vector table (16 entries, 2048-byte aligned)
/// - src/trap.S    — Context save/restore macros and exception entry points
///
/// AN8-B.5 (H-18) regression guard: every build re-reads `src/boot.S` and
/// rejects the two-instruction literal encoding of `MPIDR_CORE_ID_MASK`
/// that AN8-B replaced. This prevents a future developer from "cleaning
/// up" the `adrp`+`ldr` pair back to `mov`/`movk` literals and losing the
/// single-source-of-truth property.
///
/// WS-SM SM1.B regression guard: every build re-reads `src/boot.S` and
/// verifies the `secondary_entry` block continues to reach the per-CPU
/// data block via the symbol-based `adrp`+`add` / `adrp`+`ldr` pattern
/// (against `PER_CPU_DATA` and `PER_CPU_DATA_SLOT_SIZE_SYM`).  If
/// either symbol reference disappears from `boot.S` while the
/// `msr tpidr_el1` write remains, the per-CPU base register would be
/// set to a stale or literal value at runtime — silently breaking
/// every secondary core's per-CPU lookup.  Catching this at
/// elaboration time (vs. link time) means the contributor sees the
/// diagnostic during `cargo build`, not during a downstream binary
/// link or QEMU boot.
fn main() {
    // AN8-B.5: scan boot.S for the legacy literal pattern on every target
    // (not gated on aarch64) so the regression check fires even in host
    // test builds. The scanner is a simple whitespace-tolerant substring
    // match to avoid pulling `regex` into the workspace build graph.
    scan_boot_s_for_legacy_mpidr_literal();

    // WS-SM SM1.B: verify the symbol-based PER_CPU_DATA setup is intact
    // in boot.S::secondary_entry. Runs on every target so the regression
    // check fires even in host test builds (the asm file is read, not
    // assembled, on non-aarch64).
    scan_boot_s_for_per_cpu_data_setup();

    // Only build assembly for aarch64 targets
    let target_arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    if target_arch != "aarch64" {
        return;
    }

    cc::Build::new()
        .file("src/boot.S")
        .file("src/vectors.S")
        .file("src/trap.S")
        .compile("sele4n_hal_asm");

    // Re-run build script if assembly files change
    println!("cargo:rerun-if-changed=src/boot.S");
    println!("cargo:rerun-if-changed=src/vectors.S");
    println!("cargo:rerun-if-changed=src/trap.S");
    println!("cargo:rerun-if-changed=link.ld");
    println!("cargo:rerun-if-changed=build.rs");
}

/// AN8-B.5 (H-18): Reject the legacy `mov x2, #0xFFFF ; movk x2, #0xFF, lsl #16`
/// pattern in `boot.S`.
///
/// We accept any whitespace (including newlines) between tokens, so formatting
/// changes still trigger the rejection. The match is case-insensitive on the
/// mnemonic to tolerate stylistic differences.
fn scan_boot_s_for_legacy_mpidr_literal() {
    let path = "src/boot.S";
    println!("cargo:rerun-if-changed={path}");
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            // Fail loudly if boot.S is missing — the rest of the build
            // would fail anyway.
            panic!("AN8-B.5 scanner: failed to read {path}: {e}");
        }
    };

    // Strip `//` line comments before scanning. Assembly comments must
    // not trigger the regression guard — we only care about live
    // instructions. Block comments `/* ... */` are not used in `boot.S`
    // and are therefore not stripped here; if the codebase ever adopts
    // them for assembly, extend this stripper.
    let stripped: String = contents
        .lines()
        .map(|line| {
            if let Some(idx) = line.find("//") { &line[..idx] } else { line }
        })
        .collect::<Vec<_>>()
        .join("\n");

    // Normalise whitespace: collapse ASCII whitespace to single spaces and
    // lowercase. This makes the match resilient to formatting changes.
    let normalised: String = stripped
        .chars()
        .map(|c| if c.is_ascii_whitespace() { ' ' } else { c.to_ascii_lowercase() })
        .collect();
    let mut deduped = String::with_capacity(normalised.len());
    let mut prev_space = false;
    for c in normalised.chars() {
        if c == ' ' {
            if !prev_space {
                deduped.push(c);
            }
            prev_space = true;
        } else {
            deduped.push(c);
            prev_space = false;
        }
    }

    // Legacy pattern (whitespace-normalised, lowercased):
    //   "mov x2, #0xffff" adjacent to "movk x2, #0xff, lsl #16".
    // We scan for the two literals as separate substrings to stay robust
    // against interleaving comments or labels. Both must be present to
    // flag a regression; matching either alone would false-positive on
    // benign uses of `#0xffff` elsewhere.
    let mov_lit = "mov x2, #0xffff";
    let movk_lit = "movk x2, #0xff, lsl #16";
    let has_mov = deduped.contains(mov_lit);
    let has_movk = deduped.contains(movk_lit);

    if has_mov && has_movk {
        // Emit a clear, actionable error. Cargo's build-script protocol
        // treats any panic as a build failure with the panic message
        // surfaced to the user.
        panic!(
            "AN8-B.5 (H-18) regression: `{path}` contains the legacy \
             literal encoding of MPIDR_CORE_ID_MASK. \
             Use `adrp`+`ldr` via `MPIDR_CORE_ID_MASK_SYM` instead \
             (cpu.rs).  See WS-AN AN8-B (historical record in \
             docs/WORKSTREAM_HISTORY.md)."
        );
    }
}

/// **WS-SM SM1.B** regression guard: verify `boot.S::secondary_entry`
/// continues to reach the per-CPU data block through the symbol-based
/// `adrp`/`add`/`ldr` pattern.
///
/// The SM0.N+SM1.B contract is:
///   1. `adrp` against `PER_CPU_DATA`   (load slot-zero page address)
///   2. `add` `:lo12:PER_CPU_DATA`      (resolve full address)
///   3. `adrp` against `PER_CPU_DATA_SLOT_SIZE_SYM` (load stride symbol)
///   4. `ldr [:lo12:PER_CPU_DATA_SLOT_SIZE_SYM]`   (resolve stride value)
///   5. `madd` to compute `slot_addr = PER_CPU_DATA + context_id * stride`
///   6. `msr tpidr_el1, ...`            (commit per-core base register)
///
/// If any of (1)..(4) disappear from `boot.S` while `tpidr_el1` is
/// still written, the per-CPU base would point at a stale / wrong
/// slot — every secondary core would dereference the same slot or
/// fault on a non-existent address.
///
/// The scanner is positive-existence: it verifies the symbol-based
/// pattern is present, not that no literal pattern exists.  This is
/// the strongest check that doesn't false-positive on benign asm
/// (e.g., `mov x5, #64` could appear in unrelated code).
fn scan_boot_s_for_per_cpu_data_setup() {
    let path = "src/boot.S";
    // Re-run hook already emitted by the AN8-B.5 scanner above; do
    // not double-emit (cargo allows it, but keeping the directives in
    // one place is cleaner).
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            panic!("WS-SM SM1.B scanner: failed to read {path}: {e}");
        }
    };

    // Strip `//` line comments before scanning so docstring mentions of
    // the symbol names do not satisfy the check spuriously.
    let stripped: String = contents
        .lines()
        .map(|line| {
            if let Some(idx) = line.find("//") {
                &line[..idx]
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join("\n");

    // Whitespace-tolerant lowercase substring match.  We do NOT collapse
    // adjacent spaces here (unlike the MPIDR scanner) because the
    // patterns we match are single tokens (`PER_CPU_DATA`,
    // `PER_CPU_DATA_SLOT_SIZE_SYM`) that are not whitespace-sensitive.
    let normalised = stripped.to_ascii_lowercase();

    // The two symbol references we require in boot.S.  Lowercase form
    // because asm files are case-insensitive on symbol names by GAS
    // convention (Rust links against the mangled-case form; `adrp`
    // matches case-sensitively, but the scanner is forgiving).
    let per_cpu_data_ref = "per_cpu_data";
    let slot_size_sym_ref = "per_cpu_data_slot_size_sym";
    let tpidr_write = "tpidr_el1, x"; // `msr tpidr_el1, xN` form

    let has_per_cpu_data = normalised.contains(per_cpu_data_ref);
    let has_slot_size_sym = normalised.contains(slot_size_sym_ref);
    let has_tpidr_write = normalised.contains(tpidr_write);

    // If `tpidr_el1` is written somewhere in boot.S but the symbol-based
    // setup is missing, that's a regression: the write would set
    // TPIDR_EL1 to whatever stale value happens to be in the source
    // register, silently breaking per-CPU lookups.
    if has_tpidr_write && (!has_per_cpu_data || !has_slot_size_sym) {
        panic!(
            "WS-SM SM1.B regression: `{path}` writes `tpidr_el1` but is \
             missing the symbol-based per-CPU data setup. \
             Expected `adrp`+`add` against `PER_CPU_DATA` (found: {pcd}) \
             and `adrp`+`ldr` against `PER_CPU_DATA_SLOT_SIZE_SYM` \
             (found: {sym}).  These references are required so the asm \
             reads the slot stride from `.rodata` (Rust constant) rather \
             than a hardcoded literal.  See WS-SM SM1.B (per_cpu.rs \
             module docstring; closes SMP-M4).",
            pcd = if has_per_cpu_data { "yes" } else { "MISSING" },
            sym = if has_slot_size_sym { "yes" } else { "MISSING" },
        );
    }
}
