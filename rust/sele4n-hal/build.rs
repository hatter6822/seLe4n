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
fn main() {
    // AN8-B.5: scan boot.S for the legacy literal pattern on every target
    // (not gated on aarch64) so the regression check fires even in host
    // test builds. The scanner is a simple whitespace-tolerant substring
    // match to avoid pulling `regex` into the workspace build graph.
    scan_boot_s_for_legacy_mpidr_literal();

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
             (cpu.rs). See docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §11 AN8-B."
        );
    }
}
