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

    // WS-SM SM1.C.2 (closes SMP-C2 VBAR step): verify `boot.rs` and
    // `smp.rs` both route through the shared `install_exception_vectors`
    // helper instead of inlining a `write_vbar_el1` call.  A regression
    // that bypasses the helper would create a primary/secondary boot
    // asymmetry — the helper is the single source of truth for VBAR_EL1
    // initialisation order (write + dsb_sy + isb).
    scan_boot_rs_uses_install_exception_vectors();
    scan_smp_rs_uses_install_exception_vectors();

    // WS-SM SM1.C.5 (closes SMP-C2 full sequence): verify that the
    // secondary boot path in `smp.rs::rust_secondary_main` invokes
    // every required per-core init helper.  A future refactor that
    // accidentally drops one of MMU/VBAR/GIC/timer init would create
    // a partial-init secondary that silently violates the SMP-C2
    // contract.
    scan_smp_rs_invokes_secondary_init_helpers();

    // WS-SM SM1.C audit-pass-2: verify the asm-level context_id
    // defense in `boot.S::secondary_entry` is intact.  The asm
    // rejects out-of-range PSCI context_ids BEFORE the SP and
    // TPIDR_EL1 arithmetic uses them, preventing boot-core stack
    // corruption that the Rust-level validator alone cannot
    // prevent (the Rust validator runs after the function prologue).
    scan_boot_s_for_secondary_entry_context_id_validation();

    // WS-SM SM1.D (closes the DTB-cmdline / Phase-5 contract): verify
    // `boot.rs::rust_boot_main` actually invokes the SM1.D Phase-5
    // helpers (`cmdline::parse_cmdline_from_dtb` +
    // `cmdline::apply_cmdline_and_start_smp`).  A regression that
    // dropped Phase 5 would silently default to "no secondary cores"
    // because `smp::SMP_ENABLED` stays `false` at module load — the
    // production-vs-stub behaviour would diverge without any compile
    // error.  Pinning the call sites at build time forces the contract.
    scan_boot_rs_phase5_uses_cmdline();

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
            if let Some(idx) = line.find("//") {
                &line[..idx]
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join("\n");

    // Normalise whitespace: collapse ASCII whitespace to single spaces and
    // lowercase. This makes the match resilient to formatting changes.
    let normalised: String = stripped
        .chars()
        .map(|c| {
            if c.is_ascii_whitespace() {
                ' '
            } else {
                c.to_ascii_lowercase()
            }
        })
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

/// **WS-SM SM1.C.2** regression guard: verify `boot.rs::rust_boot_main`
/// routes through `install_exception_vectors()` instead of inlining a
/// `write_vbar_el1` call.
///
/// The SM1.C.2 contract is that the **same** code path installs the
/// EL1 exception vector table on every core (primary in `boot.rs`,
/// secondaries in `smp.rs::rust_secondary_main`).  A regression that
/// reintroduces an inline `crate::registers::write_vbar_el1(...)` call
/// in `boot.rs` would bypass the shared helper and could (intentionally
/// or otherwise) diverge the primary's barrier ordering from the
/// secondary's — silently creating a security asymmetry.
///
/// This scanner fails the build at the earliest point if `boot.rs`
/// either (a) writes `vbar_el1` without going through the helper, or
/// (b) loses the `install_exception_vectors()` call entirely.
fn scan_boot_rs_uses_install_exception_vectors() {
    let path = "src/boot.rs";
    println!("cargo:rerun-if-changed={path}");
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => panic!("WS-SM SM1.C.2 scanner: failed to read {path}: {e}"),
    };

    // Strip `//` line comments before scanning so docstring mentions of
    // the helper / register don't satisfy the check spuriously.
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
    let normalised = stripped.to_ascii_lowercase();

    // We require the helper call to exist in boot.rs (in non-comment
    // code).  Absence is a regression.
    let has_helper_call = normalised.contains("install_exception_vectors(");
    if !has_helper_call {
        panic!(
            "WS-SM SM1.C.2 regression: `{path}` no longer calls \
             `install_exception_vectors()`.  The primary boot path must \
             use the same VBAR_EL1 installation helper as \
             `smp.rs::rust_secondary_main` to keep boot-time exception \
             vector ordering symmetric between primary and secondary.  \
             See WS-SM SM1.C.2 (closes SMP-C2 VBAR step)."
        );
    }

    // Defense-in-depth: also reject a direct `write_vbar_el1` call in
    // `boot.rs` (allowing only the helper to make that call from
    // `install_exception_vectors`).  The helper itself lives in the
    // same file, so we count occurrences: exactly one
    // `write_vbar_el1(` is the helper body; more would indicate an
    // inlined-bypass.
    let write_count = normalised.matches("write_vbar_el1(").count();
    if write_count > 1 {
        panic!(
            "WS-SM SM1.C.2 regression: `{path}` has {} non-comment \
             references to `write_vbar_el1(` — only the body of \
             `install_exception_vectors` should call it directly.  \
             Other VBAR_EL1 writes must route through that helper to \
             preserve the primary/secondary symmetry.  See WS-SM SM1.C.2.",
            write_count
        );
    }
}

/// **WS-SM SM1.C.2** regression guard: verify `smp.rs::rust_secondary_main`
/// invokes `install_exception_vectors()` so secondaries install the
/// EL1 exception vectors via the shared helper.
fn scan_smp_rs_uses_install_exception_vectors() {
    let path = "src/smp.rs";
    println!("cargo:rerun-if-changed={path}");
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => panic!("WS-SM SM1.C.2 scanner: failed to read {path}: {e}"),
    };

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
    let normalised = stripped.to_ascii_lowercase();

    let has_helper_call = normalised.contains("install_exception_vectors(");
    if !has_helper_call {
        panic!(
            "WS-SM SM1.C.2 regression: `{path}` no longer calls \
             `install_exception_vectors()`.  Every secondary core must \
             install its EL1 exception vectors via the shared helper \
             so primary and secondary VBAR_EL1 setup stay symmetric.  \
             See WS-SM SM1.C.2 (closes SMP-C2 VBAR step)."
        );
    }
}

/// **WS-SM SM1.C.5** regression guard: verify
/// `smp.rs::rust_secondary_main` invokes every per-core init helper.
///
/// The SM1.C.5 contract is that the full secondary boot path must
/// initialise (in order):
///   1. MMU       — `mmu::init_mmu_secondary`
///   2. VBAR      — `boot::install_exception_vectors` (covered above)
///   3. GIC       — `gic::init_cpu_interface_secondary`
///   4. Timer     — `timer::init_timer_secondary`
///   5. IRQ unmask — `interrupts::enable_irq`
///   6. Lean kernel entry — `lean_secondary_kernel_main`
///
/// A regression that silently drops one of these steps would result
/// in a secondary core entering Lean without (e.g.) the MMU enabled
/// or the timer armed.  The build-script fires before any such
/// regression can be linked.
fn scan_smp_rs_invokes_secondary_init_helpers() {
    let path = "src/smp.rs";
    // Re-run hook already emitted above; not redoing here.
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => panic!("WS-SM SM1.C.5 scanner: failed to read {path}: {e}"),
    };

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
    let normalised = stripped.to_ascii_lowercase();

    // Required per-core init helpers.  Each entry is a (call site,
    // human-readable step name) pair so the diagnostic message names
    // exactly what's missing.
    //
    // Step 0 (`validate_secondary_context_id`) is the audit-pass-1
    // defense-in-depth gate that rejects out-of-range PSCI
    // context_ids before any per-core init runs.  A regression that
    // dropped this validator (e.g., refactor that reintroduces the
    // pre-audit raw `core_idx as usize` indexing) would bypass the
    // defense.  Pinning the call site here forces the contract.
    let required: &[(&str, &str)] = &[
        (
            "validate_secondary_context_id(",
            "Step 0: PSCI context_id defense-in-depth validation",
        ),
        ("init_mmu_secondary(", "Step 1: MMU enable"),
        ("init_cpu_interface_secondary(", "Step 3: GIC CPU interface"),
        ("init_timer_secondary(", "Step 4: Timer arm"),
        ("enable_irq(", "Step 5: IRQ unmask"),
        ("lean_secondary_kernel_main", "Step 6: Lean kernel entry"),
    ];

    let mut missing: Vec<&str> = Vec::new();
    for (call, step) in required {
        if !normalised.contains(call) {
            missing.push(step);
        }
    }

    if !missing.is_empty() {
        panic!(
            "WS-SM SM1.C.5 regression: `{path}::rust_secondary_main` is \
             missing one or more required per-core init steps.  Missing: \
             {missing:?}.  Each step must be invoked by name so a \
             refactor cannot accidentally short-circuit the boot path.  \
             See WS-SM SM1.C.5 (closes SMP-C2 full sequence)."
        );
    }
}

/// **WS-SM SM1.C audit-pass-2** regression guard: verify the
/// `boot.S::secondary_entry` asm rejects out-of-range PSCI context_ids
/// BEFORE the SP / TPIDR_EL1 setup uses them.
///
/// The audit-pass-2 contract is that every code path in
/// `secondary_entry` that uses `context_id` (x0) arithmetically must
/// be guarded by a prior bounds check.  Two textual checks codify
/// this:
///
///   1. The asm must reference `MAX_CORE_COUNT_SYM` (the upper-bound
///      symbol exposed from `smp.rs`).  Without this, the asm would
///      use a hardcoded literal `4` that could drift from
///      `MAX_SECONDARY_CORES + 1`.
///   2. The asm must contain a `.L_secondary_invalid` halt label
///      (the target of the rejection branches `cbz` and `b.hs`).
///
/// Without these, a malicious PSCI implementation passing
/// `context_id == 0` or `context_id >= 4` could:
///   * Alias a secondary's per-core state with the boot core's
///     `PerCpuData` slot (TPIDR_EL1 = PER_CPU_DATA + 0 = boot slot).
///   * Corrupt the boot core's stack (SP = stack_top - 3 * 64K =
///     `__smp_secondary_stacks_bottom`, adjacent to `.stack`).
///
/// The Rust-side `validate_secondary_context_id` provides a second
/// defense layer, but only catches the issue AFTER the function
/// prologue has run — too late to prevent the SP corruption.
fn scan_boot_s_for_secondary_entry_context_id_validation() {
    let path = "src/boot.S";
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            panic!("WS-SM SM1.C audit-pass-2 scanner: failed to read {path}: {e}");
        }
    };

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

    let normalised = stripped.to_ascii_lowercase();

    // We require the symbol reference (case-insensitive per GAS
    // convention) and the invalid-halt label.  The actual branch
    // instructions (`cbz`, `b.hs`) are not pinned by name because
    // alternative encodings (`cmp` + `b.eq` or `tbz`) are also valid;
    // the SYMBOL reference is the load-bearing structural pin.
    let max_core_count_ref = "max_core_count_sym";
    let invalid_label = ".l_secondary_invalid";

    let has_symbol = normalised.contains(max_core_count_ref);
    let has_label = normalised.contains(invalid_label);

    if !has_symbol || !has_label {
        panic!(
            "WS-SM SM1.C audit-pass-2 regression: `{path}::secondary_entry` \
             is missing the asm-level PSCI context_id defense.\n\
             Expected:\n\
             - reference to `MAX_CORE_COUNT_SYM` (Rust-side bound symbol; \
             found: {sym})\n\
             - `.L_secondary_invalid` halt label (target of the \
             rejection branches; found: {lbl})\n\
             Without these, a malformed `context_id` from PSCI could \
             corrupt the boot core's stack (the SP arithmetic in Step 2 \
             produces a SP inside `.stack` for `context_id == 4`).  See \
             WS-SM SM1.C audit-pass-2 in CHANGELOG.md.",
            sym = if has_symbol { "yes" } else { "MISSING" },
            lbl = if has_label { "yes" } else { "MISSING" },
        );
    }
}

/// **WS-SM SM1.D** regression guard: verify `boot.rs::rust_boot_main`
/// invokes the SM1.D Phase-5 cmdline-parse + SMP-bring-up entry points.
///
/// The SM1.D contract is that Phase 5 of `rust_boot_main`:
///   1. Parses the DTB-supplied bootargs via
///      `cmdline::parse_cmdline_from_dtb(dtb_ptr)`.
///   2. Applies the parsed config + brings up secondaries via
///      `cmdline::apply_cmdline_and_start_smp(&cmdline_cfg)`.
///
/// A regression that silently drops either call would result in:
///   - Either `SMP_ENABLED` stays at its module-load default
///     (`false`), and the kernel boots single-core even with no
///     `smp_enabled=false` cmdline override (silent disable).
///   - Or the parser runs but the bring-up never happens, so the
///     secondaries stay parked in `boot.S::.L_secondary_spin` forever.
///
/// Both failures are user-invisible without the cmdline scanner;
/// pinning them at build time forces the contract.
fn scan_boot_rs_phase5_uses_cmdline() {
    let path = "src/boot.rs";
    // Re-run hook already emitted by an earlier scanner; not duplicating.
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => panic!("WS-SM SM1.D scanner: failed to read {path}: {e}"),
    };

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
    let normalised = stripped.to_ascii_lowercase();

    // Required Phase-5 call sites.  Each entry is (call site, step name).
    let required: &[(&str, &str)] = &[
        (
            "cmdline::parse_cmdline_from_dtb(",
            "Phase 5 step 1: DTB cmdline parse",
        ),
        (
            "cmdline::apply_cmdline_and_start_smp(",
            "Phase 5 step 2: SMP bring-up dispatch",
        ),
    ];

    let mut missing: Vec<&str> = Vec::new();
    for (call, step) in required {
        if !normalised.contains(call) {
            missing.push(step);
        }
    }

    if !missing.is_empty() {
        panic!(
            "WS-SM SM1.D regression: `{path}::rust_boot_main` is missing \
             one or more required Phase 5 call sites.  Missing: \
             {missing:?}.  Phase 5 must (1) parse the DTB cmdline via \
             `cmdline::parse_cmdline_from_dtb` and (2) dispatch the SMP \
             bring-up via `cmdline::apply_cmdline_and_start_smp`.  \
             Without these, the kernel falls back to the module-load \
             default `SMP_ENABLED=false`, silently boots single-core, \
             and `smp_enabled=true` in the DTB bootargs has no effect.  \
             See WS-SM SM1.D in `docs/planning/SMP_RUST_HAL_PLAN.md` §5.4."
        );
    }
}
