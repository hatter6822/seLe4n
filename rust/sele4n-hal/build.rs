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

    // WS-SM SM1.F.8 (closes the SGI ordering contract): verify that
    // every send_sgi* function in `gic.rs` emits `dsb_ish` BEFORE the
    // GICD_SGIR write.  Without the DSB, prior kernel-state writes by
    // the sender are not guaranteed to be observable on the receiving
    // PE before the SGI fires — a hard-to-debug race that would only
    // manifest under heavy SMP load.  ARM ARM B2.7.5 mandates the
    // DSB; this scanner ensures the source still honours it.
    scan_gic_rs_send_sgi_emits_dsb_ish();

    // WS-SM SM1.I.1 (per-core IRQ handler contract): verify
    // `trap.rs::handle_irq_per_core` exists and routes through the
    // per-core stats record path.  SM5 will swap the assembly entry
    // vector from `handle_irq` to `handle_irq_per_core`; if a future
    // refactor removed or renamed the function, the SM5 swap would
    // fail at link time.  This scanner forces the contract earlier
    // (at elaboration) with an actionable diagnostic.
    scan_trap_rs_handle_irq_per_core_intact();

    // WS-SM SM2.D.5 (verified-lock FFI bridge contract): verify the
    // SM2.D lock-bridge module is present and every required FFI
    // export in `ffi.rs` resolves to a helper in `lock_bridge.rs`.
    // A refactor that dropped one of the SM2.D FFI exports would
    // silently break the Lean ↔ Rust bridge — the Lean side would
    // emit `@[extern]` declarations that resolve to nothing at link
    // time when the verified kernel hardware build pulls in the
    // HAL library.  Pinning the call sites at build time forces the
    // contract earlier (at elaboration) than the link-time failure
    // would surface it.
    scan_lock_bridge_rs_intact();
    scan_ffi_rs_exposes_lock_ffi_exports();

    // WS-SM SM2.E (closes the queued_rw_lock protocol contract):
    // verify that the mode-encoded four-state parked machine and the
    // stale-self tail detection are intact in `queued_rw_lock.rs`.
    // A refactor that re-introduces `AtomicBool` parked, drops any
    // of the four states (especially the WAITING_READER vs
    // WAITING_WRITER distinction that closes the stale-mode-read
    // race), or removes the stale-self check would re-open the
    // writer-readers exclusion panic that the Stream B protocol fix
    // closed.
    scan_queued_rw_lock_protocol_intact();

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

/// **WS-SM SM1.F.8** regression guard: verify every `send_sgi*` function
/// in `src/gic.rs` emits `crate::barriers::dsb_ish()` BEFORE the
/// `GICD_SGIR` write.
///
/// The SM1.F.8 contract is grounded in ARM ARM B2.7.5: writes prior
/// to a DSB are observed by all PEs in the IS domain before subsequent
/// operations.  When the sender writes GICD_SGIR (which triggers SGI
/// delivery on the receiver), the receiver's handler reads kernel-
/// state slots that the sender just wrote.  Without the DSB, those
/// writes may not be visible on the receiver yet, producing a
/// silent SMP correctness bug.
///
/// This scanner pins the textual presence of `dsb_ish()` and
/// `mmio_write32` calls in the three send_sgi* function bodies.  A
/// regression that removed the DSB would fail the build before any
/// SMP race could manifest.
///
/// Strategy: parse the source by section, locate each `pub fn
/// send_sgi*(...)` body, and verify that BOTH `dsb_ish()` and
/// `mmio_write32(GICD_BASE + gicd::SGIR` appear inside the body, in
/// that order.  We use a simple line-scan rather than a real AST
/// parser to avoid pulling `syn` into the build graph.
fn scan_gic_rs_send_sgi_emits_dsb_ish() {
    let path = "src/gic.rs";
    println!("cargo:rerun-if-changed={path}");
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => panic!("WS-SM SM1.F.8 scanner: failed to read {path}: {e}"),
    };

    // Strip `//` line comments so docstring mentions of "dsb_ish"
    // don't satisfy the check spuriously.
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

    // Locate each public function body and verify the ordering
    // contract.  We require:
    //   1. `pub fn send_sgi(`           — the explicit-mask variant
    //   2. `pub fn send_sgi_to_self(`   — self-only variant
    //   3. `pub fn send_sgi_to_all_but_self(`  — all-but-self variant
    //
    // For each body, we verify `crate::barriers::dsb_ish()` appears
    // BEFORE `mmio_write32(GICD_BASE + gicd::SGIR`.  We use simple
    // substring search within the function body slice.
    let required_fns: &[&str] = &[
        "pub fn send_sgi(",
        "pub fn send_sgi_to_self(",
        "pub fn send_sgi_to_all_but_self(",
    ];

    for fn_sig in required_fns {
        let Some(fn_start) = stripped.find(fn_sig) else {
            panic!(
                "WS-SM SM1.F.8 scanner: `{path}` no longer defines `{fn_sig}`.  \
                 The SGI primitive was renamed or removed.  Update the build \
                 scanner if intentional, otherwise restore the function."
            );
        };
        // Find the closing `}` of the function body.  We approximate
        // by scanning forward for the next `pub fn` (start of the
        // next function) or end of file, whichever comes first.
        let body_start = fn_start;
        let body_end = stripped[body_start + fn_sig.len()..]
            .find("\npub fn ")
            .map(|off| body_start + fn_sig.len() + off)
            .unwrap_or(stripped.len());
        let body = &stripped[body_start..body_end];

        // Check 1: `crate::barriers::dsb_ish()` must appear in the body.
        let dsb_pos = match body.find("crate::barriers::dsb_ish()") {
            Some(p) => p,
            None => panic!(
                "WS-SM SM1.F.8 regression: `{path}::{fn_sig}` body does NOT call \
                 `crate::barriers::dsb_ish()` before the GICD_SGIR write.  ARM ARM \
                 B2.7.5 requires a DSB before the SGIR write so prior kernel-state \
                 writes are observable on every IS-domain PE before the receiver's \
                 handler runs.  Restore the `crate::barriers::dsb_ish()` call \
                 immediately before `mmio_write32(GICD_BASE + gicd::SGIR, ...)`. \
                 See WS-SM SM1.F.8 in CHANGELOG.md."
            ),
        };

        // Check 2: `mmio_write32(GICD_BASE + gicd::SGIR` must appear AFTER the DSB.
        let sgir_write_pos = match body.find("mmio_write32(GICD_BASE + gicd::SGIR") {
            Some(p) => p,
            None => panic!(
                "WS-SM SM1.F.8 regression: `{path}::{fn_sig}` body does NOT write \
                 to `GICD_BASE + gicd::SGIR`.  The SGI primitive must produce an \
                 SGI by writing GICD_SGIR; a refactor that removed this write \
                 would break the entire SGI subsystem.  See WS-SM SM1.F."
            ),
        };

        if dsb_pos >= sgir_write_pos {
            panic!(
                "WS-SM SM1.F.8 regression: `{path}::{fn_sig}` body has the DSB \
                 AFTER the GICD_SGIR write.  The DSB must precede the write so \
                 prior kernel-state writes are visible on every IS-domain PE \
                 before the receiver's handler reads them.  See ARM ARM B2.7.5 \
                 and WS-SM SM1.F.8."
            );
        }
    }
}

/// **WS-SM SM1.I.1**: verify `trap.rs::handle_irq_per_core` is intact.
///
/// SM1.I.1 adds the per-core IRQ handler entry as the SM5 landing seam
/// — SM5 will redirect `trap.S`'s IRQ assembly entry from `handle_irq`
/// to `handle_irq_per_core`.  This scanner forces the contract at
/// elaboration time:
///
///   1. The function `pub extern "C" fn handle_irq_per_core` exists
///      (a regression that removed or renamed it would fail SM5's
///      assembly swap at link time; we catch it earlier).
///   2. The `#[no_mangle]` attribute is preserved (otherwise the
///      assembly entry cannot resolve the symbol at link time).
///   3. The body invokes `crate::per_cpu_stats::record_irq_dispatch`
///      so per-core IRQ attribution is wired (this is the
///      substantive SM1.I.1 contract; a refactor that dropped the
///      counter increment would silently break SM5+ per-core
///      diagnostics).
///   4. The body invokes
///      `crate::per_cpu::current_core_id_from_tpidr` so the
///      [core N] log prefix correctly identifies the calling core.
fn scan_trap_rs_handle_irq_per_core_intact() {
    let path = "src/trap.rs";
    println!("cargo:rerun-if-changed={path}");
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => panic!("WS-SM SM1.I.1 scanner: failed to read {path}: {e}"),
    };

    // Strip `//` line comments so docstring mentions of these symbols
    // don't satisfy the check spuriously.
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

    // Check 1: the function signature is present.
    let fn_sig = "pub extern \"C\" fn handle_irq_per_core(";
    let Some(fn_start) = stripped.find(fn_sig) else {
        panic!(
            "WS-SM SM1.I.1 regression: `{path}` no longer defines \
             `pub extern \"C\" fn handle_irq_per_core(...)`.  This is the \
             SM5 landing seam — SM5 will redirect `trap.S`'s IRQ entry to \
             this function.  Restore the function or update the scanner if \
             SM5 has landed and the contract changed."
        );
    };

    // Find the body — scan forward for the next `\npub ` (start of
    // next public item) or end of file.
    let body_start = fn_start;
    let body_end = stripped[body_start + fn_sig.len()..]
        .find("\npub ")
        .map(|off| body_start + fn_sig.len() + off)
        .unwrap_or(stripped.len());
    let body = &stripped[body_start..body_end];

    // Check 2: `#[no_mangle]` attribute precedes the function.  We
    // look in the 200 bytes BEFORE `fn_start` for the attribute.
    let preamble_start = fn_start.saturating_sub(200);
    let preamble = &stripped[preamble_start..fn_start];
    if !preamble.contains("#[no_mangle]") {
        panic!(
            "WS-SM SM1.I.1 regression: `{path}::handle_irq_per_core` no longer \
             has the `#[no_mangle]` attribute.  Without it, the assembly entry \
             vector (SM5 will redirect to this function) cannot resolve the \
             symbol at link time.  Restore `#[no_mangle]` immediately above the \
             function declaration."
        );
    }

    // Check 3: per-core stats record path.
    if !body.contains("crate::per_cpu_stats::record_irq_dispatch") {
        panic!(
            "WS-SM SM1.I.1 regression: `{path}::handle_irq_per_core` no longer \
             invokes `crate::per_cpu_stats::record_irq_dispatch`.  Per-core IRQ \
             attribution is the substantive SM1.I.1 contract — a refactor that \
             dropped the counter increment would silently break SM5+ per-core \
             diagnostics.  Restore the `record_irq_dispatch` call (it must run \
             unconditionally for every dispatched IRQ)."
        );
    }

    // Check 4: TPIDR_EL1 per-core identification.
    if !body.contains("crate::per_cpu::current_core_id_from_tpidr") {
        panic!(
            "WS-SM SM1.I.1 regression: `{path}::handle_irq_per_core` no longer \
             reads `crate::per_cpu::current_core_id_from_tpidr()`.  The per-core \
             handler must identify its calling core for the [core N] log prefix \
             and for SM5+ per-core scheduler dispatch.  Restore the TPIDR_EL1 \
             read at the top of the function body."
        );
    }
}

/// WS-SM SM2.D.5: Verify `lock_bridge.rs` defines every required
/// helper function with its expected `pub fn` declaration.
///
/// A regression that drops or renames any helper would silently break
/// the Lean ↔ Rust bridge: the corresponding `ffi.rs` export would
/// fail to resolve at compile time (caught), but if the export is
/// also dropped concurrently the breakage would only surface at the
/// verified kernel hardware build's link step.  This scanner forces
/// the contract at elaboration time so contributors see the failure
/// immediately during `cargo build`.
fn scan_lock_bridge_rs_intact() {
    let path = "src/lock_bridge.rs";
    println!("cargo:rerun-if-changed={path}");
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => panic!("WS-SM SM2.D.5 scanner: failed to read {path}: {e}"),
    };

    // Strip line comments so docstring mentions don't satisfy checks.
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

    // The 16 required public helpers in `lock_bridge.rs` that the
    // SM2.D FFI exports forward to.  Plus the build anchor constant.
    let required = [
        "pub const STATIC_TICKET_LOCK_POOL_SIZE: usize",
        "pub const STATIC_RW_LOCK_POOL_SIZE: usize",
        "pub static STATIC_TICKET_LOCK_POOL:",
        "pub static STATIC_RW_LOCK_POOL:",
        // SM2.D.4 trace counters: per-pool-slot atomic counters used
        // by the cross-core test (SM2.D.8) to verify FFI serialisation.
        // Each is `pub static` so a removal would fail the build (the
        // helper functions reference them).  Pinning the textual
        // presence here catches a refactor that drops them entirely.
        "pub static TICKET_LOCK_ACQUIRE_COUNT:",
        "pub static TICKET_LOCK_RELEASE_COUNT:",
        "pub static RW_LOCK_ACQUIRE_READ_COUNT:",
        "pub static RW_LOCK_RELEASE_READ_COUNT:",
        "pub static RW_LOCK_ACQUIRE_WRITE_COUNT:",
        "pub static RW_LOCK_RELEASE_WRITE_COUNT:",
        // SM2.D handle decoders.
        "pub const fn decode_ticket_lock_handle(",
        "pub const fn decode_rw_lock_handle(",
        // SM2.D.1 / SM2.D.2 / SM2.D.4 FFI helpers.
        "pub fn ticket_lock_static_handle(",
        "pub fn ticket_lock_acquire(",
        "pub fn ticket_lock_release(",
        "pub fn ticket_lock_peek_holder(",
        "pub fn ticket_lock_acquire_count(",
        "pub fn ticket_lock_release_count(",
        "pub fn rw_lock_static_handle(",
        "pub fn rw_lock_acquire_read(",
        "pub fn rw_lock_release_read(",
        "pub fn rw_lock_acquire_write(",
        "pub fn rw_lock_release_write(",
        "pub fn rw_lock_snapshot(",
        "pub fn rw_lock_acquire_read_count(",
        "pub fn rw_lock_release_read_count(",
        "pub fn rw_lock_acquire_write_count(",
        "pub fn rw_lock_release_write_count(",
        // SM2.D.7 theorem-count constant + build anchor.
        "pub const SM2_THEOREM_COUNT: usize = 22",
        "pub const SM2D_BUILD_ANCHOR:",
    ];
    for needle in required {
        if !stripped.contains(needle) {
            panic!(
                "WS-SM SM2.D.5 regression: `{path}` no longer declares `{needle}`.  \
                 The SM2.D FFI bridge expects every lock-bridge helper to remain \
                 publicly available.  Restore the declaration or, if SM5+ has \
                 landed an architectural shift, update this scanner in lockstep \
                 with the `ffi.rs` exports and the Lean `@[extern]` declarations \
                 in `SeLe4n/Platform/FFI.lean`."
            );
        }
    }
}

/// WS-SM SM2.D.5: Verify `ffi.rs` exposes every required SM2.D FFI
/// `#[no_mangle] pub extern "C" fn` export.
///
/// Symmetric to `scan_lock_bridge_rs_intact`: catches a regression
/// where the helper exists in `lock_bridge.rs` but the FFI export
/// got dropped from `ffi.rs`.
fn scan_ffi_rs_exposes_lock_ffi_exports() {
    let path = "src/ffi.rs";
    println!("cargo:rerun-if-changed={path}");
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => panic!("WS-SM SM2.D.5 scanner: failed to read {path}: {e}"),
    };

    // Strip line comments.
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

    // Every SM2.D FFI export.  Lean's `@[extern "<symbol>"]` declarations
    // in `SeLe4n/Platform/FFI.lean` resolve against these exports at the
    // verified kernel hardware build's link step.
    let required_ffi_symbols = [
        "pub extern \"C\" fn ffi_ticket_lock_static_handle(",
        "pub extern \"C\" fn ffi_ticket_lock_acquire(",
        "pub extern \"C\" fn ffi_ticket_lock_release(",
        "pub extern \"C\" fn ffi_ticket_lock_peek_holder(",
        "pub extern \"C\" fn ffi_ticket_lock_acquire_count(",
        "pub extern \"C\" fn ffi_ticket_lock_release_count(",
        "pub extern \"C\" fn ffi_rw_lock_static_handle(",
        "pub extern \"C\" fn ffi_rw_lock_acquire_read(",
        "pub extern \"C\" fn ffi_rw_lock_release_read(",
        "pub extern \"C\" fn ffi_rw_lock_acquire_write(",
        "pub extern \"C\" fn ffi_rw_lock_release_write(",
        "pub extern \"C\" fn ffi_rw_lock_snapshot(",
        "pub extern \"C\" fn ffi_rw_lock_acquire_read_count(",
        "pub extern \"C\" fn ffi_rw_lock_release_read_count(",
        "pub extern \"C\" fn ffi_rw_lock_acquire_write_count(",
        "pub extern \"C\" fn ffi_rw_lock_release_write_count(",
    ];
    for needle in required_ffi_symbols {
        if !stripped.contains(needle) {
            panic!(
                "WS-SM SM2.D.5 regression: `{path}` no longer declares `{needle}`.  \
                 The verified-kernel hardware build expects every SM2.D FFI \
                 export to remain reachable via `#[no_mangle] pub extern \"C\"`.  \
                 If you removed the export deliberately, also remove the \
                 corresponding `@[extern]` declaration in \
                 `SeLe4n/Platform/FFI.lean`, the helper in \
                 `src/lock_bridge.rs`, and the scanner entry above (in lockstep)."
            );
        }
    }
}

/// **WS-SM SM2.E** (closes the queued_rw_lock protocol contract): verify
/// that `queued_rw_lock.rs` retains the protocol invariants Stream A
/// + Stream B established to eliminate the documented hangs and the
///   residual writer-readers exclusion panic.
///
/// The scanner checks for THREE contractual patterns:
///
/// 1. **Mode-encoded four-state parked machine**: the four constants
///    `PARKED_NOT_IN_QUEUE`, `PARKED_WAITING_READER`,
///    `PARKED_WAITING_WRITER`, `PARKED_ADMITTED` must all be defined.
///    A regression that collapses WAITING_READER and WAITING_WRITER
///    back to a single WAITING re-opens the stale-mode-read race
///    that PR #790 commit-3 left unresolved — the walker would
///    consult `slot.mode` (Relaxed, race-prone) instead of the
///    atomic mode-encoded parked value.
///
/// 2. **Stale-self tail detection**: the literal
///    `if raw_prev_tail == core_id` must appear in BOTH
///    `acquire_read` and `acquire_write` (at least 2 occurrences in
///    the file).  Removing this detection re-opens the self-link
///    deadlock that PR #790 closed.
///
/// 3. **Writer admission via state-CAS (not fetch_or)**: the FORBIDDEN
///    `state.fetch_or(WRITER_BIT` pattern must NOT appear anywhere in
///    `signal_next_waiter` or in admission paths.  A regression that
///    re-introduces `fetch_or` for writer admission re-opens the
///    writer-readers coexistence race.
fn scan_queued_rw_lock_protocol_intact() {
    let path = "src/queued_rw_lock.rs";
    println!("cargo:rerun-if-changed={path}");
    let contents = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(_) => return,
    };

    // Strip comments to avoid false positives from documentation.
    // The state machine, like the other build scanners, uses a simple
    // line-based filter: lines starting with `//` (after trimming
    // whitespace) are dropped.  This is adequate for our needs — the
    // protocol contract uses constants and CAS calls in code, not in
    // comments.
    let mut stripped = String::new();
    for line in contents.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with("*") {
            continue;
        }
        stripped.push_str(line);
        stripped.push('\n');
    }

    // Check (1): four-state parked machine.
    let required_constants = [
        "pub const PARKED_NOT_IN_QUEUE: u8",
        "pub const PARKED_WAITING_READER: u8",
        "pub const PARKED_WAITING_WRITER: u8",
        "pub const PARKED_ADMITTED: u8",
    ];
    for needle in required_constants {
        if !stripped.contains(needle) {
            panic!(
                "WS-SM SM2.E protocol regression: `{path}` no longer defines `{needle}`.  \
                 The mode-encoded four-state parked machine is essential for \
                 the writer-readers exclusion invariant under cross-iteration \
                 stale-chain-link traversal.  Removing this constant re-opens \
                 the residual writer-readers panic that Stream B closed.  \
                 If you intend to restructure the parked machine, update the \
                 scanner in lockstep and verify the protocol still satisfies \
                 the SM2.A operational memory model's writer-readers exclusion \
                 invariant under stress test."
            );
        }
    }

    // Check (2): stale-self tail detection in both acquire paths.
    let stale_self_pattern = "if raw_prev_tail == core_id";
    let occurrences = stripped.matches(stale_self_pattern).count();
    if occurrences < 2 {
        panic!(
            "WS-SM SM2.E protocol regression: `{path}` no longer carries the \
             stale-self tail detection (`{stale_self_pattern}`) in both \
             `acquire_read` and `acquire_write`.  Found {occurrences} \
             occurrence(s); required: 2 (one per acquire path).  Removing \
             this detection re-opens the self-link deadlock that PR #790 \
             closed (10% → 0% hang rate).  If you intend to restructure \
             the acquire path, update this scanner in lockstep and verify \
             stress passes 100/100 iterations."
        );
    }

    // Check (3): forbidden fetch_or for writer admission.
    let forbidden_pattern = "self.state.fetch_or(WRITER_BIT";
    if stripped.contains(forbidden_pattern) {
        panic!(
            "WS-SM SM2.E protocol regression: `{path}` contains the forbidden \
             pattern `{forbidden_pattern}`.  Writer admission MUST use \
             `state.compare_exchange(0, WRITER_BIT)` — never `fetch_or` — \
             because `fetch_or` unconditionally sets the writer bit even when \
             reader bits are set, producing the `WRITER_BIT | reader_bits` \
             state that directly violates writer-readers exclusion.  If you \
             intend to use a different admission mechanism, ensure it preserves \
             the SM2.A invariant: every reachable state is in \
             {{0}} ∪ {{1..=READER_MASK}} ∪ {{WRITER_BIT}} — never the union with \
             `WRITER_BIT | non-zero-reader-bits`."
        );
    }
}
