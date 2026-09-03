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
    scan_boot_rs_calls_cmdline_smp_startup();

    // WS-SM SM1.F.8 (closes the SGI ordering contract): verify that
    // every send_sgi* function in `gic.rs` emits `dsb_ish` BEFORE the
    // GICD_SGIR write.  Without the DSB, prior kernel-state writes by
    // the sender are not guaranteed to be observable on the receiving
    // PE before the SGI fires — a hard-to-debug race that would only
    // manifest under heavy SMP load.  ARM ARM B2.7.5 mandates the
    // DSB; this scanner ensures the source still honours it.
    scan_gic_rs_send_sgi_emits_dsb_ish();

    // WS-SM SM1.I.1 / SM5 (per-core IRQ handler contract): verify
    // `trap.rs::handle_irq_per_core` exists and routes through the
    // per-core stats record path and the per-core CNTP ISR seam.  It is
    // the live IRQ path (`trap.S`'s IRQ vectors branch to it); if a
    // future refactor removed or renamed the function, the assembly
    // branch would fail at link time.  This scanner forces the contract
    // earlier (at elaboration) with an actionable diagnostic.
    scan_trap_rs_handle_irq_per_core_intact();

    // WS-SM SM5 (IRQ vector redirect contract): verify `trap.S`'s IRQ
    // vectors branch to `handle_irq_per_core` and that no vector still
    // branches to a bare `handle_irq` (the removed single-core legacy
    // entry).  A regression that re-pointed a vector at a handler
    // without the per-core scheduler seam would silently disconnect
    // the verified per-core timer tick and the `.reschedule` receiver
    // from the hardware IRQ path.
    scan_trap_s_irq_vector_redirect();

    // WS-SM SM5.C.5 (reschedule receiver contract): verify the
    // `.reschedule` SGI seam is intact end to end on the Rust side —
    // `trap.rs` defines the handler + its kernel-entry bracket, and
    // `boot.rs` registers it at boot.  A regression that dropped the
    // registration would silently demote every cross-core wake to
    // wake-on-next-tick (the SGI would land on the no-op table arm).
    scan_reschedule_sgi_seam_intact();

    // WS-SM (Lean-runtime readiness contract): verify every Rust seam
    // that calls into Lean consults the per-core readiness gate
    // (`lean_ready`) — the structural form of the constraint
    // shootdown.rs states in prose ("a reentrant per-core Lean runtime
    // … does not exist").  A regression that dropped a gate would let a
    // hand-built image enter the Lean runtime from a PE that never
    // initialized it — undefined behaviour at that PE's first
    // interrupt.
    scan_lean_ready_gates_intact();
    scan_lean_upcalls_readiness_gated();

    // WS-RR RR5.18: the two safety tripwires whose documented behaviour is a
    // clean halt were `debug_assert!`s, which a `--release` build — the way a
    // `kernel8.img` is built — compiles out.  Each is now a real branch to
    // `cpu::fatal_halt()`, and this scanner holds them to that.
    scan_release_surviving_tripwires();

    // WS-RR RR4.25 (single classification path): verify `trap.rs` routes
    // synchronous exceptions on the class the **Lean model** returns, and
    // does not re-derive one from a local `esr_ec` match.  Two
    // classifications that can drift is the defect this scanner exists to
    // keep closed: a drift on the abort arms would route a fault to the
    // wrong handler, or to none.
    scan_trap_rs_classifies_via_lean();
    scan_trap_rs_abort_fallback_halts();
    scan_trap_rs_faulted_outcome_halts();

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
    scan_ffi_rs_exposes_switch_to_thread_exports();

    // WS-SM SM5.I (commit-coupled shadow-clock contract): verify `ffi.rs`
    // still exposes the shadow-advance export the Lean tick entry's
    // committed clock advance resolves against, and that the timer ISR
    // has not regrown an invocation-time incrementer beside it (the
    // drift the commit-coupling exists to make impossible).
    scan_ffi_rs_exposes_timer_shadow_advance_export();

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

    // WS-RR RR1.4 (closes the FEAT_TLBIOS contract): verify every
    // outer-shareable TLBI wrapper in `tlb.rs` still fails closed on a
    // PE that does not implement FEAT_TLBIOS, and that each `*OS`
    // mnemonic is still bracketed by a balanced `.arch_extension`
    // pair.  Both properties are invisible to the host build — the
    // `asm!` blocks are `#[cfg(target_arch = "aarch64")]` — and a
    // dropped guard would turn a mis-declared `SharingDomain::Outer`
    // into an undefined-instruction trap on Cortex-A76 instead of a
    // diagnosed halt.  Runs on every target so the check fires in host
    // builds too.
    // The views come first: every scanner below reads them, so a
    // stripper defect would otherwise be reported as a clean tree.
    verify_rust_code_views();
    verify_lean_upcall_scanner();
    verify_handler_routing_scanner();
    verify_classifier_scanner();
    verify_abort_fallback_scanner();
    verify_faulted_outcome_scanner();
    scan_tlb_rs_outer_shareable_guards_intact();

    // Only build assembly for aarch64 targets
    let target_arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    if target_arch != "aarch64" {
        return;
    }

    let mut asm = cc::Build::new();
    // WS-RR RR1.6: pick an assembler that can actually target aarch64.
    // Left to its defaults, `cc` falls back to the host `cc` for
    // `aarch64-unknown-none` and hands three ARM64 sources to an x86
    // assembler — 54 "no such instruction" errors from `boot.S` alone,
    // before the build even reaches `vectors.S`, all of them describing
    // the toolchain rather than the code.
    select_cross_assembler(&mut asm);
    asm.file("src/boot.S")
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
    // Assembly grammar: `//` AND `/* */`, since the `.S` sources go
    // through the C preprocessor. See `asm_code_view`.
    let stripped = asm_code_view(&contents);

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
             docs/REGISTERED_DEBT.md)."
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
    // Assembly grammar: `//` AND `/* */`, since the `.S` sources go
    // through the C preprocessor. See `asm_code_view`.
    let stripped = asm_code_view(&contents);

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
    // Identifier questions read the STRING-BLANKED view: a name inside
    // a literal is a mention, not a call. See `rust_code_views`.
    let (_, stripped) = rust_code_views(&contents);
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

    // Identifier questions read the STRING-BLANKED view: a name inside
    // a literal is a mention, not a call. See `rust_code_views`.
    let (_, stripped) = rust_code_views(&contents);
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

    // Identifier questions read the STRING-BLANKED view: a name inside
    // a literal is a mention, not a call. See `rust_code_views`.
    let (_, stripped) = rust_code_views(&contents);
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
        (
            "lean_secondary_kernel_main",
            "Step 5: Lean kernel bring-up entry",
        ),
        (
            "with_kernel_entry(",
            "Step 5: kernel-entry bracket around the bring-up entry",
        ),
        ("enable_irq(", "Step 6: IRQ unmask"),
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

    // Assembly grammar: `//` AND `/* */`, since the `.S` sources go
    // through the C preprocessor. See `asm_code_view`.
    let stripped = asm_code_view(&contents);

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
fn scan_boot_rs_calls_cmdline_smp_startup() {
    let path = "src/boot.rs";
    // Re-run hook already emitted by an earlier scanner; not duplicating.
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => panic!("WS-SM SM1.D scanner: failed to read {path}: {e}"),
    };

    // Identifier questions read the STRING-BLANKED view: a name inside
    // a literal is a mention, not a call. See `rust_code_views`.
    let (_, stripped) = rust_code_views(&contents);
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
    // Identifier questions read the STRING-BLANKED view: a name inside
    // a literal is a mention, not a call. See `rust_code_views`.
    let (_, stripped) = rust_code_views(&contents);

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

/// **WS-SM SM1.I.1 / SM5**: verify `trap.rs::handle_irq_per_core` is
/// intact.
///
/// `handle_irq_per_core` is the live IRQ path — `trap.S`'s IRQ vectors
/// branch to it (the redirect the SM1.I.1 seam was staged for; pinned
/// by `scan_trap_s_irq_vector_redirect`).  This scanner forces the
/// contract at elaboration time:
///
///   1. The function `pub extern "C" fn handle_irq_per_core` exists
///      (a regression that removed or renamed it would fail the
///      assembly branch at link time; we catch it earlier).
///   2. The `#[no_mangle]` attribute is preserved (otherwise the
///      assembly entry cannot resolve the symbol at link time).
///   3. The body invokes `crate::per_cpu_stats::record_irq_dispatch`
///      so per-core IRQ attribution is wired (this is the
///      substantive SM1.I.1 contract; a refactor that dropped the
///      counter increment would silently break per-core
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
    // Identifier questions read the STRING-BLANKED view: a name inside
    // a literal is a mention, not a call. See `rust_code_views`.
    let (_, stripped) = rust_code_views(&contents);

    // Check 1: the function signature is present.
    let fn_sig = "pub extern \"C\" fn handle_irq_per_core(";
    let Some(fn_start) = stripped.find(fn_sig) else {
        panic!(
            "WS-SM SM1.I.1 regression: `{path}` no longer defines \
             `pub extern \"C\" fn handle_irq_per_core(...)`.  This is the \
             live IRQ path — `trap.S`'s IRQ vectors branch to it.  \
             Restore the function."
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
             vector (`trap.S`'s IRQ entries branch to this function) cannot \
             resolve the symbol at link time.  Restore `#[no_mangle]` \
             immediately above the function declaration."
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

    // Check 5: WS-SM SM5.D.1 — the timer branch drives the verified Lean
    // per-core scheduler timer tick via the per-core CNTP ISR seam.  A refactor
    // that drops this call (reverting the timer branch to a bare comparator
    // re-arm) would silently disconnect the per-core scheduler from its timer.
    if !body.contains("crate::timer::per_core_timer_tick_isr") {
        panic!(
            "WS-SM SM5.D.1 regression: `{path}::handle_irq_per_core`'s timer \
             branch no longer calls `crate::timer::per_core_timer_tick_isr(core_id)`. \
             This is the seam that drives the verified Lean per-core scheduler \
             timer tick (`Kernel.timerTickOnCore`).  Restore the call in the \
             `intid == TIMER_PPI_ID` branch."
        );
    }
}

/// **WS-SM SM5**: verify `trap.S`'s IRQ vectors branch to the per-core
/// IRQ handler.
///
/// The redirect from the single-core legacy entry to
/// `handle_irq_per_core` is what connects the hardware IRQ path to the
/// verified per-core scheduler (the SM5.D.1 timer-tick seam and the
/// SM5.C.5 `.reschedule` receiver both hang off the per-core handler's
/// dispatch closure).  Two textual checks codify the contract:
///
///   1. `bl handle_irq_per_core` appears at least twice (the EL0 and
///      EL1 IRQ vectors).
///   2. No `bl handle_irq` line targets anything other than
///      `handle_irq_per_core` — the single-core legacy entry was
///      removed with the redirect, so a bare `bl handle_irq` would be
///      an unresolved symbol reintroducing the pre-SM5 split brain.
fn scan_trap_s_irq_vector_redirect() {
    let path = "src/trap.S";
    println!("cargo:rerun-if-changed={path}");
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => panic!("WS-SM SM5 scanner: failed to read {path}: {e}"),
    };

    // Strip `//` line comments so prose mentions don't satisfy (or
    // trip) the checks.
    // Assembly grammar: `//` AND `/* */`, since the `.S` sources go
    // through the C preprocessor. See `asm_code_view`.
    let stripped = asm_code_view(&contents);

    let per_core_branches = stripped.matches("bl      handle_irq_per_core").count()
        + stripped.matches("bl handle_irq_per_core").count();
    if per_core_branches < 2 {
        panic!(
            "WS-SM SM5 regression: `{path}` must branch to \
             `handle_irq_per_core` from both IRQ vectors \
             (`__el0_irq_entry` and `__el1_irq_entry`); found \
             {per_core_branches} branch(es).  The per-core handler is \
             the seam that drives the verified per-core scheduler from \
             hardware IRQs."
        );
    }

    // A `bl handle_irq` token NOT followed by `_per_core` is the
    // removed legacy entry.
    for line in stripped.lines() {
        let Some(idx) = line.find("bl") else { continue };
        let target = line[idx + 2..].trim();
        if target == "handle_irq" {
            panic!(
                "WS-SM SM5 regression: `{path}` branches to the removed \
                 single-core `handle_irq`.  Both IRQ vectors must branch \
                 to `handle_irq_per_core`."
            );
        }
    }
}

/// **WS-SM SM5.C.5**: verify the `.reschedule` SGI receiver seam is
/// intact end to end on the Rust side.
///
///   1. `trap.rs` defines `reschedule_sgi_handler` and brackets its
///      Lean call (`lean_per_core_reschedule`) in
///      `kernel_entry::with_kernel_entry` — an unbracketed commit
///      racing another core's entry loses one transition whole.
///   2. `trap.rs` defines `register_reschedule_sgi_handler` (the
///      write-once boot registration wrapper).
///   3. `boot.rs` calls `register_reschedule_sgi_handler` — without
///      the registration, every cross-core wake silently demotes to
///      wake-on-next-tick (the SGI lands on the no-op table arm).
fn scan_reschedule_sgi_seam_intact() {
    let trap_path = "src/trap.rs";
    let boot_path = "src/boot.rs";
    let strip = |contents: &str| -> String {
        contents
            .lines()
            .map(|line| {
                if let Some(idx) = line.find("//") {
                    &line[..idx]
                } else {
                    line
                }
            })
            .collect::<Vec<_>>()
            .join("\n")
    };

    let trap = match std::fs::read_to_string(trap_path) {
        Ok(s) => strip(&s),
        Err(e) => panic!("WS-SM SM5.C.5 scanner: failed to read {trap_path}: {e}"),
    };
    let boot = match std::fs::read_to_string(boot_path) {
        Ok(s) => strip(&s),
        Err(e) => panic!("WS-SM SM5.C.5 scanner: failed to read {boot_path}: {e}"),
    };

    let Some(handler_start) = trap.find("fn reschedule_sgi_handler(") else {
        panic!(
            "WS-SM SM5.C.5 regression: `{trap_path}` no longer defines \
             `reschedule_sgi_handler`.  This is the receiver seam of the \
             cross-core wake protocol; restore the handler."
        );
    };
    let handler_end = trap[handler_start..]
        .find("\npub unsafe fn register_reschedule_sgi_handler")
        .map(|off| handler_start + off)
        .unwrap_or(trap.len());
    let handler_body = &trap[handler_start..handler_end];
    if !handler_body.contains("with_kernel_entry") {
        panic!(
            "WS-SM SM5.C.5 regression: `{trap_path}::reschedule_sgi_handler` \
             no longer brackets its Lean call in \
             `kernel_entry::with_kernel_entry`.  The reschedule commits \
             kernel state; an unbracketed commit racing another core's \
             entry loses one transition whole.  Restore the bracket."
        );
    }
    if !handler_body.contains("lean_per_core_reschedule") {
        panic!(
            "WS-SM SM5.C.5 regression: `{trap_path}::reschedule_sgi_handler` \
             no longer drives the Lean reschedule entry \
             (`lean_per_core_reschedule`).  Restore the hw_target-gated \
             call so the verified `handleRescheduleSgiOnCore` transition \
             runs on SGI receipt."
        );
    }
    if !trap.contains("pub unsafe fn register_reschedule_sgi_handler") {
        panic!(
            "WS-SM SM5.C.5 regression: `{trap_path}` no longer defines \
             `register_reschedule_sgi_handler`.  Restore the write-once \
             boot registration wrapper."
        );
    }
    if !boot.contains("register_reschedule_sgi_handler") {
        panic!(
            "WS-SM SM5.C.5 regression: `{boot_path}` no longer registers \
             the `.reschedule` SGI handler at boot (phase 3).  Without \
             the registration every cross-core wake silently demotes to \
             wake-on-next-tick.  Restore the \
             `crate::trap::register_reschedule_sgi_handler()` call."
        );
    }
}

/// **WS-SM**: verify every Rust seam that calls into the Lean runtime
/// consults the per-core readiness gate (`lean_ready::lean_ready`)
/// before its Lean call — **inside the seam function's own body, gate
/// before symbol** (PR #880 review round 2: a file-level containment
/// check would accept a gate parked in one function while another
/// function's Lean call runs ungated).
///
/// The three seams and the symbols they resolve:
///
///   1. `timer.rs::per_core_timer_tick_isr` → `lean_per_core_timer_tick`
///   2. `trap.rs::reschedule_sgi_handler`   → `lean_per_core_reschedule`
///   3. `smp.rs::rust_secondary_main`       → `lean_secondary_kernel_main`
///
/// For each seam the scanner extracts the named function's body (first
/// `fn <name>(` declaration through its brace-matched close, on the
/// comment-stripped text so prose mentions neither satisfy nor trip the
/// checks) and requires the first `lean_ready(` call to appear
/// **before** the first occurrence of the Lean symbol within that body.
/// A body carrying the symbol without a preceding gate is exactly the
/// regression this scanner exists to catch (a PE entering a Lean
/// runtime it never initialized — the constraint `shootdown.rs`
/// documents and `lean_ready.rs` enforces).
/// WS-RR RR4.25: verify `trap.rs` classifies synchronous exceptions through
/// the Lean model and nowhere else.
///
/// Three relations, not three token presences:
///
/// 1. `handle_synchronous_exception`'s body **matches on the value
///    `classify_synchronous_exception` returned** — checked by requiring both
///    the binding and the `match` on that binding, so a body that calls the
///    classifier and then ignores it fails.
/// 2. That body contains **no `ec::` constant at all**.  The routing arms are
///    the place a second classification would reappear, and it would reappear
///    looking exactly like the retired one: `ec::DABT_LOWER | ec::DABT_CURRENT
///    => …`.  Keeping the call and adding an `ec::` arm is the
///    mutation that a presence check would miss.
/// 3. The **hardware-gated** definition of `classify_synchronous_exception`
///    resolves `lean_classify_synchronous_exception`.  Checked by requiring
///    the `hw_target` cfg immediately above the first definition and the Lean
///    symbol inside that definition's brace-matched body — so a host mirror
///    promoted to the hardware target, or a hardware definition that stopped
///    calling Lean, both fail.
fn scan_trap_rs_classifies_via_lean() {
    let path = "src/trap.rs";
    println!("cargo:rerun-if-changed={path}");
    let raw = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => panic!("WS-RR RR4.25 scanner: failed to read {path}: {e}"),
    };
    // Comment-free, strings-blanked view: a scanner must not be satisfied — or
    // tripped — by the prose that explains it, nor by a mention of a symbol
    // inside a string literal.  The strings-kept view answers the one question
    // that *is* about a literal: the `#[cfg(feature = "hw_target")]` attribute.
    let (kept, stripped) = rust_code_views(&raw);

    fn body_after<'a>(stripped: &'a str, from: usize, what: &str) -> &'a str {
        let open_rel = stripped[from..].find('{').unwrap_or_else(|| {
            panic!("WS-RR RR4.25 scanner: `{what}` has no body block after its declaration.")
        });
        let body_start = from + open_rel;
        let mut depth = 0usize;
        for (i, ch) in stripped[body_start..].char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        return &stripped[body_start..body_start + i + 1];
                    }
                }
                _ => {}
            }
        }
        panic!("WS-RR RR4.25 scanner: unbalanced braces while extracting `{what}`.")
    }

    // (1) + (2): the router matches the Lean classification and nothing else.
    let handler_idx = stripped
        .find("fn handle_synchronous_exception(")
        .unwrap_or_else(|| {
            panic!(
                "WS-RR RR4.25 regression: `{path}` no longer declares \
                 `fn handle_synchronous_exception`."
            )
        });
    let handler_body = body_after(&stripped, handler_idx, "handle_synchronous_exception");
    if let Err(why) = handler_routing_status(handler_body) {
        panic!("{why} (`{path}`'s `handle_synchronous_exception`)");
    }

    // (3): the hardware-gated classifier calls into Lean — the *call*, behind
    // the readiness gate, with the pre-readiness mirror as the other branch.
    // PR #887 review round 2: the first cut accepted the symbol's presence,
    // which the `extern "C"` declaration inside the body satisfies on its own,
    // so deleting the call and returning a constant passed.  The declaration
    // is blanked before the call is looked for.
    let classifier_idx = stripped
        .find("fn classify_synchronous_exception(")
        .unwrap_or_else(|| {
            panic!(
                "WS-RR RR4.25 regression: `{path}` no longer declares \
                 `fn classify_synchronous_exception`."
            )
        });
    let preamble_start = classifier_idx.saturating_sub(120);
    if !kept[preamble_start..classifier_idx].contains("#[cfg(feature = \"hw_target\")]") {
        panic!(
            "WS-RR RR4.25 regression: in `{path}`, the first \
             `fn classify_synchronous_exception` is not the `hw_target` one.  The \
             hardware definition must come first so this scanner checks the live \
             path, and the host lane's must stay behind \
             `#[cfg(not(feature = \"hw_target\"))]`."
        );
    }
    let classifier_body = body_after(&stripped, classifier_idx, "classify_synchronous_exception");
    // …and the host lane classifies through the same mirror, so the table the
    // host tests pin is the table a not-ready core runs.
    let host_idx = stripped[classifier_idx + 1..]
        .find("fn classify_synchronous_exception(")
        .map(|i| classifier_idx + 1 + i)
        .unwrap_or_else(|| {
            panic!(
                "WS-RR RR4.25 regression: `{path}` has no host-lane \
                 `fn classify_synchronous_exception` after the hardware one."
            )
        });
    let host_body = body_after(&stripped, host_idx, "classify_synchronous_exception (host)");
    // PR #887 review round 6: the relation on both bodies — the hardware
    // classifier's value is the readiness conditional on the executing PE,
    // whose ready branch IS the Lean call and whose not-ready branch IS the
    // mirror call; the host classifier's value IS the mirror call.  Round 2
    // looked for the call after the gate and the mirror's presence anywhere,
    // which `else { let _ = mirror(esr); sync_class::SVC }` satisfied.
    if let Err(why) = classifier_status(classifier_body, host_body) {
        panic!("{why} (`{path}`)");
    }
}

/// PR #887 review round 6: **the classifier's branches are bound to their
/// values.**  The round-2 check proved the Lean call after the gate and the
/// mirror's presence *somewhere* in the hardware body, so
/// `else { let _ = classify_synchronous_exception_mirror(esr); sync_class::SVC }`
/// kept the token and routed every not-ready abort into the SVC path — and
/// the host classifier is a separate definition, so the mirror-table tests
/// never executed that branch.  On the hardware body (`hw_body`, from its
/// `{`, strings blanked, the `extern "C"` declaration blanked here) the
/// relation is read off top-level statements:
///
///   * the body's LAST statement — its value — is
///     `if <guard> { … } else { … }`, with nothing after the `else` block and
///     no `else if` chain;
///   * `<guard>` entails readiness (`ready_condition_argument`) and its
///     argument names the executing PE (`ready_argument_is_executing_core`);
///   * the ready branch's last statement is exactly
///     `unsafe { lean_classify_synchronous_exception(esr) }`;
///   * the not-ready branch's only statement is exactly
///     `classify_synchronous_exception_mirror(esr)`.
///
/// The host body's only statement is that same mirror call.
fn classifier_status(hw_body: &str, host_body: &str) -> Result<(), String> {
    const LEAN_CALL: &str = "unsafe { lean_classify_synchronous_exception(esr) }";
    const MIRROR_CALL: &str = "classify_synchronous_exception_mirror(esr)";
    let hw = blank_extern_blocks(hw_body);
    let body_open = hw
        .find('{')
        .ok_or_else(|| "PR #887 review round 6: the hardware classifier has no body".to_string())?;
    let body_close = matching_close_brace(&hw, body_open).ok_or_else(|| {
        "PR #887 review round 6: the hardware classifier's body is unbalanced".to_string()
    })?;
    let statements = top_level_statements(&hw, body_open, body_close);
    let &(lo, hi) = statements.last().ok_or_else(|| {
        "PR #887 review round 6: the hardware classifier's body is empty".to_string()
    })?;
    let stmt = hw[lo..hi].trim_start();
    let if_at = hi - stmt.len();
    if strip_word_prefix(stmt, "if").is_none() {
        return Err(format!(
            "PR #887 review round 6 regression: the hardware classifier's value is `{}`, \
             not the readiness conditional.  A conditional found earlier in the body \
             decides nothing if it is not what the function returns",
            collapse_whitespace(stmt.trim())
        ));
    }
    let true_open = block_open_after(&hw, if_at).ok_or_else(|| {
        "PR #887 review round 6: the readiness conditional has no block".to_string()
    })?;
    let cond = hw[if_at + 2..true_open].trim();
    let arg = ready_condition_argument(cond).ok_or_else(|| {
        format!(
            "PR #887 review round 6 regression: the hardware classifier's terminal \
             conditional `if {cond}` does not entail readiness — the Lean call must sit \
             in the true branch of a bare `lean_ready(…)` guard"
        )
    })?;
    if !ready_argument_is_executing_core(&hw, body_open, if_at, arg) {
        return Err(format!(
            "PR #887 review round 6 regression: the hardware classifier's readiness guard \
             reads `lean_ready({arg})`, and `{arg}` is not bound to the executing PE's \
             TPIDR-derived core id by a statement dominating the guard"
        ));
    }
    let true_close = matching_close_brace(&hw, true_open)
        .ok_or_else(|| "PR #887 review round 6: the ready branch is unbalanced".to_string())?;
    let after = hw[true_close + 1..hi].trim_start();
    let else_body = strip_word_prefix(after, "else")
        .map(str::trim_start)
        .ok_or_else(|| {
            "PR #887 review round 6 regression: the readiness conditional has no `else` \
             branch, so a not-ready core has no classification"
                .to_string()
        })?;
    if !else_body.starts_with('{') {
        return Err(
            "PR #887 review round 6 regression: the readiness conditional continues with \
             `else if`; the not-ready branch must be the mirror call, unconditionally"
                .to_string(),
        );
    }
    let else_open = hi - else_body.len();
    let else_close = matching_close_brace(&hw, else_open)
        .ok_or_else(|| "PR #887 review round 6: the not-ready branch is unbalanced".to_string())?;
    if !hw[else_close + 1..hi].trim().is_empty() {
        return Err(
            "PR #887 review round 6 regression: text follows the `else` block inside the \
             classifier's terminal statement"
                .to_string(),
        );
    }
    let branch_value = |open: usize, close: usize| -> Vec<String> {
        top_level_statements(&hw, open, close)
            .iter()
            .map(|&(a, b)| collapse_whitespace(hw[a..b].trim()))
            .collect()
    };
    let ready = branch_value(true_open, true_close);
    if ready.last().map(String::as_str) != Some(LEAN_CALL) {
        return Err(format!(
            "PR #887 review round 6 regression: the hardware classifier's ready branch \
             evaluates to `{}`, not to the Lean call `{LEAN_CALL}`",
            ready.last().map(String::as_str).unwrap_or("")
        ));
    }
    let not_ready = branch_value(else_open, else_close);
    if not_ready.len() != 1 || not_ready[0] != MIRROR_CALL {
        return Err(format!(
            "PR #887 review round 6 regression: the hardware classifier's not-ready branch \
             is {not_ready:?}, not exactly the mirror call `{MIRROR_CALL}`.  A core whose \
             Lean runtime is not up must classify through the table pinned to the Lean \
             one, so the fail-closed seams route on the class the model would return"
        ));
    }
    let host_open = host_body
        .find('{')
        .ok_or_else(|| "PR #887 review round 6: the host classifier has no body".to_string())?;
    let host_close = matching_close_brace(host_body, host_open).ok_or_else(|| {
        "PR #887 review round 6: the host classifier's body is unbalanced".to_string()
    })?;
    let host: Vec<String> = top_level_statements(host_body, host_open, host_close)
        .iter()
        .map(|&(a, b)| collapse_whitespace(host_body[a..b].trim()))
        .collect();
    if host.len() != 1 || host[0] != MIRROR_CALL {
        return Err(format!(
            "PR #887 review round 6 regression: the host-lane classifier is {host:?}, not \
             exactly the mirror call `{MIRROR_CALL}`, so the host tests would pin a table \
             the pre-readiness path does not run"
        ));
    }
    Ok(())
}

/// Token-preserving mutations for `classifier_status`: every case keeps the
/// Lean call, the gate and the mirror call present and breaks the relation
/// between a branch and its value.
fn verify_classifier_scanner() {
    const GOOD_HW: &str = "{\n    let core_id = crate::per_cpu::current_core_id_from_tpidr();\n    if \
                           crate::lean_ready::lean_ready(core_id as usize) {\n        extern \"C\" {\n            \
                           fn lean_classify_synchronous_exception(esr: u64) -> u32;\n        }\n        unsafe \
                           { lean_classify_synchronous_exception(esr) }\n    } else {\n        \
                           classify_synchronous_exception_mirror(esr)\n    }\n}\n";
    const GOOD_HOST: &str = "{\n    classify_synchronous_exception_mirror(esr)\n}\n";
    let status = |hw: &str, host: &str| {
        let (_, hw_view) = rust_code_views(hw);
        let (_, host_view) = rust_code_views(host);
        classifier_status(&hw_view, &host_view)
    };
    if let Err(why) = status(GOOD_HW, GOOD_HOST) {
        panic!("build.rs self-check: the good classifier fixture was refused: {why}");
    }
    let hw_mutations: &[(&str, &str, &str)] = &[
        (
            "the not-ready branch discarding the mirror's result",
            "    } else {\n        classify_synchronous_exception_mirror(esr)\n    }\n",
            "    } else {\n        let _ = classify_synchronous_exception_mirror(esr);\n        \
             sync_class::SVC\n    }\n",
        ),
        (
            "the not-ready branch classifying another syndrome",
            "        classify_synchronous_exception_mirror(esr)\n",
            "        classify_synchronous_exception_mirror(0)\n",
        ),
        (
            "the ready branch returning the mirror after calling into Lean",
            "        unsafe { lean_classify_synchronous_exception(esr) }\n",
            "        let _ = unsafe { lean_classify_synchronous_exception(esr) };\n        \
             classify_synchronous_exception_mirror(esr)\n",
        ),
        (
            "the gate on a literal core",
            "    if crate::lean_ready::lean_ready(core_id as usize) {\n",
            "    if crate::lean_ready::lean_ready(0) {\n",
        ),
        (
            "the conditional no longer the classifier's value",
            "        classify_synchronous_exception_mirror(esr)\n    }\n}\n",
            "        classify_synchronous_exception_mirror(esr)\n    };\n    sync_class::SVC\n}\n",
        ),
        (
            "an `else if` chain before the mirror",
            "    } else {\n        classify_synchronous_exception_mirror(esr)\n    }\n",
            "    } else if esr == 0 {\n        classify_synchronous_exception_mirror(esr)\n    } else {\n        \
             sync_class::SVC\n    }\n",
        ),
        (
            "the ready branch's Lean call nested under a condition",
            "        unsafe { lean_classify_synchronous_exception(esr) }\n",
            "        if esr == 0 {\n            return unsafe { lean_classify_synchronous_exception(esr) \
             };\n        }\n        classify_synchronous_exception_mirror(esr)\n",
        ),
    ];
    for (what, from, to) in hw_mutations {
        assert!(
            GOOD_HW.contains(from),
            "build.rs self-check: classifier mutation `{what}` does not apply"
        );
        let mutated = GOOD_HW.replacen(from, to, 1);
        assert_ne!(
            mutated, GOOD_HW,
            "build.rs self-check: classifier mutation `{what}` is inert"
        );
        if status(&mutated, GOOD_HOST).is_ok() {
            panic!("build.rs self-check: `classifier_status` accepted a broken hardware classifier: {what}");
        }
    }
    let host_mutated =
        "{\n    let _ = classify_synchronous_exception_mirror(esr);\n    sync_class::SVC\n}\n";
    if status(GOOD_HW, host_mutated).is_ok() {
        panic!(
            "build.rs self-check: `classifier_status` accepted a host classifier that discards \
             the mirror's result"
        );
    }
}

/// The routing relation in `handle_synchronous_exception`'s body — a
/// strings-blanked code view — read off the body's top-level statements:
///
///   1. `halt_if_kernel_origin(frame, esr);` is an unconditional top-level
///      statement: every synchronous exception taken from EL1 halts there,
///      whatever else the frame holds;
///   2. `let exception_class = classify_synchronous_exception(esr);` is a
///      later top-level statement — the class is bound, immutably, to the
///      Lean classifier's result and to nothing else;
///   3. the body's LAST top-level statement is `match exception_class { … }`
///      (`terminal_routing_match`) — the complete routing, after which
///      nothing runs — and exactly one of its arms is
///      `sync_class::KERNEL_ABORT`;
///   4. `exception_class` occurs exactly twice in the body: the binding and
///      the scrutinee.  No comparison, copy, second binding or reassignment
///      consumes it, so the terminal match is the only construct that routes
///      on the class;
///   5. no other `match` names a `sync_class::` tag, no `ec::` constant is
///      referenced, and the pre-readiness mirror is not reached.
///
/// PR #887 review round 3 replaced token counting with the binding's
/// initializer; round 4 made the routing match a top-level statement; round
/// 6 made the gate one too — nested under `if frame.x0() == 0 { … }` it
/// preceded the classifier textually and guarded nothing when `x0` was
/// nonzero — and closed the non-`match` competitors: a no-op top-level match
/// followed by `if exception_class == sync_class::SVC { … }` routed
/// everything while the sweep looked for a second `match`.
fn handler_routing_status(body: &str) -> Result<(), String> {
    let body_open = body.find('{').ok_or_else(|| {
        "PR #887 review round 4: the handler text carries no body block".to_string()
    })?;
    let body_close = matching_close_brace(body, body_open)
        .ok_or_else(|| "PR #887 review round 4: the handler's body is unbalanced".to_string())?;
    let statements = top_level_statements(body, body_open, body_close);
    let text = |span: &(usize, usize)| body[span.0..span.1].trim();
    let gate = statements
        .iter()
        .position(|span| text(span) == "halt_if_kernel_origin(frame, esr);")
        .ok_or_else(|| {
            "PR #887 review round 6 regression: `halt_if_kernel_origin(frame, esr);` is not \
             an unconditional top-level statement of the handler.  Nested under a \
             condition it precedes the classifier textually and guards nothing when the \
             condition is false: an EL1 exception would be classified and delivered with \
             the kernel's register window"
                .to_string()
        })?;
    let binding = statements
        .iter()
        .position(|span| {
            let t = text(span);
            t.starts_with("let exception_class") || t.starts_with("let mut exception_class")
        })
        .ok_or_else(|| {
            "WS-RR RR4.25 regression: no top-level `let exception_class = …` binding, so \
             the routing class is not bound at all"
                .to_string()
        })?;
    let binding_text = text(&statements[binding]);
    let (pattern, init) = let_binding_parts(binding_text).ok_or_else(|| {
        "PR #887 review regression: the `exception_class` binding has no initializer".to_string()
    })?;
    if binding_text.starts_with("let mut") || pattern != "exception_class" {
        return Err(
            "PR #887 review regression: the routing class is bound mutably or by pattern; \
             it must be `let exception_class = …`, immutable, so no later statement can \
             route another class"
                .to_string(),
        );
    }
    if init != "classify_synchronous_exception(esr)" {
        return Err(format!(
            "WS-RR RR4.25 regression: the routing class is bound to `{init}`, not to \
             `classify_synchronous_exception(esr)` — the Lean model is the single \
             classification path, and a second one here can drift from it silently"
        ));
    }
    if gate > binding {
        return Err(
            "PR #887 regression: the kernel-origin gate runs *after* the classification.  \
             The gate must precede it: a kernel fault must never reach the routing match"
                .to_string(),
        );
    }
    let routing = terminal_routing_match(body, body_open, body_close)?;
    let routing_text = body[routing.0..routing.1].trim_start();
    let routing_match_at = routing.1 - routing_text.len();
    let arms = match_arm_spans(routing_text).ok_or_else(|| {
        "PR #887 review round 6: the routing match's arms could not be parsed".to_string()
    })?;
    let kernel_abort_arms = arms
        .iter()
        .filter(|arm| {
            routing_text[arm.pattern.0..arm.pattern.1].trim() == "sync_class::KERNEL_ABORT"
        })
        .count();
    if kernel_abort_arms != 1 {
        return Err(format!(
            "PR #887 regression: the routing match has {kernel_abort_arms} \
             `sync_class::KERNEL_ABORT` arms, not one.  A current-EL abort must halt on \
             its own class, not fall through to the unknown-exception delivery"
        ));
    }
    let uses = word_occurrences(&body[body_open..=body_close], "exception_class");
    if uses != 2 {
        return Err(format!(
            "PR #887 review round 6 regression: `exception_class` occurs {uses} times in the \
             handler; it must occur exactly twice — its binding and the terminal match's \
             scrutinee.  A comparison, a copy, a second binding or a reassignment is a \
             second construct routing on the class, beside the verified match"
        ));
    }
    // No competing routing match: every `match` whose arms name a
    // `sync_class::` tag must be the terminal routing match itself.
    let mut search = 0usize;
    while let Some(hit) = body[search..].find("match ") {
        let at = search + hit;
        search = at + "match ".len();
        let bytes = body.as_bytes();
        if at > 0 && (bytes[at - 1].is_ascii_alphanumeric() || bytes[at - 1] == b'_') {
            continue;
        }
        let Some(open) = block_open_after(body, at) else {
            continue;
        };
        let Some(close) = matching_close_brace(body, open) else {
            continue;
        };
        if body[open..=close].contains("sync_class::") && at != routing_match_at {
            let excerpt: String = body[at..].chars().take(40).collect();
            return Err(format!(
                "PR #887 review round 4: a second match routes on `sync_class::` tags \
                 (`{excerpt}…`); the terminal `match exception_class` is the only \
                 routing construct the handler may have"
            ));
        }
    }
    if let Some(idx) = body.find("ec::") {
        let excerpt: String = body[idx..].chars().take(40).collect();
        return Err(format!(
            "WS-RR RR4.25 regression: the handler references a raw exception-class \
             constant (`{excerpt}…`).  The routing arms must use the `sync_class::` tags \
             the Lean model returns; matching on `ec::` values re-introduces the second \
             classification path RR4.25 removed"
        ));
    }
    if body.contains("classify_synchronous_exception_mirror(") {
        return Err("PR #887 review regression: the handler reaches \
                    `classify_synchronous_exception_mirror` directly.  The mirror is the \
                    classifier's pre-readiness branch, chosen behind the readiness gate; a \
                    handler that calls it is a second classification path"
            .to_string());
    }
    Ok(())
}

/// Token-preserving mutations for `handler_routing_status`: each keeps every
/// token the old presence checks looked for and breaks the relation.
fn verify_handler_routing_scanner() {
    let good = "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
                frame.esr_el1;\n    halt_if_kernel_origin(frame, esr);\n    let exception_class \
                = classify_synchronous_exception(esr);\n    match exception_class {\n        \
                sync_class::KERNEL_ABORT => {\n            halt_on_kernel_abort(frame, esr);\n        \
                }\n        _ => {}\n    }\n}\n";
    let status = |source: &str| {
        let (_, code) = rust_code_views(source);
        handler_routing_status(&code)
    };
    assert!(
        status(good).is_ok(),
        "handler routing self-check: the live shape must pass: {:?}",
        status(good)
    );
    let cases: &[(&str, &str)] = &[
        (
            "the classifier called and discarded, the mirror routed",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    halt_if_kernel_origin(frame, esr);\n    let _ = \
             classify_synchronous_exception(esr);\n    let exception_class = \
             classify_synchronous_exception_mirror(esr);\n    match exception_class {\n        \
             sync_class::KERNEL_ABORT => {\n            halt_on_kernel_abort(frame, esr);\n        \
             }\n        _ => {}\n    }\n}\n",
        ),
        (
            "the class reassigned after the binding",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    halt_if_kernel_origin(frame, esr);\n    let mut exception_class \
             = classify_synchronous_exception(esr);\n    exception_class = 5;\n    match \
             exception_class {\n        sync_class::KERNEL_ABORT => {\n            \
             halt_on_kernel_abort(frame, esr);\n        }\n        _ => {}\n    }\n}\n",
        ),
        (
            "the kernel-origin gate after the classification",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    let exception_class = classify_synchronous_exception(esr);\n    \
             halt_if_kernel_origin(frame, esr);\n    match exception_class {\n        \
             sync_class::KERNEL_ABORT => {\n            halt_on_kernel_abort(frame, esr);\n        \
             }\n        _ => {}\n    }\n}\n",
        ),
        (
            "the routing match on a copy of the class",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    halt_if_kernel_origin(frame, esr);\n    let exception_class = \
             classify_synchronous_exception(esr);\n    let routed = exception_class;\n    match \
             routed {\n        sync_class::KERNEL_ABORT => {\n            \
             halt_on_kernel_abort(frame, esr);\n        }\n        _ => {}\n    }\n}\n",
        ),
        (
            "a raw exception-class constant in the arms",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    halt_if_kernel_origin(frame, esr);\n    let exception_class = \
             classify_synchronous_exception(esr);\n    match exception_class {\n        \
             sync_class::KERNEL_ABORT => {\n            halt_on_kernel_abort(frame, esr);\n        \
             }\n        _ => {\n            if esr_ec(esr) == ec::DABT_LOWER {}\n        }\n    \
             }\n}\n",
        ),
        (
            "the mirror reached from the handler",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    halt_if_kernel_origin(frame, esr);\n    let exception_class = \
             classify_synchronous_exception(esr);\n    let _ = \
             classify_synchronous_exception_mirror(esr);\n    match exception_class {\n        \
             sync_class::KERNEL_ABORT => {\n            halt_on_kernel_abort(frame, esr);\n        \
             }\n        _ => {}\n    }\n}\n",
        ),
        // PR #887 review round 4: the routing match found after the binding
        // but nested under a condition, and a competing routing match.
        (
            "the routing match nested under a condition",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    halt_if_kernel_origin(frame, esr);\n    let exception_class = \
             classify_synchronous_exception(esr);\n    if frame.x0() == 0 {\n        match \
             exception_class {\n            sync_class::KERNEL_ABORT => {\n                \
             halt_on_kernel_abort(frame, esr);\n            }\n            _ => {}\n        }\n    \
             }\n}\n",
        ),
        (
            "a competing routing match on another scrutinee",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    halt_if_kernel_origin(frame, esr);\n    let exception_class = \
             classify_synchronous_exception(esr);\n    let other = esr_ec(esr) as u32;\n    match \
             other {\n        sync_class::SVC => {}\n        _ => {}\n    }\n    match \
             exception_class {\n        sync_class::KERNEL_ABORT => {\n            \
             halt_on_kernel_abort(frame, esr);\n        }\n        _ => {}\n    }\n}\n",
        ),
        (
            "the KERNEL_ABORT arm outside the routing match",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    halt_if_kernel_origin(frame, esr);\n    let exception_class = \
             classify_synchronous_exception(esr);\n    match exception_class {\n        _ => {}\n    \
             }\n    let _arm = \"sync_class::KERNEL_ABORT => {\";\n}\n",
        ),
        // PR #887 review round 6: the gate nested under a condition still
        // precedes the classifier textually; a no-op top-level match followed
        // by an `if` router on the class is not a second `match`; a statement
        // after the routing match runs on every routed class; a copy of the
        // class taken before the match is a second consumer.
        (
            "the kernel-origin gate nested under a condition",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    if frame.x0() == 0 {\n        halt_if_kernel_origin(frame, esr);\n    \
             }\n    let exception_class = classify_synchronous_exception(esr);\n    match \
             exception_class {\n        sync_class::KERNEL_ABORT => {\n            \
             halt_on_kernel_abort(frame, esr);\n        }\n        _ => {}\n    }\n}\n",
        ),
        (
            "a no-op routing match followed by an `if` router on the class",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    halt_if_kernel_origin(frame, esr);\n    let exception_class = \
             classify_synchronous_exception(esr);\n    match exception_class {\n        \
             sync_class::KERNEL_ABORT => {\n            halt_on_kernel_abort(frame, esr);\n        \
             }\n        _ => {}\n    }\n    if exception_class == sync_class::SVC {\n        \
             deliver_fault(frame, error_code::USER_EXCEPTION);\n    } else {\n        \
             halt_on_kernel_abort(frame, esr);\n    }\n}\n",
        ),
        (
            "a statement after the terminal routing match",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    halt_if_kernel_origin(frame, esr);\n    let exception_class = \
             classify_synchronous_exception(esr);\n    match exception_class {\n        \
             sync_class::KERNEL_ABORT => {\n            halt_on_kernel_abort(frame, esr);\n        \
             }\n        _ => {}\n    }\n    deliver_fault(frame, error_code::USER_EXCEPTION);\n}\n",
        ),
        (
            "a copy of the class taken before the routing match",
            "fn handle_synchronous_exception(frame: &mut TrapFrame) {\n    let esr = \
             frame.esr_el1;\n    halt_if_kernel_origin(frame, esr);\n    let exception_class = \
             classify_synchronous_exception(esr);\n    let _probe = exception_class;\n    match \
             exception_class {\n        sync_class::KERNEL_ABORT => {\n            \
             halt_on_kernel_abort(frame, esr);\n        }\n        _ => {}\n    }\n}\n",
        ),
    ];
    for (what, source) in cases {
        assert!(
            status(source).is_err(),
            "handler routing self-check: {what} passed the routing relation"
        );
    }
}

/// PR #887 review round 6: the handler's terminal routing statement — the
/// LAST top-level statement of the body `code[body_open..=body_close]`,
/// which must be `match exception_class { … }`.  Terminal, because a
/// statement after the match would run on every class the match routed, and
/// the match would no longer be the complete routing; last rather than
/// first-found, because a match found anywhere after the binding is what a
/// decoy nested under a condition satisfies.
fn terminal_routing_match(
    code: &str,
    body_open: usize,
    body_close: usize,
) -> Result<(usize, usize), String> {
    let statements = top_level_statements(code, body_open, body_close);
    let &(lo, hi) = statements
        .last()
        .ok_or_else(|| "PR #887 review round 6: the handler body is empty".to_string())?;
    if !code[lo..hi]
        .trim_start()
        .starts_with("match exception_class {")
    {
        return Err(
            "WS-RR RR4.25 regression: the handler's last top-level statement is not \
             `match exception_class { … }`.  The routing match must be the terminal \
             statement: routing under a condition, after the match, or on a copy of the \
             class is a second routing construct beside the verified one"
                .to_string(),
        );
    }
    Ok((lo, hi))
}

/// One arm of a `match`, as byte spans into the text `match_arm_spans` read:
/// the pattern (everything before `=>`, guard included) and the body (a
/// brace block including its braces, or the expression up to its `,`).
struct MatchArm {
    pattern: (usize, usize),
    body: (usize, usize),
}

/// The arms of the `match` expression that `text` starts with — a
/// strings-blanked view, so no `=>` or brace inside a literal can split an
/// arm — or `None` if the text is not a balanced match.  Round 6 (PR #887):
/// an arm is located by its pattern among the arms of a located match, never
/// by the first textual occurrence of the pattern in a file or a function.
fn match_arm_spans(text: &str) -> Option<Vec<MatchArm>> {
    strip_word_prefix(text.trim_start(), "match")?;
    let open = block_open_after(text, 0)?;
    let close = matching_close_brace(text, open)?;
    let bytes = text.as_bytes();
    let mut arms = Vec::new();
    let mut i = open + 1;
    loop {
        while i < close && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= close {
            break;
        }
        let pattern_start = i;
        let mut depth = 0i32;
        let mut arrow = None;
        let mut j = i;
        while j < close {
            match bytes[j] {
                b'(' | b'[' | b'{' => depth += 1,
                b')' | b']' | b'}' => depth -= 1,
                b'=' if depth == 0 && bytes.get(j + 1) == Some(&b'>') => {
                    arrow = Some(j);
                    break;
                }
                _ => {}
            }
            j += 1;
        }
        let arrow = arrow?;
        let mut k = arrow + 2;
        while k < close && bytes[k].is_ascii_whitespace() {
            k += 1;
        }
        if k >= close {
            return None;
        }
        let body_start = k;
        let body_end;
        if bytes[k] == b'{' {
            let block_close = matching_close_brace(text, k)?;
            if block_close >= close {
                return None;
            }
            body_end = block_close + 1;
            k = body_end;
            while k < close && bytes[k].is_ascii_whitespace() {
                k += 1;
            }
            if k < close && bytes[k] == b',' {
                k += 1;
            }
        } else {
            let mut depth = 0i32;
            let mut m = k;
            while m < close {
                match bytes[m] {
                    b'(' | b'[' | b'{' => depth += 1,
                    b')' | b']' | b'}' => depth -= 1,
                    b',' if depth == 0 => break,
                    _ => {}
                }
                m += 1;
            }
            body_end = m;
            k = if m < close { m + 1 } else { m };
        }
        arms.push(MatchArm {
            pattern: (pattern_start, arrow),
            body: (body_start, body_end),
        });
        i = k;
    }
    Some(arms)
}

/// Blank every `extern "C" { … }` block in `body` (byte-aligned), so a
/// declaration inside it cannot stand in for a call.
fn blank_extern_blocks(body: &str) -> String {
    let mut out = body.as_bytes().to_vec();
    let mut search = 0usize;
    while let Some(hit) = body[search..].find("extern \"C\" {") {
        let open = search + hit + "extern \"C\" ".len();
        let mut depth = 0usize;
        let mut end = open;
        for (index, ch) in body[open..].char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        end = open + index + 1;
                        break;
                    }
                }
                _ => {}
            }
        }
        for byte in out.iter_mut().take(end).skip(search + hit) {
            if *byte != b'\n' {
                *byte = b' ';
            }
        }
        search = end.max(open + 1);
    }
    String::from_utf8(out).expect("blanking ASCII bytes keeps the text UTF-8")
}

fn scan_lean_ready_gates_intact() {
    let strip = |contents: &str| -> String {
        contents
            .lines()
            .map(|line| {
                if let Some(idx) = line.find("//") {
                    &line[..idx]
                } else {
                    line
                }
            })
            .collect::<Vec<_>>()
            .join("\n")
    };
    // The named function's body: from its `fn <name>(` declaration through
    // the brace-matched close of its outermost block.
    fn function_body<'a>(stripped: &'a str, path: &str, fn_name: &str) -> &'a str {
        let decl = format!("fn {fn_name}(");
        let decl_idx = stripped.find(&decl).unwrap_or_else(|| {
            panic!(
                "WS-SM regression: `{path}` no longer declares `fn {fn_name}`. \
                 The Lean seam moved or was renamed; update the lean-ready \
                 scanner's site table in the same change so the readiness-gate \
                 contract keeps tracking the real call sites."
            )
        });
        let open_rel = stripped[decl_idx..].find('{').unwrap_or_else(|| {
            panic!(
                "WS-SM lean-ready scanner: `{path}`'s `fn {fn_name}` has no \
                 body block after its declaration."
            )
        });
        let body_start = decl_idx + open_rel;
        let mut depth = 0usize;
        for (i, ch) in stripped[body_start..].char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        return &stripped[body_start..body_start + i + 1];
                    }
                }
                _ => {}
            }
        }
        panic!(
            "WS-SM lean-ready scanner: unbalanced braces while extracting \
             `{path}`'s `fn {fn_name}` body."
        );
    }
    let sites = LEAN_READY_GATED_SEAMS;
    for (path, fn_name, lean_symbol) in sites {
        println!("cargo:rerun-if-changed={path}");
        let stripped = match std::fs::read_to_string(path) {
            Ok(s) => strip(&s),
            Err(e) => panic!("WS-SM lean-ready scanner: failed to read {path}: {e}"),
        };
        let body = function_body(&stripped, path, fn_name);
        let sym_idx = body.find(lean_symbol).unwrap_or_else(|| {
            panic!(
                "WS-SM regression: `{path}`'s `fn {fn_name}` no longer resolves \
                 `{lean_symbol}` in its body.  The Lean seam moved or was \
                 dropped; update this scanner's site table in the same change \
                 so the readiness-gate contract keeps tracking the real call \
                 sites."
            )
        });
        let gate_idx = body.find("lean_ready(").unwrap_or_else(|| {
            panic!(
                "WS-SM regression: `{path}`'s `fn {fn_name}` calls into the \
                 Lean runtime (`{lean_symbol}`) without consulting the per-core \
                 readiness gate (`crate::lean_ready::lean_ready(core)`) in its \
                 body.  A PE must never enter a Lean runtime it has not \
                 initialized; restore the gate around the Lean call."
            )
        });
        if gate_idx >= sym_idx {
            panic!(
                "WS-SM regression: in `{path}`'s `fn {fn_name}`, the readiness \
                 gate (`lean_ready(`) appears only after `{lean_symbol}` — the \
                 Lean call is reachable before the gate is consulted.  Move the \
                 `crate::lean_ready::lean_ready(core)` check so it guards the \
                 Lean call."
            );
        }
    }
}

/// **The Lean seams that consult the per-core readiness gate**, as
/// `(source, enclosing fn, Lean symbol)`.
///
/// This table is a **pin, not the source of truth**:
/// `scan_lean_upcalls_readiness_gated` derives the set of Lean upcalls from
/// the Lean tree's `@[export]` attributes and the HAL's own `extern "C"`
/// declarations, attributes every call to its enclosing function, and fails
/// the build when a gated call is missing here or an entry here has no call
/// behind it.  A hand-written list cannot see the seam that does not exist
/// yet — the PR #887 review found the classifier upcall outside the gate
/// precisely because nothing derived the set — so the derivation decides and
/// this table records.
const LEAN_READY_GATED_SEAMS: &[(&str, &str, &str)] = &[
    (
        "src/timer.rs",
        "per_core_timer_tick_isr",
        "lean_per_core_timer_tick",
    ),
    (
        "src/trap.rs",
        "reschedule_sgi_handler",
        "lean_per_core_reschedule",
    ),
    (
        "src/smp.rs",
        "rust_secondary_main",
        "lean_secondary_kernel_main",
    ),
    // The fault-delivery seam: `deliver_fault` enters the Lean runtime to run
    // `faultDeliverOnCore` against the live kernel state.
    ("src/trap.rs", "deliver_fault", "lean_handle_fault"),
    // PR #887 review: the unknown-syscall seam enters the runtime the same way.
    (
        "src/trap.rs",
        "deliver_unknown_syscall",
        "lean_handle_unknown_syscall",
    ),
    // PR #887 review round 2: the classifier is a Lean-emitted symbol like
    // any other, so it consults the gate too; a not-ready core classifies
    // through the pinned Rust mirror instead.
    (
        "src/trap.rs",
        "classify_synchronous_exception",
        "lean_classify_synchronous_exception",
    ),
    // WS-RR RR5.6: the SVC dispatch seam — the highest-traffic route into the
    // Lean runtime, and one of the two `kernel_entry.rs`'s five-entry table
    // claimed consulted the gate while neither did.
    (
        "src/svc_dispatch.rs",
        "dispatch_svc",
        "lean_syscall_dispatch_cross_core",
    ),
    // WS-RR RR5.7: the cross-core suspend seam.  It reaches Lean through
    // `sele4n_suspend_thread` rather than a `lean_*` symbol, which is why the
    // derived scan — over the Lean tree's `@[export]`s — is what finds it.
    (
        "src/ffi.rs",
        "sele4n_suspend_thread",
        "suspend_thread_cross_core",
    ),
];

/// **Lean upcalls that run outside the readiness gate, by design or as
/// registered debt** — `(source, enclosing fn, Lean symbol, occurrences, why)`.
///
/// Every entry is a call `scan_lean_upcalls_readiness_gated` would otherwise
/// reject, so adding one is a decision with a reason a reader can check, and
/// an entry whose call no longer exists fails the build rather than
/// lingering.
///
/// **PR #887 review round 6: an entry exempts exactly `occurrences` calls**
/// of the symbol in that function, reconciled in both directions by
/// `reconcile_upcall_exemptions`.  The round-3 table was keyed by
/// `(source, fn, symbol)` and recorded one boolean per entry, so a second
/// `lean_syscall_dispatch_cross_core(…)` written into `dispatch_svc` — a
/// second commit of the same syscall, with no reason of its own — matched
/// the existing debt entry and passed.  Now it is a count mismatch, and the
/// entry's count has to change in the same diff as the call.
const LEAN_UPCALLS_OUTSIDE_THE_GATE: &[(&str, &str, &str, usize, &str)] = &[
    (
        "src/boot.rs",
        "rust_boot_main",
        "lean_kernel_main",
        1,
        "the primary core's boot install: this call is the one that initializes \
         the Lean runtime the gate stands for, so it cannot sit behind the gate; \
         the boot core is marked ready after it, the image target's obligation",
    ),
    // WS-RR RR5.6/RR5.7 shrank this table from three entries to one: the SVC
    // dispatch seam and the cross-core suspend seam now consult the gate and
    // have moved to `LEAN_READY_GATED_SEAMS`.  What remains is the boot
    // install, which cannot sit behind the gate because it is the call that
    // initializes the runtime the gate stands for.
];

/// **WS-RR RR5.18**: the two safety tripwires that must survive a release
/// build, as `(source, enclosing fn, a token the condition must name)`.
///
/// This list is a *pin*, and deliberately short: both entries are checks whose
/// documented purpose is to convert a latent hardware-level failure into a
/// clean halt, and both were written as `debug_assert!`, which a `--release`
/// build compiles out.  A `kernel8.img` is built `--release`
/// (`scripts/test_qemu.sh`), so each existed only in the configuration that did
/// not need it.
///
/// Every other `debug_assert!` in the crate is a genuine debug aid — an
/// internal consistency claim about a data structure — and is deliberately not
/// held to this.  What distinguishes these two is that the *documented*
/// behaviour on failure is a halt, so the check has to be able to produce one.
const RELEASE_SURVIVING_TRIPWIRES: &[(&str, &str, &str)] = &[
    (
        "src/kernel_entry.rs",
        "assert_not_holding_round_lock",
        "crate::shootdown::round_lock_held_by(core_id)",
    ),
    (
        "src/boot.rs",
        "install_exception_vectors",
        "!vbar.is_multiple_of(2048)",
    ),
];

/// **WS-RR RR5.18**: each pinned tripwire is a real branch to a fail-closed
/// halt, in every profile.
///
/// Two relations per entry, both asked of the function's own brace-matched
/// body over the comment-blanked view:
///
///   * the body contains no `debug_assert` — a check that compiles out cannot
///     halt anything; and
///   * some `if` in the body whose condition **is** the tripwire's declared
///     failure condition — the whole predicate, whitespace aside, not a token
///     it contains (PR #889 review round 2) — has a block whose **last
///     top-level statement diverges**, which is the statement-level form of
///     "this branch stops the core" rather than "this branch mentions
///     `fatal_halt` somewhere".
///
/// The condition is compared as a predicate because a token is not a
/// relation: `if vbar.is_multiple_of(2048) { fatal_halt() }` keeps `2048` and
/// a terminal halt while halting every *aligned* boot and letting a misaligned
/// VBAR through, and `if !round_lock_held_by(core_id)` keeps the call while
/// halting exactly the cores that respected the lock order.  The second
/// relation is also why a mutation that keeps `fatal_halt()` but nests it
/// under a further condition, or moves it above the branch, is refused.
fn release_surviving_tripwire_status(
    code: &str,
    fn_name: &str,
    condition: &str,
) -> Result<(), String> {
    let signature = format!("fn {fn_name}(");
    let at = code
        .find(&signature)
        .ok_or_else(|| format!("`{fn_name}` is not defined here"))?;
    // An offset *inside* the body: `enclosing_fn_span` resolves the innermost
    // `fn` whose brace-matched body contains it, and the signature itself sits
    // outside that span.
    let brace = at
        + code[at..]
            .find('{')
            .ok_or_else(|| format!("`{fn_name}` has no body"))?;
    let (_, body_open, body_close) = enclosing_fn_span(code, brace + 1)
        .ok_or_else(|| format!("`{fn_name}`'s body could not be resolved"))?;
    let body = &code[body_open..=body_close];
    if body.contains("debug_assert") {
        return Err(format!(
            "`{fn_name}` uses `debug_assert`, which a `--release` build compiles out — the \
             halt it documents would not exist in the image that ships"
        ));
    }
    let wanted = condition_key(condition);
    let mut saw_condition = false;
    for (if_at, block_open) in if_statements(body) {
        if condition_key(&body[if_at + 2..block_open]) != wanted {
            continue;
        }
        saw_condition = true;
        let Some(block_close) = matching_close_brace(body, block_open) else {
            continue;
        };
        let statements = top_level_statements(body, block_open, block_close);
        if statements
            .last()
            .map(|&(lo, hi)| statement_diverges(&body[lo..hi]))
            .unwrap_or(false)
        {
            return Ok(());
        }
    }
    if saw_condition {
        Err(format!(
            "`{fn_name}` has an `if {condition}` but its block does not end in a diverging \
             statement — the tripwire does not stop the core on the condition it exists to catch"
        ))
    } else {
        Err(format!(
            "`{fn_name}` has no `if` whose condition is exactly `{condition}` — a reversed, \
             widened or rewritten predicate keeps the tripwire's tokens and halts on the wrong \
             case"
        ))
    }
}

/// The whitespace-free spelling of a condition, for comparing predicates
/// rather than tokens.
fn condition_key(condition: &str) -> String {
    condition.chars().filter(|c| !c.is_whitespace()).collect()
}

/// Every `if` statement in `body`: the offset of its `if` keyword and the
/// offset of the `{` opening its block.  An `if` is a keyword only at a word
/// boundary, so `elif`-like identifiers and field names do not count.
fn if_statements(body: &str) -> Vec<(usize, usize)> {
    let bytes = body.as_bytes();
    let is_ident = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
    let mut out = Vec::new();
    let mut search = 0usize;
    while let Some(hit) = body[search..].find("if") {
        let if_at = search + hit;
        search = if_at + 2;
        let before_ok = if_at == 0 || !is_ident(bytes[if_at - 1]);
        let after_ok = if_at + 2 < bytes.len()
            && (bytes[if_at + 2].is_ascii_whitespace() || matches!(bytes[if_at + 2], b'(' | b'!'));
        if !(before_ok && after_ok) {
            continue;
        }
        if let Some(block_open) = block_open_after(body, if_at + 2) {
            out.push((if_at, block_open));
        }
    }
    out
}

/// **WS-RR RR5.18**: run `release_surviving_tripwire_status` over the pin.
fn scan_release_surviving_tripwires() {
    verify_release_surviving_tripwire_scanner();
    for (path, fn_name, condition) in RELEASE_SURVIVING_TRIPWIRES {
        println!("cargo:rerun-if-changed={path}");
        let contents = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("WS-RR RR5.18 scanner: cannot read `{path}`: {e}"));
        let (_, code) = rust_code_views(&contents);
        if let Err(why) = release_surviving_tripwire_status(&code, fn_name, condition) {
            panic!("WS-RR RR5.18 regression: `{path}`: {why}");
        }
    }
}

/// Token-preserving self-check for `release_surviving_tripwire_status`.
fn verify_release_surviving_tripwire_scanner() {
    const GOOD: &str = r#"
#[inline]
pub fn assert_not_holding_round_lock(core_id: usize) {
    if crate::shootdown::round_lock_held_by(core_id) {
        crate::kprintln!("[kernel-entry] FATAL: lock order violated");
        crate::cpu::fatal_halt();
    }
}
"#;
    let check = |source: &str| -> Result<(), String> {
        let (_, code) = rust_code_views(source);
        release_surviving_tripwire_status(
            &code,
            "assert_not_holding_round_lock",
            "crate::shootdown::round_lock_held_by(core_id)",
        )
    };
    if let Err(why) = check(GOOD) {
        panic!("build.rs self-check: the good tripwire fixture was refused: {why}");
    }
    verify_release_surviving_tripwire_polarity();
    let mutations: [(&str, &str, &str); 6] = [
        (
            "the predicate is reversed, keeping its call",
            "    if crate::shootdown::round_lock_held_by(core_id) {",
            "    if !crate::shootdown::round_lock_held_by(core_id) {",
        ),
        (
            "the predicate is widened, keeping its call",
            "    if crate::shootdown::round_lock_held_by(core_id) {",
            "    if crate::shootdown::round_lock_held_by(core_id) && crate::shootdown::retry_pending() {",
        ),
        (
            "the halt survives but the branch becomes a debug_assert",
            "    if crate::shootdown::round_lock_held_by(core_id) {\n        crate::kprintln!(\"[kernel-entry] FATAL: lock order violated\");\n        crate::cpu::fatal_halt();\n    }",
            "    debug_assert!(!crate::shootdown::round_lock_held_by(core_id));\n    if false {\n        crate::cpu::fatal_halt();\n    }",
        ),
        (
            "the halt is kept but nested under an unrelated condition",
            "        crate::cpu::fatal_halt();\n    }",
            "        if crate::shootdown::retry_pending() {\n            crate::cpu::fatal_halt();\n        }\n    }",
        ),
        (
            "the halt is kept but is no longer the branch's last statement",
            "        crate::cpu::fatal_halt();\n    }",
            "        crate::cpu::fatal_halt();\n        crate::kprintln!(\"unreached\");\n    }",
        ),
        (
            "the halt is kept but moves above the branch, so the branch decides nothing",
            "    if crate::shootdown::round_lock_held_by(core_id) {\n        crate::kprintln!(\"[kernel-entry] FATAL: lock order violated\");\n        crate::cpu::fatal_halt();\n    }",
            "    let held = crate::shootdown::round_lock_held_by(core_id);\n    crate::cpu::fatal_halt();\n    if held {\n        crate::kprintln!(\"[kernel-entry] FATAL: lock order violated\");\n    }",
        ),
    ];
    for (what, from, to) in mutations {
        assert!(
            GOOD.contains(from),
            "build.rs self-check: tripwire mutation `{what}` does not apply"
        );
        let mutated = GOOD.replacen(from, to, 1);
        assert_ne!(
            mutated, GOOD,
            "build.rs self-check: tripwire mutation `{what}` is inert"
        );
        assert!(
            mutated.contains("fatal_halt("),
            "build.rs self-check: tripwire mutation `{what}` DELETED the halt; the mutation \
             must keep the token and break the relation"
        );
        if check(&mutated).is_ok() {
            panic!(
                "build.rs self-check: `release_surviving_tripwire_status` accepted a broken \
                 fixture: {what}"
            );
        }
    }
}

/// **PR #889 review round 2**: the VBAR tripwire's negated predicate, and the
/// polarity mutations that keep every token of it.  `2048` and a terminal halt
/// survive each of them; what changes is which boots halt.
fn verify_release_surviving_tripwire_polarity() {
    const GOOD: &str = r#"
pub fn install_exception_vectors() {
    let vbar = vector_base();
    if !vbar.is_multiple_of(2048) {
        crate::kprintln!("[boot] FATAL: exception vector table is not 2048-byte aligned");
        crate::cpu::fatal_halt();
    }
    crate::registers::write_vbar_el1(vbar);
}
"#;
    let check = |source: &str| -> Result<(), String> {
        let (_, code) = rust_code_views(source);
        release_surviving_tripwire_status(
            &code,
            "install_exception_vectors",
            "!vbar.is_multiple_of(2048)",
        )
    };
    if let Err(why) = check(GOOD) {
        panic!("build.rs self-check: the good VBAR tripwire fixture was refused: {why}");
    }
    let mutations: [(&str, &str, &str); 3] = [
        (
            "the alignment predicate is reversed: aligned boots halt, misaligned ones proceed",
            "    if !vbar.is_multiple_of(2048) {",
            "    if vbar.is_multiple_of(2048) {",
        ),
        (
            "the predicate is rewritten around the same constant with the wrong polarity",
            "    if !vbar.is_multiple_of(2048) {",
            "    if vbar % 2048 == 0 {",
        ),
        (
            "the halt is kept but the condition is a stored, later-negated flag",
            "    if !vbar.is_multiple_of(2048) {",
            "    let aligned = vbar.is_multiple_of(2048);\n    if aligned {",
        ),
    ];
    for (what, from, to) in mutations {
        assert!(
            GOOD.contains(from),
            "build.rs self-check: VBAR tripwire mutation `{what}` does not apply"
        );
        let mutated = GOOD.replacen(from, to, 1);
        assert_ne!(
            mutated, GOOD,
            "build.rs self-check: VBAR tripwire mutation `{what}` is inert"
        );
        assert!(
            mutated.contains("2048") && mutated.contains("fatal_halt("),
            "build.rs self-check: VBAR tripwire mutation `{what}` DELETED a token; the \
             mutation must keep the tokens and break the relation"
        );
        if check(&mutated).is_ok() {
            panic!(
                "build.rs self-check: `release_surviving_tripwire_status` accepted a VBAR \
                 tripwire with the wrong polarity: {what}"
            );
        }
    }
}

/// **WS-RR RR5.9**: where a Lean symbol's declaration or definition sits, as
/// the scanner classifies it.
#[derive(Debug, PartialEq, Eq)]
struct LeanSymbolDeclaration {
    /// The Lean symbol declared or defined.
    symbol: String,
    /// Is this an `extern "C"` declaration or definition, or does it carry
    /// `#[no_mangle]`?  Either way it puts the Lean name in the linker's hands.
    linker_visible: bool,
    /// The verdict of the innermost decisive `cfg` region enclosing it:
    /// `Some(true)` when the enclosing `#[cfg(..)]` attributes **entail**
    /// `feature = "hw_target"` (the item is compiled only with the feature on),
    /// `Some(false)` when they entail its negation, `None` when the scanner can
    /// establish neither (`hw_target_region`).
    hw_target: Option<bool>,
}

/// **WS-RR RR5.9**: what one `cfg` predicate entails about `feature =
/// "hw_target"`.
///
/// Four entailments, every one **under-approximated**: `true` is an entailment
/// the evaluator established, `false` says only that it established none.  A
/// verdict built from them can therefore refuse a gate that is in fact sound —
/// `any(feature = "hw_target", feature = "hw_target")`, say — and can never
/// accept one that is not, which is the direction that fails closed.  The
/// combinators follow the `cfg` grammar (`not`, `all`, `any`); an atom other
/// than the feature itself entails nothing in either direction.
///
/// This replaced two substring tests (`contains("not(feature = \"hw_target\")")`
/// first, then `contains("feature = \"hw_target\"")`), which read the *token*
/// off the header and not the *predicate*: a `cfg_attr(feature = "hw_target",
/// ..)` — which gates nothing — and an `any(feature = "hw_target", ..)` — which
/// compiles the item without the feature — both carried the token and both
/// passed as a positive gate.  Presence is not a relation; the relation here is
/// entailment, and it is computed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct HwTargetEntailment {
    /// `P → hw_target`: the item exists only with the feature on.
    needs_hw: bool,
    /// `P → ¬hw_target`: the item exists only with the feature off.
    needs_not_hw: bool,
    /// `hw_target → P`: the feature on suffices for the item to exist.
    given_hw: bool,
    /// `¬hw_target → P`: the feature off suffices for the item to exist.
    given_not_hw: bool,
}

impl HwTargetEntailment {
    /// `true` (the empty conjunction): entailed by everything, entails nothing.
    const TRIVIAL: Self = Self {
        needs_hw: false,
        needs_not_hw: false,
        given_hw: true,
        given_not_hw: true,
    };

    /// The conjunction `all(self, other)`.
    fn and(self, other: Self) -> Self {
        Self {
            needs_hw: self.needs_hw || other.needs_hw,
            needs_not_hw: self.needs_not_hw || other.needs_not_hw,
            given_hw: self.given_hw && other.given_hw,
            given_not_hw: self.given_not_hw && other.given_not_hw,
        }
    }
}

/// **WS-RR RR5.9**: split `args` at the commas outside parentheses and string
/// literals — the arguments of one `cfg` combinator.
fn split_top_level_commas(args: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    let mut start = 0usize;
    for (i, b) in args.bytes().enumerate() {
        if in_string {
            if escaped {
                escaped = false;
            } else if b == b'\\' {
                escaped = true;
            } else if b == b'"' {
                in_string = false;
            }
            continue;
        }
        match b {
            b'"' => in_string = true,
            b'(' => depth += 1,
            b')' => depth = depth.saturating_sub(1),
            b',' if depth == 0 => {
                out.push(&args[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(&args[start..]);
    out.into_iter()
        .map(str::trim)
        .filter(|a| !a.is_empty())
        .collect()
}

/// **WS-RR RR5.9**: the entailment of one `cfg` predicate (`hw_target_region`).
fn cfg_predicate_entailment(pred: &str) -> HwTargetEntailment {
    let pred = pred.trim();
    // `feature = "hw_target"`, whitespace-insensitively: the atom.
    let squeezed: String = pred.split_whitespace().collect();
    if squeezed == "feature=\"hw_target\"" {
        return HwTargetEntailment {
            needs_hw: true,
            needs_not_hw: false,
            given_hw: true,
            given_not_hw: false,
        };
    }
    let Some(open) = pred.find('(') else {
        return HwTargetEntailment::default();
    };
    if !pred.ends_with(')') {
        return HwTargetEntailment::default();
    }
    let head = pred[..open].trim();
    let args: Vec<HwTargetEntailment> = split_top_level_commas(&pred[open + 1..pred.len() - 1])
        .into_iter()
        .map(cfg_predicate_entailment)
        .collect();
    match head {
        // `¬P → hw` iff `¬hw → P`, and so on: the four entailments of a
        // negation are the four of its operand, read across the diagonal.
        "not" if args.len() == 1 => {
            let p = args[0];
            HwTargetEntailment {
                needs_hw: p.given_not_hw,
                needs_not_hw: p.given_hw,
                given_hw: p.needs_not_hw,
                given_not_hw: p.needs_hw,
            }
        }
        "all" => args
            .iter()
            .fold(HwTargetEntailment::TRIVIAL, |acc, p| acc.and(*p)),
        // A disjunction needs the feature only when every disjunct does, and
        // is given by the feature when any disjunct is.
        "any" => HwTargetEntailment {
            needs_hw: !args.is_empty() && args.iter().all(|p| p.needs_hw),
            needs_not_hw: !args.is_empty() && args.iter().all(|p| p.needs_not_hw),
            given_hw: args.iter().any(|p| p.given_hw),
            given_not_hw: args.iter().any(|p| p.given_not_hw),
        },
        _ => HwTargetEntailment::default(),
    }
}

/// **WS-RR RR5.9**: the predicates of the `#[cfg(..)]` attributes in one item
/// header, in order.  Only `cfg` — `cfg_attr` and every other attribute are
/// skipped, whatever they mention.
fn cfg_attribute_predicates(header: &str) -> Vec<&str> {
    let bytes = header.as_bytes();
    let mut out = Vec::new();
    let mut search = 0usize;
    while let Some(hit) = header[search..].find("#[") {
        let mut i = search + hit + 2;
        search = i;
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        let name_start = i;
        while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
            i += 1;
        }
        if &header[name_start..i] != "cfg" {
            continue;
        }
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= bytes.len() || bytes[i] != b'(' {
            continue;
        }
        let pred_start = i + 1;
        let mut depth = 0usize;
        let mut in_string = false;
        let mut escaped = false;
        let mut pred_end = None;
        let mut j = i;
        while j < bytes.len() {
            let b = bytes[j];
            if in_string {
                if escaped {
                    escaped = false;
                } else if b == b'\\' {
                    escaped = true;
                } else if b == b'"' {
                    in_string = false;
                }
            } else {
                match b {
                    b'"' => in_string = true,
                    b'(' => depth += 1,
                    b')' => {
                        depth -= 1;
                        if depth == 0 {
                            pred_end = Some(j);
                            break;
                        }
                    }
                    _ => {}
                }
            }
            j += 1;
        }
        let Some(pred_end) = pred_end else { break };
        let mut k = pred_end + 1;
        while k < bytes.len() && bytes[k].is_ascii_whitespace() {
            k += 1;
        }
        if k < bytes.len() && bytes[k] == b']' {
            out.push(&header[pred_start..pred_end]);
        }
        search = pred_end + 1;
    }
    out
}

/// **WS-RR RR5.9**: the verdict of one item header — `Some(true)` when its
/// `cfg` attributes, conjoined, entail `feature = "hw_target"`, `Some(false)`
/// when they entail its negation, `None` when the evaluator can establish
/// neither (no `cfg`, a `cfg` that does not mention the feature, or one that
/// mentions it without deciding it).  A header entailing both is contradictory
/// — the item is never compiled — and is `None` too, so it satisfies nothing.
fn header_verdict(header: &str) -> Option<bool> {
    let preds = cfg_attribute_predicates(header);
    if preds.is_empty() {
        return None;
    }
    let e = preds
        .iter()
        .map(|p| cfg_predicate_entailment(p))
        .fold(HwTargetEntailment::TRIVIAL, HwTargetEntailment::and);
    match (e.needs_hw, e.needs_not_hw) {
        (true, false) => Some(true),
        (false, true) => Some(false),
        _ => None,
    }
}

/// **WS-RR RR5.9**: the `hw_target` cfg region enclosing byte `at`, or `None`.
///
/// Walks outward from `at`: first the *item header* ending at `at` (the text
/// back to the previous statement boundary, which carries the attributes of a
/// module-level item), then each enclosing block's own header, innermost first.
/// The first header with a decisive verdict (`header_verdict`) decides: a
/// `cfg` on an enclosing module or block gates everything inside it, and an
/// inner header whose `cfg` does not mention the feature leaves the decision
/// to the next one out.
///
/// `code` must be a comment-blanked view: a comment naming the feature would
/// otherwise gate an item that no attribute gates — the presence-versus-relation
/// mistake, in the direction that fails *open*.
fn hw_target_region(code: &str, at: usize) -> Option<bool> {
    // The header of the construct whose body/text contains `pos`: back to the
    // previous statement boundary.
    fn header_before(code: &str, pos: usize) -> &str {
        let bytes = code.as_bytes();
        let mut i = pos;
        while i > 0 {
            match bytes[i - 1] {
                b';' | b'{' | b'}' => break,
                _ => i -= 1,
            }
        }
        &code[i..pos]
    }
    if let Some(v) = header_verdict(header_before(code, at)) {
        return Some(v);
    }
    let bytes = code.as_bytes();
    let mut pos = at;
    loop {
        // The innermost unmatched `{` before `pos`.
        let mut depth = 0usize;
        let mut open = None;
        let mut i = pos;
        while i > 0 {
            i -= 1;
            match bytes[i] {
                b'}' => depth += 1,
                b'{' => {
                    if depth == 0 {
                        open = Some(i);
                        break;
                    }
                    depth -= 1;
                }
                _ => {}
            }
        }
        let open = open?;
        if let Some(v) = header_verdict(header_before(code, open)) {
            return Some(v);
        }
        pos = open;
    }
}

/// **WS-RR RR5.9**: does an item header put the item's name in the symbol
/// table?  The `extern` keyword (an `extern "C" fn`, or the header of the
/// `extern "C" { .. }` block a declaration sits in), or a `no_mangle` attribute
/// in either spelling — `#[no_mangle]` and the edition-2024 `#[unsafe(no_mangle)]`,
/// which the 2021 edition this crate builds under accepts as well.  Read as
/// whole words on the blanked view, not as substrings: an attribute *string*
/// is blanked before this sees it, and an identifier that merely contains the
/// letters is not the keyword.
fn header_is_linker_visible(header: &str) -> bool {
    contains_word(header, "extern") || contains_word(header, "no_mangle")
}

/// **WS-RR RR5.9**: `word` occurs in `text` as a whole identifier.
fn contains_word(text: &str, word: &str) -> bool {
    let bytes = text.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut search = 0usize;
    while let Some(hit) = text[search..].find(word) {
        let at = search + hit;
        let end = at + word.len();
        search = end;
        if (at == 0 || !is_ident(bytes[at - 1])) && (end == bytes.len() || !is_ident(bytes[end])) {
            return true;
        }
    }
    false
}

/// **WS-RR RR5.9**: every declaration or definition of a Lean symbol in one
/// comment- and string-blanked source view, with where it sits.
///
/// A declaration is the symbol preceded by the `fn` keyword — the same
/// classification `lean_upcall_sites` uses to tell a declaration from a call,
/// so the two scanners cannot disagree about what a site is.  `linker_visible`
/// is true when the item is `extern` (an `extern "C" { … }` block's contents, or
/// an `extern "C" fn` definition) or carries `#[no_mangle]`: those are the forms
/// that put the Lean name in the symbol table, which is what RR5.8 confines to
/// `hw_target`.
fn lean_symbol_declarations(
    code: &str,
    strings_kept: &str,
    exports: &[&str],
) -> Vec<LeanSymbolDeclaration> {
    let bytes = code.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut out = Vec::new();
    for symbol in exports {
        // `#[export_name = "<symbol>"]` (or `#[unsafe(export_name = ..)]`) puts
        // the *string* in the symbol table, whatever the item is called, so it
        // is a linker-visible declaration of the Lean symbol wherever it sits.
        // Read off the strings-kept view, where the name still exists.
        let needle = format!("\"{symbol}\"");
        let mut search = 0usize;
        while let Some(hit) = strings_kept[search..].find(&needle) {
            let at = search + hit;
            search = at + needle.len();
            let lead: String = strings_kept[..at]
                .chars()
                .rev()
                .take_while(|c| *c != '#')
                .collect::<String>()
                .chars()
                .rev()
                .filter(|c| !c.is_whitespace())
                .collect();
            if lead == "[export_name=" || lead == "[unsafe(export_name=" {
                out.push(LeanSymbolDeclaration {
                    symbol: (*symbol).to_string(),
                    linker_visible: true,
                    hw_target: hw_target_region(strings_kept, at),
                });
            }
        }
        let mut search = 0usize;
        while let Some(hit) = code[search..].find(*symbol) {
            let at = search + hit;
            let end = at + symbol.len();
            search = end;
            if (at > 0 && is_ident(bytes[at - 1])) || (end < bytes.len() && is_ident(bytes[end])) {
                continue;
            }
            let mut before = at;
            while before > 0 && matches!(bytes[before - 1], b' ' | b'\t' | b'\n' | b'\r') {
                before -= 1;
            }
            let declared = before >= 2
                && &code[before - 2..before] == "fn"
                && (before == 2 || !is_ident(bytes[before - 3]));
            if !declared {
                continue;
            }
            // The item's own header, plus — for a declaration inside an
            // `extern "C" { … }` block — that block's header.
            let header = {
                let mut i = before - 2;
                while i > 0 && !matches!(bytes[i - 1], b';' | b'{' | b'}') {
                    i -= 1;
                }
                let own = &code[i..before];
                let mut enclosing = String::new();
                if i > 0 && bytes[i - 1] == b'{' {
                    let block_open = i - 1;
                    let mut j = block_open;
                    while j > 0 && !matches!(bytes[j - 1], b';' | b'{' | b'}') {
                        j -= 1;
                    }
                    enclosing.push_str(&code[j..block_open]);
                }
                format!("{enclosing}\n{own}")
            };
            out.push(LeanSymbolDeclaration {
                symbol: (*symbol).to_string(),
                linker_visible: header_is_linker_visible(&header),
                // The cfg attributes are read from the **strings-kept** view,
                // byte-aligned with this one: `feature = "hw_target"` is a
                // string literal, and the blanked view the declarations are
                // located in has erased it.  A gate read from a view that
                // blanked the gate is the round-3 defect where an `asm!`
                // template's own directives were counted off a view that had
                // blanked the template.
                hw_target: hw_target_region(strings_kept, at),
            });
        }
    }
    out
}

/// **WS-RR RR5.9**: no Lean symbol is declared, defined or exported outside a
/// `hw_target` region.
///
/// The second half of the finding RR5.6/RR5.7 close.  The readiness gate decides
/// whether a Lean call *executes*; it says nothing about whether the call path is
/// *compiled*, and both seams declared their Lean `extern` under
/// `#[cfg(not(test))]` — so `cargo build -p sele4n-hal`, the default host
/// profile, compiled a call to a bare-metal symbol nothing on the host provides,
/// and `cargo test` linked one into every test binary through a `#[no_mangle]`
/// stub.  Two rules, both structural:
///
///   * a **linker-visible** form (an `extern "C"` declaration or definition, or
///     any `#[no_mangle]` item) may exist only under
///     `#[cfg(feature = "hw_target")]`; and
///   * a plain Rust definition of the same name — a host-lane stand-in — may
///     exist only under `#[cfg(not(feature = "hw_target"))]`, so it cannot
///     shadow the real entry point on hardware.
///
/// Calls are not this scanner's business: `scan_lean_upcalls_readiness_gated`
/// owns them, and a call to a symbol declared only under `hw_target` is a
/// compile error on any other configuration.
fn lean_extern_gating_status(
    views: &[(String, String, String)],
    exports: &[&str],
) -> Result<usize, String> {
    let mut checked = 0usize;
    for (path, code, strings_kept) in views {
        for decl in lean_symbol_declarations(code, strings_kept, exports) {
            checked += 1;
            let LeanSymbolDeclaration {
                symbol,
                linker_visible,
                hw_target,
            } = decl;
            match (linker_visible, hw_target) {
                (true, Some(true)) => {}
                (false, Some(false)) => {}
                (true, _) => {
                    return Err(format!(
                        "`{path}` declares or exports the Lean symbol `{symbol}` outside \
                         `#[cfg(feature = \"hw_target\")]`.  An `extern \"C\"` declaration or a \
                         `#[no_mangle]` definition puts a bare-metal kernel entry point in the \
                         linker's hands on every configuration that compiles it — including the \
                         default host profile, which has nothing to resolve it against.  Gate the \
                         item on `feature = \"hw_target\"`; a host lane needs a plain Rust \
                         stand-in under `cfg(not(feature = \"hw_target\"))`, not an `extern`"
                    ));
                }
                (false, _) => {
                    return Err(format!(
                        "`{path}` defines a plain Rust function named after the Lean symbol \
                         `{symbol}` outside `#[cfg(not(feature = \"hw_target\"))]`.  A host-lane \
                         stand-in must be confined to the host lane, or it shadows the real \
                         entry point in a build that links the kernel"
                    ));
                }
            }
        }
    }
    Ok(checked)
}

/// **WS-RR RR5.9**: token-preserving self-check for `lean_extern_gating_status`.
///
/// Every mutation **keeps** the tokens a presence check would look for — the
/// `extern "C"`, the symbol name, and the literal `hw_target` — and breaks only
/// the *relation* the scanner is about: which cfg region the item sits in, and
/// whether the item is linker-visible there.  A fixture that mutated by deleting
/// the gate would be survived by any scanner that merely greps for it, which is
/// the failure mode CLAUDE.md's "test a gate by breaking the relation" rule
/// names.
///
/// The fixture is no thinner than the real sources: it carries a gated `extern`
/// block, a gated `extern` nested two blocks deep (the `timer.rs` shape), a
/// negation-gated host stand-in, and a comment naming the feature — so a
/// scanner reading the raw text rather than the comment-blanked view fails the
/// last case.
fn verify_lean_extern_gating_scanner() {
    const GOOD: &str = r#"
#[cfg(feature = "hw_target")]
extern "C" {
    fn lean_alpha(x: u64) -> u64;
}

#[cfg(not(feature = "hw_target"))]
unsafe fn lean_alpha(_x: u64) -> u64 {
    0
}

fn beta_seam(core: usize) {
    #[cfg(feature = "hw_target")]
    {
        if crate::lean_ready::lean_ready(core) {
            extern "C" {
                fn lean_beta(core_id: u64);
            }
            unsafe { lean_beta(core as u64) };
        }
    }
}

#[cfg(all(feature = "hw_target", target_arch = "aarch64"))]
extern "C" {
    fn lean_gamma() -> u64;
}

#[cfg(not(feature = "hw_target"))]
fn lean_gamma() -> u64 {
    0
}
"#;
    let exports = ["lean_alpha", "lean_beta", "lean_gamma"];
    let check = |source: &str| -> Result<usize, String> {
        let (kept, blanked) = rust_code_views(source);
        lean_extern_gating_status(&[("fixture.rs".to_string(), blanked, kept)], &exports)
    };
    match check(GOOD) {
        Ok(5) => {}
        Ok(n) => panic!(
            "build.rs self-check: the good extern-gating fixture classified {n} declarations, \
             expected 5 (the gated extern, the host stand-in, the nested extern, the \
             `all`-gated extern and its stand-in)"
        ),
        Err(why) => {
            panic!("build.rs self-check: the good extern-gating fixture was refused: {why}")
        }
    }
    let mutations: [(&str, &str, &str); 12] = [
        (
            "the extern keeps its cfg but the gate becomes a different feature",
            "#[cfg(feature = \"hw_target\")]\nextern \"C\" {\n    fn lean_alpha",
            "#[cfg(feature = \"host_tools\")]\nextern \"C\" {\n    fn lean_alpha",
        ),
        (
            "the extern keeps the literal `hw_target` but under its negation",
            "#[cfg(feature = \"hw_target\")]\nextern \"C\" {\n    fn lean_alpha",
            "#[cfg(not(feature = \"hw_target\"))]\nextern \"C\" {\n    fn lean_alpha",
        ),
        (
            "the host stand-in keeps its body but loses the negated gate",
            "#[cfg(not(feature = \"hw_target\"))]\nunsafe fn lean_alpha",
            "unsafe fn lean_alpha",
        ),
        (
            "the host stand-in stays negation-gated but becomes linker-visible",
            "#[cfg(not(feature = \"hw_target\"))]\nunsafe fn lean_alpha",
            "#[cfg(not(feature = \"hw_target\"))]\n#[no_mangle]\nunsafe fn lean_alpha",
        ),
        (
            "the nested extern keeps every enclosing block but the outer gate moves off it",
            "    #[cfg(feature = \"hw_target\")]\n    {\n        if crate::lean_ready",
            "    {\n        if crate::lean_ready",
        ),
        (
            "the gate is present only as a comment",
            "#[cfg(feature = \"hw_target\")]\nextern \"C\" {\n    fn lean_alpha",
            "// #[cfg(feature = \"hw_target\")]\nextern \"C\" {\n    fn lean_alpha",
        ),
        (
            "the extern keeps the literal in a `cfg_attr`, which gates nothing",
            "#[cfg(feature = \"hw_target\")]\nextern \"C\" {\n    fn lean_alpha",
            "#[cfg_attr(feature = \"hw_target\", allow(dead_code))]\nextern \"C\" {\n    fn lean_alpha",
        ),
        (
            "the extern's gate becomes an `any` the feature does not decide",
            "#[cfg(feature = \"hw_target\")]\nextern \"C\" {\n    fn lean_alpha",
            "#[cfg(any(feature = \"hw_target\", feature = \"host_tools\"))]\nextern \"C\" {\n    \
             fn lean_alpha",
        ),
        (
            "the host stand-in's negation wraps an `all` the feature does not decide",
            "#[cfg(not(feature = \"hw_target\"))]\nunsafe fn lean_alpha",
            "#[cfg(not(all(feature = \"hw_target\", feature = \"host_tools\")))]\nunsafe fn lean_alpha",
        ),
        (
            "the `all`-gated extern keeps every conjunct but under `any`",
            "#[cfg(all(feature = \"hw_target\", target_arch = \"aarch64\"))]\nextern \"C\" {\n    \
             fn lean_gamma",
            "#[cfg(any(feature = \"hw_target\", target_arch = \"aarch64\"))]\nextern \"C\" {\n    \
             fn lean_gamma",
        ),
        (
            "the host stand-in stays negation-gated but becomes linker-visible through the \
             edition-2024 attribute spelling",
            "#[cfg(not(feature = \"hw_target\"))]\nunsafe fn lean_alpha",
            "#[cfg(not(feature = \"hw_target\"))]\n#[unsafe(no_mangle)]\nunsafe fn lean_alpha",
        ),
        (
            "a host item of another name is exported under the Lean symbol's name",
            "#[cfg(not(feature = \"hw_target\"))]\nfn lean_gamma() -> u64 {",
            "#[cfg(not(feature = \"hw_target\"))]\n#[export_name = \"lean_gamma\"]\nfn \
             host_gamma() -> u64 {",
        ),
    ];
    for (what, from, to) in mutations {
        assert!(
            GOOD.contains(from),
            "build.rs self-check: extern-gating mutation `{what}` does not apply"
        );
        let mutated = GOOD.replacen(from, to, 1);
        assert_ne!(
            mutated, GOOD,
            "build.rs self-check: extern-gating mutation `{what}` is inert"
        );
        assert!(
            mutated.contains("hw_target"),
            "build.rs self-check: extern-gating mutation `{what}` DELETED the token; the \
             mutation must keep it and break the relation"
        );
        if check(&mutated).is_ok() {
            panic!(
                "build.rs self-check: `lean_extern_gating_status` accepted a broken fixture: \
                 {what}"
            );
        }
    }
}

/// One call from HAL Rust into a Lean-emitted symbol, as the scanner found it.
#[derive(Debug, PartialEq, Eq)]
struct LeanUpcallSite {
    /// The `fn` whose brace-matched body holds the call.
    enclosing_fn: String,
    /// The Lean symbol called.
    symbol: String,
    /// Whether a readiness guard on the executing PE dominates the call
    /// (`readiness_guard_dominates`).
    gated: bool,
}

/// Every reference to a Lean-emitted symbol in `code` — a strings-blanked
/// code view — for `symbol` in `exports`, resolved to the call it stands for
/// and attributed to its enclosing function.
///
/// A declaration (`fn symbol(` inside an `extern "C"` block) or a definition
/// (a host-lane stub, `extern "C" fn symbol(`) is not a call: the token is
/// present but nothing is invoked, which is the presence-versus-relation
/// mistake the PR #887 review found in the classifier scanner.  A call at
/// module scope cannot be attributed and is an error, so it fails closed.
///
/// **PR #887 review round 6: a reference that is not a call is an error
/// too.**  The round-3 scanner looked for the spelling `symbol(`, so
/// `let invoke = lean_x; unsafe { invoke(1) }` produced no site at all — the
/// aliased upcall was in neither inventory and the build passed.  Every
/// whole-identifier occurrence of an exported symbol is now classified: a
/// declaration or definition is skipped, a call (the name followed by `(`)
/// is attributed, and anything else — a `let` alias, a function-pointer
/// argument, a cast, a `use` re-export — is refused, because a readiness
/// gate cannot be attributed to a value that escapes.  Call the symbol
/// directly, under the gate.
fn lean_upcall_sites(code: &str, exports: &[&str]) -> Result<Vec<LeanUpcallSite>, String> {
    let bytes = code.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut sites = Vec::new();
    for symbol in exports {
        let mut search = 0usize;
        while let Some(hit) = code[search..].find(*symbol) {
            let at = search + hit;
            let end = at + symbol.len();
            search = end;
            // Whole identifier: neither `not_lean_x` nor `lean_x2` is `lean_x`.
            if (at > 0 && is_ident(bytes[at - 1])) || (end < bytes.len() && is_ident(bytes[end])) {
                continue;
            }
            // A declaration or definition is `fn` followed by the name.
            let mut before = at;
            while before > 0 && matches!(bytes[before - 1], b' ' | b'\t' | b'\n' | b'\r') {
                before -= 1;
            }
            let declared = before >= 2
                && &code[before - 2..before] == "fn"
                && (before == 2 || !is_ident(bytes[before - 3]));
            if declared {
                continue;
            }
            // A call is the name followed by `(`; any other reference escapes.
            let mut after = end;
            while after < bytes.len() && matches!(bytes[after], b' ' | b'\t' | b'\n' | b'\r') {
                after += 1;
            }
            if after >= bytes.len() || bytes[after] != b'(' {
                let excerpt: String = code[at..].chars().take(48).collect();
                return Err(format!(
                    "the Lean symbol `{symbol}` is referenced at byte {at} without being \
                     called (`{excerpt}…`).  An alias, a function pointer, a cast or a \
                     re-export cannot be attributed to a readiness gate; call the symbol \
                     directly, under the gate"
                ));
            }
            let Some((enclosing_fn, open, _)) = enclosing_fn_span(code, at) else {
                return Err(format!(
                    "call to the Lean symbol `{symbol}` at byte {at} is not inside any \
                     function, so its readiness gate cannot be attributed"
                ));
            };
            let gated = readiness_guard_dominates(code, open, at);
            sites.push(LeanUpcallSite {
                enclosing_fn,
                symbol: (*symbol).to_string(),
                gated,
            });
        }
    }
    Ok(sites)
}

/// Does a readiness check **control** the call at `call`?  Textual precedence
/// is not control: `let _ = lean_ready(c);` precedes a call it does not guard,
/// and an `if lean_ready(c) { … }` block closed before the call guards nothing
/// after it (PR #887 review round 3).  Two shapes count, both read off the
/// brace structure of the strings-blanked view:
///
///   * `if <cond> {` where `<cond>` contains `lean_ready(`, is not negated and
///     joins nothing with `||`, and the call sits inside that block — the
///     true branch dominates the call;
///   * `if !lean_ready(…) { … }` whose block diverges (`return`, `panic!`,
///     `fatal_halt(`, `unreachable!`) and closes before the call — the
///     fail-closed early exit dominates everything after it.
///
/// Anything else — a `match`, a `while`, a stored boolean, a disjunction — is
/// not recognised and reads as ungated, which is the fail-closed direction.
///
/// **Round 4 (PR #887): the relation is on statements, not on a region.**
/// The first cut of this function resolved the guard's block and then looked
/// for a divergence *token* inside it, and accepted any condition without
/// `||` as entailing readiness — a region-scoped presence check, which
/// `if !lean_ready(c) { if retry { return; } }` and
/// `if lean_ready(c) == false { … }` both passed.  Now the negated guard's
/// block must END in a diverging top-level statement
/// (`top_level_statements` + `statement_diverges`), and the positive guard's
/// condition must be a conjunction one of whose conjuncts is exactly the
/// `lean_ready(…)` call (`ready_condition_argument`): no comparison, no `!`,
/// no `||` anywhere.
///
/// **Round 6 (PR #887): the guard is the executing PE's.**  Both shapes
/// require the call's argument to name the executing core
/// (`ready_argument_is_executing_core`): `lean_ready(0)` on core 1 gates the
/// wrong core, and a parameter is whatever the caller sent.
fn readiness_guard_dominates(code: &str, body_open: usize, call: usize) -> bool {
    let bytes = code.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut search = body_open;
    while let Some(hit) = code[search..call].find("lean_ready(") {
        let gate = search + hit;
        search = gate + "lean_ready(".len();
        // Whole identifier: `mark_lean_ready(` is not the check.
        if gate > 0 && is_ident(bytes[gate - 1]) {
            continue;
        }
        let Some(if_at) = enclosing_if_keyword(code, body_open, gate) else {
            continue;
        };
        let Some(block_open) = block_open_after(code, gate) else {
            continue;
        };
        let Some(block_close) = matching_close_brace(code, block_open) else {
            continue;
        };
        let cond = code[if_at + 2..block_open].trim();
        // PR #887 review round 6: the guard must be the EXECUTING PE's — its
        // argument resolves to `current_core_id_from_tpidr()` inline, through
        // a `let` bound from it, or through an `assert_eq!` against it, in a
        // statement that dominates the guard.  `lean_ready(0)` on core 1 is a
        // gate on the wrong core, and a parameter is whatever the caller sent.
        let names_executing_core =
            |arg: &str| ready_argument_is_executing_core(code, body_open, if_at, arg);
        if let Some(arg) = negated_ready_call_argument(cond) {
            if !names_executing_core(arg) {
                continue;
            }
            let statements = top_level_statements(code, block_open, block_close);
            let last_diverges = statements
                .last()
                .map(|&(lo, hi)| statement_diverges(&code[lo..hi]))
                .unwrap_or(false);
            if last_diverges && block_close < call {
                return true;
            }
        } else if let Some(arg) = ready_condition_argument(cond) {
            if names_executing_core(arg) && block_open < call && call < block_close {
                return true;
            }
        }
    }
    false
}

/// PR #887 review round 6: does `arg` — the argument of a `lean_ready(…)`
/// guard whose `if` sits at `guard_at` inside the function body opening at
/// `body_open` — name the **executing PE**?  Three structural forms are
/// accepted, and nothing else:
///
///   * the call `crate::per_cpu::current_core_id_from_tpidr()` itself
///     (optionally path-shortened, cast with `as`, parenthesised);
///   * an identifier bound by a `let` whose initializer is that call, in a
///     statement that **dominates** the guard — a top-level statement of the
///     function body or of a block enclosing the guard, ending before it;
///   * an identifier compared to that call by an `assert_eq!` in such a
///     dominating statement (`debug_assert_eq!` is not accepted: a check that
///     release builds compile out guarantees nothing on hardware).
///
/// A parameter, a literal, a value from another module, or a binding in a
/// sibling block reads as *not* the executing core — the fail-closed
/// direction.  So does an identifier whose TPIDR binding a later dominating
/// statement shadows or reassigns: the last verdict wins
/// (`executing_core_verdict`).
fn ready_argument_is_executing_core(
    code: &str,
    body_open: usize,
    guard_at: usize,
    arg: &str,
) -> bool {
    if is_tpidr_core_expression(arg) {
        return true;
    }
    let ident = strip_cast_and_parens(arg);
    if ident.is_empty()
        || !ident
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_')
    {
        return false;
    }
    let Some(body_close) = matching_close_brace(code, body_open) else {
        return false;
    };
    let mut verdict = false;
    for (lo, hi) in dominating_statements(code, body_open, body_close, guard_at) {
        if let Some(latest) = executing_core_verdict(&code[lo..hi], ident) {
            verdict = latest;
        }
    }
    verdict
}

/// Is `expr`, after parentheses and a trailing `as <type>` are stripped, a
/// call of `current_core_id_from_tpidr()`?
fn is_tpidr_core_expression(expr: &str) -> bool {
    matches!(
        strip_cast_and_parens(expr),
        "crate::per_cpu::current_core_id_from_tpidr()"
            | "per_cpu::current_core_id_from_tpidr()"
            | "current_core_id_from_tpidr()"
    )
}

/// `expr` without enclosing parentheses and without trailing `as <type>`
/// casts.
fn strip_cast_and_parens(expr: &str) -> &str {
    let mut e = expr.trim();
    loop {
        if e.starts_with('(') && e.ends_with(')') && matching_close_paren(e, 0) == Some(e.len() - 1)
        {
            e = e[1..e.len() - 1].trim();
            continue;
        }
        if let Some(at) = e.rfind(" as ") {
            let cast = e[at + 4..].trim();
            if !cast.is_empty() && cast.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
                e = e[..at].trim();
                continue;
            }
        }
        return e;
    }
}

/// What the top-level statement `statement` says about `ident` as the
/// executing core.  `Some(true)`: it binds `ident` to
/// `current_core_id_from_tpidr()` (`let ident = …;`, typed or not, `mut` or
/// not) or validates it against that call (`assert_eq!(ident, …)` in either
/// order; `debug_assert_eq!` is not accepted, since a check release builds
/// compile out guarantees nothing on hardware).  `Some(false)`: it binds or
/// assigns `ident` to anything else — a shadowing `let`, a destructuring
/// pattern naming it, a plain or compound assignment.  `None`: it does not
/// touch `ident`.  Leading attribute lines (`#[cfg(…)]`) are skipped.  The
/// verdict that counts is the LAST one among the statements dominating the
/// guard (`ready_argument_is_executing_core`), so a shadow or a reassignment
/// after the TPIDR binding reads as not the executing core.
fn executing_core_verdict(statement: &str, ident: &str) -> Option<bool> {
    let text = strip_leading_attributes(statement.trim());
    let text = text.trim().trim_end_matches(';').trim();
    if let Some((pattern, init)) = let_binding_parts(text) {
        if word_occurrences(pattern, ident) == 0 {
            return None;
        }
        return Some(pattern == ident && is_tpidr_core_expression(init));
    }
    if let Some(rest) = strip_word_prefix(text, ident) {
        let rest = rest.trim_start();
        let assigns = (rest.starts_with('=') && !rest.starts_with("=="))
            || ["+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="]
                .iter()
                .any(|op| rest.starts_with(op));
        if assigns {
            return Some(false);
        }
    }
    if let Some(rest) = text.strip_prefix("assert_eq!") {
        if rest.starts_with('(') {
            let close = matching_close_paren(text, "assert_eq!".len())?;
            let inner = &text["assert_eq!(".len()..close];
            let parts = split_top_level(inner, ",");
            if parts.len() >= 2 {
                let a = strip_cast_and_parens(parts[0]);
                let b = strip_cast_and_parens(parts[1]);
                if (a == ident && is_tpidr_core_expression(b))
                    || (b == ident && is_tpidr_core_expression(a))
                {
                    return Some(true);
                }
            }
        }
    }
    None
}

/// `text` without its leading attribute lines (`#[…]`, one or more).
fn strip_leading_attributes(text: &str) -> &str {
    let mut t = text.trim_start();
    while t.starts_with("#[") {
        match t.find(']') {
            Some(end) => t = t[end + 1..].trim_start(),
            None => return t,
        }
    }
    t
}

/// `text` after a leading whole-word `word`, if it starts with one.
fn strip_word_prefix<'a>(text: &'a str, word: &str) -> Option<&'a str> {
    let rest = text.strip_prefix(word)?;
    match rest.bytes().next() {
        Some(b) if b.is_ascii_alphanumeric() || b == b'_' => None,
        _ => Some(rest),
    }
}

/// `let <pattern>[: <type>] = <init>` split into the pattern (without `mut`
/// and without its type annotation) and the initializer (without a trailing
/// `;`).  `None` when `text` is not a `let` binding with an initializer.
fn let_binding_parts(text: &str) -> Option<(&str, &str)> {
    let rest = strip_word_prefix(text.trim(), "let")?.trim_start();
    let bytes = rest.as_bytes();
    let mut depth = 0i32;
    let mut eq = None;
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'=' if depth == 0
                && bytes.get(i + 1) != Some(&b'=')
                && bytes.get(i + 1) != Some(&b'>')
                && (i == 0 || !matches!(bytes[i - 1], b'!' | b'<' | b'>' | b'=')) =>
            {
                eq = Some(i);
                break;
            }
            _ => {}
        }
    }
    let eq = eq?;
    let lhs = rest[..eq].trim();
    let lhs = strip_word_prefix(lhs, "mut")
        .map(str::trim_start)
        .unwrap_or(lhs);
    let lb = lhs.as_bytes();
    let mut cut = lhs.len();
    let mut depth = 0i32;
    for i in 0..lb.len() {
        match lb[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b':' if depth == 0 && lb.get(i + 1) != Some(&b':') && (i == 0 || lb[i - 1] != b':') => {
                cut = i;
                break;
            }
            _ => {}
        }
    }
    let pattern = lhs[..cut].trim();
    let init = rest[eq + 1..].trim().trim_end_matches(';').trim();
    Some((pattern, init))
}

/// The position of `word` among the elements of the tuple `text` — `Some(0)`
/// when `text` is `word` itself — or `None` when it is neither.
fn tuple_index_of(text: &str, word: &str) -> Option<usize> {
    let t = text.trim();
    if t == word {
        return Some(0);
    }
    if !t.starts_with('(') || matching_close_paren(t, 0) != Some(t.len() - 1) {
        return None;
    }
    split_top_level(&t[1..t.len() - 1], ",")
        .iter()
        .position(|element| element.trim() == word)
}

/// Whole-word occurrences of `word` in `text`: an occurrence bounded on both
/// sides by non-identifier bytes.  Round 6 (PR #887): the count is how a
/// scanner asks "is this the ONLY consumer" — a binding plus one scrutinee is
/// two, and a comparison, a copy or a shadow is a third.
fn word_occurrences(text: &str, word: &str) -> usize {
    let bytes = text.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut count = 0usize;
    let mut search = 0usize;
    while let Some(hit) = text[search..].find(word) {
        let at = search + hit;
        let end = at + word.len();
        search = end;
        let bounded =
            (at == 0 || !is_ident(bytes[at - 1])) && (end >= bytes.len() || !is_ident(bytes[end]));
        if bounded {
            count += 1;
        }
    }
    count
}

/// `text` with every run of whitespace collapsed to one space.
fn collapse_whitespace(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The statements that **dominate** position `at` inside the block
/// `code[body_open..=body_close]`: at every nesting level from the body
/// inward, the top-level statements that end before `at`, descending only
/// into the block statement that contains `at`.  A statement in a sibling
/// block is not returned — it need not have run.
fn dominating_statements(
    code: &str,
    body_open: usize,
    body_close: usize,
    at: usize,
) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    let mut open = body_open;
    let mut close = body_close;
    loop {
        let statements = top_level_statements(code, open, close);
        let mut container: Option<(usize, usize)> = None;
        for &(lo, hi) in &statements {
            if hi <= at {
                out.push((lo, hi));
            } else if lo <= at && at < hi {
                container = Some((lo, hi));
                break;
            }
        }
        let Some((lo, hi)) = container else {
            break;
        };
        let Some(inner_open) = block_open_after(code, lo) else {
            break;
        };
        if inner_open >= at || inner_open >= hi {
            break;
        }
        let Some(inner_close) = matching_close_brace(code, inner_open) else {
            break;
        };
        if !(inner_open < at && at < inner_close) {
            break;
        }
        open = inner_open;
        close = inner_close;
    }
    out
}

/// The argument of the bare readiness call a positive guard's condition
/// carries, when the condition entails readiness: no `||`, and a conjunction
/// (`&&` at depth zero) one of whose conjuncts is exactly the call.
fn ready_condition_argument(cond: &str) -> Option<&str> {
    if cond.contains("||") {
        return None;
    }
    split_top_level(cond, "&&")
        .into_iter()
        .find_map(bare_ready_call_argument)
}

/// The argument of `!lean_ready(…)` when `cond` is exactly that.
fn negated_ready_call_argument(cond: &str) -> Option<&str> {
    cond.trim()
        .strip_prefix('!')
        .and_then(bare_ready_call_argument)
}

/// If `expr` is exactly a `lean_ready(<arg>)` call (optionally path-qualified
/// or parenthesised, balanced, nothing after the closing parenthesis), its
/// argument text.
fn bare_ready_call_argument(expr: &str) -> Option<&str> {
    let mut e = expr.trim();
    while e.starts_with('(') && e.ends_with(')') && matching_close_paren(e, 0) == Some(e.len() - 1)
    {
        e = e[1..e.len() - 1].trim();
    }
    let rest = e
        .strip_prefix("crate::lean_ready::lean_ready(")
        .or_else(|| e.strip_prefix("lean_ready::lean_ready("))
        .or_else(|| e.strip_prefix("lean_ready("))?;
    let mut depth = 1i32;
    for (index, ch) in rest.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return rest[index + 1..]
                        .trim()
                        .is_empty()
                        .then_some(rest[..index].trim());
                }
            }
            _ => {}
        }
    }
    None
}

/// The `)` matching the `(` at `open` in `text`, if balanced.
fn matching_close_paren(text: &str, open: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (index, ch) in text[open..].char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(open + index);
                }
            }
            _ => {}
        }
    }
    None
}

/// Split `text` on `sep` at parenthesis/bracket/brace depth zero.
fn split_top_level<'a>(text: &'a str, sep: &str) -> Vec<&'a str> {
    let bytes = text.as_bytes();
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            _ if depth == 0 && text[i..].starts_with(sep) => {
                parts.push(&text[start..i]);
                i += sep.len();
                start = i;
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    parts.push(&text[start..]);
    parts
}

/// The top-level statements of the block whose `{` is at `open` and whose
/// matching `}` is at `close`, as byte spans of the block's interior.  A
/// statement ends at a `;` at depth zero, or where a depth-zero brace block
/// closes and is not continued by `else`; a trailing `;` after such a block
/// belongs to that statement; a final expression without `;` is the last
/// statement.  Parentheses, brackets and braces are tracked, and the views
/// this runs on have strings and comments blanked, so no brace inside a
/// literal can unbalance the count.
///
/// This is the view every divergence and routing question is asked on: what
/// a block does *unconditionally* is what its top-level statements say, and a
/// token nested under a conditional inside it says nothing about that.
fn top_level_statements(code: &str, open: usize, close: usize) -> Vec<(usize, usize)> {
    top_level_statements_in(code, open + 1, close)
}

/// `top_level_statements` over an arbitrary interior `[start, end)`.
fn top_level_statements_in(code: &str, start: usize, end: usize) -> Vec<(usize, usize)> {
    let bytes = code.as_bytes();
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut paren = 0i32;
    let mut stmt_start = start;
    let mut i = start;
    while i < end {
        match bytes[i] {
            b'(' | b'[' => paren += 1,
            b')' | b']' => paren -= 1,
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 && paren == 0 {
                    let mut next = i + 1;
                    while next < end && bytes[next].is_ascii_whitespace() {
                        next += 1;
                    }
                    if !code[next.min(end)..end].starts_with("else") {
                        let stmt_end = if next < end && bytes[next] == b';' {
                            next + 1
                        } else {
                            i + 1
                        };
                        out.push((stmt_start, stmt_end));
                        stmt_start = stmt_end;
                        i = stmt_end;
                        continue;
                    }
                }
            }
            b';' if depth == 0 && paren == 0 => {
                out.push((stmt_start, i + 1));
                stmt_start = i + 1;
            }
            _ => {}
        }
        i += 1;
    }
    if !code[stmt_start..end].trim().is_empty() {
        out.push((stmt_start, end));
    }
    out
}

/// Does a top-level statement diverge unconditionally?  A `return`, a
/// `panic!`, an `unreachable!`, or a call to `fatal_halt` — the four forms the
/// HAL's fail-closed paths use.  A conditional that *contains* one does not:
/// `if retry { return; }` reaches the next statement when `retry` is false.
fn statement_diverges(statement: &str) -> bool {
    let s = statement.trim().trim_end_matches(';').trim();
    s == "return"
        || s.starts_with("return ")
        || s.starts_with("return(")
        || s.starts_with("panic!(")
        || s.starts_with("unreachable!(")
        || s.starts_with("crate::cpu::fatal_halt(")
        || s.starts_with("cpu::fatal_halt(")
        || s.starts_with("fatal_halt(")
}

/// The `if` whose condition contains `at`: the nearest preceding `if` token
/// with no statement boundary (`;`, `{`, `}`) between it and `at`.
fn enclosing_if_keyword(code: &str, lo: usize, at: usize) -> Option<usize> {
    let bytes = code.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut i = at;
    while i > lo {
        i -= 1;
        match bytes[i] {
            b';' | b'{' | b'}' => return None,
            b'i' if code[i..].starts_with("if")
                && (i == 0 || !is_ident(bytes[i - 1]))
                && matches!(bytes.get(i + 2), Some(b' ' | b'(' | b'!' | b'\n' | b'\t')) =>
            {
                return Some(i);
            }
            _ => {}
        }
    }
    None
}

/// The `{` that opens the block of the condition containing `from`: the first
/// brace at parenthesis depth zero, with no `;` before it.
fn block_open_after(code: &str, from: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (index, ch) in code[from..].char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            ';' if depth == 0 => return None,
            '{' if depth == 0 => return Some(from + index),
            _ => {}
        }
    }
    None
}

/// The `}` matching the `{` at `open`.
fn matching_close_brace(code: &str, open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (index, ch) in code[open..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(open + index);
                }
            }
            _ => {}
        }
    }
    None
}

/// The names declared as functions inside `extern "C" { … }` blocks of `code`.
fn extern_block_declarations(code: &str) -> Vec<String> {
    let mut names = Vec::new();
    let mut search = 0usize;
    while let Some(hit) = code[search..].find("extern \"C\" {") {
        let open = search + hit + "extern \"C\" ".len();
        let mut depth = 0usize;
        let mut end = open;
        for (index, ch) in code[open..].char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        end = open + index;
                        break;
                    }
                }
                _ => {}
            }
        }
        let block = &code[open..end];
        let mut inner = 0usize;
        while let Some(f) = block[inner..].find("fn ") {
            let at = inner + f;
            inner = at + 3;
            if at > 0
                && (block.as_bytes()[at - 1].is_ascii_alphanumeric()
                    || block.as_bytes()[at - 1] == b'_')
            {
                continue;
            }
            let name: String = block[at + 3..]
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() && !names.contains(&name) {
                names.push(name);
            }
        }
        search = end.max(open + 1);
    }
    names
}

/// Every `@[export name]` under `dir`, recursively — the Lean-emitted symbol
/// set the HAL can call.
fn collect_lean_exports(dir: &std::path::Path, out: &mut Vec<String>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(e) => panic!(
            "Lean upcall scanner: cannot read the Lean tree at {}: {e}",
            dir.display()
        ),
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_lean_exports(&path, out);
            continue;
        }
        if path.extension().and_then(|e| e.to_str()) != Some("lean") {
            continue;
        }
        let Ok(contents) = std::fs::read_to_string(&path) else {
            continue;
        };
        for name in lean_exports_in(&lean_code_view(&contents)) {
            if !out.contains(&name) {
                out.push(name);
            }
        }
    }
}

/// **PR #889 review round 2**: the comment-free, string-free view of a Lean
/// source, byte-aligned with it — `--` line comments, nested `/- … -/` block
/// comments (docstrings and module docs included), string literals and the
/// `'"'` character literal blanked to spaces, newlines kept.  The same rules
/// `scripts/lean_code_view.py` applies for the Python-side gates.
///
/// `collect_lean_exports` read raw text, so the commented
/// `@[export lean_endpoint_call_cross_core]` that records a *retired* seam
/// counted as a live export, and a docstring could add a symbol to the gated
/// inventory that drives the readiness and declaration classification.  A gate
/// reads code; prose is not in the inventory.
fn lean_code_view(src: &str) -> String {
    let b = src.as_bytes();
    let mut out = b.to_vec();
    let is_ident = |c: u8| c.is_ascii_alphanumeric() || c == b'_' || c == b'\'' || c == b'.';
    let mut i = 0usize;
    while i < b.len() {
        if b[i] == b'-' && i + 1 < b.len() && b[i + 1] == b'-' {
            while i < b.len() && b[i] != b'\n' {
                out[i] = b' ';
                i += 1;
            }
        } else if b[i] == b'/' && i + 1 < b.len() && b[i + 1] == b'-' {
            let mut depth = 0usize;
            while i < b.len() {
                if b[i] == b'/' && i + 1 < b.len() && b[i + 1] == b'-' {
                    depth += 1;
                    out[i] = b' ';
                    out[i + 1] = b' ';
                    i += 2;
                    continue;
                }
                if b[i] == b'-' && i + 1 < b.len() && b[i + 1] == b'/' {
                    depth -= 1;
                    out[i] = b' ';
                    out[i + 1] = b' ';
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                    continue;
                }
                if b[i] != b'\n' {
                    out[i] = b' ';
                }
                i += 1;
            }
        } else if b[i] == b'"' {
            out[i] = b' ';
            i += 1;
            while i < b.len() && b[i] != b'"' {
                if b[i] == b'\\' && i + 1 < b.len() {
                    out[i] = b' ';
                    i += 1;
                }
                if b[i] != b'\n' {
                    out[i] = b' ';
                }
                i += 1;
            }
            if i < b.len() {
                out[i] = b' ';
                i += 1;
            }
        } else if b[i] == b'\''
            && i + 2 < b.len()
            && b[i + 1] == b'"'
            && b[i + 2] == b'\''
            && (i == 0 || !is_ident(b[i - 1]))
        {
            out[i] = b' ';
            out[i + 1] = b' ';
            out[i + 2] = b' ';
            i += 3;
        } else {
            i += 1;
        }
    }
    // Every byte the scan rewrote became an ASCII space, so the view is valid
    // UTF-8 exactly when the source was.
    String::from_utf8(out).expect("lean_code_view: the source was not UTF-8")
}

/// **PR #889 review round 2**: every `export <name>` attribute in `code` — a
/// Lean code view — in order of first occurrence.  The attribute list
/// `@[ … ]` is split on commas, so `@[inline, export name]` counts, and the
/// separator after `export` is any whitespace, so a line break before the
/// name counts; the old `find("@[export ")` saw neither.
fn lean_exports_in(code: &str) -> Vec<String> {
    let mut names: Vec<String> = Vec::new();
    let mut search = 0usize;
    while let Some(hit) = code[search..].find("@[") {
        let open = search + hit + 2;
        let mut depth = 1usize;
        let mut close = None;
        for (index, ch) in code[open..].char_indices() {
            match ch {
                '[' => depth += 1,
                ']' => {
                    depth -= 1;
                    if depth == 0 {
                        close = Some(open + index);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(close) = close else {
            break;
        };
        for attr in code[open..close].split(',') {
            let attr = attr.trim();
            if let Some(rest) = attr.strip_prefix("export") {
                if rest.starts_with(|c: char| c.is_whitespace()) {
                    let name: String = rest
                        .trim_start()
                        .chars()
                        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                        .collect();
                    if !name.is_empty() && !names.contains(&name) {
                        names.push(name);
                    }
                }
            }
        }
        search = close + 1;
    }
    names
}

/// Token-preserving self-check for the export collector: every mutation keeps
/// the `@[export name]` text and breaks the relation that it is *code*.
fn verify_lean_export_collector() {
    const GOOD: &str = "/-- doc -/\n@[export lean_alpha]\ndef alpha : Nat := 0\n\n\
                        @[inline, export lean_beta]\ndef beta : Nat := 1\n\n\
                        @[export\n  lean_gamma]\ndef gamma : Nat := 2\n";
    let got = lean_exports_in(&lean_code_view(GOOD));
    assert_eq!(
        got,
        vec!["lean_alpha", "lean_beta", "lean_gamma"],
        "build.rs self-check: the export collector missed a live attribute form"
    );
    assert_eq!(
        lean_code_view(GOOD).len(),
        GOOD.len(),
        "build.rs self-check: the Lean code view is not byte-aligned"
    );
    let mutations: [(&str, &str, &str, &str); 6] = [
        (
            "the attribute is commented out with `--`",
            "@[export lean_alpha]\n",
            "-- @[export lean_alpha]\n",
            "lean_alpha",
        ),
        (
            "the attribute sits inside a block comment",
            "@[export lean_alpha]\n",
            "/- @[export lean_alpha] -/\n",
            "lean_alpha",
        ),
        (
            "the attribute sits inside a nested block comment",
            "@[export lean_alpha]\n",
            "/- outer /- @[export lean_alpha] -/ still a comment -/\n",
            "lean_alpha",
        ),
        (
            "the attribute is quoted in a docstring",
            "/-- doc -/",
            "/-- doc: the former @[export lean_delta] seam -/",
            "lean_delta",
        ),
        (
            "the attribute is a string literal",
            "def alpha : Nat := 0\n",
            "def alpha : Nat := 0\ndef s : String := \"@[export lean_epsilon]\"\n",
            "lean_epsilon",
        ),
        (
            "the attribute is a trailing line comment after code",
            "def beta : Nat := 1\n",
            "def beta : Nat := 1 -- was @[export lean_zeta]\n",
            "lean_zeta",
        ),
    ];
    for (what, from, to, must_vanish) in mutations {
        assert!(
            GOOD.contains(from),
            "build.rs self-check: export-collector mutation `{what}` does not apply"
        );
        let mutated = GOOD.replacen(from, to, 1);
        assert_ne!(
            mutated, GOOD,
            "build.rs self-check: export-collector mutation `{what}` is inert"
        );
        assert!(
            mutated.contains(&format!("export {must_vanish}")),
            "build.rs self-check: export-collector mutation `{what}` DELETED the attribute; \
             the mutation must keep the token and break the relation"
        );
        let names = lean_exports_in(&lean_code_view(&mutated));
        if names.iter().any(|n| n == must_vanish) {
            panic!("build.rs self-check: the export collector read prose as code: {what}");
        }
    }
}

/// Every `.rs` file under `dir`, recursively.
fn collect_rust_sources(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(e) => panic!("Lean upcall scanner: cannot read {}: {e}", dir.display()),
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_rust_sources(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

/// **PR #887 review round 2 — derived, not enumerated**: every call from the
/// HAL into a Lean-emitted symbol consults the per-core readiness gate, or is
/// registered in `LEAN_UPCALLS_OUTSIDE_THE_GATE` with its reason.
///
/// `scan_lean_ready_gates_intact` checks the seams it is told about; this
/// scanner finds them.  The Lean symbol set is derived from the Lean tree —
/// every `@[export name]` attribute under `../../SeLe4n` — plus the
/// `lean_`-prefixed functions the HAL itself declares in `extern "C"` blocks
/// (the image's `lean_kernel_main` entry is emitted by the Lean toolchain
/// rather than an attribute).  Every `.rs` file under `src/` is read through
/// the strings-blanked code view, each call is attributed to its enclosing
/// function, and the gate must precede the call in that body.  The set of
/// gated seams found must then equal `LEAN_READY_GATED_SEAMS`, so a new seam
/// forces a table entry with its docstring and a stale entry fails the build.
/// `verify_lean_upcall_scanner` runs the token-preserving mutations first.
fn scan_lean_upcalls_readiness_gated() {
    verify_lean_extern_gating_scanner();
    verify_lean_export_collector();
    let lean_root = std::path::Path::new("../../SeLe4n");
    println!("cargo:rerun-if-changed=../../SeLe4n");
    let mut exports: Vec<String> = Vec::new();
    collect_lean_exports(lean_root, &mut exports);
    if exports.is_empty() {
        panic!(
            "Lean upcall scanner: found no `@[export …]` attribute under {} — the Lean \
             tree is the source of the symbol set, and an empty set would pass every \
             upcall unchecked.",
            lean_root.display()
        );
    }
    let mut sources: Vec<std::path::PathBuf> = Vec::new();
    collect_rust_sources(std::path::Path::new("src"), &mut sources);
    sources.sort();
    let mut views: Vec<(String, String, String)> = Vec::new();
    for path in &sources {
        let contents = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => panic!(
                "Lean upcall scanner: failed to read {}: {e}",
                path.display()
            ),
        };
        let (strings_kept, code) = rust_code_views(&contents);
        // HAL-declared `lean_*` externs join the set: the toolchain-emitted
        // entry is declared here and nowhere in the Lean sources.
        for name in extern_block_declarations(&code) {
            if name.starts_with("lean_") && !exports.contains(&name) {
                exports.push(name);
            }
        }
        views.push((
            path.to_string_lossy().replace('\\', "/"),
            code,
            strings_kept,
        ));
    }
    exports.sort();
    let export_refs: Vec<&str> = exports.iter().map(String::as_str).collect();

    let mut gated_found: Vec<(String, String, String)> = Vec::new();
    let mut ungated_found: Vec<(String, String, String)> = Vec::new();
    for (path, code, _) in &views {
        let sites = match lean_upcall_sites(code, &export_refs) {
            Ok(s) => s,
            Err(e) => panic!("Lean upcall scanner: `{path}`: {e}"),
        };
        for site in sites {
            let gated = site.gated;
            let found = (path.clone(), site.enclosing_fn, site.symbol);
            if gated {
                gated_found.push(found);
            } else {
                ungated_found.push(found);
            }
        }
    }
    // WS-RR RR5.9: the other half of the finding — a Lean symbol may be
    // declared or exported only under `hw_target`, and a host-lane stand-in of
    // the same name only under its negation.  Shares this scan's derived export
    // set and code views, so the two checks can never disagree about which
    // names are Lean symbols.
    match lean_extern_gating_status(&views, &export_refs) {
        Ok(0) => panic!(
            "WS-RR RR5.9: the extern-gating scanner found no Lean symbol declaration in \
             `src/` at all.  Every seam declares its Lean entry point somewhere; a zero \
             here means the classification stopped matching and the check passes \
             vacuously."
        ),
        Ok(_) => {}
        Err(why) => panic!("WS-RR RR5.9 regression: {why}"),
    }

    // PR #887 review round 6: the ungated calls are reconciled against the
    // exemption table by OCCURRENCE — every ungated call is covered by an
    // entry, and every entry covers exactly the calls that exist.
    let ungated_refs: Vec<(&str, &str, &str)> = ungated_found
        .iter()
        .map(|(p, f, s)| (p.as_str(), f.as_str(), s.as_str()))
        .collect();
    if let Err(why) = reconcile_upcall_exemptions(&ungated_refs, LEAN_UPCALLS_OUTSIDE_THE_GATE) {
        panic!("Lean upcall scanner: {why}");
    }
    for (p, f, sym) in &gated_found {
        let pinned = LEAN_READY_GATED_SEAMS
            .iter()
            .any(|(tp, tf, ts)| tp == p && tf == f && ts == sym);
        if !pinned {
            panic!(
                "Lean upcall scanner: `{p}`'s `fn {f}` calls `{sym}` behind the \
                 readiness gate, but the seam is not recorded in \
                 `LEAN_READY_GATED_SEAMS`.  Add it there with a comment saying what the \
                 seam commits, so the readiness contract's table keeps tracking the \
                 real call sites."
            );
        }
    }
    for (tp, tf, ts) in LEAN_READY_GATED_SEAMS {
        if !gated_found
            .iter()
            .any(|(p, f, sym)| p == tp && f == tf && sym == ts)
        {
            panic!(
                "Lean upcall scanner: `LEAN_READY_GATED_SEAMS` records `{tp}`'s `fn {tf}` \
                 calling `{ts}` behind the gate, but no such gated call was found.  The \
                 seam moved, lost its gate, or was renamed; update the table in the \
                 same change."
            );
        }
    }
}

/// PR #887 review round 6: reconcile the ungated Lean upcalls the scanner
/// found against `LEAN_UPCALLS_OUTSIDE_THE_GATE`, occurrence by occurrence.
/// `Ok(())` exactly when every `(source, fn, symbol)` group of ungated calls
/// has an entry whose count equals the group's size, and every entry's group
/// exists with exactly that size — a table row and the tree's calls have to
/// change together.
fn reconcile_upcall_exemptions(
    ungated: &[(&str, &str, &str)],
    table: &[(&str, &str, &str, usize, &str)],
) -> Result<(), String> {
    let mut groups: Vec<((&str, &str, &str), usize)> = Vec::new();
    for &(p, f, s) in ungated {
        match groups.iter_mut().find(|(key, _)| *key == (p, f, s)) {
            Some((_, n)) => *n += 1,
            None => groups.push(((p, f, s), 1)),
        }
    }
    for &(p, f, s, expected, _) in table {
        if expected == 0 {
            return Err(format!(
                "`LEAN_UPCALLS_OUTSIDE_THE_GATE` exempts zero calls of `{s}` in `{p}`'s \
                 `fn {f}`; an entry that covers nothing is a stale entry — remove it"
            ));
        }
        let found = groups
            .iter()
            .find(|(key, _)| *key == (p, f, s))
            .map(|(_, n)| *n)
            .unwrap_or(0);
        if found != expected {
            return Err(format!(
                "`LEAN_UPCALLS_OUTSIDE_THE_GATE` exempts {expected} ungated call(s) of `{s}` \
                 in `{p}`'s `fn {f}`, but {found} exist there.  A call was added without a \
                 reviewed reason of its own, or removed without retiring its entry; the \
                 count changes in the same change as the call"
            ));
        }
    }
    for ((p, f, s), n) in &groups {
        let registered = table
            .iter()
            .any(|(tp, tf, ts, _, _)| tp == p && tf == f && ts == s);
        if !registered {
            return Err(format!(
                "`{p}`'s `fn {f}` calls the Lean-emitted symbol `{s}` ({n} call(s)) without \
                 a readiness guard on the executing PE dominating the call \
                 (`if crate::lean_ready::lean_ready(<this core's TPIDR-derived id>) {{ … }}`).  \
                 A PE must never enter a Lean runtime it has not initialized.  Either gate \
                 the call — and add the seam to `LEAN_READY_GATED_SEAMS` — or, if it is the \
                 call that establishes readiness or a registered gap, add it to \
                 `LEAN_UPCALLS_OUTSIDE_THE_GATE` with its occurrence count and reason"
            ));
        }
    }
    Ok(())
}

/// PR #887 review round 6: the reconciliation is by occurrence, both ways.
fn verify_upcall_exemption_reconciliation() {
    let one_entry: &[(&str, &str, &str, usize, &str)] = &[("src/a.rs", "f", "lean_x", 1, "why")];
    let one_call: &[(&str, &str, &str)] = &[("src/a.rs", "f", "lean_x")];
    let two_calls: &[(&str, &str, &str)] =
        &[("src/a.rs", "f", "lean_x"), ("src/a.rs", "f", "lean_x")];
    let none: &[(&str, &str, &str)] = &[];
    assert!(
        reconcile_upcall_exemptions(one_call, one_entry).is_ok(),
        "exemption self-check: one registered call must reconcile: {:?}",
        reconcile_upcall_exemptions(one_call, one_entry)
    );
    assert!(
        reconcile_upcall_exemptions(two_calls, one_entry).is_err(),
        "exemption self-check: a second call in an exempt function passed on the first call's entry"
    );
    assert!(
        reconcile_upcall_exemptions(none, one_entry).is_err(),
        "exemption self-check: a stale entry passed"
    );
    let elsewhere: &[(&str, &str, &str)] = &[("src/a.rs", "g", "lean_x")];
    assert!(
        reconcile_upcall_exemptions(elsewhere, one_entry).is_err(),
        "exemption self-check: an ungated call in an unregistered function passed"
    );
    let two_entry: &[(&str, &str, &str, usize, &str)] = &[("src/a.rs", "f", "lean_x", 2, "why")];
    assert!(
        reconcile_upcall_exemptions(one_call, two_entry).is_err(),
        "exemption self-check: an entry exempting two calls passed on one"
    );
    assert!(
        reconcile_upcall_exemptions(two_calls, two_entry).is_ok(),
        "exemption self-check: two registered calls must reconcile"
    );
    let zero_entry: &[(&str, &str, &str, usize, &str)] = &[("src/a.rs", "f", "lean_x", 0, "why")];
    assert!(
        reconcile_upcall_exemptions(none, zero_entry).is_err(),
        "exemption self-check: a zero-count entry passed"
    );
}

/// Token-preserving mutations for `lean_upcall_sites`: every case keeps the
/// symbol present in the text and breaks the relation the scanner is meant to
/// see, so a scanner that had degraded to a presence check fails here before
/// it is trusted with the tree.
///
/// PR #887 review round 6: the executing-core provenance of the guard is part
/// of the relation, so every fixture that expects a gated verdict binds the
/// guard's argument from `current_core_id_from_tpidr()` the way the seams do
/// (`BIND`), and the round-3 shape — a parameter as the guard's argument —
/// is now one of the refused fixtures.
fn verify_lean_upcall_scanner() {
    let exports = ["lean_x"];
    let sites = |source: &str| {
        let (_, code) = rust_code_views(source);
        lean_upcall_sites(&code, &exports)
    };
    const BIND: &str = "    let c = crate::per_cpu::current_core_id_from_tpidr() as usize;\n";
    let seam =
        |body: &str| format!("fn seam(other: bool, retry: bool) -> u32 {{\n{BIND}{body}}}\n");
    let gated = sites(&seam(
        "    if crate::lean_ready::lean_ready(c) {\n        extern \"C\" {\n            fn lean_x(a: \
         u64) -> u32;\n        }\n        unsafe { lean_x(1) }\n    } else {\n        0\n    }\n",
    ))
    .expect("gated fixture attributes");
    assert_eq!(
        gated,
        vec![LeanUpcallSite {
            enclosing_fn: "seam".to_string(),
            symbol: "lean_x".to_string(),
            gated: true,
        }],
        "Lean upcall scanner self-check: a gated call must be found once, gated"
    );
    let declaration_only = sites(
        "fn seam() -> u32 {\n    extern \"C\" {\n        fn lean_x(a: u64) -> u32;\n    }\n    7\n}\n",
    )
    .expect("declaration fixture attributes");
    assert!(
        declaration_only.is_empty(),
        "Lean upcall scanner self-check: an `extern` declaration stood in for a call"
    );
    let stub = sites("#[no_mangle]\nextern \"C\" fn lean_x(_a: u64) -> u32 {\n    17\n}\n")
        .expect("stub fixture attributes");
    assert!(
        stub.is_empty(),
        "Lean upcall scanner self-check: a host-lane stub definition counted as a call"
    );
    let gate_after = sites(&seam(
        "    extern \"C\" {\n        fn lean_x(a: u64) -> u32;\n    }\n    let r = unsafe { lean_x(1) \
         };\n    if crate::lean_ready::lean_ready(c) {\n        r\n    } else {\n        0\n    }\n",
    ))
    .expect("late-gate fixture attributes");
    assert!(
        gate_after.len() == 1 && !gate_after[0].gated,
        "Lean upcall scanner self-check: a gate *after* the call passed as gating it"
    );
    let mention = sites("fn seam() -> u32 {\n    let _note = \"lean_x(1)\";\n    0\n}\n")
        .expect("mention fixture attributes");
    assert!(
        mention.is_empty(),
        "Lean upcall scanner self-check: a string-literal mention counted as a call"
    );
    let suffix = sites(
        "fn seam() -> u32 {\n    not_lean_x(1)\n}\nfn not_lean_x(_a: u64) -> u32 {\n    0\n}\n",
    )
    .expect("suffix fixture attributes");
    assert!(
        suffix.is_empty(),
        "Lean upcall scanner self-check: a longer identifier matched the symbol"
    );
    let prefix =
        sites("fn seam() -> u32 {\n    lean_x2(1)\n}\nfn lean_x2(_a: u64) -> u32 {\n    0\n}\n")
            .expect("prefix fixture attributes");
    assert!(
        prefix.is_empty(),
        "Lean upcall scanner self-check: a longer identifier starting with the symbol matched it"
    );
    let orphan = sites("static Y: u32 = lean_x(1);\n");
    assert!(
        orphan.is_err(),
        "Lean upcall scanner self-check: a call outside any function must fail closed"
    );
    let ungated = |source: &str, what: &str| {
        let found = sites(source).expect("fixture attributes");
        assert!(
            found.len() == 1 && !found[0].gated,
            "Lean upcall scanner self-check: {what} passed as gating the call"
        );
    };
    let gated_by = |source: &str, what: &str| {
        let found = sites(source).expect("fixture attributes");
        assert!(
            found.len() == 1 && found[0].gated,
            "Lean upcall scanner self-check: {what} was not recognised as the guard"
        );
    };
    // PR #887 review round 3: a readiness token that does not CONTROL the call.
    ungated(
        &seam("    let _ = crate::lean_ready::lean_ready(c);\n    unsafe { lean_x(1) }\n"),
        "a stored readiness value",
    );
    ungated(
        &seam(
            "    if crate::lean_ready::lean_ready(c) {\n        0\n    } else {\n        0\n    };\n    \
             unsafe { lean_x(1) }\n",
        ),
        "a readiness block closed before the call",
    );
    ungated(
        &seam(
            "    if other || crate::lean_ready::lean_ready(c) {\n        unsafe { lean_x(1) }\n    } \
             else {\n        0\n    }\n",
        ),
        "a disjunction with the readiness check",
    );
    ungated(
        &seam("    if !crate::lean_ready::lean_ready(c) {\n    }\n    unsafe { lean_x(1) }\n"),
        "a negated check whose block does not diverge",
    );
    gated_by(
        &seam(
            "    if !crate::lean_ready::lean_ready(c) {\n        return 0;\n    }\n    unsafe { \
             lean_x(1) }\n",
        ),
        "the fail-closed early return",
    );
    gated_by(
        &seam(
            "    if other && crate::lean_ready::lean_ready(c) {\n        unsafe { lean_x(1) }\n    } \
             else {\n        0\n    }\n",
        ),
        "a conjunction with the readiness check",
    );
    // PR #887 review round 4: a region-scoped presence check is still a
    // presence check.  The divergence must be the negated block's LAST
    // top-level statement, and the positive guard's condition must be the
    // readiness call itself, not any comparison on it.
    ungated(
        &seam(
            "    if !crate::lean_ready::lean_ready(c) {\n        if retry {\n            return 0;\n        \
             }\n    }\n    unsafe { lean_x(1) }\n",
        ),
        "a negated check whose divergence is nested under a condition",
    );
    ungated(
        &seam(
            "    if crate::lean_ready::lean_ready(c) == false {\n        unsafe { lean_x(1) }\n    } \
             else {\n        0\n    }\n",
        ),
        "an inverted comparison on the readiness check",
    );
    ungated(
        &seam(
            "    if crate::lean_ready::lean_ready(c) != true {\n        unsafe { lean_x(1) }\n    } \
             else {\n        0\n    }\n",
        ),
        "an inverted inequality on the readiness check",
    );
    ungated(
        &seam(
            "    let ready = crate::lean_ready::lean_ready(c);\n    if ready {\n        unsafe { \
             lean_x(1) }\n    } else {\n        0\n    }\n",
        ),
        "a readiness value consulted through a binding",
    );
    gated_by(
        &seam(
            "    if !crate::lean_ready::lean_ready(c) {\n        crate::kprintln!(\"not ready\");\n        \
             crate::cpu::fatal_halt();\n    }\n    unsafe { lean_x(1) }\n",
        ),
        "a fail-closed halt as the negated block's last statement",
    );
    gated_by(
        &seam(
            "    if (crate::lean_ready::lean_ready(c)) {\n        unsafe { lean_x(1) }\n    } else {\n        \
             0\n    }\n",
        ),
        "a parenthesised readiness check",
    );
    // PR #887 review round 6: the guard must be the EXECUTING PE's.  A
    // literal, a parameter, a `debug_assert_eq!`, an assertion after the
    // guard, a binding in a sibling block, a shadow and a reassignment all
    // keep the readiness token and break the provenance; the inline TPIDR
    // call, an `assert_eq!` before the guard, and a top-level TPIDR binding
    // dominating a guard inside a `#[cfg]` block are the accepted shapes.
    ungated(
        "fn seam() -> u32 {\n    if crate::lean_ready::lean_ready(0) {\n        unsafe { lean_x(1) }\n    \
         } else {\n        0\n    }\n}\n",
        "a readiness check on a literal core",
    );
    ungated(
        "fn seam(c: usize) -> u32 {\n    if crate::lean_ready::lean_ready(c) {\n        unsafe { lean_x(1) \
         }\n    } else {\n        0\n    }\n}\n",
        "a readiness check on a parameter",
    );
    gated_by(
        "fn seam() -> u32 {\n    if \
         crate::lean_ready::lean_ready(crate::per_cpu::current_core_id_from_tpidr() as usize) {\n        \
         unsafe { lean_x(1) }\n    } else {\n        0\n    }\n}\n",
        "an inline TPIDR-derived core",
    );
    gated_by(
        "fn seam(c: u64) -> u32 {\n    assert_eq!(c, crate::per_cpu::current_core_id_from_tpidr(), \
         \"wrong core\");\n    if crate::lean_ready::lean_ready(c as usize) {\n        unsafe { lean_x(1) \
         }\n    } else {\n        0\n    }\n}\n",
        "a parameter validated against TPIDR by `assert_eq!`",
    );
    ungated(
        "fn seam(c: u64) -> u32 {\n    debug_assert_eq!(c, crate::per_cpu::current_core_id_from_tpidr(), \
         \"wrong core\");\n    if crate::lean_ready::lean_ready(c as usize) {\n        unsafe { lean_x(1) \
         }\n    } else {\n        0\n    }\n}\n",
        "a parameter validated only by `debug_assert_eq!`",
    );
    ungated(
        "fn seam(c: u64) -> u32 {\n    let r = if crate::lean_ready::lean_ready(c as usize) {\n        \
         unsafe { lean_x(1) }\n    } else {\n        0\n    };\n    assert_eq!(c, \
         crate::per_cpu::current_core_id_from_tpidr(), \"wrong core\");\n    r\n}\n",
        "an assertion after the guard it should precede",
    );
    ungated(
        "fn seam(flag: bool) -> u32 {\n    if flag {\n        let c = \
         crate::per_cpu::current_core_id_from_tpidr() as usize;\n        let _ = c;\n    }\n    let c = \
         0usize;\n    if crate::lean_ready::lean_ready(c) {\n        unsafe { lean_x(1) }\n    } else {\n        \
         0\n    }\n}\n",
        "a TPIDR binding in a sibling block",
    );
    ungated(
        "fn seam() -> u32 {\n    let c = crate::per_cpu::current_core_id_from_tpidr() as usize;\n    let c \
         = 0usize;\n    if crate::lean_ready::lean_ready(c) {\n        unsafe { lean_x(1) }\n    } else {\n        \
         0\n    }\n}\n",
        "the executing core shadowed before the guard",
    );
    ungated(
        "fn seam() -> u32 {\n    let mut c = crate::per_cpu::current_core_id_from_tpidr() as usize;\n    c \
         = 0;\n    if crate::lean_ready::lean_ready(c) {\n        unsafe { lean_x(1) }\n    } else {\n        \
         0\n    }\n}\n",
        "the executing core reassigned before the guard",
    );
    gated_by(
        "fn seam() -> u32 {\n    let c = crate::per_cpu::current_core_id_from_tpidr() as usize;\n    \
         #[cfg(feature = \"hw_target\")]\n    {\n        if crate::lean_ready::lean_ready(c) {\n            \
         extern \"C\" {\n                fn lean_x(a: u64) -> u32;\n            }\n            return unsafe \
         { lean_x(1) };\n        }\n    }\n    0\n}\n",
        "a top-level TPIDR binding dominating a guard inside a `#[cfg]` block",
    );
    gated_by(
        "fn seam(c: u64) -> u32 {\n    #[cfg(feature = \"hw_target\")]\n    assert_eq!(\n        c,\n        \
         crate::per_cpu::current_core_id_from_tpidr(),\n        \"wrong core\"\n    );\n    #[cfg(feature = \
         \"hw_target\")]\n    {\n        if crate::lean_ready::lean_ready(c as usize) {\n            return \
         unsafe { lean_x(1) };\n        }\n    }\n    0\n}\n",
        "an attribute-prefixed `assert_eq!` dominating a guard inside a `#[cfg]` block",
    );
    // PR #887 review round 6: a reference that is not a call fails closed.
    let alias = |source: &str, what: &str| {
        assert!(
            sites(source).is_err(),
            "Lean upcall scanner self-check: {what} produced no site and passed"
        );
    };
    alias(
        "fn seam() -> u32 {\n    let invoke = lean_x;\n    unsafe { invoke(1) }\n}\n",
        "a `let` alias of the symbol",
    );
    alias(
        "fn seam() -> u32 {\n    call_through(lean_x)\n}\n",
        "the symbol passed as a function pointer",
    );
    alias(
        "fn seam() -> usize {\n    lean_x as usize\n}\n",
        "the symbol cast to an address",
    );
    alias("pub use crate::ffi::lean_x;\n", "a re-export of the symbol");
    verify_upcall_exemption_reconciliation();
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
    // Identifier questions read the STRING-BLANKED view: a name inside
    // a literal is a mention, not a call. See `rust_code_views`.
    let (_, stripped) = rust_code_views(&contents);

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
        "pub const LOCK_THEOREM_COUNT: usize = 22",
        "pub const LOCK_BRIDGE_BUILD_ANCHOR:",
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
    // Identifier questions read the STRING-BLANKED view: a name inside
    // a literal is a mention, not a call. See `rust_code_views`.
    let (_, stripped) = rust_code_views(&contents);

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

/// **WS-SM SM5.B.7**: verify `src/ffi.rs` still declares the per-core
/// context-switch FFI seam (`ffi_switch_to_thread` + `ffi_per_core_current_thread`).
/// The Lean `@[extern]` declarations in `SeLe4n/Platform/FFI.lean` resolve
/// against these exports at the verified-kernel hardware build's link step;
/// pinning them at elaboration time forces the contract earlier than the
/// link-time failure would.
fn scan_ffi_rs_exposes_switch_to_thread_exports() {
    let path = "src/ffi.rs";
    println!("cargo:rerun-if-changed={path}");
    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => panic!("WS-SM SM5.B.7 scanner: failed to read {path}: {e}"),
    };

    // Strip line comments so the needles match only real declarations.
    // Identifier questions read the STRING-BLANKED view: a name inside
    // a literal is a mention, not a call. See `rust_code_views`.
    let (_, stripped) = rust_code_views(&contents);

    let required_ffi_symbols = [
        "pub extern \"C\" fn ffi_switch_to_thread(",
        "pub extern \"C\" fn ffi_per_core_current_thread(",
    ];
    for needle in required_ffi_symbols {
        if !stripped.contains(needle) {
            panic!(
                "WS-SM SM5.B.7 regression: `{path}` no longer declares `{needle}`.  \
                 The verified-kernel hardware build expects the per-core \
                 context-switch FFI seam to remain reachable via \
                 `#[no_mangle] pub extern \"C\"`.  If you removed the export \
                 deliberately, also remove the corresponding `@[extern]` \
                 declaration in `SeLe4n/Platform/FFI.lean` and the Lean typed \
                 wrapper in `SeLe4n/Kernel/Concurrency/Runtime.lean` (in lockstep)."
            );
        }
    }
}

/// **WS-SM SM5.I** (commit-coupled shadow clock — PR #880 follow-up): verify
/// the shadow-advance seam holds on both sides of the crate.
///
/// 1. `ffi.rs` must declare `ffi_timer_advance_tick_count` — the export the
///    Lean tick entry (`perCoreTimerTickEntry`, whose `@[extern]` declaration
///    resolves against it at the verified-kernel hardware build's link step)
///    calls iff the committed step advanced the model clock.  Dropping it
///    would only surface at that future link step; pin it at elaboration.
/// 2. `timer.rs::per_core_timer_tick_isr` must NOT have regrown an
///    invocation-time `increment_tick_count` call — an ISR-side increment
///    counts invocations rather than commits, which is exactly the drift
///    (pre-readiness offsets, failed entries counted) the commit-coupled
///    design exists to make impossible.  Checked on the ISR's brace-matched
///    body over comment-stripped text, like the lean-ready gate scanner.
fn scan_ffi_rs_exposes_timer_shadow_advance_export() {
    let strip = |contents: &str| -> String {
        contents
            .lines()
            .map(|line| {
                if let Some(idx) = line.find("//") {
                    &line[..idx]
                } else {
                    line
                }
            })
            .collect::<Vec<_>>()
            .join("\n")
    };

    let ffi_path = "src/ffi.rs";
    println!("cargo:rerun-if-changed={ffi_path}");
    let ffi_stripped = match std::fs::read_to_string(ffi_path) {
        Ok(s) => strip(&s),
        Err(e) => panic!("WS-SM SM5.I shadow-clock scanner: failed to read {ffi_path}: {e}"),
    };
    let needle = "pub extern \"C\" fn ffi_timer_advance_tick_count(";
    if !ffi_stripped.contains(needle) {
        panic!(
            "WS-SM SM5.I regression: `{ffi_path}` no longer declares `{needle}`.  \
             The Lean tick entry's commit-coupled shadow advance \
             (`ffiTimerAdvanceTickCount`) resolves against this export at the \
             verified-kernel hardware build's link step; without it the \
             `TICK_COUNT` shadow can never advance.  If you removed the export \
             deliberately, also remove the `@[extern]` declaration in \
             `SeLe4n/Platform/FFI.lean` and rework `perCoreTimerTickEntry` \
             (in lockstep)."
        );
    }

    let timer_path = "src/timer.rs";
    println!("cargo:rerun-if-changed={timer_path}");
    let timer_stripped = match std::fs::read_to_string(timer_path) {
        Ok(s) => strip(&s),
        Err(e) => panic!("WS-SM SM5.I shadow-clock scanner: failed to read {timer_path}: {e}"),
    };
    let decl = "fn per_core_timer_tick_isr(";
    let decl_idx = timer_stripped.find(decl).unwrap_or_else(|| {
        panic!(
            "WS-SM SM5.I shadow-clock scanner: `{timer_path}` no longer declares \
             `fn per_core_timer_tick_isr` — update this scanner in lockstep with \
             the seam move."
        )
    });
    let open_rel = timer_stripped[decl_idx..].find('{').unwrap_or_else(|| {
        panic!(
            "WS-SM SM5.I shadow-clock scanner: `{timer_path}`'s \
             `fn per_core_timer_tick_isr` has no body block after its declaration."
        )
    });
    let body_start = decl_idx + open_rel;
    let mut depth = 0usize;
    let mut body_end = None;
    for (i, ch) in timer_stripped[body_start..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    body_end = Some(body_start + i + 1);
                    break;
                }
            }
            _ => {}
        }
    }
    let body = &timer_stripped[body_start..body_end.unwrap_or_else(|| {
        panic!(
            "WS-SM SM5.I shadow-clock scanner: unbalanced braces while extracting \
             `{timer_path}`'s `fn per_core_timer_tick_isr` body."
        )
    })];
    if body.contains("increment_tick_count") {
        panic!(
            "WS-SM SM5.I regression: `{timer_path}`'s `per_core_timer_tick_isr` \
             calls `increment_tick_count` again.  The `TICK_COUNT` shadow is \
             commit-coupled: its sole incrementer is \
             `ffi::ffi_timer_advance_tick_count`, driven by the Lean entry iff \
             the committed step advanced the model clock.  An ISR-side \
             increment counts invocations rather than commits and reintroduces \
             the pre-readiness / failed-entry drift; remove it."
        );
    }
}

/// **WS-SM SM2** (closes the queued_rw_lock protocol contract): verify
/// that `queued_rw_lock.rs` retains the invariants that make the ticket
/// protocol deadlock-free.
///
/// This scanner previously pinned the MCS queue's guards — the
/// mode-encoded four-state `parked` machine and the stale-self tail
/// detection. That queue **deadlocked** (v0.32.147: the lock free,
/// `state == 0`, every core parked) and was replaced at v0.32.148 by a
/// ticket protocol with no linked structure at all, so those patterns no
/// longer exist to pin. Their scanner entries are gone rather than
/// weakened: they described machinery that is not there.
///
/// What replaces them is the property the whole deadlock-freedom
/// argument rests on, plus the exclusion invariant that outlived the
/// rewrite:
///
/// 1. **The ticket is passed on exactly once per issued ticket.** Both
///    `now_serving.fetch_add` (in `pass_turn`) and `next_ticket.fetch_add`
///    (in `take_ticket`) must be present. A regression that advances
///    `now_serving` by a store of some computed value can regress it and
///    admit two cores at once; one that drops the advance entirely
///    strands every later ticket — which is precisely how the MCS
///    version failed, with the duty to admit the next waiter resting on a
///    chain reference that could be stale or destroyed.
///
/// 2. **Writer admission is a CAS from exactly zero, never `fetch_or`.**
///    Carried over unchanged: `fetch_or` sets the writer bit even when
///    reader bits are set, producing the `WRITER_BIT | reader_bits` state
///    that directly violates writer-readers exclusion.
fn scan_queued_rw_lock_protocol_intact() {
    let path = "src/queued_rw_lock.rs";
    println!("cargo:rerun-if-changed={path}");
    let contents = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(_) => return,
    };

    // Strip comments to avoid false positives from documentation.
    let mut stripped = String::new();
    for line in contents.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with("*") {
            continue;
        }
        stripped.push_str(line);
        stripped.push('\n');
    }

    // Check (1): the ticket hand-off primitives.
    let required = [
        (
            "self.now_serving.fetch_add(1",
            "the ticket is passed on by a monotone fetch_add",
        ),
        (
            "self.next_ticket.fetch_add(1",
            "tickets are issued by a monotone fetch_add",
        ),
    ];
    for (needle, why) in required {
        if !stripped.contains(needle) {
            panic!(
                "WS-SM SM2 protocol regression: `{path}` no longer contains \
                 `{needle}` ({why}).  `now_serving` must be advanced exactly \
                 once per issued ticket, unconditionally, by whoever that \
                 ticket admits — a reader on entry, a writer on exit.  That \
                 single property is the whole deadlock-freedom argument: it \
                 is what guarantees every issued ticket is eventually \
                 served.  The MCS queue this replaced had no such guarantee \
                 and deadlocked with the lock free.  If you intend to \
                 restructure the hand-off, update this scanner in lockstep \
                 and re-run the contention harness (400 attempts, 4 cores) \
                 plus the full suite 100x."
            );
        }
    }

    // Check (2): forbidden fetch_or for writer admission.
    let forbidden_pattern = "self.state.fetch_or(WRITER_BIT";
    if stripped.contains(forbidden_pattern) {
        panic!(
            "WS-SM SM2 protocol regression: `{path}` contains the forbidden \
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

/// **WS-RR RR1.4** regression guard: verify the outer-shareable TLBI
/// wrappers in `tlb.rs` keep their fail-closed FEAT_TLBIOS guard and
/// their balanced `.arch_extension` bracket.
///
/// `TLBI VMALLE1OS / VAE1OS / ASIDE1OS / VALE1OS` are FEAT_TLBIOS
/// (ARMv8.4-A).  Cortex-A76 — the core in the RPi5's BCM2712 — is
/// ARMv8.2-A and does not implement them, so on the project's first
/// hardware target the encodings are UNDEFINED.  Two properties keep
/// that from becoming a runtime trap, and neither is visible to any
/// compiler on the host:
///
///  1. Each wrapper calls `require_feat_tlbios()` before its `asm!`,
///     diverging into `cpu::fatal_halt()` when the PE cannot execute
///     the instruction.  Dropping the call would substitute an
///     undefined-instruction exception for a diagnosed halt.
///  2. Each `*OS` mnemonic sits inside a `.arch_extension tlb-rmi` …
///     `.arch_extension notlb-rmi` pair.  Dropping the *enable* breaks
///     the aarch64 build (loudly); dropping the *restore* leaves the
///     extension enabled for every later inline-asm block in the same
///     object, so a v8.4-only instruction elsewhere would silently
///     assemble.  That one fails open, which is why the balance is
///     pinned here rather than left to the aarch64 build to notice.
///
/// The scan runs over the comment-stripped source, so a docstring
/// mentioning `require_feat_tlbios` cannot satisfy it.  Both properties are
/// checked as ORDER, not presence: a guard below the `asm!` and a reversed
/// `.arch_extension` pair each leave every token in place while breaking
/// what the check means.  See CLAUDE.md's "A presence check is not a
/// relation check".
fn scan_tlb_rs_outer_shareable_guards_intact() {
    let path = "src/tlb.rs";
    println!("cargo:rerun-if-changed={path}");

    let contents = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            panic!("WS-RR RR1.4 scanner: failed to read {path}: {e}");
        }
    };

    // TWO views, byte-aligned with each other and with the file (see
    // `rust_code_views`).  `templates` keeps string contents, because the
    // assembly this scanner checks -- the `tlbi` mnemonics and the
    // `.arch_extension` bracket -- lives inside `asm!` template strings.
    // `code` blanks them, because an identifier inside a string is a
    // mention and must not satisfy a check that the wrapper CALLS its
    // guard: with one view for both, `let _note = "require_feat_tlbios()";`
    // stood in for the call and the scanner passed (PR #883 review round 3).
    let (templates, code) = rust_code_views(&contents);
    let stripped = &code;

    // The fail-closed helper itself must exist and must diverge.
    if !stripped.contains("fn require_feat_tlbios()") {
        panic!(
            "WS-RR RR1.4 regression: `{path}` no longer defines \
             `require_feat_tlbios()`.  It is the fail-closed guard that \
             keeps a `SharingDomain::Outer` binding from executing an \
             UNDEFINED instruction on a PE without FEAT_TLBIOS \
             (Cortex-A76 / RPi5).  See the `tlb.rs` module docstring, \
             section \"FEAT_TLBIOS is not baseline\"."
        );
    }
    // The guard must DIVERGE on the negative branch, and that is checked
    // inside the helper's own body rather than as a file-wide token.
    // `stripped.contains("fatal_halt()")` was satisfied by any occurrence
    // anywhere in `tlb.rs`, so neutering the helper to `return;` while a
    // `fatal_halt()` remained elsewhere in the file passed cleanly -- the
    // per-wrapper ordering checks then proved only that an ineffective
    // helper was called before the `asm!` (PR #883 review, round 2).
    let guard_body = enclosing_fn_body(stripped, "fn require_feat_tlbios()").unwrap_or_else(|| {
        panic!(
            "WS-RR RR1.4 scanner: could not delimit the body of \
                 `{path}::require_feat_tlbios`.  If the helper was \
                 restructured, update this scanner so the fail-closed \
                 contract stays pinned."
        )
    });
    let negative_branch =
        braced_block_after(guard_body, "if !has_feat_tlbios()").unwrap_or_else(|| {
            panic!(
                "WS-RR RR1.4 regression: `{path}::require_feat_tlbios` no \
                 longer branches on `if !has_feat_tlbios()`.  The guard's \
                 whole purpose is to act when the probe says the feature \
                 is ABSENT; a differently-shaped condition is not \
                 something this scanner can verify, so it must be \
                 re-pinned deliberately."
            )
        });
    // The call must be UNCONDITIONAL within that branch, which means it has
    // to sit at the branch's own statement level.  `contains` cannot see
    // that: it is satisfied by a `fatal_halt()` nested inside any construct,
    // including one whose condition is the negation of the branch's own --
    //
    //     if !has_feat_tlbios() { if has_feat_tlbios() { fatal_halt(); } }
    //
    // -- which keeps every token the check searched for and diverges on
    // exactly the PEs that do not need it (PR #883 review round 3).  So
    // nested blocks are removed and the remaining top-level statements are
    // what must reach the call.
    let top_level = statements_at_block_level(negative_branch);
    let halt_at = top_level.find("fatal_halt()");
    let escapes_first = halt_at.is_some_and(|at| top_level[..at].contains("return"));
    if halt_at.is_none() || escapes_first {
        panic!(
            "WS-RR RR1.4 regression: the `if !has_feat_tlbios()` branch of \
             `{path}::require_feat_tlbios` does not unconditionally diverge \
             into `cpu::fatal_halt()`.\n\
             Branch body: {negative_branch:?}\n\
             At the branch's own statement level (nested blocks removed): \
             {top_level:?}\n\
             The guard must DIVERGE when FEAT_TLBIOS is absent.  Returning \
             normally leaves the caller to execute the UNDEFINED `TLBI \
             *OS` encoding, and falling back to the inner-shareable \
             variant would service only the inner domain while the caller \
             asked for the outer one -- leaving live stale translations on \
             the PEs outside it.\n\
             A `fatal_halt()` reached only from inside a nested `if`, \
             `match` or loop is not something this scanner can prove \
             executes, so it is rejected rather than accepted: the guard \
             must be re-pinned deliberately if it is ever restructured."
        );
    }

    // Every `*OS` wrapper must call the guard before its `asm!`.
    //
    // The list below is a FLOOR, not the source of truth: the wrappers that
    // actually need the guard are derived from the mnemonics `tlb.rs`
    // emits, so a fifth `*OS` wrapper added later is guarded from the day
    // it is written.  A hand-written list cannot see a wrapper that does
    // not exist yet -- the hole the TLBI gate had for its own local-wrapper
    // enumeration (PR #883 review round 4).
    let derived_os_wrappers = outer_shareable_emitters(&templates, &code);
    for name in &derived_os_wrappers {
        if !OS_WRAPPERS.contains(&name.as_str()) {
            panic!(
                "WS-RR RR1.4 regression: `{path}::{name}` emits a `TLBI \
                 *OS` mnemonic but is not in this scanner's OS_WRAPPERS \
                 list, so its FEAT_TLBIOS guard is never checked.\n\
                 Every outer-shareable wrapper must call \
                 `require_feat_tlbios()` before its `asm!`; add the name \
                 here so the ordering and `.arch_extension` bracket are \
                 pinned for it too."
            );
        }
    }

    const OS_WRAPPERS: [&str; 4] = [
        "tlbi_vmalle1os",
        "tlbi_vae1os",
        "tlbi_aside1os",
        "tlbi_vale1os",
    ];
    for name in OS_WRAPPERS {
        let signature = format!("pub fn {name}(");
        let Some(start) = stripped.find(&signature) else {
            panic!(
                "WS-RR RR1.4 regression: `{path}` no longer defines \
                 `pub fn {name}`.  The four outer-shareable wrappers are \
                 the only production route to the FEAT_TLBIOS \
                 instructions; if one was renamed, rename it in this \
                 scanner too so the guard stays pinned."
            );
        };
        // Top-level function bodies in this file end at a `}` in column
        // zero, so the next such line bounds the body.
        let body_start = start + signature.len();
        let body_end = stripped[body_start..]
            .find("\n}\n")
            .map(|i| body_start + i)
            .unwrap_or(stripped.len());
        let body = &stripped[body_start..body_end];

        let upper = name.trim_start_matches("tlbi_").to_ascii_uppercase();

        // POSITION, not mere presence.  A refactor that moved the guard
        // below the `asm!` would leave the call in the body and satisfy a
        // `contains` check, while the PE executed the UNDEFINED encoding
        // before ever reaching the fail-closed halt (PR #883 review).
        let guard_at = body.find("require_feat_tlbios()");
        let asm_at = body.find("asm!");
        match (guard_at, asm_at) {
            (None, _) => panic!(
                "WS-RR RR1.4 regression: `{path}::{name}` no longer calls \
                 `require_feat_tlbios()` before its `asm!`.\n\
                 `TLBI {upper}` is FEAT_TLBIOS (ARMv8.4-A) and is NOT \
                 implemented by Cortex-A76, the core in the RPi5's \
                 BCM2712.  Without the guard, a platform binding whose \
                 `sharingDomain` is `.outer` executes an UNDEFINED \
                 encoding instead of halting with a diagnosis."
            ),
            (Some(_), None) => panic!(
                "WS-RR RR1.4 scanner: `{path}::{name}` no longer contains \
                 an `asm!` block.  If the wrapper was rewritten, update \
                 this scanner so the FEAT_TLBIOS contract stays pinned."
            ),
            (Some(guard), Some(asm)) if guard > asm => panic!(
                "WS-RR RR1.4 regression: `{path}::{name}` calls \
                 `require_feat_tlbios()` AFTER its `asm!`, so the \
                 fail-closed guard runs only once the UNDEFINED `TLBI \
                 {upper}` has already executed.  The guard must precede \
                 the instruction it protects."
            ),
            _ => {}
        }

        // The `.arch_extension` bracket is checked PER WRAPPER and in
        // order.  File-wide counts cannot see a pair that is mismatched
        // across two wrappers, or a restore that precedes its own enable.
        // Read from the STRING-KEEPING view at the same byte offsets: the
        // assembler directives and the mnemonic are template contents, and
        // the identifier view has blanked them.
        let template_body = &templates[body_start..body_end];
        let enable_at = template_body.find(".arch_extension tlb-rmi");
        let restore_at = template_body.find(".arch_extension notlb-rmi");
        let mnemonic = format!("tlbi {}", upper.to_ascii_lowercase());
        let mnemonic_at = template_body.find(&mnemonic);
        match (enable_at, mnemonic_at, restore_at) {
            (Some(enable), Some(instr), Some(restore)) if enable < instr && instr < restore => {}
            (enable, instr, restore) => panic!(
                "WS-RR RR1.4 regression: `{path}::{name}` no longer wraps \
                 `{mnemonic}` in an ordered `.arch_extension tlb-rmi` … \
                 `notlb-rmi` pair (enable: {enable:?}, mnemonic: \
                 {instr:?}, restore: {restore:?}, as byte offsets in the \
                 function body).\n\
                 Without the enable the aarch64 build fails loudly; \
                 without the restore the extension stays live for every \
                 later inline-asm block in the same object, so a v8.4-only \
                 instruction added elsewhere would assemble silently and \
                 trap on the ARMv8.2-A target.  That direction fails OPEN, \
                 which is why the order is pinned rather than the count."
            ),
        }
    }

    // File-wide totals as well, so a stray enable outside any wrapper --
    // which the per-wrapper checks above cannot see -- is still caught.
    // Counted over the template view: the directives are string contents.
    let enables = templates.matches(".arch_extension tlb-rmi").count();
    let restores = templates.matches(".arch_extension notlb-rmi").count();
    if enables != OS_WRAPPERS.len() || restores != OS_WRAPPERS.len() {
        panic!(
            "WS-RR RR1.4 regression: `{path}` has {enables} \
             `.arch_extension tlb-rmi` enable(s) and {restores} \
             `notlb-rmi` restore(s); expected {expected} of each — one \
             pair per outer-shareable wrapper.\n\
             A pair outside the four wrappers leaves FEAT_TLBIOS \
             mnemonics assemblable for inline asm this scanner does not \
             inspect.",
            expected = OS_WRAPPERS.len(),
        );
    }
}

/// **WS-RR RR1.6**: choose an assembler that can build the three `.S`
/// sources for the *target* architecture, not the host's.
///
/// `cc`'s default search finds no cross compiler for
/// `aarch64-unknown-none` on a typical x86 host and falls back to the
/// bare `cc` on `PATH`.  That silently hands `boot.S`, `vectors.S` and
/// `trap.S` to an x86 assembler, which reports every ARM64 mnemonic as
/// "no such instruction" — 54 errors from `boot.S` alone, all of which
/// look like broken assembly and are entirely an artefact of the
/// toolchain choice.  Diagnosing that once is cheap; diagnosing it on
/// every fresh clone is not, so the choice is made here.
///
/// ## Order of precedence
///
/// 1. **An explicit compiler wins.**  If the environment already names a
///    compiler for this target in a variable `cc` itself consults
///    (`CC_<target>`, `TARGET_CC`, `CC`), this function does nothing and
///    leaves `cc` to honour it.  A developer who has pointed the build at
///    a specific toolchain must not have it silently replaced.
/// 2. **`CROSS_COMPILE` is applied, not merely detected.**  It is the
///    conventional toolchain *prefix* and `cc` does **not** read it, so
///    returning early on it left `cc` to fall back to the host compiler
///    -- the failure this function exists to prevent.  The prefix is
///    expanded (`<prefix>gcc`, then `cc`, then `clang`), probed, and
///    installed via `build.compiler`.  A prefix that cannot assemble for
///    the target warns and falls through rather than being honoured
///    blindly or ignored.
/// 3. **Otherwise, probe candidates in order** and take the first that
///    actually assembles a trivial aarch64 translation unit:
///    the bare `cc` (only when the host is already aarch64, where it is
///    the native compiler), then the conventional bare-metal and
///    Linux cross prefixes, then `clang`, which is multi-target by
///    construction and needs only the `--target` flag `cc` already
///    passes it.
///
/// The probe compiles rather than merely checking for the binary on
/// `PATH`: a name being present says nothing about whether that build
/// of it has an AArch64 backend, and an assembler chosen on presence
/// alone reproduces exactly the failure this function exists to avoid.
///
/// If no candidate works, the panic names the target and lists what to
/// install, because "error occurred in cc-rs" with a wall of x86
/// assembler diagnostics is not an actionable message.
fn select_cross_assembler(build: &mut cc::Build) {
    let target = std::env::var("TARGET").unwrap_or_default();
    let host = std::env::var("HOST").unwrap_or_default();

    // 1a. Respect an explicit override.  These are the variables `cc`
    // ITSELF consults, so if any is set it has already decided and this
    // function must not second-guess it.
    let target_underscores = target.replace('-', "_");
    let cc_consulted = [
        format!("CC_{target}"),
        format!("CC_{target_underscores}"),
        "TARGET_CC".to_string(),
        "CC".to_string(),
    ];
    let mut overridden = false;
    for var in &cc_consulted {
        println!("cargo:rerun-if-env-changed={var}");
        if std::env::var_os(var).is_some() {
            overridden = true;
        }
    }
    if overridden {
        println!(
            "sele4n-hal: assembler selection deferred to the environment \
             (one of {cc_consulted:?} is set)"
        );
        return;
    }

    // 1b. `CROSS_COMPILE` is the conventional toolchain PREFIX, and `cc`
    // does NOT consult it.  Treating it as an override -- returning and
    // leaving `cc` to honour it -- was wrong in the one direction that
    // matters: `cc` resumed its default lookup, which on an x86 host is
    // the bare `cc`, which is exactly the host-assembler fallback this
    // whole function exists to prevent.  A developer who sets
    // `CROSS_COMPILE=aarch64-linux-gnu-` got the host assembler and 54
    // errors that look like broken ARM64 assembly (PR #883 review round
    // 5).
    //
    // So the prefix is APPLIED rather than merely detected: expanded to a
    // concrete compiler and probed like any other candidate.  If it does
    // not assemble for the target the probe falls through with a warning
    // rather than silently using it -- the developer named a toolchain,
    // and being told it cannot build this target is more useful than
    // either honouring it blindly or ignoring them.
    println!("cargo:rerun-if-env-changed=CROSS_COMPILE");
    if let Some(prefix) = std::env::var_os("CROSS_COMPILE") {
        let prefix = prefix.to_string_lossy().into_owned();
        for suffix in ["gcc", "cc", "clang"] {
            let candidate = format!("{prefix}{suffix}");
            if probe_assembles_aarch64(&candidate, &target) {
                println!(
                    "sele4n-hal: assembling .S sources for {target} with \
                     `{candidate}` (from CROSS_COMPILE={prefix})"
                );
                build.compiler(&candidate);
                return;
            }
        }
        println!(
            "cargo:warning=sele4n-hal: CROSS_COMPILE={prefix} names a \
             toolchain whose gcc/cc/clang cannot assemble for {target}; \
             falling through to the standard probe."
        );
    }

    // 2. Probe candidates.  `cc` is only a candidate when the host is
    // itself aarch64 — there it is the native compiler and the right
    // first choice; on an x86 host it is precisely the wrong answer.
    let host_is_aarch64 = host.starts_with("aarch64");
    let mut candidates: Vec<&str> = Vec::new();
    if host_is_aarch64 {
        candidates.push("cc");
    }
    candidates.extend([
        // Bare-metal (newlib / no-OS) cross toolchains.
        "aarch64-none-elf-gcc",
        "aarch64-elf-gcc",
        // Linux cross toolchains: their assembler is the same GNU as,
        // and these sources never link against a libc.
        "aarch64-linux-gnu-gcc",
        "aarch64-none-linux-gnu-gcc",
        // Multi-target by construction; `cc` passes it `--target`.
        "clang",
    ]);

    for candidate in &candidates {
        if probe_assembles_aarch64(candidate, &target) {
            println!("sele4n-hal: assembling .S sources for {target} with `{candidate}`");
            build.compiler(candidate);
            return;
        }
    }

    panic!(
        "WS-RR RR1.6: no assembler on PATH can build the AArch64 sources \
         for target `{target}`.\n\
         Tried, in order: {candidates:?}.\n\
         \n\
         Install one of:\n\
         - `clang` (any recent build; it is multi-target and needs no \
         extra packages)\n\
         - the `gcc-aarch64-linux-gnu` package (Debian/Ubuntu)\n\
         - a bare-metal `aarch64-none-elf` toolchain\n\
         \n\
         Or point the build at a specific one by exporting \
         `CC_{target_underscores}=<compiler>`.\n\
         \n\
         Without this, `cc` would fall back to the host `cc` and hand \
         ARM64 assembly to an x86 assembler."
    );
}

/// **WS-RR RR1.6**: can `candidate` assemble an AArch64 translation unit
/// for `target`?
///
/// Compiles a one-instruction `.S` file rather than checking `PATH` or
/// parsing `--version`: the question is whether this build of the tool
/// has an AArch64 backend, and only asking it to produce an object file
/// answers that.  A missing binary surfaces as a spawn error and is
/// reported as "cannot assemble", which is the correct answer for the
/// caller.
///
/// The probe writes into `OUT_DIR`, so it leaves nothing behind in the
/// source tree and is discarded with the rest of the build directory.
fn probe_assembles_aarch64(candidate: &str, target: &str) -> bool {
    use std::path::PathBuf;

    let Ok(out_dir) = std::env::var("OUT_DIR") else {
        // No OUT_DIR means we are not running under cargo; refuse to
        // guess rather than probing into the source tree.
        return false;
    };
    let out_dir = PathBuf::from(out_dir);

    let src = out_dir.join("rr1_assembler_probe.S");
    // `nop` is valid AArch64 and invalid on x86-family assemblers only
    // in combination with the `.arch` directive, so pin the ISA
    // explicitly: `.arch armv8-a` is rejected outright by an assembler
    // without an AArch64 backend, which is exactly the discrimination
    // this probe needs.  `msr daifset` additionally requires the A64
    // system-register parser, so a probe that passes really can handle
    // the sources.
    let probe_source = ".arch armv8-a\n.text\n.globl rr1_assembler_probe\nrr1_assembler_probe:\n    msr daifset, #0xf\n    nop\n    ret\n";
    if std::fs::write(&src, probe_source).is_err() {
        return false;
    }

    let obj = out_dir.join(format!(
        "rr1_assembler_probe_{}.o",
        candidate.replace(['/', '\\', '.'], "_")
    ));

    let mut cmd = std::process::Command::new(candidate);
    // `cc` passes clang an explicit `--target`; mirror that here so the
    // probe exercises the same configuration the real build will use.
    // GCC cross compilers encode their target in the binary name and
    // reject the flag, so it is added only for clang-like names.
    if candidate.contains("clang") && !target.is_empty() {
        cmd.arg(format!("--target={target}"));
    }
    cmd.arg("-c")
        .arg(&src)
        .arg("-o")
        .arg(&obj)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());

    let ok = matches!(cmd.status(), Ok(status) if status.success());
    let _ = std::fs::remove_file(&obj);
    ok
}

/// **WS-RR RR1.4**: the body of a top-level `fn` in a scanned source.
///
/// Returns the text between the signature and the closing `}` that sits in
/// column zero.  Scanners in this file need to ask questions *about a
/// function* -- "does this branch diverge", "does the guard precede the
/// `asm!`" -- and a file-wide `contains` cannot answer either: it is
/// satisfied by any occurrence anywhere, including one in a different
/// function entirely.  See CLAUDE.md's "A presence check is not a relation
/// check".
fn enclosing_fn_body<'a>(source: &'a str, signature: &str) -> Option<&'a str> {
    let start = source.find(signature)? + signature.len();
    let end = source[start..].find("\n}\n").map(|i| start + i)?;
    Some(&source[start..end])
}

/// **WS-RR RR1.12**: functions in `tlb.rs` that emit a `TLBI *OS` mnemonic.
///
/// Derived from the template view (the mnemonic is `asm!` template
/// content) and attributed through the identifier view's brace-matched
/// function bodies, which are byte-aligned with it.  A wrapper emitting an
/// outer-shareable invalidation from outside any function cannot be
/// attributed, so it panics rather than passing unchecked.
fn outer_shareable_emitters(templates: &str, code: &str) -> Vec<String> {
    let mut found: Vec<String> = Vec::new();
    let bytes = templates.as_bytes();
    let mut at = 0usize;
    while let Some(hit) = templates[at..].find("tlbi ") {
        let start = at + hit;
        // Must begin an assembly statement, not sit inside an identifier.
        let preceded_ok =
            start == 0 || matches!(bytes[start - 1], b' ' | b'\t' | b'\n' | b';' | b'"');
        at = start + 5;
        if !preceded_ok {
            continue;
        }
        let operation: String = templates[at..]
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric())
            .collect();
        if !operation.to_ascii_lowercase().ends_with("os") {
            continue;
        }
        let name = enclosing_fn_name(code, start);
        match name {
            Some(owner) => {
                if !found.contains(&owner) {
                    found.push(owner);
                }
            }
            None => panic!(
                "WS-RR RR1.4 scanner: `src/tlb.rs` emits `tlbi {operation}` \
                 outside any function, so the FEAT_TLBIOS guard cannot be \
                 attributed to a wrapper. Move the emission into a named \
                 wrapper."
            ),
        }
    }
    found
}

/// **WS-RR RR1.12**: the innermost `fn` whose brace-matched body contains
/// `offset`, or `None` at module scope.
fn enclosing_fn_name(code: &str, offset: usize) -> Option<String> {
    enclosing_fn_span(code, offset).map(|(name, _, _)| name)
}

/// The innermost `fn` whose brace-matched body contains `offset`, with the
/// byte offsets of that body's opening and closing braces — the span a
/// scanner needs to ask whether a guard precedes a call *in the same body*.
fn enclosing_fn_span(code: &str, offset: usize) -> Option<(String, usize, usize)> {
    let bytes = code.as_bytes();
    let mut best: Option<(String, usize, usize)> = None;
    let mut search = 0usize;
    while let Some(hit) = code[search..].find("fn ") {
        let at = search + hit;
        search = at + 3;
        if at > 0 && (bytes[at - 1].is_ascii_alphanumeric() || bytes[at - 1] == b'_') {
            continue;
        }
        let name: String = code[at + 3..]
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        if name.is_empty() {
            continue;
        }
        let Some(open) = code[at..].find('{').map(|i| at + i) else {
            continue;
        };
        // A `;` before the brace means a bodyless declaration.
        if code[at..open].contains(';') {
            continue;
        }
        let mut depth = 0usize;
        let mut end = open;
        for (index, ch) in code[open..].char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        end = open + index;
                        break;
                    }
                }
                _ => {}
            }
        }
        if open < offset && offset < end && best.as_ref().is_none_or(|(_, s, _)| open > *s) {
            best = Some((name, open, end));
        }
    }
    best
}

/// **WS-RR RR1.12**: the assembly code view for the `.S` sources.
///
/// The `.S` files are preprocessed by a C compiler, so BOTH `//` and
/// `/* */` open comments there.  Thirteen scanners in this file carried a
/// line-based `//`-only stripper; a `/* */` splitting a token left it
/// invisible to them, exactly as it did to the TLBI containment gate.
/// Byte-aligned by blanking to spaces, which also splices a token that a
/// comment interrupts back together, as `cpp` does for the assembler.
///
/// C block comments do not nest, unlike Rust's.
fn asm_code_view(contents: &str) -> String {
    let bytes = contents.as_bytes();
    let mut out = bytes.to_vec();
    let mut index = 0usize;
    while index < bytes.len() {
        let end = if bytes[index..].starts_with(b"//") {
            bytes[index..]
                .iter()
                .position(|&b| b == b'\n')
                .map_or(bytes.len(), |p| index + p)
        } else if bytes[index..].starts_with(b"/*") {
            match contents[index + 2..].find("*/") {
                Some(offset) => index + 2 + offset + 2,
                None => bytes.len(),
            }
        } else {
            index += 1;
            continue;
        };
        for byte in out.iter_mut().take(end).skip(index) {
            if *byte != b'\n' {
                *byte = b' ';
            }
        }
        index = end;
    }
    String::from_utf8(out).expect("blanking preserves UTF-8")
}

/// **WS-RR RR1.12**: pin `rust_code_views`, because a stripper that stops
/// stripping fails SILENTLY -- every scanner reading it keeps reporting a
/// clean tree.
///
/// Each witness KEEPS the token it is about and changes only the relation:
/// the `//` moves inside a string, the identifier moves inside a string,
/// the brace moves inside a literal.  A witness that deletes the token is
/// passed by the line-based stripper this replaced, and so certifies
/// nothing (CLAUDE.md, "Test a gate by breaking the relation, not by
/// deleting the token").
fn verify_rust_code_views() {
    let case = |label: &str, source: &str, in_templates: &[&str], not_in_code: &[&str]| {
        let (templates, code) = rust_code_views(source);
        assert_eq!(
            templates.len(),
            source.len(),
            "WS-RR RR1.12: `{label}` -- template view is not byte-aligned"
        );
        assert_eq!(
            code.len(),
            source.len(),
            "WS-RR RR1.12: `{label}` -- code view is not byte-aligned"
        );
        for needle in in_templates {
            assert!(
                templates.contains(needle),
                "WS-RR RR1.12: `{label}` -- template view lost {needle:?}\n\
                 view: {templates:?}"
            );
        }
        for needle in not_in_code {
            assert!(
                !code.contains(needle),
                "WS-RR RR1.12: `{label}` -- code view kept {needle:?}, which \
                 is inside a string literal and is a mention, not a call\n\
                 view: {code:?}"
            );
        }
    };

    // An assembler comment and an instruction as sibling template lines on
    // ONE source line: the shape a line-based stripper deletes.
    case(
        "asm template comment does not hide the next template line",
        "asm!(\"// note\", \"tlbi vae1os, {0}\");\n",
        &["tlbi vae1os"],
        &["tlbi vae1os"],
    );
    // An identifier inside a string is a mention: it must not satisfy a
    // check that the code CALLS it.
    case(
        "an identifier in a string is not a call",
        "let _note = \"require_feat_tlbios()\";\nfoo();\n",
        &["require_feat_tlbios()"],
        &["require_feat_tlbios()"],
    );
    // An `extern "C"` ABI string is syntax and must survive the blanked
    // view, or every scanner asserting that an export still exists breaks.
    let (_, code) = rust_code_views("pub extern \"C\" fn handle_irq() { let s = \"data\"; }\n");
    assert!(
        code.contains("extern \"C\" fn handle_irq"),
        "WS-RR RR1.12: an `extern` ABI string was blanked: {code:?}"
    );
    assert!(
        !code.contains("data"),
        "WS-RR RR1.12: an ordinary string survived the blanked view: {code:?}"
    );

    // A real comment is blanked in BOTH views.
    let (templates, code) = rust_code_views("let a = 1; // secret\n");
    assert!(
        !templates.contains("secret") && !code.contains("secret"),
        "WS-RR RR1.12: a real `//` comment survived the views"
    );
    // Raw strings, escapes and nested block comments.
    let (templates, _) = rust_code_views("let s = r#\"a \" b // c\"#;\n");
    assert!(
        templates.contains("a \" b // c"),
        "WS-RR RR1.12: raw string body did not survive the template view"
    );
    let (_, code) = rust_code_views("let s = \"a\\\" // still string\"; let t = 1;\n");
    assert!(
        code.contains("let t = 1;"),
        "WS-RR RR1.12: an escaped quote ended the string early"
    );
    let (_, code) = rust_code_views("/* outer /* inner */ still */ let a = 1;\n");
    assert!(
        code.contains("let a = 1;") && !code.contains("still"),
        "WS-RR RR1.12: nested block comment mishandled"
    );
    // A lifetime is code, not a char literal; mistaking it swallows the
    // rest of the file.
    let (_, code) = rust_code_views("fn f<'a>(x: &'a str) -> &'a str { x }\n");
    assert!(
        code.contains("-> &'a str { x }"),
        "WS-RR RR1.12: a lifetime was lexed as a char literal: {code:?}"
    );
    // A brace inside a literal must not desynchronise block nesting.
    let (_, code) = rust_code_views("fn a() { let s = \"}\"; done(); }\n");
    assert_eq!(
        statements_at_block_level(&code).trim(),
        "fn a()",
        "WS-RR RR1.12: a brace inside a string literal closed the block"
    );
}

/// **WS-RR RR1.12**: the two Rust code views this build script scans.
///
/// Returns `(strings_kept, strings_blanked)`.  Both blank every comment;
/// they differ in whether a string literal's contents survive.  Both are
/// BYTE-ALIGNED with `contents` -- comment and string bytes are replaced by
/// spaces rather than removed, newlines preserved -- so an offset found in
/// one view names the same position in the other and in the original file,
/// and the two can be compared directly.
///
/// The distinction is load-bearing in both directions, and the line-based
/// stripper this replaces got both wrong:
///
///   * an `asm!` template is DATA the assembler consumes, so `tlbi vae1os`
///     and `.arch_extension tlb-rmi` must survive.  Truncating a line at
///     its first `//` deletes them whenever a sibling template line carries
///     an assembler comment.
///   * an identifier inside a string is a MENTION, not a call, so
///     `let _note = "require_feat_tlbios()";` must not satisfy the check
///     that the wrapper calls its guard.  It did: the scanner accepted a
///     `tlbi_vae1os` whose guard call had been replaced by that string,
///     which is the fail-open direction on the check that keeps an
///     UNDEFINED instruction off a Cortex-A76.
///
/// This mirrors `scripts/rust_code_view.py`, which serves the Python-side
/// gates; the two exist separately only because a build script cannot
/// import Python.  `verify_rust_code_views()` pins the semantics here.
fn rust_code_views(contents: &str) -> (String, String) {
    let src = contents.as_bytes();
    let mut kept = src.to_vec();
    let mut blanked = src.to_vec();
    let blank = |buffer: &mut [u8], from: usize, to: usize| {
        for byte in buffer.iter_mut().take(to).skip(from) {
            if *byte != b'\n' {
                *byte = b' ';
            }
        }
    };

    let mut i = 0usize;
    while i < src.len() {
        // Line comment.
        if src[i] == b'/' && i + 1 < src.len() && src[i + 1] == b'/' {
            let end = src[i..]
                .iter()
                .position(|&b| b == b'\n')
                .map_or(src.len(), |p| i + p);
            blank(&mut kept, i, end);
            blank(&mut blanked, i, end);
            i = end;
            continue;
        }
        // Block comment, nested.
        if src[i] == b'/' && i + 1 < src.len() && src[i + 1] == b'*' {
            let start = i;
            let mut depth = 0usize;
            while i < src.len() {
                if src[i..].starts_with(b"/*") {
                    depth += 1;
                    i += 2;
                } else if src[i..].starts_with(b"*/") {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    i += 1;
                }
            }
            blank(&mut kept, start, i);
            blank(&mut blanked, start, i);
            continue;
        }
        // Raw string: r"…", r#"…"#, br#"…"#, cr#"…"#.
        if let Some((body_start, body_end, end)) = raw_string_at(src, i) {
            blank(&mut blanked, body_start, body_end);
            i = end;
            continue;
        }
        // Ordinary, byte and C strings.
        if let Some((body_start, body_end, end)) = quoted_string_at(src, i) {
            // An `extern "C"` ABI string is SYNTAX, not data. Blanking it
            // turns `pub extern "C" fn f` into `pub extern " " fn f`, and
            // a scanner asserting that a required export still exists then
            // reports it missing -- or, worse, a differently-shaped check
            // reports it present when it is gone. ABI strings stay in both
            // views.
            if !preceded_by_keyword(src, i, b"extern") {
                blank(&mut blanked, body_start, body_end);
            }
            i = end;
            continue;
        }
        // Char literal (a lifetime such as `'a` is code and is left alone).
        if src[i] == b'\'' {
            if let Some(end) = char_literal_end(src, i) {
                blank(&mut blanked, i + 1, end - 1);
                i = end;
                continue;
            }
        }
        i += 1;
    }
    (
        String::from_utf8(kept).expect("blanking preserves UTF-8"),
        String::from_utf8(blanked).expect("blanking preserves UTF-8"),
    )
}

/// Is the token immediately before `at` exactly `keyword`?
fn preceded_by_keyword(src: &[u8], at: usize, keyword: &[u8]) -> bool {
    let mut end = at;
    while end > 0 && src[end - 1].is_ascii_whitespace() {
        end -= 1;
    }
    if end < keyword.len() || &src[end - keyword.len()..end] != keyword {
        return false;
    }
    let before = end - keyword.len();
    before == 0 || !(src[before - 1].is_ascii_alphanumeric() || src[before - 1] == b'_')
}

/// Start of body, end of body, and end of literal for a raw string at `at`.
fn raw_string_at(src: &[u8], at: usize) -> Option<(usize, usize, usize)> {
    let mut cursor = at;
    if matches!(src.get(cursor), Some(b'b' | b'c')) {
        cursor += 1;
    }
    if src.get(cursor) != Some(&b'r') {
        return None;
    }
    // A preceding identifier byte means this is part of a longer name.
    if at > 0 && (src[at - 1].is_ascii_alphanumeric() || src[at - 1] == b'_') {
        return None;
    }
    cursor += 1;
    let hash_start = cursor;
    while src.get(cursor) == Some(&b'#') {
        cursor += 1;
    }
    if src.get(cursor) != Some(&b'"') {
        return None;
    }
    let hashes = cursor - hash_start;
    let body_start = cursor + 1;
    let mut scan = body_start;
    while scan < src.len() {
        // The length bound is part of the terminator test, not an
        // afterthought: `take(hashes)` over a short tail yields fewer
        // elements and `all` is vacuously true, so without it a `"` near
        // end-of-file would close a raw string whose hashes are not there.
        if src[scan] == b'"'
            && scan + 1 + hashes <= src.len()
            && src[scan + 1..scan + 1 + hashes].iter().all(|&b| b == b'#')
        {
            return Some((body_start, scan, scan + 1 + hashes));
        }
        scan += 1;
    }
    panic!("WS-RR RR1.12: unterminated raw string at byte {at}");
}

/// Start of body, end of body, and end of literal for a `"`-string at `at`.
fn quoted_string_at(src: &[u8], at: usize) -> Option<(usize, usize, usize)> {
    let quote = if src[at] == b'"' {
        at
    } else if matches!(src[at], b'b' | b'c')
        && src.get(at + 1) == Some(&b'"')
        && !(at > 0 && (src[at - 1].is_ascii_alphanumeric() || src[at - 1] == b'_'))
    {
        at + 1
    } else {
        return None;
    };
    let body_start = quote + 1;
    let mut scan = body_start;
    while scan < src.len() {
        match src[scan] {
            b'\\' => scan += 2,
            b'"' => return Some((body_start, scan, scan + 1)),
            _ => scan += 1,
        }
    }
    panic!("WS-RR RR1.12: unterminated string at byte {at}");
}

/// End offset of the char literal at `at`, or `None` for a lifetime.
///
/// `'a'` closes after one character or one escape; `'a` in `&'a str` or
/// `'outer: loop` never does.
fn char_literal_end(src: &[u8], at: usize) -> Option<usize> {
    let mut scan = at + 1;
    if src.get(scan) == Some(&b'\\') {
        scan += 2;
        while scan < src.len() && src[scan] != b'\'' {
            scan += 1;
        }
        return (src.get(scan) == Some(&b'\'')).then_some(scan + 1);
    }
    // Step over one whole UTF-8 scalar.
    scan += 1;
    while scan < src.len() && (src[scan] & 0xC0) == 0x80 {
        scan += 1;
    }
    (src.get(scan) == Some(&b'\'')).then_some(scan + 1)
}

/// **WS-RR RR1.4**: `block` with every nested `{...}` removed.
///
/// What remains is the block's OWN statement level -- the statements that
/// run unconditionally when the block is entered.  The distinction is the
/// whole content of a divergence check: a `fatal_halt()` anywhere inside
/// the block satisfies `contains`, but only one at this level is reached
/// on every path through it.
///
/// Removal, not extraction: an unbalanced block (which cannot occur in
/// source the compiler has already accepted, since this scanner runs on
/// `tlb.rs` at build time) leaves the tail dropped, which makes the result
/// *shorter* and so fails the caller's check rather than passing it.
fn statements_at_block_level(block: &str) -> String {
    let mut depth = 0usize;
    let mut out = String::with_capacity(block.len());
    for ch in block.chars() {
        match ch {
            '{' => depth += 1,
            '}' => depth = depth.saturating_sub(1),
            _ if depth == 0 => out.push(ch),
            _ => {}
        }
    }
    out
}

/// **WS-RR RR1.4**: the brace-delimited block introduced by `header`.
///
/// Brace-matched rather than delimited by the next `}`, so a nested block
/// inside the branch does not truncate it.  String and char literals are
/// not tracked: the scanned bodies are guard clauses, not parsers, and a
/// stray brace in a literal would make the block *shorter*, which fails
/// the caller's check rather than passing it -- the safe direction.
fn braced_block_after<'a>(source: &'a str, header: &str) -> Option<&'a str> {
    let header_at = source.find(header)?;
    let open = header_at + source[header_at..].find('{')?;
    let mut depth = 0usize;
    for (offset, ch) in source[open..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(&source[open + 1..open + offset]);
                }
            }
            _ => {}
        }
    }
    None
}

/// PR #887 review round 3: **the not-ready abort path halts on hardware, and
/// the fallback frame is host-only.**
///
/// An EL0 abort leaves `ELR_EL1` on the faulting instruction, so a status
/// frame published by a not-ready core would be `eret`ed straight back into
/// the same abort — the wedge RR4 removed, reintroduced on the fallback.  The
/// relation this pins, on `deliver_fault`'s body: inside its
/// `#[cfg(feature = "hw_target")]` block the readiness guard's true branch
/// halts (the delivered arm), the text *after* that branch — the not-ready
/// path — calls `halt_abort_before_lean_ready(` and publishes no frame, and
/// every `set_return_frame(` outside the block sits under
/// `#[cfg(not(feature = "hw_target"))]`.  Presence is not enough on any of
/// the three: the helper called from the ready branch, a frame written before
/// the halt, or the host attribute dropped all keep every token, and
/// `verify_abort_fallback_scanner` runs exactly those mutations.
fn scan_trap_rs_abort_fallback_halts() {
    let path = "src/trap.rs";
    let raw = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("build.rs: cannot read `{path}`: {e}"));
    if let Err(why) = abort_fallback_status(&raw) {
        panic!("PR #887 review round 3 regression: in `{path}`, {why}");
    }
}

/// The relation behind `scan_trap_rs_abort_fallback_halts`, on a source
/// text: `Ok(())` or the first reason it does not hold.  Reads the
/// strings-blanked view for structure and the strings-kept view for the two
/// `cfg` attributes, which are literals.
fn abort_fallback_status(raw: &str) -> Result<(), String> {
    let (kept, stripped) = rust_code_views(raw);
    let sig = stripped
        .find("fn deliver_fault(")
        .ok_or_else(|| "no `fn deliver_fault(`".to_string())?;
    let open = block_open_after(&stripped, sig)
        .ok_or_else(|| "`deliver_fault` has no body".to_string())?;
    let close = matching_close_brace(&stripped, open)
        .ok_or_else(|| "`deliver_fault`'s body is unbalanced".to_string())?;
    let hw_attr = "#[cfg(feature = \"hw_target\")]";
    let host_attr = "#[cfg(not(feature = \"hw_target\"))]";
    let attr_at = open
        + kept[open..=close]
            .find(hw_attr)
            .ok_or_else(|| "`deliver_fault` has no `hw_target` block".to_string())?;
    let hw_open = block_open_after(&stripped, attr_at)
        .ok_or_else(|| "the `hw_target` attribute is not followed by a block".to_string())?;
    let hw_close = matching_close_brace(&stripped, hw_open)
        .ok_or_else(|| "the `hw_target` block is unbalanced".to_string())?;
    let guard_at = hw_open
        + stripped[hw_open..hw_close]
            .find("if crate::lean_ready::lean_ready(")
            .ok_or_else(|| "the `hw_target` block has no readiness guard".to_string())?;
    let ready_open = block_open_after(&stripped, guard_at)
        .ok_or_else(|| "the readiness guard has no block".to_string())?;
    let ready_close = matching_close_brace(&stripped, ready_open)
        .ok_or_else(|| "the readiness guard's block is unbalanced".to_string())?;
    let ready_branch = &stripped[ready_open..=ready_close];
    // Round 4 (PR #887): both halts are UNCONDITIONAL TERMINAL statements —
    // the last top-level statement of the delivered arm is the SM10.1 halt,
    // and the not-ready tail is exactly one statement, the helper call.  A
    // halt nested under `if frame.x0() == 0 { … }` keeps the token and lets
    // the function return on hardware, which is the wedge this pins against.
    let ready_statements = top_level_statements(&stripped, ready_open, ready_close);
    let ready_last = ready_statements
        .last()
        .map(|&(lo, hi)| stripped[lo..hi].trim())
        .unwrap_or("");
    if !(statement_diverges(ready_last) && ready_last.contains("fatal_halt(")) {
        return Err(
            "the delivered arm (the readiness guard's true branch) does not END in the \
                    unconditional `fatal_halt()` that stands in for the SM10.1 successor \
                    install"
                .to_string(),
        );
    }
    if ready_branch.contains("halt_abort_before_lean_ready(") {
        return Err(
            "`halt_abort_before_lean_ready(` sits inside the readiness guard's true \
                    branch; it is the NOT-ready path's halt and must follow that branch"
                .to_string(),
        );
    }
    let tail = &stripped[ready_close + 1..hw_close];
    let tail_statements = top_level_statements_in(&stripped, ready_close + 1, hw_close);
    let tail_is_the_halt = tail_statements.len() == 1
        && stripped[tail_statements[0].0..tail_statements[0].1]
            .trim()
            .starts_with("halt_abort_before_lean_ready(");
    if !tail_is_the_halt {
        return Err(
            "the not-ready path of the `hw_target` block (after the readiness guard's \
                    branch) is not exactly one unconditional `halt_abort_before_lean_ready(…)` \
                    statement — a not-ready core would return through the faulting instruction"
                .to_string(),
        );
    }
    if tail.contains("set_return_frame(") {
        return Err(
            "the not-ready path of the `hw_target` block publishes a return frame; an \
                    abort's frame is `eret`ed back into the abort"
                .to_string(),
        );
    }
    let body_kept = &kept[open..=close];
    let mut from = 0usize;
    while let Some(rel) = body_kept[from..].find("set_return_frame(") {
        let at = open + from + rel;
        from += rel + "set_return_frame(".len();
        if at > hw_open && at < hw_close {
            return Err("the `hw_target` block publishes a return frame".to_string());
        }
        let line_start = kept[..at].rfind('\n').map(|i| i + 1).unwrap_or(0);
        let before = kept[open..line_start].trim_end();
        if !before.ends_with(host_attr) {
            return Err(format!(
                "a `set_return_frame(` in `deliver_fault` is not immediately under \
                 `{host_attr}`; the fallback frame is the host lane's observable and must \
                 never be compiled for hardware"
            ));
        }
    }
    let helper = stripped
        .find("fn halt_abort_before_lean_ready(")
        .ok_or_else(|| "no `fn halt_abort_before_lean_ready(`".to_string())?;
    let helper_open = block_open_after(&stripped, helper)
        .ok_or_else(|| "`halt_abort_before_lean_ready` has no body".to_string())?;
    let helper_close = matching_close_brace(&stripped, helper_open)
        .ok_or_else(|| "`halt_abort_before_lean_ready`'s body is unbalanced".to_string())?;
    if !stripped[helper..helper_open].contains("-> !") {
        return Err("`halt_abort_before_lean_ready` does not diverge (`-> !`)".to_string());
    }
    if !stripped[helper_open..=helper_close].contains("fatal_halt(") {
        return Err("`halt_abort_before_lean_ready` does not call `fatal_halt(`".to_string());
    }
    Ok(())
}

/// Token-preserving self-check for `abort_fallback_status`: the fixture is
/// no thinner than `deliver_fault` itself, and every mutation keeps the tokens
/// a presence check would look for.
fn verify_abort_fallback_scanner() {
    const GOOD: &str = r#"
#[allow(unused_variables)]
fn deliver_fault(frame: &mut TrapFrame, fallback_discriminant: u32) {
    #[cfg(feature = "hw_target")]
    {
        let core_id = crate::per_cpu::current_core_id_from_tpidr();
        if crate::lean_ready::lean_ready(core_id as usize) {
            extern "C" {
                fn lean_handle_fault(core_id: u64, esr: u64);
            }
            let (esr, elr) = (frame.esr_el1, frame.elr_el1);
            // SAFETY: the gate just checked; the entry lock serialises the commit.
            crate::kernel_entry::with_kernel_entry(core_id as usize, || unsafe {
                lean_handle_fault(core_id, esr);
            });
            crate::kprintln!("[core {}] fault delivered; halting (ESR=0x{:016x})", core_id, esr);
            crate::cpu::fatal_halt();
        }
        // A frame cannot fail-close an abort: halt.
        halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);
    }
    #[cfg(not(feature = "hw_target"))]
    frame.set_return_frame(crate::svc_dispatch::error_frame_regs(fallback_discriminant));
}

#[cfg_attr(not(feature = "hw_target"), allow(dead_code))]
fn halt_abort_before_lean_ready(core_id: u64, esr: u64, elr: u64) -> ! {
    crate::kprintln!("[core {}] EL0 abort before ready (ESR=0x{:016x} ELR=0x{:016x})", core_id, esr, elr);
    crate::cpu::fatal_halt()
}
"#;
    if let Err(why) = abort_fallback_status(GOOD) {
        panic!("build.rs self-check: the good abort-fallback fixture was refused: {why}");
    }
    let mutations: [(&str, &str, &str); 9] = [
        (
            "the not-ready halt moved into the ready branch (token kept, path broken)",
            "            crate::cpu::fatal_halt();\n        }\n        // A frame cannot fail-close an abort: halt.\n        halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);\n",
            "            halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);\n            crate::cpu::fatal_halt();\n        }\n",
        ),
        (
            "a frame published on the not-ready path before the halt (both tokens kept)",
            "        halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);\n",
            "        frame.set_return_frame(crate::svc_dispatch::error_frame_regs(fallback_discriminant));\n        halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);\n",
        ),
        (
            "the host-only attribute dropped from the fallback frame (token kept, compiled for hardware)",
            "    #[cfg(not(feature = \"hw_target\"))]\n    frame.set_return_frame(",
            "    frame.set_return_frame(",
        ),
        (
            "the not-ready halt reduced to a string literal",
            "        halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);\n",
            "        let _why = \"halt_abort_before_lean_ready(core_id, esr, elr)\";\n",
        ),
        (
            "the not-ready halt reduced to a comment",
            "        halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);\n",
            "        // halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);\n",
        ),
        (
            "the delivered arm returning instead of halting (helper token kept)",
            "            crate::cpu::fatal_halt();\n        }\n",
            "            return;\n        }\n",
        ),
        // PR #887 review round 4: the halts must be unconditional terminal
        // statements, not tokens somewhere in their region.
        (
            "the not-ready halt nested under a condition",
            "        halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);\n",
            "        if frame.x0() == 0 {\n            halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);\n        }\n",
        ),
        (
            "the delivered arm's halt nested under a condition",
            "            crate::cpu::fatal_halt();\n        }\n",
            "            if core_id == 0 {\n                crate::cpu::fatal_halt();\n            }\n        }\n",
        ),
        (
            "a statement after the not-ready halt",
            "        halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);\n    }\n",
            "        halt_abort_before_lean_ready(core_id, frame.esr_el1, frame.elr_el1);\n        let _ = frame.x0();\n    }\n",
        ),
    ];
    for (what, from, to) in mutations {
        assert!(
            GOOD.contains(from),
            "build.rs self-check: abort-fallback mutation `{what}` does not apply"
        );
        let mutated = GOOD.replacen(from, to, 1);
        assert_ne!(
            mutated, GOOD,
            "build.rs self-check: abort-fallback mutation `{what}` is inert"
        );
        if abort_fallback_status(&mutated).is_ok() {
            panic!(
                "build.rs self-check: `abort_fallback_status` accepted a broken fixture: {what}"
            );
        }
    }
}

/// PR #887 review round 5: **a delivered syscall fault halts the core.**
///
/// The Lean dispatch answers a capability fault it delivered with outcome
/// tag 2 (`SyscallOutcome.faulted`), distinct from a block (tag 1): the
/// model restarts that caller *at* the `SVC` on its handler's reply, so the
/// `Blocked` arm's sentinel — which resumes the caller past the `SVC` —
/// would run a thread the model has waiting on a fault.  Two relations, on
/// the statement-level view: `dispatch_svc` decodes tag 2 to
/// `SvcOutcome::Faulted`, and the handler's `Faulted` arm is exactly one
/// unconditional statement, the diverging `halt_after_delivered_syscall_fault(`.
fn scan_trap_rs_faulted_outcome_halts() {
    let trap = std::fs::read_to_string("src/trap.rs")
        .unwrap_or_else(|e| panic!("build.rs: cannot read `src/trap.rs`: {e}"));
    let dispatch = std::fs::read_to_string("src/svc_dispatch.rs")
        .unwrap_or_else(|e| panic!("build.rs: cannot read `src/svc_dispatch.rs`: {e}"));
    if let Err(why) = faulted_outcome_status(&trap, &dispatch) {
        panic!("PR #887 review round 5 regression: {why}");
    }
}

/// The relation behind `scan_trap_rs_faulted_outcome_halts`, on the two
/// source texts: `Ok(())` or the first reason it does not hold.
///
/// **PR #887 review round 7: the decode and the arm are located, not found.**
/// The round-5 cut asked whether `svc_dispatch.rs` *contained*
/// `2 => Ok(SvcOutcome::Faulted),` — a whole-file presence check a helper or
/// a `#[cfg(test)]` block satisfies while `dispatch_svc`'s own match maps
/// tag 2 to `Blocked` — and took the *first textual* `SvcOutcome::Faulted) =>`
/// arm in the handler, which a decoy match nested under a condition supplies
/// while the live arm publishes a frame.  Both questions are now asked of the
/// statement that answers them (`dispatch_decodes_faulted`,
/// `handler_faulted_arm_halts`).
fn faulted_outcome_status(trap_raw: &str, dispatch_raw: &str) -> Result<(), String> {
    let (_, dispatch) = rust_code_views(dispatch_raw);
    dispatch_decodes_faulted(&dispatch)?;
    let (_, trap) = rust_code_views(trap_raw);
    handler_faulted_arm_halts(&trap)?;
    svc_arm_readiness_gate_status(&trap, &dispatch)
}

/// The `sync_class::SVC` arm of `handle_synchronous_exception`'s terminal
/// routing match, as `(block_open, block_close, handler_body_open)`.
fn svc_arm_block(trap: &str) -> Result<(usize, usize, usize), String> {
    let needle = "fn handle_synchronous_exception(";
    if trap.matches(needle).count() != 1 {
        return Err(format!(
            "`trap.rs` declares `fn handle_synchronous_exception(` {} times",
            trap.matches(needle).count()
        ));
    }
    let handler = trap.find(needle).unwrap_or(0);
    let body_open = block_open_after(trap, handler)
        .ok_or_else(|| "`handle_synchronous_exception` has no body".to_string())?;
    let body_close = matching_close_brace(trap, body_open)
        .ok_or_else(|| "`handle_synchronous_exception`'s body is unbalanced".to_string())?;
    let routing = terminal_routing_match(trap, body_open, body_close)?;
    let routing_text = trap[routing.0..routing.1].trim_start();
    let routing_at = routing.1 - routing_text.len();
    let arms = match_arm_spans(routing_text)
        .ok_or_else(|| "the terminal routing match could not be parsed".to_string())?;
    let svc: Vec<&MatchArm> = arms
        .iter()
        .filter(|arm| routing_text[arm.pattern.0..arm.pattern.1].trim() == "sync_class::SVC")
        .collect();
    if svc.len() != 1 {
        return Err(format!(
            "the terminal routing match has {} `sync_class::SVC` arms",
            svc.len()
        ));
    }
    let (svc_open, svc_end) = (routing_at + svc[0].body.0, routing_at + svc[0].body.1);
    if trap.as_bytes().get(svc_open) != Some(&b'{') {
        return Err("the `sync_class::SVC` arm is not a block".to_string());
    }
    Ok((svc_open, svc_end - 1, body_open))
}

/// **PR #889 review**: in the SVC arm, the readiness gate precedes **every**
/// outcome.  The relation, on the statement-level view of the arm:
///
///   * exactly one top-level statement is `if !crate::lean_ready::lean_ready(<core>) { … }`,
///     with no `||` or `&&` in the condition, and `<core>` names the executing
///     PE (`ready_argument_is_executing_core`: `current_core_id_from_tpidr()`
///     inline, or a binding a dominating statement makes from it);
///   * that statement comes **before** the `let dispatched = …` binding — so
///     before the full-width narrowing of `x7`, the prefilters inside
///     `dispatch_svc`, and the unknown-syscall delivery;
///   * its block's last top-level statement is a call to
///     `crate::svc_dispatch::halt_syscall_before_lean_ready(…)`; and
///   * that helper (in `svc_dispatch.rs`) is declared `-> !` and ends in
///     `fatal_halt(`.
///
/// A behavioural test cannot pin this: `handle_synchronous_exception` is
/// `extern "C"`, so the host lane's halt (a panic) aborts the test process
/// rather than unwinding into a `catch_unwind`.  Presence of the guard
/// somewhere in the arm is not the relation — after the binding, nested under a
/// condition, on a literal core, or ending in a frame write, the token is there
/// and the thread still resumes on a not-ready core.
fn svc_arm_readiness_gate_status(trap: &str, dispatch: &str) -> Result<(), String> {
    let (svc_open, svc_close, body_open) = svc_arm_block(trap)?;
    let statements = top_level_statements(trap, svc_open, svc_close);
    let text = |span: &(usize, usize)| trap[span.0..span.1].trim();
    let gates: Vec<usize> = (0..statements.len())
        .filter(|&i| {
            let t = text(&statements[i]);
            t.starts_with("if !crate::lean_ready::lean_ready(") || t.starts_with("if !lean_ready(")
        })
        .collect();
    if gates.len() != 1 {
        return Err(format!(
            "the SVC arm has {} top-level `if !lean_ready(..)` statements; the readiness gate \
             must be exactly one, at the arm's top level",
            gates.len()
        ));
    }
    let gate = gates[0];
    let dispatched = (0..statements.len()).find(|&i| {
        let_binding_parts(strip_leading_attributes(text(&statements[i])))
            .is_some_and(|(pattern, _)| word_occurrences(pattern, "dispatched") > 0)
    });
    match dispatched {
        Some(d) if gate < d => {}
        Some(_) => {
            return Err(
                "the SVC arm's readiness gate comes AFTER the `dispatched` binding — the \
                 full-width narrowing, the prefilters and the unknown-syscall delivery run \
                 on a not-ready core before the gate is consulted"
                    .to_string(),
            )
        }
        None => return Err("the SVC arm binds no `dispatched`".to_string()),
    }
    let (gate_lo, gate_hi) = statements[gate];
    let gate_text = &trap[gate_lo..gate_hi];
    let cond_open = gate_text
        .find("lean_ready(")
        .map(|i| i + "lean_ready(".len())
        .ok_or_else(|| "the readiness gate has no `lean_ready(`".to_string())?;
    let cond_close = matching_close_paren(gate_text, cond_open - 1)
        .ok_or_else(|| "the readiness gate's `lean_ready(` is unbalanced".to_string())?;
    let condition_end = block_open_after(gate_text, cond_close)
        .ok_or_else(|| "the readiness gate has no block".to_string())?;
    let condition = &gate_text[..condition_end];
    if condition.contains("||") || condition.contains("&&") {
        return Err(
            "the SVC arm's readiness gate has a compound condition; the gate must be the \
             bare readiness test"
                .to_string(),
        );
    }
    let arg = gate_text[cond_open..cond_close].trim();
    if !ready_argument_is_executing_core(trap, body_open, gate_lo + cond_open, arg) {
        return Err(format!(
            "the SVC arm's readiness gate tests `lean_ready({arg})`, which does not name the \
             executing core"
        ));
    }
    let block_open = gate_lo + condition_end;
    let block_close = matching_close_brace(trap, block_open)
        .ok_or_else(|| "the readiness gate's block is unbalanced".to_string())?;
    let inner = top_level_statements(trap, block_open, block_close);
    let last = inner
        .last()
        .map(|&(lo, hi)| trap[lo..hi].trim())
        .unwrap_or("");
    let calls_halt = last.starts_with("crate::svc_dispatch::halt_syscall_before_lean_ready(")
        || last.starts_with("halt_syscall_before_lean_ready(");
    if !calls_halt {
        return Err(
            "the SVC arm's readiness gate does not END in `halt_syscall_before_lean_ready(..)` \
             — a not-ready core would fall through to the dispatch"
                .to_string(),
        );
    }
    let helper = "fn halt_syscall_before_lean_ready(";
    if dispatch.matches(helper).count() != 1 {
        return Err(format!(
            "`svc_dispatch.rs` declares `{helper}` {} times",
            dispatch.matches(helper).count()
        ));
    }
    let helper_at = dispatch.find(helper).unwrap_or(0);
    let helper_open = block_open_after(dispatch, helper_at)
        .ok_or_else(|| "`halt_syscall_before_lean_ready` has no body".to_string())?;
    let helper_close = matching_close_brace(dispatch, helper_open)
        .ok_or_else(|| "`halt_syscall_before_lean_ready`'s body is unbalanced".to_string())?;
    if !dispatch[helper_at..helper_open].contains("-> !") {
        return Err("`halt_syscall_before_lean_ready` does not diverge (`-> !`)".to_string());
    }
    let helper_last = top_level_statements(dispatch, helper_open, helper_close)
        .last()
        .map(|&(lo, hi)| dispatch[lo..hi].trim())
        .unwrap_or("");
    if !(statement_diverges(helper_last) && helper_last.contains("fatal_halt(")) {
        return Err("`halt_syscall_before_lean_ready` does not END in `fatal_halt(`".to_string());
    }
    Ok(())
}

/// In `dispatch_svc` (the strings-blanked `svc_dispatch.rs`): `tag` is bound
/// by exactly one top-level `let`, and that binding makes it the Lean
/// dispatch's outcome (`outcome_tag_binding_status`); no other top-level
/// statement but the terminal one mentions `tag`; the function's LAST
/// top-level statement — its value — is `match tag { … }`; that match has
/// exactly one `2 =>` arm, whose expression is `Ok(SvcOutcome::Faulted)`;
/// and `Faulted` occurs nowhere else in the body.
fn dispatch_decodes_faulted(dispatch: &str) -> Result<(), String> {
    let needle = "fn dispatch_svc(";
    let definitions = dispatch.matches(needle).count();
    if definitions != 1 {
        return Err(format!(
            "`svc_dispatch.rs` declares `fn dispatch_svc(` {definitions} times; the decode \
             is read off exactly one definition"
        ));
    }
    let at = dispatch.find(needle).unwrap_or(0);
    let open =
        block_open_after(dispatch, at).ok_or_else(|| "`dispatch_svc` has no body".to_string())?;
    let close = matching_close_brace(dispatch, open)
        .ok_or_else(|| "`dispatch_svc`'s body is unbalanced".to_string())?;
    let statements = top_level_statements(dispatch, open, close);
    let text = |span: &(usize, usize)| dispatch[span.0..span.1].trim();
    let &(last_lo, last_hi) = statements
        .last()
        .ok_or_else(|| "`dispatch_svc`'s body is empty".to_string())?;
    let bindings: Vec<&(usize, usize)> = statements
        .iter()
        .filter(|span| {
            let_binding_parts(strip_leading_attributes(text(span)))
                .is_some_and(|(pattern, _)| word_occurrences(pattern, "tag") > 0)
        })
        .collect();
    if bindings.len() != 1 {
        return Err(format!(
            "`dispatch_svc` binds `tag` {} times at its top level; the outcome tag must be \
             bound exactly once, from the Lean dispatch",
            bindings.len()
        ));
    }
    outcome_tag_binding_status(text(bindings[0]))?;
    for span in &statements {
        if span != bindings[0]
            && *span != (last_lo, last_hi)
            && word_occurrences(text(span), "tag") > 0
        {
            return Err(
                "`tag` is consumed by a top-level statement of `dispatch_svc` other than its \
                 binding and the terminal decode, so the decoded value need not be the Lean \
                 dispatch's"
                    .to_string(),
            );
        }
    }
    let last = dispatch[last_lo..last_hi].trim_start();
    if !last.starts_with("match tag {") {
        return Err(
            "`dispatch_svc`'s value is not `match tag { … }` — the decode of the Lean \
             outcome tag must be the function's terminal statement, not a match found \
             elsewhere in the file"
                .to_string(),
        );
    }
    let arms = match_arm_spans(last)
        .ok_or_else(|| "`dispatch_svc`'s terminal match could not be parsed".to_string())?;
    let two: Vec<&MatchArm> = arms
        .iter()
        .filter(|arm| last[arm.pattern.0..arm.pattern.1].trim() == "2")
        .collect();
    if two.len() != 1 {
        return Err(format!(
            "`dispatch_svc`'s terminal `match tag` has {} `2 =>` arms; outcome tag 2 must \
             be decoded by exactly one",
            two.len()
        ));
    }
    let expr = last[two[0].body.0..two[0].body.1]
        .trim()
        .trim_end_matches(',')
        .trim();
    if expr != "Ok(SvcOutcome::Faulted)" {
        return Err(format!(
            "`dispatch_svc` decodes outcome tag 2 to `{expr}`, not to \
             `Ok(SvcOutcome::Faulted)` — a delivered syscall fault would be read as a block \
             and resumed"
        ));
    }
    let mentions = word_occurrences(&dispatch[open..=close], "Faulted");
    if mentions != 1 {
        return Err(format!(
            "`Faulted` occurs {mentions} times in `dispatch_svc`; only the tag-2 arm may \
             name it"
        ));
    }
    Ok(())
}

/// PR #887 review round 7: is the top-level `let` statement `statement` of
/// `dispatch_svc` the binding that makes `tag` the Lean dispatch's outcome?
/// Two shapes are accepted:
/// `let tag = unsafe { lean_syscall_dispatch_cross_core(…) };` directly, or
/// the live one — `let (tag, …) = <bracket>(…, || { … })`, a closure that
/// binds `tag` that way exactly once and returns it in the tuple position the
/// pattern reads it from.  Anything else — a constant in that position with
/// the Lean call discarded, the call kept only inside a statement whose value
/// is not bound — is refused.
fn outcome_tag_binding_status(statement: &str) -> Result<(), String> {
    let (pattern, init) = let_binding_parts(strip_leading_attributes(statement))
        .ok_or_else(|| "`dispatch_svc`'s `tag` statement is not a `let` binding".to_string())?;
    let pattern_index = tuple_index_of(pattern, "tag").ok_or_else(|| {
        format!(
            "`dispatch_svc` binds `tag` through the pattern `{pattern}`, which the scanner \
             cannot resolve"
        )
    })?;
    if is_lean_outcome_call(init) {
        return if pattern == "tag" {
            Ok(())
        } else {
            Err(format!(
                "`dispatch_svc` binds the Lean call's value to `{pattern}`, not to `tag`"
            ))
        };
    }
    let closure_at = init.find("||").ok_or_else(|| {
        format!(
            "`dispatch_svc` binds `tag` from `{}`, which is neither the Lean call \
             `unsafe {{ lean_syscall_dispatch_cross_core(…) }}` nor a closure returning it",
            collapse_whitespace(init)
        )
    })?;
    let block_open = block_open_after(init, closure_at + 2)
        .ok_or_else(|| "`dispatch_svc`'s outcome closure has no block".to_string())?;
    if !init[closure_at + 2..block_open].trim().is_empty() {
        return Err("`dispatch_svc`'s outcome closure is not `|| { … }`".to_string());
    }
    let block_close = matching_close_brace(init, block_open)
        .ok_or_else(|| "`dispatch_svc`'s outcome closure is unbalanced".to_string())?;
    let statements = top_level_statements(init, block_open, block_close);
    let &(lo, hi) = statements
        .last()
        .ok_or_else(|| "`dispatch_svc`'s outcome closure is empty".to_string())?;
    let tail = init[lo..hi].trim();
    let value_index = tuple_index_of(tail, "tag").ok_or_else(|| {
        format!(
            "`dispatch_svc`'s outcome closure evaluates to `{}`, which does not return `tag`",
            collapse_whitespace(tail)
        )
    })?;
    if value_index != pattern_index {
        return Err(format!(
            "`dispatch_svc` reads `tag` from tuple position {pattern_index} but the closure \
             returns it in position {value_index}"
        ));
    }
    let inner: Vec<&str> = statements[..statements.len() - 1]
        .iter()
        .map(|&(a, b)| strip_leading_attributes(init[a..b].trim()).trim())
        .collect();
    let tag_bindings: Vec<(&str, &str)> = inner
        .iter()
        .filter_map(|s| let_binding_parts(s))
        .filter(|(p, _)| word_occurrences(p, "tag") > 0)
        .collect();
    if tag_bindings.len() != 1 {
        return Err(format!(
            "`dispatch_svc`'s outcome closure binds `tag` {} times; exactly once, from the \
             Lean call",
            tag_bindings.len()
        ));
    }
    let (p, i) = tag_bindings[0];
    if p != "tag" || !is_lean_outcome_call(i) {
        return Err(format!(
            "inside `dispatch_svc`'s outcome closure `tag` is bound from `{}`, not from \
             `unsafe {{ lean_syscall_dispatch_cross_core(…) }}`",
            collapse_whitespace(i)
        ));
    }
    for s in &inner {
        if strip_word_prefix(s, "tag").is_some_and(|rest| {
            let rest = rest.trim_start();
            rest.starts_with('=') && !rest.starts_with("==")
        }) {
            return Err("`tag` is assigned inside `dispatch_svc`'s outcome closure".to_string());
        }
    }
    Ok(())
}

/// Is `init` exactly `unsafe { lean_syscall_dispatch_cross_core(<args>) }`,
/// whitespace collapsed, arguments balanced, nothing after the call?
fn is_lean_outcome_call(init: &str) -> bool {
    let collapsed = collapse_whitespace(init);
    let prefix = "unsafe { lean_syscall_dispatch_cross_core";
    if !collapsed.starts_with(prefix) || collapsed.as_bytes().get(prefix.len()) != Some(&b'(') {
        return false;
    }
    match matching_close_paren(&collapsed, prefix.len()) {
        Some(close) => collapsed[close + 1..].trim() == "}",
        None => false,
    }
}

/// In `handle_synchronous_exception` (the strings-blanked `trap.rs`): the
/// terminal routing match (`terminal_routing_match`) has exactly one
/// `sync_class::SVC` arm; in that arm's block `dispatched` is bound by
/// exactly one top-level `let` whose initializer is the dispatch itself
/// (`dispatched_binding_status`), occurs exactly twice, and is the scrutinee
/// of the block's LAST top-level statement `match dispatched { … }`; that
/// match has exactly one `Ok(crate::svc_dispatch::SvcOutcome::Faulted)` arm,
/// whose block is the single unconditional statement
/// `halt_after_delivered_syscall_fault(frame);`; `Faulted` occurs nowhere
/// else in the handler; and the helper diverges into `fatal_halt`.
fn handler_faulted_arm_halts(trap: &str) -> Result<(), String> {
    let needle = "fn handle_synchronous_exception(";
    let definitions = trap.matches(needle).count();
    if definitions != 1 {
        return Err(format!(
            "`trap.rs` declares `fn handle_synchronous_exception(` {definitions} times"
        ));
    }
    let handler = trap.find(needle).unwrap_or(0);
    let body_open = block_open_after(trap, handler)
        .ok_or_else(|| "`handle_synchronous_exception` has no body".to_string())?;
    let body_close = matching_close_brace(trap, body_open)
        .ok_or_else(|| "`handle_synchronous_exception`'s body is unbalanced".to_string())?;
    let routing = terminal_routing_match(trap, body_open, body_close)?;
    let routing_text = trap[routing.0..routing.1].trim_start();
    let routing_at = routing.1 - routing_text.len();
    let arms = match_arm_spans(routing_text)
        .ok_or_else(|| "the terminal routing match could not be parsed".to_string())?;
    let svc: Vec<&MatchArm> = arms
        .iter()
        .filter(|arm| routing_text[arm.pattern.0..arm.pattern.1].trim() == "sync_class::SVC")
        .collect();
    if svc.len() != 1 {
        return Err(format!(
            "the terminal routing match has {} `sync_class::SVC` arms; the syscall path must \
             be exactly one arm, on exactly that class",
            svc.len()
        ));
    }
    let (svc_open, svc_end) = (routing_at + svc[0].body.0, routing_at + svc[0].body.1);
    if trap.as_bytes().get(svc_open) != Some(&b'{') {
        return Err("the `sync_class::SVC` arm is not a block".to_string());
    }
    let svc_close = svc_end - 1;
    let svc_statements = top_level_statements(trap, svc_open, svc_close);
    let text = |span: &(usize, usize)| trap[span.0..span.1].trim();
    let bindings: Vec<&(usize, usize)> = svc_statements
        .iter()
        .filter(|span| {
            let_binding_parts(strip_leading_attributes(text(span)))
                .is_some_and(|(pattern, _)| word_occurrences(pattern, "dispatched") > 0)
        })
        .collect();
    if bindings.len() != 1 {
        return Err(format!(
            "the SVC arm binds `dispatched` {} times; the dispatch result must be bound \
             exactly once",
            bindings.len()
        ));
    }
    dispatched_binding_status(text(bindings[0]))?;
    let uses = word_occurrences(&trap[svc_open..=svc_close], "dispatched");
    if uses != 2 {
        return Err(format!(
            "`dispatched` occurs {uses} times in the SVC arm; it must occur exactly twice — \
             its binding and the routing match's scrutinee — so nothing but that match \
             consumes the dispatch result"
        ));
    }
    let &(last_lo, last_hi) = svc_statements
        .last()
        .ok_or_else(|| "the SVC arm is empty".to_string())?;
    let last = trap[last_lo..last_hi].trim_start();
    let last_at = last_hi - last.len();
    if !last.starts_with("match dispatched {") {
        return Err(
            "the SVC arm's terminal statement is not `match dispatched { … }` — the dispatch \
             result is routed where the scanner cannot bind it, or something runs after \
             the routing"
                .to_string(),
        );
    }
    let dispatched_arms = match_arm_spans(last)
        .ok_or_else(|| "the `match dispatched` arms could not be parsed".to_string())?;
    let faulted: Vec<&MatchArm> = dispatched_arms
        .iter()
        .filter(|arm| {
            last[arm.pattern.0..arm.pattern.1].trim()
                == "Ok(crate::svc_dispatch::SvcOutcome::Faulted)"
        })
        .collect();
    if faulted.len() != 1 {
        return Err(format!(
            "`match dispatched` has {} `Ok(crate::svc_dispatch::SvcOutcome::Faulted)` arms; \
             a delivered syscall fault must be routed by exactly one",
            faulted.len()
        ));
    }
    let (arm_open, arm_end) = (last_at + faulted[0].body.0, last_at + faulted[0].body.1);
    if trap.as_bytes().get(arm_open) != Some(&b'{') {
        return Err(
            "the `Faulted` arm is an expression, not a block ending in the halt".to_string(),
        );
    }
    let arm_statements = top_level_statements(trap, arm_open, arm_end - 1);
    let sole_halt = arm_statements.len() == 1
        && text(&arm_statements[0]) == "halt_after_delivered_syscall_fault(frame);";
    if !sole_halt {
        return Err(
            "the `Faulted` arm of `handle_synchronous_exception` is not exactly one \
             unconditional `halt_after_delivered_syscall_fault(frame);` statement — the \
             caller would be resumed past the `SVC` its handler restarts it at"
                .to_string(),
        );
    }
    let mentions = word_occurrences(&trap[body_open..=body_close], "Faulted");
    if mentions != 1 {
        return Err(format!(
            "`Faulted` occurs {mentions} times in `handle_synchronous_exception`; a second \
             arm — a decoy under a condition, or a second routing — is a second answer to \
             a delivered fault"
        ));
    }
    let helper = trap
        .find("fn halt_after_delivered_syscall_fault(")
        .ok_or_else(|| "no `fn halt_after_delivered_syscall_fault(`".to_string())?;
    let helper_open = block_open_after(trap, helper)
        .ok_or_else(|| "`halt_after_delivered_syscall_fault` has no body".to_string())?;
    let helper_close = matching_close_brace(trap, helper_open)
        .ok_or_else(|| "`halt_after_delivered_syscall_fault`'s body is unbalanced".to_string())?;
    if !trap[helper..helper_open].contains("-> !") {
        return Err("`halt_after_delivered_syscall_fault` does not diverge (`-> !`)".to_string());
    }
    let helper_statements = top_level_statements(trap, helper_open, helper_close);
    let helper_last = helper_statements
        .last()
        .map(|&(lo, hi)| trap[lo..hi].trim())
        .unwrap_or("");
    if !(statement_diverges(helper_last) && helper_last.contains("fatal_halt(")) {
        return Err(
            "`halt_after_delivered_syscall_fault` does not END in `fatal_halt(`".to_string(),
        );
    }
    Ok(())
}

/// PR #887 review round 7: is the SVC arm's `let dispatched = …` statement
/// the dispatch itself?  Its initializer must be
/// `match u32::try_from(frame.x7()) { … }` (the full-width syscall number of
/// review round 3) with exactly two arms: `Ok(syscall_id)` evaluating to
/// `crate::svc_dispatch::dispatch_svc(syscall_id, &args)` and `Err(_)` to
/// `Err(crate::svc_dispatch::DispatchError::InvalidSyscallId)`.
fn dispatched_binding_status(statement: &str) -> Result<(), String> {
    let (pattern, init) = let_binding_parts(strip_leading_attributes(statement))
        .ok_or_else(|| "the `dispatched` statement is not a `let` binding".to_string())?;
    if pattern != "dispatched" {
        return Err(format!(
            "the dispatch result is bound through `{pattern}`, not `dispatched`"
        ));
    }
    if !init.starts_with("match u32::try_from(frame.x7()) {") {
        return Err(format!(
            "`dispatched` is bound from `{}`, not from the full-width syscall-number match \
             `match u32::try_from(frame.x7()) {{ … }}`",
            collapse_whitespace(init)
        ));
    }
    let arms = match_arm_spans(init)
        .ok_or_else(|| "the `dispatched` binding's match could not be parsed".to_string())?;
    let mut pairs: Vec<(String, String)> = arms
        .iter()
        .map(|arm| {
            (
                collapse_whitespace(init[arm.pattern.0..arm.pattern.1].trim()),
                collapse_whitespace(
                    init[arm.body.0..arm.body.1]
                        .trim()
                        .trim_end_matches(',')
                        .trim(),
                ),
            )
        })
        .collect();
    pairs.sort();
    let expected: Vec<(String, String)> = vec![
        (
            "Err(_)".to_string(),
            "Err(crate::svc_dispatch::DispatchError::InvalidSyscallId)".to_string(),
        ),
        (
            "Ok(syscall_id)".to_string(),
            "crate::svc_dispatch::dispatch_svc(syscall_id, &args)".to_string(),
        ),
    ];
    if pairs != expected {
        return Err(format!(
            "`dispatched` is bound from a match whose arms are {pairs:?}; the routed value \
             must be `crate::svc_dispatch::dispatch_svc(syscall_id, &args)` on \
             `Ok(syscall_id)` and the unknown-syscall error on `Err(_)`"
        ));
    }
    Ok(())
}

/// Token-preserving self-check for `faulted_outcome_status`.  The fixtures
/// carry the live shapes — the SVC arm's dispatch binding, the
/// unknown-syscall and abort arms, the kernel-entry bracket and the host
/// stub — so a check the real file would fail cannot pass on a thinner toy.
fn verify_faulted_outcome_scanner() {
    const GOOD_TRAP: &str = r#"
pub extern "C" fn handle_synchronous_exception(frame: &mut TrapFrame) {
    let esr = frame.esr_el1;
    halt_if_kernel_origin(frame, esr);
    let exception_class = classify_synchronous_exception(esr);
    crate::barriers::csdb();
    match exception_class {
        sync_class::SVC => {
            let _ = crate::per_cpu_stats::record_syscall();
            if !crate::lean_ready::lean_ready(crate::per_cpu::current_core_id_from_tpidr() as usize) {
                crate::svc_dispatch::halt_syscall_before_lean_ready(
                    crate::per_cpu::current_core_id_from_tpidr() as usize,
                    frame.x7(),
                );
            }
            let args = crate::svc_dispatch::SyscallArgs::from_trap_frame(frame);
            let dispatched = match u32::try_from(frame.x7()) {
                Ok(syscall_id) => crate::svc_dispatch::dispatch_svc(syscall_id, &args),
                Err(_) => Err(crate::svc_dispatch::DispatchError::InvalidSyscallId),
            };
            match dispatched {
                Ok(crate::svc_dispatch::SvcOutcome::Frame(regs)) => frame.set_return_frame(regs),
                // The caller took a fault at the seam: halt pending the successor install.
                Ok(crate::svc_dispatch::SvcOutcome::Faulted) => {
                    halt_after_delivered_syscall_fault(frame);
                }
                Ok(crate::svc_dispatch::SvcOutcome::Blocked) => {
                    frame.set_return_frame(crate::svc_dispatch::blocked_resume_sentinel_regs());
                }
                Err(crate::svc_dispatch::DispatchError::InvalidSyscallId) => {
                    deliver_unknown_syscall(frame);
                }
                Err(e) => frame.set_return_frame(crate::svc_dispatch::error_frame_regs(
                    e.kernel_error_discriminant(),
                )),
            }
        }
        sync_class::KERNEL_ABORT => {
            halt_on_kernel_abort(frame, esr);
        }
        sync_class::DATA_ABORT | sync_class::INSTR_ABORT => {
            let _ = crate::per_cpu_stats::record_vm_fault();
            deliver_fault(frame, error_code::VM_FAULT);
        }
        _ => {
            deliver_fault(frame, error_code::USER_EXCEPTION);
        }
    }
}

fn halt_after_delivered_syscall_fault(frame: &TrapFrame) -> ! {
    crate::kprintln!("syscall fault delivered; halting (x7=0x{:x})", frame.x7());
    crate::cpu::fatal_halt()
}
"#;
    const GOOD_DISPATCH: &str = r#"
pub enum SvcOutcome {
    Frame([u64; 6]),
    Blocked,
    Faulted,
}
pub fn dispatch_svc(syscall_id: u32, args: &SyscallArgs) -> Result<SvcOutcome, DispatchError> {
    let sid = match SyscallId::from_u32(syscall_id) {
        Some(sid) => sid,
        None => return Err(DispatchError::InvalidSyscallId),
    };
    let core = crate::per_cpu::current_core_id_from_tpidr() as usize;
    let (tag, regs) = crate::kernel_entry::with_kernel_entry(core, || {
        #[allow(unused_unsafe)]
        let tag = unsafe { lean_syscall_dispatch_cross_core(sid.to_u32(), args.msg_info) };
        (tag, return_frame_read_in(&RETURN_FRAMES, core))
    });
    match tag {
        0 => Ok(SvcOutcome::Frame(regs)),
        1 => Ok(SvcOutcome::Blocked),
        2 => Ok(SvcOutcome::Faulted),
        other => panic!("unknown outcome tag {other}"),
    }
}
#[cfg(feature = "hw_target")]
extern "C" {
    fn lean_syscall_dispatch_cross_core(syscall_id: u32, msg_info: u64) -> u32;
}
#[cfg(not(feature = "hw_target"))]
extern "C" fn lean_syscall_dispatch_cross_core(_syscall_id: u32, _msg_info: u64) -> u32 {
    1
}
pub(crate) fn halt_syscall_before_lean_ready(core: usize, syscall_word: u64) -> ! {
    crate::kprintln!("[core {}] SVC before ready (x7=0x{:x})", core, syscall_word);
    crate::cpu::fatal_halt()
}
"#;
    if let Err(why) = faulted_outcome_status(GOOD_TRAP, GOOD_DISPATCH) {
        panic!("build.rs self-check: the good faulted-outcome fixture was refused: {why}");
    }
    let trap_mutations: &[(&str, &str, &str)] = &[
        (
            "the Faulted arm resuming behind the sentinel (helper token kept in a comment)",
            "                Ok(crate::svc_dispatch::SvcOutcome::Faulted) => {\n                    halt_after_delivered_syscall_fault(frame);\n                }\n",
            "                Ok(crate::svc_dispatch::SvcOutcome::Faulted) => {\n                    // halt_after_delivered_syscall_fault(frame);\n                    frame.set_return_frame(crate::svc_dispatch::blocked_resume_sentinel_regs());\n                }\n",
        ),
        (
            "the halt nested under a condition",
            "                    halt_after_delivered_syscall_fault(frame);\n",
            "                    if frame.x0() == 0 {\n                        halt_after_delivered_syscall_fault(frame);\n                    }\n",
        ),
        (
            "a statement after the halt",
            "                    halt_after_delivered_syscall_fault(frame);\n                }\n                Ok(crate::svc_dispatch::SvcOutcome::Blocked)",
            "                    halt_after_delivered_syscall_fault(frame);\n                    let _ = frame.x0();\n                }\n                Ok(crate::svc_dispatch::SvcOutcome::Blocked)",
        ),
        (
            "the helper mentioned in a string only",
            "                    halt_after_delivered_syscall_fault(frame);\n",
            "                    let _why = \"halt_after_delivered_syscall_fault(frame)\";\n",
        ),
        (
            "the helper no longer ending in the halt",
            "    crate::kprintln!(\"syscall fault delivered; halting (x7=0x{:x})\", frame.x7());\n    crate::cpu::fatal_halt()\n",
            "    crate::cpu::fatal_halt();\n    crate::kprintln!(\"syscall fault delivered; halting (x7=0x{:x})\", frame.x7());\n    loop {}\n",
        ),
        // PR #887 review round 7: the arm is located in the live routing, not
        // found first in the text.
        (
            "a decoy Faulted arm under a condition, the live arm resuming behind the sentinel",
            "            match dispatched {\n                Ok(crate::svc_dispatch::SvcOutcome::Frame(regs)) => frame.set_return_frame(regs),\n                // The caller took a fault at the seam: halt pending the successor install.\n                Ok(crate::svc_dispatch::SvcOutcome::Faulted) => {\n                    halt_after_delivered_syscall_fault(frame);\n                }\n",
            "            if frame.x0() == 0 {\n                match dispatched {\n                    Ok(crate::svc_dispatch::SvcOutcome::Faulted) => {\n                        halt_after_delivered_syscall_fault(frame);\n                    }\n                    _ => {}\n                }\n            }\n            match dispatched {\n                Ok(crate::svc_dispatch::SvcOutcome::Frame(regs)) => frame.set_return_frame(regs),\n                Ok(crate::svc_dispatch::SvcOutcome::Faulted) => {\n                    frame.set_return_frame(crate::svc_dispatch::blocked_resume_sentinel_regs());\n                }\n",
        ),
        (
            "the SVC arm widened to another class",
            "        sync_class::SVC => {\n",
            "        sync_class::SVC | sync_class::PC_ALIGNMENT => {\n",
        ),
        (
            "a frame written after the dispatch routing",
            "                )),\n            }\n        }\n        sync_class::KERNEL_ABORT => {\n",
            "                )),\n            }\n            frame.set_return_frame(crate::svc_dispatch::blocked_resume_sentinel_regs());\n        }\n        sync_class::KERNEL_ABORT => {\n",
        ),
        (
            "the dispatch result shadowed before the routing",
            "            match dispatched {\n                Ok(crate::svc_dispatch::SvcOutcome::Frame(regs))",
            "            let dispatched = Ok::<_, crate::svc_dispatch::DispatchError>(crate::svc_dispatch::SvcOutcome::Blocked);\n            match dispatched {\n                Ok(crate::svc_dispatch::SvcOutcome::Frame(regs))",
        ),
        (
            "the routed value not the dispatch's result (the dispatch kept in a string)",
            "                Ok(syscall_id) => crate::svc_dispatch::dispatch_svc(syscall_id, &args),\n",
            "                Ok(syscall_id) => {\n                    let _ = \"crate::svc_dispatch::dispatch_svc(syscall_id, &args)\";\n                    Ok(crate::svc_dispatch::SvcOutcome::Blocked)\n                }\n",
        ),
        (
            "a statement after the terminal routing match",
            "        _ => {\n            deliver_fault(frame, error_code::USER_EXCEPTION);\n        }\n    }\n}\n",
            "        _ => {\n            deliver_fault(frame, error_code::USER_EXCEPTION);\n        }\n    }\n    let _ = frame.x0();\n}\n",
        ),
        // PR #889 review: the readiness gate precedes every SVC outcome.  Each
        // mutation keeps the gate's tokens and breaks the relation.
        (
            "the readiness gate after the dispatched binding (the narrowing runs ungated)",
            "            if !crate::lean_ready::lean_ready(crate::per_cpu::current_core_id_from_tpidr() as usize) {\n                crate::svc_dispatch::halt_syscall_before_lean_ready(\n                    crate::per_cpu::current_core_id_from_tpidr() as usize,\n                    frame.x7(),\n                );\n            }\n            let args = crate::svc_dispatch::SyscallArgs::from_trap_frame(frame);\n            let dispatched = match u32::try_from(frame.x7()) {\n                Ok(syscall_id) => crate::svc_dispatch::dispatch_svc(syscall_id, &args),\n                Err(_) => Err(crate::svc_dispatch::DispatchError::InvalidSyscallId),\n            };\n",
            "            let args = crate::svc_dispatch::SyscallArgs::from_trap_frame(frame);\n            let dispatched = match u32::try_from(frame.x7()) {\n                Ok(syscall_id) => crate::svc_dispatch::dispatch_svc(syscall_id, &args),\n                Err(_) => Err(crate::svc_dispatch::DispatchError::InvalidSyscallId),\n            };\n            if !crate::lean_ready::lean_ready(crate::per_cpu::current_core_id_from_tpidr() as usize) {\n                crate::svc_dispatch::halt_syscall_before_lean_ready(\n                    crate::per_cpu::current_core_id_from_tpidr() as usize,\n                    frame.x7(),\n                );\n            }\n",
        ),
        (
            "the readiness gate nested under an unrelated condition",
            "            if !crate::lean_ready::lean_ready(crate::per_cpu::current_core_id_from_tpidr() as usize) {\n                crate::svc_dispatch::halt_syscall_before_lean_ready(\n                    crate::per_cpu::current_core_id_from_tpidr() as usize,\n                    frame.x7(),\n                );\n            }\n",
            "            if frame.x0() == 0 {\n                if !crate::lean_ready::lean_ready(crate::per_cpu::current_core_id_from_tpidr() as usize) {\n                    crate::svc_dispatch::halt_syscall_before_lean_ready(\n                        crate::per_cpu::current_core_id_from_tpidr() as usize,\n                        frame.x7(),\n                    );\n                }\n            }\n",
        ),
        (
            "the readiness gate on a literal core",
            "            if !crate::lean_ready::lean_ready(crate::per_cpu::current_core_id_from_tpidr() as usize) {\n",
            "            if !crate::lean_ready::lean_ready(0) {\n",
        ),
        (
            "the readiness gate with a compound condition",
            "            if !crate::lean_ready::lean_ready(crate::per_cpu::current_core_id_from_tpidr() as usize) {\n",
            "            if !crate::lean_ready::lean_ready(crate::per_cpu::current_core_id_from_tpidr() as usize) || frame.x0() == 0 {\n",
        ),
        (
            "the readiness gate ending in a frame write instead of the halt",
            "                crate::svc_dispatch::halt_syscall_before_lean_ready(\n                    crate::per_cpu::current_core_id_from_tpidr() as usize,\n                    frame.x7(),\n                );\n            }\n            let args",
            "                let _ = \"crate::svc_dispatch::halt_syscall_before_lean_ready\";\n                frame.set_return_frame(crate::svc_dispatch::blocked_resume_sentinel_regs());\n            }\n            let args",
        ),
    ];
    for (what, from, to) in trap_mutations {
        assert!(
            GOOD_TRAP.contains(from),
            "build.rs self-check: faulted-outcome mutation `{what}` does not apply"
        );
        let mutated = GOOD_TRAP.replacen(from, to, 1);
        assert_ne!(
            mutated, GOOD_TRAP,
            "build.rs self-check: faulted-outcome mutation `{what}` is inert"
        );
        if faulted_outcome_status(&mutated, GOOD_DISPATCH).is_ok() {
            panic!("build.rs self-check: `faulted_outcome_status` accepted a broken trap fixture: {what}");
        }
    }
    // PR #887 review round 7: the decode is read off `dispatch_svc`'s own
    // terminal match, and the tag it decodes is the Lean call's value.
    let dispatch_mutations: &[(&str, &str, &str)] = &[
        (
            "tag 2 decoded as a block (the Faulted variant still declared)",
            "        2 => Ok(SvcOutcome::Faulted),\n",
            "        2 => Ok(SvcOutcome::Blocked),\n",
        ),
        (
            "the tag-2 decode in a test helper, the live match decoding a block",
            "        2 => Ok(SvcOutcome::Faulted),\n        other => panic!(\"unknown outcome tag {other}\"),\n    }\n}\n",
            "        2 => Ok(SvcOutcome::Blocked),\n        other => panic!(\"unknown outcome tag {other}\"),\n    }\n}\n#[cfg(test)]\nfn decode_outcome(tag: u32) -> Result<SvcOutcome, DispatchError> {\n    match tag {\n        0 => Ok(SvcOutcome::Frame([0; 6])),\n        1 => Ok(SvcOutcome::Blocked),\n        2 => Ok(SvcOutcome::Faulted),\n        other => panic!(\"unknown outcome tag {other}\"),\n    }\n}\n",
        ),
        (
            "the terminal match decoding a shadowed tag",
            "    match tag {\n        0 => Ok(SvcOutcome::Frame(regs)),\n",
            "    let tag = 1;\n    match tag {\n        0 => Ok(SvcOutcome::Frame(regs)),\n",
        ),
        (
            "the tag-2 decode delegated to a helper the terminal match does not name",
            "        2 => Ok(SvcOutcome::Faulted),\n        other => panic!(\"unknown outcome tag {other}\"),\n    }\n}\n",
            "        other => decode_rest(other),\n    }\n}\nfn decode_rest(tag: u32) -> Result<SvcOutcome, DispatchError> {\n    match tag {\n        2 => Ok(SvcOutcome::Faulted),\n        other => panic!(\"unknown outcome tag {other}\"),\n    }\n}\n",
        ),
        (
            "the tag bound to a constant, the Lean call discarded",
            "        let tag = unsafe { lean_syscall_dispatch_cross_core(sid.to_u32(), args.msg_info) };\n        (tag, return_frame_read_in(&RETURN_FRAMES, core))\n",
            "        let _ = unsafe { lean_syscall_dispatch_cross_core(sid.to_u32(), args.msg_info) };\n        (1, return_frame_read_in(&RETURN_FRAMES, core))\n",
        ),
        (
            "a second decode of the tag before the terminal one",
            "    match tag {\n        0 => Ok(SvcOutcome::Frame(regs)),\n",
            "    if tag == 2 {\n        return Ok(SvcOutcome::Blocked);\n    }\n    match tag {\n        0 => Ok(SvcOutcome::Frame(regs)),\n",
        ),
    ];
    for (what, from, to) in dispatch_mutations {
        assert!(
            GOOD_DISPATCH.contains(from),
            "build.rs self-check: dispatch mutation `{what}` does not apply"
        );
        let mutated = GOOD_DISPATCH.replacen(from, to, 1);
        assert_ne!(
            mutated, GOOD_DISPATCH,
            "build.rs self-check: dispatch mutation `{what}` is inert"
        );
        if faulted_outcome_status(GOOD_TRAP, &mutated).is_ok() {
            panic!("build.rs self-check: `faulted_outcome_status` accepted a broken dispatch fixture: {what}");
        }
    }
}
