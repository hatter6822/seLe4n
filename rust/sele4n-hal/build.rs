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
    let body_no_decl = blank_extern_blocks(classifier_body);
    let call_idx = body_no_decl
        .find("lean_classify_synchronous_exception(esr)")
        .unwrap_or_else(|| {
            panic!(
                "WS-RR RR4.25 regression: `{path}`'s hardware-target \
                 `classify_synchronous_exception` never *calls* \
                 `lean_classify_synchronous_exception(esr)` — declaring the symbol is \
                 not classifying through it.  On hardware the class must come from \
                 the Lean model; a local table here is the divergence RR4.25 closed."
            )
        });
    let gate_idx = body_no_decl.find("lean_ready(").unwrap_or_else(|| {
        panic!(
            "PR #887 review regression: `{path}`'s hardware-target \
             `classify_synchronous_exception` calls into Lean without consulting the \
             per-core readiness gate.  No Lean-emitted symbol may be entered from a \
             PE whose runtime is not initialized, pure or not."
        )
    });
    if gate_idx > call_idx {
        panic!(
            "PR #887 review regression: in `{path}`'s hardware-target \
             `classify_synchronous_exception`, the Lean call precedes the readiness \
             gate.  The gate must guard the call."
        );
    }
    if !body_no_decl.contains("classify_synchronous_exception_mirror(esr)") {
        panic!(
            "PR #887 review regression: `{path}`'s hardware-target \
             `classify_synchronous_exception` has no pre-readiness branch through \
             `classify_synchronous_exception_mirror(esr)`.  A core that is not ready \
             must still classify — through the mirror pinned to the Lean table — so \
             the fail-closed seams below can route."
        );
    }
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
    if !host_body.contains("classify_synchronous_exception_mirror(esr)") {
        panic!(
            "PR #887 review regression: `{path}`'s host-lane \
             `classify_synchronous_exception` does not classify through \
             `classify_synchronous_exception_mirror(esr)`, so the host tests would \
             pin a table the pre-readiness path does not run."
        );
    }
}

/// The routing relation in `handle_synchronous_exception`'s body — a
/// strings-blanked code view: the class the handler routes on is bound to
/// the Lean classifier's result and nothing else, after the kernel-origin
/// gate, and the handler never reaches the pre-readiness mirror itself.
///
/// PR #887 review round 3: the previous checks proved a classifier call
/// *somewhere* in the body and a `match exception_class` *somewhere* else, so
/// `let _ = classify_synchronous_exception(esr); let exception_class =
/// classify_synchronous_exception_mirror(esr);` passed — the divergent second
/// path the gate exists to keep out.  This parses the binding's initializer
/// and forbids a second binding or a reassignment, instead of counting tokens.
fn handler_routing_status(body: &str) -> Result<(), String> {
    let gate = body
        .find("halt_if_kernel_origin(frame, esr);")
        .ok_or_else(|| {
            "PR #887 regression: no `halt_if_kernel_origin(frame, esr)` call — every \
         synchronous exception taken from EL1 must halt before it is classified and \
         routed"
                .to_string()
        })?;
    let needle = "let exception_class = ";
    let binding = body.find(needle).ok_or_else(|| {
        "WS-RR RR4.25 regression: no `let exception_class = …` binding, so the routing \
         class is not bound at all"
            .to_string()
    })?;
    if body[binding + needle.len()..].contains(needle) {
        return Err(
            "PR #887 review regression: `exception_class` is bound twice; the \
                    second binding shadows the classifier's result"
                .to_string(),
        );
    }
    let init_start = binding + needle.len();
    let init_end = body[init_start..]
        .find(';')
        .map(|i| init_start + i)
        .ok_or_else(|| {
            "PR #887 review regression: the `exception_class` binding is unterminated".to_string()
        })?;
    let init = body[init_start..init_end].trim();
    if init != "classify_synchronous_exception(esr)" {
        return Err(format!(
            "WS-RR RR4.25 regression: the routing class is bound to `{init}`, not to \
             `classify_synchronous_exception(esr)` — the Lean model is the single \
             classification path, and a second one here can drift from it silently"
        ));
    }
    if gate > binding {
        return Err(
            "PR #887 regression: the kernel-origin gate runs *after* the \
                    classification.  The gate must precede it: a kernel fault must never \
                    reach the routing match"
                .to_string(),
        );
    }
    // No reassignment of the bound class (also catches a `let mut` rebinding).
    let mut search = 0usize;
    while let Some(hit) = body[search..].find("exception_class =") {
        let at = search + hit;
        search = at + 1;
        let is_binding = at >= needle.len() - "exception_class = ".len()
            && at + "exception_class = ".len() == init_start;
        let is_comparison = body[at + "exception_class =".len()..].starts_with('=');
        if !is_binding && !is_comparison {
            return Err(
                "PR #887 review regression: `exception_class` is assigned after its \
                        binding, so the routed class need not be the classifier's"
                    .to_string(),
            );
        }
    }
    // Round 4 (PR #887): the routing match is a TOP-LEVEL statement of the
    // handler — one that runs on every entry — not a `match` found anywhere
    // after the binding, which a copy nested under `if frame.x0() == 0 { … }`
    // satisfied while a second match routed the rest.
    let body_open = body.find('{').ok_or_else(|| {
        "PR #887 review round 4: the handler text carries no body block".to_string()
    })?;
    let body_close = matching_close_brace(body, body_open)
        .ok_or_else(|| "PR #887 review round 4: the handler's body is unbalanced".to_string())?;
    let statements = top_level_statements(body, body_open, body_close);
    let routing = statements
        .iter()
        .copied()
        .find(|&(lo, _)| {
            body[lo..]
                .trim_start()
                .starts_with("match exception_class {")
        })
        .ok_or_else(|| {
            "WS-RR RR4.25 regression: the handler binds the classifier's result but \
             does not route on it as a top-level statement (`match exception_class`).  \
             Calling it and ignoring it — or matching on it only under a condition — \
             is the same defect as not calling it"
                .to_string()
        })?;
    if routing.0 < init_end {
        return Err(
            "PR #887 review round 4: the routing match precedes the binding it matches on"
                .to_string(),
        );
    }
    let routing_text = &body[routing.0..routing.1];
    if !routing_text.contains("sync_class::KERNEL_ABORT => {") {
        return Err(
            "PR #887 regression: no `sync_class::KERNEL_ABORT` arm in the routing \
                    match.  A current-EL abort must halt on its own class, not fall \
                    through to the unknown-exception delivery"
                .to_string(),
        );
    }
    // No competing routing match: every `match` whose arms name a
    // `sync_class::` tag must be the top-level routing match itself.
    let routing_match_at = routing.0 + (routing_text.len() - routing_text.trim_start().len());
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
                 (`{excerpt}…`); the top-level `match exception_class` is the only \
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
    ];
    for (what, source) in cases {
        assert!(
            status(source).is_err(),
            "handler routing self-check: {what} passed the routing relation"
        );
    }
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
];

/// **Lean upcalls that run outside the readiness gate, by design or as
/// registered debt** — `(source, enclosing fn, Lean symbol, why)`.
///
/// Every entry is a call `scan_lean_upcalls_readiness_gated` would otherwise
/// reject, so adding one is a decision with a reason a reader can check, and
/// an entry whose call no longer exists fails the build rather than
/// lingering.
const LEAN_UPCALLS_OUTSIDE_THE_GATE: &[(&str, &str, &str, &str)] = &[
    (
        "src/boot.rs",
        "rust_boot_main",
        "lean_kernel_main",
        "the primary core's boot install: this call is the one that initializes \
         the Lean runtime the gate stands for, so it cannot sit behind the gate; \
         the boot core is marked ready after it, the image target's obligation",
    ),
    (
        "src/svc_dispatch.rs",
        "dispatch_svc",
        "lean_syscall_dispatch_cross_core",
        "the SVC dispatch seam: registered debt, closed by the release-readiness \
         plan's boot-path fail-open phase (docs/WORKSTREAM_HISTORY.md)",
    ),
    (
        "src/ffi.rs",
        "sele4n_suspend_thread",
        "suspend_thread_cross_core",
        "the cross-core suspend seam: the same registered debt as the SVC seam",
    ),
];

/// One call from HAL Rust into a Lean-emitted symbol, as the scanner found it.
#[derive(Debug, PartialEq, Eq)]
struct LeanUpcallSite {
    /// The `fn` whose brace-matched body holds the call.
    enclosing_fn: String,
    /// The Lean symbol called.
    symbol: String,
    /// Whether `lean_ready(` occurs in the enclosing body *before* the call.
    gated: bool,
}

/// Every call expression `symbol(` in `code` — a strings-blanked code view —
/// for `symbol` in `exports`, attributed to its enclosing function.
///
/// A declaration (`fn symbol(` inside an `extern "C"` block) or a definition
/// (a host-lane stub, `extern "C" fn symbol(`) is not a call: the token is
/// present but nothing is invoked, which is the presence-versus-relation
/// mistake the PR #887 review found in the classifier scanner.  A call at
/// module scope cannot be attributed and is an error, so it fails closed.
fn lean_upcall_sites(code: &str, exports: &[&str]) -> Result<Vec<LeanUpcallSite>, String> {
    let bytes = code.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut sites = Vec::new();
    for symbol in exports {
        let needle = format!("{symbol}(");
        let mut search = 0usize;
        while let Some(hit) = code[search..].find(&needle) {
            let at = search + hit;
            search = at + needle.len();
            // Whole identifier: `not_lean_x(` must not match `lean_x(`.
            if at > 0 && is_ident(bytes[at - 1]) {
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
/// `lean_ready(…)` call (`condition_entails_ready`): no comparison, no `!`,
/// no `||` anywhere.
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
        if is_negated_ready_call(cond) {
            let statements = top_level_statements(code, block_open, block_close);
            let last_diverges = statements
                .last()
                .map(|&(lo, hi)| statement_diverges(&code[lo..hi]))
                .unwrap_or(false);
            if last_diverges && block_close < call {
                return true;
            }
        } else if condition_entails_ready(cond) && block_open < call && call < block_close {
            return true;
        }
    }
    false
}

/// Does `cond` — the text between an `if` and its `{` — entail readiness?
/// Yes exactly when it contains no `||` and is a conjunction (`&&` at
/// parenthesis depth zero) one of whose conjuncts is a bare `lean_ready(…)`
/// call.  `lean_ready(c) == false`, `!lean_ready(c)`, `ready_flag` and
/// `lean_ready(c) || x` all read as not entailing it — the fail-closed
/// direction.
fn condition_entails_ready(cond: &str) -> bool {
    if cond.contains("||") {
        return false;
    }
    split_top_level(cond, "&&")
        .iter()
        .any(|conjunct| is_bare_ready_call(conjunct))
}

/// Is `expr` exactly a call of `lean_ready` (optionally path-qualified,
/// optionally parenthesised), with balanced arguments and nothing after the
/// closing parenthesis?
fn is_bare_ready_call(expr: &str) -> bool {
    let mut e = expr.trim();
    while e.starts_with('(') && e.ends_with(')') && matching_close_paren(e, 0) == Some(e.len() - 1)
    {
        e = e[1..e.len() - 1].trim();
    }
    let Some(rest) = e
        .strip_prefix("crate::lean_ready::lean_ready(")
        .or_else(|| e.strip_prefix("lean_ready::lean_ready("))
        .or_else(|| e.strip_prefix("lean_ready("))
    else {
        return false;
    };
    let mut depth = 1i32;
    for (index, ch) in rest.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return rest[index + 1..].trim().is_empty();
                }
            }
            _ => {}
        }
    }
    false
}

/// Is `cond` exactly `!lean_ready(…)` — the negated bare guard whose block
/// must diverge?
fn is_negated_ready_call(cond: &str) -> bool {
    cond.trim()
        .strip_prefix('!')
        .map(is_bare_ready_call)
        .unwrap_or(false)
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
        let mut search = 0usize;
        while let Some(hit) = contents[search..].find("@[export ") {
            let at = search + hit + "@[export ".len();
            search = at;
            let name: String = contents[at..]
                .trim_start()
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() && !out.contains(&name) {
                out.push(name);
            }
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
    let mut views: Vec<(String, String)> = Vec::new();
    for path in &sources {
        let contents = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => panic!(
                "Lean upcall scanner: failed to read {}: {e}",
                path.display()
            ),
        };
        let (_, code) = rust_code_views(&contents);
        // HAL-declared `lean_*` externs join the set: the toolchain-emitted
        // entry is declared here and nowhere in the Lean sources.
        for name in extern_block_declarations(&code) {
            if name.starts_with("lean_") && !exports.contains(&name) {
                exports.push(name);
            }
        }
        views.push((path.to_string_lossy().replace('\\', "/"), code));
    }
    exports.sort();
    let export_refs: Vec<&str> = exports.iter().map(String::as_str).collect();

    let mut gated_found: Vec<(String, String, String)> = Vec::new();
    let mut exempt_seen = vec![false; LEAN_UPCALLS_OUTSIDE_THE_GATE.len()];
    for (path, code) in &views {
        let sites = match lean_upcall_sites(code, &export_refs) {
            Ok(s) => s,
            Err(e) => panic!("Lean upcall scanner: `{path}`: {e}"),
        };
        for site in sites {
            if site.gated {
                gated_found.push((path.clone(), site.enclosing_fn, site.symbol));
                continue;
            }
            let exempt = LEAN_UPCALLS_OUTSIDE_THE_GATE
                .iter()
                .position(|(p, f, sym, _)| {
                    *p == path.as_str() && *f == site.enclosing_fn && *sym == site.symbol
                });
            match exempt {
                Some(i) => exempt_seen[i] = true,
                None => panic!(
                    "Lean upcall scanner: `{path}`'s `fn {}` calls the Lean-emitted \
                     symbol `{}` without consulting the per-core readiness gate \
                     (`crate::lean_ready::lean_ready(core)`) earlier in its body.  A PE \
                     must never enter a Lean runtime it has not initialized.  Either \
                     gate the call — and add the seam to `LEAN_READY_GATED_SEAMS` — or, \
                     if it is the call that establishes readiness or a registered gap, \
                     add it to `LEAN_UPCALLS_OUTSIDE_THE_GATE` with its reason.",
                    site.enclosing_fn, site.symbol
                ),
            }
        }
    }
    for (i, (p, f, sym, _)) in LEAN_UPCALLS_OUTSIDE_THE_GATE.iter().enumerate() {
        if !exempt_seen[i] {
            panic!(
                "Lean upcall scanner: `LEAN_UPCALLS_OUTSIDE_THE_GATE` lists `{p}`'s \
                 `fn {f}` calling `{sym}`, but no ungated call to that symbol exists \
                 there any more.  Remove the stale entry, or re-attribute a call that \
                 moved."
            );
        }
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

/// Token-preserving mutations for `lean_upcall_sites`: every case keeps the
/// symbol present in the text and breaks the relation the scanner is meant to
/// see, so a scanner that had degraded to a presence check fails here before
/// it is trusted with the tree.
fn verify_lean_upcall_scanner() {
    let exports = ["lean_x"];
    let sites = |source: &str| {
        let (_, code) = rust_code_views(source);
        lean_upcall_sites(&code, &exports)
    };
    let gated = sites(
        "fn seam(c: usize) -> u32 {\n    if crate::lean_ready::lean_ready(c) {\n        \
         extern \"C\" {\n            fn lean_x(a: u64) -> u32;\n        }\n        \
         unsafe { lean_x(1) }\n    } else {\n        0\n    }\n}\n",
    )
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
    let gate_after = sites(
        "fn seam(c: usize) -> u32 {\n    extern \"C\" {\n        fn lean_x(a: u64) -> u32;\n    }\n    \
         let r = unsafe { lean_x(1) };\n    if crate::lean_ready::lean_ready(c) {\n        r\n    } \
         else {\n        0\n    }\n}\n",
    )
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
    let orphan = sites("static Y: u32 = lean_x(1);\n");
    assert!(
        orphan.is_err(),
        "Lean upcall scanner self-check: a call outside any function must fail closed"
    );
    // PR #887 review round 3: a readiness token that does not CONTROL the call.
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
    ungated(
        "fn seam(c: usize) -> u32 {\n    let _ = crate::lean_ready::lean_ready(c);\n    \
         unsafe { lean_x(1) }\n}\n",
        "a stored readiness value",
    );
    ungated(
        "fn seam(c: usize) -> u32 {\n    if crate::lean_ready::lean_ready(c) {\n        \
         0\n    } else {\n        0\n    };\n    unsafe { lean_x(1) }\n}\n",
        "a readiness block closed before the call",
    );
    ungated(
        "fn seam(c: usize, other: bool) -> u32 {\n    if other || \
         crate::lean_ready::lean_ready(c) {\n        unsafe { lean_x(1) }\n    } else {\n        \
         0\n    }\n}\n",
        "a disjunction with the readiness check",
    );
    ungated(
        "fn seam(c: usize) -> u32 {\n    if !crate::lean_ready::lean_ready(c) {\n    }\n    \
         unsafe { lean_x(1) }\n}\n",
        "a negated check whose block does not diverge",
    );
    gated_by(
        "fn seam(c: usize) -> u32 {\n    if !crate::lean_ready::lean_ready(c) {\n        \
         return 0;\n    }\n    unsafe { lean_x(1) }\n}\n",
        "the fail-closed early return",
    );
    gated_by(
        "fn seam(c: usize, other: bool) -> u32 {\n    if other && \
         crate::lean_ready::lean_ready(c) {\n        unsafe { lean_x(1) }\n    } else {\n        \
         0\n    }\n}\n",
        "a conjunction with the readiness check",
    );
    // PR #887 review round 4: a region-scoped presence check is still a
    // presence check.  The divergence must be the negated block's LAST
    // top-level statement, and the positive guard's condition must be the
    // readiness call itself, not any comparison on it.
    ungated(
        "fn seam(c: usize, retry: bool) -> u32 {\n    if !crate::lean_ready::lean_ready(c) {\n        \
         if retry {\n            return 0;\n        }\n    }\n    unsafe { lean_x(1) }\n}\n",
        "a negated check whose divergence is nested under a condition",
    );
    ungated(
        "fn seam(c: usize) -> u32 {\n    if crate::lean_ready::lean_ready(c) == false {\n        \
         unsafe { lean_x(1) }\n    } else {\n        0\n    }\n}\n",
        "an inverted comparison on the readiness check",
    );
    ungated(
        "fn seam(c: usize) -> u32 {\n    if crate::lean_ready::lean_ready(c) != true {\n        \
         unsafe { lean_x(1) }\n    } else {\n        0\n    }\n}\n",
        "an inverted inequality on the readiness check",
    );
    ungated(
        "fn seam(c: usize) -> u32 {\n    let ready = crate::lean_ready::lean_ready(c);\n    if ready \
         {\n        unsafe { lean_x(1) }\n    } else {\n        0\n    }\n}\n",
        "a readiness value consulted through a binding",
    );
    gated_by(
        "fn seam(c: usize) -> u32 {\n    if !crate::lean_ready::lean_ready(c) {\n        \
         crate::kprintln!(\"not ready\");\n        crate::cpu::fatal_halt();\n    }\n    unsafe { \
         lean_x(1) }\n}\n",
        "a fail-closed halt as the negated block's last statement",
    );
    gated_by(
        "fn seam(c: usize) -> u32 {\n    if (crate::lean_ready::lean_ready(c)) {\n        unsafe { \
         lean_x(1) }\n    } else {\n        0\n    }\n}\n",
        "a parenthesised readiness check",
    );
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
fn faulted_outcome_status(trap_raw: &str, dispatch_raw: &str) -> Result<(), String> {
    let (_, dispatch) = rust_code_views(dispatch_raw);
    if !dispatch.contains("2 => Ok(SvcOutcome::Faulted),") {
        return Err(
            "`svc_dispatch.rs` does not decode outcome tag 2 to `SvcOutcome::Faulted` — \
                    a delivered syscall fault would be read as a block and resumed"
                .to_string(),
        );
    }
    let (_, trap) = rust_code_views(trap_raw);
    let handler = trap
        .find("fn handle_synchronous_exception(")
        .ok_or_else(|| "`trap.rs` has no `fn handle_synchronous_exception(`".to_string())?;
    let body_open = block_open_after(&trap, handler)
        .ok_or_else(|| "`handle_synchronous_exception` has no body".to_string())?;
    let body_close = matching_close_brace(&trap, body_open)
        .ok_or_else(|| "`handle_synchronous_exception`'s body is unbalanced".to_string())?;
    let arm_at = body_open
        + trap[body_open..body_close]
            .find("SvcOutcome::Faulted) =>")
            .ok_or_else(|| {
                "`handle_synchronous_exception` has no `SvcOutcome::Faulted` arm — a delivered \
                 syscall fault would fall through to another arm"
                    .to_string()
            })?;
    let arm_open = block_open_after(&trap, arm_at)
        .ok_or_else(|| "the `Faulted` arm has no block".to_string())?;
    let arm_close = matching_close_brace(&trap, arm_open)
        .ok_or_else(|| "the `Faulted` arm's block is unbalanced".to_string())?;
    let statements = top_level_statements(&trap, arm_open, arm_close);
    let sole_halt = statements.len() == 1
        && trap[statements[0].0..statements[0].1]
            .trim()
            .starts_with("halt_after_delivered_syscall_fault(");
    if !sole_halt {
        return Err(
            "the `Faulted` arm of `handle_synchronous_exception` is not exactly one \
                    unconditional `halt_after_delivered_syscall_fault(…)` statement — the caller \
                    would be resumed past the `SVC` its handler restarts it at"
                .to_string(),
        );
    }
    if trap[arm_open..=arm_close].contains("set_return_frame(") {
        return Err("the `Faulted` arm publishes a return frame".to_string());
    }
    let helper = trap
        .find("fn halt_after_delivered_syscall_fault(")
        .ok_or_else(|| "no `fn halt_after_delivered_syscall_fault(`".to_string())?;
    let helper_open = block_open_after(&trap, helper)
        .ok_or_else(|| "`halt_after_delivered_syscall_fault` has no body".to_string())?;
    let helper_close = matching_close_brace(&trap, helper_open)
        .ok_or_else(|| "`halt_after_delivered_syscall_fault`'s body is unbalanced".to_string())?;
    if !trap[helper..helper_open].contains("-> !") {
        return Err("`halt_after_delivered_syscall_fault` does not diverge (`-> !`)".to_string());
    }
    let helper_statements = top_level_statements(&trap, helper_open, helper_close);
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

/// Token-preserving self-check for `faulted_outcome_status`.
fn verify_faulted_outcome_scanner() {
    const GOOD_TRAP: &str = r#"
pub extern "C" fn handle_synchronous_exception(frame: &mut TrapFrame) {
    let esr = frame.esr_el1;
    halt_if_kernel_origin(frame, esr);
    let exception_class = classify_synchronous_exception(esr);
    match exception_class {
        sync_class::SVC => {
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
                Err(e) => frame.set_return_frame(crate::svc_dispatch::error_frame_regs(
                    e.kernel_error_discriminant(),
                )),
            }
        }
        sync_class::KERNEL_ABORT => {
            halt_on_kernel_abort(frame, esr);
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
    let (tag, regs) = run(syscall_id, args);
    match tag {
        0 => Ok(SvcOutcome::Frame(regs)),
        1 => Ok(SvcOutcome::Blocked),
        2 => Ok(SvcOutcome::Faulted),
        other => panic!("unknown outcome tag {other}"),
    }
}
"#;
    if let Err(why) = faulted_outcome_status(GOOD_TRAP, GOOD_DISPATCH) {
        panic!("build.rs self-check: the good faulted-outcome fixture was refused: {why}");
    }
    let trap_mutations: [(&str, &str, &str); 5] = [
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
    let decode_as_block = GOOD_DISPATCH.replacen(
        "2 => Ok(SvcOutcome::Faulted),",
        "2 => Ok(SvcOutcome::Blocked),",
        1,
    );
    assert_ne!(
        decode_as_block, GOOD_DISPATCH,
        "build.rs self-check: the decode mutation is inert"
    );
    if faulted_outcome_status(GOOD_TRAP, &decode_as_block).is_ok() {
        panic!(
            "build.rs self-check: `faulted_outcome_status` accepted tag 2 decoded as a block \
                (the `Faulted` variant still declared)"
        );
    }
}
