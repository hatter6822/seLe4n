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

    // WS-RR RR4.25 (single classification path): verify `trap.rs` routes
    // synchronous exceptions on the class the **Lean model** returns, and
    // does not re-derive one from a local `esr_ec` match.  Two
    // classifications that can drift is the defect this scanner exists to
    // keep closed: a drift on the abort arms would route a fault to the
    // wrong handler, or to none.
    scan_trap_rs_classifies_via_lean();

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
    // Comment-free view: a scanner must not be satisfied — or tripped — by the
    // prose that explains it.
    let stripped: String = raw
        .lines()
        .map(|line| match line.find("//") {
            Some(idx) => &line[..idx],
            None => line,
        })
        .collect::<Vec<_>>()
        .join("\n");

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
    if !handler_body.contains("classify_synchronous_exception(esr)") {
        panic!(
            "WS-RR RR4.25 regression: `{path}`'s `handle_synchronous_exception` no \
             longer obtains its class from `classify_synchronous_exception(esr)` — \
             the Lean model is the single classification path, and a second one \
             here can drift from it silently."
        );
    }
    // PR #887 review (relation, not presence): the kernel-origin gate must run
    // *before* the classification.  Both `__el0_sync_entry` and
    // `__el1_sync_entry` reach this handler; an EL1-origin exception routed
    // to the fault path would hand a user handler the kernel's own fault.
    let gate_idx = handler_body
        .find("halt_if_kernel_origin(frame, esr);")
        .unwrap_or_else(|| {
            panic!(
                "PR #887 regression: `{path}`'s `handle_synchronous_exception` no longer \
             calls `halt_if_kernel_origin(frame, esr)`.  Every synchronous exception \
             taken from EL1 must halt before it is classified and routed."
            )
        });
    let classify_idx = handler_body
        .find("classify_synchronous_exception(esr)")
        .expect("checked above");
    if gate_idx > classify_idx {
        panic!(
            "PR #887 regression: in `{path}`'s `handle_synchronous_exception`, the \
             kernel-origin gate runs *after* the classification.  The gate must \
             precede it: a kernel fault must never reach the routing match."
        );
    }
    if !handler_body.contains("sync_class::KERNEL_ABORT => {") {
        panic!(
            "PR #887 regression: `{path}`'s `handle_synchronous_exception` has no \
             `sync_class::KERNEL_ABORT` arm.  A current-EL abort must halt on its own \
             class, not fall through to the unknown-exception delivery."
        );
    }
    if !handler_body.contains("match exception_class {") {
        panic!(
            "WS-RR RR4.25 regression: `{path}`'s `handle_synchronous_exception` calls \
             the classifier but no longer routes on its result (`match \
             exception_class`).  Calling it and ignoring it is the same defect as \
             not calling it."
        );
    }
    if let Some(idx) = handler_body.find("ec::") {
        let excerpt: String = handler_body[idx..].chars().take(40).collect();
        panic!(
            "WS-RR RR4.25 regression: `{path}`'s `handle_synchronous_exception` \
             references a raw exception-class constant (`{excerpt}…`).  The routing \
             arms must use the `sync_class::` tags the Lean model returns; matching \
             on `ec::` values re-introduces the second classification path RR4.25 \
             removed."
        );
    }

    // (3): the hardware-gated classifier calls into Lean.
    let classifier_idx = stripped
        .find("fn classify_synchronous_exception(")
        .unwrap_or_else(|| {
            panic!(
                "WS-RR RR4.25 regression: `{path}` no longer declares \
                 `fn classify_synchronous_exception`."
            )
        });
    let preamble_start = classifier_idx.saturating_sub(120);
    if !stripped[preamble_start..classifier_idx].contains("#[cfg(feature = \"hw_target\")]") {
        panic!(
            "WS-RR RR4.25 regression: in `{path}`, the first \
             `fn classify_synchronous_exception` is not the `hw_target` one.  The \
             hardware definition must come first so this scanner checks the live \
             path, and the host mirror must stay behind \
             `#[cfg(not(feature = \"hw_target\"))]`."
        );
    }
    let classifier_body = body_after(&stripped, classifier_idx, "classify_synchronous_exception");
    if !classifier_body.contains("lean_classify_synchronous_exception") {
        panic!(
            "WS-RR RR4.25 regression: `{path}`'s hardware-target \
             `classify_synchronous_exception` no longer resolves \
             `lean_classify_synchronous_exception`.  On hardware the class must come \
             from the Lean model; a local table here is the divergence RR4.25 closed."
        );
    }
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
    let sites: &[(&str, &str, &str)] = &[
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
        // WS-RR RR4.23: the fault-delivery seam.  `deliver_fault` enters the
        // Lean runtime to run `faultDeliverOnCore` against the live kernel
        // state, so it consults the same readiness gate as the timer tick and
        // the `.reschedule` receiver.
        ("src/trap.rs", "deliver_fault", "lean_handle_fault"),
        // PR #887 review: the unknown-syscall seam enters the Lean runtime
        // the same way, so it consults the same gate.
        (
            "src/trap.rs",
            "deliver_unknown_syscall",
            "lean_handle_unknown_syscall",
        ),
    ];
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
    let bytes = code.as_bytes();
    let mut best: Option<(String, usize)> = None;
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
        if open < offset && offset < end && best.as_ref().is_none_or(|(_, s)| open > *s) {
            best = Some((name, open));
        }
    }
    best.map(|(name, _)| name)
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
