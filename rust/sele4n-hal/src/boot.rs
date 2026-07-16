// SPDX-License-Identifier: GPL-3.0-or-later
//! Boot sequence for the seLe4n microkernel on Raspberry Pi 5.
//!
//! Entry flow: ATF → U-Boot → `_start` (boot.S) → `rust_boot_main` (this file).
//!
//! Phase 1: UART initialization → boot banner → per-CPU data verification
//!          (WS-SM SM1.D.5: `check_per_cpu_invariants` runs here, before
//!           TPIDR_EL1 is set and before any code consumes per-core state)
//! Phase 2: MMU initialization → VBAR_EL1 setup
//! Phase 3: GIC-400 + ARM Generic Timer initialization (AG5)
//! Phase 4: TPIDR_EL1 setup → IRQ enable
//! Phase 5: WS-SM SM1.D — DTB cmdline parse → secondary-core bring-up
//!          (when `smp_enabled=true`, which is the default at v0.31.6)
//! Phase 6: Handoff to Lean kernel (AG7 — FFI bridge)

/// Kernel version string — matches Lean lakefile.toml version.
const KERNEL_VERSION: &str = "0.32.69";

/// Rust entry point called from assembly `_start` after BSS zeroing and
/// stack setup. Receives the DTB pointer from U-Boot in x0.
///
/// This function must never return. If the kernel main returns (which it
/// shouldn't), we enter an infinite WFE loop.
///
/// AN8-E (R-HAL-L7): `#[no_mangle]` exports the symbol with the literal
/// name `rust_boot_main`. The assembly stub in `boot.S` references it via
/// `bl rust_boot_main`, so the linker resolves the call at link time
/// against this Rust definition. If a future refactor renames this
/// function, `boot.S` must be updated in lockstep — `cargo build` would
/// fail with an unresolved-symbol error before any binary is produced.
#[no_mangle]
pub extern "C" fn rust_boot_main(dtb_ptr: u64) -> ! {
    // -----------------------------------------------------------------------
    // Phase 1: UART initialization, boot banner, per-CPU data verification
    //
    // WS-SM SM1.D.5: `check_per_cpu_invariants()` runs in this phase
    // (immediately after UART is online so the diagnostic kprintln can
    // be written).  Verifying the `PER_CPU_DATA` const-initialiser
    // before any subsequent phase prevents a regressed boot.S
    // `secondary_entry` macro from putting a secondary into a slot
    // whose `core_id` field disagrees with its array index — which
    // would silently break per-CPU lookups for that core.  The check
    // runs in O(coreCount) so the cost is negligible.
    //
    // Pre-SM1.D the check ran in Phase 4 (just before TPIDR_EL1 write);
    // moving it earlier:
    //   1. Surfaces a regressed initialiser earlier (Phase 1 vs Phase 4).
    //   2. Lets Phase 5's `apply_cmdline_and_start_smp` rely on the
    //      invariant having been verified at boot start.
    // -----------------------------------------------------------------------
    crate::uart::init_boot_uart();
    crate::kprintln!();
    crate::kprintln!("seLe4n v{} booting on Raspberry Pi 5", KERNEL_VERSION);
    crate::kprintln!("  ARM64 / BCM2712 / Cortex-A76");
    crate::kprintln!();

    // Report current exception level
    let el = crate::registers::read_current_el();
    crate::kprintln!("[boot] Current exception level: EL{}", el);

    // SM1.D.5: per-CPU data verification before any subsequent phase.
    // The check is platform-independent (host stubs run identically),
    // so it executes on every build profile.
    crate::per_cpu::check_per_cpu_invariants();
    crate::kprintln!(
        "[boot] per-cpu data verified ({} cores)",
        crate::per_cpu::PER_CPU_DATA.len()
    );

    // WS-SM SM1.I audit-pass-4 (defense-in-depth for early-boot EL1
    // exceptions): set TPIDR_EL1 here in Phase 1 (immediately after
    // `check_per_cpu_invariants` has verified the static array) so
    // that any subsequent EL1-originated synchronous exception during
    // Phase 2 (MMU) or Phase 3 (GIC + timer) — caused by a kernel
    // bug like a misaligned access or instruction-abort on an
    // unmapped kernel page — reaches `handle_synchronous_exception`
    // with a valid TPIDR_EL1.  Pre-audit-pass-4 the write lived in
    // Phase 4 (just before `enable_irq`); since SM1.I.4 wired the
    // synchronous-exception handler to read TPIDR_EL1 via
    // `per_cpu_stats::record_*` → `current_per_cpu_stats` →
    // `current_per_cpu`, an early-boot EL1 fault would have
    // dereferenced uninitialised TPIDR_EL1 = UB.
    //
    // Phase 4's `write_tpidr_el1` is retained (now idempotent on
    // the boot core) as a defence-in-depth re-write, also providing
    // the diagnostic kprintln line for the boot trace.  Secondaries
    // continue to set their own TPIDR_EL1 in `boot.S::secondary_entry`
    // before calling `rust_secondary_main`.
    //
    // Note: writing TPIDR_EL1 here does NOT enable IRQ delivery —
    // that's still Phase 4's `enable_irq`.  Async exceptions (IRQ,
    // FIQ, SError) remain masked from boot through Phase 3 so they
    // cannot fire during Phases 1-3.  Only synchronous exceptions
    // (caused by a kernel bug) could reach the handler during this
    // window, and the early TPIDR_EL1 write makes that path safe.
    #[cfg(target_arch = "aarch64")]
    {
        let boot_per_cpu = crate::per_cpu::per_cpu_slot_addr(0) as u64;
        crate::registers::write_tpidr_el1(boot_per_cpu);
        crate::barriers::isb();
        crate::kprintln!(
            "[boot] TPIDR_EL1 set early (Phase 1) to PER_CPU_DATA[0] = {:#x}",
            boot_per_cpu
        );
    }

    // -----------------------------------------------------------------------
    // Phase 2: MMU initialization
    // -----------------------------------------------------------------------
    crate::kprintln!("[boot] Configuring MMU...");
    crate::mmu::init_mmu();
    crate::kprintln!("[boot] MMU enabled (identity map, L1 block descriptors)");

    // Set VBAR_EL1 to exception vector table.  WS-SM SM1.C.2 extracted
    // the previously-private helper into `install_exception_vectors`
    // (shared with `smp::rust_secondary_main`); the primary call site
    // now uses the same code path the secondaries do.
    install_exception_vectors();
    crate::kprintln!("[boot] VBAR_EL1 set to exception vector table");

    // -----------------------------------------------------------------------
    // Phase 3: GIC-400 and timer initialization (AG5)
    // -----------------------------------------------------------------------
    crate::kprintln!("[boot] Initializing GIC-400...");
    crate::gic::init_gic();
    crate::kprintln!("[boot] GIC-400 initialized (distributor + CPU interface)");

    crate::kprintln!("[boot] Initializing timer (1000 Hz)...");
    // AJ5-C/L-14 + AK5-J/AK5-L: init_timer returns Result — on failure,
    // log the error and halt via idle_loop since the kernel cannot function
    // without a timer. The error set now includes `CntfrqNotProgrammed`
    // (AK5-J) for the "firmware failed to program CNTFRQ_EL0" case, which
    // would have silently fallen back to 54 MHz on real hardware.
    match crate::timer::init_timer(crate::timer::DEFAULT_TICK_HZ) {
        Ok(()) => {}
        Err(e) => {
            crate::kprintln!("[boot] FATAL: timer init failed: {}", e);
            idle_loop();
        }
    }
    crate::kprintln!("[boot] Timer initialized (54 MHz counter, 1ms ticks)");

    // -----------------------------------------------------------------------
    // Phase 4: TPIDR_EL1 setup → IRQ enable
    //
    // WS-SM SM0.N / SM1.B (closes SMP-M4): set TPIDR_EL1 on the boot core.
    //
    // Secondaries set their own TPIDR_EL1 in `boot.S::secondary_entry`
    // before calling `rust_secondary_main`; the boot core does it
    // here, **before** enabling IRQ delivery so that any future IRQ
    // handler that consumes TPIDR_EL1 sees a defined value rather
    // than the architectural UNKNOWN state.
    //
    // Boot core's `PerCpuData` slot is `PER_CPU_DATA[0]` per the
    // PSCI context_id convention (0 = boot core, 1..3 = secondaries).
    // After this point, every core — boot and secondary — can
    // dispatch through `mrs xN, tpidr_el1` to find its own per-core
    // state without a context_id parameter.
    //
    // SM1.D.5: the `check_per_cpu_invariants()` gate ran in Phase 1
    // (after UART, before any other init), so the per-CPU table has
    // already been validated by the time we reach this write.
    //
    // Audit note: an earlier draft of this hook ran *after*
    // `enable_irq()`.  Pre-SM1.I the IRQ handler (`handle_irq`)
    // never read TPIDR_EL1, so that ordering was functionally safe;
    // moving the write here made the discipline robust against
    // future per-core handler additions (e.g., SM5's per-core
    // scheduler tick).
    //
    // WS-SM SM1.I.4 update: `handle_synchronous_exception` now reads
    // TPIDR_EL1 via `crate::per_cpu_stats::record_*` (each branch
    // increments a per-core counter through `current_per_cpu_stats`).
    // This makes the Phase-4-before-enable_irq ordering MANDATORY,
    // not merely defensive — any synchronous exception from EL0
    // (SVC, page fault from a user-mode caller) lands in
    // `handle_synchronous_exception` and would dereference an
    // uninitialised TPIDR_EL1 if it fired before Phase 4.  EL0 code
    // does not run until the Lean kernel handoff in Phase 6, which
    // is well after Phase 4 — the ordering is safe by construction.
    //
    // EL1-originated synchronous exceptions (kernel bug: misaligned
    // access, instruction abort on an unmapped kernel page) during
    // Phases 1..3 would have read garbage TPIDR_EL1 → UB before
    // the audit-pass-4 fix.
    //
    // **Audit-pass-4 (defense-in-depth)**: Phase 1 now ALSO writes
    // TPIDR_EL1, immediately after `check_per_cpu_invariants`
    // (which validates `PER_CPU_DATA[0]` is well-formed).  This
    // closes the EL1-early-boot UB window structurally: any EL1
    // synchronous exception from Phase 2 onward reads a valid
    // TPIDR_EL1.  The Phase 4 write below is retained as an
    // idempotent re-write (one extra `mrs tpidr_el1` cycle) so the
    // SM5 landing seam contract (TPIDR_EL1 set immediately before
    // the per-core handler swap) remains structurally visible at
    // the Phase-4 site.
    //
    // WS-SM SM1.I.1 also adds `handle_irq_per_core` which reads
    // TPIDR_EL1.  At SM1.I that function is NOT wired into the
    // assembly entry vector (legacy `handle_irq` still is); SM5
    // swaps the vector.  When SM5 lands, the IRQ path joins the
    // synchronous-exception path in depending on TPIDR_EL1 — both
    // are safe after the audit-pass-4 Phase 1 write.
    // -----------------------------------------------------------------------
    #[cfg(target_arch = "aarch64")]
    {
        let boot_per_cpu = crate::per_cpu::per_cpu_slot_addr(0) as u64;
        // Idempotent re-write — Phase 1 (audit-pass-4) already wrote
        // the same value.  This second write is harmless and emits
        // the diagnostic kprintln for the Phase 4 boot-trace banner.
        crate::registers::write_tpidr_el1(boot_per_cpu);
        crate::barriers::isb();
        crate::kprintln!(
            "[boot] TPIDR_EL1 re-confirmed at Phase 4: {:#x}",
            boot_per_cpu
        );
        let live_id = crate::per_cpu::current_core_id_from_tpidr();
        crate::kprintln!("[boot] current_core_id_from_tpidr() = {}", live_id);
    }

    // Enable IRQ delivery now that GIC, timer, and per-core base
    // register (TPIDR_EL1) are configured.
    crate::interrupts::enable_irq();
    crate::kprintln!("[boot] IRQ delivery enabled");

    // -----------------------------------------------------------------------
    // Phase 5: WS-SM SM1.D — DTB cmdline parse + secondary-core bring-up
    //
    // SM1.D.1: parse the kernel command-line from the DTB's
    // `/chosen/bootargs` property (or use defaults if the DTB is
    // absent / malformed / missing the property).  The default config
    // (`CmdlineConfig::default()`) at v1.0.0 has `smp_enabled = true`
    // and `smp_max_cores = 4` per maintainer decision #7.
    //
    // SM1.D.2: when `smp_enabled` is true, issue PSCI CPU_ON for each
    // secondary up to `smp_max_cores`, then signal them via SEV.
    // SM1.D.6: the `smp_max_cores` cap lets operators do partial
    // bring-up (e.g., QEMU `-smp 2 -append "smp_max_cores=2"`).
    //
    // SM1.D.4: all locks needed for SMP coordination live inside
    // their owning objects (per-object fine locks; SM0.I).  Object
    // initialisers default-initialise locks to `.unheld`, so locks
    // are usable from the moment the static is loaded — no separate
    // "lock-init phase" is needed.  This is unlike a global-BKL
    // design where the BKL static would need explicit initialisation
    // before the first secondary touches kernel state.
    //
    // Pre-SM1.D the kernel reached Phase 5's predecessor "Handoff
    // summary" without ever issuing CPU_ON, so secondaries stayed
    // parked in the boot.S `.L_secondary_spin` loop forever and only
    // the boot core ran kernel code.  Post-SM1.D (with the default
    // `smp_enabled=true`), all 4 RPi5 cores are online by the time
    // the Lean kernel main runs.
    // -----------------------------------------------------------------------
    let cmdline_cfg = crate::cmdline::parse_cmdline_from_dtb(dtb_ptr);
    crate::kprintln!(
        "[boot] cmdline parsed: smp_enabled={}, smp_max_cores={}",
        cmdline_cfg.smp_enabled,
        cmdline_cfg.smp_max_cores
    );
    // Always call `apply_cmdline_and_start_smp` — this both stores
    // the parsed `smp_enabled` into `smp::SMP_ENABLED` (so later
    // kernel paths see the canonical state) AND brings up
    // secondaries when enabled.  Calling it unconditionally is
    // simpler than branching and ensures the SMP_ENABLED atomic is
    // always in sync with the parsed cmdline (defense against a
    // future bug where the disabled-branch forgets to commit the
    // false state to the atomic).
    let online = crate::cmdline::apply_cmdline_and_start_smp(&cmdline_cfg);
    if cmdline_cfg.smp_enabled {
        crate::kprintln!(
            "[boot] Phase 5: {} secondary core(s) online (max requested: {})",
            online,
            cmdline_cfg.smp_max_cores
        );
    } else {
        crate::kprintln!("[boot] Phase 5: SMP disabled by cmdline (single-core boot)");
    }

    // -----------------------------------------------------------------------
    // Phase 6: Handoff summary + Lean kernel entry
    // -----------------------------------------------------------------------
    crate::kprintln!();
    crate::kprintln!("[boot] Hardware initialization complete:");
    crate::kprintln!("  UART   : PL011 @ 0xFE201000 (115200 8N1)");
    crate::kprintln!("  MMU    : identity map (3 GiB RAM + 1 GiB device)");
    crate::kprintln!("  VBAR   : exception vectors installed");
    crate::kprintln!("  GIC    : GIC-400 distributor + CPU interface");
    crate::kprintln!("  Timer  : 1000 Hz (54 MHz / 54000 counts per tick)");
    crate::kprintln!(
        "  SMP    : {} (max cores: {})",
        if cmdline_cfg.smp_enabled {
            "enabled"
        } else {
            "disabled"
        },
        cmdline_cfg.smp_max_cores
    );
    crate::kprintln!();
    crate::kprintln!("[boot] Boot complete, entering kernel");

    // AG7-A: Lean kernel entry via FFI bridge.
    // On hardware builds, `lean_kernel_main` is provided by the linked Lean
    // object. On simulation/test builds, it falls through to idle_loop().
    #[cfg(feature = "hw_target")]
    {
        extern "C" {
            fn lean_kernel_main(dtb_ptr: u64);
        }
        // SAFETY: lean_kernel_main is the Lean-compiled entry point linked from
        // libsele4n.a. The DTB pointer from U-Boot is passed through. The
        // function should not return; if it does, we fall through to idle.
        unsafe { lean_kernel_main(dtb_ptr) };
    }

    // Idle fallback: enter WFE loop when no kernel main is linked (simulation)
    // or if kernel_main returns (should not happen in production).
    idle_loop()
}

/// **WS-SM SM1.C.2** (closes SMP-C2 VBAR step): Install the EL1
/// exception vector table at `VBAR_EL1`.  Shared between primary boot
/// (`rust_boot_main` Phase 2) and secondary cores
/// (`smp::rust_secondary_main` Step 2).
///
/// The vector table is defined in `vectors.S` and exported as
/// `__exception_vectors`.  It must be 2048-byte aligned per ARM ARM
/// D1.10.2; the alignment is enforced statically by the `.balign 2048`
/// directive in `vectors.S` plus the linker's section ordering
/// (`.text.vectors : ALIGN(2048) { ... }` in `link.ld`).  A runtime
/// `debug_assert!` re-checks the alignment before writing `VBAR_EL1`
/// so a regressed assembler/linker chain surfaces as a clean halt
/// rather than the architectural UNDEFINED instruction the next
/// exception would produce (ARM ARM D17.2.135: writes with bits
/// [10:0] non-zero are UNDEFINED).
///
/// **Caller obligations**: must be invoked at EL1 with IRQs disabled.
/// The boot core and every secondary satisfy this on entry from PSCI
/// CPU_ON / firmware (DAIF mask covers I/F at reset; the secondary
/// stub in `boot.S::secondary_entry` re-applies `msr daifset, #0xf`
/// defensively).
///
/// **Concurrency**: VBAR_EL1 is banked per-core; concurrent
/// invocations from multiple secondaries are independent (each core
/// programs its own banked register).  The shared `__exception_vectors`
/// linker symbol is read-only.
///
/// AN8-E (R-HAL-L9): The 2048-byte alignment of `__exception_vectors`
/// is enforced at the assembly level by the `.balign 2048` directive in
/// `vectors.S` and reinforced by the linker's section ordering in
/// `link.ld` (`.text.vectors : ALIGN(2048) { ... }`). A compile-time
/// `assert_eq!(align_of_val(...) % 2048, 0)` would require accessing
/// the linker-provided symbol's value at compile time, which Rust does
/// not currently support; the check is therefore deferred to runtime
/// via `write_vbar_el1`.
pub fn install_exception_vectors() {
    #[cfg(target_arch = "aarch64")]
    {
        extern "C" {
            static __exception_vectors: u8;
        }
        // SAFETY: __exception_vectors is a linker-provided symbol defined in
        // vectors.S with .balign 2048. We're reading its address, not its value.
        let vbar = unsafe { &raw const __exception_vectors as u64 };
        // AN8-E (R-HAL-L9): runtime alignment check before VBAR_EL1 write.
        // ARM ARM D17.2.135: VBAR_EL1 bits [10:0] are RES0 — a misaligned
        // address produces an UNDEFINED instruction on the next exception
        // entry. We catch this here so the kernel halts in a debuggable
        // state rather than at exception time.
        debug_assert_eq!(
            vbar % 2048,
            0,
            "exception vector table must be 2048-byte aligned (ARM ARM D1.10.2)"
        );
        crate::registers::write_vbar_el1(vbar);
    }
    crate::barriers::dsb_sy();
    crate::barriers::isb();
}

/// Infinite idle loop — bounded WFE to save power while waiting for events.
///
/// AN9-G (DEF-R-HAL-L17): uses [`crate::cpu::wfe_bounded`] with the
/// 10 ms RPi5 default timeout instead of unconditional `wfe`.  If a
/// timer event source ever silently disappears (mis-configured CNTFRQ,
/// mis-armed comparator), the bounded variant lets the boot diagnostic
/// loop fall through every 10 ms and re-check `next_wakeup` rather
/// than hanging silently.
///
/// The loop itself is infinite; the bound is on each individual
/// `wfe_bounded` call.  Combined with timer interrupt re-arm (AG5)
/// and `wfe_bounded`'s `CNTPCT_EL0` round-trip, this guarantees
/// progress under any single event-source failure.
fn idle_loop() -> ! {
    loop {
        let _elapsed = crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
        // Future: examine `_elapsed` and emit a diagnostic if no
        // events arrived for an unexpectedly long stretch.  The
        // hook lives in this loop (not in `wfe_bounded`) so the
        // bounded primitive remains a thin shim.
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // =====================================================================
    // WS-SM SM1.C.2 — install_exception_vectors() helper tests
    // =====================================================================

    #[test]
    fn sm1c2_install_exception_vectors_callable_on_host() {
        // SM1.C.2: the helper resolves and runs cleanly on host.  The
        // `__exception_vectors` linker symbol is not available in
        // `cargo test` (no `vectors.S` linked), so the aarch64 branch
        // is cfg-gated out and only the barrier emissions execute.
        // This test catches a regression that introduces a host-side
        // panic in the barrier helpers.
        install_exception_vectors();
    }

    #[test]
    fn sm1c2_install_exception_vectors_signature_is_no_arg_fn() {
        // SM1.C.2: the helper takes no arguments — VBAR_EL1 is banked
        // per-core, and the `__exception_vectors` table is a single
        // shared symbol.  A future refactor that adds a parameter
        // would break the call sites in `rust_boot_main` and
        // `rust_secondary_main` simultaneously; pinning the signature
        // here surfaces such a regression at compile time.
        let _: fn() = install_exception_vectors;
    }

    #[test]
    fn sm1c2_install_exception_vectors_idempotent_on_host() {
        // SM1.C.2: repeated invocation must be safe — the secondary
        // bring-up path can in principle re-call this after a TLB
        // shootdown (SM7) or post-resume.  Host-side `write_vbar_el1`
        // is a no-op so repeated calls just emit redundant barriers,
        // which is harmless.
        for _ in 0..4 {
            install_exception_vectors();
        }
    }

    #[test]
    fn sm1c2_primary_boot_path_uses_install_exception_vectors() {
        // SM1.C.2 / regression: a future refactor of `rust_boot_main`
        // that reintroduces an inline VBAR write (bypassing the shared
        // helper) would create a primary/secondary asymmetry.  We pin
        // the helper's existence at the type-system level so a removal
        // breaks the build; the textual presence of the call inside
        // `rust_boot_main` is checked by the SM1.C.2 build-script
        // scanner (see `rust/sele4n-hal/build.rs`).
        let _: fn() = install_exception_vectors;
    }

    // =====================================================================
    // WS-SM SM1.D — Phase 5 wiring tests
    //
    // We cannot call `rust_boot_main` from host tests (it's `-> !` and
    // would attempt UART writes / MMIO that abort on host).  These tests
    // verify the Phase 5 helpers — `parse_cmdline_from_dtb` and
    // `apply_cmdline_and_start_smp` — resolve through the `crate::cmdline`
    // module path, and that `KERNEL_VERSION` stays in sync with
    // `lakefile.toml`.
    //
    // The textual presence of the Phase 5 call sites inside
    // `rust_boot_main` is enforced at build time by
    // `scan_boot_rs_phase5_uses_cmdline` in `build.rs`.
    // =====================================================================

    #[test]
    fn sm1d_kernel_version_string_matches_lakefile() {
        // SM1.D: Phase 5 banner uses `KERNEL_VERSION`; pin it at the
        // current SM2.A landing version (v0.31.9).  A future bump must
        // update this test in lockstep with `lakefile.toml`.
        // `scripts/check_version_sync.sh` (Tier 0) provides the
        // canonical drift check; this test is the local pin.
        assert_eq!(KERNEL_VERSION, "0.32.69");
    }

    #[test]
    fn sm1d_parse_cmdline_from_dtb_resolves_via_crate_cmdline() {
        // SM1.D: the Phase-5 entry point used by `rust_boot_main` is
        // `crate::cmdline::parse_cmdline_from_dtb`.  Pin the symbol
        // via fn-pointer coercion so a rename or signature drift
        // surfaces at compile time.
        let _: fn(u64) -> crate::cmdline::CmdlineConfig =
            crate::cmdline::parse_cmdline_from_dtb;
    }

    #[test]
    fn sm1d_apply_cmdline_resolves_via_crate_cmdline() {
        // SM1.D: the Phase-5 SMP-start helper resolves through
        // `crate::cmdline::apply_cmdline_and_start_smp` and accepts
        // a `&CmdlineConfig`.
        let _: fn(&crate::cmdline::CmdlineConfig) -> u32 =
            crate::cmdline::apply_cmdline_and_start_smp;
    }

    #[test]
    fn sm1d_phase5_defaults_smp_enabled_to_true() {
        // SM1.D.3: per maintainer decision #7, defaults are SMP-on.
        // The Phase-5 path constructs a `CmdlineConfig` via
        // `parse_cmdline_from_dtb(0)` (NULL pointer → defaults).
        let cfg = crate::cmdline::parse_cmdline_from_dtb(0);
        assert!(
            cfg.smp_enabled,
            "Phase 5 default must be smp_enabled=true (SM1.D.3)"
        );
    }

    #[test]
    fn sm1d_phase5_defaults_smp_max_cores_to_platform_max() {
        // SM1.D.6: the default `smp_max_cores` saturates to
        // `MAX_SECONDARY_CORES + 1 = 4` on RPi5.
        let cfg = crate::cmdline::parse_cmdline_from_dtb(0);
        assert_eq!(
            cfg.smp_max_cores,
            crate::smp::MAX_SECONDARY_CORES + 1,
            "Phase 5 default must be smp_max_cores=4 (SM1.D.6 / RPi5)"
        );
    }
}
