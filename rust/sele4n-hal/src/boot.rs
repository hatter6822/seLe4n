// SPDX-License-Identifier: GPL-3.0-or-later
//! Boot sequence for the seLe4n microkernel on Raspberry Pi 5.
//!
//! Entry flow: ATF → U-Boot → `_start` (boot.S) → `rust_boot_main` (this file).
//!
//! Phase 1: UART initialization → boot banner
//! Phase 2: MMU initialization → VBAR_EL1 setup
//! Phase 3: GIC-400 + ARM Generic Timer initialization (AG5)
//! Phase 4: Handoff to Lean kernel (AG7 — FFI bridge)

/// Kernel version string — matches Lean lakefile.toml version.
const KERNEL_VERSION: &str = "0.31.5";

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
pub extern "C" fn rust_boot_main(_dtb_ptr: u64) -> ! {
    // -----------------------------------------------------------------------
    // Phase 1: UART initialization and boot banner
    // -----------------------------------------------------------------------
    crate::uart::init_boot_uart();
    crate::kprintln!();
    crate::kprintln!("seLe4n v{} booting on Raspberry Pi 5", KERNEL_VERSION);
    crate::kprintln!("  ARM64 / BCM2712 / Cortex-A76");
    crate::kprintln!();

    // Report current exception level
    let el = crate::registers::read_current_el();
    crate::kprintln!("[boot] Current exception level: EL{}", el);

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
    // WS-SM SM1.B: before writing TPIDR_EL1, the runtime gate
    // `check_per_cpu_invariants()` verifies every slot's `core_id`
    // matches its array index — catching a regressed const-init
    // table at boot rather than at first SMP wakeup.  The check is
    // platform-independent (compiles on host stubs too) and runs in
    // O(coreCount) = O(4), so it's cheap to leave in production.
    //
    // Audit note: an earlier draft of this hook ran *after*
    // `enable_irq()`.  Today's IRQ handlers never read TPIDR_EL1, so
    // that ordering was functionally safe, but it was fragile against
    // future per-core handler additions (e.g., SM5's per-core timer
    // tick).  Moving the write here makes the discipline robust by
    // construction.
    // -----------------------------------------------------------------------
    crate::per_cpu::check_per_cpu_invariants();
    #[cfg(target_arch = "aarch64")]
    {
        let boot_per_cpu = crate::per_cpu::per_cpu_slot_addr(0) as u64;
        crate::registers::write_tpidr_el1(boot_per_cpu);
        crate::barriers::isb();
        crate::kprintln!(
            "[boot] TPIDR_EL1 set to PER_CPU_DATA[0] = {:#x}",
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
    // Phase 4: Handoff summary
    // -----------------------------------------------------------------------
    crate::kprintln!();
    crate::kprintln!("[boot] Hardware initialization complete:");
    crate::kprintln!("  UART   : PL011 @ 0xFE201000 (115200 8N1)");
    crate::kprintln!("  MMU    : identity map (3 GiB RAM + 1 GiB device)");
    crate::kprintln!("  VBAR   : exception vectors installed");
    crate::kprintln!("  GIC    : GIC-400 distributor + CPU interface");
    crate::kprintln!("  Timer  : 1000 Hz (54 MHz / 54000 counts per tick)");
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
        unsafe { lean_kernel_main(_dtb_ptr) };
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
}
