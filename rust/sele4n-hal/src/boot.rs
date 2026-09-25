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
//! Phase 4: TPIDR_EL1 setup (IRQs stay masked — WS-BP BP6.2)
//! Phase 5: WS-BP BP4.1–BP4.5 — Lean library initialization → the device
//!          tree copied into a Lean `ByteArray` → the kernel-state install
//!          (`lean_kernel_main`) → the image's loaded bytes cleaned to the
//!          Point of Unification, on the boot core alone → the boot core's
//!          per-PE runtime handshake and readiness (WS-BP BP6.1/BP6.2) →
//!          IRQ enable
//! Phase 6: WS-SM SM1.D — DTB cmdline parse → secondary-core bring-up
//!          (`smp_enabled=true` is the default again since v0.32.142,
//!           when SM5.I serialised kernel entry; see
//!           `cmdline::CmdlineConfig::default`).  The bring-up consumes the
//!          `SecondaryReleasePermit` Phase 5 returns, so it cannot run first.
//! Phase 7: handoff summary → the PE-topology refusal: every declared PE
//!          must serve the kernel (Lean-ready and IRQ-ready) within the
//!          bounded window, or the system halts (WS-BP BP6.3)

/// Kernel version string — matches Lean lakefile.toml version.
const KERNEL_VERSION: &str = "0.36.2";

/// **PR #889 review round 21**: how many PEs the linked Lean kernel declares.
///
/// Pinned against `SeLe4n/Platform/RPi5/Board.lean`'s
/// `rpi5MachineConfig.declaredCoreCount` and `rpi5PlatformBinding.coreCount`,
/// which `PlatformBinding.declaredCoreCountAgrees` holds equal.  The Lean side
/// installs idle threads on exactly this many cores and bounds
/// `.tcbSetAffinity` by the same number, so a handoff to a narrower machine is
/// refused at Phase 7 rather than stranding threads on PEs that do not exist.
///
/// Compiled where it is read: the Phase-7 refusal below is `hw_target`-only,
/// and `lean_declared_core_count_matches_the_rpi5_binding` pins it under
/// `cfg(test)`.  Without the gate the default host profile warns it is dead,
/// which is true of that profile and of no other.
#[cfg(any(feature = "hw_target", test))]
const LEAN_DECLARED_CORE_COUNT: u32 = 4;

/// **PR #889 review round 23**: how long the handoff waits for every declared
/// PE to serve the kernel before refusing the topology.
///
/// Bounded on purpose: a secondary that never publishes must make the boot
/// *fail*, not hang, so the wait has a ceiling and the refusal below is what
/// runs when it expires.  The unit is `wfe_bounded` ticks (10 ms each), the
/// same clock the shootdown protocol's bounded waits use.
///
/// **One second, derived rather than picked** (the v0.36.2 audit).  Before a
/// secondary publishes it runs its MMU, vector, GIC and timer setup, the
/// per-PE handshake, the kernel bring-up entry under the kernel-entry lock —
/// which the boot core's 1 kHz tick contends — and about 390 bytes of console
/// traffic, which at 115 200 baud 8N1 (86.8 µs a byte) is ≈ 34 ms per PE and,
/// serialised through the one console lock with the boot core's own Phase-6
/// and Phase-7 lines, ≈ 100 ms for three PEs.  The previous window, 160 ms,
/// left a healthy board a margin under 2× from console traffic alone.  A
/// generous window costs nothing on a healthy boot, which ends the wait the
/// moment the last PE serves, and is paid only on a boot that fails anyway.
///
/// `hw_target`-only for the same reason as `LEAN_DECLARED_CORE_COUNT`: its one
/// reader is the Phase-7 refusal.
#[cfg(feature = "hw_target")]
const SECONDARY_READY_TIMEOUT_TICKS: u64 = crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS * 100;

/// Rust entry point called from assembly `_start` after BSS zeroing and
/// stack setup. Receives the DTB pointer from the firmware in x0, and in x1
/// the `CurrentEL` value the firmware entered `_start` at (`0x4` for EL1,
/// `0x8` for EL2), which `boot.S`'s `.L_enter_el1` reports after dropping
/// to EL1 (WS-BP BP5.5).  The entry level selects the PSCI conduit before
/// anything can make a PSCI call (`psci::select_conduit`).
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
pub extern "C" fn rust_boot_main(dtb_ptr: u64, entry_el: u64) -> ! {
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
    //   2. Lets Phase 6's `apply_cmdline_and_start_smp` rely on the
    //      invariant having been verified at boot start.
    // -----------------------------------------------------------------------
    crate::uart::init_boot_uart();
    crate::kprintln!();
    crate::kprintln!("seLe4n v{} booting on Raspberry Pi 5", KERNEL_VERSION);
    crate::kprintln!("  ARM64 / BCM2712 / Cortex-A76");
    crate::kprintln!();

    // Report the level the firmware entered at and the level the kernel
    // runs at, then select the PSCI conduit the entry level implies.  An
    // entry level `boot.S` never reports cannot pick a conduit; the core
    // halts rather than guess (WS-BP BP5.5).
    let el = crate::registers::read_current_el();
    crate::kprintln!(
        "[boot] Entered at EL{}, running at EL{}",
        (entry_el >> 2) & 0x3,
        el
    );
    match crate::psci::select_conduit(entry_el) {
        Some(conduit) => crate::kprintln!("[boot] PSCI conduit: {:?}", conduit),
        None => {
            crate::kprintln!("[boot] FATAL: unrecognised entry level {:#x}", entry_el);
            crate::cpu::fatal_halt();
        }
    }

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
    // **WS-BP BP2.6**: the identity map is built from the image's layout and
    // board constants — nothing is parsed before translation is enabled.  The
    // device-tree pointer is only checked: the window a reader may dereference
    // must lie in guaranteed RAM and outside the image.
    crate::mmu::init_mmu(dtb_ptr);
    crate::kprintln!(
        "[boot] MMU enabled (identity map, guaranteed RAM to {:#x})",
        crate::mmu::GUARANTEED_RAM_TOP
    );

    // Set VBAR_EL1 to exception vector table.  WS-SM SM1.C.2 extracted
    // the previously-private helper into `install_exception_vectors`
    // (shared with `smp::rust_secondary_main`); the primary call site
    // now uses the same code path the secondaries do.
    install_exception_vectors();
    crate::kprintln!("[boot] VBAR_EL1 set to exception vector table");
    // The v0.36.2 audit: with the vectors installed, an asynchronous external
    // abort is reported and halts (`trap::handle_serror`) rather than staying
    // pending and silent for the life of the boot.
    crate::interrupts::enable_serror();
    // ...and the cache-maintenance stride this HAL assumes is checked against
    // the PE's own `CTR_EL0` rather than trusted from the TRM.
    crate::cache::verify_cache_line_stride_or_halt(crate::cpu::fatal_halt);

    // -----------------------------------------------------------------------
    // Phase 3: GIC-400 and timer initialization (AG5)
    // -----------------------------------------------------------------------
    crate::kprintln!("[boot] Initializing GIC-400...");
    crate::gic::init_gic();
    crate::kprintln!("[boot] GIC-400 initialized (distributor + CPU interface)");

    // WS-SM SM7.B.3: register the `.tlbShootdownReq` (INTID 1) handler in
    // the SM1.F.5 SGI table.  Single-core, IRQs still masked, before
    // `bring_up_secondaries` — exactly the `register_sgi_handler`
    // write-once-at-boot contract; secondaries observe the registration
    // through the CPU_ON release edge.
    //
    // SAFETY: boot phase 3 runs on the primary core alone with PSTATE.I
    // set; no SGI can be taken and no other core is online yet.
    unsafe {
        crate::shootdown::register_tlb_shootdown_handler();
    }
    crate::kprintln!("[boot] TLB shootdown SGI handler registered (INTID 1)");

    // WS-SM SM0.H (PR #854 review): register the `haltAll` (INTID 4)
    // handler. Reserved since SM0.H and declared on the Lean side, it had
    // no implementation, so the fail-closed halt could stop only the core
    // that detected the fault.
    //
    // SAFETY: same boot-phase-3 conditions as the registration above --
    // primary core alone, PSTATE.I set, no secondary online yet.
    unsafe {
        crate::gic::register_halt_all_handler();
    }
    crate::kprintln!("[boot] halt-all SGI handler registered (INTID 4)");

    // WS-SM SM5.C.5: register the `.reschedule` (INTID 0) handler — the
    // receiver seam of the cross-core wake protocol.  A remote wake
    // enqueues the woken thread on this core's run queue and fires this
    // SGI; the handler drives the verified reschedule transition
    // (`lean_per_core_reschedule`) under the kernel-entry lock.
    //
    // SAFETY: same boot-phase-3 conditions as the registrations above --
    // primary core alone, PSTATE.I set, no secondary online yet.
    unsafe {
        crate::trap::register_reschedule_sgi_handler();
    }
    crate::kprintln!("[boot] reschedule SGI handler registered (INTID 0)");

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
    // Phase 4: TPIDR_EL1 setup (the IRQ enable moved after Phase 5, BP6.2)
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
    // `enable_irq()`.  Pre-SM1.I the then-current single-core IRQ
    // handler never read TPIDR_EL1, so that ordering was functionally
    // safe; moving the write here made the discipline robust against
    // the per-core handler that later became the live IRQ path
    // (SM5's `handle_irq_per_core`).
    //
    // WS-SM SM1.I.4 update: `handle_synchronous_exception` now reads
    // TPIDR_EL1 via `crate::per_cpu_stats::record_*` (each branch
    // increments a per-core counter through `current_per_cpu_stats`).
    // This makes the Phase-4-before-enable_irq ordering MANDATORY,
    // not merely defensive — any synchronous exception from EL0
    // (SVC, page fault from a user-mode caller) lands in
    // `handle_synchronous_exception` and would dereference an
    // uninitialised TPIDR_EL1 if it fired before Phase 4.  EL0 code
    // does not run until the Lean kernel installs its state in Phase 5, which
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
    // WS-SM SM1.I.1 / SM5: `handle_irq_per_core` (the live IRQ path —
    // `trap.S`'s IRQ vectors branch to it) reads TPIDR_EL1, so the IRQ
    // path joins the synchronous-exception path in depending on it —
    // both are safe after the audit-pass-4 Phase 1 write.
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

    // WS-BP BP6.2: IRQ delivery is NOT enabled here any more.  The boot core
    // unmasks only after Phase 5 has installed the kernel state and the core
    // has marked itself Lean-ready, which is the order every secondary keeps
    // too — so no PE takes an interrupt in the degraded, Rust-only mode once
    // the kernel exists.  Nothing in Phase 5 waits on an interrupt: the timer
    // armed in Phase 3 pends until the unmask, and a shootdown's initiator
    // never needs its own acknowledgment.

    // -----------------------------------------------------------------------
    // Phase 5: the kernel-state install (WS-BP BP4.1/BP4.2)
    //
    // `lean_kernel_main` writes the whole kernel state and the labeling
    // context outside every lock bracket (`kernel_entry.rs`).  It therefore
    // runs here, on the boot core alone, **before** Phase 6 releases any
    // secondary — so no bracketed committer exists while it runs, and the
    // lost-commit shape a concurrent secondary tick would produce cannot
    // occur.  The ordering is a type, not a comment: the bring-up consumes a
    // `SecondaryReleasePermit`, and on an image that links the Lean kernel the
    // only one is what `enter_lean_kernel` returns after the install.  An
    // image with no Lean kernel (`hw_target` off: the host lane, the QEMU
    // HAL-only boots) has no install to order and uses `no_lean_kernel`.
    //
    // A refused boot does not return: `lean_kernel_main` is the device-tree
    // boot with its failure handled
    // (`Platform.FFI.bootAndInitialiseRPi5FromDtbOrHalt`, WS-BP BP4.4), which
    // halts the system inside the call on a blob the verified parser refuses,
    // on a board that is not a Raspberry Pi 5, and on a refused boot.  The
    // firmware's blob reaches it as a `ByteArray` the HAL copies (BP4.3).
    // -----------------------------------------------------------------------
    #[cfg(feature = "hw_target")]
    let secondary_release = {
        // WS-BP BP2.3/BP2.4: initialize the Lean library, halting the system
        // if it refuses, then enter the kernel with the proof that it ran.
        let initialised = crate::lean_entry::initialise_lean_library();
        let permit = crate::lean_entry::enter_lean_kernel(initialised, dtb_ptr);
        crate::kprintln!("[boot] Phase 5: kernel state installed");
        permit
    };
    #[cfg(not(feature = "hw_target"))]
    let secondary_release = crate::lean_entry::SecondaryReleasePermit::no_lean_kernel();

    // WS-BP BP6.1/BP6.2: the boot core's per-PE runtime handshake, then its
    // readiness, then — and only then — IRQ delivery.  The per-image half ran
    // just above (`enter_lean_kernel` publishes the install); the per-PE half
    // checks that this PE is core 0, translates, runs on the boot stack, and
    // that the kernel heap serves it.  A refusal halts the system: no
    // secondary has been released, and a boot core that cannot serve the
    // kernel is a boot that failed.  `build.rs` (`readiness_publication_status`)
    // holds this statement after the install and before `enable_irq`.
    #[cfg(feature = "hw_target")]
    crate::lean_ready::become_ready_or_halt(0, crate::gic::halt_all);
    crate::interrupts::enable_irq();
    crate::kprintln!("[boot] IRQ delivery enabled");

    // -----------------------------------------------------------------------
    // Phase 6: WS-SM SM1.D — DTB cmdline parse + secondary-core bring-up
    //
    // SM1.D.1: parse the kernel command-line from the DTB's
    // `/chosen/bootargs` property (or use defaults if the DTB is
    // absent / malformed / missing the property).  The default config
    // (`CmdlineConfig::default()`) has `smp_enabled = true` and
    // `smp_max_cores = 4`.  Maintainer decision #7 enables SMP by
    // default at v1.0.0 *once SM5 lands*; SM5.I serialised kernel entry
    // at v0.32.142, so the default is opt-out again — see `cmdline.rs`
    // and `SMP_TLB_SHOOTDOWN_PLAN.md` §"Kernel-entry serialisation".
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
    // the boot core ran kernel code.  Post-SM1.D, and with SM5.I's
    // kernel-entry lock live since v0.32.142, all 4 RPi5 cores are
    // online by default once the kernel state is installed; an operator opts
    // out with `smp_enabled=false`.
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
    let online = crate::cmdline::apply_cmdline_and_start_smp(&cmdline_cfg, secondary_release);
    if cmdline_cfg.smp_enabled {
        crate::kprintln!(
            "[boot] Phase 6: {} secondary core(s) online (max requested: {})",
            online,
            cmdline_cfg.smp_max_cores
        );
    } else {
        crate::kprintln!("[boot] Phase 6: SMP disabled by cmdline (single-core boot)");
    }

    // -----------------------------------------------------------------------
    // Phase 7: Handoff summary + the topology refusal
    // -----------------------------------------------------------------------
    crate::kprintln!();
    crate::kprintln!("[boot] Hardware initialization complete:");
    crate::kprintln!("  UART   : PL011 UART10 @ 0x10_7D00_1000 (115200 8N1)");
    crate::kprintln!("  MMU    : identity map (guaranteed RAM + device window)");
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
    crate::kprintln!("[boot] Boot complete");

    // WS-BP BP4.2 / BP6.3: the topology refusal, now that the secondaries have
    // had their bounded window to publish readiness.  It is the runtime half of
    // "no seam is left dormant": every PE the linked kernel declares must have
    // marked itself Lean-ready and unmasked its IRQs within the window, or the
    // boot halts the system rather than running a kernel one core cannot
    // serve.  No EL0 thread has run yet — the first dispatch is a scheduling
    // point this refusal precedes on every core but the ones already serving —
    // so a mismatch halts before anything is served to user space.
    #[cfg(feature = "hw_target")]
    {
        // PR #889 review round 21: the linked Lean kernel declares its PE count
        // at compile time (`PlatformBinding.coreCount` = 4 for `RPi5Platform`,
        // carried into the live machine as `MachineState.declaredCoreCount`),
        // and since round 20 that number bounds `.tcbSetAffinity`.  `online` is
        // a *runtime* fact: `smp_enabled=false` starts no secondaries, an
        // `smp_max_cores` cap starts fewer, and a PSCI `CPU_ON` can fail.
        // Handing a 4-PE kernel a narrower machine strands every thread pinned
        // to an absent core — queued where nothing runs it, with the reschedule
        // SGI sent to a PE that cannot take it — and reports success.
        //
        // The two numbers are not reconcilable at this seam: `lean_kernel_main`
        // takes the device tree and nothing else, and a kernel that adapts its
        // topology at runtime is SM10.1's to build.  So the mismatch is
        // refused rather than papered over, which is what this whole cut is
        // about.  An operator who wants fewer PEs declares a binding with that
        // `coreCount`, exactly as `SimSingleCorePlatform` does; `smp_enabled=false`
        // remains fully supported for a HAL-only image, which links no Lean
        // kernel and never reaches this block.
        // PR #889 review round 23: `online` counts PSCI `CPU_ON` calls that
        // returned `Success` or `AlreadyOn` — a *proxy* for "this PE will
        // service kernel work", incremented before the secondary has run a
        // single instruction of its own init.  A PE can still halt in MMU, GIC
        // or timer setup, and an `AlreadyOn` PE may never reach
        // `secondary_entry` at all, while `online` stays at three.  The fact
        // itself is `CORE_IRQ_READY[c]`, which core `c` publishes *itself*
        // after `enable_irq` and which `shootdown.rs` already reads as the
        // IRQ-serviceable set — so this waits for it, bounded, rather than
        // trusting the proxy.  A core that never publishes leaves
        // `running_cores` short and the topology refusal below fires.
        //
        // WS-BP BP6.3: and it waits for **Lean** readiness too
        // (`smp::core_serves`).  IRQ-readiness alone is satisfied by a PE that
        // unmasked interrupts with every gated seam still dormant, which is
        // exactly the kernel "one core cannot serve".
        let running_cores = crate::smp::serving_core_count_within(
            LEAN_DECLARED_CORE_COUNT,
            SECONDARY_READY_TIMEOUT_TICKS,
        );
        if running_cores != LEAN_DECLARED_CORE_COUNT {
            crate::kprintln!(
                "[boot] FATAL: {} PE(s) serving the kernel but the linked Lean kernel declares {} \
                 ({} PSCI CPU_ON call(s) succeeded)",
                running_cores,
                LEAN_DECLARED_CORE_COUNT,
                1 + online
            );
            // The v0.36.2 audit: name the PE and the half it is short of, so
            // a board with one dead core reports which one and whether it
            // failed before its handshake (no Lean readiness) or before it
            // unmasked (no IRQ readiness).
            for core in 0..LEAN_DECLARED_CORE_COUNT as usize {
                let (irq_ready, lean_ready) = crate::smp::core_readiness(core);
                if !(irq_ready && lean_ready) {
                    crate::kprintln!(
                        "[boot]   PE {core}: IRQ-ready {irq_ready}, Lean-ready {lean_ready}"
                    );
                }
            }
            // PR #889 review round 22: `halt_all`, not `fatal_halt`.  This
            // condition is reached *after* the secondaries that did start have
            // entered `rust_secondary_main`, unmasked IRQs and begun servicing
            // timer and SGI handlers, so parking only the boot PE leaves them
            // running Rust-side interrupt work for a kernel that was never
            // handed off to.  A boot-fatal condition needs a system-wide
            // barrier, which is what this function is for and why
            // `ffi_fatal_halt_all`, the kernel-entry tripwire and the
            // shootdown timeout all use it.  Per-PE `fatal_halt` stays correct
            // for a per-PE fault — the VBAR check below is one.
            crate::gic::halt_all();
        }
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
/// runtime check re-checks the alignment before writing `VBAR_EL1`
/// so a regressed assembler/linker chain surfaces as a clean halt
/// rather than the architectural UNDEFINED instruction the next
/// exception would produce (ARM ARM D17.2.135: writes with bits
/// [10:0] non-zero are UNDEFINED).  **WS-RR RR5.18**: unconditional,
/// not a `debug_assert!` — the image that ships is a `--release` build,
/// which compiled the old form out.
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
/// — and, since WS-RR RR5.18, is a real runtime check in every profile
/// rather than a debug-only one.
pub fn install_exception_vectors() {
    #[cfg(target_arch = "aarch64")]
    {
        extern "C" {
            static __exception_vectors: u8;
        }
        // `&raw const` on an extern static forms an address without
        // performing an access, which is a safe operation — the `unsafe`
        // that used to wrap this expression was rejected as unnecessary
        // the first time the aarch64 target was compiled (WS-RR RR1.3).
        // The obligation it documented still holds and is discharged
        // structurally: `__exception_vectors` is a linker-provided symbol
        // defined in `vectors.S` under `.balign 2048`, and only its
        // address is taken here — the value is never read.  The
        // check below re-checks the alignment that `write_vbar_el1`
        // depends on.
        let vbar = &raw const __exception_vectors as u64;
        // AN8-E (R-HAL-L9): runtime alignment check before VBAR_EL1 write.
        // ARM ARM D17.2.135: VBAR_EL1 bits [10:0] are RES0 — a misaligned
        // address produces an UNDEFINED instruction on the next exception
        // entry. We catch this here so the kernel halts in a debuggable
        // state rather than at exception time.
        //
        // **WS-RR RR5.18**: this was a `debug_assert_eq!`, which is compiled
        // out of a `--release` build — and a `kernel8.img` is built
        // `--release` (`scripts/test_qemu.sh`).  The check therefore existed
        // in exactly the configuration that cannot use it and vanished from
        // the one that ships, so the documented "clean halt rather than the
        // architectural UNDEFINED instruction" was true only of a debug
        // image.  It is now an unconditional branch to the fail-closed halt:
        // one modulo and one comparison, once per core at boot.
        if !vbar.is_multiple_of(2048) {
            crate::kprintln!(
                "[boot] FATAL: exception vector table is not 2048-byte aligned \
                 (VBAR=0x{:016x}); ARM ARM D1.10.2 / D17.2.135",
                vbar
            );
            crate::cpu::fatal_halt();
        }
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
    fn install_exception_vectors_callable_on_host() {
        // SM1.C.2: the helper resolves and runs cleanly on host.  The
        // `__exception_vectors` linker symbol is not available in
        // `cargo test` (no `vectors.S` linked), so the aarch64 branch
        // is cfg-gated out and only the barrier emissions execute.
        // This test catches a regression that introduces a host-side
        // panic in the barrier helpers.
        install_exception_vectors();
    }

    #[test]
    fn install_exception_vectors_signature_is_no_arg_fn() {
        // SM1.C.2: the helper takes no arguments — VBAR_EL1 is banked
        // per-core, and the `__exception_vectors` table is a single
        // shared symbol.  A future refactor that adds a parameter
        // would break the call sites in `rust_boot_main` and
        // `rust_secondary_main` simultaneously; pinning the signature
        // here surfaces such a regression at compile time.
        let _: fn() = install_exception_vectors;
    }

    #[test]
    fn install_exception_vectors_idempotent_on_host() {
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
    fn primary_boot_path_uses_install_exception_vectors() {
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
    // WS-SM SM1.D — Phase 6 wiring tests
    //
    // We cannot call `rust_boot_main` from host tests (it's `-> !` and
    // would attempt UART writes / MMIO that abort on host).  These tests
    // verify the Phase 6 helpers — `parse_cmdline_from_dtb` and
    // `apply_cmdline_and_start_smp` — resolve through the `crate::cmdline`
    // module path, and that `KERNEL_VERSION` stays in sync with
    // `lakefile.toml`.
    //
    // The textual presence of the Phase 6 call sites inside
    // `rust_boot_main` is enforced at build time by
    // `scan_boot_rs_calls_cmdline_smp_startup` in `build.rs`.
    // =====================================================================

    #[test]
    fn kernel_version_string_matches_lakefile() {
        // SM1.D: the Phase 1 banner uses `KERNEL_VERSION`; pin it at the
        // current SM2.A landing version (v0.31.9).  A future bump must
        // update this test in lockstep with `lakefile.toml`.
        // `scripts/check_version_sync.sh` (Tier 0) provides the
        // canonical drift check; this test is the local pin.
        assert_eq!(KERNEL_VERSION, "0.36.2");
    }

    /// PR #889 review round 21: the declared PE count this handoff enforces is
    /// the Lean binding's.  Pinned here so a change to `rpi5MachineConfig`'s
    /// `declaredCoreCount` (or to `rpi5PlatformBinding.coreCount`, which
    /// `declaredCoreCountAgrees` holds equal to it) fails the Rust build too,
    /// rather than silently letting the handoff enforce a stale number.
    #[test]
    fn lean_declared_core_count_matches_the_rpi5_binding() {
        assert_eq!(
            LEAN_DECLARED_CORE_COUNT,
            (crate::smp::MAX_SECONDARY_CORES + 1) as u32,
            "the handoff's declared PE count must be the topology the HAL brings up"
        );
        assert_eq!(
            LEAN_DECLARED_CORE_COUNT, 4,
            "RPi5Platform declares coreCount := 4"
        );
    }

    #[test]
    fn parse_cmdline_from_dtb_resolves_via_crate_cmdline() {
        // SM1.D: the Phase-5 entry point used by `rust_boot_main` is
        // `crate::cmdline::parse_cmdline_from_dtb`.  Pin the symbol
        // via fn-pointer coercion so a rename or signature drift
        // surfaces at compile time.
        let _: fn(u64) -> crate::cmdline::CmdlineConfig = crate::cmdline::parse_cmdline_from_dtb;
    }

    #[test]
    fn apply_cmdline_resolves_via_crate_cmdline() {
        // SM1.D: the Phase-6 SMP-start helper resolves through
        // `crate::cmdline::apply_cmdline_and_start_smp` and accepts a
        // `&CmdlineConfig` and the release permit (WS-BP BP4.2).
        let _: fn(
            &crate::cmdline::CmdlineConfig,
            crate::lean_entry::SecondaryReleasePermit,
        ) -> u32 = crate::cmdline::apply_cmdline_and_start_smp;
    }

    #[test]
    fn default_config_leaves_smp_disabled_until_kernel_entry_serialized() {
        // SM1.D.3: the Phase-5 path constructs a `CmdlineConfig` via
        // `parse_cmdline_from_dtb(0)` (NULL pointer → defaults), and
        // then stores `cfg.smp_enabled` straight into
        // `smp::SMP_ENABLED`.  This is therefore the test that decides
        // whether a real boot brings secondaries up, which is why it
        // is the boot-side half of the safety claim: SM5.I serialised
        // kernel entry at v0.32.142, so the default brings cores up.
        let cfg = crate::cmdline::parse_cmdline_from_dtb(0);
        assert!(
            cfg.smp_enabled,
            "Phase 6 default enables SMP now that SM5.I has landed (SM1.D.3)"
        );
    }

    #[test]
    fn default_config_sets_smp_max_cores_to_platform_max() {
        // SM1.D.6: the default `smp_max_cores` saturates to
        // `MAX_SECONDARY_CORES + 1 = 4` on RPi5.
        let cfg = crate::cmdline::parse_cmdline_from_dtb(0);
        assert_eq!(
            cfg.smp_max_cores,
            crate::smp::MAX_SECONDARY_CORES + 1,
            "Phase 6 default must be smp_max_cores=4 (SM1.D.6 / RPi5)"
        );
    }
}
