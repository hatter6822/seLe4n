//! Boot sequence for the seLe4n microkernel on Raspberry Pi 5.
//!
//! Entry flow: ATF → U-Boot → `_start` (boot.S) → `rust_boot_main` (this file).
//!
//! Phase 1: UART initialization → boot banner
//! Phase 2: MMU initialization → VBAR_EL1 setup
//! Phase 3: GIC-400 + ARM Generic Timer initialization (AG5)
//! Phase 4: Handoff to Lean kernel (AG7 — FFI bridge)

/// Kernel version string — matches Lean lakefile.toml version.
const KERNEL_VERSION: &str = "0.28.4";

/// Rust entry point called from assembly `_start` after BSS zeroing and
/// stack setup. Receives the DTB pointer from U-Boot in x0.
///
/// This function must never return. If the kernel main returns (which it
/// shouldn't), we enter an infinite WFE loop.
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

    // Set VBAR_EL1 to exception vector table
    set_vbar();
    crate::kprintln!("[boot] VBAR_EL1 set to exception vector table");

    // -----------------------------------------------------------------------
    // Phase 3: GIC-400 and timer initialization (AG5)
    // -----------------------------------------------------------------------
    crate::kprintln!("[boot] Initializing GIC-400...");
    crate::gic::init_gic();
    crate::kprintln!("[boot] GIC-400 initialized (distributor + CPU interface)");

    crate::kprintln!("[boot] Initializing timer (1000 Hz)...");
    // AJ5-C/L-14: init_timer now returns Result — on failure, log the error
    // and halt via idle_loop since the kernel cannot function without a timer.
    match crate::timer::init_timer(crate::timer::DEFAULT_TICK_HZ) {
        Ok(()) => {}
        Err(e) => {
            crate::kprintln!("[boot] FATAL: timer init failed: {:?}", e);
            idle_loop();
        }
    }
    crate::kprintln!("[boot] Timer initialized (54 MHz counter, 1ms ticks)");

    // Enable IRQ delivery now that GIC and timer are configured
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

/// Set VBAR_EL1 to point to our exception vector table.
///
/// The vector table is defined in `vectors.S` and exported as
/// `__exception_vectors`. It must be 2048-byte aligned per ARM ARM D1.10.2.
fn set_vbar() {
    #[cfg(target_arch = "aarch64")]
    {
        extern "C" {
            static __exception_vectors: u8;
        }
        // SAFETY: __exception_vectors is a linker-provided symbol defined in
        // vectors.S with .balign 2048. We're reading its address, not its value.
        let vbar = unsafe { &raw const __exception_vectors as u64 };
        crate::registers::write_vbar_el1(vbar);
    }
    crate::barriers::dsb_sy();
    crate::barriers::isb();
}

/// Infinite idle loop — WFE to save power while waiting for events.
/// Used as the final state after boot when no kernel main is available yet.
fn idle_loop() -> ! {
    loop {
        crate::cpu::wfe();
    }
}
