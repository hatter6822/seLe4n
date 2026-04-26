// seLe4n ARM64 Boot Assembly
//
// Entry point for the kernel, placed at 0x80000 (standard RPi5 kernel load
// address). U-Boot or the RPi firmware loads the kernel image here and jumps
// to _start with:
//   x0 = DTB pointer (physical address of device tree blob)
//   x1-x3 = reserved (zero)
//
// Boot sequence:
//   1. Read MPIDR_EL1 — park all cores except core 0
//   2. Save DTB pointer in callee-saved register (x19)
//   3. Zero the BSS section
//   4. Set up the kernel stack
//   5. Branch to Rust entry point (rust_boot_main)

.section .text.boot, "ax"
.global _start
.global secondary_entry

_start:
    // =====================================================================
    // Step 1: Core ID check — only cluster-0 core-0 proceeds
    //
    // AK5-I (R-HAL-M02 / MEDIUM): Mask Aff0|Aff1|Aff2 = bits [23:0]. A
    // core whose cluster ID is non-zero but whose per-cluster core number
    // is 0 (e.g., {Aff1=1, Aff0=0} on symmetric BCM2712, or {Aff2=1,
    // Aff0=0} on an asymmetric variant) would previously pass this check
    // because only Aff0 was examined. BCM2712's exact mapping is not
    // fully documented, so we mask all three low-affinity fields — this
    // is strictly more conservative than either Aff1-only or Aff2-only
    // masks and is the safe default.
    //
    // Mask 0x00FFFFFF = bits [23:0]. Bits 24 (MT) and 30 (U) are
    // INTENTIONALLY excluded — they are not part of the core identifier.
    //
    // AN8-B (H-18): The mask is pulled from the Rust `.rodata` symbol
    // `MPIDR_CORE_ID_MASK_SYM` (cpu.rs) via `adrp` + `ldr` instead of an
    // assembly-side literal. This keeps the Rust constant as the single
    // source of truth — any future edit to `MPIDR_CORE_ID_MASK` in Rust
    // automatically propagates here without manual assembly updates.
    // The `build.rs` scanner rejects any regression to the old
    // `mov x2, #0xFFFF ; movk x2, #0xFF, lsl #16` literal pattern.
    // =====================================================================
    mrs     x1, mpidr_el1
    adrp    x2, MPIDR_CORE_ID_MASK_SYM
    ldr     x2, [x2, :lo12:MPIDR_CORE_ID_MASK_SYM]
    and     x1, x1, x2              // x1 = MPIDR & MPIDR_CORE_ID_MASK
    cbnz    x1, .L_secondary_spin   // If not cluster 0 core 0, park

    // =====================================================================
    // Step 2: Save DTB pointer (x0) in callee-saved register
    // =====================================================================
    mov     x19, x0                 // x19 = DTB pointer (preserved across calls)

    // =====================================================================
    // Step 3: Zero BSS section
    //
    // __bss_start and __bss_end are defined in the linker script (link.ld).
    // BSS must be zeroed before any Rust code runs (static variables rely
    // on zero initialization).
    // =====================================================================
    adrp    x0, __bss_start         // x0 = page-aligned address of BSS start
    add     x0, x0, :lo12:__bss_start
    adrp    x1, __bss_end           // x1 = page-aligned address of BSS end
    add     x1, x1, :lo12:__bss_end

.L_bss_zero_loop:
    cmp     x0, x1                  // Check if we've reached the end
    b.ge    .L_bss_done
    stp     xzr, xzr, [x0], #16    // Store 16 bytes of zeros, advance
    b       .L_bss_zero_loop

.L_bss_done:
    // =====================================================================
    // Step 4: Set up kernel stack
    //
    // __stack_top is defined in the linker script, pointing to the top of
    // a 64 KiB stack region. Stack grows downward on AArch64.
    // =====================================================================
    adrp    x0, __stack_top
    add     x0, x0, :lo12:__stack_top
    mov     sp, x0                  // SP = top of kernel stack

    // Ensure 16-byte alignment (AArch64 SP must be 16-byte aligned)
    and     sp, sp, #~0xF

    // =====================================================================
    // Step 5: Branch to Rust boot entry point
    //
    // rust_boot_main(dtb_ptr: u64) -> ! defined in boot.rs
    // =====================================================================
    mov     x0, x19                 // x0 = DTB pointer (first argument)
    bl      rust_boot_main          // Call Rust entry point

    // rust_boot_main should never return, but if it does:
    b       .L_secondary_spin

// =========================================================================
// Secondary core spin loop — park non-primary cores
//
// Secondary cores enter a low-power WFE loop. Multi-core support (SMP) is
// closed by AN9-J (DEF-R-HAL-L20) per
// docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12. To wake a secondary
// core, write to a mailbox and issue SEV.
//
// AK5-N (R-HAL-L9 / R-HAL-L16): Wake-storm risk is latent because the
// current kernel never issues SEV; any future WFE-aware spinlock must
// ensure secondary cores gate on a mailbox value before exiting WFE so a
// spurious SEV (or SEVL) does not cause all secondary cores to race into
// boot simultaneously. Documented here until AN9-J adds the proper SMP
// bring-up with a per-core parking mailbox (closes DEF-R-HAL-L20).
// =========================================================================
.L_secondary_spin:
    wfe
    b       .L_secondary_spin

// =========================================================================
// AN9-J (DEF-R-HAL-L20): Secondary-core entry point
//
// PSCI CPU_ON (psci.rs::cpu_on) jumps here on each secondary core after
// the primary issues `hvc #0` with PSCI function id 0xC4000003.  The
// firmware sets up x0 = context_id (passed as the third PSCI argument).
//
// Responsibilities:
//   1. Mask interrupts (DAIF = 0xF) so the secondary cannot take an
//      asynchronous trap before its trap-frame storage is set up.
//   2. Set up a per-core stack.  At v1.0.0 with SMP_ENABLED=false this
//      symbol is never reached at runtime; we still need to provide a
//      working stack so that the linker resolves the address and so
//      that opting into SMP at deployment time does not require an
//      assembly rebuild.  Per-core stack regions are allocated in the
//      `.bss.smp_stacks` section by `smp.rs` and selected by
//      `(context_id - 1) * 0x10000` (64 KiB per secondary).
//   3. Branch to `rust_secondary_main(context_id)` which performs the
//      remaining per-core initialisation (MMU, GIC, ready-flag spin).
//
// Each secondary core is responsible for its own MMU + GIC bring-up
// inside `rust_secondary_main`; this assembly stub is purely the
// entry-point shim PSCI requires.
//
// AN9-J test discipline: the `bring_up_secondaries` host stub does
// NOT call this function (it cannot — there is no actual core to wake
// on host).  The symbol is reachable only via the production-build
// PSCI HVC path on aarch64 firmware.
// =========================================================================
secondary_entry:
    // Step 1: mask all maskable interrupts.  PSCI returns with DAIF
    // unset on some firmwares; do not assume.
    msr     daifset, #0xf

    // Step 2: per-core stack.  Use `__smp_secondary_stack_top` defined
    // by the linker script + offset by (context_id - 1) * 64 KiB.
    // Since context_id is in x0, offset = (x0 - 1) * 0x10000.
    sub     x1, x0, #1               // x1 = secondary index (0..=2)
    lsl     x1, x1, #16              // x1 = index * 0x10000 (64 KiB)
    adrp    x2, __smp_secondary_stack_top
    add     x2, x2, :lo12:__smp_secondary_stack_top
    sub     sp, x2, x1               // sp = stack_top - offset
    and     sp, sp, #~0xF            // ensure 16-byte alignment

    // Step 3: jump to Rust per-core init with the original context_id.
    //
    // Note: x0 already holds context_id from the PSCI calling
    // convention (DEN0022D §5.1.7), so no register reshuffle is
    // needed — Rust's `extern "C"` ABI takes the first argument in x0.
    bl      rust_secondary_main

    // rust_secondary_main is `-> !` so this should be unreachable.
    // If we ever fall through, halt the core in a low-power loop.
    b       .L_secondary_spin
