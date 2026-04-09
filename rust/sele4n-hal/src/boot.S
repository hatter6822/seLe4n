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

_start:
    // =====================================================================
    // Step 1: Core ID check — only core 0 proceeds
    // =====================================================================
    mrs     x1, mpidr_el1           // Read Multiprocessor Affinity Register
    and     x1, x1, #0xFF          // Extract Aff0 (core number within cluster)
    cbnz    x1, .L_secondary_spin  // If not core 0, park

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
// deferred to WS-V. To wake a secondary core, write to a mailbox and issue
// SEV.
// =========================================================================
.L_secondary_spin:
    wfe
    b       .L_secondary_spin
