/* seLe4n Kernel Linker Script for Raspberry Pi 5
 *
 * Memory layout:
 *   0x00000000 – 0xFC000000 : RAM (4032 MiB, BCM2712 4GB model)
 *   0xFE000000 – 0xFF850000 : Peripherals (BCM2712 + GIC-400)
 *
 * Kernel load address: 0x80000 (standard RPi5 kernel entry point, matching
 * the address used by U-Boot and the RPi firmware bootloader).
 *
 * Section order: .text.boot → .text.vectors → .text → .rodata → .data → .bss
 */

ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000, LENGTH = 0xFBF80000
}

SECTIONS
{
    /* Boot code — must be at the load address (0x80000) */
    .text.boot : {
        KEEP(*(.text.boot))
    } > RAM

    /* Exception vector table — 2048-byte aligned per ARM ARM D1.10.2 */
    .text.vectors : ALIGN(2048) {
        KEEP(*(.text.vectors))
    } > RAM

    /* Kernel code */
    .text : ALIGN(4096) {
        *(.text .text.*)
    } > RAM

    /* Read-only data */
    .rodata : ALIGN(4096) {
        *(.rodata .rodata.*)
    } > RAM

    /* Initialized data */
    .data : ALIGN(4096) {
        *(.data .data.*)
    } > RAM

    /* Uninitialized data — zeroed during boot (boot.S) */
    .bss (NOLOAD) : ALIGN(4096) {
        __bss_start = .;
        *(.bss .bss.*)
        *(COMMON)
        . = ALIGN(16);
        __bss_end = .;
    } > RAM

    /* AK5-E.4: Boot page tables live inside `.bss` now (the `PageTableCell`
     * wrapper is declared `static` with `repr(align(4096))`), so the
     * dedicated `.bss.page_tables` section is no longer required. The
     * linker places `BOOT_L1_TABLE` at a 4 KiB-aligned offset inside
     * `.bss` which satisfies the ARMv8 TTBR BAADDR alignment.
     *
     * AN8-E (R-HAL-L6) cross-reference: see `sele4n-hal/src/mmu.rs`
     * (`PageTableCell` + `BOOT_L1_TABLE` definitions) for the Rust-side
     * struct. The `.bss` ALIGN(4096) directive above is what allows
     * `#[repr(align(4096))]` on `PageTableCell` to be satisfied without
     * extra linker arithmetic — the struct's first byte is naturally on
     * a 4 KiB boundary, matching the TTBR0_EL1 BAADDR contract.
     */

    /* Kernel stack — 64 KiB, 16-byte aligned (AArch64 SP requirement) */
    .stack (NOLOAD) : ALIGN(16) {
        __stack_bottom = .;
        . += 64K;
        __stack_top = .;
    } > RAM

    /* Discard unneeded sections */
    /DISCARD/ : {
        *(.comment)
        *(.note.*)
        *(.eh_frame*)
    }
}
