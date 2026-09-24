/* seLe4n Kernel Linker Script for Raspberry Pi 5
 *
 * Memory layout:
 *   0x00000000 – 0x40000000 : RAM every Raspberry Pi 5 has (the smallest
 *                             board's 1 GiB) — the image, arena included,
 *                             must lie inside it, because it is the RAM the
 *                             boot map covers (`mmu::GUARANTEED_RAM_TOP`)
 *   0xFE000000 – 0xFF850000 : Peripherals (BCM2712 + GIC-400)
 *
 * Kernel load address: 0x80000 (standard RPi5 kernel entry point, matching
 * the address used by U-Boot and the RPi firmware bootloader).
 *
 * Section order: .text.boot → .text.vectors → .text → .rodata → .data → .bss
 */

ENTRY(_start)

/* WS-BP BP2.1: the Lean heap arena's size.  A link-time constant: the kernel's
 * Lean runtime is served from `.lean_heap` below and from nothing else, so the
 * heap is exactly this big on every board and no firmware or device tree can
 * change it.  Raising it is this one line; the ASSERTs at the end refuse a
 * value the smallest Raspberry Pi 5 cannot hold. */
LEAN_HEAP_SIZE = 64M;

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000, LENGTH = 0x3FF80000
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

    /* Kernel code.  WS-BP BP2.6: the boot map's permission boundaries are
     * assigned inside the sections they bound.  `[_start, __text_end)` is
     * mapped read-only and executable, `[__rodata_start, __rodata_end)`
     * read-only and never executable, and everything after it writable and
     * never executable (`mmu::image_layout`).  Each is page aligned, because a
     * permission cannot change inside a 4 KiB page, and the read-only data must
     * begin exactly where the text ends — so no section between the two (an
     * orphan the linker places on its own) can be mapped executable.  Inside
     * the sections, because `lld` attaches a location-counter change written
     * *between* sections to the section that follows, which would move a
     * boundary with the very gap it exists to detect; and an assignment inside
     * `.rodata` keeps that section and its address even when it holds no
     * input. */
    .text : ALIGN(4096) {
        *(.text .text.*)
        . = ALIGN(4096);
        __text_end = .;
    } > RAM

    /* Read-only data */
    .rodata : ALIGN(4096) {
        __rodata_start = .;
        *(.rodata .rodata.*)
        . = ALIGN(4096);
        __rodata_end = .;
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

    /* AN9-J (DEF-R-HAL-L20): per-core stacks for SMP secondaries.
     *
     * Three 64 KiB regions, one per secondary core (BCM2712 has 3
     * secondaries — 4 cores total, primary uses `.stack` above).
     * Each secondary's `secondary_entry` (boot.S) computes its own
     * stack top via `__smp_secondary_stack_top - (context_id - 1) *
     * 0x10000`.
     *
     * Reachable only when `SMP_ENABLED=true`, which is the default
     * since SM5.I serialised kernel entry (v0.32.142); the linker keeps
     * the section present so the symbol resolves in either
     * configuration.
     */
    .smp_stacks (NOLOAD) : ALIGN(16) {
        __smp_secondary_stacks_bottom = .;
        . += (3 * 64K);
        __smp_secondary_stack_top = .;
    } > RAM

    /* WS-BP BP2.1: the Lean heap arena.  `NOLOAD`, so it costs the image
     * file nothing and the firmware copies nothing into it; `boot.S` does not
     * zero it either — `lean_heap::Heap::from_arena` initialises every
     * metadata byte it reads and never reads the pages it serves.  4 KiB
     * aligned, because the allocator's pages are MMU granules.  Its bounds are
     * the only way the Rust side learns the extent
     * (`lean_heap::arena_extent`), and the boot map's critical ranges include
     * it (`mmu::image_ranges`), so translation is never enabled over tables
     * that leave the heap unmapped. */
    .lean_heap (NOLOAD) : ALIGN(4096) {
        __lean_heap_start = .;
        . += LEAN_HEAP_SIZE;
        __lean_heap_end = .;
    } > RAM

    /* Discard unneeded sections */
    /DISCARD/ : {
        *(.comment)
        *(.note.*)
        *(.eh_frame*)
    }
}

/* WS-BP BP2.1: the arena is a whole number of pages, and the whole image —
 * arena included — ends inside the smallest Raspberry Pi 5's RAM, which is
 * [0, 1 GiB) (`rpi5Variants` in SeLe4n/Platform/RPi5/Board.lean, and
 * `mmu::GUARANTEED_RAM_TOP`, the RAM the boot map covers).  A heap that does
 * not fit is a link error, never a boot-time surprise. */
ASSERT(LEAN_HEAP_SIZE % 4096 == 0, "LEAN_HEAP_SIZE must be a whole number of 4 KiB pages")
ASSERT(__lean_heap_start % 4096 == 0, "the Lean heap arena must be 4 KiB aligned")
ASSERT(__lean_heap_end <= 0x40000000, "the image, Lean heap included, must end inside the smallest RPi5's 1 GiB of RAM")

/* WS-BP BP2.6: the permission boundaries `mmu::ImageLayout::is_well_formed`
 * requires — each on a page, the text non-empty and ahead of the read-only
 * data, which starts where the text ends. */
ASSERT(_start % 4096 == 0, "the kernel text must start on a 4 KiB page")
ASSERT(__text_end % 4096 == 0 && __text_end > _start, "the kernel text must end on a 4 KiB page after it starts")
ASSERT(__rodata_start == __text_end, "the read-only data must begin where the kernel text ends")
ASSERT(__rodata_end % 4096 == 0 && __rodata_end >= __text_end, "the read-only data must end on a 4 KiB page")
