// seLe4n ARM64 Exception Vector Table
//
// ARM ARM D1.10.2: The vector table must be 2048-byte aligned (VBAR_EL1).
// Each entry is 128 bytes (32 instructions maximum). There are 16 entries
// organized as 4 exception types × 4 source states.
//
// Layout:
//   Offset 0x000: Current EL with SP0 (Synchronous)
//   Offset 0x080: Current EL with SP0 (IRQ)
//   Offset 0x100: Current EL with SP0 (FIQ)
//   Offset 0x180: Current EL with SP0 (SError)
//   Offset 0x200: Current EL with SPx (Synchronous)
//   Offset 0x280: Current EL with SPx (IRQ)
//   Offset 0x300: Current EL with SPx (FIQ)
//   Offset 0x380: Current EL with SPx (SError)
//   Offset 0x400: Lower EL, AArch64  (Synchronous)
//   Offset 0x480: Lower EL, AArch64  (IRQ)
//   Offset 0x500: Lower EL, AArch64  (FIQ)
//   Offset 0x580: Lower EL, AArch64  (SError)
//   Offset 0x600: Lower EL, AArch32  (Synchronous)
//   Offset 0x680: Lower EL, AArch32  (IRQ)
//   Offset 0x700: Lower EL, AArch32  (FIQ)
//   Offset 0x780: Lower EL, AArch32  (SError)

.section .text.vectors, "ax"
.global __exception_vectors

.balign 2048
__exception_vectors:

// =========================================================================
// Current EL with SP0 (not used — seLe4n always uses SPx at EL1)
//
// AK5-N (R-HAL-L10): These vectors are formally unreachable. seLe4n
// enters EL1 with SPSel=1 (SPx) and never switches to SP0; therefore an
// exception taken to "Current EL with SP0" indicates a corrupted PSTATE.
// The `__exception_stub` infinite-WFE loop treats this as a terminal
// fault (see the SP0-unreachable rationale in WS-V SMP design notes).
// =========================================================================

// 0x000: Synchronous — Current EL, SP0
.balign 128
    b   __exception_stub

// 0x080: IRQ — Current EL, SP0
.balign 128
    b   __exception_stub

// 0x100: FIQ — Current EL, SP0
.balign 128
    b   __exception_stub

// 0x180: SError — Current EL, SP0
.balign 128
    b   __exception_stub

// =========================================================================
// Current EL with SPx (kernel-to-kernel exceptions)
// =========================================================================

// 0x200: Synchronous — Current EL, SPx (e.g., kernel page fault)
.balign 128
    b   __el1_sync_entry

// 0x280: IRQ — Current EL, SPx (interrupt while in kernel)
.balign 128
    b   __el1_irq_entry

// 0x300: FIQ — Current EL, SPx (not used)
.balign 128
    b   __exception_stub

// 0x380: SError — Current EL, SPx
.balign 128
    b   __el1_serror_entry

// =========================================================================
// Lower EL, AArch64 (user-to-kernel exceptions — primary path)
// =========================================================================

// 0x400: Synchronous — Lower EL, AArch64 (SVC syscall entry)
.balign 128
    b   __el0_sync_entry

// 0x480: IRQ — Lower EL, AArch64 (interrupt from user mode)
.balign 128
    b   __el0_irq_entry

// 0x500: FIQ — Lower EL, AArch64 (not used)
.balign 128
    b   __exception_stub

// 0x580: SError — Lower EL, AArch64
.balign 128
    b   __el0_serror_entry

// =========================================================================
// Lower EL, AArch32 (not supported by seLe4n)
// =========================================================================

// 0x600: Synchronous — Lower EL, AArch32
.balign 128
    b   __exception_stub

// 0x680: IRQ — Lower EL, AArch32
.balign 128
    b   __exception_stub

// 0x700: FIQ — Lower EL, AArch32
.balign 128
    b   __exception_stub

// 0x780: SError — Lower EL, AArch32
.balign 128
    b   __exception_stub

// =========================================================================
// Stub for unused vectors — infinite WFE loop
// =========================================================================
__exception_stub:
    wfe
    b   __exception_stub
