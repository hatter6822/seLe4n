// seLe4n ARM64 Trap Entry/Exit Assembly
//
// Saves the full CPU context (31 GPRs + SP_EL0 + ELR_EL1 + SPSR_EL1) into
// a TrapFrame on the kernel stack, calls the appropriate Rust handler, then
// restores context and returns via ERET.
//
// TrapFrame layout (288 bytes, must match trap.rs TrapFrame):
//   Offset   0: x0-x1   (stp pair)
//   Offset  16: x2-x3
//   Offset  32: x4-x5
//   Offset  48: x6-x7
//   Offset  64: x8-x9
//   Offset  80: x10-x11
//   Offset  96: x12-x13
//   Offset 112: x14-x15
//   Offset 128: x16-x17
//   Offset 144: x18-x19
//   Offset 160: x20-x21
//   Offset 176: x22-x23
//   Offset 192: x24-x25
//   Offset 208: x26-x27
//   Offset 224: x28-x29
//   Offset 240: x30 (LR)
//   Offset 248: SP_EL0
//   Offset 256: ELR_EL1
//   Offset 264: SPSR_EL1
//   Offset 272: ESR_EL1  (AK5-F — snapshot at entry)
//   Offset 280: FAR_EL1  (AK5-F — snapshot at entry)

.section .text

// =========================================================================
// save_context macro — push TrapFrame onto kernel stack
//
// Pre-condition:  SP points to kernel stack with sufficient space
// Post-condition: SP points to TrapFrame base, x0 = SP (frame pointer)
// =========================================================================
.macro save_context
    // AK5-F: Allocate TrapFrame on stack (288 bytes, 16-byte aligned).
    // Previously 272; extended by 16 bytes to hold ESR_EL1 + FAR_EL1.
    sub     sp, sp, #288

    // Save x0-x29 in pairs
    stp     x0,  x1,  [sp, #0]
    stp     x2,  x3,  [sp, #16]
    stp     x4,  x5,  [sp, #32]
    stp     x6,  x7,  [sp, #48]
    stp     x8,  x9,  [sp, #64]
    stp     x10, x11, [sp, #80]
    stp     x12, x13, [sp, #96]
    stp     x14, x15, [sp, #112]
    stp     x16, x17, [sp, #128]
    stp     x18, x19, [sp, #144]
    stp     x20, x21, [sp, #160]
    stp     x22, x23, [sp, #176]
    stp     x24, x25, [sp, #192]
    stp     x26, x27, [sp, #208]
    stp     x28, x29, [sp, #224]

    // Save x30 (LR)
    str     x30, [sp, #240]

    // Save SP_EL0
    mrs     x0, sp_el0
    str     x0, [sp, #248]

    // Save ELR_EL1 (return address)
    mrs     x0, elr_el1
    str     x0, [sp, #256]

    // Save SPSR_EL1 (saved processor state)
    mrs     x0, spsr_el1
    str     x0, [sp, #264]

    // AK5-F: Snapshot ESR_EL1 at offset 272. Handlers read this instead
    // of the live register so nested exceptions cannot corrupt the value.
    mrs     x0, esr_el1
    str     x0, [sp, #272]

    // AK5-F: Snapshot FAR_EL1 at offset 280. Same rationale as ESR.
    mrs     x0, far_el1
    str     x0, [sp, #280]

    // x0 = pointer to TrapFrame (first argument to Rust handler)
    mov     x0, sp
.endm

// =========================================================================
// restore_context macro — pop TrapFrame from kernel stack and ERET
//
// Pre-condition:  SP points to TrapFrame base
// Post-condition: Returns to ELR_EL1 with restored PSTATE from SPSR_EL1
// =========================================================================
.macro restore_context
    // AK5-F: ESR_EL1 and FAR_EL1 are read-only in the TrapFrame (snapshot
    // at entry). They are NOT restored to hardware on exception return —
    // ELR/SPSR alone control the return path. Skip offsets 272/280.

    // Restore SPSR_EL1
    ldr     x0, [sp, #264]
    msr     spsr_el1, x0

    // Restore ELR_EL1
    ldr     x0, [sp, #256]
    msr     elr_el1, x0

    // Restore SP_EL0
    ldr     x0, [sp, #248]
    msr     sp_el0, x0

    // Restore x30 (LR)
    ldr     x30, [sp, #240]

    // Restore x0-x29 in pairs
    ldp     x28, x29, [sp, #224]
    ldp     x26, x27, [sp, #208]
    ldp     x24, x25, [sp, #192]
    ldp     x22, x23, [sp, #176]
    ldp     x20, x21, [sp, #160]
    ldp     x18, x19, [sp, #144]
    ldp     x16, x17, [sp, #128]
    ldp     x14, x15, [sp, #112]
    ldp     x12, x13, [sp, #96]
    ldp     x10, x11, [sp, #80]
    ldp     x8,  x9,  [sp, #64]
    ldp     x6,  x7,  [sp, #48]
    ldp     x4,  x5,  [sp, #32]
    ldp     x2,  x3,  [sp, #16]
    ldp     x0,  x1,  [sp, #0]

    // AK5-F: Deallocate TrapFrame — 288 bytes (was 272).
    add     sp, sp, #288

    // Return from exception — restores PC from ELR, PSTATE from SPSR
    eret
.endm

// =========================================================================
// EL0 Synchronous — SVC syscall entry (primary user-to-kernel path)
// =========================================================================
.global __el0_sync_entry
__el0_sync_entry:
    save_context
    bl      handle_synchronous_exception
    restore_context

// =========================================================================
// EL0 IRQ — interrupt from user mode
// =========================================================================
.global __el0_irq_entry
__el0_irq_entry:
    save_context
    bl      handle_irq
    restore_context

// =========================================================================
// EL0 SError — system error from user mode
// =========================================================================
.global __el0_serror_entry
__el0_serror_entry:
    save_context
    bl      handle_serror
    // handle_serror does not return (loops on WFE), but if it ever did:
    restore_context

// =========================================================================
// EL1 Synchronous — kernel-mode exception (page fault, etc.)
// =========================================================================
.global __el1_sync_entry
__el1_sync_entry:
    save_context
    bl      handle_synchronous_exception
    restore_context

// =========================================================================
// EL1 IRQ — interrupt while in kernel
// =========================================================================
.global __el1_irq_entry
__el1_irq_entry:
    save_context
    bl      handle_irq
    restore_context

// =========================================================================
// EL1 SError — system error in kernel mode
// =========================================================================
.global __el1_serror_entry
__el1_serror_entry:
    save_context
    bl      handle_serror
    // AK5-K (R-HAL-M12): handle_serror is declared `-> !` (never returns)
    // so this restore_context is formally dead. It stays as a defensive
    // fall-through: if a future refactor ever relaxes the signature, the
    // kernel still terminates via ERET rather than racing off the end of
    // the section.
    restore_context
