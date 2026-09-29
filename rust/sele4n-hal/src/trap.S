// seLe4n ARM64 Trap Entry/Exit Assembly
//
// Saves the full CPU context (31 GPRs + SP_EL0 + ELR_EL1 + SPSR_EL1 +
// TPIDR_EL0) into
// a TrapFrame on the kernel stack, calls the appropriate Rust handler, then
// restores context and returns via ERET.
//
// TrapFrame layout (304 bytes, must match trap.rs TrapFrame):
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
//   Offset 288: TPIDR_EL0 (v0.36.30 — the thread pointer EL0 writes untrapped;
//               saved and restored so no thread reads another's)
//   Offset 296: padding (keeps the frame 16-byte aligned)

.section .text

// =========================================================================
// save_context macro — push TrapFrame onto kernel stack
//
// Pre-condition:  SP points to kernel stack with sufficient space
// Post-condition: SP points to TrapFrame base, x0 = SP (frame pointer)
// =========================================================================
.macro save_context
    // Allocate TrapFrame on stack (304 bytes, 16-byte aligned).  AK5-F
    // grew it 272 -> 288 for ESR_EL1 + FAR_EL1; v0.36.30 grew it to 304 for
    // TPIDR_EL0 and one padding word.
    sub     sp, sp, #304

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

    // v0.36.30: Save TPIDR_EL0 at offset 288.  EL0 writes it with no trap,
    // so it is thread context: restore_context writes back what the frame
    // holds, which is this value unless a context restore installed another
    // thread's.
    mrs     x0, tpidr_el0
    str     x0, [sp, #288]

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

    // v0.36.30: Restore TPIDR_EL0 (offset 288).
    ldr     x0, [sp, #288]
    msr     tpidr_el0, x0

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

    // Deallocate TrapFrame — 304 bytes.
    add     sp, sp, #304

    // Return from exception — restores PC from ELR, PSTATE from SPSR
    eret
.endm

// =========================================================================
// set_fault_stack macro — PR #904 (`v0.36.41`)
//
// After an EL0 entry has saved the thread's SP_EL0 into the frame, point SP_EL0
// at this PE's fault stack top, `__fault_stacks_bottom + (core + 1) *
// FAULT_STACK_SIZE`, with the core read from `PerCpuData.core_id` at offset 0
// of the slot TPIDR_EL1 names.  Every PE holds SP_EL0 there while it runs at
// EL1, so an EL1-origin fault (`vectors.S` 0x200 / 0x380) has a stack; the
// thread's own value comes back from the frame in `restore_context`.
// Clobbers x1 and x2 only — both already saved — and preserves x0 (the frame).
// =========================================================================
.macro set_fault_stack
    mrs     x1, tpidr_el1
    ldr     x1, [x1]                 // PerCpuData.core_id
    add     x1, x1, #1
    lsl     x1, x1, #14              // (core + 1) * FAULT_STACK_SIZE (16 KiB)
    adrp    x2, __fault_stacks_bottom
    add     x2, x2, :lo12:__fault_stacks_bottom
    add     x1, x1, x2
    msr     sp_el0, x1
.endm

// =========================================================================
// EL0 Synchronous — SVC syscall entry (primary user-to-kernel path)
// =========================================================================
.global __el0_sync_entry
__el0_sync_entry:
    save_context
    set_fault_stack
    bl      handle_synchronous_exception
    restore_context

// =========================================================================
// EL0 IRQ — interrupt from user mode
// =========================================================================
// WS-SM SM5: routed to the per-core IRQ handler (`handle_irq_per_core`),
// which reads the executing core's id from TPIDR_EL1, records per-core
// IRQ statistics, drives the verified Lean per-core scheduler timer tick
// on the timer PPI, and dispatches SGIs with genuine source-CPU
// attribution.  This replaced the single-core `handle_irq` when the SM5
// per-core scheduler state landed (the redirect the SM1.I.1 seam was
// staged for).  Pinned by `build.rs::scan_trap_s_irq_vector_redirect`.
.global __el0_irq_entry
__el0_irq_entry:
    save_context
    set_fault_stack
    bl      handle_irq_per_core
    restore_context

// =========================================================================
// EL0 SError — system error from user mode
// =========================================================================
.global __el0_serror_entry
__el0_serror_entry:
    save_context
    set_fault_stack
    bl      handle_serror
    // handle_serror is declared `-> !` (never returns; body is `loop { wfe() }`).
    // If the compiler ever dropped the divergence contract, `b .` halts the
    // core here rather than racing off the end of the section or attempting an
    // ERET with SError-corrupted context. Per AK10 dead-code removal and the
    // audit's original R-HAL-M12 remediation ("make signature `-> !` and `b .`
    // after `bl` in asm").
    b       .

// =========================================================================
// EL1 Synchronous — kernel-mode exception (page fault, etc.)
// =========================================================================
.global __el1_sync_entry
__el1_sync_entry:
    save_context
    bl      handle_synchronous_exception
    // PR #904 (`v0.36.41`): an EL1-origin synchronous exception is the
    // kernel's own fault and `handle_synchronous_exception` halts the PE on it
    // (`halt_if_kernel_origin`) before anything else.  It runs on the fault
    // stack (`vectors.S` 0x200), so there is no frame to return through: park
    // rather than `eret` if the halt were ever relaxed.
    b       .

// =========================================================================
// EL1 IRQ — interrupt while in kernel
// =========================================================================
// WS-SM SM5: same per-core routing as `__el0_irq_entry` above.
.global __el1_irq_entry
__el1_irq_entry:
    save_context
    bl      handle_irq_per_core
    restore_context

// =========================================================================
// EL1 SError — system error in kernel mode
// =========================================================================
.global __el1_serror_entry
__el1_serror_entry:
    save_context
    bl      handle_serror
    // AK10 dead-code removal: the `-> !` divergence of handle_serror makes
    // the previous `restore_context` unreachable. Replaced with `b .` per
    // the audit's original R-HAL-M12 remediation so the kernel halts here
    // rather than attempting an ERET with SError-corrupted context if the
    // divergence contract is ever relaxed.
    b       .
