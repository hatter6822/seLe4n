// SPDX-License-Identifier: GPL-3.0-or-later
// seLe4n  - A Lean Microkernel
// Copyright (C) 2026  Adam Hall
// This program comes with ABSOLUTELY NO WARRANTY.
// This is free software, and you are welcome to redistribute it
// under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
//
// WS-BP BP7.9 -- the lazy FP/SIMD switch's register routines.
//
// The kernel is FP-free (`aarch64-unknown-none-softfloat`, and
// `scripts/check_fp_simd_free_objects.py` over the object code), and these
// four routines are the ONE exception: a thread's FP/SIMD context has to be
// moved between its TCB and the registers by code that names them.  They live
// in their own section, `.text.sele4n_fp_context`, and the disassembly gate
// exempts exactly `sele4n_fp_save_context` and `sele4n_fp_load_context` BY
// SYMBOL -- reconciled both ways, so an FP register anywhere else still fails
// it and an exemption that stops naming one is reported stale.
//
// They are also the only code outside the boot prologues that writes
// CPACR_EL1 (`build.rs`'s `FP_CONTEXT_CPACR_WRITERS` pins each write to its
// routine).  FPEN = 0b11 (bits [21:20], `0x300000`) lifts the FP/SIMD trap at
// EL0 and EL1; ZEN and SMEN stay 0, so SVE and SME still trap, and a thread
// that uses them takes a `userException` fault.
//
// Buffer layout (66 doublewords, 16-byte aligned), the Lean `FpContext.word`
// layout: `v0`..`v31` as 32 little-endian 128-bit values (word `2n` is
// `vN[63:0]`, word `2n+1` is `vN[127:64]`), then FPCR at word 64 and FPSR at
// word 65.

.section .text.sele4n_fp_context

// -------------------------------------------------------------------------
// sele4n_fp_save_context(x0 = *mut [u64; 66])
//
// Lift the trap, store the live registers, and ARM the trap again: a capture
// is taken exactly when the registers are about to stop being the running
// thread's, so nothing that runs next may reach them without trapping.
// -------------------------------------------------------------------------
.balign 4
.global sele4n_fp_save_context
.type sele4n_fp_save_context, %function
sele4n_fp_save_context:
    mov     x9, #0x300000
    msr     cpacr_el1, x9
    isb
    stp     q0, q1, [x0, #0]
    stp     q2, q3, [x0, #32]
    stp     q4, q5, [x0, #64]
    stp     q6, q7, [x0, #96]
    stp     q8, q9, [x0, #128]
    stp     q10, q11, [x0, #160]
    stp     q12, q13, [x0, #192]
    stp     q14, q15, [x0, #224]
    stp     q16, q17, [x0, #256]
    stp     q18, q19, [x0, #288]
    stp     q20, q21, [x0, #320]
    stp     q22, q23, [x0, #352]
    stp     q24, q25, [x0, #384]
    stp     q26, q27, [x0, #416]
    stp     q28, q29, [x0, #448]
    stp     q30, q31, [x0, #480]
    mrs     x9, fpcr
    mrs     x10, fpsr
    str     x9, [x0, #512]
    str     x10, [x0, #520]
    msr     cpacr_el1, xzr
    isb
    ret
.size sele4n_fp_save_context, . - sele4n_fp_save_context

// -------------------------------------------------------------------------
// sele4n_fp_load_context(x0 = *const [u64; 66])
//
// Lift the trap and load every register the context names, FPCR and FPSR
// included, so nothing a previous owner left in them survives.  The trap
// stays lifted: the thread whose context this is resumes next.
// -------------------------------------------------------------------------
.balign 4
.global sele4n_fp_load_context
.type sele4n_fp_load_context, %function
sele4n_fp_load_context:
    mov     x9, #0x300000
    msr     cpacr_el1, x9
    isb
    ldp     q0, q1, [x0, #0]
    ldp     q2, q3, [x0, #32]
    ldp     q4, q5, [x0, #64]
    ldp     q6, q7, [x0, #96]
    ldp     q8, q9, [x0, #128]
    ldp     q10, q11, [x0, #160]
    ldp     q12, q13, [x0, #192]
    ldp     q14, q15, [x0, #224]
    ldp     q16, q17, [x0, #256]
    ldp     q18, q19, [x0, #288]
    ldp     q20, q21, [x0, #320]
    ldp     q22, q23, [x0, #352]
    ldp     q24, q25, [x0, #384]
    ldp     q26, q27, [x0, #416]
    ldp     q28, q29, [x0, #448]
    ldp     q30, q31, [x0, #480]
    ldr     x9, [x0, #512]
    ldr     x10, [x0, #520]
    msr     fpcr, x9
    msr     fpsr, x10
    ret
.size sele4n_fp_load_context, . - sele4n_fp_load_context

// -------------------------------------------------------------------------
// sele4n_fp_trap_lift() -- the core resumes its FP owner, whose values the
// registers already hold: lift the trap and touch no FP/SIMD register.
// -------------------------------------------------------------------------
.balign 4
.global sele4n_fp_trap_lift
.type sele4n_fp_trap_lift, %function
sele4n_fp_trap_lift:
    mov     x9, #0x300000
    msr     cpacr_el1, x9
    isb
    ret
.size sele4n_fp_trap_lift, . - sele4n_fp_trap_lift

// -------------------------------------------------------------------------
// sele4n_fp_trap_arm() -- the core resumes anything but its FP owner: arm the
// trap (CPACR_EL1 := 0, the boot prologue's value).
// -------------------------------------------------------------------------
.balign 4
.global sele4n_fp_trap_arm
.type sele4n_fp_trap_arm, %function
sele4n_fp_trap_arm:
    msr     cpacr_el1, xzr
    isb
    ret
.size sele4n_fp_trap_arm, . - sele4n_fp_trap_arm
