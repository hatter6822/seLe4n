// seLe4n ARM64 Boot Assembly
//
// Entry point for the kernel, placed at 0x80000 (standard RPi5 kernel load
// address). U-Boot or the RPi firmware loads the kernel image here and jumps
// to _start with:
//   x0 = DTB pointer (physical address of device tree blob)
//   x1-x3 = reserved (zero)
//
// Boot sequence:
//   0. Trap FP/SIMD at EL0 and EL1 (CPACR_EL1 := 0)
//   0.5 Reach EL1: the firmware enters at EL2 on the RPi5, so drop to
//       EL1h (`.L_enter_el1`); an entry at EL3 or any other level halts
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
    // Step 0: reach EL1 before anything else runs.  The Raspberry Pi 5
    // firmware enters a 64-bit kernel at EL2; QEMU's `virt` machine enters
    // at EL1.  `.L_enter_el1` returns at EL1 either way, with x0 (the DTB
    // pointer) intact and the entry level in x9, or halts this PE if it
    // was entered at EL3 or an unrecognised level.
    //
    // It runs FIRST because the FP trap below is written to a register
    // whose NAME depends on the level: at EL2 with HCR_EL2.E2H = 1 an
    // access spelled `cpacr_el1` is redirected to CPTR_EL2 (ARM ARM
    // D8.2.30, the VHE register redirection), and E2H resets to an
    // architecturally UNKNOWN value — so a write made before the drop
    // could land in the very register `.L_enter_el1` then overwrites,
    // leaving CPACR_EL1 at its UNKNOWN reset value and FP untrapped at
    // EL1 (the v0.36.2 audit).  `build.rs` (`scan_el1_entry`) requires
    // this call to be the first item of both entries and pins the
    // routine's body.
    // =====================================================================
    bl      .L_enter_el1

    // =====================================================================
    // Step 0.5: trap FP/SIMD at EL0 and EL1 — now at EL1, where
    // `cpacr_el1` names CPACR_EL1 unconditionally.
    //
    // CPACR_EL1 := 0 sets FPEN (and ZEN / SMEN) to 0b00: every FP, SIMD,
    // SVE and SME access at EL0 or EL1 traps (ARM ARM D19.2.30).  The
    // kernel is built FP-free (aarch64-unknown-none-softfloat), so the
    // trap costs it nothing, and a stray FP instruction becomes a halt
    // (`halt_if_kernel_origin`) instead of a silent clobber of the
    // interrupted thread's q0-q31, which the trap frame does not save.
    // No encoding traps EL1 alone, so EL0 FP traps too until threads
    // carry an FP context (WS-BP BP7); until then an EL0 access is
    // delivered as a userException fault.  The ISB makes the write take
    // effect before the next instruction.  `build.rs`
    // (`scan_fp_trap_prologue`) requires these two statements to follow
    // the `.L_enter_el1` call in both boot entries and refuses any other
    // write to CPACR_EL1.
    // =====================================================================
    msr     cpacr_el1, xzr
    isb
    mov     x20, x9                 // x20 = the level the firmware entered at

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
    // WS-SM SM0.M (closes SMP-M3): Zero the SMP secondary-core stacks.
    //
    // The `.smp_stacks` region (link.ld) is `(NOLOAD)` and therefore not
    // zeroed by the BSS sweep above.  This was harmless while SMP was
    // off by default and secondaries never entered; SM1 landed the PSCI
    // bring-up and SM5.I (v0.32.142) made SMP the default, so the
    // zeroing is now load-bearing rather than defensive — without it
    // the stale RAM contents are observable to secondary cores after
    // PSCI CPU_ON.  Closed structurally here rather than relying on the
    // "secondaries never enter" runtime invariant.
    //
    // Cost on Cortex-A76: 192 KiB / 16 B = 12 288 stp instructions ≈
    // 12 K cycles at one-issue-per-cycle for stp xzr, xzr — negligible
    // compared to the rest of the boot pipeline.
    // =====================================================================
    adrp    x0, __smp_secondary_stacks_bottom
    add     x0, x0, :lo12:__smp_secondary_stacks_bottom
    adrp    x1, __smp_secondary_stack_top
    add     x1, x1, :lo12:__smp_secondary_stack_top

.L_smp_stacks_zero_loop:
    cmp     x0, x1
    b.ge    .L_smp_stacks_done
    stp     xzr, xzr, [x0], #16
    b       .L_smp_stacks_zero_loop

.L_smp_stacks_done:
    // =====================================================================
    // Step 4: Set up kernel stack
    //
    // __stack_top is defined in the linker script, pointing to the top of
    // a 64 KiB stack region. Stack grows downward on AArch64.
    // =====================================================================
    adrp    x0, __stack_top
    add     x0, x0, :lo12:__stack_top

    // Ensure 16-byte alignment (AArch64 SP must be 16-byte aligned)
    // BEFORE the value reaches SP.  `AND (immediate)` accepts SP as its
    // destination but NOT as its source operand (ARM ARM C6.2.13:
    // `AND <Xd|SP>, <Xn>, #imm`), so `and sp, sp, #~0xF` does not
    // assemble.  Masking in the general register also means SP is never
    // transiently misaligned: with SCTLR_EL1.SA set, the first
    // SP-relative access after a misaligned `mov sp, xN` would raise an
    // SP alignment fault before the mask could run.
    and     x0, x0, #~0xF
    mov     sp, x0                  // SP = top of kernel stack

    // =====================================================================
    // Step 5: Branch to Rust boot entry point
    //
    // rust_boot_main(dtb_ptr: u64, entry_el: u64) -> ! defined in boot.rs;
    // `entry_el` is the CurrentEL value `.L_enter_el1` reported, which
    // decides the PSCI conduit (`psci::select_conduit`).
    // =====================================================================
    mov     x0, x19                 // x0 = DTB pointer (first argument)
    mov     x1, x20                 // x1 = entry CurrentEL (second argument)
    bl      rust_boot_main          // Call Rust entry point

    // rust_boot_main should never return, but if it does:
    b       .L_secondary_spin

// =========================================================================
// Secondary core spin loop — park non-primary cores
//
// Secondary cores enter a low-power WFE loop. Multi-core support (SMP) is
// implemented in WS-SM (tracked in
// docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md). The AN9-J scaffolding
// (DEF-R-HAL-L20) is the substrate; WS-SM activates and verifies it.
// To wake a secondary core, write to a mailbox and issue SEV.
//
// AK5-N (R-HAL-L9 / R-HAL-L16): Wake-storm risk is latent because the
// current kernel never issues SEV; any future WFE-aware spinlock must
// ensure secondary cores gate on a mailbox value before exiting WFE so a
// spurious SEV (or SEVL) does not cause all secondary cores to race into
// boot simultaneously. Documented here until WS-SM SM3 ships per-core
// parking mailboxes alongside the verified TicketLock primitive.
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
    // Step 0: reach EL1 before anything else runs on this PE.  PSCI
    // CPU_ON enters the target at the level of the CPU_ON caller
    // (DEN0022D), which is EL1 once the boot core has dropped, and an EL1
    // entry leaves this PE's EL2 state to the firmware as it does on the
    // boot core.  A firmware that enters a secondary at EL2 regardless is
    // not excluded, so every PE takes the same routine as the boot core —
    // and takes it first, for the reason `_start`'s Step 0 gives.
    // x0 (the PSCI context_id) survives it.
    bl      .L_enter_el1

    // Step 0.5: trap FP/SIMD at EL0 and EL1.  CPACR_EL1 is per-PE and
    // PSCI CPU_ON gives no guarantee about its value; see `_start`'s
    // Step 0.5.
    msr     cpacr_el1, xzr
    isb

    // Step 1: mask all maskable interrupts.  PSCI returns with DAIF
    // unset on some firmwares; do not assume.  Also mandatory before
    // the Step 1.5 invalid-context_id halt so the halt loop cannot be
    // interrupted into a partially-initialised state.
    msr     daifset, #0xf

    // =====================================================================
    // Step 1.5: WS-SM SM1.C audit-pass-2 defense-in-depth — validate the
    // PSCI context_id BEFORE the per-core stack and TPIDR_EL1 setup.
    //
    // The Step 2 SP arithmetic uses `context_id` directly:
    //   SP = __smp_secondary_stack_top - (context_id - 1) * 64 KiB
    // For `context_id == 0` the offset wraps around (effectively
    // +64 KiB above stack_top, into adjacent kernel memory); for
    // `context_id >= 4` (= MAX_SECONDARY_CORES + 1 on RPi5) the SP
    // falls inside or before the boot core's `.stack` region, so a
    // subsequent push from `rust_secondary_main`'s prologue would
    // corrupt the boot core's stack.
    //
    // The Rust-side `validate_secondary_context_id` (smp.rs) catches
    // the same conditions, but only AFTER the prologue runs — too late
    // to prevent the corruption.  This asm-level gate halts the
    // offending core in `.L_secondary_invalid` before any SP /
    // TPIDR_EL1 write that uses `context_id`.
    //
    // The bound is read from the Rust `MAX_CORE_COUNT_SYM` `.rodata`
    // symbol (not a literal) so a future PR bumping
    // `MAX_SECONDARY_CORES` automatically updates the asm-side bound
    // — same single-source-of-truth pattern as
    // `PER_CPU_DATA_SLOT_SIZE_SYM` (SM1.B) and `MPIDR_CORE_ID_MASK_SYM`
    // (AN8-B).
    //
    // x3 = MAX_CORE_COUNT_SYM value (= MAX_SECONDARY_CORES + 1 = 4)
    // =====================================================================
    cbz     x0, .L_secondary_invalid  // reject context_id == 0 (boot slot)
    adrp    x3, MAX_CORE_COUNT_SYM
    ldr     x3, [x3, :lo12:MAX_CORE_COUNT_SYM]
    cmp     x0, x3
    b.hs    .L_secondary_invalid      // reject context_id >= total core count

    // Step 2: per-core stack.  Use `__smp_secondary_stack_top` defined
    // by the linker script + offset by (context_id - 1) * 64 KiB.
    // Since context_id is in x0, offset = (x0 - 1) * 0x10000.
    // Step 1.5 has rejected `context_id == 0` and `context_id >= 4`,
    // so `context_id` is in `[1, 3]` here and the SP arithmetic is
    // structurally safe.
    sub     x1, x0, #1               // x1 = secondary index (0..=2)
    lsl     x1, x1, #16              // x1 = index * 0x10000 (64 KiB)
    adrp    x2, __smp_secondary_stack_top
    add     x2, x2, :lo12:__smp_secondary_stack_top
    sub     x2, x2, x1               // x2 = stack_top - offset
    // Align in the general register before the value reaches SP: `AND
    // (immediate)` cannot take SP as its source operand, and an
    // intermediate misaligned SP would fault on the first SP-relative
    // access.  See the primary path above.
    and     x2, x2, #~0xF            // ensure 16-byte alignment
    mov     sp, x2                   // sp = aligned per-core stack top

    // =====================================================================
    // WS-SM SM0.N / SM1.B (closes SMP-M4): set TPIDR_EL1 to per-CPU data base.
    //
    // ARMv8-A reserves TPIDR_EL1 as the kernel's per-core scratch
    // register (ARM ARM D17.2.139).  At kernel-mode entry, every core
    // expects TPIDR_EL1 to point at its own `PerCpuData` slot in the
    // `PER_CPU_DATA` array (per_cpu.rs — moved from smp.rs at SM1.B;
    // the symbol name is unchanged thanks to `#[no_mangle]`).  Loading
    // the slot address here (before any Rust code executes on this
    // core) gives `mrs xN, tpidr_el1` a defined value from the very
    // first instruction of `rust_secondary_main`.
    //
    // Slot offset = context_id * sizeof(PerCpuData) where the layout
    // is PER_CPU_DATA[0] = boot core, PER_CPU_DATA[1..3] = secondaries.
    // x0 already holds context_id from the PSCI calling convention.
    //
    // The slot stride is the Rust constant `PER_CPU_DATA_SLOT_SIZE`
    // (per_cpu.rs).  Rather than hard-code the literal here (which
    // would silently drift if the Rust struct grew without updating
    // the asm), the slot stride is read from the `.rodata` symbol
    // `PER_CPU_DATA_SLOT_SIZE_SYM` via the same `adrp`+`ldr` pattern
    // AN8-B uses for `MPIDR_CORE_ID_MASK_SYM`.  This makes the Rust
    // constant the single source of truth — any inconsistency between
    // the struct size and the asm-observed stride is structurally
    // impossible because there is no asm-observed stride independent
    // of the symbol.
    //
    // x4 = address of PER_CPU_DATA[0]
    // x5 = PER_CPU_DATA_SLOT_SIZE = sizeof(PerCpuData)
    // x6 = TPIDR_EL1 = PER_CPU_DATA + context_id * PER_CPU_DATA_SLOT_SIZE
    // =====================================================================
    adrp    x4, PER_CPU_DATA
    add     x4, x4, :lo12:PER_CPU_DATA
    adrp    x5, PER_CPU_DATA_SLOT_SIZE_SYM
    ldr     x5, [x5, :lo12:PER_CPU_DATA_SLOT_SIZE_SYM]
    madd    x6, x0, x5, x4           // x6 = x0 * stride + x4
    msr     tpidr_el1, x6

    // Step 3: jump to Rust per-core init with the original context_id.
    //
    // Note: x0 already holds context_id from the PSCI calling
    // convention (DEN0022D §5.1.7), so no register reshuffle is
    // needed — Rust's `extern "C"` ABI takes the first argument in x0.
    bl      rust_secondary_main

    // rust_secondary_main is `-> !` so this should be unreachable.
    // If we ever fall through, halt the core in a low-power loop.
    b       .L_secondary_spin

// =========================================================================
// WS-SM SM1.C audit-pass-2: invalid PSCI context_id halt.
//
// Reached only when the PSCI firmware passes an out-of-range context_id
// (== 0 or >= MAX_CORE_COUNT_SYM).  DAIF was masked at the top of
// `secondary_entry`, so this loop runs uninterruptible.  We never wrote
// SP or TPIDR_EL1 (the validation runs BEFORE those steps), so no
// per-core state has been corrupted on this core.  The primary core and
// any already-initialised secondaries continue running unaffected.
//
// This is the asm-layer companion to Rust-side
// `validate_secondary_context_id`; both layers reject the same
// conditions, but the asm layer catches them BEFORE the SP / TPIDR_EL1
// arithmetic uses `context_id`, preventing boot-core stack corruption
// (which would otherwise happen for context_id == 4 — the resulting SP
// would land at __smp_secondary_stacks_bottom, adjacent to the boot
// core's stack).
// =========================================================================
.L_secondary_invalid:
    wfe
    b       .L_secondary_invalid

// =========================================================================
// WS-BP BP5.5: enter EL1 from whichever level the firmware chose.
//
// Called by `bl` as each entry's first action, ahead of the FP prologue (a
// `cpacr_el1` write at EL2 may denote CPTR_EL2 — see `_start`'s Step 0), with
// no stack (SP_EL1 is UNKNOWN on an EL2 entry until the caller sets it).
// Clobbers x9, x10 and x30; preserves every other general register, so
// x0 — the DTB pointer on `_start`, the PSCI context_id on
// `secondary_entry` — reaches the caller unchanged.  `eret` writes no
// general register.  Returns in x9 the CurrentEL value it was entered at
// (#0x4 or #0x8): once EL2 is vacated nothing can service an `hvc`, so
// the PSCI conduit depends on it (`psci::select_conduit`).
//
// CurrentEL[3:2] is the level (ARM ARM D19.2.29):
//   0b01 (#0x4) EL1 — return;
//   0b10 (#0x8) EL2 — configure EL2 for a non-virtualised EL1 and `eret`
//                     to the caller at EL1h;
//   otherwise       — EL3 (or a value no architecture defines): halt.
// Interrupts are masked first, at every level: nothing below installs an
// EL2 vector table, so an exception taken at EL2 here would have nowhere
// to go.
//
// What the EL2 path writes, and why each one:
//   HCR_EL2     := RW (bit 31) alone.  EL1 is AArch64; TSC = 0, so an
//                  EL1 `smc` reaches the EL3 firmware; E2H = 0 (the
//                  non-VHE layout every register below is written in, made
//                  effective by the `isb` before CPTR_EL2); VM = 0 (no
//                  stage 2); IMO/FMO/AMO = 0, so IRQ, FIQ and SError are
//                  taken at EL1, where the kernel's vectors are.
//   CPTR_EL2    := 0x33FF.  TFP (bit 10) = 0, so FP/SIMD is not trapped to
//                  EL2 and the CPACR_EL1 trap the prologue set is the one
//                  that fires — an EL0 FP access must reach EL1's vectors,
//                  not an EL2 with no handler.  TTA, TAM and TCPAC are 0.
//                  Bits 13:12, 9:8 and 7:0 are written 1: on the
//                  Cortex-A76 (no SVE, no SME) TZ (bit 8) and TSM (bit 12)
//                  are RES1 with the rest.
//   CNTHCTL_EL2 := EL1PCTEN | EL1PCEN (0x3): EL1 reads the physical counter
//                  and owns the physical timer (`timer.rs`), untrapped.
//   CNTVOFF_EL2 := 0: the virtual counter equals the physical one.
//   VPIDR_EL2 / VMPIDR_EL2 := MIDR_EL1 / MPIDR_EL1: an EL1 read of MIDR or
//                  MPIDR returns these when EL2 exists, and their reset
//                  values are UNKNOWN — the core-id check in `_start` and
//                  every `current_core_id` read depend on the real MPIDR.
//   MDCR_EL2    := HPMN = PMCR_EL0.N when a PMU is implemented
//                  (ID_AA64DFR0_EL1.PMUVer not 0 or 0xF), else 0; every
//                  trap bit 0, so EL1's PMU (`profiling.rs`) and debug
//                  accesses are not trapped to EL2, and every counter is
//                  EL1's.
//   SCTLR_EL1   := 0x30D00800: its RES1 bits, MMU and caches off,
//                  little-endian (EE = E0E = 0).  Its reset value is
//                  UNKNOWN on an EL2 entry and the kernel runs with
//                  translation off until `init_mmu` writes the whole
//                  register.
//   SPSR_EL2    := 0x3C5: M = EL1h (0b0101), D, A, I, F masked.
//   ELR_EL2     := x30: the `eret` returns to the instruction after the
//                  caller's `bl`, now at EL1.
//
// `build.rs` (`scan_el1_entry`) pins this sequence item for item and
// refuses a write to any EL2 register anywhere else.
// =========================================================================
.L_enter_el1:
    msr     daifset, #0xf
    mrs     x9, currentel
    cmp     x9, #0x4
    b.ne    .L_enter_el1_from_el2
    ret
.L_enter_el1_from_el2:
    cmp     x9, #0x8
    b.ne    .L_unsupported_el
    mov     x9, #0x80000000
    msr     hcr_el2, x9
    isb
    mov     x9, #0x33ff
    msr     cptr_el2, x9
    mov     x9, #0x3
    msr     cnthctl_el2, x9
    msr     cntvoff_el2, xzr
    mrs     x9, midr_el1
    msr     vpidr_el2, x9
    mrs     x9, mpidr_el1
    msr     vmpidr_el2, x9
    mov     x10, xzr
    mrs     x9, s3_0_c0_c5_0         // ID_AA64DFR0_EL1 (op0 3, op1 0, CRn 0, CRm 5, op2 0)
    ubfx    x9, x9, #8, #4
    cbz     x9, .L_enter_el1_mdcr
    cmp     x9, #0xf
    b.eq    .L_enter_el1_mdcr
    mrs     x10, pmcr_el0
    ubfx    x10, x10, #11, #5
.L_enter_el1_mdcr:
    msr     mdcr_el2, x10
    mov     x9, #0x0800
    movk    x9, #0x30d0, lsl #16
    msr     sctlr_el1, x9
    mov     x9, #0x3c5
    msr     spsr_el2, x9
    msr     elr_el2, x30
    mov     x9, #0x8
    eret

// Entered at EL3 or an unrecognised level: this kernel neither runs at EL3
// nor knows how to leave it, so the PE halts here with interrupts masked.
.L_unsupported_el:
    wfe
    b       .L_unsupported_el
