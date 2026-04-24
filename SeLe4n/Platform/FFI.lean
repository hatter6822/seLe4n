/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

/-!
# FFI Bridge: Lean Kernel → Rust HAL

> **STATUS: staged for H3 hardware binding** (AN7-D.6 / PLT-M07).  This
> module is wired into `SeLe4n.Platform.Staged` so every CI run verifies
> it compiles.  See `docs/spec/SELE4N_SPEC.md` §8.15 for the activation
> roadmap.

AG7-A-iii/iv: `@[extern]` declarations for Lean-to-Rust FFI bridge.

Each declaration corresponds to a `#[no_mangle] pub extern "C"` function in
`rust/sele4n-hal/src/ffi.rs`. On hardware builds (`HW_TARGET` option), the Lean
compiler resolves these symbols against `libsele4n_hal.a`. On simulation builds,
pure-model stubs provide equivalent semantics for testing.

## Function groups

- **Timer**: Counter read, tick count, reprogram
- **GIC**: IRQ acknowledge, end-of-interrupt, spurious check
- **TLB**: Full flush, per-ASID flush, per-VAddr flush
- **MMIO**: 32/64-bit volatile read/write
- **UART**: Debug character output
- **Interrupts**: Enable/disable interrupt delivery

## Conditional compilation

The `@[extern]` attribute is only active when building with
`-DhwTarget=true` (hardware target). Otherwise, the functions
resolve to pure stubs matching the simulation platform contract.
-/

namespace SeLe4n.Platform.FFI

-- ============================================================================
-- AG7-A-iii: Timer FFI declarations
-- ============================================================================

/-- Read the ARM Generic Timer physical counter (CNTPCT_EL0).
    Returns the current 64-bit counter value (54 MHz on RPi5).
    Rust: `ffi_timer_read_counter` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_timer_read_counter"]
opaque ffiTimerReadCounter : BaseIO UInt64

/-- Reprogram the timer comparator for the next tick interval and
    increment the tick counter.
    Rust: `ffi_timer_reprogram` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_timer_reprogram"]
opaque ffiTimerReprogram : BaseIO Unit

/-- Get the current tick count (timer interrupts since boot).
    Rust: `ffi_timer_get_tick_count` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_timer_get_tick_count"]
opaque ffiTimerGetTickCount : BaseIO UInt64

-- ============================================================================
-- AG7-A-iii: GIC FFI declarations
-- ============================================================================

/-- Acknowledge a pending GIC interrupt (read GICC_IAR).
    Returns the INTID (bits [9:0]).
    Rust: `ffi_gic_acknowledge` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_gic_acknowledge"]
opaque ffiGicAcknowledge : BaseIO UInt32

/-- Signal end-of-interrupt to the GIC (write GICC_EOIR).
    Rust: `ffi_gic_eoi` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_gic_eoi"]
opaque ffiGicEoi : UInt32 → BaseIO Unit

/-- Check if an interrupt ID is spurious (INTID >= 1020).
    Rust: `ffi_gic_is_spurious` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_gic_is_spurious"]
opaque ffiGicIsSpurious : UInt32 → BaseIO Bool

-- ============================================================================
-- AG7-A-iii: TLB FFI declarations
-- ============================================================================

/-- Flush all TLB entries at EL1 (TLBI VMALLE1 + DSB ISH + ISB).
    Rust: `ffi_tlbi_all` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_tlbi_all"]
opaque ffiTlbiAll : BaseIO Unit

/-- Flush TLB entries by ASID at EL1 (TLBI ASIDE1 + DSB ISH + ISB).
    Rust: `ffi_tlbi_by_asid` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_tlbi_by_asid"]
opaque ffiTlbiByAsid : UInt16 → BaseIO Unit

/-- Flush TLB entries by virtual address + ASID (TLBI VAE1 + DSB ISH + ISB).
    Rust: `ffi_tlbi_by_vaddr` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_tlbi_by_vaddr"]
opaque ffiTlbiByVaddr : UInt16 → UInt64 → BaseIO Unit

-- ============================================================================
-- AG7-A-iii: MMIO FFI declarations
-- ============================================================================

/-- Read a 32-bit value from an MMIO address (volatile).
    Rust: `ffi_mmio_read32` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_mmio_read32"]
opaque ffiMmioRead32 : UInt64 → BaseIO UInt32

/-- Write a 32-bit value to an MMIO address (volatile).
    Rust: `ffi_mmio_write32` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_mmio_write32"]
opaque ffiMmioWrite32 : UInt64 → UInt32 → BaseIO Unit

/-- Read a 64-bit value from an MMIO address (volatile).
    Rust: `ffi_mmio_read64` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_mmio_read64"]
opaque ffiMmioRead64 : UInt64 → BaseIO UInt64

/-- Write a 64-bit value to an MMIO address (volatile).
    Rust: `ffi_mmio_write64` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_mmio_write64"]
opaque ffiMmioWrite64 : UInt64 → UInt64 → BaseIO Unit

-- ============================================================================
-- AG7-A-iii: UART FFI declarations
-- ============================================================================

/-- Transmit a single character on the debug UART (PL011).
    Rust: `ffi_uart_putc` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_uart_putc"]
opaque ffiUartPutc : UInt8 → BaseIO Unit

-- ============================================================================
-- AG7-A-iii: Interrupt FFI declarations
-- ============================================================================

/-- Disable all maskable interrupts. Returns saved DAIF for restoration.
    Rust: `ffi_disable_interrupts` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_disable_interrupts"]
opaque ffiDisableInterrupts : BaseIO UInt64

/-- Restore interrupt state from a previously saved DAIF value.
    Rust: `ffi_restore_interrupts` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_restore_interrupts"]
opaque ffiRestoreInterrupts : UInt64 → BaseIO Unit

/-- Enable IRQ delivery (clear PSTATE.I).
    Rust: `ffi_enable_interrupts` in `sele4n-hal/src/ffi.rs` -/
@[extern "ffi_enable_interrupts"]
opaque ffiEnableInterrupts : BaseIO Unit

end SeLe4n.Platform.FFI
