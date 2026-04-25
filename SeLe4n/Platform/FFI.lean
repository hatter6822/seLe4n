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

-- ============================================================================
-- AN9-D (DEF-C-M04): suspendThread atomicity bracket
-- ============================================================================

/-- AN9-D (DEF-C-M04): Lean → Rust direction.  Calls the
    `sele4n_suspend_thread` Rust wrapper that brackets the inner Lean
    dispatch with `with_interrupts_disabled`.

    Used when a Lean module invoking `suspendThread` from a path that
    must enforce hardware atomicity (i.e., not the abstract
    sequential model) wants to ensure the FFI bracket is in place.

    See `rust/sele4n-hal/src/ffi.rs::sele4n_suspend_thread`. -/
@[extern "sele4n_suspend_thread"]
opaque ffiSuspendThread : UInt64 → BaseIO UInt32

/-- AN9-D inner — Rust → Lean direction.  Exported so the Rust
    `sele4n_suspend_thread` wrapper can call back into the Lean
    suspend dispatch (after `with_interrupts_disabled` is set up).

    `@[export]` instructs the Lean compiler to emit a C-callable
    `suspend_thread_inner` symbol; the Rust side declares
    `extern "C" { fn suspend_thread_inner(...) -> u32; }` in
    `rust/sele4n-hal/src/ffi.rs`.

    Returns a `KernelError` discriminant; `0` means success (matching
    the `KernelError::Ok` slot reserved at AK4-A).  At v1.0.0 this is
    the Rust-→-Lean channel; substantive routing into the Lean
    `suspendThread` API is the closure work tracked in
    `docs/HARDWARE_TESTING.md` §4.3. -/
@[export suspend_thread_inner]
def suspendThreadInner (_tid : UInt64) : UInt32 :=
  -- KernelError::NotImplemented = 17 until the AN9-D Lean glue routes
  -- into `suspendThread` proper (requires threading the active
  -- SystemState through the FFI, which is the v1.x work item).
  17

-- ============================================================================
-- AN9-F (DEF-R-HAL-L14): SVC dispatch entry — Rust → Lean direction
-- ============================================================================

/-- AN9-F: Lean-side SVC dispatch routine called BY Rust through the
    `syscall_dispatch_inner` `extern "C"` symbol.  This is the
    Rust-→-Lean direction (opposite of every other declaration in
    this module): `@[export]` instructs the Lean compiler to emit a
    C-callable wrapper named `syscall_dispatch_inner` that resolves
    the Rust-side `extern "C" { fn syscall_dispatch_inner(...) }`
    declaration in `rust/sele4n-hal/src/svc_dispatch.rs`.

    Encoding of the return value (matching
    `rust/sele4n-hal/src/svc_dispatch.rs::dispatch_svc`):
    - bit 63 = 1  → low 32 bits = `KernelError` discriminant
    - bit 63 = 0  → low 64 bits = success return value

    Current implementation: returns the `NotImplemented = 17` error
    flag because the full kernel-side syscall table wiring lives
    behind another v1.0.0 follow-up (the syscall table needs the
    SystemState to be threaded; the Rust-→-Lean glue is the channel
    this AN9-F sub-task delivers).  Substantive routing into
    `syscallEntryChecked` is the closure work documented in
    `docs/HARDWARE_TESTING.md` §4.4 as the SVC end-to-end test. -/
@[export syscall_dispatch_inner]
def syscallDispatchInner
    (_syscallId : UInt32) (_msgInfo : UInt64)
    (_x0 _x1 _x2 _x3 _x4 _x5 : UInt64)
    (_ipcBufferAddr : UInt64) : UInt64 :=
  -- Bit 63 set + low 32 bits = NotImplemented (17).  See the docstring
  -- above for the encoding contract.
  ((1 : UInt64) <<< 63) ||| 17

-- ============================================================================
-- AN9-A (DEF-A-M04): TLB+Cache composition witnesses
-- ============================================================================

/-- AN9-A.1: TLB+Cache composition witness — clean a page-table page
    range followed by `dsb ish` so the writeback completes before any
    subsequent operation observes the page-table state.

    Rust: `cache::clean_pagetable_range` in `sele4n-hal/src/cache.rs`. -/
@[extern "cache_clean_pagetable_range"]
opaque ffiCacheCleanPagetableRange : UInt64 → UInt64 → BaseIO Unit

/-- AN9-A.1: I-cache invalidation witness — drop every I-cache line so
    subsequent instruction fetches re-read from coherent memory.

    Rust: `cache::ic_iallu` in `sele4n-hal/src/cache.rs`. -/
@[extern "cache_ic_iallu"]
opaque ffiIcIallu : BaseIO Unit

end SeLe4n.Platform.FFI
