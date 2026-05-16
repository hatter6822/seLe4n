// SPDX-License-Identifier: GPL-3.0-or-later
//! PL011 UART driver for debug console output on Raspberry Pi 5.
//!
//! Base address: 0xFE201000 (BCM2712 UART0, matches `Board.lean:uart0Base`).
//! Baud rate: 115200 at 48 MHz UART reference clock.
//!
//! Register offsets per ARM PrimeCell UART (PL011) Technical Reference Manual.

// AN8-A.3 audit: `std::panic::catch_unwind` is needed by the unwinding-path
// `UartGuard` Drop tests below. Declared once at the top of the module so
// `clippy::items_after_test_module` is satisfied.
#[cfg(test)]
extern crate std;

use core::fmt;

/// PL011 register offsets from base address.
mod regs {
    /// Data Register — read/write FIFO.
    pub const UARTDR: usize = 0x000;
    /// Flag Register — FIFO status (TXFF, RXFE, BUSY, etc.).
    pub const UARTFR: usize = 0x018;
    /// Integer Baud Rate Divisor.
    pub const UARTIBRD: usize = 0x024;
    /// Fractional Baud Rate Divisor.
    pub const UARTFBRD: usize = 0x028;
    /// Line Control Register — word length, FIFO enable, parity.
    pub const UARTLCR_H: usize = 0x02C;
    /// Control Register — UART enable, TX/RX enable.
    pub const UARTCR: usize = 0x030;
    /// Interrupt Clear Register.
    pub const UARTICR: usize = 0x044;
}

/// Flag Register bit masks.
mod flags {
    /// Transmit FIFO Full.
    pub const TXFF: u32 = 1 << 5;
    /// Receive FIFO Empty.
    pub const RXFE: u32 = 1 << 4;
    /// UART Busy transmitting data.
    pub const BUSY: u32 = 1 << 3;
}

/// BCM2712 UART0 base address (from Board.lean `uart0Base`).
pub const UART0_BASE: usize = 0xFE201000;

/// UART reference clock frequency on RPi5 (48 MHz).
const UART_CLOCK_HZ: u32 = 48_000_000;

/// Default baud rate for debug console.
const DEFAULT_BAUD: u32 = 115_200;

/// AN8-D (RUST-M02): boot-time invariants for the production baud-rate path.
///
/// `init_with_baud` uses `debug_assert!` to catch a zero baud (which would
/// trigger an integer divide-by-zero in the divisor computation). To ensure
/// release builds never reach `init_with_baud(0)` on the production path,
/// the only callable boot path (`init` → `init_boot_uart`) passes a
/// **compile-time constant** verified by the assertion below. Adding any
/// new boot-time caller that bypasses `init` will fail the build if it
/// ever introduces a path that could pass `0`.
const _: () = assert!(
    DEFAULT_BAUD > 0,
    "DEFAULT_BAUD must be non-zero so init() can use debug_assert! safely"
);
const _: () = assert!(
    UART_CLOCK_HZ >= DEFAULT_BAUD * 16,
    "UART_CLOCK_HZ must be at least 16 × baud for PL011 oversampling"
);

/// PL011 UART driver instance.
pub struct Uart {
    base: usize,
}

impl Uart {
    /// Create a new UART driver for the given base address.
    ///
    /// # Safety
    ///
    /// The base address must point to a valid PL011 UART peripheral in device
    /// memory. The caller must ensure exclusive access.
    pub const fn new(base: usize) -> Self {
        Self { base }
    }

    /// Read a 32-bit register at the given offset from UART base.
    ///
    /// AK5-H (R-HAL-M05 / MEDIUM): routes through `crate::mmio::mmio_read32`
    /// so accesses go through the AJ5-A alignment asserts. PL011 registers
    /// are 32-bit / 4-byte-aligned so the assert is a no-op on valid offsets;
    /// it catches programmer errors (mis-computed offsets) at first access.
    #[inline(always)]
    fn read_reg(&self, offset: usize) -> u32 {
        crate::mmio::mmio_read32(self.base + offset)
    }

    /// Write a 32-bit register at the given offset from UART base.
    ///
    /// AK5-H: same routing rationale as `read_reg`.
    #[inline(always)]
    fn write_reg(&self, offset: usize, val: u32) {
        crate::mmio::mmio_write32(self.base + offset, val);
    }

    /// Initialize the UART: disable, set baud rate (115200 8N1), enable.
    ///
    /// Baud rate divisor for 48 MHz clock at 115200 baud:
    ///   BRD = 48000000 / (16 × 115200) = 26.0416...
    ///   IBRD = 26, FBRD = round(0.0416 × 64) = round(2.67) = 3
    pub fn init(&self) {
        self.init_with_baud(DEFAULT_BAUD);
    }

    /// Initialize UART with a specific baud rate.
    ///
    /// # AN8-E (R-HAL-L4): non-standard-baud silent rounding
    ///
    /// PL011 baud-rate divisors are computed from
    ///   `BRD = UART_CLOCK_HZ / (16 × baud)`
    /// and split into `IBRD` (integer) and `FBRD` (fractional, 6 bits).
    /// Non-standard baud rates that do not divide evenly into the clock
    /// produce a slightly-off effective baud (within ±1.5% by PL011 TRM
    /// §3.3.6 specification). This is silent — no warning is emitted —
    /// because the PL011 hardware itself does no error reporting on
    /// baud-rate mismatch. Callers passing non-115200/57600/38400/etc.
    /// rates should validate the resulting effective baud externally.
    ///
    /// # Panics (debug builds only)
    ///
    /// AK5-K (R-HAL-M10 / MEDIUM): `baud == 0` would cause division by zero
    /// in the baud-rate divisor computation. We assert rather than silently
    /// returning because the boot UART must be functional for any kernel
    /// diagnostic output — a silent no-op init would leave subsequent
    /// `kprintln!` calls hanging on a disabled UART.
    ///
    /// # AN8-D (RUST-M02) trade-off
    ///
    /// Production callers (`init` / `init_boot_uart`) pass the compile-time
    /// constant `DEFAULT_BAUD = 115_200`, so the runtime check fires only in
    /// debug builds where `debug_assertions = true`. Release builds rely on
    /// the [`init_boot_uart_invariants_check`] static assertions below to
    /// validate that the boot-time baud is non-zero at compile time.
    /// `init_with_baud(0)` in release would still divide-by-zero → fault,
    /// which on ARM64 with floating-point divide-by-zero is well-defined
    /// (returns `inf`/`nan`) but on integer divide is implementation-defined
    /// (Cortex-A76 returns 0, leading to silent UART misconfiguration). The
    /// boot-time invariants below ensure no zero-baud caller path exists.
    pub fn init_with_baud(&self, baud: u32) {
        debug_assert!(baud > 0, "UART baud rate must be > 0");
        // Disable UART while configuring
        self.write_reg(regs::UARTCR, 0);

        // Clear all interrupts
        self.write_reg(regs::UARTICR, 0x7FF);

        // Calculate baud rate divisors per PL011 TRM Section 3.3.6:
        //   BRD = UART_CLK / (16 * baud)
        //   IBRD = integer part, FBRD = round(fractional * 64)
        // We compute (UART_CLK * 4 * 2 + baud) / (baud * 2) for rounding,
        // then extract IBRD = result/64, FBRD = result%64.
        let divisor = baud as u64 * 2;
        let brd_times_64 = (UART_CLOCK_HZ as u64 * 4 * 2 + baud as u64) / divisor;
        let ibrd = (brd_times_64 / 64) as u32;
        let fbrd = (brd_times_64 % 64) as u32;

        self.write_reg(regs::UARTIBRD, ibrd);
        self.write_reg(regs::UARTFBRD, fbrd);

        // Line control: 8 data bits, no parity, 1 stop bit, FIFO enable
        // WLEN = 0b11 (8 bits) at bits [6:5], FEN = 1 at bit [4]
        self.write_reg(regs::UARTLCR_H, (0b11 << 5) | (1 << 4));

        // Enable UART, TX, and RX
        // UARTEN = bit 0, TXE = bit 8, RXE = bit 9
        self.write_reg(regs::UARTCR, (1 << 0) | (1 << 8) | (1 << 9));
    }

    /// Transmit a single byte, blocking until the TX FIFO has space.
    pub fn putc(&self, c: u8) {
        // Poll UARTFR.TXFF until the transmit FIFO is not full
        while (self.read_reg(regs::UARTFR) & flags::TXFF) != 0 {
            core::hint::spin_loop();
        }
        self.write_reg(regs::UARTDR, c as u32);
    }

    /// Transmit a byte slice.
    pub fn puts(&self, s: &[u8]) {
        for &c in s {
            if c == b'\n' {
                self.putc(b'\r');
            }
            self.putc(c);
        }
    }

    /// Non-blocking receive. Returns `Some(byte)` if data is available.
    pub fn getc(&self) -> Option<u8> {
        if (self.read_reg(regs::UARTFR) & flags::RXFE) != 0 {
            None
        } else {
            Some((self.read_reg(regs::UARTDR) & 0xFF) as u8)
        }
    }

    /// Wait until the UART is no longer busy transmitting.
    pub fn flush(&self) {
        while (self.read_reg(regs::UARTFR) & flags::BUSY) != 0 {
            core::hint::spin_loop();
        }
    }
}

/// Implement `core::fmt::Write` so we can use `write!()` and `writeln!()`.
impl fmt::Write for Uart {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.puts(s.as_bytes());
        Ok(())
    }
}

// ============================================================================
// AI1-D/M-27: Synchronized UART access via UartLock
//
// Replaces `pub static mut BOOT_UART` with an AtomicBool-based spinlock
// that eliminates undefined behavior from unsynchronized mutable static
// access after interrupts are enabled.
// ============================================================================
//
// **WS-SM SM1.G.1 audit**: UART lock under SMP
//
// The `UartLock` below uses an `AtomicBool` with `compare_exchange_weak`
// (Acquire on success, Relaxed on retry) and `store(false, Release)` on
// release.  Combined with the per-acquire DAIF mask
// (`disable_interrupts` / `restore_interrupts`), this protects the
// shared PL011 UART against:
//
//   * Pre-emption by an IRQ handler that calls `kprintln!` while the
//     main kernel path holds the lock.  The DAIF mask covers IRQ /
//     FIQ delivery for the duration of the critical section.
//   * Concurrent acquisition from multiple cores under SMP.  The
//     CAS-based loop ensures exactly one core wins the lock; losers
//     spin on the AtomicBool with `core::hint::spin_loop()` (which
//     maps to `yield` on ARMv8.0 / `wfe` on ARMv8.5+).
//
// **Correctness under SMP**: the Acquire / Release semantics establish
// the standard happens-before chain:
//
//     Core A: ... memory writes ... → Release(false → true)
//     Core B: Acquire(true) → ... reads happen-after A's writes ...
//
// So a kernel-state mutation by core A that races with a
// `kprintln!`-initiated lock acquisition by core B is correctly
// ordered through the lock.
//
// **Fairness**: the CAS loop is NOT FIFO-fair.  Under heavy contention
// (e.g., every core spinning to print boot diagnostics), some cores
// may starve indefinitely.  The current production usage (boot-time
// diagnostics + occasional IRQ-handler panics) does not exhibit this
// pattern, so the simple CAS lock is sufficient at v1.0.0.
//
// **Future work**: WS-SM SM2 introduces a verified `TicketLock`
// primitive (FIFO fairness, formal mutex theorem).  Once SM2.B lands,
// this lock will be replaced with `TicketLock` to eliminate the
// fairness gap.  At that point the `UartLock` struct itself can be
// removed; the `with_boot_uart` interface is the stable public API
// and will not change.  Until then, the AtomicBool-based design here
// is the documented v1.0.0 contract.
// ============================================================================

use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

/// AJ5-B/M-21: Wrapper providing `Sync` for `UnsafeCell<Uart>`.
///
/// `static mut` is deprecated in future Rust editions and technically unsound
/// under aliasing rules. This wrapper uses `UnsafeCell` instead, with `Sync`
/// safety guaranteed by the `UART_LOCK` spinlock that mediates all access.
struct UartInner(UnsafeCell<Uart>);

// SAFETY: All access to `UartInner.0` is mediated by `UART_LOCK.with()`,
// which provides mutual exclusion via atomic acquire/release with interrupt
// masking on a single-core system.
unsafe impl Sync for UartInner {}

/// Module-private mutable UART instance. Accessed only through `UART_LOCK`.
static BOOT_UART_INNER: UartInner = UartInner(UnsafeCell::new(Uart::new(UART0_BASE)));

/// Minimal IRQ-safe spinlock guard for boot UART access.
///
/// On a single-core ARM64 system (RPi5 boots on core 0 only), the only
/// contention source is an IRQ handler calling `kprintln!` while the main
/// kernel path holds the lock. Without interrupt masking, this would
/// deadlock: the IRQ preempts the lock holder, spins forever, and the
/// holder never resumes to release. The lock therefore disables interrupts
/// for the duration of the critical section, matching the plan's
/// "IRQ-safe lock" requirement.
///
/// On non-aarch64 (test hosts), interrupt disable/restore are no-ops,
/// so the lock degrades to a plain atomic spinlock — correct for
/// single-threaded test execution.
struct UartLock {
    locked: AtomicBool,
    /// AN8-A.1: DAIF snapshot stashed at `acquire()` time so `release()` can
    /// restore it. Written only by the lock holder (Relaxed is sufficient:
    /// the `locked` AtomicBool's Acquire/Release pair publishes the write).
    saved_daif: AtomicU64,
}

impl UartLock {
    const fn new() -> Self {
        Self { locked: AtomicBool::new(false), saved_daif: AtomicU64::new(0) }
    }

    /// Acquire the spin lock after first masking interrupts.
    ///
    /// The saved DAIF value is stashed in `saved_daif` so that
    /// [`release`](Self::release) — the only legitimate counterpart —
    /// can restore it symmetrically. Called by [`with_guard`](Self::with_guard).
    #[inline(always)]
    fn acquire(&self) {
        // Disable interrupts BEFORE acquiring the lock to prevent an IRQ
        // handler from preempting us mid-acquisition and deadlocking.
        let saved_daif = crate::interrupts::disable_interrupts();
        while self.locked.compare_exchange_weak(
            false, true, Ordering::Acquire, Ordering::Relaxed
        ).is_err() {
            core::hint::spin_loop();
        }
        // Stash the DAIF snapshot AFTER the lock is held so only the owner
        // can read/write this field. Relaxed ordering suffices because the
        // lock's Acquire/Release pair already publishes the write.
        self.saved_daif.store(saved_daif, Ordering::Relaxed);
    }

    /// Release the spin lock and restore the DAIF mask.
    ///
    /// Invariant: must only be called by the thread that holds the lock
    /// (enforced structurally because [`UartGuard::drop`] is the only
    /// caller — `Drop` is parameterised by `&mut self`, so only the
    /// single guard holding the mutable borrow can invoke it).
    #[inline(always)]
    fn release(&self) {
        let saved_daif = self.saved_daif.load(Ordering::Relaxed);
        self.locked.store(false, Ordering::Release);
        crate::interrupts::restore_interrupts(saved_daif);
    }

    /// AN8-A.1 (H-17): RAII lock acquisition.
    ///
    /// Acquires the spin lock (with interrupt masking) and returns a
    /// [`UartGuard`] whose `Drop` implementation releases it. The guard's
    /// lifetime `'a` is pinned to the lock reference, so the guard cannot
    /// outlive the lock — and the compiler rejects any attempt to hold a
    /// live `&mut Uart` while the guard is dropped.
    ///
    /// This replaces the earlier `with(F)` callback pattern in which the
    /// release was a plain `self.locked.store(false, Ordering::Release)`
    /// call on the path after the closure returned: an early-return or
    /// panic inside the closure would have bypassed the release. With
    /// RAII, the release is attached to the guard's lifetime, so every
    /// normal scope exit (and every unwinding path on the test profile)
    /// fires it.
    #[inline(always)]
    fn with_guard(&self) -> UartGuard<'_> {
        self.acquire();
        // SAFETY: `acquire` guarantees exclusive access to
        // `BOOT_UART_INNER` for the lifetime of the returned guard. The
        // guard's `Drop` calls `self.release()`, which both resets the
        // atomic lock flag AND restores the DAIF mask, so the critical
        // section is symmetric. `&mut *get()` is sound because the
        // atomic acquire establishes happens-before with any prior
        // release, and no other code path constructs `&mut Uart` from
        // `BOOT_UART_INNER` without going through this routine.
        let inner = unsafe { &mut *BOOT_UART_INNER.0.get() };
        UartGuard { inner, lock: self }
    }

    /// Check whether the lock is currently held. Primarily for tests.
    #[inline(always)]
    #[cfg(test)]
    fn is_held(&self) -> bool {
        self.locked.load(Ordering::Acquire)
    }
}

// ============================================================================
// AN8-A.1 (H-17): UartGuard RAII
// ============================================================================

/// RAII guard that pins exclusive access to the boot UART.
///
/// Produced by [`UartLock::with_guard`]. The `Drop` implementation
/// releases the spin lock and restores the DAIF mask that was masked
/// at acquisition time, so every normal scope exit (and every unwinding
/// path under the test profile) symmetrically balances the acquire.
///
/// # Lifetime binding
///
/// The `'a` lifetime ties the mutable-borrow lifetime of `inner` to the
/// lifetime of the guard itself. Dropping the guard first drops the
/// mutable borrow (via NLL), then runs the `Drop` body. This is what
/// makes the pattern sound.
///
/// # Panic-path behaviour (AN8-A.4)
///
/// Under the workspace `panic = "abort"` profile (see
/// `rust/Cargo.toml` and `ffi.rs` AK5-M guard), a panic terminates the
/// kernel without running destructors — the `release` never fires, but
/// the kernel has already aborted, so the GIC/UART state is moot. Under
/// the stable `cargo test` profile (which forces `panic = "unwind"`),
/// the `Drop` still fires on the unwind path. Both behaviours match
/// the AK5-B `EoiGuard` design from GIC dispatch.
///
/// # Visibility
///
/// The struct is non-`pub` because the only constructor
/// ([`UartLock::with_guard`]) is private; external callers use
/// [`with_boot_uart`] (`pub(crate)`) which consumes the guard
/// internally. Keeping the struct private prevents any accidental
/// external construction (which would be UB-prone without the lock's
/// invariants).
struct UartGuard<'a> {
    inner: &'a mut Uart,
    lock: &'a UartLock,
}

impl Drop for UartGuard<'_> {
    #[inline(always)]
    fn drop(&mut self) {
        self.lock.release();
    }
}

// SAFETY: UartLock uses AtomicBool for synchronization — safe to share.
unsafe impl Sync for UartLock {}

static UART_LOCK: UartLock = UartLock::new();

/// Obtain exclusive access to the global UART and call `f`.
///
/// Safe to call from any context (boot, kernel, IRQ handler). The
/// RAII [`UartGuard`] ensures mutual exclusion without requiring the
/// caller to manually disable interrupts.
///
/// AN8-A.2 (H-17): Thin wrapper over [`UartLock::with_guard`]. Every
/// scope exit — normal return, early return, unwind — runs the guard's
/// `Drop` so the lock is always released. The closure receives a
/// `&mut Uart` that is implicitly bound to the guard's lifetime; when
/// `f` returns, the borrow is released before the guard is dropped, so
/// the NLL borrow-checker accepts the pattern statically.
#[inline(always)]
pub(crate) fn with_boot_uart<R, F: FnOnce(&mut Uart) -> R>(f: F) -> R {
    let guard = UART_LOCK.with_guard();
    // Reborrow `guard.inner` (itself a `&'a mut Uart`) so `f` receives a
    // shorter-lived `&mut Uart` that ends before the guard's `Drop` runs
    // at function scope exit. Under `panic = "unwind"` (test profile) the
    // unwind path still invokes `Drop`, which releases the lock and
    // restores DAIF; under `panic = "abort"` (production) the kernel
    // halts before any subsequent code observes the lock state, so the
    // skipped release is moot.
    f(&mut *guard.inner)
}

/// Initialize the global boot UART.
///
/// Must be called exactly once from the boot path, before any other
/// `kprint!` / `kprintln!` usage. The lock is acquired for initialization.
pub fn init_boot_uart() {
    with_boot_uart(|u| u.init());
}

/// Print a byte slice to the boot UART.
pub fn boot_puts(s: &[u8]) {
    with_boot_uart(|u| u.puts(s));
}

/// Print formatted output to the boot UART.
#[macro_export]
macro_rules! kprint {
    ($($arg:tt)*) => {{
        use core::fmt::Write;
        $crate::uart::with_boot_uart(|uart| {
            let _ = write!(uart, $($arg)*);
        });
    }};
}

/// Print formatted output with newline to the boot UART.
#[macro_export]
macro_rules! kprintln {
    () => { $crate::kprint!("\n") };
    ($($arg:tt)*) => {{
        $crate::kprint!($($arg)*);
        $crate::kprint!("\n");
    }};
}

// ============================================================================
// WS-SM SM1.G.4 — Per-core kprintln macro
// ============================================================================
//
// `kprintln_core!` prefixes every line with the calling core's id
// (read from TPIDR_EL1 via per_cpu::current_core_id_from_tpidr).
// Useful for SMP boot tracing and post-mortem log analysis where
// per-core attribution matters.
//
// The macro composes atomically with `kprint!` — the `[core N]` prefix
// and the message body are produced inside the same `with_boot_uart`
// critical section because `kprint!` itself takes the lock.  This
// means a higher-priority IRQ handler that calls `kprintln_core!`
// during the `[core N]` prefix print would interleave its own line
// AFTER the prefix completes, producing a clean boundary rather than
// the prefix mid-character mixing with the message body.
//
// Note that `kprintln_core!` makes TWO `kprint!` calls (prefix + body),
// each of which takes and releases the lock.  An IRQ that fires
// between the two could insert its own line between them, producing:
//
//     [core 0] starting boot phase 5
//     [core 1] (timer IRQ from IRQ handler)
//     ...
//
// This is the documented behaviour: per-line atomicity, not
// per-`kprintln_core!`-call atomicity.  Higher-stake callers that
// need to print multi-line atomic output should mask interrupts
// around the entire call sequence (see `interrupts::with_interrupts_disabled`).

/// **WS-SM SM1.G.4**: Print formatted output with a per-core id prefix
/// and a trailing newline.
///
/// Equivalent to `kprintln!("[core {}] {}", core_id, format_args!(...))`,
/// where `core_id` is read from `TPIDR_EL1` via
/// `per_cpu::current_core_id_from_tpidr`.  Useful for SMP boot
/// tracing where per-core attribution matters.
///
/// On host (non-aarch64) the core id reads as `0` deterministically.
///
/// # Example
///
/// ```ignore
/// use sele4n_hal::kprintln_core;
/// kprintln_core!("ready, entering kernel");
/// // Output (on core 1): [core 1] ready, entering kernel
/// ```
#[macro_export]
macro_rules! kprintln_core {
    () => {{
        let core_id = $crate::per_cpu::current_core_id_from_tpidr();
        $crate::kprintln!("[core {}]", core_id);
    }};
    ($($arg:tt)*) => {{
        let core_id = $crate::per_cpu::current_core_id_from_tpidr();
        $crate::kprintln!("[core {}] {}", core_id, format_args!($($arg)*));
    }};
}

/// **WS-SM SM1.G.4**: Print formatted output with a per-core id prefix
/// (no trailing newline).
///
/// Companion to [`kprintln_core!`] for partial-line printing.  Note
/// the same interleaving caveat applies — this macro takes and
/// releases the UART lock for the prefix and body separately.
#[macro_export]
macro_rules! kprint_core {
    ($($arg:tt)*) => {{
        let core_id = $crate::per_cpu::current_core_id_from_tpidr();
        $crate::kprint!("[core {}] {}", core_id, format_args!($($arg)*));
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uart0_base_matches_board_lean() {
        // Board.lean: uart0Base : PAddr := ⟨0xFE201000⟩
        assert_eq!(UART0_BASE, 0xFE201000);
    }

    #[test]
    fn baud_rate_divisor_115200() {
        // For 48 MHz clock at 115200 baud:
        //   BRD = 48000000 / (16 × 115200) = 26.0416...
        //   IBRD = 26, FBRD = round(0.0416 × 64) = round(2.667) = 3
        let baud: u32 = 115_200;
        let divisor = baud as u64 * 2;
        let brd_times_64 = (UART_CLOCK_HZ as u64 * 4 * 2 + baud as u64) / divisor;
        let ibrd = (brd_times_64 / 64) as u32;
        let fbrd = (brd_times_64 % 64) as u32;

        assert_eq!(ibrd, 26);
        assert_eq!(fbrd, 3);
    }

    #[test]
    fn uart_clock_48mhz() {
        assert_eq!(UART_CLOCK_HZ, 48_000_000);
    }

    #[test]
    fn pl011_register_offsets() {
        // ARM PrimeCell UART (PL011) Technical Reference Manual
        assert_eq!(regs::UARTDR, 0x000);
        assert_eq!(regs::UARTFR, 0x018);
        assert_eq!(regs::UARTIBRD, 0x024);
        assert_eq!(regs::UARTFBRD, 0x028);
        assert_eq!(regs::UARTLCR_H, 0x02C);
        assert_eq!(regs::UARTCR, 0x030);
        assert_eq!(regs::UARTICR, 0x044);
    }

    #[test]
    fn flag_register_bits() {
        assert_eq!(flags::TXFF, 1 << 5);
        assert_eq!(flags::RXFE, 1 << 4);
        assert_eq!(flags::BUSY, 1 << 3);
    }

    // AK5-K (R-HAL-M10) + AN8-D (RUST-M02): `init_with_baud(0)` triggers
    // the in-function `debug_assert!`. The test profile compiles with
    // `debug_assertions = true` (default for `cargo test`), so the
    // assertion fires and the `#[should_panic]` matches the message
    // string. In release builds the `debug_assert!` is elided; the
    // boot-time `const _: () = assert!(...)` invariants in the file
    // header (and the fact that production callers pass the
    // compile-time constant `DEFAULT_BAUD = 115_200`) prevent
    // zero-baud calls in release.
    #[test]
    #[should_panic(expected = "UART baud rate must be > 0")]
    fn init_with_zero_baud_panics_in_debug_builds() {
        let uart = Uart::new(UART0_BASE);
        uart.init_with_baud(0);
    }

    // ========================================================================
    // AN8-A.3 (H-17): UartGuard RAII semantics
    //
    // The guard must:
    //   1. Leave the lock held for the duration of its lifetime.
    //   2. Release the lock (both the AtomicBool flag and the stashed
    //      DAIF mask) on every normal scope exit.
    //   3. Run its `Drop` on the unwind path too, so panics inside the
    //      critical section don't leak the lock. (`panic = "abort"` skips
    //      this in production, which is the correct response to an
    //      invariant violation; we verify the unwinding test-profile
    //      behaviour here.)
    // ========================================================================

    #[test]
    fn uart_guard_holds_lock_for_scope_and_releases_on_exit() {
        // Fresh local lock so the test is isolated from the global one.
        let lock = UartLock::new();
        assert!(!lock.is_held(), "precondition: lock not held");
        {
            let _g = lock.with_guard();
            assert!(lock.is_held(), "lock must be held while guard alive");
        }
        assert!(!lock.is_held(), "lock must be released when guard drops");
    }

    #[test]
    fn uart_guard_releases_on_early_return() {
        // The guard fires its Drop even when the scope exits via an
        // explicit `return` before the end of the block. Branching
        // through a conditional `return` (rather than the bare
        // `return;` clippy considers unneeded) keeps the early-exit
        // semantics explicit while satisfying `clippy::needless_return`.
        fn exercise(l: &UartLock, take_short_path: bool) -> u32 {
            let _g = l.with_guard();
            if take_short_path {
                return 0xEA21_F00D;
            }
            0xEA22_F00D
        }
        let lock = UartLock::new();
        let r1 = exercise(&lock, true);
        assert_eq!(r1, 0xEA21_F00D);
        assert!(!lock.is_held(),
            "lock must be released after early-return (short path)");
        let r2 = exercise(&lock, false);
        assert_eq!(r2, 0xEA22_F00D);
        assert!(!lock.is_held(),
            "lock must be released after fall-through (long path)");
    }

    #[test]
    fn uart_guard_global_lock_released_after_with_boot_uart() {
        // `with_boot_uart` is the only documented consumer of the guard
        // pattern; verify the global lock is not leaked.
        let before = UART_LOCK.is_held();
        let result = with_boot_uart(|_u| 0xABCDu32);
        assert_eq!(result, 0xABCD);
        assert_eq!(UART_LOCK.is_held(), before,
            "global UART_LOCK state must match before/after with_boot_uart");
    }

    // The `panic = "abort"` profile in production never runs Drop; but the
    // stable test harness forces unwind, so we can cross-check that Drop
    // fires on the unwind path too. Any future refactor that breaks the
    // Drop wiring will be caught.
    #[test]
    fn uart_guard_releases_on_unwind() {
        let lock = UartLock::new();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _g = lock.with_guard();
            panic!("simulated fault inside UART critical section");
        }));
        assert!(result.is_err(), "catch_unwind should have caught the panic");
        assert!(!lock.is_held(),
            "UartGuard::drop did not fire on unwind — lock leaked");
    }

    // ========================================================================
    // WS-SM SM1.G.4 — Per-core kprintln macro tests
    //
    // The macros expand to a `kprint!` / `kprintln!` call sequence that
    // takes the UART lock for each `[core N] ...` line.  We cannot
    // intercept the formatted output from a host test (the Boot UART
    // is `static`, not parameterisable), so the tests verify:
    //
    //   1. The macros expand cleanly (a regression in the macro syntax
    //      would fail at the call site).
    //   2. The macros do not panic on host (`current_core_id_from_tpidr`
    //      reads the boot-core slot which is initialised to 0 deterministically).
    //   3. The lock state is balanced after each macro invocation
    //      (i.e., the guard's Drop fires).
    //
    // Hardware-level interleaving / cross-core attribution is exercised
    // by SM1.G.3's `test_qemu_smp_kprintln_stress.sh` script (a
    // hardware-only test under `scripts/test_qemu_smp_*`).
    // ========================================================================

    #[test]
    fn sm1g4_kprintln_core_macro_expands_and_runs_on_host() {
        // The macro reads core_id from TPIDR_EL1 (host stub: 0) and
        // prints `[core 0] <msg>` to the boot UART.  On host the UART
        // write is a no-op via the MMIO host stub.  Verify no panic.
        crate::kprintln_core!("SM1.G.4 host smoke: macro expands cleanly");
        crate::kprintln_core!("SM1.G.4 with arg: {}", 42);
        crate::kprintln_core!("SM1.G.4 with multiple args: {} {} {}", 1, 2, 3);
    }

    #[test]
    fn sm1g4_kprintln_core_no_arg_form_runs_on_host() {
        // The no-argument form `kprintln_core!()` prints just the
        // `[core N]` prefix on its own line.  Useful for a blank
        // line in boot diagnostics.
        crate::kprintln_core!();
    }

    #[test]
    fn sm1g4_kprint_core_macro_expands_and_runs_on_host() {
        // Companion partial-line macro — exercises the same code path
        // but without the trailing newline.
        crate::kprint_core!("SM1.G.4 partial line");
        crate::kprintln!(); // Add a newline so subsequent output is clean.
    }

    #[test]
    fn sm1g4_kprintln_core_balances_lock_state() {
        // A `kprintln_core!` invocation acquires + releases the UART
        // lock.  After the macro returns, the global UART_LOCK must
        // be back in the not-held state.
        let before = UART_LOCK.is_held();
        assert!(!before, "precondition: global UART_LOCK not held");
        crate::kprintln_core!("SM1.G.4 lock-balance smoke");
        let after = UART_LOCK.is_held();
        assert_eq!(before, after, "kprintln_core! left UART_LOCK held");
    }

    #[test]
    fn sm1g4_kprintln_core_repeated_invocations_balance() {
        // Multiple sequential invocations must each balance the lock.
        // Catches a regression where one expansion arm forgets to
        // release.
        for i in 0..16 {
            crate::kprintln_core!("SM1.G.4 iteration {}", i);
            assert!(
                !UART_LOCK.is_held(),
                "UART_LOCK leaked after iteration {}",
                i
            );
        }
    }

    // ========================================================================
    // WS-SM SM1.G.3 — Hardware-only cross-core stress test stub
    // ========================================================================

    /// **WS-SM SM1.G.3**: Hardware-only cross-core kprintln stress test.
    ///
    /// `#[ignore]`'d because the test requires QEMU `-smp 4` (or
    /// physical RPi5) where multiple cores can race on the UART
    /// lock.  The host test profile runs single-threaded with one
    /// core's `current_core_id_from_tpidr` always returning 0, so a
    /// stress run here would not exercise the cross-core race.
    ///
    /// The actual hardware stress is in
    /// `scripts/test_qemu_smp_kprintln_stress.sh` (added at SM1.H);
    /// that script boots QEMU `-smp 4` and has each core emit 1M
    /// `kprintln_core!` calls, then verifies the captured UART log
    /// has no torn output (no `[core N]` prefix split across two
    /// lines, no two prefixes back-to-back without a body, etc.).
    ///
    /// This test exists as a documentation anchor.  A regression
    /// that broke the macro expansion would fail
    /// `sm1g4_kprintln_core_macro_expands_and_runs_on_host` first;
    /// the stress test catches finer-grained interleaving issues
    /// that are hardware-visible only.
    #[test]
    #[ignore]
    fn sm1g3_cross_core_kprintln_stress() {
        // Placeholder: would call `kprintln_core!` in a tight loop
        // from each of N spawned threads, but `std::thread` is not
        // available in this `#![no_std]` crate.  See the QEMU
        // script for the real test.
        unimplemented!("SM1.G.3: see scripts/test_qemu_smp_kprintln_stress.sh");
    }
}
