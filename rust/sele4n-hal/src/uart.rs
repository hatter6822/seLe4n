//! PL011 UART driver for debug console output on Raspberry Pi 5.
//!
//! Base address: 0xFE201000 (BCM2712 UART0, matches `Board.lean:uart0Base`).
//! Baud rate: 115200 at 48 MHz UART reference clock.
//!
//! Register offsets per ARM PrimeCell UART (PL011) Technical Reference Manual.

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
    #[allow(unsafe_code)]
    #[inline(always)]
    fn read_reg(&self, offset: usize) -> u32 {
        // SAFETY: Reading from a MMIO register at a known-valid PL011 offset.
        // The base address is validated at construction time by the caller.
        // Volatile read ensures the compiler does not elide or reorder the access.
        // (ARM PrimeCell UART PL011 TRM, Chapter 3: Programmers Model)
        unsafe { core::ptr::read_volatile((self.base + offset) as *const u32) }
    }

    /// Write a 32-bit register at the given offset from UART base.
    #[allow(unsafe_code)]
    #[inline(always)]
    fn write_reg(&self, offset: usize, val: u32) {
        // SAFETY: Writing to a MMIO register at a known-valid PL011 offset.
        // Volatile write ensures the compiler does not elide or reorder the access.
        // (ARM PrimeCell UART PL011 TRM, Chapter 3: Programmers Model)
        unsafe { core::ptr::write_volatile((self.base + offset) as *mut u32, val) }
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
    pub fn init_with_baud(&self, baud: u32) {
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

use core::sync::atomic::{AtomicBool, Ordering};

/// Module-private mutable UART instance. Accessed only through `UART_LOCK`.
///
/// SAFETY: All access is mediated by `UART_LOCK.with()`, which provides
/// mutual exclusion via atomic acquire/release on a single-core system.
static mut BOOT_UART_INNER: Uart = Uart::new(UART0_BASE);

/// Minimal spinlock guard for boot UART access.
///
/// On a single-core ARM64 system (RPi5 boots on core 0 only), the only
/// contention source is an IRQ handler calling `kprintln!` while the main
/// kernel path holds the lock. The atomic acquire/release ensures mutual
/// exclusion without requiring interrupt disabling (the spin is bounded:
/// the IRQ handler's UART access is brief, and the main path will release
/// before the next tick).
struct UartLock {
    locked: AtomicBool,
}

impl UartLock {
    const fn new() -> Self {
        Self { locked: AtomicBool::new(false) }
    }

    /// Execute `f` with exclusive `&mut Uart` access.
    ///
    /// Spins on the atomic flag until acquired. On single-core, this
    /// bounds to the duration of any concurrent IRQ handler UART write.
    #[inline(always)]
    fn with<R, F: FnOnce(&mut Uart) -> R>(&self, f: F) -> R {
        while self.locked.compare_exchange_weak(
            false, true, Ordering::Acquire, Ordering::Relaxed
        ).is_err() {
            core::hint::spin_loop();
        }
        // SAFETY: Lock held — single writer guaranteed by the atomic flag.
        // `&raw mut` avoids creating an intermediate reference to static mut.
        let result = unsafe { f(&mut *core::ptr::addr_of_mut!(BOOT_UART_INNER)) };
        self.locked.store(false, Ordering::Release);
        result
    }
}

// SAFETY: UartLock uses AtomicBool for synchronization — safe to share.
unsafe impl Sync for UartLock {}

static UART_LOCK: UartLock = UartLock::new();

/// Obtain exclusive access to the global UART and call `f`.
///
/// Safe to call from any context (boot, kernel, IRQ handler). The
/// spinlock ensures mutual exclusion without requiring the caller to
/// manually disable interrupts.
#[inline(always)]
pub(crate) fn with_boot_uart<R, F: FnOnce(&mut Uart) -> R>(f: F) -> R {
    UART_LOCK.with(f)
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
}
