//! ARM Generic Timer driver for Raspberry Pi 5.
//!
//! Counter frequency: 54 MHz (from Board.lean `timerFrequencyHz`).
//! Default tick rate: 1000 Hz (1 ms ticks).
//!
//! Stub implementation for AG4. Full driver with comparator programming
//! and timer interrupt enable implemented in AG5 (AG5-D).

/// Counter frequency on RPi5: 54 MHz crystal.
/// Matches Lean `rpi5TimerConfig.counterFrequencyHz`.
pub const COUNTER_FREQ_HZ: u32 = 54_000_000;

/// Default tick rate in Hz (1 ms ticks).
pub const DEFAULT_TICK_HZ: u32 = 1000;

/// Counter increments per tick at default rate: 54000000 / 1000 = 54000.
/// Matches Lean `rpi5TimerConfig` `countsPerTick` computation.
pub const COUNTS_PER_TICK: u32 = COUNTER_FREQ_HZ / DEFAULT_TICK_HZ;
