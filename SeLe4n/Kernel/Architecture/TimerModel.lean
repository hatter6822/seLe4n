/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine

/-!
# AG3-E (FINDING-08): Hardware Timer Model Binding

Bridges the abstract model timer (`Nat` incremented by `timerTick`) to ARM64
hardware timer semantics. ARM64 uses:

- **CNTPCT_EL0**: Physical counter register (monotonically increasing)
- **CNTP_CVAL_EL0**: Comparator register (triggers interrupt when counter ≥ value)
- **CNTFRQ_EL0**: Counter frequency (54 MHz on Raspberry Pi 5)

## Mapping

One model `timerTick` corresponds to one timer interrupt event, which occurs
when the hardware counter reaches the comparator value. The `HardwareTimerConfig`
captures the hardware timer parameters needed to compute this relationship.

## Design

The timer model is **pure** — no hardware interaction. It defines the
mathematical relationship between hardware counter values and model ticks,
enabling proofs that the abstract timer semantics correctly represent the
hardware behavior.
-/

namespace SeLe4n.Kernel.Architecture

/-- AG3-E: Hardware timer configuration parameters.
    Captures the architectural constants needed to map between hardware
    counter values and model timer ticks. -/
structure HardwareTimerConfig where
  /-- Counter frequency in Hz (e.g., 54000000 for RPi5 at 54 MHz). -/
  counterFrequencyHz : Nat
  /-- Desired tick interval in nanoseconds (e.g., 1000000 for 1ms ticks). -/
  tickIntervalNs : Nat
  /-- Current comparator value (CNTP_CVAL_EL0). When the hardware counter
      reaches this value, a timer interrupt fires. -/
  comparatorValue : Nat
  deriving Repr, DecidableEq

namespace HardwareTimerConfig

/-- AG3-E: Counter increments per model tick.
    Computed as: frequency × interval / 10^9.
    For RPi5 at 54 MHz with 1ms ticks: 54000000 × 1000000 / 10^9 = 54000. -/
def countsPerTick (cfg : HardwareTimerConfig) : Nat :=
  cfg.counterFrequencyHz * cfg.tickIntervalNs / 1000000000

/-- AG3-E: Convert a hardware counter value to the model's abstract tick count.
    The model tick is the number of complete tick intervals that have elapsed
    since counter value 0.

    For a 54 MHz counter with 1ms ticks, counter value 162000 → tick 3. -/
def hardwareTimerToModelTick (cfg : HardwareTimerConfig) (counterValue : Nat) : Nat :=
  if cfg.countsPerTick = 0 then 0
  else counterValue / cfg.countsPerTick

/-- AG3-E: Reprogram the comparator for the next tick.
    Sets CNTP_CVAL_EL0 to the next interrupt point: current comparator
    value + counts per tick. This produces evenly-spaced timer interrupts. -/
def reprogramComparator (cfg : HardwareTimerConfig) : HardwareTimerConfig :=
  { cfg with comparatorValue := cfg.comparatorValue + cfg.countsPerTick }

/-- AG3-E: `hardwareTimerToModelTick` is monotonically non-decreasing.
    If counter value a ≤ counter value b, then tick(a) ≤ tick(b).
    This follows from the monotonicity of natural number division. -/
theorem hardwareTimerToModelTick_monotone (cfg : HardwareTimerConfig)
    (a b : Nat) (hab : a ≤ b) :
    cfg.hardwareTimerToModelTick a ≤ cfg.hardwareTimerToModelTick b := by
  simp only [hardwareTimerToModelTick]
  split
  · omega
  · exact Nat.div_le_div_right hab

/-- AG3-E: Reprogramming the comparator advances it by exactly one tick interval. -/
theorem reprogramComparator_advances (cfg : HardwareTimerConfig) :
    (cfg.reprogramComparator).comparatorValue = cfg.comparatorValue + cfg.countsPerTick := rfl

/-- AG3-E: Reprogramming preserves the counter frequency. -/
theorem reprogramComparator_preserves_frequency (cfg : HardwareTimerConfig) :
    (cfg.reprogramComparator).counterFrequencyHz = cfg.counterFrequencyHz := rfl

/-- AG3-E: Reprogramming preserves the tick interval. -/
theorem reprogramComparator_preserves_interval (cfg : HardwareTimerConfig) :
    (cfg.reprogramComparator).tickIntervalNs = cfg.tickIntervalNs := rfl

end HardwareTimerConfig

-- ============================================================================
-- RPi5 timer configuration (54 MHz ARM generic timer)
-- ============================================================================

/-- AG3-E: Raspberry Pi 5 timer configuration.
    BCM2712 ARM Cortex-A76 generic timer at 54 MHz.
    1ms tick interval (matching seL4 default timer quantum). -/
def rpi5TimerConfig : HardwareTimerConfig where
  counterFrequencyHz := 54000000
  tickIntervalNs := 1000000
  comparatorValue := 0

/-- AG3-E: RPi5 timer produces 54000 counter increments per tick. -/
theorem rpi5TimerConfig_countsPerTick :
    rpi5TimerConfig.countsPerTick = 54000 := by decide

end SeLe4n.Kernel.Architecture
