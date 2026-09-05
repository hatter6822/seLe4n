-- SPDX-License-Identifier: GPL-3.0-or-later
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

> **STATUS: staged for H3 hardware binding** (AN7-D.6 / PLT-M07).  This
> module is wired into `SeLe4n.Platform.Staged` so every CI run verifies
> it compiles.  See `docs/spec/SELE4N_SPEC.md` §8.15 for the activation
> roadmap.

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

/-- AG3-E / AK3-H: Hardware timer configuration parameters.
    Captures the architectural constants needed to map between hardware
    counter values and model timer ticks.

    AK3-H (A-M05 / MEDIUM): Enforces `countsPerTick > 0` via a separate
    well-formedness predicate (`countsPerTickPositive`) and boot guard.
    A zero-count configuration (e.g., if `counterFrequencyHz * tickIntervalNs
    < 10^9` due to underprovisioned DT) would cause `countsPerTick` to
    round down to 0, leading to division-by-zero on `hardwareTimerToModelTick`
    and a boot-time wedge. -/
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

/-- **PR #890 review round 4**: the number of model ticks an interval of
    `cycles` counter cycles can span — the **ceiling** of the division.

    A different question from `hardwareTimerToModelTick`, which converts an
    *absolute* counter value to the tick it falls in and floors.  An
    interval is not an absolute value: one that begins mid-tick crosses
    one boundary more than its length alone suggests, so a duration bound
    read through the absolute conversion under-counts by one (1024 cycles
    at 54000 per tick is 0 ticks by the floor and 1 boundary at counter
    53500).  `hardwareTimerToModelTick_sub_le_duration` is the relation
    between the two: the ticks elapsed between any start counter and that
    counter plus the interval are at most this figure. -/
def hardwareDurationToModelTicks (cfg : HardwareTimerConfig) (cycles : Nat) : Nat :=
  if cfg.countsPerTick = 0 then 0
  else (cycles + cfg.countsPerTick - 1) / cfg.countsPerTick

/-- A longer interval spans no fewer ticks. -/
theorem hardwareDurationToModelTicks_monotone (cfg : HardwareTimerConfig)
    (a b : Nat) (hab : a ≤ b) :
    cfg.hardwareDurationToModelTicks a ≤ cfg.hardwareDurationToModelTicks b := by
  simp only [hardwareDurationToModelTicks]
  split
  · omega
  · exact Nat.div_le_div_right (by omega)

/-- **PR #890 review round 4**: the ticks elapsed across an interval, from
    **any** start counter, are bounded by the interval's duration in ticks.

    With `start = q * p + r` (`r < p`) the absolute tick after the
    interval is `q + (r + d) / p`, so the difference is `(r + d) / p`,
    which is at most `(d + p - 1) / p` because `r ≤ p - 1`.  The floor
    conversion alone gives `d / p`, which the phase `r` can exceed by one
    — the bound a duration budget needs is this one. -/
theorem hardwareTimerToModelTick_sub_le_duration (cfg : HardwareTimerConfig)
    (start d : Nat) :
    cfg.hardwareTimerToModelTick (start + d) - cfg.hardwareTimerToModelTick start
      ≤ cfg.hardwareDurationToModelTicks d := by
  by_cases h : cfg.countsPerTick = 0
  · simp [hardwareTimerToModelTick, hardwareDurationToModelTicks, h]
  · simp only [hardwareTimerToModelTick, hardwareDurationToModelTicks, h, if_false]
    have hp : 0 < cfg.countsPerTick := Nat.pos_of_ne_zero h
    have hSplit : start
        = cfg.countsPerTick * (start / cfg.countsPerTick) + start % cfg.countsPerTick :=
      (Nat.div_add_mod start cfg.countsPerTick).symm
    have hR : start % cfg.countsPerTick < cfg.countsPerTick := Nat.mod_lt _ hp
    have hEq : (start + d) / cfg.countsPerTick
        = start / cfg.countsPerTick
            + (start % cfg.countsPerTick + d) / cfg.countsPerTick := by
      have hMul :=
        Nat.mul_add_div hp (start / cfg.countsPerTick) (start % cfg.countsPerTick + d)
      rw [← Nat.add_assoc, ← hSplit] at hMul
      exact hMul
    rw [hEq, Nat.add_sub_cancel_left]
    exact Nat.div_le_div_right (by omega)

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

-- ============================================================================
-- AK3-H (A-M05 / MEDIUM): Timer `countsPerTick` positivity
-- ============================================================================

namespace HardwareTimerConfig

/-- AK3-H (A-M05 / MEDIUM): `countsPerTick` well-formedness.
    A timer configuration is "positive" iff its `countsPerTick` is strictly
    positive; this prevents division-by-zero in `hardwareTimerToModelTick`
    and other tick arithmetic. Violated only when
    `counterFrequencyHz * tickIntervalNs < 10^9` (e.g., DT says 1 kHz with
    1 ns tick → 1*1/10^9 = 0). -/
def countsPerTickPositive (cfg : HardwareTimerConfig) : Prop :=
  cfg.countsPerTick > 0

/-- AK3-H: Decidable runtime check — boot code uses this to reject malformed
    configurations before committing them to `MachineState`. -/
@[inline] def countsPerTickPositiveCheck (cfg : HardwareTimerConfig) : Bool :=
  decide (cfg.countsPerTick > 0)

theorem countsPerTickPositive_iff_check (cfg : HardwareTimerConfig) :
    cfg.countsPerTickPositive ↔ cfg.countsPerTickPositiveCheck = true := by
  unfold countsPerTickPositive countsPerTickPositiveCheck
  simp [decide_eq_true_eq]

end HardwareTimerConfig

/-- AK3-H (A-M05 / MEDIUM): RPi5 hardware timer configuration satisfies
    the `countsPerTick > 0` well-formedness predicate (54000 > 0). -/
theorem rpi5TimerConfig_countsPerTickPositive :
    rpi5TimerConfig.countsPerTickPositive := by
  unfold HardwareTimerConfig.countsPerTickPositive
  rw [rpi5TimerConfig_countsPerTick]
  decide

/-- AK3-H (A-M05 / MEDIUM): Boot-time assertion for a timer configuration.
    Intended usage: a future `PlatformConfig.timerConfig : Option
    HardwareTimerConfig` field would be validated at boot via this
    predicate; current production code uses the module-constant
    `rpi5TimerConfig` which already satisfies the predicate (proven by
    `rpi5TimerConfig_countsPerTickPositive`).

    Runtime check pattern for future callers:
    `if cfg.countsPerTickPositiveCheck then ... else .error .invalidArgument`. -/
def bootTimerConfigValid (cfg : HardwareTimerConfig) : Prop :=
  cfg.countsPerTickPositive

/-- AK3-H: The default RPi5 config passes the boot validity check. -/
theorem rpi5TimerConfig_bootValid : bootTimerConfigValid rpi5TimerConfig :=
  rpi5TimerConfig_countsPerTickPositive

-- ============================================================================
-- AG5-E: Timer interrupt → timerTick binding
-- ============================================================================

/-- AG5-E: Timer interrupt handler configuration.
    Captures the state needed by the Rust timer interrupt handler to bind
    hardware timer events to the Lean model's `timerTick` function.

    The handler is invoked when INTID 30 (timer PPI) fires:
    1. Reprogram the comparator for the next tick
    2. Call `timerTick` to advance the model timer
    3. The comparator reprogramming is modeled by `reprogramComparator`

    This structure is pure — the actual hardware interaction is in the
    Rust HAL (`sele4n-hal/src/timer.rs`). -/
structure TimerInterruptBinding where
  /-- Timer configuration (frequency, interval, comparator). -/
  config : HardwareTimerConfig
  /-- Number of tick interrupts processed so far. -/
  tickCount : Nat := 0
  deriving Repr, DecidableEq

namespace TimerInterruptBinding

/-- AG5-E: Process a timer interrupt event.
    Advances the comparator and increments the tick count.
    Returns the updated binding state.

    This models the Rust side: `reprogram_timer()` + `increment_tick_count()`. -/
def handleTimerInterrupt (binding : TimerInterruptBinding) : TimerInterruptBinding :=
  { binding with
    config := binding.config.reprogramComparator
    tickCount := binding.tickCount + 1 }

/-- AG5-E: Timer interrupt increments tick count by exactly 1. -/
theorem handleTimerInterrupt_incrementsTickCount (binding : TimerInterruptBinding) :
    (binding.handleTimerInterrupt).tickCount = binding.tickCount + 1 := rfl

/-- AG5-E: Timer interrupt advances comparator by exactly one interval. -/
theorem handleTimerInterrupt_advancesComparator (binding : TimerInterruptBinding) :
    (binding.handleTimerInterrupt).config.comparatorValue =
    binding.config.comparatorValue + binding.config.countsPerTick := rfl

/-- AG5-E: Timer interrupt preserves frequency. -/
theorem handleTimerInterrupt_preservesFrequency (binding : TimerInterruptBinding) :
    (binding.handleTimerInterrupt).config.counterFrequencyHz =
    binding.config.counterFrequencyHz := rfl

/-- AG5-E: Timer interrupt preserves tick interval. -/
theorem handleTimerInterrupt_preservesInterval (binding : TimerInterruptBinding) :
    (binding.handleTimerInterrupt).config.tickIntervalNs =
    binding.config.tickIntervalNs := rfl

end TimerInterruptBinding

/-- AG5-E: Default RPi5 timer interrupt binding (starts at tick 0). -/
def rpi5TimerBinding : TimerInterruptBinding where
  config := rpi5TimerConfig
  tickCount := 0

end SeLe4n.Kernel.Architecture
