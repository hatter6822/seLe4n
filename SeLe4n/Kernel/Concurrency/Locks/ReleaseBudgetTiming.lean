-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Locks.RwLock
import SeLe4n.Kernel.Architecture.TimerModel

/-!
# WS-LC LC5.5 — the release budget in hardware ticks

> **STATUS: staged.**  It imports `Architecture.TimerModel`, which is staged
> for H3, and production must not import staged.  That partition is the right
> one rather than an obstacle: everything here needs a **counter frequency**,
> which is a property of a board and not of a lock, so it cannot belong to the
> lock model even in principle.

## The three denominations, and why they are three

`MAX_RELEASE_DELAY` is a count of **lock operations**.  That is the only unit
`FairTrace` can speak in, because a step is the only thing an execution
records — which is exactly what SM2.C-T registered as debt: a holder may
occupy its critical section for an unbounded real interval with no operation
recorded, so a step figure read as wall-clock is a figure with no denominator.

WS-LC LC5 supplies the denominators, one conversion at a time, each with the
assumption it needs stated where it is used:

1. **steps → cycles** needs a per-critical-section ceiling `tCs`
   (`RwLockExecution.BoundedCriticalSection`).  That assumption is about the
   *deployment's* code, so it lives in the lock model as a hypothesis:
   `releaseBudgetCycles`.
2. **cycles → model ticks** needs the counter's frequency and the tick
   interval.  That is a property of the hardware, so it lives here, and it
   reuses `HardwareTimerConfig.hardwareTimerToModelTick` rather than
   re-deriving the division — the same conversion the timer subsystem
   performs, applied to a different number.

A reader who wants `MAX_RELEASE_DELAY` in milliseconds needs both, and the
two-step shape is the point: each step names the assumption that makes it
valid, so no figure can be quoted as a time without also quoting what was
assumed to get it there.
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n.Kernel.Architecture

/-- **WS-LC LC5.5**: the release budget expressed in the timer model's ticks.

A cycle count *is* a counter value — the counter increments once per cycle at
`counterFrequencyHz` — so the budget in ticks is the timer subsystem's own
counter-to-tick conversion applied to the budget in cycles.  Reusing
`hardwareTimerToModelTick` rather than writing the division again is
deliberate: a second spelling of the same conversion is a second answer to one
question, and the two would drift the first time the timer model's rounding
changed. -/
def releaseBudgetTicks (cfg : HardwareTimerConfig) (maxDelay tCs : Nat) : Nat :=
  cfg.hardwareTimerToModelTick (releaseBudgetCycles maxDelay tCs)

/-- **WS-LC LC5.5**: a longer budget is never fewer ticks.

Inherited from the timer model's own monotonicity, which is the property that
makes the conversion usable as a bound at all: an upper bound in cycles maps
to an upper bound in ticks. -/
theorem releaseBudgetTicks_monotone (cfg : HardwareTimerConfig)
    (maxDelay tCs tCs' : Nat) (h : tCs ≤ tCs') :
    releaseBudgetTicks cfg maxDelay tCs ≤ releaseBudgetTicks cfg maxDelay tCs' :=
  cfg.hardwareTimerToModelTick_monotone _ _ (Nat.mul_le_mul_left maxDelay h)

/-- **WS-LC LC5.5**: an execution's actual delay, in ticks, never exceeds the
budget in ticks.

The composition of the two conversions, and the result that makes the
denomination worth having: a bound proved in *steps* by the fairness argument
is here a bound in the units a timer interrupt counts.  Both assumptions are
visible in the statement — the per-critical-section ceiling, and the board's
timer configuration. -/
theorem elapsed_ticks_le_releaseBudgetTicks (cfg : HardwareTimerConfig)
    (e : RwLockExecution) (maxDelay tCs : Nat)
    (h_cost : e.BoundedCriticalSection tCs) (a b : Nat) (h : b - a ≤ maxDelay) :
    cfg.hardwareTimerToModelTick (e.elapsed a b)
      ≤ releaseBudgetTicks cfg maxDelay tCs :=
  cfg.hardwareTimerToModelTick_monotone _ _
    (releaseBudgetCycles_bounds_elapsed e maxDelay tCs h_cost a b h)

/-- **WS-LC LC5.5**: what the placeholder is worth on the first hardware
target.

The Raspberry Pi 5's generic timer runs at 54 MHz with 1 ms model ticks, so
one tick is 54000 counter cycles.  At a one-cycle critical-section ceiling the
1024-step budget is under a single tick; at a 54000-cycle ceiling — a full
millisecond of critical section, which would be a serious kernel defect — it
is 1024 ticks.

Stated as a pair of evaluations rather than prose because the arithmetic is
the whole content: the same step budget spans three orders of magnitude of
real time depending on an assumption the lock model does not make, which is
precisely why the step figure alone was never a time. -/
theorem releaseBudgetTicks_rpi5_range :
    releaseBudgetTicks
      { counterFrequencyHz := 54000000, tickIntervalNs := 1000000,
        comparatorValue := 0 } MAX_RELEASE_DELAY 1 = 0 ∧
    releaseBudgetTicks
      { counterFrequencyHz := 54000000, tickIntervalNs := 1000000,
        comparatorValue := 0 } MAX_RELEASE_DELAY 54000 = MAX_RELEASE_DELAY := by
  constructor <;> rfl

end SeLe4n.Kernel.Concurrency
