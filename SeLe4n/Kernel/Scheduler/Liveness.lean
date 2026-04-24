/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Liveness.WCRT
import SeLe4n.Kernel.Scheduler.Liveness.RPi5CanonicalConfig

/-!
# D5-N: Scheduler Liveness — Re-export Hub

This module re-exports all scheduler liveness submodules:
- `TraceModel`: Trace model types, query predicates, counting functions
- `TimerTick`: Timer-tick budget monotonicity and preemption bounds
- `Replenishment`: CBS replenishment timing bounds
- `Yield`: Yield/rotation semantics and FIFO progress bounds
- `BandExhaustion`: Priority-band exhaustion analysis
- `DomainRotation`: Domain rotation bounds
- `WCRT`: CBS-aware WCRT hypotheses, main bounded latency theorem, PIP enhancement
- `RPi5CanonicalConfig`: AN5-E — `DeploymentSchedulingConfig` schema and
  canonical RPi5 instance discharging the `eventuallyExits` hypothesis for
  the v1.0.0 release target (closes `DEF-AK2-K.4`).
-/
