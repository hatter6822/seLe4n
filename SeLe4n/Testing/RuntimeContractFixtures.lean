-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n

open SeLe4n.Model

namespace SeLe4n.Testing

/--
Testing-only permissive runtime contract fixture.

This contract is intentionally broad to exercise success branches in adapter traces
and MUST NOT be imported by production kernel modules.
-/
def runtimeContractAcceptAll : SeLe4n.Kernel.Architecture.RuntimeBoundaryContract :=
  {
    timerMonotonic := fun st st' => st.machine.timer ≤ st'.machine.timer
    registerContextStable := fun _ _ => True
    memoryAccessAllowed := fun _ _ => True
    timerMonotonicDecidable := by
      intro st st'
      infer_instance
    registerContextStableDecidable := by
      intro st st'
      infer_instance
    memoryAccessAllowedDecidable := by
      intro st addr
      infer_instance
  }

/--
Testing-only restrictive runtime contract fixture.

This contract intentionally denies all runtime paths so tests can assert explicit
error branches in adapter semantics.
-/
def runtimeContractDenyAll : SeLe4n.Kernel.Architecture.RuntimeBoundaryContract :=
  {
    timerMonotonic := fun _ _ => False
    registerContextStable := fun _ _ => False
    memoryAccessAllowed := fun _ _ => False
    timerMonotonicDecidable := by
      intro st st'
      infer_instance
    registerContextStableDecidable := by
      intro st st'
      infer_instance
    memoryAccessAllowedDecidable := by
      intro st addr
      infer_instance
  }

/--
Testing-only timer-centric runtime contract fixture (WS-D5/F-09).

Allows timer operations (timer monotonicity passes) but denies register
context stability and memory access.  Exercises the timer-success /
register-denied / memory-denied branch combination.
-/
def runtimeContractTimerOnly : SeLe4n.Kernel.Architecture.RuntimeBoundaryContract :=
  {
    timerMonotonic := fun st st' => st.machine.timer ≤ st'.machine.timer
    registerContextStable := fun _ _ => False
    memoryAccessAllowed := fun _ _ => False
    timerMonotonicDecidable := by
      intro st st'
      infer_instance
    registerContextStableDecidable := by
      intro st st'
      infer_instance
    memoryAccessAllowedDecidable := by
      intro st addr
      infer_instance
  }

/--
Testing-only read-only memory runtime contract fixture (WS-D5/F-09).

Allows memory access but denies timer monotonicity and register context
stability.  Exercises the memory-success / timer-denied / register-denied
branch combination.
-/
def runtimeContractReadOnlyMemory : SeLe4n.Kernel.Architecture.RuntimeBoundaryContract :=
  {
    timerMonotonic := fun _ _ => False
    registerContextStable := fun _ _ => False
    memoryAccessAllowed := fun _ _ => True
    timerMonotonicDecidable := by
      intro st st'
      infer_instance
    registerContextStableDecidable := by
      intro st st'
      infer_instance
    memoryAccessAllowedDecidable := by
      intro st addr
      infer_instance
  }

end SeLe4n.Testing
