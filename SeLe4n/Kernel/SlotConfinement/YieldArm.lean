-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SlotConfinement.Legs
import SeLe4n.Kernel.Scheduler.Operations.PerCoreScheduleFrames

/-!
# WS-ZA ZA4.3 — the yield writes only the executing core

The SM8.B confinement statements for the yield syscall's transition and the
per-core scheduling point it ends in.  The cross-core non-interference statement
built on them is `yieldOnCore_crossCoreNonInterference`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- WS-ZA ZA4.3: the per-core scheduling point writes only the core it runs on —
its run queue and `current` slot, its register bank, and the outgoing thread's
saved context. -/
theorem scheduleEffectiveOnCore_confinedToCores (st st' : SystemState) (c : CoreId)
    (h : scheduleEffectiveOnCore st c = .ok st') :
    observableSlotsConfinedToCores st st' [c] := by
  have hne : ∀ c', c' ∉ [c] → c ≠ c' := fun c' hc he => hc (by simp [he])
  exact ⟨fun c' hc =>
      (scheduleEffectiveOnCore_independent_of_other_core st c c' st' (hne c' hc) h).2,
    fun c' hc => (scheduleEffectiveOnCore_independent_of_other_core st c c' st' (hne c' hc) h).1,
    fun c' _ => scheduleEffectiveOnCore_activeDomainOnCore st c st' c' h,
    fun c' _ => scheduleEffectiveOnCore_domainTimeRemainingOnCore st c st' c' h,
    fun c' _ => scheduleEffectiveOnCore_domainScheduleIndexOnCore st c st' c' h,
    fun c' hc => scheduleEffectiveOnCore_machine_regsOnCore_ne st c c' st' (hne c' hc) h⟩

/-- WS-ZA ZA4.3: the yield's charge writes only the executing core: the slice
expiry and the budget spend re-enqueue the caller on core `c` (the spend also
refills there, and the replenish queue is no observable slot), and the key hook
raises flags alone. -/
theorem yieldChargeOnCore_confinedToCores (st st' : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (h : yieldChargeOnCore st c tid = .ok st') :
    observableSlotsConfinedToCores st st' [c] := by
  have hne : ∀ c', c' ∉ [c] → c ≠ c' := fun c' hc he => hc (by simp [he])
  unfold yieldChargeOnCore at h
  split at h
  · cases h
  · split at h
    · cases h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c' hc <;>
        simp [sliceExpireOnCore, hne c' hc, SystemState.rewriteObject_scheduler,
          SystemState.rewriteObject_machine]
    all_goals
      split at h
      · cases h
        refine observableSlotsConfinedToCores_then_flagOnly ?_
          (markKeyChangeFor_confinedToCores _ _ _)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c' hc <;>
          simp [spendBudgetOnCore, replenishOnCore, hne c' hc,
            SystemState.rewriteObject_scheduler, SystemState.rewriteObject_machine]
      · cases h

/-- WS-ZA ZA4.3: **the yield writes only the executing core** — its charge and
the scheduling point on that core. -/
theorem yieldOnCore_confinedToCores (st st' : SystemState) (c : CoreId)
    (h : yieldOnCore st c = .ok st') :
    observableSlotsConfinedToCores st st' [c] := by
  unfold yieldOnCore at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i st1 hCharge
      have h2 := observableSlotsConfinedToCores_trans
        (yieldChargeOnCore_confinedToCores st st1 c _ hCharge)
        (scheduleEffectiveOnCore_confinedToCores st1 st' c h)
      exact observableSlotsConfinedToCores_mono (by simp) h2


end SeLe4n.Kernel
