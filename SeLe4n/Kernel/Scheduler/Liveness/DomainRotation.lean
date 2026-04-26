-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Liveness.BandExhaustion

namespace SeLe4n.Kernel.Liveness

open SeLe4n.Model

-- ============================================================================
-- D5-J: Domain rotation bound
-- ============================================================================

/-- D5-J: Conservative upper bound on domain rotation: D × L_max ticks. -/
def domainRotationBound (numDomains : Nat) (maxDomainLength : Nat) : Nat :=
  numDomains * maxDomainLength

/-- D5-J: Maximum domain schedule entry length (recursive, avoiding foldl). -/
def maxDomainLength : List DomainScheduleEntry → Nat
  | [] => 0
  | e :: rest => Nat.max (DomainScheduleEntry.length e) (maxDomainLength rest)

/-- D5-J: Total ticks for one full rotation (recursive). -/
def domainRotationTotal : List DomainScheduleEntry → Nat
  | [] => 0
  | e :: rest => DomainScheduleEntry.length e + domainRotationTotal rest

/-- D5-J: `switchDomain` advances the domain index. Re-export. -/
theorem switchDomain_index_advances
    (schedule : List DomainScheduleEntry)
    (idx : Nat) (hNe : schedule ≠ []) :
    ((idx + 1) % schedule.length) < schedule.length :=
  switchDomain_index_in_bounds schedule idx hNe

/-- D5-J: Domain rotation bound is monotone. -/
theorem domainRotationBound_mono {D₁ D₂ L₁ L₂ : Nat}
    (hD : D₁ ≤ D₂) (hL : L₁ ≤ L₂) :
    domainRotationBound D₁ L₁ ≤ domainRotationBound D₂ L₂ := by
  simp [domainRotationBound]; exact Nat.mul_le_mul hD hL

/-- D5-J: Domain rotation bound is zero for empty schedule. -/
theorem domainRotationBound_empty :
    domainRotationBound 0 L = 0 := by
  simp [domainRotationBound]

/-- D5-J: `maxDomainLength` ≥ each entry's length. -/
theorem maxDomainLength_ge_each
    (schedule : List DomainScheduleEntry) (e : DomainScheduleEntry)
    (hMem : e ∈ schedule) :
    DomainScheduleEntry.length e ≤ maxDomainLength schedule := by
  induction schedule with
  | nil => simp at hMem
  | cons hd tl ih =>
    simp only [maxDomainLength]
    cases hMem with
    | head => exact Nat.le_max_left _ _
    | tail _ hMem => exact Nat.le_trans (ih hMem) (Nat.le_max_right _ _)

/-- D5-J: Domain rotation total ≤ count × max. -/
theorem domainRotationTotal_le_bound
    (schedule : List DomainScheduleEntry) :
    domainRotationTotal schedule ≤
    domainRotationBound schedule.length (maxDomainLength schedule) := by
  induction schedule with
  | nil => simp [domainRotationTotal, domainRotationBound]
  | cons hd tl ih =>
    simp only [domainRotationTotal, maxDomainLength, domainRotationBound,
               List.length_cons]
    -- Need: hd.length + total(tl) ≤ (1 + tl.length) * max(hd.length, maxDomainLength tl)
    have h1 : DomainScheduleEntry.length hd ≤ Nat.max (DomainScheduleEntry.length hd) (maxDomainLength tl) :=
      Nat.le_max_left _ _
    have h2 : maxDomainLength tl ≤ Nat.max (DomainScheduleEntry.length hd) (maxDomainLength tl) :=
      Nat.le_max_right _ _
    have h3 : domainRotationTotal tl ≤ tl.length * maxDomainLength tl := ih
    have h4 : tl.length * maxDomainLength tl ≤
              tl.length * Nat.max (DomainScheduleEntry.length hd) (maxDomainLength tl) :=
      Nat.mul_le_mul_left _ h2
    calc DomainScheduleEntry.length hd + domainRotationTotal tl
        ≤ Nat.max (DomainScheduleEntry.length hd) (maxDomainLength tl) +
          tl.length * Nat.max (DomainScheduleEntry.length hd) (maxDomainLength tl) := by
          omega
      _ = (tl.length + 1) * Nat.max (DomainScheduleEntry.length hd) (maxDomainLength tl) := by
          rw [Nat.succ_mul, Nat.add_comm]

end SeLe4n.Kernel.Liveness
