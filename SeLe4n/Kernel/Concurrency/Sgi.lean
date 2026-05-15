-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM0.H SgiKind enumeration)

import SeLe4n.Prelude

/-!
# WS-SM SM0.H — Software-Generated Interrupt (SGI) kinds

ARM GIC-400's SGI INTID space `[0, 16)` carries software-generated
interrupts.  The seLe4n kernel reserves five of those slots for
SMP coordination duties:

| INTID | Kind                | Purpose |
|-------|---------------------|---------|
| 0     | `reschedule`        | Wake a remote core for scheduling |
| 1     | `tlbShootdownReq`   | Request a remote TLB invalidation |
| 2     | `tlbShootdownAck`   | Acknowledge completion of (1)     |
| 3     | `cacheBroadcast`    | Broadcast cache-maintenance op    |
| 4     | `haltAll`           | Halt all cores (panic / shutdown) |

The remaining 11 slots `[5, 16)` are reserved for application-layer
use via a future capability operation (post-1.0; not in WS-SM scope).

Each kind maps to a distinct `Fin 16` index — proven both
**injective** (`toIntid_injective`) and **in-range**
(`toIntid_in_range`) so downstream SM5 cross-core wake primitives
can route a `SgiKind` to the GIC's INTID register without an
out-of-bounds branch.
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM0.H — SgiKind enumeration and INTID mapping
-- ============================================================================

/-- WS-SM SM0.H: software-generated interrupt kinds reserved for
kernel-internal SMP coordination.  Each kind binds to a fixed
INTID in the ARM GIC-400 software-generated range `[0, 16)`. -/
inductive SgiKind where
  | reschedule         -- INTID 0
  | tlbShootdownReq    -- INTID 1
  | tlbShootdownAck    -- INTID 2
  | cacheBroadcast     -- INTID 3
  | haltAll            -- INTID 4
  deriving DecidableEq, Repr, Inhabited

/-- WS-SM SM0.H: map an `SgiKind` to its reserved GIC-400 INTID.
The result is `Fin 16` so the in-range obligation is structurally
discharged at the type level — no runtime bounds check is required
when emitting the value to GICD_SGIR.  Each numeric literal is
verified `< 16` by `decide` at definition time. -/
def SgiKind.toIntid : SgiKind → Fin 16
  | .reschedule      => ⟨0, by decide⟩
  | .tlbShootdownReq => ⟨1, by decide⟩
  | .tlbShootdownAck => ⟨2, by decide⟩
  | .cacheBroadcast  => ⟨3, by decide⟩
  | .haltAll         => ⟨4, by decide⟩

/-- WS-SM SM0.H: distinct kinds map to distinct INTIDs.  C(5,2) = 10
inequalities verified by case analysis + `decide`.  Catches an
accidental INTID collision at elaboration if a future maintainer
edits `toIntid` to alias two kinds. -/
theorem SgiKind.toIntid_injective :
    ∀ k₁ k₂ : SgiKind, k₁ ≠ k₂ → k₁.toIntid ≠ k₂.toIntid := by
  intro k₁ k₂ h
  cases k₁ <;> cases k₂ <;> simp_all <;> decide

/-- WS-SM SM0.H: every reserved INTID lies in the SGI range
`[0, 16)`.  Trivial from the `Fin 16` carrier; surfaced as a named
theorem so SM5 cross-core wake primitives can `apply` it directly
when constructing `gicd_sgir` register values. -/
theorem SgiKind.toIntid_in_range :
    ∀ k : SgiKind, k.toIntid.val < 16 := by
  intro k; exact k.toIntid.isLt

/-- WS-SM SM0.H: enumerate every SGI kind.  Used by the SM0
foundations test suite to walk the inductive at meta level. -/
def SgiKind.all : List SgiKind :=
  [.reschedule, .tlbShootdownReq, .tlbShootdownAck, .cacheBroadcast, .haltAll]

/-- WS-SM SM0.H: the enumeration has exactly five entries. -/
theorem SgiKind.all_length : SgiKind.all.length = 5 := by decide

/-- WS-SM SM0.H: the enumeration has no duplicates. -/
theorem SgiKind.all_nodup : SgiKind.all.Nodup := by decide

/-- WS-SM SM0.H: every INTID assignment is `< 5` because the kernel
only reserves the lowest 5 slots.  Stronger than `toIntid_in_range`
(which gives `< 16`); useful when a downstream theorem needs to
distinguish kernel-reserved from application-reserved SGIs. -/
theorem SgiKind.toIntid_lt_five :
    ∀ k : SgiKind, k.toIntid.val < 5 := by
  intro k; cases k <;> decide

/-- WS-SM SM0.H: per-kind INTID assignments — decidable witnesses
useful for surface-anchor `#check`s and `decide` examples in the
foundations test suite. -/
theorem SgiKind.reschedule_intid : SgiKind.reschedule.toIntid.val = 0 := rfl
theorem SgiKind.tlbShootdownReq_intid : SgiKind.tlbShootdownReq.toIntid.val = 1 := rfl
theorem SgiKind.tlbShootdownAck_intid : SgiKind.tlbShootdownAck.toIntid.val = 2 := rfl
theorem SgiKind.cacheBroadcast_intid : SgiKind.cacheBroadcast.toIntid.val = 3 := rfl
theorem SgiKind.haltAll_intid : SgiKind.haltAll.toIntid.val = 4 := rfl

end SeLe4n.Kernel.Concurrency
