/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.RobinHood.Invariant.MapValueAt

/-!
# A fold that reads values through a projection

WS-ZA ZA4.7.  `RHTable.fold` visits the slots in order, so a fold that reads
each value only through `π` sees nothing but the table's slots seen through
`π` (`RHTable.slotView`): two tables with the same view fold to the same result
(`RHTable.fold_eq_of_slotView`).  A `mapValueAt` whose rewrite `π` cannot see
keeps the view (`RHTable.slotView_mapValueAt`), on any table.

The reply-receive's in-place path carries a whole-table scan across its reply
leg this way: the scan reads one code per object, and no write of the reply
leg moves that code.
-/

namespace SeLe4n.Kernel.RobinHood

variable {α β γ : Type} [BEq α] [Hashable α]

/-- The table's slots, each value read through `π`. -/
def RHTable.slotView (t : RHTable α β) (π : β → γ) : List (Option γ) :=
  t.slots.toList.map (Option.map fun e => π e.value)

omit [BEq α] [Hashable α] in
private theorem foldl_slots_view {δ : Type} (π : β → γ) (F : δ → γ → δ) :
    ∀ (l : List (Option (RHEntry α β))) (init : δ),
      l.foldl (fun acc slot => match slot with | none => acc | some e => F acc (π e.value)) init =
        (l.map (Option.map fun e => π e.value)).foldl
          (fun acc s => match s with | none => acc | some x => F acc x) init
  | [], _ => rfl
  | none :: tl, init => by
      simp only [List.foldl_cons, List.map_cons, Option.map_none]
      exact foldl_slots_view π F tl init
  | some e :: tl, init => by
      simp only [List.foldl_cons, List.map_cons, Option.map_some]
      exact foldl_slots_view π F tl _

omit [BEq α] [Hashable α] in
/-- **A fold reading values through `π` sees only the slots' view.** -/
theorem RHTable.fold_eq_of_slotView {δ : Type} (t t' : RHTable α β) (π : β → γ) (init : δ)
    (F : δ → γ → δ) (h : t'.slotView π = t.slotView π) :
    t'.fold init (fun acc _ v => F acc (π v)) = t.fold init (fun acc _ v => F acc (π v)) := by
  unfold RHTable.fold
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  have h1 := foldl_slots_view π F t'.slots.toList init
  have h2 := foldl_slots_view π F t.slots.toList init
  unfold RHTable.slotView at h
  rw [h] at h1
  exact h1.trans h2.symm

omit [BEq α] [Hashable α] in
private theorem map_modify_of {δ ε : Type} (g : δ → ε) (m : δ → δ) (l : List δ) (i : Nat)
    (h : ∀ x, l[i]? = some x → g (m x) = g x) :
    (l.modify i m).map g = l.map g := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, List.getElem?_modify]
  split
  · next hij =>
    subst hij
    cases hx : l[i]? with
    | none => rfl
    | some x => simp [h x hx]
  · simp

/-- **Mapping one value in place keeps the view** when the map keeps `π` of
the value the key holds. -/
theorem RHTable.slotView_mapValueAt [LawfulBEq α] (t : RHTable α β) (k : α) (f : β → β)
    (π : β → γ) (h : ∀ v, t.get? k = some v → π (f v) = π v) :
    (t.mapValueAt k f).slotView π = t.slotView π := by
  unfold RHTable.slotView RHTable.mapValueAt
  simp only [Array.toList_modify]
  apply map_modify_of
  intro x hx
  rw [Array.getElem?_toList] at hx
  cases x with
  | none => rfl
  | some e =>
    have hGet : t.get? k = some e.value := by
      unfold RHTable.get?
      rw [getLoop_eq_findIdxLoop, hx]
      rfl
    simp only [RHEntry.mapValue, Option.map_some, h e.value hGet]

end SeLe4n.Kernel.RobinHood
