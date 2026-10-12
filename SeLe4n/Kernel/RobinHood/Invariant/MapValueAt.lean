/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.RobinHood.Invariant.Preservation

/-!
# Rewriting one key's value where it stands

WS-ZA ZA4.5: `RHTable.mapValueAt t k f` applies `f` to the value stored under
`k` in its slot — no probe for a free slot, no resize, no key or distance
moved.  Because a lookup reads slots only through their keys and distances,
the frame holds on **every** table, well-formed or not: `k`'s lookup is mapped
through `f` and every other key's lookup is untouched (`get?_mapValueAt`).
`invExt` is kept as well (`mapValueAt_invExt`).

The run queue writes its links into TCBs through this operation, so the
"nothing but the run-queue links changed" frame needs no table hypothesis.
Compiled, it is one in-place slot write on an exclusive table.
-/

namespace SeLe4n.Kernel.RobinHood

variable {α β : Type} [BEq α] [Hashable α]

/-- Apply `f` to the value stored under `k`, in its slot; a table without `k`
is unchanged (the probe answers `capacity`, past the array). -/
@[inline] def RHTable.mapValueAt (t : RHTable α β) (k : α) (f : β → β) : RHTable α β :=
  let i := findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots
    t.capacity t.hSlotsLen t.hCapPos
  { t with
      slots     := t.slots.modify i (RHEntry.mapValue f)
      hSlotsLen := by rw [Array.size_modify]; exact t.hSlotsLen }

@[simp] theorem RHTable.mapValueAt_size (t : RHTable α β) (k : α) (f : β → β) :
    (t.mapValueAt k f).size = t.size := rfl

@[simp] theorem RHTable.mapValueAt_capacity (t : RHTable α β) (k : α) (f : β → β) :
    (t.mapValueAt k f).capacity = t.capacity := rfl

omit [Hashable α] in
/-- Mapping one slot's value leaves every probe where it was. -/
theorem findIdxLoop_modify_mapValue (fuel idx : Nat) (k : α) (d : Nat)
    (s : Array (Option (RHEntry α β))) (i : Nat) (f : β → β) (capacity : Nat)
    (hLen' : (s.modify i (RHEntry.mapValue f)).size = capacity)
    (hCapPos : 0 < capacity) :
    findIdxLoop fuel idx k d (s.modify i (RHEntry.mapValue f)) capacity hLen' hCapPos =
      findIdxLoop fuel idx k d s capacity (by rw [← hLen', Array.size_modify]) hCapPos :=
  findIdxLoop_congr _ _ _ _ _ _ _ _ _ _ (by
    intro j h1 h2
    simp only [Array.getElem_modify]
    split
    · next hj => subst hj; cases s[i] <;> rfl
    · rfl)

/-- **The frame, on every table**: `k`'s lookup is mapped through `f`, every
other key's is unchanged. -/
theorem RHTable.get?_mapValueAt [LawfulBEq α] (t : RHTable α β) (k x : α) (f : β → β) :
    (t.mapValueAt k f).get? x = if k == x then (t.get? x).map f else t.get? x := by
  unfold RHTable.mapValueAt RHTable.get?
  simp only [getLoop_eq_findIdxLoop]
  rw [findIdxLoop_modify_mapValue, Array.getElem?_modify]
  split
  · next hij =>
    by_cases hlt : findIdxLoop t.capacity (idealIndex x t.capacity t.hCapPos) x 0 t.slots
        t.capacity t.hSlotsLen t.hCapPos < t.capacity
    · obtain ⟨e, he, hex⟩ := findIdxLoop_key _ _ _ _ _ _ _ _ hlt
      obtain ⟨e', he', hek⟩ := findIdxLoop_key _ _ k _ _ _ _ _ (by rw [hij]; exact hlt)
      rw [hij, he] at he'; cases he'
      have hkx : (k == x) = true :=
        beq_iff_eq.2 ((beq_iff_eq.1 hek).symm.trans (beq_iff_eq.1 hex))
      rw [if_pos hkx, he]
      simp [RHEntry.mapValue]
    · have hNone : t.slots[findIdxLoop t.capacity (idealIndex x t.capacity t.hCapPos) x 0
          t.slots t.capacity t.hSlotsLen t.hCapPos]? = none :=
        Array.getElem?_eq_none (by rw [t.hSlotsLen]; omega)
      rw [hNone]
      split <;> simp
  · next hij =>
    have hkx : (k == x) = false := by
      cases e : (k == x)
      · rfl
      · exact absurd (by rw [beq_iff_eq.1 e]) hij
    simp [hkx]


-- ============================================================================
-- `invExt` is kept: no key, distance or occupancy moves
-- ============================================================================

private theorem countP_modify_of {γ : Type} (p : γ → Bool) (g : γ → γ)
    (hg : ∀ a, p (g a) = p a) :
    ∀ (l : List γ) (i : Nat), (l.modify i g).countP p = l.countP p
  | [], _ => by simp
  | a :: l, 0 => by simp [List.modify, List.countP_cons, hg]
  | a :: l, i + 1 => by
      simp only [List.modify_succ_cons, List.countP_cons]
      rw [countP_modify_of p g hg l i]

/-- Every slot of the mapped table holds what the original holds there, up to
the value. -/
private theorem mapValueAt_slot (t : RHTable α β) (k : α) (f : β → β) (j : Nat)
    (h : j < (t.mapValueAt k f).slots.size) (h' : j < t.slots.size) :
    ((t.mapValueAt k f).slots[j]'h).map (fun e => (e.key, e.dist)) =
      (t.slots[j]'h').map (fun e => (e.key, e.dist)) := by
  unfold RHTable.mapValueAt
  simp only [Array.getElem_modify]
  split
  · cases t.slots[j] <;> rfl
  · rfl

private theorem mapValueAt_slot_back (t : RHTable α β) (k : α) (f : β → β) {j : Nat}
    (h : j < (t.mapValueAt k f).slots.size) (h' : j < t.slots.size) {e : RHEntry α β}
    (he : (t.mapValueAt k f).slots[j]'h = some e) :
    ∃ e₀, t.slots[j]'h' = some e₀ ∧ e.key = e₀.key ∧ e.dist = e₀.dist := by
  have := mapValueAt_slot t k f j h h'
  rw [he] at this
  cases hs : t.slots[j]'h' with
  | none => rw [hs] at this; cases this
  | some e₀ =>
      rw [hs] at this
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      exact ⟨e₀, rfl, this.1, this.2⟩

private theorem mapValueAt_slot_fwd (t : RHTable α β) (k : α) (f : β → β) {j : Nat}
    (h : j < (t.mapValueAt k f).slots.size) (h' : j < t.slots.size) {e₀ : RHEntry α β}
    (he : t.slots[j]'h' = some e₀) :
    ∃ e, (t.mapValueAt k f).slots[j]'h = some e ∧ e.key = e₀.key ∧ e.dist = e₀.dist := by
  have := mapValueAt_slot t k f j h h'
  rw [he] at this
  cases e : (t.mapValueAt k f).slots[j]'h with
  | none => rw [e] at this; cases this
  | some e' =>
      rw [e] at this
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      exact ⟨e', rfl, this.1, this.2⟩

theorem RHTable.mapValueAt_invExt [LawfulBEq α] (t : RHTable α β) (k : α) (f : β → β)
    (hInv : t.invExt) : (t.mapValueAt k f).invExt := by
  obtain ⟨hWF, hDist, hNoDup, hPCD⟩ := hInv
  have hLen : ∀ j, j < t.capacity → j < t.slots.size := fun j h => t.hSlotsLen ▸ h
  have hLen' : ∀ j, j < t.capacity → j < (t.mapValueAt k f).slots.size :=
    fun j h => (t.mapValueAt k f).hSlotsLen ▸ h
  refine ⟨⟨(t.mapValueAt k f).hSlotsLen, t.hCapPos, ?_, hWF.sizeBound⟩, ?_, ?_, ?_⟩
  · show t.size = countOccupied (t.slots.modify _ (RHEntry.mapValue f))
    unfold countOccupied
    rw [Array.toList_modify, countP_modify_of _ _ (fun a => by cases a <;> rfl)]
    exact hWF.sizeCount
  · intro i hi e he
    obtain ⟨e₀, he₀, hk, hd⟩ := mapValueAt_slot_back t k f _ (hLen i hi) he
    rw [hk, hd]; exact hDist i hi e₀ he₀
  · intro i j hi hj ei ej hei hej hkey
    obtain ⟨ei₀, hei₀, hki, _⟩ := mapValueAt_slot_back t k f _ (hLen i hi) hei
    obtain ⟨ej₀, hej₀, hkj, _⟩ := mapValueAt_slot_back t k f _ (hLen j hj) hej
    exact hNoDup i j hi hj ei₀ ej₀ hei₀ hej₀ (by rw [← hki, ← hkj]; exact hkey)
  · intro p hp e he d hd
    obtain ⟨e₀, he₀, hk, hdist⟩ := mapValueAt_slot_back t k f _ (hLen p hp) he
    obtain ⟨e'', he'', hge⟩ := hPCD p hp e₀ he₀ d (hdist ▸ hd)
    obtain ⟨e', he', _, hd'⟩ := mapValueAt_slot_fwd t k f _ _ he''
    exact ⟨e', by simp only [RHTable.mapValueAt_capacity, hk] at he' ⊢; exact he', hd' ▸ hge⟩

end SeLe4n.Kernel.RobinHood
