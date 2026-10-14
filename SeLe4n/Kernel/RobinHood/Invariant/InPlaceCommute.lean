/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.RobinHood.Invariant.MapValueAt

/-!
# In-place writes commute

WS-ZA ZA4.7.  On a table with no resize due, every write to a present key is
`mapValueAt` (`insert_eq_mapValueAt`, `modify_eq_mapValueAt`): one slot's value
rewritten where it stands, no key moved.  Two such writes at different keys
touch different slots, so they commute (`mapValueAt_comm`), and two at one key
compose (`mapValueAt_mapValueAt`).  A fast path that writes one key's value
early, rather than where the specification writes it, is proven equal to the
specification through these.
-/

namespace SeLe4n.Kernel.RobinHood

variable {α β : Type} [BEq α] [Hashable α]

/-- The slot a key's probe answers (`capacity` when the key is absent). -/
@[reducible] def RHTable.probe (t : RHTable α β) (k : α) : Nat :=
  findIdxLoop t.capacity (idealIndex k t.capacity t.hCapPos) k 0 t.slots
    t.capacity t.hSlotsLen t.hCapPos

/-- No resize is due: an insert at a present key rewrites it in place. -/
def RHTable.noResizeDue (t : RHTable α β) : Prop := ¬ t.size * 4 ≥ t.capacity * 3

omit [BEq α] [Hashable α] in
theorem RHTable.ext_slots {t t' : RHTable α β} (hs : t.slots = t'.slots)
    (hz : t.size = t'.size) (hc : t.capacity = t'.capacity) : t = t' := by
  cases t; cases t'; cases hs; cases hz; cases hc; rfl

theorem RHTable.probe_mapValueAt (t : RHTable α β) (k x : α) (f : β → β) :
    (t.mapValueAt k f).probe x = t.probe x := by
  unfold RHTable.probe RHTable.mapValueAt
  dsimp only
  rw [findIdxLoop_modify_mapValue]

theorem RHTable.mapValueAt_slots (t : RHTable α β) (k : α) (f : β → β) :
    (t.mapValueAt k f).slots = t.slots.modify (t.probe k) (RHEntry.mapValue f) := rfl

@[simp] theorem RHTable.noResizeDue_mapValueAt (t : RHTable α β) (k : α) (f : β → β) :
    (t.mapValueAt k f).noResizeDue ↔ t.noResizeDue := Iff.rfl

/-- Two keys whose probes land in one slot below the capacity are one key. -/
theorem RHTable.eq_of_probe_eq [LawfulBEq α] (t : RHTable α β) {k k' : α}
    (h : t.probe k = t.probe k') (hlt : t.probe k < t.capacity) : k = k' := by
  obtain ⟨e, he, hk⟩ := findIdxLoop_key _ _ _ _ _ _ _ _ hlt
  obtain ⟨e', he', hk'⟩ := findIdxLoop_key _ _ k' _ _ _ _ _ (h ▸ hlt)
  have h1 : t.slots[t.probe k]? = some (some e) := he
  have h2 : t.slots[t.probe k']? = some (some e') := he'
  rw [← h, h1] at h2
  cases h2
  exact (beq_iff_eq.1 hk).symm.trans (beq_iff_eq.1 hk')

theorem Array.modify_comm_of_ne {γ : Type} (a : Array γ) {i j : Nat} (f g : γ → γ)
    (h : i ≠ j) : (a.modify i f).modify j g = (a.modify j g).modify i f := by
  apply Array.ext
  · simp
  · intro n h1 h2
    simp only [Array.getElem_modify]
    by_cases hi : i = n <;> by_cases hj : j = n
    · exact absurd (hi.trans hj.symm) h
    · simp [hi, hj]
    · simp [hi, hj]
    · simp [hi, hj]

theorem Array.modify_modify_same {γ : Type} (a : Array γ) (i : Nat) (f g : γ → γ) :
    (a.modify i g).modify i f = a.modify i (f ∘ g) := by
  apply Array.ext
  · simp
  · intro n h1 h2
    simp only [Array.getElem_modify]
    by_cases hi : i = n <;> simp [hi]

theorem Array.modify_of_size_le {γ : Type} (a : Array γ) {i : Nat} (f : γ → γ)
    (h : a.size ≤ i) : a.modify i f = a := by
  apply Array.ext
  · simp
  · intro n h1 h2
    simp only [Array.getElem_modify]
    have : i ≠ n := by simp at h1; omega
    simp [this]

/-- **Writes at two keys commute**: they rewrite two different slots, or (a key
absent) nothing. -/
theorem RHTable.mapValueAt_comm [LawfulBEq α] (t : RHTable α β) {k k' : α} (f g : β → β)
    (hne : k ≠ k') :
    (t.mapValueAt k' g).mapValueAt k f = (t.mapValueAt k f).mapValueAt k' g := by
  refine RHTable.ext_slots ?_ rfl rfl
  simp only [RHTable.mapValueAt_slots, RHTable.probe_mapValueAt]
  by_cases hp : t.probe k = t.probe k'
  · by_cases hlt : t.probe k < t.capacity
    · exact absurd (t.eq_of_probe_eq hp hlt) hne
    · have hs : t.slots.size ≤ t.probe k := by rw [t.hSlotsLen]; omega
      have hs' : t.slots.size ≤ t.probe k' := hp ▸ hs
      rw [Array.modify_of_size_le t.slots _ hs', Array.modify_of_size_le t.slots _ hs,
        Array.modify_of_size_le t.slots _ hs']
  · exact Array.modify_comm_of_ne _ _ _ (Ne.symm hp)

/-- Two writes at one key compose. -/
theorem RHTable.mapValueAt_mapValueAt (t : RHTable α β) (k : α) (f g : β → β) :
    (t.mapValueAt k g).mapValueAt k f = t.mapValueAt k (f ∘ g) := by
  refine RHTable.ext_slots ?_ rfl rfl
  simp only [RHTable.mapValueAt_slots, RHTable.probe_mapValueAt]
  rw [Array.modify_modify_same]
  congr 1
  funext o
  cases o <;> rfl

/-- **An in-place insert is a slot write**. -/
theorem RHTable.insert_eq_mapValueAt [LawfulBEq α] {t : RHTable α β} {k : α} (v : β)
    (h : t.findsInPlace k = true) : t.insert k v = t.mapValueAt k (fun _ => v) := by
  unfold RHTable.findsInPlace at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  obtain ⟨hNo, hFound⟩ := h
  unfold RHTable.insert
  rw [if_neg hNo, RHTable.insertNoResize_eq_impl]
  unfold RHTable.insertNoResizeImpl modifySlotAt
  dsimp only
  rw [if_pos hFound]
  refine RHTable.ext_slots ?_ rfl rfl
  show t.slots.modify (t.probe k) (RHEntry.withValue v) =
    t.slots.modify (t.probe k) (RHEntry.mapValue (fun _ => v))
  congr 1

/-- A present key under no resize is found in place. -/
theorem RHTable.findsInPlace_of_get? [LawfulBEq α] {t : RHTable α β} {k : α} {v : β}
    (hNo : t.noResizeDue) (h : t.get? k = some v) : t.findsInPlace k = true := by
  unfold RHTable.findsInPlace
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq]
  refine ⟨hNo, ?_⟩
  unfold RHTable.get? at h
  simp only [getLoop_eq_findIdxLoop] at h
  apply Classical.byContradiction
  intro hge
  rw [Array.getElem?_eq_none (by rw [t.hSlotsLen]; omega)] at h
  cases h

/-- The value a present key's slot holds. -/
theorem RHTable.slot_of_get? [LawfulBEq α] {t : RHTable α β} {k : α} {v : β}
    (h : t.get? k = some v) :
    ∃ e : RHEntry α β, t.slots[t.probe k]? = some (some e) ∧ e.value = v := by
  unfold RHTable.get? at h
  simp only [getLoop_eq_findIdxLoop] at h
  revert h
  show (t.slots[t.probe k]?).join.map RHEntry.value = some v → _
  cases hs : t.slots[t.probe k]? with
  | none => simp
  | some o =>
    cases o with
    | none => simp
    | some e => intro he; simp at he; exact ⟨e, rfl, he⟩

/-- An absent key's write changes nothing. -/
theorem RHTable.mapValueAt_of_get?_none [LawfulBEq α] {t : RHTable α β} {k : α}
    (h : t.get? k = none) (f : β → β) : t.mapValueAt k f = t := by
  refine RHTable.ext_slots ?_ rfl rfl
  rw [RHTable.mapValueAt_slots]
  by_cases hlt : t.probe k < t.capacity
  · obtain ⟨e, he, _⟩ := findIdxLoop_key _ _ _ _ _ _ _ _ hlt
    unfold RHTable.get? at h
    simp only [getLoop_eq_findIdxLoop] at h
    have he' : t.slots[t.probe k]? = some (some e) := he
    change (t.slots[t.probe k]?).join.map RHEntry.value = none at h
    rw [he'] at h
    cases h
  · exact Array.modify_of_size_le _ _ (by rw [t.hSlotsLen]; omega)

/-- A slot write reads the slot's value only: two writes agreeing on it agree. -/
theorem RHTable.mapValueAt_congr [LawfulBEq α] {t : RHTable α β} {k : α} {v : β}
    (h : t.get? k = some v) {F G : β → β} (hv : F v = G v) :
    t.mapValueAt k F = t.mapValueAt k G := by
  obtain ⟨e, he, hev⟩ := RHTable.slot_of_get? h
  refine RHTable.ext_slots ?_ rfl rfl
  rw [RHTable.mapValueAt_slots, RHTable.mapValueAt_slots]
  apply Array.ext
  · simp
  · intro n h1 h2
    simp only [Array.getElem_modify]
    split
    · next hn =>
      subst hn
      have hlt : t.probe k < t.slots.size := by simpa using h1
      have : t.slots[t.probe k]'hlt = some e := by
        rw [Array.getElem?_eq_getElem hlt] at he
        exact Option.some.inj he
      rw [this]; simp [RHEntry.mapValue, hev, hv]
    · rfl

/-- The identity write changes nothing. -/
theorem RHTable.mapValueAt_id (t : RHTable α β) (k : α) : t.mapValueAt k id = t := by
  refine RHTable.ext_slots ?_ rfl rfl
  rw [RHTable.mapValueAt_slots]
  apply Array.ext
  · simp
  · intro n h1 h2
    simp only [Array.getElem_modify]
    split
    · cases t.slots[n] <;> rfl
    · rfl

/-- **`modify` under no resize is a slot write**. -/
theorem RHTable.modify_eq_mapValueAt [LawfulBEq α] {t : RHTable α β} (k : α) (f : β → β)
    (hNo : t.noResizeDue) : t.modify k f = t.mapValueAt k f := by
  cases hg : t.get? k with
  | none =>
    unfold RHTable.modify; rw [hg, RHTable.mapValueAt_of_get?_none hg]
  | some v =>
    rw [RHTable.modify_of_get? hg, RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? hNo hg)]
    exact RHTable.mapValueAt_congr hg rfl

/-- An insert's no-resize state is the table's when it lands in place. -/
theorem RHTable.noResizeDue_of_findsInPlace {t : RHTable α β} {k : α}
    (h : t.findsInPlace k = true) : t.noResizeDue := by
  unfold RHTable.findsInPlace at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact h.1

end SeLe4n.Kernel.RobinHood
