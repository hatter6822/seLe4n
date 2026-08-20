/-
Copyright (c) 2025 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license.

WS-SM SM9.D.1 / SM9.D.13: **declassification taint** — the causal provenance the
laundering detector reasons over.

A taint value is a bounded set of *declassification event timestamps*: the
identities of the downgrades whose released content reached the object carrying
the taint.  SM9.A.1a made those identities stable across drains
(`timestamp = epoch + index`), which is what lets a tag outlive the trail entry
that created it — a prerequisite this module depends on rather than restates.

**Why a leaf.**  `DeclassificationEvent.predecessorTags` (SM9.D.13a) carries a
taint snapshot, `AuditRecord.lean` sits below `Model/State.lean`, and the
mounted table is a `SystemState` field — so the *value* type has to sit below
all three.  It imports `SeLe4n.Prelude` and nothing else; the table type, the
propagation planners and the live seam are `InformationFlow/TaintPropagation.lean`,
above `Model/State.lean`.

**Why the bound is a field of the type and not an invariant.**  §6 of
`docs/planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md` decides this for all
three SM9 mounts: a bound carried by the type costs no `proofLayerInvariantBundle`
conjunct and — more to the point — no *capacity obligation at every writer*.
`RefusalLedger` gets it from a `Vector` and two `Fin`s; a taint is a variable-size
set, so it gets it from a refinement field instead.  Lean's definitional proof
irrelevance makes that free at the equality level (`DecidableEq` below compares
the two data fields and nothing else), and it makes `tags_bounded` available for
**every** value of the type, including one a frame lemma carried across an
unrelated transition.

**Why overflow saturates rather than evicting.**  Evicting a tag loses a causal
link, which for a *detector* is a false negative — the unsafe direction.
Saturating claims the value is tainted by everything, which can only add reports
(`taintSaturate_over_approximates` states that direction as a theorem rather
than leaving it to a comment).  `saturated` is therefore the top of the order,
and `top` is its canonical representative: an operation that saturates discards
the tags it held, so no value the API produces can be simultaneously saturated
and carrying a stale tag list.
-/
import SeLe4n.Prelude

namespace SeLe4n.Kernel

-- ============================================================================
-- §1  WS-SM SM9.D.1 — the bounded tag list
-- ============================================================================

/-- WS-SM SM9.D.1: how many distinct declassification identities one object may
carry before its taint saturates.

A configuration choice, not a correctness one — every theorem here is stated
against the name.  Sized small deliberately: the tags are exported to a
privileged monitor through SM9.A's chunk protocol, at up to
`maxAuditFieldChunks` calls per tag, and an object that has received content
from eight distinct authorized downgrades is already a laundering report's
subject rather than a value whose ninth tag adds information. -/
def maxTaintTags : Nat := 8

/-- WS-SM SM9.D.1: `maxTaintTags` is positive, so a single tag always fits and
`insert` on an empty taint never saturates.  Stated because the saturation arms
below would otherwise be vacuously reachable from `empty`. -/
theorem maxTaintTags_pos : 0 < maxTaintTags := by decide

/-- WS-SM SM9.D.1: ordered, duplicate-free insertion into a tag list.

Sorted rather than prepended so the representation is canonical for a given set:
two propagation orders that deliver the same tags produce the same *value*, which
is what keeps a golden fixture stable and a recorded `predecessorTags` snapshot
comparable across runs.  (The semilattice laws below are still stated up to
`taintEquiv`; canonicity makes them hold at the value level in practice, and
proving that would need a sorted-list extensionality result the toolchain's core
library does not carry.) -/
def insertTag : List Nat → Nat → List Nat
  | [], t => [t]
  | x :: xs, t => if t < x then t :: x :: xs else if t = x then x :: xs else x :: insertTag xs t

/-- WS-SM SM9.D.1: insertion adds at most one element — the arithmetic the
bound's `if` below rests on. -/
theorem insertTag_length_le (l : List Nat) (t : Nat) :
    (insertTag l t).length ≤ l.length + 1 := by
  induction l with
  | nil => simp [insertTag]
  | cons x xs ih =>
    simp only [insertTag]
    split
    · simp
    · split
      · simp
      · simp only [List.length_cons]; omega

/-- WS-SM SM9.D.1: insertion never removes an element. -/
theorem insertTag_length_ge (l : List Nat) (t : Nat) :
    l.length ≤ (insertTag l t).length := by
  induction l with
  | nil => simp [insertTag]
  | cons x xs ih =>
    simp only [insertTag]
    split
    · simp
    · split
      · simp
      · simp only [List.length_cons]; omega

/-- WS-SM SM9.D.1: **membership after insertion** — the inserted tag and exactly
the tags that were already there.  Every propagation result below is read
through this. -/
theorem mem_insertTag (l : List Nat) (t a : Nat) :
    a ∈ insertTag l t ↔ a = t ∨ a ∈ l := by
  induction l with
  | nil => simp [insertTag]
  | cons x xs ih =>
    simp only [insertTag]
    split
    · simp only [List.mem_cons]
    · split
      · rename_i heq
        subst heq
        simp only [List.mem_cons]
        constructor
        · rintro (rfl | h)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)
        · rintro (rfl | rfl | h)
          · exact Or.inl rfl
          · exact Or.inl rfl
          · exact Or.inr h
      · simp only [List.mem_cons, ih]
        constructor
        · rintro (rfl | rfl | h)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)
        · rintro (rfl | rfl | h)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)

-- ============================================================================
-- §2  WS-SM SM9.D.1 — the taint value
-- ============================================================================

/-- WS-SM SM9.D.1 / SM9.D.13: **a bounded set of declassification identities**,
with a top.

`tags` names the downgrades whose released content reached this object;
`saturated` is the top of the order, reached when a join would exceed
`maxTaintTags`.  A saturated taint contains *every* identity
(`contains_of_saturated`), which is the over-approximation a detector needs.

`tags_bounded` is the structural bound §6 of the plan calls for: it holds of
every value of the type, so no writer owes a capacity obligation and no
`proofLayerInvariantBundle` conjunct reads the mounted table. -/
structure DeclassificationTaint where
  /-- Tainted by everything: the top of the order. -/
  saturated : Bool
  /-- The declassification identities (SM9.A.1a global timestamps) this value
      carries, ordered and duplicate-free. -/
  tags : List Nat
  /-- WS-SM SM9.D.1: the structural bound.  A `Prop` field, so definitional
      proof irrelevance keeps it invisible to equality. -/
  tags_bounded : tags.length ≤ maxTaintTags

namespace DeclassificationTaint

/-- WS-SM SM9.D.1: two taints are equal exactly when their data fields are —
the proof field is irrelevant, definitionally.  Written by hand rather than
derived because `deriving DecidableEq` has no instance for a `Prop` field. -/
instance : DecidableEq DeclassificationTaint := fun a b =>
  if h : a.saturated = b.saturated ∧ a.tags = b.tags then
    .isTrue (by
      obtain ⟨hs, ht⟩ := h
      cases a with | mk sa ta pa =>
      cases b with | mk sb tb pb =>
      simp only at hs ht
      subst hs; subst ht; rfl)
  else
    .isFalse (fun heq => h (by subst heq; exact ⟨rfl, rfl⟩))

/-- WS-SM SM9.D.1: the external rendering — the data fields, since the proof
field has no content.  Hand-written for the same reason `DecidableEq` is. -/
instance : Repr DeclassificationTaint where
  reprPrec T _ := Std.Format.text s!"taint(saturated := {T.saturated}, tags := {T.tags})"

/-- WS-SM SM9.D.1: **no identities** — the boot value and the value every object
starts with. -/
def empty : DeclassificationTaint := ⟨false, [], by simp⟩

/-- WS-SM SM9.D.1: **tainted by everything** — the top of the order, and the
canonical saturated value.

Canonical deliberately: an operation that saturates drops the tags it was
carrying, so `saturated = true` and a non-empty `tags` list is not a shape the
API produces (`insert_saturated`, `join_saturated`). -/
def top : DeclassificationTaint := ⟨true, [], by simp⟩

instance : Inhabited DeclassificationTaint := ⟨empty⟩

/-- WS-SM SM9.D.1: **does this taint carry the identity `t`?**

`true` for every `t` on a saturated value — that is what "tainted by everything"
means, and it is the direction that keeps the detector free of false negatives. -/
def contains (T : DeclassificationTaint) (t : Nat) : Bool :=
  T.saturated || decide (t ∈ T.tags)

/-- WS-SM SM9.D.1: the empty taint carries nothing. -/
@[simp] theorem contains_empty (t : Nat) : empty.contains t = false := by
  simp [contains, empty]

/-- WS-SM SM9.D.13: **a saturated taint carries every identity** — the
over-approximation, at the value level. -/
@[simp] theorem contains_top (t : Nat) : top.contains t = true := by
  simp [contains, top]

/-- WS-SM SM9.D.13: the same, for any saturated value. -/
theorem contains_of_saturated {T : DeclassificationTaint} (h : T.saturated = true)
    (t : Nat) : T.contains t = true := by
  simp [contains, h]

/-- WS-SM SM9.D.1: on an unsaturated taint, `contains` is list membership. -/
theorem contains_iff_mem {T : DeclassificationTaint} (h : T.saturated = false) (t : Nat) :
    T.contains t = true ↔ t ∈ T.tags := by
  simp [contains, h]

/-- WS-SM SM9.D.1: **add one identity.**

Saturates rather than evicting when the bound is reached, and collapses a
saturated input to `top` so the result is canonical.  The bound is checked on
the *output* list, which is what makes `insert` total and its result
unconditionally well-formed. -/
def insert (T : DeclassificationTaint) (t : Nat) : DeclassificationTaint :=
  if T.saturated then top
  else
    if h : (insertTag T.tags t).length ≤ maxTaintTags then
      ⟨false, insertTag T.tags t, h⟩
    else top

/-- WS-SM SM9.D.1: a saturated taint absorbs insertion. -/
@[simp] theorem insert_saturated {T : DeclassificationTaint} (h : T.saturated = true)
    (t : Nat) : T.insert t = top := by
  simp [insert, h]

/-- WS-SM SM9.D.1: **insertion records the identity** — whatever the bound does. -/
@[simp] theorem contains_insert_self (T : DeclassificationTaint) (t : Nat) :
    (T.insert t).contains t = true := by
  unfold insert
  split
  · simp
  · split
    · rename_i hb
      simp only [contains, Bool.false_or, decide_eq_true_eq]
      exact (mem_insertTag T.tags t t).mpr (Or.inl rfl)
    · simp

/-- WS-SM SM9.D.1: **insertion never forgets** — the no-loss property, and the
reason overflow saturates instead of evicting. -/
theorem contains_insert_of_contains {T : DeclassificationTaint} {a : Nat}
    (h : T.contains a = true) (t : Nat) : (T.insert t).contains a = true := by
  unfold insert
  split
  · simp
  · rename_i hsat
    simp only [Bool.not_eq_true] at hsat
    split
    · rename_i hb
      simp only [contains, Bool.false_or, decide_eq_true_eq]
      exact (mem_insertTag T.tags t a).mpr (Or.inr ((contains_iff_mem hsat a).mp h))
    · simp


/-- WS-SM SM9.D.1: **insertion leaves the value unsaturated exactly when it was
unsaturated and the result still fits** — the branch analysis every exactness
statement below reduces to. -/
theorem insert_not_saturated_iff (T : DeclassificationTaint) (t : Nat) :
    (T.insert t).saturated = false ↔
      (T.saturated = false ∧ (insertTag T.tags t).length ≤ maxTaintTags) := by
  unfold insert
  cases hsat : T.saturated with
  | true => simp [top]
  | false =>
    simp only [Bool.false_eq_true, if_false, true_and]
    split
    · rename_i hb; simp [hb]
    · rename_i hb; simp [hb, top]

/-- WS-SM SM9.D.1: the tags of an unsaturated insertion. -/
theorem insert_tags_of_not_saturated {T : DeclassificationTaint} {t : Nat}
    (hOut : (T.insert t).saturated = false) :
    (T.insert t).tags = insertTag T.tags t := by
  obtain ⟨hsat, hb⟩ := (insert_not_saturated_iff T t).mp hOut
  unfold insert
  simp [hsat, hb]

/-- WS-SM SM9.D.1: insertion adds **only** the identity asked for, whenever it
does not saturate — the exactness half of `contains_insert_of_contains`, and
what keeps the taint from over-approximating except through saturation. -/
theorem contains_insert_iff_of_not_saturated {T : DeclassificationTaint} {t a : Nat}
    (hOut : (T.insert t).saturated = false) :
    (T.insert t).contains a = true ↔ (a = t ∨ T.contains a = true) := by
  obtain ⟨hsat, _⟩ := (insert_not_saturated_iff T t).mp hOut
  rw [contains_iff_mem hOut, insert_tags_of_not_saturated hOut, mem_insertTag,
    contains_iff_mem hsat]

-- ============================================================================
-- §3  WS-SM SM9.D.1 — join, the propagation primitive
-- ============================================================================

/-- WS-SM SM9.D.1: **join** — the union, saturating on overflow.

A saturated right operand gives `top` outright (`a ⊔ ⊤ = ⊤`); otherwise the
right operand's identities are inserted into the left one at a time, so the
result is `top` exactly when the union does not fit.

Deliberately **not** short-circuited on a saturated *left* operand: `insert`
already collapses one to `top`, and short-circuiting would make
`join a empty = a` false for a saturated `a` whose tag list the API never
produces but a `SystemState` frame could still be carrying. -/
def join (a b : DeclassificationTaint) : DeclassificationTaint :=
  if b.saturated then top
  else b.tags.foldl (fun acc t => acc.insert t) a

/-- WS-SM SM9.D.1: joining the empty taint in changes nothing — the identity
law, and the reason a propagation site whose source is untainted is a no-op. -/
@[simp] theorem join_empty (a : DeclassificationTaint) : join a empty = a := by
  simp [join, empty]

/-- WS-SM SM9.D.1: joining anything into the top stays at the top. -/
@[simp] theorem join_top_right (a : DeclassificationTaint) : join a top = top := by
  simp [join, top]

/-- WS-SM SM9.D.1: **saturation is absorbing along the fold.** -/
private theorem foldl_saturated_of_saturated (l : List Nat) :
    ∀ acc : DeclassificationTaint, acc.saturated = true →
      (l.foldl (fun s t => s.insert t) acc).saturated = true := by
  induction l with
  | nil => intro acc h; simpa using h
  | cons x xs ih =>
    intro acc h
    simp only [List.foldl_cons]
    exact ih (acc.insert x) (by rw [insert_saturated h]; rfl)

/-- WS-SM SM9.D.1: **the fold never forgets what the accumulator held.** -/
theorem contains_foldl_insert_of_contains (l : List Nat) :
    ∀ (acc : DeclassificationTaint) {a : Nat}, acc.contains a = true →
      (l.foldl (fun s t => s.insert t) acc).contains a = true := by
  induction l with
  | nil => intro acc a h; simpa using h
  | cons x xs ih =>
    intro acc a h
    simp only [List.foldl_cons]
    exact ih (acc.insert x) (contains_insert_of_contains h x)

/-- WS-SM SM9.D.1: **the fold records every identity it is given.** -/
theorem contains_foldl_insert_of_mem (l : List Nat) :
    ∀ (acc : DeclassificationTaint) {a : Nat}, a ∈ l →
      (l.foldl (fun s t => s.insert t) acc).contains a = true := by
  induction l with
  | nil => intro acc a h; exact absurd h (by simp)
  | cons x xs ih =>
    intro acc a h
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact contains_foldl_insert_of_contains xs (acc.insert a) (contains_insert_self acc a)
    · exact ih (acc.insert x) hmem

/-- WS-SM SM9.D.1: **the fold introduces nothing else** — whenever it does not
saturate, every identity in the result came from the accumulator or from the
list.  The exactness direction; saturation is the only source of the extra
identities `taintSaturate_over_approximates` exhibits. -/
private theorem foldl_contains_subset (l : List Nat) :
    ∀ (acc : DeclassificationTaint),
      (l.foldl (fun s t => s.insert t) acc).saturated = false →
      ∀ {a : Nat}, (l.foldl (fun s t => s.insert t) acc).contains a = true →
        acc.contains a = true ∨ a ∈ l := by
  induction l with
  | nil => intro acc _ a h; exact Or.inl (by simpa using h)
  | cons x xs ih =>
    intro acc hsat a h
    simp only [List.foldl_cons] at hsat h
    have hInsSat : (acc.insert x).saturated = false := by
      cases hc : (acc.insert x).saturated with
      | false => rfl
      | true =>
        exact absurd (foldl_saturated_of_saturated xs (acc.insert x) hc)
          (by rw [hsat]; simp)
    rcases ih (acc.insert x) hsat h with hStep | hMem
    · rcases (contains_insert_iff_of_not_saturated (T := acc) (t := x) (a := a) hInsSat).mp hStep
        with rfl | hAcc
      · exact Or.inr (by simp)
      · exact Or.inl hAcc
    · exact Or.inr (List.mem_cons.mpr (Or.inr hMem))

/-- WS-SM SM9.D.1: **join keeps the left operand's identities.** -/
theorem contains_join_of_left {a b : DeclassificationTaint} {t : Nat}
    (h : a.contains t = true) : (join a b).contains t = true := by
  unfold join
  split
  · simp
  · exact contains_foldl_insert_of_contains b.tags a h

/-- WS-SM SM9.D.1: **join keeps the right operand's identities** — the half the
propagation sites consume, since a sink joins its source's taint in. -/
theorem contains_join_of_right {a b : DeclassificationTaint} {t : Nat}
    (h : b.contains t = true) : (join a b).contains t = true := by
  unfold join
  cases hsat : b.saturated with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact contains_foldl_insert_of_mem b.tags a ((contains_iff_mem hsat t).mp h)

/-- WS-SM SM9.D.1 (**the union property**): a join carries every identity either
operand carried.  The direction every propagation theorem reads. -/
theorem contains_join_of_or {a b : DeclassificationTaint} {t : Nat}
    (h : a.contains t = true ∨ b.contains t = true) : (join a b).contains t = true := by
  rcases h with h | h
  · exact contains_join_of_left h
  · exact contains_join_of_right h

/-- WS-SM SM9.D.1 (**exactness**): an unsaturated join carries **exactly** the
union.  Together with `contains_join_of_or` this pins the join as the least
upper bound wherever the bound is not reached — so the residual imprecision the
detector inherits is saturation and nothing else, which is what
`staleTaint_is_not_saturation` and `taintSaturate_over_approximates` between
them keep on the record. -/
theorem contains_join_iff_of_not_saturated {a b : DeclassificationTaint} {t : Nat}
    (hOut : (join a b).saturated = false) :
    (join a b).contains t = true ↔ (a.contains t = true ∨ b.contains t = true) := by
  constructor
  · intro hc
    unfold join at hc hOut
    cases hsat : b.saturated with
    | true => rw [hsat] at hOut; simp [top] at hOut
    | false =>
      rw [hsat] at hc hOut
      simp only [Bool.false_eq_true, if_false] at hc hOut
      rcases foldl_contains_subset b.tags a hOut hc with hAcc | hMem
      · exact Or.inl hAcc
      · exact Or.inr ((contains_iff_mem hsat t).mpr hMem)
  · exact contains_join_of_or

-- ============================================================================
-- §4  WS-SM SM9.D.1 — the order, and the semilattice laws
-- ============================================================================

/-- WS-SM SM9.D.1: **`a` is at least as tainted as `b`** — decidable, because a
detector has to compute it.

Sound as an implication about `contains` (`covers_sound`), which is the
direction every consumer needs.  Not stated as `∀ t, b.contains t → a.contains t`
because that quantifier ranges over an unbounded `Nat` and is not decidable in
the shape a checker can run. -/
def covers (a b : DeclassificationTaint) : Bool :=
  (!b.saturated || a.saturated) && b.tags.all (fun t => a.contains t)

/-- WS-SM SM9.D.1: **`covers` is sound** — it really does imply containment at
every identity. -/
theorem covers_sound {a b : DeclassificationTaint} (h : covers a b = true) {t : Nat}
    (hb : b.contains t = true) : a.contains t = true := by
  simp only [covers, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hSat, hAll⟩ := h
  cases hbsat : b.saturated with
  | true =>
    rcases hSat with hc | hc
    · exact absurd hbsat (by rw [hc]; simp)
    · exact contains_of_saturated hc t
  | false =>
    have hmem : t ∈ b.tags := (contains_iff_mem hbsat t).mp hb
    simpa using (List.all_eq_true.mp hAll t hmem)

/-- WS-SM SM9.D.1: reflexivity of the order. -/
@[simp] theorem covers_refl (a : DeclassificationTaint) : covers a a = true := by
  simp only [covers, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨by cases a.saturated <;> simp, ?_⟩
  refine List.all_eq_true.mpr (fun t ht => ?_)
  simp only [contains]
  simp [ht]

/-- WS-SM SM9.D.1: transitivity of the order. -/
theorem covers_trans {a b c : DeclassificationTaint}
    (hab : covers a b = true) (hbc : covers b c = true) : covers a c = true := by
  simp only [covers, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · cases hcsat : c.saturated with
    | false => exact Or.inl rfl
    | true =>
      have hb : b.saturated = true := by
        simp only [covers, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hbc
        rcases hbc.1 with h | h
        · exact absurd hcsat (by rw [h]; simp)
        · exact h
      have ha : a.saturated = true := by
        simp only [covers, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hab
        rcases hab.1 with h | h
        · exact absurd hb (by rw [h]; simp)
        · exact h
      exact Or.inr ha
  · refine List.all_eq_true.mpr (fun t ht => ?_)
    have hc : c.contains t = true := by simp only [contains]; simp [ht]
    exact covers_sound hab (covers_sound hbc hc)

/-- WS-SM SM9.D.1: the top covers everything. -/
@[simp] theorem covers_top (a : DeclassificationTaint) : covers top a = true := by
  simp only [covers, top, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  exact ⟨Or.inr trivial, List.all_eq_true.mpr (fun t _ => by simp [contains])⟩

/-- WS-SM SM9.D.1: everything covers the empty taint. -/
@[simp] theorem covers_empty (a : DeclassificationTaint) : covers a empty = true := by
  simp [covers, empty]

/-- WS-SM SM9.D.1: **saturation on the left survives the join** — the fold
inserts into a saturated accumulator, and `insert` collapses that to `top`. -/
theorem join_saturated_of_left {a : DeclassificationTaint} (h : a.saturated = true)
    (b : DeclassificationTaint) : (join a b).saturated = true := by
  unfold join
  cases hbsat : b.saturated with
  | true => simp [top]
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact foldl_saturated_of_saturated b.tags a h

/-- WS-SM SM9.D.1: **join is an upper bound of its left operand.** -/
theorem covers_join_left (a b : DeclassificationTaint) : covers (join a b) a = true := by
  simp only [covers, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨?_, List.all_eq_true.mpr (fun t ht =>
    contains_join_of_left (by simp only [contains]; simp [ht]))⟩
  cases hasat : a.saturated with
  | false => exact Or.inl rfl
  | true => exact Or.inr (join_saturated_of_left hasat b)

/-- WS-SM SM9.D.1: **join is an upper bound of its right operand.** -/
theorem covers_join_right (a b : DeclassificationTaint) : covers (join a b) b = true := by
  simp only [covers, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · cases hbsat : b.saturated with
    | false => exact Or.inl rfl
    | true => exact Or.inr (by simp [join, hbsat, top])
  · exact List.all_eq_true.mpr (fun t ht =>
      contains_join_of_right (by simp only [contains]; simp [ht]))

/-- WS-SM SM9.D.1 / SM9.D.13: **join is the least upper bound** — for a target
that is itself saturated, or for a join that is not.

The disjunctive hypothesis is the honest statement of what is machine-checked
here.  The one case it leaves out — an *unsaturated* `c` covering both operands
of a *saturating* join — is unreachable: covering both operands puts every
identity of the union into `c.tags`, and the join saturates only when that union
exceeds `maxTaintTags`, which is `c.tags`'s own bound.  That pigeonhole step is
deliberately not proven, because the toolchain's core library carries no
nodup-subset length lemma and nothing downstream consumes the missing case: the
semilattice results below all supply one disjunct directly.

So `(DeclassificationTaint, covers, join)` is a join-semilattice up to
`taintEquiv`, with `top` an absorbing element above it — the SM9.D.13 saturation
policy restated at the algebra rather than at the detector. -/
theorem covers_join_of_covers {c a b : DeclassificationTaint}
    (hCase : c.saturated = true ∨ (join a b).saturated = false)
    (ha : covers c a = true) (hb : covers c b = true) : covers c (join a b) = true := by
  rcases hCase with hc | hOut
  · simp only [covers, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    exact ⟨Or.inr hc, List.all_eq_true.mpr (fun t _ => contains_of_saturated hc t)⟩
  · simp only [covers, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    refine ⟨Or.inl hOut, List.all_eq_true.mpr (fun t ht => ?_)⟩
    have hjt : (join a b).contains t = true := by simp only [contains]; simp [ht]
    rcases (contains_join_iff_of_not_saturated (a := a) (b := b) (t := t) hOut).mp hjt with h | h
    · exact covers_sound ha h
    · exact covers_sound hb h

-- ============================================================================
-- §5  WS-SM SM9.D.13 — saturation, and the direction it errs in
-- ============================================================================

/-- WS-SM SM9.D.1: the taint carrying exactly one identity — what a
declassification originates on the objects its released content reaches. -/
def singleton (t : Nat) : DeclassificationTaint := empty.insert t

/-- WS-SM SM9.D.1: a singleton carries its identity. -/
@[simp] theorem contains_singleton_self (t : Nat) : (singleton t).contains t = true :=
  contains_insert_self empty t

/-- WS-SM SM9.D.1: a singleton carries nothing else — `maxTaintTags` is positive,
so the single insertion never saturates. -/
@[simp] theorem contains_singleton_iff (t a : Nat) :
    (singleton t).contains a = true ↔ a = t := by
  have hOut : (singleton t).saturated = false := by
    simp [singleton, insert, empty, insertTag, maxTaintTags]
  rw [singleton, contains_insert_iff_of_not_saturated hOut]
  simp

/-- WS-SM SM9.D.1: the taint accumulated from a list of identities — used by the
propagation planners and by the fixtures, so the two build a taint the same
way. -/
def ofList (l : List Nat) : DeclassificationTaint :=
  l.foldl (fun acc t => acc.insert t) empty

/-- WS-SM SM9.D.1: `ofList` records every identity it is given. -/
theorem contains_ofList_of_mem {l : List Nat} {t : Nat} (h : t ∈ l) :
    (ofList l).contains t = true :=
  contains_foldl_insert_of_mem l empty h

/-- WS-SM SM9.D.1: **the structural bound**, restated as a public fact about the
type rather than as a field access.

This is what §6 of the plan means by "bounded by its type": it holds of *every*
value, including one a frame lemma carried across an unrelated transition, so no
writer owes a capacity obligation and the mounted table needs no
`proofLayerInvariantBundle` conjunct. -/
theorem taint_bounded_structurally (T : DeclassificationTaint) :
    T.tags.length ≤ maxTaintTags := T.tags_bounded

/-- WS-SM SM9.D.13 (**the safe direction, as a theorem**): saturation
over-approximates — a saturated taint reports identities neither operand
carried, and never drops one either operand did.

For a *detector* that is the sound direction: the residual imprecision is extra
laundering reports, never a missed chain.  It would be the unsafe direction for
an enforcement gate, which is why nothing enforces on taint.

The witness is the smallest one the bound admits: `maxTaintTags` identities
joined with one more overflows, and the result reports an identity — `99` here —
that no operand ever held. -/
theorem taintSaturate_over_approximates :
    ∃ (a b : DeclassificationTaint) (t : Nat),
      a.contains t = false ∧ b.contains t = false ∧ (join a b).contains t = true := by
  refine ⟨ofList [0, 1, 2, 3, 4, 5, 6, 7], singleton 8, 99, by decide, by decide, by decide⟩

/-- WS-SM SM9.D.13: **a saturated join is still an upper bound** — `top` covers
everything, so saturation costs precision and never soundness.  The companion
of `taintSaturate_over_approximates`: that one exhibits the extra identities,
this one records that no identity is lost with them. -/
theorem join_saturated_covers_all {a b : DeclassificationTaint}
    (h : (join a b).saturated = true) (c : DeclassificationTaint) :
    covers (join a b) c = true := by
  simp only [covers, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  exact ⟨Or.inr h, List.all_eq_true.mpr (fun t _ => contains_of_saturated h t)⟩

/-- WS-SM SM9.D.1: **mutual coverage** — the equivalence the semilattice laws
are stated up to.  Two taints that cover each other agree on every identity
(`taintEquiv_contains`), which is all any consumer reads. -/
def taintEquiv (a b : DeclassificationTaint) : Bool := covers a b && covers b a

/-- WS-SM SM9.D.1: equivalent taints agree on every identity. -/
theorem taintEquiv_contains {a b : DeclassificationTaint} (h : taintEquiv a b = true)
    (t : Nat) : a.contains t = b.contains t := by
  simp only [taintEquiv, Bool.and_eq_true] at h
  cases hb : b.contains t with
  | true => simp [covers_sound h.1 hb]
  | false =>
    cases ha : a.contains t with
    | true => exact absurd (covers_sound h.2 ha) (by simp [hb])
    | false => rfl

/-- WS-SM SM9.D.1: `taintEquiv` is reflexive. -/
@[simp] theorem taintEquiv_refl (a : DeclassificationTaint) : taintEquiv a a = true := by
  simp [taintEquiv]

/-- WS-SM SM9.D.1: `taintEquiv` is symmetric. -/
theorem taintEquiv_symm {a b : DeclassificationTaint} (h : taintEquiv a b = true) :
    taintEquiv b a = true := by
  simp only [taintEquiv, Bool.and_eq_true] at h ⊢
  exact ⟨h.2, h.1⟩

/-- WS-SM SM9.D.1: `taintEquiv` is transitive. -/
theorem taintEquiv_trans {a b c : DeclassificationTaint}
    (hab : taintEquiv a b = true) (hbc : taintEquiv b c = true) : taintEquiv a c = true := by
  simp only [taintEquiv, Bool.and_eq_true] at hab hbc ⊢
  exact ⟨covers_trans hab.1 hbc.1, covers_trans hbc.2 hab.2⟩

/-- WS-SM SM9.D.1 (**commutativity, up to the order**): the two join orders
carry the same identities whenever neither saturates.

Stated up to `taintEquiv` rather than as an equality because the value-level
statement would need a sorted-list extensionality result the toolchain's core
library does not carry.  `insertTag` keeps the representation canonical, so the
two *are* the same value in practice; what is proven here is the property every
consumer reads. -/
theorem join_comm_equiv {a b : DeclassificationTaint}
    (hab : (join a b).saturated = false) (hba : (join b a).saturated = false) :
    taintEquiv (join a b) (join b a) = true := by
  simp only [taintEquiv, Bool.and_eq_true]
  exact ⟨covers_join_of_covers (Or.inr hba) (covers_join_right a b) (covers_join_left a b),
         covers_join_of_covers (Or.inr hab) (covers_join_right b a) (covers_join_left b a)⟩

/-- WS-SM SM9.D.1 (**commutativity's saturated half**): when both joins
saturate, each is a top and they cover each other — three lines from
`join_saturated_covers_all`.  With `join_comm_equiv` this leaves exactly one
case unstated: one join saturated, the other not.  That case is in fact
unreachable — a saturated operand saturates both orders, and fold overflow is
a property of the operands' *union*, which does not see the order — but
stating it needs a fold-symmetry induction this algebra does not otherwise
owe, so the coverage is recorded here rather than implied complete. -/
theorem join_comm_equiv_of_saturated {a b : DeclassificationTaint}
    (hab : (join a b).saturated = true) (hba : (join b a).saturated = true) :
    taintEquiv (join a b) (join b a) = true := by
  simp only [taintEquiv, Bool.and_eq_true]
  exact ⟨join_saturated_covers_all hab _, join_saturated_covers_all hba _⟩

/-- WS-SM SM9.D.1 (**idempotence, up to the order**). -/
theorem join_idem_equiv {a : DeclassificationTaint} (h : (join a a).saturated = false) :
    taintEquiv (join a a) a = true := by
  simp only [taintEquiv, Bool.and_eq_true]
  exact ⟨covers_join_left a a, covers_join_of_covers (Or.inr h) (covers_refl a) (covers_refl a)⟩

/-- WS-SM SM9.D.1 (**associativity, up to the order**). -/
theorem join_assoc_equiv {a b c : DeclassificationTaint}
    (hL : (join (join a b) c).saturated = false) (hR : (join a (join b c)).saturated = false)
    (hab : (join a b).saturated = false) (hbc : (join b c).saturated = false) :
    taintEquiv (join (join a b) c) (join a (join b c)) = true := by
  simp only [taintEquiv, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · exact covers_join_of_covers (Or.inr hR)
      (covers_trans (covers_join_left (join a b) c) (covers_join_left a b))
      (covers_join_of_covers (Or.inr hbc)
        (covers_trans (covers_join_left (join a b) c) (covers_join_right a b))
        (covers_join_right (join a b) c))
  · exact covers_join_of_covers (Or.inr hL)
      (covers_join_of_covers (Or.inr hab)
        (covers_join_left a (join b c))
        (covers_trans (covers_join_right a (join b c)) (covers_join_left b c)))
      (covers_trans (covers_join_right a (join b c)) (covers_join_right b c))

end DeclassificationTaint

-- ============================================================================
-- §6  WS-SM SM9.D.2 — the side table
-- ============================================================================

/-- WS-SM SM9.D.2: **the declassification taint side table** — provenance for
every object id.

A **total function** rather than an `RHTable`, and the choice is load-bearing
rather than stylistic.  `RHTable`'s lookup-after-insert lemmas
(`RHTable.getElem?_insert_self`, `_insert_ne`) take `invExt` as a hypothesis, so
a hash-table representation would have to carry that well-formedness as an
invariant — a seventeenth `proofLayerInvariantBundle` conjunct plus a capacity
obligation at every writer, which is exactly what §6 of the plan decides against
for all three SM9 mounts.  A total function has no well-formedness to carry, so
the frames are `rfl` and the bound that matters — the number of identities *per
object* — stays where it belongs, in `DeclassificationTaint.tags_bounded`.

The representation is precedented in this codebase for exactly this reason:
`Machine.Memory` is `PAddr → UInt8` and `RegisterFile.gpr` is
`RegName → RegValue`, both with the same recorded rationale (proofs stay total,
and a concrete implementation is a refinement concern rather than a model one). -/
abbrev TaintTable := SeLe4n.ObjId → DeclassificationTaint

namespace TaintTable

/-- WS-SM SM9.D.2: no object carries provenance — the boot table. -/
def empty : TaintTable := fun _ => DeclassificationTaint.empty

instance : Inhabited TaintTable := ⟨empty⟩

/-- WS-SM SM9.D.2: replace one object's provenance. -/
def set (tbl : TaintTable) (oid : SeLe4n.ObjId) (T : DeclassificationTaint) : TaintTable :=
  fun o => if o = oid then T else tbl o

/-- WS-SM SM9.D.2: **add provenance to one object**, keeping what it had — the
propagation primitive.  A sink joins its source's taint in; nothing is ever
replaced, so a propagation step cannot lose a causal link.

**Value-preserving writes are elided.**  The table is a function, so each `set`
closes over the previous one and a lookup walks the chain; joining an empty
source into an untainted sink — which is what *every* edge of ordinary untainted
IPC does — would otherwise extend that chain on the syscall hot path forever,
making later reads progressively slower and retaining unbounded closure history
for no semantic gain.  The guard returns the table itself when the join changes
nothing, so a write survives only when it actually moves the value.  It is
observationally invisible (`joinAt_self`/`joinAt_ne` below are unchanged, and
`joinAt_eq_of_join_eq` states the elided case), because the branch it takes is
exactly the case where the two tables are already pointwise equal. -/
def joinAt (tbl : TaintTable) (oid : SeLe4n.ObjId) (T : DeclassificationTaint) : TaintTable :=
  let joined := DeclassificationTaint.join (tbl oid) T
  if joined = tbl oid then tbl else tbl.set oid joined

/-- WS-SM SM9.D.12: **forget one object's provenance** — what a retype owes,
and the only operation in this module that removes a causal link.

Retype commits `storeObject target newObj` at the *same* id, so a framed retype
would leave a destroyed object's tags on its unrelated replacement — a false
positive with nothing to do with saturation, which is why
`staleTaint_is_not_saturation` keeps the two apart. -/
def clearAt (tbl : TaintTable) (oid : SeLe4n.ObjId) : TaintTable :=
  tbl.set oid DeclassificationTaint.empty

@[simp] theorem empty_apply (oid : SeLe4n.ObjId) : empty oid = DeclassificationTaint.empty := rfl

@[simp] theorem set_self (tbl : TaintTable) (oid : SeLe4n.ObjId) (T : DeclassificationTaint) :
    tbl.set oid T oid = T := by simp [set]

@[simp] theorem set_ne (tbl : TaintTable) {oid o : SeLe4n.ObjId} (h : o ≠ oid)
    (T : DeclassificationTaint) : tbl.set oid T o = tbl o := by simp [set, h]

@[simp] theorem joinAt_self (tbl : TaintTable) (oid : SeLe4n.ObjId) (T : DeclassificationTaint) :
    tbl.joinAt oid T oid = DeclassificationTaint.join (tbl oid) T := by
  unfold joinAt
  split
  · next hEq => exact hEq.symm
  · simp

@[simp] theorem joinAt_ne (tbl : TaintTable) {oid o : SeLe4n.ObjId} (h : o ≠ oid)
    (T : DeclassificationTaint) : tbl.joinAt oid T o = tbl o := by
  unfold joinAt
  split
  · rfl
  · simp [h]

/-- WS-SM SM9.D.2 (**the elision is invisible**): when the join changes nothing
the table is returned unchanged, which is pointwise the same table the
unconditional `set` would have produced.  The property that lets the hot-path
guard exist without any theorem about `joinAt` having to know it is there. -/
theorem joinAt_eq_of_join_eq (tbl : TaintTable) (oid : SeLe4n.ObjId)
    (T : DeclassificationTaint) (h : DeclassificationTaint.join (tbl oid) T = tbl oid) :
    tbl.joinAt oid T = tbl := by
  unfold joinAt
  simp [h]

@[simp] theorem clearAt_self (tbl : TaintTable) (oid : SeLe4n.ObjId) :
    tbl.clearAt oid oid = DeclassificationTaint.empty := by simp [clearAt]

@[simp] theorem clearAt_ne (tbl : TaintTable) {oid o : SeLe4n.ObjId} (h : o ≠ oid) :
    tbl.clearAt oid o = tbl o := by simp [clearAt, h]

/-- WS-SM SM9.D.2: **joining never forgets** — the table-level no-loss property,
lifted from `DeclassificationTaint.contains_join_of_left`. -/
theorem contains_joinAt_of_contains (tbl : TaintTable) (oid o : SeLe4n.ObjId)
    (T : DeclassificationTaint) {t : Nat} (h : (tbl o).contains t = true) :
    ((tbl.joinAt oid T) o).contains t = true := by
  by_cases hEq : o = oid
  · subst hEq; simp only [joinAt_self]; exact DeclassificationTaint.contains_join_of_left h
  · simpa [joinAt_ne tbl hEq] using h

/-- WS-SM SM9.D.2: **joining records the source's identities at the sink** — the
half every propagation theorem consumes. -/
theorem contains_joinAt_of_source (tbl : TaintTable) (oid : SeLe4n.ObjId)
    (T : DeclassificationTaint) {t : Nat} (h : T.contains t = true) :
    ((tbl.joinAt oid T) oid).contains t = true := by
  simp only [joinAt_self]; exact DeclassificationTaint.contains_join_of_right h

/-- WS-SM SM9.D.12: **a cleared object carries nothing** — the property
`retypedObject_taint_empty` is stated over. -/
@[simp] theorem contains_clearAt_self (tbl : TaintTable) (oid : SeLe4n.ObjId) (t : Nat) :
    ((tbl.clearAt oid) oid).contains t = false := by
  simp only [clearAt_self]; exact DeclassificationTaint.contains_empty t

end TaintTable

end SeLe4n.Kernel
