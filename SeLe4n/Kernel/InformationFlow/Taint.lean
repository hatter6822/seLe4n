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
against the name.

Sized small for **internal** cost, and the earlier rationale here was wrong about
which cost: it said the tags are exported to a privileged monitor through SM9.A's
chunk protocol.  They are not, deliberately.  A tag is a global
`declassificationAuditEpoch`-relative identity, and exporting one would defeat the
view-local re-indexing the partially-cleared reader exists to enforce — so the
audit interface returns only opaque causality verdicts
(`AuditReadOp.chainNamesPredecessor` / `chainNamesEntry`), one bit per query,
never the tags themselves.

What the bound actually pays for is the snapshot and the lookup: every recorded
`DeclassificationEvent` carries a `predecessorTags` copy of the **acting
subject's** tag list, and every join walks both operands.  Eight is also where the
value stops adding information for a detector — a subject that has released
content behind eight distinct authorized downgrades is already a laundering
report's subject rather than one whose ninth tag changes the verdict.

The *subject's*, not the target's (PR #873 round 9 — this said "its target's").
`declassificationActorTaint` reads `actor.subject.toObjId` and that is what
`declassifyStoreEvent` records, which is the whole shape of the causal check: a
downgrade names an earlier one when the **actor** was already carrying that
identity.  The target is tagged separately, *after* the event is committed
(`originationTags`).  Reversing the two would let a reader conclude that
downgrading a tainted target records its provenance even when the acting subject
has none — the case the detector must not claim. -/
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

/-- WS-SM SM9.D.1 (PR #873 round 7): **strictly increasing above a floor.**

The auxiliary the canonical shape is defined through, because it is what makes
the insertion proof one line per branch: `tagsAbove b l` says every entry of `l`
is above `b` *and* above its predecessor, so the recursive call already carries
the bound the cons case needs. -/
def tagsAbove : Nat -> List Nat -> Prop
  | _, [] => True
  | b, a :: rest => b < a ∧ tagsAbove a rest

/-- WS-SM SM9.D.1 (PR #873 round 7): **the tag list's canonical shape** —
strictly increasing, which is sortedness and duplicate-freeness in one predicate.

Carried as a field below rather than left to the operations.  `tags_bounded` was
the only structural constraint, so the public constructor accepted any bounded
list: `⟨false, [5,5,5,5,5,5,5,5], _⟩` is eight tags of one identity, and
inserting a second *distinct* timestamp into it saturates the value to `top` —
which matches every later identity, so a laundering verdict could be manufactured
out of a value naming only two.  The field doc said "ordered and duplicate-free"
and nothing enforced it, which is the implicit-invariant shape CLAUDE.md requires
to be made structural. -/
def tagsCanonical : List Nat -> Prop
  | [] => True
  | a :: rest => tagsAbove a rest

/-- WS-SM SM9.D.1: **insertion preserves the floor.**

`insertTag` places the tag in order and drops an exact duplicate, so a list whose
every entry is above `b` still is after inserting a `t` that is itself above `b`.
Three branches, one line each — which is the whole reason `tagsAbove` exists
rather than reasoning about heads after the fact. -/
theorem insertTag_above :
    ∀ (l : List Nat) (b t : Nat), b < t -> tagsAbove b l -> tagsAbove b (insertTag l t)
  | [], _, _, hbt, _ => ⟨hbt, trivial⟩
  | x :: xs, b, t, hbt, h => by
      simp only [insertTag]
      split
      · next hlt => exact ⟨hbt, hlt, h.2⟩
      · split
        · exact h
        · next h₁ h₂ => exact ⟨h.1, insertTag_above xs x t (by omega) h.2⟩

/-- WS-SM SM9.D.1: **insertion preserves the canonical shape** — the fact the
type carries, so no value of `DeclassificationTaint` can hold a duplicate or an
out-of-order tag however it was built. -/
theorem insertTag_canonical :
    ∀ (l : List Nat) (t : Nat), tagsCanonical l -> tagsCanonical (insertTag l t)
  | [], _, _ => trivial
  | x :: xs, t, h => by
      simp only [insertTag]
      split
      · next hlt => exact ⟨hlt, h⟩
      · split
        · exact h
        · next h₁ h₂ => exact insertTag_above xs x t (by omega) h

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
      carries, ordered and duplicate-free — and that is a *field obligation*
      (`tags_canonical`), not a convention the operations happen to keep. -/
  tags : List Nat
  /-- WS-SM SM9.D.1: the structural bound.  A `Prop` field, so definitional
      proof irrelevance keeps it invisible to equality. -/
  tags_bounded : tags.length ≤ maxTaintTags
  /-- WS-SM SM9.D.1 (PR #873 round 7): the tags are strictly increasing, which
      is ordered *and* duplicate-free in one predicate.

      Bounded-ness alone left `⟨false, [5,5,5,5,5,5,5,5], _⟩` constructible —
      eight copies of one identity — and inserting a second distinct timestamp
      into that saturates the value to `top`, which matches every later identity.
      A causal verdict could then be manufactured from a value naming two.  Also
      a `Prop` field, so it stays invisible to equality. -/
  tags_canonical : tagsCanonical tags

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
def empty : DeclassificationTaint := ⟨false, [], by simp, trivial⟩

/-- WS-SM SM9.D.1: **tainted by everything** — the top of the order, and the
canonical saturated value.

Canonical deliberately: an operation that saturates drops the tags it was
carrying, so `saturated = true` and a non-empty `tags` list is not a shape the
API produces (`insert_saturated`, `join_saturated`). -/
def top : DeclassificationTaint := ⟨true, [], by simp, trivial⟩

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
      ⟨false, insertTag T.tags t, h, insertTag_canonical T.tags t T.tags_canonical⟩
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

/-- WS-SM SM9.D.2: the association list a `TaintTable` is, before the wrapper.

Kept **canonical**: no entry ever holds `DeclassificationTaint.empty`, so the
list's length is the number of objects that currently carry provenance rather
than a record of how many writes have happened.  `eraseKey` is what maintains
that, and it is why `clearAt` genuinely shrinks the table. -/
def TaintEntries := List (SeLe4n.ObjId × DeclassificationTaint)

/-- WS-SM SM9.D.2: the provenance recorded for `oid`, or none at all.

Defined by structural recursion rather than through `List.find?` so every lemma
below is a plain induction on the list, with no `find?`-over-`filter` reasoning
in the way. -/
def taintEntriesLookup : TaintEntries → SeLe4n.ObjId → DeclassificationTaint
  | [], _ => DeclassificationTaint.empty
  | (k, v) :: rest, o => if k = o then v else taintEntriesLookup rest o

/-- WS-SM SM9.D.2: drop every entry for `oid`.  Total, and removes duplicates as
well as the first hit, so the canonical form survives any construction. -/
def taintEntriesErase : TaintEntries → SeLe4n.ObjId → TaintEntries
  | [], _ => []
  | (k, v) :: rest, o =>
      if k = o then taintEntriesErase rest o else (k, v) :: taintEntriesErase rest o

@[simp] theorem taintEntriesLookup_erase_self (l : TaintEntries) (o : SeLe4n.ObjId) :
    taintEntriesLookup (taintEntriesErase l o) o = DeclassificationTaint.empty := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    by_cases h : k = o
    · simp [taintEntriesErase, h, ih]
    · simp [taintEntriesErase, taintEntriesLookup, h, ih]

@[simp] theorem taintEntriesLookup_erase_ne (l : TaintEntries) {o o' : SeLe4n.ObjId}
    (h : o' ≠ o) :
    taintEntriesLookup (taintEntriesErase l o) o' = taintEntriesLookup l o' := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = o
    · subst hk
      have hne : ¬ (k = o') := fun hc => h hc.symm
      simpa [taintEntriesErase, taintEntriesLookup, hne] using ih
    · by_cases hk' : k = o'
      · simp [taintEntriesErase, taintEntriesLookup, hk', h]
      · simpa [taintEntriesErase, taintEntriesLookup, hk, hk'] using ih

/-- WS-SM SM9.D.2: `o` has no entry in this list.

Structural recursion rather than `∀ p ∈ l, p.1 ≠ o`, for the same reason
`taintEntriesLookup` is: every lemma below is then a plain induction with no
membership reasoning in the way. -/
def TaintEntries.NoKey (o : SeLe4n.ObjId) : TaintEntries → Prop
  | [] => True
  | (k, _) :: rest => k ≠ o ∧ TaintEntries.NoKey o rest

/-- WS-SM SM9.D.2: **the canonical form** — at most one entry per object, and no
entry holding the empty taint.

This is the property the table's size claim rests on: with it, the list's length
*is* the number of objects currently carrying provenance rather than a record of
how many writes have happened.  It is a **field of `TaintTable`** rather than a
sentence in its docstring, because an invariant maintained only by convention is
one a later constructor breaks silently — and here the convention was doing real
work, since an unconstrained list admits duplicate and empty-valued rows that
reintroduce exactly the unbounded growth the keyed representation removed. -/
def TaintEntries.Canonical : TaintEntries → Prop
  | [] => True
  | (k, v) :: rest =>
      v ≠ DeclassificationTaint.empty ∧ TaintEntries.NoKey k rest ∧
        TaintEntries.Canonical rest

theorem TaintEntries.noKey_erase_self (o : SeLe4n.ObjId) :
    ∀ (l : TaintEntries), TaintEntries.NoKey o (taintEntriesErase l o) := by
  intro l
  induction l with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨k, _⟩ := p
    by_cases h : k = o
    · simpa [taintEntriesErase, h] using ih
    · simp only [taintEntriesErase, if_neg h]
      exact ⟨h, ih⟩

theorem TaintEntries.noKey_erase (o k : SeLe4n.ObjId) :
    ∀ (l : TaintEntries), TaintEntries.NoKey k l →
      TaintEntries.NoKey k (taintEntriesErase l o) := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons p rest ih =>
    obtain ⟨kk, _⟩ := p
    intro h
    by_cases hk : kk = o
    · simpa [taintEntriesErase, hk] using ih h.2
    · simp only [taintEntriesErase, if_neg hk]
      exact ⟨h.1, ih h.2⟩

theorem TaintEntries.canonical_erase (o : SeLe4n.ObjId) :
    ∀ (l : TaintEntries), TaintEntries.Canonical l →
      TaintEntries.Canonical (taintEntriesErase l o) := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons p rest ih =>
    obtain ⟨k, _⟩ := p
    intro h
    by_cases hk : k = o
    · simpa [taintEntriesErase, hk] using ih h.2.2
    · simp only [taintEntriesErase, if_neg hk]
      exact ⟨h.1, TaintEntries.noKey_erase o k rest h.2.1, ih h.2.2⟩

theorem TaintEntries.ne_of_noKey (k : SeLe4n.ObjId) :
    ∀ (l : List (SeLe4n.ObjId × DeclassificationTaint)), TaintEntries.NoKey k l →
      ∀ p ∈ l, p.1 ≠ k := by
  intro l
  induction l with
  | nil => intro _ p hp; cases hp
  | cons q rest ih =>
    obtain ⟨_, _⟩ := q
    intro h p hp
    cases hp with
    | head => exact h.1
    | tail _ hrest => exact ih h.2 p hrest

/-- WS-SM SM9.D.2: **every row of a canonical list is live** — the lookup returns
it, and it is not the empty taint.

This is what the canonicity field buys, stated so it cannot quietly stop being
true: no row is a duplicate shadowed by an earlier one, and none is an empty
value occupying space, so the list's length counts objects that currently carry
provenance.  Without the field this was a docstring sentence that any
`TaintTable.mk` could falsify without a single taint value changing. -/
theorem TaintEntries.live_of_canonical :
    ∀ (l : List (SeLe4n.ObjId × DeclassificationTaint)), TaintEntries.Canonical l →
      ∀ p ∈ l,
        taintEntriesLookup l p.1 = p.2 ∧ p.2 ≠ DeclassificationTaint.empty := by
  intro l
  induction l with
  | nil => intro _ p hp; cases hp
  | cons q rest ih =>
    obtain ⟨kk, v⟩ := q
    intro h p hp
    cases hp with
    | head => exact ⟨by simp [taintEntriesLookup], h.1⟩
    | tail _ hrest =>
      have hne : p.1 ≠ kk := TaintEntries.ne_of_noKey kk rest h.2.1 p hrest
      have hrec := ih h.2.2 p hrest
      refine ⟨?_, hrec.2⟩
      have hkk : ¬ (kk = p.1) := fun hc => hne hc.symm
      simpa [taintEntriesLookup, hkk] using hrec.1

/-- WS-SM SM9.D.2: **the declassification taint side table** — provenance for
every object id.

A **keyed** table under a total lookup, and both halves of that are
load-bearing.

*Keyed*, because the table is read and written by `applySyscallTaint` on the
live syscall path.  It was a bare `SeLe4n.ObjId → DeclassificationTaint`, and a
function representation records history rather than state: every value-changing
write closes over the previous table and a lookup walks the chain, so the
ordinary authorized cycle — a declassified badge stored, then consumed by
`.notificationWait`, then stored again — added two closures per cycle for ever.
Guards that elide value-*preserving* writes made the inert case free and left
that one untouched, because it is the case where the value really does change.
`Machine.Memory : PAddr → UInt8` was cited as precedent for the function form,
and that citation was the flaw in the argument: `Machine.Memory` is a
specification of hardware that is never executed, while this table is.

The association list is bounded by the number of objects that currently carry
provenance, not by the number of writes — `clearAt` erases rather than storing
an empty value, so a consumed transport leaves the table smaller than it found
it.

*Under a total lookup*, because the reason the function form was chosen still
holds: `RHTable`'s lookup-after-write lemmas take `invExt` (and `erase_ne` a
capacity bound) as hypotheses, so a hash-table representation would have to
carry that well-formedness — a seventeenth `proofLayerInvariantBundle` conjunct
plus an obligation at every writer, which §6 of the plan decides against for all
three SM9 mounts.  A list needs no such invariant, and the `CoeFun` below keeps
every downstream site reading `tbl oid` exactly as it did, so the pointwise
lemmas are unchanged in statement and the frames stay `rfl`. -/
structure TaintTable where
  /-- The entries: at most one per object, never empty-valued. -/
  entries : TaintEntries
  /-- ...and that is *carried*, not asserted.  `TaintTable.mk` cannot build a
  table with a duplicate or empty-valued row, so the length claim above holds of
  every value of this type rather than only of the ones the API happens to
  produce. -/
  canonical : TaintEntries.Canonical entries

namespace TaintTable

/-- WS-SM SM9.D.2: a table *is* its lookup, so every existing `tbl oid` reads
unchanged and no downstream statement moves. -/
instance : CoeFun TaintTable (fun _ => SeLe4n.ObjId → DeclassificationTaint) :=
  ⟨fun tbl => taintEntriesLookup tbl.entries⟩

/-- WS-SM SM9.D.2: **the size claim, carried rather than asserted.**

Every entry this table holds is one a lookup actually returns, and none of them
is empty — so `entries.length` is the number of objects currently carrying
provenance.  That is the claim the keyed representation was adopted for, and
until the `canonical` field existed it rested on the API happening not to build
a duplicate or empty-valued row. -/
theorem entries_live (tbl : TaintTable) :
    ∀ p ∈ show List (SeLe4n.ObjId × DeclassificationTaint) from tbl.entries,
      tbl p.1 = p.2 ∧ p.2 ≠ DeclassificationTaint.empty :=
  TaintEntries.live_of_canonical tbl.entries tbl.canonical

/-- WS-SM SM9.D.2: no object carries provenance — the boot table. -/
def empty : TaintTable := ⟨[], trivial⟩

instance : Inhabited TaintTable := ⟨empty⟩

/-- WS-SM SM9.D.2: replace one object's provenance.

Storing `DeclassificationTaint.empty` **erases** rather than recording an empty
entry, which is what keeps the representation canonical — and therefore what
makes `clearAt` shrink the table instead of extending it. -/
def set (tbl : TaintTable) (oid : SeLe4n.ObjId) (T : DeclassificationTaint) : TaintTable :=
  if h : T = DeclassificationTaint.empty then
    ⟨taintEntriesErase tbl.entries oid,
     TaintEntries.canonical_erase oid tbl.entries tbl.canonical⟩
  else
    ⟨(oid, T) :: taintEntriesErase tbl.entries oid,
     ⟨h, TaintEntries.noKey_erase_self oid tbl.entries,
      TaintEntries.canonical_erase oid tbl.entries tbl.canonical⟩⟩

/-- WS-SM SM9.D.2: **add provenance to one object**, keeping what it had — the
propagation primitive.  A sink joins its source's taint in; nothing is ever
replaced, so a propagation step cannot lose a causal link.

**Value-preserving writes are elided.**  The rationale is no longer the closure
chain a function representation would have grown — the table is a canonical
association list now, so `set` rebuilds entries rather than closing over a
previous table, and a lookup does not walk a write history.  What the guard saves
is the erase-and-reinsert the rebuild would otherwise perform: joining an empty
source into an untainted sink — which is what *every* edge of ordinary untainted
IPC does — would walk the entry list, drop the key and cons it back with a value
identical to the one removed, on the syscall hot path, for no semantic gain.  The
guard returns the table itself when the join changes nothing, so a write survives
only when it actually moves the value.  It is
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
`staleTaint_is_not_saturation` keeps the two apart.

**Value-preserving clears are elided**, for the reason `joinAt` elides
value-preserving joins and with more force: `contentFlowClears` empties the
transport on *every* `.notificationWait` and every direct-to-waiter signal, and
on ordinary untainted traffic that object's entry is already absent — so an
unguarded clear would walk the whole entry list looking for a key that is not
there, on the notification hot path, exactly where the content-derived model made
clears frequent.  The guard
returns the table itself when there is nothing to forget; `clearAt_eq_of_empty`
states that case, and `clearAt_self` / `clearAt_ne` are unchanged, because the
branch it takes is the one where the two tables are already pointwise equal. -/
def clearAt (tbl : TaintTable) (oid : SeLe4n.ObjId) : TaintTable :=
  if tbl oid = DeclassificationTaint.empty then tbl
  else tbl.set oid DeclassificationTaint.empty

@[simp] theorem empty_apply (oid : SeLe4n.ObjId) : empty oid = DeclassificationTaint.empty := rfl

@[simp] theorem set_self (tbl : TaintTable) (oid : SeLe4n.ObjId) (T : DeclassificationTaint) :
    tbl.set oid T oid = T := by
  unfold set
  split
  · next hT => simpa using hT.symm
  · simp [taintEntriesLookup]

@[simp] theorem set_ne (tbl : TaintTable) {oid o : SeLe4n.ObjId} (h : o ≠ oid)
    (T : DeclassificationTaint) : tbl.set oid T o = tbl o := by
  unfold set
  split
  · simp [taintEntriesLookup_erase_ne _ h]
  · simp [taintEntriesLookup, Ne.symm h, taintEntriesLookup_erase_ne _ h]

@[simp] theorem joinAt_self (tbl : TaintTable) (oid : SeLe4n.ObjId) (T : DeclassificationTaint) :
    tbl.joinAt oid T oid = DeclassificationTaint.join (tbl oid) T := by
  unfold joinAt
  -- The non-dependent `let` elaborates to `letFun`, which `split` cannot see
  -- through; `dsimp only` reduces it without touching anything else.
  dsimp only
  split
  · next hEq => exact hEq.symm
  · simp

@[simp] theorem joinAt_ne (tbl : TaintTable) {oid o : SeLe4n.ObjId} (h : o ≠ oid)
    (T : DeclassificationTaint) : tbl.joinAt oid T o = tbl o := by
  unfold joinAt
  dsimp only
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
    tbl.clearAt oid oid = DeclassificationTaint.empty := by
  unfold clearAt
  split
  · next hEmpty => exact hEmpty
  · simp

@[simp] theorem clearAt_ne (tbl : TaintTable) {oid o : SeLe4n.ObjId} (h : o ≠ oid) :
    tbl.clearAt oid o = tbl o := by
  unfold clearAt
  split
  · rfl
  · simp [h]

/-- WS-SM SM9.D.2 (**the clear elision is invisible**): an object that carries no
provenance is left literally alone, which is pointwise the same table the
unconditional `set` would have produced.  The `clearAt` counterpart of
`joinAt_eq_of_join_eq`, and what lets the hot-path guard exist without any
theorem about `clearAt` having to know it is there. -/
theorem clearAt_eq_of_empty (tbl : TaintTable) (oid : SeLe4n.ObjId)
    (h : tbl oid = DeclassificationTaint.empty) : tbl.clearAt oid = tbl := by
  unfold clearAt
  simp [h]

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

/-! ### WS-SM SM9.D.2 — the table is bounded by what it holds, not by its history

The reason the representation is keyed rather than functional.  A function-backed
table recorded every write, so the store/consume cycle ordinary authorized
notification traffic performs — a declassified badge stored, taken by
`.notificationWait`, stored again — grew it without bound and made lookups of
unrelated objects walk the whole history.  These three say that cannot happen
here: an erase never grows the list, it is idempotent, and therefore one full
cycle leaves the table no larger than it started. -/

theorem taintEntriesErase_length_le (l : TaintEntries) (o : SeLe4n.ObjId) :
    (taintEntriesErase l o).length ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = o
    · simp only [taintEntriesErase, if_pos hk, List.length_cons]
      exact Nat.le_succ_of_le ih
    · simp only [taintEntriesErase, if_neg hk, List.length_cons]
      exact Nat.succ_le_succ ih

theorem taintEntriesErase_idem (l : TaintEntries) (o : SeLe4n.ObjId) :
    taintEntriesErase (taintEntriesErase l o) o = taintEntriesErase l o := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = o
    · simp only [taintEntriesErase, if_pos hk]; exact ih
    · simp only [taintEntriesErase, if_neg hk]; rw [ih]

/-- **A store then a consume leaves exactly the erase.**

Computing the composition rather than bounding each half: both branches of `set`
collapse to the same list once the clear runs, because a clear at the key the
set just wrote removes what it wrote.  This is what makes the cycle bound tight
rather than off by the cons. -/
theorem clearAt_set_entries (tbl : TaintTable) (oid : SeLe4n.ObjId)
    (T : DeclassificationTaint) :
    ((tbl.set oid T).clearAt oid).entries = taintEntriesErase tbl.entries oid := by
  by_cases hT : T = DeclassificationTaint.empty
  · subst hT
    unfold clearAt
    rw [if_pos (set_self tbl oid DeclassificationTaint.empty)]
    simp [set]
  · unfold clearAt
    rw [if_neg (by rw [set_self]; exact hT)]
    have hentries : ((tbl.set oid T).set oid DeclassificationTaint.empty).entries
        = taintEntriesErase (taintEntriesErase tbl.entries oid) oid := by
      simp [set, hT, taintEntriesErase]
    rw [hentries]
    exact taintEntriesErase_idem _ _

/-- **A store-then-consume cycle leaves the table no larger.**

The property the functional representation could not have: `joinAt` then
`clearAt` at the same key is exactly the notification cycle — a declassified
badge stored, then taken by `.notificationWait` — and it returns a table bounded
by the one it started from rather than one two writes longer.

The bound is on *entries*, which is what a lookup walks, so an object's read cost
depends on how many objects currently carry provenance and never on how many
times any of them has been written. -/
theorem storeThenClear_no_growth (tbl : TaintTable) (oid : SeLe4n.ObjId)
    (T : DeclassificationTaint) :
    ((tbl.joinAt oid T).clearAt oid).entries.length ≤ tbl.entries.length := by
  unfold joinAt
  dsimp only
  split
  · -- The join changed nothing, so the cycle is just the clear.
    unfold clearAt
    split
    · exact Nat.le_refl _
    · simp only [set]
      exact taintEntriesErase_length_le _ _
  · rw [clearAt_set_entries]
    exact taintEntriesErase_length_le _ _

end TaintTable

end SeLe4n.Kernel
