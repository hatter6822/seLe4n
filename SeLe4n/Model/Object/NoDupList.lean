-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude

/-! # `NoDupList α` — structural smart-constructor wrapper around `List α`

WS-RC R4.C (DEEP-IPC-05; subsumes DEEP-IPC-01): wrapper structure carrying
`List.Nodup` at construction time. The smart constructors discharge the
invariant; the runtime-checked `consWithGuard?` constructor folds the
runtime duplicate-guard responsibility into the type system itself, so a
caller cannot insert a duplicate without explicitly handling the `none`
result.

`Notification.waitingThreads` (in `SeLe4n.Model.Object.Types`) carries
this wrapper around `List SeLe4n.ThreadId`. The state-level invariant
`SeLe4n.Kernel.uniqueWaiters` is now trivially derivable via
`SeLe4n.Kernel.uniqueWaiters_holds` from the structural `hNodup` field —
no preservation theorem is required for the wrapper's no-duplicate
property since it cannot be violated at construction.

## Operational vs. proof-side API

* Operational sites (kernel transitions) use `consWithGuard?` (runtime
  membership check returning `Option`) at cons sites,
  `tail?` (NoDupList smart accessor) at pop sites, `filter` for
  multi-element removal, and `empty` for boot/initial state. The
  smart constructors discharge `Nodup` inline.
* Proof sites (preservation theorems) destructure `.val` to recover the
  underlying `List α` for pattern-matching tactics, or use the bridge
  lemmas `tail?_eq_{none,some}_iff` and `consWithGuard?_eq_{none,some}_iff`
  to align the operational match shapes with `.val`-based reasoning.
  The proof-carrying `consWithGuard` is reserved for future proof
  sites that have a non-membership witness in scope from another
  cross-subsystem invariant.

The operational↔proof bridge for the runtime guard is the existing
in-tree theorem `notificationWait_runtime_check_implied_by_nodup`
(in `IPC/Invariant/QueueNoDup.lean`), which proves that the
TCB-state-based duplicate guard at `Endpoint.lean` implies the
structural Nodup precondition under `notificationWaiterConsistent`.
-/

namespace SeLe4n

/-- WS-RC R4.C: wrapper around `List α` carrying `List.Nodup` invariantly.

    Every smart constructor in this namespace discharges the obligation via
    inline Nodup-preserving arguments, so the structural property cannot be
    regressed by future refactors without breaking Lean elaboration. The
    underlying list is the value held in field `val`; the discharge witness
    is held in field `hNodup`. -/
structure NoDupList (α : Type) [DecidableEq α] where
  val    : List α
  hNodup : val.Nodup

namespace NoDupList

variable {α : Type} [DecidableEq α]

/-! ## Smart constructors -/

/-- The empty list trivially satisfies `Nodup`. -/
@[inline] def empty : NoDupList α := ⟨[], List.nodup_nil⟩

/-- Proof-carrying cons: prepend an element with an explicit
    non-membership witness. Used at proof sites under
    `notificationWaiterConsistent`, where
    `not_mem_waitingThreads_of_ipcState_ne` (`IPC/Invariant/Defs.lean`)
    supplies `h`. -/
@[inline] def consWithGuard (x : α) (l : NoDupList α) (h : x ∉ l.val) :
    NoDupList α :=
  ⟨x :: l.val, List.nodup_cons.mpr ⟨h, l.hNodup⟩⟩

/-- Runtime-checked cons: returns `none` if the element is already present.

    This **subsumes** the line-723 runtime duplicate guard at
    `IPC/Operations/Endpoint.lean`: the typed smart constructor IS the
    duplicate guard. Callers translate the `none` branch into the
    appropriate kernel error (e.g., `.alreadyWaiting`).

    Uses `if h :` so the negative branch's `h : x ∉ l.val` discharges
    the Nodup obligation for the produced cons. -/
@[inline] def consWithGuard? (x : α) (l : NoDupList α) :
    Option (NoDupList α) :=
  if h : x ∈ l.val then
    none
  else
    some ⟨x :: l.val, List.nodup_cons.mpr ⟨h, l.hNodup⟩⟩

/-- Filter preserves Nodup unconditionally; proven inline since
    `List.Nodup.filter` is not in the v4.28.0 core library. -/
theorem nodup_filter {α : Type} (l : List α) (p : α → Bool) (h : l.Nodup) :
    (l.filter p).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rcases List.nodup_cons.mp h with ⟨hNotMem, hTNodup⟩
    rw [List.filter_cons]
    by_cases hp : p a = true
    · rw [if_pos hp]
      refine List.nodup_cons.mpr ⟨?_, ih hTNodup⟩
      intro hMem
      exact hNotMem (List.mem_filter.mp hMem).1
    · rw [if_neg hp]
      exact ih hTNodup

/-- Filter; preserves Nodup via `nodup_filter`. -/
@[inline] def filter (l : NoDupList α) (p : α → Bool) : NoDupList α :=
  ⟨l.val.filter p, nodup_filter l.val p l.hNodup⟩

/-- Pop the head; preserves Nodup unconditionally (the tail of a Nodup
    list is Nodup). Returns `none` for the empty list.

    The implementation extracts the head/tail via a non-dependent match on
    `.val.head?`/`.val.tail`, which avoids the dependent-equation form
    that makes inversion proofs awkward. The tail's Nodup discharge uses
    `List.nodup_cons.mp` after re-establishing the cons shape via the
    `val.head?` non-emptiness witness. -/
@[inline] def tail? (l : NoDupList α) : Option (α × NoDupList α) :=
  match hL : l.val with
  | []       => none
  | x :: xs  =>
      some (x, ⟨xs, by
        have : (x :: xs).Nodup := hL ▸ l.hNodup
        exact (List.nodup_cons.mp this).2⟩)

/-- Equation lemma: `tail?` on the empty case. -/
theorem tail?_nil_eq_none (l : NoDupList α) (h : l.val = []) :
    l.tail? = none := by
  unfold tail?
  -- The match reduces by rewriting; cleanly via `subst`.
  cases l with
  | mk lv lh =>
    cases h
    rfl

/-- Equation lemma: `tail?` on the cons case yields the structural pair. -/
theorem tail?_cons_eq_some (l : NoDupList α) (x : α) (xs : List α)
    (hx : xs.Nodup) (h : l.val = x :: xs) :
    l.tail? = some (x, ⟨xs, hx⟩) := by
  unfold tail?
  cases l with
  | mk lv lh =>
    cases h
    rfl

/-! ## Read-only accessors

These exist as explicit `@[inline]` wrappers so that dot-notation lookup
finds them in the `NoDupList` namespace before falling back through the
`CoeHead` instance to the underlying `List` namespace. Keeps elaboration
fast on the hot read-only paths. -/

@[inline] def length (l : NoDupList α) : Nat := l.val.length

@[inline] def head? (l : NoDupList α) : Option α := l.val.head?

@[inline] def isEmpty (l : NoDupList α) : Bool := l.val.isEmpty

@[inline] def contains (l : NoDupList α) [BEq α] (x : α) : Bool :=
  l.val.contains x

@[inline] def all (l : NoDupList α) (p : α → Bool) : Bool := l.val.all p

@[inline] def any (l : NoDupList α) (p : α → Bool) : Bool := l.val.any p

@[inline] def foldr {β : Type} (f : α → β → β) (init : β) (l : NoDupList α) :
    β := l.val.foldr f init

/-! ## Instances -/

instance : CoeHead (NoDupList α) (List α) where
  coe := NoDupList.val

instance : Inhabited (NoDupList α) := ⟨empty⟩

instance : Membership α (NoDupList α) where
  mem l x := x ∈ l.val

instance : DecidableEq (NoDupList α) := fun a b =>
  match decEq a.val b.val with
  | isTrue  h => isTrue (by cases a; cases b; cases h; rfl)
  | isFalse h => isFalse (fun heq => h (heq ▸ rfl))

instance [Repr α] : Repr (NoDupList α) where
  reprPrec l n := reprPrec l.val n

/-! ## Forwarding lemmas -/

@[simp] theorem val_empty : (empty : NoDupList α).val = [] := rfl

@[simp] theorem val_consWithGuard (x : α) (l : NoDupList α) (h : x ∉ l.val) :
    (consWithGuard x l h).val = x :: l.val := rfl

@[simp] theorem val_filter (l : NoDupList α) (p : α → Bool) :
    (l.filter p).val = l.val.filter p := rfl

@[simp] theorem mem_iff (x : α) (l : NoDupList α) : x ∈ l ↔ x ∈ l.val :=
  Iff.rfl

/-- Two `NoDupList α` values are equal iff their underlying lists are equal
    (Nodup is propositionally irrelevant). -/
@[simp] theorem eq_iff (a b : NoDupList α) : a = b ↔ a.val = b.val :=
  ⟨fun h => h ▸ rfl,
   fun h => by cases a; cases b; cases h; rfl⟩

/-! ## tail? bridge lemmas

These bridge between the operational `tail?` matching and the proof-side
`.val` cons/nil pattern matching, enabling preservation proofs to
structurally case-split on the underlying list while operational code
remains abstraction-preserving. -/

/-- `tail?` returns `none` iff the underlying list is empty. -/
theorem tail?_eq_none_iff (l : NoDupList α) :
    l.tail? = none ↔ l.val = [] := by
  refine ⟨?_, tail?_nil_eq_none l⟩
  intro h
  match hL : l.val, h with
  | [], _ => rfl
  | (a :: as), h' =>
    have hNdTail : as.Nodup := by
      have := l.hNodup; rw [hL] at this
      exact (List.nodup_cons.mp this).2
    have hTail := tail?_cons_eq_some l a as hNdTail hL
    rw [hTail] at h'
    cases h'

/-- `tail?` returns `some (head, tail)` iff the underlying list is
    `head :: tail.val`. -/
theorem tail?_eq_some_iff (l : NoDupList α) (head : α) (tail : NoDupList α) :
    l.tail? = some (head, tail) ↔ l.val = head :: tail.val := by
  constructor
  · intro h
    cases hL : l.val with
    | nil =>
      rw [tail?_nil_eq_none l hL] at h
      cases h
    | cons a as =>
      have hNdTail : as.Nodup := by
        have := l.hNodup; rw [hL] at this
        exact (List.nodup_cons.mp this).2
      have hT := tail?_cons_eq_some l a as hNdTail hL
      rw [hT] at h
      -- h : some (a, ⟨as, hNdTail⟩) = some (head, tail)
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hHead, hRest⟩ := h
      subst hHead
      have hT' : tail.val = as := by
        have := congrArg NoDupList.val hRest
        exact this.symm
      rw [hT']
  · intro hEq
    have hNd : tail.val.Nodup := tail.hNodup
    exact tail?_cons_eq_some l head tail.val hNd hEq

/-! ## Witness theorems for the WS-RC R4.C discharge index -/

/-- WS-RC R4.C: `consWithGuard?` returns `none` iff the element is a
    duplicate. The runtime-checked smart constructor is equivalent to
    the explicit membership test followed by `consWithGuard`. -/
theorem consWithGuard?_eq_none_iff (x : α) (l : NoDupList α) :
    consWithGuard? x l = none ↔ x ∈ l.val := by
  unfold consWithGuard?
  by_cases h : x ∈ l.val
  · simp [h]
  · simp [h]

/-- WS-RC R4.C: `consWithGuard?` returns `some` iff the element is not a
    duplicate. -/
theorem consWithGuard?_eq_some_iff (x : α) (l : NoDupList α)
    (l' : NoDupList α) :
    consWithGuard? x l = some l' ↔ x ∉ l.val ∧ l'.val = x :: l.val := by
  unfold consWithGuard?
  by_cases h : x ∈ l.val
  · simp [h]
  · simp [h]
    cases l' with
    | mk lv lh =>
      exact ⟨fun heq => heq.symm, fun heq => heq.symm⟩

/-- WS-RC R4.C structural witness: every `NoDupList α` has a `Nodup`
    underlying list by construction. The proof is `hNodup` itself, lifted
    to the discharge-index name so a future auditor can reach the closure
    by `#check`-ing this identifier alone. -/
theorem nodup_witness (l : NoDupList α) : l.val.Nodup := l.hNodup

end NoDupList
end SeLe4n

/-! ## WS-RC R4.C discharge-index marker

The `SeLe4n.NoDupList α` wrapper carries `List.Nodup` invariantly at
construction time.  `Notification.waitingThreads` has been migrated to
`SeLe4n.NoDupList SeLe4n.ThreadId` (R4.C LANDED — see
`docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §8.5), so the
state-level `uniqueWaiters` invariant is now a trivial projection of
`hNodup` via `SeLe4n.Kernel.uniqueWaiters_holds`. This marker theorem
exists so the tier-3 invariant-surface gate can locate the
structural-promotion foundation by name. -/
namespace SeLe4n.Kernel

theorem noDupList_module_ready : True := trivial
-- Cross-reference: docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md §3.D D.4

end SeLe4n.Kernel
