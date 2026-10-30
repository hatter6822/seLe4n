-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude

/-!
# Singly linked chains of scheduling contexts

WS-ZA ZA6.3: each core's release queue keeps its scheduling contexts in a
singly linked list whose links are stored in the contexts (`SchedContext.releaseNextCode`)
and whose head is stored per core, as seL4-MCS links its release queue through
the threads.  This module is the representation-independent part: a list `l`
*is* the chain a link function `nx` describes from a head code (`Chain`), and
the three edits the release queue performs — placing a context between two
members, unlinking a member, and dropping a prefix — are proven to give the
chain of the edited list, given only what the edit wrote at each member.

A link is a context code (`code s = s.val + 1`, `0` for none), so a link field
is a scalar.
-/

namespace SeLe4n.Kernel.ReleaseChain

open SeLe4n

/-- The scalar code of a scheduling context: `SchedContextId.optCode (some s)`. -/
@[inline] def code (s : SchedContextId) : Nat := s.val + 1

theorem code_ne_zero (s : SchedContextId) : code s ≠ 0 := Nat.succ_ne_zero _

/-- The context a nonzero code stands for. -/
@[inline] def decode (c : Nat) : SchedContextId := ⟨c - 1⟩

@[simp] theorem decode_code (s : SchedContextId) : decode (code s) = s := by
  cases s; simp [decode, code]

theorem code_inj {a b : SchedContextId} (h : code a = code b) : a = b := by
  simpa using congrArg decode h

theorem code_decode {c : Nat} (h : c ≠ 0) : code (decode c) = c := by
  simp only [code, decode]; omega

/-- The code of `l`'s first element, `e` when `l` is empty. -/
def firstCode (e : Nat) : List SchedContextId → Nat
  | [] => e
  | x :: _ => code x

@[simp] theorem firstCode_nil (e : Nat) : firstCode e [] = e := rfl
@[simp] theorem firstCode_cons (e : Nat) (x : SchedContextId) (r : List SchedContextId) :
    firstCode e (x :: r) = code x := rfl

/-- The code of `l`'s last element, `e` when `l` is empty. -/
def lastCode (e : Nat) (l : List SchedContextId) : Nat := l.foldl (fun _ x => code x) e

@[simp] theorem lastCode_nil (e : Nat) : lastCode e [] = e := rfl
@[simp] theorem lastCode_cons (e : Nat) (x : SchedContextId) (l : List SchedContextId) :
    lastCode e (x :: l) = lastCode (code x) l := rfl

theorem lastCode_append (e : Nat) (A B : List SchedContextId) :
    lastCode e (A ++ B) = lastCode (lastCode e A) B := by
  simp [lastCode, List.foldl_append]

@[simp] theorem lastCode_append_single (e : Nat) (A : List SchedContextId) (y : SchedContextId) :
    lastCode e (A ++ [y]) = code y := by
  rw [lastCode_append]; rfl

/-- **A segment**: reading from code `h` along `nx` meets `l`'s members in order
and then code `e`. -/
def Seg (nx : SchedContextId → Nat) : Nat → Nat → List SchedContextId → Prop
  | h, e, [] => h = e
  | h, e, x :: r => h = code x ∧ Seg nx (nx x) e r

@[simp] theorem seg_nil (nx : SchedContextId → Nat) (h e : Nat) : Seg nx h e [] ↔ h = e := Iff.rfl

@[simp] theorem seg_cons (nx : SchedContextId → Nat) (h e : Nat) (x : SchedContextId)
    (r : List SchedContextId) : Seg nx h e (x :: r) ↔ h = code x ∧ Seg nx (nx x) e r := Iff.rfl

/-- **A chain**: the segment that ends at no context. -/
abbrev Chain (nx : SchedContextId → Nat) (h : Nat) (l : List SchedContextId) : Prop :=
  Seg nx h 0 l

/-- A segment starts at its first member's code. -/
theorem Seg.head_eq {nx : SchedContextId → Nat} {h e : Nat} {l : List SchedContextId}
    (hs : Seg nx h e l) : h = firstCode e l := by
  cases l with
  | nil => exact hs
  | cons x r => exact hs.1

/-- `Seg` reads `nx` only at the members. -/
theorem Seg.congr {nx nx' : SchedContextId → Nat} {h e : Nat} {l : List SchedContextId}
    (hs : Seg nx h e l) (hEq : ∀ x ∈ l, nx' x = nx x) : Seg nx' h e l := by
  induction l generalizing h with
  | nil => exact hs
  | cons x r ih =>
    refine ⟨hs.1, ?_⟩
    rw [hEq x (List.mem_cons_self ..)]
    exact ih hs.2 (fun y hy => hEq y (List.mem_cons_of_mem _ hy))

/-- A segment of `A ++ B` is a segment of `A` to `B`'s first code and one of `B`. -/
theorem seg_append {nx : SchedContextId → Nat} {h e : Nat} {A B : List SchedContextId} :
    Seg nx h e (A ++ B) ↔ Seg nx h (firstCode e B) A ∧ Seg nx (firstCode e B) e B := by
  induction A generalizing h with
  | nil =>
    simp only [List.nil_append, seg_nil]
    constructor
    · intro hs; exact ⟨hs.head_eq, hs.head_eq ▸ hs⟩
    · rintro ⟨rfl, hs⟩; exact hs
  | cons x r ih =>
    simp only [List.cons_append, seg_cons]
    rw [ih]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

/-- A member's link names the code of its successor. -/
theorem Seg.next_eq {nx : SchedContextId → Nat} {h e : Nat} {A B : List SchedContextId}
    {x : SchedContextId} (hs : Seg nx h e (A ++ x :: B)) : nx x = firstCode e B := by
  have := (seg_append.mp hs).2
  exact this.2.head_eq

/-- A chain of `A ++ B` holds a chain of `B` from `B`'s first code: dropping a
prefix is moving the head. -/
theorem Chain.drop {nx : SchedContextId → Nat} {h : Nat} {A B : List SchedContextId}
    (hc : Chain nx h (A ++ B)) : Chain nx (firstCode 0 B) B :=
  (seg_append.mp hc).2

/-- **Retargeting a segment's end**: rewriting only the last member's link to
`e'` (and keeping every other member's) makes a segment to `e'`. -/
theorem Seg.retarget {nx nx' : SchedContextId → Nat} {h e e' : Nat} {A : List SchedContextId}
    (hs : Seg nx h e A) (hnd : A.Nodup)
    (hMid : ∀ x ∈ A, A.getLast? ≠ some x → nx' x = nx x)
    (hLast : ∀ z, A.getLast? = some z → nx' z = e') :
    Seg nx' (firstCode e' A) e' A := by
  induction A generalizing h with
  | nil => rfl
  | cons x r ih =>
    cases r with
    | nil =>
      refine ⟨rfl, ?_⟩
      exact hLast x rfl
    | cons y r' =>
      have hx : x ∉ y :: r' := (List.nodup_cons.mp hnd).1
      have hLx : (x :: y :: r').getLast? ≠ some x := by
        intro hl
        rw [List.getLast?_cons_cons] at hl
        exact hx (List.mem_of_getLast? hl)
      refine ⟨rfl, ?_⟩
      rw [hMid x (List.mem_cons_self ..) hLx]
      have hs2 := hs.2
      have hy : nx x = code y := hs2.1
      rw [hy]
      have := ih (h := nx x) hs2 (List.nodup_cons.mp hnd).2
        (fun z hz hzl => hMid z (List.mem_cons_of_mem _ hz) (by
          rw [List.getLast?_cons_cons]; exact hzl))
        (fun z hz => hLast z (by rw [List.getLast?_cons_cons]; exact hz))
      exact this

theorem lastCode_eq_getLast? (e : Nat) (A : List SchedContextId) :
    lastCode e A = match A.getLast? with | some z => code z | none => e := by
  induction A generalizing e with
  | nil => rfl
  | cons x r ih =>
    rw [lastCode_cons, ih]
    cases r with
    | nil => rfl
    | cons y r' =>
      rw [List.getLast?_cons_cons]
      cases hl : (y :: r').getLast? with
      | none => simp at hl
      | some z => rfl

theorem lastCode_zero_eq_zero_iff (A : List SchedContextId) : lastCode 0 A = 0 ↔ A = [] := by
  rw [lastCode_eq_getLast?]
  cases h : A.getLast? with
  | none => simp only [List.getLast?_eq_none_iff] at h; simp [h]
  | some z =>
    simp only [code_ne_zero, false_iff]
    intro hA; subst hA; cases h

/-- On a nonempty list `firstCode` does not read its default. -/
theorem firstCode_of_ne_nil {A : List SchedContextId} (h : A ≠ []) (a b : Nat) :
    firstCode a A = firstCode b A := by
  cases A with
  | nil => exact absurd rfl h
  | cons x r => rfl

/-- **Placing `y` between `A` and `B`**: `y` names `B`'s first code, `A`'s last
member names `y`, every other member keeps its link, and the head moves to `y`
exactly when `A` is empty. -/
theorem chain_insert {nx nx' : SchedContextId → Nat} {h : Nat} {A B : List SchedContextId}
    {y : SchedContextId} (hc : Chain nx h (A ++ B)) (hnd : (A ++ B).Nodup)
    (hMid : ∀ x ∈ A ++ B, A.getLast? ≠ some x → nx' x = nx x)
    (hLast : ∀ z, A.getLast? = some z → nx' z = code y)
    (hY : nx' y = firstCode 0 B) :
    Chain nx' (firstCode (code y) A) (A ++ y :: B) := by
  obtain ⟨hA, hB⟩ := seg_append.mp hc
  have hndA : A.Nodup := (List.nodup_append.mp hnd).1
  have hDisj : ∀ a ∈ A, ∀ b ∈ B, a ≠ b := fun a ha b hb => (List.nodup_append.mp hnd).2.2 a ha b hb
  refine seg_append.mpr ⟨?_, ?_⟩
  · exact hA.retarget hndA (fun x hx hxl => hMid x (List.mem_append_left _ hx) hxl) hLast
  · refine ⟨rfl, ?_⟩
    rw [hY]
    refine hB.congr fun x hx => hMid x (List.mem_append_right _ hx) ?_
    intro hl
    exact hDisj x (List.mem_of_getLast? hl) x hx rfl

/-- **Unlinking `x` from `A ++ x :: B`**: `A`'s last member takes over `x`'s
link, every other member keeps its own, and the head moves past `x` exactly
when `A` is empty. -/
theorem chain_unlink {nx nx' : SchedContextId → Nat} {h : Nat} {A B : List SchedContextId}
    {x : SchedContextId} (hc : Chain nx h (A ++ x :: B)) (hnd : (A ++ x :: B).Nodup)
    (hMid : ∀ z ∈ A ++ B, A.getLast? ≠ some z → nx' z = nx z)
    (hLast : ∀ z, A.getLast? = some z → nx' z = firstCode 0 B) :
    Chain nx' (firstCode (firstCode 0 B) A) (A ++ B) := by
  obtain ⟨hA, hXB⟩ := seg_append.mp hc
  have hB : Chain nx (nx x) B := hXB.2
  have hnx : nx x = firstCode 0 B := hB.head_eq
  rw [hnx] at hB
  have hndA : A.Nodup := (List.nodup_append.mp hnd).1
  have hDisj : ∀ a ∈ A, ∀ b ∈ x :: B, a ≠ b :=
    fun a ha b hb => (List.nodup_append.mp hnd).2.2 a ha b hb
  refine seg_append.mpr ⟨?_, ?_⟩
  · exact hA.retarget hndA (fun z hz hzl => hMid z (List.mem_append_left _ hz) hzl) hLast
  · refine hB.congr fun z hz => hMid z (List.mem_append_right _ hz) ?_
    intro hl
    exact hDisj z (List.mem_of_getLast? hl) z (List.mem_cons_of_mem _ hz) rfl

/-! ## Walks

Each walk reads from a head code along `nx`, at most `fuel` steps; the release
queue's count is the fuel, and with at least as much fuel as the chain has
members each walk reads the chain's list. -/

/-- The contexts read from code `h` forward along `nx`, at most `fuel` of them. -/
def walk (nx : SchedContextId → Nat) : Nat → Nat → List SchedContextId
  | 0, _ => []
  | f + 1, h => if h = 0 then [] else decode h :: walk nx f (nx (decode h))

theorem Chain.walk_eq {nx : SchedContextId → Nat} {h : Nat} {l : List SchedContextId}
    (hc : Chain nx h l) {f : Nat} (hf : l.length ≤ f) : walk nx f h = l := by
  induction l generalizing h f with
  | nil =>
    cases f with
    | zero => rfl
    | succ f => simp [walk, show h = 0 from hc]
  | cons x r ih =>
    cases f with
    | zero => simp at hf
    | succ f =>
      obtain ⟨rfl, hr⟩ := hc
      simp only [walk, code_ne_zero, if_false, decode_code]
      rw [ih hr (by simpa using hf)]

/-- The code of the member after which a context released at `t` is placed:
the last member, read from `h`, released no later than `t` (`p` when there is
none) — the place `ReplenishQueue.insertSorted` puts the entry. -/
def predBefore (nx : SchedContextId → Nat) (tm : SchedContextId → Nat) (t : Nat) :
    Nat → Nat → Nat → Nat
  | 0, p, _ => p
  | f + 1, p, h =>
    if h = 0 then p
    else if t < tm (decode h) then p else predBefore nx tm t f h (nx (decode h))

theorem Chain.predBefore_eq {nx : SchedContextId → Nat} {h : Nat} {l : List SchedContextId}
    (hc : Chain nx h l) (tm : SchedContextId → Nat) (t : Nat) {f : Nat} (hf : l.length ≤ f)
    (p : Nat) :
    predBefore nx tm t f p h = lastCode p (l.takeWhile fun x => !decide (t < tm x)) := by
  induction l generalizing h f p with
  | nil =>
    cases f with
    | zero => rfl
    | succ f => simp [predBefore, show h = 0 from hc]
  | cons x r ih =>
    cases f with
    | zero => simp at hf
    | succ f =>
      obtain ⟨rfl, hr⟩ := hc
      simp only [predBefore, code_ne_zero, if_false, decode_code, List.takeWhile_cons]
      by_cases ht : t < tm x
      · simp [ht]
      · simp only [ht, if_false, decide_false, Bool.not_false]
        exact ih hr (by simpa using hf) _

/-- The code of `s`'s predecessor read from `h` (`p` when `s` is the first). -/
def predOf (nx : SchedContextId → Nat) (s : SchedContextId) : Nat → Nat → Nat → Nat
  | 0, p, _ => p
  | f + 1, p, h =>
    if h = 0 then p else if decode h = s then p else predOf nx s f h (nx (decode h))

theorem Chain.predOf_eq {nx : SchedContextId → Nat} {h : Nat} {A B : List SchedContextId}
    {s : SchedContextId} (hc : Chain nx h (A ++ s :: B)) (hs : s ∉ A) {f : Nat}
    (hf : (A ++ s :: B).length ≤ f) (p : Nat) : predOf nx s f p h = lastCode p A := by
  induction A generalizing h f p with
  | nil =>
    cases f with
    | zero => simp at hf
    | succ f =>
      obtain ⟨rfl, -⟩ := hc
      simp [predOf, code_ne_zero]
  | cons x r ih =>
    cases f with
    | zero => simp at hf
    | succ f =>
      obtain ⟨rfl, hr⟩ := hc
      have hxs : x ≠ s := fun e => hs (e ▸ List.mem_cons_self ..)
      simp only [predOf, code_ne_zero, if_false, decode_code, hxs, lastCode_cons]
      exact ih hr (fun m => hs (List.mem_cons_of_mem _ m)) (by simpa using hf) _

end SeLe4n.Kernel.ReleaseChain
