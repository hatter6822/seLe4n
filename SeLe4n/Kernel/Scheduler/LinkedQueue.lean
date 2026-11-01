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
# Doubly linked thread queues over link functions

WS-ZA ZA4.5: the run queue keeps its threads in doubly linked lists whose links
are stored per thread (`RunQueue.links`) and whose ends are stored per queue, so
that enqueue, dequeue and rotation rewrite a few scalar words in place and never
build a list cell.  This module is the representation-independent part: a list
`l` *is* the queue a pair of link functions `nx`/`pv` and a pair of end codes
describe (`IsQueue`), and the two edits the run queue performs — appending a
thread and unlinking one — are proven to produce the queue of `l ++ [y]` and of
`l` without the thread, given only what the edit wrote at each member.

A link is a thread code (`code t = t.val + 1`, `0` for none), the encoding
`ThreadId.optCode` uses, so a link field is a scalar.
-/

namespace SeLe4n.Kernel.LinkedQueue

open SeLe4n

/-- The scalar code of a thread: `ThreadId.optCode (some t)`. -/
@[inline] def code (t : ThreadId) : Nat := t.val + 1

theorem code_ne_zero (t : ThreadId) : code t ≠ 0 := Nat.succ_ne_zero _

theorem code_inj {a b : ThreadId} (h : code a = code b) : a = b := by
  cases a; cases b; simp only [code] at h; congr; omega

/-- The thread a nonzero code stands for. -/
@[inline] def decode (c : Nat) : ThreadId := ⟨c - 1⟩

@[simp] theorem decode_code (t : ThreadId) : decode (code t) = t := by
  cases t; simp [decode, code]

/-- The code of `l`'s last element, `pre` when `l` is empty. -/
def lastCode (pre : Nat) (l : List ThreadId) : Nat := l.foldl (fun _ x => code x) pre

@[simp] theorem lastCode_nil (pre : Nat) : lastCode pre [] = pre := rfl

@[simp] theorem lastCode_cons (pre : Nat) (x : ThreadId) (l : List ThreadId) :
    lastCode pre (x :: l) = lastCode (code x) l := rfl

theorem lastCode_append (pre : Nat) (A B : List ThreadId) :
    lastCode pre (A ++ B) = lastCode (lastCode pre A) B := by
  simp [lastCode, List.foldl_append]

@[simp] theorem lastCode_append_single (pre : Nat) (A : List ThreadId) (y : ThreadId) :
    lastCode pre (A ++ [y]) = code y := by
  rw [lastCode_append]; rfl

/-- `lastCode` is `pre` or the code of a member. -/
theorem lastCode_cases (pre : Nat) (l : List ThreadId) :
    lastCode pre l = pre ∨ ∃ x ∈ l, lastCode pre l = code x := by
  induction l generalizing pre with
  | nil => exact Or.inl rfl
  | cons x r ih =>
    rcases ih (code x) with h | ⟨z, hz, h⟩
    · exact Or.inr ⟨x, List.mem_cons_self .., h⟩
    · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, h⟩

/-- Each element of `l` names its predecessor through `f`; the first names
`pre`.  Read over `l` it is the backward links, over `l.reverse` the forward
ones. -/
def Linked (f : ThreadId → Nat) : Nat → List ThreadId → Prop
  | _, [] => True
  | pre, x :: r => f x = pre ∧ Linked f (code x) r

@[simp] theorem linked_nil (f : ThreadId → Nat) (pre : Nat) : Linked f pre [] := trivial

@[simp] theorem linked_cons (f : ThreadId → Nat) (pre : Nat) (x : ThreadId) (r : List ThreadId) :
    Linked f pre (x :: r) ↔ f x = pre ∧ Linked f (code x) r := Iff.rfl

theorem linked_append (f : ThreadId → Nat) (pre : Nat) (A B : List ThreadId) :
    Linked f pre (A ++ B) ↔ Linked f pre A ∧ Linked f (lastCode pre A) B := by
  induction A generalizing pre with
  | nil => simp
  | cons x r ih => simp only [List.cons_append, linked_cons, ih, lastCode_cons, and_assoc]

/-- **A member's link names its list's predecessor or another member**: what
a reader of one link learns of the thread it names. -/
theorem linked_mem {f : ThreadId → Nat} {pre : Nat} {l : List ThreadId} (h : Linked f pre l)
    {x : ThreadId} (hx : x ∈ l) : f x = pre ∨ ∃ z ∈ l, f x = code z := by
  induction l generalizing pre with
  | nil => cases hx
  | cons y r ih =>
    obtain ⟨hy, hr⟩ := h
    rcases List.mem_cons.mp hx with e | hm
    · subst e; exact .inl hy
    · rcases ih hr hm with e | ⟨z, hz, ez⟩
      · exact .inr ⟨y, List.mem_cons_self .., e⟩
      · exact .inr ⟨z, List.mem_cons_of_mem _ hz, ez⟩

/-- `Linked` reads `f` only at the members. -/
theorem linked_congr {f g : ThreadId → Nat} {pre : Nat} {l : List ThreadId}
    (h : ∀ x ∈ l, f x = g x) : Linked f pre l ↔ Linked g pre l := by
  induction l generalizing pre with
  | nil => simp
  | cons x r ih =>
    simp only [linked_cons, h x (List.mem_cons_self ..),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem lastCode_eq_zero_iff (l : List ThreadId) : lastCode 0 l = 0 ↔ l = [] := by
  constructor
  · intro h
    rcases lastCode_cases 0 l with h0 | ⟨x, _, hx⟩
    · cases l with
      | nil => rfl
      | cons y r =>
        rcases lastCode_cases (code y) r with h1 | ⟨z, _, hz⟩
        · simp only [lastCode_cons, h1] at h; exact absurd h (code_ne_zero y)
        · simp only [lastCode_cons] at h; rw [hz] at h; exact absurd h (code_ne_zero z)
    · rw [hx] at h; exact absurd h (code_ne_zero x)
  · rintro rfl; rfl

/-- On a nonempty list `lastCode` does not read its default. -/
theorem lastCode_of_ne_nil {l : List ThreadId} (h : l ≠ []) (a b : Nat) :
    lastCode a l = lastCode b l := by
  cases l with
  | nil => exact absurd rfl h
  | cons x r => rfl

/-- `l` is the queue whose forward links are `nx`, whose backward links are
`pv`, whose first element has code `head` and whose last has code `tail` (both
`0` for the empty queue). -/
def IsQueue (nx pv : ThreadId → Nat) (head tail : Nat) (l : List ThreadId) : Prop :=
  head = lastCode 0 l.reverse ∧ tail = lastCode 0 l ∧ Linked pv 0 l ∧ Linked nx 0 l.reverse

theorem isQueue_nil (nx pv : ThreadId → Nat) : IsQueue nx pv 0 0 [] := by
  simp [IsQueue]

theorem isQueue_congr {nx pv nx' pv' : ThreadId → Nat} {head tail : Nat} {l : List ThreadId}
    (hnx : ∀ x ∈ l, nx' x = nx x) (hpv : ∀ x ∈ l, pv' x = pv x) :
    IsQueue nx' pv' head tail l ↔ IsQueue nx pv head tail l := by
  unfold IsQueue
  rw [linked_congr hpv, linked_congr (fun x hx => hnx x (List.mem_reverse.mp hx))]

/-- Appending `y` to the queue `l`: `y` points back at the old tail and forward
at nothing, the old tail points forward at `y`, and every other member keeps
its links. -/
theorem isQueue_append {nx pv nx' pv' : ThreadId → Nat} {head tail : Nat}
    {l : List ThreadId} {y : ThreadId}
    (hq : IsQueue nx pv head tail l) (hnd : l.Nodup)
    (hnx : ∀ x ∈ l, nx' x = if code x = tail then code y else nx x) (hnxy : nx' y = 0)
    (hpv : ∀ x ∈ l, pv' x = pv x) (hpvy : pv' y = tail) :
    IsQueue nx' pv' (if tail = 0 then code y else head) (code y) (l ++ [y]) := by
  obtain ⟨hH, hT, hP, hN⟩ := hq
  refine ⟨?_, by simp, ?_, ?_⟩
  · rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · simp [hT]
    · have hne : tail ≠ 0 := by rw [hT]; simp [List.concat_eq_append]; exact code_ne_zero b
      rw [if_neg hne, hH]
      simp only [List.concat_eq_append, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, lastCode_cons]
  · rw [linked_append, linked_congr hpv]
    exact ⟨hP, by simp [hpvy, hT]⟩
  · simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, linked_cons, hnxy, true_and]
    rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · simp
    · simp only [List.concat_eq_append] at hN hnx hnd hT ⊢
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, linked_cons] at hN ⊢
      simp only [lastCode_append_single] at hT
      refine ⟨by rw [hnx b (by simp), if_pos hT.symm], ?_⟩
      rw [linked_congr (g := nx)]
      · exact hN.2
      · intro x hx
        have hxL : x ∈ L := List.mem_reverse.mp hx
        rw [hnx x (List.mem_append_left _ hxL), if_neg]
        intro hc
        have hxb : x = b := code_inj (hc.trans hT)
        have := (List.nodup_append.mp hnd).2.2 x hxL b (by simp)
        exact this hxb

/-- Unlinking `x` from the chain `A ++ x :: B` along one direction: the members
of `A` keep their links and the first member of `B` takes over `x`'s. -/
theorem linked_unlink {f f' : ThreadId → Nat} {pre : Nat} {A B : List ThreadId} {x : ThreadId}
    (h : Linked f pre (A ++ x :: B)) (hA : ∀ z ∈ A, f' z = f z)
    (hB : ∀ b B', B = b :: B' → f' b = f x ∧ ∀ z ∈ B', f' z = f z) :
    Linked f' pre (A ++ B) := by
  rw [linked_append] at h ⊢
  obtain ⟨hLA, hx, hLB⟩ := h
  refine ⟨(linked_congr hA).mpr hLA, ?_⟩
  cases B with
  | nil => trivial
  | cons b B' =>
    obtain ⟨hb, hB'⟩ := hB b B' rfl
    obtain ⟨_, hLB'⟩ := hLB
    exact ⟨hb.trans hx, (linked_congr hB').mpr hLB'⟩

/-- The link `x` holds in one direction is the code of its neighbour there. -/
theorem linked_mid {f : ThreadId → Nat} {pre : Nat} {A B : List ThreadId} {x : ThreadId}
    (h : Linked f pre (A ++ x :: B)) : f x = lastCode pre A := by
  rw [linked_append] at h; exact h.2.1

/-- A member of a duplicate-free list other than its last element does not
carry the list's last code. -/
theorem code_ne_lastCode {A : List ThreadId} {z : ThreadId} (hnd : A.Nodup)
    (hz : z ∈ A) (hzl : z ≠ A.getLast?.getD z) : code z ≠ lastCode 0 A := by
  rcases List.eq_nil_or_concat A with rfl | ⟨A0, a, rfl⟩
  · simp at hz
  · simp only [List.concat_eq_append, lastCode_append_single, List.getLast?_append,
      List.getLast?_singleton, Option.some_or, Option.getD_some] at hzl ⊢
    intro hc; exact hzl (code_inj hc)

/-- Unlinking `x` from the queue `A ++ x :: B`: its predecessor takes over its
forward link, its successor its backward link, an end it occupied passes to its
neighbour, and every other member keeps its links. -/
theorem isQueue_unlink {nx pv nx' pv' : ThreadId → Nat} {head tail : Nat}
    {A B : List ThreadId} {x : ThreadId}
    (hq : IsQueue nx pv head tail (A ++ x :: B)) (hnd : (A ++ x :: B).Nodup)
    (hnx : ∀ z ∈ A ++ B, nx' z = if code z = pv x then nx x else nx z)
    (hpv : ∀ z ∈ A ++ B, pv' z = if code z = nx x then pv x else pv z) :
    IsQueue nx' pv' (if pv x = 0 then nx x else head) (if nx x = 0 then pv x else tail)
      (A ++ B) := by
  obtain ⟨hH, hT, hP, hN⟩ := hq
  have hpvx : pv x = lastCode 0 A := linked_mid hP
  have hNr : Linked nx 0 (B.reverse ++ x :: A.reverse) := by
    simpa [List.reverse_append] using hN
  have hnxx : nx x = lastCode 0 B.reverse := linked_mid hNr
  obtain ⟨hndA, hndxB, hAxB⟩ := List.nodup_append.mp hnd
  obtain ⟨hxB, hndB⟩ := List.nodup_cons.mp hndxB
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a ≠ b := fun a ha b hb => hAxB a ha b (List.mem_cons_of_mem _ hb)
  have F1 : ∀ z ∈ B, code z ≠ pv x := by
    intro z hz hc
    rw [hpvx] at hc
    rcases lastCode_cases 0 A with h0 | ⟨a, ha, h⟩
    · rw [h0] at hc; exact code_ne_zero z hc
    · rw [h] at hc; exact hAB a ha z hz (code_inj hc).symm
  have F2 : ∀ z ∈ A, code z ≠ nx x := by
    intro z hz hc
    rw [hnxx] at hc
    rcases lastCode_cases 0 B.reverse with h0 | ⟨b, hb, h⟩
    · rw [h0] at hc; exact code_ne_zero z hc
    · rw [h] at hc; exact hAB z hz b (List.mem_reverse.mp hb) (code_inj hc)
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hA0 : pv x = 0
    · rw [if_pos hA0]
      rw [hpvx, lastCode_eq_zero_iff] at hA0; subst hA0
      simpa using hnxx
    · rw [if_neg hA0, hH]
      have hAne : A ≠ [] := fun h => hA0 (by rw [hpvx, h]; rfl)
      have hArne : A.reverse ≠ [] := by simpa using hAne
      simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append,
        lastCode_append, lastCode_cons]
      exact lastCode_of_ne_nil hArne _ _
  · by_cases hB0 : nx x = 0
    · rw [if_pos hB0]
      rw [hnxx, lastCode_eq_zero_iff, List.reverse_eq_nil_iff] at hB0; subst hB0
      simpa using hpvx
    · rw [if_neg hB0, hT]
      have hBne : B ≠ [] := fun h => hB0 (by rw [hnxx, h]; rfl)
      simp only [lastCode_append, lastCode_cons]
      exact lastCode_of_ne_nil hBne _ _
  · refine linked_unlink hP (fun z hz => ?_) ?_
    · rw [hpv z (List.mem_append_left _ hz), if_neg (F2 z hz)]
    · rintro b B' rfl
      · have hcb : code b = nx x := by rw [hnxx]; simp
        refine ⟨by rw [hpv b (by simp), if_pos hcb], fun z hz => ?_⟩
        rw [hpv z (List.mem_append_right _ (List.mem_cons_of_mem _ hz)), if_neg]
        intro hc
        exact (List.nodup_cons.mp hndB).1 (code_inj (hc.trans hcb.symm) ▸ hz)
  · rw [List.reverse_append]
    refine linked_unlink hNr (fun z hz => ?_) ?_
    · have hzB := List.mem_reverse.mp hz
      rw [hnx z (List.mem_append_right _ hzB), if_neg (F1 z hzB)]
    · rcases List.eq_nil_or_concat A with rfl | ⟨A0, a, rfl⟩
      · intro b B' h; simp at h
      · simp only [List.concat_eq_append, List.reverse_append, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.singleton_append, List.cons.injEq]
        rintro b B' ⟨rfl, rfl⟩
        have hca : code a = pv x := by rw [hpvx]; simp [List.concat_eq_append]
        refine ⟨by rw [hnx a (by simp [List.concat_eq_append]), if_pos hca], fun z hz => ?_⟩
        have hzA0 := List.mem_reverse.mp hz
        rw [hnx z (List.mem_append_left _ (by simp [List.concat_eq_append, hzA0])), if_neg]
        intro hc
        have hza : z = a := code_inj (hc.trans hca.symm)
        simp only [List.concat_eq_append] at hndA
        exact (List.nodup_append.mp hndA).2.2 z hzA0 a (by simp) hza

/-- The threads read from code `c` forward along `nx`, at most `fuel` of them;
reading stops at a `0` link. -/
def walk (nx : ThreadId → Nat) : Nat → Nat → List ThreadId
  | 0, _ => []
  | _ + 1, 0 => []
  | n + 1, c + 1 => ⟨c⟩ :: walk nx n (nx ⟨c⟩)

@[simp] theorem walk_zero_code (nx : ThreadId → Nat) (n : Nat) : walk nx n 0 = [] := by
  cases n <;> rfl

theorem walk_succ_code (nx : ThreadId → Nat) (n : Nat) (x : ThreadId) :
    walk nx (n + 1) (code x) = x :: walk nx n (nx x) := rfl

/-- Reading a queue from its head with at least as much fuel as it has members
gives the queue. -/
theorem walk_of_linked {nx : ThreadId → Nat} :
    ∀ (l : List ThreadId) (n : Nat), Linked nx 0 l.reverse → l.length ≤ n →
      walk nx n (lastCode 0 l.reverse) = l
  | [], n, _, _ => by simp
  | x :: r, n, h, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp only [List.reverse_cons] at h ⊢
    rw [linked_append] at h
    rw [lastCode_append_single, walk_succ_code, h.2.1]
    exact congrArg _ (walk_of_linked r m h.1 (by simp at hn; omega))

theorem IsQueue.walk_eq {nx pv : ThreadId → Nat} {head tail : Nat} {l : List ThreadId}
    (hq : IsQueue nx pv head tail l) {n : Nat} (hn : l.length ≤ n) : walk nx n head = l := by
  rw [hq.1]; exact walk_of_linked l n hq.2.2.2 hn

theorem IsQueue.head_eq_zero_iff {nx pv : ThreadId → Nat} {head tail : Nat} {l : List ThreadId}
    (hq : IsQueue nx pv head tail l) : head = 0 ↔ l = [] := by
  rw [hq.1, lastCode_eq_zero_iff, List.reverse_eq_nil_iff]

theorem IsQueue.tail_eq_zero_iff {nx pv : ThreadId → Nat} {head tail : Nat} {l : List ThreadId}
    (hq : IsQueue nx pv head tail l) : tail = 0 ↔ l = [] := by
  rw [hq.2.1, lastCode_eq_zero_iff]

end SeLe4n.Kernel.LinkedQueue
