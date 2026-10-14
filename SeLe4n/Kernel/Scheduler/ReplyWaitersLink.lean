-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.ReplyWaiters

/-!
# Linking a reply waiter, over views (WS-ZA ZA4.6)

A caller that becomes reply-blocked on a server joins the head of the server's
queue: its view names the server and links to the old head, the old head links
back to it, and the server's head and count move.  `consistent_link` proves the
queues stay consistent across exactly that change of views, whatever store
transition makes it.
-/

namespace SeLe4n.Model.ReplyViews

open SeLe4n

/-- A queue read through views that agree on its members is the same queue. -/
theorem chain_congr {V V' : ReplyViews} :
    ∀ {l : List ThreadId} {p c : Option ThreadId}, V.chain p c l →
      (∀ x ∈ l, V' x.toObjId = V x.toObjId) → V'.chain p c l
  | [], _, _, h, _ => h
  | x :: l, _, _, ⟨hc, v, hV, hP, hR⟩, hE => by
    refine ⟨hc, v, (hE x (List.mem_cons_self ..)).trans hV, hP, chain_congr hR ?_⟩
    exact fun y hy => hE y (List.mem_cons_of_mem _ hy)

/-- The members of a consistent queue are waiters of its server. -/
theorem queue_waiter {V : ReplyViews} {s : ThreadId} {vs : ReplyView} {l : List ThreadId}
    (hQ : V.queue s vs l) {x : ThreadId} (hx : x ∈ l) : V.waiterOf x s := (hQ.2.2.2 x).mp hx

/-- A thread whose view names no server is in no queue. -/
theorem not_mem_queue_of_server_none {V : ReplyViews} {s : ThreadId} {vs : ReplyView}
    {l : List ThreadId} (hQ : V.queue s vs l) {x : ThreadId} {vx : ReplyView}
    (hX : V x.toObjId = some vx) (hN : vx.server = none) : x ∉ l := fun hx => by
  obtain ⟨v, hV, hB⟩ := queue_waiter hQ hx
  rw [hX] at hV; cases hV; rw [hN] at hB; cases hB

/-- A thread reply-blocked on another server is not in this one's queue. -/
theorem not_mem_queue_of_server_ne {V : ReplyViews} {s : ThreadId} {vs : ReplyView}
    {l : List ThreadId} (hQ : V.queue s vs l) {x s' : ThreadId} {vx : ReplyView}
    (hX : V x.toObjId = some vx) (hS : vx.server = some s') (hne : s' ≠ s) : x ∉ l := fun hx => by
  obtain ⟨v, hV, hB⟩ := queue_waiter hQ hx
  rw [hX] at hV; cases hV; rw [hS] at hB; exact hne (Option.some.inj hB)

/-- The views a link leaves: `w` joins `s`'s queue at its head. -/
structure LinkStep (V0 V : ReplyViews) (w s : ThreadId) (vw0 vs0 : ReplyView) : Prop where
  hW0 : V0 w.toObjId = some vw0
  hWn : vw0.server = none
  hS0 : V0 s.toObjId = some vs0
  hSn : vs0.server = none
  hne : w ≠ s
  hW : V w.toObjId = some { vw0 with server := some s, prevCode := 0, nextCode := vs0.headCode }
  hS : V s.toObjId = some { vs0 with headCode := ThreadId.optCode (some w), count := vs0.count + 1 }
  hH : ∀ x, ThreadId.ofOptCode vs0.headCode = some x → ∃ vx, V0 x.toObjId = some vx ∧
    V x.toObjId = some { vx with prevCode := ThreadId.optCode (some w) }
  hO : ∀ y : ThreadId, y ≠ w → y ≠ s → ThreadId.ofOptCode vs0.headCode ≠ some y →
    V y.toObjId = V0 y.toObjId

namespace LinkStep

variable {V0 V : ReplyViews} {w s : ThreadId} {vw0 vs0 : ReplyView}

/-- Off `w`, a slot holds a view after the link exactly when it did before, and
the server, the successor, and (off `s`) the head and count are unchanged. -/
theorem off_w (L : LinkStep V0 V w s vw0 vs0) {y : ThreadId} (hy : y ≠ w) :
    (V y.toObjId = none ↔ V0 y.toObjId = none) ∧
    ∀ v v0, V y.toObjId = some v → V0 y.toObjId = some v0 →
      v.server = v0.server ∧ v.nextCode = v0.nextCode ∧
      (y ≠ s → v.headCode = v0.headCode ∧ v.count = v0.count) ∧
      (ThreadId.ofOptCode vs0.headCode ≠ some y → v.prevCode = v0.prevCode) := by
  by_cases hys : y = s
  · subst hys
    refine ⟨by rw [L.hS, L.hS0]; simp, fun v v0 hv hv0 => ?_⟩
    rw [L.hS] at hv; rw [L.hS0] at hv0; cases hv; cases hv0
    exact ⟨rfl, rfl, fun h => absurd rfl h, fun _ => rfl⟩
  by_cases hyh : ThreadId.ofOptCode vs0.headCode = some y
  · obtain ⟨vx, hx0, hx⟩ := L.hH y hyh
    refine ⟨by rw [hx, hx0]; simp, fun v v0 hv hv0 => ?_⟩
    rw [hx] at hv; rw [hx0] at hv0; cases hv; cases hv0
    exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd hyh h⟩
  · have e := L.hO y hy hys hyh
    refine ⟨by rw [e], fun v v0 hv hv0 => ?_⟩
    rw [e, hv0] at hv; cases hv
    exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- Off `w`, a thread waits on a server after the link exactly when it did before. -/
theorem waiterOf_off_w (L : LinkStep V0 V w s vw0 vs0) {y s' : ThreadId} (hy : y ≠ w) :
    V.waiterOf y s' ↔ V0.waiterOf y s' := by
  obtain ⟨hNone, hRel⟩ := L.off_w hy
  constructor
  · rintro ⟨v, hv, hb⟩
    cases hv0 : V0 y.toObjId with
    | none => rw [← hNone] at hv0; rw [hv0] at hv; cases hv
    | some v0 => exact ⟨v0, hv0, (hRel v v0 hv hv0).1 ▸ hb⟩
  · rintro ⟨v0, hv0, hb⟩
    cases hv : V y.toObjId with
    | none => rw [hNone] at hv; rw [hv] at hv0; cases hv0
    | some v => exact ⟨v, hv, (hRel v v0 hv hv0).1.trans hb⟩

end LinkStep

/-- The head of a queue is its first member. -/
theorem chain_head_mem {V : ReplyViews} {l : List ThreadId} {p : Option ThreadId}
    {h : ThreadId} (hC : V.chain p (some h) l) : h ∈ l := by
  cases l with
  | nil => cases hC
  | cons x _ => obtain ⟨hc, -⟩ := hC; cases hc; exact List.mem_cons_self ..

namespace LinkStep

variable {V0 V : ReplyViews} {w s : ThreadId} {vw0 vs0 : ReplyView}

/-- The members of a queue other than `s`'s, and of `s`'s other than its old
head, keep their views across the link. -/
theorem view_eq_of_waiter (L : LinkStep V0 V w s vw0 vs0) {y s' : ThreadId}
    (hy : V0.waiterOf y s') (hh : ThreadId.ofOptCode vs0.headCode ≠ some y) :
    V y.toObjId = V0 y.toObjId := by
  obtain ⟨vy, hvy, hb⟩ := hy
  refine L.hO y (fun e => ?_) (fun e => ?_) hh
  · subst e; rw [L.hW0] at hvy; cases hvy; rw [L.hWn] at hb; cases hb
  · subst e; rw [L.hS0] at hvy; cases hvy; rw [L.hSn] at hb; cases hb

/-- `s`'s old head is a waiter of `s`. -/
theorem head_waiter (L : LinkStep V0 V w s vw0 vs0) (hc : V0.consistent) {h : ThreadId}
    (hh : ThreadId.ofOptCode vs0.headCode = some h) : V0.waiterOf h s := by
  obtain ⟨l, hQ⟩ := hc.1 s vs0 L.hS0
  exact queue_waiter hQ (chain_head_mem (hh ▸ hQ.1))

/-- A waiter of a server other than `s` is not `s`'s old head. -/
theorem head_ne_of_waiter (L : LinkStep V0 V w s vw0 vs0) (hc : V0.consistent)
    {y s' : ThreadId} (hy : V0.waiterOf y s') (hs' : s' ≠ s) :
    ThreadId.ofOptCode vs0.headCode ≠ some y := fun hh => by
  obtain ⟨v, hv, hb⟩ := L.head_waiter hc hh
  obtain ⟨v', hv', hb'⟩ := hy
  rw [hv] at hv'; cases hv'; rw [hb] at hb'; exact hs' (Option.some.inj hb').symm

end LinkStep

namespace LinkStep

variable {V0 V : ReplyViews} {w s : ThreadId} {vw0 vs0 : ReplyView}

/-- `s`'s queue after the link: `w` in front of the old one. -/
theorem queue_s (L : LinkStep V0 V w s vw0 vs0) {l : List ThreadId}
    (hQ : V0.queue s vs0 l) :
    V.queue s { vs0 with headCode := ThreadId.optCode (some w), count := vs0.count + 1 }
      (w :: l) := by
  have hwl : w ∉ l := not_mem_queue_of_server_none hQ L.hW0 L.hWn
  refine ⟨⟨by simp, _, L.hW, by simp, ?_⟩, by simp [hQ.2.1], List.nodup_cons.mpr ⟨hwl, hQ.2.2.1⟩,
    fun x => ?_⟩
  · have hC := hQ.1
    cases l with
    | nil => exact hC
    | cons h rest =>
      obtain ⟨hh, vh, hvh0, -, hR⟩ := hC
      obtain ⟨vx, hx0, hx⟩ := L.hH h hh
      rw [hvh0] at hx0; cases hx0
      refine ⟨hh, _, hx, by simp, chain_congr hR fun y hy => ?_⟩
      have hnd := hQ.2.2.1
      refine L.view_eq_of_waiter (queue_waiter hQ (List.mem_cons_of_mem _ hy)) (fun e => ?_)
      rw [hh] at e; cases e
      exact (List.nodup_cons.mp hnd).1 hy
  · by_cases hx : x = w
    · subst hx
      exact ⟨fun _ => ⟨_, L.hW, rfl⟩, fun _ => List.mem_cons_self ..⟩
    · rw [L.waiterOf_off_w hx, ← hQ.2.2.2 x]
      exact ⟨fun h => (List.mem_cons.mp h).resolve_left hx, List.mem_cons_of_mem _⟩

/-- A queue of a server other than `s` is unchanged by the link. -/
theorem queue_other (L : LinkStep V0 V w s vw0 vs0) (hc : V0.consistent) {s' : ThreadId}
    (hs' : s' ≠ s) {vs' v0 : ReplyView} {l : List ThreadId} (hQ : V0.queue s' v0 l)
    (hH : vs'.headCode = v0.headCode) (hN : vs'.count = v0.count) :
    V.queue s' vs' l := by
  refine ⟨hH ▸ chain_congr hQ.1 fun y hy => ?_, hN ▸ hQ.2.1, hQ.2.2.1, fun x => ?_⟩
  · have hw := queue_waiter hQ hy
    exact L.view_eq_of_waiter hw (L.head_ne_of_waiter hc hw hs')
  · by_cases hx : x = w
    · subst hx
      refine ⟨fun h => absurd h (not_mem_queue_of_server_none hQ L.hW0 L.hWn), ?_⟩
      rintro ⟨v, hv, hb⟩
      rw [L.hW] at hv; cases hv
      exact absurd (Option.some.inj hb).symm hs'
    · rw [L.waiterOf_off_w hx]; exact hQ.2.2.2 x

end LinkStep

namespace LinkStep

variable {V0 V : ReplyViews} {w s : ThreadId} {vw0 vs0 : ReplyView}

/-- WS-ZA ZA4.6: **linking a new waiter at its server's head keeps the queues
consistent.** -/
theorem consistent (L : LinkStep V0 V w s vw0 vs0) (hc : V0.consistent) : V.consistent := by
  refine ⟨fun s' vs' hS' => ?_, fun y vy s'' hy hb => ?_, fun y vy hy hb => ?_,
    fun y vy hy => ?_⟩
  · by_cases hs : s' = s
    · subst hs
      rw [L.hS] at hS'; cases hS'
      obtain ⟨l, hQ⟩ := hc.1 _ vs0 L.hS0
      exact ⟨_, L.queue_s hQ⟩
    · by_cases hw : s' = w
      · subst hw
        rw [L.hW] at hS'; cases hS'
        obtain ⟨l, hQ⟩ := hc.1 _ vw0 L.hW0
        exact ⟨l, L.queue_other hc hs hQ rfl rfl⟩
      · obtain ⟨hNone, hRel⟩ := L.off_w hw
        cases hv0 : V0 s'.toObjId with
        | none => rw [← hNone] at hv0; rw [hv0] at hS'; cases hS'
        | some v0 =>
          obtain ⟨l, hQ⟩ := hc.1 _ v0 hv0
          obtain ⟨-, -, hHC, -⟩ := hRel vs' v0 hS' hv0
          obtain ⟨hH, hN⟩ := hHC hs
          exact ⟨l, L.queue_other hc hs hQ hH hN⟩
  · by_cases hyw : y = w
    · subst hyw
      rw [L.hW] at hy; cases hy; cases hb
      exact ⟨_, L.hS⟩
    · obtain ⟨hNone, hRel⟩ := L.off_w hyw
      cases hv0 : V0 y.toObjId with
      | none => rw [← hNone] at hv0; rw [hv0] at hy; cases hy
      | some v0 =>
        have hb0 : v0.server = some s'' := (hRel vy v0 hy hv0).1 ▸ hb
        obtain ⟨vs, hvs⟩ := hc.2.1 y v0 s'' hv0 hb0
        by_cases hsw : s'' = w
        · subst hsw; exact ⟨_, L.hW⟩
        · cases hV : V s''.toObjId with
          | some v => exact ⟨v, rfl⟩
          | none => rw [(L.off_w hsw).1] at hV; rw [hV] at hvs; cases hvs
  · have hyw : y ≠ w := fun e => by subst e; rw [L.hW] at hy; cases hy; cases hb
    obtain ⟨hNone, hRel⟩ := L.off_w hyw
    cases hv0 : V0 y.toObjId with
    | none => rw [← hNone] at hv0; rw [hv0] at hy; cases hy
    | some v0 =>
      obtain ⟨hSv, hNx, -, hPv⟩ := hRel vy v0 hy hv0
      obtain ⟨hP0, hN0⟩ := hc.2.2.1 y v0 hv0 (hSv ▸ hb)
      refine ⟨?_, hNx.trans hN0⟩
      refine (hPv fun hh => ?_).trans hP0
      obtain ⟨v, hv, hbs⟩ := L.head_waiter hc hh
      rw [hv0] at hv; cases hv; rw [← hSv, hb] at hbs; cases hbs
  · by_cases hyw : y = w
    · subst hyw
      rw [L.hW] at hy; cases hy
      exact fun e => L.hne (Option.some.inj e).symm
    · obtain ⟨hNone, hRel⟩ := L.off_w hyw
      cases hv0 : V0 y.toObjId with
      | none => rw [← hNone] at hv0; rw [hv0] at hy; cases hy
      | some v0 => rw [(hRel vy v0 hy hv0).1]; exact hc.2.2.2 y v0 hv0

end LinkStep

end SeLe4n.Model.ReplyViews
