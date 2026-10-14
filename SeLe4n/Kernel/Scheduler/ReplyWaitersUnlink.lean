-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.ReplyWaitersLink

/-!
# Unlinking a reply waiter, over views (WS-ZA ZA4.6)

A waiter that stops being reply-blocked leaves its server's queue: its
predecessor (or the server's head) skips to its successor, its successor links
back to its predecessor, the server's count drops, and the leaver's own links
clear as its view stops naming a server.  `UnlinkStep.consistent` proves the
queues stay consistent across exactly that change of views.
-/

namespace SeLe4n.Model.ReplyViews

open SeLe4n

/-- A queue read through views that agree on its members' links is the same queue. -/
theorem chain_congr_links {V V' : ReplyViews} :
    ∀ {l : List ThreadId} {p c : Option ThreadId}, V.chain p c l →
      (∀ x ∈ l, (V' x.toObjId).map (fun v => (v.prevCode, v.nextCode)) =
        (V x.toObjId).map (fun v => (v.prevCode, v.nextCode))) → V'.chain p c l
  | [], _, _, h, _ => h
  | x :: l, _, _, ⟨hc, v, hV, hP, hR⟩, hE => by
    have hx := hE x (List.mem_cons_self ..)
    rw [hV] at hx
    cases hV' : V' x.toObjId with
    | none => rw [hV'] at hx; cases hx
    | some v' =>
      rw [hV'] at hx
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      refine ⟨hc, v', hV', hx.1 ▸ hP, hx.2 ▸ chain_congr_links hR ?_⟩
      exact fun y hy => hE y (List.mem_cons_of_mem _ hy)

/-- A member's successor is none or a member. -/
theorem chain_next_mem {V : ReplyViews} :
    ∀ {l : List ThreadId} {p c : Option ThreadId}, V.chain p c l →
      ∀ {w : ThreadId} {vw : ReplyView} {n : ThreadId}, w ∈ l → V w.toObjId = some vw →
        ThreadId.ofOptCode vw.nextCode = some n → n ∈ l
  | [], _, _, _, _, _, _, hw, _, _ => absurd hw List.not_mem_nil
  | x :: l, _, _, ⟨hc, v, hV, _, hR⟩, w, vw, n, hw, hW, hN => by
    rcases List.mem_cons.mp hw with e | hw'
    · subst e; rw [hV] at hW; cases hW
      exact List.mem_cons_of_mem _ (chain_head_mem (hN ▸ hR))
    · exact List.mem_cons_of_mem _ (chain_next_mem hR hw' hW hN)

/-- A member that is not the queue's start has a member as predecessor. -/
theorem chain_prev_mem {V : ReplyViews} :
    ∀ {l : List ThreadId} {p c : Option ThreadId}, V.chain p c l →
      ∀ {w : ThreadId} {vw : ReplyView}, w ∈ l → V w.toObjId = some vw → c ≠ some w →
        ∃ z ∈ l, ThreadId.ofOptCode vw.prevCode = some z
  | [], _, _, _, _, _, hw, _, _ => absurd hw List.not_mem_nil
  | x :: l, _, _, ⟨hc, v, hV, _, hR⟩, w, vw, hw, hW, hne => by
    rcases List.mem_cons.mp hw with e | hw'
    · subst e; exact absurd hc hne
    · by_cases hh : ThreadId.ofOptCode v.nextCode = some w
      · cases l with
        | nil => exact absurd hw' List.not_mem_nil
        | cons y r =>
          obtain ⟨hc', v', hV', hP', -⟩ := hR
          rw [hh] at hc'; cases hc'
          rw [hW] at hV'; cases hV'
          exact ⟨x, List.mem_cons_self .., hP'⟩
      · obtain ⟨z, hz, hP⟩ := chain_prev_mem hR hw' hW hh
        exact ⟨z, List.mem_cons_of_mem _ hz, hP⟩

/-- In a queue of distinct threads entered from outside it, a member is neither
of its own neighbours, and its two neighbours differ. -/
theorem chain_neighbours {V : ReplyViews} :
    ∀ {l : List ThreadId} {p c : Option ThreadId}, V.chain p c l → l.Nodup →
      (∀ z, p = some z → z ∉ l) →
      ∀ {w : ThreadId} {vw : ReplyView}, w ∈ l → V w.toObjId = some vw →
        ThreadId.ofOptCode vw.nextCode ≠ some w ∧ ThreadId.ofOptCode vw.prevCode ≠ some w ∧
        ∀ z, ThreadId.ofOptCode vw.prevCode = some z → ThreadId.ofOptCode vw.nextCode ≠ some z
  | [], _, _, _, _, _, _, _, hw, _ => absurd hw List.not_mem_nil
  | x :: rest, p, _, ⟨hc, v, hV, hP, hR⟩, hnd, hp, w, vw, hw, hW => by
    have hndx := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hw with e | hw'
    · subst e; rw [hV] at hW; cases hW
      refine ⟨fun e => hndx.1 (chain_head_mem (e ▸ hR)), fun e => ?_, fun z hz e => ?_⟩
      · rw [hP] at e; exact hp _ e hw
      · rw [hP] at hz
        exact hp z hz (List.mem_cons_of_mem _ (chain_head_mem (e ▸ hR)))
    · exact chain_neighbours hR hndx.2 (fun z e => by cases e; exact hndx.1) hw' hW

/-- The views an unlink leaves: `w` leaves `s`'s queue and names no server. -/
structure UnlinkStep (V0 V : ReplyViews) (w s : ThreadId) (vw0 vs0 : ReplyView) : Prop where
  hW0 : V0 w.toObjId = some vw0
  hWSrv : vw0.server = some s
  hS0 : V0 s.toObjId = some vs0
  hW : V w.toObjId = some { vw0 with server := none, prevCode := 0, nextCode := 0 }
  hS : V s.toObjId = some { vs0 with
    headCode := if vw0.prevCode = 0 then vw0.nextCode else vs0.headCode,
    count := vs0.count - 1 }
  hP : ∀ p, ThreadId.ofOptCode vw0.prevCode = some p → ∃ vp, V0 p.toObjId = some vp ∧
    V p.toObjId = some { vp with nextCode := vw0.nextCode }
  hN : ∀ n, ThreadId.ofOptCode vw0.nextCode = some n → ∃ vn, V0 n.toObjId = some vn ∧
    V n.toObjId = some { vn with prevCode := vw0.prevCode }
  hO : ∀ y : ThreadId, y ≠ w → y ≠ s → ThreadId.ofOptCode vw0.prevCode ≠ some y →
    ThreadId.ofOptCode vw0.nextCode ≠ some y → V y.toObjId = V0 y.toObjId

namespace UnlinkStep

variable {V0 V : ReplyViews} {w s : ThreadId} {vw0 vs0 : ReplyView}

theorem ne_s (U : UnlinkStep V0 V w s vw0 vs0) (hc : V0.consistent) : w ≠ s := fun e => by
  subst e; exact hc.2.2.2 _ _ U.hW0 U.hWSrv

/-- Off `w`, a slot holds a view after the unlink exactly when it did before; the
server is unchanged, off `s` the head and count are, and off `w`'s neighbours the
links are. -/
theorem off_w (U : UnlinkStep V0 V w s vw0 vs0) {y : ThreadId}
    (hy : y ≠ w) :
    (V y.toObjId = none ↔ V0 y.toObjId = none) ∧
    ∀ v v0, V y.toObjId = some v → V0 y.toObjId = some v0 →
      v.server = v0.server ∧
      (y ≠ s → v.headCode = v0.headCode ∧ v.count = v0.count) ∧
      (ThreadId.ofOptCode vw0.prevCode ≠ some y → ThreadId.ofOptCode vw0.nextCode ≠ some y →
        v.prevCode = v0.prevCode ∧ v.nextCode = v0.nextCode) := by
  by_cases hys : y = s
  · subst hys
    refine ⟨by rw [U.hS, U.hS0]; simp, fun v v0 hv hv0 => ?_⟩
    rw [U.hS] at hv; rw [U.hS0] at hv0; cases hv; cases hv0
    exact ⟨rfl, fun h => absurd rfl h, fun _ _ => ⟨rfl, rfl⟩⟩
  by_cases hyp : ThreadId.ofOptCode vw0.prevCode = some y
  · obtain ⟨vx, hx0, hx⟩ := U.hP y hyp
    refine ⟨by rw [hx, hx0]; simp, fun v v0 hv hv0 => ?_⟩
    rw [hx] at hv; rw [hx0] at hv0; cases hv; cases hv0
    exact ⟨rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd hyp h⟩
  by_cases hyn : ThreadId.ofOptCode vw0.nextCode = some y
  · obtain ⟨vx, hx0, hx⟩ := U.hN y hyn
    refine ⟨by rw [hx, hx0]; simp, fun v v0 hv hv0 => ?_⟩
    rw [hx] at hv; rw [hx0] at hv0; cases hv; cases hv0
    exact ⟨rfl, fun _ => ⟨rfl, rfl⟩, fun _ h => absurd hyn h⟩
  · have e := U.hO y hy hys hyp hyn
    refine ⟨by rw [e], fun v v0 hv hv0 => ?_⟩
    rw [e, hv0] at hv; cases hv
    exact ⟨rfl, fun _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩

/-- Off `w`, a thread waits on a server after the unlink exactly when it did before. -/
theorem waiterOf_off_w (U : UnlinkStep V0 V w s vw0 vs0)
    {y s' : ThreadId} (hy : y ≠ w) : V.waiterOf y s' ↔ V0.waiterOf y s' := by
  obtain ⟨hNone, hRel⟩ := U.off_w hy
  constructor
  · rintro ⟨v, hv, hb⟩
    cases hv0 : V0 y.toObjId with
    | none => rw [← hNone] at hv0; rw [hv0] at hv; cases hv
    | some v0 => exact ⟨v0, hv0, (hRel v v0 hv hv0).1 ▸ hb⟩
  · rintro ⟨v0, hv0, hb⟩
    cases hv : V y.toObjId with
    | none => rw [hNone] at hv; rw [hv] at hv0; cases hv0
    | some v => exact ⟨v, hv, (hRel v v0 hv hv0).1.trans hb⟩

/-- `w` waits on no server after the unlink. -/
theorem not_waiter_w (U : UnlinkStep V0 V w s vw0 vs0) {s' : ThreadId} : ¬ V.waiterOf w s' :=
  fun ⟨v, hv, hb⟩ => by rw [U.hW] at hv; cases hv; cases hb

end UnlinkStep

namespace UnlinkStep

variable {V0 V : ReplyViews} {w s : ThreadId} {vw0 vs0 : ReplyView}

/-- A waiter of `s` is not `s`. -/
theorem waiter_ne_s (hc : V0.consistent) {y : ThreadId} (hy : V0.waiterOf y s) : y ≠ s :=
  fun e => by subst e; obtain ⟨v, hv, hb⟩ := hy; exact hc.2.2.2 _ v hv hb

/-- A waiter's neighbours wait on its server. -/
theorem nb_waiter (hc : V0.consistent) (hW0 : V0 w.toObjId = some vw0) (hWSrv : vw0.server = some s)
    (hS0 : V0 s.toObjId = some vs0) {z : ThreadId}
    (hz : ThreadId.ofOptCode vw0.prevCode = some z ∨ ThreadId.ofOptCode vw0.nextCode = some z) :
    V0.waiterOf z s := by
  obtain ⟨l0, hQ0⟩ := hc.1 s vs0 hS0
  have hw : w ∈ l0 := (hQ0.2.2.2 w).mpr ⟨vw0, hW0, hWSrv⟩
  refine (hQ0.2.2.2 z).mp ?_
  rcases hz with hz | hz
  · by_cases hh : ThreadId.ofOptCode vs0.headCode = some w
    · cases l0 with
      | nil => exact absurd hw List.not_mem_nil
      | cons a r =>
        obtain ⟨hc', v', hv', hp', -⟩ := hQ0.1
        rw [hh] at hc'; cases hc'
        rw [hW0] at hv'; cases hv'; rw [hp'] at hz; cases hz
    · obtain ⟨z', hz', hpz⟩ := chain_prev_mem hQ0.1 hw hW0 hh
      rw [hpz] at hz; cases hz; exact hz'
  · exact chain_next_mem hQ0.1 hw hW0 hz

/-- **The queue without `w`**: erasing `w` from a stretch of `s`'s queue reads,
after the unlink, from the same predecessor, starting where it started unless it
started at `w`, in which case at `w`'s successor. -/
theorem chain_erase (U : UnlinkStep V0 V w s vw0 vs0) (hc : V0.consistent) :
    ∀ {l : List ThreadId} {p c : Option ThreadId}, V0.chain p c l → l.Nodup → w ∈ l →
      (∀ z, p = some z → z ∉ l) → (∀ y ∈ l, V0.waiterOf y s) →
      V.chain p (if c = some w then ThreadId.ofOptCode vw0.nextCode else c) (l.erase w)
  | [], _, _, _, _, hw, _, _ => absurd hw List.not_mem_nil
  | x :: rest, p, c, ⟨hcx, vx, hvx, hpx, hR⟩, hnd, hw, hp, hws => by
    have hndx := List.nodup_cons.mp hnd
    by_cases hxw : x = w
    · subst hxw
      rw [U.hW0] at hvx; cases hvx
      rw [if_pos hcx, List.erase_cons_head]
      cases rest with
      | nil => exact hR
      | cons y r =>
        obtain ⟨hy, vy, hvy, -, hR'⟩ := hR
        obtain ⟨vn, hvn0, hvn⟩ := U.hN y hy
        rw [hvy] at hvn0; cases hvn0
        refine ⟨hy, _, hvn, hpx, chain_congr hR' fun z hz => U.hO z ?_ ?_ ?_ ?_⟩
        · exact fun e => hndx.1 (e ▸ List.mem_cons_of_mem _ hz)
        · exact waiter_ne_s hc (hws z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)))
        · rw [hpx]; exact fun e => hp z e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
        · rw [hy]; intro e; cases e
          exact (List.nodup_cons.mp hndx.2).1 hz
    · have hcw : c ≠ some w := by rw [hcx]; exact fun e => hxw (Option.some.inj e)
      rw [if_neg hcw, List.erase_cons_tail (by simpa using hxw)]
      have hw' : w ∈ rest := (List.mem_cons.mp hw).resolve_left (fun e => hxw e.symm)
      have IH := chain_erase U hc hR hndx.2 hw'
        (fun z e => by cases e; exact hndx.1)
        (fun y hy => hws y (List.mem_cons_of_mem _ hy))
      have hxs : x ≠ s := waiter_ne_s hc (hws x (List.mem_cons_self ..))
      by_cases hnw : ThreadId.ofOptCode vx.nextCode = some w
      · rw [if_pos hnw] at IH
        -- `w` heads `rest`, so its predecessor is `x`.
        have hpw : ThreadId.ofOptCode vw0.prevCode = some x := by
          cases rest with
          | nil => exact absurd hw' List.not_mem_nil
          | cons y r =>
            obtain ⟨hc', v', hv', hp', -⟩ := hR
            rw [hnw] at hc'; cases hc'
            rw [U.hW0] at hv'; cases hv'; exact hp'
        obtain ⟨vp, hvp0, hvp⟩ := U.hP x hpw
        rw [hvx] at hvp0; cases hvp0
        exact ⟨hcx, _, hvp, hpx, IH⟩
      · rw [if_neg hnw] at IH
        have hV : V x.toObjId = V0 x.toObjId := by
          refine U.hO x hxw hxs (fun e => ?_) (fun e => ?_)
          · obtain ⟨z, hz, hpz⟩ := chain_prev_mem hR hw' U.hW0 hnw
            rw [hpz] at e; cases e; exact hndx.1 hz
          · exact hndx.1 (chain_next_mem hR hw' U.hW0 e)
        exact ⟨hcx, vx, hV.trans hvx, hpx, IH⟩

end UnlinkStep

namespace UnlinkStep

variable {V0 V : ReplyViews} {w s : ThreadId} {vw0 vs0 : ReplyView}

/-- `s`'s queue after the unlink: the old one without `w`. -/
theorem queue_s (U : UnlinkStep V0 V w s vw0 vs0) (hc : V0.consistent) {l : List ThreadId}
    (hQ : V0.queue s vs0 l) :
    V.queue s { vs0 with
      headCode := if vw0.prevCode = 0 then vw0.nextCode else vs0.headCode,
      count := vs0.count - 1 } (l.erase w) := by
  have hw : w ∈ l := (hQ.2.2.2 w).mpr ⟨vw0, U.hW0, U.hWSrv⟩
  have hCh := U.chain_erase hc hQ.1 hQ.2.2.1 hw (fun _ e => by cases e)
    (fun y hy => queue_waiter hQ hy)
  refine ⟨?_, by rw [List.length_erase_of_mem hw, hQ.2.1], hQ.2.2.1.erase w, fun x => ?_⟩
  · -- `w` heads the queue exactly when it has no predecessor.
    have hHead : (if ThreadId.ofOptCode vs0.headCode = some w then
        ThreadId.ofOptCode vw0.nextCode else ThreadId.ofOptCode vs0.headCode) =
        ThreadId.ofOptCode (if vw0.prevCode = 0 then vw0.nextCode else vs0.headCode) := by
      by_cases hh : ThreadId.ofOptCode vs0.headCode = some w
      · rw [if_pos hh]
        have hPrevZero : vw0.prevCode = 0 := by
          cases l with
          | nil => exact absurd hw List.not_mem_nil
          | cons y r =>
            obtain ⟨hc', v', hv', hp', -⟩ := hQ.1
            rw [hh] at hc'; cases hc'
            rw [U.hW0] at hv'; cases hv'
            cases e : vw0.prevCode with
            | zero => rfl
            | succ k => rw [e] at hp'; cases hp'
        rw [if_pos hPrevZero]
      · rw [if_neg hh]
        have hPrevZero : vw0.prevCode ≠ 0 := fun e => by
          obtain ⟨z, -, hz⟩ := chain_prev_mem hQ.1 hw U.hW0 hh
          rw [e] at hz; cases hz
        rw [if_neg hPrevZero]
    rw [← hHead]; exact hCh
  · by_cases hxw : x = w
    · subst hxw
      exact ⟨fun h => absurd h (hQ.2.2.1.not_mem_erase), fun h => absurd h U.not_waiter_w⟩
    · rw [hQ.2.2.1.mem_erase_iff, U.waiterOf_off_w hxw, ← hQ.2.2.2 x]
      exact ⟨fun h => h.2, fun h => ⟨hxw, h⟩⟩

/-- A queue of a server other than `s` is unchanged by the unlink. -/
theorem queue_other (U : UnlinkStep V0 V w s vw0 vs0) (hc : V0.consistent) {s' : ThreadId}
    (hs' : s' ≠ s) {vs' v0 : ReplyView} {l : List ThreadId} (hQ : V0.queue s' v0 l)
    (hH : vs'.headCode = v0.headCode) (hN : vs'.count = v0.count) :
    V.queue s' vs' l := by
  refine ⟨hH ▸ chain_congr_links hQ.1 fun y hy => ?_, hN ▸ hQ.2.1, hQ.2.2.1, fun x => ?_⟩
  · obtain ⟨vy, hvy, hb⟩ := queue_waiter hQ hy
    have hyw : y ≠ w := fun e => by
      subst e; rw [U.hW0] at hvy; cases hvy; rw [U.hWSrv] at hb
      exact hs' (Option.some.inj hb).symm
    -- `w`'s neighbours wait on `s`, so they are not in `s'`'s queue.
    have hNb : ∀ z, (ThreadId.ofOptCode vw0.prevCode = some z ∨
        ThreadId.ofOptCode vw0.nextCode = some z) → z ≠ y := by
      intro z hz e; subst e
      obtain ⟨v1, hv1, hb1⟩ := nb_waiter hc U.hW0 U.hWSrv U.hS0 hz
      rw [hvy] at hv1; cases hv1; rw [hb] at hb1; exact hs' (Option.some.inj hb1)
    obtain ⟨hNone, hRel⟩ := U.off_w hyw
    cases hv : V y.toObjId with
    | none => rw [hNone] at hv; rw [hv] at hvy; cases hvy
    | some v =>
      obtain ⟨-, -, hL⟩ := hRel v vy hv hvy
      obtain ⟨hp, hn⟩ := hL (fun e => hNb y (Or.inl e) rfl) (fun e => hNb y (Or.inr e) rfl)
      rw [hvy]; simp [hp, hn]
  · by_cases hxw : x = w
    · subst hxw
      refine ⟨fun h => ?_, fun h => absurd h U.not_waiter_w⟩
      obtain ⟨v, hv, hb⟩ := queue_waiter hQ h
      rw [U.hW0] at hv; cases hv; rw [U.hWSrv] at hb; exact absurd (Option.some.inj hb).symm hs'
    · rw [U.waiterOf_off_w hxw]; exact hQ.2.2.2 x

/-- WS-ZA ZA4.6: **unlinking a waiter keeps the queues consistent.** -/
theorem consistent (U : UnlinkStep V0 V w s vw0 vs0) (hc : V0.consistent) : V.consistent := by
  refine ⟨fun s' vs' hS' => ?_, fun y vy s'' hy hb => ?_, fun y vy hy hb => ?_,
    fun y vy hy => ?_⟩
  · by_cases hs : s' = s
    · subst hs
      rw [U.hS] at hS'; cases hS'
      obtain ⟨l, hQ⟩ := hc.1 _ vs0 U.hS0
      exact ⟨_, U.queue_s hc hQ⟩
    · by_cases hw : s' = w
      · subst hw
        rw [U.hW] at hS'; cases hS'
        obtain ⟨l, hQ⟩ := hc.1 _ vw0 U.hW0
        exact ⟨l, U.queue_other hc hs hQ rfl rfl⟩
      · obtain ⟨hNone, hRel⟩ := U.off_w hw
        cases hv0 : V0 s'.toObjId with
        | none => rw [← hNone] at hv0; rw [hv0] at hS'; cases hS'
        | some v0 =>
          obtain ⟨l, hQ⟩ := hc.1 _ v0 hv0
          obtain ⟨-, hHC, -⟩ := hRel vs' v0 hS' hv0
          obtain ⟨hH, hN⟩ := hHC hs
          exact ⟨l, U.queue_other hc hs hQ hH hN⟩
  · have hyw : y ≠ w := fun e => by subst e; rw [U.hW] at hy; cases hy; cases hb
    obtain ⟨hNone, hRel⟩ := U.off_w hyw
    cases hv0 : V0 y.toObjId with
    | none => rw [← hNone] at hv0; rw [hv0] at hy; cases hy
    | some v0 =>
      have hb0 : v0.server = some s'' := (hRel vy v0 hy hv0).1 ▸ hb
      obtain ⟨vs, hvs⟩ := hc.2.1 y v0 s'' hv0 hb0
      by_cases hsw : s'' = w
      · subst hsw; exact ⟨_, U.hW⟩
      · cases hV : V s''.toObjId with
        | some v => exact ⟨v, rfl⟩
        | none => rw [(U.off_w hsw).1] at hV; rw [hV] at hvs; cases hvs
  · by_cases hyw : y = w
    · subst hyw; rw [U.hW] at hy; cases hy; exact ⟨rfl, rfl⟩
    obtain ⟨hNone, hRel⟩ := U.off_w hyw
    cases hv0 : V0 y.toObjId with
    | none => rw [← hNone] at hv0; rw [hv0] at hy; cases hy
    | some v0 =>
      obtain ⟨hSv, -, hL⟩ := hRel vy v0 hy hv0
      -- A neighbour of `w` waits on `s`, so it is not blocked on no server.
      have hNb : ∀ z, (ThreadId.ofOptCode vw0.prevCode = some z ∨
          ThreadId.ofOptCode vw0.nextCode = some z) → z ≠ y := by
        intro z hz e; subst e
        obtain ⟨v1, hv1, hb1⟩ := nb_waiter hc U.hW0 U.hWSrv U.hS0 hz
        rw [hv0] at hv1; cases hv1; rw [← hSv, hb] at hb1; cases hb1
      obtain ⟨hp, hn⟩ := hL (fun e => hNb y (Or.inl e) rfl) (fun e => hNb y (Or.inr e) rfl)
      obtain ⟨hP0, hN0⟩ := hc.2.2.1 y v0 hv0 (hSv ▸ hb)
      exact ⟨hp.trans hP0, hn.trans hN0⟩
  · by_cases hyw : y = w
    · subst hyw; rw [U.hW] at hy; cases hy; exact fun e => by cases e
    · obtain ⟨hNone, hRel⟩ := U.off_w hyw
      cases hv0 : V0 y.toObjId with
      | none => rw [← hNone] at hv0; rw [hv0] at hy; cases hy
      | some v0 => rw [(hRel vy v0 hy hv0).1]; exact hc.2.2.2 y v0 hv0

end UnlinkStep

end SeLe4n.Model.ReplyViews
