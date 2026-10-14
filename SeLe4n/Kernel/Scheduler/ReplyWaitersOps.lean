-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.ReplyWaitersUnlink
import SeLe4n.Kernel.Scheduler.RunQueueLinkFrame

/-!
# Linking and unlinking a reply waiter (WS-ZA ZA4.6)

`SystemState.linkReplyWaiter st w s` puts `w` at the front of server `s`'s
queue of reply waiters and `SystemState.unlinkReplyWaiter st w s` takes it out
(seL4 keeps the same queue as the reply objects of a call stack).  Each writes
TCBs in their slots (`SystemState.mapTcbInPlace`), so neither allocates.

Neither writes `w`'s IPC state: the transition that blocks `w` on a reply, or
ends that block, writes it beside the link.  Each operation reads and writes
reply views alone (`replyViews_linkReplyWaiter`, `replyViews_unlinkReplyWaiter`),
so the queues' consistency is proven over views: `w`'s block written beside a
link is a `LinkStep` (`linkStep_of_link`), and its end written beside an unlink
is an `UnlinkStep` (`unlinkStep_of_unlink`).
-/

namespace SeLe4n.Model.ReplyViews

open SeLe4n

/-- The views with thread `t`'s rewritten through `f`. -/
def mapAt (V : ReplyViews) (t : ThreadId) (f : ReplyView → ReplyView) : ReplyViews :=
  fun k => if t.toObjId = k then (V k).map f else V k

/-- The views with the thread a link code names rewritten; none for the code `0`. -/
def mapAtCode (V : ReplyViews) (c : Nat) (f : ReplyView → ReplyView) : ReplyViews :=
  match ThreadId.ofOptCode c with
  | some x => V.mapAt x f
  | none => V

/-- Thread `t`'s server, as the IPC state writes it. -/
def setServer (V : ReplyViews) (t : ThreadId) (srv : Option ThreadId) : ReplyViews :=
  V.mapAt t fun v => { v with server := srv }

/-- `s`'s head code; `0` off a view. -/
def headCodeOf (V : ReplyViews) (s : ThreadId) : Nat :=
  match V s.toObjId with
  | some v => v.headCode
  | none => 0

/-- `w`'s predecessor code; `0` off a view. -/
def prevCodeOf (V : ReplyViews) (w : ThreadId) : Nat :=
  match V w.toObjId with
  | some v => v.prevCode
  | none => 0

/-- `w`'s successor code; `0` off a view. -/
def nextCodeOf (V : ReplyViews) (w : ThreadId) : Nat :=
  match V w.toObjId with
  | some v => v.nextCode
  | none => 0

/-- `w` in front of `s`'s queue, on views. -/
def link (V : ReplyViews) (w s : ThreadId) : ReplyViews :=
  let h := V.headCodeOf s
  (((V.mapAt w fun v => { v with prevCode := 0, nextCode := h }).mapAtCode h
      fun v => { v with prevCode := ThreadId.optCode (some w) }).mapAt s
    fun v => { v with headCode := ThreadId.optCode (some w), count := v.count + 1 })

/-- `w` out of `s`'s queue, on views. -/
def unlink (V : ReplyViews) (w s : ThreadId) : ReplyViews :=
  let pv := V.prevCodeOf w
  let nx := V.nextCodeOf w
  ((((V.mapAtCode pv fun v => { v with nextCode := nx }).mapAtCode nx
      fun v => { v with prevCode := pv }).mapAt s
    fun v => { v with headCode := if pv = 0 then nx else v.headCode, count := v.count - 1 }).mapAt w
    fun v => { v with prevCode := 0, nextCode := 0 })

theorem mapAt_self (V : ReplyViews) (t : ThreadId) (f : ReplyView → ReplyView) :
    V.mapAt t f t.toObjId = (V t.toObjId).map f := if_pos rfl

theorem mapAt_ne (V : ReplyViews) {t y : ThreadId} (f : ReplyView → ReplyView) (h : y ≠ t) :
    V.mapAt t f y.toObjId = V y.toObjId :=
  if_neg fun e => h (ThreadId.toObjId_injective _ _ e).symm

theorem mapAtCode_some (V : ReplyViews) {c : Nat} {x : ThreadId} (h : ThreadId.ofOptCode c = some x)
    (f : ReplyView → ReplyView) : V.mapAtCode c f = V.mapAt x f := by
  unfold mapAtCode; rw [h]

theorem mapAtCode_none (V : ReplyViews) {c : Nat} (h : ThreadId.ofOptCode c = none)
    (f : ReplyView → ReplyView) : V.mapAtCode c f = V := by
  unfold mapAtCode; rw [h]

end SeLe4n.Model.ReplyViews

namespace SeLe4n.Model.SystemState

open SeLe4n
open SeLe4n.Kernel.LinkedQueue

/-- `s`'s head code, read in its slot through `objectEntry?`; `0` off a TCB. -/
@[inline] def replyHeadCode (st : SystemState) (s : ThreadId) : Nat :=
  match st.objectEntry? s.toObjId with
  | some e => match e.value with
    | .tcb t => t.replyWaitersHeadCode
    | _ => 0
  | none => 0

/-- `w`'s predecessor code, read in its slot through `objectEntry?`; `0` off a TCB. -/
@[inline] def replyPrevCode (st : SystemState) (w : ThreadId) : Nat :=
  match st.objectEntry? w.toObjId with
  | some e => match e.value with
    | .tcb t => t.replyWaiterPrevCode
    | _ => 0
  | none => 0

/-- `w`'s successor code, read in its slot through `objectEntry?`; `0` off a TCB. -/
@[inline] def replyNextCode (st : SystemState) (w : ThreadId) : Nat :=
  match st.objectEntry? w.toObjId with
  | some e => match e.value with
    | .tcb t => t.replyWaiterNextCode
    | _ => 0
  | none => 0

/-- WS-ZA ZA4.6: **`w` joins the front of server `s`'s reply-waiter queue**:
`w` links forward to the old head, the old head links back to `w`, and `s`'s
head and count move.  For a thread on no reply-waiter queue; the caller writes
`w`'s reply block beside it. -/
def linkReplyWaiter (st : SystemState) (w s : ThreadId) : SystemState :=
  let h := st.replyHeadCode s
  let st1 := st.mapTcbInPlace w fun x => { x with
    replyWaiterPrevCode := 0, replyWaiterNextCode := h }
  let st2 := st1.updateTcbAtCode h fun x => { x with replyWaiterPrevCode := code w }
  st2.mapTcbInPlace s fun x => { x with
    replyWaitersHeadCode := code w, replyWaitersCount := x.replyWaitersCount + 1 }

/-- WS-ZA ZA4.6: **`w` leaves server `s`'s reply-waiter queue** (seL4's
`tcbEPDequeue` shape): its predecessor and successor link past it, `s`'s head
moves past it when it headed the queue, `s`'s count drops, and `w` keeps no
links.  The caller writes the end of `w`'s reply block beside it. -/
def unlinkReplyWaiter (st : SystemState) (w s : ThreadId) : SystemState :=
  let pv := st.replyPrevCode w
  let nx := st.replyNextCode w
  let st1 := st.updateTcbAtCode pv fun x => { x with replyWaiterNextCode := nx }
  let st2 := st1.updateTcbAtCode nx fun x => { x with replyWaiterPrevCode := pv }
  let st3 := st2.mapTcbInPlace s fun x => { x with
    replyWaitersHeadCode := if pv = 0 then nx else x.replyWaitersHeadCode,
    replyWaitersCount := x.replyWaitersCount - 1 }
  st3.mapTcbInPlace w fun x => { x with replyWaiterPrevCode := 0, replyWaiterNextCode := 0 }

theorem objReplyView_map_mapTcb {g : TCB → TCB} {gv : ReplyView → ReplyView}
    (hg : ∀ x, (g x).replyView = gv x.replyView) (o : Option KernelObject) :
    objReplyView (o.map (KernelObject.mapTcb g)) = (objReplyView o).map gv := by
  cases o with
  | none => rfl
  | some o => cases o <;> simp [objReplyView, KernelObject.mapTcb, hg]

/-- A TCB rewrite that acts on reply views as `gv` rewrites the views by `gv`. -/
theorem replyViews_mapTcbInPlace (st : SystemState) (t : ThreadId) {g : TCB → TCB}
    {gv : ReplyView → ReplyView} (hg : ∀ x, (g x).replyView = gv x.replyView) :
    (st.mapTcbInPlace t g).replyViews = ReplyViews.mapAt st.replyViews t gv := by
  funext k
  unfold replyViews ReplyViews.mapAt
  rw [objects_mapTcbInPlace]
  by_cases h : t.toObjId = k
  · rw [if_pos (by simpa using h), if_pos h, objReplyView_map_mapTcb hg]
  · rw [if_neg (by simpa using h), if_neg h]

theorem decode_of_ofOptCode {c : Nat} {x : ThreadId} (h : ThreadId.ofOptCode c = some x) :
    decode c = x := by
  cases c with
  | zero => cases h
  | succ k => cases h; rfl

theorem replyViews_updateTcbAtCode (st : SystemState) (c : Nat) {g : TCB → TCB}
    {gv : ReplyView → ReplyView} (hg : ∀ x, (g x).replyView = gv x.replyView) :
    (st.updateTcbAtCode c g).replyViews = ReplyViews.mapAtCode st.replyViews c gv := by
  unfold updateTcbAtCode
  cases hc : ThreadId.ofOptCode c with
  | none =>
    rw [ReplyViews.mapAtCode_none _ hc]
    cases c with
    | zero => rfl
    | succ k => cases hc
  | some x =>
    rw [ReplyViews.mapAtCode_some _ hc]
    have hc0 : c ≠ 0 := fun e => by subst e; cases hc
    rw [if_neg hc0, decode_of_ofOptCode hc]
    exact replyViews_mapTcbInPlace st x hg

theorem replyHeadCode_eq (st : SystemState) (s : ThreadId) :
    st.replyHeadCode s = ReplyViews.headCodeOf st.replyViews s := by
  unfold replyHeadCode ReplyViews.headCodeOf replyViews
  rw [objects_get?_eq_objectEntry?]
  cases st.objectEntry? s.toObjId with
  | none => rfl
  | some e => cases h : e.value <;> simp [h, objReplyView, TCB.replyView]

theorem replyPrevCode_eq (st : SystemState) (w : ThreadId) :
    st.replyPrevCode w = ReplyViews.prevCodeOf st.replyViews w := by
  unfold replyPrevCode ReplyViews.prevCodeOf replyViews
  rw [objects_get?_eq_objectEntry?]
  cases st.objectEntry? w.toObjId with
  | none => rfl
  | some e => cases h : e.value <;> simp [h, objReplyView, TCB.replyView]

theorem replyNextCode_eq (st : SystemState) (w : ThreadId) :
    st.replyNextCode w = ReplyViews.nextCodeOf st.replyViews w := by
  unfold replyNextCode ReplyViews.nextCodeOf replyViews
  rw [objects_get?_eq_objectEntry?]
  cases st.objectEntry? w.toObjId with
  | none => rfl
  | some e => cases h : e.value <;> simp [h, objReplyView, TCB.replyView]

/-- The link reads and writes reply views alone. -/
theorem replyViews_linkReplyWaiter (st : SystemState) (w s : ThreadId) :
    (st.linkReplyWaiter w s).replyViews = ReplyViews.link st.replyViews w s := by
  unfold linkReplyWaiter ReplyViews.link
  simp only []
  rw [replyHeadCode_eq,
    replyViews_mapTcbInPlace _ s (gv := fun v => { v with
      headCode := ThreadId.optCode (some w), count := v.count + 1 }) (fun _ => rfl),
    replyViews_updateTcbAtCode _ _ (gv := fun v => { v with
      prevCode := ThreadId.optCode (some w) }) (fun _ => rfl),
    replyViews_mapTcbInPlace _ w (gv := fun v => { v with
      prevCode := 0, nextCode := ReplyViews.headCodeOf st.replyViews s }) (fun _ => rfl)]

/-- The unlink reads and writes reply views alone. -/
theorem replyViews_unlinkReplyWaiter (st : SystemState) (w s : ThreadId) :
    (st.unlinkReplyWaiter w s).replyViews = ReplyViews.unlink st.replyViews w s := by
  unfold unlinkReplyWaiter ReplyViews.unlink
  simp only []
  rw [replyPrevCode_eq, replyNextCode_eq,
    replyViews_mapTcbInPlace _ w (gv := fun v => { v with prevCode := 0, nextCode := 0 })
      (fun _ => rfl),
    replyViews_mapTcbInPlace _ s (gv := fun v => { v with
      headCode := if ReplyViews.prevCodeOf st.replyViews w = 0 then ReplyViews.nextCodeOf st.replyViews w
        else v.headCode, count := v.count - 1 }) (fun _ => rfl),
    replyViews_updateTcbAtCode _ _ (gv := fun v => { v with
      prevCode := ReplyViews.prevCodeOf st.replyViews w }) (fun _ => rfl),
    replyViews_updateTcbAtCode _ _ (gv := fun v => { v with
      nextCode := ReplyViews.nextCodeOf st.replyViews w }) (fun _ => rfl)]

end SeLe4n.Model.SystemState

namespace SeLe4n.Model.ReplyViews

open SeLe4n

theorem mapAtCode_self (V : ReplyViews) {c : Nat} {x : ThreadId} (h : ThreadId.ofOptCode c = some x)
    (f : ReplyView → ReplyView) : V.mapAtCode c f x.toObjId = (V x.toObjId).map f := by
  rw [mapAtCode_some _ h, mapAt_self]

theorem mapAtCode_ne (V : ReplyViews) {c : Nat} {y : ThreadId}
    (h : ∀ x, ThreadId.ofOptCode c = some x → x ≠ y)
    (f : ReplyView → ReplyView) : V.mapAtCode c f y.toObjId = V y.toObjId := by
  cases hc : ThreadId.ofOptCode c with
  | none => rw [mapAtCode_none _ hc]
  | some x => rw [mapAtCode_some _ hc, mapAt_ne _ _ (fun e => h x hc e.symm)]

/-- WS-ZA ZA4.6: **blocking `w` on server `s` and linking it is a `LinkStep`.**
`w` was blocked on no server and `s` is live and blocked on none. -/
theorem linkStep_of_link {V0 : ReplyViews} {w s : ThreadId} {vw0 vs0 : ReplyView}
    (hc : V0.consistent) (hW0 : V0 w.toObjId = some vw0) (hWn : vw0.server = none)
    (hS0 : V0 s.toObjId = some vs0) (hSn : vs0.server = none) (hne : w ≠ s) :
    LinkStep V0 ((V0.setServer w (some s)).link w s) w s vw0 vs0 := by
  have hV1s : (V0.setServer w (some s)) s.toObjId = some vs0 := by
    unfold setServer; rw [mapAt_ne _ _ (Ne.symm hne), hS0]
  have hH : (V0.setServer w (some s)).headCodeOf s = vs0.headCode := by
    unfold headCodeOf; rw [hV1s]
  -- The old head waits on `s`, so it is neither `w` nor `s`.
  have hHd : ∀ x, ThreadId.ofOptCode vs0.headCode = some x →
      V0.waiterOf x s ∧ x ≠ w ∧ x ≠ s := by
    intro x hx
    obtain ⟨l, hQ⟩ := hc.1 s vs0 hS0
    have hwx := queue_waiter hQ (chain_head_mem (hx ▸ hQ.1))
    refine ⟨hwx, fun e => ?_, UnlinkStep.waiter_ne_s hc hwx⟩
    subst e; obtain ⟨v, hv, hb⟩ := hwx; rw [hW0] at hv; cases hv; rw [hWn] at hb; cases hb
  unfold link; simp only []; rw [hH]
  refine ⟨hW0, hWn, hS0, hSn, hne, ?_, ?_, ?_, ?_⟩
  · rw [mapAt_ne _ _ hne, mapAtCode_ne _ (fun x hx => (hHd x hx).2.1), mapAt_self]
    unfold setServer; rw [mapAt_self, hW0]; rfl
  · rw [mapAt_self, mapAtCode_ne _ (fun x hx => (hHd x hx).2.2), mapAt_ne _ _ (Ne.symm hne), hV1s]
    rfl
  · intro x hx
    obtain ⟨⟨vx, hvx, -⟩, hxw, hxs⟩ := hHd x hx
    refine ⟨vx, hvx, ?_⟩
    rw [mapAt_ne _ _ hxs, mapAtCode_self _ hx, mapAt_ne _ _ hxw]
    unfold setServer; rw [mapAt_ne _ _ hxw, hvx]; rfl
  · intro y hyw hys hyh
    rw [mapAt_ne _ _ hys, mapAtCode_ne _ (fun x hx e => hyh (by subst e; exact hx)), mapAt_ne _ _ hyw]
    unfold setServer; rw [mapAt_ne _ _ hyw]

/-- WS-ZA ZA4.6: **ending `w`'s block on server `s` and unlinking it is an
`UnlinkStep`.** -/
theorem unlinkStep_of_unlink {V0 : ReplyViews} {w s : ThreadId} {vw0 vs0 : ReplyView}
    (hc : V0.consistent) (hW0 : V0 w.toObjId = some vw0) (hWSrv : vw0.server = some s)
    (hS0 : V0 s.toObjId = some vs0) :
    UnlinkStep V0 ((V0.setServer w none).unlink w s) w s vw0 vs0 := by
  have hws : w ≠ s := fun e => by subst e; exact hc.2.2.2 _ _ hW0 hWSrv
  have hV1w : (V0.setServer w none) w.toObjId = some { vw0 with server := none } := by
    unfold setServer; rw [mapAt_self, hW0]; rfl
  have hV1 : ∀ y, y ≠ w → (V0.setServer w none) y.toObjId = V0 y.toObjId := fun y hy => by
    unfold setServer; rw [mapAt_ne _ _ hy]
  have hPv : (V0.setServer w none).prevCodeOf w = vw0.prevCode := by
    unfold prevCodeOf; rw [hV1w]
  have hNx : (V0.setServer w none).nextCodeOf w = vw0.nextCode := by
    unfold nextCodeOf; rw [hV1w]
  -- `w`'s neighbours wait on `s`: neither is `w` or `s`, and they differ.
  obtain ⟨l, hQ⟩ := hc.1 s vs0 hS0
  have hwl : w ∈ l := (hQ.2.2.2 w).mpr ⟨vw0, hW0, hWSrv⟩
  obtain ⟨hNw, hPw, hPN⟩ := chain_neighbours hQ.1 hQ.2.2.1 (fun _ e => by cases e) hwl hW0
  have hNb : ∀ z, (ThreadId.ofOptCode vw0.prevCode = some z ∨
      ThreadId.ofOptCode vw0.nextCode = some z) → V0.waiterOf z s ∧ z ≠ w ∧ z ≠ s := by
    intro z hz
    have hzw := UnlinkStep.nb_waiter hc hW0 hWSrv hS0 hz
    refine ⟨hzw, fun e => ?_, UnlinkStep.waiter_ne_s hc hzw⟩
    subst e; rcases hz with hz | hz
    · exact hPw hz
    · exact hNw hz
  unfold unlink; simp only []; rw [hPv, hNx]
  refine ⟨hW0, hWSrv, hS0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mapAt_self, mapAt_ne _ _ hws,
      mapAtCode_ne _ (fun x hx => (hNb x (Or.inr hx)).2.1),
      mapAtCode_ne _ (fun x hx => (hNb x (Or.inl hx)).2.1), hV1w]
    rfl
  · rw [mapAt_ne _ _ (Ne.symm hws), mapAt_self,
      mapAtCode_ne _ (fun x hx => (hNb x (Or.inr hx)).2.2),
      mapAtCode_ne _ (fun x hx => (hNb x (Or.inl hx)).2.2), hV1 s (Ne.symm hws), hS0]
    rfl
  · intro p hp
    obtain ⟨⟨vp, hvp, -⟩, hpw, hps⟩ := hNb p (Or.inl hp)
    refine ⟨vp, hvp, ?_⟩
    rw [mapAt_ne _ _ hpw, mapAt_ne _ _ hps,
      mapAtCode_ne _ (fun x hx e => hPN p hp (by subst e; exact hx)), mapAtCode_self _ hp, hV1 p hpw, hvp]
    rfl
  · intro n hn
    obtain ⟨⟨vn, hvn, -⟩, hnw, hns⟩ := hNb n (Or.inr hn)
    refine ⟨vn, hvn, ?_⟩
    rw [mapAt_ne _ _ hnw, mapAt_ne _ _ hns, mapAtCode_self _ hn,
      mapAtCode_ne _ (fun x hx e => hPN x hx (e ▸ hn)), hV1 n hnw, hvn]
    rfl
  · intro y hyw hys hyp hyn
    rw [mapAt_ne _ _ hyw, mapAt_ne _ _ hys, mapAtCode_ne _ (fun x hx e => hyn (by subst e; exact hx)),
      mapAtCode_ne _ (fun x hx e => hyp (by subst e; exact hx)), hV1 y hyw]

end SeLe4n.Model.ReplyViews

namespace SeLe4n.Model.SystemState

open SeLe4n
open SeLe4n.Kernel.Concurrency (CoreId)

/-! WS-ZA ZA4.6: **run-queue writes keep every reply view.**  Run-queue links
and reply-waiter links are both free in `objectsAgreeOffRunLinks`, so a step that
writes run-queue links states separately that it leaves reply views alone; the
waiter list reads nothing else (`waitersOf_of_replyViews`). -/

theorem replyViews_congr {a b : SystemState} (h : a.objects = b.objects) :
    a.replyViews = b.replyViews := by
  unfold replyViews; rw [h]

theorem mapTcbInPlace_replyViews_eq (st : SystemState) (t : ThreadId) {g : TCB → TCB}
    (hg : ∀ x, (g x).replyView = x.replyView) :
    (st.mapTcbInPlace t g).replyViews = st.replyViews := by
  rw [replyViews_mapTcbInPlace st t (gv := id) hg]
  funext k; unfold ReplyViews.mapAt; split
  · cases st.replyViews k <;> rfl
  · rfl

theorem updateTcbAtCode_replyViews_eq (st : SystemState) (c : Nat) {g : TCB → TCB}
    (hg : ∀ x, (g x).replyView = x.replyView) :
    (st.updateTcbAtCode c g).replyViews = st.replyViews := by
  unfold updateTcbAtCode; split
  · rfl
  · exact mapTcbInPlace_replyViews_eq _ _ hg

theorem runAppendLinks_replyViews_eq (st : SystemState) (c : CoreId) (t : ThreadId)
    (p : SeLe4n.Priority) : (st.runAppendLinks c t p).replyViews = st.replyViews := by
  unfold runAppendLinks; dsimp only
  rw [updateTcbAtCode_replyViews_eq _ _ ?h1, updateTcbAtCode_replyViews_eq _ _ ?h2,
    mapTcbInPlace_replyViews_eq _ _ ?h3]
  all_goals intro x; rfl

theorem runEnqueueAdmitted_replyViews_eq (st : SystemState) (c : CoreId) (t : ThreadId)
    (p : SeLe4n.Priority) : (st.runEnqueueAdmitted c t p).replyViews = st.replyViews := by
  have h := runEnqueueAdmitted_objects st c t p
  split at h
  · exact replyViews_congr h
  · exact (replyViews_congr h).trans (runAppendLinks_replyViews_eq st c t p)

theorem runEnqueueOnCore_replyViews_eq (st : SystemState) (c : CoreId) (t : ThreadId)
    (p : SeLe4n.Priority) : (st.runEnqueueOnCore c t p).replyViews = st.replyViews := by
  unfold runEnqueueOnCore; split
  · exact runEnqueueAdmitted_replyViews_eq st c t p
  · rfl

end SeLe4n.Model.SystemState

namespace SeLe4n.Model.SystemState

open SeLe4n

/-! WS-ZA ZA4.6: the link and unlink write reply-waiter links alone: each is a
frame for every reading that ignores them (`objectsAgreeOffRunLinks`, whose
erasure clears them), and each writes the object store and nothing else. -/

theorem linkReplyWaiter_objectsAgreeOffRunLinks (st : SystemState) (w s : ThreadId) :
    objectsAgreeOffRunLinks (st.linkReplyWaiter w s) st := by
  unfold linkReplyWaiter; dsimp only
  exact .trans (mapTcbInPlace_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
    (.trans (updateTcbAtCode_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
      (mapTcbInPlace_objectsAgreeOffRunLinks _ _ (fun _ => rfl)))

theorem unlinkReplyWaiter_objectsAgreeOffRunLinks (st : SystemState) (w s : ThreadId) :
    objectsAgreeOffRunLinks (st.unlinkReplyWaiter w s) st := by
  unfold unlinkReplyWaiter; dsimp only
  exact .trans (mapTcbInPlace_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
    (.trans (mapTcbInPlace_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
      (.trans (updateTcbAtCode_objectsAgreeOffRunLinks _ _ (fun _ => rfl))
        (updateTcbAtCode_objectsAgreeOffRunLinks _ _ (fun _ => rfl))))

/-- The link writes the object store alone. -/
theorem linkReplyWaiter_eq_objects (st : SystemState) (w s : ThreadId) :
    st.linkReplyWaiter w s = { st with objects := (st.linkReplyWaiter w s).objects } := by
  unfold linkReplyWaiter updateTcbAtCode mapTcbInPlace; dsimp only; split <;> rfl

/-- The unlink writes the object store alone. -/
theorem unlinkReplyWaiter_eq_objects (st : SystemState) (w s : ThreadId) :
    st.unlinkReplyWaiter w s = { st with objects := (st.unlinkReplyWaiter w s).objects } := by
  unfold unlinkReplyWaiter updateTcbAtCode mapTcbInPlace; dsimp only; split <;> split <;> rfl

theorem linkReplyWaiter_objects_invExt (st : SystemState) (w s : ThreadId)
    (h : st.objects.invExt) : (st.linkReplyWaiter w s).objects.invExt := by
  unfold linkReplyWaiter; dsimp only
  exact mapTcbInPlace_objects_invExt _ _ _
    (updateTcbAtCode_objects_invExt _ _ _ (mapTcbInPlace_objects_invExt _ _ _ h))

theorem unlinkReplyWaiter_objects_invExt (st : SystemState) (w s : ThreadId)
    (h : st.objects.invExt) : (st.unlinkReplyWaiter w s).objects.invExt := by
  unfold unlinkReplyWaiter; dsimp only
  exact mapTcbInPlace_objects_invExt _ _ _ (mapTcbInPlace_objects_invExt _ _ _
    (updateTcbAtCode_objects_invExt _ _ _ (updateTcbAtCode_objects_invExt _ _ _ h)))

end SeLe4n.Model.SystemState
