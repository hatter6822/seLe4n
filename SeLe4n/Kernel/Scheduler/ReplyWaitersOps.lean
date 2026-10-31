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

/-- `s`'s reply-waiter head: the thread `linkReplyWaiter _ s` relinks, which a
lock footprint that links onto `s`'s queue declares. -/
def replyWaitersHead? (st : SystemState) (s : ThreadId) : Option ThreadId :=
  ThreadId.ofOptCode (st.replyHeadCode s)

/-- `w`'s reply-waiter predecessor: one of the two threads
`unlinkReplyWaiter w _` relinks. -/
def replyWaiterPrev? (st : SystemState) (w : ThreadId) : Option ThreadId :=
  ThreadId.ofOptCode (st.replyPrevCode w)

/-- `w`'s reply-waiter successor: the other thread `unlinkReplyWaiter w _`
relinks. -/
def replyWaiterNext? (st : SystemState) (w : ThreadId) : Option ThreadId :=
  ThreadId.ofOptCode (st.replyNextCode w)

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

/-- `linkReplyWaiter`'s three TCB writes on the object table alone, given the
server's old head code. -/
def linkReplyObjects (o : Kernel.RobinHood.RHTable ObjId KernelObject) (w s : ThreadId) (h : Nat) :
    Kernel.RobinHood.RHTable ObjId KernelObject :=
  let o1 := o.mapValueAt w.toObjId (KernelObject.mapTcb fun x => { x with
    replyWaiterPrevCode := 0, replyWaiterNextCode := h })
  let o2 := if h = 0 then o1 else
    o1.mapValueAt (decode h).toObjId (KernelObject.mapTcb fun x => { x with replyWaiterPrevCode := code w })
  o2.mapValueAt s.toObjId (KernelObject.mapTcb fun x => { x with
    replyWaitersHeadCode := code w, replyWaitersCount := x.replyWaitersCount + 1 })

/-- WS-ZA ZA4.7: the compiled `linkReplyWaiter`.  The head code is read first;
the state record is then rebuilt once around the table writes, with no branch
between taking it apart and rebuilding it, so an exclusive state is rewritten
in place (the branch in `updateTcbAtCode` had made every call copy the record). -/
def linkReplyWaiterImpl (st : SystemState) (w s : ThreadId) : SystemState :=
  let h := st.replyHeadCode s
  { st with objects := linkReplyObjects st.objects w s h }

@[csimp] theorem linkReplyWaiter_eq_impl : @linkReplyWaiter = @linkReplyWaiterImpl := by
  funext st w s
  unfold linkReplyWaiter linkReplyWaiterImpl linkReplyObjects updateTcbAtCode mapTcbInPlace
  dsimp only
  split <;> rfl

/-- `unlinkReplyWaiter`'s four TCB writes on the object table alone, given
`w`'s old predecessor and successor codes. -/
def unlinkReplyObjects (o : Kernel.RobinHood.RHTable ObjId KernelObject) (w s : ThreadId) (pv nx : Nat) :
    Kernel.RobinHood.RHTable ObjId KernelObject :=
  let o1 := if pv = 0 then o else
    o.mapValueAt (decode pv).toObjId (KernelObject.mapTcb fun x => { x with replyWaiterNextCode := nx })
  let o2 := if nx = 0 then o1 else
    o1.mapValueAt (decode nx).toObjId (KernelObject.mapTcb fun x => { x with replyWaiterPrevCode := pv })
  let o3 := o2.mapValueAt s.toObjId (KernelObject.mapTcb fun x => { x with
    replyWaitersHeadCode := if pv = 0 then nx else x.replyWaitersHeadCode,
    replyWaitersCount := x.replyWaitersCount - 1 })
  o3.mapValueAt w.toObjId (KernelObject.mapTcb fun x => { x with
    replyWaiterPrevCode := 0, replyWaiterNextCode := 0 })

/-- WS-ZA ZA4.7: the compiled `unlinkReplyWaiter`, rebuilding the state record
once around the table writes, as `linkReplyWaiterImpl`. -/
def unlinkReplyWaiterImpl (st : SystemState) (w s : ThreadId) : SystemState :=
  let pv := st.replyPrevCode w
  let nx := st.replyNextCode w
  { st with objects := unlinkReplyObjects st.objects w s pv nx }

@[csimp] theorem unlinkReplyWaiter_eq_impl : @unlinkReplyWaiter = @unlinkReplyWaiterImpl := by
  funext st w s
  unfold unlinkReplyWaiter unlinkReplyWaiterImpl unlinkReplyObjects updateTcbAtCode mapTcbInPlace
  dsimp only
  split <;> split <;> rfl

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
  unfold replyViews getObject? ReplyViews.mapAt
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
  unfold replyHeadCode ReplyViews.headCodeOf replyViews getObject?
  rw [objects_get?_eq_objectEntry?]
  cases st.objectEntry? s.toObjId with
  | none => rfl
  | some e => cases h : e.value <;> simp [h, objReplyView, TCB.replyView]

theorem replyPrevCode_eq (st : SystemState) (w : ThreadId) :
    st.replyPrevCode w = ReplyViews.prevCodeOf st.replyViews w := by
  unfold replyPrevCode ReplyViews.prevCodeOf replyViews getObject?
  rw [objects_get?_eq_objectEntry?]
  cases st.objectEntry? w.toObjId with
  | none => rfl
  | some e => cases h : e.value <;> simp [h, objReplyView, TCB.replyView]

theorem replyNextCode_eq (st : SystemState) (w : ThreadId) :
    st.replyNextCode w = ReplyViews.nextCodeOf st.replyViews w := by
  unfold replyNextCode ReplyViews.nextCodeOf replyViews getObject?
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
  unfold replyViews getObject?; rw [h]

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

/-- A thread's TCB carries across any write that agrees off run-queue (and
reply-waiter) links, equal up to those links. -/
theorem getTcb?_of_objectsAgreeOffRunLinks {st st' : SystemState}
    (h : objectsAgreeOffRunLinks st' st) {t : ThreadId} {tc : TCB}
    (hT : st.getTcb? t = some tc) :
    ∃ tc', st'.getTcb? t = some tc' ∧ tc'.withoutRunLinks = tc.withoutRunLinks := by
  obtain ⟨tc', h', e⟩ := h.get_tcb ((getTcb?_eq_some_iff _ t tc).mp hT)
  exact ⟨tc', (getTcb?_eq_some_iff _ t tc').mpr h', e⟩

/-- `w`'s predecessor code, read through its TCB lookup. -/
theorem replyPrevCode_eq_getTcb? (st : SystemState) (w : ThreadId) :
    st.replyPrevCode w = ((st.getTcb? w).map TCB.replyWaiterPrevCode).getD 0 := by
  unfold replyPrevCode getTcb?
  rw [objects_get?_eq_objectEntry?]
  cases st.objectEntry? w.toObjId with
  | none => rfl
  | some e => cases h : e.value <;> simp [h]

/-- `w`'s successor code, read through its TCB lookup. -/
theorem replyNextCode_eq_getTcb? (st : SystemState) (w : ThreadId) :
    st.replyNextCode w = ((st.getTcb? w).map TCB.replyWaiterNextCode).getD 0 := by
  unfold replyNextCode getTcb?
  rw [objects_get?_eq_objectEntry?]
  cases st.objectEntry? w.toObjId with
  | none => rfl
  | some e => cases h : e.value <;> simp [h]

/-- A code-addressed write leaves every key but the one its code names. -/
theorem updateTcbAtCode_objects_ne (st : SystemState) (c : Nat) (g : TCB → TCB)
    (x : SeLe4n.ObjId) (hx : ∀ t, ThreadId.ofOptCode c = some t → x ≠ t.toObjId) :
    (st.updateTcbAtCode c g).objects[x]? = st.objects[x]? := by
  unfold updateTcbAtCode
  split
  · rfl
  · rename_i hc
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
    rw [objects_mapTcbInPlace, if_neg]
    intro e
    exact hx ⟨k⟩ rfl (by simpa [SeLe4n.Kernel.LinkedQueue.decode] using (beq_iff_eq.mp e).symm)

/-- **The unlink's footprint**: it writes the waiter, its server and the two
neighbours the waiter's own links name, and no other key. -/
theorem unlinkReplyWaiter_objects_ne (st : SystemState) (w s : ThreadId) (x : SeLe4n.ObjId)
    (hw : x ≠ w.toObjId) (hs : x ≠ s.toObjId)
    (hp : ∀ t, ThreadId.ofOptCode (st.replyPrevCode w) = some t → x ≠ t.toObjId)
    (hn : ∀ t, ThreadId.ofOptCode (st.replyNextCode w) = some t → x ≠ t.toObjId) :
    (st.unlinkReplyWaiter w s).objects[x]? = st.objects[x]? := by
  unfold unlinkReplyWaiter; dsimp only
  rw [objects_mapTcbInPlace, if_neg (fun e => hw (beq_iff_eq.mp e).symm),
    objects_mapTcbInPlace, if_neg (fun e => hs (beq_iff_eq.mp e).symm),
    updateTcbAtCode_objects_ne _ _ _ _ hn, updateTcbAtCode_objects_ne _ _ _ _ hp]

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

namespace SeLe4n.Model.SystemState

open SeLe4n

/-! WS-ZA ZA4.6: what the link and unlink leave alone, in the forms the
operations' existing proofs consume: every state field but the object store,
every object's kind, and the run-queue agreement. -/

section Fields
variable (st : SystemState) (w s : ThreadId)

@[simp] theorem linkReplyWaiter_scheduler : (st.linkReplyWaiter w s).scheduler = st.scheduler :=
  (congrArg SystemState.scheduler (linkReplyWaiter_eq_objects st w s) :)
@[simp] theorem linkReplyWaiter_machine : (st.linkReplyWaiter w s).machine = st.machine :=
  (congrArg SystemState.machine (linkReplyWaiter_eq_objects st w s) :)
@[simp] theorem linkReplyWaiter_cdt : (st.linkReplyWaiter w s).cdt = st.cdt :=
  (congrArg SystemState.cdt (linkReplyWaiter_eq_objects st w s) :)
@[simp] theorem linkReplyWaiter_lifecycle : (st.linkReplyWaiter w s).lifecycle = st.lifecycle :=
  (congrArg SystemState.lifecycle (linkReplyWaiter_eq_objects st w s) :)
@[simp] theorem linkReplyWaiter_objectIndex : (st.linkReplyWaiter w s).objectIndex = st.objectIndex :=
  (congrArg SystemState.objectIndex (linkReplyWaiter_eq_objects st w s) :)
@[simp] theorem linkReplyWaiter_objectIndexSet :
    (st.linkReplyWaiter w s).objectIndexSet = st.objectIndexSet :=
  (congrArg SystemState.objectIndexSet (linkReplyWaiter_eq_objects st w s) :)
@[simp] theorem unlinkReplyWaiter_scheduler : (st.unlinkReplyWaiter w s).scheduler = st.scheduler :=
  (congrArg SystemState.scheduler (unlinkReplyWaiter_eq_objects st w s) :)
@[simp] theorem unlinkReplyWaiter_machine : (st.unlinkReplyWaiter w s).machine = st.machine :=
  (congrArg SystemState.machine (unlinkReplyWaiter_eq_objects st w s) :)
@[simp] theorem unlinkReplyWaiter_cdt : (st.unlinkReplyWaiter w s).cdt = st.cdt :=
  (congrArg SystemState.cdt (unlinkReplyWaiter_eq_objects st w s) :)
@[simp] theorem unlinkReplyWaiter_lifecycle : (st.unlinkReplyWaiter w s).lifecycle = st.lifecycle :=
  (congrArg SystemState.lifecycle (unlinkReplyWaiter_eq_objects st w s) :)
@[simp] theorem unlinkReplyWaiter_objectIndex :
    (st.unlinkReplyWaiter w s).objectIndex = st.objectIndex :=
  (congrArg SystemState.objectIndex (unlinkReplyWaiter_eq_objects st w s) :)
@[simp] theorem unlinkReplyWaiter_objectIndexSet :
    (st.unlinkReplyWaiter w s).objectIndexSet = st.objectIndexSet :=
  (congrArg SystemState.objectIndexSet (unlinkReplyWaiter_eq_objects st w s) :)

end Fields

theorem linkReplyWaiter_kindPreservingWrite (st : SystemState) (w s : ThreadId) :
    kindPreservingWrite st (st.linkReplyWaiter w s) :=
  (linkReplyWaiter_objectsAgreeOffRunLinks st w s).kindPreserving

theorem unlinkReplyWaiter_kindPreservingWrite (st : SystemState) (w s : ThreadId) :
    kindPreservingWrite st (st.unlinkReplyWaiter w s) :=
  (unlinkReplyWaiter_objectsAgreeOffRunLinks st w s).kindPreserving

theorem mapTcbInPlace_runQueueRefined_of_runLinks (st : SystemState) (t : ThreadId)
    {g : TCB → TCB} (hg : ∀ x c, (g x).runLinkOn c = x.runLinkOn c)
    (h : st.runQueueRefined) : (st.mapTcbInPlace t g).runQueueRefined :=
  runQueueRefined_of_frame (st := st) (st' := st.mapTcbInPlace t g) (fun c x => by
      rw [runLinkOn_mapTcbInPlace_map st t g c id (fun tcb => hg tcb c) rfl x]
      try (split <;> rfl))
    rfl rfl h

theorem updateTcbAtCode_runQueueRefined_of_runLinks (st : SystemState) (k : Nat)
    {g : TCB → TCB} (hg : ∀ x c, (g x).runLinkOn c = x.runLinkOn c)
    (h : st.runQueueRefined) : (st.updateTcbAtCode k g).runQueueRefined := by
  unfold updateTcbAtCode; split
  · exact h
  · exact mapTcbInPlace_runQueueRefined_of_runLinks _ _ hg h

theorem linkReplyWaiter_runQueueRefined (st : SystemState) (w s : ThreadId)
    (h : st.runQueueRefined) : (st.linkReplyWaiter w s).runQueueRefined := by
  unfold linkReplyWaiter; dsimp only
  exact mapTcbInPlace_runQueueRefined_of_runLinks _ _ (fun _ _ => rfl)
    (updateTcbAtCode_runQueueRefined_of_runLinks _ _ (fun _ _ => rfl)
      (mapTcbInPlace_runQueueRefined_of_runLinks _ _ (fun _ _ => rfl) h))

theorem unlinkReplyWaiter_runQueueRefined (st : SystemState) (w s : ThreadId)
    (h : st.runQueueRefined) : (st.unlinkReplyWaiter w s).runQueueRefined := by
  unfold unlinkReplyWaiter; dsimp only
  exact mapTcbInPlace_runQueueRefined_of_runLinks _ _ (fun _ _ => rfl)
    (mapTcbInPlace_runQueueRefined_of_runLinks _ _ (fun _ _ => rfl)
      (updateTcbAtCode_runQueueRefined_of_runLinks _ _ (fun _ _ => rfl)
        (updateTcbAtCode_runQueueRefined_of_runLinks _ _ (fun _ _ => rfl) h)))

end SeLe4n.Model.SystemState

namespace SeLe4n.Model.SystemState

open SeLe4n

/-- WS-ZA ZA4.6: unlink `w` from the queue of the server its blocking state
named, if it named one (a reply wait recorded with no server is on no queue). -/
@[inline] def unlinkReplyWaiterOpt (st : SystemState) (w : ThreadId) :
    Option ThreadId → SystemState
  | some s => st.unlinkReplyWaiter w s
  | none => st

section Opt
variable (st : SystemState) (w : ThreadId) (s? : Option ThreadId)

theorem unlinkReplyWaiterOpt_objectsAgreeOffRunLinks :
    objectsAgreeOffRunLinks (st.unlinkReplyWaiterOpt w s?) st := by
  cases s? with
  | none => exact .refl _
  | some s => exact unlinkReplyWaiter_objectsAgreeOffRunLinks st w s

theorem unlinkReplyWaiterOpt_eq_objects :
    st.unlinkReplyWaiterOpt w s? = { st with objects := (st.unlinkReplyWaiterOpt w s?).objects } := by
  cases s? with
  | none => rfl
  | some s => exact unlinkReplyWaiter_eq_objects st w s

theorem unlinkReplyWaiterOpt_objects_invExt (h : st.objects.invExt) :
    (st.unlinkReplyWaiterOpt w s?).objects.invExt := by
  cases s? with
  | none => exact h
  | some s => exact unlinkReplyWaiter_objects_invExt st w s h

theorem unlinkReplyWaiterOpt_kindPreservingWrite :
    kindPreservingWrite st (st.unlinkReplyWaiterOpt w s?) :=
  (unlinkReplyWaiterOpt_objectsAgreeOffRunLinks st w s?).kindPreserving

theorem unlinkReplyWaiterOpt_runQueueRefined (h : st.runQueueRefined) :
    (st.unlinkReplyWaiterOpt w s?).runQueueRefined := by
  cases s? with
  | none => exact h
  | some s => exact unlinkReplyWaiter_runQueueRefined st w s h

@[simp] theorem unlinkReplyWaiterOpt_scheduler :
    (st.unlinkReplyWaiterOpt w s?).scheduler = st.scheduler := by cases s? <;> simp [unlinkReplyWaiterOpt]
@[simp] theorem unlinkReplyWaiterOpt_machine :
    (st.unlinkReplyWaiterOpt w s?).machine = st.machine := by cases s? <;> simp [unlinkReplyWaiterOpt]
@[simp] theorem unlinkReplyWaiterOpt_cdt :
    (st.unlinkReplyWaiterOpt w s?).cdt = st.cdt := by cases s? <;> simp [unlinkReplyWaiterOpt]
@[simp] theorem unlinkReplyWaiterOpt_lifecycle :
    (st.unlinkReplyWaiterOpt w s?).lifecycle = st.lifecycle := by
  cases s? <;> simp [unlinkReplyWaiterOpt]
@[simp] theorem unlinkReplyWaiterOpt_objectIndex :
    (st.unlinkReplyWaiterOpt w s?).objectIndex = st.objectIndex := by
  cases s? <;> simp [unlinkReplyWaiterOpt]

end Opt

end SeLe4n.Model.SystemState

namespace SeLe4n.Model

/-! WS-ZA ZA4.6: **agreement off the reply-waiter links.**  The link and unlink
write the four reply-waiter fields of a few TCBs and nothing else; every reading
that ignores those fields (a thread's placement, its state, its binding, any
non-TCB object) carries across them through this relation, as readings that
ignore run-queue links carry across `objectsAgreeOffRunLinks`. -/

/-- A TCB with its reply-waiter links cleared. -/
def TCB.withoutReplyLinks (t : TCB) : TCB :=
  { t with replyWaiterPrevCode := 0, replyWaiterNextCode := 0,
           replyWaitersHeadCode := 0, replyWaitersCount := 0 }

/-- An object with its reply-waiter links cleared (only a TCB has any). -/
def KernelObject.withoutReplyLinks : KernelObject → KernelObject
  | .tcb t => .tcb t.withoutReplyLinks
  | o => o

theorem KernelObject.withoutReplyLinks_eq_tcb {o : KernelObject} {t : TCB}
    (h : o.withoutReplyLinks = (KernelObject.tcb t).withoutReplyLinks) :
    ∃ t', o = .tcb t' ∧ t'.withoutReplyLinks = t.withoutReplyLinks := by
  cases o with
  | tcb t' => exact ⟨t', rfl, KernelObject.tcb.inj h⟩
  | _ => cases h

theorem KernelObject.withoutReplyLinks_eq_of_not_tcb {o o' : KernelObject}
    (h : o'.withoutReplyLinks = o.withoutReplyLinks) (hNot : ∀ t, o ≠ .tcb t) : o' = o := by
  cases o with
  | tcb t => exact absurd rfl (hNot t)
  | _ =>
    cases o' with
    | tcb t' => cases h
    | _ => exact h

end SeLe4n.Model

namespace SeLe4n.Model.SystemState

open SeLe4n

/-- Two stores hold the same objects, up to the TCBs' reply-waiter links. -/
def objectsAgreeOffReplyLinks (st' st : SystemState) : Prop :=
  ∀ x : SeLe4n.ObjId,
    (st'.objects[x]?).map KernelObject.withoutReplyLinks =
      (st.objects[x]?).map KernelObject.withoutReplyLinks

namespace objectsAgreeOffReplyLinks

theorem refl (st : SystemState) : objectsAgreeOffReplyLinks st st := fun _ => rfl

theorem symm {st st' : SystemState} (h : objectsAgreeOffReplyLinks st' st) :
    objectsAgreeOffReplyLinks st st' := fun x => (h x).symm

theorem trans {st st' st'' : SystemState} (h₂ : objectsAgreeOffReplyLinks st'' st')
    (h₁ : objectsAgreeOffReplyLinks st' st) : objectsAgreeOffReplyLinks st'' st :=
  fun x => (h₂ x).trans (h₁ x)

variable {st st' : SystemState} (h : objectsAgreeOffReplyLinks st' st)
include h

theorem get_of_not_tcb {x : SeLe4n.ObjId} {o : KernelObject}
    (hNot : ∀ t, o ≠ .tcb t) (hx : st.objects[x]? = some o) : st'.objects[x]? = some o := by
  have hx' := h x
  rw [hx] at hx'
  cases e : st'.objects[x]? with
  | none => rw [e] at hx'; cases hx'
  | some o' =>
      rw [e] at hx'
      exact congrArg some (KernelObject.withoutReplyLinks_eq_of_not_tcb (Option.some.inj hx') hNot)

theorem get_of_not_tcb' {x : SeLe4n.ObjId} {o : KernelObject}
    (hNot : ∀ t, o ≠ .tcb t) (hx : st'.objects[x]? = some o) : st.objects[x]? = some o :=
  h.symm.get_of_not_tcb hNot hx

theorem get_tcb {x : SeLe4n.ObjId} {t : TCB} (hx : st.objects[x]? = some (.tcb t)) :
    ∃ t', st'.objects[x]? = some (.tcb t') ∧ t'.withoutReplyLinks = t.withoutReplyLinks := by
  have hx' := h x
  rw [hx] at hx'
  cases e : st'.objects[x]? with
  | none => rw [e] at hx'; cases hx'
  | some o' =>
      rw [e] at hx'
      obtain ⟨t', rfl, ht⟩ := KernelObject.withoutReplyLinks_eq_tcb (Option.some.inj hx')
      exact ⟨t', rfl, ht⟩

theorem get_tcb' {x : SeLe4n.ObjId} {t' : TCB} (hx : st'.objects[x]? = some (.tcb t')) :
    ∃ t, st.objects[x]? = some (.tcb t) ∧ t'.withoutReplyLinks = t.withoutReplyLinks := by
  obtain ⟨t, ht, e⟩ := h.symm.get_tcb hx
  exact ⟨t, ht, e.symm⟩

theorem get_none_iff {x : SeLe4n.ObjId} : st'.objects[x]? = none ↔ st.objects[x]? = none := by
  have hx := h x
  constructor
  · intro e; rw [e] at hx; cases f : st.objects[x]? with
    | none => rfl
    | some _ => rw [f] at hx; cases hx
  · intro e; rw [e] at hx; cases f : st'.objects[x]? with
    | none => rfl
    | some _ => rw [f] at hx; cases hx

/-- A thread that resolves to no TCB in `st` resolves to none in `st'`. -/
theorem getTcb?_none {t : ThreadId} (hT : st.getTcb? t = none) : st'.getTcb? t = none := by
  cases hX : st'.getTcb? t with
  | none => rfl
  | some t' =>
    obtain ⟨t0, h0, -⟩ := h.get_tcb' ((getTcb?_eq_some_iff _ t t').mp hX)
    rw [(getTcb?_eq_some_iff _ t t0).mpr h0] at hT; cases hT

/-- Any reading of a thread's TCB that ignores the reply-waiter links agrees. -/
theorem getTcb?_map {α : Type _} (f : TCB → α)
    (hf : ∀ u : TCB, f u.withoutReplyLinks = f u := by intro; rfl) (t : ThreadId) :
    (st'.getTcb? t).map f = (st.getTcb? t).map f := by
  cases hT : st.getTcb? t with
  | none => rw [h.getTcb?_none hT]
  | some tc =>
    obtain ⟨tc', h', e⟩ := h.get_tcb ((getTcb?_eq_some_iff _ t tc).mp hT)
    rw [(getTcb?_eq_some_iff _ t tc').mpr h']
    show some (f tc') = some (f tc)
    rw [← hf tc', ← hf tc, e]

end objectsAgreeOffReplyLinks

theorem mapTcbInPlace_objectsAgreeOffReplyLinks (st : SystemState) (tid : ThreadId)
    {g : TCB → TCB} (hg : ∀ x, (g x).withoutReplyLinks = x.withoutReplyLinks) :
    objectsAgreeOffReplyLinks (st.mapTcbInPlace tid g) st := by
  intro x
  rw [objects_mapTcbInPlace]
  split
  · cases st.objects[x]? with
    | none => rfl
    | some o => cases o <;> simp [KernelObject.mapTcb, KernelObject.withoutReplyLinks, hg _]
  · rfl

theorem updateTcbAtCode_objectsAgreeOffReplyLinks (st : SystemState) (k : Nat)
    {g : TCB → TCB} (hg : ∀ x, (g x).withoutReplyLinks = x.withoutReplyLinks) :
    objectsAgreeOffReplyLinks (st.updateTcbAtCode k g) st := by
  unfold updateTcbAtCode; split
  · exact .refl _
  · exact mapTcbInPlace_objectsAgreeOffReplyLinks _ _ hg

theorem linkReplyWaiter_objectsAgreeOffReplyLinks (st : SystemState) (w s : ThreadId) :
    objectsAgreeOffReplyLinks (st.linkReplyWaiter w s) st := by
  unfold linkReplyWaiter; dsimp only
  exact .trans (mapTcbInPlace_objectsAgreeOffReplyLinks _ _ (fun _ => rfl))
    (.trans (updateTcbAtCode_objectsAgreeOffReplyLinks _ _ (fun _ => rfl))
      (mapTcbInPlace_objectsAgreeOffReplyLinks _ _ (fun _ => rfl)))

theorem unlinkReplyWaiter_objectsAgreeOffReplyLinks (st : SystemState) (w s : ThreadId) :
    objectsAgreeOffReplyLinks (st.unlinkReplyWaiter w s) st := by
  unfold unlinkReplyWaiter; dsimp only
  exact .trans (mapTcbInPlace_objectsAgreeOffReplyLinks _ _ (fun _ => rfl))
    (.trans (mapTcbInPlace_objectsAgreeOffReplyLinks _ _ (fun _ => rfl))
      (.trans (updateTcbAtCode_objectsAgreeOffReplyLinks _ _ (fun _ => rfl))
        (updateTcbAtCode_objectsAgreeOffReplyLinks _ _ (fun _ => rfl))))

theorem unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks (st : SystemState) (w : ThreadId)
    (s? : Option ThreadId) : objectsAgreeOffReplyLinks (st.unlinkReplyWaiterOpt w s?) st := by
  cases s? with
  | none => exact .refl _
  | some s => exact unlinkReplyWaiter_objectsAgreeOffReplyLinks st w s

end SeLe4n.Model.SystemState

namespace SeLe4n.Model.SystemState

open SeLe4n

/-- A step that writes only reply-waiter links and no scheduler field is a
run-queue stage: every run link, current slot and thread state reads as before. -/
theorem RunQueueStage.of_objectsAgreeOffReplyLinks {st st' : SystemState}
    (hA : objectsAgreeOffReplyLinks st' st) (hS : st'.scheduler = st.scheduler)
    (hI : st.objects.invExt → st'.objects.invExt)
    (hT : st'.referenceTables = st.referenceTables) : RunQueueStage st st' := by
  have hL : ∀ c t, st'.runLinkOn c t = st.runLinkOn c t := by
    intro c t
    have e := hA.getTcb?_map (fun x => x.runLinkOn c) (t := t)
    unfold runLinkOn
    cases h1 : st'.getTcb? t <;> cases h2 : st.getTcb? t <;> rw [h1, h2] at e <;>
      first | rfl | cases e | exact Option.some.inj e
  have hM : StateMono st st' :=
    StateMono.of_stateFields (fun t => hA.getTcb?_map _ (t := t))
  exact ⟨.of_tableFrame (fun h r => ⟨hI h, runQueueRefined_of_frame hL (by rw [hS]) (by rw [hS]) r⟩)
      (fun _ => .of_map (g := KernelObject.withoutReplyLinks) (fun o => by cases o <;> rfl) hT hA)
      (fun _ => ⟨.of_map KernelObject.withoutReplyLinks (fun o _ => by cases o <;> rfl) hA,
        by rw [hS]⟩)
      (fun _ => Kernel.RefillViewsKept.of_map KernelObject.withoutReplyLinks
        (fun o => by cases o <;> rfl) hA)
      (fun _ => Kernel.YieldLinksKept.of_map KernelObject.withoutReplyLinks
        (fun o => by cases o <;> rfl) hA),
    fun _ _ _ _ d => currentDequeuedUniqueExcept_of_eq (by rw [hS]) hL hM d, fun _ _ => hM⟩

theorem linkReplyWaiter_runQueueStage (st : SystemState) (w s : ThreadId) :
    RunQueueStage st (st.linkReplyWaiter w s) :=
  .of_objectsAgreeOffReplyLinks (linkReplyWaiter_objectsAgreeOffReplyLinks st w s)
    (linkReplyWaiter_scheduler st w s) (linkReplyWaiter_objects_invExt st w s)
    ((congrArg SystemState.referenceTables (linkReplyWaiter_eq_objects st w s)).trans rfl)

theorem unlinkReplyWaiter_runQueueStage (st : SystemState) (w s : ThreadId) :
    RunQueueStage st (st.unlinkReplyWaiter w s) :=
  .of_objectsAgreeOffReplyLinks (unlinkReplyWaiter_objectsAgreeOffReplyLinks st w s)
    (unlinkReplyWaiter_scheduler st w s) (unlinkReplyWaiter_objects_invExt st w s)
    ((congrArg SystemState.referenceTables (unlinkReplyWaiter_eq_objects st w s)).trans rfl)

theorem unlinkReplyWaiterOpt_runQueueStage (st : SystemState) (w : ThreadId)
    (s? : Option ThreadId) : RunQueueStage st (st.unlinkReplyWaiterOpt w s?) := by
  cases s? with
  | none => exact .refl _
  | some s => exact unlinkReplyWaiter_runQueueStage st w s

end SeLe4n.Model.SystemState
