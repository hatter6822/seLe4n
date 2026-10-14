-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# The reply-waiter queues (WS-ZA ZA4.6)

A thread reply-blocked on a server (`TCB.blockingServer?`) is linked into that
server's queue of reply waiters through its own `replyWaiterPrev` /
`replyWaiterNext` links; the server holds the queue's head and its length
(`replyWaitersHead`, `replyWaitersCount`).  Priority inheritance reads the
maximum priority of a server's waiters from this queue, so it never scans the
object store for them.

The queues read five fields of a TCB, its **reply view** (`TCB.replyView`), and
nothing else.  The invariant is stated over the store's views
(`SystemState.replyViews`), so a transition that keeps every view keeps it
(`replyWaitersConsistent.of_views`), and the transitions that change views are
proven over views alone.

`replyWaitersConsistent`: every server's queue is a list of distinct threads,
linked both ways from its head, as long as its count says, whose members are
exactly the threads reply-blocked on that server; a thread reply-blocked on a
server names a live thread; a thread blocked on no server holds no
reply-waiter links; and no thread is reply-blocked on itself.
-/

namespace SeLe4n.Model

open SeLe4n

/-- What the reply-waiter queues read of one TCB: the server it is
reply-blocked on, its two links (as codes), and its own queue's head (as a
code) and length. -/
structure ReplyView where
  server : Option ThreadId
  prevCode : Nat
  nextCode : Nat
  headCode : Nat
  count : Nat
  deriving DecidableEq, Repr

/-- A TCB's reply view. -/
@[inline] def TCB.replyView (t : TCB) : ReplyView :=
  ⟨t.blockingServer?, t.replyWaiterPrevCode, t.replyWaiterNextCode,
    t.replyWaitersHeadCode, t.replyWaitersCount⟩

/-- What the reply-waiter queues read of one object slot. -/
def objReplyView : Option KernelObject → Option ReplyView
  | some (.tcb t) => some t.replyView
  | _ => none

@[simp] theorem objReplyView_tcb (t : TCB) : objReplyView (some (.tcb t)) = some t.replyView := rfl

/-- The reply view of every slot of the store: none for an empty slot or a
non-TCB object, so the slot is read kind-agnostically. -/
def SystemState.replyViews (st : SystemState) (k : ObjId) : Option ReplyView :=
  objReplyView (st.getObject? k)

/-- The views of a store, as a function of slots. -/
abbrev ReplyViews := ObjId → Option ReplyView

namespace ReplyViews

/-- `w` is reply-blocked on `s`. -/
def waiterOf (V : ReplyViews) (w s : ThreadId) : Prop :=
  ∃ v, V w.toObjId = some v ∧ v.server = some s

/-- `l` is the reply-waiter queue that starts at `cur`, its first thread naming
`prev` as its predecessor and its last thread having no successor. -/
def chain (V : ReplyViews) : Option ThreadId → Option ThreadId → List ThreadId → Prop
  | _, cur, [] => cur = none
  | prev, cur, w :: l => cur = some w ∧ ∃ v, V w.toObjId = some v ∧
      ThreadId.ofOptCode v.prevCode = prev ∧ chain V (some w) (ThreadId.ofOptCode v.nextCode) l

/-- `l` is server `s`'s queue, `vs` being `s`'s view. -/
def queue (V : ReplyViews) (s : ThreadId) (vs : ReplyView) (l : List ThreadId) : Prop :=
  V.chain none (ThreadId.ofOptCode vs.headCode) l ∧ l.length = vs.count ∧ l.Nodup ∧
  ∀ w, w ∈ l ↔ V.waiterOf w s

/-- The queues are consistent (module docstring). -/
def consistent (V : ReplyViews) : Prop :=
  (∀ (s : ThreadId) (vs : ReplyView), V s.toObjId = some vs → ∃ l, V.queue s vs l) ∧
  (∀ (w : ThreadId) (vw : ReplyView) (s : ThreadId), V w.toObjId = some vw →
    vw.server = some s → ∃ vs, V s.toObjId = some vs) ∧
  (∀ (w : ThreadId) (vw : ReplyView), V w.toObjId = some vw → vw.server = none →
    vw.prevCode = 0 ∧ vw.nextCode = 0) ∧
  (∀ (w : ThreadId) (vw : ReplyView), V w.toObjId = some vw → vw.server ≠ some w)

end ReplyViews

/-- WS-ZA ZA4.6: **the reply-waiter queues are consistent** (module docstring). -/
def SystemState.replyWaitersConsistent (st : SystemState) : Prop :=
  ReplyViews.consistent st.replyViews

/-- A step that keeps every slot's reply view keeps the queues consistent. -/
theorem SystemState.replyWaitersConsistent.of_views {st st' : SystemState}
    (h : st'.replyViews = st.replyViews) (hc : st.replyWaitersConsistent) :
    st'.replyWaitersConsistent := by
  unfold replyWaitersConsistent; rw [h]; exact hc

/-- A TCB at a slot gives that slot its view. -/
theorem SystemState.replyViews_of_tcb {st : SystemState} {k : ObjId} {t : TCB}
    (h : st.objects[k]? = some (.tcb t)) : st.replyViews k = some t.replyView := by
  unfold replyViews getObject?; rw [h]; rfl

/-- A view at a slot is the view of a TCB there. -/
theorem SystemState.tcb_of_replyViews {st : SystemState} {k : ObjId} {v : ReplyView}
    (h : st.replyViews k = some v) : ∃ t, st.objects[k]? = some (.tcb t) ∧ t.replyView = v := by
  unfold replyViews getObject? at h
  cases hO : st.objects[k]? with
  | none => rw [hO] at h; cases h
  | some o =>
    rw [hO] at h
    cases o <;> simp only [objReplyView, Option.some.injEq, reduceCtorEq] at h
    exact ⟨_, rfl, h⟩

/-- The threads reached from `cur` along successor links, at most `fuel` of them. -/
def SystemState.replyWaitersWalk (st : SystemState) : Nat → Option ThreadId → List ThreadId
  | 0, _ => []
  | _ + 1, none => []
  | n + 1, some w => w :: SystemState.replyWaitersWalk st n ((st.getTcb? w).bind TCB.replyWaiterNext)

/-- A queue is what the walk of its length reads from its start. -/
theorem SystemState.replyWaitersWalk_of_chain {st : SystemState} :
    ∀ {l : List ThreadId} {prev cur : Option ThreadId}, ReplyViews.chain st.replyViews prev cur l →
      st.replyWaitersWalk l.length cur = l
  | [], _, _, _ => rfl
  | w :: l, prev, cur, h => by
    obtain ⟨hc, v, hV, -, hRest⟩ := h
    subst hc
    obtain ⟨tw, hT, rfl⟩ := tcb_of_replyViews hV
    have hG : st.getTcb? w = some tw := (st.getTcb?_eq_some_iff w tw).mpr hT
    simp only [List.length_cons, replyWaitersWalk, hG, Option.bind_some]
    exact congrArg (w :: ·) (replyWaitersWalk_of_chain hRest)

/-- The threads reply-blocked on `s`, read from `s`'s queue: the waiters
priority inheritance takes the maximum of.  Under `replyWaitersConsistent` they
are exactly the threads reply-blocked on `s` (`mem_replyWaitersOf`), each once
(`replyWaitersOf_nodup`). -/
def SystemState.replyWaitersOf (st : SystemState) (s : ThreadId) : List ThreadId :=
  match st.getTcb? s with
  | some ts => st.replyWaitersWalk ts.replyWaitersCount ts.replyWaitersHead
  | none => []

/-- A live server's waiter list is its queue. -/
theorem SystemState.replyWaitersOf_eq_queue {st : SystemState} {s : ThreadId} {ts : TCB}
    {l : List ThreadId} (hT : st.objects[s.toObjId]? = some (.tcb ts))
    (hQ : ReplyViews.queue st.replyViews s ts.replyView l) : st.replyWaitersOf s = l := by
  have hG : st.getTcb? s = some ts := (st.getTcb?_eq_some_iff s ts).mpr hT
  unfold replyWaitersOf; rw [hG]; dsimp only
  have := replyWaitersWalk_of_chain hQ.1
  rw [hQ.2.1] at this; exact this

/-- WS-ZA ZA4.6: **the queue holds exactly the waiters.** -/
theorem SystemState.mem_replyWaitersOf {st : SystemState} (h : st.replyWaitersConsistent)
    {s w : ThreadId} : w ∈ st.replyWaitersOf s ↔ ReplyViews.waiterOf st.replyViews w s := by
  cases hG : st.getTcb? s with
  | some ts =>
    have hT := (st.getTcb?_eq_some_iff s ts).mp hG
    obtain ⟨l, hQ⟩ := h.1 s ts.replyView (replyViews_of_tcb hT)
    rw [replyWaitersOf_eq_queue hT hQ]; exact hQ.2.2.2 w
  | none =>
    unfold replyWaitersOf; rw [hG]
    simp only [List.not_mem_nil, false_iff]
    rintro ⟨vw, hW, hB⟩
    obtain ⟨vs, hS⟩ := h.2.1 w vw s hW hB
    obtain ⟨ts, hT, -⟩ := tcb_of_replyViews hS
    rw [(st.getTcb?_eq_some_iff s ts).mpr hT] at hG; cases hG

/-- Each waiter is in the list once. -/
theorem SystemState.replyWaitersOf_nodup {st : SystemState} (h : st.replyWaitersConsistent)
    (s : ThreadId) : (st.replyWaitersOf s).Nodup := by
  cases hG : st.getTcb? s with
  | some ts =>
    have hT := (st.getTcb?_eq_some_iff s ts).mp hG
    obtain ⟨l, hQ⟩ := h.1 s ts.replyView (replyViews_of_tcb hT)
    rw [replyWaitersOf_eq_queue hT hQ]; exact hQ.2.2.1
  | none => unfold replyWaitersOf; rw [hG]; exact List.nodup_nil

/-- `waiterOf` over a store's views is a TCB reply-blocked on `s`. -/
theorem SystemState.waiterOf_iff {st : SystemState} {w s : ThreadId} :
    ReplyViews.waiterOf st.replyViews w s ↔
      ∃ tw, st.objects[w.toObjId]? = some (.tcb tw) ∧ tw.blockingServer? = some s := by
  constructor
  · rintro ⟨v, hV, hB⟩
    obtain ⟨tw, hT, rfl⟩ := tcb_of_replyViews hV
    exact ⟨tw, hT, hB⟩
  · rintro ⟨tw, hT, hB⟩
    exact ⟨_, replyViews_of_tcb hT, hB⟩

/-- A thread's TCB read through its view. -/
theorem SystemState.getTcb?_map_replyView (st : SystemState) (w : ThreadId) :
    (st.getTcb? w).map TCB.replyView = st.replyViews w.toObjId := by
  unfold getTcb? replyViews getObject?
  cases st.objects[w.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- The successor the walk reads is a function of the views. -/
theorem SystemState.getTcb?_bind_replyWaiterNext (st : SystemState) (w : ThreadId) :
    (st.getTcb? w).bind TCB.replyWaiterNext =
      (st.replyViews w.toObjId).bind fun v => ThreadId.ofOptCode v.nextCode := by
  rw [← getTcb?_map_replyView]
  cases st.getTcb? w <;> rfl

/-- **The waiter list is a function of the views**: two stores with the same
reply views list the same waiters, whatever else differs. -/
theorem SystemState.replyWaitersOf_of_replyViews {st st' : SystemState}
    (h : st'.replyViews = st.replyViews) (s : ThreadId) :
    st'.replyWaitersOf s = st.replyWaitersOf s := by
  have hW : st'.replyWaitersWalk = st.replyWaitersWalk := by
    funext n cur
    induction n generalizing cur with
    | zero => rfl
    | succ n ih =>
      cases cur with
      | none => rfl
      | some w =>
        simp only [replyWaitersWalk, getTcb?_bind_replyWaiterNext, h]
        exact congrArg (w :: ·) (ih _)
  have hS : (st'.getTcb? s).map TCB.replyView = (st.getTcb? s).map TCB.replyView := by
    rw [getTcb?_map_replyView, getTcb?_map_replyView, h]
  unfold replyWaitersOf
  rw [hW]
  cases h1 : st'.getTcb? s with
  | none =>
    cases h2 : st.getTcb? s with
    | none => rfl
    | some t => rw [h1, h2] at hS; cases hS
  | some t' =>
    cases h2 : st.getTcb? s with
    | none => rw [h1, h2] at hS; cases hS
    | some t =>
      rw [h1, h2] at hS
      have hv : t'.replyView = t.replyView := Option.some.inj hS
      have hc : t'.replyWaitersCount = t.replyWaitersCount := congrArg ReplyView.count hv
      have hh : t'.replyWaitersHeadCode = t.replyWaitersHeadCode := congrArg ReplyView.headCode hv
      simp only [TCB.replyWaitersHead, hc, hh]

end SeLe4n.Model
