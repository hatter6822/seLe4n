/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
-- STATUS: staged for WS-ZA ZA5.4 part 24 — the non-head notification unlink keeps `notificationWaiterConsistent`, staged with `IPC.Invariant.CancelAllReachability`, its one consumer.
import SeLe4n.Kernel.IPC.Invariant.NotificationQueue

/-!
# A waiter unlinked from the middle or the back of a notification queue

WS-ZA ZA5.4 part 24: a thread blocked on a notification leaves its queue, as a
cancel takes it off (`removeFromNotificationWaitQueue`, seL4's `tcbEPDequeue`),
wherever it waits.  The head's removal is the signal's pop
(`notificationWaiterConsistent_of_headPop`); this module is the other case — a
waiter with a predecessor, whose predecessor is pointed at its successor and its
successor (or, at the back of the queue, the queue's tail) back at its
predecessor — stated, as the other shapes are, over the objects the step leaves
behind (`notificationWaiterConsistent_of_unlink`).

* **The neighbours are other threads.**  A waiter the queue reaches is not its
  own predecessor, nor its predecessor's predecessor
  (`notificationQueueReaches_noShortPrevCycle`), so a waiter's predecessor, the
  waiter and its successor are three threads
  (`notificationWaiter_neighbours_distinct`).
* **Membership.**  Every thread the old queue reached, other than the waiter, is
  reached in the new one: the waiter's predecessor now links to its successor.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- A thread a notification queue reaches has a queue head before it: the
notification is present and its queue is not empty. -/
theorem notificationQueueReaches_head {st : SystemState} {n : SeLe4n.ObjId}
    {u : SeLe4n.ThreadId} (hR : notificationQueueReaches st n u) :
    ∃ ntfn h, st.objects[n]? = some (.notification ntfn) ∧ ntfn.waitHead = some h := by
  induction hR with
  | head hN hH => exact ⟨_, _, hN, hH⟩
  | next _ _ _ ih => exact ih

/-- **No waiter the queue reaches closes a predecessor cycle of length one or
two**: it is not its own predecessor, and its predecessor's predecessor is not
it.  By induction along the queue: the head has no predecessor, and a successor's
predecessor is the thread that names it. -/
theorem notificationQueueReaches_noShortPrevCycle {st : SystemState} {nid : SeLe4n.ObjId}
    (hInv : notificationWaiterConsistent st) {u : SeLe4n.ThreadId}
    (hR : notificationQueueReaches st nid u) :
    ∀ tu, st.objects[u.toObjId]? = some (.tcb tu) →
      tu.ntfnPrev ≠ some u ∧ ∀ a ta, tu.ntfnPrev = some a →
        st.objects[a.toObjId]? = some (.tcb ta) → ta.ntfnPrev ≠ some u := by
  induction hR with
  | head hN hH =>
    intro tu hTu
    rw [hInv.headNoPrev hN hH hTu]
    exact ⟨fun h => (by cases h), fun _ _ h _ => (by cases h)⟩
  | @next a b ta hRa hTa hNx ih =>
    intro tb hTb
    obtain ⟨ta', hTa', hBa⟩ := notificationQueueReaches_blocked hInv hRa
    rw [hTa] at hTa'; cases hTa'
    obtain ⟨_, _, _, _, hNextA⟩ := hInv.2.1 a ta _ hTa hBa
    obtain ⟨-, tb', hTb', -, hPb⟩ := hNextA b hNx
    rw [hTb] at hTb'; cases hTb'
    obtain ⟨ih1, ih2⟩ := ih ta hTa
    refine ⟨fun e => ?_, fun a' ta2 hA hTa2 e => ?_⟩
    · rw [hPb] at e; cases e
      rw [hTa] at hTb; cases hTb
      exact ih1 hPb
    · rw [hPb] at hA; cases hA
      rw [hTa] at hTa2; cases hTa2
      exact ih2 b tb e hTb hPb

/-- **A waiter's predecessor, the waiter and its successor are three threads.** -/
theorem notificationWaiter_neighbours_distinct {st : SystemState} {nid : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} {ttcb : TCB} (hInv : notificationWaiterConsistent st)
    (hT : st.objects[t.toObjId]? = some (.tcb ttcb))
    (hB : ttcb.ipcState = .blockedOnNotification nid) :
    (∀ p, ttcb.ntfnPrev = some p → p ≠ t) ∧
      (∀ b, ttcb.ntfnNext = some b → b ≠ t ∧ ∀ p, ttcb.ntfnPrev = some p → b ≠ p) := by
  obtain ⟨hP1, hP2⟩ := notificationQueueReaches_noShortPrevCycle hInv (hInv.reaches hT hB) ttcb hT
  obtain ⟨_, _, _, _, hNext⟩ := hInv.2.1 t ttcb nid hT hB
  refine ⟨fun p hp e => hP1 (e ▸ hp), fun b hb => ⟨fun e => ?_, fun p hp e => ?_⟩⟩
  · subst e
    obtain ⟨-, tb, hTb, -, hPb⟩ := hNext b hb
    rw [hT] at hTb; cases hTb
    exact hP1 hPb
  · subst e
    obtain ⟨-, tb, hTb, -, hPb⟩ := hNext b hb
    exact hP2 b tb hp hTb hPb

/-- **A waiter with a predecessor unlinked from its notification's queue**
(`removeFromNotificationWaitQueue` when the waiter is not the head): the
notification keeps its head, and its tail is the waiter's predecessor when the
waiter ended the queue; the waiter is blocked on no notification and holds no
links; the predecessor keeps its state and predecessor link and now links to the
waiter's successor; the successor keeps its state and successor link and now
links back to the predecessor; and no other object changed. -/
theorem notificationWaiterConsistent_of_unlink {st st' : SystemState}
    {nid : SeLe4n.ObjId} {ntfn n' : Notification} {t p : SeLe4n.ThreadId} {ttcb : TCB}
    (hInv : notificationWaiterConsistent st)
    (hN : st.objects[nid]? = some (.notification ntfn))
    (hT : st.objects[t.toObjId]? = some (.tcb ttcb))
    (hBt : ttcb.ipcState = .blockedOnNotification nid)
    (hPrev : ttcb.ntfnPrev = some p)
    (hPostN : st'.objects[nid]? = some (.notification n'))
    (hHd' : n'.waitHead = ntfn.waitHead)
    (hTl' : n'.waitTail = if ttcb.ntfnNext.isSome then ntfn.waitTail else some p)
    (hPostT : ∃ x, st'.objects[t.toObjId]? = some (.tcb x) ∧
      (∀ oid, x.ipcState ≠ .blockedOnNotification oid) ∧ x.ntfnPrev = none ∧ x.ntfnNext = none)
    (hPostP : ∀ tp, st.objects[p.toObjId]? = some (.tcb tp) →
      ∃ tp', st'.objects[p.toObjId]? = some (.tcb tp') ∧ tp'.ipcState = tp.ipcState ∧
        tp'.ntfnPrev = tp.ntfnPrev ∧ tp'.ntfnNext = ttcb.ntfnNext)
    (hPostS : ∀ b tb, ttcb.ntfnNext = some b → st.objects[b.toObjId]? = some (.tcb tb) →
      ∃ tb', st'.objects[b.toObjId]? = some (.tcb tb') ∧ tb'.ipcState = tb.ipcState ∧
        tb'.ntfnPrev = some p ∧ tb'.ntfnNext = tb.ntfnNext)
    (hPostO : ∀ x, x ≠ nid → x ≠ t.toObjId → x ≠ p.toObjId →
      (∀ b, ttcb.ntfnNext = some b → x ≠ b.toObjId) → st'.objects[x]? = st.objects[x]?) :
    notificationWaiterConsistent st' := by
  have hInj : ∀ (x y : SeLe4n.ThreadId), x ≠ y → x.toObjId ≠ y.toObjId :=
    fun x y hne e => hne (SeLe4n.ThreadId.toObjId_injective _ _ e)
  obtain ⟨hpt, hbD⟩ := notificationWaiter_neighbours_distinct hInv hT hBt
  have hpt' : p ≠ t := hpt p hPrev
  obtain ⟨hIff, hHeadC, hTailC⟩ := hInv.1 nid ntfn hN
  obtain ⟨n0, hN0, hPrevT, hTailT, hNextT⟩ := hInv.2.1 t ttcb nid hT hBt
  rw [hN] at hN0; cases hN0
  have hNotHead : ntfn.waitHead ≠ some t := fun e => by
    rw [hInv.headNoPrev hN e hT] at hPrev; cases hPrev
  obtain ⟨tp, hTp, hBp, hNp⟩ : ∃ tp, st.objects[p.toObjId]? = some (.tcb tp) ∧
      tp.ipcState = .blockedOnNotification nid ∧ tp.ntfnNext = some t := by
    rcases hPrevT with e | ⟨a, ta, ha, hTa, hBa, hNa⟩
    · exact absurd e hNotHead
    · rw [hPrev] at ha; cases ha; exact ⟨ta, hTa, hBa, hNa⟩
  have hSucc : ∀ b, ttcb.ntfnNext = some b → b ≠ t ∧ b ≠ p ∧ ntfn.waitHead ≠ some b ∧
      ∃ tb, st.objects[b.toObjId]? = some (.tcb tb) ∧
        tb.ipcState = .blockedOnNotification nid ∧ tb.ntfnPrev = some t := by
    intro b hb
    obtain ⟨hbt, hbp⟩ := hbD b hb
    obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNextT b hb
    exact ⟨hbt, hbp p hPrev, hne, tb, hTb, hBb, hPb⟩
  have hNid : ∀ (x : SeLe4n.ThreadId) (tx : TCB), st.objects[x.toObjId]? = some (.tcb tx) →
      x.toObjId ≠ nid := fun x tx hx e => by rw [e, hN] at hx; cases hx
  obtain ⟨tx0, hTx0, hNBt, hPt0, hNt0⟩ := hPostT
  -- Every TCB other than the waiter: its state kept, and only the predecessor's
  -- successor link and the successor's predecessor link moved.
  have hCorr : ∀ (x : SeLe4n.ThreadId) (tx : TCB), st.objects[x.toObjId]? = some (.tcb tx) →
      x ≠ t → ∃ tx', st'.objects[x.toObjId]? = some (.tcb tx') ∧ tx'.ipcState = tx.ipcState ∧
        (x ≠ p → tx'.ntfnNext = tx.ntfnNext) ∧ (x = p → tx'.ntfnNext = ttcb.ntfnNext) ∧
        (ttcb.ntfnNext ≠ some x → tx'.ntfnPrev = tx.ntfnPrev) ∧
        (ttcb.ntfnNext = some x → tx'.ntfnPrev = some p) := by
    intro x tx hx hxt
    by_cases hxp : x = p
    · rw [hxp] at hx ⊢
      rw [hTp] at hx; cases hx
      obtain ⟨tp', h1, h2, h3, h4⟩ := hPostP tp hTp
      exact ⟨tp', h1, h2, fun e => absurd rfl e, fun _ => h4, fun _ => h3,
        fun hs => absurd rfl (hSucc p hs).2.1⟩
    · by_cases hs : ttcb.ntfnNext = some x
      · obtain ⟨tb', h1, h2, h3, h4⟩ := hPostS x tx hs hx
        exact ⟨tb', h1, h2, fun _ => h4, fun e => absurd e hxp, fun e => absurd hs e, fun _ => h3⟩
      · refine ⟨tx, ?_, rfl, fun _ => rfl, fun e => absurd e hxp, fun _ => rfl,
          fun e => absurd e hs⟩
        rw [hPostO _ (hNid x tx hx) (hInj x t hxt) (hInj x p hxp)
          (fun b hb => hInj x b (fun e => hs (e ▸ hb)))]
        exact hx
  have hCorrB : ∀ (x : SeLe4n.ThreadId) (tx' : TCB), st'.objects[x.toObjId]? = some (.tcb tx') →
      x ≠ t → ∃ tx, st.objects[x.toObjId]? = some (.tcb tx) ∧ tx'.ipcState = tx.ipcState ∧
        (x ≠ p → tx'.ntfnNext = tx.ntfnNext) ∧ (x = p → tx'.ntfnNext = ttcb.ntfnNext) ∧
        (ttcb.ntfnNext ≠ some x → tx'.ntfnPrev = tx.ntfnPrev) ∧
        (ttcb.ntfnNext = some x → tx'.ntfnPrev = some p) := by
    intro x tx' hx hxt
    obtain ⟨tx, hTx⟩ : ∃ tx, st.objects[x.toObjId]? = some (.tcb tx) := by
      by_cases hxp : x = p
      · rw [hxp]; exact ⟨tp, hTp⟩
      · by_cases hs : ttcb.ntfnNext = some x
        · obtain ⟨-, -, -, tb, hTb, -⟩ := hSucc x hs; exact ⟨tb, hTb⟩
        · have h1 : x.toObjId ≠ nid := by intro e; rw [e, hPostN] at hx; cases hx
          exact ⟨tx', by
            rw [← hPostO _ h1 (hInj x t hxt) (hInj x p hxp)
              (fun b hb => hInj x b (fun e => hs (e ▸ hb)))]
            exact hx⟩
    obtain ⟨t2, hT2, rest⟩ := hCorr x tx hTx hxt
    rw [hx] at hT2; cases hT2
    exact ⟨tx, hTx, rest⟩
  have hPresX : ∀ (x : SeLe4n.ThreadId) (tx : TCB), st.objects[x.toObjId]? = some (.tcb tx) →
      x ≠ t → x ≠ p → ttcb.ntfnNext ≠ some x → st'.objects[x.toObjId]? = some (.tcb tx) := by
    intro x tx hx hxt hxp hs
    rw [hPostO _ (hNid x tx hx) (hInj x t hxt) (hInj x p hxp)
      (fun b hb => hInj x b (fun e => hs (e ▸ hb)))]
    exact hx
  -- A TCB blocked on another notification is none of the three.
  have hNeOfOther : ∀ (x : SeLe4n.ThreadId) (tx : TCB) (oid : SeLe4n.ObjId),
      st.objects[x.toObjId]? = some (.tcb tx) → tx.ipcState = .blockedOnNotification oid →
      oid ≠ nid → x ≠ t ∧ x ≠ p ∧ ttcb.ntfnNext ≠ some x := by
    intro x tx oid hx hb hne
    refine ⟨fun e => ?_, fun e => ?_, fun hs => ?_⟩
    · rw [e, hT] at hx; cases hx; rw [hBt] at hb; cases hb; exact hne rfl
    · rw [e, hTp] at hx; cases hx; rw [hBp] at hb; cases hb; exact hne rfl
    · obtain ⟨-, -, -, tb, hTb, hBb, -⟩ := hSucc x hs
      rw [hx] at hTb; cases hTb; rw [hb] at hBb; cases hBb; exact hne rfl
  -- Any other notification is unchanged: the keys written hold TCBs.
  have hKeyO : ∀ (oid : SeLe4n.ObjId), (∃ n, st.objects[oid]? = some (.notification n) ∨
      st'.objects[oid]? = some (.notification n)) → oid ≠ nid →
      st'.objects[oid]? = st.objects[oid]? := by
    intro oid ⟨n, hn⟩ hO
    obtain ⟨tp', hTp', -⟩ := hPostP tp hTp
    refine hPostO oid hO ?_ ?_ ?_
    · intro e; subst e; rcases hn with hn | hn
      · rw [hT] at hn; cases hn
      · rw [hTx0] at hn; cases hn
    · intro e; subst e; rcases hn with hn | hn
      · rw [hTp] at hn; cases hn
      · rw [hTp'] at hn; cases hn
    · intro b hb e; subst e
      obtain ⟨-, -, -, tb, hTb, -⟩ := hSucc b hb
      rcases hn with hn | hn
      · rw [hTb] at hn; cases hn
      · obtain ⟨tb', hTb', -⟩ := hPostS b tb hb hTb
        rw [hTb'] at hn; cases hn
  have hTidNeT : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (oid : SeLe4n.ObjId),
      st'.objects[tid.toObjId]? = some (.tcb tcb) → tcb.ipcState = .blockedOnNotification oid →
      tid ≠ t := by
    intro tid tcb oid hPt hB e; subst e; rw [hTx0] at hPt; cases hPt; exact hNBt oid hB
  have hHeadSome : ∃ h, ntfn.waitHead = some h := by
    obtain ⟨n1, h1, hN1, hH1⟩ := notificationQueueReaches_head (hInv.reaches hT hBt)
    rw [hN] at hN1; cases hN1; exact ⟨h1, hH1⟩
  refine ⟨fun oid n hPn => ?_, fun tid tcb oid hPt hB => ?_, fun tid tcb oid hPt hB => ?_,
    fun oid n hd tcb hPn hHd hPt => ?_, fun tid tcb hPt hNB => ?_⟩
  -- The notification's three clauses.
  · by_cases hO : oid = nid
    · subst hO
      rw [hPostN] at hPn; cases hPn
      obtain ⟨h0, hH0⟩ := hHeadSome
      have hTailSome : ntfn.waitTail ≠ none := fun e => by
        rw [← hIff, hH0] at e; cases e
      refine ⟨?_, fun h hh => ?_, fun tl htl => ?_⟩
      · rw [hHd', hTl', hH0]
        cases ttcb.ntfnNext with
        | none => simp
        | some b => simp [hTailSome]
      · rw [hHd'] at hh
        obtain ⟨th, hTh, hBh⟩ := hHeadC h hh
        have hht : h ≠ t := fun e => hNotHead (e ▸ hh)
        obtain ⟨th', hTh', hI, -⟩ := hCorr h th hTh hht
        exact ⟨th', hTh', hI.trans hBh⟩
      · rw [hTl'] at htl
        cases hnx : ttcb.ntfnNext with
        | none =>
          rw [hnx] at htl; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at htl
          cases htl
          obtain ⟨tp', hTp', hI, -, hNx⟩ := hPostP tp hTp
          exact ⟨tp', hTp', hI.trans hBp, hNx.trans hnx⟩
        | some b =>
          rw [hnx] at htl; simp only [Option.isSome_some, ↓reduceIte] at htl
          obtain ⟨tt, hTt, hBtl, hNtl⟩ := hTailC tl htl
          have htt : tl ≠ t := by
            intro e; rw [e, hT] at hTt; cases hTt; rw [hnx] at hNtl; cases hNtl
          have htp : tl ≠ p := by
            intro e; rw [e, hTp] at hTt; cases hTt; rw [hNp] at hNtl; cases hNtl
          obtain ⟨tt', hTt', hI, hNx, -⟩ := hCorr tl tt hTt htt
          exact ⟨tt', hTt', hI.trans hBtl, (hNx htp).trans hNtl⟩
    · have hPn' : st.objects[oid]? = some (.notification n) := by
        rw [← hKeyO oid ⟨n, Or.inr hPn⟩ hO]; exact hPn
      obtain ⟨hIff2, hH2, hT2⟩ := hInv.1 oid n hPn'
      refine ⟨hIff2, fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨tx, hTx, hBx⟩ := hH2 x hx
        obtain ⟨a1, a2, a3⟩ := hNeOfOther x tx oid hTx hBx hO
        exact ⟨tx, hPresX x tx hTx a1 a2 a3, hBx⟩
      · obtain ⟨tx, hTx, hBx, hNx⟩ := hT2 x hx
        obtain ⟨a1, a2, a3⟩ := hNeOfOther x tx oid hTx hBx hO
        exact ⟨tx, hPresX x tx hTx a1 a2 a3, hBx, hNx⟩
  -- A blocked thread's neighbours.
  · have hth := hTidNeT tid tcb oid hPt hB
    obtain ⟨tx, hPre, hI, hNxNp, hNxP, hPvNs, hPvS⟩ := hCorrB tid tcb hPt hth
    have hBx : tx.ipcState = .blockedOnNotification oid := hI ▸ hB
    obtain ⟨n1, hN1, hPrevX, hTailX, hNextX⟩ := hInv.2.1 tid tx oid hPre hBx
    by_cases hO : oid = nid
    · subst hO
      rw [hN] at hN1; cases hN1
      obtain ⟨tp', hTp', hIp, -, hNp'⟩ := hPostP tp hTp
      refine ⟨n', hPostN, ?_, fun hnone => ?_, fun b hb => ?_⟩
      · by_cases hs : ttcb.ntfnNext = some tid
        · exact Or.inr ⟨p, tp', hPvS hs, hTp', hIp.trans hBp, hNp'.trans hs⟩
        · rcases hPrevX with hh | ⟨a, ta, ha, hTa, hBa, hNa⟩
          · exact Or.inl (hHd'.trans hh)
          · have hat : a ≠ t := by
              intro e; rw [e, hT] at hTa; cases hTa; exact hs hNa
            have hap : a ≠ p := by
              intro e; rw [e, hTp] at hTa; cases hTa; rw [hNp] at hNa; cases hNa; exact hth rfl
            obtain ⟨ta', hTa', hIa, hNa', -⟩ := hCorr a ta hTa hat
            exact Or.inr ⟨a, ta', (hPvNs hs).trans ha, hTa', hIa.trans hBa, (hNa' hap).trans hNa⟩
      · rw [hTl']
        by_cases htp : tid = p
        · rw [hNxP htp] at hnone; rw [hnone, htp]; rfl
        · have ht := hTailX ((hNxNp htp).symm.trans hnone)
          cases hnx : ttcb.ntfnNext with
          | none => rw [hTailT hnx] at ht; cases ht; exact absurd rfl hth
          | some b => simp only [Option.isSome_some, ↓reduceIte]; exact ht
      · by_cases htp : tid = p
        · rw [hNxP htp] at hb
          obtain ⟨-, -, hne, tb, hTb, hBb, -⟩ := hSucc b hb
          obtain ⟨tb', hTb', hIb, hPb', -⟩ := hPostS b tb hb hTb
          exact ⟨hHd' ▸ hne, tb', hTb', hIb.trans hBb, hPb'.trans (by rw [htp])⟩
        · rw [hNxNp htp] at hb
          obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNextX b hb
          have hbt : b ≠ t := by
            intro e; rw [e, hT] at hTb; cases hTb; rw [hPrev] at hPb; cases hPb; exact htp rfl
          have hns : ttcb.ntfnNext ≠ some b := by
            intro hnx
            obtain ⟨-, -, -, tb2, hTb2, -, hPb2⟩ := hSucc b hnx
            rw [hTb] at hTb2; cases hTb2; rw [hPb] at hPb2; cases hPb2; exact hth rfl
          obtain ⟨tb', hTb', hIb, -, -, hPb1, -⟩ := hCorr b tb hTb hbt
          exact ⟨hHd' ▸ hne, tb', hTb', hIb.trans hBb, (hPb1 hns).trans hPb⟩
    · obtain ⟨a1, a2, a3⟩ := hNeOfOther tid tx oid hPre hBx hO
      have hEq := hPresX tid tx hPre a1 a2 a3
      rw [hPt] at hEq; cases hEq
      refine ⟨n1, by rw [hKeyO oid ⟨n1, Or.inl hN1⟩ hO]; exact hN1, ?_, hTailX, fun b hb => ?_⟩
      · rcases hPrevX with hh | ⟨a, ta, ha, hTa, hBa, hNa⟩
        · exact Or.inl hh
        · obtain ⟨c1, c2, c3⟩ := hNeOfOther a ta oid hTa hBa hO
          exact Or.inr ⟨a, ta, ha, hPresX a ta hTa c1 c2 c3, hBa, hNa⟩
      · obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNextX b hb
        obtain ⟨c1, c2, c3⟩ := hNeOfOther b tb oid hTb hBb hO
        exact ⟨hne, tb, hPresX b tb hTb c1 c2 c3, hBb, hPb⟩
  -- Membership.
  · have hth := hTidNeT tid tcb oid hPt hB
    obtain ⟨tx, hPre, hI, -⟩ := hCorrB tid tcb hPt hth
    have hBx : tx.ipcState = .blockedOnNotification oid := hI ▸ hB
    have hR := hInv.reaches hPre hBx
    by_cases hO : oid = nid
    · subst hO
      -- Every thread the old queue reached, but the waiter, is reached anew;
      -- past the waiter, its successor is reached from its predecessor.
      have hKey : ∀ u, notificationQueueReaches st oid u →
          (u ≠ t → notificationQueueReaches st' oid u) ∧
          (u = t → ∀ b, ttcb.ntfnNext = some b → notificationQueueReaches st' oid b) := by
        intro u hu
        induction hu with
        | head hN1 hH1 =>
          rw [hN] at hN1; cases hN1
          refine ⟨fun _ => .head hPostN (hHd'.trans hH1), fun e => absurd (e ▸ hH1) hNotHead⟩
        | @next a c ta hRa hTa hNx ih =>
          -- A step into the waiter comes from its predecessor.
          have hIntoT : c = t → ∀ b, ttcb.ntfnNext = some b →
              notificationQueueReaches st' oid b := by
            intro hct b hb
            have hat : a ≠ t := by
              intro e; rw [e, hT] at hTa; cases hTa; rw [hct] at hNx
              exact (hSucc b hb).1 (by rw [hNx] at hb; cases hb; rfl)
            obtain ⟨ta', hTa'', hBa⟩ := notificationQueueReaches_blocked hInv hRa
            rw [hTa] at hTa''; cases hTa''
            obtain ⟨_, _, _, _, hNextA⟩ := hInv.2.1 a ta _ hTa hBa
            obtain ⟨-, tc, hTc, -, hPc⟩ := hNextA c hNx
            rw [hct, hT] at hTc; cases hTc
            rw [hPrev] at hPc; cases hPc
            obtain ⟨tp', hTp', -, -, hNp'⟩ := hPostP ta hTa
            exact .next ((ih.1 hat)) hTp' (hNp'.trans hb)
          refine ⟨fun hct => ?_, hIntoT⟩
          by_cases hat : a = t
          · rw [hat, hT] at hTa; cases hTa
            exact ih.2 hat c hNx
          · have hap : a ≠ p := by
              intro e; rw [e, hTp] at hTa; cases hTa; rw [hNp] at hNx; cases hNx
              exact hct rfl
            obtain ⟨ta', hTa', -, hNa', -⟩ := hCorr a ta hTa hat
            exact .next (ih.1 hat) hTa' ((hNa' hap).trans hNx)
      exact (hKey tid hR).1 hth
    · refine hR.transport (fun n1 h1 hN1 hH1 => ?_) (fun a _ ta hRa hTa hNx hRa' => ?_)
      · exact .head (by rw [hKeyO oid ⟨n1, Or.inl hN1⟩ hO]; exact hN1) hH1
      · obtain ⟨ta', hTa', hBa⟩ := notificationQueueReaches_blocked hInv hRa
        rw [hTa] at hTa'; cases hTa'
        obtain ⟨c1, c2, c3⟩ := hNeOfOther a ta oid hTa hBa hO
        exact .next hRa' (hPresX a ta hTa c1 c2 c3) hNx
  -- The head has no predecessor.
  · by_cases hO : oid = nid
    · subst hO
      rw [hPostN] at hPn; cases hPn
      rw [hHd'] at hHd
      have hdt : hd ≠ t := fun e => hNotHead (e ▸ hHd)
      obtain ⟨tx, hTx, -, -, -, hP1, -⟩ := hCorrB hd tcb hPt hdt
      have hns : ttcb.ntfnNext ≠ some hd := fun hs => (hSucc hd hs).2.2.1 hHd
      rw [hP1 hns]
      exact hInv.headNoPrev hN hHd hTx
    · have hPn' : st.objects[oid]? = some (.notification n) := by
        rw [← hKeyO oid ⟨n, Or.inr hPn⟩ hO]; exact hPn
      obtain ⟨tx, hTx, hBx⟩ := (hInv.1 oid n hPn').2.1 hd hHd
      obtain ⟨c1, c2, c3⟩ := hNeOfOther hd tx oid hTx hBx hO
      have hEq := hPresX hd tx hTx c1 c2 c3
      rw [hPt] at hEq; cases hEq
      exact hInv.headNoPrev hPn' hHd hTx
  -- A thread off every queue holds no links.
  · by_cases hth : tid = t
    · rw [hth, hTx0] at hPt; cases hPt; exact ⟨hPt0, hNt0⟩
    · obtain ⟨tx, hPre, hI, hNxNp, -, hPvNs, -⟩ := hCorrB tid tcb hPt hth
      have hNB' : ∀ o, tx.ipcState ≠ .blockedOnNotification o := fun o e => hNB o (hI.trans e)
      obtain ⟨hPx, hNx0⟩ := hInv.unqueuedNoLinks hPre hNB'
      have htp : tid ≠ p := by
        intro e; rw [e, hTp] at hPre; cases hPre; exact hNB' nid hBp
      have hns : ttcb.ntfnNext ≠ some tid := by
        intro hs
        obtain ⟨-, -, -, tb, hTb, hBb, -⟩ := hSucc tid hs
        rw [hPre] at hTb; cases hTb; exact hNB' nid hBb
      exact ⟨(hPvNs hns).trans hPx, (hNxNp htp).trans hNx0⟩

end SeLe4n.Kernel
