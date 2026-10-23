-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.Defs

/-!
# The notification wait queue's consistency, by the objects a step writes

WS-ZA ZA4.4.  A notification wait queue is linked through its waiters' TCBs
(`TCB.ntfnPrev` / `TCB.ntfnNext`), and `notificationWaiterConsistent` relates
each object to its direct neighbours.  Every step that touches a queue is one
of four shapes, each stated here over the objects it leaves behind rather than
over the operation that wrote them, so the live, per-core and cleanup forms all
discharge through the same theorem:

* a frame — no notification and no notification-blocked TCB changes;
* a pop of the head (`notificationSignal`'s wake);
* an append at the tail (`notificationWait`'s block);
* a write of one TCB that is blocked on no notification before or after.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Membership carried across a step: the queue's head is reached in the new
state, and each link out of a thread reached in both states is followed there. -/
theorem notificationQueueReaches.transport {st st' : SystemState} {n : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} (hR : notificationQueueReaches st n t)
    (hHead : ∀ (ntfn : Notification) (h : SeLe4n.ThreadId),
      st.objects[n]? = some (.notification ntfn) → ntfn.waitHead = some h →
      notificationQueueReaches st' n h)
    (hStep : ∀ (a b : SeLe4n.ThreadId) (ta : TCB), notificationQueueReaches st n a →
      st.objects[a.toObjId]? = some (.tcb ta) → ta.ntfnNext = some b →
      notificationQueueReaches st' n a → notificationQueueReaches st' n b) :
    notificationQueueReaches st' n t := by
  induction hR with
  | head hN hH => exact hHead _ _ hN hH
  | next hRa hTa hNx ih => exact hStep _ _ _ hRa hTa hNx ih

/-- The frame: a step that changes no notification, keeps every notification a
blocked thread names, and changes no TCB blocked on a notification, before or
after, keeps the queues consistent. -/
theorem notificationWaiterConsistent_frame {st st' : SystemState}
    (hInv : notificationWaiterConsistent st)
    (hNtfnBack : ∀ (noid : SeLe4n.ObjId) (ntfn : Notification),
      st'.objects[noid]? = some (.notification ntfn) →
      st.objects[noid]? = some (.notification ntfn))
    (hNtfnFwd : ∀ (noid : SeLe4n.ObjId) (ntfn : Notification) (tid : SeLe4n.ThreadId) (tcb : TCB),
      st.objects[noid]? = some (.notification ntfn) →
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.ipcState = .blockedOnNotification noid →
      st'.objects[noid]? = some (.notification ntfn))
    (hBlockedPre : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (oid : SeLe4n.ObjId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.ipcState = .blockedOnNotification oid →
      st'.objects[tid.toObjId]? = st.objects[tid.toObjId]?)
    (hBlockedPost : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (oid : SeLe4n.ObjId),
      st'.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.ipcState = .blockedOnNotification oid →
      st'.objects[tid.toObjId]? = st.objects[tid.toObjId]?)
    (hUnblocked : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st'.objects[tid.toObjId]? = some (.tcb tcb) →
      (∀ oid, tcb.ipcState ≠ .blockedOnNotification oid) →
      st'.objects[tid.toObjId]? = st.objects[tid.toObjId]? ∨
        (tcb.ntfnPrev = none ∧ tcb.ntfnNext = none)) :
    notificationWaiterConsistent st' := by
  refine ⟨fun oid ntfn hN => ?_, fun tid tcb oid hT hB => ?_, fun tid tcb oid hT hB => ?_,
    fun oid ntfn hd tcb hN hH hT => ?_, fun tid tcb hT hNB => ?_⟩
  · obtain ⟨hIff, hHead, hTail⟩ := hInv.1 oid ntfn (hNtfnBack oid ntfn hN)
    refine ⟨hIff, fun h hh => ?_, fun t ht => ?_⟩
    · obtain ⟨tcb, hT, hB⟩ := hHead h hh
      exact ⟨tcb, (hBlockedPre h tcb oid hT hB).trans hT, hB⟩
    · obtain ⟨tcb, hT, hB, hN'⟩ := hTail t ht
      exact ⟨tcb, (hBlockedPre t tcb oid hT hB).trans hT, hB, hN'⟩
  · have hTpre : st.objects[tid.toObjId]? = some (.tcb tcb) :=
      (hBlockedPost tid tcb oid hT hB).symm.trans hT
    obtain ⟨ntfn, hN, hPrev, hTail, hNext⟩ := hInv.2.1 tid tcb oid hTpre hB
    refine ⟨ntfn, hNtfnFwd oid ntfn tid tcb hN hTpre hB, ?_, hTail, ?_⟩
    · rcases hPrev with h | ⟨a, ta, ha, hTa, hBa, hNa⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, ta, ha, (hBlockedPre a ta oid hTa hBa).trans hTa, hBa, hNa⟩
    · intro b hb
      obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNext b hb
      exact ⟨hne, tb, (hBlockedPre b tb oid hTb hBb).trans hTb, hBb, hPb⟩
  · have hTpre : st.objects[tid.toObjId]? = some (.tcb tcb) :=
      (hBlockedPost tid tcb oid hT hB).symm.trans hT
    refine (hInv.reaches hTpre hB).transport
      (fun _ _ hN hH => .head (hNtfnFwd _ _ tid tcb hN hTpre hB) hH) (fun a _ ta hRa hTa hNx hRa' => ?_)
    obtain ⟨ta', hTa', hBa⟩ := notificationQueueReaches_blocked hInv hRa
    rw [hTa] at hTa'; cases hTa'
    exact .next hRa' ((hBlockedPre a ta oid hTa hBa).trans hTa) hNx
  · have hN0 := hNtfnBack oid ntfn hN
    obtain ⟨t0, hT0, hB0⟩ := (hInv.1 oid ntfn hN0).2.1 hd hH
    have hEq := (hBlockedPre hd t0 oid hT0 hB0).trans hT0
    rw [hT] at hEq; cases hEq
    exact hInv.headNoPrev hN0 hH hT0
  · rcases hUnblocked tid tcb hT hNB with hEq | hL
    · exact hInv.unqueuedNoLinks (hEq.symm.trans hT) hNB
    · exact hL

/-- WS-ZA ZA4.5: a step that writes nothing but run-queue links keeps the
queues consistent — every clause reads notifications and the TCBs' IPC state and
notification links, none of which a run-queue write touches. -/
theorem notificationWaiterConsistent_of_objectsAgreeOffRunLinks {st st' : SystemState}
    (h : st'.objectsAgreeOffRunLinks st) (hInv : notificationWaiterConsistent st) :
    notificationWaiterConsistent st' := by
  have reach : ∀ {n t}, notificationQueueReaches st n t → notificationQueueReaches st' n t := by
    intro n t hR
    induction hR with
    | head hN hH => exact .head (h.get_notification_iff.mpr hN) hH
    | @next a b ta _ hTa hNx ih =>
      run_links_fwd h at ta hTa
      exact .next ih hTa hNx
  refine ⟨fun oid ntfn hN => ?_, fun tid tcb oid hT hB => ?_, fun tid tcb oid hT hB => ?_,
    fun oid ntfn hd tcb hN hH hT => ?_, fun tid tcb hT hNB => ?_⟩
  · obtain ⟨hIff, hHead, hTail⟩ := hInv.1 oid ntfn (h.get_notification_iff.mp hN)
    refine ⟨hIff, fun hd hh => ?_, fun t ht => ?_⟩
    · obtain ⟨tcb, hT, hB⟩ := hHead hd hh
      run_links_fwd h at tcb hT
      exact ⟨_, hT, hB⟩
    · obtain ⟨tcb, hT, hB, hN'⟩ := hTail t ht
      run_links_fwd h at tcb hT
      exact ⟨_, hT, hB, hN'⟩
  · run_links_back h at tcb hT
    obtain ⟨ntfn, hN, hPrev, hTail, hNext⟩ := hInv.2.1 tid tcb oid hT hB
    refine ⟨ntfn, h.get_notification_iff.mpr hN, ?_, hTail, ?_⟩
    · rcases hPrev with hp | ⟨a, ta, ha, hTa, hBa, hNa⟩
      · exact Or.inl hp
      · run_links_fwd h at ta hTa
        exact Or.inr ⟨a, _, ha, hTa, hBa, hNa⟩
    · intro b hb
      obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNext b hb
      run_links_fwd h at tb hTb
      exact ⟨hne, _, hTb, hBb, hPb⟩
  · run_links_back h at tcb hT
    exact reach (hInv.reaches hT hB)
  · run_links_back h at tcb hT
    have hP := hInv.headNoPrev (h.get_notification_iff.mp hN) hH hT
    exact hP
  · run_links_back h at tcb hT
    have hL := hInv.unqueuedNoLinks hT hNB
    exact hL

/-- One object written, at a key that holds a TCB blocked on no notification
before the write and after it: the queues are untouched. -/
theorem notificationWaiterConsistent_of_unblocked_tcb_write {st st' : SystemState}
    {tid : SeLe4n.ThreadId}
    (hInv : notificationWaiterConsistent st)
    (hPre : ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      ∀ oid, tcb.ipcState ≠ .blockedOnNotification oid)
    (hPost : ∃ tcb, st'.objects[tid.toObjId]? = some (.tcb tcb) ∧
      ∀ oid, tcb.ipcState ≠ .blockedOnNotification oid)
    (hLinks : ∀ t0 t1, st.objects[tid.toObjId]? = some (.tcb t0) →
      st'.objects[tid.toObjId]? = some (.tcb t1) →
      t1.ntfnPrev = t0.ntfnPrev ∧ t1.ntfnNext = t0.ntfnNext)
    (hOther : ∀ x, x ≠ tid.toObjId → st'.objects[x]? = st.objects[x]?) :
    notificationWaiterConsistent st' := by
  obtain ⟨t0, hT0, hNB0⟩ := hPre
  obtain ⟨t1, hT1, hNB1⟩ := hPost
  refine notificationWaiterConsistent_frame hInv ?_ ?_ ?_ ?_ ?_
  · intro noid ntfn hN
    by_cases h : noid = tid.toObjId
    · subst h; rw [hT1] at hN; cases hN
    · rwa [hOther noid h] at hN
  · intro noid ntfn _ _ hN _ _
    by_cases h : noid = tid.toObjId
    · subst h; rw [hT0] at hN; cases hN
    · rwa [hOther noid h]
  · intro x tcb oid hT hB
    by_cases h : x.toObjId = tid.toObjId
    · rw [h, hT0] at hT; cases hT; exact absurd hB (hNB0 oid)
    · exact hOther _ h
  · intro x tcb oid hT hB
    by_cases h : x.toObjId = tid.toObjId
    · rw [h, hT1] at hT; cases hT; exact absurd hB (hNB1 oid)
    · exact hOther _ h
  · intro x tcb hT _
    by_cases h : x.toObjId = tid.toObjId
    · rw [h, hT1] at hT; cases hT
      obtain ⟨hP, hN⟩ := hLinks t0 t1 hT0 hT1
      obtain ⟨hP0, hN0⟩ := hInv.unqueuedNoLinks hT0 hNB0
      exact Or.inr ⟨hP.trans hP0, hN.trans hN0⟩
    · exact Or.inl (hOther _ h)

/-- The head popped (`notificationSignal`'s wake, seL4's `tcbEPDequeue` at the
head): the notification now heads its queue with the old head's successor, the
old head is blocked on no notification and holds no links, the successor keeps
its state and successor link and drops its predecessor link, and no other
object changed. -/
theorem notificationWaiterConsistent_of_headPop {st st' : SystemState}
    {nid : SeLe4n.ObjId} {ntfn : Notification} {h : SeLe4n.ThreadId} {htcb : TCB}
    (hInv : notificationWaiterConsistent st)
    (hN : st.objects[nid]? = some (.notification ntfn))
    (hHead : ntfn.waitHead = some h)
    (hT : st.objects[h.toObjId]? = some (.tcb htcb))
    (hPostN : st'.objects[nid]? = some (.notification (ntfn.withHeadPopped htcb.ntfnNext)))
    (hPostH : ∃ t, st'.objects[h.toObjId]? = some (.tcb t) ∧
      (∀ oid, t.ipcState ≠ .blockedOnNotification oid) ∧ t.ntfnPrev = none ∧ t.ntfnNext = none)
    (hPostS : ∀ (b : SeLe4n.ThreadId) (tb : TCB), htcb.ntfnNext = some b →
      st.objects[b.toObjId]? = some (.tcb tb) →
      ∃ tb', st'.objects[b.toObjId]? = some (.tcb tb') ∧ tb'.ipcState = tb.ipcState ∧
        tb'.ntfnPrev = none ∧ tb'.ntfnNext = tb.ntfnNext)
    (hPostO : ∀ x, x ≠ nid → x ≠ h.toObjId →
      (∀ b, htcb.ntfnNext = some b → x ≠ b.toObjId) → st'.objects[x]? = st.objects[x]?) :
    notificationWaiterConsistent st' := by
  obtain ⟨th, hTh, hNBh, hPh, hNh⟩ := hPostH
  obtain ⟨hIff, hHeadC, hTailC⟩ := hInv.1 nid ntfn hN
  have hBh : htcb.ipcState = .blockedOnNotification nid := by
    obtain ⟨t, ht, hb⟩ := hHeadC h hHead
    rw [hT] at ht; cases ht; exact hb
  obtain ⟨n0, hN0, _, hTailH, hNextH⟩ := hInv.2.1 h htcb nid hT hBh
  rw [hN] at hN0; cases hN0
  have hInj : ∀ (x y : SeLe4n.ThreadId), x ≠ y → x.toObjId ≠ y.toObjId :=
    fun x y hne e => hne (SeLe4n.ThreadId.toObjId_injective _ _ e)
  -- The successor: blocked on this notification, linked back to the old head.
  have hSucc : ∀ b, htcb.ntfnNext = some b → b ≠ h ∧ ∃ tb,
      st.objects[b.toObjId]? = some (.tcb tb) ∧ tb.ipcState = .blockedOnNotification nid ∧
        tb.ntfnPrev = some h := by
    intro b hb
    obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNextH b hb
    exact ⟨fun e => hne (e ▸ hHead), tb, hTb, hBb, hPb⟩
  -- Every other TCB keeps its state and successor link; only the successor's
  -- predecessor link moves, to none.
  have hCorr : ∀ (x : SeLe4n.ThreadId) (tx : TCB), st.objects[x.toObjId]? = some (.tcb tx) →
      x ≠ h → ∃ tx', st'.objects[x.toObjId]? = some (.tcb tx') ∧ tx'.ipcState = tx.ipcState ∧
        tx'.ntfnNext = tx.ntfnNext ∧ (htcb.ntfnNext ≠ some x → tx'.ntfnPrev = tx.ntfnPrev) ∧
        (htcb.ntfnNext = some x → tx'.ntfnPrev = none) := by
    intro x tx hx hxh
    by_cases hs : htcb.ntfnNext = some x
    · obtain ⟨tb', hB', hI, hP, hNx⟩ := hPostS x tx hs hx
      exact ⟨tb', hB', hI, hNx, fun e => absurd hs e, fun _ => hP⟩
    · have h1 : x.toObjId ≠ nid := by intro e; rw [e, hN] at hx; cases hx
      have h3 : ∀ b, htcb.ntfnNext = some b → x.toObjId ≠ b.toObjId :=
        fun b hb => hInj x b (fun e => hs (e ▸ hb))
      exact ⟨tx, by rw [hPostO _ h1 (hInj x h hxh) h3]; exact hx, rfl, rfl,
        fun _ => rfl, fun e => absurd e hs⟩
  have hCorrB : ∀ (x : SeLe4n.ThreadId) (tx' : TCB), st'.objects[x.toObjId]? = some (.tcb tx') →
      x ≠ h → ∃ tx, st.objects[x.toObjId]? = some (.tcb tx) ∧ tx'.ipcState = tx.ipcState ∧
        tx'.ntfnNext = tx.ntfnNext ∧ (htcb.ntfnNext ≠ some x → tx'.ntfnPrev = tx.ntfnPrev) ∧
        (htcb.ntfnNext = some x → tx'.ntfnPrev = none) := by
    intro x tx' hx hxh
    obtain ⟨tx, hTx⟩ : ∃ tx, st.objects[x.toObjId]? = some (.tcb tx) := by
      by_cases hs : htcb.ntfnNext = some x
      · obtain ⟨_, tb, hTb, _⟩ := hSucc x hs; exact ⟨tb, hTb⟩
      · have h1 : x.toObjId ≠ nid := by intro e; rw [e, hPostN] at hx; cases hx
        have h3 : ∀ b, htcb.ntfnNext = some b → x.toObjId ≠ b.toObjId :=
          fun b hb => hInj x b (fun e => hs (e ▸ hb))
        exact ⟨tx', by rw [← hPostO _ h1 (hInj x h hxh) h3]; exact hx⟩
    obtain ⟨t2, hT2, hI, hNx, hP1, hP2⟩ := hCorr x tx hTx hxh
    rw [hx] at hT2; cases hT2
    exact ⟨tx, hTx, hI, hNx, hP1, hP2⟩
  have hPresX : ∀ (x : SeLe4n.ThreadId) (tx : TCB), st.objects[x.toObjId]? = some (.tcb tx) →
      x ≠ h → htcb.ntfnNext ≠ some x → st'.objects[x.toObjId]? = some (.tcb tx) := by
    intro x tx hx hxh hs
    have h1 : x.toObjId ≠ nid := by intro e; rw [e, hN] at hx; cases hx
    rw [hPostO _ h1 (hInj x h hxh) (fun b hb => hInj x b (fun e => hs (e ▸ hb)))]; exact hx
  -- A TCB blocked on another notification is neither the old head nor its successor.
  have hNeOfOther : ∀ (x : SeLe4n.ThreadId) (tx : TCB) (oid : SeLe4n.ObjId),
      st.objects[x.toObjId]? = some (.tcb tx) → tx.ipcState = .blockedOnNotification oid →
      oid ≠ nid → x ≠ h := by
    intro x tx oid hx hb hne e
    subst e; rw [hT] at hx; cases hx; rw [hBh] at hb; cases hb; exact hne rfl
  have hNotSuccOfOther : ∀ (x : SeLe4n.ThreadId) (tx : TCB) (oid : SeLe4n.ObjId),
      st.objects[x.toObjId]? = some (.tcb tx) → tx.ipcState = .blockedOnNotification oid →
      oid ≠ nid → htcb.ntfnNext ≠ some x := by
    intro x tx oid hx hb hne hs
    obtain ⟨_, tb, hTb, hBb, _⟩ := hSucc x hs
    rw [hx] at hTb; cases hTb; rw [hb] at hBb; cases hBb; exact hne rfl
  -- Any other notification is unchanged: the two TCB keys written hold TCBs.
  have hKeyO : ∀ (oid : SeLe4n.ObjId), (∃ n, st.objects[oid]? = some (.notification n) ∨
      st'.objects[oid]? = some (.notification n)) → oid ≠ nid →
      st'.objects[oid]? = st.objects[oid]? := by
    intro oid ⟨n, hn⟩ hO
    refine hPostO oid hO ?_ ?_
    · intro e; subst e; rcases hn with hn | hn
      · rw [hT] at hn; cases hn
      · rw [hTh] at hn; cases hn
    · intro b hb e; subst e
      obtain ⟨_, tb, hTb, _⟩ := hSucc b hb
      rcases hn with hn | hn
      · rw [hTb] at hn; cases hn
      · obtain ⟨tb', hTb', _⟩ := hPostS b tb hb hTb
        rw [hTb'] at hn; cases hn
  have hTidNeH : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (oid : SeLe4n.ObjId),
      st'.objects[tid.toObjId]? = some (.tcb tcb) → tcb.ipcState = .blockedOnNotification oid →
      tid ≠ h := by
    intro tid tcb oid hPt hB e; subst e; rw [hTh] at hPt; cases hPt; exact hNBh oid hB
  refine ⟨fun oid n hPn => ?_, fun tid tcb oid hPt hB => ?_, fun tid tcb oid hPt hB => ?_,
    fun oid n hd tcb hPn hHd hPt => ?_, fun tid tcb hPt hNB => ?_⟩
  -- The notification's three clauses.
  · by_cases hO : oid = nid
    · subst hO
      rw [hPostN] at hPn; cases hPn
      refine ⟨?_, fun b hb => ?_, fun t ht => ?_⟩
      · have hTailSome : ntfn.waitTail ≠ none := fun e => by
          rw [← hIff] at e; rw [hHead] at e; cases e
        cases hnx : htcb.ntfnNext with
        | none => simp
        | some b => simp [hTailSome]
      · rw [Notification.withHeadPopped_waitHead] at hb
        obtain ⟨hbh, tb, hTb, hBb, _⟩ := hSucc b hb
        obtain ⟨tb', hTb', hI, _⟩ := hCorr b tb hTb hbh
        exact ⟨tb', hTb', hI.trans hBb⟩
      · rw [Notification.withHeadPopped_waitTail] at ht
        cases hnx : htcb.ntfnNext with
        | none => rw [hnx] at ht; simp at ht
        | some b =>
          rw [hnx] at ht; simp only [Option.isSome_some, ↓reduceIte] at ht
          obtain ⟨tt, hTt, hBt, hNt⟩ := hTailC t ht
          have hth : t ≠ h := by
            intro e; subst e; rw [hT] at hTt; cases hTt; rw [hnx] at hNt; cases hNt
          obtain ⟨tt', hTt', hI, hNx, _⟩ := hCorr t tt hTt hth
          exact ⟨tt', hTt', hI.trans hBt, hNx.trans hNt⟩
    · have hPn' : st.objects[oid]? = some (.notification n) := by
        rw [← hKeyO oid ⟨n, Or.inr hPn⟩ hO]; exact hPn
      obtain ⟨hIff2, hH2, hT2⟩ := hInv.1 oid n hPn'
      refine ⟨hIff2, fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨tx, hTx, hBx⟩ := hH2 x hx
        exact ⟨tx, hPresX x tx hTx (hNeOfOther x tx oid hTx hBx hO)
          (hNotSuccOfOther x tx oid hTx hBx hO), hBx⟩
      · obtain ⟨tx, hTx, hBx, hNx⟩ := hT2 x hx
        exact ⟨tx, hPresX x tx hTx (hNeOfOther x tx oid hTx hBx hO)
          (hNotSuccOfOther x tx oid hTx hBx hO), hBx, hNx⟩
  -- A blocked thread's neighbours.
  · have hth := hTidNeH tid tcb oid hPt hB
    obtain ⟨tx, hPre, hI, hNx, hP1, hP2⟩ := hCorrB tid tcb hPt hth
    have hBx : tx.ipcState = .blockedOnNotification oid := hI ▸ hB
    obtain ⟨n0, hN0, hPrev, hTailT, hNextT⟩ := hInv.2.1 tid tx oid hPre hBx
    by_cases hO : oid = nid
    · subst hO
      rw [hN] at hN0; cases hN0
      refine ⟨_, hPostN, ?_, fun hnone => ?_, fun b hb => ?_⟩
      · by_cases hs : htcb.ntfnNext = some tid
        · exact Or.inl (by rw [Notification.withHeadPopped_waitHead, hs])
        · rcases hPrev with hh | ⟨a, ta, ha, hTa, hBa, hNa⟩
          · rw [hHead] at hh; cases hh; exact absurd rfl hth
          · by_cases hah : a = h
            · subst hah; rw [hT] at hTa; cases hTa; exact absurd hNa hs
            · obtain ⟨ta', hTa', hIa, hNa', _⟩ := hCorr a ta hTa hah
              exact Or.inr ⟨a, ta', (hP1 hs).trans ha, hTa', hIa.trans hBa, hNa'.trans hNa⟩
      · have ht := hTailT (hNx ▸ hnone)
        rw [Notification.withHeadPopped_waitTail]
        cases hnx : htcb.ntfnNext with
        | none => rw [hTailH hnx] at ht; cases ht; exact absurd rfl hth
        | some b => simp only [Option.isSome_some, ↓reduceIte]; exact ht
      · obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNextT b (hNx ▸ hb)
        have hbh : b ≠ h := fun e => hne (e ▸ hHead)
        have hns : htcb.ntfnNext ≠ some b := by
          intro hnx
          obtain ⟨_, tb', hTb', _, hPb'⟩ := hSucc b hnx
          rw [hTb] at hTb'; cases hTb'; rw [hPb] at hPb'; cases hPb'; exact hth rfl
        obtain ⟨tb', hTb', hIb, _, hPb1, _⟩ := hCorr b tb hTb hbh
        refine ⟨?_, tb', hTb', hIb.trans hBb, (hPb1 hns).trans hPb⟩
        rw [Notification.withHeadPopped_waitHead]; exact hns
    · have hs := hNotSuccOfOther tid tx oid hPre hBx hO
      have hEq := hPresX tid tx hPre hth hs
      rw [hPt] at hEq; cases hEq
      refine ⟨n0, by rw [hKeyO oid ⟨n0, Or.inl hN0⟩ hO]; exact hN0, ?_, hTailT, fun b hb => ?_⟩
      · rcases hPrev with hh | ⟨a, ta, ha, hTa, hBa, hNa⟩
        · exact Or.inl hh
        · exact Or.inr ⟨a, ta, ha, hPresX a ta hTa (hNeOfOther a ta oid hTa hBa hO)
            (hNotSuccOfOther a ta oid hTa hBa hO), hBa, hNa⟩
      · obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNextT b hb
        exact ⟨hne, tb, hPresX b tb hTb (hNeOfOther b tb oid hTb hBb hO)
          (hNotSuccOfOther b tb oid hTb hBb hO), hBb, hPb⟩
  -- Membership.
  · have hth := hTidNeH tid tcb oid hPt hB
    obtain ⟨tx, hPre, hI, _, _, _⟩ := hCorrB tid tcb hPt hth
    have hBx : tx.ipcState = .blockedOnNotification oid := hI ▸ hB
    have hR := hInv.reaches hPre hBx
    by_cases hO : oid = nid
    · subst hO
      -- Every thread the old queue reached is the old head or reached anew:
      -- the old head's successor heads the queue now.
      have hKey : ∀ u, notificationQueueReaches st oid u →
          u = h ∨ notificationQueueReaches st' oid u := by
        intro u hu
        induction hu with
        | head hN1 hH1 => rw [hN] at hN1; cases hN1; rw [hHead] at hH1; cases hH1; exact Or.inl rfl
        | @next a b ta hRa hTa hNx ih =>
          by_cases hah : a = h
          · subst hah; rw [hT] at hTa; cases hTa
            exact Or.inr (.head hPostN (by rw [Notification.withHeadPopped_waitHead, hNx]))
          · rcases ih with e | hRa'
            · exact absurd e hah
            · obtain ⟨ta', hTa', _, hNa', _⟩ := hCorr a ta hTa hah
              exact Or.inr (.next hRa' hTa' (hNa'.trans hNx))
      rcases hKey tid hR with e | h'
      · exact absurd e hth
      · exact h'
    · refine hR.transport (fun n1 h1 hN1 hH1 => ?_) (fun a _ ta hRa hTa hNx hRa' => ?_)
      · exact .head (by rw [hKeyO oid ⟨n1, Or.inl hN1⟩ hO]; exact hN1) hH1
      · obtain ⟨ta', hTa', hBa⟩ := notificationQueueReaches_blocked hInv hRa
        rw [hTa] at hTa'; cases hTa'
        exact .next hRa' (hPresX a ta hTa (hNeOfOther a ta oid hTa hBa hO)
          (hNotSuccOfOther a ta oid hTa hBa hO)) hNx
  -- The head has no predecessor.
  · by_cases hO : oid = nid
    · subst hO
      rw [hPostN] at hPn; cases hPn
      rw [Notification.withHeadPopped_waitHead] at hHd
      obtain ⟨hdh, _⟩ := hSucc hd hHd
      obtain ⟨_, _, _, _, _, hP2⟩ := hCorrB hd tcb hPt hdh
      exact hP2 hHd
    · have hPn' : st.objects[oid]? = some (.notification n) := by
        rw [← hKeyO oid ⟨n, Or.inr hPn⟩ hO]; exact hPn
      obtain ⟨tx, hTx, hBx⟩ := (hInv.1 oid n hPn').2.1 hd hHd
      have hEq := hPresX hd tx hTx (hNeOfOther hd tx oid hTx hBx hO)
        (hNotSuccOfOther hd tx oid hTx hBx hO)
      rw [hPt] at hEq; cases hEq
      exact hInv.headNoPrev hPn' hHd hTx
  -- A thread off every queue holds no links.
  · by_cases hth : tid = h
    · subst hth; rw [hTh] at hPt; cases hPt; exact ⟨hPh, hNh⟩
    · obtain ⟨tx, hPre, hI, hNx, hP1, hP2⟩ := hCorrB tid tcb hPt hth
      obtain ⟨hPx, hNx0⟩ := hInv.unqueuedNoLinks hPre (fun o e => hNB o (hI.trans e))
      refine ⟨?_, hNx.trans hNx0⟩
      by_cases hs : htcb.ntfnNext = some tid
      · exact hP2 hs
      · exact (hP1 hs).trans hPx

/-- A waiter appended at the tail (`notificationWait`'s block): the waiter was
blocked on no notification and is now blocked on this one, linked in behind the
old tail; the old tail's successor link names it; nothing else changed. -/
theorem notificationWaiterConsistent_of_append {st st' : SystemState}
    {nid : SeLe4n.ObjId} {ntfn : Notification} {w : SeLe4n.ThreadId} {wtcb : TCB}
    (hInv : notificationWaiterConsistent st)
    (hN : st.objects[nid]? = some (.notification ntfn))
    (hW : st.objects[w.toObjId]? = some (.tcb wtcb))
    (hWNB : ∀ oid, wtcb.ipcState ≠ .blockedOnNotification oid)
    (hPostN : st'.objects[nid]? = some (.notification (ntfn.withWaiterAppended w)))
    (hPostW : ∃ tw, st'.objects[w.toObjId]? = some (.tcb tw) ∧
      tw.ipcState = .blockedOnNotification nid ∧ tw.ntfnPrev = ntfn.waitTail ∧
      tw.ntfnNext = none)
    (hPostT : ∀ (t : SeLe4n.ThreadId) (ttcb : TCB), ntfn.waitTail = some t →
      st.objects[t.toObjId]? = some (.tcb ttcb) →
      ∃ tt, st'.objects[t.toObjId]? = some (.tcb tt) ∧ tt.ipcState = ttcb.ipcState ∧
        tt.ntfnPrev = ttcb.ntfnPrev ∧ tt.ntfnNext = some w)
    (hPostO : ∀ x, x ≠ nid → x ≠ w.toObjId →
      (∀ t, ntfn.waitTail = some t → x ≠ t.toObjId) →
      (st'.objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks) :
    notificationWaiterConsistent st' := by
  obtain ⟨tw, hTw, hBw, hPw, hNw⟩ := hPostW
  have hNotTcb : ∀ n : Notification, ∀ t, KernelObject.notification n ≠ .tcb t :=
    fun _ _ e => KernelObject.noConfusion e
  obtain ⟨hIff, hHeadC, hTailC⟩ := hInv.1 nid ntfn hN
  have hNeW : ∀ (x : SeLe4n.ThreadId) (tx : TCB) (oid : SeLe4n.ObjId),
      st.objects[x.toObjId]? = some (.tcb tx) → tx.ipcState = .blockedOnNotification oid →
      x ≠ w := by
    intro x tx oid hx hb e; subst e; rw [hW] at hx; cases hx; exact hWNB oid hb
  have hInj : ∀ (x y : SeLe4n.ThreadId), x ≠ y → x.toObjId ≠ y.toObjId :=
    fun x y hne e => hne (SeLe4n.ThreadId.toObjId_injective _ _ e)
  -- Every thread but the waiter keeps its object; the old tail's successor link
  -- is the one link that moves.
  have hCorr : ∀ (x : SeLe4n.ThreadId) (tx : TCB), x ≠ w →
      st.objects[x.toObjId]? = some (.tcb tx) →
      ∃ t', st'.objects[x.toObjId]? = some (.tcb t') ∧ t'.ipcState = tx.ipcState ∧
        t'.ntfnPrev = tx.ntfnPrev ∧
        (ntfn.waitTail ≠ some x → t'.ntfnNext = tx.ntfnNext) ∧
        (ntfn.waitTail = some x → t'.ntfnNext = some w) := by
    intro x tx hxw hx
    by_cases hxt : ntfn.waitTail = some x
    · obtain ⟨tt, hTt, hI, hP, hNx⟩ := hPostT x tx hxt hx
      exact ⟨tt, hTt, hI, hP, fun h => absurd hxt h, fun _ => hNx⟩
    · have h1 : x.toObjId ≠ nid := by intro e; rw [e, hN] at hx; cases hx
      have h3 : ∀ t, ntfn.waitTail = some t → x.toObjId ≠ t.toObjId := by
        intro t ht; exact hInj x t (fun e => hxt (e ▸ ht))
      obtain ⟨t', hT', ht⟩ := KernelObject.map_withoutRunLinks_tcb
        (hPostO _ h1 (hInj x w hxw) h3) hx
      exact ⟨t', hT', TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState ht,
        TCB.proj_eq_of_withoutRunLinks_eq TCB.ntfnPrev ht,
        fun _ => TCB.proj_eq_of_withoutRunLinks_eq TCB.ntfnNext ht, fun h => absurd h hxt⟩
  have hBwd : ∀ (x : SeLe4n.ThreadId) (t' : TCB), x ≠ w →
      st'.objects[x.toObjId]? = some (.tcb t') →
      ∃ tx, st.objects[x.toObjId]? = some (.tcb tx) := by
    intro x t' hxw hx
    by_cases hxt : ntfn.waitTail = some x
    · obtain ⟨tt, hTt, _, _⟩ := hTailC x hxt; exact ⟨tt, hTt⟩
    · have h1 : x.toObjId ≠ nid := by intro e; rw [e, hPostN] at hx; cases hx
      have h3 : ∀ t, ntfn.waitTail = some t → x.toObjId ≠ t.toObjId := by
        intro t ht; exact hInj x t (fun e => hxt (e ▸ ht))
      obtain ⟨tx, hTx, _⟩ := KernelObject.map_withoutRunLinks_tcb
        (hPostO _ h1 (hInj x w hxw) h3).symm hx
      exact ⟨tx, hTx⟩
  have hTailNe : ∀ (x : SeLe4n.ThreadId) (tx : TCB) (oid : SeLe4n.ObjId),
      st.objects[x.toObjId]? = some (.tcb tx) → tx.ipcState = .blockedOnNotification oid →
      oid ≠ nid → ntfn.waitTail ≠ some x := by
    intro x tx oid hx hb hne ht
    obtain ⟨tt, hTt, hBt, _⟩ := hTailC x ht
    rw [hx] at hTt; cases hTt; rw [hb] at hBt; cases hBt; exact hne rfl
  refine ⟨fun oid n hPn => ?_, fun tid tcb oid hPt hB => ?_, fun tid tcb oid hPt hB => ?_,
    fun oid n hd tcb hPn hHd hPt => ?_, fun tid tcb hPt hNB => ?_⟩
  · by_cases hO : oid = nid
    · subst hO
      rw [hPostN] at hPn; cases hPn
      refine ⟨by simp, fun x hx => ?_, fun x hx => ?_⟩
      · rw [Notification.withWaiterAppended_waitHead] at hx
        cases hh : ntfn.waitHead with
        | none => rw [hh] at hx; cases hx; exact ⟨tw, hTw, hBw⟩
        | some h =>
          rw [hh] at hx; cases hx
          obtain ⟨th, hTh, hBh⟩ := hHeadC h hh
          obtain ⟨t', hT', hI, _⟩ := hCorr h th (hNeW h th _ hTh hBh) hTh
          exact ⟨t', hT', hI.trans hBh⟩
      · rw [Notification.withWaiterAppended_waitTail] at hx; cases hx
        exact ⟨tw, hTw, hBw, hNw⟩
    · have hOW : oid ≠ w.toObjId := by intro e; rw [e, hTw] at hPn; cases hPn
      have hOT : ∀ t, ntfn.waitTail = some t → oid ≠ t.toObjId := by
        intro t ht e
        obtain ⟨tt, hTt, hBt, _⟩ := hTailC t ht
        obtain ⟨t', hT', _⟩ := hCorr t tt (hNeW t tt nid hTt hBt) hTt
        rw [e, hT'] at hPn; cases hPn
      have hPn' : st.objects[oid]? = some (.notification n) := by
        exact KernelObject.map_withoutRunLinks_of_not_tcb (hPostO oid hO hOW hOT).symm hPn
          (hNotTcb n)
      obtain ⟨hIff2, hH2, hT2⟩ := hInv.1 oid n hPn'
      refine ⟨hIff2, fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨tx, hTx, hBx⟩ := hH2 x hx
        obtain ⟨t', hT', hI, _⟩ := hCorr x tx (hNeW x tx oid hTx hBx) hTx
        exact ⟨t', hT', hI.trans hBx⟩
      · obtain ⟨tx, hTx, hBx, hNx⟩ := hT2 x hx
        obtain ⟨t', hT', hI, _, hNe, _⟩ := hCorr x tx (hNeW x tx oid hTx hBx) hTx
        exact ⟨t', hT', hI.trans hBx, (hNe (hTailNe x tx oid hTx hBx hO)).trans hNx⟩
  · by_cases htw : tid = w
    · subst htw
      rw [hTw] at hPt; cases hPt
      rw [hBw] at hB; cases hB
      refine ⟨_, hPostN, ?_, fun _ => by simp, fun b hb => by rw [hNw] at hb; cases hb⟩
      cases hh : ntfn.waitHead with
      | none => exact Or.inl (by simp [hh])
      | some h =>
        have hts : ntfn.waitTail ≠ none := fun e => by rw [← hIff, hh] at e; cases e
        obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hts
        obtain ⟨tt, hTt, hBt, _⟩ := hTailC t ht
        obtain ⟨t', hT', hI, _, _, hNx⟩ := hCorr t tt (hNeW t tt nid hTt hBt) hTt
        exact Or.inr ⟨t, t', by rw [hPw, ht], hT', hI.trans hBt, hNx ht⟩
    · obtain ⟨tcb0, hPre⟩ := hBwd tid tcb htw hPt
      obtain ⟨t', hT', hI, hP, hNeq, hNt⟩ := hCorr tid tcb0 htw hPre
      rw [hPt] at hT'; cases hT'
      have hB0 : tcb0.ipcState = .blockedOnNotification oid := hI ▸ hB
      obtain ⟨n0, hN0, hPrev, hTailT, hNextT⟩ := hInv.2.1 tid tcb0 oid hPre hB0
      by_cases hO : oid = nid
      · subst hO
        rw [hN] at hN0; cases hN0
        refine ⟨_, hPostN, ?_, fun hnone => ?_, fun b hb => ?_⟩
        · rcases hPrev with hh | ⟨a, ta, ha, hTa, hBa, hNa⟩
          · exact Or.inl (by simp [hh])
          · have haw := hNeW a ta _ hTa hBa
            have hat : ntfn.waitTail ≠ some a := by
              intro e; obtain ⟨tt, hTt, _, hNtt⟩ := hTailC a e
              rw [hTa] at hTt; cases hTt; rw [hNa] at hNtt; cases hNtt
            obtain ⟨a', hA', hAI, _, hANe, _⟩ := hCorr a ta haw hTa
            exact Or.inr ⟨a, a', hP ▸ ha, hA', hAI.trans hBa, (hANe hat).trans hNa⟩
        · by_cases hxt : ntfn.waitTail = some tid
          · rw [hNt hxt] at hnone; cases hnone
          · rw [hNeq hxt] at hnone; exact absurd (hTailT hnone) hxt
        · rw [Notification.withWaiterAppended_waitHead]
          by_cases hxt : ntfn.waitTail = some tid
          · rw [hNt hxt] at hb; cases hb
            refine ⟨?_, tw, hTw, hBw, by rw [hPw, hxt]⟩
            cases hh : ntfn.waitHead with
            | none => rw [hIff] at hh; rw [hh] at hxt; cases hxt
            | some h =>
              obtain ⟨th, hTh, hBh⟩ := hHeadC h hh
              intro e; simp only [Option.getD_some, Option.some.injEq] at e
              exact hNeW h th _ hTh hBh e
          · rw [hNeq hxt] at hb
            obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNextT b hb
            have hbw := hNeW b tb _ hTb hBb
            obtain ⟨b', hB', hBI, hBP, _⟩ := hCorr b tb hbw hTb
            refine ⟨?_, b', hB', hBI.trans hBb, hBP.trans hPb⟩
            cases hh : ntfn.waitHead with
            | none => simp only [Option.getD_none, ne_eq, Option.some.injEq]; exact fun e => hbw e.symm
            | some h => simp only [Option.getD_some]; rw [hh] at hne; exact hne
      · have hON : oid ≠ nid := hO
        have hOW : oid ≠ w.toObjId := by intro e; rw [e, hW] at hN0; cases hN0
        have hOT : ∀ t, ntfn.waitTail = some t → oid ≠ t.toObjId := by
          intro t ht e
          obtain ⟨tt, hTt, _, _⟩ := hTailC t ht
          rw [e, hTt] at hN0; cases hN0
        refine ⟨n0, KernelObject.map_withoutRunLinks_of_not_tcb (hPostO oid hON hOW hOT) hN0
          (hNotTcb n0), ?_, ?_, fun b hb => ?_⟩
        · rcases hPrev with hh | ⟨a, ta, ha, hTa, hBa, hNa⟩
          · exact Or.inl hh
          · obtain ⟨a', hA', hAI, _, hANe, _⟩ := hCorr a ta (hNeW a ta oid hTa hBa) hTa
            exact Or.inr ⟨a, a', hP ▸ ha, hA', hAI.trans hBa,
              (hANe (hTailNe a ta oid hTa hBa hO)).trans hNa⟩
        · intro hnone
          exact hTailT ((hNeq (hTailNe tid tcb0 oid hPre hB0 hO)) ▸ hnone)
        · rw [hNeq (hTailNe tid tcb0 oid hPre hB0 hO)] at hb
          obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNextT b hb
          obtain ⟨b', hB', hBI, hBP, _⟩ := hCorr b tb (hNeW b tb oid hTb hBb) hTb
          exact ⟨hne, b', hB', hBI.trans hBb, hBP.trans hPb⟩
  · -- A thread reached before is reached after: the head is kept (or the waiter
    -- heads an empty queue), and only the old tail's link moves, to the waiter.
    have hTransport : ∀ (u : SeLe4n.ThreadId) (o : SeLe4n.ObjId),
        notificationQueueReaches st o u → notificationQueueReaches st' o u := by
      intro u o hu
      refine hu.transport (fun n1 h1 hN1 hH1 => ?_) (fun a _ ta hRa hTa hNx hRa' => ?_)
      · by_cases hO : o = nid
        · subst hO; rw [hN] at hN1; cases hN1
          exact .head hPostN (by simp [hH1])
        · have hOW : o ≠ w.toObjId := by intro e; rw [e, hW] at hN1; cases hN1
          have hOT : ∀ t, ntfn.waitTail = some t → o ≠ t.toObjId := by
            intro t ht e
            obtain ⟨tt, hTt, _, _⟩ := hTailC t ht
            rw [e, hTt] at hN1; cases hN1
          exact .head (KernelObject.map_withoutRunLinks_of_not_tcb (hPostO o hO hOW hOT) hN1
            (hNotTcb _)) hH1
      · obtain ⟨ta', hTa', hBa⟩ := notificationQueueReaches_blocked hInv hRa
        rw [hTa] at hTa'; cases hTa'
        have hat : ntfn.waitTail ≠ some a := by
          intro e; obtain ⟨tt, hTt, _, hNtt⟩ := hTailC a e
          rw [hTa] at hTt; cases hTt; rw [hNx] at hNtt; cases hNtt
        obtain ⟨a', hA', _, _, hANe, _⟩ := hCorr a ta (hNeW a ta _ hTa hBa) hTa
        exact .next hRa' hA' ((hANe hat).trans hNx)
    by_cases htw : tid = w
    · subst htw
      rw [hTw] at hPt; cases hPt
      rw [hBw] at hB; cases hB
      cases hh : ntfn.waitHead with
      | none => exact .head hPostN (by simp [hh])
      | some h =>
        have hts : ntfn.waitTail ≠ none := fun e => by rw [← hIff, hh] at e; cases e
        obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hts
        obtain ⟨tt, hTt, hBt, _⟩ := hTailC t ht
        obtain ⟨t', hT', _, _, _, hNx⟩ := hCorr t tt (hNeW t tt nid hTt hBt) hTt
        exact .next (hTransport t nid (hInv.2.2.1 t tt nid hTt hBt)) hT' (hNx ht)
    · obtain ⟨tcb0, hPre⟩ := hBwd tid tcb htw hPt
      obtain ⟨t', hT', hI, _⟩ := hCorr tid tcb0 htw hPre
      rw [hPt] at hT'; cases hT'
      exact hTransport tid oid (hInv.2.2.1 tid tcb0 oid hPre (hI ▸ hB))
  -- The head has no predecessor: an empty queue's new head is the waiter, linked
  -- behind the empty tail; any other head is unchanged.
  · by_cases hO : oid = nid
    · subst hO
      rw [hPostN] at hPn; cases hPn
      rw [Notification.withWaiterAppended_waitHead] at hHd
      cases hh : ntfn.waitHead with
      | none =>
        rw [hh] at hHd; simp only [Option.getD_none, Option.some.injEq] at hHd; subst hHd
        rw [hTw] at hPt; cases hPt
        rw [hPw]; exact (hIff.mp hh)
      | some h0 =>
        rw [hh] at hHd; simp only [Option.getD_some, Option.some.injEq] at hHd; subst hHd
        obtain ⟨th, hTh, hBh⟩ := hHeadC h0 hh
        obtain ⟨t', hT', _, hP, _⟩ := hCorr h0 th (hNeW h0 th _ hTh hBh) hTh
        rw [hPt] at hT'; cases hT'
        exact hP.trans (hInv.headNoPrev hN hh hTh)
    · have hOW : oid ≠ w.toObjId := by intro e; rw [e, hTw] at hPn; cases hPn
      have hOT : ∀ t, ntfn.waitTail = some t → oid ≠ t.toObjId := by
        intro t ht e
        obtain ⟨tt, hTt, hBt, _⟩ := hTailC t ht
        obtain ⟨t', hT', _⟩ := hCorr t tt (hNeW t tt nid hTt hBt) hTt
        rw [e, hT'] at hPn; cases hPn
      have hPn' : st.objects[oid]? = some (.notification n) :=
        KernelObject.map_withoutRunLinks_of_not_tcb (hPostO oid hO hOW hOT).symm hPn (hNotTcb n)
      obtain ⟨tx, hTx, hBx⟩ := (hInv.1 oid n hPn').2.1 hd hHd
      obtain ⟨t', hT', _, hP, _⟩ := hCorr hd tx (hNeW hd tx oid hTx hBx) hTx
      rw [hPt] at hT'; cases hT'
      exact hP.trans (hInv.headNoPrev hPn' hHd hTx)
  -- A thread off every queue is not the waiter and not the old tail, so it
  -- keeps both (empty) links.
  · have htw : tid ≠ w := by
      intro e; subst e; rw [hTw] at hPt; cases hPt; exact hNB nid hBw
    obtain ⟨tcb0, hPre⟩ := hBwd tid tcb htw hPt
    obtain ⟨t', hT', hI, hP, hNeq, _⟩ := hCorr tid tcb0 htw hPre
    rw [hPt] at hT'; cases hT'
    have hNB0 : ∀ oid, tcb0.ipcState ≠ .blockedOnNotification oid :=
      fun o e => hNB o (hI.trans e)
    obtain ⟨hP0, hN0⟩ := hInv.unqueuedNoLinks hPre hNB0
    have hxt : ntfn.waitTail ≠ some tid := by
      intro ht; obtain ⟨tt, hTt, hBt, _⟩ := hTailC tid ht
      rw [hPre] at hTt; cases hTt; exact hNB0 nid hBt
    exact ⟨hP.trans hP0, (hNeq hxt).trans hN0⟩


/-- A notification rewritten with the same queue ends, and nothing else changed
(`notificationSignal`'s merge, `notificationWait` consuming a badge): the queues
are untouched. -/
theorem notificationWaiterConsistent_of_queueEnds_write {st st' : SystemState}
    {nid : SeLe4n.ObjId} {ntfn n' : Notification}
    (hInv : notificationWaiterConsistent st)
    (hN : st.objects[nid]? = some (.notification ntfn))
    (hPostN : st'.objects[nid]? = some (.notification n'))
    (hH : n'.waitHead = ntfn.waitHead) (hT : n'.waitTail = ntfn.waitTail)
    (hO : ∀ x, x ≠ nid → st'.objects[x]? = st.objects[x]?) :
    notificationWaiterConsistent st' := by
  have hTcb : ∀ (x : SeLe4n.ThreadId) (tx : TCB), st.objects[x.toObjId]? = some (.tcb tx) →
      st'.objects[x.toObjId]? = some (.tcb tx) := by
    intro x tx hx
    have hne : x.toObjId ≠ nid := by intro e; rw [e, hN] at hx; cases hx
    rw [hO _ hne]; exact hx
  have hTcbB : ∀ (x : SeLe4n.ThreadId) (tx : TCB), st'.objects[x.toObjId]? = some (.tcb tx) →
      st.objects[x.toObjId]? = some (.tcb tx) := by
    intro x tx hx
    have hne : x.toObjId ≠ nid := by intro e; rw [e, hPostN] at hx; cases hx
    rw [← hO _ hne]; exact hx
  refine ⟨fun oid n hPn => ?_, fun tid tcb oid hPt hB => ?_, fun tid tcb oid hPt hB => ?_,
    fun oid n hd tcb hPn hHd hPt => ?_, fun tid tcb hPt hNB => ?_⟩
  · by_cases hO' : oid = nid
    · subst hO'
      rw [hPostN] at hPn; cases hPn
      obtain ⟨hIff, hHd, hTl⟩ := hInv.1 _ ntfn hN
      refine ⟨by rw [hH, hT]; exact hIff, fun h hh => ?_, fun t ht => ?_⟩
      · obtain ⟨tx, hx, hb⟩ := hHd h (by rw [← hH]; exact hh)
        exact ⟨tx, hTcb _ _ hx, hb⟩
      · obtain ⟨tx, hx, hb, hn⟩ := hTl t (by rw [← hT]; exact ht)
        exact ⟨tx, hTcb _ _ hx, hb, hn⟩
    · have hPn' : st.objects[oid]? = some (.notification n) := by rwa [hO oid hO'] at hPn
      obtain ⟨hIff, hHd, hTl⟩ := hInv.1 oid n hPn'
      refine ⟨hIff, fun h hh => ?_, fun t ht => ?_⟩
      · obtain ⟨tx, hx, hb⟩ := hHd h hh
        exact ⟨tx, hTcb _ _ hx, hb⟩
      · obtain ⟨tx, hx, hb, hn⟩ := hTl t ht
        exact ⟨tx, hTcb _ _ hx, hb, hn⟩
  · have hTid : tid.toObjId ≠ nid := by intro e; rw [e, hPostN] at hPt; cases hPt
    have hPre : st.objects[tid.toObjId]? = some (.tcb tcb) := by rwa [hO _ hTid] at hPt
    obtain ⟨n0, hN0, hPrev, hTailT, hNextT⟩ := hInv.2.1 tid tcb oid hPre hB
    have hPrev' : ∀ (n1 : Notification), n1.waitHead = n0.waitHead →
        (n1.waitHead = some tid ∨ ∃ a ta, tcb.ntfnPrev = some a ∧
          st'.objects[a.toObjId]? = some (.tcb ta) ∧
          ta.ipcState = .blockedOnNotification oid ∧ ta.ntfnNext = some tid) := by
      intro n1 h1
      rcases hPrev with hh | ⟨a, ta, ha, hTa, hBa, hNa⟩
      · exact Or.inl (h1 ▸ hh)
      · exact Or.inr ⟨a, ta, ha, hTcb _ _ hTa, hBa, hNa⟩
    have hNext' : ∀ (n1 : Notification), n1.waitHead = n0.waitHead →
        ∀ b, tcb.ntfnNext = some b → n1.waitHead ≠ some b ∧
          ∃ tb, st'.objects[b.toObjId]? = some (.tcb tb) ∧
            tb.ipcState = .blockedOnNotification oid ∧ tb.ntfnPrev = some tid := by
      intro n1 h1 b hb
      obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNextT b hb
      exact ⟨h1 ▸ hne, tb, hTcb _ _ hTb, hBb, hPb⟩
    by_cases hO' : oid = nid
    · subst hO'
      rw [hN] at hN0; cases hN0
      exact ⟨n', hPostN, hPrev' n' hH, fun hn => hT ▸ hTailT hn, hNext' n' hH⟩
    · exact ⟨n0, by rw [hO oid hO']; exact hN0, hPrev' n0 rfl, hTailT, hNext' n0 rfl⟩
  · have hTid : tid.toObjId ≠ nid := by intro e; rw [e, hPostN] at hPt; cases hPt
    have hPre : st.objects[tid.toObjId]? = some (.tcb tcb) := by rwa [hO _ hTid] at hPt
    refine (hInv.2.2.1 tid tcb oid hPre hB).transport (fun n1 h1 hN1 hH1 => ?_)
      (fun _ _ _ _ hTa hNx hRa' => .next hRa' (hTcb _ _ hTa) hNx)
    by_cases hO' : oid = nid
    · subst hO'; rw [hN] at hN1; cases hN1; exact .head hPostN (hH.trans hH1)
    · exact .head (by rw [hO oid hO']; exact hN1) hH1
  · by_cases hO' : oid = nid
    · subst hO'
      rw [hPostN] at hPn; cases hPn
      exact hInv.headNoPrev hN (hH ▸ hHd) (hTcbB _ _ hPt)
    · exact hInv.headNoPrev (by rwa [hO oid hO'] at hPn) hHd (hTcbB _ _ hPt)
  · exact hInv.unqueuedNoLinks (hTcbB _ _ hPt) hNB

/-- A well-formed notification holding a pending badge has no waiters. -/
theorem notificationQueueWellFormed_waitHead_of_pendingBadge {ntfn : Notification}
    {b : SeLe4n.Badge} (hWF : notificationQueueWellFormed ntfn)
    (hB : ntfn.pendingBadge = some b) : ntfn.waitHead = none := by
  unfold notificationQueueWellFormed at hWF
  cases hs : ntfn.state <;> rw [hs] at hWF <;> simp_all

/-- The field frame: notifications unchanged, and every TCB, read in either
direction, keeps its IPC state and both queue links.  A step that rewrites only
fields the queues do not read (a reply link, a scheduling binding) keeps them
consistent whichever threads it writes. -/
theorem notificationWaiterConsistent_of_tcbLinkFrame {st st' : SystemState}
    (hInv : notificationWaiterConsistent st)
    (hNtfnBack : ∀ (k : SeLe4n.ObjId) (n : Notification),
      st'.objects[k]? = some (.notification n) → st.objects[k]? = some (.notification n))
    (hNtfnFwd : ∀ (k : SeLe4n.ObjId) (n : Notification),
      st.objects[k]? = some (.notification n) → st'.objects[k]? = some (.notification n))
    (hFwd : ∀ (k : SeLe4n.ObjId) (ty : TCB), st.objects[k]? = some (.tcb ty) →
      ∃ tx, st'.objects[k]? = some (.tcb tx) ∧ tx.ipcState = ty.ipcState ∧
        tx.ntfnPrev = ty.ntfnPrev ∧ tx.ntfnNext = ty.ntfnNext)
    (hBwd : ∀ (k : SeLe4n.ObjId) (tx : TCB), st'.objects[k]? = some (.tcb tx) →
      ∃ ty, st.objects[k]? = some (.tcb ty) ∧ tx.ipcState = ty.ipcState ∧
        tx.ntfnPrev = ty.ntfnPrev ∧ tx.ntfnNext = ty.ntfnNext) :
    notificationWaiterConsistent st' := by
  refine ⟨fun oid n hPn => ?_, fun tid tcb oid hPt hB => ?_, fun tid tcb oid hPt hB => ?_,
    fun oid n hd tcb hPn hHd hPt => ?_, fun tid tcb hPt hNB => ?_⟩
  · obtain ⟨hIff, hH, hT⟩ := hInv.1 oid n (hNtfnBack oid n hPn)
    refine ⟨hIff, fun h hh => ?_, fun t ht => ?_⟩
    · obtain ⟨ty, hy, hb⟩ := hH h hh
      obtain ⟨tx, hx, hI, _, _⟩ := hFwd _ ty hy
      exact ⟨tx, hx, hI.trans hb⟩
    · obtain ⟨ty, hy, hb, hn⟩ := hT t ht
      obtain ⟨tx, hx, hI, _, hN⟩ := hFwd _ ty hy
      exact ⟨tx, hx, hI.trans hb, hN.trans hn⟩
  · obtain ⟨ty, hy, hI, hP, hN⟩ := hBwd _ tcb hPt
    obtain ⟨n0, hN0, hPrev, hTail, hNext⟩ := hInv.2.1 tid ty oid hy (hI ▸ hB)
    refine ⟨n0, hNtfnFwd oid n0 hN0, ?_, fun hn => hTail (hN ▸ hn), fun b hb => ?_⟩
    · rcases hPrev with hh | ⟨a, ta, ha, hTa, hBa, hNa⟩
      · exact Or.inl hh
      · obtain ⟨ta', hA', hAI, _, hAN⟩ := hFwd _ ta hTa
        exact Or.inr ⟨a, ta', hP ▸ ha, hA', hAI.trans hBa, hAN.trans hNa⟩
    · obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNext b (hN ▸ hb)
      obtain ⟨tb', hB', hBI, hBP, _⟩ := hFwd _ tb hTb
      exact ⟨hne, tb', hB', hBI.trans hBb, hBP.trans hPb⟩
  · obtain ⟨ty, hy, hI, _, _⟩ := hBwd _ tcb hPt
    refine (hInv.2.2.1 tid ty oid hy (hI ▸ hB)).transport
      (fun _ _ hN1 hH1 => .head (hNtfnFwd _ _ hN1) hH1) (fun _ _ ta _ hTa hNx hRa' => ?_)
    obtain ⟨tx, hx, _, _, hN⟩ := hFwd _ ta hTa
    exact .next hRa' hx (hN.trans hNx)
  · obtain ⟨ty, hy, _, hP, _⟩ := hBwd _ tcb hPt
    exact hP.trans (hInv.headNoPrev (hNtfnBack oid n hPn) hHd hy)
  · obtain ⟨ty, hy, hI, hP, hN⟩ := hBwd _ tcb hPt
    obtain ⟨hP0, hN0⟩ := hInv.unqueuedNoLinks hy (fun o e => hNB o (hI.trans e))
    exact ⟨hP.trans hP0, hN.trans hN0⟩


/-- The queues read the object store and nothing else. -/
theorem notificationWaiterConsistent_of_objects_eq {st st' : SystemState}
    (h : st'.objects = st.objects) (hInv : notificationWaiterConsistent st) :
    notificationWaiterConsistent st' :=
  notificationWaiterConsistent_frame hInv (fun _ _ hN => by rwa [h] at hN)
    (fun _ _ _ _ hN _ _ => by rwa [h]) (fun _ _ _ _ _ => by rw [h]) (fun _ _ _ _ _ => by rw [h])
    (fun _ _ _ _ => Or.inl (by rw [h]))
