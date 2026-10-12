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

/-- The frame: a step that changes no notification and no TCB blocked on a
notification, before or after, keeps the queues consistent. -/
theorem notificationWaiterConsistent_frame {st st' : SystemState}
    (hInv : notificationWaiterConsistent st)
    (hNtfnBack : ∀ (noid : SeLe4n.ObjId) (ntfn : Notification),
      st'.objects[noid]? = some (.notification ntfn) →
      st.objects[noid]? = some (.notification ntfn))
    (hNtfnFwd : ∀ (noid : SeLe4n.ObjId) (ntfn : Notification),
      st.objects[noid]? = some (.notification ntfn) →
      st'.objects[noid]? = some (.notification ntfn))
    (hBlockedPre : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (oid : SeLe4n.ObjId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.ipcState = .blockedOnNotification oid →
      st'.objects[tid.toObjId]? = st.objects[tid.toObjId]?)
    (hBlockedPost : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (oid : SeLe4n.ObjId),
      st'.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.ipcState = .blockedOnNotification oid →
      st'.objects[tid.toObjId]? = st.objects[tid.toObjId]?) :
    notificationWaiterConsistent st' := by
  refine ⟨fun oid ntfn hN => ?_, fun tid tcb oid hT hB => ?_, fun tid tcb oid hT hB => ?_⟩
  · obtain ⟨hIff, hHead, hTail⟩ := hInv.1 oid ntfn (hNtfnBack oid ntfn hN)
    refine ⟨hIff, fun h hh => ?_, fun t ht => ?_⟩
    · obtain ⟨tcb, hT, hB⟩ := hHead h hh
      exact ⟨tcb, (hBlockedPre h tcb oid hT hB).trans hT, hB⟩
    · obtain ⟨tcb, hT, hB, hN'⟩ := hTail t ht
      exact ⟨tcb, (hBlockedPre t tcb oid hT hB).trans hT, hB, hN'⟩
  · have hTpre : st.objects[tid.toObjId]? = some (.tcb tcb) :=
      (hBlockedPost tid tcb oid hT hB).symm.trans hT
    obtain ⟨ntfn, hN, hPrev, hTail, hNext⟩ := hInv.2.1 tid tcb oid hTpre hB
    refine ⟨ntfn, hNtfnFwd oid ntfn hN, ?_, hTail, ?_⟩
    · rcases hPrev with h | ⟨a, ta, ha, hTa, hBa, hNa⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, ta, ha, (hBlockedPre a ta oid hTa hBa).trans hTa, hBa, hNa⟩
    · intro b hb
      obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNext b hb
      exact ⟨hne, tb, (hBlockedPre b tb oid hTb hBb).trans hTb, hBb, hPb⟩
  · have hTpre : st.objects[tid.toObjId]? = some (.tcb tcb) :=
      (hBlockedPost tid tcb oid hT hB).symm.trans hT
    refine (hInv.2.2 tid tcb oid hTpre hB).transport
      (fun _ _ hN hH => .head (hNtfnFwd _ _ hN) hH) (fun a _ ta hRa hTa hNx hRa' => ?_)
    obtain ⟨ta', hTa', hBa⟩ := notificationQueueReaches_blocked hInv hRa
    rw [hTa] at hTa'; cases hTa'
    exact .next hRa' ((hBlockedPre a ta oid hTa hBa).trans hTa) hNx

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
  refine ⟨fun oid ntfn hN => ?_, fun tid tcb oid hT hB => ?_, fun tid tcb oid hT hB => ?_⟩
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
    exact reach (hInv.2.2 tid tcb oid hT hB)

/-- One object written, at a key that holds a TCB blocked on no notification
before the write and after it: the queues are untouched. -/
theorem notificationWaiterConsistent_of_unblocked_tcb_write {st st' : SystemState}
    {tid : SeLe4n.ThreadId}
    (hInv : notificationWaiterConsistent st)
    (hPre : ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      ∀ oid, tcb.ipcState ≠ .blockedOnNotification oid)
    (hPost : ∃ tcb, st'.objects[tid.toObjId]? = some (.tcb tcb) ∧
      ∀ oid, tcb.ipcState ≠ .blockedOnNotification oid)
    (hOther : ∀ x, x ≠ tid.toObjId → st'.objects[x]? = st.objects[x]?) :
    notificationWaiterConsistent st' := by
  obtain ⟨t0, hT0, hNB0⟩ := hPre
  obtain ⟨t1, hT1, hNB1⟩ := hPost
  refine notificationWaiterConsistent_frame hInv ?_ ?_ ?_ ?_
  · intro noid ntfn hN
    by_cases h : noid = tid.toObjId
    · subst h; rw [hT1] at hN; cases hN
    · rwa [hOther noid h] at hN
  · intro noid ntfn hN
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

/-- The head popped (`notificationSignal`'s wake): the notification now heads
its queue with the old head's successor, the old head is blocked on no
notification, and no other object changed.  Nothing else need be written: the
new head's predecessor link is not read. -/
theorem notificationWaiterConsistent_of_headPop {st st' : SystemState}
    {nid : SeLe4n.ObjId} {ntfn : Notification} {h : SeLe4n.ThreadId} {htcb : TCB}
    (hInv : notificationWaiterConsistent st)
    (hN : st.objects[nid]? = some (.notification ntfn))
    (hHead : ntfn.waitHead = some h)
    (hT : st.objects[h.toObjId]? = some (.tcb htcb))
    (hPostN : st'.objects[nid]? = some (.notification (ntfn.withHeadPopped htcb.ntfnNext)))
    (hPostH : ∃ t, st'.objects[h.toObjId]? = some (.tcb t) ∧
      ∀ oid, t.ipcState ≠ .blockedOnNotification oid)
    (hPostO : ∀ x, x ≠ nid → x ≠ h.toObjId → st'.objects[x]? = st.objects[x]?) :
    notificationWaiterConsistent st' := by
  obtain ⟨th, hTh, hNBh⟩ := hPostH
  obtain ⟨hIff, hHeadC, hTailC⟩ := hInv.1 nid ntfn hN
  have hBh : htcb.ipcState = .blockedOnNotification nid := by
    obtain ⟨t, ht, hb⟩ := hHeadC h hHead
    rw [hT] at ht; cases ht; exact hb
  obtain ⟨n0, hN0, _, hTailH, hNextH⟩ := hInv.2.1 h htcb nid hT hBh
  rw [hN] at hN0; cases hN0
  have hPres : ∀ (x : SeLe4n.ThreadId) (tx : TCB), st.objects[x.toObjId]? = some (.tcb tx) →
      x ≠ h → st'.objects[x.toObjId]? = some (.tcb tx) := by
    intro x tx hx hne
    have h1 : x.toObjId ≠ nid := by intro e; rw [e, hN] at hx; cases hx
    have h2 : x.toObjId ≠ h.toObjId := fun e => hne (SeLe4n.ThreadId.toObjId_injective _ _ e)
    rw [hPostO _ h1 h2]; exact hx
  -- A TCB blocked on another notification is not the old head.
  have hNeOfOther : ∀ (x : SeLe4n.ThreadId) (tx : TCB) (oid : SeLe4n.ObjId),
      st.objects[x.toObjId]? = some (.tcb tx) → tx.ipcState = .blockedOnNotification oid →
      oid ≠ nid → x ≠ h := by
    intro x tx oid hx hb hne e
    subst e; rw [hT] at hx; cases hx; rw [hBh] at hb; cases hb; exact hne rfl
  refine ⟨fun oid n hPn => ?_, fun tid tcb oid hPt hB => ?_, fun tid tcb oid hPt hB => ?_⟩
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
        obtain ⟨hne, tb, hTb, hBb, _⟩ := hNextH b hb
        have hbh : b ≠ h := fun e => hne (e ▸ hHead)
        exact ⟨tb, hPres b tb hTb hbh, hBb⟩
      · rw [Notification.withHeadPopped_waitTail] at ht
        cases hnx : htcb.ntfnNext with
        | none => rw [hnx] at ht; simp at ht
        | some b =>
          rw [hnx] at ht; simp only [Option.isSome_some, ↓reduceIte] at ht
          obtain ⟨tt, hTt, hBt, hNt⟩ := hTailC t ht
          have hth : t ≠ h := by
            intro e; subst e; rw [hT] at hTt; cases hTt; rw [hnx] at hNt; cases hNt
          exact ⟨tt, hPres t tt hTt hth, hBt, hNt⟩
    · have hOH : oid ≠ h.toObjId := by intro e; rw [e, hTh] at hPn; cases hPn
      have hPn' : st.objects[oid]? = some (.notification n) := by rwa [hPostO oid hO hOH] at hPn
      obtain ⟨hIff2, hH2, hT2⟩ := hInv.1 oid n hPn'
      refine ⟨hIff2, fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨tx, hTx, hBx⟩ := hH2 x hx
        exact ⟨tx, hPres x tx hTx (hNeOfOther x tx oid hTx hBx hO), hBx⟩
      · obtain ⟨tx, hTx, hBx, hNx⟩ := hT2 x hx
        exact ⟨tx, hPres x tx hTx (hNeOfOther x tx oid hTx hBx hO), hBx, hNx⟩
  · have hTidNeH : tid.toObjId ≠ h.toObjId := by
      intro e; rw [e, hTh] at hPt; cases hPt; exact hNBh oid hB
    have hTidNeN : tid.toObjId ≠ nid := by intro e; rw [e, hPostN] at hPt; cases hPt
    have hPre : st.objects[tid.toObjId]? = some (.tcb tcb) := by
      rwa [hPostO _ hTidNeN hTidNeH] at hPt
    have hth : tid ≠ h := fun e => hTidNeH (e ▸ rfl)
    obtain ⟨n0, hN0, hPrev, hTailT, hNextT⟩ := hInv.2.1 tid tcb oid hPre hB
    by_cases hO : oid = nid
    · subst hO
      rw [hN] at hN0; cases hN0
      refine ⟨_, hPostN, ?_, fun hnone => ?_, fun b hb => ?_⟩
      · rcases hPrev with hh | ⟨a, ta, ha, hTa, hBa, hNa⟩
        · rw [hHead] at hh; cases hh; exact absurd rfl hth
        · by_cases hah : a = h
          · subst hah; rw [hT] at hTa; cases hTa
            exact Or.inl (by rw [Notification.withHeadPopped_waitHead, hNa])
          · exact Or.inr ⟨a, ta, ha, hPres a ta hTa hah, hBa, hNa⟩
      · have ht := hTailT hnone
        rw [Notification.withHeadPopped_waitTail]
        cases hnx : htcb.ntfnNext with
        | none => rw [hTailH hnx] at ht; cases ht; exact absurd rfl hth
        | some b => simp only [Option.isSome_some, ↓reduceIte]; exact ht
      · obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNextT b hb
        have hbh : b ≠ h := fun e => hne (e ▸ hHead)
        refine ⟨?_, tb, hPres b tb hTb hbh, hBb, hPb⟩
        rw [Notification.withHeadPopped_waitHead]
        intro hnx
        obtain ⟨_, tb', hTb', _, hPb'⟩ := hNextH b hnx
        rw [hTb] at hTb'; cases hTb'; rw [hPb] at hPb'; cases hPb'; exact hth rfl
    · have hON : oid ≠ h.toObjId := by intro e; rw [e, hT] at hN0; cases hN0
      refine ⟨n0, by rw [hPostO oid hO hON]; exact hN0, ?_, hTailT, fun b hb => ?_⟩
      · rcases hPrev with hh | ⟨a, ta, ha, hTa, hBa, hNa⟩
        · exact Or.inl hh
        · exact Or.inr ⟨a, ta, ha, hPres a ta hTa (hNeOfOther a ta oid hTa hBa hO), hBa, hNa⟩
      · obtain ⟨hne, tb, hTb, hBb, hPb⟩ := hNextT b hb
        exact ⟨hne, tb, hPres b tb hTb (hNeOfOther b tb oid hTb hBb hO), hBb, hPb⟩
  · have hTidNeH : tid.toObjId ≠ h.toObjId := by
      intro e; rw [e, hTh] at hPt; cases hPt; exact hNBh oid hB
    have hTidNeN : tid.toObjId ≠ nid := by intro e; rw [e, hPostN] at hPt; cases hPt
    have hPre : st.objects[tid.toObjId]? = some (.tcb tcb) := by
      rwa [hPostO _ hTidNeN hTidNeH] at hPt
    have hth : tid ≠ h := fun e => hTidNeH (e ▸ rfl)
    have hR := hInv.2.2 tid tcb oid hPre hB
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
            · exact Or.inr (.next hRa' (hPres a ta hTa hah) hNx)
      rcases hKey tid hR with e | h'
      · exact absurd e hth
      · exact h'
    · refine hR.transport (fun n1 h1 hN1 hH1 => ?_) (fun a _ ta hRa hTa hNx hRa' => ?_)
      · have hOH : oid ≠ h.toObjId := by intro e; rw [e, hT] at hN1; cases hN1
        exact .head (by rw [hPostO oid hO hOH]; exact hN1) hH1
      · obtain ⟨ta', hTa', hBa⟩ := notificationQueueReaches_blocked hInv hRa
        rw [hTa] at hTa'; cases hTa'
        exact .next hRa' (hPres a ta hTa (hNeOfOther a ta oid hTa hBa hO)) hNx

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
      (∀ t, ntfn.waitTail = some t → x ≠ t.toObjId) → st'.objects[x]? = st.objects[x]?) :
    notificationWaiterConsistent st' := by
  obtain ⟨tw, hTw, hBw, hPw, hNw⟩ := hPostW
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
      refine ⟨tx, by rw [hPostO _ h1 (hInj x w hxw) h3]; exact hx, rfl, rfl,
        fun _ => rfl, fun h => absurd h hxt⟩
  have hBwd : ∀ (x : SeLe4n.ThreadId) (t' : TCB), x ≠ w →
      st'.objects[x.toObjId]? = some (.tcb t') →
      ∃ tx, st.objects[x.toObjId]? = some (.tcb tx) := by
    intro x t' hxw hx
    by_cases hxt : ntfn.waitTail = some x
    · obtain ⟨tt, hTt, _, _⟩ := hTailC x hxt; exact ⟨tt, hTt⟩
    · have h1 : x.toObjId ≠ nid := by intro e; rw [e, hPostN] at hx; cases hx
      have h3 : ∀ t, ntfn.waitTail = some t → x.toObjId ≠ t.toObjId := by
        intro t ht; exact hInj x t (fun e => hxt (e ▸ ht))
      exact ⟨t', by rw [← hPostO _ h1 (hInj x w hxw) h3]; exact hx⟩
  have hTailNe : ∀ (x : SeLe4n.ThreadId) (tx : TCB) (oid : SeLe4n.ObjId),
      st.objects[x.toObjId]? = some (.tcb tx) → tx.ipcState = .blockedOnNotification oid →
      oid ≠ nid → ntfn.waitTail ≠ some x := by
    intro x tx oid hx hb hne ht
    obtain ⟨tt, hTt, hBt, _⟩ := hTailC x ht
    rw [hx] at hTt; cases hTt; rw [hb] at hBt; cases hBt; exact hne rfl
  refine ⟨fun oid n hPn => ?_, fun tid tcb oid hPt hB => ?_, fun tid tcb oid hPt hB => ?_⟩
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
        rwa [hPostO oid hO hOW hOT] at hPn
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
        refine ⟨n0, by rw [hPostO oid hON hOW hOT]; exact hN0, ?_, ?_, fun b hb => ?_⟩
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
          exact .head (by rw [hPostO o hO hOW hOT]; exact hN1) hH1
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
        exact .next (hTransport t nid (hInv.2.2 t tt nid hTt hBt)) hT' (hNx ht)
    · obtain ⟨tcb0, hPre⟩ := hBwd tid tcb htw hPt
      obtain ⟨t', hT', hI, _⟩ := hCorr tid tcb0 htw hPre
      rw [hPt] at hT'; cases hT'
      exact hTransport tid oid (hInv.2.2 tid tcb0 oid hPre (hI ▸ hB))


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
  refine ⟨fun oid n hPn => ?_, fun tid tcb oid hPt hB => ?_, fun tid tcb oid hPt hB => ?_⟩
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
    refine (hInv.2.2 tid tcb oid hPre hB).transport (fun n1 h1 hN1 hH1 => ?_)
      (fun _ _ _ _ hTa hNx hRa' => .next hRa' (hTcb _ _ hTa) hNx)
    by_cases hO' : oid = nid
    · subst hO'; rw [hN] at hN1; cases hN1; exact .head hPostN (hH.trans hH1)
    · exact .head (by rw [hO oid hO']; exact hN1) hH1

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
  refine ⟨fun oid n hPn => ?_, fun tid tcb oid hPt hB => ?_, fun tid tcb oid hPt hB => ?_⟩
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
    refine (hInv.2.2 tid ty oid hy (hI ▸ hB)).transport
      (fun _ _ hN1 hH1 => .head (hNtfnFwd _ _ hN1) hH1) (fun _ _ ta _ hTa hNx hRa' => ?_)
    obtain ⟨tx, hx, _, _, hN⟩ := hFwd _ ta hTa
    exact .next hRa' hx (hN.trans hNx)


/-- The queues read the object store and nothing else. -/
theorem notificationWaiterConsistent_of_objects_eq {st st' : SystemState}
    (h : st'.objects = st.objects) (hInv : notificationWaiterConsistent st) :
    notificationWaiterConsistent st' :=
  notificationWaiterConsistent_frame hInv (fun _ _ hN => by rwa [h] at hN)
    (fun _ _ hN => by rwa [h]) (fun _ _ _ _ _ => by rw [h]) (fun _ _ _ _ _ => by rw [h])
