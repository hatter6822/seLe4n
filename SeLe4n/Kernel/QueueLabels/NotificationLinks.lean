-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.QueueLabels.Stage

/-! # The notification-queue writes, under one labelling

WS-SX SX21.1 (D46).  The writes a records frame does not keep (SX20's core
frames: the notification stores, the queue links, the bind and the unbind)
keep `notificationLabelsAgree` where each new queue end or link names a thread
of the label the slot asks for.  The two-way gate admits equal labels only
(`twoWayLabelGate_iff_eq`), so those labels come from the pre-state's own
clauses: a queue's head, its tail and a thread's neighbours all carry one
label, the notification's.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

namespace notificationLabelsAgree

variable {ctx : LabelingContext}

/-- **One slot rewritten**, the others kept. -/
theorem of_slot {st st' : SystemState} {k : SeLe4n.ObjId} (H : notificationLabelsAgree ctx st)
    (hNe : ∀ j, j ≠ k → st'.objects[j]? = st.objects[j]?)
    (hSelf : ∀ o', st'.objects[k]? = some o' → notificationEntryLabelsAgree ctx k o') :
    notificationLabelsAgree ctx st' := fun oid obj' hO => by
  by_cases hk : oid = k
  · subst hk; exact hSelf obj' hO
  · rw [hNe _ hk] at hO; exact H oid obj' hO

/-- A raw insert. -/
theorem insert {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject} (hInv : st.objects.invExt)
    (H : notificationLabelsAgree ctx st) (hSelf : notificationEntryLabelsAgree ctx k o) :
    notificationLabelsAgree ctx { st with objects := st.objects.insert k o } :=
  of_slot H (fun j hj => by
      show (st.objects.insert k o)[j]? = _
      simp only [RHTable_getElem?_eq_get?]
      exact RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hj (eq_of_beq hb).symm) hInv)
    fun o' hO => by
      have : (st.objects.insert k o)[k]? = some o := by
        simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
      rw [show ({ st with objects := st.objects.insert k o } : SystemState).objects[k]? = _ from this] at hO
      cases hO; exact hSelf

/-- A store. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (h : SeLe4n.Model.storeObject k o st = .ok ((), st'))
    (H : notificationLabelsAgree ctx st) (hSelf : notificationEntryLabelsAgree ctx k o) :
    notificationLabelsAgree ctx st' :=
  of_slot H (fun j hj => storeObject_objects_ne st st' k j o hj hInv h) fun o' hO => by
    rw [storeObject_objects_eq st st' k o hInv h] at hO
    cases hO; exact hSelf

/-- **The unchecked TCB write.** -/
theorem updateTcb {st : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (H : notificationLabelsAgree ctx st)
    (hSelf : ∀ x, st.objects[t.toObjId]? = some (.tcb x) →
      notificationEntryLabelsAgree ctx t.toObjId (.tcb (f x))) :
    notificationLabelsAgree ctx (st.updateTcb t f) := by
  cases hT : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact H
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hT]
    exact insert hInv H (hSelf x ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT))

/-- **The checked TCB write.** -/
theorem modifyTcb {st st' : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st')
    (H : notificationLabelsAgree ctx st)
    (hSelf : ∀ x, st.objects[t.toObjId]? = some (.tcb x) →
      notificationEntryLabelsAgree ctx t.toObjId (.tcb (f x))) :
    notificationLabelsAgree ctx st' := by
  obtain ⟨tcb, hL, hSt⟩ := modifyTcb_ok_decompose h
  exact storeObject hInv hSt H (hSelf tcb (lookupTcb_some_objects st t tcb hL))

/-- A thread's share, with its link labels stated. -/
theorem tcb_entry {oid : SeLe4n.ObjId} {y : TCB}
    (hI : ∀ nid, y.ipcState = .blockedOnNotification nid →
      notificationFlowGate ctx nid (SeLe4n.ThreadId.ofObjId oid) = true)
    (hP : ∀ u, y.ntfnPrev = some u → ctx.threadLabelOf u = ctx.threadLabelOf (SeLe4n.ThreadId.ofObjId oid))
    (hN : ∀ u, y.ntfnNext = some u → ctx.threadLabelOf u = ctx.threadLabelOf (SeLe4n.ThreadId.ofObjId oid)) :
    notificationEntryLabelsAgree ctx oid (.tcb y) := ⟨hI, hP, hN⟩

/-- **A thread's links rewritten**, its IPC state kept, each new neighbour of
its label. -/
theorem linksWrite {st : SystemState} {oid : SeLe4n.ObjId} {x : TCB} {p n : Nat}
    (H : notificationLabelsAgree ctx st) (hO : st.objects[oid]? = some (.tcb x))
    (hP : ∀ u, SeLe4n.ThreadId.ofOptCode p = some u →
      ctx.threadLabelOf u = ctx.threadLabelOf (SeLe4n.ThreadId.ofObjId oid))
    (hN : ∀ u, SeLe4n.ThreadId.ofOptCode n = some u →
      ctx.threadLabelOf u = ctx.threadLabelOf (SeLe4n.ThreadId.ofObjId oid)) :
    notificationEntryLabelsAgree ctx oid (.tcb { x with ntfnPrevCode := p, ntfnNextCode := n }) :=
  ⟨(H oid _ hO).1, hP, hN⟩

/-- **A notification's queue fields rewritten**, each new end and the bound
thread admitted by the gate. -/
theorem ntfn_entry {oid : SeLe4n.ObjId} {n : Notification}
    (hB : ∀ t, n.boundTCB = some t → notificationFlowGate ctx oid t = true)
    (hH : ∀ t, n.waitHead = some t → notificationFlowGate ctx oid t = true)
    (hT : ∀ t, n.waitTail = some t → notificationFlowGate ctx oid t = true) :
    notificationEntryLabelsAgree ctx oid (.notification n) := ⟨hB, hH, hT⟩

/-- The gate at a thread of an admitted thread's label. -/
theorem gate_of_label {oid : SeLe4n.ObjId} {t u : SeLe4n.ThreadId}
    (hG : notificationFlowGate ctx oid t = true) (hL : ctx.threadLabelOf u = ctx.threadLabelOf t) :
    notificationFlowGate ctx oid u = true :=
  (twoWayLabelGate_iff_eq _ _).mpr (((twoWayLabelGate_iff_eq _ _).mp hG).trans hL.symm)

/-- Two threads admitted at one notification carry one label. -/
theorem label_of_gates {oid : SeLe4n.ObjId} {t u : SeLe4n.ThreadId}
    (ht : notificationFlowGate ctx oid t = true) (hu : notificationFlowGate ctx oid u = true) :
    ctx.threadLabelOf u = ctx.threadLabelOf t :=
  ((twoWayLabelGate_iff_eq _ _).mp hu).symm.trans ((twoWayLabelGate_iff_eq _ _).mp ht)

end notificationLabelsAgree

/-! ### The link writes -/

namespace notificationLabelsAgree

variable {ctx : LabelingContext}

theorem modifyTcb_invExt {st st' : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st') :
    st'.objects.invExt := by
  obtain ⟨_, _, hSt⟩ := modifyTcb_ok_decompose h
  exact storeObject_preserves_objects_invExt st st' _ _ hInv hSt

/-- **The neighbours spliced**: the predecessor's successor and the
successor's predecessor rewritten, where the two carry one label. -/
theorem unlinkNtfnNeighbours {st : SystemState} {prev next : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (H : notificationLabelsAgree ctx st)
    (hL : ∀ p n, prev = some p → next = some n → ctx.threadLabelOf p = ctx.threadLabelOf n) :
    notificationLabelsAgree ctx (_root_.SeLe4n.Kernel.unlinkNtfnNeighbours st prev next) := by
  unfold _root_.SeLe4n.Kernel.unlinkNtfnNeighbours
  cases prev with
  | none =>
    cases next with
    | none => exact H
    | some n =>
      exact updateTcb hInv H fun x hx => ⟨(H _ _ hx).1, fun u hu => by
        simp [TCB.ntfnPrev] at hu, (H _ _ hx).2.2⟩
  | some p =>
    have H1 : notificationLabelsAgree ctx
        (st.updateTcb p (fun t => { t with ntfnNextCode := SeLe4n.ThreadId.optCode next })) :=
      updateTcb hInv H fun x hx => ⟨(H _ _ hx).1, (H _ _ hx).2.1, fun u hu => by
        simp only [TCB.ntfnNext, SeLe4n.ThreadId.ofOptCode_optCode] at hu
        exact (hL p u rfl hu).symm⟩
    have I1 := SystemState.updateTcb_preserves_objects_invExt st p
      (fun t => { t with ntfnNextCode := SeLe4n.ThreadId.optCode next }) hInv
    cases next with
    | none => exact H1
    | some n =>
      exact updateTcb I1 H1 fun x hx => ⟨(H1 _ _ hx).1, fun u hu => by
        simp only [TCB.ntfnPrev, SeLe4n.ThreadId.ofOptCode_optCode, Option.some.injEq] at hu
        subst hu; exact hL _ n rfl rfl, (H1 _ _ hx).2.2⟩

end notificationLabelsAgree

namespace NtfnLabelsKept

/-- **A thread leaving its queue keeps no links.** -/
theorem clearNtfnLinks (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    NtfnLabelsKept st (_root_.SeLe4n.Kernel.clearNtfnLinks st t) := fun _ H =>
  notificationLabelsAgree.updateTcb hInv H fun _ hx =>
    notificationLabelsAgree.linksWrite H hx (by simp) (by simp)

/-- **The head's detach**: the old head drops its links, its successor its
predecessor. -/
theorem detachNtfnHead (st : SystemState) (h : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : NtfnLabelsKept st (_root_.SeLe4n.Kernel.detachNtfnHead st h next) :=
  fun ctx H => notificationLabelsAgree.unlinkNtfnNeighbours
    (SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv) (clearNtfnLinks st h hInv ctx H)
    (fun _ _ hp => by cases hp)

theorem detachNtfnHeadCode (st : SystemState) (h : SeLe4n.ThreadId) (c : Nat)
    (hInv : st.objects.invExt) :
    NtfnLabelsKept st (_root_.SeLe4n.Kernel.detachNtfnHeadCode st h c) := by
  have := detachNtfnHead st h (SeLe4n.ThreadId.ofOptCode c) hInv
  rwa [detachNtfnHead_eq_code, SeLe4n.ThreadId.optCode_ofOptCode] at this

end NtfnLabelsKept

namespace notificationLabelsAgree

variable {ctx : LabelingContext}

/-- **A parked waiter linked in behind the old tail**, the tail of its label. -/
theorem linkNtfnWaiter {st st' : SystemState} {w : SeLe4n.ThreadId} {tail : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.linkNtfnWaiter st w tail = .ok st')
    (H : notificationLabelsAgree ctx st)
    (hL : ∀ u, tail = some u → ctx.threadLabelOf u = ctx.threadLabelOf w) :
    notificationLabelsAgree ctx st' := by
  unfold _root_.SeLe4n.Kernel.linkNtfnWaiter at h
  cases h3 : storeTcbNtfnLinks st w tail none with
  | error _ => rw [h3] at h; cases h
  | ok st3 =>
    rw [h3] at h
    have I3 := modifyTcb_invExt hInv h3
    have H3 : notificationLabelsAgree ctx st3 := modifyTcb hInv h3 H fun _ hx =>
      linksWrite H hx (fun u hu => by simpa using hL u (by simpa using hu)) (by simp)
    unfold relinkNtfnNext modifyTcbOpt at h
    cases tail with
    | none => cases h; exact H3
    | some t =>
      exact modifyTcb I3 h H3 fun x hx => ⟨(H3 _ _ hx).1, (H3 _ _ hx).2.1, fun u hu => by
        simp only [TCB.ntfnNext, SeLe4n.ThreadId.ofOptCode_optCode, Option.some.injEq] at hu
        subst hu; exact (hL t rfl).symm⟩

end notificationLabelsAgree

namespace NtfnLabelsKept

open notificationLabelsAgree in
/-- **A thread taken out of its notification queue** (`tcbEPDequeue`): the new
queue ends are its neighbours or the old ends, and its neighbours, spliced,
carry its label, which is the notification's. -/
theorem removeFromNotificationWaitQueue (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    NtfnLabelsKept st (_root_.SeLe4n.Kernel.removeFromNotificationWaitQueue st t) := fun ctx H => by
  unfold _root_.SeLe4n.Kernel.removeFromNotificationWaitQueue
  split
  · rename_i tcb hT
    split
    · rename_i oid hI
      split
      · rename_i notif hN hW
        dsimp only
        have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
        have hNo := (SystemState.getNotification?_eq_some_iff _ _ _).mp hN
        obtain ⟨hSelf, hP, hNx⟩ := H _ _ hTo
        have hG : notificationFlowGate ctx oid t = true := hSelf oid hI
        obtain ⟨hB, hH, hTl⟩ := H _ _ hNo
        have gP : ∀ u, tcb.ntfnPrev = some u → notificationFlowGate ctx oid u = true :=
          fun u hu => notificationLabelsAgree.gate_of_label hG (hP u hu)
        have gN : ∀ u, tcb.ntfnNext = some u → notificationFlowGate ctx oid u = true :=
          fun u hu => notificationLabelsAgree.gate_of_label hG (hNx u hu)
        have H1 := notificationLabelsAgree.insert (o := .notification { notif with
            waitHeadCode := SeLe4n.ThreadId.optCode
              (if notif.waitHead = some t then tcb.ntfnNext else notif.waitHead)
            waitTailCode := SeLe4n.ThreadId.optCode (if tcb.ntfnNext.isSome then notif.waitTail
              else if notif.waitHead = some t then none else tcb.ntfnPrev)
            state := if notif.state = .waiting ∧
                (if notif.waitHead = some t then tcb.ntfnNext else notif.waitHead).isNone
              then .idle else notif.state }) hInv H (notificationLabelsAgree.ntfn_entry hB
            (fun u hu => by
              change SeLe4n.ThreadId.ofOptCode (SeLe4n.ThreadId.optCode
                (if notif.waitHead = some t then tcb.ntfnNext else notif.waitHead)) = some u at hu
              rw [SeLe4n.ThreadId.ofOptCode_optCode] at hu
              by_cases hc : notif.waitHead = some t
              · rw [if_pos hc] at hu; exact gN u hu
              · rw [if_neg hc] at hu; exact hH u hu)
            (fun u hu => by
              change SeLe4n.ThreadId.ofOptCode (SeLe4n.ThreadId.optCode
                (if tcb.ntfnNext.isSome then notif.waitTail
                  else if notif.waitHead = some t then none else tcb.ntfnPrev)) = some u at hu
              rw [SeLe4n.ThreadId.ofOptCode_optCode] at hu
              by_cases hc : tcb.ntfnNext.isSome = true
              · rw [if_pos hc] at hu; exact hTl u hu
              · rw [if_neg hc] at hu
                by_cases hc2 : notif.waitHead = some t
                · rw [if_pos hc2] at hu; cases hu
                · rw [if_neg hc2] at hu; exact gP u hu))
        exact notificationLabelsAgree.unlinkNtfnNeighbours
          (SystemState.updateTcb_preserves_objects_invExt _ _ _
            (RHTable_insert_preserves_invExt _ _ _ hInv))
          (clearNtfnLinks _ t (RHTable_insert_preserves_invExt _ _ _ hInv) ctx H1) fun p n hp hn => by
            have hn' : ctx.threadLabelOf n = ctx.threadLabelOf t := hNx n hn
            split at hp
            · cases hp
            · exact (hP p hp).trans hn'.symm
      · exact H
    · exact H
  · exact H

end NtfnLabelsKept

end SeLe4n.Kernel
