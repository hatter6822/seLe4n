-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.IPC.Operations.CancelAll
import SeLe4n.Kernel.RobinHood.Invariant.InPlaceCommute
import SeLe4n.Kernel.RobinHood.Invariant.MapValueAt

/-!
# The suspend's checks, read before any write

seL4's `suspend` never fails once its target is decoded: it cancels the
thread's IPC, marks it `Inactive` and takes it off the scheduler.  The
specification here (`Lifecycle.Suspend.suspendThreadOnCore`) also ends the
thread's reservation: a context bound to it is released and a context it holds
on loan goes back to its lender, and that return
(`cleanupDonatedSchedContext`) can refuse after the teardown has written.

This module asks, on the state the suspend is handed and before anything is
written, every question the suspend's later steps ask of the states they run
on (`suspendAdmitted`): the IPC the thread is blocked in, the binding it holds
once the teardown has run, and whether the return of a loan commits.  When the
checks pass the suspend's state is `suspendPerform`, every write in its slot
(`suspendThreadOnCore_of_admitted`), so the syscall entry hands the state to
the writes alone (`RefusalCarrying.ofChecked`) and keeps no copy of it for a
refusal that cannot come.

No question here assumes the store invariant: each lookup a later step makes is
answered through the table's own frame (`RHTable.get?_mapValueAt`), which holds
on every table whose writes land in place, and that is one `O(1)` question of
the table (`RHTable.noResizeDue`), asked once.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  Stores at a present key on a table no insert resizes
-- ============================================================================

/-- A store at a key the table holds, on a table no insert resizes, lands in
place. -/
theorem findsInPlace_of_present {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hNR : st.objects.noResizeDue) (hk : st.objects[k]? = some o) :
    st.objects.findsInPlace k = true :=
  RHTable.findsInPlace_of_get? hNR hk

/-- ...so it leaves every other key's object. -/
theorem storeObject_keeps_other_of_present {st st' : SystemState} {k j : SeLe4n.ObjId}
    {o0 o : KernelObject} (hNR : st.objects.noResizeDue) (hk : st.objects[k]? = some o0)
    (hS : storeObject k o st = .ok ((), st')) (hne : j ≠ k) :
    st'.objects[j]? = st.objects[j]? :=
  storeObject_objects_ne_of_findsInPlace (findsInPlace_of_present hNR hk) (Ne.symm hne) hS

/-- ...reads back what it wrote... -/
theorem storeObject_self_of_present {st st' : SystemState} {k : SeLe4n.ObjId}
    {o0 o : KernelObject} (hNR : st.objects.noResizeDue) (hk : st.objects[k]? = some o0)
    (hS : storeObject k o st = .ok ((), st')) :
    st'.objects[k]? = some o :=
  storeObject_objects_self_of_findsInPlace (findsInPlace_of_present hNR hk) hS

/-- ...and leaves the table one no insert resizes. -/
theorem storeObject_noResizeDue_of_present {st st' : SystemState} {k : SeLe4n.ObjId}
    {o0 o : KernelObject} (hNR : st.objects.noResizeDue) (hk : st.objects[k]? = some o0)
    (hS : storeObject k o st = .ok ((), st')) :
    st'.objects.noResizeDue := by
  have hF := findsInPlace_of_present hNR hk
  have hF' : st'.objects.findsInPlace k = true := by
    rw [storeObject_findsInPlace_of_findsInPlace hF hS]; exact hF
  exact RHTable.noResizeDue_of_findsInPlace hF'

/-- A reply store keeps every object that is no reply. -/
private theorem storeReply_keeps_nonReply_nr {s s' : SystemState} {k : SeLe4n.ObjId}
    {r0 r' : Reply} (hNR : s.objects.noResizeDue) (hK : s.objects[k]? = some (.reply r0))
    (hS : storeObject k (.reply r') s = .ok ((), s'))
    {j : SeLe4n.ObjId} {o : KernelObject} (hJ : s.objects[j]? = some o)
    (hO : ∀ r, o ≠ KernelObject.reply r) :
    s'.objects[j]? = some o := by
  have hne : j ≠ k := by
    intro e; subst e; rw [hK] at hJ; cases hJ; exact hO r0 rfl
  rw [storeObject_keeps_other_of_present hNR hK hS hne]; exact hJ

/-- After a reply store at a reply, every key that held a reply still holds
one. -/
private theorem storeReply_keeps_reply_nr {s s' : SystemState} {k : SeLe4n.ObjId}
    {r0 r' : Reply} (hNR : s.objects.noResizeDue) (hK : s.objects[k]? = some (.reply r0))
    (hS : storeObject k (.reply r') s = .ok ((), s'))
    {j : SeLe4n.ObjId} {r : Reply} (hJ : s.objects[j]? = some (.reply r)) :
    ∃ r'', s'.objects[j]? = some (.reply r'') := by
  by_cases e : j = k
  · subst e; exact ⟨r', storeObject_self_of_present hNR hK hS⟩
  · exact ⟨r, by rw [storeObject_keeps_other_of_present hNR hK hS e]; exact hJ⟩

/-- The reply-stack head pop commits when its head and the head's lower frame
are replies, keeps every object that is no reply, and leaves the table one no
insert resizes. -/
private theorem storeDonationHeadPop_ok_of_nr {s : SystemState} {scId : SeLe4n.SchedContextId}
    {rid : SeLe4n.ReplyId} {r : Reply} (hNR : s.objects.noResizeDue)
    (hR : s.objects[rid.toObjId]? = some (.reply r))
    (hPrev : ∀ p, r.prev = some p → ∃ b, s.objects[p.toObjId]? = some (.reply b)) :
    ∃ s', storeDonationHeadPop scId (some (rid, r)) s = .ok s' ∧ s'.objects.noResizeDue ∧
      ∀ (j : SeLe4n.ObjId) (o : KernelObject), s.objects[j]? = some o →
        (∀ r, o ≠ KernelObject.reply r) → s'.objects[j]? = some o := by
  have hG : s.getReply? rid = some r := (SystemState.getReply?_eq_some_iff _ _ _).mpr hR
  obtain ⟨s1, hS1⟩ : ∃ s1, storeObject rid.toObjId (.reply { r with prev := none, next := none }) s
      = .ok ((), s1) := ⟨_, rfl⟩
  have hNR1 := storeObject_noResizeDue_of_present hNR hR hS1
  have hC : storeDonationHeadClear (some rid) s = .ok s1 := by
    rw [storeDonationHeadClear_some, hG]; simp only []; rw [hS1]
  rw [storeDonationHeadPop_some, hC]; simp only []
  cases hP : r.prev with
  | none =>
    exact ⟨s1, storeReplyReHead_none _ _, hNR1,
      fun j o hJ hO => storeReply_keeps_nonReply_nr hNR hR hS1 hJ hO⟩
  | some p =>
    obtain ⟨b, hB⟩ := hPrev p hP
    obtain ⟨b1, hB1⟩ := storeReply_keeps_reply_nr hNR hR hS1 hB
    have hG1 : s1.getReply? p = some b1 := (SystemState.getReply?_eq_some_iff _ _ _).mpr hB1
    obtain ⟨s2, hS2⟩ : ∃ s2, storeObject p.toObjId (.reply { b1 with next := some (.head scId) }) s1
        = .ok ((), s2) := ⟨_, rfl⟩
    refine ⟨s2, ?_, storeObject_noResizeDue_of_present hNR1 hB1 hS2,
      fun j o hJ hO => storeReply_keeps_nonReply_nr hNR1 hB1 hS2
        (storeReply_keeps_nonReply_nr hNR hR hS1 hJ hO) hO⟩
    rw [storeReplyReHead_some, hG1]; simp only []; rw [hS2]

/-- **The donation return commits on every state `donatedReturnCommits` admits,
on a table no insert resizes** (`returnDonatedSchedContextResolved_ok_of_commits`
without the store invariant): every store the return makes is at a key the
admission has read, so it lands in place and keeps every other key. -/
theorem returnDonatedSchedContextResolved_ok_of_commits_nr {st : SystemState}
    {serverTid : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId}
    (hNR : st.objects.noResizeDue)
    (h : donatedReturnCommits st serverTid scId originalOwner = true) :
    ∃ st', returnDonatedSchedContextResolved st serverTid scId originalOwner = .ok st' := by
  unfold donatedReturnCommits at h
  unfold returnDonatedSchedContextResolved
  cases hRes : replyStackOuterCaller? st scId with
  | error e => rw [hRes] at h; cases h
  | ok newOwner? =>
    rw [hRes] at h
    simp only []
    cases hSc : st.getSchedContext? scId with
    | none => rw [hSc] at h; cases h
    | some sc =>
      rw [hSc] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨hB, hOut⟩, hRcp⟩, hOw⟩, hSv⟩ := h
      unfold returnDonatedSchedContext
      rw [hSc]
      simp only [bne_iff_ne, ne_eq, hOut, hRcp, Bool.not_true]
      have hBeq : sc.boundThread = some serverTid := by simpa using hB
      rw [if_neg (fun hn => hn hBeq)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hScO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
      have hHead : ∃ head?, donationHeadOf? st scId sc = .ok head? ∧
          ∀ rid r, head? = some (rid, r) →
            st.objects[rid.toObjId]? = some (.reply r) ∧
            ∀ p, r.prev = some p → ∃ b, st.objects[p.toObjId]? = some (.reply b) := by
        unfold replyStackOuterCaller? at hRes
        rw [hSc] at hRes
        simp only [] at hRes
        cases hH : donationHeadOf? st scId sc with
        | error e => rw [hH] at hRes; cases hRes
        | ok head? =>
          refine ⟨head?, rfl, fun rid r hEq => ?_⟩
          subst hEq
          rw [hH] at hRes
          simp only [] at hRes
          have hHeadAt : st.objects[rid.toObjId]? = some (.reply r) := by
            unfold donationHeadOf? at hH
            revert hH
            cases sc.scReply with
            | none => intro hH; cases hH
            | some rid' =>
              simp only []
              cases hG : st.getReply? rid' with
              | none => intro hH; cases hH
              | some r' =>
                simp only []
                split
                · intro hH; cases hH
                · intro hH; cases hH
                  exact (SystemState.getReply?_eq_some_iff _ _ _).mp hG
          refine ⟨hHeadAt, fun p hP => ?_⟩
          rw [hP] at hRes
          simp only [] at hRes
          cases hGb : st.getReply? p with
          | none => rw [hGb] at hRes; cases hRes
          | some b => exact ⟨b, (SystemState.getReply?_eq_some_iff _ _ _).mp hGb⟩
      obtain ⟨head?, hH, hHeadFacts⟩ := hHead
      rw [hH]
      simp only []
      obtain ⟨st1, hS1⟩ : ∃ st1, storeObject scId.toObjId (.schedContext
          (donationReturnSchedContext sc originalOwner (head?.bind (fun p => p.2.prev)) newOwner?))
          st = .ok ((), st1) := ⟨_, rfl⟩
      rw [hS1]
      simp only []
      have hNR1 := storeObject_noResizeDue_of_present hNR hScO hS1
      obtain ⟨ow, hOwL⟩ := Option.isSome_iff_exists.mp hOw
      obtain ⟨sv, hSvL⟩ := Option.isSome_iff_exists.mp hSv
      have hOwNR := lookupTcb_some_not_reserved _ _ _ hOwL
      have hSvNR := lookupTcb_some_not_reserved _ _ _ hSvL
      have hOwO : st.objects[originalOwner.toObjId]? = some (.tcb ow) :=
        (SystemState.getTcb?_eq_some_iff _ _ _).mp (by
          unfold lookupTcb at hOwL; rw [if_neg hOwNR] at hOwL; exact hOwL)
      have hSvO : st.objects[serverTid.toObjId]? = some (.tcb sv) :=
        (SystemState.getTcb?_eq_some_iff _ _ _).mp (by
          unfold lookupTcb at hSvL; rw [if_neg hSvNR] at hSvL; exact hSvL)
      have keep1 : ∀ (k : SeLe4n.ObjId) (t : TCB), st.objects[k]? = some (KernelObject.tcb t) →
          st1.objects[k]? = some (KernelObject.tcb t) := by
        intro k t hk
        have hne : k ≠ scId.toObjId := by
          intro e; subst e; rw [hScO] at hk; cases hk
        rw [storeObject_keeps_other_of_present hNR hScO hS1 hne]; exact hk
      obtain ⟨st2, hS2, hNR2, keep2⟩ : ∃ st2, storeDonationHeadPop scId head? st1 = .ok st2 ∧
          st2.objects.noResizeDue ∧
          ∀ (k : SeLe4n.ObjId) (t : TCB), st1.objects[k]? = some (KernelObject.tcb t) →
            st2.objects[k]? = some (KernelObject.tcb t) := by
        cases hHd : head? with
        | none => exact ⟨st1, rfl, hNR1, fun _ _ h => h⟩
        | some pr =>
          obtain ⟨rid, r⟩ := pr
          obtain ⟨hHeadAt, hPrev⟩ := hHeadFacts rid r hHd
          have hne : rid.toObjId ≠ scId.toObjId := by
            intro e; rw [e, hScO] at hHeadAt; cases hHeadAt
          have hHeadAt1 : st1.objects[rid.toObjId]? = some (.reply r) := by
            rw [storeObject_keeps_other_of_present hNR hScO hS1 hne]; exact hHeadAt
          have hPrev1 : ∀ p, r.prev = some p → ∃ b, st1.objects[p.toObjId]? = some (.reply b) := by
            intro p hp
            obtain ⟨b, hb⟩ := hPrev p hp
            have hne' : p.toObjId ≠ scId.toObjId := by
              intro e; rw [e, hScO] at hb; cases hb
            exact ⟨b, by rw [storeObject_keeps_other_of_present hNR hScO hS1 hne']; exact hb⟩
          obtain ⟨st2, h2, hN2, hk⟩ := storeDonationHeadPop_ok_of_nr (scId := scId) hNR1 hHeadAt1 hPrev1
          exact ⟨st2, h2, hN2, fun k t hkt => hk k _ hkt (fun _ h => by cases h)⟩
      rw [hS2]
      simp only []
      have hOw2O : st2.objects[originalOwner.toObjId]? = some (.tcb ow) := keep2 _ _ (keep1 _ _ hOwO)
      have hOw2 : lookupTcb st2 originalOwner = some ow := by
        unfold lookupTcb; rw [if_neg hOwNR]
        exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr hOw2O
      rw [hOw2]
      simp only []
      generalize hOwT : ({ ow with
          scBindingScCode := SchedContextBinding.scCode (donationReturnBinding scId newOwner?),
          scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding scId newOwner?) } : TCB) = owT
      obtain ⟨st3, hS3⟩ : ∃ st3, storeObject originalOwner.toObjId (.tcb owT) st2 = .ok ((), st3) :=
        ⟨_, rfl⟩
      rw [hS3]
      simp only []
      have hSv3 : ∃ t, lookupTcb st3 serverTid = some t := by
        unfold lookupTcb; rw [if_neg hSvNR]
        by_cases e : serverTid.toObjId = originalOwner.toObjId
        · exact ⟨owT, (SystemState.getTcb?_eq_some_iff _ _ _).mpr
            (by rw [e]; exact storeObject_self_of_present hNR2 hOw2O hS3)⟩
        · exact ⟨sv, (SystemState.getTcb?_eq_some_iff _ _ _).mpr
            (by rw [storeObject_keeps_other_of_present hNR2 hOw2O hS3 e]
                exact keep2 _ _ (keep1 _ _ hSvO))⟩
      obtain ⟨svT, hSvT⟩ := hSv3
      rw [hSvT]
      exact ⟨_, rfl⟩

-- ============================================================================
-- §2  Writes that keep every thread's binding
-- ============================================================================

/-- `st'` is `st` written in place: no insert resizes it, and every thread `st`
holds is still held, with the same scheduling-context binding codes. -/
def TcbBindingsKept (st st' : SystemState) : Prop :=
  st'.objects.noResizeDue ∧ ∀ u t, st.getTcb? u = some t →
    ∃ t', st'.getTcb? u = some t' ∧ t'.scBindingScCode = t.scBindingScCode ∧
      t'.scBindingOwnerCode = t.scBindingOwnerCode

theorem TcbBindingsKept.refl {st : SystemState} (h : st.objects.noResizeDue) :
    TcbBindingsKept st st :=
  ⟨h, fun _ t ht => ⟨t, ht, rfl, rfl⟩⟩

theorem TcbBindingsKept.trans {a b c : SystemState} (h₁ : TcbBindingsKept a b)
    (h₂ : TcbBindingsKept b c) : TcbBindingsKept a c := by
  refine ⟨h₂.1, fun u t ht => ?_⟩
  obtain ⟨t1, h1, e1, f1⟩ := h₁.2 u t ht
  obtain ⟨t2, h2, e2, f2⟩ := h₂.2 u t1 h1
  exact ⟨t2, h2, e2.trans e1, f2.trans f1⟩

/-- An object update in its slot that maps each thread to one with its binding
codes keeps every thread's binding. -/
theorem TcbBindingsKept.modifyObject {st : SystemState} (hNR : st.objects.noResizeDue)
    (k : SeLe4n.ObjId) (g : KernelObject → KernelObject)
    (hg : ∀ t, ∃ t', g (.tcb t) = .tcb t' ∧ t'.scBindingScCode = t.scBindingScCode ∧
      t'.scBindingOwnerCode = t.scBindingOwnerCode) :
    TcbBindingsKept st (st.modifyObject k g) := by
  have hObj : (st.modifyObject k g).objects = st.objects.mapValueAt k g := by
    unfold SystemState.modifyObject; exact RHTable.modify_eq_mapValueAt k g hNR
  refine ⟨?_, fun u t ht => ?_⟩
  · unfold RHTable.noResizeDue at hNR ⊢
    rw [hObj, RHTable.mapValueAt_size, RHTable.mapValueAt_capacity]; exact hNR
  · have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht
    rw [RHTable_getElem?_eq_get?] at hO
    by_cases hk : (k == u.toObjId) = true
    · obtain ⟨t', hgt, he, hf⟩ := hg t
      refine ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr ?_, he, hf⟩
      rw [RHTable_getElem?_eq_get?, hObj, RHTable.get?_mapValueAt, if_pos hk, hO]
      simp [hgt]
    · refine ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mpr ?_, rfl, rfl⟩
      rw [RHTable_getElem?_eq_get?, hObj, RHTable.get?_mapValueAt, if_neg hk, hO]

/-- A thread update that keeps the binding codes keeps every thread's binding. -/
theorem TcbBindingsKept.updateTcb {st : SystemState} (hNR : st.objects.noResizeDue)
    (x : SeLe4n.ThreadId) (f : TCB → TCB)
    (hf : ∀ t, (f t).scBindingScCode = t.scBindingScCode ∧
      (f t).scBindingOwnerCode = t.scBindingOwnerCode) :
    TcbBindingsKept st (st.updateTcb x f) := by
  rw [SystemState.updateTcb_eq_impl]
  unfold SystemState.updateTcbImpl
  split
  · exact TcbBindingsKept.modifyObject hNR _ _ fun t => ⟨f t, rfl, (hf t).1, (hf t).2⟩
  · exact TcbBindingsKept.refl hNR

theorem unlinkNtfnNeighbours_bindingsKept {st : SystemState} (hNR : st.objects.noResizeDue)
    (prev next : Option SeLe4n.ThreadId) :
    TcbBindingsKept st (unlinkNtfnNeighbours st prev next) := by
  unfold unlinkNtfnNeighbours
  cases prev with
  | none =>
    cases next with
    | none => exact TcbBindingsKept.refl hNR
    | some n => exact TcbBindingsKept.updateTcb hNR n _ (fun _ => ⟨rfl, rfl⟩)
  | some p =>
    have h := TcbBindingsKept.updateTcb hNR p
      (fun t => { t with ntfnNextCode := SeLe4n.ThreadId.optCode next }) (fun _ => ⟨rfl, rfl⟩)
    cases next with
    | none => exact h
    | some n => exact h.trans (TcbBindingsKept.updateTcb h.1 n _ (fun _ => ⟨rfl, rfl⟩))

theorem clearNtfnLinks_bindingsKept {st : SystemState} (hNR : st.objects.noResizeDue)
    (t : SeLe4n.ThreadId) : TcbBindingsKept st (clearNtfnLinks st t) := by
  unfold clearNtfnLinks
  exact TcbBindingsKept.updateTcb hNR t _ (fun _ => ⟨rfl, rfl⟩)

theorem restoreToReadyCancelled_bindingsKept {st : SystemState} (hNR : st.objects.noResizeDue)
    (t : SeLe4n.ThreadId) :
    TcbBindingsKept st (Lifecycle.Suspend.restoreToReadyCancelled st t) := by
  unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
  exact TcbBindingsKept.updateTcb hNR t _ (fun _ => ⟨rfl, rfl⟩)

/-- **A notification waiter's cancel keeps every thread's binding**
(`storeNotificationBlockedCancelled`): the notification's cell, the waiter's
and its neighbours' links and the waiter's restore each rewrite a slot and no
binding code. -/
theorem storeNotificationBlockedCancelled_bindingsKept {st : SystemState}
    (hNR : st.objects.noResizeDue) (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (isHead : Bool)
    (prev next : Option SeLe4n.ThreadId) :
    TcbBindingsKept st (storeNotificationBlockedCancelled st n t isHead prev next) := by
  unfold storeNotificationBlockedCancelled
  have h1 := TcbBindingsKept.modifyObject hNR n (cancelledNotificationObject isHead prev next)
    (fun t => ⟨t, rfl, rfl, rfl⟩)
  have h2 := h1.trans (clearNtfnLinks_bindingsKept h1.1 t)
  have h3 := h2.trans (unlinkNtfnNeighbours_bindingsKept h2.1 (if isHead then none else prev) next)
  exact h3.trans (restoreToReadyCancelled_bindingsKept h3.1 t)

-- ============================================================================
-- §3  The suspend's checks and its writes
-- ============================================================================

namespace Lifecycle.Suspend

/-- **The IPC teardown of an admitted suspend, as its writes** (seL4's
`cancelIPC`): a thread blocked on a notification leaves that notification's
queue wherever it waits there and is restored `.ready` with the cancellation
frame (`storeNotificationBlockedCancelled`, which the specification's
`cancelIpcBlocking` notification arm is, `cancelIpcBlocking_notification_inPlace`);
any other thread is left as it is.  The notification is read once, and the
waiter's head question is asked of its code. -/
def suspendTeardownState (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some tcb =>
    match tcb.ipcStateCode with
    | 2 =>
      let n : SeLe4n.ObjId := ⟨tcb.ipcObjectCode⟩
      match st.getNotification? n with
      | some ntfn =>
        storeNotificationBlockedCancelled st n tid (ntfn.waitHeadCode == tid.val + 1)
          tcb.ntfnPrev tcb.ntfnNext
      | none => st
    | _ => st
  | none => st

/-- **Whether the thread at `tid` holds a context on loan**, read off its two
binding codes (`.donated`, `SchedContextBinding.ofCodes`). -/
@[inline] def suspendHoldsLoan (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? tid with
  | some tcb => tcb.scBindingScCode != 0 && tcb.scBindingOwnerCode != 0
  | none => false

/-- **The return of a context the suspended thread holds on loan** (the
specification's `cancelDonatedDonationOnCore`: the context handed back to its
lender through the reply-stack resolver, its replenishments moved to the
lender's core).  On a state the admission reads it never refuses
(`cancelDonationArmOnCore_eq_bindingState`); the identity otherwise. -/
def suspendLoanReturnState (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some tcb =>
    match cancelDonatedDonationOnCore st tid tcb with
    | .ok s => s
    | .error _ => st
  | none => st

/-- **The end of the suspended thread's reservation** (the specification's
`cancelDonationArmOnCore`, read off the state the teardown leaves): a context
it holds on loan goes back to its lender (`suspendLoanReturnState`), a context
bound to it is released (`suspendReleasePerform`), and a thread holding none is
left as it is. -/
def suspendBindingState (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  if suspendHoldsLoan st tid then suspendLoanReturnState st tid
  else suspendReleasePerform st tid

/-- **Whether a loan the thread holds goes back without refusing**, read on the
state the suspend is handed: a thread holding no loan answers `true`; one
holding `s` on loan from `L` is no reserved thread (the return looks it up as
`lookupTcb` does) and the return of `s` to `L` commits
(`donatedReturnCommits`, every refusal of the reply-stack resolver and the
return decided on this state). -/
@[inline] def suspendLoanReturnCommits (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : Bool :=
  match tcb.scBindingScCode with
  | 0 => true
  | s + 1 =>
    match tcb.scBindingOwnerCode with
    | 0 => true
    | o + 1 => !tid.isReserved && donatedReturnCommits st tid ⟨s⟩ ⟨o⟩

/-- **The checks `.tcbSuspend` makes, asked before any write** (seL4's
`decodeTCBInvocation` then `suspend`, which never fails): the target is a
thread not already `.Inactive`, and

* it is blocked on no IPC (`ready`, no object): nothing is torn down, and a
  loan it holds goes back without refusing (`suspendLoanReturnCommits`), its
  slot found in place when it holds one, so the return's reads are this
  state's; or
* it is blocked on a notification the store holds, its slot found in place
  (so the cancel's writes land in place and every thread keeps its binding,
  `storeNotificationBlockedCancelled_bindingsKept`), and it holds no loan: the
  cancel is the specification's (`cancelIpcBlocking_notification_inPlace`) and
  writes no binding, so the binding the release reads is the one read here.

When they pass the suspend's state is `suspendPerform`
(`suspendThreadOnCore_of_admitted`). -/
@[inline] def suspendAdmitted (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? tid with
  | some tcb =>
    !(tcb.threadState == .Inactive) &&
      match tcb.ipcStateCode with
      | 0 =>
        tcb.ipcObjectCode == 0 &&
          (tcb.scBindingOwnerCode == 0 ||
            st.objects.findsInPlace tid.toObjId && suspendLoanReturnCommits st tid tcb)
      | 2 =>
        st.objects.findsInPlace tid.toObjId && tcb.scBindingOwnerCode == 0 &&
          (st.getNotification? ⟨tcb.ipcObjectCode⟩).isSome
      | _ => false
  | none => false

/-- **The admitted suspend** (seL4's `suspend`): the placement, the core
running the thread and the executing core's current priority read before
anything is written; then the IPC teardown (`suspendTeardownState`), the end of
the thread's reservation (`suspendBindingState`), its removal from where the
state places it, its pending state cleared, `.Inactive`, its yield link
cancelled and the local scheduling point.  The state is handed to the writes
alone. -/
def suspendPerform (st : SystemState) (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) :
    SystemState :=
  let tid := vtid.val
  let placed := placedCoreOf? st tid
  let runningCore? := runningCoreOf? st tid
  let curCode := st.scheduler.currentCode.get executingCore
  let prioCode := currentEffectivePrioCode st executingCore
  let st0 := suspendBindingState (suspendTeardownState st tid) tid
  let st1 := descheduleAt st0 tid placed
  let st2 := clearPendingStateValid st1 vtid
  let st3 := st2.updateTcb tid fun t => { t with threadState := .Inactive }
  let st4 := cancelYieldTo st3 tid
  suspendRescheduleState st4 (runningCore?.getD executingCore) executingCore
    runningCore?.isSome (currentDeboostedFromCode st4 executingCore curCode prioCode)

/-- A thread's binding is a function of its two codes. -/
theorem schedContextBinding_eq_of_codes {t t' : TCB}
    (h₁ : t'.scBindingScCode = t.scBindingScCode) (h₂ : t'.scBindingOwnerCode = t.scBindingOwnerCode) :
    t'.schedContextBinding = t.schedContextBinding := by
  unfold TCB.schedContextBinding; rw [h₁, h₂]

/-- **The reservation's end commits as `suspendBindingState`** on a thread
whose loan, when it holds one, goes back without refusing. -/
theorem cancelDonationArmOnCore_eq_bindingState {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} (hT : st.getTcb? tid = some tcb)
    (hC : tcb.scBindingOwnerCode = 0 ∨
      (st.objects.findsInPlace tid.toObjId = true ∧ suspendLoanReturnCommits st tid tcb = true)) :
    cancelDonationArmOnCore st tid tcb = .ok (suspendBindingState st tid) := by
  unfold cancelDonationArmOnCore suspendBindingState suspendHoldsLoan
  rw [hT]
  cases hb : tcb.schedContextBinding with
  | unbound =>
    have hS : tcb.scBindingScCode = 0 := by
      unfold TCB.schedContextBinding SchedContextBinding.ofCodes at hb
      split at hb
      · assumption
      · split at hb <;> cases hb
    simp only [hS, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    unfold suspendReleasePerform; simp only [hT, hb]
  | bound scId =>
    have hO : tcb.scBindingOwnerCode = 0 := by
      unfold TCB.schedContextBinding SchedContextBinding.ofCodes at hb
      split at hb
      · cases hb
      · split at hb
        · assumption
        · cases hb
    simp only [hO, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact cancelBoundDonationOnCore_eq_release hT hb
  | donated scId owner =>
    obtain ⟨s, hs, o, ho, hsc, hoo⟩ : ∃ s, tcb.scBindingScCode = s + 1 ∧ ∃ o,
        tcb.scBindingOwnerCode = o + 1 ∧ scId = ⟨s⟩ ∧ owner = ⟨o⟩ := by
      unfold TCB.schedContextBinding SchedContextBinding.ofCodes at hb
      split at hb
      · cases hb
      · rename_i s hs
        split at hb
        · cases hb
        · rename_i o ho
          cases hb
          exact ⟨s, hs, o, ho, rfl, rfl⟩
    subst hsc hoo
    have hC' : st.objects.findsInPlace tid.toObjId = true ∧
        suspendLoanReturnCommits st tid tcb = true := by
      rcases hC with h | h
      · rw [ho] at h; cases h
      · exact h
    obtain ⟨hF, hR⟩ := hC'
    unfold suspendLoanReturnCommits at hR
    rw [hs, ho] at hR
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hR
    obtain ⟨hNRes, hCommit⟩ := hR
    have hNR := RHTable.noResizeDue_of_findsInPlace hF
    obtain ⟨st', hRet⟩ := returnDonatedSchedContextResolved_ok_of_commits_nr hNR hCommit
    have hLk : lookupTcb st tid = some tcb := by
      unfold lookupTcb; rw [if_neg (by simpa using hNRes)]; exact hT
    have hCl : cleanupDonatedSchedContext st tid = .ok st' := by
      unfold cleanupDonatedSchedContext; rw [hLk]; simp only [hb]; exact hRet
    have hD : cancelDonatedDonationOnCore st tid tcb = .ok
        (migrateSchedContextReplenishment st' ⟨s⟩ (determineTargetCore st tid)
          (determineTargetCore st' ⟨o⟩)) := by
      unfold cancelDonatedDonationOnCore; simp only [hb]; rw [hCl]
    have hL : (s + 1 != 0 && o + 1 != 0) = true := by simp
    simp only [hs, ho, hL, ↓reduceIte, suspendLoanReturnState, hT, hD]

/-- **Every check `suspendThreadOnCore` makes is `suspendAdmitted`'s, and when
it passes the suspend commits as `suspendPerform`.**  The ready arm tears
nothing down; the notification arm's teardown is the in-place cancel and keeps
every binding, so the reservation's end reads the binding the admission read;
the loan's return commits on the state it runs on because that is the state the
admission read. -/
theorem suspendThreadOnCore_of_admitted (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) (h : suspendAdmitted st vtid.val = true) :
    ∃ sgi, suspendThreadOnCore st vtid executingCore =
      .ok (suspendPerform st vtid executingCore, sgi) := by
  unfold suspendAdmitted at h
  cases hT : st.getTcb? vtid.val with
  | none => simp [hT] at h
  | some tcb =>
    simp only [hT, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hI, hArm⟩ := h
    -- the teardown, the revert and the binding the reservation's end reads
    have hMid : cancelIpcBlockingReclaimed vtid.val tcb st = suspendTeardownState st vtid.val ∧
        PriorityInheritance.blockingServer st vtid.val = none ∧
        cancelDonationArmOnCore (suspendTeardownState st vtid.val) vtid.val
          (((suspendTeardownState st vtid.val).getTcb? vtid.val).getD tcb) =
          .ok (suspendBindingState (suspendTeardownState st vtid.val) vtid.val) := by
      cases hc : tcb.ipcStateCode with
      | zero =>
        rw [hc] at hArm
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hArm
        obtain ⟨hO, hL⟩ := hArm
        have hReady : tcb.ipcState = .ready := by
          simp only [TCB.ipcState, hO, hc]; rfl
        have hTd : suspendTeardownState st vtid.val = st := by
          unfold suspendTeardownState; rw [hT]; simp only [hc]
        rw [hTd, hT, Option.getD_some]
        refine ⟨?_, ?_, cancelDonationArmOnCore_eq_bindingState hT ?_⟩
        · rw [cancelIpcBlockingReclaimed_of_no_donation _ _ _
            (by unfold cancelledCallerDonation?; rw [hReady])]
          unfold cancelIpcBlocking; rw [hReady]
        · unfold PriorityInheritance.blockingServer
          rw [hT]; simp [TCB.blockingServer?, hReady]
        · rcases hL with hL | hL
          · exact .inl hL
          · exact .inr hL
      | succ k =>
        cases k with
        | zero => rw [hc] at hArm; cases hArm
        | succ k =>
          cases k with
          | succ k => rw [hc] at hArm; cases hArm
          | zero =>
            rw [hc] at hArm
            simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hArm
            obtain ⟨⟨hF, hO⟩, ntfn, hN⟩ := hArm
            have hB : tcb.ipcState = .blockedOnNotification ⟨tcb.ipcObjectCode⟩ := by
              simp only [TCB.ipcState, hc]; rfl
            have hHead : (ntfn.waitHeadCode == vtid.val.val + 1) = (ntfn.waitHead == some vtid.val) := by
              unfold Notification.waitHead
              cases hw : ntfn.waitHeadCode with
              | zero => simp [SeLe4n.ThreadId.ofOptCode]
              | succ w =>
                simp only [SeLe4n.ThreadId.ofOptCode]
                rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
                constructor
                · intro h
                  have hv : w = vtid.val.val := by omega
                  rw [hv]
                · intro h
                  rw [← Option.some.inj h]
            have hTd : suspendTeardownState st vtid.val =
                storeNotificationBlockedCancelled st ⟨tcb.ipcObjectCode⟩ vtid.val
                  (ntfn.waitHead == some vtid.val) tcb.ntfnPrev tcb.ntfnNext := by
              unfold suspendTeardownState; rw [hT]; simp only [hc, hN, hHead]
            have hNR := RHTable.noResizeDue_of_findsInPlace hF
            obtain ⟨t2, hT2, hS2, hO2⟩ :=
              (storeNotificationBlockedCancelled_bindingsKept hNR ⟨tcb.ipcObjectCode⟩ vtid.val
                (ntfn.waitHead == some vtid.val) tcb.ntfnPrev tcb.ntfnNext).2 _ _ hT
            refine ⟨?_, ?_, ?_⟩
            · rw [cancelIpcBlockingReclaimed_of_no_donation _ _ _
                (by unfold cancelledCallerDonation?; rw [hB]), hTd]
              exact cancelIpcBlocking_notification_inPlace hN hT hB
            · unfold PriorityInheritance.blockingServer
              rw [hT]; simp [TCB.blockingServer?, hB]
            · rw [hTd, hT2, Option.getD_some]
              rw [← hTd]
              exact cancelDonationArmOnCore_eq_bindingState (by rw [hTd]; exact hT2)
                (.inl (by rw [hO2]; exact hO))
    obtain ⟨hC, hBS, hD⟩ := hMid
    unfold suspendThreadOnCore suspendPerform
    simp only [hT, hI, Bool.false_eq_true, ↓reduceIte, hC, hBS,
      currentDeboostedFrom_eq_code st]
    rw [suspendDonationArm_eq_cancelDonationArmOnCore, hD]
    exact suspendRescheduleOnCore_eq_state _ _ _ _ _

end Lifecycle.Suspend

end SeLe4n.Kernel
