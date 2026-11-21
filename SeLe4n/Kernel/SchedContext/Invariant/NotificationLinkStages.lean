-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.NotificationLink
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Scheduling

/-!
# A context's notification binding keeps the kernel's stage invariants

`schedContextBindNotification` writes two link words, the context's
`notificationCode` and the notification's `schedContextCode`, in the two
objects' own slots (`bindNotificationSchedLink_eq`).  No run-queue, release,
refill or yield view reads either word, no mapping fact or record view does, and
the IPC bundle reads a notification's state, waiters and badge and a context's
bound thread alone — so the bind is a run-queue stage; it writes a context's
slot and a notification's alone (`schedContextBindNotification_slots`), which the
mapping, record, scheduling-key and saved-register frames read in their own
families, and its IPC-bundle half is `NotificationLinkIpc`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage objStateMono_nonTcb)

/-- **The bind is a run-queue stage**: two link words written, a context bound
to no notification and a notification bound to no context linked together
(`bindNotificationSchedLink_preserves_notificationLinksAgree`). -/
theorem bindNotificationSchedLink_runQueueStage {st : SystemState}
    {s : SeLe4n.SchedContextId} {n : SeLe4n.ObjId} {sc : SchedContext} {ntfn : Notification}
    (hS : st.getSchedContext? s = some sc) (hS0 : sc.notificationCode = 0)
    (hN : st.getNotification? n = some ntfn) (hN0 : ntfn.schedContextCode = 0) :
    RunQueueStage st (bindNotificationSchedLink st s n) := by
  have hI1 : st.objects.invExt → (st.updateSchedContext s
      (fun sc => { sc with notificationCode := n.val + 1 })).objects.invExt := fun hInv =>
    SystemState.updateSchedContext_preserves_objects_invExt st s _ hInv
  refine runQueueStage_of_objectsAgreeOffNotificationLinks (fun hInv => ?_) (fun hInv => ?_)
    (fun hInv => ?_) (fun hInv => ?_)
    (fun hInv => bindNotificationSchedLink_preserves_notificationLinksAgree st s n hInv hS hS0 hN hN0)
  all_goals obtain ⟨h1, hEq⟩ := bindNotificationSchedLink_eq hS hN hInv
  · rw [hEq]
    exact (objectsAgreeOffNotificationLinks.notificationLinkInsert h1 _ (hI1 hInv)).trans
      (.notificationCodeWrite hS _ hInv)
  · rw [hEq]; exact SystemState.updateSchedContext_scheduler st s _
  · rw [hEq]; exact SystemState.updateSchedContext_machine st s _
  · rw [hEq]; exact RHTable_insert_preserves_invExt _ _ _ (hI1 hInv)

theorem schedContextBindNotification_runQueueStage {vScId : SeLe4n.ValidObjId}
    {n : SeLe4n.ObjId} {st st' : SystemState}
    (h : schedContextBindNotification vScId n st = .ok ((), st')) : RunQueueStage st st' := by
  obtain ⟨hA, rfl⟩ := schedContextBindNotification_ok_admitted h
  obtain ⟨_, _, hS, hS0, hN, hN0⟩ := schedContextBindNotificationAdmitted_facts hA
  exact bindNotificationSchedLink_runQueueStage hS hS0 hN hN0



/-- **The bind writes a context's slot and a notification's slot alone**: every
other slot is as it was, and neither written slot is or becomes a thread. -/
theorem schedContextBindNotification_slots {vScId : SeLe4n.ValidObjId}
    {n : SeLe4n.ObjId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : schedContextBindNotification vScId n st = .ok ((), st')) :
    ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
      ((∀ x : TCB, st.objects[oid]? ≠ some (.tcb x)) ∧
        (∀ x : TCB, st'.objects[oid]? ≠ some (.tcb x))) := by
  obtain ⟨hA, rfl⟩ := schedContextBindNotification_ok_admitted h
  obtain ⟨sc, ntfn, hS, -, hN, -⟩ := schedContextBindNotificationAdmitted_facts hA
  obtain ⟨h1, hEq⟩ := bindNotificationSchedLink_eq hS hN hInv
  have hSraw := (SystemState.getSchedContext?_eq_some_iff st _ sc).mp hS
  have hNraw := (SystemState.getNotification?_eq_some_iff st n ntfn).mp hN
  have hI1 := SystemState.updateSchedContext_preserves_objects_invExt st
    (SeLe4n.SchedContextId.ofObjId vScId.val) (fun sc => { sc with notificationCode := n.val + 1 }) hInv
  intro oid
  rw [hEq]
  by_cases hn : oid = n
  · subst hn
    right
    refine ⟨fun x e => (by rw [hNraw] at e; cases e), fun x e => ?_⟩
    rw [insertObjects_getElem_self _ _ _ hI1] at e; cases e
  · rw [insertObjects_getElem_ne _ _ _ _ hn hI1]
    by_cases hs : (SeLe4n.SchedContextId.ofObjId vScId.val).toObjId = oid
    · subst hs
      right
      refine ⟨fun x e => (by rw [hSraw] at e; cases e), fun x e => ?_⟩
      rw [SystemState.updateSchedContext_eq_of_some hS] at e
      rw [insertObjects_getElem_self _ _ _ hInv] at e; cases e
    · left; exact SystemState.updateSchedContext_objects_ne _ _ _ _ hs hInv

/-- **`SchedContext_Unbind` is a kernel-entry stage**: the thread unbind's, then
the notification unbind's and the reply-stack unlink's stages. -/
theorem schedContextUnbindAllOnCore_runQueueEntryStage {vScId : SeLe4n.ValidObjId}
    {ec : Concurrency.CoreId} {st st' : SystemState}
    {sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContextOps.schedContextUnbindAllOnCore vScId ec st = .ok (st', sgi)) :
    SystemState.RunQueueEntryStage st st' := by
  obtain ⟨stU, hU | ⟨-, hU, -⟩, rfl⟩ := SchedContextOps.schedContextUnbindAllOnCore_ok h
  · obtain ⟨rfl, -⟩ := hU
    exact ((unbindSchedContextNotification_runQueueStage _ _).trans
      (schedContextUnbindReply_runQueueStage _ _)).entry
  · exact (schedContextUnbindOnCore_runQueueEntryStage hU).trans
      ((unbindSchedContextNotification_runQueueStage _ _).trans
        (schedContextUnbindReply_runQueueStage _ _)).entry

/-- **`SchedContext_Unbind` blocks no thread.** -/
theorem schedContextUnbindAllOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop}
    {vScId : SeLe4n.ValidObjId} {ec : Concurrency.CoreId} {st st' : SystemState}
    {sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)} (hD : st.currentDequeuedUnique)
    (h : SchedContextOps.schedContextUnbindAllOnCore vScId ec st = .ok (st', sgi)) :
    readyKeptStage S st st' := by
  obtain ⟨stU, hU | ⟨-, -, hU⟩, rfl⟩ := SchedContextOps.schedContextUnbindAllOnCore_ok h
  · obtain ⟨rfl, -⟩ := hU
    exact .of_stage ((unbindSchedContextNotification_runQueueStage _ _).trans
      (schedContextUnbindReply_runQueueStage _ _))
  · have A := SchedContextOps.schedContextUnbind_runQueueStage_of_dequeued vScId st stU hD hU
    exact (readyKeptStage.of_stage A).trans A.1
      (.of_stage ((unbindSchedContextNotification_runQueueStage _ _).trans
        (schedContextUnbindReply_runQueueStage _ _)))

/-- **The notification unbind read from the context's end writes a context's
slot and a notification's alone**: every other slot is as it was, and neither
written slot is or becomes a thread. -/
theorem unbindSchedContextNotification_slots (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) :
    ∀ oid : SeLe4n.ObjId, (unbindSchedContextNotification st s).objects[oid]? = st.objects[oid]? ∨
      ((∀ x : TCB, st.objects[oid]? ≠ some (.tcb x)) ∧
        (∀ x : TCB, (unbindSchedContextNotification st s).objects[oid]? ≠ some (.tcb x))) := by
  intro oid
  have hI1 := SystemState.updateSchedContext_preserves_objects_invExt st s
    (fun c => { c with notificationCode := 0 }) hInv
  have hSc : ∀ sc, st.getSchedContext? s = some sc →
      (st.updateSchedContext s (fun c => { c with notificationCode := 0 })).objects[oid]? =
        st.objects[oid]? ∨
      ((∀ x : TCB, st.objects[oid]? ≠ some (.tcb x)) ∧
        (∀ x : TCB, (st.updateSchedContext s
          (fun c => { c with notificationCode := 0 })).objects[oid]? ≠ some (.tcb x))) := by
    intro sc hS
    have hSraw := (SystemState.getSchedContext?_eq_some_iff st s sc).mp hS
    by_cases hs : s.toObjId = oid
    · subst hs
      right
      refine ⟨fun x e => (by rw [hSraw] at e; cases e), fun x e => ?_⟩
      rw [SystemState.updateSchedContext_eq_of_some hS] at e
      rw [insertObjects_getElem_self _ _ _ hInv] at e; cases e
    · left; exact SystemState.updateSchedContext_objects_ne _ _ _ _ hs hInv
  rcases unbindSchedContextNotification_shape st s hInv with h | ⟨sc, hS, h | ⟨n, ntfn, h1, h⟩⟩
  · rw [h]; exact Or.inl rfl
  · rw [h]; exact hSc sc hS
  · rw [h]
    by_cases hn : oid = n
    · subst hn
      right
      rcases hSc sc hS with e0 | ⟨e0, -⟩
      · refine ⟨fun x e => (by rw [← e0, h1] at e; cases e), fun x e => ?_⟩
        rw [insertObjects_getElem_self _ _ _ hI1] at e; cases e
      · refine ⟨e0, fun x e => ?_⟩
        rw [insertObjects_getElem_self _ _ _ hI1] at e; cases e
    · rw [insertObjects_getElem_ne _ _ _ _ hn hI1]; exact hSc sc hS

/-- **A context's reply-stack unlink keeps the object store's extended
invariant.** -/
theorem schedContextUnbindReply_preserves_objects_invExt (st : SystemState) (x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) : (schedContextUnbindReply st x).objects.invExt :=
  schedContextUnbindReply_induct (fun _ b => b.objects.invExt) st x hInv
    (fun _ _ _ _ _ _ _ _ hS => SystemState.updateSchedContext_preserves_objects_invExt _ _ _
      (storeObject_preserves_objects_invExt _ _ _ _ hInv hS))

/-- **A context's reply-stack unlink writes a Reply's slot and a context's
alone**: every other slot is as it was, and neither written slot is or becomes a
thread. -/
theorem schedContextUnbindReply_slots (st : SystemState) (x : SeLe4n.ObjId)
    (hInv : st.objects.invExt) :
    ∀ oid : SeLe4n.ObjId, (schedContextUnbindReply st x).objects[oid]? = st.objects[oid]? ∨
      ((∀ y : TCB, st.objects[oid]? ≠ some (.tcb y)) ∧
        (∀ y : TCB, (schedContextUnbindReply st x).objects[oid]? ≠ some (.tcb y))) := by
  intro oid
  refine schedContextUnbindReply_induct (fun a b => b.objects[oid]? = a.objects[oid]? ∨
      ((∀ y : TCB, a.objects[oid]? ≠ some (.tcb y)) ∧
        (∀ y : TCB, b.objects[oid]? ≠ some (.tcb y)))) st x (Or.inl rfl) ?_
  intro _ rid r s1 _ _ hR _ hS
  have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS
  have hRraw := (SystemState.getReply?_eq_some_iff st rid r).mp hR
  -- the reply's slot
  have hStep1 : s1.objects[oid]? = st.objects[oid]? ∨
      ((∀ y : TCB, st.objects[oid]? ≠ some (.tcb y)) ∧
        (∀ y : TCB, s1.objects[oid]? ≠ some (.tcb y))) := by
    by_cases ho : oid = rid.toObjId
    · subst ho; right
      refine ⟨fun y e => (by rw [hRraw] at e; cases e), fun y e => ?_⟩
      rw [storeObject_objects_eq _ _ _ _ hInv hS] at e; cases e
    · left; exact storeObject_objects_ne _ _ _ _ _ ho hInv hS
  cases hG : s1.getSchedContext? ⟨x.val⟩ with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hG]; exact hStep1
  | some y =>
    have hGraw := (SystemState.getSchedContext?_eq_some_iff _ _ y).mp hG
    by_cases hs : (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = oid
    · subst hs; right
      refine ⟨fun z e => ?_, fun z e => ?_⟩
      · rcases hStep1 with e1 | ⟨e1, -⟩
        · rw [← e1, hGraw] at e; cases e
        · exact e1 z e
      · rw [SystemState.updateSchedContext_eq_of_some hG] at e
        rw [insertObjects_getElem_self _ _ _ hI1] at e; cases e
    · rw [SystemState.updateSchedContext_objects_ne _ _ _ _ hs hI1]; exact hStep1

end SeLe4n.Kernel
