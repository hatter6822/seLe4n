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

/-- **A context's notification link rewritten is a run-queue stage**: no view
the stage reads reads the link. -/
theorem notificationCodeWrite_runQueueStage {st : SystemState} {s : SeLe4n.SchedContextId}
    {sc : SchedContext} (hS : st.getSchedContext? s = some sc) (c : Nat) :
    RunQueueStage st (st.updateSchedContext s (fun sc => { sc with notificationCode := c })) := by
  have hSraw := (SystemState.getSchedContext?_eq_some_iff st s sc).mp hS
  have hU := SystemState.updateSchedContext_scheduler st s
    (fun sc => { sc with notificationCode := c })
  have hM := SystemState.updateSchedContext_machine st s
    (fun sc => { sc with notificationCode := c })
  exact RunQueueStage.insert (k := s.toObjId)
    (obj := .schedContext { sc with notificationCode := c })
    (congrArg SystemState.objects (SystemState.updateSchedContext_eq_of_some hS _))
    (by rw [hU]) (by rw [hU]) (fun c => by rw [hSraw]; rfl)
    (objStateMono_nonTcb (by rw [hSraw]; rfl) rfl) (by rw [hU])
    (fun c => by rw [hSraw]; rfl) (by rw [hSraw]; rfl) (by rw [hSraw]; rfl) (by rw [hU])
    (by rw [hM])

/-- **A notification's scheduling-context link rewritten is a run-queue stage**. -/
theorem notificationLinkInsert_runQueueStage {st : SystemState} {n : SeLe4n.ObjId}
    {ntfn : Notification} (h1 : st.objects[n]? = some (.notification ntfn)) (c : Nat) :
    RunQueueStage st
      { st with objects := st.objects.insert n (.notification { ntfn with schedContextCode := c }) } :=
  RunQueueStage.insert (k := n) (obj := .notification { ntfn with schedContextCode := c })
    rfl rfl rfl (fun c => by rw [h1]; rfl) (objStateMono_nonTcb (by rw [h1]; rfl) rfl) rfl
    (fun c => by rw [h1]; rfl) (by rw [h1]; rfl) (by rw [h1]; rfl) rfl rfl

/-- **The bind is a run-queue stage**: two one-object writes, each giving every
view the run-queue stage reads the value the replaced object gave. -/
theorem bindNotificationSchedLink_runQueueStage {st : SystemState}
    {s : SeLe4n.SchedContextId} {n : SeLe4n.ObjId} {sc : SchedContext} {ntfn : Notification}
    (hS : st.getSchedContext? s = some sc) (hN : st.getNotification? n = some ntfn) :
    RunQueueStage st (bindNotificationSchedLink st s n) := by
  refine RunQueueStage.of_invExt fun hInv => ?_
  obtain ⟨h1, hEq⟩ := bindNotificationSchedLink_eq hS hN hInv
  rw [hEq]
  exact (notificationCodeWrite_runQueueStage hS _).trans (notificationLinkInsert_runQueueStage h1 _)

/-- **The notification unbind read from the context's end is a run-queue
stage.** -/
theorem unbindSchedContextNotification_runQueueStage (st : SystemState)
    (s : SeLe4n.SchedContextId) : RunQueueStage st (unbindSchedContextNotification st s) := by
  refine RunQueueStage.of_invExt fun hInv => ?_
  rcases unbindSchedContextNotification_shape st s hInv with h | ⟨sc, hS, h | ⟨n, ntfn, h1, h⟩⟩
  · rw [h]; exact .refl st
  · rw [h]; exact notificationCodeWrite_runQueueStage hS 0
  · rw [h]; exact (notificationCodeWrite_runQueueStage hS 0).trans (notificationLinkInsert_runQueueStage h1 0)

theorem schedContextBindNotification_runQueueStage {vScId : SeLe4n.ValidObjId}
    {n : SeLe4n.ObjId} {st st' : SystemState}
    (h : schedContextBindNotification vScId n st = .ok ((), st')) : RunQueueStage st st' := by
  obtain ⟨hA, rfl⟩ := schedContextBindNotification_ok_admitted h
  obtain ⟨_, _, hS, -, hN, -⟩ := schedContextBindNotificationAdmitted_facts hA
  exact bindNotificationSchedLink_runQueueStage hS hN



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
the notification unbind's stage. -/
theorem schedContextUnbindAllOnCore_runQueueEntryStage {vScId : SeLe4n.ValidObjId}
    {ec : Concurrency.CoreId} {st st' : SystemState}
    {sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (h : SchedContextOps.schedContextUnbindAllOnCore vScId ec st = .ok (st', sgi)) :
    SystemState.RunQueueEntryStage st st' := by
  obtain ⟨stU, hU | ⟨-, hU, -⟩, rfl⟩ := SchedContextOps.schedContextUnbindAllOnCore_ok h
  · obtain ⟨rfl, -⟩ := hU
    exact (unbindSchedContextNotification_runQueueStage _ _).entry
  · exact (schedContextUnbindOnCore_runQueueEntryStage hU).trans
      (unbindSchedContextNotification_runQueueStage _ _).entry

/-- **`SchedContext_Unbind` blocks no thread.** -/
theorem schedContextUnbindAllOnCore_readyKeptStage {S : SeLe4n.ThreadId → Prop}
    {vScId : SeLe4n.ValidObjId} {ec : Concurrency.CoreId} {st st' : SystemState}
    {sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)} (hD : st.currentDequeuedUnique)
    (h : SchedContextOps.schedContextUnbindAllOnCore vScId ec st = .ok (st', sgi)) :
    readyKeptStage S st st' := by
  obtain ⟨stU, hU | ⟨-, -, hU⟩, rfl⟩ := SchedContextOps.schedContextUnbindAllOnCore_ok h
  · obtain ⟨rfl, -⟩ := hU
    exact .of_stage (unbindSchedContextNotification_runQueueStage _ _)
  · have A := SchedContextOps.schedContextUnbind_runQueueStage_of_dequeued vScId st stU hD hU
    exact (readyKeptStage.of_stage A).trans A.1
      (.of_stage (unbindSchedContextNotification_runQueueStage _ _))

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

end SeLe4n.Kernel
