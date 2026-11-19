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

/-- **The bind is a run-queue stage**: two one-object writes, each giving every
view the run-queue stage reads the value the replaced object gave. -/
theorem bindNotificationSchedLink_runQueueStage {st : SystemState}
    {s : SeLe4n.SchedContextId} {n : SeLe4n.ObjId} {sc : SchedContext} {ntfn : Notification}
    (hS : st.getSchedContext? s = some sc) (hN : st.getNotification? n = some ntfn) :
    RunQueueStage st (bindNotificationSchedLink st s n) := by
  refine RunQueueStage.of_invExt fun hInv => ?_
  obtain ⟨h1, hEq⟩ := bindNotificationSchedLink_eq hS hN hInv
  have hSraw := (SystemState.getSchedContext?_eq_some_iff st s sc).mp hS
  have hU := SystemState.updateSchedContext_scheduler st s
    (fun sc => { sc with notificationCode := n.val + 1 })
  have hM := SystemState.updateSchedContext_machine st s
    (fun sc => { sc with notificationCode := n.val + 1 })
  rw [hEq]
  refine (RunQueueStage.insert (k := s.toObjId)
    (obj := .schedContext { sc with notificationCode := n.val + 1 })
    (congrArg SystemState.objects (SystemState.updateSchedContext_eq_of_some hS _))
    (by rw [hU]) (by rw [hU]) (fun c => by rw [hSraw]; rfl)
    (objStateMono_nonTcb (by rw [hSraw]; rfl) rfl) (by rw [hU])
    (fun c => by rw [hSraw]; rfl) (by rw [hSraw]; rfl) (by rw [hSraw]; rfl) (by rw [hU])
    (by rw [hM])).trans ?_
  exact RunQueueStage.insert (k := n) (obj := .notification { ntfn with schedContextCode := s.val + 1 })
    rfl rfl rfl (fun c => by rw [h1]; rfl) (objStateMono_nonTcb (by rw [h1]; rfl) rfl) rfl
    (fun c => by rw [h1]; rfl) (by rw [h1]; rfl) (by rw [h1]; rfl) rfl rfl

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

end SeLe4n.Kernel
