-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.NotificationLink
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation

/-!
# A context's notification binding keeps the IPC bundle

`schedContextBindNotification` writes the context's `notificationCode` and the
notification's `schedContextCode` (`bindNotificationSchedLink_eq`).  The IPC
bundle reads a notification's state, waiters, badge and binding codes and a
context's bound thread alone, so neither word moves it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **A notification's scheduling-context link rewritten keeps the IPC bundle**:
the bundle reads a notification's state, waiters and badge, and its binding
codes, none of them the link. -/
theorem insertObjects_notificationSchedLink_preserves_ipcInvariantFull
    (st : SystemState) (n : SeLe4n.ObjId) (ntfn : Notification) (code : Nat)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[n]? = some (.notification ntfn)) :
    ipcInvariantFull
      { st with objects := st.objects.insert n (.notification { ntfn with schedContextCode := code }) } := by
  have hAt := insertObjects_getElem_self st n
    (.notification { ntfn with schedContextCode := code }) hObjInv
  have hNe : ∀ oid : SeLe4n.ObjId, oid ≠ n →
      ({ st with objects := st.objects.insert n (.notification { ntfn with schedContextCode := code }) }
        : SystemState).objects[oid]? = st.objects[oid]? :=
    fun oid h => insertObjects_getElem_ne st n _ oid h hObjInv
  have hView := ipcReadViewAgreement.of_notification_content_write hPre hAt hNe rfl rfl rfl
  have hCodes := sameNotificationBindings.of_single_write hNe (by rw [hAt, hPre]; rfl)
  have hCap : capabilityBadgesWellFormed
      { st with objects := st.objects.insert n (.notification { ntfn with schedContextCode := code }) } := by
    intro oid cn slot cap badge hCn hLk hB
    by_cases hK : oid = n
    · rw [hK, hAt] at hCn
      cases Option.some.inj hCn; simp [KernelObject.slotCap] at hLk
    · rw [hNe _ hK] at hCn
      exact hInv.badgeWellFormed.2 oid cn slot cap badge hCn hLk hB
  exact ipcInvariantFull_of_readViewAgreement hView hCodes hCap hInv

/-- **The bind keeps the IPC bundle**: the context keeps its bound thread and the
notification its read view and binding codes. -/
theorem schedContextBindNotification_preserves_ipcInvariantFull (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (n : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : schedContextBindNotification vScId n st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨hA, rfl⟩ := schedContextBindNotification_ok_admitted hStep
  obtain ⟨_, ntfn, hS, -, hN, -⟩ := schedContextBindNotificationAdmitted_facts hA
  obtain ⟨h1, hEq⟩ := bindNotificationSchedLink_eq hS hN hObjInv
  rw [hEq]
  exact insertObjects_notificationSchedLink_preserves_ipcInvariantFull _ n ntfn _
    (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hObjInv)
    (updateSchedContext_boundKept_preserves_ipcInvariantFull _ _ _ hObjInv hInv (fun _ => rfl)) h1

/-- **The notification unbind read from the context's end keeps the IPC
bundle**: the context keeps its bound thread and the notification its read view
and binding codes. -/
theorem unbindSchedContextNotification_preserves_ipcInvariantFull (st : SystemState)
    (s : SeLe4n.SchedContextId) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (unbindSchedContextNotification st s) := by
  have hSc := updateSchedContext_boundKept_preserves_ipcInvariantFull st s
    (fun c => { c with notificationCode := 0 }) hObjInv hInv (fun _ => rfl)
  rcases unbindSchedContextNotification_shape st s hObjInv with h | ⟨sc, hS, h | ⟨n, ntfn, h1, h⟩⟩
  · rw [h]; exact hInv
  · rw [h]; exact hSc
  · rw [h]
    exact insertObjects_notificationSchedLink_preserves_ipcInvariantFull _ n ntfn 0
      (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hObjInv) hSc h1

/-- **`SchedContext_Unbind` keeps the IPC bundle**: the thread unbind (the
current thread's context is refused, so the per-core form's seam writes nothing
and the step is the single-core unbind), then the notification unbind. -/
theorem schedContextUnbindAllOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (vScId : SeLe4n.ValidObjId) (ec : Concurrency.CoreId)
    (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) (hR : st.runQueueRefined)
    (hStep : SchedContextOps.schedContextUnbindAllOnCore vScId ec st = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  obtain ⟨stU, hU | ⟨-, -, hU⟩, rfl⟩ := SchedContextOps.schedContextUnbindAllOnCore_ok hStep
  · obtain ⟨rfl, -⟩ := hU
    exact unbindSchedContextNotification_preserves_ipcInvariantFull _ _ hObjInv hInv
  · exact unbindSchedContextNotification_preserves_ipcInvariantFull _ _
      ((SchedContextOps.schedContextUnbind_runQueueEntryStage vScId st stU hU).1 hObjInv hR).1
      (schedContextUnbind_preserves_ipcInvariantFull st stU vScId hObjInv hInv hU)

/-- **`SchedContext_UnbindObject` on a thread preserves `ipcInvariantFull`**:
it is the per-core thread unbind, whose seam writes nothing on a context the
executing core does not run, so the step is the single-core unbind. -/
theorem schedContextUnbindThreadObjectOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (vScId : SeLe4n.ValidObjId) (tid : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : SchedContextOps.schedContextUnbindThreadObjectOnCore vScId tid ec st = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  obtain ⟨-, hU, -⟩ := SchedContextOps.schedContextUnbindOnCore_ok
    (SchedContextOps.schedContextUnbindThreadObjectOnCore_ok hStep)
  exact schedContextUnbind_preserves_ipcInvariantFull st st' vScId hObjInv hInv hU

/-- **`SchedContext_UnbindObject` on a notification preserves
`ipcInvariantFull`**: it is the notification unbind. -/
theorem schedContextUnbindNotificationObject_preserves_ipcInvariantFull
    (st st' : SystemState) (vScId : SeLe4n.ValidObjId) (n : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : SchedContextOps.schedContextUnbindNotificationObject vScId n st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨-, rfl⟩ := SchedContextOps.schedContextUnbindNotificationObject_ok hStep
  exact unbindSchedContextNotification_preserves_ipcInvariantFull _ _ hObjInv hInv

end SeLe4n.Kernel
