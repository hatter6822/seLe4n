-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Cancel
import SeLe4n.Kernel.ContextLenders.Notification
import SeLe4n.Kernel.ContextLenders.Interrupt

/-! # The receive's own writes keep the lenders' flow

WS-SX SX8.  seL4-MCS `receiveIPC` and `completeSignal` around the rendezvous:
the busy reply's holder cancelled (`LendersFrame.cancelReplyHolder`), the bound
notification's wait, the context returned before the receive
(`schedContextReturnPerform`: the context's thread link and the thread's
binding cleared, the context off its release queue) and the donation to the
receiver.  None pushes a frame: the return and the donation keep every
context's head, the wait writes a notification and thread records. -/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace chainObjectsKept

/-- **seL4 `receiveSignal`**: the notification and the waiter's records. -/
theorem notificationWaitOnCore (nid : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (c : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) :
    chainObjectsKept st (_root_.SeLe4n.Kernel.notificationWaitOnCore nid waiter c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationWaitOnCore
  split
  · rename_i ntfn hN
    have hNO := (SystemState.getNotification?_eq_some_iff _ _ _).mp hN
    split
    · dsimp only
      split
      · exact refl _
      · rename_i st1 hS
        have K1 := storeObject_other hInv hS (fun _ e => by cases e) (fun _ e => by cases e)
          (.ofNotification hNO (.inr rfl))
        have I1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS
        split
        · exact refl _
        · rename_i st2 hT
          exact K1.trans (modifyTcb I1 hT)
    · split
      · exact refl _
      · rename_i tcb hTcb
        have hTO := lookupTcb_some_objects _ _ _ hTcb
        split
        · exact refl _
        · dsimp only
          split
          · exact refl _
          · rename_i st1 hS
            have K1 := storeObject_other hInv hS (fun _ e => by cases e) (fun _ e => by cases e)
              (.ofNotification hNO (.inr rfl))
            have hT1 : st1.objects[waiter.toObjId]? = some (.tcb tcb) := by
              rw [storeObject_objects_ne st st1 _ _ _ (fun e => by rw [e] at hTO; rw [hTO] at hNO; cases hNO)
                hInv hS]; exact hTO
            have I1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS
            split
            · exact refl _
            · rename_i st2 hT
              unfold storeTcbIpcStateAndMessage_fromTcb at hT
              revert hT
              cases hSt : storeObject waiter.toObjId _ st1 with
              | error _ => intro h; cases h
              | ok p =>
                obtain ⟨⟨⟩, s⟩ := p
                intro h
                have he := Except.ok.inj h
                subst he
                have K2 := storeObject_other I1 hSt (fun _ e => by cases e) (fun _ e => by cases e)
                  (.ofTcb hT1 (.inr ⟨rfl, rfl⟩))
                have I2 := storeObject_preserves_objects_invExt _ _ _ _ I1 hSt
                split
                · exact refl _
                · rename_i st4 hLink
                  have I3 := (RecordsFrame.linkNtfnWaiter I2 hLink).invExt
                  have K3 : chainObjectsKept s st4 := by
                    unfold linkNtfnWaiter at hLink
                    split at hLink
                    · cases hLink
                    · rename_i s3 hL3
                      have K := modifyTcb I2 hL3
                      have I := modifyTcb_preserves_objects_invExt I2 hL3
                      unfold relinkNtfnNext modifyTcbOpt at hLink
                      split at hLink
                      · cases hLink; exact K
                      · exact K.trans (modifyTcb I hLink)
                  exact ((K1.trans K2).trans K3).trans (removeRunnableOnCore _ waiter c)
  · split <;> exact refl _

end chainObjectsKept

namespace LendersFrame

theorem notificationWaitCrossCoreDispatchChecked (ctx : LabelingContext) (nid : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (c : CoreId) (st : SystemState) (hInv : st.objects.invExt)
    (hW : NotParkedAt st waiter) :
    LendersFrame st
      (_root_.SeLe4n.Kernel.notificationWaitCrossCoreDispatchChecked ctx nid waiter c st).1 := by
  refine ⟨?_, (RecordsStep.notificationWaitCrossCoreDispatchChecked hInv hW).invExt⟩
  unfold _root_.SeLe4n.Kernel.notificationWaitCrossCoreDispatchChecked
  split
  · split
    · exact .refl _
    · exact (chainObjectsKept.notificationWaitOnCore nid waiter c st hInv).linksShrink
  · exact .refl _

theorem writeReturnFrameToTcb (st : SystemState) (t : SeLe4n.ThreadId)
    (f : Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    LendersFrame st (Architecture.writeReturnFrameToTcb st t f) :=
  of_kept (chainObjectsKept.writeReturnFrameToTcb st t f hInv)
    (RecordsFrame.writeReturnFrameToTcb st t f hInv)

end LendersFrame

namespace LendersStep

variable {ctx : LabelingContext}

/-- **seL4's return of a context**: its thread link and the thread's binding
cleared in place, then the reschedule flags; the context keeps its head. -/
theorem schedContextReturnLinks (st : SystemState) (vS : SeLe4n.ValidObjId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    LendersStep ctx st (SeLe4n.Kernel.schedContextReturnLinks st vS tid) := by
  have hU : ∀ S : SystemState, S.objects.invExt → LendersStep ctx S
      (S.updateTcb tid fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 }) :=
    fun S h => updateTcb_grow S tid _ h (fun _ _ _ hs => by simp at hs)
      (fun _ _ _ _ hs _ => by simp at hs)
  have hM : ∀ (S : SystemState) (c : CoreId), S.objects.invExt →
      LendersStep ctx S (S.markReschedulePendingOnCore c) := fun S c h =>
    of_frame (LendersFrame.of_kept (chainObjectsKept.of_objects_eq rfl)
      (RecordsFrame.markReschedulePendingOnCore S c h))
  unfold SeLe4n.Kernel.schedContextReturnLinks
  split
  · exact refl hInv
  rename_i sc hSc _
  split
  · exact refl hInv
  dsimp only
  refine LendersStep.andThen ?_ fun h => of_frame (LendersFrame.markKeyChangeFor _ _ _ h)
  refine LendersStep.andThen ?_ fun h => of_frame (LendersFrame.of_kept
    (chainObjectsKept.of_objects_eq (markCandidacyGainFor_objects _ _ _))
    (RecordsFrame.markCandidacyGainFor _ _ _ h))
  split
  · exact ((rewriteObject_schedContext_grow hSc { sc with boundThreadCode := 0 } rfl _ hInv
      (fun _ ht => by simp at ht)).andThen fun h => hU _ h).andThen fun h => hM _ _ h
  · exact (rewriteObject_schedContext_grow hSc { sc with boundThreadCode := 0 } rfl _ hInv
      (fun _ ht => by simp at ht)).andThen fun h => hU _ h

theorem schedContextReturnPerform (st : SystemState) (vS : SeLe4n.ValidObjId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    LendersStep ctx st (SeLe4n.Kernel.schedContextReturnPerform st vS tid) :=
  (schedContextReturnLinks st vS tid hInv).andThen fun h =>
    of_frame (LendersFrame.of_views (contextStackViewsAgree_of_objectsAgreeOffReleaseLinks
      (SchedContextOps.purgeReplenishment_agree _ _))
      (SchedContextOps.purgeReplenishment_objects_invExt _ _ h))

theorem maybeReturnSchedContext (st : SystemState) (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : LendersStep ctx st (SeLe4n.Kernel.maybeReturnSchedContext st n t) :=
  maybeReturnSchedContext_induct (fun a b => LendersStep ctx a b) st n t (refl hInv)
    (fun vS _ _ _ => schedContextReturnPerform st vS t hInv)

theorem receiveReturnSchedContext (blocks : Bool) (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    LendersStep ctx st (SeLe4n.Kernel.receiveReturnSchedContext blocks st t) :=
  receiveReturnSchedContext_induct (fun a b => LendersStep ctx a b) blocks st t (refl hInv)
    (fun vS _ _ _ => schedContextReturnPerform st vS t hInv)

/-- **A receive that completes its bound notification** (seL4-MCS
`completeSignal`): the checked wait, then the badge written and the checked
donation (its check is its label equation), or the context returned. -/
theorem completeSignalArm {tid : SeLe4n.ThreadId} {nid : SeLe4n.ObjId}
    {c : CoreId} {st st' : SystemState} (hInv : st.objects.invExt) (hW : NotParkedAt st tid)
    (h : SeLe4n.Kernel.completeSignalArm ctx tid nid c st = .ok ((), st')) : LendersStep ctx st st' := by
  have W := LendersFrame.notificationWaitCrossCoreDispatchChecked ctx nid tid c st hInv hW
  unfold SeLe4n.Kernel.completeSignalArm at h
  split at h
  · rename_i hR
    cases h
    rw [hR] at W
    exact (of_frame (W.andThen fun h => LendersFrame.writeReturnFrameToTcb _ _ _ h)).andThen
      fun h => maybeDonateSchedContextFlowing _ nid tid h
  · rename_i hR
    cases h
    rw [hR] at W
    exact (of_frame W).andThen fun h => maybeReturnSchedContext _ nid tid h
  · cases h

end LendersStep

end SeLe4n.Kernel
