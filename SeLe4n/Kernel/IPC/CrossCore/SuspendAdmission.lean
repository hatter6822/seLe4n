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
thread's IPC, takes it off the scheduler and its context off the release queues,
marks it `Inactive` and cancels its yield link.  The specification here
(`Lifecycle.Suspend.suspendThreadOnCore`) is that, and is total after its two
checks (WS-ZA ZA6.33, `suspendThreadOnCore_total`).

This module asks, on the state the suspend is handed and before anything is
written, which arms run in place (`suspendAdmitted`): a thread blocked on no IPC,
or on a notification whose slot is found in place.  When it answers `true` the
suspend's state is `suspendPerform`, every write in its slot
(`suspendThreadOnCore_of_admitted`), so the syscall entry hands the state to the
writes alone (`RefusalCarrying.ofChecked`) and keeps no copy of it; any other
arm runs the specification.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  The suspend's checks and its writes
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

/-- **The checks `.tcbSuspend` makes, asked before any write** (seL4's
`decodeTCBInvocation` then `suspend`, which never fails): the target is a
thread not already `.Inactive`, and

* it is blocked on no IPC (`ready`, no object): nothing is torn down; or
* it is blocked on a notification the store holds, its slot found in place, so
  the cancel's writes land in place and are the specification's
  (`cancelIpcBlocking_notification_inPlace`).

WS-ZA ZA6.33: seL4's `suspend` neither unbinds the thread's context nor returns
a loan it holds, so nothing about its binding is asked.  When the checks pass
the suspend's state is `suspendPerform` (`suspendThreadOnCore_of_admitted`). -/
@[inline] def suspendAdmitted (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? tid with
  | some tcb =>
    !(tcb.threadState == .Inactive) &&
      match tcb.ipcStateCode with
      | 0 => tcb.ipcObjectCode == 0
      | 2 =>
        st.objects.findsInPlace tid.toObjId &&
          (st.getNotification? ⟨tcb.ipcObjectCode⟩).isSome
      | _ => false
  | none => false

/-- **The admitted suspend** (seL4's `suspend`): the placement, the core
running the thread and the executing core's current priority read before
anything is written; then the IPC teardown (`suspendTeardownState`), the
thread's removal from where the state places it, its pending state cleared,
`.Inactive`, its context off the release queues (`releaseRemoveThread`, seL4's
`tcbReleaseRemove`), its yield link cancelled and the local scheduling point.
The state is handed to the writes alone. -/
def suspendPerform (st : SystemState) (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId) :
    SystemState :=
  let tid := vtid.val
  let placed := placedCoreOf? st tid
  let runningCore? := runningCoreOf? st tid
  let curCode := st.scheduler.currentCode.get executingCore
  let prioCode := currentEffectivePrioCode st executingCore
  let st0 := suspendTeardownState st tid
  let st1 := descheduleAt st0 tid placed
  let st2 := clearPendingStateValid st1 vtid
  let st3 := st2.updateTcb tid fun t => { t with threadState := .Inactive }
  let st3a := releaseRemoveThread st3 tid
  let st4 := cancelYieldTo st3a tid
  suspendRescheduleState st4 (runningCore?.getD executingCore) executingCore
    runningCore?.isSome (currentDeboostedFromCode st4 executingCore curCode prioCode)

/-- **Every check `suspendThreadOnCore` makes is `suspendAdmitted`'s, and when
it passes the suspend commits as `suspendPerform`.**  The ready arm tears
nothing down; the notification arm's teardown is the in-place cancel; neither
thread waits on a server, so there is no chain to revert. -/
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
    have hMid : cancelIpcKeepingContexts st vtid.val tcb = suspendTeardownState st vtid.val ∧
        PriorityInheritance.blockingServer st vtid.val = none := by
      cases hc : tcb.ipcStateCode with
      | zero =>
        rw [hc] at hArm
        simp only [beq_iff_eq] at hArm
        have hReady : tcb.ipcState = .ready := by
          simp only [TCB.ipcState, hArm, hc]; rfl
        have hTd : suspendTeardownState st vtid.val = st := by
          unfold suspendTeardownState; rw [hT]; simp only [hc]
        rw [hTd]
        refine ⟨?_, ?_⟩
        · rw [cancelIpcKeepingContexts_of_not_reply _ _ _ (by rw [hReady]; intro _ _ h; cases h)]
          unfold cancelIpcBlocking; rw [hReady]
        · unfold PriorityInheritance.blockingServer
          rw [hT]; simp [TCB.blockingServer?, hReady]
      | succ k =>
        cases k with
        | zero => rw [hc] at hArm; cases hArm
        | succ k =>
          cases k with
          | succ k => rw [hc] at hArm; cases hArm
          | zero =>
            rw [hc] at hArm
            simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hArm
            obtain ⟨_, ntfn, hN⟩ := hArm
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
            refine ⟨?_, ?_⟩
            · rw [cancelIpcKeepingContexts_of_not_reply _ _ _ (by rw [hB]; intro _ _ h; cases h),
                hTd]
              exact cancelIpcBlocking_notification_inPlace hN hT hB
            · unfold PriorityInheritance.blockingServer
              rw [hT]; simp [TCB.blockingServer?, hB]
    obtain ⟨hC, hBS⟩ := hMid
    unfold suspendThreadOnCore suspendPerform
    simp only [hT, hI, Bool.false_eq_true, ↓reduceIte, hC, hBS,
      currentDeboostedFrom_eq_code st]
    exact suspendRescheduleOnCore_eq_state _ _ _ _ _

end Lifecycle.Suspend

end SeLe4n.Kernel
