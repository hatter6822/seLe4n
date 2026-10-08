-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SlotConfinement.Predicate
import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatch
import SeLe4n.Kernel.API
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.IPC.CrossCore.SuspendFootprint

/-!
# Per-core slot confinement — the primitives and the IPC legs

Each theorem here bounds one transition by a write set **computed from the
pre-state**, so a caller decides membership rather than being handed an
existential.  A write set is proved sound in the one direction that
matters (every core outside it is untouched), never tight: a transition
confined to fewer cores than declared is safe, and the wake paths collapse
to the empty set on the fail-closed arms.

* §1 — the per-core scheduler primitives (`enqueueRunnableOnCore`,
  `removeRunnableOnCore`, `wakeThread`, `descheduleThread`) and the
  scheduler-silent object-store steps, confined to `[]`.
* §2 — the notification signal and wait.
* §3 — the endpoint call (the two-core case: the receiver's home core and
  the caller's).
* §4 — the reply; §4a — the receive leg.
* §5 — the cancellation: `descheduleThread` and the composed
  `cancelIpcBlockingOnCore`.
* §5a — the priority-inheritance chain walk, and the union that bounds the
  live `.call` arm: the walk re-buckets on each boosted server's *home*
  core, so the below-API write sets do not bound the arm on their own.

The `*_determineTargetCore_eq` facts a write set needs to name a core at
the pre-state live beside their primitives in
`IPC/CrossCore/EndpointCall.lean`.  The live syscall arms are the sibling
modules; `SeLe4n.Kernel.SlotConfinement` imports them all.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Kernel.PriorityInheritance

-- §1 The per-core scheduler primitives
-- ============================================================================

/-- SM8.B.2: a bare run-queue write is confined to the core it names.

The structural helper the SchedContext proofs compose, rather than re-deriving
the six-field obligation inline each time — which is where a `simp_all` hid the
mid-state home-core problem in the first attempt. -/
theorem setRunQueueOnCore_confinedToCores (st : SystemState) (cc : CoreId)
    (q : SeLe4n.Kernel.RunQueue) :
    observableSlotsConfinedToCores st
      { st with scheduler := st.scheduler.setRunQueueOnCore cc q } [cc] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
    simp only [List.mem_singleton] at hc
  · exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ cc c q (fun h => hc h.symm)
  · exact SchedulerState.setRunQueueOnCore_currentOnCore _ cc c q
  · exact SchedulerState.setRunQueueOnCore_activeDomainOnCore _ cc c q
  · exact SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore _ cc c q
  · exact SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore _ cc c q
  · rfl

/-- SM8.B.2: a **replenish**-queue write is confined to no core at all — the
replenish queue is outside the six observable slots, so it is per-core silent
even on the core it names. -/
theorem setReplenishQueueOnCore_confinedToCores (st : SystemState) (cc : CoreId)
    (q : SeLe4n.Kernel.ReplenishQueue) :
    observableSlotsConfinedToCores st
      { st with scheduler := st.scheduler.setReplenishQueueOnCore cc q } [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c _
  · exact SchedulerState.setReplenishQueueOnCore_runQueueOnCore _ cc c q
  · exact SchedulerState.setReplenishQueueOnCore_currentOnCore _ cc c q
  · exact SchedulerState.setReplenishQueueOnCore_activeDomainOnCore _ cc c q
  · exact SchedulerState.setReplenishQueueOnCore_domainTimeRemainingOnCore _ cc c q
  · exact SchedulerState.setReplenishQueueOnCore_domainScheduleIndexOnCore _ cc c q
  · rfl

/-- SM8.B.2 (PR #861 review round 17): a replenish-queue **purge** writes no
confined slot, at any core.

The named form of the lemma above, for the SchedContext operations' per-core
purges. The replenish queue is not one of the six confined slots, so the
purge's *target core* does not enter the write set — which is what lets the
round-17 fix reroute all three purge sites without widening any bound. -/
theorem purgeReplenishmentOnCore_confinedToCores (st : SystemState) (cc : CoreId)
    (scId : SeLe4n.SchedContextId) :
    observableSlotsConfinedToCores st
      (SchedContextOps.purgeReplenishmentOnCore st cc scId) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c _ <;> simp

/-- SM8.B.2: and so does the all-cores sweep — every fold step is the above. -/
theorem purgeReplenishmentFromAllCores_confinedToCores (st : SystemState)
    (scId : SeLe4n.SchedContextId) :
    observableSlotsConfinedToCores st
      (SchedContextOps.purgeReplenishmentFromAllCores st scId) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c _ <;> simp

/-- SM8.B.2: `enqueueRunnableOnCore` writes core `cc`'s run-queue slot and the
enqueued TCB, and nothing else per-core. -/
theorem enqueueRunnableOnCore_confinedToCores (st : SystemState) (cc : CoreId)
    (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (enqueueRunnableOnCore st cc tid) [cc] :=
  ⟨fun c hc => enqueueRunnableOnCore_runQueueOnCore_ne st cc c tid
      (fun h => hc (by simp [h])),
   fun c _ => enqueueRunnableOnCore_currentOnCore st cc tid c,
   fun c _ => enqueueRunnableOnCore_activeDomainOnCore st cc tid c,
   fun c _ => enqueueRunnableOnCore_domainTimeRemainingOnCore st cc tid c,
   fun c _ => enqueueRunnableOnCore_domainScheduleIndexOnCore st cc tid c,
   fun _ _ => by rw [enqueueRunnableOnCore_machineEq]⟩

/-- SM8.B.2: `removeRunnableOnCore` writes core `cc`'s run-queue and current
slots, and nothing else per-core. -/
theorem removeRunnableOnCore_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) (cc : CoreId) :
    observableSlotsConfinedToCores st (removeRunnableOnCore st tid cc) [cc] :=
  ⟨fun c hc => removeRunnableOnCore_runQueueOnCore_ne st tid cc c (fun h => hc (by simp [h])),
   fun c hc => removeRunnableOnCore_currentOnCore_ne st tid cc c (fun h => hc (by simp [h])),
   fun c _ => removeRunnableOnCore_activeDomainOnCore st tid cc c,
   fun c _ => removeRunnableOnCore_domainTimeRemainingOnCore st tid cc c,
   fun c _ => removeRunnableOnCore_domainScheduleIndexOnCore st tid cc c,
   fun _ _ => by rw [removeRunnableOnCore_machine_eq]⟩

/-- WS-RR RR8.6: a removal at a pre-resolved placement writes that core's
run-queue and current slots when there is one, and nothing per-core when the
placement is `none`. -/
theorem descheduleAt_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (placed : Option CoreId) :
    observableSlotsConfinedToCores st (descheduleAt st tid placed) placed.toList := by
  unfold descheduleAt
  cases placed with
  | none => exact observableSlotsConfinedToCores_refl st []
  | some c => exact removeRunnableOnCore_confinedToCores st tid c

/-- The state-resolved step's own confinement, stated once where every consumer
— the reply path's donation return, the cancellation composite, the live
suspend's write set — can reach it: the cores it may write are read off the
SAME resolver the step itself uses. -/
theorem descheduleAtPlacement_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (descheduleAtPlacement st tid)
      (descheduleAtPlacementCores st tid) := by
  rw [descheduleAtPlacementCores_eq_toList]
  exact descheduleAt_confinedToCores st tid (placedCoreOf? st tid)

/-- SM8.B.2: **the cross-core wake writes exactly the woken thread's home
core.** The write set is `[determineTargetCore st tid]` — read off the
pre-state, and *not* the executing core, which is the whole point of SM5.C: a
wake routes to the target's home core, so a signaller on core 0 waking a thread
homed on core 2 writes core 2's run queue and nothing of core 0's or core 1's. -/
theorem wakeThread_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    observableSlotsConfinedToCores st (wakeThread st tid executingCore).1
      [determineTargetCore st tid] := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_confinedToCores st (determineTargetCore st tid) tid

/-- SM8.B.2: the wake's dual — `descheduleThread` writes exactly the core the
state **places** the victim on (WS-RR RR8.6; its home core until then, which
an unpinned thread preempted off its home is not on). -/
theorem descheduleThread_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    observableSlotsConfinedToCores st (descheduleThread st tid executingCore).1
      (descheduleAtPlacementCores st tid) := by
  rw [descheduleThread_state_eq]
  exact descheduleAtPlacement_confinedToCores st tid

/-- SM8.B.2: a successful `storeObject` is per-core silent — it writes the
object store and neither the scheduler nor any register bank, so it is confined
to the **empty** core set. Every cross-core IPC pipeline below is a chain of
these plus one or two scheduler primitives. -/
theorem storeObject_confinedToCores (st st' : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (hStep : storeObject oid obj st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (storeObject_scheduler_eq st st' oid obj hStep)
    (storeObject_machine_eq st st' oid obj hStep)

theorem storeTcbIpcStateAndMessage_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (storeTcbIpcStateAndMessage_scheduler_eq st st' tid ipc msg hStep)
    (storeTcbIpcStateAndMessage_machine_eq st st' tid ipc msg hStep)

theorem storeTcbIpcState_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (storeTcbIpcState_scheduler_eq st st' tid ipc hStep)
    (storeTcbIpcState_machine_eq st st' tid ipc hStep)

theorem storeTcbIpcState_fromTcb_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState_fromTcb st tid tcb ipc = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  unfold storeTcbIpcState_fromTcb at hStep
  cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
  | error e => simp [hStore] at hStep
  | ok pair =>
    simp only [hStore] at hStep
    have hEq := Except.ok.inj hStep; subst hEq
    exact storeObject_confinedToCores st pair.2 _ _ hStore

theorem endpointQueuePopHead_confinedToCores (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) {headTcb : TCB}
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (endpointQueuePopHead_scheduler_eq endpointId isReceiveQ st st' tid hStep)
    (endpointQueuePopHead_machine_eq endpointId isReceiveQ st st' tid hStep)

theorem endpointQueueEnqueue_confinedToCores (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (endpointQueueEnqueue_scheduler_eq endpointId isReceiveQ tid st st' hStep)
    (endpointQueueEnqueue_machine_eq endpointId isReceiveQ tid st st' hStep)

theorem linkServerStashedReply_confinedToCores (caller server : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (linkServerStashedReply_scheduler_eq st st' caller server hStep)
    (linkServerStashedReply_machine_eq st st' caller server hStep)

theorem consumeCallerReply_confinedToCores (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (SystemState.consumeCallerReply_scheduler_eq st st' caller rid hStep)
    (SystemState.consumeCallerReply_machine_eq st st' caller rid hStep)

/-- **WS-RM (`v0.35.6`)**: the removal touches neither the scheduler nor the
machine — the splice writes only Reply objects and the consume two objects. -/
theorem removeCallerReplyFrame_confinedToCores (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (removeCallerReplyFrame_scheduler_eq st st' caller rid hStep)
    (removeCallerReplyFrame_machine_eq st st' caller rid hStep)

theorem linkCallerReply_confinedToCores (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (st st' : SystemState)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (linkCallerReply_scheduler_eq st st' caller rid hStep)
    (linkCallerReply_machine_eq st st' caller rid hStep)

theorem endpointQueueRemoveDual_confinedToCores (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (endpointQueueRemoveDual_scheduler_eq st st' endpointId isReceiveQ tid hStep)
    (endpointQueueRemoveDual_machine_eq st st' endpointId isReceiveQ tid hStep)

theorem storeTcbReceiveComplete_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (storeTcbReceiveComplete_scheduler_eq st st' tid msg hStep)
    (storeTcbReceiveComplete_machine_eq st st' tid msg hStep)

/-- SM8.B.2: a replenishment migration is per-core silent — it moves a
SchedContext's replenishments between two cores' **replenishment** queues, and
SM8.A's `onCore_perCore_independence` puts that queue outside the observer's
read set entirely. -/
theorem migrateSchedContextReplenishment_confinedToCores (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) :
    observableSlotsConfinedToCores st
      (migrateSchedContextReplenishment st scId fromCore toCore) [] := by
  refine ⟨fun c _ => (migrateSchedContextReplenishment_runQueue_current_eq st scId fromCore
            toCore c).1,
          fun c _ => (migrateSchedContextReplenishment_runQueue_current_eq st scId fromCore
            toCore c).2, ?_, ?_, ?_, ?_⟩
  all_goals intro c _
  all_goals (unfold migrateSchedContextReplenishment; split <;> simp)

theorem cleanupPreReceiveDonationChecked_confinedToCores (st st' : SystemState)
    (receiver : SeLe4n.ThreadId)
    (hStep : cleanupPreReceiveDonationChecked st receiver = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  have hEq : cleanupPreReceiveDonation st receiver = st' :=
    cleanupPreReceiveDonationChecked_ok_eq_cleanup st st' receiver hStep
  exact observableSlotsConfinedToCores_nil_of_scheduler_except_reschedule_machine_eq
    (hEq ▸ cleanupPreReceiveDonation_scheduler_eq st receiver)
    (hEq ▸ cleanupPreReceiveDonation_machine_eq st receiver)

/-- **`v0.35.161`**: the pre-receive return's own migration is that silence at the
receive leg — the reservation's replenishments move from the receiver's home core
to the owner's, and no observable slot moves with them. -/
theorem preReceiveReturnMigration_confinedToCores (st stClean : SystemState)
    (receiver : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores stClean (preReceiveReturnMigration st stClean receiver) [] := by
  unfold preReceiveReturnMigration
  split
  · exact migrateSchedContextReplenishment_confinedToCores _ _ _ _
  · exact observableSlotsConfinedToCores_refl _ _

/-- **`v0.35.161`**: and so the migrated return — the pop, then the migration — is
as silent as the bare pop was, which is what keeps `endpointReceiveDualWriteSet`'s
block-path entry at the executing core alone. -/
theorem cleanupPreReceiveDonationMigrated_confinedToCores (st st' : SystemState)
    (receiver : SeLe4n.ThreadId)
    (hStep : cleanupPreReceiveDonationMigrated st receiver = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  obtain ⟨stClean, hC, rfl⟩ := cleanupPreReceiveDonationMigrated_ok_decompose hStep
  exact observableSlotsConfinedToCores_trans
    (cleanupPreReceiveDonationChecked_confinedToCores st stClean receiver hC)
    (preReceiveReturnMigration_confinedToCores st stClean receiver)

theorem storeTcbIpcStateAndMessage_fromTcb_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage_fromTcb st tid tcb ipc msg = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  unfold storeTcbIpcStateAndMessage_fromTcb at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next st1 hStore =>
    simp only [Except.ok.injEq] at hStep
    subst hStep
    exact storeObject_confinedToCores st st1 _ _ hStore


-- ============================================================================
-- §2 SM6.B — the notification transitions
-- ============================================================================

-- SM8.B.2, relocated at **WS-RR RR8.12**: `notificationSignalWriteSet` is declared
-- in `IPC/CrossCore/NotificationSignal.lean`, beside the transition it is about.
-- This module is **staged** and imports `Kernel.API`, so the production
-- scheduler-domain footprint `schedLockSet_notificationSignalOnCore` could not
-- read a core list declared here and would have grown a second one; *when a
-- question has one owner and an asker that cannot see it, the owner is in the
-- wrong layer.*  The confinement theorem below, which consumes it, stays here.

/-- SM8.B.2 (coherence with the SM6.B lock set): the write set names the home
core of exactly the thread `notificationSignalWaiter?` pre-resolves — the thread
whose TCB write lock the runtime takes. -/
theorem notificationSignalWriteSet_eq_lockSet_waiter (st : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (hWaiter : notificationSignalWaiter? st notificationId = some waiter) :
    notificationSignalWriteSet st notificationId = [determineTargetCore st waiter] := by
  unfold notificationSignalWriteSet
  split
  · next ntfn hN =>
    split
    · next headWaiter rest hT =>
      have hResolve : notificationSignalWaiter? st notificationId = some headWaiter := by
        simp only [notificationSignalWaiter?, hN]
        exact SeLe4n.NoDupList.head?_eq_of_tail? hT
      rw [hResolve] at hWaiter
      simp only [Option.some.injEq] at hWaiter
      subst hWaiter
      rfl
    · next hT =>
      have hResolve : notificationSignalWaiter? st notificationId = none := by
        simp only [notificationSignalWaiter?, hN,
          SeLe4n.NoDupList.head?_eq_none_of_tail?_eq_none hT]
      rw [hResolve] at hWaiter; exact absurd hWaiter (by simp)
  · next hN =>
    have hResolve : notificationSignalWaiter? st notificationId = none := by
      simp only [notificationSignalWaiter?, hN]
    rw [hResolve] at hWaiter; exact absurd hWaiter (by simp)

/-- SM8.B.2 (**SM6.B, cross-core**): a notification signal's per-core writes stay
on the head waiter's home core.

The three-step pipeline — store the notification, store the waiter's IPC state,
wake the waiter — contributes `[] ++ [] ++ [home]`: the two object stores are
scheduler-silent and the wake writes exactly `determineTargetCore`. Pushing the
wake target back through the two stores is the same affinity-stability argument
SM6.B's `notificationSignalOnCore_remote_wake_preState` makes: neither store
touches `cpuAffinity`, and the notification id and the waiter's TCB are distinct
objects (recovered from the store's success, `notification_ne_waiter_of_store`). -/
theorem notificationSignalOnCore_confinedToCores (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (notificationSignalOnCore notificationId badge executingCore st).1
      (notificationSignalWriteSet st notificationId) := by
  unfold notificationSignalOnCore notificationSignalWriteSet
  cases hN : st.getNotification? notificationId with
  | none =>
    simp only []
    split <;> exact observableSlotsConfinedToCores_of_eq _ rfl
  | some ntfn =>
    simp only []
    cases hT : ntfn.waitingThreads.tail? with
    | none =>
      simp only []
      split
      · exact observableSlotsConfinedToCores_of_eq _ rfl
      · next st1 hStore => exact storeObject_confinedToCores st st1 _ _ hStore
    | some pair =>
      simp only []
      split
      · exact observableSlotsConfinedToCores_of_eq _ rfl
      · next st1 hStore =>
        split
        · exact observableSlotsConfinedToCores_of_eq _ rfl
        · next st2 hMsg =>
          have hInv' : st1.objects.invExt :=
            storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hStore
          have hNtfn' := storeObject_objects_eq st st1 notificationId _ hObjInv hStore
          have hNe : notificationId ≠ pair.1.toObjId :=
            notification_ne_waiter_of_store st1 st2 notificationId pair.1 _ .ready _
              hNtfn' hMsg
          have hTarget : determineTargetCore st2 pair.1 = determineTargetCore st pair.1 := by
            rw [storeTcbIpcStateAndMessage_determineTargetCore_eq st1 st2 pair.1 .ready _
                  pair.1 hInv' hMsg,
                storeObject_determineTargetCore_eq st st1 notificationId _ pair.1 hNe
                  hObjInv hStore]
          have hChain := observableSlotsConfinedToCores_trans
            (observableSlotsConfinedToCores_trans
              (storeObject_confinedToCores st st1 _ _ hStore)
              (storeTcbIpcStateAndMessage_confinedToCores st1 st2 pair.1 .ready _ hMsg))
            (wakeThread_confinedToCores st2 pair.1 executingCore)
          rw [hTarget] at hChain
          exact hChain

/-- SM8.B.2 (**SM6.B, cross-core**): a notification *wait* never writes another
core. The block path removes the caller from its own core's run queue; the
badge-consume path keeps it runnable and writes no scheduler slot at all. So a
waiter on core 0 is invisible to every observer on cores 1..n outright — there
is no "unless the shared half moved" caveat to discharge on the per-core side. -/
theorem notificationWaitOnCore_confinedToCores (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (executingCore : CoreId) (st : SystemState) :
    observableSlotsConfinedToCores st
      (notificationWaitOnCore notificationId waiter executingCore st).1 [executingCore] := by
  unfold notificationWaitOnCore
  cases hN : st.getNotification? notificationId with
  | none =>
    simp only []
    split <;> exact observableSlotsConfinedToCores_of_eq _ rfl
  | some ntfn =>
    simp only []
    cases hB : ntfn.pendingBadge with
    | some badge =>
      simp only []
      split
      · exact observableSlotsConfinedToCores_of_eq _ rfl
      · next st1 hStore =>
        split
        · exact observableSlotsConfinedToCores_of_eq _ rfl
        · next st2 hIpc =>
          exact observableSlotsConfinedToCores_widen
            (observableSlotsConfinedToCores_trans
              (storeObject_confinedToCores st st1 _ _ hStore)
              (storeTcbIpcState_confinedToCores st1 st2 waiter .ready hIpc))
    | none =>
      simp only []
      split
      · exact observableSlotsConfinedToCores_of_eq _ rfl
      · next tcb hLk =>
        split
        · exact observableSlotsConfinedToCores_of_eq _ rfl
        · split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next wt' hGuard =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next st1 hStore =>
              split
              · exact observableSlotsConfinedToCores_of_eq _ rfl
              · next st2 hIpc =>
                exact observableSlotsConfinedToCores_trans
                  (observableSlotsConfinedToCores_trans
                    (storeObject_confinedToCores st st1 _ _ hStore)
                    (storeTcbIpcStateAndMessage_fromTcb_confinedToCores st1 st2 waiter tcb _ _ hIpc))
                  (removeRunnableOnCore_confinedToCores st2 waiter executingCore)

-- SM8.B.2, relocated at **WS-RR RR8.12**: `notificationSignalBoundWriteSet` is
-- declared in `IPC/CrossCore/NotificationBind.lean`, beside
-- `notificationSignalBoundOnCore` and beside the production scheduler-domain
-- footprint `schedLockSet_notificationSignalBoundOnCore` that reads it.

/-- SM8.B.2 (**SM6.B, cross-core** — the *bound* signal, the live `.signal` arm):
a bound-aware signal's per-core writes stay inside
`notificationSignalBoundWriteSet`.

Two shapes:

* **Bound delivery** — dequeue the bound TCB from the endpoint it is blocked on,
  store the badge, **wake it on its home core**: `[] ++ [] ++ [boundHome]`.
  Naming `boundHome` at the pre-state needs the dequeue and the badge store to
  be non-migrations, which is what the two §1a frames added for this path say.
* **Fall-through** — no bound-delivery target, so the transition *is*
  `notificationSignalOnCore` and its own confinement applies verbatim. -/
theorem notificationSignalBoundOnCore_confinedToCores (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (notificationSignalBoundOnCore notificationId badge executingCore st).1
      (notificationSignalBoundWriteSet st notificationId) := by
  unfold notificationSignalBoundOnCore notificationSignalBoundWriteSet
  cases hTarget : boundDeliveryTarget? st notificationId with
  | none =>
    simp only []
    exact notificationSignalOnCore_confinedToCores notificationId badge executingCore st hObjInv
  | some pair =>
    obtain ⟨t, epId⟩ := pair
    simp only []
    cases hRemove : endpointQueueRemoveDual epId true t st with
    | error e => exact observableSlotsConfinedToCores_of_eq _ rfl
    | ok u =>
      obtain ⟨_, st1⟩ := u
      simp only []
      have hInv1 : st1.objects.invExt :=
        endpointQueueRemoveDual_preserves_objects_invExt st st1 epId true t hObjInv hRemove
      have hT1 : determineTargetCore st1 t = determineTargetCore st t :=
        endpointQueueRemoveDual_determineTargetCore_eq st st1 epId true t t hObjInv hRemove
      cases hStore : storeTcbReceiveComplete st1 t
          (some { IpcMessage.empty with badge := some badge }) with
      | error e => exact observableSlotsConfinedToCores_of_eq _ rfl
      | ok st2 =>
        have hT2 : determineTargetCore st2 t = determineTargetCore st1 t :=
          storeTcbReceiveComplete_determineTargetCore_eq st1 st2 t _ t hInv1 hStore
        have hChain := observableSlotsConfinedToCores_widen_cons
          (observableSlotsConfinedToCores_trans
            (endpointQueueRemoveDual_confinedToCores epId true t st st1 hRemove)
            (storeTcbReceiveComplete_confinedToCores st1 st2 t _ hStore))
          (wakeThread_confinedToCores st2 t executingCore)
        rw [hT2, hT1] at hChain
        exact hChain

-- ============================================================================
-- §3 SM6.A — the endpoint call
-- ============================================================================

-- **WS-RR RR8.12 Cut C3a (`v0.35.163`)**: `endpointCallWriteSet` moved to
-- `IPC/CrossCore/EndpointCall.lean`, beside the resolver it reads
-- (`endpointCallReceiver?`), so the production scheduler footprint
-- `schedLockSet_endpointCallOnCore` can read it.  The confinement theorem below
-- stays here: `observableSlotsConfinedToCores` is this module's predicate.

/-- SM8.B.2 (**the flagship two-core instantiation**): a cross-core endpoint
call's per-core writes stay inside `endpointCallWriteSet`.

The rendezvous path is a six-step pipeline — pop the receive queue, store the
receiver's message, **wake the receiver on its home core**, store the caller's
blocked state, link the stashed reply, **deschedule the caller on its own core**
— contributing `[] ++ [] ++ [receiverHome] ++ [] ++ [] ++ [executingCore]`. The
`§1a` frame layer is what lets `receiverHome` be named at the *pre-state*: the
pop and the two stores rewrite queue links, an endpoint and IPC fields, never a
`cpuAffinity`, so none of them is a migration.

The blocking path enqueues the caller and deschedules it, writing only
`executingCore`; every fail-closed arm writes nothing. -/
theorem endpointCallOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointCallOnCore endpointId caller msg executingCore st).1
      (endpointCallWriteSet st endpointId executingCore) := by
  unfold endpointCallOnCore endpointCallWriteSet endpointCallReceiver?
  split
  · exact observableSlotsConfinedToCores_of_eq _ rfl
  · split
    · exact observableSlotsConfinedToCores_of_eq _ rfl
    · cases hEp : st.getEndpoint? endpointId with
      | none =>
        simp only []
        split <;> exact observableSlotsConfinedToCores_of_eq _ rfl
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none =>
          -- Blocking path: enqueue the caller, store its blocked state,
          -- deschedule it on its own core.
          simp only []
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next st1 hEnq =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next st2 hMsg =>
              exact observableSlotsConfinedToCores_trans
                (observableSlotsConfinedToCores_trans
                  (endpointQueueEnqueue_confinedToCores endpointId false caller st st1 hEnq)
                  (storeTcbIpcStateAndMessage_confinedToCores st1 st2 caller _ _ hMsg))
                (removeRunnableOnCore_confinedToCores st2 caller executingCore)
        | some headRecv =>
          -- Rendezvous path: wake the receiver on its home core, block the caller.
          simp only []
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next recvTid recvTcb st1 hPop =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next st2 hMsgR =>
              split
              · exact observableSlotsConfinedToCores_of_eq _ rfl
              · next st4 hMsgC =>
                split
                · exact observableSlotsConfinedToCores_of_eq _ rfl
                · next st5 hLink =>
                  have hEpObj : st.objects[endpointId]? = some (.endpoint ep) :=
                    (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
                  have hPopHead : ep.receiveQ.head = some recvTid := by
                    have h := endpointQueuePopHead_returns_head endpointId true st ep recvTid
                      st1 hEpObj hPop
                    simpa using h
                  have hRecv : recvTid = headRecv := by
                    rw [hHead] at hPopHead; simpa using hPopHead.symm
                  have hInv1 : st1.objects.invExt :=
                    endpointQueuePopHead_preserves_objects_invExt endpointId true st st1
                      recvTid recvTcb hObjInv hPop
                  have hT1 : determineTargetCore st1 recvTid = determineTargetCore st recvTid :=
                    endpointQueuePopHead_determineTargetCore_eq endpointId true st st1
                      recvTid recvTcb recvTid hObjInv hPop
                  have hT2 : determineTargetCore st2 recvTid = determineTargetCore st1 recvTid :=
                    storeTcbIpcStateAndMessage_determineTargetCore_eq st1 st2 recvTid
                      .ready (some msg) recvTid hInv1 hMsgR
                  have hChain := observableSlotsConfinedToCores_trans
                    (observableSlotsConfinedToCores_trans
                      (observableSlotsConfinedToCores_trans
                        (endpointQueuePopHead_confinedToCores endpointId true st st1
                          recvTid hPop)
                        (storeTcbIpcStateAndMessage_confinedToCores st1 st2 recvTid
                          .ready (some msg) hMsgR))
                      (wakeThread_confinedToCores st2 recvTid executingCore))
                    (observableSlotsConfinedToCores_trans
                      (observableSlotsConfinedToCores_trans
                        (storeTcbIpcStateAndMessage_confinedToCores
                          (wakeThread st2 recvTid executingCore).1 st4 caller _ _ hMsgC)
                        (linkServerStashedReply_confinedToCores caller recvTid st4 st5 hLink))
                      (removeRunnableOnCore_confinedToCores st5 caller executingCore))
                  rw [hT2, hT1, hRecv] at hChain
                  exact observableSlotsConfinedToCores_mono (by intro c hc; simpa using hc) hChain

-- ============================================================================
-- §4 SM6.C — the reply transition
-- ============================================================================

/-- SM8.B.2 (**SM6.C, cross-core**): a cross-core reply's per-core writes stay on
the **unblocked caller's** home core. The replier does not block — it keeps
running on its own core — so unlike the call this is a one-element write set,
and it is a *remote* one whenever the answered caller is homed elsewhere.

The target is a parameter rather than a pre-resolution, so no lock-set coherence
lemma is needed here: the transition and the write set name the same thread by
construction. -/
theorem endpointReplyOnCore_confinedToCores (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointReplyOnCore replier target msg executingCore st).1
      [determineTargetCore st target] := by
  unfold endpointReplyOnCore
  split
  · exact observableSlotsConfinedToCores_of_eq _ rfl
  · split
    · exact observableSlotsConfinedToCores_of_eq _ rfl
    · cases hLk : lookupTcb st target with
      | none => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
      | some tcb =>
        simp only []
        split
        · next epId replyTarget hIpc =>
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next expected hSome =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next st1 hStore =>
              have hOld : st.getTcb? target = some tcb :=
                (SystemState.getTcb?_eq_some_iff st target tcb).mpr
                  (lookupTcb_some_objects st target tcb hLk)
              have hT1 : determineTargetCore st1 target = determineTargetCore st target :=
                storeTcbIpcStateAndMessage_fromTcb_determineTargetCore_eq st st1 target tcb
                  .ready (some msg) target hOld hObjInv hStore
              have hPre := observableSlotsConfinedToCores_trans
                (storeTcbIpcStateAndMessage_fromTcb_confinedToCores st st1 target tcb
                  .ready (some msg) hStore)
                (wakeThread_confinedToCores st1 target executingCore)
              rw [hT1] at hPre
              split
              · exact hPre
              · next rid hReply =>
                split
                · next unit st2 hConsume =>
                  exact observableSlotsConfinedToCores_trans hPre
                    (removeCallerReplyFrame_confinedToCores _ st2 target rid hConsume)
                · exact observableSlotsConfinedToCores_of_eq _ rfl
        · exact observableSlotsConfinedToCores_of_eq _ rfl

-- ============================================================================
-- §4a SM6.C — the receive leg
-- ============================================================================

-- SM8.B.2, relocated at **WS-RR RR8.12**: `endpointReceiveDualWriteSet` is
-- declared in `IPC/CrossCore/EndpointReply.lean`, beside `endpointReceiveDualOnCore`
-- and beside the production scheduler-domain footprint
-- `schedLockSet_endpointReceiveOnCore` that reads it.  This module imports
-- `Kernel.API`, which the footprint cannot, so a core list declared here would
-- be unreachable from the footprint the syscall seam brackets over.

/-- SM8.B.2 (**SM6.C, cross-core** — the `replyRecv` receive leg): a cross-core
endpoint receive's per-core writes stay inside `endpointReceiveDualWriteSet`.

Three shapes, all covered:

* **`blockedOnSend` rendezvous** — pop the send queue, mark the sender `.ready`,
  **wake it on its home core**, store the receiver's message:
  `[] ++ [] ++ [senderHome] ++ []`. The §1a frame layer is what lets
  `senderHome` be named at the pre-state.
* **`blockedOnCall` rendezvous** — the caller becomes `.blockedOnReply` and is
  deliberately *not* woken (the Call contract), so this path writes no core at
  all and is covered by the declared set through the append.
* **Block path** — return any donated SchedContext (and, since `v0.35.161`,
  migrate its replenishments home — a replenish-queue write, which is outside
  the observer's read set), enqueue on the receive queue, stash the server's
  reply object, then deschedule the receiver on **its own** core:
  `[executingCore]`.

Every fail-closed arm returns the pre-state. -/
theorem endpointReceiveDualOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1
      (endpointReceiveDualWriteSet st endpointId executingCore) := by
  unfold endpointReceiveDualOnCore endpointReceiveDualWriteSet
  cases hEp : st.getEndpoint? endpointId with
  | none =>
    simp only []
    split <;> exact observableSlotsConfinedToCores_of_eq _ rfl
  | some ep =>
    simp only []
    cases hHead : ep.sendQ.head with
    | none =>
      -- Block path: every step is scheduler-silent until the receiver is
      -- descheduled on its own core.
      simp only []
      split
      · exact observableSlotsConfinedToCores_of_eq _ rfl
      · next stClean hClean =>
        split
        · exact observableSlotsConfinedToCores_of_eq _ rfl
        · next st1 hEnq =>
          have hPre := observableSlotsConfinedToCores_trans
            (cleanupPreReceiveDonationMigrated_confinedToCores st stClean receiver hClean)
            (endpointQueueEnqueue_confinedToCores endpointId true receiver stClean st1 hEnq)
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next st2 hIpc =>
            have hPre2 := observableSlotsConfinedToCores_trans hPre
              (storeTcbIpcStateAndMessage_confinedToCores st1 st2 receiver _ _ hIpc)
            split
            · exact observableSlotsConfinedToCores_widen_cons hPre2
                (removeRunnableOnCore_confinedToCores st2 receiver executingCore)
            · next rTcb hTcb =>
              split
              · split
                · exact observableSlotsConfinedToCores_of_eq _ rfl
                · next _ st3 hStash =>
                  exact observableSlotsConfinedToCores_widen_cons
                    (observableSlotsConfinedToCores_trans hPre2
                      (storeObject_confinedToCores st2 st3 _ _ hStash))
                    (removeRunnableOnCore_confinedToCores st3 receiver executingCore)
              · exact observableSlotsConfinedToCores_of_eq _ rfl
    | some senderHead =>
      simp only []
      split
      · exact observableSlotsConfinedToCores_of_eq _ rfl
      · next sender senderTcb st1 hPop =>
        have hEpObj : st.objects[endpointId]? = some (.endpoint ep) :=
          (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
        have hPopHead : ep.sendQ.head = some sender := by
          have h := endpointQueuePopHead_returns_head endpointId false st ep sender st1
            hEpObj hPop
          simpa using h
        have hSender : sender = senderHead := by
          rw [hHead] at hPopHead; simpa using hPopHead.symm
        have hInv1 : st1.objects.invExt :=
          endpointQueuePopHead_preserves_objects_invExt endpointId false st st1
            sender senderTcb hObjInv hPop
        have hT1 : determineTargetCore st1 sender = determineTargetCore st sender :=
          endpointQueuePopHead_determineTargetCore_eq endpointId false st st1
            sender senderTcb sender hObjInv hPop
        have hPopConf := endpointQueuePopHead_confinedToCores endpointId false st st1
          sender hPop
        split
        · -- `blockedOnCall` sender: recorded as `.blockedOnReply`, never woken.
          rw [if_pos rfl]
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next st2 hIpc =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next rid =>
              split
              · exact observableSlotsConfinedToCores_of_eq _ rfl
              · next st3 hLink =>
                split
                · next st4 hMsg =>
                  exact observableSlotsConfinedToCores_widen_any
                    (observableSlotsConfinedToCores_trans
                      (observableSlotsConfinedToCores_trans hPopConf
                        (storeTcbIpcStateAndMessage_confinedToCores st1 st2 sender _ _ hIpc))
                      (observableSlotsConfinedToCores_trans
                        (linkCallerReply_confinedToCores sender rid st2 st3 hLink)
                        (storeTcbIpcStateAndMessage_confinedToCores st3 st4 receiver _ _ hMsg)))
                · exact observableSlotsConfinedToCores_of_eq _ rfl
        · -- `blockedOnSend` sender: woken on its own home core.
          rw [if_neg (by simp)]
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next st2 hReady =>
            have hT2 : determineTargetCore st2 sender = determineTargetCore st1 sender :=
              storeTcbIpcStateAndMessage_determineTargetCore_eq st1 st2 sender
                .ready none sender hInv1 hReady
            split
            · next st3 hMsg =>
              have hChain := observableSlotsConfinedToCores_trans
                (observableSlotsConfinedToCores_trans hPopConf
                  (storeTcbIpcStateAndMessage_confinedToCores st1 st2 sender .ready none hReady))
                (observableSlotsConfinedToCores_trans
                  (wakeThread_confinedToCores st2 sender executingCore)
                  (storeTcbIpcStateAndMessage_confinedToCores
                    (wakeThread st2 sender executingCore).1 st3 receiver _ _ hMsg))
              rw [hT2, hT1, hSender] at hChain
              exact observableSlotsConfinedToCores_mono (by intro c hc; simpa using hc) hChain
            · exact observableSlotsConfinedToCores_of_eq _ rfl

-- ============================================================================
-- §5 SM6.E — the cancellation transition
-- ============================================================================

/-- SM8.B.2 (**SM6.E, cross-core**): the cancellation mechanism is
`descheduleThread`, whose confinement §1 proves — it writes only the core the
state **places** the victim on (WS-RR RR8.6), not the core running the
cancellation. This restates that at the SM6.E name so the coverage list below
reads off one theorem per sub-phase: a `tcbSuspend` issued on core 0 against a
victim placed on core 2 is invisible to observers on cores 1 and 3 outright. -/
theorem cancellationCrossCore_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    observableSlotsConfinedToCores st (descheduleThread st tid executingCore).1
      (descheduleAtPlacementCores st tid) :=
  descheduleThread_confinedToCores st tid executingCore

/-- SM8.B.2: the SM6.E object-level teardown is per-core **silent** — it rewrites
the victim's IPC fields, the endpoint/notification queues it sat in, and its
reply link, and touches neither the scheduler nor any register bank.

The `machine` half is `cancelIpcBlocking_machine_eq`, added beside the
long-standing `cancelIpcBlocking_scheduler_eq` for this consumer: per-core
confinement reads the register banks as well as the scheduler slots, so a
scheduler frame alone never bounded the teardown's observable writes. -/
theorem cancelIpcBlocking_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) :
    observableSlotsConfinedToCores st (cancelIpcBlocking st tid tcb) [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_except_reschedule_machine_eq
    (cancelIpcBlocking_scheduler_eq st tid tcb) (cancelIpcBlocking_machine_eq st tid tcb)

-- ============================================================================
-- §5a SM5.F — the priority-inheritance chain walk
-- ============================================================================
--
-- The below-API transitions above are *not* the whole live picture. The live
-- `.call` arm is `endpointCallCrossCoreDispatch`, which runs the transition and
-- then `applyCallDonation` + `propagatePipChainCrossCore`; the chain walk
-- re-buckets each boosted server's run queue **on that server's home core**, so
-- it can write cores the endpoint call's own write set does not name.
--
-- Leaving that out would make any claim about the live dispatch's write set
-- false, so the chain walk gets a write set of its own, by the same discipline:
-- computed from the pre-state, mirroring the transition's own recursion.

/-- KSC-1 (the reschedule-SGI accumulator): the reschedule-pending flags are not
observable slots, so clearing one is confined to no core. -/
theorem clearReschedulePendingOnCore_confinedToCores (st : SystemState) (c : CoreId) :
    observableSlotsConfinedToCores st (st.clearReschedulePendingOnCore c) [] :=
  ⟨fun _ _ => by simp, fun _ _ => by simp, fun _ _ => by simp, fun _ _ => by simp,
   fun _ _ => by simp, fun _ _ => rfl⟩

/-- KSC-1: the key-change writer only raises flags, so it is confined to no core. -/
theorem markKeyChangeFor_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    observableSlotsConfinedToCores st (markKeyChangeFor st tid k) [] :=
  ⟨fun _ _ => by rw [markKeyChangeFor_runQueueOnCore],
   fun _ _ => by rw [markKeyChangeFor_currentOnCore],
   fun _ _ => by rw [markKeyChangeFor_activeDomainOnCore],
   fun _ _ => by rw [markKeyChangeFor_domainTimeRemainingOnCore],
   fun _ _ => by rw [markKeyChangeFor_domainScheduleIndexOnCore],
   fun _ _ => by rw [markKeyChangeFor_machine]⟩

/-- KSC-1: the pre-state form of the key-change writer only raises flags too. -/
theorem markKeyChangeFrom_confinedToCores (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (markKeyChangeFrom pre st tid) [] :=
  ⟨fun _ _ => by rw [markKeyChangeFrom_runQueueOnCore],
   fun _ _ => by rw [markKeyChangeFrom_currentOnCore],
   fun _ _ => by rw [markKeyChangeFrom_activeDomainOnCore],
   fun _ _ => by rw [markKeyChangeFrom_domainTimeRemainingOnCore],
   fun _ _ => by rw [markKeyChangeFrom_domainScheduleIndexOnCore],
   fun _ _ => by rw [markKeyChangeFrom_machine]⟩

/-- KSC-1: a trailing flag-only write does not widen a confinement set. -/
theorem observableSlotsConfinedToCores_then_flagOnly {st stMid st' : SystemState}
    {cs : List CoreId} (h₁ : observableSlotsConfinedToCores st stMid cs)
    (h₂ : observableSlotsConfinedToCores stMid st' []) :
    observableSlotsConfinedToCores st st' cs :=
  List.append_nil cs ▸ observableSlotsConfinedToCores_trans h₁ h₂

/-- SM8.B.2: a PIP re-bucketing writes core `c`'s run queue and the boosted
TCB, and nothing else per-core. -/
theorem updatePipBoostOnCore_confinedToCores (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (updatePipBoostOnCore st c tid) [c] := by
  refine ⟨fun c' hc => updatePipBoostOnCore_runQueueOnCore_ne st c c' tid
            (fun h => hc (by simp [h])),
          fun c' _ => updatePipBoostOnCore_currentOnCore st c c' tid, ?_, ?_, ?_, ?_⟩
  all_goals intro c' _
  all_goals simp only [updatePipBoostOnCore, SystemState.getTcb?]
  all_goals repeat' split
  all_goals first
    | rfl
    | (simp only [markKeyChangeFor_activeDomainOnCore,
        markKeyChangeFor_domainTimeRemainingOnCore,
        markKeyChangeFor_domainScheduleIndexOnCore, markKeyChangeFor_machine,
        SchedulerState.setRunQueueOnCore_activeDomainOnCore,
        SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore,
        SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]
       try rfl)

/-- SM8.B.2: one chain step writes exactly the boosted thread's home core. -/
theorem pipBoostWithWake_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    observableSlotsConfinedToCores st (pipBoostWithWake st tid executingCore).1
      [determineTargetCore st tid] :=
  updatePipBoostOnCore_confinedToCores st (determineTargetCore st tid) tid

-- **WS-RR RR8.12 Cut 8b (`v0.35.145`)**: `pipChainWriteSet` moved to
-- `Scheduler/PriorityInheritance/Propagate.lean`, beside the walk it mirrors.
-- It was declared here, in a STAGED module, and the `.replyRecv` write sets that
-- compose it have to reach production so the arm can declare a scheduler-domain
-- footprint -- *when a question has one owner and an asker that cannot see it,
-- the owner is in the wrong layer*, for the fifth time in this row (Cuts 5 and 7
-- moved four others for the same reason).  It keeps the `SeLe4n.Kernel`
-- namespace it was declared in, so the move renames nothing.

/-- SM8.B.2 (**SM5.F, cross-core**): the chain walk's per-core writes stay inside
`pipChainWriteSet`. By induction on the fuel, composing one
`pipBoostWithWake_confinedToCores` per step. -/
theorem propagatePipChainCrossCore_confinedToCores (executingCore : CoreId) :
    ∀ (fuel : Nat) (st : SystemState) (startTid : SeLe4n.ThreadId),
      observableSlotsConfinedToCores st
        (propagatePipChainCrossCore st startTid executingCore fuel).1
        (pipChainWriteSet st startTid executingCore fuel)
  | 0, st, _ => observableSlotsConfinedToCores_of_eq _ rfl
  | fuel + 1, st, startTid => by
      rw [propagatePipChainCrossCore_step]
      simp only [pipChainWriteSet]
      cases hNext : blockingServer st startTid with
      | none =>
        exact pipBoostWithWake_confinedToCores st startTid executingCore
      | some nextServer =>
        exact observableSlotsConfinedToCores_trans
          (pipBoostWithWake_confinedToCores st startTid executingCore)
          (propagatePipChainCrossCore_confinedToCores executingCore fuel
            (pipBoostWithWake st startTid executingCore).1 nextServer)


/-- **WS-RR RR7.22 (residual, remediation)**: the migrated teardown writes no
observable slot beyond the plain teardown's — a replenish queue is not one. -/
theorem cancelIpcBlockingMigrated_confinedToCores (victim : SeLe4n.ThreadId) (tcb : TCB)
    (st : SystemState) :
    observableSlotsConfinedToCores (cancelIpcBlocking st victim tcb)
      (cancelIpcBlockingMigrated victim tcb st) [] := by
  unfold cancelIpcBlockingMigrated
  split
  · rename_i scId holder _
    exact migrateSchedContextReplenishment_confinedToCores _ scId _ _
  · exact observableSlotsConfinedToCores_refl _ _

/-- **`v0.35.158`** (WS-OD OD1.7's wake until then): the reclaim's holder
deschedule writes exactly the unbound holder's placed core — and no core at all
when it does not fire, which is every arm but a reply arm whose caller had
donated, and a holder placed nowhere. -/
theorem descheduleUnboundHolder_confinedToCores (stPre stPost : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) :
    observableSlotsConfinedToCores stPost
      (descheduleUnboundHolder stPre stPost victim tcb)
      (cancelUnboundHolderCore? stPre stPost victim tcb).toList := by
  unfold descheduleUnboundHolder cancelUnboundHolderCore?
  cases hW : cancelUnboundHolder? stPre stPost victim tcb with
  | none => exact observableSlotsConfinedToCores_refl _ _
  | some holder =>
    show observableSlotsConfinedToCores stPost (descheduleAtPlacement stPost holder)
      (placedCoreOf? stPost holder).toList
    rw [← descheduleAtPlacementCores_eq_toList]
    exact descheduleAtPlacement_confinedToCores stPost holder

/-- **WS-RR RR8.12**, re-keyed at `v0.35.158`: the teardown with its reclaim
completed writes exactly the unbound holder's placed core — the migration
contributing nothing observable and the teardown itself nothing per-core.

Derived once here, because both consumers need it: the composite below, and the
live suspend pipeline's G2 (`suspendThreadOnCoreWriteSet`), which until RR8.12
took the bare teardown and so declared no core for a step it did not perform. -/
theorem cancelIpcBlockingReclaimed_confinedToCores (victim : SeLe4n.ThreadId) (tcb : TCB)
    (st : SystemState) :
    observableSlotsConfinedToCores st (cancelIpcBlockingReclaimed victim tcb st)
      (cancelUnboundHolderCore? st (cancelIpcBlockingMigrated victim tcb st)
        victim tcb).toList := by
  have h := observableSlotsConfinedToCores_trans
    (observableSlotsConfinedToCores_trans
      (cancelIpcBlocking_confinedToCores st victim tcb)
      (cancelIpcBlockingMigrated_confinedToCores victim tcb st))
    (descheduleUnboundHolder_confinedToCores st
      (cancelIpcBlockingMigrated victim tcb st) victim tcb)
  simpa only [List.nil_append, cancelIpcBlockingReclaimed] using h

/-- SM8.B.2 (**SM6.E, the composed cancellation**): `cancelIpcBlockingOnCore`
writes the core the pre-state **places** the victim on (WS-RR RR8.6), and —
since `v0.35.158` — the core its reclaim's holder deschedule removes the unbound
holder from, when there is one (WS-OD OD1.7's wake wrote that holder's *home*
core until then).  Not the core running the cancellation, and not any core the
victim's endpoint or notification neighbours are homed on.

`[] ++ [] ++ holder ++ placed`: the teardown contributes nothing per-core, WS-RR
RR7.22's replenishment migration contributes nothing either (it writes a
replenish queue, which is not an observable slot), the holder deschedule
contributes the holder's placed core exactly when it fires, and the victim's
placement removal contributes at most one core.  The victim's removal resolves
its core on the post-reclaim state and this list is stated on the **pre**-state,
which is the only state a caller holds;
`cancelIpcBlockingReclaimed_placedCoreOf?_victim` is the pushback, an equation —
until `v0.35.158` it was a disjunction, because the wake could on no reachable
state insert the victim itself, and the list is still stated through `mono`
only to put the cores in reading order.

**The second core is the point of the reclaim's scheduler step, not a
regression.**  The list read `[determineTargetCore st victim]` before OD1.7, and
that was true only because the reclaim's abort left the holder on no run queue
at all — the stranding defect.  Taking the holder the reclaim unbound off its
placement necessarily writes that core, which is neither the victim's nor the
executing core, so the honest statement names it.  Where no donation is resolved
the holder list is empty and this is the pre-OD1.7 statement at the placed core
(`cancelIpcBlockingOnCore_confinedToCores_of_no_donation`). -/
theorem cancelIpcBlockingOnCore_confinedToCores (victim : SeLe4n.ThreadId) (tcb : TCB)
    (executingCore : CoreId) (st : SystemState) :
    observableSlotsConfinedToCores st
      (cancelIpcBlockingOnCore victim tcb executingCore st).1
      ((cancelUnboundHolderCore? st (cancelIpcBlockingMigrated victim tcb st)
          victim tcb).toList ++ descheduleAtPlacementCores st victim) := by
  have hStep := observableSlotsConfinedToCores_trans
    (cancelIpcBlockingReclaimed_confinedToCores victim tcb st)
    (descheduleAtPlacement_confinedToCores (cancelIpcBlockingReclaimed victim tcb st) victim)
  refine observableSlotsConfinedToCores_mono ?_ hStep
  intro c hc
  simp only [List.mem_append] at hc ⊢
  rcases hc with hw | hd
  · exact Or.inl hw
  · rw [descheduleAtPlacementCores_eq_toList, cancelIpcBlockingReclaimed_placedCoreOf?_victim]
      at hd
    rw [descheduleAtPlacementCores_eq_toList]
    exact Or.inr hd

/-- `v0.35.158` (WS-OD OD1.7's wake until then): with no donation resolved the
reclaim deschedules nobody, so the composite is confined to the victim's placed
core exactly as it was before OD1.7 — which is every arm but a reply arm whose
caller had donated. -/
theorem cancelIpcBlockingOnCore_confinedToCores_of_no_donation (victim : SeLe4n.ThreadId)
    (tcb : TCB) (executingCore : CoreId) (st : SystemState)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = none) :
    observableSlotsConfinedToCores st
      (cancelIpcBlockingOnCore victim tcb executingCore st).1
      (descheduleAtPlacementCores st victim) := by
  have hW := cancelIpcBlockingOnCore_confinedToCores victim tcb executingCore st
  rwa [cancelUnboundHolderCore?_of_no_donation _ _ victim tcb h, Option.toList,
    List.nil_append] at hW

/-- SM8.B.2: SchedContext donation is per-core silent — it rewrites bindings in
the object store and, at most, the replenishment queue, which SM8.A's
`onCore_perCore_independence` puts outside the observer's read set entirely. -/
theorem applyCallDonation_confinedToCores (st st' : SystemState)
    (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (hStep : applyCallDonation st callerVtid receiverVtid = .ok st') :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_except_reschedule_machine_eq
    (applyCallDonation_scheduler_eq st callerVtid receiverVtid st' hStep)
    (applyCallDonation_machine_eq st callerVtid receiverVtid st' hStep)

/-- WS-RR RR2.7: the **migrating** call donation is per-core silent too. The
RR2.2 replenishment migration it adds writes two replenish-queue slots, and
SM8.A's `onCore_perCore_independence` puts that queue outside the observer's
read set entirely — the same reason the cancellation arm's migration is silent.
So routing the live `.call` arm through the migrating form changes nothing an
observer can see, and the dispatch write set below is unchanged by RR2.7. -/
theorem applyCallDonationOnCore_confinedToCores (st st' : SystemState)
    (callerVtid receiverVtid : SeLe4n.ValidThreadId) (donorHome doneeHome : CoreId)
    (hStep : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  obtain ⟨st1, hDon, harm⟩ := applyCallDonationOnCore_ok_decompose st st' callerVtid receiverVtid
    donorHome doneeHome hStep
  have h1 := applyCallDonation_confinedToCores st st1 callerVtid receiverVtid hDon
  rcases harm with ⟨_, hEq⟩ | ⟨scId, _, hEq⟩
  · rw [hEq]; exact h1
  · rw [hEq]
    simpa using observableSlotsConfinedToCores_trans h1
      (migrateSchedContextReplenishment_confinedToCores st1 scId donorHome doneeHome)

/-- **WS-OD OD3.6**: the shared rendezvous hand-off is per-core silent, and so is
its guarded form.

Both receiving arms run it, so its confinement is stated once here rather than
re-derived at each arm — and `[]` rather than a core list because a SchedContext
hand-off writes only bindings, which the per-core observer does not read. -/
theorem applyRendezvousCallDonation_confinedToCores (st st' : SystemState)
    (receiver donor : SeLe4n.ThreadId)
    (hStep : applyRendezvousCallDonation st receiver donor = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  obtain ⟨donorV, receiverV, _, _, hDon⟩ :=
    applyRendezvousCallDonation_ok_decompose st st' receiver donor hStep
  exact applyCallDonationOnCore_confinedToCores st st' donorV receiverV _ _ hDon

/-- WS-OD OD3.6: and the guarded form, whose other arm is the identity. -/
theorem applyReceiveRendezvousDonation_confinedToCores (st st' : SystemState)
    (receiver dequeued : SeLe4n.ThreadId)
    (hStep : applyReceiveRendezvousDonation st receiver dequeued = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  unfold applyReceiveRendezvousDonation at hStep
  cases hCall : rendezvousDequeuedCall st dequeued with
  | false =>
    rw [hCall] at hStep
    simp only [Bool.false_eq_true, if_false] at hStep
    cases hStep
    exact observableSlotsConfinedToCores_refl st []
  | true =>
    rw [hCall] at hStep
    simp only [if_true] at hStep
    exact applyRendezvousCallDonation_confinedToCores st st' receiver dequeued hStep

/-- **WS-OD OD3.14: the cores the receive rendezvous' hand-off may write.**

OD3.6's donation half is per-core silent, so this is exactly the chain walk's own
write set — the receiver's home core, and every boosted server's above it.  On a
receive that dequeued no `Call` neither half runs and the set is empty.

Like `.call`'s `endpointCallLiveWriteSet`, the chain leg is **not** computable
from the pre-state: the walk runs at the *post-donation* state, and the donation
rewrites SchedContext bindings that `determineTargetCore` reads.  `chainState` is
therefore a parameter rather than something this definition pretends to recover;
callers instantiate it at the donation's own result. -/
def receiveRendezvousHandoffWriteSet (st : SystemState)
    (receiver dequeued : SeLe4n.ThreadId) (executingCore : CoreId)
    (chainState : SystemState) : List CoreId :=
  if rendezvousDequeuedCall st dequeued then
    pipChainWriteSet chainState receiver executingCore chainState.objectIndex.length
  else []

/-- **WS-OD OD3.14**: the hand-off's per-core writes stay inside that set.

Two legs composed, and nothing new: the donation is `[]`-confined (OD3.6) and
the walk is confined to `pipChainWriteSet` at the state it runs on (SM8.B.2).
The declared set is the walk's alone because widening `[]` into it is free
(`observableSlotsConfinedToCores_mono`) — stating the union `[] ++ …` would
declare the same cores in a shape every consumer would have to normalise. -/
theorem applyReceiveRendezvousHandoff_confinedToCores (st stDon st' : SystemState)
    (receiver dequeued : SeLe4n.ThreadId) (executingCore : CoreId)
    (hDon : applyReceiveRendezvousDonation st receiver dequeued = .ok stDon)
    (hStep : applyReceiveRendezvousHandoff st receiver dequeued executingCore = .ok st') :
    observableSlotsConfinedToCores st st'
      (receiveRendezvousHandoffWriteSet st receiver dequeued executingCore stDon) := by
  obtain ⟨stDon', hDon', hEq⟩ :=
    applyReceiveRendezvousHandoff_ok_decompose st st' receiver dequeued executingCore hStep
  have hSame : stDon' = stDon := by rw [hDon'] at hDon; exact Except.ok.inj hDon
  subst hSame
  have hDonConf : observableSlotsConfinedToCores st stDon' [] :=
    applyReceiveRendezvousDonation_confinedToCores st stDon' receiver dequeued hDon'
  unfold receiveRendezvousHandoffWriteSet
  cases hCall : rendezvousDequeuedCall st dequeued with
  | false =>
      rw [hCall] at hEq
      simp only [Bool.false_eq_true, if_false] at hEq
      subst hEq
      simp only [Bool.false_eq_true, if_false]
      exact hDonConf
  | true =>
      rw [hCall] at hEq
      simp only [if_true] at hEq
      subst hEq
      simp only [if_true]
      unfold applyReceiverPipHandoff
      exact observableSlotsConfinedToCores_trans hDonConf
        (propagatePipChainCrossCore_confinedToCores executingCore
          stDon'.objectIndex.length stDon' receiver)

-- **WS-RR RR8.12 Cut 8b (`v0.35.145`)**: `receiveLegPipHandoffWriteSet` moved to `Kernel/IPC/Operations/Donation.lean`, beside the
-- transition it describes.  A write set declared in a STAGED module is one the
-- production scheduler footprint cannot read, which is the layering rule Cuts 5
-- and 7 applied four times over.  The CONFINEMENT theorem stays here: it is an
-- SM8.B claim about `observableSlotsConfinedToCores`, which is this module's.

/-- **WS-OD OD3.14**: the receive leg's hand-off writes only inside that set —
nothing at all on the two identity arms, and the chain walk's own cores on the
third. -/
theorem applyReceiveLegPipHandoff_confinedToCores (st : SystemState)
    (receiver dequeued alreadyWalked : SeLe4n.ThreadId) (executingCore : CoreId) :
    observableSlotsConfinedToCores st
      (applyReceiveLegPipHandoff st receiver dequeued alreadyWalked executingCore)
      (receiveLegPipHandoffWriteSet st receiver dequeued alreadyWalked executingCore) := by
  unfold applyReceiveLegPipHandoff receiveLegPipHandoffWriteSet applyReceiverPipHandoff
  split
  · exact observableSlotsConfinedToCores_refl st []
  · split
    · exact propagatePipChainCrossCore_confinedToCores executingCore st.objectIndex.length st
        receiver
    · exact observableSlotsConfinedToCores_refl st []


/-- SM8.B.2: **the cores the live cross-core `.call` may write.**

`endpointCallCrossCoreDispatch` is not just `endpointCallOnCore`: it runs the
transition (in its WithCaps form), then `applyCallDonation`, then
`propagatePipChainCrossCore`. The donation is per-core silent, but the chain
walk re-buckets each boosted server's run queue on that server's **home** core,
which the endpoint call's own write set does not name. A claim about the live
dispatch has to be made against the union — anything narrower is false.

**The chain leg is not computable from the pre-state, and this signature says
so.** The live walk is `propagatePipChainCrossCore st'' receiverTid`: it starts
at the *resolved receiver*, not the caller, and runs at the *post-donation*
state, not `st`. Both matter — the call blocks the caller on reply and the
donation rewrites SchedContext bindings, so `blockingServer` at `st''` is
genuinely not `blockingServer` at `st`, and a pre-state walk from the caller
would name a different chain. An earlier form of this definition did exactly
that and was wrong (PR #861 review).

So `chainState` and `chainStart` are explicit parameters rather than something
this definition pretends to recover: instantiate them at the post-donation state
and the receiver `endpointCallReceiver? st endpointId` resolves. The
`pipChainWriteSet` leg is then sound by
`propagatePipChainCrossCore_confinedToCores` at that state. -/
def endpointCallLiveWriteSet (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) (chainState : SystemState)
    (chainStart : SeLe4n.ThreadId) : List CoreId :=
  endpointCallWriteSet st endpointId executingCore
    ++ pipChainWriteSet chainState chainStart executingCore
        chainState.objectIndex.length

/-- SM8.B.2: the live write set contains the below-API one, so a core outside it
is outside both. The composition rule that makes the union the right premise. -/
theorem endpointCallWriteSet_subset_live (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) (chainState : SystemState) (chainStart : SeLe4n.ThreadId)
    (c : CoreId)
    (h : c ∉ endpointCallLiveWriteSet st endpointId executingCore chainState chainStart) :
    c ∉ endpointCallWriteSet st endpointId executingCore :=
  fun hm => h (List.mem_append.mpr (Or.inl hm))

theorem pipChainWriteSet_subset_live (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) (chainState : SystemState) (chainStart : SeLe4n.ThreadId)
    (c : CoreId)
    (h : c ∉ endpointCallLiveWriteSet st endpointId executingCore chainState chainStart) :
    c ∉ pipChainWriteSet chainState chainStart executingCore
          chainState.objectIndex.length :=
  fun hm => h (List.mem_append.mpr (Or.inr hm))

/-- SM8.B.2: **the composition rule for the live `.call` legs.**

Read the signature literally: `stTrans` and `stDon` are *arbitrary* states and
`hTrans` / `hDonation` are *hypotheses about them*. This is a composition
lemma; on its own it establishes nothing about `endpointCallCrossCoreDispatch`.

It is no longer the end of the story. §5b below discharges those premises from
an actual dispatch result — `endpointCallCrossCoreDispatch_confinedToCores`,
whose write set mirrors the dispatch's own control flow and instantiates this
rule at the resolved receiver and the post-donation state. This theorem is what
that one composes with. -/
theorem endpointCallLive_confinedToCores (st stTrans stDon : SystemState)
    (endpointId : SeLe4n.ObjId) (executingCore : CoreId) (chainStart : SeLe4n.ThreadId)
    (hTrans : observableSlotsConfinedToCores st stTrans
      (endpointCallWriteSet st endpointId executingCore))
    (hDonation : observableSlotsConfinedToCores stTrans stDon []) :
    observableSlotsConfinedToCores st
      (propagatePipChainCrossCore stDon chainStart executingCore
        stDon.objectIndex.length).1
      (endpointCallLiveWriteSet st endpointId executingCore stDon chainStart) :=
  observableSlotsConfinedToCores_trans
    (observableSlotsConfinedToCores_mono
      (by intro c hc; simpa using hc)
      (observableSlotsConfinedToCores_trans hTrans hDonation))
    (propagatePipChainCrossCore_confinedToCores executingCore
      stDon.objectIndex.length stDon chainStart)

end SeLe4n.Kernel
