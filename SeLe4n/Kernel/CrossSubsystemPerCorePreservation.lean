-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.CrossSubsystemPerCore
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Architecture.Invariant
import SeLe4n.Kernel.Capability.Invariant

/-!
# WS-SM SM4.D audit-pass-2 — per-operation cross-subsystem SMP-preservation

This module is the preservation layer of the SM4.D cross-subsystem
migration (plan `docs/planning/SMP_PER_CORE_STATE_PLAN.md` §5.4).  It is
the SM4.D analogue of SM4.C's `Scheduler/Invariant/PerCorePreservation.lean`:
it connects the per-core / `∀ c` SMP invariant *predicates* (landed in the
SM4.D modules) to the kernel's *transitions*, by proving that concrete
cross-subsystem operations preserve the SMP forms.

Each per-operation theorem **reuses the existing single-core preservation
theorem verbatim** and lifts it through:

* a boot-core bridge (`…_perCore_bootCore_iff`), and
* the `…_holds_if_idle` discharge for non-boot cores (§1) — every
  cross-subsystem per-core predicate except `passiveServerIdle` is
  *vacuous* on an idle core (empty run queue / no current thread).

`passiveServerIdle_perCore` is the one exception: its idle-core slice is
NOT vacuous (it reduces to "every unbound thread is passive").  So its
preservation goes through the **`passiveServerIdle_scheduledNowhere`**
natural-SMP form (§3) — "an unbound thread scheduled on no core is
passive" — which is implied *directly* by the single-core
`passiveServerIdle` (stronger hypotheses), giving clean per-op
preservation without any idle hypothesis.  The uniform `∀ c`
`passiveServerIdle_smp` is *stronger* and implies this natural form
(`passiveServerIdle_smp_to_scheduledNowhere`).

The non-boot-idle hypothesis (`∀ c ≠ bootCoreId, …`) is the SM4.B
structural fact (operations write only `bootCoreId`'s scheduler slots, so
non-boot cores keep their default-idle values) — supplied by the caller
(SM5) exactly as in SM4.C's `_smp_of_bootCore_preservation`.

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  `…_holds_if_idle` — per-core predicates are vacuous on an idle core
-- ============================================================================

theorem runnableThreadIpcReady_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hRQ : (st.scheduler.runQueueOnCore c).toList = []) :
    runnableThreadIpcReady_perCore st c := by
  intro tid tcb _ hMem; rw [hRQ] at hMem; exact absurd hMem List.not_mem_nil

theorem blockedOnSendNotRunnable_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hRQ : (st.scheduler.runQueueOnCore c).toList = []) :
    blockedOnSendNotRunnable_perCore st c := by
  intro tid tcb eid _ _; rw [hRQ]; exact List.not_mem_nil

theorem blockedOnReceiveNotRunnable_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hRQ : (st.scheduler.runQueueOnCore c).toList = []) :
    blockedOnReceiveNotRunnable_perCore st c := by
  intro tid tcb eid _ _; rw [hRQ]; exact List.not_mem_nil

theorem blockedOnCallNotRunnable_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hRQ : (st.scheduler.runQueueOnCore c).toList = []) :
    blockedOnCallNotRunnable_perCore st c := by
  intro tid tcb eid _ _; rw [hRQ]; exact List.not_mem_nil

theorem blockedOnReplyNotRunnable_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hRQ : (st.scheduler.runQueueOnCore c).toList = []) :
    blockedOnReplyNotRunnable_perCore st c := by
  intro tid tcb eid rt _ _; rw [hRQ]; exact List.not_mem_nil

theorem blockedOnNotificationNotRunnable_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hRQ : (st.scheduler.runQueueOnCore c).toList = []) :
    blockedOnNotificationNotRunnable_perCore st c := by
  intro tid tcb nid _ _; rw [hRQ]; exact List.not_mem_nil

theorem ipcSchedulerContractPredicates_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hRQ : (st.scheduler.runQueueOnCore c).toList = []) :
    ipcSchedulerContractPredicates_perCore st c :=
  ⟨runnableThreadIpcReady_perCore_holds_if_idle hRQ,
   blockedOnSendNotRunnable_perCore_holds_if_idle hRQ,
   blockedOnReceiveNotRunnable_perCore_holds_if_idle hRQ,
   blockedOnCallNotRunnable_perCore_holds_if_idle hRQ,
   blockedOnReplyNotRunnable_perCore_holds_if_idle hRQ,
   blockedOnNotificationNotRunnable_perCore_holds_if_idle hRQ⟩

theorem currentThreadIpcReady_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hCur : st.scheduler.currentOnCore c = none) :
    currentThreadIpcReady_perCore st c := by
  simp only [currentThreadIpcReady_perCore, hCur]

theorem currentNotEndpointQueueHead_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hCur : st.scheduler.currentOnCore c = none) :
    currentNotEndpointQueueHead_perCore st c := by
  simp only [currentNotEndpointQueueHead_perCore, hCur]

theorem currentNotOnNotificationWaitList_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hCur : st.scheduler.currentOnCore c = none) :
    currentNotOnNotificationWaitList_perCore st c := by
  simp only [currentNotOnNotificationWaitList_perCore, hCur]

theorem currentThreadDequeueCoherent_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hCur : st.scheduler.currentOnCore c = none) :
    currentThreadDequeueCoherent_perCore st c :=
  ⟨currentThreadIpcReady_perCore_holds_if_idle hCur,
   currentNotEndpointQueueHead_perCore_holds_if_idle hCur,
   currentNotOnNotificationWaitList_perCore_holds_if_idle hCur⟩

theorem registerDecodeConsistent_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hCur : st.scheduler.currentOnCore c = none) :
    Architecture.registerDecodeConsistent_perCore st c := by
  intro tid hCurSome; rw [hCur] at hCurSome; exact absurd hCurSome (by simp)

theorem cleanupNoStaleSchedRef_perCore_holds_if_idle {st : SystemState}
    {target : SeLe4n.ObjId} {c : CoreId}
    (hRQ : (st.scheduler.runQueueOnCore c).toList = []) :
    cleanupNoStaleSchedRef_perCore st target c := by
  intro tcb _ hMem
  have hFlat : (st.scheduler.runQueueOnCore c).flat = [] := hRQ
  rw [hFlat] at hMem; exact absurd hMem List.not_mem_nil

theorem schedContextRunQueueConsistent_perCore_holds_if_idle {st : SystemState} {c : CoreId}
    (hRQ : (st.scheduler.runQueueOnCore c).toList = []) :
    schedContextRunQueueConsistent_perCore st c := by
  intro tid hMem; rw [hRQ] at hMem; exact absurd hMem List.not_mem_nil

-- ============================================================================
-- §2  Generic single-core → SMP lifters (the SM5 composition)
-- ============================================================================
--
-- Each lifter takes the live single-core post-state predicate (from the
-- existing single-core preservation theorem) plus the non-boot-idle
-- structural fact, and concludes the `∀ c` SMP form: boot core via the
-- bridge, non-boot cores via `…_holds_if_idle`.

theorem ipcSchedulerContractPredicates_smp_of_singleCore_and_idle {st : SystemState}
    (hSingle : ipcSchedulerContractPredicates st)
    (hIdle : ∀ c, c ≠ bootCoreId → (st.scheduler.runQueueOnCore c).toList = []) :
    ipcSchedulerContractPredicates_smp st := by
  intro c
  by_cases hc : c = bootCoreId
  · subst hc; exact (ipcSchedulerContractPredicates_perCore_bootCore_iff st).mpr hSingle
  · exact ipcSchedulerContractPredicates_perCore_holds_if_idle (hIdle c hc)

theorem currentThreadDequeueCoherent_smp_of_singleCore_and_idle {st : SystemState}
    (hSingle : currentThreadDequeueCoherent st)
    (hIdle : ∀ c, c ≠ bootCoreId → st.scheduler.currentOnCore c = none) :
    currentThreadDequeueCoherent_smp st := by
  intro c
  by_cases hc : c = bootCoreId
  · subst hc; exact (currentThreadDequeueCoherent_perCore_bootCore_iff st).mpr hSingle
  · exact currentThreadDequeueCoherent_perCore_holds_if_idle (hIdle c hc)

theorem registerDecodeConsistent_smp_of_singleCore_and_idle {st : SystemState}
    (hSingle : Architecture.registerDecodeConsistent st)
    (hIdle : ∀ c, c ≠ bootCoreId → st.scheduler.currentOnCore c = none) :
    Architecture.registerDecodeConsistent_smp st := by
  intro c
  by_cases hc : c = bootCoreId
  · subst hc; exact (Architecture.registerDecodeConsistent_perCore_bootCore_iff st).mpr hSingle
  · exact registerDecodeConsistent_perCore_holds_if_idle (hIdle c hc)

theorem schedContextRunQueueConsistent_smp_of_singleCore_and_idle {st : SystemState}
    (hSingle : schedContextRunQueueConsistent st)
    (hIdle : ∀ c, c ≠ bootCoreId → (st.scheduler.runQueueOnCore c).toList = []) :
    (∀ c : CoreId, schedContextRunQueueConsistent_perCore st c) := by
  intro c
  by_cases hc : c = bootCoreId
  · subst hc; exact (schedContextRunQueueConsistent_perCore_bootCore_iff st).mpr hSingle
  · exact schedContextRunQueueConsistent_perCore_holds_if_idle (hIdle c hc)

theorem cleanupNoStaleSchedRef_smp_of_singleCore_and_idle {st : SystemState}
    {target : SeLe4n.ObjId}
    (hSingle : ∀ tcb, st.objects[target]? = some (.tcb tcb) →
      ¬ (tcb.tid ∈ (st.scheduler.runQueueOnCore bootCoreId).flat))
    (hIdle : ∀ c, c ≠ bootCoreId → (st.scheduler.runQueueOnCore c).toList = []) :
    cleanupNoStaleSchedRef_smp st target := by
  intro c
  by_cases hc : c = bootCoreId
  · subst hc; exact (cleanupNoStaleSchedRef_perCore_bootCore_iff st target).mpr hSingle
  · exact cleanupNoStaleSchedRef_perCore_holds_if_idle (hIdle c hc)

-- ============================================================================
-- §3  `passiveServerIdle` natural-SMP form (preservation-friendly)
-- ============================================================================
--
-- `passiveServerIdle_perCore` is NOT vacuous on an idle core (its idle
-- slice reduces to "every unbound thread is passive"), so the `∀ c`
-- `passiveServerIdle_smp` cannot be lifted from the single-core form by
-- the idle discharge.  The natural-SMP form below — "an unbound thread
-- scheduled on no core is passive" — IS implied directly by the
-- single-core `passiveServerIdle` (its hypotheses are stronger), giving
-- clean per-op preservation; and it is implied by the `∀ c` form too.

/-- SM4.D: the natural SMP generalisation of `passiveServerIdle` — an
unbound thread that is in no core's run queue and is no core's current
thread is in a passive state. -/
def passiveServerIdle_scheduledNowhere (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.getTcb? tid = some tcb →
    tcb.schedContextBinding = .unbound →
    (∀ c : CoreId, tid ∉ (st.scheduler.runQueueOnCore c)) →
    (∀ c : CoreId, st.scheduler.currentOnCore c ≠ some tid) →
    (tcb.ipcState = .ready ∨
     ∃ epId, tcb.ipcState = .blockedOnReceive epId ∨
             tcb.ipcState = .blockedOnNotification epId)

/-- SM4.D: the natural-SMP form follows directly from the single-core
`passiveServerIdle` (the natural form's "scheduled nowhere" hypotheses
imply the single-core "not boot-scheduled" hypotheses).  This is the
clean per-op preservation route. -/
theorem passiveServerIdle_scheduledNowhere_of_singleCore {st : SystemState}
    (h : passiveServerIdle st) : passiveServerIdle_scheduledNowhere st := by
  intro tid tcb hTcb hUnbound hNoQ hNoC
  exact h tid tcb ((SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb) hUnbound
    (hNoQ bootCoreId) (hNoC bootCoreId)

/-- SM4.D: the uniform `∀ c` `passiveServerIdle_smp` is stronger than the
natural form and implies it (instantiate the conjunction at `bootCoreId`). -/
theorem passiveServerIdle_smp_to_scheduledNowhere {st : SystemState}
    (h : passiveServerIdle_smp st) : passiveServerIdle_scheduledNowhere st := by
  intro tid tcb hTcb hUnbound hNoQ hNoC
  exact h bootCoreId tid tcb hTcb hUnbound (hNoQ bootCoreId) (hNoC bootCoreId)

theorem default_passiveServerIdle_scheduledNowhere :
    passiveServerIdle_scheduledNowhere (default : SystemState) :=
  passiveServerIdle_smp_to_scheduledNowhere default_passiveServerIdle_smp

/-- SM4.D: clean per-op preservation route for `passiveServerIdle` — any
operation that preserves the single-core `ipcInvariantFull` bundle
preserves the natural-SMP `passiveServerIdle_scheduledNowhere` (extract
`passiveServerIdle` from the bundle, then lift).  SM5 plugs in the op's
existing `…_preserves_ipcInvariantFull` theorem for the post-state. -/
theorem passiveServerIdle_scheduledNowhere_of_ipcInvariantFull {st : SystemState}
    (h : ipcInvariantFull st) : passiveServerIdle_scheduledNowhere st :=
  passiveServerIdle_scheduledNowhere_of_singleCore (ipcInvariantFull.passiveServerIdle h)

-- ============================================================================
-- §4  Concrete per-operation SMP-preservation theorems
-- ============================================================================
--
-- Each reuses the existing single-core preservation theorem verbatim and
-- lifts it via the §2 generic lifter.  The `hNonBootIdle` hypothesis is
-- the SM4.B structural fact (operations write only `bootCoreId`'s
-- scheduler slots); SM5 discharges it from the non-boot cores' default-
-- idle values.

-- §4.1  IPC operations preserve `ipcSchedulerContractPredicates_smp`.

theorem endpointSendDual_preserves_ipcSchedulerContractPredicates_smp
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hPre : ipcSchedulerContractPredicates_smp st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st'))
    (hNonBootIdle : ∀ c, c ≠ bootCoreId → (st'.scheduler.runQueueOnCore c).toList = []) :
    ipcSchedulerContractPredicates_smp st' :=
  ipcSchedulerContractPredicates_smp_of_singleCore_and_idle
    (endpointSendDual_preserves_ipcSchedulerContractPredicates st st' endpointId sender msg
      (ipcSchedulerContractPredicates_smp_to_singleCore st hPre) hObjInv hStep)
    hNonBootIdle

theorem endpointReceiveDual_preserves_ipcSchedulerContractPredicates_smp
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver senderId : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (hPre : ipcSchedulerContractPredicates_smp st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st'))
    (hNonBootIdle : ∀ c, c ≠ bootCoreId → (st'.scheduler.runQueueOnCore c).toList = []) :
    ipcSchedulerContractPredicates_smp st' :=
  ipcSchedulerContractPredicates_smp_of_singleCore_and_idle
    (endpointReceiveDual_preserves_ipcSchedulerContractPredicates st st' endpointId receiver
      senderId replyId (ipcSchedulerContractPredicates_smp_to_singleCore st hPre) hObjInv hStep)
    hNonBootIdle

theorem endpointCall_preserves_ipcSchedulerContractPredicates_smp
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hPre : ipcSchedulerContractPredicates_smp st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st'))
    (hNonBootIdle : ∀ c, c ≠ bootCoreId → (st'.scheduler.runQueueOnCore c).toList = []) :
    ipcSchedulerContractPredicates_smp st' :=
  ipcSchedulerContractPredicates_smp_of_singleCore_and_idle
    (endpointCall_preserves_ipcSchedulerContractPredicates st st' endpointId caller msg
      (ipcSchedulerContractPredicates_smp_to_singleCore st hPre) hObjInv hStep)
    hNonBootIdle

theorem endpointReply_preserves_ipcSchedulerContractPredicates_smp
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hPre : ipcSchedulerContractPredicates_smp st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st'))
    (hNonBootIdle : ∀ c, c ≠ bootCoreId → (st'.scheduler.runQueueOnCore c).toList = []) :
    ipcSchedulerContractPredicates_smp st' :=
  ipcSchedulerContractPredicates_smp_of_singleCore_and_idle
    (endpointReply_preserves_ipcSchedulerContractPredicates st st' replier target msg
      (ipcSchedulerContractPredicates_smp_to_singleCore st hPre) hObjInv hStep)
    hNonBootIdle

theorem endpointReplyRecv_preserves_ipcSchedulerContractPredicates_smp
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId)
    (hPre : ipcSchedulerContractPredicates_smp st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st'))
    (hNonBootIdle : ∀ c, c ≠ bootCoreId → (st'.scheduler.runQueueOnCore c).toList = []) :
    ipcSchedulerContractPredicates_smp st' :=
  ipcSchedulerContractPredicates_smp_of_singleCore_and_idle
    (endpointReplyRecv_preserves_ipcSchedulerContractPredicates st st' endpointId receiver
      replyTarget msg (ipcSchedulerContractPredicates_smp_to_singleCore st hPre) hObjInv replyId hStep)
    hNonBootIdle

theorem notificationSignal_preserves_ipcSchedulerContractPredicates_smp
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hPre : ipcSchedulerContractPredicates_smp st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st'))
    (hNonBootIdle : ∀ c, c ≠ bootCoreId → (st'.scheduler.runQueueOnCore c).toList = []) :
    ipcSchedulerContractPredicates_smp st' :=
  ipcSchedulerContractPredicates_smp_of_singleCore_and_idle
    (notificationSignal_preserves_ipcSchedulerContractPredicates st st' notificationId badge
      (ipcSchedulerContractPredicates_smp_to_singleCore st hPre) hObjInv hStep)
    hNonBootIdle

theorem notificationWait_preserves_ipcSchedulerContractPredicates_smp
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hPre : ipcSchedulerContractPredicates_smp st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st'))
    (hNonBootIdle : ∀ c, c ≠ bootCoreId → (st'.scheduler.runQueueOnCore c).toList = []) :
    ipcSchedulerContractPredicates_smp st' :=
  ipcSchedulerContractPredicates_smp_of_singleCore_and_idle
    (notificationWait_preserves_ipcSchedulerContractPredicates st st' notificationId waiter
      result (ipcSchedulerContractPredicates_smp_to_singleCore st hPre) hObjInv hStep)
    hNonBootIdle

theorem endpointQueueRemoveDual_preserves_ipcSchedulerContractPredicates_smp
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (isSendQ : Bool) (tid : SeLe4n.ThreadId)
    (hPre : ipcSchedulerContractPredicates_smp st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isSendQ tid st = .ok ((), st'))
    (hNonBootIdle : ∀ c, c ≠ bootCoreId → (st'.scheduler.runQueueOnCore c).toList = []) :
    ipcSchedulerContractPredicates_smp st' :=
  ipcSchedulerContractPredicates_smp_of_singleCore_and_idle
    (endpointQueueRemoveDual_preserves_ipcSchedulerContractPredicates st st' endpointId isSendQ
      tid (ipcSchedulerContractPredicates_smp_to_singleCore st hPre) hObjInv hStep)
    hNonBootIdle

-- §4.2  Architecture operations preserve `registerDecodeConsistent_smp`.

theorem advanceTimerState_preserves_registerDecodeConsistent_smp
    (ticks : Nat) (st : SystemState)
    (hPre : Architecture.registerDecodeConsistent_smp st)
    (hNonBootIdle : ∀ c, c ≠ bootCoreId →
      (Architecture.advanceTimerState ticks st).scheduler.currentOnCore c = none) :
    Architecture.registerDecodeConsistent_smp (Architecture.advanceTimerState ticks st) :=
  registerDecodeConsistent_smp_of_singleCore_and_idle
    (Architecture.advanceTimerState_preserves_registerDecodeConsistent ticks st
      (Architecture.registerDecodeConsistent_smp_to_singleCore st hPre))
    hNonBootIdle

theorem writeRegisterState_preserves_registerDecodeConsistent_smp
    (reg : SeLe4n.RegName) (value : SeLe4n.RegValue) (st : SystemState)
    (hPre : Architecture.registerDecodeConsistent_smp st)
    (hNonBootIdle : ∀ c, c ≠ bootCoreId →
      (Architecture.writeRegisterState reg value st).scheduler.currentOnCore c = none) :
    Architecture.registerDecodeConsistent_smp (Architecture.writeRegisterState reg value st) :=
  registerDecodeConsistent_smp_of_singleCore_and_idle
    (Architecture.writeRegisterState_preserves_registerDecodeConsistent reg value st
      (Architecture.registerDecodeConsistent_smp_to_singleCore st hPre))
    hNonBootIdle

-- §4.3  `timerTick` preserves the per-core SchedContext↔run-queue consistency
-- (SM4.C's `schedContextRunQueueConsistent_perCore`, used by the SM4.D capstone).

theorem timerTick_preserves_schedContextRunQueueConsistent_smp
    (st st' : SystemState)
    (hRunnable : st'.scheduler.runnable = st.scheduler.runnable)
    (hObjects : st'.objects = st.objects)
    (hInv : schedContextRunQueueConsistent st)
    (hNonBootIdle : ∀ c, c ≠ bootCoreId → (st'.scheduler.runQueueOnCore c).toList = []) :
    ∀ c : CoreId, schedContextRunQueueConsistent_perCore st' c :=
  schedContextRunQueueConsistent_smp_of_singleCore_and_idle
    (timerTick_preserves_schedContextRunQueueConsistent st st' hRunnable hObjects hInv)
    hNonBootIdle

end SeLe4n.Kernel
