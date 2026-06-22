-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.Defs

/-!
# WS-SM SM4.D — Per-core IPC↔scheduler coherence invariants

This module is the IPC slice of the SM4.D cross-subsystem migration
(plan `docs/planning/SMP_PER_CORE_STATE_PLAN.md` §5.4, sub-tasks
SM4.D.1 / SM4.D.2).  It lifts the IPC↔scheduler coherence predicates
defined in `IPC/Invariant/Defs.lean` from the single-core forms (pinned
to `bootCoreId` after SM4.B) to per-core forms parameterised by an
explicit `(c : CoreId)`, following plan §3.4 Pattern 1: each per-core
form's body is the existing predicate's body with `bootCoreId` → `c`
and `s.scheduler.runnable` → `(s.scheduler.runQueueOnCore c).toList`.

The migration is **additive and soundness-preserving**, exactly as the
SM4.C scheduler-invariant migration: every per-core form at `bootCoreId`
is *equivalent* to the existing single-core predicate (the §2 boot-core
bridges), so the live IPC invariant surface (`ipcSchedulerContractPredicates`,
`currentThreadDequeueCoherent`, `passiveServerIdle`, and the hundreds of
preservation theorems that consume them) is untouched and stays green.
SM4.D strictly *adds* the per-core layer SM5's per-core scheduler consumes.

**AK7 typed-accessor discipline** (matching SM4.C): every per-core
predicate routes its TCB lookups through the typed `getTcb?` accessor
rather than a raw object-store projection keyed by `tid`, so the per-core
layer adds zero `tid`-keyed raw-lookup sites (`RAW_LOOKUP_TID` unchanged)
and grows `GETTCB_ADOPTION`.  The boot-core bridges therefore go through
`getTcb?_eq_some_iff` (the per-core `getTcb?` form is equivalent to the
legacy raw `= some (.tcb …)` object-store form).  The endpoint /
notification predicates keep their raw `objects[oid]?` lookup (an
`ObjId`, not a `tid`-keyed projection, so outside `RAW_LOOKUP_TID`) so
they stay textually parallel to the single-core surface and their bridges
close by `Iff.rfl`.

## What this module provides

For each of the twelve IPC↔scheduler-reading predicates: a per-core form
(`…_perCore`), a boot-core bridge (`…_perCore_bootCore_iff`), a frame
lemma (`…_perCore_frame`: each depends only on core `c`'s `current` /
`runQueue` slot plus `objects`), a default-state witness
(`default_…_perCore`), and the `∀ c` system-wide SMP aggregate
(`…_smp` + `_smp_at` + `_smp_to_singleCore`).  The `∀ c` form is the
genuine SMP generalisation (e.g. a send-blocked thread is not runnable on
*any* core's run queue).

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

/-- Local helper: if two `SystemState`s agree on `objects`, every `getTcb?`
query agrees too (mirrors the SM4.C private helper of the same name). -/
private theorem getTcb?_congr_objects
    {st st' : SystemState} (h : st'.objects = st.objects)
    (tid : SeLe4n.ThreadId) : st'.getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?; rw [h]

/-- Local helper: object-store agreement lifts to `getEndpoint?` agreement. -/
private theorem getEndpoint?_congr_objects
    {st st' : SystemState} (h : st'.objects = st.objects)
    (oid : SeLe4n.ObjId) : st'.getEndpoint? oid = st.getEndpoint? oid := by
  unfold SystemState.getEndpoint?; rw [h]

/-- Local helper: object-store agreement lifts to `getNotification?` agreement. -/
private theorem getNotification?_congr_objects
    {st st' : SystemState} (h : st'.objects = st.objects)
    (oid : SeLe4n.ObjId) : st'.getNotification? oid = st.getNotification? oid := by
  unfold SystemState.getNotification?; rw [h]

-- ============================================================================
-- §1  Per-core predicate forms (plan §3.4 migration pattern)
-- ============================================================================

/-- SM4.D: per-core form of `runnableThreadIpcReady`.  Every TCB in core
`c`'s run queue has `ipcState = .ready`. -/
def runnableThreadIpcReady_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb,
    st.getTcb? tid = some tcb →
    tid ∈ (st.scheduler.runQueueOnCore c).toList → tcb.ipcState = .ready

/-- SM4.D: per-core form of `blockedOnSendNotRunnable`.  A send-blocked
thread is not in core `c`'s run queue. -/
def blockedOnSendNotRunnable_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.getTcb? tid = some tcb → tcb.ipcState = .blockedOnSend endpointId →
    tid ∉ (st.scheduler.runQueueOnCore c).toList

/-- SM4.D: per-core form of `blockedOnReceiveNotRunnable`. -/
def blockedOnReceiveNotRunnable_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.getTcb? tid = some tcb → tcb.ipcState = .blockedOnReceive endpointId →
    tid ∉ (st.scheduler.runQueueOnCore c).toList

/-- SM4.D: per-core form of `blockedOnCallNotRunnable`. -/
def blockedOnCallNotRunnable_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId,
    st.getTcb? tid = some tcb → tcb.ipcState = .blockedOnCall endpointId →
    tid ∉ (st.scheduler.runQueueOnCore c).toList

/-- SM4.D: per-core form of `blockedOnReplyNotRunnable`. -/
def blockedOnReplyNotRunnable_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb endpointId replyTarget,
    st.getTcb? tid = some tcb →
    tcb.ipcState = .blockedOnReply endpointId replyTarget →
    tid ∉ (st.scheduler.runQueueOnCore c).toList

/-- SM4.D: per-core form of `blockedOnNotificationNotRunnable`. -/
def blockedOnNotificationNotRunnable_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) tcb notificationId,
    st.getTcb? tid = some tcb →
    tcb.ipcState = .blockedOnNotification notificationId →
    tid ∉ (st.scheduler.runQueueOnCore c).toList

/-- SM4.D: per-core form of `currentThreadIpcReady`.  Core `c`'s current
thread (if any) has `ipcState = .ready`. -/
def currentThreadIpcReady_perCore (st : SystemState) (c : CoreId) : Prop :=
  match (st.scheduler.currentOnCore c) with
  | none => True
  | some tid => ∀ tcb, st.getTcb? tid = some tcb → tcb.ipcState = .ready

/-- SM4.D: per-core form of `currentNotEndpointQueueHead`.  Core `c`'s
current thread is not the head of any endpoint queue.  Object-store
lookups route through the typed `getEndpoint?` accessor (the AK7
typed-accessor discipline for new code); the boot-core bridge therefore
goes through `getEndpoint?_eq_some_iff`. -/
def currentNotEndpointQueueHead_perCore (st : SystemState) (c : CoreId) : Prop :=
  match (st.scheduler.currentOnCore c) with
  | none => True
  | some tid =>
    ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
      st.getEndpoint? oid = some ep →
      ep.receiveQ.head ≠ some tid ∧ ep.sendQ.head ≠ some tid

/-- SM4.D: per-core form of `currentNotOnNotificationWaitList`.  Core `c`'s
current thread is not on any notification wait list.  Lookups route
through the typed `getNotification?` accessor. -/
def currentNotOnNotificationWaitList_perCore (st : SystemState) (c : CoreId) : Prop :=
  match (st.scheduler.currentOnCore c) with
  | none => True
  | some tid =>
    ∀ (oid : SeLe4n.ObjId) (ntfn : Notification),
      st.getNotification? oid = some ntfn →
      tid ∉ ntfn.waitingThreads

/-- SM4.D: per-core form of `passiveServerIdle`.  An unbound thread that is
not in core `c`'s run queue and not core `c`'s current thread is either
ready, blocked-on-receive/notification (a passive server), or blocked-on-reply
(Finding F-3: a donor that gave up its SchedContext during a Call and awaits
the reply).  Kept in lock-step with the single-core `passiveServerIdle`. -/
def passiveServerIdle_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.getTcb? tid = some tcb →
    tcb.schedContextBinding = .unbound →
    tid ∉ (st.scheduler.runQueueOnCore c) →
    (st.scheduler.currentOnCore c) ≠ some tid →
    (tcb.ipcState = .ready ∨
     (∃ epId, tcb.ipcState = .blockedOnReceive epId ∨
              tcb.ipcState = .blockedOnNotification epId) ∨
     ∃ epId replyTarget, tcb.ipcState = .blockedOnReply epId replyTarget)

-- ----------------------------------------------------------------------------
-- §1.1  Per-core aggregate predicates
-- ----------------------------------------------------------------------------

/-- SM4.D: per-core form of `ipcSchedulerContractPredicates` — the six
runnable↔IPC-blocking-state coherence conjuncts on core `c`. -/
def ipcSchedulerContractPredicates_perCore (st : SystemState) (c : CoreId) : Prop :=
  runnableThreadIpcReady_perCore st c ∧ blockedOnSendNotRunnable_perCore st c ∧
  blockedOnReceiveNotRunnable_perCore st c ∧ blockedOnCallNotRunnable_perCore st c ∧
  blockedOnReplyNotRunnable_perCore st c ∧ blockedOnNotificationNotRunnable_perCore st c

/-- SM4.D: per-core form of `currentThreadDequeueCoherent` — the three
dequeue-on-dispatch coherence conjuncts on core `c`. -/
def currentThreadDequeueCoherent_perCore (st : SystemState) (c : CoreId) : Prop :=
  currentThreadIpcReady_perCore st c ∧ currentNotEndpointQueueHead_perCore st c ∧
  currentNotOnNotificationWaitList_perCore st c

-- ============================================================================
-- §2  Boot-core bridges (the non-orphan connection to the live surface)
-- ============================================================================
--
-- Each per-core form at `bootCoreId` is equivalent to the existing
-- single-core predicate.  The `getTcb?`-using predicates bridge through
-- `getTcb?_eq_some_iff` (the per-core `getTcb? tid = some tcb` form is the
-- legacy raw `= some (.tcb tcb)` object-store form), with `runnable`
-- defeq `(runQueueOnCore bootCoreId).toList`.  The
-- endpoint/notification predicates coincide syntactically and close by
-- `Iff.rfl`.

theorem runnableThreadIpcReady_perCore_bootCore_iff (st : SystemState) :
    runnableThreadIpcReady_perCore st bootCoreId ↔ runnableThreadIpcReady st := by
  unfold runnableThreadIpcReady_perCore runnableThreadIpcReady
  simp only [SystemState.getTcb?_eq_some_iff]

theorem blockedOnSendNotRunnable_perCore_bootCore_iff (st : SystemState) :
    blockedOnSendNotRunnable_perCore st bootCoreId ↔ blockedOnSendNotRunnable st := by
  unfold blockedOnSendNotRunnable_perCore blockedOnSendNotRunnable
  simp only [SystemState.getTcb?_eq_some_iff]

theorem blockedOnReceiveNotRunnable_perCore_bootCore_iff (st : SystemState) :
    blockedOnReceiveNotRunnable_perCore st bootCoreId ↔ blockedOnReceiveNotRunnable st := by
  unfold blockedOnReceiveNotRunnable_perCore blockedOnReceiveNotRunnable
  simp only [SystemState.getTcb?_eq_some_iff]

theorem blockedOnCallNotRunnable_perCore_bootCore_iff (st : SystemState) :
    blockedOnCallNotRunnable_perCore st bootCoreId ↔ blockedOnCallNotRunnable st := by
  unfold blockedOnCallNotRunnable_perCore blockedOnCallNotRunnable
  simp only [SystemState.getTcb?_eq_some_iff]

theorem blockedOnReplyNotRunnable_perCore_bootCore_iff (st : SystemState) :
    blockedOnReplyNotRunnable_perCore st bootCoreId ↔ blockedOnReplyNotRunnable st := by
  unfold blockedOnReplyNotRunnable_perCore blockedOnReplyNotRunnable
  simp only [SystemState.getTcb?_eq_some_iff]

theorem blockedOnNotificationNotRunnable_perCore_bootCore_iff (st : SystemState) :
    blockedOnNotificationNotRunnable_perCore st bootCoreId ↔
      blockedOnNotificationNotRunnable st := by
  unfold blockedOnNotificationNotRunnable_perCore blockedOnNotificationNotRunnable
  simp only [SystemState.getTcb?_eq_some_iff]

theorem currentThreadIpcReady_perCore_bootCore_iff (st : SystemState) :
    currentThreadIpcReady_perCore st bootCoreId ↔ currentThreadIpcReady st := by
  unfold currentThreadIpcReady_perCore currentThreadIpcReady
  cases st.scheduler.currentOnCore bootCoreId with
  | none => exact Iff.rfl
  | some tid => simp only [SystemState.getTcb?_eq_some_iff]

theorem currentNotEndpointQueueHead_perCore_bootCore_iff (st : SystemState) :
    currentNotEndpointQueueHead_perCore st bootCoreId ↔ currentNotEndpointQueueHead st := by
  unfold currentNotEndpointQueueHead_perCore currentNotEndpointQueueHead
  cases st.scheduler.currentOnCore bootCoreId with
  | none => exact Iff.rfl
  | some tid => simp only [SystemState.getEndpoint?_eq_some_iff]

theorem currentNotOnNotificationWaitList_perCore_bootCore_iff (st : SystemState) :
    currentNotOnNotificationWaitList_perCore st bootCoreId ↔
      currentNotOnNotificationWaitList st := by
  unfold currentNotOnNotificationWaitList_perCore currentNotOnNotificationWaitList
  cases st.scheduler.currentOnCore bootCoreId with
  | none => exact Iff.rfl
  | some tid => simp only [SystemState.getNotification?_eq_some_iff]

theorem passiveServerIdle_perCore_bootCore_iff (st : SystemState) :
    passiveServerIdle_perCore st bootCoreId ↔ passiveServerIdle st := by
  unfold passiveServerIdle_perCore passiveServerIdle
  simp only [SystemState.getTcb?_eq_some_iff]

/-- SM4.D: the per-core IPC scheduler-contract aggregate at `bootCoreId`
is the single-core `ipcSchedulerContractPredicates` (each conjunct via
its boot-core bridge). -/
theorem ipcSchedulerContractPredicates_perCore_bootCore_iff (st : SystemState) :
    ipcSchedulerContractPredicates_perCore st bootCoreId ↔
      ipcSchedulerContractPredicates st := by
  unfold ipcSchedulerContractPredicates_perCore ipcSchedulerContractPredicates
  exact and_congr (runnableThreadIpcReady_perCore_bootCore_iff st)
    (and_congr (blockedOnSendNotRunnable_perCore_bootCore_iff st)
      (and_congr (blockedOnReceiveNotRunnable_perCore_bootCore_iff st)
        (and_congr (blockedOnCallNotRunnable_perCore_bootCore_iff st)
          (and_congr (blockedOnReplyNotRunnable_perCore_bootCore_iff st)
            (blockedOnNotificationNotRunnable_perCore_bootCore_iff st)))))

/-- SM4.D: the per-core dequeue-coherence aggregate at `bootCoreId` is the
single-core `currentThreadDequeueCoherent`. -/
theorem currentThreadDequeueCoherent_perCore_bootCore_iff (st : SystemState) :
    currentThreadDequeueCoherent_perCore st bootCoreId ↔
      currentThreadDequeueCoherent st := by
  unfold currentThreadDequeueCoherent_perCore currentThreadDequeueCoherent
  exact and_congr (currentThreadIpcReady_perCore_bootCore_iff st)
    (and_congr (currentNotEndpointQueueHead_perCore_bootCore_iff st)
      (currentNotOnNotificationWaitList_perCore_bootCore_iff st))

-- ============================================================================
-- §3  Frame lemmas (the substantive SM5 content)
-- ============================================================================
--
-- Each per-core IPC↔scheduler predicate on core `c` reads only `objects`
-- (via `getTcb?` / the raw endpoint-notification lookup) plus core `c`'s
-- `runQueue` / `current` slots.  A modification that frames those reads
-- preserves the predicate.  SM5's per-core scheduler discharges the
-- framing hypotheses from the SM4.B `set…OnCore_…OnCore_ne` cross-core
-- independence algebra.

theorem runnableThreadIpcReady_perCore_frame {st st' : SystemState} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c) :
    runnableThreadIpcReady_perCore st' c ↔ runnableThreadIpcReady_perCore st c := by
  unfold runnableThreadIpcReady_perCore
  simp only [getTcb?_congr_objects hObj, hRQ]

theorem blockedOnSendNotRunnable_perCore_frame {st st' : SystemState} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c) :
    blockedOnSendNotRunnable_perCore st' c ↔ blockedOnSendNotRunnable_perCore st c := by
  unfold blockedOnSendNotRunnable_perCore
  simp only [getTcb?_congr_objects hObj, hRQ]

theorem blockedOnReceiveNotRunnable_perCore_frame {st st' : SystemState} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c) :
    blockedOnReceiveNotRunnable_perCore st' c ↔ blockedOnReceiveNotRunnable_perCore st c := by
  unfold blockedOnReceiveNotRunnable_perCore
  simp only [getTcb?_congr_objects hObj, hRQ]

theorem blockedOnCallNotRunnable_perCore_frame {st st' : SystemState} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c) :
    blockedOnCallNotRunnable_perCore st' c ↔ blockedOnCallNotRunnable_perCore st c := by
  unfold blockedOnCallNotRunnable_perCore
  simp only [getTcb?_congr_objects hObj, hRQ]

theorem blockedOnReplyNotRunnable_perCore_frame {st st' : SystemState} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c) :
    blockedOnReplyNotRunnable_perCore st' c ↔ blockedOnReplyNotRunnable_perCore st c := by
  unfold blockedOnReplyNotRunnable_perCore
  simp only [getTcb?_congr_objects hObj, hRQ]

theorem blockedOnNotificationNotRunnable_perCore_frame {st st' : SystemState} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c) :
    blockedOnNotificationNotRunnable_perCore st' c ↔
      blockedOnNotificationNotRunnable_perCore st c := by
  unfold blockedOnNotificationNotRunnable_perCore
  simp only [getTcb?_congr_objects hObj, hRQ]

theorem currentThreadIpcReady_perCore_frame {st st' : SystemState} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :
    currentThreadIpcReady_perCore st' c ↔ currentThreadIpcReady_perCore st c := by
  unfold currentThreadIpcReady_perCore
  rw [hCur]
  cases st.scheduler.currentOnCore c with
  | none => exact Iff.rfl
  | some tid => simp only [getTcb?_congr_objects hObj]

theorem currentNotEndpointQueueHead_perCore_frame {st st' : SystemState} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :
    currentNotEndpointQueueHead_perCore st' c ↔ currentNotEndpointQueueHead_perCore st c := by
  unfold currentNotEndpointQueueHead_perCore
  rw [hCur]
  cases st.scheduler.currentOnCore c with
  | none => exact Iff.rfl
  | some tid => simp only [getEndpoint?_congr_objects hObj]

theorem currentNotOnNotificationWaitList_perCore_frame {st st' : SystemState} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :
    currentNotOnNotificationWaitList_perCore st' c ↔
      currentNotOnNotificationWaitList_perCore st c := by
  unfold currentNotOnNotificationWaitList_perCore
  rw [hCur]
  cases st.scheduler.currentOnCore c with
  | none => exact Iff.rfl
  | some tid => simp only [getNotification?_congr_objects hObj]

theorem passiveServerIdle_perCore_frame {st st' : SystemState} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :
    passiveServerIdle_perCore st' c ↔ passiveServerIdle_perCore st c := by
  unfold passiveServerIdle_perCore
  simp only [getTcb?_congr_objects hObj, hRQ, hCur]

-- ============================================================================
-- §4  Default-state: every core satisfies the per-core invariant at boot
-- ============================================================================
--
-- On the freshly-booted (empty) system every conjunct holds vacuously:
-- the object store is empty (so `getTcb?` is `none` everywhere — the
-- TCB-lookup hypotheses are false), each core's run queue is empty (the
-- `∈ runnable` hypotheses are false / the `∉ runnable` conclusions hold),
-- and each core's `current` is `none`.

/-- Local helper: each core's `current` is `none` on the default state. -/
private theorem default_currentOnCore_none (c : CoreId) :
    (default : SystemState).scheduler.currentOnCore c = none :=
  (default_state_perCoreInitialized c).1

/-- Local helper: each core's run queue is empty on the default state. -/
private theorem default_runQueueOnCore_empty (c : CoreId) :
    (default : SystemState).scheduler.runQueueOnCore c = RunQueue.empty :=
  (default_state_perCoreInitialized c).2.1

/-- Local helper: the default system state's object store is empty (stated
over a generic `ObjId` so the source carries no `tid`-keyed raw-lookup
text). -/
private theorem default_objects_getElem_none (oid : SeLe4n.ObjId) :
    (default : SystemState).objects[oid]? = none := by
  simp only [RHTable_getElem?_eq_get?]
  exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_empty 16 (by omega) oid

/-- Local helper: `getTcb?` is `none` for every thread on the default
state (the object store is empty). -/
private theorem default_getTcb?_none (tid : SeLe4n.ThreadId) :
    (default : SystemState).getTcb? tid = none := by
  unfold SystemState.getTcb?
  rw [default_objects_getElem_none]

theorem default_runnableThreadIpcReady_perCore (c : CoreId) :
    runnableThreadIpcReady_perCore (default : SystemState) c := by
  intro tid tcb _ hMem
  rw [default_runQueueOnCore_empty c, RunQueue.toList_empty] at hMem
  exact absurd hMem (List.not_mem_nil)

theorem default_blockedOnSendNotRunnable_perCore (c : CoreId) :
    blockedOnSendNotRunnable_perCore (default : SystemState) c := by
  intro tid tcb eid _ _
  rw [default_runQueueOnCore_empty c, RunQueue.toList_empty]; exact List.not_mem_nil

theorem default_blockedOnReceiveNotRunnable_perCore (c : CoreId) :
    blockedOnReceiveNotRunnable_perCore (default : SystemState) c := by
  intro tid tcb eid _ _
  rw [default_runQueueOnCore_empty c, RunQueue.toList_empty]; exact List.not_mem_nil

theorem default_blockedOnCallNotRunnable_perCore (c : CoreId) :
    blockedOnCallNotRunnable_perCore (default : SystemState) c := by
  intro tid tcb eid _ _
  rw [default_runQueueOnCore_empty c, RunQueue.toList_empty]; exact List.not_mem_nil

theorem default_blockedOnReplyNotRunnable_perCore (c : CoreId) :
    blockedOnReplyNotRunnable_perCore (default : SystemState) c := by
  intro tid tcb eid rt _ _
  rw [default_runQueueOnCore_empty c, RunQueue.toList_empty]; exact List.not_mem_nil

theorem default_blockedOnNotificationNotRunnable_perCore (c : CoreId) :
    blockedOnNotificationNotRunnable_perCore (default : SystemState) c := by
  intro tid tcb nid _ _
  rw [default_runQueueOnCore_empty c, RunQueue.toList_empty]; exact List.not_mem_nil

theorem default_currentThreadIpcReady_perCore (c : CoreId) :
    currentThreadIpcReady_perCore (default : SystemState) c := by
  simp only [currentThreadIpcReady_perCore, default_currentOnCore_none c]

theorem default_currentNotEndpointQueueHead_perCore (c : CoreId) :
    currentNotEndpointQueueHead_perCore (default : SystemState) c := by
  simp only [currentNotEndpointQueueHead_perCore, default_currentOnCore_none c]

theorem default_currentNotOnNotificationWaitList_perCore (c : CoreId) :
    currentNotOnNotificationWaitList_perCore (default : SystemState) c := by
  simp only [currentNotOnNotificationWaitList_perCore, default_currentOnCore_none c]

theorem default_passiveServerIdle_perCore (c : CoreId) :
    passiveServerIdle_perCore (default : SystemState) c := by
  intro tid tcb hTcb _ _ _
  rw [default_getTcb?_none] at hTcb
  exact absurd hTcb (by simp)

theorem default_ipcSchedulerContractPredicates_perCore (c : CoreId) :
    ipcSchedulerContractPredicates_perCore (default : SystemState) c :=
  ⟨default_runnableThreadIpcReady_perCore c, default_blockedOnSendNotRunnable_perCore c,
   default_blockedOnReceiveNotRunnable_perCore c, default_blockedOnCallNotRunnable_perCore c,
   default_blockedOnReplyNotRunnable_perCore c, default_blockedOnNotificationNotRunnable_perCore c⟩

theorem default_currentThreadDequeueCoherent_perCore (c : CoreId) :
    currentThreadDequeueCoherent_perCore (default : SystemState) c :=
  ⟨default_currentThreadIpcReady_perCore c, default_currentNotEndpointQueueHead_perCore c,
   default_currentNotOnNotificationWaitList_perCore c⟩

-- ============================================================================
-- §5  System-wide SMP aggregates (∀ c) + per-conjunct projections
-- ============================================================================
--
-- The `∀ c` form is the genuine SMP generalisation: each property holds
-- on *every* core's run-queue / current slot.  For the IPC↔scheduler
-- predicates this is exactly the right SMP semantics (e.g. a send-blocked
-- thread must not be runnable on *any* core).  `_smp_to_singleCore`
-- recovers the live single-core surface via the boot-core bridge; the
-- reverse direction needs SM5's per-core idleness witnesses.

/-- SM4.D: system-wide SMP form of the IPC scheduler-contract aggregate. -/
def ipcSchedulerContractPredicates_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, ipcSchedulerContractPredicates_perCore st c

/-- SM4.D: system-wide SMP form of dequeue-on-dispatch coherence. -/
def currentThreadDequeueCoherent_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, currentThreadDequeueCoherent_perCore st c

/-- SM4.D: system-wide SMP form of `passiveServerIdle` (an unbound thread
not scheduled on any core is passive). -/
def passiveServerIdle_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, passiveServerIdle_perCore st c

theorem ipcSchedulerContractPredicates_smp_aggregateForall (st : SystemState) :
    (∀ c : CoreId, ipcSchedulerContractPredicates_perCore st c) ↔
      ipcSchedulerContractPredicates_smp st := Iff.rfl

theorem currentThreadDequeueCoherent_smp_aggregateForall (st : SystemState) :
    (∀ c : CoreId, currentThreadDequeueCoherent_perCore st c) ↔
      currentThreadDequeueCoherent_smp st := Iff.rfl

theorem passiveServerIdle_smp_aggregateForall (st : SystemState) :
    (∀ c : CoreId, passiveServerIdle_perCore st c) ↔ passiveServerIdle_smp st := Iff.rfl

theorem ipcSchedulerContractPredicates_smp_at (st : SystemState) (c : CoreId)
    (h : ipcSchedulerContractPredicates_smp st) :
    ipcSchedulerContractPredicates_perCore st c := h c

theorem currentThreadDequeueCoherent_smp_at (st : SystemState) (c : CoreId)
    (h : currentThreadDequeueCoherent_smp st) :
    currentThreadDequeueCoherent_perCore st c := h c

theorem passiveServerIdle_smp_at (st : SystemState) (c : CoreId)
    (h : passiveServerIdle_smp st) : passiveServerIdle_perCore st c := h c

/-- SM4.D: the SMP IPC scheduler-contract implies the live single-core
`ipcSchedulerContractPredicates` (instantiate at `bootCoreId` + bridge). -/
theorem ipcSchedulerContractPredicates_smp_to_singleCore (st : SystemState)
    (h : ipcSchedulerContractPredicates_smp st) : ipcSchedulerContractPredicates st :=
  (ipcSchedulerContractPredicates_perCore_bootCore_iff st).mp (h bootCoreId)

theorem currentThreadDequeueCoherent_smp_to_singleCore (st : SystemState)
    (h : currentThreadDequeueCoherent_smp st) : currentThreadDequeueCoherent st :=
  (currentThreadDequeueCoherent_perCore_bootCore_iff st).mp (h bootCoreId)

theorem passiveServerIdle_smp_to_singleCore (st : SystemState)
    (h : passiveServerIdle_smp st) : passiveServerIdle st :=
  (passiveServerIdle_perCore_bootCore_iff st).mp (h bootCoreId)

/-- SM4.D: the natural SMP reading of `passiveServerIdle_smp` proved as a
theorem.  An unbound thread that is scheduled on **no** core — not in any
core's run queue, not current on any core — is in a passive state
(`ready` / `blockedOnReceive` / `blockedOnNotification` / `blockedOnReply`).

`passiveServerIdle_smp` (the per-core conjunction `∀ c, passiveServerIdle_perCore`)
is *stronger* than this statement — each core's slice independently
constrains threads under weaker per-core hypotheses — so the natural
"not scheduled anywhere" reading is a genuine consequence, derived here by
instantiating the conjunction at `bootCoreId`.  This makes the documented
intuition a machine-checked theorem rather than prose.  (Finding F-3: the
passive states now include `.blockedOnReply` — a donor that gave up its
SchedContext during a Call and is descheduled while awaiting the reply.) -/
theorem passiveServerIdle_smp_not_scheduled_anywhere {st : SystemState}
    (h : passiveServerIdle_smp st)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb)
    (hUnbound : tcb.schedContextBinding = .unbound)
    (hNoQueue : ∀ c : CoreId, tid ∉ (st.scheduler.runQueueOnCore c))
    (hNoCurrent : ∀ c : CoreId, st.scheduler.currentOnCore c ≠ some tid) :
    tcb.ipcState = .ready ∨
      (∃ epId, tcb.ipcState = .blockedOnReceive epId ∨
               tcb.ipcState = .blockedOnNotification epId) ∨
      ∃ epId replyTarget, tcb.ipcState = .blockedOnReply epId replyTarget :=
  h bootCoreId tid tcb hTcb hUnbound (hNoQueue bootCoreId) (hNoCurrent bootCoreId)

theorem default_ipcSchedulerContractPredicates_smp :
    ipcSchedulerContractPredicates_smp (default : SystemState) :=
  fun c => default_ipcSchedulerContractPredicates_perCore c

theorem default_currentThreadDequeueCoherent_smp :
    currentThreadDequeueCoherent_smp (default : SystemState) :=
  fun c => default_currentThreadDequeueCoherent_perCore c

theorem default_passiveServerIdle_smp :
    passiveServerIdle_smp (default : SystemState) :=
  fun c => default_passiveServerIdle_perCore c

-- Per-conjunct projections from the per-core aggregates (cheap accessors).

theorem ipcSchedulerContractPredicates_perCore_to_runnableThreadIpcReady
    {st : SystemState} {c : CoreId} (h : ipcSchedulerContractPredicates_perCore st c) :
    runnableThreadIpcReady_perCore st c := h.1

theorem ipcSchedulerContractPredicates_perCore_to_blockedOnSendNotRunnable
    {st : SystemState} {c : CoreId} (h : ipcSchedulerContractPredicates_perCore st c) :
    blockedOnSendNotRunnable_perCore st c := h.2.1

theorem ipcSchedulerContractPredicates_perCore_to_blockedOnReceiveNotRunnable
    {st : SystemState} {c : CoreId} (h : ipcSchedulerContractPredicates_perCore st c) :
    blockedOnReceiveNotRunnable_perCore st c := h.2.2.1

theorem ipcSchedulerContractPredicates_perCore_to_blockedOnCallNotRunnable
    {st : SystemState} {c : CoreId} (h : ipcSchedulerContractPredicates_perCore st c) :
    blockedOnCallNotRunnable_perCore st c := h.2.2.2.1

theorem ipcSchedulerContractPredicates_perCore_to_blockedOnReplyNotRunnable
    {st : SystemState} {c : CoreId} (h : ipcSchedulerContractPredicates_perCore st c) :
    blockedOnReplyNotRunnable_perCore st c := h.2.2.2.2.1

theorem ipcSchedulerContractPredicates_perCore_to_blockedOnNotificationNotRunnable
    {st : SystemState} {c : CoreId} (h : ipcSchedulerContractPredicates_perCore st c) :
    blockedOnNotificationNotRunnable_perCore st c := h.2.2.2.2.2

theorem currentThreadDequeueCoherent_perCore_to_currentThreadIpcReady
    {st : SystemState} {c : CoreId} (h : currentThreadDequeueCoherent_perCore st c) :
    currentThreadIpcReady_perCore st c := h.1

theorem currentThreadDequeueCoherent_perCore_to_currentNotEndpointQueueHead
    {st : SystemState} {c : CoreId} (h : currentThreadDequeueCoherent_perCore st c) :
    currentNotEndpointQueueHead_perCore st c := h.2.1

theorem currentThreadDequeueCoherent_perCore_to_currentNotOnNotificationWaitList
    {st : SystemState} {c : CoreId} (h : currentThreadDequeueCoherent_perCore st c) :
    currentNotOnNotificationWaitList_perCore st c := h.2.2

end SeLe4n.Kernel
