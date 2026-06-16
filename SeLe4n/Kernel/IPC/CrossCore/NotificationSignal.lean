-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.B: PRODUCTION (LANDED).  `notificationSignalOnCore` entered the
-- production import closure when the live bound-aware `.notificationSignal`
-- dispatch (`API.dispatchWithCap{,Checked}` →
-- `notificationSignalBoundCrossCoreDispatch{,Checked}`) was wired through it.
-- (Former "STATUS: staged" marker replaced with this landing note per the
-- implement-the-improvement rule; see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md §3.1, §5.)

import SeLe4n.Kernel.IPC.CrossCore.EndpointCall

/-!
# WS-SM SM6.B — Notification across cores

This module is the SM6.B deliverable of the WS-SM Phase 6 cross-core IPC
workstream (plan `docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.1, §5).  It lifts
the single-core notification syscalls to *cross-core* transitions under the
SM3.B per-object lock-set discipline:

* **`notificationSignalOnCore`** — the cross-core generalisation of
  `notificationSignal`.  On a signal that unblocks a waiter, the waiter wake is
  routed through the SM5.C cross-core `wakeThread` (so a waiter bound to a
  *remote* core is enqueued on that core and a `.reschedule` SGI is surfaced for
  the runtime to fire — plan SM6.B.2 `notificationSignal_remote_wake`).  The
  signaller does **not** block, so no per-core deschedule occurs.
* **`notificationWaitOnCore`** — the cross-core generalisation of
  `notificationWait`.  On the block path the caller is removed from *its own*
  core via the SM6.A `removeRunnableOnCore … executingCore` generalisation of
  `removeRunnable`.

The single-core forms (in `IPC.Operations.Endpoint`) remain the canonical
bootCore semantics; these cross-core transitions substitute only the scheduler
placement of the woken waiter / blocked caller, exactly as SM6.A's
`endpointCallOnCore` does for the endpoint-call rendezvous.  The lock-set
footprints `lockSet_notificationSignal` / `lockSet_notificationWait` (SM3.B.3)
are unchanged; this module proves the SM6.B theorems the runtime `withLockSet`
bracket consumes.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  The cross-core notification-signal transition (plan §3.1)
-- ============================================================================

/-- WS-SM SM6.B.1 (plan §3.1): notification signal across cores.

Mirrors the single-core `notificationSignal`, with one cross-core substitution:
on a signal that unblocks the head waiter, the waiter is woken through the SM5.C
`wakeThread … executingCore`, which enqueues it on its *home* core
(`determineTargetCore`) and returns `some (target, .reschedule)` when that core
differs from `executingCore` (the cross-core poke the runtime fires).  The
signaller is *not* descheduled (signal is non-blocking from its perspective).

Returns the post-state paired with `Except KernelError (Option (CoreId ×
SgiKind))`: an error on a failed step (pre-state returned, so a `withLockSet`
bracket still releases cleanly), or `.ok sgi?` with the optional cross-core SGI
to emit after the state commit. -/
def notificationSignalOnCore (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  match st.getNotification? notificationId with
  | some ntfn =>
      match ntfn.waitingThreads.tail? with
      | some (waiter, rest) =>
          let nextState : NotificationState := if rest.val.isEmpty then .idle else .waiting
          -- WS-SM SM6.B: carry `boundTCB := ntfn.boundTCB` so an ordinary signal
          -- preserves the notification ↔ TCB binding; a fresh record (boundTCB
          -- defaulting to `none`) would silently destroy it on every signal.
          let ntfn' : Notification := {
            state := nextState
            waitingThreads := rest
            pendingBadge := none
            boundTCB := ntfn.boundTCB
          }
          match storeObject notificationId (.notification ntfn') st with
          | .error e => (st, .error e)
          | .ok ((), st') =>
              let badgeMsg : IpcMessage := { IpcMessage.empty with badge := some badge }
              match storeTcbIpcStateAndMessage st' waiter .ready (some badgeMsg) with
              | .error e => (st, .error e)
              | .ok st'' =>
                  -- Cross-core waiter wake (SM5.C): route to the waiter's home
                  -- core, capturing the optional `.reschedule` SGI.
                  ((wakeThread st'' waiter executingCore).1,
                   .ok (wakeThread st'' waiter executingCore).2)
      | none =>
          -- WS-F5/D1c: word-bounded Badge.bor accumulation (mirrors single-core).
          let mergedBadge : SeLe4n.Badge :=
            match ntfn.pendingBadge with
            | some existing => SeLe4n.Badge.bor existing badge
            | none => SeLe4n.Badge.ofNatMasked badge.toNat
          let ntfn' : Notification := {
            state := .active
            waitingThreads := SeLe4n.NoDupList.empty
            pendingBadge := some mergedBadge
            boundTCB := ntfn.boundTCB
          }
          match storeObject notificationId (.notification ntfn') st with
          | .error e => (st, .error e)
          | .ok ((), st') => (st', .ok none)
  | none =>
      -- Typed-accessor dispatch (AK7 cascade discipline): `getNotification?` is
      -- `none` for both an absent object and a wrong-kinded one.  Recover the
      -- single-core error distinction without a raw object-store variant match: a
      -- present-but-wrong-kind object fails with `.invalidCapability`, a genuinely
      -- absent one with `.objectNotFound`.
      if (st.objects[notificationId]?).isSome then (st, .error .invalidCapability)
      else (st, .error .objectNotFound)

/-- WS-SM SM6.B.1 (plan §3.1): notification wait across cores.

Mirrors the single-core `notificationWait`, with one cross-core substitution: on
the block path (no pending badge) the caller is removed from *its own* core's run
queue/current via `removeRunnableOnCore … executingCore` (the SM6.A
generalisation of `removeRunnable`).  The badge-consume path keeps the caller
runnable, so it makes no scheduler change.  No cross-core SGI is ever surfaced —
a wait pokes no other core.

Returns the post-state paired with `Except KernelError (Option Badge)`: the
consumed badge (`some badge` on the badge path, `none` on the block path), or an
error (pre-state returned). -/
def notificationWaitOnCore (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option SeLe4n.Badge) :=
  match st.getNotification? notificationId with
  | some ntfn =>
      match ntfn.pendingBadge with
      | some badge =>
          let ntfn' : Notification :=
            { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none, boundTCB := ntfn.boundTCB }
          match storeObject notificationId (.notification ntfn') st with
          | .error e => (st, .error e)
          | .ok ((), st') =>
              match storeTcbIpcState st' waiter .ready with
              | .error e => (st, .error e)
              | .ok st'' => (st'', .ok (some badge))
      | none =>
          match lookupTcb st waiter with
          | none => (st, .error .objectNotFound)
          | some tcb =>
              if tcb.ipcState = .blockedOnNotification notificationId then
                (st, .error .alreadyWaiting)
              else
                match ntfn.waitingThreads.consWithGuard? waiter with
                | none => (st, .error .alreadyWaiting)
                | some wt' =>
                    let ntfn' : Notification := {
                      state := .waiting
                      waitingThreads := wt'
                      pendingBadge := none
                      boundTCB := ntfn.boundTCB
                    }
                    match storeObject notificationId (.notification ntfn') st with
                    | .error e => (st, .error e)
                    | .ok ((), st') =>
                        match storeTcbIpcState_fromTcb st' waiter tcb
                            (.blockedOnNotification notificationId) with
                        | .error e => (st, .error e)
                        | .ok st'' => (removeRunnableOnCore st'' waiter executingCore, .ok none)
  | none =>
      -- Typed-accessor dispatch (AK7 cascade discipline) — same wrong-kind vs
      -- absent recovery as `notificationSignalOnCore`.
      if (st.objects[notificationId]?).isSome then (st, .error .invalidCapability)
      else (st, .error .objectNotFound)

-- ============================================================================
-- §2  Pre-resolution helpers + state-resolved lock-sets (plan §3.1)
-- ============================================================================

/-- WS-SM SM6.B.1: the waiter a cross-core signal would wake — the head of the
notification's waiter list, if any.  Pre-resolved from the pre-state so the
signaller can assemble the `lockSet_notificationSignal` footprint (the waiter TCB
write lock is present iff a waiter is blocked). -/
def notificationSignalWaiter? (st : SystemState) (notificationId : SeLe4n.ObjId) :
    Option SeLe4n.ThreadId :=
  match st.getNotification? notificationId with
  | some ntfn => ntfn.waitingThreads.head?
  | none => none

/-- WS-SM SM6.B.1: the concrete lock-set a cross-core `notificationSignalOnCore`
on state `st` acquires — `lockSet_notificationSignal` with the woken waiter
**pre-resolved from `st`** via `notificationSignalWaiter?` (the notification's
waiter-list head).  This is the footprint the runtime `withLockSet` bracket
acquires before invoking `notificationSignalOnCore`. -/
def lockSet_notificationSignalOnCore (st : SystemState) (notificationId : SeLe4n.ObjId)
    (signaller : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId) : LockSet :=
  lockSet_notificationSignal signaller cnodeRootObjId notificationId
    (notificationSignalWaiter? st notificationId)

/-- WS-SM SM6.B.1: the concrete lock-set a cross-core `notificationWaitOnCore`
on state `st` acquires — `lockSet_notificationWait` (caller TCB write, CNode
read, notification write).  The wait footprint is independent of the pre-state
(no optional members), so this is a thin alias kept for symmetry with
`lockSet_notificationSignalOnCore`. -/
def lockSet_notificationWaitOnCore (notificationId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId) : LockSet :=
  lockSet_notificationWait caller cnodeRootObjId notificationId

-- ============================================================================
-- §3  Path reduction lemmas (full characterisation of each control path)
-- ============================================================================

/-- WS-SM SM6.B.1: full reduction of the **waiter** path (a waiter is blocked on
the notification).  The post-state is the badge-delivered, waiter-woken
(cross-core) state; the surfaced SGI is exactly the waiter wake's. -/
theorem notificationSignalOnCore_waiter_eq
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification)
    (waiter : SeLe4n.ThreadId) (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest))
    (hStore : storeObject notificationId (.notification
        { state := if rest.val.isEmpty then .idle else .waiting,
          waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hMsg : storeTcbIpcStateAndMessage st' waiter .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st'') :
    notificationSignalOnCore notificationId badge executingCore st
      = ((wakeThread st'' waiter executingCore).1,
         .ok (wakeThread st'' waiter executingCore).2) := by
  unfold notificationSignalOnCore
  have hObjN : st.getNotification? notificationId = some ntfn :=
    (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mpr hObj
  simp only [hObjN, hWaiters, hStore, hMsg]

/-- WS-SM SM6.B.1: full reduction of the **no-waiter** path (the signal merges
its badge into the notification's pending badge).  No wake occurs, so no SGI is
surfaced. -/
theorem notificationSignalOnCore_noWaiter_eq
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification) (st' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = none)
    (hStore : storeObject notificationId (.notification
        { state := .active, waitingThreads := SeLe4n.NoDupList.empty,
          pendingBadge := some (match ntfn.pendingBadge with
            | some existing => SeLe4n.Badge.bor existing badge
            | none => SeLe4n.Badge.ofNatMasked badge.toNat), boundTCB := ntfn.boundTCB }) st = .ok ((), st')) :
    notificationSignalOnCore notificationId badge executingCore st = (st', .ok none) := by
  unfold notificationSignalOnCore
  have hObjN : st.getNotification? notificationId = some ntfn :=
    (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mpr hObj
  simp only [hObjN, hWaiters, hStore]

-- ============================================================================
-- §4  SM6.B.2 — Cross-core waiter wake: SGI emission
-- ============================================================================

/-- WS-SM SM6.B.2 (`notificationSignal_remote_wake`).  When a cross-core
notification signal unblocks a waiter whose home core differs from the executing
core, the operation surfaces a `.reschedule` SGI targeting the waiter's core —
the cross-core poke the runtime fires after the state commit.  The target core is
the waiter's home core `determineTargetCore … waiter` (its `cpuAffinity`), read
at the wake site `st''`; the intervening notification-store + TCB-store mutate
only the notification object and the waiter's `ipcState` / `pendingMessage`,
never its `cpuAffinity`, so this is the same core the plan's pre-state target
names. -/
theorem notificationSignalOnCore_remote_wake
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification)
    (waiter : SeLe4n.ThreadId) (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (waiterTcb'' : TCB) (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest))
    (hStore : storeObject notificationId (.notification
        { state := if rest.val.isEmpty then .idle else .waiting,
          waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hMsg : storeTcbIpcStateAndMessage st' waiter .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st'')
    (hTcb'' : st''.getTcb? waiter = some waiterTcb'')
    (hRemote : determineTargetCore st'' waiter ≠ executingCore) :
    (notificationSignalOnCore notificationId badge executingCore st).2
      = .ok (some (determineTargetCore st'' waiter, SgiKind.reschedule)) := by
  rw [notificationSignalOnCore_waiter_eq notificationId badge executingCore st ntfn
        waiter rest st' st'' hObj hWaiters hStore hMsg]
  show Except.ok (wakeThread st'' waiter executingCore).2
      = Except.ok (some (determineTargetCore st'' waiter, SgiKind.reschedule))
  rw [wakeThread_emits_sgi_if_remote st'' waiter executingCore waiterTcb'' hTcb'' hRemote]

/-- WS-SM SM6.B.2: dually, a cross-core signal whose waiter is *local* (home core
= executing core) surfaces **no** SGI — the local scheduler picks the
newly-runnable waiter up on its next decision. -/
theorem notificationSignalOnCore_no_sgi_if_local_waiter
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification)
    (waiter : SeLe4n.ThreadId) (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest))
    (hStore : storeObject notificationId (.notification
        { state := if rest.val.isEmpty then .idle else .waiting,
          waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hMsg : storeTcbIpcStateAndMessage st' waiter .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st'')
    (hLocal : determineTargetCore st'' waiter = executingCore) :
    (notificationSignalOnCore notificationId badge executingCore st).2 = .ok none := by
  rw [notificationSignalOnCore_waiter_eq notificationId badge executingCore st ntfn
        waiter rest st' st'' hObj hWaiters hStore hMsg]
  show Except.ok (wakeThread st'' waiter executingCore).2 = Except.ok none
  rw [wakeThread_no_sgi_if_local st'' waiter executingCore hLocal]

/-- WS-SM SM6.B.2: the **no-waiter** path (the signal merges its badge into the
notification's pending badge) surfaces no SGI — no thread is woken, so there is
no cross-core poke.  Completes the SGI characterisation: a signal pokes a remote
core *only* when it wakes a waiter bound to that remote core. -/
theorem notificationSignalOnCore_noWaiter_no_sgi
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification) (st' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = none)
    (hStore : storeObject notificationId (.notification
        { state := .active, waitingThreads := SeLe4n.NoDupList.empty,
          pendingBadge := some (match ntfn.pendingBadge with
            | some existing => SeLe4n.Badge.bor existing badge
            | none => SeLe4n.Badge.ofNatMasked badge.toNat), boundTCB := ntfn.boundTCB }) st = .ok ((), st')) :
    (notificationSignalOnCore notificationId badge executingCore st).2 = .ok none := by
  rw [notificationSignalOnCore_noWaiter_eq notificationId badge executingCore st ntfn st'
        hObj hWaiters hStore]

-- ============================================================================
-- §5  SM6.B.1 — Lock-set correctness (`.notificationSignal` / `.notificationWait`)
-- ============================================================================

/-- WS-SM SM6.B.1: the `notificationSignal` lock-set is **hierarchically
correct** — every lock it declares has a kind in `permittedKinds
.notificationSignal` (so the acquisitions respect the SM0.I lock ladder), and its
keys are duplicate-free (the SM3.B well-formedness `LockSet` carries by
construction).  Together these are the structural soundness conditions the
deadlock-freedom theorem (2.1.9) and the 2PL serializability corollary (2.1.11)
consume. -/
theorem notificationSignalOnCore_lockSet_correct
    (signaller : SeLe4n.ThreadId) (cnRoot notificationId : SeLe4n.ObjId)
    (waiter? : Option SeLe4n.ThreadId) :
    (∀ p ∈ (lockSet_notificationSignal signaller cnRoot notificationId waiter?).pairs,
        p.fst.kind ∈ permittedKinds .notificationSignal) ∧
    ((lockSet_notificationSignal signaller cnRoot notificationId waiter?).pairs.map
        (·.fst)).Nodup :=
  ⟨lockSet_consistent_notificationSignal signaller cnRoot notificationId waiter?,
   (lockSet_notificationSignal signaller cnRoot notificationId waiter?).hUniqueKeys⟩

/-- WS-SM SM6.B.1: the **state-resolved** signal lock-set
(`lockSet_notificationSignalOnCore`, with the waiter pre-resolved from `st`) is
hierarchically correct — every lock it declares has a kind permitted for
`.notificationSignal`.  This is the form the runtime acquisition consumes, so its
correctness is a corollary of the parametric `lockSet_consistent_notificationSignal`. -/
theorem lockSet_notificationSignalOnCore_correct
    (st : SystemState) (notificationId : SeLe4n.ObjId) (signaller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) :
    ∀ p ∈ (lockSet_notificationSignalOnCore st notificationId signaller cnodeRootObjId).pairs,
      p.fst.kind ∈ permittedKinds .notificationSignal :=
  lockSet_consistent_notificationSignal signaller cnodeRootObjId notificationId
    (notificationSignalWaiter? st notificationId)

/-- WS-SM SM6.B.1: the `notificationWait` lock-set is hierarchically correct —
every declared lock has a kind in `permittedKinds .notificationWait`, and its keys
are duplicate-free.  The wait footprint has no optional members (caller TCB write,
CNode read, notification write), so this is the full structural soundness of the
wait acquisition. -/
theorem notificationWaitOnCore_lockSet_correct
    (caller : SeLe4n.ThreadId) (cnRoot notificationId : SeLe4n.ObjId) :
    (∀ p ∈ (lockSet_notificationWait caller cnRoot notificationId).pairs,
        p.fst.kind ∈ permittedKinds .notificationWait) ∧
    ((lockSet_notificationWait caller cnRoot notificationId).pairs.map (·.fst)).Nodup :=
  ⟨lockSet_consistent_notificationWait caller cnRoot notificationId,
   (lockSet_notificationWait caller cnRoot notificationId).hUniqueKeys⟩

-- ============================================================================
-- §6  SM6.B.6 — Notification ↔ TCB binding under the lock-set (membership)
-- ============================================================================

/-- A **write**-mode `insertOrMerge` always leaves its key write-locked: on the
fresh branch the `(l, .write)` pair is prepended; on the merge branch the
existing entry is replaced by `(l, oldMode.lub .write) = (l, .write)` (write is
the `AccessMode.lub` top).  So `(l, .write)` is a member of the result
unconditionally — the structural fact behind "both ends of the signal binding are
write-locked". -/
theorem self_write_mem_insertOrMerge (S : LockSet) (l : LockId) :
    (l, AccessMode.write) ∈ (S.insertOrMerge l AccessMode.write).pairs := by
  unfold LockSet.insertOrMerge
  split
  · rename_i hc
    rw [LockSet.containsKey, List.any_eq_true] at hc
    obtain ⟨p, hpmem, hpfst⟩ := hc
    have hEq : p.fst = l := of_decide_eq_true hpfst
    exact List.mem_map.mpr ⟨p, hpmem, by rw [if_pos hEq, AccessMode.lub_write_right]⟩
  · exact List.mem_cons.mpr (Or.inl rfl)

/-- WS-SM SM6.B.6 (binding under lock-set, notification end): the **notification
write lock** — under which the signal mutates the notification's waiter list /
pending badge — is a declared member of the `notificationSignal` lock-set
footprint, present whether or not a waiter is woken.  Together with
`notificationSignalOnCore_lockSet_correct` this is one half of "the notification ↔
TCB binding is held under lock": the notification end. -/
theorem lockSet_notificationSignal_notification_write_mem
    (signaller : SeLe4n.ThreadId) (cnRoot notificationId : SeLe4n.ObjId)
    (waiter? : Option SeLe4n.ThreadId) :
    (notificationLock notificationId, AccessMode.write)
      ∈ (lockSet_notificationSignal signaller cnRoot notificationId waiter?).pairs := by
  -- Base: the notification lock is the outermost `insertOrMerge` of the list.
  have hBase : (notificationLock notificationId, AccessMode.write)
      ∈ (lockSetOfList [(tcbLock signaller, .read), (cnodeLock cnRoot, .read),
            (notificationLock notificationId, .write)]).pairs := by
    show (notificationLock notificationId, AccessMode.write)
      ∈ (((LockSet.empty.insertOrMerge (tcbLock signaller) .read).insertOrMerge
          (cnodeLock cnRoot) .read).insertOrMerge (notificationLock notificationId)
          AccessMode.write).pairs
    exact self_write_mem_insertOrMerge _ (notificationLock notificationId)
  -- The optional waiter extension (a distinct TCB-kind lock) preserves it.
  unfold lockSet_notificationSignal
  cases hw : waiter? with
  | none => simp only [lockSetExtendOpt, Option.map_none]; exact hBase
  | some wt =>
    simp only [lockSetExtendOpt, Option.map_some]
    refine mem_insertOrMerge_of_mem_of_ne _ _ _ _ hBase ?_
    show notificationLock notificationId ≠ tcbLock wt
    intro h; simp [notificationLock, tcbLock] at h

/-- WS-SM SM6.B.6 (binding under lock-set, TCB end): the **woken waiter's TCB
write lock** — under which the signal writes the waiter's `ipcState := .ready` and
enqueues it on its home core — is a declared member of the `notificationSignal`
lock-set footprint whenever a waiter is present.  Together with
`lockSet_notificationSignal_notification_write_mem` this makes the
notification ↔ TCB binding concrete: *both* ends of the wake are covered by a
held write lock, so under the 2PL bracket
(`notificationSignalOnCore_atomic_under_lockSet`) the binding mutation is
serialised against every other core.  Unconditional in the waiter (no
distinctness side-condition): even were the waiter the signaller itself, the
write lock subsumes the signaller's read lock via the `AccessMode.lub`. -/
theorem lockSet_notificationSignal_waiter_tcb_write_mem
    (signaller : SeLe4n.ThreadId) (cnRoot notificationId : SeLe4n.ObjId)
    (wt : SeLe4n.ThreadId) :
    (tcbLock wt, AccessMode.write)
      ∈ (lockSet_notificationSignal signaller cnRoot notificationId (some wt)).pairs := by
  unfold lockSet_notificationSignal
  simp only [lockSetExtendOpt, Option.map_some, Option.map_none]
  exact self_write_mem_insertOrMerge _ (tcbLock wt)

/-- WS-SM SM6.B/SM6.D (PR #822 Codex review): the bound-delivery **bound-TCB write
lock** — under which `notificationSignalBoundOnCore` writes the dequeued bound TCB
(`.ready` + badge) — is a declared member of the canonical `notificationSignal`
footprint once the bound TCB is resolved (`boundTcb := some bt`).  This is the
endpoint-receive-queue/receiver-TCB write that the prior footprint left outside the
2PL set; it is now covered (the live state-resolved form is
`lockSet_notificationSignalBoundOnCore`). -/
theorem lockSet_notificationSignal_bound_tcb_write_mem
    (signaller : SeLe4n.ThreadId) (cnRoot notificationId : SeLe4n.ObjId)
    (waiter? : Option SeLe4n.ThreadId) (boundEp? : Option SeLe4n.ObjId)
    (bt : SeLe4n.ThreadId) :
    (tcbLock bt, AccessMode.write)
      ∈ (lockSet_notificationSignal signaller cnRoot notificationId waiter? boundEp? (some bt)).pairs := by
  unfold lockSet_notificationSignal
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (tcbLock bt)

/-- WS-SM SM6.B/SM6.D (PR #822 Codex review): the bound-delivery **endpoint write
lock** — under which `notificationSignalBoundOnCore` dequeues the bound TCB from its
endpoint (`endpointQueueRemoveDual`, an endpoint-queue mutation) — is a declared
member of the canonical `notificationSignal` footprint once the bound endpoint + TCB
are resolved. -/
theorem lockSet_notificationSignal_bound_endpoint_write_mem
    (signaller : SeLe4n.ThreadId) (cnRoot notificationId : SeLe4n.ObjId)
    (waiter? : Option SeLe4n.ThreadId) (ep : SeLe4n.ObjId) (bt : SeLe4n.ThreadId) :
    (endpointLock ep, AccessMode.write)
      ∈ (lockSet_notificationSignal signaller cnRoot notificationId waiter? (some ep) (some bt)).pairs := by
  unfold lockSet_notificationSignal
  simp only [lockSetExtendOpt, Option.map_some]
  refine mem_insertOrMerge_of_mem_of_ne _ _ _ _ ?_ ?_
  · exact self_write_mem_insertOrMerge _ (endpointLock ep)
  · show endpointLock ep ≠ tcbLock bt
    intro h; simp [endpointLock, tcbLock] at h

-- ============================================================================
-- §7  SM6.B.5 — Per-core consistency of the signal wake
-- ============================================================================

/-- WS-SM SM6.B.5 (`notificationSignal_perCore_consistent`): the signal's
cross-core waiter wake is **confined to the waiter's home core** — every *other*
core's run queue and current thread are exactly the pre-state's.  The signaller is
not descheduled (signal is non-blocking), and the only scheduler edit is the
waiter's enqueue on `determineTargetCore st'' waiter`; a concurrent scheduling
decision on any sibling core cannot observe a change to its own per-core state
(the per-core locality matching the `runQueue ⟨target⟩` write lock of
`wakeThreadLockSet` covering only the target). -/
theorem notificationSignalOnCore_perCore_consistent
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification)
    (waiter : SeLe4n.ThreadId) (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (st' st'' : SystemState) (c' : CoreId)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest))
    (hStore : storeObject notificationId (.notification
        { state := if rest.val.isEmpty then .idle else .waiting,
          waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hMsg : storeTcbIpcStateAndMessage st' waiter .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st'')
    (hOther : determineTargetCore st'' waiter ≠ c') :
    (notificationSignalOnCore notificationId badge executingCore st).1.scheduler.runQueueOnCore c'
        = st.scheduler.runQueueOnCore c'
    ∧ (notificationSignalOnCore notificationId badge executingCore st).1.scheduler.currentOnCore c'
        = st.scheduler.currentOnCore c' := by
  have hSched : st''.scheduler = st.scheduler := by
    rw [storeTcbIpcStateAndMessage_scheduler_eq st' st'' waiter .ready _ hMsg,
        storeObject_scheduler_eq st st' notificationId _ hStore]
  rw [notificationSignalOnCore_waiter_eq notificationId badge executingCore st ntfn
        waiter rest st' st'' hObj hWaiters hStore hMsg]
  obtain ⟨hRQ, hCur⟩ := wakeThread_independent_of_other_core st'' waiter executingCore c' hOther
  exact ⟨by rw [hRQ, hSched], by rw [hCur, hSched]⟩

-- ============================================================================
-- §8  SM6.B.4 — 2PL atomicity of the notification syscalls under their lock-set
-- ============================================================================

/-- WS-SM SM6.B.4 (`notificationWait_atomic_under_lockSet`, plan §3.4 / Theorem
2.1.10): under its `notificationWait` lock-set the cross-core transition is a
single two-phase-locked atomic step — wrapping `notificationWaitOnCore` in
`withLockSet` decomposes deterministically into the acquire fold, the transition,
and the release fold.  No partial intermediate is observable to a lock-insensitive
observer; this is the operational atomicity the per-core IPC invariant
preservation (SM6.D) rests on. -/
theorem notificationWaitOnCore_atomic_under_lockSet
    (notificationId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (executingCore : CoreId)
    (cnRoot : SeLe4n.ObjId) (s : SystemState) :
    withLockSet (lockSet_notificationWait caller cnRoot notificationId) executingCore
        (notificationWaitOnCore notificationId caller executingCore) s
      = (releaseAll executingCore
          (lockSet_notificationWait caller cnRoot notificationId).lockAcquireSequence.reverse
          (notificationWaitOnCore notificationId caller executingCore
            (acquireAll executingCore
              (lockSet_notificationWait caller cnRoot notificationId).lockAcquireSequence s)).1,
         (notificationWaitOnCore notificationId caller executingCore
            (acquireAll executingCore
              (lockSet_notificationWait caller cnRoot notificationId).lockAcquireSequence s)).2) :=
  lockSet_atomic_under_2pl _ executingCore _ s

/-- WS-SM SM6.B.4 (companion): the cross-core `notificationSignal` is likewise a
single 2PL-atomic step under its `notificationSignal` lock-set. -/
theorem notificationSignalOnCore_atomic_under_lockSet
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (signaller : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId)
    (waiter? : Option SeLe4n.ThreadId) (s : SystemState) :
    withLockSet (lockSet_notificationSignal signaller cnRoot notificationId waiter?) executingCore
        (notificationSignalOnCore notificationId badge executingCore) s
      = (releaseAll executingCore
          (lockSet_notificationSignal signaller cnRoot notificationId waiter?).lockAcquireSequence.reverse
          (notificationSignalOnCore notificationId badge executingCore
            (acquireAll executingCore
              (lockSet_notificationSignal signaller cnRoot notificationId waiter?).lockAcquireSequence s)).1,
         (notificationSignalOnCore notificationId badge executingCore
            (acquireAll executingCore
              (lockSet_notificationSignal signaller cnRoot notificationId waiter?).lockAcquireSequence s)).2) :=
  lockSet_atomic_under_2pl _ executingCore _ s

-- ============================================================================
-- §9  SM6.B.3 — Multi-waiter discipline preserved
-- ============================================================================

/-- WS-SM SM6.B.3 (structural discipline): a signal that finds waiters wakes
**exactly the head** waiter and leaves the rest intact — the waiter list
decomposes as `waiter :: rest.val`, the woken `waiter` is *not* a member of the
remaining list `rest` (the original list was duplicate-free), and `rest` is itself
duplicate-free.  This is the multi-waiter invariant the signal preserves: one wake
per signal, no waiter lost or duplicated. -/
theorem notificationSignalOnCore_wakes_head
    (ntfn : Notification) (waiter : SeLe4n.ThreadId)
    (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest)) :
    ntfn.waitingThreads.val = waiter :: rest.val
    ∧ waiter ∉ rest.val
    ∧ rest.val.Nodup := by
  have hVal := (SeLe4n.NoDupList.tail?_eq_some_iff ntfn.waitingThreads waiter rest).mp hWaiters
  have hNd : (waiter :: rest.val).Nodup := hVal ▸ ntfn.waitingThreads.hNodup
  exact ⟨hVal, (List.nodup_cons.mp hNd).1, rest.hNodup⟩

/-- The signalled notification id and the woken waiter denote **distinct
objects**: a store at the waiter's TCB after the notification was written would
have failed (`lookupTcb` would find a notification, not a TCB) had they
coincided.  Derived from the *success* of the waiter store — no separate
well-formedness hypothesis is needed. -/
private theorem notification_ne_waiter_of_store
    (st' st'' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (ntfn' : Notification) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hNtfn : st'.objects[notificationId]? = some (.notification ntfn'))
    (hMsg : storeTcbIpcStateAndMessage st' waiter ipc msg = .ok st'') :
    notificationId ≠ waiter.toObjId := by
  intro hEq
  rw [hEq] at hNtfn
  have hLk : lookupTcb st' waiter = none := by
    unfold lookupTcb
    by_cases hRes : waiter.isReserved
    · simp [hRes]
    · simp [hRes, hNtfn]
  simp [storeTcbIpcStateAndMessage, hLk] at hMsg

/-- WS-SM SM6.B.3 (preservation through the cross-core wake): after the
cross-core signal, the **observable** notification has exactly the remaining
waiter list `rest` — the woken head is gone, the rest are preserved, and the
list is still duplicate-free.  The cross-core waiter wake (`wakeThread`) is
object-invisible (the waiter was just set `.ready`, so the wake's identical-value
re-insert agrees on every object lookup), so reading the notification back through
the wake yields the notification stored by the signal. -/
theorem notificationSignalOnCore_remaining_waiters
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification)
    (waiter : SeLe4n.ThreadId) (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest))
    (hStore : storeObject notificationId (.notification
        { state := if rest.val.isEmpty then .idle else .waiting,
          waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hMsg : storeTcbIpcStateAndMessage st' waiter .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st'')
    (hObjInv : st.objects.invExt) :
    ∃ ntfnPost,
      (notificationSignalOnCore notificationId badge executingCore st).1.objects[notificationId]?
        = some (.notification ntfnPost)
      ∧ ntfnPost.waitingThreads = rest
      ∧ waiter ∉ ntfnPost.waitingThreads.val
      ∧ ntfnPost.state = (if rest.val.isEmpty then .idle else .waiting)
      ∧ ntfnPost.pendingBadge = none := by
  have hInv' : st'.objects.invExt :=
    storeObject_preserves_objects_invExt st st' notificationId _ hObjInv hStore
  have hInv'' : st''.objects.invExt :=
    storeTcbIpcStateAndMessage_preserves_objects_invExt st' st'' waiter _ _ hInv' hMsg
  obtain ⟨wTcb, hwGet, hwReady⟩ :=
    storeTcbIpcStateAndMessage_getTcb?_ipcState st' st'' waiter .ready _ hInv' hMsg
  have hNtfn' : st'.objects[notificationId]? = some (.notification
      { state := if rest.val.isEmpty then .idle else .waiting,
        waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }) :=
    storeObject_objects_eq st st' notificationId _ hObjInv hStore
  have hNe : notificationId ≠ waiter.toObjId :=
    notification_ne_waiter_of_store st' st'' notificationId waiter _ .ready _ hNtfn' hMsg
  refine ⟨{ state := if rest.val.isEmpty then .idle else .waiting,
            waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }, ?_, rfl, ?_, rfl, rfl⟩
  · rw [notificationSignalOnCore_waiter_eq notificationId badge executingCore st ntfn
          waiter rest st' st'' hObj hWaiters hStore hMsg]
    show (wakeThread st'' waiter executingCore).1.objects[notificationId]?
      = some (.notification _)
    rw [wakeThread_objects_getElem_eq_of_ready st'' waiter executingCore wTcb hwGet hwReady
          hInv'' notificationId,
        storeTcbIpcStateAndMessage_preserves_objects_ne st' st'' waiter .ready _ notificationId
          hNe hInv' hMsg]
    exact hNtfn'
  · exact (notificationSignalOnCore_wakes_head ntfn waiter rest hWaiters).2.1

-- ============================================================================
-- §10  SM6.B.2 (strengthening) — SGI target is the *pre-state* home core
-- ============================================================================

/-- `determineTargetCore` depends on the thread only through its TCB's
`cpuAffinity`: two states whose `getTcb?` agree up to `cpuAffinity` route the
thread to the same core.  The congruence that lets the SGI target be read at the
pre-state rather than at the post-store wake site. -/
theorem determineTargetCore_congr (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (h : (st'.getTcb? tid).map (·.cpuAffinity) = (st.getTcb? tid).map (·.cpuAffinity)) :
    determineTargetCore st' tid = determineTargetCore st tid := by
  cases hT' : st'.getTcb? tid with
  | none => cases hT : st.getTcb? tid with
    | none => simp [determineTargetCore, hT', hT]
    | some t => rw [hT', hT] at h; simp at h
  | some t' => cases hT : st.getTcb? tid with
    | none => rw [hT', hT] at h; simp at h
    | some t =>
      have hAff : t'.cpuAffinity = t.cpuAffinity := by rw [hT', hT] at h; simpa using h
      simp [determineTargetCore, hT', hT, hAff]

/-- `storeTcbIpcStateAndMessage` preserves every thread's `cpuAffinity` (it writes
only `ipcState` / `pendingMessage`), hence preserves `determineTargetCore`. -/
theorem storeTcbIpcStateAndMessage_determineTargetCore_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (msg : Option IpcMessage) (x : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    determineTargetCore st' x = determineTargetCore st x := by
  refine determineTargetCore_congr st st' x ?_
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLk : lookupTcb st tid with
  | none => simp [hLk] at hStep
  | some tcb =>
    simp only [hLk] at hStep
    cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hSO] at hStep
    | ok pair =>
      simp only [hSO] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      simp only [SystemState.getTcb?]
      by_cases hEq2 : x.toObjId = tid.toObjId
      · rw [hEq2]
        simp [storeObject_objects_eq' st tid.toObjId _ pair hObjInv hSO,
              lookupTcb_some_objects st tid tcb hLk]
      · rw [storeObject_objects_ne' st tid.toObjId x.toObjId _ pair hEq2 hObjInv hSO]

/-- `storeObject` at an id distinct from `x`'s TCB preserves `x`'s
`determineTargetCore` (it does not touch `x`'s TCB). -/
theorem storeObject_determineTargetCore_eq
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject) (x : SeLe4n.ThreadId)
    (hNe : id ≠ x.toObjId) (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  refine determineTargetCore_congr st st' x ?_
  simp only [SystemState.getTcb?,
    storeObject_objects_ne st st' id x.toObjId obj (fun h => hNe h.symm) hObjInv hStore]

/-- WS-SM SM6.B.2 (honest SGI target): the cross-core signal's `.reschedule` SGI
targets the waiter's **pre-state** home core `determineTargetCore st waiter` — the
intervening notification-store + waiter-store touch only the notification object
and the waiter's `ipcState` / `pendingMessage`, never its `cpuAffinity`, so the
wake-site target coincides with the pre-state one.  The cleaner form of
`notificationSignalOnCore_remote_wake` (whose target is read at `st''`). -/
theorem notificationSignalOnCore_remote_wake_preState
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification)
    (waiter : SeLe4n.ThreadId) (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (waiterTcb'' : TCB) (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest))
    (hStore : storeObject notificationId (.notification
        { state := if rest.val.isEmpty then .idle else .waiting,
          waitingThreads := rest, pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hMsg : storeTcbIpcStateAndMessage st' waiter .ready
        (some { IpcMessage.empty with badge := some badge }) = .ok st'')
    (hTcb'' : st''.getTcb? waiter = some waiterTcb'')
    (hObjInv : st.objects.invExt)
    (hRemote : determineTargetCore st waiter ≠ executingCore) :
    (notificationSignalOnCore notificationId badge executingCore st).2
      = .ok (some (determineTargetCore st waiter, SgiKind.reschedule)) := by
  -- The wake-site target equals the pre-state target (affinity is frame-stable).
  have hNe : notificationId ≠ waiter.toObjId := by
    have hNtfn' := storeObject_objects_eq st st' notificationId _ hObjInv hStore
    exact notification_ne_waiter_of_store st' st'' notificationId waiter _ .ready _ hNtfn' hMsg
  have hInv' : st'.objects.invExt :=
    storeObject_preserves_objects_invExt st st' notificationId _ hObjInv hStore
  have hTarget : determineTargetCore st'' waiter = determineTargetCore st waiter := by
    rw [storeTcbIpcStateAndMessage_determineTargetCore_eq st' st'' waiter .ready _ waiter hInv' hMsg,
        storeObject_determineTargetCore_eq st st' notificationId _ waiter hNe hObjInv hStore]
  rw [notificationSignalOnCore_remote_wake notificationId badge executingCore st ntfn waiter rest
        waiterTcb'' st' st'' hObj hWaiters hStore hMsg hTcb'' (by rw [hTarget]; exact hRemote),
      hTarget]

-- ============================================================================
-- §11  SM6.B (coherence) — the lock-set pre-resolution names the woken thread
-- ============================================================================

/-- WS-SM SM6.B (lock-set / transition coherence): the waiter the lock-set
pre-resolves (`notificationSignalWaiter?`, the notification's waiter-list head,
used to build `lockSet_notificationSignalOnCore`) is **exactly** the thread the
transition wakes (the `tail?` head).  So the runtime acquires the waiter-TCB write
lock on the very TCB the signal mutates — the footprint declaration and the
operation agree. -/
theorem notificationSignalWaiter?_eq_wake_head
    (st : SystemState) (notificationId : SeLe4n.ObjId) (ntfn : Notification)
    (waiter : SeLe4n.ThreadId) (rest : SeLe4n.NoDupList SeLe4n.ThreadId)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads.tail? = some (waiter, rest)) :
    notificationSignalWaiter? st notificationId = some waiter := by
  have hObjN : st.getNotification? notificationId = some ntfn :=
    (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mpr hObj
  unfold notificationSignalWaiter?
  rw [hObjN]
  have hVal : ntfn.waitingThreads.val = waiter :: rest.val :=
    (SeLe4n.NoDupList.tail?_eq_some_iff ntfn.waitingThreads waiter rest).mp hWaiters
  show ntfn.waitingThreads.head? = some waiter
  unfold SeLe4n.NoDupList.head?
  rw [hVal]; rfl

-- ============================================================================
-- §12  SM6.B.1 — `notificationWaitOnCore` path reductions + per-core blocking
-- ============================================================================

/-- WS-SM SM6.B.1: full reduction of the **badge-consume** path (the notification
has a pending badge).  The caller stays runnable and receives the badge; no SGI
and no deschedule. -/
theorem notificationWaitOnCore_badge_eq
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification) (badge : SeLe4n.Badge) (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hBadge : ntfn.pendingBadge = some badge)
    (hStore : storeObject notificationId (.notification
        { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none, boundTCB := ntfn.boundTCB }) st
        = .ok ((), st'))
    (hTcb : storeTcbIpcState st' waiter .ready = .ok st'') :
    notificationWaitOnCore notificationId waiter executingCore st = (st'', .ok (some badge)) := by
  unfold notificationWaitOnCore
  have hObjN : st.getNotification? notificationId = some ntfn :=
    (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mpr hObj
  simp only [hObjN, hBadge, hStore, hTcb]

/-- WS-SM SM6.B.1: full reduction of the **block** path (no pending badge, the
caller is not already waiting, and the waiter-list cons succeeds).  The caller is
appended to the waiter list, transitions to `blockedOnNotification`, and is
removed from *its own* core's run queue/current via `removeRunnableOnCore`. -/
theorem notificationWaitOnCore_block_eq
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification) (tcb : TCB)
    (wt' : SeLe4n.NoDupList SeLe4n.ThreadId) (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hBadge : ntfn.pendingBadge = none)
    (hLk : lookupTcb st waiter = some tcb)
    (hNotWaiting : ¬ (tcb.ipcState = .blockedOnNotification notificationId))
    (hCons : ntfn.waitingThreads.consWithGuard? waiter = some wt')
    (hStore : storeObject notificationId (.notification
        { state := .waiting, waitingThreads := wt', pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hTcb : storeTcbIpcState_fromTcb st' waiter tcb (.blockedOnNotification notificationId) = .ok st'') :
    notificationWaitOnCore notificationId waiter executingCore st
      = (removeRunnableOnCore st'' waiter executingCore, .ok none) := by
  unfold notificationWaitOnCore
  have hObjN : st.getNotification? notificationId = some ntfn :=
    (SystemState.getNotification?_eq_some_iff st notificationId ntfn).mpr hObj
  simp only [hObjN, hBadge, hLk, if_neg hNotWaiting, hCons, hStore, hTcb]

/-- WS-SM SM6.B.1 (`notificationWait_perCore_blocking`): on the block path the
caller is **blocked on its own core** — removed from `executingCore`'s run queue
and cleared from `executingCore`'s current slot.  The wait pokes no other core
(no SGI); the deschedule is confined to the executing core. -/
theorem notificationWaitOnCore_perCore_blocking
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (ntfn : Notification) (tcb : TCB)
    (wt' : SeLe4n.NoDupList SeLe4n.ThreadId) (st' st'' : SystemState)
    (hObj : st.objects[notificationId]? = some (.notification ntfn))
    (hBadge : ntfn.pendingBadge = none)
    (hLk : lookupTcb st waiter = some tcb)
    (hNotWaiting : ¬ (tcb.ipcState = .blockedOnNotification notificationId))
    (hCons : ntfn.waitingThreads.consWithGuard? waiter = some wt')
    (hStore : storeObject notificationId (.notification
        { state := .waiting, waitingThreads := wt', pendingBadge := none, boundTCB := ntfn.boundTCB }) st = .ok ((), st'))
    (hTcb : storeTcbIpcState_fromTcb st' waiter tcb (.blockedOnNotification notificationId) = .ok st'') :
    waiter ∉ (notificationWaitOnCore notificationId waiter executingCore st).1.scheduler.runQueueOnCore executingCore ∧
    (notificationWaitOnCore notificationId waiter executingCore st).1.scheduler.currentOnCore executingCore
      ≠ some waiter := by
  rw [notificationWaitOnCore_block_eq notificationId waiter executingCore st ntfn tcb wt' st' st''
        hObj hBadge hLk hNotWaiting hCons hStore hTcb]
  exact ⟨removeRunnableOnCore_not_mem_self st'' waiter executingCore,
         removeRunnableOnCore_currentOnCore_ne_self st'' waiter executingCore⟩

end SeLe4n.Kernel
