-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.A: PRODUCTION (LANDED).  `endpointCallOnCore` entered the production
-- import closure when the live `.call` dispatch (`API.dispatchWithCap{,Checked}`)
-- was wired through the cross-core call (`endpointCallCrossCoreDispatch`, which
-- builds on this transition).  (Former "STATUS: staged" marker replaced with this
-- landing note per the implement-the-improvement rule; see
-- docs/planning/SMP_CROSS_CORE_IPC_PLAN.md.)

import SeLe4n.Kernel.IPC.DualQueue.Transport
import SeLe4n.Kernel.IPC.DualQueue.WithCaps
import SeLe4n.Kernel.Scheduler.Operations.Selection
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.Concurrency.Locks.LockSetTransitions
import SeLe4n.Kernel.Concurrency.Locks.LockSet2PL

/-!
# WS-SM SM6.A — Endpoint call across cores

This module is the SM6.A deliverable of the WS-SM Phase 6 cross-core IPC
workstream (plan `docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.2, §5).  It
lifts the single-core `endpointCall` rendezvous (the blocking RPC send) to a
*cross-core* transition `endpointCallOnCore` that:

* runs on an explicit `executingCore : CoreId` (the caller's core),
* routes the receiver wake through the SM5.C cross-core `wakeThread`
  (so a receiver bound to a *remote* core is enqueued on that core and a
  `.reschedule` SGI is surfaced for the runtime to fire — plan Theorem 3.2.1),
* blocks the caller on *its own* core via the per-core `removeRunnableOnCore`
  generalisation of `removeRunnable`, and
* declares the SM3.B `lockSet_endpointCall` footprint (caller TCB write,
  sender CNode read, endpoint write, receiver TCB write on rendezvous, donated
  SchedContext write) under which the transition is two-phase-locked.

The single-core `endpointCall` (in `IPC.DualQueue.Transport`) remains the
canonical bootCore form: `endpointCallOnCore … bootCoreId` is its cross-core
generalisation, and `removeRunnableOnCore … bootCoreId = removeRunnable`
definitionally (the SM5.A backward-compatibility bridge pattern).

Staged until the SM5.I FFI seam wires `endpointCallOnCore` into the live
syscall dispatch with the `withLockSet` acquisition over `lockSet_endpointCall`
(the SM5.F tracked-debt closure); this module proves the SM6.A theorems that
the wiring consumes.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  Per-core caller blocking — `removeRunnableOnCore`
-- ============================================================================

/-- WS-SM SM6.A.1 (plan §3.2 steps 5–6): the per-core generalisation of
`removeRunnable`.  Removes `tid` from core `c`'s run queue and, if `tid` is
core `c`'s current thread, clears `c`'s current slot.  Only core `c`'s
scheduler slots are touched; every other core is framed out.

The single-core `removeRunnable` (bootCore-pinned) is exactly the `bootCoreId`
instance — see `removeRunnableOnCore_bootCoreId`. -/
def removeRunnableOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    SystemState :=
  { st with
      scheduler := (st.scheduler.setRunQueueOnCore c
          ((st.scheduler.runQueueOnCore c).remove tid)).setCurrentOnCore c
          (if (st.scheduler.currentOnCore c) = some tid then none
            else (st.scheduler.currentOnCore c)) }

/-- WS-SM SM6.A.1: `removeRunnableOnCore` at the boot core is exactly the
single-core `removeRunnable` — the backward-compatibility bridge. -/
@[simp] theorem removeRunnableOnCore_bootCoreId (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    removeRunnableOnCore st tid bootCoreId = removeRunnable st tid := rfl

-- ============================================================================
-- §2  Lock-set pre-resolution helpers (plan §3.1 / §4.2)
-- ============================================================================

/-- WS-SM SM6.A.1: the receiver a cross-core call would rendezvous with — the
head of the endpoint's receive queue, if any.  Pre-resolved from the pre-state
so the caller can assemble the `lockSet_endpointCall` footprint (the receiver
TCB write lock is present iff a receiver is waiting). -/
def endpointCallReceiver? (st : SystemState) (endpointId : SeLe4n.ObjId) :
    Option SeLe4n.ThreadId :=
  match st.getEndpoint? endpointId with
  | some ep => ep.receiveQ.head
  | none    => none

/-- WS-SM SM6.A.5: the SchedContext the caller would donate on this call — its
own bound SC (a `.bound scId` binding), if any.  A caller that is `.unbound` or
already holds a `.donated _ _` binding donates nothing on this call (matching
`applyCallDonation`), so the SC write lock is in the footprint iff the caller
has an active SC of its own to donate. -/
def endpointCallDonatedSc? (st : SystemState) (caller : SeLe4n.ThreadId) :
    Option SeLe4n.SchedContextId :=
  match st.getTcb? caller with
  | some tcb =>
      match tcb.schedContextBinding with
      | .bound scId => some scId
      | _           => none
  | none => none

/-- WS-SM SM6.D (PR #822 review): the server-first stashed Reply object this call
links, if any.  On a **server-first** `Call` rendezvous the popped receiver is a
server already `.blockedOnReceive` having pre-supplied a reply object via
`endpoint_receive_with_reply` (`TCB.pendingReceiveReply = some rid`); the rendezvous
links the woken caller to it (`linkServerFirstCaller` writes `reply.caller := caller`
and clears the server's stash), so the per-object **reply write-lock** must be in the
Call footprint.  `none` for a receiver that did a plain receive (no stash) or when
there is no receiver (the caller blocks). -/
def endpointCallServerFirstReply? (st : SystemState) (endpointId : SeLe4n.ObjId) :
    Option SeLe4n.ReplyId :=
  (endpointCallReceiver? st endpointId).bind fun receiver =>
    (st.getTcb? receiver).bind (·.pendingReceiveReply)

/-- WS-SM SM6.A.1: the concrete lock-set a cross-core `endpointCallOnCore` on
state `st` acquires — `lockSet_endpointCall` with the receiver, donated
SchedContext, and (SM6.D, PR #822 review) the server-first stashed reply object
**pre-resolved from `st`** via `endpointCallReceiver?` / `endpointCallDonatedSc?` /
`endpointCallServerFirstReply?` (the receiver is the endpoint's receive-queue head;
the donated SC is the caller's own bound SC; the reply object is the server's
pre-supplied `pendingReceiveReply`, which `linkServerFirstCaller` writes on a
server-first rendezvous).  This is the footprint the runtime `withLockSet` bracket
(the SM5.I FFI seam) acquires before invoking
`endpointCallOnCore endpointId caller … executingCore st`. -/
def lockSet_endpointCallOnCore (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId) : LockSet :=
  lockSet_endpointCall caller cnodeRootObjId endpointId
    (endpointCallReceiver? st endpointId) (endpointCallDonatedSc? st caller)
    (endpointCallServerFirstReply? st endpointId)

-- ============================================================================
-- §3  WithCaps lock-set (plan §3.1)
-- ============================================================================

/-- WS-SM SM6.A.8 (plan §3.1): the lock-set for `endpointCallWithCaps`.  Extends
`lockSet_endpointCall` with the **destination CNode write lock** (the receiver's
CSpace root, into which `ipcUnwrapCaps` installs the transferred capabilities).
The sender CNode (read) is already part of `lockSet_endpointCall`; if the dest
CNode coincides with the sender CNode, `insertOrMerge`'s `AccessMode.lub`
upgrades it to write (conservative, union-over-all-paths). -/
def lockSet_endpointCallWithCaps (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (destCnodeObjId : SeLe4n.ObjId)
    (endpointObjId : SeLe4n.ObjId)
    (receiverTid : Option SeLe4n.ThreadId)
    (donatedScId : Option SeLe4n.SchedContextId) : LockSet :=
  lockSetExtendOpt
    (lockSet_endpointCall callerTid cnodeRootObjId endpointObjId receiverTid donatedScId)
    (some (cnodeLock destCnodeObjId, .write))

-- ============================================================================
-- §4  The cross-core endpoint-call transition (plan §3.2)
-- ============================================================================

/-- WS-SM SM6.A.1 (plan §3.2): endpoint call across cores.

Mirrors the single-core `endpointCall` rendezvous, with two cross-core
substitutions:

* **Receiver wake** — on rendezvous the receiver is woken through the SM5.C
  `wakeThread … executingCore`, which enqueues it on its *home* core
  (`determineTargetCore`) and returns `some (target, .reschedule)` when that
  core differs from `executingCore` (the cross-core poke the runtime fires).
* **Caller block** — the caller is removed from *its own* core's run
  queue/current via `removeRunnableOnCore … executingCore`.

Returns the post-state paired with `Except KernelError (Option (CoreId ×
SgiKind))`: an error on a failed step (pre-state returned, so a `withLockSet`
bracket still releases cleanly), or `.ok sgi?` with the optional cross-core SGI
to emit after the state commit. -/
def endpointCallOnCore (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  if msg.registers.size > maxMessageRegisters then (st, .error .ipcMessageTooLarge)
  else if msg.caps.size > maxExtraCaps then (st, .error .ipcMessageTooManyCaps)
  else
  match st.getEndpoint? endpointId with
  | some ep =>
      match ep.receiveQ.head with
      | some _ =>
          match endpointQueuePopHead endpointId true st with
          | .error e => (st, .error e)
          | .ok (receiver, _tcb, st') =>
              match storeTcbIpcStateAndMessage st' receiver .ready (some msg) with
              | .error e => (st, .error e)
              | .ok st'' =>
                  -- Cross-core receiver wake (SM5.C): route to the receiver's
                  -- home core, capturing the optional `.reschedule` SGI.
                  match storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
                      caller (.blockedOnReply endpointId (some receiver)) none with
                  | .error e => (st, .error e)
                  | .ok st4 => (removeRunnableOnCore st4 caller executingCore,
                                .ok (wakeThread st'' receiver executingCore).2)
      | none =>
          match endpointQueueEnqueue endpointId false caller st with
          | .error e => (st, .error e)
          | .ok st' =>
              match storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
              | .error e => (st, .error e)
              | .ok st'' => (removeRunnableOnCore st'' caller executingCore, .ok none)
  | none =>
      -- Typed-accessor dispatch (AK7 cascade discipline): `getEndpoint?` is
      -- `none` for both an absent object and a wrong-kinded one.  Recover the
      -- single-core `endpointCall` error distinction without a raw object-store
      -- variant match: a present-but-wrong-kind object fails with
      -- `.invalidCapability`, a genuinely absent one with `.objectNotFound`.
      if (st.objects[endpointId]?).isSome then (st, .error .invalidCapability)
      else (st, .error .objectNotFound)

-- ============================================================================
-- §5  Path reduction lemmas (full characterisation of each control path)
-- ============================================================================

/-- WS-SM SM6.A.1: full reduction of the **rendezvous** path (a receiver is
waiting on the endpoint).  The post-state is the caller-blocked state with the
receiver woken (cross-core) and the caller removed from its own core; the
surfaced SGI is exactly the receiver wake's. -/
theorem endpointCallOnCore_rendezvous_eq
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (recvTcb0 : TCB) (st' st'' st4 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4) :
    endpointCallOnCore endpointId caller msg executingCore st
      = (removeRunnableOnCore st4 caller executingCore,
         .ok (wakeThread st'' receiver executingCore).2) := by
  unfold endpointCallOnCore
  rw [if_neg hSz1, if_neg hSz2]
  have hObjE : st.getEndpoint? endpointId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mpr hObj
  simp only [hObjE, hHead, hPop, hStore, hCallerStore]

/-- WS-SM SM6.A.1: full reduction of the **no-receiver** path (the caller
enqueues on the endpoint's send queue as `blockedOnCall`).  No wake occurs, so
no SGI is surfaced; the caller is removed from its own core. -/
theorem endpointCallOnCore_noReceiver_eq
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint) (st' st'' : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = none)
    (hEnq : endpointQueueEnqueue endpointId false caller st = .ok st')
    (hStore : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg)
        = .ok st'') :
    endpointCallOnCore endpointId caller msg executingCore st
      = (removeRunnableOnCore st'' caller executingCore, .ok none) := by
  unfold endpointCallOnCore
  rw [if_neg hSz1, if_neg hSz2]
  have hObjE : st.getEndpoint? endpointId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mpr hObj
  simp only [hObjE, hHead, hEnq, hStore]

-- ============================================================================
-- §6  SM6.A.3 — Cross-core wake: SGI emission (plan Theorem 3.2.1)
-- ============================================================================

/-- WS-SM SM6.A.3 (plan §3.2 Theorem 3.2.1,
`endpointCall_emits_sgi_if_remote_receiver`).  When a cross-core `endpointCall`
rendezvous unblocks a receiver whose home core differs from the executing core,
the operation surfaces a `.reschedule` SGI targeting the receiver's core — the
cross-core poke the runtime fires after the state commit.  The target core is
the receiver's home core `determineTargetCore … receiver` (its `cpuAffinity`),
read at the wake site `st''`; the intervening pop + store mutate only the
receiver's `ipcState` / `pendingMessage` and the endpoint queue links, never its
`cpuAffinity`, so this is the same core the plan's pre-state `determineTargetCore
s receiver` names. -/
theorem endpointCallOnCore_emits_sgi_if_remote_receiver
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (recvTcb0 recvTcb'' : TCB) (st' st'' st4 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hTcb'' : st''.getTcb? receiver = some recvTcb'')
    (hRemote : determineTargetCore st'' receiver ≠ executingCore) :
    (endpointCallOnCore endpointId caller msg executingCore st).2
      = .ok (some (determineTargetCore st'' receiver, SgiKind.reschedule)) := by
  rw [endpointCallOnCore_rendezvous_eq endpointId caller msg executingCore st ep receiver
        recvTcb0 st' st'' st4 hSz1 hSz2 hObj hHead hPop hStore hCallerStore]
  show Except.ok (wakeThread st'' receiver executingCore).2
      = Except.ok (some (determineTargetCore st'' receiver, SgiKind.reschedule))
  rw [wakeThread_emits_sgi_if_remote st'' receiver executingCore recvTcb'' hTcb'' hRemote]

/-- WS-SM SM6.A.3: dually, a cross-core call whose receiver is *local* (home
core = executing core) surfaces **no** SGI — the local scheduler picks the
newly-runnable receiver up on its next decision. -/
theorem endpointCallOnCore_no_sgi_if_local_receiver
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (recvTcb0 : TCB) (st' st'' st4 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hLocal : determineTargetCore st'' receiver = executingCore) :
    (endpointCallOnCore endpointId caller msg executingCore st).2 = .ok none := by
  rw [endpointCallOnCore_rendezvous_eq endpointId caller msg executingCore st ep receiver
        recvTcb0 st' st'' st4 hSz1 hSz2 hObj hHead hPop hStore hCallerStore]
  show Except.ok (wakeThread st'' receiver executingCore).2 = Except.ok none
  rw [wakeThread_no_sgi_if_local st'' receiver executingCore hLocal]

/-- WS-SM SM6.A.3: the **no-receiver** path (the caller enqueues on the
endpoint's send queue as `blockedOnCall`) surfaces no SGI — no thread is woken,
so there is no cross-core poke.  Completes the SGI characterisation: a call pokes
a remote core *only* on a rendezvous with a remote receiver. -/
theorem endpointCallOnCore_noReceiver_no_sgi
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint) (st' st'' : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = none)
    (hEnq : endpointQueueEnqueue endpointId false caller st = .ok st')
    (hStore : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg)
        = .ok st'') :
    (endpointCallOnCore endpointId caller msg executingCore st).2 = .ok none := by
  rw [endpointCallOnCore_noReceiver_eq endpointId caller msg executingCore st ep st' st''
        hSz1 hSz2 hObj hHead hEnq hStore]

-- ============================================================================
-- §7  SM6.A.2 — `endpointCall` lock-set correctness
-- ============================================================================

/-- WS-SM SM6.A.2 (`endpointCall_lockSet_correct`): the `endpointCall`
lock-set is **hierarchically correct** — every lock it declares has a kind in
`permittedKinds .call` (so the acquisitions respect the SM0.I lock ladder), and
its keys are duplicate-free (the SM3.B well-formedness `LockSet` carries by
construction).  Together these are the structural soundness conditions the
deadlock-freedom theorem (2.1.9) and the 2PL serializability corollary
(2.1.11) consume. -/
theorem endpointCallOnCore_lockSet_correct
    (caller : SeLe4n.ThreadId) (cnRoot endpointId : SeLe4n.ObjId)
    (receiver? : Option SeLe4n.ThreadId) (donatedSc? : Option SeLe4n.SchedContextId) :
    (∀ p ∈ (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?).pairs,
        p.fst.kind ∈ permittedKinds .call) ∧
    ((lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?).pairs.map
        (·.fst)).Nodup :=
  ⟨lockSet_consistent_call caller cnRoot endpointId receiver? donatedSc?,
   (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?).hUniqueKeys⟩

/-- WS-SM SM6.A.2: the **state-resolved** call lock-set
(`lockSet_endpointCallOnCore`, with the receiver and donated SchedContext
pre-resolved from `st`) is hierarchically correct — every lock it declares has a
kind permitted for `.call`.  This is the form the runtime acquisition consumes,
so its correctness is a corollary of the parametric `lockSet_consistent_call`. -/
theorem lockSet_endpointCallOnCore_correct
    (st : SystemState) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) :
    ∀ p ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId).pairs,
      p.fst.kind ∈ permittedKinds .call :=
  lockSet_consistent_call caller cnodeRootObjId endpointId
    (endpointCallReceiver? st endpointId) (endpointCallDonatedSc? st caller)
    (endpointCallServerFirstReply? st endpointId)

-- ============================================================================
-- §8  SM6.A.5 — Donation-chain lock-set extension
-- ============================================================================

/-- WS-SM SM6.A.5 (plan §4.3): the cross-core donation-chain lock-set
extension.  When the caller donates a SchedContext on the call, the
`endpointCall` lock-set is *exactly* the non-donating lock-set extended with the
donated SchedContext's **write** lock — so the SC migration (`applyCallDonation`
rebinding `boundThread` across cores, SM5.H.4) runs under a held SC write lock,
serialised against every other core. -/
theorem lockSet_endpointCall_donation_extension
    (caller : SeLe4n.ThreadId) (cnRoot endpointId : SeLe4n.ObjId)
    (receiver? : Option SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) :
    lockSet_endpointCall caller cnRoot endpointId receiver? (some scId)
      = lockSetExtendOpt
          (lockSet_endpointCall caller cnRoot endpointId receiver? none)
          (some (schedContextLock scId, .write)) := by
  unfold lockSet_endpointCall
  rfl

-- ============================================================================
-- §9  SM6.A.8 — `endpointCallWithCaps` lock-set correctness
-- ============================================================================

/-- WS-SM SM6.A.8 (`endpointCallWithCaps_lockSet_correct`): the
`endpointCallWithCaps` lock-set — `endpointCall`'s footprint extended with the
**destination CNode write lock** — is hierarchically correct: every declared
lock still has a kind in `permittedKinds .call` (the destination CNode is a
`.cnode`, already a permitted kind, so the capability-transfer extension does
not breach the call's lock ladder). -/
theorem endpointCallWithCaps_lockSet_correct
    (caller : SeLe4n.ThreadId) (cnRoot destCnode endpointId : SeLe4n.ObjId)
    (receiver? : Option SeLe4n.ThreadId) (donatedSc? : Option SeLe4n.SchedContextId) :
    ∀ p ∈ (lockSet_endpointCallWithCaps caller cnRoot destCnode endpointId
              receiver? donatedSc?).pairs,
      p.fst.kind ∈ permittedKinds .call := by
  unfold lockSet_endpointCallWithCaps
  refine lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_call caller cnRoot endpointId receiver? donatedSc?) ?_
  intro pp hpp
  cases hpp
  show LockKind.cnode ∈ permittedKinds .call
  decide

-- ============================================================================
-- §10  SM6.A.9 — `endpointCall` atomicity under its lock-set (2PL)
-- ============================================================================

/-- WS-SM SM6.A.9 (`endpointCall_atomic_under_lockSet`, plan §3.4 / Theorem
2.1.10): under its `endpointCall` lock-set the cross-core transition is a
single two-phase-locked atomic step — wrapping `endpointCallOnCore` in
`withLockSet` decomposes deterministically into the acquire fold, the
transition, and the release fold.  No partial intermediate is observable to a
lock-insensitive observer (`lockSet_observer_atomic`); this is the operational
atomicity the `ipcInvariantFull_perCore` preservation (SM6.D) rests on. -/
theorem endpointCallOnCore_atomic_under_lockSet
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (cnRoot : SeLe4n.ObjId)
    (receiver? : Option SeLe4n.ThreadId) (donatedSc? : Option SeLe4n.SchedContextId)
    (s : SystemState) :
    withLockSet (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?)
        executingCore (endpointCallOnCore endpointId caller msg executingCore) s
      = (releaseAll executingCore
          (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?).lockAcquireSequence.reverse
          (endpointCallOnCore endpointId caller msg executingCore
            (acquireAll executingCore
              (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?).lockAcquireSequence s)).1,
         (endpointCallOnCore endpointId caller msg executingCore
            (acquireAll executingCore
              (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?).lockAcquireSequence s)).2) :=
  lockSet_atomic_under_2pl _ executingCore _ s

-- ============================================================================
-- §11  `removeRunnableOnCore` frame lemmas
-- ============================================================================

/-- `removeRunnableOnCore` touches only the scheduler — every object is preserved. -/
theorem removeRunnableOnCore_preserves_objects (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (removeRunnableOnCore st tid c).objects = st.objects := rfl

/-- `removeRunnableOnCore` preserves every `getTcb?` lookup (objects unchanged). -/
theorem removeRunnableOnCore_getTcb? (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (x : SeLe4n.ThreadId) :
    (removeRunnableOnCore st tid c).getTcb? x = st.getTcb? x := rfl

/-- `removeRunnableOnCore` writes core `c`'s run-queue slot to `remove tid`. -/
@[simp] theorem removeRunnableOnCore_runQueueOnCore_self (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.runQueueOnCore c
      = (st.scheduler.runQueueOnCore c).remove tid := by
  simp [removeRunnableOnCore]

/-- `removeRunnableOnCore` clears core `c`'s current slot when it held `tid`. -/
theorem removeRunnableOnCore_currentOnCore_self (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.currentOnCore c
      = if st.scheduler.currentOnCore c = some tid then none
        else st.scheduler.currentOnCore c := by
  simp [removeRunnableOnCore]

/-- After `removeRunnableOnCore`, `tid` is not in core `c`'s run queue. -/
theorem removeRunnableOnCore_not_mem_self (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    tid ∉ (removeRunnableOnCore st tid c).scheduler.runQueueOnCore c := by
  rw [removeRunnableOnCore_runQueueOnCore_self]
  exact RunQueue.not_mem_remove_self _ tid

/-- After `removeRunnableOnCore`, `tid` is not core `c`'s current thread. -/
theorem removeRunnableOnCore_currentOnCore_ne_self (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.currentOnCore c ≠ some tid := by
  rw [removeRunnableOnCore_currentOnCore_self]
  split
  · simp
  · assumption

/-- Cross-core frame: `removeRunnableOnCore` on core `c` leaves a *different*
core `c'`'s run-queue slot untouched (per-core locality). -/
theorem removeRunnableOnCore_runQueueOnCore_ne (st : SystemState)
    (tid : SeLe4n.ThreadId) (c c' : CoreId) (h : c ≠ c') :
    (removeRunnableOnCore st tid c).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' := by
  simp [removeRunnableOnCore, SchedulerState.setCurrentOnCore_runQueueOnCore,
    SchedulerState.setRunQueueOnCore_runQueueOnCore_ne, h]

/-- Cross-core frame: `removeRunnableOnCore` on core `c` leaves a *different*
core `c'`'s current slot untouched (per-core locality). -/
theorem removeRunnableOnCore_currentOnCore_ne (st : SystemState)
    (tid : SeLe4n.ThreadId) (c c' : CoreId) (h : c ≠ c') :
    (removeRunnableOnCore st tid c).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  simp [removeRunnableOnCore, SchedulerState.setRunQueueOnCore_currentOnCore,
    SchedulerState.setCurrentOnCore_currentOnCore_ne, h]

-- ============================================================================
-- §12  SM6.A.4 — Per-core caller blocking (plan §3.2 steps 5–6)
-- ============================================================================

/-- WS-SM SM6.A.4 (`endpointCall_perCore_blocking`): on a rendezvous call, the
caller is **blocked on its own core** — removed from `executingCore`'s run
queue and cleared from `executingCore`'s current slot.  The receiver wake
targets the receiver's home core; the caller's descheduling is confined to the
executing core, never disturbing another core's scheduler (the per-core
locality `chooseThreadOnCore executingCore` then picks the next thread). -/
theorem endpointCallOnCore_perCore_blocking
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (recvTcb0 : TCB) (st' st'' st4 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4) :
    caller ∉ (endpointCallOnCore endpointId caller msg executingCore st).1.scheduler.runQueueOnCore executingCore ∧
    (endpointCallOnCore endpointId caller msg executingCore st).1.scheduler.currentOnCore executingCore
      ≠ some caller := by
  rw [endpointCallOnCore_rendezvous_eq endpointId caller msg executingCore st ep receiver
        recvTcb0 st' st'' st4 hSz1 hSz2 hObj hHead hPop hStore hCallerStore]
  exact ⟨removeRunnableOnCore_not_mem_self st4 caller executingCore,
         removeRunnableOnCore_currentOnCore_ne_self st4 caller executingCore⟩

-- ============================================================================
-- §13  SM6.A.6 — Reply-state allocation under the caller-TCB write lock
-- ============================================================================

/-- A `storeTcbIpcStateAndMessage` that succeeds resolves the target TCB and
sets its `ipcState` to the stored value.  (`invExt`-dependent: RobinHood table
lookups need the store well-formedness invariant.) -/
theorem storeTcbIpcStateAndMessage_getTcb?_ipcState
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    ∃ t, st'.getTcb? tid = some t ∧ t.ipcState = ipc := by
  -- The store succeeded, so `tid` resolves to a TCB; lift it through
  -- `tcb_exists_at_target` (whose `_hTcb` parameter shape is inferred, so this
  -- proof writes no raw typed-id object-store lookup of its own).
  obtain ⟨tcb', hTcb'⟩ :=
    storeTcbIpcStateAndMessage_tcb_exists_at_target st st' tid ipc msg hObjInv hStep
      (by cases hL : lookupTcb st tid with
          | none => simp [storeTcbIpcStateAndMessage, hL] at hStep
          | some tcb => exact ⟨tcb, lookupTcb_some_objects st tid tcb hL⟩)
  exact ⟨tcb', (SystemState.getTcb?_eq_some_iff st' tid tcb').mpr hTcb',
         storeTcbIpcStateAndMessage_ipcState_eq st st' tid ipc msg hObjInv hStep tcb' hTcb'⟩

/-- WS-SM SM6.A.6 (`reply allocation under lock-set`): on a rendezvous call the
caller's **reply linkage** is established — its TCB transitions to
`blockedOnReply endpointId (some receiver)`, recording the authorised replier
(`receiver`) so that only that server can later reply (the confused-deputy
gate of `endpointReply`).  This write lands on the caller's TCB, which
`lockSet_endpointCall` covers with a **write** lock (§3.1 footprint;
`endpointCallOnCore_lockSet_correct` confirms it is a permitted, declared
lock), so under the 2PL bracket (`endpointCallOnCore_atomic_under_lockSet`) the
reply-state allocation is serialised against every other core. -/
theorem endpointCallOnCore_reply_linkage_under_lockSet
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (recvTcb0 : TCB) (st' st'' st4 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hObjInv : st.objects.invExt) :
    ∃ t, (endpointCallOnCore endpointId caller msg executingCore st).1.getTcb? caller = some t
      ∧ t.ipcState = .blockedOnReply endpointId (some receiver) := by
  have hInv' : st'.objects.invExt :=
    endpointQueuePopHead_preserves_objects_invExt endpointId true st st' receiver recvTcb0 hObjInv hPop
  have hInv'' : st''.objects.invExt :=
    storeTcbIpcStateAndMessage_preserves_objects_invExt st' st'' receiver .ready (some msg) hInv' hStore
  have hInvW : (wakeThread st'' receiver executingCore).1.objects.invExt :=
    wakeThread_preserves_objects_invExt st'' receiver executingCore hInv''
  obtain ⟨t, hGet, hIpc⟩ :=
    storeTcbIpcStateAndMessage_getTcb?_ipcState (wakeThread st'' receiver executingCore).1 st4
      caller (.blockedOnReply endpointId (some receiver)) none hInvW hCallerStore
  rw [endpointCallOnCore_rendezvous_eq endpointId caller msg executingCore st ep receiver
        recvTcb0 st' st'' st4 hSz1 hSz2 hObj hHead hPop hStore hCallerStore]
  exact ⟨t, hGet, hIpc⟩

-- ============================================================================
-- §14  SM6.A.6 — the caller-TCB write lock IS in the footprint (membership)
-- ============================================================================

/-- Forward `insertOrMerge` membership: a pair already present under a key
distinct from `l` survives the insert (it is neither replaced nor merged). -/
theorem mem_insertOrMerge_of_mem_of_ne (S : LockSet) (l : LockId) (m : AccessMode)
    (p : LockId × AccessMode) (hp : p ∈ S.pairs) (hne : p.fst ≠ l) :
    p ∈ (S.insertOrMerge l m).pairs := by
  unfold LockSet.insertOrMerge
  split
  · exact List.mem_map.mpr ⟨p, hp, by simp [hne]⟩
  · exact List.mem_cons_of_mem _ hp

/-- Forward `insertOrMerge` membership: a fresh key's pair is in the result. -/
theorem self_mem_insertOrMerge_of_not_containsKey (S : LockSet) (l : LockId)
    (m : AccessMode) (h : LockSet.containsKey l S = false) :
    (l, m) ∈ (S.insertOrMerge l m).pairs := by
  unfold LockSet.insertOrMerge
  split
  · exfalso; rename_i hc; rw [h] at hc; exact Bool.noConfusion hc
  · exact List.mem_cons.mpr (Or.inl rfl)

/-- WS-SM SM6.A.6 (the substantive "under lock-set"): the **caller-TCB write
lock** — under which the call writes the caller's reply-blocked state — is a
declared member of the `endpointCall` lock-set footprint.  (The receiver, when
present, is a *distinct* thread from the caller — you do not `Call` yourself — so
its TCB write lock does not displace the caller's.)  Together with
`endpointCallOnCore_reply_linkage_under_lockSet` this makes "reply-state
allocation under lock-set" concrete: the specific lock covering the write is in
the held footprint. -/
theorem lockSet_endpointCall_caller_tcb_write_mem
    (caller : SeLe4n.ThreadId) (cnRoot endpointId : SeLe4n.ObjId)
    (receiver? : Option SeLe4n.ThreadId) (donatedSc? : Option SeLe4n.SchedContextId)
    (hRecvNe : ∀ rt, receiver? = some rt → tcbLock rt ≠ tcbLock caller) :
    (tcbLock caller, AccessMode.write)
      ∈ (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?).pairs := by
  -- Base: the head of the explicit list is the caller-TCB write lock.
  have hBase : (tcbLock caller, AccessMode.write)
      ∈ (lockSetOfList [(tcbLock caller, .write), (cnodeLock cnRoot, .read),
            (endpointLock endpointId, .write)]).pairs := by
    show (tcbLock caller, AccessMode.write)
      ∈ ((((LockSet.empty.insertOrMerge (tcbLock caller) .write).insertOrMerge
          (cnodeLock cnRoot) .read).insertOrMerge (endpointLock endpointId) .write)).pairs
    refine mem_insertOrMerge_of_mem_of_ne _ _ _ _
      (mem_insertOrMerge_of_mem_of_ne _ _ _ _
        (self_mem_insertOrMerge_of_not_containsKey _ _ _ rfl) ?_) ?_
    · show tcbLock caller ≠ cnodeLock cnRoot
      intro h; simp [tcbLock, cnodeLock] at h
    · show tcbLock caller ≠ endpointLock endpointId
      intro h; simp [tcbLock, endpointLock] at h
  -- Receiver extension (distinct TCB) preserves it.
  have hRecv : (tcbLock caller, AccessMode.write)
      ∈ (lockSetExtendOpt
          (lockSetOfList [(tcbLock caller, .write), (cnodeLock cnRoot, .read),
            (endpointLock endpointId, .write)])
          (receiver?.map (fun rt => (tcbLock rt, .write)))).pairs := by
    cases hr : receiver? with
    | none => simp only [lockSetExtendOpt, Option.map_none]; exact hBase
    | some rt =>
      simp only [lockSetExtendOpt, Option.map_some]
      exact mem_insertOrMerge_of_mem_of_ne _ _ _ _ hBase (Ne.symm (hRecvNe rt hr))
  -- SchedContext extension (distinct kind) preserves it.
  unfold lockSet_endpointCall
  cases hsc : donatedSc? with
  | none => simp only [lockSetExtendOpt, Option.map_none]; exact hRecv
  | some sc =>
    simp only [lockSetExtendOpt, Option.map_some]
    refine mem_insertOrMerge_of_mem_of_ne _ _ _ _ hRecv ?_
    show tcbLock caller ≠ schedContextLock sc
    intro h; simp [tcbLock, schedContextLock] at h

end SeLe4n.Kernel
