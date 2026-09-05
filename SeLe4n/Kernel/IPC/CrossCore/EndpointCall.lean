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

/-- WS-RR RR2.9 (frame): descheduling a thread on a core writes that core's run
queue and current slot and nothing else — in particular **no** replenish queue.
The reply path's donation return composes the SM5.H replenishment migration with
this deschedule, so the affinity invariant the migration establishes has to
survive it. -/
@[simp] theorem removeRunnableOnCore_replenishQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c c' : CoreId) :
    (removeRunnableOnCore st tid c).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  simp [removeRunnableOnCore]

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
links the woken caller to it (the folded `linkServerStashedReply` writes
`reply.caller := caller` and clears the server's stash), so the per-object **reply
write-lock** must be in the Call footprint.  `none` for a receiver that did a plain receive (no stash) or when
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
pre-supplied `pendingReceiveReply`, which the folded `linkServerStashedReply` writes
on a server-first rendezvous).  This is the footprint the runtime `withLockSet` bracket
(the SM5.I FFI seam) acquires before invoking
`endpointCallOnCore endpointId caller … executingCore st`. -/
def lockSet_endpointCallOnCore (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    -- **WS-RR RR7.8**: the message, because whether this call installs
    -- capabilities is a property of what it carries.  Defaulted to the empty
    -- message (no registers, and `caps` empty by the field's own default) so
    -- every capless call site is unchanged and reduces definitionally to the
    -- pre-RR7.8 footprint.
    (msg : IpcMessage := { registers := #[] }) : LockSet :=
  lockSet_endpointCall caller cnodeRootObjId endpointId
    (endpointCallReceiver? st endpointId) (endpointCallDonatedSc? st caller)
    (endpointCallServerFirstReply? st endpointId)
    -- **WS-RR RR7.8**: the capability-transfer destination, resolved from the
    -- same pre-state expression `endpointCallWithCaps` reads
    -- (`rendezvousCapsDestination?`), so the declared footprint and the
    -- transition cannot disagree about which CSpace root is written — the
    -- discipline `receiveInstallsCaps` established for the receive side.
    (rendezvousCapsDestination? st endpointId msg)

/-- **WS-RR RR7.8**: the capless resolved call footprint is definitionally the
pre-RR7.8 one, so every statement and fixture taken over the four-argument form
survives unchanged. -/
theorem lockSet_endpointCallOnCore_capless (st : SystemState)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) :
    lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId
      = lockSet_endpointCall caller cnodeRootObjId endpointId
          (endpointCallReceiver? st endpointId) (endpointCallDonatedSc? st caller)
          (endpointCallServerFirstReply? st endpointId) := rfl

/-- **WS-RR RR7.8**: the concrete lock-set a cross-core caps-carrying `.send`
acquires.  The send side had no resolved footprint at all — its capless shape
needed none, since every member was an argument — and the capability-transfer
destination is the first member that has to be read from the state.

The receiver is the endpoint's receive-queue head, as it is for the call; the
destination is `rendezvousCapsDestination?`, the expression
`endpointSendDualWithCaps` itself evaluates. -/
def lockSet_endpointSendOnCore (st : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (msg : IpcMessage := { registers := #[] }) : LockSet :=
  lockSet_endpointSend sender cnodeRootObjId endpointId
    (endpointCallReceiver? st endpointId)
    (rendezvousCapsDestination? st endpointId msg)

-- ============================================================================
-- §3  WithCaps lock-set (plan §3.1)
-- ============================================================================

/-- WS-SM SM6.A.8 (plan §3.1): the lock-set for `endpointCallWithCaps`.

**WS-RR RR7.7: this is `lockSet_endpointCall` at `some destCnodeObjId`**, not a
second definition beside it.  It used to extend the base footprint from out
here, and the two could drift: a member added to the base was inherited, but a
member the *capability transfer* needs had to be remembered twice — which is
how the `stateLevelLock` the CDT write requires came to be on neither.  Folding
the destination into the base as an optional makes "the caps footprint" a value
of the base's own argument, so there is one place where the transfer's
obligations are declared and `lockSet_endpointSend` states the same ones.

What that argument adds is documented at `lockSet_endpointCall`: the
destination CSpace root in write mode (merged with the sender's root by
`AccessMode.lub` when they coincide, so the size bound is unchanged on that
path) and the state-level lock for the CDT maps the install writes. -/
def lockSet_endpointCallWithCaps (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (destCnodeObjId : SeLe4n.ObjId)
    (endpointObjId : SeLe4n.ObjId)
    (receiverTid : Option SeLe4n.ThreadId)
    (donatedScId : Option SeLe4n.SchedContextId)
    -- WS-SM SM6.D (PR #827 review): a server-first `Call` rendezvous through the
    -- WithCaps path links the waiting server's stashed Reply object
    -- (`linkServerStashedReply` writes `reply.caller`); thread `replyId` so that
    -- write is covered by `replyLock rid` inside the WithCaps footprint, keeping
    -- copied reply caps on another core inside the 2PL serialization.
    (replyId : Option SeLe4n.ReplyId := none) : LockSet :=
  lockSet_endpointCall callerTid cnodeRootObjId endpointObjId receiverTid donatedScId
    replyId (some destCnodeObjId)

/-- **WS-RR RR7.7**: the caps footprint *is* the base footprint at `some`, by
`rfl`.  A refactor that reintroduces a second definition breaks this marker at
elaboration rather than at the next audit. -/
theorem lockSet_endpointCallWithCaps_eq_call_some (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId destCnodeObjId endpointObjId : SeLe4n.ObjId)
    (receiverTid : Option SeLe4n.ThreadId)
    (donatedScId : Option SeLe4n.SchedContextId)
    (replyId : Option SeLe4n.ReplyId) :
    lockSet_endpointCallWithCaps callerTid cnodeRootObjId destCnodeObjId endpointObjId
        receiverTid donatedScId replyId
      = lockSet_endpointCall callerTid cnodeRootObjId endpointObjId receiverTid
          donatedScId replyId (some destCnodeObjId) := rfl

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
                  | .ok st4 =>
                      -- WS-SM SM6.D (#7.3b fold): link the caller to the Reply object the
                      -- woken server stashed on its server-first `Recv` and clear the
                      -- stash, atomically (formerly the separate `linkServerFirstCaller`
                      -- dispatch step).  Fails closed when the server provided none.
                      match SystemState.linkServerStashedReply caller receiver st4 with
                      | .error e => (st, .error e)
                      | .ok ((), st5) =>
                          (removeRunnableOnCore st5 caller executingCore,
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
    (receiver : SeLe4n.ThreadId) (recvTcb0 : TCB) (st' st'' st4 st5 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    -- WS-SM SM6.D (#7.3b fold): the server-first reply link is folded into the
    -- transition; the rendezvous reduces only when the link succeeds (a server
    -- with a stashed reply object — the production dispatch always provides one).
    (hLink : SystemState.linkServerStashedReply caller receiver st4 = .ok ((), st5)) :
    endpointCallOnCore endpointId caller msg executingCore st
      = (removeRunnableOnCore st5 caller executingCore,
         .ok (wakeThread st'' receiver executingCore).2) := by
  unfold endpointCallOnCore
  rw [if_neg hSz1, if_neg hSz2]
  have hObjE : st.getEndpoint? endpointId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mpr hObj
  simp only [hObjE, hHead, hPop, hStore, hCallerStore, hLink]

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
    (receiver : SeLe4n.ThreadId) (recvTcb0 recvTcb'' : TCB) (st' st'' st4 st5 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hLink : SystemState.linkServerStashedReply caller receiver st4 = .ok ((), st5))
    (hTcb'' : st''.getTcb? receiver = some recvTcb'')
    (hRemote : determineTargetCore st'' receiver ≠ executingCore) :
    (endpointCallOnCore endpointId caller msg executingCore st).2
      = .ok (some (determineTargetCore st'' receiver, SgiKind.reschedule)) := by
  rw [endpointCallOnCore_rendezvous_eq endpointId caller msg executingCore st ep receiver
        recvTcb0 st' st'' st4 st5 hSz1 hSz2 hObj hHead hPop hStore hCallerStore hLink]
  show Except.ok (wakeThread st'' receiver executingCore).2
      = Except.ok (some (determineTargetCore st'' receiver, SgiKind.reschedule))
  rw [wakeThread_emits_sgi_if_remote st'' receiver executingCore recvTcb'' hTcb'' hRemote]

/-- WS-SM SM6.A.3: dually, a cross-core call whose receiver is *local* (home
core = executing core) surfaces **no** SGI — the local scheduler picks the
newly-runnable receiver up on its next decision. -/
theorem endpointCallOnCore_no_sgi_if_local_receiver
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (recvTcb0 : TCB) (st' st'' st4 st5 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hLink : SystemState.linkServerStashedReply caller receiver st4 = .ok ((), st5))
    (hLocal : determineTargetCore st'' receiver = executingCore) :
    (endpointCallOnCore endpointId caller msg executingCore st).2 = .ok none := by
  rw [endpointCallOnCore_rendezvous_eq endpointId caller msg executingCore st ep receiver
        recvTcb0 st' st'' st4 st5 hSz1 hSz2 hObj hHead hPop hStore hCallerStore hLink]
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
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage := { registers := #[] }) :
    ∀ p ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs,
      p.fst.kind ∈ permittedKinds .call :=
  lockSet_consistent_call caller cnodeRootObjId endpointId
    (endpointCallReceiver? st endpointId) (endpointCallDonatedSc? st caller)
    (endpointCallServerFirstReply? st endpointId)
    (rendezvousCapsDestination? st endpointId msg)

/-- **WS-RR RR7.8**: the send footprint's kinds are permitted too, over every
message — the send side's first resolved-footprint correctness statement. -/
theorem lockSet_endpointSendOnCore_correct
    (st : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage := { registers := #[] }) :
    ∀ p ∈ (lockSet_endpointSendOnCore st endpointId sender cnodeRootObjId msg).pairs,
      p.fst.kind ∈ permittedKinds .send :=
  lockSet_consistent_send sender cnodeRootObjId endpointId
    (endpointCallReceiver? st endpointId)
    (rendezvousCapsDestination? st endpointId msg)

-- ============================================================================
-- §7b  WS-RR RR7.8 — the capability transfer's write set is declared
-- ============================================================================

/-! ## What `ipcUnwrapCaps` writes, and where it is declared

`ipcTransferSingleCap` — the one place an `.ipcTransfer` edge is made — writes
exactly two things on its installing path: the **CNode at
`receiverCspaceRoot`** (through `cspaceInsertSlot`), and the **`SystemState`-level
CDT structure** (`ensureCdtNodeForSlot`'s counter and both keyed maps, plus the
edge itself).  Nothing else in the transfer mutates state.

Both are declared, and each theorem below names one.  The destination is the
resolver's own output, so there is no gap between "the lock the bracket takes"
and "the object the transfer writes": `rendezvousCapsDestination?` is the
expression `endpointSendDualWithCaps` and `endpointCallWithCaps` evaluate
(`endpointSendDualWithCaps_reduces_to_unwrap`,
`endpointCallWithCaps_reduces_to_unwrap`), read from the same pre-state.
-/

/-- **WS-RR RR7.8**: a caps-carrying `.call` holds the destination CSpace root
in **write** mode. -/
theorem lockSet_endpointCallOnCore_covers_capsDestination
    (st : SystemState) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage) (recvRoot : SeLe4n.ObjId)
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot) :
    (cnodeLock recvRoot, AccessMode.write)
      ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs := by
  unfold lockSet_endpointCallOnCore lockSet_endpointCall
  rw [hDest]
  exact mem_write_lockSetExtendOpt _ _ _ (LockSet.mem_insertOrMerge_write_self _ _)

/-- **WS-RR RR7.8**: …and the state-level lock, for the CDT structure the
install writes.  Without this member two transfers into *different* CSpaces have
provably disjoint footprints while read-modify-writing one derivation map. -/
theorem lockSet_endpointCallOnCore_covers_cdt
    (st : SystemState) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage) (recvRoot : SeLe4n.ObjId)
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs := by
  unfold lockSet_endpointCallOnCore lockSet_endpointCall
  rw [hDest]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-RR RR7.8**: the same two members on the send arm — the same transfer,
so the same write set, so the same declaration. -/
theorem lockSet_endpointSendOnCore_covers_capsDestination
    (st : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage) (recvRoot : SeLe4n.ObjId)
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot) :
    (cnodeLock recvRoot, AccessMode.write)
      ∈ (lockSet_endpointSendOnCore st endpointId sender cnodeRootObjId msg).pairs := by
  unfold lockSet_endpointSendOnCore lockSet_endpointSend
  rw [hDest]
  exact mem_write_lockSetExtendOpt _ _ _ (LockSet.mem_insertOrMerge_write_self _ _)

/-- **WS-RR RR7.8**: and the send arm's state-level member. -/
theorem lockSet_endpointSendOnCore_covers_cdt
    (st : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage) (recvRoot : SeLe4n.ObjId)
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_endpointSendOnCore st endpointId sender cnodeRootObjId msg).pairs := by
  unfold lockSet_endpointSendOnCore lockSet_endpointSend
  rw [hDest]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-RR RR7.8, the capstone: every object a caps-carrying send changes is
declared write-mode in the footprint its bracket acquires.**

This is what "the transfer's write set is contained in the declared footprint"
means as a theorem, and what the registered `capTransferReceiverCnode` domain
was registered for.  It composes three facts that were each true and separately
stated: the transfer changes no object but the receiver root
(`ipcUnwrapCaps_preserves_objects_ne`), the root it is handed is the resolver's
own output (`endpointSendDualWithCaps_reduces_to_unwrap`, since RR7.8 both read
the same pre-state), and the resolver's output is declared
(`lockSet_endpointSendOnCore_covers_capsDestination`).

Stated contrapositively — *changed implies declared* — because that is the
shape a 2PL consumer needs: it asks of an object it is about to write whether
it holds the lock, not of a lock whether something used it. -/
theorem endpointSendDualWithCaps_object_writes_declared
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot cnodeRootObjId : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' st'' : SystemState) (recvRoot : SeLe4n.ObjId)
    (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (hSend : endpointSendDual endpointId sender
        { msg with capsGranted := endpointRights.mem .grant } st = .ok ((), st'))
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot)
    (hObjInv : st'.objects.invExt)
    (hStep : endpointSendDualWithCaps endpointId sender msg endpointRights
        senderCspaceRoot receiverSlotBase st = .ok (summary, st''))
    (hChanged : st''.objects[oid]? ≠ st'.objects[oid]?) :
    (cnodeLock oid, AccessMode.write)
      ∈ (lockSet_endpointSendOnCore st endpointId sender cnodeRootObjId msg).pairs := by
  have hUnwrap : ipcUnwrapCaps { msg with capsGranted := endpointRights.mem .grant }
      senderCspaceRoot recvRoot receiverSlotBase (endpointRights.mem .grant) st'
      = .ok (summary, st'') := by
    rw [← endpointSendDualWithCaps_reduces_to_unwrap endpointId sender msg endpointRights
      senderCspaceRoot receiverSlotBase st st' recvRoot hSend hDest]
    exact hStep
  by_cases hEq : oid = recvRoot
  · subst hEq
    exact lockSet_endpointSendOnCore_covers_capsDestination st endpointId sender cnodeRootObjId msg oid hDest
  · exact absurd
      (ipcUnwrapCaps_preserves_objects_ne _ _ _ _ _ _ _ _ _ hEq hObjInv hUnwrap) hChanged

/-- **WS-RR RR7.8**: and the same capstone on the `.call` arm — the same
transfer, reached through the same resolver, declared in the same two
members. -/
theorem endpointCallWithCaps_object_writes_declared
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot cnodeRootObjId : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' st'' : SystemState) (recvRoot : SeLe4n.ObjId)
    (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (hCall : endpointCall endpointId caller
        { msg with capsGranted := endpointRights.mem .grant } st = .ok ((), st'))
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot)
    (hObjInv : st'.objects.invExt)
    (hStep : endpointCallWithCaps endpointId caller msg endpointRights
        callerCspaceRoot receiverSlotBase st = .ok (summary, st''))
    (hChanged : st''.objects[oid]? ≠ st'.objects[oid]?) :
    (cnodeLock oid, AccessMode.write)
      ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs := by
  have hUnwrap : ipcUnwrapCaps { msg with capsGranted := endpointRights.mem .grant }
      callerCspaceRoot recvRoot receiverSlotBase (endpointRights.mem .grant) st'
      = .ok (summary, st'') := by
    rw [← endpointCallWithCaps_reduces_to_unwrap endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase st st' recvRoot hCall hDest]
    exact hStep
  by_cases hEq : oid = recvRoot
  · subst hEq
    exact lockSet_endpointCallOnCore_covers_capsDestination st endpointId caller cnodeRootObjId msg oid hDest
  · exact absurd
      (ipcUnwrapCaps_preserves_objects_ne _ _ _ _ _ _ _ _ _ hEq hObjInv hUnwrap) hChanged

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
`endpointCallWithCaps` lock-set is hierarchically correct — every declared lock
has a kind in `permittedKinds .call`.

**WS-RR RR7.7**: it is now `lockSet_consistent_call` at `some destCnode`, and
that is the whole proof.  Before the fold, this theorem re-derived the
destination CNode's admissibility out here while the base's consistency was
proved in `LockSetTransitions.lean`; the two obligations for one footprint sat
in two files, which is what let the state-level member the CDT write needs be
declared in neither.  `permittedKinds .call` gained `.objStore` in the same cut,
so the ladder is still respected — level 0, acquired first. -/
theorem endpointCallWithCaps_lockSet_correct
    (caller : SeLe4n.ThreadId) (cnRoot destCnode endpointId : SeLe4n.ObjId)
    (receiver? : Option SeLe4n.ThreadId) (donatedSc? : Option SeLe4n.SchedContextId)
    (replyId? : Option SeLe4n.ReplyId := none) :
    ∀ p ∈ (lockSet_endpointCallWithCaps caller cnRoot destCnode endpointId
              receiver? donatedSc? replyId?).pairs,
      p.fst.kind ∈ permittedKinds .call :=
  lockSet_consistent_call caller cnRoot endpointId receiver? donatedSc? replyId?
    (some destCnode)

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
    -- WS-SM SM6.D (PR #827 review): the lock-set carries the optional stashed
    -- reply object so the server-first `linkServerStashedReply` write is inside
    -- the 2PL bracket; the decomposition is generic over the footprint.
    (replyId? : Option SeLe4n.ReplyId := none)
    (s : SystemState) :
    withLockSet (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc? replyId?)
        executingCore (endpointCallOnCore endpointId caller msg executingCore) s
      = (unwindAll executingCore
          (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc? replyId?).lockAcquireSequence.reverse
          (endpointCallOnCore endpointId caller msg executingCore
            (acquireAll executingCore
              (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc? replyId?).lockAcquireSequence s)).1,
         (endpointCallOnCore endpointId caller msg executingCore
            (acquireAll executingCore
              (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc? replyId?).lockAcquireSequence s)).2) :=
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
    (receiver : SeLe4n.ThreadId) (recvTcb0 : TCB) (st' st'' st4 st5 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hLink : SystemState.linkServerStashedReply caller receiver st4 = .ok ((), st5)) :
    caller ∉ (endpointCallOnCore endpointId caller msg executingCore st).1.scheduler.runQueueOnCore executingCore ∧
    (endpointCallOnCore endpointId caller msg executingCore st).1.scheduler.currentOnCore executingCore
      ≠ some caller := by
  rw [endpointCallOnCore_rendezvous_eq endpointId caller msg executingCore st ep receiver
        recvTcb0 st' st'' st4 st5 hSz1 hSz2 hObj hHead hPop hStore hCallerStore hLink]
  exact ⟨removeRunnableOnCore_not_mem_self st5 caller executingCore,
         removeRunnableOnCore_currentOnCore_ne_self st5 caller executingCore⟩

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

/-- Finding F-1: a `storeTcbReceiveComplete` that succeeds resolves the target TCB
and sets its `ipcState` to `.ready`.  Mirror of
`storeTcbIpcStateAndMessage_getTcb?_ipcState`. -/
theorem storeTcbReceiveComplete_getTcb?_ipcState
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    ∃ t, st'.getTcb? tid = some t ∧ t.ipcState = .ready := by
  obtain ⟨tcb', hTcb'⟩ :=
    storeTcbReceiveComplete_tcb_exists_at_target st st' tid msg hObjInv hStep
      (by cases hL : lookupTcb st tid with
          | none => simp [storeTcbReceiveComplete, hL] at hStep
          | some tcb => exact ⟨tcb, lookupTcb_some_objects st tid tcb hL⟩)
  exact ⟨tcb', (SystemState.getTcb?_eq_some_iff st' tid tcb').mpr hTcb',
         storeTcbReceiveComplete_ipcState_eq st st' tid msg hObjInv hStep tcb' hTcb'⟩

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
    (receiver : SeLe4n.ThreadId) (recvTcb0 : TCB) (st' st'' st4 st5 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hLink : SystemState.linkServerStashedReply caller receiver st4 = .ok ((), st5))
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
  have hObjInv4 : st4.objects.invExt :=
    storeTcbIpcStateAndMessage_preserves_objects_invExt (wakeThread st'' receiver executingCore).1 st4
      caller (.blockedOnReply endpointId (some receiver)) none hInvW hCallerStore
  have hT4 : st4.objects[caller.toObjId]? = some (.tcb t) := (SystemState.getTcb?_eq_some_iff st4 caller t).mp hGet
  -- WS-SM SM6.D (#7.3b fold): the server-first reply link sets the caller's
  -- `replyObject` but leaves its `ipcState` (`.blockedOnReply`) intact.
  rw [endpointCallOnCore_rendezvous_eq endpointId caller msg executingCore st ep receiver
        recvTcb0 st' st'' st4 st5 hSz1 hSz2 hObj hHead hPop hStore hCallerStore hLink,
      removeRunnableOnCore_getTcb?]
  obtain ⟨t', hT5⟩ :=
    linkServerStashedReply_tcb_forward st4 st5 caller receiver caller.toObjId t hObjInv4 hLink hT4
  obtain ⟨tb, hTb, hIpcEq⟩ :=
    linkServerStashedReply_tcb_ipcState_backward st4 st5 caller receiver caller t' hObjInv4 hLink hT5
  refine ⟨t', (SystemState.getTcb?_eq_some_iff st5 caller t').mpr hT5, ?_⟩
  have hbt : t = tb := by simpa using hT4.symm.trans hTb
  rw [← hIpcEq, ← hbt]; exact hIpc

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
declared member of the `endpointCall` lock-set footprint.  Together with
`endpointCallOnCore_reply_linkage_under_lockSet` this makes "reply-state
allocation under lock-set" concrete: the specific lock covering the write is in
the held footprint.

**WS-RR RR7.11**: the `hRecvNe` hypothesis is gone.  It said a present receiver
is a thread distinct from the caller — true (you do not `Call` yourself) but
irrelevant to the conclusion, because a coinciding key merges under
`AccessMode.lub` and `.write` is that lattice's top, so the member survives
either way.  A hypothesis that the conclusion does not need is one every caller
has to discharge for nothing, and it made this statement look narrower than the
fact it records.  The general form is
`lockSet_endpointCall_caller_tcb_write_mem_unconditional`, stated over the
capability-transfer arguments too; this is that theorem at the arguments SM6.A
cites it with. -/
theorem lockSet_endpointCall_caller_tcb_write_mem
    (caller : SeLe4n.ThreadId) (cnRoot endpointId : SeLe4n.ObjId)
    (receiver? : Option SeLe4n.ThreadId) (donatedSc? : Option SeLe4n.SchedContextId) :
    (tcbLock caller, AccessMode.write)
      ∈ (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?).pairs :=
  lockSet_endpointCall_caller_tcb_write_mem_unconditional caller cnRoot endpointId
    receiver? donatedSc? none none

-- ============================================================================
-- §9  WS-RR RR2.4 — the scheduler-domain footprint of the cross-core `.call`
-- ============================================================================
--
-- `lockSet_endpointCall` is a `LockSet` over the SM0.I **object** domain
-- (`LockId` = kind × ObjId).  The RR2.2 replenishment migration writes two
-- **per-core replenish-queue** slots, which are not object locks at all — they
-- live in the `SchedLockId` domain, whose whole reason for existing (SM5.A.2)
-- is that a per-core scheduler slot has no `ObjId` to key a `LockId` on.  So
-- "extend the call's footprint with `migrateSchedContextReplenishmentLockSet`"
-- is a statement in the cross-domain `SchedLockId` order, exactly as SM6.E's
-- `cancelDonatedDonationOnCoreSchedLockSet` is for the `.tcbSuspend` arm that
-- runs the same migration.  Both footprints below are `SchedLockId` lists in
-- plan §4.4 ascending order (`object < runQueue < replenishQueue`), each
-- same-kind segment `CoreId`-ascending, so the list *is* the SM3.D acquisition
-- sequence.

/-- WS-RR RR2.4: the scheduler-domain footprint of the cross-core `.call`
**donation** (`applyCallDonationOnCore`) — the object-store table write lock
plus the replenish-queue write locks of **both** migration endpoints (the
donor's home core, purged, and the donee's home core, receiving), emitted in
`CoreId`-ascending order.  On a shared home core the two endpoints coincide, the
migration is a definitional no-op, and the footprint collapses to the single
slot.

Structurally identical to `cancelDonatedDonationOnCoreSchedLockSet`, and for the
same reason: it is the same primitive, moving the same SchedContext's
replenishments between the same two kinds of core. -/
def applyCallDonationOnCoreSchedLockSet (donorHome doneeHome : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  (SchedLockId.object schedObjStoreLockId, .write) ::
    sortedSchedCorePair (fun c => SchedLockId.replenishQueue ⟨c⟩) donorHome doneeHome

/-- RR2.4: every lock in the donation footprint is acquired in **write** mode
(the rebinding writes the object store; the migration writes both queues). -/
theorem applyCallDonationOnCoreSchedLockSet_write_only (donorHome doneeHome : CoreId) :
    ∀ p ∈ applyCallDonationOnCoreSchedLockSet donorHome doneeHome,
      p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [applyCallDonationOnCoreSchedLockSet, List.mem_cons] at hp
  rcases hp with h | hp
  · subst h; rfl
  · unfold sortedSchedCorePair at hp
    split at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp; rfl
    · split at hp <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
         rcases hp with h | h <;> subst h <;> rfl)

/-- RR2.4: the donor's home-core replenish-queue write lock is in the footprint
(the migration's source / purge slot). -/
theorem applyCallDonationOnCoreSchedLockSet_contains_donorHome_write
    (donorHome doneeHome : CoreId) :
    (SchedLockId.replenishQueue ⟨donorHome⟩, Concurrency.AccessMode.write)
      ∈ applyCallDonationOnCoreSchedLockSet donorHome doneeHome := by
  unfold applyCallDonationOnCoreSchedLockSet sortedSchedCorePair
  by_cases hEq : donorHome = doneeHome
  · simp [hEq]
  · by_cases hLe : donorHome ≤ doneeHome <;> simp [hEq, hLe]

/-- RR2.4: the donee's home-core replenish-queue write lock is in the footprint
(the migration's destination). -/
theorem applyCallDonationOnCoreSchedLockSet_contains_doneeHome_write
    (donorHome doneeHome : CoreId) :
    (SchedLockId.replenishQueue ⟨doneeHome⟩, Concurrency.AccessMode.write)
      ∈ applyCallDonationOnCoreSchedLockSet donorHome doneeHome := by
  unfold applyCallDonationOnCoreSchedLockSet sortedSchedCorePair
  by_cases hEq : donorHome = doneeHome
  · simp [hEq]
  · by_cases hLe : donorHome ≤ doneeHome <;> simp [hEq, hLe]

/-- **RR2.4's coverage obligation**: the footprint covers
`migrateSchedContextReplenishmentLockSet` member for member.  This is the
statement that makes the SM3 serializability argument hold across the donation:
the migration writes only the two replenish-queue slots, and the `.call`
footprint declares both, so no write escapes the declared `withLockSet`
bracket. -/
theorem applyCallDonationOnCoreSchedLockSet_covers_migration
    (donorHome doneeHome : CoreId) :
    ∀ p ∈ migrateSchedContextReplenishmentLockSet donorHome doneeHome,
      p ∈ applyCallDonationOnCoreSchedLockSet donorHome doneeHome := by
  intro p hp
  simp only [migrateSchedContextReplenishmentLockSet, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with h | h <;> subst h
  · exact applyCallDonationOnCoreSchedLockSet_contains_donorHome_write donorHome doneeHome
  · exact applyCallDonationOnCoreSchedLockSet_contains_doneeHome_write donorHome doneeHome

/-- RR2.4: the donation footprint's keys form a `SchedLockId`-ascending
acquisition sequence — `object < replenishQueue` across domains, and the two
replenish endpoints in `CoreId`-ascending order. -/
theorem applyCallDonationOnCoreSchedLockSet_pairwise_le (donorHome doneeHome : CoreId) :
    ((applyCallDonationOnCoreSchedLockSet donorHome doneeHome).map (·.1)).Pairwise (· ≤ ·) := by
  have hObjLe : ∀ (c : CoreId), SchedLockId.object schedObjStoreLockId
      ≤ SchedLockId.replenishQueue (⟨c⟩ : ReplenishQueueLockId) :=
    fun c => (SchedLockId.object_lt_replenishQueue _ _).1
  unfold applyCallDonationOnCoreSchedLockSet
  rw [List.map_cons, List.pairwise_cons]
  refine ⟨?_, sortedSchedCorePair_pairwise_le _ _ _ (fun c d h => h)⟩
  intro x hx
  rcases sortedSchedCorePair_map_fst_mem hx with rfl | rfl <;> exact hObjLe _

/-- RR2.4: the donation footprint is within the SM3.D `maxLockSetSize`
cap — three locks at most (object store plus at most two replenish queues).

**WS-RR RR7.11**: stated against the constant, not the numeral. -/
theorem applyCallDonationOnCoreSchedLockSet_size_le_maxLockSetSize
    (donorHome doneeHome : CoreId) :
    (applyCallDonationOnCoreSchedLockSet donorHome doneeHome).length
      ≤ Concurrency.maxLockSetSize := by
  unfold applyCallDonationOnCoreSchedLockSet sortedSchedCorePair Concurrency.maxLockSetSize
  by_cases hEq : donorHome = doneeHome
  · simp [hEq]
  · by_cases hLe : donorHome ≤ doneeHome <;> simp [hEq, hLe]

/-- WS-RR RR2.4: the scheduler-domain footprint of the **whole** cross-core
`.call` dispatch — the union of what its three scheduling effects write:

* the object-store table lock (the rendezvous' TCB / endpoint / CSpace writes
  and the donation's rebinding);
* the **run-queue** write locks of the executing core (the block path's
  `removeRunnableOnCore` deschedule of the caller) and of the receiver's home
  core (the rendezvous' `wakeThread` enqueue) — one entry when they coincide;
* the **replenish-queue** write locks of the two donation endpoints (RR2.2).

**Dynamic chain extension (declared, not static).**  The dispatch also runs
`propagatePipChainCrossCore`, which re-buckets each blocking-chain member's run
queue on *that member's* home core.  The chain is state-discovered, so no static
footprint can enumerate those cores — the SM3.C.11 obligation
(`pipChainStart_tcbSuspend`, `LockSetTransitions.lean`) covers this walk too:
per chain step the walker acquires the member's TCB write lock *and* its
home-core run-queue write lock.  SM6.E's suspend footprint carries the identical
caveat for the identical walk. -/
def endpointCallCrossCoreDispatchSchedLockSet
    (executingCore receiverHome donorHome doneeHome : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  (SchedLockId.object schedObjStoreLockId, .write) ::
  (sortedSchedCorePair (fun c => SchedLockId.runQueue ⟨c⟩) executingCore receiverHome
    ++ sortedSchedCorePair (fun c => SchedLockId.replenishQueue ⟨c⟩) donorHome doneeHome)

/-- RR2.4: the dispatch footprint's keys form a `SchedLockId`-ascending
acquisition sequence — the full three-domain ladder `object < runQueue <
replenishQueue`, each same-kind segment `CoreId`-ascending. -/
theorem endpointCallCrossCoreDispatchSchedLockSet_pairwise_le
    (executingCore receiverHome donorHome doneeHome : CoreId) :
    ((endpointCallCrossCoreDispatchSchedLockSet executingCore receiverHome donorHome
      doneeHome).map (·.1)).Pairwise (· ≤ ·) := by
  have hObjRQ : ∀ (c : CoreId), SchedLockId.object schedObjStoreLockId
      ≤ SchedLockId.runQueue (⟨c⟩ : RunQueueLockId) :=
    fun c => (SchedLockId.object_lt_runQueue _ _).1
  have hObjRep : ∀ (c : CoreId), SchedLockId.object schedObjStoreLockId
      ≤ SchedLockId.replenishQueue (⟨c⟩ : ReplenishQueueLockId) :=
    fun c => (SchedLockId.object_lt_replenishQueue _ _).1
  have hRQRep : ∀ (c d : CoreId), SchedLockId.runQueue (⟨c⟩ : RunQueueLockId)
      ≤ SchedLockId.replenishQueue (⟨d⟩ : ReplenishQueueLockId) :=
    fun c d => (SchedLockId.runQueue_lt_replenishQueue _ _).1
  unfold endpointCallCrossCoreDispatchSchedLockSet
  rw [List.map_cons, List.map_append, List.pairwise_cons]
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases sortedSchedCorePair_map_fst_mem hx with rfl | rfl <;> exact hObjRQ _
    · rcases sortedSchedCorePair_map_fst_mem hx with rfl | rfl <;> exact hObjRep _
  · rw [List.pairwise_append]
    refine ⟨sortedSchedCorePair_pairwise_le _ _ _ (fun c d h => h),
      sortedSchedCorePair_pairwise_le _ _ _ (fun c d h => h), ?_⟩
    intro x hx y hy
    rcases sortedSchedCorePair_map_fst_mem hx with rfl | rfl <;>
    rcases sortedSchedCorePair_map_fst_mem hy with rfl | rfl <;> exact hRQRep _ _

/-- RR2.4: the dispatch footprint is write-only. -/
theorem endpointCallCrossCoreDispatchSchedLockSet_write_only
    (executingCore receiverHome donorHome doneeHome : CoreId) :
    ∀ p ∈ endpointCallCrossCoreDispatchSchedLockSet executingCore receiverHome donorHome doneeHome,
      p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [endpointCallCrossCoreDispatchSchedLockSet, List.mem_cons] at hp
  rcases hp with h | hp
  · subst h; rfl
  · have hAny : ∀ (f : CoreId → SchedLockId) (a b : CoreId),
        p ∈ sortedSchedCorePair f a b → p.2 = Concurrency.AccessMode.write := by
      intro f a b hmem
      unfold sortedSchedCorePair at hmem
      split at hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem; rfl
      · split at hmem <;>
          (simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
           rcases hmem with h | h <;> subst h <;> rfl)
    rcases List.mem_append.mp hp with hp | hp
    · exact hAny _ _ _ hp
    · exact hAny _ _ _ hp

/-- **RR2.4 (dispatch-level coverage)**: the whole-dispatch footprint covers the
donation footprint member for member, hence — by
`applyCallDonationOnCoreSchedLockSet_covers_migration` — the migration's two
replenish-queue write locks.  A `withLockSet` bracket over the dispatch
footprint therefore holds every lock the RR2.2 migration writes under, which is
what keeps the SM3 serializability argument valid across the new write. -/
theorem endpointCallCrossCoreDispatchSchedLockSet_covers_donation
    (executingCore receiverHome donorHome doneeHome : CoreId) :
    ∀ p ∈ applyCallDonationOnCoreSchedLockSet donorHome doneeHome,
      p ∈ endpointCallCrossCoreDispatchSchedLockSet executingCore receiverHome donorHome doneeHome := by
  intro p hp
  simp only [applyCallDonationOnCoreSchedLockSet, List.mem_cons] at hp
  rcases hp with h | hp
  · subst h; exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ hp)

end SeLe4n.Kernel
