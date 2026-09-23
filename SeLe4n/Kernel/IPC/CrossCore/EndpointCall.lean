-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.A: PRODUCTION (LANDED). `endpointCallOnCore` entered the production
-- import closure when the live `.call` dispatch (`API.dispatchWithCap{,Checked}`)
-- was wired through the cross-core call (`endpointCallCrossCoreDispatch`, which
-- builds on this transition). (Former "STATUS: staged" marker replaced with this
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
workstream (plan `docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.2, §5). It
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
-- §1 Per-core caller blocking — `removeRunnableOnCore`
-- ============================================================================
--
-- **`v0.35.158` — the placement primitives live in the scheduler layer.**
-- `removeRunnableOnCore`, `descheduleAt`, `descheduleAtPlacement` and
-- `descheduleAtPlacementCores` were declared here from SM6.A.1 / WS-RR RR8.6 on,
-- with their per-core frames (§11 below) and the `placedCoreOf?` congruences.
-- They now sit in `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, beside
-- `placedCoreOf?`, the resolver the state-resolved form is defined by.  The
-- cancellation reclaim's holder deschedule (`descheduleUnboundHolder`,
-- `Lifecycle/Suspend.lean`) needed the state-resolved removal and could not see
-- it: this module imports the scheduler layer, `Lifecycle/Suspend.lean` imports
-- the scheduler layer, and neither imports the other.  *When a question has one
-- owner and an asker that cannot see it, the owner is in the wrong layer* — a
-- removal from a run queue and a current slot is a scheduler operation, and an
-- IPC cross-core module never had a claim on it.  The `SeLe4n.Kernel` namespace
-- is unchanged, so every reference in the tree is untouched.  The one theorem
-- kept here is the bridge to the single-core `removeRunnable`, which the
-- scheduler layer cannot name.

/-- WS-SM SM6.A.1: `removeRunnableOnCore` at the boot core is exactly the
single-core `removeRunnable` — the backward-compatibility bridge. -/
@[simp] theorem removeRunnableOnCore_bootCoreId (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    removeRunnableOnCore st tid bootCoreId = removeRunnable st tid := rfl

-- ============================================================================
-- §2 Lock-set pre-resolution helpers (plan §3.1 / §4.2)
-- ============================================================================

/-- WS-SM SM6.A.1: the receiver a cross-core call would rendezvous with — the
head of the endpoint's receive queue, if any. Pre-resolved from the pre-state
so the caller can assemble the `lockSet_endpointCall` footprint (the receiver
TCB write lock is present iff a receiver is waiting). -/
def endpointCallReceiver? (st : SystemState) (endpointId : SeLe4n.ObjId) :
    Option SeLe4n.ThreadId :=
  match st.getEndpoint? endpointId with
  | some ep => ep.receiveQ.head
  | none => none

/-- SM8.B.2, relocated to production at **WS-RR RR8.12 Cut C3a**: **the cores a
cross-core endpoint call may write** — the receiver's home core (when a receiver
is waiting, so the call rendezvouses and wakes it) together with the caller's own
core (where the caller is descheduled, on either path).

This is the two-element write set that motivates `observableSlotsConfinedToCores`:
in the interesting case the two are different cores, and no single-core
confinement statement covers the transition.  Both are read from the pre-state,
via `endpointCallReceiver?` above — the same pre-resolution `lockSet_endpointCall`
uses to decide whether the receiver-TCB write lock is in the footprint — so the
declared information-flow write set, the declared 2PL footprint and the
scheduler-domain footprint (`schedLockSet_endpointCallOnCore`, Cut C3a) agree on
which receiver is meant.

Relocated for the reason `endpointSendWriteSet`'s docstring gives: the
scheduler-domain footprint is production and
`InformationFlow/NonInterferenceCrossCore.lean`, where this was declared, is
staged and imports `Kernel.API`.  Its confinement theorem
`endpointCallOnCore_confinedToCores` stays there, because
`observableSlotsConfinedToCores` is that module's predicate. -/
def endpointCallWriteSet (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) : List CoreId :=
  match endpointCallReceiver? st endpointId with
  | some receiver => [determineTargetCore st receiver, executingCore]
  | none => [executingCore]

/-- With a receiver waiting: its home core and the caller's own. -/
@[simp] theorem endpointCallWriteSet_of_receiver (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) (receiver : SeLe4n.ThreadId)
    (h : endpointCallReceiver? st endpointId = some receiver) :
    endpointCallWriteSet st endpointId executingCore
      = [determineTargetCore st receiver, executingCore] := by
  unfold endpointCallWriteSet; rw [h]

/-- With none: the caller's own core alone, where it blocks. -/
@[simp] theorem endpointCallWriteSet_of_no_receiver (st : SystemState)
    (endpointId : SeLe4n.ObjId) (executingCore : CoreId)
    (h : endpointCallReceiver? st endpointId = none) :
    endpointCallWriteSet st endpointId executingCore = [executingCore] := by
  unfold endpointCallWriteSet; rw [h]

/-- The caller's own core is a member on both paths — it is descheduled there
whether it rendezvouses or blocks. -/
theorem executingCore_mem_endpointCallWriteSet (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) :
    executingCore ∈ endpointCallWriteSet st endpointId executingCore := by
  unfold endpointCallWriteSet
  split <;> simp

/-- **WS-OD OD3.11**: the `.send` / `.call` instance of the queue-structure
neighbour -- those arms pop the **receive** queue and block on the **send**
queue.

Derived from `endpointCallReceiver?` above, the resolver the arm's receiver
member already comes from, so the footprint and the transition cannot disagree
about which branch this call takes: a receiver resolved is a rendezvous, none is
a block. -/
def sendSideQueueStructureNeighbor? (st : SystemState) (endpointId : SeLe4n.ObjId) :
    Option SeLe4n.ThreadId :=
  endpointQueueStructureNeighbor? st (endpointCallReceiver? st endpointId)
    ((st.getEndpoint? endpointId).bind (·.sendQ.tail))

/-- **WS-OD OD3.11**: with a receiver waiting, the neighbour is that receiver's
successor -- the thread the pop promotes to head. -/
theorem sendSideQueueStructureNeighbor?_rendezvous (st : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (tcb : TCB)
    (hRecv : endpointCallReceiver? st endpointId = some receiver)
    (hTcb : st.getTcb? receiver = some tcb) :
    sendSideQueueStructureNeighbor? st endpointId = tcb.queueNext := by
  unfold sendSideQueueStructureNeighbor?
  rw [hRecv]
  exact endpointQueueStructureNeighbor?_rendezvous st receiver tcb _ hTcb

/-- **WS-OD OD3.11**: with none, it is the send queue's old tail -- the thread
the enqueue relinks. -/
theorem sendSideQueueStructureNeighbor?_block (st : SystemState)
    (endpointId : SeLe4n.ObjId)
    (hNone : endpointCallReceiver? st endpointId = none) :
    sendSideQueueStructureNeighbor? st endpointId
      = (st.getEndpoint? endpointId).bind (·.sendQ.tail) := by
  unfold sendSideQueueStructureNeighbor?; rw [hNone]; rfl

/-- WS-SM SM6.A.5: the SchedContext the caller would donate on this call — the
context it *effectively holds*, bound or donated, if any.  Only an `.unbound`
caller donates nothing, so the SC write lock is in the footprint exactly when the
caller has a context to hand on.

**WS-OD OD4.2**: the `.donated` arm used to answer `none`, matching the
pre-OD4 `applyCallDonation`, which donated only from a `.bound` caller.  With
the guard widened to the effective context the footprint follows in the same
cut — a footprint narrower than its transition is *false*, and this one would
have omitted the SchedContext the push rebinds at every call depth ≥ 2.  Both
sides now read `SchedContextBinding.scId?`, so neither can widen without the
other. -/
def endpointCallDonatedSc? (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) : Option SeLe4n.SchedContextId :=
  (endpointCallReceiver? st endpointId).bind fun receiver =>
    callDonationSchedContext? st caller receiver

/-- WS-SM SM6.D (PR #822 review): the server-first stashed Reply object this call
links, if any. On a **server-first** `Call` rendezvous the popped receiver is a
server already `.blockedOnReceive` having pre-supplied a reply object via
`endpoint_receive_with_reply` (`TCB.pendingReceiveReply = some rid`); the rendezvous
links the woken caller to it (the folded `linkServerStashedReply` writes
`reply.caller := caller` and clears the server's stash), so the per-object **reply
write-lock** must be in the Call footprint. `none` for a receiver that did a plain receive (no stash) or when
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
on a server-first rendezvous). This is the footprint the runtime `withLockSet` bracket
(the SM5.I FFI seam) acquires before invoking
`endpointCallOnCore endpointId caller … executingCore st`. -/
def lockSet_endpointCallOnCore (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    -- **WS-RR RR7.8**: the message, because whether this call installs
    -- capabilities is a property of what it carries. Defaulted to the empty
    -- message (no registers, and `caps` empty by the field's own default) so
    -- every capless call site is unchanged and reduces definitionally to the
    -- pre-RR7.8 footprint.
    (msg : IpcMessage := { registers := #[] }) : LockSet :=
  lockSet_endpointCall caller cnodeRootObjId endpointId
    (endpointCallReceiver? st endpointId) (endpointCallDonatedSc? st endpointId caller)
    (endpointCallServerFirstReply? st endpointId)
    -- **WS-RR RR7.8**: the capability-transfer destination, resolved from the
    -- same pre-state expression `endpointCallWithCaps` reads
    -- (`rendezvousCapsDestination?`), so the declared footprint and the
    -- transition cannot disagree about which CSpace root is written — the
    -- discipline `receiveInstallsCaps` established for the receive side.
    (rendezvousCapsDestination? st endpointId msg)
    -- **WS-OD OD3.11**: and the queue-structure neighbour, resolved from the
    -- same branch the transition takes.
    (sendSideQueueStructureNeighbor? st endpointId)
    -- **WS-OD (`v0.35.4`)**: and the old head of the donated context -- the
    -- frame the push rewrites below the one it adds -- read off the very
    -- context `endpointCallDonatedSc?` resolves, so the footprint and the push
    -- cannot disagree about which stack is extended.
    ((endpointCallDonatedSc? st endpointId caller).bind (replyStackHead? st))

/-- **WS-RR RR7.8**: the capless resolved call footprint is definitionally the
pre-RR7.8 one, so every statement and fixture taken over the four-argument form
survives unchanged. -/
theorem lockSet_endpointCallOnCore_capless (st : SystemState)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) :
    lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId
      = lockSet_endpointCall caller cnodeRootObjId endpointId
          (endpointCallReceiver? st endpointId) (endpointCallDonatedSc? st endpointId caller)
          (endpointCallServerFirstReply? st endpointId) none
          -- **WS-OD OD3.11**: "capless" is about the *message*, not about the
          -- queue.  A call that carries no capabilities still pops or enqueues,
          -- so the neighbour member is resolved here rather than `none`.
          (sendSideQueueStructureNeighbor? st endpointId)
          -- **WS-OD (`v0.35.4`)**: and the old head, for the same reason.
          ((endpointCallDonatedSc? st endpointId caller).bind (replyStackHead? st)) := rfl

/-- **WS-RR RR7.8**: the concrete lock-set a cross-core caps-carrying `.send`
acquires. The send side had no resolved footprint at all — its capless shape
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
    -- **WS-OD OD3.11**: and the queue-structure neighbour.
    (sendSideQueueStructureNeighbor? st endpointId)

-- ============================================================================
-- §3 WithCaps lock-set (plan §3.1)
-- ============================================================================

/-- WS-SM SM6.A.8 (plan §3.1): the lock-set for `endpointCallWithCaps`.

**WS-RR RR7.7: this is `lockSet_endpointCall` at `some destCnodeObjId`**, not a
second definition beside it. It used to extend the base footprint from out
here, and the two could drift: a member added to the base was inherited, but a
member the *capability transfer* needs had to be remembered twice — which is
how the `stateLevelLock` the CDT write requires came to be on neither. Folding
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
    (replyId : Option SeLe4n.ReplyId := none)
    -- **WS-OD OD3.11**: and the queue-structure neighbour, threaded through for
    -- the same reason -- the caps footprint *is* the base footprint at `some
    -- destCnodeObjId`, so every member the base declares it declares too.
    (queueNeighbour : Option SeLe4n.ThreadId := none)
    -- **WS-OD (`v0.35.4`)**: and the old head the donation push rewrites.
    (donationOldHeadReplyId : Option SeLe4n.ReplyId := none) : LockSet :=
  lockSet_endpointCall callerTid cnodeRootObjId endpointObjId receiverTid donatedScId
    replyId (some destCnodeObjId) queueNeighbour donationOldHeadReplyId

/-- **WS-RR RR7.7**: the caps footprint *is* the base footprint at `some`, by
`rfl`. A refactor that reintroduces a second definition breaks this marker at
elaboration rather than at the next audit. -/
theorem lockSet_endpointCallWithCaps_eq_call_some (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId destCnodeObjId endpointObjId : SeLe4n.ObjId)
    (receiverTid : Option SeLe4n.ThreadId)
    (donatedScId : Option SeLe4n.SchedContextId)
    (replyId : Option SeLe4n.ReplyId)
    (queueNeighbour : Option SeLe4n.ThreadId)
    (donationOldHeadReplyId : Option SeLe4n.ReplyId) :
    lockSet_endpointCallWithCaps callerTid cnodeRootObjId destCnodeObjId endpointObjId
        receiverTid donatedScId replyId queueNeighbour donationOldHeadReplyId
      = lockSet_endpointCall callerTid cnodeRootObjId endpointObjId receiverTid
          donatedScId replyId (some destCnodeObjId) queueNeighbour
          donationOldHeadReplyId := rfl

-- ============================================================================
-- §4 The cross-core endpoint-call transition (plan §3.2)
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
                      -- dispatch step). Fails closed when the server provided none.
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
      -- `none` for both an absent object and a wrong-kinded one, so the
      -- presence question is asked of the kind-agnostic accessor `getObject?`
      -- -- a present-but-wrong-kind object fails with `.invalidCapability`, a
      -- genuinely absent one with `.objectNotFound`.  Reading the store raw
      -- here would have been the very pattern the comment claimed to avoid.
      if (st.getObject? endpointId).isSome then (st, .error .invalidCapability)
      else (st, .error .objectNotFound)

-- ============================================================================
-- §5 Path reduction lemmas (full characterisation of each control path)
-- ============================================================================

/-- WS-SM SM6.A.1: full reduction of the **rendezvous** path (a receiver is
waiting on the endpoint). The post-state is the caller-blocked state with the
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
enqueues on the endpoint's send queue as `blockedOnCall`). No wake occurs, so
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
-- §6 SM6.A.3 — Cross-core wake: SGI emission (plan Theorem 3.2.1)
-- ============================================================================

/-- **WS-RR RR8.12 Cut C3a (frame)**: the bare cross-core call writes **no
replenish queue** on any path.  Its scheduler writes are the receiver's wake on a
rendezvous and the caller's own deschedule on both paths, and neither touches a
replenish queue; every store around them writes objects alone.  The `.call`
footprint's replenish segment is the donation's, and this is the frame that
licenses it — a footprint that declared nothing for a leg that migrated would be
false. -/
theorem endpointCallOnCore_replenishQueueOnCore (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (c : CoreId) :
    (endpointCallOnCore endpointId caller msg executingCore st).1.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold endpointCallOnCore
  split
  · rfl
  · split
    · rfl
    · cases hEp : st.getEndpoint? endpointId with
      | none => simp only []; split <;> rfl
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none =>
          simp only []
          cases hEnq : endpointQueueEnqueue endpointId false caller st with
          | error e => rfl
          | ok st' =>
            simp only []
            cases hStore : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId)
                (some msg) with
            | error e => rfl
            | ok st'' =>
              simp only [removeRunnableOnCore_replenishQueueOnCore]
              rw [storeTcbIpcStateAndMessage_scheduler_eq st' st'' caller _ _ hStore,
                endpointQueueEnqueue_scheduler_eq endpointId false caller st st' hEnq]
        | some _ =>
          simp only []
          cases hPop : endpointQueuePopHead endpointId true st with
          | error e => rfl
          | ok triple =>
            obtain ⟨receiver, _headTcb, st'⟩ := triple
            simp only []
            cases hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) with
            | error e => rfl
            | ok st'' =>
              simp only []
              cases hStore2 : storeTcbIpcStateAndMessage
                  (wakeThread st'' receiver executingCore).1 caller
                  (.blockedOnReply endpointId (some receiver)) none with
              | error e => rfl
              | ok st4 =>
                simp only []
                cases hLink : SystemState.linkServerStashedReply caller receiver st4 with
                | error e => rfl
                | ok pr =>
                  obtain ⟨_, st5⟩ := pr
                  simp only [removeRunnableOnCore_replenishQueueOnCore]
                  rw [linkServerStashedReply_scheduler_eq st4 st5 caller receiver hLink,
                    storeTcbIpcStateAndMessage_scheduler_eq _ st4 caller _ _ hStore2,
                    wakeThread_replenishQueueOnCore,
                    storeTcbIpcStateAndMessage_scheduler_eq st' st'' receiver _ _ hStore,
                    endpointQueuePopHead_scheduler_eq endpointId true st st' receiver hPop]

/-- WS-SM SM6.A.3 (plan §3.2 Theorem 3.2.1,
`endpointCall_emits_sgi_if_remote_receiver`). When a cross-core `endpointCall`
rendezvous unblocks a receiver whose home core differs from the executing core,
the operation surfaces a `.reschedule` SGI targeting the receiver's core — the
cross-core poke the runtime fires after the state commit. The target core is
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
so there is no cross-core poke. Completes the SGI characterisation: a call pokes
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
-- §7 SM6.A.2 — `endpointCall` lock-set correctness
-- ============================================================================

/-- WS-SM SM6.A.2 (`endpointCall_lockSet_correct`): the `endpointCall`
lock-set is **hierarchically correct** — every lock it declares has a kind in
`permittedKinds .call` (so the acquisitions respect the SM0.I lock ladder), and
its keys are duplicate-free (the SM3.B well-formedness `LockSet` carries by
construction). Together these are the structural soundness conditions the
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
kind permitted for `.call`. This is the form the runtime acquisition consumes,
so its correctness is a corollary of the parametric `lockSet_consistent_call`. -/
theorem lockSet_endpointCallOnCore_correct
    (st : SystemState) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage := { registers := #[] }) :
    ∀ p ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs,
      p.fst.kind ∈ permittedKinds .call :=
  lockSet_consistent_call caller cnodeRootObjId endpointId
    (endpointCallReceiver? st endpointId) (endpointCallDonatedSc? st endpointId caller)
    (endpointCallServerFirstReply? st endpointId)
    (rendezvousCapsDestination? st endpointId msg)
    (sendSideQueueStructureNeighbor? st endpointId)
    ((endpointCallDonatedSc? st endpointId caller).bind (replyStackHead? st))

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
    (sendSideQueueStructureNeighbor? st endpointId)

-- ============================================================================
-- §7b WS-RR RR7.8 — the capability transfer's write set is declared
-- ============================================================================

/-! ## What `ipcUnwrapCaps` writes, and where it is declared

`ipcTransferSingleCap` — the one place an `.ipcTransfer` edge is made — writes
exactly two things on its installing path: the **CNode at
`receiverCspaceRoot`** (through `cspaceInsertSlot`), and the **`SystemState`-level
CDT structure** (`ensureCdtNodeForSlot`'s counter and both keyed maps, plus the
edge itself). Nothing else in the transfer mutates state.

Both are declared, and each theorem below names one. The destination is the
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
  -- WS-OD OD3.11: one more extension outside (the queue-structure neighbour).
  exact mem_write_lockSetExtendOpt _ _ _
    (mem_write_lockSetExtendOpt _ _ _ (LockSet.mem_insertOrMerge_write_self _ _))

/-- **WS-RR RR7.8**: …and the state-level lock, for the CDT structure the
install writes. Without this member two transfers into *different* CSpaces have
provably disjoint footprints while read-modify-writing one derivation map. -/
theorem lockSet_endpointCallOnCore_covers_cdt
    (st : SystemState) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage) (recvRoot : SeLe4n.ObjId)
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs := by
  unfold lockSet_endpointCallOnCore lockSet_endpointCall
  rw [hDest]
  exact mem_write_lockSetExtendOpt _ _ _ (LockSet.mem_insertOrMerge_write_self _ _)

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
  -- WS-OD OD3.11: one more extension outside (the queue-structure neighbour).
  exact mem_write_lockSetExtendOpt _ _ _
    (mem_write_lockSetExtendOpt _ _ _ (LockSet.mem_insertOrMerge_write_self _ _))

/-- **WS-OD OD3.11**: the queue-structure neighbour is a declared **write**
member of the resolved `.call` footprint.

This is the finding this row closes.  A `.call` either pops the endpoint's
receive queue -- which relinks the popped receiver's successor into the head --
or enqueues the caller on the send queue, which relinks that queue's old tail.
Exactly one of those TCBs is written on any given call, and the footprint named
neither, so a `.call` on one core and a `.tcbSuspend` of the affected neighbour
on another had provably disjoint footprints while both writing it.

Stated over the resolver rather than over a supplied thread: which of the two
branches this call takes is a property of the pre-state, and the resolver reads
it from the same expression the transition branches on. -/
theorem lockSet_endpointCallOnCore_covers_queueNeighbour
    (st : SystemState) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage) (q : SeLe4n.ThreadId)
    (hq : sendSideQueueStructureNeighbor? st endpointId = some q) :
    (tcbLock q, AccessMode.write)
      ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs := by
  unfold lockSet_endpointCallOnCore lockSet_endpointCall
  rw [hq]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-OD OD4.7 / `v0.35.4`: the resolved `.call` footprint declares every
object the donation push writes.**

OD4.1 gave `donateSchedContext` two more stores than it had: the scheduling
context also carries the stack head `scReply`, and the Reply the new frame *is*
gets its links.  OD4.7 found the push's four keys were declared members already:

* the scheduling context, by `endpointCallDonatedSc?` -- declared since SM6.A.5,
  and (OD4.2) widened to the caller's *effective* context, so it names the right
  one at every chain depth.  The old head the push reads is read out of that same
  object, under that same write lock.
* the Reply, by `endpointCallServerFirstReply?` -- declared since SM6.D for the
  rendezvous's own `linkServerStashedReply` write.  `endpointCall`'s rendezvous
  arm fails closed unless the woken server stashed a Reply and links it to *this*
  caller, so the Reply the push then finds in `TCB.replyObject` is that one.
* the caller's TCB and the receiver's TCB, which the rendezvous writes anyway.

OD4.7 concluded that a push adds no member.  That was true of the singly linked
push and is **false** of the doubly linked one (`v0.35.4`):
`storeDonationFramePush` also rewrites the *old head* -- the frame below the one
it adds now points up at it (`next := .frame pushRid`) -- and that Reply was
named by no member.  It is declared as the fifth key
(`lockSet_endpointCallOnCore_covers_donationOldHead`, below), resolved by
`replyStackHead?` on the very context `endpointCallDonatedSc?` names, and it is
one of the two members the ceiling moved for at that cut.  The four OD4.7 named
are stated here as they were. -/
theorem lockSet_endpointCallOnCore_covers_donationPush
    (st : SystemState) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage)
    (scId : SeLe4n.SchedContextId) (rid : SeLe4n.ReplyId) (receiver : SeLe4n.ThreadId)
    (hSc : endpointCallDonatedSc? st endpointId caller = some scId)
    (hRid : endpointCallServerFirstReply? st endpointId = some rid)
    (hRecv : endpointCallReceiver? st endpointId = some receiver) :
    (schedContextLock scId, AccessMode.write)
        ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs ∧
    (replyLock rid, AccessMode.write)
        ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs ∧
    (tcbLock caller, AccessMode.write)
        ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs ∧
    (tcbLock receiver, AccessMode.write)
        ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs := by
  unfold lockSet_endpointCallOnCore
  rw [hSc, hRid, hRecv]
  exact ⟨lockSet_endpointCall_donatedSc_write_mem _ _ _ _ _ _ _ _ _,
    lockSet_endpointCall_reply_write_mem _ _ _ _ _ _ _ _ _,
    lockSet_endpointCall_caller_tcb_write_mem_unconditional _ _ _ _ _ _ _ _ _,
    lockSet_endpointCall_receiver_tcb_write_mem _ _ _ _ _ _ _ _ _⟩

/-- **WS-OD (`v0.35.4`)**: the fifth key of the push -- the donated context's
old head, rewritten by `storeDonationFramePush` -- is a declared write of the
resolved `.call` footprint whenever the context heads a frame.  Stated over the
two resolvers the member is derived from, so it is a statement about the arm
rather than about an argument value. -/
theorem lockSet_endpointCallOnCore_covers_donationOldHead
    (st : SystemState) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage)
    (scId : SeLe4n.SchedContextId) (oldHead : SeLe4n.ReplyId)
    (hSc : endpointCallDonatedSc? st endpointId caller = some scId)
    (hOld : replyStackHead? st scId = some oldHead) :
    (replyLock oldHead, AccessMode.write)
        ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs := by
  unfold lockSet_endpointCallOnCore
  rw [hSc]
  have h2 : Option.bind (some scId) (replyStackHead? st) = some oldHead := hOld
  rw [h2]
  exact lockSet_endpointCall_donationOldHead_write_mem _ _ _ _ _ _ _ _ _

/-- **WS-RR RR8.16 (`v0.35.189`)**: the member is `none` on the arm that donates
nothing because there is nobody to donate to.

The blocking arm of a `.call` has no receiver at all, so the resolver answers
`none` and the footprint declares no SchedContext write lock and no old-head
Reply lock — where until `v0.35.189` it declared both from the caller's own
binding, whatever the endpoint held. -/
@[simp] theorem endpointCallDonatedSc?_of_no_receiver (st : SystemState)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (h : endpointCallReceiver? st endpointId = none) :
    endpointCallDonatedSc? st endpointId caller = none := by
  unfold endpointCallDonatedSc?
  rw [h]
  rfl

/-- **WS-RR RR8.16 (`v0.35.189`)**: and at a resolved receiver the member IS the
donation's own guard — which is the whole content of the narrowing.

`callDonationSchedContext?` is what `applyCallDonation` branches on, so the
footprint and the transition now ask one question of one pair of threads; before
this the member was the caller's `scId?` alone, with no test that the receiver is
passive, and a `.call` to a *bound* receiver declared a SchedContext write lock
for a donation the transition declines. -/
@[simp] theorem endpointCallDonatedSc?_of_receiver (st : SystemState)
    (endpointId : SeLe4n.ObjId) (caller receiver : SeLe4n.ThreadId)
    (h : endpointCallReceiver? st endpointId = some receiver) :
    endpointCallDonatedSc? st endpointId caller
      = callDonationSchedContext? st caller receiver := by
  unfold endpointCallDonatedSc?
  rw [h]
  rfl

/-- **WS-OD OD4.7**: and the resolver names the *effective* context at every
depth, so the member above is the one a depth-≥ 2 push writes.

The guard reads `SchedContextBinding.scId?`, which answers for a `.donated`
caller exactly as it does for a `.bound` one.  Before OD4.2 it answered `none`
there -- a footprint narrower than its transition, which is *false* -- so this is
the statement that the two widened together.

**WS-RR RR8.16 (`v0.35.189`)**: restated over the narrowed resolver, so it now
carries the receiver premises too — the receiver must exist and be passive, which
is what makes the declaration exact rather than merely wide.  It is
`callDonationSchedContext?_of_donated_caller` at this arm's own receiver; the
lookup moved from `getTcb?` to `lookupTcb`, which differs only on a reserved id,
where the transition refuses. -/
theorem endpointCallDonatedSc?_of_donated (st : SystemState)
    (endpointId : SeLe4n.ObjId) (caller receiver : SeLe4n.ThreadId)
    (tcb rTcb : TCB) (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (hRecv : endpointCallReceiver? st endpointId = some receiver)
    (hR : lookupTcb st receiver = some rTcb)
    (hRB : rTcb.schedContextBinding = .unbound)
    (hT : lookupTcb st caller = some tcb)
    (hB : tcb.schedContextBinding = .donated scId owner) :
    endpointCallDonatedSc? st endpointId caller = some scId := by
  rw [endpointCallDonatedSc?_of_receiver st endpointId caller receiver hRecv]
  exact callDonationSchedContext?_of_donated_caller st caller receiver scId owner
    tcb rTcb hR hRB hT hB

/-- **WS-OD OD3.11**: and on the send arm -- the same two primitives, so the
same neighbour and the same declaration. -/
theorem lockSet_endpointSendOnCore_covers_queueNeighbour
    (st : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage) (q : SeLe4n.ThreadId)
    (hq : sendSideQueueStructureNeighbor? st endpointId = some q) :
    (tcbLock q, AccessMode.write)
      ∈ (lockSet_endpointSendOnCore st endpointId sender cnodeRootObjId msg).pairs := by
  unfold lockSet_endpointSendOnCore lockSet_endpointSend
  rw [hq]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-RR RR7.8**: and the send arm's state-level member. -/
theorem lockSet_endpointSendOnCore_covers_cdt
    (st : SystemState) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage) (recvRoot : SeLe4n.ObjId)
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_endpointSendOnCore st endpointId sender cnodeRootObjId msg).pairs := by
  unfold lockSet_endpointSendOnCore lockSet_endpointSend
  rw [hDest]
  exact mem_write_lockSetExtendOpt _ _ _ (LockSet.mem_insertOrMerge_write_self _ _)

/-- **WS-RR RR7.8, the capstone: every object a caps-carrying send changes is
declared write-mode in the footprint its bracket acquires.**

This is what "the transfer's write set is contained in the declared footprint"
means as a theorem, and what the registered `capTransferReceiverCnode` domain
was registered for. It composes three facts that were each true and separately
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
    (cnodeRootObjId : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' st'' : SystemState) (recvRoot : SeLe4n.ObjId)
    (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (hSend : endpointSendDual endpointId sender
        { msg with capsGranted := endpointRights.mem .grant } st = .ok ((), st'))
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot)
    (hObjInv : st'.objects.invExt)
    (hStep : endpointSendDualWithCaps endpointId sender msg endpointRights
        receiverSlotBase st = .ok (summary, st''))
    (hChanged : st''.objects[oid]? ≠ st'.objects[oid]?) :
    (cnodeLock oid, AccessMode.write)
      ∈ (lockSet_endpointSendOnCore st endpointId sender cnodeRootObjId msg).pairs := by
  have hUnwrap : ipcUnwrapCaps { msg with capsGranted := endpointRights.mem .grant }
      recvRoot receiverSlotBase (endpointRights.mem .grant) st'
      = .ok (summary, st'') := by
    rw [← endpointSendDualWithCaps_reduces_to_unwrap endpointId sender msg endpointRights
      receiverSlotBase st st' recvRoot hSend hDest]
    exact hStep
  by_cases hEq : oid = recvRoot
  · subst hEq
    exact lockSet_endpointSendOnCore_covers_capsDestination st endpointId sender cnodeRootObjId msg oid hDest
  · exact absurd
      (ipcUnwrapCaps_preserves_objects_ne _ _ _ _ _ _ _ _ hEq hObjInv hUnwrap) hChanged

/-- **WS-RR RR7.8**: and the same capstone on the `.call` arm — the same
transfer, reached through the same resolver, declared in the same two
members. -/
theorem endpointCallWithCaps_object_writes_declared
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (cnodeRootObjId : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' st'' : SystemState) (recvRoot : SeLe4n.ObjId)
    (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (hCall : endpointCall endpointId caller
        { msg with capsGranted := endpointRights.mem .grant } st = .ok ((), st'))
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot)
    (hObjInv : st'.objects.invExt)
    (hStep : endpointCallWithCaps endpointId caller msg endpointRights
        receiverSlotBase st = .ok (summary, st''))
    (hChanged : st''.objects[oid]? ≠ st'.objects[oid]?) :
    (cnodeLock oid, AccessMode.write)
      ∈ (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).pairs := by
  have hUnwrap : ipcUnwrapCaps { msg with capsGranted := endpointRights.mem .grant }
      recvRoot receiverSlotBase (endpointRights.mem .grant) st'
      = .ok (summary, st'') := by
    rw [← endpointCallWithCaps_reduces_to_unwrap endpointId caller msg endpointRights
      receiverSlotBase st st' recvRoot hCall hDest]
    exact hStep
  by_cases hEq : oid = recvRoot
  · subst hEq
    exact lockSet_endpointCallOnCore_covers_capsDestination st endpointId caller cnodeRootObjId msg oid hDest
  · exact absurd
      (ipcUnwrapCaps_preserves_objects_ne _ _ _ _ _ _ _ _ hEq hObjInv hUnwrap) hChanged

-- ============================================================================
-- §8 SM6.A.5 — Donation-chain lock-set extension
-- ============================================================================

/-- WS-SM SM6.A.5 (plan §4.3): the cross-core donation-chain lock-set
extension. When the caller donates a SchedContext on the call, the
`endpointCall` lock-set is the non-donating lock-set extended with the donated
SchedContext's **write** lock — so the SC migration (`applyCallDonation`
rebinding `boundThread` across cores, SM5.H.4) runs under a held SC write lock,
serialised against every other core.

**WS-OD OD3.5: and with the state-level lock**, because `donateSchedContext`
does not stop at the object stores.  Its final step is
`scThreadIndexAdd`/`scThreadIndexRemove` on `SystemState.scThreadIndex`, an
`RHTable` whose insert may rehash and back-shift the whole table — so it does
not decompose by object, and the SM3.A.10 declared subject for such structure is
`stateLevelLock`.  The extension is therefore **two** members, not one; saying
"exactly the non-donating set plus the SC lock", as this theorem did, was a
statement about the object stores read as a statement about the operation. -/
theorem lockSet_endpointCall_donation_extension
    (caller : SeLe4n.ThreadId) (cnRoot endpointId : SeLe4n.ObjId)
    (receiver? : Option SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) :
    lockSet_endpointCall caller cnRoot endpointId receiver? (some scId)
      = lockSetExtendOpt
          (lockSetExtendOpt
            (lockSet_endpointCall caller cnRoot endpointId receiver? none)
            (some (schedContextLock scId, .write)))
          (some (stateLevelLock, .write)) := by
  unfold lockSet_endpointCall
  rfl

-- ============================================================================
-- §9 SM6.A.8 — `endpointCallWithCaps` lock-set correctness
-- ============================================================================

/-- WS-SM SM6.A.8 (`endpointCallWithCaps_lockSet_correct`): the
`endpointCallWithCaps` lock-set is hierarchically correct — every declared lock
has a kind in `permittedKinds .call`.

**WS-RR RR7.7**: it is now `lockSet_consistent_call` at `some destCnode`, and
that is the whole proof. Before the fold, this theorem re-derived the
destination CNode's admissibility out here while the base's consistency was
proved in `LockSetTransitions.lean`; the two obligations for one footprint sat
in two files, which is what let the state-level member the CDT write needs be
declared in neither. `permittedKinds .call` gained `.objStore` in the same cut,
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
-- §10 SM6.A.9 — `endpointCall` atomicity under its lock-set (2PL)
-- ============================================================================

/-- WS-SM SM6.A.9 (`endpointCall_atomic_under_lockSet`, plan §3.4 / Theorem
2.1.10): under its `endpointCall` lock-set the cross-core transition is a
single two-phase-locked atomic step — wrapping `endpointCallOnCore` in
`withLockSet` decomposes deterministically into the acquire fold, the
transition, and the release fold. No partial intermediate is observable to a
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
-- §11 `removeRunnableOnCore` frame lemmas — relocated (`v0.35.158`)
-- ============================================================================
--
-- The frame family of the placement primitives (`_preserves_objects`,
-- `_getTcb?`, `_runQueueOnCore_self` / `_ne`, `_currentOnCore_self` / `_ne`,
-- `_not_mem_self`, `_currentOnCore_ne_self`, `_replenishQueueOnCore`,
-- `_determineTargetCore`, `descheduleAtPlacement_{preserves_objects,
-- determineTargetCore,machine_eq,replenishQueueOnCore}`,
-- `descheduleAtPlacementCores_eq_toList` and the `placedCoreOf?` congruences)
-- moved with the definitions to `Scheduler/Operations/Selection.lean` — see the
-- §1 note above.  Nothing is renamed.

-- ============================================================================
-- WS-RR RR8.12: the home-core frame layer
-- ============================================================================
--
-- **Relocated to production at `v0.35.104`** from
-- `InformationFlow/NonInterferenceCrossCore.lean`, which is staged and imports
-- `Kernel.API`.  These eight facts are about **production** primitives -- the
-- object store, the IPC stores, the dual-queue removals -- and the question they
-- answer is *is this step a migration?*, which every production scheduler
-- footprint has to ask before it may name a core at the pre-state.  Living in a
-- staged module made that answer unreachable from the asker, which is this
-- project's own layering rule (`v0.35.59`: when a question has one owner and an
-- asker that cannot see it, the owner is in the wrong layer).  Measured before
-- moving: all eight had **zero** consumers outside that module, so the
-- relocation is a pure layering fix rather than a re-homing of live reasoning.
--
-- The general fact: a home core is `getTcb?` composed with `cpuAffinity`, so a
-- store preserves it whenever the store preserves that composite -- which every
-- IPC-pipeline store does, since none of them is a *migration*.

-- ============================================================================
-- §1a The home-core frame layer
-- ============================================================================
--
-- Every write set below names `determineTargetCore st _` at the **pre-state**,
-- but the wake it describes happens several object stores later. Pushing the
-- target back across those stores is the affinity-stability argument SM6.B makes
-- for one pipeline (`notificationSignalOnCore_remote_wake_preState`); the
-- cross-core IPC transitions need it for four more, so it is factored here into
-- a reusable layer rather than repeated.
--
-- The general fact: a home core is `getTcb?` composed with `cpuAffinity`, so a
-- store preserves it whenever the store preserves that composite — which every
-- IPC-pipeline store does, since none of them is a *migration*.

/-- SM8.B.2: storing a TCB that agrees with the current one on `cpuAffinity`
preserves **every** thread's home core. The generic form behind the
IPC-pipeline frames: an IPC store rewrites `ipcState`, `pendingMessage` or the
queue links, never the affinity, so it is never a migration. -/
theorem storeObject_tcb_determineTargetCore_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb newTcb : TCB) (x : SeLe4n.ThreadId)
    (hOld : st.getTcb? tid = some tcb)
    (hAff : newTcb.cpuAffinity = tcb.cpuAffinity)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject tid.toObjId (.tcb newTcb) st = .ok ((), st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  -- Stated over the typed accessor (AK7 cascade discipline): the raw store form
  -- is recovered inside the proof, so no caller has to name it.
  have hRaw := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hOld
  refine determineTargetCore_congr st st' x ?_
  by_cases hEq : x.toObjId = tid.toObjId
  · simp [SystemState.getTcb?, hEq, hRaw,
      storeObject_objects_eq st st' tid.toObjId (.tcb newTcb) hObjInv hStore, hAff]
  · simp only [SystemState.getTcb?,
      storeObject_objects_ne st st' tid.toObjId x.toObjId (.tcb newTcb) hEq hObjInv hStore]

/-- SM8.B.2: storing an **endpoint** over an object that is already an endpoint
preserves every thread's home core. Note there is no disjointness hypothesis
and none is needed: at a *different* id the TCB lookup is framed, and at the
*same* id the lookup fails both before and after (an endpoint is not a TCB), so
both sides read the unbound default. -/
theorem storeObject_endpoint_determineTargetCore_eq (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (ep ep' : Endpoint) (x : SeLe4n.ThreadId)
    (hPre : st.objects[endpointId]? = some (.endpoint ep))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  refine determineTargetCore_congr st st' x ?_
  by_cases hEq : x.toObjId = endpointId
  · simp only [SystemState.getTcb?, hEq, hPre,
      storeObject_objects_eq st st' endpointId (.endpoint ep') hObjInv hStore]
  · simp only [SystemState.getTcb?,
      storeObject_objects_ne st st' endpointId x.toObjId (.endpoint ep') hEq hObjInv hStore]

/-- SM8.B.2: storing a **SchedContext** preserves every thread's home core.

The `storeObject_endpoint_determineTargetCore_eq` argument verbatim, and for the
same reason it needs no disjointness hypothesis: at a different id the TCB
lookup is framed, and at the *same* id `getTcb?` fails both before and after
(`SystemState.getTcb?` matches only `some (.tcb _)`, and a SchedContext is not a
TCB), so both sides read the unbound default.

Added in PR #861 review round 14 for the SchedContext arms: the reroute through
`determineTargetCore` made them remote writers, and their write sets name the
home core at the *pre*-state while the transitions compute it after this
store. -/
theorem storeObject_schedContext_determineTargetCore_eq (st st' : SystemState)
    (scObjId : SeLe4n.ObjId) (sc sc' : SchedContext) (x : SeLe4n.ThreadId)
    (hPre : st.objects[scObjId]? = some (.schedContext sc))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject scObjId (.schedContext sc') st = .ok ((), st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  refine determineTargetCore_congr st st' x ?_
  by_cases hEq : x.toObjId = scObjId
  · simp only [SystemState.getTcb?, hEq, hPre,
      storeObject_objects_eq st st' scObjId (.schedContext sc') hObjInv hStore]
  · simp only [SystemState.getTcb?,
      storeObject_objects_ne st st' scObjId x.toObjId (.schedContext sc') hEq hObjInv hStore]

-- The raw-`objects.insert` frames these operations need already exist as SM5.I
-- atoms in `Scheduler/Operations/PerCoreTickCbsAffinity.lean`, imported above:
-- `determineTargetCore_insert_tcb` (a TCB insert with unchanged `cpuAffinity`) and
-- `getTcb?_insert_schedContext_eq` (a SchedContext insert leaves every TCB lookup
-- alone). They are used rather than re-proved here.

/-- SM8.B.2: the `_fromTcb` IPC store is not a migration either. -/
theorem storeTcbIpcStateAndMessage_fromTcb_determineTargetCore_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (x : SeLe4n.ThreadId)
    (hOld : st.getTcb? tid = some tcb)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage_fromTcb st tid tcb ipc msg = .ok st') :
    determineTargetCore st' x = determineTargetCore st x := by
  unfold storeTcbIpcStateAndMessage_fromTcb at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next st1 hStore =>
    simp only [Except.ok.injEq] at hStep
    subst hStep
    exact storeObject_tcb_determineTargetCore_eq st st1 tid tcb
      { tcb with ipcState := ipc, pendingMessage := msg } x hOld rfl hObjInv hStore

/-- SM8.B.2: a queue-link store is not a migration. -/
theorem storeTcbQueueLinks_determineTargetCore_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId) (x : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    determineTargetCore st' x = determineTargetCore st x := by
  unfold storeTcbQueueLinks at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next tcb hLk =>
    split at hStep
    · exact absurd hStep (by simp)
    · next st1 hStore =>
      simp only [Except.ok.injEq] at hStep
      subst hStep
      exact storeObject_tcb_determineTargetCore_eq st st1 tid tcb
        (tcbWithQueueLinks tcb prev pprev next) x
        ((SystemState.getTcb?_eq_some_iff st tid tcb).mpr
          (lookupTcb_some_objects st tid tcb hLk)) rfl hObjInv hStore

/-- SM8.B.2: `endpointQueueRemoveDual` is not a migration — the mid-queue splice
rewrites the endpoint, the removed thread's links and its neighbours', never an
affinity. Composed from the two directions of the transition's own TCB
transport: backward gives affinity agreement where the post-state has a TCB,
forward rules out a TCB appearing or vanishing. -/
theorem endpointQueueRemoveDual_determineTargetCore_eq (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid x : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  refine determineTargetCore_congr st st' x ?_
  cases hPost : st'.getTcb? x with
  | none =>
    cases hPre : st.getTcb? x with
    | none => simp
    | some tcb =>
      -- A TCB cannot vanish: the forward transport produces one at the same key.
      obtain ⟨tcb', hTcb'⟩ := endpointQueueRemoveDual_tcb_forward st st' endpointId
        isReceiveQ tid x.toObjId tcb hObjInv hStep
        ((SystemState.getTcb?_eq_some_iff st x tcb).mp hPre)
      rw [(SystemState.getTcb?_eq_some_iff st' x tcb').mpr hTcb'] at hPost
      exact absurd hPost (by simp)
  | some tcb' =>
    obtain ⟨tcb, hPreRaw, hAff⟩ := endpointQueueRemoveDual_tcb_cpuAffinity_backward st st'
      endpointId isReceiveQ tid x tcb' hObjInv hStep
      ((SystemState.getTcb?_eq_some_iff st' x tcb').mp hPost)
    rw [(SystemState.getTcb?_eq_some_iff st x tcb).mpr hPreRaw]
    simp [hAff]

/-- SM8.B.2: `storeTcbReceiveComplete` is not a migration — it rewrites the
receiver's `ipcState`, `pendingMessage` and reply stash, never its affinity. -/
theorem storeTcbReceiveComplete_determineTargetCore_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (msg : Option IpcMessage) (x : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    determineTargetCore st' x = determineTargetCore st x := by
  unfold storeTcbReceiveComplete at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_tcb_determineTargetCore_eq st pair.2 tid tcb
        { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none } x
        ((SystemState.getTcb?_eq_some_iff st tid tcb).mpr
          (lookupTcb_some_objects st tid tcb hTcb)) rfl hObjInv hStore

/-- SM8.B.2: `endpointQueuePopHead` is not a migration either — it rewrites the
endpoint's queue and two threads' link fields, and nothing's affinity. -/
theorem endpointQueuePopHead_determineTargetCore_eq (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (st st' : SystemState) (rTid : SeLe4n.ThreadId) (rTcb : TCB)
    (x : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  unfold endpointQueuePopHead SystemState.getObject? at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _
    | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []
        cases hLookup : lookupTcb st headTid with
        | none => simp
        | some headTcb =>
          simp only []
          -- PR #873 round 11: the send-queue message-presence guard --
          -- a head that fails it errors, so it is not this `.ok`.
          split
          · simp
          cases hStore : storeObject endpointId
              (.endpoint (if isReceiveQ
                then { ep with receiveQ := _ } else { ep with sendQ := _ })) st with
          | error e => simp
          | ok pair =>
            have hInv1 : pair.2.objects.invExt :=
              storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hT1 : determineTargetCore pair.2 x = determineTargetCore st x :=
              storeObject_endpoint_determineTargetCore_eq st pair.2 endpointId ep _ x hObj
                hObjInv (by rw [hStore])
            simp only []
            cases hNext : headTcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, hEq⟩; subst hEq
                rw [storeTcbQueueLinks_determineTargetCore_eq pair.2 st3 headTid none none none
                      x hInv1 hFinal, hT1]
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none
                    (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  have hInv2 : st2.objects.invExt :=
                    storeTcbQueueLinks_preserves_objects_invExt pair.2 st2 nextTid none
                      (some QueuePPrev.endpointHead) nextTcb.queueNext hInv1 hLink
                  have hT2 : determineTargetCore st2 x = determineTargetCore st x := by
                    rw [storeTcbQueueLinks_determineTargetCore_eq pair.2 st2 nextTid none
                          (some QueuePPrev.endpointHead) nextTcb.queueNext x hInv1 hLink, hT1]
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, hEq⟩; subst hEq
                    rw [storeTcbQueueLinks_determineTargetCore_eq st2 st3 headTid none none
                          none x hInv2 hFinal, hT2]

/-- **WS-RR RR8.12**: storing a **Reply** preserves every thread's home core.

The fourth member of the `storeObject_*_determineTargetCore_eq` family, and it
was missing: the three above cover a TCB, an endpoint and a SchedContext, and the
receive leg's `linkCallerReply` stores a Reply.  `CLAUDE.md`'s *keep the tables
symmetric* rule is what says to add it rather than to special-case the one caller
-- an asymmetric family is how a cell stays uncovered until someone needs it.

Needs no disjointness hypothesis, for the same reason its endpoint sibling does
not: at a different id the TCB lookup is framed, and at the *same* id `getTcb?`
fails before and after (it matches only `some (.tcb _)`, and a Reply is not a
TCB), so both sides read the unbound default. -/
theorem storeObject_reply_determineTargetCore_eq (st st' : SystemState)
    (replyObjId : SeLe4n.ObjId) (r r' : SeLe4n.Kernel.Reply) (x : SeLe4n.ThreadId)
    (hPre : st.objects[replyObjId]? = some (.reply r))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject replyObjId (.reply r') st = .ok ((), st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  refine determineTargetCore_congr st st' x ?_
  by_cases hEq : x.toObjId = replyObjId
  · simp only [SystemState.getTcb?, hEq, hPre,
      storeObject_objects_eq st st' replyObjId (.reply r') hObjInv hStore]
  · simp only [SystemState.getTcb?,
      storeObject_objects_ne st st' replyObjId x.toObjId (.reply r') hEq hObjInv hStore]

/-- **WS-RR RR8.12**: parking a thread on an endpoint queue is not a migration.

`endpointQueueEnqueue` writes the endpoint's own queue boundary and one or two
threads' link fields (`storeTcbQueueLinks`), and no path through it touches an
affinity -- so a receive that *blocks* leaves every home core where it was, which
is the arm a pre-state scheduler footprint names the executing core on.

The dual of `endpointQueuePopHead_determineTargetCore_eq` above: that one covers
the rendezvous arm, this one the block arm, and between them the receive leg's
two shapes are both framed. -/
theorem endpointQueueEnqueue_determineTargetCore_eq (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (x : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    determineTargetCore st' x = determineTargetCore st x := by
  unfold endpointQueueEnqueue SystemState.getObject? at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _
    | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hLk : lookupTcb st tid with
      | none => simp
      | some tcb =>
        simp only []
        split
        · simp
        · split
          · simp
          · cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
                simp only
                cases hStore : storeObject endpointId
                    (.endpoint (if isReceiveQ
                      then { ep with receiveQ := { head := some tid, tail := some tid } }
                      else { ep with sendQ := { head := some tid, tail := some tid } })) st with
                | error e => simp
                | ok pair =>
                  simp only
                  have hInv1 : pair.2.objects.invExt :=
                    storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  have hT1 : determineTargetCore pair.2 x = determineTargetCore st x :=
                    storeObject_endpoint_determineTargetCore_eq st pair.2 endpointId ep _ x hObj
                      hObjInv (by rw [hStore])
                  cases hLinks : storeTcbQueueLinks pair.2 tid none (some .endpointHead) none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq]
                    intro hEq; subst hEq
                    rw [storeTcbQueueLinks_determineTargetCore_eq pair.2 st3 tid none
                          (some .endpointHead) none x hInv1 hLinks, hT1]
            | some tailTid =>
                simp only
                cases hLkT : lookupTcb st tailTid with
                | none => simp
                | some tailTcb =>
                  simp only
                  cases hStore : storeObject endpointId
                      (.endpoint (if isReceiveQ
                        then { ep with receiveQ :=
                          { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head,
                            tail := some tid } }
                        else { ep with sendQ :=
                          { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head,
                            tail := some tid } })) st with
                  | error e => simp
                  | ok pair =>
                    simp only
                    have hInv1 : pair.2.objects.invExt :=
                      storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                    have hT1 : determineTargetCore pair.2 x = determineTargetCore st x :=
                      storeObject_endpoint_determineTargetCore_eq st pair.2 endpointId ep _ x hObj
                        hObjInv (by rw [hStore])
                    cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev
                        tailTcb.queuePPrev (some tid) with
                    | error e => simp
                    | ok st2 =>
                      simp only
                      have hInv2 : st2.objects.invExt :=
                        storeTcbQueueLinks_preserves_objects_invExt pair.2 st2 tailTid _ _ _
                          hInv1 hLink1
                      have hT2 : determineTargetCore st2 x = determineTargetCore st x := by
                        rw [storeTcbQueueLinks_determineTargetCore_eq pair.2 st2 tailTid
                          tailTcb.queuePrev tailTcb.queuePPrev (some tid) x hInv1 hLink1, hT1]
                      cases hLink2 : storeTcbQueueLinks st2 tid (some tailTid)
                          (some (.tcbNext tailTid)) none with
                      | error e => simp
                      | ok st3 =>
                        simp only [Except.ok.injEq]
                        intro hEq; subst hEq
                        rw [storeTcbQueueLinks_determineTargetCore_eq st2 st3 tid (some tailTid)
                          (some (.tcbNext tailTid)) none x hInv2 hLink2, hT2]

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

/-- **WS-RR RR8.12**: linking a dequeued caller to its reply object moves no
thread's home core.

The composite the receive leg's `Call` rendezvous runs, and the fifth member of
this family: `linkReply` stores a **Reply** (`storeObject_reply_…` above) and the
second step stores the caller's TCB with only `replyObject` set, so `cpuAffinity`
is `rfl` on both writes.  Nothing here consults an affinity, which is the whole
content -- and what lets a *pre-state* scheduler footprint name the home cores a
later step resolves, rather than assuming the two coincide. -/
theorem linkCallerReply_determineTargetCore_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (x : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  unfold SystemState.linkCallerReply at hStep
  cases hLink : SystemState.linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hFrame1 : determineTargetCore st1 x = determineTargetCore st x := by
      unfold SystemState.linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => rw [hGetR] at hLink; simp at hLink
      | some r =>
        simp only [hGetR] at hLink
        split at hLink
        · exact storeObject_reply_determineTargetCore_eq st st1 rid.toObjId r
            { r with caller := some caller } x
            ((SystemState.getReply?_eq_some_iff st rid r).mp hGetR) hObjInv hLink
        · simp at hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · have hInv1 :=
          SystemState.linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
        rw [storeObject_tcb_determineTargetCore_eq st1 st' caller tcb
          { tcb with replyObject := some rid } x hT rfl hInv1 hStep, hFrame1]
      · simp at hStep

/-- **WS-RR RR8.12**: and installing the capabilities a parked send was carrying
moves no thread's home core either.

The last step of the live `.receive` arm's receive leg.  `ipcUnwrapCaps` writes
CNodes and the CDT, and its own TCB frame holds at *every* key in both directions
(`ipcUnwrapCaps_preserves_tcb_objects` / `_tcb_backward`), so the whole
`getTcb?` projection is fixed -- a strictly stronger fact than the affinity this
needs, which is why no per-field argument appears here. -/
theorem ipcUnwrapCaps_determineTargetCore_eq (msg : IpcMessage)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary) (x : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg receiverRoot slotBase grantRight st = .ok (summary, st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  have hEq : st'.getTcb? x = st.getTcb? x := by
    cases hT' : st'.getTcb? x with
    | none =>
        cases hT : st.getTcb? x with
        | none => rfl
        | some tcb =>
            have hFwd := ipcUnwrapCaps_preserves_tcb_objects msg receiverRoot slotBase
              grantRight st st' summary x.toObjId tcb
              ((SystemState.getTcb?_eq_some_iff st x tcb).mp hT) hObjInv hStep
            simp [(SystemState.getTcb?_eq_some_iff st' x tcb).mpr hFwd] at hT'
    | some tcb' =>
        have hBwd := ipcUnwrapCaps_tcb_backward msg receiverRoot slotBase grantRight
          st st' summary x.toObjId tcb' hObjInv hStep
          ((SystemState.getTcb?_eq_some_iff st' x tcb').mp hT')
        rw [(SystemState.getTcb?_eq_some_iff st x tcb').mpr hBwd]
  exact determineTargetCore_congr st st' x (by rw [hEq])

-- ============================================================================
-- §11b  `v0.35.161` (register row 57) — the SchedContext-resolution frames of
--       the receive leg's steps
-- ============================================================================
--
-- The `_determineTargetCore_eq` family above says the receive leg moves no
-- thread's home core.  `replenishQueueAffinityConsistentOnCore` reads one more
-- thing — `getSchedContext?`, the object a replenish entry is about — and the
-- leg framed it nowhere, which is why no theorem could say the leg preserves the
-- SM5.H affinity invariant at all (register row 57: the surface was silent, not
-- wrong).  These are the siblings, one per step, each an instance of one
-- store-level fact: every store the leg performs is at a key its own lookup
-- showed to hold a TCB, an endpoint or a Reply, and writes the same kind back,
-- so at that key both sides resolve no SchedContext and at every other key the
-- store is invisible.  *Keep the tables symmetric*: a family with a
-- `_determineTargetCore_eq` row and no `_getSchedContext?_eq` row is how a cell
-- stays uncovered until someone needs it.

/-- `v0.35.161`: a `storeObject` at a key holding no SchedContext, of a value that is
no SchedContext, frames every SchedContext resolution — the one store-level fact
behind the rows below. -/
theorem storeObject_getSchedContext?_eq_of_nonSchedContext
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hOld : ∀ sc, st.objects[id]? ≠ some (.schedContext sc))
    (hNew : ∀ sc, obj ≠ .schedContext sc)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st'))
    (scId : SeLe4n.SchedContextId) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?
  by_cases hEq : scId.toObjId = id
  · rw [hEq, storeObject_objects_eq st st' id obj hObjInv hStore]
    cases hPre : st.objects[id]? with
    | none => cases obj <;> first | rfl | exact absurd rfl (hNew _)
    | some o =>
      cases o <;> cases obj <;>
        first | rfl | exact absurd rfl (hNew _) | exact absurd hPre (hOld _)
  · rw [storeObject_objects_ne st st' id scId.toObjId obj hEq hObjInv hStore]

/-- `v0.35.161`: storing a TCB over a TCB frames every SchedContext resolution. -/
theorem storeObject_tcb_getSchedContext?_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb newTcb : TCB) (scId : SeLe4n.SchedContextId)
    (hPre : st.getTcb? tid = some tcb)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject tid.toObjId (.tcb newTcb) st = .ok ((), st')) :
    st'.getSchedContext? scId = st.getSchedContext? scId :=
  storeObject_getSchedContext?_eq_of_nonSchedContext st st' tid.toObjId (.tcb newTcb)
    (fun _ h => by
      rw [(SystemState.getTcb?_eq_some_iff st tid tcb).mp hPre] at h
      exact KernelObject.noConfusion (Option.some.inj h))
    (fun _ h => KernelObject.noConfusion h) hObjInv hStore scId

/-- `v0.35.161`: storing an endpoint over an endpoint frames every SchedContext
resolution. -/
theorem storeObject_endpoint_getSchedContext?_eq (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (ep ep' : Endpoint) (scId : SeLe4n.SchedContextId)
    (hPre : st.objects[endpointId]? = some (.endpoint ep))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st')) :
    st'.getSchedContext? scId = st.getSchedContext? scId :=
  storeObject_getSchedContext?_eq_of_nonSchedContext st st' endpointId (.endpoint ep')
    (fun _ h => by rw [hPre] at h; exact KernelObject.noConfusion (Option.some.inj h))
    (fun _ h => KernelObject.noConfusion h) hObjInv hStore scId

/-- `v0.35.161`: storing a Reply over a Reply frames every SchedContext resolution. -/
theorem storeObject_reply_getSchedContext?_eq (st st' : SystemState)
    (replyObjId : SeLe4n.ObjId) (r r' : SeLe4n.Kernel.Reply) (scId : SeLe4n.SchedContextId)
    (hPre : st.objects[replyObjId]? = some (.reply r))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject replyObjId (.reply r') st = .ok ((), st')) :
    st'.getSchedContext? scId = st.getSchedContext? scId :=
  storeObject_getSchedContext?_eq_of_nonSchedContext st st' replyObjId (.reply r')
    (fun _ h => by rw [hPre] at h; exact KernelObject.noConfusion (Option.some.inj h))
    (fun _ h => KernelObject.noConfusion h) hObjInv hStore scId

/-- `v0.35.161`: `storeTcbQueueLinks` rewrites one TCB's three link fields; the slot
is a TCB before and after. -/
theorem storeTcbQueueLinks_getSchedContext?_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  unfold storeTcbQueueLinks at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next tcb hLk =>
    split at hStep
    · exact absurd hStep (by simp)
    · next st1 hStore =>
      simp only [Except.ok.injEq] at hStep
      subst hStep
      exact storeObject_tcb_getSchedContext?_eq st st1 tid tcb
        (tcbWithQueueLinks tcb prev pprev next) scId
        ((SystemState.getTcb?_eq_some_iff st tid tcb).mpr
          (lookupTcb_some_objects st tid tcb hLk)) hObjInv hStore

/-- `v0.35.161`: `endpointQueuePopHead` rewrites the endpoint's queue and two threads'
link fields, and no SchedContext — the sibling of
`endpointQueuePopHead_determineTargetCore_eq`, walked the same way. -/
theorem endpointQueuePopHead_getSchedContext?_eq (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (st st' : SystemState) (rTid : SeLe4n.ThreadId) (rTcb : TCB)
    (scId : SeLe4n.SchedContextId) (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  unfold endpointQueuePopHead SystemState.getObject? at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _
    | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []
        cases hLookup : lookupTcb st headTid with
        | none => simp
        | some headTcb =>
          simp only []
          split
          · simp
          cases hStore : storeObject endpointId
              (.endpoint (if isReceiveQ
                then { ep with receiveQ := _ } else { ep with sendQ := _ })) st with
          | error e => simp
          | ok pair =>
            have hInv1 : pair.2.objects.invExt :=
              storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hT1 : pair.2.getSchedContext? scId = st.getSchedContext? scId :=
              storeObject_endpoint_getSchedContext?_eq st pair.2 endpointId ep _ scId hObj
                hObjInv (by rw [hStore])
            simp only []
            cases hNext : headTcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, hEq⟩; subst hEq
                rw [storeTcbQueueLinks_getSchedContext?_eq pair.2 st3 headTid none none none
                      scId hInv1 hFinal, hT1]
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none
                    (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  have hInv2 : st2.objects.invExt :=
                    storeTcbQueueLinks_preserves_objects_invExt pair.2 st2 nextTid none
                      (some QueuePPrev.endpointHead) nextTcb.queueNext hInv1 hLink
                  have hT2 : st2.getSchedContext? scId = st.getSchedContext? scId := by
                    rw [storeTcbQueueLinks_getSchedContext?_eq pair.2 st2 nextTid none
                          (some QueuePPrev.endpointHead) nextTcb.queueNext scId hInv1 hLink,
                      hT1]
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, hEq⟩; subst hEq
                    rw [storeTcbQueueLinks_getSchedContext?_eq st2 st3 headTid none none
                          none scId hInv2 hFinal, hT2]

/-- `v0.35.161`: `endpointQueueEnqueue` rewrites the endpoint's queue boundary and one
or two threads' link fields, and no SchedContext — the sibling of
`endpointQueueEnqueue_determineTargetCore_eq`, for the receive leg's block path. -/
theorem endpointQueueEnqueue_getSchedContext?_eq (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (scId : SeLe4n.SchedContextId) (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  unfold endpointQueueEnqueue SystemState.getObject? at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _
    | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hLk : lookupTcb st tid with
      | none => simp
      | some tcb =>
        simp only []
        split
        · simp
        · split
          · simp
          · cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
                simp only
                cases hStore : storeObject endpointId
                    (.endpoint (if isReceiveQ
                      then { ep with receiveQ := { head := some tid, tail := some tid } }
                      else { ep with sendQ := { head := some tid, tail := some tid } })) st with
                | error e => simp
                | ok pair =>
                  simp only
                  have hInv1 : pair.2.objects.invExt :=
                    storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  have hT1 : pair.2.getSchedContext? scId = st.getSchedContext? scId :=
                    storeObject_endpoint_getSchedContext?_eq st pair.2 endpointId ep _ scId hObj
                      hObjInv (by rw [hStore])
                  cases hLinks : storeTcbQueueLinks pair.2 tid none (some .endpointHead) none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq]
                    intro hEq; subst hEq
                    rw [storeTcbQueueLinks_getSchedContext?_eq pair.2 st3 tid none
                          (some .endpointHead) none scId hInv1 hLinks, hT1]
            | some tailTid =>
                simp only
                cases hLkT : lookupTcb st tailTid with
                | none => simp
                | some tailTcb =>
                  simp only
                  cases hStore : storeObject endpointId
                      (.endpoint (if isReceiveQ
                        then { ep with receiveQ :=
                          { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head,
                            tail := some tid } }
                        else { ep with sendQ :=
                          { head := (if isReceiveQ then ep.receiveQ else ep.sendQ).head,
                            tail := some tid } })) st with
                  | error e => simp
                  | ok pair =>
                    simp only
                    have hInv1 : pair.2.objects.invExt :=
                      storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                    have hT1 : pair.2.getSchedContext? scId = st.getSchedContext? scId :=
                      storeObject_endpoint_getSchedContext?_eq st pair.2 endpointId ep _ scId
                        hObj hObjInv (by rw [hStore])
                    cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev
                        tailTcb.queuePPrev (some tid) with
                    | error e => simp
                    | ok st2 =>
                      simp only
                      have hInv2 : st2.objects.invExt :=
                        storeTcbQueueLinks_preserves_objects_invExt pair.2 st2 tailTid _ _ _
                          hInv1 hLink1
                      have hT2 : st2.getSchedContext? scId = st.getSchedContext? scId := by
                        rw [storeTcbQueueLinks_getSchedContext?_eq pair.2 st2 tailTid
                          tailTcb.queuePrev tailTcb.queuePPrev (some tid) scId hInv1 hLink1, hT1]
                      cases hLink2 : storeTcbQueueLinks st2 tid (some tailTid)
                          (some (.tcbNext tailTid)) none with
                      | error e => simp
                      | ok st3 =>
                        simp only [Except.ok.injEq]
                        intro hEq; subst hEq
                        rw [storeTcbQueueLinks_getSchedContext?_eq st2 st3 tid (some tailTid)
                          (some (.tcbNext tailTid)) none scId hInv2 hLink2, hT2]

/-- `v0.35.161`: `storeTcbIpcStateAndMessage` writes one TCB's `ipcState` and
`pendingMessage`, and no SchedContext. -/
theorem storeTcbIpcStateAndMessage_getSchedContext?_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (msg : Option IpcMessage) (scId : SeLe4n.SchedContextId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLk : lookupTcb st tid with
  | none => simp [hLk] at hStep
  | some tcb =>
    simp only [hLk] at hStep
    cases hSO : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hSO] at hStep
    | ok pair =>
      simp only [hSO] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_tcb_getSchedContext?_eq st pair.2 tid tcb
        { tcb with ipcState := ipc, pendingMessage := msg } scId
        ((SystemState.getTcb?_eq_some_iff st tid tcb).mpr
          (lookupTcb_some_objects st tid tcb hLk)) hObjInv (by rw [hSO])

/-- `v0.35.161`: linking a dequeued caller to its reply object stores a Reply and a
TCB, and no SchedContext — the sibling of `linkCallerReply_determineTargetCore_eq`. -/
theorem linkCallerReply_getSchedContext?_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId)
    (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.linkCallerReply at hStep
  cases hLink : SystemState.linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hFrame1 : st1.getSchedContext? scId = st.getSchedContext? scId := by
      unfold SystemState.linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => rw [hGetR] at hLink; simp at hLink
      | some r =>
        simp only [hGetR] at hLink
        split at hLink
        · exact storeObject_reply_getSchedContext?_eq st st1 rid.toObjId r
            { r with caller := some caller } scId
            ((SystemState.getReply?_eq_some_iff st rid r).mp hGetR) hObjInv hLink
        · simp at hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · have hInv1 :=
          SystemState.linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
        rw [storeObject_tcb_getSchedContext?_eq st1 st' caller tcb
          { tcb with replyObject := some rid } scId hT hInv1 hStep, hFrame1]
      · simp at hStep

/-- `v0.35.161`: installing the capabilities a parked send was carrying writes CNodes
and the CDT, and no SchedContext.  At the receiver's root a SchedContext already there
is carried forward (`ipcUnwrapCaps_preserves_schedContext_objects`) and anything else
either survives or becomes a CNode (`ipcUnwrapCaps_objects_at_root_orig_or_cnode`);
every other key is untouched. -/
theorem ipcUnwrapCaps_getSchedContext?_eq (msg : IpcMessage)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary) (scId : SeLe4n.SchedContextId)
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg receiverRoot slotBase grantRight st = .ok (summary, st')) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?
  by_cases hRoot : scId.toObjId = receiverRoot
  · cases hPre : st.objects[scId.toObjId]? with
    | some obj =>
      cases obj with
      | schedContext sc =>
        rw [ipcUnwrapCaps_preserves_schedContext_objects msg receiverRoot slotBase grantRight
          st st' summary scId.toObjId sc hPre hObjInv hStep]
      | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | reply _ | endpoint _ =>
        rw [hRoot] at hPre ⊢
        rcases ipcUnwrapCaps_objects_at_root_orig_or_cnode msg receiverRoot slotBase grantRight
          st st' summary hObjInv hStep with hOrig | ⟨cn', hCn⟩
        · rw [hOrig, hPre]
        · rw [hCn]
    | none =>
      rw [hRoot] at hPre ⊢
      rcases ipcUnwrapCaps_objects_at_root_orig_or_cnode msg receiverRoot slotBase grantRight
        st st' summary hObjInv hStep with hOrig | ⟨cn', hCn⟩
      · rw [hOrig, hPre]
      · rw [hCn]
  · rw [ipcUnwrapCaps_preserves_objects_ne msg receiverRoot slotBase grantRight st st' summary
      scId.toObjId hRoot hObjInv hStep]

/-- `v0.35.161`: waking an already-`.ready` thread is object-invisible, so it frames
every SchedContext resolution — the shape the receive leg's plain-`Send` wake has,
the sender having just been stored `.ready`. -/
theorem wakeThread_getSchedContext?_eq_of_ready (st : SystemState)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hInv : st.objects.invExt) :
    (wakeThread st tid ec).1.getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?
  rw [wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hInv]

-- ============================================================================
-- §12 SM6.A.4 — Per-core caller blocking (plan §3.2 steps 5–6)
-- ============================================================================

/-- WS-SM SM6.A.4 (`endpointCall_perCore_blocking`): on a rendezvous call, the
caller is **blocked on its own core** — removed from `executingCore`'s run
queue and cleared from `executingCore`'s current slot. The receiver wake
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
-- §13 SM6.A.6 — Reply-state allocation under the caller-TCB write lock
-- ============================================================================

/-- A `storeTcbIpcStateAndMessage` that succeeds resolves the target TCB and
sets its `ipcState` to the stored value. (`invExt`-dependent: RobinHood table
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

/-- WS-SM SM6.A.1: the cross-core endpoint call preserves object-store
integrity (`invExt`).  On every control path the post-state's object store is
either `st`'s (an error / no-op leaf) or the result of the
pop / store / wake / store / deschedule chain, each step of which preserves
`invExt`.  Unconditional: an error leaf returns the pre-state unchanged. -/
theorem endpointCallOnCore_preserves_objects_invExt
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    (endpointCallOnCore endpointId caller msg executingCore st).1.objects.invExt := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hObjInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hObjInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hObjInv
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hObjInv
      | ok st' =>
        simp only
        have h1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hObjInv
        | ok st'' =>
          simp only
          have h2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st' st'' caller _ _ h1 hMsg
          show (removeRunnableOnCore st'' caller executingCore).objects.invExt
          rw [removeRunnableOnCore_preserves_objects]; exact h2
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hObjInv
      | ok pair =>
        simp only
        have h1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hObjInv
        | ok st2 =>
          simp only
          have h2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ h1 hMsg
          have hW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore h2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hObjInv
          | ok st4 =>
            simp only
            have h4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hW hCS
            -- WS-SM SM6.D (#7.3b fold): thread the server-first reply link
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact hObjInv
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have h5 := linkServerStashedReply_preserves_objects_invExt st4 st5 caller pair.1 h4 hLink
              show (removeRunnableOnCore st5 caller executingCore).objects.invExt
              rw [removeRunnableOnCore_preserves_objects]; exact h5

open SeLe4n.Model.SystemState in
/-- D6 (per-core): a `wakeThread` of a `.ready` thread preserves every TCB's binding (its state
effect is `enqueueRunnableOnCore` — a scheduler-only step that leaves the object store
pointwise-unchanged for a `.ready` target). -/
theorem wakeThread_sameSchedContextBindings_of_ready
    (st : SystemState) (wtid : SeLe4n.ThreadId) (ec : CoreId) (wtcb : TCB)
    (hWGet : st.getTcb? wtid = some wtcb) (hWReady : wtcb.ipcState = .ready)
    (hObjInv : st.objects.invExt) :
    sameSchedContextBindings st (wakeThread st wtid ec).1 := by
  intro y tcY hY
  rw [wakeThread_objects_getElem_eq_of_ready st wtid ec wtcb hWGet hWReady hObjInv y.toObjId] at hY
  exact ⟨tcY, hY, rfl⟩

/-! **WS-RR RR8.16 (`v0.35.189`)**: the D6 binding frame below was relocated here
from the staged `EndpointCallInvariant.lean` rather than re-proved.  It is what
makes the arm's donation member *pre-state computable*:
`applyCallDonationOnCore` runs at the post-leg state and branches on
`callDonationSchedContext?` there, while `lockSet_endpointCallOnCore` must resolve
before the transition runs, and a binding frame is what makes those one answer
(`endpointCallDonatedSc?_some_of_post`). -/

open SeLe4n.Model.SystemState in
/-- D6 (per-core): `endpointCallOnCore` preserves every TCB's `schedContextBinding` (the cross-core
mirror of `endpointCall_sameSchedContextBindings`; `wakeThread`/`removeRunnableOnCore` are
scheduler-only, the store/link ops never write a binding). -/
theorem endpointCallOnCore_sameSchedContextBindings
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    sameSchedContextBindings st (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact sameSchedContextBindings.refl st
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact sameSchedContextBindings.refl st
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact sameSchedContextBindings.refl st
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact sameSchedContextBindings.refl st
      | ok st' =>
        simp only
        have hS1 := endpointQueueEnqueue_sameSchedContextBindings endpointId false caller st st' hObjInv hEnq
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact sameSchedContextBindings.refl st
        | ok st'' =>
          simp only
          have hS2 := hS1.trans (storeTcbIpcStateAndMessage_sameSchedContextBindings st' st'' caller (.blockedOnCall endpointId) (some msg) hObj1 hMsg)
          show sameSchedContextBindings st (removeRunnableOnCore st'' caller executingCore)
          exact hS2.trans (sameSchedContextBindings.of_objects_eq (removeRunnableOnCore_preserves_objects st'' caller executingCore))
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact sameSchedContextBindings.refl st
      | ok pair =>
        simp only
        have hS1 := endpointQueuePopHead_sameSchedContextBindings endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact sameSchedContextBindings.refl st
        | ok st2 =>
          simp only
          have hS2 := hS1.trans (storeTcbIpcStateAndMessage_sameSchedContextBindings pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg)
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hS3 := hS2.trans (wakeThread_sameSchedContextBindings_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObj2)
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact sameSchedContextBindings.refl st
          | ok st4 =>
            simp only
            have hS4 := hS3.trans (storeTcbIpcStateAndMessage_sameSchedContextBindings (wakeThread st2 pair.1 executingCore).1 st4 caller (.blockedOnReply endpointId (some pair.1)) none hObjW hCS)
            have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hObjW hCS
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact sameSchedContextBindings.refl st
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have hS5 := hS4.trans (linkServerStashedReply_sameSchedContextBindings st4 st5 caller pair.1 hObjInv4 hLink)
              show sameSchedContextBindings st (removeRunnableOnCore st5 caller executingCore)
              exact hS5.trans (sameSchedContextBindings.of_objects_eq (removeRunnableOnCore_preserves_objects st5 caller executingCore))

/-- Finding F-1: a `storeTcbReceiveComplete` that succeeds resolves the target TCB
and sets its `ipcState` to `.ready`. Mirror of
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
gate of `endpointReply`). This write lands on the caller's TCB, which
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
-- §14 SM6.A.6 — the caller-TCB write lock IS in the footprint (membership)
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
declared member of the `endpointCall` lock-set footprint. Together with
`endpointCallOnCore_reply_linkage_under_lockSet` this makes "reply-state
allocation under lock-set" concrete: the specific lock covering the write is in
the held footprint.

**WS-RR RR7.11**: the `hRecvNe` hypothesis is gone. It said a present receiver
is a thread distinct from the caller — true (you do not `Call` yourself) but
irrelevant to the conclusion, because a coinciding key merges under
`AccessMode.lub` and `.write` is that lattice's top, so the member survives
either way. A hypothesis that the conclusion does not need is one every caller
has to discharge for nothing, and it made this statement look narrower than the
fact it records. The general form is
`lockSet_endpointCall_caller_tcb_write_mem_unconditional`, stated over the
capability-transfer arguments too; this is that theorem at the arguments SM6.A
cites it with. -/
theorem lockSet_endpointCall_caller_tcb_write_mem
    (caller : SeLe4n.ThreadId) (cnRoot endpointId : SeLe4n.ObjId)
    (receiver? : Option SeLe4n.ThreadId) (donatedSc? : Option SeLe4n.SchedContextId) :
    (tcbLock caller, AccessMode.write)
      ∈ (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?).pairs :=
  lockSet_endpointCall_caller_tcb_write_mem_unconditional caller cnRoot endpointId
    receiver? donatedSc? none none none none

-- ============================================================================
-- §9 WS-RR RR2.4 — the scheduler-domain footprint of the cross-core `.call`
-- ============================================================================
--
-- `lockSet_endpointCall` is a `LockSet` over the SM0.I **object** domain
-- (`LockId` = kind × ObjId). The RR2.2 replenishment migration writes two
-- **per-core replenish-queue** slots, which are not object locks at all — they
-- live in the `SchedLockId` domain, whose whole reason for existing (SM5.A.2)
-- is that a per-core scheduler slot has no `ObjId` to key a `LockId` on. So
-- "extend the call's footprint with `migrateSchedContextReplenishmentLockSet`"
-- is a statement in the cross-domain `SchedLockId` order, exactly as SM6.E's
-- `cancelDonatedDonationOnCoreSchedLockSet` is for the `.tcbSuspend` arm that
-- runs the same migration. Both footprints below are `SchedLockId` lists in
-- plan §4.4 ascending order (`object < runQueue < replenishQueue`), each
-- same-kind segment `CoreId`-ascending, so the list *is* the SM3.D acquisition
-- sequence.

/-- WS-RR RR2.4: the scheduler-domain footprint of the cross-core `.call`
**donation** (`applyCallDonationOnCore`) — the object-store table write lock
plus the replenish-queue write locks of **both** migration endpoints (the
donor's home core, purged, and the donee's home core, receiving), emitted in
`CoreId`-ascending order. On a shared home core the two endpoints coincide, the
migration is a definitional no-op, and the footprint collapses to the single
slot.

Structurally identical to `cancelDonatedDonationOnCoreSchedLockSet`, and for the
same reason: it is the same primitive, moving the same SchedContext's
replenishments between the same two kinds of core.

**WS-RR RR8.12**: spelled through `schedFootprintOfCores`, which is the shared
answer to "what is a scheduler-domain footprint over these core sets" — an
empty run set here, because a donation moves replenishments and touches no run
queue.  Its `_pairwise_le` and `_write_only` come with it. -/
def applyCallDonationOnCoreSchedLockSet (donorHome doneeHome : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores [] [donorHome, doneeHome]

/-- RR2.4: every lock in the donation footprint is acquired in **write** mode
(the rebinding writes the object store; the migration writes both queues). -/
theorem applyCallDonationOnCoreSchedLockSet_write_only (donorHome doneeHome : CoreId) :
    ∀ p ∈ applyCallDonationOnCoreSchedLockSet donorHome doneeHome,
      p.2 = Concurrency.AccessMode.write :=
  schedFootprintOfCores_write_only _ _

/-- RR2.4: the donor's home-core replenish-queue write lock is in the footprint
(the migration's source / purge slot). -/
theorem applyCallDonationOnCoreSchedLockSet_contains_donorHome_write
    (donorHome doneeHome : CoreId) :
    (SchedLockId.replenishQueue ⟨donorHome⟩, Concurrency.AccessMode.write)
      ∈ applyCallDonationOnCoreSchedLockSet donorHome doneeHome :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ donorHome).mpr (by simp)

/-- RR2.4: the donee's home-core replenish-queue write lock is in the footprint
(the migration's destination). -/
theorem applyCallDonationOnCoreSchedLockSet_contains_doneeHome_write
    (donorHome doneeHome : CoreId) :
    (SchedLockId.replenishQueue ⟨doneeHome⟩, Concurrency.AccessMode.write)
      ∈ applyCallDonationOnCoreSchedLockSet donorHome doneeHome :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ doneeHome).mpr (by simp)

/-- **RR2.4's coverage obligation**: the footprint covers
`migrateSchedContextReplenishmentLockSet` member for member. This is the
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
    ((applyCallDonationOnCoreSchedLockSet donorHome doneeHome).map (·.1)).Pairwise (· ≤ ·) :=
  schedFootprintOfCores_pairwise_le _ _

/-- RR2.4: the donation footprint is within the SM3.D `maxLockSetSize`
cap — three locks at most (object store plus at most two replenish queues).

**WS-RR RR7.11**: stated against the constant, not the numeral. -/
theorem applyCallDonationOnCoreSchedLockSet_size_le_maxLockSetSize
    (donorHome doneeHome : CoreId) :
    (applyCallDonationOnCoreSchedLockSet donorHome doneeHome).length
      ≤ Concurrency.maxLockSetSize := by
  have hSeg := schedFootprintOfCores_length_le (runCores := ([] : List CoreId))
    (replenishCores := [donorHome, doneeHome])
  have hN : Concurrency.numCores = 4 := rfl
  have hM : Concurrency.maxLockSetSize = 24 := rfl
  unfold applyCallDonationOnCoreSchedLockSet
  omega

/-- WS-RR RR2.4: the scheduler-domain footprint of the **whole** cross-core
`.call` dispatch — the union of what its three scheduling effects write:

* the object-store table lock (the rendezvous' TCB / endpoint / CSpace writes
  and the donation's rebinding);
* the **run-queue** write locks of the executing core (the block path's
  `removeRunnableOnCore` deschedule of the caller) and of the receiver's home
  core (the rendezvous' `wakeThread` enqueue) — one entry when they coincide;
* the **replenish-queue** write locks of the two donation endpoints (RR2.2).

**Dynamic chain extension (declared, not static).** The dispatch also runs
`propagatePipChainCrossCore`, which re-buckets each blocking-chain member's run
queue on *that member's* home core. The chain is state-discovered, so no static
footprint can enumerate those cores — the SM3.C.11 obligation
(`pipChainStart_tcbSuspend`, `LockSetTransitions.lean`) covers this walk too:
per chain step the walker acquires the member's TCB write lock *and* its
home-core run-queue write lock. SM6.E's suspend footprint carries the identical
caveat for the identical walk. -/
def endpointCallCrossCoreDispatchSchedLockSet
    (executingCore receiverHome donorHome doneeHome : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores [executingCore, receiverHome] [donorHome, doneeHome]

/-- RR2.4: the dispatch footprint's keys form a `SchedLockId`-ascending
acquisition sequence — the full three-domain ladder `object < runQueue <
replenishQueue`, each same-kind segment `CoreId`-ascending. -/
theorem endpointCallCrossCoreDispatchSchedLockSet_pairwise_le
    (executingCore receiverHome donorHome doneeHome : CoreId) :
    ((endpointCallCrossCoreDispatchSchedLockSet executingCore receiverHome donorHome
      doneeHome).map (·.1)).Pairwise (· ≤ ·) :=
  schedFootprintOfCores_pairwise_le _ _

/-- RR2.4: the dispatch footprint is write-only. -/
theorem endpointCallCrossCoreDispatchSchedLockSet_write_only
    (executingCore receiverHome donorHome doneeHome : CoreId) :
    ∀ p ∈ endpointCallCrossCoreDispatchSchedLockSet executingCore receiverHome donorHome doneeHome,
      p.2 = Concurrency.AccessMode.write :=
  schedFootprintOfCores_write_only _ _

/-- **RR2.4 (dispatch-level coverage)**: the whole-dispatch footprint covers the
donation footprint member for member, hence — by
`applyCallDonationOnCoreSchedLockSet_covers_migration` — the migration's two
replenish-queue write locks. A `withLockSet` bracket over the dispatch
footprint therefore holds every lock the RR2.2 migration writes under, which is
what keeps the SM3 serializability argument valid across the new write. -/
theorem endpointCallCrossCoreDispatchSchedLockSet_covers_donation
    (executingCore receiverHome donorHome doneeHome : CoreId) :
    ∀ p ∈ applyCallDonationOnCoreSchedLockSet donorHome doneeHome,
      p ∈ endpointCallCrossCoreDispatchSchedLockSet executingCore receiverHome donorHome doneeHome :=
  schedFootprintOfCores_subset (fun _ h => absurd h (by simp)) (fun _ h => h)

end SeLe4n.Kernel
