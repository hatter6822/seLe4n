-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.C: PRODUCTION (LANDED).  `endpointReplyOnCore` enters the production
-- import closure when the live `.reply` / `.replyRecv` dispatch
-- (`API.dispatchWithCap{,Checked}`) routes through the cross-core reply
-- (`endpointReplyCrossCoreDispatch`, which builds on this transition).  See
-- docs/planning/SMP_CROSS_CORE_IPC_PLAN.md §3.1, §5 (SM6.C).

import SeLe4n.Kernel.IPC.CrossCore.EndpointCall

/-!
# WS-SM SM6.C — Reply path across cores

This module is the SM6.C deliverable of the WS-SM Phase 6 cross-core IPC
workstream (plan `docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.1, §5).  It lifts
the single-core reply syscalls to *cross-core* transitions under the SM3.B
per-object lock-set discipline:

* **`endpointReplyOnCore`** — the cross-core generalisation of `endpointReply`.
  The reply unblocks the *original caller* (the `blockedOnReply` thread recorded
  as `target`).  That caller's wake is routed through the SM5.C cross-core
  `wakeThread … executingCore`, so a caller bound to a *remote* core is enqueued
  on that core and a `.reschedule` SGI is surfaced for the runtime to fire (plan
  SM6.C.2 `endpointReply_remote_wake`).  The replier (server) does **not** block,
  so no per-core deschedule occurs in this transition (the donation-return
  deschedule of a passive server is the dispatch wrapper's concern — §10).
* **`endpointReceiveDualOnCore`** — the cross-core generalisation of
  `endpointReceiveDual` (the receive leg of `replyRecv`): on the no-sender block
  path the receiver is descheduled on *its own* core via `removeRunnableOnCore`;
  on a `blockedOnSend` rendezvous the woken sender is routed to *its* home core
  via `wakeThread` (surfacing the optional SGI).  A `blockedOnCall` sender
  becomes `blockedOnReply` (not woken), exactly as single-core.
* **`endpointReplyRecvOnCore`** — the cross-core generalisation of
  `endpointReplyRecv`: the reply leg (`endpointReplyOnCore`) then the receive leg
  (`endpointReceiveDualOnCore`), surfacing the union of both legs' cross-core
  SGIs.

The single-core forms (in `IPC.DualQueue.Transport`) remain the canonical
bootCore semantics; these cross-core transitions substitute only the scheduler
placement of the woken caller / blocked receiver / woken sender, exactly as
SM6.A's `endpointCallOnCore` and SM6.B's `notificationSignalOnCore` do.  The
lock-set footprints `lockSet_endpointReply` / `lockSet_replyRecv` (SM3.B.3) are
unchanged; this module proves the SM6.C theorems the runtime `withLockSet`
bracket consumes.

> **Model note.**  This kernel now has a first-class `Reply` *object*
> (`KernelObject.reply`, addressed by `ReplyId`) carrying the caller back-link in
> `reply.caller`.  The `.reply` lock-kind is a **live level-6 per-object lock**:
> `LockId.lookup` resolves `(reply.lock, .reply r)` via `getReply?` and `lockHeld`
> reads `Reply.lock` (`LockIdProjection.lookup_reply`, `LockSetHeld`).  SM6.C.6
> ("reply object lifecycle") is the lifecycle of `reply.caller` — set on the
> receive path (`linkCallerReply`) and consumed `:= none` on reply
> (`consumeReply`) — and SM6.C.7 ("reply-replay protection") is that single-use
> consumption: once delivered the caller is `.ready` and `reply.caller = none`, so
> a second reply fails closed with `.replyCapInvalid`.  The `reply.caller` write is
> serialised by the per-object reply write-lock (`replyLock`) carried in the
> reply/replyRecv lock-set footprints (`lockSet_endpointReply` / `lockSet_replyRecv`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  The cross-core reply transition (plan §3.1, SM6.C.1)
-- ============================================================================

/-- WS-SM SM6.C.1 (plan §3.1): endpoint reply across cores.

Mirrors the single-core `endpointReply`, with one cross-core substitution: on a
reply that unblocks the recorded caller (`target`, in `blockedOnReply` state with
the matching authorised `replier`), the caller is woken through the SM5.C
`wakeThread … executingCore`, which enqueues it on its *home* core
(`determineTargetCore`) and returns `some (target, .reschedule)` when that core
differs from `executingCore` (the cross-core poke the runtime fires).  The
replier is *not* descheduled (reply is non-blocking from its perspective).

The confused-deputy gate is unchanged: the reply succeeds only when `replier ==
expected` (the `replyTarget` the caller recorded at `endpointCall` time), and
fails closed (`.replyCapInvalid`) on a `none` recorded target, a mismatched
replier, or a caller not in `blockedOnReply` state — the SM6.C.7 replay barrier.

Returns the post-state paired with `Except KernelError (Option (CoreId ×
SgiKind))`: an error on a failed step (pre-state returned, so a `withLockSet`
bracket still releases cleanly), or `.ok sgi?` with the optional cross-core SGI
to emit after the state commit. -/
def endpointReplyOnCore (replier : SeLe4n.ThreadId) (target : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  if msg.registers.size > maxMessageRegisters then (st, .error .ipcMessageTooLarge)
  else if msg.caps.size > maxExtraCaps then (st, .error .ipcMessageTooManyCaps)
  else
  match lookupTcb st target with
  | none => (st, .error .objectNotFound)
  | some tcb =>
      match tcb.ipcState with
      | .blockedOnReply _ replyTarget =>
          match replyTarget with
          | none => (st, .error .replyCapInvalid)
          | some expected =>
            if replier == expected then
              match storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) with
              | .error e => (st, .error e)
              | .ok st' => ((wakeThread st' target executingCore).1,
                            .ok (wakeThread st' target executingCore).2)
            else (st, .error .replyCapInvalid)
      | _ => (st, .error .replyCapInvalid)

/-- WS-SM SM6.C.5 (plan §3.1): endpoint receive across cores — the receive leg of
`replyRecv`.

Mirrors the single-core `endpointReceiveDual`, with two cross-core
substitutions:

* **Block path** (no waiting sender) — the receiver is removed from *its own*
  core's run queue/current via `removeRunnableOnCore … executingCore` (the SM6.A
  generalisation of `removeRunnable`).
* **`blockedOnSend` rendezvous** — the woken sender is routed to *its* home core
  via `wakeThread … executingCore`, surfacing the optional `.reschedule` SGI.

A `blockedOnCall` sender becomes `blockedOnReply (some receiver)` (not woken,
matching the Call contract), so it surfaces no SGI.

Returns the post-state paired with `Except KernelError (ThreadId × Option (CoreId
× SgiKind))`: the rendezvous/blocked thread id and the optional cross-core SGI
(the woken `blockedOnSend` sender's, else `none`). -/
def endpointReceiveDualOnCore (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (SeLe4n.ThreadId × Option (CoreId × SgiKind)) :=
  match st.getEndpoint? endpointId with
  | some ep =>
      match ep.sendQ.head with
      | some _ =>
          match endpointQueuePopHead endpointId false st with
          | .error e => (st, .error e)
          | .ok (sender, senderTcb, st') =>
              let (senderMsg, senderWasCall) :=
                (senderTcb.pendingMessage, match senderTcb.ipcState with
                  | .blockedOnCall _ => true
                  | _ => false)
              if senderWasCall then
                match storeTcbIpcStateAndMessage st' sender
                    (.blockedOnReply endpointId (some receiver)) none with
                | .error e => (st, .error e)
                | .ok st'' =>
                    match storeTcbIpcStateAndMessage st'' receiver .ready senderMsg with
                    | .ok st''' => (st''', .ok (sender, none))
                    | .error e => (st, .error e)
              else
                match storeTcbIpcStateAndMessage st' sender .ready none with
                | .error e => (st, .error e)
                | .ok st'' =>
                    -- Cross-core sender wake (SM5.C): route to the sender's home core.
                    match storeTcbIpcStateAndMessage (wakeThread st'' sender executingCore).1
                        receiver .ready senderMsg with
                    | .ok st4 => (st4, .ok (sender, (wakeThread st'' sender executingCore).2))
                    | .error e => (st, .error e)
      | none =>
          match cleanupPreReceiveDonationChecked st receiver with
          | .error e => (st, .error e)
          | .ok stClean =>
            match endpointQueueEnqueue endpointId true receiver stClean with
            | .error e => (st, .error e)
            | .ok st' =>
                match storeTcbIpcState st' receiver (.blockedOnReceive endpointId) with
                | .error e => (st, .error e)
                | .ok st'' => (removeRunnableOnCore st'' receiver executingCore, .ok (receiver, none))
  | none =>
      -- Typed-accessor dispatch (AK7 cascade discipline): `getEndpoint?` is `none`
      -- for both an absent object and a wrong-kinded one.  Recover the single-core
      -- error distinction without a raw object-store variant match: a
      -- present-but-wrong-kind object fails with `.invalidCapability`, a genuinely
      -- absent one with `.objectNotFound` (mirrors `endpointCallOnCore`).
      if (st.objects[endpointId]?).isSome then (st, .error .invalidCapability)
      else (st, .error .objectNotFound)

/-- WS-SM SM6.C.5 (plan §3.1): reply-and-receive across cores.

The cross-core generalisation of `endpointReplyRecv`: the reply leg
(`endpointReplyOnCore receiver replyTarget …` — the server `receiver` replies to
the recorded caller `replyTarget`) then the receive leg
(`endpointReceiveDualOnCore endpointId receiver …` — the server receives its next
request).  Surfaces the **union** of both legs' cross-core SGIs (the reply-leg
caller wake and, on a `blockedOnSend` rendezvous, the receive-leg sender wake).

On any failed leg the pre-state is returned (`withLockSet` clean release), so the
combined op is all-or-nothing exactly as the single-core `endpointReplyRecv`. -/
def endpointReplyRecvOnCore (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyTarget : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) :
    SystemState × Except KernelError (List (CoreId × SgiKind)) :=
  match endpointReplyOnCore receiver replyTarget msg executingCore st with
  | (_, .error e) => (st, .error e)
  | (st1, .ok replySgi?) =>
      match endpointReceiveDualOnCore endpointId receiver executingCore st1 with
      | (_, .error e) => (st, .error e)
      | (st2, .ok (_, recvSgi?)) => (st2, .ok (replySgi?.toList ++ recvSgi?.toList))

-- ============================================================================
-- §2  Pre-resolution helpers + state-resolved lock-sets (plan §3.1)
-- ============================================================================

/-- WS-SM SM6.C.3: the SchedContext the replier would *return* on this reply —
its own donated SC (a `.donated scId originalOwner` binding) paired with the
original owner, if any.  A replier that is `.bound _` or `.unbound` returns
nothing (matching `applyReplyDonation`), so the SC write lock and the
original-owner TCB write lock are in the `lockSet_endpointReply` footprint iff the
replier currently holds a donated SC to return. -/
def endpointReplyDonation? (st : SystemState) (replier : SeLe4n.ThreadId) :
    Option (SeLe4n.SchedContextId × SeLe4n.ThreadId) :=
  match st.getTcb? replier with
  | some tcb =>
      match tcb.schedContextBinding with
      | .donated scId originalOwner => some (scId, originalOwner)
      | _                           => none
  | none => none

/-- WS-SM SM6.C.1: the concrete lock-set a cross-core `endpointReplyOnCore` on
state `st` acquires — `lockSet_endpointReply` with the returned SchedContext +
original owner **pre-resolved from `st`** via `endpointReplyDonation?` (the
replier's own donated binding).  The caller being replied to (`target`) is a known
argument, contributing its TCB **write** lock (the reply-state lifecycle write).
This is the footprint the runtime `withLockSet` bracket (the SM5.I FFI seam)
acquires before invoking `endpointReplyOnCore replier target … executingCore st`. -/
def lockSet_endpointReplyOnCore (st : SystemState) (replier : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (target : SeLe4n.ThreadId) : LockSet :=
  -- WS-SM SM6.D: the reply consumes the first-class Reply object the caller
  -- (`target`) is blocked on — `target.replyObject` (its forward C-link, set by
  -- `linkCallerReply`).  Resolving it from `st` puts the per-object reply
  -- **write**-lock in the footprint, serialising the `reply.caller := none`
  -- consume against any other core using a copied reply cap.
  lockSet_endpointReply replier cnodeRootObjId target
    ((endpointReplyDonation? st replier).map (·.1))
    ((endpointReplyDonation? st replier).map (·.2))
    ((st.getTcb? target).bind (·.replyObject))

/-- WS-SM SM6.C.5: the concrete lock-set a cross-core `endpointReplyRecvOnCore` on
state `st` acquires — `lockSet_replyRecv` with the new sender (the receive-leg
rendezvous head), the returned SchedContext, and its original owner all
**pre-resolved from `st`**.  The new sender is the endpoint's send-queue head (the
thread the receive leg rendezvouses with, if any); the donation pair is the
replier's own donated binding. -/
def lockSet_endpointReplyRecvOnCore (st : SystemState) (replier : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (endpointObjId : SeLe4n.ObjId) : LockSet :=
  let newSender? := match st.getEndpoint? endpointObjId with
    | some ep => ep.sendQ.head
    | none    => none
  -- WS-SM SM6.D: replyRecv consumes the prior caller's Reply object and re-links
  -- it to the next caller — the reply object is `target.replyObject`; resolving it
  -- from `st` puts the per-object reply write-lock in the footprint.
  lockSet_replyRecv replier cnodeRootObjId target endpointObjId newSender?
    ((endpointReplyDonation? st replier).map (·.1))
    ((endpointReplyDonation? st replier).map (·.2))
    ((st.getTcb? target).bind (·.replyObject))

-- ============================================================================
-- §3  Path reduction lemmas (full characterisation of each control path)
-- ============================================================================

/-- WS-SM SM6.C.1: full reduction of the **reply** (success) path — the caller
`target` is in `blockedOnReply` state recording the authorised replier `expected`,
and `replier == expected`.  The post-state delivers the reply message + `.ready`
to the caller and wakes it cross-core; the surfaced SGI is exactly the caller
wake's. -/
theorem endpointReplyOnCore_reply_eq
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hReplier : (replier == expected) = true)
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st') :
    endpointReplyOnCore replier target msg executingCore st
      = ((wakeThread st' target executingCore).1, .ok (wakeThread st' target executingCore).2) := by
  unfold endpointReplyOnCore
  rw [if_neg hSz1, if_neg hSz2]
  simp only [hLk, hIpc]
  rw [if_pos hReplier]
  simp only [hStore]

/-- WS-SM SM6.C.7 (replay barrier): a reply to a caller **not** in `blockedOnReply`
state fails closed with `.replyCapInvalid` — no state change, no wake.  Because a
*delivered* reply leaves the caller `.ready` (SM6.C.6 lifecycle), this is exactly
the protection against replaying a consumed reply linkage: the second reply finds
the caller `.ready`, not `blockedOnReply`, and is rejected. -/
theorem endpointReplyOnCore_not_blocked_eq
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (tcb : TCB)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt) :
    endpointReplyOnCore replier target msg executingCore st = (st, .error .replyCapInvalid) := by
  unfold endpointReplyOnCore
  rw [if_neg hSz1, if_neg hSz2]
  simp only [hLk]

/-- WS-SM SM6.C.1/.7: a reply whose `replier` does **not** match the caller's
recorded authorised replier (`expected`) fails closed with `.replyCapInvalid`
(the confused-deputy gate) — no state change, no wake. -/
theorem endpointReplyOnCore_wrong_replier_eq
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hReplier : (replier == expected) = false) :
    endpointReplyOnCore replier target msg executingCore st = (st, .error .replyCapInvalid) := by
  unfold endpointReplyOnCore
  rw [if_neg hSz1, if_neg hSz2]
  simp only [hLk, hIpc]
  rw [if_neg (by simp [hReplier])]

-- ============================================================================
-- §4  SM6.C.2 — Cross-core caller wake: SGI emission (`endpointReply_remote_wake`)
-- ============================================================================

/-- WS-SM SM6.C.2 (`endpointReply_remote_wake`).  When a cross-core reply
unblocks the recorded caller whose home core differs from the executing core, the
operation surfaces a `.reschedule` SGI targeting the caller's core — the
cross-core poke the runtime fires after the state commit.  The target core is the
caller's home core `determineTargetCore … target` (its `cpuAffinity`), read at the
wake site `st'`; the reply store mutates only the caller's `ipcState` /
`pendingMessage`, never its `cpuAffinity`, so this is the same core the plan's
pre-state target names. -/
theorem endpointReplyOnCore_remote_wake
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (targetTcb' : TCB)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hReplier : (replier == expected) = true)
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hTcb' : st'.getTcb? target = some targetTcb')
    (hRemote : determineTargetCore st' target ≠ executingCore) :
    (endpointReplyOnCore replier target msg executingCore st).2
      = .ok (some (determineTargetCore st' target, SgiKind.reschedule)) := by
  rw [endpointReplyOnCore_reply_eq replier target msg executingCore st st' tcb ep expected
        hSz1 hSz2 hLk hIpc hReplier hStore]
  show Except.ok (wakeThread st' target executingCore).2
      = Except.ok (some (determineTargetCore st' target, SgiKind.reschedule))
  rw [wakeThread_emits_sgi_if_remote st' target executingCore targetTcb' hTcb' hRemote]

/-- WS-SM SM6.C.2: dually, a cross-core reply whose caller is *local* (home core =
executing core) surfaces **no** SGI — the local scheduler picks the newly-runnable
caller up on its next decision. -/
theorem endpointReplyOnCore_no_sgi_if_local
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hReplier : (replier == expected) = true)
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hLocal : determineTargetCore st' target = executingCore) :
    (endpointReplyOnCore replier target msg executingCore st).2 = .ok none := by
  rw [endpointReplyOnCore_reply_eq replier target msg executingCore st st' tcb ep expected
        hSz1 hSz2 hLk hIpc hReplier hStore]
  show Except.ok (wakeThread st' target executingCore).2 = Except.ok none
  rw [wakeThread_no_sgi_if_local st' target executingCore hLocal]

/-- WS-SM SM6.C.2: a failed reply (wrong replier, no recorded target, caller not
blocked, or absent caller) surfaces no SGI — no thread is woken, so there is no
cross-core poke.  Completes the SGI characterisation: a reply pokes a remote core
*only* when it wakes a caller bound to that remote core. -/
theorem endpointReplyOnCore_not_blocked_no_sgi
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (tcb : TCB)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt) :
    (endpointReplyOnCore replier target msg executingCore st).2 = .error .replyCapInvalid := by
  rw [endpointReplyOnCore_not_blocked_eq replier target msg executingCore st tcb hSz1 hSz2 hLk hIpc]

-- ============================================================================
-- §5  SM6.C.1/.5 — Lock-set correctness (`.reply` / `.replyRecv`)
-- ============================================================================

/-- WS-SM SM6.C.1 (`endpointReply_lockSet_correct`): the `endpointReply` lock-set
is **hierarchically correct** — every lock it declares has a kind in
`permittedKinds .reply` (so the acquisitions respect the SM0.I lock ladder), and
its keys are duplicate-free (the SM3.B well-formedness `LockSet` carries by
construction).  Together these are the structural soundness conditions the
deadlock-freedom theorem (2.1.9) and the 2PL serializability corollary (2.1.11)
consume. -/
theorem endpointReplyOnCore_lockSet_correct
    (replier : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (donatedSc? : Option SeLe4n.SchedContextId) (donatedOwner? : Option SeLe4n.ThreadId) :
    (∀ p ∈ (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?).pairs,
        p.fst.kind ∈ permittedKinds .reply) ∧
    ((lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?).pairs.map
        (·.fst)).Nodup :=
  ⟨lockSet_consistent_reply replier cnRoot target donatedSc? donatedOwner?,
   (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?).hUniqueKeys⟩

/-- WS-SM SM6.C.1: the **state-resolved** reply lock-set
(`lockSet_endpointReplyOnCore`, with the returned SchedContext + original owner
pre-resolved from `st`) is hierarchically correct — every lock it declares has a
kind permitted for `.reply`.  This is the form the runtime acquisition consumes,
so its correctness is a corollary of the parametric `lockSet_consistent_reply`. -/
theorem lockSet_endpointReplyOnCore_correct
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) :
    ∀ p ∈ (lockSet_endpointReplyOnCore st replier cnodeRootObjId target).pairs,
      p.fst.kind ∈ permittedKinds .reply := by
  unfold lockSet_endpointReplyOnCore
  exact lockSet_consistent_reply replier cnodeRootObjId target _ _ _

/-- WS-SM SM6.C.5 (`endpointReplyRecv_lockSet_correct`): the combined `replyRecv`
lock-set — the reply footprint extended with the receive-leg endpoint write and
the optional new sender's TCB write — is **hierarchically correct**: every
declared lock has a kind in `permittedKinds .replyRecv`, and its keys are
duplicate-free. -/
theorem endpointReplyRecv_lockSet_correct
    (replier : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (newSender? : Option SeLe4n.ThreadId)
    (donatedSc? : Option SeLe4n.SchedContextId) (donatedOwner? : Option SeLe4n.ThreadId) :
    (∀ p ∈ (lockSet_replyRecv replier cnRoot target epId newSender? donatedSc? donatedOwner?).pairs,
        p.fst.kind ∈ permittedKinds .replyRecv) ∧
    ((lockSet_replyRecv replier cnRoot target epId newSender? donatedSc? donatedOwner?).pairs.map
        (·.fst)).Nodup :=
  ⟨lockSet_consistent_replyRecv replier cnRoot target epId newSender? donatedSc? donatedOwner?,
   (lockSet_replyRecv replier cnRoot target epId newSender? donatedSc? donatedOwner?).hUniqueKeys⟩

/-- WS-SM SM6.C.5: the **state-resolved** replyRecv lock-set is hierarchically
correct — the form the runtime acquisition consumes. -/
theorem lockSet_endpointReplyRecvOnCore_correct
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId) :
    ∀ p ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target endpointObjId).pairs,
      p.fst.kind ∈ permittedKinds .replyRecv := by
  unfold lockSet_endpointReplyRecvOnCore
  exact lockSet_consistent_replyRecv replier cnodeRootObjId target endpointObjId _ _ _ _

-- ============================================================================
-- §6  SM6.C.4 / SM6.C.6 — Reply payload delivery + reply-state lifecycle
-- ============================================================================

/-- The post-state TCB after a `_fromTcb` store: the target resolves to exactly
the supplied `tcb` with its `ipcState` / `pendingMessage` updated.  (`invExt`-
dependent: the RobinHood self-lookup needs the store well-formedness invariant.) -/
theorem storeTcbIpcStateAndMessage_fromTcb_self
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbIpcStateAndMessage_fromTcb st tid tcb ipc msg = .ok st') :
    st'.getTcb? tid = some { tcb with ipcState := ipc, pendingMessage := msg } := by
  unfold storeTcbIpcStateAndMessage_fromTcb at hStore
  cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
  | error e => exact absurd hStore (by simp [hSO])
  | ok p =>
      simp only [hSO, Except.ok.injEq] at hStore
      subst hStore
      exact (SystemState.getTcb?_eq_some_iff p.2 tid _).mpr
        (storeObject_objects_eq' st tid.toObjId _ p hObjInv hSO)

/-- The cross-core `wakeThread` of an already-`.ready` thread preserves every
thread's `getTcb?` (the wake is object-invisible — keystone
`wakeThread_objects_getElem_eq_of_ready`). -/
private theorem wakeThread_getTcb?_eq_of_ready (st : SystemState) (tid : SeLe4n.ThreadId)
    (ec : CoreId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    (wakeThread st tid ec).1.getTcb? x = st.getTcb? x := by
  simp only [SystemState.getTcb?]
  rw [wakeThread_objects_getElem_eq_of_ready st tid ec tcb hTcb hReady hInv x.toObjId]

/-- WS-SM SM6.C.4 (`endpointReply_perCore_delivery`): the reply payload is
delivered to the **right TCB** — the recorded caller `target` (and no other).
After the cross-core reply the caller resolves to a TCB whose `ipcState` is
`.ready` and whose `pendingMessage` is exactly the reply `msg`.  The
caller-TCB write lock (`lockSet_endpointReply_target_tcb_write_mem`) covers this
write, so under the 2PL bracket the payload cannot be mis-delivered to a
concurrently-running thread on another core (the "reply payload delivered to wrong
TCB" risk row, mitigated). -/
theorem endpointReplyOnCore_perCore_delivery
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hReplier : (replier == expected) = true)
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hObjInv : st.objects.invExt) :
    ∃ t, (endpointReplyOnCore replier target msg executingCore st).1.getTcb? target = some t
      ∧ t.ipcState = .ready ∧ t.pendingMessage = some msg := by
  have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
    rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
  have hInv' : st'.objects.invExt :=
    storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready (some msg) hObjInv hStore'
  have hSelf : st'.getTcb? target = some { tcb with ipcState := .ready, pendingMessage := some msg } :=
    storeTcbIpcStateAndMessage_fromTcb_self st st' target tcb .ready (some msg) hObjInv hStore
  rw [endpointReplyOnCore_reply_eq replier target msg executingCore st st' tcb ep expected
        hSz1 hSz2 hLk hIpc hReplier hStore]
  refine ⟨{ tcb with ipcState := .ready, pendingMessage := some msg }, ?_, rfl, rfl⟩
  show (wakeThread st' target executingCore).1.getTcb? target = some _
  rw [wakeThread_getTcb?_eq_of_ready st' target executingCore
        { tcb with ipcState := .ready, pendingMessage := some msg } hSelf rfl hInv' target]
  exact hSelf

-- ── SM6.C.6 — the caller-TCB write lock is in the footprint (the reply-state
--    lifecycle write `blockedOnReply → .ready` lands on this lock) ──

/-- A **write**-mode `insertOrMerge` always leaves its key write-locked
(write is the `AccessMode.lub` top).  (Local private copy of the SM6.B structural
fact, kept private so the reply module needs no import of the notification
module.) -/
private theorem self_write_mem_insertOrMerge (S : LockSet) (l : LockId) :
    (l, AccessMode.write) ∈ (S.insertOrMerge l AccessMode.write).pairs := by
  unfold LockSet.insertOrMerge
  split
  · rename_i hc
    rw [LockSet.containsKey, List.any_eq_true] at hc
    obtain ⟨p, hpmem, hpfst⟩ := hc
    have hEq : p.fst = l := of_decide_eq_true hpfst
    exact List.mem_map.mpr ⟨p, hpmem, by rw [if_pos hEq, AccessMode.lub_write_right]⟩
  · exact List.mem_cons.mpr (Or.inl rfl)

/-- An existing write-lock survives *any* further write `insertOrMerge`: a
distinct key leaves it untouched; the same key merges write+write = write. -/
private theorem write_mem_insertOrMerge_of_write_mem (S : LockSet) (l k : LockId)
    (h : (l, AccessMode.write) ∈ S.pairs) :
    (l, AccessMode.write) ∈ (S.insertOrMerge k AccessMode.write).pairs := by
  by_cases hEq : k = l
  · rw [hEq]; exact self_write_mem_insertOrMerge S l
  · exact mem_insertOrMerge_of_mem_of_ne S k AccessMode.write (l, AccessMode.write) h
      (fun hh => hEq hh.symm)

/-- An existing write-lock survives `lockSetExtendOpt` with a *write*-mode
extension (a `.map (fun x => (f x, .write))`): the `none` extension is the
identity; a `some` extension is `write_mem_insertOrMerge_of_write_mem`. -/
private theorem write_mem_lockSetExtendOpt_map {α : Type} (S : LockSet) (l : LockId)
    (o : Option α) (f : α → LockId) (h : (l, AccessMode.write) ∈ S.pairs) :
    (l, AccessMode.write)
      ∈ (lockSetExtendOpt S (o.map (fun x => (f x, AccessMode.write)))).pairs := by
  cases o with
  | none => simpa only [Option.map_none, lockSetExtendOpt] using h
  | some x =>
      simp only [Option.map_some, lockSetExtendOpt]
      exact write_mem_insertOrMerge_of_write_mem S l (f x) h

/-- WS-SM SM6.C.6 (reply-state lifecycle under lock-set): the **caller-TCB write
lock** — under which the reply writes the caller's `blockedOnReply → .ready`
state transition (the reply-state "object" lifecycle; this kernel has no separate
reply object — see the module note) — is a declared member of the
`endpointReply` lock-set footprint, present whether or not a SchedContext is
returned and *whatever* the original owner is (even if the original owner is the
caller itself, the `AccessMode.lub` merge keeps the write).  Together with
`endpointReplyOnCore_perCore_delivery` this makes "reply object lifecycle under
lock-set" concrete: the lifecycle write lands on a held write lock. -/
theorem lockSet_endpointReply_target_tcb_write_mem
    (replier : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (donatedSc? : Option SeLe4n.SchedContextId) (donatedOwner? : Option SeLe4n.ThreadId) :
    (tcbLock target, AccessMode.write)
      ∈ (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?).pairs := by
  have hBase : (tcbLock target, AccessMode.write)
      ∈ (lockSetOfList [(tcbLock replier, .write), (cnodeLock cnRoot, .read),
            (tcbLock target, .write)]).pairs := by
    show (tcbLock target, AccessMode.write)
      ∈ (((LockSet.empty.insertOrMerge (tcbLock replier) .write).insertOrMerge
          (cnodeLock cnRoot) .read).insertOrMerge (tcbLock target) AccessMode.write).pairs
    exact self_write_mem_insertOrMerge _ (tcbLock target)
  unfold lockSet_endpointReply
  exact write_mem_lockSetExtendOpt_map _ _ donatedOwner? (fun ot => tcbLock ot)
    (write_mem_lockSetExtendOpt_map _ _ donatedSc? (fun sc => schedContextLock sc) hBase)

/-- WS-SM SM6.D (reply-object lifecycle under lock-set): the **per-object reply
write lock** — under which the reply consumes the first-class Reply object
(`consumeReply` writes `reply.caller := none`, the single-use barrier) — is a
declared member of the `endpointReply` lock-set footprint once the reply object
`rid` is resolved (`replyId := some rid`).  Together with
`lockSet_endpointReply_target_tcb_write_mem` and `endpointReplyOnCore_perCore_delivery`
this makes the SM6.C.6 reply-object lifecycle concrete: the `reply.caller := none`
consume lands on a held per-object write lock, serialised under 2PL against a
second core using a copied reply cap (the SM6.D fix for PR #822 review 6J90-5). -/
theorem lockSet_endpointReply_reply_write_mem
    (replier : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (donatedSc? : Option SeLe4n.SchedContextId) (donatedOwner? : Option SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) :
    (replyLock rid, AccessMode.write)
      ∈ (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner? (some rid)).pairs := by
  unfold lockSet_endpointReply
  exact self_write_mem_insertOrMerge _ (replyLock rid)

-- ============================================================================
-- §7  SM6.C.7 — Reply-replay protection
-- ============================================================================

/-- A successful `lookupTcb` witnesses non-reservation (reservation is state-
independent), so the post-reply caller — which `getTcb?`-resolves to `.ready` —
also `lookupTcb`-resolves to that TCB on the post-state. -/
private theorem lookupTcb_some_of_getTcb?_some
    (st0 stx : SystemState) (tid : SeLe4n.ThreadId) (tcb0 t : TCB)
    (hLk0 : lookupTcb st0 tid = some tcb0)
    (hGet : stx.getTcb? tid = some t) :
    lookupTcb stx tid = some t := by
  -- The object-store fact is obtained through the *typed* `getTcb?` accessor
  -- (`getTcb?_eq_some_iff`), not a raw object-store boundary lookup (AK7 cascade
  -- discipline): its type (the object-store entry at the TCB's id is a `.tcb t`) is
  -- inferred, and rewrites the `lookupTcb` match once the reserved guard is cleared.
  have hObj := (SystemState.getTcb?_eq_some_iff stx tid t).mp hGet
  have hNotRes : tid.isReserved ≠ true := by
    cases hr : tid.isReserved with
    | true => simp [lookupTcb, hr] at hLk0
    | false => exact Bool.false_ne_true
  unfold lookupTcb
  rw [if_neg hNotRes, hObj]

/-- WS-SM SM6.C.7 (replay barrier, composed): a reply cap is **single use**.
Once a reply is delivered, the caller is `.ready` (SM6.C.6 lifecycle / SM6.C.4
delivery), so a **second** reply to the same caller — whatever the (re-)claimed
replier or message — fails closed with `.replyCapInvalid`.  The reply linkage was
consumed by the first delivery; it cannot be replayed to wake the caller a second
time or inject a second payload.  (Composes the delivery `.ready` post-state with
the replay-rejection `endpointReplyOnCore_not_blocked_eq`.) -/
theorem endpointReplyOnCore_replay_rejected
    (replier replier2 target : SeLe4n.ThreadId) (msg msg2 : IpcMessage)
    (executingCore executingCore2 : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hReplier : (replier == expected) = true)
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hObjInv : st.objects.invExt)
    (hSz1' : ¬ msg2.registers.size > maxMessageRegisters)
    (hSz2' : ¬ msg2.caps.size > maxExtraCaps) :
    (endpointReplyOnCore replier2 target msg2 executingCore2
        (endpointReplyOnCore replier target msg executingCore st).1).2 = .error .replyCapInvalid := by
  obtain ⟨t, hGet, hReady, _⟩ :=
    endpointReplyOnCore_perCore_delivery replier target msg executingCore st st' tcb ep expected
      hSz1 hSz2 hLk hIpc hReplier hStore hObjInv
  have hLkPost : lookupTcb (endpointReplyOnCore replier target msg executingCore st).1 target = some t :=
    lookupTcb_some_of_getTcb?_some st _ target tcb t hLk hGet
  rw [endpointReplyOnCore_not_blocked_no_sgi replier2 target msg2 executingCore2
        (endpointReplyOnCore replier target msg executingCore st).1 t hSz1' hSz2' hLkPost
        (by intro ep' rt'; rw [hReady]; exact fun h => ThreadIpcState.noConfusion h)]

-- ============================================================================
-- §8  SM6.C — 2PL atomicity of the reply syscalls under their lock-set
-- ============================================================================

/-- WS-SM SM6.C (`endpointReply_atomic_under_lockSet`, plan §3.4 / Theorem
2.1.10): under its `endpointReply` lock-set the cross-core transition is a single
two-phase-locked atomic step — wrapping `endpointReplyOnCore` in `withLockSet`
decomposes deterministically into the acquire fold, the transition, and the
release fold.  No partial intermediate is observable to a lock-insensitive
observer; this is the operational atomicity the per-core IPC invariant
preservation (SM6.D) rests on. -/
theorem endpointReplyOnCore_atomic_under_lockSet
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (cnRoot : SeLe4n.ObjId) (donatedSc? : Option SeLe4n.SchedContextId)
    (donatedOwner? : Option SeLe4n.ThreadId) (s : SystemState) :
    withLockSet (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?)
        executingCore (endpointReplyOnCore replier target msg executingCore) s
      = (releaseAll executingCore
          (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?).lockAcquireSequence.reverse
          (endpointReplyOnCore replier target msg executingCore
            (acquireAll executingCore
              (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?).lockAcquireSequence s)).1,
         (endpointReplyOnCore replier target msg executingCore
            (acquireAll executingCore
              (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?).lockAcquireSequence s)).2) :=
  lockSet_atomic_under_2pl _ executingCore _ s

/-- WS-SM SM6.C.5 (companion): the cross-core `replyRecv` is likewise a single
2PL-atomic step under its `replyRecv` lock-set. -/
theorem endpointReplyRecvOnCore_atomic_under_lockSet
    (endpointId : SeLe4n.ObjId) (receiver target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (cnRoot : SeLe4n.ObjId) (newSender? : Option SeLe4n.ThreadId)
    (donatedSc? : Option SeLe4n.SchedContextId) (donatedOwner? : Option SeLe4n.ThreadId)
    (s : SystemState) :
    withLockSet (lockSet_replyRecv receiver cnRoot target endpointId newSender? donatedSc? donatedOwner?)
        executingCore (endpointReplyRecvOnCore endpointId receiver target msg executingCore) s
      = (releaseAll executingCore
          (lockSet_replyRecv receiver cnRoot target endpointId newSender? donatedSc? donatedOwner?).lockAcquireSequence.reverse
          (endpointReplyRecvOnCore endpointId receiver target msg executingCore
            (acquireAll executingCore
              (lockSet_replyRecv receiver cnRoot target endpointId newSender? donatedSc? donatedOwner?).lockAcquireSequence s)).1,
         (endpointReplyRecvOnCore endpointId receiver target msg executingCore
            (acquireAll executingCore
              (lockSet_replyRecv receiver cnRoot target endpointId newSender? donatedSc? donatedOwner?).lockAcquireSequence s)).2) :=
  lockSet_atomic_under_2pl _ executingCore _ s

-- ============================================================================
-- §9  SM6.C — Per-core consistency of the reply wake
-- ============================================================================

/-- WS-SM SM6.C (`endpointReply_perCore_consistent`): the reply's cross-core
caller wake is **confined to the caller's home core** — every *other* core's run
queue and current thread are exactly the pre-state's.  The replier is not
descheduled (reply is non-blocking), and the only scheduler edit is the caller's
enqueue on `determineTargetCore st' target`; a concurrent scheduling decision on
any sibling core cannot observe a change to its own per-core state. -/
theorem endpointReplyOnCore_perCore_consistent
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (c' : CoreId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hReplier : (replier == expected) = true)
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hOther : determineTargetCore st' target ≠ c') :
    (endpointReplyOnCore replier target msg executingCore st).1.scheduler.runQueueOnCore c'
        = st.scheduler.runQueueOnCore c'
    ∧ (endpointReplyOnCore replier target msg executingCore st).1.scheduler.currentOnCore c'
        = st.scheduler.currentOnCore c' := by
  have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
    rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
  have hSched : st'.scheduler = st.scheduler :=
    storeTcbIpcStateAndMessage_scheduler_eq st st' target .ready (some msg) hStore'
  rw [endpointReplyOnCore_reply_eq replier target msg executingCore st st' tcb ep expected
        hSz1 hSz2 hLk hIpc hReplier hStore]
  obtain ⟨hRQ, hCur⟩ := wakeThread_independent_of_other_core st' target executingCore c' hOther
  exact ⟨by rw [hRQ, hSched], by rw [hCur, hSched]⟩

end SeLe4n.Kernel
