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
-- **WS-RR RR8.12 (PR #897 Codex review)**: the `.receive` arm's replenish
-- segment is derived from the donation's own guard, so the footprint's module
-- must see `rendezvousDequeuedCall`.  `Operations.Donation` is a sibling of
-- `CrossCore.EndpointCall` -- its closure is `DualQueue.Transport`,
-- `PriorityInheritance.Propagate`, `Operations.Donation.Primitives` and
-- `SchedContext.ReplenishAffinity`, none of which reaches `CrossCore/` -- so
-- this edge closes no cycle.  Asking the question with a locally-spelled copy
-- of that guard is what would let the footprint and the transition disagree.
import SeLe4n.Kernel.IPC.Operations.Donation

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

Authority is the reply **capability** (PR #822 review 6J-lYm): the live `.reply` /
`.replyRecv` arms resolve the cap to `reply.caller = target` and pass the cap
*holder* as `replier`, so this below-API primitive does **not** gate on `replier ==
expected` — a copied/minted (delegated) reply cap held by a *different* server is
legitimate authority (seL4-MCS reply caps are delegatable).  It fails closed
(`.replyCapInvalid`) only on a `none` recorded target or a caller not in
`blockedOnReply` state (the SM6.C.7 replay barrier — a consumed reply leaves the
caller `.ready`).  The `replier` parameter is retained for caller documentation
(the dispatch passes the cap holder) though the gate it fed has been removed.

WS-SM SM6.D (PR #827 review #3 fold): a delivered reply now **consumes** the
answered caller↔Reply link atomically (`removeCallerReplyFrame`, keyed on the
woken caller's own `replyObject`; no-op when unlinked) — the former separate
dispatch-layer consume is folded in, so a direct below-API caller gets full
single-use reply semantics.

**WS-RM (`v0.35.6`)**: the removal is seL4's `reply_remove` — the answered frame
is taken off its reply stack (the frame above links down past it — to the frame
below the cut, or to nothing at a bottom frame) *before* the caller link is
consumed, so no frame is left named by a `prev` whose target has had its links
cleared.  On a head frame the splice is the identity and this
is the pre-`v0.35.6` consume, definitionally.

Returns the post-state paired with `Except KernelError (Option (CoreId ×
SgiKind))`: an error on a failed step (pre-state returned, so a `withLockSet`
bracket still releases cleanly), or `.ok sgi?` with the optional cross-core SGI
to emit after the state commit.  (`_replier` — the cap holder the dispatch passes —
is retained for documentation but unused in the body since the `replier == expected`
gate was removed: authority is the reply capability, PR #822 review 6J-lYm.) -/
def endpointReplyOnCore (_replier : SeLe4n.ThreadId) (target : SeLe4n.ThreadId)
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
          | some _expected =>
            -- PR #822 review 6J-lYm: authority flows from **holding the reply
            -- capability**, not from the syscall issuer being the originally-called
            -- server.  The live `.reply`/`.replyRecv` arms resolve the reply cap to
            -- `reply.caller = target` and pass the *cap holder* as `replier`; a
            -- copied/minted reply cap held by a different server is legitimate
            -- delegated authority (seL4-MCS reply caps are delegatable), so this
            -- below-API primitive no longer gates on `replier == expected`.  The
            -- replay barrier remains: only a caller still in `.blockedOnReply` is
            -- delivered (a consumed reply leaves the caller `.ready`).
            match storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) with
            | .error e => (st, .error e)
            | .ok st' =>
                -- WS-SM SM6.D (PR #827 #3 fold): tear down the answered
                -- caller↔Reply link atomically with the delivery (single-use,
                -- seL4-MCS): clear `reply.caller` + the woken target's
                -- `replyObject`, keyed on the caller's own forward link (no-op
                -- when unlinked).  Formerly the separate dispatch-layer
                -- `consumeCallerReply`; a direct below-API caller now gets full
                -- reply semantics.
                --
                -- **WS-RM (`v0.35.6`)**: and the answered frame comes **off its
                -- reply stack first** — `removeCallerReplyFrame` is seL4's
                -- `reply_remove` with the middle case spliced (WS-HP HP6.3):
                -- the frame above is linked down to the frame below and that
                -- frame back up, then the consume severs the caller link.  Without it
                -- `Reply.consumed` cleared a non-head frame's links while the
                -- frame above still linked down to it, and every later pop of
                -- that stack refused, fail-closed, for good — the wedge a
                -- *delegated* reply capability answering a middle caller
                -- created.  On every reply of the nested Call pattern the
                -- answered frame is the head, the splice is the identity and
                -- this **is** the former consume, definitionally
                -- (`removeCallerReplyFrame_eq_consume_of_no_frame_above`).  Both
                -- legs are total, so the error surface and the surfaced wake SGI
                -- are unchanged.
                match tcb.replyObject with
                | none => ((wakeThread st' target executingCore).1,
                           .ok (wakeThread st' target executingCore).2)
                | some rid =>
                    match removeCallerReplyFrame target rid
                        (wakeThread st' target executingCore).1 with
                    | .ok ((), st'') => (st'', .ok (wakeThread st' target executingCore).2)
                    | .error e => (st, .error e)
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
    (replyId : Option SeLe4n.ReplyId)
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
                    -- WS-SM SM6.D (#7.2 fold): link the dequeued caller (now
                    -- `.blockedOnReply`) to the server-supplied reply object in the
                    -- same transition (the former `linkReceivedCaller` dispatch step).
                    -- A Call rendezvous carrying no reply object fails closed
                    -- (`.replyCapInvalid`); the pre-state is returned, so the caller is
                    -- never stranded `.blockedOnReply` with no reply.
                    match replyId with
                    | none => (st, .error .replyCapInvalid)
                    | some rid =>
                        match SystemState.linkCallerReply sender rid st'' with
                        | .error e => (st, .error e)
                        | .ok ((), stLinked) =>
                            match storeTcbIpcStateAndMessage stLinked receiver .ready senderMsg with
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
                -- PR #873 round 11: clear `pendingMessage` atomically with the block,
                -- exactly as the single-core `endpointReceiveDual` does -- a receiver
                -- that already collected a message would otherwise carry it into
                -- `.blockedOnReceive`, breaking `blockedThreadsPendingMessageConsistent`.
                match storeTcbIpcStateAndMessage st' receiver (.blockedOnReceive endpointId) none with
                | .error e => (st, .error e)
                | .ok st'' =>
                    -- WS-SM SM6.D (#7.2 fold): server-first stash — record the
                    -- server-supplied reply object on the now-`.blockedOnReceive`
                    -- receiver so a later `Call` rendezvous links to it.  `none`
                    -- (a plain receive) clears any stale stash.
                    match st''.getTcb? receiver with
                    | none => (removeRunnableOnCore st'' receiver executingCore, .ok (receiver, none))
                    | some rTcb =>
                        -- WS-SM SM6.D (PR #827 review #6): mirror the single-core stash guard —
                        -- reject an absent / in-use / already-stashed `rid` before the store, so
                        -- a below-API cross-core caller cannot strand the `.blockedOnReceive`
                        -- receiver on a `pendingReceiveReply` that breaks well-formedness.
                        -- PR #827 review #7: validate against the *input* state `st` (not the
                        -- post-block `st''`) for the same reason as the single-core path — the
                        -- post-block receiver self-reserves its own stale `rid` in
                        -- `replyIsStashed`, which would falsely reject a legitimate re-stash.
                        if st.replyStashValid replyId then
                          match storeObject receiver.toObjId
                              (.tcb { rTcb with pendingReceiveReply := replyId }) st'' with
                          | .error e => (st, .error e)
                          | .ok ((), stStashed) =>
                              (removeRunnableOnCore stStashed receiver executingCore, .ok (receiver, none))
                        else (st, .error .replyCapInvalid)
  | none =>
      -- Typed-accessor dispatch (AK7 cascade discipline): `getEndpoint?` is
      -- `none` for both an absent object and a wrong-kinded one, so the
      -- presence question is asked of the kind-agnostic accessor `getObject?`
      -- -- a present-but-wrong-kind object fails with `.invalidCapability`, a
      -- genuinely absent one with `.objectNotFound`.  Reading the store raw
      -- here would have been the very pattern the comment claimed to avoid.
      if (st.getObject? endpointId).isSome then (st, .error .invalidCapability)
      else (st, .error .objectNotFound)

/-- **WS-SM SM6 (PR #873 round 6): the per-core receive that installs the
capabilities a parked send was carrying.**

The cross-core sibling of `endpointReceiveDualWithCaps`, and the one the live
`.receive` arm runs — exactly as `endpointSendDualWithCapsOnCore` is the sibling
of `endpointSendDualWithCaps` and the one the live `.send` arm runs.

**Why it had to exist.**  `endpointSendDualWithCaps`' own docstring already said
what should happen: "If no receiver was waiting (sender enqueued): caps stay in
the message stored in the sender's TCB.  *They will be unwrapped when a receiver
later dequeues the sender.*"  Nothing did.  The live `.receive` ran the bare
`endpointReceiveDualOnCore`, which moves the parked sender's `pendingMessage`
across wholesale and installs nothing, while an immediate rendezvous transferred
the capabilities — so whether a capability arrived depended on which side reached
the endpoint first.  The verified receive-side transition existed and had no live
caller; this is that transition on the per-core base the live arm needs.

**Whose grant right.**  The message's own (`IpcMessage.capsGranted`), recorded by
the sender when it built the message from its endpoint capability.  Not the
receiver's endpoint rights, which is what the single-core sibling used to consult:
that is a different principal's authority, and consulting it here would have left
the orderings disagreeing whenever a granting sender met a non-granting receiver
— the same order-dependence one case narrower.

Returns the post-state, the dequeued sender, the transfer summary, and the
receive's cross-core SGI.  The AK1-I fail-closed `.invalidCapability` on a sender
with no CSpace root is preserved, keeping the NI symmetry all three transfer
paths share. -/
def endpointReceiveDualWithCapsOnCore
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    SystemState ×
      Except KernelError
        (SeLe4n.ThreadId × CapTransferSummary × Option (CoreId × SgiKind)) :=
  match endpointReceiveDualOnCore endpointId receiver replyId executingCore st with
  | (st', .error e) => (st', .error e)
  | (st', .ok (senderId, sgi)) =>
      -- PR #873 round 8: **a receive that dequeued nothing installs nothing.**
      -- `receiveRendezvousSender?` is read at the pre-state, which is what the
      -- transition above branches on.  Testing `pendingMessage` alone was the
      -- capability-duplication defect: the blocking branch returns the receiver's
      -- own id and does not clear that field, so a receiver still holding a
      -- previously delivered caps-bearing message had those capabilities
      -- unwrapped a second time into a fresh receive slot — an extra copy of
      -- authority minted by a receive that consumed no message.
      if (receiveRendezvousSender? st endpointId).isNone then
        (st', .ok (senderId, { results := #[] }, sgi))
      else
      -- A receiver that *enqueued* has no delivered message, and a delivered
      -- message with no caps has nothing to install; both are the empty summary.
      match st'.getTcb? receiver with
      | none => (st', .ok (senderId, { results := #[] }, sgi))
      | some receiverTcb =>
        match receiverTcb.pendingMessage with
        | none => (st', .ok (senderId, { results := #[] }, sgi))
        | some msg =>
          if msg.caps.isEmpty then (st', .ok (senderId, { results := #[] }, sgi))
          else
            -- **WS-RR RR7.33**: the per-core sibling of the single-core receive
            -- arm, and it loses the same lookup for the same reason.  It read
            -- the *sender's* CSpace root only to feed `ipcUnwrapCaps`, which
            -- has not consumed it since the derivation parent moved onto
            -- `TransferCap.srcNode`; its `.invalidCapability` failed the
            -- *receiver's* syscall on a fact about the *sender's* TCB.  Leaving
            -- it here while the single-core arm dropped it would be exactly the
            -- asymmetry AK1-I exists to prevent, one path apart.
            match ipcUnwrapCaps msg receiverCspaceRoot receiverSlotBase
                msg.capsGranted st' with
            | .error e => (st', .error e)
            | .ok (summary, st'') => (st'', .ok (senderId, summary, sgi))

/-- WS-SM SM6 (PR #873 round 6): with nothing to install, the WithCaps per-core
receive is exactly the bare per-core receive — so every capless pin taken against
the bare transition still describes the live arm. -/
theorem endpointReceiveDualWithCapsOnCore_no_caps
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st st' : SystemState)
    (senderId : SeLe4n.ThreadId) (sgi : Option (CoreId × SgiKind))
    (hRecv : endpointReceiveDualOnCore endpointId receiver replyId executingCore st
      = (st', .ok (senderId, sgi)))
    (hNoCaps : ∀ tcb, st'.getTcb? receiver = some tcb →
      ∀ m, tcb.pendingMessage = some m → m.caps.isEmpty = true) :
    endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
        receiverSlotBase executingCore st
      = (st', .ok (senderId, { results := #[] }, sgi)) := by
  unfold endpointReceiveDualWithCapsOnCore
  simp only [hRecv]
  cases hTcb : st'.getTcb? receiver with
  | none => simp
  | some tcb =>
    cases hMsg : tcb.pendingMessage with
    | none => simp [hMsg]
    | some m => simp [hMsg, hNoCaps tcb hTcb m hMsg]

/-- SM8.B.2 (PR #873 round 7), relocated to production at **WS-RR RR8.12**: the
WithCaps per-core **receive** leaves the scheduler where the bare receive left it.

The same shape as `endpointSendDualWithCapsOnCore_scheduler_eq`, and for the same
reason: the extra leg is an `ipcUnwrapCaps`, which installs capabilities into a
CNode and writes no run queue. Every other branch — a receiver that enqueued, a
delivered message with no caps, a sender with no CSpace root — returns the bare
receive's own post-state. -/
theorem endpointReceiveDualWithCapsOnCore_scheduler_eq (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
        receiverSlotBase executingCore st).1.scheduler
      = (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1.scheduler := by
  unfold endpointReceiveDualWithCapsOnCore
  cases hRecv : endpointReceiveDualOnCore endpointId receiver replyId executingCore st with
  | mk stRecv res =>
    cases res with
    | error e => rfl
    | ok pair =>
      obtain ⟨senderId, sgi⟩ := pair
      simp only []
      repeat' split
      all_goals first
        | rfl
        | (rename_i h; exact ipcUnwrapCaps_preserves_scheduler _ _ _ _ _ _ _ h)

/-- **WS-SM SM6 (PR #873 round 8): a receive that dequeued nothing installs
nothing.**

The security property, stated where it can be checked.  `endpointReceiveDual*`'s
blocking branch returns the *receiver's own* id and leaves `pendingMessage`
untouched, so a wrapper that decides by looking at that field alone cannot tell a
fresh delivery from one the receiver has been holding since its last receive.
While `.receive` installed nothing that was harmless; once PR #873 routed the
live arms through this transition it became capability duplication — a receiver
holding one caps-bearing message could re-unwrap it into a new receive slot on
every subsequent receive against an idle endpoint, minting copies of authority
without a sender.

The gate is the endpoint's own pre-state send queue, which is exactly what the
bare transition branches on, so this is a fact about the two agreeing rather than
a guard bolted on beside them. -/
theorem endpointReceiveDualWithCapsOnCore_blocked_installs_nothing
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st st' : SystemState)
    (senderId : SeLe4n.ThreadId) (sgi : Option (CoreId × SgiKind))
    (hBlocked : receiveRendezvousSender? st endpointId = none)
    (hRecv : endpointReceiveDualOnCore endpointId receiver replyId executingCore st
      = (st', .ok (senderId, sgi))) :
    endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
        receiverSlotBase executingCore st
      = (st', .ok (senderId, { results := #[] }, sgi)) := by
  unfold endpointReceiveDualWithCapsOnCore
  simp [hRecv, hBlocked]

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
    (replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    -- WS-SM SM6.D (#7.2 fold): the reply object the server supplies for the *next*
    -- caller on the receive leg, threaded into the folded `endpointReceiveDualOnCore`.
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId)
    (st : SystemState) :
    SystemState × Except KernelError (List (CoreId × SgiKind)) :=
  match endpointReplyOnCore receiver replyTarget msg executingCore st with
  | (_, .error e) => (st, .error e)
  | (st1, .ok replySgi?) =>
      match endpointReceiveDualOnCore endpointId receiver replyId executingCore st1 with
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

/-- **WS-RR RR7.11: the thread a reply capability answers.**

Authority on the reply path flows from *holding* the capability, so the thread a
`.reply` or `.replyRecv` answers is the one recorded in the Reply object the
capability names — `reply.caller`, the forward half of the single-use linkage
`linkCallerReply` writes.

Named once because three places ask it: the live `.reply` arm, the live
`.replyRecv` arm's `resolveReplyRecvReply`, and (RR7.11) the declared-footprint
resolver, which has to name the *same* answered thread the transition will write
or the footprint is about a different operation.  All three previously spelled
out the two-level match, and both live spellings collapse a dangling reply and an
unlinked one onto `.replyCapInvalid`, so nothing is lost by returning `Option`
here and nothing can drift by having one place to change. -/
def replyAnsweredCaller? (st : SystemState) (rid : SeLe4n.ReplyId) :
    Option SeLe4n.ThreadId :=
  (st.getReply? rid).bind (·.caller)

/-- **WS-RR RR7.11**: at a resolved Reply object the answer is its `caller`
field — the rewrite every proof about the reply arms needs. -/
theorem replyAnsweredCaller?_of_getReply (st : SystemState)
    (rid : SeLe4n.ReplyId) (reply : SeLe4n.Kernel.Reply)
    (h : st.getReply? rid = some reply) :
    replyAnsweredCaller? st rid = reply.caller := by
  unfold replyAnsweredCaller?
  rw [h]
  rfl

/-- **WS-RR RR7.11**: and at a dangling one there is no answered thread. -/
theorem replyAnsweredCaller?_of_none (st : SystemState)
    (rid : SeLe4n.ReplyId) (h : st.getReply? rid = none) :
    replyAnsweredCaller? st rid = none := by
  unfold replyAnsweredCaller?
  rw [h]
  rfl

/-- **WS-RR RR7.11**: the resolver is the two-level match it replaced, so the
live arms' behaviour is pinned rather than described. -/
theorem replyAnsweredCaller?_eq_match (st : SystemState) (rid : SeLe4n.ReplyId) :
    replyAnsweredCaller? st rid
      = (match st.getReply? rid with
         | some reply => reply.caller
         | none => none) := by
  unfold replyAnsweredCaller?
  cases st.getReply? rid <;> rfl

/-- WS-SM SM6.D (PR #822 review): the **recorded server** of a `blockedOnReply`
caller — the thread that received the original `Call` (recorded as `some expected`
in `caller.ipcState = .blockedOnReply ep (some expected)`) and therefore holds any
SchedContext the caller donated.  After PR #822 review `6J-lYm` the reply-cap
holder (`replier`) may be a *delegate* (a copied/minted reply cap), so the
SchedContext donation **return** and the priority-inheritance **reversion** must be
keyed on this recorded server, not on `replier`. -/
def recordedReplyServer? (st : SystemState) (target : SeLe4n.ThreadId) :
    Option SeLe4n.ThreadId :=
  match st.getTcb? target with
  | some tcb =>
      match tcb.ipcState with
      | .blockedOnReply _ (some expected) => some expected
      | _                                 => none
  | none => none

-- ----------------------------------------------------------------------------
-- WS-HP HP7 (`v0.35.46`): the retired binding-driven pop trigger
-- ----------------------------------------------------------------------------
--
-- `endpointReplyServerDonation?` stood here from WS-SM SM6.D: the SchedContext a
-- reply returned, resolved from the **recorded server's** `.donated` binding
-- through `recordedReplyServer?`.  It was the reply path's donation-pop trigger
-- until WS-HP HP4 (`v0.35.38`) moved both spines onto the answered reply frame's
-- own `.head` link (`replyFrameHeadHolder?` / `answeredFrameHeadContext?`), and
-- HP6.2 (`v0.35.44`) repointed the last two footprints off it.  After that no
-- transition, footprint or invariant read it, and HP6.8 (`v0.35.45`) made the
-- splice live, which puts the two readings in disagreement on reachable states --
-- at an orphan head, a frame heading a context whose recorded reply server is
-- gone and `.unbound`.
--
-- **It is deleted rather than kept as the legacy reading.**  Its one remaining
-- consumer was the witness that refutes it, and the retired spelling now lives
-- there and nowhere else: `tests/SmpCrossCoreReplySuite.lean`'s
-- `bindingDrivenReplyServerDonation?`, private to that suite, computed beside the
-- live resolver on the agreeing shape and on the orphan head so the assertions are
-- known to discriminate.  That is the pattern `tests/SmpCancellationSuite.lean`
-- §3.20 set for the cancellation side at HP5.5 (`bindingDrivenCancelledCallerDonation?`)
-- and `FrozenOpsSuite`'s `FO-042` set for the frozen surface.
--
-- `recordedReplyServer?` above is **not** retired with it: the reply path still
-- reads it for the priority-inheritance chain walk, which keys on waiters rather
-- than on donations (see `propagatePipChainCrossCore`'s call site).

/-- **WS-RM (`v0.35.6`): the frame *above* the answered caller's reply object** —
the frame the removal's splice re-points at the frame below the cut (or clears, at
a bottom frame), and the member both reply footprints declare for it.

Derived from the **same** expression the arm's existing reply member is resolved
from (`(st.getTcb? target).bind (·.replyObject)`) composed with the splice's own
resolver (`replyFrameAbove?`), so the footprint and the transition cannot
disagree about which frame is answered or which frame sits above it.

`some` exactly when the answered frame is not a stack head and its `next` names a
frame — the shape a *delegated* reply capability answering a middle caller
creates.  On every reply of the nested Call pattern it is `none` and the splice
is the identity. -/
def answeredReplyFrameAbove? (st : SystemState) (target : SeLe4n.ThreadId) :
    Option SeLe4n.ReplyId :=
  ((st.getTcb? target).bind (·.replyObject)).bind (replyFrameAbove? st)

/-- A thread holding no reply object has no frame above one. -/
@[simp] theorem answeredReplyFrameAbove?_of_no_reply (st : SystemState)
    (target : SeLe4n.ThreadId) (h : (st.getTcb? target).bind (·.replyObject) = none) :
    answeredReplyFrameAbove? st target = none := by
  unfold answeredReplyFrameAbove?; rw [h]; rfl

/-- The resolver, unfolded on a thread whose reply object resolves. -/
theorem answeredReplyFrameAbove?_eq (st : SystemState) (target : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (h : (st.getTcb? target).bind (·.replyObject) = some rid) :
    answeredReplyFrameAbove? st target = replyFrameAbove? st rid := by
  unfold answeredReplyFrameAbove?; rw [h]; rfl

-- ============================================================================
-- WS-HP HP1.1: the head-driven donation-pop trigger, at the answered caller
-- ============================================================================

/-- The existing frame-above member is that resolver composed with the splice's
own, so the shared expression has a consumer rather than a second spelling. -/
theorem answeredReplyFrameAbove?_eq_bind (st : SystemState) (target : SeLe4n.ThreadId) :
    answeredReplyFrameAbove? st target
      = (answeredReplyObject? st target).bind (replyFrameAbove? st) := rfl

/-- **WS-HP HP3.1: the frame *below* the answered one** -- the second object the
removal writes, and the member both reply footprints declare for it; declared
at HP3 ahead of HP6.3 (`v0.35.45`), which is the cut that made the removal a
splice and the member live.

Composed exactly as the frame-above member is, so the footprint and the splice
read one answer to "which frame sits below the cut". -/
def answeredReplyFrameBelow? (st : SystemState) (target : SeLe4n.ThreadId) :
    Option SeLe4n.ReplyId :=
  (answeredReplyObject? st target).bind (replyFrameBelow? st)

/-- A thread holding no reply object has no frame below one. -/
@[simp] theorem answeredReplyFrameBelow?_of_no_reply (st : SystemState)
    (target : SeLe4n.ThreadId) (h : answeredReplyObject? st target = none) :
    answeredReplyFrameBelow? st target = none := by
  unfold answeredReplyFrameBelow?; rw [h]; rfl

/-- The resolver, unfolded on a thread whose reply object resolves. -/
theorem answeredReplyFrameBelow?_eq (st : SystemState) (target : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (h : answeredReplyObject? st target = some rid) :
    answeredReplyFrameBelow? st target = replyFrameBelow? st rid := by
  unfold answeredReplyFrameBelow?; rw [h]; rfl

/-- **WS-HP HP3.1: no frame above means no frame below** -- the resolver-level
exclusion, which needs no coherence fact: the frame below is declared only on a
*mid-stack* removal, and a frame with nothing above it is not one.  This is what
keeps the reachable `.replyRecv` bound at eighteen where the declared ceiling
grows. -/
@[simp] theorem answeredReplyFrameBelow?_of_no_frameAbove (st : SystemState)
    (target : SeLe4n.ThreadId) (h : answeredReplyFrameAbove? st target = none) :
    answeredReplyFrameBelow? st target = none := by
  unfold answeredReplyFrameBelow?
  unfold answeredReplyFrameAbove? at h
  cases hRid : answeredReplyObject? st target with
  | none => rfl
  | some rid =>
    have hRid' : (st.getTcb? target).bind (·.replyObject) = some rid := hRid
    rw [hRid'] at h
    exact replyFrameBelow?_of_no_frame_above st rid h

/-- **WS-HP HP6.6: the reply path's lifting of the containment** -- the frame the
removal's splice writes below the cut is the one this arm's footprint declares.

The reply footprints resolve their below-frame member through
`answeredReplyFrameBelow?`, and the operation resolves its own through
`spliceFrameBelow?` on the answered caller's reply object; `spliceFrameBelow?`'s
two extra refusals make its answer strictly narrower, which is the direction a
footprint must satisfy.  Lifted through `answeredReplyObject?` -- the one
expression the arm's existing reply member also comes from -- so the footprint and
the transition cannot disagree about *which* frame is answered either. -/
theorem spliceFrameBelow?_mem_answeredReplyFrameBelow? (st : SystemState)
    (target : SeLe4n.ThreadId) (rid above below : SeLe4n.ReplyId) (r b : Reply)
    (hRid : answeredReplyObject? st target = some rid)
    (hR : st.getReply? rid = some r)
    (hAbove : answeredReplyFrameAbove? st target = some above)
    (h : spliceFrameBelow? st rid r above = some (below, b)) :
    answeredReplyFrameBelow? st target = some below := by
  rw [answeredReplyFrameBelow?_eq st target rid hRid]
  refine spliceFrameBelow?_mem_replyFrameBelow? hR ?_ h
  rw [answeredReplyFrameAbove?_eq_bind, hRid] at hAbove
  exact hAbove

/-- **WS-HP HP1.2: the pop's trigger and the splice's member are mutually
exclusive.**  A frame with a frame above it heads nothing, so no reply both pops a
donation and splices -- the exclusion that keeps the *reachable* footprint bound
where HP3 raises the declared ceiling. -/
theorem answeredFrameHeadContext?_none_of_frameAbove (st : SystemState)
    (target : SeLe4n.ThreadId) (above : SeLe4n.ReplyId)
    (hAbove : answeredReplyFrameAbove? st target = some above) :
    answeredFrameHeadContext? st target = none := by
  rw [answeredReplyFrameAbove?_eq_bind] at hAbove
  cases hRid : answeredReplyObject? st target with
  | none => exact answeredFrameHeadContext?_of_no_reply st target hRid
  | some rid =>
    rw [hRid] at hAbove
    rw [answeredFrameHeadContext?_eq st target rid hRid]
    exact replyFrameHeadHolder?_of_no_head st rid
      (replyFrameHeadContext?_of_frameAbove st rid above hAbove)

/-- And the converse exclusion, at the member HP3 declares: a reply that pops a
donation splices nothing. -/
theorem answeredReplyFrameBelow?_none_of_headContext (st : SystemState)
    (target : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : answeredFrameHeadContext? st target = some (scId, holder)) :
    answeredReplyFrameBelow? st target = none := by
  obtain ⟨rid, hRid, hHead, _⟩ := answeredFrameHeadContext?_eq_some h
  rw [answeredReplyFrameBelow?_eq st target rid hRid,
    replyFrameBelow?_of_headContext st rid scId hHead]

/-- And the frame above is absent there too, which is the same exclusion read from
the other side. -/
theorem answeredReplyFrameAbove?_none_of_headContext (st : SystemState)
    (target : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : answeredFrameHeadContext? st target = some (scId, holder)) :
    answeredReplyFrameAbove? st target = none := by
  obtain ⟨rid, hRid, hHead, _⟩ := answeredFrameHeadContext?_eq_some h
  rw [answeredReplyFrameAbove?_eq_bind, hRid]
  exact replyFrameAbove?_of_headContext st rid scId hHead

/-- **WS-HP HP1.2: the trigger is a function of the store projections it reads** --
the answered caller's TCB, every Reply and every SchedContext.  The frame lemma
every step that writes no chain object crosses. -/
theorem answeredFrameHeadContext?_congr {s1 s2 : SystemState} (target : SeLe4n.ThreadId)
    (hTcb : s2.getTcb? target = s1.getTcb? target)
    (hReply : ∀ rid : SeLe4n.ReplyId, s2.getReply? rid = s1.getReply? rid)
    (hSc : ∀ scId : SeLe4n.SchedContextId,
      s2.getSchedContext? scId = s1.getSchedContext? scId) :
    answeredFrameHeadContext? s2 target = answeredFrameHeadContext? s1 target := by
  unfold answeredFrameHeadContext? answeredReplyObject?
  rw [hTcb]
  cases (s1.getTcb? target).bind (·.replyObject) with
  | none => rfl
  | some rid => exact replyFrameHeadHolder?_congr rid (hReply rid) hSc

/-- WS-SM SM6.C.1: the concrete lock-set a cross-core `endpointReplyOnCore` on
state `st` acquires — `lockSet_endpointReply` with the pop's members **pre-resolved
from `st`** through `answeredFrameHeadContext?`, the expression the pop itself
reads.  The caller being replied to (`target`) is a known argument, contributing
its TCB **write** lock (the reply-state lifecycle write).  This is the footprint
the runtime `withLockSet` bracket (the SM5.I FFI seam) acquires before invoking
`endpointReplyOnCore replier target … executingCore st`.

**WS-HP HP6.2 (`v0.35.44`): resolved from the trigger, not from a binding.**  The
donation members came from `endpointReplyServerDonation?` — the *recorded server's*
binding — while the pop has read the answered frame since HP4.1.  Under the sever
in force until `v0.35.44` the two agreed, and
`lockSet_endpointReplyOnCore_covers_headDrivenPop` held the gap closed with the
two coherence facts as hypotheses; the splice (HP6.8, `v0.35.45`) is the change
that makes them disagree, so the repoint landed *before* it — a transition goes
live only after the declarations that cover it.  Coverage is now definitional
(`lockSet_endpointReplyOnCore_covers_donationPop`), and the stand-in is deleted.

Measured against the composite's three write sites rather than reasoned from the
resolver: `endpointReplyOnCore` writes the answered caller, the Replies and the
frame above; `propagatePipChainCrossCore expected` writes the **recorded server**;
`applyReplyDonationOnCore` writes the SchedContext, the **holder**
(`sc.boundThread`, set `.unbound`) and the answered caller again (the rebind).  So
`server` stays keyed on the recorded server — the reversion's thread — and the
holder takes `donatedScHolderTid`, with the recipient needing no member because it
*is* `target`. -/
def lockSet_endpointReplyOnCore (st : SystemState) (replier : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (target : SeLe4n.ThreadId) : LockSet :=
  -- WS-SM SM6.D: the reply consumes the first-class Reply object the caller
  -- (`target`) is blocked on — `target.replyObject` (its forward C-link, set by
  -- `linkCallerReply`).  Resolving it from `st` puts the per-object reply
  -- **write**-lock in the footprint, serialising the `reply.caller := none`
  -- consume against any other core using a copied reply cap.
  -- **WS-HP HP6.2**: the donation members are the pop's, read off
  -- `answeredFrameHeadContext? st target` -- the composition of
  -- `answeredReplyObject?` with `replyFrameHeadHolder?` that
  -- `applyReplyDonationOnCore` itself reads, so the footprint and the transition
  -- cannot disagree about which context is popped or which thread is unbound.
  -- The first TCB **write** lock stays keyed on the **recorded** server
  -- (`server`), because that is the thread `propagatePipChainCrossCore` walks
  -- from and rewrites; the splice can make it a different thread from the
  -- holder, which is why both are declared.  The cap holder `replier` is only
  -- read-locked via its CSpace root, and in the non-delegated case
  -- (`server = replier`) the footprint is unchanged.
  -- **WS-OD OD3.7**: and the two objects the donation return reads *below* the
  -- reply-stack head.  Resolved through `replyStackBelowHead?` on the very
  -- SchedContext this arm pops — one resolver for one question, so the
  -- footprint cannot disagree with the walk `replyStackOuterCaller?` performs.
  -- Both are `none` below the first donating `Call`, so this arm's declared
  -- footprint was unchanged until OD4.1 (`v0.35.2`) wrote a `scReply`; it is
  -- load-bearing at depth >= 2 and inert at depth 1.
  let server := (recordedReplyServer? st target).getD replier
  let belowHead := match (answeredFrameHeadContext? st target).map (·.1) with
    | none => (none, none)
    | some scId => replyStackBelowHead? st scId
  lockSet_endpointReply server cnodeRootObjId target
    ((answeredFrameHeadContext? st target).map (·.1))
    ((answeredFrameHeadContext? st target).map (·.2))
    ((st.getTcb? target).bind (·.replyObject))
    belowHead.1 belowHead.2
    -- **WS-OD (`v0.35.4`)**: the head of the returned context's stack, which
    -- the pop clears -- resolved on the same context the members above are.
    -- **WS-HP HP6.2**: under the head-driven trigger this is *provably* the
    -- answered caller's own reply object (`answeredFrameHeadContext?_head_is_answered_reply`,
    -- no hypothesis), where the binding reading needed a stated coherence fact to
    -- say so -- one HP7 (`v0.35.46`) deleted, its content having become that
    -- theorem.
    (((answeredFrameHeadContext? st target).map (·.1)).bind (replyStackHead? st))
    -- **WS-RM (`v0.35.6`)**: and the frame above the answered one, which the
    -- removal splices out before it consumes the caller link.
    (answeredReplyFrameAbove? st target)
    -- **WS-HP HP3.1**: and the frame **below** it, which the removal's splice
    -- re-links upward in the same step.  Resolved from the same
    -- `answeredReplyObject?` expression as the member above it, so the two
    -- halves of the splice's write set are read off one answer to "which frame
    -- does this reply answer".
    (answeredReplyFrameBelow? st target)
    -- **WS-HP HP10.6**: and the origin a bottom-of-stack pop redirects the
    -- reservation to -- read off `donationOriginRecipient?` on the very context
    -- this arm pops, which is the expression HP10.7's arm will read, so the
    -- footprint and the transition answer "who receives the reservation" once.
    --
    -- **It is live, not absent**, and the distinction matters: HP10.4 records an
    -- origin on every first push, so a depth-1 donating reply resolves this member
    -- to `some` -- and there the recorded origin *is* the answered caller, so
    -- `insertOrMerge` collapses it into `replyTargetTid` and the declaration is
    -- unchanged.  Where it is a *distinct* key is the out-of-order removal this
    -- phase exists for: the client's own frame came off the bottom of the stack,
    -- reachability now names the intermediate caller, and the recorded origin does
    -- not.  That is precisely the state HP10.7's pop writes a different TCB on, so
    -- the widening is the declaration catching up with the write -- one row before
    -- the code, which is the plan's own numbering rule.
    (((answeredFrameHeadContext? st target).map (·.1)).bind
      (donationOriginRecipient? st))

/-- **WS-OD OD3.5: the SchedContext the receive leg's rendezvous donates.**

`replyRecvBody`'s post-receive stage is `replyRecvPostReceiveDonation`, and it
does not stop at the return: when the thread the receive leg dequeues turns out
to have `Call`ed, it runs `applyCallDonationOnCore nextThread tid`, whose
`donateSchedContext` writes the **new** caller's SchedContext.  That object is
never the returned one — two threads cannot be bound to a single context — so
the arm performs *two* SchedContext hand-offs and declared one, writing a
kernel object under no lock the footprint names.

Resolved through `endpointCallDonatedSc?`, the resolver `.call` uses for the
same question ("what would this thread donate"), applied to the thread the
receive leg will dequeue — `receiveRendezvousSender?`, which is the resolver
`receiveInstallsCaps` and the `newSenderTid` member beside it already use, so
"which thread does this receive dequeue" is answered once for the whole
receiving family rather than by a second `sendQ.head` read that can drift from
it.  Reading the head from the pre-state over-approximates in the safe
direction: the head may turn out to be a plain sender that donates nothing, and
a declared-but-unwritten lock costs contention, never soundness.

**WS-OD OD3.6**: named for the *rendezvous*, not for one arm, because
`.receive` asks it too.  Both receiving arms dequeue a `Call` the same way and
must therefore hand its scheduling context over the same way; a name carrying
`replyRecv` invited the second copy. -/
def receiveRendezvousDonatedSc? (st : SystemState) (endpointObjId : SeLe4n.ObjId) :
    Option SeLe4n.SchedContextId :=
  (receiveRendezvousSender? st endpointObjId).bind (endpointCallDonatedSc? st)

/-- WS-OD OD3.5: an endpoint with nothing queued to send donates nothing. -/
@[simp] theorem receiveRendezvousDonatedSc?_of_no_sender (st : SystemState)
    (endpointObjId : SeLe4n.ObjId)
    (h : receiveRendezvousSender? st endpointObjId = none) :
    receiveRendezvousDonatedSc? st endpointObjId = none := by
  unfold receiveRendezvousDonatedSc?
  rw [h]
  rfl

/-- WS-OD OD3.5: and at a queued sender it is exactly what a `.call` from that
thread would declare — the two arms ask one question. -/
@[simp] theorem receiveRendezvousDonatedSc?_of_sender (st : SystemState)
    (endpointObjId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (h : receiveRendezvousSender? st endpointObjId = some sender) :
    receiveRendezvousDonatedSc? st endpointObjId = endpointCallDonatedSc? st sender := by
  unfold receiveRendezvousDonatedSc?
  rw [h]
  rfl

/-- **WS-OD (`v0.35.4`)**: the **pre-receive return** a `.receive` performs --
`some (scId, owner)` exactly when the arm blocks (no sender queued) and the
receiver holds a donated context, which `cleanupPreReceiveDonationChecked` then
pops back to the frame below before the receiver enqueues
(`endpointReceiveDualOnCore`'s blocking arm; AI4-A / AK1-A).  Resolved from the
two fields the transition branches on: the send-queue head
(`receiveRendezvousSender?`, the resolver every other receive-side member reads)
and the receiver's own binding (`endpointReplyDonation?`, the resolver the reply
arms read the same fact through).  `none` on the rendezvous arm, where the
cleanup does not run.

This return was the receive-side write no footprint named: `.receive`'s
`donatedScId` is the *incoming* rendezvous donation, which is `none` on exactly
the arm where this pop runs, so a `.donated` receiver blocking in `.receive` wrote
its context, the previous owner's TCB, two Replies and `scThreadIndex` under no
declared lock.  **`.replyRecv`'s receive leg runs the same cleanup on the invoking replier, and
declares it through the same two resolvers** (PR #894 review).  It used to cite a
refusal for the shape where the replier's own pop does not coincide with the
recorded server's return — but that theorem never existed, and the refusal it
named (`lockSetForSyscall_replyRecv_delegated`, concluding `none`) had already
been retired by WS-OD OD3.5, so the delegated shape declared a footprint that
omitted these five members rather than falling back to the coarse serialisation.
The coincidence holds on a *non-delegated* reply only, where the recorded server
**is** the replier and the reply leg has just made it `.unbound`, leaving the pop
inert; delegation is exactly what breaks it.  Nothing is excused here now:
`lockSet_endpointReplyRecvOnCore` threads these resolvers on `replier`, and
`lockSet_endpointReplyRecvOnCore_covers_preReturn` is the statement that it
does. -/
def receivePreReturn? (st : SystemState) (endpointObjId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId) :=
  match receiveRendezvousSender? st endpointObjId with
  | some _ => none
  | none => endpointReplyDonation? st receiver

/-- WS-OD (`v0.35.4`): a receive with a sender queued returns nothing before it
blocks -- it does not block. -/
@[simp] theorem receivePreReturn?_of_sender (st : SystemState) (endpointObjId : SeLe4n.ObjId)
    (receiver sender : SeLe4n.ThreadId)
    (h : receiveRendezvousSender? st endpointObjId = some sender) :
    receivePreReturn? st endpointObjId receiver = none := by
  unfold receivePreReturn?; rw [h]

/-- WS-OD (`v0.35.4`): and on the blocking arm it is the receiver's own donated
binding. -/
theorem receivePreReturn?_of_no_sender (st : SystemState) (endpointObjId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (h : receiveRendezvousSender? st endpointObjId = none) :
    receivePreReturn? st endpointObjId receiver = endpointReplyDonation? st receiver := by
  unfold receivePreReturn?; rw [h]

/-- WS-OD (`v0.35.4`): the head, the frame below it and the outer caller the
pre-receive return reaches, derived from `receivePreReturn?`'s context -- the
pop's own three stack objects, in the modes the pop takes them. -/
def receivePreReturnStack? (st : SystemState) (endpointObjId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) :
    Option SeLe4n.ReplyId × Option SeLe4n.ReplyId × Option SeLe4n.ThreadId :=
  match (receivePreReturn? st endpointObjId receiver).map (·.1) with
  | none => (none, none, none)
  | some scId => (replyStackHead? st scId, (replyStackBelowHead? st scId).1,
                  (replyStackBelowHead? st scId).2)

/-- **PR #894 review**: a receive that rendezvouses reaches no stack objects
before it blocks -- it does not block.  The stack-level reading of
`receivePreReturn?_of_sender`, stated beside the resolver rather than re-derived
at each bound, since the sharp `.replyRecv` size bounds are not the only consumer
that will need it. -/
@[simp] theorem receivePreReturnStack?_of_sender (st : SystemState)
    (endpointObjId : SeLe4n.ObjId) (receiver sender : SeLe4n.ThreadId)
    (h : receiveRendezvousSender? st endpointObjId = some sender) :
    receivePreReturnStack? st endpointObjId receiver = (none, none, none) := by
  unfold receivePreReturnStack?
  rw [receivePreReturn?_of_sender st endpointObjId receiver sender h]
  rfl

/-- WS-SM SM6.C.5: the concrete lock-set a cross-core `endpointReplyRecvOnCore` on
state `st` acquires — `lockSet_replyRecv` with the new sender (the receive-leg
rendezvous head), the returned SchedContext, and its original owner all
**pre-resolved from `st`**.  The new sender is the endpoint's send-queue head (the
thread the receive leg rendezvouses with, if any); the donation pair is resolved
from the replyRecv invoker `replier` — the common non-delegated case, where
`replier` *is* the recorded server it received the request on.  (The live dispatch's
donation pop, `replyRecvPopDonation`, keys the **old** return on
the *recorded* server — like the delegatable plain `.reply` path — so a delegated
`replyRecv` returns the previous caller's donation from the server that actually
holds it, while still donating any new received `Call` to the receiver.) -/
def lockSet_endpointReplyRecvOnCore (st : SystemState) (replier : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (endpointObjId : SeLe4n.ObjId) : LockSet :=
  -- **PR #894 review**: through `receiveRendezvousSender?`, not through an
  -- inlined copy of its body.  Every other receive-side member of this footprint
  -- -- the queue-structure neighbour, the re-donated context, and the invoker's
  -- own pre-receive return -- is resolved from that function, and this one asked
  -- the same question a second way.  The two answers are definitionally equal,
  -- so nothing was ever wrong at runtime; what it cost is that no statement about
  -- the send queue could reach this member, which is why the reachable size bound
  -- could not be stated branch-wise until the duplicate went.
  let newSender? := receiveRendezvousSender? st endpointObjId
  -- WS-SM SM6.D: replyRecv consumes the prior caller's Reply object and re-links
  -- it to the next caller — the reply object is `target.replyObject`; resolving it
  -- from `st` puts the per-object reply write-lock in the footprint.
  -- PR #873 round 8: the receive leg installs capabilities when the sender it
  -- dequeues parked a caps-bearing message, and `ipcTransferSingleCap` writes the
  -- receiver's own CSpace root to do it — so the resolved footprint holds that
  -- root in WRITE mode exactly then.  Resolved from `st` by the same predicate
  -- the transition branches on, so the declared footprint and the transition
  -- cannot disagree about when the write happens.
  -- **PR #892 review round 6**: the donation returned on this reply is not the
  -- cap holder's.  This arm read `endpointReplyDonation? st replier`, the
  -- possibly-*delegated* holder's own binding, while the transition writes the
  -- thread the reply leg's own frame names.  On a delegated reply the two are
  -- different threads, so the declared members named a donation the transition
  -- does not touch and omitted the one it does — a footprint that is *false*,
  -- which this tree rates worse than a wide one.
  -- **WS-HP HP6.2**: and the resolver is now the pop's own,
  -- `answeredFrameHeadContext? st target`, for the reason
  -- `lockSet_endpointReplyOnCore`'s docstring records — this arm's reply leg
  -- *is* that transition, so the two footprints read one answer.  Note the
  -- second component's role: it is the thread the pop sets `.unbound`, not the
  -- thread that receives the context (which is `target`).
  --
  -- PR #892 review round 6 could only fix the *resolution* here: the entry
  -- resolver still refused the delegated case outright, because the recorded
  -- server's own TCB write lock had no room left under a `maxLockSetSize` of
  -- nine.  The note that stood here said so, and named the refusing theorem.
  -- **WS-OD OD3.5 is the "future consumer that finds room"** it anticipated —
  -- the ceiling is eleven, the entry resolver declares
  -- (`lockSetForSyscall_replyRecv_delegated_declares`), and the refusal it
  -- named (`lockSetForSyscall_replyRecv_delegated`, concluding `none`) is
  -- retired.  New code must not read the delegated case as falling back to the
  -- coarse serialisation.
  -- **WS-OD OD3.5**: the two members this arm was missing.  The recorded server
  -- is resolved unconditionally — on a non-delegated reply it *is* `replier` and
  -- `insertOrMerge`'s key merge collapses the two, so declaring it costs nothing
  -- there and is the only thing that made the delegated case declarable at all.
  -- It is the thread the priority-inheritance reversion walks from, which the
  -- splice can separate from the pop's holder, so HP6.2 leaves it keyed here.
  -- The re-donated SchedContext comes from the same send-queue head `newSender?`
  -- does, through the resolver `.call` uses for the same question.
  -- **WS-OD OD3.7**: the two below-head reads, resolved on the SchedContext this
  -- arm pops — the same resolver the `.reply` arm uses, for the same
  -- question.  This is the arm the ceiling moved for: at depth ≥ 2 they are two
  -- keys nothing else covers, taking the widest declared footprint to thirteen.
  let belowHead := match (answeredFrameHeadContext? st target).map (·.1) with
    | none => (none, none)
    | some scId => replyStackBelowHead? st scId
  lockSet_replyRecv replier cnodeRootObjId target endpointObjId newSender?
    ((answeredFrameHeadContext? st target).map (·.1))
    ((answeredFrameHeadContext? st target).map (·.2))
    ((st.getTcb? target).bind (·.replyObject))
    (receiveInstallsCaps st endpointObjId)
    (recordedReplyServer? st target)
    (receiveRendezvousDonatedSc? st endpointObjId)
    belowHead.1 belowHead.2
    -- **WS-OD OD3.13**: and the receive leg's queue-structure neighbour, through
    -- the same resolver `.receive` uses -- it is the same transition.
    (receiveSideQueueStructureNeighbor? st endpointObjId)
    -- **WS-OD (`v0.35.4`)**: the old head of the re-donated context -- the frame
    -- the receive leg's push rewrites -- and the head of the returned context's
    -- stack, which the reply leg's pop clears.  Both resolved by
    -- `replyStackHead?` on the contexts the members above already name.
    ((receiveRendezvousDonatedSc? st endpointObjId).bind (replyStackHead? st))
    (((answeredFrameHeadContext? st target).map (·.1)).bind (replyStackHead? st))
    -- **PR #894 review — the INVOKING receiver's own pre-receive return.**  The
    -- receive leg is `.receive`'s transition, so with no sender queued it runs
    -- `cleanupPreReceiveDonationChecked` on `replier`, and the donation return
    -- runs *after* it -- so `replier` still carries the `.donated` binding it
    -- entered with.  Resolved through the same two resolvers `.receive` uses, on
    -- `replier`: the one question this footprint never asked of the invoking
    -- thread, which is why `replier` was consumed exactly once in this body.
    ((receivePreReturn? st endpointObjId replier).map (·.1))
    ((receivePreReturn? st endpointObjId replier).map (·.2))
    (receivePreReturnStack? st endpointObjId replier).1
    (receivePreReturnStack? st endpointObjId replier).2.1
    (receivePreReturnStack? st endpointObjId replier).2.2
    -- **WS-RM (`v0.35.6`)**: and the frame above the answered caller's reply
    -- object, which this arm's reply leg splices out -- the same resolver the
    -- `.reply` arm uses, because it is the same transition.
    (answeredReplyFrameAbove? st target)
    -- **WS-HP HP3.1**: and the frame **below** it, which the removal's splice
    -- re-links upward in the same step -- again the same resolver the `.reply`
    -- arm reads, since this arm's reply leg *is* that transition.
    (answeredReplyFrameBelow? st target)
    -- **WS-HP HP10.6**: and the origin the reply leg's bottom-of-stack pop
    -- redirects to -- the same resolver the `.reply` arm reads, for the same
    -- write, since this arm's reply leg *is* that transition.  Live at depth 1
    -- and merged there; a distinct key on the out-of-order removal, for the
    -- reason `lockSet_endpointReplyOnCore` records.
    (((answeredFrameHeadContext? st target).map (·.1)).bind
      (donationOriginRecipient? st))


/-- **WS-RR RR7.11: the concrete lock-set a cross-core `.receive` acquires.**

The one receive-shaped arm that had no resolved footprint.  `.call`, `.send`,
`.reply`, `.replyRecv`, `.notificationSignal` and `.notificationWait` all had
one; `.receive` was declared only in the argument-taking
`lockSet_endpointReceive`, so nothing named the values a live receive resolves
them to and the declaration could not be handed to a bracket.

Every state-dependent member is read from the pre-state through the expression
the transition itself branches on, which is the discipline RR7.8 established for
the caps destination:

* `senderTid` — `receiveRendezvousSender?`, the endpoint's send-queue head, the
  thread `endpointReceiveDualOnCore` dequeues and writes;
* `installsCaps` — `receiveInstallsCaps`, which is *literally* the condition
  `endpointReceiveDualWithCapsOnCore` tests before it unwraps, so the receiver's
  own CSpace root is declared `.write` exactly when `ipcTransferSingleCap` writes
  it, and (RR7.11) the state-level lock is declared exactly when that install
  writes the CDT.

`replyId` stays an argument: it is the *server-supplied* Reply object, addressed
by `RecvArgs.replyCPtr` in the caller's own message registers and resolved
against the caller's CSpace by `resolveRecvReplyId`.  It is a decoded operand,
not a fact about the endpoint, so reading it from `st` here would be inventing a
second resolution beside the dispatcher's. -/
def lockSet_endpointReceiveOnCore (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (replyId : Option SeLe4n.ReplyId := none) : LockSet :=
  lockSet_endpointReceive receiver cnodeRootObjId endpointId
    (receiveRendezvousSender? st endpointId)
    replyId
    (receiveInstallsCaps st endpointId)
    -- **WS-OD OD3.6**: the SchedContext the rendezvous donates, resolved from
    -- the same pre-state and through the same `receiveRendezvousSender?` the two
    -- members above read.
    (receiveRendezvousDonatedSc? st endpointId)
    -- **WS-OD OD3.12**: and the queue-structure neighbour, through the same
    -- resolver again.
    (receiveSideQueueStructureNeighbor? st endpointId)
    -- **WS-OD (`v0.35.4`)**: the old head the rendezvous donation's push
    -- rewrites, and the five objects of the receiver's own pre-receive return
    -- -- each through the resolver it is derived from.
    ((receiveRendezvousDonatedSc? st endpointId).bind (replyStackHead? st))
    ((receivePreReturn? st endpointId receiver).map (·.1))
    ((receivePreReturn? st endpointId receiver).map (·.2))
    (receivePreReturnStack? st endpointId receiver).1
    (receivePreReturnStack? st endpointId receiver).2.1
    (receivePreReturnStack? st endpointId receiver).2.2

-- ============================================================================
-- §3  Path reduction lemmas (full characterisation of each control path)
-- ============================================================================

/-- WS-SM SM6.C.1: full reduction of the **reply** (success) path for an
**unlinked** caller (`tcb.replyObject = none` — the folded PR #827 #3 consume is
a no-op) — the caller `target` is in `blockedOnReply` state recording an
authorised replier (`some expected`).  Authority flows from holding the reply cap
(resolved by the dispatch), so the delivery is independent of `replier` (PR #822
review 6J-lYm).  The post-state delivers the reply message + `.ready` to the
caller and wakes it cross-core; the surfaced SGI is exactly the caller wake's.
For a caller carrying a forward reply link see the companion
`endpointReplyOnCore_reply_eq_linked`. -/
theorem endpointReplyOnCore_reply_eq
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hRO : tcb.replyObject = none) :
    endpointReplyOnCore replier target msg executingCore st
      = ((wakeThread st' target executingCore).1, .ok (wakeThread st' target executingCore).2) := by
  unfold endpointReplyOnCore
  rw [if_neg hSz1, if_neg hSz2]
  simp only [hLk, hIpc]
  simp only [hStore]
  simp only [hRO]

/-- WS-SM SM6.D (PR #827 review #3 fold): full reduction of the **reply** (success)
path for a **linked** caller (`tcb.replyObject = some rid`).  A delivered reply now
consumes the answered caller↔Reply link **atomically** with the delivery
(single-use, seL4-MCS): after the store + cross-core wake, the folded
`removeCallerReplyFrame target rid` takes the answered frame off its reply stack
and clears `reply.caller` and the woken caller's `replyObject`.  Both legs are
total (`removeCallerReplyFrame_isOk`), so the transition
still succeeds and the surfaced SGI is exactly the caller wake's — the post-state
is the consume's output on the wake state.  (Formerly the consume was a separate
dispatch-layer step; folding it in gives a direct below-API caller full single-use
reply semantics.) -/
theorem endpointReplyOnCore_reply_eq_linked
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hRO : tcb.replyObject = some rid) :
    ∃ st'', removeCallerReplyFrame target rid
        (wakeThread st' target executingCore).1 = .ok ((), st'')
      ∧ endpointReplyOnCore replier target msg executingCore st
          = (st'', .ok (wakeThread st' target executingCore).2) := by
  obtain ⟨st'', hCons⟩ := removeCallerReplyFrame_isOk
    (wakeThread st' target executingCore).1 target rid
  refine ⟨st'', hCons, ?_⟩
  unfold endpointReplyOnCore
  rw [if_neg hSz1, if_neg hSz2]
  simp only [hLk, hIpc]
  simp only [hStore]
  simp only [hRO, hCons]

/-- WS-SM SM6.C.1 (branch-independent `.2` reduction): whatever the caller's
forward reply link, a successful reply surfaces exactly the caller wake's SGI —
the folded consume (PR #827 #3) is total and scheduler-invisible, so it cannot
disturb the result component.  The uniform driver behind the §4 SGI-emission and
§9 per-core-consistency conclusions. -/
theorem endpointReplyOnCore_reply_snd_eq
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st') :
    (endpointReplyOnCore replier target msg executingCore st).2
      = .ok (wakeThread st' target executingCore).2 := by
  cases hRO : tcb.replyObject with
  | none =>
      rw [endpointReplyOnCore_reply_eq replier target msg executingCore st st' tcb ep expected
            hSz1 hSz2 hLk hIpc hStore hRO]
  | some rid =>
      obtain ⟨st'', _, hEq⟩ := endpointReplyOnCore_reply_eq_linked replier target msg
        executingCore st st' tcb ep expected rid hSz1 hSz2 hLk hIpc hStore hRO
      rw [hEq]

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

/-- WS-SM SM6.C (PR #822 review 6J-lYm): a reply whose `replier` does **not** match
the caller's recorded `expected` server — a holder of a **copied/minted (delegated)
reply cap** — now **succeeds** (delivers + wakes), exactly like the original server.
Authority is the reply *capability* (resolved by the dispatch to `reply.caller =
target`), not the fixed recorded replier; seL4-MCS reply caps are delegatable.  The
confused-deputy protection is the cap (only a holder reaches this primitive); replay
is the `.blockedOnReply` state barrier (a consumed reply leaves the caller `.ready`).
Subsumed by `endpointReplyOnCore_reply_eq`, which is now replier-independent. -/
theorem endpointReplyOnCore_delegated_replier_eq
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (_hDelegated : (replier == expected) = false)
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hRO : tcb.replyObject = none) :
    endpointReplyOnCore replier target msg executingCore st
      = ((wakeThread st' target executingCore).1, .ok (wakeThread st' target executingCore).2) :=
  endpointReplyOnCore_reply_eq replier target msg executingCore st st' tcb ep expected
    hSz1 hSz2 hLk hIpc hStore hRO

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
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hTcb' : st'.getTcb? target = some targetTcb')
    (hRemote : determineTargetCore st' target ≠ executingCore) :
    (endpointReplyOnCore replier target msg executingCore st).2
      = .ok (some (determineTargetCore st' target, SgiKind.reschedule)) := by
  rw [endpointReplyOnCore_reply_snd_eq replier target msg executingCore st st' tcb ep expected
        hSz1 hSz2 hLk hIpc hStore]
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
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hLocal : determineTargetCore st' target = executingCore) :
    (endpointReplyOnCore replier target msg executingCore st).2 = .ok none := by
  rw [endpointReplyOnCore_reply_snd_eq replier target msg executingCore st st' tcb ep expected
        hSz1 hSz2 hLk hIpc hStore]
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
    (donatedSc? : Option SeLe4n.SchedContextId) (donatedOwner? : Option SeLe4n.ThreadId)
    -- **WS-OD OD3.7**: stated at FULL arity.  It sat at `replyId`'s default, so
    -- the consistency claim covered a shape the live `.reply` dispatch never
    -- declares (`lockSet_endpointReplyOnCore` resolves that optional to `some`)
    -- — the RR7.18 defect its own `.replyRecv` sibling below already refuses in
    -- as many words.  The two below-head reads join it at the same time.
    (replyId? : Option SeLe4n.ReplyId)
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    -- **WS-OD (`v0.35.4`)**: and at the head arity.
    (donatedHead? : Option SeLe4n.ReplyId)
    -- **WS-RM (`v0.35.6`)**: and at the frame-above arity — the member the
    -- removal's splice writes.
    (answeredFrameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: and at the frame-below arity -- the second member the
    -- removal's splice writes.
    (answeredFrameBelow? : Option SeLe4n.ReplyId)
    -- **WS-HP HP10.6**: and at the origin-recipient arity.
    (originRecipient? : Option SeLe4n.ThreadId) :
    (∀ p ∈ (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?
              replyId? belowHeadReply? outerCaller? donatedHead?
              answeredFrameAbove? answeredFrameBelow? originRecipient?).pairs,
        p.fst.kind ∈ permittedKinds .reply) ∧
    ((lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?
        replyId? belowHeadReply? outerCaller? donatedHead? answeredFrameAbove? answeredFrameBelow? originRecipient?).pairs.map
        (·.fst)).Nodup :=
  ⟨lockSet_consistent_reply replier cnRoot target donatedSc? donatedOwner?
      replyId? belowHeadReply? outerCaller? donatedHead? answeredFrameAbove? answeredFrameBelow? originRecipient?,
   (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?
      replyId? belowHeadReply? outerCaller? donatedHead?
      answeredFrameAbove? answeredFrameBelow? originRecipient?).hUniqueKeys⟩

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
  exact lockSet_consistent_reply _ cnodeRootObjId target _ _ _ _ _ _ _ _ _

/-- WS-SM SM6.C.5 (`endpointReplyRecv_lockSet_correct`): the combined `replyRecv`
lock-set — the reply footprint extended with the receive-leg endpoint write and
the optional new sender's TCB write — is **hierarchically correct**: every
declared lock has a kind in `permittedKinds .replyRecv`, and its keys are
duplicate-free. -/
theorem endpointReplyRecv_lockSet_correct
    (replier : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (newSender? : Option SeLe4n.ThreadId)
    (donatedSc? : Option SeLe4n.SchedContextId) (donatedOwner? : Option SeLe4n.ThreadId)
    -- WS-OD OD3.5: stated over the two members OD3.5 added as well, not at their
    -- absence — a consistency claim checked at one argument value while the
    -- resolved footprint supplies another is the shape RR7.18 exists to refuse.
    (replyId? : Option SeLe4n.ReplyId) (installsCaps : Bool)
    (donationServer? : Option SeLe4n.ThreadId)
    (redonatedSc? : Option SeLe4n.SchedContextId)
    -- WS-OD OD3.7: and over the two below-head reads, for the same reason.
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    -- **WS-OD OD3.13**: at the queue-structure-neighbour arity.
    (queueNeighbour? : Option SeLe4n.ThreadId)
    -- **WS-OD (`v0.35.4`)**: and at the old-head and head arity.
    (redonationOldHead? donatedHead? : Option SeLe4n.ReplyId)
    -- **PR #894 review**: and over the invoking receiver's own pre-receive
    -- return, for the same reason again.
    (preReturnSc? : Option SeLe4n.SchedContextId) (preReturnOwner? : Option SeLe4n.ThreadId)
    (preReturnHead? preReturnBelowHead? : Option SeLe4n.ReplyId)
    (preReturnOuterCaller? : Option SeLe4n.ThreadId)
    -- **WS-RM (`v0.35.6`)**: and over the frame above the answered caller's
    -- reply object, for the same reason once more.
    (answeredFrameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: and at the frame-below arity -- the second member the
    -- removal's splice writes.
    (answeredFrameBelow? : Option SeLe4n.ReplyId)
    -- **WS-HP HP10.6**: and at the origin-recipient arity.
    (originRecipient? : Option SeLe4n.ThreadId) :
    (∀ p ∈ (lockSet_replyRecv replier cnRoot target epId newSender? donatedSc? donatedOwner?
              replyId? installsCaps donationServer? redonatedSc?
              belowHeadReply? outerCaller? queueNeighbour? redonationOldHead?
              donatedHead? preReturnSc? preReturnOwner? preReturnHead? preReturnBelowHead?
              preReturnOuterCaller? answeredFrameAbove? answeredFrameBelow? originRecipient?).pairs,
        p.fst.kind ∈ permittedKinds .replyRecv) ∧
    ((lockSet_replyRecv replier cnRoot target epId newSender? donatedSc? donatedOwner?
        replyId? installsCaps donationServer? redonatedSc?
        belowHeadReply? outerCaller? queueNeighbour? redonationOldHead?
        donatedHead? preReturnSc? preReturnOwner? preReturnHead? preReturnBelowHead?
        preReturnOuterCaller? answeredFrameAbove? answeredFrameBelow? originRecipient?).pairs.map
        (·.fst)).Nodup :=
  ⟨lockSet_consistent_replyRecv replier cnRoot target epId newSender? donatedSc? donatedOwner?
      replyId? installsCaps donationServer? redonatedSc? belowHeadReply? outerCaller?
      queueNeighbour? redonationOldHead? donatedHead? preReturnSc? preReturnOwner?
      preReturnHead? preReturnBelowHead? preReturnOuterCaller? answeredFrameAbove? answeredFrameBelow? originRecipient?,
   (lockSet_replyRecv replier cnRoot target epId newSender? donatedSc? donatedOwner?
      replyId? installsCaps donationServer? redonatedSc?
      belowHeadReply? outerCaller? queueNeighbour? redonationOldHead?
      donatedHead? preReturnSc? preReturnOwner? preReturnHead? preReturnBelowHead?
      preReturnOuterCaller? answeredFrameAbove? answeredFrameBelow? originRecipient?).hUniqueKeys⟩

/-- **WS-OD OD3.13**: the queue-structure neighbour of the **receive leg** is a
declared write member of the resolved `.replyRecv` footprint.

The arm the ceiling was raised for.  `.replyRecv`'s receive leg *is*
`endpointReceiveDualOnCore`, so it pops the send queue or enqueues on the
receive queue exactly as `.receive` does, and writes the same one neighbour TCB
-- but the arm was already at 13 of 13, so declaring it cost
`maxLockSetSize` a raise to 14 and `admissibleCriticalSection` two microseconds
on the 1 ms tick.  Read that cost as the price of the alternative: a footprint
that omits a written object is *false*, and this project rates that worse than a
wide one. -/
theorem lockSet_endpointReplyRecvOnCore_covers_queueNeighbour
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId) (q : SeLe4n.ThreadId)
    (hq : receiveSideQueueStructureNeighbor? st endpointObjId = some q) :
    (tcbLock q, AccessMode.write)
      ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
           endpointObjId).pairs := by
  unfold lockSet_endpointReplyRecvOnCore lockSet_replyRecv
  rw [hq]
  -- WS-RM (`v0.35.6`) / WS-HP HP3.1 / WS-HP HP10.6: three extensions sit above
  -- it — the frame above the cut, the frame below it that the splice
  -- re-links, and the origin a bottom-of-stack pop redirects to.
  iterate 3 apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- WS-SM SM6.C.5: the **state-resolved** replyRecv lock-set is hierarchically
correct — the form the runtime acquisition consumes. -/
theorem lockSet_endpointReplyRecvOnCore_correct
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId) :
    ∀ p ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target endpointObjId).pairs,
      p.fst.kind ∈ permittedKinds .replyRecv := by
  unfold lockSet_endpointReplyRecvOnCore
  exact lockSet_consistent_replyRecv replier cnodeRootObjId target endpointObjId
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

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
TCB" risk row, mitigated).  On a linked caller the folded consume (PR #827 #3)
additionally clears the caller's `replyObject`, but preserves its `ipcState` /
`pendingMessage` (`removeCallerReplyFrame_tcb_backward`), so the delivered payload
survives the atomic link teardown. -/
theorem endpointReplyOnCore_perCore_delivery
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
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
  have hWake : (wakeThread st' target executingCore).1.getTcb? target
      = some { tcb with ipcState := .ready, pendingMessage := some msg } := by
    rw [wakeThread_getTcb?_eq_of_ready st' target executingCore
          { tcb with ipcState := .ready, pendingMessage := some msg } hSelf rfl hInv' target]
    exact hSelf
  cases hRO : tcb.replyObject with
  | none =>
      rw [endpointReplyOnCore_reply_eq replier target msg executingCore st st' tcb ep expected
            hSz1 hSz2 hLk hIpc hStore hRO]
      exact ⟨{ tcb with ipcState := .ready, pendingMessage := some msg }, hWake, rfl, rfl⟩
  | some rid =>
      obtain ⟨st'', hCons, hEq⟩ := endpointReplyOnCore_reply_eq_linked replier target msg
        executingCore st st' tcb ep expected rid hSz1 hSz2 hLk hIpc hStore hRO
      rw [hEq]
      have hInvW : (wakeThread st' target executingCore).1.objects.invExt :=
        wakeThread_preserves_objects_invExt st' target executingCore hInv'
      have hObjW : (wakeThread st' target executingCore).1.objects[target.toObjId]?
          = some (.tcb { tcb with ipcState := .ready, pendingMessage := some msg }) :=
        (SystemState.getTcb?_eq_some_iff _ target _).mp hWake
      obtain ⟨tx, hTx, hIpcEq, hMsgEq, _⟩ :=
        removeCallerReplyFrame_tcb_backward
          (wakeThread st' target executingCore).1 st'' target rid hInvW hCons
          target.toObjId { tcb with ipcState := .ready, pendingMessage := some msg } hObjW
      exact ⟨tx, (SystemState.getTcb?_eq_some_iff st'' target tx).mpr hTx,
        by rw [hIpcEq], by rw [hMsgEq]⟩

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
    (donatedSc? : Option SeLe4n.SchedContextId) (donatedOwner? : Option SeLe4n.ThreadId)
    -- **WS-RR RR7.11**: stated over the SM6.D reply optional too.  Left at its
    -- default this covered only a reply-less footprint, while
    -- `lockSet_endpointReplyOnCore` resolves that optional from the state — so
    -- the one shape a live `.reply` actually declares was outside the theorem.
    (replyId : Option SeLe4n.ReplyId)
    -- WS-OD OD3.7: and over the two below-head reads, for the same reason.
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    -- WS-OD (`v0.35.4`): and over the head the pop clears.
    (donatedHead? : Option SeLe4n.ReplyId)
    -- **WS-RM (`v0.35.6`)**: and at the frame-above arity.
    (answeredFrameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: and at the frame-below arity -- the second member the
    -- removal's splice writes.
    (answeredFrameBelow? : Option SeLe4n.ReplyId)
    -- **WS-HP HP10.6**: and at the origin-recipient arity.
    (originRecipient? : Option SeLe4n.ThreadId) :
    (tcbLock target, AccessMode.write)
      ∈ (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner? replyId
          belowHeadReply? outerCaller? donatedHead? answeredFrameAbove? answeredFrameBelow? originRecipient?).pairs := by
  unfold lockSet_endpointReply lockSetOfList
  simp only [List.foldl]
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower, so a member added to this footprint cannot leave a nesting depth
  -- silently wrong (WS-OD OD3.7).
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_self _ _

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
    (rid : SeLe4n.ReplyId)
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    (donatedHead? : Option SeLe4n.ReplyId)
    -- **WS-RM (`v0.35.6`)**: and at the frame-above arity.
    (answeredFrameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: and at the frame-below arity -- the second member the
    -- removal's splice writes.
    (answeredFrameBelow? : Option SeLe4n.ReplyId)
    -- **WS-HP HP10.6**: and at the origin-recipient arity.
    (originRecipient? : Option SeLe4n.ThreadId) :
    (replyLock rid, AccessMode.write)
      ∈ (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner? (some rid)
          belowHeadReply? outerCaller? donatedHead? answeredFrameAbove? answeredFrameBelow? originRecipient?).pairs := by
  unfold lockSet_endpointReply
  -- An EXACT count, not `repeat`: this member is introduced by an extension, so
  -- peeling one layer too far would discard the very lock being proved present.
  -- Seven layers sit above it — the origin a bottom-of-stack pop redirects to
  -- (WS-HP HP10.6), the frame below the answered reply (WS-HP HP3.1) and the frame
  -- above it (WS-RM `v0.35.6`), the returned context's head (WS-OD `v0.35.4`),
  -- WS-OD OD3.7's two below-head members and the state-level lock.
  iterate 7 apply mem_write_lockSetExtendOpt
  exact self_write_mem_insertOrMerge _ (replyLock rid)

/-- WS-SM SM6.D (PR #822 review 6J-NL9): the per-object reply **write** lock is a
declared member of the `.receive` lock-set footprint once the linked reply object
is resolved (`replyId := some rid`).  A `Call` rendezvous on the receive path links
a server-supplied Reply object to the just-dequeued caller (`linkCallerReply` writes
`reply.caller`), so that write must fall inside the 2PL set — closing the race where
two cores with copied caps to the same Reply both observe it free and race
`reply.caller`/`tcb.replyObject`. -/
theorem lockSet_endpointReceive_reply_write_mem
    (callerTid : SeLe4n.ThreadId) (cnRoot endpointObjId : SeLe4n.ObjId)
    (senderTid : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (installsCaps : Bool) (donatedScId : Option SeLe4n.SchedContextId)
    -- **WS-OD OD3.12**: at the queue-structure-neighbour arity.
    (queueNeighbour : Option SeLe4n.ThreadId)
    -- **WS-OD (`v0.35.4`)**: and at the old-head and pre-receive-return arity.
    (donationOldHeadReplyId : Option SeLe4n.ReplyId)
    (preReturnScId : Option SeLe4n.SchedContextId)
    (preReturnOwnerTid : Option SeLe4n.ThreadId)
    (preReturnHeadReplyId preReturnBelowHeadReplyId : Option SeLe4n.ReplyId)
    (preReturnOuterCallerTid : Option SeLe4n.ThreadId) :
    (replyLock rid, AccessMode.write)
      ∈ (lockSet_endpointReceive callerTid cnRoot endpointObjId senderTid (some rid)
          installsCaps donatedScId queueNeighbour donationOldHeadReplyId preReturnScId
          preReturnOwnerTid preReturnHeadReplyId preReturnBelowHeadReplyId
          preReturnOuterCallerTid).pairs := by
  unfold lockSet_endpointReceive
  -- WS-OD OD3.6: one extension deeper -- the donated SchedContext sits between
  -- this member and the state-level lock.  WS-OD OD3.12: and one deeper again.
  -- WS-OD (`v0.35.4`): and six deeper still -- the push's old head and the five
  -- pre-receive-return members -- nine layers in all.
  iterate 9 apply mem_write_lockSetExtendOpt
  exact self_write_mem_insertOrMerge _ (replyLock rid)

/-- **WS-SM SM3.B (PR #873 round 8): a capability-installing receive holds the
receiver's CSpace root in WRITE mode.**

The checkable form of the round-8 finding.  Both receive-shaped arms reach
`ipcTransferSingleCap`, which mutates the receiver's root CNode through
`cspaceInsertSlot`, while the footprint declared that same CNode `.read` — so
once SM3.C.9 consumes these footprints a concurrent CSpace writer could share the
alleged read lock and one update would be lost.

Stated at `installsCaps := true`, which is the shape
`receiveInstallsCaps` resolves to exactly when the dequeued sender parked a
caps-bearing message.  At `false` the member stays `.read`, which is why this is
a mode on the existing member rather than a new one: the size and the acquisition
order are untouched. -/
theorem lockSet_endpointReceive_capsInstall_write_mem
    (callerTid : SeLe4n.ThreadId) (cnRoot endpointObjId : SeLe4n.ObjId)
    (senderTid : Option SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (donatedScId : Option SeLe4n.SchedContextId)
    -- **WS-OD OD3.12**: at the queue-structure-neighbour arity.
    (queueNeighbour : Option SeLe4n.ThreadId)
    -- **WS-OD (`v0.35.4`)**: and at the old-head and pre-receive-return arity.
    (donationOldHeadReplyId : Option SeLe4n.ReplyId)
    (preReturnScId : Option SeLe4n.SchedContextId)
    (preReturnOwnerTid : Option SeLe4n.ThreadId)
    (preReturnHeadReplyId preReturnBelowHeadReplyId : Option SeLe4n.ReplyId)
    (preReturnOuterCallerTid : Option SeLe4n.ThreadId) :
    (cnodeLock cnRoot, AccessMode.write)
      ∈ (lockSet_endpointReceive callerTid cnRoot endpointObjId senderTid replyId
          (installsCaps := true) donatedScId queueNeighbour donationOldHeadReplyId
          preReturnScId preReturnOwnerTid preReturnHeadReplyId preReturnBelowHeadReplyId
          preReturnOuterCallerTid).pairs := by
  unfold lockSet_endpointReceive lockSetOfList
  simp only [List.foldl, if_true, Bool.true_or]
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower (WS-OD `v0.35.4` took the tower from five to eleven), so a member
  -- added to this footprint cannot leave a nesting depth silently wrong.
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
    (LockSet.mem_insertOrMerge_write_self _ _)

/-- **WS-SM SM3.B (PR #873 round 8): and so does `.replyRecv`'s receive leg** —
the same transition, so the same write, so the same declared mode. -/
theorem lockSet_replyRecv_capsInstall_write_mem
    (callerTid : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (endpointObjId : SeLe4n.ObjId) (newSenderTid : Option SeLe4n.ThreadId)
    (donatedScId : Option SeLe4n.SchedContextId)
    (donatedOwnerTid : Option SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (donationServer? : Option SeLe4n.ThreadId)
    (redonatedSc? : Option SeLe4n.SchedContextId)
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    -- **WS-OD OD3.13**: at the queue-structure-neighbour arity.
    (queueNeighbour? : Option SeLe4n.ThreadId)
    -- **WS-OD (`v0.35.4`)**: and at the old-head and head arity.
    (redonationOldHead? donatedHead? : Option SeLe4n.ReplyId)
    -- **PR #894 review**: and at the invoker's pre-receive-return arity.
    (preReturnSc? : Option SeLe4n.SchedContextId)
    (preReturnOwner? : Option SeLe4n.ThreadId)
    (preReturnHead? preReturnBelowHead? : Option SeLe4n.ReplyId)
    (preReturnOuterCaller? : Option SeLe4n.ThreadId)
    -- **WS-RM (`v0.35.6`)**: and at the frame-above arity.
    (answeredFrameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: and at the frame-below arity -- the second member the
    -- removal's splice writes.
    (answeredFrameBelow? : Option SeLe4n.ReplyId)
    -- **WS-HP HP10.6**: and at the origin-recipient arity.
    (originRecipient? : Option SeLe4n.ThreadId) :
    (cnodeLock cnRoot, AccessMode.write)
      ∈ (lockSet_replyRecv callerTid cnRoot target endpointObjId newSenderTid
          donatedScId donatedOwnerTid replyId (installsCaps := true)
          donationServer? redonatedSc? belowHeadReply? outerCaller?
          queueNeighbour? redonationOldHead? donatedHead?
          preReturnSc? preReturnOwner? preReturnHead? preReturnBelowHead?
          preReturnOuterCaller? answeredFrameAbove? answeredFrameBelow? originRecipient?).pairs := by
  unfold lockSet_replyRecv lockSetOfList
  simp only [List.foldl, if_true]
  -- The optional extensions are peeled by count rather than by a hand-nested
  -- tower, so a member added to this footprint cannot leave a nesting depth
  -- silently wrong (WS-OD OD3.7).
  repeat apply mem_write_lockSetExtendOpt
  exact LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
    (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ _
      (LockSet.mem_insertOrMerge_write_self _ _))

/-- **WS-RR RR7.11**: the resolved receive footprint declares the state-level
write its capability install needs, on exactly the states where it installs. -/
theorem lockSet_endpointReceiveOnCore_covers_cdt
    (st : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (replyId : Option SeLe4n.ReplyId)
    (hCaps : receiveInstallsCaps st endpointId = true) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).pairs := by
  unfold lockSet_endpointReceiveOnCore
  rw [hCaps]
  exact lockSet_endpointReceive_stateLevel_write_mem receiver cnodeRootObjId endpointId
    (receiveRendezvousSender? st endpointId) replyId
    (receiveRendezvousDonatedSc? st endpointId)
    (receiveSideQueueStructureNeighbor? st endpointId)
    _ _ _ _ _ _
/-- **WS-RR RR7.11**: and the receiver's own CSpace root in **write** mode, the
member `ipcTransferSingleCap`'s `cspaceInsertSlot` needs. -/
theorem lockSet_endpointReceiveOnCore_covers_capsDestination
    (st : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (replyId : Option SeLe4n.ReplyId)
    (hCaps : receiveInstallsCaps st endpointId = true) :
    (cnodeLock cnodeRootObjId, AccessMode.write)
      ∈ (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).pairs := by
  unfold lockSet_endpointReceiveOnCore
  rw [hCaps]
  exact lockSet_endpointReceive_capsInstall_write_mem receiver cnodeRootObjId endpointId
    (receiveRendezvousSender? st endpointId) replyId
    (receiveRendezvousDonatedSc? st endpointId)
    (receiveSideQueueStructureNeighbor? st endpointId)
    _ _ _ _ _ _

/-- **WS-OD OD3.12**: the queue-structure neighbour is a declared **write**
member of the resolved `.receive` footprint.

A `.receive` either pops the endpoint's send queue -- relinking the popped
sender's successor into the head -- or enqueues the receiver on the receive
queue, relinking that queue's old tail.  Exactly one TCB, and the footprint
named neither until this row, so a `.receive` on one core and a `.tcbSuspend`
of the affected neighbour on another had provably disjoint footprints while
both writing it. -/
theorem lockSet_endpointReceiveOnCore_covers_queueNeighbour
    (st : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (replyId : Option SeLe4n.ReplyId)
    (q : SeLe4n.ThreadId)
    (hq : receiveSideQueueStructureNeighbor? st endpointId = some q) :
    (tcbLock q, AccessMode.write)
      ∈ (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).pairs := by
  unfold lockSet_endpointReceiveOnCore lockSet_endpointReceive
  rw [hq]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-OD OD3.6: the resolved `.receive` footprint covers the rendezvous
donation.**

The two objects `donateSchedContext` writes: the donated context itself, and the
`SystemState.scThreadIndex` entry the hand-off maintains — an `RHTable` whose
insert may rehash, so no per-object lock decomposes it and `stateLevelLock` is
the declared subject.  Both are conditioned on the *resolver*, so the footprint
fires exactly when the transition's own guard does; before OD3.6 the arm
performed no donation and declared neither. -/
theorem lockSet_endpointReceiveOnCore_covers_donatedSc
    (st : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (replyId : Option SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId)
    (hSc : receiveRendezvousDonatedSc? st endpointId = some scId) :
    (schedContextLock scId, AccessMode.write)
      ∈ (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).pairs := by
  unfold lockSet_endpointReceiveOnCore
  rw [hSc]
  exact lockSet_endpointReceive_donated_sc_write_mem receiver cnodeRootObjId endpointId
    (receiveRendezvousSender? st endpointId) replyId (receiveInstallsCaps st endpointId) scId
    (receiveSideQueueStructureNeighbor? st endpointId)
    _ _ _ _ _ _

/-- WS-OD OD3.6: and the state-level lock, on the donating path — which is the
passive-server steady state and installs no capability, so the CDT-conditioned
statement beside this one does not cover it. -/
theorem lockSet_endpointReceiveOnCore_covers_donationIndex
    (st : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (replyId : Option SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId)
    (hSc : receiveRendezvousDonatedSc? st endpointId = some scId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).pairs := by
  unfold lockSet_endpointReceiveOnCore
  rw [hSc]
  exact lockSet_endpointReceive_donation_stateLevel_write_mem receiver cnodeRootObjId endpointId
    (receiveRendezvousSender? st endpointId) replyId (receiveInstallsCaps st endpointId) scId
    (receiveSideQueueStructureNeighbor? st endpointId)
    _ _ _ _ _ _

/-- **WS-RR RR7.11**: and `.replyRecv`'s resolved footprint declares the same
state-level write, since its receive leg is the same transition. -/
theorem lockSet_endpointReplyRecvOnCore_covers_cdt
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId)
    (hCaps : receiveInstallsCaps st endpointObjId = true) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
          endpointObjId).pairs := by
  unfold lockSet_endpointReplyRecvOnCore
  rw [hCaps]
  exact lockSet_replyRecv_stateLevel_write_mem replier cnodeRootObjId target endpointObjId
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **WS-OD (`v0.35.4`)**: the old head the rendezvous donation's push rewrites
is a declared write of the resolved `.receive` footprint. -/
theorem lockSet_endpointReceiveOnCore_covers_donationOldHead
    (st : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (replyId : Option SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId) (oldHead : SeLe4n.ReplyId)
    (hSc : receiveRendezvousDonatedSc? st endpointId = some scId)
    (hOld : replyStackHead? st scId = some oldHead) :
    (replyLock oldHead, AccessMode.write)
      ∈ (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).pairs := by
  unfold lockSet_endpointReceiveOnCore
  rw [hSc]
  have h2 : Option.bind (some scId) (replyStackHead? st) = some oldHead := hOld
  rw [h2]
  exact lockSet_endpointReceive_donationOldHead_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **WS-OD (`v0.35.4`)**: the pre-receive return's writes -- the context the
blocking receiver hands back, the previous owner's TCB, the head cleared and
the frame below re-headed -- are declared writes of the resolved `.receive`
footprint, together with the state-level lock its `scThreadIndex` maintenance
takes.  Each is conditioned on the resolver that names it, so the footprint
carries the member exactly when the arm blocks holding a donation. -/
theorem lockSet_endpointReceiveOnCore_covers_preReturn
    (st : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (replyId : Option SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (hRet : receivePreReturn? st endpointId receiver = some (scId, owner)) :
    (schedContextLock scId, AccessMode.write)
        ∈ (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).pairs ∧
    (tcbLock owner, AccessMode.write)
        ∈ (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).pairs ∧
    (∀ head, replyStackHead? st scId = some head →
      (replyLock head, AccessMode.write)
        ∈ (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).pairs) ∧
    (∀ below, (replyStackBelowHead? st scId).1 = some below →
      (replyLock below, AccessMode.write)
        ∈ (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).pairs) ∧
    (stateLevelLock, AccessMode.write)
        ∈ (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).pairs := by
  unfold lockSet_endpointReceiveOnCore receivePreReturnStack?
  rw [hRet]
  simp only [Option.map_some]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact lockSet_endpointReceive_preReturn_sc_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact lockSet_endpointReceive_preReturn_owner_tcb_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · intro head hHead
    rw [hHead]
    exact lockSet_endpointReceive_preReturn_head_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · intro below hBelow
    rw [hBelow]
    exact lockSet_endpointReceive_preReturn_belowHead_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · unfold lockSet_endpointReceive
    simp only [Option.isSome_some, Bool.or_true, if_true]
    exact mem_write_lockSetExtendOpt _ _ _ (LockSet.mem_insertOrMerge_write_self _ _)

/-- **WS-HP HP6.2 (`v0.35.44`): the donation pop's SchedContext and the TCB it
unbinds are declared writes of the resolved `.reply` footprint — with no
hypothesis.**

This replaces HP4.4's `lockSet_endpointReplyOnCore_covers_headDrivenPop`, which
had to bridge two resolvers: the footprint read the *recorded server's* binding
while the pop read the answered frame, so coverage held only under
`donationOwnerValid` and a stated coherence fact (`answeredHeadContextIsServerDonation`,
deleted at HP7), and it reached the holder's TCB by proving the holder **is** the
recorded server — the very equation the splice breaks.  With the footprint repointed onto
`answeredFrameHeadContext?`, the members *are* the trigger's answer and the
relation is definitional.

Both members are stated on their own account: the SchedContext through
`lockSet_endpointReply_donatedSc_write_mem`, and the holder through
`lockSet_endpointReply_donatedHolder_tcb_write_mem`, which HP6.2 had to add —
the second donation member had no write-membership lemma on either footprint,
which is why the stand-in had to route through `callerTid`'s.

The *recipient* needs no member of its own: the head-driven pop hands the context
to the answered caller, which is `target`, a non-optional argument of this
footprint. -/
theorem lockSet_endpointReplyOnCore_covers_donationPop
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hHead : answeredFrameHeadContext? st target = some (scId, holder)) :
    (schedContextLock scId, AccessMode.write)
      ∈ (lockSet_endpointReplyOnCore st replier cnodeRootObjId target).pairs ∧
    (tcbLock holder, AccessMode.write)
      ∈ (lockSet_endpointReplyOnCore st replier cnodeRootObjId target).pairs := by
  unfold lockSet_endpointReplyOnCore
  rw [hHead]
  simp only [Option.map_some]
  exact ⟨lockSet_endpointReply_donatedSc_write_mem _ _ _ _ _ _ _ _ _ _ _ _,
    lockSet_endpointReply_donatedHolder_tcb_write_mem _ _ _ _ _ _ _ _ _ _ _ _⟩

set_option maxHeartbeats 1000000 in
/-- **WS-HP HP6.2**: and `.replyRecv`'s, which is the same pop because its reply
leg is the `.reply` arm's transition.  Stated because the tables are symmetric:
the stand-in this replaces had no `.replyRecv` twin at all, so nothing said the
hottest IPC arm's pop wrote under declared locks. -/
theorem lockSet_endpointReplyRecvOnCore_covers_donationPop
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hHead : answeredFrameHeadContext? st target = some (scId, holder)) :
    (schedContextLock scId, AccessMode.write)
      ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
           endpointObjId).pairs ∧
    (tcbLock holder, AccessMode.write)
      ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
           endpointObjId).pairs := by
  unfold lockSet_endpointReplyRecvOnCore
  rw [hHead]
  simp only [Option.map_some]
  refine ⟨?_, ?_⟩
  · exact lockSet_replyRecv_donatedSc_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _
  · exact lockSet_replyRecv_donatedHolder_tcb_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _

/-- **WS-OD (`v0.35.4`)**: the reply-stack pop's two Reply writes -- the head it
clears and the frame below it re-heads -- are declared writes of the resolved
`.reply` footprint, on the context the arm pops.

**WS-HP HP6.2 (`v0.35.44`)**: keyed on the pop's own trigger.  It read the
recorded server's binding, which is not what the pop reads, so on a state where
the two disagree this said nothing about the objects the transition writes. -/
theorem lockSet_endpointReplyOnCore_covers_pop
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hDon : answeredFrameHeadContext? st target = some (scId, holder)) :
    (∀ head, replyStackHead? st scId = some head →
      (replyLock head, AccessMode.write)
        ∈ (lockSet_endpointReplyOnCore st replier cnodeRootObjId target).pairs) ∧
    (∀ below, (replyStackBelowHead? st scId).1 = some below →
      (replyLock below, AccessMode.write)
        ∈ (lockSet_endpointReplyOnCore st replier cnodeRootObjId target).pairs) := by
  unfold lockSet_endpointReplyOnCore
  rw [hDon]
  simp only [Option.map_some]
  constructor
  · intro head hHead
    have h2 : Option.bind (some scId) (replyStackHead? st) = some head := hHead
    rw [h2]
    exact lockSet_endpointReply_donatedHead_write_mem _ _ _ _ _ _ _ _ _ _ _ _
  · intro below hBelow
    rw [hBelow]
    exact lockSet_endpointReply_belowHead_write_mem _ _ _ _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 1000000 in
/-- **WS-OD (`v0.35.4`)**: the old head the receive leg's re-donation push
rewrites is a declared write of the resolved `.replyRecv` footprint. -/
theorem lockSet_endpointReplyRecvOnCore_covers_redonationOldHead
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId)
    (scId : SeLe4n.SchedContextId) (oldHead : SeLe4n.ReplyId)
    (hSc : receiveRendezvousDonatedSc? st endpointObjId = some scId)
    (hOld : replyStackHead? st scId = some oldHead) :
    (replyLock oldHead, AccessMode.write)
      ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
           endpointObjId).pairs := by
  unfold lockSet_endpointReplyRecvOnCore
  rw [hSc]
  have h2 : Option.bind (some scId) (replyStackHead? st) = some oldHead := hOld
  rw [h2]
  exact lockSet_replyRecv_redonationOldHead_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _

set_option maxHeartbeats 1000000 in
/-- **WS-OD (`v0.35.4`)**: and the reply leg's pop -- the head it clears and the
frame below it re-heads -- on the context the arm pops.  **WS-HP HP6.2**: keyed
on the pop's own trigger, for the reason its `.reply` twin records. -/
theorem lockSet_endpointReplyRecvOnCore_covers_pop
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hDon : answeredFrameHeadContext? st target = some (scId, holder)) :
    (∀ head, replyStackHead? st scId = some head →
      (replyLock head, AccessMode.write)
        ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
             endpointObjId).pairs) ∧
    (∀ below, (replyStackBelowHead? st scId).1 = some below →
      (replyLock below, AccessMode.write)
        ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
             endpointObjId).pairs) := by
  unfold lockSet_endpointReplyRecvOnCore
  rw [hDon]
  simp only [Option.map_some]
  constructor
  · intro head hHead
    have h2 : Option.bind (some scId) (replyStackHead? st) = some head := hHead
    rw [h2]
    exact lockSet_replyRecv_donatedHead_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _
  · intro below hBelow
    rw [hBelow]
    exact lockSet_replyRecv_belowHead_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _

/-- **WS-RM (`v0.35.6`)**: the frame the reply leg's splice rewrites is a declared
write of the resolved `.reply` footprint.

The reply-path twin of `lockSet_cancelIpcBlockingOnCore_covers_splicedFrameAbove`,
which the cancellation path has carried since `v0.35.4`.  It is the relation the
Tier 3 anchor over this footprint's definition does not make: that anchor asks
that `answeredReplyFrameAbove? st target` *occur* in the definition, and a member
occurring is not a member being a declared write at the mode the splice needs.

Like every member of this family the resolution is on the pre-state, which is
what `runUnderDeclaredLockSet` re-resolves and refuses on change (WS-RR RR7.12);
the bracket, not the member, is where the two states are reconciled. -/
theorem lockSet_endpointReplyOnCore_covers_splicedFrameAbove
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (above : SeLe4n.ReplyId)
    (hAbove : answeredReplyFrameAbove? st target = some above) :
    (replyLock above, AccessMode.write)
      ∈ (lockSet_endpointReplyOnCore st replier cnodeRootObjId target).pairs := by
  unfold lockSet_endpointReplyOnCore
  rw [hAbove]
  exact lockSet_endpointReply_frameAbove_write_mem _ _ _ _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 1000000 in
/-- **WS-RM (`v0.35.6`)**: and `.replyRecv`'s, which is the same splice because
its reply leg is the `.reply` arm's transition. -/
theorem lockSet_endpointReplyRecvOnCore_covers_splicedFrameAbove
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId) (above : SeLe4n.ReplyId)
    (hAbove : answeredReplyFrameAbove? st target = some above) :
    (replyLock above, AccessMode.write)
      ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
           endpointObjId).pairs := by
  unfold lockSet_endpointReplyRecvOnCore
  rw [hAbove]
  exact lockSet_replyRecv_frameAbove_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _

/-- **WS-HP HP3.3**: and the frame the removal re-links *below* the cut is a
declared write of the resolved `.reply` footprint too — the second half of
`reply_remove`'s write set.

HP6 makes `spliceReplyFrameOutOrSelf` a splice, which patches the frame below
the cut to point past it (`next := .frame above`).  A footprint that names only
the frame above would then be **false** of the operation, which this project
rates worse than a wide one — so the member is declared here, one phase before
the code that writes it, which is the plan's own numbering rule (a transition
goes live only after the proofs that cover it).

The resolver is `answeredReplyFrameBelow?`, which asks
`answeredReplyFrameAbove?` first: a frame with nothing above it is not being
removed from the middle of anything, so it declares no below-member and the
*reachable* footprint does not widen.  That is why HP3.2 moved the
unconditional `.replyRecv` bound (19 → 20) and left the two reachable ones at
eighteen and seventeen. -/
theorem lockSet_endpointReplyOnCore_covers_splicedFrameBelow
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (below : SeLe4n.ReplyId)
    (hBelow : answeredReplyFrameBelow? st target = some below) :
    (replyLock below, AccessMode.write)
      ∈ (lockSet_endpointReplyOnCore st replier cnodeRootObjId target).pairs := by
  unfold lockSet_endpointReplyOnCore
  rw [hBelow]
  exact lockSet_endpointReply_frameBelow_write_mem _ _ _ _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 1000000 in
/-- **WS-HP HP3.3**: and `.replyRecv`'s, which is the same removal because its
reply leg is the `.reply` arm's transition. -/
theorem lockSet_endpointReplyRecvOnCore_covers_splicedFrameBelow
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId) (below : SeLe4n.ReplyId)
    (hBelow : answeredReplyFrameBelow? st target = some below) :
    (replyLock below, AccessMode.write)
      ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
           endpointObjId).pairs := by
  unfold lockSet_endpointReplyRecvOnCore
  rw [hBelow]
  exact lockSet_replyRecv_frameBelow_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _

/-- **WS-HP HP10.6: the origin a bottom-of-stack pop redirects the reservation to
is a declared write of the resolved `.reply` footprint.**

Declared one row before the arm that writes it, which is the plan's own numbering
rule — a footprint that omits a written object is *false*, so the member lands
first and the flip lands second.  The resolver is the expression HP10.7's arm
reads (`donationOriginRecipient?`), applied to the very context this arm pops, so
the footprint and the transition cannot disagree about which thread receives the
reservation.

**Inert at this version**, because nothing reads `SchedContext.donationOrigin`
yet: the member is `some` exactly where the pop is at the bottom of its stack and
the context records an acceptable origin, and the flip is what makes that
reachable answer load-bearing.

It costs the *reachable* footprint nothing.  The origin member is live only at the
bottom of a stack, where the two below-head members are both absent
(`replyStackBelowHead?_of_originRecipient`), so a reachable footprint trades two
members for one; what moved is `maxLockSetSize`, which bounds the union over all
argument values and is what `boundedWait_under_2pl` and the WCRT surface consume. -/
theorem lockSet_endpointReplyOnCore_covers_originRecipient
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (origin : SeLe4n.ThreadId)
    (hHead : answeredFrameHeadContext? st target = some (scId, holder))
    (hOrigin : donationOriginRecipient? st scId = some origin) :
    (tcbLock origin, AccessMode.write)
      ∈ (lockSet_endpointReplyOnCore st replier cnodeRootObjId target).pairs := by
  unfold lockSet_endpointReplyOnCore
  rw [hHead]
  simp only [Option.map_some, Option.bind_some, hOrigin]
  exact lockSet_endpointReply_originRecipient_write_mem _ _ _ _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 1000000 in
/-- **WS-HP HP10.6**: and `.replyRecv`'s, which is the same write because its
reply leg is the `.reply` arm's transition. -/
theorem lockSet_endpointReplyRecvOnCore_covers_originRecipient
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId) (origin : SeLe4n.ThreadId)
    (hHead : answeredFrameHeadContext? st target = some (scId, holder))
    (hOrigin : donationOriginRecipient? st scId = some origin) :
    (tcbLock origin, AccessMode.write)
      ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
           endpointObjId).pairs := by
  unfold lockSet_endpointReplyRecvOnCore
  rw [hHead]
  simp only [Option.map_some, Option.bind_some, hOrigin]
  exact lockSet_replyRecv_originRecipient_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _

set_option maxHeartbeats 1000000 in
/-- **PR #894 review — the invoking receiver's own pre-receive return is
declared.**

The twin of `lockSet_endpointReceiveOnCore_covers_preReturn`, and the statement
that makes this footprint true of the delegated shape.  `.replyRecv`'s receive
leg is `.receive`'s transition, so when the endpoint has no queued sender it runs
`cleanupPreReceiveDonationChecked` on the **invoker** -- and the donation return
runs *after* the receive leg, so the invoker still carries whatever `.donated`
binding it entered with.  On a non-delegated reply the recorded server *is* the
invoker and the reply leg has just made it `.unbound`, which is exactly the
coincidence delegation breaks.

The five members are resolved off `replier`, and the recorded server's members
cannot stand in for them: two threads cannot be bound to one scheduling context,
so `receivePreReturn?`'s context is provably never the one the *recorded server's*
binding names.  (That binding-driven resolver was deleted at HP7 (`v0.35.46`); the
argument is unchanged, since it is about the two contexts and not about how either
is spelled.) -/
theorem lockSet_endpointReplyRecvOnCore_covers_preReturn
    (st : SystemState) (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (hRet : receivePreReturn? st endpointObjId replier = some (scId, owner)) :
    (schedContextLock scId, AccessMode.write)
        ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
             endpointObjId).pairs ∧
    (tcbLock owner, AccessMode.write)
        ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
             endpointObjId).pairs ∧
    (∀ head, replyStackHead? st scId = some head →
      (replyLock head, AccessMode.write)
        ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
             endpointObjId).pairs) ∧
    (∀ below, (replyStackBelowHead? st scId).1 = some below →
      (replyLock below, AccessMode.write)
        ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
             endpointObjId).pairs) := by
  unfold lockSet_endpointReplyRecvOnCore receivePreReturnStack?
  rw [hRet]
  simp only [Option.map_some]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lockSet_replyRecv_preReturn_sc_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _
  · exact lockSet_replyRecv_preReturn_owner_tcb_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _
  · intro head hHead
    rw [hHead]
    exact lockSet_replyRecv_preReturn_head_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _
  · intro below hBelow
    rw [hBelow]
    exact lockSet_replyRecv_preReturn_belowHead_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _

/- **WS-OD OD4.7**: the reply **write** member of the `.call` footprint now lives
beside the footprint it is about, as
`Concurrency.lockSet_endpointCall_reply_write_mem`
(`SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`).

It was stated here from SM6.D until OD4.7 needed it in `EndpointCall.lean` — which
cannot import this module, since this module imports it — and a second copy was
added there.  Two theorems with one conclusion is the shape this project deletes
rather than reconciles, so the statement moved to the module that defines
`lockSet_endpointCall` and carries its four sibling membership lemmas, and this
comment records where it went. -/

/-- WS-SM SM6.D (PR #827 review): the per-object reply **write** lock is likewise a
declared member of the **WithCaps** `.call` footprint once the linked reply object
is resolved (`replyId := some rid`).

**WS-RR RR7.7**: since the caps footprint *is* the base footprint at `some
destCnode`, this is the lemma above at that argument.  It used to re-derive the
membership out here through a key-distinctness argument about the destination
CNode, which had to be extended by hand for every member the transfer added —
and the state-level lock the CDT write needs would have been the second such
extension nobody made. -/
theorem lockSet_endpointCallWithCaps_reply_write_mem
    (callerTid : SeLe4n.ThreadId) (cnRoot destCnode endpointObjId : SeLe4n.ObjId)
    (receiverTid : Option SeLe4n.ThreadId) (donatedScId : Option SeLe4n.SchedContextId)
    (rid : SeLe4n.ReplyId) :
    (replyLock rid, AccessMode.write)
      ∈ (lockSet_endpointCallWithCaps callerTid cnRoot destCnode endpointObjId
            receiverTid donatedScId (some rid)).pairs :=
  Concurrency.lockSet_endpointCall_reply_write_mem callerTid cnRoot endpointObjId receiverTid
    donatedScId rid (some destCnode) none none

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
  unfold lookupTcb SystemState.getTcb?
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
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hObjInv : st.objects.invExt)
    (hSz1' : ¬ msg2.registers.size > maxMessageRegisters)
    (hSz2' : ¬ msg2.caps.size > maxExtraCaps) :
    (endpointReplyOnCore replier2 target msg2 executingCore2
        (endpointReplyOnCore replier target msg executingCore st).1).2 = .error .replyCapInvalid := by
  obtain ⟨t, hGet, hReady, _⟩ :=
    endpointReplyOnCore_perCore_delivery replier target msg executingCore st st' tcb ep expected
      hSz1 hSz2 hLk hIpc hStore hObjInv
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
    (donatedOwner? : Option SeLe4n.ThreadId)
    -- WS-OD OD3.7: stated over the reply optional and both below-head reads, so
    -- the atomicity claim covers the footprint a live `.reply` acquires.
    (replyId? : Option SeLe4n.ReplyId)
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    -- WS-OD (`v0.35.4`): and over the head the pop clears.
    (donatedHead? : Option SeLe4n.ReplyId)
    -- **WS-RM (`v0.35.6`)**: and over the frame the removal's splice writes.
    (answeredFrameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: and at the frame-below arity -- the second member the
    -- removal's splice writes.
    (answeredFrameBelow? : Option SeLe4n.ReplyId)
    -- **WS-HP HP10.6**: and at the origin-recipient arity.
    (originRecipient? : Option SeLe4n.ThreadId)
    (s : SystemState) :
    withLockSet (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?
        replyId? belowHeadReply? outerCaller? donatedHead? answeredFrameAbove? answeredFrameBelow? originRecipient?)
        executingCore (endpointReplyOnCore replier target msg executingCore) s
      = (unwindAll executingCore
          (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?
            replyId? belowHeadReply? outerCaller? donatedHead?
            answeredFrameAbove? answeredFrameBelow? originRecipient?).lockAcquireSequence.reverse
          (endpointReplyOnCore replier target msg executingCore
            (acquireAll executingCore
              (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?
            replyId? belowHeadReply? outerCaller? donatedHead?
            answeredFrameAbove? answeredFrameBelow? originRecipient?).lockAcquireSequence s)).1,
         (endpointReplyOnCore replier target msg executingCore
            (acquireAll executingCore
              (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?
            replyId? belowHeadReply? outerCaller? donatedHead?
            answeredFrameAbove? answeredFrameBelow? originRecipient?).lockAcquireSequence s)).2) :=
  lockSet_atomic_under_2pl _ executingCore _ s

/-- WS-SM SM6.C.5 (companion): the cross-core `replyRecv` is likewise a single
2PL-atomic step under its `replyRecv` lock-set. -/
theorem endpointReplyRecvOnCore_atomic_under_lockSet
    (endpointId : SeLe4n.ObjId) (receiver target : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId)
    (executingCore : CoreId) (cnRoot : SeLe4n.ObjId) (newSender? : Option SeLe4n.ThreadId)
    (donatedSc? : Option SeLe4n.SchedContextId) (donatedOwner? : Option SeLe4n.ThreadId)
    -- WS-OD OD3.5: stated over the two members OD3.5 added too, so the atomicity
    -- claim covers the footprint a live `.replyRecv` actually acquires.
    (installsCaps : Bool) (donationServer? : Option SeLe4n.ThreadId)
    (redonatedSc? : Option SeLe4n.SchedContextId)
    -- WS-OD OD3.7: and over both below-head reads, for the same reason.
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    -- WS-OD OD3.13 / `v0.35.4`: and over the queue neighbour, the re-donation's
    -- old head and the returned context's head.
    (queueNeighbour? : Option SeLe4n.ThreadId)
    (redonationOldHead? donatedHead? : Option SeLe4n.ReplyId)
    -- **PR #894 review / WS-RM (`v0.35.6`)**: and over the invoker's own
    -- pre-receive return and the frame the reply leg's splice writes.  Stated
    -- rather than defaulted: an atomicity claim checked at one argument value
    -- while the resolved footprint supplies another is about a different
    -- footprint.
    (preReturnSc? : Option SeLe4n.SchedContextId) (preReturnOwner? : Option SeLe4n.ThreadId)
    (preReturnHead? preReturnBelowHead? : Option SeLe4n.ReplyId)
    (preReturnOuterCaller? : Option SeLe4n.ThreadId)
    (answeredFrameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: and at the frame-below arity -- the second member the
    -- removal's splice writes.
    (answeredFrameBelow? : Option SeLe4n.ReplyId)
    -- **WS-HP HP10.6**: and at the origin-recipient arity.
    (originRecipient? : Option SeLe4n.ThreadId)
    (s : SystemState) :
    withLockSet (lockSet_replyRecv receiver cnRoot target endpointId newSender? donatedSc? donatedOwner? replyId installsCaps donationServer? redonatedSc? belowHeadReply? outerCaller? queueNeighbour? redonationOldHead? donatedHead? preReturnSc? preReturnOwner? preReturnHead? preReturnBelowHead? preReturnOuterCaller? answeredFrameAbove? answeredFrameBelow? originRecipient?)
        executingCore (endpointReplyRecvOnCore endpointId receiver target msg replyId executingCore) s
      = (unwindAll executingCore
          (lockSet_replyRecv receiver cnRoot target endpointId newSender? donatedSc? donatedOwner? replyId installsCaps donationServer? redonatedSc? belowHeadReply? outerCaller? queueNeighbour? redonationOldHead? donatedHead? preReturnSc? preReturnOwner? preReturnHead? preReturnBelowHead? preReturnOuterCaller? answeredFrameAbove? answeredFrameBelow? originRecipient?).lockAcquireSequence.reverse
          (endpointReplyRecvOnCore endpointId receiver target msg replyId executingCore
            (acquireAll executingCore
              (lockSet_replyRecv receiver cnRoot target endpointId newSender? donatedSc? donatedOwner? replyId installsCaps donationServer? redonatedSc? belowHeadReply? outerCaller? queueNeighbour? redonationOldHead? donatedHead? preReturnSc? preReturnOwner? preReturnHead? preReturnBelowHead? preReturnOuterCaller? answeredFrameAbove? answeredFrameBelow? originRecipient?).lockAcquireSequence s)).1,
         (endpointReplyRecvOnCore endpointId receiver target msg replyId executingCore
            (acquireAll executingCore
              (lockSet_replyRecv receiver cnRoot target endpointId newSender? donatedSc? donatedOwner? replyId installsCaps donationServer? redonatedSc? belowHeadReply? outerCaller? queueNeighbour? redonationOldHead? donatedHead? preReturnSc? preReturnOwner? preReturnHead? preReturnBelowHead? preReturnOuterCaller? answeredFrameAbove? answeredFrameBelow? originRecipient?).lockAcquireSequence s)).2) :=
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
  obtain ⟨hRQ, hCur⟩ := wakeThread_independent_of_other_core st' target executingCore c' hOther
  cases hRO : tcb.replyObject with
  | none =>
      rw [endpointReplyOnCore_reply_eq replier target msg executingCore st st' tcb ep expected
            hSz1 hSz2 hLk hIpc hStore hRO]
      exact ⟨by rw [hRQ, hSched], by rw [hCur, hSched]⟩
  | some rid =>
      obtain ⟨st'', hCons, hEq⟩ := endpointReplyOnCore_reply_eq_linked replier target msg
        executingCore st st' tcb ep expected rid hSz1 hSz2 hLk hIpc hStore hRO
      -- The folded removal is scheduler-invisible (`removeCallerReplyFrame_scheduler_eq`),
      -- so the other-core frame transports across it unchanged.
      have hSchedC : st''.scheduler = (wakeThread st' target executingCore).1.scheduler :=
        removeCallerReplyFrame_scheduler_eq
          (wakeThread st' target executingCore).1 st'' target rid hCons
      rw [hEq]
      constructor
      · show st''.scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c'
        rw [hSchedC, hRQ, hSched]
      · show st''.scheduler.currentOnCore c' = st.scheduler.currentOnCore c'
        rw [hSchedC, hCur, hSched]

-- ============================================================================
-- WS-RR RR2.10 — the scheduler-domain footprint of the cross-core `.reply`
-- ============================================================================
--
-- The mirror of RR2.4's call-side footprints, in the same cross-domain
-- `SchedLockId` order (`object < runQueue < replenishQueue`, each same-kind
-- segment `CoreId`-ascending, so the list is the SM3.D acquisition sequence).
-- `lockSet_endpointReply` is an object-domain `LockSet` and cannot name a
-- per-core replenish-queue slot at all; these are where the RR2.8 migration's
-- two writes are declared.

/-- WS-RR RR2.10: the scheduler-domain footprint of the cross-core `.reply`
**donation return** (`applyReplyDonationOnCore`) — the object-store table write
lock (the SchedContext rebinding), the run-queue write lock of the core the
now-passive server is descheduled on, and the replenish-queue write locks of
**both** migration endpoints (the replier's home core, purged, and the original
owner's home core, receiving).

The deschedule core is a *parameter*, not the executing core, because the
recorded server can be a different thread from the reply-cap holder and can be
running on a different core (`determineExecutingCore st expected`, PR #822
review) — the same reason `applyReplyDonationOnCore` takes it.

**WS-RR RR8.12**: spelled through `schedFootprintOfCores`, the shared answer to
"what is a scheduler-domain footprint over these core sets".  The run side was
a bare cons where every sibling footprint used a segment — a fifth spelling of
the three-domain ladder, carrying its own twenty-five-line `_pairwise_le`. -/
def applyReplyDonationOnCoreSchedLockSet
    (descheduleCore replierHome ownerHome : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores [descheduleCore] [replierHome, ownerHome]

/-- RR2.10: every lock in the donation-return footprint is a **write**. -/
theorem applyReplyDonationOnCoreSchedLockSet_write_only
    (descheduleCore replierHome ownerHome : CoreId) :
    ∀ p ∈ applyReplyDonationOnCoreSchedLockSet descheduleCore replierHome ownerHome,
      p.2 = Concurrency.AccessMode.write :=
  schedFootprintOfCores_write_only _ _

/-- RR2.10: the replier's home-core replenish-queue write lock is in the
footprint (the migration's source / purge slot). -/
theorem applyReplyDonationOnCoreSchedLockSet_contains_replierHome_write
    (descheduleCore replierHome ownerHome : CoreId) :
    (SchedLockId.replenishQueue ⟨replierHome⟩, Concurrency.AccessMode.write)
      ∈ applyReplyDonationOnCoreSchedLockSet descheduleCore replierHome ownerHome :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ replierHome).mpr (by simp)

/-- RR2.10: the original owner's home-core replenish-queue write lock is in the
footprint (the migration's destination). -/
theorem applyReplyDonationOnCoreSchedLockSet_contains_ownerHome_write
    (descheduleCore replierHome ownerHome : CoreId) :
    (SchedLockId.replenishQueue ⟨ownerHome⟩, Concurrency.AccessMode.write)
      ∈ applyReplyDonationOnCoreSchedLockSet descheduleCore replierHome ownerHome :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ ownerHome).mpr (by simp)

/-- RR2.10: the deschedule core's run-queue write lock is in the footprint. -/
theorem applyReplyDonationOnCoreSchedLockSet_contains_descheduleCore_write
    (descheduleCore replierHome ownerHome : CoreId) :
    (SchedLockId.runQueue ⟨descheduleCore⟩, Concurrency.AccessMode.write)
      ∈ applyReplyDonationOnCoreSchedLockSet descheduleCore replierHome ownerHome :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ descheduleCore).mpr (by simp)

/-- **RR2.10's coverage obligation**: the donation-return footprint covers
`migrateSchedContextReplenishmentLockSet` member for member — the RR2.8
migration writes only the two replenish-queue slots and this footprint declares
both, so the write stays inside the declared `withLockSet` bracket and the SM3
serializability argument survives it. -/
theorem applyReplyDonationOnCoreSchedLockSet_covers_migration
    (descheduleCore replierHome ownerHome : CoreId) :
    ∀ p ∈ migrateSchedContextReplenishmentLockSet replierHome ownerHome,
      p ∈ applyReplyDonationOnCoreSchedLockSet descheduleCore replierHome ownerHome := by
  intro p hp
  simp only [migrateSchedContextReplenishmentLockSet, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with h | h <;> subst h
  · exact applyReplyDonationOnCoreSchedLockSet_contains_replierHome_write _ _ _
  · exact applyReplyDonationOnCoreSchedLockSet_contains_ownerHome_write _ _ _

/-- RR2.10: the donation-return footprint's keys ascend in the `SchedLockId`
order — the full three-domain ladder. -/
theorem applyReplyDonationOnCoreSchedLockSet_pairwise_le
    (descheduleCore replierHome ownerHome : CoreId) :
    ((applyReplyDonationOnCoreSchedLockSet descheduleCore replierHome ownerHome).map
      (·.1)).Pairwise (· ≤ ·) :=
  schedFootprintOfCores_pairwise_le _ _

/-- RR2.10: the donation-return footprint is within the SM3.D `maxLockSetSize`
cap — four locks at most.

**WS-RR RR7.11**: stated against the constant its name claims rather than the
numeral the constant happened to hold.  See `maxLockSetSize`'s docstring for why
that distinction is load-bearing and why the constant moved. -/
theorem applyReplyDonationOnCoreSchedLockSet_size_le_maxLockSetSize
    (descheduleCore replierHome ownerHome : CoreId) :
    (applyReplyDonationOnCoreSchedLockSet descheduleCore replierHome ownerHome).length
      ≤ Concurrency.maxLockSetSize := by
  have hSeg := schedFootprintOfCores_length_le (runCores := [descheduleCore])
    (replenishCores := [replierHome, ownerHome])
  have hN : Concurrency.numCores = 4 := rfl
  have hM : Concurrency.maxLockSetSize = 24 := rfl
  unfold applyReplyDonationOnCoreSchedLockSet
  omega

/-- WS-RR RR2.10: the scheduler-domain footprint of the **whole** cross-core
`.reply` dispatch — the union of what its three effects write:

* the object-store table lock (the reply delivery's TCB / Reply-object writes
  and the donation return's rebinding);
* the **run-queue** write locks of the woken caller's home core
  (`endpointReplyOnCore`'s `wakeThread`), the recorded server's own core (the
  donation return's deschedule) and the executing core (the PIP reversion's
  local re-bucketing) — duplicates collapse in the segment's canonical form, and
  all three genuinely can differ: a delegated reply cap is held by a thread that
  is neither the recorded server nor the woken caller;
* the **replenish-queue** write locks of the two RR2.8 migration endpoints.

**Dynamic chain extension (declared, not static)**, exactly as on the call side
and in SM6.E's suspend footprint: `propagatePipChainCrossCore` re-buckets each
blocking-chain member's run queue on that member's home core, and the chain is
state-discovered, so the SM3.C.11 walker obligation
(`pipChainStart_tcbSuspend`) covers those per-step acquisitions. -/
def endpointReplyCrossCoreDispatchSchedLockSet
    (callerHome serverCore executingCore replierHome ownerHome : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores [callerHome, serverCore, executingCore] [replierHome, ownerHome]

/-- RR2.10: the dispatch footprint's keys ascend in the `SchedLockId` order. -/
theorem endpointReplyCrossCoreDispatchSchedLockSet_pairwise_le
    (callerHome serverCore executingCore replierHome ownerHome : CoreId) :
    ((endpointReplyCrossCoreDispatchSchedLockSet callerHome serverCore executingCore
      replierHome ownerHome).map (·.1)).Pairwise (· ≤ ·) :=
  schedFootprintOfCores_pairwise_le _ _

/-- **RR2.10 (dispatch-level coverage)**: the whole-dispatch footprint covers
the donation-return footprint member for member — hence, by
`applyReplyDonationOnCoreSchedLockSet_covers_migration`, the RR2.8 migration's
two replenish-queue write locks and the server's deschedule run-queue lock. -/
theorem endpointReplyCrossCoreDispatchSchedLockSet_covers_donation
    (callerHome serverCore executingCore replierHome ownerHome : CoreId) :
    ∀ p ∈ applyReplyDonationOnCoreSchedLockSet serverCore replierHome ownerHome,
      p ∈ endpointReplyCrossCoreDispatchSchedLockSet callerHome serverCore executingCore
            replierHome ownerHome :=
  -- The server's own core is one of the run-queue segment's three cores.
  schedFootprintOfCores_subset (fun _ h => by simp at h; simp [h]) (fun _ h => h)

-- ============================================================================
-- §11 WS-RR RR8.12 — the scheduler-domain footprint of the cross-core `.receive`
-- ============================================================================
--
-- `lockSet_endpointReceive` is an object-domain `LockSet` and cannot name a
-- per-core run-queue or replenish-queue slot at all, so
-- `UncoveredLockDomain.syscallSeamSchedulerDomain` recorded the live `.receive`
-- arm's scheduler writes as outside the footprint the RR7.12 seam acquires.
-- This section declares them, in the same cross-domain `SchedLockId` order every
-- sibling footprint uses (`object < runQueue < replenishQueue`, each same-kind
-- segment `CoreId`-ascending, so the list *is* the SM3.D acquisition sequence).
-- Inert until the bracket cut wires `schedLockSetForSyscall`.

/-- SM8.B.2, relocated to production at **WS-RR RR8.12**: **the cores a
cross-core endpoint receive may write** — the woken sender's home core on a
rendezvous, the receiver's own core when it blocks.

Read from the pre-state through the same `sendQ.head` the transition resolves,
so the declared set and the transition name the same sender. The two arms are
genuinely exclusive: a receive that rendezvouses does not block, and a receive
that blocks wakes nobody.

Relocated for the reason `endpointSendWriteSet`'s docstring gives: the
scheduler-domain footprint below is production and
`InformationFlow/NonInterferenceCrossCore.lean`, where this was declared, is
staged and imports `Kernel.API`. -/
def endpointReceiveDualWriteSet (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) : List CoreId :=
  match st.getEndpoint? endpointId with
  | some ep =>
      match ep.sendQ.head with
      | some sender => [determineTargetCore st sender]
      | none => [executingCore]
  | none => []

/-- **WS-RR RR8.12**: on a rendezvous the set is the home core of the sender
`receiveRendezvousSender?` names.

The tie between this core list and the object-domain footprint's own `senderTid`
member, which comes from that resolver: the two cannot name different threads.
Stating it here rather than spelling the resolver inside the definition keeps
every SM8.B.2 result taken against the write set byte-identical — the `none`
arms of the two readings differ, since `receiveRendezvousSender?` answers `none`
for an unresolvable endpoint as well as for an empty send queue, and the write
set distinguishes them. -/
theorem endpointReceiveDualWriteSet_of_sender (st : SystemState)
    (endpointId : SeLe4n.ObjId) (executingCore : CoreId) (sender : SeLe4n.ThreadId)
    (hSender : receiveRendezvousSender? st endpointId = some sender) :
    endpointReceiveDualWriteSet st endpointId executingCore
      = [determineTargetCore st sender] := by
  unfold endpointReceiveDualWriteSet
  unfold receiveRendezvousSender? at hSender
  cases hEp : st.getEndpoint? endpointId with
  | none => rw [hEp] at hSender; simp at hSender
  | some ep =>
      rw [hEp] at hSender
      simp only [Option.bind_some] at hSender
      simp only [hSender]

/-- **WS-RR RR8.12**: and on the block path it is the executing core's, which the
receiver's own deschedule writes. -/
theorem endpointReceiveDualWriteSet_of_blocked (st : SystemState)
    (endpointId : SeLe4n.ObjId) (executingCore : CoreId) (ep : Endpoint)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = none) :
    endpointReceiveDualWriteSet st endpointId executingCore = [executingCore] := by
  unfold endpointReceiveDualWriteSet
  rw [hEp]
  simp only [hHead]

/-- WS-RR RR2 (closure audit): the bare per-core receive preserves the
object-store invariant — the definition walk, mirroring
`endpointSendDualOnCore_preserves_objects_invExt`. -/
theorem endpointReceiveDualOnCore_preserves_objects_invExt
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1.objects.invExt := by
  unfold endpointReceiveDualOnCore
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hObjInv
  | some ep =>
    simp only
    cases hHead : ep.sendQ.head with
    | some sender0 =>
      simp only
      cases hPop : endpointQueuePopHead endpointId false st with
      | error e => simp only; exact hObjInv
      | ok popRes =>
        obtain ⟨sender, senderTcb, st'⟩ := popRes
        simp only
        have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId false
          st st' sender senderTcb hObjInv hPop
        split
        · -- The dequeued sender was a `Call`: re-block it on reply, link, deliver.
          cases hS1 : storeTcbIpcStateAndMessage st' sender
              (.blockedOnReply endpointId (some receiver)) none with
          | error e => simp only; exact hObjInv
          | ok st'' =>
            simp only
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st' st''
              sender _ _ hObjInv1 hS1
            cases replyId with
            | none => exact hObjInv
            | some rid =>
              simp only
              cases hLink : SystemState.linkCallerReply sender rid st'' with
              | error e => simp only; exact hObjInv
              | ok pLink =>
                obtain ⟨⟨⟩, stLinked⟩ := pLink
                simp only
                have hObjInv3 := linkCallerReply_preserves_objects_invExt st'' stLinked
                  sender rid hObjInv2 hLink
                cases hS2 : storeTcbIpcStateAndMessage stLinked receiver .ready
                    senderTcb.pendingMessage with
                | ok st3 =>
                    exact storeTcbIpcStateAndMessage_preserves_objects_invExt stLinked st3
                      receiver _ _ hObjInv3 hS2
                | error e => simp only; exact hObjInv
        · -- A plain `Send`: complete the sender, wake it on its home core, deliver.
          cases hS1 : storeTcbIpcStateAndMessage st' sender .ready none with
          | error e => simp only; exact hObjInv
          | ok st'' =>
            simp only
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st' st''
              sender _ _ hObjInv1 hS1
            have hObjInvW := wakeThread_preserves_objects_invExt st'' sender executingCore hObjInv2
            cases hS2 : storeTcbIpcStateAndMessage (wakeThread st'' sender executingCore).1
                receiver .ready senderTcb.pendingMessage with
            | ok st4 =>
                exact storeTcbIpcStateAndMessage_preserves_objects_invExt _ st4 receiver _ _
                  hObjInvW hS2
            | error e => simp only; exact hObjInv
    | none =>
      simp only
      cases hClean : cleanupPreReceiveDonationChecked st receiver with
      | error e => simp only; exact hObjInv
      | ok stClean =>
        simp only
        have hObjInvC : stClean.objects.invExt := by
          unfold cleanupPreReceiveDonationChecked at hClean
          cases hLk : lookupTcb st receiver with
          | none => rw [hLk] at hClean; cases hClean; exact hObjInv
          | some recvTcb =>
            rw [hLk] at hClean; simp only [] at hClean
            cases hB : recvTcb.schedContextBinding with
            | donated scId originalOwner =>
                rw [hB] at hClean
                exact returnDonatedSchedContextResolved_lift hClean
                  (fun n s hs => returnDonatedSchedContext_preserves_objects_invExt st s receiver
                    scId originalOwner hObjInv n hs)
            | unbound => rw [hB] at hClean; cases hClean; exact hObjInv
            | bound scId => rw [hB] at hClean; cases hClean; exact hObjInv
        cases hEnq : endpointQueueEnqueue endpointId true receiver stClean with
        | error e => simp only; exact hObjInv
        | ok st1 =>
          simp only
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver
            stClean st1 hObjInvC hEnq
          cases hS1 : storeTcbIpcStateAndMessage st1 receiver (.blockedOnReceive endpointId)
              none with
          | error e => simp only; exact hObjInv
          | ok st2 =>
            simp only
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2
              receiver _ _ hObjInv1 hS1
            cases hGetR : st2.getTcb? receiver with
            | none =>
                show (removeRunnableOnCore st2 receiver executingCore).objects.invExt
                rw [removeRunnableOnCore_preserves_objects]
                exact hObjInv2
            | some rTcb =>
              simp only
              split
              · cases hStash : storeObject receiver.toObjId
                    (.tcb { rTcb with pendingReceiveReply := replyId }) st2 with
                | error e => simp only; exact hObjInv
                | ok pStash =>
                  obtain ⟨⟨⟩, stStashed⟩ := pStash
                  show (removeRunnableOnCore stStashed receiver executingCore).objects.invExt
                  rw [removeRunnableOnCore_preserves_objects]
                  exact storeObject_preserves_objects_invExt st2 stStashed receiver.toObjId _
                    hObjInv2 hStash
              · exact hObjInv

/-- **WS-RR RR8.12 (frame)**: a cross-core receive that **rendezvouses** moves no
thread's home core.

The theorem that licenses resolving WS-OD OD3.6's donation cores on the syscall's
*pre*-state: the donation runs at the post-receive-leg state, so a pre-state
reading is only the same reading if nothing the leg does moves a home.  Nothing
does — the rendezvous is a queue pop, TCB `ipcState` / `pendingMessage` stores, a
reply link and a run-queue insert, and `determineTargetCore` reads `cpuAffinity`,
which only `.tcbSetAffinity` writes.

**Stated on the rendezvous branch, and that is the claim's own subject rather than
an economy.**  The replenish segment `endpointReceiveHandoffReplenishCores`
declares is `[]` wherever the send queue is empty — a receive that blocks donates
nothing (`rendezvousDequeuedCall` is false for the `.blockedOnReceive` id the
block path returns) — so there is no core for a pre-state reading to get wrong
there.  The block path frames homes too (its steps are a donation return, an
enqueue, a TCB store, a stash and a run-queue removal, none of them an affinity
write); that half has no consumer, so it is not stated. -/
theorem endpointReceiveDualOnCore_determineTargetCore_eq_of_rendezvous
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId) (st : SystemState)
    (ep : Endpoint) (sender x : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = some sender) :
    determineTargetCore
        (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 x
      = determineTargetCore st x := by
  unfold endpointReceiveDualOnCore
  rw [hEp]
  simp only [hHead]
  cases hPop : endpointQueuePopHead endpointId false st with
  | error e => rfl
  | ok triple =>
      obtain ⟨popTid, popTcb, st1⟩ := triple
      dsimp only
      have hF1 : determineTargetCore st1 x = determineTargetCore st x :=
        endpointQueuePopHead_determineTargetCore_eq endpointId false st st1 popTid popTcb x
          hObjInv hPop
      have hI1 : st1.objects.invExt :=
        endpointQueuePopHead_preserves_objects_invExt endpointId false st st1 popTid popTcb
          hObjInv hPop
      split
      · -- `Call` rendezvous: the caller is parked `.blockedOnReply` and linked.
        cases hS2 : storeTcbIpcStateAndMessage st1 popTid
            (.blockedOnReply endpointId (some receiver)) none with
        | error e => rfl
        | ok st2 =>
            dsimp only
            have hF2 : determineTargetCore st2 x = determineTargetCore st x := by
              rw [storeTcbIpcStateAndMessage_determineTargetCore_eq st1 st2 popTid _ none x
                hI1 hS2, hF1]
            have hI2 : st2.objects.invExt :=
              storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2 popTid _ none hI1 hS2
            cases hRid : replyId with
            | none => rfl
            | some rid =>
                dsimp only
                cases hLink : SystemState.linkCallerReply popTid rid st2 with
                | error e => rfl
                | ok pair =>
                    obtain ⟨_, st3⟩ := pair
                    dsimp only
                    have hF3 : determineTargetCore st3 x = determineTargetCore st x := by
                      rw [linkCallerReply_determineTargetCore_eq st2 st3 popTid rid x hI2 hLink,
                        hF2]
                    have hI3 : st3.objects.invExt :=
                      linkCallerReply_preserves_objects_invExt st2 st3 popTid rid hI2 hLink
                    cases hS4 : storeTcbIpcStateAndMessage st3 receiver .ready
                        popTcb.pendingMessage with
                    | error e => rfl
                    | ok st4 =>
                        dsimp only
                        exact (storeTcbIpcStateAndMessage_determineTargetCore_eq st3 st4 receiver
                          .ready popTcb.pendingMessage x hI3 hS4).trans hF3
      · -- plain `Send` rendezvous: the sender is made `.ready` and woken.
        cases hS2 : storeTcbIpcStateAndMessage st1 popTid .ready none with
        | error e => rfl
        | ok st2 =>
            dsimp only
            have hF2 : determineTargetCore st2 x = determineTargetCore st x := by
              rw [storeTcbIpcStateAndMessage_determineTargetCore_eq st1 st2 popTid .ready none x
                hI1 hS2, hF1]
            have hI2 : st2.objects.invExt :=
              storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2 popTid .ready none hI1
                hS2
            have hFW : determineTargetCore (wakeThread st2 popTid executingCore).1 x
                = determineTargetCore st x := by
              rw [wakeThread_determineTargetCore_eq st2 popTid x executingCore hI2, hF2]
            have hIW : (wakeThread st2 popTid executingCore).1.objects.invExt :=
              wakeThread_preserves_objects_invExt st2 popTid executingCore hI2
            cases hS3 : storeTcbIpcStateAndMessage (wakeThread st2 popTid executingCore).1
                receiver .ready popTcb.pendingMessage with
            | error e => rfl
            | ok st3 =>
                dsimp only
                exact (storeTcbIpcStateAndMessage_determineTargetCore_eq _ st3 receiver .ready
                  popTcb.pendingMessage x hIW hS3).trans hFW

/-- **WS-RR RR8.12 (frame)**: and installing the parked send's capabilities moves
none either, so the whole receive leg the live `.receive` arm runs frames every
home core on the rendezvous path.

The shape `endpointReceiveDualWithCapsOnCore_scheduler_eq` has: every branch but
the last returns the bare receive's own post-state, and the last is an
`ipcUnwrapCaps`, which fixes the whole `getTcb?` projection. -/
theorem endpointReceiveDualWithCapsOnCore_determineTargetCore_eq_of_rendezvous
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (ep : Endpoint) (sender x : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = some sender) :
    determineTargetCore
        (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
          receiverSlotBase executingCore st).1 x
      = determineTargetCore st x := by
  have hLeg := endpointReceiveDualOnCore_determineTargetCore_eq_of_rendezvous endpointId
    receiver replyId executingCore st ep sender x hObjInv hEp hHead
  have hLegInv :
      ((endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1).objects.invExt :=
    endpointReceiveDualOnCore_preserves_objects_invExt endpointId receiver replyId executingCore
      st hObjInv
  unfold endpointReceiveDualWithCapsOnCore
  cases hRecv : endpointReceiveDualOnCore endpointId receiver replyId executingCore st with
  | mk stRecv res =>
      rw [hRecv] at hLeg hLegInv
      cases res with
      | error e => simpa using hLeg
      | ok pair =>
          obtain ⟨senderId, sgi⟩ := pair
          simp only []
          repeat' split
          all_goals first
            | simpa using hLeg
            | (rename_i hUnwrap
               rw [ipcUnwrapCaps_determineTargetCore_eq _ receiverCspaceRoot receiverSlotBase _
                 stRecv _ _ x hLegInv hUnwrap]
               simpa using hLeg)

/-- **WS-RR RR8.12 (frame)**: a cross-core receive touches **no** core's
replenish queue.

The obligation the footprint below owes for the replenish segment it declares:
every core in that segment comes from the *donation* the arm runs afterwards, and
none from the receive leg itself.  Both paths compose steps that frame the whole
scheduler (the queue pop or enqueue, the TCB stores, the reply link, the stash,
and — since the block path returns a donation — `cleanupPreReceiveDonationChecked`)
with one that writes a run queue alone (the rendezvous' `wakeThread`, the block's
`removeRunnableOnCore`).  A `blockedOnCall` rendezvous writes no per-core slot at
all: the caller becomes `.blockedOnReply` and is deliberately not woken. -/
theorem endpointReceiveDualOnCore_replenishQueueOnCore (epId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (ec : CoreId)
    (st : SystemState) (c : CoreId) :
    (endpointReceiveDualOnCore epId receiver replyId ec st).1.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold endpointReceiveDualOnCore
  cases hEp : st.getEndpoint? epId with
  | none => simp only []; split <;> rfl
  | some ep =>
    simp only []
    cases hHead : ep.sendQ.head with
    | none =>
      simp only []
      split
      · rfl
      · next stClean hClean =>
        split
        · rfl
        · next st1 hEnq =>
          split
          · rfl
          · next st2 hIpc =>
            have hChain : st2.scheduler = st.scheduler := by
              rw [storeTcbIpcStateAndMessage_scheduler_eq st1 st2 _ _ _ hIpc,
                endpointQueueEnqueue_scheduler_eq epId true receiver stClean st1 hEnq,
                cleanupPreReceiveDonationChecked_scheduler_eq st stClean receiver hClean]
            split
            · simp only [removeRunnableOnCore_replenishQueueOnCore, hChain]
            · next rTcb hTcb =>
              split
              · split
                · rfl
                · next _ st3 hStash =>
                  simp only [removeRunnableOnCore_replenishQueueOnCore,
                    storeObject_scheduler_eq st2 st3 _ _ hStash, hChain]
              · rfl
    | some _ =>
      simp only []
      split
      · rfl
      · next sender senderTcb st1 hPop =>
        have hPopSched : st1.scheduler = st.scheduler :=
          endpointQueuePopHead_scheduler_eq epId false st st1 sender hPop
        split
        · -- `blockedOnCall` sender: recorded `.blockedOnReply`, never woken.
          rw [if_pos rfl]
          split
          · rfl
          · next st2 hIpc =>
            split
            · rfl
            · next rid =>
              split
              · rfl
              · next st3 hLink =>
                split
                · next st4 hMsg =>
                  simp only [storeTcbIpcStateAndMessage_scheduler_eq st3 st4 _ _ _ hMsg,
                    linkCallerReply_scheduler_eq st2 st3 sender rid hLink,
                    storeTcbIpcStateAndMessage_scheduler_eq st1 st2 _ _ _ hIpc, hPopSched]
                · rfl
        · -- `blockedOnSend` sender: woken on its own home core.
          rw [if_neg (by simp)]
          split
          · rfl
          · next st2 hReady =>
            split
            · next st3 hMsg =>
              simp only [storeTcbIpcStateAndMessage_scheduler_eq _ st3 _ _ _ hMsg,
                wakeThread_replenishQueueOnCore,
                storeTcbIpcStateAndMessage_scheduler_eq st1 st2 _ _ _ hReady, hPopSched]
            · rfl

/-- **WS-RR RR8.12 (frame)**: and neither does the caps-carrying form the live
`.receive` arm runs — the capability install writes CNodes and the CDT, never the
scheduler (`ipcUnwrapCaps_preserves_scheduler`). -/
theorem endpointReceiveDualWithCapsOnCore_replenishQueueOnCore (epId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (cnRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot) (ec : CoreId)
    (st st' : SystemState) (c : CoreId)
    (h : (endpointReceiveDualWithCapsOnCore epId receiver replyId cnRoot slotBase ec st).1
      = st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  subst h
  rw [endpointReceiveDualWithCapsOnCore_scheduler_eq epId receiver replyId cnRoot slotBase ec st]
  exact endpointReceiveDualOnCore_replenishQueueOnCore epId receiver replyId ec st c

/-- **WS-RR RR8.12 (PR #897 Codex review): does this thread carry an outstanding
`Call`?** -- the PRE-state sibling of `rendezvousDequeuedCall`, clause for clause.

The two ask one question at two states and *must* be spelled separately, because a
dequeued `Call` sender is `.blockedOnCall` before the receive leg runs and
`.blockedOnReply` after it.  Asking for the post-state constructor at the pre-state
would answer `false` for exactly the sender that *will* donate, so a footprint
derived from it would **omit** a lock the transition writes -- and a footprint that
omits a written lock is false, where one wider than its operation is merely
expensive.

Reads through `lookupTcb`, not `getTcb?`, for the reason `rendezvousDequeuedCall`
does: `lookupTcb` refuses a reserved (idle) thread id, and it is the reader
`endpointQueuePopHead` itself uses, so this is the leg's own branch condition
rather than a second reading of it
(`endpointQueuePopHead_popped_tcb_eq_lookup`). -/
def rendezvousSenderIsCall (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  match lookupTcb st tid with
  | some tcb =>
      match tcb.ipcState with
      | .blockedOnCall _ => true
      | _                => false
  | none => false

/-- **WS-RR RR8.12**: true exactly of a thread the store resolves as
`.blockedOnCall`. -/
theorem rendezvousSenderIsCall_of_blockedOnCall (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (callEp : SeLe4n.ObjId)
    (hTcb : lookupTcb st tid = some tcb) (hCall : tcb.ipcState = .blockedOnCall callEp) :
    rendezvousSenderIsCall st tid = true := by
  unfold rendezvousSenderIsCall
  simp only [hTcb, hCall]

/-- **WS-RR RR8.12 (PR #897 Codex review)**: and false of one still parked
`.blockedOnSend` -- the plain `Send` rendezvous this cut narrows the footprint on.

`ipcStateQueueMembershipConsistent` admits exactly `.blockedOnSend` and
`.blockedOnCall` for a thread on an endpoint's send queue, so this is *the*
reachable non-`Call` shape there; the predicate is false for every other
`ipcState` by construction. -/
theorem rendezvousSenderIsCall_of_blockedOnSend (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (sendEp : SeLe4n.ObjId)
    (hTcb : lookupTcb st tid = some tcb) (hSend : tcb.ipcState = .blockedOnSend sendEp) :
    rendezvousSenderIsCall st tid = false := by
  unfold rendezvousSenderIsCall
  simp only [hTcb, hSend]

/-- **WS-RR RR8.12 (PR #897 Codex review): the queued sender, WHEN IT CARRIES A
`Call`.**

Derived from `receiveRendezvousSender?` -- the resolver the arm's own sender member
and `receiveRendezvousDonatedSc?` already come from -- so the three cannot disagree
about which thread a rendezvous dequeues, and narrowed by `rendezvousSenderIsCall`,
which is `rendezvousDequeuedCall`'s pre-state sibling.  A `Bool` guard rather than a
nested match, so a consumer splits an `if` rather than reducing a matcher. -/
def receiveRendezvousCallSender? (st : SystemState) (endpointId : SeLe4n.ObjId) :
    Option SeLe4n.ThreadId :=
  (receiveRendezvousSender? st endpointId).bind fun sender =>
    if rendezvousSenderIsCall st sender then some sender else none

/-- **WS-RR RR8.12**: it narrows `receiveRendezvousSender?` and never names another
thread -- the two resolvers agree about *which* thread whenever this one answers. -/
theorem receiveRendezvousCallSender?_eq_sender (st : SystemState)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (h : receiveRendezvousCallSender? st endpointId = some sender) :
    receiveRendezvousSender? st endpointId = some sender := by
  unfold receiveRendezvousCallSender? at h
  cases hS : receiveRendezvousSender? st endpointId with
  | none => rw [hS] at h; exact absurd h (by simp)
  | some s =>
    -- `cases hS :` has already substituted the resolver's value in the GOAL, so
    -- only `h` still mentions it.
    simp only [hS, Option.bind_some] at h
    split at h
    · exact congrArg some (Option.some.inj h)
    · exact absurd h (by simp)

/-- **WS-RR RR8.12**: `none` when the endpoint has no queued sender at all -- the
block path, where the arm donates nothing. -/
theorem receiveRendezvousCallSender?_of_blocked (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = none) :
    receiveRendezvousCallSender? st endpointId = none := by
  unfold receiveRendezvousCallSender? receiveRendezvousSender?
  rw [hEp]
  simp only [Option.bind_some, hHead]
  rfl

/-- **WS-RR RR8.12 (PR #897 Codex review)**: and `none` on a plain `Send`
rendezvous -- the case this cut exists to close. -/
theorem receiveRendezvousCallSender?_of_blockedOnSend (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint) (sender : SeLe4n.ThreadId)
    (senderTcb : TCB) (sendEp : SeLe4n.ObjId)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = some sender)
    (hTcb : lookupTcb st sender = some senderTcb)
    (hSend : senderTcb.ipcState = .blockedOnSend sendEp) :
    receiveRendezvousCallSender? st endpointId = none := by
  unfold receiveRendezvousCallSender? receiveRendezvousSender?
  rw [hEp]
  simp only [Option.bind_some, hHead,
    rendezvousSenderIsCall_of_blockedOnSend st sender senderTcb sendEp hTcb hSend]
  rfl

/-- **WS-RR RR8.12 (PR #897 Codex review)**: and `some sender` on a `Call`
rendezvous -- the one shape on which the arm's donation can migrate a
replenishment. -/
theorem receiveRendezvousCallSender?_of_blockedOnCall (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint) (sender : SeLe4n.ThreadId)
    (senderTcb : TCB) (callEp : SeLe4n.ObjId)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = some sender)
    (hTcb : lookupTcb st sender = some senderTcb)
    (hCall : senderTcb.ipcState = .blockedOnCall callEp) :
    receiveRendezvousCallSender? st endpointId = some sender := by
  unfold receiveRendezvousCallSender? receiveRendezvousSender?
  rw [hEp]
  simp only [Option.bind_some, hHead,
    rendezvousSenderIsCall_of_blockedOnCall st sender senderTcb callEp hTcb hCall]
  rfl

/-- **WS-RR RR8.12 (PR #897 Codex review)**: the donation guard reads the store
only through `lookupTcb`, so a step that fixes the `getTcb?` projection fixes the
guard.  The congruence the `ipcUnwrapCaps` tail of the `.receive` arm needs. -/
private theorem rendezvousDequeuedCall_congr_getTcb? (st' st : SystemState)
    (tid : SeLe4n.ThreadId) (h : st'.getTcb? tid = st.getTcb? tid) :
    rendezvousDequeuedCall st' tid = rendezvousDequeuedCall st tid := by
  have hL : lookupTcb st' tid = lookupTcb st tid := by
    unfold lookupTcb
    split
    · rfl
    · exact h
  unfold rendezvousDequeuedCall
  rw [hL]

/-- **WS-RR RR8.12 (PR #897 Codex review)**: a `.ready` thread is not a dequeued
`Call`.  The `lookupTcb`/`getTcb?` bridge the walk below needs: a reserved id
resolves to nothing there, and every other id resolves through `getTcb?`. -/
private theorem rendezvousDequeuedCall_false_of_getTcb?_ready (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready) :
    rendezvousDequeuedCall st tid = false := by
  have hL : lookupTcb st tid = none ∨ lookupTcb st tid = some tcb := by
    unfold lookupTcb
    split
    · exact Or.inl rfl
    · exact Or.inr hTcb
  unfold rendezvousDequeuedCall
  rcases hL with h | h
  · simp only [h]
  · simp only [h, hReady]

/-- **WS-RR RR8.12 (PR #897 Codex review)**: and neither is a thread still parked
`.blockedOnSend`, which is what the refusal branches of the receive leg return. -/
private theorem rendezvousDequeuedCall_false_of_blockedOnSend (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (sendEp : SeLe4n.ObjId)
    (hTcb : lookupTcb st tid = some tcb) (hSend : tcb.ipcState = .blockedOnSend sendEp) :
    rendezvousDequeuedCall st tid = false := by
  unfold rendezvousDequeuedCall
  simp only [hTcb, hSend]

/-- **WS-RR RR8.12 (PR #897 Codex review): a plain `Send` rendezvous leaves the
dequeued sender `.ready`, so the post-state donation guard is FALSE.**

This is the licence for declaring an **empty** replenish segment there, and the
whole content of the narrowing: `endpointReceiveHandoffReplenishCores` used to name
both cores whenever the send queue was non-empty, while WS-OD OD3.6's donation fires
only on a dequeued `Call` -- so every ordinary `seL4_Send` rendezvous declared two
replenish-queue write locks for a migration that provably does not happen, and lock
contention is an observable channel (SM8.D's CC-5) rather than a free
over-approximation.

`endpointReceiveDualOnCore` branches on the *pre*-dequeue TCB's `ipcState` -- the
record `endpointQueuePopHead` hands back, which
`endpointQueuePopHead_popped_tcb_eq_lookup` ties to `lookupTcb st sender`, so this
reads the leg's own branch condition rather than a second copy of it.  The `Send`
arm stores `.ready` at the sender's key, wakes it (`getTcb?`-invisible on a `.ready`
thread) and then stores the *receiver*; whether the two ids coincide is immaterial,
because the last write at the sender's key is `.ready` either way, which is why no
distinctness hypothesis appears.

Unconditional in the result, refusal branches included: those return the pre-state,
where the sender is `.blockedOnSend` and so not `.blockedOnReply`.  That is why the
hypothesis names `.blockedOnSend` rather than "not a `Call`": a pre-state sender
already `.blockedOnReply` satisfies the weaker hypothesis and refutes the conclusion
on a refusal, and `ipcStateQueueMembershipConsistent` is what says `.blockedOnSend`
is the reachable non-`Call` shape for a thread on a send queue. -/
theorem endpointReceiveDualOnCore_not_dequeuedCall_of_blockedOnSend
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId) (st : SystemState)
    (ep : Endpoint) (sender : SeLe4n.ThreadId) (senderTcb : TCB) (sendEp : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = some sender)
    (hTcb : lookupTcb st sender = some senderTcb)
    (hSend : senderTcb.ipcState = .blockedOnSend sendEp) :
    rendezvousDequeuedCall
        (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 sender
      = false := by
  have hFail := rendezvousDequeuedCall_false_of_blockedOnSend st sender senderTcb sendEp hTcb hSend
  have hEpObj : st.objects[endpointId]? = some (.endpoint ep) :=
    (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
  unfold endpointReceiveDualOnCore
  rw [hEp]
  simp only [hHead]
  cases hPop : endpointQueuePopHead endpointId false st with
  | error e => simpa using hFail
  | ok triple =>
      obtain ⟨popTid, popTcb, st1⟩ := triple
      simp only []
      have hHeadQ : (if (false : Bool) then ep.receiveQ else ep.sendQ).head = some sender := by
        simpa using hHead
      have hPopId : popTid = sender :=
        endpointQueuePopHead_popped_eq_head endpointId false st st1 ep popTid sender popTcb
          hEpObj hHeadQ hPop
      have hPopTcb : lookupTcb st sender = some popTcb :=
        endpointQueuePopHead_popped_tcb_eq_lookup endpointId false st st1 ep popTid sender popTcb
          hEpObj hHeadQ hPop
      -- The popped record IS the one the hypothesis names; keep `popTcb` (the
      -- body's own binding) and carry the hypothesis onto it, rather than
      -- substituting and leaving the body's `let` mentioning a dead name.
      have hEqTcb : popTcb = senderTcb := Option.some.inj (hPopTcb.symm.trans hTcb)
      have hSend' : popTcb.ipcState = .blockedOnSend sendEp := by rw [hEqTcb]; exact hSend
      subst hPopId
      have hI1 : st1.objects.invExt :=
        endpointQueuePopHead_preserves_objects_invExt endpointId false st st1 popTid popTcb
          hObjInv hPop
      split
      · -- The `Call` arm is unreachable: the branch test is `senderTcb.ipcState`,
        -- which `hSend` fixes at `.blockedOnSend`.
        rename_i hCall
        rw [hSend'] at hCall
        exact absurd hCall (by simp)
      · cases hS2 : storeTcbIpcStateAndMessage st1 popTid .ready none with
        | error e => simpa using hFail
        | ok st2 =>
            simp only []
            obtain ⟨t2, hT2, hR2⟩ :=
              storeTcbIpcStateAndMessage_getTcb?_ipcState st1 st2 popTid .ready none hI1 hS2
            have hI2 : st2.objects.invExt :=
              storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2 popTid .ready none hI1 hS2
            have hTW : (wakeThread st2 popTid executingCore).1.getTcb? popTid = some t2 := by
              rw [wakeThread_getTcb?_eq_of_ready st2 popTid executingCore t2 hT2 hR2 hI2 popTid]
              exact hT2
            have hIW : (wakeThread st2 popTid executingCore).1.objects.invExt :=
              wakeThread_preserves_objects_invExt st2 popTid executingCore hI2
            cases hS3 : storeTcbIpcStateAndMessage (wakeThread st2 popTid executingCore).1
                receiver .ready popTcb.pendingMessage with
            | error e => simpa using hFail
            | ok st3 =>
                simp only []
                by_cases hEqId : receiver = popTid
                · subst hEqId
                  obtain ⟨t3, hT3, hR3⟩ :=
                    storeTcbIpcStateAndMessage_getTcb?_ipcState _ st3 receiver .ready
                      popTcb.pendingMessage hIW hS3
                  exact rendezvousDequeuedCall_false_of_getTcb?_ready st3 receiver t3 hT3 hR3
                · have hNe : popTid.toObjId ≠ receiver.toObjId := fun h =>
                    hEqId (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
                  have hFrame := storeTcbIpcStateAndMessage_preserves_objects_ne
                    (wakeThread st2 popTid executingCore).1 st3 receiver .ready
                    popTcb.pendingMessage popTid.toObjId hNe hIW hS3
                  refine rendezvousDequeuedCall_false_of_getTcb?_ready st3 popTid t2 ?_ hR2
                  simp only [SystemState.getTcb?] at hTW ⊢
                  rw [hFrame]
                  exact hTW

/-- **WS-RR RR8.12 (PR #897 Codex review)**: `ipcUnwrapCaps` fixes the whole
`getTcb?` projection -- forward by `ipcUnwrapCaps_preserves_tcb_objects`, back by
`ipcUnwrapCaps_tcb_backward`, so the two directions join into an equality.

Cap transfer writes only `receiverRoot`, and only as a CNode, so no TCB is
created, destroyed or altered.  The `determineTargetCore` family reaches the same
conclusion one field down; this is the whole record, because the donation guard
reads `ipcState` rather than `cpuAffinity`. -/
private theorem ipcUnwrapCaps_getTcb?_eq (msg : IpcMessage) (receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool) (st st' : SystemState)
    (summary : CapTransferSummary) (x : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg receiverRoot slotBase grantRight st = .ok (summary, st')) :
    st'.getTcb? x = st.getTcb? x := by
  simp only [SystemState.getTcb?]
  cases hT : st.objects[x.toObjId]? with
  | none =>
      cases hT' : st'.objects[x.toObjId]? with
      | none => rfl
      | some obj =>
          cases obj with
          | tcb tcb =>
              rw [ipcUnwrapCaps_tcb_backward msg receiverRoot slotBase grantRight st st' summary
                x.toObjId tcb hObjInv hStep hT'] at hT
              exact absurd hT (by simp)
          | cnode _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _
          | reply _ => rfl
  | some obj =>
      cases obj with
      | tcb tcb =>
          rw [ipcUnwrapCaps_preserves_tcb_objects msg receiverRoot slotBase grantRight st st'
            summary x.toObjId tcb hT hObjInv hStep]
      | cnode _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _
      | reply _ =>
          cases hT' : st'.objects[x.toObjId]? with
          | none => rfl
          | some obj' =>
              cases obj' with
              | tcb tcb' =>
                  rw [ipcUnwrapCaps_tcb_backward msg receiverRoot slotBase grantRight st st'
                    summary x.toObjId tcb' hObjInv hStep hT'] at hT
                  exact absurd hT (by simp)
              | cnode _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
              | schedContext _ | reply _ => rfl

/-- **WS-RR RR8.12 (PR #897 Codex review)**: and installing the parked send's
capabilities does not revive the guard, so the leg's verdict is the whole arm's.

Same shape as `endpointReceiveDualWithCapsOnCore_determineTargetCore_eq_of_rendezvous`:
every branch but the last returns the bare leg's own post-state, and the last is an
`ipcUnwrapCaps`, which fixes the whole `getTcb?` projection. -/
theorem endpointReceiveDualWithCapsOnCore_not_dequeuedCall_of_blockedOnSend
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (ep : Endpoint) (sender : SeLe4n.ThreadId) (senderTcb : TCB) (sendEp : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = some sender)
    (hTcb : lookupTcb st sender = some senderTcb)
    (hSend : senderTcb.ipcState = .blockedOnSend sendEp) :
    rendezvousDequeuedCall
        (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
          receiverSlotBase executingCore st).1 sender
      = false := by
  have hLeg := endpointReceiveDualOnCore_not_dequeuedCall_of_blockedOnSend endpointId receiver
    replyId executingCore st ep sender senderTcb sendEp hObjInv hEp hHead hTcb hSend
  have hLegInv :
      ((endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1).objects.invExt :=
    endpointReceiveDualOnCore_preserves_objects_invExt endpointId receiver replyId executingCore
      st hObjInv
  unfold endpointReceiveDualWithCapsOnCore
  cases hRecv : endpointReceiveDualOnCore endpointId receiver replyId executingCore st with
  | mk stRecv res =>
      rw [hRecv] at hLeg hLegInv
      cases res with
      | error e => simpa using hLeg
      | ok pair =>
          obtain ⟨senderId, sgi⟩ := pair
          simp only []
          repeat' split
          all_goals
            first
              | simpa using hLeg
              | (rename_i hUnwrap
                 refine (rendezvousDequeuedCall_congr_getTcb? _ stRecv sender ?_).trans hLeg
                 exact ipcUnwrapCaps_getTcb?_eq _ receiverCspaceRoot receiverSlotBase _ stRecv _ _
                   sender hLegInv hUnwrap)

/-- **WS-RR RR8.12**: **the cores whose replenish queue a cross-core receive may
write** — the dequeued donor's home and the receiver's, on a rendezvous, and none
at all when the receive blocks.

The replenish twin of `endpointReceiveDualWriteSet`, and the reason it is a
definition rather than two parameters on the footprint below: *a parameter is a
place for a caller to be wrong.*  The two cores are WS-OD OD3.6's
`applyRendezvousCallDonation` own `determineTargetCore` arguments, and the donation
runs at the *post*-receive-leg state — so a footprint taking them as operands would
let its caller declare locks for a migration between two cores the transition never
touches, and a bracket that must resolve a footprint *before* the transition runs
could not supply them at all.

Read on the **pre**-state, which is sound because the receive leg moves no thread's
home core: `endpointReceiveDualWithCapsOnCore_determineTargetCore_eq_of_rendezvous`
is that fact, and
`endpointReceiveHandoffReplenishCores_of_call_rendezvous` below is this list
*being* the pair the donation resolves.  So this closes, for `.receive`, the
footprint/transition resolution asymmetry WS-HP HP10.8 registered for the reply
arm's origin member rather than adding a second instance of it.

`[]` on the block path is not an economy either: `rendezvousDequeuedCall` is false
for the `.blockedOnReceive` id that path returns, so the arm donates nothing there
and a segment naming two cores would be a footprint wider than its operation —
which this project rates as a real cost, lock contention being an observable
channel (SM8.D's CC-5).

**PR #897 Codex review**: and that reasoning was applied to the block path and not
to its sibling.  The segment keyed on `receiveRendezvousSender?` — *is there a
queued sender at all* — while WS-OD OD3.6's donation fires only on a dequeued
`Call`, so **every ordinary `seL4_Send` rendezvous declared two replenish-queue
write locks for a migration that provably does not happen**: the same
over-declaration the paragraph above rejects, on the more common path.  It keys on
`receiveRendezvousCallSender?` now, whose licence is
`endpointReceiveDualWithCapsOnCore_not_dequeuedCall_of_blockedOnSend` — a plain
`Send` rendezvous leaves the dequeued sender `.ready`, so the post-state guard is
false and the donation step is the identity.

**What this still over-declares, and why it is a separate cut.**  A dequeued `Call`
whose donation prerequisites fail — the receiver already holds a context, or the
sender holds none — migrates nothing either, and the transition's own guard for
that is `callDonationSchedContext?`.  Narrowing on it needs the pre-state answer
transported across the receive leg, which is `sameSchedContextBindings`, and two
things are in the way.  **No** such frame exists for `endpointReceiveDual` or
`endpointReceiveDualWithCaps` at all: the two theorems that need one
(`endpointReceiveDual_preserves_donationBudgetTransfer`,
`endpointReceiveDual_preserves_donationOwnerUnique`) each inline the whole
rendezvous composition, so it has to be extracted — a de-duplication.  And
`IPC/Operations/Donation.lean`'s import closure contains neither
`IPC/Invariant/Defs.lean`, where `sameSchedContextBindings` is declared, nor the
reverse, so a bridge from the frame to `callDonationSchedContext?` has no home
beside the resolver; moving the owner down is this tree's own remedy for that
shape (`v0.35.59`).  What is **not** in the way is reachability: the family's
per-primitive members in `IPC/Invariant/Structural/DualQueueMembership.lean` are
reachable from here (through `EndpointCall`, `PerCoreWake`, the per-core scheduler
chain, `CrossSubsystem` and `IPC.Invariant`), which an earlier draft of this
docstring denied — so the deferral is a placement cost rather than an
impossibility.  It is registered in `docs/REGISTERED_DEBT.md` table C with that
closure. -/
def endpointReceiveHandoffReplenishCores (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) : List CoreId :=
  match receiveRendezvousCallSender? st endpointId with
  | some sender => [determineTargetCore st sender, determineTargetCore st receiver]
  | none        => []

/-- **WS-RR RR8.12**: and on the block path it is empty — a receive that parks
itself donates nothing, so no replenish queue is written and none is declared. -/
theorem endpointReceiveHandoffReplenishCores_of_blocked (st : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (ep : Endpoint)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = none) :
    endpointReceiveHandoffReplenishCores st endpointId receiver = [] := by
  unfold endpointReceiveHandoffReplenishCores
  rw [receiveRendezvousCallSender?_of_blocked st endpointId ep hEp hHead]

/-- **WS-RR RR8.12 (PR #897 Codex review)**: and empty on a plain `Send`
rendezvous — the case this narrowing closes.

The licence is
`endpointReceiveDualWithCapsOnCore_not_dequeuedCall_of_blockedOnSend`: the receive
leg leaves the dequeued sender `.ready`, so `applyReceiveRendezvousDonation` is the
identity (`applyReceiveRendezvousDonation_of_no_call`) and no replenish queue moves.
Declaring two cores there is not conservatism but contention nobody needs. -/
theorem endpointReceiveHandoffReplenishCores_of_blockedOnSend (st : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (ep : Endpoint)
    (sender : SeLe4n.ThreadId) (senderTcb : TCB) (sendEp : SeLe4n.ObjId)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = some sender)
    (hTcb : lookupTcb st sender = some senderTcb)
    (hSend : senderTcb.ipcState = .blockedOnSend sendEp) :
    endpointReceiveHandoffReplenishCores st endpointId receiver = [] := by
  unfold endpointReceiveHandoffReplenishCores
  rw [receiveRendezvousCallSender?_of_blockedOnSend st endpointId ep sender senderTcb sendEp
    hEp hHead hTcb hSend]

/-- **WS-RR RR8.12: the licence.**  On a **`Call`** rendezvous the pre-state reading
**is** the pair of cores WS-OD OD3.6's donation resolves at the state it runs on.

Not "agrees with" and not "over-approximates": the two lists are equal, so the
footprint the RR7.12-style bracket acquires before the transition and the migration
the transition then performs cannot name different cores.  What makes it true is
that nothing in the receive leg writes a `cpuAffinity` — the only field
`determineTargetCore` reads, and one only `.tcbSetAffinity` writes.

**PR #897 Codex review**: `.blockedOnCall` is a hypothesis now rather than a
consequence of the queue being non-empty, and the name says so.  The retired
`_of_rendezvous` spelling held for *every* rendezvous because the segment was
`.blockedOnSend`-blind, which is exactly the over-declaration this cut removes; a
theorem still claiming the equality there would be claiming the footprint names two
cores on a path where it names none.  The plain-`Send` case is
`endpointReceiveHandoffReplenishCores_of_blockedOnSend`. -/
theorem endpointReceiveHandoffReplenishCores_of_call_rendezvous (st : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId)
    (ep : Endpoint) (sender : SeLe4n.ThreadId) (senderTcb : TCB) (callEp : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = some sender)
    (hTcb : lookupTcb st sender = some senderTcb)
    (hCall : senderTcb.ipcState = .blockedOnCall callEp) :
    endpointReceiveHandoffReplenishCores st endpointId receiver
      = [determineTargetCore
             (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
               receiverSlotBase executingCore st).1 sender,
         determineTargetCore
             (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
               receiverSlotBase executingCore st).1 receiver] := by
  have hFrame := endpointReceiveDualWithCapsOnCore_determineTargetCore_eq_of_rendezvous
    endpointId receiver replyId receiverCspaceRoot receiverSlotBase executingCore st ep sender
  unfold endpointReceiveHandoffReplenishCores
  rw [receiveRendezvousCallSender?_of_blockedOnCall st endpointId ep sender senderTcb callEp
    hEp hHead hTcb hCall]
  rw [hFrame sender hObjInv hEp hHead, hFrame receiver hObjInv hEp hHead]

/-- **WS-RR RR8.12**: the scheduler-domain footprint of the live `.receive` arm —
the object-store table write lock, the run-queue write lock of the one core the
receive leg moves, and the replenish-queue write locks of the two endpoints
WS-OD OD3.6's donation migrates between.

**Every core is derived; nothing is a parameter.**  The run segment is
`endpointReceiveDualWriteSet`, which the arm's own SM8.B confinement theorem
`endpointReceiveDualWithCapsOnCore_confinedToCores` is stated at, so the footprint
and the confinement claim cannot name different cores (Cut 7's rule).  The
replenish segment is `endpointReceiveHandoffReplenishCores`, which is the
donation's own pair by theorem.  The remaining arguments are the syscall's own
operands, so a bracket resolving this footprint has everything it needs before the
transition runs — the property WS-HP HP10.8 could not get for the reply arm's
origin member and registered as an asymmetry.

**Dynamic chain extension (declared, not static).** The arm also runs
`applyReceiverPipHandoff`, which re-buckets each blocking-chain member's run
queue on *that member's* home core.  The chain is state-discovered, so no static
footprint can enumerate those cores: `PriorityInheritance.pipChainSchedFootprint`
declares them per walked member, and the SM3.C obligation
`pipChainStart_endpointReceive` is what ties the walk to it.  Every sibling
footprint over an arm that walks a chain carries the identical caveat. -/
def schedLockSet_endpointReceiveOnCore (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (executingCore : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores (endpointReceiveDualWriteSet st endpointId executingCore)
    (endpointReceiveHandoffReplenishCores st endpointId receiver)

-- No `_write_only` / `_pairwise_le` restatement here, and that is deliberate: both
-- are `schedFootprintOfCores_write_only` / `_pairwise_le` applied to this
-- footprint's own arguments, so a consumer reaches for the shared lemma directly.
-- Cut 7's four arm footprints omit them for the same reason; the RR2.4 / RR2.10
-- siblings that carry them predate the shared constructor.

/-- **WS-RR RR8.12**: on the rendezvous path the footprint names the woken
sender's home core — resolved through `receiveRendezvousSender?`, the resolver the
object-domain footprint's own sender member comes from. -/
theorem schedLockSet_endpointReceiveOnCore_contains_sender_runQueue_write (st : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (executingCore : CoreId)
    (sender : SeLe4n.ThreadId)
    (hSender : receiveRendezvousSender? st endpointId = some sender) :
    (SchedLockId.runQueue ⟨determineTargetCore st sender⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_endpointReceiveOnCore st endpointId receiver executingCore := by
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  rw [endpointReceiveDualWriteSet_of_sender st endpointId executingCore sender hSender]
  simp

/-- **WS-RR RR8.12**: and on the block path it names the executing core's, which
the receiver's own deschedule writes.  The two arms are exclusive — a receive
that rendezvouses does not block — so the run segment is one member either
way. -/
theorem schedLockSet_endpointReceiveOnCore_contains_executing_runQueue_write (st : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (executingCore : CoreId)
    (ep : Endpoint) (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = none) :
    (SchedLockId.runQueue ⟨executingCore⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_endpointReceiveOnCore st endpointId receiver executingCore := by
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  rw [endpointReceiveDualWriteSet_of_blocked st endpointId executingCore ep hEp hHead]
  simp

/-- **WS-RR RR8.12**: and a receive that blocks declares no replenish-queue lock at
all — the segment is empty, so the footprint is the table lock and one run queue. -/
theorem schedLockSet_endpointReceiveOnCore_no_replenishQueue_of_blocked (st : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (executingCore : CoreId)
    (ep : Endpoint) (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = none)
    (c : CoreId) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∉ schedLockSet_endpointReceiveOnCore st endpointId receiver executingCore := by
  intro hMem
  have := (mem_schedFootprintOfCores_replenishQueue_iff _ _ c).mp hMem
  rw [endpointReceiveHandoffReplenishCores_of_blocked st endpointId receiver ep hEp hHead] at this
  simp at this

/-- **WS-RR RR8.12 (PR #897 Codex review): the payoff.**  On a plain `Send`
rendezvous the arm's donation step is the **identity**, so it writes no replenish
queue and the empty segment is exact rather than merely narrow.

The composition a bracket consumer cites: the receive leg leaves the dequeued
sender `.ready`, so WS-OD OD3.6's post-state guard is false and
`applyReceiveRendezvousDonation_of_no_call` collapses the step.  Nothing here is a
claim about the *object* domain — the arm still writes the endpoint and the two
TCBs, and `lockSet_endpointReceive` still declares them. -/
theorem applyReceiveRendezvousDonation_eq_self_of_blockedOnSend
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (ep : Endpoint) (sender : SeLe4n.ThreadId) (senderTcb : TCB) (sendEp : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = some sender)
    (hTcb : lookupTcb st sender = some senderTcb)
    (hSend : senderTcb.ipcState = .blockedOnSend sendEp) :
    applyReceiveRendezvousDonation
        (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
          receiverSlotBase executingCore st).1 receiver sender
      = .ok (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
              receiverSlotBase executingCore st).1 :=
  applyReceiveRendezvousDonation_of_no_call _ receiver sender
    (endpointReceiveDualWithCapsOnCore_not_dequeuedCall_of_blockedOnSend endpointId receiver
      replyId receiverCspaceRoot receiverSlotBase executingCore st ep sender senderTcb sendEp
      hObjInv hEp hHead hTcb hSend)

/-- **WS-RR RR8.12 (PR #897 Codex review)**: and the step the live arm actually runs
is the identity too — *a proxy is not the fact*.

`API.lean`'s `.receive` arm runs `applyReceiveRendezvousHandoff`, which is WS-OD
OD3.6's donation **and** OD3.14's priority-inheritance walk under one guard, so the
donation alone is a component rather than the arm's stage.  Both halves are gated on
`rendezvousDequeuedCall`, so on a plain `Send` rendezvous neither fires: the whole
hand-off is the identity, which is stronger than the component fact and is what a
bracket consumer over this arm needs.

(The walk writes run queues rather than replenish queues — declared dynamically
through `PriorityInheritance.pipChainSchedFootprint` — so the *replenish* segment's
own licence is the donation half; this states the arm's step so that neither half
can be read as the other.) -/
theorem applyReceiveRendezvousHandoff_eq_self_of_blockedOnSend
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore handoffCore : CoreId) (st : SystemState)
    (ep : Endpoint) (sender : SeLe4n.ThreadId) (senderTcb : TCB) (sendEp : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = some sender)
    (hTcb : lookupTcb st sender = some senderTcb)
    (hSend : senderTcb.ipcState = .blockedOnSend sendEp) :
    applyReceiveRendezvousHandoff
        (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
          receiverSlotBase executingCore st).1 receiver sender handoffCore
      = .ok (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
              receiverSlotBase executingCore st).1 :=
  applyReceiveRendezvousHandoff_of_no_call _ receiver sender handoffCore
    (endpointReceiveDualWithCapsOnCore_not_dequeuedCall_of_blockedOnSend endpointId receiver
      replyId receiverCspaceRoot receiverSlotBase executingCore st ep sender senderTcb sendEp
      hObjInv hEp hHead hTcb hSend)

/-- **WS-RR RR8.12 (PR #897 Codex review)**: and so the `.receive` footprint declares
**no** replenish-queue lock on a plain `Send` rendezvous — the sibling of
`schedLockSet_endpointReceiveOnCore_no_replenishQueue_of_blocked`, for the path that
used to declare two.

Over-declaring is sound and not free: lock contention is an observable channel
(SM8.D's CC-5), and WS-OD OD3.5 narrowed a footprint for exactly this reason. -/
theorem schedLockSet_endpointReceiveOnCore_no_replenishQueue_of_blockedOnSend
    (st : SystemState) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (executingCore : CoreId) (ep : Endpoint) (sender : SeLe4n.ThreadId)
    (senderTcb : TCB) (sendEp : SeLe4n.ObjId)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = some sender)
    (hTcb : lookupTcb st sender = some senderTcb)
    (hSend : senderTcb.ipcState = .blockedOnSend sendEp) (c : CoreId) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∉ schedLockSet_endpointReceiveOnCore st endpointId receiver executingCore := by
  intro hMem
  have := (mem_schedFootprintOfCores_replenishQueue_iff _ _ c).mp hMem
  rw [endpointReceiveHandoffReplenishCores_of_blockedOnSend st endpointId receiver ep sender
    senderTcb sendEp hEp hHead hTcb hSend] at this
  simp at this

/-- **WS-RR RR8.12 (arm-level coverage)**: the `.receive` footprint covers WS-OD
OD3.6's donation footprint member for member — hence, by
`applyCallDonationOnCoreSchedLockSet_covers_migration`, the SM5.H replenishment
migration's two replenish-queue write locks.

This is the statement that makes the declaration *true* rather than merely
plausible, and it is stated at the cores the donation **actually** resolves, on the
post-receive-leg state it runs on — not at two operands a caller supplied.  A
`withLockSet` bracket over this footprint therefore holds both migration slots.

**PR #897 Codex review**: conditioned on the dequeued sender carrying a `Call`,
because that is the only shape on which the donation migrates anything — and so the
only shape on which there is a migration to cover.  On a plain `Send` rendezvous the
step is the identity
(`endpointReceiveDualWithCapsOnCore_not_dequeuedCall_of_blockedOnSend`) and the
segment is empty (`endpointReceiveHandoffReplenishCores_of_blockedOnSend`), so a
coverage claim there would be covering nothing while reading like coverage. -/
theorem schedLockSet_endpointReceiveOnCore_covers_donation (st : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId)
    (ep : Endpoint) (sender : SeLe4n.ThreadId) (senderTcb : TCB) (callEp : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt)
    (hEp : st.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = some sender)
    (hTcb : lookupTcb st sender = some senderTcb)
    (hCall : senderTcb.ipcState = .blockedOnCall callEp) :
    ∀ p ∈ applyCallDonationOnCoreSchedLockSet
             (determineTargetCore
               (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
                 receiverSlotBase executingCore st).1 sender)
             (determineTargetCore
               (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
                 receiverSlotBase executingCore st).1 receiver),
      p ∈ schedLockSet_endpointReceiveOnCore st endpointId receiver executingCore := by
  refine schedFootprintOfCores_subset (fun _ h => absurd h (by simp)) (fun c hc => ?_)
  rw [endpointReceiveHandoffReplenishCores_of_call_rendezvous st endpointId receiver replyId
    receiverCspaceRoot receiverSlotBase executingCore ep sender senderTcb callEp hObjInv hEp
    hHead hTcb hCall]
  exact hc

end SeLe4n.Kernel
