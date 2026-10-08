-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatch
import SeLe4n.Kernel.IPC.Operations.Donation
import SeLe4n.Kernel.Architecture.SyscallReturn
import SeLe4n.Kernel.Scheduler.Operations

/-!
# The ReplyRecv transition, `endpointReplyRecvOnCore`

The one transition the `.replyRecv` syscall arm runs, in both the checked and the
unchecked dispatch (audit IPC-2, `v0.36.49`).  It composes, in seL4-MCS's
`doReplyTransfer` → `reply_remove` → `receiveIPC` order:

1. the reply leg, `endpointReplyOnCore`;
2. the donation pop, `replyRecvPopDonation`;
3. the capability-installing receive leg, `endpointReceiveDualWithCapsOnCore`,
   which re-links the same Reply object to the next caller;
4. the post-receive donation, `replyRecvPostReceiveDonation`; and
5. the receive leg's priority hand-off, `applyReceiveLegPipHandoff`, then the two
   return-frame stagers.

Until `v0.36.49` the name `endpointReplyRecvOnCore` belonged to a two-leg
composite (reply leg then the bare receive leg) that no syscall arm called, and
the live body was `replyRecvBody` in `API.lean`.  The live body moved here under
the proved name, and the two-leg composite was deleted with the theorems that
were stated only about it, so every theorem that names `endpointReplyRecvOnCore`
is a theorem about the code the syscall executes.

This module holds the operations: the transition, its two donation halves and the
per-core write sets and scheduler footprint that mirror its control flow.  The
proofs are in `IPC/CrossCore/EndpointReplyRecvInvariant.lean`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId
  LockKey)

/-- **WS-RM (`v0.35.6`): the pop half**, and the half that must run *before* the
receive leg.

seL4-MCS's `doReplyTransfer` calls `reply_remove` — which on a stack **head** is
`reply_pop`: it hands the scheduling context back and takes the frame off the
stack — and only then does `receiveIPC` run.  This kernel ran the whole donation
resolution *after* both legs, and that order is not merely unfaithful: the
receive leg re-links the very Reply the reply leg just answered, and
`Reply.consumed` keeps a head's stack links deliberately (the pop validates the
head by them), so `Reply.isFree` was false and `linkReply` / `replyStashValid`
both refused with `.replyCapInvalid`.  A passive server whose client donated its
scheduling context — the MCS steady state — could therefore never complete a
`seL4_ReplyRecv`.

Splitting the resolution at the point where it stops depending only on the reply
leg is what fixes that: the return needs nothing the receive leg establishes,
while the re-donation needs the thread the receive leg dequeued.  The returned
context is handed on so the post-receive half knows which arm it is on without
re-reading a binding this step has already cleared.

`returnDonatedSchedContextResolved` resolves the new owner off the context's own
reply stack, on this hop's pre-state — which is the pop's own pre-state, since
nothing runs between the two.  At depth 1 the stack is empty and the resolver
answers `none`, so that call is the pre-OD4 body verbatim
(`returnDonatedSchedContextResolved_eq_legacy_of_no_stack`).

WS-RR RR2.20: the return moves the context's binding from its holder to the
answered caller, so its pending CBS replenishments must follow (SM5.H.4).  Both
endpoints are read from this hop's **pre**-state, which is sound because
`returnDonatedSchedContextValid` never writes a `cpuAffinity`
(`returnDonatedSchedContext_getTcb?_cpuAffinity_eq`).

**WS-HP HP4.5: this pop is head-driven too, and it has to be.**  The `.reply`
arm's pop reads the answered frame (`replyFrameHeadHolder?`); leaving this one
reading the recorded server's `.donated` binding would be one question answered
two ways on the two arms that ask it, and the two answers diverge on exactly the
state HP6 creates.  Here the frame needs no resolving: `rid` **is** the reply
capability the arm was invoked with, and `target` is the caller it answers, so
this arm is cleaner than `.reply`'s — which has to recover the frame from
`answeredReplyObject?` because its dispatch does not carry the capability.

Two arms rather than four, and what they mean changed: a frame heading no
scheduling context is the identity (where the binding reading said "this server
holds no donation"), and a holder or caller that will not promote to a
`ValidThreadId` is `.invalidArgument`.  The pre-HP4.5 `.objectNotFound` arm — an
unresolvable recorded server — is gone with the lookup it guarded; it was
unreachable, since the recorded server defaults to the invoking receiver, whose
TCB exists by the time the reply leg has succeeded.

**The result carries the HOLDER, and that is the whole of PR #897's second
finding.**  What this pop makes `.unbound` is the answered frame's head context's
own `boundThread`; what the post-receive half descheduled was
`recordedReplyServer?`, the server the answered caller recorded when it *Called*.
HP4.5 above repointed the **trigger** onto the frame and left the **deschedule**
on the binding-era proxy, and HP6.8's splice is what makes the two disagree: a
spliced middle caller leaves an orphan head, so the context's bound thread is no
longer the thread the caller recorded.  Measured on the live body — the holder
ended `.unbound` and still queued (`hasSufficientBudget` is unconditionally `true`
for an unbound thread, so it runs at its legacy TCB band charged to no
reservation), while an unrelated thread that still held its own reservation was
taken off its run queue and left `.ready`, which OD1.7 enumerates as
unrecoverable.  So the pair travels with the arm selector rather than beside it:
one `Option`, so a consumer cannot hold the context and the holder apart and pass
a different thread to the deschedule than the one this pop unbound.

The `.reply` arm's two pops (`applyReplyDonation`, `applyReplyDonationOnCore`)
have always descheduled `holder`; this is the fourth site of the same question,
and it was the only one answering it with a proxy. -/
def replyRecvPopDonation (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId) :
    Kernel (Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) :=
  fun st =>
    match replyFrameHeadHolder? st rid with
    | some (oldScId, holder) =>
        -- The two `toValid?` matches are the sentinel refusals and nothing
        -- else: after them the pop and the migration read `holder` and
        -- `target` themselves (`v0.35.61` -- the return took `holderV.val` and
        -- the migration `holder`, one thread under two spellings, and every
        -- proof over this step carried a `toValid?_some_val_eq` rewrite to
        -- reconcile them).
        match holder.toValid?, target.toValid? with
        | some _, some _ =>
            -- **WS-HP HP10.7**: the recipient at the bottom of the stack is the
            -- reservation's recorded origin, and the migration's DESTINATION is
            -- that thread's home core rather than the answered caller's.  Both
            -- read `replyDonationRecipient`, which is the identity wherever no
            -- origin is recorded -- so this is the pre-HP10.7 body verbatim on
            -- every state before HP10.4 recorded one.  `oldScId` is in scope
            -- here, so these are the same expressions the live `.reply` spine
            -- resolves through `replyDonationRecipientHome`
            -- (`replyDonationRecipientHome_of_head` is the tie).  One binding,
            -- because "which thread receives the context" is one question and
            -- the return and the migration must not be free to answer it twice.
            let recipient := replyDonationRecipient st oldScId target
            match returnDonatedSchedContextResolved st holder oldScId recipient with
            | .error e => .error e
            | .ok st1' =>
                .ok (some (oldScId, holder), migrateSchedContextReplenishment st1' oldScId
                  (determineTargetCore st holder)
                  (determineTargetCore st recipient))
        | _, _ => .error .invalidArgument
    | none => .ok (none, st)

/-- The deschedule of the thread the pop unbound, on the Call arm of
`replyRecvPostReceiveDonation`.

The pop has already returned that thread's donated context, so it is passive
unless the receive leg hands it a new one — and the new one goes to the
**receiver** `tid`.  So this is the identity when the holder *is* the receiver
(it keeps running on the new request's budget) and a real deschedule otherwise,
where the holder would stay queued while `.unbound` and run at its legacy TCB
priority charged to no reservation (PR #895 review round 8).

**The argument is the HOLDER, not `recordedReplyServer?`** (PR #897 review).  Both
were `recordedServer` until then, which is the thread the answered caller recorded
when it *Called* — a proxy for the thread the pop unbounds, and one HP6.8's splice
falsifies: an orphan head leaves the context bound to a thread the caller never
recorded.  Measured on the live body, that descheduled a bystander still holding
its own reservation (stranding it `.ready` off every queue) while leaving the
actual holder runnable and unbudgeted.  The holder now arrives inside the arm
selector `replyRecvPopDonation` returns, so no caller can supply a different
thread.  The two coincide on every non-delegated reply, which is why this is the
identity there (`replyRecvHolderDeschedule_eq_of_holder_eq_recordedServer`).

Named rather than inlined so the relation has one spelling and its own frames:
the two facts its consumers need are stated directly below each of them.

**It resolves its own core** (PR #895 review round 10).  The first cut took the
`serverCore` the caller had already computed, which is
`determineExecutingCore st recordedServer` — a core the server is *current* on,
falling back to `bootCoreId`.  A server that is queued rather than running
matches that nowhere, so the deschedule edited the boot core's queue while the
server sat on another, and the temporal-isolation defect this step exists to
close survived untouched on exactly the preempted case.  `determineTargetCore`
is no better: `affinityAdmitsCore` is `true` on every core for an unpinned
thread, so an unpinned server may legitimately sit on any queue while that
resolver answers `bootCoreId`.

Both are *proxies*; the fact a removal is about is where the thread is placed,
and `placedCoreOf?` is that witness.  Taking it as a parameter is what let a
core computed for the priority-inheritance walk decide a run-queue removal, so
the parameter is gone — a caller cannot pass the wrong core to a function that
does not accept one. -/
def replyRecvHolderDeschedule (tid holder : SeLe4n.ThreadId)
    (st : SystemState) : SystemState :=
  if holder = tid then st
  else descheduleAtPlacement st holder

/-- **WS-RM (`v0.35.6`): the post-receive half** — everything the donation
resolution cannot decide until the receive leg has run.

`returned?` is the **(context, holder)** pair `replyRecvPopDonation` handed back,
and it is passed rather than re-derived because the pop has already cleared the
binding that used to select this arm: reading it here would put every reply on the
never-donated path.

* If the receive rendezvoused with a **Call** — `nextThread` is now
  `.blockedOnReply`, a freshly dequeued request whose donation the queued `Call`
  deferred — the new client's context is donated to the **receiver** `tid`
  (`applyRendezvousCallDonation`, the step `.receive` performs too, WS-OD OD3.6),
  so a receiver that is itself the holder keeps running on the new request's
  budget; that donation migrates its own replenishments.  **When the holder is not
  `tid`** it receives nothing here — so it is descheduled on this arm too, exactly
  as on the one below.
* Otherwise (a plain `Send` rendezvous, or the server blocked with no waiter) the
  now-passive **holder** is descheduled at its placement.

A reply that popped **no** context needs no donation change — the run-queue state
is left to the receive leg.  Every arm reverts the reply leg's
priority-inheritance boost through the cross-core chain walk from
`recordedServer`.

**Two threads, two questions** (PR #897 review).  `recordedServer` is
`recordedReplyServer?` of the answered caller — the thread it recorded when it
*Called* — and it is the right start for the **chain walk**, which keys on
waiters rather than on donations (WS-HP HP7 kept that resolver for exactly this).
It is the **wrong** thread to deschedule: what the pop unbounds is the answered
frame's head context's `boundThread`, and HP6.8's splice makes the two differ on
reachable states.  Both deschedule arms therefore name the holder the pop
returned and both walks keep `recordedServer`; the two coincide on every
non-delegated reply, so this is the pre-fix body verbatim there. -/
def replyRecvPostReceiveDonation (tid recordedServer : SeLe4n.ThreadId)
    (nextThread : SeLe4n.ThreadId) (serverCore : Concurrency.CoreId)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) : Kernel Unit :=
  fun st =>
    match returned? with
    | none =>
        .ok ((), (PriorityInheritance.propagatePipChainCrossCore st recordedServer serverCore).1)
    | some (_, holder) =>
        if rendezvousDequeuedCall st nextThread then
            -- New Call: donate to the RECEIVER `tid`, not the (possibly delegated)
            -- recorded server.  WS-RR RR2.20: via the cross-core form, so the new
            -- client's replenishments migrate to the receiver's home core as well.
            --
            -- **...and `tid` IS the HOLDER only when the pop unbound the receiver
            -- itself** (PR #895 review round 8, re-keyed at PR #897's).  Where the
            -- two differ the holder receives nothing here, and the pop has already
            -- made it `.unbound` — so leaving it queued would run it at its legacy
            -- TCB priority charged to no reservation, which is WS-OD OD3.6's
            -- defect on the delegated path.  `passiveServerIdle` cannot see it:
            -- that conjunct is conditioned on the thread already being
            -- descheduled, so an unbound thread that is still queued satisfies it
            -- vacuously.
            --
            -- The deschedule runs on the PRE-donation state, because it is a
            -- consequence of the pop rather than of the new donation, and
            -- `removeRunnableOnCore` writes no object — so every object-level
            -- fact the donation needs transports across it unchanged.
            match applyRendezvousCallDonation
                (replyRecvHolderDeschedule tid holder st) tid nextThread with
            | .error e => .error e
            | .ok st2 =>
                .ok ((), (PriorityInheritance.propagatePipChainCrossCore st2 recordedServer serverCore).1)
        else
            -- **The same deschedule, resolved the same way** (PR #895 review
            -- round 11).  This arm passed `serverCore` — which `endpointReplyRecvOnCore`
            -- then computed as a core the server is *current* on, else the
            -- boot core (a resolver since deleted) — so a server preempted
            -- on a non-boot queue was removed from a queue it was not on and
            -- stayed runnable while `.unbound`.  Round 10 removed that proxy
            -- from the sibling arm above and left this one, because the fix
            -- protected a named wrapper while `removeRunnableOnCore` still
            -- accepted a core from anyone.  Both arms call one step now.
            --
            -- **...and on the HOLDER** (PR #897 review): the thread this arm
            -- makes passive is the one the pop unbound, and `recordedServer` is
            -- a *different* thread on an orphan head.  Descheduling it stranded a
            -- bystander that still held its own reservation while the real holder
            -- stayed runnable and unbudgeted.  The walk below still starts at
            -- `recordedServer`, because that one keys on waiters.
            .ok ((), (PriorityInheritance.propagatePipChainCrossCore
              (descheduleAtPlacement st holder) recordedServer serverCore).1)

/-- **WS-RM RM5.2**: the state `.replyRecv`'s receive leg runs on — the reply
leg's committed state with the donation pop applied.

A *total* accessor over `replyRecvPopDonation`, so a hypothesis about the receive
leg's pre-state is a flat pre-state-computable expression rather than a
quantification nested under the pop's own success.  The refusal arm answers the
unpopped state, which is sound because the arm has already returned `.error`
there and the receive leg never runs: a hypothesis stated at that value is an
obligation with no consumer, never a claim about a state the kernel reaches
(`replyRecvPostPopState_eq_of_error`).

Derived from the transition rather than restated, so the accessor and the step
cannot disagree about which state the receive leg sees. -/
def replyRecvPostPopState (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId)
    (st1 : SystemState) : SystemState :=
  match replyRecvPopDonation rid target st1 with
  | .error _ => st1
  | .ok (_, st1p) => st1p

/-- **WS-RM RM5.2**: the donation the pop handed back — the scheduling context
**and the thread it unbound** — as a total accessor.  `none` on the refusal arm
for the reason above: the post-receive step never runs there.

Renamed from `replyRecvPoppedDonation` at PR #897's review, with the pair the pop
now returns: an accessor called "context" that answers a `(context, holder)` pair
is a name that no longer describes what it is, and the holder is the load-bearing
half — it is the thread the post-receive half deschedules. -/
def replyRecvPoppedDonation (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId)
    (st1 : SystemState) : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId) :=
  match replyRecvPopDonation rid target st1 with
  | .error _ => none
  | .ok (returned?, _) => returned?

/-- WS-SM SM6.D (faithful seL4-MCS `ReplyRecv`): the *unchecked* reply-and-receive
body, shared by both dispatch arms (so the checked arm = a flow-gated wrapper over
exactly this).  Steps reusing the verified cross-core transitions:
1. **reply leg** — `endpointReplyOnCore` delivers to `prevCaller` (the recorded
   caller) and, **atomically with the delivery** (PR #827 review #3 fold), tears
   the answered frame off its reply stack and down the reply link
   (`removeCallerReplyFrame`, keyed on the caller's own `replyObject` — the
   single-use barrier).  The PIP reversion and the *deschedule* are deferred to
   step 4 — descheduling the server *before* the receive leg would leave a server
   that immediately rendezvouses with a queued `Call` stuck `.ready` but absent
   from the run queues (PR #822 review, 6J90-w);
2. **donation pop** — `replyRecvPopDonation` hands the old client's SC back.
   **WS-RM (`v0.35.6`) moved it here, between the legs**, which is seL4-MCS's own
   order: `doReplyTransfer` calls `reply_remove` — on a stack head, `reply_pop` —
   before `receiveIPC`.  It has to be here: the receive leg below re-links the
   very Reply `rid` the reply leg just answered, and a frame that *heads* a
   scheduling context keeps its stack links when its caller is consumed
   (`Reply.consumed`, deliberately — the pop validates the head by them), so
   `Reply.isFree` is false until this step takes it off;
3. **receive + re-link leg** — `endpointReceiveDualWithCapsOnCore … (some rid)`
   receives the next message, **installs the capabilities it carries** into the
   server's own CSpace, and, on a `Call` rendezvous, links the *same* freed reply
   object to the next caller atomically (#7.2 fold — faithful one-object reuse,
   formerly the separate `linkReceivedCaller` step);
4. **post-receive donation** — `replyRecvPostReceiveDonation` donates the new
   client's SC when a new `Call` rendezvoused, so the passive server keeps running
   on the new request's budget (seL4-MCS SC-follows-message), deschedules the
   server when nothing rendezvoused and it gave its context back, and always
   reverts the recorded server's priority-inheritance chain.

**The receive leg installs, and why it must** (PR #873 round 7).  It ran the
*bare* per-core receive until this cut, so a capability-bearing sender that parked
before the server invoked `.replyRecv` had its message moved across wholesale and
its capabilities dropped — while a sender that arrived *after* the server blocked
took the WithCaps send path and had them installed.  That is exactly the
arrival-order dependence the `.receive` arms shed one round earlier, surviving in
the one arm that is a receive without being spelled `.receive`.  A server loop
written the seL4-MCS way (`Recv` once, then `ReplyRecv` forever) would have
received capabilities on its first request and silently none afterwards.

The authority is the sender's, carried on the message (`IpcMessage.capsGranted`),
so both orderings ask the same question.  The summary is **returned** rather than
staged here, because the arm owns the return frame — `.replyRecv`'s `extraCaps`
is now the honest installed count instead of a hardcoded zero. -/
def endpointReplyRecvOnCore (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : Concurrency.CoreId)
    : Kernel CapTransferSummary :=
  fun st =>
    -- WS-SM SM6.D (PR #822 review): capture the recorded server (the passive server
    -- `prevCaller` donated its SC to) and its home core BEFORE the reply leg consumes
    -- `prevCaller.blockedOnReply` — on a delegated reply cap this differs from the
    -- receiver `tid`, and the OLD donation return must key on it (not on `tid`).
    let recordedServer := (recordedReplyServer? st prevCaller).getD tid
    match endpointReplyOnCore tid prevCaller msg executingCore st with
    | (_, .error e) => .error e
    | (st1, .ok _replySgi) =>
        -- **WS-RM (`v0.35.6`): the pop runs here, between the legs** — seL4-MCS's
        -- own order, where `doReplyTransfer` calls `reply_remove` (on a stack head,
        -- `reply_pop`) before `receiveIPC`.  It must: the receive leg below re-links
        -- the very Reply `rid` the reply leg just answered, and a frame that heads a
        -- scheduling context keeps its stack links when its caller is consumed
        -- (`Reply.consumed`, deliberately — the pop validates the head by them), so
        -- `Reply.isFree` is false until this step takes it off.  With the pop last,
        -- `linkCallerReply` and the server-first stash both refused
        -- `.replyCapInvalid` and no passive server whose client had donated could
        -- ever complete a `seL4_ReplyRecv`.
        -- **WS-HP HP4.5**: keyed on the frame the reply capability names and the
        -- caller it answers, so this arm and the `.reply` arm ask one question.
        match replyRecvPopDonation rid prevCaller st1 with
        | .error e => .error e
        | .ok (returnedSc?, st1p) =>
        -- WS-RA RA.B.5b: capture the send-queue head the receive leg will
        -- dequeue (from `st1p`, the state that leg runs on) — a *plain* sender
        -- completing there is owed the unit success frame; a `Call` sender
        -- lands `.blockedOnReply` and the completion stager's guard skips it.
        let wokenSender? := (st1p.getEndpoint? epId).bind (·.sendQ.head)
        -- WS-SM SM6.D (#7.2 fold): the receive leg links the *same* reply object
        -- `rid` (freed by the reply leg's folded consume — PR #827 review #3, and
        -- taken off its reply stack by the pop above — WS-RM) to the next `Call`
        -- caller atomically — faithful one-object reuse, formerly the separate
        -- `linkReceivedCaller nextThread (some rid)` dispatch step.
        match endpointReceiveDualWithCapsOnCore epId tid (some rid) receiverCspaceRoot
            receiverSlotBase executingCore st1p with
        | (_, .error e) => .error e
        | (st2, .ok (nextThread, summary, _)) =>
            -- The return donation's chain walk is told the core THIS syscall
            -- runs on, which is what its SGI decision is relative to ("is the
            -- boosted holder's home core remote?").  It used to be told
            -- `determineExecutingCore st recordedServer`, a core the server is
            -- *current* on or else the boot core: a wrong reference for that
            -- question, and the boot-core fallback this cut retired.  The walk's
            -- state is independent of the core
            -- (`propagatePipChainCrossCore_state_core_independent`).
            match replyRecvPostReceiveDonation tid recordedServer nextThread executingCore
                returnedSc? st2 with
            | .error e => .error e
            | .ok ((), st3) =>
                -- WS-RA RA.B.5b: stage the reply leg's woken caller
                -- (`prevCaller`, `.ready` with the reply in `pendingMessage` —
                -- `.call`'s frame, delivered entirely through this path) and
                -- the receive leg's completed plain sender (unit frame).  Both
                -- stagers are guard-inert when their target was not woken.
                -- Installed count 0 *for `prevCaller`*: the reply message is
                -- built `caps := #[]` by both `.reply`-shaped arms and the
                -- reply path runs no unwrap (PR #866 round-2).  The receive
                -- leg's own count is the returned `summary`, staged by the arm.
                -- **WS-OD OD3.14: the receive leg's priority hand-off.**  The
                -- return donation's walk starts at `recordedServer`, which is the
                -- receiver `tid` on every NON-delegated reply and covers both
                -- legs there; on a *delegated* one they differ and the receiver
                -- has just completed a rendezvous, so `blockingServer` does not
                -- relate them and the reply leg's walk never reaches `tid`.  The
                -- newly dequeued caller's priority would be lost exactly as it
                -- was on `.receive` before OD3.14 -- the same defect at a sibling
                -- site.  Gated on the equality that makes the earlier walk BE
                -- this one, so the non-delegated arm is unchanged.
                .ok (summary, Architecture.stageWokenSendCompletion
                          (Architecture.stageDeliveredMessage
                            (applyReceiveLegPipHandoff st3 tid nextThread recordedServer
                              executingCore)
                            prevCaller 0)
                          wokenSender?)


-- ============================================================================
-- WS-RR RR8.12 Cut 8b: the `.replyRecv` arm's per-core write sets
-- ============================================================================
--
-- Relocated from the STAGED `InformationFlow/NonInterferenceCrossCore.lean` at
-- `v0.35.145`, beside the transitions they describe.  A write set declared in a
-- staged module is one a **production** scheduler-domain footprint cannot read,
-- and Cut 7's rule is that an arm's footprint is `schedFootprintOfCores` of the
-- arm's own SM8.B write set rather than of a second resolution of the same cores
-- -- so the footprint and the confinement claim cannot name different cores.
-- That is the same layering correction Cuts 5 and 7 made four times over: *when a
-- question has one owner and an asker that cannot see it, the owner is in the
-- wrong layer.*  The CONFINEMENT theorems stay in the staged module, because
-- `observableSlotsConfinedToCores` is its predicate.
--
-- They keep the `SeLe4n.Kernel` namespace they were declared in, so the move
-- renames nothing and every reference in the tree is untouched.

/-- SM8.B.2: the tail the post-receive half's non-rendezvous arm takes —
deschedule the now-passive **holder** at its placement, then revert the
**recorded server's** chain from the post-deschedule state.

Two threads, because the arm performs two steps that ask different questions
(PR #897 review): the deschedule is about the thread the pop unbound and the walk
about the thread the answered caller recorded.  A write set that named one thread
for both would be false of exactly the orphan head HP6.8's splice produces. -/
def replyRecvDescheduleAndWalkWriteSet (holder recordedServer : SeLe4n.ThreadId)
    (serverCore : Concurrency.CoreId) (st : SystemState) : List Concurrency.CoreId :=
  -- The deschedule's cores come from the SAME resolver the step uses, not from
  -- `serverCore`: this arm removed the server at `determineExecutingCore`'s
  -- answer until round 11, so the footprint named a core the transition did not
  -- write and omitted the one it did.
  descheduleAtPlacementCores st holder
    ++ pipChainWriteSet (descheduleAtPlacement st holder)
      recordedServer serverCore
      (descheduleAtPlacement st holder).objectIndex.length
/-- **PR #895 review round 8**: the cores `replyRecvHolderDeschedule` may write.

None when the holder *is* the receiver, where the step is the identity because
the receiver keeps the new request's budget; the holder's own placement
otherwise, where it is a real deschedule.  Keyed on the holder since PR #897's
review, with the step it mirrors. -/
def replyRecvHolderDescheduleWriteSet (tid holder : SeLe4n.ThreadId)
    (st : SystemState) : List Concurrency.CoreId :=
  if holder = tid then []
  else descheduleAtPlacementCores st holder
/-- SM8.B.2 / WS-RR RR2.20 / **WS-RM (`v0.35.6`)**: **the cores the post-receive
half may write**, mirroring its own control flow.  Three shapes: the
never-donated arm walks the chain from its pre-state; the rendezvous arm donates
(per-core silent) and walks from the post-donation state; the remaining arm
deschedules the recorded server on its own core first.  The fail-closed arm
produces no post-state at all, so its entry is `[]` and the confinement theorem's
hypothesis rules it out.

The arm is selected by `returned?` — the context the pop handed back — rather
than by re-reading a binding the pop has already cleared, which is the same
reason the transition takes it as an argument. -/
def replyRecvPostReceiveDonationWriteSet (tid recordedServer nextThread : SeLe4n.ThreadId)
    (serverCore : Concurrency.CoreId)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (st : SystemState) : List Concurrency.CoreId :=
  match returned? with
  | none => pipChainWriteSet st recordedServer serverCore st.objectIndex.length
  | some (_, holder) =>
      if rendezvousDequeuedCall st nextThread then
        match applyRendezvousCallDonation
            (replyRecvHolderDeschedule tid holder st) tid nextThread with
        | .error _ => []
        | .ok st2 =>
            -- The deschedule's cores come FIRST, because it runs first: the
            -- holder is taken off its own core before the new client's context
            -- is donated to the invoker (PR #895 review round 8).  A footprint
            -- that omitted them would be false of exactly that arm.
            replyRecvHolderDescheduleWriteSet tid holder st ++
              pipChainWriteSet st2 recordedServer serverCore st2.objectIndex.length
      else replyRecvDescheduleAndWalkWriteSet holder recordedServer serverCore st
/-- SM8.B.2: **the cores the live `.replyRecv` may write** — the answered
caller's home core, the receive leg's set at the reply's post-state, the
donation leg's set at the receive's post-state, and (**WS-OD OD3.14**) the
receive leg's priority hand-off at the donation return's post-state. Each leg is
read at the state that leg actually runs at, which is the discipline
`endpointCallDispatchChainWriteSet` established: reading a later leg at `st`
would name a different chain.

The fourth leg is empty on every **non-delegated** reply, because there the
donation return's own walk already started at the receiver and OD3.14's gate
makes this step the identity — so no pin taken against the three-leg set moves
on any state a non-delegated `.replyRecv` reaches. -/
def endpointReplyRecvWriteSet (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : Concurrency.CoreId) (st : SystemState) : List Concurrency.CoreId :=
  determineTargetCore st prevCaller ::
    (match endpointReplyOnCore receiver prevCaller msg executingCore st with
     | (_, .error _) => []
     | (st1, .ok _) =>
        -- **WS-RM (`v0.35.6`)**: the pop runs between the legs and writes no core
        -- (`replyRecvPopDonation_confinedToCores`), so it contributes nothing here
        -- — but the states the later legs branch on are its post-state, and a
        -- write set that mirrors a transition has to read the states it reads.
        -- **WS-HP HP4.5**: keyed on the frame and the answered caller, as the
        -- transition is.
        (match replyRecvPopDonation replyId prevCaller st1 with
         | .error _ => []
         | .ok (returnedSc?, st1p) =>
            endpointReceiveDualWriteSet st1p endpointId executingCore ++
              (match endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId)
                  receiverCspaceRoot receiverSlotBase executingCore st1p with
               | (_, .error _) => []
               | (st2, .ok (nextThread, _, _)) =>
                  replyRecvPostReceiveDonationWriteSet receiver
                    ((recordedReplyServer? st prevCaller).getD receiver) nextThread
                    executingCore returnedSc? st2 ++
                    (match replyRecvPostReceiveDonation receiver
                        ((recordedReplyServer? st prevCaller).getD receiver) nextThread
                        executingCore
                        returnedSc? st2 with
                     | .error _ => []
                     | .ok (_, st3) =>
                        receiveLegPipHandoffWriteSet st3 receiver nextThread
                          ((recordedReplyServer? st prevCaller).getD receiver) executingCore))))

-- ============================================================================
-- WS-RR RR8.12 Cut C2 (`v0.35.162`): the `.replyRecv` arm's scheduler-domain footprint
-- ============================================================================
--
-- The arm performs up to THREE SchedContext hand-offs, each migrating a
-- reservation's CBS replenishments between two cores: the pop between the reply
-- leg and the receive leg (`replyRecvPopDonation`, WS-RM), the pre-receive return on
-- the receive leg's block path (`cleanupPreReceiveDonationMigrated`, `v0.35.161`),
-- and the re-donation to the receiver when the receive leg dequeues a `Call`
-- (`replyRecvPostReceiveDonation`, WS-RR RR2.20).  The replenish segment below
-- mirrors the spine exactly, the way `endpointReplyRecvWriteSet` mirrors it for the run
-- segment: each hand-off is read AT THE STATE IT RUNS ON, through ITS OWN arm
-- selector -- the pop's frame trigger `replyFrameHeadHolder?` (the answer its
-- `returned?` carries, `replyRecvPopDonation_holder_eq_frameHead`), the block path's
-- `receivePreReturn?`, the re-donation's `callDonationSchedContext?` -- so the
-- footprint and the transition
-- cannot disagree about which cores a hand-off moves between.  Nothing is a
-- parameter, and no core is resolved a second way: every reading is one the
-- transition itself performs.
--
-- Why this arm could not take the `.receive` footprint's pre-state form: the pop
-- rewrites the receiver's binding between the reply leg and the receive leg, so a
-- pre-state reading of the receive leg's donation guard would be a proxy for the
-- guard the transition reads two legs later (*a proxy is not the fact*).  Reading
-- each leg at its own state is what `endpointReplyRecvWriteSet` has done since SM8.B.2,
-- and it is what WS-HP HP10.8 registered the reply arm's ORIGIN member for lacking;
-- this footprint has no such asymmetry, because its resolution and the
-- transition's are the same computation.
--
-- The two chain walks -- the reversion from the recorded server inside
-- `replyRecvPostReceiveDonation` and the receive leg's hand-off
-- (`applyReceiveLegPipHandoff`, WS-OD OD3.14) -- are in the RUN segment, not left
-- to the dynamic extension: `endpointReplyRecvWriteSet` re-runs the spine to the state
-- each walk starts from and appends `pipChainWriteSet` there, so every run queue
-- either walk re-buckets is a static member, bounded by the object count rather
-- than by a constant (a `LockSet` carries no cardinality bound).  What the
-- `pipChainStart_replyRecv*` obligations still add, through
-- `PriorityInheritance.pipChainSchedFootprint`, is the object domain's per-member
-- TCB write lock, which no scheduler footprint can name.  (`v0.35.162` recorded
-- the walks as "declared dynamically"; Cut C3a corrects that here and in the prose
-- that repeated it -- the `.call` and `.reply` write sets carry their walks the
-- same way.)

-- **WS-RR RR8.12 Cut C3a (`v0.35.163`)**: `replyRecvPopReplenishCores` -- the pop's
-- pair keyed on the `returned?` the pop answers -- is retired for the frame-keyed
-- `replyDonationReturnReplenishCores` (`IPC/CrossCore/EndpointReplyDispatch.lean`
-- §1), one owner for both reply-shaped arms: the `.reply` dispatch's return reads
-- the same trigger at the same state, and `replyRecvPopDonation_holder_eq_frameHead`
-- / `replyRecvPopDonation_ok_none_frameHead` are what say the pop's `returned?` IS
-- that trigger's answer.  Two spellings of one pair held together by a theorem is
-- the duplication this project retires.

/-- **WS-RR RR8.12 Cut C2**: the replenish-queue cores the post-receive half
migrates between -- the dequeued caller's home and the receiver's, when the pop
handed a context back AND the receive leg dequeued a `Call` AND the donation's own
resolver answers `some` at the state the donation runs on (the post-deschedule
state, which is scheduler-only relative to the receive leg's post-state).  Every
other arm migrates nothing: the never-donated arm walks the chain only, and the
non-`Call` arm deschedules and walks.

The three-way gate is the transition's own, clause for clause
(`replyRecvPostReceiveDonation`): a footprint keyed on fewer conditions would
declare two replenish locks for a migration that does not happen, and lock
contention is an observable channel (SM8.D's CC-5). -/
def replyRecvPostReceiveReplenishCores (tid nextThread : SeLe4n.ThreadId)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (st : SystemState) :
    List Concurrency.CoreId :=
  match returned? with
  | none => []
  | some (_, holder) =>
      if rendezvousDequeuedCall st nextThread then
        rendezvousCallDonationReplenishCores (replyRecvHolderDeschedule tid holder st)
          tid nextThread
      else []

/-- **WS-RR RR8.12 Cut C2**: the replenish-queue cores the live `.replyRecv` may
write, mirroring the arm's own control flow -- the pop's pair at the reply leg's
post-state, the receive leg's block-path return at the pop's post-state, and the
post-receive half's re-donation at the receive leg's post-state.  Each leg is read
at the state that leg actually runs at, which is the discipline
`endpointReplyRecvWriteSet` established for the run segment: reading a later leg at
`st` would name a different pair.

A failed leg contributes nothing, because the body then commits nothing and there
is no migration to cover. -/
def replyRecvHandoffReplenishCores (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : Concurrency.CoreId) (st : SystemState) : List Concurrency.CoreId :=
  match endpointReplyOnCore receiver prevCaller msg executingCore st with
  | (_, .error _) => []
  | (st1, .ok _) =>
      match replyRecvPopDonation replyId prevCaller st1 with
      | .error _ => []
      | .ok (returnedSc?, st1p) =>
          replyDonationReturnReplenishCores st1 replyId prevCaller ++
            (receivePreReturnReplenishCores st1p endpointId receiver ++
              (match endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId)
                  receiverCspaceRoot receiverSlotBase executingCore st1p with
               | (_, .error _) => []
               | (st2, .ok (nextThread, _, _)) =>
                  replyRecvPostReceiveReplenishCores receiver nextThread returnedSc? st2))

/-- **WS-RR RR8.12 Cut C2**: the scheduler-domain footprint of the live `.replyRecv`
arm -- the object-store table write lock, the run-queue write locks of
`endpointReplyRecvWriteSet` (the arm's own SM8.B write set, which its confinement
theorem `endpointReplyRecvOnCore_confinedToCores` is stated at, so the footprint and the
confinement claim cannot name different cores -- Cut 7's rule), and the
replenish-queue write locks of `replyRecvHandoffReplenishCores`.

**Every core is derived; nothing is a parameter.**  The remaining arguments are the
syscall's own operands, so a bracket resolving this footprint has everything it
needs before the transition runs.  Inert until the bracket cut, like every sibling.

The three hand-offs are covered by theorem, each at the cores the migration
actually resolves on the state it runs on
(`schedLockSet_endpointReplyRecvOnCore_covers_pop`, `…_covers_preReturnMigration`,
`…_covers_postReceiveDonation`); and where no hand-off fires the segment is empty
(`…_no_replenishQueue_of_no_donation`) and the transition writes no replenish queue
(`endpointReplyRecvOnCore_replenishQueueOnCore_of_no_donation`), so the declaration is exact
in both directions on that shape.  The run segment's coverage is
`endpointReplyRecvOnCore_confinedToCores`, stated at the same list. -/
def schedLockSet_endpointReplyRecvOnCore (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : Concurrency.CoreId) (st : SystemState) :
    List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores
    (endpointReplyRecvWriteSet endpointId receiver replyId prevCaller msg receiverCspaceRoot
      receiverSlotBase executingCore st)
    (replyRecvHandoffReplenishCores endpointId receiver replyId prevCaller msg
      receiverCspaceRoot receiverSlotBase executingCore st)

-- No `_write_only` / `_pairwise_le` restatement here, and that is deliberate: both
-- are `schedFootprintOfCores_write_only` / `_pairwise_le` applied to this
-- footprint's own arguments, so a consumer reaches for the shared lemma directly.


end SeLe4n.Kernel
