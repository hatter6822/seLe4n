-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE

  STATUS: staged
-/
import SeLe4n.Kernel.Concurrency.Locks.Deadlock
import SeLe4n.Kernel.IPC.CrossCore.EndpointCall
import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.CrossCore.NotificationSignal
import SeLe4n.Kernel.IPC.CrossCore.Cancellation

/-!
# WS-RR RR7.18 — size bounds for the **state-resolved** lock footprints

`lockSetTransitions_within_bound` bounds the *argument-taking* footprints —
`lockSet_endpointSend a b c d e` and its thirty-four siblings.  What RR7.12's
bracket actually acquires is not one of those: it is a **state-resolved** form
(`lockSet_endpointSendOnCore st …`), which applies the base footprint to values
read out of the pre-state.  Until this row none of those had a size bound, so
`boundedWait_under_2pl` and the WCRT surface had no premise about the set the
live seam holds — the reasoning was *silent* about it rather than conservative.

Every proof here is one application of the base's bound.  That is the point:
the results were cheap and simply absent, which is what a hand-written
conjunction of thirty-one members cannot notice about itself.
`SeLe4n/Testing/LockFootprintBoundCensus.lean` derives the footprint set from
the elaborated environment and requires each bound at the footprint's own
arity, so the next resolved footprint is covered the day it is written.

**Why this module and not the four that declare the footprints.**  The bounds
cite `Locks/Deadlock.lean`, which is staged — it carries the deadlock-freedom
and WCRT models, which no kernel image links.  Stating them in
`IPC/CrossCore/EndpointCall.lean` and its siblings would have imported a staged
module into production and broken the partition
(`scripts/check_production_staging_partition.sh`), so they live here, staged
with the surface that consumes them.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  The endpoint rendezvous footprints
-- ============================================================================

/-- The state-resolved **send** footprint is within the static bound.  Stated
over the message, not at its default: whether the footprint carries the
capability-transfer destination is a property of what the send carries. -/
theorem lockSet_endpointSendOnCore_size_le (st : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage) :
    (lockSet_endpointSendOnCore st endpointId sender cnodeRootObjId msg).size
      ≤ maxLockSetSize :=
  lockSet_endpointSend_size_le _ _ _ _ _ _

/-- The state-resolved **call** footprint. -/
theorem lockSet_endpointCallOnCore_size_le (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage) :
    (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).size
      ≤ maxLockSetSize :=
  lockSet_endpointCall_size_le _ _ _ _ _ _ _ _ _

/-- The WithCaps footprint is `lockSet_endpointCall` at `some destCnodeObjId`,
so its bound is that one's.  Stated over the reply optional, not at its default
— a defaulted trailing argument is silently filled in at the citation, which is
how a footprint comes to be bounded only in its narrow shape. -/
theorem lockSet_endpointCallWithCaps_size_le (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId destCnodeObjId endpointObjId : SeLe4n.ObjId)
    (receiverTid : Option SeLe4n.ThreadId)
    (donatedScId : Option SeLe4n.SchedContextId)
    (replyId : Option SeLe4n.ReplyId)
    -- **WS-OD OD3.11**: and over the queue-structure neighbour, for the same
    -- reason the reply optional is stated rather than defaulted.
    (queueNeighbour : Option SeLe4n.ThreadId)
    -- **WS-OD (`v0.35.4`)**: and over the old head the donation push rewrites.
    (donationOldHeadReplyId : Option SeLe4n.ReplyId) :
    (lockSet_endpointCallWithCaps callerTid cnodeRootObjId destCnodeObjId
        endpointObjId receiverTid donatedScId replyId queueNeighbour
        donationOldHeadReplyId).size
      ≤ maxLockSetSize :=
  lockSet_endpointCall_size_le _ _ _ _ _ _ _ _ _

/-- The state-resolved **reply** footprint. -/
theorem lockSet_endpointReplyOnCore_size_le (st : SystemState)
    (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) :
    (lockSet_endpointReplyOnCore st replier cnodeRootObjId target).size
      ≤ maxLockSetSize := by
  unfold lockSet_endpointReplyOnCore
  exact lockSet_endpointReply_size_le _ _ _ _ _ _ _ _ _ _ _ _

/-- The `replyRecv` resolved footprint — the widest IPC footprint the kernel
declares.  **Twenty-one** members over all argument values on the widest path: a
delegated reply that returns a donation, re-donates, installs capabilities,
(WS-OD OD3.7) reaches the Reply below the reply-stack head and that frame's
caller's TCB, (WS-OD `v0.35.4`) names the head the pop clears and the old head
the re-donation's push rewrites, and (PR #894 review) declares the five objects
the **invoking** receiver's own pre-receive return touches.

Twenty-one is what the *definition* can produce; no reachable state carries the
last five and the re-donation members at once, which
`lockSet_endpointReplyRecvOnCore_size_le_eighteen` states. -/
theorem lockSet_endpointReplyRecvOnCore_size_le (st : SystemState)
    (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId) :
    (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target endpointObjId).size
      ≤ maxLockSetSize :=
  lockSet_replyRecv_size_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- WS-OD OD1.5: `none` extends nothing. -/
private theorem extendOpt_none (S : LockSet) : lockSetExtendOpt S none = S := rfl

-- ----------------------------------------------------------------------------
-- WS-HP HP7 (`v0.35.46`): the retired binding-driven trigger's scaffolding
-- ----------------------------------------------------------------------------
--
-- Six declarations lived here and are **deleted**, not left as unused
-- predicates.  Three were the *stated* coherence facts the binding-driven
-- donation pop needed and no invariant in this tree entails --
-- `replyDonationOwnerIsAnsweredCaller` (the returned donation is owned by the
-- thread the reply answers) and `replyStackHeadIsAnsweredReply` (the returned
-- context's stack is headed by that caller's own reply object) here, with
-- `answeredHeadContextIsServerDonation` in
-- `IPC/CrossCore/EndpointReplyDispatchInvariant.lean`.  Three were the
-- scaffolding that consumed them: `replyStackHead?_none_of_answeredFrameAbove`
-- (the exclusion the retired `…_size_le_seventeen` bound rested on),
-- `donatedContextHeadsStack` with its vacuity lemma, and HP2.2's
-- `serverDonation_implies_answeredFrameHeadContext?`.
--
-- **What made them dead, in order.**  HP4 (`v0.35.38`) and HP5 (`v0.35.39`)
-- moved both pop triggers onto the answered frame's own `.head` link, so the
-- question "does this donated context head a stack" stopped being asked -- a
-- context that heads no stack simply does not pop.  HP6.2 (`v0.35.44`)
-- repointed the two reply footprints onto that trigger, which retired
-- `…_size_le_seventeen` (its merge occurs on no state the head reading
-- reaches) and made `…_size_le_eighteen` **unconditional** where it had taken
-- two of these facts.  HP6.8 (`v0.35.45`) then made the splice live, which
-- **falsifies** `answeredHeadContextIsServerDonation` on reachable states: a
-- spliced cut re-heads a frame whose recorded reply server is gone and
-- `.unbound`.
--
-- So by HP7 the three facts had no consumer and the scaffolding had no subject.
-- Each one's own docstring said so and named this row as the deletion.  A
-- stated fact nothing consumes reads in a bundle exactly like one that is
-- load-bearing, which is why they are removed rather than marked.
--
-- **Where the evidence went.**  The equivalence HP2 proved -- that the flip was
-- behaviour-preserving on every state the sever could reach -- and HP2.3's
-- orphan-head refutation are now *executed* witnesses rather than theorems
-- whose hypotheses nothing reachable satisfies:
-- `tests/SmpCrossCoreReplySuite.lean` computes the retired binding-driven
-- reading beside the live one on both the agreeing shape and the orphan head,
-- with the retired spelling private to that suite.  That is the pattern
-- `tests/SmpCancellationSuite.lean` §3.20 set for the cancellation side at
-- HP5.5 and `FrozenOpsSuite`'s `FO-042` set for the frozen surface: the retired
-- reading lives in the test that refutes it, and nowhere else.

/-- **WS-RM (`v0.35.6`): what a `.replyRecv` declares with no hypothesis at all —
nineteen.**

The ceiling is twenty-two because a `LockSet` bounds the union over **all**
argument values.  No *state* produces all twenty-two, and the reason is a mutual
exclusion between two groups of members rather than an invariant anyone has to
supply:

* the receive leg's **re-donation** members — the new sender, the context it
  re-donates and the frame its push rewrites — are live exactly when the
  endpoint has a queued sender (`receiveRendezvousDonatedSc?_of_no_sender`);
* the **invoking** receiver's own pre-receive return is live exactly when it
  does not (`receivePreReturn?_of_sender`).

So a rendezvous declares `4 + 14 = 18` and a blocking receive `4 + 16 = 20`, and
twenty bounds both.  Three of the ceiling's twenty-three are slack that no state
can take up; the remaining one is the exclusion the *next* theorem states, which
needs a coherence fact and so cannot live here.

**WS-HP HP3.1 moved this figure and not the two below it.**  The frame below the
answered reply is declared on a mid-stack removal, and nothing *here* rules that
out at the same time as the pop's three members -- that exclusion is the coherence
fact's, so it belongs to the next theorem.  The two sharp bounds are therefore
unchanged at eighteen and seventeen, which is what "the reachable bound does not
move" means: this one is the union over argument values, not a statement about a
reachable state. -/
theorem lockSet_endpointReplyRecvOnCore_size_le_twenty (st : SystemState)
    (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId) :
    (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target endpointObjId).size
      ≤ 20 := by
  unfold lockSet_endpointReplyRecvOnCore
  -- **WS-HP HP10.6**: split on the pop's trigger first, so the origin member and
  -- the two below-head members are decided by one answer.  A frame that heads no
  -- context contributes neither; one that does contributes the origin exactly when
  -- the pop is at the bottom of its stack, and there the below-head pair is absent
  -- (`replyStackBelowHead?_of_originRecipient`).
  cases hHead : answeredFrameHeadContext? st target with
  | none =>
      simp only [Option.map_none, Option.bind_none]
      cases hS : receiveRendezvousSender? st endpointObjId with
      | some sender =>
          rw [receivePreReturn?_of_sender st endpointObjId replier sender hS,
            receivePreReturnStack?_of_sender st endpointObjId replier sender hS]
          simp only [Option.map_none]
          exact Nat.le_trans
            (lockSet_replyRecv_size_le_eighteen_of_no_preReturn_of_no_origin
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by decide : (18 : Nat) ≤ 20)
      | none =>
          rw [receiveRendezvousDonatedSc?_of_no_sender st endpointObjId hS]
          simp only [Option.bind_none]
          exact lockSet_replyRecv_size_le_twenty_of_no_sender_of_no_origin
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | some pr =>
      obtain ⟨scId, holder⟩ := pr
      simp only [Option.map_some, Option.bind_some]
      cases hOrigin : donationOriginRecipient? st scId with
      | none =>
          cases hS : receiveRendezvousSender? st endpointObjId with
          | some sender =>
              rw [receivePreReturn?_of_sender st endpointObjId replier sender hS,
                receivePreReturnStack?_of_sender st endpointObjId replier sender hS]
              simp only [Option.map_none]
              exact Nat.le_trans
                (lockSet_replyRecv_size_le_eighteen_of_no_preReturn_of_no_origin
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (by decide : (18 : Nat) ≤ 20)
          | none =>
              rw [receiveRendezvousDonatedSc?_of_no_sender st endpointObjId hS]
              simp only [Option.bind_none]
              exact lockSet_replyRecv_size_le_twenty_of_no_sender_of_no_origin
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      | some origin =>
          rw [replyStackBelowHead?_of_originRecipient st hOrigin]
          cases hS : receiveRendezvousSender? st endpointObjId with
          | some sender =>
              rw [receivePreReturn?_of_sender st endpointObjId replier sender hS,
                receivePreReturnStack?_of_sender st endpointObjId replier sender hS]
              simp only [Option.map_none]
              exact Nat.le_trans
                (lockSet_replyRecv_size_le_seventeen_of_no_preReturn_of_no_belowHead
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (by decide : (17 : Nat) ≤ 20)
          | none =>
              rw [receiveRendezvousDonatedSc?_of_no_sender st endpointObjId hS]
              simp only [Option.bind_none]
              exact Nat.le_trans
                (lockSet_replyRecv_size_le_nineteen_of_no_sender_of_no_belowHead
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (by decide : (19 : Nat) ≤ 20)

/-- **WS-RM (`v0.35.6`): eighteen — and since WS-HP HP6.2 (`v0.35.44`) with **no
hypothesis at all**.**

The splice's members cost the *reachable* footprint nothing, and this is the
theorem that says so: the answered frame has a frame above it exactly when it is
not a stack head, so the three members the pop contributes are absent whenever the
splice's two are present, and a blocking `.replyRecv` that splices declares
**seventeen**, one fewer than one that pops (sixteen, two fewer, until WS-HP HP3.1
declared the frame below the cut).  Eighteen bounds both branches and both
groups.

**What HP6.2 changed is the price of saying it.**  Under the binding-driven
resolvers the exclusion needed `donationChainWellFormed` *and*
`replyStackHeadIsAnsweredReply`, because nothing tied the context the footprint
named to the frame the reply answered.  With the footprint repointed onto
`answeredFrameHeadContext?` the exclusion is structural — a frame with a frame
above it heads nothing (`answeredReplyFrameAbove?_none_of_headContext`,
`answeredReplyFrameBelow?_none_of_headContext`) — so both hypotheses are gone and
the bound holds on *every* state, reachable or not.  That is strictly stronger
than what it replaces, and it is the first of the two coherence facts the repoint
left with no consumer.  WS-HP HP7 (`v0.35.46`) then **deleted** both; see the
tombstone above. -/
theorem lockSet_endpointReplyRecvOnCore_size_le_eighteen (st : SystemState)
    (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId) :
    (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target endpointObjId).size
      ≤ 18 := by
  unfold lockSet_endpointReplyRecvOnCore
  cases hHead : answeredFrameHeadContext? st target with
  | none =>
      -- The pop contributes nothing -- no context, no holder, no head, no
      -- below-head pair and (WS-HP HP10.6) no origin, since the origin member is
      -- `bind`ed on this very answer.
      simp only [Option.map_none, Option.bind_none]
      cases hS : receiveRendezvousSender? st endpointObjId with
      | some sender =>
          rw [receivePreReturn?_of_sender st endpointObjId replier sender hS,
            receivePreReturnStack?_of_sender st endpointObjId replier sender hS]
          simp only [Option.map_none]
          exact lockSet_replyRecv_size_le_eighteen_of_no_preReturn_of_no_origin
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      | none =>
          rw [receiveRendezvousDonatedSc?_of_no_sender st endpointObjId hS]
          simp only [Option.bind_none]
          exact Nat.le_trans
            (lockSet_replyRecv_size_le_seventeen_of_no_sender_of_no_head_of_no_origin
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by decide : (17 : Nat) ≤ 18)
  | some pr =>
      obtain ⟨scId, holder⟩ := pr
      -- **WS-HP HP6.2**: the exclusion is structural under this trigger.  A
      -- frame that heads a context has no frame above it and none below it,
      -- so the removal's two members are absent on exactly the states the
      -- pop's three are present -- no coherence fact required.
      rw [answeredReplyFrameAbove?_none_of_headContext st target scId holder hHead,
        answeredReplyFrameBelow?_none_of_headContext st target scId holder hHead]
      simp only [Option.map_some, Option.bind_some]
      cases hOrigin : donationOriginRecipient? st scId with
      | none =>
          cases hS : receiveRendezvousSender? st endpointObjId with
          | some sender =>
              rw [receivePreReturn?_of_sender st endpointObjId replier sender hS,
                receivePreReturnStack?_of_sender st endpointObjId replier sender hS]
              simp only [Option.map_none]
              exact lockSet_replyRecv_size_le_eighteen_of_no_preReturn_of_no_origin
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          | none =>
              rw [receiveRendezvousDonatedSc?_of_no_sender st endpointObjId hS]
              simp only [Option.bind_none]
              exact lockSet_replyRecv_size_le_eighteen_of_no_sender_of_no_frameAbove_of_no_origin
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      | some origin =>
          -- **WS-HP HP10.6**: the redirect fires, so the pop is at the bottom of
          -- its stack and the two below-head members are absent -- two members
          -- traded for one, which is why the reachable figure does not move.
          rw [replyStackBelowHead?_of_originRecipient st hOrigin]
          cases hS : receiveRendezvousSender? st endpointObjId with
          | some sender =>
              rw [receivePreReturn?_of_sender st endpointObjId replier sender hS,
                receivePreReturnStack?_of_sender st endpointObjId replier sender hS]
              simp only [Option.map_none]
              exact Nat.le_trans
                (lockSet_replyRecv_size_le_seventeen_of_no_preReturn_of_no_belowHead
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (by decide : (17 : Nat) ≤ 18)
          | none =>
              rw [receiveRendezvousDonatedSc?_of_no_sender st endpointObjId hS]
              simp only [Option.bind_none]
              exact Nat.le_trans
                (lockSet_replyRecv_size_le_seventeen_of_no_sender_of_no_frameAbove_of_no_belowHead
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (by decide : (17 : Nat) ≤ 18)

/-! **WS-HP HP6.2 (`v0.35.44`): `lockSet_endpointReplyRecvOnCore_size_le_seventeen`
is retired, and the reason is the whole of what the repoint costs.**

OD3.7 stated seventeen — one below the bound above — and the single merge that
bought it was `replyDonationOwnerIsAnsweredCaller`: the *owner* the binding-driven
resolver reported is the answered caller, so two arguments named one key and
`insertOrMerge` lubbed the modes without moving the cardinality.

Under the head-driven trigger that merge has no subject.  The pair's second
component is the thread the pop sets `.unbound` — `sc.boundThread`, the thread
*running on* the context — and the answered caller is `.blockedOnReply`, so the
two are never the same thread on any state this arm reaches: the merge is not
merely unproved, it is false.  What is available instead is *holder = the recorded
server*, which is `answeredHeadContextIsServerDonation`'s content and exactly what
the splice falsifies at an orphan head — so a seventeen resting on it would be a
sharp figure that stops holding in the cut after next.

So the reachable figure is **eighteen**, and it is now unconditional where before
it took two coherence facts.  That is the trade this row makes, stated rather than
absorbed: one unit of slack against two hypotheses and a figure that survives the
splice.

**And HP7 (`v0.35.46`) closed that door rather than opening it.**  This paragraph
used to say a sharper bound becomes available again if HP7 derives the
holder/server fact.  It does not: the splice **falsifies** that fact on reachable
states -- an orphan head is a frame heading a context whose recorded reply server
is gone and `.unbound` -- so HP7 deleted the predicate rather than deriving it, and
no sharper reachable bound can rest on it.  Eighteen is the figure. -/

/-- The resolved **receive** footprint.  Stated over the reply optional rather
than at its default, so the receive-with-reply shape is bounded too. -/
theorem lockSet_endpointReceiveOnCore_size_le (st : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (replyId : Option SeLe4n.ReplyId) :
    (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).size
      ≤ maxLockSetSize :=
  lockSet_endpointReceive_size_le _ _ _ _ _ _ _ _ _ _ _ _ _ _

-- ============================================================================
-- §2  The notification footprints
-- ============================================================================

/-- The state-resolved **signal** footprint.  Both arms apply
`lockSet_notificationSignal`, the bound-delivery one at `some`/`some` — the arm
SM9.C's fix had to reach, and the reason that bound is stated over all *seven*
arguments (six before WS-OD OD3.10's splice neighbours) rather than at their
defaults. -/
theorem lockSet_notificationSignalOnCore_size_le (st : SystemState)
    (notificationId : SeLe4n.ObjId) (signaller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) :
    (lockSet_notificationSignalOnCore st notificationId signaller cnodeRootObjId).size
      ≤ maxLockSetSize := by
  unfold lockSet_notificationSignalOnCore
  split <;> exact lockSet_notificationSignal_size_le _ _ _ _ _ _ _

/-- The **wait** footprint, which resolves nothing from `st` and is the base at
its own arguments. -/
theorem lockSet_notificationWaitOnCore_size_le (notificationId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId) :
    (lockSet_notificationWaitOnCore notificationId caller cnodeRootObjId).size
      ≤ maxLockSetSize :=
  lockSet_notificationWait_size_le _ _ _

-- ============================================================================
-- §3  The cancellation teardown footprints
-- ============================================================================

/-- The parametric cancellation footprint: the victim's TCB plus fourteen
optionals.  Stated over all of them, not at their defaults: a bound stated at
fewer arguments would elaborate against the wider footprint with the missing
ones defaulted, and say nothing about the shape the live arm declares. -/
theorem lockSet_cancelIpcBlocking_size_le (victimTid : SeLe4n.ThreadId)
    (blockedEndpointObjId blockedNotificationObjId : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (returnedDonationSc : Option SeLe4n.SchedContextId)
    (donationHolderTid : Option SeLe4n.ThreadId)
    (holderEndpointObjId : Option SeLe4n.ObjId)
    (holderSpliceNeighbors : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId)
    (reclaimHeadReplyId splicedFrameAboveReplyId : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedFrameBelowReplyId : Option SeLe4n.ReplyId) :
    (lockSet_cancelIpcBlocking victimTid blockedEndpointObjId
        blockedNotificationObjId consumedReplyId returnedDonationSc donationHolderTid
        holderEndpointObjId holderSpliceNeighbors belowHeadReplyId outerCallerTid
        reclaimHeadReplyId splicedFrameAboveReplyId splicedFrameBelowReplyId).size
      ≤ maxLockSetSize := by
  unfold lockSet_cancelIpcBlocking maxLockSetSize
  -- WS-OD OD3.5: nine optionals — the donation hand-back's state-level lock.
  -- WS-OD OD3.7: eleven — the two objects the hand-back reaches below the head.
  -- WS-OD (`v0.35.4`): thirteen — the reclaimed head and the detached frame.
  -- **WS-HP HP3.1**: fourteen — the frame below the cut, which the splice
  -- re-links upward in the same step as the frame above's rewrite.
  refine Nat.le_trans (size_le_14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  simp only [List.length_cons, List.length_nil]
  omega

/-- The donation-cancellation footprint: the victim's TCB plus the bound
SchedContext, the donated arm's original owner, (WS-OD `v0.35.4`) the pop's
three stack objects and the state-level lock. -/
theorem lockSet_cancelDonation_size_le (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (headReplyId belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId) :
    (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid
        headReplyId belowHeadReplyId outerCallerTid).size
      ≤ maxLockSetSize := by
  unfold lockSet_cancelDonation maxLockSetSize
  -- WS-OD OD3.5: three optionals — the state-level lock joined the SchedContext
  -- and the original owner.  WS-OD (`v0.35.4`): six, with the pop's objects.
  refine Nat.le_trans (size_le_6 _ _ _ _ _ _ _) ?_
  simp only [List.length_cons, List.length_nil]
  omega

/-- WS-OD OD1.5: **the reply-arm shape of the cancellation footprint** —
**thirteen** over all argument values since WS-HP HP3.1 (twelve at `v0.35.4`).

A `.blockedOnReply` victim is on no endpoint or notification queue, so those two
members are `none` and eleven optionals remain: the consumed reply, the returned
SchedContext, the donation holder, the holder's endpoint and its two splice
neighbours (OD1.5), the frame below the head and the outer caller (OD3.7), the
reclaimed head and the detached frame above (`v0.35.4`), the frame below the cut
(WS-HP HP3.1), and the state-level lock (OD3.5).  Stated parametrically so the
resolved bound below composes it rather than re-running the arithmetic.  The
reachable figure is still **ten**, unmoved by HP3.1: the reclaimed head is the
consumed reply on every reachable state, and a caller with a frame above its own
is owed no reclaim — so on a reachable reply arm the detached frame *and* the
frame below it are both `none`, which is the exclusion
`cancelSplicedFrameBelow?_of_no_frameAbove` states at the resolver. -/
theorem lockSet_cancelIpcBlocking_reply_size_le (victimTid : SeLe4n.ThreadId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (returnedDonationSc : Option SeLe4n.SchedContextId)
    (donationHolderTid : Option SeLe4n.ThreadId)
    (holderEndpointObjId : Option SeLe4n.ObjId)
    (holderSpliceNeighbors : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId)
    (reclaimHeadReplyId splicedFrameAboveReplyId : Option SeLe4n.ReplyId)
    (splicedFrameBelowReplyId : Option SeLe4n.ReplyId) :
    (lockSet_cancelIpcBlocking victimTid none none consumedReplyId returnedDonationSc
        donationHolderTid holderEndpointObjId holderSpliceNeighbors
        belowHeadReplyId outerCallerTid reclaimHeadReplyId
        splicedFrameAboveReplyId splicedFrameBelowReplyId).size ≤ 13 := by
  unfold lockSet_cancelIpcBlocking
  simp only [Option.map_none, extendOpt_none]
  refine Nat.le_trans (size_le_12 _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  simp only [List.length_cons, List.length_nil]
  omega

/-- WS-OD OD1.5: **the no-donation shape is six** (five before WS-HP HP3.1).
Without a donation there is no holder, so no abort, so none of the three members
OD1.5 added, no below-head objects and no reclaimed head — what remains is the
victim's own blocked object, its consumed reply and (WS-OD `v0.35.4`, WS-HP
HP3.1) the two frames the removal re-links, which are reply-arm writes that need
no donation. -/
theorem lockSet_cancelIpcBlocking_noDonation_size_le (victimTid : SeLe4n.ThreadId)
    (blockedEndpointObjId blockedNotificationObjId : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (splicedFrameAboveReplyId : Option SeLe4n.ReplyId)
    (splicedFrameBelowReplyId : Option SeLe4n.ReplyId) :
    (lockSet_cancelIpcBlocking victimTid blockedEndpointObjId blockedNotificationObjId
        consumedReplyId none none none (none, none) none none none
        splicedFrameAboveReplyId splicedFrameBelowReplyId).size ≤ 6 := by
  unfold lockSet_cancelIpcBlocking
  simp only [Option.map_none, extendOpt_none]
  refine Nat.le_trans (size_le_5 _ _ _ _ _ _) ?_
  simp only [List.length_cons, List.length_nil]
  omega

/-- WS-OD (`v0.35.4`), WS-HP HP3.1: **the resolved cancellation footprint on a
victim owed no donation is at most eight** — the victim, its own blocked object,
its consumed reply, the two frames the removal re-links (the one above the cut
and the one below it) and, on the endpoint arm alone, its two splice neighbours.
Every donation-derived member is `none` here, each by its own `_of_no_donation`
reading of the resolver this branch has found to be `none`. -/
theorem lockSet_cancelIpcBlockingOnCore_size_le_of_no_donation (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB)
    (hT : st.getTcb? victimTid = some tcb)
    (hRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = none) :
    (lockSet_cancelIpcBlockingOnCore st victimTid).size ≤ 8 := by
  unfold lockSet_cancelIpcBlockingOnCore
  rw [hT]
  simp only [hRes, Option.map_none, cancelHolderBlockedEndpoint?_none,
    cancelHolderSpliceNeighbors?_none,
    cancelBelowHeadReads?_of_no_donation st victimTid tcb hRes,
    cancelReclaimHead?_of_no_donation st victimTid tcb hRes]
  refine Nat.le_trans (lockSetExtendOpt_size_le _ _) ?_
  refine Nat.le_trans (Nat.add_le_add_right (lockSetExtendOpt_size_le _ _) 1) ?_
  have := lockSet_cancelIpcBlocking_noDonation_size_le victimTid (cancelBlockedEndpoint? tcb)
    (cancelBlockedNotification? tcb) (cancelConsumedReply? tcb)
    (cancelSplicedFrameAbove? st tcb) (cancelSplicedFrameBelow? st tcb)
  omega

/-- WS-OD (`v0.35.4`), WS-HP HP3.1: **…and on a victim owed a donation, at most
thirteen** — the reply arm, whose own endpoint and notification members are
`none` and whose arm-selected neighbours are `(none, none)`, so the parametric
reply-arm bound applies at the resolved arguments.  The *reachable* figure stays
ten: a caller owed a reclaim is the innermost live caller, so its frame has
nothing above it, and both removal members are `none` there. -/
theorem lockSet_cancelIpcBlockingOnCore_size_le_of_donation (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId)
    (hT : st.getTcb? victimTid = some tcb)
    (hRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = some (scId, holder)) :
    (lockSet_cancelIpcBlockingOnCore st victimTid).size ≤ 13 := by
  obtain ⟨ep, rt, hIp⟩ := cancelledCallerDonation?_some_blockedOnReply hRes
  have hE : cancelBlockedEndpoint? tcb = none := by
    unfold cancelBlockedEndpoint?; rw [hIp]
  have hN : cancelBlockedNotification? tcb = none := by
    unfold cancelBlockedNotification?; rw [hIp]
  have hNb : cancelArmSpliceNeighbors? tcb = (none, none) :=
    cancelArmSpliceNeighbors?_of_not_blockedEndpoint tcb hE
  unfold lockSet_cancelIpcBlockingOnCore
  rw [hT]
  simp only [hE, hN, hNb, Option.map_none, extendOpt_none]
  exact lockSet_cancelIpcBlocking_reply_size_le _ _ _ _ _ _ _ _ _ _ _

/-- **The bound over all argument values of the footprint the cancellation
declares: thirteen** (twelve before WS-HP HP3.1).

The state-resolved footprint carries sixteen optional members at full arity —
the victim's blocked endpoint or notification, its consumed reply, the returned
SchedContext, the donation holder, the victim's two splice neighbours, (WS-OD
OD1.5) the holder's endpoint and *its* two splice neighbours, (WS-OD OD3.5) the
state-level lock, (WS-OD OD3.7) the two objects the hand-back reaches below the
reply-stack head, (WS-OD `v0.35.4`) the head the reclaim clears and the frame
above the cut, which the splice rewrites, and (WS-HP HP3.1) the frame below the cut, which the splice
re-links upward.  The bound is thirteen because the members are
**arm-selected**, and selected for a checkable reason rather than by
convention: every resolver keys on `tcb.ipcState`.  `cancelledCallerDonation?`
answers `some` only for a `.blockedOnReply` victim, and so do the eight members
derived from it; `cancelBlockedEndpoint?` / `cancelBlockedNotification?` answer
`some` only for the other blocking states; `cancelArmSpliceNeighbors?` answers
`(none, none)` on every arm but the one that splices; and
`cancelSplicedFrameAbove?` and `cancelSplicedFrameBelow?` are both reply-arm
members, the second derived from the first's resolver.

Arm by arm: the reply arm is `1 + 12 = 13`, the endpoint arm `1 + 3 = 4`, the
notification arm `1 + 1 = 2`, and `.ready` is the victim's TCB alone.  The
**reachable** reply-arm figure is ten, as it was at OD3.7: the reclaimed head is
the consumed reply on every reachable state (they merge by key), and a caller
with a frame above its own is a middle caller, which no reclaim is resolved for
— so on a reachable state the detached frame and the frame below the cut are
*both* `none`, which is why HP3.1 moves the declared bound and not the reachable
one.  A declared bound is the union over all argument values, and it is stated
as such. -/
theorem lockSet_cancelIpcBlockingOnCore_size_le_thirteen (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    (lockSet_cancelIpcBlockingOnCore st victimTid).size ≤ 13 := by
  cases hT : st.getTcb? victimTid with
  | some tcb =>
    cases hRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb with
    | none =>
      exact Nat.le_trans
        (lockSet_cancelIpcBlockingOnCore_size_le_of_no_donation st victimTid tcb hT hRes)
        (by omega)
    | some pr =>
      obtain ⟨scId, holder⟩ := pr
      exact lockSet_cancelIpcBlockingOnCore_size_le_of_donation st victimTid tcb scId holder
        hT hRes
  | none =>
    unfold lockSet_cancelIpcBlockingOnCore
    rw [hT]
    exact Nat.le_trans
      (lockSet_cancelIpcBlocking_noDonation_size_le victimTid none none none none none)
      (by omega)

/-- …and therefore inside the declared ceiling, which is the form
`boundedWait_under_2pl` and the WCRT surface consume. -/
theorem lockSet_cancelIpcBlockingOnCore_size_le (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    (lockSet_cancelIpcBlockingOnCore st victimTid).size ≤ maxLockSetSize :=
  Nat.le_trans (lockSet_cancelIpcBlockingOnCore_size_le_thirteen st victimTid)
    (by unfold maxLockSetSize; omega)

/-- …and the state-resolved donation cancellation, which adds nothing beyond the
parametric form's arguments. -/
theorem lockSet_cancelDonationOnCore_size_le (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    (lockSet_cancelDonationOnCore st victimTid).size ≤ maxLockSetSize := by
  unfold lockSet_cancelDonationOnCore
  split <;> exact lockSet_cancelDonation_size_le _ _ _ _ _ _

-- ============================================================================
-- §4  The `.tcbSuspend` footprint — the widest the kernel declares
-- ============================================================================

/-- WS-OD (`v0.35.4`): the arithmetic of the suspend footprint's widest shape,
stated once over an arbitrary root.  Two read extensions, then a write extension
on a key the root already holds (a mode merge, which costs nothing —
`LockSet.size_insertOrMerge_of_containsKey`), then two more extensions: at most
the root's size plus four. -/
private theorem suspend_reclaim_tail_bound (R : LockSet) (a b : LockId × AccessMode)
    (l : LockId) (o₁ o₂ : Option (LockId × AccessMode)) (hR : R.size ≤ 13)
    (hKey : (lockSetExtendOpt (lockSetExtendOpt R (some a)) (some b)).containsKey l = true) :
    (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
      (lockSetExtendOpt R (some a)) (some b)) (some (l, AccessMode.write))) o₁) o₂).size
      ≤ 17 := by
  have h1 := lockSetExtendOpt_size_le R (some a)
  have h2 := lockSetExtendOpt_size_le (lockSetExtendOpt R (some a)) (some b)
  have hM : (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt R (some a)) (some b))
      (some (l, AccessMode.write))).size
      = (lockSetExtendOpt (lockSetExtendOpt R (some a)) (some b)).size :=
    LockSet.size_insertOrMerge_of_containsKey _ l AccessMode.write hKey
  have h3 := lockSetExtendOpt_size_le (lockSetExtendOpt (lockSetExtendOpt
    (lockSetExtendOpt R (some a)) (some b)) (some (l, AccessMode.write))) o₁
  have h4 := lockSetExtendOpt_size_le (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
    (lockSetExtendOpt R (some a)) (some b)) (some (l, AccessMode.write))) o₁) o₂
  omega

/-- **WS-OD (`v0.35.4`), WS-HP HP3.1: the resolved `.tcbSuspend` footprint is at
most seventeen** (sixteen before HP3.1).

Case by case on what the victim is and what it is owed:

* no victim TCB: the root is the victim's lock alone, plus the caller's two
  reads — three;
* a victim owed no donation: the cancellation root is at most eight
  (`lockSet_cancelIpcBlockingOnCore_size_le_of_no_donation`), the caller's two
  reads and the donation cancellation's five members plus the state-level lock
  — sixteen at most;
* a victim owed a donation at the bottom of its stack: the root is at most
  thirteen and the tail is empty — fifteen;
* a victim owed a donation above the bottom — the second pop: the root is at
  most thirteen, the caller's two reads make fifteen, the outer caller's write
  **merges** with the read the root already holds
  (`lockSet_cancelIpcBlockingOnCore_covers_outerCaller_key`), and the second
  frame's Reply and its caller make **seventeen**.

The last shape is a reply-arm victim at call depth ≥ 3 whose frame has
something above it *and* is owed a reclaim — which no reachable state supplies
(the removal's two frame members and the reclaim are exclusive there), so the
reachable figure is fifteen.  The bound is stated over all argument values, as
every declared bound is.

It is **not** the footprint that sets the ceiling: since PR #894 and WS-RM that
is `lockSet_endpointReplyRecvOnCore`, at twenty-three since HP3.2. -/
theorem lockSet_tcbSuspendOnCore_size_le_seventeen (st : SystemState)
    (callerTid : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (targetTid : SeLe4n.ThreadId) :
    (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).size ≤ 17 := by
  cases hT : st.getTcb? targetTid with
  | none =>
    have hTail : suspendDonationCancelTailOf? st targetTid = {} := by
      unfold suspendDonationCancelTailOf?; rw [hT]
    have hRoot : (lockSet_cancelIpcBlockingOnCore st targetTid).size ≤ 6 := by
      unfold lockSet_cancelIpcBlockingOnCore
      rw [hT]
      exact lockSet_cancelIpcBlocking_noDonation_size_le targetTid none none none none none
    unfold lockSet_tcbSuspendOnCore
    rw [hTail]
    simp only [Option.map_none, extendOpt_none, Option.isSome_none, Bool.false_eq_true,
      if_false]
    have h1 := lockSetExtendOpt_size_le (lockSet_cancelIpcBlockingOnCore st targetTid)
      (some (tcbLock callerTid, AccessMode.read))
    have h2 := lockSetExtendOpt_size_le (lockSetExtendOpt
      (lockSet_cancelIpcBlockingOnCore st targetTid) (some (tcbLock callerTid, AccessMode.read)))
      (some (cnodeLock cnodeRootObjId, AccessMode.read))
    omega
  | some tcb =>
    cases hRes : Lifecycle.Suspend.cancelledCallerDonation? st targetTid tcb with
    | none =>
      have hRoot := lockSet_cancelIpcBlockingOnCore_size_le_of_no_donation st targetTid tcb hT hRes
      unfold lockSet_tcbSuspendOnCore
      exact Nat.le_trans (size_le_8_over _ _ _ _ _ _ _ _ _) (by omega)
    | some pr =>
      obtain ⟨scId, holder⟩ := pr
      have hRoot := lockSet_cancelIpcBlockingOnCore_size_le_of_donation st targetTid tcb scId
        holder hT hRes
      cases hOuter : (replyStackBelowHead? st scId).2 with
      | none =>
        have hTail := suspendDonationCancelTailOf?_of_reclaim_bottom st targetTid tcb scId holder
          hT hRes hOuter
        unfold lockSet_tcbSuspendOnCore
        rw [hTail]
        simp only [Option.map_none, extendOpt_none, Option.isSome_none, Bool.false_eq_true,
          if_false]
        have h1 := lockSetExtendOpt_size_le (lockSet_cancelIpcBlockingOnCore st targetTid)
          (some (tcbLock callerTid, AccessMode.read))
        have h2 := lockSetExtendOpt_size_le (lockSetExtendOpt
          (lockSet_cancelIpcBlockingOnCore st targetTid)
          (some (tcbLock callerTid, AccessMode.read)))
          (some (cnodeLock cnodeRootObjId, AccessMode.read))
        omega
      | some outer =>
        have hTail := suspendDonationCancelTailOf?_of_reclaim_outer st targetTid tcb scId holder
          outer hT hRes hOuter
        have hKey : (lockSetExtendOpt (lockSetExtendOpt
            (lockSet_cancelIpcBlockingOnCore st targetTid)
            (some (tcbLock callerTid, AccessMode.read)))
            (some (cnodeLock cnodeRootObjId, AccessMode.read))).containsKey (tcbLock outer)
            = true :=
          containsKey_lockSetExtendOpt_of_containsKey _ _ _
            (containsKey_lockSetExtendOpt_of_containsKey _ _ _
              (lockSet_cancelIpcBlockingOnCore_covers_outerCaller_key st targetTid tcb scId
                holder outer hT hRes hOuter))
        unfold lockSet_tcbSuspendOnCore
        rw [hTail]
        simp only [Option.map_none, Option.map_some, extendOpt_none, Option.isSome_none,
          Bool.false_eq_true, if_false]
        exact suspend_reclaim_tail_bound _ _ _ _ _ _ hRoot hKey

/-- …and therefore inside the ceiling — the form the census, the deadlock-freedom
theorem and the WCRT surface consume. -/
theorem lockSet_tcbSuspendOnCore_size_le (st : SystemState) (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (targetTid : SeLe4n.ThreadId) :
    (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).size ≤ maxLockSetSize :=
  Nat.le_trans (lockSet_tcbSuspendOnCore_size_le_seventeen st callerTid cnodeRootObjId targetTid)
    (by unfold maxLockSetSize; omega)

/-- WS-SM SM3.D.6 / WS-OD (`v0.35.4`): the `KernelOperation` for a `.tcbSuspend`,
built over the state-resolved footprint the seam acquires and its bound.  It
replaces `KernelOperation.ofTcbSuspend`, which was built over the retired
parametric footprint. -/
def KernelOperation.ofTcbSuspendOnCore (st : SystemState) (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (targetTid : SeLe4n.ThreadId) : KernelOperation :=
  ⟨lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid,
   lockSet_tcbSuspendOnCore_size_le st callerTid cnodeRootObjId targetTid⟩

end SeLe4n.Kernel
