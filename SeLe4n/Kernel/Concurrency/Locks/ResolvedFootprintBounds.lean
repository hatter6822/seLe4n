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
  exact lockSet_endpointReply_size_le _ _ _ _ _ _ _ _ _

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
  lockSet_replyRecv_size_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- WS-OD OD1.5: `none` extends nothing. -/
private theorem extendOpt_none (S : LockSet) : lockSetExtendOpt S none = S := rfl

/-- **WS-OD OD3.7: what a reachable `.replyRecv` actually declares.**

The donation a reply returns is owned by the thread the reply answers —
`applyCallDonation` recorded it that way when the caller made the Call.  But
`ipcInvariantFull` does **not** entail it: `donationOwnerValid` says only that the
owner is `.unbound` and `.blockedOnReply epId rt` for *some* `rt`, and relates
`rt` to no donation.  WS-RR RR7.22 met the same gap from the cancellation end and
closed it by stating `donationHolderIsReplyTarget`; this is its reply-side twin,
and it is stated rather than derived for exactly that reason.

Kept as a predicate on `(st, target)` rather than folded into a bundle: it is a
*local* coherence fact about one reply, and the resolved bound below is the only
consumer.  A conjunct of `ipcReachable` would oblige every transition to
re-establish it for every thread. -/
def replyDonationOwnerIsAnsweredCaller (st : SystemState) (target : SeLe4n.ThreadId) : Prop :=
  ∀ scId owner, endpointReplyServerDonation? st target = some (scId, owner) → owner = target

/-- **PR #894 review: what a reachable `.replyRecv` actually declares — eighteen,
with no hypothesis at all.**

The ceiling is twenty-one because a `LockSet` bounds the union over **all**
argument values.  No *state* produces all twenty-one, and the reason is a mutual
exclusion between two groups of members rather than an invariant anyone has to
supply:

* the receive leg's **re-donation** members — the new sender, the context it
  re-donates and the frame its push rewrites — are live exactly when the
  endpoint has a queued sender (`receiveRendezvousDonatedSc?_of_no_sender`);
* the **invoking** receiver's own pre-receive return is live exactly when it
  does not (`receivePreReturn?_of_sender`).

So a rendezvous declares `4 + 12 = 16` and a blocking receive `4 + 14 = 18`, and
eighteen bounds both.  Three of the ceiling's twenty-one are slack that no state
can take up; stating that here is what stops the next reader re-deriving it from
the definition, the way WS-OD OD3.7 established for this same arm. -/
theorem lockSet_endpointReplyRecvOnCore_size_le_eighteen (st : SystemState)
    (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId) :
    (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target endpointObjId).size
      ≤ 18 := by
  unfold lockSet_endpointReplyRecvOnCore
  cases hS : receiveRendezvousSender? st endpointObjId with
  | some sender =>
      -- A rendezvous: the invoker does not block, so its pre-receive return does
      -- not run and the five members it would contribute are absent.
      rw [receivePreReturn?_of_sender st endpointObjId replier sender hS,
        receivePreReturnStack?_of_sender st endpointObjId replier sender hS]
      simp only [Option.map_none]
      exact Nat.le_trans
        (lockSet_replyRecv_size_le_sixteen_of_no_preReturn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (by decide : (16 : Nat) ≤ 18)
  | none =>
      -- A blocking receive: nothing is dequeued, so the new sender, the
      -- re-donated context and the frame its push would rewrite are all absent.
      rw [receiveRendezvousDonatedSc?_of_no_sender st endpointObjId hS]
      simp only [Option.bind_none]
      exact lockSet_replyRecv_size_le_eighteen_of_no_sender
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **WS-OD OD3.7: and one narrower still under the donation discipline —
seventeen.**

**WS-OD OD3.13** moved the ceiling and this figure together (fourteen and
thirteen); **WS-OD `v0.35.4`** added the head the pop clears and the old head the
re-donation's push rewrites; **PR #894 review** added the invoking receiver's own
pre-receive return and took the ceiling to twenty-one.  What this theorem adds
over the unconditional eighteen above is the one *merge* the invariants supply:
the returned donation's owner is the answered caller, so two arguments name one
key and `insertOrMerge` lubs the modes without moving the cardinality.

That merge is the whole of the remaining sharpening.  The other candidate — the
recorded server with the invoking thread — holds exactly on a *non-delegated*
reply, which is a case split rather than an invariant, and the delegated case is
precisely the one WS-OD OD3.5 exists to declare and PR #894's review found still
undeclared.

Neither figure moves `maxLockSetSize`: the parametric bound is what
`boundedWait_under_2pl` and the WCRT surface consume, and it must stay true of
every argument value.  What these give is a smaller number available where the
state permits — the relationship `lockSet_cancelIpcBlockingOnCore_size_le_ten`
already has to the ceiling. -/
theorem lockSet_endpointReplyRecvOnCore_size_le_seventeen (st : SystemState)
    (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId)
    (hOwner : replyDonationOwnerIsAnsweredCaller st target) :
    (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target endpointObjId).size
      ≤ 17 := by
  unfold lockSet_endpointReplyRecvOnCore
  cases hS : receiveRendezvousSender? st endpointObjId with
  | some sender =>
      -- A rendezvous declares sixteen whatever the reply returns; the owner merge
      -- is not even needed to stay inside seventeen here.
      rw [receivePreReturn?_of_sender st endpointObjId replier sender hS,
        receivePreReturnStack?_of_sender st endpointObjId replier sender hS]
      simp only [Option.map_none]
      exact Nat.le_trans
        (lockSet_replyRecv_size_le_sixteen_of_no_preReturn
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by decide : (16 : Nat) ≤ 17)
  | none =>
      rw [receiveRendezvousDonatedSc?_of_no_sender st endpointObjId hS]
      cases hDon : endpointReplyServerDonation? st target with
      | none =>
          -- Nothing to return: neither group of state-resolved members is live
          -- but the invoker's own pre-receive return, so this is thirteen.
          simp only [Option.map_none, Option.bind_none]
          exact Nat.le_trans
            (lockSet_replyRecv_size_le_thirteen_of_no_sender_of_no_donation
              _ _ _ _ _ _ _ _ _ _ _ _ _) (by decide : (13 : Nat) ≤ 17)
      | some pr =>
          obtain ⟨scId, owner⟩ := pr
          have hEq : owner = target := hOwner scId owner hDon
          subst hEq
          simp only [Option.map_some, Option.bind_none]
          exact lockSet_replyRecv_size_le_seventeen_of_owner_eq_target_of_no_sender
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

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

/-- The parametric cancellation footprint: the victim's TCB plus thirteen
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
    (reclaimHeadReplyId detachedFrameAboveReplyId : Option SeLe4n.ReplyId) :
    (lockSet_cancelIpcBlocking victimTid blockedEndpointObjId
        blockedNotificationObjId consumedReplyId returnedDonationSc donationHolderTid
        holderEndpointObjId holderSpliceNeighbors belowHeadReplyId outerCallerTid
        reclaimHeadReplyId detachedFrameAboveReplyId).size
      ≤ maxLockSetSize := by
  unfold lockSet_cancelIpcBlocking maxLockSetSize
  -- WS-OD OD3.5: nine optionals — the donation hand-back's state-level lock.
  -- WS-OD OD3.7: eleven — the two objects the hand-back reaches below the head.
  -- WS-OD (`v0.35.4`): thirteen — the reclaimed head and the detached frame.
  refine Nat.le_trans (size_le_13 _ _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
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

/-- WS-OD OD1.5: **the reply-arm shape of the cancellation footprint** — twelve
over all argument values since WS-OD `v0.35.4`.

A `.blockedOnReply` victim is on no endpoint or notification queue, so those two
members are `none` and eleven optionals remain: the consumed reply, the returned
SchedContext, the donation holder, the holder's endpoint and its two splice
neighbours (OD1.5), the frame below the head and the outer caller (OD3.7), the
reclaimed head and the detached frame above (`v0.35.4`), and the state-level
lock (OD3.5).  Stated parametrically so the resolved bound below composes it
rather than re-running the arithmetic.  The reachable figure is ten: the
reclaimed head is the consumed reply on every reachable state, and a caller
with a frame above its own is owed no reclaim. -/
theorem lockSet_cancelIpcBlocking_reply_size_le (victimTid : SeLe4n.ThreadId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (returnedDonationSc : Option SeLe4n.SchedContextId)
    (donationHolderTid : Option SeLe4n.ThreadId)
    (holderEndpointObjId : Option SeLe4n.ObjId)
    (holderSpliceNeighbors : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId)
    (reclaimHeadReplyId detachedFrameAboveReplyId : Option SeLe4n.ReplyId) :
    (lockSet_cancelIpcBlocking victimTid none none consumedReplyId returnedDonationSc
        donationHolderTid holderEndpointObjId holderSpliceNeighbors
        belowHeadReplyId outerCallerTid reclaimHeadReplyId
        detachedFrameAboveReplyId).size ≤ 12 := by
  unfold lockSet_cancelIpcBlocking
  simp only [Option.map_none, extendOpt_none]
  refine Nat.le_trans (size_le_11 _ _ _ _ _ _ _ _ _ _ _ _) ?_
  simp only [List.length_cons, List.length_nil]
  omega

/-- WS-OD OD1.5: **the no-donation shape is five.**  Without a donation there is
no holder, so no abort, so none of the three members OD1.5 added, no below-head
objects and no reclaimed head — what remains is the victim's own blocked object,
its consumed reply and (WS-OD `v0.35.4`) the frame the detach unlinks, which is a
reply-arm write that needs no donation. -/
theorem lockSet_cancelIpcBlocking_noDonation_size_le (victimTid : SeLe4n.ThreadId)
    (blockedEndpointObjId blockedNotificationObjId : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (detachedFrameAboveReplyId : Option SeLe4n.ReplyId) :
    (lockSet_cancelIpcBlocking victimTid blockedEndpointObjId blockedNotificationObjId
        consumedReplyId none none none (none, none) none none none
        detachedFrameAboveReplyId).size ≤ 5 := by
  unfold lockSet_cancelIpcBlocking
  simp only [Option.map_none, extendOpt_none]
  refine Nat.le_trans (size_le_4 _ _ _ _ _) ?_
  simp only [List.length_cons, List.length_nil]
  omega

/-- WS-OD (`v0.35.4`): **the resolved cancellation footprint on a victim owed no
donation is at most seven** — the victim, its own blocked object, its consumed
reply, the frame the detach unlinks and, on the endpoint arm alone, its two
splice neighbours.  Every donation-derived member is `none` here, each by its
own `_of_no_donation` reading of the resolver this branch has found to be
`none`. -/
theorem lockSet_cancelIpcBlockingOnCore_size_le_of_no_donation (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB)
    (hT : st.getTcb? victimTid = some tcb)
    (hRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = none) :
    (lockSet_cancelIpcBlockingOnCore st victimTid).size ≤ 7 := by
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
    (cancelDetachedFrameAbove? st tcb)
  omega

/-- WS-OD (`v0.35.4`): **…and on a victim owed a donation, at most twelve** —
the reply arm, whose own endpoint and notification members are `none` and whose
arm-selected neighbours are `(none, none)`, so the parametric reply-arm bound
applies at the resolved arguments. -/
theorem lockSet_cancelIpcBlockingOnCore_size_le_of_donation (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId)
    (hT : st.getTcb? victimTid = some tcb)
    (hRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = some (scId, holder)) :
    (lockSet_cancelIpcBlockingOnCore st victimTid).size ≤ 12 := by
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
  exact lockSet_cancelIpcBlocking_reply_size_le _ _ _ _ _ _ _ _ _ _

/-- **The bound over all argument values of the footprint the cancellation
declares: twelve.**

The state-resolved footprint carries fifteen optional members at full arity —
the victim's blocked endpoint or notification, its consumed reply, the returned
SchedContext, the donation holder, the victim's two splice neighbours, (WS-OD
OD1.5) the holder's endpoint and *its* two splice neighbours, (WS-OD OD3.5) the
state-level lock, (WS-OD OD3.7) the two objects the hand-back reaches below the
reply-stack head, and (WS-OD `v0.35.4`) the head the reclaim clears and the frame
the detach unlinks.  The bound is twelve because the members are
**arm-selected**, and selected for a checkable reason rather than by
convention: every resolver keys on `tcb.ipcState`.  `cancelledCallerDonation?`
answers `some` only for a `.blockedOnReply` victim, and so do the eight members
derived from it; `cancelBlockedEndpoint?` / `cancelBlockedNotification?` answer
`some` only for the other blocking states; `cancelArmSpliceNeighbors?` answers
`(none, none)` on every arm but the one that splices; and
`cancelDetachedFrameAbove?` is a reply-arm member.

Arm by arm: the reply arm is `1 + 11 = 12`, the endpoint arm `1 + 3 = 4`, the
notification arm `1 + 1 = 2`, and `.ready` is the victim's TCB alone.  The
**reachable** reply-arm figure is ten, as it was at OD3.7: the reclaimed head is
the consumed reply on every reachable state (they merge by key), and a caller
with a frame above its own is a middle caller, which no reclaim is resolved for
— but a declared bound is the union over all argument values, and it is stated
as such. -/
theorem lockSet_cancelIpcBlockingOnCore_size_le_twelve (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    (lockSet_cancelIpcBlockingOnCore st victimTid).size ≤ 12 := by
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
      (lockSet_cancelIpcBlocking_noDonation_size_le victimTid none none none none)
      (by omega)

/-- …and therefore inside the declared ceiling, which is the form
`boundedWait_under_2pl` and the WCRT surface consume. -/
theorem lockSet_cancelIpcBlockingOnCore_size_le (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    (lockSet_cancelIpcBlockingOnCore st victimTid).size ≤ maxLockSetSize :=
  Nat.le_trans (lockSet_cancelIpcBlockingOnCore_size_le_twelve st victimTid)
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
    (l : LockId) (o₁ o₂ : Option (LockId × AccessMode)) (hR : R.size ≤ 12)
    (hKey : (lockSetExtendOpt (lockSetExtendOpt R (some a)) (some b)).containsKey l = true) :
    (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
      (lockSetExtendOpt R (some a)) (some b)) (some (l, AccessMode.write))) o₁) o₂).size
      ≤ 16 := by
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

/-- **WS-OD (`v0.35.4`): the resolved `.tcbSuspend` footprint is at most sixteen —
the footprint that defines `maxLockSetSize`.**

Case by case on what the victim is and what it is owed:

* no victim TCB: the root is the victim's lock alone, plus the caller's two
  reads — three;
* a victim owed no donation: the cancellation root is at most seven
  (`lockSet_cancelIpcBlockingOnCore_size_le_of_no_donation`), the caller's two
  reads and the donation cancellation's five members plus the state-level lock
  — fifteen at most;
* a victim owed a donation at the bottom of its stack: the root is at most
  twelve and the tail is empty — fourteen;
* a victim owed a donation above the bottom — the second pop: the root is at
  most twelve, the caller's two reads make fourteen, the outer caller's write
  **merges** with the read the root already holds
  (`lockSet_cancelIpcBlockingOnCore_covers_outerCaller_key`), and the second
  frame's Reply and its caller make **sixteen**.

The last shape is a reply-arm victim at call depth ≥ 3 whose frame has
something above it *and* is owed a reclaim — which no reachable state supplies
(the detached-frame member and the reclaim are exclusive there), so the
reachable figure is fifteen.  The bound is stated over all argument values, as
every declared bound is. -/
theorem lockSet_tcbSuspendOnCore_size_le_sixteen (st : SystemState)
    (callerTid : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (targetTid : SeLe4n.ThreadId) :
    (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).size ≤ 16 := by
  cases hT : st.getTcb? targetTid with
  | none =>
    have hTail : suspendDonationCancelTailOf? st targetTid = {} := by
      unfold suspendDonationCancelTailOf?; rw [hT]
    have hRoot : (lockSet_cancelIpcBlockingOnCore st targetTid).size ≤ 5 := by
      unfold lockSet_cancelIpcBlockingOnCore
      rw [hT]
      exact lockSet_cancelIpcBlocking_noDonation_size_le targetTid none none none none
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
theorem and the WCRT surface consume.  The ceiling is sixteen *because* this
footprint reaches it. -/
theorem lockSet_tcbSuspendOnCore_size_le (st : SystemState) (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (targetTid : SeLe4n.ThreadId) :
    (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).size ≤ maxLockSetSize :=
  Nat.le_trans (lockSet_tcbSuspendOnCore_size_le_sixteen st callerTid cnodeRootObjId targetTid)
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
