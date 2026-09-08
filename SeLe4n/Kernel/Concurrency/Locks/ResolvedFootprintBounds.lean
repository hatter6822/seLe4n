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
  lockSet_endpointSend_size_le _ _ _ _ _

/-- The state-resolved **call** footprint. -/
theorem lockSet_endpointCallOnCore_size_le (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId) (msg : IpcMessage) :
    (lockSet_endpointCallOnCore st endpointId caller cnodeRootObjId msg).size
      ≤ maxLockSetSize :=
  lockSet_endpointCall_size_le _ _ _ _ _ _ _

/-- The WithCaps footprint is `lockSet_endpointCall` at `some destCnodeObjId`,
so its bound is that one's.  Stated over the reply optional, not at its default
— a defaulted trailing argument is silently filled in at the citation, which is
how a footprint comes to be bounded only in its narrow shape. -/
theorem lockSet_endpointCallWithCaps_size_le (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId destCnodeObjId endpointObjId : SeLe4n.ObjId)
    (receiverTid : Option SeLe4n.ThreadId)
    (donatedScId : Option SeLe4n.SchedContextId)
    (replyId : Option SeLe4n.ReplyId) :
    (lockSet_endpointCallWithCaps callerTid cnodeRootObjId destCnodeObjId
        endpointObjId receiverTid donatedScId replyId).size
      ≤ maxLockSetSize :=
  lockSet_endpointCall_size_le _ _ _ _ _ _ _

/-- The state-resolved **reply** footprint. -/
theorem lockSet_endpointReplyOnCore_size_le (st : SystemState)
    (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) :
    (lockSet_endpointReplyOnCore st replier cnodeRootObjId target).size
      ≤ maxLockSetSize := by
  unfold lockSet_endpointReplyOnCore
  exact lockSet_endpointReply_size_le _ _ _ _ _ _

/-- The `replyRecv` resolved footprint — the widest the kernel declares, and the
one `maxLockSetSize` is measured against (nine members on the
donation-return-plus-caps-install path). -/
theorem lockSet_endpointReplyRecvOnCore_size_le (st : SystemState)
    (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId) :
    (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target endpointObjId).size
      ≤ maxLockSetSize :=
  lockSet_replyRecv_size_le _ _ _ _ _ _ _ _ _

/-- The resolved **receive** footprint.  Stated over the reply optional rather
than at its default, so the receive-with-reply shape is bounded too. -/
theorem lockSet_endpointReceiveOnCore_size_le (st : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (replyId : Option SeLe4n.ReplyId) :
    (lockSet_endpointReceiveOnCore st endpointId receiver cnodeRootObjId replyId).size
      ≤ maxLockSetSize :=
  lockSet_endpointReceive_size_le _ _ _ _ _ _

-- ============================================================================
-- §2  The notification footprints
-- ============================================================================

/-- The state-resolved **signal** footprint.  Both arms apply
`lockSet_notificationSignal`, the bound-delivery one at `some`/`some` — the arm
SM9.C's fix had to reach, and the reason that bound is stated over all six
arguments rather than at their defaults. -/
theorem lockSet_notificationSignalOnCore_size_le (st : SystemState)
    (notificationId : SeLe4n.ObjId) (signaller : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) :
    (lockSet_notificationSignalOnCore st notificationId signaller cnodeRootObjId).size
      ≤ maxLockSetSize := by
  unfold lockSet_notificationSignalOnCore
  split <;> exact lockSet_notificationSignal_size_le _ _ _ _ _ _

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

/-- The parametric cancellation footprint: the victim's TCB plus five optionals
(the endpoint or notification it was blocked on, the reply object it consumed,
and — WS-RR RR7.22 (residual, remediation) — the SchedContext the reply arm hands
back with its holder's TCB).  Stated over all five, not at their defaults: a
bound stated at fewer arguments would elaborate against the wider footprint with
the missing ones defaulted, and say nothing about the shape the live arm
declares. -/
theorem lockSet_cancelIpcBlocking_size_le (victimTid : SeLe4n.ThreadId)
    (blockedEndpointObjId blockedNotificationObjId : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (returnedDonationSc : Option SeLe4n.SchedContextId)
    (donationHolderTid : Option SeLe4n.ThreadId)
    (holderEndpointObjId : Option SeLe4n.ObjId)
    (holderSpliceNeighbors : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId) :
    (lockSet_cancelIpcBlocking victimTid blockedEndpointObjId
        blockedNotificationObjId consumedReplyId returnedDonationSc donationHolderTid
        holderEndpointObjId holderSpliceNeighbors).size
      ≤ maxLockSetSize := by
  unfold lockSet_cancelIpcBlocking maxLockSetSize
  refine Nat.le_trans (size_le_8 _ _ _ _ _ _ _ _ _) ?_
  simp only [List.length_cons, List.length_nil]
  omega

/-- The donation-cancellation footprint: the victim's TCB plus the bound
SchedContext and the donated arm's original owner. -/
theorem lockSet_cancelDonation_size_le (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId) :
    (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid).size
      ≤ maxLockSetSize := by
  unfold lockSet_cancelDonation maxLockSetSize
  refine Nat.le_trans (size_le_2 _ _ _) ?_
  simp only [List.length_cons, List.length_nil]
  omega

/-- WS-OD OD1.5: `none` extends nothing. -/
private theorem extendOpt_none (S : LockSet) : lockSetExtendOpt S none = S := rfl

/-- WS-OD OD1.5: **the reply-arm shape of the cancellation footprint is seven.**

A `.blockedOnReply` victim is on no endpoint or notification queue, so those two
members are `none` and six remain: the victim's TCB, its consumed reply, the
returned SchedContext, the donation holder, and — since OD1.5 — the holder's
endpoint and its two splice neighbours.  Stated parametrically so the resolved
bound below composes it with the victim's own two neighbours rather than
re-running the arithmetic. -/
theorem lockSet_cancelIpcBlocking_reply_size_le (victimTid : SeLe4n.ThreadId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (returnedDonationSc : Option SeLe4n.SchedContextId)
    (donationHolderTid : Option SeLe4n.ThreadId)
    (holderEndpointObjId : Option SeLe4n.ObjId)
    (holderSpliceNeighbors : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId) :
    (lockSet_cancelIpcBlocking victimTid none none consumedReplyId returnedDonationSc
        donationHolderTid holderEndpointObjId holderSpliceNeighbors).size ≤ 7 := by
  unfold lockSet_cancelIpcBlocking
  simp only [Option.map_none, extendOpt_none]
  refine Nat.le_trans (size_le_6 _ _ _ _ _ _ _) ?_
  simp only [List.length_cons, List.length_nil]
  omega

/-- WS-OD OD1.5: **the no-donation shape is four.**  Without a donation there is
no holder, so no abort, so none of the three members OD1.5 added — and no
consumed reply either, since that too is a `.blockedOnReply` fact. -/
theorem lockSet_cancelIpcBlocking_noDonation_size_le (victimTid : SeLe4n.ThreadId)
    (blockedEndpointObjId blockedNotificationObjId : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId) :
    (lockSet_cancelIpcBlocking victimTid blockedEndpointObjId blockedNotificationObjId
        consumedReplyId none none none (none, none)).size ≤ 4 := by
  unfold lockSet_cancelIpcBlocking
  simp only [Option.map_none, extendOpt_none]
  refine Nat.le_trans (size_le_3 _ _ _ _) ?_
  simp only [List.length_cons, List.length_nil]
  omega

/-- WS-OD OD1.5: a resolved cancellation donation witnesses a `.blockedOnReply`
victim.

Restated here rather than imported: `cancelledCallerDonation?_some`
(`Lifecycle/Invariant/CancellationReplyShape.lean`) says more and sits above this
module, and the bound needs only the `ipcState` shape — which is what makes the
donation members and the victim's own blocked-object members mutually
exclusive. -/
private theorem cancelledCallerDonation_some_blockedOnReply
    {st : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB}
    {scId : SeLe4n.SchedContextId} {holder : SeLe4n.ThreadId}
    (h : Lifecycle.Suspend.cancelledCallerDonation? st tid tcb = some (scId, holder)) :
    ∃ ep rt, tcb.ipcState = .blockedOnReply ep rt := by
  unfold Lifecycle.Suspend.cancelledCallerDonation? at h
  repeat' split at h
  all_goals simp_all

/-- **The one the `.tcbSuspend` bracket acquires**, and the tightest bound in the
tree.

The state-resolved footprint carries **ten** optional members at full arity — the
victim's blocked endpoint or notification, its consumed reply, the returned
SchedContext, the donation holder, the victim's two splice neighbours, and (WS-OD
OD1.5) the holder's endpoint and *its* two splice neighbours.  Summed, that is
eleven, over the ceiling; the bound holds because the two groups are **mutually
exclusive**, and exclusive for a checkable reason rather than by convention: both
key on `tcb.ipcState`.  `cancelledCallerDonation?` answers `some` only for a
`.blockedOnReply` victim, and `cancelBlockedEndpoint?` / `cancelBlockedNotification?`
answer `some` only for the other blocking states.

So the reply arm is `1 + 8 = 9`, exactly `maxLockSetSize`, and every other arm is
`1 + 3 = 4` or less.  **Nine leaves no headroom**: the arm-selected split (WS-OD
OD3.6) is what buys it back, and it is scheduled before OD3.7 adds the previous
reply's read for exactly this reason. -/
theorem lockSet_cancelIpcBlockingOnCore_size_le (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    (lockSet_cancelIpcBlockingOnCore st victimTid).size ≤ maxLockSetSize := by
  unfold lockSet_cancelIpcBlockingOnCore
  split
  · rename_i tcb _
    cases hRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb with
    | none =>
      -- No donation: the five donation-derived members are `none`, so the chain
      -- is the victim's own blocked object, its reply and its two neighbours.
      simp only [Option.map_none, cancelHolderBlockedEndpoint?_none,
        cancelHolderSpliceNeighbors?_none]
      refine Nat.le_trans (lockSetExtendOpt_size_le _ _) ?_
      refine Nat.le_trans (Nat.add_le_add_right (lockSetExtendOpt_size_le _ _) 1) ?_
      have := lockSet_cancelIpcBlocking_noDonation_size_le victimTid (cancelBlockedEndpoint? tcb)
        (cancelBlockedNotification? tcb) (cancelConsumedReply? tcb)
      unfold maxLockSetSize
      omega
    | some pr =>
      -- A donation: the victim is `.blockedOnReply`, so its own endpoint and
      -- notification members are `none` and eight optional members remain.
      obtain ⟨scId, holder⟩ := pr
      obtain ⟨ep, rt, hIp⟩ := cancelledCallerDonation_some_blockedOnReply hRes
      have hE : cancelBlockedEndpoint? tcb = none := by
        unfold cancelBlockedEndpoint?; rw [hIp]
      have hN : cancelBlockedNotification? tcb = none := by
        unfold cancelBlockedNotification?; rw [hIp]
      rw [hE, hN]
      refine Nat.le_trans (lockSetExtendOpt_size_le _ _) ?_
      refine Nat.le_trans (Nat.add_le_add_right (lockSetExtendOpt_size_le _ _) 1) ?_
      refine Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right
        (lockSet_cancelIpcBlocking_reply_size_le _ _ _ _ _ _) 1) 1) ?_
      unfold maxLockSetSize
      omega
  · exact lockSet_cancelIpcBlocking_size_le _ _ _ _ _ _ _ _

/-- …and the state-resolved donation cancellation, which adds nothing beyond the
parametric form's arguments. -/
theorem lockSet_cancelDonationOnCore_size_le (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    (lockSet_cancelDonationOnCore st victimTid).size ≤ maxLockSetSize := by
  unfold lockSet_cancelDonationOnCore
  split <;> exact lockSet_cancelDonation_size_le _ _ _

end SeLe4n.Kernel
