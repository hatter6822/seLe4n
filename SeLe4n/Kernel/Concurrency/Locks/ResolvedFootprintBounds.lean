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

/-- The parametric cancellation footprint: the victim's TCB plus three optionals
(the endpoint or notification it was blocked on, and the reply object it
consumed).  Stated over all three, not at their defaults. -/
theorem lockSet_cancelIpcBlocking_size_le (victimTid : SeLe4n.ThreadId)
    (blockedEndpointObjId blockedNotificationObjId : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId) :
    (lockSet_cancelIpcBlocking victimTid blockedEndpointObjId
        blockedNotificationObjId consumedReplyId).size
      ≤ maxLockSetSize := by
  unfold lockSet_cancelIpcBlocking maxLockSetSize
  refine Nat.le_trans (size_le_3 _ _ _ _) ?_
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

/-- **The one the `.tcbSuspend` bracket acquires.**  The state-resolved
cancellation footprint adds the two splice-neighbour TCB writes on top of the
parametric form, so it is the widest of this family — six members on a victim
that is mid-queue with a consumed reply — and the one whose bound bounded-wait
needs. -/
theorem lockSet_cancelIpcBlockingOnCore_size_le (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    (lockSet_cancelIpcBlockingOnCore st victimTid).size ≤ maxLockSetSize := by
  unfold lockSet_cancelIpcBlockingOnCore lockSet_cancelIpcBlocking maxLockSetSize
  split
  · refine Nat.le_trans (size_le_5 _ _ _ _ _ _) ?_
    simp only [List.length_cons, List.length_nil]
    omega
  · refine Nat.le_trans (size_le_3 _ _ _ _) ?_
    simp only [List.length_cons, List.length_nil]
    omega

/-- …and the state-resolved donation cancellation, which adds nothing beyond the
parametric form's arguments. -/
theorem lockSet_cancelDonationOnCore_size_le (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    (lockSet_cancelDonationOnCore st victimTid).size ≤ maxLockSetSize := by
  unfold lockSet_cancelDonationOnCore
  split <;> exact lockSet_cancelDonation_size_le _ _ _

end SeLe4n.Kernel
