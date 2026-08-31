-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR2.14: PRODUCTION.  The whole-bundle statement for the capability
-- transfer leg every `*WithCaps*` IPC transition ends in.  Enters the production
-- import closure through the cross-core `.send` and `.call` bundle theorems.

import SeLe4n.Kernel.IPC.Invariant.Structural
import SeLe4n.Kernel.Capability.Invariant

/-!
# WS-RR RR2.14 — `ipcUnwrapCaps` preserves the whole IPC invariant bundle

Every capability-carrying IPC transition (`endpointSendDualWithCaps{,OnCore}`,
`endpointCallWithCaps{,OnCore}`, `endpointReceiveDualWithCaps`) is its bare
transition followed by `ipcUnwrapCaps`, which installs the transferred
capabilities into the receiver's CSpace.  The per-conjunct preservation lemmas
for that step all existed; what did not exist was the **assembly**, so each
WithCaps bundle theorem re-derived it inline and a per-core WithCaps bundle
would have had to re-derive it again.

Stating it once is what makes the cross-core `.send` and `.call` bundles
(RR2.14, RR2.6) a two-line composition instead of a second copy of an
eighteen-conjunct proof.

## Nothing is threaded

All twenty conjuncts are **established** from the pre-state — including
`blockedThreadsPendingMessageConsistent` and both halves of `replyCallerLinkage`,
which the single-core WithCaps bundles thread, because the transfer touches no
TCB and no Reply object at all.

`dualQueueSystemInvariant` and `badgeWellFormed` are established too, from the
preservation lemmas the tree already had
(`ipcUnwrapCaps_preserves_dualQueueSystemInvariant`,
`…_preserves_badgeWellFormed`).  Each needs a side condition, and both are
conditions on the operation's *inputs* rather than on its result: a CNode at the
receiver's CSpace root, and badge validity of the capabilities carried in the
message.  Neither can be satisfied by the transition they constrain, which is the
distinction that makes them preconditions rather than threading.

So this module removes two of the eight sites **WS-RR RR3.11** ("de-thread
`dualQueueSystemInvariant` / `badgeWellFormed` at the eight remaining sites")
inherits, rather than adding a ninth.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model



-- WS-RR RR3.3 / RR3.8: `ipcUnwrapCaps_preserves_blockedThreadsPendingMessageConsistent`,
-- `ipcUnwrapCaps_preserves_replyCallerLinkageReciprocal` and the
-- `ipcUnwrapCaps_reply_backward` transport the second rests on, moved UP to
-- `Structural/PerOperation.lean`, beside the other `ipcUnwrapCaps` conjunct
-- frames.  The `*WithCaps` `ipcInvariantFull` bundles (in
-- `Structural/DualQueueMembership.lean`, upstream of this module) now
-- **establish** both conjuncts instead of threading them, and an establisher
-- has to be reachable from the bundle that calls it.  Both rest only on
-- `IPC/Operations/CapTransfer.lean`'s transport drivers, so the move is a
-- relocation, not a re-proof; every consumer here resolves them through the
-- `Structural` import unchanged.

/-- WS-RR RR2.14: the capability transfer preserves
`blockedThreadTimeoutConsistent` — every post-state TCB is its pre-state self,
and a pre-state SchedContext survives the transfer forward. -/
theorem ipcUnwrapCaps_preserves_blockedThreadTimeoutConsistent
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt)
    (hInv : blockedThreadTimeoutConsistent st)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    blockedThreadTimeoutConsistent st' := by
  intro tid tcb scId hTcb' hBudget
  obtain ⟨⟨sc, hSc⟩, hBlk⟩ := hInv tid tcb scId
    (ipcUnwrapCaps_tcb_backward msg senderRoot receiverRoot slotBase grantRight
      st st' summary tid.toObjId tcb hObjInv hStep hTcb') hBudget
  exact ⟨⟨sc, ipcUnwrapCaps_preserves_schedContext_objects msg senderRoot receiverRoot slotBase
    grantRight st st' summary scId.toObjId sc hSc hObjInv hStep⟩, hBlk⟩


/-- **WS-RR RR2.14 / RR2.6: the capability transfer preserves `ipcInvariantFull`.**

All twenty conjuncts are established from the pre-state.  The two that a first
cut threaded — `dualQueueSystemInvariant` and `badgeWellFormed` — already had
their own preservation theorems in the tree
(`ipcUnwrapCaps_preserves_dualQueueSystemInvariant`,
`ipcUnwrapCaps_preserves_badgeWellFormed`); what they need is not a post-state
hypothesis but two *pre*-state side conditions, so they are taken as such:

* `hCn` — the receiver's CSpace root holds a CNode.  The transfer's own loop
  short-circuits (rather than failing) when it does not, so success alone does
  not witness it; the caller resolves the root and knows.
* `hCaps` — every badge carried in the message is valid.  This is a property of
  the syscall's *argument*, not of the state: `badgeWellFormed` constrains
  badges in CNodes and notifications, and says nothing about an `IpcMessage`.

Both are ordinary preconditions on the operation's inputs, categorically unlike
a threaded post-state conjunct: neither can be satisfied by the transition it is
supposed to constrain.

The donation quartet falls out of the two donation frames: the transfer writes no
TCB, so `sameSchedContextBindings` holds outright, and `donationOwnerFrame`
carries the SchedContext and owner readings forward. -/
theorem ipcUnwrapCaps_preserves_ipcInvariantFull
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (cn : CNode)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hCn : st.objects[receiverRoot]? = some (.cnode cn))
    (hCaps : ∀ (i : Nat) (c : TransferCap), msg.caps[i]? = some c →
      ∀ b, c.cap.badge = some b → b.valid)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    ipcInvariantFull st' := by
  have hDualQueue' : dualQueueSystemInvariant st' :=
    ipcUnwrapCaps_preserves_dualQueueSystemInvariant msg senderRoot receiverRoot slotBase
      grantRight st st' summary cn hCn hInv.dualQueueSystemInvariant hObjInv hStep
  have hBadge' : badgeWellFormed st' :=
    ipcUnwrapCaps_preserves_badgeWellFormed msg senderRoot receiverRoot slotBase grantRight
      st st' summary hInv.badgeWellFormed hObjInv hCaps hStep
  have hSame := ipcUnwrapCaps_sameSchedContextBindings msg senderRoot receiverRoot slotBase
    grantRight st st' summary hObjInv hStep
  have hDOV' := donationOwnerValid_of_frames hSame
    (ipcUnwrapCaps_donationOwnerFrame msg senderRoot receiverRoot slotBase grantRight
      st st' summary hObjInv hStep)
    hInv.donationOwnerValid
  exact ⟨ipcUnwrapCaps_preserves_ipcInvariant msg senderRoot receiverRoot slotBase grantRight
      st st' summary hInv.ipcInvariant hObjInv hStep,
    hDualQueue',
    ipcUnwrapCaps_preserves_allPendingMessagesBounded msg senderRoot receiverRoot slotBase
      grantRight st st' summary hObjInv hInv.allPendingMessagesBounded hStep,
    hBadge',
    ipcUnwrapCaps_preserves_blockedThreadsPendingMessageConsistent msg senderRoot receiverRoot
      slotBase grantRight st st' summary hObjInv hInv.blockedThreadsPendingMessageConsistent hStep,
    ipcUnwrapCaps_preserves_endpointQueueNoDup msg senderRoot receiverRoot slotBase grantRight
      st st' summary hObjInv hInv.endpointQueueNoDup hStep,
    ipcUnwrapCaps_preserves_ipcStateQueueMembershipConsistent msg senderRoot receiverRoot
      slotBase grantRight st st' summary hObjInv hInv.ipcStateQueueMembershipConsistent hStep,
    ipcUnwrapCaps_preserves_queueNextBlockingConsistent msg senderRoot receiverRoot slotBase
      grantRight st st' summary hObjInv hInv.queueNextBlockingConsistent hStep,
    ipcUnwrapCaps_preserves_queueHeadBlockedConsistent msg senderRoot receiverRoot slotBase
      grantRight st st' summary hObjInv hInv.queueHeadBlockedConsistent hStep,
    ipcUnwrapCaps_preserves_blockedThreadTimeoutConsistent msg senderRoot receiverRoot slotBase
      grantRight st st' summary hObjInv hInv.blockedThreadTimeoutConsistent hStep,
    donationOwnerValid_implies_donationChainAcyclic st' hDOV', hDOV',
    passiveServerIdle_of_frame
      (ipcUnwrapCaps_passiveServerIdleFrame msg senderRoot receiverRoot slotBase grantRight
        st st' summary hObjInv hStep)
      hInv.passiveServerIdle,
    donationBudgetTransfer_of_sameSchedContextBindings hSame hInv.donationBudgetTransfer,
    ipcUnwrapCaps_preserves_blockedOnReplyHasTarget msg senderRoot receiverRoot slotBase
      grantRight st st' summary hObjInv hInv.blockedOnReplyHasTarget hStep,
    ⟨ipcUnwrapCaps_preserves_replyCallerLinkageReciprocal msg senderRoot receiverRoot slotBase
        grantRight st st' summary hObjInv hInv.replyCallerLinkage.1 hStep,
      ipcUnwrapCaps_preserves_blockedOnReplyHasReplyObject msg senderRoot receiverRoot slotBase
        grantRight st st' summary hObjInv hInv.replyCallerLinkage.2 hStep⟩,
    ipcUnwrapCaps_preserves_pendingReceiveReplyWellFormed msg senderRoot receiverRoot slotBase
      grantRight st st' summary hObjInv hInv.pendingReceiveReplyWellFormed hStep,
    donationOwnerUnique_of_sameSchedContextBindings hSame hInv.donationOwnerUnique,
    ipcUnwrapCaps_preserves_endpointQueueTailBlockedConsistent msg senderRoot receiverRoot
      slotBase grantRight st st' summary hObjInv hInv.endpointQueueTailBlockedConsistent hStep,
    ipcUnwrapCaps_preserves_queueNextTargetBlocked msg senderRoot receiverRoot slotBase
      grantRight st st' summary hObjInv hInv.queueNextTargetBlocked hStep⟩

end SeLe4n.Kernel
