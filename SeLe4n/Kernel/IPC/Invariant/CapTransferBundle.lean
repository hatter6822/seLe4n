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

## What is threaded, and why

Two conjuncts arrive as post-state hypotheses: `dualQueueSystemInvariant` and
`badgeWellFormed`.  Both have real preservation lemmas for this step
(`ipcUnwrapCaps_preserves_dualQueueSystemInvariant`,
`…_preserves_badgeWellFormed`), but each needs a side condition the *caller*
holds — a CNode at the receiver's root, and badge validity of the transferred
capabilities — and the single-core WithCaps bundles this composes with thread
them for exactly that reason.  Discharging them is `IPC_INVARIANT_DETHREADING`
slice D-11, owned by **WS-RR RR3.11** ("de-thread `dualQueueSystemInvariant` /
`badgeWellFormed` at the eight remaining sites"); adding a ninth site here that
threads them keeps this composition honest and does not enlarge that list, since
the sites it serves already threaded them.

Everything else — including `blockedThreadsPendingMessageConsistent` and both
halves of `replyCallerLinkage`, which the single-core WithCaps bundles thread —
is **established** here from the pre-state, because the transfer touches no TCB
and no Reply object at all.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-RR RR2.14: a Reply object present after a capability transfer was present
before it.  The transfer writes the receiver's CSpace root and nothing else
(`ipcUnwrapCaps_preserves_objects_ne`), and the root holds a CNode after the
write, so a post-state Reply is at a different key and reads through.  The
missing sibling of `ipcUnwrapCaps_tcb_backward` / `_endpoint_backward`. -/
theorem ipcUnwrapCaps_reply_backward
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (r : Reply)
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st'))
    (hReply' : st'.objects[oid]? = some (.reply r)) :
    st.objects[oid]? = some (.reply r) := by
  by_cases hNe : oid = receiverRoot
  · rw [hNe] at hReply' ⊢
    rcases ipcUnwrapCaps_objects_at_root_orig_or_cnode msg senderRoot receiverRoot slotBase
      grantRight st st' summary hObjInv hStep with h | ⟨cn, h⟩
    · rw [← h]; exact hReply'
    · rw [h] at hReply'; cases hReply'
  · rw [ipcUnwrapCaps_preserves_objects_ne msg senderRoot receiverRoot slotBase grantRight
      st st' summary oid hNe hObjInv hStep] at hReply'
    exact hReply'

/-- WS-RR RR2.14: the capability transfer preserves
`blockedThreadsPendingMessageConsistent` — it writes no TCB, so every post-state
TCB is its pre-state self (`ipcUnwrapCaps_tcb_backward`). -/
theorem ipcUnwrapCaps_preserves_blockedThreadsPendingMessageConsistent
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt)
    (hInv : blockedThreadsPendingMessageConsistent st)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    blockedThreadsPendingMessageConsistent st' := by
  intro tid tcb hTcb'
  exact hInv tid tcb (ipcUnwrapCaps_tcb_backward msg senderRoot receiverRoot slotBase grantRight
    st st' summary tid.toObjId tcb hObjInv hStep hTcb')

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

/-- WS-RR RR2.14: the capability transfer preserves the **reciprocal** half of
`replyCallerLinkage`.  Neither direction can break: a post-state TCB is its
pre-state self, a pre-state Reply survives forward, and a post-state Reply was
one before (`ipcUnwrapCaps_reply_backward`). -/
theorem ipcUnwrapCaps_preserves_replyCallerLinkageReciprocal
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt)
    (hInv : replyCallerLinkageReciprocal st)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    replyCallerLinkageReciprocal st' := by
  refine ⟨?_, ?_⟩
  · intro tid tcb rid hTcb' hRO
    obtain ⟨r, hr, hrc⟩ := hInv.1 tid tcb rid
      (ipcUnwrapCaps_tcb_backward msg senderRoot receiverRoot slotBase grantRight
        st st' summary tid.toObjId tcb hObjInv hStep hTcb') hRO
    exact ⟨r, ipcUnwrapCaps_preserves_reply_objects msg senderRoot receiverRoot slotBase
      grantRight st st' summary rid.toObjId r hr hObjInv hStep, hrc⟩
  · intro rid r tid hr' hrc
    obtain ⟨tcb, hTcb, hRO, hBlk⟩ := hInv.2 rid r tid
      (ipcUnwrapCaps_reply_backward msg senderRoot receiverRoot slotBase grantRight
        st st' summary rid.toObjId r hObjInv hStep hr') hrc
    exact ⟨tcb, ipcUnwrapCaps_preserves_tcb_objects msg senderRoot receiverRoot slotBase
      grantRight st st' summary tid.toObjId tcb hTcb hObjInv hStep, hRO, hBlk⟩

/-- **WS-RR RR2.14: the capability transfer preserves `ipcInvariantFull`.**

Eighteen of the twenty conjuncts are established from the pre-state; the two
that are not (`dualQueueSystemInvariant`, `badgeWellFormed`) are threaded for
the reason the module docstring gives, and are RR3.11's to discharge.

The donation quartet falls out of the two donation frames: the transfer writes no
TCB, so `sameSchedContextBindings` holds outright, and `donationOwnerFrame`
carries the SchedContext and owner readings forward. -/
theorem ipcUnwrapCaps_preserves_ipcInvariantFull
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBadge' : badgeWellFormed st')
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    ipcInvariantFull st' := by
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
