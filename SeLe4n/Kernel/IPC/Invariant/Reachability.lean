-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-RR RR3.13 — the pre-state side of the de-threaded IPC
-- bundle family: the state predicate their state-shaped hypotheses come from,
-- and the derivations that turn their thread- and queue-shaped ones from
-- assumptions into consequences.  Staged, not experimental: its consumer is
-- the staged payoff tier in `IPC.Invariant.DispatchPayoff` (each quiescence
-- pack's `reachable` field, RR3.23–25; the pending register at
-- `docs/planning/ipc_dethreading_pending.txt` carries zero registrations),
-- and nothing *production* imports it yet — the pair moves to production
-- together when the call-chain surface promotes.

import SeLe4n.Kernel.IPC.Invariant.Structural
import SeLe4n.Kernel.Architecture.Invariant

/-!
# WS-RR RR3.13 — discharging the IPC bundles' pre-state preconditions

De-threading moved the `*_preserves_ipcInvariantFull` family off post-state
conjuncts and onto pre-state hypotheses.  That is the right direction only if
the pre-state hypotheses are actually **dischargeable**; a bundle whose
preconditions nobody can establish is conditional in a different way.

This module is where they are established.  Three kinds appear across the
family, and they are answered differently:

* **State-shaped** — `st.objects.invExt`, `allTimeoutBudgetsNone`,
  `pendingMessageCapBadgesWellFormed`, `ipcInvariantFull` itself.  Collected
  into `ipcReachable`, one predicate per pack discharge, with
  `ipcReachable_default` (RR3.14) showing the boot state satisfies it, so the
  bundle is inhabited rather than vacuous.  Carrying it *along a trace* —
  concluding the pack's components alongside the bundle so the next syscall's
  pack is fed from the last one's conclusion — is the registered WS-DT
  trace-composition debt (`docs/REGISTERED_DEBT.md`, closure target SM10):
  no per-syscall `ipcReachable` preservation theorem exists yet, and the
  payoffs conclude `ipcInvariantFull` alone.

* **Running-caller-shaped** — the freshness and blocking-state conditions about
  the syscall's *own* thread (`hFreshSender`, `hSenderNotRecv`,
  `hSenderNotReply`, `hCallerReady`, …).  These are **not** assumptions about
  the world: a `.ready` thread cannot be an endpoint queue's head or tail,
  because `queueHeadBlockedConsistent` and `endpointQueueTailBlockedConsistent`
  say every head and tail is blocked.  `readyThread_endpointQueueFresh` derives
  the whole conjunction from those two conjuncts.

* **Queue-tail-shaped** — `hSendTailFresh` / `hRecvTailFresh`, that an endpoint's
  outgoing queue tail is not simultaneously some *other* queue's tail.  Also not
  an assumption: a tail is blocked on the queue it tails, a thread has one
  `ipcState`, and the two directions carry different constructors and different
  endpoint ids.  `sendTailCrossQueueFresh` / `recvTailCrossQueueFresh` derive
  them from `ipcInvariantFull` alone.

What this module deliberately does **not** claim is the argument-shaped
conditions (`messageCapBadgesValid msg`, reply-object freshness): those are
about a syscall's arguments, not about the state, and belong to whatever
resolves those arguments.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The state-shaped preconditions
-- ============================================================================

/-- WS-RR RR3.13: the state-shaped preconditions of the de-threaded IPC bundle
family, as one predicate.

`ipcInvariantFull` is the bundle the family preserves; the other four are the
side conditions its members read of their pre-state and nothing establishes for
them.  `objects.invExt` is the object store's own extended invariant (every
`storeObject` frame needs it), `allTimeoutBudgetsNone` is what
`blockedThreadTimeoutConsistent` is established from,
`pendingMessageCapBadgesWellFormed` is the in-flight badge property the
capability transfer installs from, and `notificationWaiterConsistent` is the
notification bundles' companion.

**WS-OD OD2.6**: `donationChainWellFormed` joins them.  The SchedContext
donation chain — `SchedContext.scReply` heading a `prev`-linked stack of Reply
objects — is a state-shaped precondition of exactly this kind: the donation
return validates the link it follows against the target's own `donatedSc`, and
that validation is only *sound* if the stack is acyclic, every member names the
same context, and the context's head is the whole of its stack.  It is a
conjunct **here** rather than of `ipcInvariantFull`, which has exactly twenty
conjuncts and a theorem family whose size a Tier-0 gate holds equal to the prose
quoting it; and it is *preserved* rather than assumed — `donationChainFrame`
(`IPC.Invariant.Defs`) is what every transition discharges it through, so it is
an invariant rather than a hypothesis wearing an invariant's name. -/
def ipcReachable (st : SystemState) : Prop :=
  ipcInvariantFull st ∧
  st.objects.invExt ∧
  allTimeoutBudgetsNone st ∧
  pendingMessageCapBadgesWellFormed st ∧
  notificationWaiterConsistent st ∧
  donationChainWellFormed st

namespace ipcReachable

theorem ipcInvariantFull {st : SystemState} (h : ipcReachable st) :
    _root_.SeLe4n.Kernel.ipcInvariantFull st := h.1
theorem objects_invExt {st : SystemState} (h : ipcReachable st) :
    st.objects.invExt := h.2.1
theorem allTimeoutBudgetsNone {st : SystemState} (h : ipcReachable st) :
    _root_.SeLe4n.Kernel.allTimeoutBudgetsNone st := h.2.2.1
theorem pendingMessageCapBadgesWellFormed {st : SystemState} (h : ipcReachable st) :
    _root_.SeLe4n.Kernel.pendingMessageCapBadgesWellFormed st := h.2.2.2.1
theorem notificationWaiterConsistent {st : SystemState} (h : ipcReachable st) :
    _root_.SeLe4n.Kernel.notificationWaiterConsistent st := h.2.2.2.2.1
/-- WS-OD OD2.6: the SchedContext donation chain is well formed. -/
theorem donationChainWellFormed {st : SystemState} (h : ipcReachable st) :
    _root_.SeLe4n.Kernel.donationChainWellFormed st := h.2.2.2.2.2

end ipcReachable

-- ============================================================================
-- §2  The running caller is fresh — derived, not assumed
-- ============================================================================

/-- WS-RR RR3.13: **a `.ready` thread is no endpoint queue's head or tail.**

This is the `hFreshSender` / `hFreshReceiver` / `hFreshCaller` hypothesis every
enqueueing bundle carries, and it is a consequence rather than an assumption:
`queueHeadBlockedConsistent` says an endpoint's head is blocked on that endpoint,
`endpointQueueTailBlockedConsistent` says the same of its tail, and `.ready` is
none of those states.

The syscall caller is `.ready` by construction — it is the thread the kernel was
entered on — so every enqueueing IPC bundle's freshness precondition is
discharged by this lemma at the dispatch layer. -/
theorem readyThread_endpointQueueFresh
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hHead : queueHeadBlockedConsistent st)
    (hTail : endpointQueueTailBlockedConsistent st)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hReady : tcb.ipcState = .ready) :
    ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some tid ∧ ep.sendQ.tail ≠ some tid ∧
      ep.receiveQ.head ≠ some tid ∧ ep.receiveQ.tail ≠ some tid := by
  intro epId ep hEp
  obtain ⟨hRecvHead, hSendHead⟩ := hHead epId ep tid tcb hEp hTcb
  obtain ⟨hRecvTail, hSendTail⟩ := hTail epId ep tid tcb hEp hTcb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; rcases hSendHead h with hs | hs <;> rw [hReady] at hs <;> cases hs
  · intro h; rcases hSendTail h with hs | hs <;> rw [hReady] at hs <;> cases hs
  · intro h; have := hRecvHead h; rw [hReady] at this; cases this
  · intro h; have := hRecvTail h; rw [hReady] at this; cases this

/-- WS-RR RR3.13: a `.ready` thread is not parked to collect — the
`hSenderNotRecv` / `hReceiverNotRecv` hypothesis. -/
theorem readyThread_notBlockedOnReceive
    (tcb : TCB) (hReady : tcb.ipcState = .ready) :
    ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep := by
  intro ep h; rw [hReady] at h; cases h

/-- WS-RR RR3.13: a `.ready` thread is not awaiting a reply — the
`hSenderNotReply` / `hCallerNotReply` hypothesis. -/
theorem readyThread_notBlockedOnReply
    (tcb : TCB) (hReady : tcb.ipcState = .ready) :
    ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt := by
  intro ep rt h; rw [hReady] at h; cases h

/-- WS-RR RR3.13: **nothing is donated by a `.ready` thread** — the
`hNoDonationOwnedBy` hypothesis the reply bundles carry.

A donation owner is `.blockedOnReply` (`donationOwnerValid`), which the caller
of a syscall is not.  So on the non-donating reply path the condition is not an
extra assumption about the world either; it is `.ready` again. -/
theorem readyThread_ownsNoDonation
    (st : SystemState) (woken : SeLe4n.ThreadId) (wokenTcb : TCB)
    (hDOV : donationOwnerValid st)
    (hTcb : st.objects[woken.toObjId]? = some (.tcb wokenTcb))
    (hReady : wokenTcb.ipcState = .ready) :
    ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .donated scId woken := by
  intro tid tcb scId hT hBind
  obtain ⟨_, ownerTcb, hOwner, _, ep, rt, hBlk⟩ := hDOV tid tcb scId woken hT hBind
  rw [hTcb] at hOwner
  obtain rfl := KernelObject.tcb.inj (Option.some.inj hOwner)
  rw [hReady] at hBlk
  cases hBlk

-- ============================================================================
-- §3  Queue tails are not shared — derived, not assumed
-- ============================================================================

/-- WS-RR RR3.13: **an endpoint's send-queue tail tails nothing else.**

This is the `hSendTailFresh` hypothesis, and like the freshness one it follows
from the bundle itself.  A send-queue tail is `.blockedOnSend`/`.blockedOnCall`
on *its* endpoint (`endpointQueueTailBlockedConsistent`); a receive-queue tail is
`.blockedOnReceive` on its own; a thread has one `ipcState`; and the blocking
states carry the endpoint id, so two different endpoints cannot both claim it.

The tail's TCB comes from `dualQueueSystemInvariant`'s tail boundary, so nothing
has to be assumed about the queue's contents either. -/
theorem sendTailCrossQueueFresh
    (st : SystemState) (endpointId : SeLe4n.ObjId)
    (hDQSI : dualQueueSystemInvariant st)
    (hTail : endpointQueueTailBlockedConsistent st) :
    ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid) := by
  intro ep tailTid hEp hTl epId' ep' hEp'
  -- The tail resolves to a TCB, from the dual-queue tail boundary.
  have hWf := hDQSI.1 endpointId ep hEp
  unfold dualQueueEndpointWellFormed at hWf
  rw [hEp] at hWf
  obtain ⟨tcb, hTcb, _⟩ := hWf.1.2.2 tailTid hTl
  -- It is `.blockedOnSend`/`.blockedOnCall` on `endpointId`.
  have hSend := (hTail endpointId ep tailTid tcb hEp hTcb).2 hTl
  refine ⟨fun hNe => ⟨?_, ?_⟩, fun _ => ?_⟩
  · intro hOther
    have hOtherSend := (hTail epId' ep' tailTid tcb hEp' hTcb).2 hOther
    apply hNe
    rcases hSend with hs | hs <;> rcases hOtherSend with ho | ho
    · have hEq := hs.symm.trans ho; simp at hEq; exact hEq.symm
    · have hEq := hs.symm.trans ho; simp at hEq
    · have hEq := hs.symm.trans ho; simp at hEq
    · have hEq := hs.symm.trans ho; simp at hEq; exact hEq.symm
  · intro hOther
    have hOtherRecv := (hTail epId' ep' tailTid tcb hEp' hTcb).1 hOther
    rcases hSend with hs | hs <;> · have hEq := hs.symm.trans hOtherRecv; simp at hEq
  · intro hOther
    have hOtherRecv := (hTail epId' ep' tailTid tcb hEp' hTcb).1 hOther
    rcases hSend with hs | hs <;> · have hEq := hs.symm.trans hOtherRecv; simp at hEq

/-- WS-RR RR3.13: the receive-side dual of `sendTailCrossQueueFresh` — the
`hRecvTailFresh` hypothesis, likewise derived from the bundle. -/
theorem recvTailCrossQueueFresh
    (st : SystemState) (endpointId : SeLe4n.ObjId)
    (hDQSI : dualQueueSystemInvariant st)
    (hTail : endpointQueueTailBlockedConsistent st) :
    ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid) := by
  intro ep tailTid hEp hTl epId' ep' hEp'
  have hWf := hDQSI.1 endpointId ep hEp
  unfold dualQueueEndpointWellFormed at hWf
  rw [hEp] at hWf
  obtain ⟨tcb, hTcb, _⟩ := hWf.2.2.2 tailTid hTl
  have hRecv := (hTail endpointId ep tailTid tcb hEp hTcb).1 hTl
  refine ⟨fun hNe => ⟨?_, ?_⟩, fun _ => ?_⟩
  · intro hOther
    have hOtherSend := (hTail epId' ep' tailTid tcb hEp' hTcb).2 hOther
    rcases hOtherSend with ho | ho <;> · have hEq := hRecv.symm.trans ho; simp at hEq
  · intro hOther
    have hOtherRecv := (hTail epId' ep' tailTid tcb hEp' hTcb).1 hOther
    apply hNe
    have hEq := hRecv.symm.trans hOtherRecv
    simp at hEq
    exact hEq.symm
  · intro hOther
    have hOtherSend := (hTail epId' ep' tailTid tcb hEp' hTcb).2 hOther
    rcases hOtherSend with ho | ho <;> · have hEq := hRecv.symm.trans ho; simp at hEq

-- ============================================================================
-- §4  RR3.14 — the bundle is inhabited
-- ============================================================================

/-- WS-RR RR3.14: **the boot state is `ipcReachable`.**

An inhabitation witness, and the reason this module is a bundle rather than a
list of hypotheses: without it `ipcReachable` could be an unsatisfiable
conjunction and every theorem taking it would be vacuous — the failure shape the
whole de-threading phase exists to remove, reintroduced one level up.

Every conjunct is discharged from the empty boot object store, the IPC bundle
through the architecture layer's `default_ipcInvariantFull`. -/
theorem ipcReachable_default : ipcReachable (default : SystemState) := by
  refine ⟨Architecture.default_ipcInvariantFull, ?_, ?_, ?_,
    default_notificationWaiterConsistent, ?_⟩
  · exact capabilityInvariantBundle.objectsInvExt
      (Architecture.default_system_state_proofLayerInvariantBundle).2.1
  · intro tid tcb hTcb
    rw [Architecture.default_objects_none] at hTcb
    cases hTcb
  · intro tid tcb m hTcb
    rw [Architecture.default_objects_none] at hTcb
    cases hTcb
  · -- WS-OD OD2.6: the empty boot store holds no Reply and no SchedContext, so
    -- the chain invariant holds with nothing to walk.
    refine donationChainWellFormed_of_no_reply_or_schedContext _ ?_ ?_
    · intro rid r hR
      rw [Architecture.default_objects_none] at hR
      cases hR
    · intro scId sc hSc
      rw [Architecture.default_objects_none] at hSc
      cases hSc

-- ============================================================================
-- §5  WS-OD OD2.4 — the chain predicate decides rather than refuses
-- ============================================================================

/-! `donationChainWellFormed` is *vacuously* true of every state this tree
reaches today.  The one transition that writes `Reply.donatedSc`, `Reply.prev`
and `SchedContext.scReply` is the donation pop, and its writing arm needs a
context that already heads a reply stack — which nothing constructs until OD4's
push.  So every discharge in the tree is one of the two vacuous
constructors: `ipcReachable_default` uses
`donationChainWellFormed_of_no_reply_or_schedContext` (the empty boot store holds
neither kind), and the two dispatch-pack witnesses use
`donationChainWellFormed_of_no_donations` (their store holds both kinds, and
neither carries a link).

A predicate discharged only vacuously is one nobody has checked against the
structure it exists to constrain, and an **over-strong** conjunct looks exactly
the same from that side: the obligation never fires, so it never fails.  That is
the failure this file exists to remove, one level down — the same argument
`ipcReachable_default` makes for the bundle.

So the witness below builds the state a depth-2 Call chain leaves — one
scheduling context heading two `prev`-linked Reply objects, both naming it — and
proves the **whole** predicate of it, the completeness clause included.  With
`donationChainWellFormed_of_no_donations` on one side and this on the other, the
predicate is known to admit both the state the tree has today and the state OD3
and OD4 will produce, so neither the pop nor the push is walking into a
conjunct that refuses its own subject. -/

/-- The scheduling context donated down the witness chain. -/
def donationChainWitnessContext : SeLe4n.SchedContextId := ⟨11⟩

/-- The **inner** call's Reply — the head of the stack. -/
def donationChainWitnessInner : SeLe4n.ReplyId := ⟨12⟩

/-- The **outer** call's Reply — the reply below the head. -/
def donationChainWitnessOuter : SeLe4n.ReplyId := ⟨13⟩

/-- The witness's scheduling context, heading the inner call's reply.  Public
because a consumer of the witness needs its objects: WS-OD OD3.8 pops this stack
and re-proves the chain invariant of the result, which is what keeps the pop's
preservation theorem from being exercised only on the `head? = none` arm. -/
def witnessChainSchedContext : SchedContext :=
  { SchedContext.empty donationChainWitnessContext with
      scReply := some donationChainWitnessInner }

/-- The witness's inner (head) reply: donates the context, links down to the
outer one.  Public for the same reason as `witnessChainSchedContext`. -/
def witnessChainInnerReply : Reply :=
  { replyId := donationChainWitnessInner,
    donatedSc := some donationChainWitnessContext,
    prev := some donationChainWitnessOuter }

/-- The witness's outer reply: donates the context and is the bottom of the
stack.  Public for the same reason as `witnessChainSchedContext`. -/
def witnessChainOuterReply : Reply :=
  { replyId := donationChainWitnessOuter,
    donatedSc := some donationChainWitnessContext }

private def chainWitnessSt1 : SystemState :=
  { (default : SystemState) with
    objects := (default : SystemState).objects.insert
      donationChainWitnessContext.toObjId (.schedContext witnessChainSchedContext) }

private def chainWitnessSt2 : SystemState :=
  { chainWitnessSt1 with
    objects := chainWitnessSt1.objects.insert
      donationChainWitnessOuter.toObjId (.reply witnessChainOuterReply) }

/-- WS-OD OD2.4: the state a depth-2 Call chain leaves — the context heads the
inner call's reply, which links down to the outer call's, and both replies name
the context they carry. -/
def donationChainWitness : SystemState :=
  { chainWitnessSt2 with
    objects := chainWitnessSt2.objects.insert
      donationChainWitnessInner.toObjId (.reply witnessChainInnerReply) }

private theorem chainWitnessObjInv0 : (default : SystemState).objects.invExt :=
  capabilityInvariantBundle.objectsInvExt
    (Architecture.default_system_state_proofLayerInvariantBundle).2.1

private theorem chainWitnessObjInv1 : chainWitnessSt1.objects.invExt :=
  RHTable_insert_preserves_invExt _ _ _ chainWitnessObjInv0

private theorem chainWitnessObjInv2 : chainWitnessSt2.objects.invExt :=
  RHTable_insert_preserves_invExt _ _ _ chainWitnessObjInv1

private theorem chainWitnessSt1_lookup (oid : SeLe4n.ObjId) :
    chainWitnessSt1.objects[oid]?
      = if donationChainWitnessContext.toObjId == oid
        then some (.schedContext witnessChainSchedContext) else none := by
  show ((default : SystemState).objects.insert donationChainWitnessContext.toObjId
      (.schedContext witnessChainSchedContext))[oid]? = _
  rw [RHTable_getElem?_eq_get?, RHTable_getElem?_insert _ _ _ chainWitnessObjInv0]
  split
  · rfl
  · rw [← RHTable_getElem?_eq_get?, Architecture.default_objects_none]

private theorem chainWitnessSt2_lookup (oid : SeLe4n.ObjId) :
    chainWitnessSt2.objects[oid]?
      = if donationChainWitnessOuter.toObjId == oid
        then some (.reply witnessChainOuterReply)
        else chainWitnessSt1.objects[oid]? := by
  show (chainWitnessSt1.objects.insert donationChainWitnessOuter.toObjId
      (.reply witnessChainOuterReply))[oid]? = _
  rw [RHTable_getElem?_eq_get?, RHTable_getElem?_insert _ _ _ chainWitnessObjInv1]
  split
  · rfl
  · rw [← RHTable_getElem?_eq_get?]

private theorem donationChainWitness_lookup (oid : SeLe4n.ObjId) :
    donationChainWitness.objects[oid]?
      = if donationChainWitnessInner.toObjId == oid
        then some (.reply witnessChainInnerReply)
        else chainWitnessSt2.objects[oid]? := by
  show (chainWitnessSt2.objects.insert donationChainWitnessInner.toObjId
      (.reply witnessChainInnerReply))[oid]? = _
  rw [RHTable_getElem?_eq_get?, RHTable_getElem?_insert _ _ _ chainWitnessObjInv2]
  split
  · rfl
  · rw [← RHTable_getElem?_eq_get?]

/-- Every object in the witness store, by key: the three the chain needs and
nothing else.  Public since WS-OD OD3.8, which pops the witness's stack and needs
to read the store back at the two keys the pop writes. -/
theorem donationChainWitness_lookup_cases (oid : SeLe4n.ObjId) :
    donationChainWitness.objects[oid]?
      = if donationChainWitnessInner.toObjId == oid
        then some (.reply witnessChainInnerReply)
        else if donationChainWitnessOuter.toObjId == oid
        then some (.reply witnessChainOuterReply)
        else if donationChainWitnessContext.toObjId == oid
        then some (.schedContext witnessChainSchedContext)
        else none := by
  rw [donationChainWitness_lookup, chainWitnessSt2_lookup, chainWitnessSt1_lookup]

/-- WS-OD OD3.8: the witness's object store is well formed as a table.  Every
store-level lemma the pop composes takes this, so exposing it is what makes the
witness usable as the pop's *input* rather than only as a state that satisfies
the predicate. -/
theorem donationChainWitness_objects_invExt : donationChainWitness.objects.invExt :=
  RHTable_insert_preserves_invExt _ _ _ chainWitnessObjInv2

/-- WS-OD OD2.4: the walk from the context's own head yields the whole stack,
innermost first — the positive half of the chain's meaning, computed rather than
asserted. -/
theorem donationChainWitness_chain :
    donationChainFrom donationChainWitness donationChainWitnessContext 2
        witnessChainSchedContext.scReply
      = some [donationChainWitnessInner, donationChainWitnessOuter] := by
  have hInner : replyStackLinksAt? donationChainWitness donationChainWitnessInner
      = some (some donationChainWitnessContext, some donationChainWitnessOuter) := by
    unfold replyStackLinksAt?
    rw [donationChainWitness_lookup_cases]
    simp [replyStackLinks?, witnessChainInnerReply]
  have hOuter : replyStackLinksAt? donationChainWitness donationChainWitnessOuter
      = some (some donationChainWitnessContext, none) := by
    unfold replyStackLinksAt?
    rw [donationChainWitness_lookup_cases]
    simp [replyStackLinks?, witnessChainOuterReply,
      show (donationChainWitnessInner.toObjId == donationChainWitnessOuter.toObjId) = false from
        by decide]
  have hTail : donationChainFrom donationChainWitness donationChainWitnessContext 1
      (some donationChainWitnessOuter) = some [donationChainWitnessOuter] := by
    rw [donationChainFrom_succ, hOuter]; simp
  show donationChainFrom donationChainWitness donationChainWitnessContext 2
      (some donationChainWitnessInner) = _
  rw [donationChainFrom_succ, hInner]
  simp [hTail]

/-- WS-OD OD2.4: **the depth-2 chain satisfies the whole predicate.**  The
completeness clause is the substantive one: the two replies naming the context
are exactly the two the walk returns, so `donatedSc = some scId` and "on `scId`'s
stack" are the same statement on this state — which is what the donation return's
link validation relies on. -/
theorem donationChainWitness_wellFormed :
    donationChainWellFormed donationChainWitness := by
  have hInnerNe : (donationChainWitnessInner.toObjId
      == donationChainWitnessContext.toObjId) = false := by decide
  have hOuterNe : (donationChainWitnessOuter.toObjId
      == donationChainWitnessContext.toObjId) = false := by decide
  refine ⟨?_, ?_, ?_⟩
  · -- Every stored Reply carries a donation, so `Reply.wellFormed` is immediate.
    intro rid r hR
    rw [donationChainWitness_lookup_cases] at hR
    split at hR
    · cases hR; intro hNone; simp [witnessChainInnerReply] at hNone
    · split at hR
      · cases hR; intro hNone; simp [witnessChainOuterReply] at hNone
      · split at hR
        · cases hR
        · cases hR
  · -- Both replies name the context, and the store holds it.
    intro rid r scId hR hDon
    have hScId : scId = donationChainWitnessContext := by
      rw [donationChainWitness_lookup_cases] at hR
      split at hR
      · cases hR; simp [witnessChainInnerReply] at hDon; exact hDon.symm
      · split at hR
        · cases hR; simp [witnessChainOuterReply] at hDon; exact hDon.symm
        · split at hR
          · cases hR
          · cases hR
    subst hScId
    refine ⟨witnessChainSchedContext, ?_⟩
    rw [donationChainWitness_lookup_cases]
    simp [hInnerNe, hOuterNe]
  · -- The context's head walks the whole stack, and the stack holds exactly the
    -- replies naming the context.
    intro scId sc hSc
    have hEq : scId = donationChainWitnessContext ∧ sc = witnessChainSchedContext := by
      rw [donationChainWitness_lookup_cases] at hSc
      split at hSc
      · cases hSc
      · split at hSc
        · cases hSc
        · split at hSc
          · next hKey =>
            cases hSc
            exact ⟨(SeLe4n.SchedContextId.toObjId_injective _ _ (eq_of_beq hKey)).symm, rfl⟩
          · cases hSc
    obtain ⟨rfl, rfl⟩ := hEq
    refine ⟨2, [donationChainWitnessInner, donationChainWitnessOuter],
      donationChainWitness_chain, ?_⟩
    intro rid r hR _
    rw [donationChainWitness_lookup_cases] at hR
    split at hR
    · next hKey =>
      have hRid : rid = donationChainWitnessInner :=
        (SeLe4n.ReplyId.toObjId_injective _ _ (eq_of_beq hKey)).symm
      subst hRid
      simp
    · split at hR
      · next hKey =>
        have hRid : rid = donationChainWitnessOuter :=
          (SeLe4n.ReplyId.toObjId_injective _ _ (eq_of_beq hKey)).symm
        subst hRid
        simp
      · split at hR
        · cases hR
        · cases hR

end SeLe4n.Kernel
