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
import SeLe4n.Kernel.InformationFlow.Invariant.Composition
import SeLe4n.Kernel.IPC.CrossCore.ReplyWaitersDispatch

/-!
# WS-RR RR3.13 — discharging the IPC bundles' pre-state preconditions

De-threading moved the `*_preserves_ipcInvariantFull` family off post-state
conjuncts and onto pre-state hypotheses.  That is the right direction only if
the pre-state hypotheses are actually **dischargeable**; a bundle whose
preconditions nobody can establish is conditional in a different way.

This module is where they are established.  Three kinds appear across the
family, and they are answered differently:

* **State-shaped** — `st.objects.invExt`, `allTimeoutBudgetsNone`,
  `ipcInvariantFull` itself.  Collected
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
conditions (reply-object freshness): those are about a syscall's arguments,
not about the state, and belong to whatever resolves those arguments.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The state-shaped preconditions
-- ============================================================================

/-- WS-RR RR3.13: the state-shaped preconditions of the de-threaded IPC bundle
family, as one predicate.

`ipcInvariantFull` is the bundle the family preserves; the other three are the
side conditions its members read of their pre-state and nothing establishes for
them.  `objects.invExt` is the object store's own extended invariant (every
`storeObject` frame needs it), `allTimeoutBudgetsNone` is what
`blockedThreadTimeoutConsistent` is established from, and
`notificationWaiterConsistent` is the notification bundles' companion.  There is
no in-flight badge condition: a message holds no capability, so the capability
transfer installs only what it resolves from a CNode at the rendezvous, whose
badges `badgeWellFormed` already bounds.

**WS-OD OD2.6**: `donationChainWellFormed` joins them.  The SchedContext
donation chain — `SchedContext.scReply` heading a doubly-linked stack of Reply
objects (`Reply.prev` down, `Reply.next` up, since `v0.35.4`) — is a state-shaped
precondition of exactly this kind: the donation return validates the link it
follows against the frame's own **upward** link (`Reply.next = some (.frame …)`,
`replyStackOuterCaller?`), and
that validation is only *sound* if the stack is acyclic, every member names the
same context, and the context's head is the whole of its stack.  It is a
conjunct **here** rather than of `ipcInvariantFull`, which has exactly twenty
conjuncts and a theorem family whose size a Tier-0 gate holds equal to the prose
quoting it; and it is *preserved* rather than assumed — `donationChainFrame`
(`IPC.Invariant.Defs`) is what every transition discharges it through, so it is
an invariant rather than a hypothesis wearing an invariant's name.

**WS-ZA ZA4.5**: `runQueueRefined` joins them on the same terms.  Every core's
run queue agrees with the run-queue links its threads carry, and every kernel
entry keeps it: each one is a `RunQueueStage` (`IPC.Invariant.RunQueueAgreement`),
so the agreement the dispatch reads is carried, not assumed.

**WS-ZA ZA4.6**: `replyWaitersConsistent` joins them.  Every server's reply-waiter
queue, linked through its waiters' TCBs, is exactly the threads reply-blocked on
it, so priority inheritance reads its waiters off the links.  Each transition that
links or unlinks a waiter, and each live IPC arm around it, keeps it
(`IPC.CrossCore.ReplyWaitersPreservation`, `…Cancellation`, `…Dispatch`). -/
def ipcReachable (st : SystemState) : Prop :=
  ipcInvariantFull st ∧
  st.objects.invExt ∧
  allTimeoutBudgetsNone st ∧
  notificationWaiterConsistent st ∧
  donationChainWellFormed st ∧
  st.runQueueRefined ∧
  st.replyWaitersConsistent

namespace ipcReachable

theorem ipcInvariantFull {st : SystemState} (h : ipcReachable st) :
    _root_.SeLe4n.Kernel.ipcInvariantFull st := h.1
theorem objects_invExt {st : SystemState} (h : ipcReachable st) :
    st.objects.invExt := h.2.1
theorem allTimeoutBudgetsNone {st : SystemState} (h : ipcReachable st) :
    _root_.SeLe4n.Kernel.allTimeoutBudgetsNone st := h.2.2.1
theorem notificationWaiterConsistent {st : SystemState} (h : ipcReachable st) :
    _root_.SeLe4n.Kernel.notificationWaiterConsistent st := h.2.2.2.1
/-- WS-OD OD2.6: the SchedContext donation chain is well formed. -/
theorem donationChainWellFormed {st : SystemState} (h : ipcReachable st) :
    _root_.SeLe4n.Kernel.donationChainWellFormed st := h.2.2.2.2.1
/-- WS-ZA ZA4.5: every core's run queue agrees with the threads' run-queue links. -/
theorem runQueueRefined {st : SystemState} (h : ipcReachable st) : st.runQueueRefined :=
  h.2.2.2.2.2.1
/-- WS-ZA ZA4.6: every server's reply-waiter queue is consistent with its waiters. -/
theorem replyWaitersConsistent {st : SystemState} (h : ipcReachable st) :
    st.replyWaitersConsistent :=
  h.2.2.2.2.2.2

end ipcReachable

-- ============================================================================
-- §1b  `v0.35.196` (register row 183, part 2) — the labelled pre-state pack
-- ============================================================================

/-- **WS-RR RR8.16 (`v0.35.196`): the reachable pack under a labelling.**

`ipcReachable` collects the state-shaped preconditions of the IPC bundle family,
and the three **flow** facts (`InformationFlow/Invariant/Composition.lean`) are
state-shaped preconditions of exactly the same kind — what a gate checked at the
transition and the store records no trace of.  They could not be conjuncts of it
for one reason: they are parametrised by a `LabelingContext` and `ipcReachable` is
not, so adding them would make every existing consumer carry a `ctx` it does not
use.

So this is an **opt-in extension** rather than a widening: a consumer that reasons
about flows asks for `ipcReachableUnder ctx`, a consumer that does not keeps
`ipcReachable`, and `.reachable` projects one to the other.  That is the shape
register row 183's part (2) named as the decision, and taking it this way is what
makes it a decision rather than a cost imposed on every caller.

What it does **not** yet carry is preservation along a trace — no
`ipcReachableUnder` preservation theorem exists, exactly as none exists for
`ipcReachable` itself (the WS-DT trace-composition debt).  What the per-arm lifts
in `IPC/Invariant/BlockedSenderPreservation.lean` give is each conjunct across one
transition, which is what a consumer composes by hand until that debt closes. -/
def ipcReachableUnder (ctx : LabelingContext) (st : SystemState) : Prop :=
  ipcReachable st ∧
  blockedSenderFlowsToEndpoint ctx st ∧
  blockedReceiverFlowsFromEndpoint ctx st ∧
  donationOwnerFlowsToHolder ctx st

namespace ipcReachableUnder

/-- Project the unlabelled pack: a consumer that reasons about no flow keeps the
hypothesis it already had. -/
theorem reachable {ctx : LabelingContext} {st : SystemState}
    (h : ipcReachableUnder ctx st) : ipcReachable st := h.1

theorem blockedSenders {ctx : LabelingContext} {st : SystemState}
    (h : ipcReachableUnder ctx st) :
    _root_.SeLe4n.Kernel.blockedSenderFlowsToEndpoint ctx st := h.2.1

theorem blockedReceivers {ctx : LabelingContext} {st : SystemState}
    (h : ipcReachableUnder ctx st) :
    _root_.SeLe4n.Kernel.blockedReceiverFlowsFromEndpoint ctx st := h.2.2.1

theorem donationFlow {ctx : LabelingContext} {st : SystemState}
    (h : ipcReachableUnder ctx st) :
    _root_.SeLe4n.Kernel.donationOwnerFlowsToHolder ctx st := h.2.2.2

end ipcReachableUnder

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
  refine ⟨Architecture.default_ipcInvariantFull, ?_, ?_,
    default_notificationWaiterConsistent, ?_, SystemState.default_runQueueRefined,
    SystemState.replyWaitersConsistent_of_idle fun k v hv => ?_⟩
  · exact capabilityInvariantBundle.objectsInvExt
      (Architecture.default_system_state_proofLayerInvariantBundle).2.1
  · intro tid tcb hTcb
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
  · -- WS-ZA ZA4.6: the empty boot store holds no thread, so no view.
    unfold SystemState.replyViews SystemState.getObject? at hv
    rw [Architecture.default_objects_none] at hv
    cases hv

/-- **WS-RR RR8.16 (`v0.35.196`)**: and the labelled pack is inhabited too, under
**every** labelling.

The three flow facts are all quantified over a *blocked* or *donating* thread and
the empty boot store holds none, so each is vacuous rather than cheap — which is
what makes the pack a bundle rather than an unsatisfiable conjunction, for the
reason `ipcReachable_default` gives one level down.  Stated for an arbitrary `ctx`
because the boot state's emptiness is what discharges it, not anything about the
labelling: a deployment's own context is admitted by the boot's witness check
(`isInsecureDefaultContext`), which is a different question from this one. -/
theorem ipcReachableUnder_default (ctx : LabelingContext) :
    ipcReachableUnder ctx (default : SystemState) := by
  refine ⟨ipcReachable_default, ?_, ?_, ?_⟩
  · refine blockedSenderFlowsToEndpoint_of_none_blocked ?_
    intro tid tcb epId hLook
    rw [lookupTcb] at hLook
    split at hLook
    · cases hLook
    · rw [SystemState.getTcb?, Architecture.default_objects_none] at hLook
      cases hLook
  · refine blockedReceiverFlowsFromEndpoint_of_none_blocked ?_
    intro tid tcb epId hLook
    rw [lookupTcb] at hLook
    split at hLook
    · cases hLook
    · rw [SystemState.getTcb?, Architecture.default_objects_none] at hLook
      cases hLook
  · intro holder owner scId hRet
    unfold replyDonationReturn? at hRet
    rw [show lookupTcb (default : SystemState) holder = none from by
          rw [lookupTcb]
          split
          · rfl
          · rw [SystemState.getTcb?, Architecture.default_objects_none]] at hRet
    exact absurd hRet (by simp)

-- ============================================================================
-- §5  WS-OD OD2.4 — the chain predicate decides rather than refuses
-- ============================================================================

/-! **When this section was written** (OD2.4, `v0.34.125`)
`donationChainWellFormed` was *vacuously* true of every state the tree reached:
the one transition writing a Reply's stack links and
`SchedContext.scReply` was the donation pop, whose writing arm needs a context
that already heads a reply stack, and nothing constructed one.  Every discharge
was therefore one of the two vacuous constructors — `ipcReachable_default` uses
`donationChainWellFormed_of_no_reply_or_schedContext` (the empty boot store holds
neither kind) and the two dispatch-pack witnesses use
`donationChainWellFormed_of_no_donations` (their store holds both kinds, and
neither carries a link).  **OD4.1 (`v0.35.2`) ended that**: `donationHeadPush`
builds a frame on every donating `Call`, so a depth-2 chain is an ordinary
reachable state and the completeness clause below fires on it.  The two vacuous
discharges remain correct for the *states they are about* — a boot store and two
link-free pack witnesses — and this section's argument is unchanged, which is the
point of having made it before the push existed.

A predicate discharged only vacuously is one nobody has checked against the
structure it exists to constrain, and an **over-strong** conjunct looks exactly
the same from that side: the obligation never fires, so it never fails.  That is
the failure this file exists to remove, one level down — the same argument
`ipcReachable_default` makes for the bundle.

So the witness below builds the state a depth-2 Call chain leaves — one
scheduling context heading two doubly-linked Reply objects (`v0.35.4`: the head's
`next` names the context, the frame below it answers the head with `.frame`, and
each frame's `prev` names the one below) — and proves the **whole** predicate of
it, every reciprocity clause included.  With
`donationChainWellFormed_of_no_donations` on one side and this on the other, the
predicate is known to admit both the link-free state and the depth-2 state OD3's
pop and OD4's push produce, so neither is walking into a conjunct that refuses
its own subject. -/

/-- The scheduling context donated down the witness chain. -/
def donationChainWitnessContext : SeLe4n.SchedContextId := ⟨11⟩

/-- The **inner** call's Reply — the head of the stack. -/
def donationChainWitnessInner : SeLe4n.ReplyId := ⟨12⟩

/-- The **outer** call's Reply — the reply below the head. -/
def donationChainWitnessOuter : SeLe4n.ReplyId := ⟨13⟩

/-- The outer call's caller — the client at the bottom of the chain.  A Reply on
a stack has a caller (`Reply.wellFormed`), so the witness frames name one; any two
distinct ids off the three object ids above will do for the predicate. -/
def donationChainWitnessOuterCaller : SeLe4n.ThreadId := ⟨14⟩

/-- The inner call's caller — the intermediate server, calling onward. -/
def donationChainWitnessInnerCaller : SeLe4n.ThreadId := ⟨15⟩

/-- The witness's scheduling context, heading the inner call's reply.  Public
because a consumer of the witness needs its objects: WS-OD OD3.8 pops this stack
and re-proves the chain invariant of the result, which is what keeps the pop's
preservation theorem from being exercised only on the `head? = none` arm. -/
def witnessChainSchedContext : SchedContext :=
  { SchedContext.empty donationChainWitnessContext with
      scReply := some donationChainWitnessInner }

/-- The witness's inner (head) reply: heads the context (`next := .head`), links
down to the outer one.  Public for the same reason as `witnessChainSchedContext`. -/
def witnessChainInnerReply : Reply :=
  { replyId := donationChainWitnessInner,
    callerCode := SeLe4n.ThreadId.optCode (some donationChainWitnessInnerCaller),
    prev := some donationChainWitnessOuter,
    next := some (.head donationChainWitnessContext) }

/-- The witness's outer reply: answers the head above it (`next := .frame`) and
is the bottom of the stack.  Public for the same reason as
`witnessChainSchedContext`. -/
def witnessChainOuterReply : Reply :=
  { replyId := donationChainWitnessOuter,
    callerCode := SeLe4n.ThreadId.optCode (some donationChainWitnessOuterCaller),
    next := some (.frame donationChainWitnessInner) }

-- The three stores are the pure store (`withObjectStored`, `v0.35.73`): each
-- key held nothing in the boot state, and the witness the pop is run on now
-- carries the store's own bookkeeping.
private def chainWitnessSt1 : SystemState :=
  (default : SystemState).withObjectStored donationChainWitnessContext.toObjId
    (.schedContext witnessChainSchedContext)

private def chainWitnessSt2 : SystemState :=
  chainWitnessSt1.withObjectStored donationChainWitnessOuter.toObjId
    (.reply witnessChainOuterReply)

/-- WS-OD OD2.4: the state a depth-2 Call chain leaves — the context heads the
inner call's reply, which links down to the outer call's, and every link is
answered by the object it names. -/
def donationChainWitness : SystemState :=
  chainWitnessSt2.withObjectStored donationChainWitnessInner.toObjId
    (.reply witnessChainInnerReply)

private theorem chainWitnessObjInv0 : (default : SystemState).objects.invExt :=
  capabilityInvariantBundle.objectsInvExt
    (Architecture.default_system_state_proofLayerInvariantBundle).2.1

private theorem chainWitnessObjInv1 : chainWitnessSt1.objects.invExt :=
  SystemState.withObjectStored_preserves_objects_invExt _ _ _ chainWitnessObjInv0

private theorem chainWitnessObjInv2 : chainWitnessSt2.objects.invExt :=
  SystemState.withObjectStored_preserves_objects_invExt _ _ _ chainWitnessObjInv1

private theorem chainWitnessSt1_lookup (oid : SeLe4n.ObjId) :
    chainWitnessSt1.objects[oid]?
      = if donationChainWitnessContext.toObjId == oid
        then some (.schedContext witnessChainSchedContext) else none := by
  unfold chainWitnessSt1
  rw [SystemState.withObjectStored_objects, RHTable_getElem?_eq_get?,
    RHTable_getElem?_insert _ _ _ chainWitnessObjInv0]
  split
  · rfl
  · rw [← RHTable_getElem?_eq_get?, Architecture.default_objects_none]

private theorem chainWitnessSt2_lookup (oid : SeLe4n.ObjId) :
    chainWitnessSt2.objects[oid]?
      = if donationChainWitnessOuter.toObjId == oid
        then some (.reply witnessChainOuterReply)
        else chainWitnessSt1.objects[oid]? := by
  unfold chainWitnessSt2
  rw [SystemState.withObjectStored_objects, RHTable_getElem?_eq_get?,
    RHTable_getElem?_insert _ _ _ chainWitnessObjInv1]
  split
  · rfl
  · rw [← RHTable_getElem?_eq_get?]

private theorem donationChainWitness_lookup (oid : SeLe4n.ObjId) :
    donationChainWitness.objects[oid]?
      = if donationChainWitnessInner.toObjId == oid
        then some (.reply witnessChainInnerReply)
        else chainWitnessSt2.objects[oid]? := by
  unfold donationChainWitness
  rw [SystemState.withObjectStored_objects, RHTable_getElem?_eq_get?,
    RHTable_getElem?_insert _ _ _ chainWitnessObjInv2]
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
  SystemState.withObjectStored_preserves_objects_invExt _ _ _ chainWitnessObjInv2

/-- WS-OD OD2.4: the walk from the context's own head yields the whole stack,
innermost first — the positive half of the chain's meaning, computed rather than
asserted. -/
theorem donationChainWitness_chain :
    donationChainFrom donationChainWitness donationChainWitnessContext 2
        witnessChainSchedContext.scReply
      = some [donationChainWitnessInner, donationChainWitnessOuter] := by
  have hInner : replyStackLinksAt? donationChainWitness donationChainWitnessInner
      = some (some donationChainWitnessOuter, some (.head donationChainWitnessContext)) := by
    unfold replyStackLinksAt? SystemState.getObject?
    rw [donationChainWitness_lookup_cases]
    simp [replyStackLinks?, witnessChainInnerReply]
  have hOuter : replyStackLinksAt? donationChainWitness donationChainWitnessOuter
      = some (none, some (.frame donationChainWitnessInner)) := by
    unfold replyStackLinksAt? SystemState.getObject?
    rw [donationChainWitness_lookup_cases]
    simp [replyStackLinks?, witnessChainOuterReply,
      show (donationChainWitnessInner.toObjId == donationChainWitnessOuter.toObjId) = false from
        by decide]
  have hTail : donationChainWalk donationChainWitness (.frame donationChainWitnessInner) 1
      (some donationChainWitnessOuter) = some [donationChainWitnessOuter] := by
    rw [donationChainWalk_succ, hOuter]; simp
  show donationChainFrom donationChainWitness donationChainWitnessContext 2
      (some donationChainWitnessInner) = _
  rw [donationChainFrom_succ, hInner]
  simp [hTail]

/-- WS-OD OD2.4 / `v0.35.4`: **the depth-2 chain satisfies the whole predicate.**
The reciprocity clauses are the substantive ones: the context's head answers it
(`headLinkReciprocal` / `headLinkResolves`), the head's `prev` is answered by a
frame whose `next` names the head back (`prevLinkReciprocal`), and the walk from
the head terminates on exactly those two frames — which is what the donation
return's link validation and the removal's `O(1)` splice both rely on. -/
theorem donationChainWitness_wellFormed :
    donationChainWellFormed donationChainWitness := by
  have hInnerNe : (donationChainWitnessInner.toObjId
      == donationChainWitnessContext.toObjId) = false := by decide
  have hOuterNe : (donationChainWitnessOuter.toObjId
      == donationChainWitnessContext.toObjId) = false := by decide
  have hInnerNeOuter : (donationChainWitnessInner.toObjId
      == donationChainWitnessOuter.toObjId) = false := by decide
  -- The one SchedContext in the store, by key.
  have hScCases : ∀ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
      donationChainWitness.objects[scId.toObjId]? = some (.schedContext sc) →
      scId = donationChainWitnessContext ∧ sc = witnessChainSchedContext := by
    intro scId sc hSc
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Every stored Reply has a caller, so `Reply.wellFormed` is immediate.
    intro rid r hR
    rw [donationChainWitness_lookup_cases] at hR
    split at hR
    · cases hR; intro hNone; simp [witnessChainInnerReply] at hNone
    · split at hR
      · cases hR; intro hNone; simp [witnessChainOuterReply] at hNone
      · split at hR
        · cases hR
        · cases hR
  · -- The context's head is the inner reply, which heads it back.
    intro scId sc hSc rid hRid
    obtain ⟨rfl, rfl⟩ := hScCases scId sc hSc
    have hRid' : rid = donationChainWitnessInner := by
      simpa [witnessChainSchedContext] using hRid.symm
    subst hRid'
    refine ⟨witnessChainInnerReply, ?_, rfl⟩
    rw [donationChainWitness_lookup_cases]
    simp
  · -- The one Reply heading a context heads the witness context, whose head it is.
    intro rid r scId hR hNext
    rw [donationChainWitness_lookup_cases] at hR
    split at hR
    · next hKey =>
      cases hR
      have hRid : rid = donationChainWitnessInner :=
        (SeLe4n.ReplyId.toObjId_injective _ _ (eq_of_beq hKey)).symm
      subst hRid
      have hScId : scId = donationChainWitnessContext := by
        simpa [witnessChainInnerReply] using hNext.symm
      subst hScId
      refine ⟨witnessChainSchedContext, ?_, rfl⟩
      rw [donationChainWitness_lookup_cases]
      simp [hInnerNe, hOuterNe]
    · split at hR
      · cases hR; simp [witnessChainOuterReply] at hNext
      · split at hR
        · cases hR
        · cases hR
  · -- The one `prev` link — the head's — is answered by the outer reply.
    intro rid r below hR hPrev
    rw [donationChainWitness_lookup_cases] at hR
    split at hR
    · next hKey =>
      cases hR
      have hRid : rid = donationChainWitnessInner :=
        (SeLe4n.ReplyId.toObjId_injective _ _ (eq_of_beq hKey)).symm
      subst hRid
      have hBelow : below = donationChainWitnessOuter := by
        simpa [witnessChainInnerReply] using hPrev.symm
      subst hBelow
      refine ⟨witnessChainOuterReply, ?_, rfl⟩
      rw [donationChainWitness_lookup_cases]
      simp [hInnerNeOuter]
    · split at hR
      · cases hR; simp [witnessChainOuterReply] at hPrev
      · split at hR
        · cases hR
        · cases hR
  · -- The context's head walks the whole stack.
    intro scId sc hSc
    obtain ⟨rfl, rfl⟩ := hScCases scId sc hSc
    exact ⟨2, [donationChainWitnessInner, donationChainWitnessOuter], donationChainWitness_chain⟩
  · -- The one `next` frame link — the outer reply's — is answered by the head.
    intro rid r above hR hNext
    rw [donationChainWitness_lookup_cases] at hR
    split at hR
    · cases hR; simp [witnessChainInnerReply] at hNext
    · split at hR
      · next hKey =>
        cases hR
        have hRid : rid = donationChainWitnessOuter :=
          (SeLe4n.ReplyId.toObjId_injective _ _ (eq_of_beq hKey)).symm
        subst hRid
        have hAbove : above = donationChainWitnessInner := by
          simpa [witnessChainOuterReply] using hNext.symm
        subst hAbove
        refine ⟨witnessChainInnerReply, ?_, rfl⟩
        rw [donationChainWitness_lookup_cases]
        simp
      · split at hR
        · cases hR
        · cases hR

-- ============================================================================
-- §6  WS-ZA ZA4.6 — the live arms carry the reply-waiter queues
-- ============================================================================

section ReplyWaiters

open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId)

/-- A thread whose block names no server waits on no reply. -/
theorem serverFree_of_tcb {st : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    (hT : st.objects[t.toObjId]? = some (.tcb tcb)) (hS : tcb.blockingServer? = none) :
    ReplyViews.serverFree st.replyViews t := by
  intro v hv
  rw [replyViews_of_tcb hT] at hv
  cases hv; exact hS

/-- The head of a receive queue is blocked on the receive, so it waits on no
server. -/
theorem receiveHead_serverFree {st : SystemState} (hQ : queueHeadBlockedConsistent st)
    {eid : SeLe4n.ObjId} {ep : Endpoint} {r : SeLe4n.ThreadId}
    (hE : st.objects[eid]? = some (.endpoint ep)) (hH : ep.receiveQ.head = some r) :
    ReplyViews.serverFree st.replyViews r := by
  intro v hv
  obtain ⟨t, hT, rfl⟩ := tcb_of_replyViews hv
  have hR := (hQ eid ep r t hE hT).1 hH
  simp only [TCB.replyView, TCB.blockingServer?, hR]

/-- The head of a send queue is blocked on the send or the call, so it waits
on no server. -/
theorem sendHead_serverFree {st : SystemState} (hQ : queueHeadBlockedConsistent st)
    {eid : SeLe4n.ObjId} {ep : Endpoint} {s : SeLe4n.ThreadId}
    (hE : st.objects[eid]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s) :
    ReplyViews.serverFree st.replyViews s := by
  intro v hv
  obtain ⟨t, hT, rfl⟩ := tcb_of_replyViews hv
  rcases (hQ eid ep s t hE hT).2 hH with hS | hS <;>
    simp only [TCB.replyView, TCB.blockingServer?, hS]

/-- The head of a notification's wait queue is blocked on it, so it waits on
no server. -/
theorem notificationHead_serverFree {st : SystemState} (hN : notificationWaiterConsistent st)
    {nid : SeLe4n.ObjId} {n : Notification} {w : SeLe4n.ThreadId}
    (hG : st.getNotification? nid = some n) (hH : n.waitHead = some w) :
    ReplyViews.serverFree st.replyViews w := by
  obtain ⟨t, hT, hB⟩ := (hN.1 nid n ((getNotification?_eq_some_iff st nid n).1 hG)).2.1 w hH
  exact serverFree_of_tcb hT (by simp only [TCB.blockingServer?, hB])

/-- **The live call carries the reply-waiter queues**, its side conditions read
off the reachable-state pack and the running caller. -/
theorem endpointCallCrossCoreDispatch_preserves_replyWaitersConsistent_of_reachable
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (base : SeLe4n.Slot) (c : CoreId) (st : SystemState)
    (hReach : ipcReachable st) (tcb : TCB) (hT : st.objects[caller.toObjId]? = some (.tcb tcb))
    (hReady : tcb.ipcState = .ready) :
    (endpointCallCrossCoreDispatch endpointId caller payload base c
      st).1.replyWaitersConsistent :=
  have hI := hReach.ipcInvariantFull
  endpointCallCrossCoreDispatch_preserves_replyWaitersConsistent endpointId caller payload
    base c st hReach.objects_invExt hReach.replyWaitersConsistent
    (serverFree_of_tcb hT (by simp only [TCB.blockingServer?, hReady]))
    (fun ep r hE hH => ⟨fun h => by
        subst h
        exact (readyThread_endpointQueueFresh st _ tcb hI.queueHeadBlockedConsistent
          hI.endpointQueueTailBlockedConsistent hT hReady endpointId ep hE).2.2.1 hH,
      receiveHead_serverFree hI.queueHeadBlockedConsistent hE hH⟩)

/-- **The live receive carries the reply-waiter queues**, likewise. -/
theorem endpointReceiveDualWithCapsOnCore_preserves_replyWaitersConsistent_of_reachable
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (root : SeLe4n.ObjId) (base : SeLe4n.Slot) (c : CoreId)
    (st : SystemState) (hReach : ipcReachable st) (tcb : TCB)
    (hT : st.objects[receiver.toObjId]? = some (.tcb tcb)) (hReady : tcb.ipcState = .ready) :
    (endpointReceiveDualWithCapsOnCore endpointId receiver replyId root base c
      st).1.replyWaitersConsistent :=
  have hI := hReach.ipcInvariantFull
  endpointReceiveDualWithCapsOnCore_preserves_replyWaitersConsistent endpointId receiver
    replyId root base c st hReach.objects_invExt hReach.replyWaitersConsistent
    (serverFree_of_tcb hT (by simp only [TCB.blockingServer?, hReady]))
    (fun ep s hE hH => ⟨fun h => by
        subst h
        exact (readyThread_endpointQueueFresh st _ tcb hI.queueHeadBlockedConsistent
          hI.endpointQueueTailBlockedConsistent hT hReady endpointId ep hE).1 hH,
      sendHead_serverFree hI.queueHeadBlockedConsistent hE hH⟩)

/-- **The live send carries the reply-waiter queues**, likewise. -/
theorem endpointSendDualWithCapsOnCore_preserves_replyWaitersConsistent_of_reachable
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (base : SeLe4n.Slot) (c : CoreId) (st : SystemState)
    (hReach : ipcReachable st) (tcb : TCB) (hT : st.objects[sender.toObjId]? = some (.tcb tcb))
    (hReady : tcb.ipcState = .ready) :
    (endpointSendDualWithCapsOnCore endpointId sender payload base c
      st).1.replyWaitersConsistent :=
  endpointSendDualWithCapsOnCore_preserves_replyWaitersConsistent endpointId sender payload
    base c st hReach.objects_invExt hReach.replyWaitersConsistent
    (serverFree_of_tcb hT (by simp only [TCB.blockingServer?, hReady]))
    (fun _ _ hE hH => receiveHead_serverFree hReach.ipcInvariantFull.queueHeadBlockedConsistent hE hH)

/-- **Signal carries the reply-waiter queues**, its waiter read off the
notification queue invariant. -/
theorem notificationSignalOnCore_preserves_replyWaitersConsistent_of_reachable (nid : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) (hReach : ipcReachable st) :
    (notificationSignalOnCore nid badge c st).1.replyWaitersConsistent :=
  notificationSignalOnCore_preserves_replyWaitersConsistent nid badge c st hReach.objects_invExt
    hReach.replyWaitersConsistent
    (fun _ _ hG hH => notificationHead_serverFree hReach.notificationWaiterConsistent hG hH)

end ReplyWaiters


-- ============================================================================
-- §  The final-delete retire keeps the reachable state
-- ============================================================================

/-- **A notification a thread waits on is not quiescent**: the thread is in its
queue (`notificationWaiterConsistent`'s membership clause), so the queue has a
head. -/
theorem notificationWaiterConsistent.waitedOn_not_quiescent {st : SystemState}
    (h : notificationWaiterConsistent st) {tid : SeLe4n.ThreadId} {tcb : TCB}
    {oid : SeLe4n.ObjId} (hT : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hB : tcb.ipcState = .blockedOnNotification oid) : passiveObjectQuiescent st oid = false := by
  have hHead : ∀ {u : SeLe4n.ThreadId}, notificationQueueReaches st oid u →
      ∃ ntfn hd, st.objects[oid]? = some (.notification ntfn) ∧ ntfn.waitHead = some hd := by
    intro u hR
    induction hR with
    | head hN hH => exact ⟨_, _, hN, hH⟩
    | next _ _ _ ih => exact ih
  obtain ⟨ntfn, hd, hN, hH⟩ := hHead (h.reaches hT hB)
  cases hq : passiveObjectQuiescent st oid with
  | false => rfl
  | true => rw [(passiveObjectQuiescent_notification hq hN).1] at hH; cases hH

/-- **The retire keeps the notification queues**: it keeps every thread, keeps
every notification it leaves, and erases none a thread waits on — that one's
queue has a head, so it is not quiescent. -/
theorem retireFinalObject_preserves_notificationWaiterConsistent (ec : Concurrency.CoreId)
    (target recorder : Nat) {st : SystemState} (hObjInv : st.objects.invExt)
    (h : notificationWaiterConsistent st) :
    notificationWaiterConsistent (retireFinalObject ec target recorder st) := by
  have hPost : ∀ k t, (retireFinalObject ec target recorder st).objects[k]? =
      some (KernelObject.tcb t) →
      (retireFinalObject ec target recorder st).objects[k]? = st.objects[k]? :=
    fun _ _ hk => retireFinalObject_tcb_post ec target recorder st hObjInv hk
  refine notificationWaiterConsistent_frame h
    (fun _ _ hN => retireFinalObject_back ec target recorder st hObjInv hN (fun _ e => by cases e))
    (fun _ _ _ _ hN hTt hB => by
      rw [retireFinalObject_passive_kept ec target recorder st hObjInv (by rw [hN]; trivial)
        (h.waitedOn_not_quiescent hTt hB)]
      exact hN)
    (fun _ tcb _ hTt hB => by
      rcases retireFinalObject_tcb_kept_or_quiescent ec target recorder st hObjInv hTt with
        e | ⟨-, -, -, hQ, -⟩
      · exact e
      · rw [threadQuiescent_ipcState hQ] at hB; cases hB)
    (fun _ tcb _ hTt _ => hPost _ tcb hTt)
    (fun _ tcb hTt _ => .inl (hPost _ tcb hTt))

/-- **The retire keeps the donation chains**: every reply and scheduling
context it leaves is as it was, and no reply or context a chain reads is
erased — each is linked into the chain on its own side (a head reply up to its
context, a context down to its head, a lower frame up to the frame above, an
upper frame down to the one below, every member upward), so none is
quiescent. -/
theorem retireFinalObject_preserves_donationChainWellFormed (ec : Concurrency.CoreId)
    (target recorder : Nat) {st : SystemState} (hObjInv : st.objects.invExt)
    (h : donationChainWellFormed st) :
    donationChainWellFormed (retireFinalObject ec target recorder st) := by
  have back : ∀ {o : SeLe4n.ObjId} {obj : KernelObject},
      (retireFinalObject ec target recorder st).objects[o]? = some obj →
      (∀ U, obj ≠ .untyped U) → st.objects[o]? = some obj :=
    fun hp hn => retireFinalObject_back ec target recorder st hObjInv hp hn
  have keepReply : ∀ {o : SeLe4n.ObjId} {r : Reply}, st.objects[o]? = some (.reply r) →
      r.prev.isSome = true ∨ r.next.isSome = true →
      (retireFinalObject ec target recorder st).objects[o]? = some (.reply r) :=
    fun hR hL => by
      rw [retireFinalObject_passive_kept ec target recorder st hObjInv (by rw [hR]; trivial)
        (hL.elim (passiveObjectQuiescent_of_prev hR) (passiveObjectQuiescent_of_next hR))]
      exact hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rid r hR
    exact h.replyWellFormed rid r (back hR (fun _ e => by cases e))
  · intro scId sc hSc rid hr
    obtain ⟨r, hR, hN⟩ := h.headLinkReciprocal scId sc (back hSc (fun _ e => by cases e)) rid hr
    exact ⟨r, keepReply hR (.inr (by rw [hN]; rfl)), hN⟩
  · intro rid r scId hR hN
    obtain ⟨sc, hSc, hS⟩ := h.headLinkResolves rid r scId (back hR (fun _ e => by cases e)) hN
    exact ⟨sc, retireFinalObject_schedContext ec target recorder st hObjInv hSc
      (schedContextRetirable_false_of_scReply hSc hS), hS⟩
  · intro rid r below hR hP
    obtain ⟨b, hB, hBN⟩ := h.prevLinkReciprocal rid r below (back hR (fun _ e => by cases e)) hP
    exact ⟨b, keepReply hB (.inr (by rw [hBN]; rfl)), hBN⟩
  · intro scId sc hSc
    obtain ⟨fuel, chain, hC⟩ := h.headTerminates scId sc (back hSc (fun _ e => by cases e))
    refine ⟨fuel, chain, ?_⟩
    unfold donationChainFrom at hC ⊢
    refine donationChainWalk_congr_on_chain fuel _ _ chain hC (fun m hm => ?_)
    obtain ⟨r, hR, hNs⟩ := donationChainWalk_mem st fuel _ _ chain hC m hm
    unfold replyStackLinksAt? SystemState.getObject?
    rw [keepReply hR (.inr hNs), hR]
  · intro rid r above hR hN
    obtain ⟨a, hA, hAP⟩ := h.nextLinkReciprocal rid r above (back hR (fun _ e => by cases e)) hN
    exact ⟨a, keepReply hA (.inl (by rw [hAP]; rfl)), hAP⟩

/-- **The retire keeps every thread's reply view but a quiescent thread's**:
a key keeps its view, or loses an idle one — the retired thread's, which waits on
no server and heads no queue. -/
theorem retireFinalObject_replyViews (ec : Concurrency.CoreId) (target recorder : Nat)
    {st : SystemState} (hObjInv : st.objects.invExt) (k : SeLe4n.ObjId) :
    (retireFinalObject ec target recorder st).replyViews k = st.replyViews k ∨
      ((retireFinalObject ec target recorder st).replyViews k = none ∧
        ∃ v, st.replyViews k = some v ∧ v.server = none ∧ v.headCode = 0) := by
  unfold SystemState.replyViews SystemState.getObject?
  rcases retireFinalObject_key ec target recorder st hObjInv k with e | ⟨-, hNT, hn | ⟨U, hU⟩⟩
  · rw [e]; exact .inl rfl
  · cases hk : st.objects[k]? with
    | none => rw [hn]; exact .inl rfl
    | some o => cases o with
      | tcb t =>
        obtain ⟨t', hT', -, -, hQ, -⟩ := threadRetirable_parts (hNT t hk)
        rw [hk] at hT'; cases hT'
        refine .inr ⟨by rw [hn]; rfl, t.replyView, rfl, threadQuiescent_blockingServer hQ, ?_⟩
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h0, -⟩ := threadQuiescent_codes hQ
        exact h0
      | _ => rw [hn]; exact .inl rfl
  · rw [hU]
    cases hk : st.objects[k]? with
    | none => exact .inl rfl
    | some o => cases o with
      | tcb t =>
        exfalso
        rcases (retireFinalObject_frame ec target recorder st hObjInv).2.2.2.2 k with
          e | ⟨-, -, hn'⟩ | ⟨U', -, -, hU0, -, -⟩
        · rw [e, hk] at hU; cases hU
        · rw [hn'] at hU; cases hU
        · rw [hk] at hU0; cases hU0
      | _ => exact .inl rfl

/-- **The final-delete retire keeps the reachable state** (`ipcReachable`): the
IPC bundle (`retireFinalObject_preserves_ipcInvariantFull`), the store's
invariant, the timeout budgets and run-queue links (it keeps every thread and
the scheduler), the notification queues, the donation chains and the
reply-waiter queues. -/
theorem retireFinalObject_preserves_ipcReachable (ec : Concurrency.CoreId)
    (target recorder : Nat) {st : SystemState} (h : ipcReachable st) :
    ipcReachable (retireFinalObject ec target recorder st) := by
  have hObjInv := h.objects_invExt
  obtain ⟨hI, hE⟩ := retireFinalObject_preserves_ipcInvariantFull ec target recorder st hObjInv
    h.ipcInvariantFull h.allTimeoutBudgetsNone
  have hS := (retireFinalObject_fields ec target recorder st).2.1
  refine ⟨hI, hE, fun tid tcb hT => h.allTimeoutBudgetsNone tid tcb
      (retireFinalObject_tcb_back ec target recorder st hObjInv hT),
    retireFinalObject_preserves_notificationWaiterConsistent ec target recorder hObjInv
      h.notificationWaiterConsistent,
    retireFinalObject_preserves_donationChainWellFormed ec target recorder hObjInv
      h.donationChainWellFormed,
    SystemState.runQueueRefined_of_frame
      (fun c t => retireFinalObject_runLinkOn ec target recorder hObjInv c t)
      (by rw [hS]) (by rw [hS]) h.runQueueRefined,
    SystemState.replyWaitersConsistent.of_views_erased
      (retireFinalObject_replyViews ec target recorder hObjInv) h.replyWaitersConsistent⟩

-- ============================================================================
-- §  What the retire's own-link guards answer: an admitted object is named by none
-- ============================================================================

/-- **A thread whose state codes name `x`** (`ipcCodesName`) is queued on it as
an endpoint or waits on it as a notification. -/
theorem ipcCodesName_true {t : TCB} {x : SeLe4n.ObjId}
    (h : ipcCodesName t.ipcObjectCode t.ipcStateCode x = true) :
    ipcStateQueuedOn x t.ipcState ∨ t.ipcState = .blockedOnNotification x := by
  unfold TCB.ipcState
  unfold ipcCodesName at h
  generalize t.ipcObjectCode = o at h ⊢
  generalize t.ipcStateCode = s at h ⊢
  rcases x with ⟨xv⟩
  rcases s with _ | _ | _ | _ | s
  · cases o with
    | zero => simp at h
    | succ o =>
      simp only [if_true, beq_iff_eq, Nat.add_right_cancel_iff] at h
      subst h; exact .inl rfl
  · simp at h; subst h; exact .inl rfl
  · simp at h; subst h; exact .inr rfl
  · simp at h; subst h; exact .inl rfl
  · simp at h

/-- **No object names a quiescent passive object by id** (`objectNamesById`),
under the reachable invariants: so the retire reads its own links alone.  A
thread blocked on it would be queued on it or wait in its queue, and its queues
are empty (`passiveObjectQuiescent_notQueuedOn`,
`notificationWaiterConsistent.waitedOn_not_quiescent`); a thread bound to it is
answered by its bound-thread code (`notificationBindingReciprocal`), which is
zero; a caller's reply link to it by its caller (`replyCallerLinkage`), which it
has none of; a receiver's stash of it by its stash record
(`pendingReceiveReplyWellFormed.stashedAt`), which names no live stasher; a
reply's stack link to it, either way, and a context's head link to it, by its
own stack links (`donationChainWellFormed`), which it has none of. -/
theorem passiveObjectQuiescent.namedByNone {st : SystemState} (h : ipcReachable st)
    {x : SeLe4n.ObjId} (hQ : passiveObjectQuiescent st x = true)
    {k : SeLe4n.ObjId} {o : KernelObject} (hK : st.objects[k]? = some o) :
    objectNamesById o x = false := by
  have hI := h.ipcInvariantFull
  have hRx : ∀ r : Reply, st.objects[x]? = some (.reply r) →
      r.callerCode = 0 ∧ st.replyStashedAt ⟨x.val⟩ r = false ∧ r.prev = none ∧ r.next = none :=
    fun r hR => passiveObjectQuiescent_reply hQ hR
  cases o with
  | tcb t =>
    have hT : st.objects[(SeLe4n.ThreadId.ofObjId k).toObjId]? = some (.tcb t) := hK
    unfold objectNamesById
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    refine ⟨⟨⟨?_, fun hc => ?_⟩, fun hc => ?_⟩, fun hc => ?_⟩
    · cases hn : ipcCodesName t.ipcObjectCode t.ipcStateCode x with
      | false => rfl
      | true =>
        rcases ipcCodesName_true hn with hq | hb
        · exact absurd hq (passiveObjectQuiescent_notQueuedOn hQ h.objects_invExt hI hT)
        · rw [h.notificationWaiterConsistent.waitedOn_not_quiescent hT hb] at hQ; cases hQ
    · have hB := (hI.notificationBindingReciprocal k).1 x.val (by
        simp [notificationBindingCodes, KernelObject.bindingCodes, hK, hc])
      have hC := passiveObjectQuiescent_bindingCodes (passiveObjectQuiescent.passive hQ) hQ
      have hB' : (notificationBindingCodes st.objects[x]?).2 = k.val + 1 := hB
      rw [hC] at hB'; simp at hB'
    · obtain ⟨r, hR, hC⟩ := hI.replyCallerLinkage.1.1 _ t ⟨x.val⟩ hT (by
        simp only [TCB.replyObject, hc]; rfl)
      simp [Reply.caller, (hRx r hR).1] at hC
    · obtain ⟨r, hR, hS⟩ := pendingReceiveReplyWellFormed.stashedAt
        hI.pendingReceiveReplyWellFormed hT (rid := ⟨x.val⟩) (by
          simp only [TCB.pendingReceiveReply, hc]; rfl)
      rw [(hRx r hR).2.1] at hS; cases hS
  | reply r =>
    have hR : st.objects[(SeLe4n.ReplyId.ofObjId k).toObjId]? = some (.reply r) := hK
    have hPrev : (match r.prev with | some p => p.toObjId == x | none => false) = false := by
      cases hp : r.prev with
      | none => rfl
      | some p =>
        cases hx : (p.toObjId == x) with
        | false => simp [hx]
        | true =>
          obtain ⟨b, hB, hBN⟩ := h.donationChainWellFormed.prevLinkReciprocal _ r p hR hp
          rw [beq_iff_eq.mp hx] at hB
          rw [(hRx b hB).2.2.2] at hBN; cases hBN
    have hNext : (match r.next with | some (.frame a) => a.toObjId == x | _ => false) = false := by
      cases hn : r.next with
      | none => rfl
      | some l =>
        cases l with
        | head _ => rfl
        | frame a =>
          cases hx : (a.toObjId == x) with
          | false => simp [hx]
          | true =>
            obtain ⟨b, hB, hBP⟩ := h.donationChainWellFormed.nextLinkReciprocal _ r a hR hn
            rw [beq_iff_eq.mp hx] at hB
            rw [(hRx b hB).2.2.1] at hBP; cases hBP
    unfold objectNamesById; rw [Bool.or_eq_false_iff]; exact ⟨hPrev, hNext⟩
  | schedContext sc =>
    have hS : st.objects[(SeLe4n.SchedContextId.ofObjId k).toObjId]? = some (.schedContext sc) := hK
    have hHd : (match sc.scReply with | some r => r.toObjId == x | none => false) = false := by
      cases hr : sc.scReply with
      | none => rfl
      | some rid =>
        cases hx : (rid.toObjId == x) with
        | false => simp [hx]
        | true =>
          obtain ⟨b, hB, hBN⟩ := h.donationChainWellFormed.headLinkReciprocal _ sc hS rid hr
          rw [beq_iff_eq.mp hx] at hB
          rw [(hRx b hB).2.2.2] at hBN; cases hBN
    unfold objectNamesById; exact hHd
  | _ => rfl

/-- **A run-queue neighbour is queued on the same core**: a thread queued on
core `c` (its core code names `c`) whose forward, backward or bucket link names
`z` has `z` queued on `c` too.  The queue is one list (`RunQueue.Layout`), every
link of a member names another member (`LinkedQueue.linked_mem`), and every
member's entry is its thread's (`runQueueRefined`). -/
theorem SystemState.runQueueRefined.neighbour_queued {st : SystemState} (h : st.runQueueRefined)
    (c : Concurrency.CoreId) {K : SeLe4n.ThreadId} {u : TCB} (hU : st.getTcb? K = some u)
    (hc : u.runCoreCode = c.val + 1) {z : SeLe4n.ThreadId}
    (hz : u.runNextCode = LinkedQueue.code z ∨ u.runPrevCode = LinkedQueue.code z ∨
      u.runBucketNextCode = LinkedQueue.code z ∨ u.runBucketPrevCode = LinkedQueue.code z) :
    ∃ tz, st.getTcb? z = some tz ∧ tz.runCoreCode = c.val + 1 := by
  have hR := (h c).2
  generalize hq : st.scheduler.runQueueOnCore c = rq at hR
  have hK : rq.queuedLink K = u.runLink := by
    rw [← hR K]; unfold SystemState.runLinkOn; rw [hU]; dsimp only; unfold TCB.runLinkOn; rw [if_pos hc]
  have hCont : rq.contains K = true := by rw [← RunQueue.queuedLink_queued, hK]; rfl
  have hL : RunQueue.linkOf rq.links K = u.runLink :=
    (RunQueue.queuedLink_of_contains hCont).symm.trans hK
  have lay := rq.layout_toList
  have hKm : K ∈ rq.toList := (lay.queued K).mp (by rw [hL]; rfl)
  have hzNe : LinkedQueue.code z ≠ 0 := LinkedQueue.code_ne_zero z
  have ofLink : ∀ {f : SeLe4n.ThreadId → Nat} {l : List SeLe4n.ThreadId},
      LinkedQueue.Linked f 0 l → K ∈ l → f K = LinkedQueue.code z → z ∈ l := by
    intro f l hl hm e
    rcases LinkedQueue.linked_mem hl hm with e0 | ⟨w, hw, ew⟩
    · rw [e] at e0; exact absurd e0 hzNe
    · rw [e] at ew; rw [LinkedQueue.code_inj ew]; exact hw
  have hBk : K ∈ rq.toList.filter (fun t => (RunQueue.linkOf rq.links t).prio ==
      (RunQueue.linkOf rq.links K).prio) := List.mem_filter.mpr ⟨hKm, by simp⟩
  have hzm : z ∈ rq.toList := by
    rcases hz with e | e | e | e
    · exact List.mem_reverse.mp (ofLink lay.queue.2.2.2 (List.mem_reverse.mpr hKm)
        (by rw [hL]; exact e))
    · exact ofLink lay.queue.2.2.1 hKm (by rw [hL]; exact e)
    · exact (List.mem_filter.mp (List.mem_reverse.mp (ofLink (lay.bucket _).2.2.2
        (List.mem_reverse.mpr hBk) (by rw [hL]; exact e)))).1
    · exact (List.mem_filter.mp (ofLink (lay.bucket _).2.2.1 hBk (by rw [hL]; exact e))).1
  have hzq : (rq.queuedLink z).queued = true := by
    rw [RunQueue.queuedLink_queued]; exact (lay.queued z).mpr hzm
  rw [← hR z] at hzq
  unfold SystemState.runLinkOn at hzq
  cases hT : st.getTcb? z with
  | none => rw [hT] at hzq; cases hzq
  | some tz =>
    rw [hT] at hzq; dsimp only at hzq
    refine ⟨tz, rfl, ?_⟩
    unfold TCB.runLinkOn at hzq
    by_cases e : tz.runCoreCode = c.val + 1
    · exact e
    · rw [if_neg e] at hzq; cases hzq

/-- **No object names a retirable thread by id** (`objectNamesThread`), under
the reachable invariants and the scheduling-context binding pair: so the retire
reads the thread's own links alone.  Each reference is answered on the thread's
side, where its quiescent record holds nothing: an endpoint-queue neighbour by
its own link (`tcbQueueLinkIntegrity`, `queuePPrevAgreesWithPrev`); a queue end,
a notification waiter or a donation owner by its state, which is ready
(`queueHeadBlockedConsistent`, `endpointQueueTailBlockedConsistent`,
`notificationWaiterConsistent`, `donationOwnerValid`); a run-queue neighbour by
its core code (`runQueueRefined.neighbour_queued`); a reply-waiter neighbour, a
waiter or a server's queue head by its reply view (`replyWaitersConsistent`); a
notification's binding by its own (`notificationBindingReciprocal`); a reply's
caller by its state (`replyCallerLinkage`); a context bound to it by its own
binding (`schedContextBindingConsistent`). -/
theorem threadRetirable.namedByNone {st : SystemState} (h : ipcReachable st)
    (hBind : schedContextBindingConsistent st) {x : SeLe4n.ObjId}
    (hRet : threadRetirable st x = true) {k : SeLe4n.ObjId} {o : KernelObject}
    (hK : st.objects[k]? = some o) : objectNamesThread o (x.val + 1) = false := by
  have hI := h.ipcInvariantFull
  obtain ⟨t, hTx, -, -, hQ, -⟩ := threadRetirable_parts hRet
  obtain ⟨-, -, -, -, hQN, hQP, -, -, -, hRC, -, -, hRWH, hSC, hSO, hBN, -⟩ :=
    threadQuiescent_codes hQ
  have hReady := threadQuiescent_ipcState hQ
  have hServ := threadQuiescent_blockingServer hQ
  have hX : st.objects[(SeLe4n.ThreadId.ofObjId x).toObjId]? = some (.tcb t) := hTx
  have isT : ∀ {tt : TCB}, st.objects[(SeLe4n.ThreadId.ofObjId x).toObjId]? = some (.tcb tt) →
      tt = t := fun e => by rw [hX] at e; cases e; rfl
  have dec : ∀ {n : Nat}, n = x.val + 1 →
      SeLe4n.ThreadId.ofOptCode n = some (SeLe4n.ThreadId.ofObjId x) := by
    intro n e; subst e; rfl
  have notBlocked : ∀ {tt : TCB}, st.objects[(SeLe4n.ThreadId.ofObjId x).toObjId]? =
      some (.tcb tt) → ∀ s : ThreadIpcState, s ≠ .ready → tt.ipcState ≠ s := by
    intro tt e s hs hE; rw [isT e, hReady] at hE; exact hs hE.symm
  have V := h.replyWaitersConsistent
  have hVX : st.replyViews (SeLe4n.ThreadId.ofObjId x).toObjId = some t.replyView := by
    unfold SystemState.replyViews; rw [SystemState.getObject?_eq_getElem, hX]; rfl
  have serverOf : ∀ {s : SeLe4n.ThreadId}, ReplyViews.waiterOf st.replyViews (SeLe4n.ThreadId.ofObjId x) s →
      False := by
    intro s ⟨v, hv, hs⟩
    rw [hVX] at hv; cases hv
    simp only [TCB.replyView, hServ] at hs; cases hs
  cases o with
  | tcb u =>
    have hU : st.objects[(SeLe4n.ThreadId.ofObjId k).toObjId]? = some (.tcb u) := hK
    have hVK : st.replyViews (SeLe4n.ThreadId.ofObjId k).toObjId = some u.replyView := by
      unfold SystemState.replyViews; rw [SystemState.getObject?_eq_getElem, hU]; rfl
    have f1 : (u.queueNextCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      obtain ⟨tb, hB, hP⟩ := hI.dualQueueSystemInvariant.linkIntegrity.1 _ u hU _ (dec e)
      rw [isT hB] at hP; unfold TCB.queuePrev at hP; rw [hQP] at hP; cases hP
    have prevX : u.queuePrev ≠ some (SeLe4n.ThreadId.ofObjId x) := fun e => by
      obtain ⟨ta, hA, hN⟩ := hI.dualQueueSystemInvariant.linkIntegrity.2 _ u hU _ e
      rw [isT hA] at hN; unfold TCB.queueNext at hN; rw [hQN] at hN; cases hN
    have f2 : (u.queuePrevCode == x.val + 1) = false :=
      beq_eq_false_iff_ne.mpr fun e => prevX (dec e)
    have f3 : (u.queuePPrevCode == x.val + 1 + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      have hAg := hI.dualQueueSystemInvariant.pprevAgrees _ u hU
      unfold TCB.queuePPrevAgreesWithPrev at hAg
      simp only [TCB.queuePPrev, e, QueuePPrev.ofOptCode] at hAg
      exact prevX hAg
    have hNW := h.notificationWaiterConsistent
    have f4 : (u.ntfnNextCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      by_cases hb : ∃ oid, u.ipcState = .blockedOnNotification oid
      · obtain ⟨oid, hb⟩ := hb
        obtain ⟨_, -, -, -, hNx⟩ := hNW.2.1 _ u oid hU hb
        obtain ⟨-, tb, hB, hBl, -⟩ := hNx _ (dec e)
        exact notBlocked hB _ (by intro e'; cases e') hBl
      · have := (hNW.2.2.2.2 _ u hU (fun oid e' => hb ⟨oid, e'⟩)).2
        unfold TCB.ntfnNext at this; rw [dec e] at this; cases this
    have f5 : (u.ntfnPrevCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      have hp : u.ntfnPrev = some (SeLe4n.ThreadId.ofObjId x) := dec e
      by_cases hb : ∃ oid, u.ipcState = .blockedOnNotification oid
      · obtain ⟨oid, hb⟩ := hb
        obtain ⟨ntfn, hN, hHd, -⟩ := hNW.2.1 _ u oid hU hb
        rcases hHd with hH | ⟨a, ta, hPa, hA, hAB, -⟩
        · rw [hNW.headNoPrev hN hH hU] at hp; cases hp
        · rw [hp] at hPa; cases hPa
          exact notBlocked hA _ (by intro e'; cases e') hAB
      · have := (hNW.2.2.2.2 _ u hU (fun oid e' => hb ⟨oid, e'⟩)).1
        rw [hp] at this; cases this
    have fRun : (u.runCoreCode != 0 && decide (u.runCoreCode ≤ Concurrency.numCores) &&
        (u.runNextCode == x.val + 1 || u.runPrevCode == x.val + 1 ||
          u.runBucketNextCode == x.val + 1 || u.runBucketPrevCode == x.val + 1)) = false := by
      cases g : (u.runCoreCode != 0 && decide (u.runCoreCode ≤ Concurrency.numCores)) with
      | false => rfl
      | true =>
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at g
        obtain ⟨c0, hc0⟩ := Nat.exists_eq_succ_of_ne_zero g.1
        have hlt : c0 < Concurrency.numCores := by omega
        cases hn : (u.runNextCode == x.val + 1 || u.runPrevCode == x.val + 1 ||
            u.runBucketNextCode == x.val + 1 || u.runBucketPrevCode == x.val + 1) with
        | false => rfl
        | true =>
          exfalso
          simp only [Bool.or_eq_true, beq_iff_eq] at hn
          have hz : u.runNextCode = LinkedQueue.code (SeLe4n.ThreadId.ofObjId x) ∨
              u.runPrevCode = LinkedQueue.code (SeLe4n.ThreadId.ofObjId x) ∨
              u.runBucketNextCode = LinkedQueue.code (SeLe4n.ThreadId.ofObjId x) ∨
              u.runBucketPrevCode = LinkedQueue.code (SeLe4n.ThreadId.ofObjId x) := by
            rcases hn with ((e | e) | e) | e
            · exact .inl e
            · exact .inr (.inl e)
            · exact .inr (.inr (.inl e))
            · exact .inr (.inr (.inr e))
          obtain ⟨tz, hTz, hTzc⟩ := SystemState.runQueueRefined.neighbour_queued h.runQueueRefined ⟨c0, hlt⟩
            ((SystemState.getTcb?_eq_some_iff st _ u).mpr hU) hc0 hz
          rw [isT ((SystemState.getTcb?_eq_some_iff st _ tz).mp hTz), hRC] at hTzc
          cases hTzc
    have waiterNe : ∀ {s : SeLe4n.ThreadId}, u.blockingServer? = some s →
        ∃ vs l, ReplyViews.queue st.replyViews s vs l ∧ SeLe4n.ThreadId.ofObjId k ∈ l := by
      intro s hs
      obtain ⟨vs, hvs⟩ := V.2.1 _ u.replyView s hVK (by simpa [TCB.replyView])
      obtain ⟨l, hq⟩ := V.1 s _ hvs
      exact ⟨vs, l, hq, (hq.2.2.2 _).mpr ⟨_, hVK, by simpa [TCB.replyView]⟩⟩
    have f6 : (u.replyWaiterNextCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      cases hs : u.blockingServer? with
      | none =>
        have := (V.2.2.1 _ u.replyView hVK (by simpa [TCB.replyView])).2
        simp only [TCB.replyView] at this; omega
      | some s =>
        obtain ⟨_, l, hq, hKl⟩ := waiterNe hs
        have hXl := ReplyViews.chain_next_mem hq.1 hKl hVK (n := SeLe4n.ThreadId.ofObjId x)
          (by simp only [TCB.replyView]; exact dec e)
        exact serverOf ((hq.2.2.2 _).mp hXl)
    have f7 : (u.replyWaiterPrevCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      cases hs : u.blockingServer? with
      | none =>
        have := (V.2.2.1 _ u.replyView hVK (by simpa [TCB.replyView])).1
        simp only [TCB.replyView] at this; omega
      | some s =>
        obtain ⟨vs, l, hq, hKl⟩ := waiterNe hs
        by_cases hh : SeLe4n.ThreadId.ofOptCode vs.headCode = some (SeLe4n.ThreadId.ofObjId k)
        · have hCh := hq.1
          rw [hh] at hCh
          cases l with
          | nil => cases hKl
          | cons w l' =>
            obtain ⟨hw, v, hv, hp, -⟩ := hCh
            cases hw
            rw [hVK] at hv; cases hv
            simp only [TCB.replyView, dec e] at hp; cases hp
        · obtain ⟨z, hz, hzP⟩ := ReplyViews.chain_prev_mem hq.1 hKl hVK hh
          simp only [TCB.replyView, dec e] at hzP; cases hzP
          exact serverOf ((hq.2.2.2 _).mp hz)
    have f8 : (u.replyWaitersHeadCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      obtain ⟨l, hq⟩ := V.1 _ u.replyView hVK
      have hCh := hq.1
      simp only [TCB.replyView, dec e] at hCh
      exact serverOf ((hq.2.2.2 _).mp (ReplyViews.chain_head_mem hCh))
    have f9 : (u.scBindingScCode != 0 && u.scBindingOwnerCode == x.val + 1) = false := by
      cases g : (u.scBindingScCode != 0 && u.scBindingOwnerCode == x.val + 1) with
      | false => rfl
      | true =>
        exfalso
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at g
        obtain ⟨s0, hs0⟩ := Nat.exists_eq_succ_of_ne_zero g.1
        have hb : u.schedContextBinding = .donated ⟨s0⟩ (SeLe4n.ThreadId.ofObjId x) := by
          unfold TCB.schedContextBinding; rw [hs0, g.2]; rfl
        obtain ⟨-, ot, hO, -, ep, rt, hBl⟩ := hI.donationOwnerValid _ u _ _ hU hb
        exact notBlocked hO _ (by intro e'; cases e') hBl
    have f10 : (u.ipcStateCode == x.val + 1 + 4) = false := beq_eq_false_iff_ne.mpr fun e => by
      have hs : u.blockingServer? = some (SeLe4n.ThreadId.ofObjId x) := by
        simp [TCB.blockingServer?, TCB.ipcState, e, ThreadIpcState.ofCodes]; rfl
      obtain ⟨l, hq⟩ := V.1 _ t.replyView hVX
      have hCh := hq.1
      simp only [TCB.replyView, hRWH] at hCh
      have hl := ReplyViews.chain_none hCh
      have hKl := (hq.2.2.2 (SeLe4n.ThreadId.ofObjId k)).mpr ⟨_, hVK, by simpa [TCB.replyView]⟩
      rw [hl] at hKl; cases hKl
    simp only [objectNamesThread, f1, f2, f3, f4, f5, fRun, f6, f7, f8, f9, f10, Bool.or_false]
  | endpoint ep =>
    have hHB := hI.queueHeadBlockedConsistent k ep _ t hK hX
    have hTB := hI.endpointQueueTailBlockedConsistent k ep _ t hK hX
    have g1 : (ep.sendHeadCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      rcases hHB.2 (dec e) with hE | hE <;> rw [hReady] at hE <;> cases hE
    have g2 : (ep.sendTailCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      rcases hTB.2 (dec e) with hE | hE <;> rw [hReady] at hE <;> cases hE
    have g3 : (ep.recvHeadCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      have hE := hHB.1 (dec e); rw [hReady] at hE; cases hE
    have g4 : (ep.recvTailCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      have hE := hTB.1 (dec e); rw [hReady] at hE; cases hE
    simp only [objectNamesThread, g1, g2, g3, g4, Bool.or_false]
  | notification n =>
    obtain ⟨-, hHd, hTl⟩ := h.notificationWaiterConsistent.1 k n hK
    have g1 : (n.waitHeadCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      obtain ⟨tb, hB, hBl⟩ := hHd _ (dec e)
      exact notBlocked hB _ (by intro e'; cases e') hBl
    have g2 : (n.waitTailCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      obtain ⟨tb, hB, hBl, -⟩ := hTl _ (dec e)
      exact notBlocked hB _ (by intro e'; cases e') hBl
    have g3 : (n.boundTCBCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      have hB := (hI.notificationBindingReciprocal k).2 x.val (by
        simp [notificationBindingCodes, KernelObject.bindingCodes, hK, e])
      have hB' : (notificationBindingCodes st.objects[x]?).1 = k.val + 1 := hB
      simp [notificationBindingCodes, KernelObject.bindingCodes, hTx, hBN] at hB'
    simp only [objectNamesThread, g1, g2, g3, Bool.or_false]
  | reply r =>
    have g : (r.callerCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      obtain ⟨tb, hB, -, ep, rt, hBl⟩ :=
        hI.replyCallerLinkage.1.2 (SeLe4n.ReplyId.ofObjId k) r _ hK (dec e)
      exact notBlocked hB _ (by intro e'; cases e') hBl
    simp only [objectNamesThread, g]
  | schedContext sc =>
    have g : (sc.boundThreadCode == x.val + 1) = false := beq_eq_false_iff_ne.mpr fun e => by
      obtain ⟨tb, hB, hb⟩ := hBind.2 (SeLe4n.SchedContextId.ofObjId k) sc hK _ (dec e)
      rw [isT hB] at hb
      unfold TCB.schedContextBinding at hb; rw [hSC] at hb
      rcases hb with hb | ⟨_, hb⟩ <;> cases hb
    simp only [objectNamesThread, g]
  | _ => rfl

/-- **No object names a scheduling context the retire admits**
(`objectNamesSchedContext`), under the reachable invariants and the binding
pair, though the guard reads the context's own links alone.  A thread bound to
it, as its own or on loan, or holding it as its timeout budget, is answered by
`schedContextRetirable.tcbNamesNone`; a reply heading its stack by the context's
own head link (`donationChainWellFormed.headLinkResolves`), which it has none
of. -/
theorem schedContextRetirable.namedByNone {st : SystemState} (h : ipcReachable st)
    (hBind : schedContextBindingConsistent st) {x : SeLe4n.ObjId}
    (hR : schedContextRetirable st x = true)
    {k : SeLe4n.ObjId} {o : KernelObject} (hK : st.objects[k]? = some o) :
    objectNamesSchedContext o (x.val + 1) = false := by
  obtain ⟨sc, hS, -, -, hRep, -⟩ := schedContextRetirable_parts hR
  cases o with
  | tcb t =>
    exact schedContextRetirable.tcbNamesNone hR hBind h.ipcInvariantFull.donationOwnerValid
      h.allTimeoutBudgetsNone hK
  | reply r =>
    simp only [objectNamesSchedContext]
    cases hn : r.next with
    | none => rfl
    | some l =>
      cases l with
      | frame _ => rfl
      | head s =>
        cases hx : (s.val + 1 == x.val + 1) with
        | false => exact hx
        | true =>
          have hs : s.toObjId = x := by
            have e : s.val = x.val := by have := beq_iff_eq.mp hx; omega
            show (⟨s.val⟩ : SeLe4n.ObjId) = x
            rw [e]
          obtain ⟨sc', hS', hH⟩ := h.donationChainWellFormed.headLinkResolves
            (SeLe4n.ReplyId.ofObjId k) r s hK hn
          rw [hs, hS] at hS'; cases hS'
          rw [hRep] at hH; cases hH
  | _ => rfl

/-- **No core queues a replenishment for a context the retire admits**: every
queued context is bound (`replenishQueueEntriesBound_smp`), and an admitted one
is bound to no thread. -/
theorem schedContextRetirable.replenishQueuedNowhere {st : SystemState}
    (hQ : replenishQueueEntriesBound_smp st) {x : SeLe4n.ObjId}
    (hR : schedContextRetirable st x = true) (c : Concurrency.CoreId) (n : Nat) :
    (⟨x.val⟩, n) ∉ (st.scheduler.replenishQueueOnCore c).entries := by
  intro hMem
  obtain ⟨sc, hS, -⟩ := schedContextRetirable_parts hR
  obtain ⟨sc', hS', tid, hb⟩ := hQ c _ n hMem
  have hS'' := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS'
  have hx : (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x := rfl
  rw [hx, hS] at hS''; cases hS''
  rw [schedContextRetirable_boundThread hR hS] at hb; cases hb

end SeLe4n.Kernel
