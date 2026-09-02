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
notification bundles' companion. -/
def ipcReachable (st : SystemState) : Prop :=
  ipcInvariantFull st ∧
  st.objects.invExt ∧
  allTimeoutBudgetsNone st ∧
  pendingMessageCapBadgesWellFormed st ∧
  notificationWaiterConsistent st

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
    _root_.SeLe4n.Kernel.notificationWaiterConsistent st := h.2.2.2.2

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
    default_notificationWaiterConsistent⟩
  · exact capabilityInvariantBundle.objectsInvExt
      (Architecture.default_system_state_proofLayerInvariantBundle).2.1
  · intro tid tcb hTcb
    rw [Architecture.default_objects_none] at hTcb
    cases hTcb
  · intro tid tcb m hTcb
    rw [Architecture.default_objects_none] at hTcb
    cases hTcb

end SeLe4n.Kernel
