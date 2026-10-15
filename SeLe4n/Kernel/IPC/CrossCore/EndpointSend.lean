-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6: PRODUCTION. The cross-core `Send` transition. Enters the
-- production import closure through the live `.send` dispatch arm
-- (`API.dispatchWithCap{,Checked}` via `endpointSendDualWithCaps`).

import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch

/-!
# WS-SM SM6 — the cross-core `Send`

`endpointSendDual` (`IPC/DualQueue/Transport.lean`) is the single-core send. It
has two scheduling effects, and **both were boot-pinned**:

* on a **rendezvous** it wakes the dequeued receiver with `ensureRunnable`,
  which enqueues on `bootCoreId` regardless of the receiver's `cpuAffinity`;
* on the **block** path it deschedules the sender with `removeRunnable`, which
  clears the boot core's slots regardless of where the sender is running.

PR #861 review round 10 found the live `.send` arm still routed there. The
consequences on a multi-core system are the two halves of the same bug: a
receiver woken by a remote sender is placed on a run queue its own core never
dispatches from, and a sender that blocks on a secondary core **remains current
and runnable on that core** — it should have stopped, and instead keeps being a
candidate for dispatch.

`endpointSendDualOnCore` is the per-core form, built exactly like its SM6.A/SM6.C
siblings (`endpointCallOnCore`, `endpointReceiveDualOnCore`): the receiver is
woken on **its own home core** via the SM5.C `wakeThread`, which returns the
`.reschedule` SGI that core must receive, and the sender is descheduled on the
**executing** core via `removeRunnableOnCore`. Every non-scheduling step is
shared with the single-core transition, so the message semantics — bounds
checks, badge propagation, the `pendingReceiveReply` clear on a plain `Send`
completing a server-first `Recv` — are unchanged.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

/-- WS-SM SM6 (operation): the cross-core `Send`.

Mirrors `endpointSendDual` step for step, replacing its two boot-pinned
scheduling calls with their per-core forms:

* **rendezvous** — `wakeThread st'' receiver executingCore` routes the wake to
  `determineTargetCore st'' receiver`, the receiver's *own* home core, and
  surfaces the `.reschedule` SGI that core must take;
* **block** — `removeRunnableOnCore st'' sender executingCore` clears the
  sender from the core it is actually running on.

Fail-closed on every error arm: the **pre-state** is returned, so a rejected
send leaves neither the endpoint queues nor the scheduler touched. -/
def endpointSendDualOnCore (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  if msg.registers.size > maxMessageRegisters then (st, .error .ipcMessageTooLarge)
  else if msg.caps.size > maxExtraCaps then (st, .error .ipcMessageTooManyCaps)
  else
  match st.getEndpoint? endpointId with
  | some ep =>
      match ep.receiveQ.head with
      | some _ =>
          -- PR #873 round 17: the sender has to exist even though this arm
          -- never looks it up -- the message goes straight from the argument
          -- into the receiver's TCB. In lockstep with `endpointSendDual`,
          -- which is what `endpointSendDualOnCore_eq_single_on_bootCore` ties
          -- the two to.
          match st.getTcb? sender with
          | none => (st, .error .objectNotFound)
          | some _ =>
          match endpointQueuePopHead endpointId true st with
          | .error e => (st, .error e)
          | .ok (receiver, _tcb, st') =>
              match storeTcbReceiveComplete st' receiver (some msg) with
              | .error e => (st, .error e)
              | .ok st'' =>
                  -- Cross-core receiver wake (SM5.C): route to the receiver's
                  -- HOME core, not the boot core.
                  --
                  -- Bound once. Projecting `.1` and `.2` out of two separate
                  -- calls made the compiled path run the whole wake twice --
                  -- object-store update and run-queue insertion included -- to
                  -- take the state from one and the SGI from the other, on the
                  -- send rendezvous, which is as hot as this kernel's paths get.
                  let (stWoken, wakeSgi) := wakeThread st'' receiver executingCore
                  (stWoken, .ok wakeSgi)
      | none =>
          match endpointQueueEnqueue endpointId false sender st with
          | .error e => (st, .error e)
          | .ok st' =>
              match storeTcbIpcStateAndMessage st' sender (.blockedOnSend endpointId)
                  (some msg) with
              | .error e => (st, .error e)
              | .ok st'' =>
                  -- The sender blocks on the core it is RUNNING on.
                  (removeRunnableOnCore st'' sender executingCore, .ok none)
  | none =>
      -- Typed-accessor dispatch (AK7 cascade discipline): `getEndpoint?` is
      -- `none` for both an absent object and a wrong-kinded one, so the
      -- presence question is asked of the kind-agnostic accessor `getObject?`
      -- -- a present-but-wrong-kind object fails with `.invalidCapability`, a
      -- genuinely absent one with `.objectNotFound`.  Reading the store raw
      -- here would have been the very pattern the comment claimed to avoid.
      if (st.getObject? endpointId).isSome then (st, .error .invalidCapability)
      else (st, .error .objectNotFound)

/-- WS-ZA ZA4.7: the endpoint a send rendezvous leaves: its receive queue
starts at the popped head's successor, given as its code
(`SeLe4n.ThreadId.optCode`), so a caller holding the successor's link code
passes it without building an `Option`. -/
@[inline] def sendRendezvousEndpoint (nextCode : Nat) :
    KernelObject → KernelObject
  | .endpoint e =>
      -- the queue ends are codes in the endpoint, rewritten in its cell
      -- (`Endpoint.withReceiveQ_head`)
      match nextCode with
      | 0 => .endpoint { e with recvHeadCode := 0, recvTailCode := 0 }
      | c + 1 => .endpoint { e with recvHeadCode := c + 1 }
  | o => o

/-- WS-ZA ZA4.7: the receive completion a send rendezvous writes into the
woken receiver. -/
@[inline] def receiveCompleteTcb (msg : IpcMessage) (t : TCB) : TCB :=
  (TCB.setIpcState { t with pendingMessage := some msg, pendingReceiveReplyCode := 0 } .ready)

/-- WS-ZA ZA4.7: a thread taken off an endpoint queue: its three link codes
cleared (`tcbWithQueueLinks t none none none` by definition). -/
@[inline] def tcbOffQueue (t : TCB) : TCB :=
  { t with queuePrevCode := 0, queuePPrevCode := 0, queueNextCode := 0 }

/-- WS-ZA ZA4.7: a queue's new head: no predecessor, its back-pointer the
queue head, as codes (`tcbAsQueueHead_eq`). -/
@[inline] def tcbAsQueueHead (t : TCB) : TCB :=
  { t with queuePrevCode := 0, queuePPrevCode := 1 }

theorem tcbAsQueueHead_eq (t : TCB) :
    tcbAsQueueHead t = tcbWithQueueLinks t none (some .endpointHead) t.queueNext := by
  simp only [tcbAsQueueHead, tcbWithQueueLinks, TCB.optCode_queueNext]
  rfl

/-- WS-ZA ZA4.7: the send rendezvous's writes, each in its slot: the head
popped off the receive queue, its successor made the new head, the popped
receiver unlinked and handed the message.  Compiled as its own function so
each update is specialised in. -/
@[noinline] def storeSendRendezvous (st : SystemState) (endpointId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (msg : IpcMessage) :
    SystemState :=
  let s1 := st.modifyObject endpointId (sendRendezvousEndpoint (ThreadId.optCode next))
  let s2 := match next with
    | none => s1
    | some n => s1.updateTcb n tcbAsQueueHead
  (s2.updateTcb head tcbOffQueue).updateTcb head
    (receiveCompleteTcb msg)

/-- WS-ZA ZA4.7: **the send rendezvous writes only its slots** — the endpoint,
the popped receiver and its successor each rewritten where it stands
(`RHTable.findsInPlace`), each store changing only `objects`
(`storeLeavesIndexAndTypes`), the receiver and its successor distinct,
unreserved TCBs. -/
@[inline] def sendWakesInPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) : Bool :=
  !head.isReserved &&
  storeLeavesIndexAndTypes st endpointId .endpoint &&
  st.objects.findsInPlace endpointId &&
  storeLeavesIndexAndTypes st head.toObjId .tcb &&
  st.objects.findsInPlace head.toObjId &&
  (match next with
   | none => true
   | some n => !n.isReserved && n != head &&
       storeLeavesIndexAndTypes st n.toObjId .tcb &&
       st.objects.findsInPlace n.toObjId &&
       (st.getTcb? n).isSome)

/-- WS-ZA ZA4.7: the guarded send rendezvous's writes are the specification's
pop and receive completion. -/
theorem sendRendezvous_inPlace_eq (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (head : SeLe4n.ThreadId) (ht : TCB) (msg : IpcMessage)
    (hE : st.objects[endpointId]? = some (.endpoint ep))
    (hH : ep.receiveQ.head = some head)
    (hT : st.objects[head.toObjId]? = some (.tcb ht))
    (hG : sendWakesInPlace st endpointId head ht.queueNext = true) :
    (match endpointQueuePopHead endpointId true st with
      | .error _ => none
      | .ok (r, _, st') =>
          match storeTcbReceiveComplete st' r (some msg) with
          | .error _ => none
          | .ok st'' => some (r, st''))
      = some (head, storeSendRendezvous st endpointId head ht.queueNext msg) := by
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨hRes, hLE⟩, hFE⟩, hLH⟩, hFH⟩, hNx⟩ := hG
  have hNeEH : endpointId ≠ head.toObjId := by
    intro h; rw [h, hT] at hE; cases hE
  have hLook : lookupTcb st head = some ht := by
    simp only [lookupTcb, hRes, Bool.false_eq_true, ↓reduceIte]
    exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  -- the endpoint store, as one state both sides name
  obtain ⟨S1, hS1⟩ : ∃ S1 : SystemState, S1 = { st with objects :=
      (st.objects.insert endpointId
        (sendRendezvousEndpoint (ThreadId.optCode ht.queueNext) (.endpoint ep))) } :=
    ⟨_, rfl⟩
  have hMo : st.modifyObject endpointId (sendRendezvousEndpoint (ThreadId.optCode ht.queueNext)) =
      S1 := by
    rw [hS1]; unfold SystemState.modifyObject
    rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? hE]
  have hNotV : ∀ r, sendRendezvousEndpoint (ThreadId.optCode ht.queueNext) (.endpoint ep) ≠
      .vspaceRoot r := by
    intro r h; simp only [sendRendezvousEndpoint] at h; split at h <;> cases h
  have hF1 : ∀ k, S1.objects.findsInPlace k = st.objects.findsInPlace k := fun k => by
    rw [hS1]; exact SeLe4n.Kernel.RobinHood.RHTable.findsInPlace_insert_of_findsInPlace k _ hFE
  have hG1 : ∀ k, endpointId ≠ k → S1.objects[k]? = st.objects[k]? := fun k hk => by
    rw [hS1]; exact SeLe4n.Kernel.RobinHood.RHTable.get?_insert_ne_of_findsInPlace k _ hFE hk
  have hL1 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes S1 id ty = true := fun h => by
    rw [hS1]; exact storeLeavesIndexAndTypes_insert_inPlace hFE hNotV h
  have hT1 : S1.getTcb? head = some ht :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr ((hG1 _ hNeEH).trans hT)
  unfold endpointQueuePopHead storeSendRendezvous
  simp only [SystemState.getObject?, hE, hH, hLook, Bool.not_true, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]
  rw [hMo]
  cases hN : ht.queueNext with
  | none =>
    have hSt : storeObject endpointId (.endpoint (ep.withReceiveQ {})) st = .ok ((), S1) := by
      rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLE), hS1, hN]; rfl
    simp only [hSt]
    have hQ : storeTcbQueueLinks S1 head none none none =
        .ok (S1.updateTcb head tcbOffQueue) :=
      modifyTcb_eq_updateTcb _ hRes hT1 (hL1 hLH)
    rw [hQ]
    simp only []
    have hT3 := updateTcb_getTcb?_self_of_findsInPlace
      tcbOffQueue hT1 ((hF1 _).trans hFH)
    have hRC : storeTcbReceiveComplete
        (S1.updateTcb head tcbOffQueue) head (some msg) =
        .ok ((S1.updateTcb head tcbOffQueue).updateTcb head
          (receiveCompleteTcb msg)) :=
      modifyTcb_eq_updateTcb _ hRes hT3
        (updateTcb_storeLeaves _ hT1 ((hF1 _).trans hFH) (hL1 hLH))
    rw [hRC]
  | some n =>
    rw [hN] at hNx
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hNx
    obtain ⟨⟨⟨⟨hRn, hNeH⟩, hLN⟩, hFN⟩, hTnB⟩ := hNx
    obtain ⟨nt, hTn⟩ := Option.isSome_iff_exists.mp hTnB
    have hNeEN : endpointId ≠ n.toObjId := by
      intro h; rw [h, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTn] at hE; cases hE
    have hNeNH : n.toObjId ≠ head.toObjId := fun h => hNeH (SeLe4n.ThreadId.toObjId_injective _ _ h)
    have hSt : storeObject endpointId
        (.endpoint (ep.withReceiveQ { head := some n, tail := ep.receiveQ.tail })) st =
        .ok ((), S1) := by
      rw [Endpoint.withReceiveQ_head, storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLE), hS1, hN]; rfl
    simp only [hSt]
    have hTn1 : S1.getTcb? n = some nt :=
      (SystemState.getTcb?_eq_some_iff _ _ _).mpr
        ((hG1 _ hNeEN).trans ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTn))
    have hLookN : lookupTcb S1 n = some nt := by
      simp only [lookupTcb, hRn, Bool.false_eq_true, ↓reduceIte]; exact hTn1
    rw [hLookN]
    simp only []
    let g := tcbAsQueueHead
    have hQn : storeTcbQueueLinks S1 n none (some .endpointHead) nt.queueNext =
        .ok (S1.updateTcb n g) := by
      have := modifyTcb_eq_updateTcb (fun t => tcbWithQueueLinks t none (some .endpointHead)
        nt.queueNext) hRn hTn1 (hL1 hLN)
      rw [show storeTcbQueueLinks S1 n none (some .endpointHead) nt.queueNext =
        modifyTcb S1 n (fun t => tcbWithQueueLinks t none (some .endpointHead) nt.queueNext)
        from rfl, this, SystemState.updateTcb_eq_of_some hTn1, SystemState.updateTcb_eq_of_some hTn1]
      simp only [g, tcbAsQueueHead_eq]
    rw [hQn]
    simp only []
    obtain ⟨S2, hS2⟩ : ∃ S2 : SystemState, S2 = S1.updateTcb n g := ⟨_, rfl⟩
    rw [← hS2]
    have hFn1 : S1.objects.findsInPlace n.toObjId = true := (hF1 _).trans hFN
    have hT2 : S2.getTcb? head = some ht := by
      rw [hS2, SystemState.getTcb?_eq_some_iff,
        updateTcb_get?_ne_of_findsInPlace g hTn1 hFn1 hNeNH]
      exact (SystemState.getTcb?_eq_some_iff _ _ _).mp hT1
    have hF2 : ∀ k, S2.objects.findsInPlace k = st.objects.findsInPlace k := fun k => by
      rw [hS2, updateTcb_findsInPlace g hTn1 hFn1, hF1]
    have hL2 : storeLeavesIndexAndTypes S2 head.toObjId .tcb = true := by
      rw [hS2]; exact updateTcb_storeLeaves g hTn1 hFn1 (hL1 hLH)
    have hQ : storeTcbQueueLinks S2 head none none none =
        .ok (S2.updateTcb head tcbOffQueue) :=
      modifyTcb_eq_updateTcb _ hRes hT2 hL2
    rw [hQ]
    simp only []
    have hT3 := updateTcb_getTcb?_self_of_findsInPlace
      tcbOffQueue hT2 ((hF2 _).trans hFH)
    have hRC : storeTcbReceiveComplete
        (S2.updateTcb head tcbOffQueue) head (some msg) =
        .ok ((S2.updateTcb head tcbOffQueue).updateTcb head
          (receiveCompleteTcb msg)) :=
      modifyTcb_eq_updateTcb _ hRes hT3
        (updateTcb_storeLeaves _ hT2 ((hF2 _).trans hFH) hL2)
    rw [hRC]

/-- WS-ZA ZA4.7: the compiled `endpointSendDualOnCore`.  A rendezvous whose
writes stay in their slots (`sendWakesInPlace`) makes them in place
(`storeSendRendezvous`, `sendRendezvous_inPlace_eq`) and holds no pre-state
for a refusal that cannot happen (`ZERO_ALLOCATION_SYSCALL_PLAN.md` D1);
otherwise the specification's body. -/
def endpointSendDualOnCoreImpl (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  if msg.registers.size > maxMessageRegisters then (st, .error .ipcMessageTooLarge)
  else if msg.caps.size > maxExtraCaps then (st, .error .ipcMessageTooManyCaps)
  else
  match st.getEndpoint? endpointId with
  | some ep =>
      match ep.receiveQ.head with
      | some head =>
          match st.getTcb? sender with
          | none => (st, .error .objectNotFound)
          | some _ =>
          match st.getTcb? head with
          | some ht =>
              if sendWakesInPlace st endpointId head ht.queueNext then
                let (stWoken, wakeSgi) := wakeThread
                  (storeSendRendezvous st endpointId head ht.queueNext msg) head executingCore
                (stWoken, .ok wakeSgi)
              else
              match endpointQueuePopHead endpointId true st with
              | .error e => (st, .error e)
              | .ok (receiver, _tcb, st') =>
                  match storeTcbReceiveComplete st' receiver (some msg) with
                  | .error e => (st, .error e)
                  | .ok st'' =>
                      let (stWoken, wakeSgi) := wakeThread st'' receiver executingCore
                      (stWoken, .ok wakeSgi)
          | none =>
              match endpointQueuePopHead endpointId true st with
              | .error e => (st, .error e)
              | .ok (receiver, _tcb, st') =>
                  match storeTcbReceiveComplete st' receiver (some msg) with
                  | .error e => (st, .error e)
                  | .ok st'' =>
                      let (stWoken, wakeSgi) := wakeThread st'' receiver executingCore
                      (stWoken, .ok wakeSgi)
      | none =>
          match endpointQueueEnqueue endpointId false sender st with
          | .error e => (st, .error e)
          | .ok st' =>
              match storeTcbIpcStateAndMessage st' sender (.blockedOnSend endpointId)
                  (some msg) with
              | .error e => (st, .error e)
              | .ok st'' => (removeRunnableOnCore st'' sender executingCore, .ok none)
  | none =>
      if (st.getObject? endpointId).isSome then (st, .error .invalidCapability)
      else (st, .error .objectNotFound)

@[csimp] theorem endpointSendDualOnCore_eq_impl :
    @endpointSendDualOnCore = @endpointSendDualOnCoreImpl := by
  funext endpointId sender msg executingCore st
  unfold endpointSendDualOnCore endpointSendDualOnCoreImpl
  split
  · rfl
  · split
    · rfl
    · cases hEp : st.getEndpoint? endpointId with
      | none => rfl
      | some ep =>
        dsimp only
        cases hH : ep.receiveQ.head with
        | none => rfl
        | some head =>
          dsimp only
          cases hS : st.getTcb? sender with
          | none => rfl
          | some _ =>
            dsimp only
            cases hTo : st.getTcb? head with
            | none => rfl
            | some ht =>
                dsimp only
                by_cases hG : sendWakesInPlace st endpointId head ht.queueNext = true
                · rw [if_pos hG]
                  have h := sendRendezvous_inPlace_eq st endpointId ep head ht msg
                    ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp) hH
                    ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTo) hG
                  revert h
                  split
                  · intro h; cases h
                  · next r _ st' hPop =>
                    split
                    · intro h; cases h
                    · next st'' hRC =>
                      intro h
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      rfl
                · rw [if_neg hG]

/-- WS-SM SM6: the absent-endpoint arm is fail-closed — the pre-state is
returned untouched.

This used to be called `…_bootCore_state` and to claim, in its docstring, that
"the per-core send agrees with the single-core `endpointSendDual` on the
resulting state". It proved no such thing: `hNoEndpoint` and `hAbsent` together
pin it to the `.objectNotFound` arm, where the transition trivially returns the
pre-state, and the statement never mentioned `endpointSendDual` at all
(PR #861 review round 15). The real bridges are the two theorems below, one per
success path; this one is renamed to say what it actually checks. -/
theorem endpointSendDualOnCore_absent_endpoint (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hTooLarge : ¬ (msg.registers.size > maxMessageRegisters))
    (hTooMany : ¬ (msg.caps.size > maxExtraCaps))
    (hNoEndpoint : st.getEndpoint? endpointId = none)
    (hAbsent : (st.objects[endpointId]?).isSome = false) :
    endpointSendDualOnCore endpointId sender msg executingCore st
      = (st, .error .objectNotFound) := by
  simp [endpointSendDualOnCore, hTooLarge, hTooMany, hNoEndpoint, hAbsent]

/-- WS-SM SM6 (**the wake bridge**): on the boot core, the per-core wake commits
exactly what the single-core `ensureRunnable` commits.

The two are *not* the same function, which is why this needs stating rather than
asserting. `enqueueRunnableOnCore` guards on `runnableOnSomeCore` (all cores)
where `ensureRunnable` guards on boot-core membership, and it additionally writes
the object store, marking the woken thread `.ready`. Each difference is
discharged by a hypothesis that is true on the wake paths:

* `hHome` — the thread's home is the boot core, the only placement the
  single-core transition models;
* `hNotElsewhere` — it is queued on no other core, which collapses
  `runnableOnSomeCore` onto the boot-core test;
* `hReady` — its `ipcState` is already `.ready` (every wake path stores the
  thread ready before enqueueing it), so the object write re-inserts the value
  already present;
* `hNoResize` — and the table is below its resize threshold, so that re-insert
  is the identity rather than a rehash.

The last two are exactly `RHTable.insert_eq_self_of_get?`: a Robin Hood table has
no extensionality principle, so "the insert writes back what was already there"
had to be proved structurally, by showing the insert walk and the lookup walk
run in lockstep down the same probe sequence. -/
theorem wakeThread_bootCore_eq_ensureRunnable (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb)
    (hHome : determineTargetCore st tid = bootCoreId)
    (hNotElsewhere : ∀ c : CoreId, c ≠ bootCoreId → st.queuedOn c tid = false)
    (hReady : tcb.ipcState = .ready)
    (hNoResize : ¬ (st.objects.size * 4 ≥ st.objects.capacity * 3)) :
    (wakeThread st tid bootCoreId).1 = ensureRunnable st tid := by
  unfold wakeThread enqueueRunnableOnCore ensureRunnable
  simp only [hHome, hTcb, SystemState.getTcbWitnessed?_eq_some hTcb, SystemState.rewriteObject]
  -- `runnableOnSomeCore` collapses onto the boot-core membership test.
  have hSome : runnableOnSomeCore st tid = st.queuedOn bootCoreId tid := by
    unfold runnableOnSomeCore
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨c, -, hc⟩
      by_cases hcb : c = bootCoreId
      · exact hcb ▸ hc
      · rw [hNotElsewhere c hcb] at hc; cases hc
    · intro h
      exact ⟨bootCoreId, SeLe4n.Kernel.Concurrency.mem_allCores _, h⟩
  -- `hReady` makes the wake's object write a re-store of the value already
  -- present: structure eta collapses the update to the TCB itself.
  have hEta : ((tcb.setIpcState (.ready : ThreadIpcState)) : TCB) = tcb := by
    rw [← hReady, TCB.setIpcState_ipcState]
  have hObj : st.objects.insert tid.toObjId (.tcb (tcb.setIpcState .ready))
      = st.objects := by
    refine SeLe4n.Kernel.RobinHood.RHTable.insert_eq_self_of_get? _ _ _ hNoResize ?_
    have hRaw := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
    rw [RHTable_getElem?_eq_get?] at hRaw
    rw [hEta]
    exact hRaw
  have hSt : ({ st with objects :=
      (st.objects.insert tid.toObjId (.tcb (tcb.setIpcState .ready))) } : SystemState)
      = st := by
    rw [hObj]
  simp only [hSt]
  unfold wakeDeclines
  rw [hSome]
  by_cases hMem : st.queuedOn bootCoreId tid = true
  · simp [hMem]
  · by_cases hA : st.runEnqueueAdmits bootCoreId tid = true
    · simp [hMem, hA]
    · simp [hMem, hA]

/-- WS-SM SM6 (**the blocking leg's bootCore bridge**): with no receiver waiting,
the per-core send on the boot core commits **exactly** the single-core
`endpointSendDual`'s state.

Unconditional on this path, and the reason is one `rfl`: the two transitions run
the same enqueue and the same TCB store, and differ only in the final
deschedule — `removeRunnableOnCore … bootCoreId` *is* `removeRunnable`
(`removeRunnableOnCore_bootCoreId`). This is the refinement claim the old
`…_bootCore_state` docstring wanted and did not make. -/
theorem endpointSendDualOnCore_bootCore_block_eq_single (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (st st' : SystemState) (ep : Endpoint)
    (hEp : st.getEndpoint? endpointId = some ep)
    (hNoReceiver : ep.receiveQ.head = none)
    (hSingle : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    (endpointSendDualOnCore endpointId sender msg bootCoreId st).1 = st' := by
  -- The bounds guards are derived, not required: a successful single-core send
  -- already refutes them, so making the caller re-supply them would be
  -- redundant. Both sides then reduce past the same two `if`s.
  have hRegs : ¬ (msg.registers.size > maxMessageRegisters) := by
    intro h; rw [endpointSendDual] at hSingle; simp [h] at hSingle
  have hCaps : ¬ (msg.caps.size > maxExtraCaps) := by
    intro h; rw [endpointSendDual] at hSingle; simp [hRegs, h] at hSingle
  -- The single-core form matches the object store directly while the per-core
  -- one goes through `getEndpoint?` (the AK7 typed-accessor discipline), so the
  -- raw form is *recovered here* rather than demanded of the caller — stating it
  -- as a hypothesis would put a raw object-store pattern on the public surface.
  have hRaw := (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
  unfold endpointSendDualOnCore
  unfold endpointSendDual SystemState.getObject? at hSingle
  simp only [hRegs, hCaps, hRaw, hEp, hNoReceiver, if_false] at hSingle ⊢
  repeat' split at hSingle
  all_goals simp_all [removeRunnableOnCore_bootCoreId]

/-- WS-SM SM6 (**the rendezvous leg's bootCore bridge**): with a receiver
waiting whose home is the boot core, the per-core send on the boot core commits
**exactly** the single-core `endpointSendDual`'s state.

This is the leg that needed real work. The two transitions run the same pop and
the same receive-complete store, and then diverge: the single-core one calls
`ensureRunnable`, the per-core one calls `wakeThread`, and those are genuinely
different functions. `wakeThread_bootCore_eq_ensureRunnable` is what closes the
gap, and its object-store half rests in turn on the Robin Hood insert-identity
lemma — a hash table has no extensionality principle, so "re-inserting the value
already present changes nothing" had to be proved by walking the probe sequence.

The mid-states are named by the theorem, as everywhere else on this surface: the
wake's four side conditions are conditions on the state the wake actually sees,
and inventing a pre-state form for them would mean asserting frame lemmas this
module cannot see. -/
theorem endpointSendDualOnCore_bootCore_rendezvous_eq_single (endpointId : SeLe4n.ObjId)
    (sender receiver : SeLe4n.ThreadId) (msg : IpcMessage)
    (st st' stPop stRecv : SystemState) (ep : Endpoint) (headTcb rTcb : TCB)
    (hEp : st.getEndpoint? endpointId = some ep)
    (hReceiver : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, headTcb, stPop))
    (hStore : storeTcbReceiveComplete stPop receiver (some msg) = .ok stRecv)
    (hTcb : stRecv.getTcb? receiver = some rTcb)
    (hHome : determineTargetCore stRecv receiver = bootCoreId)
    (hNotElsewhere : ∀ c : CoreId, c ≠ bootCoreId → stRecv.queuedOn c receiver = false)
    (hReady : rTcb.ipcState = .ready)
    (hNoResize : ¬ (stRecv.objects.size * 4 ≥ stRecv.objects.capacity * 3))
    (hSingle : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    (endpointSendDualOnCore endpointId sender msg bootCoreId st).1 = st' := by
  have hRegs : ¬ (msg.registers.size > maxMessageRegisters) := by
    intro h; rw [endpointSendDual] at hSingle; simp [h] at hSingle
  have hCaps : ¬ (msg.caps.size > maxExtraCaps) := by
    intro h; rw [endpointSendDual] at hSingle; simp [hRegs, h] at hSingle
  have hRaw := (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
  unfold endpointSendDualOnCore
  unfold endpointSendDual SystemState.getObject? at hSingle
  -- PR #873 round 17: both sides now resolve the sender first, so the split is
  -- shared. The declining arm cannot be this `.ok`, which is what discharges it
  -- without adding a hypothesis to the statement.
  cases hSnd : st.getTcb? sender with
  | none =>
    exfalso
    simp only [hRegs, hCaps, hRaw, hReceiver, hSnd, if_false] at hSingle
    simp at hSingle
  | some _ =>
  simp only [hRegs, hCaps, hRaw, hEp, hReceiver, hSnd, hPop, hStore, if_false] at hSingle ⊢
  -- Both sides are now the same mid-state, wired to two different wakes.
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hSingle
  rw [← hSingle]
  exact wakeThread_bootCore_eq_ensureRunnable stRecv receiver rTcb hTcb hHome
    hNotElsewhere hReady hNoResize

/-- WS-SM SM6: the bounds rejections are fail-closed and state-preserving. -/
theorem endpointSendDualOnCore_tooLarge (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (h : msg.registers.size > maxMessageRegisters) :
    endpointSendDualOnCore endpointId sender msg executingCore st
      = (st, .error .ipcMessageTooLarge) := by
  simp [endpointSendDualOnCore, h]

theorem endpointSendDualOnCore_tooManyCaps (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hLarge : ¬ (msg.registers.size > maxMessageRegisters))
    (h : msg.caps.size > maxExtraCaps) :
    endpointSendDualOnCore endpointId sender msg executingCore st
      = (st, .error .ipcMessageTooManyCaps) := by
  simp [endpointSendDualOnCore, hLarge, h]

-- ============================================================================
-- §2 Cross-core `endpointSendDualWithCaps`
-- ============================================================================

/-- WS-SM SM6 (operation): endpoint send with capability transfer, across cores.

The exact shape of its SM6.A sibling `endpointCallWithCapsOnCore`: the cross-core
`endpointSendDualOnCore` rendezvous (which surfaces the receiver-wake SGI), then —
on an immediate rendezvous carrying caps — `ipcUnwrapCaps` installs the
transferred capabilities into the receiver's CSpace, gated on the endpoint's
`grant` right. Returns the post-state, the capability-transfer summary, and the
optional cross-core SGI.

Capability-transfer behaviour is unchanged from `endpointSendDualWithCaps`,
including the AK1-I fail-closed `.invalidCapability` on a receiver with no CSpace
root (the NI-symmetry fix shared by all three transfer paths). -/
def endpointSendDualWithCapsOnCore
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (CapTransferSummary × Option (CoreId × SgiKind)) :=
  -- PR #873 round 13: stamp the endpoint's grant right into the message, so the
  -- queued ordering and the immediate rendezvous read the same authority from the
  -- same place. See `endpointSendDualWithCaps` for the ordering this removes.
  let hasReceiver := match st.getEndpoint? endpointId with
    | some ep => ep.receiveQ.head.isSome
    | none => false
  match endpointSendDualOnCore endpointId sender { msg with capsGranted := endpointRights.mem .grant } executingCore st with
  | (st', .error e) => (st', .error e)
  | (st', .ok sgi) =>
      if !hasReceiver || msg.caps.isEmpty then (st', .ok ({ results := #[] }, sgi))
      else
        match st.getEndpoint? endpointId with
        | some ep =>
          match ep.receiveQ.head with
          | some receiverId =>
            match lookupCspaceRoot st' receiverId with
            | some recvRoot =>
              match ipcUnwrapCaps { msg with capsGranted := endpointRights.mem .grant } recvRoot
                  receiverSlotBase (endpointRights.mem .grant) st' with
              | .error e => (st', .error e)
              | .ok (summary, st'') => (st'', .ok (summary, sgi))
            | none => (st', .error .invalidCapability)
          | none => (st', .ok ({ results := #[] }, sgi))
        | none => (st', .ok ({ results := #[] }, sgi))

/-- WS-ZA ZA4.7: the compiled `endpointSendDualWithCapsOnCore`.  The receive
queue's head is read once, before the send, so the pre-state is not held across
the send's writes for a second read of the endpoint
(`ZERO_ALLOCATION_SYSCALL_PLAN.md` D1). -/
@[inline] def endpointSendDualWithCapsOnCoreImpl
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (CapTransferSummary × Option (CoreId × SgiKind)) :=
  let receiverHead? := match st.getEndpoint? endpointId with
    | some ep => ep.receiveQ.head
    | none => none
  -- A message already stamped with the grant bit is sent as it is.
  let stamped := if msg.capsGranted == endpointRights.mem .grant then msg
    else { msg with capsGranted := endpointRights.mem .grant }
  match endpointSendDualOnCore endpointId sender stamped executingCore st with
  | (st', .error e) => (st', .error e)
  | (st', .ok sgi) =>
      if !receiverHead?.isSome || msg.caps.isEmpty then (st', .ok ({ results := #[] }, sgi))
      else
        match receiverHead? with
        | some receiverId =>
            match lookupCspaceRoot st' receiverId with
            | some recvRoot =>
              match ipcUnwrapCaps { msg with capsGranted := endpointRights.mem .grant } recvRoot
                  receiverSlotBase (endpointRights.mem .grant) st' with
              | .error e => (st', .error e)
              | .ok (summary, st'') => (st'', .ok (summary, sgi))
            | none => (st', .error .invalidCapability)
        | none => (st', .ok ({ results := #[] }, sgi))

@[csimp] theorem endpointSendDualWithCapsOnCore_eq_impl :
    @endpointSendDualWithCapsOnCore = @endpointSendDualWithCapsOnCoreImpl := by
  funext endpointId sender msg endpointRights receiverSlotBase executingCore st
  have hStamp : (if msg.capsGranted == endpointRights.mem .grant then msg
      else { msg with capsGranted := endpointRights.mem .grant }) =
      { msg with capsGranted := endpointRights.mem .grant } := by
    split
    · next h => cases msg; simp only [beq_iff_eq] at h; subst h; rfl
    · rfl
  unfold endpointSendDualWithCapsOnCore endpointSendDualWithCapsOnCoreImpl
  rw [hStamp]
  cases st.getEndpoint? endpointId <;> rfl

/-- WS-SM SM6: with no capabilities to transfer, the WithCaps cross-core send is
exactly the bare cross-core send (empty transfer summary), so its surfaced SGI is
the bare send's. -/
theorem endpointSendDualWithCapsOnCore_no_caps
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hCaps : msg.caps.isEmpty = true) :
    endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
        receiverSlotBase executingCore st
      = ((endpointSendDualOnCore endpointId sender { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1,
         (endpointSendDualOnCore endpointId sender { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).2.map
           (fun sgi => ({ results := #[] }, sgi))) := by
  -- PR #873 round 13: against the **stamped** message, because that is what the
  -- wrapper transmits. With no capabilities the grant bit changes no behaviour,
  -- but it is part of the message the send parks.
  unfold endpointSendDualWithCapsOnCore
  cases h : endpointSendDualOnCore endpointId sender { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st with
  | mk st' res => cases res with
    | error e => simp [Except.map]
    | ok sgi => simp [hCaps, Except.map]

-- ============================================================================
-- §3 Information-flow-checked cross-core send (the live checked `.send`)
-- ============================================================================

/-- WS-SM SM6 (live `.send` enforcement): the **information-flow-checked**
cross-core send — the cross-core analogue of `endpointSendDualChecked`. Mirrors
the single-core checked `.send` arm exactly: message bounds first (so a bounds
fault is not masked by the flow gate, WS-H12d/A-09), then the SM-IF guard
`securityFlowsTo senderLabel endpointLabel` rejecting with `.flowDenied`, then the
cross-core WithCaps send. This is the operation the live `dispatchWithCapChecked`
`.send` arm routes through, replacing the boot-pinned `endpointSendDualChecked`. -/
def endpointSendCrossCoreDispatchChecked
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (CapTransferSummary × Option (CoreId × SgiKind)) :=
  if msg.registers.size > maxMessageRegisters then (st, .error .ipcMessageTooLarge)
  else if msg.caps.size > maxExtraCaps then (st, .error .ipcMessageTooManyCaps)
  -- WS-SM SM8.C: global lattice check AND this endpoint's configured override.
  else if endpointFlowGate ctx endpointId (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) then
    endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
      receiverSlotBase executingCore st
  else
    (st, .error .flowDenied)

/-- WS-SM SM6: a disallowed flow is rejected before any state change — the checked
cross-core send is fail-closed (state unchanged, `.flowDenied`). -/
theorem endpointSendCrossCoreDispatchChecked_flow_denied
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState)
    (hTooLarge : ¬ (msg.registers.size > maxMessageRegisters))
    (hTooMany : ¬ (msg.caps.size > maxExtraCaps))
    (hDeny : securityFlowsTo (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) = false) :
    endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
        receiverSlotBase executingCore st = (st, .error .flowDenied) := by
  -- WS-SM SM8.C: a denied global flow denies the gate whatever the override says.
  simp [endpointSendCrossCoreDispatchChecked, hTooLarge, hTooMany,
    endpointFlowGate_false_of_securityFlowsTo_false ctx endpointId _ _ hDeny]

/-- WS-SM SM6: when the flow is permitted (and the message is within bounds, which
the unchecked path re-checks itself), the checked cross-core send is exactly the
unchecked cross-core WithCaps send — the guard is a pure precondition. -/
theorem endpointSendCrossCoreDispatchChecked_flow_allowed
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState)
    (hTooLarge : ¬ (msg.registers.size > maxMessageRegisters))
    (hTooMany : ¬ (msg.caps.size > maxExtraCaps))
    (hAllow : securityFlowsTo (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) = true)
    -- WS-SM SM8.C: the endpoint's override must admit the flow too.
    (hOverride : endpointOverrideAllows ctx endpointId (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) = true) :
    endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
        receiverSlotBase executingCore st
      = endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
          receiverSlotBase executingCore st := by
  simp [endpointSendCrossCoreDispatchChecked, hTooLarge, hTooMany,
    endpointFlowGate_of ctx endpointId _ _ hAllow hOverride]

/-- WS-ZA ZA4.7: the cross-core send answers a refusal with the state it was
handed: every refusal precedes its first write or returns the pre-state. -/
theorem endpointSendDualOnCore_error_state (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (e : KernelError)
    (h : (endpointSendDualOnCore endpointId sender msg executingCore st).2 = .error e) :
    (endpointSendDualOnCore endpointId sender msg executingCore st).1 = st := by
  unfold endpointSendDualOnCore at h ⊢
  repeat' split at h <;> (try simp only [] at h ⊢) <;> (try split) <;> (try rfl) <;>
    (try simp_all)

/-- WS-ZA ZA4.7: with no capabilities to transfer, the checked cross-core send
answers a refusal with the state it was handed. -/
theorem endpointSendCrossCoreDispatchChecked_error_state
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (e : KernelError) (hCaps : msg.caps.isEmpty = true)
    (h : (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
      receiverSlotBase executingCore st).2 = .error e) :
    (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
      receiverSlotBase executingCore st).1 = st := by
  unfold endpointSendCrossCoreDispatchChecked at h ⊢
  split
  · rfl
  · split
    · rfl
    · split
      · next hG =>
        rw [if_neg (by assumption), if_neg (by assumption), if_pos hG] at h
        rw [endpointSendDualWithCapsOnCore_no_caps _ _ _ _ _ _ _ hCaps] at h ⊢
        simp only at h ⊢
        apply endpointSendDualOnCore_error_state _ _ _ _ _ e
        revert h
        cases endpointSendDualOnCore endpointId sender
          { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st with
        | mk s r => cases r <;> simp [Except.map]
      · rfl

/-- **WS-RR RR8.12 (frame)**: a cross-core send touches **no** core's replenish
queue.

The obligation the scheduler-domain footprint below owes for declaring an *empty*
replenish segment.  Both paths compose steps that frame the whole scheduler (the
endpoint pop or enqueue, the receiver's or sender's TCB store) with one that
writes a run queue alone (the rendezvous' `wakeThread`, the block's
`removeRunnableOnCore`).  A plain send carries no scheduling context — only
`.call` donates — so there is nothing in the replenishment domain for it to
move. -/
theorem endpointSendDualOnCore_replenishQueueOnCore (epId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (ec : CoreId) (st : SystemState)
    (c : CoreId) :
    (endpointSendDualOnCore epId sender msg ec st).1.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold endpointSendDualOnCore
  split
  · rfl
  · split
    · rfl
    · cases hEp : st.getEndpoint? epId with
      | none => simp only []; split <;> rfl
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none =>
          simp only []
          cases hEnq : endpointQueueEnqueue epId false sender st with
          | error e => rfl
          | ok st1 =>
            simp only []
            cases hIpc : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend epId) (some msg) with
            | error e => rfl
            | ok st2 =>
              simp only []
              rw [removeRunnableOnCore_replenishQueueOnCore,
                storeTcbIpcStateAndMessage_scheduler_eq st1 st2 _ _ _ hIpc,
                endpointQueueEnqueue_scheduler_eq epId false sender st st1 hEnq]
        | some _ =>
          simp only []
          cases hSnd : st.getTcb? sender with
          | none => rfl
          | some _ =>
            simp only []
            cases hPop : endpointQueuePopHead epId true st with
            | error e => rfl
            | ok triple =>
              obtain ⟨receiver, headTcb, st1⟩ := triple
              simp only []
              cases hRecv : storeTcbReceiveComplete st1 receiver (some msg) with
              | error e => rfl
              | ok st2 =>
                simp only []
                rw [wakeThread_replenishQueueOnCore,
                  storeTcbReceiveComplete_scheduler_eq st1 st2 _ _ hRecv,
                  endpointQueuePopHead_scheduler_eq epId true st st1 receiver hPop]

/-- **WS-RR RR8.12 (frame)**: and neither does the caps-carrying form — the
capability transfer writes CNodes and the CDT, never the scheduler
(`ipcUnwrapCaps_preserves_scheduler`). -/
theorem endpointSendDualWithCapsOnCore_replenishQueueOnCore (epId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (rights : AccessRightSet)
    (slotBase : SeLe4n.Slot) (ec : CoreId) (st st' : SystemState) (c : CoreId)
    (h : (endpointSendDualWithCapsOnCore epId sender msg rights slotBase ec st).1 = st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  subst h
  unfold endpointSendDualWithCapsOnCore
  have hBare := endpointSendDualOnCore_replenishQueueOnCore epId sender
    { msg with capsGranted := rights.mem .grant } ec st c
  cases hSend : endpointSendDualOnCore epId sender
      { msg with capsGranted := rights.mem .grant } ec st with
  | mk st1 res =>
    rw [hSend] at hBare
    cases res with
    | error e => simpa using hBare
    | ok sgi =>
      simp only []
      repeat' split
      all_goals
        first
          | exact hBare
          | (rename_i hUnwrap
             rw [ipcUnwrapCaps_preserves_scheduler _ _ _ _ _ _ _ hUnwrap]
             exact hBare)

/-- **WS-RR RR8.12 (frame)**: and neither does the **live** `.send` arm.  Its
three gates each return the pre-state; past them it *is* the caps-carrying
form. -/
theorem endpointSendCrossCoreDispatchChecked_replenishQueueOnCore (ctx : LabelingContext)
    (epId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (rights : AccessRightSet) (slotBase : SeLe4n.Slot) (ec : CoreId)
    (st st' : SystemState) (c : CoreId)
    (h : (endpointSendCrossCoreDispatchChecked ctx epId sender msg rights slotBase ec st).1
      = st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  subst h
  unfold endpointSendCrossCoreDispatchChecked
  split
  · rfl
  · split
    · rfl
    · split
      · exact endpointSendDualWithCapsOnCore_replenishQueueOnCore epId sender msg rights
          slotBase ec st _ c rfl
      · rfl

/-- WS-SM SM8.B.2, relocated to production at **WS-RR RR8.12**: **the cores a
cross-core send may write.**  Exactly one, on either path:

* **rendezvous** — a receiver is parked, so it is woken on *its* home core and the
  executing core is untouched;
* **block** — nobody is waiting, so the sender is descheduled on the **executing**
  core and no other core moves.

The receiver is resolved from the pre-state through SM6.A's own
`endpointCallReceiver?` — the receive-queue head, which is the same rendezvous
partner a `.call` would take, so send and call name it once rather than twice.

Relocated for the reason `notificationSignalWriteSet`'s docstring gives: the
scheduler-domain footprint below is production and
`InformationFlow/NonInterferenceCrossCore.lean`, where this was declared, is
staged and imports `Kernel.API`. -/
def endpointSendWriteSet (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) : List CoreId :=
  match endpointCallReceiver? st endpointId with
  | some receiver => [determineTargetCore st receiver]
  | none => [executingCore]

/-- **WS-RR RR8.12**: the scheduler-domain footprint of the live `.send` arm — the
object-store table write lock and the run-queue write lock of the one core the
send moves.

Defined over `endpointSendWriteSet`, so this footprint and
`endpointSendCrossCoreDispatchChecked_confinedToCores` read one core list rather
than two that have to be kept in step.  No replenish segment: a plain send
carries no scheduling context (only `.call` donates), so `.send` writes no
replenish queue on any path. -/
def schedLockSet_endpointSendOnCore (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) : List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (endpointSendWriteSet st endpointId executingCore) []

/-- **WS-LS LS2.3**: the write set reads the object store alone — the endpoint's
receive queue and the receiver's home core — so two states with the same store
give the same core list.  What lets the footprint be resolved before the arm's
extra-capability resolution mints its derivation nodes (which writes the store's
CDT but neither the endpoint nor any TCB). -/
theorem endpointSendWriteSet_congr_objects {st st' : SystemState}
    (h : st'.objects = st.objects) (endpointId : SeLe4n.ObjId) (executingCore : CoreId) :
    endpointSendWriteSet st' endpointId executingCore
      = endpointSendWriteSet st endpointId executingCore := by
  unfold endpointSendWriteSet endpointCallReceiver?
  rw [SystemState.getEndpoint?_frame h]
  cases st.getEndpoint? endpointId with
  | none => rfl
  | some ep =>
    simp only
    cases ep.receiveQ.head with
    | none => rfl
    | some receiver =>
      simp only
      rw [determineTargetCore_congr st st' receiver (by rw [SystemState.getTcb?_frame h])]

theorem schedLockSet_endpointSendOnCore_congr_objects {st st' : SystemState}
    (h : st'.objects = st.objects) (endpointId : SeLe4n.ObjId) (executingCore : CoreId) :
    schedLockSet_endpointSendOnCore st' endpointId executingCore
      = schedLockSet_endpointSendOnCore st endpointId executingCore := by
  unfold schedLockSet_endpointSendOnCore
  rw [endpointSendWriteSet_congr_objects h]

/-- **WS-RR RR8.12**: on the rendezvous path the footprint names the woken
receiver's home core. -/
theorem schedLockSet_endpointSendOnCore_contains_receiver_runQueue_write (st : SystemState)
    (endpointId : SeLe4n.ObjId) (executingCore : CoreId) (receiver : SeLe4n.ThreadId)
    (hRecv : endpointCallReceiver? st endpointId = some receiver) :
    (LockKey.runQueue (determineTargetCore st receiver), Concurrency.AccessMode.write)
      ∈ schedLockSet_endpointSendOnCore st endpointId executingCore := by
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  unfold endpointSendWriteSet
  rw [hRecv]
  simp

/-- **WS-RR RR8.12**: and on the block path it names the executing core's, which
the sender's own deschedule writes.  The two arms are exclusive — a send that
rendezvouses does not block — so the footprint is one run-queue member either
way. -/
theorem schedLockSet_endpointSendOnCore_contains_executing_runQueue_write (st : SystemState)
    (endpointId : SeLe4n.ObjId) (executingCore : CoreId)
    (hRecv : endpointCallReceiver? st endpointId = none) :
    (LockKey.runQueue executingCore, Concurrency.AccessMode.write)
      ∈ schedLockSet_endpointSendOnCore st endpointId executingCore := by
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  unfold endpointSendWriteSet
  rw [hRecv]
  simp

end SeLe4n.Kernel
