-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6: PRODUCTION.  The cross-core `Send` transition.  Enters the
-- production import closure through the live `.send` dispatch arm
-- (`API.dispatchWithCap{,Checked}` via `endpointSendDualWithCaps`).

import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch

/-!
# WS-SM SM6 — the cross-core `Send`

`endpointSendDual` (`IPC/DualQueue/Transport.lean`) is the single-core send.  It
has two scheduling effects, and **both were boot-pinned**:

* on a **rendezvous** it wakes the dequeued receiver with `ensureRunnable`,
  which enqueues on `bootCoreId` regardless of the receiver's `cpuAffinity`;
* on the **block** path it deschedules the sender with `removeRunnable`, which
  clears the boot core's slots regardless of where the sender is running.

PR #861 review round 10 found the live `.send` arm still routed there.  The
consequences on a multi-core system are the two halves of the same bug: a
receiver woken by a remote sender is placed on a run queue its own core never
dispatches from, and a sender that blocks on a secondary core **remains current
and runnable on that core** — it should have stopped, and instead keeps being a
candidate for dispatch.

`endpointSendDualOnCore` is the per-core form, built exactly like its SM6.A/SM6.C
siblings (`endpointCallOnCore`, `endpointReceiveDualOnCore`): the receiver is
woken on **its own home core** via the SM5.C `wakeThread`, which returns the
`.reschedule` SGI that core must receive, and the sender is descheduled on the
**executing** core via `removeRunnableOnCore`.  Every non-scheduling step is
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
          match endpointQueuePopHead endpointId true st with
          | .error e => (st, .error e)
          | .ok (receiver, _tcb, st') =>
              match storeTcbReceiveComplete st' receiver (some msg) with
              | .error e => (st, .error e)
              | .ok st'' =>
                  -- Cross-core receiver wake (SM5.C): route to the receiver's
                  -- HOME core, not the boot core.
                  --
                  -- Bound once.  Projecting `.1` and `.2` out of two separate
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
      -- Typed-accessor dispatch (AK7 cascade discipline), exactly as
      -- `endpointReceiveDualOnCore`: `getEndpoint?` is `none` both for an absent
      -- object and for a wrong-kinded one, so recover the single-core error
      -- distinction without a raw object-store variant match.
      if (st.objects[endpointId]?).isSome then (st, .error .invalidCapability)
      else (st, .error .objectNotFound)

/-- WS-SM SM6: the absent-endpoint arm is fail-closed — the pre-state is
returned untouched.

This used to be called `…_bootCore_state` and to claim, in its docstring, that
"the per-core send agrees with the single-core `endpointSendDual` on the
resulting state".  It proved no such thing: `hNoEndpoint` and `hAbsent` together
pin it to the `.objectNotFound` arm, where the transition trivially returns the
pre-state, and the statement never mentioned `endpointSendDual` at all
(PR #861 review round 15).  The real bridges are the two theorems below, one per
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

/-- WS-SM SM6 (**the duplication guard**): the IPC-local
`ipcEffectiveRunQueuePriority` computes the scheduler's
`effectiveRunQueuePriority`.

`Endpoint.lean` carries its own copy of the PIP-effective priority because
importing `Scheduler.Invariant` from there would close an import cycle, and its
docstring says the two agree.  Until now nothing checked that: two independent
definitions agreeing by convention is exactly the case this project requires be
enforced structurally.  This is the first module that sees both names, so this
is the first place the claim can be *stated* — and with it stated, a change to
either body that the other does not mirror stops the build rather than silently
re-bucketing every wake.

`rfl`, today; the point is that it is a compile-time obligation, not that it is
hard. -/
theorem ipcEffectiveRunQueuePriority_eq_effectiveRunQueuePriority (tcb : TCB) :
    ipcEffectiveRunQueuePriority tcb
      = SeLe4n.Kernel.effectiveRunQueuePriority tcb := rfl

/-- WS-SM SM6 (**the wake bridge**): on the boot core, the per-core wake commits
exactly what the single-core `ensureRunnable` commits.

The two are *not* the same function, which is why this needs stating rather than
asserting.  `enqueueRunnableOnCore` guards on `runnableOnSomeCore` (all cores)
where `ensureRunnable` guards on boot-core membership, and it additionally writes
the object store, marking the woken thread `.ready`.  Each difference is
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
    (hNotElsewhere : ∀ c : CoreId, c ≠ bootCoreId →
      ¬ (st.scheduler.runQueueOnCore c).contains tid)
    (hReady : tcb.ipcState = .ready)
    (hNoResize : ¬ (st.objects.size * 4 ≥ st.objects.capacity * 3)) :
    (wakeThread st tid bootCoreId).1 = ensureRunnable st tid := by
  unfold wakeThread enqueueRunnableOnCore ensureRunnable
  simp only [hHome, hTcb]
  -- `runnableOnSomeCore` collapses onto the boot-core membership test.
  have hSome : runnableOnSomeCore st tid
      = (st.scheduler.runQueueOnCore bootCoreId).contains tid := by
    unfold runnableOnSomeCore
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨c, -, hc⟩
      by_cases hcb : c = bootCoreId
      · exact hcb ▸ hc
      · exact absurd hc (by simpa using hNotElsewhere c hcb)
    · intro h
      exact ⟨bootCoreId, SeLe4n.Kernel.Concurrency.mem_allCores _, h⟩
  -- `hReady` makes the wake's object write a re-store of the value already
  -- present: structure eta collapses the update to the TCB itself.
  have hEta : ({ tcb with ipcState := (.ready : ThreadIpcState) } : TCB) = tcb := by
    rw [← hReady]
  have hObj : st.objects.insert tid.toObjId (.tcb { tcb with ipcState := .ready })
      = st.objects := by
    refine SeLe4n.Kernel.RobinHood.RHTable.insert_eq_self_of_get? _ _ _ hNoResize ?_
    have hRaw := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
    rw [RHTable_getElem?_eq_get?] at hRaw
    rw [hEta]
    exact hRaw
  by_cases hMem : (st.scheduler.runQueueOnCore bootCoreId).contains tid = true
  · simp [hSome, hMem, RunQueue.mem_iff_contains]
  · simp [hSome, hMem, RunQueue.mem_iff_contains, hObj,
      ipcEffectiveRunQueuePriority_eq_effectiveRunQueuePriority]

/-- WS-SM SM6 (**the blocking leg's bootCore bridge**): with no receiver waiting,
the per-core send on the boot core commits **exactly** the single-core
`endpointSendDual`'s state.

Unconditional on this path, and the reason is one `rfl`: the two transitions run
the same enqueue and the same TCB store, and differ only in the final
deschedule — `removeRunnableOnCore … bootCoreId` *is* `removeRunnable`
(`removeRunnableOnCore_bootCoreId`).  This is the refinement claim the old
`…_bootCore_state` docstring wanted and did not make. -/
theorem endpointSendDualOnCore_bootCore_block_eq_single (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (st st' : SystemState) (ep : Endpoint)
    (hEp : st.getEndpoint? endpointId = some ep)
    (hNoReceiver : ep.receiveQ.head = none)
    (hSingle : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    (endpointSendDualOnCore endpointId sender msg bootCoreId st).1 = st' := by
  -- The bounds guards are derived, not required: a successful single-core send
  -- already refutes them, so making the caller re-supply them would be
  -- redundant.  Both sides then reduce past the same two `if`s.
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
  unfold endpointSendDual at hSingle
  simp only [hRegs, hCaps, hRaw, hEp, hNoReceiver, if_false] at hSingle ⊢
  repeat' split at hSingle
  all_goals simp_all [removeRunnableOnCore_bootCoreId]

/-- WS-SM SM6 (**the rendezvous leg's bootCore bridge**): with a receiver
waiting whose home is the boot core, the per-core send on the boot core commits
**exactly** the single-core `endpointSendDual`'s state.

This is the leg that needed real work.  The two transitions run the same pop and
the same receive-complete store, and then diverge: the single-core one calls
`ensureRunnable`, the per-core one calls `wakeThread`, and those are genuinely
different functions.  `wakeThread_bootCore_eq_ensureRunnable` is what closes the
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
    (hNotElsewhere : ∀ c : CoreId, c ≠ bootCoreId →
      ¬ (stRecv.scheduler.runQueueOnCore c).contains receiver)
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
  unfold endpointSendDual at hSingle
  simp only [hRegs, hCaps, hRaw, hEp, hReceiver, hPop, hStore, if_false] at hSingle ⊢
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
-- §2  Cross-core `endpointSendDualWithCaps`
-- ============================================================================

/-- WS-SM SM6 (operation): endpoint send with capability transfer, across cores.

The exact shape of its SM6.A sibling `endpointCallWithCapsOnCore`: the cross-core
`endpointSendDualOnCore` rendezvous (which surfaces the receiver-wake SGI), then —
on an immediate rendezvous carrying caps — `ipcUnwrapCaps` installs the
transferred capabilities into the receiver's CSpace, gated on the endpoint's
`grant` right.  Returns the post-state, the capability-transfer summary, and the
optional cross-core SGI.

Capability-transfer behaviour is unchanged from `endpointSendDualWithCaps`,
including the AK1-I fail-closed `.invalidCapability` on a receiver with no CSpace
root (the NI-symmetry fix shared by all three transfer paths). -/
def endpointSendDualWithCapsOnCore
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (CapTransferSummary × Option (CoreId × SgiKind)) :=
  let hasReceiver := match st.getEndpoint? endpointId with
    | some ep => ep.receiveQ.head.isSome
    | none    => false
  match endpointSendDualOnCore endpointId sender msg executingCore st with
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
              match ipcUnwrapCaps msg senderCspaceRoot recvRoot receiverSlotBase
                  (endpointRights.mem .grant) st' with
              | .error e => (st', .error e)
              | .ok (summary, st'') => (st'', .ok (summary, sgi))
            | none => (st', .error .invalidCapability)
          | none => (st', .ok ({ results := #[] }, sgi))
        | none => (st', .ok ({ results := #[] }, sgi))

/-- WS-SM SM6: with no capabilities to transfer, the WithCaps cross-core send is
exactly the bare cross-core send (empty transfer summary), so its surfaced SGI is
the bare send's. -/
theorem endpointSendDualWithCapsOnCore_no_caps
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (senderCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hCaps : msg.caps.isEmpty = true) :
    endpointSendDualWithCapsOnCore endpointId sender msg endpointRights senderCspaceRoot
        receiverSlotBase executingCore st
      = ((endpointSendDualOnCore endpointId sender msg executingCore st).1,
         (endpointSendDualOnCore endpointId sender msg executingCore st).2.map
           (fun sgi => ({ results := #[] }, sgi))) := by
  unfold endpointSendDualWithCapsOnCore
  cases h : endpointSendDualOnCore endpointId sender msg executingCore st with
  | mk st' res => cases res with
    | error e => simp [Except.map]
    | ok sgi => simp [hCaps, Except.map]

-- ============================================================================
-- §3  Information-flow-checked cross-core send (the live checked `.send`)
-- ============================================================================

/-- WS-SM SM6 (live `.send` enforcement): the **information-flow-checked**
cross-core send — the cross-core analogue of `endpointSendDualChecked`.  Mirrors
the single-core checked `.send` arm exactly: message bounds first (so a bounds
fault is not masked by the flow gate, WS-H12d/A-09), then the SM-IF guard
`securityFlowsTo senderLabel endpointLabel` rejecting with `.flowDenied`, then the
cross-core WithCaps send.  This is the operation the live `dispatchWithCapChecked`
`.send` arm routes through, replacing the boot-pinned `endpointSendDualChecked`. -/
def endpointSendCrossCoreDispatchChecked
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (CapTransferSummary × Option (CoreId × SgiKind)) :=
  if msg.registers.size > maxMessageRegisters then (st, .error .ipcMessageTooLarge)
  else if msg.caps.size > maxExtraCaps then (st, .error .ipcMessageTooManyCaps)
  -- WS-SM SM8.C: global lattice check AND this endpoint's configured override.
  else if endpointFlowGate ctx endpointId (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) then
    endpointSendDualWithCapsOnCore endpointId sender msg endpointRights senderCspaceRoot
      receiverSlotBase executingCore st
  else
    (st, .error .flowDenied)

/-- WS-SM SM6: a disallowed flow is rejected before any state change — the checked
cross-core send is fail-closed (state unchanged, `.flowDenied`). -/
theorem endpointSendCrossCoreDispatchChecked_flow_denied
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState)
    (hTooLarge : ¬ (msg.registers.size > maxMessageRegisters))
    (hTooMany : ¬ (msg.caps.size > maxExtraCaps))
    (hDeny : securityFlowsTo (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) = false) :
    endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
        senderCspaceRoot receiverSlotBase executingCore st = (st, .error .flowDenied) := by
  -- WS-SM SM8.C: a denied global flow denies the gate whatever the override says.
  simp [endpointSendCrossCoreDispatchChecked, hTooLarge, hTooMany,
    endpointFlowGate_false_of_securityFlowsTo_false ctx endpointId _ _ hDeny]

/-- WS-SM SM6: when the flow is permitted (and the message is within bounds, which
the unchecked path re-checks itself), the checked cross-core send is exactly the
unchecked cross-core WithCaps send — the guard is a pure precondition. -/
theorem endpointSendCrossCoreDispatchChecked_flow_allowed
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState)
    (hTooLarge : ¬ (msg.registers.size > maxMessageRegisters))
    (hTooMany : ¬ (msg.caps.size > maxExtraCaps))
    (hAllow : securityFlowsTo (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) = true)
    -- WS-SM SM8.C: the endpoint's override must admit the flow too.
    (hOverride : endpointOverrideAllows ctx endpointId (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) = true) :
    endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
        senderCspaceRoot receiverSlotBase executingCore st
      = endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
          senderCspaceRoot receiverSlotBase executingCore st := by
  simp [endpointSendCrossCoreDispatchChecked, hTooLarge, hTooMany,
    endpointFlowGate_of ctx endpointId _ _ hAllow hOverride]

end SeLe4n.Kernel
