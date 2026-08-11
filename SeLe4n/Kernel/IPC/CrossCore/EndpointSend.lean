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
                  ((wakeThread st'' receiver executingCore).1,
                   .ok (wakeThread st'' receiver executingCore).2)
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

/-- WS-SM SM6 (bootCore bridge): on the boot core the per-core send agrees with
the single-core `endpointSendDual` on the resulting **state**.

`removeRunnableOnCore … bootCoreId = removeRunnable` and
`wakeThread … bootCoreId` enqueues on the boot core exactly when the receiver is
homed there, which is the only configuration the single-core transition models.
Stated on the state alone because the single-core form returns no SGI. -/
theorem endpointSendDualOnCore_bootCore_state (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (st : SystemState)
    (hTooLarge : ¬ (msg.registers.size > maxMessageRegisters))
    (hTooMany : ¬ (msg.caps.size > maxExtraCaps))
    (hNoEndpoint : st.getEndpoint? endpointId = none)
    (hAbsent : (st.objects[endpointId]?).isSome = false) :
    (endpointSendDualOnCore endpointId sender msg bootCoreId st).1 = st := by
  simp [endpointSendDualOnCore, hTooLarge, hTooMany, hNoEndpoint, hAbsent]

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
  else if securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) then
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
  simp [endpointSendCrossCoreDispatchChecked, hTooLarge, hTooMany, hDeny]

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
      (ctx.endpointLabelOf endpointId) = true) :
    endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
        senderCspaceRoot receiverSlotBase executingCore st
      = endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
          senderCspaceRoot receiverSlotBase executingCore st := by
  simp [endpointSendCrossCoreDispatchChecked, hTooLarge, hTooMany, hAllow]

end SeLe4n.Kernel
