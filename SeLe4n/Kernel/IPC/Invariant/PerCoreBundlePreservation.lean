-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundle
import SeLe4n.Kernel.Scheduler.Operations.Selection
import SeLe4n.Kernel.IPC.CrossCore.EndpointCall
import SeLe4n.Kernel.IPC.Invariant.DonationPreservation

/-!
# WS-SM SM6.D.2 — Per-operation preservation of the per-core IPC bundle

This module is the preservation layer of SM6.D (plan
WS-SM SM6 §3.3, Theorem 3.3.1): each of
the six IPC operations — send, receive, call, reply (+ the combined
reply-receive), signal, wait — preserves every core's view of the IPC
invariant bundle (`ipcInvariantFull_perCore`, SM6.D.1).

## Proof architecture

Every conjunct of the bundle reads only the object store (`v0.36.136`
retired `passiveServerIdle`, the one that read the scheduler), so each
per-core theorem is *derived* from the existing single-core whole-bundle
theorem (`…_preserves_ipcInvariantFull`,
`Structural/DualQueueMembership.lean`) through the SM6.D.1 exact-
decomposition bridges — precisely the plan's "the existing single-core
proof carries through" (§3.3), with zero proof duplication and zero
weakening.  **No idle-core assumption is used anywhere** — unlike the
SM4.D-era `…_smp_of_singleCore_and_idle` lifters, these theorems hold
on a state where all four cores are actively scheduling.

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §0 Home-core / wake-target coherence
-- ============================================================================

/-- WS-SM SM6.D: the per-core bundle's thread-domain restriction
(`threadHomeCore`, SM6.D.1) coincides with the operational cross-core
wake target (`determineTargetCore`, SM5.C) on every live thread — the
invariant slices partition threads by exactly the core the wake path
delivers them to. -/
theorem determineTargetCore_eq_threadHomeCore {st : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB}
    (hTcb : st.getTcb? tid = some tcb) :
    determineTargetCore st tid = threadHomeCore tcb := by
  unfold determineTargetCore threadHomeCore
  rw [hTcb]
  cases h : tcb.cpuAffinity <;> simp [h, Option.getD]

-- ============================================================================
-- §1 SM6.D.2: per-operation preservation of the per-core IPC bundle
-- ============================================================================
--
-- Theorem 3.3.1 of the plan, one theorem per IPC operation: from the
-- ∀-core pre-state bundle (`ipcInvariantFull_smp`), the operation's
-- post-state satisfies EVERY core's bundle view: the bundle rides the
-- existing single-core whole-bundle theorem through the SM6.D.1
-- exact-decomposition bridges. Hypotheses mirror the single-core
-- theorems' (freshness, readiness, binding side conditions, and -- since
-- WS-RR RR3 -- the *pre*-state conditions that replaced the threaded
-- post-state facts `hWtpmn'`/`hRCLRecip'`/`hDOV'`/`hDualQueue'`/`hBadge'`),
-- with TCB lookups routed through the typed `getTcb?`.

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (signal): `notificationSignal` preserves every core's view of
the IPC invariant bundle. -/
theorem notificationSignal_preserves_ipcInvariantFull_perCore
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (notificationSignal_preserves_ipcInvariantFull st st' notificationId badge
      (ipcInvariantFull_of_smp hInv) hObjInv hNWC hAllBudgetsNone hStep)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (wait): `notificationWait` preserves every core's view of the
IPC invariant bundle. -/
theorem notificationWait_preserves_ipcInvariantFull_perCore
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWaiterNotRecv : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hWaiterNotReply : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hWaiterReady : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        tcb.ipcState = .ready)
    (hStep : notificationWait notificationId waiter st = .ok (result, st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (notificationWait_preserves_ipcInvariantFull st st' notificationId waiter result
      (ipcInvariantFull_of_smp hInv) hObjInv hWaiterNotRecv
      (fun tcb hRaw => hWaiterNotReply tcb ((getTcb?_eq_some_iff st waiter tcb).mpr hRaw))
      hAllBudgetsNone
      (fun tcb hRaw => hWaiterReady tcb ((getTcb?_eq_some_iff st waiter tcb).mpr hRaw))
      hStep)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (send): `endpointSendDual` preserves every core's view of the
IPC invariant bundle. -/
theorem endpointSendDual_preserves_ipcInvariantFull_perCore
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hSenderNotRecv : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hSenderNotReply : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hSenderNotUnbound : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        tcb.schedContextBinding ≠ .unbound)
    (hStep : endpointSendDual endpointId sender payload st = .ok ((), st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointSendDual_preserves_ipcInvariantFull st st' endpointId sender payload
      (ipcInvariantFull_of_smp hInv) hObjInv hAllBudgetsNone
      hFreshSender hSendTailFresh hSenderNotRecv
      (fun tcb hRaw => hSenderNotReply tcb ((getTcb?_eq_some_iff st sender tcb).mpr hRaw))
      (fun tcb hRaw => hSenderNotUnbound tcb ((getTcb?_eq_some_iff st sender tcb).mpr hRaw))
      hStep)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (receive): `endpointReceiveDual` preserves every core's view
of the IPC invariant bundle. -/
theorem endpointReceiveDual_preserves_ipcInvariantFull_perCore
    (endpointId : SeLe4n.ObjId) (receiver senderId : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (st st' : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    -- **WS-OD OD4.4**: the pre-receive cleanup's pop resolves its new owner from
    -- the reply stack; this is the obligation that resolution carries.
    (hStackValid : cleanupDonationStackValid st receiver)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready)
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointReceiveDual_preserves_ipcInvariantFull endpointId receiver senderId replyId st st'
      (ipcInvariantFull_of_smp hInv) hObjInv hStackValid hAllBudgetsNone
      hFreshReceiver hRecvTailFresh hReplyIdValid hReceiverNotRecv
      (fun tcb hRaw => hReceiverReady tcb ((getTcb?_eq_some_iff st receiver tcb).mpr hRaw))
      hStep)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (call): `endpointCall` preserves every core's view of the IPC
invariant bundle. -/
theorem endpointCall_preserves_ipcInvariantFull_perCore
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hCallerNotReply : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hCallerNotUnbound : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        tcb.schedContextBinding ≠ .unbound)
    (hCallerReady : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        tcb.ipcState = .ready)
    (hStep : endpointCall endpointId caller payload st = .ok ((), st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointCall_preserves_ipcInvariantFull st st' endpointId caller payload
      (ipcInvariantFull_of_smp hInv) hObjInv hAllBudgetsNone
      hFreshCaller hSendTailFresh hCallerNotRecv
      (fun tcb hRaw => hCallerNotReply tcb ((getTcb?_eq_some_iff st caller tcb).mpr hRaw))
      (fun tcb hRaw => hCallerNotUnbound tcb ((getTcb?_eq_some_iff st caller tcb).mpr hRaw))
      (fun tcb hRaw => hCallerReady tcb ((getTcb?_eq_some_iff st caller tcb).mpr hRaw))
      hStep)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (reply): `endpointReply` preserves every core's view of the
IPC invariant bundle. -/
theorem endpointReply_preserves_ipcInvariantFull_perCore
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    -- WS-RR RR3.12: replaces the threaded post-state `hDOV'`, which no state on the
    -- donating path satisfies. A pre-state condition, hence dischargeable.
    (hNoDonationOwnedBy : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
      (scId : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .donated scId target)
    (hStep : endpointReply replier target msg st = .ok ((), st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointReply_preserves_ipcInvariantFull st st' replier target msg
      (ipcInvariantFull_of_smp hInv) hObjInv hAllBudgetsNone hNoDonationOwnedBy hStep)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (reply-receive): `endpointReplyRecv` preserves every core's
view of the IPC invariant bundle. -/
theorem endpointReplyRecv_preserves_ipcInvariantFull_perCore
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    -- **WS-OD OD4.4**: see `endpointReplyRecv_preserves_ipcInvariantFull` — the
    -- obligation is keyed on the reply leg's own post-state, not quantified over
    -- every `SystemState`.
    (hStackValid : ∀ s : SystemState,
      endpointReply receiver replyTarget msg st = .ok ((), s) →
      cleanupDonationStackValid s receiver)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    -- WS-RR RR3.12: replaces the threaded post-state `hDOV'`, which no state on the
    -- donating path satisfies. A pre-state condition, hence dischargeable.
    (hNoDonationOwnedBy : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
      (scId : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .donated scId replyTarget)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointReplyRecv_preserves_ipcInvariantFull st st' endpointId receiver replyTarget msg replyId
      (ipcInvariantFull_of_smp hInv) hObjInv hStackValid hAllBudgetsNone hNoDonationOwnedBy
      hFreshReceiver hRecvTailFresh hReplyIdValid hReceiverNotRecv
      (fun tcb hRaw => hReceiverReady tcb ((getTcb?_eq_some_iff st receiver tcb).mpr hRaw))
      hStep)

-- ============================================================================
-- §2 SM6.D.2: the WithCaps trio — per-core bundle
-- ============================================================================
--
-- The live `.send` dispatch routes through `endpointSendDualWithCaps` (and
-- the capability-carrying receive/call variants exist on the same footing),
-- so the per-core bundle layer must cover the WithCaps compositions too:
-- base transition + `lookupCspaceRoot` + `ipcUnwrapCaps`. The per-core
-- bundle theorems ride the single-core WithCaps whole-bundle theorems
-- through the SM6.D.1 bridges.

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (send, capability-carrying): `endpointSendDualWithCaps` — the
transition behind the **live** `.send` dispatch — preserves every core's
view of the IPC invariant bundle. -/
theorem endpointSendDualWithCaps_preserves_ipcInvariantFull_perCore
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (payload : SendPayload)
    (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hSenderNotRecv : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hSenderNotReply : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hSenderNotUnbound : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        tcb.schedContextBinding ≠ .unbound)
    (hStep : endpointSendDualWithCaps endpointId sender payload
             receiverSlotBase st = .ok (summary, st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointSendDualWithCaps_preserves_ipcInvariantFull endpointId sender payload
      receiverSlotBase st st' summary (ipcInvariantFull_of_smp hInv) hObjInv
      hAllBudgetsNone hFreshSender hSendTailFresh
      hSenderNotRecv
      (fun tcb hRaw => hSenderNotReply tcb ((getTcb?_eq_some_iff st sender tcb).mpr hRaw))
      (fun tcb hRaw => hSenderNotUnbound tcb ((getTcb?_eq_some_iff st sender tcb).mpr hRaw))
      hStep)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (receive, capability-carrying): `endpointReceiveDualWithCaps`
preserves every core's view of the IPC invariant bundle. -/
theorem endpointReceiveDualWithCaps_preserves_ipcInvariantFull_perCore
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    -- **WS-OD OD4.4**: see `endpointReceiveDualWithCaps_preserves_ipcInvariantFull`.
    (hStackValid : cleanupDonationStackValid st receiver)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready)
    (hStep : endpointReceiveDualWithCaps endpointId receiver replyId
             receiverCspaceRoot receiverSlotBase st = .ok ((senderId, summary), st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointReceiveDualWithCaps_preserves_ipcInvariantFull endpointId receiver replyId receiverCspaceRoot receiverSlotBase st st' senderId summary
      (ipcInvariantFull_of_smp hInv) hObjInv hStackValid hAllBudgetsNone
      hFreshReceiver hRecvTailFresh hReplyIdValid hReceiverNotRecv
      (fun tcb hRaw => hReceiverReady tcb ((getTcb?_eq_some_iff st receiver tcb).mpr hRaw))
      hStep)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (call, capability-carrying): `endpointCallWithCaps` preserves
every core's view of the IPC invariant bundle. -/
theorem endpointCallWithCaps_preserves_ipcInvariantFull_perCore
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (payload : SendPayload)
    (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hCallerNotReply : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hCallerNotUnbound : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        tcb.schedContextBinding ≠ .unbound)
    (hCallerReady : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        tcb.ipcState = .ready)
    (hStep : endpointCallWithCaps endpointId caller payload
             receiverSlotBase st = .ok (summary, st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointCallWithCaps_preserves_ipcInvariantFull endpointId caller payload
      receiverSlotBase st st' summary (ipcInvariantFull_of_smp hInv) hObjInv
      hAllBudgetsNone hFreshCaller hSendTailFresh
      hCallerNotRecv
      (fun tcb hRaw => hCallerNotReply tcb ((getTcb?_eq_some_iff st caller tcb).mpr hRaw))
      (fun tcb hRaw => hCallerNotUnbound tcb ((getTcb?_eq_some_iff st caller tcb).mpr hRaw))
      (fun tcb hRaw => hCallerReady tcb ((getTcb?_eq_some_iff st caller tcb).mpr hRaw))
      hStep)

end SeLe4n.Kernel
