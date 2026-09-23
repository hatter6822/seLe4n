-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-RR RR4.17/RR4.18 — the fault-IPC `ipcInvariantFull`
-- surface. Staged because the delivery's bundle composes the staged
-- `EndpointCallInvariant` (the `.call` chain's cross-core bundle, whose own
-- staging note this inherits); the transitions it covers
-- (`SeLe4n/Kernel/IPC/{Operations,CrossCore}/Fault.lean`) are production, and
-- this module promotes with that surface.

import SeLe4n.Kernel.IPC.CrossCore.Fault
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallInvariant
import SeLe4n.Kernel.IPC.CrossCore.DispatchInvariant
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatchInvariant
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation

/-!
# WS-RR RR4.17/RR4.18 — the fault path preserves the IPC bundle

Fault delivery is an endpoint **Call** with a kernel-built message, and a
fault reply is an endpoint **Reply** followed by a register writeback. So
neither owes `ipcInvariantFull` a fresh proof: each is a composition of a
transition that already has one with TCB writes that touch **no field any
conjunct reads**.

That is the whole design argument for RR4.11's "reuse the Call machinery
rather than a parallel path", cashed out. Concretely, the fault path's own
writes are:

| write | fields touched | read by a conjunct? |
|---|---|---|
| `recordPendingFault` | `pendingFault` | no |
| `faultSuspend` / `faultSuspendOnCore` | `threadState`, run queue | no / frame |
| `faultAbandon` / `faultAbandonOnCore` | `threadState`, `pendingFault`, run queue | no / frame |
| `applyFaultRestart` | `registerContext`, `pendingFault` | no |

Every one of them therefore goes through the one-TCB-rewrite lever
(`insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull`), whose nine
field-agreement obligations all discharge by `rfl`. The run-queue removal is
handled by the same lever's passive-server frame, which reads the scheduler
only through `passiveServerIdleFrame`.
-/

namespace SeLe4n.Kernel

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1 The kernel's own fault-path writes
-- ============================================================================

/-- WS-RR RR4.17: recording the fault a thread is blocked on rewrites one
TCB's `pendingFault` — a field no conjunct reads — so the whole bundle
transports. -/
theorem recordPendingFault_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (tf : ThreadFault)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (recordPendingFault st tid tf) := by
  unfold recordPendingFault
  cases hT : st.getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact hInv
  | some tcb =>
      rw [SystemState.updateTcb_eq_of_some hT]
      exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull st tid tcb
        { tcb with pendingFault := some tf } hObjInv hInv
        ((SystemState.getTcb?_eq_some_iff st tid tcb).mp hT)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- WS-RR RR4.9/RR4.17: the deschedule half of the fail-closed dispositions
preserves the bundle.

`removeRunnableOnCore` leaves the object map untouched, so nineteen conjuncts
transport by lookup congruence; the twentieth, `passiveServerIdle`, is the one
a *removal* can perturb — descheduling a thread adds it to the "passive" set
the invariant constrains — and it transports through the SM6.D removal frame
under `hAllowed`.

`hAllowed` is a pre-state fact and dischargeable: a **faulting thread is
running**, hence `.ready`, hence in `passiveServerIdleAllowed`
(`faultSuspendOnCore_preserves_ipcInvariantFull_of_ready`). It is stated in
this general form because the abandon path reaches it from a woken (also
`.ready`) thread by the same argument. -/
private theorem removeRunnableOnCore_preserves_bundle
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hAllowed : ∀ tcb : TCB, st.getTcb? tid = some tcb →
      tcb.schedContextBinding ≠ .unbound ∨ passiveServerIdleAllowed tcb.ipcState)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (removeRunnableOnCore st tid c) :=
  ipcInvariantFull_of_getElem_eq (s1 := st) (fun _ => rfl)
    (passiveServerIdle_of_frame
      (removeRunnableOnCore_passiveServerIdleFrame st tid c
        (fun tcb hTcb => hAllowed tcb ((SystemState.getTcb?_eq_some_iff st tid tcb).mpr hTcb)))
      hInv.passiveServerIdle)
    hInv

/-- WS-RR RR4.9/RR4.17: **the fail-closed suspend preserves the bundle.**

The deschedule transports by the lemma above; the `.Inactive` store rewrites
one TCB's `threadState`, a field no conjunct reads, so it transports by the
one-TCB-rewrite lever with every field obligation `rfl`.

This is what makes RR4.9 free of a soundness cost: fail-closed suspension is
not a hole punched in the IPC invariant, it is a state change the invariant
cannot see. -/
theorem faultSuspendOnCore_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hAllowed : ∀ tcb : TCB, st.getTcb? tid = some tcb →
      tcb.schedContextBinding ≠ .unbound ∨ passiveServerIdleAllowed tcb.ipcState)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (faultSuspendOnCore st tid c) := by
  have hInvR : ipcInvariantFull (removeRunnableOnCore st tid c) :=
    removeRunnableOnCore_preserves_bundle st tid c hAllowed hInv
  unfold faultSuspendOnCore
  cases hT : (removeRunnableOnCore st tid c).getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact hInvR
  | some tcb =>
      rw [SystemState.updateTcb_eq_of_some hT]
      exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull
          (removeRunnableOnCore st tid c) tid tcb
          { tcb with threadState := .Inactive } hObjInv hInvR
          ((SystemState.getTcb?_eq_some_iff _ tid tcb).mp hT)
          rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- WS-RR RR4.9: the dischargeable form — a **running** thread is `.ready`,
which is a `passiveServerIdleAllowed` state, so a fault suspension of the
thread that just faulted needs no side condition beyond what the trap path
already knows. -/
theorem faultSuspendOnCore_preserves_ipcInvariantFull_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hReady : ∀ tcb : TCB, st.getTcb? tid = some tcb →
      tcb.ipcState = .ready)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (faultSuspendOnCore st tid c) :=
  faultSuspendOnCore_preserves_ipcInvariantFull st tid c hObjInv
    (fun tcb hTcb => Or.inr (Or.inl (hReady tcb hTcb))) hInv

/-- WS-RR RR4.18: the reply-declined disposition preserves the bundle — it
adds only the `pendingFault` clear to the suspend's writes, and that field is
read by no conjunct either. -/
theorem faultAbandonOnCore_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hAllowed : ∀ tcb : TCB, st.getTcb? tid = some tcb →
      tcb.schedContextBinding ≠ .unbound ∨ passiveServerIdleAllowed tcb.ipcState)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (faultAbandonOnCore st tid c) := by
  have hInvR : ipcInvariantFull (removeRunnableOnCore st tid c) :=
    removeRunnableOnCore_preserves_bundle st tid c hAllowed hInv
  unfold faultAbandonOnCore
  cases hT : (removeRunnableOnCore st tid c).getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact hInvR
  | some tcb =>
      rw [SystemState.updateTcb_eq_of_some hT]
      exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull
          (removeRunnableOnCore st tid c) tid tcb
          { tcb with threadState := .Inactive, pendingFault := none } hObjInv hInvR
          ((SystemState.getTcb?_eq_some_iff _ tid tcb).mp hT)
          rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- WS-RR RR4.18: the dischargeable form — the thread a reply abandons was
woken `.ready` by that reply. -/
theorem faultAbandonOnCore_preserves_ipcInvariantFull_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hReady : ∀ tcb : TCB, st.getTcb? tid = some tcb →
      tcb.ipcState = .ready)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (faultAbandonOnCore st tid c) :=
  faultAbandonOnCore_preserves_ipcInvariantFull st tid c hObjInv
    (fun tcb hTcb => Or.inr (Or.inl (hReady tcb hTcb))) hInv

/-- WS-RR RR4.16/RR4.18: **installing a restart frame preserves the bundle.**

The restart writes `registerContext` (the RR4.16 writeback) and clears
`pendingFault`; neither is read by any conjunct, so the whole bundle
transports. This is the same lever `writeReturnFrameToTcb` goes through for
a syscall return — the two writebacks share a mechanism, so they share a
preservation argument. -/
theorem applyFaultRestart_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (applyFaultRestart st tid frame) := by
  unfold applyFaultRestart
  cases hT : st.getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact hInv
  | some tcb =>
      rw [SystemState.updateTcb_eq_of_some hT]
      exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull st tid tcb
        { tcb.withRestartFrame frame with pendingFault := none } hObjInv hInv
        ((SystemState.getTcb?_eq_some_iff st tid tcb).mp hT)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- **WS-RR RR8.16 (`v0.35.200`) — RELOCATED**: the four fault-path
-- `_preserves_objects_invExt` frames (`recordPendingFault`, `applyFaultRestart`,
-- `faultSuspendOnCore`, `faultAbandonOnCore`) now live beside the operations they
-- frame, in `IPC/Operations/Fault.lean` and `IPC/CrossCore/Fault.lean`.  Each is
-- one citation of `SystemState.updateTcb_preserves_objects_invExt` and reads no
-- staged surface, so keeping them in *this* module — staged for the
-- `ipcInvariantFull` call-chain surface — put them out of reach of the production
-- bundle lifts in `IPC/Invariant/FaultBundlePreservation.lean`, which is the
-- RR2-closure rule (*a theorem that reads no staged surface is production*)
-- arriving at four frames nobody had asked of it before.

-- **WS-RR RR8.16 (`v0.35.200`) — RELOCATED**: the two chain
-- `_preserves_objects_invExt` frames now live beside the chains they frame, in
-- the production `IPC/CrossCore/EndpointCallDispatch.lean` and
-- `IPC/CrossCore/EndpointReplyDispatchInvariant.lean`.  Same reason as the four
-- fault-path frames above: neither reads a staged surface, and the production
-- bundle lifts in `IPC/Invariant/FaultBundlePreservation.lean` must be able to
-- cite them.

-- ============================================================================
-- §2 The Call and Reply chains preserve the object-store invariant
-- ============================================================================



/-- WS-RR RR4.17 (**the delivery payoff**): `faultDeliverOnCore` preserves
`ipcInvariantFull`, on both dispositions.

The composition, arm for arm:

* **delivered** — the live `.call` chain's own bundle theorem, then the fault
  record (a `pendingFault` write no conjunct reads);
* **suspended** — the fail-closed deschedule-and-`.Inactive`, then the same
  record.

Every hypothesis is a **pre-state** fact about the faulting thread and the
endpoints, in the RR3 de-threaded style: nothing is threaded on a post-state.
`hCallerReady` is the running-thread fact the trap path knows by construction
(a thread that faults was executing), and it discharges `hCallerNotRecv` and
`hCallerNotReply` on the spot; `hCallerNotUnbound` is the SchedContext a
running thread necessarily holds. -/
theorem faultDeliverOnCore_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext)
    (c : CoreId)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some tid ∧ ep.sendQ.tail ≠ some tid ∧
      ep.receiveQ.head ≠ some tid ∧ ep.receiveQ.tail ≠ some tid)
    (hSendTailFresh : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ epId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = epId → ep'.receiveQ.tail ≠ some tailTid))
    (hCallerReady : ∀ (tcb : TCB), st.getTcb? tid = some tcb → tcb.ipcState = .ready)
    (hCallerNotUnbound : ∀ (tcb : TCB), st.getTcb? tid = some tcb →
      tcb.schedContextBinding ≠ .unbound)
    (hNotSelf : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (receiverTid : SeLe4n.ThreadId),
      st.getEndpoint? epId = some ep → ep.receiveQ.head = some receiverTid →
      tid ≠ receiverTid) :
    ipcInvariantFull (faultDeliverOnCore st tid f ctx c).1 := by
  have hNotRecv : ∀ (tcb : TCB), st.getTcb? tid = some tcb →
      ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep := by
    intro tcb hTcb ep; rw [hCallerReady tcb hTcb]; exact fun h => by cases h
  have hNotReply : ∀ (tcb : TCB), st.getTcb? tid = some tcb →
      ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt := by
    intro tcb hTcb ep rt; rw [hCallerReady tcb hTcb]; exact fun h => by cases h
  rcases hRes : resolveFaultHandler st tid with e | tgt
  · simp only [faultDeliverOnCore, hRes]
    exact recordPendingFault_preserves_ipcInvariantFull _ tid _
      (faultSuspendOnCore_preserves_objects_invExt st tid c hObjInv)
      (faultSuspendOnCore_preserves_ipcInvariantFull_of_ready st tid c hObjInv
        hCallerReady hInv)
  · have hCall := endpointCallCrossCoreDispatch_preserves_ipcInvariantFull tgt.endpoint tid
      (faultMessage f ctx tgt.cap.badge) tgt.cap.rights (SeLe4n.Slot.ofNat 0)
      c st hInv hObjInv hAllBudgetsNone
      (by intro i cap hCap; simp [faultMessage] at hCap)
      hFreshCaller (hSendTailFresh tgt.endpoint) hNotRecv hCallerReady hNotReply
      hCallerNotUnbound (fun ep r hEp hHead => hNotSelf tgt.endpoint ep r hEp hHead)
    have hCallObj := endpointCallCrossCoreDispatch_preserves_objects_invExt tgt.endpoint tid
      (faultMessage f ctx tgt.cap.badge) tgt.cap.rights (SeLe4n.Slot.ofNat 0)
      c st hObjInv
    rcases hStep : endpointCallCrossCoreDispatch tgt.endpoint tid
        (faultMessage f ctx tgt.cap.badge) tgt.cap.rights
        (SeLe4n.Slot.ofNat 0) c st with ⟨stC, res⟩
    rw [hStep] at hCall hCallObj
    simp only at hCall hCallObj
    cases res with
    | error e =>
        simp only [faultDeliverOnCore, hRes, hStep]
        exact recordPendingFault_preserves_ipcInvariantFull _ tid _
          (faultSuspendOnCore_preserves_objects_invExt st tid c hObjInv)
          (faultSuspendOnCore_preserves_ipcInvariantFull_of_ready st tid c hObjInv
            hCallerReady hInv)
    | ok r =>
        obtain ⟨summary, sgi?⟩ := r
        simp only [faultDeliverOnCore, hRes, hStep]
        exact recordPendingFault_preserves_ipcInvariantFull _ tid _
          (stageWokenDelivery_preserves_objects_invExt stC _ _ hCallObj)
          (stageWokenDelivery_preserves_ipcInvariantFull stC _ _ hCallObj hCall)

/-- WS-RR RR4.17: and the delivery preserves the object-store invariant. -/
theorem faultDeliverOnCore_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext)
    (c : CoreId) (hObjInv : st.objects.invExt) :
    (faultDeliverOnCore st tid f ctx c).1.objects.invExt := by
  rcases hRes : resolveFaultHandler st tid with e | tgt
  · simp only [faultDeliverOnCore, hRes]
    exact recordPendingFault_preserves_objects_invExt _ tid _
      (faultSuspendOnCore_preserves_objects_invExt st tid c hObjInv)
  · have hCallObj := endpointCallCrossCoreDispatch_preserves_objects_invExt tgt.endpoint tid
      (faultMessage f ctx tgt.cap.badge) tgt.cap.rights (SeLe4n.Slot.ofNat 0)
      c st hObjInv
    rcases hStep : endpointCallCrossCoreDispatch tgt.endpoint tid
        (faultMessage f ctx tgt.cap.badge) tgt.cap.rights
        (SeLe4n.Slot.ofNat 0) c st with ⟨stC, res⟩
    rw [hStep] at hCallObj
    simp only at hCallObj
    cases res with
    | error e =>
        simp only [faultDeliverOnCore, hRes, hStep]
        exact recordPendingFault_preserves_objects_invExt _ tid _
          (faultSuspendOnCore_preserves_objects_invExt st tid c hObjInv)
    | ok r =>
        obtain ⟨summary, sgi?⟩ := r
        simp only [faultDeliverOnCore, hRes, hStep]
        exact recordPendingFault_preserves_objects_invExt _ tid _
          (stageWokenDelivery_preserves_objects_invExt stC _ _ hCallObj)


/-- WS-RR RR4.17/RR4.20: **the flow-checked delivery preserves the bundle.**

The arm `Kernel/FaultEntry.lean` actually calls. It needs no hypothesis the
unchecked delivery does not: a permitted flow *is* the unchecked delivery
(`faultDeliverOnCoreChecked_flow_allowed`), and a denied one is the RR4.9
suspend, which the `_of_ready` corollary already covers from `hCallerReady`.
So gating the live entry costs the invariant surface nothing — the property
that let the gate be added without reopening RR4.17. -/
theorem faultDeliverOnCoreChecked_preserves_ipcInvariantFull
    (lctx : LabelingContext) (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault)
    (ctx : FaultContext) (c : CoreId)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some tid ∧ ep.sendQ.tail ≠ some tid ∧
      ep.receiveQ.head ≠ some tid ∧ ep.receiveQ.tail ≠ some tid)
    (hSendTailFresh : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ epId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = epId → ep'.receiveQ.tail ≠ some tailTid))
    (hCallerReady : ∀ (tcb : TCB), st.getTcb? tid = some tcb → tcb.ipcState = .ready)
    (hCallerNotUnbound : ∀ (tcb : TCB), st.getTcb? tid = some tcb →
      tcb.schedContextBinding ≠ .unbound)
    (hNotSelf : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (receiverTid : SeLe4n.ThreadId),
      st.getEndpoint? epId = some ep → ep.receiveQ.head = some receiverTid →
      tid ≠ receiverTid) :
    ipcInvariantFull (faultDeliverOnCoreChecked lctx st tid f ctx c).1 := by
  have hSusp : ipcInvariantFull
      (recordPendingFault (faultSuspendOnCore st tid c) tid { fault := f, context := ctx }) :=
    recordPendingFault_preserves_ipcInvariantFull _ tid _
      (faultSuspendOnCore_preserves_objects_invExt st tid c hObjInv)
      (faultSuspendOnCore_preserves_ipcInvariantFull_of_ready st tid c hObjInv
        hCallerReady hInv)
  unfold faultDeliverOnCoreChecked
  cases hRes : resolveFaultHandler st tid with
  | error e => simpa only [hRes] using hSusp
  | ok tgt =>
      by_cases hGate : endpointFlowGate lctx tgt.endpoint (lctx.threadLabelOf tid)
          (lctx.endpointLabelOf tgt.endpoint) = true
      · simp only [hGate, if_true]
        exact faultDeliverOnCore_preserves_ipcInvariantFull st tid f ctx c hInv hObjInv
          hAllBudgetsNone hFreshCaller hSendTailFresh hCallerReady hCallerNotUnbound hNotSelf
      · simp only [Bool.not_eq_true] at hGate
        simpa only [hRes, hGate, Bool.false_eq_true, if_false] using hSusp

/-- WS-RR RR4.20: and the flow-checked delivery preserves the object-store
invariant, by the same two-arm split. -/
theorem faultDeliverOnCoreChecked_preserves_objects_invExt
    (lctx : LabelingContext) (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault)
    (ctx : FaultContext) (c : CoreId) (hObjInv : st.objects.invExt) :
    (faultDeliverOnCoreChecked lctx st tid f ctx c).1.objects.invExt := by
  have hSusp : (recordPendingFault (faultSuspendOnCore st tid c) tid
      { fault := f, context := ctx }).objects.invExt :=
    recordPendingFault_preserves_objects_invExt _ tid _
      (faultSuspendOnCore_preserves_objects_invExt st tid c hObjInv)
  unfold faultDeliverOnCoreChecked
  cases hRes : resolveFaultHandler st tid with
  | error e => simpa only [hRes] using hSusp
  | ok tgt =>
      by_cases hGate : endpointFlowGate lctx tgt.endpoint (lctx.threadLabelOf tid)
          (lctx.endpointLabelOf tgt.endpoint) = true
      · simp only [hGate, if_true]
        exact faultDeliverOnCore_preserves_objects_invExt st tid f ctx c hObjInv
      · simp only [Bool.not_eq_true] at hGate
        simpa only [hRes, hGate, Bool.false_eq_true, if_false] using hSusp

-- ============================================================================
-- §4 RR4.18 — the fault reply preserves the bundle
-- ============================================================================

/-- WS-RR RR4.18 (**the reply payoff**): `faultReplyOnCore` preserves
`ipcInvariantFull` on both outcomes.

The composition: the live `.reply` chain's own bundle theorem (which brings
the donation return and the priority-inheritance reversion with it — the
reason a bare reply's post-state satisfies only
`ipcInvariantFullExceptDonationOwner` and this one satisfies the full bundle),
then either the restart writeback or the abandon.

**WS-RR RR8.16 (`v0.35.195`): the DONATING fault reply is covered, and until this
cut it was not.**  The composition ran through
`endpointReplyCrossCoreDispatch_preserves_ipcInvariantFull`, whose
`hNoDonationOwnedBy` says no thread's binding is `.donated _ faulted` — and on the
ordinary MCS fault path of a thread that holds a reservation that is **false**:
`faultDeliverOnCore` composes the live `.call` chain, so the delivery donates the
faulted thread's scheduling context to its handler, and the handler's binding is
`.donated sc faulted` in exactly the state it replies from.  So the payoff was
stated over a premise the path it is named for refutes, which is vacuity wearing a
confinement.  It composes `endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull`
instead — the same five pre-state-computable conditions the live `.reply` arm's
own dispatch payoff already carries, at `IpcMessage.empty` — and the confinement is
gone rather than restated.

**WS-RR RR8.16 (`v0.35.195`): the abandon arm's idle-state side condition is
DERIVED, not carried.**  It used to be a hypothesis (`hTargetIdleAllowed`), a
post-reply fact about the dispatch's own output, and the docstring said in prose
why it holds: *the reply wakes its target `.ready`, and `.ready` is a
`passiveServerIdleAllowed` state*.  A sentence is not a discharge, and the
hypothesis was consumed on the `.ok` branch alone — so nothing weaker was ever
being asked for, and
`endpointReplyCrossCoreDispatch_ok_target_ready` reads the same fact off the
**outcome**, which is what retires it.  Closing this is what lets the staged
dispatch payoff's `.reply` arm cover a faulted caller at all: a caller could not
discharge a post-state hypothesis without threading one, which is what the RR3
de-threading gate forbids.

The condition binds only on the abandon arm, where the thread is descheduled —
the restart arm writes no scheduler slot at all. -/
theorem faultReplyOnCore_preserves_ipcInvariantFull
    (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (c : CoreId) (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    -- **WS-RR RR8.16**: the five conditions
    -- `endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull` carries, at
    -- the empty message this seam replies with.  Each is a pre-state-computable
    -- expression, so the de-threading discipline is respected and a caller
    -- discharges them before the step.
    (hDonationReturned : ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
        (endpointReplyOnCore replier faulted IpcMessage.empty c st).1.objects[s.toObjId]?
            = some (.tcb sTcb) →
        sTcb.schedContextBinding = .donated sc faulted →
        ∃ rid : SeLe4n.ReplyId, answeredReplyObject? st faulted = some rid ∧
          replyFrameHeadHolder?
            (endpointReplyOnCore replier faulted IpcMessage.empty c st).1 rid = some (sc, s))
    (hHolderDonation : ∀ rid : SeLe4n.ReplyId, answeredReplyObject? st faulted = some rid →
      replyFrameHeadHolderDonation
        (endpointReplyOnCore replier faulted IpcMessage.empty c st).1 rid faulted)
    (hHolderIdleAllowed : ∀ (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId)
        (holder : SeLe4n.ThreadId),
      answeredReplyObject? st faulted = some rid →
      replyFrameHeadHolder?
          (endpointReplyOnCore replier faulted IpcMessage.empty c st).1 rid
            = some (scId, holder) →
      ∀ tcb, (endpointReplyOnCore replier faulted IpcMessage.empty c st).1.getTcb? holder
          = some tcb →
        passiveServerIdleAllowed tcb.ipcState)
    -- **WS-OD OD4.4**: the reply's donation return resolves its new owner from
    -- the context's reply stack; this is the obligation that resolution carries,
    -- stated at the state the pop runs at (the reply leg commits first).
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid
          (endpointReplyOnCore replier faulted IpcMessage.empty c st).1
          scId serverTid originalOwner)
    -- **`v0.35.157`**: the origin redirect's coherence obligation, at the same
    -- state and quantified over the answered frame like the trigger's own fields.
    (hOriginCoherent : ∀ rid : SeLe4n.ReplyId, answeredReplyObject? st faulted = some rid →
      redirectedOriginFrameCoherent
        (endpointReplyOnCore replier faulted IpcMessage.empty c st).1 rid faulted) :
    ipcInvariantFull (faultReplyOnCore replier faulted mi regs c st).1 := by
  cases hTcb : st.getTcb? faulted with
  | none => simpa only [faultReplyOnCore, hTcb] using hInv
  | some tcb =>
      cases hFault : tcb.pendingFault with
      | none => simpa only [faultReplyOnCore, hTcb, hFault] using hInv
      | some tf =>
          have hRep := endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull replier
            faulted IpcMessage.empty c st hInv hObjInv hDonationReturned hHolderDonation
            hAllBudgetsNone hHolderIdleAllowed hStackValid hOriginCoherent
          have hRepObj := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier
            faulted IpcMessage.empty c st hObjInv
          rcases hStep : endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty c st
            with ⟨stR, res⟩
          rw [hStep] at hRep hRepObj
          simp only at hRep hRepObj
          cases res with
          | error e => simpa only [faultReplyOnCore, hTcb, hFault, hStep] using hInv
          | ok sgi? =>
              -- **WS-RR RR8.16**: the abandon arm's idle-state obligation, read
              -- off the dispatch's own `.ok` outcome rather than carried.
              have hAbandonIdleAllowed : ∀ u : TCB, stR.getTcb? faulted = some u →
                  u.schedContextBinding ≠ .unbound ∨ passiveServerIdleAllowed u.ipcState := by
                intro u hU
                refine Or.inr ?_
                have hReady : u.ipcState = .ready :=
                  endpointReplyCrossCoreDispatch_ok_target_ready replier faulted
                    IpcMessage.empty c st hObjInv (by rw [hStep]) (by rw [hStep]; exact hU)
                rw [hReady]
                exact Or.inl rfl
              simp only [faultReplyOnCore, hTcb, hFault, hStep, faultReplyApplyOnCore]
              cases hOut : decodeFaultReply tf.fault tf.context mi regs with
              | restart frame =>
                  simpa only [hOut] using
                    applyFaultRestart_preserves_ipcInvariantFull stR faulted frame hRepObj hRep
              | abandon =>
                  simpa only [hOut] using
                    faultAbandonOnCore_preserves_ipcInvariantFull stR faulted
                      (determineTargetCore stR faulted) hRepObj hAbandonIdleAllowed hRep

/-- WS-RR RR4.18: and the reply preserves the object-store invariant. -/
theorem faultReplyOnCore_preserves_objects_invExt
    (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (c : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    (faultReplyOnCore replier faulted mi regs c st).1.objects.invExt := by
  cases hTcb : st.getTcb? faulted with
  | none => simpa only [faultReplyOnCore, hTcb] using hObjInv
  | some tcb =>
      cases hFault : tcb.pendingFault with
      | none => simpa only [faultReplyOnCore, hTcb, hFault] using hObjInv
      | some tf =>
          have hRepObj := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier
            faulted IpcMessage.empty c st hObjInv
          rcases hStep : endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty c st
            with ⟨stR, res⟩
          rw [hStep] at hRepObj
          simp only at hRepObj
          cases res with
          | error e => simpa only [faultReplyOnCore, hTcb, hFault, hStep] using hObjInv
          | ok sgi? =>
              simp only [faultReplyOnCore, hTcb, hFault, hStep, faultReplyApplyOnCore]
              cases hOut : decodeFaultReply tf.fault tf.context mi regs with
              | restart frame =>
                  simpa only [hOut] using
                    applyFaultRestart_preserves_objects_invExt stR faulted frame hRepObj
              | abandon =>
                  simpa only [hOut] using
                    faultAbandonOnCore_preserves_objects_invExt stR faulted
                      (determineTargetCore stR faulted) hRepObj

-- ============================================================================
-- WS-RM RM5.2 — the fault reply frames the donation chain
-- ============================================================================

/-- **WS-RM (`v0.35.6`)**: installing a restart frame carries no chain data.

`applyFaultRestart`'s one write is a `.tcb` at a key that already held one
(`getTcb?` is what selects the arm), so no Reply and no SchedContext is created,
destroyed or rewritten. -/
theorem applyFaultRestart_donationChainFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame)
    (hObjInv : st.objects.invExt) :
    donationChainFrame st (applyFaultRestart st tid frame) := by
  unfold applyFaultRestart
  cases hT : st.getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact donationChainFrame.refl st
  | some tcb =>
      rw [SystemState.updateTcb_eq_of_some hT]
      exact donationChainFrame_of_objects_insert hObjInv
        (by rw [(SystemState.getTcb?_eq_some_iff st tid tcb).mp hT]; rfl)
        (by rw [(SystemState.getTcb?_eq_some_iff st tid tcb).mp hT]; rfl)
        (fun _ h => by cases h)

/-- **WS-RM (`v0.35.6`)**: and so does abandoning the faulted thread — a
deschedule, which writes no object at all, then the same shape of `.tcb`
rewrite. -/
theorem faultAbandonOnCore_donationChainFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (hObjInv : st.objects.invExt) :
    donationChainFrame st (faultAbandonOnCore st tid c) := by
  have hObjsR : (removeRunnableOnCore st tid c).objects = st.objects :=
    removeRunnableOnCore_preserves_objects st tid c
  have hFrameR : donationChainFrame st (removeRunnableOnCore st tid c) :=
    donationChainFrame.of_objects_eq hObjsR
  have hInvR : (removeRunnableOnCore st tid c).objects.invExt := by
    rw [hObjsR]; exact hObjInv
  refine hFrameR.trans ?_
  unfold faultAbandonOnCore
  cases hT : (removeRunnableOnCore st tid c).getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact donationChainFrame.refl _
  | some tcb =>
      rw [SystemState.updateTcb_eq_of_some hT]
      exact donationChainFrame_of_objects_insert hInvR
        (by rw [(SystemState.getTcb?_eq_some_iff _ tid tcb).mp hT]; rfl)
        (by rw [(SystemState.getTcb?_eq_some_iff _ tid tcb).mp hT]; rfl)
        (fun _ h => by cases h)

/-- **WS-RM (`v0.35.6`)**: the fault reply's third stage frames the chain on
both outcomes. -/
theorem faultReplyApplyOnCore_donationChainFrame (st : SystemState)
    (faulted : SeLe4n.ThreadId) (outcome : FaultReplyOutcome)
    (hObjInv : st.objects.invExt) :
    donationChainFrame st (faultReplyApplyOnCore st faulted outcome) := by
  cases outcome with
  | restart frame =>
      simpa only [faultReplyApplyOnCore] using
        applyFaultRestart_donationChainFrame st faulted frame hObjInv
  | abandon =>
      simpa only [faultReplyApplyOnCore] using
        faultAbandonOnCore_donationChainFrame st faulted
          (determineTargetCore st faulted) hObjInv

/-- **WS-RM RM5.2**: the fault reply preserves the donation chain.

Its second stage **is** the live `.reply` chain, so the reply path's own payoff
(`endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed`) carries the
whole of the chain reasoning; stage 3 writes a TCB and nothing else.  The
hypothesis is therefore the reply payoff's own -- a fault reply that answers a
caller whose reply frame *heads* a scheduling context leaves that context
headless unless the donation pop beneath it re-heads the frame below.

**WS-HP HP4.4**: under the head-driven trigger the pop resolves that context from
the very frame the relaxation sits at, so the coherence relation this composite
used to carry was no longer needed; what remains is `replyFrameHeadIsBound`, which
rules out a head context bound to nobody.  That relation --
`answeredHeadContextIsServerDonation` -- was **deleted** at HP7 (`v0.35.46`), once
HP6.8's splice had also falsified it on reachable states; see the tombstone beside
the `WS-HP HP7` banner in `IPC/CrossCore/EndpointReplyDispatchInvariant.lean`. -/
theorem faultReplyOnCore_preserves_donationChainWellFormed
    (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (c : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hHeadBound : ∀ rid : SeLe4n.ReplyId, answeredReplyObject? st faulted = some rid →
      replyFrameHeadIsBound (endpointReplyOnCore replier faulted IpcMessage.empty c st).1 rid) :
    donationChainWellFormed (faultReplyOnCore replier faulted mi regs c st).1 := by
  unfold faultReplyOnCore
  cases hTcb : st.getTcb? faulted with
  | none => simpa only [hTcb] using hChain
  | some tcb =>
    cases hFault : tcb.pendingFault with
    | none => simpa only [hTcb, hFault] using hChain
    | some tf =>
      have hRepChain := endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed
        replier faulted IpcMessage.empty c st hObjInv hChain hHeadBound
      have hRepObj := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier
        faulted IpcMessage.empty c st hObjInv
      rcases hStep : endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty c st
        with ⟨stR, res⟩
      rw [hStep] at hRepChain hRepObj
      simp only at hRepChain hRepObj
      cases res with
      | error e => simpa only [hTcb, hFault, hStep] using hChain
      | ok sgi? =>
          simp only [hFault]
          exact donationChainWellFormed_of_frame
            (faultReplyApplyOnCore_donationChainFrame stR faulted
              (decodeFaultReply tf.fault tf.context mi regs) hRepObj) hRepChain

/-- **WS-RM RM5.2**: and so does the reply *transfer* — seL4's
`doReplyTransfer`, whose two branches are the two theorems above.

**One** chain hypothesis, not one per branch: the fault branch replies with
`IpcMessage.empty` and the ordinary branch with `msg`, which differed only in the
post-state expression the condition used to be written over.  The message is not
something the question reads — it asks which scheduling context a *pre-state*
reply frame heads — so at the pre-state the two spellings are one proposition,
and a caller supplies it once. -/
theorem replyTransferOnCore_preserves_donationChainWellFormed
    (replier callerTid : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (msg : IpcMessage) (c : CoreId)
    (st st' : SystemState) (u : Unit)
    (hObjInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    -- **WS-HP HP4.4**: the fault arm and the ordinary arm reply with different
    -- messages and the same *frame*, so the one condition still serves both.
    (hHeadBoundFault : ∀ rid : SeLe4n.ReplyId, answeredReplyObject? st callerTid = some rid →
      replyFrameHeadIsBound (endpointReplyOnCore replier callerTid IpcMessage.empty c st).1 rid)
    (hHeadBound : ∀ rid : SeLe4n.ReplyId, answeredReplyObject? st callerTid = some rid →
      replyFrameHeadIsBound (endpointReplyOnCore replier callerTid msg c st).1 rid)
    (hStep : replyTransferOnCore replier callerTid mi regs msg c st = .ok (u, st')) :
    donationChainWellFormed st' := by
  unfold replyTransferOnCore at hStep
  by_cases hF : threadHasPendingFault st callerTid
  · rw [if_pos hF] at hStep
    have hChainF := faultReplyOnCore_preserves_donationChainWellFormed replier callerTid
      mi regs c st hObjInv hChain hHeadBoundFault
    rcases hFR : faultReplyOnCore replier callerTid mi regs c st with ⟨stF, resF⟩
    rw [hFR] at hStep hChainF
    simp only at hChainF
    cases resF with
    | error e => rw [show (Except.error e : Except KernelError _) = _ from rfl] at hStep; cases hStep
    | ok _ =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        exact hStep.2 ▸ hChainF
  · rw [if_neg hF] at hStep
    have hChainR := endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed
      replier callerTid msg c st hObjInv hChain hHeadBound
    have hObjR := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier callerTid
      msg c st hObjInv
    rcases hRD : endpointReplyCrossCoreDispatch replier callerTid msg c st with ⟨stR, resR⟩
    rw [hRD] at hStep hChainR hObjR
    simp only at hChainR hObjR
    cases resR with
    | error e => simp only [] at hStep; cases hStep
    | ok _ =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        refine hStep.2 ▸ donationChainWellFormed_of_frame ?_ hChainR
        exact stageDeliveredMessage_donationChainFrame stR callerTid 0 hObjR


end SeLe4n.Kernel
