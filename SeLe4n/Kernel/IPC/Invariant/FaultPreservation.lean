-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-RR RR4.17/RR4.18 — the fault-IPC `ipcInvariantFull`
-- surface.  Staged because the delivery's bundle composes the staged
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
fault reply is an endpoint **Reply** followed by a register writeback.  So
neither owes `ipcInvariantFull` a fresh proof: each is a composition of a
transition that already has one with TCB writes that touch **no field any
conjunct reads**.

That is the whole design argument for RR4.11's "reuse the Call machinery
rather than a parallel path", cashed out.  Concretely, the fault path's own
writes are:

| write | fields touched | read by a conjunct? |
|---|---|---|
| `recordPendingFault` | `pendingFault` | no |
| `faultSuspend` / `faultSuspendOnCore` | `threadState`, run queue | no / frame |
| `faultAbandon` / `faultAbandonOnCore` | `threadState`, `pendingFault`, run queue | no / frame |
| `applyFaultRestart` | `registerContext`, `pendingFault` | no |

Every one of them therefore goes through the one-TCB-rewrite lever
(`insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull`), whose nine
field-agreement obligations all discharge by `rfl`.  The run-queue removal is
handled by the same lever's passive-server frame, which reads the scheduler
only through `passiveServerIdleFrame`.
-/

namespace SeLe4n.Kernel

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  The kernel's own fault-path writes
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
  | none => exact hInv
  | some tcb =>
      exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull st tid tcb
        { tcb with pendingFault := some tf } hObjInv hInv
        ((SystemState.getTcb?_eq_some_iff st tid tcb).mp hT)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- WS-RR RR4.17: `recordPendingFault` preserves the object-store invariant —
one `insert` of a well-typed TCB. -/
theorem recordPendingFault_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (tf : ThreadFault)
    (hObjInv : st.objects.invExt) :
    (recordPendingFault st tid tf).objects.invExt := by
  unfold recordPendingFault
  cases st.getTcb? tid with
  | none => exact hObjInv
  | some tcb => exact RobinHood.RHTable.insert_preserves_invExt _ _ _ hObjInv

/-- WS-RR RR4.9/RR4.17: the deschedule half of the fail-closed dispositions
preserves the bundle.

`removeRunnableOnCore` leaves the object map untouched, so nineteen conjuncts
transport by lookup congruence; the twentieth, `passiveServerIdle`, is the one
a *removal* can perturb — descheduling a thread adds it to the "passive" set
the invariant constrains — and it transports through the SM6.D removal frame
under `hAllowed`.

`hAllowed` is a pre-state fact and dischargeable: a **faulting thread is
running**, hence `.ready`, hence in `passiveServerIdleAllowed`
(`faultSuspendOnCore_preserves_ipcInvariantFull_of_ready`).  It is stated in
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
  simp only [faultSuspendOnCore]
  cases hT : (removeRunnableOnCore st tid c).getTcb? tid with
  | none => simpa only [hT] using hInvR
  | some tcb =>
      simpa only [hT] using
        insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull
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

/-- WS-RR RR4.9: and it preserves the object-store invariant. -/
theorem faultSuspendOnCore_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hObjInv : st.objects.invExt) :
    (faultSuspendOnCore st tid c).objects.invExt := by
  simp only [faultSuspendOnCore]
  cases hT : (removeRunnableOnCore st tid c).getTcb? tid with
  | none => simpa only [hT] using hObjInv
  | some tcb =>
      simpa only [hT] using
        RobinHood.RHTable.insert_preserves_invExt
          (removeRunnableOnCore st tid c).objects tid.toObjId _ hObjInv

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
  simp only [faultAbandonOnCore]
  cases hT : (removeRunnableOnCore st tid c).getTcb? tid with
  | none => simpa only [hT] using hInvR
  | some tcb =>
      simpa only [hT] using
        insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull
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

/-- WS-RR RR4.18: and it preserves the object-store invariant. -/
theorem faultAbandonOnCore_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hObjInv : st.objects.invExt) :
    (faultAbandonOnCore st tid c).objects.invExt := by
  simp only [faultAbandonOnCore]
  cases hT : (removeRunnableOnCore st tid c).getTcb? tid with
  | none => simpa only [hT] using hObjInv
  | some tcb =>
      simpa only [hT] using
        RobinHood.RHTable.insert_preserves_invExt
          (removeRunnableOnCore st tid c).objects tid.toObjId _ hObjInv

/-- WS-RR RR4.16/RR4.18: **installing a restart frame preserves the bundle.**

The restart writes `registerContext` (the RR4.16 writeback) and clears
`pendingFault`; neither is read by any conjunct, so the whole bundle
transports.  This is the same lever `writeReturnFrameToTcb` goes through for
a syscall return — the two writebacks share a mechanism, so they share a
preservation argument. -/
theorem applyFaultRestart_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (applyFaultRestart st tid frame) := by
  unfold applyFaultRestart
  cases hT : st.getTcb? tid with
  | none => exact hInv
  | some tcb =>
      exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull st tid tcb
        { tcb.withRestartFrame frame with pendingFault := none } hObjInv hInv
        ((SystemState.getTcb?_eq_some_iff st tid tcb).mp hT)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- WS-RR RR4.16: and it preserves the object-store invariant. -/
theorem applyFaultRestart_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame)
    (hObjInv : st.objects.invExt) :
    (applyFaultRestart st tid frame).objects.invExt := by
  unfold applyFaultRestart
  cases st.getTcb? tid with
  | none => exact hObjInv
  | some tcb => exact RobinHood.RHTable.insert_preserves_invExt _ _ _ hObjInv

-- ============================================================================
-- §2  The Call and Reply chains preserve the object-store invariant
-- ============================================================================

/-- The `.call` chain preserves `objects.invExt` — the rendezvous-plus-transfer
leg, the donation, and the priority-inheritance walk each do, and the chain is
their composition.  Needed because the fault delivery writes the fault record
onto the chain's post-state, and that write is an `insert`. -/
theorem endpointCallCrossCoreDispatch_preserves_objects_invExt
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    (endpointCallCrossCoreDispatch endpointId caller msg endpointRights callerCspaceRoot
      receiverSlotBase executingCore st).1.objects.invExt := by
  have hWc := endpointCallWithCapsOnCore_preserves_objects_invExt endpointId caller msg
    endpointRights callerCspaceRoot receiverSlotBase executingCore st hObjInv
  unfold endpointCallCrossCoreDispatch
  cases hWcEq : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st with
  | mk stW resW =>
      rw [hWcEq] at hWc
      simp only at hWc ⊢
      cases resW with
      | error e => exact hWc
      | ok r =>
          obtain ⟨summaryW, sgiW⟩ := r
          simp only
          split
          · split
            · split
              · exact hWc
              · rename_i stD hDon
                exact PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt
                  _ _ _ _
                  (applyCallDonationOnCore_preserves_objects_invExt _ _ _ _ _ _ hWc hDon)
            · exact hWc
          · exact hWc

/-- The `.reply` chain preserves `objects.invExt` — same shape, over the reply
delivery, the donation return and the priority-inheritance reversion. -/
theorem endpointReplyCrossCoreDispatch_preserves_objects_invExt
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (endpointReplyCrossCoreDispatch replier target msg executingCore st).1.objects.invExt := by
  have hRep := endpointReplyOnCore_preserves_objects_invExt replier target msg executingCore
    st hObjInv
  unfold endpointReplyCrossCoreDispatch
  cases hRepEq : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res1 =>
      rw [hRepEq] at hRep
      simp only at hRep ⊢
      cases res1 with
      | error e => exact hObjInv
      | ok replySgi? =>
          simp only
          split
          · split
            · split
              · exact hObjInv
              · rename_i st2 hRet
                exact PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt
                  _ _ _ _
                  (applyReplyDonationOnCore_preserves_objects_invExt _ _ _ _ _ _ hRep hRet)
            · exact hObjInv
          · exact hObjInv

-- ============================================================================
-- §3  RR4.17 — fault delivery preserves the bundle
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
      (faultMessage f ctx tgt.cap.badge) tgt.cap.rights tgt.cspaceRoot (SeLe4n.Slot.ofNat 0)
      c st hInv hObjInv hAllBudgetsNone
      (by intro i cap hCap; simp [faultMessage] at hCap)
      hFreshCaller (hSendTailFresh tgt.endpoint) hNotRecv hCallerReady hNotReply
      hCallerNotUnbound (fun ep r hEp hHead => hNotSelf tgt.endpoint ep r hEp hHead)
    have hCallObj := endpointCallCrossCoreDispatch_preserves_objects_invExt tgt.endpoint tid
      (faultMessage f ctx tgt.cap.badge) tgt.cap.rights tgt.cspaceRoot (SeLe4n.Slot.ofNat 0)
      c st hObjInv
    rcases hStep : endpointCallCrossCoreDispatch tgt.endpoint tid
        (faultMessage f ctx tgt.cap.badge) tgt.cap.rights tgt.cspaceRoot
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
        exact recordPendingFault_preserves_ipcInvariantFull stC tid _ hCallObj hCall

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
      (faultMessage f ctx tgt.cap.badge) tgt.cap.rights tgt.cspaceRoot (SeLe4n.Slot.ofNat 0)
      c st hObjInv
    rcases hStep : endpointCallCrossCoreDispatch tgt.endpoint tid
        (faultMessage f ctx tgt.cap.badge) tgt.cap.rights tgt.cspaceRoot
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
        exact recordPendingFault_preserves_objects_invExt stC tid _ hCallObj


/-- WS-RR RR4.17/RR4.20: **the flow-checked delivery preserves the bundle.**

The arm `Kernel/FaultEntry.lean` actually calls.  It needs no hypothesis the
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
-- §4  RR4.18 — the fault reply preserves the bundle
-- ============================================================================

/-- WS-RR RR4.18 (**the reply payoff**): `faultReplyOnCore` preserves
`ipcInvariantFull` on both outcomes.

The composition: the live `.reply` chain's own bundle theorem (which brings
the donation return and the priority-inheritance reversion with it — the
reason a bare reply's post-state satisfies only
`ipcInvariantFullExceptDonationOwner` and this one satisfies the full bundle),
then either the restart writeback or the abandon.

`hTargetIdleAllowed` is a post-reply side condition of exactly the kind the
`.reply` chain's own theorem already carries as `hServerIdleAllowed`, and it
is dischargeable for the same reason: the reply wakes its target `.ready`, and
`.ready` is a `passiveServerIdleAllowed` state.  It binds only on the abandon
arm, where the thread is descheduled — the restart arm writes no scheduler
slot at all. -/
theorem faultReplyOnCore_preserves_ipcInvariantFull
    (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (c : CoreId) (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hNoDonationOwnedBy : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
      (scId : SeLe4n.SchedContextId),
      st.getTcb? tid = some tcb →
      tcb.schedContextBinding ≠ .donated scId faulted)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hServerIdleAllowed : ∀ (expected : SeLe4n.ThreadId),
      recordedReplyServer? st faulted = some expected →
      ∀ tcb, st.getTcb? expected = some tcb → passiveServerIdleAllowed tcb.ipcState)
    (hTargetIdleAllowed : ∀ tcb : TCB,
      (endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty c st).1.getTcb? faulted
          = some tcb →
      tcb.schedContextBinding ≠ .unbound ∨ passiveServerIdleAllowed tcb.ipcState) :
    ipcInvariantFull (faultReplyOnCore replier faulted mi regs c st).1 := by
  cases hTcb : st.getTcb? faulted with
  | none => simpa only [faultReplyOnCore, hTcb] using hInv
  | some tcb =>
      cases hFault : tcb.pendingFault with
      | none => simpa only [faultReplyOnCore, hTcb, hFault] using hInv
      | some tf =>
          have hRep := endpointReplyCrossCoreDispatch_preserves_ipcInvariantFull replier
            faulted IpcMessage.empty c st hInv hObjInv
            (fun t tcb' sc hS => hNoDonationOwnedBy t tcb' sc
              ((SystemState.getTcb?_eq_some_iff st t tcb').mpr hS))
            hAllBudgetsNone hServerIdleAllowed
          have hRepObj := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier
            faulted IpcMessage.empty c st hObjInv
          rcases hStep : endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty c st
            with ⟨stR, res⟩
          rw [hStep] at hRep hRepObj hTargetIdleAllowed
          simp only at hRep hRepObj hTargetIdleAllowed
          cases res with
          | error e => simpa only [faultReplyOnCore, hTcb, hFault, hStep] using hInv
          | ok sgi? =>
              simp only [faultReplyOnCore, hTcb, hFault, hStep, faultReplyApplyOnCore]
              cases hOut : decodeFaultReply tf.fault tf.context mi regs with
              | restart frame =>
                  simpa only [hOut] using
                    applyFaultRestart_preserves_ipcInvariantFull stR faulted frame hRepObj hRep
              | abandon =>
                  simpa only [hOut] using
                    faultAbandonOnCore_preserves_ipcInvariantFull stR faulted
                      (determineTargetCore stR faulted) hRepObj hTargetIdleAllowed hRep

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

end SeLe4n.Kernel
