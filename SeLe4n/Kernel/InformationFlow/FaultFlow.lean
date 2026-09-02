-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-RR RR4.20 — the fault path's information-flow slice.
-- Staged with the cross-core call NI surface it composes
-- (`IPC/CrossCore/EndpointCallNI.lean`); the transitions it covers are
-- production, and this module promotes with that surface.

import SeLe4n.Kernel.IPC.CrossCore.Fault
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallNI

/-!
# WS-RR RR4.20 — fault delivery and the information-flow policy

A fault message is a *kernel-originated* IPC: the kernel decides its content,
its destination and when it is sent, and none of those decisions is a syscall
the faulting thread made.  So the two questions the policy asks of any
transition have to be asked here too, and answered separately:

1. **May this flow happen at all?**  A fault message flows from the faulting
   thread's domain into the handler's, so it goes through the same
   `endpointFlowGate` the `.call` syscall arm uses — and when the gate denies
   it, the delivery does not *fail*: it takes the **fail-closed suspend**.
   That distinction matters.  Returning an error would leave the faulting
   thread runnable at the instruction that faulted, which is the RR4.19
   livelock reintroduced through the policy layer; suspending contains the
   thread whether or not its fault can be reported.  **That arm is not in this
   module**: `faultDeliverOnCoreChecked` is what `Kernel/FaultEntry.lean`
   calls, so it is production, and it lives in `IPC/CrossCore/Fault.lean` §5
   beside the transition it guards.  A gate reachable only from a staged
   module would be a gate the kernel does not apply.

2. **Does the message itself carry anything it should not?**  A fault message
   is a function of the faulting thread's *own* syndrome registers and *own*
   saved register context, and it transfers no capabilities (§2).  So no other
   subject's data — and no authority at all — can ride it across a label
   boundary, whatever the gate decides.

§3 closes the covert-channel direction: a fault involving only non-observable
subjects is invisible to a low observer, on the delivery path and on the
fail-closed path alike.  This module is the half that composes the staged
cross-core call NI surface, and is staged with it.
-/

namespace SeLe4n.Kernel

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §2  RR4.20 — the message carries nothing across the boundary
-- ============================================================================

/-- WS-RR RR4.20: **the fault context reads the faulting thread and nothing
else.**  Two states that agree on the faulting thread's TCB produce the same
fault context, whatever else differs between them — so no other subject's
register content can reach the handler through a fault message. -/
theorem faultContextOfThread_congr (st₁ st₂ : SystemState) (tid : SeLe4n.ThreadId)
    (faultIP spsr : UInt64) (hAgree : st₁.getTcb? tid = st₂.getTcb? tid) :
    faultContextOfThread st₁ tid faultIP spsr = faultContextOfThread st₂ tid faultIP spsr := by
  unfold faultContextOfThread
  rw [hAgree]

/-- WS-RR RR4.20: and therefore so does the message.  The remaining inputs are
the syndrome registers the hardware latched for *this* trap and the handler
capability's own badge — neither is another subject's data. -/
theorem faultMessage_of_thread_congr (st₁ st₂ : SystemState) (tid : SeLe4n.ThreadId)
    (f : Fault) (faultIP spsr : UInt64) (badge : Option SeLe4n.Badge)
    (hAgree : st₁.getTcb? tid = st₂.getTcb? tid) :
    faultMessage f (faultContextOfThread st₁ tid faultIP spsr) badge
      = faultMessage f (faultContextOfThread st₂ tid faultIP spsr) badge := by
  rw [faultContextOfThread_congr st₁ st₂ tid faultIP spsr hAgree]

/-- WS-RR RR4.20 (**no authority crosses**): a fault message transfers no
capabilities and grants none, so the *authority* half of an information flow
is empty on this path whatever the data half does.

This is what makes the gate above a statement about a data flow alone, and it
is not an accident of the current encoder: `faultMessage` fixes `caps := #[]`
and `capsGranted := false` structurally. -/
theorem faultMessage_transfers_no_authority (f : Fault) (fctx : FaultContext)
    (badge : Option SeLe4n.Badge) :
    (faultMessage f fctx badge).caps = #[] ∧
    (faultMessage f fctx badge).capsGranted = false :=
  ⟨rfl, rfl⟩

/-- WS-RR RR4.20: **and the grant bit the Call chain stamps on is inert.**

`endpointCallWithCapsOnCore` overwrites a message's `capsGranted` from the
*endpoint capability's* rights, so a fault delivered through a handler
capability — which must carry `.grant`, or the handler could not reply
(`faultHandlerRights`) — arrives with the bit **set**, not with the `false`
the encoder wrote.

That is not a leak, and this is why: `capsGranted` authorises the installation
of the capabilities the message carries, and a fault message carries none.
Stated over an arbitrary grant bit rather than over the delivered value, so
the guarantee does not depend on which rights a particular deployment's
handler capability happens to hold. -/
theorem faultMessage_grant_is_inert (f : Fault) (fctx : FaultContext)
    (badge : Option SeLe4n.Badge) (granted : Bool) :
    ({ faultMessage f fctx badge with capsGranted := granted } : IpcMessage).caps = #[] :=
  rfl

-- ============================================================================
-- §3  RR4.20 — a high fault is invisible to a low observer
-- ============================================================================

/-- Recording a fault writes one high TCB's `pendingFault`, so a low observer
sees nothing. -/
theorem recordPendingFault_preserves_projection (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (tid : SeLe4n.ThreadId)
    (tf : ThreadFault)
    (hHighObj : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (recordPendingFault st tid tf)
      = projectState ctx observer st := by
  simp only [recordPendingFault]
  cases hT : st.getTcb? tid with
  | none => rfl
  | some tcb =>
      simp only
      have hProj := projectObjects_insert_high ctx observer st
        ({ st with objects := st.objects.insert tid.toObjId (KernelObject.tcb { tcb with pendingFault := some tf }) } : SystemState)
        tid (KernelObject.tcb { tcb with pendingFault := some tf }) rfl hHighObj hObjInv
      -- `congr 1` discharges the twelve unchanged projections by `rfl` and the
      -- object projection from `hProj` (which it finds by `assumption`).
      simp only [projectState]
      congr 1

/-- WS-RR RR4.20: **the fail-closed suspend of a high thread is invisible.**

Both halves are high writes: the deschedule removes a non-observable thread
from a run queue, and the `.Inactive` store lands on a non-observable TCB.  So
a low observer cannot detect that some other domain's thread faulted and was
contained — which is the covert channel a fault path most obviously risks,
since faults are frequent and their timing is attacker-influenced. -/
theorem faultSuspendOnCore_preserves_projection (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hHigh : threadObservable ctx observer tid = false)
    (hHighObj : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (faultSuspendOnCore st tid c)
      = projectState ctx observer st := by
  simp only [faultSuspendOnCore]
  cases hT : (removeRunnableOnCore st tid c).getTcb? tid with
  | none =>
      simp only
      exact removeRunnableOnCore_preserves_projection ctx observer st tid c hHigh
  | some tcb =>
      simp only
      have hProj := projectObjects_insert_high ctx observer (removeRunnableOnCore st tid c)
        ({ removeRunnableOnCore st tid c with objects := (removeRunnableOnCore st tid c).objects.insert tid.toObjId (KernelObject.tcb { tcb with threadState := .Inactive }) } : SystemState)
        tid (KernelObject.tcb { tcb with threadState := .Inactive }) rfl hHighObj hObjInv
      rw [← removeRunnableOnCore_preserves_projection ctx observer st tid c hHigh]
      -- `congr 1` discharges the twelve unchanged projections by `rfl` and the
      -- object projection from `hProj` (which it finds by `assumption`).
      simp only [projectState]
      congr 1

/-- WS-RR RR4.20 (**the fail-closed path is silent**): a fault that cannot be
delivered — no handler, an unresolvable one, or a flow the policy forbids —
changes nothing a low observer can see. -/
theorem faultDeliverOnCoreChecked_denied_preserves_projection (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault)
    (fctx : FaultContext) (c : CoreId) (tgt : FaultHandlerTarget)
    (hRes : resolveFaultHandler st tid = .ok tgt)
    (hDeny : endpointFlowGate ctx tgt.endpoint (ctx.threadLabelOf tid)
      (ctx.endpointLabelOf tgt.endpoint) = false)
    (hHigh : threadObservable ctx observer tid = false)
    (hHighObj : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (faultDeliverOnCoreChecked ctx st tid f fctx c).1
      = projectState ctx observer st := by
  have hSuspObj : (faultSuspendOnCore st tid c).objects.invExt := by
    simp only [faultSuspendOnCore]
    cases (removeRunnableOnCore st tid c).getTcb? tid with
    | none => exact hObjInv
    | some tcb =>
        exact RobinHood.RHTable.insert_preserves_invExt
          (removeRunnableOnCore st tid c).objects tid.toObjId _ hObjInv
  rw [faultDeliverOnCoreChecked_flow_denied ctx st tid f fctx c tgt hRes hDeny]
  simp only
  rw [recordPendingFault_preserves_projection ctx observer _ tid _ hHighObj hSuspObj]
  exact faultSuspendOnCore_preserves_projection ctx observer st tid c hHigh hHighObj hObjInv

end SeLe4n.Kernel
