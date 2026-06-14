-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.NotificationBind
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch

/-!
# WS-SM SM6.B — Below-API cross-core bound-signal dispatch

The pure dispatch ops the live `API` `.notificationSignal` arm routes through (the
notification analogue of SM6.A's `endpointCallCrossCoreDispatch{,Checked}`):

* `notificationSignalBoundCrossCoreDispatch` — `notificationSignalBoundOnCore`
  with the executing core derived from the live state
  (`determineExecutingCore st signaler`: the signaller is the current thread on
  its core), so no hardware-core parameter is threaded through the `Kernel`-monad
  chain.
* `notificationSignalBoundCrossCoreDispatchChecked` — the info-flow-checked form,
  gating on `securityFlowsTo signaler→notification` (rejecting `.flowDenied`).

Both surface the optional cross-core `.reschedule` SGI; the live runtime entry
re-derives and fires it from the committed state diff (`computeCrossCoreSgis`),
so no new Rust extern is needed (the SM6.A SGI seam is operation-agnostic).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

/-- WS-SM SM6.B: the unchecked cross-core bound-signal dispatch — the bound-aware
cross-core signal with the executing core read from the live state. -/
def notificationSignalBoundCrossCoreDispatch (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (signaler : SeLe4n.ThreadId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  notificationSignalBoundOnCore notificationId badge (determineExecutingCore st signaler) st

/-- WS-SM SM6.B: the info-flow-checked cross-core bound-signal dispatch.  Gates on
`securityFlowsTo signaler→notification` AND — when the signal would take the
bound-delivery path (`boundDeliveryTarget?` resolves a bound `BlockedOnReceive`
TCB) — on `securityFlowsTo notification→receiver`, because bound delivery writes
the badge **directly into the bound TCB**, a second sink beyond the notification.
Without the receiver gate a policy permitting a high signaler → high notification
but denying flow to a *low* bound TCB would be bypassed (codex review #3): the badge
would leak to the low receiver.  Fail-closed with `.flowDenied` on either denial. -/
def notificationSignalBoundCrossCoreDispatchChecked (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (st : SystemState) : SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  if securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) then
    match boundDeliveryTarget? st notificationId with
    | some (receiver, _) =>
        if securityFlowsTo (ctx.objectLabelOf notificationId) (ctx.threadLabelOf receiver) then
          notificationSignalBoundOnCore notificationId badge (determineExecutingCore st signaler) st
        else
          (st, .error .flowDenied)
    | none =>
        notificationSignalBoundOnCore notificationId badge (determineExecutingCore st signaler) st
  else
    (st, .error .flowDenied)

/-- WS-SM SM6.B: a disallowed signaler→notification flow is rejected before any
state change. -/
theorem notificationSignalBoundCrossCoreDispatchChecked_flow_denied
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = false) :
    notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge st
      = (st, .error .flowDenied) := by
  simp [notificationSignalBoundCrossCoreDispatchChecked, hDeny]

/-- WS-SM SM6.B: even with signaler→notification permitted, a bound delivery whose
receiver the notification may **not** flow to is rejected before any state change —
the badge never reaches a lower bound TCB (codex review #3). -/
theorem notificationSignalBoundCrossCoreDispatchChecked_flow_denied_to_receiver
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (st : SystemState) (receiver : SeLe4n.ThreadId) (ep : SeLe4n.ObjId)
    (hAllow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = true)
    (hTarget : boundDeliveryTarget? st notificationId = some (receiver, ep))
    (hDenyR : securityFlowsTo (ctx.objectLabelOf notificationId) (ctx.threadLabelOf receiver) = false) :
    notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge st
      = (st, .error .flowDenied) := by
  simp [notificationSignalBoundCrossCoreDispatchChecked, hAllow, hTarget, hDenyR]

/-- WS-SM SM6.B: with signaler→notification permitted and no bound-delivery target
(the ordinary signal path), the checked dispatch is exactly the unchecked one. -/
theorem notificationSignalBoundCrossCoreDispatchChecked_flow_allowed_no_delivery
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (st : SystemState)
    (hAllow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = true)
    (hNone : boundDeliveryTarget? st notificationId = none) :
    notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge st
      = notificationSignalBoundCrossCoreDispatch notificationId badge signaler st := by
  simp [notificationSignalBoundCrossCoreDispatchChecked, notificationSignalBoundCrossCoreDispatch,
    hAllow, hNone]

/-- WS-SM SM6.B: when both the signaler→notification and notification→receiver flows
are permitted, the checked bound delivery is exactly the unchecked one. -/
theorem notificationSignalBoundCrossCoreDispatchChecked_flow_allowed_to_receiver
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (st : SystemState) (receiver : SeLe4n.ThreadId) (ep : SeLe4n.ObjId)
    (hAllow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = true)
    (hTarget : boundDeliveryTarget? st notificationId = some (receiver, ep))
    (hAllowR : securityFlowsTo (ctx.objectLabelOf notificationId) (ctx.threadLabelOf receiver) = true) :
    notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge st
      = notificationSignalBoundCrossCoreDispatch notificationId badge signaler st := by
  simp [notificationSignalBoundCrossCoreDispatchChecked, notificationSignalBoundCrossCoreDispatch,
    hAllow, hTarget, hAllowR]

/-- WS-SM SM6.B: the unchecked dispatch preserves `objects.invExt`. -/
theorem notificationSignalBoundCrossCoreDispatch_preserves_objects_invExt
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (signaler : SeLe4n.ThreadId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (notificationSignalBoundCrossCoreDispatch notificationId badge signaler st).1.objects.invExt :=
  notificationSignalBoundOnCore_preserves_objects_invExt notificationId badge
    (determineExecutingCore st signaler) st hObjInv

/-- WS-SM SM6.B: the unchecked dispatch preserves `ipcInvariant`. -/
theorem notificationSignalBoundCrossCoreDispatch_preserves_ipcInvariant
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (signaler : SeLe4n.ThreadId)
    (st : SystemState) (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) :
    ipcInvariant (notificationSignalBoundCrossCoreDispatch notificationId badge signaler st).1 :=
  notificationSignalBoundOnCore_preserves_ipcInvariant notificationId badge
    (determineExecutingCore st signaler) st hInv hObjInv

-- ============================================================================
-- §5  Cross-core notification WAIT dispatch (per-core deschedule)
-- ============================================================================

/-- WS-SM SM6.B: the unchecked cross-core notification-wait dispatch — runs
`notificationWaitOnCore` with the executing core read from the live state
(`determineExecutingCore st waiter`: the waiter is the current thread on its core),
so a `.notificationWait` issued on a *non-boot* core deschedules the blocked caller
on **its own** core rather than the boot core.  The wait analogue of
`notificationSignalBoundCrossCoreDispatch`; a wait surfaces no cross-core SGI (it
pokes no other core), so the result carries only the consumed badge. -/
def notificationWaitCrossCoreDispatch (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (st : SystemState) :
    SystemState × Except KernelError (Option SeLe4n.Badge) :=
  notificationWaitOnCore notificationId waiter (determineExecutingCore st waiter) st

/-- WS-SM SM6.B: the info-flow-checked cross-core notification-wait dispatch — gates
on `securityFlowsTo notification→waiter` (the badge flows from the notification to
the waiter, matching `notificationWaitChecked`), fail-closed with `.flowDenied`. -/
def notificationWaitCrossCoreDispatchChecked (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (st : SystemState) :
    SystemState × Except KernelError (Option SeLe4n.Badge) :=
  if securityFlowsTo (ctx.objectLabelOf notificationId) (ctx.threadLabelOf waiter) then
    notificationWaitOnCore notificationId waiter (determineExecutingCore st waiter) st
  else
    (st, .error .flowDenied)

/-- WS-SM SM6.B: a disallowed wait flow is rejected before any state change. -/
theorem notificationWaitCrossCoreDispatchChecked_flow_denied
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.objectLabelOf notificationId) (ctx.threadLabelOf waiter) = false) :
    notificationWaitCrossCoreDispatchChecked ctx notificationId waiter st
      = (st, .error .flowDenied) := by
  simp [notificationWaitCrossCoreDispatchChecked, hDeny]

/-- WS-SM SM6.B: when the flow is permitted, the checked wait dispatch is exactly the
unchecked one — the guard is a pure precondition. -/
theorem notificationWaitCrossCoreDispatchChecked_flow_allowed
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (st : SystemState)
    (hAllow : securityFlowsTo (ctx.objectLabelOf notificationId) (ctx.threadLabelOf waiter) = true) :
    notificationWaitCrossCoreDispatchChecked ctx notificationId waiter st
      = notificationWaitCrossCoreDispatch notificationId waiter st := by
  simp [notificationWaitCrossCoreDispatchChecked, notificationWaitCrossCoreDispatch, hAllow]

/-- WS-SM SM6.B: the cross-core wait dispatch preserves `objects.invExt`. -/
theorem notificationWaitCrossCoreDispatch_preserves_objects_invExt
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    (notificationWaitCrossCoreDispatch notificationId waiter st).1.objects.invExt :=
  notificationWaitOnCore_preserves_objects_invExt notificationId waiter
    (determineExecutingCore st waiter) st hObjInv

/-- WS-SM SM6.B: the cross-core wait dispatch preserves `ipcInvariant`. -/
theorem notificationWaitCrossCoreDispatch_preserves_ipcInvariant
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (st : SystemState)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) :
    ipcInvariant (notificationWaitCrossCoreDispatch notificationId waiter st).1 :=
  notificationWaitOnCore_preserves_ipcInvariant notificationId waiter
    (determineExecutingCore st waiter) st hInv hObjInv

end SeLe4n.Kernel
