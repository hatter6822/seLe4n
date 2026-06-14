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

/-- WS-SM SM6.B: the info-flow-checked cross-core bound-signal dispatch — gates on
`securityFlowsTo signaler→notification`, fail-closed with `.flowDenied`. -/
def notificationSignalBoundCrossCoreDispatchChecked (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (st : SystemState) : SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  if securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) then
    notificationSignalBoundOnCore notificationId badge (determineExecutingCore st signaler) st
  else
    (st, .error .flowDenied)

/-- WS-SM SM6.B: a disallowed flow is rejected before any state change. -/
theorem notificationSignalBoundCrossCoreDispatchChecked_flow_denied
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = false) :
    notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge st
      = (st, .error .flowDenied) := by
  simp [notificationSignalBoundCrossCoreDispatchChecked, hDeny]

/-- WS-SM SM6.B: when the flow is permitted, the checked dispatch is exactly the
unchecked bound dispatch — the guard is a pure precondition. -/
theorem notificationSignalBoundCrossCoreDispatchChecked_flow_allowed
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (st : SystemState)
    (hAllow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = true) :
    notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge st
      = notificationSignalBoundCrossCoreDispatch notificationId badge signaler st := by
  simp [notificationSignalBoundCrossCoreDispatchChecked, notificationSignalBoundCrossCoreDispatch, hAllow]

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

end SeLe4n.Kernel
