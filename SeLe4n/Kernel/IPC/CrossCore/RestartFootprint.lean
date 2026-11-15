/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.Restart
import SeLe4n.Kernel.IPC.CrossCore.SuspendFootprint
import SeLe4n.Kernel.Lifecycle.ResumeFootprint

/-!
# The scheduler-domain footprint of the restart (`.tcbResume`)

WS-SX SX4: `restartThreadOnCore` is the resume of an `Inactive` thread, the
suspend's IPC cancel followed by that resume for a thread blocked in an IPC, or
nothing.  Its footprint is the resume's for the first and the last arm, and for
the cancelling arm the suspend's cores joined with the resume's, each read off
the state its stage runs on — the suspend's off the entry state, the resume's off
the state the suspend leaves — exactly as the suspend's own footprint reads each
of its stages off the spine re-run to it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency
open SeLe4n.Kernel.Lifecycle.Suspend

/-- The state the restart's cancelling arm hands its resume, the fault retire
run: `some` exactly on that arm. -/
def restartCancelledState? (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : Option SystemState :=
  match st.getTcb? vtid.val with
  | none => none
  | some tcb =>
    if tcb.threadState == .Inactive then none
    else if tcb.ipcState != .ready then
      match suspendThreadOnCore st vtid executingCore with
      | .ok (st1, _) => some st1
      | .error _ => none
    else none

/-- The cores whose run queue and current slot the restart may write. -/
def restartThreadOnCoreWriteSet (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List CoreId :=
  match restartCancelledState? st vtid executingCore with
  | some st1 => suspendThreadOnCoreWriteSet st vtid executingCore ++
      resumeThreadOnCoreWriteSet (retirePendingFaultForResume st1 vtid.val) vtid executingCore
  | none => resumeThreadOnCoreWriteSet st vtid executingCore

/-- The cores whose replenish queue the restart may write. -/
def restartThreadOnCoreReplenishCores (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List CoreId :=
  match restartCancelledState? st vtid executingCore with
  | some st1 => suspendThreadReplenishCores st vtid executingCore ++
      resumeThreadOnCoreReplenishCores (retirePendingFaultForResume st1 vtid.val) vtid
  | none => resumeThreadOnCoreReplenishCores st vtid

/-- **The live `.tcbResume` arm's scheduler-domain footprint.** -/
def schedLockSet_restartThreadOnCore (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (restartThreadOnCoreWriteSet st vtid executingCore)
    (restartThreadOnCoreReplenishCores st vtid executingCore)

/-- Off the cancelling arm the restart's footprint is the resume's. -/
theorem schedLockSet_restartThreadOnCore_of_none {st : SystemState}
    {vtid : SeLe4n.ValidThreadId} {executingCore : CoreId}
    (h : restartCancelledState? st vtid executingCore = none) :
    schedLockSet_restartThreadOnCore st vtid executingCore =
      schedLockSet_resumeThreadOnCore st vtid executingCore := by
  unfold schedLockSet_restartThreadOnCore restartThreadOnCoreWriteSet
    restartThreadOnCoreReplenishCores schedLockSet_resumeThreadOnCore
  rw [h]

/-- A scheduler-domain footprint is always an accepted lock set. -/
theorem schedFootprintOfCores_ofList?_isSome (runCores replenishCores : List CoreId) :
    ∃ S, LockSet.ofList? (schedFootprintOfCores runCores replenishCores) = some S :=
  ⟨_, dif_pos (schedFootprintOfCores_keys_nodup runCores replenishCores)⟩

end SeLe4n.Kernel
