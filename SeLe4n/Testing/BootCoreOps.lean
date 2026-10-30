/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n
import SeLe4n.Kernel.Architecture.ExceptionModel

/-!
# The live scheduler operations on the boot core, for the suites

WS-ZA ZA4.5: the single-core reference operations (`schedule`, `timerTick`,
`handleYield`, `switchDomain`, `scheduleDomain`, `chooseThread`) write the run
queue only through its proof-only ghost, so they have no compiled code.  The
suites and the main trace run the kernel's live per-core operations on the boot
core instead.  Each is given here in the `Kernel` shape the reference operation
had, so a scenario reads the same; the reschedule SGIs a tick reports are
dropped, as a single-core scenario has no other core to deliver them to.
-/

namespace SeLe4n.Testing

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Kernel.SchedContext.PriorityManagement
open SeLe4n.Kernel.Concurrency (bootCoreId)

/-- `scheduleEffectiveOnCore` on the boot core. -/
def bootSchedule : Kernel Unit := fun st =>
  (scheduleEffectiveOnCore st bootCoreId).map ((), ·)

/-- `timerTickOnCore` on the boot core (total); the reschedule flags it raises
stay in the state. -/
def bootTimerTick : Kernel Unit := fun st =>
  .ok ((), timerTickOnCore st bootCoreId)

/-- `yieldOnCore` on the boot core. -/
def bootYield : Kernel Unit := fun st =>
  (yieldOnCore st bootCoreId).map ((), ·)

/-- `switchDomainOnCore` on the boot core. -/
def bootSwitchDomain : Kernel Unit := fun st =>
  (switchDomainOnCore st bootCoreId).map ((), ·)

/-- `scheduleDomainOnCore` on the boot core. -/
def bootScheduleDomain : Kernel Unit := fun st =>
  (scheduleDomainOnCore st bootCoreId).map ((), ·)

/-- `chooseThreadEffectiveOnCore` on the boot core; the state is unchanged. -/
def bootChooseThread : Kernel (Option SeLe4n.ThreadId) := fun st =>
  (chooseThreadEffectiveOnCore st bootCoreId).map (·, st)

/-- `suspendThreadOnCore` on the boot core; its reschedule SGI is dropped. -/
def bootSuspendThread (st : SystemState) (vtid : SeLe4n.ValidThreadId) :
    Except KernelError SystemState :=
  (suspendThreadOnCore st vtid bootCoreId).map (·.1)

/-- `resumeThreadOnCore` on the boot core; its reschedule SGI is dropped. -/
def bootResumeThread (st : SystemState) (vtid : SeLe4n.ValidThreadId) :
    Except KernelError SystemState :=
  (resumeThreadOnCore st vtid bootCoreId).map (·.1)

/-- `setPriorityOnCore` on the boot core; its reschedule SGI is dropped. -/
def bootSetPriority (st : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (newPriority : SeLe4n.Priority) : Except KernelError SystemState :=
  (setPriorityOnCore st vCallerTid vTargetTid newPriority bootCoreId).map (·.1)

/-- `setMCPriorityOnCore` on the boot core; its reschedule SGI is dropped. -/
def bootSetMCPriority (st : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (newMCP : SeLe4n.Priority) : Except KernelError SystemState :=
  (setMCPriorityOnCore st vCallerTid vTargetTid newMCP bootCoreId).map (·.1)

/-- `interruptDispatchSequence` with the boot core's live tick. -/
def bootInterruptDispatchSequence (st : SystemState) (rawIntId : Nat) :
    Except KernelError (Unit × SystemState) :=
  interruptDispatchSequenceWith bootTimerTick st rawIntId

/-- `dispatchException` with the boot core's live tick. -/
def bootDispatchException (etype : ExceptionType) (ectx : ExceptionContext)
    (rawIntId : Nat := 0) (st : SystemState)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId := bootCoreId) :
    Except KernelError
      (Option (SeLe4n.Kernel.Concurrency.CoreId × SeLe4n.Kernel.Concurrency.SgiKind) × SystemState) :=
  dispatchExceptionWith bootTimerTick etype ectx rawIntId st executingCore

/-- `scheduleChecked` in front of the boot core's live schedule. -/
def bootScheduleChecked : Kernel Unit := withOutgoingContextChecked bootSchedule

/-- `handleYieldChecked` in front of the boot core's live yield. -/
def bootYieldChecked : Kernel Unit := withOutgoingContextChecked bootYield

/-- `timerTickChecked` in front of the boot core's live tick. -/
def bootTimerTickChecked : Kernel Unit := withOutgoingContextChecked bootTimerTick

/-- `switchDomainChecked` in front of the boot core's live domain switch. -/
def bootSwitchDomainChecked : Kernel Unit := withOutgoingContextChecked bootSwitchDomain

end SeLe4n.Testing
