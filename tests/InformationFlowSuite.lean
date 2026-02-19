import SeLe4n
import SeLe4n.Testing.StateBuilder

open SeLe4n.Model

namespace SeLe4n.Testing

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"information-flow check passed [{label}]"
  else
    throw <| IO.userError s!"information-flow check failed [{label}]"

private def publicLabel : SeLe4n.Kernel.SecurityLabel :=
  { confidentiality := .low, integrity := .untrusted }

private def secretLabel : SeLe4n.Kernel.SecurityLabel :=
  { confidentiality := .high, integrity := .trusted }

private def reviewer : SeLe4n.Kernel.IfObserver :=
  { clearance := publicLabel }

private def admin : SeLe4n.Kernel.IfObserver :=
  { clearance := secretLabel }

private def sampleServiceEntry : ServiceGraphEntry :=
  {
    identity := { sid := 1, backingObject := 1, owner := 1 }
    status := .running
    dependencies := []
    isolatedFrom := []
  }

private def sampleState : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject 1 (.endpoint { state := .idle, queue := [], waitingReceiver := none })
    |>.withObject 2 (.notification { state := .active, waitingThreads := [], pendingBadge := some 7 })
    |>.withService 1 sampleServiceEntry
    |>.withRunnable [1, 2]
    |>.withCurrent (some 2)
    |>.build)

private def sampleLabeling : SeLe4n.Kernel.LabelingContext :=
  {
    objectLabelOf := fun oid => if oid = 2 then secretLabel else publicLabel
    threadLabelOf := fun tid => if tid = 2 then secretLabel else publicLabel
    endpointLabelOf := fun _ => publicLabel
    serviceLabelOf := fun sid => if sid = 1 then secretLabel else publicLabel
  }

private def runInformationFlowChecks : IO Unit := do
  expect "security flow is reflexive"
    (SeLe4n.Kernel.securityFlowsTo secretLabel secretLabel)

  expect "public can flow to secret"
    (SeLe4n.Kernel.securityFlowsTo publicLabel secretLabel)

  expect "secret cannot flow to public"
    (!(SeLe4n.Kernel.securityFlowsTo secretLabel publicLabel))

  let publicProjection := SeLe4n.Kernel.projectState sampleLabeling reviewer sampleState
  let adminProjection := SeLe4n.Kernel.projectState sampleLabeling admin sampleState

  expect "public observer cannot see secret object"
    ((publicProjection.objects 2).isNone)

  expect "public observer cannot see secret current thread"
    ((publicProjection.current).isNone)

  expect "admin observer can see secret object"
    ((adminProjection.objects 2).isSome)

  expect "admin observer can see current thread"
    (adminProjection.current = some 2)

  let _baselineEq : SeLe4n.Kernel.lowEquivalent sampleLabeling reviewer sampleState sampleState := by
    rfl
  IO.println "information-flow check passed [lowEquivalent reflexive proof witness]"

  let redactedState : SystemState :=
    { sampleState with services := fun _ => none }

  let serviceBefore := (SeLe4n.Kernel.projectState sampleLabeling reviewer sampleState).services 1
  let serviceAfter := (SeLe4n.Kernel.projectState sampleLabeling reviewer redactedState).services 1

  expect "public observer cannot see secret service status"
    (serviceBefore = none)

  expect "service-only mutation is hidden when service is above observer"
    (decide (serviceBefore = serviceAfter))


end SeLe4n.Testing

def main : IO Unit :=
  SeLe4n.Testing.runInformationFlowChecks
