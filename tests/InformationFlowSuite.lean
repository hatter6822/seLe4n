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

/-- A public-level service entry visible to the low observer. -/
private def publicServiceEntry : ServiceGraphEntry :=
  {
    identity := { sid := 2, backingObject := 3, owner := 3 }
    status := .running
    dependencies := []
    isolatedFrom := []
  }

private def sampleState : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject 1 (.endpoint { state := .idle, queue := [], waitingReceiver := none })
    |>.withObject 2 (.notification { state := .active, waitingThreads := [], pendingBadge := some 7 })
    |>.withService 1 sampleServiceEntry
    |>.withService 2 publicServiceEntry
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

/-- A second state that differs from sampleState only in secret (high-domain) components.

This state changes the secret object (oid=2) and the scheduler current thread while
keeping all public-level objects identical. For a public observer, this state should
project identically to sampleState because the differing components are all invisible.

Key differences from sampleState:
- oid=2 (secret): notification state is .idle with no badge (vs .active with badge=7)
- current thread: none (vs some tid=2, which is secret and projected to none anyway) -/
private def altState : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject 1 (.endpoint { state := .idle, queue := [], waitingReceiver := none })
    -- Secret object differs: different notification state and no pending badge
    |>.withObject 2 (.notification { state := .idle, waitingThreads := [], pendingBadge := none })
    |>.withService 1 sampleServiceEntry
    |>.withService 2 publicServiceEntry
    |>.withRunnable [1, 2]
    -- Current thread differs: none (vs some tid=2 in sampleState).
    -- Both project to none for the public observer since tid=2 is secret.
    |>.withCurrent none
    |>.build)

private def runInformationFlowChecks : IO Unit := do
  -- === Policy relation checks ===
  expect "security flow is reflexive"
    (SeLe4n.Kernel.securityFlowsTo secretLabel secretLabel)

  expect "public can flow to secret"
    (SeLe4n.Kernel.securityFlowsTo publicLabel secretLabel)

  expect "secret cannot flow to public"
    (!(SeLe4n.Kernel.securityFlowsTo secretLabel publicLabel))

  -- === Object projection checks ===
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

  -- === F-04 fix: Replace tautological lowEquivalent reflexivity with distinct-state comparison ===
  -- Compare sampleState and altState: they differ in secret components (oid=2, current=tid2)
  -- but should project identically for a public observer because those components are invisible.
  let publicProjectionSample := SeLe4n.Kernel.projectState sampleLabeling reviewer sampleState
  let publicProjectionAlt := SeLe4n.Kernel.projectState sampleLabeling reviewer altState

  -- Verify the two states ARE actually different (so this isn't a tautological comparison)
  expect "altState differs from sampleState (secret object changed)"
    (sampleState.objects 2 ≠ altState.objects 2)

  expect "altState differs from sampleState (current thread changed)"
    (sampleState.scheduler.current ≠ altState.scheduler.current)

  -- Verify public projections of distinct states are equal (non-trivial low-equivalence)
  expect "distinct states: public object projection matches for public observer"
    (publicProjectionSample.objects 1 = publicProjectionAlt.objects 1)

  expect "distinct states: secret objects both hidden for public observer"
    ((publicProjectionSample.objects 2).isNone && (publicProjectionAlt.objects 2).isNone)

  expect "distinct states: public runnable queues match"
    (publicProjectionSample.runnable = publicProjectionAlt.runnable)

  -- The key non-tautological check: current thread is secret in both states,
  -- so both project to none despite having different actual current threads
  expect "distinct states: current thread hidden for public observer despite different actual values"
    (publicProjectionSample.current = none && publicProjectionAlt.current = none)

  -- Full structural low-equivalence check across distinct states.
  -- Function-level equality is not decidable at runtime, so we check point-wise
  -- on all object IDs and service IDs present in the test fixtures.
  let knownOids : List SeLe4n.ObjId := [1, 2]
  let knownSids : List ServiceId := [1, 2]
  let objectsMatch := knownOids.all (fun oid =>
    publicProjectionSample.objects oid = publicProjectionAlt.objects oid)
  let servicesMatch := knownSids.all (fun sid =>
    publicProjectionSample.services sid = publicProjectionAlt.services sid)
  let fullLowEq := objectsMatch
    && publicProjectionSample.runnable = publicProjectionAlt.runnable
    && publicProjectionSample.current = publicProjectionAlt.current
    && servicesMatch
  expect "full low-equivalence holds between distinct states for public observer"
    fullLowEq

  IO.println "information-flow check passed [lowEquivalent distinct-state witness (replaces reflexive tautology)]"

  -- === F-04 fix: Service projection with visible service below observer ===
  -- Service 2 has publicLabel in sampleLabeling, so it IS visible to the reviewer (public observer).
  -- This tests that projectServiceStatus returns meaningful data (not always none).
  let publicServiceProjection := SeLe4n.Kernel.projectServiceStatus sampleLabeling reviewer sampleState

  expect "public observer CAN see public service status"
    ((publicServiceProjection 2).isSome)

  match publicServiceProjection 2 with
  | some status =>
      expect "public service status is running"
        (status = .running)
  | none =>
      throw <| IO.userError "information-flow check failed [public service should be visible to public observer]"

  -- Secret service (sid=1) should still be hidden from public observer
  expect "public observer cannot see secret service status"
    ((publicServiceProjection 1).isNone)

  -- === F-04 fix: Explicit projectServiceStatus coverage ===
  -- Verify projectServiceStatus returns correct status for admin observer on secret service
  let adminServiceProjection := SeLe4n.Kernel.projectServiceStatus sampleLabeling admin sampleState
  expect "admin observer can see secret service status"
    ((adminServiceProjection 1).isSome)

  match adminServiceProjection 1 with
  | some status =>
      expect "secret service status is running for admin"
        (status = .running)
  | none =>
      throw <| IO.userError "information-flow check failed [admin should see secret service status]"

  -- Admin can also see public service
  expect "admin observer can see public service status"
    ((adminServiceProjection 2).isSome)

  -- === F-04 fix: Observer discrimination test ===
  -- High-clearance observer (admin) sees MORE than low-clearance observer (reviewer) on the same state.
  let publicVisibleObjects := [1, 2].filter (fun oid => (publicProjection.objects oid).isSome)
  let adminVisibleObjects := [1, 2].filter (fun oid => (adminProjection.objects oid).isSome)

  expect "admin sees more objects than public observer"
    (adminVisibleObjects.length > publicVisibleObjects.length)

  -- Admin sees secret object that public cannot
  expect "admin sees oid=2 that public cannot"
    ((adminProjection.objects 2).isSome && (publicProjection.objects 2).isNone)

  -- Admin sees current thread that public cannot
  expect "admin sees current thread that public cannot"
    (adminProjection.current.isSome && publicProjection.current.isNone)

  -- Admin sees secret service that public cannot
  let adminSvc1 := (SeLe4n.Kernel.projectServiceStatus sampleLabeling admin sampleState) 1
  let publicSvc1 := (SeLe4n.Kernel.projectServiceStatus sampleLabeling reviewer sampleState) 1
  expect "admin sees secret service that public cannot"
    (adminSvc1.isSome && publicSvc1.isNone)

  -- Both see public service (no discrimination on public data)
  let adminSvc2 := (SeLe4n.Kernel.projectServiceStatus sampleLabeling admin sampleState) 2
  let publicSvc2 := (SeLe4n.Kernel.projectServiceStatus sampleLabeling reviewer sampleState) 2
  expect "both observers see public service"
    (adminSvc2.isSome && publicSvc2.isSome)

  -- === WS-D2 enforcement boundary checks (F-02) ===

  -- endpointSendChecked: public sender to public endpoint should succeed (same-domain flow)
  let publicEndpointState :=
    (BootstrapBuilder.empty
      |>.withObject 10 (.endpoint { state := .idle, queue := [], waitingReceiver := none })
      |>.withRunnable [1]
      |>.withCurrent (some 1)
      |>.build)

  let publicCtx : SeLe4n.Kernel.LabelingContext :=
    { objectLabelOf := fun _ => publicLabel
      threadLabelOf := fun _ => publicLabel
      endpointLabelOf := fun _ => publicLabel
      serviceLabelOf := fun _ => publicLabel }

  -- Same-domain send should be allowed (same result as unchecked)
  let checkedResult := SeLe4n.Kernel.endpointSendChecked publicCtx 10 1 publicEndpointState
  let uncheckedResult := SeLe4n.Kernel.endpointSend 10 1 publicEndpointState
  expect "same-domain endpointSendChecked equals unchecked send"
    (match checkedResult, uncheckedResult with
      | .ok ((), s₁), .ok ((), s₂) => s₁.objects 10 = s₂.objects 10
      | .error e₁, .error e₂ => e₁ = e₂
      | _, _ => false)

  -- Cross-domain send (secret sender → public endpoint) should be denied
  let secretSenderCtx : SeLe4n.Kernel.LabelingContext :=
    { objectLabelOf := fun _ => publicLabel
      threadLabelOf := fun tid => if tid = 1 then secretLabel else publicLabel
      endpointLabelOf := fun _ => publicLabel
      serviceLabelOf := fun _ => publicLabel }

  let deniedResult := SeLe4n.Kernel.endpointSendChecked secretSenderCtx 10 1 publicEndpointState
  expect "secret-to-public endpointSendChecked returns flowDenied"
    (match deniedResult with
      | .error .flowDenied => true
      | _ => false)

  -- cspaceMintChecked: same-domain mint should be allowed
  let mintState :=
    (BootstrapBuilder.empty
      |>.withObject 100 (.cnode { guard := 0, radix := 8, slots := [(0, { target := .object 200, rights := [.read, .write], badge := none })] })
      |>.withObject 101 (.cnode { guard := 0, radix := 8, slots := [] })
      |>.build)

  let sameDomainMintCtx : SeLe4n.Kernel.LabelingContext :=
    { objectLabelOf := fun _ => publicLabel
      threadLabelOf := fun _ => publicLabel
      endpointLabelOf := fun _ => publicLabel
      serviceLabelOf := fun _ => publicLabel }

  let srcAddr : SeLe4n.Kernel.CSpaceAddr := { cnode := 100, slot := 0 }
  let dstAddr : SeLe4n.Kernel.CSpaceAddr := { cnode := 101, slot := 0 }

  let checkedMint := SeLe4n.Kernel.cspaceMintChecked sameDomainMintCtx srcAddr dstAddr [.read] none mintState
  let uncheckedMint := SeLe4n.Kernel.cspaceMint srcAddr dstAddr [.read] none mintState
  expect "same-domain cspaceMintChecked matches unchecked mint"
    (match checkedMint, uncheckedMint with
      | .ok _, .ok _ => true
      | .error e₁, .error e₂ => e₁ = e₂
      | _, _ => false)

  -- Cross-domain mint should be denied
  let crossDomainMintCtx : SeLe4n.Kernel.LabelingContext :=
    { objectLabelOf := fun oid => if oid = 100 then secretLabel else publicLabel
      threadLabelOf := fun _ => publicLabel
      endpointLabelOf := fun _ => publicLabel
      serviceLabelOf := fun _ => publicLabel }

  let deniedMint := SeLe4n.Kernel.cspaceMintChecked crossDomainMintCtx srcAddr dstAddr [.read] none mintState
  expect "secret-to-public cspaceMintChecked returns flowDenied"
    (match deniedMint with
      | .error .flowDenied => true
      | _ => false)

  IO.println "information-flow enforcement boundary checks passed [WS-D2 F-02]"

  -- =========================================================================
  -- WS-E5/H-04: N-level security domain lattice checks (≥3 domains)
  -- =========================================================================

  -- Three-domain linear lattice: 0=public, 1=internal, 2=secret
  let d0 := SeLe4n.Kernel.SecurityDomainN.ofLevel 0  -- public
  let d1 := SeLe4n.Kernel.SecurityDomainN.ofLevel 1  -- internal
  let d2 := SeLe4n.Kernel.SecurityDomainN.ofLevel 2  -- secret

  expect "N-domain: reflexive flow (public→public)"
    (SeLe4n.Kernel.SecurityDomainN.flowsTo d0 d0)

  expect "N-domain: reflexive flow (internal→internal)"
    (SeLe4n.Kernel.SecurityDomainN.flowsTo d1 d1)

  expect "N-domain: reflexive flow (secret→secret)"
    (SeLe4n.Kernel.SecurityDomainN.flowsTo d2 d2)

  expect "N-domain: public→internal allowed"
    (SeLe4n.Kernel.SecurityDomainN.flowsTo d0 d1)

  expect "N-domain: public→secret allowed"
    (SeLe4n.Kernel.SecurityDomainN.flowsTo d0 d2)

  expect "N-domain: internal→secret allowed"
    (SeLe4n.Kernel.SecurityDomainN.flowsTo d1 d2)

  expect "N-domain: secret→public denied"
    (!(SeLe4n.Kernel.SecurityDomainN.flowsTo d2 d0))

  expect "N-domain: secret→internal denied"
    (!(SeLe4n.Kernel.SecurityDomainN.flowsTo d2 d1))

  expect "N-domain: internal→public denied"
    (!(SeLe4n.Kernel.SecurityDomainN.flowsTo d1 d0))

  -- Verify transitivity: public→internal→secret
  expect "N-domain: transitivity public→internal→secret"
    (SeLe4n.Kernel.SecurityDomainN.flowsTo d0 d1 &&
     SeLe4n.Kernel.SecurityDomainN.flowsTo d1 d2 &&
     SeLe4n.Kernel.SecurityDomainN.flowsTo d0 d2)

  -- Generic SecurityLattice interface checks
  expect "generic lattice: SecurityLabel flowsTo is reflexive"
    (SeLe4n.Kernel.genericFlowsTo secretLabel secretLabel)

  expect "generic lattice: SecurityDomainN flowsTo is reflexive"
    (SeLe4n.Kernel.genericFlowsTo d1 d1)

  expect "generic lattice: SecurityDomainN allows upward flow"
    (SeLe4n.Kernel.genericFlowsTo d0 d2)

  expect "generic lattice: SecurityDomainN denies downward flow"
    (!(SeLe4n.Kernel.genericFlowsTo d2 d0))

  IO.println "WS-E5/H-04 three-domain lattice checks passed"

  -- =========================================================================
  -- WS-E5/H-04: Per-endpoint flow policy checks
  -- =========================================================================

  -- Default policy: defers to label-based flow
  let defaultPctx : SeLe4n.Kernel.PolicyContext :=
    { labels := publicCtx
      endpointPolicy := fun _ => .useDefault }

  let defaultPolicyResult := SeLe4n.Kernel.resolveEndpointFlow
    defaultPctx publicLabel publicLabel 10
  expect "per-endpoint: useDefault with same-domain allows flow"
    defaultPolicyResult

  -- permitAlways overrides labels: secret→public allowed
  let permitPctx : SeLe4n.Kernel.PolicyContext :=
    { labels := secretSenderCtx
      endpointPolicy := fun _ => .permitAlways }

  let permitResult := SeLe4n.Kernel.resolveEndpointFlow
    permitPctx secretLabel publicLabel 10
  expect "per-endpoint: permitAlways overrides denial"
    permitResult

  -- denyAlways overrides labels: same-domain denied
  let denyPctx : SeLe4n.Kernel.PolicyContext :=
    { labels := publicCtx
      endpointPolicy := fun _ => .denyAlways }

  let denyResult := SeLe4n.Kernel.resolveEndpointFlow
    denyPctx publicLabel publicLabel 10
  expect "per-endpoint: denyAlways overrides same-domain"
    (!denyResult)

  -- Mixed policy: endpoint 10 has permitAlways, endpoint 20 uses default
  let mixedPctx : SeLe4n.Kernel.PolicyContext :=
    { labels := secretSenderCtx
      endpointPolicy := fun eid => if eid = 10 then .permitAlways else .useDefault }

  expect "per-endpoint: mixed policy permits endpoint 10"
    (SeLe4n.Kernel.resolveEndpointFlow mixedPctx secretLabel publicLabel 10)

  expect "per-endpoint: mixed policy denies endpoint 20 (secret→public)"
    (!(SeLe4n.Kernel.resolveEndpointFlow mixedPctx secretLabel publicLabel 20))

  -- Policy-checked send with per-endpoint policy
  let permitSendResult := SeLe4n.Kernel.endpointSendPolicyChecked
    permitPctx 10 1 publicEndpointState
  expect "per-endpoint: permitAlways send succeeds even for cross-domain"
    (match permitSendResult with
      | .ok _ => true
      | .error _ => false)

  let denySendResult := SeLe4n.Kernel.endpointSendPolicyChecked
    denyPctx 10 1 publicEndpointState
  expect "per-endpoint: denyAlways send returns flowDenied"
    (match denySendResult with
      | .error .flowDenied => true
      | _ => false)

  IO.println "WS-E5/H-04 per-endpoint flow policy checks passed"

  -- =========================================================================
  -- WS-E5/M-07: Enforcement boundary classification checks
  -- =========================================================================

  -- Verify that enforcement boundary soundness: denied flows produce errors
  let deniedSendResult := SeLe4n.Kernel.endpointSendChecked secretSenderCtx 10 1 publicEndpointState
  expect "M-07: enforcement boundary blocks cross-domain endpointSend"
    (match deniedSendResult with
      | .error .flowDenied => true
      | _ => false)

  -- Verify that same-domain operations pass through unchecked
  let allowedSendResult := SeLe4n.Kernel.endpointSendChecked publicCtx 10 1 publicEndpointState
  let uncheckedSendResult := SeLe4n.Kernel.endpointSend 10 1 publicEndpointState
  expect "M-07: same-domain endpointSendChecked matches unchecked"
    (match allowedSendResult, uncheckedSendResult with
      | .ok ((), s₁), .ok ((), s₂) => s₁.objects 10 = s₂.objects 10
      | .error e₁, .error e₂ => e₁ = e₂
      | _, _ => false)

  IO.println "WS-E5/M-07 enforcement boundary classification checks passed"
  IO.println "all WS-E5 information-flow maturity checks passed"

end SeLe4n.Testing

def main : IO Unit :=
  SeLe4n.Testing.runInformationFlowChecks
