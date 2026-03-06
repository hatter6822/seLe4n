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
    (!(sampleState.objects[(2 : SeLe4n.ObjId)]? == altState.objects[(2 : SeLe4n.ObjId)]?))

  expect "altState differs from sampleState (current thread changed)"
    (sampleState.scheduler.current ≠ altState.scheduler.current)

  -- Verify public projections of distinct states are equal (non-trivial low-equivalence)
  expect "distinct states: public object projection matches for public observer"
    (publicProjectionSample.objects 1 == publicProjectionAlt.objects 1)

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
    publicProjectionSample.objects oid == publicProjectionAlt.objects oid)
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
      | .ok ((), s₁), .ok ((), s₂) => s₁.objects[(10 : SeLe4n.ObjId)]? == s₂.objects[(10 : SeLe4n.ObjId)]?
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
      |>.withObject 100 (.cnode { guard := 0, radix := 8, slots := (Std.HashMap.ofList [(0, { target := .object 200, rights := [.read, .write], badge := none })]) })
      |>.withObject 101 (.cnode { guard := 0, radix := 8, slots := (Std.HashMap.ofList []) })
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
  -- WS-E5/H-04: Parameterized domain lattice checks (≥3 domains)
  -- =========================================================================

  -- 3-domain linear order: domain 0 → domain 1 → domain 2
  let threeDomain := SeLe4n.Kernel.DomainFlowPolicy.linearOrder

  expect "H-04 linear order: domain 0 flows to domain 1"
    (SeLe4n.Kernel.domainFlowsTo threeDomain ⟨0⟩ ⟨1⟩)

  expect "H-04 linear order: domain 1 flows to domain 2"
    (SeLe4n.Kernel.domainFlowsTo threeDomain ⟨1⟩ ⟨2⟩)

  expect "H-04 linear order: domain 0 flows to domain 2 (transitive)"
    (SeLe4n.Kernel.domainFlowsTo threeDomain ⟨0⟩ ⟨2⟩)

  expect "H-04 linear order: domain 2 cannot flow to domain 0"
    (!(SeLe4n.Kernel.domainFlowsTo threeDomain ⟨2⟩ ⟨0⟩))

  expect "H-04 linear order: domain 2 cannot flow to domain 1"
    (!(SeLe4n.Kernel.domainFlowsTo threeDomain ⟨2⟩ ⟨1⟩))

  expect "H-04 linear order: self-flow (reflexive)"
    (SeLe4n.Kernel.domainFlowsTo threeDomain ⟨1⟩ ⟨1⟩)

  -- Test allowAll policy
  let allPolicy := SeLe4n.Kernel.DomainFlowPolicy.allowAll

  expect "H-04 allowAll: any domain flows to any domain"
    (SeLe4n.Kernel.domainFlowsTo allPolicy ⟨5⟩ ⟨0⟩ &&
     SeLe4n.Kernel.domainFlowsTo allPolicy ⟨0⟩ ⟨99⟩)

  -- Test legacy embedding preserves semantics
  let embeddedPublic := SeLe4n.Kernel.embedLegacyLabel publicLabel
  let embeddedSecret := SeLe4n.Kernel.embedLegacyLabel secretLabel

  expect "H-04 legacy embedding: public maps to domain 0"
    (embeddedPublic.id = 0)

  expect "H-04 legacy embedding: kernelTrusted maps to domain 3"
    (embeddedSecret.id = 3)

  expect "H-04 legacy embedding: public→secret flow preserved under linearOrder"
    (SeLe4n.Kernel.domainFlowsTo SeLe4n.Kernel.DomainFlowPolicy.linearOrder
      embeddedPublic embeddedSecret)

  expect "H-04 legacy embedding: secret→public flow denied under linearOrder"
    (!(SeLe4n.Kernel.domainFlowsTo SeLe4n.Kernel.DomainFlowPolicy.linearOrder
      embeddedSecret embeddedPublic))

  -- Test GenericLabelingContext
  let genericCtx : SeLe4n.Kernel.GenericLabelingContext := {
    policy := SeLe4n.Kernel.DomainFlowPolicy.linearOrder
    objectDomainOf := fun oid => if oid = 1 then ⟨0⟩ else ⟨2⟩
    threadDomainOf := fun tid => if tid = 1 then ⟨0⟩ else ⟨1⟩
    endpointDomainOf := fun _ => ⟨1⟩
    serviceDomainOf := fun _ => ⟨0⟩
  }

  expect "H-04 generic context: thread 1 (domain 0) → endpoint (domain 1)"
    (SeLe4n.Kernel.genericFlowCheck genericCtx (genericCtx.threadDomainOf 1) (genericCtx.endpointDomainOf 10))

  expect "H-04 generic context: thread 2 (domain 1) → endpoint (domain 1) (same domain)"
    (SeLe4n.Kernel.genericFlowCheck genericCtx (genericCtx.threadDomainOf 2) (genericCtx.endpointDomainOf 10))

  expect "H-04 generic context: object 2 (domain 2) cannot flow to service (domain 0)"
    (!(SeLe4n.Kernel.genericFlowCheck genericCtx (genericCtx.objectDomainOf 2) (genericCtx.serviceDomainOf 1)))

  -- Test per-endpoint flow policy
  let customEndpointPolicy : SeLe4n.Kernel.DomainFlowPolicy :=
    { canFlow := fun src dst => src.id = dst.id }  -- same-domain only

  let epPolicy : SeLe4n.Kernel.EndpointFlowPolicy :=
    { endpointPolicy := fun eid => if eid = 10 then some customEndpointPolicy else none }

  expect "H-04 per-endpoint: endpoint 10 has custom policy (same-domain only)"
    (SeLe4n.Kernel.endpointFlowCheck genericCtx epPolicy 10 ⟨1⟩ ⟨1⟩ &&
     !(SeLe4n.Kernel.endpointFlowCheck genericCtx epPolicy 10 ⟨0⟩ ⟨1⟩))

  expect "H-04 per-endpoint: endpoint 20 falls back to global policy"
    (SeLe4n.Kernel.endpointFlowCheck genericCtx epPolicy 20 ⟨0⟩ ⟨1⟩)

  IO.println "WS-E5/H-04 parameterized domain lattice checks passed"

  -- =========================================================================
  -- WS-E5/M-07: Enforcement boundary classification checks
  -- =========================================================================

  expect "M-07 enforcement boundary: 3 policy-gated operations defined"
    ((SeLe4n.Kernel.enforcementBoundary.filter (fun c =>
      match c with | .policyGated _ => true | _ => false)).length == 3)

  expect "M-07 enforcement boundary: capability-only operations defined"
    ((SeLe4n.Kernel.enforcementBoundary.filter (fun c =>
      match c with | .capabilityOnly _ => true | _ => false)).length > 0)

  expect "M-07 enforcement boundary: read-only operations defined"
    ((SeLe4n.Kernel.enforcementBoundary.filter (fun c =>
      match c with | .readOnly _ => true | _ => false)).length > 0)

  expect "M-07 enforcement boundary: total 17 classified operations"
    (SeLe4n.Kernel.enforcementBoundary.length == 17)

  -- Verify enforcement boundary: denied flows produce errors
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
      | .ok ((), s₁), .ok ((), s₂) => s₁.objects[(10 : SeLe4n.ObjId)]? == s₂.objects[(10 : SeLe4n.ObjId)]?
      | .error e₁, .error e₂ => e₁ = e₂
      | _, _ => false)

  IO.println "WS-E5/M-07 enforcement boundary checks passed"
  IO.println "all WS-E5 information-flow maturity checks passed"

  -- =========================================================================
  -- WS-F3: Information-flow completeness — new ObservableState fields
  -- =========================================================================

  -- ---------- activeDomain projection (scheduling transparency) ----------
  -- activeDomain is always visible regardless of observer clearance.
  let publicActiveDomain := publicProjection.activeDomain
  let adminActiveDomain := adminProjection.activeDomain

  expect "WS-F3: activeDomain visible to public observer"
    (publicActiveDomain = sampleState.scheduler.activeDomain)

  expect "WS-F3: activeDomain visible to admin observer"
    (adminActiveDomain = sampleState.scheduler.activeDomain)

  expect "WS-F3: activeDomain consistent across observers"
    (publicActiveDomain = adminActiveDomain)

  -- ---------- IRQ handler projection ----------
  -- Build a state with IRQ handlers pointing to both public and secret objects.
  let irqState :=
    (BootstrapBuilder.empty
      |>.withObject 1 (.endpoint { state := .idle, queue := [], waitingReceiver := none })
      |>.withObject 2 (.notification { state := .active, waitingThreads := [], pendingBadge := some 7 })
      |>.withIrqHandler 0 1   -- IRQ 0 → oid 1 (public object)
      |>.withIrqHandler 1 2   -- IRQ 1 → oid 2 (secret object)
      |>.build)

  let irqPublicProj := SeLe4n.Kernel.projectState sampleLabeling reviewer irqState
  let irqAdminProj := SeLe4n.Kernel.projectState sampleLabeling admin irqState

  -- Public observer sees IRQ 0 → oid 1 (public target)
  expect "WS-F3: public observer sees IRQ handler to public object"
    ((irqPublicProj.irqHandlers 0) = some 1)

  -- Public observer cannot see IRQ 1 → oid 2 (secret target)
  expect "WS-F3: public observer cannot see IRQ handler to secret object"
    ((irqPublicProj.irqHandlers 1).isNone)

  -- Admin sees both IRQ handlers
  expect "WS-F3: admin observer sees IRQ handler to public object"
    ((irqAdminProj.irqHandlers 0) = some 1)

  expect "WS-F3: admin observer sees IRQ handler to secret object"
    ((irqAdminProj.irqHandlers 1) = some 2)

  -- Unmapped IRQ returns none for both observers
  expect "WS-F3: unmapped IRQ returns none for public observer"
    ((irqPublicProj.irqHandlers 99).isNone)

  expect "WS-F3: unmapped IRQ returns none for admin observer"
    ((irqAdminProj.irqHandlers 99).isNone)

  IO.println "WS-F3 IRQ handler projection checks passed"

  -- ---------- Object index projection ----------
  -- objectIndex is auto-built from builder objects list.
  -- sampleState has objects [1, 2], where oid 2 is secret.
  let publicObjIndex := publicProjection.objectIndex
  let adminObjIndex := adminProjection.objectIndex

  -- Public observer sees only oid 1 in the object index
  expect "WS-F3: public object index contains public oid"
    (publicObjIndex.contains 1)

  expect "WS-F3: public object index excludes secret oid"
    (!publicObjIndex.contains 2)

  -- Admin sees both oids in the object index
  expect "WS-F3: admin object index contains public oid"
    (adminObjIndex.contains 1)

  expect "WS-F3: admin object index contains secret oid"
    (adminObjIndex.contains 2)

  IO.println "WS-F3 object index projection checks passed"

  -- ---------- CNode slot filtering (F-22) ----------
  -- Build a CNode with caps targeting both public and secret objects.
  let cnodeState :=
    (BootstrapBuilder.empty
      |>.withObject 1 (.endpoint { state := .idle, queue := [], waitingReceiver := none })  -- public target
      |>.withObject 2 (.notification { state := .idle, waitingThreads := [], pendingBadge := none })  -- secret target
      |>.withObject 50 (.cnode { guard := 0, radix := 8, slots := (Std.HashMap.ofList
          [ (0, { target := .object 1, rights := [.read], badge := none })
          , (1, { target := .object 2, rights := [.read, .write], badge := none })
          , (2, { target := .replyCap 1, rights := [.read], badge := none })
          ]) })
      |>.build)

  -- oid 50 (the CNode) is public so both observers can see it
  let cnodeLabeling : SeLe4n.Kernel.LabelingContext :=
    { objectLabelOf := fun oid => if oid = 2 then secretLabel else publicLabel
      threadLabelOf := fun tid => if tid = 2 then secretLabel else publicLabel
      endpointLabelOf := fun _ => publicLabel
      serviceLabelOf := fun _ => publicLabel }

  let cnodePublicProj := SeLe4n.Kernel.projectState cnodeLabeling reviewer cnodeState
  let cnodeAdminProj := SeLe4n.Kernel.projectState cnodeLabeling admin cnodeState

  -- Public observer sees the CNode but with filtered slots
  match cnodePublicProj.objects 50 with
  | some (.cnode cn) =>
    -- Slot 0 (target: public obj 1) should be present
    expect "WS-F3/F-22: public observer sees cap slot targeting public object"
      (cn.slots.contains 0)
    -- Slot 1 (target: secret obj 2) should be filtered out
    expect "WS-F3/F-22: public observer cannot see cap slot targeting secret object"
      (!cn.slots.contains 1)
    -- Slot 2 (target: replyCap to public thread 1) should be present
    expect "WS-F3/F-22: public observer sees reply cap to public thread"
      (cn.slots.contains 2)
    -- Verify slot count
    expect "WS-F3/F-22: public observer sees exactly 2 of 3 slots"
      (cn.slots.size = 2)
  | _ =>
    throw <| IO.userError "WS-F3/F-22: public observer should see CNode object at oid 50"

  -- Admin observer sees all slots (full clearance)
  match cnodeAdminProj.objects 50 with
  | some (.cnode cn) =>
    expect "WS-F3/F-22: admin observer sees all 3 cap slots"
      (cn.slots.size = 3)
  | _ =>
    throw <| IO.userError "WS-F3/F-22: admin observer should see CNode object at oid 50"

  -- Non-CNode objects pass through unchanged
  match cnodePublicProj.objects 1 with
  | some (.endpoint _) =>
    expect "WS-F3/F-22: non-CNode object passes through unchanged"
      true
  | _ =>
    throw <| IO.userError "WS-F3/F-22: endpoint at oid 1 should be visible to public observer"

  -- CNode slot filtering for .cnodeSlot target variant
  let cnodeSlotState :=
    (BootstrapBuilder.empty
      |>.withObject 1 (.endpoint { state := .idle, queue := [], waitingReceiver := none })  -- public target
      |>.withObject 2 (.notification { state := .idle, waitingThreads := [], pendingBadge := none })  -- secret target
      |>.withObject 60 (.cnode { guard := 0, radix := 8, slots := (Std.HashMap.ofList
          [ (0, { target := .cnodeSlot 1 0, rights := [.read], badge := none })
          , (1, { target := .cnodeSlot 2 0, rights := [.read], badge := none })
          ]) })
      |>.build)

  let cnodeSlotProj := SeLe4n.Kernel.projectState cnodeLabeling reviewer cnodeSlotState
  match cnodeSlotProj.objects 60 with
  | some (.cnode cn) =>
    expect "WS-F3/F-22: cnodeSlot target to public CNode is visible"
      (cn.slots.contains 0)
    expect "WS-F3/F-22: cnodeSlot target to secret CNode is filtered"
      (!cn.slots.contains 1)
    expect "WS-F3/F-22: cnodeSlot variant: exactly 1 of 2 slots visible"
      (cn.slots.size = 1)
  | _ =>
    throw <| IO.userError "WS-F3/F-22: CNode at oid 60 should be visible for cnodeSlot test"

  IO.println "WS-F3/F-22 CNode slot filtering checks passed"

  -- ---------- Full 7-field low-equivalence ----------
  -- Extend the distinct-state comparison to all 7 ObservableState fields.
  let knownIrqs : List SeLe4n.Irq := [0, 1, 2, 3]
  let irqMatch := knownIrqs.all (fun irq =>
    publicProjectionSample.irqHandlers irq = publicProjectionAlt.irqHandlers irq)
  let fullLowEq7 := objectsMatch
    && publicProjectionSample.runnable = publicProjectionAlt.runnable
    && publicProjectionSample.current = publicProjectionAlt.current
    && servicesMatch
    && publicProjectionSample.activeDomain = publicProjectionAlt.activeDomain
    && irqMatch
    && publicProjectionSample.objectIndex = publicProjectionAlt.objectIndex

  expect "WS-F3: full 7-field low-equivalence holds between distinct states"
    fullLowEq7

  IO.println "WS-F3 full 7-field low-equivalence check passed"

  -- ---------- serviceRestartChecked enforcement (WS-F3) ----------
  -- Build a state with a running service for restart testing.
  let restartServiceEntry : ServiceGraphEntry :=
    { identity := { sid := 10, backingObject := 20, owner := 1 }
      status := .running
      dependencies := []
      isolatedFrom := [] }

  let restartState :=
    (BootstrapBuilder.empty
      |>.withObject 20 (.endpoint { state := .idle, queue := [], waitingReceiver := none })
      |>.withService 10 restartServiceEntry
      |>.withService 5 { identity := { sid := 5, backingObject := 25, owner := 1 }
                         status := .running, dependencies := [], isolatedFrom := [] }
      |>.build)

  let allowAll : SeLe4n.Kernel.ServicePolicy := fun _ => true

  -- Same-domain restart (orchestrator sid=5, target sid=10, both public)
  let sameDomainRestartCtx : SeLe4n.Kernel.LabelingContext :=
    { objectLabelOf := fun _ => publicLabel
      threadLabelOf := fun _ => publicLabel
      endpointLabelOf := fun _ => publicLabel
      serviceLabelOf := fun _ => publicLabel }

  let checkedRestart := SeLe4n.Kernel.serviceRestartChecked sameDomainRestartCtx 5 10 allowAll allowAll restartState
  let uncheckedRestart := SeLe4n.Kernel.serviceRestart 10 allowAll allowAll restartState

  expect "WS-F3: same-domain serviceRestartChecked matches unchecked"
    (match checkedRestart, uncheckedRestart with
      | .ok ((), s₁), .ok ((), s₂) =>
          (s₁.services[(10 : ServiceId)]?).map ServiceGraphEntry.status =
            (s₂.services[(10 : ServiceId)]?).map ServiceGraphEntry.status
      | .error e₁, .error e₂ => e₁ = e₂
      | _, _ => false)

  -- Cross-domain restart (secret orchestrator → public service) should be denied
  let crossDomainRestartCtx : SeLe4n.Kernel.LabelingContext :=
    { objectLabelOf := fun _ => publicLabel
      threadLabelOf := fun _ => publicLabel
      endpointLabelOf := fun _ => publicLabel
      serviceLabelOf := fun sid => if sid = 5 then secretLabel else publicLabel }

  let deniedRestart := SeLe4n.Kernel.serviceRestartChecked crossDomainRestartCtx 5 10 allowAll allowAll restartState
  expect "WS-F3: cross-domain serviceRestartChecked returns flowDenied"
    (match deniedRestart with
      | .error .flowDenied => true
      | _ => false)

  IO.println "WS-F3 serviceRestartChecked enforcement checks passed"
  IO.println "all WS-F3 information-flow completeness checks passed"

end SeLe4n.Testing

def main : IO Unit :=
  SeLe4n.Testing.runInformationFlowChecks
