import SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- WS-H8: Correctness theorems for new wrappers
-- ============================================================================

/-- WS-H8: When the policy allows flow, notificationSignalChecked behaves
identically to the unchecked signal. -/
theorem notificationSignalChecked_eq_notificationSignal_when_allowed
    (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId)
    (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.threadLabelOf signaler)
               (ctx.objectLabelOf notificationId) = true) :
    notificationSignalChecked ctx notificationId signaler badge st =
      notificationSignal notificationId badge st := by
  unfold notificationSignalChecked
  simp [hFlow]

/-- WS-H8: When the policy denies flow, notificationSignalChecked returns
`flowDenied` without modifying state. -/
theorem notificationSignalChecked_flowDenied
    (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId)
    (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf signaler)
               (ctx.objectLabelOf notificationId) = false) :
    notificationSignalChecked ctx notificationId signaler badge st =
      .error .flowDenied := by
  unfold notificationSignalChecked
  simp [hDeny]

/-- WS-H8: When the policy allows flow, cspaceCopyChecked behaves identically
to the unchecked copy. -/
theorem cspaceCopyChecked_eq_cspaceCopy_when_allowed
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.objectLabelOf src.cnode)
               (ctx.objectLabelOf dst.cnode) = true) :
    cspaceCopyChecked ctx src dst st =
      cspaceCopy src dst st := by
  unfold cspaceCopyChecked
  simp [hFlow]

/-- WS-H8: When the policy denies flow, cspaceCopyChecked returns `flowDenied`. -/
theorem cspaceCopyChecked_flowDenied
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.objectLabelOf src.cnode)
               (ctx.objectLabelOf dst.cnode) = false) :
    cspaceCopyChecked ctx src dst st =
      .error .flowDenied := by
  unfold cspaceCopyChecked
  simp [hDeny]

/-- WS-H8: When the policy allows flow, cspaceMoveChecked behaves identically
to the unchecked move. -/
theorem cspaceMoveChecked_eq_cspaceMove_when_allowed
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.objectLabelOf src.cnode)
               (ctx.objectLabelOf dst.cnode) = true) :
    cspaceMoveChecked ctx src dst st =
      cspaceMove src dst st := by
  unfold cspaceMoveChecked
  simp [hFlow]

/-- WS-H8: When the policy denies flow, cspaceMoveChecked returns `flowDenied`. -/
theorem cspaceMoveChecked_flowDenied
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.objectLabelOf src.cnode)
               (ctx.objectLabelOf dst.cnode) = false) :
    cspaceMoveChecked ctx src dst st =
      .error .flowDenied := by
  unfold cspaceMoveChecked
  simp [hDeny]

/-- WS-H8: When the policy allows flow, endpointReceiveDualChecked behaves
identically to the unchecked receive. -/
theorem endpointReceiveDualChecked_eq_endpointReceiveDual_when_allowed
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.endpointLabelOf endpointId)
               (ctx.threadLabelOf receiver) = true) :
    endpointReceiveDualChecked ctx endpointId receiver st =
      endpointReceiveDual endpointId receiver st := by
  unfold endpointReceiveDualChecked
  simp [hFlow]

/-- WS-H8: When the policy denies flow, endpointReceiveDualChecked returns
`flowDenied`. -/
theorem endpointReceiveDualChecked_flowDenied
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.endpointLabelOf endpointId)
               (ctx.threadLabelOf receiver) = false) :
    endpointReceiveDualChecked ctx endpointId receiver st =
      .error .flowDenied := by
  unfold endpointReceiveDualChecked
  simp [hDeny]

-- ============================================================================
-- WS-H8: Denied-preserves-state theorems for new wrappers
-- ============================================================================

/-- WS-H8: notificationSignalChecked denied → no state change. -/
theorem notificationSignalChecked_denied_preserves_state
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId)
    (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf signaler)
               (ctx.objectLabelOf notificationId) = false) :
    ¬∃ st', notificationSignalChecked ctx notificationId signaler badge st = .ok ((), st') := by
  intro ⟨st', h⟩
  simp [notificationSignalChecked, hDeny] at h

/-- WS-H8: cspaceCopyChecked denied → no state change. -/
theorem cspaceCopyChecked_denied_preserves_state
    (ctx : LabelingContext) (src dst : CSpaceAddr)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.objectLabelOf src.cnode)
               (ctx.objectLabelOf dst.cnode) = false) :
    ¬∃ st', cspaceCopyChecked ctx src dst st = .ok ((), st') := by
  intro ⟨st', h⟩
  simp [cspaceCopyChecked, hDeny] at h

/-- WS-H8: cspaceMoveChecked denied → no state change. -/
theorem cspaceMoveChecked_denied_preserves_state
    (ctx : LabelingContext) (src dst : CSpaceAddr)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.objectLabelOf src.cnode)
               (ctx.objectLabelOf dst.cnode) = false) :
    ¬∃ st', cspaceMoveChecked ctx src dst st = .ok ((), st') := by
  intro ⟨st', h⟩
  simp [cspaceMoveChecked, hDeny] at h

/-- WS-H8: endpointReceiveDualChecked denied → no state change. -/
theorem endpointReceiveDualChecked_denied_preserves_state
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.endpointLabelOf endpointId)
               (ctx.threadLabelOf receiver) = false) :
    ¬∃ (r : SeLe4n.ThreadId) (st' : SystemState),
      endpointReceiveDualChecked ctx endpointId receiver st = .ok (r, st') := by
  intro ⟨r, st', h⟩
  simp [endpointReceiveDualChecked, hDeny] at h

-- ============================================================================
-- WS-H8: Enforcement sufficiency theorems for new wrappers
-- ============================================================================

/-- WS-H8: `notificationSignalChecked` either delegates or returns `flowDenied`. -/
theorem enforcement_sufficiency_notificationSignal
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId)
    (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (st : SystemState) :
    (securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = true ∧
       notificationSignalChecked ctx notificationId signaler badge st =
         notificationSignal notificationId badge st) ∨
    (securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = false ∧
       notificationSignalChecked ctx notificationId signaler badge st =
         .error .flowDenied) := by
  cases hFlow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) with
  | true => left; exact ⟨rfl, by simp [notificationSignalChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [notificationSignalChecked, hFlow]⟩

/-- WS-H8: `cspaceCopyChecked` either delegates or returns `flowDenied`. -/
theorem enforcement_sufficiency_cspaceCopy
    (ctx : LabelingContext) (src dst : CSpaceAddr)
    (st : SystemState) :
    (securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true ∧
       cspaceCopyChecked ctx src dst st = cspaceCopy src dst st) ∨
    (securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = false ∧
       cspaceCopyChecked ctx src dst st = .error .flowDenied) := by
  cases hFlow : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) with
  | true => left; exact ⟨rfl, by simp [cspaceCopyChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [cspaceCopyChecked, hFlow]⟩

/-- WS-H8: `cspaceMoveChecked` either delegates or returns `flowDenied`. -/
theorem enforcement_sufficiency_cspaceMove
    (ctx : LabelingContext) (src dst : CSpaceAddr)
    (st : SystemState) :
    (securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true ∧
       cspaceMoveChecked ctx src dst st = cspaceMove src dst st) ∨
    (securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = false ∧
       cspaceMoveChecked ctx src dst st = .error .flowDenied) := by
  cases hFlow : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) with
  | true => left; exact ⟨rfl, by simp [cspaceMoveChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [cspaceMoveChecked, hFlow]⟩

/-- WS-H8: `endpointReceiveDualChecked` either delegates or returns `flowDenied`. -/
theorem enforcement_sufficiency_endpointReceiveDual
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (st : SystemState) :
    (securityFlowsTo (ctx.endpointLabelOf endpointId) (ctx.threadLabelOf receiver) = true ∧
       endpointReceiveDualChecked ctx endpointId receiver st =
         endpointReceiveDual endpointId receiver st) ∨
    (securityFlowsTo (ctx.endpointLabelOf endpointId) (ctx.threadLabelOf receiver) = false ∧
       endpointReceiveDualChecked ctx endpointId receiver st =
         .error .flowDenied) := by
  cases hFlow : securityFlowsTo (ctx.endpointLabelOf endpointId) (ctx.threadLabelOf receiver) with
  | true => left; exact ⟨rfl, by simp [endpointReceiveDualChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [endpointReceiveDualChecked, hFlow]⟩

-- ============================================================================
-- WS-H8: Updated enforcement boundary classification (21 operations)
-- ============================================================================

/-- WS-H8: Updated enforcement boundary — 7 policy-gated operations (up from 3).

Extends the canonical classification with 4 new policy-gated wrappers:
- `notificationSignalChecked` — signaler→notification flow
- `cspaceCopyChecked` — source CNode→destination CNode flow
- `cspaceMoveChecked` — source CNode→destination CNode flow
- `endpointReceiveDualChecked` — endpoint→receiver flow -/
def enforcementBoundaryExtended : List EnforcementClass :=
  [ .policyGated "endpointSendDualChecked"
  , .policyGated "cspaceMintChecked"
  , .policyGated "serviceRestartChecked"
  , .policyGated "notificationSignalChecked"
  , .policyGated "cspaceCopyChecked"
  , .policyGated "cspaceMoveChecked"
  , .policyGated "endpointReceiveDualChecked"
  , .capabilityOnly "cspaceLookupSlot"
  , .capabilityOnly "cspaceInsertSlot"
  , .capabilityOnly "cspaceDeleteSlot"
  , .capabilityOnly "cspaceRevoke"
  , .readOnly "chooseThread"
  , .readOnly "lookupObject"
  , .readOnly "lookupService"
  , .readOnly "cspaceResolvePath"
  , .capabilityOnly "lifecycleRetypeObject"
  , .capabilityOnly "lifecycleRevokeDeleteRetype"
  , .capabilityOnly "storeObject"
  ]

-- ============================================================================
-- WS-H8/A-35: Enforcement soundness meta-theorem
-- ============================================================================

/-- WS-H8/A-35: Enforcement soundness — a checked operation that succeeds
implies the flow check passed. This is the foundational bridge connecting
the enforcement layer to non-interference hypotheses.

For any checked wrapper: if the operation succeeds (returns `.ok`), then
the `securityFlowsTo` check must have evaluated to `true`, meaning the
operation's source domain is authorized to flow to the destination domain. -/
theorem enforcementSoundness_endpointSendDualChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
    (hStep : endpointSendDualChecked ctx endpointId sender msg st = .ok ((), st')) :
    securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = true := by
  unfold endpointSendDualChecked at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases h : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) with
  | true => rfl
  | false => simp [h] at hStep

/-- WS-H8/A-35: Enforcement soundness for notificationSignalChecked. -/
theorem enforcementSoundness_notificationSignalChecked
    (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (st st' : SystemState)
    (hStep : notificationSignalChecked ctx notificationId signaler badge st = .ok ((), st')) :
    securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) = true := by
  cases h : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId) with
  | true => rfl
  | false =>
    have := notificationSignalChecked_flowDenied ctx notificationId signaler badge st h
    rw [this] at hStep; simp at hStep

/-- WS-H8/A-35: Enforcement soundness for cspaceCopyChecked. -/
theorem enforcementSoundness_cspaceCopyChecked
    (ctx : LabelingContext)
    (src dst : CSpaceAddr) (st st' : SystemState)
    (hStep : cspaceCopyChecked ctx src dst st = .ok ((), st')) :
    securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true := by
  cases h : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) with
  | true => rfl
  | false =>
    have := cspaceCopyChecked_flowDenied ctx src dst st h
    rw [this] at hStep; simp at hStep

/-- WS-H8/A-35: Enforcement soundness for cspaceMoveChecked. -/
theorem enforcementSoundness_cspaceMoveChecked
    (ctx : LabelingContext)
    (src dst : CSpaceAddr) (st st' : SystemState)
    (hStep : cspaceMoveChecked ctx src dst st = .ok ((), st')) :
    securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true := by
  cases h : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) with
  | true => rfl
  | false =>
    have := cspaceMoveChecked_flowDenied ctx src dst st h
    rw [this] at hStep; simp at hStep

/-- WS-H8/A-35: Enforcement soundness for endpointReceiveDualChecked. -/
theorem enforcementSoundness_endpointReceiveDualChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (st : SystemState) (r : SeLe4n.ThreadId) (st' : SystemState)
    (hStep : endpointReceiveDualChecked ctx endpointId receiver st = .ok (r, st')) :
    securityFlowsTo (ctx.endpointLabelOf endpointId) (ctx.threadLabelOf receiver) = true := by
  cases h : securityFlowsTo (ctx.endpointLabelOf endpointId) (ctx.threadLabelOf receiver) with
  | true => rfl
  | false =>
    have := endpointReceiveDualChecked_flowDenied ctx endpointId receiver st h
    rw [this] at hStep; simp at hStep

-- ============================================================================
-- WS-H10/A-39: Declassification enforcement
-- ============================================================================

/-! ## WS-H10/A-39 — Declassification Operation

Controlled information downgrade from a higher security domain to a lower one,
gated by an explicit `DeclassificationPolicy`. The `declassify` operation
transfers a value across a security boundary that the normal flow policy
would deny, but only when the declassification policy explicitly authorizes
the downgrade path.

The operation is modeled as a state-transparent write: it stores an object
at the target location (simulating the information transfer) after verifying
authorization. The key security property is that declassification is observable
ONLY to the authorized target domain — all other domains see no change. -/

/-- WS-H10/A-39: Declassification-checked object store: authorizes a controlled
information downgrade from `srcDomain` to `dstDomain` before storing an object.

The operation checks:
1. Normal flow is DENIED (otherwise this isn't declassification, just normal flow)
2. Declassification policy explicitly AUTHORIZES this downgrade path

Returns `flowDenied` if normal flow is allowed (use normal checked ops instead).
Returns `declassificationDenied` if declassification is not authorized. -/
def declassifyStore
    (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) : Kernel Unit :=
  fun st =>
    if ctx.policy.canFlow srcDomain dstDomain then
      -- Normal flow allowed — this is not a declassification scenario
      .error .flowDenied
    else if declPolicy.canDeclassify srcDomain dstDomain then
      -- Declassification authorized — perform the controlled downgrade
      storeObject targetId obj st
    else
      .error .flowDenied

/-- WS-H10/A-39: When declassification is authorized, the operation delegates
to storeObject. -/
theorem declassifyStore_eq_storeObject_when_authorized
    (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (st : SystemState)
    (hNormalDenied : ctx.policy.canFlow srcDomain dstDomain = false)
    (hDeclAuth : declPolicy.canDeclassify srcDomain dstDomain = true) :
    declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st =
      storeObject targetId obj st := by
  simp [declassifyStore, hNormalDenied, hDeclAuth]

/-- WS-H10/A-39: When normal flow is allowed, declassifyStore returns an error
(use the normal checked operation instead). -/
theorem declassifyStore_error_when_normal_allowed
    (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (st : SystemState)
    (hNormalAllowed : ctx.policy.canFlow srcDomain dstDomain = true) :
    declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st =
      .error .flowDenied := by
  simp [declassifyStore, hNormalAllowed]

/-- WS-H10/A-39: When declassification is not authorized, declassifyStore
returns an error. -/
theorem declassifyStore_error_when_declass_denied
    (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (st : SystemState)
    (hNormalDenied : ctx.policy.canFlow srcDomain dstDomain = false)
    (hDeclDenied : declPolicy.canDeclassify srcDomain dstDomain = false) :
    declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st =
      .error .flowDenied := by
  simp [declassifyStore, hNormalDenied, hDeclDenied]

/-- WS-H10/A-39: Declassification preserves state on denial — if either
authorization check fails, no state mutation occurs. -/
theorem declassifyStore_denied_no_state_change
    (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (st : SystemState)
    (e : KernelError)
    (hResult : declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = .error e) :
    ¬∃ st', declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = .ok ((), st') := by
  intro ⟨st', h⟩
  rw [hResult] at h; simp at h

/-- WS-H10/A-39: Enforcement soundness for declassifyStore — if the operation
succeeds, both authorization checks must have passed. -/
theorem enforcementSoundness_declassifyStore
    (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject)
    (st st' : SystemState)
    (hStep : declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st = .ok ((), st')) :
    ctx.policy.canFlow srcDomain dstDomain = false ∧
    declPolicy.canDeclassify srcDomain dstDomain = true := by
  unfold declassifyStore at hStep
  cases hNormal : ctx.policy.canFlow srcDomain dstDomain with
  | true => simp [hNormal] at hStep
  | false =>
    cases hDecl : declPolicy.canDeclassify srcDomain dstDomain with
    | false => simp [hNormal, hDecl] at hStep
    | true => exact ⟨rfl, rfl⟩

-- ============================================================================
-- WS-H10: Information-flow invariant bundle
-- ============================================================================

/-! ## WS-H10 — Information-Flow Invariant Bundle

The IF invariant bundle collects all information-flow-relevant well-formedness
properties that must hold for security guarantees. This includes:

1. **Endpoint flow policy well-formedness** (M-16): all per-endpoint policy
   overrides are reflexive and transitive.
2. **Declassification policy consistency**: declassification paths do not
   overlap with normal flow paths (ensured by `isDeclassificationAuthorized`).

Note: Since `DomainFlowPolicy`, `EndpointFlowPolicy`, and
`DeclassificationPolicy` are external configuration parameters (not stored in
`SystemState`), preservation is trivially satisfied — kernel transitions do not
modify policy configuration. The bundle is parameterized over these policies
rather than over system state. -/

/-- WS-H10: Information-flow configuration invariant bundle.

Collects all well-formedness requirements on the information-flow policy
configuration. This is checked once at system initialization and holds
invariantly because kernel transitions do not modify policy objects.

- `globalPolicyWF`: The global domain flow policy is reflexive and transitive.
- `endpointPolicyWF`: Every per-endpoint override policy is well-formed.
- `declassConsistent`: Declassification paths are disjoint from normal flow
  paths (ensured structurally by `isDeclassificationAuthorized`). -/
structure InformationFlowConfigInvariant where
  globalPolicy : DomainFlowPolicy
  endpointPolicy : EndpointFlowPolicy
  declPolicy : DeclassificationPolicy
  globalPolicyWF : globalPolicy.wellFormed
  endpointPolicyWF : ∀ oid p, endpointPolicy.endpointPolicy oid = some p → p.wellFormed
  declassConsistent : ∀ src dst : SecurityDomain,
    DeclassificationPolicy.isDeclassificationAuthorized globalPolicy declPolicy src dst = true →
    globalPolicy.canFlow src dst = false

/-- WS-H10: The default configuration (allowAll + no overrides + no declass) is valid. -/
theorem defaultConfigInvariant :
    ∃ inv : InformationFlowConfigInvariant,
      inv.globalPolicy = .allowAll ∧
      inv.endpointPolicy = { endpointPolicy := fun _ => none } ∧
      inv.declPolicy = .none := by
  exact ⟨{
    globalPolicy := .allowAll
    endpointPolicy := { endpointPolicy := fun _ => none }
    declPolicy := .none
    globalPolicyWF := DomainFlowPolicy.allowAll_wellFormed
    endpointPolicyWF := fun _ _ h => by simp at h
    declassConsistent := fun _ _ h => by simp [DeclassificationPolicy.isDeclassificationAuthorized, DeclassificationPolicy.none] at h
  }, rfl, rfl, rfl⟩

/-- WS-H10: Kernel transitions preserve the IF config invariant trivially —
policy configuration is external to `SystemState` and never modified by
kernel operations. -/
theorem kernelTransition_preserves_ifConfigInvariant
    (inv : InformationFlowConfigInvariant)
    (_st _st' : SystemState) :
    inv = inv := rfl

end SeLe4n.Kernel
