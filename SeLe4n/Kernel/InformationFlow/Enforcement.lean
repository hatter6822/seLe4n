import SeLe4n.Kernel.InformationFlow.Policy
import SeLe4n.Kernel.IPC.Operations
import SeLe4n.Kernel.IPC.DualQueue
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Service.Operations

/-!
# Information-Flow Enforcement (WS-D2, F-02)

This module wires `securityFlowsTo` policy checks into kernel operations.

## Enforcement boundary decision

The seLe4n information-flow enforcement boundary follows a two-layer design:

1. **Policy-checked operations** (this module): operations that cross domain boundaries
   and carry explicit information flow risk receive a `securityFlowsTo` gate that returns
   `flowDenied` when the labeling context forbids the flow. These are:
   - `endpointSendChecked` — sender→endpoint flow (IPC channel boundary),
   - `cspaceMintChecked` — source CNode→destination CNode flow (authority derivation boundary),
   - `serviceRestartChecked` — orchestrator→service flow (service lifecycle boundary).

2. **Capability-only operations** (existing modules): operations whose authority is fully
   determined by possession of a valid capability (e.g., `cspaceLookupSlot`,
   `notificationSignal`, `vspaceMapPage`) rely on capability-based authority alone.
   Information-flow enforcement is redundant for these because the capability itself
   encodes the authority grant.

This separation is documented as the canonical enforcement boundary for the abstract model.
Hardware-targeted slices may extend enforcement to additional operations as the threat model
evolves.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Policy-checked endpoint send (legacy): verifies that information may flow
from the sender's security domain to the endpoint's security domain before
delegating to the underlying `endpointSend` operation.

WS-G7: Deprecated in favor of `endpointSendDualChecked` which uses O(1)
intrusive dual-queue operations. Retained for backward compatibility of
existing invariant proofs.

Returns `flowDenied` when `securityFlowsTo senderLabel endpointLabel = false`. -/
def endpointSendChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    let senderLabel := ctx.threadLabelOf sender
    let endpointLabel := ctx.endpointLabelOf endpointId
    if securityFlowsTo senderLabel endpointLabel then
      endpointSend endpointId sender st
    else
      .error .flowDenied

/-- WS-G7/F-P04: Policy-checked endpoint send using O(1) dual-queue.

Verifies that information may flow from the sender's security domain to the
endpoint's security domain, then delegates to `endpointSendDual`.

This is the recommended replacement for `endpointSendChecked` as part of the
legacy-to-dual-queue migration (WS-G7).

Returns `flowDenied` when `securityFlowsTo senderLabel endpointLabel = false`. -/
def endpointSendDualChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (msg : IpcMessage := IpcMessage.empty) : Kernel Unit :=
  fun st =>
    let senderLabel := ctx.threadLabelOf sender
    let endpointLabel := ctx.endpointLabelOf endpointId
    if securityFlowsTo senderLabel endpointLabel then
      endpointSendDual endpointId sender msg st
    else
      .error .flowDenied

/-- Policy-checked capability mint: verifies that information may flow from
the source CNode's security domain to the destination CNode's security domain
before delegating to the underlying `cspaceMint` operation.

Returns `flowDenied` when `securityFlowsTo srcLabel dstLabel = false`. -/
def cspaceMintChecked
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge := none) : Kernel Unit :=
  fun st =>
    let srcLabel := ctx.objectLabelOf src.cnode
    let dstLabel := ctx.objectLabelOf dst.cnode
    if securityFlowsTo srcLabel dstLabel then
      cspaceMint src dst rights badge st
    else
      .error .flowDenied

/-- Policy-checked service restart: verifies that information may flow from
the orchestrator's security domain to the service's security domain before
delegating to the underlying `serviceRestart` operation.

Returns `flowDenied` when `securityFlowsTo orchestratorLabel serviceLabel = false`. -/
def serviceRestartChecked
    (ctx : LabelingContext)
    (orchestrator : ServiceId)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy) : Kernel Unit :=
  fun st =>
    let orchestratorLabel := ctx.serviceLabelOf orchestrator
    let serviceLabel := ctx.serviceLabelOf sid
    if securityFlowsTo orchestratorLabel serviceLabel then
      serviceRestart sid policyAllowsStop policyAllowsStart st
    else
      .error .flowDenied

-- ============================================================================
-- Enforcement correctness theorems
-- ============================================================================

/-- When the policy allows flow, the checked send behaves identically to the
unchecked send. -/
theorem endpointSendChecked_eq_endpointSend_when_allowed
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = true) :
    endpointSendChecked ctx endpointId sender st =
      endpointSend endpointId sender st := by
  unfold endpointSendChecked
  simp [hFlow]

/-- WS-G7: When the policy allows flow, the dual-queue checked send behaves
identically to the unchecked dual-queue send. -/
theorem endpointSendDualChecked_eq_endpointSendDual_when_allowed
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = true) :
    endpointSendDualChecked ctx endpointId sender msg st =
      endpointSendDual endpointId sender msg st := by
  unfold endpointSendDualChecked
  simp [hFlow]

/-- WS-G7: When the policy denies flow, the dual-queue checked send returns
`flowDenied` without modifying state. -/
theorem endpointSendDualChecked_flowDenied
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = false) :
    endpointSendDualChecked ctx endpointId sender msg st =
      .error .flowDenied := by
  unfold endpointSendDualChecked
  simp [hDeny]

/-- When the policy denies flow, the checked send returns `flowDenied`
without modifying state. -/
theorem endpointSendChecked_flowDenied
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = false) :
    endpointSendChecked ctx endpointId sender st =
      .error .flowDenied := by
  unfold endpointSendChecked
  simp [hDeny]

/-- When the policy allows flow, the checked mint behaves identically to the
unchecked mint. -/
theorem cspaceMintChecked_eq_cspaceMint_when_allowed
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.objectLabelOf src.cnode)
               (ctx.objectLabelOf dst.cnode) = true) :
    cspaceMintChecked ctx src dst rights badge st =
      cspaceMint src dst rights badge st := by
  unfold cspaceMintChecked
  simp [hFlow]

/-- When the policy denies flow, the checked mint returns `flowDenied`
without modifying state. -/
theorem cspaceMintChecked_flowDenied
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.objectLabelOf src.cnode)
               (ctx.objectLabelOf dst.cnode) = false) :
    cspaceMintChecked ctx src dst rights badge st =
      .error .flowDenied := by
  unfold cspaceMintChecked
  simp [hDeny]

/-- When the policy allows flow, the checked restart behaves identically to the
unchecked restart. -/
theorem serviceRestartChecked_eq_serviceRestart_when_allowed
    (ctx : LabelingContext)
    (orchestrator sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.serviceLabelOf orchestrator)
               (ctx.serviceLabelOf sid) = true) :
    serviceRestartChecked ctx orchestrator sid policyAllowsStop policyAllowsStart st =
      serviceRestart sid policyAllowsStop policyAllowsStart st := by
  unfold serviceRestartChecked
  simp [hFlow]

/-- When the policy denies flow, the checked restart returns `flowDenied`
without modifying state. -/
theorem serviceRestartChecked_flowDenied
    (ctx : LabelingContext)
    (orchestrator sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.serviceLabelOf orchestrator)
               (ctx.serviceLabelOf sid) = false) :
    serviceRestartChecked ctx orchestrator sid policyAllowsStop policyAllowsStart st =
      .error .flowDenied := by
  unfold serviceRestartChecked
  simp [hDeny]

/-- Reflexive flow always allows: self-domain operations are never denied. -/
theorem endpointSendChecked_self_domain_allowed
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (st : SystemState)
    (hSameLabel : ctx.threadLabelOf sender = ctx.endpointLabelOf endpointId) :
    endpointSendChecked ctx endpointId sender st =
      endpointSend endpointId sender st := by
  apply endpointSendChecked_eq_endpointSend_when_allowed
  rw [hSameLabel]
  exact securityFlowsTo_refl _

-- ============================================================================
-- WS-E5/M-07: Enforcement boundary specification
-- ============================================================================

/-! ## M-07 — Enforcement Boundary Specification

This section formally classifies all kernel operations into enforcement categories
and proves that the three policy-checked wrappers are sufficient for the
enforcement boundary.

**Canonical classification (17 operations):**

| Category | Operations |
|---|---|
| **Policy-gated** (3) | `endpointSendChecked`, `cspaceMintChecked`, `serviceRestartChecked` |
| **Capability-only** (7) | `cspaceLookupSlot`, `cspaceInsertSlot`, `cspaceDeleteSlot`, `cspaceRevoke`, `cspaceCopy`, `cspaceMove`, `notificationSignal` |
| **Read-only** (4) | `chooseThread`, `lookupObject`, `lookupService`, `cspaceResolvePath` |
| **Internal/lifecycle** (3) | `lifecycleRetypeObject`, `lifecycleRevokeDeleteRetype`, `storeObject` |

Policy-gated operations cross domain boundaries and carry explicit information-flow
risk. Capability-only operations derive authority entirely from capability
possession. Read-only operations produce no state mutation. Internal operations
are building blocks used by the public API under capability-guarded contexts.

The `*_denied_preserves_state` theorems prove that when a policy-gated operation
denies a flow, no state change occurs. The `enforcement_sufficiency_*` theorems
prove the complete disjunction: each checked operation either delegates to the
unchecked version or returns `flowDenied`, covering all cases. -/

/-- WS-E5/M-07: Classification of kernel operations for enforcement purposes. -/
inductive EnforcementClass where
  | policyGated (name : String)
  | capabilityOnly (name : String)
  | readOnly (name : String)
  deriving Repr

/-- WS-E5/M-07: Canonical enforcement boundary classification table (17 entries). -/
def enforcementBoundary : List EnforcementClass :=
  [ .policyGated "endpointSendChecked"
  , .policyGated "cspaceMintChecked"
  , .policyGated "serviceRestartChecked"
  , .capabilityOnly "cspaceLookupSlot"
  , .capabilityOnly "cspaceInsertSlot"
  , .capabilityOnly "cspaceDeleteSlot"
  , .capabilityOnly "cspaceRevoke"
  , .capabilityOnly "cspaceCopy"
  , .capabilityOnly "cspaceMove"
  , .capabilityOnly "notificationSignal"
  , .readOnly "chooseThread"
  , .readOnly "lookupObject"
  , .readOnly "lookupService"
  , .readOnly "cspaceResolvePath"
  , .capabilityOnly "lifecycleRetypeObject"
  , .capabilityOnly "lifecycleRevokeDeleteRetype"
  , .capabilityOnly "storeObject"
  ]

-- ============================================================================
-- WS-E5/M-07: Denied-preserves-state theorems
-- ============================================================================

/-- When the policy denies flow, `endpointSendChecked` produces no state change. -/
theorem endpointSendChecked_denied_preserves_state
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = false) :
    ¬∃ st', endpointSendChecked ctx endpointId sender st = .ok ((), st') := by
  intro ⟨st', h⟩
  simp [endpointSendChecked, hDeny] at h

/-- When the policy denies flow, `cspaceMintChecked` produces no state change. -/
theorem cspaceMintChecked_denied_preserves_state
    (ctx : LabelingContext) (src dst : CSpaceAddr)
    (rights : List AccessRight) (badge : Option SeLe4n.Badge)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.objectLabelOf src.cnode)
               (ctx.objectLabelOf dst.cnode) = false) :
    ¬∃ st', cspaceMintChecked ctx src dst rights badge st = .ok ((), st') := by
  intro ⟨st', h⟩
  simp [cspaceMintChecked, hDeny] at h

/-- When the policy denies flow, `serviceRestartChecked` produces no state change. -/
theorem serviceRestartChecked_denied_preserves_state
    (ctx : LabelingContext) (orchestrator sid : ServiceId)
    (policyAllowsStop policyAllowsStart : ServicePolicy)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.serviceLabelOf orchestrator)
               (ctx.serviceLabelOf sid) = false) :
    ¬∃ st', serviceRestartChecked ctx orchestrator sid
              policyAllowsStop policyAllowsStart st = .ok ((), st') := by
  intro ⟨st', h⟩
  simp [serviceRestartChecked, hDeny] at h

-- ============================================================================
-- WS-E5/M-07: Enforcement sufficiency theorems (complete disjunction)
-- ============================================================================

/-- `endpointSendChecked` either delegates to unchecked or returns `flowDenied`. -/
theorem enforcement_sufficiency_endpointSend
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (st : SystemState) :
    (securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = true ∧
       endpointSendChecked ctx endpointId sender st = endpointSend endpointId sender st) ∨
    (securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = false ∧
       endpointSendChecked ctx endpointId sender st = .error .flowDenied) := by
  cases hFlow : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) with
  | true => left; exact ⟨rfl, by simp [endpointSendChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [endpointSendChecked, hFlow]⟩

/-- `cspaceMintChecked` either delegates to unchecked or returns `flowDenied`. -/
theorem enforcement_sufficiency_cspaceMint
    (ctx : LabelingContext) (src dst : CSpaceAddr)
    (rights : List AccessRight) (badge : Option SeLe4n.Badge)
    (st : SystemState) :
    (securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true ∧
       cspaceMintChecked ctx src dst rights badge st = cspaceMint src dst rights badge st) ∨
    (securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = false ∧
       cspaceMintChecked ctx src dst rights badge st = .error .flowDenied) := by
  cases hFlow : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) with
  | true => left; exact ⟨rfl, by simp [cspaceMintChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [cspaceMintChecked, hFlow]⟩

/-- `serviceRestartChecked` either delegates to unchecked or returns `flowDenied`. -/
theorem enforcement_sufficiency_serviceRestart
    (ctx : LabelingContext) (orchestrator sid : ServiceId)
    (policyAllowsStop policyAllowsStart : ServicePolicy)
    (st : SystemState) :
    (securityFlowsTo (ctx.serviceLabelOf orchestrator) (ctx.serviceLabelOf sid) = true ∧
       serviceRestartChecked ctx orchestrator sid policyAllowsStop policyAllowsStart st =
         serviceRestart sid policyAllowsStop policyAllowsStart st) ∨
    (securityFlowsTo (ctx.serviceLabelOf orchestrator) (ctx.serviceLabelOf sid) = false ∧
       serviceRestartChecked ctx orchestrator sid policyAllowsStop policyAllowsStart st =
         .error .flowDenied) := by
  cases hFlow : securityFlowsTo (ctx.serviceLabelOf orchestrator) (ctx.serviceLabelOf sid) with
  | true => left; exact ⟨rfl, by simp [serviceRestartChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [serviceRestartChecked, hFlow]⟩

-- ============================================================================
-- WS-H8: Missing enforcement wrappers (A-35/H-07)
-- ============================================================================

/-! ## WS-H8 — Enforcement-NI Bridge & Missing Wrappers

Findings addressed:
- **A-35 / H-07** (CRITICAL): Enforcement-NI bridge is disconnected — no theorem
  connects `securityFlowsTo` checks to domain-separation guarantees.
- **H-07** (HIGH): `notificationSignal`, `cspaceCopy`, `cspaceMove`,
  `endpointReceiveDual` lack information-flow enforcement wrappers.
- **A-36 / A-37 / H-11** (HIGH): Domain timing metadata not projected.

This section adds 4 new policy-checked wrappers and their correctness theorems,
extending the enforcement boundary from 3 to 7 policy-gated operations. -/

/-- WS-H8/H-07: Policy-checked notification signal: verifies that information
may flow from the signaler's security domain to the notification object's
security domain before delegating to `notificationSignal`.

A high-domain thread signaling a low-domain notification leaks one bit of
information; the wrapper gates on `securityFlowsTo` to prevent this.

Returns `flowDenied` when `securityFlowsTo signalerLabel notificationLabel = false`. -/
def notificationSignalChecked
    (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId)
    (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) : Kernel Unit :=
  fun st =>
    let signalerLabel := ctx.threadLabelOf signaler
    let notificationLabel := ctx.objectLabelOf notificationId
    if securityFlowsTo signalerLabel notificationLabel then
      notificationSignal notificationId badge st
    else
      .error .flowDenied

/-- WS-H8/H-07: Policy-checked capability copy: verifies that information may
flow from the source CNode's domain to the destination CNode's domain before
delegating to `cspaceCopy`.

Cross-domain capability copy could transfer authority from a restricted domain
to an unrestricted domain; the wrapper gates on `securityFlowsTo`.

Returns `flowDenied` when `securityFlowsTo srcLabel dstLabel = false`. -/
def cspaceCopyChecked
    (ctx : LabelingContext)
    (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    let srcLabel := ctx.objectLabelOf src.cnode
    let dstLabel := ctx.objectLabelOf dst.cnode
    if securityFlowsTo srcLabel dstLabel then
      cspaceCopy src dst st
    else
      .error .flowDenied

/-- WS-H8/H-07: Policy-checked capability move: verifies that information may
flow from the source CNode's domain to the destination CNode's domain before
delegating to `cspaceMove`.

Returns `flowDenied` when `securityFlowsTo srcLabel dstLabel = false`. -/
def cspaceMoveChecked
    (ctx : LabelingContext)
    (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    let srcLabel := ctx.objectLabelOf src.cnode
    let dstLabel := ctx.objectLabelOf dst.cnode
    if securityFlowsTo srcLabel dstLabel then
      cspaceMove src dst st
    else
      .error .flowDenied

/-- WS-H8/H-07: Policy-checked endpoint receive (dual-queue): verifies that
information may flow from the endpoint's domain to the receiver's domain
before delegating to `endpointReceiveDual`.

The receiver learns about the sender's presence and message content; the
wrapper gates on `securityFlowsTo` from endpoint to receiver domain.

Returns `flowDenied` when `securityFlowsTo endpointLabel receiverLabel = false`. -/
def endpointReceiveDualChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) : Kernel SeLe4n.ThreadId :=
  fun st =>
    let endpointLabel := ctx.endpointLabelOf endpointId
    let receiverLabel := ctx.threadLabelOf receiver
    if securityFlowsTo endpointLabel receiverLabel then
      endpointReceiveDual endpointId receiver st
    else
      .error .flowDenied

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
  [ .policyGated "endpointSendChecked"
  , .policyGated "endpointSendDualChecked"
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
  cases h : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) with
  | true => rfl
  | false =>
    have := endpointSendDualChecked_flowDenied ctx endpointId sender msg st h
    rw [this] at hStep; simp at hStep

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

end SeLe4n.Kernel
