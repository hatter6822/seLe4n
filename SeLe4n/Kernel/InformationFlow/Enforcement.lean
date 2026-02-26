import SeLe4n.Kernel.InformationFlow.Policy
import SeLe4n.Kernel.IPC.Operations
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

/-- Policy-checked endpoint send: verifies that information may flow from the
sender's security domain to the endpoint's security domain before delegating
to the underlying `endpointSend` operation.

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
-- WS-E5/H-04: Per-endpoint flow policy enforcement
-- ============================================================================

/-- WS-E5/H-04: Policy-checked endpoint send using per-endpoint flow policy.
    Uses `resolveEndpointFlow` which supports per-endpoint overrides
    (`permitAlways`, `denyAlways`) alongside the default label-based check. -/
def endpointSendPolicyChecked
    (pctx : PolicyContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    let senderLabel := pctx.labels.threadLabelOf sender
    let endpointLabel := pctx.labels.endpointLabelOf endpointId
    if resolveEndpointFlow pctx senderLabel endpointLabel endpointId then
      endpointSend endpointId sender st
    else
      .error .flowDenied

/-- WS-E5/H-04: When per-endpoint policy resolves to allow, the policy-checked
    send behaves identically to the unchecked send. -/
theorem endpointSendPolicyChecked_eq_send_when_allowed
    (pctx : PolicyContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (st : SystemState)
    (hAllow : resolveEndpointFlow pctx
                (pctx.labels.threadLabelOf sender)
                (pctx.labels.endpointLabelOf endpointId)
                endpointId = true) :
    endpointSendPolicyChecked pctx endpointId sender st =
      endpointSend endpointId sender st := by
  unfold endpointSendPolicyChecked
  simp [hAllow]

/-- WS-E5/H-04: When per-endpoint policy resolves to deny, the policy-checked
    send returns `flowDenied` without modifying state. -/
theorem endpointSendPolicyChecked_flowDenied
    (pctx : PolicyContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (st : SystemState)
    (hDeny : resolveEndpointFlow pctx
               (pctx.labels.threadLabelOf sender)
               (pctx.labels.endpointLabelOf endpointId)
               endpointId = false) :
    endpointSendPolicyChecked pctx endpointId sender st =
      .error .flowDenied := by
  unfold endpointSendPolicyChecked
  simp [hDeny]

/-- WS-E5/H-04: With default policy context, the policy-checked send equals
    the standard label-checked send. -/
theorem endpointSendPolicyChecked_default_eq_checked
    (pctx : PolicyContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (st : SystemState)
    (hDefault : pctx.endpointPolicy endpointId = .useDefault) :
    endpointSendPolicyChecked pctx endpointId sender st =
      endpointSendChecked pctx.labels endpointId sender st := by
  unfold endpointSendPolicyChecked endpointSendChecked
  simp [resolveEndpointFlow, hDefault]

end SeLe4n.Kernel
