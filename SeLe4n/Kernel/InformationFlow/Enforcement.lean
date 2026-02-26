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
-- WS-E5/M-07: Enforcement boundary completeness
-- ============================================================================

/-!
## WS-E5/M-07: Enforcement boundary — unchecked operation safety

### Enforcement gate classification

Every kernel operation falls into exactly one category:

**Category 1 — Policy-gated (cross-domain flow risk)**:
Operations that transfer information across security domain boundaries.
Each has a `*Checked` wrapper that interposes a `securityFlowsTo` gate.
- `endpointSend` → `endpointSendChecked` (sender→endpoint IPC boundary)
- `cspaceMint` → `cspaceMintChecked` (CNode→CNode authority derivation)
- `serviceRestart` → `serviceRestartChecked` (orchestrator→service lifecycle)

**Category 2 — Non-interference proven (no enforcement needed)**:
Operations with standalone non-interference proofs demonstrating they preserve
`lowEquivalent` for any observer. No enforcement gate is needed because the
proofs guarantee no information leaks regardless of domain assignment.
- `chooseThread` — read-only scheduler query; `chooseThread_preserves_lowEquivalent`
- `cspaceRevoke` — single-CNode local revocation; `cspaceRevoke_preserves_lowEquivalent`
- `lifecycleRetypeObject` — single-object retype; `lifecycleRetypeObject_preserves_lowEquivalent`

**Category 3 — Capability-bounded (single-domain operations)**:
Operations whose effects are confined to objects already within the caller's
authority scope (possession of a valid capability). No cross-domain flow occurs
because the operation reads/writes only the object(s) addressed by the capability.
- `cspaceLookupSlot` — reads a single CNode slot within the caller's CSpace
- `cspaceCopy`, `cspaceMove`, `cspaceMutate` — operate on source/dest within one CSpace
- `cspaceDeleteSlot` — removes a single slot from the caller's CNode
- `cspaceInsertSlot` — inserts into a slot the caller already holds authority over
- `notificationSignal`, `notificationWait` — operate on a single notification object
- `endpointAwaitReceive`, `endpointReceive` — receiver-side IPC (blocked on the endpoint)
- `schedule`, `handleYield` — scheduler transitions; scheduler state is global but
  domain-independent (no per-thread label information leaks through scheduling order)

**Category 4 — Internal helpers (not standalone transitions)**:
Functions that are only invoked as sub-steps of Category 1–3 operations.
They are never called directly from the public API surface.
- `removeRunnable`, `ensureRunnable` — scheduler list manipulation
- `lookupTcb`, `storeTcbIpcState` — TCB state access
- `storeServiceEntry` — service graph node update
- `serviceBfsFuel`, `serviceHasPathTo` — service graph queries (pure/read-only)
-/

-- ----------------------------------------------------------------------------
-- Checked operation completeness: the gate decides, never silently passes
-- ----------------------------------------------------------------------------

/-- WS-E5/M-07: The checked send either delegates to the unchecked send
or denies — there is no third outcome. This ensures the enforcement gate
is a complete decision point. -/
theorem endpointSendChecked_complete
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (st : SystemState) :
    (endpointSendChecked ctx endpointId sender st =
      endpointSend endpointId sender st) ∨
    (endpointSendChecked ctx endpointId sender st =
      .error .flowDenied) := by
  unfold endpointSendChecked
  cases h : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId)
  · right; simp [h]
  · left; simp [h]

/-- WS-E5/M-07: The checked mint either delegates or denies. -/
theorem cspaceMintChecked_complete
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (st : SystemState) :
    (cspaceMintChecked ctx src dst rights badge st =
      cspaceMint src dst rights badge st) ∨
    (cspaceMintChecked ctx src dst rights badge st =
      .error .flowDenied) := by
  unfold cspaceMintChecked
  cases h : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode)
  · right; simp [h]
  · left; simp [h]

/-- WS-E5/M-07: The checked restart either delegates or denies. -/
theorem serviceRestartChecked_complete
    (ctx : LabelingContext)
    (orchestrator sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy)
    (st : SystemState) :
    (serviceRestartChecked ctx orchestrator sid policyAllowsStop policyAllowsStart st =
      serviceRestart sid policyAllowsStop policyAllowsStart st) ∨
    (serviceRestartChecked ctx orchestrator sid policyAllowsStop policyAllowsStart st =
      .error .flowDenied) := by
  unfold serviceRestartChecked
  cases h : securityFlowsTo (ctx.serviceLabelOf orchestrator) (ctx.serviceLabelOf sid)
  · right; simp [h]
  · left; simp [h]

-- ----------------------------------------------------------------------------
-- Transitivity: if A→B and B→C are allowed, then chaining is safe
-- ----------------------------------------------------------------------------

/-- WS-E5/M-07: Transitive flow safety — if the policy allows flow from
domain A to B and from B to C, then a sequence of checked operations
through A→B→C cannot create a flow that the policy would deny at each step. -/
theorem transitive_flow_allowed
    (a b c : SecurityLabel)
    (h1 : securityFlowsTo a b = true)
    (h2 : securityFlowsTo b c = true) :
    securityFlowsTo a c = true :=
  securityFlowsTo_trans a b c h1 h2

end SeLe4n.Kernel
