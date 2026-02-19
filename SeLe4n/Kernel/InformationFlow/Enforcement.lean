/-!
# Information-Flow Enforcement Layer (WS-D2, F-02)

This module defines the **enforcement boundary** for SeLe4n's information-flow policy.

## Enforcement Architecture

The enforcement boundary sits between the syscall entry layer and the core kernel operations:

```
  User request
       │
       ▼
  ┌─────────────────────────┐
  │  Enforcement Layer      │  ← securityFlowsTo checked HERE
  │  (this module)          │
  └────────────┬────────────┘
               │ (only if policy allows)
               ▼
  ┌─────────────────────────┐
  │  Core Kernel Operations │  ← capability-based authority only
  │  (IPC, Capability, …)  │
  └─────────────────────────┘
```

### Design Decision (ADR)

**Which operations check information-flow policy vs. rely on capability-based authority alone?**

The enforced operations are those that transfer information or authority across security domains:

| Operation | Enforcement | Rationale |
|---|---|---|
| `endpointSend` | **Enforced** | Sender→endpoint flow: prevents high-domain data from leaking to low-domain endpoints. |
| `cspaceMint` | **Enforced** | Source→destination CNode flow: prevents high-domain authority from being minted into low-domain CSpaces. |
| `serviceRestart` | **Enforced** | Orchestrator→service flow: prevents unauthorized cross-domain service lifecycle control. |
| `chooseThread` | Not enforced | Read-only operation; does not mutate state. No information flow occurs. |
| `schedule` | Not enforced | Internal scheduler transition; operates within the kernel trusted domain. |
| `cspaceLookupSlot` | Not enforced | Read-only; no cross-domain flow. |
| `cspaceDeleteSlot` | Not enforced | Destructive but contained; deleting your own capability does not leak information. |
| `cspaceRevoke` | Not enforced | Revocation is authority *reduction*, not transfer. |
| `lifecycleRetypeObject` | Not enforced | Already gated by capability authority; retype does not transfer information across domains. |

This boundary is intentionally conservative: enforcement is applied at the three operations
identified in audit finding F-02 as the minimum viable enforcement surface. Future milestones
(IF-M3+) may extend enforcement to additional operations.
-/
import SeLe4n.Kernel.InformationFlow.Projection
import SeLe4n.Kernel.IPC.Operations
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Service.Operations

namespace SeLe4n.Kernel

open SeLe4n.Model

/-! ## Enforced kernel operations -/

/-- Policy-enforced endpoint send: checks that the sender's security label flows to
the endpoint's security label before delegating to the core `endpointSend` operation.

**Enforcement semantics:** A thread at confidentiality level `high` cannot send to an endpoint
labeled `low`, preventing information from flowing downward in the confidentiality lattice.
Symmetrically, integrity must not flow upward. -/
def enforcedEndpointSend
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    if securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) then
      endpointSend endpointId sender st
    else
      .error .policyDenied

/-- Policy-enforced capability mint: checks that the source CNode's security label flows to
the destination CNode's security label before delegating to the core `cspaceMint` operation.

**Enforcement semantics:** A capability in a `high`-confidentiality CNode cannot be minted
into a `low`-confidentiality CNode, preventing authority from leaking downward. -/
def enforcedCspaceMint
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge := none) : Kernel Unit :=
  fun st =>
    if securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) then
      cspaceMint src dst rights badge st
    else
      .error .policyDenied

/-- Policy-enforced service restart: checks that the orchestrator thread's security label
flows to the target service's security label before delegating to the core `serviceRestart`.

**Enforcement semantics:** A `low`-integrity orchestrator cannot restart a `high`-integrity
service, and a `high`-confidentiality orchestrator cannot restart a `low`-confidentiality
service (to prevent covert channels through service state transitions). -/
def enforcedServiceRestart
    (ctx : LabelingContext)
    (orchestrator : SeLe4n.ThreadId)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy) : Kernel Unit :=
  fun st =>
    if securityFlowsTo (ctx.threadLabelOf orchestrator) (ctx.serviceLabelOf sid) then
      serviceRestart sid policyAllowsStop policyAllowsStart st
    else
      .error .policyDenied

/-! ## Enforcement denial lemmas -/

/-- Enforcement denial for endpoint send when information-flow policy is violated. -/
theorem enforcedEndpointSend_denied
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (st : SystemState)
    (hDenied : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = false) :
    enforcedEndpointSend ctx endpointId sender st = .error .policyDenied := by
  unfold enforcedEndpointSend
  simp [hDenied]

/-- Enforcement denial for capability mint when information-flow policy is violated. -/
theorem enforcedCspaceMint_denied
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (st : SystemState)
    (hDenied : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = false) :
    enforcedCspaceMint ctx src dst rights badge st = .error .policyDenied := by
  unfold enforcedCspaceMint
  simp [hDenied]

/-- Enforcement denial for service restart when information-flow policy is violated. -/
theorem enforcedServiceRestart_denied
    (ctx : LabelingContext)
    (orchestrator : SeLe4n.ThreadId)
    (sid : ServiceId)
    (policyAllowsStop policyAllowsStart : ServicePolicy)
    (st : SystemState)
    (hDenied : securityFlowsTo (ctx.threadLabelOf orchestrator) (ctx.serviceLabelOf sid) = false) :
    enforcedServiceRestart ctx orchestrator sid policyAllowsStop policyAllowsStart st = .error .policyDenied := by
  unfold enforcedServiceRestart
  simp [hDenied]

/-! ## Enforcement pass-through lemmas -/

/-- When policy allows, enforced endpoint send delegates to the core operation. -/
theorem enforcedEndpointSend_delegates
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (st : SystemState)
    (hAllowed : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = true) :
    enforcedEndpointSend ctx endpointId sender st = endpointSend endpointId sender st := by
  unfold enforcedEndpointSend
  simp [hAllowed]

/-- When policy allows, enforced capability mint delegates to the core operation. -/
theorem enforcedCspaceMint_delegates
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (st : SystemState)
    (hAllowed : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true) :
    enforcedCspaceMint ctx src dst rights badge st = cspaceMint src dst rights badge st := by
  unfold enforcedCspaceMint
  simp [hAllowed]

/-- When policy allows, enforced service restart delegates to the core operation. -/
theorem enforcedServiceRestart_delegates
    (ctx : LabelingContext)
    (orchestrator : SeLe4n.ThreadId)
    (sid : ServiceId)
    (policyAllowsStop policyAllowsStart : ServicePolicy)
    (st : SystemState)
    (hAllowed : securityFlowsTo (ctx.threadLabelOf orchestrator) (ctx.serviceLabelOf sid) = true) :
    enforcedServiceRestart ctx orchestrator sid policyAllowsStop policyAllowsStart st =
      serviceRestart sid policyAllowsStop policyAllowsStart st := by
  unfold enforcedServiceRestart
  simp [hAllowed]

end SeLe4n.Kernel
