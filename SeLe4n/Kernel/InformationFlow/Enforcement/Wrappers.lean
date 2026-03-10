import SeLe4n.Kernel.InformationFlow.Policy
import SeLe4n.Kernel.IPC.Operations
import SeLe4n.Kernel.IPC.DualQueue
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Service.Operations

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-G7/F-P04: Policy-checked endpoint send using O(1) dual-queue.

Verifies that information may flow from the sender's security domain to the
endpoint's security domain, then delegates to `endpointSendDual`.

This replaced the legacy `endpointSendChecked` (removed in WS-H12a) as part of the
legacy-to-dual-queue migration (WS-G7).

Returns `flowDenied` when `securityFlowsTo senderLabel endpointLabel = false`. -/
def endpointSendDualChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (msg : IpcMessage := IpcMessage.empty) : Kernel Unit :=
  fun st =>
    -- WS-H12d/A-09: Enforce message payload bounds before flow check
    if msg.registers.size > maxMessageRegisters then .error .ipcMessageTooLarge
    else if msg.caps.size > maxExtraCaps then .error .ipcMessageTooManyCaps
    else
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
  -- WS-H12d: Bounds checks are first; when both fail, we reach the flow check
  -- which succeeds (hFlow), delegating to endpointSendDual unchanged
  simp only []
  split
  · -- bounds1 fails: LHS = .error .ipcMessageTooLarge
    -- But endpointSendDual also checks bounds, producing the same error
    unfold endpointSendDual; simp [*]
  · split
    · unfold endpointSendDual; simp [*]
    · simp

/-- WS-G7/WS-H12d: When the policy denies flow and the message is within bounds,
the dual-queue checked send returns `flowDenied` without modifying state.
WS-H12d: Bounds checks precede the flow check, so the theorem requires
`msg.checkBounds = true` to guarantee the flow-denied path is reached. -/
theorem endpointSendDualChecked_flowDenied
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (st : SystemState)
    (hBounds : msg.checkBounds = true)
    (hDeny : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = false) :
    endpointSendDualChecked ctx endpointId sender msg st =
      .error .flowDenied := by
  unfold endpointSendDualChecked
  have ⟨hR, hC⟩ := (IpcMessage.checkBounds_iff_bounded msg).mp hBounds
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from Nat.not_lt.mpr hR, ite_false]
  simp only [show ¬(maxExtraCaps < msg.caps.size) from Nat.not_lt.mpr hC, ite_false]
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
| **Policy-gated** (3) | `endpointSendDualChecked`, `cspaceMintChecked`, `serviceRestartChecked` |
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
  [ .policyGated "endpointSendDualChecked"
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

/-- When the policy denies flow, `endpointSendDualChecked` produces no state change.
WS-H12d: Bounds checks precede the flow check but also produce errors, so the
conclusion ¬∃ st' still holds unconditionally. -/
theorem endpointSendDualChecked_denied_preserves_state
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = false) :
    ¬∃ st', endpointSendDualChecked ctx endpointId sender msg st = .ok ((), st') := by
  intro ⟨st', h⟩
  unfold endpointSendDualChecked at h
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict h : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro hc; simp [hc] at h, ↓reduceIte] at h
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro hc; simp [hc] at h, ↓reduceIte] at h
  simp [hDeny] at h

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

/-- WS-H12d: `endpointSendDualChecked` either returns a bounds error,
delegates to unchecked (when flow allowed), or returns `flowDenied` (when denied).
This is the complete disjunction of enforcement outcomes. -/
theorem enforcement_sufficiency_endpointSendDual
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (st : SystemState) :
    (msg.registers.size > maxMessageRegisters ∧
       endpointSendDualChecked ctx endpointId sender msg st = .error .ipcMessageTooLarge) ∨
    (msg.caps.size > maxExtraCaps ∧
       endpointSendDualChecked ctx endpointId sender msg st = .error .ipcMessageTooManyCaps) ∨
    (securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = true ∧
       endpointSendDualChecked ctx endpointId sender msg st = endpointSendDual endpointId sender msg st) ∨
    (securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = false ∧
       endpointSendDualChecked ctx endpointId sender msg st = .error .flowDenied) := by
  unfold endpointSendDualChecked endpointSendDual
  by_cases hR : maxMessageRegisters < msg.registers.size
  · left; exact ⟨hR, by simp [hR]⟩
  · by_cases hC : maxExtraCaps < msg.caps.size
    · right; left; exact ⟨hC, by simp [hR, hC]⟩
    · cases hFlow : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) with
      | true => right; right; left; exact ⟨rfl, by simp [hR, hC, hFlow]⟩
      | false => right; right; right; exact ⟨rfl, by simp [hR, hC, hFlow]⟩

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

