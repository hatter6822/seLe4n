/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.Policy
import SeLe4n.Kernel.IPC.DualQueue
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Service.Operations
import SeLe4n.Kernel.Service.Registry

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-G7/F-P04: Policy-checked endpoint send using O(1) dual-queue with
capability transfer.

Verifies that information may flow from the sender's security domain to the
endpoint's security domain, then delegates to `endpointSendDualWithCaps`.

AH1-A (H-01 fix): Previously delegated to `endpointSendDual` (no capability
transfer). Now delegates to `endpointSendDualWithCaps` so that checked `.send`
performs capability transfer on rendezvous, matching the unchecked path.

Returns `flowDenied` when `securityFlowsTo senderLabel endpointLabel = false`. -/
def endpointSendDualChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) : Kernel CapTransferSummary :=
  fun st =>
    -- WS-H12d/A-09: Enforce message payload bounds before flow check
    if msg.registers.size > maxMessageRegisters then .error .ipcMessageTooLarge
    else if msg.caps.size > maxExtraCaps then .error .ipcMessageTooManyCaps
    else
    let senderLabel := ctx.threadLabelOf sender
    let endpointLabel := ctx.endpointLabelOf endpointId
    if securityFlowsTo senderLabel endpointLabel then
      endpointSendDualWithCaps endpointId sender msg endpointRights
        senderCspaceRoot receiverSlotBase st
    else
      .error .flowDenied

/-- Policy-checked capability mint: verifies that information may flow from
the source CNode's security domain to the destination CNode's security domain
before delegating to `cspaceMintWithCdt` for CDT-tracked derivation.

Returns `flowDenied` when `securityFlowsTo srcLabel dstLabel = false`. -/
def cspaceMintChecked
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge := none) : Kernel Unit :=
  fun st =>
    let srcLabel := ctx.objectLabelOf src.cnode
    let dstLabel := ctx.objectLabelOf dst.cnode
    if securityFlowsTo srcLabel dstLabel then
      cspaceMintWithCdt src dst rights badge st
    else
      .error .flowDenied

-- ============================================================================
-- Enforcement correctness theorems
-- ============================================================================

/-- WS-G7/AH1-C-1: When the policy allows flow, the dual-queue checked send
behaves identically to the unchecked WithCaps send (with capability transfer).
AH1: Updated from `endpointSendDual` to `endpointSendDualWithCaps` target. -/
theorem endpointSendDualChecked_eq_endpointSendDualWithCaps_when_allowed
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = true) :
    endpointSendDualChecked ctx endpointId sender msg endpointRights
        senderCspaceRoot receiverSlotBase st =
      endpointSendDualWithCaps endpointId sender msg endpointRights
        senderCspaceRoot receiverSlotBase st := by
  unfold endpointSendDualChecked
  -- WS-H12d: Bounds checks are first; when both fail, we reach the flow check
  -- which succeeds (hFlow), delegating to endpointSendDualWithCaps unchanged
  simp only []
  split
  · -- bounds1 fails: LHS = .error .ipcMessageTooLarge
    -- endpointSendDualWithCaps delegates to endpointSendDual which checks bounds
    unfold endpointSendDualWithCaps endpointSendDual; simp [*]
  · split
    · unfold endpointSendDualWithCaps endpointSendDual; simp [*]
    · simp

/-- WS-G7/WS-H12d/AH1-C-2: When the policy denies flow and the message is
within bounds, the dual-queue checked send returns `flowDenied` without
modifying state.
WS-H12d: Bounds checks precede the flow check, so the theorem requires
`msg.checkBounds = true` to guarantee the flow-denied path is reached. -/
theorem endpointSendDualChecked_flowDenied
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState)
    (hBounds : msg.checkBounds = true)
    (hDeny : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = false) :
    endpointSendDualChecked ctx endpointId sender msg endpointRights
        senderCspaceRoot receiverSlotBase st =
      .error .flowDenied := by
  unfold endpointSendDualChecked
  have ⟨hR, hC⟩ := (IpcMessage.checkBounds_iff_bounded msg).mp hBounds
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from Nat.not_lt.mpr hR, ite_false]
  simp only [show ¬(maxExtraCaps < msg.caps.size) from Nat.not_lt.mpr hC, ite_false]
  simp [hDeny]

/-- When the policy allows flow, the checked mint behaves identically to the
CDT-tracked mint. -/
theorem cspaceMintChecked_eq_cspaceMintWithCdt_when_allowed
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.objectLabelOf src.cnode)
               (ctx.objectLabelOf dst.cnode) = true) :
    cspaceMintChecked ctx src dst rights badge st =
      cspaceMintWithCdt src dst rights badge st := by
  unfold cspaceMintChecked
  simp [hFlow]

/-- When the policy denies flow, the checked mint returns `flowDenied`
without modifying state. -/
theorem cspaceMintChecked_flowDenied
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.objectLabelOf src.cnode)
               (ctx.objectLabelOf dst.cnode) = false) :
    cspaceMintChecked ctx src dst rights badge st =
      .error .flowDenied := by
  unfold cspaceMintChecked
  simp [hDeny]

-- ============================================================================
-- WS-E5/M-07: Enforcement boundary specification
-- ============================================================================

/-! ## M-07 — Enforcement Boundary Specification

This section formally classifies all kernel operations into enforcement categories
and proves that the policy-checked wrappers are sufficient for the enforcement
boundary.

**Canonical classification (22 operations — V2-B/C updated):**

| Category | Operations |
|---|---|
| **Policy-gated** (11) | `endpointSendDualChecked`, `endpointReceiveDualChecked`, `endpointCallChecked` (U5-B), `endpointReplyChecked` (U5-C), `cspaceMintChecked`, `cspaceCopyChecked`, `cspaceMoveChecked`, `notificationSignalChecked`, `registerServiceChecked`, `notificationWaitChecked` (V2-A), `endpointReplyRecvChecked` (V2-C) |
| **Capability-only** (7) | `cspaceLookupSlot`, `cspaceInsertSlot`, `cspaceDeleteSlot`, `cspaceRevoke`, `lifecycleRetypeObject`, `lifecycleRevokeDeleteRetype`, `storeObject` |
| **Read-only** (4) | `chooseThread`, `lookupObject`, `lookupService`, `cspaceResolvePath` |

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

/-- WS-E5/M-07/Q1-D/U5-B/U5-C/V2-B/C/Z8-M/D1/D2: Canonical enforcement boundary
classification table (33 entries). V2-B/C added `notificationWaitChecked` and
`endpointReplyRecvChecked`. Z8-M added 3 SchedContext capability-only operations.
D1 added 2 thread lifecycle capability-only operations.
D2 added 2 priority management capability-only operations.
Operations with both policy-gated and capability-only variants are classified
under their policy-gated variant here (the checked dispatch path uses the
policy-gated variant; the unchecked dispatch path uses the capability-only
variant). -/
def enforcementBoundary : List EnforcementClass :=
  [ -- Policy-gated: cross-domain operations checked via securityFlowsTo
    .policyGated "endpointSendDualChecked"
  , .policyGated "endpointReceiveDualChecked"
  , .policyGated "endpointCallChecked"       -- U5-B: previously inline check
  , .policyGated "endpointReplyChecked"      -- U5-C: defense-in-depth
  , .policyGated "cspaceMintChecked"
  , .policyGated "cspaceCopyChecked"
  , .policyGated "cspaceMoveChecked"
  , .policyGated "notificationSignalChecked"
  , .policyGated "registerServiceChecked"
  , .policyGated "notificationWaitChecked"        -- V2-A: notification wait IF check
  , .policyGated "endpointReplyRecvChecked"       -- V2-C: compound reply+recv IF check
  -- Capability-only: authority derived from capability possession
  , .capabilityOnly "cspaceLookupSlot"
  , .capabilityOnly "cspaceInsertSlot"
  , .capabilityOnly "cspaceDeleteSlot"
  , .capabilityOnly "cspaceRevoke"
  -- Read-only: no state mutation
  , .readOnly "chooseThread"
  , .readOnly "lookupObject"
  , .readOnly "lookupService"
  , .readOnly "cspaceResolvePath"
  -- Internal/lifecycle: building blocks used under capability-guarded contexts
  , .capabilityOnly "lifecycleRetypeObject"
  , .capabilityOnly "lifecycleRevokeDeleteRetype"
  , .capabilityOnly "storeObject"
  -- Z8-M: SchedContext capability-only operations (authority from cap possession)
  , .capabilityOnly "schedContextConfigure"
  , .capabilityOnly "schedContextBind"
  , .capabilityOnly "schedContextUnbind"
  -- D1: Thread lifecycle capability-only operations (authority from cap possession)
  , .capabilityOnly "suspendThread"
  , .capabilityOnly "resumeThread"
  -- D2: Priority management capability-only operations (authority from cap + MCP)
  , .capabilityOnly "setPriority"
  , .capabilityOnly "setMCPriority"
  -- D3: IPC buffer configuration capability-only operation
  , .capabilityOnly "setIPCBuffer"
  -- AC4-D: VSpace operations (capability-only; internally delegate to storeObject)
  , .capabilityOnly "vspaceMapPageCheckedWithFlushFromState"
  , .capabilityOnly "vspaceUnmapPageWithFlush"
  -- AC4-D: Service revocation (capability-only; operates on serviceRegistry)
  , .capabilityOnly "revokeService"
  ]

-- ============================================================================
-- AC4-D/IF-01: Enforcement boundary completeness witness
-- ============================================================================

/-- AC4-D: Map each `SyscallId` to the name of its corresponding enforcement
    boundary entry. This bridges the typed `SyscallId` inductive to the
    string-based `EnforcementClass` list, enabling compile-time completeness
    verification. -/
def syscallIdToEnforcementName : SyscallId → String
  | .send                  => "endpointSendDualChecked"
  | .receive               => "endpointReceiveDualChecked"
  | .call                  => "endpointCallChecked"
  | .reply                 => "endpointReplyChecked"
  | .cspaceMint            => "cspaceMintChecked"
  | .cspaceCopy            => "cspaceCopyChecked"
  | .cspaceMove            => "cspaceMoveChecked"
  | .cspaceDelete          => "cspaceDeleteSlot"
  | .lifecycleRetype       => "lifecycleRetypeObject"
  | .vspaceMap             => "vspaceMapPageCheckedWithFlushFromState"
  | .vspaceUnmap           => "vspaceUnmapPageWithFlush"
  | .serviceRegister       => "registerServiceChecked"
  | .serviceRevoke         => "revokeService"
  | .serviceQuery          => "lookupService"
  | .notificationSignal    => "notificationSignalChecked"
  | .notificationWait      => "notificationWaitChecked"
  | .replyRecv             => "endpointReplyRecvChecked"
  | .schedContextConfigure => "schedContextConfigure"
  | .schedContextBind      => "schedContextBind"
  | .schedContextUnbind    => "schedContextUnbind"
  | .tcbSuspend            => "suspendThread"
  | .tcbResume             => "resumeThread"
  | .tcbSetPriority        => "setPriority"
  | .tcbSetMCPriority      => "setMCPriority"
  | .tcbSetIPCBuffer       => "setIPCBuffer"

/-- AC4-D: Check whether every SyscallId maps to an operation name present in
    the enforcement boundary list. Returns `true` iff every syscall is covered. -/
def enforcementBoundaryComplete : Bool :=
  SyscallId.all.all (fun sid =>
    let name := syscallIdToEnforcementName sid
    enforcementBoundary.any (fun ec =>
      match ec with
      | .policyGated n | .capabilityOnly n | .readOnly n => n == name))

/-- AC4-D/IF-01: **Compile-time completeness theorem** — every `SyscallId` variant
    maps to an operation present in the enforcement boundary.

    This theorem fails at compile time if:
    - A new `SyscallId` variant is added without updating `syscallIdToEnforcementName`.
    - A `syscallIdToEnforcementName` mapping references a name absent from
      `enforcementBoundary`.
    - An `enforcementBoundary` entry is removed that was the sole coverage for
      a `SyscallId` variant. -/
-- AF4-A: Replaced `native_decide` with `decide` to remove Lean runtime
-- evaluator from the TCB. The 25-element SyscallId enumeration is small enough
-- for the kernel-checked `decide` tactic (may increase compile time slightly).
theorem enforcementBoundary_is_complete :
    enforcementBoundaryComplete = true := by decide

-- ============================================================================
-- WS-E5/M-07: Denied-preserves-state theorems
-- ============================================================================

/-- AH1-C-3: When the policy denies flow, `endpointSendDualChecked` produces no
state change. WS-H12d: Bounds checks precede the flow check but also produce
errors, so the conclusion ¬∃ r st' still holds unconditionally. -/
theorem endpointSendDualChecked_denied_preserves_state
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = false) :
    ¬∃ (r : CapTransferSummary) (st' : SystemState),
        endpointSendDualChecked ctx endpointId
        sender msg endpointRights senderCspaceRoot receiverSlotBase st =
        .ok (r, st') := by
  intro ⟨r, st', h⟩
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
    (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.objectLabelOf src.cnode)
               (ctx.objectLabelOf dst.cnode) = false) :
    ¬∃ st', cspaceMintChecked ctx src dst rights badge st = .ok ((), st') := by
  intro ⟨st', h⟩
  simp [cspaceMintChecked, hDeny] at h

-- ============================================================================
-- WS-E5/M-07: Enforcement sufficiency theorems (complete disjunction)
-- ============================================================================

/-- WS-H12d/AH1: `endpointSendDualChecked` either returns a bounds error,
delegates to WithCaps (when flow allowed), or returns `flowDenied` (when denied).
This is the complete disjunction of enforcement outcomes.
AH1: Updated target from `endpointSendDual` to `endpointSendDualWithCaps`. -/
theorem enforcement_sufficiency_endpointSendDual
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState) :
    (msg.registers.size > maxMessageRegisters ∧
       endpointSendDualChecked ctx endpointId sender msg endpointRights
         senderCspaceRoot receiverSlotBase st = .error .ipcMessageTooLarge) ∨
    (msg.caps.size > maxExtraCaps ∧
       endpointSendDualChecked ctx endpointId sender msg endpointRights
         senderCspaceRoot receiverSlotBase st = .error .ipcMessageTooManyCaps) ∨
    (securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = true ∧
       endpointSendDualChecked ctx endpointId sender msg endpointRights
         senderCspaceRoot receiverSlotBase st =
       endpointSendDualWithCaps endpointId sender msg endpointRights
         senderCspaceRoot receiverSlotBase st) ∨
    (securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = false ∧
       endpointSendDualChecked ctx endpointId sender msg endpointRights
         senderCspaceRoot receiverSlotBase st = .error .flowDenied) := by
  unfold endpointSendDualChecked endpointSendDualWithCaps
  by_cases hR : maxMessageRegisters < msg.registers.size
  · left; exact ⟨hR, by simp [hR]⟩
  · by_cases hC : maxExtraCaps < msg.caps.size
    · right; left; exact ⟨hC, by simp [hR, hC]⟩
    · cases hFlow : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) with
      | true => right; right; left; exact ⟨rfl, by simp [hR, hC, hFlow]⟩
      | false => right; right; right; exact ⟨rfl, by simp [hR, hC, hFlow]⟩

/-- `cspaceMintChecked` either delegates to CDT-tracked mint or returns `flowDenied`. -/
theorem enforcement_sufficiency_cspaceMint
    (ctx : LabelingContext) (src dst : CSpaceAddr)
    (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (st : SystemState) :
    (securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true ∧
       cspaceMintChecked ctx src dst rights badge st = cspaceMintWithCdt src dst rights badge st) ∨
    (securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = false ∧
       cspaceMintChecked ctx src dst rights badge st = .error .flowDenied) := by
  cases hFlow : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) with
  | true => left; exact ⟨rfl, by simp [cspaceMintChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [cspaceMintChecked, hFlow]⟩

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
-- WS-Q1: Service registration enforcement wrapper
-- ============================================================================

/-- WS-Q1/Q1-D: Policy-checked service registration: verifies that information
may flow from the registering thread's security domain to the service's security
domain before delegating to `registerService`.

Service registration binds a service identity to an endpoint capability,
creating a persistent mapping that reveals the registrar's intent. The wrapper
gates on `securityFlowsTo` from the thread's domain to the service's domain.

Returns `flowDenied` when `securityFlowsTo threadLabel serviceLabel = false`. -/
def registerServiceChecked
    (ctx : LabelingContext)
    (caller : SeLe4n.ThreadId)
    (reg : ServiceRegistration) : Kernel Unit :=
  fun st =>
    let threadLabel := ctx.threadLabelOf caller
    let serviceLabel := ctx.serviceLabelOf reg.sid
    if securityFlowsTo threadLabel serviceLabel then
      registerService reg st
    else
      .error .flowDenied

-- ============================================================================
-- U5-B/U-M01: endpointCall enforcement wrapper
-- ============================================================================

/-- U5-B/U-M01: Policy-checked endpoint call using the WithCaps path.
Verifies that information may flow from the caller's security domain to the
endpoint's security domain, then delegates to `endpointCallWithCaps`.

Previously, `dispatchWithCapChecked` performed this check inline with a
raw `securityFlowsTo` guard. This wrapper centralizes the enforcement in
the same layer as all other policy-gated operations.

Returns `flowDenied` when `securityFlowsTo callerLabel endpointLabel = false`. -/
def endpointCallChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) : Kernel CapTransferSummary :=
  fun st =>
    let callerLabel := ctx.threadLabelOf caller
    let endpointLabel := ctx.endpointLabelOf endpointId
    if securityFlowsTo callerLabel endpointLabel then
      endpointCallWithCaps endpointId caller msg endpointRights
        callerCspaceRoot receiverSlotBase st
    else
      .error .flowDenied

-- ============================================================================
-- U5-C/U-M04: Reply enforcement wrapper
-- ============================================================================

/-- U5-C/U-M04: Policy-checked endpoint reply.
Verifies that information may flow from the replier's security domain to the
target thread's security domain before delegating to `endpointReply`.

**Design rationale**: In seL4, the reply capability is single-use authority
that is consumed upon use. The flow check here is a defense-in-depth measure:
reply caps inherently limit the scope of information flow to the original
call chain. However, routing through the enforcement layer ensures the
reply path is auditable and consistent with all other cross-domain operations.

Returns `flowDenied` when `securityFlowsTo replierLabel targetLabel = false`. -/
def endpointReplyChecked
    (ctx : LabelingContext)
    (replier : SeLe4n.ThreadId)
    (target : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    let replierLabel := ctx.threadLabelOf replier
    let targetLabel := ctx.threadLabelOf target
    if securityFlowsTo replierLabel targetLabel then
      endpointReply replier target msg st
    else
      .error .flowDenied

/-- V2-A: Policy-checked notification wait: verifies that information may flow
from the notification's domain to the waiter's domain before delegating to
`notificationWait`.

The waiter learns about the notification state (badge value or blocking);
the wrapper gates on `securityFlowsTo` from notification to waiter domain.

Returns `flowDenied` when `securityFlowsTo notificationLabel waiterLabel = false`. -/
def notificationWaitChecked
    (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) : Kernel (Option SeLe4n.Badge) :=
  fun st =>
    let waiterLabel := ctx.threadLabelOf waiter
    let notificationLabel := ctx.objectLabelOf notificationId
    if securityFlowsTo notificationLabel waiterLabel then
      notificationWait notificationId waiter st
    else
      .error .flowDenied

/-- V2-C: Policy-checked endpointReplyRecv: verifies that information may flow
from the replier's domain to the reply target's domain (for the reply leg),
and from the endpoint's domain to the receiver's domain (for the receive leg).

This is a compound operation (reply + receive). Both legs must satisfy their
respective flow checks.

Returns `flowDenied` if either flow check fails. -/
def endpointReplyRecvChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    let receiverLabel := ctx.threadLabelOf receiver
    let targetLabel := ctx.threadLabelOf replyTarget
    let endpointLabel := ctx.endpointLabelOf endpointId
    -- Reply leg: receiver → replyTarget
    if securityFlowsTo receiverLabel targetLabel then
      -- Receive leg: endpoint → receiver
      if securityFlowsTo endpointLabel receiverLabel then
        endpointReplyRecv endpointId receiver replyTarget msg st
      else
        .error .flowDenied
    else
      .error .flowDenied


