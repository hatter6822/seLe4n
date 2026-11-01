-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
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
    (payload : SendPayload)
    (receiverSlotBase : SeLe4n.Slot) : Kernel CapTransferSummary :=
  fun st =>
    let senderLabel := ctx.threadLabelOf sender
    let endpointLabel := ctx.endpointLabelOf endpointId
    -- WS-SM SM8.C: the global lattice check AND this endpoint's configured
    -- override. A conjunction, so the override can only narrow.
    if endpointFlowGate ctx endpointId senderLabel endpointLabel then
      endpointSendDualWithCaps endpointId sender payload receiverSlotBase st
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
    (payload : SendPayload)
    (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = true)
    -- WS-SM SM8.C: the endpoint's own override must admit the flow too. Not a
    -- free premise: it is exactly what a configured deployment can deny, and
    -- `endpointOverrideAllows_default` discharges it where none is configured.
    (hOverride : endpointOverrideAllows ctx endpointId (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = true) :
    endpointSendDualChecked ctx endpointId sender payload receiverSlotBase st =
      endpointSendDualWithCaps endpointId sender payload receiverSlotBase st := by
  have hGate := endpointFlowGate_of ctx endpointId _ _ hFlow hOverride
  -- Verified load-bearing: dropping `hGate` leaves the
  -- `if endpointFlowGate … then … else .flowDenied` unreduced, so `hOverride`
  -- is a real premise rather than decoration.
  simp only [endpointSendDualChecked, hGate, ↓reduceIte]

/-- WS-G7/AH1-C-2: When the policy denies flow, the dual-queue checked send
returns `flowDenied` without modifying state.  WS-ZA ZA4.7: the send carries
no message to bound -- its words are its frame's, cut to at most
`maxMessageRegisters` -- so the flow gate is its first check. -/
theorem endpointSendDualChecked_flowDenied
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (payload : SendPayload)
    (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = false) :
    endpointSendDualChecked ctx endpointId sender payload receiverSlotBase st =
      .error .flowDenied := by
  unfold endpointSendDualChecked
  -- WS-SM SM8.C: a denied global flow denies the gate whatever the override
  -- says, so this theorem keeps the hypothesis it had before the gate existed.
  simp [endpointFlowGate_false_of_securityFlowsTo_false ctx endpointId _ _ hDeny]

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

**Canonical classification (21 operations):**

| Category | Operations |
|---|---|
| **Policy-gated** (13) | `endpointSendDualChecked`, `endpointReceiveDualChecked`, `endpointCallChecked` (U5-B), `endpointReplyChecked` (U5-C), `cspaceMintChecked`, `cspaceCopyChecked`, `cspaceMoveChecked`, `notificationSignalChecked`, `registerServiceChecked`, `lookupServiceChecked`, `revokeServiceChecked`, `notificationWaitChecked` (V2-A), `endpointReplyRecvChecked` (V2-C) |
| **Capability-only** (5) | `cspaceLookupSlot`, `cspaceInsertSlot`, `cspaceDeleteSlot`, `cspaceRevoke`, `storeObject` |
| **Read-only** (3) | `chooseThread`, `lookupObject`, `cspaceResolvePath` |

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
classification table.

The entry count is **not** restated here: it is pinned by
`enforcementBoundaryExtended_count` (`Enforcement/Soundness.lean`), which is the
authority, and a number repeated in prose goes stale the first time an entry
lands without a docstring edit — as this one did, having read "33 entries"
across six subsequent expansions. Read the theorem.

Operations with both policy-gated and capability-only variants are classified
under their policy-gated variant here (the checked dispatch path uses the
policy-gated variant; the unchecked dispatch path uses the capability-only
variant). -/
def enforcementBoundary : List EnforcementClass :=
  [ -- Policy-gated: cross-domain operations checked via securityFlowsTo
    .policyGated "endpointSendDualChecked"
  , .policyGated "endpointReceiveDualChecked"
  , .policyGated "endpointCallChecked" -- U5-B: previously inline check
  , .policyGated "endpointReplyChecked" -- U5-C: defense-in-depth
  , .policyGated "cspaceMintChecked"
  , .policyGated "cspaceCopyChecked"
  , .policyGated "cspaceMoveChecked"
  , .policyGated "notificationSignalChecked"
  , .policyGated "registerServiceChecked"
  , .policyGated "lookupServiceChecked"
  , .policyGated "revokeServiceChecked"
  , .policyGated "notificationWaitChecked" -- V2-A: notification wait IF check
  , .policyGated "endpointReplyRecvChecked" -- V2-C: compound reply+recv IF check
  -- Capability-only: authority derived from capability possession
  , .capabilityOnly "cspaceLookupSlot"
  , .capabilityOnly "cspaceInsertSlot"
  , .capabilityOnly "cspaceDeleteSlot"
  , .capabilityOnly "cspaceRevoke"
  -- **WS-BP BP7.1 (`v0.36.7`)**: the two destroying arms' live transitions —
  -- the delete and the CDT revocation, each followed by the removal of every
  -- mapping a destroyed frame capability recorded (seL4's `finaliseCap`).
  -- Capability-only: the authority is the CNode capability the delete and the
  -- revocation already demand; what the teardown removes is mappings whose
  -- capabilities the caller is destroying, so no principal loses access it
  -- still holds authority for.  The inner `cspaceDeleteSlot` entry stays, as
  -- the internal step other composites reach.  (WS-RR RR8.16's
  -- `cspaceRevokeCdt` entry left with the general revocation it named, at
  -- WS-ZA ZA5.3 part 8, `v0.36.111`: the revoke arm's live transition is the
  -- finalising loop below.)
  , .capabilityOnly "cspaceDeleteSlotZombie"
  , .capabilityOnly "cspaceRevokeCdtFinalising"
  -- **WS-BP BP7.1 (`v0.36.5`)**: the untyped carve, named at the transition the
  -- live `.untypedRetype` arm calls — the decode, the two slot resolutions and
  -- `untypedRetypeObject` behind them.  Capability-only: the authority is the
  -- untyped capability (its `.retype` right) and a writable capability to the
  -- destination CNode, and nothing flows between labelled principals — the
  -- carved memory is fresh and a RAM page is zeroed before any capability to it
  -- exists.
  , .capabilityOnly "untypedRetypeFromCap"
  -- **WS-BP BP7.1 (`v0.36.6`)**: the untyped reset, the transition the live
  -- `.untypedReset` arm calls.  Capability-only: the authority is the untyped
  -- capability's `.retype` right — authority over the memory it hands back.
  -- Since WS-ZA ZA5.4 the reset is seL4's: `untypedResetFromCap` resolves the
  -- invoked slot, refuses while that slot has a derivation child or the
  -- untyped records a carved object, and writes `0` to the slot's free index —
  -- a word of the caller's own capability.  It removes no object, mapping or
  -- capability, so no principal loses anything it holds.
  , .capabilityOnly "untypedResetFromCap"
  -- Read-only: no state mutation
  , .readOnly "chooseThread"
  , .readOnly "lookupObject"
  , .readOnly "cspaceResolvePath"
  -- Internal/lifecycle: building blocks used under capability-guarded contexts
  , .capabilityOnly "storeObject"
  -- Z8-M: SchedContext capability-only operations (authority from cap possession)
  , .capabilityOnly "schedControlConfigure"
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
  -- WS-SM SM5.H.4: CPU-affinity configuration capability-only operation
  , .capabilityOnly "setThreadCpuAffinity"
  -- PR #887 review round: fault-handler configuration (seL4 `TCB_SetSpace`'s
  -- `fault_ep`). Capability-only: the authority is the TCB capability's write
  -- right, the candidate CPtr is validated through the *target's* CSpace at
  -- set time, and the write touches one TCB field — no data crosses a label
  -- boundary until the thread faults, and that delivery is policy-gated by
  -- `faultDeliverOnCoreChecked`.
  , .capabilityOnly "setThreadFaultHandlerOp"
  -- **WS-BP BP7.1 (`v0.36.11`)**: `seL4_TCB_SetSpace`'s roots.  Capability-only:
  -- the authority is the TCB capability's write right plus the caller's own
  -- capabilities to the two roots (`resolveSetSpace`: `.grant`+`.write` on the
  -- CNode, `.write` on the VSpace root), and the write touches one suspended
  -- TCB's two space slots and the derivation links of those slots, their
  -- sources and neighbours — no data crosses a label boundary.  WS-ZA ZA5.4
  -- part 26: named at the transition the live arm calls, which deletes an old
  -- CSpace root that is the last capability to a populated CNode through the
  -- zombie loop first, under the same authority as the delete's.
  , .capabilityOnly "copyThreadSpacesZombie"
  -- **WS-BP BP7.1 (`v0.36.12`)**: intermediate page tables.  Capability-only:
  -- the authority is the table capability's write right plus, for the install,
  -- the caller's own `.write` capability to the address space — and what moves
  -- is which page an address space's walk passes through, never data.
  , .capabilityOnly "pageTableMap"
  , .capabilityOnly "pageTableUnmap"
  -- **WS-ZA ZA4.3**: the yield (`seL4_Yield` under MCS).  It invokes no
  -- capability at all: its authority is being the thread current on the
  -- executing core, which the dispatcher checks first.  Listed with the
  -- capability-only operations because, like them, it needs no flow check — it
  -- writes the caller's own allotment and the executing core's queues, the
  -- writes the timer tick makes when that allotment runs out, and carries no
  -- data across a label boundary.
  , .capabilityOnly "yieldOnCore"
  -- WS-ZA ZA6.9: the Consumed invocation, a SchedContext capability's.
  , .capabilityOnly "schedContextConsumedOnCore"
  -- WS-SM SM6.B: notification-binding capability-only operations (seL4
  -- NotificationBind / UnbindNotification — mutate the boundTCB ⇄ boundNotification
  -- relation; gated by the TCB capability, not an information-flow policy)
  , .capabilityOnly "bindNotification"
  , .capabilityOnly "unbindNotification"
  -- WS-SM SM6.D / PR #822 Phase H: mint a reply cap from an `.object`-to-Reply cap
  -- (authority from holding the object cap to the Reply; no information-flow policy —
  -- a local CSpace cap derivation, CDT-tracked like the other mint paths).
  , .capabilityOnly "mintReplyCapWithCdt"
  -- AC4-D: VSpace operations (capability-only; internally delegate to storeObject)
  , .capabilityOnly "vspaceMapPageCheckedWithShootdownFromState"
  , .capabilityOnly "vspaceUnmapPageWithShootdown"
  -- WS-SM SM7.D: instruction/data unification of one mapped page (seL4
  -- Page_Unify_Instruction). Capability-only: it modifies no page table and
  -- carries no message payload — it publishes the caller's *own* stores to the
  -- Point of Unification and drops the corresponding instruction lines. The
  -- authority is the `.write` right on the page's capability (you may publish
  -- code you were able to write); there is no information-flow policy to
  -- consult, because no data crosses a label boundary.
  , .capabilityOnly "vspaceUnifyInstructionPage"
  -- WS-SM SM8.C.9: the live declassification. **Policy-gated**, and it is the
  -- one entry whose gate is not `securityFlowsTo`: it runs the two-check
  -- `declassificationDecision` (base policy must *deny*, declassification policy
  -- must permit), which is the only way a flow the lattice forbids is ever
  -- admitted. Classifying it capability-only would say the capability alone
  -- authorizes the downgrade, which is exactly what it does not.
  , .policyGated "declassifyObjectFromCore"
  -- WS-SM SM9.C.8: the *data-carrying* declassification. **Policy-gated**, and
  -- for the same reason as its sibling above — it runs
  -- `declassificationDecision` at each hop, so a flow the lattice forbids is
  -- admitted only where the declassification policy says so.
  --
  -- What makes this entry different from `declassifyObjectFromCore` is that it
  -- gates **two** hops: the signaller into the notification, and the
  -- notification onward into the *resolved receiver*. A classification naming
  -- only the first would be the badge-leak class SM6.B closed at v0.31.73 —
  -- an authorized signaller aimed at a sink the policy never authorized — so
  -- the boundary entry names the transition that performs both checks, not the
  -- ordinary `notificationSignalBoundOnCore` it wraps.
  --
  -- The label is the LIVE entry the `.declassifySignal` arm calls (the PR #870
  -- round-5 rule): the executing core, and hence both the actor identity the
  -- audit records and the wake target, are read from the state inside it.
  , .policyGated "notificationSignalDeclassifiedCrossCoreDispatch"
  -- WS-SM SM9.A.11: the declassification audit trail's reader and drain.
  -- **Capability-only**, and the classification is the honest one rather than
  -- the flattering one. Neither consults an information-flow *policy* the way
  -- `declassifyObjectFromCore` does: what they consult is the caller's own
  -- clearance, and they use it to *filter* what is returned rather than to
  -- admit or deny a flow the lattice forbids. A `.policyGated` classification
  -- would claim a policy decision they do not make; `.readOnly` would claim the
  -- drain changes nothing, which is false of a transition that removes entries
  -- and advances the epoch.
  --
  -- The authority is a dedicated `CapTarget.auditTrail` capability
  -- (`extractAuditAuthority`), *not* a right on an arbitrary capability — the
  -- v0.32.97 confused-deputy class — with `.read` and `.write` as the second
  -- gate so a monitoring deployment can hand out a reader that cannot drain.
  --
  -- PR #870 review (P2): the reader's entry is `auditReadFromCore` — the LIVE
  -- entry point the `.auditRead` arm calls, whose subject-resolution seam
  -- (the reader's clearance read off the running thread, never off an operand)
  -- is precisely what the boundary exists to audit. Its first cut named the
  -- inner query `auditReadWord`, which takes a caller-supplied reader domain —
  -- so the coverage checks would have stayed green had the live seam drifted
  -- onto exactly the confused-clearance shape the entry point exists to
  -- prevent. The drain's label was the live entry from the start.
  , .capabilityOnly "auditReadFromCore"
  , .capabilityOnly "auditDrainVisiblePrefix"
  -- WS-SM SM8.E.3: the SM3 two-phase-locking bracket, promoted here from the
  -- separate per-core list SM8.B introduced. **Capability-only**, and for the
  -- same reason as `storeObject`'s: it is an
  -- internal building block invoked under an already-capability-guarded
  -- context, and it consults no information-flow policy — the bracket cannot
  -- admit a flow the guarded transition would not admit, because it carries no
  -- data across a label boundary at all (`withLockSet_preserves_projection`,
  -- which holds *unconditionally* once SM8.B.4 erased the per-object `lock`
  -- from the projection). What it does add is the lock-contention timing
  -- channel the covert-channel inventory registers as CC-5, bounded rather
  -- than closed by SM8.D (`lockContention_delay_bounded`).
  --
  -- Appended **last** deliberately: it makes the per-core boundary
  -- (`enforcementBoundaryPerCore`, which was this list plus the bracket plus
  -- the cross-core wrappers) the identical list it already was, so the
  -- promotion moves one entry between two definitions and changes no third
  -- thing. `enforcementBoundary_classifies_withLockSet` is where that is
  -- checked rather than argued.
  , .capabilityOnly "withLockSet"
  ]

-- ============================================================================
-- AC4-D/IF-01: Enforcement boundary completeness witness
-- ============================================================================

/-- AC4-D: Map each `SyscallId` to the name of its corresponding enforcement
    boundary entry. This bridges the typed `SyscallId` inductive to the
    string-based `EnforcementClass` list, enabling compile-time completeness
    verification. -/
def syscallIdToEnforcementName : SyscallId → String
  | .send => "endpointSendDualChecked"
  | .receive => "endpointReceiveDualChecked"
  | .call => "endpointCallChecked"
  | .reply => "endpointReplyChecked"
  | .cspaceMint => "cspaceMintChecked"
  | .cspaceCopy => "cspaceCopyChecked"
  | .cspaceMove => "cspaceMoveChecked"
  | .cspaceDelete => "cspaceDeleteSlotZombie"
  | .cspaceRevoke => "cspaceRevokeCdtFinalising"
  | .untypedRetype => "untypedRetypeFromCap"
  | .untypedReset => "untypedResetFromCap"
  | .vspaceMap => "vspaceMapPageCheckedWithShootdownFromState"
  | .vspaceUnmap => "vspaceUnmapPageWithShootdown"
  | .serviceRegister => "registerServiceChecked"
  | .serviceRevoke => "revokeServiceChecked"
  | .serviceQuery => "lookupServiceChecked"
  | .notificationSignal => "notificationSignalChecked"
  | .notificationWait => "notificationWaitChecked"
  | .replyRecv => "endpointReplyRecvChecked"
  | .schedContextConfigure => "schedControlConfigure"
  | .schedContextBind => "schedContextBind"
  | .schedContextUnbind => "schedContextUnbind"
  | .tcbSuspend => "suspendThread"
  | .tcbResume => "resumeThread"
  | .tcbSetPriority => "setPriority"
  | .tcbSetMCPriority => "setMCPriority"
  | .tcbSetIPCBuffer => "setIPCBuffer"
  | .tcbSetAffinity => "setThreadCpuAffinity"
  | .tcbSetFaultHandler => "setThreadFaultHandlerOp"
  | .tcbSetSpace => "copyThreadSpacesZombie"
  | .pageTableMap => "pageTableMap"
  | .pageTableUnmap => "pageTableUnmap"
  | .yield => "yieldOnCore"
  | .schedContextConsumed => "schedContextConsumedOnCore"
  | .tcbBindNotification => "bindNotification"
  | .tcbUnbindNotification => "unbindNotification"
  | .mintReplyCap => "mintReplyCapWithCdt"
  | .vspaceUnifyInstruction => "vspaceUnifyInstructionPage"
  | .declassify => "declassifyObjectFromCore"
  | .declassifySignal => "notificationSignalDeclassifiedCrossCoreDispatch"
  | .auditRead => "auditReadFromCore"
  | .auditDrain => "auditDrainVisiblePrefix"

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
-- evaluator from the TCB. The 26-element SyscallId enumeration is small enough
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
    (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf sender)
               (ctx.endpointLabelOf endpointId) = false) :
    ¬∃ (r : CapTransferSummary) (st' : SystemState),
        endpointSendDualChecked ctx endpointId sender payload receiverSlotBase st =
        .ok (r, st') := by
  intro ⟨r, st', h⟩
  rw [endpointSendDualChecked_flowDenied ctx endpointId sender payload receiverSlotBase st
    hDeny] at h
  cases h

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

/-- AH1: `endpointSendDualChecked` either delegates to WithCaps (when flow
allowed) or returns `flowDenied` (when denied).  This is the complete
disjunction of enforcement outcomes; WS-ZA ZA4.7 retired the two bounds
outcomes with the message argument they checked. -/
theorem enforcement_sufficiency_endpointSendDual
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState) :
    -- WS-SM SM8.C: the two flow disjuncts are stated against `endpointFlowGate`,
    -- the predicate the wrapper actually branches on.
    (endpointFlowGate ctx endpointId (ctx.threadLabelOf sender)
        (ctx.endpointLabelOf endpointId) = true ∧
       endpointSendDualChecked ctx endpointId sender payload receiverSlotBase st =
       endpointSendDualWithCaps endpointId sender payload receiverSlotBase st) ∨
    (endpointFlowGate ctx endpointId (ctx.threadLabelOf sender)
        (ctx.endpointLabelOf endpointId) = false ∧
       endpointSendDualChecked ctx endpointId sender payload receiverSlotBase st =
         .error .flowDenied) := by
  unfold endpointSendDualChecked
  cases hFlow : endpointFlowGate ctx endpointId (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) with
  | true => left; exact ⟨rfl, by simp [hFlow]⟩
  | false => right; exact ⟨rfl, by simp [hFlow]⟩

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
    (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) : Kernel SeLe4n.ThreadId :=
  fun st =>
    let endpointLabel := ctx.endpointLabelOf endpointId
    let receiverLabel := ctx.threadLabelOf receiver
    -- WS-SM SM8.C: global check ∧ this endpoint's override.
    if endpointFlowGate ctx endpointId endpointLabel receiverLabel then
      endpointReceiveDual endpointId receiver replyId st
    else
      .error .flowDenied

-- ============================================================================
-- WS-Q1: Service registration enforcement wrapper
-- ============================================================================

/-- **The label of a service registration is its endpoint's object label.**

A registration has no identity apart from the endpoint it names: the endpoint
records it (`Endpoint.serviceRegistered`), the service query reads it back through a
capability to that endpoint, and the projection shows it exactly when it shows
the endpoint (`serviceObservable`).  So writing a registration is a write to the
endpoint, and reading one is a read of it; the two gates below are the write-up
and read-down checks on that one label.

A caller may write a registration on `epId` when its label flows to the
endpoint's. -/
def serviceEndpointWriteAdmitted (ctx : LabelingContext) (caller : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) : Bool :=
  securityFlowsTo (ctx.threadLabelOf caller) (ctx.objectLabelOf epId)

/-- A caller may read the registration recorded on `epId` when the endpoint's
label flows to its own. -/
def serviceEndpointReadAdmitted (ctx : LabelingContext) (caller : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) : Bool :=
  securityFlowsTo (ctx.objectLabelOf epId) (ctx.threadLabelOf caller)

/-- A registration may be written by `caller` when it names an endpoint the
caller may write.  One naming no object is refused here, as `registerService`
would refuse it. -/
def registrationWriteAdmitted (ctx : LabelingContext) (caller : SeLe4n.ThreadId)
    (reg : ServiceRegistration) : Bool :=
  match reg.endpointCap.target with
  | .object epId => serviceEndpointWriteAdmitted ctx caller epId
  | _ => false

/-- WS-Q1/Q1-D: Policy-checked service registration: information must be able
to flow from the registering thread to the endpoint the registration names
(`registrationWriteAdmitted`) before `registerService` runs.

Returns `flowDenied` otherwise. -/
def registerServiceChecked
    (ctx : LabelingContext)
    (caller : SeLe4n.ThreadId)
    (reg : ServiceRegistration) : Kernel Unit :=
  fun st =>
    if registrationWriteAdmitted ctx caller reg then
      registerService reg st
    else
      .error .flowDenied

/-- **WS-ZA ZA5.5**: an admitted checked registration — the flow check and
every `registerService` check passing on the state handed in — succeeds as
`registerServicePerform`, the write alone. -/
theorem registerServiceChecked_of_admitted (ctx : LabelingContext)
    (caller : SeLe4n.ThreadId) (reg : ServiceRegistration) (st : SystemState)
    (h : (registrationWriteAdmitted ctx caller reg && registerServiceAdmitted st reg) = true) :
    registerServiceChecked ctx caller reg st = .ok ((), registerServicePerform st reg) := by
  simp only [Bool.and_eq_true] at h
  unfold registerServiceChecked
  rw [if_pos h.1]
  exact registerService_of_admitted st reg h.2

/-- Policy-checked service query: the endpoint's label must flow to the caller's
(`serviceEndpointReadAdmitted`) before the registration it records is read.
The check reads labels only and precedes the lookup, so a refusal says nothing
about the registry; every other read a caller makes of an object it holds a
capability to is gated the same way (`notificationWaitChecked`, the receive
gate).

Returns `flowDenied` otherwise. -/
def lookupServiceChecked
    (ctx : LabelingContext)
    (caller : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) : Kernel ServiceRegistration :=
  fun st =>
    if serviceEndpointReadAdmitted ctx caller epId then
      lookupServiceByRecordedRegistration epId st
    else
      .error .flowDenied

/-- **The checked service query as the dispatcher runs it**: the policy-checked
lookup, its answer staged as the caller's return word (`x0` = the
registration's `ServiceId`, success in `x1`, no message registers).  The lookup
leaves the state, so the only write is the caller's return frame. -/
def serviceQueryStaged
    (ctx : LabelingContext)
    (caller : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) : Kernel Unit :=
  fun st =>
    match lookupServiceChecked ctx caller epId st with
    | .ok (reg, st') => .ok ((), Architecture.writeReturnFrameToTcb st' caller
        (Architecture.returnFrameOfWord reg.sid.val.toUInt64))
    | .error e => .error e

/-- Policy-checked service revocation: the caller's label must flow to the
endpoint's (`serviceEndpointWriteAdmitted`) before the registration that
endpoint records is removed (`revokeServiceByRecordedRegistration`).

Returns `flowDenied` otherwise. -/
def revokeServiceChecked
    (ctx : LabelingContext)
    (caller : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) : Kernel Unit :=
  fun st =>
    if serviceEndpointWriteAdmitted ctx caller epId then
      revokeServiceByRecordedRegistration epId st
    else
      .error .flowDenied

/-- **WS-ZA ZA5.5**: the checked query's write, total: the registration the
endpoint records staged as the caller's return word, written as the frame's
six words.  The word is the endpoint's own id (a service's identity is its
endpoint's), read off the endpoint's record with no table read (WS-ZA ZA5.8).
A state with no recorded registration is returned unchanged;
`recordedRegistrationPresent` rules it out. -/
@[inline] def serviceQueryPerform (st : SystemState) (caller : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) : SystemState :=
  match st.getObject? epId with
  | some (.endpoint ep) =>
    match ep.serviceRegistered with
    | false => st
    | true =>
      -- The frame's words written in place, no frame record built
      -- (`writeReturnFrameToTcb_ofWord_eq_words`).
      st.updateTcb caller
        (TCB.withReturnWords · (ServiceId.ofNat epId.toNat).val.toUInt64 0 0 0 0 0)
  | _ => st

/-- An admitted checked query — the read flow and the recorded registration —
succeeds as `serviceQueryPerform`. -/
theorem serviceQueryStaged_of_admitted (ctx : LabelingContext) (caller : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (st : SystemState)
    (h : (serviceEndpointReadAdmitted ctx caller epId && recordedRegistrationPresent st epId) =
      true) :
    serviceQueryStaged ctx caller epId st = .ok ((), serviceQueryPerform st caller epId) := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨hF, hP⟩ := h
  unfold recordedRegistrationPresent at hP
  unfold serviceQueryStaged lookupServiceChecked lookupServiceByRecordedRegistration serviceQueryPerform
  rw [if_pos hF]
  split at hP
  · next ep hObj =>
    simp only [hObj, hP, EndpointService.registrationAt_sid,
      Architecture.writeReturnFrameToTcb_ofWord_eq_words]
  · cases hP

/-- An admitted checked revoke — the write flow and the recorded registration —
succeeds as `revokeServiceByRecordedRegistrationPerform`. -/
theorem revokeServiceChecked_of_admitted (ctx : LabelingContext) (caller : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (st : SystemState)
    (h : (serviceEndpointWriteAdmitted ctx caller epId && recordedRegistrationPresent st epId) =
      true) :
    revokeServiceChecked ctx caller epId st =
      .ok ((), revokeServiceByRecordedRegistrationPerform st epId) := by
  simp only [Bool.and_eq_true] at h
  unfold revokeServiceChecked
  rw [if_pos h.1]
  exact revokeServiceByRecordedRegistration_of_admitted st epId h.2

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
    (payload : SendPayload)
    (receiverSlotBase : SeLe4n.Slot) : Kernel CapTransferSummary :=
  fun st =>
    let callerLabel := ctx.threadLabelOf caller
    let endpointLabel := ctx.endpointLabelOf endpointId
    -- WS-SM SM8.C: global check ∧ this endpoint's override.
    if endpointFlowGate ctx endpointId callerLabel endpointLabel then
      endpointCallWithCaps endpointId caller payload receiverSlotBase st
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

/-! ### WS-SM SM8.C — the gates the endpoint policy does *not* govern

`endpointPolicy` is per-**endpoint**, so it governs flows crossing an endpoint.
Three live gates are deliberately outside it: both notification gates (a
notification is not an endpoint) and the reply *leg* of `replyRecv` (which
carries `replier → prevCaller`, a thread-to-thread flow that crosses no
endpoint).

Left as prose in the SM8.C landing cut, which made the boundary a reading of the
code rather than a checked fact. These three theorems state it: each gate's
verdict is independent of the context's `endpointPolicy` field, so an operator
cannot configure one and expect it to reach these paths, and a future cut that
routes one of them through `endpointFlowGate` breaks the corresponding theorem
rather than silently changing what an override means. -/

/-- WS-SM SM8.C: the notification **signal** gate ignores `endpointPolicy` — a
notification is not an endpoint, so no per-endpoint override governs it. -/
theorem notificationSignalChecked_endpointPolicy_independent
    (ctx : LabelingContext) (epPolicy : EndpointFlowPolicy)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge) :
    notificationSignalChecked { ctx with endpointPolicy := epPolicy } notificationId
        signaler badge =
      notificationSignalChecked ctx notificationId signaler badge := rfl

/-- WS-SM SM8.C: and the notification **wait** gate, for the same reason. -/
theorem notificationWaitChecked_endpointPolicy_independent
    (ctx : LabelingContext) (epPolicy : EndpointFlowPolicy)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) :
    notificationWaitChecked { ctx with endpointPolicy := epPolicy } notificationId waiter =
      notificationWaitChecked ctx notificationId waiter := rfl

/-- WS-SM SM8.C: the **reply** gate ignores `endpointPolicy` — a reply carries
`replier → target`, a thread-to-thread flow that crosses no endpoint.

This is the theorem behind the `endpointReplyRecvChecked` comment that says the
override governs the receive leg and not the reply leg: the reply leg's gate is
this one, and it cannot see the field. -/
theorem endpointReplyChecked_endpointPolicy_independent
    (ctx : LabelingContext) (epPolicy : EndpointFlowPolicy)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) :
    endpointReplyChecked { ctx with endpointPolicy := epPolicy } replier target msg =
      endpointReplyChecked ctx replier target msg := rfl

/-- WS-SM SM8.C (**the load-bearing contrast**): the send gate is *not*
independent of `endpointPolicy`.

Without this the three theorems above would be consistent with a wiring in which
no gate reads the field at all — which is the state the SM8.B debt described. -/
theorem endpointSendDualChecked_endpointPolicy_dependent :
    ∃ (ctx : LabelingContext) (epPolicy : EndpointFlowPolicy) (endpointId : SeLe4n.ObjId)
      (senderLabel endpointLabel : SecurityLabel),
      endpointFlowGate { ctx with endpointPolicy := epPolicy } endpointId senderLabel
          endpointLabel ≠
        endpointFlowGate ctx endpointId senderLabel endpointLabel := by
  refine ⟨{ objectLabelOf := fun _ => SecurityLabel.publicLabel
            threadLabelOf := fun _ => SecurityLabel.publicLabel
            endpointLabelOf := fun _ => SecurityLabel.publicLabel },
          { endpointPolicy := fun _ => some { canFlow := fun _ _ => false } },
          ⟨0⟩, SecurityLabel.publicLabel, SecurityLabel.publicLabel, by decide⟩

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
    (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId) : Kernel Unit :=
  fun st =>
    let receiverLabel := ctx.threadLabelOf receiver
    let targetLabel := ctx.threadLabelOf replyTarget
    let endpointLabel := ctx.endpointLabelOf endpointId
    -- Reply leg: receiver → replyTarget.
    -- WS-SM SM8.C: the endpoint override is deliberately **not** consulted here.
    -- It governs flows that cross this endpoint, and the reply leg's pair names
    -- neither the endpoint's own label nor a flow through it — the reply travels
    -- to the caller the endpoint already admitted on the way in, which the
    -- receive leg below gates.
    if securityFlowsTo receiverLabel targetLabel then
      -- Receive leg: endpoint → receiver. WS-SM SM8.C: global check ∧ override.
      if endpointFlowGate ctx endpointId endpointLabel receiverLabel then
        endpointReplyRecv endpointId receiver replyTarget msg replyId st
      else
        .error .flowDenied
    else
      .error .flowDenied


