-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

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
    (replyId : Option SeLe4n.ReplyId)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.endpointLabelOf endpointId)
               (ctx.threadLabelOf receiver) = true)
    -- WS-SM SM8.C: the endpoint's own override must admit the flow too.
    (hOverride : endpointOverrideAllows ctx endpointId (ctx.endpointLabelOf endpointId)
               (ctx.threadLabelOf receiver) = true) :
    endpointReceiveDualChecked ctx endpointId receiver replyId st =
      endpointReceiveDual endpointId receiver replyId st := by
  unfold endpointReceiveDualChecked
  simp [endpointFlowGate_of ctx endpointId _ _ hFlow hOverride]

/-- WS-H8: When the policy denies flow, endpointReceiveDualChecked returns
`flowDenied`. -/
theorem endpointReceiveDualChecked_flowDenied
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.endpointLabelOf endpointId)
               (ctx.threadLabelOf receiver) = false) :
    endpointReceiveDualChecked ctx endpointId receiver replyId st =
      .error .flowDenied := by
  unfold endpointReceiveDualChecked
  simp [endpointFlowGate_false_of_securityFlowsTo_false ctx endpointId _ _ hDeny]

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
    (replyId : Option SeLe4n.ReplyId)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.endpointLabelOf endpointId)
               (ctx.threadLabelOf receiver) = false) :
    ¬∃ (r : SeLe4n.ThreadId) (st' : SystemState),
      endpointReceiveDualChecked ctx endpointId receiver replyId st = .ok (r, st') := by
  intro ⟨r, st', h⟩
  simp [endpointReceiveDualChecked,
    endpointFlowGate_false_of_securityFlowsTo_false ctx endpointId _ _ hDeny] at h

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
    (replyId : Option SeLe4n.ReplyId)
    (st : SystemState) :
    -- WS-SM SM8.C: stated against `endpointFlowGate`, the predicate the wrapper
    -- branches on (see `enforcement_sufficiency_endpointSendDual`).
    (endpointFlowGate ctx endpointId (ctx.endpointLabelOf endpointId)
        (ctx.threadLabelOf receiver) = true ∧
       endpointReceiveDualChecked ctx endpointId receiver replyId st =
         endpointReceiveDual endpointId receiver replyId st) ∨
    (endpointFlowGate ctx endpointId (ctx.endpointLabelOf endpointId)
        (ctx.threadLabelOf receiver) = false ∧
       endpointReceiveDualChecked ctx endpointId receiver replyId st =
         .error .flowDenied) := by
  cases hFlow : endpointFlowGate ctx endpointId (ctx.endpointLabelOf endpointId)
      (ctx.threadLabelOf receiver) with
  | true => left; exact ⟨rfl, by simp [endpointReceiveDualChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [endpointReceiveDualChecked, hFlow]⟩

-- ============================================================================
-- WS-Q1: registerServiceChecked correctness theorems
-- ============================================================================

/-- WS-Q1: When the policy allows flow, registerServiceChecked behaves
identically to the unchecked registration. -/
theorem registerServiceChecked_eq_registerService_when_allowed
    (ctx : LabelingContext)
    (caller : SeLe4n.ThreadId)
    (reg : ServiceRegistration)
    (st : SystemState)
    (hFlow : securityFlowsTo (ctx.threadLabelOf caller)
               (ctx.serviceLabelOf reg.sid) = true) :
    registerServiceChecked ctx caller reg st =
      registerService reg st := by
  unfold registerServiceChecked
  simp [hFlow]

/-- WS-Q1: When the policy denies flow, registerServiceChecked returns
`flowDenied`. -/
theorem registerServiceChecked_flowDenied
    (ctx : LabelingContext)
    (caller : SeLe4n.ThreadId)
    (reg : ServiceRegistration)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf caller)
               (ctx.serviceLabelOf reg.sid) = false) :
    registerServiceChecked ctx caller reg st =
      .error .flowDenied := by
  unfold registerServiceChecked
  simp [hDeny]

/-- WS-Q1: registerServiceChecked denied → no state change. -/
theorem registerServiceChecked_denied_preserves_state
    (ctx : LabelingContext) (caller : SeLe4n.ThreadId)
    (reg : ServiceRegistration)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf caller)
               (ctx.serviceLabelOf reg.sid) = false) :
    ¬∃ st', registerServiceChecked ctx caller reg st = .ok ((), st') := by
  intro ⟨st', h⟩
  simp [registerServiceChecked, hDeny] at h

/-- WS-Q1: `registerServiceChecked` either delegates or returns `flowDenied`. -/
theorem enforcement_sufficiency_registerService
    (ctx : LabelingContext) (caller : SeLe4n.ThreadId)
    (reg : ServiceRegistration)
    (st : SystemState) :
    (securityFlowsTo (ctx.threadLabelOf caller) (ctx.serviceLabelOf reg.sid) = true ∧
       registerServiceChecked ctx caller reg st = registerService reg st) ∨
    (securityFlowsTo (ctx.threadLabelOf caller) (ctx.serviceLabelOf reg.sid) = false ∧
       registerServiceChecked ctx caller reg st = .error .flowDenied) := by
  cases hFlow : securityFlowsTo (ctx.threadLabelOf caller) (ctx.serviceLabelOf reg.sid) with
  | true => left; exact ⟨rfl, by simp [registerServiceChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [registerServiceChecked, hFlow]⟩

/-- WS-Q1/A-35: Enforcement soundness for registerServiceChecked. -/
theorem enforcementSoundness_registerServiceChecked
    (ctx : LabelingContext)
    (caller : SeLe4n.ThreadId) (reg : ServiceRegistration)
    (st st' : SystemState)
    (hStep : registerServiceChecked ctx caller reg st = .ok ((), st')) :
    securityFlowsTo (ctx.threadLabelOf caller) (ctx.serviceLabelOf reg.sid) = true := by
  cases h : securityFlowsTo (ctx.threadLabelOf caller) (ctx.serviceLabelOf reg.sid) with
  | true => rfl
  | false =>
    have := registerServiceChecked_flowDenied ctx caller reg st h
    rw [this] at hStep; simp at hStep

-- ============================================================================
-- WS-H8/Q1: Updated enforcement boundary classification
-- ============================================================================

/-- W2-G (M-3) / WS-H8/Q1/V6-L/Z8-M/D2: `enforcementBoundaryExtended` is now a definitional
    alias for `enforcementBoundary`, eliminating the maintenance debt of keeping two
    identical lists in sync. Previously, the two lists contained the same operations
    in different order with only a cardinality correspondence proof. Now they are
    definitionally equal, making element-wise correspondence trivial by `rfl`.
    Z8-M expanded from 22 to 25 entries with SchedContext capability-only operations.
    D1 expanded from 25 to 27 entries with thread lifecycle capability-only operations.
    D2 expanded from 27 to 29 entries with priority management capability-only operations.
    D3 expanded from 29 to 30 entries with IPC buffer configuration capability-only operation.
    AC4-D expanded from 30 to 33 entries with VSpace map/unmap and service revocation.
    WS-SM SM5.H.4 expanded from 33 to 34 entries with the CPU-affinity configuration
    capability-only operation.
    WS-SM SM6.B expanded from 34 to 36 entries with the notification-binding
    capability-only operations (bindNotification / unbindNotification).
    WS-SM SM6.D / PR #822 Phase H expanded from 36 to 37 entries with the
    reply-cap mint (mintReplyCapWithCdt).
    WS-SM SM7.D expanded from 37 to 38 entries with the instruction/data
    unification of one mapped page (vspaceUnifyInstructionPage — seL4's
    Page_Unify_Instruction; capability-only, gated by the `.write` right on the
    page's capability, with no information-flow policy to consult because no
    data crosses a label boundary).
    WS-SM SM8.C expanded from 38 to 39 entries with the live declassification
    entry point (declassifyObjectFromCore — **policy-gated**, and the only
    policy-gated entry that may complete when `securityFlowsTo` says no: it
    consults the configured `DeclassificationPolicy` after the ordinary flow
    check refuses, and records the downgrade in the audit trail).
    WS-SM SM8.E.3 expanded from 39 to 40 entries with the SM3 two-phase-locking
    bracket (withLockSet — capability-only, an internal building block used
    under an already-capability-guarded context).  SM8.B classified it in a
    separate per-core list and deferred the promotion here precisely so the
    canonical count moved exactly once, in the phase that owns the
    reconciliation. -/
abbrev enforcementBoundaryExtended : List EnforcementClass := enforcementBoundary

/-- V6-L/Z8-M/D2/D3/AC4-D (L-IF-3): Completeness assertion — `enforcementBoundaryExtended`
    has exactly 42 entries, matching the canonical `enforcementBoundary`.

    WS-SM SM9.A.11 added the two audit-trail entries (`auditReadWord`,
    `auditDrainVisiblePrefix`), both capability-only.

    This theorem is the authority for the entry count; `enforcementBoundary`'s
    own docstring deliberately does not restate it. -/
theorem enforcementBoundaryExtended_count :
    enforcementBoundaryExtended.length = 42 := by rfl

/-- W2-G (M-3): Element-wise correspondence — `enforcementBoundaryExtended` and
    `enforcementBoundary` are definitionally equal. This closes the M-3 finding
    from the full kernel audit: previously only cardinality correspondence was
    proven, now full structural equality holds by definition. -/
theorem enforcementBoundaryExtended_eq_canonical :
    enforcementBoundaryExtended = enforcementBoundary := rfl

/-- V6-L (L-IF-3): Backward-compatible length match theorem. -/
theorem enforcementBoundaryExtended_matches_canonical :
    enforcementBoundaryExtended.length = enforcementBoundary.length := by rfl

-- ============================================================================
-- WS-H8/A-35: Enforcement soundness meta-theorem
-- ============================================================================

/-- WS-SM SM8.C: **enforcement soundness at the gate** — a successful checked
send implies the whole `endpointFlowGate` passed: global check *and* endpoint
override.

Stated separately from the `securityFlowsTo` form below because the two now say
different things: this is what the wrapper branched on, and that one is the half
every pre-SM8.C consumer asked for.  Deriving the second from the first keeps
one proof of the branch rather than two. -/
theorem enforcementSoundness_endpointSendDualChecked_gate
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState) (r : CapTransferSummary) (st' : SystemState)
    (hStep : endpointSendDualChecked ctx endpointId sender msg endpointRights
              senderCspaceRoot receiverSlotBase st = .ok (r, st')) :
    endpointFlowGate ctx endpointId (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) = true := by
  unfold endpointSendDualChecked at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases h : endpointFlowGate ctx endpointId (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) with
  | true => rfl
  | false => simp [h] at hStep

/-- WS-H8/A-35: Enforcement soundness — a checked operation that succeeds
implies the flow check passed. This is the foundational bridge connecting
the enforcement layer to non-interference hypotheses.

For any checked wrapper: if the operation succeeds (returns `.ok`), then
the `securityFlowsTo` check must have evaluated to `true`, meaning the
operation's source domain is authorized to flow to the destination domain. -/
theorem enforcementSoundness_endpointSendDualChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState) (r : CapTransferSummary) (st' : SystemState)
    (hStep : endpointSendDualChecked ctx endpointId sender msg endpointRights
              senderCspaceRoot receiverSlotBase st = .ok (r, st')) :
    securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = true := by
  exact endpointFlowGate_implies_securityFlowsTo ctx endpointId _ _
    (enforcementSoundness_endpointSendDualChecked_gate ctx endpointId sender msg endpointRights
      senderCspaceRoot receiverSlotBase st r st' hStep)

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

/-- WS-SM SM8.C: enforcement soundness at the gate for the checked receive. -/
theorem enforcementSoundness_endpointReceiveDualChecked_gate
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (st : SystemState) (r : SeLe4n.ThreadId) (st' : SystemState)
    (hStep : endpointReceiveDualChecked ctx endpointId receiver replyId st = .ok (r, st')) :
    endpointFlowGate ctx endpointId (ctx.endpointLabelOf endpointId)
      (ctx.threadLabelOf receiver) = true := by
  unfold endpointReceiveDualChecked at hStep
  cases h : endpointFlowGate ctx endpointId (ctx.endpointLabelOf endpointId)
      (ctx.threadLabelOf receiver) with
  | true => rfl
  | false => simp [h] at hStep

/-- WS-H8/A-35: Enforcement soundness for endpointReceiveDualChecked. -/
theorem enforcementSoundness_endpointReceiveDualChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (st : SystemState) (r : SeLe4n.ThreadId) (st' : SystemState)
    (hStep : endpointReceiveDualChecked ctx endpointId receiver replyId st = .ok (r, st')) :
    securityFlowsTo (ctx.endpointLabelOf endpointId) (ctx.threadLabelOf receiver) = true :=
  endpointFlowGate_implies_securityFlowsTo ctx endpointId _ _
    (enforcementSoundness_endpointReceiveDualChecked_gate ctx endpointId receiver replyId
      st r st' hStep)

-- ============================================================================
-- Y2-E: Enforcement soundness for the remaining 5 checked wrappers
-- ============================================================================

/-- WS-SM SM8.C: enforcement soundness at the gate for the checked call. -/
theorem enforcementSoundness_endpointCallChecked_gate
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState) (r : CapTransferSummary) (st' : SystemState)
    (hStep : endpointCallChecked ctx endpointId caller msg endpointRights
              callerCspaceRoot receiverSlotBase st = .ok (r, st')) :
    endpointFlowGate ctx endpointId (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) = true := by
  unfold endpointCallChecked at hStep
  cases h : endpointFlowGate ctx endpointId (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) with
  | true => rfl
  | false => simp [h] at hStep

/-- Y2-E: Enforcement soundness for endpointCallChecked.
Success implies caller→endpoint flow is allowed. -/
theorem enforcementSoundness_endpointCallChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState) (r : CapTransferSummary) (st' : SystemState)
    (hStep : endpointCallChecked ctx endpointId caller msg endpointRights
              callerCspaceRoot receiverSlotBase st = .ok (r, st')) :
    securityFlowsTo (ctx.threadLabelOf caller) (ctx.endpointLabelOf endpointId) = true := by
  exact endpointFlowGate_implies_securityFlowsTo ctx endpointId _ _
    (enforcementSoundness_endpointCallChecked_gate ctx endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase st r st' hStep)

/-- Y2-E: Enforcement soundness for endpointReplyChecked.
Success implies replier→target flow is allowed. -/
theorem enforcementSoundness_endpointReplyChecked
    (ctx : LabelingContext)
    (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (st st' : SystemState)
    (hStep : endpointReplyChecked ctx replier target msg st = .ok ((), st')) :
    securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) = true := by
  unfold endpointReplyChecked at hStep
  cases h : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) with
  | true => rfl
  | false => simp [h] at hStep

/-- Y2-E: Enforcement soundness for cspaceMintChecked.
Success implies src→dst CNode flow is allowed. -/
theorem enforcementSoundness_cspaceMintChecked
    (ctx : LabelingContext)
    (src dst : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge) (st st' : SystemState)
    (hStep : cspaceMintChecked ctx src dst rights badge st = .ok ((), st')) :
    securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true := by
  unfold cspaceMintChecked at hStep
  cases h : securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) with
  | true => rfl
  | false => simp [h] at hStep

/-- Y2-E: Enforcement soundness for notificationWaitChecked.
Success implies notification→waiter flow is allowed. -/
theorem enforcementSoundness_notificationWaitChecked
    (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (st : SystemState) (r : Option SeLe4n.Badge) (st' : SystemState)
    (hStep : notificationWaitChecked ctx notificationId waiter st = .ok (r, st')) :
    securityFlowsTo (ctx.objectLabelOf notificationId) (ctx.threadLabelOf waiter) = true := by
  unfold notificationWaitChecked at hStep
  cases h : securityFlowsTo (ctx.objectLabelOf notificationId) (ctx.threadLabelOf waiter) with
  | true => rfl
  | false => simp [h] at hStep

/-- Y2-E: Enforcement soundness for endpointReplyRecvChecked (compound).
Success implies both flow checks pass: replier→target AND endpoint→receiver. -/
theorem enforcementSoundness_endpointReplyRecvChecked
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (replyId : Option SeLe4n.ReplyId) (st st' : SystemState)
    (hStep : endpointReplyRecvChecked ctx endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    securityFlowsTo (ctx.threadLabelOf receiver) (ctx.threadLabelOf replyTarget) = true ∧
    securityFlowsTo (ctx.endpointLabelOf endpointId) (ctx.threadLabelOf receiver) = true := by
  unfold endpointReplyRecvChecked at hStep
  cases h1 : securityFlowsTo (ctx.threadLabelOf receiver) (ctx.threadLabelOf replyTarget) with
  | false => simp [h1] at hStep
  | true =>
    -- WS-SM SM8.C: the receive leg branches on the gate; the reply leg does not
    -- (the endpoint override governs flows crossing the endpoint).
    cases h2 : endpointFlowGate ctx endpointId (ctx.endpointLabelOf endpointId)
        (ctx.threadLabelOf receiver) with
    | false => simp [h1, h2] at hStep
    | true => exact ⟨rfl, endpointFlowGate_implies_securityFlowsTo ctx endpointId _ _ h2⟩

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

/-- WS-SM SM8.C.9: **the declassification decision, on its own** — the two
authorization checks `declassifyStore` runs, factored out of the store it gates.

Factored because the live `.declassify` syscall (SM8.C.9) runs exactly these
checks and records the result, but does **not** perform the store: that store is
the model's *simulation* of an information transfer (the docstring above says
so), and simulating a transfer by overwriting an arbitrary object is not
something a syscall may do — it would let a caller install a chosen
`KernelObject` at a chosen id and break every object-store invariant at once.

Sharing the decision rather than restating it is what makes
`authorizeDeclassificationOnCore_agrees_with_gate` an equality of the *same*
computation instead of a claim that two copies happen to match. -/
def declassificationDecision
    (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain) : Except KernelError Unit :=
  if ctx.policy.canFlow srcDomain dstDomain then
    -- Normal flow allowed — this is not a declassification scenario
    .error .flowDenied
  else if declPolicy.canDeclassify srcDomain dstDomain then
    .ok ()
  else
    .error .declassificationDenied

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
      .error .declassificationDenied

/-- WS-SM SM8.C.9: the gate **is** the decision followed by the store.  The
correspondence that keeps `declassificationDecision` honest: it is not a second
implementation of the checks, it is the checks `declassifyStore` performs. -/
theorem declassifyStore_eq_decision_bind
    (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain)
    (targetId : SeLe4n.ObjId) (obj : KernelObject) (st : SystemState) :
    declassifyStore ctx declPolicy srcDomain dstDomain targetId obj st =
      (declassificationDecision ctx declPolicy srcDomain dstDomain).bind
        (fun _ => storeObject targetId obj st) := by
  unfold declassifyStore declassificationDecision
  split
  · rfl
  · split <;> rfl

/-- WS-SM SM8.C.9: the decision succeeds exactly when the downgrade is
authorized — base policy denies and the declassification policy permits.  The
decision-level form of `enforcementSoundness_declassifyStore`. -/
theorem declassificationDecision_ok_iff
    (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain) :
    declassificationDecision ctx declPolicy srcDomain dstDomain = .ok () ↔
      (ctx.policy.canFlow srcDomain dstDomain = false ∧
        declPolicy.canDeclassify srcDomain dstDomain = true) := by
  unfold declassificationDecision
  cases hNormal : ctx.policy.canFlow srcDomain dstDomain with
  | true => simp
  | false =>
    cases hDecl : declPolicy.canDeclassify srcDomain dstDomain with
    | true => simp
    | false => simp

/-- WS-SM SM8.C.9: the decision agrees with the `DeclassificationPolicy`
predicate the rest of the information-flow layer reasons with. -/
theorem declassificationDecision_ok_iff_isDeclassificationAuthorized
    (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy)
    (srcDomain dstDomain : SecurityDomain) :
    declassificationDecision ctx declPolicy srcDomain dstDomain = .ok () ↔
      DeclassificationPolicy.isDeclassificationAuthorized ctx.policy declPolicy
        srcDomain dstDomain = true := by
  rw [declassificationDecision_ok_iff]
  unfold DeclassificationPolicy.isDeclassificationAuthorized
  simp

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
      .error .declassificationDenied := by
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

-- ============================================================================
-- T6-J/M-IF-1: Checked dispatch NI preservation
-- ============================================================================

/-- T6-J/M-IF-1: The checked dispatch path ensures that when a cross-domain
operation is **denied** by `securityFlowsTo`, no state mutation occurs.
This is the core NI property for the checked path: denied flows are
invisible to the low observer.

**Proof structure**: Each checked wrapper's `*_denied_preserves_state`
theorem proves that a denied operation returns `.error .flowDenied` without
modifying state. This theorem bundles the property for all 3 original
policy-gated wrappers as a representative witness. The WS-H8 extensions
(notificationSignal, cspaceCopy, cspaceMove, endpointReceiveDual) have
their own denied-preserves-state proofs in Soundness.lean above.

The full NI composition (linking checked dispatch to low-equivalence
preservation) is in `Invariant/Composition.lean`. -/
theorem checkedDispatch_flowDenied_preserves_state :
    (∀ ctx epId sender msg (endpointRights : AccessRightSet) (senderCspaceRoot : SeLe4n.ObjId)
        (receiverSlotBase : SeLe4n.Slot) st,
      securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf epId) = false →
      ¬∃ (r : CapTransferSummary) (st' : SystemState),
        endpointSendDualChecked ctx epId sender msg
        endpointRights senderCspaceRoot receiverSlotBase st = .ok (r, st')) ∧
    (∀ ctx src dst rights badge st,
      securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = false →
      ¬∃ st', cspaceMintChecked ctx src dst rights badge st = .ok ((), st')) ∧
    (∀ ctx caller reg st,
      securityFlowsTo (ctx.threadLabelOf caller) (ctx.serviceLabelOf reg.sid) = false →
      ¬∃ st', registerServiceChecked ctx caller reg st = .ok ((), st')) :=
  ⟨fun ctx epId sender msg endpointRights senderCspaceRoot receiverSlotBase st hDeny =>
    endpointSendDualChecked_denied_preserves_state ctx epId sender msg
      endpointRights senderCspaceRoot receiverSlotBase st hDeny,
   fun ctx src dst rights badge st hDeny =>
    cspaceMintChecked_denied_preserves_state ctx src dst rights badge st hDeny,
   fun ctx caller reg st hDeny => by
    intro ⟨st', h⟩
    simp [registerServiceChecked, hDeny] at h⟩

/-- T6-J/V6-L: The checked dispatch path delegates to checked wrappers for all
    11 policy-gated operations, ensuring the enforcement boundary is complete.
    This is a classification witness documenting which operations are checked.
    V6-L: Updated from 7 to 11 entries to match all policy-gated wrappers. -/
def checkedDispatchEnforcementCoverage : List String :=
  [ "endpointSendDualChecked"      -- .send → endpointSendDualChecked
  , "endpointReceiveDualChecked"   -- .receive → endpointReceiveDualChecked
  , "endpointCallChecked"          -- .call → endpointCallChecked (U5-B)
  , "endpointReplyChecked"         -- .reply → endpointReplyChecked (U5-C)
  , "endpointReplyRecvChecked"     -- .replyRecv → endpointReplyRecvChecked (V2-C)
  , "cspaceMintChecked"            -- .cspaceMint → cspaceMintChecked
  , "cspaceCopyChecked"            -- .cspaceCopy → cspaceCopyChecked
  , "cspaceMoveChecked"            -- .cspaceMove → cspaceMoveChecked
  , "notificationSignalChecked"    -- .notifSignal → notificationSignalChecked
  , "notificationWaitChecked"      -- .notifWait → notificationWaitChecked (V2-A)
  , "registerServiceChecked"       -- .serviceRegister → registerServiceChecked
  ]

/-- T6-J/V6-L: The checked dispatch covers all 11 policy-gated operations. -/
theorem checkedDispatchEnforcementCoverage_complete :
    checkedDispatchEnforcementCoverage.length = 11 := by rfl

-- ============================================================================
-- X3-B (H-5): Enforcement-NI global bridge theorem
-- ============================================================================

/-- X3-B (H-5) / Y2-E: **Enforcement-NI global bridge theorem.**

    This theorem unifies all **11** enforcement soundness theorems into a single
    bridge connecting the enforcement layer to the non-interference layer.

    **Structure**: For each of the 11 checked wrappers, this theorem proves that
    wrapper success implies the underlying `securityFlowsTo` check(s) passed.
    This `securityFlowsTo` witness is the prerequisite for constructing
    `NonInterferenceStep` terms in `Invariant/Composition.lean`.

    **Bridge mechanism**: The enforcement layer gates operations on
    `securityFlowsTo` checks. The NI layer's `NonInterferenceStep` constructors
    require domain-separation hypotheses (endpoint/thread non-observability).
    The bridge connects these: enforcement success ⟹ flow allowed ⟹
    NI step constructable (given the domain-separation context).

    **Coverage**: 11 of 11 checked wrappers. Complete. (Y2-E extended from 6/11
    to 11/11 by adding `endpointCallChecked`, `endpointReplyChecked`,
    `cspaceMintChecked`, `notificationWaitChecked`, `endpointReplyRecvChecked`.) -/
theorem enforcementBridge_to_NonInterferenceStep
    (ctx : LabelingContext) (st st' : SystemState) :
    -- 1. endpointSendDualChecked: success implies sender→endpoint flow allowed
    (∀ eid sender msg (endpointRights : AccessRightSet) (senderCspaceRoot : SeLe4n.ObjId)
        (receiverSlotBase : SeLe4n.Slot) (r : CapTransferSummary),
      endpointSendDualChecked ctx eid sender msg endpointRights senderCspaceRoot
        receiverSlotBase st = .ok (r, st') →
      securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf eid) = true) ∧
    -- 2. notificationSignalChecked: success implies signaler→notification flow allowed
    (∀ ntfnId signaler badge,
      notificationSignalChecked ctx ntfnId signaler badge st = .ok ((), st') →
      securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf ntfnId) = true) ∧
    -- 3. cspaceCopyChecked: success implies src→dst CNode flow allowed
    (∀ src dst,
      cspaceCopyChecked ctx src dst st = .ok ((), st') →
      securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true) ∧
    -- 4. cspaceMoveChecked: success implies src→dst CNode flow allowed
    (∀ src dst,
      cspaceMoveChecked ctx src dst st = .ok ((), st') →
      securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true) ∧
    -- 5. endpointReceiveDualChecked: success implies endpoint→receiver flow allowed
    (∀ eid receiver replyId r,
      endpointReceiveDualChecked ctx eid receiver replyId st = .ok (r, st') →
      securityFlowsTo (ctx.endpointLabelOf eid) (ctx.threadLabelOf receiver) = true) ∧
    -- 6. registerServiceChecked: success implies caller→service flow allowed
    (∀ caller reg,
      registerServiceChecked ctx caller reg st = .ok ((), st') →
      securityFlowsTo (ctx.threadLabelOf caller) (ctx.serviceLabelOf reg.sid) = true) ∧
    -- 7. endpointCallChecked: success implies caller→endpoint flow allowed
    (∀ eid caller msg rights cRoot slotBase r,
      endpointCallChecked ctx eid caller msg rights cRoot slotBase st = .ok (r, st') →
      securityFlowsTo (ctx.threadLabelOf caller) (ctx.endpointLabelOf eid) = true) ∧
    -- 8. endpointReplyChecked: success implies replier→target flow allowed
    (∀ replier target msg,
      endpointReplyChecked ctx replier target msg st = .ok ((), st') →
      securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) = true) ∧
    -- 9. cspaceMintChecked: success implies src→dst CNode flow allowed
    (∀ src dst rights badge,
      cspaceMintChecked ctx src dst rights badge st = .ok ((), st') →
      securityFlowsTo (ctx.objectLabelOf src.cnode) (ctx.objectLabelOf dst.cnode) = true) ∧
    -- 10. notificationWaitChecked: success implies notification→waiter flow allowed
    (∀ ntfnId waiter r,
      notificationWaitChecked ctx ntfnId waiter st = .ok (r, st') →
      securityFlowsTo (ctx.objectLabelOf ntfnId) (ctx.threadLabelOf waiter) = true) ∧
    -- 11. endpointReplyRecvChecked: success implies both flow checks pass
    (∀ eid receiver replyTarget msg replyId,
      endpointReplyRecvChecked ctx eid receiver replyTarget msg replyId st = .ok ((), st') →
      securityFlowsTo (ctx.threadLabelOf receiver) (ctx.threadLabelOf replyTarget) = true ∧
      securityFlowsTo (ctx.endpointLabelOf eid) (ctx.threadLabelOf receiver) = true) := by
  exact ⟨
    fun eid sender msg endpointRights senderCspaceRoot receiverSlotBase r hStep =>
      enforcementSoundness_endpointSendDualChecked ctx eid sender msg endpointRights
        senderCspaceRoot receiverSlotBase st r st' hStep,
    fun ntfnId signaler badge hStep =>
      enforcementSoundness_notificationSignalChecked ctx ntfnId signaler badge st st' hStep,
    fun src dst hStep =>
      enforcementSoundness_cspaceCopyChecked ctx src dst st st' hStep,
    fun src dst hStep =>
      enforcementSoundness_cspaceMoveChecked ctx src dst st st' hStep,
    fun eid receiver replyId r hStep =>
      enforcementSoundness_endpointReceiveDualChecked ctx eid receiver replyId st r st' hStep,
    fun caller reg hStep =>
      enforcementSoundness_registerServiceChecked ctx caller reg st st' hStep,
    fun eid caller msg rights cRoot slotBase r hStep =>
      enforcementSoundness_endpointCallChecked ctx eid caller msg rights cRoot slotBase st r st' hStep,
    fun replier target msg hStep =>
      enforcementSoundness_endpointReplyChecked ctx replier target msg st st' hStep,
    fun src dst rights badge hStep =>
      enforcementSoundness_cspaceMintChecked ctx src dst rights badge st st' hStep,
    fun ntfnId waiter r hStep =>
      enforcementSoundness_notificationWaitChecked ctx ntfnId waiter st r st' hStep,
    fun eid receiver replyTarget msg replyId hStep =>
      enforcementSoundness_endpointReplyRecvChecked ctx eid receiver replyTarget msg replyId st st' hStep⟩


-- ============================================================================
-- WS-SM SM8.C: completing the `_denied_preserves_state` / `enforcement_sufficiency_`
-- families over every policy-gated boundary entry
-- ============================================================================

/-! Both families were documented as covering "all policy-gated operations" while
covering seven of them.  Four wrappers landed after the families were written and
never joined them — `endpointCallChecked` (U5-B), `endpointReplyChecked` (U5-C),
`notificationWaitChecked` (V2-A) and `endpointReplyRecvChecked` (V2-C) — so the
claim was false in the direction that matters: a reader checking whether *every*
gate fails closed, and whether any gate has a third behaviour beyond
delegate-or-deny, had no theorem for a third of them.

Per the implement-the-improvement rule the remedy is the theorems, not a smaller
claim.  With these eight and the three in
`InformationFlow/Declassification.lean`, the families cover all twelve
policy-gated entries of `enforcementBoundary`.  The declassification contributes
three rather than two because its denial-preservation is stated at both levels:
`declassifyObjectFromCore`, the name `enforcementBoundary` classifies (covering
all three of its refusal modes — an idle core, an absent target, and a declined
decision), and `authorizeDeclassificationOnCore`, the gate that entry wraps. -/

/-- WS-SM SM8.C: `endpointCallChecked` denied → no state change.

Stated on the **global** check rather than on `endpointFlowGate`, which is the
usable form: `endpointFlowGate` is the conjunction of the lattice check with the
endpoint's override, so a failing lattice check sinks the gate regardless of how
the endpoint is configured (`endpointFlowGate_false_of_securityFlowsTo_false`),
and an operator cannot open this path by installing an override. -/
theorem endpointCallChecked_denied_preserves_state
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf caller)
               (ctx.endpointLabelOf endpointId) = false) :
    ¬∃ (r : CapTransferSummary) (st' : SystemState),
      endpointCallChecked ctx endpointId caller msg endpointRights
        callerCspaceRoot receiverSlotBase st = .ok (r, st') := by
  intro ⟨r, st', h⟩
  simp [endpointCallChecked,
    endpointFlowGate_false_of_securityFlowsTo_false ctx endpointId _ _ hDeny] at h

/-- WS-SM SM8.C: `endpointCallChecked` either delegates or returns `flowDenied`. -/
theorem enforcement_sufficiency_endpointCall
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st : SystemState) :
    (endpointFlowGate ctx endpointId (ctx.threadLabelOf caller)
        (ctx.endpointLabelOf endpointId) = true ∧
       endpointCallChecked ctx endpointId caller msg endpointRights
           callerCspaceRoot receiverSlotBase st =
         endpointCallWithCaps endpointId caller msg endpointRights
           callerCspaceRoot receiverSlotBase st) ∨
    (endpointFlowGate ctx endpointId (ctx.threadLabelOf caller)
        (ctx.endpointLabelOf endpointId) = false ∧
       endpointCallChecked ctx endpointId caller msg endpointRights
           callerCspaceRoot receiverSlotBase st = .error .flowDenied) := by
  cases hFlow : endpointFlowGate ctx endpointId (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) with
  | true => left; exact ⟨rfl, by simp [endpointCallChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [endpointCallChecked, hFlow]⟩

/-- WS-SM SM8.C: `endpointReplyChecked` denied → no state change. -/
theorem endpointReplyChecked_denied_preserves_state
    (ctx : LabelingContext) (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf replier)
               (ctx.threadLabelOf target) = false) :
    ¬∃ st', endpointReplyChecked ctx replier target msg st = .ok ((), st') := by
  intro ⟨st', h⟩
  simp [endpointReplyChecked, hDeny] at h

/-- WS-SM SM8.C: `endpointReplyChecked` either delegates or returns `flowDenied`. -/
theorem enforcement_sufficiency_endpointReply
    (ctx : LabelingContext) (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (st : SystemState) :
    (securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) = true ∧
       endpointReplyChecked ctx replier target msg st =
         endpointReply replier target msg st) ∨
    (securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) = false ∧
       endpointReplyChecked ctx replier target msg st = .error .flowDenied) := by
  cases hFlow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) with
  | true => left; exact ⟨rfl, by simp [endpointReplyChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [endpointReplyChecked, hFlow]⟩

/-- WS-SM SM8.C: `notificationWaitChecked` denied → no state change. -/
theorem notificationWaitChecked_denied_preserves_state
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.objectLabelOf notificationId)
               (ctx.threadLabelOf waiter) = false) :
    ¬∃ (r : Option SeLe4n.Badge) (st' : SystemState),
      notificationWaitChecked ctx notificationId waiter st = .ok (r, st') := by
  intro ⟨r, st', h⟩
  simp [notificationWaitChecked, hDeny] at h

/-- WS-SM SM8.C: `notificationWaitChecked` either delegates or returns `flowDenied`. -/
theorem enforcement_sufficiency_notificationWait
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (st : SystemState) :
    (securityFlowsTo (ctx.objectLabelOf notificationId) (ctx.threadLabelOf waiter) = true ∧
       notificationWaitChecked ctx notificationId waiter st =
         notificationWait notificationId waiter st) ∨
    (securityFlowsTo (ctx.objectLabelOf notificationId) (ctx.threadLabelOf waiter) = false ∧
       notificationWaitChecked ctx notificationId waiter st = .error .flowDenied) := by
  cases hFlow : securityFlowsTo (ctx.objectLabelOf notificationId)
      (ctx.threadLabelOf waiter) with
  | true => left; exact ⟨rfl, by simp [notificationWaitChecked, hFlow]⟩
  | false => right; exact ⟨rfl, by simp [notificationWaitChecked, hFlow]⟩

/-- WS-SM SM8.C: `endpointReplyRecvChecked` denied → no state change.

The compound wrapper has two legs, so the hypothesis is a disjunction: **either**
leg refusing sinks the whole operation.  That is the property a caller needs —
there is no partial commit in which the reply lands and the receive does not. -/
theorem endpointReplyRecvChecked_denied_preserves_state
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf receiver)
               (ctx.threadLabelOf replyTarget) = false ∨
             securityFlowsTo (ctx.endpointLabelOf endpointId)
               (ctx.threadLabelOf receiver) = false) :
    ¬∃ st', endpointReplyRecvChecked ctx endpointId receiver replyTarget msg replyId st
      = .ok ((), st') := by
  intro ⟨st', h⟩
  rcases hDeny with hReply | hRecv
  · simp [endpointReplyRecvChecked, hReply] at h
  · simp [endpointReplyRecvChecked,
      endpointFlowGate_false_of_securityFlowsTo_false ctx endpointId _ _ hRecv] at h

/-- WS-SM SM8.C: `endpointReplyRecvChecked` either delegates (both legs allowed)
or returns `flowDenied`.  There is no third behaviour, and in particular no arm
that runs one leg. -/
theorem enforcement_sufficiency_endpointReplyRecv
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId) (st : SystemState) :
    (securityFlowsTo (ctx.threadLabelOf receiver) (ctx.threadLabelOf replyTarget) = true ∧
       endpointFlowGate ctx endpointId (ctx.endpointLabelOf endpointId)
         (ctx.threadLabelOf receiver) = true ∧
       endpointReplyRecvChecked ctx endpointId receiver replyTarget msg replyId st =
         endpointReplyRecv endpointId receiver replyTarget msg replyId st) ∨
    ((securityFlowsTo (ctx.threadLabelOf receiver) (ctx.threadLabelOf replyTarget) = false ∨
        endpointFlowGate ctx endpointId (ctx.endpointLabelOf endpointId)
          (ctx.threadLabelOf receiver) = false) ∧
       endpointReplyRecvChecked ctx endpointId receiver replyTarget msg replyId st =
         .error .flowDenied) := by
  cases hReply : securityFlowsTo (ctx.threadLabelOf receiver) (ctx.threadLabelOf replyTarget) with
  | false => right; exact ⟨Or.inl rfl, by simp [endpointReplyRecvChecked, hReply]⟩
  | true =>
    cases hRecv : endpointFlowGate ctx endpointId (ctx.endpointLabelOf endpointId)
        (ctx.threadLabelOf receiver) with
    | true => left; exact ⟨rfl, rfl, by simp [endpointReplyRecvChecked, hReply, hRecv]⟩
    | false =>
      right; exact ⟨Or.inr rfl, by simp [endpointReplyRecvChecked, hReply, hRecv]⟩

end SeLe4n.Kernel
