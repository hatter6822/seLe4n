import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Lifecycle.Invariant

/-!
# Capability Invariant Preservation Proofs (M2)

This module defines the capability invariant components, the composed bundle entrypoint,
and transition-level preservation theorems for CSpace operations. It also contains
cross-subsystem composed bundles (M3, M3.5, M4-A).

## Proof scope qualification (F-16, WS-E2 C-01/H-01/H-03)

**Non-trivial invariant components** (WS-E2 / C-01 — reformulated from tautological):
- `cspaceSlotUnique`: CNode slot-index uniqueness — each slot index maps to at most
  one capability within every CNode in the system state. This is a structural invariant
  that depends on `CNode.insert` removing duplicates before prepending.
- `cspaceLookupSound`: Lookup completeness — every capability entry in a CNode's slot
  list is retrievable via `lookupSlotCap`. This property is non-trivial because
  `List.find?` returns only the first match; it requires `cspaceSlotUnique` to hold.

**Compositional preservation proofs** (WS-E2 / H-01 — refactored from re-prove):
All preservation proofs now derive post-state invariant components from pre-state
components through the operation's specific state transformation. For CNode-modifying
operations, the proof traces CNode slot-index uniqueness through `CNode.insert_slotsUnique`,
`CNode.remove_slotsUnique`, or `CNode.revokeTargetLocal_slotsUnique`. For operations that
don't modify CNodes, the proof uses object-store frame conditions to transfer the
pre-state invariant directly.

**Badge/notification routing consistency** (WS-E2 / H-03):
- `mintDerivedCap_badge_propagated`: badge faithfully stored in minted capability
- `cspaceMint_child_badge_preserved`: operation-level badge consistency
- `notificationSignal_badge_stored_fresh`: badge stored in notification
- `notificationWait_recovers_pending_badge`: badge delivered to waiter
- `badge_notification_routing_consistent`: end-to-end chain
- `badge_merge_idempotent`: badge OR-merge idempotency

**Substantive preservation theorems** (high assurance — prove invariant preservation
over *changed* state after a *successful* operation, using pre-state invariant
components compositionally):
- `cspaceMint_preserves_capabilityInvariantBundle`
- `cspaceInsertSlot_preserves_capabilityInvariantBundle`
- `cspaceDeleteSlot_preserves_capabilityInvariantBundle`
- `cspaceRevoke_preserves_capabilityInvariantBundle`
- `lifecycleRetypeObject_preserves_capabilityInvariantBundle`
- `lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle`
- all `endpointSend/AwaitReceive/Receive_preserves_capabilityInvariantBundle`
- composed bundle preservation theorems (`m3IpcSeed`, `m35`, `m4a`)

**Badge-override safety theorems** (high assurance — F-06 / TPI-D04):
- `mintDerivedCap_rights_attenuated_with_badge_override`
- `mintDerivedCap_target_preserved_with_badge_override`
- `cspaceMint_badge_override_safe`

**Structural / functional-correctness theorems** (high assurance):
- `mintDerivedCap_attenuates`
- `cspaceMint_child_attenuates`
- `cspaceDeleteSlot_authority_reduction`
- `cspaceRevoke_local_target_reduction`
- `cspaceRevoke_preserves_source`

**Error-case preservation theorems** (trivially true — the error path returns
unchanged state, so any pre-state invariant holds trivially in the post-state):
- `lifecycleRevokeDeleteRetype_error_preserves_m4aLifecycleInvariantBundle`
- `cspaceLookupSlot_preserves_capabilityInvariantBundle` (read-only, no mutation)

Error-case theorems are retained for proof-surface completeness and compositional
coverage, but they do not constitute meaningful security evidence.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- CNode slot-index uniqueness across all CNodes in the system state.

WS-E2 / C-01 reformulation: this is a non-trivial structural invariant. Each slot
index within a CNode maps to at most one capability. Without this, `CNode.lookup`
(which uses `List.find?`) could return a different capability than what was stored
at a given slot index, because `find?` returns only the first match.

This invariant is maintained by `CNode.insert` (which removes the old entry before
prepending), `CNode.remove` (which only filters), and `CNode.revokeTargetLocal`
(which only filters). -/
def cspaceSlotUnique (st : SystemState) : Prop :=
  ∀ cnodeId cn,
    st.objects cnodeId = some (.cnode cn) →
    cn.slotsUnique

/-- Lookup completeness: every capability entry in a CNode's slot list is retrievable
via `lookupSlotCap`.

WS-E2 / C-01 reformulation: this is non-trivial because `CNode.lookup` uses
`List.find?`, which returns only the first match for a given slot index. If duplicate
slot indices existed (violating `cspaceSlotUnique`), later entries would be
unretrievable. This property holds if and only if `cspaceSlotUnique` holds. -/
def cspaceLookupSound (st : SystemState) : Prop :=
  ∀ cnodeId cn slot cap,
    st.objects cnodeId = some (.cnode cn) →
    (slot, cap) ∈ cn.slots →
    SystemState.lookupSlotCap st { cnode := cnodeId, slot := slot } = some cap

/-- Attenuation rule component used by the M2 capability invariant bundle. -/
def cspaceAttenuationRule : Prop :=
  ∀ parent child rights badge,
    mintDerivedCap parent rights badge = .ok child →
    capAttenuates parent child

/-- Lifecycle-transition authority monotonicity obligations for the active slice.

This models transition-local non-escalation constraints:
1. delete cannot leave authority in the deleted slot,
2. local revoke cannot leave sibling authority to the revoked target.

Direct mint/derive attenuation remains the dedicated `cspaceAttenuationRule` bundle component. -/
def lifecycleAuthorityMonotonicity (st : SystemState) : Prop :=
  (∀ addr st',
      cspaceDeleteSlot addr st = .ok ((), st') →
      SystemState.lookupSlotCap st' addr = none) ∧
  (∀ addr st' parent,
      cspaceRevoke addr st = .ok ((), st') →
      cspaceLookupSlot addr st = .ok (parent, st) →
      ∀ slot cap,
        SystemState.lookupSlotCap st' { cnode := addr.cnode, slot := slot } = some cap →
        cap.target = parent.target →
        slot = addr.slot)

/-- Composed capability invariant bundle entrypoint.

The active lifecycle slice extends the M2 foundation bundle with explicit lifecycle-transition
authority obligations (`delete`/`revoke`) so lifecycle preservation can be stated against a
single invariant entrypoint. -/
def capabilityInvariantBundle (st : SystemState) : Prop :=
  cspaceSlotUnique st ∧ cspaceLookupSound st ∧ cspaceAttenuationRule ∧
    lifecycleAuthorityMonotonicity st

/-- M4-B bridge bundle: ties stale-reference exclusion to lifecycle transition authority
monotonicity so composition proofs can depend on a single named assumption. -/
def lifecycleCapabilityStaleAuthorityInvariant (st : SystemState) : Prop :=
  lifecycleStaleReferenceExclusionInvariant st ∧ lifecycleAuthorityMonotonicity st

theorem lifecycleCapabilityStaleAuthorityInvariant_of_bundles
    (st : SystemState)
    (hLifecycle : lifecycleInvariantBundle st)
    (hCap : capabilityInvariantBundle st) :
    lifecycleCapabilityStaleAuthorityInvariant st := by
  refine ⟨lifecycleStaleReferenceExclusionInvariant_of_lifecycleInvariantBundle st hLifecycle, ?_⟩
  exact hCap.2.2.2


-- ============================================================================
-- Composed invariant bundle definitions (M3, M3.5, M4-A)
-- ============================================================================


/-- M3 composed bundle entrypoint: M1 scheduler + M2 capability + M3 IPC. -/
def m3IpcSeedInvariantBundle (st : SystemState) : Prop :=
  schedulerInvariantBundle st ∧ capabilityInvariantBundle st ∧ ipcInvariant st

/-- Named M3.5 coherence component: runnable threads stay IPC-ready. -/
def ipcSchedulerRunnableReadyComponent (st : SystemState) : Prop :=
  runnableThreadIpcReady st

/-- Named M3.5 coherence component: send-blocked threads are not runnable. -/
def ipcSchedulerBlockedSendComponent (st : SystemState) : Prop :=
  blockedOnSendNotRunnable st

/-- Named M3.5 coherence component: receive-blocked threads are not runnable. -/
def ipcSchedulerBlockedReceiveComponent (st : SystemState) : Prop :=
  blockedOnReceiveNotRunnable st

/-- Named M3.5 aggregate coherence component for IPC+scheduler interaction. -/
def ipcSchedulerCoherenceComponent (st : SystemState) : Prop :=
  ipcSchedulerRunnableReadyComponent st ∧
  ipcSchedulerBlockedSendComponent st ∧
  ipcSchedulerBlockedReceiveComponent st

theorem ipcSchedulerCoherenceComponent_iff_contractPredicates (st : SystemState) :
    ipcSchedulerCoherenceComponent st ↔ ipcSchedulerContractPredicates st := by
  rfl

/-- M3.5 composed bundle entrypoint layered over the M3 IPC seed bundle.

This is the step-4 composition target for active-slice endpoint/scheduler coupling. -/
def m35IpcSchedulerInvariantBundle (st : SystemState) : Prop :=
  m3IpcSeedInvariantBundle st ∧ ipcSchedulerCoherenceComponent st

/-- M4-A composed bundle entrypoint:
M3.5 IPC+scheduler composition plus lifecycle metadata/invariant obligations. -/
def m4aLifecycleInvariantBundle (st : SystemState) : Prop :=
  m35IpcSchedulerInvariantBundle st ∧ lifecycleInvariantBundle st

end SeLe4n.Kernel
