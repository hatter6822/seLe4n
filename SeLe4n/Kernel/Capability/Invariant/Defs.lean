import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Lifecycle.Invariant

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
  ∀ (cnodeId : SeLe4n.ObjId) (cn : CNode),
    st.objects[cnodeId]? = some (KernelObject.cnode cn) →
    cn.slotsUnique

/-- Lookup completeness: every capability stored in a CNode's slot HashMap is
retrievable via `lookupSlotCap`.

WS-G5: With HashMap-backed slots, lookup completeness is direct — `CNode.lookup`
delegates to `HashMap.getElem?`, which is the canonical accessor. The property
is trivially true by the identity `CNode.lookup slot = cn.slots[slot]?`. -/
def cspaceLookupSound (st : SystemState) : Prop :=
  ∀ (cnodeId : SeLe4n.ObjId) (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability),
    st.objects[cnodeId]? = some (KernelObject.cnode cn) →
    cn.lookup slot = some cap →
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

-- ============================================================================
-- WS-H4: Meaningful capability invariant predicates (replacing trivially-true)
-- ============================================================================

/-- WS-H4/C-03: Every CNode has at most `2^radixBits` occupied slots.
This is the meaningful slot-capacity invariant that replaces the trivially-true
`slotsUnique` predicate for actual security assurance. -/
def cspaceSlotCountBounded (st : SystemState) : Prop :=
  ∀ (cnodeId : SeLe4n.ObjId) (cn : CNode),
    st.objects[cnodeId]? = some (KernelObject.cnode cn) → cn.slotCountBounded

/-- WS-H4/M-08: CDT node-slot coherence — every registered CDT node
points to an object that exists in the state. This ensures CDT-based
revocation can locate capabilities referenced by node mappings. The
predicate is robust through `detachSlotFromCdt` operations because
detached nodes lose their mapping (vacuously satisfying the condition).

**Scope vs spec intent**: The WS-H4 spec envisions mint-based CDT
completeness ("every derived capability has a CDT edge"). This predicate
captures the weaker but foundational node-slot reachability property:
CDT nodes never point to deleted objects. Mint-tracking completeness
requires `cspaceMintWithCdt` as the sole mint path (see M-08/A-20
annotation in API.lean). -/
def cdtCompleteness (st : SystemState) : Prop :=
  ∀ (nodeId : CdtNodeId) (ref : SlotRef),
    st.cdtNodeSlot[nodeId]? = some ref →
    st.objects[ref.cnode]? ≠ none

/-- WS-H4/M-03: CDT acyclicity — the capability derivation tree has no cycles.
Required for `descendantsOf` termination and revocation completeness. Uses the
edge-well-founded formulation for clean subset-preservation proofs. -/
def cdtAcyclicity (st : SystemState) : Prop :=
  st.cdt.edgeWellFounded

/-- WS-H13/H-01: CSpace depth consistency — every CNode has bounded depth and
well-formed bit allocation.

Each CNode in the object store has `depth ≤ maxCSpaceDepth`, and whenever its
`bitsConsumed` is positive it satisfies `cnodeWellFormed` (guard + radix ≤ depth,
individual widths bounded). Combined with `bitsConsumed > 0`, this guarantees
that multi-level `resolveCapAddress` terminates by structural recursion on
remaining bit count — no cross-CNode depth ordering is required. -/
def cspaceDepthConsistent (st : SystemState) : Prop :=
  ∀ (cnodeId : SeLe4n.ObjId) (cn : CNode),
    st.objects[cnodeId]? = some (.cnode cn) →
    cn.depth ≤ maxCSpaceDepth ∧
    (cn.bitsConsumed > 0 → cn.wellFormed)

/-- Composed capability invariant bundle entrypoint.

The active lifecycle slice extends the M2 foundation bundle with explicit lifecycle-transition
authority obligations (`delete`/`revoke`) so lifecycle preservation can be stated against a
single invariant entrypoint.

WS-H4: Extended from 4-tuple to 7-tuple with meaningful security predicates:
- `cspaceSlotCountBounded`: slot capacity bound (replaces trivially-true `slotsUnique`)
- `cdtCompleteness`: CDT node-slot reachability (every CDT node points to an existing object)
- `cdtAcyclicity`: CDT cycle-freedom for sound revocation

WS-H13: Extended to 8-tuple with depth consistency:
- `cspaceDepthConsistent`: child CNodes have strictly smaller depth than parents

**Design decisions (WS-H4):**
- CDT-modifying operations (`cspaceCopy`, `cspaceMove`, `cspaceMintWithCdt`) take
  `hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st'` as hypotheses rather than
  proving acyclicity preservation through `addEdge`. This is because proving
  `addEdge_preserves_acyclicity` requires a cycle-check precondition that must be
  validated at the caller; the hypothesis pattern correctly defers this obligation.
- CDT-shrinking operations (revoke/delete) prove acyclicity via
  `CapDerivationTree.edgeWellFounded_sub` (edge subset preserves well-foundedness).
- `cspaceSlotUnique` is retained alongside `cspaceSlotCountBounded` for backward
  compatibility with the existing proof surface. -/
def capabilityInvariantBundle (st : SystemState) : Prop :=
  cspaceSlotUnique st ∧ cspaceLookupSound st ∧ cspaceAttenuationRule ∧
    lifecycleAuthorityMonotonicity st ∧
    cspaceSlotCountBounded st ∧ cdtCompleteness st ∧ cdtAcyclicity st ∧
    cspaceDepthConsistent st

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
  exact hCap.2.2.2.1

-- ============================================================================
-- WS-H4: Extraction theorems for new bundle components
-- ============================================================================

theorem cspaceSlotCountBounded_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cspaceSlotCountBounded st := hInv.2.2.2.2.1

theorem cdtCompleteness_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cdtCompleteness st := hInv.2.2.2.2.2.1

theorem cdtAcyclicity_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cdtAcyclicity st := hInv.2.2.2.2.2.2.1

theorem cspaceDepthConsistent_of_capabilityInvariantBundle
    (st : SystemState) (hInv : capabilityInvariantBundle st) :
    cspaceDepthConsistent st := hInv.2.2.2.2.2.2.2

-- ============================================================================
-- WS-H4: Transfer theorems for new components through state transitions
-- ============================================================================

/-- WS-H4: Transfer cspaceSlotCountBounded through storeObject when
the stored object is NOT a CNode (endpoint, TCB, etc.). -/
private theorem cspaceSlotCountBounded_of_storeObject_nonCNode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hBounded : cspaceSlotCountBounded st)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hNotCNode : ∀ cn, obj ≠ .cnode cn) :
    cspaceSlotCountBounded st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = oid
  · subst hEq
    have := storeObject_objects_eq st st' cnodeId obj hStore
    rw [this] at hObj
    cases obj with
    | cnode cn' => exact absurd rfl (hNotCNode cn')
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => cases hObj
  · have hPre := storeObject_objects_ne st st' oid cnodeId obj hEq hStore
    rw [hPre] at hObj
    exact hBounded cnodeId cn hObj

/-- WS-H4: Transfer cspaceSlotCountBounded through storeObject when
the stored object IS a CNode (requires new CNode to be bounded). -/
theorem cspaceSlotCountBounded_of_storeObject_cnode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (cn' : CNode)
    (hBounded : cspaceSlotCountBounded st)
    (hStore : storeObject oid (.cnode cn') st = .ok ((), st'))
    (hNewBounded : cn'.slotCountBounded) :
    cspaceSlotCountBounded st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = oid
  · subst hEq
    have := storeObject_objects_eq st st' cnodeId (.cnode cn') hStore
    rw [this] at hObj; cases hObj
    exact hNewBounded
  · have hPre := storeObject_objects_ne st st' oid cnodeId (.cnode cn') hEq hStore
    rw [hPre] at hObj
    exact hBounded cnodeId cn hObj

/-- WS-H4: Transfer cspaceSlotCountBounded when objects are unchanged. -/
theorem cspaceSlotCountBounded_of_objects_eq
    (st st' : SystemState)
    (hBounded : cspaceSlotCountBounded st)
    (hObjEq : st'.objects = st.objects) :
    cspaceSlotCountBounded st' := by
  intro cnodeId cn hObj
  rw [hObjEq] at hObj
  exact hBounded cnodeId cn hObj

/-- WS-H4: Transfer cdtCompleteness when CDT and cdtNodeSlot are unchanged. -/
theorem cdtCompleteness_of_objects_nodeSlot_eq
    (st st' : SystemState)
    (hComp : cdtCompleteness st)
    (hObjEq : st'.objects = st.objects)
    (hNodeSlotEq : st'.cdtNodeSlot = st.cdtNodeSlot) :
    cdtCompleteness st' := by
  intro nodeId ref hNS
  rw [hNodeSlotEq] at hNS
  rw [hObjEq]
  exact hComp nodeId ref hNS

/-- WS-H4: Transfer cdtCompleteness through storeObject. After storeObject,
objects may change but every key that was non-none stays non-none. -/
theorem cdtCompleteness_of_storeObject
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hComp : cdtCompleteness st)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hNodeSlotEq : st'.cdtNodeSlot = st.cdtNodeSlot) :
    cdtCompleteness st' := by
  intro nodeId ref hNS
  rw [hNodeSlotEq] at hNS
  have hPre := hComp nodeId ref hNS
  by_cases hEq : ref.cnode = oid
  · rw [hEq]; rw [storeObject_objects_eq st st' oid obj hStore]; simp
  · rw [storeObject_objects_ne st st' oid ref.cnode obj hEq hStore]; exact hPre

/-- WS-H4: Transfer cdtAcyclicity when CDT is unchanged. -/
theorem cdtAcyclicity_of_cdt_eq
    (st st' : SystemState)
    (hAcyclic : cdtAcyclicity st)
    (hCdtEq : st'.cdt = st.cdt) :
    cdtAcyclicity st' := by
  unfold cdtAcyclicity
  rw [hCdtEq]
  exact hAcyclic

/-- WS-H4: storeObject preserves CDT cdtNodeSlot field. -/
theorem storeObject_cdtNodeSlot_eq
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    st'.cdtNodeSlot = st.cdtNodeSlot ∧ st'.cdtSlotNode = st.cdtSlotNode := by
  unfold storeObject at hStore
  cases hStore; exact ⟨rfl, rfl⟩

/-- WS-H4: Transfer cspaceSlotCountBounded through storeTcbIpcState
(stores a TCB, not a CNode, so slot bounds are preserved). -/
private theorem cspaceSlotCountBounded_of_storeTcbIpcState
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hBounded : cspaceSlotCountBounded st)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    cspaceSlotCountBounded st' := by
  intro cnodeId cn hObj
  have hPre : st.objects[cnodeId]? = some (.cnode cn) :=
    storeTcbIpcState_cnode_backward st st' tid ipc cnodeId cn hStep hObj
  exact hBounded cnodeId cn hPre

/-- WS-H4: storeTcbIpcState preserves CDT fields (delegates to storeObject). -/
private theorem storeTcbIpcState_cdt_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot ∧ st'.cdtSlotNode = st.cdtSlotNode := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact ⟨storeObject_cdt_eq st pair.2 tid.toObjId _ hStore,
             (storeObject_cdtNodeSlot_eq st pair.2 tid.toObjId _ hStore).1,
             (storeObject_cdtNodeSlot_eq st pair.2 tid.toObjId _ hStore).2⟩

/-- WS-H4: storeTcbIpcStateAndMessage preserves CDT fields. -/
private theorem storeTcbIpcStateAndMessage_cdt_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot ∧ st'.cdtSlotNode = st.cdtSlotNode := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact ⟨storeObject_cdt_eq st pair.2 tid.toObjId _ hStore,
             (storeObject_cdtNodeSlot_eq st pair.2 tid.toObjId _ hStore).1,
             (storeObject_cdtNodeSlot_eq st pair.2 tid.toObjId _ hStore).2⟩

/-- WS-H4: storeCapabilityRef preserves CDT fields. -/
theorem storeCapabilityRef_cdt_eq
    (st st' : SystemState) (ref : SlotRef) (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot ∧
    st'.cdtSlotNode = st.cdtSlotNode ∧ st'.objects = st.objects := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; exact ⟨rfl, rfl, rfl, rfl⟩

/-- WS-H4: clearCapabilityRefsState preserves CDT fields and objects. -/
private theorem clearCapabilityRefsState_cdt_eq
    (refs : List SlotRef) (st : SystemState) :
    (clearCapabilityRefsState refs st).cdt = st.cdt ∧
    (clearCapabilityRefsState refs st).cdtNodeSlot = st.cdtNodeSlot ∧
    (clearCapabilityRefsState refs st).cdtSlotNode = st.cdtSlotNode ∧
    (clearCapabilityRefsState refs st).objects = st.objects := by
  induction refs generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons ref rest ih =>
    simp only [clearCapabilityRefsState]
    exact ih _

/-- WS-H4: clearCapabilityRefs (monadic form) preserves CDT fields and objects. -/
theorem clearCapabilityRefs_cdt_eq
    (st st' : SystemState) (refs : List SlotRef)
    (hStep : clearCapabilityRefs refs st = .ok ((), st')) :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot ∧
    st'.cdtSlotNode = st.cdtSlotNode ∧ st'.objects = st.objects := by
  unfold clearCapabilityRefs at hStep; cases hStep
  exact clearCapabilityRefsState_cdt_eq refs st

/-- WS-H4: Transfer all three new predicates through a storeObject that is
not a CNode. Combines cspaceSlotCountBounded + cdtCompleteness + cdtAcyclicity. -/
private theorem cdtPredicates_of_storeObject_nonCNode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hNotCNode : ∀ cn, obj ≠ .cnode cn) :
    cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' := by
  have hCdt := storeObject_cdt_eq st st' oid obj hStore
  have ⟨hNS, _⟩ := storeObject_cdtNodeSlot_eq st st' oid obj hStore
  exact ⟨cspaceSlotCountBounded_of_storeObject_nonCNode st st' oid obj hBounded hStore hNotCNode,
    cdtCompleteness_of_storeObject st st' oid obj hComp hStore hNS,
    cdtAcyclicity_of_cdt_eq st st' hAcyclic hCdt⟩

/-- WS-H4: Transfer all three new predicates when objects and CDT fields are
both preserved. Used for scheduler-only updates (removeRunnable, ensureRunnable). -/
private theorem cdtPredicates_of_objects_cdtNodeSlot_eq
    (st st' : SystemState)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hObjEq : st'.objects = st.objects)
    (hCdtEq : st'.cdt = st.cdt)
    (hNodeSlotEq : st'.cdtNodeSlot = st.cdtNodeSlot) :
    cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' :=
  ⟨cspaceSlotCountBounded_of_objects_eq st st' hBounded hObjEq,
   cdtCompleteness_of_objects_nodeSlot_eq st st' hComp hObjEq hNodeSlotEq,
   cdtAcyclicity_of_cdt_eq st st' hAcyclic hCdtEq⟩

/-- WS-H4: detachSlotFromCdt preserves cdtCompleteness.
detachSlotFromCdt only clears entries from cdtNodeSlot (making the quantifier
vacuously true) and preserves objects. -/
theorem cdtCompleteness_of_detachSlotFromCdt
    (st : SystemState) (ref : SlotRef)
    (hComp : cdtCompleteness st) :
    cdtCompleteness (st.detachSlotFromCdt ref) := by
  intro nodeId slotRef hNS
  unfold SystemState.detachSlotFromCdt at hNS ⊢
  cases hLookup : st.cdtSlotNode[ref]? with
  | none => simp only [hLookup] at hNS ⊢; exact hComp nodeId slotRef hNS
  | some origNode =>
    simp only [hLookup] at hNS ⊢
    -- objects unchanged except possibly at `origNode` erased by detach.
    by_cases hEq : nodeId = origNode
    · subst hEq
      rw [HashMap_getElem?_erase] at hNS
      simp at hNS
    · rw [HashMap_getElem?_erase] at hNS
      have hNeBeq : ¬((origNode == nodeId) = true) := by
        intro hBeq
        exact hEq (eq_of_beq hBeq).symm
      simp [hNeBeq] at hNS
      exact hComp nodeId slotRef hNS

/-- WS-H4: detachSlotFromCdt preserves cdtAcyclicity (CDT edges unchanged). -/
theorem cdtAcyclicity_of_detachSlotFromCdt
    (st : SystemState) (ref : SlotRef)
    (hAcyclic : cdtAcyclicity st) :
    cdtAcyclicity (st.detachSlotFromCdt ref) := by
  unfold cdtAcyclicity
  show (st.detachSlotFromCdt ref).cdt.edgeWellFounded
  have : (st.detachSlotFromCdt ref).cdt = st.cdt := by
    unfold SystemState.detachSlotFromCdt; cases st.cdtSlotNode[ref]? <;> rfl
  rw [this]; exact hAcyclic

/-- WS-H4: detachSlotFromCdt preserves cspaceSlotCountBounded (objects unchanged). -/
theorem cspaceSlotCountBounded_of_detachSlotFromCdt
    (st : SystemState) (ref : SlotRef)
    (hBounded : cspaceSlotCountBounded st) :
    cspaceSlotCountBounded (st.detachSlotFromCdt ref) := by
  exact cspaceSlotCountBounded_of_objects_eq st _ hBounded
    (SystemState.detachSlotFromCdt_objects_eq st ref)

/-- WS-H4: Transfer all three new predicates through detachSlotFromCdt. -/
private theorem cdtPredicates_of_detachSlotFromCdt
    (st : SystemState) (ref : SlotRef)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st) :
    cspaceSlotCountBounded (st.detachSlotFromCdt ref) ∧
    cdtCompleteness (st.detachSlotFromCdt ref) ∧
    cdtAcyclicity (st.detachSlotFromCdt ref) :=
  ⟨cspaceSlotCountBounded_of_detachSlotFromCdt st ref hBounded,
   cdtCompleteness_of_detachSlotFromCdt st ref hComp,
   cdtAcyclicity_of_detachSlotFromCdt st ref hAcyclic⟩

/-- WS-H13: Transfer cspaceDepthConsistent when objects are unchanged. -/
theorem cspaceDepthConsistent_of_objects_eq
    (st st' : SystemState)
    (hDepth : cspaceDepthConsistent st)
    (hObjEq : st'.objects = st.objects) :
    cspaceDepthConsistent st' := by
  intro cnodeId cn hObj; rw [hObjEq] at hObj; exact hDepth cnodeId cn hObj

/-- WS-H13: Transfer cspaceDepthConsistent through storeObject when the stored
object is NOT a CNode (endpoint, TCB, etc.). -/
private theorem cspaceDepthConsistent_of_storeObject_nonCNode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hDepth : cspaceDepthConsistent st)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hNotCNode : ∀ cn, obj ≠ .cnode cn) :
    cspaceDepthConsistent st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = oid
  · subst hEq
    have := storeObject_objects_eq st st' cnodeId obj hStore
    rw [this] at hObj; cases obj with
    | cnode cn' => exact absurd rfl (hNotCNode cn')
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => cases hObj
  · rw [storeObject_objects_ne st st' oid cnodeId obj hEq hStore] at hObj
    exact hDepth cnodeId cn hObj

/-- WS-H13: Transfer cspaceDepthConsistent through storeObject when the stored
CNode has the same depth and bit-width fields as the pre-state CNode at that oid.
This covers CNode.insert, CNode.remove, and CNode.revokeTargetLocal. -/
theorem cspaceDepthConsistent_of_storeObject_sameCNode
    (st st' : SystemState) (targetOid : SeLe4n.ObjId) (preCn cn' : CNode)
    (hDepth : cspaceDepthConsistent st)
    (hPreObj : st.objects[targetOid]? = some (.cnode preCn))
    (hStore : storeObject targetOid (.cnode cn') st = .ok ((), st'))
    (hSameDepth : cn'.depth = preCn.depth)
    (hSameGW : cn'.guardWidth = preCn.guardWidth)
    (hSameRW : cn'.radixWidth = preCn.radixWidth) :
    cspaceDepthConsistent st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = targetOid
  · rw [hEq] at hObj
    rw [storeObject_objects_eq st st' targetOid (.cnode cn') hStore] at hObj; cases hObj
    have hPreBound := hDepth targetOid preCn hPreObj
    constructor
    · rw [hSameDepth]; exact hPreBound.1
    · intro hBits
      have hBitsPre : preCn.bitsConsumed > 0 := by
        unfold CNode.bitsConsumed at hBits ⊢; rw [hSameGW, hSameRW] at hBits; exact hBits
      have hWfPre := hPreBound.2 hBitsPre
      unfold CNode.wellFormed at hWfPre ⊢
      constructor
      · unfold CNode.bitsConsumed at hWfPre ⊢; rw [hSameGW, hSameRW, hSameDepth]; exact hWfPre.1
      · unfold CNode.bitsConsumed at hWfPre ⊢; rw [hSameGW, hSameRW]; exact hWfPre.2
  · rw [storeObject_objects_ne st st' targetOid cnodeId (.cnode cn') hEq hStore] at hObj
    exact hDepth cnodeId cn hObj

/-- WS-H13: Transfer cspaceDepthConsistent through storeObject when inserting a capability
into a CNode, given the inserted capability satisfies the parent-child depth constraint. -/
theorem cspaceDepthConsistent_of_storeObject_insertCNode
    (st st' : SystemState) (targetOid : SeLe4n.ObjId) (preCn : CNode)
    (insertSlot : SeLe4n.Slot) (insertCap : Capability)
    (hDepth : cspaceDepthConsistent st)
    (hPreObj : st.objects[targetOid]? = some (.cnode preCn))
    (hStore : storeObject targetOid (.cnode (preCn.insert insertSlot insertCap)) st = .ok ((), st')) :
    cspaceDepthConsistent st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = targetOid
  · rw [hEq] at hObj
    rw [storeObject_objects_eq st st' targetOid _ hStore] at hObj; cases hObj
    exact hDepth targetOid preCn hPreObj
  · rw [storeObject_objects_ne st st' targetOid cnodeId _ hEq hStore] at hObj
    exact hDepth cnodeId cn hObj

/-- WS-H13: Transfer cspaceDepthConsistent through detachSlotFromCdt (objects unchanged). -/
theorem cspaceDepthConsistent_of_detachSlotFromCdt
    (st : SystemState) (ref : SlotRef)
    (hDepth : cspaceDepthConsistent st) :
    cspaceDepthConsistent (st.detachSlotFromCdt ref) :=
  cspaceDepthConsistent_of_objects_eq st _ hDepth
    (SystemState.detachSlotFromCdt_objects_eq st ref)

/-- WS-H13: CNode.remove preserves depth/guardWidth/radixWidth and has slot subset. -/
private theorem CNode.remove_depth_eq (cn : CNode) (slot : SeLe4n.Slot) :
    (cn.remove slot).depth = cn.depth := rfl

private theorem CNode.remove_guardWidth_eq (cn : CNode) (slot : SeLe4n.Slot) :
    (cn.remove slot).guardWidth = cn.guardWidth := rfl

private theorem CNode.remove_radixWidth_eq (cn : CNode) (slot : SeLe4n.Slot) :
    (cn.remove slot).radixWidth = cn.radixWidth := rfl

private theorem CNode.remove_slots_sub (cn : CNode) (slot : SeLe4n.Slot) :
    ∀ (s : SeLe4n.Slot) (cap : Capability), (cn.remove slot).slots[s]? = some cap → cn.slots[s]? = some cap := by
  intro s cap hLookup
  simp [CNode.remove] at hLookup
  rw [Std.HashMap.getElem?_erase] at hLookup
  by_cases h : (slot == s) = true
  · simp [h] at hLookup
  · simp [h] at hLookup; exact hLookup

/-- WS-H13: CNode.revokeTargetLocal preserves depth/guardWidth/radixWidth and has slot subset. -/
private theorem CNode.revokeTargetLocal_depth_eq (cn : CNode) (slot : SeLe4n.Slot) (target : CapTarget) :
    (cn.revokeTargetLocal slot target).depth = cn.depth := rfl

private theorem CNode.revokeTargetLocal_guardWidth_eq (cn : CNode) (slot : SeLe4n.Slot) (target : CapTarget) :
    (cn.revokeTargetLocal slot target).guardWidth = cn.guardWidth := rfl

private theorem CNode.revokeTargetLocal_radixWidth_eq (cn : CNode) (slot : SeLe4n.Slot) (target : CapTarget) :
    (cn.revokeTargetLocal slot target).radixWidth = cn.radixWidth := rfl

private theorem CNode.revokeTargetLocal_slots_sub (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) :
    ∀ (s : SeLe4n.Slot) (cap : Capability), (cn.revokeTargetLocal sourceSlot target).slots[s]? = some cap → cn.slots[s]? = some cap := by
  intro s cap hLookup
  simp only [CNode.revokeTargetLocal] at hLookup
  -- Filter only keeps entries from the original map
  have hMem : s ∈ cn.slots.filter (fun s c => s == sourceSlot || !(c.target == target)) :=
    Std.HashMap.mem_iff_isSome_getElem?.mpr (by rw [hLookup]; rfl)
  have hMemOrig : s ∈ cn.slots := Std.HashMap.mem_of_mem_filter hMem
  -- Reconstruct the value
  have h1 : (cn.slots.filter (fun s c => s == sourceSlot || !(c.target == target)))[s]? =
      some ((cn.slots.filter (fun s c => s == sourceSlot || !(c.target == target)))[s]) :=
    Std.HashMap.getElem?_eq_some_getElem hMem
  have h2 : cn.slots[s]? = some cn.slots[s] := Std.HashMap.getElem?_eq_some_getElem hMemOrig
  rw [h1] at hLookup
  have hCapEq := (Option.some.inj hLookup).symm
  rw [hCapEq, Std.HashMap.getElem_filter (m := cn.slots)
    (f := fun s c => s == sourceSlot || !(c.target == target))]
  exact h2

/-- WS-H13: CNode.insert preserves depth/guardWidth/radixWidth. -/
private theorem CNode.insert_depth_eq (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).depth = cn.depth := rfl

private theorem CNode.insert_guardWidth_eq (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).guardWidth = cn.guardWidth := rfl

private theorem CNode.insert_radixWidth_eq (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).radixWidth = cn.radixWidth := rfl

/-- WS-H4: CDT-only state update preserves cspaceSlotCountBounded and cdtCompleteness.
Used for `{ st with cdt := cdt' }` where objects and cdtNodeSlot are unchanged. -/
private theorem boundedCompleteness_of_cdt_only_update
    (st : SystemState) (cdt' : CapDerivationTree)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) :
    cspaceSlotCountBounded { st with cdt := cdt' } ∧
    cdtCompleteness { st with cdt := cdt' } :=
  ⟨hBounded, hComp⟩

/-- WS-H4: Transfer WS-H4 predicates through endpoint/TCB blocking path.
storeObject(.endpoint) → storeTcbIpcState → removeRunnable preserves all three. -/
private theorem cdtPredicates_through_blocking_path
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ep : Endpoint) (ipc : ThreadIpcState)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hStore : storeObject endpointId (.endpoint ep) st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target ipc = .ok st2) :
    cspaceSlotCountBounded (removeRunnable st2 target) ∧
    cdtCompleteness (removeRunnable st2 target) ∧
    cdtAcyclicity (removeRunnable st2 target) := by
  have hCdt1 := storeObject_cdt_eq st st1 endpointId (.endpoint ep) hStore
  have ⟨hNS1, _⟩ := storeObject_cdtNodeSlot_eq st st1 endpointId (.endpoint ep) hStore
  have ⟨hCdt2, hNS2, _⟩ := storeTcbIpcState_cdt_eq st1 st2 target ipc hTcb
  have hBnd1 := cspaceSlotCountBounded_of_storeObject_nonCNode st st1 endpointId (.endpoint ep)
    hBounded hStore (fun cn h => by cases h)
  have hBnd2 := cspaceSlotCountBounded_of_storeTcbIpcState st1 st2 target ipc hBnd1 hTcb
  refine ⟨?_, ?_, ?_⟩
  · exact cspaceSlotCountBounded_of_objects_eq st2 _ hBnd2 (removeRunnable_preserves_objects st2 target)
  · -- cdtCompleteness transfers through storeObject, storeTcbIpcState, removeRunnable
    -- All three only replace object entries (never delete), so objects[ref.cnode]? ≠ none is preserved
    have hComp1 := cdtCompleteness_of_storeObject st st1 endpointId (.endpoint ep) hComp hStore hNS1
    have hComp2 : cdtCompleteness st2 := by
      unfold storeTcbIpcState at hTcb
      cases hLookup : lookupTcb st1 target with
      | none => simp [hLookup] at hTcb
      | some tcb =>
        simp only [hLookup] at hTcb
        cases hS : storeObject target.toObjId (.tcb { tcb with ipcState := ipc }) st1 with
        | error e => simp [hS] at hTcb
        | ok pair =>
          simp only [hS] at hTcb
          have hEq := Except.ok.inj hTcb; subst hEq
          exact cdtCompleteness_of_storeObject st1 pair.2 target.toObjId _ hComp1 hS
            (storeObject_cdtNodeSlot_eq st1 pair.2 target.toObjId _ hS).1
    exact cdtCompleteness_of_objects_nodeSlot_eq st2 _ hComp2
      (removeRunnable_preserves_objects st2 target)
      (by simp [removeRunnable])
  · exact cdtAcyclicity_of_cdt_eq st (removeRunnable st2 target) hAcyclic
      (by show (removeRunnable st2 target).cdt = st.cdt; simp [removeRunnable]; rw [hCdt2, hCdt1])

/-- WS-H4: Transfer WS-H4 predicates through endpoint/TCB handshake path.
storeObject(.endpoint) → storeTcbIpcState → ensureRunnable preserves all three. -/
private theorem cdtPredicates_through_handshake_path
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ep : Endpoint)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hStore : storeObject endpointId (.endpoint ep) st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target .ready = .ok st2) :
    cspaceSlotCountBounded (ensureRunnable st2 target) ∧
    cdtCompleteness (ensureRunnable st2 target) ∧
    cdtAcyclicity (ensureRunnable st2 target) := by
  have hCdt1 := storeObject_cdt_eq st st1 endpointId (.endpoint ep) hStore
  have ⟨hNS1, _⟩ := storeObject_cdtNodeSlot_eq st st1 endpointId (.endpoint ep) hStore
  have ⟨hCdt2, hNS2, _⟩ := storeTcbIpcState_cdt_eq st1 st2 target .ready hTcb
  have hBnd1 := cspaceSlotCountBounded_of_storeObject_nonCNode st st1 endpointId (.endpoint ep)
    hBounded hStore (fun cn h => by cases h)
  have hBnd2 := cspaceSlotCountBounded_of_storeTcbIpcState st1 st2 target .ready hBnd1 hTcb
  have hComp1 := cdtCompleteness_of_storeObject st st1 endpointId (.endpoint ep) hComp hStore hNS1
  have hComp2 : cdtCompleteness st2 := by
    unfold storeTcbIpcState at hTcb
    cases hLookup : lookupTcb st1 target with
    | none => simp [hLookup] at hTcb
    | some tcb =>
      simp only [hLookup] at hTcb
      cases hS : storeObject target.toObjId (.tcb { tcb with ipcState := .ready }) st1 with
      | error e => simp [hS] at hTcb
      | ok pair =>
        simp only [hS] at hTcb
        have hEq := Except.ok.inj hTcb; subst hEq
        exact cdtCompleteness_of_storeObject st1 pair.2 target.toObjId _ hComp1 hS
          (storeObject_cdtNodeSlot_eq st1 pair.2 target.toObjId _ hS).1
  have hEnsNS : (ensureRunnable st2 target).cdtNodeSlot = st2.cdtNodeSlot := by
    unfold ensureRunnable
    split
    · rfl
    · split
      · rfl
      · rfl
  have hEnsCdt : (ensureRunnable st2 target).cdt = st.cdt := by
    unfold ensureRunnable; split
    · rw [hCdt2, hCdt1]
    · split <;> rw [hCdt2, hCdt1]
  exact ⟨cspaceSlotCountBounded_of_objects_eq st2 _ hBnd2 (ensureRunnable_preserves_objects st2 target),
    cdtCompleteness_of_objects_nodeSlot_eq st2 _ hComp2
      (ensureRunnable_preserves_objects st2 target) hEnsNS,
    cdtAcyclicity_of_cdt_eq st _ hAcyclic hEnsCdt⟩

/-- WS-H4: Transfer WS-H4 predicates through reply path.
storeTcbIpcStateAndMessage → ensureRunnable preserves all three. -/
theorem cdtPredicates_through_reply_path
    (st st1 : SystemState) (target : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hTcb : storeTcbIpcStateAndMessage st target ipc msg = .ok st1) :
    cspaceSlotCountBounded (ensureRunnable st1 target) ∧
    cdtCompleteness (ensureRunnable st1 target) ∧
    cdtAcyclicity (ensureRunnable st1 target) := by
  have ⟨hCdt1, hNS1, _⟩ := storeTcbIpcStateAndMessage_cdt_eq st st1 target ipc msg hTcb
  have hBnd1 : cspaceSlotCountBounded st1 := by
    unfold storeTcbIpcStateAndMessage at hTcb
    cases hL : lookupTcb st target with
    | none => simp [hL] at hTcb
    | some tcb =>
      simp only [hL] at hTcb
      cases hS : storeObject target.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
      | error e => simp [hS] at hTcb
      | ok pair =>
        simp only [hS] at hTcb; have hEq := Except.ok.inj hTcb; subst hEq
        exact cspaceSlotCountBounded_of_storeObject_nonCNode st pair.2 target.toObjId _ hBounded hS
          (fun cn h => by cases h)
  have hComp1 : cdtCompleteness st1 := by
    unfold storeTcbIpcStateAndMessage at hTcb
    cases hL : lookupTcb st target with
    | none => simp [hL] at hTcb
    | some tcb =>
      simp only [hL] at hTcb
      cases hS : storeObject target.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
      | error e => simp [hS] at hTcb
      | ok pair =>
        simp only [hS] at hTcb; have hEq := Except.ok.inj hTcb; subst hEq
        exact cdtCompleteness_of_storeObject st pair.2 target.toObjId _ hComp hS
          (storeObject_cdtNodeSlot_eq st pair.2 target.toObjId _ hS).1
  have hEnsNS : (ensureRunnable st1 target).cdtNodeSlot = st1.cdtNodeSlot := by
    unfold ensureRunnable
    split
    · rfl
    · split
      · rfl
      · rfl
  have hEnsCdt : (ensureRunnable st1 target).cdt = st.cdt := by
    unfold ensureRunnable; split
    · rw [hCdt1]
    · split <;> rw [hCdt1]
  exact ⟨cspaceSlotCountBounded_of_objects_eq st1 _ hBnd1 (ensureRunnable_preserves_objects st1 target),
    cdtCompleteness_of_objects_nodeSlot_eq st1 _ hComp1
      (ensureRunnable_preserves_objects st1 target) hEnsNS,
    cdtAcyclicity_of_cdt_eq st _ hAcyclic hEnsCdt⟩
