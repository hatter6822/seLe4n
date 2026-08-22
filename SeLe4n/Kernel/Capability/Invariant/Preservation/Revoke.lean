-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.CopyMoveMutate

/-!
AN4-F.3 (CAP-M03) child module extracted from
`SeLe4n.Kernel.Capability.Invariant.Preservation`. Contains the CDT-revocation
preservation cluster: `processRevokeNode` + the private fold helpers
(`revokeCdtFoldBody`, `revokeCdtFold_preserves`), the compositional
preservation theorems for `cspaceRevokeCdt`, `cspaceRevokeCdtStrict`,
and `cspaceRevokeCdtStreaming`, and the `capabilityInvariantBundle_of_cdt_update`
helper. Private fold infrastructure is promoted to public so the hub and
future cross-subsystem consumers can reason about the fold shape.
All declarations retain their original names, order, and proofs.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Internal

-- ============================================================================
-- WS-F4/F-06: cspaceRevokeCdt and cspaceRevokeCdtStrict preservation
-- ============================================================================

/-- Helper: CDT-only state updates preserve capabilityInvariantBundle,
given that the new CDT is acyclic. -/
theorem capabilityInvariantBundle_of_cdt_update
    (st : SystemState) (cdt' : CapDerivationTree)
    (hInv : capabilityInvariantBundle st)
    (hAcyclic' : cdt'.edgeWellFounded) :
    capabilityInvariantBundle { st with cdt := cdt' } := by
  rcases hInv with ⟨_, hBnd, hComp, _, hDepthPre, hObjInvPre⟩
  have hObjEq : ({ st with cdt := cdt' } : SystemState).objects = st.objects := rfl
  -- WS-RC R4.A.6: cspaceSlotUnique conjunct removed from bundle; the new
  -- 6-tuple skips the legacy uniqueness slot.
  exact ⟨cspaceLookupSound_holds _,
    hBnd, hComp, hAcyclic',
    cspaceDepthConsistent_of_objects_eq st _ hDepthPre hObjEq,
    hObjEq ▸ hObjInvPre⟩

/-- `processRevokeNode` preserves `cdtNodeSlot.invExtK`
when it succeeds. -/
theorem processRevokeNode_preserves_cdtNodeSlot
    (st st' : SystemState) (node : CdtNodeId)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : processRevokeNode st node = .ok st') :
    st'.cdtNodeSlot.invExtK := by
  unfold processRevokeNode at hStep
  cases hSlot : SystemState.lookupCdtSlotOfNode st node with
  | none => simp [hSlot] at hStep; cases hStep; exact hNodeSlotK
  | some descAddr =>
    simp [hSlot] at hStep
    cases hDel : cspaceDeleteSlotCore descAddr st with
    | error _ => simp [hDel] at hStep
    | ok pair =>
      obtain ⟨_, stDel⟩ := pair
      -- V5-N: After removing redundant detachSlotFromCdt, the post-state is
      -- { stDel with cdt := stDel.cdt.removeNode node }, which has the same
      -- cdtNodeSlot as stDel (only cdt is changed by removeNode).
      simp [hDel] at hStep; cases hStep
      have hKDel := cspaceDeleteSlotCore_preserves_cdtNodeSlot st stDel descAddr
        hNodeSlotK hDel
      exact hKDel

/-- R2-A/R2-F: `processRevokeNode` preserves the full capability invariant bundle
when it succeeds.

Two cases handled:
- **No slot mapping** (`lookupCdtSlotOfNode = none`): just `removeNode` — CDT-only
  update preserves all object-level invariants.
- **Successful delete**: chains `cspaceDeleteSlot_preserves` → `detachSlotFromCdt`
  invariant reconstruction → `removeNode` CDT update.

The error case (`cspaceDeleteSlot` fails) now returns `.error` and does not
produce a post-state, so no invariant proof is needed for that path.

This is the single proof obligation for per-node revocation, shared by both the
materialized fold (`cspaceRevokeCdt`) and streaming BFS (`streamingRevokeBFS`). -/
theorem processRevokeNode_preserves_capabilityInvariantBundle
    (st st' : SystemState) (node : CdtNodeId)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : processRevokeNode st node = .ok st') :
    capabilityInvariantBundle st' := by
  unfold processRevokeNode at hStep
  cases hSlot : SystemState.lookupCdtSlotOfNode st node with
  | none =>
    simp [hSlot] at hStep; cases hStep
    exact capabilityInvariantBundle_of_cdt_update st _ hInv
      (CapDerivationTree.edgeWellFounded_sub _ _ hInv.2.2.2.1 (CapDerivationTree.removeNode_edges_sub st.cdt node))
  | some descAddr =>
    simp [hSlot] at hStep
    cases hDel : cspaceDeleteSlotCore descAddr st with
    | error _ => simp [hDel] at hStep
    | ok pair =>
      obtain ⟨_, stDel⟩ := pair
      -- V5-N: processRevokeNode no longer calls detachSlotFromCdt after
      -- cspaceDeleteSlotCore (it's already done inside cspaceDeleteSlotCore).
      -- The proof goes directly from stDel to removeNode.
      simp [hDel] at hStep; cases hStep
      have hDelInv := cspaceDeleteSlotCore_preserves_capabilityInvariantBundle st stDel descAddr hInv
        hNodeSlotK hDel
      have hKDel :=
        cspaceDeleteSlotCore_preserves_cdtNodeSlot st stDel descAddr hNodeSlotK hDel
      exact capabilityInvariantBundle_of_cdt_update _ _ hDelInv
        (CapDerivationTree.edgeWellFounded_sub _ _ hDelInv.2.2.2.1
          (CapDerivationTree.removeNode_edges_sub stDel.cdt node))

/-- Fold body function for cspaceRevokeCdt: processes one CDT descendant node.
Delegates to `processRevokeNode` for the actual state transformation.
Updated in WS-R2 to handle `processRevokeNode`'s `Except` return type. -/
def revokeCdtFoldBody
    (acc : Except KernelError (Unit × SystemState)) (node : CdtNodeId) :
    Except KernelError (Unit × SystemState) :=
  match acc with
  | .error e => .error e
  | .ok ((), stAcc) =>
      match processRevokeNode stAcc node with
      | .error e => .error e
      | .ok stNext => .ok ((), stNext)

/-- Single fold step preserves capabilityInvariantBundle.
Delegates to `processRevokeNode_preserves_capabilityInvariantBundle`. -/
theorem revokeCdtFoldBody_preserves
    (stAcc stNext : SystemState) (node : CdtNodeId)
    (hInv : capabilityInvariantBundle stAcc)
    (hNodeSlotK : stAcc.cdtNodeSlot.invExtK)
    (hStep : revokeCdtFoldBody (.ok ((), stAcc)) node = .ok ((), stNext)) :
    capabilityInvariantBundle stNext ∧ stNext.cdtNodeSlot.invExtK := by
  unfold revokeCdtFoldBody at hStep
  simp only [] at hStep
  cases hProc : processRevokeNode stAcc node with
  | error e => simp [hProc] at hStep
  | ok stMid =>
    simp [hProc] at hStep; subst hStep
    exact ⟨processRevokeNode_preserves_capabilityInvariantBundle stAcc stMid node hInv hNodeSlotK hProc,
           processRevokeNode_preserves_cdtNodeSlot stAcc stMid node hNodeSlotK hProc⟩

/-- Error propagation: revokeCdtFoldBody propagates errors unchanged. -/
theorem revokeCdtFoldBody_error (e : KernelError) (node : CdtNodeId) :
    revokeCdtFoldBody (.error e) node = .error e := by
  unfold revokeCdtFoldBody; rfl

/-- Fold error propagation: foldl revokeCdtFoldBody starting from error stays error. -/
theorem revokeCdtFoldBody_foldl_error
    (nodes : List CdtNodeId) (e : KernelError) :
    nodes.foldl revokeCdtFoldBody (.error e) = .error e := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => simp [List.foldl, revokeCdtFoldBody_error, ih]

/-- Fold induction: cspaceRevokeCdt fold preserves capabilityInvariantBundle. -/
theorem revokeCdtFold_preserves
    (nodes : List CdtNodeId)
    (stInit stFinal : SystemState)
    (hInv : capabilityInvariantBundle stInit)
    (hNodeSlotK : stInit.cdtNodeSlot.invExtK)
    (hFold : nodes.foldl revokeCdtFoldBody (.ok ((), stInit)) = .ok ((), stFinal)) :
    capabilityInvariantBundle stFinal := by
  induction nodes generalizing stInit stFinal with
  | nil =>
    simp [List.foldl] at hFold; cases hFold; exact hInv
  | cons node rest ih =>
    simp only [List.foldl] at hFold
    -- Case split on whether the step succeeds or errors
    cases hStep : revokeCdtFoldBody (.ok ((), stInit)) node with
    | error e =>
      rw [hStep, revokeCdtFoldBody_foldl_error] at hFold; simp at hFold
    | ok val =>
      obtain ⟨_, stMid⟩ := val
      rw [hStep] at hFold
      have ⟨hInvMid, hKMid⟩ := revokeCdtFoldBody_preserves stInit stMid node hInv hNodeSlotK hStep
      exact ih stMid stFinal hInvMid hKMid hFold

/-- **Consuming in-flight transfers preserves the capability bundle.**

Every conjunct quantifies over `.cnode` lookups (and, for
`replyCapPointsToValidReply`, a `.reply` lookup), and the sweep rewrites only
TCBs -- so `revokePendingTransfersFrom_frame` frames all seven.  This is what
lets `cspaceRevokeCdt` close the in-flight hole without weakening anything it
already proved. -/
theorem revokePendingTransfersFrom_preserves_capabilityInvariantBundle
    (st : SystemState) (nodes : List CdtNodeId)
    (hInv : capabilityInvariantBundle st) :
    capabilityInvariantBundle (revokePendingTransfersFrom st nodes) := by
  obtain ⟨hSound, hBounded, hComp, hAcyclic, hDepth, hExt, hReply⟩ := hInv
  obtain ⟨hExt', hCdt, hNS, _, hObj⟩ := revokePendingTransfersFrom_frame st nodes hExt
  -- Every CNode the post-state exposes was already there: the sweep's only
  -- writes are TCBs, so the `.tcb` half of the frame cannot produce a `.cnode`.
  have hCnode : ∀ (oid : SeLe4n.ObjId) (cn : CNode),
      (revokePendingTransfersFrom st nodes).objects[oid]? = some (KernelObject.cnode cn) →
      st.objects[oid]? = some (KernelObject.cnode cn) := by
    intro oid cn h
    rcases hObj oid with hEq | ⟨_, _, _, hT⟩
    · rw [h] at hEq; exact hEq.symm
    · rw [h] at hT; cases hT
  refine ⟨?_, ?_, ?_, ?_, ?_, hExt', ?_⟩
  · intro cnodeId cn slot cap hCn hLk
    have hOrig := hSound cnodeId cn slot cap (hCnode cnodeId cn hCn) hLk
    unfold SystemState.lookupSlotCap SystemState.lookupCNode at hOrig ⊢
    rw [hCn]
    rw [hCnode cnodeId cn hCn] at hOrig
    exact hOrig
  · intro cnodeId cn hCn; exact hBounded cnodeId cn (hCnode cnodeId cn hCn)
  · intro nodeId ref hRef
    have hRef' : st.cdtNodeSlot[nodeId]? = some ref := by rw [← hNS]; exact hRef
    have hNe := hComp nodeId ref hRef'
    intro hNone
    apply hNe
    rcases hObj ref.cnode with hEq | ⟨_, _, _, hT'⟩
    · rw [← hEq]; exact hNone
    · rw [hNone] at hT'; cases hT'
  · unfold cdtAcyclicity at hAcyclic ⊢; rw [hCdt]; exact hAcyclic
  · intro cnodeId cn hCn; exact hDepth cnodeId cn (hCnode cnodeId cn hCn)
  · intro oid cn slot cap rid hCn hLk hTarget
    have hOrig := hReply oid cn slot cap rid (hCnode oid cn hCn) hLk hTarget
    unfold SystemState.getReply? at hOrig ⊢
    rcases hObj rid.toObjId with hEq | ⟨_, _, hT, _⟩
    · rw [hEq]; exact hOrig
    · rw [hT] at hOrig; simp at hOrig

/-- **The local revoke leaves `cdtNodeSlot` alone.**

`storeObject` and `revokeAndClearRefsState` both preserve it, so the node→slot
map a caller carried into `cspaceRevoke` is the one it carries out.

Extracted from the three revocation preservation theorems that each held a
verbatim copy of this derivation. -/
theorem cspaceRevoke_preserves_cdtNodeSlot
    (st stLocal : SystemState) (addr : CSpaceAddr)
    (hRevoke : cspaceRevoke addr st = .ok ((), stLocal)) :
    stLocal.cdtNodeSlot = st.cdtNodeSlot := by
  unfold cspaceRevoke at hRevoke
  cases hLookup : cspaceLookupSlot addr st with
  | error e => simp [hLookup] at hRevoke
  | ok pair =>
    rcases pair with ⟨parent, st1⟩
    have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr parent hLookup
    subst st1; simp [hLookup] at hRevoke
    cases hObj : st.objects[addr.cnode]? with
    | none => simp [hObj] at hRevoke
    | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hRevoke
      | cnode preCn =>
        simp [hObj] at hRevoke
        cases hStore : storeObject addr.cnode
            (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) st with
        | error e => simp [hStore] at hRevoke
        | ok pair =>
          obtain ⟨_, stMid⟩ := pair; simp [hStore] at hRevoke; rw [← hRevoke]
          have hNSMid := (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
          have ⟨_, hNSClear, _, _⟩ :=
            revokeAndClearRefsState_cdt_eq preCn addr.slot parent.target addr.cnode stMid
          rw [hNSClear, hNSMid]

/-- **The scaffold preserves the bundle whenever its traversal does.**

The revocation entry points shared a preservation *argument* as well as a
transition: local revoke, then a walk, then (since the in-flight fix) the
consuming sweep, with the same two framing steps at either end.  Each variant's
theorem re-derived all of it.  Proved once here, a variant's obligation is
exactly its traversal's — which is the only part that differs.

`hTraverse` is stated over an arbitrary traversal, so this covers the four
variants that exist and any that do not exist yet. -/
theorem revokeCdtScaffold_preserves_capabilityInvariantBundle {ρ : Type}
    (emptyReport : ρ)
    (traverse : SystemState → CdtNodeId → List CdtNodeId →
      Except KernelError (RevokeTraversalOutcome ρ))
    (hTraverse : ∀ (stLocal : SystemState) (rootNode : CdtNodeId)
        (descendants : List CdtNodeId) (out : RevokeTraversalOutcome ρ),
        capabilityInvariantBundle stLocal → stLocal.cdtNodeSlot.invExtK →
        traverse stLocal rootNode descendants = .ok out →
        capabilityInvariantBundle out.state)
    (st st' : SystemState) (addr : CSpaceAddr) (r : ρ)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : revokeCdtScaffold emptyReport traverse addr st = .ok (r, st')) :
    capabilityInvariantBundle st' := by
  unfold revokeCdtScaffold at hStep
  split at hStep
  · simp at hStep
  · rename_i stLocal hRevoke
    have hLocalInv :=
      cspaceRevoke_preserves_capabilityInvariantBundle st stLocal addr hInv hRevoke
    have hLocalK : stLocal.cdtNodeSlot.invExtK :=
      cspaceRevoke_preserves_cdtNodeSlot st stLocal addr hRevoke ▸ hNodeSlotK
    split at hStep
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨_, hEq⟩ := hStep; exact hEq ▸ hLocalInv
    · rename_i rootNode _
      split at hStep
      · simp at hStep
      · rename_i out hTrav
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep; subst hEq
        exact revokePendingTransfersFrom_preserves_capabilityInvariantBundle _ _
          (hTraverse stLocal rootNode _ out hLocalInv hLocalK hTrav)

/-- The materialized traversal preserves the bundle: it is `revokeCdtFoldBody`
under a different spelling. -/
theorem revokeCdtMaterializedTraversal_preserves
    (stLocal : SystemState) (rootNode : CdtNodeId) (descendants : List CdtNodeId)
    (out : RevokeTraversalOutcome Unit)
    (hInv : capabilityInvariantBundle stLocal)
    (hNodeSlotK : stLocal.cdtNodeSlot.invExtK)
    (hTrav : revokeCdtMaterializedTraversal stLocal rootNode descendants = .ok out) :
    capabilityInvariantBundle out.state := by
  unfold revokeCdtMaterializedTraversal at hTrav
  split at hTrav
  · simp at hTrav
  · rename_i stDone hFold
    simp only [Except.ok.injEq] at hTrav
    subst hTrav
    -- the inline lambda is definitionally equal to `revokeCdtFoldBody`
    change descendants.foldl revokeCdtFoldBody (.ok ((), stLocal)) = .ok ((), stDone) at hFold
    exact revokeCdtFold_preserves _ stLocal stDone hInv hNodeSlotK hFold

/-- R2-F: Error propagation consistency theorem. When `cspaceDeleteSlotCore` fails
for a CDT descendant, `processRevokeNode` (and therefore `revokeCdtFoldBody`)
now propagates the error. This theorem proves that the error propagation is
correct: the fold body returns the same error that `cspaceDeleteSlotCore` produced.
This replaces the former `cspaceRevokeCdt_swallowed_error_consistent` theorem. -/
theorem cspaceRevokeCdt_error_propagation_consistent
    (stAcc : SystemState) (node : CdtNodeId)
    (descAddr : CSpaceAddr) (err : KernelError)
    (hSlot : SystemState.lookupCdtSlotOfNode stAcc node = some descAddr)
    (hDelErr : cspaceDeleteSlotCore descAddr stAcc = .error err) :
    revokeCdtFoldBody (.ok ((), stAcc)) node = .error err := by
  unfold revokeCdtFoldBody
  simp only []
  unfold processRevokeNode
  simp [hSlot, hDelErr]

/-- R2-F/M-05: Fuel exhaustion preservation theorem. When `streamingRevokeBFS`
returns `.error .resourceExhausted`, the input state is unchanged — the error
is returned before any state modification occurs in the exhaustion case. -/
theorem streamingRevokeBFS_fuel_exhaustion_returns_error
    (queue : List CdtNodeId) (st : SystemState) (node : CdtNodeId)
    (rest : List CdtNodeId)
    (hQueue : queue = node :: rest) :
    streamingRevokeBFS 0 queue st = .error .resourceExhausted := by
  subst hQueue; unfold streamingRevokeBFS; rfl

/-- **The shared reporting step preserves the bundle and `cdtNodeSlot.invExtK`.**

`cspaceRevokeCdtStrict` and `cspaceRevokeCdtTransactional` fold the same step, so
this is proved once rather than restated inline in each variant's theorem — which
is how the transactional variant came to have no preservation theorem at all
while the strict one carried a 25-line copy of the fold body in a `suffices`.

On a deletion failure the state is returned unchanged (AH3-A/L-04 preserves the
CDT node), so that branch is immediate. -/
theorem revokeCdtReportingStep_preserves
    (acc : RevokeCdtStrictReport × SystemState) (node : CdtNodeId)
    (hInv : capabilityInvariantBundle acc.2)
    (hK : acc.2.cdtNodeSlot.invExtK) :
    capabilityInvariantBundle (revokeCdtReportingStep acc node).2 ∧
      (revokeCdtReportingStep acc node).2.cdtNodeSlot.invExtK := by
  obtain ⟨report, stAcc⟩ := acc
  unfold revokeCdtReportingStep
  simp only []
  cases report.firstFailure with
  | some _ => exact ⟨hInv, hK⟩
  | none =>
    simp only []
    cases hSlot : SystemState.lookupCdtSlotOfNode stAcc node with
    | none =>
      simp only []
      exact ⟨capabilityInvariantBundle_of_cdt_update stAcc _ hInv
        (CapDerivationTree.edgeWellFounded_sub _ _ hInv.2.2.2.1
          (CapDerivationTree.removeNode_edges_sub stAcc.cdt node)), hK⟩
    | some descAddr =>
      simp only []
      cases hDel : cspaceDeleteSlotCore descAddr stAcc with
      | error err => simp only []; exact ⟨hInv, hK⟩
      | ok pair =>
        obtain ⟨_, stDel⟩ := pair
        simp only []
        have hDelInv := cspaceDeleteSlotCore_preserves_capabilityInvariantBundle stAcc stDel
          descAddr hInv hK hDel
        have hKDel := cspaceDeleteSlotCore_preserves_cdtNodeSlot stAcc stDel descAddr hK hDel
        exact ⟨capabilityInvariantBundle_of_cdt_update _ _ hDelInv
          (CapDerivationTree.edgeWellFounded_sub _ _ hDelInv.2.2.2.1
            (CapDerivationTree.removeNode_edges_sub stDel.cdt node)), hKDel⟩

/-- The reporting fold preserves the bundle, by induction on the node list. -/
theorem revokeCdtReportingFold_preserves :
    ∀ (nodes : List CdtNodeId) (acc : RevokeCdtStrictReport × SystemState),
      capabilityInvariantBundle acc.2 → acc.2.cdtNodeSlot.invExtK →
      capabilityInvariantBundle (nodes.foldl revokeCdtReportingStep acc).2 := by
  intro nodes
  induction nodes with
  | nil => intro acc hI _; exact hI
  | cons node rest ih =>
    intro acc hI hK
    simp only [List.foldl_cons]
    obtain ⟨hI', hK'⟩ := revokeCdtReportingStep_preserves acc node hI hK
    exact ih _ hI' hK'

/-- The reporting outcome's state is the fold's state, so it inherits the fold's
preservation. Shared by both reporting traversals. -/
theorem revokeCdtReportingOutcome_preserves
    (stLocal : SystemState) (descendants : List CdtNodeId)
    (hInv : capabilityInvariantBundle stLocal)
    (hK : stLocal.cdtNodeSlot.invExtK) :
    capabilityInvariantBundle (revokeCdtReportingOutcome stLocal descendants).state := by
  unfold revokeCdtReportingOutcome
  split
  · rename_i report stFinal hFold
    have hFoldInv := revokeCdtReportingFold_preserves descendants
      ({ deletedSlots := [], firstFailure := none }, stLocal) hInv hK
    rw [hFold] at hFoldInv
    exact hFoldInv

/-- The best-effort reporting traversal preserves the bundle. -/
theorem revokeCdtStrictTraversal_preserves
    (stLocal : SystemState) (rootNode : CdtNodeId) (descendants : List CdtNodeId)
    (out : RevokeTraversalOutcome RevokeCdtStrictReport)
    (hInv : capabilityInvariantBundle stLocal)
    (hK : stLocal.cdtNodeSlot.invExtK)
    (hTrav : revokeCdtStrictTraversal stLocal rootNode descendants = .ok out) :
    capabilityInvariantBundle out.state := by
  unfold revokeCdtStrictTraversal at hTrav
  simp only [Except.ok.injEq] at hTrav
  subst hTrav
  exact revokeCdtReportingOutcome_preserves stLocal descendants hInv hK

/-- The validated reporting traversal preserves the bundle: validation only
inspects state, so a successful validation hands the same state to the same
fold. -/
theorem revokeCdtTransactionalTraversal_preserves
    (stLocal : SystemState) (rootNode : CdtNodeId) (descendants : List CdtNodeId)
    (out : RevokeTraversalOutcome RevokeCdtStrictReport)
    (hInv : capabilityInvariantBundle stLocal)
    (hK : stLocal.cdtNodeSlot.invExtK)
    (hTrav : revokeCdtTransactionalTraversal stLocal rootNode descendants = .ok out) :
    capabilityInvariantBundle out.state := by
  unfold revokeCdtTransactionalTraversal at hTrav
  split at hTrav
  · simp at hTrav
  · simp only [Except.ok.injEq] at hTrav
    subst hTrav
    exact revokeCdtReportingOutcome_preserves stLocal descendants hInv hK


-- ============================================================================
-- M-P04: Streaming CDT revocation preservation (WS-M5)
-- ============================================================================

/-- M-P04/R2-F: Each node-processing step in the streaming BFS preserves the
capability invariant bundle. Direct delegation to
`processRevokeNode_preserves_capabilityInvariantBundle`. -/
theorem streamingRevokeBFS_step_preserves
    (st st' : SystemState) (node : CdtNodeId)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : processRevokeNode st node = .ok st') :
    capabilityInvariantBundle st' :=
  processRevokeNode_preserves_capabilityInvariantBundle st st' node hInv hNodeSlotK hStep

/-- M-P04/R2-F: The full streaming BFS loop preserves the capability invariant bundle.
Proof by induction on `fuel`. Each step processes one node (preserving
the invariant by `streamingRevokeBFS_step_preserves`) then recurses with
fuel-1 and the updated queue + state.

Updated in WS-R2: fuel exhaustion case (`0, _ :: _`) now returns `.error`,
so the proof obligation for that case is vacuously discharged by contradiction. -/
theorem streamingRevokeBFS_preserves
    (fuel : Nat) (queue : List CdtNodeId)
    (stInit stFinal : SystemState)
    (hInv : capabilityInvariantBundle stInit)
    (hNodeSlotK : stInit.cdtNodeSlot.invExtK)
    (hBFS : streamingRevokeBFS fuel queue stInit = .ok ((), stFinal)) :
    capabilityInvariantBundle stFinal := by
  induction fuel generalizing queue stInit stFinal with
  | zero =>
    unfold streamingRevokeBFS at hBFS
    cases queue with
    | nil => simp at hBFS; cases hBFS; exact hInv
    | cons _ _ => simp at hBFS  -- .error ≠ .ok → contradiction
  | succ n ih =>
    unfold streamingRevokeBFS at hBFS
    cases queue with
    | nil => simp at hBFS; cases hBFS; exact hInv
    | cons node rest =>
      simp only [] at hBFS
      cases hProc : processRevokeNode stInit node with
      | error e => simp [hProc] at hBFS
      | ok stNext =>
        simp [hProc] at hBFS
        have hStepInv := streamingRevokeBFS_step_preserves stInit stNext node hInv hNodeSlotK hProc
        have hKPost := processRevokeNode_preserves_cdtNodeSlot stInit stNext node hNodeSlotK hProc
        exact ih _ _ _ hStepInv hKPost hBFS

/-- The streaming traversal preserves the bundle: the BFS loop is the whole of
its state transformation. -/
theorem revokeCdtStreamingTraversal_preserves
    (stLocal : SystemState) (rootNode : CdtNodeId) (descendants : List CdtNodeId)
    (out : RevokeTraversalOutcome Unit)
    (hInv : capabilityInvariantBundle stLocal)
    (hK : stLocal.cdtNodeSlot.invExtK)
    (hTrav : revokeCdtStreamingTraversal stLocal rootNode descendants = .ok out) :
    capabilityInvariantBundle out.state := by
  unfold revokeCdtStreamingTraversal at hTrav
  split at hTrav
  · simp at hTrav
  · rename_i stDone hBfs
    simp only [Except.ok.injEq] at hTrav
    subst hTrav
    exact streamingRevokeBFS_preserves _ _ stLocal stDone hInv hK hBfs

-- ============================================================================
-- Per-entry-point preservation: the scaffold lemma at each traversal
-- ============================================================================

/-- WS-F4/F-06: `cspaceRevokeCdt` preserves `capabilityInvariantBundle`. -/
theorem cspaceRevokeCdt_preserves_capabilityInvariantBundle
    (st st' : SystemState) (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceRevokeCdt addr st = .ok ((), st')) :
    capabilityInvariantBundle st' :=
  revokeCdtScaffold_preserves_capabilityInvariantBundle () _
    (fun _ _ _ _ hI hKk hT => revokeCdtMaterializedTraversal_preserves _ _ _ _ hI hKk hT)
    st st' addr () hInv hNodeSlotK hStep

/-- M-P04: `cspaceRevokeCdtStreaming` preserves `capabilityInvariantBundle`. -/
theorem cspaceRevokeCdtStreaming_preserves_capabilityInvariantBundle
    (st st' : SystemState) (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceRevokeCdtStreaming addr st = .ok ((), st')) :
    capabilityInvariantBundle st' :=
  revokeCdtScaffold_preserves_capabilityInvariantBundle () _
    (fun _ _ _ _ hI hKk hT => revokeCdtStreamingTraversal_preserves _ _ _ _ hI hKk hT)
    st st' addr () hInv hNodeSlotK hStep

/-- WS-F4/F-06: `cspaceRevokeCdtStrict` preserves `capabilityInvariantBundle`. -/
theorem cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle
    (st st' : SystemState) (addr : CSpaceAddr) (report : RevokeCdtStrictReport)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceRevokeCdtStrict addr st = .ok (report, st')) :
    capabilityInvariantBundle st' :=
  revokeCdtScaffold_preserves_capabilityInvariantBundle _ _
    (fun _ _ _ _ hI hKk hT => revokeCdtStrictTraversal_preserves _ _ _ _ hI hKk hT)
    st st' addr report hInv hNodeSlotK hStep

/-- AK8-B: `cspaceRevokeCdtTransactional` preserves `capabilityInvariantBundle`.

The transactional variant had no preservation theorem: the strict one restated
the fold inline instead of naming it, so there was nothing for a second variant
over the same fold to reuse. Sharing the step made this one line. -/
theorem cspaceRevokeCdtTransactional_preserves_capabilityInvariantBundle
    (st st' : SystemState) (addr : CSpaceAddr) (report : RevokeCdtStrictReport)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceRevokeCdtTransactional addr st = .ok (report, st')) :
    capabilityInvariantBundle st' :=
  revokeCdtScaffold_preserves_capabilityInvariantBundle _ _
    (fun _ _ _ _ hI hKk hT => revokeCdtTransactionalTraversal_preserves _ _ _ _ hI hKk hT)
    st st' addr report hInv hNodeSlotK hStep



end SeLe4n.Kernel
