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
  rcases hInv with ⟨hU, _, hBnd, hComp, _, hDepthPre, hObjInvPre⟩
  have hObjEq : ({ st with cdt := cdt' } : SystemState).objects = st.objects := rfl
  exact ⟨cspaceSlotUnique_of_objects_eq st _ hU hObjEq,
    cspaceLookupSound_of_cspaceSlotUnique _ (cspaceSlotUnique_of_objects_eq st _ hU hObjEq),
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
      (CapDerivationTree.edgeWellFounded_sub _ _ hInv.2.2.2.2.1 (CapDerivationTree.removeNode_edges_sub st.cdt node))
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
        (CapDerivationTree.edgeWellFounded_sub _ _ hDelInv.2.2.2.2.1
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

/-- WS-F4/F-06: cspaceRevokeCdt preserves capabilityInvariantBundle.
Composes cspaceRevoke (proven) + fold over CDT descendants. -/
theorem cspaceRevokeCdt_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceRevokeCdt addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceRevokeCdt at hStep
  split at hStep
  · simp at hStep
  · rename_i stLocal hRevoke
    have hLocalInv := cspaceRevoke_preserves_capabilityInvariantBundle st stLocal addr hInv hRevoke
    -- cspaceRevoke preserves cdtNodeSlot (storeObject + revokeAndClearRefsState both preserve it)
    have hLocalNS : stLocal.cdtNodeSlot = st.cdtNodeSlot := by
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
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hRevoke
          | cnode preCn =>
            simp [hObj] at hRevoke
            cases hStore : storeObject addr.cnode
                (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) st with
            | error e => simp [hStore] at hRevoke
            | ok pair =>
              obtain ⟨_, stMid⟩ := pair; simp [hStore] at hRevoke; rw [← hRevoke]
              have hNSMid := (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
              have ⟨_, hNSClear, _, _⟩ := revokeAndClearRefsState_cdt_eq preCn addr.slot parent.target addr.cnode stMid
              rw [hNSClear, hNSMid]
    have hLocalK : stLocal.cdtNodeSlot.invExtK := hLocalNS ▸ hNodeSlotK
    split at hStep
    · simp at hStep; cases hStep; exact hLocalInv
    · rename_i rootNode hLookup
      -- hStep has the fold result; the inline lambda is definitionally equal to revokeCdtFoldBody
      change (stLocal.cdt.descendantsOf rootNode).foldl revokeCdtFoldBody
          (.ok ((), stLocal)) = .ok ((), st') at hStep
      exact revokeCdtFold_preserves _ stLocal st' hLocalInv hLocalK hStep

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

/-- WS-F4/F-06: cspaceRevokeCdtStrict preserves capabilityInvariantBundle.
The strict variant composes cspaceRevoke + a fold that only does cspaceDeleteSlot
and CDT operations, same as the non-strict variant. -/
theorem cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (report : RevokeCdtStrictReport)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceRevokeCdtStrict addr st = .ok (report, st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceRevokeCdtStrict at hStep
  split at hStep
  · simp at hStep
  · rename_i stLocal hRevoke
    have hLocalInv := cspaceRevoke_preserves_capabilityInvariantBundle st stLocal addr hInv hRevoke
    -- cspaceRevoke preserves cdtNodeSlot
    have hLocalNS : stLocal.cdtNodeSlot = st.cdtNodeSlot := by
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
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hRevoke
          | cnode preCn =>
            simp [hObj] at hRevoke
            cases hStore : storeObject addr.cnode
                (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) st with
            | error e => simp [hStore] at hRevoke
            | ok pair =>
              obtain ⟨_, stMid⟩ := pair; simp [hStore] at hRevoke; rw [← hRevoke]
              have hNSMid := (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
              have ⟨_, hNSClear, _, _⟩ := revokeAndClearRefsState_cdt_eq preCn addr.slot parent.target addr.cnode stMid
              rw [hNSClear, hNSMid]
    have hLocalK : stLocal.cdtNodeSlot.invExtK := hLocalNS ▸ hNodeSlotK
    split at hStep
    · -- No CDT root: stLocal is the final state
      simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact hLocalInv
    · -- CDT root found: fold processes descendants
      rename_i rootNode _hLookup
      suffices h : ∀ (nodes : List CdtNodeId) (rep : RevokeCdtStrictReport) (stAcc : SystemState),
          capabilityInvariantBundle stAcc →
          stAcc.cdtNodeSlot.invExtK →
          capabilityInvariantBundle (nodes.foldl (fun acc node =>
            let (report, stCur) := acc
            match report.firstFailure with
            | some _ => (report, stCur)
            | none =>
                match SystemState.lookupCdtSlotOfNode stCur node with
                | none => (report, { stCur with cdt := stCur.cdt.removeNode node })
                | some descAddr =>
                    match cspaceDeleteSlotCore descAddr stCur with
                    | .error err =>
                        -- AH3-A (L-04): Preserve CDT node on slot deletion failure
                        ({ report with firstFailure := some {
                            offendingNode := node, offendingSlot := some descAddr, error := err } },
                         stCur)
                    | .ok ((), stDel) =>
                        -- V5-N: Redundant detachSlotFromCdt removed (done inside cspaceDeleteSlotCore)
                        ({ report with deletedSlots := descAddr :: report.deletedSlots },
                         { stDel with cdt := stDel.cdt.removeNode node })
          ) (rep, stAcc)).2 by
        simp at hStep
        have hInvFold := h (stLocal.cdt.descendantsOf rootNode)
          { deletedSlots := [], firstFailure := none } stLocal hLocalInv hLocalK
        obtain ⟨_, hStEq⟩ := hStep
        rw [← hStEq]; exact hInvFold
      intro nodes
      induction nodes with
      | nil => intro rep stAcc hI _; simpa [List.foldl] using hI
      | cons node rest ih =>
        intro rep stAcc hI hKAcc
        simp only [List.foldl]
        cases rep.firstFailure with
        | some _ => exact ih rep stAcc hI hKAcc
        | none =>
          cases hSlot : SystemState.lookupCdtSlotOfNode stAcc node with
          | none =>
            simp
            exact ih rep { stAcc with cdt := stAcc.cdt.removeNode node }
              (capabilityInvariantBundle_of_cdt_update stAcc _ hI
                (CapDerivationTree.edgeWellFounded_sub _ _ hI.2.2.2.2.1 (CapDerivationTree.removeNode_edges_sub stAcc.cdt node)))
              hKAcc
          | some descAddr =>
            simp
            cases hDel : cspaceDeleteSlotCore descAddr stAcc with
            | error err =>
              -- AH3-A (L-04): Error branch preserves state unchanged (no removeNode)
              simp
              exact ih _ stAcc hI hKAcc
            | ok pair =>
              obtain ⟨_, stDel⟩ := pair
              simp
              -- V5-N: After removing redundant detachSlotFromCdt, the proof goes
              -- directly from stDel to removeNode (detach is already inside cspaceDeleteSlotCore).
              have hDelInv := cspaceDeleteSlotCore_preserves_capabilityInvariantBundle stAcc stDel
                descAddr hI hKAcc hDel
              have hKDel := cspaceDeleteSlotCore_preserves_cdtNodeSlot stAcc stDel
                descAddr hKAcc hDel
              exact ih _ _ (capabilityInvariantBundle_of_cdt_update _ _ hDelInv
                (CapDerivationTree.edgeWellFounded_sub _ _ hDelInv.2.2.2.2.1
                  (CapDerivationTree.removeNode_edges_sub stDel.cdt node)))
                hKDel

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

/-- M-P04: `cspaceRevokeCdtStreaming` preserves the capability invariant bundle.
Composes `cspaceRevoke_preserves_capabilityInvariantBundle` with
`streamingRevokeBFS_preserves`. -/
theorem cspaceRevokeCdtStreaming_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceRevokeCdtStreaming addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceRevokeCdtStreaming at hStep
  split at hStep
  · simp at hStep
  · rename_i stLocal hRevoke
    have hLocalInv := cspaceRevoke_preserves_capabilityInvariantBundle st stLocal addr hInv hRevoke
    -- cspaceRevoke preserves cdtNodeSlot (same derivation as in cspaceRevokeCdt)
    have hLocalNS : stLocal.cdtNodeSlot = st.cdtNodeSlot := by
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
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hRevoke
          | cnode preCn =>
            simp [hObj] at hRevoke
            cases hStore : storeObject addr.cnode
                (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) st with
            | error e => simp [hStore] at hRevoke
            | ok pair =>
              obtain ⟨_, stMid⟩ := pair; simp [hStore] at hRevoke; rw [← hRevoke]
              have hNSMid := (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
              have ⟨_, hNSClear, _, _⟩ := revokeAndClearRefsState_cdt_eq preCn addr.slot parent.target addr.cnode stMid
              rw [hNSClear, hNSMid]
    split at hStep
    · simp at hStep; cases hStep; exact hLocalInv
    · rename_i rootNode hLookup
      exact streamingRevokeBFS_preserves _ _ stLocal st' hLocalInv
        (hLocalNS ▸ hNodeSlotK) hStep


end SeLe4n.Kernel
