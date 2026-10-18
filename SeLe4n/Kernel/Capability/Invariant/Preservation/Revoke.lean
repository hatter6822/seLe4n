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
and `cspaceRevokeCdtStreaming`.  The `capabilityInvariantBundle_of_cdt_update`
helper they use lives in the Delete sibling, whose splice uses it first.
Private fold infrastructure is promoted to public so the hub and
future cross-subsystem consumers can reason about the fold shape.
All declarations retain their original names, order, and proofs.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Internal

-- ============================================================================
-- WS-F4/F-06: cspaceRevokeCdt and cspaceRevokeCdtStrict preservation
-- ============================================================================

/-- Removing one node from the tree keeps the bundle: the store is untouched and
the tree only loses edges. -/
theorem capabilityInvariantBundle_of_removeNode (st : SystemState) (node : SlotRef)
    (hInv : capabilityInvariantBundle st) :
    capabilityInvariantBundle { st with cdt := st.cdt.removeNode node } :=
  capabilityInvariantBundle_of_cdt_update st _ hInv
    (CapDerivationTree.edgeWellFounded_sub _ _ hInv.2.2.2.1
      (CapDerivationTree.removeNode_edges_sub st.cdt node))
    (fun ref h => CapDerivationTree.removeNode_mentions st.cdt node ref h)

/-- R2-A/R2-F: `processRevokeNode` preserves the full capability invariant bundle
when it succeeds: the slot's delete keeps it (`cspaceDeleteSlotCore`), and
removing the slot's node from the tree keeps it.

The error case (`cspaceDeleteSlotCore` fails) returns `.error` and produces no
post-state.

This is the single proof obligation for per-node revocation, shared by both the
materialized fold (`cspaceRevokeCdt`) and streaming BFS (`streamingRevokeBFS`). -/
theorem processRevokeNode_preserves_capabilityInvariantBundle
    (st st' : SystemState) (node : SlotRef)
    (hInv : capabilityInvariantBundle st)
    (hStep : processRevokeNode st node = .ok st') :
    capabilityInvariantBundle st' := by
  unfold processRevokeNode at hStep
  cases hDel : cspaceDeleteSlotCore node st with
  | error _ => simp [hDel] at hStep
  | ok pair =>
    obtain ⟨_, stDel⟩ := pair
    simp [hDel] at hStep; cases hStep
    exact capabilityInvariantBundle_of_removeNode stDel node
      (cspaceDeleteSlotCore_preserves_capabilityInvariantBundle st stDel node hInv hDel)

-- **Tombstone (`v0.35.190`).**  `revokeCdtFoldBody`, `revokeCdtFoldBody_error`
-- and `revokeCdtFoldBody_foldl_error` moved to `Capability/Operations.lean`,
-- beside `revokeCdtMaterializedTraversal`, which is now *defined* through the
-- body rather than inlining it.  The predicate-generic induction is
-- `revokeCdtFold_induct` / `revokeCdtMaterializedTraversal_ok_induct`, also
-- there, so the capability bundle's argument and the IPC bundle's are one
-- induction.

/-- Single fold step preserves capabilityInvariantBundle.
Delegates to `processRevokeNode_preserves_capabilityInvariantBundle`. -/
theorem revokeCdtFoldBody_preserves
    (psAcc psNext : List MappedPage) (stAcc stNext : SystemState) (node : SlotRef)
    (hInv : capabilityInvariantBundle stAcc)
    (hStep : revokeCdtFoldBody (.ok (psAcc, stAcc)) node = .ok (psNext, stNext)) :
    capabilityInvariantBundle stNext := by
  unfold revokeCdtFoldBody at hStep
  simp only [] at hStep
  cases hProc : processRevokeNode stAcc node with
  | error e => simp [hProc] at hStep
  | ok stMid =>
    simp [hProc] at hStep; obtain ⟨-, rfl⟩ := hStep
    exact processRevokeNode_preserves_capabilityInvariantBundle stAcc stMid node hInv hProc

/-- Fold induction: the `cspaceRevokeCdt` fold preserves `capabilityInvariantBundle`
(an instance of the shared `revokeCdtFold_induct`). -/
theorem revokeCdtFold_preserves
    (nodes : List SlotRef) (psInit psFinal : List MappedPage)
    (stInit stFinal : SystemState)
    (hInv : capabilityInvariantBundle stInit)
    (hFold : nodes.foldl revokeCdtFoldBody (.ok (psInit, stInit)) = .ok (psFinal, stFinal)) :
    capabilityInvariantBundle stFinal :=
  revokeCdtFold_induct (P := capabilityInvariantBundle)
    (fun stA stB node hP hStep =>
      processRevokeNode_preserves_capabilityInvariantBundle stA stB node hP hStep)
    nodes psInit psFinal stInit stFinal hInv hFold

/-- **The scaffold preserves the bundle whenever its traversal does.**

The revocation entry points share a preservation *argument* as well as a
transition: a read of the source slot, then a walk.  Proved once here, a
variant's obligation is exactly its traversal's — which is the only part that
differs.  The first step writes nothing, so the walk starts from the pre-state.

`hTraverse` is stated over an arbitrary traversal, so this covers the four
variants that exist and any that do not exist yet. -/
theorem revokeCdtScaffold_preserves_capabilityInvariantBundle {ρ : Type}
    (traverse : SystemState → SlotRef → List SlotRef →
      Except KernelError (RevokeTraversalOutcome ρ))
    (hTraverse : ∀ (stLocal : SystemState) (rootNode : SlotRef)
        (descendants : List SlotRef) (out : RevokeTraversalOutcome ρ),
        capabilityInvariantBundle stLocal →
        traverse stLocal rootNode descendants = .ok out →
        capabilityInvariantBundle out.state)
    (st st' : SystemState) (addr : CSpaceAddr) (r : ρ)
    (hInv : capabilityInvariantBundle st)
    (hStep : revokeCdtScaffold traverse addr st = .ok (r, st')) :
    capabilityInvariantBundle st' := by
  -- `v0.35.190`: the case analysis is `revokeCdtScaffold_ok_decompose`'s, beside
  -- the definition, so this proof and the IPC bundle's read one answer.
  obtain ⟨_, out, hTrav, rfl⟩ :=
    revokeCdtScaffold_ok_decompose traverse st st' addr r hStep
  exact hTraverse st addr _ out hInv hTrav

/-- The materialized traversal preserves the bundle: it is `revokeCdtFoldBody`
under a different spelling. -/
theorem revokeCdtMaterializedTraversal_preserves
    (stLocal : SystemState) (rootNode : SlotRef) (descendants : List SlotRef)
    (out : RevokeTraversalOutcome (List MappedPage))
    (hInv : capabilityInvariantBundle stLocal)
    (hTrav : revokeCdtMaterializedTraversal stLocal rootNode descendants = .ok out) :
    capabilityInvariantBundle out.state :=
  revokeCdtMaterializedTraversal_ok_induct (P := capabilityInvariantBundle)
    (fun stA stB node hP hStep =>
      processRevokeNode_preserves_capabilityInvariantBundle stA stB node hP hStep)
    stLocal rootNode descendants out hInv hTrav

/-- R2-F: Error propagation consistency theorem. When `cspaceDeleteSlotCore` fails
for a CDT descendant, `processRevokeNode` (and therefore `revokeCdtFoldBody`)
propagates the error: the fold body returns the same error that
`cspaceDeleteSlotCore` produced. -/
theorem cspaceRevokeCdt_error_propagation_consistent
    (psAcc : List MappedPage) (stAcc : SystemState) (node : SlotRef)
    (err : KernelError)
    (hDelErr : cspaceDeleteSlotCore node stAcc = .error err) :
    revokeCdtFoldBody (.ok (psAcc, stAcc)) node = .error err := by
  unfold revokeCdtFoldBody
  simp only []
  unfold processRevokeNode
  simp [hDelErr]

/-- R2-F/M-05: Fuel exhaustion preservation theorem. When `streamingRevokeBFS`
returns `.error .resourceExhausted`, the input state is unchanged — the error
is returned before any state modification occurs in the exhaustion case. -/
theorem streamingRevokeBFS_fuel_exhaustion_returns_error
    (queue : List SlotRef) (st : SystemState) (node : SlotRef)
    (rest : List SlotRef)
    (hQueue : queue = node :: rest) :
    streamingRevokeBFS 0 queue st = .error .resourceExhausted := by
  subst hQueue; unfold streamingRevokeBFS; rfl

/-- **The shared reporting step preserves the bundle.**

`cspaceRevokeCdtStrict` and `cspaceRevokeCdtTransactional` fold the same step, so
this is proved once rather than restated inline in each variant's theorem.

On a deletion failure the state is returned unchanged, so that branch is
immediate. -/
theorem revokeCdtReportingStep_preserves
    (acc : RevokeCdtStrictReport × SystemState) (node : SlotRef)
    (hInv : capabilityInvariantBundle acc.2) :
    capabilityInvariantBundle (revokeCdtReportingStep acc node).2 := by
  obtain ⟨report, stAcc⟩ := acc
  unfold revokeCdtReportingStep
  simp only []
  cases report.firstFailure with
  | some _ => exact hInv
  | none =>
    simp only []
    cases hDel : cspaceDeleteSlotCore node stAcc with
    | error err => simp only []; exact hInv
    | ok pair =>
      obtain ⟨_, stDel⟩ := pair
      simp only []
      exact capabilityInvariantBundle_of_removeNode stDel node
        (cspaceDeleteSlotCore_preserves_capabilityInvariantBundle stAcc stDel node hInv hDel)

/-- The reporting fold preserves the bundle, by induction on the node list. -/
theorem revokeCdtReportingFold_preserves :
    ∀ (nodes : List SlotRef) (acc : RevokeCdtStrictReport × SystemState),
      capabilityInvariantBundle acc.2 →
      capabilityInvariantBundle (nodes.foldl revokeCdtReportingStep acc).2 := by
  intro nodes
  induction nodes with
  | nil => intro acc hI; exact hI
  | cons node rest ih =>
    intro acc hI
    simp only [List.foldl_cons]
    exact ih _ (revokeCdtReportingStep_preserves acc node hI)

/-- The reporting outcome's state is the fold's state, so it inherits the fold's
preservation. Shared by both reporting traversals. -/
theorem revokeCdtReportingOutcome_preserves
    (stLocal : SystemState) (descendants : List SlotRef)
    (hInv : capabilityInvariantBundle stLocal) :
    capabilityInvariantBundle (revokeCdtReportingOutcome stLocal descendants).state := by
  unfold revokeCdtReportingOutcome
  split
  · rename_i report stFinal hFold
    have hFoldInv := revokeCdtReportingFold_preserves descendants
      ({ deletedSlots := [], firstFailure := none }, stLocal) hInv
    rw [hFold] at hFoldInv
    exact hFoldInv

/-- The best-effort reporting traversal preserves the bundle. -/
theorem revokeCdtStrictTraversal_preserves
    (stLocal : SystemState) (rootNode : SlotRef) (descendants : List SlotRef)
    (out : RevokeTraversalOutcome RevokeCdtStrictReport)
    (hInv : capabilityInvariantBundle stLocal)
    (hTrav : revokeCdtStrictTraversal stLocal rootNode descendants = .ok out) :
    capabilityInvariantBundle out.state := by
  unfold revokeCdtStrictTraversal at hTrav
  simp only [Except.ok.injEq] at hTrav
  subst hTrav
  exact revokeCdtReportingOutcome_preserves stLocal descendants hInv

/-- The validated reporting traversal preserves the bundle: validation only
inspects state, so a successful validation hands the same state to the same
fold. -/
theorem revokeCdtTransactionalTraversal_preserves
    (stLocal : SystemState) (rootNode : SlotRef) (descendants : List SlotRef)
    (out : RevokeTraversalOutcome RevokeCdtStrictReport)
    (hInv : capabilityInvariantBundle stLocal)
    (hTrav : revokeCdtTransactionalTraversal stLocal rootNode descendants = .ok out) :
    capabilityInvariantBundle out.state := by
  unfold revokeCdtTransactionalTraversal at hTrav
  split at hTrav
  · simp at hTrav
  · simp only [Except.ok.injEq] at hTrav
    subst hTrav
    exact revokeCdtReportingOutcome_preserves stLocal descendants hInv


-- ============================================================================
-- M-P04: Streaming CDT revocation preservation (WS-M5)
-- ============================================================================

/-- M-P04/R2-F: The full streaming BFS loop preserves the capability invariant bundle.
Proof by induction on `fuel`. Each step processes one node (preserving
the invariant by `processRevokeNode_preserves_capabilityInvariantBundle`) then
recurses with fuel-1 and the updated queue + state.

Fuel exhaustion (`0, _ :: _`) returns `.error`, so that case is vacuous. -/
theorem streamingRevokeBFS_preserves
    (fuel : Nat) (queue : List SlotRef)
    (stInit stFinal : SystemState)
    (hInv : capabilityInvariantBundle stInit)
    (hBFS : streamingRevokeBFS fuel queue stInit = .ok ((), stFinal)) :
    capabilityInvariantBundle stFinal := by
  induction fuel generalizing queue stInit stFinal with
  | zero =>
    unfold streamingRevokeBFS at hBFS
    cases queue with
    | nil => simp at hBFS; cases hBFS; exact hInv
    | cons _ _ => simp at hBFS
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
        exact ih _ _ _
          (processRevokeNode_preserves_capabilityInvariantBundle stInit stNext node hInv hProc) hBFS

/-- The streaming traversal preserves the bundle: the BFS loop is the whole of
its state transformation. -/
theorem revokeCdtStreamingTraversal_preserves
    (stLocal : SystemState) (rootNode : SlotRef) (descendants : List SlotRef)
    (out : RevokeTraversalOutcome Unit)
    (hInv : capabilityInvariantBundle stLocal)
    (hTrav : revokeCdtStreamingTraversal stLocal rootNode descendants = .ok out) :
    capabilityInvariantBundle out.state := by
  unfold revokeCdtStreamingTraversal at hTrav
  split at hTrav
  · simp at hTrav
  · rename_i stDone hBfs
    simp only [Except.ok.injEq] at hTrav
    subst hTrav
    exact streamingRevokeBFS_preserves _ _ stLocal stDone hInv hBfs

-- ============================================================================
-- Per-entry-point preservation: the scaffold lemma at each traversal
-- ============================================================================

/-- WS-F4/F-06: `cspaceRevokeCdt` preserves `capabilityInvariantBundle`. -/
theorem cspaceRevokeCdt_preserves_capabilityInvariantBundle
    (st st' : SystemState) (addr : CSpaceAddr) (pages : List MappedPage)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevokeCdt addr st = .ok (pages, st')) :
    capabilityInvariantBundle st' :=
  revokeCdtScaffold_preserves_capabilityInvariantBundle _
    (fun _ _ _ _ hI hT => revokeCdtMaterializedTraversal_preserves _ _ _ _ hI hT)
    st st' addr pages hInv hStep

/-- M-P04: `cspaceRevokeCdtStreaming` preserves `capabilityInvariantBundle`. -/
theorem cspaceRevokeCdtStreaming_preserves_capabilityInvariantBundle
    (st st' : SystemState) (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevokeCdtStreaming addr st = .ok ((), st')) :
    capabilityInvariantBundle st' :=
  revokeCdtScaffold_preserves_capabilityInvariantBundle _
    (fun _ _ _ _ hI hT => revokeCdtStreamingTraversal_preserves _ _ _ _ hI hT)
    st st' addr () hInv hStep

/-- WS-F4/F-06: `cspaceRevokeCdtStrict` preserves `capabilityInvariantBundle`. -/
theorem cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle
    (st st' : SystemState) (addr : CSpaceAddr) (report : RevokeCdtStrictReport)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevokeCdtStrict addr st = .ok (report, st')) :
    capabilityInvariantBundle st' :=
  revokeCdtScaffold_preserves_capabilityInvariantBundle _
    (fun _ _ _ _ hI hT => revokeCdtStrictTraversal_preserves _ _ _ _ hI hT)
    st st' addr report hInv hStep

/-- AK8-B: `cspaceRevokeCdtTransactional` preserves `capabilityInvariantBundle`. -/
theorem cspaceRevokeCdtTransactional_preserves_capabilityInvariantBundle
    (st st' : SystemState) (addr : CSpaceAddr) (report : RevokeCdtStrictReport)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevokeCdtTransactional addr st = .ok (report, st')) :
    capabilityInvariantBundle st' :=
  revokeCdtScaffold_preserves_capabilityInvariantBundle _
    (fun _ _ _ _ hI hT => revokeCdtTransactionalTraversal_preserves _ _ _ _ hI hT)
    st st' addr report hInv hStep

end SeLe4n.Kernel
