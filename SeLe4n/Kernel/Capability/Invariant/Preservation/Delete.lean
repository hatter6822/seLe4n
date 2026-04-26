-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.Insert

/-!
AN4-F.3 (CAP-M03) child module extracted from
`SeLe4n.Kernel.Capability.Invariant.Preservation`. Contains compositional
preservation theorems for capability deletion operations
(`cspaceDeleteSlotCore`, `cspaceDeleteSlot`) and the core
`cspaceRevoke` primitive that loops delete over all derived children.
Private `cdtNodeSlot` preservation helpers are promoted to public so
the Revoke sibling module can invoke them for transitive CDT-revocation
fold induction. All declarations retain their original names, order,
and proofs.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Internal

/-- Core preservation theorem for `cspaceDeleteSlotCore` (no CDT guard).
Used directly by internal callers (processRevokeNode, cspaceMove, cspaceRevokeCdtStrict)
and indirectly by the `cspaceDeleteSlot` wrapper. -/
theorem cspaceDeleteSlotCore_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hBounded, hComp, hAcyclic, hDepthPre, hObjInv⟩
  have hUnique' : cspaceSlotUnique st' := by
    intro cnodeId cn hObj
    unfold cspaceDeleteSlotCore at hStep
    cases hPre : st.objects[addr.cnode]? with
    | none => simp [hPre] at hStep
    | some preObj =>
      cases preObj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hPre] at hStep
      | cnode preCn =>
        simp [hPre] at hStep
        cases hStore : storeObject addr.cnode (.cnode (preCn.remove addr.slot)) st with
        | error e => simp [hStore] at hStep
        | ok pair =>
          obtain ⟨_, stMid⟩ := pair
          cases hRef : storeCapabilityRef addr none stMid with
          | error e => simp [hStore, hRef] at hStep
          | ok pairRef =>
            obtain ⟨_, stRef⟩ := pairRef
            simp [hStore, hRef] at hStep
            cases hStep
            have hObjRef : stRef.objects = stMid.objects :=
              storeCapabilityRef_preserves_objects stMid stRef addr none hRef
            have hObjDetach : (SystemState.detachSlotFromCdt stRef addr).objects = stRef.objects :=
              SystemState.detachSlotFromCdt_objects_eq stRef addr
            by_cases hEq : cnodeId = addr.cnode
            · rw [hEq] at hObj
              have hObjMid := storeObject_objects_eq st stMid addr.cnode
                (.cnode (preCn.remove addr.slot)) hObjInv hStore
              have : (SystemState.detachSlotFromCdt stRef addr).objects[addr.cnode]? =
                  some (.cnode (preCn.remove addr.slot)) := by
                rw [hObjDetach, hObjRef, ← hObjMid]
              rw [this] at hObj; cases hObj
              exact CNode.remove_slotsUnique preCn addr.slot (hUnique addr.cnode preCn hPre)
            · have hObjMid := storeObject_objects_ne st stMid addr.cnode cnodeId
                (.cnode (preCn.remove addr.slot)) hEq hObjInv hStore
              have : (SystemState.detachSlotFromCdt stRef addr).objects[cnodeId]? = st.objects[cnodeId]? := by
                rw [hObjDetach, hObjRef, ← hObjMid]
              rw [this] at hObj
              exact hUnique cnodeId cn hObj
  -- WS-H4: Prove new components through storeObject → storeCapabilityRef → detachSlotFromCdt
  have ⟨hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' ∧ st'.objects.invExt := by
    unfold cspaceDeleteSlotCore at hStep
    cases hPre : st.objects[addr.cnode]? with
    | none => simp [hPre] at hStep
    | some preObj =>
      cases preObj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hPre] at hStep
      | cnode preCn =>
        simp [hPre] at hStep
        cases hStore : storeObject addr.cnode (.cnode (preCn.remove addr.slot)) st with
        | error e => simp [hStore] at hStep
        | ok pair =>
          obtain ⟨_, stMid⟩ := pair
          cases hRef : storeCapabilityRef addr none stMid with
          | error e => simp [hStore, hRef] at hStep
          | ok pairRef =>
            obtain ⟨_, stRef⟩ := pairRef
            simp [hStore, hRef] at hStep; cases hStep
            have ⟨hRefCdt, hRefNS, _, hRefObj⟩ := storeCapabilityRef_cdt_eq stMid stRef addr none hRef
            have hBndMid := cspaceSlotCountBounded_of_storeObject_cnode st stMid addr.cnode
              (preCn.remove addr.slot) hBounded hObjInv hStore (CNode.remove_slotCountBounded preCn addr.slot (hBounded addr.cnode preCn hPre))
            have hCompMid := cdtCompleteness_of_storeObject st stMid addr.cnode _ hComp hObjInv hStore
              (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
            have hAcyclicMid := cdtAcyclicity_of_cdt_eq st stMid hAcyclic
              (storeObject_cdt_eq st stMid addr.cnode _ hStore)
            have hDepthMid := cspaceDepthConsistent_of_storeObject_sameCNode
              st stMid addr.cnode preCn (preCn.remove addr.slot) hDepthPre hObjInv hPre hStore rfl rfl rfl rfl
            have hObjInvMid := storeObject_preserves_objects_invExt st stMid addr.cnode _ hObjInv hStore
            have hBndRef := cspaceSlotCountBounded_of_objects_eq stMid stRef hBndMid hRefObj
            have hCompRef := cdtCompleteness_of_objects_nodeSlot_eq stMid stRef hCompMid hRefObj hRefNS
            have hAcyclicRef := cdtAcyclicity_of_cdt_eq stMid stRef hAcyclicMid hRefCdt
            have hDepthRef := cspaceDepthConsistent_of_objects_eq stMid stRef hDepthMid hRefObj
            have hObjInvRef : stRef.objects.invExt := hRefObj ▸ hObjInvMid
            have hNSMid := (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
            have hNodeSlotKRef : stRef.cdtNodeSlot.invExtK := by
              rw [hRefNS, hNSMid]; exact hNodeSlotK
            exact ⟨cspaceSlotCountBounded_of_detachSlotFromCdt stRef addr hBndRef,
              cdtCompleteness_of_detachSlotFromCdt stRef addr hCompRef hNodeSlotKRef,
              cdtAcyclicity_of_detachSlotFromCdt stRef addr hAcyclicRef,
              cspaceDepthConsistent_of_detachSlotFromCdt stRef addr hDepthRef,
              (SystemState.detachSlotFromCdt_objects_eq stRef addr) ▸ hObjInvRef⟩
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique',
    hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩

/-- WS-E2 / H-01: Compositional preservation of `cspaceDeleteSlot` (guarded wrapper).
Delegates to `cspaceDeleteSlotCore_preserves_capabilityInvariantBundle` after discharging
the U-H03 CDT children guard. -/
theorem cspaceDeleteSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceDeleteSlot at hStep
  split at hStep
  · simp at hStep
  · exact cspaceDeleteSlotCore_preserves_capabilityInvariantBundle
      st st' addr hInv hNodeSlotK hStep

/-- Core: `cspaceDeleteSlotCore` preserves `cdtNodeSlot.invExtK`. -/
theorem cspaceDeleteSlotCore_preserves_cdtNodeSlot
    (st st' : SystemState) (addr : CSpaceAddr)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    st'.cdtNodeSlot.invExtK := by
  unfold cspaceDeleteSlotCore at hStep
  cases hPre : st.objects[addr.cnode]? with
  | none => simp [hPre] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hPre] at hStep
    | cnode preCn =>
      simp [hPre] at hStep
      cases hStore : storeObject addr.cnode (.cnode (preCn.remove addr.slot)) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        obtain ⟨_, stMid⟩ := pair
        cases hRef : storeCapabilityRef addr none stMid with
        | error e => simp [hStore, hRef] at hStep
        | ok pairRef =>
          obtain ⟨_, stRef⟩ := pairRef
          simp [hStore, hRef] at hStep; cases hStep
          have hNSMid := (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
          have ⟨_, hNSRef, _, _⟩ := storeCapabilityRef_cdt_eq stMid stRef addr none hRef
          have hRefEqSt : stRef.cdtNodeSlot = st.cdtNodeSlot := by rw [hNSRef, hNSMid]
          -- detachSlotFromCdt either leaves cdtNodeSlot unchanged or erases one key
          unfold SystemState.detachSlotFromCdt
          cases hLookup : stRef.cdtSlotNode[addr]? with
          | none =>
            simp only []
            exact hRefEqSt ▸ hNodeSlotK
          | some origNode =>
            simp only []
            have hKRef : stRef.cdtNodeSlot.invExtK := by rw [hRefEqSt]; exact hNodeSlotK
            exact stRef.cdtNodeSlot.erase_preserves_invExtK origNode hKRef

/-- `cspaceDeleteSlot` preserves `cdtNodeSlot.invExtK` (guarded wrapper). -/
theorem cspaceDeleteSlot_preserves_cdtNodeSlot
    (st st' : SystemState) (addr : CSpaceAddr)
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    st'.cdtNodeSlot.invExtK := by
  unfold cspaceDeleteSlot at hStep
  split at hStep
  · simp at hStep
  · exact cspaceDeleteSlotCore_preserves_cdtNodeSlot st st' addr hNodeSlotK hStep

/-- WS-E2 / H-01: Compositional preservation of `cspaceRevoke`.
Uses pre-state `cspaceSlotUnique` + `CNode.revokeTargetLocal_slotsUnique` to derive
post-state uniqueness. -/
theorem cspaceRevoke_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hBounded, hComp, hAcyclic, hDepthPre, hObjInv⟩
  have hUnique' : cspaceSlotUnique st' := by
    intro cnodeId cn hObj
    unfold cspaceRevoke at hStep
    cases hLookup : cspaceLookupSlot addr st with
    | error e => simp [hLookup] at hStep
    | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr parent hLookup
      subst st1
      cases hPre : st.objects[addr.cnode]? with
      | none => simp [hLookup, hPre] at hStep
      | some preObj =>
        cases preObj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hLookup, hPre] at hStep
        | cnode preCn =>
          simp [hLookup, hPre] at hStep
          cases hStore : storeObject addr.cnode
            (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) st with
          | error e => simp [hStore] at hStep
          | ok pair =>
            obtain ⟨_, stMid⟩ := pair
            simp [hStore] at hStep
            -- M-P01: hStep now gives st' = revokeAndClearRefsState ...
            have hObjRef : st'.objects = stMid.objects := by
              have hFused := revokeAndClearRefsState_preserves_objects preCn addr.slot parent.target addr.cnode stMid
              simp_all
            by_cases hEq : cnodeId = addr.cnode
            · rw [hEq] at hObj
              have hObjMid := storeObject_objects_eq st stMid addr.cnode
                (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) hObjInv hStore
              have : st'.objects[addr.cnode]? =
                  some (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) := by
                rw [← hObjMid]; exact congrArg (·[addr.cnode]?) hObjRef
              rw [this] at hObj; cases hObj
              exact CNode.revokeTargetLocal_slotsUnique preCn addr.slot parent.target
                (hUnique addr.cnode preCn hPre)
            · have hObjMid := storeObject_objects_ne st stMid addr.cnode cnodeId
                (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) hEq hObjInv hStore
              have : st'.objects[cnodeId]? = st.objects[cnodeId]? := by
                rw [← hObjMid]; exact congrArg (·[cnodeId]?) hObjRef
              rw [this] at hObj
              exact hUnique cnodeId cn hObj
  -- WS-H4: storeObject(CNode.revokeTargetLocal) → revokeAndClearRefsState (M-P01)
  have ⟨hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' ∧ st'.objects.invExt := by
    unfold cspaceRevoke at hStep
    cases hLookup2 : cspaceLookupSlot addr st with
    | error e => simp [hLookup2] at hStep
    | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr parent hLookup2; subst st1
      cases hPre : st.objects[addr.cnode]? with
      | none => simp [hLookup2, hPre] at hStep
      | some preObj =>
        cases preObj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hLookup2, hPre] at hStep
        | cnode preCn =>
          simp [hLookup2, hPre] at hStep
          cases hStore : storeObject addr.cnode (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) st with
          | error e => simp [hStore] at hStep
          | ok pair =>
            obtain ⟨_, stMid⟩ := pair; simp [hStore] at hStep
            have hBndMid := cspaceSlotCountBounded_of_storeObject_cnode st stMid addr.cnode _ hBounded hObjInv hStore
              (CNode.revokeTargetLocal_slotCountBounded preCn addr.slot parent.target
                (hBounded addr.cnode preCn hPre) (hUnique addr.cnode preCn hPre))
            have hCompMid := cdtCompleteness_of_storeObject st stMid addr.cnode _ hComp hObjInv hStore
              (storeObject_cdtNodeSlot_eq st stMid addr.cnode _ hStore).1
            have hAcyclicMid := cdtAcyclicity_of_cdt_eq st stMid hAcyclic
              (storeObject_cdt_eq st stMid addr.cnode _ hStore)
            have hDepthMid := cspaceDepthConsistent_of_storeObject_sameCNode
              st stMid addr.cnode preCn (preCn.revokeTargetLocal addr.slot parent.target)
              hDepthPre hObjInv hPre hStore rfl rfl rfl rfl
            have hObjInvMid := storeObject_preserves_objects_invExt st stMid addr.cnode _ hObjInv hStore
            -- M-P01: Use revokeAndClearRefsState field preservation
            have ⟨hClearCdt, hClearNS, _, hClearObj⟩ :=
              revokeAndClearRefsState_cdt_eq preCn addr.slot parent.target addr.cnode stMid
            rw [hStep] at *
            exact ⟨cspaceSlotCountBounded_of_objects_eq stMid _ hBndMid hClearObj,
              cdtCompleteness_of_objects_nodeSlot_eq stMid _ hCompMid hClearObj hClearNS,
              cdtAcyclicity_of_cdt_eq stMid _ hAcyclicMid hClearCdt,
              cspaceDepthConsistent_of_objects_eq stMid _ hDepthMid hClearObj,
              hClearObj ▸ hObjInvMid⟩
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique',
    hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩


end SeLe4n.Kernel
