-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.PerCoreCacheModel

/-!
# The frame unmap, split into its checks and its writes

WS-ZA ZA5.4.  The unmap as seL4 splits an invocation, below the teardown that
runs it for every live page a deleted capability records: the checks are read
first (`vspaceUnmapAdmittedAt`), and an admitted unmap is its writes
(`vspaceUnmapPerformAt`), the root changed in its slot through
`storeVSpaceRootWith`.  `vspaceUnmapPageWithShootdownAndIcacheBroadcast_of_admitted`
is the equality the dispatcher's arm and the teardown's in-place unmap
(`unmapPageStateInPlace`) rest on.  The frame map, unify and page-table
operations are in `SeLe4n.Kernel.VSpacePerform`, over the same lemmas.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-ZA ZA5.4: the descriptor store a map records (`mappingStore?`), read
from the root as stored after the mapping. -/
@[inline] def mappedRootLedger (st : SystemState) (rootId : SeLe4n.ObjId)
    (vaddr : SeLe4n.VAddr) : List Architecture.PhysicalWrite :=
  match st.getVSpaceRoot? rootId with
  | some r => (Architecture.mappingStore? st r vaddr).toList
  | none => []

open SeLe4n.Kernel.RobinHood in
/-- The ASID table naming `rootId` for `asid`, and the root there carrying
`asid`, resolve `asid` to that root. -/
theorem resolveAsidRoot_of_holds {st : SystemState} {asid : SeLe4n.ASID}
    {rootId : SeLe4n.ObjId} {root : VSpaceRoot} (hH : st.asidTable.holds asid rootId = true)
    (hR : st.objects[rootId]? = some (.vspaceRoot root)) (hA : root.asid = asid) :
    Architecture.resolveAsidRoot st asid = some (rootId, root) := by
  unfold Architecture.resolveAsidRoot
  rw [RHTable_getElem?_eq_get?, RHTable.get?_of_holds _ _ _ hH]
  simp only [SystemState.getVSpaceRoot?, hR, hA, ↓reduceIte]

/-- The descriptor store reads only the page tables, so two states with the
same page tables agree on it. -/
theorem mappingStore?_congr {s t : SystemState}
    (h : ∀ id, s.getPageTable? id = t.getPageTable? id) (r : VSpaceRoot) (v : SeLe4n.VAddr) :
    Architecture.mappingStore? s r v = Architecture.mappingStore? t r v := by
  unfold Architecture.mappingStore? Architecture.tablePageAt?
  simp only [h]

open SeLe4n.Kernel.RobinHood in
/-- A root written in its slot leaves every page table where it was. -/
theorem storeVSpaceRootWith_getPageTable? {st : SystemState} {rootId : SeLe4n.ObjId}
    {root : VSpaceRoot} (hR : st.objects[rootId]? = some (.vspaceRoot root))
    (hIn : st.objects.findsInPlace rootId = true) (f : VSpaceRoot → VSpaceRoot)
    (hf : (f root).asid = root.asid) (id : SeLe4n.ObjId) :
    (st.storeVSpaceRootWith rootId f).getPageTable? id = st.getPageTable? id := by
  unfold SystemState.getPageTable?
  rw [SystemState.storeVSpaceRootWith_objects hR f hf]
  by_cases hEq : rootId = id
  · subst hEq
    rw [RHTable_getElem?_eq_get?, RHTable.get?_insert_self_of_findsInPlace _ hIn, hR]
  · rw [RHTable_getElem?_eq_get?, RHTable.get?_insert_ne_of_findsInPlace _ _ hIn hEq]
    rfl

/-- Recording physical writes touches only the ledger, so it commutes with a
root written in its slot. -/
theorem storeVSpaceRootWith_recordPhysicalWrites (st : SystemState) (ws : List Architecture.PhysicalWrite)
    (id : SeLe4n.ObjId) (f : VSpaceRoot → VSpaceRoot) :
    (Architecture.recordPhysicalWrites st ws).storeVSpaceRootWith id f =
      Architecture.recordPhysicalWrites (st.storeVSpaceRootWith id f) ws := by
  have hO : (Architecture.recordPhysicalWrites st ws).objects = st.objects := rfl
  have hL : ∀ r, (Architecture.recordPhysicalWrites st ws).storeLeavesRootTables id r =
      st.storeLeavesRootTables id r := fun _ => rfl
  unfold SystemState.storeVSpaceRootWith
  rw [hO]
  split
  · next r _ =>
    rw [hL r]
    by_cases hc : st.storeLeavesRootTables id r = true
    · simp only [hc, ↓reduceIte]; rfl
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]; rfl
  · rfl

-- ============================================================================
-- The frame unmap
-- ============================================================================

/-- WS-ZA ZA5.4: the root an unmap leaves (`VSpaceRoot.unmapPage`'s erase). -/
@[inline] def rootWithoutMapping (vaddr : SeLe4n.VAddr) (r : VSpaceRoot) : VSpaceRoot :=
  { r with mappings := r.mappings.erase vaddr, mappingEpochs := r.mappingEpochs.erase vaddr }

open SeLe4n.Kernel.RobinHood in
/-- WS-ZA ZA5.4: the epoch entry of `vaddr` erased from a root as compiled:
its slot found as a bare index, and the cell erased from it becomes the root's
spare epoch cell (`VSpaceRoot.epochSpare`), which the next map's epoch writes
over (`rootWithEpochCells`). -/
@[inline] def rootWithoutEpochCells (vaddr : SeLe4n.VAddr) (r : VSpaceRoot) : VSpaceRoot :=
  let t := r.mappingEpochs
  let i := findIdxLoop t.capacity (idealIndex vaddr t.capacity t.hCapPos) vaddr 0 t.slots
    t.capacity t.hSlotsLen t.hCapPos
  if h : i < t.capacity then
    let old := t.slots[i]'(by rw [t.hSlotsLen]; exact h)
    { r with mappingEpochs := t.eraseAt i h, epochSpare := Squash.mk old }
  else r

open SeLe4n.Kernel.RobinHood in
/-- WS-ZA ZA5.4: `rootWithoutMapping` as compiled: the mapping's slot is found
as a bare index, and the cell erased from it (its `some`, its entry and its
value pair) becomes the root's spare (`VSpaceRoot.mappingSpare`), which the
next map writes over, so no slot `Option` is built and the cell is not freed;
the epoch entry goes the same way (`rootWithoutEpochCells`). -/
@[inline] def rootWithoutMappingCells (vaddr : SeLe4n.VAddr) (r : VSpaceRoot) : VSpaceRoot :=
  let t := r.mappings
  let i := findIdxLoop t.capacity (idealIndex vaddr t.capacity t.hCapPos) vaddr 0 t.slots
    t.capacity t.hSlotsLen t.hCapPos
  if h : i < t.capacity then
    let old := t.slots[i]'(by rw [t.hSlotsLen]; exact h)
    rootWithoutEpochCells vaddr { r with mappings := t.eraseAt i h, mappingSpare := Squash.mk old }
  else rootWithoutEpochCells vaddr r

open SeLe4n.Kernel.RobinHood in
theorem rootWithoutEpochCells_eq (vaddr : SeLe4n.VAddr) (r : VSpaceRoot) :
    rootWithoutEpochCells vaddr r = { r with mappingEpochs := r.mappingEpochs.erase vaddr } := by
  unfold rootWithoutEpochCells
  rw [RHTable.erase_eq_eraseAt]
  dsimp only
  split
  · cases r
    simp only [VSpaceRoot.mk.injEq, and_true, true_and]
    exact Subsingleton.elim _ _
  · rfl

open SeLe4n.Kernel.RobinHood in
@[csimp] theorem rootWithoutMapping_eq_cells :
    @rootWithoutMapping = @rootWithoutMappingCells := by
  funext vaddr r
  unfold rootWithoutMapping rootWithoutMappingCells
  rw [RHTable.erase_eq_eraseAt]
  dsimp only
  split
  · rw [rootWithoutEpochCells_eq]
    cases r
    simp only [VSpaceRoot.mk.injEq, and_true, true_and]
    exact Subsingleton.elim _ _
  · rw [rootWithoutEpochCells_eq]

/-- WS-ZA ZA5.4: **an admitted unmap's writes**: the mapping erased in the
root's slot, its invalid descriptor on the ledger, the executing core's flush,
the shootdown round, the initiator's drain, and — for an executable mapping —
the instruction-cache broadcast, whose operand is read before the write
(`vspaceUnmapPageWithShootdownAndIcacheBroadcast`). -/
def vspaceUnmapPerformAt (ec : Concurrency.CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (rootId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  let op? := Architecture.unmapIcacheOperand st asid vaddr
  let st1 := st.storeVSpaceRootWith rootId (rootWithoutMapping vaddr)
  let st1 := Architecture.recordPhysicalWrites st1 (mappedRootLedger st1 rootId vaddr)
  let st2 := { st1 with tlb := adapterFlushTlbByVAddr st1.tlb asid vaddr }
  let st3 := Architecture.tlbShootdownBroadcastCoalescing st2 ec
    (Architecture.shootdownTargets ec) (Architecture.encodePageInvalidation asid vaddr)
  let st4 := Architecture.drainInitiatorPageOnCore st3 ec asid vaddr
  match op? with
  | none => st4
  | some op =>
    Architecture.recordIcacheMaintenance
      (Architecture.icInvalidateBroadcast st4 Architecture.icBroadcastReach op) op

/-- WS-ZA ZA5.4: **the unmap's checks**, read before any write: the root the
invoked capability names carries `asid` and maps `vaddr` (`.translationFault`
otherwise), and the in-place conditions of the map (`vspaceMapAdmittedAt`). -/
def vspaceUnmapAdmittedAt (st : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (rootId : SeLe4n.ObjId) : Bool :=
  (match st.getVSpaceRoot? rootId with
   | some root => root.asid == asid && (root.mappings[vaddr]?).isSome
   | none => false) &&
  st.asidTable.holds asid rootId &&
  st.objects.findsInPlace rootId

open SeLe4n.Kernel.RobinHood in
/-- **WS-ZA ZA5.4: an admitted unmap is its writes.** -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_of_admitted (ec : Concurrency.CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (rootId : SeLe4n.ObjId) (st : SystemState)
    (hA : vspaceUnmapAdmittedAt st asid vaddr rootId = true) :
    Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st =
      .ok ((), vspaceUnmapPerformAt ec asid vaddr rootId st) := by
  unfold vspaceUnmapAdmittedAt at hA
  cases hGR : st.getVSpaceRoot? rootId with
  | none => simp [hGR] at hA
  | some root =>
  have hR : st.objects[rootId]? = some (.vspaceRoot root) :=
    (SystemState.getVSpaceRoot?_eq_some_iff st rootId root).1 hGR
  simp only [hGR, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hA
  obtain ⟨⟨⟨hAs, e, hE⟩, hH⟩, hIn⟩ := hA
  have hRes := resolveAsidRoot_of_holds hH hR hAs
  let f := rootWithoutMapping vaddr
  have hf : (f root).asid = root.asid := rfl
  let st1 := st.storeVSpaceRootWith rootId f
  have hObj1 : st1.objects[rootId]? = some (.vspaceRoot (f root)) := by
    show (st.storeVSpaceRootWith rootId f).objects[rootId]? = _
    rw [SystemState.storeVSpaceRootWith_objects hR f hf, RHTable_getElem?_eq_get?,
      RHTable.get?_insert_self_of_findsInPlace _ hIn]
  have hLedger : mappedRootLedger st1 rootId vaddr =
      (Architecture.mappingStore? st (f root) vaddr).toList := by
    unfold mappedRootLedger
    rw [show st1.getVSpaceRoot? rootId = some (f root) by
      simp only [SystemState.getVSpaceRoot?, hObj1]]
    dsimp only
    rw [mappingStore?_congr (storeVSpaceRootWith_getPageTable? hR hIn f hf)]
  have hStore : storeObject rootId (.vspaceRoot (f root))
      (Architecture.recordPhysicalWrites st (Architecture.mappingStore? st (f root) vaddr).toList)
      = .ok ((), Architecture.recordPhysicalWrites st1 (mappedRootLedger st1 rootId vaddr)) := by
    rw [hLedger, ← storeVSpaceRootWith_recordPhysicalWrites]
    exact SystemState.storeObject_vspaceRoot_eq_storeVSpaceRootWith
      (st := Architecture.recordPhysicalWrites st _) hR f hf
  have hUn : root.unmapPage vaddr = some (f root) := by
    unfold VSpaceRoot.unmapPage
    rw [hE]
    rfl
  unfold Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast Architecture.withIcacheBroadcast
    Architecture.vspaceUnmapPageWithShootdownPerCore Architecture.vspaceUnmapPageWithShootdown
    Architecture.vspaceUnmapPageWithFlush Architecture.vspaceUnmapPage
  rw [hRes]
  dsimp only
  rw [hUn]
  dsimp only
  rw [hStore]
  unfold vspaceUnmapPerformAt
  dsimp only [Architecture.withShootdownRound]
  cases Architecture.unmapIcacheOperand st asid vaddr <;> rfl

end SeLe4n.Kernel
