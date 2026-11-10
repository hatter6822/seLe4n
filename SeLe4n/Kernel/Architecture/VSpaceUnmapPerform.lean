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
its slot found as a bare index, and the cell erased from it is handed back to
the root's spare epoch cells (`VSpaceRoot.epochSpare`), which the next map's
epoch writes over (`rootWithEpochCells`). -/
@[inline] def rootWithoutEpochCells (vaddr : SeLe4n.VAddr) (r : VSpaceRoot) : VSpaceRoot :=
  let t := r.mappingEpochs
  let i := findIdxLoop t.capacity (idealIndex vaddr t.capacity t.hCapPos) vaddr 0 t.slots
    t.capacity t.hSlotsLen t.hCapPos
  if h : i < t.capacity then
    let old := t.slots[i]'(by rw [t.hSlotsLen]; exact h)
    let sp := r.epochSpare
    let r0 := { r with mappingEpochs := t.eraseAt i h, epochSpare := Squash.mk #[] }
    Quot.lift (fun a => { r0 with epochSpare := Squash.mk (a.push old) })
      (fun _ _ _ => by simp only [VSpaceRoot.with_epochSpare]) sp
  else r

open SeLe4n.Kernel.RobinHood in
/-- WS-ZA ZA5.4: `rootWithoutMapping` as compiled: the mapping's slot is found
as a bare index, and the cell erased from it (its `some`, its entry and its
value pair) is handed back to the root's spares (`VSpaceRoot.mappingSpare`),
which the next map writes over, so no slot `Option` is built and the cell is not freed;
the epoch entry goes the same way (`rootWithoutEpochCells`).  Out of line:
inlined into the object update, the root would be checked for sole ownership
while its object still held it, and so be rebuilt. -/
@[noinline] def rootWithoutMappingCells (vaddr : SeLe4n.VAddr) (r : VSpaceRoot) : VSpaceRoot :=
  let t := r.mappings
  let i := findIdxLoop t.capacity (idealIndex vaddr t.capacity t.hCapPos) vaddr 0 t.slots
    t.capacity t.hSlotsLen t.hCapPos
  if h : i < t.capacity then
    let old := t.slots[i]'(by rw [t.hSlotsLen]; exact h)
    let sp := r.mappingSpare
    let r0 := { r with mappings := t.eraseAt i h, mappingSpare := Squash.mk #[] }
    rootWithoutEpochCells vaddr
      (Quot.lift (fun a => { r0 with mappingSpare := Squash.mk (a.push old) })
        (fun _ _ _ => by simp only [VSpaceRoot.with_mappingSpare]) sp)
  else rootWithoutEpochCells vaddr r

open SeLe4n.Kernel.RobinHood in
theorem rootWithoutEpochCells_eq (vaddr : SeLe4n.VAddr) (r : VSpaceRoot) :
    rootWithoutEpochCells vaddr r = { r with mappingEpochs := r.mappingEpochs.erase vaddr } := by
  unfold rootWithoutEpochCells
  rw [RHTable.erase_eq_eraseAt]
  dsimp only
  split
  · cases r with
    | mk asid mappings tableBase tables mappingEpochs sp esp tsp =>
      induction esp using Squash.ind with
      | h a =>
        show VSpaceRoot.mk _ _ _ _ _ _ _ _ = _
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
    cases r with
    | mk asid mappings tableBase tables mappingEpochs sp esp tsp =>
      induction sp using Squash.ind with
      | h a =>
        show VSpaceRoot.mk _ _ _ _ _ _ _ _ = _
        simp only [Squash.mk, VSpaceRoot.mk.injEq, true_and, and_true]
        exact Subsingleton.elim _ _
  · rw [rootWithoutEpochCells_eq]

/-- WS-ZA ZA5.4: **an admitted unmap's writes**: the mapping erased in the
root's slot, its invalid descriptor on the ledger, the executing core's flush,
the shootdown round (its descriptor written over the last drained one,
`tlbShootdownBroadcastPage`), the initiator's drain, and — for an executable mapping —
the instruction-cache broadcast, whose operand is read before the write
(`vspaceUnmapPageWithShootdownAndIcacheBroadcast`). -/
def vspaceUnmapPerformAt (ec : Concurrency.CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (rootId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  let op? := Architecture.unmapIcacheOperand st asid vaddr
  let st1 := st.storeVSpaceRootWith rootId (rootWithoutMapping vaddr)
  let st1 := Architecture.recordPhysicalWrites st1 (mappedRootLedger st1 rootId vaddr)
  let st2 := { st1 with tlb := adapterFlushTlbByVAddr st1.tlb asid vaddr }
  let st3 := Architecture.tlbShootdownBroadcastPage st2 ec
    (Architecture.shootdownTargets ec) asid vaddr
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
  simp only [Architecture.tlbShootdownBroadcastPage_eq]
  cases Architecture.unmapIcacheOperand st asid vaddr <;> rfl

/-- The unmap's writes before its instruction-cache operand: the mapping erased
in the root's slot, its descriptor on the ledger, the flush, the shootdown round
and the initiator's drain (`vspaceUnmapPerformAt`'s first five steps). -/
@[noinline] def vspaceUnmapWritesAt (ec : Concurrency.CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (rootId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  let st1 := st.storeVSpaceRootWith rootId (rootWithoutMapping vaddr)
  let st1 := Architecture.recordPhysicalWrites st1 (mappedRootLedger st1 rootId vaddr)
  let st2 := { st1 with tlb := adapterFlushTlbByVAddr st1.tlb asid vaddr }
  let st3 := Architecture.tlbShootdownBroadcastPage st2 ec
    (Architecture.shootdownTargets ec) asid vaddr
  Architecture.drainInitiatorPageOnCore st3 ec asid vaddr

/-- An executable unmap's instruction-cache broadcast and its record, as
`vspaceUnifyPerformAtCells` writes a unify's: over an empty ledger the operand
is written over the drained ledger's cells first (`recordIcacheIvauCells`) and
the broadcast reads it back, so neither an operand nor a list cell is built; a
ledger that is not empty takes the specification's writes
(`recordUnmapIvauAt_eq`). -/
@[noinline] def recordUnmapIvauAt (paddr : SeLe4n.PAddr) (st : SystemState) : SystemState :=
  match st.pendingIcacheMaintenance with
  | [] =>
    let st1 := Architecture.recordIcacheIvauCells st paddr
    match st1.pendingIcacheMaintenance with
    | op :: _ => Architecture.icInvalidateBroadcast st1 Architecture.icBroadcastReach op
    | [] => Architecture.icInvalidateBroadcast st1 Architecture.icBroadcastReach (.ivauPage paddr)
  | _ :: _ =>
    Architecture.recordIcacheMaintenance
      (Architecture.icInvalidateBroadcast st Architecture.icBroadcastReach (.ivauPage paddr))
      (.ivauPage paddr)

theorem recordUnmapIvauAt_eq (paddr : SeLe4n.PAddr) (st : SystemState) :
    recordUnmapIvauAt paddr st =
      Architecture.recordIcacheMaintenance
        (Architecture.icInvalidateBroadcast st Architecture.icBroadcastReach (.ivauPage paddr))
        (.ivauPage paddr) := by
  unfold recordUnmapIvauAt
  cases hP : st.pendingIcacheMaintenance with
  | nil =>
    dsimp only
    rw [Architecture.recordIcacheIvauCells_eq st paddr hP,
      Architecture.recordIcacheMaintenance_of_nil hP]
    rfl
  | cons _ _ => rfl

/-- **`vspaceUnmapPerformAt` as compiled**: whether the mapping is executable,
and its frame's address, are read from the root before the first write, as
words, so no operand or `Option` is built and the root is not held across its
store; the writes follow (`vspaceUnmapWritesAt`), then, for an executable
mapping, the instruction-cache broadcast over the ledger's spare cells
(`recordUnmapIvauAt`).  Equal to the specification
(`vspaceUnmapPerformAt_eq_cells`). -/
def vspaceUnmapPerformAtCells (ec : Concurrency.CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (rootId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  match Architecture.resolveAsidRoot st asid with
  | some (_, root) =>
    match VSpaceRoot.lookup root vaddr with
    | some (paddr, perms) =>
      if perms.execute then recordUnmapIvauAt paddr (vspaceUnmapWritesAt ec asid vaddr rootId st)
      else vspaceUnmapWritesAt ec asid vaddr rootId st
    | none => vspaceUnmapWritesAt ec asid vaddr rootId st
  | none => vspaceUnmapWritesAt ec asid vaddr rootId st

@[csimp] theorem vspaceUnmapPerformAt_eq_cells :
    @vspaceUnmapPerformAt = @vspaceUnmapPerformAtCells := by
  funext ec asid vaddr rootId st
  unfold vspaceUnmapPerformAt vspaceUnmapPerformAtCells Architecture.unmapIcacheOperand
    Architecture.unmapExecutablePaddr
  rw [show vspaceUnmapWritesAt ec asid vaddr rootId st =
      Architecture.drainInitiatorPageOnCore
        (Architecture.tlbShootdownBroadcastPage
          { Architecture.recordPhysicalWrites (st.storeVSpaceRootWith rootId (rootWithoutMapping vaddr))
              (mappedRootLedger (st.storeVSpaceRootWith rootId (rootWithoutMapping vaddr)) rootId vaddr) with
            tlb := adapterFlushTlbByVAddr
              (Architecture.recordPhysicalWrites (st.storeVSpaceRootWith rootId (rootWithoutMapping vaddr))
                (mappedRootLedger (st.storeVSpaceRootWith rootId (rootWithoutMapping vaddr)) rootId vaddr)).tlb
              asid vaddr }
          ec (Architecture.shootdownTargets ec) asid vaddr) ec asid vaddr from rfl]
  cases Architecture.resolveAsidRoot st asid with
  | none => rfl
  | some rr =>
    obtain ⟨_, root⟩ := rr
    dsimp only [Option.bind]
    cases VSpaceRoot.lookup root vaddr with
    | none => rfl
    | some lk =>
      obtain ⟨paddr, perms⟩ := lk
      dsimp only
      cases perms.execute
      · rfl
      · simp only [↓reduceIte, Option.map, recordUnmapIvauAt_eq]

/-- **The unmap's refusal of an address nothing is mapped at**, read before any
write: the root at `rootId` is the one the ASID table names for `asid`, and it
maps nothing at `vaddr`, so the unmap answers `translationFault`
(`vspaceUnmapPageWithShootdownAndIcacheBroadcast_of_unmappedAt`).  The arm
answers it without running the unmap's instruction-cache operand or its
wrappers. -/
def vspaceUnmapUnmappedAt (st : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (rootId : SeLe4n.ObjId) : Bool :=
  (match st.getVSpaceRoot? rootId with
   | some root => root.asid == asid && (root.mappings[vaddr]?).isNone
   | none => false) &&
  st.asidTable.holds asid rootId

/-- An unmap the check reads is refused with `translationFault`. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_of_unmappedAt (ec : Concurrency.CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (rootId : SeLe4n.ObjId) (st : SystemState)
    (h : vspaceUnmapUnmappedAt st asid vaddr rootId = true) :
    Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st =
      .error .translationFault := by
  unfold vspaceUnmapUnmappedAt at h
  cases hGR : st.getVSpaceRoot? rootId with
  | none => simp [hGR] at h
  | some root =>
  have hR : st.objects[rootId]? = some (.vspaceRoot root) :=
    (SystemState.getVSpaceRoot?_eq_some_iff st rootId root).1 hGR
  simp only [hGR, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨hAs, hN⟩, hH⟩ := h
  have hRes := resolveAsidRoot_of_holds hH hR hAs
  rw [Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast_error_iff]
  unfold Architecture.vspaceUnmapPageWithShootdownPerCore
    Architecture.vspaceUnmapPageWithShootdown Architecture.vspaceUnmapPageWithFlush
    Architecture.vspaceUnmapPage
  simp only [hRes, VSpaceRoot.unmapPage, hN]

end SeLe4n.Kernel
